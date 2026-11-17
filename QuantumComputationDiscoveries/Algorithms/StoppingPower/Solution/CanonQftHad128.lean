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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.SharedUnary108Koff
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Slot3Norm1sPhys80
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.ApexOffsetHoist

set_option Elab.async false

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section JunctionUncondHadTailCut
local instance (priority := 1000000) instNeZeroTwoPow_JunctionUncondHadTailCut (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

namespace JunctionUncondHadTailCut
set_option exponentiation.threshold 8192
open QuantumComputation Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt
  HermitianMat Real
open scoped Matrix BigOperators ComplexOrder MatrixOrder Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet xAllCircuit count_xAllCircuit_toff
  count_xAllCircuit_t
open DyadicQft64Engine
open NuclearTwistAndXor654Concrete
open NuclearTwistRealizes
open ProjZ512QftAndTwist288 hiding
  basisBits_symm_apply fullSysCoreWires_eq_add
open FusedVepCore288 JunctionApexCSA288
open InterWalkRSum42Hoist
open Proj3DCut.WhHelper
open Proj3DCut
noncomputable def uHad3DCore {mPayload : ℕ} (m : Fin 8) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  (rProjAxis rId 0).embedUnitary (wireHadamard8 m) *
    ((rProjAxis rId 1).embedUnitary (wireHadamard8 m) *
      (rProjAxis rId 2).embedUnitary (wireHadamard8 m))
theorem uHad3DCore_eq_uCoin0Stage3D {mPayload : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8) :
    (uHad3DCore (mPayload := mPayload) m) =
      uCoin0Stage3D hm (fun _ ↦ wireHadamard8 m) (wireHadamard8 m) := by
  have h1 : ∀ w : Fin 3,
      (rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w).embedUnitary (wireHadamard8 m) =
        uCoin0Stage1DCore hm w (fun _ ↦ wireHadamard8 m) (wireHadamard8 m) := by
    intro w; apply Subtype.ext; ext i j
    simp [uCoin0Stage1DCore, uCoin0Stage1DMat]
  unfold uHad3DCore uCoin0Stage3D
  exact congrArg₂ (· * ·) (h1 0) (congrArg₂ (· * ·) (h1 1) (h1 2))
theorem uHad3DCore_inv {mPayload : ℕ} (hm : 22 ≤ mPayload) (m : Fin 8) :
    (uHad3DCore (mPayload := mPayload) m)⁻¹ = uHad3DCore m := by
  have hsq : wireHadamard8 m * wireHadamard8 m = 1 :=
    (congrArg (wireHadamard8 m * ·) (wireHadamard8_inv m).symm).trans (mul_inv_cancel _)
  apply inv_eq_of_mul_eq_one_right
  rw [uHad3DCore_eq_uCoin0Stage3D hm m, uCoin0Stage3D_mul,
    show (fun _ : Fin 2 ↦ wireHadamard8 m * wireHadamard8 m) = fun _ ↦ 1 from funext fun _ ↦ hsq,
    hsq]
  apply Subtype.ext
  simp [uCoin0Stage3D, uCoin0Stage1DCore, uCoin0Stage1DMat_one]
def cH_3D {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) (m : Fin 8) :
    Circuit n :=
  (Circuit.H m : Circuit 8).onRegister (rProjAxis rCore 2) ;;ᶜ
    ((Circuit.H m : Circuit 8).onRegister (rProjAxis rCore 1) ;;ᶜ
      (Circuit.H m : Circuit 8).onRegister (rProjAxis rCore 0))
@[scoped simp] theorem count_cH_3D_toff {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (m : Fin 8) :
    (cH_3D rCore m).count .TOFF = 0 := by simp [cH_3D, Circuit.count_seq, Circuit.H]
@[scoped simp] theorem count_cH_3D_t {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (m : Fin 8) :
    (cH_3D rCore m).count .T = 0 := by simp [cH_3D, Circuit.count_seq, Circuit.H]
theorem cH_3D_eval {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n)
    (m : Fin 8) : (cH_3D rCore m).eval = rCore.embedUnitary (uHad3DCore m) := by
  have hH : (Circuit.H m : Circuit 8).eval = wireHadamard8 m := rfl
  unfold cH_3D uHad3DCore
  simp only [Circuit.eval_seq, Circuit.eval_onRegister, hH,
    QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose, mul_assoc]
  rfl
def dHUncond_3D {mPayload : ℕ} (isInv : Bool) (m : Fin 8) {Var : Type} {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) : DynamicCircuit Var n :=
  if isInv then .circuit (cH_3D rCore m).inverse else .circuit (cH_3D rCore m)
@[scoped simp]
theorem count_dHUncond_3D_toff {mPayload : ℕ} (isInv : Bool) (m : Fin 8) {Var : Type} {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (dHUncond_3D isInv m (Var := Var) rCore).count .TOFF = 0 := by
  cases isInv <;> simp [dHUncond_3D]
@[scoped simp]
theorem count_dHUncond_3D_t {mPayload : ℕ} (isInv : Bool) (m : Fin 8) {Var : Type} {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (dHUncond_3D isInv m (Var := Var) rCore).count .T = 0 := by
  cases isInv <;> simp [dHUncond_3D]
noncomputable def uHad1To7_8 : Unitary 256 := wireHadamard8 1 * (wireHadamard8 2 *
    (wireHadamard8 3 * (wireHadamard8 4 * (wireHadamard8 5 * (wireHadamard8 6 * wireHadamard8
    7)))))
noncomputable def uTailHadLocal8 : Unitary 256 := uTailLocal8 * uHad1To7_8
def cHad1To7_8 : Circuit 8 :=
  Circuit.H 7 ;;ᶜ
    (Circuit.H 6 ;;ᶜ
      (Circuit.H 5 ;;ᶜ
        (Circuit.H 4 ;;ᶜ
          (Circuit.H 3 ;;ᶜ
            (Circuit.H 2 ;;ᶜ Circuit.H 1)))))
def cTailHadLocal8 : Circuit 8 :=
  cHad1To7_8 ;;ᶜ cTailLocal8
@[scoped simp] theorem count_cHad1To7_8_toff : cHad1To7_8.count .TOFF = 0 := rfl
@[scoped simp] theorem count_cHad1To7_8_t : cHad1To7_8.count .T = 0 := rfl
@[scoped simp] theorem count_cTailHadLocal8_toff : cTailHadLocal8.count .TOFF = 0 := rfl
@[scoped simp] theorem count_cTailHadLocal8_t : cTailHadLocal8.count .T = 0 := rfl
theorem cHad1To7_8_eval_eq : cHad1To7_8.eval = uHad1To7_8 := by
  unfold cHad1To7_8 uHad1To7_8
  simp only [Circuit.eval_seq, mul_assoc]
  rfl
theorem cTailHadLocal8_eval_eq : cTailHadLocal8.eval = uTailHadLocal8 := by
  unfold cTailHadLocal8 uTailHadLocal8
  rw [Circuit.eval_seq, cTailLocal8_eval_eq, cHad1To7_8_eval_eq]
noncomputable def uTailHad3DCore {mPayload : ℕ} : Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  (rProjAxis rId 0).embedUnitary uTailHadLocal8 *
    ((rProjAxis rId 1).embedUnitary uTailHadLocal8 *
      (rProjAxis rId 2).embedUnitary uTailHadLocal8)
def cTailHad_3D {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) : Circuit n :=
  cTailHadLocal8.onRegister (rProjAxis rCore 2) ;;ᶜ
    (cTailHadLocal8.onRegister (rProjAxis rCore 1) ;;ᶜ
      cTailHadLocal8.onRegister (rProjAxis rCore 0))
@[scoped simp] theorem count_cTailHad_3D_toff {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (cTailHad_3D rCore).count .TOFF = 0 := by
  unfold cTailHad_3D
  simp [Circuit.count_seq, Circuit.count_onRegister]
@[scoped simp] theorem count_cTailHad_3D_t {mPayload n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (cTailHad_3D rCore).count .T = 0 := by
  unfold cTailHad_3D
  simp [Circuit.count_seq, Circuit.count_onRegister]
theorem cTailHad_3D_eval {mPayload n : ℕ} (rCore : QRegister (fullSysCoreWires mPayload) n) :
    (cTailHad_3D rCore).eval = rCore.embedUnitary uTailHad3DCore := by
  unfold cTailHad_3D uTailHad3DCore
  simp only [Circuit.eval_seq, Circuit.eval_onRegister, cTailHadLocal8_eval_eq,
    QRegister.embedUnitary_mul, ← QRegister.embedUnitary_compose, mul_assoc]
  rfl
def dConjInvTailHad3D {mPayload : ℕ} {Var : Type} {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (dInner : DynamicCircuit Var n) :
    DynamicCircuit Var n := dPureConj (cTailHad_3D rCore).inverse dInner
@[scoped simp] theorem count_dConjInvTailHad3D_toff {mPayload : ℕ} {Var : Type} {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (dInner : DynamicCircuit Var n)
    (hIn : dInner.count .TOFF = 0) : (dConjInvTailHad3D rCore dInner).count .TOFF = 0 := by
  unfold dConjInvTailHad3D
  rw [count_dPureConj_toff _
    (by rw [count_inverse_toff, count_cTailHad_3D_toff]), hIn]
@[scoped simp] theorem count_dConjInvTailHad3D_t {mPayload : ℕ} {Var : Type} {n : ℕ}
    (rCore : QRegister (fullSysCoreWires mPayload) n) (dInner : DynamicCircuit Var n) :
    (dConjInvTailHad3D rCore dInner).count .T = dInner.count .T := by
  unfold dConjInvTailHad3D
  exact count_dPureConj_t _ (count_inverse_t_of_zero (count_cTailHad_3D_t rCore)) dInner
noncomputable def uProj3DHadCut1DCore {mPayload : ℕ} (hm : 22 ≤ mPayload) (w : Fin 3) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uCoin0Stage1DCore hm w uProjPlus512_1D uTailHadLocal8
noncomputable def uProj3DHadCutCore {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload)) :=
  uProj3DHadCut1DCore hm 0 * (uProj3DHadCut1DCore hm 1 * uProj3DHadCut1DCore hm 2)
theorem dyadicDiag_comm_uHad1D {mPayload : ℕ}
    (e : BitAssignment (fullSysCoreWires mPayload) → ℤ) (w' : Fin 3) (j : Fin 8) (he : ∀ γ₁
    γ₂ : BitAssignment (fullSysCoreWires mPayload), (∀ u, u ≠ rProjAxis (QRegExt.idReg _)
    w' j → γ₁ u = γ₂ u) → e γ₁ = e γ₂) : (rProjAxis (QRegExt.idReg (fullSysCoreWires
    mPayload)) w').embedUnitary (wireHadamard8 j) * DyadicQft64.dyadicDiagUnitary
    (fullSysCoreWires mPayload) 48 e = DyadicQft64.dyadicDiagUnitary
    (fullSysCoreWires mPayload) 48 e * (rProjAxis (QRegExt.idReg (fullSysCoreWires
    mPayload)) w').embedUnitary (wireHadamard8 j) := by
  apply Subtype.ext; apply matrix_ext_basisKet; intro γ
  let rId := QRegExt.idReg (fullSysCoreWires mPayload)
  let w₀ := rProjAxis rId w' j
  have hComp : (rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w').compose
    (QRegister.singleton j) =
      QRegister.singleton w₀ := by
    apply qreg_ext_local; intro i; fin_cases i; rfl
  have hEmbH : (rProjAxis (QRegExt.idReg (fullSysCoreWires mPayload)) w').embedUnitary
    (wireHadamard8 j) =
      (QRegister.singleton w₀).embedUnitary Qubit.H := by
    unfold wireHadamard8
    rw [← QRegister.embedUnitary_compose, hComp]
  rw [Submonoid.coe_mul, Submonoid.coe_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    JunctionApexCSA288.dyadicDiagUnitary_mulVec_basisKet, Matrix.mulVec_smul,
    hEmbH, QRegister.embedUnitary_val, vepEmbedMatrix_mulVec_basisKet, Matrix.mulVec_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [Matrix.mulVec_smul, JunctionApexCSA288.dyadicDiagUnitary_mulVec_basisKet,
    smul_smul, smul_smul, mul_comm]
  congr 2
  apply congrArg (DyadicQft64.dyadicTurn 48)
  apply he γ (vepWriteReg γ (QRegister.singleton w₀) (basisBits 1 l))
  intro u hu
  symm
  apply vepWriteReg_not_mem
  rintro ⟨i, rfl⟩
  fin_cases i
  exact hu rfl
theorem uWhUngatedCore_comm_uHad3DCore_of_le {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (k : Fin 7) (j : Fin 8) (hjk : j.val ≤ k.val) :
    uHad3DCore (mPayload := mPayload) j * uWhUngatedCore hm k =
      uWhUngatedCore hm k * uHad3DCore (mPayload := mPayload) j := by
  unfold uHad3DCore uWhUngatedCore
  dsimp only
  have hc (w : Fin 3) := dyadicDiag_comm_uHad1D (whUngatedExp hm k) w j
    (whUngatedExp_congr_outside_le hm k w j hjk)
  rw [mul_assoc, mul_assoc, hc 2, ← mul_assoc ((rProjAxis _ 1).embedUnitary _), hc 1,
    mul_assoc _ ((rProjAxis _ 1).embedUnitary _),
    ← mul_assoc ((rProjAxis _ 0).embedUnitary _), hc 0, mul_assoc]
noncomputable def uProj3DHadCutPre16Cat {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  let eC := (rCoreBlock48 mPayload).embedUnitary
  uWhRemCat hm false *
    (uWhStgCutCat hm 0 false *
      (eC (uHad3DCore 1) *
        (uWhStgCutCat hm 1 false *
          (eC (uHad3DCore 2) *
            (uWhStgCutCat hm 2 false *
              (eC (uHad3DCore 3) *
                (uWhStgCutCat hm 3 false *
                  (eC (uHad3DCore 4) *
                    (uWhStgCutCat hm 4 false *
                      (eC (uHad3DCore 5) *
                        (uWhStgCutCat hm 5 false *
                          (eC (uHad3DCore 6) *
                            (uWhStgCutCat hm 6 false *
                              (eC (uHad3DCore 7) *
                                uWhStg7CutCat hm false))))))))))))))
noncomputable def uProj3DHadCutApexCat {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  (rCoreBlock48 mPayload).embedUnitary uTail3DCore * uProj3DHadCutPre16Cat hm
theorem fixesLow3924_uProj3DHadCutApexCat (hm : 22 ≤ 80) :
    FixesLow3924 h3924_cat (uProj3DHadCutApexCat hm).1 := by
  let rC0 : QRegister (fullSysCoreWires 80) (fullSysCoreWires 80 + 48) := rCoreBlock48 80
  have hPref : IsLow3924Prefix h3924_core h3924_cat rC0 :=
    isLow3924Prefix_block0 h3924_core h3924_cat (by decide)
  have hStgCore : ∀ (F_c0 : Fin 2 → Unitary 256) (F_other : Unitary 256),
      FixesLow3924 h3924_cat (rC0.embedUnitary (uCoin0Stage3D hm F_c0 F_other)).1 := by
    intro F_c0 F_other
    rw [QRegister.embedUnitary_val]
    refine fixesLow3924_embedMatrix_prefix hPref ?_
    unfold uCoin0Stage3D
    simp only [Submonoid.coe_mul]
    exact (fixesLow3924_uCoin0Stage1DCore hm 0 F_c0 F_other).mul
      ((fixesLow3924_uCoin0Stage1DCore hm 1 F_c0 F_other).mul
        (fixesLow3924_uCoin0Stage1DCore hm 2 F_c0 F_other))
  have hTail : FixesLow3924 h3924_cat (rC0.embedUnitary uTail3DCore).1 := by
    rw [uTail3DCore_eq_uCoin0Stage3D hm]
    exact hStgCore (fun _ ↦ uTailLocal8) uTailLocal8
  have hHad : ∀ m : Fin 8, FixesLow3924 h3924_cat (rC0.embedUnitary (uHad3DCore m)).1 := by
    intro m
    rw [uHad3DCore_eq_uCoin0Stage3D hm m]
    exact hStgCore (fun _ ↦ wireHadamard8 m) (wireHadamard8 m)
  have h7 : FixesLow3924 h3924_cat (uWhStg7CutCat hm false).1 :=
    fixesLow3924_embed_dyadicDiag h3924_cat _ _
  have hStg : ∀ k : Fin 7, FixesLow3924 h3924_cat (uWhStgCutCat hm k false).1 := by
    intro k; unfold uWhStgCutCat
    simp only [Submonoid.coe_mul]
    exact (fixesLow3924_uApexShift45 h3924_core _ _).mul (fixesLow3924_embed_dyadicDiag h3924_cat _
      _)
  have hRem : FixesLow3924 h3924_cat (uWhRemCat hm false).1 := by
    unfold uWhRemCat
    simp only [Submonoid.coe_mul]
    exact (fixesLow3924_uApexShift45 h3924_core _ _).mul (fixesLow3924_embed_dyadicDiag h3924_cat _
      _)
  unfold uProj3DHadCutApexCat uProj3DHadCutPre16Cat
  dsimp only []
  simp only [Submonoid.coe_mul]
  exact hTail.mul (hRem.mul ((hStg 0).mul ((hHad 1).mul ((hStg 1).mul ((hHad 2).mul ((hStg
    2).mul ((hHad 3).mul ((hStg 3).mul ((hHad 4).mul ((hStg 4).mul ((hHad 5).mul ((hStg 5).mul
    ((hHad 6).mul ((hStg 6).mul ((hHad 7).mul h7)))))))))))))))
theorem uProj3DHadCutApexCat_intertwinesLocal {mPayload : ℕ} (hm : 22 ≤ mPayload)
    (U_cat_48 : Unitary (2 ^ 48))
    (hcol0 : U_cat_48.1.mulVec (Pi.single 0 1) = phaseGradKet 48) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
      (uProj3DHadCutApexCat hm) (uProj3DHadCutCore hm) := by
  have h7 := uWhStg7CutCat_intertwinesLocal hm U_cat_48
  have hH (m : Fin 8) := NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary
    U_cat_48 (uHad3DCore (mPayload := mPayload) m)
  have hS (k : Fin 7) := uWhStgCutCat_intertwinesLocal hm k U_cat_48 hcol0
  have hRem := uWhRemCat_intertwinesLocal hm U_cat_48 hcol0
  have hTail : NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
      ((rCoreBlock48 mPayload).embedUnitary uTail3DCore)
      (uCoin0Stage3D hm (fun _ ↦ uTailLocal8) uTailLocal8) := by
    rw [← uTail3DCore_eq_uCoin0Stage3D hm]
    exact NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48 uTail3DCore
  have hProd := ((((((((((((((((h7.mul (hH 7)).mul (hS 6)).mul (hH 6)).mul (hS 5)).mul (hH
      5)).mul (hS 4)).mul (hH 4)).mul (hS 3)).mul (hH 3)).mul (hS 2)).mul (hH 2)).mul (hS
      1)).mul (hH 1)).mul (hS 0)).mul hRem).mul hTail)
  suffices hEff :
      uCoin0Stage3D hm (fun _ ↦ uTailLocal8) uTailLocal8 *
        (uWhRemCore hm *
          ((uCoin0Stage3D hm (whGatedDiag8 0) 1 * uWhUngatedCore hm 0) *
            (uHad3DCore 1 *
              ((uCoin0Stage3D hm (whGatedDiag8 1) 1 * uWhUngatedCore hm 1) *
                (uHad3DCore 2 *
                  ((uCoin0Stage3D hm (whGatedDiag8 2) 1 * uWhUngatedCore hm 2) *
                    (uHad3DCore 3 *
                      ((uCoin0Stage3D hm (whGatedDiag8 3) 1 * uWhUngatedCore hm 3) *
                        (uHad3DCore 4 *
                          ((uCoin0Stage3D hm (whGatedDiag8 4) 1 * uWhUngatedCore hm 4) *
                            (uHad3DCore 5 *
                              ((uCoin0Stage3D hm (whGatedDiag8 5) 1 * uWhUngatedCore hm 5) *
                                (uHad3DCore 6 *
                                  ((uCoin0Stage3D hm (whGatedDiag8 6) 1 * uWhUngatedCore hm 6) *
                                    (uHad3DCore 7 *
                                      uCoin0Stage3D hm whStg7Diag8 1))))))))))))))) =
      uProj3DHadCutCore hm by
    rw [← hEff]; exact hProd
  have pullG : ∀ (k j : Fin 7) (X : Unitary (2 ^ (fullSysCoreWires mPayload))),
      uCoin0Stage3D hm (whGatedDiag8 j) 1 * (uWhUngatedCore hm k * X) =
        uWhUngatedCore hm k * (uCoin0Stage3D hm (whGatedDiag8 j) 1 * X) := by
    intro k j X
    rw [← mul_assoc, uWhUngatedCore_comm_coin0DiagStage hm k (whGatedDiag8 j) (fun _ ↦
      ⟨_, rfl⟩), mul_assoc]
  have pullH : ∀ (k : Fin 7) (j : Fin 8) (hjk : j.val ≤ k.val)
      (X : Unitary (2 ^ (fullSysCoreWires mPayload))), uHad3DCore j *
      (uWhUngatedCore hm k * X) = uWhUngatedCore hm k * (uHad3DCore j * X) := by
    intro k j hjk X
    rw [← mul_assoc, uWhUngatedCore_comm_uHad3DCore_of_le hm k j hjk, mul_assoc]
  have pullGH : ∀ (k j : Fin 7) (i : Fin 8) (hi : i.val ≤ k.val)
      (X : Unitary (2 ^ (fullSysCoreWires mPayload))),
      uCoin0Stage3D hm (whGatedDiag8 j) 1 * (uHad3DCore i * (uWhUngatedCore hm k * X)) =
        uWhUngatedCore hm k * (uCoin0Stage3D hm (whGatedDiag8 j) 1 * (uHad3DCore i * X)) := by
    intro k j i hi X
    rw [pullH k i hi X, pullG k j]
  rw [mul_assoc (uCoin0Stage3D hm (whGatedDiag8 0) 1) (uWhUngatedCore hm 0), pullG 0 0,
    mul_assoc (uCoin0Stage3D hm (whGatedDiag8 1) 1) (uWhUngatedCore hm 1), pullG 1 1,
    pullGH 1 0 1 (by decide),
    mul_assoc (uCoin0Stage3D hm (whGatedDiag8 2) 1) (uWhUngatedCore hm 2), pullG 2 2,
    pullGH 2 1 2 (by decide), pullGH 2 0 1 (by decide),
    mul_assoc (uCoin0Stage3D hm (whGatedDiag8 3) 1) (uWhUngatedCore hm 3), pullG 3 3,
    pullGH 3 2 3 (by decide), pullGH 3 1 2 (by decide), pullGH 3 0 1 (by decide),
    mul_assoc (uCoin0Stage3D hm (whGatedDiag8 4) 1) (uWhUngatedCore hm 4), pullG 4 4,
    pullGH 4 3 4 (by decide), pullGH 4 2 3 (by decide), pullGH 4 1 2 (by decide),
    pullGH 4 0 1 (by decide),
    mul_assoc (uCoin0Stage3D hm (whGatedDiag8 5) 1) (uWhUngatedCore hm 5), pullG 5 5,
    pullGH 5 4 5 (by decide), pullGH 5 3 4 (by decide), pullGH 5 2 3 (by decide),
    pullGH 5 1 2 (by decide), pullGH 5 0 1 (by decide),
    mul_assoc (uCoin0Stage3D hm (whGatedDiag8 6) 1) (uWhUngatedCore hm 6), pullG 6 6,
    pullGH 6 5 6 (by decide), pullGH 6 4 5 (by decide), pullGH 6 3 4 (by decide),
    pullGH 6 2 3 (by decide), pullGH 6 1 2 (by decide), pullGH 6 0 1 (by decide)]
  have hCancel (Rest : Unitary (2 ^ (fullSysCoreWires mPayload))) :
      uWhRemCore hm * (uWhUngatedCore hm 0 * (uWhUngatedCore hm 1 * (uWhUngatedCore hm 2 *
        (uWhUngatedCore hm 3 * (uWhUngatedCore hm 4 *
          (uWhUngatedCore hm 5 * (uWhUngatedCore hm 6 * Rest))))))) = Rest := by
    simpa only [mul_assoc, one_mul] using congrArg (· * Rest) (uWhRemCore_cancel_all hm)
  rw [hCancel, uHad3DCore_eq_uCoin0Stage3D hm 1, uHad3DCore_eq_uCoin0Stage3D hm 2,
    uHad3DCore_eq_uCoin0Stage3D hm 3, uHad3DCore_eq_uCoin0Stage3D hm 4,
    uHad3DCore_eq_uCoin0Stage3D hm 5, uHad3DCore_eq_uCoin0Stage3D hm 6,
    uHad3DCore_eq_uCoin0Stage3D hm 7]
  simp only [uCoin0Stage3D_mul, mul_one, one_mul]
  change uCoin0Stage3D hm _ uTailHadLocal8 = uCoin0Stage3D hm uProjPlus512_1D uTailHadLocal8
  congr 1; funext b
  unfold uTailLocal8
  rw [mul_assoc bitRev8Unitary (wireHadamard8 0)]
  have hWh8 := whEightStage_eq_eightStage b
  simp only [mul_assoc] at hWh8
  rw [hWh8]
  apply Subtype.ext
  have h8 := eightStageProj512_eq_uProjPlus512_1D b
  simpa only [Submonoid.coe_mul, Matrix.mul_assoc] using h8
noncomputable def uProj3DVepHadPre16Cat {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  let eC := (rCoreBlock48 mPayload).embedUnitary
  uWhRemCat hm false *
    (uWhStgCat hm 0 false *
      (eC (uHad3DCore 1) *
        (uWhStgCat hm 1 false *
          (eC (uHad3DCore 2) *
            (uWhStgCat hm 2 false *
              (eC (uHad3DCore 3) *
                (uWhStgCat hm 3 false *
                  (eC (uHad3DCore 4) *
                    (uWhStgCat hm 4 false *
                      (eC (uHad3DCore 5) *
                        (uWhStgCat hm 5 false *
                          (eC (uHad3DCore 6) *
                            (uWhStgCat hm 6 false *
                              (eC (uHad3DCore 7) *
                                uWhStg7Cat hm false))))))))))))))
noncomputable def uPrefixProjHadCutAndXorCat {mPayload : ℕ} (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  (rCoreBlock48 mPayload).embedUnitary (uXor32Core mPayload) * uProj3DHadCutApexCat hm
set_option exponentiation.threshold 256
end JunctionUncondHadTailCut
end JunctionUncondHadTailCut

section CoreQftHadamard140And160
local instance (priority := 1000000) instNeZeroTwoPow_CoreQftHadamard140And160 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
# `128`-Wire Canonical QFT-Hadamard Stage Builders (`CoreQftHadamard140And160`)

Defines `nCanon4062 := (3924 + 3 + 7) + 128`, `CanonStageSpec128`, `buildXorApexChainFrom128`,
`stageD2CanonStage128`, `stageD1CanonStage128`, `stageH654CanonStage128`, and
`toFullSysQft654BundleOfLe128` (`128 ≤ mWork`, `0` `.TOFF`).
-/

namespace CoreQftHadamard140And160
set_option exponentiation.threshold 8192
open DyadicQft64Engine DyadicQft64
open DyadicQft64WalkCircuit
open DyadicQft64WalkCircuit288
open FullSysCatSegmentBridge
open scoped Matrix BigOperators
local instance (priority :=
  1000000) instLoc_CoreQftHadamard140And160_1InstNeZeroTwoPowQf (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k)⟩
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt
open SpecsAux.SpecMirror
abbrev nCanon4062 : ℕ := (3924 + 3 + 7) + 128
def rQftCanon128 : QRegister (3924 + 3 + 7) nCanon4062 :=
  QRegister.block 0 (3924 + 3 + 7) (by decide)
def rWorkCanon128 : QRegister 128 nCanon4062 := QRegister.block (3924 + 3 + 7) 128 (by decide)
theorem rQftCanon128_disjoint_rWorkCanon128 : rQftCanon128.DisjointWires rWorkCanon128 :=
  disjoint_block_sep (by decide)
def rSysCanon128 : QRegister (3924 + 3) nCanon4062 := rQftCanon128.compose rIdInCat
def rPGCanon128 : QRegister 7 nCanon4062 := rQftCanon128.compose rPGInCat
theorem rSysCanon128_disjoint_rPGCanon128 : rSysCanon128.DisjointWires rPGCanon128 :=
  rIdOfCat_disjoint_rPGOfCat rQftCanon128
theorem rSysCanon128_disjoint_rWorkCanon128 : rSysCanon128.DisjointWires rWorkCanon128 :=
  rQftCanon128_disjoint_rWorkCanon128.compose_left _
theorem rPGCanon128_disjoint_rWorkCanon128 : rPGCanon128.DisjointWires rWorkCanon128 :=
  rQftCanon128_disjoint_rWorkCanon128.compose_left _
structure CanonStageSpec128 where
  uCat : Unitary (2 ^ (3924 + 3 + 7))
  uEff : Unitary (2 ^ (3924 + 3))
  tCost : ℕ
  dFwd : DynamicCircuit Unit nCanon4062
  dInv : DynamicCircuit Unit nCanon4062
  hToffFwd : dFwd.count .TOFF = 0
  hToffInv : dInv.count .TOFF = 0
  hTFwd : dFwd.count .T = tCost
  hTInv : dInv.count .T = tCost
  hRealFwd : RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon128 rWorkCanon128 uCat dFwd
  hRealInv : RealizesEmbeddedUnitaryWithCleanWorkspace rQftCanon128 rWorkCanon128 uCat⁻¹ dInv
  hIntertwines : ∀ {N : ℕ} [NeZero (2 ^ N)]
    (rId : QRegister (3924 + 3) N) (rPG : QRegister 7 N) (hdisj : rId.DisjointWires rPG)
    (U_cat7 : Unitary (2 ^ 7)),
    U_cat7.1.mulVec (Pi.single 0 1) = DyadicQft64.phaseGradKet 7 →
    DyadicQft64.IntertwinesCatOp
      (rPG.embedUnitary U_cat7).1
      (rPG.basisOutcomeProjector 0)
      ((rId.concat rPG hdisj).embedUnitary uCat).1
      (rId.embedUnitary uEff).1
noncomputable def CanonStageSpec128.id : CanonStageSpec128 where
  uCat := 1
  uEff := 1
  tCost := 0
  dFwd := .circuit .identity
  dInv := .circuit .identity
  hToffFwd := rfl
  hToffInv := rfl
  hTFwd := rfl
  hTInv := rfl
  hRealFwd :=
    realizesEmbeddedUnitaryWithCleanWorkspace_circuit rQftCanon128 rWorkCanon128 1 .identity
    (by simp [Circuit.eval_identity])
  hRealInv :=
    realizesEmbeddedUnitaryWithCleanWorkspace_circuit rQftCanon128 rWorkCanon128 1⁻¹ .identity
    (by simp [Circuit.eval_identity])
  hIntertwines rId rPG hdisj U_cat7 _ := by
    rw [(rId.concat rPG hdisj).embedUnitary_one, rId.embedUnitary_one, OneMemClass.coe_one]
    exact DyadicQft64.IntertwinesCatOp.refl_of_comm ((one_mul _).trans (mul_one _).symm)
      ((one_mul _).trans (mul_one _).symm)
noncomputable def CanonStageSpec128.seq (S₁ S₂ : CanonStageSpec128) : CanonStageSpec128 where
  uCat := S₂.uCat * S₁.uCat
  uEff := S₂.uEff * S₁.uEff
  tCost := S₁.tCost + S₂.tCost
  dFwd := .seq S₁.dFwd S₂.dFwd
  dInv := .seq S₂.dInv S₁.dInv
  hToffFwd := by simp [S₁.hToffFwd, S₂.hToffFwd]
  hToffInv := by simp [S₂.hToffInv, S₁.hToffInv]
  hTFwd := by simp [S₁.hTFwd, S₂.hTFwd]
  hTInv := by simp only [DynamicCircuit.count, S₂.hTInv, S₁.hTInv, Nat.add_comm]
  hRealFwd := S₁.hRealFwd.seq rQftCanon128_disjoint_rWorkCanon128 S₂.hRealFwd
  hRealInv := by
    rw [_root_.mul_inv_rev]
    exact S₂.hRealInv.seq rQftCanon128_disjoint_rWorkCanon128 S₁.hRealInv
  hIntertwines rId rPG hdisj U_cat7 hcol0 := by
    rw [(rId.concat rPG hdisj).embedUnitary_mul, rId.embedUnitary_mul,
      Submonoid.coe_mul, Submonoid.coe_mul]
    exact (S₂.hIntertwines rId rPG hdisj U_cat7 hcol0).mul
      (S₁.hIntertwines rId rPG hdisj U_cat7 hcol0)
noncomputable def CanonStageSpec128.congr (S : CanonStageSpec128)
    {uEff' : Unitary (2 ^ (3924 + 3))} {tCost' : ℕ}
    (hu : S.uEff = uEff') (ht : S.tCost = tCost') : CanonStageSpec128 where
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
theorem concat_compose_rQftCanon128 {n : ℕ} (rQftCat : QRegister (3924 + 3 + 7) n)
    (rWork : QRegister 128 n) (hdisj : rQftCat.DisjointWires rWork) :
    (rQftCat.concat rWork hdisj).compose rQftCanon128 = rQftCat := by
  apply DyadicQft64WalkCircuit288Alt.qreg_ext; intro i
  rw [QRegister.compose_apply]
  have hi : rQftCanon128 i = Fin.castAdd 128 i := Fin.ext (by simp [rQftCanon128])
  rw [hi, QRegister.concat_apply_left]
theorem concat_compose_rWorkCanon128 {n : ℕ} (rQftCat : QRegister (3924 + 3 + 7) n)
    (rWork : QRegister 128 n) (hdisj : rQftCat.DisjointWires rWork) :
    (rQftCat.concat rWork hdisj).compose rWorkCanon128 = rWork := by
  apply DyadicQft64WalkCircuit288Alt.qreg_ext; intro j
  rw [QRegister.compose_apply]
  have hj : rWorkCanon128 j = Fin.natAdd (3924 + 3 + 7) j := Fin.ext (by simp [rWorkCanon128])
  rw [hj, QRegister.concat_apply_right]
theorem stage128_intertwines_fullSys (S : CanonStageSpec128) (U_cat7 : Unitary (2 ^ 7))
    (hcol : ∀ m : Fin (2 ^ 7), U_cat7.1 m 0 = PhaseGradCatalystCore.phaseGradientState 7 m) :
    IntertwinesLocalCat U_cat7 S.uCat S.uEff := by
  let rAct0 : QRegister (3924 + 3) ((3924 + 3) + 7) := QRegister.block 0 (3924 + 3) qft_act0_le
  let rCat0 : QRegister 7 ((3924 + 3) + 7) := QRegister.block (3924 + 3) 7 le_rfl
  have hRaw :=
    S.hIntertwines rAct0 rCat0 qft_disj0 U_cat7 (mulVec_col0_eq_phaseGradKet7 U_cat7 hcol)
  have hWhole : (rAct0.concat rCat0 qft_disj0).embedUnitary S.uCat = S.uCat := by
    rw [concat_blocks_eq_whole_local (3924 + 3) 7 qft_disj0]
    exact QRegister.whole_embedUnitary _
  rw [hWhole] at hRaw
  exact ⟨hRaw.1, hRaw.2.1, hRaw.2.2⟩

noncomputable def toFullSysQft654BundleOfLe128 (S : CanonStageSpec128)
    (mWork : ℕ) (_hm : 128 ≤ mWork) :
    FullSysCatSegmentBridge.FullSysQft654Bundle where
  mWorkQft := mWork
  uQft654 := S.uEff
  uQftCat := S.uCat
  hIntertwinesQft := stage128_intertwines_fullSys S

set_option exponentiation.threshold 256
end CoreQftHadamard140And160
end CoreQftHadamard140And160

section Slot3Norm1s36CoreWide
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Norm1s36CoreWide (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
Parametric `(K, D)` 1-Sided Normalized Slot-3 Core Circuit on `mWork = 262` Clean Wires (Top
Assembly).

Provides:
1. Exact `Norm1sTier.tCoreWide` (`11,048 .. 11,672 T`, `0 .TOFF`) and active-register seam
   abbreviations bridged to `Slot3Norm1s36Physics80`.
2. Guarded barrel/Booth forward (`n1sDFwd411`) and `0 .TOFF` dynamic reverse (`n1sDRev411`)
   realizations on `M = 411` (`149 + 262`) over `Slot3Norm1s36CoreWideBooth`.
3. Full 8-stage `mWork = 262` pipeline `dCoreNorm1s_262` with `0 .TOFF`, `<= t.tCoreWide` `T`,
   `RealizesEmbeddedUnitaryWithCleanWorkspace` for `uCore149Norm1s t cfg`, and `wp` specification.
-/

namespace Slot3Norm1s36CoreWide
set_option exponentiation.threshold 256

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open SpecsAux.SpecMirror
open scoped Matrix ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator
noncomputable section

open _root_.QuantumComputation.Specs.StoppingPowerSolution (wire_ne_of_lt wire_ne_of_gt CliffProg
  TempPhaseProg cleanRem)
open _root_.QuantumComputation.Specs.StoppingPowerSolution (ValidCleanRem ScopedBlock TempCtx
  ctxCliffAlloc ctxTempBit RealizesCleanUnitary_seq_asym)
open MeasureBranchHadamardSem (bit_cases RealizesCleanUnitary)
open StreamingBchComparator (PreservesStoreConst)
open MomSlot0CircuitHalf (padZeroBits)
open FullSysMomSlots0135Concrete (momCoreWires momSysReg momCoinReg)
open MomSlots35Slot3ProjNuclear (shellMu3 shellMu3_lt_seven shellMagCoord3 s3ShellMagCoord3_lt_128
  s3ProjGridBool)
open MomSlots35Slot3ProjNuclear (validShellNu3 s3ProjStepHw negSign3_22 s3U22Core s3S3Core s3C8Core)
open MomSlots35Slot3ProjNuclear (s3Fine30Core s3BParCore s3U16Core)
open TwosCompAndWire0Cancel (projAxisField)
open Slot5MatrixAndScaleCert (signBit3 twosMomentum)
open ModWrapCoarse8PureMomentum (nearestProtonCoord)
open SubvoxelNuclearTrunc36Physics (trunc36Cfg)
open StepBBlock0 (padZeroBits149_clean bitsVal_eq_of_testBit bitsVal_split_add hmPay80)
open StepBBlock0 (embedAlpha107 embedAlpha107_fields zmod2_eq_zero_or_one)
open Prod57BoothHoist (bitsVal_injective bitsVal_slice_eq_div_mod p57ProjW p57S3W p57U38W p57MW)
open Prod57BoothHoist (p57OutW sTrue18WDefault sTrueRawVal sTrueRawValPBuf p57CleanDiagProj
  p57CleanDiagProj_conjTranspose)
open Prod57BoothHoist (p57SeqClean_prog_inv dCleanMsbSub_count_t dCleanMsbSub_count_toff
  msbClearStatic)
open Prod57BoothHoist (msbClearStatic_spec sTrue18FwdPBuf275 sTrue18RevPBuf275
  sTrue18RevPBuf275_spec)
open Prod57BoothHoist (p57ToDynWith_count_t p57ToDynWith_count_toff)
open StepBOuter (coinW coinOkW muW u22WAux top7W bParWAux)
open StepBOuter (pBufW accWAux cat42W validStaticW getU22 getProj)
open StepBOuter (getU22_congr bitsVal_congrAux elecsTrueRawValPBuf_eq rejKick275 rejKick275_spec
  cSwap24_275)
open StepBOuter (cSwap24_275_spec s3Flip275 s3Flip275_spec)
open Slot3Exact216Oracle80 (s3NucleusIdx216 validStaticVal216 RetainedInv216 fwdPrep216_275
  fwdPrep216_275_spec revUncomp216_275)
open Slot3Exact216Oracle80 (revUncomp216_275_spec progMidKick216_437 progMidKick216_437_raw_spec
  tempPhaseProg216_seq_evalBits top7_eq_shellMu3_216)
open Slot3MicroEngineAux (boolToZMod2 getBoolAt initBoolList evalMicroList allBelow TempCtxLiftEx)
open Slot3MicroEngineAux (ctxMicro ctxMicro_scoped ctxLtCompLoop ctxLtCompLoop_countTempAnd
  ctxLtCompLoop_props ctxLtCompLoop_scoped)
open Slot3Outer2344AndRelayWide.Slot3Exact216TruncBr31 (axisStep3_fast_275
  axisStep3_fast_275_eq_orig revTail216_br31_275)
open Slot3Outer2344AndRelayWide.Slot3RevUncompDynPruned (InvRevTailPruned216)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide (isBadA)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide (progNotTarget progNotTarget_evalBits)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide (st0)
open Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide (st1 pStep1)
open Slot3MidKick36_161w (progMidKick216_36_411 progMidKick216_36_411_raw_spec
  progMidKick216_36_411_eq_437)
open Slot3Norm1s36_161w (Norm1sTier clz18Log2 norm1sMant18 clz18Log2_le_17 norm1sHwRowsAux
  norm1sHwProd)
open Slot3Norm1s36_161w (accThr accThr_lt_two_pow_wAcc clz18Ops clz18Ops_meta projNe128Ops
  projNe128OutSlot)
open Slot3Norm1s36_161w (projNe128Ops_meta accLoadRowCliff accLoadThrLoop st0_clean_and_not_badA
  st1_clean_and_not_badA)
open Slot3Norm1s36CoreWideBooth (two_mul_mu_le_clz18Log2 barrel59Ops barrel59Ops_meta subDOh18_15Ops
  subDOh18_15Slot subDOh18_15Ops_meta)
open Slot3Norm1s36CoreWideBooth (subDOh18_15Ops_spec projNe128Ops_spec accLoadThrLoop_eval
  n1s_tier_bounds n1s_norm1sMant18_lt n1s_allBelow_of_noMutBelow)
open Slot3Norm1s36CoreWideBooth (n1sProjW411 n1sU38W411 n1sUKW411 n1sAccFlagW411 n1sMuW411
  n1sOut32W411)
open Slot3Norm1s36CoreWideBooth (n1sValidStaticW411 n1sSTrue18W411 n1sEW411 n1sInBarrelW411
  n1sMantW411 n1s_u38W411_range)
open Slot3Norm1s36CoreWideBooth (n1s_uKW411_range n1s_sTrue18W411_range n1s_sTrue18W411_lt_275
  n1s_sTrue18W411_inj n1s_inBarrelW411_lt_297 n1s_inBarrelW411_inj)
open Slot3Norm1s36CoreWideBooth (n1s_uKW411_bitsVal n1sCtxClz411 n1sCtxBarrel411 n1s_clz18Ops_noMut
  n1s_ctxClz_and_barrel_fwd n1sDBaseRevD18)
open Slot3Norm1s36CoreWideBooth (n1sDLowRowRev n1sDHighRowRev n1sTopRowRevStatic)
open Slot3Norm1s36CoreWideBooth (n1sBoothFwd411 n1sBoothPrefixRevStatic n1sBoothRevStatic411
  n1sDBoothPrefixRev n1s_hwProd_lt_two_pow_wAcc)
open Slot3Norm1s36CoreWideBooth (n1sBoothInv n1sBoothDoneInv n1s_mant_uK_congr n1s_boothFwd411_spec
  n1s_bitsVal_of_nat)
open Slot3Norm1s36CoreWideBooth (n1s_dBaseRevD18_props n1s_lowRowRev_spec n1s_dLowRowRev_props
  n1s_highRowRev_spec n1s_dHighRowRev_props n1s_topRowRev_spec)
open Slot3Norm1s36CoreWideBooth (n1sBoothFwdAnds n1sBoothPrefixRevT n1sBoothRevT
  n1s_boothFwd411_countTempAnd n1s_boothPrefixRev_spec)

/- ## Section 1: `Norm1sTier.tCoreWide` and Active-Register Seam Abbreviations -/

/-- Exact `0 .TOFF` core `T`-count realized by `dCoreNorm1s_262` on `mWork = 262` clean wires. -/
def Norm1sTier.tCoreWide : Norm1sTier → ℕ
  | .t26_18 => 11048
  | .t26_17 => 11192
  | .t26_16 => 11328
  | .t27_17 => 11348
  | .t28_17 => 11504
  | .t29_18 => 11516
  | .t29_17 => 11660
  | .t30_18 => 11672

/-- Radial acceptance predicate for `Norm1sTier` (`Slot3Norm1s36Physics80.norm1sRadAccept`). -/
abbrev norm1sRadAccept (t : Norm1sTier) (mu sTrue u38 : ℕ) : Bool :=
  Slot3Norm1s36Physics80.norm1sRadAccept t mu sTrue u38

/-- Full Slot-3 acceptance predicate on `momCoreWires mPayload`
  (`Slot3Norm1s36Physics80.s3AcceptNorm1s`). -/
noncomputable abbrev s3AcceptNorm1s (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) : Bool :=
  Slot3Norm1s36Physics80.s3AcceptNorm1s t hmPay z

/-- Basis permutation on `momCoreWires mPayload` induced by `s3AcceptNorm1s t`. -/
noncomputable abbrev s3CoreMapNorm1s (t : Norm1sTier) {mPayload : ℕ} (hmPay : 80 ≤ mPayload)
    (z : Fin (2 ^ (momCoreWires mPayload))) : Fin (2 ^ (momCoreWires mPayload)) :=
  Slot3Norm1s36Physics80.s3CoreMapNorm1s t hmPay z

/-- Restricted `107`-wire active swap/rejection map for `Norm1sTier`. -/
noncomputable abbrev swapRejMap107_norm1s (t : Norm1sTier) (α : BitAssignment 107) :
    BitAssignment 107 :=
  Slot3Norm1s36Physics80.swapRejMap107Norm1s t α

/-- `42`-bit catalytic adder shift on `α107` under `trunc36Cfg cfg` and `s3AcceptNorm1s t`. -/
noncomputable abbrev s3Shift42_norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α107 : BitAssignment 107) : ℕ :=
  Slot3Norm1s36Physics80.s3Shift42Norm1s t cfg α107

/-- Active `149`-wire basis permutation realized by `dCoreNorm1s_262 t cfg`. -/
noncomputable abbrev corePerm149_norm1s (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α : BitAssignment 149) : BitAssignment 149 :=
  Slot3Norm1s36Physics80.corePerm149Norm1s t cfg α

/-- Active `149`-wire `ZMod 2` rejection phase exponent realized by `dCoreNorm1s_262 t cfg`. -/
noncomputable abbrev corePhase149_norm1s (t : Norm1sTier) (α : BitAssignment 149) : ZMod 2 :=
  Slot3Norm1s36Physics80.corePhase149Norm1s t α

theorem n1s_if_pos {α : Type*} {c : Prop} {d : Decidable c} {t e : α} (hc : c) :
    @ite α c d t e = t := by
  cases d with
  | isTrue _ => rfl
  | isFalse h => exact absurd hc h

theorem n1s_if_neg {α : Type*} {c : Prop} {d : Decidable c} {t e : α} (hc : ¬ c) :
    @ite α c d t e = e := by
  cases d with
  | isTrue h => exact absurd h hc
  | isFalse _ => rfl

private theorem n1s_dif_pos {α : Sort*} {c : Prop} {d : Decidable c} {t : c → α} {e : ¬ c → α}
    (hc : c) : @dite α c d t e = t hc := by
  cases d with
  | isTrue _ => rfl
  | isFalse h => exact absurd hc h

private theorem n1s_dif_neg {α : Sort*} {c : Prop} {d : Decidable c} {t : c → α} {e : ¬ c → α}
    (hc : ¬ c) : @dite α c d t e = e hc := by
  cases d with
  | isTrue h => exact absurd h hc
  | isFalse _ => rfl

theorem n1s_dyn_count_seq {Var : Type} {n k : ℕ} (d₁ d₂ : DynamicCircuit Var n)
    (g : PrimitiveGate k) : (d₁.seq d₂).count g = d₁.count g + d₂.count g := rfl

theorem n1s_dBoothPrefixRev_counts (t : Norm1sTier) {Var : Type} {n : ℕ}
    (v : Var) (rComb : QRegister 411 n) :
    ∀ (m : ℕ) (hm : m ≤ t.kBits),
      (n1sDBoothPrefixRev t v rComb m hm).count PrimitiveGate.T = n1sBoothPrefixRevT t m ∧
      (n1sDBoothPrefixRev t v rComb m hm).count PrimitiveGate.TOFF = 0
  | 0, _ => ⟨by simp [n1sDBoothPrefixRev, n1sBoothPrefixRevT], by simp [n1sDBoothPrefixRev]⟩
  | 1, _ => by
      dsimp only [n1sDBoothPrefixRev, n1sBoothPrefixRevT]
      split_ifs <;> exact ⟨by simp [DynamicCircuit.count], by simp [DynamicCircuit.count]⟩
  | 2, _ => by
      rw [n1sDBoothPrefixRev, n1sBoothPrefixRevT]
      by_cases hd18 : t.dCut = 18
      · rw [n1s_dif_pos hd18, n1s_if_pos hd18]
        dsimp only [n1sDBaseRevD18]
        exact ⟨by
          simp [p57ToDynWith_count_t, ctxCliffAlloc, TempCtx.countTempAnd,
            dCleanMsbSub_count_t],
            p57ToDynWith_count_toff v rComb _ (dCleanMsbSub_count_toff v rComb _ _ _ _ _ _ _ _ _ _ _
              _
              _ _ _) _⟩
      · rw [n1s_dif_neg hd18, n1s_if_neg hd18]
        have hb := n1s_tier_bounds t
        obtain ⟨hcT2, hcToff2⟩ := n1s_dBoothPrefixRev_counts t v rComb 1 (by omega)
        dsimp only [n1sDLowRowRev]
        exact ⟨by
            simp [DynamicCircuit.count, p57ToDynWith_count_t, ctxCliffAlloc,
              TempCtx.countTempAnd, dCleanMsbSub_count_t, hcT2, n1sBoothPrefixRevT],
          by
            simp [DynamicCircuit.count, hcToff2, p57ToDynWith_count_toff v rComb _
              (dCleanMsbSub_count_toff v rComb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _]⟩
  | m + 3, hm => by
      rw [n1sDBoothPrefixRev, n1sBoothPrefixRevT]
      have hb := n1s_tier_bounds t
      obtain ⟨hcT2, hcToff2⟩ := n1s_dBoothPrefixRev_counts t v rComb (m + 2) (by omega)
      split_ifs <;> dsimp only [n1sDLowRowRev, n1sDHighRowRev] <;>
        exact ⟨by
            simp [DynamicCircuit.count, p57ToDynWith_count_t, ctxCliffAlloc,
              TempCtx.countTempAnd, dCleanMsbSub_count_t, hcT2],
          by
            simp [DynamicCircuit.count, hcToff2, p57ToDynWith_count_toff v rComb _
              (dCleanMsbSub_count_toff v rComb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _]⟩

theorem n1s_realizes_seq_prog411 {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) (rem : ℕ) (hrem : rem ≤ 411)
    (Inv1 Inv2 : BitAssignment 411 → Prop) (p1 p2 : TempPhaseProg 411)
    (d1 d2 : DynamicCircuit Var n) (hR1 : RealizesCleanUnitary v (p57CleanDiagProj rComb rem
    hrem Inv1) d1 (((p1.onRegister rComb).toToffCircuit).eval)) (hR2 : RealizesCleanUnitary v
    (p57CleanDiagProj rComb rem hrem Inv2) d2 (((p2.onRegister rComb).toToffCircuit).eval))
    (hStep : ∀ γ, cleanRem 411 rem γ → Inv1 γ → cleanRem 411 rem (p1.evalBits γ) ∧ Inv2
    (p1.evalBits γ)) : RealizesCleanUnitary v (p57CleanDiagProj rComb rem hrem Inv1)
    (.seq d1 d2) ((((TempPhaseProg.seq p1 p2).onRegister rComb).toToffCircuit).eval) := by
  have hSeq := RealizesCleanUnitary_seq_asym
      (p57CleanDiagProj_conjTranspose rComb rem hrem Inv1)
      (p57CleanDiagProj_conjTranspose rComb rem hrem Inv2) hR1 hR2
      (p57SeqClean_prog_inv rComb p1 hrem hrem hStep)
  have hMul : (((p2.onRegister rComb).toToffCircuit).eval) *
      (((p1.onRegister rComb).toToffCircuit).eval) =
      ((((TempPhaseProg.seq p1 p2).onRegister rComb).toToffCircuit).eval) := by
    simp only [TempPhaseProg.onRegister, TempPhaseProg.toToffCircuit, Circuit.eval_seq]
  rw [hMul] at hSeq
  exact hSeq

theorem n1s_dBoothPrefixRev_props_core (t : Norm1sTier)
    {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)]
    (v : Var) (rComb : QRegister 411 n) :
    ∀ (m : ℕ) (hm : m ≤ t.kBits),
      PreservesStoreConst (n1sDBoothPrefixRev t v rComb m hm) ∧
      ((t.dCut = 18 → m ≠ 1) →
        RealizesCleanUnitary v (p57CleanDiagProj rComb (411 - 379) (by decide) (n1sBoothInv t m))
          (n1sDBoothPrefixRev t v rComb m hm)
          ((((n1sBoothPrefixRevStatic t m hm).onRegister rComb).toToffCircuit).eval))
  | 0, _ =>
      ⟨PreservesStoreConst.circuit _, fun _ ↦ RealizesCleanUnitary.circuit v _ _⟩
  | 1, _ => by
      rw [n1sDBoothPrefixRev, n1sBoothPrefixRevStatic]
      by_cases hd18 : t.dCut = 18
      · rw [n1s_dif_pos hd18, n1s_dif_pos hd18]
        exact ⟨PreservesStoreConst.circuit _, fun hne ↦ absurd rfl (hne hd18)⟩
      · rw [n1s_dif_neg hd18, n1s_dif_neg hd18]
        exact ⟨PreservesStoreConst.circuit _, fun _ ↦ RealizesCleanUnitary.circuit v _ _⟩
  | 2, _ => by
      rw [n1sDBoothPrefixRev, n1sBoothPrefixRevStatic]
      by_cases hd18 : t.dCut = 18
      · rw [n1s_dif_pos hd18, n1s_dif_pos hd18]
        obtain ⟨_, _, hPres, hReal0⟩ := n1s_dBaseRevD18_props t hd18 v rComb
        exact ⟨hPres, fun _ ↦ hReal0⟩
      · rw [n1s_dif_neg hd18, n1s_dif_neg hd18]
        have hb := n1s_tier_bounds t
        obtain ⟨_, _, hPr1, hR1⟩ := n1s_dLowRowRev_props t 1 le_rfl (by omega) (by omega) v rComb
        obtain ⟨hPr2, hR2⟩ := n1s_dBoothPrefixRev_props_core t v rComb 1 (by omega)
        obtain ⟨_, hEv1⟩ := n1s_lowRowRev_spec t 1 le_rfl (by omega) (by omega)
        exact ⟨PreservesStoreConst.seq hPr1 hPr2, fun _ ↦ n1s_realizes_seq_prog411 v rComb
          (411 - 379) (by decide) _ _ _ _ _ _ hR1 (hR2 (fun h ↦ absurd h hd18)) (fun γ hcr hi
          ↦ ⟨(hEv1 γ hcr).2.1, ((hEv1 γ hcr).2.2.2 hi).1⟩)⟩
  | m + 3, hm => by
      rw [n1sDBoothPrefixRev, n1sBoothPrefixRevStatic]
      have hb := n1s_tier_bounds t
      obtain ⟨hPr2, hR2⟩ := n1s_dBoothPrefixRev_props_core t v rComb (m + 2) (by omega)
      by_cases hlow : m + 2 < t.dCut
      · rw [n1s_dif_pos hlow, n1s_dif_pos hlow]
        obtain ⟨_, _, hPr1, hR1⟩ :=
          n1s_dLowRowRev_props t (m + 2) (by omega) hlow (by omega) v rComb
        obtain ⟨_, hEv1⟩ := n1s_lowRowRev_spec t (m + 2) (by omega) hlow (by omega)
        exact ⟨PreservesStoreConst.seq hPr1 hPr2, fun _ ↦
          n1s_realizes_seq_prog411 v rComb (411 - 379) (by decide) _ _ _ _ _ _
            hR1 (hR2 (fun _ ↦ by omega))
            (fun γ hcr hi ↦ ⟨(hEv1 γ hcr).2.1, ((hEv1 γ hcr).2.2.2 hi).1⟩)⟩
      · rw [n1s_dif_neg hlow, n1s_dif_neg hlow]
        have heq3 : t.dCut + ((m + 2) - t.dCut) + 1 = m + 3 := by omega
        have heq2 : t.dCut + ((m + 2) - t.dCut) = m + 2 := by omega
        obtain ⟨_, _, hPr1, hR1⟩ := n1s_dHighRowRev_props t ((m + 2) - t.dCut) (by omega) v rComb
        obtain ⟨_, hEv1⟩ := n1s_highRowRev_spec t ((m + 2) - t.dCut) (by omega)
        rw [heq3] at hR1
        exact ⟨PreservesStoreConst.seq hPr1 hPr2, fun _ ↦
          n1s_realizes_seq_prog411 v rComb (411 - 379) (by decide) _ _ _ _ _ _
            hR1 (hR2 (fun _ ↦ by omega))
            (fun γ hcr hi ↦ by
              rw [← heq3] at hi
              have h1 := ((hEv1 γ hcr).2.2.2 hi).1
              rw [heq2] at h1
              exact ⟨(hEv1 γ hcr).2.1, h1⟩)⟩

theorem n1s_dBoothPrefixRev_props (t : Norm1sTier) {Var : Type} [Fintype Var]
    [DecidableEq Var] {n : ℕ} [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) (m : ℕ)
    (hm : m ≤ t.kBits) : (n1sDBoothPrefixRev t v rComb m hm).count PrimitiveGate.T =
    n1sBoothPrefixRevT t m ∧ (n1sDBoothPrefixRev t v rComb m hm).count PrimitiveGate.TOFF = 0
    ∧ PreservesStoreConst (n1sDBoothPrefixRev t v rComb m hm) ∧ ((t.dCut = 18 → m ≠ 1) →
    RealizesCleanUnitary v (p57CleanDiagProj rComb (411 - 379) (by decide) (n1sBoothInv t m))
    (n1sDBoothPrefixRev t v rComb m hm) ((((n1sBoothPrefixRevStatic t m hm).onRegister
    rComb).toToffCircuit).eval)) :=
  let ⟨hcT, hcToff⟩ := n1s_dBoothPrefixRev_counts t v rComb m hm
  let ⟨hPr, hR⟩ := n1s_dBoothPrefixRev_props_core t v rComb m hm
  ⟨hcT, hcToff, hPr, hR⟩

theorem n1s_boothRevStatic411_spec (t : Norm1sTier) :
    let p := n1sBoothRevStatic411 t
    ValidCleanRem 411 (411 - 379) p ∧
      (∀ β : BitAssignment 411, cleanRem 411 (411 - 379) β →
        p.evalSign β = 0 ∧
        cleanRem 411 (411 - 379) (p.evalBits β) ∧
        (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) → p.evalBits β q = β q) ∧
        (n1sBoothDoneInv t β → ∀ k : Fin 32, p.evalBits β (n1sOut32W411 k) = 0)) := by
  dsimp only [n1sBoothRevStatic411]
  have hb := n1s_tier_bounds t
  obtain ⟨hv1, hEv1⟩ := n1s_topRowRev_spec t
  obtain ⟨hv2, hEv2⟩ := n1s_boothPrefixRev_spec t t.kBits le_rfl
  refine ⟨⟨411 - 379, by decide, hv1, hv2, fun β hβ ↦ (hEv1 β hβ).2.1⟩, fun β hβ ↦ ?_⟩
  obtain ⟨hs1, hcl1, hnon1, hinv1⟩ := hEv1 β hβ
  let β₁ := (n1sTopRowRevStatic t).evalBits β
  obtain ⟨hs2, hcl2, hnon2, hinv2⟩ := hEv2 β₁ hcl1
  refine ⟨by
      change (n1sTopRowRevStatic t).evalSign β +
        (n1sBoothPrefixRevStatic t t.kBits le_rfl).evalSign β₁ = 0; rw [hs1, hs2, add_zero], hcl2,
    fun q hq ↦ (hnon2 q hq).trans (hnon1 q hq), fun hDone k ↦ ?_⟩
  have hInv0 := hinv2 (fun _ ↦ by omega) (hinv1 hDone).1
  have hz : bitsVal (fun j : Fin 32 ↦ (n1sBoothPrefixRevStatic t t.kBits le_rfl).evalBits β₁
      (n1sOut32W411 j)) = bitsVal (fun _ : Fin 32 ↦ (0 : ZMod 2)) := by
    simpa [n1sBoothInv, norm1sHwRowsAux, bitsVal] using hInv0
  exact congrFun (bitsVal_injective hz) k

theorem n1s_fwdBits_append {M : ℕ} (F G : TempCtx M) (β : BitAssignment M) :
    (F.append G).fwdBits β = G.fwdBits (F.fwdBits β) := by
  induction F generalizing β with
  | hole => rfl
  | seqPre _ _ ih => exact ih _
  | seqPost _ _ ih => exact ih _
  | tempAnd _ _ _ _ _ _ _ ih => exact ih _

theorem n1s_subDOh18_15Slot_bounds (d : Fin 18) :
    8 ≤ subDOh18_15Slot d ∧ subDOh18_15Slot d < 28 := by
  fin_cases d <;> decide

theorem n1s_projNe128Slot_bounds : 8 ≤ projNe128OutSlot ∧ projNe128OutSlot < 15 := by
  decide

/-- `8`-bit `(mu, e)` input map `mu[0..3) ++ e[0..5)` feeding `subDOh18_15Ops` (`< 297`). -/
def n1sInSub8W411 (i : Fin 8) : Wire 411 :=
  if h : i.val < 3 then n1sMuW411 ⟨i.val, h⟩ else n1sEW411 ⟨i.val - 3, by omega⟩

theorem n1s_inSub8W411_lt_297 (i : Fin 8) : (n1sInSub8W411 i).val < 297 := by
  unfold n1sInSub8W411
  split_ifs <;> simp [n1sMuW411, n1sEW411] <;> omega

theorem n1s_inSub8W411_inj : Function.Injective n1sInSub8W411 := by
  intro i j hij
  have hv := congrArg Fin.val hij
  dsimp only [n1sInSub8W411] at hv
  split_ifs at hv <;> simp only [n1sMuW411, n1sEW411] at hv <;> exact Fin.ext (by omega)

theorem n1s_projW411_inj (w : Fin 3) : Function.Injective (n1sProjW411 w) := by
  intro a b hab
  have hv := congrArg Fin.val hab; dsimp [n1sProjW411] at hv; exact Fin.ext (by omega)

/-- One-hot wire `oh_d` (`d : Fin 18`) in `[297..317)` produced by `subDOh18_15Ops`. -/
def n1sOhAux (d : Fin 18) : Wire 411 :=
  ⟨297 + (subDOh18_15Slot d - 8), by have := (n1s_subDOh18_15Slot_bounds d).2; omega⟩

/-- Projectile axis `w` non-grid output wire in `[317 + 7*w .. 324 + 7*w)`. -/
def n1sNeAxisW411 (w : Fin 3) : Wire 411 :=
  ⟨317 + 7 * w.val + (projNe128OutSlot - 8), by have := n1s_projNe128Slot_bounds.2; omega⟩

/-- Combined `validStatic * projOk` wire `340` on `Wire 411`. -/
abbrev n1sValidProjW411 : Wire 411 := ⟨340, by decide⟩

/-- Threshold loader wire slice `[341 .. 341 + t.wAcc)` (`< 373`). -/
def n1sThrW411 (t : Norm1sTier) (j : Fin t.wAcc) : Wire 411 :=
  ⟨341 + j.val, by have := t.wAcc_le_32; omega⟩

/-- Hardware product low `t.wAcc` bits `[201 .. 201 + t.wAcc)` on `Wire 411`. -/
def n1sOutAccW411 (t : Norm1sTier) (j : Fin t.wAcc) : Wire 411 :=
  n1sOut32W411 ⟨j.val, lt_of_lt_of_le j.isLt t.wAcc_le_32⟩

/-- Comparator output wire `373 + t.wAcc` (`<= 405 < 406`) of `ctxLtCompLoop`. -/
def n1sLtOutW411 (t : Norm1sTier) : Wire 411 :=
  ⟨373 + t.wAcc, by have := t.wAcc_le_32; omega⟩

theorem n1s_thrWire411_inj (t : Norm1sTier) : Function.Injective (n1sThrW411 t) := by
  intro a b hab
  have hv := congrArg Fin.val hab; dsimp [n1sThrW411] at hv; exact Fin.ext (by omega)

theorem n1s_ohAux_ne_thrWire411 (t : Norm1sTier) (d : Fin 18) (j : Fin t.wAcc) :
    n1sOhAux d ≠ n1sThrW411 t j :=
  wire_ne_of_lt (by
    have := (n1s_subDOh18_15Slot_bounds d).2
    dsimp [n1sOhAux, n1sThrW411]; omega)

theorem n1s_accLoadRowCliff_props {M bound : ℕ} {mutW : Wire M → Prop} (val : ℕ) (oh : Wire M)
    (hoh_lt : oh.val < bound) (hnoh : ¬ mutW oh) :
    ∀ (w : ℕ) (thrW : Fin w → Wire M) (hne : ∀ j : Fin w, oh ≠ thrW j),
      (∀ j, (thrW j).val < bound) → (∀ j, ¬ mutW (thrW j)) →
      (accLoadRowCliff val oh w thrW hne).SupportsBelow bound ∧
        CliffDisjoint mutW (accLoadRowCliff val oh w thrW hne)
  | 0, _, _, _, _ => ⟨trivial, trivial⟩
  | w + 1, thrW, hne, hlt, hnm => by
      dsimp only [accLoadRowCliff]
      obtain ⟨hsR, hdR⟩ := n1s_accLoadRowCliff_props (val / 2) oh hoh_lt hnoh w
        (fun j ↦ thrW j.succ) (fun j ↦ hne j.succ) (fun j ↦ hlt j.succ) (fun j ↦ hnm j.succ)
      by_cases hv : val % 2 = 1
      · rw [n1s_if_pos hv]
        exact ⟨⟨⟨hoh_lt, hlt 0⟩, hsR⟩, ⟨⟨hnoh, hnm 0⟩, hdR⟩⟩
      · rw [n1s_if_neg hv]
        exact ⟨hsR, hdR⟩

theorem n1s_accLoadThrLoop_props {M bound : ℕ} {mutW : Wire M → Prop}
    (kBits dCut wAcc : ℕ) (thrW : Fin wAcc → Wire M) (ohW : Fin 18 → Wire M)
    (hne : ∀ (d : Fin 18) (j : Fin wAcc), ohW d ≠ thrW j)
    (hoh_lt : ∀ d, (ohW d).val < bound) (hthr_lt : ∀ j, (thrW j).val < bound)
    (hnoh : ∀ d, ¬ mutW (ohW d)) (hnthr : ∀ j, ¬ mutW (thrW j)) :
    ∀ (rem : ℕ) (hrem : rem ≤ 18),
      (accLoadThrLoop kBits dCut wAcc thrW rem hrem ohW hne).SupportsBelow bound ∧
        CliffDisjoint mutW (accLoadThrLoop kBits dCut wAcc thrW rem hrem ohW hne)
  | 0, _ => ⟨trivial, trivial⟩
  | rem + 1, hrem => by
      dsimp only [accLoadThrLoop]
      let dIdx : Fin 18 := ⟨18 - (rem + 1), by omega⟩
      obtain ⟨hs1, hd1⟩ := n1s_accLoadRowCliff_props (accThr kBits dCut dIdx.val) (ohW dIdx)
        (hoh_lt dIdx) (hnoh dIdx) wAcc thrW (fun j ↦ hne dIdx j) hthr_lt hnthr
      obtain ⟨hs2, hd2⟩ := n1s_accLoadThrLoop_props kBits dCut wAcc thrW ohW hne
        hoh_lt hthr_lt hnoh hnthr rem (by omega)
      exact ⟨⟨hs1, hs2⟩, ⟨hd1, hd2⟩⟩

/-- One-hot subtractor micro-context on `[297..317)` (`15` `TempAnd`s). -/
def n1sKSub411 : TempCtx 411 := ctxMicro n1sInSub8W411 n1s_inSub8W411_inj 297 20 15
    n1s_inSub8W411_lt_297 subDOh18_15Ops subDOh18_15Ops_meta (by decide)

theorem n1s_kSub411_scoped :
    n1sKSub411.countTempAnd = 15 ∧
    (∀ {mutW : Wire 411 → Prop},
      (∀ i, ¬ mutW (n1sInSub8W411 i)) → (∀ w : Wire 411, 297 ≤ w.val → ¬ mutW w) →
      n1sKSub411.DisjointFrom mutW ∧ n1sKSub411.SupportsBelowCtx (297 + 20)) ∧
    TempCtxLiftEx 297 (297 + 20) n1sKSub411 ∧
    (∀ β : BitAssignment 411, cleanRem 411 (411 - 297) β →
      let m := bitsVal (fun i ↦ β (n1sInSub8W411 i))
      let stOut := evalMicroList 8 subDOh18_15Ops (initBoolList 8 (8 + 20) m)
      cleanRem 411 (411 - (297 + 20)) (n1sKSub411.fwdBits β) ∧
      (allBelow 8 (fun i ↦ getBoolAt stOut i == m.testBit i) = true →
        ∀ w : Wire 411, w.val < 297 → n1sKSub411.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hlo : 8 ≤ s) (hhi : s < 8 + 20),
        n1sKSub411.fwdBits β ⟨297 + (s - 8), by omega⟩ = boolToZMod2 (getBoolAt stOut s))) :=
  ctxMicro_scoped n1sInSub8W411 n1s_inSub8W411_inj 297 20 15
    n1s_inSub8W411_lt_297 subDOh18_15Ops subDOh18_15Ops_meta (by decide)

/-- Projectile non-grid check micro-context on `[cur .. cur + 7)` (`7` `TempAnd`s). -/
def n1sKNe411 (w : Fin 3) (cur : ℕ) (hlo24 : 24 ≤ cur) (hcur : cur + 7 ≤ 411) : TempCtx 411 :=
  ctxMicro (n1sProjW411 w) (n1s_projW411_inj w) cur 7 7
    (fun b ↦ by dsimp [n1sProjW411]; omega) projNe128Ops projNe128Ops_meta hcur

theorem n1s_kNe411_scoped (w : Fin 3) (cur : ℕ) (hlo24 : 24 ≤ cur) (hcur : cur + 7 ≤ 411) :
    (n1sKNe411 w cur hlo24 hcur).countTempAnd = 7 ∧
    (∀ {mutW : Wire 411 → Prop},
      (∀ i, ¬ mutW (n1sProjW411 w i)) → (∀ q : Wire 411, cur ≤ q.val → ¬ mutW q) →
      (n1sKNe411 w cur hlo24 hcur).DisjointFrom mutW ∧
        (n1sKNe411 w cur hlo24 hcur).SupportsBelowCtx (cur + 7)) ∧
    TempCtxLiftEx cur (cur + 7) (n1sKNe411 w cur hlo24 hcur) ∧
    (∀ β : BitAssignment 411, cleanRem 411 (411 - cur) β →
      let m := bitsVal (fun i ↦ β (n1sProjW411 w i))
      let stOut := evalMicroList 8 projNe128Ops (initBoolList 8 (8 + 7) m)
      cleanRem 411 (411 - (cur + 7)) ((n1sKNe411 w cur hlo24 hcur).fwdBits β) ∧
      (allBelow 8 (fun i ↦ getBoolAt stOut i == m.testBit i) = true →
        ∀ q : Wire 411, q.val < cur → (n1sKNe411 w cur hlo24 hcur).fwdBits β q = β q) ∧
      (∀ (s : ℕ) (hlo : 8 ≤ s) (hhi : s < 8 + 7),
        (n1sKNe411 w cur hlo24 hcur).fwdBits β ⟨cur + (s - 8), by omega⟩ =
          boolToZMod2 (getBoolAt stOut s))) :=
  ctxMicro_scoped (n1sProjW411 w) (n1s_projW411_inj w) cur 7 7
    (fun b ↦ by dsimp [n1sProjW411]; omega) projNe128Ops projNe128Ops_meta hcur

/-- Guard context on `[297 .. 373 + t.wAcc + 1)` (`15 + 21 + 3 + t.wAcc` `TempAnd`s, `< 406`). -/
def n1sCtxGuard411 (t : Norm1sTier) : TempCtx 411 :=
  let K_sub := n1sKSub411
  let K_ne0 := n1sKNe411 0 317 (by decide) (by decide)
  let K_ne1 := n1sKNe411 1 324 (by decide) (by decide)
  let K_ne2 := n1sKNe411 2 331 (by decide) (by decide)
  let K_p01 := ctxTempBit (n1sNeAxisW411 0) (n1sNeAxisW411 1) ⟨338, by decide⟩
    (wire_ne_of_lt (by have := n1s_projNe128Slot_bounds; dsimp [n1sNeAxisW411]; omega))
    (wire_ne_of_lt (by have := n1s_projNe128Slot_bounds; dsimp [n1sNeAxisW411]; omega))
    (wire_ne_of_lt (by have := n1s_projNe128Slot_bounds; dsimp [n1sNeAxisW411]; omega))
  let K_pok := ctxTempBit ⟨338, by decide⟩ (n1sNeAxisW411 2) ⟨339, by decide⟩
    (wire_ne_of_gt (by have := n1s_projNe128Slot_bounds; dsimp [n1sNeAxisW411]; omega))
    (by decide)
    (wire_ne_of_lt (by have := n1s_projNe128Slot_bounds; dsimp [n1sNeAxisW411]; omega))
  let K_vp := ctxTempBit n1sValidStaticW411 ⟨339, by decide⟩ n1sValidProjW411
    (by decide) (by decide) (by decide)
  let K_thr := ctxCliffAlloc (accLoadThrLoop t.kBits t.dCut t.wAcc (n1sThrW411 t)
    18 le_rfl n1sOhAux (n1s_ohAux_ne_thrWire411 t))
  let K_lt := ctxLtCompLoop t.wAcc 373 (by have := t.wAcc_le_32; omega)
    (n1sOutAccW411 t) (n1sThrW411 t)
    (fun j ↦ wire_ne_of_lt (by
      have :=
        t.wAcc_le_32; dsimp [n1sOutAccW411, n1sOut32W411, n1sThrW411]; omega))
    (fun j ↦ by have := t.wAcc_le_32; dsimp [n1sOutAccW411, n1sOut32W411]; omega)
    (fun j ↦ by have := t.wAcc_le_32; dsimp [n1sThrW411]; omega)
  K_sub.append (K_ne0.append (K_ne1.append (K_ne2.append
    (K_p01.append (K_pok.append (K_vp.append (K_thr.append K_lt)))))))

theorem n1s_countTempAnd_append {M : ℕ} (F G : TempCtx M) :
    (F.append G).countTempAnd = F.countTempAnd + G.countTempAnd := by
  induction F with
  | hole => simp [TempCtx.append, TempCtx.countTempAnd]
  | seqPre _ _ ih => simp [TempCtx.append, TempCtx.countTempAnd, ih]
  | seqPost _ _ ih => simp [TempCtx.append, TempCtx.countTempAnd, ih]
  | tempAnd _ _ _ _ _ _ _ ih => simp [TempCtx.append, TempCtx.countTempAnd, ih]; omega

theorem n1s_fwdBits_mut {M : ℕ} {mutW : Wire M → Prop} {K : TempCtx M}
    (hDisj : K.DisjointFrom mutW) (β : BitAssignment M) {w : Wire M} (hw : mutW w) :
    K.fwdBits β w = β w := by
  induction K generalizing β with
  | hole => rfl
  | seqPre c _ ih => exact (ih hDisj.2 (c.eval β)).trans (hDisj.1.eval_mut β hw)
  | seqPost _ _ ih => exact ih hDisj.1 β
  | tempAnd _ _ anc _ _ _ _ ih =>
      exact (ih hDisj.2.2.2 _).trans
        (Function.update_of_ne (fun (heq : w = anc) ↦ hDisj.2.2.1 (heq ▸ hw)) _ _)

theorem n1s_liftEx_append {M cur mid next : ℕ} {F G : TempCtx M}
    (hF : TempCtxLiftEx cur mid F) (hG : TempCtxLiftEx mid next G) :
    TempCtxLiftEx cur next (F.append G) := by
  unfold TempCtxLiftEx
  intro _ _ _ hBody
  exact TempCtxLiftEx.append hF hG hBody

private theorem n1s_outAcc_ne_thr (t : Norm1sTier) (j : Fin t.wAcc) :
    n1sOutAccW411 t j ≠ n1sThrW411 t j :=
  wire_ne_of_lt (by have := t.wAcc_le_32; dsimp [n1sOutAccW411, n1sOut32W411, n1sThrW411]; omega)

private theorem n1s_outAcc_lt_373 (t : Norm1sTier) (j : Fin t.wAcc) :
    (n1sOutAccW411 t j).val < 373 := by
  have := t.wAcc_le_32; dsimp [n1sOutAccW411, n1sOut32W411]; omega

private theorem n1s_thr_lt_373 (t : Norm1sTier) (j : Fin t.wAcc) :
    (n1sThrW411 t j).val < 373 := by
  have := t.wAcc_le_32; dsimp [n1sThrW411]; omega

theorem n1s_ctxGuard411_pkg (t : Norm1sTier) :
    let K := n1sCtxGuard411 t
    let mutAcc : Wire 411 → Prop := fun q ↦ q = n1sAccFlagW411
    K.countTempAnd = 15 + 21 + 3 + t.wAcc ∧
    K.DisjointFrom mutAcc ∧
    K.SupportsBelowCtx (373 + t.wAcc + 1) ∧
    TempCtxLiftEx 297 (373 + t.wAcc + 1) K := by
  have hb := t.wAcc_le_32
  dsimp only [n1sCtxGuard411]
  obtain ⟨hc0, hp0, hl0, _⟩ := n1s_kSub411_scoped
  obtain ⟨hc1, hp1, hl1, _⟩ := n1s_kNe411_scoped 0 317 (by decide) (by decide)
  obtain ⟨hc2, hp2, hl2, _⟩ := n1s_kNe411_scoped 1 324 (by decide) (by decide)
  obtain ⟨hc3, hp3, hl3, _⟩ := n1s_kNe411_scoped 2 331 (by decide) (by decide)
  let mutAcc : Wire 411 → Prop := fun q ↦ q = n1sAccFlagW411
  have hn_ge297 {c : ℕ} (hc : 297 ≤ c) : ∀ w : Wire 411, c ≤ w.val → ¬ mutAcc w :=
    fun w hw h ↦ by subst h; dsimp [n1sAccFlagW411] at hw; omega
  have hn_sub : ∀ i, ¬ mutAcc (n1sInSub8W411 i) := fun i h ↦ by
    have hv := congrArg Fin.val h
    dsimp only [n1sInSub8W411, n1sAccFlagW411] at hv
    split_ifs at hv <;> simp only [n1sMuW411, n1sEW411] at hv <;> omega
  have hn_proj (w : Fin 3) (b : Fin 8) : ¬ mutAcc (n1sProjW411 w b) := fun h ↦ by
    have hv := congrArg Fin.val h; dsimp [n1sProjW411, n1sAccFlagW411] at hv; omega
  obtain ⟨hd0, hs0⟩ := hp0 hn_sub (hn_ge297 le_rfl)
  obtain ⟨hd1, hs1⟩ := hp1 (hn_proj 0) (hn_ge297 (by decide))
  obtain ⟨hd2, hs2⟩ := hp2 (hn_proj 1) (hn_ge297 (by decide))
  obtain ⟨hd3, hs3⟩ := hp3 (hn_proj 2) (hn_ge297 (by decide))
  obtain ⟨hsThr, hdThr⟩ := n1s_accLoadThrLoop_props (bound := 373) (mutW := mutAcc)
    t.kBits t.dCut t.wAcc (n1sThrW411 t) n1sOhAux (n1s_ohAux_ne_thrWire411 t)
    (fun d ↦ by have := (n1s_subDOh18_15Slot_bounds d).2; dsimp [n1sOhAux]; omega)
    (n1s_thr_lt_373 t)
    (fun d h ↦ by have hv := congrArg Fin.val h; dsimp [n1sOhAux, n1sAccFlagW411] at hv; omega)
    (fun j h ↦ by have hv := congrArg Fin.val h; dsimp [n1sThrW411, n1sAccFlagW411] at hv; omega)
    18 le_rfl
  obtain ⟨hdLt, hsLt⟩ := ctxLtCompLoop_props (mutW := mutAcc) t.wAcc 373 (by omega)
    (n1sOutAccW411 t) (n1sThrW411 t) (n1s_outAcc_ne_thr t)
    (n1s_outAcc_lt_373 t) (n1s_thr_lt_373 t)
    (fun j h ↦ by
      have hv :=
        congrArg Fin.val h; dsimp [n1sOutAccW411, n1sOut32W411, n1sAccFlagW411] at hv; omega)
    (fun j h ↦ by have hv := congrArg Fin.val h; dsimp [n1sThrW411, n1sAccFlagW411] at hv; omega)
    (hn_ge297 (by decide))
  have hcLt := ctxLtCompLoop_countTempAnd t.wAcc 373 (by omega) (n1sOutAccW411 t) (n1sThrW411 t)
    (n1s_outAcc_ne_thr t) (n1s_outAcc_lt_373 t) (n1s_thr_lt_373 t)
  have hne_ne : ∀ w : Fin 3, ¬ mutAcc (n1sNeAxisW411 w) := fun w h ↦ by
    have hv := congrArg Fin.val h; dsimp [n1sNeAxisW411, n1sAccFlagW411] at hv; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw[n1s_countTempAnd_append, hc0, n1s_countTempAnd_append, hc1, n1s_countTempAnd_append,
      hc2, n1s_countTempAnd_append, hc3, n1s_countTempAnd_append, n1s_countTempAnd_append,
      n1s_countTempAnd_append, n1s_countTempAnd_append, hcLt]
    dsimp only [ctxTempBit, ctxCliffAlloc, TempCtx.countTempAnd]
    omega
  · exact TempCtx.disjointFrom_append hd0
      (TempCtx.disjointFrom_append hd1
        (TempCtx.disjointFrom_append hd2
          (TempCtx.disjointFrom_append hd3
            (TempCtx.disjointFrom_append ⟨hne_ne 0, hne_ne 1, by decide, trivial⟩
              (TempCtx.disjointFrom_append ⟨by decide, hne_ne 2, by decide, trivial⟩
                (TempCtx.disjointFrom_append ⟨by decide, by decide, by decide, trivial⟩
                  (TempCtx.disjointFrom_append ⟨hdThr, trivial, CliffDisjoint.inv hdThr⟩ hdLt)))))))
  · exact TempCtx.supportsBelowCtx_append (by omega) hs0
      (TempCtx.supportsBelowCtx_append (by omega) hs1
        (TempCtx.supportsBelowCtx_append (by omega) hs2
          (TempCtx.supportsBelowCtx_append (by omega) hs3
            (TempCtx.supportsBelowCtx_append (c₁ := 339) (by omega) ⟨by decide, trivial⟩
              (TempCtx.supportsBelowCtx_append (c₁ := 340) (by omega) ⟨by decide, trivial⟩
                (TempCtx.supportsBelowCtx_append (c₁ := 341) (by omega) ⟨by decide, trivial⟩
                  (TempCtx.supportsBelowCtx_append (c₁ := 373) (by omega)
                    ⟨hsThr, trivial, CliffProg.inv_supportsBelow _ hsThr⟩ hsLt)))))))
  · have hl_p01 : TempCtxLiftEx 338 339 _ := TempCtxLiftEx.tempBit (M := 411) 338 (by decide)
      (n1sNeAxisW411 0) (n1sNeAxisW411 1)
      (wire_ne_of_lt (by have := n1s_projNe128Slot_bounds; dsimp [n1sNeAxisW411]; omega))
      (by have := n1s_projNe128Slot_bounds; dsimp [n1sNeAxisW411]; omega)
      (by have := n1s_projNe128Slot_bounds; dsimp [n1sNeAxisW411]; omega)
    have hl_pok : TempCtxLiftEx 339 340 _ := TempCtxLiftEx.tempBit (M := 411) 339 (by decide)
      ⟨338, by decide⟩ (n1sNeAxisW411 2)
      (wire_ne_of_gt (by have := n1s_projNe128Slot_bounds; dsimp [n1sNeAxisW411]; omega))
      (by decide)
      (by have := n1s_projNe128Slot_bounds; dsimp [n1sNeAxisW411]; omega)
    have hl_vp : TempCtxLiftEx 340 373 _ := TempCtxLiftEx.mono
      (TempCtxLiftEx.tempBit (M := 411) 340 (by decide)
        n1sValidStaticW411 ⟨339, by decide⟩ (by decide) (by decide) (by decide) :
          TempCtxLiftEx 340 341 _)
      le_rfl (by decide : 341 ≤ 373) (by decide)
    have hl_thr : TempCtxLiftEx 373 373 _ :=
      TempCtxLiftEx.cliff (M := 411) 373 (by decide) _ hsThr
    have hl_lt : TempCtxLiftEx 373 (373 + t.wAcc + 1) _ :=
      TempCtxLiftEx.ltCompLoop (M := 411) t.wAcc 373 (by omega)
        (n1sOutAccW411 t) (n1sThrW411 t) (n1s_outAcc_ne_thr t)
        (n1s_outAcc_lt_373 t) (n1s_thr_lt_373 t)
    unfold TempCtxLiftEx
    intro leaf body sBody hBody
    exact (n1s_liftEx_append hl0 (n1s_liftEx_append hl1 (n1s_liftEx_append hl2
      (n1s_liftEx_append hl3 (n1s_liftEx_append hl_p01 (n1s_liftEx_append hl_pok
      (n1s_liftEx_append hl_vp (n1s_liftEx_append hl_thr hl_lt)))))))) hBody

theorem n1s_inSub8_bitsVal (β : BitAssignment 411) : bitsVal
    (fun i : Fin 8 ↦ β (n1sInSub8W411 i)) = bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) + 8 *
    bitsVal (fun b : Fin 5 ↦ β (n1sEW411 b)) := by
  let f : Fin (3 + 5) → ZMod 2 := fun i ↦ β (n1sInSub8W411 i)
  have hsp := bitsVal_split_add 3 5 f
  have hlo : (fun i : Fin 3 ↦ f ⟨i.val, by omega⟩) = fun i ↦ β (n1sMuW411 i) :=
    funext fun i ↦ by dsimp [f, n1sInSub8W411]; rw [n1s_dif_pos i.isLt]
  have hhi : (fun b : Fin 5 ↦ f ⟨3 + b.val, by omega⟩) = fun b ↦ β (n1sEW411 b) :=
    funext fun b ↦ by
      dsimp [f, n1sInSub8W411]
      rw [n1s_dif_neg (by omega)]
      exact congrArg (fun k ↦ β (n1sEW411 k)) (Fin.ext (by dsimp; omega))
  rw [hlo, hhi] at hsp
  exact hsp

theorem n1s_ctxTempBit_fwdBits {M : ℕ} (a b c : Wire M) (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c)
    (γ : BitAssignment M) :
    (ctxTempBit a b c h1 h2 h3).fwdBits γ = Function.update γ c (γ c + γ a * γ b) := rfl

theorem n1s_ctxCliffAlloc_fwdBits {M : ℕ} (p : CliffProg M) (γ : BitAssignment M) :
    (ctxCliffAlloc p).fwdBits γ = p.eval γ := rfl

private theorem n1s_kNe411_eval_axis (w : Fin 3) (cur : ℕ) (h24 : 24 ≤ cur)
    (hcur : cur + 7 ≤ 411) (hw_eq : cur = 317 + 7 * w.val) (γ : BitAssignment 411)
    (hcl : cleanRem 411 (411 - cur) γ) :
    let γ' := (n1sKNe411 w cur h24 hcur).fwdBits γ
    cleanRem 411 (411 - (cur + 7)) γ' ∧
    (∀ q : Wire 411, q.val < cur → γ' q = γ q) ∧
    γ' (n1sNeAxisW411 w) = boolToZMod2 (decide (bitsVal (fun b ↦ γ (n1sProjW411 w b)) ≠ 128)) := by
  obtain ⟨_, _, _, hEv⟩ := n1s_kNe411_scoped w cur h24 hcur
  obtain ⟨hcl', hpr_raw, hout⟩ := hEv γ hcl
  have hlt := n1s_projNe128Slot_bounds
  have hw : n1sNeAxisW411 w = ⟨cur + (projNe128OutSlot - 8), by omega⟩ :=
    Fin.ext (by dsimp [n1sNeAxisW411]; omega)
  exact ⟨hcl', hpr_raw (projNe128Ops_spec _ (bitsVal_lt_two_pow _)).1,
    by rw [hw, hout projNe128OutSlot hlt.1 hlt.2, (projNe128Ops_spec _ (bitsVal_lt_two_pow _)).2]⟩

theorem n1s_ctxGuard411_fwd (t : Norm1sTier) (β₁ : BitAssignment 411)
    (hcl₁ : cleanRem 411 (411 - 297) β₁) :
    let δ := (n1sCtxGuard411 t).fwdBits β₁
    let mu := bitsVal (fun i : Fin 3 ↦ β₁ (n1sMuW411 i))
    let e := bitsVal (fun b : Fin 5 ↦ β₁ (n1sEW411 b))
    let outVal := bitsVal (fun k : Fin 32 ↦ β₁ (n1sOut32W411 k))
    cleanRem 411 (411 - (373 + t.wAcc + 1)) δ ∧
    δ n1sAccFlagW411 = β₁ n1sAccFlagW411 ∧
    δ n1sValidProjW411 =
      β₁ n1sValidStaticW411 *
        boolToZMod2 (decide (bitsVal (fun b ↦ β₁ (n1sProjW411 0 b)) ≠ 128) &&
          decide (bitsVal (fun b ↦ β₁ (n1sProjW411 1 b)) ≠ 128) &&
          decide (bitsVal (fun b ↦ β₁ (n1sProjW411 2 b)) ≠ 128)) ∧
    (mu < 7 → 2 * mu ≤ e → e ≤ 17 → outVal < 2 ^ t.wAcc →
      δ (n1sLtOutW411 t) =
        boolToZMod2 (decide (outVal < accThr t.kBits t.dCut (e - 2 * mu)))) := by
  intro δ mu e outVal
  have hb := t.wAcc_le_32
  have hAccEq : δ n1sAccFlagW411 = β₁ n1sAccFlagW411 :=
    n1s_fwdBits_mut (n1s_ctxGuard411_pkg t).2.1 β₁ rfl
  obtain ⟨_, _, _, hSubEv⟩ := n1s_kSub411_scoped
  obtain ⟨hcl₀, hpr₀_raw, hout₀⟩ := hSubEv β₁ hcl₁
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀, n1sKSub411.fwdBits β₁ = γ₀ := ⟨_, rfl⟩
  rw [hγ₀] at hcl₀ hpr₀_raw
  have hpr₀ : ∀ w : Wire 411, w.val < 297 → γ₀ w = β₁ w :=
    hpr₀_raw (subDOh18_15Ops_spec _ (bitsVal_lt_two_pow _)).1
  obtain ⟨hclN0, hprN0, hNe0⟩ := n1s_kNe411_eval_axis 0 317 (by decide) (by decide) rfl γ₀ hcl₀
  obtain ⟨γ₁, hγ₁⟩ : ∃ γ₁, (n1sKNe411 0 317 (by decide) (by decide)).fwdBits γ₀ = γ₁ := ⟨_, rfl⟩
  rw [hγ₁] at hclN0 hprN0 hNe0
  obtain ⟨hclN1, hprN1, hNe1⟩ := n1s_kNe411_eval_axis 1 324 (by decide) (by decide) rfl γ₁ hclN0
  obtain ⟨γ₂, hγ₂⟩ : ∃ γ₂, (n1sKNe411 1 324 (by decide) (by decide)).fwdBits γ₁ = γ₂ := ⟨_, rfl⟩
  rw [hγ₂] at hclN1 hprN1 hNe1
  obtain ⟨hclN2, hprN2, hNe2⟩ := n1s_kNe411_eval_axis 2 331 (by decide) (by decide) rfl γ₂ hclN1
  obtain ⟨γ₃, hγ₃⟩ : ∃ γ₃, (n1sKNe411 2 331 (by decide) (by decide)).fwdBits γ₂ = γ₃ := ⟨_, rfl⟩
  rw [hγ₃] at hclN2 hprN2 hNe2
  have hγ₃_317 : ∀ w : Wire 411, w.val < 317 → γ₃ w = γ₀ w := fun w hw ↦
    (hprN2 w (by omega)).trans ((hprN1 w (by omega)).trans (hprN0 w hw))
  have hγ₃_297 : ∀ w : Wire 411, w.val < 297 → γ₃ w = β₁ w := fun w hw ↦
    (hγ₃_317 w (by omega)).trans (hpr₀ w hw)
  have hlt := n1s_projNe128Slot_bounds
  have hp0 : (fun b ↦ γ₀ (n1sProjW411 0 b)) = fun b ↦ β₁ (n1sProjW411 0 b) :=
    funext fun b ↦ hpr₀ _ (by dsimp [n1sProjW411]; omega)
  have hp1 : (fun b ↦ γ₁ (n1sProjW411 1 b)) = fun b ↦ β₁ (n1sProjW411 1 b) :=
    funext fun b ↦ (hprN0 _ (by dsimp [n1sProjW411]; omega)).trans
      (hpr₀ _ (by dsimp [n1sProjW411]; omega))
  have hp2 : (fun b ↦ γ₂ (n1sProjW411 2 b)) = fun b ↦ β₁ (n1sProjW411 2 b) :=
    funext fun b ↦ (hprN1 _ (by dsimp [n1sProjW411]; omega)).trans
      ((hprN0 _ (by dsimp [n1sProjW411]; omega)).trans (hpr₀ _ (by dsimp [n1sProjW411]; omega)))
  have hNe0_val : γ₃ (n1sNeAxisW411 0) =
      boolToZMod2 (decide (bitsVal (fun b ↦ β₁ (n1sProjW411 0 b)) ≠ 128)) := by
    rw [hprN2 _ (by dsimp [n1sNeAxisW411]; omega),
      hprN1 _ (by dsimp [n1sNeAxisW411]; omega), hNe0, hp0]
  have hNe1_val : γ₃ (n1sNeAxisW411 1) =
      boolToZMod2 (decide (bitsVal (fun b ↦ β₁ (n1sProjW411 1 b)) ≠ 128)) := by
    rw [hprN2 _ (by dsimp [n1sNeAxisW411]; omega), hNe1, hp1]
  have hNe2_val : γ₃ (n1sNeAxisW411 2) =
      boolToZMod2 (decide (bitsVal (fun b ↦ β₁ (n1sProjW411 2 b)) ≠ 128)) := by
    rw [hNe2, hp2]
  set γ₄a :=
    Function.update γ₃ ⟨338, by decide⟩ (γ₃ ⟨338, by
    decide⟩ + γ₃ (n1sNeAxisW411 0) * γ₃ (n1sNeAxisW411 1))
  set γ₄b :=
    Function.update γ₄a ⟨339, by decide⟩ (γ₄a ⟨339, by decide⟩ + γ₄a ⟨338, by
    decide⟩ * γ₄a (n1sNeAxisW411 2))
  set γ₄ :=
    Function.update γ₄b n1sValidProjW411 (γ₄b n1sValidProjW411 + γ₄b n1sValidStaticW411 * γ₄b ⟨339,
    by decide⟩)
  have hγ₄_338 : ∀ w : Wire 411, w.val < 338 → γ₄ w = γ₃ w := fun w hw ↦ by
    dsimp [γ₄, γ₄b, γ₄a]
    rw [Function.update_of_ne (wire_ne_of_lt (by dsimp [n1sValidProjW411]; omega)),
      Function.update_of_ne (wire_ne_of_lt (by dsimp; omega)),
      Function.update_of_ne (wire_ne_of_lt (by dsimp; omega))]
  have hcl₄ : cleanRem 411 (411 - 341) γ₄ := fun w hw ↦ by
    dsimp [γ₄, γ₄b, γ₄a]
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [n1sValidProjW411]; omega)),
      Function.update_of_ne (wire_ne_of_gt (by dsimp; omega)),
      Function.update_of_ne (wire_ne_of_gt (by dsimp; omega))]
    exact hclN2 w (by omega)
  have hγ₄_vp : γ₄ n1sValidProjW411 = β₁ n1sValidStaticW411 * boolToZMod2 (decide (bitsVal
      (fun b ↦ β₁ (n1sProjW411 0 b)) ≠ 128) && decide (bitsVal (fun b ↦ β₁ (n1sProjW411 1 b))
      ≠ 128) && decide (bitsVal (fun b ↦ β₁ (n1sProjW411 2 b)) ≠ 128)) := by
    have hlt := n1s_projNe128Slot_bounds
    have h338_0 : γ₃ ⟨338, by decide⟩ = 0 := hclN2 ⟨338, by decide⟩ (by decide)
    have h339_0 : γ₃ ⟨339, by decide⟩ = 0 := hclN2 ⟨339, by decide⟩ (by decide)
    have h340_0 : γ₃ n1sValidProjW411 = 0 := hclN2 n1sValidProjW411 (by decide)
    dsimp only [γ₄, γ₄b, γ₄a]
    rw [Function.update_self,
      Function.update_of_ne (wire_ne_of_gt (by decide)),
      Function.update_of_ne (wire_ne_of_gt (by decide)),
      h340_0, zero_add,
      Function.update_of_ne (wire_ne_of_lt (by decide)),
      Function.update_of_ne (wire_ne_of_lt (by decide)),
      hγ₃_297 n1sValidStaticW411 (by decide),
      Function.update_self,
      Function.update_of_ne (wire_ne_of_gt (by decide)),
      h339_0, zero_add, Function.update_self, h338_0, zero_add,
      Function.update_of_ne (wire_ne_of_lt (by dsimp [n1sNeAxisW411]; omega)),
      hNe0_val, hNe1_val, hNe2_val]
    congr 1
    generalize decide (bitsVal (fun b ↦ β₁ (n1sProjW411 0 b)) ≠ 128) = x0
    generalize decide (bitsVal (fun b ↦ β₁ (n1sProjW411 1 b)) ≠ 128) = x1
    generalize decide (bitsVal (fun b ↦ β₁ (n1sProjW411 2 b)) ≠ 128) = x2
    cases x0 <;> cases x1 <;> cases x2 <;> rfl
  obtain ⟨hThrNon, hThrVal⟩ := accLoadThrLoop_eval t.kBits t.dCut t.wAcc (n1sThrW411 t)
    (n1s_thrWire411_inj t) n1sOhAux (n1s_ohAux_ne_thrWire411 t) 18 le_rfl γ₄
  obtain ⟨γ₅, hγ₅⟩ : ∃ γ₅, (accLoadThrLoop t.kBits t.dCut t.wAcc (n1sThrW411 t) 18 le_rfl n1sOhAux
    (n1s_ohAux_ne_thrWire411 t)).eval γ₄ = γ₅ := ⟨_, rfl⟩
  rw [hγ₅] at hThrNon hThrVal
  have hcl₅ : cleanRem 411 (411 - 373) γ₅ := fun w hw ↦ by
    rw [hThrNon w (fun j ↦ wire_ne_of_gt (by dsimp [n1sThrW411]; omega))]
    exact hcl₄ w (by omega)
  obtain ⟨_, hLtEv⟩ := ctxLtCompLoop_scoped t.wAcc 373 (by omega)
    (n1sOutAccW411 t) (n1sThrW411 t)
    (n1s_outAcc_ne_thr t) (n1s_outAcc_lt_373 t) (n1s_thr_lt_373 t)
  obtain ⟨hclOut, hLtIff⟩ := hLtEv γ₅ hcl₅
  obtain ⟨hdLtVp, _⟩ := ctxLtCompLoop_props (mutW := fun q : Wire 411 ↦ q = n1sValidProjW411)
    t.wAcc 373 (by omega) (n1sOutAccW411 t) (n1sThrW411 t)
    (n1s_outAcc_ne_thr t) (n1s_outAcc_lt_373 t) (n1s_thr_lt_373 t)
    (fun j h ↦ by
      have hv := congrArg Fin.val h
      dsimp [n1sOutAccW411, n1sOut32W411, n1sValidProjW411] at hv
      omega)
    (fun j h ↦ by
      have hv := congrArg Fin.val h
      dsimp [n1sThrW411, n1sValidProjW411] at hv
      omega)
    (fun w hw h ↦ by subst h; dsimp [n1sValidProjW411] at hw; omega)
  have hVpOut :
      (ctxLtCompLoop t.wAcc 373 _ (n1sOutAccW411 t) (n1sThrW411 t) _ _ _).fwdBits
        γ₅ n1sValidProjW411 = γ₄ n1sValidProjW411 :=
    (n1s_fwdBits_mut hdLtVp γ₅ rfl).trans
      (hThrNon n1sValidProjW411
        (fun j ↦ wire_ne_of_lt (by dsimp [n1sValidProjW411, n1sThrW411]; omega)))
  have hδ : δ = (ctxLtCompLoop t.wAcc 373 (by omega) (n1sOutAccW411 t) (n1sThrW411 t)
      (n1s_outAcc_ne_thr t) (n1s_outAcc_lt_373 t) (n1s_thr_lt_373 t)).fwdBits γ₅ := by
    dsimp only [δ, n1sCtxGuard411]
    rw [n1s_fwdBits_append, hγ₀,
      n1s_fwdBits_append, hγ₁,
      n1s_fwdBits_append, hγ₂,
      n1s_fwdBits_append, hγ₃,
      n1s_fwdBits_append, n1s_ctxTempBit_fwdBits,
        show Function.update γ₃ ⟨338, by
          decide⟩ _ = γ₄a from rfl,
      n1s_fwdBits_append, n1s_ctxTempBit_fwdBits,
        show Function.update γ₄a ⟨339, by
          decide⟩ _ = γ₄b from rfl,
      n1s_fwdBits_append, n1s_ctxTempBit_fwdBits,
        show Function.update γ₄b n1sValidProjW411 _ = γ₄ from rfl,
      n1s_fwdBits_append, n1s_ctxCliffAlloc_fwdBits, hγ₅]
  refine ⟨hδ ▸ hclOut, hAccEq, ?_, fun hmu hle he17 hout_lt ↦ ?_⟩
  · rw [hδ]; exact hVpOut.trans hγ₄_vp
  · rw [hδ]
    have hOutSlice : bitsVal (fun j : Fin t.wAcc ↦ γ₅ (n1sOutAccW411 t j)) = outVal := by
      have hfn : (fun j : Fin t.wAcc ↦ γ₅ (n1sOutAccW411 t j)) =
          fun j : Fin t.wAcc ↦ β₁ (n1sOut32W411 ⟨0 + j.val, by omega⟩) :=
        funext fun j ↦ (hThrNon (n1sOutAccW411 t j) (fun k ↦
          wire_ne_of_lt (by dsimp [n1sOutAccW411, n1sOut32W411, n1sThrW411]; omega))).trans
          ((hγ₄_338 (n1sOutAccW411 t j) (by dsimp [n1sOutAccW411, n1sOut32W411]; omega)).trans
            ((hγ₃_297 (n1sOutAccW411 t j) (by dsimp [n1sOutAccW411, n1sOut32W411]; omega)).trans
              (show β₁ (n1sOut32W411 ⟨j.val, lt_of_lt_of_le j.isLt t.wAcc_le_32⟩) =
                  β₁ (n1sOut32W411 ⟨0 + j.val, by omega⟩) from
                congrArg (fun k ↦ β₁ (n1sOut32W411 k)) (Fin.ext (by dsimp; omega)))))
      rw [hfn, bitsVal_slice_eq_div_mod (by omega) (fun k : Fin 32 ↦ β₁ (n1sOut32W411 k))]
      change (outVal / 1) % 2 ^ t.wAcc = outVal
      rw [Nat.div_one, Nat.mod_eq_of_lt hout_lt]
    have hm8_eq := n1s_inSub8_bitsVal β₁
    have hm8_lt : bitsVal (fun i : Fin 8 ↦ β₁ (n1sInSub8W411 i)) < 256 := bitsVal_lt_two_pow _
    have hm8_mod : bitsVal (fun i : Fin 8 ↦ β₁ (n1sInSub8W411 i)) % 8 = mu := by
      have hmu8 : mu < 8 := bitsVal_lt_two_pow _; omega
    have hm8_div : bitsVal (fun i : Fin 8 ↦ β₁ (n1sInSub8W411 i)) / 8 = e := by
      have hmu8 : mu < 8 := bitsVal_lt_two_pow _; omega
    have hSubSpec := (subDOh18_15Ops_spec _ hm8_lt).2 (by omega) (by omega) (by omega)
    let dStar : Fin 18 := ⟨e - 2 * mu, by omega⟩
    have hOhVal : ∀ d : Fin 18, γ₄ (n1sOhAux d) = if d = dStar then 1 else 0 := fun d ↦ by
      have hb_slot := n1s_subDOh18_15Slot_bounds d
      rw [hγ₄_338 _ (by dsimp [n1sOhAux]; omega), hγ₃_317 _ (by dsimp [n1sOhAux]; omega)]
      have hw : n1sOhAux d = ⟨297 + (subDOh18_15Slot d - 8), by omega⟩ := rfl
      rw [hw, ← hγ₀, hout₀ (subDOh18_15Slot d) hb_slot.1 hb_slot.2, hSubSpec d, hm8_mod, hm8_div]
      by_cases hd : d = dStar
      · subst hd; simp [dStar, boolToZMod2]
      · have hne_v : e - 2 * mu ≠ d.val := fun hv ↦ hd (Fin.ext hv.symm)
        simp [hd, hne_v, boolToZMod2]
    have hThrBits : bitsVal (fun j : Fin t.wAcc ↦ γ₅ (n1sThrW411 t j)) =
        accThr t.kBits t.dCut (e - 2 * mu) := by
      have hfn : (fun j : Fin t.wAcc ↦ γ₅ (n1sThrW411 t j)) =
          fun j : Fin t.wAcc ↦ boolToZMod2 ((accThr t.kBits t.dCut (e - 2 * mu)).testBit j.val) :=
            by
        funext j
        rw [hThrVal j, hcl₄ (n1sThrW411 t j) (by dsimp [n1sThrW411]; omega), zero_add]
        have hsum : (∑ d : Fin 18, if 18 - 18 ≤ d.val then
            if (accThr t.kBits t.dCut d.val).testBit j.val then γ₄ (n1sOhAux d) else 0 else 0) =
            if (accThr t.kBits t.dCut dStar.val).testBit j.val then 1 else 0 := by
          have hcongr : ∀ d : Fin 18,
              (if 18 - 18 ≤ d.val then
                if (accThr t.kBits t.dCut d.val).testBit j.val then γ₄ (n1sOhAux d) else 0 else 0) =
              if d = dStar then (if (accThr t.kBits t.dCut dStar.val).testBit j.val then
                (1 : ZMod 2) else 0) else 0 := by
            intro d; rw [n1s_if_pos (by omega), hOhVal d]; by_cases hd : d = dStar <;> simp [hd]
          simp only [hcongr, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        rw [hsum]
        dsimp [dStar, boolToZMod2]
      rw [hfn]
      exact n1s_bitsVal_of_nat t.wAcc _ (accThr_lt_two_pow_wAcc t dStar.isLt)
    rw [hOutSlice, hThrBits] at hLtIff
    change (ctxLtCompLoop t.wAcc 373 _ (n1sOutAccW411 t) (n1sThrW411 t) _ _ _).fwdBits γ₅
      ⟨373 + t.wAcc, _⟩ = _
    rcases bit_cases ((ctxLtCompLoop t.wAcc 373 _ (n1sOutAccW411 t) (n1sThrW411 t) _ _ _).fwdBits γ₅
      ⟨373 + t.wAcc, by omega⟩) with h0 | h1
    · have hnot : ¬ (outVal < accThr t.kBits t.dCut (e - 2 * mu)) :=
        fun hlt ↦ zero_ne_one (h0.symm.trans (hLtIff.mpr hlt))
      simp [h0, hnot, boolToZMod2]
    · have hlt : outVal < accThr t.kBits t.dCut (e - 2 * mu) := hLtIff.mp h1
      simp [h1, hlt, boolToZMod2]

theorem n1s_realizes_toDyn_true {Var : Type} [Fintype Var] [DecidableEq Var] {n : ℕ}
    [NeZero (2 ^ n)] (v : Var) (rComb : QRegister 411 n) (p : TempPhaseProg 411) (rem : ℕ)
    (hrem : rem ≤ 411) (hv : ValidCleanRem 411 rem p) : RealizesCleanUnitary v
    (p57CleanDiagProj rComb rem hrem (fun _ ↦ True)) ((p.onRegister rComb).toDyn v)
    (((p.onRegister rComb).toToffCircuit).eval) := by
  rw [Slot3Outer2344AndRelayWide.Slot3MidKickWidthWide.p57CleanDiagProj_true_eq]
  exact realizes_of_validCleanRem v rComb p rem hrem hv

theorem n1s_ctxBarrel411_scoped :
    n1sCtxBarrel411.countTempAnd = 59 ∧
    (∀ {mutW : Wire 411 → Prop},
      (∀ i, ¬ mutW (n1sInBarrelW411 i)) → (∀ w : Wire 411, 297 ≤ w.val → ¬ mutW w) →
      n1sCtxBarrel411.DisjointFrom mutW ∧ n1sCtxBarrel411.SupportsBelowCtx (297 + 82)) ∧
    TempCtxLiftEx 297 (297 + 82) n1sCtxBarrel411 ∧
    (∀ β : BitAssignment 411, cleanRem 411 (411 - 297) β →
      let m := bitsVal (fun i ↦ β (n1sInBarrelW411 i))
      let stOut := evalMicroList 40 barrel59Ops (initBoolList 40 (40 + 82) m)
      cleanRem 411 (411 - (297 + 82)) (n1sCtxBarrel411.fwdBits β) ∧
      (allBelow 40 (fun i ↦ getBoolAt stOut i == m.testBit i) = true →
        ∀ w : Wire 411, w.val < 297 → n1sCtxBarrel411.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hlo : 40 ≤ s) (hhi : s < 40 + 82),
        n1sCtxBarrel411.fwdBits β ⟨297 + (s - 40), by omega⟩ = boolToZMod2 (getBoolAt stOut s))) :=
  ctxMicro_scoped n1sInBarrelW411 n1s_inBarrelW411_inj 297 82 59
    n1s_inBarrelW411_lt_297 barrel59Ops barrel59Ops_meta (by decide)

/-- Barrel-wrapped forward Booth subprogram on `[297..411)`. -/
def n1sPBarFwd411 (t : Norm1sTier) : TempPhaseProg 411 :=
  n1sCtxBarrel411.plug (n1sBoothFwd411 t)

/-- Barrel-wrapped reverse Booth static reference on `[297..411)`. -/
def n1sPBarRev411 (t : Norm1sTier) : TempPhaseProg 411 :=
  n1sCtxBarrel411.plug (n1sBoothRevStatic411 t)

theorem n1s_ctxBarrel411_pkg :
    let mutOut : Wire 411 → Prop := fun q ↦ ∃ k : Fin 32, q = n1sOut32W411 k
    n1sCtxBarrel411.countTempAnd = 59 ∧
    n1sCtxBarrel411.DisjointFrom mutOut ∧
    n1sCtxBarrel411.SupportsBelowCtx 379 ∧
    TempCtxLiftEx 297 379 n1sCtxBarrel411 := by
  intro mutOut
  obtain ⟨hc, hp, hl, _⟩ := n1s_ctxBarrel411_scoped
  obtain ⟨hd, hs⟩ := hp
    (fun i (h : mutOut (n1sInBarrelW411 i)) ↦ by
      rcases h with ⟨k, hk⟩
      dsimp [n1sInBarrelW411] at hk
      by_cases hi : i.val < 18
      · rw [n1s_dif_pos hi] at hk
        have hr := n1s_sTrue18W411_range ⟨i.val, hi⟩
        have hv := congrArg Fin.val hk; dsimp [n1sOut32W411] at hv
        rcases hr with h | h | h <;> omega
      · rw [n1s_dif_neg hi] at hk
        have hv := congrArg Fin.val hk; dsimp [n1sOut32W411] at hv; omega)
    (fun w hw (h : mutOut w) ↦ by
      rcases h with ⟨k, hk⟩; subst hk; dsimp [n1sOut32W411] at hw; omega)
  exact ⟨hc, hd, hs, hl⟩

private theorem n1s_plug411_297 (curHole : ℕ) (mutW : Wire 411 → Prop)
    (K : TempCtx 411) (P : TempPhaseProg 411) (hd : K.DisjointFrom mutW)
    (hs : K.SupportsBelowCtx curHole) (hhole : 411 - curHole ≤ 411 - 297)
    (hl : TempCtxLiftEx 297 curHole K) (hvIn : ValidCleanRem 411 (411 - curHole) P)
    (hPresIn : ∀ γ, cleanRem 411 (411 - curHole) γ → ∀ w, ¬ mutW w → P.evalBits γ w = γ w)
    (hSgnIn : ∀ γ, cleanRem 411 (411 - curHole) γ → P.evalSign γ = 0)
    (hClFwd : ∀ β₁, cleanRem 411 (411 - 297) β₁ → cleanRem 411 (411 - curHole) (K.fwdBits β₁))
    (hMutBelow : ∀ w : Wire 411, 297 ≤ w.val → ¬ mutW w) :
    ValidCleanRem 411 (411 - 297) (K.plug P) ∧
    (K.plug P).countTempAnd = K.countTempAnd + P.countTempAnd ∧
    ∀ β₁ : BitAssignment 411, cleanRem 411 (411 - 297) β₁ →
      (K.plug P).evalSign β₁ = 0 ∧ cleanRem 411 (411 - 297) ((K.plug P).evalBits β₁) ∧
      (∀ q, ¬ mutW q → (K.plug P).evalBits β₁ q = β₁ q) ∧
      (∀ q, mutW q → (K.plug P).evalBits β₁ q = P.evalBits (K.fwdBits β₁) q) := by
  classical
  obtain ⟨hv, hcnt, hsgn, hbits⟩ :=
    Prod57BoothHoist.ScopedBlock.graft_mutating_clean
      (M := 411) (rem := 411 - 297) (curHole := curHole) mutW K hd hs hhole K.fwdBits
      (TempCtxLiftEx.probe hl) P hvIn hPresIn
  refine ⟨hv, hcnt, fun β₁ hβ₁ ↦ ?_⟩
  have hnon : ∀ q, ¬ mutW q → (K.plug P).evalBits β₁ q = β₁ q :=
    fun q hq ↦ by rw [hbits β₁ hβ₁ q, n1s_if_neg hq]
  exact ⟨by rw [hsgn β₁ hβ₁, hSgnIn _ (hClFwd β₁ hβ₁)],
    fun w hw ↦ (hnon w (hMutBelow w hw)).trans (hβ₁ w hw), hnon,
    fun q hq ↦ by rw [hbits β₁ hβ₁ q, n1s_if_pos hq]⟩

theorem n1s_pBarFwd411_spec (t : Norm1sTier) : ValidCleanRem 411 (411 - 297) (n1sPBarFwd411 t)
    ∧ (n1sPBarFwd411 t).countTempAnd = 59 + n1sBoothFwdAnds t ∧ (∀ β₁ : BitAssignment 411,
    cleanRem 411 (411 - 297) β₁ → (n1sPBarFwd411 t).evalSign β₁ = 0 ∧ cleanRem 411 (411 - 297)
    ((n1sPBarFwd411 t).evalBits β₁) ∧ (∀ q : Wire 411, (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
    (n1sPBarFwd411 t).evalBits β₁ q = β₁ q) ∧ ((∀ k : Fin 32, β₁ (n1sOut32W411 k) = 0) →
    bitsVal (fun k : Fin 32 ↦ (n1sPBarFwd411 t).evalBits β₁ (n1sOut32W411 k)) = norm1sHwProd
    t.kBits t.dCut (bitsVal (fun i : Fin 18 ↦ (n1sCtxBarrel411.fwdBits β₁) (n1sMantW411 i)))
    (bitsVal (fun m : Fin t.kBits ↦ (n1sCtxBarrel411.fwdBits β₁) (n1sUKW411 t m))))) := by
  dsimp only [n1sPBarFwd411]
  obtain ⟨hcB, hdB, hsB, hlB⟩ := n1s_ctxBarrel411_pkg
  obtain ⟨hvIn, hEvIn⟩ := n1s_boothFwd411_spec t
  obtain ⟨_, _, _, hBarEv⟩ := n1s_ctxBarrel411_scoped
  obtain ⟨hv, hcnt, hEv⟩ := n1s_plug411_297 379 (fun q ↦ ∃ k : Fin 32, q = n1sOut32W411 k)
    n1sCtxBarrel411 (n1sBoothFwd411 t) hdB hsB (by decide) hlB hvIn
    (fun γ hγ w hnw ↦ (hEvIn γ hγ).2.2.1 w (fun k hk ↦ hnw ⟨k, hk⟩))
    (fun γ hγ ↦ (hEvIn γ hγ).1) (fun β₁ hβ₁ ↦ (hBarEv β₁ hβ₁).1)
    (fun w hw ⟨k, hk⟩ ↦ by subst hk; dsimp [n1sOut32W411] at hw; omega)
  refine ⟨hv, by rw [hcnt, hcB, n1s_boothFwd411_countTempAnd], fun β₁ hβ₁ ↦ ?_⟩
  obtain ⟨hsgn, hcl, hnon, hmut⟩ := hEv β₁ hβ₁
  have hcl₂ := (hBarEv β₁ hβ₁).1
  refine ⟨hsgn, hcl, fun q hq ↦ hnon q (fun ⟨k, hk⟩ ↦ hq k hk), fun hout0 ↦ ?_⟩
  have hout0' : ∀ k : Fin 32, (n1sCtxBarrel411.fwdBits β₁) (n1sOut32W411 k) = 0 :=
    fun k ↦ (n1s_fwdBits_mut hdB β₁ ⟨k, rfl⟩).trans (hout0 k)
  have hDone := (hEvIn _ hcl₂).2.2.2 hout0'
  obtain ⟨hmEq, huEq⟩ := n1s_mant_uK_congr t (hEvIn _ hcl₂).2.2.1
  unfold n1sBoothDoneInv at hDone
  rw [hmEq, huEq] at hDone
  have hfn : (fun k : Fin 32 ↦ (n1sCtxBarrel411.plug (n1sBoothFwd411 t)).evalBits β₁
      (n1sOut32W411 k)) =
      fun k : Fin 32 ↦ (n1sBoothFwd411 t).evalBits (n1sCtxBarrel411.fwdBits β₁) (n1sOut32W411 k) :=
    funext fun k ↦ hmut (n1sOut32W411 k) ⟨k, rfl⟩
  rw [hfn]
  exact hDone

theorem n1s_pBarRev411_spec (t : Norm1sTier) : ValidCleanRem 411 (411 - 297) (n1sPBarRev411 t)
    ∧ (∀ β₁ : BitAssignment 411, cleanRem 411 (411 - 297) β₁ → (n1sPBarRev411 t).evalSign β₁ =
    0 ∧ cleanRem 411 (411 - 297) ((n1sPBarRev411 t).evalBits β₁) ∧ (∀ q : Wire 411, (∀ k : Fin
    32, q ≠ n1sOut32W411 k) → (n1sPBarRev411 t).evalBits β₁ q = β₁ q) ∧ (n1sBoothDoneInv t
    (n1sCtxBarrel411.fwdBits β₁) → ∀ k : Fin 32, (n1sPBarRev411 t).evalBits β₁ (n1sOut32W411
    k) = 0)) := by
  dsimp only [n1sPBarRev411]
  obtain ⟨_, hdB, hsB, hlB⟩ := n1s_ctxBarrel411_pkg
  obtain ⟨hvIn, hEvIn⟩ := n1s_boothRevStatic411_spec t
  obtain ⟨_, _, _, hBarEv⟩ := n1s_ctxBarrel411_scoped
  obtain ⟨hv, _, hEv⟩ := n1s_plug411_297 379 (fun q ↦ ∃ k : Fin 32, q = n1sOut32W411 k)
    n1sCtxBarrel411 (n1sBoothRevStatic411 t) hdB hsB (by decide) hlB hvIn
    (fun γ hγ w hnw ↦ (hEvIn γ hγ).2.2.1 w (fun k hk ↦ hnw ⟨k, hk⟩))
    (fun γ hγ ↦ (hEvIn γ hγ).1) (fun β₁ hβ₁ ↦ (hBarEv β₁ hβ₁).1)
    (fun w hw ⟨k, hk⟩ ↦ by subst hk; dsimp [n1sOut32W411] at hw; omega)
  refine ⟨hv, fun β₁ hβ₁ ↦ ?_⟩
  obtain ⟨hsgn, hcl, hnon, hmut⟩ := hEv β₁ hβ₁
  exact ⟨hsgn, hcl, fun q hq ↦ hnon q (fun ⟨k, hk⟩ ↦ hq k hk),
    fun hDone k ↦ (hmut (n1sOut32W411 k) ⟨k, rfl⟩).trans
      ((hEvIn _ (hBarEv β₁ hβ₁).1).2.2.2 hDone k)⟩

/-- `1`-`TempAnd` (`msbClearStatic`) inner acceptance XOR at clean wire `373 + t.wAcc + 1`. -/
def n1sGuardInner (t : Norm1sTier) : TempPhaseProg 411 :=
  msbClearStatic (373 + t.wAcc + 1) (by have := t.wAcc_le_32; omega)
    n1sValidProjW411 (n1sLtOutW411 t) n1sAccFlagW411
    (wire_ne_of_lt (by dsimp [n1sValidProjW411, n1sLtOutW411]; omega))
    (by dsimp [n1sValidProjW411]; omega)
    (by dsimp [n1sLtOutW411]; omega)
    (by dsimp [n1sAccFlagW411]; omega)

/-- Guard-wrapped acceptance flag toggle on `[297..411)`. -/
def n1sPGuard411 (t : Norm1sTier) : TempPhaseProg 411 :=
  (n1sCtxGuard411 t).plug (n1sGuardInner t)

/-- Target `ZMod 2` acceptance bit value on `Wire 411`. -/
def n1sAccTarget411 (t : Norm1sTier) (β : BitAssignment 411) : ZMod 2 :=
  let s := bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))
  let uK := bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits)
  let mu := bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i))
  β n1sValidStaticW411 *
    (if ∀ w : Fin 3, bitsVal (fun b : Fin 8 ↦ β (n1sProjW411 w b)) ≠ 128 then 1 else 0) *
    (if norm1sHwProd t.kBits t.dCut (norm1sMant18 s) uK <
        accThr t.kBits t.dCut (clz18Log2 s - 2 * mu) then 1 else 0)

theorem n1s_pGuard411_spec (t : Norm1sTier) : ValidCleanRem 411 (411 - 297) (n1sPGuard411 t) ∧
    (n1sPGuard411 t).countTempAnd = (15 + 21 + 3 + t.wAcc) + 1 ∧ (∀ β₁ : BitAssignment 411,
    cleanRem 411 (411 - 297) β₁ → (n1sPGuard411 t).evalSign β₁ = 0 ∧ cleanRem 411 (411 - 297)
    ((n1sPGuard411 t).evalBits β₁) ∧ (∀ q : Wire 411, q ≠ n1sAccFlagW411 → (n1sPGuard411
    t).evalBits β₁ q = β₁ q) ∧ (n1sPGuard411 t).evalBits β₁ n1sAccFlagW411 = β₁ n1sAccFlagW411
    + ((n1sCtxGuard411 t).fwdBits β₁) n1sValidProjW411 * ((n1sCtxGuard411 t).fwdBits β₁)
    (n1sLtOutW411 t)) := by
  dsimp only [n1sPGuard411, n1sGuardInner]
  have hb := t.wAcc_le_32
  obtain ⟨hcG, hdG, hsG, hlG⟩ := n1s_ctxGuard411_pkg t
  obtain ⟨hvIn, hcIn, hsIn, hbIn⟩ := msbClearStatic_spec (373 + t.wAcc + 1) (by omega)
    n1sValidProjW411 (n1sLtOutW411 t) n1sAccFlagW411
    (wire_ne_of_lt (by dsimp [n1sValidProjW411, n1sLtOutW411]; omega))
    (wire_ne_of_gt (by decide))
    (wire_ne_of_gt (by dsimp [n1sLtOutW411, n1sAccFlagW411]; omega))
    (by dsimp [n1sValidProjW411]; omega)
    (by dsimp [n1sLtOutW411]; omega)
    (by dsimp [n1sAccFlagW411]; omega)
  obtain ⟨hv, hcnt, hEv⟩ := n1s_plug411_297 (373 + t.wAcc + 1) (fun q ↦ q = n1sAccFlagW411)
    (n1sCtxGuard411 t) _ hdG hsG (by omega) hlG hvIn
    (fun γ hγ w hnw ↦ by rw [hbIn γ hγ, Function.update_of_ne hnw])
    hsIn (fun β₁ hβ₁ ↦ (n1s_ctxGuard411_fwd t β₁ hβ₁).1)
    (fun w hw h ↦ by subst h; dsimp [n1sAccFlagW411] at hw; omega)
  refine ⟨hv, by rw [hcnt, hcG, hcIn], fun β₁ hβ₁ ↦ ?_⟩
  obtain ⟨hclH, hAccH, _, _⟩ := n1s_ctxGuard411_fwd t β₁ hβ₁
  obtain ⟨hsgn, hcl, hnon, hmut⟩ := hEv β₁ hβ₁
  exact ⟨hsgn, hcl, hnon,
    by rw [hmut n1sAccFlagW411 rfl, hbIn _ hclH, Function.update_self, hAccH]⟩

theorem n1s_ctxClz411_scoped :
    n1sCtxClz411.countTempAnd = 16 ∧
    (∀ {mutW : Wire 411 → Prop},
      (∀ i, ¬ mutW (n1sSTrue18W411 i)) → (∀ w : Wire 411, 275 ≤ w.val → ¬ mutW w) →
      n1sCtxClz411.DisjointFrom mutW ∧ n1sCtxClz411.SupportsBelowCtx (275 + 22)) ∧
    TempCtxLiftEx 275 (275 + 22) n1sCtxClz411 ∧
    (∀ β : BitAssignment 411, cleanRem 411 (411 - 275) β →
      let m := bitsVal (fun i ↦ β (n1sSTrue18W411 i))
      let stOut := evalMicroList 18 clz18Ops (initBoolList 18 (18 + 22) m)
      cleanRem 411 (411 - (275 + 22)) (n1sCtxClz411.fwdBits β) ∧
      (allBelow 18 (fun i ↦ getBoolAt stOut i == m.testBit i) = true →
        ∀ w : Wire 411, w.val < 275 → n1sCtxClz411.fwdBits β w = β w) ∧
      (∀ (s : ℕ) (hlo : 18 ≤ s) (hhi : s < 18 + 22),
        n1sCtxClz411.fwdBits β ⟨275 + (s - 18), by omega⟩ = boolToZMod2 (getBoolAt stOut s))) :=
  ctxMicro_scoped n1sSTrue18W411 n1s_sTrue18W411_inj 275 22 16
    n1s_sTrue18W411_lt_275 clz18Ops clz18Ops_meta (by decide)

theorem n1s_ctxClz411_pkg :
    let mut32Acc : Wire 411 → Prop := fun q ↦ q = n1sAccFlagW411 ∨ ∃ k : Fin 32, q = n1sOut32W411 k
    n1sCtxClz411.countTempAnd = 16 ∧
    n1sCtxClz411.DisjointFrom mut32Acc ∧
    n1sCtxClz411.SupportsBelowCtx 297 ∧
    TempCtxLiftEx 275 297 n1sCtxClz411 := by
  intro mut32Acc
  obtain ⟨hc, hp, hl, _⟩ := n1s_ctxClz411_scoped
  obtain ⟨hd, hs⟩ := hp
    (fun i (h : mut32Acc (n1sSTrue18W411 i)) ↦ by
      have hr := n1s_sTrue18W411_range i
      rcases h with h1 | ⟨k, hk⟩
      · have hv := congrArg Fin.val h1; dsimp [n1sAccFlagW411] at hv
        rcases hr with r | r | r <;> omega
      · have hv := congrArg Fin.val hk; dsimp [n1sOut32W411] at hv
        rcases hr with r | r | r <;> omega)
    (fun w hw (h : mut32Acc w) ↦ by
      rcases h with h1 | ⟨k, hk⟩
      · subst h1; dsimp [n1sAccFlagW411] at hw; omega
      · subst hk; dsimp [n1sOut32W411] at hw; omega)
  exact ⟨hc, hd, hs, hl⟩

theorem n1s_guardHole_eq_target (t : Norm1sTier) (β β₁ : BitAssignment 411)
    (hcl₁ : cleanRem 411 (411 - 297) β₁) (hag : ∀ w : Wire 411, w.val < 275 → w ≠
    n1sAccFlagW411 → (∀ k : Fin 32, w ≠ n1sOut32W411 k) → β₁ w = β w) (he : bitsVal (fun b :
    Fin 5 ↦ β₁ (n1sEW411 b)) = clz18Log2 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))))
    (hout : bitsVal (fun k : Fin 32 ↦ β₁ (n1sOut32W411 k)) = norm1sHwProd t.kBits t.dCut
    (norm1sMant18 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)))) (bitsVal (fun k : Fin 38
    ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits))) (hvalid : β n1sValidStaticW411 = 1 → bitsVal
    (fun i : Fin 3 ↦ β (n1sMuW411 i)) < 7 ∧ 2 * bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) ≤
    clz18Log2 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)))) :
    ((n1sCtxGuard411 t).fwdBits β₁) n1sValidProjW411 * ((n1sCtxGuard411 t).fwdBits β₁)
    (n1sLtOutW411 t) = n1sAccTarget411 t β := by
  obtain ⟨_, _, hvp, hlt_fn⟩ := n1s_ctxGuard411_fwd t β₁ hcl₁
  have hvs_eq : β₁ n1sValidStaticW411 = β n1sValidStaticW411 :=
    hag n1sValidStaticW411 (by decide) (by decide)
      (fun k ↦ wire_ne_of_gt (by dsimp [n1sValidStaticW411, n1sOut32W411]; omega))
  have hpr_eq : ∀ w : Fin 3, bitsVal (fun b : Fin 8 ↦ β₁ (n1sProjW411 w b)) =
      bitsVal (fun b : Fin 8 ↦ β (n1sProjW411 w b)) := fun w ↦
    congrArg bitsVal (funext fun b ↦ hag (n1sProjW411 w b) (by dsimp [n1sProjW411]; omega)
      (wire_ne_of_lt (by dsimp [n1sProjW411, n1sAccFlagW411]; omega))
      (fun k ↦ wire_ne_of_lt (by dsimp [n1sProjW411, n1sOut32W411]; omega)))
  have hmu_eq : bitsVal (fun i : Fin 3 ↦ β₁ (n1sMuW411 i)) =
      bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) :=
    congrArg bitsVal (funext fun i ↦ hag (n1sMuW411 i) (by dsimp [n1sMuW411]; omega)
      (wire_ne_of_gt (by dsimp [n1sMuW411, n1sAccFlagW411]; omega))
      (fun k ↦ wire_ne_of_lt (by dsimp [n1sMuW411, n1sOut32W411]; omega)))
  unfold n1sAccTarget411
  dsimp only
  rcases bit_cases (β n1sValidStaticW411) with hvs0 | hvs1
  · rw [hvp, hvs_eq, hvs0, zero_mul, zero_mul, zero_mul, zero_mul]
  · obtain ⟨hmu7, h2mu⟩ := hvalid hvs1
    set s := bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))
    set uK := bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits)
    set mu := bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i))
    have hout_lt : norm1sHwProd t.kBits t.dCut (norm1sMant18 s) uK < 2 ^ t.wAcc :=
      (n1s_hwProd_lt_two_pow_wAcc t _ uK (n1s_norm1sMant18_lt s (bitsVal_lt_two_pow _))).2
    have hlt_eq : ((n1sCtxGuard411 t).fwdBits β₁) (n1sLtOutW411 t) =
        if norm1sHwProd t.kBits t.dCut (norm1sMant18 s) uK <
            accThr t.kBits t.dCut (clz18Log2 s - 2 * mu) then 1 else 0 := by
      have h1 := hlt_fn (by rw [hmu_eq]; exact hmu7) (by rw [hmu_eq, he]; exact h2mu)
        (by rw [he]; exact clz18Log2_le_17 s) (by rw [hout]; exact hout_lt)
      rw [hout, he, hmu_eq] at h1
      rw [h1]
      by_cases hc : norm1sHwProd t.kBits t.dCut (norm1sMant18 s) uK <
          accThr t.kBits t.dCut (clz18Log2 s - 2 * mu) <;> simp [hc, boolToZMod2]
    have hvp_eq : ((n1sCtxGuard411 t).fwdBits β₁) n1sValidProjW411 =
        if ∀ w : Fin 3, bitsVal (fun b : Fin 8 ↦ β (n1sProjW411 w b)) ≠ 128 then 1 else 0 := by
      rw [hvp, hvs_eq, hvs1, one_mul, hpr_eq 0, hpr_eq 1, hpr_eq 2]
      by_cases hAll : ∀ w : Fin 3, bitsVal (fun b : Fin 8 ↦ β (n1sProjW411 w b)) ≠ 128
      · rw [n1s_if_pos hAll, decide_eq_true (hAll 0), decide_eq_true (hAll 1),
          decide_eq_true (hAll 2)]
        rfl
      · rw [n1s_if_neg hAll]
        have hF : (decide (bitsVal (fun b ↦ β (n1sProjW411 0 b)) ≠ 128) &&
            decide (bitsVal (fun b ↦ β (n1sProjW411 1 b)) ≠ 128) &&
            decide (bitsVal (fun b ↦ β (n1sProjW411 2 b)) ≠ 128)) = false := by
          rw [Bool.eq_false_iff]
          intro hT
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hT
          exact hAll fun
            | ⟨0, _⟩ => hT.1.1
            | ⟨1, _⟩ => hT.1.2
            | ⟨2, _⟩ => hT.2
            | ⟨_ + 3, h⟩ => by omega
        rw [hF]
        rfl
    rw [hvp_eq, hlt_eq, hvs1, one_mul]

/-- Symbolic `T`-gate count of `n1sDFwd411 t v rComb`. -/
def n1sFwdT (t : Norm1sTier) : ℕ :=
  4 * 16 + ((4 * 59 + 4 * n1sBoothFwdAnds t) + (4 * (15 + 21 + 3 + t.wAcc) + 4))

/-- Full `M = 411` Stage-2 static forward program (`clz18` + barrel/Booth + guard). -/
def n1sFwdStatic411 (t : Norm1sTier) : TempPhaseProg 411 :=
  n1sCtxClz411.plug (.seq (n1sPBarFwd411 t) (n1sPGuard411 t))

theorem n1s_plug_seq_411_gen (mutW : Wire 411 → Prop) [DecidablePred mutW] (K : TempCtx 411)
    (hDisj : K.DisjointFrom mutW) (hSupp : K.SupportsBelowCtx 297)
    (hLift : TempCtxLiftEx 275 297 K) (p₁ p₂ : TempPhaseProg 411)
    (hv₁ : ValidCleanRem 411 (411 - 297) p₁) (hv₂ : ValidCleanRem 411 (411 - 297) p₂) (hcl₁ :
    ∀ γ, cleanRem 411 (411 - 297) γ → cleanRem 411 (411 - 297) (p₁.evalBits γ)) (hnon₁ : ∀ γ,
    cleanRem 411 (411 - 297) γ → ∀ w, ¬ mutW w → p₁.evalBits γ w = γ w) (hnon₂ : ∀ γ, cleanRem
    411 (411 - 297) γ → ∀ w, ¬ mutW w → p₂.evalBits γ w = γ w) : ValidCleanRem 411 (411 - 275)
    (K.plug (.seq p₁ p₂)) ∧ (∀ β : BitAssignment 411, cleanRem 411 (411 - 275) β → (K.plug
    (.seq p₁ p₂)).evalSign β = p₁.evalSign (K.fwdBits β) + p₂.evalSign (p₁.evalBits (K.fwdBits
    β))) ∧ (∀ β : BitAssignment 411, cleanRem 411 (411 - 275) β → ∀ w : Wire 411, (K.plug
    (.seq p₁ p₂)).evalBits β w = if mutW w then p₂.evalBits (p₁.evalBits (K.fwdBits β)) w else
    β w) := by
  have hvIn : ValidCleanRem 411 (411 - 297) (.seq p₁ p₂) :=
    ⟨411 - 297, by decide, hv₁, hv₂, hcl₁⟩
  obtain ⟨hv, _, hsgn, hbits⟩ :=
    Prod57BoothHoist.ScopedBlock.graft_mutating_clean
      (M := 411) (rem := 411 - 275) (curHole := 297)
      mutW K hDisj hSupp (by decide) K.fwdBits
      (TempCtxLiftEx.probe hLift) (.seq p₁ p₂) hvIn
      (fun γ hγ w hnw ↦ (hnon₂ (p₁.evalBits γ) (hcl₁ γ hγ) w hnw).trans (hnon₁ γ hγ w hnw))
  exact ⟨hv, fun β hβ ↦ hsgn β hβ, fun β hβ w ↦ hbits β hβ w⟩

theorem n1s_fwdStatic411_spec (t : Norm1sTier) : ValidCleanRem 411 (411 - 275)
    (n1sFwdStatic411 t) ∧ (∀ β : BitAssignment 411, cleanRem 411 (411 - 275) β →
    (n1sFwdStatic411 t).evalSign β = 0 ∧ cleanRem 411 (411 - 275) ((n1sFwdStatic411
    t).evalBits β) ∧ (∀ q : Wire 411, q ≠ n1sAccFlagW411 → (∀ k : Fin 32, q ≠ n1sOut32W411 k)
    → (n1sFwdStatic411 t).evalBits β q = β q) ∧ ((∀ k : Fin 32, β (n1sOut32W411 k) = 0) → β
    n1sAccFlagW411 = 0 → (β n1sValidStaticW411 = 1 → bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i))
    < 7 ∧ 2 * bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) ≤ clz18Log2 (bitsVal (fun i : Fin 18 ↦
    β (n1sSTrue18W411 i)))) → bitsVal (fun k : Fin 32 ↦ (n1sFwdStatic411 t).evalBits β
    (n1sOut32W411 k)) = norm1sHwProd t.kBits t.dCut (norm1sMant18 (bitsVal (fun i : Fin 18 ↦ β
    (n1sSTrue18W411 i)))) (bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits)) ∧
    (n1sFwdStatic411 t).evalBits β n1sAccFlagW411 = n1sAccTarget411 t β)) := by
  dsimp only [n1sFwdStatic411]
  obtain ⟨_, hdC, hsC, hlC⟩ := n1s_ctxClz411_pkg
  obtain ⟨hvB, _, hEvB⟩ := n1s_pBarFwd411_spec t
  obtain ⟨hvG, _, hEvG⟩ := n1s_pGuard411_spec t
  obtain ⟨hv, hsgn, hbits⟩ := n1s_plug_seq_411_gen
      (fun q ↦ q = n1sAccFlagW411 ∨ ∃ k : Fin 32, q = n1sOut32W411 k) n1sCtxClz411 hdC hsC hlC
      (n1sPBarFwd411 t) (n1sPGuard411 t) hvB hvG (fun γ hγ ↦ (hEvB γ hγ).2.1) (fun γ hγ w hnw
      ↦ (hEvB γ hγ).2.2.1 w (fun k hk ↦ hnw (Or.inr ⟨k, hk⟩)))
      (fun γ hγ w hnw ↦ (hEvG γ hγ).2.2.1 w (fun h ↦ hnw (Or.inl h)))
  refine ⟨hv, fun β hβ ↦ ?_⟩
  obtain ⟨hcl₁, hpres₁, heVal, _, hpres₂, hmVal⟩ := n1s_ctxClz_and_barrel_fwd β hβ
  let β₁ := n1sCtxClz411.fwdBits β
  obtain ⟨hsB, hcl_mid, hnonB, hvalB⟩ := hEvB β₁ hcl₁
  let β_mid := (n1sPBarFwd411 t).evalBits β₁
  obtain ⟨hsG, _, hnonG, hvalG⟩ := hEvG β_mid hcl_mid
  have hnon : ∀ q : Wire 411, q ≠ n1sAccFlagW411 → (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      (n1sCtxClz411.plug (.seq (n1sPBarFwd411 t) (n1sPGuard411 t))).evalBits β q = β q :=
    fun q h1 h2 ↦ (hbits β hβ q).trans (n1s_if_neg (fun h ↦ h.elim h1 (fun ⟨k, hk⟩ ↦ h2 k hk)))
  refine ⟨(hsgn β hβ).trans ((congrArg₂ (· + ·) hsB hsG).trans (add_zero (0 : ZMod 2))),
    fun w hw ↦ (hnon w (wire_ne_of_gt (by dsimp [n1sAccFlagW411]; omega))
      (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))).trans (hβ w hw),
    hnon, fun hout0 hacc0 hvalid ↦ ?_⟩
  have hout0_1 : ∀ k : Fin 32, β₁ (n1sOut32W411 k) = 0 :=
    fun k ↦ (hpres₁ _ (by dsimp [n1sOut32W411]; omega)).trans (hout0 k)
  have huK_eq : bitsVal (fun m : Fin t.kBits ↦ (n1sCtxBarrel411.fwdBits β₁) (n1sUKW411 t m)) =
      bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits) := by
    have hfn : (fun m : Fin t.kBits ↦ (n1sCtxBarrel411.fwdBits β₁) (n1sUKW411 t m)) =
        fun m ↦ β (n1sUKW411 t m) := funext fun m ↦ by
      have hr := (n1s_uKW411_range t m).2
      exact (hpres₂ _ (by omega)).trans (hpres₁ _ (by omega))
    exact (congrArg bitsVal hfn).trans (by rw [n1s_uKW411_bitsVal])
  have hout_mid : bitsVal (fun k : Fin 32 ↦ β_mid (n1sOut32W411 k)) = norm1sHwProd t.kBits
      t.dCut (norm1sMant18 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))))
      (bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits)) :=
      (hvalB hout0_1).trans (congrArg₂ (norm1sHwProd t.kBits t.dCut) hmVal huK_eq)
  have hout_final : bitsVal (fun k : Fin 32 ↦ (n1sCtxClz411.plug (.seq (n1sPBarFwd411 t)
      (n1sPGuard411 t))).evalBits β (n1sOut32W411 k)) = bitsVal
      (fun k : Fin 32 ↦ β_mid (n1sOut32W411 k)) :=
    congrArg bitsVal (funext fun k ↦
      (hbits β hβ (n1sOut32W411 k)).trans
        ((n1s_if_pos (Or.inr ⟨k, rfl⟩)).trans
          (hnonG (n1sOut32W411 k) (wire_ne_of_gt (by
            dsimp [n1sOut32W411,
              n1sAccFlagW411]; omega)))))
  have hacc_mid : β_mid n1sAccFlagW411 = 0 :=
    (hnonB n1sAccFlagW411 (fun k ↦
      wire_ne_of_lt (by dsimp [n1sAccFlagW411, n1sOut32W411]; omega))).trans
      ((hpres₁ n1sAccFlagW411 (by decide)).trans hacc0)
  have he_mid : bitsVal (fun b : Fin 5 ↦ β_mid (n1sEW411 b)) =
      clz18Log2 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))) := by
    have hfn : (fun b : Fin 5 ↦ β_mid (n1sEW411 b)) = fun b ↦ β₁ (n1sEW411 b) :=
      funext fun b ↦ hnonB (n1sEW411 b)
        (fun k ↦ wire_ne_of_gt (by dsimp [n1sEW411, n1sOut32W411]; omega))
    exact (congrArg bitsVal hfn).trans heVal
  have hacc_final : (n1sCtxClz411.plug (.seq (n1sPBarFwd411 t) (n1sPGuard411 t))).evalBits β
      n1sAccFlagW411 = n1sAccTarget411 t β := (hbits β hβ n1sAccFlagW411).trans ((n1s_if_pos
      (Or.inl rfl)).trans (hvalG.trans ((congrArg (· + ((n1sCtxGuard411 t).fwdBits β_mid)
      n1sValidProjW411 * ((n1sCtxGuard411 t).fwdBits β_mid) (n1sLtOutW411 t)) hacc_mid).trans
      ((zero_add _).trans (n1s_guardHole_eq_target t β β_mid hcl_mid (fun w hw _ h2 ↦ (hnonB w
      h2).trans (hpres₁ w hw)) he_mid hout_mid hvalid)))))
  exact ⟨hout_final.trans hout_mid, hacc_final⟩

/-- Symbolic `T`-gate count of `n1sDRev411 t v rComb`. -/
def n1sRevT (t : Norm1sTier) : ℕ :=
  4 * 16 + (4 * (15 + 21 + 3 + t.wAcc) + (4 * 59 + n1sBoothRevT t))

/-- Entry invariant on `M = 411` for Stage-6 `0 .TOFF` reverse circuit `n1sDRev411`. -/
def n1sRevInv411 (t : Norm1sTier) (β : BitAssignment 411) : Prop :=
  let s := bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))
  let uK := bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits)
  let mu := bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i))
  bitsVal (fun k : Fin 32 ↦ β (n1sOut32W411 k)) =
    norm1sHwProd t.kBits t.dCut (norm1sMant18 s) uK ∧
  (β n1sValidStaticW411 = 1 → mu < 7 ∧ 2 * mu ≤ clz18Log2 s) ∧
  β n1sAccFlagW411 = n1sAccTarget411 t β

/-- Full `M = 411` Stage-6 static reverse reference (`clz18` + guard + barrel/BoothRev). -/
def n1sRevStatic411 (t : Norm1sTier) : TempPhaseProg 411 :=
  n1sCtxClz411.plug (.seq (n1sPGuard411 t) (n1sPBarRev411 t))

theorem n1s_revHole_invs (t : Norm1sTier) (β : BitAssignment 411)
    (hβ : cleanRem 411 (411 - 275) β) (hInv : n1sRevInv411 t β) :
    let β₁ := n1sCtxClz411.fwdBits β
    let β₁' := (n1sPGuard411 t).evalBits β₁
    (((n1sCtxGuard411 t).fwdBits β₁) n1sAccFlagW411 =
      ((n1sCtxGuard411 t).fwdBits β₁) n1sValidProjW411 *
        ((n1sCtxGuard411 t).fwdBits β₁) (n1sLtOutW411 t)) ∧
    β₁' n1sAccFlagW411 = 0 ∧
    cleanRem 411 (411 - 297) β₁' ∧
    n1sBoothDoneInv t (n1sCtxBarrel411.fwdBits β₁') := by
  intro β₁ β₁'
  obtain ⟨hcl₁, hpres₁, heVal, _, _, _⟩ := n1s_ctxClz_and_barrel_fwd β hβ
  have hpres₁' : ∀ w : Wire 411, w.val < 275 → β₁ w = β w := hpres₁
  obtain ⟨hOut, hValid, hAcc⟩ := hInv
  have hout₁ : bitsVal (fun k : Fin 32 ↦ β₁ (n1sOut32W411 k)) = norm1sHwProd t.kBits t.dCut
      (norm1sMant18 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i))))
      (bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits)) := by
    have hfn : (fun k : Fin 32 ↦ β₁ (n1sOut32W411 k)) = fun k ↦ β (n1sOut32W411 k) :=
      funext fun k ↦ hpres₁' _ (by dsimp [n1sOut32W411]; omega)
    exact (congrArg bitsVal hfn).trans hOut
  have hProd := n1s_guardHole_eq_target t β β₁ hcl₁
    (fun w hw _ _ ↦ hpres₁' w hw) heVal hout₁ hValid
  have hHole1 : ((n1sCtxGuard411 t).fwdBits β₁) n1sAccFlagW411 =
      ((n1sCtxGuard411 t).fwdBits β₁) n1sValidProjW411 * ((n1sCtxGuard411 t).fwdBits β₁)
      (n1sLtOutW411 t) := ((n1s_ctxGuard411_fwd t β₁ hcl₁).2.1).trans
      ((hpres₁' n1sAccFlagW411 (by decide)).trans (hAcc.trans hProd.symm))
  obtain ⟨_, hcl₁', hnonG, hvalG⟩ := (n1s_pGuard411_spec t).2.2 β₁ hcl₁
  have hAcc0 : β₁' n1sAccFlagW411 = 0 := hvalG.trans ((congrArg (· + ((n1sCtxGuard411
      t).fwdBits β₁) n1sValidProjW411 * ((n1sCtxGuard411 t).fwdBits β₁) (n1sLtOutW411 t))
      ((hpres₁' n1sAccFlagW411 (by decide)).trans (hAcc.trans hProd.symm))).trans
      (CharTwo.add_self_eq_zero _))
  let β0 : BitAssignment 411 := Function.update β n1sAccFlagW411 0
  have hcl_β0 : cleanRem 411 (411 - 275) β0 := fun w hw ↦ by
    dsimp [β0]
    rw [Function.update_of_ne (wire_ne_of_gt (by dsimp [n1sAccFlagW411]; omega))]
    exact hβ w hw
  have hs_eq : bitsVal (fun i : Fin 18 ↦ β0 (n1sSTrue18W411 i)) =
      bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)) :=
    congrArg bitsVal (funext fun i ↦ by
      dsimp [β0]
      refine Function.update_of_ne (fun h ↦ ?_) _ _
      have hr := n1s_sTrue18W411_range i
      have hv := congrArg Fin.val h; dsimp [n1sAccFlagW411] at hv
      rcases hr with r | r | r <;> omega)
  have hβ₁'_eq : β₁' = n1sCtxClz411.fwdBits β0 := by
    obtain ⟨_, _, _, hClzEv⟩ := n1s_ctxClz411_scoped
    obtain ⟨hcl_a, hp_a, hout_a⟩ := hClzEv β hβ
    obtain ⟨hcl_b, hp_b, hout_b⟩ := hClzEv β0 hcl_β0
    have hp0 := hp_b (n1s_allBelow_of_noMutBelow 18 22
      (bitsVal (fun i ↦ β0 (n1sSTrue18W411 i))) clz18Ops clz18Ops_meta.2.1 n1s_clz18Ops_noMut)
    have hβ0_acc : β0 n1sAccFlagW411 = 0 := by simp [β0]
    funext w
    by_cases hw1 : w = n1sAccFlagW411
    · subst hw1
      exact hAcc0.trans (hβ0_acc.symm.trans (hp0 n1sAccFlagW411 (by decide)).symm)
    · refine (hnonG w hw1).trans ?_
      by_cases hw275 : w.val < 275
      · exact (hpres₁' w hw275).trans
          (((Function.update_of_ne hw1 _ _).symm).trans (hp0 w hw275).symm)
      · by_cases hw297 : w.val < 297
        · have hw_idx : w = ⟨275 + ((18 + (w.val - 275)) - 18), by omega⟩ :=
            Fin.ext (by dsimp; omega)
          rw [hw_idx]
          exact (hout_a (18 + (w.val - 275)) (by omega) (by omega)).trans ((congrArg (fun m ↦
            boolToZMod2 (getBoolAt (evalMicroList 18 clz18Ops (initBoolList 18 (18 + 22) m))
            (18 + (w.val - 275)))) hs_eq.symm).trans (hout_b (18 + (w.val - 275)) (by omega)
            (by omega)).symm)
        · exact (hcl_a w (by omega)).trans (hcl_b w (by omega)).symm
  obtain ⟨_, hpres₁_0, _, _, hpres₂_0, hmVal_0⟩ := n1s_ctxClz_and_barrel_fwd β0 hcl_β0
  refine ⟨hHole1, hAcc0, hcl₁', ?_⟩
  suffices hDone0 : n1sBoothDoneInv t (n1sCtxBarrel411.fwdBits (n1sCtxClz411.fwdBits β0)) from
    hβ₁'_eq.symm ▸ hDone0
  unfold n1sBoothDoneInv
  have hout_b2 : bitsVal (fun j : Fin 32 ↦
    (n1sCtxBarrel411.fwdBits (n1sCtxClz411.fwdBits β0)) (n1sOut32W411 j)) =
      bitsVal (fun j : Fin 32 ↦ β (n1sOut32W411 j)) :=
    congrArg bitsVal (funext fun j ↦
      (hpres₂_0 _ (by dsimp [n1sOut32W411]; omega)).trans
        ((hpres₁_0 _ (by dsimp [n1sOut32W411]; omega)).trans
          (Function.update_of_ne (wire_ne_of_gt (by
            dsimp [n1sOut32W411,
              n1sAccFlagW411]; omega)) _ _)))
  have huK_b2 : bitsVal (fun k : Fin t.kBits ↦
    (n1sCtxBarrel411.fwdBits (n1sCtxClz411.fwdBits β0)) (n1sUKW411 t k)) =
      bitsVal (fun k : Fin 38 ↦ β (n1sU38W411 k)) / 2 ^ (38 - t.kBits) := by
    have hfn : (fun k : Fin t.kBits ↦
      (n1sCtxBarrel411.fwdBits (n1sCtxClz411.fwdBits β0)) (n1sUKW411 t k)) =
        fun k ↦ β (n1sUKW411 t k) := funext fun k ↦ by
      have hr := (n1s_uKW411_range t k).2
      exact (hpres₂_0 _ (by omega)).trans ((hpres₁_0 _ (by omega)).trans
        (Function.update_of_ne (wire_ne_of_lt (by dsimp [n1sAccFlagW411]; omega)) _ _))
    exact (congrArg bitsVal hfn).trans (by rw [n1s_uKW411_bitsVal])
  exact hout_b2.trans (hOut.trans (congrArg₂ (norm1sHwProd t.kBits t.dCut) (hmVal_0.trans
    (congrArg norm1sMant18 hs_eq)) huK_b2).symm)

theorem n1s_revStatic411_spec (t : Norm1sTier) : ValidCleanRem 411 (411 - 275)
    (n1sRevStatic411 t) ∧ (∀ β : BitAssignment 411, cleanRem 411 (411 - 275) β →
    (n1sRevStatic411 t).evalSign β = 0 ∧ cleanRem 411 (411 - 275) ((n1sRevStatic411
    t).evalBits β) ∧ (∀ q : Wire 411, q ≠ n1sAccFlagW411 → (∀ k : Fin 32, q ≠ n1sOut32W411 k)
    → (n1sRevStatic411 t).evalBits β q = β q) ∧ (n1sRevInv411 t β → (n1sRevStatic411
    t).evalBits β n1sAccFlagW411 = 0 ∧ ∀ k : Fin 32, (n1sRevStatic411 t).evalBits β
    (n1sOut32W411 k) = 0)) := by
  dsimp only [n1sRevStatic411]
  obtain ⟨_, hdC, hsC, hlC⟩ := n1s_ctxClz411_pkg
  obtain ⟨hvG, _, hEvG⟩ := n1s_pGuard411_spec t
  obtain ⟨hvB, hEvB⟩ := n1s_pBarRev411_spec t
  obtain ⟨hv, hsgn, hbits⟩ := n1s_plug_seq_411_gen
      (fun q ↦ q = n1sAccFlagW411 ∨ ∃ k : Fin 32, q = n1sOut32W411 k) n1sCtxClz411 hdC hsC hlC
      (n1sPGuard411 t) (n1sPBarRev411 t) hvG hvB (fun γ hγ ↦ (hEvG γ hγ).2.1)
      (fun γ hγ w hnw ↦ (hEvG γ hγ).2.2.1 w (fun h ↦ hnw (Or.inl h))) (fun γ hγ w hnw ↦ (hEvB
      γ hγ).2.2.1 w (fun k hk ↦ hnw (Or.inr ⟨k, hk⟩)))
  refine ⟨hv, fun β hβ ↦ ?_⟩
  obtain ⟨hcl₁, _, _, _, _, _⟩ := n1s_ctxClz_and_barrel_fwd β hβ
  let β₁ := n1sCtxClz411.fwdBits β
  obtain ⟨hsG, hcl₁', _, _⟩ := hEvG β₁ hcl₁
  obtain ⟨hsB, _, hnonB, hzeroB⟩ := hEvB ((n1sPGuard411 t).evalBits β₁) hcl₁'
  have hnon : ∀ q : Wire 411, q ≠ n1sAccFlagW411 → (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      (n1sCtxClz411.plug (.seq (n1sPGuard411 t) (n1sPBarRev411 t))).evalBits β q = β q :=
    fun q h1 h2 ↦ (hbits β hβ q).trans (n1s_if_neg (fun h ↦ h.elim h1 (fun ⟨k, hk⟩ ↦ h2 k hk)))
  refine ⟨(hsgn β hβ).trans ((congrArg₂ (· + ·) hsG hsB).trans (add_zero (0 : ZMod 2))),
    fun w hw ↦ (hnon w (wire_ne_of_gt (by dsimp [n1sAccFlagW411]; omega))
      (fun k ↦ wire_ne_of_gt (by dsimp [n1sOut32W411]; omega))).trans (hβ w hw),
    hnon, fun hInv ↦ ?_⟩
  obtain ⟨_, hAcc0, _, hDone⟩ := n1s_revHole_invs t β hβ hInv
  exact ⟨(hbits β hβ n1sAccFlagW411).trans ((n1s_if_pos (Or.inl rfl)).trans
      ((hnonB n1sAccFlagW411
        (fun k ↦ wire_ne_of_lt (by dsimp [n1sAccFlagW411, n1sOut32W411]; omega))).trans hAcc0)),
    fun k ↦
      (hbits β hβ (n1sOut32W411 k)).trans ((n1s_if_pos (Or.inr ⟨k, rfl⟩)).trans (hzeroB hDone k))⟩

theorem n1s_step_wit {α : Type} (x : α) : ∃ y : α, y = x := ⟨x, rfl⟩

/-- Retained-scratch invariant across Stages 1..6 of `dCoreNorm1s_262` (`[233..258)` clean). -/
structure N1sRetainedInv (γ : BitAssignment 437) : Prop where
  hcl : cleanRem 437 (437 - 275) γ
  hcoin : γ coinOkW = if bitsVal (fun b ↦ γ (coinW b)) = 6 then 1 else 0
  hmu : ∀ j : Fin 3, γ (muW j) = if (shellMu3 (getU22 γ)).testBit j.val then 1 else 0
  hm : ∀ (w : Fin 3) (b : Fin 7),
    γ (p57MW w b) = if (shellMagCoord3 (getU22 γ) w).testBit b.val then 1 else 0
  hvs : γ validStaticW = validStaticVal216 γ
  hstrue : bitsVal (fun j ↦ γ (sTrue18WDefault j)) = sTrueRawVal γ
  hpbuf : ∀ (w : Fin 3) (b : Fin 8), γ (pBufW w b) =
    if (StepBOuter.axisFastVal
        (getProj γ w) (shellMagCoord3 (getU22 γ) w) (γ (p57S3W w)).val).testBit b.val
    then 1 else 0
  hz233 : ∀ w : Wire 437, 233 ≤ w.val → w.val < 258 → γ w = 0

theorem N1sRetainedInv.mu_val {γ : BitAssignment 437} (h : N1sRetainedInv γ) :
    bitsVal (fun j ↦ γ (muW j)) = shellMu3 (getU22 γ) :=
  bitsVal_eq_of_testBit _ _ (lt_trans (shellMu3_lt_seven _) (by decide)) h.hmu

theorem N1sRetainedInv.m_val {γ : BitAssignment 437} (h : N1sRetainedInv γ) (w : Fin 3) :
    bitsVal (fun b ↦ γ (p57MW w b)) = shellMagCoord3 (getU22 γ) w :=
  bitsVal_eq_of_testBit _ _ (s3ShellMagCoord3_lt_128 _ w) (h.hm w)

theorem N1sRetainedInv.of_agree_core {γ₁ γ₂ : BitAssignment 437} (h1 : N1sRetainedInv γ₁)
    (hcl2 : cleanRem 437 (437 - 275) γ₂)
    (hz2 : ∀ w : Wire 437, 233 ≤ w.val → w.val < 258 → γ₂ w = 0) (hag : ∀ q : Wire 437, ¬(107
    ≤ q.val ∧ q.val < 150) → ¬(201 ≤ q.val ∧ q.val < 258) → q.val < 275 → γ₂ q = γ₁ q) :
    N1sRetainedInv γ₂ := by
  have hu22 : getU22 γ₂ = getU22 γ₁ :=
    getU22_congr fun i ↦ hag _ (by dsimp [u22WAux]; omega)
      (by dsimp [u22WAux]; omega) (by dsimp [u22WAux]; omega)
  have hpr : ∀ w, getProj γ₂ w = getProj γ₁ w := fun w ↦
    Fin.ext (bitsVal_congrAux fun b ↦ hag _ (by dsimp [p57ProjW]; omega)
      (by dsimp [p57ProjW]; omega) (by dsimp [p57ProjW]; omega))
  have hc_fn : (fun b ↦ γ₂ (coinW b)) = fun b ↦ γ₁ (coinW b) := funext fun b ↦
    hag _ (by dsimp [coinW]; omega) (by dsimp [coinW]; omega) (by dsimp [coinW]; omega)
  have hs3_fn : ∀ w, γ₂ (p57S3W w) = γ₁ (p57S3W w) := fun w ↦
    hag _ (by dsimp [p57S3W]; omega) (by dsimp [p57S3W]; omega) (by dsimp [p57S3W]; omega)
  have hm_fn : ∀ w, (fun b ↦ γ₂ (p57MW w b)) = fun b ↦ γ₁ (p57MW w b) := fun w ↦ funext fun b ↦
    hag _ (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega)
  have hst_fn : (fun j ↦ γ₂ (sTrue18WDefault j)) = fun j ↦ γ₁ (sTrue18WDefault j) := funext fun j ↦
    by
    have hb := Slot3Exact216Oracle80.sTrue18WDefault216_bounds j
    exact hag _ (by omega) (by omega) (by omega)
  have hp_fn : ∀ w, (fun b ↦ γ₂ (p57ProjW w b)) = fun b ↦ γ₁ (p57ProjW w b) := fun w ↦
    funext fun b ↦
    hag _ (by dsimp [p57ProjW]; omega) (by dsimp [p57ProjW]; omega) (by dsimp [p57ProjW]; omega)
  refine
    { hcl := hcl2
      hcoin := by rw [hag coinOkW (by decide) (by decide) (by decide), hc_fn]; exact h1.hcoin
      hmu := fun j ↦ by
        rw [hag (muW j) (by dsimp [muW]; omega) (by dsimp [muW]; omega)
          (by dsimp [muW]; omega), hu22]; exact h1.hmu j
      hm := fun w b ↦ by
        rw [hag (p57MW w b) (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega)
          (by dsimp [p57MW]; omega), hu22]; exact h1.hm w b
      hvs := by
        rw [hag validStaticW (by decide) (by decide) (by decide)]
        unfold validStaticVal216; simp only [hc_fn, hu22, hs3_fn]; exact h1.hvs
      hstrue := by
        rw [hst_fn]; unfold sTrueRawVal; simp only [hp_fn, hm_fn, hs3_fn]; exact h1.hstrue
      hpbuf := fun w b ↦ by
        rw [hag (pBufW w b) (by dsimp [pBufW]; omega) (by dsimp [pBufW]; omega)
          (by dsimp [pBufW]; omega), hpr w, hu22, hs3_fn w]; exact h1.hpbuf w b
      hz233 := hz2 }

/-- Predicate marking `accWAux` (`149`) and `p57OutW` (`[201..258)`), untouched by `pStep1`. -/
def n1sKeep149_201_258 (w : Wire 437) : Bool :=
  decide (w.val = 149 ∨ (201 ≤ w.val ∧ w.val < 258))

theorem n1s_progNotTarget_seq {M : ℕ} (f : Wire M → Bool) (p q : TempPhaseProg M)
    (hp : progNotTarget f p = true) (hq : progNotTarget f q = true) :
    progNotTarget f (.seq p q) = true := by
  change (progNotTarget f p && progNotTarget f q) = true
  rw [hp, hq]; rfl

theorem n1s_pStep1_notTarget_keep : progNotTarget n1sKeep149_201_258 pStep1 = true := by
  unfold pStep1
  exact n1s_progNotTarget_seq _ _ _ (by decide +kernel)
    (n1s_progNotTarget_seq _ _ _ (by decide +kernel)
      (n1s_progNotTarget_seq _ _ _ (by decide +kernel)
        (n1s_progNotTarget_seq _ _ _ (by decide +kernel) (by decide +kernel))))

theorem n1s_st1_props (α : BitAssignment 149) :
    N1sRetainedInv (st1 α) ∧
    (∀ k : Fin 149, st1 α ⟨k.val, by omega⟩ = α k) ∧
    st1 α accWAux = 0 ∧
    (∀ j : Fin 32, st1 α ⟨201 + j.val, by omega⟩ = 0) := by
  have hcl0 : cleanRem 437 (437 - 275) (st0 α) :=
    (Slot3Norm1s36_161w.st0_clean_and_not_badA α).1
  have hcl1 : cleanRem 437 (437 - 275) (st1 α) :=
    (Slot3Norm1s36_161w.st1_clean_and_not_badA α).1
  obtain ⟨v₀, hv₀⟩ := n1s_step_wit
    (Slot3Exact216Oracle80.validStatic216_275.evalBits
      (StepBOuter.magUnpack275.evalBits
        (StepBOuter.coinMuXor275.evalBits (st0 α))))
  obtain ⟨γ₂, hγ₂⟩ := n1s_step_wit
    (Prod57BoothHoist.boothAdd57_275.evalBits (st1 α))
  obtain ⟨γ₃, hγ₃⟩ := n1s_step_wit
    (StepBOuter.accXor275.evalBits γ₂)
  have hcl_c := StepBOuter.coinMuXor275_spec.1.2.2.1 (st0 α) hcl0
  have hcl_m := StepBOuter.magUnpack275_spec.1.2.2.1 _ hcl_c
  have hcl_v : cleanRem 437 (437 - 275) v₀ :=
    hv₀.symm ▸ Slot3Exact216Oracle80.validStatic216_275_spec.1.2.2.1 _ hcl_m
  have hγ₃_eq : γ₃ = fwdPrep216_275.evalBits (padZeroBits (mClean := 288) α) := by
    have hst1 : st1 α = sTrue18FwdPBuf275.evalBits (axisStep3_fast_275.evalBits v₀) := by
      dsimp only [st1, pStep1]
      repeat rw [tempPhaseProg216_seq_evalBits]
      exact congrArg (fun x ↦ sTrue18FwdPBuf275.evalBits (axisStep3_fast_275.evalBits x)) hv₀.symm
    have hfast : st1 α = sTrue18FwdPBuf275.evalBits
        (StepBOuter.axisStep3_275.evalBits v₀) :=
      hst1.trans (congrArg sTrue18FwdPBuf275.evalBits (axisStep3_fast_275_eq_orig v₀ hcl_v))
    have horig : StepBOuter.accXor275.evalBits
        (Prod57BoothHoist.boothAdd57_275.evalBits
          (sTrue18FwdPBuf275.evalBits
            (StepBOuter.axisStep3_275.evalBits v₀))) =
        fwdPrep216_275.evalBits (padZeroBits (mClean := 288) α) :=
      (congrArg (fun x ↦ StepBOuter.accXor275.evalBits
          (Prod57BoothHoist.boothAdd57_275.evalBits
            (sTrue18FwdPBuf275.evalBits
              (StepBOuter.axisStep3_275.evalBits x)))) hv₀).trans
        (Slot3Exact216Oracle80.fwdPrep216_275_evalBits (st0 α)).symm
    exact hγ₃.trans ((congrArg StepBOuter.accXor275.evalBits
      (hγ₂.trans (congrArg Prod57BoothHoist.boothAdd57_275.evalBits hfast))).trans
      horig)
  have hAct3 : ∀ k : Fin 149, γ₃ ⟨k.val, by omega⟩ = α k :=
    fun k ↦ (congrFun hγ₃_eq ⟨k.val, by omega⟩).trans ((fwdPrep216_275_spec.2.2.2 α).1 k)
  have hInv3 : RetainedInv216 γ₃ := hγ₃_eq.symm ▸ (fwdPrep216_275_spec.2.2.2 α).2
  obtain ⟨hcl₂_raw, hnon₂_raw, _⟩ :=
    Prod57BoothHoist.boothAdd57_275_spec.2.2.2 (st1 α) hcl1
  have hcl₂ : cleanRem 437 (437 - 275) γ₂ := hγ₂.symm ▸ hcl₂_raw
  have hag13 : ∀ q : Wire 437, q.val ≠ 149 → ¬(201 ≤ q.val ∧ q.val < 258) → st1 α q = γ₃ q :=
    fun q h149 h201 ↦ by
      have h32 : γ₃ q = γ₂ q :=
        (congrFun hγ₃ q).trans
          (StepBOuter.accXor275_spec.1.2.2.2 γ₂ hcl₂ q
            (fun h ↦ h149 (by subst h; rfl)))
      have h21 : γ₂ q = st1 α q :=
        (congrFun hγ₂ q).trans
          (hnon₂_raw q (fun m hm ↦ by
            subst hm; exact h201 ⟨by dsimp [p57OutW]; omega, by dsimp [p57OutW]; omega⟩))
      exact (h32.trans h21).symm
  have hz_keep : ∀ w : Wire 437, (w.val = 149 ∨ (201 ≤ w.val ∧ w.val < 258)) → st1 α w = 0 :=
    fun w hw ↦ by
      have hk : n1sKeep149_201_258 w = true := decide_eq_true hw
      have hp :=
        progNotTarget_evalBits n1sKeep149_201_258 pStep1 n1s_pStep1_notTarget_keep (st0 α) w hk
      change st1 α w = st0 α w at hp
      exact hp.trans (StepBBlock0.padZeroBits149_clean α w (by omega))
  have hInv1 : N1sRetainedInv (st1 α) := by
    have hu22 : getU22 (st1 α) = getU22 γ₃ :=
      getU22_congr fun i ↦ hag13 _ (by dsimp [u22WAux]; omega) (by dsimp [u22WAux]; omega)
    have hpr : ∀ w, getProj (st1 α) w = getProj γ₃ w := fun w ↦
      Fin.ext (bitsVal_congrAux fun b ↦
        hag13 _ (by dsimp [p57ProjW]; omega) (by dsimp [p57ProjW]; omega))
    have hc_fn : (fun b ↦ st1 α (coinW b)) = fun b ↦ γ₃ (coinW b) := funext fun b ↦
      hag13 _ (by dsimp [coinW]; omega) (by dsimp [coinW]; omega)
    have hs3_fn : ∀ w, st1 α (p57S3W w) = γ₃ (p57S3W w) := fun w ↦
      hag13 _ (by dsimp [p57S3W]; omega) (by dsimp [p57S3W]; omega)
    have hm_fn : ∀ w, (fun b ↦ st1 α (p57MW w b)) = fun b ↦ γ₃ (p57MW w b) := fun w ↦ funext fun b ↦
      hag13 _ (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega)
    have hst_fn : (fun j ↦ st1 α (sTrue18WDefault j)) = fun j ↦ γ₃ (sTrue18WDefault j) :=
      funext fun j ↦ by
      have hb := Slot3Exact216Oracle80.sTrue18WDefault216_bounds j
      exact hag13 _ (by omega) (by omega)
    have hp_fn : ∀ w, (fun b ↦ st1 α (p57ProjW w b)) = fun b ↦ γ₃ (p57ProjW w b) := fun w ↦
      funext fun b ↦
      hag13 _ (by dsimp [p57ProjW]; omega) (by dsimp [p57ProjW]; omega)
    refine
      { hcl := hcl1
        hcoin := by rw [hag13 coinOkW (by decide) (by decide), hc_fn]; exact hInv3.hcoin
        hmu := fun j ↦
          by rw [hag13 (muW j) (by dsimp [muW]; omega) (by dsimp [muW]; omega),
          hu22]; exact hInv3.hmu j
        hm := fun w b ↦
          by rw [hag13 (p57MW w b) (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega),
          hu22]; exact hInv3.hm w b
        hvs := by
          rw [hag13 validStaticW (by decide) (by decide)]; unfold validStaticVal216; simp only
          [hc_fn, hu22, hs3_fn]; exact hInv3.hvs
        hstrue := by
          rw [hst_fn]; unfold sTrueRawVal; simp only [hp_fn, hm_fn, hs3_fn]; exact hInv3.hstrue
        hpbuf := fun w b ↦
          by rw [hag13 (pBufW w b) (by dsimp [pBufW]; omega) (by dsimp [pBufW]; omega), hpr w, hu22,
          hs3_fn w]; exact hInv3.hpbuf w b
        hz233 := fun w h1 h2 ↦ hz_keep w (Or.inr ⟨by omega, h2⟩) }
  exact ⟨hInv1,
    fun k ↦ (hag13 ⟨k.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)).trans (hAct3 k),
    hz_keep accWAux (Or.inl rfl),
    fun j ↦ hz_keep ⟨201 + j.val, by omega⟩ (Or.inr ⟨by dsimp; omega, by dsimp; omega⟩)⟩

theorem n1s_accBit_eq_s3AcceptNorm1s (t : Norm1sTier) (α107 : BitAssignment 107)
    {γ : BitAssignment 437} (hInv : N1sRetainedInv γ)
    (hlt107 : ∀ k : Fin 107, γ ⟨k.val, by omega⟩ = α107 k) :
    γ validStaticW *
      (if ∀ w : Fin 3, (getProj γ w).val ≠ 128 then 1 else 0) *
      (if norm1sHwProd t.kBits t.dCut (norm1sMant18 (sTrueRawVal γ))
            (bitsVal (fun k : Fin 38 ↦ γ (p57U38W k)) / 2 ^ (38 - t.kBits)) <
          accThr t.kBits t.dCut (clz18Log2 (sTrueRawVal γ) - 2 * shellMu3 (getU22 γ))
        then 1 else 0) =
      if s3AcceptNorm1s t hmPay80 ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)) =
        true
      then 1 else 0 := by
  let z80 := (basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)
  obtain ⟨hProj, hCoin, hU22, hS3, _, _, _, _⟩ := embedAlpha107_fields α107
  have hProjEq : ∀ w : Fin 3, projAxisField ((momSysReg 80).extractIndex z80) w = getProj γ w :=
    fun w ↦ Fin.ext ((hProj w).trans (bitsVal_congrAux fun b ↦
      (hlt107 ⟨8 * w.val + b.val, by omega⟩).symm))
  have hCoinEq : bitsVal (fun b ↦ γ (coinW b)) = ((momCoinReg 80).extractIndex z80).val :=
    (bitsVal_congrAux fun b ↦ hlt107 ⟨24 + b.val, by omega⟩).trans hCoin.symm
  have hU22Eq : getU22 γ = (s3U22Core hmPay80).extractIndex z80 :=
    Fin.ext ((bitsVal_congrAux fun b ↦ hlt107 ⟨27 + b.val, by omega⟩).trans hU22.symm)
  have hS3Eq : ∀ w : Fin 3, (γ (p57S3W w)).val = signBit3 ((s3S3Core hmPay80).extractIndex z80) w :=
    fun w ↦ (congrArg ZMod.val (hlt107 ⟨49 + w.val, by omega⟩)).trans (hS3 w).symm
  have hU38Eq := Slot3Exact216Oracle80.u38_216_val_eq α107 hlt107
  dsimp only at hU38Eq
  have hGridIff : (∀ w : Fin 3, (getProj γ w).val ≠ 128) ↔
      s3ProjGridBool ((momSysReg 80).extractIndex z80) = true := by
    rw [MomSlots35Slot3ProjNuclear.s3ProjGridBool_eq_true_iff]
    exact forall_congr' fun w ↦ by rw [hProjEq w]
  rw [hInv.hvs]
  set coin := (momCoinReg 80).extractIndex z80
  set gBool := s3ProjGridBool ((momSysReg 80).extractIndex z80)
  set u22 := (s3U22Core hmPay80).extractIndex z80
  set s3 := (s3S3Core hmPay80).extractIndex z80
  set c8 := (s3C8Core hmPay80).extractIndex z80
  set f30 := (s3Fine30Core hmPay80).extractIndex z80
  set pAx := projAxisField ((momSysReg 80).extractIndex z80)
  change validStaticVal216 γ * (if ∀ w : Fin 3, (getProj γ w).val ≠ 128 then 1 else 0)
    * (if norm1sHwProd t.kBits t.dCut (norm1sMant18 (sTrueRawVal γ)) (bitsVal (fun k : Fin 38
    ↦ γ (p57U38W k)) / 2 ^ (38 - t.kBits)) < accThr t.kBits t.dCut (clz18Log2 (sTrueRawVal γ)
    - 2 * shellMu3 (getU22 γ)) then 1 else 0) = if (decide (coin.val = 6) && gBool &&
    validShellNu3 u22 s3 && norm1sRadAccept t (shellMu3 u22) ((s3ProjStepHw (pAx 0)
    (shellMagCoord3 u22 0) (signBit3 s3 0)).2.1 * (s3ProjStepHw (pAx 0) (shellMagCoord3 u22 0)
    (signBit3 s3 0)).2.1 + (s3ProjStepHw (pAx 1) (shellMagCoord3 u22 1) (signBit3 s3 1)).2.1 *
    (s3ProjStepHw (pAx 1) (shellMagCoord3 u22 1) (signBit3 s3 1)).2.1 + (s3ProjStepHw (pAx 2)
    (shellMagCoord3 u22 2) (signBit3 s3 2)).2.1 * (s3ProjStepHw (pAx 2) (shellMagCoord3 u22 2)
    (signBit3 s3 2)).2.1) (f30.val + 2 ^ 30 * c8.val)) = true then 1 else 0
  clear_value coin gBool u22 s3 c8 f30 pAx
  clear z80 hProj hCoin hU22 hS3 hlt107
  by_cases hGrid : ∀ w : Fin 3, (getProj γ w).val ≠ 128
  · have hGridB : gBool = true := hGridIff.mp hGrid
    have hsTrue : sTrueRawVal γ =
        (s3ProjStepHw (pAx 0) (shellMagCoord3 u22 0) (signBit3 s3 0)).2.1 *
          (s3ProjStepHw (pAx 0) (shellMagCoord3 u22 0) (signBit3 s3 0)).2.1 +
        (s3ProjStepHw (pAx 1) (shellMagCoord3 u22 1) (signBit3 s3 1)).2.1 *
          (s3ProjStepHw (pAx 1) (shellMagCoord3 u22 1) (signBit3 s3 1)).2.1 +
        (s3ProjStepHw (pAx 2) (shellMagCoord3 u22 2) (signBit3 s3 2)).2.1 *
          (s3ProjStepHw (pAx 2) (shellMagCoord3 u22 2) (signBit3 s3 2)).2.1 := by
      rw [Prod57BoothHoist.sTrueRawVal_eq_of_ne_128 γ
        (getProj γ) (fun _ ↦ rfl) hGrid, Fin.sum_univ_three]
      dsimp only
      simp only [hInv.m_val, hU22Eq, hS3Eq, ← hProjEq]
    have hVshIff : (32768 ≤ u22.val ∧ 2 ^ shellMu3 u22 ≤ max (shellMagCoord3 u22 0) (max
        (shellMagCoord3 u22 1) (shellMagCoord3 u22 2)) ∧ (∀ w : Fin 3, ¬(shellMagCoord3 u22 w
        = 0 ∧ signBit3 s3 w = 1))) ↔ validShellNu3 u22 s3 = true := by
      unfold validShellNu3; simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    by_cases hvs1 : validStaticVal216 γ = 1
    · have hle_mu : 2 * shellMu3 (getU22 γ) ≤ clz18Log2 (sTrueRawVal γ) :=
        two_mul_mu_le_clz18Log2 hvs1 hInv.m_val
      have hcv : coin.val = 6 ∧ validShellNu3 u22 s3 = true := by
        unfold validStaticVal216 at hvs1
        rw [hCoinEq] at hvs1; simp only [hU22Eq, hS3Eq, hVshIff] at hvs1
        by_cases hc : coin.val = 6 <;> cases hv : validShellNu3 u22 s3 <;> simp [hc, hv] at hvs1 ⊢
      rw [hvs1, n1s_if_pos hGrid, mul_one, one_mul, hGridB, hcv.2, decide_eq_true hcv.1]
      unfold norm1sRadAccept Slot3Norm1s36Physics80.norm1sRadAccept
      rw [← hsTrue, ← hU38Eq, ← hU22Eq]
      simp only [Bool.true_and]
      rw [decide_eq_true hle_mu, Bool.true_and]
      by_cases hlt : norm1sHwProd t.kBits t.dCut (norm1sMant18 (sTrueRawVal γ))
            (bitsVal (fun k : Fin 38 ↦ γ (p57U38W k)) / 2 ^ (38 - t.kBits)) <
          accThr t.kBits t.dCut (clz18Log2 (sTrueRawVal γ) - 2 * shellMu3 (getU22 γ))
      · rw [n1s_if_pos hlt, decide_eq_true hlt, n1s_if_pos rfl]
      · rw [n1s_if_neg hlt, decide_eq_false hlt, n1s_if_neg Bool.noConfusion]
    · have hvs0 : validStaticVal216 γ = 0 := by
        rcases bit_cases (validStaticVal216 γ) with h0 | h1
        · exact h0
        · exact absurd h1 hvs1
      have hcv_f : (decide (coin.val = 6) && gBool && validShellNu3 u22 s3) = false := by
        unfold validStaticVal216 at hvs0
        rw [hCoinEq] at hvs0; simp only [hU22Eq, hS3Eq, hVshIff] at hvs0
        by_cases hc : coin.val = 6 <;> cases hv : validShellNu3 u22 s3 <;>
          simp [hc, hv, hGridB] at hvs0 ⊢
      rw [hvs0, zero_mul, zero_mul, hcv_f, Bool.false_and, n1s_if_neg Bool.noConfusion]
  · have hGridF : gBool = false := Bool.eq_false_iff.mpr (fun hb ↦ hGrid (hGridIff.mpr hb))
    rw [n1s_if_neg hGrid, mul_zero, zero_mul, hGridF]
    simp

theorem n1s_rejKick_evalSign (t : Norm1sTier) (α : BitAssignment 149)
    {γ : BitAssignment 437} (hInv : N1sRetainedInv γ)
    (hlt107 : ∀ k : Fin 107, γ ⟨k.val, by omega⟩ = α (Fin.castLE (by decide) k))
    (hacc : γ accWAux =
      if s3AcceptNorm1s t hmPay80
          ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 (fun i ↦
            α (Fin.castLE (by decide) i)))) = true
      then 1 else 0) :
    rejKick275.evalSign γ = corePhase149_norm1s t α := by
  let α107 : BitAssignment 107 := fun i ↦ α (Fin.castLE (by decide) i)
  obtain ⟨_, hCoin, _, _, _, _, hBPar, _⟩ := embedAlpha107_fields α107
  set z80 := (basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)
  have hCoinEq : bitsVal (fun b ↦ γ (coinW b)) = ((momCoinReg 80).extractIndex z80).val :=
    (bitsVal_congrAux fun b ↦ hlt107 ⟨24 + b.val, by omega⟩).trans hCoin.symm
  have hBParEq : γ bParWAux = basisBits (momCoreWires 80) z80 (s3BParCore hmPay80) :=
    (hlt107 ⟨90, by decide⟩).trans hBPar.symm
  rw [rejKick275_spec.2.2.2 γ hInv.hcl, hInv.hcoin, hCoinEq, hacc, hBParEq]
  exact Slot3Exact216Oracle80.rejPhase216_ite_eq _ _ _

theorem n1s_shift42_eq (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α107 : BitAssignment 107) (z80 : Fin (2 ^ momCoreWires 80)) (hz80 : (basisBitsEquiv
    (momCoreWires 80)).symm (embedAlpha107 α107) = z80) : s3Shift42_norm1s t cfg α107 = if
    s3AcceptNorm1s t hmPay80 z80 = true then ((-∑ w : Fin 3, (twosMomentum ((momSysReg
    80).extractIndex (s3CoreMapNorm1s t hmPay80 z80)) .projectile - twosMomentum ((momSysReg
    80).extractIndex z80) .projectile) w * nearestProtonCoord 42 (SpecsAux.SpecMirror.cellVolume ^
    (1 / 3 : ℝ)) ((trunc36Cfg cfg).nuclei (s3NucleusIdx216 hmPay80 z80) w)).emod (2 ^ 42 :
    ℤ)).toNat else 0 := by
  unfold s3Shift42_norm1s Slot3Norm1s36Physics80.s3Shift42Norm1s
    Slot3Norm1s36Physics80.s3Shift48_36
  dsimp only
  change (if s3AcceptNorm1s t hmPay80 ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107))
    = true
      then _ else 0) / 64 = _
  rw [hz80]
  by_cases ha : s3AcceptNorm1s t hmPay80 z80 = true
  · rw [n1s_if_pos ha, n1s_if_pos ha, Nat.mul_div_right _ (by decide)]
  · rw [n1s_if_neg ha, n1s_if_neg ha]

theorem n1s_corePerm149_lt107 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α : BitAssignment 149) (k : Fin 149) (hk : k.val < 107) : corePerm149_norm1s t cfg α k =
    swapRejMap107_norm1s t (fun i ↦ α (Fin.castLE (by decide) i)) ⟨k.val, hk⟩ := by
  unfold corePerm149_norm1s Slot3Norm1s36Physics80.corePerm149Norm1s
  exact n1s_dif_pos hk

theorem n1s_corePerm149_natAdd (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α : BitAssignment 149) (j : Fin 42) :
    corePerm149_norm1s t cfg α (Fin.natAdd 107 j) =
      let α107 : BitAssignment 107 := fun i ↦ α (Fin.castLE (by decide) i)
      let vNew42 : ℕ :=
        (bitsVal (fun m : Fin 42 ↦ α (Fin.natAdd 107 m)) + s3Shift42_norm1s t cfg α107) % 2 ^ 42
      if vNew42.testBit j.val then 1 else 0 := by
  unfold corePerm149_norm1s Slot3Norm1s36Physics80.corePerm149Norm1s
  rw [n1s_dif_neg (by dsimp [Fin.natAdd]; omega)]
  have hsub : (Fin.natAdd 107 j).val - 107 = j.val := by dsimp [Fin.natAdd]; omega
  rw [hsub]

theorem n1s_midKick36_cat42_aux (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α : BitAssignment 149) {γ : BitAssignment 437}
    (hInv : N1sRetainedInv γ)
    (hγ_lt : ∀ k : Fin 149, γ ⟨k.val, by omega⟩ = α k)
    (hAccBit : γ accWAux =
      if s3AcceptNorm1s t hmPay80
          ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 (fun i ↦
            α (Fin.castLE (by decide) i)))) = true
      then 1 else 0)
    (γ₂ : BitAssignment 437)
    (hMidMod :
      ((bitsVal (fun m : Fin 42 ↦ γ₂ ⟨107 + m.val, by omega⟩) : ℤ)).emod (2 ^ 42 : ℤ) =
        ((bitsVal (fun m : Fin 42 ↦
          γ ⟨107 + m.val, by omega⟩) : ℤ) + ((γ ⟨149, by decide⟩).val : ℤ) *
          ∑ w : Fin 3,
            (TwosCompAndWire0Cancel.twosComp8Int
                ⟨bitsVal (fun b : Fin 8 ↦
                  γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩ -
              TwosCompAndWire0Cancel.twosComp8Int
                ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩) *
              (FastMidKick275Aux.fmkNegCoordTable (trunc36Cfg cfg) w
                ⟨(γ ⟨91 + (0 : Fin 16).val, by omega⟩).val +
                    2 * (γ ⟨91 + (1 : Fin 16).val, by omega⟩).val +
                    4 * Slot3Exact216Oracle80.s3NucleusQ27
                      (fun i : Fin 16 ↦ γ ⟨91 + i.val, by omega⟩) +
                    128 * (γ ⟨90, by decide⟩).val,
                  by have := ZMod.val_lt (γ ⟨91 + (0 : Fin 16).val, by omega⟩)
                     have := ZMod.val_lt (γ ⟨91 + (1 : Fin 16).val, by omega⟩)
                     have := Slot3Exact216Oracle80.s3NucleusQ27_lt
                       (fun i : Fin 16 ↦ γ ⟨91 + i.val, by omega⟩)
                     have := ZMod.val_lt (γ ⟨90, by decide⟩); omega⟩ : ℤ)).emod
          (2 ^ 42 : ℤ))
    (j : Fin 42) :
    γ₂ ⟨107 + j.val, by omega⟩ = corePerm149_norm1s t cfg α (Fin.natAdd 107 j) := by
  rw [n1s_corePerm149_natAdd t cfg α j]
  dsimp only
  set α107 : BitAssignment 107 := fun i ↦ α (Fin.castLE (by decide) i)
  have hlt107 : ∀ k : Fin 107, γ ⟨k.val, by omega⟩ = α107 k :=
    fun k ↦ hγ_lt (Fin.castLE (by decide) k)
  obtain ⟨hProj, _e1, hU22, hS3, _e2, _e3, hBPar, hU16⟩ := embedAlpha107_fields α107
  clear _e1 _e2 _e3
  obtain ⟨z80, hz80⟩ := n1s_step_wit ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107))
  have hsh42_def := n1s_shift42_eq t cfg α107 z80 hz80.symm
  change γ accWAux =
    if s3AcceptNorm1s t hmPay80 ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)) =
    true then 1 else 0 at hAccBit
  rw [← hz80] at hAccBit hProj hU22 hS3 hBPar hU16
  clear hz80
  obtain ⟨sh42, hsh42_eq⟩ := n1s_step_wit (s3Shift42_norm1s t cfg α107)
  rw [← hsh42_eq] at hsh42_def ⊢; clear hsh42_eq
  let vNew42 : ℕ := (bitsVal (fun m : Fin 42 ↦ α (Fin.natAdd 107 m)) + sh42) % 2 ^ 42
  have hcOut_emod : ((bitsVal (fun m : Fin 42 ↦
    γ₂ ⟨107 + m.val, by omega⟩) : ℤ)).emod (2 ^ 42 : ℤ) =
      (bitsVal (fun m : Fin 42 ↦ γ₂ ⟨107 + m.val, by omega⟩) : ℤ) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (bitsVal_lt_two_pow _))
  have hcOld_eq : bitsVal (fun m : Fin 42 ↦ γ ⟨107 + m.val, by omega⟩) =
      bitsVal (fun m : Fin 42 ↦ α (Fin.natAdd 107 m)) :=
    bitsVal_congrAux
      (g := fun m : Fin 42 ↦ α (Fin.natAdd 107 m))
      fun m ↦ (congrArg γ (Fin.ext rfl)).trans (hγ_lt (Fin.natAdd 107 m))
  let u16W : Fin 16 → Wire 437 := fun i ↦ ⟨91 + i.val, by omega⟩
  let idx0 : Fin 256 :=
    ⟨(γ (u16W 0)).val + 2 * (γ (u16W 1)).val +
        4 * Slot3Exact216Oracle80.s3NucleusQ27 (fun i ↦ γ (u16W i)) +
        128 * (γ ⟨90, by decide⟩).val,
      by have := ZMod.val_lt (γ (u16W 0)); have := ZMod.val_lt (γ (u16W 1))
         have := Slot3Exact216Oracle80.s3NucleusQ27_lt (fun i ↦ γ (u16W i))
         have := ZMod.val_lt (γ ⟨90, by decide⟩); omega⟩
  let pNew0 : Fin 3 → Fin 256 := fun w ↦
    ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
  let pOld0 : Fin 3 → Fin 256 := fun w ↦
    ⟨bitsVal (fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩), bitsVal_lt_two_pow _⟩
  let tc8 := TwosCompAndWire0Cancel.twosComp8Int
  let fmkTbl := FastMidKick275Aux.fmkNegCoordTable (trunc36Cfg cfg)
  have hShiftMod : (((bitsVal (fun m : Fin 42 ↦ α (Fin.natAdd 107 m)) : ℤ) + ((γ accWAux).val
      : ℤ) * ∑ w : Fin 3, (tc8 (pNew0 w) - tc8 (pOld0 w)) * (fmkTbl w idx0 : ℤ)).emod (2 ^ 42
      : ℤ)) = (vNew42 : ℤ) := by
    have hvNew_cast : (vNew42 : ℤ) =
        ((bitsVal (fun m : Fin 42 ↦ α (Fin.natAdd 107 m)) : ℤ) + (sh42 : ℤ)).emod (2 ^ 42 : ℤ) := by
      dsimp only [vNew42]; rw [Int.natCast_emod, Int.natCast_add]; rfl
    rw [hvNew_cast]
    cases hz : s3AcceptNorm1s t hmPay80 z80 with
    | false =>
        have hne : ¬(s3AcceptNorm1s t hmPay80 z80 = true) := by rw [hz]; exact Bool.noConfusion
        have hacc0 : (γ accWAux).val = 0 := by rw [hAccBit, n1s_if_neg hne]; rfl
        have hsh0 : sh42 = 0 := by rw [hsh42_def, n1s_if_neg hne]
        rw [hacc0, hsh0]; simp only [Nat.cast_zero, zero_mul, add_zero]
    | true =>
        have hacc1 : (γ accWAux).val = 1 := by rw [hAccBit, n1s_if_pos hz]; rfl
        have hU22Eq : getU22 γ = (s3U22Core hmPay80).extractIndex z80 :=
          Fin.ext ((bitsVal_congrAux
            (g := fun b : Fin 22 ↦ α107 ⟨27 + b.val, by omega⟩)
            fun b ↦
              (congrArg γ (Fin.ext rfl)).trans (hlt107 ⟨27 + b.val, by omega⟩)).trans hU22.symm)
        have hS3Eq : ∀ w : Fin 3,
          (γ (p57S3W w)).val = signBit3 ((s3S3Core hmPay80).extractIndex z80) w :=
          fun w ↦
            (congrArg ZMod.val ((congrArg γ (Fin.ext rfl)).trans (hlt107 ⟨49 + w.val, by
            omega⟩))).trans (hS3 w).symm
        have hpOldEq : ∀ w : Fin 3, pOld0 w = projAxisField ((momSysReg 80).extractIndex z80) w :=
          fun w ↦ Fin.ext ((bitsVal_congrAux
            (g := fun b : Fin 8 ↦ α107 ⟨8 * w.val + b.val, by omega⟩)
            fun b ↦ hlt107 ⟨8 * w.val + b.val, by omega⟩).trans (hProj w).symm)
        have hGrid : ∀ w : Fin 3, (projAxisField ((momSysReg 80).extractIndex z80) w).val ≠ 128 :=
          by
          have hg : s3ProjGridBool ((momSysReg 80).extractIndex z80) = true := by
            unfold s3AcceptNorm1s Slot3Norm1s36Physics80.s3AcceptNorm1s at hz
            simp only [Bool.and_eq_true] at hz; exact hz.1.1.2
          exact (MomSlots35Slot3ProjNuclear.s3ProjGridBool_eq_true_iff _).mp hg
        have hpNewEq : ∀ w : Fin 3,
            pNew0 w =
              projAxisField ((momSysReg 80).extractIndex (s3CoreMapNorm1s t hmPay80 z80)) w := by
          intro w
          rcases Slot3Norm1s36Physics80.s3CoreMapNorm1s_fields hz with
            ⟨_s0, hsys', _s2, _s3, _s4, _s5, _s6, _s7, _s8, _s9⟩
          clear _s0 _s2 _s3 _s4 _s5 _s6 _s7 _s8 _s9
          rw [hsys', (MomSlots35Slot3ProjNuclear.s3UpdateSysProj_fields _ _).2 w]
          apply Fin.ext
          have hbVal : bitsVal (fun b ↦ γ (pBufW w b)) =
              StepBOuter.axisFastVal
                (getProj γ w) (shellMagCoord3 (getU22 γ) w) (γ (p57S3W w)).val :=
            bitsVal_eq_of_testBit _ _
              (StepBOuter.axisFastVal_lt _ _ _) (hInv.hpbuf w)
          have hpr : getProj γ w = projAxisField ((momSysReg 80).extractIndex z80) w :=
            (Fin.ext (bitsVal_congrAux
              (g := fun b : Fin 8 ↦ γ ⟨8 * w.val + b.val, by omega⟩)
              fun b ↦ congrArg γ (Fin.ext (by dsimp [p57ProjW])))).trans (hpOldEq w)
          have hpNew_w : bitsVal (fun b : Fin 8 ↦ γ ⟨150 + 8 * w.val + b.val, by omega⟩) =
              bitsVal (fun b ↦ γ (pBufW w b)) :=
            bitsVal_congrAux
              (g := fun b : Fin 8 ↦ γ (pBufW w b))
              fun b ↦ congrArg γ (Fin.ext (by dsimp [pBufW]))
          dsimp only [pNew0]
          rw [hpNew_w, hbVal, hpr, hU22Eq, hS3Eq w]
          exact StepBOuter.axisFastStep_eq_s3ProjStepHw _ _ _ (hGrid w)
            (s3ShellMagCoord3_lt_128 _ w)
            (MomSlots35Slot3ProjNuclear.s3SignBit3_le_one _ w)
        have hIdxNuc : ∀ w : Fin 3, (fmkTbl w idx0 : ℤ) = (-nearestProtonCoord 42
            (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ)) ((trunc36Cfg cfg).nuclei (s3NucleusIdx216
            hmPay80 z80) w)).emod (2 ^ 42 : ℤ) := by
          intro w
          have hu16_val : bitsVal (fun i ↦
            γ (u16W i)) = ((s3U16Core hmPay80).extractIndex z80).val :=
            (bitsVal_congrAux
              (g := fun i : Fin 16 ↦ α107 ⟨91 + i.val, by omega⟩)
              fun i ↦ hlt107 ⟨91 + i.val, by omega⟩).trans hU16.symm
          have hu16_bits : (fun i ↦
            γ (u16W i)) = basisBits 16 ((s3U16Core hmPay80).extractIndex z80) :=
            ((basisBitsEquiv 16).apply_symm_apply (fun i ↦ γ (u16W i))).symm.trans
              (congrArg (basisBits 16) (Fin.ext hu16_val))
          have hlo2_eq : (γ (u16W 0)).val + 2 * (γ (u16W 1)).val =
            ((s3U16Core hmPay80).extractIndex z80).val % 4 := by
            have hsp := StepBBlock0.bitsVal_split_add 2 14 (fun i : Fin (2 + 14) ↦ γ (u16W i))
            change bitsVal (fun i : Fin 16 ↦ γ (u16W i)) =
              bitsVal (fun i : Fin 2 ↦ γ (u16W ⟨i.val, by omega⟩)) +
                2 ^ 2 * bitsVal (fun m : Fin 14 ↦ γ (u16W ⟨2 + m.val, by omega⟩)) at hsp
            have h2 : bitsVal (fun i : Fin 2 ↦
              γ (u16W ⟨i.val, by omega⟩)) = (γ (u16W 0)).val + 2 * (γ (u16W 1)).val := by
              simp [bitsVal, Fin.sum_univ_two]; ring
            have h0lt := ZMod.val_lt (γ (u16W 0)); have h1lt := ZMod.val_lt (γ (u16W 1))
            rw [hu16_val, h2] at hsp; omega
          have hbpar_val : (γ 90).val =
            (basisBits (momCoreWires 80) z80 (s3BParCore hmPay80)).val :=
            congrArg ZMod.val ((hlt107 ⟨90, by decide⟩).trans hBPar.symm)
          have hbpar_lt := ZMod.val_lt (basisBits (momCoreWires 80) z80 (s3BParCore hmPay80))
          have hq27_lt : Slot3Exact216Oracle80.s3NucleusQ27
              (basisBits 16 ((s3U16Core hmPay80).extractIndex z80)) < 27 :=
              Slot3Exact216Oracle80.s3NucleusQ27_lt _
          have hl_eq : 2 * (idx0.val % 128) + idx0.val / 128 = (s3NucleusIdx216 hmPay80 z80).val :=
            by
            dsimp [idx0, s3NucleusIdx216]; rw [hlo2_eq, hu16_bits, hbpar_val]; omega
          have hl_lt : 2 * (idx0.val % 128) + idx0.val / 128 < 216 := by
            rw [hl_eq]; exact (s3NucleusIdx216 hmPay80 z80).isLt
          dsimp only [fmkTbl]; unfold FastMidKick275Aux.fmkNegCoordTable
          dsimp only; rw [n1s_dif_pos hl_lt]
          have hfin : (⟨2 * (idx0.val % 128) + idx0.val / 128,
            hl_lt⟩ : Fin 216) = s3NucleusIdx216 hmPay80 z80 :=
            Fin.ext hl_eq
          rw [hfin]; exact Slot3Exact216Oracle80.toNat216_emod_two_pow42 _
        let kInt : ℤ := -∑ w : Fin 3,
          (twosMomentum ((momSysReg 80).extractIndex (s3CoreMapNorm1s t hmPay80 z80)) .projectile -
            twosMomentum ((momSysReg 80).extractIndex z80) .projectile) w *
            nearestProtonCoord 42 (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ))
              ((trunc36Cfg cfg).nuclei (s3NucleusIdx216 hmPay80 z80) w)
        have hsh_eq : (sh42 : ℤ) = kInt.emod (2 ^ 42 : ℤ) := by
          rw [show sh42 = (kInt.emod (2 ^ 42 : ℤ)).toNat by rw [hsh42_def, n1s_if_pos hz]]
          exact Slot3Exact216Oracle80.toNat216_emod_two_pow42 kInt
        let M42 : ℤ := 2 ^ 42
        let dTerm : Fin 3 → ℤ := fun w ↦ tc8 (pNew0 w) - tc8 (pOld0 w)
        let rTerm : Fin 3 → ℤ := fun w ↦
          -nearestProtonCoord 42 (SpecsAux.SpecMirror.cellVolume ^ (1 / 3 : ℝ))
          ((trunc36Cfg cfg).nuclei (s3NucleusIdx216 hmPay80 z80) w)
        have hd_eq : ∀ w : Fin 3, dTerm w =
            (twosMomentum ((momSysReg 80).extractIndex (s3CoreMapNorm1s t hmPay80 z80)) .projectile
              -
              twosMomentum ((momSysReg 80).extractIndex z80) .projectile) w := fun w ↦ by
          dsimp [dTerm, tc8, twosMomentum]; rw [hpNewEq w, hpOldEq w]
        have hSumEqK : ∑ w : Fin 3, dTerm w * rTerm w = kInt := by
          simp only [rTerm, kInt, hd_eq, mul_neg, Finset.sum_neg_distrib]
        have hSumMod : (∑ w : Fin 3, dTerm w * (fmkTbl w idx0 : ℤ)).emod M42 = kInt.emod M42 := by
          rw [← hSumEqK]; simp only [hIdxNuc, Fin.sum_univ_three]
          exact Slot3Exact216Oracle80.elec216_emod_sum3
            (dTerm 0) (rTerm 0) (dTerm 1) (rTerm 1) (dTerm 2) (rTerm 2) M42
        rw [hacc1, Int.ofNat_one, one_mul, hsh_eq]
        change ((bitsVal (fun m : Fin 42 ↦ α (Fin.natAdd 107 m)) : ℤ) +
            ∑ w : Fin 3, dTerm w * (fmkTbl w idx0 : ℤ)).emod M42 =
          ((bitsVal (fun m : Fin 42 ↦ α (Fin.natAdd 107 m)) : ℤ) + kInt.emod M42).emod M42
        rw [← Slot3Exact216Oracle80.elec216_emod_add_emod_right _ _ M42, hSumMod]
  change ((bitsVal (fun m : Fin 42 ↦ γ₂ ⟨107 + m.val, by omega⟩) : ℤ)).emod (2 ^ 42 : ℤ) =
    ((bitsVal (fun m : Fin 42 ↦ γ ⟨107 + m.val, by omega⟩) : ℤ) + ((γ accWAux).val : ℤ) *
      ∑ w : Fin 3,
        (tc8 (pNew0 w) - tc8 (pOld0 w)) * (fmkTbl w idx0 : ℤ)).emod (2 ^ 42 : ℤ) at hMidMod
  rw [hcOut_emod, hcOld_eq] at hMidMod
  have hcOut_eq : bitsVal (fun m : Fin 42 ↦ γ₂ ⟨107 + m.val, by omega⟩) = vNew42 :=
    Int.ofNat.inj (hMidMod.trans hShiftMod)
  let g : Fin 42 → ZMod 2 := fun m ↦ if vNew42.testBit m.val then 1 else 0
  have hg : bitsVal g = vNew42 :=
    bitsVal_eq_of_testBit g vNew42 (Nat.mod_lt _ (Nat.two_pow_pos 42)) (fun _ ↦ rfl)
  exact congrFun (bitsVal_injective (hcOut_eq.trans hg.symm)) j

theorem n1s_midKick36_cat42_eq (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α : BitAssignment 149) {γ : BitAssignment 437}
    (hInv : N1sRetainedInv γ)
    (hγ_lt : ∀ k : Fin 149, γ ⟨k.val, by omega⟩ = α k)
    (hAccBit : γ accWAux =
      if s3AcceptNorm1s t hmPay80
          ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 (fun i ↦
            α (Fin.castLE (by decide) i)))) = true
      then 1 else 0) :
    let γ411 : BitAssignment 411 := fun j ↦ γ ⟨j.val, by omega⟩
    (∀ q : Wire 411, ¬(107 ≤ q.val ∧ q.val < 149) →
      (progMidKick216_36_411 cfg).evalBits γ411 q = γ411 q) ∧
    (∀ j : Fin 42, (progMidKick216_36_411 cfg).evalBits γ411 ⟨107 + j.val, by omega⟩ =
      corePerm149_norm1s t cfg α (Fin.natAdd 107 j)) := by
  intro γ411
  have hmk : Slot3MidKick36_161w.mk36Clean161 γ411 := fun j hj ↦ by
    rcases hj with ⟨h1, h2⟩ | h3
    · exact hInv.hz233 ⟨j.val, by omega⟩ h1 h2
    · exact hInv.hcl ⟨j.val, by omega⟩ (by dsimp; omega)
  refine ⟨(progMidKick216_36_411_raw_spec cfg).2.2.1 γ411 hmk, fun j ↦ ?_⟩
  exact (progMidKick216_36_411_eq_437 cfg γ411 γ hmk hInv.hcl (fun _ _ ↦ rfl) (107 + j.val)
    (by omega)).trans (n1s_midKick36_cat42_aux t cfg α hInv hγ_lt hAccBit ((progMidKick216_437
    (trunc36Cfg cfg)).evalBits γ) ((progMidKick216_437_raw_spec (trunc36Cfg cfg)).2.2.2.2 γ
    hInv.hcl) j)

theorem n1s_negSignBit_eq (b : ZMod 2) (m : ℕ) :
    (b + if m = 0 then 0 else 1).val = if m = 0 then b.val else 1 - b.val := by
  by_cases hm : m = 0
  · rw [n1s_if_pos hm, n1s_if_pos hm, add_zero]
  · rw [n1s_if_neg hm, n1s_if_neg hm]
    rcases zmod2_eq_zero_or_one b with rfl | rfl <;> decide

theorem n1s_cSwapFlip_preserves_and_perm (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α : BitAssignment 149) {γ₂ γ_m : BitAssignment 437}
    (hγ_m_def : γ_m = s3Flip275.evalBits (cSwap24_275.evalBits γ₂))
    (hInv : N1sRetainedInv γ₂)
    (hlt107 : ∀ k : Fin 107, γ₂ ⟨k.val, by omega⟩ = α (Fin.castLE (by decide) k))
    (hcat : ∀ j : Fin 42, γ₂ (cat42W j) = corePerm149_norm1s t cfg α (Fin.natAdd 107 j))
    (hAccBit : γ₂ accWAux =
      if s3AcceptNorm1s t hmPay80
          ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 (fun i ↦
            α (Fin.castLE (by decide) i)))) = true
      then 1 else 0) :
    N1sRetainedInv γ_m ∧
    (∀ k : Fin 149, γ_m ⟨k.val, by omega⟩ = corePerm149_norm1s t cfg α k) ∧
    (∀ q : Wire 437, ¬(q.val < 24) → ¬(49 ≤ q.val ∧ q.val < 52) →
      ¬(150 ≤ q.val ∧ q.val < 174) → γ_m q = γ₂ q) ∧
    sTrueRawVal γ_m = sTrueRawVal γ₂ ∧
    ((∀ w : Fin 3, (getProj γ_m w).val ≠ 128) ↔
      (∀ w : Fin 3, (getProj γ₂ w).val ≠ 128)) := by
  obtain ⟨γ₃, hγ₃⟩ := n1s_step_wit (cSwap24_275.evalBits γ₂)
  have hγ_m : γ_m = s3Flip275.evalBits γ₃ :=
    hγ_m_def.trans (congrArg s3Flip275.evalBits hγ₃.symm)
  clear hγ_m_def
  let α107 : BitAssignment 107 := fun i ↦ α (Fin.castLE (by decide) i)
  change γ₂ accWAux =
    if s3AcceptNorm1s t hmPay80 ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107)) =
      true
    then 1 else 0 at hAccBit
  obtain ⟨z80, hz80⟩ := n1s_step_wit ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 α107))
  rw [← hz80] at hAccBit
  obtain ⟨_, _, _, hClSw, hEvSw⟩ := cSwap24_275_spec
  obtain ⟨hBFl, _, hEvFl⟩ := s3Flip275_spec
  have hcl₃ : cleanRem 437 (437 - 275) γ₃ := hγ₃.symm ▸ hClSw γ₂ hInv.hcl
  have hcl_m : cleanRem 437 (437 - 275) γ_m := hγ_m.symm ▸ hBFl.2.2.1 γ₃ hcl₃
  have hFlOut : ∀ q : Wire 437, ¬(49 ≤ q.val ∧ q.val < 52) → γ_m q = γ₃ q :=
    fun q hn ↦ (congrFun hγ_m q).trans
      (hBFl.2.2.2 γ₃ hcl₃ q (fun ⟨w, hw⟩ ↦ hn (by subst hw; dsimp [p57S3W]; omega)))
  have hSwOut : ∀ q : Wire 437, ¬(q.val < 24) → ¬(150 ≤ q.val ∧ q.val < 174) → γ₃ q = γ₂ q :=
    fun q h24 h150 ↦ (congrFun hγ₃ q).trans ((hEvSw γ₂ hInv.hcl).2.2 q h24 h150)
  have hUnchanged : ∀ q : Wire 437, ¬(q.val < 24) → ¬(49 ≤ q.val ∧ q.val < 52) →
      ¬(150 ≤ q.val ∧ q.val < 174) → γ_m q = γ₂ q :=
    fun q h24 h49 h150 ↦ (hFlOut q h49).trans (hSwOut q h24 h150)
  cases hz : s3AcceptNorm1s t hmPay80 z80 with
  | false =>
      have hSwRej : swapRejMap107_norm1s t α107 = α107 := by
        funext k
        unfold swapRejMap107_norm1s Slot3Norm1s36Physics80.swapRejMap107Norm1s
          Slot3Norm1s36Physics80.s3CoreMapNorm1s
        dsimp only [s3AcceptNorm1s] at hz ⊢
        rw [← hz80, n1s_if_neg (by rw [hz]; exact Bool.noConfusion), hz80,
          StepBBlock0.basisBits_symm,
          StepBBlock0.embedAlpha107_sel107_80]
      clear hz80
      have hne : ¬(s3AcceptNorm1s t hmPay80 z80 = true) := by rw [hz]; exact Bool.noConfusion
      have hacc0 : γ₂ accWAux = 0 := by rw [hAccBit, n1s_if_neg hne]
      have hacc_ne1 : γ₂ accWAux ≠ 1 := by rw [hacc0]; decide
      have hγ₃_eq : γ₃ = γ₂ := by
        rw [hγ₃]; funext q
        by_cases h24 : q.val < 24
        · let w : Fin 3 := ⟨q.val / 8, by omega⟩; let b : Fin 8 := ⟨q.val % 8, by omega⟩
          have hq : q = p57ProjW w b := Fin.ext (by dsimp [p57ProjW, w, b]; omega)
          rw [hq, (hEvSw γ₂ hInv.hcl).1 w b, n1s_if_neg hacc_ne1]
        · by_cases h150 : 150 ≤ q.val ∧ q.val < 174
          · let w : Fin 3 := ⟨(q.val - 150) / 8, by omega⟩;
            let b : Fin 8 :=
              ⟨(q.val - 150) % 8, by omega⟩
            have hq : q = pBufW w b := Fin.ext (by dsimp [pBufW, w, b]; omega)
            rw [hq, (hEvSw γ₂ hInv.hcl).2.1 w b, n1s_if_neg hacc_ne1]
          · exact (hEvSw γ₂ hInv.hcl).2.2 q h24 h150
      have hγ_m_eq : γ_m = γ₂ := by
        rw [hγ_m, hγ₃_eq]; funext q
        by_cases hs : ∃ w, q = p57S3W w
        · obtain ⟨w, rfl⟩ := hs; rw [hEvFl γ₂ hInv.hcl w, hacc0, zero_mul, add_zero]
        · exact hBFl.2.2.2 γ₂ hInv.hcl q hs
      rw [hγ_m_eq]
      refine ⟨hInv, fun k ↦ ?_, fun _ _ _ _ ↦ rfl, rfl, Iff.rfl⟩
      by_cases hk : k.val < 107
      · rw [n1s_corePerm149_lt107 t cfg α k hk,
        show (fun i ↦
          α (Fin.castLE (by decide) i)) = α107 from rfl,
            hSwRej]; exact hlt107 ⟨k.val, hk⟩
      · let j : Fin 42 := ⟨k.val - 107, by omega⟩
        have hk_eq : k = Fin.natAdd 107 j := Fin.ext (by dsimp [j, Fin.natAdd]; omega)
        have hw_eq : (⟨k.val, by omega⟩ : Wire 437) = cat42W j :=
          Fin.ext (by dsimp [cat42W, j]; omega)
        rw [hw_eq, hk_eq]; exact hcat j
  | true =>
      have hz' : s3AcceptNorm1s t hmPay80 ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107
        α107)) = true := by
        rw [← hz80]; exact hz
      obtain ⟨hSwProj, hSwS3, hSwRest⟩ :=
        Slot3Norm1s36Physics80.swapRejMap107Norm1s_of_accept t α107 hz'
      obtain ⟨hProj, _e1, hU22, hS3, _e2, _e3, _e4, _e5⟩ := embedAlpha107_fields α107
      clear _e1 _e2 _e3 _e4 _e5
      rw [← hz80] at hProj hU22 hS3; clear hz80 hz'
      have hacc1 : γ₂ accWAux = 1 := by rw [hAccBit, n1s_if_pos hz]
      have hU22Eq : getU22 γ₂ = (s3U22Core hmPay80).extractIndex z80 :=
        Fin.ext ((bitsVal_congrAux
          (g := fun b : Fin 22 ↦ α107 ⟨27 + b.val, by omega⟩)
          fun b ↦
            (congrArg γ₂ (Fin.ext rfl)).trans (hlt107 ⟨27 + b.val, by omega⟩)).trans hU22.symm)
      have hS3Eq : ∀ w : Fin 3,
        (γ₂ (p57S3W w)).val = signBit3 ((s3S3Core hmPay80).extractIndex z80) w :=
        fun w ↦
          (congrArg ZMod.val ((congrArg γ₂ (Fin.ext rfl)).trans (hlt107 ⟨49 + w.val, by
          omega⟩))).trans (hS3 w).symm
      have hpOldEq : ∀ w : Fin 3,
        getProj γ₂ w = projAxisField ((momSysReg 80).extractIndex z80) w :=
        fun w ↦ Fin.ext ((bitsVal_congrAux
          (g := fun b : Fin 8 ↦ α107 ⟨8 * w.val + b.val, by omega⟩)
          fun b ↦
            (congrArg γ₂ (Fin.ext rfl)).trans (hlt107 ⟨8 * w.val + b.val, by
            omega⟩)).trans (hProj w).symm)
      have hGrid : ∀ w : Fin 3, (projAxisField ((momSysReg 80).extractIndex z80) w).val ≠ 128 := by
        have hg : s3ProjGridBool ((momSysReg 80).extractIndex z80) = true := by
          unfold s3AcceptNorm1s Slot3Norm1s36Physics80.s3AcceptNorm1s at hz
          simp only [Bool.and_eq_true] at hz; exact hz.1.1.2
        exact (MomSlots35Slot3ProjNuclear.s3ProjGridBool_eq_true_iff _).mp hg
      have hvsh : validShellNu3 ((s3U22Core hmPay80).extractIndex z80) ((s3S3Core
        hmPay80).extractIndex z80) = true := by
        unfold s3AcceptNorm1s Slot3Norm1s36Physics80.s3AcceptNorm1s at hz
        simp only [Bool.and_eq_true] at hz; exact hz.1.2
      obtain ⟨u22, hu22_def⟩ := n1s_step_wit ((s3U22Core hmPay80).extractIndex z80)
      obtain ⟨s3, hs3_def⟩ := n1s_step_wit ((s3S3Core hmPay80).extractIndex z80)
      obtain ⟨pOld, hpOld_def⟩ := n1s_step_wit (fun w ↦
        projAxisField ((momSysReg 80).extractIndex z80) w)
      have hpOld_w : ∀ w, projAxisField ((momSysReg 80).extractIndex z80) w = pOld w :=
        fun w ↦ (congrFun hpOld_def w).symm
      rw [← hu22_def] at hU22Eq hvsh;
      rw [← hs3_def] at hS3Eq hvsh;
      simp only [hpOld_w] at hpOldEq
      simp only [hpOld_w] at hGrid
      clear hu22_def hs3_def hpOld_def hpOld_w hProj hU22 hS3 hAccBit hz z80
      have hProj_m : ∀ (w : Fin 3) (b : Fin 8), γ_m (p57ProjW w b) = γ₂ (pBufW w b) :=
        fun w b ↦ (hFlOut _ (by dsimp [p57ProjW]; omega)).trans
          ((congrFun hγ₃ _).trans (((hEvSw γ₂ hInv.hcl).1 w b).trans (n1s_if_pos hacc1)))
      have hPBuf_m : ∀ (w : Fin 3) (b : Fin 8), γ_m (pBufW w b) = γ₂ (p57ProjW w b) :=
        fun w b ↦ (hFlOut _ (by dsimp [pBufW]; omega)).trans
          ((congrFun hγ₃ _).trans (((hEvSw γ₂ hInv.hcl).2.1 w b).trans (n1s_if_pos hacc1)))
      have hS3_m : ∀ w : Fin 3,
        γ_m (p57S3W w) = γ₂ (p57S3W w) + (if shellMagCoord3 (getU22 γ₂) w = 0 then 0 else 1) :=
        fun w ↦ by
        have hacc3 : γ₃ accWAux = 1 := (hSwOut accWAux (by decide) (by decide)).trans hacc1
        have hs3_3 : γ₃ (p57S3W w) = γ₂ (p57S3W w) :=
          hSwOut (p57S3W w) (by dsimp [p57S3W]; omega) (by dsimp [p57S3W]; omega)
        have hm_3 : bitsVal (fun j ↦ γ₃ (p57MW w j)) = shellMagCoord3 (getU22 γ₂) w := by
          have hfn : (fun j ↦ γ₃ (p57MW w j)) = fun j ↦ γ₂ (p57MW w j) := funext fun j ↦
            hSwOut _ (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega)
          rw [hfn, hInv.m_val w]
        rw [congrFun hγ_m (p57S3W w), hEvFl γ₃ hcl₃ w, hs3_3, hacc3, one_mul, hm_3]
      have hu_eq_shared : (⟨bitsVal (fun i : Fin 22 ↦ α107 ⟨27 + i.val, by omega⟩),
          bitsVal_lt_two_pow (fun i : Fin 22 ↦
            α107 ⟨27 + i.val, by omega⟩)⟩ : Fin 4194304) = getU22 γ₂ :=
        Fin.ext (bitsVal_congrAux
          (f := fun i : Fin 22 ↦ α107 ⟨27 + i.val, by omega⟩)
          (g := fun i : Fin 22 ↦ γ₂ (u22WAux i))
          fun i ↦ (hlt107 ⟨27 + i.val, by omega⟩).symm.trans (congrArg γ₂ (Fin.ext rfl)))
      have hPerm149 : ∀ k : Fin 149, γ_m ⟨k.val, by omega⟩ = corePerm149_norm1s t cfg α k := fun k ↦
        by
        by_cases hk : k.val < 107
        · rw [n1s_corePerm149_lt107 t cfg α k hk,
            show (fun i ↦ α (Fin.castLE (by decide) i)) = α107 from rfl]
          dsimp only [swapRejMap107_norm1s]
          by_cases h24 : k.val < 24
          · let w : Fin 3 := ⟨k.val / 8, by omega⟩; let b : Fin 8 := ⟨k.val % 8, by omega⟩
            have hw437 : (⟨k.val, by omega⟩ : Wire 437) = p57ProjW w b :=
              Fin.ext (by dsimp [p57ProjW, w, b]; omega)
            have hk107 : (⟨k.val, hk⟩ : Fin 107) = ⟨8 * w.val + b.val, by omega⟩ :=
              Fin.ext (by dsimp [w, b]; omega)
            rw [hw437, hk107, hProj_m w b, hInv.hpbuf w b]
            have hsw := hSwProj w b; dsimp -failIfUnchanged only at hsw
            rw [hsw]
            have hp_eq : (⟨bitsVal (fun j : Fin 8 ↦ α107 ⟨8 * w.val + j.val, by omega⟩),
                bitsVal_lt_two_pow (fun j : Fin 8 ↦
                  α107 ⟨8 * w.val + j.val, by omega⟩)⟩ : Fin 256) = getProj γ₂ w :=
              Fin.ext (bitsVal_congrAux
                (f := fun j : Fin 8 ↦ α107 ⟨8 * w.val + j.val, by omega⟩)
                (g := fun j : Fin 8 ↦ γ₂ (p57ProjW w j))
                fun j ↦ (hlt107 ⟨8 * w.val + j.val, by omega⟩).symm.trans
                  (congrArg γ₂ (Fin.ext (by dsimp [p57ProjW]))))
            have hs_eq : (α107 ⟨49 + w.val, by omega⟩).val = (γ₂ (p57S3W w)).val :=
              congrArg ZMod.val (hlt107 ⟨49 + w.val, by omega⟩).symm
            rw [hp_eq, hu_eq_shared, hs_eq, StepBOuter.axisFastStep_eq_s3ProjStepHw
              (getProj γ₂ w) (shellMagCoord3 (getU22 γ₂) w) (γ₂ (p57S3W w)).val
              (by rw [hpOldEq w]; exact hGrid w) (s3ShellMagCoord3_lt_128 _ w)
              (by have := ZMod.val_lt (γ₂ (p57S3W w)); omega)]
          · by_cases h49 : 49 ≤ k.val ∧ k.val < 52
            · let w : Fin 3 := ⟨k.val - 49, by omega⟩
              have hw437 : (⟨k.val, by omega⟩ : Wire 437) = p57S3W w :=
                Fin.ext (by dsimp [p57S3W, w]; omega)
              have hk107 : (⟨k.val, hk⟩ : Fin 107) = ⟨49 + w.val, by omega⟩ :=
                Fin.ext (by dsimp [w]; omega)
              have hs3_k : γ₂ (p57S3W w) = α107 ⟨49 + w.val, by omega⟩ :=
                (congrArg γ₂ (Fin.ext rfl)).trans (hlt107 ⟨49 + w.val, by omega⟩)
              rw [hw437, hk107, hS3_m w, hSwS3 w, hs3_k, hu_eq_shared]
            · rw [hUnchanged ⟨k.val, by omega⟩ h24 h49 (by dsimp; omega),
                hSwRest ⟨k.val, hk⟩ h24 h49, hlt107 ⟨k.val, hk⟩]
        · let j : Fin 42 := ⟨k.val - 107, by omega⟩
          have hk_eq : k = Fin.natAdd 107 j := Fin.ext (by dsimp [j, Fin.natAdd]; omega)
          have hw_eq : (⟨k.val, by omega⟩ : Wire 437) = cat42W j :=
            Fin.ext (by dsimp [cat42W, j]; omega)
          rw [hw_eq, hk_eq,
            hUnchanged (cat42W j) (by dsimp [cat42W]; omega) (by dsimp [cat42W]; omega) (by
              dsimp
                [cat42W]; omega)]
          exact hcat j
      have hu22_m : getU22 γ_m = getU22 γ₂ :=
        getU22_congr fun i ↦
          hUnchanged _ (by dsimp [u22WAux]; omega) (by dsimp [u22WAux]; omega) (by
            dsimp [u22WAux];
              omega)
      have hS3_m_val : ∀ w : Fin 3, (γ_m (p57S3W w)).val = signBit3 (negSign3_22 u22 s3) w :=
        fun w ↦ by
        rw [MomSlots35Slot3ProjNuclear.signBit3_negSign3_22 u22 s3 w, hS3_m w, hU22Eq, ← hS3Eq w]
        exact n1s_negSignBit_eq _ _
      have hProj_m_val : ∀ w : Fin 3,
        getProj γ_m w = (s3ProjStepHw (pOld w) (shellMagCoord3 u22 w) (signBit3 s3 w)).1 := fun w ↦
        by
        apply Fin.ext
        have hfn : (fun b ↦ γ_m (p57ProjW w b)) = fun b ↦ γ₂ (pBufW w b) := funext (hProj_m w)
        change bitsVal (fun b ↦ γ_m (p57ProjW w b)) = _
        rw [hfn, bitsVal_eq_of_testBit _ _ (StepBOuter.axisFastVal_lt _ _ _) (hInv.hpbuf w),
          hpOldEq w, hU22Eq, hS3Eq w]
        exact StepBOuter.axisFastStep_eq_s3ProjStepHw _ _ _ (hGrid w)
          (s3ShellMagCoord3_lt_128 _ w)
          (MomSlots35Slot3ProjNuclear.s3SignBit3_le_one _ w)
      have hInvAx := fun w ↦ MomSlots35Slot3ProjNuclear.s3AxisStep_involutive (hGrid w) hvsh w
      have hGrid_m : ∀ w : Fin 3, (getProj γ_m w).val ≠ 128 := fun w ↦
        by rw [hProj_m_val w]; exact (hInvAx w).1
      have hGrid₂ : ∀ w : Fin 3, (getProj γ₂ w).val ≠ 128 := fun w ↦
        by rw [hpOldEq w]; exact hGrid w
      have hsTrue_m_eq : sTrueRawVal γ_m = sTrueRawVal γ₂ := by
        have hm_m : ∀ w : Fin 3, bitsVal (fun b ↦ γ_m (p57MW w b)) = shellMagCoord3 u22 w := fun w ↦
          by
          have hfn : (fun b ↦ γ_m (p57MW w b)) = fun b ↦ γ₂ (p57MW w b) := funext fun b ↦
            hUnchanged _ (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega) (by
              dsimp [p57MW];
                omega)
          rw [hfn, hInv.m_val w, hU22Eq]
        rw [Prod57BoothHoist.sTrueRawVal_eq_of_ne_128 γ_m (getProj γ_m) (fun _ ↦ rfl) hGrid_m,
          Prod57BoothHoist.sTrueRawVal_eq_of_ne_128 γ₂ (getProj γ₂) (fun _ ↦ rfl) hGrid₂]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        dsimp only;
        rw [hProj_m_val w, hm_m w, hS3_m_val w, hpOldEq w, hInv.m_val w, hU22Eq,
          hS3Eq w, (hInvAx w).2.2]
      have hvs_val_m : validStaticVal216 γ_m = validStaticVal216 γ₂ := by
        unfold validStaticVal216
        have hc_fn : (fun b ↦ γ_m (coinW b)) = fun b ↦ γ₂ (coinW b) := funext fun b ↦
          hUnchanged _ (by dsimp [coinW]; omega) (by dsimp [coinW]; omega) (by dsimp [coinW]; omega)
        have hs3_cond : (∀ w : Fin 3,
          ¬(shellMagCoord3 (getU22 γ₂) w = 0 ∧ (γ_m (p57S3W w)).val = 1)) ↔
            (∀ w : Fin 3, ¬(shellMagCoord3 (getU22 γ₂) w = 0 ∧ (γ₂ (p57S3W w)).val = 1)) :=
          forall_congr' fun w ↦ not_congr (and_congr_right fun hm0 ↦
            by rw [hS3_m w, n1s_if_pos hm0, add_zero])
        simp only [hc_fn, hu22_m, hs3_cond]
      refine ⟨?_, hPerm149, hUnchanged, hsTrue_m_eq, ⟨fun _ ↦ hGrid₂, fun _ ↦ hGrid_m⟩⟩
      exact
        { hcl := hcl_m
          hcoin := by
            have hc_fn : (fun b ↦ γ_m (coinW b)) = fun b ↦ γ₂ (coinW b) := funext fun b ↦
              hUnchanged _ (by dsimp [coinW]; omega) (by dsimp [coinW]; omega) (by
                dsimp [coinW];
                  omega)
            rw [hUnchanged coinOkW (by decide) (by decide) (by decide), hc_fn]; exact hInv.hcoin
          hmu := fun j ↦ by
            rw [hUnchanged (muW j) (by dsimp [muW]; omega) (by dsimp [muW]; omega) (by
              dsimp [muW];
                omega), hu22_m]
            exact hInv.hmu j
          hm := fun w b ↦ by
            rw [hUnchanged (p57MW w b) (by dsimp [p57MW]; omega) (by dsimp [p57MW]; omega) (by
              dsimp
                [p57MW]; omega), hu22_m]
            exact hInv.hm w b
          hvs := by
            rw [hUnchanged validStaticW (by decide) (by decide) (by decide),
            hvs_val_m]; exact hInv.hvs
          hstrue := by
            have hst : (fun j ↦ γ_m (sTrue18WDefault j)) = fun j ↦ γ₂ (sTrue18WDefault j) :=
              funext fun j ↦ by
              have hb := Slot3Exact216Oracle80.sTrue18WDefault216_bounds j
              exact hUnchanged _ (by omega) (by omega) (by omega)
            rw [hst, hsTrue_m_eq]; exact hInv.hstrue
          hpbuf := fun w b ↦ by
            rw [hPBuf_m w b, hu22_m, hU22Eq, hProj_m_val w, hS3_m_val w,
              StepBOuter.axisFastStep_eq_s3ProjStepHw _ _ _ (hInvAx w).1
                (s3ShellMagCoord3_lt_128 _ w)
                (MomSlots35Slot3ProjNuclear.s3SignBit3_le_one _ w),
              (hInvAx w).2.1, ← hpOldEq w]
            let g8 : Fin 8 → ZMod 2 := fun j ↦ if (getProj γ₂ w).val.testBit j.val then 1 else 0
            have hg8 : bitsVal g8 = bitsVal (fun j ↦ γ₂ (p57ProjW w j)) :=
              bitsVal_eq_of_testBit g8 (getProj γ₂ w).val (getProj γ₂ w).isLt (fun _ ↦ rfl)
            exact congrFun (bitsVal_injective hg8.symm) b
          hz233 := fun w h1 h2 ↦
            (hUnchanged w (by omega) (by omega) (by omega)).trans (hInv.hz233 w h1 h2) }

theorem n1s_revTail_eq_st0 (β_perm : BitAssignment 149) {δ₅ δ₆ : BitAssignment 437}
    (hδ₆_def : δ₆ = sTrue18RevPBuf275.evalBits δ₅)
    (hInv5 : N1sRetainedInv δ₅)
    (hAct5 : ∀ k : Fin 149, δ₅ ⟨k.val, by omega⟩ = β_perm k)
    (hAcc5 : δ₅ accWAux = 0)
    (hOut5 : ∀ w : Wire 437, 201 ≤ w.val → w.val < 258 → δ₅ w = 0) :
    cleanRem 437 (437 - 275) δ₆ ∧
    (∀ w : Wire 437, isBadA w = true → δ₆ w = 0) ∧
    InvRevTailPruned216 δ₆ ∧
    st0 β_perm = revTail216_br31_275.evalBits δ₆ := by
  obtain ⟨hcl6_raw, hnon6_raw, hzero6_raw⟩ := sTrue18RevPBuf275_spec.2.2.2 δ₅ hInv5.hcl
  have hcl6 : cleanRem 437 (437 - 275) δ₆ := hδ₆_def.symm ▸ hcl6_raw
  have hst5_pbuf : bitsVal (fun j ↦ δ₅ (sTrue18WDefault j)) = sTrueRawValPBuf δ₅ :=
    hInv5.hstrue.trans (elecsTrueRawValPBuf_eq δ₅ hInv5.m_val (fun w ↦
      hInv5.hpbuf w ⟨7, by decide⟩)).symm
  have hz6_st : ∀ j : Fin 18, δ₆ (sTrue18WDefault j) = 0 :=
    fun j ↦ (congrFun hδ₆_def _).trans (hzero6_raw hst5_pbuf j)
  have hp6 : ∀ q : Wire 437,
    ¬((199 ≤ q.val ∧ q.val < 201) ∨ (259 ≤ q.val ∧ q.val < 275)) → δ₆ q = δ₅ q :=
    fun q hq ↦ (congrFun hδ₆_def q).trans (hnon6_raw q (fun j hj ↦ by
      subst hj; exact hq (Slot3Exact216Oracle80.sTrue18WDefault216_bounds j)))
  clear hδ₆_def hcl6_raw hnon6_raw hzero6_raw
  have hbadA6 : ∀ w : Wire 437, isBadA w = true → δ₆ w = 0 := fun w hw ↦ by
    have hb : 201 ≤ w.val ∧ w.val < 227 := of_decide_eq_true hw
    exact (hp6 w (by omega)).trans (hOut5 w hb.1 (by omega))
  have hInvTail5 : InvRevTailPruned216 δ₅ := by
    refine ⟨fun w b ↦ ?_, ⟨hInv5.mu_val, hInv5.m_val, hInv5.hcoin, hInv5.hvs⟩,
      ⟨hInv5.mu_val, hInv5.hm⟩, ⟨hInv5.hcoin, fun j ↦ ?_⟩⟩
    · rw [hInv5.m_val w]; exact hInv5.hpbuf w b
    · rw [top7_eq_shellMu3_216 δ₅]; exact hInv5.hmu j
  have hInvTail6 : InvRevTailPruned216 δ₆ :=
    (Slot3Outer2344AndRelayWide.Slot3RevUncompDynPruned.InvRevTailPruned216_congr
      (fun w b ↦ hp6 _ (by dsimp [p57ProjW]; omega))
      (fun w b ↦ hp6 _ (by dsimp [p57MW]; omega))
      (fun w ↦ hp6 _ (by dsimp [p57S3W]; omega))
      (fun w b ↦ hp6 _ (by dsimp [pBufW]; omega))
      (fun j ↦ hp6 _ (by dsimp [muW]; omega))
      (fun i ↦ hp6 _ (by dsimp [u22WAux]; omega))
      (fun b ↦ hp6 _ (by dsimp [coinW]; omega))
      (fun i ↦ hp6 _ (by dsimp [top7W]; omega))
      (hp6 _ (by decide)) (hp6 _ (by decide))).mpr hInvTail5
  obtain ⟨γ_ref, hγ_ref⟩ := n1s_step_wit (fwdPrep216_275.evalBits (padZeroBits (mClean :=
    288) β_perm))
  have hActR : ∀ k : Fin 149, γ_ref ⟨k.val, by omega⟩ = β_perm k :=
    fun k ↦ (congrFun hγ_ref ⟨k.val, by omega⟩).trans ((fwdPrep216_275_spec.2.2.2 β_perm).1 k)
  have hInvR : RetainedInv216 γ_ref := hγ_ref.symm ▸ (fwdPrep216_275_spec.2.2.2 β_perm).2
  clear hγ_ref
  obtain ⟨ξ₁, hξ₁⟩ := n1s_step_wit (StepBOuter.accXor275.evalBits γ_ref)
  obtain ⟨ξ₂, hξ₂⟩ := n1s_step_wit (Prod57BoothHoist.boothSub57_275.evalBits ξ₁)
  obtain ⟨ξ₃, hξ₃⟩ := n1s_step_wit (sTrue18RevPBuf275.evalBits ξ₂)
  obtain ⟨hB7, _, hE7⟩ := StepBOuter.accXor275_spec
  obtain ⟨_, _, _, h6R⟩ := Prod57BoothHoist.boothSub57_275_spec
  obtain ⟨_, _, _, h5R⟩ := sTrue18RevPBuf275_spec
  have hcl_ξ₁ : cleanRem 437 (437 - 275) ξ₁ := hξ₁.symm ▸ hB7.2.2.1 γ_ref hInvR.hcl
  have hcl_ξ₂ : cleanRem 437 (437 - 275) ξ₂ := hξ₂.symm ▸ (h6R ξ₁ hcl_ξ₁).1
  have hcl_ξ₃ : cleanRem 437 (437 - 275) ξ₃ := hξ₃.symm ▸ (h5R ξ₂ hcl_ξ₂).1
  have hpR1 : ∀ q : Wire 437, q.val ≠ 149 → ξ₁ q = γ_ref q :=
    fun q hq ↦ (congrFun hξ₁ q).trans (hB7.2.2.2 γ_ref hInvR.hcl q (fun h ↦ hq (by subst h; rfl)))
  have hpR2 : ∀ q : Wire 437, ¬(201 ≤ q.val ∧ q.val < 258) → ξ₂ q = ξ₁ q :=
    fun q hq ↦ (congrFun hξ₂ q).trans
      ((h6R ξ₁ hcl_ξ₁).2.1 q (fun m hm ↦
        by subst hm; exact hq ⟨by dsimp [p57OutW]; omega, by dsimp [p57OutW]; omega⟩))
  have hpR3 : ∀ q : Wire 437,
    ¬((199 ≤ q.val ∧ q.val < 201) ∨ (259 ≤ q.val ∧ q.val < 275)) → ξ₃ q = ξ₂ q :=
    fun q hq ↦ (congrFun hξ₃ q).trans
      ((h5R ξ₂ hcl_ξ₂).2.1 q (fun j hj ↦
        by subst hj; exact hq (Slot3Exact216Oracle80.sTrue18WDefault216_bounds j)))
  have hlt149_eq : ∀ q : Wire 437, (hq : q.val < 149) → δ₅ q = γ_ref q :=
    fun q hq ↦ (hAct5 ⟨q.val, hq⟩).trans (hActR ⟨q.val, hq⟩).symm
  have hu22_eq : getU22 δ₅ = getU22 γ_ref :=
    getU22_congr fun i ↦ hlt149_eq _ (by dsimp [u22WAux]; omega)
  have hpr_eq : ∀ w, getProj δ₅ w = getProj γ_ref w := fun w ↦
    Fin.ext (bitsVal_congrAux
      (g := fun b : Fin 8 ↦ γ_ref (p57ProjW w b))
      fun b ↦ hlt149_eq _ (by dsimp [p57ProjW]; omega))
  have hc_fn : (fun b ↦ δ₅ (coinW b)) = fun b ↦ γ_ref (coinW b) :=
    funext fun b ↦ hlt149_eq _ (by dsimp [coinW]; omega)
  have h6eq (q : Wire 437) (hr : (q.val < 199 ∨ q.val = 258) ∧ q.val ≠ 149)
      (hv : δ₅ q = γ_ref q) : δ₆ q = ξ₃ q :=
    (hp6 q (by omega)).trans (hv.trans
      (((hpR3 q (by omega)).trans ((hpR2 q (by omega)).trans (hpR1 q hr.2))).symm))
  have hδ₆_eq : δ₆ = ξ₃ := by
    funext q
    by_cases h149 : q.val < 149
    · exact h6eq q ⟨Or.inl (by omega), by omega⟩ (hlt149_eq q h149)
    by_cases heq149 : q.val = 149
    · have hq : q = accWAux := Fin.ext heq149
      subst hq
      have hξ₁_0 : ξ₁ accWAux = 0 := by
        rw [congrFun hξ₁ accWAux,
          hE7 γ_ref hInvR.hcl (shellMu3 (getU22 γ_ref)) (shellMu3_lt_seven _) hInvR.mu_val,
          hInvR.hacc, hInvR.hvs, hInvR.hprod]
        exact Slot3Exact216Oracle80.zMod2_216_add_self _
      exact (hp6 accWAux (by decide)).trans (hAcc5.trans
        (((hpR3 accWAux (by decide)).trans (hpR2 accWAux (by decide))).trans hξ₁_0).symm)
    by_cases h150 : 150 ≤ q.val ∧ q.val < 174
    · let w : Fin 3 := ⟨(q.val - 150) / 8, by omega⟩
      let b : Fin 8 := ⟨(q.val - 150) % 8, by omega⟩
      have hq : q = pBufW w b := Fin.ext (by dsimp [pBufW, w, b]; omega)
      refine h6eq q ⟨Or.inl (by omega), heq149⟩ ?_
      rw [hq, hInv5.hpbuf w b, hInvR.hpbuf w b, hpr_eq w, hu22_eq,
        hlt149_eq (p57S3W w) (by dsimp [p57S3W]; omega)]
    by_cases h174 : 174 ≤ q.val ∧ q.val < 177
    · let j : Fin 3 := ⟨q.val - 174, by omega⟩
      have hq : q = muW j := Fin.ext (by dsimp [muW, j]; omega)
      refine h6eq q ⟨Or.inl (by omega), heq149⟩ ?_
      rw [hq, hInv5.hmu j, hInvR.hmu j, hu22_eq]
    by_cases h177 : 177 ≤ q.val ∧ q.val < 198
    · let w : Fin 3 := ⟨(q.val - 177) / 7, by omega⟩
      let b : Fin 7 := ⟨(q.val - 177) % 7, by omega⟩
      have hq : q = p57MW w b := Fin.ext (by dsimp [p57MW, w, b]; omega)
      refine h6eq q ⟨Or.inl (by omega), heq149⟩ ?_
      rw [hq, hInv5.hm w b, hInvR.hm w b, hu22_eq]
    by_cases h198 : q.val = 198
    · refine h6eq q ⟨Or.inl (by omega), heq149⟩ ?_
      have hq : q = coinOkW := Fin.ext h198
      rw [hq, hInv5.hcoin, hInvR.hcoin, hc_fn]
    by_cases h201 : 201 ≤ q.val ∧ q.val < 258
    · let m : Fin 57 := ⟨q.val - 201, by omega⟩
      have hq : q = p57OutW m := Fin.ext (by dsimp [p57OutW, m]; omega)
      have hout₁ : bitsVal (fun m ↦ ξ₁ (p57OutW m)) =
          bitsVal (fun j ↦ ξ₁ (sTrue18WDefault j)) * (bitsVal (fun k ↦ ξ₁ (p57U38W k)) + 1) +
            Prod57BoothHoist.boothConst57 := by
        have ho : (fun m ↦ ξ₁ (p57OutW m)) = fun m ↦ γ_ref (p57OutW m) :=
          funext fun m ↦ hpR1 _ (by dsimp [p57OutW]; omega)
        have hs : (fun j ↦ ξ₁ (sTrue18WDefault j)) = fun j ↦ γ_ref (sTrue18WDefault j) :=
          funext fun j ↦ by
            have := Slot3Exact216Oracle80.sTrue18WDefault216_bounds j
            exact hpR1 _ (by omega)
        have hu : (fun k ↦ ξ₁ (p57U38W k)) = fun k ↦ γ_ref (p57U38W k) :=
          funext fun k ↦ by
            have := Slot3Exact216Oracle80.p57U38W216_lt107 k
            exact hpR1 _ (by omega)
        rw [ho, hs, hu, hInvR.hprod, hInvR.hstrue]
        rfl
      rw [hq, hp6 _ (by dsimp [p57OutW]; omega),
        hOut5 _ (by dsimp [p57OutW]; omega) (by dsimp [p57OutW]; omega),
        hpR3 _ (by dsimp [p57OutW]; omega), congrFun hξ₂ _, (h6R ξ₁ hcl_ξ₁).2.2 hout₁ m]
    by_cases h258 : q.val = 258
    · refine h6eq q ⟨Or.inr h258, heq149⟩ ?_
      have hq : q = validStaticW := Fin.ext h258
      have hs3_fn : ∀ w, δ₅ (p57S3W w) = γ_ref (p57S3W w) :=
        fun w ↦ hlt149_eq _ (by dsimp [p57S3W]; omega)
      rw [hq, hInv5.hvs, hInvR.hvs]
      unfold validStaticVal216
      simp only [hc_fn, hu22_eq, hs3_fn]
    by_cases h275 : 275 ≤ q.val
    · exact (hcl6 q h275).trans (hcl_ξ₃ q h275).symm
    · have hs_mem : ∃ j : Fin 18, q = sTrue18WDefault j := by
        by_cases h199 : 199 ≤ q.val ∧ q.val < 201
        · refine ⟨⟨q.val - 199 + 16, by omega⟩, Fin.ext ?_⟩
          dsimp [sTrue18WDefault]; omega
        · refine ⟨⟨q.val - 259, by omega⟩, Fin.ext ?_⟩
          dsimp only [sTrue18WDefault]; rw [n1s_dif_pos (by omega)]; dsimp only; omega
      obtain ⟨j, rfl⟩ := hs_mem
      have hst_ξ₂ : bitsVal (fun j ↦ ξ₂ (sTrue18WDefault j)) = sTrueRawValPBuf ξ₂ := by
        have hs : (fun j ↦ ξ₂ (sTrue18WDefault j)) = fun j ↦ γ_ref (sTrue18WDefault j) :=
          funext fun i ↦ by
          have := Slot3Exact216Oracle80.sTrue18WDefault216_bounds i
          exact (hpR2 _ (by omega)).trans (hpR1 _ (by omega))
        have hpb : sTrueRawValPBuf ξ₂ = sTrueRawValPBuf γ_ref :=
          StepBOuter.sTrueRawValPBuf_congr
            (fun w ↦
              (hpR2 _ (by dsimp [p57ProjW]; omega)).trans (hpR1 _ (by dsimp [p57ProjW]; omega)))
            (fun w ↦ (hpR2 _ (by dsimp [Prod57BoothHoist.p57PBufW]; omega)).trans
              (hpR1 _ (by dsimp [Prod57BoothHoist.p57PBufW]; omega)))
            (fun w ↦ (hpR2 _ (by dsimp [p57S3W]; omega)).trans (hpR1 _ (by dsimp [p57S3W]; omega)))
            (fun w b ↦ (hpR2 _ (by dsimp [p57MW]; omega)).trans (hpR1 _ (by dsimp [p57MW]; omega)))
        rw [hs, hpb, hInvR.hstrue]
        exact (elecsTrueRawValPBuf_eq γ_ref hInvR.m_val (fun w ↦ hInvR.hpbuf w ⟨7, by decide⟩)).symm
      exact (hz6_st j).trans ((congrFun hξ₃ _).trans ((h5R ξ₂ hcl_ξ₂).2.2 hst_ξ₂ j)).symm
  refine ⟨hcl6, hbadA6, hInvTail6, ?_⟩
  rw [hδ₆_eq]
  have hRevSpec : revUncomp216_275.evalBits γ_ref = st0 β_perm :=
    (revUncomp216_275_spec.2.2.2 γ_ref hInvR).trans
      (congrArg (padZeroBits (mClean := 288)) (funext hActR))
  have hξ₃_exp : ξ₃ = sTrue18RevPBuf275.evalBits
      (Prod57BoothHoist.boothSub57_275.evalBits
        (StepBOuter.accXor275.evalBits γ_ref)) :=
    hξ₃.trans (congrArg sTrue18RevPBuf275.evalBits hξ₂ |>.trans
      (congrArg (fun x ↦ sTrue18RevPBuf275.evalBits
        (Prod57BoothHoist.boothSub57_275.evalBits x)) hξ₁))
  have hTailEq : revTail216_br31_275.evalBits ξ₃ =
      StepBOuter.coinMuXor275.evalBits
        (StepBOuter.magUnpack275.evalBits
          (Slot3Exact216Oracle80.validStatic216_275.evalBits
            (StepBOuter.axisStep3_275.evalBits ξ₃))) := by
    have hseq : revTail216_br31_275.evalBits ξ₃ =
        StepBOuter.coinMuXor275.evalBits
          (StepBOuter.magUnpack275.evalBits
            (Slot3Exact216Oracle80.validStatic216_275.evalBits
              (axisStep3_fast_275.evalBits ξ₃))) := by
      dsimp only [revTail216_br31_275]
      repeat rw [tempPhaseProg216_seq_evalBits]
    exact hseq.trans (congrArg StepBOuter.coinMuXor275.evalBits
      (congrArg StepBOuter.magUnpack275.evalBits (congrArg
      Slot3Exact216Oracle80.validStatic216_275.evalBits
      (axisStep3_fast_275_eq_orig ξ₃ hcl_ξ₃))))
  exact hRevSpec.symm.trans
    ((Slot3Exact216Oracle80.revUncomp216_275_evalBits γ_ref).trans
    ((congrArg (fun x ↦ StepBOuter.coinMuXor275.evalBits
    (StepBOuter.magUnpack275.evalBits
    (Slot3Exact216Oracle80.validStatic216_275.evalBits
    (StepBOuter.axisStep3_275.evalBits x)))) hξ₃_exp.symm).trans
    hTailEq.symm))

/-- Lift a `411`-wire `TempPhaseProg.evalBits` action onto `BitAssignment 437` (`0` on
  `[411..437)`). -/
def n1sLiftEval411 (p : TempPhaseProg 411) (γ : BitAssignment 437) : BitAssignment 437 :=
  fun w ↦ if hw : w.val < 411 then p.evalBits (fun j : Wire 411 ↦
    γ ⟨j.val, by omega⟩) ⟨w.val, hw⟩ else 0

/-- Stage-2 (`n1sFwdStatic411 t`) output state on `BitAssignment 437`. -/
def n1sSt2 (t : Norm1sTier) (α : BitAssignment 149) : BitAssignment 437 :=
  n1sLiftEval411 (n1sFwdStatic411 t) (st1 α)

/-- Stage-4 (`progMidKick216_36_411 cfg`) output state on `BitAssignment 437`. -/
noncomputable def n1sSt3 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) (α :
    BitAssignment 149) :
    BitAssignment 437 :=
  n1sLiftEval411 (progMidKick216_36_411 cfg) (n1sSt2 t α)

/-- Stage-5 (`cSwap24_275 + s3Flip275`) output state on `BitAssignment 437`. -/
noncomputable def n1sSt4 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) (α :
    BitAssignment 149) :
    BitAssignment 437 :=
  s3Flip275.evalBits (cSwap24_275.evalBits (n1sSt3 t cfg α))

/-- Stage-6 (`n1sRevStatic411 t`) output state on `BitAssignment 437`. -/
noncomputable def n1sSt5 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) (α :
    BitAssignment 149) :
    BitAssignment 437 :=
  n1sLiftEval411 (n1sRevStatic411 t) (n1sSt4 t cfg α)

/-- Stage-7 (`sTrue18RevPBuf275`) output state on `BitAssignment 437`. -/
noncomputable def n1sSt6 (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration)
    (α : BitAssignment 149) : BitAssignment 437 := sTrue18RevPBuf275.evalBits (n1sSt5 t cfg α)

/-- `411`-wire prefix slice of `st1 α`. -/
def n1sSt1_411 (α : BitAssignment 149) : BitAssignment 411 :=
  fun j ↦ st1 α ⟨j.val, by omega⟩

private theorem n1s_lift411_retained (p : TempPhaseProg 411) {γ : BitAssignment 437}
    (hInv : N1sRetainedInv γ)
    (hcl_ev : cleanRem 411 (411 - 275) (p.evalBits fun j ↦ γ ⟨j.val, by omega⟩))
    (hnon_ev : ∀ q : Wire 411, q ≠ n1sAccFlagW411 → (∀ k : Fin 32, q ≠ n1sOut32W411 k) →
      p.evalBits (fun j ↦ γ ⟨j.val, by omega⟩) q = γ ⟨q.val, by omega⟩) :
    N1sRetainedInv (n1sLiftEval411 p γ) ∧
    (∀ q : Wire 437, q.val ≠ 149 → ¬(201 ≤ q.val ∧ q.val < 233) →
      n1sLiftEval411 p γ q = γ q) := by
  have hcl' : cleanRem 437 (437 - 275) (n1sLiftEval411 p γ) := fun w hw ↦ by
    dsimp only [n1sLiftEval411]
    by_cases h411 : w.val < 411
    · rw [n1s_dif_pos h411]
      exact hcl_ev ⟨w.val, h411⟩ hw
    · exact n1s_dif_neg h411
  have hnon' : ∀ q : Wire 437, q.val ≠ 149 → ¬(201 ≤ q.val ∧ q.val < 233) →
      n1sLiftEval411 p γ q = γ q := fun q h149 h201 ↦ by
    dsimp only [n1sLiftEval411]
    by_cases h411 : q.val < 411
    · rw [n1s_dif_pos h411]
      exact hnon_ev ⟨q.val, h411⟩ (fun h ↦ h149 (congrArg Fin.val h))
        (fun k hk ↦ h201 (by have hv := congrArg Fin.val hk; dsimp [n1sOut32W411] at hv; omega))
    · rw [n1s_dif_neg h411]
      exact (hInv.hcl q (by omega)).symm
  exact ⟨N1sRetainedInv.of_agree_core hInv hcl'
    (fun w h1 h2 ↦ (hnon' w (by omega) (by omega)).trans (hInv.hz233 w h1 h2))
    (fun q _ _ _ ↦ hnon' q (by omega) (by omega)), hnon'⟩

private theorem n1s_valid411_of_retained {γ : BitAssignment 437} (hInv : N1sRetainedInv γ) :
    let β : BitAssignment 411 := fun j ↦ γ ⟨j.val, by omega⟩
    bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)) = sTrueRawVal γ ∧
    bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) = shellMu3 (getU22 γ) ∧
    (β n1sValidStaticW411 = 1 →
      bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) < 7 ∧
      2 * bitsVal (fun i : Fin 3 ↦ β (n1sMuW411 i)) ≤
        clz18Log2 (bitsVal (fun i : Fin 18 ↦ β (n1sSTrue18W411 i)))) := by
  have hs : bitsVal (fun i : Fin 18 ↦ γ ⟨(n1sSTrue18W411 i).val, by omega⟩) = sTrueRawVal γ :=
    (congrArg bitsVal (funext fun i ↦
      congrArg γ (Fin.ext (by fin_cases i <;> rfl)))).trans hInv.hstrue
  have hmu : bitsVal (fun i : Fin 3 ↦ γ ⟨(n1sMuW411 i).val, by omega⟩) =
      shellMu3 (getU22 γ) :=
    (congrArg bitsVal (funext fun i ↦
      congrArg γ (Fin.ext (by fin_cases i <;> rfl)))).trans hInv.mu_val
  refine ⟨hs, hmu, fun hvs ↦ ?_⟩
  rw [hmu, hs]
  have hvs' : validStaticVal216 γ = 1 :=
    (hInv.hvs.symm.trans (congrArg γ (Fin.ext rfl)).symm).trans hvs
  exact ⟨shellMu3_lt_seven _, two_mul_mu_le_clz18Log2 hvs' hInv.m_val⟩

theorem n1s_st2_props (t : Norm1sTier) (α : BitAssignment 149) :
    N1sRetainedInv (n1sSt2 t α) ∧
    (∀ k : Fin 149, n1sSt2 t α ⟨k.val, by omega⟩ = α k) ∧
    (∀ q : Wire 437, q.val ≠ 149 → ¬(201 ≤ q.val ∧ q.val < 233) → n1sSt2 t α q = st1 α q) ∧
    bitsVal (fun k : Fin 32 ↦ n1sSt2 t α ⟨201 + k.val, by omega⟩) =
      norm1sHwProd t.kBits t.dCut
        (norm1sMant18 (bitsVal (fun i : Fin 18 ↦ n1sSt1_411 α (n1sSTrue18W411 i))))
        (bitsVal (fun k : Fin 38 ↦ n1sSt1_411 α (n1sU38W411 k)) / 2 ^ (38 - t.kBits)) ∧
    n1sSt2 t α accWAux = n1sAccTarget411 t (n1sSt1_411 α) ∧
    n1sSt2 t α accWAux =
      if s3AcceptNorm1s t hmPay80
          ((basisBitsEquiv (momCoreWires 80)).symm (embedAlpha107 (fun i ↦
            α (Fin.castLE (by decide) i)))) = true
      then 1 else 0 := by
  let β₁ : BitAssignment 411 := n1sSt1_411 α
  obtain ⟨hInv1, hAct1, hAcc1, hOut1⟩ := n1s_st1_props α
  obtain ⟨_, hcl_ev, hnon_ev, hval_ev⟩ :=
    (n1s_fwdStatic411_spec t).2 β₁ (fun j hj ↦ hInv1.hcl ⟨j.val, by omega⟩ hj)
  obtain ⟨hInv2, hnon2⟩ := n1s_lift411_retained (n1sFwdStatic411 t) hInv1 hcl_ev hnon_ev
  obtain ⟨hs_val', hmu_val', hvalid⟩ := n1s_valid411_of_retained hInv1
  have hs_val : bitsVal (fun i : Fin 18 ↦ β₁ (n1sSTrue18W411 i)) = sTrueRawVal (st1 α) := hs_val'
  have hmu_val : bitsVal (fun i : Fin 3 ↦ β₁ (n1sMuW411 i)) = shellMu3 (getU22 (st1 α)) :=
    hmu_val'
  obtain ⟨hout_ev, hacc_ev⟩ := hval_ev hOut1 hAcc1 hvalid
  have hout2 : bitsVal (fun k : Fin 32 ↦ n1sSt2 t α ⟨201 + k.val, by omega⟩) =
      bitsVal (fun k : Fin 32 ↦ (n1sFwdStatic411 t).evalBits β₁ (n1sOut32W411 k)) :=
    congrArg bitsVal (funext fun k ↦ by
      dsimp only [n1sSt2, n1sLiftEval411, n1sOut32W411, β₁]; rw [n1s_dif_pos (by omega)]; rfl)
  have hacc2 : n1sSt2 t α accWAux = n1sAccTarget411 t β₁ := by
    dsimp only [n1sSt2, n1sLiftEval411, accWAux]; rw [n1s_dif_pos (by decide)]; exact hacc_ev
  have hTargetEq : n1sAccTarget411 t β₁ = if s3AcceptNorm1s t hmPay80 ((basisBitsEquiv
      (momCoreWires 80)).symm (embedAlpha107 (fun i ↦ α (Fin.castLE (by decide) i)))) = true
      then 1 else 0 := by
    unfold n1sAccTarget411
    dsimp only
    have hu38_val : bitsVal (fun k : Fin 38 ↦ β₁ (n1sU38W411 k)) =
        bitsVal (fun k : Fin 38 ↦ st1 α (p57U38W k)) :=
      congrArg bitsVal (funext fun k ↦ congrArg (st1 α) (Fin.ext (by fin_cases k <;> rfl)))
    have hpr_val : ∀ w : Fin 3, bitsVal (fun b : Fin 8 ↦
      β₁ (n1sProjW411 w b)) = (getProj (st1 α) w).val :=
      fun w ↦ congrArg bitsVal (funext fun b ↦
        congrArg (st1 α) (Fin.ext (by fin_cases w <;> fin_cases b <;> rfl)))
    have hvs_eq : β₁ n1sValidStaticW411 = st1 α validStaticW :=
      congrArg (st1 α) (Fin.ext rfl)
    rw [hs_val, hu38_val, hmu_val, hvs_eq]
    simp_rw [hpr_val]
    exact n1s_accBit_eq_s3AcceptNorm1s t (fun i ↦ α (Fin.castLE (by decide) i)) hInv1
      (fun k ↦ hAct1 (Fin.castLE (by decide) k))
  exact ⟨hInv2, fun k ↦
    (hnon2 ⟨k.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)).trans (hAct1 k),
    hnon2, hout2.trans hout_ev, hacc2, hacc2.trans hTargetEq⟩

theorem n1s_st4_props (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) (α : BitAssignment
    149) :
    N1sRetainedInv (n1sSt4 t cfg α) ∧
    (∀ k : Fin 149, n1sSt4 t cfg α ⟨k.val, by omega⟩ = corePerm149_norm1s t cfg α k) ∧
    n1sRevInv411 t (fun j : Wire 411 ↦ n1sSt4 t cfg α ⟨j.val, by omega⟩) := by
  obtain ⟨hInv2, hAct2, hnon2, hout2, hacc2_tgt, hacc2_s3⟩ := n1s_st2_props t α
  obtain ⟨hmk_non, hmk_cat⟩ := n1s_midKick36_cat42_eq t cfg α hInv2 hAct2 hacc2_s3
  have hnon3 : ∀ q : Wire 437, ¬(107 ≤ q.val ∧ q.val < 149) → n1sSt3 t cfg α q = n1sSt2 t α q :=
    fun q h107 ↦ by
      dsimp only [n1sSt3, n1sLiftEval411]
      by_cases h411 : q.val < 411
      · rw [n1s_dif_pos h411]; exact hmk_non ⟨q.val, h411⟩ h107
      · rw [n1s_dif_neg h411]; exact (hInv2.hcl q (by omega)).symm
  have hcl3 : cleanRem 437 (437 - 275) (n1sSt3 t cfg α) :=
    fun w hw ↦ (hnon3 w (by omega)).trans (hInv2.hcl w hw)
  have hInv3 : N1sRetainedInv (n1sSt3 t cfg α) := N1sRetainedInv.of_agree_core hInv2 hcl3
      (fun w h1 h2 ↦ (hnon3 w (by omega)).trans (hInv2.hz233 w h1 h2))
      (fun q h107 _ _ ↦ hnon3 q (by omega))
  have hlt107_3 : ∀ k : Fin 107, n1sSt3 t cfg α ⟨k.val, by omega⟩ = α (Fin.castLE (by decide) k) :=
    fun k ↦ (hnon3 ⟨k.val, by omega⟩ (by dsimp; omega)).trans (hAct2 (Fin.castLE (by decide) k))
  have hcat3 : ∀ j : Fin 42,
    n1sSt3 t cfg α (cat42W j) = corePerm149_norm1s t cfg α (Fin.natAdd 107 j) :=
    fun j ↦ by
      dsimp only [n1sSt3, n1sLiftEval411, cat42W]
      rw [n1s_dif_pos (by omega)]
      exact hmk_cat j
  have hacc3 : n1sSt3 t cfg α accWAux = if s3AcceptNorm1s t hmPay80 ((basisBitsEquiv
      (momCoreWires 80)).symm (embedAlpha107 (fun i ↦ α (Fin.castLE (by decide) i)))) = true
      then 1 else 0 := (hnon3 accWAux (by decide)).trans hacc2_s3
  obtain ⟨hInv4, hPerm4, hUnch4, _, hGridIff4⟩ :=
    n1s_cSwapFlip_preserves_and_perm t cfg α (γ_m := n1sSt4 t cfg α) rfl hInv3 hlt107_3 hcat3 hacc3
  let β₁ : BitAssignment 411 := fun j ↦ st1 α ⟨j.val, by omega⟩
  let β₄ : BitAssignment 411 := fun j ↦ n1sSt4 t cfg α ⟨j.val, by omega⟩
  have hEq4_1 : ∀ q : Wire 437, ¬(q.val < 24) → ¬(49 ≤ q.val ∧ q.val < 52) →
      ¬(107 ≤ q.val ∧ q.val < 174) → ¬(201 ≤ q.val ∧ q.val < 233) →
      n1sSt4 t cfg α q = st1 α q := fun q h24 h49 h107 h201 ↦
    (hUnch4 q h24 h49 (by omega)).trans ((hnon3 q (by omega)).trans (hnon2 q (by omega) h201))
  have hs_eq : bitsVal (fun i : Fin 18 ↦ β₄ (n1sSTrue18W411 i)) =
      bitsVal (fun i : Fin 18 ↦ β₁ (n1sSTrue18W411 i)) :=
    congrArg bitsVal (funext fun i ↦ by
      have hr := n1s_sTrue18W411_range i
      exact hEq4_1 ⟨(n1sSTrue18W411 i).val, by omega⟩
        (by dsimp; rcases hr with r | r | r <;> omega)
        (by dsimp; rcases hr with r | r | r <;> omega)
        (by dsimp; rcases hr with r | r | r <;> omega)
        (by dsimp; rcases hr with r | r | r <;> omega))
  have hu38_eq : bitsVal (fun k : Fin 38 ↦ β₄ (n1sU38W411 k)) =
      bitsVal (fun k : Fin 38 ↦ β₁ (n1sU38W411 k)) :=
    congrArg bitsVal (funext fun k ↦ by
      have hr := n1s_u38W411_range k
      exact hEq4_1 ⟨(n1sU38W411 k).val, by omega⟩
        (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega))
  have hmu_eq : bitsVal (fun i : Fin 3 ↦ β₄ (n1sMuW411 i)) =
      bitsVal (fun i : Fin 3 ↦ β₁ (n1sMuW411 i)) :=
    congrArg bitsVal (funext fun i ↦
      hEq4_1 ⟨174 + i.val, by
        omega⟩ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega) (by dsimp; omega))
  have hvs_eq : β₄ n1sValidStaticW411 = β₁ n1sValidStaticW411 :=
    hEq4_1 validStaticW (by decide) (by decide) (by decide) (by decide)
  have hout4_eq : bitsVal (fun k : Fin 32 ↦ β₄ (n1sOut32W411 k)) =
      bitsVal (fun k : Fin 32 ↦ n1sSt2 t α ⟨201 + k.val, by omega⟩) :=
    congrArg bitsVal (funext fun k ↦
      (hUnch4 ⟨201 + k.val, by omega⟩ (by dsimp; omega) (by dsimp; omega) (by dsimp; omega)).trans
        (hnon3 ⟨201 + k.val, by omega⟩ (by dsimp; omega)))
  have hacc4_eq : β₄ n1sAccFlagW411 = n1sSt2 t α accWAux :=
    (hUnch4 accWAux (by decide) (by decide) (by decide)).trans (hnon3 accWAux (by decide))
  have hAux_1 : ∀ w : Fin 3, (getProj (n1sSt3 t cfg α) w).val =
      bitsVal (fun b : Fin 8 ↦ β₁ (n1sProjW411 w b)) := fun w ↦
    congrArg bitsVal (funext fun b ↦
      ((hnon3 (p57ProjW w b) (by dsimp [p57ProjW]; omega)).trans
        (hnon2 (p57ProjW w b) (by dsimp [p57ProjW]; omega) (by dsimp [p57ProjW]; omega))).trans
        (congrArg (st1 α) (Fin.ext (by fin_cases w <;> fin_cases b <;> rfl))))
  have hGrid4_1 : (∀ w : Fin 3, bitsVal (fun b : Fin 8 ↦ β₄ (n1sProjW411 w b)) ≠ 128) ↔
      (∀ w : Fin 3, bitsVal (fun b : Fin 8 ↦ β₁ (n1sProjW411 w b)) ≠ 128) :=
    hGridIff4.trans (forall_congr' fun w ↦ by rw [hAux_1 w])
  refine ⟨hInv4, hPerm4, ?_, ?_, ?_⟩
  · rw [hout4_eq, hs_eq, hu38_eq]; exact hout2
  · exact (n1s_valid411_of_retained hInv4).2.2
  · change β₄ n1sAccFlagW411 = n1sAccTarget411 t β₄
    rw [hacc4_eq, hacc2_tgt]
    change n1sAccTarget411 t β₁ = n1sAccTarget411 t β₄
    unfold n1sAccTarget411
    simp only [hs_eq, hu38_eq, hmu_eq, hvs_eq, hGrid4_1]

theorem n1s_st5_props (t : Norm1sTier) (cfg : SpecsAux.SpecMirror.Configuration) (α : BitAssignment
    149) :
    N1sRetainedInv (n1sSt5 t cfg α) ∧
    (∀ k : Fin 149, n1sSt5 t cfg α ⟨k.val, by omega⟩ = corePerm149_norm1s t cfg α k) ∧
    n1sSt5 t cfg α accWAux = 0 ∧
    (∀ w : Wire 437, 201 ≤ w.val → w.val < 258 → n1sSt5 t cfg α w = 0) := by
  obtain ⟨hInv4, hPerm4, hRevInv4⟩ := n1s_st4_props t cfg α
  let β₄ : BitAssignment 411 := fun j ↦ n1sSt4 t cfg α ⟨j.val, by omega⟩
  have hcl_β₄ : cleanRem 411 (411 - 275) β₄ := fun j hj ↦ hInv4.hcl ⟨j.val, by omega⟩ hj
  obtain ⟨_, hcl_ev, hnon_ev, hzero_ev⟩ := (n1s_revStatic411_spec t).2 β₄ hcl_β₄
  obtain ⟨hacc0_ev, hout0_ev⟩ := hzero_ev hRevInv4
  obtain ⟨hInv5, hnon5⟩ := n1s_lift411_retained (n1sRevStatic411 t) hInv4 hcl_ev hnon_ev
  have hz233_5 : ∀ w : Wire 437, 233 ≤ w.val → w.val < 258 → n1sSt5 t cfg α w = 0 :=
    hInv5.hz233
  refine ⟨hInv5,
    fun k ↦ (hnon5 ⟨k.val, by omega⟩ (by dsimp; omega) (by dsimp; omega)).trans (hPerm4 k),
    by dsimp only [n1sSt5, n1sLiftEval411, accWAux]; rw [n1s_dif_pos (by decide)]; exact hacc0_ev,
    fun w h1 h2 ↦ ?_⟩
  by_cases h233 : w.val < 233
  · dsimp only [n1sSt5, n1sLiftEval411]; rw [n1s_dif_pos (by omega)]
    have hw_eq : (⟨w.val, by omega⟩ : Wire 411) = n1sOut32W411 ⟨w.val - 201, by omega⟩ :=
      Fin.ext (by dsimp [n1sOut32W411]; omega)
    rw [hw_eq]; exact hout0_ev _
  · exact hz233_5 w (by omega) h2

end
end Slot3Norm1s36CoreWide
end Slot3Norm1s36CoreWide

section Slot3Norm1s36LatticeBase
local instance (priority := 1000000) instNeZeroTwoPow_Slot3Norm1s36LatticeBase (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-
Exact 3D Octant-Orbit Lattice Certificate for Parametric `(K, D)` 1-Sided Normalized
Slot-3 Momentum Oracles (`Bk = 36`, `M0 = 127`, folding period `2 * 127 + 1 = 255`).

Provides the verified symbolic discrepancy definitions, bounds, and 3D-to-octant reduction
for `Slot3Norm1s262CoreSpec`, reducing the `16,581,374`-vector `nonzeroBox3D 127` sum
`46.3x` onto `357,759` sorted octant triples with `O(1)` C++ kernel `m_whnf_cache` reuse
across the `241,184` distinct `(mu, sTrue)` pairs.
-/

namespace Slot3Norm1s36LatticeBase
open Real
open scoped BigOperators

open Slot3Norm1s36_161w (Norm1sTier clz18Log2 clz18Log2_le_17 clz18Log2_bounds norm1sMant18
  norm1sMant18_bounds norm1sHwProd wc2TrueNat accThr)
open Slot3Norm1s36Physics80 (deltaBitTerm deltaNorm1sAux deltaNorm1s norm1sHwProd_int_eq
  deltaNorm1sAux_abs_le two_mul_mod_add_deltaAbsSum_le norm1sAcceptCountK)
open MomSlots35Slot3ProjNuclear (cRad7Computable)
open ModWrapCoarse8PureMomentum (modFoldCoord modFold3D sumNatAbsSq maxCoordNatAbs shellIndex
  nonzeroBox3D box3D mem_box3D mem_nonzeroBox3D modFoldCoord_eq modFoldCoord_eq_zero_iff
  sumNatAbsSq_pos_of_ne_zero maxCoordNatAbs_pos_of_ne_zero log2Fast127 log2Fast127_le_six
  nat_log_two_eq_log2Fast127 octWeight natSum natSum_congr natSum_add_split octShell
  sum_nonzeroBox3D_eq_oct_natSum max2Nat max3Nat max3Nat_eq_max max3Nat_swap12 max3Nat_swap23
  maxCoordNatAbs_eq_max3Nat inv4Val7 inv4Val7_eq)

attribute [local irreducible] box3D nonzeroBox3D

private theorem n1s_lat_if_pos {α : Type*} {c : Prop} {d : Decidable c} {t e : α} (hc : c) :
    @ite α c d t e = t := by
  cases d with
  | isTrue _ => rfl
  | isFalse h => exact absurd hc h

private theorem n1s_lat_if_neg {α : Type*} {c : Prop} {d : Decidable c} {t e : α} (hc : ¬ c) :
    @ite α c d t e = e := by
  cases d with
  | isTrue h => exact absurd h hc
  | isFalse _ => rfl

/- ## Section 1: Unboxed `ℕ` Lookup Trees and Unsigned Bit-Window Primitives -/

/-- Closed literal `2 ^ t.dCut` for each `Norm1sTier` avoiding `Nat.pow` in kernel WHNF. -/
def n1sPowD : Norm1sTier → ℕ
  | .t26_18 => 262144
  | .t26_17 => 131072
  | .t26_16 => 65536
  | .t27_17 => 131072
  | .t28_17 => 131072
  | .t29_18 => 262144
  | .t29_17 => 131072
  | .t30_18 => 262144

/-- Closed literal `t.dCut * 2 ^ t.dCut` bounding `|deltaNorm1sAux|` across all `uK`. -/
def n1sWindowBound : Norm1sTier → ℕ
  | .t26_18 => 4718592
  | .t26_17 => 2228224
  | .t26_16 => 1048576
  | .t27_17 => 2228224
  | .t28_17 => 2228224
  | .t29_18 => 4718592
  | .t29_17 => 2228224
  | .t30_18 => 4718592

/-- Closed literal `2 ^ t.kBits` for each `Norm1sTier`. -/
def n1sPow2K : Norm1sTier → ℕ
  | .t26_18 => 67108864
  | .t26_17 => 67108864
  | .t26_16 => 67108864
  | .t27_17 => 134217728
  | .t28_17 => 268435456
  | .t29_18 => 536870912
  | .t29_17 => 536870912
  | .t30_18 => 1073741824

/-- Closed literal `2 ^ (38 - t.kBits)` for each `Norm1sTier`. -/
def n1sPow2Sub38 : Norm1sTier → ℕ
  | .t26_18 => 4096
  | .t26_17 => 4096
  | .t26_16 => 4096
  | .t27_17 => 2048
  | .t28_17 => 1024
  | .t29_18 => 512
  | .t29_17 => 512
  | .t30_18 => 256

theorem n1sPowD_eq (t : Norm1sTier) : n1sPowD t = 2 ^ t.dCut := by
  cases t <;> rfl

theorem n1sWindowBound_eq (t : Norm1sTier) : n1sWindowBound t = t.dCut * 2 ^ t.dCut := by
  cases t <;> rfl

theorem n1sWindowBound_le (t : Norm1sTier) : n1sWindowBound t ≤ 4718592 := by
  cases t <;> exact Nat.ble_eq.mp rfl

theorem n1sPow2K_eq (t : Norm1sTier) : n1sPow2K t = 2 ^ t.kBits := by
  cases t <;> rfl

theorem n1sPow2Sub38_eq (t : Norm1sTier) : n1sPow2Sub38 t = 2 ^ (38 - t.kBits) := by
  cases t <;> rfl

theorem n1s_five_le_dCut (t : Norm1sTier) : 5 ≤ t.dCut := by
  cases t <;> dsimp [Norm1sTier.dCut] <;> omega

/-- Depth-5 binary-search `18`-entry lookup over `d < 18` (`v17` for `17 ≤ d`). -/
def n1sTable18 (d v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 : ℕ) : ℕ :=
    bif Nat.blt d 9 then bif Nat.blt d 4 then bif Nat.blt d 2 then bif Nat.blt d 1 then v0
    else v1 else bif Nat.blt d 3 then v2 else v3 else bif Nat.blt d 6 then bif Nat.blt d 5
    then v4 else v5 else bif Nat.blt d 7 then v6 else bif Nat.blt d 8 then v7 else v8 else bif
    Nat.blt d 13 then bif Nat.blt d 11 then bif Nat.blt d 10 then v9 else v10 else bif Nat.blt
    d 12 then v11 else v12 else bif Nat.blt d 15 then bif Nat.blt d 14 then v13 else v14 else
    bif Nat.blt d 16 then v15 else bif Nat.blt d 17 then v16 else v17

/-- Precomputed `(2 * accThr K D d - 2 - wc2TrueNat K D) * 2 ^ D` table over `d < 18`. -/
def n1sRhsConst (t : Norm1sTier) (d : ℕ) : ℕ :=
  match t with
  | .t26_18 =>
    n1sTable18 d
      35037228040192 17518613757952 8759306878976 4379653439488 2189826719744 1094913097728
        547456811008 273728143360 136863809536
      68432166912 34216083456 17108041728 8553758720 4276617216 2138570752 1069023232 534249472
        267386880
  | .t26_17 =>
    n1sTable18 d
      35037228171264 17518614151168 8759307010048 4379653570560 2189826588672 1094913228800
        547456679936 273728274432 136864202752
      68432035840 34215952384 17107910656 8553889792 4277010432 2138439680 1069154304 534642688
        267255808
  | .t26_16 =>
    n1sTable18 d
      35037228171264 17518614151168 8759307010048 4379653439488 2189826719744 1094913359872
        547456679936 273728274432 136864202752
      68432035840 34215952384 17108041728 8554020864 4277010432 2138439680 1069154304 534642688
        267255808
  | .t27_17 =>
    n1sTable18 d
      70074456473600 35037228171264 17518614151168 8759307010048 4379653570560 2189826588672
        1094913228800 547456679936 273728274432
      136864202752 68432035840 34215952384 17107910656 8553889792 4277010432 2138439680 1069154304
        534642688
  | .t28_17 =>
    n1sTable18 d
      140148912816128 70074456473600 35037228171264 17518614151168 8759307010048 4379653570560
        2189826588672 1094913228800 547456679936
      273728274432 136864202752 68432035840 34215952384 17107910656 8553889792 4277010432 2138439680
        1069154304
  | .t29_18 =>
    n1sTable18 d
      280297825894400 140148912685056 70074456604672 35037228040192 17518613757952 8759306878976
        4379653439488 2189826719744 1094913097728
      547456811008 273728143360 136863809536 68432166912 34216083456 17108041728 8553758720
        4276617216 2138570752
  | .t29_17 =>
    n1sTable18 d
      280297825763328 140148912816128 70074456473600 35037228171264 17518614151168 8759307010048
        4379653570560 2189826588672 1094913228800
      547456679936 273728274432 136864202752 68432035840 34215952384 17107910656 8553889792
        4277010432 2138439680
  | .t30_18 =>
    n1sTable18 d
      560595651788800 280297825894400 140148912685056 70074456604672 35037228040192 17518613757952
        8759306878976 4379653439488 2189826719744
      1094913097728 547456811008 273728143360 136863809536 68432166912 34216083456 17108041728
        8553758720 4276617216

/-- Half-threshold `((2 * accThr K D d - 2 - wc2TrueNat K D) * 2 ^ D + D * 2 ^ D) / 2` over `d <
  18`. -/
def n1sLimConst (t : Norm1sTier) (d : ℕ) : ℕ :=
  Nat.div (Nat.add (n1sRhsConst t d) (n1sWindowBound t)) 2

theorem n1s_lt18_cases {d : ℕ} (hd : d < 18) :
    d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨
    d = 9 ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 ∨ d = 16 ∨ d = 17 := by
  omega

theorem n1sRhsConst_int_eq (t : Norm1sTier) {d : ℕ} (hd : d < 18) : (n1sRhsConst t d : ℤ) = (2
    * (accThr t.kBits t.dCut d : ℤ) - 2 - (wc2TrueNat t.kBits t.dCut : ℤ)) * (2 ^ t.dCut : ℤ)
    := by
  cases t <;>
    rcases n1s_lt18_cases hd with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem n1sLimConst_int_eq (t : Norm1sTier) {d : ℕ} (hd : d < 18) : 2 * (n1sLimConst t d : ℤ)
    = (n1sRhsConst t d : ℤ) + (t.dCut : ℤ) * (2 ^ t.dCut : ℤ) := by
  cases t <;>
    rcases n1s_lt18_cases hd with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

theorem n1sRhsConst_ge_pow24 (t : Norm1sTier) {d : ℕ} (hd : d < 18) :
    16777216 ≤ n1sRhsConst t d := by
  cases t <;>
    rcases n1s_lt18_cases hd with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact Nat.ble_eq.mp rfl
theorem n1s_accThr_pos (t : Norm1sTier) {d : ℕ} (hd : d < 18) :
    0 < accThr t.kBits t.dCut d := by
  have h1 := n1sRhsConst_int_eq t hd
  have h2 := n1sRhsConst_ge_pow24 t hd
  have hp : (0 : ℤ) < (2 ^ t.dCut : ℤ) := by positivity
  have hpos : (0 : ℤ) < (2 * (accThr t.kBits t.dCut d : ℤ) - 2 - (wc2TrueNat t.kBits t.dCut :
      ℤ)) * (2 ^ t.dCut : ℤ) := by
    rw [← h1]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 16777216) h2)
  have hfac : (0 : ℤ) < 2 * (accThr t.kBits t.dCut d : ℤ) - 2 -
      (wc2TrueNat t.kBits t.dCut : ℤ) := pos_of_mul_pos_left hpos hp.le
  omega

/-- Depth-5 binary-search `⌊log_2 s⌋` on `0 < s < 2 ^ 18` (`0` when `s ≤ 1`). -/
def n1sClz18Fast (s : ℕ) : ℕ := bif Nat.blt s 512 then bif Nat.blt s 32 then bif Nat.blt s 4
    then bif Nat.blt s 2 then 0 else 1 else bif Nat.blt s 8 then 2 else bif Nat.blt s 16 then
    3 else 4 else bif Nat.blt s 128 then bif Nat.blt s 64 then 5 else 6 else bif Nat.blt s 256
    then 7 else 8 else bif Nat.blt s 8192 then bif Nat.blt s 2048 then bif Nat.blt s 1024 then
    9 else 10 else bif Nat.blt s 4096 then 11 else 12 else bif Nat.blt s 32768 then bif
    Nat.blt s 16384 then 13 else 14 else bif Nat.blt s 65536 then 15 else bif Nat.blt s 131072
    then 16 else 17

private theorem n1s_cond_bool_eq {b : Bool} {P : Prop} [Decidable P] (heq : (b = true) = P)
    {α : Type} (x y : α) : (bif b then x else y) = if P then x else y := by
  cases hb : b <;> split_ifs with hp
  · exact Bool.noConfusion (hb.symm.trans (heq.mpr hp))
  · rfl
  · rfl
  · exact (hp (heq.mp hb)).elim

theorem n1s_cond_blt_eq (a b : ℕ) {α : Type} (x y : α) :
    (bif Nat.blt a b then x else y) = if a < b then x else y :=
  n1s_cond_bool_eq Nat.blt_eq x y

theorem n1s_cond_ble_eq (a b : ℕ) {α : Type} (x y : α) :
    (bif Nat.ble a b then x else y) = if a ≤ b then x else y :=
  n1s_cond_bool_eq Nat.ble_eq x y

theorem n1s_cond_beq_eq (a b : ℕ) {α : Type} (x y : α) :
    (bif Nat.beq a b then x else y) = if a = b then x else y :=
  n1s_cond_bool_eq Nat.beq_eq x y

theorem n1sClz18Fast_bounds {s : ℕ} (hs0 : 0 < s) (hs18 : s < 262144) :
    2 ^ n1sClz18Fast s ≤ s ∧ s < 2 ^ (n1sClz18Fast s + 1) := by
  unfold n1sClz18Fast
  simp only [n1s_cond_blt_eq]
  split_ifs <;> norm_num <;> omega

theorem n1sClz18Fast_eq_clz18Log2 {s : ℕ} (hs18 : s < 262144) :
    n1sClz18Fast s = clz18Log2 s := by
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · rfl
  · obtain ⟨hlo1, hhi1⟩ := n1sClz18Fast_bounds hs0 hs18
    obtain ⟨hlo2, hhi2⟩ := clz18Log2_bounds hs0 (show s < 2 ^ 18 by norm_num; exact hs18)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hp : 2 ^ (n1sClz18Fast s + 1) ≤ 2 ^ clz18Log2 s :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have hp : 2 ^ (clz18Log2 s + 1) ≤ 2 ^ n1sClz18Fast s :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

/-- Lookup tree for `2 ^ (17 - e)` across `e ≤ 17`. -/
def n1sPow2Sub17Fast (e : ℕ) : ℕ :=
  n1sTable18 e 131072 65536 32768 16384 8192 4096 2048 1024 512 256 128 64 32 16 8 4 2 1

theorem n1sPow2Sub17Fast_eq {e : ℕ} (he : e ≤ 17) : n1sPow2Sub17Fast e = 2 ^ (17 - e) := by
  rcases n1s_lt18_cases (Nat.lt_succ_of_le he) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
/-- Lookup tree for `cRad7Computable mu` across `mu ≤ 6`. -/
def n1sCRadFast (mu : ℕ) : ℕ := bif Nat.blt mu 3 then bif Nat.blt mu 1 then 273728345630 else
    bif Nat.blt mu 2 then 1094913382523 else 4379653530094 else bif Nat.blt mu 5 then bif
    Nat.blt mu 4 then 17518614120377 else 70074456481511 else bif Nat.blt mu 6 then
    280297825926047 else 1121191303704190

theorem n1sCRadFast_eq {mu : ℕ} (hmu : mu ≤ 6) : n1sCRadFast mu = cRad7Computable mu := by
  rcases (show mu = 0 ∨ mu = 1 ∨ mu = 2 ∨ mu = 3 ∨ mu = 4 ∨ mu = 5 ∨ mu = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem n1s_nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl

theorem n1s_nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl

theorem n1s_nat_mul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl

theorem n1s_nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl

theorem n1s_nat_mod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl

/-- Direct `@Nat.rec` call-by-value application forcing `x` to a `LitVal` (`Nat.add 1 x` blocks
  symbolic WHNF). -/
def n1sCbv (f : ℕ → ℕ) (x : ℕ) : ℕ := @Nat.rec (fun _ ↦ ℕ) 0 (fun v _ ↦ f v) (Nat.add 1 x)

theorem n1sCbv_eq (f : ℕ → ℕ) (x : ℕ) : n1sCbv f x = f x := by
  change @Nat.rec (fun _ ↦ ℕ) 0 (fun v _ ↦ f v) (1 + x) = f x
  rw [Nat.one_add]

/-- Auxiliary second-stage curried application for `n1sCbv2` (`0` inline lambdas). -/
def n1sCbv2Aux (f : ℕ → ℕ → ℕ) (b va : ℕ) : ℕ := n1sCbv (f va) b

/-- Two-argument call-by-value application keying `m_whnf_cache` on `(LitVal a, LitVal b)`. -/
def n1sCbv2 (f : ℕ → ℕ → ℕ) (a b : ℕ) : ℕ := n1sCbv (n1sCbv2Aux f b) a

theorem n1sCbv2_eq (f : ℕ → ℕ → ℕ) (a b : ℕ) : n1sCbv2 f a b = f a b := by
  unfold n1sCbv2 n1sCbv2Aux
  rw [n1sCbv_eq, n1sCbv_eq]

/-- Branchless natural minimum `a - (a - b)` sharing `a`'s pointer in `m_whnf_cache`. -/
def n1sMinFast (a b : ℕ) : ℕ := Nat.sub a (Nat.sub a b)

theorem n1sMinFast_eq_min (a b : ℕ) : n1sMinFast a b = min a b := by
  unfold n1sMinFast
  simp only [n1s_nat_sub_eq]
  omega

/-- Unsigned branchless natural distance `|x - y|` sharing `(x, y)` pointers in `m_whnf_cache`. -/
def n1sNatDist (x y : ℕ) : ℕ := Nat.add (Nat.sub x y) (Nat.sub y x)

/-- Single-recursor `@Nat.rec` sum over `0..n-1` (`1` `reduce_recursor` entry per step). -/
def n1sSumTail (n : ℕ) (g : ℕ → ℕ) : ℕ :=
  @Nat.rec (fun _ ↦ ℕ) 0 (fun k acc ↦ Nat.add acc (g k)) n

theorem n1sSumTail_eq (n : ℕ) (g : ℕ → ℕ) : n1sSumTail n g = natSum n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      change Nat.add (n1sSumTail k g) (g k) = natSum k g + g k
      rw [ih, n1s_nat_add_eq]

/-- Shifts index `j` by `c` via `n1sCbv` `LitVal` evaluation before calling `g`. -/
def n1sShiftIdx (c : ℕ) (g : ℕ → ℕ) (j : ℕ) : ℕ := n1sCbv g (Nat.add c j)

theorem n1sShiftIdx_eq (c : ℕ) (g : ℕ → ℕ) : n1sShiftIdx c g = fun j ↦ g (c + j) := by
  funext j
  unfold n1sShiftIdx
  rw [n1sCbv_eq, n1s_nat_add_eq]

/-- Branchless natural maximum `a + (b - a)` sharing `a`'s pointer in `m_whnf_cache`. -/
def n1sMax2Fast (a b : ℕ) : ℕ := Nat.add a (Nat.sub b a)

theorem n1sNatDist_cast_eq (x y : ℕ) :
    (n1sNatDist x y : ℝ) = |(x : ℝ) - (y : ℝ)| := by
  unfold n1sNatDist
  simp only [n1s_nat_add_eq, n1s_nat_sub_eq]
  rcases le_total x y with h | h
  · have h1 : x - y = 0 := Nat.sub_eq_zero_of_le h
    have hr : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast h
    rw [h1, zero_add, Nat.cast_sub h, abs_of_nonpos (by linarith)]
    ring
  · have h2 : y - x = 0 := Nat.sub_eq_zero_of_le h
    have hr : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast h
    rw [h2, add_zero, Nat.cast_sub h, abs_of_nonneg (by linarith)]

/- ## Section 2: Flat-Spine Unsigned Bit-Remainder Evaluators for `deltaNorm1sAux` -/

/-- Doubling modulo `powD` for `x < powD` using DAG-shared `let` and `Nat.blt`. -/
def n1sStepX (powD x : ℕ) : ℕ :=
  let x2 := Nat.add x x
  bif Nat.blt x2 powD then x2 else Nat.sub x2 powD

/-- Five-step doubling modulo `powD` (`2` args for flat kernel spine). -/
def n1sStep5 (powD x0 : ℕ) : ℕ :=
  n1sStepX powD (n1sStepX powD (n1sStepX powD (n1sStepX powD (n1sStepX powD x0))))

/-- Reference tail-recursive unsigned accumulator computing `(deltaNorm1sAux d mS u d + d * 2^d)
  / 2`. -/
def n1sRemLoop (powD : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | k + 1, x, u, acc =>
      let term := bif Nat.beq (u % 2) 0 then x else powD - x
      let xn := n1sStepX powD x
      n1sRemLoop powD k xn (u / 2) (acc + term)

/-- Unrolled 5-bit low prefix of `n1sRemLoop` on `r = u % 32` (`3` args for flat kernel spine). -/
def n1sRemLow5 (powD x0 r : ℕ) : ℕ :=
  let t0 := bif Nat.beq (r % 2) 0 then x0 else powD - x0
  let x1 := n1sStepX powD x0
  let r1 := r / 2
  let t1 := bif Nat.beq (r1 % 2) 0 then x1 else powD - x1
  let x2 := n1sStepX powD x1
  let r2 := r1 / 2
  let t2 := bif Nat.beq (r2 % 2) 0 then x2 else powD - x2
  let x3 := n1sStepX powD x2
  let r3 := r2 / 2
  let t3 := bif Nat.beq (r3 % 2) 0 then x3 else powD - x3
  let x4 := n1sStepX powD x3
  let r4 := r3 / 2
  let t4 := bif Nat.beq (r4 % 2) 0 then x4 else powD - x4
  t0 + (t1 + (t2 + (t3 + t4)))

theorem n1sStepX_eq_mul_two_mod {powD x : ℕ} (hx : x < powD) :
    n1sStepX powD x = (x * 2) % powD := by
  unfold n1sStepX
  dsimp only
  simp only [n1s_nat_add_eq, n1s_nat_sub_eq, n1s_cond_blt_eq]
  split_ifs with hlt
  · rw [show x + x = x * 2 by omega, Nat.mod_eq_of_lt (by omega)]
  · rw [show x * 2 = (x + x - powD) + powD by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem n1sStepX_chain {powD : ℕ} (x a b : ℕ) (hab : a * 2 = b) (hpos : 0 < powD) :
    n1sStepX powD ((x * a) % powD) = (x * b) % powD := by
  rw [n1sStepX_eq_mul_two_mod (Nat.mod_lt _ hpos),
    Nat.mul_mod ((x * a) % powD) 2 powD, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc, hab]

theorem n1sStep5_eq_mod {powD x0 : ℕ} (hx0 : x0 < powD) :
    n1sStep5 powD x0 = (x0 * 32) % powD := by
  have hp : 0 < powD := by omega
  unfold n1sStep5
  rw[n1sStepX_eq_mul_two_mod hx0, n1sStepX_chain x0 2 4 rfl hp, n1sStepX_chain x0 4 8 rfl hp,
      n1sStepX_chain x0 8 16 rfl hp, n1sStepX_chain x0 16 32 rfl hp]

theorem n1sDiv_chain (u a b : ℕ) (hab : a * 2 = b) : (u / a) / 2 = u / b := by
  rw [Nat.div_div_eq_div_mul, hab]

/-- Zero-`let` 5-bit low remainder sum on `r = u % 32` (`38` AST nodes, `O(1)` `m_whnf_cache`
  shifts). -/
def n1sRemLow5Fast (powD x0 r : ℕ) : ℕ := Nat.add
    (bif Nat.beq (Nat.mod r 2) 0 then x0 else Nat.sub powD x0) (Nat.add (bif Nat.beq (Nat.mod
    (Nat.div r 2) 2) 0 then Nat.mod (Nat.mul x0 2) powD else Nat.sub powD (Nat.mod (Nat.mul x0
    2) powD)) (Nat.add (bif Nat.beq (Nat.mod (Nat.div r 4) 2) 0 then Nat.mod (Nat.mul x0 4)
    powD else Nat.sub powD (Nat.mod (Nat.mul x0 4) powD)) (Nat.add (bif Nat.beq (Nat.mod
    (Nat.div r 8) 2) 0 then Nat.mod (Nat.mul x0 8) powD else Nat.sub powD (Nat.mod (Nat.mul x0
    8) powD)) (bif Nat.beq (Nat.mod (Nat.div r 16) 2) 0 then Nat.mod (Nat.mul x0 16) powD else
    Nat.sub powD (Nat.mod (Nat.mul x0 16) powD)))))

theorem n1sRemLow5Fast_eq {powD x0 : ℕ} (hx0 : x0 < powD) (r : ℕ) :
    n1sRemLow5Fast powD x0 r = n1sRemLow5 powD x0 r := by
  have hp : 0 < powD := by omega
  unfold n1sRemLow5Fast n1sRemLow5
  dsimp only
  simp only [n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq, n1s_nat_div_eq, n1s_nat_mod_eq]
  rw[n1sStepX_eq_mul_two_mod hx0, n1sStepX_chain x0 2 4 rfl hp, n1sStepX_chain x0 4 8 rfl hp,
      n1sStepX_chain x0 8 16 rfl hp, n1sDiv_chain r 2 4 rfl, n1sDiv_chain r 4 8 rfl,
      n1sDiv_chain r 8 16 rfl]

theorem n1s_one_sub_sub_eq_ble (a b : ℕ) : 1 - (a - b) = (bif Nat.ble a b then 1 else 0) := by
  rw [n1s_cond_ble_eq]
  split_ifs <;> omega

/-- Zero-`let` 3-step unsigned remainder sum at `powD = 65536` (`2` args). -/
def n1sRem3_65536 (x0 q0 : ℕ) : ℕ :=
  Nat.add (Nat.add ((bif Nat.beq (Nat.mod (q0) 2) 0 then x0 else
    Nat.sub 65536 (x0))) (bif Nat.beq (Nat.mod (Nat.div q0 2) 2) 0 then
    Nat.mod (Nat.mul x0 2) 65536 else
    Nat.sub 65536 (Nat.mod (Nat.mul x0 2) 65536))) (bif Nat.beq (Nat.mod (Nat.div q0 4) 2) 0 then
    Nat.mod (Nat.mul x0 4) 65536 else Nat.sub 65536 (Nat.mod (Nat.mul x0 4) 65536))

theorem n1sRem3_65536_eq {x0 : ℕ} (hx0 : x0 < 65536) (q0 : ℕ) :
    n1sRem3_65536 x0 q0 = n1sRemLoop 65536 3 x0 q0 0 := by
  have hp : 0 < 65536 := by norm_num
  unfold n1sRem3_65536
  simp only [n1sRemLoop, Nat.zero_add,
    n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq, n1s_nat_div_eq, n1s_nat_mod_eq]
  rw[n1sStepX_eq_mul_two_mod hx0, n1sStepX_chain x0 2 4 rfl hp, n1sDiv_chain q0 2 4 rfl]

/-- Zero-`let` 4-step unsigned remainder sum parameterized by `powD`. -/
def n1sRem4 (powD x0 q0 : ℕ) : ℕ := Nat.add (Nat.add (Nat.add (bif Nat.beq (Nat.mod q0 2) 0
    then x0 else Nat.sub powD x0) (bif Nat.beq (Nat.mod (Nat.div q0 2) 2) 0 then Nat.mod
    (Nat.mul x0 2) powD else Nat.sub powD (Nat.mod (Nat.mul x0 2) powD))) (bif Nat.beq
    (Nat.mod (Nat.div q0 4) 2) 0 then Nat.mod (Nat.mul x0 4) powD else Nat.sub powD (Nat.mod
    (Nat.mul x0 4) powD))) (bif Nat.beq (Nat.mod (Nat.div q0 8) 2) 0 then Nat.mod (Nat.mul x0
    8) powD else Nat.sub powD (Nat.mod (Nat.mul x0 8) powD))

theorem n1sRem4_eq {powD x0 : ℕ} (hx0 : x0 < powD) (q0 : ℕ) :
    n1sRem4 powD x0 q0 = n1sRemLoop powD 4 x0 q0 0 := by
  have hp : 0 < powD := by omega
  unfold n1sRem4
  simp only [n1sRemLoop, Nat.zero_add,
    n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq, n1s_nat_div_eq, n1s_nat_mod_eq]
  rw[n1sStepX_eq_mul_two_mod hx0, n1sStepX_chain x0 2 4 rfl hp, n1sStepX_chain x0 4 8 rfl hp,
      n1sDiv_chain q0 2 4 rfl, n1sDiv_chain q0 4 8 rfl]

/-- Zero-`let` 5-step unsigned remainder sum at `powD = 262144` (`2` args). -/
def n1sRem5_262144 (x0 q0 : ℕ) : ℕ := Nat.add (n1sRem4 262144 x0 q0) (bif Nat.beq (Nat.mod
    (Nat.div q0 16) 2) 0 then Nat.mod (Nat.mul x0 16) 262144 else Nat.sub 262144 (Nat.mod
    (Nat.mul x0 16) 262144))

theorem n1sRem5_262144_eq {x0 : ℕ} (hx0 : x0 < 262144) (q0 : ℕ) :
    n1sRem5_262144 x0 q0 = n1sRemLoop 262144 5 x0 q0 0 := by
  have hp : 0 < 262144 := by norm_num
  unfold n1sRem5_262144 n1sRem4
  simp only [n1sRemLoop, Nat.zero_add,
    n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq, n1s_nat_div_eq, n1s_nat_mod_eq]
  rw[n1sStepX_eq_mul_two_mod hx0, n1sStepX_chain x0 2 4 rfl hp, n1sStepX_chain x0 4 8 rfl hp,
      n1sStepX_chain x0 8 16 rfl hp, n1sDiv_chain q0 2 4 rfl, n1sDiv_chain q0 4 8 rfl,
      n1sDiv_chain q0 8 16 rfl]

/-- Decoupled `4 + 4 + 3`-bit high remainder sum at `powD = 65536` (`0` `@Nat.rec`s). -/
def n1sRemHi11_65536 (x5 q : ℕ) : ℕ := Nat.add (Nat.add (n1sRem4 65536 x5 (Nat.mod q 16))
    (n1sRem4 65536 (Nat.mod (Nat.mul x5 16) 65536) (Nat.mod (Nat.div q 16) 16)))
    (n1sRem3_65536 (Nat.mod (Nat.mul x5 256) 65536) (Nat.mod (Nat.div q 256) 8))

/-- Decoupled `4 + 4 + 4`-bit high remainder sum at `powD = 131072` (`0` `@Nat.rec`s). -/
def n1sRemHi12_131072 (x5 q : ℕ) : ℕ := Nat.add (Nat.add (n1sRem4 131072 x5 (Nat.mod q 16))
    (n1sRem4 131072 (Nat.mod (Nat.mul x5 16) 131072) (Nat.mod (Nat.div q 16) 16))) (n1sRem4
    131072 (Nat.mod (Nat.mul x5 256) 131072) (Nat.mod (Nat.div q 256) 16))

/-- Decoupled `4 + 4 + 5`-bit high remainder sum at `powD = 262144` (`0` `@Nat.rec`s). -/
def n1sRemHi13_262144 (x5 q : ℕ) : ℕ := Nat.add (Nat.add (n1sRem4 262144 x5 (Nat.mod q 16))
    (n1sRem4 262144 (Nat.mod (Nat.mul x5 16) 262144) (Nat.mod (Nat.div q 16) 16)))
    (n1sRem5_262144 (Nat.mod (Nat.mul x5 256) 262144) (Nat.mod (Nat.div q 256) 32))
/-- Flat `3`-arg high-bit remainder dispatcher avoiding deep partial-application spines in WHNF. -/
def n1sRemHi5 (t : Norm1sTier) (x5 q : ℕ) : ℕ :=
  match t with
  | .t26_18 | .t29_18 | .t30_18 => n1sRemHi13_262144 x5 q
  | .t26_17 | .t27_17 | .t28_17 | .t29_17 => n1sRemHi12_131072 x5 q
  | .t26_16 => n1sRemHi11_65536 x5 q

theorem n1sStepX_step {d k n : ℕ} (hd : n + (k + 1) = d) (mS : ℕ) : (mS % 2 ^ (k + 1)) * 2 ^ n
    ≤ 2 ^ d ∧ n1sStepX (2 ^ d) ((mS % 2 ^ (k + 1)) * 2 ^ n) = (mS % 2 ^ k) * 2 ^ (n + 1) := by
  have hmod : mS % 2 ^ (k + 1) = mS % 2 ^ k + 2 ^ k * ((mS / 2 ^ k) % 2) := Nat.mod_pow_succ
  have hr_lt : mS % 2 ^ k < 2 ^ k := Nat.mod_lt mS (Nat.two_pow_pos k)
  have hpowD : 2 ^ d = 2 ^ (k + 1) * 2 ^ n := by rw [← pow_add]; congr 1; omega
  have hpowD' : 2 ^ d = 2 ^ k * 2 ^ (n + 1) := by rw [← pow_add]; congr 1; omega
  have hx_lt : (mS % 2 ^ (k + 1)) * 2 ^ n < 2 ^ d := by
    rw [hpowD]
    exact Nat.mul_lt_mul_of_pos_right (Nat.mod_lt mS (Nat.two_pow_pos (k + 1))) (Nat.two_pow_pos n)
  have hxn_lt : (mS % 2 ^ k) * 2 ^ (n + 1) < 2 ^ d := by
    rw [hpowD']
    exact Nat.mul_lt_mul_of_pos_right hr_lt (Nat.two_pow_pos (n + 1))
  refine ⟨hx_lt.le, ?_⟩
  unfold n1sStepX
  dsimp only
  simp only [n1s_nat_add_eq, n1s_nat_sub_eq]
  rw [n1s_cond_blt_eq]
  rcases Nat.mod_two_eq_zero_or_one (mS / 2 ^ k) with hb0 | hb1
  · have hx2 : (mS % 2 ^ (k + 1)) * 2 ^ n + (mS % 2 ^ (k + 1)) * 2 ^ n =
        (mS % 2 ^ k) * 2 ^ (n + 1) := by
      rw [hmod, hb0, pow_succ]; ring
    rw [hx2, n1s_lat_if_pos hxn_lt]
  · have hx2 : (mS % 2 ^ (k + 1)) * 2 ^ n + (mS % 2 ^ (k + 1)) * 2 ^ n =
        (mS % 2 ^ k) * 2 ^ (n + 1) + 2 ^ d := by
      rw [hmod, hb1, hpowD', pow_succ]; ring
    rw [hx2, n1s_lat_if_neg (by omega)]
    omega

theorem n1sRemLoop_invariant (d mS uK : ℕ) :
    ∀ k n : ℕ, n + k = d → ∀ acc : ℕ,
      2 * (acc : ℤ) - (n : ℤ) * (2 ^ d : ℤ) = deltaNorm1sAux d mS uK n →
      2 * (n1sRemLoop (2 ^ d) k ((mS % 2 ^ k) * 2 ^ n) (uK / 2 ^ n) acc : ℤ) -
          (d : ℤ) * (2 ^ d : ℤ) =
        deltaNorm1sAux d mS uK d
  | 0, n, hd, acc, hacc => by
      have hn : n = d := by omega
      subst hn
      exact hacc
  | k + 1, n, hd, acc, hacc => by
      obtain ⟨hx_le, hstep⟩ := n1sStepX_step hd mS
      have hsub : d - n = k + 1 := by omega
      have hn_lt : n < d := by omega
      have hpowD : (2 ^ d : ℤ) = (2 ^ (k + 1) : ℤ) * (2 ^ n : ℤ) := by
        rw [← pow_add]; congr 1; omega
      have hdiv : (uK / 2 ^ n) / 2 = uK / 2 ^ (n + 1) := by
        rw [Nat.div_div_eq_div_mul, ← pow_succ]
      set x := (mS % 2 ^ (k + 1)) * 2 ^ n
      set term := bif Nat.beq ((uK / 2 ^ n) % 2) 0 then x else 2 ^ d - x
      have hbit : 2 * (term : ℤ) - (2 ^ d : ℤ) = deltaBitTerm d n mS (uK.testBit n) := by
        dsimp only [term]
        rw [n1s_cond_beq_eq, Nat.testBit_eq_decide_div_mod_eq]
        unfold deltaBitTerm
        simp only [hn_lt, ite_true, hsub]
        rcases Nat.mod_two_eq_zero_or_one (uK / 2 ^ n) with hu0 | hu1
        · have hdec : decide ((uK / 2 ^ n) % 2 = 1) = false := by rw [hu0]; rfl
          rw [n1s_lat_if_pos hu0, hdec]
          simp only [x, Bool.false_eq_true, ite_false, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
            hpowD]
          ring
        · have hne0 : (uK / 2 ^ n) % 2 ≠ 0 := by omega
          have hdec : decide ((uK / 2 ^ n) % 2 = 1) = true := by rw [hu1]; rfl
          rw [n1s_lat_if_neg hne0, hdec]
          simp only [x, ite_true, Nat.cast_sub hx_le, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
            hpowD]
          ring
      have hnext : 2 * ((acc + term : ℕ) : ℤ) - ((n + 1 : ℕ) : ℤ) * (2 ^ d : ℤ) =
          deltaNorm1sAux d mS uK (n + 1) := by
        rw [deltaNorm1sAux, ← hacc, ← hbit]
        push_cast
        ring
      unfold n1sRemLoop
      dsimp only
      rw [hstep, hdiv]
      exact n1sRemLoop_invariant d mS uK k (n + 1) (by omega) (acc + term) hnext

theorem n1sRemLoop_eq_deltaNorm1sAux (d mS uK : ℕ) :
    2 * (n1sRemLoop (2 ^ d) d (mS % 2 ^ d) uK 0 : ℤ) - (d : ℤ) * (2 ^ d : ℤ) =
      deltaNorm1sAux d mS uK d := by
  simpa using n1sRemLoop_invariant d mS uK d 0 (by omega) 0 (by simp [deltaNorm1sAux])

theorem n1sRemLoop_acc (powD : ℕ) : ∀ k x u acc,
    n1sRemLoop powD k x u acc = acc + n1sRemLoop powD k x u 0
  | 0, _, _, acc => (Nat.add_zero acc).symm
  | k + 1, x, u, acc => by
      dsimp only [n1sRemLoop]
      rw [n1sRemLoop_acc powD k, n1sRemLoop_acc powD k _ _ (0 + _), zero_add, Nat.add_assoc]

theorem n1sRemLoop_succ_zero (powD k x u : ℕ) : n1sRemLoop powD (k + 1) x u 0 =
    (bif Nat.beq (u % 2) 0 then x else powD - x) + n1sRemLoop powD k (n1sStepX powD x) (u / 2)
    0 := by
  dsimp only [n1sRemLoop]
  rw [n1sRemLoop_acc, zero_add]

private theorem n1sRemLoop_mod_pow2 (powD : ℕ) :
    ∀ k x0 u, n1sRemLoop powD k x0 (u % 2 ^ k) 0 = n1sRemLoop powD k x0 u 0
  | 0, _, _ => rfl
  | m + 1, x0, u => by
      have hd1 := Nat.div_add_mod u 2
      have hd2 := Nat.div_add_mod (u / 2) (2 ^ m)
      have hlt2 : (u / 2) % 2 ^ m < 2 ^ m := Nat.mod_lt _ (Nat.two_pow_pos m)
      have hu : u = (2 * ((u / 2) % 2 ^ m) + u % 2) + 2 ^ (m + 1) * ((u / 2) / 2 ^ m) := by
        have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        rw [hp]
        linarith
      have hlt : 2 * ((u / 2) % 2 ^ m) + u % 2 < 2 ^ (m + 1) := by
        have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        omega
      have hmod : u % 2 ^ (m + 1) = 2 * ((u / 2) % 2 ^ m) + u % 2 := by
        conv_lhs => rw [hu]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      rw [n1sRemLoop_succ_zero, n1sRemLoop_succ_zero,
        show (u % 2 ^ (m + 1)) % 2 = u % 2 by omega,
        show (u % 2 ^ (m + 1)) / 2 = (u / 2) % 2 ^ m by omega,
        n1sRemLoop_mod_pow2 powD m]

theorem n1sRemLoop_mod3 (powD x0 u : ℕ) :
    n1sRemLoop powD 3 x0 (u % 8) 0 = n1sRemLoop powD 3 x0 u 0 :=
  n1sRemLoop_mod_pow2 powD 3 x0 u

theorem n1sRemLoop_mod4 (powD x0 u : ℕ) :
    n1sRemLoop powD 4 x0 (u % 16) 0 = n1sRemLoop powD 4 x0 u 0 :=
  n1sRemLoop_mod_pow2 powD 4 x0 u

theorem n1sRemLoop_mod5 (powD x0 u : ℕ) :
    n1sRemLoop powD 5 x0 (u % 32) 0 = n1sRemLoop powD 5 x0 u 0 :=
  n1sRemLoop_mod_pow2 powD 5 x0 u

theorem n1sRemLoop_split4 {d : ℕ} (hd4 : 4 ≤ d) {powD x0 : ℕ} (hx0 : x0 < powD) (u : ℕ) :
    n1sRemLoop powD d x0 u 0 = n1sRemLoop powD 4 x0 (u % 16) 0 + n1sRemLoop powD (d - 4)
    ((x0 * 16) % powD) (u / 16) 0 := by
  have hp : 0 < powD := by omega
  have hd_eq : d = (d - 4) + 4 := by omega
  conv_lhs =>
    rw [hd_eq, n1sRemLoop_succ_zero, n1sRemLoop_succ_zero, n1sRemLoop_succ_zero,
    n1sRemLoop_succ_zero]
  conv_rhs =>
    rw [n1sRemLoop_succ_zero, n1sRemLoop_succ_zero, n1sRemLoop_succ_zero, n1sRemLoop_succ_zero]
  dsimp only [n1sRemLoop]
  have hm0 : (u % 16) % 2 = u % 2 := by omega
  have hm1 : ((u % 16) / 2) % 2 = (u / 2) % 2 := by omega
  have hm2 : (((u % 16) / 2) / 2) % 2 = ((u / 2) / 2) % 2 := by omega
  have hm3 : ((((u % 16) / 2) / 2) / 2) % 2 = (((u / 2) / 2) / 2) % 2 := by omega
  have hdiv : ((((u / 2) / 2) / 2) / 2) = u / 16 := by omega
  have hstep4 : n1sStepX powD (n1sStepX powD (n1sStepX powD (n1sStepX powD x0))) =
      (x0 * 16) % powD := by
    rw[n1sStepX_eq_mul_two_mod hx0, n1sStepX_chain x0 2 4 rfl hp,
        n1sStepX_chain x0 4 8 rfl hp, n1sStepX_chain x0 8 16 rfl hp]
  rw [hm0, hm1, hm2, hm3, hdiv, hstep4]
  ac_rfl

theorem n1sRemLoop_split4_4 {k powD x5 : ℕ} (hx5 : x5 < powD) (q : ℕ) : n1sRemLoop powD
    (8 + k) x5 q 0 = (n1sRemLoop powD 4 x5 (q % 16) 0 + n1sRemLoop powD 4 ((x5 * 16) % powD)
    ((q / 16) % 16) 0) + n1sRemLoop powD k ((x5 * 256) % powD) (q / 256) 0 := by
  have hp : 0 < powD := by omega
  rw [n1sRemLoop_split4 (by omega) hx5 q]
  have hsub1 : 8 + k - 4 = 4 + k := by omega
  rw [hsub1, n1sRemLoop_split4 (by omega) (Nat.mod_lt _ hp) (q / 16)]
  have hsub2 : 4 + k - 4 = k := by omega
  have hx256 : ((x5 * 16) % powD * 16) % powD = (x5 * 256) % powD := by
    rw [Nat.mul_mod ((x5 * 16) % powD), Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]
  have hq256 : (q / 16) / 16 = q / 256 := by omega
  rw [hsub2, hx256, hq256, Nat.add_assoc]

theorem n1sRemHi11_65536_eq {x5 : ℕ} (hx5 : x5 < 65536) (q : ℕ) :
    n1sRemHi11_65536 x5 q = n1sRemLoop 65536 11 x5 q 0 := by
  have hp : 0 < 65536 := by norm_num
  unfold n1sRemHi11_65536
  simp only [n1s_nat_add_eq, n1s_nat_mul_eq, n1s_nat_div_eq, n1s_nat_mod_eq]
  rw [n1sRem4_eq hx5, n1sRem4_eq (Nat.mod_lt _ hp), n1sRem3_65536_eq (Nat.mod_lt _ hp),
    n1sRemLoop_mod3]
  exact (n1sRemLoop_split4_4 (k := 3) hx5 q).symm

theorem n1sRemHi12_131072_eq {x5 : ℕ} (hx5 : x5 < 131072) (q : ℕ) :
    n1sRemHi12_131072 x5 q = n1sRemLoop 131072 12 x5 q 0 := by
  have hp : 0 < 131072 := by norm_num
  unfold n1sRemHi12_131072
  simp only [n1s_nat_add_eq, n1s_nat_mul_eq, n1s_nat_div_eq, n1s_nat_mod_eq]
  rw [n1sRem4_eq hx5, n1sRem4_eq (Nat.mod_lt _ hp), n1sRem4_eq (Nat.mod_lt _ hp),
    n1sRemLoop_mod4 131072 _ (q / 256)]
  exact (n1sRemLoop_split4_4 (k := 4) hx5 q).symm

theorem n1sRemHi13_262144_eq {x5 : ℕ} (hx5 : x5 < 262144) (q : ℕ) :
    n1sRemHi13_262144 x5 q = n1sRemLoop 262144 13 x5 q 0 := by
  have hp : 0 < 262144 := by norm_num
  unfold n1sRemHi13_262144
  simp only [n1s_nat_add_eq, n1s_nat_mul_eq, n1s_nat_div_eq, n1s_nat_mod_eq]
  rw [n1sRem4_eq hx5, n1sRem4_eq (Nat.mod_lt _ hp), n1sRem5_262144_eq (Nat.mod_lt _ hp),
    n1sRemLoop_mod5]
  exact (n1sRemLoop_split4_4 (k := 5) hx5 q).symm
theorem n1sRemHi5_eq (t : Norm1sTier) {x5 : ℕ} (hx5 : x5 < 2 ^ t.dCut) (q : ℕ) :
    n1sRemHi5 t x5 q = n1sRemLoop (2 ^ t.dCut) (t.dCut - 5) x5 q 0 := by
  cases t <;>
    (dsimp only [n1sRemHi5, Norm1sTier.dCut] at hx5 ⊢
     simp only [Nat.reducePow, Nat.reduceSub] at hx5 ⊢
     first
     | exact n1sRemHi13_262144_eq hx5 q
     | exact n1sRemHi12_131072_eq hx5 q
     | exact n1sRemHi11_65536_eq hx5 q)

theorem n1sRemLoop_split5 {d : ℕ} (hd5 : 5 ≤ d) (powD x0 u : ℕ) : n1sRemLoop powD d x0 u 0 =
    n1sRemLow5 powD x0 (u % 32) + n1sRemLoop powD (d - 5) (n1sStep5 powD x0) (u / 32) 0 := by
  have hd_eq : d = (d - 5) + 5 := by omega
  conv_lhs => rw [hd_eq]
  simp only [n1sRemLoop_succ_zero, n1sRemLow5, n1sStep5]
  have hm0 : (u % 32) % 2 = u % 2 := by omega
  have hm1 : ((u % 32) / 2) % 2 = (u / 2) % 2 := by omega
  have hm2 : (((u % 32) / 2) / 2) % 2 = ((u / 2) / 2) % 2 := by omega
  have hm3 : ((((u % 32) / 2) / 2) / 2) % 2 = (((u / 2) / 2) / 2) % 2 := by omega
  have hm4 : (((((u % 32) / 2) / 2) / 2) / 2) % 2 = ((((u / 2) / 2) / 2) / 2) % 2 := by omega
  have hdiv : (((((u / 2) / 2) / 2) / 2) / 2) = u / 32 := by omega
  rw [hm0, hm1, hm2, hm3, hm4, hdiv]
  ac_rfl

/- ## Section 3: Flat-Spine `[uLo, uHi)` Boundary Scan and Equivalence to `norm1sAcceptCountK` -/

/-- Reference plain-`let` specification of `n1sFastAcceptCountK` for proof bridging. -/
def n1sSpecAcceptCountK (t : Norm1sTier) (mu s : ℕ) : ℕ :=
  let e := n1sClz18Fast s
  bif Nat.blt e (2 * mu) then 0
  else
    let mS := s * n1sPow2Sub17Fast e
    let powD := n1sPowD t
    let x0 := mS % powD
    let bNat := n1sWindowBound t
    let d := e - 2 * mu
    let rhs := n1sRhsConst t d
    let mS2 := mS + mS
    let mS4 := mS2 + mS2
    let capK := n1sPow2K t
    let uLo := n1sMinFast capK ((rhs + mS2 - bNat) / mS4)
    let uHi := n1sMinFast capK ((rhs + mS2 + bNat) / mS4)
    bif Nat.ble uHi uLo then uLo
    else
      let x5 := n1sStep5 powD x0
      let q0 := uLo / 32
      let h0 := n1sRemHi5 t x5 q0
      let h1 := bif Nat.beq ((uHi - 1) / 32) q0 then h0 else n1sRemHi5 t x5 (q0 + 1)
      let lim := n1sLimConst t d
      uLo + natSum (uHi - uLo) (fun i ↦
        let u := uLo + i
        let hiRem := bif Nat.beq (u / 32) q0 then h0 else h1
        bif Nat.ble (mS2 * u + mS + (n1sRemLow5 powD x0 (u % 32) + hiRem)) lim then 1 else 0)

/-- Branchless zero-`let` single-point evaluation sharing leaf `BVar` pointers (`0` `@Nat.rec`s). -/
def n1sScanAt (powD x0 mS2 baseH lim u : ℕ) : ℕ := Nat.sub 1 (Nat.sub (Nat.add (Nat.mul mS2 u)
    (Nat.add baseH (n1sRemLow5Fast powD x0 (Nat.mod u 32)))) lim)

/-- Shifts scan index `i` to `u = pHi + i` before calling `n1sScanAt` (`0` `@Nat.rec`s). -/
def n1sScanSubStep (powD x0 mS2 baseH lim pHi i : ℕ) : ℕ :=
  n1sScanAt powD x0 mS2 baseH lim (Nat.add pHi i)

/-- Unrolled zero-recursor scan sum for `n ≤ 5` sharing leaf `BVar` pointers (`0` `@Nat.rec`s on
  all active windows). -/
def n1sSumTailLe5 (n powD x0 mS2 baseH lim pHi : ℕ) : ℕ := bif Nat.beq n 0 then 0 else bif
    Nat.beq n 1 then n1sScanAt powD x0 mS2 baseH lim pHi else bif Nat.beq n 2 then Nat.add
    (n1sScanAt powD x0 mS2 baseH lim pHi) (n1sScanAt powD x0 mS2 baseH lim (Nat.add pHi 1))
    else bif Nat.beq n 3 then Nat.add (Nat.add (n1sScanAt powD x0 mS2 baseH lim pHi)
    (n1sScanAt powD x0 mS2 baseH lim (Nat.add pHi 1)))
    (n1sScanAt powD x0 mS2 baseH lim (Nat.add pHi 2)) else bif Nat.beq n 4 then Nat.add
    (Nat.add (n1sScanAt powD x0 mS2 baseH lim pHi) (n1sScanAt powD x0 mS2 baseH lim (Nat.add
    pHi 1))) (Nat.add (n1sScanAt powD x0 mS2 baseH lim (Nat.add pHi 2)) (n1sScanAt powD x0 mS2
    baseH lim (Nat.add pHi 3))) else bif Nat.beq n 5 then Nat.add (Nat.add (Nat.add (n1sScanAt
    powD x0 mS2 baseH lim pHi) (n1sScanAt powD x0 mS2 baseH lim (Nat.add pHi 1))) (Nat.add
    (n1sScanAt powD x0 mS2 baseH lim (Nat.add pHi 2)) (n1sScanAt powD x0 mS2 baseH lim
    (Nat.add pHi 3)))) (n1sScanAt powD x0 mS2 baseH lim (Nat.add pHi 4)) else n1sSumTail n
    (n1sScanSubStep powD x0 mS2 baseH lim pHi)

/-- Evaluates `(pHi - a) + sum_{i < sHi - pHi} n1sScanSubStep` sharing `(pHi, sHi)` pointers (`0`
  `@Nat.rec`s). -/
def n1sScanFromBounds (powD x0 mS2 lim a baseH pHi sHi : ℕ) : ℕ := Nat.add (Nat.sub pHi a)
    (n1sSumTailLe5 (Nat.sub sHi pHi) powD x0 mS2 baseH lim pHi)

/-- Computes `sHi` from `pHi` and dispatches to `n1sScanFromBounds` (`0` `@Nat.rec`s). -/
def n1sScanFromPHi (powD x0 mS2 lim a b baseH pHi : ℕ) : ℕ :=
  n1sScanFromBounds powD x0 mS2 lim a baseH pHi
    (n1sMax2Fast pHi (n1sMinFast b (Nat.add (Nat.div (Nat.sub lim baseH) mS2) 1)))

/-- Computes `pHi` from `baseH` and dispatches to `n1sScanFromPHi` (`0` `@Nat.rec`s). -/
def n1sScanFromBase (powD x0 mS2 lim a b baseH : ℕ) : ℕ := bif Nat.blt lim baseH then 0 else
    n1sScanFromPHi powD x0 mS2 lim a b baseH (n1sMinFast b (n1sMax2Fast a (Nat.div (Nat.sub
    (Nat.add lim mS2) (Nat.add baseH (Nat.mul 5 powD))) mS2)))

/-- Counts `u ∈ [a, b)` with `mS2 * u + mS + (low5(u) + h) ≤ lim` scanning only `[pHi, sHi)` (`≤
  5` points). -/
def n1sScanConstHi (powD x0 mS2 mS lim h a b : ℕ) : ℕ := bif Nat.ble b a then 0 else
    n1sScanFromBase powD x0 mS2 lim a b (Nat.add mS h)

/-- Splits `[uLo, uHi)` at `bnd = (q0 + 1) * 32` into at most two constant-`hiRem` sub-intervals. -/
def n1sAcceptWindowFromQ0 (t : Norm1sTier) (powD mS mS2 x0 lim x5 q0 uLo uHi h0 bnd : ℕ) : ℕ
    := bif Nat.ble uHi bnd then Nat.add uLo (n1sScanConstHi powD x0 mS2 mS lim h0 uLo uHi)
    else Nat.add uLo (Nat.add (n1sScanConstHi powD x0 mS2 mS lim h0 uLo bnd) (n1sScanConstHi
    powD x0 mS2 mS lim (n1sRemHi5 t x5 (Nat.add q0 1)) bnd uHi))

/-- Dispatches `(h0, bnd)` once `q0 = uLo / 32` is bound (`0` `@Nat.rec`s). -/
def n1sAcceptWinQ0 (t : Norm1sTier) (powD mS mS2 x0 uLo uHi lim x5 q0 : ℕ) : ℕ :=
  n1sAcceptWindowFromQ0 t powD mS mS2 x0 lim x5 q0 uLo uHi
    (n1sRemHi5 t x5 q0) (Nat.mul (Nat.add q0 1) 32)

/-- Shares `x0 = mS % powD` across `n1sAcceptWinQ0` and `x5 = (x0 * 32) % powD` (`0`
  `@Nat.rec`s). -/
def n1sCntX0 (t : Norm1sTier) (d mS mS2 powD uLo uHi x0 : ℕ) : ℕ := n1sAcceptWinQ0 t powD mS
    mS2 x0 uLo uHi (n1sLimConst t d) (Nat.mod (Nat.mul x0 32) powD) (Nat.div uLo 32)

/-- Checks `uHi ≤ uLo` before sharing `(powD, x0)` (`0` `@Nat.rec`s). -/
def n1sCntBounds (t : Norm1sTier) (d mS mS2 powD uLo uHi : ℕ) : ℕ := bif Nat.ble uHi uLo then
    uLo else n1sCntX0 t d mS mS2 powD uLo uHi (Nat.mod mS powD)

/-- Computes `(uLo, uHi)` once `mS4 = 4 * mS` is shared (`0` `@Nat.rec`s). -/
def n1sCntMS4 (t : Norm1sTier) (d mS mS2 rhs mS4 : ℕ) : ℕ :=
  n1sCntBounds t d mS mS2 (n1sPowD t)
    (n1sMinFast (n1sPow2K t) (Nat.div (Nat.sub (Nat.add rhs mS2) (n1sWindowBound t)) mS4))
    (n1sMinFast (n1sPow2K t) (Nat.div (Nat.add (Nat.add rhs mS2) (n1sWindowBound t)) mS4))

/-- Normalized `(t, d, mS, mS2)` accept-count evaluator sharing leaf `BVar` pointers (`0`
  `@Nat.rec`s). -/
def n1sCntDMS (t : Norm1sTier) (d mS mS2 : ℕ) : ℕ :=
  n1sCntMS4 t d mS mS2 (n1sRhsConst t d) (Nat.add mS2 mS2)

/-- Shares `mS` across `mS2 = mS + mS` (`0` `@Nat.rec`s). -/
def n1sCntMS (t : Norm1sTier) (d mS : ℕ) : ℕ := n1sCntDMS t d mS (Nat.add mS mS)

/-- Stage `e` of `n1sFastAcceptCountK` sharing `e` (`0` `let`s, `0` `@Nat.rec`s). -/
def n1sFastCntE (t : Norm1sTier) (mu s e : ℕ) : ℕ := bif Nat.blt e (Nat.mul 2 mu) then 0 else
    n1sCntMS t (Nat.sub e (Nat.mul 2 mu)) (Nat.mul s (n1sPow2Sub17Fast e))

/-- Zero-recursor unboxed `ℕ` evaluator of `norm1sAcceptCountK t mu s` (`0` `let`s, `0`
  `@Nat.rec`s). -/
def n1sFastAcceptCountK (t : Norm1sTier) (mu s : ℕ) : ℕ := n1sFastCntE t mu s (n1sClz18Fast s)

private theorem n1s_natSum_zero (g : ℕ → ℕ) : natSum 0 g = 0 := rfl

private theorem n1s_natSum_succ (k : ℕ) (g : ℕ → ℕ) : natSum (k + 1) g = natSum k g + g k := rfl

theorem n1sSumTailLe5_eq (n powD x0 mS2 baseH lim pHi : ℕ) : n1sSumTailLe5 n powD x0 mS2 baseH
    lim pHi = natSum n (fun i ↦ n1sScanAt powD x0 mS2 baseH lim (pHi + i)) := by
  unfold n1sSumTailLe5 n1sScanSubStep
  simp only [n1s_cond_beq_eq, n1sSumTail_eq, n1s_nat_add_eq]
  split_ifs with h0 h1 h2 h3 h4 h5 <;>
    first
    | rfl
    | (subst_vars
       simp only [n1s_natSum_succ, n1s_natSum_zero, Nat.add_zero, Nat.zero_add, Nat.add_assoc])

theorem n1sMax2Fast_eq_max (a b : ℕ) : n1sMax2Fast a b = max a b := by
  unfold n1sMax2Fast
  simp only [n1s_nat_add_eq, n1s_nat_sub_eq]
  omega

theorem n1sCondTerm_le (powD x : ℕ) (hx : x ≤ powD) (b : Bool) :
    (bif b then x else powD - x) ≤ powD := by
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> omega

theorem n1sRemLow5_le_five_mul {powD x0 : ℕ} (hx0 : x0 < powD) (r : ℕ) :
    n1sRemLow5 powD x0 r ≤ 5 * powD := by
  have hp : 0 < powD := by omega
  have hx1 : n1sStepX powD x0 < powD := by
    rw [n1sStepX_eq_mul_two_mod hx0]; exact Nat.mod_lt _ hp
  have hx2 : n1sStepX powD (n1sStepX powD x0) < powD := by
    rw [n1sStepX_eq_mul_two_mod hx1]; exact Nat.mod_lt _ hp
  have hx3 : n1sStepX powD (n1sStepX powD (n1sStepX powD x0)) < powD := by
    rw [n1sStepX_eq_mul_two_mod hx2]; exact Nat.mod_lt _ hp
  have hx4 : n1sStepX powD (n1sStepX powD (n1sStepX powD (n1sStepX powD x0))) < powD := by
    rw [n1sStepX_eq_mul_two_mod hx3]; exact Nat.mod_lt _ hp
  unfold n1sRemLow5
  dsimp only
  have ht0 := n1sCondTerm_le powD x0 hx0.le (Nat.beq (r % 2) 0)
  have ht1 := n1sCondTerm_le powD _ hx1.le (Nat.beq ((r / 2) % 2) 0)
  have ht2 := n1sCondTerm_le powD _ hx2.le (Nat.beq (((r / 2) / 2) % 2) 0)
  have ht3 := n1sCondTerm_le powD _ hx3.le (Nat.beq ((((r / 2) / 2) / 2) % 2) 0)
  have ht4 := n1sCondTerm_le powD _ hx4.le (Nat.beq (((((r / 2) / 2) / 2) / 2) % 2) 0)
  omega

theorem n1s_natSum_eq_zero {n : ℕ} {g : ℕ → ℕ} (h : ∀ i < n, g i = 0) : natSum n g = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
      change natSum k g + g k = 0
      rw [ih (fun i hi ↦ h i (by omega)), h k (by omega)]

theorem n1s_natSum_eq_len {n : ℕ} {g : ℕ → ℕ} (h : ∀ i < n, g i = 1) : natSum n g = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      change natSum k g + g k = k + 1
      rw [ih (fun i hi ↦ h i (by omega)), h k (by omega)]

theorem n1s_natSum_add_split (m n : ℕ) (g : ℕ → ℕ) :
    natSum (m + n) g = natSum m g + natSum n (fun i ↦ g (m + i)) := by
  induction n with
  | zero => simp [natSum]
  | succ k ih =>
      rw [← Nat.add_assoc]
      change natSum (m + k) g + g (m + k) = natSum m g + (natSum k (fun i ↦ g (m + i)) + g (m + k))
      rw [ih, Nat.add_assoc]

theorem n1s_natSum_congr_lt {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) :
    natSum n f = natSum n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      change natSum k f + f k = natSum k g + g k
      rw [ih (fun i hi ↦ h i (by omega)), h k (by omega)]

theorem n1sScanConstHi_eq {powD x0 mS2 : ℕ} (hx0 : x0 < powD) (hmS2 : 0 < mS2)
    (mS lim h a b : ℕ) :
    n1sScanConstHi powD x0 mS2 mS lim h a b =
      natSum (b - a) (fun i ↦
        let u := a + i
        bif Nat.ble (mS2 * u + mS + (n1sRemLow5 powD x0 (u % 32) + h)) lim then 1 else 0) := by
  unfold n1sScanConstHi n1sScanFromBase n1sScanFromPHi n1sScanFromBounds
  rw [n1s_cond_ble_eq]
  split_ifs with hba
  · have h0 : b - a = 0 := by omega
    rw [h0]; rfl
  · rw [n1sSumTailLe5_eq]
    unfold n1sScanAt
    simp only [n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq, n1s_nat_div_eq, n1s_nat_mod_eq,
      n1s_one_sub_sub_eq_ble, n1sMinFast_eq_min, n1sMax2Fast_eq_max]
    rw [n1s_cond_blt_eq]
    set baseH := mS + h
    split_ifs with hlim
    · symm
      refine n1s_natSum_eq_zero fun i _ ↦ ?_
      rw [n1s_cond_ble_eq, n1s_lat_if_neg (by dsimp [baseH] at hlim; omega)]
    · set pRaw := (lim + mS2 - (baseH + 5 * powD)) / mS2
      set pHi := min b (max a pRaw)
      set sHi := max pHi (min b ((lim - baseH) / mS2 + 1))
      have ha_le_pHi : a ≤ pHi := le_min (by omega) (le_max_left _ _)
      have hpHi_le_sHi : pHi ≤ sHi := le_max_left _ _
      have hsHi_le_b : sHi ≤ b := max_le (min_le_left _ _) (min_le_left _ _)
      let g : ℕ → ℕ := fun i ↦
        let u := a + i
        bif Nat.ble (mS2 * u + mS + (n1sRemLow5 powD x0 (u % 32) + h)) lim then 1 else 0
      have hlen : b - a = (pHi - a) + (sHi - pHi) + (b - sHi) := by omega
      conv_rhs => rw [show (fun i ↦ _) = g from rfl, hlen]
      rw [n1s_natSum_add_split ((pHi - a) + (sHi - pHi)) (b - sHi) g,
        n1s_natSum_add_split (pHi - a) (sHi - pHi) g]
      have hseg1 : natSum (pHi - a) g = pHi - a := by
        refine n1s_natSum_eq_len fun i hi ↦ ?_
        have hu_lt_pHi : a + i < pHi := by omega
        have hu_lt_max : a + i < max a pRaw := lt_of_lt_of_le hu_lt_pHi (min_le_right _ _)
        have hu_lt_pRaw : a + i < pRaw := by omega
        have hmul_le : (a + i + 1) * mS2 ≤ lim + mS2 - (baseH + 5 * powD) :=
          (Nat.le_div_iff_mul_le hmS2).mp (by omega)
        have hmul_pos : 0 < (a + i + 1) * mS2 := Nat.mul_pos (by omega) hmS2
        have hprod_expand : (a + i + 1) * mS2 = mS2 * (a + i) + mS2 := by ring
        rw [hprod_expand] at hmul_le hmul_pos
        have h5_le : n1sRemLow5 powD x0 ((a + i) % 32) ≤ 5 * powD :=
          n1sRemLow5_le_five_mul hx0 _
        dsimp only [g]
        rw [n1s_cond_ble_eq, n1s_lat_if_pos]
        dsimp [baseH] at hmul_le
        omega
      have hseg3 : natSum (b - sHi) (fun i ↦ g ((pHi - a) + (sHi - pHi) + i)) = 0 := by
        refine n1s_natSum_eq_zero fun i hi ↦ ?_
        have hu_eq : a + ((pHi - a) + (sHi - pHi) + i) = sHi + i := by omega
        have hsHi_le_u : sHi ≤ sHi + i := by omega
        have hu_lt_b : sHi + i < b := by omega
        have hmin_le : min b ((lim - baseH) / mS2 + 1) ≤ sHi + i :=
          le_trans (le_max_right _ _) hsHi_le_u
        have hdiv_lt : (lim - baseH) / mS2 < sHi + i := by omega
        have hlt_mul : lim - baseH < (sHi + i) * mS2 :=
          (Nat.div_lt_iff_lt_mul hmS2).mp hdiv_lt
        have hprod_comm : (sHi + i) * mS2 = mS2 * (sHi + i) := Nat.mul_comm _ _
        rw [hprod_comm] at hlt_mul
        dsimp only [g]
        rw [hu_eq, n1s_cond_ble_eq, n1s_lat_if_neg]
        dsimp [baseH] at hlt_mul hlim
        omega
      have hseg2 : natSum (sHi - pHi) (fun i ↦ bif Nat.ble (mS2 * (pHi + i) + (baseH +
          n1sRemLow5Fast powD x0 ((pHi + i) % 32))) lim then 1 else 0) = natSum (sHi - pHi)
          (fun i ↦ g ((pHi - a) + i)) := by
        refine n1s_natSum_congr_lt fun i _ ↦ ?_
        have hu_eq : a + ((pHi - a) + i) = pHi + i := by omega
        dsimp only [g]
        rw [hu_eq, n1sRemLow5Fast_eq hx0]
        congr 2
        dsimp only [baseH]
        omega
      rw [hseg1, hseg3, Nat.add_zero, hseg2]

theorem n1sFastAcceptCountK_eq_spec (t : Norm1sTier) (mu : ℕ) {s : ℕ} (hs0 : 0 < s)
    (hs18 : s < 262144) : n1sFastAcceptCountK t mu s = n1sSpecAcceptCountK t mu s := by
  have hpowD_pos : 0 < n1sPowD t := by cases t <;> decide
  have he_eq : n1sClz18Fast s = clz18Log2 s := n1sClz18Fast_eq_clz18Log2 hs18
  have he_le : n1sClz18Fast s ≤ 17 := he_eq ▸ clz18Log2_le_17 s
  have hp17_pos : 0 < n1sPow2Sub17Fast (n1sClz18Fast s) := by
    rw [n1sPow2Sub17Fast_eq he_le]; exact Nat.two_pow_pos _
  have hmS_pos : 0 < s * n1sPow2Sub17Fast (n1sClz18Fast s) := Nat.mul_pos hs0 hp17_pos
  have hmS2_pos : 0 < s * n1sPow2Sub17Fast (n1sClz18Fast s) + s *
    n1sPow2Sub17Fast (n1sClz18Fast s) := by
    omega
  have hx0 : (s * n1sPow2Sub17Fast (n1sClz18Fast s)) % n1sPowD t < n1sPowD t :=
    Nat.mod_lt _ hpowD_pos
  unfold n1sFastAcceptCountK n1sFastCntE n1sCntMS n1sCntDMS n1sCntMS4 n1sCntBounds
    n1sSpecAcceptCountK
  dsimp only
  simp only[n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq, n1s_nat_div_eq, n1s_nat_mod_eq]
  rcases Bool.dichotomy (Nat.blt (n1sClz18Fast s) (2 * mu)) with hblt | hblt <;>
    simp only [hblt, Bool.cond_true, Bool.cond_false]
  set mS := s * n1sPow2Sub17Fast (n1sClz18Fast s)
  set mS2 := mS + mS
  set powD := n1sPowD t
  set x0 := mS % powD
  set d := n1sClz18Fast s - 2 * mu
  set uLo := n1sMinFast (n1sPow2K t) ((n1sRhsConst t d + mS2 - n1sWindowBound t) / (mS2 + mS2))
  set uHi := n1sMinFast (n1sPow2K t) ((n1sRhsConst t d + mS2 + n1sWindowBound t) / (mS2 + mS2))
  rcases Bool.dichotomy (Nat.ble uHi uLo) with hble | hble
  · simp only [hble, Bool.cond_false]
    have hnot_le : ¬(uHi ≤ uLo) := by
      rw [← Nat.ble_eq, hble]; decide
    have huLo_lt_uHi : uLo < uHi := by omega
    unfold n1sCntX0 n1sAcceptWinQ0 n1sAcceptWindowFromQ0
    simp only [n1s_nat_add_eq, n1s_nat_mul_eq, n1s_nat_div_eq, n1s_nat_mod_eq]
    rw [← n1sStep5_eq_mod hx0]
    set x5 := n1sStep5 powD x0
    set lim := n1sLimConst t d
    set q0 := uLo / 32
    set h0 := n1sRemHi5 t x5 q0
    set bnd := (q0 + 1) * 32
    rw [n1s_cond_ble_eq]
    split_ifs with hbnd
    · rw [n1sScanConstHi_eq hx0 hmS2_pos]
      congr 1
      refine n1s_natSum_congr_lt fun i hi ↦ ?_
      have hq : (uLo + i) / 32 = q0 := by dsimp [q0, bnd] at hbnd ⊢; omega
      dsimp only
      rw [n1s_cond_beq_eq, n1s_lat_if_pos hq]
    · have huLo_le_bnd : uLo ≤ bnd := by dsimp [q0, bnd]; omega
      have hbnd_lt_uHi : bnd < uHi := by omega
      have hne_top : (uHi - 1) / 32 ≠ q0 := by dsimp [q0, bnd] at hbnd_lt_uHi ⊢; omega
      rw [n1sScanConstHi_eq hx0 hmS2_pos, n1sScanConstHi_eq hx0 hmS2_pos]
      congr 1
      have hsplit : uHi - uLo = (bnd - uLo) + (uHi - bnd) := by omega
      conv_rhs => rw [hsplit, n1s_natSum_add_split]
      congr 1
      · refine n1s_natSum_congr_lt fun i hi ↦ ?_
        have hq : (uLo + i) / 32 = q0 := by dsimp [q0, bnd] at hi ⊢; omega
        dsimp only
        rw [n1s_cond_beq_eq, n1s_lat_if_pos hq]
      · refine n1s_natSum_congr_lt fun i hi ↦ ?_
        have hu_eq : uLo + (bnd - uLo + i) = bnd + i := by omega
        have hq_ne : (bnd + i) / 32 ≠ q0 := by dsimp [q0, bnd]; omega
        dsimp only
        rw [hu_eq, n1s_cond_beq_eq, n1s_lat_if_neg hq_ne, n1s_cond_beq_eq, n1s_lat_if_neg hne_top]
  · simp only [hble, Bool.cond_true]

theorem n1s_natSum_cond_eq_card_Ico (uLo len : ℕ) (P : ℕ → Bool) :
    natSum len (fun i ↦ bif P (uLo + i) then 1 else 0) =
      ((Finset.Ico uLo (uLo + len)).filter (fun u ↦ P u = true)).card := by
  induction len with
  | zero => simp [natSum]
  | succ k ih =>
      have hIco : Finset.Ico uLo (uLo + (k + 1)) =
          insert (uLo + k) (Finset.Ico uLo (uLo + k)) := by
        ext u
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      have hnot : uLo + k ∉ (Finset.Ico uLo (uLo + k)).filter (fun u ↦ P u = true) := by
        simp [Finset.mem_Ico]
      change natSum k (fun i ↦ bif P (uLo + i) then 1 else 0) +
          (bif P (uLo + k) then 1 else 0) = _
      rw [ih, hIco, Finset.filter_insert]
      cases P (uLo + k) <;> simp [hnot]

theorem n1s_hwProd_lt_iff (t : Norm1sTier) {d mS uK : ℕ} (hd : d < 18) (hmS : mS < 2 ^ 18)
    (huK : uK < 2 ^ t.kBits) : norm1sHwProd t.kBits t.dCut mS uK < accThr t.kBits t.dCut d ↔
    (mS + mS) * uK + mS + n1sRemLoop (n1sPowD t) t.dCut (mS % n1sPowD t) uK 0 ≤ n1sLimConst t
    d := by
  have hthr_pos := n1s_accThr_pos t hd
  have hid := norm1sHwProd_int_eq t hmS huK
  have hrem := n1sRemLoop_eq_deltaNorm1sAux t.dCut mS uK
  have hrhs := n1sRhsConst_int_eq t hd
  have hlim := n1sLimConst_int_eq t hd
  have hpow_pos : (0 : ℤ) < (2 ^ t.dCut : ℤ) := by positivity
  rw [n1sPowD_eq]
  set remNat := n1sRemLoop (2 ^ t.dCut) t.dCut (mS % 2 ^ t.dCut) uK 0
  set P := norm1sHwProd t.kBits t.dCut mS uK
  set thr := accThr t.kBits t.dCut d
  set wc2 := wc2TrueNat t.kBits t.dCut
  have hchain1 : P < thr ↔ (2 * (P : ℤ) - (wc2 : ℤ)) ≤ 2 * (thr : ℤ) - 2 - (wc2 : ℤ) := by
    omega
  have hchain2 : ((2 * (P : ℤ) - (wc2 : ℤ)) ≤ 2 * (thr : ℤ) - 2 - (wc2 : ℤ)) ↔ ((2 * (P : ℤ) -
      (wc2 : ℤ)) * (2 ^ t.dCut : ℤ) ≤ (2 * (thr : ℤ) - 2 - (wc2 : ℤ)) * (2 ^ t.dCut : ℤ)) :=
      ⟨fun h ↦ mul_le_mul_of_nonneg_right h hpow_pos.le, fun h ↦ le_of_mul_le_mul_right h
      hpow_pos⟩
  rw [hchain1, hchain2, hid, ← hrhs]
  unfold deltaNorm1s
  rw [← hrem]
  have hlin : (4 * (mS : ℤ) * (uK : ℤ) + (2 * (mS : ℤ) + (2 * (remNat : ℤ) - (t.dCut : ℤ) * (2
      ^ t.dCut : ℤ))) ≤ (n1sRhsConst t d : ℤ)) ↔ 2 * (((mS + mS) * uK + mS + remNat : ℕ) : ℤ)
      ≤ 2 * (n1sLimConst t d : ℤ) := by
    rw [hlim]
    push_cast
    constructor <;> intro h <;> linarith
  rw [hlin]
  constructor
  · intro h
    have h' : (((mS + mS) * uK + mS + remNat : ℕ) : ℤ) ≤ (n1sLimConst t d : ℤ) := by omega
    exact_mod_cast h'
  · intro h
    have h' : (((mS + mS) * uK + mS + remNat : ℕ) : ℤ) ≤ (n1sLimConst t d : ℤ) := by
      exact_mod_cast h
    linarith

theorem n1sSpecAcceptCountK_eq_norm1sAcceptCountK (t : Norm1sTier) {mu s : ℕ} (hs0 : 0 < s)
    (hs18 : s < 262144) : n1sSpecAcceptCountK t mu s = norm1sAcceptCountK t mu s := by
  have he_eq : n1sClz18Fast s = clz18Log2 s := n1sClz18Fast_eq_clz18Log2 hs18
  have he_le : clz18Log2 s ≤ 17 := clz18Log2_le_17 s
  unfold n1sSpecAcceptCountK norm1sAcceptCountK
  dsimp only
  rw [he_eq, n1s_cond_blt_eq]
  by_cases hmu : clz18Log2 s < 2 * mu
  · have hnot : ¬(2 * mu ≤ clz18Log2 s) := by omega
    simp [hmu, hnot]
  · have hge : 2 * mu ≤ clz18Log2 s := by omega
    simp only [hmu, hge, ite_false, ite_true]
    rw [n1sPow2Sub17Fast_eq he_le,
      show s * 2 ^ (17 - clz18Log2 s) = norm1sMant18 s from rfl]
    set mS := norm1sMant18 s
    obtain ⟨hmLo, hmHi⟩ := norm1sMant18_bounds hs0 (show s < 2 ^ 18 by norm_num; exact hs18)
    set d := clz18Log2 s - 2 * mu
    have hd_lt : d < 18 := by omega
    have hd5 : 5 ≤ t.dCut := n1s_five_le_dCut t
    rw [n1sPowD_eq, n1sPow2K_eq, n1sMinFast_eq_min, n1sMinFast_eq_min, n1s_cond_ble_eq]
    set powD := 2 ^ t.dCut
    set bNat := n1sWindowBound t
    have hb_eq_z : (bNat : ℤ) = (t.dCut : ℤ) * (powD : ℤ) := by
      dsimp [bNat, powD]
      rw [n1sWindowBound_eq]
      push_cast
      rfl
    have hb_abs_le : ∀ uK : ℕ, |deltaNorm1sAux t.dCut mS uK t.dCut| ≤ (bNat : ℤ) := by
      intro uK
      have h1 := deltaNorm1sAux_abs_le t.dCut mS uK t.dCut
      have h2 := two_mul_mod_add_deltaAbsSum_le mS t.dCut
      have hnn : (0 : ℤ) ≤ 2 * ((mS % 2 ^ t.dCut : ℕ) : ℤ) := by positivity
      dsimp [powD] at hb_eq_z
      linarith
    have hb_le_max : bNat ≤ 4718592 := n1sWindowBound_le t
    have hmLo_num : 131072 ≤ mS := by norm_num at hmLo; exact hmLo
    set mS2 := mS + mS
    set mS4 := mS2 + mS2
    have hmS4_eq : mS4 = 4 * mS := by dsimp [mS4, mS2]; omega
    have hmS4_ge : 524288 ≤ mS4 := by omega
    set rhs := n1sRhsConst t d
    have hrhs_ge : bNat ≤ rhs + mS2 := by
      have h := n1sRhsConst_ge_pow24 t hd_lt
      omega
    set uLo := min (2 ^ t.kBits) ((rhs + mS2 - bNat) / mS4)
    set uHi := min (2 ^ t.kBits) ((rhs + mS2 + bNat) / mS4)
    have huLo_le_uHi : uLo ≤ uHi := min_le_min le_rfl (Nat.div_le_div_right (by omega))
    have huHi_le_uLo18 : uHi ≤ uLo + 18 := by
      set X := rhs + mS2 - bNat
      have hX_sum : rhs + mS2 + bNat = X + 2 * bNat := by dsimp [X]; omega
      have hdiv_mod := Nat.div_add_mod X mS4
      have hmod_lt : X % mS4 < mS4 := Nat.mod_lt X (by omega)
      have h2b : 2 * bNat ≤ 18 * mS4 := by omega
      have hlt_mul : rhs + mS2 + bNat < (X / mS4 + 19) * mS4 := by
        rw [hX_sum]
        nlinarith
      have hdiv_lt : (rhs + mS2 + bNat) / mS4 < X / mS4 + 19 :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < mS4)).mpr hlt_mul
      dsimp only [X] at hdiv_lt
      dsimp only [uLo, uHi]
      omega
    set thr := accThr t.kBits t.dCut d
    set S_K := (Finset.range (2 ^ t.kBits)).filter (fun uK ↦
      norm1sHwProd t.kBits t.dCut mS uK < thr)
    have hRange_sub : Finset.range uLo ⊆ S_K := by
      intro uK huK
      rw [Finset.mem_range] at huK
      have huK_lt : uK < 2 ^ t.kBits := lt_of_lt_of_le huK (min_le_left _ _)
      have huK_div : uK < (rhs + mS2 - bNat) / mS4 := lt_of_lt_of_le huK (min_le_right _ _)
      have hmul_nat : (uK + 1) * (4 * mS) ≤ rhs + mS2 - bNat := by
        rw [← hmS4_eq]
        exact (Nat.le_div_iff_mul_le (by omega : 0 < mS4)).mp (by omega)
      have hmul_z : 4 * (mS : ℤ) * ((uK : ℤ) + 1) ≤ (rhs : ℤ) + 2 * (mS : ℤ) - (bNat : ℤ) := by
        have hcast : (((uK + 1) * (4 * mS) : ℕ) : ℤ) ≤ ((rhs + mS2 - bNat : ℕ) : ℤ) := by
          exact_mod_cast hmul_nat
        rw [Nat.cast_sub hrhs_ge, Nat.cast_add] at hcast
        dsimp [mS2] at hcast
        linarith
      have hid := norm1sHwProd_int_eq t hmHi huK_lt
      have habs := (abs_le.mp (hb_abs_le uK)).2
      have hrhs_z := n1sRhsConst_int_eq t hd_lt
      have hpow_pos : (0 : ℤ) < (2 ^ t.dCut : ℤ) := by positivity
      have hprod_le : ((2 * norm1sHwProd t.kBits t.dCut mS uK : ℤ) - (wc2TrueNat t.kBits
          t.dCut : ℤ)) * (2 ^ t.dCut : ℤ) ≤
          (2 * (thr : ℤ) - 2 - (wc2TrueNat t.kBits t.dCut : ℤ)) * (2 ^ t.dCut : ℤ) := by
        unfold deltaNorm1s at hid
        linarith
      have h2p := le_of_mul_le_mul_right hprod_le hpow_pos
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨huK_lt, by omega⟩
    have hSK_sub : S_K ⊆ Finset.range uHi := by
      intro uK huK
      rw [Finset.mem_filter, Finset.mem_range] at huK
      rcases huK with ⟨huK_lt, hlt_thr⟩
      have hid := norm1sHwProd_int_eq t hmHi huK_lt
      have habs := (abs_le.mp (hb_abs_le uK)).1
      have hrhs_z := n1sRhsConst_int_eq t hd_lt
      have hpow_pos : (0 : ℤ) < (2 ^ t.dCut : ℤ) := by positivity
      have h2p : (2 * norm1sHwProd t.kBits t.dCut mS uK : ℤ) - (wc2TrueNat t.kBits t.dCut : ℤ) ≤
          2 * (thr : ℤ) - 2 - (wc2TrueNat t.kBits t.dCut : ℤ) := by omega
      have hprod_le := mul_le_mul_of_nonneg_right h2p hpow_pos.le
      have hmul_z : 4 * (mS : ℤ) * ((uK : ℤ) + 1) ≤ (rhs : ℤ) + 2 * (mS : ℤ) + (bNat : ℤ) := by
        unfold deltaNorm1s at hid
        linarith
      have hmul_nat : (uK + 1) * mS4 ≤ rhs + mS2 + bNat := by
        rw [hmS4_eq]
        have hcast : (((uK + 1) * (4 * mS) : ℕ) : ℤ) ≤ ((rhs + mS2 + bNat : ℕ) : ℤ) := by
          dsimp [mS2]; linarith
        exact_mod_cast hcast
      have huK_div : uK < (rhs + mS2 + bNat) / mS4 := by
        have hle_d : uK + 1 ≤ (rhs + mS2 + bNat) / mS4 :=
          (Nat.le_div_iff_mul_le (by omega)).mpr hmul_nat
        omega
      rw [Finset.mem_range]
      exact lt_min huK_lt huK_div
    split_ifs with hle_hi
    · have heq_u : uLo = uHi := le_antisymm huLo_le_uHi hle_hi
      have hSK_eq : S_K = Finset.range uLo :=
        Finset.Subset.antisymm (heq_u ▸ hSK_sub) hRange_sub
      rw [hSK_eq, Finset.card_range]
    · have hlt_u : uLo < uHi := Nat.lt_of_not_ge hle_hi
      have hpart : S_K = Finset.range uLo ∪
          (Finset.Ico uLo uHi).filter (fun uK ↦ norm1sHwProd t.kBits t.dCut mS uK < thr) := by
        ext uK
        simp only [Finset.mem_union, Finset.mem_range, Finset.mem_filter, Finset.mem_Ico]
        constructor
        · intro hmem
          have hhi : uK < uHi := Finset.mem_range.mp (hSK_sub hmem)
          by_cases hlo : uK < uLo
          · exact Or.inl hlo
          · exact Or.inr ⟨⟨by omega, hhi⟩, (Finset.mem_filter.mp hmem).2⟩
        · rintro (hlo | ⟨⟨_, _⟩, hthr_u⟩)
          · exact hRange_sub (Finset.mem_range.mpr hlo)
          · have huK_lt : uK < 2 ^ t.kBits := lt_of_lt_of_le (by assumption) (min_le_left _ _)
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr huK_lt, hthr_u⟩
      have hdisj : Disjoint (Finset.range uLo)
          ((Finset.Ico uLo uHi).filter (fun uK ↦ norm1sHwProd t.kBits t.dCut mS uK < thr)) := by
        rw [Finset.disjoint_left]
        intro uK h1 h2
        rw [Finset.mem_range] at h1
        rw [Finset.mem_filter, Finset.mem_Ico] at h2
        omega
      rw [hpart, Finset.card_union_of_disjoint hdisj, Finset.card_range]
      congr 1
      set x5 := n1sStep5 powD (mS % powD)
      have hx5_lt : x5 < 2 ^ t.dCut := by
        have hm0 : mS % powD < powD := Nat.mod_lt mS (Nat.two_pow_pos t.dCut)
        dsimp [x5]
        rw [n1sStep5_eq_mod hm0]
        exact Nat.mod_lt _ (Nat.two_pow_pos t.dCut)
      set q0 := uLo / 32
      set h0 := n1sRemHi5 t x5 q0
      set h1 := bif Nat.beq ((uHi - 1) / 32) q0 then h0 else n1sRemHi5 t x5 (q0 + 1)
      set lim := n1sLimConst t d
      let P : ℕ → Bool := fun u ↦ Nat.ble (mS2 * u + mS + (n1sRemLow5 powD (mS % powD) (u %
          32) + bif Nat.beq (u / 32) q0 then h0 else h1)) lim
      change natSum (uHi - uLo) (fun i ↦ bif P (uLo + i) then 1 else 0) = _
      rw [n1s_natSum_cond_eq_card_Ico uLo (uHi - uLo) P,
        show uLo + (uHi - uLo) = uHi by omega]
      dsimp only [P]
      congr 1
      refine Finset.filter_congr fun u hu ↦ ?_
      rw [Finset.mem_Ico] at hu
      have hu_lt_K : u < 2 ^ t.kBits := lt_of_lt_of_le hu.2 (min_le_left _ _)
      have hhiRem : (bif Nat.beq (u / 32) q0 then h0 else h1) = n1sRemLoop powD (t.dCut - 5)
          x5 (u / 32) 0 := by
        have hq_cases : u / 32 = q0 ∨ (u / 32 = q0 + 1 ∧ (uHi - 1) / 32 ≠ q0) := by
          dsimp [q0]; omega
        rw [n1s_cond_beq_eq]
        rcases hq_cases with hq0 | ⟨hq1, hne0⟩
        · rw [n1s_lat_if_pos hq0]
          dsimp [h0, powD]
          rw [n1sRemHi5_eq t hx5_lt, hq0]
        · have hne_u : u / 32 ≠ q0 := by omega
          rw [n1s_lat_if_neg hne_u]
          dsimp [h1, powD]
          rw [n1s_cond_beq_eq, n1s_lat_if_neg hne0, n1sRemHi5_eq t hx5_lt, hq1]
      have hrem_tot :
          n1sRemLow5 powD (mS % powD) (u % 32) + (bif Nat.beq (u / 32) q0 then h0 else h1) =
            n1sRemLoop powD t.dCut (mS % powD) u 0 := by
        rw [hhiRem, ← n1sRemLoop_split5 hd5 powD (mS % powD) u]
      rw [hrem_tot, Nat.ble_eq]
      dsimp only [powD, mS2, lim, thr]
      rw [← n1sPowD_eq t]
      exact (n1s_hwProd_lt_iff t hd_lt hmHi hu_lt_K).symm

theorem n1sFastAcceptCountK_eq_norm1sAcceptCountK (t : Norm1sTier) {mu s : ℕ} (hs0 : 0 < s)
    (hs18 : s < 262144) : n1sFastAcceptCountK t mu s = norm1sAcceptCountK t mu s :=
    (n1sFastAcceptCountK_eq_spec t mu hs0 hs18).trans
    (n1sSpecAcceptCountK_eq_norm1sAcceptCountK t hs0 hs18)

/- ## Section 4: `m_whnf_cache`-Memoized Per-`(Tier, Shell)` Error and 3D Alias Bound -/

/-- Evaluated `LitVal` body of `n1sRawErr` (`0` `let`s, `0` inline lambdas). -/
def n1sRawErrAt (t : Norm1sTier) (mu sv : ℕ) : ℕ := bif Nat.beq sv 0 then 0 else n1sNatDist
    (Nat.mul (n1sPow2Sub38 t) (n1sFastAcceptCountK t mu sv)) (Nat.div (n1sCRadFast mu) sv)

/-- Exact integer kernel discrepancy `|2^(38 - K) * cnt - ⌊cRad(mu) / s⌋|` for `0 < s < 2 ^ 18`. -/
def n1sRawErr (t : Norm1sTier) (mu s : ℕ) : ℕ := n1sRawErrAt t mu s

theorem n1s_rec_step_zero_add (f : ℕ → ℕ) (s : ℕ) :
    @Nat.rec (fun _ ↦ ℕ) 0 (fun v _ ↦ Nat.add 0 (f v)) (Nat.add 1 s) = f s := by
  change @Nat.rec (fun _ ↦ ℕ) 0 (fun v _ ↦ 0 + f v) (1 + s) = f s
  rw [Nat.one_add]
  exact Nat.zero_add (f s)

/-- Closed `@Nat.rec` step memoizing `n1sRawErrAt t mu v` in `m_whnf_cache` when `t` and `mu` are
  closed. -/
def n1sMemoStep (t : Norm1sTier) (mu v _ : ℕ) : ℕ := Nat.add 0 (n1sRawErrAt t mu v)

/-- Closed `0`-allocation CBV error lookup for `(t, mu)` at squared norm `x`. -/
def n1sErrCached (t : Norm1sTier) (mu x : ℕ) : ℕ :=
  @Nat.rec (fun _ ↦ ℕ) 0 (n1sMemoStep t mu) (Nat.add 1 x)

theorem n1sErrCached_eq_n1sRawErr (t : Norm1sTier) {mu : ℕ} (_ : mu ≤ 6) (s : ℕ) :
    n1sErrCached t mu s = n1sRawErr t mu s := n1s_rec_step_zero_add (n1sRawErrAt t mu) s
/-- One-axis squared-alias maximum with period `2 * 127 + 1 = 255` (`{0}` at `0`, `{x^2, (255 -
  x)^2}` at `x > 0`). -/
def n1sAxisAliasMax (x : ℕ) (cont : ℕ → ℕ) (base : ℕ) : ℕ := bif Nat.beq x 0 then cont base
    else max2Nat (cont (base + x * x)) (cont (base + (255 - x) * (255 - x)))

/-- Symmetric 3-axis period-`255` alias maximum over `modFold3D 127` preimages in `box3D 254`. -/
def n1sAliasMax3 (evalS : ℕ → ℕ) (a b c : ℕ) : ℕ :=
  n1sAxisAliasMax a (n1sAxisAliasMax b (n1sAxisAliasMax c evalS)) 0

theorem n1s_max2Nat_eq_max (a b : ℕ) : max2Nat a b = max a b := by
  unfold max2Nat
  rw [n1s_cond_ble_eq]
  split_ifs with h
  · exact (max_eq_right h).symm
  · exact (max_eq_left (by omega)).symm

theorem n1sAxisAliasMax_congr {x : ℕ} {c₁ c₂ : ℕ → ℕ} (h : ∀ s, c₁ s = c₂ s) (base : ℕ) :
    n1sAxisAliasMax x c₁ base = n1sAxisAliasMax x c₂ base := by
  unfold n1sAxisAliasMax
  simp only [n1s_cond_beq_eq]
  split_ifs <;> simp [h]

theorem n1sAxisAliasMax_comm (x y : ℕ) (cont : ℕ → ℕ) (base : ℕ) : n1sAxisAliasMax x
    (n1sAxisAliasMax y cont) base = n1sAxisAliasMax y (n1sAxisAliasMax x cont) base := by
  unfold n1sAxisAliasMax
  simp only [n1s_cond_beq_eq, n1s_max2Nat_eq_max]
  split_ifs
  · rfl
  · rfl
  · rfl
  · have hab (p q : ℕ) : base + p + q = base + q + p := by omega
    rw [hab (x * x) (y * y), hab (x * x) ((255 - y) * (255 - y)),
      hab ((255 - x) * (255 - x)) (y * y), hab ((255 - x) * (255 - x)) ((255 - y) * (255 - y))]
    omega

theorem n1sAliasMax3_swap12 (evalS : ℕ → ℕ) (a b c : ℕ) : n1sAliasMax3 evalS a b c =
    n1sAliasMax3 evalS b a c := n1sAxisAliasMax_comm a b (n1sAxisAliasMax c evalS) 0

theorem n1sAliasMax3_swap23 (evalS : ℕ → ℕ) (a b c : ℕ) : n1sAliasMax3 evalS a b c =
    n1sAliasMax3 evalS a c b := n1sAxisAliasMax_congr (n1sAxisAliasMax_comm b c evalS) 0

theorem n1s_le_axisAliasMax {x dx : ℕ} (hx : if x = 0 then dx = 0 else dx = x * x ∨ dx = (255
    - x) * (255 - x)) (cont : ℕ → ℕ) (base : ℕ) : cont (base + dx) ≤ n1sAxisAliasMax x cont
    base := by
  unfold n1sAxisAliasMax
  rw [n1s_cond_beq_eq, n1s_max2Nat_eq_max]
  split_ifs with h0
  · rw [n1s_lat_if_pos h0] at hx
    rw [hx, Nat.add_zero]
  · rw [n1s_lat_if_neg h0] at hx
    rcases hx with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _

theorem n1s_modFoldCoord_127_sq_cases {d : ℤ} (hd : -(2 * (127 : ℤ)) ≤ d ∧ d ≤ 2 * (127 : ℤ))
    : if (modFoldCoord 127 d).natAbs = 0 then d.natAbs ^ 2 = 0 else d.natAbs ^ 2 =
    (modFoldCoord 127 d).natAbs * (modFoldCoord 127 d).natAbs ∨ d.natAbs ^ 2 =
    (255 - (modFoldCoord 127 d).natAbs) * (255 - (modFoldCoord 127 d).natAbs) := by
  split_ifs with ha0
  · have hfold0 : modFoldCoord 127 d = 0 := Int.natAbs_eq_zero.mp ha0
    have hd0 : d = 0 := (modFoldCoord_eq_zero_iff 127 hd).mp hfold0
    simp [hd0]
  · have hcases : d.natAbs = (modFoldCoord 127 d).natAbs ∨ d.natAbs = 255 -
      (modFoldCoord 127 d).natAbs := by
      rw [modFoldCoord_eq 127 hd]
      split_ifs <;> omega
    rcases hcases with h1 | h2
    · exact Or.inl (by rw [sq, h1])
    · exact Or.inr (by rw [sq, h2])

/-- Explicit per-`ν` kernel discrepancy upper bound `E_nu` across all `Norm1sTier` operating
  points. -/
noncomputable def eNuNorm1s (t : Norm1sTier) (ν : Fin 3 → ℤ) : ℝ :=
  (n1sAliasMax3 (n1sErrCached t (shellIndex ν)) (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ)

theorem eNuNorm1s_nonneg (t : Norm1sTier) :
    ∀ ν ∈ nonzeroBox3D (127 : ℤ), 0 ≤ eNuNorm1s t ν := by
  intro ν _
  exact Nat.cast_nonneg _

theorem n1s_shellIndex_eq_log2Fast127 {ν : Fin 3 → ℤ} (hν : ν ∈ nonzeroBox3D (127 : ℤ)) :
    shellIndex ν = log2Fast127 (max3Nat (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs) ∧
      shellIndex ν ≤ 6 := by
  rw [mem_nonzeroBox3D] at hν
  have hm_pos : 1 ≤ maxCoordNatAbs ν := maxCoordNatAbs_pos_of_ne_zero hν.1
  have hm_le : maxCoordNatAbs ν ≤ 127 := by
    have h0 := hν.2 0; have h1 := hν.2 1; have h2 := hν.2 2
    unfold maxCoordNatAbs
    omega
  unfold shellIndex
  rw [nat_log_two_eq_log2Fast127 hm_pos hm_le, maxCoordNatAbs_eq_max3Nat]
  exact ⟨rfl, log2Fast127_le_six _⟩

theorem eNuNorm1s_bound (t : Norm1sTier) :
    ∀ ν ∈ nonzeroBox3D (127 : ℤ),
      ∀ Δ ∈ box3D (2 * (127 : ℤ)),
        modFold3D 127 Δ = ν →
          |((2 ^ (38 - t.kBits) *
              norm1sAcceptCountK t (shellIndex ν) (sumNatAbsSq Δ) : ℕ) : ℝ) -
            ((cRad7Computable (shellIndex ν) / sumNatAbsSq Δ : ℕ) : ℝ)| ≤ eNuNorm1s t ν := by
  intro ν hν Δ hΔ hfold
  obtain ⟨_, hmu6⟩ := n1s_shellIndex_eq_log2Fast127 hν
  rw [mem_nonzeroBox3D] at hν
  rw [mem_box3D] at hΔ
  have hΔ_ne : Δ ≠ 0 := by
    intro h0
    apply hν.1
    rw [← hfold, h0]
    ext w
    change modFoldCoord 127 0 = 0
    exact (modFoldCoord_eq_zero_iff 127 ⟨by omega, by omega⟩).mpr rfl
  have hs_pos : 0 < sumNatAbsSq Δ := sumNatAbsSq_pos_of_ne_zero hΔ_ne
  have hs_lt : sumNatAbsSq Δ < 262144 := by
    have h0 := hΔ 0; have h1 := hΔ 1; have h2 := hΔ 2
    have hsq0 : (Δ 0).natAbs ^ 2 ≤ 254 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hsq1 : (Δ 1).natAbs ^ 2 ≤ 254 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hsq2 : (Δ 2).natAbs ^ 2 ≤ 254 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    unfold sumNatAbsSq
    rw [Fin.sum_univ_three]
    omega
  have hraw :
      |((2 ^ (38 - t.kBits) * norm1sAcceptCountK t (shellIndex ν) (sumNatAbsSq Δ) : ℕ) : ℝ) -
          ((cRad7Computable (shellIndex ν) / sumNatAbsSq Δ : ℕ) : ℝ)| =
        (n1sErrCached t (shellIndex ν) (sumNatAbsSq Δ) : ℝ) := by
    rw [n1sErrCached_eq_n1sRawErr t hmu6]
    unfold n1sRawErr n1sRawErrAt
    simp only [n1s_nat_mul_eq, n1s_nat_div_eq]
    rw [n1s_cond_beq_eq, n1s_lat_if_neg hs_pos.ne', n1sPow2Sub38_eq,
      n1sFastAcceptCountK_eq_norm1sAcceptCountK t hs_pos hs_lt, n1sCRadFast_eq hmu6,
      n1sNatDist_cast_eq]
  rw [hraw]
  unfold eNuNorm1s
  exact_mod_cast (by
    have hw0 : modFoldCoord 127 (Δ 0) = ν 0 := congrFun hfold 0
    have hw1 : modFoldCoord 127 (Δ 1) = ν 1 := congrFun hfold 1
    have hw2 : modFoldCoord 127 (Δ 2) = ν 2 := congrFun hfold 2
    have hc0 := n1s_modFoldCoord_127_sq_cases (hΔ 0); rw [hw0] at hc0
    have hc1 := n1s_modFoldCoord_127_sq_cases (hΔ 1); rw [hw1] at hc1
    have hc2 := n1s_modFoldCoord_127_sq_cases (hΔ 2); rw [hw2] at hc2
    have hsum_eq : sumNatAbsSq Δ =
        0 + (Δ 0).natAbs ^ 2 + (Δ 1).natAbs ^ 2 + (Δ 2).natAbs ^ 2 := by
      unfold sumNatAbsSq; rw [Fin.sum_univ_three]; omega
    rw [hsum_eq]
    calc n1sErrCached t (shellIndex ν)
          (0 + (Δ 0).natAbs ^ 2 + (Δ 1).natAbs ^ 2 + (Δ 2).natAbs ^ 2)
      _ ≤ n1sAxisAliasMax (ν 2).natAbs (n1sErrCached t (shellIndex ν))
            (0 + (Δ 0).natAbs ^ 2 + (Δ 1).natAbs ^ 2) :=
          n1s_le_axisAliasMax hc2 _ _
      _ ≤ n1sAxisAliasMax (ν 1).natAbs
            (n1sAxisAliasMax (ν 2).natAbs (n1sErrCached t (shellIndex ν)))
            (0 + (Δ 0).natAbs ^ 2) :=
          n1s_le_axisAliasMax hc1 _ _
      _ ≤ n1sAliasMax3 (n1sErrCached t (shellIndex ν))
            (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs :=
          n1s_le_axisAliasMax hc0 _ 0 :
    n1sErrCached t (shellIndex ν) (sumNatAbsSq Δ) ≤
      n1sAliasMax3 (n1sErrCached t (shellIndex ν)) (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs)

/- ## Section 5: Stack-Safe Hoisted Octant Reduction and Shell-Disjoint 3-Chunk Certificate -/

/-- Exact `4096`-scaled summand `4096 * eNuNorm1s t ν / 4^(shellIndex ν)` on `nonzeroBox3D 127`. -/
def n1sFLattice4096 (t : Norm1sTier) (a b c : ℕ) : ℕ :=
  let m := max3Nat a b c
  bif Nat.beq m 0 then 0
  else n1sAliasMax3 (n1sErrCached t (log2Fast127 m)) a b c * inv4Val7 (log2Fast127 m)

/-- Octant-multiplicity weighted summand `octWeight a * octWeight b * octWeight c *
  n1sFLattice4096`. -/
def n1sOctLattice (t : Norm1sTier) (a b c : ℕ) : ℕ :=
  octWeight a * octWeight b * octWeight c * n1sFLattice4096 t a b c

theorem n1sFLattice4096_zero (t : Norm1sTier) : n1sFLattice4096 t 0 0 0 = 0 := rfl

theorem n1sFLattice4096_swap12 (t : Norm1sTier) (a b c : ℕ) :
    n1sFLattice4096 t a b c = n1sFLattice4096 t b a c := by
  unfold n1sFLattice4096
  dsimp only
  rw [max3Nat_swap12 a b c]
  simp only [n1s_cond_beq_eq]
  split_ifs with hm0
  · rfl
  · rw [n1sAliasMax3_swap12]

theorem n1sFLattice4096_swap23 (t : Norm1sTier) (a b c : ℕ) :
    n1sFLattice4096 t a b c = n1sFLattice4096 t a c b := by
  unfold n1sFLattice4096
  dsimp only
  rw [max3Nat_swap23 a b c]
  simp only [n1s_cond_beq_eq]
  split_ifs with hm0
  · rfl
  · rw [n1sAliasMax3_swap23]

/-- Balanced `≤ 32`-step tail-recursive `n1sSumTail` sum (`0` closure thunks cached in WHNF). -/
def n1sNatSumFast (n : ℕ) (g : ℕ → ℕ) : ℕ := bif Nat.ble n 32 then n1sSumTail n g else bif
    Nat.ble n 64 then Nat.add (n1sSumTail 32 g) (n1sSumTail (Nat.sub n 32) (n1sShiftIdx 32 g))
    else bif Nat.ble n 96 then Nat.add
    (Nat.add (n1sSumTail 32 g) (n1sSumTail 32 (n1sShiftIdx 32 g)))
    (n1sSumTail (Nat.sub n 64) (n1sShiftIdx 64 g)) else Nat.add
    (Nat.add (n1sSumTail 32 g) (n1sSumTail 32 (n1sShiftIdx 32 g))) (Nat.add (n1sSumTail 32
    (n1sShiftIdx 64 g)) (n1sSumTail (Nat.sub n 96) (n1sShiftIdx 96 g)))

theorem n1sNatSumFast_eq (n : ℕ) (g : ℕ → ℕ) : n1sNatSumFast n g = natSum n g := by
  unfold n1sNatSumFast
  simp only [n1sSumTail_eq, n1sShiftIdx_eq, n1s_nat_add_eq, n1s_nat_sub_eq, n1s_cond_ble_eq]
  split_ifs with h32 h64 h96
  · rfl
  · conv_rhs => rw [show n = 32 + (n - 32) by omega, natSum_add_split]
  · conv_rhs =>
      rw [show n = (32 + 32) + (n - 64) by omega,
        natSum_add_split (32 + 32) (n - 64), natSum_add_split 32 32]
  · conv_rhs =>
      rw [show n = ((32 + 32) + 32) + (n - 96) by omega,
        natSum_add_split ((32 + 32) + 32) (n - 96),
        natSum_add_split (32 + 32) 32, natSum_add_split 32 32]
    simp only [Nat.reduceAdd, Nat.add_assoc]

/-- Reference plain-`let` specification of `n1sHoistedTerm` for proof bridging. -/
def n1sHoistedTermSpec (callS : ℕ → ℕ) (wVal k0 k1 b c : ℕ) : ℕ :=
  bif Nat.beq b 0 then
    bif Nat.beq c 0 then
      2 * max2Nat (callS k0) (callS k1) * wVal
    else
      let c0 := c * c
      let c1 := (255 - c) * (255 - c)
      4 * max2Nat
        (max2Nat (callS (k0 + c0)) (callS (k0 + c1)))
        (max2Nat (callS (k1 + c0)) (callS (k1 + c1))) * wVal
  else
    let b0 := b * b
    let b1 := (255 - b) * (255 - b)
    let p00 := k0 + b0
    let p01 := k0 + b1
    let p10 := k1 + b0
    let p11 := k1 + b1
    bif Nat.beq c 0 then
      4 * max2Nat
        (max2Nat (callS p00) (callS p01))
        (max2Nat (callS p10) (callS p11)) * wVal
    else
      let c0 := c * c
      let c1 := (255 - c) * (255 - c)
      8 * max2Nat
        (max2Nat
          (max2Nat (callS (p00 + c0)) (callS (p00 + c1)))
          (max2Nat (callS (p01 + c0)) (callS (p01 + c1))))
        (max2Nat
          (max2Nat (callS (p10 + c0)) (callS (p10 + c1)))
          (max2Nat (callS (p11 + c0)) (callS (p11 + c1)))) * wVal

/-- Hoisted `(k0, k1)` boundary evaluator for `n1sOctLattice t k b c` (`0` `@Nat.rec`s). -/
def n1sHoistedTerm (callS : ℕ → ℕ) (wVal k0 k1 b c : ℕ) : ℕ :=
  bif Nat.beq b 0 then
    bif Nat.beq c 0 then
      Nat.mul (Nat.mul 2 (max2Nat (callS k0) (callS k1))) wVal
    else
      let c0 := Nat.mul c c
      let c1 := Nat.mul (Nat.sub 255 c) (Nat.sub 255 c)
      Nat.mul (Nat.mul 4
        (max2Nat
          (max2Nat (callS (Nat.add k0 c0)) (callS (Nat.add k0 c1)))
          (max2Nat (callS (Nat.add k1 c0)) (callS (Nat.add k1 c1))))) wVal
  else
    let b0 := Nat.mul b b
    let b1 := Nat.mul (Nat.sub 255 b) (Nat.sub 255 b)
    let p00 := Nat.add k0 b0
    let p01 := Nat.add k0 b1
    let p10 := Nat.add k1 b0
    let p11 := Nat.add k1 b1
    bif Nat.beq c 0 then
      Nat.mul (Nat.mul 4
        (max2Nat
          (max2Nat (callS p00) (callS p01))
          (max2Nat (callS p10) (callS p11)))) wVal
    else
      let c0 := Nat.mul c c
      let c1 := Nat.mul (Nat.sub 255 c) (Nat.sub 255 c)
      Nat.mul (Nat.mul 8
        (max2Nat
          (max2Nat
            (max2Nat (callS (Nat.add p00 c0)) (callS (Nat.add p00 c1)))
            (max2Nat (callS (Nat.add p01 c0)) (callS (Nat.add p01 c1))))
          (max2Nat
            (max2Nat (callS (Nat.add p10 c0)) (callS (Nat.add p10 c1)))
            (max2Nat (callS (Nat.add p11 c0)) (callS (Nat.add p11 c1)))))) wVal

theorem n1sHoistedTerm_eq_spec (callS : ℕ → ℕ) (wVal k0 k1 b c : ℕ) :
    n1sHoistedTerm callS wVal k0 k1 b c = n1sHoistedTermSpec callS wVal k0 k1 b c := by
  unfold n1sHoistedTerm n1sHoistedTermSpec
  dsimp only
  simp only [n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq]

/-- Per-shell `mu` dispatcher substituting closed `n1sErrCached t <mu>` and literal `wVal`. -/
def n1sDispatchMu (t : Norm1sTier) (mu : ℕ) (body : (ℕ → ℕ) → ℕ → ℕ) : ℕ :=
  match mu with
  | 0 => body (n1sErrCached t 0) 4096
  | 1 => body (n1sErrCached t 1) 1024
  | 2 => body (n1sErrCached t 2) 256
  | 3 => body (n1sErrCached t 3) 64
  | 4 => body (n1sErrCached t 4) 16
  | 5 => body (n1sErrCached t 5) 4
  | _ => body (n1sErrCached t 6) 1

/-- Once-per-shell `(t, mu)` dispatcher substituting closed `n1sErrCached` and literal `wVal`. -/
def n1sDispatchShell (t : Norm1sTier) (mu : ℕ) (body : (ℕ → ℕ) → ℕ → ℕ) : ℕ :=
  match t with
  | .t26_18 => n1sDispatchMu .t26_18 mu body
  | .t26_17 => n1sDispatchMu .t26_17 mu body
  | .t26_16 => n1sDispatchMu .t26_16 mu body
  | .t27_17 => n1sDispatchMu .t27_17 mu body
  | .t28_17 => n1sDispatchMu .t28_17 mu body
  | .t29_18 => n1sDispatchMu .t29_18 mu body
  | .t29_17 => n1sDispatchMu .t29_17 mu body
  | .t30_18 => n1sDispatchMu .t30_18 mu body

theorem n1sDispatchShell_eq (t : Norm1sTier) {mu : ℕ} (hmu : mu ≤ 6) (body : (ℕ → ℕ) → ℕ → ℕ)
    : n1sDispatchShell t mu body = body (n1sErrCached t mu) (inv4Val7 mu) := by
  rcases (show mu = 0 ∨ mu = 1 ∨ mu = 2 ∨ mu = 3 ∨ mu = 4 ∨ mu = 5 ∨ mu = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases t <;> rfl

/-- Pointwise shell summand over abstract `callS` and weight `wVal`. -/
def n1sShellPoint (callS : ℕ → ℕ) (wVal a b c : ℕ) : ℕ :=
  octWeight a * octWeight b * octWeight c * (n1sAliasMax3 callS a b c * wVal)

theorem n1s_natSum_mul_const (m n : ℕ) (g : ℕ → ℕ) :
    natSum n (fun i ↦ m * g i) = m * natSum n g := by
  induction n with
  | zero => simp [natSum]
  | succ k ih =>
      change natSum k (fun i ↦ m * g i) + m * g k = m * (natSum k g + g k)
      rw [ih, Nat.mul_add]

/-- Branchless 8-point maximum for `c = j + 1 > 0` sharing leaf `BVar` pointers (`0` recursors). -/
def n1sOctCPosMaxLit (callS : ℕ → ℕ) (p00 p01 p10 p11 c0 c1 : ℕ) : ℕ := n1sMax2Fast
    (n1sMax2Fast (n1sMax2Fast (callS (Nat.add p00 c0)) (callS (Nat.add p00 c1))) (n1sMax2Fast
    (callS (Nat.add p01 c0)) (callS (Nat.add p01 c1)))) (n1sMax2Fast (n1sMax2Fast (callS
    (Nat.add p10 c0)) (callS (Nat.add p10 c1))) (n1sMax2Fast (callS (Nat.add p11 c0)) (callS
    (Nat.add p11 c1))))

/-- Unweighted 8-point alias maximum for `c = j + 1 > 0` sharing `(c0, c1)` pointers (`0`
  `@Nat.rec`s). -/
def n1sOctCPosMax (callS : ℕ → ℕ) (p00 p01 p10 p11 j : ℕ) : ℕ := n1sOctCPosMaxLit callS p00
    p01 p10 p11 (Nat.mul (Nat.add j 1) (Nat.add j 1))
    (Nat.mul (Nat.sub 254 j) (Nat.sub 254 j))

/-- Stage 5 of `n1sOctBStep`: evaluates `c = 0..b` sum once `bm1 = b - 1` is a `LitVal` (`0`
  `let`s). -/
def n1sOctBPosBM1 (callS : ℕ → ℕ) (wVal p00 p01 p10 p11 bm1 : ℕ) : ℕ := Nat.mul
    (Nat.mul 8 wVal) (Nat.add (Nat.add (n1sOctCPosMax callS p00 p01 p10 p11 bm1) (max2Nat
    (max2Nat (callS p00) (callS p01)) (max2Nat (callS p10) (callS p11)))) (Nat.mul 2
    (n1sNatSumFast bm1 (n1sOctCPosMax callS p00 p01 p10 p11))))

/-- Stage 4 of `n1sOctBStep`: binds `bm1 = b - 1` once `p00..p11` are `LitVal`s (`0` `let`s). -/
def n1sOctBPosP11 (callS : ℕ → ℕ) (wVal b p00 p01 p10 p11 : ℕ) : ℕ :=
  n1sCbv (n1sOctBPosBM1 callS wVal p00 p01 p10 p11) (Nat.sub b 1)

/-- Stage 3 of `n1sOctBStep`: binds `p11 = k1 + b1` (`0` inline lambdas). -/
def n1sOctBPosP10 (callS : ℕ → ℕ) (wVal k1 b1 b p00 p01 p10 : ℕ) : ℕ :=
  n1sCbv (n1sOctBPosP11 callS wVal b p00 p01 p10) (Nat.add k1 b1)

/-- Stage 2 of `n1sOctBStep`: binds `p10 = k1 + b0` (`0` inline lambdas). -/
def n1sOctBPosP01 (callS : ℕ → ℕ) (wVal k1 b0 b1 b p00 p01 : ℕ) : ℕ :=
  n1sCbv (n1sOctBPosP10 callS wVal k1 b1 b p00 p01) (Nat.add k1 b0)

/-- Stage 1 of `n1sOctBStep`: binds `p01 = k0 + b1` (`0` inline lambdas). -/
def n1sOctBPosP00 (callS : ℕ → ℕ) (wVal k0 k1 b0 b1 b p00 : ℕ) : ℕ :=
  n1sCbv (n1sOctBPosP01 callS wVal k1 b0 b1 b p00) (Nat.add k0 b1)

/-- Stage 0 of `n1sOctBStep`: binds `p00 = k0 + b0` once `(b0, b1)` are `LitVal`s (`0` `let`s). -/
def n1sOctBPosB01 (callS : ℕ → ℕ) (wVal k0 k1 b b0 b1 : ℕ) : ℕ :=
  n1sCbv (n1sOctBPosP00 callS wVal k0 k1 b0 b1 b) (Nat.add k0 b0)

/-- Flat outer `b`-step summand for `0 ≤ b < k` (`0` `let`s, `0` inline lambdas, hoisted `8 *
  wVal`). -/
def n1sOctBStep (callS : ℕ → ℕ) (wVal k0 k1 b : ℕ) : ℕ := bif Nat.beq b 0 then Nat.mul
    (Nat.mul 2 (max2Nat (callS k0) (callS k1))) wVal else n1sCbv2
    (n1sOctBPosB01 callS wVal k0 k1 b) (Nat.mul b b) (Nat.mul (Nat.sub 255 b) (Nat.sub 255 b))

/-- Stage 2 of `n1sOctShellBody`: evaluates shell `k` once `(k0, k1)` are `LitVal`s. -/
def n1sOctShellK1 (k : ℕ) (callS : ℕ → ℕ) (wVal k0 k1 : ℕ) : ℕ := Nat.add (Nat.add
    (n1sHoistedTerm callS wVal k0 k1 k k) (Nat.mul 3 (n1sNatSumFast k (n1sHoistedTerm callS
    wVal k0 k1 k)))) (Nat.mul 3 (n1sNatSumFast k (n1sOctBStep callS wVal k0 k1)))

/-- Stage 1 of `n1sOctShellBody`: binds `k1 = (255 - k)^2` (`0` inline lambdas). -/
def n1sOctShellK0 (k : ℕ) (callS : ℕ → ℕ) (wVal k0 : ℕ) : ℕ :=
  n1sCbv (n1sOctShellK1 k callS wVal k0) (Nat.mul (Nat.sub 255 k) (Nat.sub 255 k))

/-- Flat shell-`k` body binding `(k0, k1)` once per shell (`0` inline lambdas). -/
def n1sOctShellBody (k : ℕ) (callS : ℕ → ℕ) (wVal : ℕ) : ℕ :=
  n1sCbv (n1sOctShellK0 k callS wVal) (Nat.mul k k)

/-- Hoisted shell-`k` evaluator dispatching `(t, mu)` once per shell `k` (`0` inline lambdas). -/
def n1sOctShellFast (t : Norm1sTier) (k : ℕ) : ℕ := bif Nat.beq k 0 then 0 else
    n1sDispatchShell t (log2Fast127 k) (n1sOctShellBody k)

theorem n1sHoistedTermSpec_eq (callS : ℕ → ℕ) (wVal : ℕ) {k b c : ℕ} (hk : k ≠ 0) :
    n1sHoistedTermSpec callS wVal (k * k) ((255 - k) * (255 - k)) b c =
      n1sShellPoint callS wVal k b c := by
  unfold n1sHoistedTermSpec n1sShellPoint n1sAliasMax3 n1sAxisAliasMax octWeight
  simp only [n1s_cond_beq_eq, n1s_lat_if_neg hk, zero_add]
  cases b with
  | zero =>
      cases c with
      | zero => simp; ring
      | succ c' => simp; ring
  | succ b' =>
      cases c with
      | zero => simp; ring
      | succ c' => simp; ring

theorem n1sHoistedTerm_eq (callS : ℕ → ℕ) (wVal : ℕ) {k b c : ℕ} (hk : k ≠ 0) : n1sHoistedTerm
    callS wVal (k * k) ((255 - k) * (255 - k)) b c = n1sShellPoint callS wVal k b c :=
    (n1sHoistedTerm_eq_spec callS wVal _ _ b c).trans (n1sHoistedTermSpec_eq callS wVal hk)

theorem n1sMax2Fast_eq_max2Nat (a b : ℕ) : n1sMax2Fast a b = max2Nat a b :=
  (n1sMax2Fast_eq_max a b).trans (n1s_max2Nat_eq_max a b).symm

theorem n1sOctCPosMax_eq (callS : ℕ → ℕ) (wVal : ℕ) {k : ℕ} (hk : k ≠ 0) (b' j : ℕ) :
    (8 * wVal) * n1sOctCPosMax callS (k * k + (b' + 1) * (b' + 1))
    (k * k + (255 - (b' + 1)) * (255 - (b' + 1)))
    ((255 - k) * (255 - k) + (b' + 1) * (b' + 1))
    ((255 - k) * (255 - k) + (255 - (b' + 1)) * (255 - (b' + 1))) j = n1sShellPoint callS wVal
    k (b' + 1) (j + 1) := by
  rw [← n1sHoistedTermSpec_eq callS wVal (b := b' + 1) (c := j + 1) hk]
  unfold n1sOctCPosMax n1sOctCPosMaxLit n1sHoistedTermSpec
  have hb_beq : Nat.beq (b' + 1) 0 = false := rfl
  have hc_beq : Nat.beq (j + 1) 0 = false := rfl
  have hsub : 255 - (j + 1) = 254 - j := by omega
  rw [hb_beq, hc_beq]
  dsimp only [cond]
  simp only [n1sMax2Fast_eq_max2Nat, n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq, hsub]
  ring

theorem n1sOctCZero_eq (callS : ℕ → ℕ) (wVal : ℕ) {k : ℕ} (hk : k ≠ 0) (b' : ℕ) : 4 * max2Nat
    (max2Nat (callS (k * k + (b' + 1) * (b' + 1))) (callS (k * k + (255 - (b' + 1)) * (255 -
    (b' + 1))))) (max2Nat (callS ((255 - k) * (255 - k) + (b' + 1) * (b' + 1))) (callS ((255 -
    k) * (255 - k) + (255 - (b' + 1)) * (255 - (b' + 1))))) * wVal = n1sShellPoint callS wVal
    k (b' + 1) 0 := by
  rw [← n1sHoistedTermSpec_eq callS wVal (b := b' + 1) (c := 0) hk]
  unfold n1sHoistedTermSpec
  have hb_beq : Nat.beq (b' + 1) 0 = false := rfl
  have hc_beq : Nat.beq 0 0 = true := rfl
  rw [hb_beq, hc_beq]
  dsimp only [cond]

theorem n1sOctBStep_eq (callS : ℕ → ℕ) (wVal : ℕ) {k : ℕ} (hk : k ≠ 0) (b : ℕ) : n1sOctBStep
    callS wVal (k * k) ((255 - k) * (255 - k)) b = n1sShellPoint callS wVal k b b + 2 * natSum
    b (fun c ↦ n1sShellPoint callS wVal k b c) := by
  cases b with
  | zero =>
      rw [← n1sHoistedTermSpec_eq callS wVal (b := 0) (c := 0) hk]
      unfold n1sOctBStep n1sHoistedTermSpec
      have hz_beq : Nat.beq 0 0 = true := rfl
      rw [hz_beq]
      dsimp only [cond, natSum, Nat.mul_zero, Nat.add_zero]
      simp only [n1s_nat_mul_eq]
      rfl
  | succ b' =>
      unfold n1sOctBStep
      have hb_beq : Nat.beq (b' + 1) 0 = false := rfl
      rw [hb_beq]
      dsimp only [cond]
      rw [n1sCbv2_eq]
      unfold n1sOctBPosB01 n1sOctBPosP00 n1sOctBPosP01 n1sOctBPosP10 n1sOctBPosP11
        n1sOctBPosBM1
      repeat rw [n1sCbv_eq]
      simp only [n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq,
        Nat.add_sub_cancel, n1sNatSumFast_eq]
      have hsplit : natSum (b' + 1) (fun c ↦ n1sShellPoint callS wVal k (b' + 1) c) =
          n1sShellPoint callS wVal k (b' + 1) 0 +
            natSum b' (fun j ↦ n1sShellPoint callS wVal k (b' + 1) (j + 1)) := by
        conv_lhs => rw [show b' + 1 = 1 + b' by omega, natSum_add_split 1 b']
        have h1 : natSum 1 (fun c ↦ n1sShellPoint callS wVal k (1 + b') c) =
            n1sShellPoint callS wVal k (1 + b') 0 := Nat.zero_add _
        rw [h1]
        rw [show 1 + b' = b' + 1 by omega]
        congr 1
        exact natSum_congr fun j _ ↦ by rw [Nat.add_comm 1 j]
      have hint : (8 * wVal) * natSum b' (n1sOctCPosMax callS (k * k + (b' + 1) * (b' + 1)) (k
          * k + (255 - (b' + 1)) * (255 - (b' + 1))) ((255 - k) * (255 - k) + (b' + 1) * (b' +
          1)) ((255 - k) * (255 - k) + (255 - (b' + 1)) * (255 - (b' + 1)))) = natSum b'
          (fun j ↦ n1sShellPoint callS wVal k (b' + 1) (j + 1)) := by
        rw [← n1s_natSum_mul_const]
        exact natSum_congr fun j _ ↦ n1sOctCPosMax_eq callS wVal hk b' j
      have hdiag := n1sOctCPosMax_eq callS wVal hk b' b'
      have hc0 := n1sOctCZero_eq callS wVal hk b'
      rw [hsplit, ← hdiag, ← hc0, ← hint]
      ring

theorem n1sOctShellBody_eq {k : ℕ} (hk : k ≠ 0) (callS : ℕ → ℕ) (wVal : ℕ) :
    n1sOctShellBody k callS wVal = octShell (n1sShellPoint callS wVal) k := by
  unfold n1sOctShellBody
  rw [n1sCbv_eq]
  unfold n1sOctShellK0
  rw [n1sCbv_eq]
  unfold n1sOctShellK1 octShell
  simp only [n1s_nat_add_eq, n1s_nat_sub_eq, n1s_nat_mul_eq]
  rw[n1sNatSumFast_eq, n1sNatSumFast_eq, n1sHoistedTerm_eq callS wVal hk,
      natSum_congr (fun b _ ↦ n1sHoistedTerm_eq callS wVal hk),
      natSum_congr (fun b _ ↦ n1sOctBStep_eq callS wVal hk b)]

theorem n1sShellPoint_eq_octLattice (t : Norm1sTier) {k b c : ℕ} (hk : k ≠ 0) (hb : b ≤ k)
    (hc : c ≤ k) : n1sShellPoint (n1sErrCached t (log2Fast127 k)) (inv4Val7 (log2Fast127 k)) k
    b c = n1sOctLattice t k b c := by
  have hm : max3Nat k b c = k := by rw [max3Nat_eq_max]; omega
  unfold n1sShellPoint n1sOctLattice n1sFLattice4096
  dsimp only
  rw [hm, n1s_cond_beq_eq, n1s_lat_if_neg hk]

theorem n1sOctShellFast_eq (t : Norm1sTier) (k : ℕ) :
    n1sOctShellFast t k = octShell (n1sOctLattice t) k := by
  cases k with
  | zero => rfl
  | succ m =>
      have hk : m + 1 ≠ 0 := Nat.succ_ne_zero m
      unfold n1sOctShellFast
      rw[n1s_cond_beq_eq, n1s_lat_if_neg hk, n1sDispatchShell_eq t (log2Fast127_le_six (m + 1)),
          n1sOctShellBody_eq hk]
      unfold octShell
      exact congrArg₂ (· + ·)
        (congrArg₂ (· + ·) (n1sShellPoint_eq_octLattice t hk le_rfl le_rfl)
          (congrArg (3 * ·)
            (natSum_congr fun b hb ↦ n1sShellPoint_eq_octLattice t hk le_rfl hb.le)))
        (congrArg (3 * ·) (natSum_congr fun b hb ↦ congrArg₂ (· + ·)
          (n1sShellPoint_eq_octLattice t hk hb.le hb.le)
          (congrArg (2 * ·) (natSum_congr fun c hc ↦
            n1sShellPoint_eq_octLattice t hk hb.le (hc.trans hb).le))))

/-- Shell-disjoint low octant chunk `k ∈ [0, 64)` (`mu ∈ 0..5`, `118,875` distinct `(mu, sTrue)`
  pairs). -/
def n1sChunkLo (t : Norm1sTier) : ℕ := n1sNatSumFast 64 (n1sOctShellFast t)

/-- Shell-disjoint high octant chunk `k ∈ [64, 128)` (`mu = 6`, `122,309` distinct `(6, sTrue)`
  pairs). -/
def n1sChunkHi (t : Norm1sTier) : ℕ := n1sNatSumFast 64 (n1sShiftIdx 64 (n1sOctShellFast t))

theorem n1s_octSum128_eq_chunks2 (t : Norm1sTier) {lo hi tot : ℕ}
    (hLo : Nat.beq (n1sChunkLo t) lo = true) (hHi : Nat.beq (n1sChunkHi t) hi = true)
    (hTot : lo + hi = tot) : natSum 128 (octShell (n1sOctLattice t)) = tot := by
  have hcongr : natSum 128 (octShell (n1sOctLattice t)) = natSum 128 (n1sOctShellFast t) :=
    natSum_congr fun k _ ↦ (n1sOctShellFast_eq t k).symm
  have hsplit : natSum 128 (n1sOctShellFast t) = n1sChunkLo t + n1sChunkHi t := by
    unfold n1sChunkLo n1sChunkHi
    rw [n1sNatSumFast_eq, n1sNatSumFast_eq, n1sShiftIdx_eq]
    have h128 : (128 : ℕ) = 64 + 64 := rfl
    rw [h128, natSum_add_split 64 64]
  rw [hcongr, hsplit, Nat.beq_eq.mp hLo, Nat.beq_eq.mp hHi, hTot]

theorem n1s_real_sum_eq_octSum128 (t : Norm1sTier) :
    ∑ ν ∈ nonzeroBox3D (127 : ℤ), eNuNorm1s t ν / (2 : ℝ) ^ (2 * shellIndex ν) =
      (natSum 128 (octShell (n1sOctLattice t)) : ℝ) / 4096 := by
  have hpoint : ∀ ν ∈ nonzeroBox3D (127 : ℤ), eNuNorm1s t ν / (2 : ℝ) ^ (2 * shellIndex ν) =
      (n1sFLattice4096 t (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs : ℝ) / 4096 := by
    intro ν hν
    obtain ⟨hsh, hmu6⟩ := n1s_shellIndex_eq_log2Fast127 hν
    rw [mem_nonzeroBox3D] at hν
    have hm_pos : 1 ≤ maxCoordNatAbs ν := maxCoordNatAbs_pos_of_ne_zero hν.1
    rw [maxCoordNatAbs_eq_max3Nat] at hm_pos
    have hm_ne : max3Nat (ν 0).natAbs (ν 1).natAbs (ν 2).natAbs ≠ 0 := by omega
    unfold n1sFLattice4096 eNuNorm1s
    dsimp only
    rw [n1s_cond_beq_eq, n1s_lat_if_neg hm_ne, ← hsh, inv4Val7_eq hmu6]
    have hpow12 : (4096 : ℝ) = (2 : ℝ) ^ (2 * shellIndex ν) * (2 : ℝ) ^ (12 - 2 * shellIndex ν) :=
      by
      rw [← pow_add]
      have hexp : 2 * shellIndex ν + (12 - 2 * shellIndex ν) = 12 := by omega
      rw [hexp]
      norm_num
    push_cast
    rw [hpow12]
    have hp_ne : (2 : ℝ) ^ (12 - 2 * shellIndex ν) ≠ 0 := by positivity
    exact (mul_div_mul_right _ _ hp_ne).symm
  rw [Finset.sum_congr rfl hpoint, ← Finset.sum_div]
  congr 1
  exact sum_nonzeroBox3D_eq_oct_natSum 127 (n1sFLattice4096 t)
    (n1sFLattice4096_zero t) (n1sFLattice4096_swap12 t) (n1sFLattice4096_swap23 t)

set_option exponentiation.threshold 256
end Slot3Norm1s36LatticeBase
end Slot3Norm1s36LatticeBase

end QuantumComputation.Specs.StoppingPowerSolution
