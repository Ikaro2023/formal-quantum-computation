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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BlockEncoding

/-!
# Multiplexed Unitary Algebra, Zero-`T` `CZ`, & `4 T`-per-Pair Controlled-SWAP

Provides reusable `muxUnitary` composition/pullback lemmas, `zGate_eq_muxUnitary`, two-qubit `CZ`
(`cz2Circuit`, `0 T`), and `N`-pair controlled-SWAP (`cswapBlockDyn`, `4 * N` `T` gates, `0 TOFF`).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Solution.BlockEncodingCore

open Operator Matrix Circuit QProg Solution.CleanDyn HermitianMat
open scoped Matrix ComplexOrder MatrixOrder Circuit.Notation

/-! ### 1. `muxUnitary` Algebra (`muxUnitary_mul`, `muxUnitary_pullback`, `zGate_eq_muxUnitary`) -/

theorem muxUnitary_mul {n k_c k_t : ℕ}
    (rCtrl : QRegister k_c n) (rTgt : QRegister k_t n)
    (hdisj : rCtrl.DisjointWires rTgt)
    (F₁ F₂ : Fin (2 ^ k_c) → Unitary (2 ^ k_t)) :
    muxUnitary rCtrl rTgt hdisj F₁ * muxUnitary rCtrl rTgt hdisj F₂ =
      muxUnitary rCtrl rTgt hdisj (fun c ↦ F₁ c * F₂ c) := by
  apply Subtype.ext
  ext i g
  let c₀ := rCtrl.extractIndex g
  have hg (g' : Fin (2 ^ n)) (h : rCtrl.extractIndex g' ≠ c₀) :
      Pi.single (M := fun _ ↦ ℂ) g 1 g' = 0 := by
    rw [Pi.single_eq_of_ne]; rintro rfl; exact h rfl
  let v₁ := (rTgt.embedMatrix (F₂ c₀).1) *ᵥ Pi.single g 1
  have hv₁ (g' : Fin (2 ^ n)) (h : rCtrl.extractIndex g' ≠ c₀) : v₁ g' = 0 := by
    have hzero : rCtrl.basisOutcomeProjector (rCtrl.extractIndex g') *ᵥ v₁ = 0 := by
      dsimp [v₁]
      unfold QRegister.basisOutcomeProjector
      rw [Matrix.mulVec_mulVec,
        rCtrl.embedMatrix_comm_of_disjoint rTgt hdisj (compProj _) (F₂ c₀).1,
        ← Matrix.mulVec_mulVec]
      have hp0 : rCtrl.embedMatrix (compProj (rCtrl.extractIndex g')) *ᵥ Pi.single g 1 = 0 := by
        change rCtrl.basisOutcomeProjector (rCtrl.extractIndex g') *ᵥ Pi.single g 1 = 0
        funext q
        rw [rCtrl.basisOutcomeProjector_mulVec, Pi.zero_apply]
        by_cases hq : rCtrl.extractIndex q = rCtrl.extractIndex g'
        · rw [ite_eq_left hq, Pi.single_eq_of_ne]
          rintro rfl; exact h hq.symm
        · exact ite_eq_right hq
      rw [hp0, Matrix.mulVec_zero]
    have hval := congrFun hzero g'
    simpa [rCtrl.basisOutcomeProjector_mulVec] using hval
  have hlhs : ((muxUnitary rCtrl rTgt hdisj F₁ * muxUnitary rCtrl rTgt hdisj F₂).1 *ᵥ
      Pi.single g 1) i =
      ((rTgt.embedMatrix (F₁ c₀ * F₂ c₀).1) *ᵥ Pi.single g 1) i := by
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
    rw [muxUnitary_mulVec_of_proj rCtrl rTgt hdisj F₂ c₀ _ hg,
      muxUnitary_mulVec_of_proj rCtrl rTgt hdisj F₁ c₀ v₁ hv₁,
      Matrix.mulVec_mulVec, ← rTgt.embedMatrix_mul]
  have hrhs : ((muxUnitary rCtrl rTgt hdisj (fun c ↦ F₁ c * F₂ c)).1 *ᵥ Pi.single g 1) i =
      ((rTgt.embedMatrix (F₁ c₀ * F₂ c₀).1) *ᵥ Pi.single g 1) i := by
    rw [muxUnitary_mulVec_of_proj rCtrl rTgt hdisj _ c₀ _ hg]
  rw [Matrix.mulVec_single_one] at hlhs hrhs
  exact hlhs.trans hrhs.symm

theorem muxUnitary_pullback {n k_c k_t k₀ m₀ : ℕ}
    (rCtrl : QRegister k_c n) (rTgt : QRegister k_t n)
    (hdisj : rCtrl.DisjointWires rTgt)
    (subCtrl : QRegister k₀ k_c) (subTgt : QRegister m₀ k_t)
    (F₀ : Fin (2 ^ k₀) → Unitary (2 ^ m₀)) :
    muxUnitary (rCtrl.compose subCtrl) (rTgt.compose subTgt)
        (by
          rw [QRegister.disjoint_iff]
          intro i j
          exact hdisj.ne (subCtrl i) (subTgt j))
        F₀ =
      muxUnitary rCtrl rTgt hdisj
        (fun c ↦ subTgt.embedUnitary (F₀ (subCtrl.extractIndex c))) := by
  have hdisj₀ : (rCtrl.compose subCtrl).DisjointWires (rTgt.compose subTgt) := by
    rw [QRegister.disjoint_iff]; intro i j; exact hdisj.ne (subCtrl i) (subTgt j)
  apply Subtype.ext
  ext i g
  let c₀ := rCtrl.extractIndex g
  have hg (g' : Fin (2 ^ n)) (h : rCtrl.extractIndex g' ≠ c₀) :
      Pi.single (M := fun _ ↦ ℂ) g 1 g' = 0 := by
    rw [Pi.single_eq_of_ne]; rintro rfl; exact h rfl
  have hg₀ (g' : Fin (2 ^ n))
      (h : (rCtrl.compose subCtrl).extractIndex g' ≠ subCtrl.extractIndex c₀) :
      Pi.single (M := fun _ ↦ ℂ) g 1 g' = 0 := by
    rw [Pi.single_eq_of_ne]; rintro rfl; exact h (QRegister.extractIndex_compose _ _ _)
  have hlhs : ((muxUnitary (rCtrl.compose subCtrl) (rTgt.compose subTgt) hdisj₀ F₀).1 *ᵥ
      Pi.single g 1) i =
      ((rTgt.compose subTgt).embedMatrix (F₀ (subCtrl.extractIndex c₀)).1 *ᵥ
        Pi.single g 1) i := by
    rw [muxUnitary_mulVec_of_proj (rCtrl.compose subCtrl) (rTgt.compose subTgt)
      hdisj₀ F₀ (subCtrl.extractIndex c₀) _ hg₀]
  have hrhs : ((muxUnitary rCtrl rTgt hdisj
      (fun c ↦ subTgt.embedUnitary (F₀ (subCtrl.extractIndex c)))).1 *ᵥ Pi.single g 1) i =
      (rTgt.embedMatrix (subTgt.embedUnitary (F₀ (subCtrl.extractIndex c₀))).1 *ᵥ
        Pi.single g 1) i := by
    rw [muxUnitary_mulVec_of_proj rCtrl rTgt hdisj
      (fun c ↦ subTgt.embedUnitary (F₀ (subCtrl.extractIndex c))) c₀ _ hg]
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at hlhs hrhs
  rw [hlhs, hrhs, QRegister.embedUnitary_val, ← QRegister.embedMatrix_compose]

/-- Global `-1` phase unitary on `2 ^ k` dimensions. -/
noncomputable def negOneUnitary (k : ℕ) : Unitary (2 ^ k) :=
  ⟨(-1 : ℂ) • (1 : Operator (2 ^ k)), by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_one, smul_mul_smul_comm]
    norm_num⟩

@[simp]
theorem negOneUnitary_val (k : ℕ) :
    (negOneUnitary k).1 = (-1 : ℂ) • (1 : Operator (2 ^ k)) := rfl

/-- Zero-`TOFF` `DynamicCircuit` for `N`-pair controlled-SWAP (`4 * N` `T` gates, `1` clean
ancilla). -/
def cswapBlockDyn {Var : Type} {n : ℕ} (v : Var) (N : ℕ)
    (rPlace : QRegister (1 + 2 * N) n) (anc : Wire n) : DynamicCircuit Var n :=
  substToffoliWithAncilla v rPlace anc (cswapBlockCircuit N)

@[simp]
theorem cswapBlockDyn_count_toff {Var : Type} {n : ℕ} (v : Var) (N : ℕ)
    (rPlace : QRegister (1 + 2 * N) n) (anc : Wire n) :
    (cswapBlockDyn v N rPlace anc).count .TOFF = 0 :=
  count_substToffoliWithAncilla_toff v rPlace anc (cswapBlockCircuit N)

theorem cswapBlockDyn_count_t {Var : Type} {n : ℕ} (v : Var) (N : ℕ)
    (rPlace : QRegister (1 + 2 * N) n) (anc : Wire n)
    (hdisj : rPlace.DisjointWires (QRegister.singleton anc)) :
    (cswapBlockDyn v N rPlace anc).count .T = 4 * N := by
  rw [cswapBlockDyn, count_substToffoliWithAncilla_t v rPlace anc hdisj (cswapBlockCircuit N),
    cswapBlockCircuit_count_t, cswapBlockCircuit_count_toff, zero_add]

theorem cleanRealizes_cswapBlockDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    {n s : ℕ} (v : Var) (N : ℕ)
    (rPlace : QRegister (1 + 2 * N) n) (rScr : QRegister s n)
    (hdisj : rPlace.DisjointWires rScr) (j : Fin s) :
    CleanRealizes v rPlace rScr
      (muxUnitary (QRegister.singleton 0) (QRegister.block 1 (2 * N) (by omega))
        (by
          rw [QRegister.disjoint_iff]
          intro a b heq; fin_cases a
          have hv := congrArg Fin.val heq; simp at hv; omega)
        (fun σ ↦ if σ = 0 then 1 else Operator.permutationUnitary (spinSwapEquiv N)))
      (cswapBlockDyn v N rPlace (rScr j)) := by
  rw [← cswapBlockCircuit_eval N]
  exact cleanRealizes_substToffoliWithAncilla v rPlace rScr hdisj j (cswapBlockCircuit N)

/-! ### 3. Reversible Temporary-AND Compute / Uncompute Engine (`TempProg`) -/

/-- Little-endian Boolean bit vector of a basis index `c : Fin (2 ^ k)`. -/
def bitsOfFin (k : ℕ) (c : Fin (2 ^ k)) : Fin k → Bool :=
  fun i ↦ decide (basisBits k c i = 1)

/-- Basis index `Fin (2 ^ k)` from a Boolean bit vector `x : Fin k → Bool`. -/
def finOfBits (k : ℕ) (x : Fin k → Bool) : Fin (2 ^ k) :=
  (basisBits k).symm (fun i ↦ if x i then 1 else 0)

@[simp]
theorem bitsOfFin_finOfBits (k : ℕ) (x : Fin k → Bool) :
    bitsOfFin k (finOfBits k x) = x := by
  funext i
  change decide ((basisBits k (finOfBits k x)) i = 1) = x i
  simp only [finOfBits, Equiv.apply_symm_apply]
  cases x i <;> decide

@[simp]
theorem finOfBits_bitsOfFin (k : ℕ) (c : Fin (2 ^ k)) :
    finOfBits k (bitsOfFin k c) = c := by
  apply (basisBits k).injective
  funext i
  simp only [finOfBits, Equiv.apply_symm_apply, bitsOfFin]
  change (if decide (basisBits k c i = 1) = true then 1 else 0) = basisBits k c i
  generalize basisBits k c i = b
  fin_cases b <;> rfl

/-- Multiplexed unitary on `k_t + k_c` active wires where `0 .. k_t - 1` is the target block and
`k_t .. k_t + k_c - 1` is the `k_c`-bit control block. -/
noncomputable def muxOnAct (k_t k_c : ℕ)
    (F : (Fin k_c → Bool) → Unitary (2 ^ k_t)) : Unitary (2 ^ (k_t + k_c)) :=
  muxUnitary (QRegister.block k_t k_c (by omega)) (QRegister.block 0 k_t (by omega))
    (by
      rw [QRegister.disjoint_iff]
      intro i j heq
      have hv := congrArg Fin.val heq; simp at hv; omega)
    (fun c ↦ F (bitsOfFin k_c c))

theorem embedUnitary_muxOnAct {n k_t k_c : ℕ}
    (rTgt : QRegister k_t n) (rCtrl : QRegister k_c n)
    (hdisj : rTgt.DisjointWires rCtrl)
    (F : (Fin k_c → Bool) → Unitary (2 ^ k_t)) :
    (rTgt.concat rCtrl hdisj).embedUnitary (muxOnAct k_t k_c F) =
      muxUnitary rCtrl rTgt (QRegister.disjoint_comm.mp hdisj)
        (fun c ↦ F (bitsOfFin k_c c)) := by
  let rAct := rTgt.concat rCtrl hdisj
  have hcompT : rAct.compose (QRegister.block 0 k_t (by omega)) = rTgt := by
    ext i
    have hi : QRegister.block 0 k_t (by omega : 0 + k_t ≤ k_t + k_c) i = Fin.castAdd k_c i := by
      ext; simp
    simp [rAct, hi]
  have hcompC : rAct.compose (QRegister.block k_t k_c (by omega)) = rCtrl := by
    ext j
    have hj : QRegister.block k_t k_c (by omega : k_t + k_c ≤ k_t + k_c) j = Fin.natAdd k_t j := by
      ext; simp
    simp [rAct, hj]
  apply Subtype.ext
  change rAct.embedMatrix (muxOnAct k_t k_c F).1 = _
  dsimp only [muxOnAct, muxUnitary]
  rw [rAct.embedMatrix_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [QRegister.embedMatrix_mul]
  have hP : rAct.embedMatrix ((QRegister.block k_t k_c (by omega)).basisOutcomeProjector c) =
      rCtrl.basisOutcomeProjector c := by
    unfold QRegister.basisOutcomeProjector
    rw [← QRegister.embedMatrix_compose, hcompC]
  have hE : rAct.embedMatrix ((QRegister.block 0 k_t (by omega)).embedMatrix
      (F (bitsOfFin k_c c)).1) = rTgt.embedMatrix (F (bitsOfFin k_c c)).1 := by
    rw [← QRegister.embedMatrix_compose, hcompT]
  rw [hP, hE]

/-- Retract one clean ancilla wire `anc` from `(rAct.concat (singleton anc), rScrMid)` to
`(rAct, (singleton anc).concat rScrMid)` when `U_mid` agrees with `U_act` on `|0⟩_{anc}`. -/
theorem cleanRealizes_retract_ancilla_local {Var : Type} [Fintype Var] [DecidableEq Var]
    {N k s : ℕ}
    (v : Var) (rAct : QRegister k N) (anc : Wire N)
    (hActAnc : rAct.DisjointWires (QRegister.singleton anc))
    (rScrMid : QRegister s N)
    (hAncMid : (QRegister.singleton anc).DisjointWires rScrMid)
    (hActMid : rAct.DisjointWires rScrMid)
    (U_mid : Unitary (2 ^ (k + 1))) (U_act : Unitary (2 ^ k))
    (P : DynamicCircuit Var N)
    (hP : CleanRealizes v (rAct.concat (QRegister.singleton anc) hActAnc) rScrMid U_mid P)
    (hU_loc :
      let anc_loc : Wire (k + 1) := Fin.natAdd k (0 : Fin 1)
      let P₀_loc := (QRegister.singleton anc_loc).basisOutcomeProjector 0
      let rAct_sub : QRegister k (k + 1) := .block 0 k (by omega)
      U_mid.1 * P₀_loc = (rAct_sub.embedUnitary U_act).1 * P₀_loc) :
    CleanRealizes v rAct ((QRegister.singleton anc).concat rScrMid hAncMid) U_act P := by
  let rAnc1 := QRegister.singleton anc
  let rScr := rAnc1.concat rScrMid hAncMid
  let rActExt := rAct.concat rAnc1 hActAnc
  have hdisj : rAct.DisjointWires rScr :=
    QRegister.disjointWires_concat_right hAncMid hActAnc hActMid
  refine CleanRealizes.mk_of_disjoint v rAct rScr hdisj U_act P hP.1 hP.2.1 fun Θ hΘ ↦ ?_
  have hP₀ : rAnc1.basisOutcomeProjector 0 =
      rActExt.embedMatrix
        ((QRegister.singleton (Fin.natAdd k (0 : Fin 1))).basisOutcomeProjector 0) := by
    unfold QRegister.basisOutcomeProjector
    rw [← QRegister.embedMatrix_compose]
    congr 1; ext j; fin_cases j; simp [rActExt, rAnc1]
  have hAct : rAct.embedUnitary U_act =
      rActExt.embedUnitary ((QRegister.block 0 k (by omega)).embedUnitary U_act) := by
    have hcomp : rActExt.compose (QRegister.block 0 k (by omega)) = rAct := by
      ext j
      have hj : QRegister.block 0 k (by omega : 0 + k ≤ k + 1) j = Fin.castAdd 1 j := by
        ext; simp
      simp [rActExt, hj]
    rw [← QRegister.embedUnitary_compose, hcomp]
  have hU_amb : (rActExt.embedUnitary U_mid).1 * rAnc1.basisOutcomeProjector 0 =
      (rAct.embedUnitary U_act).1 * rAnc1.basisOutcomeProjector 0 := by
    rw [hP₀, hAct, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
      ← QRegister.embedMatrix_mul, ← QRegister.embedMatrix_mul]
    exact congrArg rActExt.embedMatrix hU_loc
  have hadj : rAnc1.basisOutcomeProjector 0 * (rActExt.embedUnitary U_mid).1ᴴ =
      rAnc1.basisOutcomeProjector 0 * (rAct.embedUnitary U_act).1ᴴ := by
    have h := congrArg conjTranspose hU_amb
    simpa only [conjTranspose_mul, QRegister.basisOutcomeProjector_conjTranspose] using h
  have hproj_mr : rScr.basisOutcomeProjector 0 =
      rScrMid.basisOutcomeProjector 0 * rAnc1.basisOutcomeProjector 0 := by
    rw [QRegister.basisOutcomeProjector_eq_diagonal, QRegister.basisOutcomeProjector_eq_diagonal,
      QRegister.basisOutcomeProjector_eq_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext g
    have heq : rScr.extractIndex g = 0 ↔
        rScrMid.extractIndex g = 0 ∧ rAnc1.extractIndex g = 0 := by
      dsimp only [rScr]
      simp only [Solution.CleanDyn.extractIndex_eq_zero_iff_basisBits_eq_zero]
      refine ⟨fun h ↦ ⟨fun j ↦ by simpa using h (Fin.natAdd 1 j),
          fun i ↦ by simpa using h (Fin.castAdd s i)⟩,
        fun ⟨h₂, h₁⟩ idx ↦ ?_⟩
      obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective idx
      · simpa using h₁ i
      · simpa using h₂ j
    by_cases h₂ : rScrMid.extractIndex g = 0 <;> by_cases h₁ : rAnc1.extractIndex g = 0 <;>
      simp [heq, h₁, h₂]
  have hproj_rm : rScr.basisOutcomeProjector 0 =
      rAnc1.basisOutcomeProjector 0 * rScrMid.basisOutcomeProjector 0 := by
    rw [hproj_mr]
    exact QRegister.embedMatrix_comm_of_disjoint rScrMid rAnc1
      (QRegister.disjoint_comm.mp hAncMid) (compProj 0) (compProj 0)
  have hswap (A : QCAssertion Var (2 ^ N)) :
      restrictAssertionToZeroAncilla A rScr =
        restrictAssertionToZeroAncilla (restrictAssertionToZeroAncilla A rScrMid) rAnc1 := by
    funext σ'; apply Subtype.ext
    simp only [restrictAssertionToZeroAncilla_coe, conj_conj, hproj_rm]
  rw [hswap, hP.2.2.1 Θ hΘ, ← hswap]
  funext σ'; apply Subtype.ext
  simp only [restrictAssertionToZeroAncilla_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj]
  rw [hproj_mr, Matrix.mul_assoc, hadj, ← Matrix.mul_assoc]

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BlockEncodingCircuit
