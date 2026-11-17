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

/-!
# `(wOuter, kZeroOut)`-Parametric Outer-`PREP` Conjugation & Sequential Wrapper

Provides computational-basis permutation conjugation (`preservesWires_conj_embedEquiv`),
zero-prefix wire-preservation under outer state-preparation conjugation (`OuterConjPreservesZero`,
`outerConjPreservesZero_of_disjoint`, `outerConjPreservesZero_mul_left_equiv`,
`outerConjPreservesZero_mul_left_invol`), and the split sequential outer wrapper
(`outerSeqWrapDyn`).

## References
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: 10.22331/q-2018-06-18-74.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: 10.22331/q-2019-12-02-208.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
- J. J. Goings, A. White, J. Lee, C. S. Tautermann, M. Degroote, C. Gidney, N. Shoresh,
  J. R. McClean, and R. Babbush, "Reliably assessing the electronic structure of cytochrome P450
  on today's classical computers and tomorrow's quantum computers," *Proc. Natl. Acad. Sci. U.S.A.*
  **119**, e2203533119 (2022), DOI: 10.1073/pnas.2203533119.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactZeroCmp20OuterParam

open Operator QProg Matrix Circuit HermitianMat Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit CoherentAlias AliasPrep Phase2MidSandwich
open CompactBilinearPrep OptFactoredMag30AndCoin9 Cat11CompactPhase2Bridge ReordOuter13Bridge
open ZeroRcHotPrepMid21Fast OptXMeasUnload21 Tuned162ScheduledSympQrom21
open Tuned162StepSympAnfQrom21 OptStepSympAnfQrom21 OptU2Grover184PrepOut13
open TopIntegrationBridge MobiusOptSubcube163Walk CompactTuned162StepWalk
open CompactTuned162StepZeroCmp20
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option exponentiation.threshold 512

local instance (priority := 1000000) instNeZeroTwoPowZeroCmp20OuterParam (k : ℕ) :
    NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-- Conjugating an operator `A` that preserves `T` (`rSub.image ⊆ T`) by a computational-basis
permutation unitary `rSub.embedUnitary U` (`ket γ ↦ ket (perm γ)`) still preserves `T`. -/
theorem preservesWires_conj_embedEquiv {N k : ℕ} {A : Operator (2 ^ N)}
    {T : Finset (Wire N)} (hA : AliasPrep.PreservesWires A T)
    (rSub : QRegister k N) (hSub : rSub.image ⊆ T)
    (U : Unitary (2 ^ k)) (perm : Equiv.Perm (BitAssignment k))
    (hUk : ∀ γ : BitAssignment k,
      U.1.mulVec (SelectSwapQROM.ket γ) = SelectSwapQROM.ket (perm γ)) :
    AliasPrep.PreservesWires ((rSub.embedUnitary U)⁻¹.1 * A * (rSub.embedUnitary U).1) T := by
  let gFwd : BitAssignment N → BitAssignment N :=
    fun β ↦ Comparators.writeReg β rSub (perm (fun i ↦ β (rSub i)))
  let gInv : BitAssignment N → BitAssignment N :=
    fun β ↦ Comparators.writeReg β rSub (perm.symm (fun i ↦ β (rSub i)))
  have hgLeft (β : BitAssignment N) : gInv (gFwd β) = β := by
    funext w
    by_cases hw : w ∈ Set.range rSub.wires
    · obtain ⟨i, rfl⟩ := hw
      dsimp only [gInv, gFwd]
      rw [Comparators.writeReg_apply_reg]
      have hfn : (fun j ↦ Comparators.writeReg β rSub (perm fun u ↦ β (rSub u)) (rSub j)) =
          perm (fun u ↦ β (rSub u)) := funext fun j ↦ Comparators.writeReg_apply_reg _ _ _ j
      rw [hfn, perm.symm_apply_apply]
    · dsimp only [gInv, gFwd]
      rw [Comparators.writeReg_apply_of_not_mem _ _ _ w hw,
        Comparators.writeReg_apply_of_not_mem _ _ _ w hw]
  have hgRight (β : BitAssignment N) : gFwd (gInv β) = β := by
    funext w
    by_cases hw : w ∈ Set.range rSub.wires
    · obtain ⟨i, rfl⟩ := hw
      dsimp only [gInv, gFwd]
      rw [Comparators.writeReg_apply_reg]
      have hfn : (fun j ↦ Comparators.writeReg β rSub (perm.symm fun u ↦ β (rSub u)) (rSub j)) =
          perm.symm (fun u ↦ β (rSub u)) := funext fun j ↦ Comparators.writeReg_apply_reg _ _ _ j
      rw [hfn, perm.apply_symm_apply]
    · dsimp only [gInv, gFwd]
      rw [Comparators.writeReg_apply_of_not_mem _ _ _ w hw,
        Comparators.writeReg_apply_of_not_mem _ _ _ w hw]
  have hUinvk (γ : BitAssignment k) :
      (U⁻¹).1.mulVec (SelectSwapQROM.ket γ) = SelectSwapQROM.ket (perm.symm γ) := by
    have h1 := congrArg (U⁻¹.1.mulVec ·) (hUk (perm.symm γ))
    rw [perm.apply_symm_apply, Matrix.mulVec_mulVec,
      show (U⁻¹).1 * U.1 = 1 from congrArg Subtype.val (inv_mul_cancel U),
      Matrix.one_mulVec] at h1
    exact h1.symm
  have hWFwd (β : BitAssignment N) :
      (rSub.embedUnitary U).1.mulVec (SelectSwapQROM.ket β) =
        SelectSwapQROM.ket (gFwd β) := by
    rw [QRegister.embedUnitary_val, Comparators.embedMatrix_mulVec_ket]
    have hcol (l : Fin (2 ^ k)) :
        U.1 l (Comparators.localIdx rSub β) =
          (U.1.mulVec (SelectSwapQROM.ket (fun i ↦ β (rSub i)))) l := by
      change U.1 l _ = (U.1.mulVec (basisState (Comparators.localIdx rSub β))) l
      simp [basisState]
    simp_rw [hcol, hUk (fun i ↦ β (rSub i))]
    rw [Finset.sum_eq_single ((basisBits k).symm (perm (fun i ↦ β (rSub i))))]
    · simp only [SelectSwapQROM.ket, basisState, Pi.single_eq_same, one_smul,
        SelectSwapQROM.basisBits_symm]; rfl
    · intro l _ hl; simp [SelectSwapQROM.ket, basisState, Pi.single_eq_of_ne hl]
    · simp
  have hWInvVec (β : BitAssignment N) :
      ((rSub.embedUnitary U)⁻¹).1.mulVec (SelectSwapQROM.ket β) =
        SelectSwapQROM.ket (gInv β) := by
    rw [← QRegister.embedUnitary_inv, QRegister.embedUnitary_val,
      Comparators.embedMatrix_mulVec_ket]
    have hcol (l : Fin (2 ^ k)) :
        (U⁻¹).1 l (Comparators.localIdx rSub β) =
          ((U⁻¹).1.mulVec (SelectSwapQROM.ket (fun i ↦ β (rSub i)))) l := by
      change (U⁻¹).1 l _ = ((U⁻¹).1.mulVec (basisState (Comparators.localIdx rSub β))) l
      simp [basisState]
    simp_rw [hcol, hUinvk (fun i ↦ β (rSub i))]
    rw [Finset.sum_eq_single ((basisBits k).symm (perm.symm (fun i ↦ β (rSub i))))]
    · simp only [SelectSwapQROM.ket, basisState, Pi.single_eq_same, one_smul,
        SelectSwapQROM.basisBits_symm]; rfl
    · intro l _ hl; simp [SelectSwapQROM.ket, basisState, Pi.single_eq_of_ne hl]
    · simp
  have hWInvAny (vec : Fin (2 ^ N) → ℂ) (i : Fin (2 ^ N)) :
      (((rSub.embedUnitary U)⁻¹).1 *ᵥ vec) i =
        vec ((basisBits N).symm (gFwd (basisBits N i))) := by
    have hv : vec = ∑ m : Fin (2 ^ N), vec m • SelectSwapQROM.ket (basisBits N m) := by
      funext x; simp [SelectSwapQROM.ket, basisState, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_sum, Finset.sum_apply]
    simp_rw [Matrix.mulVec_smul, hWInvVec, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single ((basisBits N).symm (gFwd (basisBits N i)))]
    · rw [SelectSwapQROM.ket, basisState, SelectSwapQROM.basisBits_symm, hgLeft,
        SelectSwapQROM.symm_basisBits, Pi.single_eq_same, mul_one]
    · intro m _ hm
      have hne : (basisBits N).symm (gInv (basisBits N m)) ≠ i := by
        intro heq; apply hm
        have h1 := congrArg (fun x ↦ (basisBits N).symm (gFwd (basisBits N x))) heq
        simpa only [SelectSwapQROM.basisBits_symm, hgRight,
          SelectSwapQROM.symm_basisBits] using h1
      simp [SelectSwapQROM.ket, basisState, hne.symm]
    · simp
  intro i j ⟨w, hw, hij⟩
  have hentry : ((rSub.embedUnitary U)⁻¹.1 * A * (rSub.embedUnitary U).1) i j =
      A ((basisBits N).symm (gFwd (basisBits N i)))
        ((basisBits N).symm (gFwd (basisBits N j))) := by
    have hcol : ((rSub.embedUnitary U)⁻¹.1 * A * (rSub.embedUnitary U).1) i j =
        (((rSub.embedUnitary U)⁻¹.1 * A * (rSub.embedUnitary U).1) *ᵥ
          SelectSwapQROM.ket (basisBits N j)) i := by
      simp [SelectSwapQROM.ket, basisState]
    rw [hcol, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hWInvAny, hWFwd]
    change (A *ᵥ SelectSwapQROM.ket (gFwd (basisBits N j))) _ = _
    simp [SelectSwapQROM.ket, basisState]
  rw [hentry]
  apply hA
  simp only [SelectSwapQROM.basisBits_symm]
  by_contra hall
  push Not at hall
  apply hij
  have hlocEq : (fun u ↦ gFwd (basisBits N i) (rSub u)) =
      fun u ↦ gFwd (basisBits N j) (rSub u) :=
    funext fun u ↦ hall (rSub u) (hSub ((QRegister.mem_image rSub _).mpr ⟨u, rfl⟩))
  have hgEq : gInv (gFwd (basisBits N i)) w = gInv (gFwd (basisBits N j)) w := by
    by_cases hwR : w ∈ Set.range rSub.wires
    · obtain ⟨u, rfl⟩ := hwR
      change Comparators.writeReg (gFwd (basisBits N i)) rSub _ (rSub u) =
        Comparators.writeReg (gFwd (basisBits N j)) rSub _ (rSub u)
      rw [Comparators.writeReg_apply_reg, Comparators.writeReg_apply_reg, hlocEq]
    · change Comparators.writeReg (gFwd (basisBits N i)) rSub _ w =
        Comparators.writeReg (gFwd (basisBits N j)) rSub _ w
      rw [Comparators.writeReg_apply_of_not_mem _ _ _ w hwR,
        Comparators.writeReg_apply_of_not_mem _ _ _ w hwR]
      exact hall w hw
  rwa [hgLeft, hgLeft] at hgEq

/-- Wire-preservation of `S_ext ∪ (rOut.compose (outZeroPrefixReg wOuter kZeroOut hkOut)).image`
under conjugation by `rOut.embedUnitary prepOutImpl` whenever `U_core` preserves
`rOut.image ∪ S_ext`. -/
def OuterConjPreservesZero (wOuter kZeroOut : ℕ) (hkOut : kZeroOut ≤ wOuter)
    (prepOutImpl : Unitary (2 ^ mOutUB wOuter)) : Prop :=
  ∀ {N : ℕ} (rOut : QRegister (mOutUB wOuter) N) (S_ext : Finset (Wire N)),
    Disjoint rOut.image S_ext →
    ∀ {U_core : Operator (2 ^ N)},
      AliasPrep.PreservesWires U_core (rOut.image ∪ S_ext) →
      AliasPrep.PreservesWires
        ((rOut.embedUnitary prepOutImpl)⁻¹.1 * U_core * (rOut.embedUnitary prepOutImpl).1)
        (S_ext ∪ (rOut.compose (outZeroPrefixReg wOuter kZeroOut hkOut)).image)

theorem outerConjPreservesZero_of_disjoint {wOuter kZeroOut kInit : ℕ} (hkOut : kZeroOut ≤ wOuter)
    (rInit : QRegister kInit (mOutUB wOuter))
    (hDisj : rInit.DisjointWires (outZeroPrefixReg wOuter kZeroOut hkOut))
    (uInit : Unitary (2 ^ kInit)) :
    OuterConjPreservesZero wOuter kZeroOut hkOut (rInit.embedUnitary uInit) := by
  intro N rOut S_ext hDisjOut U_core hPres
  let S_all := S_ext ∪ (rOut.compose (outZeroPrefixReg wOuter kZeroOut hkOut)).image
  have hSubAll : S_all ⊆ rOut.image ∪ S_ext :=
    Finset.union_subset Finset.subset_union_right
      ((rOut.image_compose_subset _).trans Finset.subset_union_left)
  have hCoreSub : AliasPrep.PreservesWires U_core S_all :=
    fun i j ⟨w, hw, hne⟩ ↦ hPres i j ⟨w, hSubAll hw, hne⟩
  have hDisjInit : Disjoint (rOut.compose rInit).image S_all := by
    refine Finset.disjoint_union_right.mpr
      ⟨Disjoint.mono_left (rOut.image_compose_subset _) hDisjOut,
       SelectSwapQROM.disjoint_image_of_disjointWires (QRegister.disjoint_iff.mpr fun i j hij ↦
         hDisj.ne i j (rOut.wires.injective hij))⟩
  have hW : AliasPrep.PreservesWires (rOut.embedUnitary (rInit.embedUnitary uInit)).1 S_all := by
    rw [← QRegister.embedUnitary_compose]
    exact AliasPrep.preservesWires_embedMatrix_of_disjoint _ _ S_all hDisjInit
  have hWinv :
      AliasPrep.PreservesWires ((rOut.embedUnitary (rInit.embedUnitary uInit))⁻¹).1 S_all := by
    rw [← QRegister.embedUnitary_inv, ← QRegister.embedUnitary_inv,
      ← QRegister.embedUnitary_compose]
    exact AliasPrep.preservesWires_embedMatrix_of_disjoint _ _ S_all hDisjInit
  exact AliasPrep.preservesWires_mul (AliasPrep.preservesWires_mul hWinv hCoreSub) hW

theorem outerConjPreservesZero_mul_left_equiv {wOuter kZeroOut : ℕ} {hkOut : kZeroOut ≤ wOuter}
    {uPerm uRest : Unitary (2 ^ mOutUB wOuter)}
    (perm : Equiv.Perm (BitAssignment (mOutUB wOuter)))
    (hPerm : ∀ γ : BitAssignment (mOutUB wOuter),
      uPerm.1.mulVec (SelectSwapQROM.ket γ) = SelectSwapQROM.ket (perm γ))
    (hRest : OuterConjPreservesZero wOuter kZeroOut hkOut uRest) :
    OuterConjPreservesZero wOuter kZeroOut hkOut (uPerm * uRest) := by
  intro N rOut S_ext hDisjOut U_core hPres
  have hPermPres := preservesWires_conj_embedEquiv hPres rOut Finset.subset_union_left uPerm perm
    hPerm
  have hStep := hRest rOut S_ext hDisjOut hPermPres
  have hRewrite :
      (rOut.embedUnitary (uPerm * uRest))⁻¹.1 * U_core * (rOut.embedUnitary (uPerm * uRest)).1 =
      (rOut.embedUnitary uRest)⁻¹.1 *
        ((rOut.embedUnitary uPerm)⁻¹.1 * U_core * (rOut.embedUnitary uPerm).1) *
        (rOut.embedUnitary uRest).1 := by
    rw [rOut.embedUnitary_mul, _root_.mul_inv_rev]
    simp only [Submonoid.coe_mul, Matrix.mul_assoc]
  rwa [hRewrite]

theorem outerConjPreservesZero_mul_left_invol {wOuter kZeroOut : ℕ} {hkOut : kZeroOut ≤ wOuter}
    {uPerm uRest : Unitary (2 ^ mOutUB wOuter)}
    (g : BitAssignment (mOutUB wOuter) → BitAssignment (mOutUB wOuter))
    (hgInvol : ∀ γ, g (g γ) = γ)
    (hPerm : ∀ γ : BitAssignment (mOutUB wOuter),
      uPerm.1.mulVec (SelectSwapQROM.ket γ) = SelectSwapQROM.ket (g γ))
    (hRest : OuterConjPreservesZero wOuter kZeroOut hkOut uRest) :
    OuterConjPreservesZero wOuter kZeroOut hkOut (uPerm * uRest) :=
  outerConjPreservesZero_mul_left_equiv
    { toFun := g, invFun := g, left_inv := hgInvol, right_inv := hgInvol } hPerm hRest

/-- Left-associated split outer wrapper `(pOutFwd ;; pCore) ;; pOutBwd`. -/
def outerSeqWrapDyn {Var : Type} {N : ℕ}
    (pOutFwd pCore pOutBwd : DynamicCircuit Var N) : DynamicCircuit Var N :=
  .seq (.seq pOutFwd pCore) pOutBwd

@[simp] theorem countOuterSeqWrapDyn_toff {Var : Type} {N : ℕ}
    {pOutFwd pCore pOutBwd : DynamicCircuit Var N}
    (hf : pOutFwd.count .TOFF = 0) (hc : pCore.count .TOFF = 0)
    (hb : pOutBwd.count .TOFF = 0) :
    (outerSeqWrapDyn pOutFwd pCore pOutBwd).count .TOFF = 0 := by
  simp [outerSeqWrapDyn, DynamicCircuit.count, hf, hc, hb]

@[simp] theorem countOuterSeqWrapDyn_t {Var : Type} {N : ℕ}
    (pOutFwd pCore pOutBwd : DynamicCircuit Var N) :
    (outerSeqWrapDyn pOutFwd pCore pOutBwd).count .T =
      pOutFwd.count .T + pOutBwd.count .T + pCore.count .T := by
  simp only [outerSeqWrapDyn, DynamicCircuit.count]; omega

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactZeroCmp20OuterParam
