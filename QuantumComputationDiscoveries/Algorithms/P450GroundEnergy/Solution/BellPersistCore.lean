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

public import QuantumComputationSpecs.Algorithms.P450DFTHCData
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Defs
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TwoGearQPE
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.LowBitPi145Select

/-!
# Bell-Persistent `K`-Step Super-Reflection Core Primitives & Clean-Slice `R₀` SDK

Provides the cert-free foundational circuit definitions, gate-count theorems, `iterBinDyn` weakest
precondition lemmas, `bQPE`-parametric register/outer-sandwich combinators, and clean-slice input
reflection `reflInSliceDyn` for `K`-step Bell-persistent `StageA` super-reflections.

## References
- C. Jones, "Low-overhead constructions for the fault-tolerant Toffoli gate," *Phys. Rev. A*
  **87**, 022328 (2013), DOI: `10.1103/PhysRevA.87.022328`.
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018),
  DOI: `10.22331/q-2018-06-18-74`.
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity," *Phys. Rev. X* **8**,
  041015 (2018), DOI: `10.1103/PhysRevX.8.041015`.
- D. W. Berry, C. Gidney, M. Motta, J. R. McClean, and R. Babbush, "Qubitization of Arbitrary
  Basis Quantum Chemistry Leveraging Sparsity and Low Rank Factorization," *Quantum* **3**, 208
  (2019), DOI: `10.22331/q-2019-12-02-208`.
- J. Lee, D. W. Berry, C. Gidney, W. J. Huggins, J. R. McClean, N. Wiebe, and R. Babbush,
  "Even More Efficient Quantum Computations of Chemistry Through Tensor Hypercontraction,"
  *PRX Quantum* **2**, 030305 (2021), DOI: `10.1103/PRXQuantum.2.030305`.
- J. J. Goings *et al.*, "Reliably assessing the electronic structure of cytochrome P450 on
  today's classical computers and tomorrow's quantum computers," *Proc. Natl. Acad. Sci. U.S.A.*
  **119**(37), e2203533119 (2022), DOI: `10.1073/pnas.2203533119`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellPersistCore
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias CleanDyn AliasPrep
open QuantumComputation.Specs QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
open QuantumComputation.Specs.P450 CircuitModular
open BlockEncodingCore BlockEncodingCircuit
open LowBitPi145Select BellPhaseASelect BellSingletCSwap58
open Lac2Fused184Select
open _root_.QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.CompactStepFast176Select
  hiding
  combARem midRemWidth
open CompactOuter9Bound50Core PolymorphicFused184Select
open Phase2MidSandwich MidReflCtxRetain TopIntegrationBridge
open CompactTuned162StepWalk CompactTuned162StepZeroCmp20
open CompactZeroCmp20OuterParam SelectSwapQROM Cat11CompactPhase2Bridge
open ReordOuter13Bridge DihedralWalkQPE DihedralWalkQPE.MultiGearQPE
open DihedralWalkQPE.BlockReflection
open TwoGearQPEPhase5 TwoGearBox
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance instNeZeroTwoPowBellCore (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: `iterBinDyn` Weakest Preconditions & Clean-Set Helpers -/

theorem wp_iterBinDyn_compile {Var : Type} [DecidableEq Var] {N : ℕ}
    (m : ℕ) (P : DynamicCircuit Var N) (Θ : QCAssertion Var (2 ^ N)) :
    wp (iterBinDyn m P).compile Θ = (wp P.compile)^[m] Θ := by
  induction m using Nat.strongRecOn generalizing Θ with
  | ind m ih =>
    unfold iterBinDyn
    split_ifs with h0 h1 heven
    · subst h0; simp
    · subst h1; simp
    · simp only [DynamicCircuit.compile_seq, wp_qSeq, ih (m / 2) (by omega),
        ← Function.iterate_add_apply]
      rw [show m / 2 + m / 2 = m by omega]
    · simp only [DynamicCircuit.compile_seq, wp_qSeq, ih (m / 2) (by omega),
        ← Function.iterate_add_apply, ← Function.iterate_succ_apply]
      congr 2; omega

theorem preservesVInv_iterBinDyn {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    (m : ℕ) {v : Var} {P : DynamicCircuit Var N} (hP : PreservesVInv v P) :
    PreservesVInv v (iterBinDyn m P) := by
  intro Θ hΘ σ val
  simp only [wp_iterBinDyn_compile]
  revert σ val
  induction m with
  | zero => exact hΘ
  | succ k ih =>
    intro σ val
    simp only [Function.iterate_succ_apply']
    exact hP _ ih σ val

theorem restrictZeroSet_eq_of_subset {Var : Type} [Fintype Var] {N : ℕ} [NeZero (2 ^ N)]
    {Ψ₁ Ψ₂ : QCAssertion Var (2 ^ N)} {S₀ S : Finset (Wire N)} (hsub : S₀ ⊆ S)
    (heq : SelectSwapQROM.restrictZeroSet Ψ₁ S₀ = SelectSwapQROM.restrictZeroSet Ψ₂ S₀) :
    SelectSwapQROM.restrictZeroSet Ψ₁ S = SelectSwapQROM.restrictZeroSet Ψ₂ S := by
  have hun : S₀ ∪ S = S := Finset.union_eq_right.mpr hsub
  rw [← hun, ← SelectSwapQROM.restrictZeroSet_union, heq,
    SelectSwapQROM.restrictZeroSet_union]

theorem restrictZeroSet_qcWpQAssign_comm {Var : Type} [Fintype Var] {N : ℕ} [NeZero (2 ^ N)]
    {S : Finset (Wire N)} {U : Unitary (2 ^ N)}
    (hc : U.1 * SelectSwapQROM.zeroProjOn S = SelectSwapQROM.zeroProjOn S * U.1)
    (Φ : QCAssertion Var (2 ^ N)) :
    SelectSwapQROM.restrictZeroSet (qcWpQAssign U Φ) S =
      qcWpQAssign U (SelectSwapQROM.restrictZeroSet Φ S) := by
  have hadj : SelectSwapQROM.zeroProjOn S * U.1ᴴ = U.1ᴴ * SelectSwapQROM.zeroProjOn S := by
    simpa only [conjTranspose_mul, SelectSwapQROM.zeroProjOn_conjTranspose] using
      congrArg conjTranspose hc
  funext σ; apply Subtype.ext
  simp only [SelectSwapQROM.restrictZeroSet_coe, qcWpQAssign, qcQAssignObsMap,
    Observable.conj_coe, Unitary.coe_star, Matrix.star_eq_conjTranspose, conj_conj, hadj]

theorem cleanTurnaroundWp_congr {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S₁ S₂ : Finset (Wire N)} {A₁ A₂ B₁ B₂ : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N} (hS : S₁ = S₂) (hA : A₁ = A₂) (hB : B₁ = B₂)
    (h : CleanTurnaroundWp v S₂ A₂ B₂ P) : CleanTurnaroundWp v S₁ A₁ B₁ P := by
  subst hS hA hB; exact h

theorem cleanUnloadsWp_congr {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S₁ S₂ : Finset (Wire N)} {W₁ W₂ : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N} (hS : S₁ = S₂) (hW : W₁ = W₂)
    (h : CleanUnloadsWp v S₂ W₂ P) : CleanUnloadsWp v S₁ W₁ P := by
  subst hS hW; exact h

theorem preservesWires_of_offDiag_zero {N : ℕ} {A : Operator (2 ^ N)} (S : Finset (Wire N))
    (hDiag : ∀ i j : Fin (2 ^ N), i ≠ j → A i j = 0) :
    AliasPrep.PreservesWires A S := by
  intro i j ⟨w, _, hne⟩
  exact hDiag i j fun hij ↦ hne (hij ▸ rfl)

theorem preservesWires_embed_reflIn {N k w : ℕ}
    (rWalk : QRegister k N) (inAll : QRegister w k) (S : Finset (Wire N)) :
    AliasPrep.PreservesWires (rWalk.embedUnitary (QubitisedWalk.reflInUnitary inAll)).1 S := by
  have hemb : (rWalk.embedUnitary (QubitisedWalk.reflInUnitary inAll)).1 =
      (2 : ℂ) • (rWalk.compose inAll).basisOutcomeProjector 0 - 1 := by
    change rWalk.embedMatrix ((2 : ℂ) • inAll.basisOutcomeProjector 0 - 1) = _
    rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
      CleanDyn.compose_basisOutcomeProjector]
  rw [hemb, QRegister.basisOutcomeProjector_eq_diagonal]
  refine preservesWires_of_offDiag_zero S fun i j hij ↦ ?_
  simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

/-! ## Section 2: `bQPE`-Parametric Register & Outer-Sandwich Combinators -/

/-- `bQPE`-parametric `nUB wOuter wInner2` walk subregister inside `combQubitsAt`. -/
abbrev combUBRegB (bQPE wOuter wInner2 ko km mLow sUb : ℕ) :
    QRegister (nUB wOuter wInner2) (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb) :=
  (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).compose (rUBInCat wOuter wInner2 11)

/-- `bQPE`-parametric `mOutUB wOuter` outer subregister inside `combQubitsAt`. -/
abbrev combOutRegB (bQPE wOuter wInner2 ko km mLow sUb : ℕ) :
    QRegister (mOutUB wOuter) (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb) :=
  (combUBRegB bQPE wOuter wInner2 ko km mLow sUb).compose (rOutUB wOuter wInner2)

/-- `bQPE`-parametric `mMidUB wInner2` inner subregister inside `combQubitsAt`. -/
abbrev combMidRegB (bQPE wOuter wInner2 ko km mLow sUb : ℕ) :
    QRegister (mMidUB wInner2) (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb) :=
  (combUBRegB bQPE wOuter wInner2 ko km mLow sUb).compose (rMidUB wOuter wInner2)

theorem combWalkCatRegB_disjoint_scr (bQPE wOuter wInner2 ko km mLow sUb : ℕ) :
    (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).DisjointWires
      (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb) :=
  (rWalkCatLoc_disjoint_rScrLoc bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow
    (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sUb).compose_right _

theorem combOutRegB_disjoint_scr (bQPE wOuter wInner2 ko km mLow sUb : ℕ) :
    (combOutRegB bQPE wOuter wInner2 ko km mLow sUb).DisjointWires
      (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb) :=
  ((combWalkCatRegB_disjoint_scr bQPE wOuter wInner2 ko km mLow sUb).compose_left _).compose_left _

theorem combOutRegB_disjoint_scr_midZero (bQPE wOuter wInner2 ko km mLow sUb : ℕ) (hkMid : km ≤
    wInner2) :
    Disjoint (combOutRegB bQPE wOuter wInner2 ko km mLow sUb).image
      ((combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image ∪
        ((combMidRegB bQPE wOuter wInner2 ko km mLow sUb).compose
          (midZeroPrefixReg wInner2 km hkMid)).image) := by
  rw [Finset.disjoint_union_right]
  refine ⟨SelectSwapQROM.disjoint_image_of_disjointWires
    (combOutRegB_disjoint_scr bQPE wOuter wInner2 ko km mLow sUb),
    SelectSwapQROM.disjoint_image_of_disjointWires (QRegister.disjoint_iff.mpr fun i j heq ↦
      (disjoint_rOutUB_rMidUB wOuter wInner2).ne i (midZeroPrefixReg wInner2 km hkMid j)
        ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).wires.injective heq))⟩

theorem union_outMidZero_eq_rAncZeroLoc (bQPE bCat wOuter wInner2 mLow aRem mRem sUb : ℕ)
    {kOut kMid : ℕ} (outZ : QRegister kOut (mOutUB wOuter)) (midZ : QRegister kMid
      (mMidUB wInner2)) :
    ((((rWalkCatLoc bQPE bCat (mOutUB wOuter) (mMidUB wInner2) mLow aRem mRem sUb).compose
      (rUBInCat wOuter wInner2 bCat)).compose (rOutUB wOuter wInner2)).compose outZ).image ∪
    ((((rWalkCatLoc bQPE bCat (mOutUB wOuter) (mMidUB wInner2) mLow aRem mRem sUb).compose
      (rUBInCat wOuter wInner2 bCat)).compose (rMidUB wOuter wInner2)).compose midZ).image =
    (rAncZeroLoc bQPE bCat (mOutUB wOuter) (mMidUB wInner2) mLow aRem mRem sUb
      (liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2) outZ midZ)).image := by
  have hO (i : Fin kOut) :
      ((((rWalkCatLoc bQPE bCat (mOutUB wOuter) (mMidUB wInner2) mLow aRem mRem sUb).compose
        (rUBInCat wOuter wInner2 bCat)).compose (rOutUB wOuter wInner2)).compose outZ) i =
      (rAncZeroLoc bQPE bCat (mOutUB wOuter) (mMidUB wInner2) mLow aRem mRem sUb
        (liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2) outZ midZ)) (Fin.castAdd kMid i) := by
    ext; simp [rAncZeroLoc, rWalkCatLoc, rActLoc, rWalkCatInAct, inAllWalkCat, rWalkInWalkCat,
      rAllInWalk, liftOutMidZeroToAnc, rUBInCat, rOutUB, systemQubits_local, add_assoc]
  have hM (j : Fin kMid) :
      ((((rWalkCatLoc bQPE bCat (mOutUB wOuter) (mMidUB wInner2) mLow aRem mRem sUb).compose
        (rUBInCat wOuter wInner2 bCat)).compose (rMidUB wOuter wInner2)).compose midZ) j =
      (rAncZeroLoc bQPE bCat (mOutUB wOuter) (mMidUB wInner2) mLow aRem mRem sUb
        (liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2) outZ midZ)) (Fin.natAdd kOut j) := by
    ext; simp [rAncZeroLoc, rWalkCatLoc, rActLoc, rWalkCatInAct, inAllWalkCat, rWalkInWalkCat,
      rAllInWalk, liftOutMidZeroToAnc, rUBInCat, rMidUB, systemQubits_local, add_assoc]
  ext w; simp only [Finset.mem_union, QRegister.mem_image]
  refine ⟨fun h ↦ ?_, fun ⟨u, hu⟩ ↦ ?_⟩
  · rcases h with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨Fin.castAdd kMid i, (hO i).symm⟩
    · exact ⟨Fin.natAdd kOut j, (hM j).symm⟩
  · rcases Comparators.fin_eq_castAdd_or_natAdd u with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact Or.inl ⟨i, (hO i).trans hu⟩
    · exact Or.inr ⟨j, (hM j).trans hu⟩

/-- Inner-core `mid`-reflection unitary `M_bwd† sB M_bwd · reflMid · M_fwd† sF M_fwd`. -/
noncomputable abbrev innerMidCoreUnitary {wOuter wInner2 kCat : ℕ}
    (M_fwd M_bwd : Unitary (2 ^ nUB wOuter wInner2)) (sF sB : Unitary (2 ^ (nUB wOuter wInner2 +
      kCat))) :
    Unitary (2 ^ (nUB wOuter wInner2 + kCat)) :=
  ((rUBInCat wOuter wInner2 kCat).embedUnitary M_bwd⁻¹ * sB * (rUBInCat wOuter wInner2
    kCat).embedUnitary M_bwd) *
    QubitisedWalk.reflMidUnitary (inMidWalkCat kCat (mOutUB wOuter) (mMidUB wInner2)) *
    ((rUBInCat wOuter wInner2 kCat).embedUnitary M_fwd⁻¹ * sF * (rUBInCat wOuter wInner2
      kCat).embedUnitary M_fwd)

theorem outerSandwich_cleanRealizesSet {Var : Type} [Fintype Var] [DecidableEq Var]
    {bQPE wOuter wInner2 ko km : ℕ} (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    {mLow sUb : ℕ} {v : Var} {prepOutImpl : Unitary (2 ^ mOutUB wOuter)}
    {pOutFwd pOutBwd : DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (hFwd : CleanDyn.CleanRealizes v
      (combOutRegB bQPE wOuter wInner2 ko km mLow sUb)
      (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb) prepOutImpl pOutFwd)
    (hBwd : CleanUnloadsWp v
      ((combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image ∪
        ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).compose
          (outZeroPrefixReg wOuter ko hkOut)).image)
      ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary prepOutImpl) pOutBwd)
    (hConj : OuterConjPreservesZero wOuter ko hkOut prepOutImpl)
    (U_core : Unitary (2 ^ combQubitsAt bQPE wOuter wInner2 ko km mLow sUb))
    (pCore : DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb))
    (hCore : SelectSwapQROM.CleanRealizesSet v
      ((combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image ∪
        ((combMidRegB bQPE wOuter wInner2 ko km mLow sUb).compose
          (midZeroPrefixReg wInner2 km hkMid)).image) U_core pCore)
    (hPresCore : AliasPrep.PreservesWires U_core.1
      ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).image ∪
        ((combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image ∪
          ((combMidRegB bQPE wOuter wInner2 ko km mLow sUb).compose
            (midZeroPrefixReg wInner2 km hkMid)).image))) :
    SelectSwapQROM.CleanRealizesSet v
      (((combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image ∪
        ((combMidRegB bQPE wOuter wInner2 ko km mLow sUb).compose
          (midZeroPrefixReg wInner2 km hkMid)).image) ∪
        ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).compose
          (outZeroPrefixReg wOuter ko hkOut)).image)
      (((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary prepOutImpl)⁻¹ * U_core *
        (combOutRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary prepOutImpl)
      (outerSeqWrapDyn pOutFwd pCore pOutBwd) := by
  have hFwdSet := (SelectSwapQROM.cleanRealizes_iff_set v _ _ _ _).mp
    ((AliasPrep.cleanRealizes_sbx_iff _ _ _ _ _).mpr hFwd)
  let rOut := combOutRegB bQPE wOuter wInner2 ko km mLow sUb
  let rScr := combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rMidZero := (combMidRegB bQPE wOuter wInner2 ko km mLow sUb).compose
    (midZeroPrefixReg wInner2 km hkMid)
  let rOutZero := rOut.compose (outZeroPrefixReg wOuter ko hkOut)
  let S_ext := rScr.image ∪ rMidZero.image
  let N := combQubitsAt bQPE wOuter wInner2 ko km mLow sUb
  let W_out := rOut.embedUnitary prepOutImpl; let U_target := W_out⁻¹ * U_core * W_out
  let S_all := S_ext ∪ rOutZero.image
  let rAncZero := liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2)
    (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km hkMid)
  let rUbZero : QRegister (sUb + (ko + km)) N :=
    rUbZeroLoc bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow
      (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sUb rAncZero
  have hUbImg : rUbZero.image = S_all := by
    dsimp only [rUbZero, rAncZero, S_all, S_ext, rScr, rOutZero, rMidZero, rOut,
      combScrUbRegAt, combOutRegB, combMidRegB, combUBRegB, combWalkCatRegAt]
    rw [image_rUbZeroLoc, ← union_outMidZero_eq_rAncZeroLoc]
    ext w; simp only [Finset.mem_union]; tauto
  have hDisjOut : Disjoint rOut.image S_ext :=
    combOutRegB_disjoint_scr_midZero bQPE wOuter wInner2 ko km mLow sUb hkMid
  have hTargetPres : AliasPrep.PreservesWires U_target.1 S_all :=
    hConj rOut S_ext hDisjOut hPresCore
  have hcTarget : U_target.1 * SelectSwapQROM.zeroProjOn S_all =
      SelectSwapQROM.zeroProjOn S_all * U_target.1 :=
    AliasPrep.preservesWires_comm_zeroProjOn hTargetPres Finset.Subset.rfl
  have hcWoutExt : W_out.1 * SelectSwapQROM.zeroProjOn S_ext =
      SelectSwapQROM.zeroProjOn S_ext * W_out.1 :=
    AliasPrep.preservesWires_comm_zeroProjOn
      (AliasPrep.preservesWires_embedMatrix_of_disjoint rOut prepOutImpl.1 S_ext hDisjOut)
      Finset.Subset.rfl
  have hSubAll : rScr.image ∪ rOutZero.image ⊆ S_all := fun w hw ↦ by
    dsimp only [S_all, S_ext]; simp only [Finset.mem_union] at hw ⊢; tauto
  have hBwdAll : CleanUnloadsWp v S_all W_out pOutBwd := hBwd.extend hSubAll
  have hCR : XMeasCircuit.CleanRealizes v (QRegister.whole N) rUbZero U_target
      (outerSeqWrapDyn pOutFwd pCore pOutBwd) := by
    refine XMeasCircuit.CleanRealizes.mkOfWpClean
      (by simp [outerSeqWrapDyn, DynamicCircuit.count, hFwdSet.1, hCore.1, hBwd.1])
      (fun Θ hΘ σ val ↦ hFwdSet.2.1 _ (hCore.2.1 _ (hBwd.2.1 Θ hΘ)) σ val)
      (fun Θ hΘ ↦ ?_) ?_
    · rw [SelectSwapQROM.restrictAssertionToZeroAncilla_eq_restrictZeroSet,
        SelectSwapQROM.restrictAssertionToZeroAncilla_eq_restrictZeroSet,
        QRegister.whole_embedUnitary, hUbImg]
      let Ψ2 := wp pOutBwd.compile Θ; have hΨ2 := hBwd.2.1 Θ hΘ
      let Ψ1 := wp pCore.compile Ψ2; have hΨ1 := hCore.2.1 Ψ2 hΨ2
      have hStep12 : SelectSwapQROM.restrictZeroSet
          (wp (DynamicCircuit.seq pOutFwd pCore).compile Ψ2) S_ext =
          SelectSwapQROM.restrictZeroSet (qcWpQAssign (U_core * W_out) Ψ2) S_ext := by
        change SelectSwapQROM.restrictZeroSet (wp pOutFwd.compile Ψ1) S_ext = _
        rw [restrictZeroSet_eq_of_subset Finset.subset_union_left (hFwdSet.2.2.1 Ψ1 hΨ1),
          restrictZeroSet_qcWpQAssign_comm hcWoutExt, hCore.2.2.1 Ψ2 hΨ2,
          ← restrictZeroSet_qcWpQAssign_comm hcWoutExt, qc_wp_qAssign_comp]
      have hGrp : U_core * W_out = W_out * U_target := by
        dsimp only [U_target]; simp only [← mul_assoc, mul_inv_cancel, one_mul]
      have hReassoc : wp (outerSeqWrapDyn pOutFwd pCore pOutBwd).compile Θ =
          wp (DynamicCircuit.seq pOutFwd pCore).compile Ψ2 := rfl
      rw [hReassoc, restrictZeroSet_eq_of_subset Finset.subset_union_left hStep12, hGrp,
        ← qc_wp_qAssign_comp, restrictZeroSet_qcWpQAssign_comm hcTarget, hBwdAll.2.2 Θ hΘ,
        ← restrictZeroSet_qcWpQAssign_comm hcTarget]
    · rw [QRegister.whole_embedUnitary, SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
        hUbImg, ← Matrix.mul_assoc, ← hcTarget, Matrix.mul_assoc,
        SelectSwapQROM.zeroProjOn_mul_self]
  have hSet := (SelectSwapQROM.cleanRealizes_iff_set v (QRegister.whole N) rUbZero
    U_target _).mp ((AliasPrep.cleanRealizes_sbx_iff _ _ _ _ _).mp hCR)
  rwa [QRegister.whole_embedUnitary, hUbImg] at hSet

/-! ## Section 3: Clean-Slice `R₀` Input Reflection (`reflInSliceDyn`) -/

theorem block_disjoint {n a₁ k₁ a₂ k₂ : ℕ} (h₁ : a₁ + k₁ ≤ n) (h₂ : a₂ + k₂ ≤ n)
    (hle : a₁ + k₁ ≤ a₂) :
    (QRegister.block a₁ k₁ h₁).DisjointWires (QRegister.block a₂ k₂ h₂) :=
  QRegister.disjoint_iff.mpr fun i _ hij ↦ by
    have hv := congrArg Fin.val hij
    simp only [QRegister.block_apply_val] at hv
    have := i.isLt; omega

/-- Local `(aRem + (aRem - 2))`-wire `R₀` input reflection (`4 * (aRem - 2) T`, `0 TOFF`). -/
def reflInLocDyn {Var : Type} (aRem : ℕ) (haPos : 1 ≤ aRem) (v : Var) :
    DynamicCircuit Var (aRem + (aRem - 2)) :=
  QubitisedWalk.reflInDyn v (QRegister.block 0 aRem (by omega))
    (QRegister.block aRem (aRem - 2) (by omega)) haPos le_rfl
    (block_disjoint (by omega) (by omega) (by omega))

/-- Placement of `reflInLocDyn` onto `(rWalkCat.compose refl.inAll) ++ rScrUb[0 .. aRem - 2)`. -/
def reflInSlicePlace (bQPE wOuter wInner2 ko km mLow sUb : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hsIn : combARem wOuter wInner2 ko km - 2 ≤ sUb) :
    QRegister (combARem wOuter wInner2 ko km + (combARem wOuter wInner2 ko km - 2))
      (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb) :=
  let rMain := combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rScrUb := combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb
  let refl := combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid
  have hDisj : (rMain.compose refl.inAll).DisjointWires
      (rScrUb.slice 0 (combARem wOuter wInner2 ko km - 2) (by omega)) :=
    ((combWalkCatRegB_disjoint_scr bQPE wOuter wInner2 ko km mLow sUb).compose_left _).compose_right
      _
  (rMain.compose refl.inAll).concat (rScrUb.slice 0 (combARem wOuter wInner2 ko km -
    2) (by omega)) hDisj

/-- Clean-slice `R₀` reflection on `combQubitsAt` touching only `refl.inAll` and
`rScrUb[0 .. aRem - 2)` (`4 * (aRem - 2) T`, `0 TOFF`). -/
def reflInSliceDyn {Var : Type} (bQPE wOuter wInner2 ko km mLow sUb : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hsIn : combARem wOuter wInner2 ko km -
      2 ≤ sUb) (v : Var) :
    DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb) :=
  (reflInLocDyn (combARem wOuter wInner2 ko km)
    (combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid).haPos v).onRegister
    (reflInSlicePlace bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid hsIn)

@[simp] theorem countReflInSliceDyn_toff {Var : Type} (bQPE wOuter wInner2 ko km mLow sUb : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hsIn : combARem wOuter wInner2 ko km -
      2 ≤ sUb) (v : Var) :
    (reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid hsIn v).count .TOFF = 0 := by
  simp [reflInSliceDyn, reflInLocDyn]

@[simp] theorem countReflInSliceDyn_t {Var : Type} (bQPE wOuter wInner2 ko km mLow sUb : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hsIn : combARem wOuter wInner2 ko km -
      2 ≤ sUb) (v : Var) :
    (reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid hsIn v).count .T =
      4 * (combARem wOuter wInner2 ko km - 2) := by
  simp [reflInSliceDyn, reflInLocDyn]

theorem cleanRealizesReflInSliceDyn_scrUb {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE wOuter wInner2 ko km mLow sUb : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsIn : combARem wOuter wInner2 ko km - 2 ≤ sUb) (v : Var) :
    CleanDyn.CleanRealizes v
      (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb)
      (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb)
      (QubitisedWalk.reflInUnitary (combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid).inAll)
      (reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid hsIn v) := by
  let aRem := combARem wOuter wInner2 ko km
  let refl := combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid
  let rMain := combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rScrUb := combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rAll0 : QRegister aRem (aRem + (aRem - 2)) := QRegister.block 0 aRem (by omega)
  let rScr0 : QRegister (aRem - 2) (aRem + (aRem - 2)) := QRegister.block aRem (aRem - 2) (by omega)
  let pl := reflInSlicePlace bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid hsIn
  have hWhole : rAll0.compose (QRegister.whole aRem) = rAll0 := by ext i; rfl
  have hLoc0 : CleanDyn.CleanRealizes v rAll0 rScr0
      (QubitisedWalk.reflInUnitary (QRegister.whole aRem)) (reflInLocDyn aRem refl.haPos v) := by
    have h := QubitisedWalk.reflInDyn_cleanRealizes v rAll0 (QRegister.whole aRem) rScr0 refl.haPos
      le_rfl
      (by rw [hWhole]; exact block_disjoint (by omega) (by omega) (by omega))
    simpa only [reflInLocDyn, hWhole] using h
  have hPlAct : pl.compose rAll0 = rMain.compose refl.inAll := by
    ext i
    have hr : rAll0 i = Fin.castAdd (aRem - 2) i := Fin.ext (Nat.zero_add i.val)
    dsimp only [pl, reflInSlicePlace]
    rw [QRegister.compose_apply, hr, QRegister.concat_apply_left]
  have hPlScr : pl.compose rScr0 = rScrUb.slice 0 (aRem - 2) (by omega) := by
    ext i
    have hr : rScr0 i = Fin.natAdd aRem i := Fin.ext rfl
    dsimp only [pl, reflInSlicePlace]
    rw [QRegister.compose_apply, hr, QRegister.concat_apply_right]
  have hOn : CleanDyn.CleanRealizes v (rMain.compose refl.inAll)
      (rScrUb.slice 0 (aRem - 2) (by omega)) (QubitisedWalk.reflInUnitary (QRegister.whole aRem))
      (reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid hsIn v) := by
    have h := hLoc0.onRegister pl
    rwa [hPlAct, hPlScr] at h
  have hEmbEq : refl.inAll.embedUnitary (QubitisedWalk.reflInUnitary (QRegister.whole aRem)) =
      QubitisedWalk.reflInUnitary refl.inAll := by
    rw [← QubitisedWalk.diagSignUnitary_eq_embed_reflInUnitary refl.inAll (QRegister.whole aRem),
      ← QRegister.whole_embedUnitary (QubitisedWalk.reflInUnitary refl.inAll),
      ← QubitisedWalk.diagSignUnitary_eq_embed_reflInUnitary (QRegister.whole _) refl.inAll]
    rfl
  have hSub := hOn.subregister (combWalkCatRegB_disjoint_scr bQPE wOuter wInner2 ko km mLow sUb)
    (rScrUb.image_compose_subset _)
  rwa [hEmbEq] at hSub

theorem cleanRealizesSetReflInSliceDyn {Var : Type} [Fintype Var] [DecidableEq Var]
    (bQPE wOuter wInner2 ko km mLow sUb : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsIn : combARem wOuter wInner2 ko km - 2 ≤ sUb) (v : Var) :
    SelectSwapQROM.CleanRealizesSet v
      (((combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image ∪
        ((combMidRegB bQPE wOuter wInner2 ko km mLow sUb).compose
          (midZeroPrefixReg wInner2 km hkMid)).image) ∪
        ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).compose
          (outZeroPrefixReg wOuter ko hkOut)).image)
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        (QubitisedWalk.reflInUnitary (inAllWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))))
      (reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid hsIn v) := by
  let aRem := combARem wOuter wInner2 ko km; let mRem := midRemWidth wInner2 km
  let refl := combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid
  let rMain := combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rScrUb := combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rScr := rScrLoc bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow aRem mRem sUb
  let rAncZ := liftOutMidZeroToAnc (mOutUB wOuter) (mMidUB wInner2)
    (outZeroPrefixReg wOuter ko hkOut) (midZeroPrefixReg wInner2 km hkMid)
  let rUbZero := rUbZeroLoc bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow aRem mRem sUb rAncZ
  let rFull := rFullZeroLoc bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow aRem mRem sUb rAncZ
  have hBase := cleanRealizesReflInSliceDyn_scrUb bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid
    hsIn v
  have hEmb {w : ℕ} (sub : QRegister w (walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))) :
      (rMain.embedUnitary (QubitisedWalk.reflInUnitary sub)).1 =
        (2 : ℂ) • (rMain.compose sub).basisOutcomeProjector 0 - 1 := by
    change rMain.embedMatrix ((2 : ℂ) • sub.basisOutcomeProjector 0 - 1) = _
    rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_smul, QRegister.embedMatrix_one,
      CleanDyn.compose_basisOutcomeProjector]
  have hComm : (rMain.embedUnitary (QubitisedWalk.reflInUnitary refl.inAll)).1 *
      rUbZero.basisOutcomeProjector 0 =
      rUbZero.basisOutcomeProjector 0 *
        (rMain.embedUnitary (QubitisedWalk.reflInUnitary refl.inAll)).1 := by
    rw [hEmb, SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
      SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      smul_mul_assoc, mul_smul_comm, SelectSwapQROM.zeroProjOn_mul_union,
      Finset.union_comm, ← SelectSwapQROM.zeroProjOn_mul_union]
  have hDisjScr : Disjoint rMain.image rScr.image :=
    SelectSwapQROM.disjoint_image_of_disjointWires
      (rWalkCatLoc_disjoint_rScrLoc bQPE 11 (mOutUB wOuter) (mMidUB wInner2) mLow aRem mRem sUb)
  have hCov2 := (combWalkReflCovers bQPE 11 wOuter wInner2 mLow sUb ko km hkOut hkMid).2
  have hUnionEq : (rMain.compose refl.inAll).image ∪ rUbZero.image =
      (rMain.compose (inAllWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))).image ∪ rUbZero.image := by
    ext w
    have hNotScr {k : ℕ} (sub : QRegister k _) (hw : w ∈ (rMain.compose sub).image) :
        w ∉ rScr.image := fun hs ↦
      Finset.disjoint_left.mp hDisjScr (rMain.image_compose_subset sub hw) hs
    have hCovW := Finset.ext_iff.mp hCov2 w
    rw [Finset.mem_union, Finset.mem_union, image_rFullZeroLoc, Finset.mem_union] at hCovW
    rw [Finset.mem_union, Finset.mem_union, image_rUbZeroLoc, Finset.mem_union]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rcases h with hw | (hs | ha)
      · rcases hCovW.mp (Or.inl hw) with hi | (hs | ha)
        · exact Or.inl hi
        · exact absurd hs (hNotScr _ hw)
        · exact Or.inr (Or.inr ha)
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr ha)
    · rcases h with hi | (hs | ha)
      · rcases hCovW.mpr (Or.inl hi) with hw | (hs | ha)
        · exact Or.inl hw
        · exact absurd hs (hNotScr _ hi)
        · exact Or.inr (Or.inr ha)
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr ha)
  have hAbs : XMeasCircuit.CleanRealizes v rMain rUbZero
      (QubitisedWalk.reflInUnitary (inAllWalkCat 11 (mOutUB wOuter) (mMidUB wInner2)))
      (reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid hsIn v) := by
    refine (XMeasCircuit.CleanRealizes.absorbCleanActive hBase
      (by rw [image_rUbZeroLoc]; exact Finset.subset_union_left) rfl
      (by rw [← Matrix.mul_assoc, ← hComm, Matrix.mul_assoc,
            rUbZero.basisOutcomeProjector_mul_self 0])).congrUnitary ?_
    rw [hEmb, hEmb, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, smul_mul_assoc, smul_mul_assoc,
      SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
      SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
      SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
      SelectSwapQROM.zeroProjOn_mul_union, SelectSwapQROM.zeroProjOn_mul_union, hUnionEq]
  have hSet := (SelectSwapQROM.cleanRealizes_iff_set v rMain rUbZero _ _).mp
    ((AliasPrep.cleanRealizes_sbx_iff _ _ _ _ _).mp hAbs)
  have hUbImg : rUbZero.image =
      ((rScrUb.image ∪ ((combMidRegB bQPE wOuter wInner2 ko km mLow sUb).compose
        (midZeroPrefixReg wInner2 km hkMid)).image) ∪
        ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).compose
          (outZeroPrefixReg wOuter ko hkOut)).image) := by
    dsimp only [rUbZero, rAncZ, rScrUb, combOutRegB, combMidRegB, combUBRegB,
      combScrUbRegAt, combWalkCatRegAt, aRem, mRem]
    rw [image_rUbZeroLoc, ← union_outMidZero_eq_rAncZeroLoc]
    ext w; simp only [Finset.mem_union]; tauto
  rwa [hUbImg] at hSet

theorem disjointReflInSliceDyn_bell {Var : Type}
    (bQPE wOuter wInner2 ko km mLow sUb kInner : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsInK : combARem wOuter wInner2 ko km - 2 ≤ kInner) (hsK : 1 + kInner ≤ sUb) (v : Var) :
    let rMain := combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb
    let rScrUb := combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb
    Disjoint (reflInSliceDyn bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid (by omega) v).support
      (((rMain.compose (rSysCatUB wOuter wInner2 11)).compose
        (QRegister.block 0 (2 * 58) (by decide))).image ∪ {rScrUb ⟨kInner, by omega⟩}) := by
  intro rMain rScrUb
  let refl := combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid
  let pl := reflInSlicePlace bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid (by omega)
  have hSupp := DynamicCircuit.support_onRegister_subset pl
    (reflInLocDyn (combARem wOuter wInner2 ko km) refl.haPos v)
  refine Finset.disjoint_of_subset_left hSupp (Finset.disjoint_left.mpr fun w hw hU ↦ ?_)
  have hw' : w ∈ (rMain.compose refl.inAll).image ∪
      (rScrUb.slice 0 (combARem wOuter wInner2 ko km - 2) (by omega)).image := by
    simpa only [pl, reflInSlicePlace, QRegister.image_concat] using hw
  have hMainScr := combWalkCatRegB_disjoint_scr bQPE wOuter wInner2 ko km mLow sUb
  rcases Finset.mem_union.mp hw' with hA | hS
  · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hA
    rcases Finset.mem_union.mp hU with hSys | hDst
    · obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hSys
      let rSys116 := (rSysCatUB wOuter wInner2 11).compose (QRegister.block 0 (2 * 58) (by decide))
      have hv := congrArg Fin.val (rMain.wires.injective hj : rSys116 j = refl.inAll i)
      have hjLt : (rSys116 j).val < 2 * 58 := by
        dsimp only [rSys116]
        have h1 : (QRegister.block 0 (2 * 58) (by decide) j : Fin (2 * 58 + 11)) =
            Fin.castAdd 11 j := Fin.ext (Nat.zero_add j.val)
        simp only [QRegister.compose_apply, h1, rSysCatUB, QRegister.concat_apply_left,
          rUBInCat, rSysUB, QRegister.block_apply_val, zero_add]
        exact j.isLt
      have hiGe : 2 * 58 ≤ (refl.inAll i).val := by
        dsimp only [refl, combWalkReflRegs, reducedOutMidWalkReflRegs]
        have hsys : systemQubits_local = 2 * 58 := rfl
        rcases finSumFinEquiv.surjective i with ⟨io | im, rfl⟩ <;>
          simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, QRegister.compose_apply,
            QRegister.concat_apply_left, QRegister.concat_apply_right, rWalkInWalkCat,
            rOutInWalk, rMidInWalk, QRegister.block_apply_val, zero_add] <;>
          omega
      omega
    · rw [Finset.mem_singleton] at hDst
      exact hMainScr.ne (refl.inAll i) ⟨kInner, by omega⟩ hDst
  · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hS
    rcases Finset.mem_union.mp hU with hSys | hDst
    · obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hSys
      exact hMainScr.ne _ _ hj
    · rw [Finset.mem_singleton, QRegister.slice_apply] at hDst
      have hv := congrArg Fin.val (rScrUb.wires.injective hDst)
      dsimp only at hv; have := i.isLt; omega

/-! ## Section 4: Five-Step CSwap Sandwich & `bellSuperRefl2CoreDyn` Circuit / Gate Counts -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellPersistCore
end

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearSuperPhase5
open QuantumComputation.Specs QuantumComputation.Specs.P450
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearSuperPhase5
