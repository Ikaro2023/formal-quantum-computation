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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.ThreeGearBellSuper

/-!
# Asymmetric & `D_neg` Bell-Persistent 5-Step Core & `BellAsymLegs` (`0 < wInner2`, `kPark = 0`)

Provides diagonal-phase pull-through identities (`pull_fwd_dneg`, `pull_bwd_dneg`), Bell
forbidden-wire disjointness helpers (`bellForbidSet`, `disjoint_bell_onRegister_*_slice`),
3-step prefix `wp` congruence (`restrictZeroSet_wp_threeStepPrefix_congr`), 6-unitary asymmetric
5-step core realizations (`cleanRealizesSet_fiveStepCSwap_asym`,
`cleanRealizesSet_bellFiveStepNoNegCoreSliceDyn_asym`), and the `BellAsymLegs` bundle with
turnkey `ofDNeg` and `ofSym` constructors.

## References
- C. Jones, "Low-overhead constructions for the fault-tolerant Toffoli gate," *Phys. Rev. A* **87**,
  022328 (2013), DOI: `10.1103/PhysRevA.87.022328`.
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
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellAsymCore
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias Solution.CleanDyn AliasPrep
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution Solution.TwoGearBox
open Solution.CircuitModular Solution.BlockEncodingCore
open Solution.BlockEncodingCircuit Solution.SelectSwapQROM
open Solution.TopIntegrationBridge Solution.Lac2Fused184Select Solution.Phase2MidSandwich
open Solution.MidReflCtxRetain
open Solution.PolymorphicFused184Select Solution.ReordOuter13Bridge
open Solution.CompactStepFast176Select hiding blockRemWidth
  outRemWidth midRemWidth combARem
open Solution.CompactOuter9Bound50Core Solution.CompactTuned162StepWalk
open Solution.MobiusOptSubcube163Walk
  (ubCustomMuxCatUnitary outerSandwich_eq_reflPulledPair_customMux)
open Solution.CompactTuned162StepZeroCmp20 Solution.CompactZeroCmp20OuterParam
open Solution.OneHotSimulates Solution.LowBitPi145Select Solution.BellPhaseASelect
open Solution.BellSingletCSwap58
open Solution.Cat11CompactPhase2Bridge Solution.DihedralWalkQPE
open Solution.DihedralWalkQPE.MultiGearQPE
open Solution.DihedralWalkQPE.BlockReflection Solution.TwoGearQPEPhase5
open Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open Solution.WalkQPEBridgeXMeas hiding
  image_rFullZeroLoc rFullZeroLoc
open Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open Solution.BellRouter57 Solution.CompactCore145Bundle Solution.BellPersistNoNeg
open Solution.BellSelectNoNegPair Solution.Select57Slices Solution.BellPersistCore
open Solution.BellPersistSuperWalk Solution.BellSuperNoNegWalk Solution.TwoGearSuperPhase5
open Solution.ThreeGearBellSuper

local instance instNeZeroTwoPowAsymCore (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: Pull-Through Identities & Bell Disjointness Helpers -/

/-- Combined scratch + inner-zero-prefix wire set inside `combQubitsAt`. -/
abbrev scrMidZeroSet (bQPE wOuter wInner2 ko km mLow sUb : ℕ) (hkMid : km ≤ wInner2) :
    Finset (Wire (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) :=
  (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image ∪
    ((combMidRegB bQPE wOuter wInner2 ko km mLow sUb).compose
      (midZeroPrefixReg wInner2 km hkMid)).image

/-- Combined scratch + outer-zero-prefix wire set inside `combQubitsAt`. -/
abbrev scrOutZeroSet (bQPE wOuter wInner2 ko km mLow sUb : ℕ) (hkOut : ko ≤ wOuter) :
    Finset (Wire (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) :=
  (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image ∪
    ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).compose
      (outZeroPrefixReg wOuter ko hkOut)).image

/-- Forbidden `117`-wire set (`116` system wires ∪ Bell singlet wire `rScrUb ⟨kInner, _⟩`). -/
abbrev bellForbidSet (bQPE wOuter wInner2 ko km mLow sUb kInner : ℕ) (hs : 1 + kInner ≤ sUb) :
    Finset (Wire (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) :=
  ((((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).compose
    (rSysCatUB wOuter wInner2 11)).compose
    (QRegister.block 0 (2 * 58) (by decide))).image ∪
    {(combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb) ⟨kInner, by omega⟩})

theorem embed_pull_of_cat {N wOuter wInner2 : ℕ} (rMain : QRegister (nUB wOuter wInner2 + 11) N)
    {M_pre M_post M_eff : Unitary (2 ^ nUB wOuter wInner2)}
    {s_raw s_eff : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    (hCat : s_raw * (rUBInCat wOuter wInner2 11).embedUnitary M_pre =
      (rUBInCat wOuter wInner2 11).embedUnitary M_post *
        ((rUBInCat wOuter wInner2 11).embedUnitary M_eff⁻¹ * s_eff *
          (rUBInCat wOuter wInner2 11).embedUnitary M_eff)) :
    rMain.embedUnitary s_raw * (rMain.compose (rUBInCat wOuter wInner2 11)).embedUnitary M_pre =
      (rMain.compose (rUBInCat wOuter wInner2 11)).embedUnitary M_post *
        rMain.embedUnitary ((rUBInCat wOuter wInner2 11).embedUnitary M_eff⁻¹ * s_eff *
          (rUBInCat wOuter wInner2 11).embedUnitary M_eff) := by
  rw [QRegister.embedUnitary_compose, QRegister.embedUnitary_compose,
    ← QRegister.embedUnitary_mul, ← QRegister.embedUnitary_mul, hCat]

theorem pull_fwd_dneg {N wOuter wInner2 : ℕ} (rMain : QRegister (nUB wOuter wInner2 + 11) N)
    (M_fwd D_neg : Unitary (2 ^ nUB wOuter wInner2)) (raw_4 : Unitary (2 ^ (nUB wOuter wInner2 +
      11)))
    (hDInv : D_neg⁻¹ = D_neg) :
    let D_cat := (rUBInCat wOuter wInner2 11).embedUnitary D_neg
    rMain.embedUnitary raw_4 * (rMain.compose (rUBInCat wOuter wInner2 11)).embedUnitary M_fwd =
      (rMain.compose (rUBInCat wOuter wInner2 11)).embedUnitary (D_neg * M_fwd) *
        rMain.embedUnitary ((rUBInCat wOuter wInner2 11).embedUnitary M_fwd⁻¹ * (D_cat * raw_4) *
          (rUBInCat wOuter wInner2 11).embedUnitary M_fwd) := by
  intro D_cat
  refine embed_pull_of_cat rMain ?_
  let eM := (rUBInCat wOuter wInner2 11).embedUnitary M_fwd
  have heDInv : D_cat⁻¹ = D_cat := by
    dsimp only [D_cat]
    rw [← QRegister.embedUnitary_inv, hDInv]
  have heD2 : D_cat * D_cat = 1 := by
    nth_rw 1 [← heDInv]
    exact inv_mul_cancel D_cat
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_inv]
  symm
  calc (D_cat * eM) * (eM⁻¹ * (D_cat * raw_4) * eM)
      = D_cat * ((eM * eM⁻¹) * (D_cat * (raw_4 * eM))) := by simp only [mul_assoc]
    _ = (D_cat * D_cat) * (raw_4 * eM) := by rw [mul_inv_cancel, one_mul, ← mul_assoc]
    _ = raw_4 * eM := by rw [heD2, one_mul]

theorem pull_bwd_dneg {N wOuter wInner2 : ℕ} (rMain : QRegister (nUB wOuter wInner2 + 11) N)
    (M_bwd D_neg : Unitary (2 ^ nUB wOuter wInner2)) (raw_3 : Unitary (2 ^ (nUB wOuter wInner2 +
      11))) :
    let D_cat := (rUBInCat wOuter wInner2 11).embedUnitary D_neg
    rMain.embedUnitary raw_3 *
        (rMain.compose (rUBInCat wOuter wInner2 11)).embedUnitary (D_neg * M_bwd) =
      (rMain.compose (rUBInCat wOuter wInner2 11)).embedUnitary M_bwd *
        rMain.embedUnitary ((rUBInCat wOuter wInner2 11).embedUnitary M_bwd⁻¹ * (raw_3 * D_cat) *
          (rUBInCat wOuter wInner2 11).embedUnitary M_bwd) := by
  intro D_cat
  refine embed_pull_of_cat rMain ?_
  let eM := (rUBInCat wOuter wInner2 11).embedUnitary M_bwd
  rw [QRegister.embedUnitary_mul, QRegister.embedUnitary_inv]
  symm
  calc eM * (eM⁻¹ * (raw_3 * D_cat) * eM)
      = (eM * eM⁻¹) * (raw_3 * (D_cat * eM)) := by simp only [mul_assoc]
    _ = raw_3 * (D_cat * eM) := by rw [mul_inv_cancel, one_mul]

theorem disjoint_bell_of_support_subset {Var :
    Type} {bQPE wOuter wInner2 ko km mLow sUb kInner kScr : ℕ}
    (hkScr : kScr ≤ kInner) (hs : 1 + kInner ≤ sUb) (hScr : 0 + kScr ≤ sUb)
    {P : DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (hSupp : P.support ⊆
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).compose
        (rAllInCat wOuter wInner2 11)).image ∪
        ((combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).slice 0 kScr hScr).image) :
    Disjoint P.support (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb kInner hs) := by
  let rMain := combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb
  let rScrUb := combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb
  have hMainScr := combWalkCatRegB_disjoint_scr bQPE wOuter wInner2 ko km mLow sUb
  refine Finset.disjoint_of_subset_left hSupp (Finset.disjoint_left.mpr fun w hw hF ↦ ?_)
  rcases Finset.mem_union.mp hw with hAll | hS
  · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hAll
    rcases Finset.mem_union.mp hF with hSys | hDst
    · obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hSys
      exact (disjoint_rAllInCat_rSysCatUB wOuter wInner2 11).ne i _ (rMain.wires.injective hj.symm)
    · rw [Finset.mem_singleton] at hDst
      exact hMainScr.ne (rAllInCat wOuter wInner2 11 i) ⟨kInner, by omega⟩ hDst
  · obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hS
    rcases Finset.mem_union.mp hF with hSys | hDst
    · obtain ⟨j, hj⟩ := (QRegister.mem_image _ _).mp hSys
      exact hMainScr.ne _ _ hj
    · rw [Finset.mem_singleton, QRegister.slice_apply] at hDst
      have hv := congrArg Fin.val (rScrUb.wires.injective hDst)
      dsimp only at hv
      have := i.isLt
      omega

theorem imageCombOutRegB_subset_rAllInCat {bQPE wOuter wInner2 ko km mLow sUb : ℕ} :
    (combOutRegB bQPE wOuter wInner2 ko km mLow sUb).image ⊆
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).compose
          (rAllInCat wOuter wInner2 11)).image := by
  intro w hw
  obtain ⟨i, rfl⟩ := (QRegister.mem_image _ _).mp hw
  refine (QRegister.mem_image _ _).mpr ⟨⟨i.val, by
    dsimp [mAncUB]
    omega⟩, ?_⟩
  dsimp only [rAllInCat, combOutRegB, combUBRegB, QRegister.compose_apply]
  exact congrArg _ (congrArg _ (Fin.ext rfl))

theorem disjoint_bell_onRegister_out_slice {Var : Type}
    {bQPE wOuter wInner2 ko km mLow sUb kInner kScr : ℕ}
    (hkScr : kScr ≤ kInner) (hs : 1 + kInner ≤ sUb) (hScr : 0 + kScr ≤ sUb)
    (hDisj : (combOutRegB bQPE wOuter wInner2 ko km mLow sUb).DisjointWires
      ((combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).slice 0 kScr hScr))
    (P_loc : DynamicCircuit Var (mOutUB wOuter + kScr)) :
    Disjoint (P_loc.onRegister
      ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).concat
        ((combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).slice 0 kScr hScr) hDisj)).support
      (bellForbidSet bQPE wOuter wInner2 ko km mLow sUb kInner hs) :=
  disjoint_bell_of_support_subset hkScr hs hScr ((DynamicCircuit.support_onRegister_subset _
    P_loc).trans (by
      rw [QRegister.image_concat]
      exact Finset.union_subset_union_left imageCombOutRegB_subset_rAllInCat))

/-! ## Section 2: Asymmetric 5-Step Core Realization & `BellAsymLegs` -/

theorem restrictZeroSet_wp_threeStepPrefix_congr {Var : Type} [Fintype Var] [DecidableEq Var]
    {N : ℕ} {v : Var} {S₀ S : Finset (Wire N)} (hSub : S₀ ⊆ S)
    {W_M1_pre W_M1_post W_M2_pre U_s1 U_in1 U_R : Unitary (2 ^ N)}
    {P_1 selF P_turn : DynamicCircuit Var N}
    (h1 : CleanRealizesSet v S₀ W_M1_pre P_1) (hs1 : CleanRealizesSet v S₀ U_s1 selF)
    (hTurn : CleanTurnaroundWp v S W_M1_post (W_M2_pre * U_R) P_turn)
    (hW2 : W_M2_pre.1 * zeroProjOn S₀ = zeroProjOn S₀ * W_M2_pre.1)
    (hPull1 : U_s1 * W_M1_pre = W_M1_post * U_in1)
    (hPres1 : AliasPrep.PreservesWires U_in1.1 S)
    (hPresR : AliasPrep.PreservesWires U_R.1 S)
    {X₁ X₂ : QCAssertion Var (2 ^ N)}
    (hX1 : ∀ σ val, X₁ (Function.update σ v val) = X₁ σ)
    (hX2 : ∀ σ val, X₂ (Function.update σ v val) = X₂ σ)
    (hEq0 : SelectSwapQROM.restrictZeroSet X₁ S₀ = SelectSwapQROM.restrictZeroSet X₂ S₀) :
    SelectSwapQROM.restrictZeroSet
      (wp P_1.compile (wp selF.compile (wp P_turn.compile X₁))) S =
    SelectSwapQROM.restrictZeroSet
      (wp P_1.compile (wp selF.compile (wp P_turn.compile X₂))) S := by
  have hc1 := AliasPrep.preservesWires_comm_zeroProjOn hPres1 Finset.Subset.rfl
  have hcR := AliasPrep.preservesWires_comm_zeroProjOn hPresR Finset.Subset.rfl
  have hEv {X : QCAssertion Var (2 ^ N)} (hX : ∀ σ val, X (Function.update σ v val) = X σ) :
      SelectSwapQROM.restrictZeroSet
        (wp P_1.compile (wp selF.compile (wp P_turn.compile X))) S =
      qcWpQAssign U_in1 (qcWpQAssign U_R
        (SelectSwapQROM.restrictZeroSet (qcWpQAssign W_M2_pre X) S)) := by
    change SelectSwapQROM.restrictZeroSet
      (wp (DynamicCircuit.seq P_1 selF).compile (wp P_turn.compile X)) S = _
    rw [restrictZeroSet_eq_of_subset hSub ((h1.seq hs1).2.2.1 _ (hTurn.2.1 X hX)),
      hPull1, ← qc_wp_qAssign_comp, restrictZeroSet_qcWpQAssign_comm hc1, hTurn.2.2 X hX,
      ← qc_wp_qAssign_comp, restrictZeroSet_qcWpQAssign_comm hcR]
  have hMid : SelectSwapQROM.restrictZeroSet (qcWpQAssign W_M2_pre X₁) S =
      SelectSwapQROM.restrictZeroSet (qcWpQAssign W_M2_pre X₂) S :=
    restrictZeroSet_eq_of_subset hSub (by
      rw [restrictZeroSet_qcWpQAssign_comm hW2, hEq0, ← restrictZeroSet_qcWpQAssign_comm hW2])
  rw [hEv hX1, hMid, ← hEv hX2]

theorem cleanRealizesSet_fiveStepCSwap_asym {Var : Type} [Fintype Var] [DecidableEq Var]
    {N sUb kClean wOuter wInner2 : ℕ} {v : Var} (rMain : QRegister (nUB wOuter wInner2 + 11) N)
    (rScrUb : QRegister sUb N) (rClean : QRegister kClean N) (hSub : rScrUb.image ⊆ rClean.image)
    (W_M1_pre W_M1_post W_M2_pre W_M2_post U_s1 U_s2 : Unitary (2 ^ N))
    (u_in1 u_in2 R_cat : Unitary (2 ^ (nUB wOuter wInner2 + 11)))
    {P_1 selF P_turn selB P_4 : DynamicCircuit Var N}
    (h1 : CleanRealizesSet v rScrUb.image W_M1_pre P_1)
    (hs1 : CleanRealizesSet v rScrUb.image U_s1 selF)
    (hTurn : CleanTurnaroundWp v rClean.image W_M1_post (W_M2_pre * rMain.embedUnitary R_cat)
      P_turn)
    (hs2 : CleanRealizesSet v rScrUb.image U_s2 selB)
    (h4 : CleanUnloadsWp v rClean.image W_M2_post P_4)
    (hW2_sel : W_M2_pre.1 * zeroProjOn rScrUb.image = zeroProjOn rScrUb.image * W_M2_pre.1)
    (hPull1 : U_s1 * W_M1_pre = W_M1_post * rMain.embedUnitary u_in1)
    (hPull2 : U_s2 * W_M2_pre = W_M2_post * rMain.embedUnitary u_in2)
    (hPres1 : AliasPrep.PreservesWires (rMain.embedUnitary u_in1).1 rClean.image)
    (hPresR : AliasPrep.PreservesWires (rMain.embedUnitary R_cat).1 rClean.image)
    (hPres2 : AliasPrep.PreservesWires (rMain.embedUnitary u_in2).1 rClean.image) :
    CleanRealizesSet v rClean.image (rMain.embedUnitary (u_in2 * R_cat * u_in1))
      (.seq P_1 (.seq (.seq selF (.seq P_turn selB)) P_4)) := by
  have hcV1 := AliasPrep.preservesWires_comm_zeroProjOn hPres1 Finset.Subset.rfl
  have hcRN := AliasPrep.preservesWires_comm_zeroProjOn hPresR Finset.Subset.rfl
  have hcV2 := AliasPrep.preservesWires_comm_zeroProjOn hPres2 Finset.Subset.rfl
  have hInnerPres : AliasPrep.PreservesWires
      (rMain.embedUnitary (u_in2 * R_cat * u_in1)).1 rClean.image := by
    rw [rMain.embedUnitary_mul, rMain.embedUnitary_mul]
    exact AliasPrep.preservesWires_mul (AliasPrep.preservesWires_mul hPres2 hPresR) hPres1
  have hcInner := AliasPrep.preservesWires_comm_zeroProjOn hInnerPres Finset.Subset.rfl
  have hCR : Solution.XMeasCircuit.CleanRealizes v rMain rClean (u_in2 * R_cat * u_in1)
      (.seq P_1 (.seq (.seq selF (.seq P_turn selB)) P_4)) := by
    refine Solution.XMeasCircuit.CleanRealizes.mkOfWpClean
      (by simp [DynamicCircuit.count, h1.1, hs1.1, hTurn.1, hs2.1, h4.1])
      (fun Θ hΘ σ val ↦ h1.2.1 _ (hs1.2.1 _ (hTurn.2.1 _ (hs2.2.1 _ (h4.2.1 Θ hΘ)))) σ val)
      (fun Θ hΘ ↦ ?_) ?_
    · rw [SelectSwapQROM.restrictAssertionToZeroAncilla_eq_restrictZeroSet,
        SelectSwapQROM.restrictAssertionToZeroAncilla_eq_restrictZeroSet]
      let Ψ5 := wp P_4.compile Θ
      have hΨ5 := h4.2.1 Θ hΘ
      let B_c := wp selB.compile Ψ5
      have hBcV := hs2.2.1 Ψ5 hΨ5
      have hAssoc : wp (DynamicCircuit.seq P_1 (.seq (.seq selF (.seq P_turn selB)) P_4)).compile Θ
          = wp (DynamicCircuit.seq P_1 selF).compile (wp P_turn.compile B_c) := by
        dsimp only [B_c, Ψ5]
        simp only [wp_seq_compile]
      have hStep4 : SelectSwapQROM.restrictZeroSet (qcWpQAssign W_M2_pre B_c) rClean.image =
          SelectSwapQROM.restrictZeroSet (qcWpQAssign (U_s2 * W_M2_pre) Ψ5) rClean.image :=
        restrictZeroSet_eq_of_subset hSub (by
          rw [restrictZeroSet_qcWpQAssign_comm hW2_sel, hs2.2.2.1 Ψ5 hΨ5,
            ← restrictZeroSet_qcWpQAssign_comm hW2_sel, qc_wp_qAssign_comp])
      rw [hAssoc, restrictZeroSet_eq_of_subset hSub ((h1.seq hs1).2.2.1 _ (hTurn.2.1 B_c hBcV)),
        hPull1, ← qc_wp_qAssign_comp, restrictZeroSet_qcWpQAssign_comm hcV1, hTurn.2.2 B_c hBcV,
        ← qc_wp_qAssign_comp, restrictZeroSet_qcWpQAssign_comm hcRN, hStep4, hPull2,
        ← qc_wp_qAssign_comp, restrictZeroSet_qcWpQAssign_comm hcV2, h4.2.2 Θ hΘ,
        ← restrictZeroSet_qcWpQAssign_comm hcV2, ← restrictZeroSet_qcWpQAssign_comm hcRN,
        ← restrictZeroSet_qcWpQAssign_comm hcV1, qc_wp_qAssign_comp, qc_wp_qAssign_comp,
        ← rMain.embedUnitary_mul, ← rMain.embedUnitary_mul, ← mul_assoc]
    · rw [SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn, ← Matrix.mul_assoc,
        ← hcInner, Matrix.mul_assoc, SelectSwapQROM.zeroProjOn_mul_self]
  rw [← SelectSwapQROM.cleanRealizes_iff_set]
  exact (AliasPrep.cleanRealizes_sbx_iff _ _ _ _ _).mp hCR

theorem cleanRealizesSet_bellFiveStepNoNegCoreSliceDyn_asym {Var : Type} [Fintype Var]
    [DecidableEq Var] {N kInner tCoreF tCoreB sUb kClean : ℕ} (hk7 : 7 ≤ kInner)
    {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF) (bundleB :
      GenCore145Bundle kInner tCoreB branchB)
    (stepsA stepsBF stepsBB : List (RouterStep 23)) (specA : (Fin 16 → Bool) → State24)
    (specBF specBB : State24 → State24)
    (hRunA : ∀ x16, runSteps24 hk23Le24 stepsA (initState23 x16) = some (specA x16))
    (hRunBF : ∀ x16, runSteps24 hk23Le24 stepsBF (specA x16) = some (specBF (specA x16)))
    (hBorBF : ∀ x16 (k : Fin 6), (specBF (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145F : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specBF (specA x16))) < 145)
    (hRunBB : ∀ x16, runSteps24 hk23Le24 stepsBB (specA x16) = some (specBB (specA x16)))
    (hBorBB : ∀ x16 (k : Fin 6), (specBB (specA x16)).get24 ⟨17 + k.val, by omega⟩ = false)
    (h145B : ∀ x16, pair8NatOf10 (ctrl10OfState24 (specBB (specA x16))) < 145)
    (hs : 1 + kInner ≤ sUb) (v : Var) (wOuter wInner2 : ℕ) (hGiPos : 0 < wInner2)
    (rMain : QRegister (nUB wOuter wInner2 + 11) N) (rScrUb : QRegister sUb N)
    (rClean : QRegister kClean N) (hdisj : rMain.DisjointWires rScrUb)
    (hSub : rScrUb.image ⊆ rClean.image)
    (W_M1_pre W_M1_post W_M2_pre W_M2_post U_s1 U_s2 : Unitary (2 ^ N))
    (u_in1 u_in2 R_cat : Unitary (2 ^ (nUB wOuter wInner2 + 11)))
    {P_1 P_turn P_4 : DynamicCircuit Var N}
    (h1 : CleanRealizesSet v rScrUb.image W_M1_pre P_1)
    (hs1 : CleanRealizesSet v rScrUb.image U_s1
      (selectLowBitNoNegCoreSliceDyn bundleF stepsA stepsBF hs v wOuter wInner2 hGiPos rMain
        rScrUb))
    (hTurn : CleanTurnaroundWp v rClean.image W_M1_post (W_M2_pre * rMain.embedUnitary R_cat)
      P_turn)
    (hs2 : CleanRealizesSet v rScrUb.image U_s2
      (selectLowBitNoNegCoreSliceDyn bundleB stepsA stepsBB hs v wOuter wInner2 hGiPos rMain
        rScrUb))
    (h4 : CleanUnloadsWp v rClean.image W_M2_post P_4)
    (hW2_sel : W_M2_pre.1 * zeroProjOn rScrUb.image = zeroProjOn rScrUb.image * W_M2_pre.1)
    (hPull1 : U_s1 * W_M1_pre = W_M1_post * rMain.embedUnitary u_in1)
    (hPull2 : U_s2 * W_M2_pre = W_M2_post * rMain.embedUnitary u_in2)
    (hPres1 : AliasPrep.PreservesWires (rMain.embedUnitary u_in1).1 rClean.image)
    (hPresR : AliasPrep.PreservesWires (rMain.embedUnitary R_cat).1 rClean.image)
    (hPres2 : AliasPrep.PreservesWires (rMain.embedUnitary u_in2).1 rClean.image)
    (hTurnSupp : Disjoint P_turn.support
      (((rMain.compose (rSysCatUB wOuter wInner2 11)).compose
        (QRegister.block 0 (2 * 58) (by decide))).image ∪ {rScrUb ⟨kInner, by omega⟩})) :
    CleanRealizesSet v rClean.image (rMain.embedUnitary (u_in2 * R_cat * u_in1))
      (.seq P_1 (.seq (bellSelectNoNegCoreSlicePairDyn bundleF bundleB stepsA stepsBF stepsBB hs v
        wOuter
        wInner2 hGiPos rMain rScrUb P_turn) P_4)) := by
  let selF :=
    selectLowBitNoNegCoreSliceDyn bundleF stepsA stepsBF hs v wOuter wInner2 hGiPos rMain rScrUb
  let selB :=
    selectLowBitNoNegCoreSliceDyn bundleB stepsA stepsBB hs v wOuter wInner2 hGiPos rMain rScrUb
  have hCSw := cleanRealizesSet_fiveStepCSwap_asym rMain rScrUb rClean hSub W_M1_pre W_M1_post
    W_M2_pre W_M2_post U_s1 U_s2 u_in1 u_in2 R_cat h1 hs1 hTurn hs2 h4 hW2_sel hPull1 hPull2
    hPres1 hPresR hPres2
  have hInnerPres : AliasPrep.PreservesWires
      (rMain.embedUnitary (u_in2 * R_cat * u_in1)).1 rClean.image := by
    rw [rMain.embedUnitary_mul, rMain.embedUnitary_mul]
    exact AliasPrep.preservesWires_mul (AliasPrep.preservesWires_mul hPres2 hPresR) hPres1
  have hcInner := AliasPrep.preservesWires_comm_zeroProjOn hInnerPres Finset.Subset.rfl
  have hCR : Solution.XMeasCircuit.CleanRealizes v rMain rClean (u_in2 * R_cat * u_in1)
      (.seq P_1 (.seq (bellSelectNoNegCoreSlicePairDyn bundleF bundleB stepsA stepsBF stepsBB hs v
        wOuter
        wInner2 hGiPos rMain rScrUb P_turn) P_4)) := by
    refine Solution.XMeasCircuit.CleanRealizes.mkOfWpClean
      (by simp [DynamicCircuit.count, h1.1, hTurn.1, h4.1])
      (fun Θ hΘ σ val ↦
        h1.2.1 _ (preservesVInv_bellSelectNoNegCoreSlicePairDyn bundleF bundleB stepsA
        stepsBF stepsBB hs v wOuter wInner2 hGiPos rMain rScrUb hTurn.2.1 _ (h4.2.1 Θ hΘ)) σ val)
      (fun Θ hΘ ↦ ?_) ?_
    · rw [SelectSwapQROM.restrictAssertionToZeroAncilla_eq_restrictZeroSet,
        SelectSwapQROM.restrictAssertionToZeroAncilla_eq_restrictZeroSet]
      let Ψ5 := wp P_4.compile Θ
      have hΨ5 := h4.2.1 Θ hΘ
      obtain ⟨B_c, hBcV, hBcEq, hMidEq⟩ := restrictZeroSet_wp_bellNoNegCoreSlicePair_eq_mid hk7
        bundleF bundleB stepsA stepsBF stepsBB specA specBF specBB hRunA hRunBF hBorBF h145F hRunBB
        hBorBB h145B hs v wOuter wInner2 hGiPos rMain rScrUb hdisj hTurnSupp hTurn.2.1 Ψ5 hΨ5
      have hP1 : SelectSwapQROM.restrictZeroSet
          (wp (DynamicCircuit.seq P_1 (.seq (bellSelectNoNegCoreSlicePairDyn bundleF bundleB stepsA
            stepsBF stepsBB hs v wOuter wInner2 hGiPos rMain rScrUb P_turn) P_4)).compile Θ)
              rClean.image =
          SelectSwapQROM.restrictZeroSet
            (wp P_1.compile (wp selF.compile (wp P_turn.compile B_c))) rClean.image := by
        simp only [wp_seq_compile]
        exact restrictZeroSet_eq_of_subset hSub (by rw [← h1.2.2.2, hMidEq, h1.2.2.2])
      have hCSwEq := hCSw.2.2.1 Θ hΘ
      dsimp only [Ψ5] at hBcEq hP1 ⊢
      simp only [wp_seq_compile] at hCSwEq
      exact (hP1.trans (restrictZeroSet_wp_threeStepPrefix_congr hSub h1 hs1 hTurn hW2_sel hPull1
        hPres1 hPresR hBcV (hs2.2.1 _ hΨ5) hBcEq)).trans hCSwEq
    · rw [SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn, ← Matrix.mul_assoc,
        ← hcInner, Matrix.mul_assoc, SelectSwapQROM.zeroProjOn_mul_self]
  rw [← SelectSwapQROM.cleanRealizes_iff_set]
  exact (AliasPrep.cleanRealizes_sbx_iff _ _ _ _ _).mp hCR

theorem pull_sym {N wOuter wInner2 : ℕ} (rMain : QRegister (nUB wOuter wInner2 + 11) N)
    (M : Unitary (2 ^ nUB wOuter wInner2)) (s : Unitary (2 ^ (nUB wOuter wInner2 + 11))) :
    rMain.embedUnitary s * (rMain.compose (rUBInCat wOuter wInner2 11)).embedUnitary M =
      (rMain.compose (rUBInCat wOuter wInner2 11)).embedUnitary M *
        rMain.embedUnitary ((rUBInCat wOuter wInner2 11).embedUnitary M⁻¹ * s *
          (rUBInCat wOuter wInner2 11).embedUnitary M) :=
  embed_pull_of_cat rMain (by
    let eM := (rUBInCat wOuter wInner2 11).embedUnitary M
    rw [QRegister.embedUnitary_inv]
    symm
    calc eM * (eM⁻¹ * s * eM) = (eM * eM⁻¹) * (s * eM) := by simp only [mul_assoc]
      _ = s * eM := by rw [mul_inv_cancel, one_mul])

/-- Bundled 5-leg realization & pull-through hypotheses for asymmetric `(M_1_pre, M_1_post,
M_2_pre, M_2_post)` Bell walk reflections on `combQubitsAt`. -/
def BellAsymLegs (Var : Type) [Fintype Var] [DecidableEq Var]
    (bQPE wOuter wInner2 ko km mLow sUb : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (v : Var)
    (prepOutImpl : Unitary (2 ^ mOutUB wOuter)) (M_fwd M_bwd : Unitary (2 ^ nUB wOuter wInner2))
    (raw_4 raw_3 sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11)))
    (pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) : Prop :=
  ∃ M_1_pre M_1_post M_2_pre M_2_post : Unitary (2 ^ nUB wOuter wInner2),
    Solution.CleanDyn.CleanRealizes v (combOutRegB bQPE wOuter wInner2 ko km mLow sUb)
      (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb) prepOutImpl pOutFwd ∧
    CleanUnloadsWp v (scrOutZeroSet bQPE wOuter wInner2 ko km mLow sUb hkOut)
      ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary prepOutImpl) pOutBwd ∧
    OuterConjPreservesZero wOuter ko hkOut prepOutImpl ∧
    CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_1_pre) P_1 ∧
    CleanTurnaroundWp v (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_1_post)
      (((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_2_pre) *
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
          (QubitisedWalk.reflMidUnitary (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2)))) pTurn ∧
    CleanUnloadsWp v (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_2_post) P_4 ∧
    (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_4 *
        (combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_1_pre =
      (combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_1_post *
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
          ((rUBInCat wOuter wInner2 11).embedUnitary M_fwd⁻¹ * sF *
            (rUBInCat wOuter wInner2 11).embedUnitary M_fwd) ∧
    (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_3 *
        (combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_2_pre =
      (combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_2_post *
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
          ((rUBInCat wOuter wInner2 11).embedUnitary M_bwd⁻¹ * sB *
            (rUBInCat wOuter wInner2 11).embedUnitary M_bwd) ∧
    PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        ((rUBInCat wOuter wInner2 11).embedUnitary M_fwd⁻¹ * sF *
          (rUBInCat wOuter wInner2 11).embedUnitary M_fwd)).1
      (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid) ∧
    PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        ((rUBInCat wOuter wInner2 11).embedUnitary M_bwd⁻¹ * sB *
          (rUBInCat wOuter wInner2 11).embedUnitary M_bwd)).1
      (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid) ∧
    PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        (innerMidCoreUnitary M_fwd M_bwd sF sB)).1
      ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).image ∪
        scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)

/-- General 6-unitary constructor for `BellAsymLegs` given `(M_1_pre, M_1_post, M_2_pre, M_2_post)`
and explicit pull-through identities `(hPull1, hPull2)`. -/
theorem BellAsymLegs.mk {Var : Type} [Fintype Var] [DecidableEq Var]
    {bQPE wOuter wInner2 ko km mLow sUb : ℕ} {hkOut : ko ≤ wOuter} {hkMid : km ≤ wInner2} {v : Var}
    {prepOutImpl : Unitary (2 ^ mOutUB wOuter)} {M_fwd M_bwd : Unitary (2 ^ nUB wOuter wInner2)}
    {raw_4 raw_3 sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11))}
    {pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (M_1_pre M_1_post M_2_pre M_2_post : Unitary (2 ^ nUB wOuter wInner2))
    (hFwd : Solution.CleanDyn.CleanRealizes v (combOutRegB bQPE wOuter wInner2 ko km mLow sUb)
      (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb) prepOutImpl pOutFwd)
    (hBwd : CleanUnloadsWp v (scrOutZeroSet bQPE wOuter wInner2 ko km mLow sUb hkOut)
      ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary prepOutImpl) pOutBwd)
    (hConj : OuterConjPreservesZero wOuter ko hkOut prepOutImpl)
    (h1 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_1_pre) P_1)
    (hTurn : CleanTurnaroundWp v (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_1_post)
      (((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_2_pre) *
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
          (QubitisedWalk.reflMidUnitary (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2)))) pTurn)
    (h4 : CleanUnloadsWp v (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_2_post) P_4)
    (hPull1 : (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_4 *
        (combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_1_pre =
      (combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_1_post *
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
          ((rUBInCat wOuter wInner2 11).embedUnitary M_fwd⁻¹ * sF *
            (rUBInCat wOuter wInner2 11).embedUnitary M_fwd))
    (hPull2 : (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary raw_3 *
        (combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_2_pre =
      (combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_2_post *
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
          ((rUBInCat wOuter wInner2 11).embedUnitary M_bwd⁻¹ * sB *
            (rUBInCat wOuter wInner2 11).embedUnitary M_bwd))
    (hPres1 : PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        ((rUBInCat wOuter wInner2 11).embedUnitary M_fwd⁻¹ * sF *
          (rUBInCat wOuter wInner2 11).embedUnitary M_fwd)).1
      (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid))
    (hPres2 : PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        ((rUBInCat wOuter wInner2 11).embedUnitary M_bwd⁻¹ * sB *
          (rUBInCat wOuter wInner2 11).embedUnitary M_bwd)).1
      (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid))
    (hPresAll : PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        (innerMidCoreUnitary M_fwd M_bwd sF sB)).1
      ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).image ∪
        scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)) :
    BellAsymLegs Var bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v prepOutImpl M_fwd M_bwd
      raw_4 raw_3 sF sB pOutFwd pOutBwd P_1 pTurn P_4 :=
  ⟨M_1_pre, M_1_post, M_2_pre, M_2_post, hFwd, hBwd, hConj, h1, hTurn, h4, hPull1, hPull2,
    hPres1, hPres2, hPresAll⟩

/-- Construct `BellAsymLegs` in zero-`hPull` `D_neg` mode (`P_1` loads `M_fwd`, `pTurn` turns
`D_neg * M_fwd` into `(D_neg * M_bwd) * R_mid`, `P_4` unloads `M_bwd`). -/
theorem BellAsymLegs.ofDNeg {Var : Type} [Fintype Var] [DecidableEq Var]
    {bQPE wOuter wInner2 ko km mLow sUb : ℕ} {hkOut : ko ≤ wOuter} {hkMid : km ≤ wInner2} {v : Var}
    {prepOutImpl : Unitary (2 ^ mOutUB wOuter)} (M_fwd M_bwd D_neg :
      Unitary (2 ^ nUB wOuter wInner2))
    (hDInv : D_neg⁻¹ = D_neg) (raw_4 raw_3 : Unitary (2 ^ (nUB wOuter wInner2 + 11)))
    {pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (hFwd : Solution.CleanDyn.CleanRealizes v (combOutRegB bQPE wOuter wInner2 ko km mLow sUb)
      (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb) prepOutImpl pOutFwd)
    (hBwd : CleanUnloadsWp v (scrOutZeroSet bQPE wOuter wInner2 ko km mLow sUb hkOut)
      ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary prepOutImpl) pOutBwd)
    (hConj : OuterConjPreservesZero wOuter ko hkOut prepOutImpl)
    (h1 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_fwd) P_1)
    (hTurn : CleanTurnaroundWp v (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary (D_neg * M_fwd))
      (((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary (D_neg * M_bwd)) *
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
          (QubitisedWalk.reflMidUnitary (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2)))) pTurn)
    (h4 : CleanUnloadsWp v (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_bwd) P_4)
    (hPres1 : PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        ((rUBInCat wOuter wInner2 11).embedUnitary M_fwd⁻¹ *
          ((rUBInCat wOuter wInner2 11).embedUnitary D_neg * raw_4) *
          (rUBInCat wOuter wInner2 11).embedUnitary M_fwd)).1
      (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid))
    (hPres2 : PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        ((rUBInCat wOuter wInner2 11).embedUnitary M_bwd⁻¹ *
          (raw_3 * (rUBInCat wOuter wInner2 11).embedUnitary D_neg) *
          (rUBInCat wOuter wInner2 11).embedUnitary M_bwd)).1
      (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid))
    (hPresAll : PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        (innerMidCoreUnitary M_fwd M_bwd
          ((rUBInCat wOuter wInner2 11).embedUnitary D_neg * raw_4)
          (raw_3 * (rUBInCat wOuter wInner2 11).embedUnitary D_neg))).1
      ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).image ∪
        scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)) :
    BellAsymLegs Var bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v prepOutImpl M_fwd M_bwd
      raw_4 raw_3 ((rUBInCat wOuter wInner2 11).embedUnitary D_neg * raw_4)
      (raw_3 * (rUBInCat wOuter wInner2 11).embedUnitary D_neg) pOutFwd pOutBwd P_1 pTurn P_4 :=
  ⟨M_fwd, D_neg * M_fwd, D_neg * M_bwd, M_bwd, hFwd, hBwd, hConj, h1, hTurn, h4,
    pull_fwd_dneg _ M_fwd D_neg raw_4 hDInv, pull_bwd_dneg _ M_bwd D_neg raw_3,
    hPres1, hPres2, hPresAll⟩

/-- Construct `BellAsymLegs` in symmetric `(M_fwd, M_bwd)` mode (`M_1_pre = M_1_post = M_fwd`,
`M_2_pre = M_2_post = M_bwd`, `raw_4 = sF`, `raw_3 = sB`). -/
theorem BellAsymLegs.ofSym {Var : Type} [Fintype Var] [DecidableEq Var]
    {bQPE wOuter wInner2 ko km mLow sUb : ℕ} {hkOut : ko ≤ wOuter} {hkMid : km ≤ wInner2} {v : Var}
    {prepOutImpl : Unitary (2 ^ mOutUB wOuter)} (M_fwd M_bwd : Unitary (2 ^ nUB wOuter wInner2))
    (sF sB : Unitary (2 ^ (nUB wOuter wInner2 + 11)))
    {pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)}
    (hFwd : Solution.CleanDyn.CleanRealizes v (combOutRegB bQPE wOuter wInner2 ko km mLow sUb)
      (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb) prepOutImpl pOutFwd)
    (hBwd : CleanUnloadsWp v (scrOutZeroSet bQPE wOuter wInner2 ko km mLow sUb hkOut)
      ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary prepOutImpl) pOutBwd)
    (hConj : OuterConjPreservesZero wOuter ko hkOut prepOutImpl)
    (h1 : CleanRealizesSet v (combScrUbRegAt bQPE wOuter wInner2 ko km mLow sUb).image
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_fwd) P_1)
    (hTurn : CleanTurnaroundWp v (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_fwd)
      (((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_bwd) *
        (combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
          (QubitisedWalk.reflMidUnitary (inMidWalkCat 11 (mOutUB wOuter) (mMidUB wInner2)))) pTurn)
    (h4 : CleanUnloadsWp v (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)
      ((combUBRegB bQPE wOuter wInner2 ko km mLow sUb).embedUnitary M_bwd) P_4)
    (hPres1 : PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        ((rUBInCat wOuter wInner2 11).embedUnitary M_fwd⁻¹ * sF *
          (rUBInCat wOuter wInner2 11).embedUnitary M_fwd)).1
      (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid))
    (hPres2 : PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        ((rUBInCat wOuter wInner2 11).embedUnitary M_bwd⁻¹ * sB *
          (rUBInCat wOuter wInner2 11).embedUnitary M_bwd)).1
      (scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid))
    (hPresAll : PreservesWires
      ((combWalkCatRegAt bQPE wOuter wInner2 ko km mLow sUb).embedUnitary
        (innerMidCoreUnitary M_fwd M_bwd sF sB)).1
      ((combOutRegB bQPE wOuter wInner2 ko km mLow sUb).image ∪
        scrMidZeroSet bQPE wOuter wInner2 ko km mLow sUb hkMid)) :
    BellAsymLegs Var bQPE wOuter wInner2 ko km mLow sUb hkOut hkMid v prepOutImpl M_fwd M_bwd
      sF sB sF sB pOutFwd pOutBwd P_1 pTurn P_4 :=
  ⟨M_fwd, M_fwd, M_bwd, M_bwd, hFwd, hBwd, hConj, h1, hTurn, h4,
    pull_sym _ M_fwd sF, pull_sym _ M_bwd sB, hPres1, hPres2, hPresAll⟩

/-! ## Section 3: Arbitrary-`K` (`1 ≤ K`) `WalkKStepRefl2InvErrLe` Bridge -/

/-- Invariant-subspace catalytic `L²` `K`-step super-reflection error bound (`rfl`-aligned with
`TailShiftThreeGear.WalkKStepRefl2InvErrLe` and `WalkSuperRefl2InvErrLe`). -/
noncomputable def WalkKStepRefl2InvErrLe (wOuter wInner2 K : ℕ) (uB :
    Unitary (2 ^ nUB wOuter wInner2))
    (uSuper : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))) (δSuper : ℝ) : Prop :=
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)
  let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB
  let R₂_sup := R₁ * (R₁ * R₂) ^ K
  ∃ P_inv : (Fin (2 ^ nUB wOuter wInner2) → ℂ) → Prop,
    (∀ ψ : Fin (2 ^ (2 * 58)) → ℂ,
      P_inv ((rSysInWalk mOut mMid).tensorState ψ (Pi.single 0 1))) ∧
    (∀ v, P_inv v → P_inv (R₁.1 *ᵥ v)) ∧
    (∀ v, P_inv v → P_inv (R₂.1 *ᵥ v)) ∧
    (∀ v, P_inv v →
      ‖WithLp.toLp 2
          (uSuper.1 *ᵥ tensorWalkCat v (Solution.CircuitModular.phaseGradientLowFactor 11 3) -
            tensorWalkCat (R₂_sup.1 *ᵥ v) (Solution.CircuitModular.phaseGradientLowFactor 11 3))‖ ≤
        δSuper *
          ‖WithLp.toLp 2 (tensorWalkCat v (Solution.CircuitModular.phaseGradientLowFactor 11 3))‖)

theorem walkKStepRefl2InvErrLe_of_walkRefl2InvErrLe {wOuter wInner2 : ℕ} (K : ℕ) (hK : 1 ≤ K)
    {uB : Unitary (2 ^ nUB wOuter wInner2)}
    {uRefl2 : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))} {δStep : ℝ}
    (h : WalkRefl2InvErrLe wOuter wInner2 uB uRefl2 δStep) :
    let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
    WalkKStepRefl2InvErrLe wOuter wInner2 K uB (uRefl2 * (R₁c * uRefl2) ^ (K - 1)) ((K : ℝ) *
        δStep) := by
  intro R₁c
  obtain ⟨P_inv, hInit, hR1, hR2, hErr⟩ := h
  refine ⟨P_inv, hInit, hR1, hR2, ?_⟩
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let cat := Solution.CircuitModular.phaseGradientLowFactor 11 3
  let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)
  let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB
  have hRelR₁ : InvCatRel P_inv cat R₁c R₁ 0 := ⟨hR1, fun v _ ↦ by
    have heq : R₁c.1 *ᵥ tensorWalkCat v cat = tensorWalkCat (R₁.1 *ᵥ v) cat := by
      dsimp only [R₁c]
      rw [tgEmbedUnitary_rWalkInWalkCat_reflIn, QRegister.embedUnitary_val]
      exact embedMatrix_rWalkInWalkCat_mulVec R₁.1 v cat
    rw [zero_mul, heq, sub_self, WithLp.toLp_zero, norm_zero]⟩
  have hRelR₂ : InvCatRel P_inv cat uRefl2 R₂ δStep := ⟨hR2, hErr⟩
  have hRelW : InvCatRel P_inv cat (R₁c * uRefl2) (R₁ * R₂) δStep := by
    simpa only [zero_add] using invCatRel_mul hRelR₁ hRelR₂
  have hRelSup := invCatRel_mul hRelR₂ (invCatRel_pow hRelW (K - 1))
  have hIdEq : R₁ * (R₁ * R₂) ^ K = R₂ * (R₁ * R₂) ^ (K - 1) := by
    have hm : K = (K - 1) + 1 := by omega
    conv_lhs => rw [hm, pow_succ']
    calc R₁ * ((R₁ * R₂) * (R₁ * R₂) ^ (K - 1))
        = (R₁ * R₁) * R₂ * (R₁ * R₂) ^ (K - 1) := by simp only [mul_assoc]
      _ = R₂ * (R₁ * R₂) ^ (K - 1) := by rw [QubitisedWalk.reflInUnitary_mul_self, one_mul]
  have hScal : δStep + ((K - 1 : ℕ) : ℝ) * δStep = (K : ℝ) * δStep := by
    have hK1 : 1 + (K - 1) = K := by omega
    have hcast : (1 : ℝ) + ((K - 1 : ℕ) : ℝ) = (K : ℝ) := by exact_mod_cast hK1
    calc δStep + ((K - 1 : ℕ) : ℝ) * δStep = (1 + ((K - 1 : ℕ) : ℝ)) * δStep := by ring
      _ = (K : ℝ) * δStep := by rw [hcast]
  intro v hv
  rw [hIdEq, ← hScal]
  exact hRelSup.2 v hv

theorem walkKStepRefl2InvErrLe_zero_of_exact {wOuter wInner2 : ℕ} (K : ℕ) (hK : 1 ≤ K)
    {uB : Unitary (2 ^ nUB wOuter wInner2)}
    {uRefl2 : Unitary (2 ^ walkCatWidth 11 (mOutUB wOuter) (mMidUB wInner2))}
    (h : WalkRefl2InvErrLe wOuter wInner2 uB uRefl2 0) :
    let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 (mOutUB wOuter) (mMidUB wInner2))
    WalkKStepRefl2InvErrLe wOuter wInner2 K uB (uRefl2 * (R₁c * uRefl2) ^ (K - 1)) 0 := by
  simpa only [mul_zero] using walkKStepRefl2InvErrLe_of_walkRefl2InvErrLe K hK h

/-! ## Section 4: Single-Step (`K = 1`, `StageF` / `StageB`) Circuit Aliases & Counts -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellAsymCore

end
