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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.SevenGearBondDeferC

/-!
# Seven-Gear Bond-Deferred Dihedral Engine — Part D

Invariant-subspace `L²` perturbation composition (`CoarseGearInvRel`, `gen_implQPEPertHyp`),
fully general `(M, eLB, lam, uB)` symbolic perturbation transfer (`SymbolicPertTransferHyp`),
`TailShiftRayQuantSuperBox` bridge (`symbolicPertTransfer_of_box`), and the recursive
peel `7`-Gear QPE harness (`p450SymbolicSevenGearProg`, `32 ≤ nStd ≤ 46`).

## References
- A. Luis and J. Peřina, *Phys. Rev. A* **54**, 4564 (1996), DOI: 10.1103/PhysRevA.54.4564.
- M. Möttönen et al., *Phys. Rev. Lett.* **93**, 130502 (2004), DOI: 10.1103/PhysRevLett.93.130502.
- R. Babbush et al., *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- J. Lee et al., *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SevenGearBondDefer
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Circuit Real QuantumComputation.Specs
open QuantumComputation.Specs.P450 BlockEncodingCore
open BlockEncodingCircuit TopIntegrationBridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open WalkQPEBridgeXMeas hiding image_rFullZeroLoc rFullZeroLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.Cat11CompactPhase2Bridge
open DihedralWalkQPE BlockReflection ApproxIqft16 SineWindowFlexM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.MultiGearQPE (
  outRemWidth outZeroPrefixReg combARem combAncillas combQubits combWalkCatReg
  combWalkReflRegs combWalkReflCovers comb_hbScr16 CleanWalkRefl2 WalkRefl2ErrLe
  P450RefVarBound ReordSosHyp RealizesP450GroundQPE tensorWalkCat_smul_right approxPhaseGrad11Ray
  exactPhaseGrad11RayUnitary norm_phaseGrad11RayScalar exactPhaseGrad11RayUnitary_mulVec_zero
  approxPhaseGrad11Ray_count_toff approxPhaseGrad11Ray_count_t norm_approxPhaseGrad11Ray_sub_le)
open TwoGearBox hiding m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
open TailShiftBox TwoGearQPEPhase5
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBondDefer
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 1: Invariant-Subspace Composition & Generic `5`-Coarse-Stage `ImplQPEPertHyp` -/

theorem genBlocked_mux_l2_err_le {M nStd kTail tShift : ℕ} (mOut mMid : ℕ)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (w10 : ThreeGearBondDeferSpec M 10 7 0)
    {P_inv : FGInvPred mOut mMid} {uCatIdeal : Unitary (2 ^ 11)}
    {FG0 : Fin (2 ^ 2) → FGWalkU mOut mMid} {FG1 : Fin (2 ^ 3) → FGWalkU mOut mMid}
    {FG2 : Fin (2 ^ 4) → FGWalkU mOut mMid} {FG3 : Fin (2 ^ 5) → FGWalkU mOut mMid}
    {FG4 : Fin (2 ^ 6) → FGWalkU mOut mMid}
    {uSuperM uRefl2F : FGWalkU mOut mMid} {uB : Unitary (2 ^ walkWidth mOut mMid)}
    {δCoarse δM δF : ℝ} (hδC0 : 0 ≤ δCoarse) (hδM0 : 0 ≤ δM) (hδF0 : 0 ≤ δF)
    (hR1 : ∀ v, P_inv v → P_inv ((QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)).1 *ᵥ v))
    (hR2 : ∀ v, P_inv v → P_inv ((QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB).1 *ᵥ
      v))
    (hCoarse : ∀ xc : Fin (2 ^ 6), xc.val ≤ nStd + 1 →
      let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)
      let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB
      let W := R₁ * R₂
      InvCatRel P_inv (uCatIdeal.1 *ᵥ basisState 0)
        (genCoarseFiber mOut mMid FG0 FG1 FG2 FG3 FG4 xc)
        (tailFusedScheduleFiber nStd (R₁ * W ^ 1024) (R₁ * W ^ kTail) R₁ xc) δCoarse)
    (hM : InvCatKStepErr mOut mMid P_inv uCatIdeal uB 128 uSuperM δM)
    (hF : InvCatRefl2Err mOut mMid P_inv uCatIdeal uB uRefl2F δF)
    {e₁ : Fin (2 ^ walkWidth mOut mMid) → ℂ} (hInit : P_inv e₁)
    (hwc₀_norm : ‖WithLp.toLp 2 (tensorWalkCat e₁ (uCatIdeal.1 *ᵥ basisState 0))‖ ≤ 1)
    (hWinNorm : ∑ m : Fin (2 ^ 16),
      ‖(w10.base.uIdeal.1 *ᵥ basisState (0 : Fin (2 ^ 16))) m‖ ^ 2 = 1) :
    let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)
    let rW := rWalkInWalkCat 11 mOut mMid
    let rQPE := rQPEInAct 16 11 mOut mMid
    let rComb := rQPE.concat (rWalkCatInAct 16 11 mOut mMid)
      (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)
    let FA := genCombinedHiFiber mOut mMid ts FG0 FG1 FG2 FG3 FG4 uSuperM
    let FB := affineScheduleFiber (bQPE := 16) 7 127 (R₁c * uRefl2F) R₁c
    let u3Impl := rComb.embedUnitary (QubitisedWalk.qpeMuxUnitary FB) *
      (rCombHiInAct mOut mMid 7 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary FA)
    let u3Id := rComb.embedUnitary
      (QubitisedWalk.qpeMuxUnitary (affineScheduleFiber 16 M
        (R₁c * QubitisedWalk.reflPulledUnitary (inMidWalkCat 11 mOut mMid) (rW.embedUnitary uB))
          R₁c))
    let wc₀ := tensorWalkCat e₁ (uCatIdeal.1 *ᵥ basisState 0)
    let window0 := w10.base.uIdeal.1 *ᵥ basisState (0 : Fin (2 ^ 16))
    ‖WithLp.toLp 2 (u3Impl.1 *ᵥ tgTensorWCQPE wc₀ window0 - u3Id.1 *ᵥ tgTensorWCQPE wc₀ window0)‖ ≤
      δCoarse + 7 * δM + 127 * δF := by
  intro R₁c rW rQPE rComb FA FB u3Impl u3Id wc₀ window0
  let cat := uCatIdeal.1 *ᵥ basisState (0 : Fin (2 ^ 11))
  let C_walk : ℝ := δCoarse + 7 * δM + 127 * δF
  have hC0 : 0 ≤ C_walk := by linarith
  let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)
  let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB
  let W := R₁ * R₂
  let R₂_mid := R₁ * W ^ 128
  have hR₁_inv : R₁ * R₁ = 1 := QubitisedWalk.reflInUnitary_mul_self _
  have hR₂_inv : R₂ * R₂ = 1 := QubitisedWalk.reflPulledUnitary_mul_self _ _
  have hPowInv (K : ℕ) : ∀ v, P_inv v → P_inv ((W ^ K).1 *ᵥ v) := by
    intro v hv
    induction K with
    | zero => simpa using hv
    | succ k ih =>
      rw [pow_succ', Submonoid.coe_mul, show W.1 = R₁.1 * R₂.1 from rfl,
        Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hR1 _ (hR2 _ ih)
  have hInvR128 : ∀ v, P_inv v → P_inv ((R₂_mid.1) *ᵥ v) := fun v hv ↦ by
    change P_inv ((R₁.1 * (W ^ 128).1) *ᵥ v)
    rw [← Matrix.mulVec_mulVec]
    exact hR1 _ (hPowInv 128 v hv)
  have hRelR₁ : InvCatRel P_inv cat R₁c R₁ 0 := invCatRel_reflInUnitary mOut mMid hR1
  have hRelWM : InvCatRel P_inv cat (R₁c * uSuperM) (R₁ * R₂_mid) δM := by
    simpa only [zero_add] using invCatRel_mul hRelR₁ ⟨hInvR128, hM⟩
  have hRelWF : InvCatRel P_inv cat (R₁c * uRefl2F) (R₁ * R₂) δF := by
    simpa only [zero_add] using invCatRel_mul hRelR₁ ⟨hR2, hF⟩
  have hsq : ‖WithLp.toLp 2
      (u3Impl.1 *ᵥ tgTensorWCQPE wc₀ window0 - u3Id.1 *ᵥ tgTensorWCQPE wc₀ window0)‖ ^ 2 ≤
      C_walk ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    let f : Fin (2 ^ actWidth 16 11 mOut mMid) → ℝ := fun g ↦
      ‖(u3Impl.1 *ᵥ tgTensorWCQPE wc₀ window0 - u3Id.1 *ᵥ tgTensorWCQPE wc₀ window0) g‖ ^ 2
    rw [show (∑ g, ‖(u3Impl.1 *ᵥ tgTensorWCQPE wc₀ window0 -
          u3Id.1 *ᵥ tgTensorWCQPE wc₀ window0) g‖ ^ 2) = ∑ g, f g from rfl,
      ← (tgActSplitEquiv 16 11 mOut mMid).symm.sum_comp f, Fintype.sum_prod_type_right]
    have hbranch (m : Fin (2 ^ 16)) :
        ∑ x : Fin (2 ^ walkCatWidth 11 mOut mMid),
          f ((tgActSplitEquiv 16 11 mOut mMid).symm (x, m)) ≤ ‖window0 m‖ ^ 2 * C_walk ^ 2 := by
      let xh := (rHiInQPE16 7 (by decide)).extractIndex m
      let xl : Fin (2 ^ 7) := ⟨m.val % 128, Nat.mod_lt _ (by decide)⟩
      let FId16 := affineScheduleFiber (bQPE := 16) 16 M
        (R₁c * QubitisedWalk.reflPulledUnitary (inMidWalkCat 11 mOut mMid) (rW.embedUnitary uB)) R₁c
      have hpt_sum : ∑ x, f ((tgActSplitEquiv 16 11 mOut mMid).symm (x, m)) =
          ‖window0 m‖ ^ 2 * ‖WithLp.toLp 2 (((FB m * FA xh).1) *ᵥ wc₀ - (FId16 m).1 *ᵥ wc₀)‖ ^ 2 :=
            by
        rw [EuclideanSpace.norm_sq_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        let g := (tgActSplitEquiv 16 11 mOut mMid).symm (x, m)
        have hfst : (rWalkCatInAct 16 11 mOut mMid).extractIndex g = x := by
          rw [← tgActSplitEquiv_fst, Equiv.apply_symm_apply]
        have hsnd : rQPE.extractIndex g = m := by rw [← tgActSplitEquiv_snd, Equiv.apply_symm_apply]
        dsimp only [f, Pi.sub_apply, u3Impl, u3Id, FId16, rComb, rQPE]
        rw [tgEmbed_phaseB_phaseA_mulVec (mLow := 7) (by decide) FA FB wc₀ window0 g,
          tgEmbed_qpeMuxUnitary_mulVec, hfst, hsnd]
        dsimp only [xh]
        rw [← sub_mul, norm_mul, mul_pow]
        ring
      rw [hpt_sum]
      by_cases hm : m.val ≤ M
      · let rSliceC : QRegister 6 9 := QRegister.block 3 6 (by decide)
        let rSliceM : QRegister 3 9 := QRegister.block 0 3 (by decide)
        have hxc_le : (rSliceC.extractIndex xh).val ≤ nStd + 1 := by
          have hxh_v : xh.val = m.val / 128 := qpeBlockHi_extract_val 16 9 7 (by decide) rfl m
          have hxc_v : (rSliceC.extractIndex xh).val = xh.val / 8 :=
            qpeBlockHi_extract_val 9 6 3 (by decide) rfl xh
          have h1 := ts.hM_eq
          have h2 := ts.hkTail_lt
          omega
        have hRelC := hCoarse (rSliceC.extractIndex xh) hxc_le
        have hRelM : InvCatRel P_inv cat
            (affineScheduleFiber 3 7 (R₁c * uSuperM) R₁c
              (rSliceM.extractIndex (tailShiftClockPerm ts xh)))
            (affineScheduleFiber 3 7 (R₁ * R₂_mid) R₁
              (rSliceM.extractIndex (tailShiftClockPerm ts xh))) (7 * δM) := by
          have hsumM : ∑ j ∈ Finset.range 3, chunkSize2 2 7 j = 7 := by decide
          have hc := invCatRelChunksFiber hRelR₁ hRelWM 2 7 3
            (qpeAffinePerm 3 3 7 (rSliceM.extractIndex (tailShiftClockPerm ts xh)))
          rw [hsumM] at hc
          simpa only [affineScheduleFiber, Nat.cast_ofNat] using hc
        have hFB_mod : FB m = affineScheduleFiber (bQPE := 7) 7 127 (R₁c * uRefl2F) R₁c xl :=
          affineScheduleFiber_phaseB_eq_mod (mLow := 7) (by decide) (by decide)
            (R₁c * uRefl2F) R₁c m
        have hRelF : InvCatRel P_inv cat (FB m)
            (affineScheduleFiber (bQPE := 7) 7 127 (R₁ * R₂) R₁ xl) (127 * δF) := by
          rw [hFB_mod]
          have hsumF : ∑ j ∈ Finset.range 7, chunkSize2 6 127 j = 127 := by decide
          have hc := invCatRelChunksFiber hRelR₁ hRelWF 6 127 7 (qpeAffinePerm 7 7 127 xl)
          rw [hsumF] at hc
          simpa only [affineScheduleFiber, Nat.cast_ofNat] using hc
        have hRelFMC := invCatRel_mul hRelF (invCatRel_mul hRelM hRelC)
        have hId_eq := tailShiftThreeGear_ideal_fiber_mul_eq hR₁_inv hR₂_inv (by decide) ts m hm
        dsimp only [Nat.reduceSub, Nat.reducePow] at hId_eq
        have hFId16_act : (FId16 m).1 *ᵥ wc₀ = tensorWalkCat
            ((affineScheduleFiber (bQPE := 16) 16 M (R₁ * R₂) R₁ m).1 *ᵥ e₁) cat := by
          have hEmb : FId16 m =
              rW.embedUnitary (affineScheduleFiber (bQPE := 16) 16 M (R₁ * R₂) R₁ m) := by
            dsimp only [FId16, affineScheduleFiber, R₁c, R₁, R₂]
            rw [tgEmbedUnitary_rWalkInWalkCat_reflIn, tgEmbedUnitary_rWalkInWalkCat_reflPulled,
              ← QRegister.embedUnitary_mul, ← embedUnitaryChunksFiber]
          rw [hEmb, QRegister.embedUnitary_val, embedMatrix_rWalkInWalkCat_mulVec]
        have hcat_le :
            ‖WithLp.toLp 2 (((FB m * FA xh).1) *ᵥ wc₀ - (FId16 m).1 *ᵥ wc₀)‖ ≤ C_walk := by
          rw [hFId16_act, ← hId_eq]
          have hb := hRelFMC.2 e₁ hInit
          have hcomm_add : 127 * δF + (7 * δM + δCoarse) = C_walk := by
            dsimp only [C_walk]
            ring
          rw [hcomm_add] at hb
          exact hb.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hwc₀_norm hC0)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hcat_le 2) (sq_nonneg _)
      · have hw0 : window0 m = 0 := by
          dsimp only [window0]
          rw [w10.base.ideal_mulVec_zero]
          exact ite_eq_right hm
        simp only [hw0, norm_zero, sq, zero_mul, le_rfl]
    calc ∑ m, ∑ x, f ((tgActSplitEquiv 16 11 mOut mMid).symm (x, m))
        ≤ ∑ m : Fin (2 ^ 16), ‖window0 m‖ ^ 2 * C_walk ^ 2 := Finset.sum_le_sum fun m _ ↦ hbranch m
      _ = (∑ m : Fin (2 ^ 16), ‖window0 m‖ ^ 2) * C_walk ^ 2 := (Finset.sum_mul _ _ _).symm
      _ = C_walk ^ 2 := by rw [hWinNorm, one_mul]
  exact (sq_le_sq₀ (norm_nonneg _) hC0).mp hsq

theorem genBlocked_impl_l2_err_le {M nStd kTail tShift : ℕ} (mOut mMid : ℕ)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (w10 : ThreeGearBondDeferSpec M 10 7 0)
    {P_inv : FGInvPred mOut mMid} {uCatImpl uCatIdeal : Unitary (2 ^ 11)}
    {δCat : ℝ} (hCatErr : ‖uCatImpl.1 - uCatIdeal.1‖ ≤ δCat)
    {uIqftImpl uIqftIdeal : Unitary (2 ^ 16)} {δIqft : ℝ}
    (hIqftErr : ‖uIqftImpl.1 - uIqftIdeal.1‖ ≤ δIqft)
    {FG0 : Fin (2 ^ 2) → FGWalkU mOut mMid} {FG1 : Fin (2 ^ 3) → FGWalkU mOut mMid}
    {FG2 : Fin (2 ^ 4) → FGWalkU mOut mMid} {FG3 : Fin (2 ^ 5) → FGWalkU mOut mMid}
    {FG4 : Fin (2 ^ 6) → FGWalkU mOut mMid}
    {uSuperM uRefl2F : FGWalkU mOut mMid} {uB : Unitary (2 ^ walkWidth mOut mMid)}
    {δCoarse δM δF : ℝ} (hδC0 : 0 ≤ δCoarse) (hδM0 : 0 ≤ δM) (hδF0 : 0 ≤ δF)
    (hR1 : ∀ v, P_inv v → P_inv ((QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)).1 *ᵥ v))
    (hR2 : ∀ v, P_inv v → P_inv ((QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB).1 *ᵥ
      v))
    (hCoarse : ∀ xc : Fin (2 ^ 6), xc.val ≤ nStd + 1 →
      let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)
      let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB
      let W := R₁ * R₂
      InvCatRel P_inv (uCatIdeal.1 *ᵥ basisState 0)
        (genCoarseFiber mOut mMid FG0 FG1 FG2 FG3 FG4 xc)
        (tailFusedScheduleFiber nStd (R₁ * W ^ 1024) (R₁ * W ^ kTail) R₁ xc) δCoarse)
    (hM : InvCatKStepErr mOut mMid P_inv uCatIdeal uB 128 uSuperM δM)
    (hF : InvCatRefl2Err mOut mMid P_inv uCatIdeal uB uRefl2F δF)
    (ψ : Fin (2 ^ systemQubits_local) → ℂ)
    (hInit : P_inv ((rSysInWalk mOut mMid).tensorState ψ (Pi.single 0 1)))
    (hnorm : (∑ i, Complex.normSq (ψ i)) = 1) :
    let sys : QRegister systemQubits_local (actWidth 16 11 mOut mMid) :=
      .block 0 _ (sys_le_actWidth mOut mMid)
    let init := sys.tensorState ψ (Pi.single 0 1)
    let wImplBlk := genBlockedImplUnitary mOut mMid ts uCatImpl w10.base.cWinHi.eval
      w10.base.cWinLo.eval uIqftImpl FG0 FG1 FG2 FG3 FG4 uSuperM uRefl2F
    let wIdBlk := BlockReflection.blockedIdealUnitary 16 11 mOut mMid 16 M
      uCatIdeal uB w10.base.uIdeal uIqftIdeal
    ‖WithLp.toLp 2 (wImplBlk.1 *ᵥ init - wIdBlk.1 *ᵥ init)‖ ≤
      (δCat + w10.base.δWin + δIqft) + (δCoarse + 7 * δM + 127 * δF) := by
  intro sys init wImplBlk wIdBlk
  let cat := uCatIdeal.1 *ᵥ basisState (0 : Fin (2 ^ 11))
  let window0 := w10.base.uIdeal.1 *ᵥ basisState (0 : Fin (2 ^ 16))
  have hCatNorm : ∑ c, Complex.normSq (cat c) = 1 := by
    refine (sum_normSq_unitary_mulVec_tg uCatIdeal (basisState 0)).trans ?_
    rw [Fintype.sum_eq_single 0 (fun c hc ↦ by
      simp only [basisState, Pi.single_eq_of_ne hc, Complex.normSq_zero])]
    simp only [basisState, Pi.single_eq_same, Complex.normSq_one]
  have hWinNorm : ∑ m : Fin (2 ^ 16), ‖window0 m‖ ^ 2 = 1 := by
    simp only [← Complex.normSq_eq_norm_sq]
    refine (sum_normSq_unitary_mulVec_tg w10.base.uIdeal (basisState 0)).trans ?_
    rw [Fintype.sum_eq_single 0 (fun m hm ↦ by
      simp only [basisState, Pi.single_eq_of_ne hm, Complex.normSq_zero])]
    simp only [basisState, Pi.single_eq_same, Complex.normSq_one]
  let rW := rWalkInWalkCat 11 mOut mMid
  let rQPE := rQPEInAct 16 11 mOut mMid
  let rComb := rQPE.concat (rWalkCatInAct 16 11 mOut mMid)
    (rQPEInAct_disjoint_rWalkCatInAct 16 11 mOut mMid)
  let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)
  let uWinImpl16 : Unitary (2 ^ 16) :=
    (rLoInQPE16 7 (by decide)).embedUnitary w10.base.cWinLo.eval *
      (rWinHiInQPE 7 0 (by decide) (by decide) (Nat.zero_le _)).embedUnitary w10.base.cWinHi.eval
  let FA := genCombinedHiFiber mOut mMid ts FG0 FG1 FG2 FG3 FG4 uSuperM
  let FB := affineScheduleFiber (bQPE := 16) 7 127 (R₁c * uRefl2F) R₁c
  let u1Impl := (rCatInAct 16 11 mOut mMid).embedUnitary uCatImpl
  let u1Id := (rCatInAct 16 11 mOut mMid).embedUnitary uCatIdeal
  let u2Impl := rQPE.embedUnitary uWinImpl16
  let u2Id := rQPE.embedUnitary w10.base.uIdeal
  let u3Impl := rComb.embedUnitary (QubitisedWalk.qpeMuxUnitary FB) *
    (rCombHiInAct mOut mMid 7 (by decide)).embedUnitary (QubitisedWalk.qpeMuxUnitary FA)
  let u3Id := rComb.embedUnitary (QubitisedWalk.qpeMuxUnitary (affineScheduleFiber 16 M
    (R₁c * QubitisedWalk.reflPulledUnitary (inMidWalkCat 11 mOut mMid) (rW.embedUnitary uB)) R₁c))
  let u4Impl := rQPE.embedUnitary uIqftImpl
  let u4Id := rQPE.embedUnitary uIqftIdeal
  have hinitNorm : ∑ g, Complex.normSq (init g) = 1 :=
    (sum_normSq_sys_tensorState_zero ψ).trans hnorm
  have hop1 : ‖u1Impl.1 - u1Id.1‖ ≤ δCat := by
    change ‖(rCatInAct 16 11 mOut mMid).embedMatrix uCatImpl.1 -
      (rCatInAct 16 11 mOut mMid).embedMatrix uCatIdeal.1‖ ≤ _
    rw [← QubitisedWalk.embedMatrix_sub_local]
    exact (QubitisedWalk.embedMatrix_opNorm_le _ _).trans hCatErr
  have hop4 : ‖u4Impl.1 - u4Id.1‖ ≤ δIqft := by
    change ‖rQPE.embedMatrix uIqftImpl.1 - rQPE.embedMatrix uIqftIdeal.1‖ ≤ _
    rw [← QubitisedWalk.embedMatrix_sub_local]
    exact (QubitisedWalk.embedMatrix_opNorm_le _ _).trans hIqftErr
  let e₁ := (rSysInWalk mOut mMid).tensorState ψ (Pi.single 0 1)
  let wc₀ := tensorWalkCat e₁ cat
  have hwc₀_norm : ‖WithLp.toLp 2 wc₀‖ ≤ 1 := (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp (by
    rw [EuclideanSpace.norm_sq_eq, _root_.one_pow]
    simp only [← Complex.normSq_eq_norm_sq]
    dsimp only [wc₀, e₁]
    rw [sum_normSq_tensorWalkCat, hCatNorm, mul_one,
      (sum_normSq_sys_tensorState_zero ψ).trans hnorm])
  let s1Impl := u1Impl.1 *ᵥ init
  let s1Id := u1Id.1 *ᵥ init
  let s2Impl := u2Impl.1 *ᵥ s1Impl
  let s2Id := u2Id.1 *ᵥ s1Id
  let s3Impl := u3Impl.1 *ᵥ s2Impl
  let s3Id := u3Id.1 *ᵥ s2Id
  have hs1Err : ‖WithLp.toLp 2 (s1Impl - s1Id)‖ ≤ δCat :=
    norm_mulVec_sub_le_of_opNorm u1Impl u1Id hinitNorm hop1
  have hs1Id_eq : s1Id = tgTensorWCQPE wc₀ (basisState 0) := by
    dsimp only [s1Id, init, u1Id, wc₀, cat]
    rw [tgSysAct_tensorState_zero_eq ψ, tgRCatInAct_eq_compose,
      QRegister.embedUnitary_compose, QRegister.embedUnitary_val,
      tgEmbedMatrix_rWalkCatInAct_mulVec, QRegister.embedUnitary_val,
      embedMatrix_rCatInWalkCat_mulVec]
  have hs2Id_eq : s2Id = tgTensorWCQPE wc₀ window0 := by
    dsimp only [s2Id, u2Id, window0]
    rw [hs1Id_eq, QRegister.embedUnitary_val, tgEmbedMatrix_rQPEInAct_mulVec]
  have hs2IdNorm : ∑ g, Complex.normSq (s2Id g) = 1 :=
    (sum_normSq_unitary_mulVec_tg u2Id s1Id).trans
      ((sum_normSq_unitary_mulVec_tg u1Id init).trans hinitNorm)
  have hs3IdNorm : ∑ g, Complex.normSq (s3Id g) = 1 :=
    (sum_normSq_unitary_mulVec_tg u3Id s2Id).trans hs2IdNorm
  have hb2 : ‖WithLp.toLp 2 (u2Impl.1 *ᵥ s1Id - u2Id.1 *ᵥ s1Id)‖ ≤ w10.base.δWin := by
    have hdiff : u2Impl.1 *ᵥ s1Id - u2Id.1 *ᵥ s1Id =
        tgTensorWCQPE wc₀ (uWinImpl16.1 *ᵥ basisState 0 - w10.base.uIdeal.1 *ᵥ basisState 0) := by
      dsimp only [u2Impl, u2Id]
      rw [hs1Id_eq, QRegister.embedUnitary_val, QRegister.embedUnitary_val,
        tgEmbedMatrix_rQPEInAct_mulVec, tgEmbedMatrix_rQPEInAct_mulVec]
      ext g
      simp only [Pi.sub_apply, tgTensorWCQPE, mul_sub]
    rw [hdiff, tgNorm_tensorWCQPE]
    simpa only [one_mul] using mul_le_mul hwc₀_norm w10.base.vec_err_le (norm_nonneg _) zero_le_one
  have hs2Err := norm_unitary_mulVec_sub_le u2Impl u2Id s1Impl s1Id hs1Err hb2
  have hs3MidErr : ‖WithLp.toLp 2 (u3Impl.1 *ᵥ s2Id - u3Id.1 *ᵥ s2Id)‖ ≤
      δCoarse + 7 * δM + 127 * δF := by
    rw [hs2Id_eq]
    exact genBlocked_mux_l2_err_le mOut mMid ts w10 hδC0 hδM0 hδF0 hR1 hR2 hCoarse hM hF
      hInit hwc₀_norm hWinNorm
  have hs3Err := norm_unitary_mulVec_sub_le u3Impl u3Id s2Impl s2Id hs2Err hs3MidErr
  have hu2Impl_eq :
      (rQPE.compose (rLoInQPE16 7 (by decide))).embedUnitary w10.base.cWinLo.eval *
        (rQPE.compose (rWinHiInQPE 7 0 (by decide) (by decide) (Nat.zero_le _))).embedUnitary
          w10.base.cWinHi.eval = u2Impl := by
    dsimp only [u2Impl, uWinImpl16]
    rw [QRegister.embedUnitary_compose, QRegister.embedUnitary_compose,
      ← QRegister.embedUnitary_mul]
  have hstepImpl : wImplBlk.1 *ᵥ init = u4Impl.1 *ᵥ s3Impl := by
    dsimp only [wImplBlk, genBlockedImplUnitary]
    rw [hu2Impl_eq]
    dsimp only [u4Impl, s3Impl, u3Impl, s2Impl, s1Impl, u1Impl, FA, FB, rComb, rQPE, R₁c]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  have hstepId : wIdBlk.1 *ᵥ init = u4Id.1 *ᵥ s3Id := by
    dsimp only [wIdBlk, blockedIdealUnitary, u4Id, s3Id, u3Id, s2Id,
      u2Id, s1Id, u1Id, rComb, rQPE, R₁c, rW]
    simp only [Submonoid.coe_mul, ← Matrix.mulVec_mulVec]
  rw [hstepImpl, hstepId]
  refine (norm_unitary_mulVec_sub_le u4Impl u4Id s3Impl s3Id hs3Err
    (norm_mulVec_sub_le_of_opNorm u4Impl u4Id hs3IdNorm hop4)).trans_eq ?_
  ring

theorem gen_implQPEPertHyp {M nStd kTail tShift : ℕ} (wOuter wInner2 : ℕ)
    (ts : TailShiftParams M 10 7 nStd kTail tShift)
    (cCat : Circuit 11) (uCatIdeal : Unitary (2 ^ 11)) {αCat : ℂ} (hαCat : ‖αCat‖ = 1)
    (hCatZero : uCatIdeal.1 *ᵥ basisState 0 = αCat • CircuitModular.phaseGradientLowFactor 11 3)
    {δCat : ℝ} (hCatErr : ‖cCat.eval.1 - uCatIdeal.1‖ ≤ δCat)
    (cIqft : Circuit 16) (uIqftIdeal : Unitary (2 ^ 16))
    {δIqft : ℝ} (hIqftErr : ‖cIqft.eval.1 - uIqftIdeal.1‖ ≤ δIqft)
    (w10 : ThreeGearBondDeferSpec M 10 7 0) {uB : Unitary (2 ^ nUB wOuter wInner2)}
    {FG0 : Fin (2 ^ 2) → FGWalkCatU wOuter wInner2} {FG1 : Fin (2 ^ 3) → FGWalkCatU wOuter wInner2}
    {FG2 : Fin (2 ^ 4) → FGWalkCatU wOuter wInner2} {FG3 : Fin (2 ^ 5) → FGWalkCatU wOuter wInner2}
    {FG4 : Fin (2 ^ 6) → FGWalkCatU wOuter wInner2} {uSuperM uRefl2F : FGWalkCatU wOuter wInner2}
    {δCoarse δM δF : ℝ} (hδC0 : 0 ≤ δCoarse) (hδM0 : 0 ≤ δM) (hδF0 : 0 ≤ δF)
    (hCoarse : CoarseGearInvRel wOuter wInner2 nStd kTail uB FG0 FG1 FG2 FG3 FG4 δCoarse)
    (hInvM : WalkKStepRefl2InvErrLe wOuter wInner2 128 uB uSuperM δM)
    (hInvF : WalkRefl2InvErrLe wOuter wInner2 uB uRefl2F δF) :
    MultiGearQPE.ImplQPEPertHyp wOuter wInner2 M uCatIdeal uB w10.base.uIdeal uIqftIdeal
      (genBlockedImplUnitary (mOutUB wOuter) (mMidUB wInner2) ts cCat.eval w10.base.cWinHi.eval
        w10.base.cWinLo.eval cIqft.eval FG0 FG1 FG2 FG3 FG4 uSuperM uRefl2F)
      ((δCat + w10.base.δWin + δIqft) + (δCoarse + 7 * δM + 127 * δF)) := by
  obtain ⟨P_C, hClC, hRelC⟩ := hCoarse
  obtain ⟨P_M, hInitM, hR1M, hR2M, hErrM⟩ := hInvM
  obtain ⟨P_F, hInitF, hR1F, hR2F, hErrF⟩ := hInvF
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let P_inv : FGInvPred mOut mMid := fun x ↦ P_C x ∧ P_M x ∧ P_F x
  have hClInv : WalkSubspaceClosed wOuter wInner2 uB P_inv :=
    walkSubspaceClosed_inter hClC
      (walkSubspaceClosed_inter ⟨hInitM, hR1M, hR2M⟩ ⟨hInitF, hR1F, hR2F⟩)
  let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)
  let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB
  have hR₁_sq : R₁ * R₁ = 1 := QubitisedWalk.reflInUnitary_mul_self _
  have hR₂_sq : R₂ * R₂ = 1 := QubitisedWalk.reflPulledUnitary_mul_self _ _
  obtain ⟨hFoldStd, hFoldTop⟩ := ts_qpeAffinePerm_fold ts
  have hCoarseInv (xc : Fin (2 ^ 6)) (hxc : xc.val ≤ nStd + 1) :
      InvCatRel P_inv (uCatIdeal.1 *ᵥ basisState 0)
        (genCoarseFiber mOut mMid FG0 FG1 FG2 FG3 FG4 xc)
        (tailFusedScheduleFiber nStd (R₁ * (R₁ * R₂) ^ 1024) (R₁ * (R₁ * R₂) ^ kTail) R₁ xc)
        δCoarse := by
    have hHi := ts.hnStd_hi
    have hIdEq := tailFusedScheduleFiber_eq_tailTarget (b := 6) (nStd := nStd) (kStd := 1024)
      (kTail := kTail) hR₁_sq hR₂_sq (by decide) ts.hnStd_lo (by omega) hFoldStd hFoldTop xc hxc
    dsimp only at hIdEq
    rw [hCatZero]
    exact invCatRel_lift_smul_cat hαCat (invCatRel_restrict_closed (fun x hx ↦ hx.1)
      (fun x hx ↦ hIdEq ▸ walkSubspaceClosed_zpow hClInv _ x hx) (hRelC xc hxc))
  have hRelM_cat : InvCatRel P_inv (uCatIdeal.1 *ᵥ basisState 0) uSuperM
      (R₁ * (R₁ * R₂) ^ 128) δM := hCatZero ▸ invCatRel_lift_smul_cat hαCat
    ⟨walkSubspaceClosed_refl_pow hClInv 128, fun x hx ↦ hErrM x hx.2.1⟩
  have hRelF_cat : InvCatRel P_inv (uCatIdeal.1 *ᵥ basisState 0) uRefl2F R₂ δF :=
    hCatZero ▸ invCatRel_lift_smul_cat hαCat ⟨hClInv.2.2, fun x hx ↦ hErrF x hx.2.2⟩
  exact fun _ ψ _ hnorm ↦ genBlocked_impl_l2_err_le mOut mMid ts w10 hCatErr hIqftErr
    hδC0 hδM0 hδF0 hClInv.2.1 hClInv.2.2 hCoarseInv hRelM_cat.2 hRelF_cat.2 ψ (hClInv.1 ψ) hnorm

/-! ## Section 2: Symbolic Perturbation Transfer & Universal Peel `7`-Gear -/

/-- Fully general symbolic perturbation-to-measurement transfer hypothesis. -/
noncomputable abbrev SymbolicPertTransferHyp (wOuter wInner2 ko km M sRem : ℕ)
    (uB : Unitary (2 ^ nUB wOuter wInner2)) (uWinIdeal : Unitary (2 ^ 16)) (δTotUb : ℝ)
    (estimate : Fin (2 ^ combAncillasB wOuter wInner2 ko km sRem) → ℝ) : Prop :=
  ∀ (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (wBlk : Unitary (2 ^ (2 * 58 + actAncillas 16 11 (mOutUB wOuter) (mMidUB wInner2)))) {δW : ℝ},
    0 ≤ δW → δW ≤ δTotUb →
    MultiGearQPE.ImplQPEPertHyp wOuter wInner2 M exactPhaseGrad11RayUnitary uB uWinIdeal
      (phasedIqftUnitary 16 ζ hζ) wBlk δW →
    let sys : QRegister (2 * 58) (actWidth 16 11 (mOutUB wOuter) (mMidUB wInner2)) :=
      .block 0 (2 * 58) (sys_le_actWidth (mOutUB wOuter) (mMidUB wInner2))
    MeasuresLowEnergiesFG (thcHamiltonian P450.dfthc) p450Eta p450Delta p450Eps estimate
      ((rActLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0 (combARem wOuter wInner2 ko km)
        (midRemWidth wInner2 km)
        sRem).embedUnitary (sys.embedUnitary p450FswapUninterleave.eval⁻¹ * wBlk *
          sys.embedUnitary p450FswapUninterleave.eval))

theorem symbolicPertTransfer_of_box {wOuter wInner2 ko km M nStd sRem : ℕ}
    {uB : Unitary (2 ^ nUB wOuter wInner2)} {uWinIdeal : Unitary (2 ^ 16)}
    {ci wUb dCoarseUb dStdUb dTailUb dMUb dFUb δH eRef eUb gUb effUb kp : ℝ}
    {estimate : Fin (2 ^ combAncillasB wOuter wInner2 ko km sRem) → ℝ}
    (heRef : eRef ≤ eUb) (hCoarseUb : dCoarseUb ≤ (nStd : ℝ) * dStdUb + dTailUb)
    (hbox : TailShiftRayQuantSuperBox M nStd 10 7 ci wUb dStdUb dTailUb dMUb dFUb δH eUb gUb
      effUb kp)
    (hEstTransfer : TailShiftEstTransferHyp wOuter wInner2 ko km M sRem uB uWinIdeal δH eRef gUb kp
      estimate) :
    SymbolicPertTransferHyp wOuter wInner2 ko km M sRem uB uWinIdeal
      ((ci + wUb) + (dCoarseUb + 7 * dMUb + 127 * dFUb)) estimate := by
  obtain ⟨hM1, hM2, hg1, hg2, hband, hδH0, hg0, hkp0, heff0, heGap, hgH11, heffSq, hTot⟩ := hbox
  have hGap : (eRef + 0.1) - dfthcLowerBound ≤ gUb := by
    have hb := dfthcLowerBound_eq_rat
    rw [show (0.1 : ℝ) = 1 / 10 by norm_num]
    linarith
  have heff : spectralAmpEffNorm 97.3864 gUb ≤ effUb := by
    unfold spectralAmpEffNorm
    rw [show (97.3864 : ℝ) = 973864 / 10000 by norm_num]
    exact sqrt_le_iff.mpr ⟨heff0, heffSq⟩
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := Nat.cast_add_one_pos M
  have hpiNum : π ≤ 314159265358979323847 / 10 ^ 20 := by
    have h := pi_lt_d20
    norm_num at h ⊢
    linarith
  have hqpe : kp * (spectralAmpEffNorm 97.3864 gUb / 2) * (π / ((M : ℝ) + 1)) ≤
      kp * (effUb / 2) * ((314159265358979323847 / 10 ^ 20) / ((M : ℝ) + 1)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hkp0)
      (div_le_div_of_nonneg_right hpiNum hMpos.le)
      (div_nonneg pi_pos.le hMpos.le) (mul_nonneg hkp0 (by linarith))
  have hTot' : kp * (effUb / 2) * ((314159265358979323847 / 10 ^ 20) / ((M : ℝ) + 1)) + δH +
      gUb * ((ci + wUb) + ((nStd : ℝ) * dStdUb + dTailUb + 7 * dMUb + 127 * dFUb)) ≤ 1 / 1000 := by
    simpa only [Nat.reduceSub, Nat.reducePow, Nat.cast_ofNat] using hTot
  intro ζ hζ wBlk δW hδW0 hδW_le hPert
  have hBud : kp * (spectralAmpEffNorm 97.3864 gUb / 2) * (π / ((M : ℝ) + 1)) + δH +
      gUb * δW ≤ 0.001 := by
    rw [show (0.001 : ℝ) = 1 / 1000 by norm_num]
    exact (add_le_add (add_le_add hqpe le_rfl)
      (mul_le_mul_of_nonneg_left (by linarith) hg0)).trans hTot'
  exact hEstTransfer ζ hζ wBlk hδW0 ⟨hM1, hM2, hg1, hg2, hband⟩ hGap hgH11 hδH0 hBud hPert

theorem gen_realizesEst_of_iqft_pertTransfer {Var : Type} [Fintype Var] [DecidableEq Var]
    {n M nStd kTail tShift : ℕ} [NeZero (2 ^ n)]
    (wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (hsUbG0 : sUbG0 ≤ sRem + 14) (hsUbG1 : sUbG1 ≤ sRem + (13 - 0))
    (hsUbG2 : sUbG2 ≤ sRem + (12 - 0)) (hsUbG3 : sUbG3 ≤ sRem + (11 - 0))
    (hsUbG4 : sUbG4 ≤ sRem + (10 - 0)) (hsUbM : sUbM ≤ sRem + (7 - 0))
    (d : TwoGearRegimeData) (wc10 : ThreeGearWindowCirc 10 7 0)
    (w10 : ThreeGearBondDeferSpec M 10 7 0) (hw10_circ : w10.toCirc = wc10)
    (hw10_c : w10.cWinC = cWinPrefixAt d 10)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var) (cIqft : Circuit 16)
    (hIqftToff : cIqft.count .TOFF = 0) {δIqft ci wUb dCoarseUb dMUb dFUb δTotUb : ℝ}
    (hδIqft0 : 0 ≤ δIqft) (hCi : 858 / 10 ^ 11 + δIqft ≤ ci) (hwUb : w10.base.δWin ≤ wUb)
    (hIqftEx : ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), ‖cIqft.eval.1 - (phasedIqftUnitary 16 ζ hζ).1‖ ≤ δIqft)
    (estimate : Fin (2 ^ combAncillasB wOuter wInner2 ko km sRem) → ℝ)
    (rSys : FGSysReg n) (rAnc : FGAncReg wOuter wInner2 ko km sRem n)
    (hdisj : rSys.DisjointWires rAnc)
    {uB : Unitary (2 ^ nUB wOuter wInner2)} {FG0 : Fin (2 ^ 2) → FGWalkCatU wOuter wInner2}
    {FG1 : Fin (2 ^ 3) → FGWalkCatU wOuter wInner2} {FG2 : Fin (2 ^ 4) → FGWalkCatU wOuter wInner2}
    {FG3 : Fin (2 ^ 5) → FGWalkCatU wOuter wInner2} {FG4 : Fin (2 ^ 6) → FGWalkCatU wOuter wInner2}
    {uSuperM uRefl2F : FGWalkCatU wOuter wInner2}
    {pLocG0 : FGCircAt Var 2 wOuter wInner2 ko km sUbG0}
    {pLocG1 : FGCircAt Var 3 wOuter wInner2 ko km sUbG1}
    {pLocG2 : FGCircAt Var 4 wOuter wInner2 ko km sUbG2}
    {pLocG3 : FGCircAt Var 5 wOuter wInner2 ko km sUbG3}
    {pLocG4 : FGCircAt Var 6 wOuter wInner2 ko km sUbG4}
    {pSuperM : FGCircAt Var 3 wOuter wInner2 ko km sUbM}
    {pRefl2F : FGCircB Var wOuter wInner2 ko km sRem}
    (hLoc0 : CleanGearMuxAt 2 wOuter wInner2 ko km sUbG0 hkOut hkMid v FG0 pLocG0)
    (hLoc1 : CleanGearMuxAt 3 wOuter wInner2 ko km sUbG1 hkOut hkMid v FG1 pLocG1)
    (hLoc2 : CleanGearMuxAt 4 wOuter wInner2 ko km sUbG2 hkOut hkMid v FG2 pLocG2)
    (hLoc3 : CleanGearMuxAt 5 wOuter wInner2 ko km sUbG3 hkOut hkMid v FG3 pLocG3)
    (hLoc4 : CleanGearMuxAt 6 wOuter wInner2 ko km sUbG4 hkOut hkMid v FG4 pLocG4)
    (hCleanM : CleanWalkRefl2At 3 wOuter wInner2 ko km 0 sUbM hkOut hkMid v uSuperM pSuperM)
    (hCleanF : CleanWalkRefl2 wOuter wInner2 ko km 0 sRem hkOut hkMid v uRefl2F pRefl2F)
    {δCoarse δM δF : ℝ} (hδC0 : 0 ≤ δCoarse) (hδM0 : 0 ≤ δM) (hδF0 : 0 ≤ δF)
    (hCoarse : CoarseGearInvRel wOuter wInner2 nStd kTail uB FG0 FG1 FG2 FG3 FG4 δCoarse)
    (hInvM : WalkKStepRefl2InvErrLe wOuter wInner2 128 uB uSuperM δM)
    (hInvF : WalkRefl2InvErrLe wOuter wInner2 uB uRefl2F δF)
    (hCUb : δCoarse ≤ dCoarseUb) (hMUb : δM ≤ dMUb) (hFUb : δF ≤ dFUb)
    (hBudLe : (ci + wUb) + (dCoarseUb + 7 * dMUb + 127 * dFUb) ≤ δTotUb)
    (hPertTransfer : SymbolicPertTransferHyp wOuter wInner2 ko km M sRem uB w10.base.uIdeal δTotUb
      estimate) :
    RealizesP450GroundQPEFG rSys rAnc hdisj estimate
      (genTopCircProg wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
        hkOut hkMid hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 ts v approxPhaseGrad11Ray cIqft
        pLocG0 pLocG1 pLocG2 pLocG3 pLocG4 pSuperM pRefl2F rSys rAnc) := by
  obtain ⟨ζ, hζ, hIqft⟩ := hIqftEx
  have hWindow0 := w10.base.hδ_nonneg
  have hδW0 : 0 ≤ ((858 / 10 ^ 11 : ℝ) + w10.base.δWin + δIqft) +
      (δCoarse + 7 * δM + 127 * δF) := by linarith
  have hδW_le : ((858 / 10 ^ 11 : ℝ) + w10.base.δWin + δIqft) +
      (δCoarse + 7 * δM + 127 * δF) ≤ δTotUb := by linarith
  have hPert := gen_implQPEPertHyp wOuter wInner2 ts approxPhaseGrad11Ray exactPhaseGrad11RayUnitary
    norm_phaseGrad11RayScalar exactPhaseGrad11RayUnitary_mulVec_zero
    norm_approxPhaseGrad11Ray_sub_le
    cIqft (phasedIqftUnitary 16 ζ hζ) hIqft w10 hδC0 hδM0 hδF0 hCoarse hInvM hInvF
  exact ⟨_, hPertTransfer ζ hζ _ hδW0 hδW_le hPert,
    genTopLevel_realizes wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
      hkOut hkMid hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 w10 hw10_circ hw10_c ts v
      approxPhaseGrad11Ray approxPhaseGrad11Ray_count_toff cIqft hIqftToff
      hLoc0 hLoc1 hLoc2 hLoc3 hLoc4 hCleanM hCleanF rSys rAnc hdisj⟩

/-- Slot-B peel certificate: requires a clean `kB`-step super-reflection when `top % 2 = 1`, and
only `0 ≤ dBUb` when `top % 2 ≠ 1` (since `peelGearLocalDyn` ignores `pB` on even `top`). -/
def PeelSlotBCert {Var : Type} [Fintype Var] [DecidableEq Var]
    (bGear wOuter wInner2 ko km sUb top kB : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (v : Var)
    (uB : Unitary (2 ^ nUB wOuter wInner2)) (pB : FGCircAt Var bGear wOuter wInner2 ko km sUb)
    (dBUb : ℝ) : Prop :=
  if top % 2 = 1 then
    ∃ (uSlotB : FGWalkCatU wOuter wInner2) (δB : ℝ),
      CleanWalkRefl2At bGear wOuter wInner2 ko km 0 sUb hkOut hkMid v uSlotB pB ∧
      0 ≤ δB ∧ WalkKStepRefl2InvErrLe wOuter wInner2 kB uB uSlotB δB ∧ δB ≤ dBUb
  else
    0 ≤ dBUb

theorem PeelSlotBCert.of_odd {Var : Type} [Fintype Var] [DecidableEq Var]
    {bGear wOuter wInner2 ko km sUb top kB : ℕ} {hkOut : ko ≤ wOuter} {hkMid : km ≤ wInner2}
    {v : Var}
    {uB : Unitary (2 ^ nUB wOuter wInner2)} {pB : FGCircAt Var bGear wOuter wInner2 ko km sUb}
    {uSlotB : FGWalkCatU wOuter wInner2} {δB dBUb : ℝ}
    (hClean : CleanWalkRefl2At bGear wOuter wInner2 ko km 0 sUb hkOut hkMid v uSlotB pB)
    (hδ0 : 0 ≤ δB) (hInv : WalkKStepRefl2InvErrLe wOuter wInner2 kB uB uSlotB δB)
    (hUb : δB ≤ dBUb) :
    PeelSlotBCert bGear wOuter wInner2 ko km sUb top kB hkOut hkMid v uB pB dBUb := by
  dsimp only [PeelSlotBCert]
  split_ifs
  · exact ⟨uSlotB, δB, hClean, hδ0, hInv, hUb⟩
  · linarith

theorem PeelSlotBCert.of_even {Var : Type} [Fintype Var] [DecidableEq Var]
    {bGear wOuter wInner2 ko km sUb top kB : ℕ} (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2)
    (v : Var)
    (uB : Unitary (2 ^ nUB wOuter wInner2)) (pB : FGCircAt Var bGear wOuter wInner2 ko km sUb)
    {dBUb : ℝ} (hEven : top % 2 ≠ 1) (hd0 : 0 ≤ dBUb) :
    PeelSlotBCert bGear wOuter wInner2 ko km sUb top kB hkOut hkMid v uB pB dBUb := by
  dsimp only [PeelSlotBCert]
  rw [ite_eq_right hEven]
  exact hd0

theorem peelGear_unpack {Var : Type} [Fintype Var] [DecidableEq Var]
    {bGear wOuter wInner2 ko km sUb top kA kB : ℕ} (hbGear1 : 1 ≤ bGear) (htop_lt : top < 2 ^ bGear)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (v : Var)
    {uB : Unitary (2 ^ nUB wOuter wInner2)} {uSlotA : FGWalkCatU wOuter wInner2}
    {pA pB : FGCircAt Var bGear wOuter wInner2 ko km sUb} {δA dAUb dBUb : ℝ}
    (hCleanA : CleanWalkRefl2At bGear wOuter wInner2 ko km 0 sUb hkOut hkMid v uSlotA pA)
    (hδA0 : 0 ≤ δA) (hInvA : WalkKStepRefl2InvErrLe wOuter wInner2 kA uB uSlotA δA)
    (hAUb : δA ≤ dAUb)
    (hSlotB : PeelSlotBCert bGear wOuter wInner2 ko km sUb top kB hkOut hkMid v uB pB dBUb) :
    ∃ (FG : Fin (2 ^ bGear) → FGWalkCatU wOuter wInner2)
      (P : FGInvPred (mOutUB wOuter) (mMidUB wInner2)) (δG : ℝ),
      CleanGearMuxAt bGear wOuter wInner2 ko km sUb hkOut hkMid v FG
        (peelGearLocalDyn bGear 11 (mOutUB wOuter) (mMidUB wInner2) sUb top hbGear1 htop_lt v
          (combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid) pA pB) ∧
      WalkSubspaceClosed wOuter wInner2 uB P ∧ 0 ≤ δG ∧ δG ≤ dAUb + dBUb ∧
      ∀ x : Fin (2 ^ bGear),
        let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk (mOutUB wOuter) (mMidUB wInner2))
        let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk (mOutUB wOuter) (mMidUB wInner2)) uB
        let W := R₁ * R₂
        InvCatRel P (CircuitModular.phaseGradientLowFactor 11 3) (FG x)
          (peelGearFiber top htop_lt (R₁ * W ^ kA) (R₁ * W ^ kB) R₁ x) δG := by
  obtain ⟨PA, hInitA, hR1A, hR2A, hErrA⟩ := hInvA
  have hClA : WalkSubspaceClosed wOuter wInner2 uB PA := ⟨hInitA, hR1A, hR2A⟩
  have hCov := combWalkReflCovers bGear 11 wOuter wInner2 0 sUb ko km hkOut hkMid
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)
  dsimp only [PeelSlotBCert] at hSlotB
  by_cases hOdd : top % 2 = 1
  · rw [ite_eq_left hOdd] at hSlotB
    obtain ⟨uSlotB, δB, hCleanB, hδB0, ⟨PB, hInitB, hR1B, hR2B, hErrB⟩, hBUb⟩ := hSlotB
    let P : FGInvPred mOut mMid := fun x ↦ PA x ∧ PB x
    have hCl : WalkSubspaceClosed wOuter wInner2 uB P :=
      walkSubspaceClosed_inter hClA ⟨hInitB, hR1B, hR2B⟩
    refine ⟨patFlipTwoStepFiber uSlotA uSlotB R₁c ⟨top - 1, by omega⟩, P, δA + δB, ?_,
      hCl, add_nonneg hδA0 hδB0, add_le_add hAUb hBUb, fun x ↦ ?_⟩
    · dsimp only [CleanGearMuxAt, peelGearLocalDyn]
      rw [ite_eq_left hOdd]
      exact patFlipTwoStepLocalDyn_cleanRealizes bGear 11 mOut mMid sUb hbGear1
        ⟨top - 1, by omega⟩ v hCov hCleanA hCleanB
    · dsimp only [peelGearFiber]
      rw [ite_eq_left hOdd]
      exact invCatRelPatFlipTwoStepFiber (invCatRel_reflInUnitary mOut mMid hCl.2.1)
        ⟨walkSubspaceClosed_refl_pow hCl kA, fun v hv ↦ hErrA v hv.1⟩
        ⟨walkSubspaceClosed_refl_pow hCl kB, fun v hv ↦ hErrB v hv.2⟩ ⟨top - 1, by omega⟩ x
  · rw [ite_eq_right hOdd] at hSlotB
    refine ⟨singleSignedFiber uSlotA R₁c ⟨top, htop_lt⟩, PA, δA, ?_,
      hClA, hδA0, by linarith, fun x ↦ ?_⟩
    · dsimp only [CleanGearMuxAt, peelGearLocalDyn]
      rw [ite_eq_right hOdd]
      exact singleSignedLocalDyn_cleanRealizes bGear 11 mOut mMid sUb hbGear1
        ⟨top, htop_lt⟩ v hCov hCleanA
    · dsimp only [peelGearFiber]
      rw [ite_eq_right hOdd]
      exact invCatRelSingleSignedFiber (invCatRel_reflInUnitary mOut mMid hClA.2.1)
        ⟨walkSubspaceClosed_refl_pow hClA kA, hErrA⟩ ⟨top, htop_lt⟩ x

theorem peelTop_lt_pow {nStd : ℕ} (hnHi : nStd ≤ 46) (g b : ℕ)
    (hgb : 47 < 2 ^ (g + b) := by decide) : peelTop nStd g < 2 ^ b := by
  dsimp only [peelTop]
  exact Nat.div_lt_of_lt_mul (by
    rw [← pow_add]
    omega)

/-- Bundled walk certificate for the universal symbolic peel `7`-Gear engine (`32 ≤ nStd ≤ 46`). -/
structure SymbolicSevenGearCert {Var : Type} [Fintype Var] [DecidableEq Var]
    (wOuter wInner2 ko km nStd kTail sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (v : Var) (uB : Unitary (2 ^ nUB wOuter wInner2))
    (p0A p0B : FGCircAt Var 2 wOuter wInner2 ko km sUbG0)
    (p1A p1B : FGCircAt Var 3 wOuter wInner2 ko km sUbG1)
    (p2A p2B : FGCircAt Var 4 wOuter wInner2 ko km sUbG2)
    (p3A p3B : FGCircAt Var 5 wOuter wInner2 ko km sUbG3)
    (p4A p4B : FGCircAt Var 6 wOuter wInner2 ko km sUbG4)
    (pSuperM : FGCircAt Var 3 wOuter wInner2 ko km sUbM)
    (pRefl2F : FGCircB Var wOuter wInner2 ko km sRem)
    (d0AUb d0BUb d1AUb d1BUb d2AUb d2BUb d3AUb d3BUb d4AUb d4BUb dMUb dFUb : ℝ) : Prop where
  /-- Unitary and error witnesses across `G0`, peel stages `G1..G4`, `Stage M`, and `Stage F`. -/
  exists_witness :
    ∃ (u0A u0B u1A u2A u3A u4A uSuperM uRefl2F : FGWalkCatU wOuter wInner2)
      (δ0A δ0B δ1A δ2A δ3A δ4A δM δF : ℝ),
      CleanWalkRefl2At 2 wOuter wInner2 ko km 0 sUbG0 hkOut hkMid v u0A p0A ∧
      CleanWalkRefl2At 2 wOuter wInner2 ko km 0 sUbG0 hkOut hkMid v u0B p0B ∧
      CleanWalkRefl2At 3 wOuter wInner2 ko km 0 sUbG1 hkOut hkMid v u1A p1A ∧
      CleanWalkRefl2At 4 wOuter wInner2 ko km 0 sUbG2 hkOut hkMid v u2A p2A ∧
      CleanWalkRefl2At 5 wOuter wInner2 ko km 0 sUbG3 hkOut hkMid v u3A p3A ∧
      CleanWalkRefl2At 6 wOuter wInner2 ko km 0 sUbG4 hkOut hkMid v u4A p4A ∧
      CleanWalkRefl2At 3 wOuter wInner2 ko km 0 sUbM hkOut hkMid v uSuperM pSuperM ∧
      CleanWalkRefl2 wOuter wInner2 ko km 0 sRem hkOut hkMid v uRefl2F pRefl2F ∧
      0 ≤ δ0A ∧ 0 ≤ δ0B ∧ 0 ≤ δ1A ∧ 0 ≤ δ2A ∧ 0 ≤ δ3A ∧ 0 ≤ δ4A ∧ 0 ≤ δM ∧ 0 ≤ δF ∧
      WalkKStepRefl2InvErrLe wOuter wInner2 (peelK 4) uB u0A δ0A ∧
      WalkKStepRefl2InvErrLe wOuter wInner2 (peelTail nStd kTail 4) uB u0B δ0B ∧
      WalkKStepRefl2InvErrLe wOuter wInner2 (peelStepA nStd kTail 3) uB u1A δ1A ∧
      WalkKStepRefl2InvErrLe wOuter wInner2 (peelStepA nStd kTail 2) uB u2A δ2A ∧
      WalkKStepRefl2InvErrLe wOuter wInner2 (peelStepA nStd kTail 1) uB u3A δ3A ∧
      WalkKStepRefl2InvErrLe wOuter wInner2 (peelStepA nStd kTail 0) uB u4A δ4A ∧
      WalkKStepRefl2InvErrLe wOuter wInner2 128 uB uSuperM δM ∧
      WalkRefl2InvErrLe wOuter wInner2 uB uRefl2F δF ∧
      δ0A ≤ d0AUb ∧ δ0B ≤ d0BUb ∧ δ1A ≤ d1AUb ∧ δ2A ≤ d2AUb ∧ δ3A ≤ d3AUb ∧ δ4A ≤ d4AUb ∧
      δM ≤ dMUb ∧ δF ≤ dFUb ∧
      PeelSlotBCert 3 wOuter wInner2 ko km sUbG1 (peelTop nStd 3) (peelStepB nStd kTail 3)
        hkOut hkMid v uB p1B d1BUb ∧
      PeelSlotBCert 4 wOuter wInner2 ko km sUbG2 (peelTop nStd 2) (peelStepB nStd kTail 2)
        hkOut hkMid v uB p2B d2BUb ∧
      PeelSlotBCert 5 wOuter wInner2 ko km sUbG3 (peelTop nStd 1) (peelStepB nStd kTail 1)
        hkOut hkMid v uB p3B d3BUb ∧
      PeelSlotBCert 6 wOuter wInner2 ko km sUbG4 (peelTop nStd 0) (peelStepB nStd kTail 0)
        hkOut hkMid v uB p4B d4BUb

/-- Walk-and-reflection `T`-gate count for the universal symbolic peel `7`-Gear engine. -/
def symbolicSevenGearWalkCtrlTCount
    (tShift aRem t0A t0B t1A t1B t2A t2B t3A t3B t4A t4B tM tF : ℕ) : ℕ :=
  76 * (aRem - 1) + 116 + tShift +
    t0A + t0B + t1A + t1B + t2A + t2B + t3A + t3B + t4A + t4B +
    walkCtrlTCount 3 7 aRem tM + walkCtrlTCount 7 127 aRem tF

/-- Total `T`-gate count for the universal symbolic peel `7`-Gear engine. -/
def symbolicSevenGearMasterTCount
    (tShift aRem tCat tWin tIqft t0A t0B t1A t1B t2A t2B t3A t3B t4A t4B tM tF : ℕ) : ℕ :=
  tCat + tWin + tIqft +
    symbolicSevenGearWalkCtrlTCount tShift aRem t0A t0B t1A t1B t2A t2B t3A t3B t4A t4B tM tF

/-- Universal symbolic peel `7`-Gear QPE program (`32 ≤ nStd ≤ 46`) at arbitrary
`(M, nStd, kTail, tShift, d, wc10, cIqft)`. -/
def p450SymbolicSevenGearProg {Var : Type} {n M nStd kTail tShift : ℕ}
    (wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hnHi : nStd ≤ 46)
    (hsUbG0 : sUbG0 ≤ sRem + 14) (hsUbG1 : sUbG1 ≤ sRem + (13 - 0))
    (hsUbG2 : sUbG2 ≤ sRem + (12 - 0)) (hsUbG3 : sUbG3 ≤ sRem + (11 - 0))
    (hsUbG4 : sUbG4 ≤ sRem + (10 - 0)) (hsUbM : sUbM ≤ sRem + (7 - 0))
    (d : TwoGearRegimeData) (wc10 : ThreeGearWindowCirc 10 7 0)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var) (cIqft : Circuit 16)
    (p0A p0B : FGCircAt Var 2 wOuter wInner2 ko km sUbG0)
    (p1A p1B : FGCircAt Var 3 wOuter wInner2 ko km sUbG1)
    (p2A p2B : FGCircAt Var 4 wOuter wInner2 ko km sUbG2)
    (p3A p3B : FGCircAt Var 5 wOuter wInner2 ko km sUbG3)
    (p4A p4B : FGCircAt Var 6 wOuter wInner2 ko km sUbG4)
    (pSuperM : FGCircAt Var 3 wOuter wInner2 ko km sUbM)
    (pRefl2F : FGCircB Var wOuter wInner2 ko km sRem)
    (rSys : FGSysReg n) (rAnc : FGAncReg wOuter wInner2 ko km sRem n) : DynamicCircuit Var n :=
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let refl := combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid
  genTopCircProg wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
    hkOut hkMid hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 ts v approxPhaseGrad11Ray cIqft
    (topG0LocalDyn 11 mOut mMid sUbG0 v refl p0A p0B)
    (peelGearLocalDyn 3 11 mOut mMid sUbG1 (peelTop nStd 3) (by decide)
      (peelTop_lt_pow hnHi 3 3) v refl p1A p1B)
    (peelGearLocalDyn 4 11 mOut mMid sUbG2 (peelTop nStd 2) (by decide)
      (peelTop_lt_pow hnHi 2 4) v refl p2A p2B)
    (peelGearLocalDyn 5 11 mOut mMid sUbG3 (peelTop nStd 1) (by decide)
      (peelTop_lt_pow hnHi 1 5) v refl p3A p3B)
    (peelGearLocalDyn 6 11 mOut mMid sUbG4 (peelTop nStd 0) (by decide)
      (peelTop_lt_pow hnHi 0 6) v refl p4A p4B)
    pSuperM pRefl2F rSys rAnc

theorem p450SymbolicSevenGearProg_const_cost_of_eq {Var : Type}
    {n M nStd kTail tShift wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM : ℕ}
    {tWin tIqft t0A t0B t1A t1B t2A t2B t3A t3B t4A t4B tM tF tTot c : ℕ}
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hnHi : nStd ≤ 46)
    (hsUbG0 : sUbG0 ≤ sRem + 14) (hsUbG1 : sUbG1 ≤ sRem + (13 - 0))
    (hsUbG2 : sUbG2 ≤ sRem + (12 - 0)) (hsUbG3 : sUbG3 ≤ sRem + (11 - 0))
    (hsUbG4 : sUbG4 ≤ sRem + (10 - 0)) (hsUbM : sUbM ≤ sRem + (7 - 0))
    (d : TwoGearRegimeData) (wc10 : ThreeGearWindowCirc 10 7 0)
    (w10 : ThreeGearBondDeferSpec M 10 7 0) (hw10_circ : w10.toCirc = wc10)
    (hw10_c : w10.cWinC = cWinPrefixAt d 10)
    (hw10_t : w10.base.cWinHi.count .T + w10.base.cWinLo.count .T ≤ tWin)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var)
    {cIqft : Circuit 16} (hIqftToff : cIqft.count .TOFF = 0) (hIqftT : cIqft.count .T ≤ tIqft)
    {p0A p0B : FGCircAt Var 2 wOuter wInner2 ko km sUbG0}
    {p1A p1B : FGCircAt Var 3 wOuter wInner2 ko km sUbG1}
    {p2A p2B : FGCircAt Var 4 wOuter wInner2 ko km sUbG2}
    {p3A p3B : FGCircAt Var 5 wOuter wInner2 ko km sUbG3}
    {p4A p4B : FGCircAt Var 6 wOuter wInner2 ko km sUbG4}
    {pSuperM : FGCircAt Var 3 wOuter wInner2 ko km sUbM}
    {pRefl2F : FGCircB Var wOuter wInner2 ko km sRem}
    (h0ATf : p0A.count .TOFF = 0) (h0BTf : p0B.count .TOFF = 0) (h1ATf : p1A.count .TOFF = 0)
    (h1BTf : p1B.count .TOFF = 0) (h2ATf : p2A.count .TOFF = 0) (h2BTf : p2B.count .TOFF = 0)
    (h3ATf : p3A.count .TOFF = 0) (h3BTf : p3B.count .TOFF = 0) (h4ATf : p4A.count .TOFF = 0)
    (h4BTf : p4B.count .TOFF = 0) (hMTf : pSuperM.count .TOFF = 0) (hFTf : pRefl2F.count .TOFF = 0)
    (h0AT : p0A.count .T ≤ t0A) (h0BT : p0B.count .T ≤ t0B) (h1AT : p1A.count .T ≤ t1A)
    (h1BT : p1B.count .T ≤ t1B) (h2AT : p2A.count .T ≤ t2A) (h2BT : p2B.count .T ≤ t2B)
    (h3AT : p3A.count .T ≤ t3A) (h3BT : p3B.count .T ≤ t3B) (h4AT : p4A.count .T ≤ t4A)
    (h4BT : p4B.count .T ≤ t4B) (hMT : pSuperM.count .T ≤ tM) (hFT : pRefl2F.count .T ≤ tF)
    (rSys : FGSysReg n) (rAnc : FGAncReg wOuter wInner2 ko km sRem n)
    (htTotal : symbolicSevenGearMasterTCount tShift (combARem wOuter wInner2 ko km) 1036 tWin tIqft
      t0A t0B t1A t1B t2A t2B t3A t3B t4A t4B tM tF = tTot := by decide)
    (hCost : (systemQubits_local + combAncillasB wOuter wInner2 ko km sRem) * tTot = c := by decide)
      :
    (p450SymbolicSevenGearProg wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
        hkOut hkMid hnHi hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 ts v cIqft
        p0A p0B p1A p1B p2A p2B p3A p3B p4A p4B pSuperM pRefl2F rSys rAnc).count .TOFF = 0 ∧
      (systemQubits_local + combAncillasB wOuter wInner2 ko km sRem) *
        (p450SymbolicSevenGearProg wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
          hkOut hkMid hnHi hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 ts v cIqft
          p0A p0B p1A p1B p2A p2B p3A p3B p4A p4B pSuperM pRefl2F rSys rAnc).count .T ≤ c := by
  let aRem := combARem wOuter wInner2 ko km
  let refl := combWalkReflRegs 11 wOuter wInner2 ko km hkOut hkMid
  refine ⟨genTopCircProg_count_toff wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
      hkOut hkMid hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 w10 hw10_circ hw10_c ts v
      approxPhaseGrad11Ray_count_toff hIqftToff
      (topG0LocalDyn_count_toff _ _ _ _ v refl h0ATf h0BTf)
      (peelGearLocalDyn_count_toff 3 _ _ _ _ _ _ _ v refl h1ATf h1BTf)
      (peelGearLocalDyn_count_toff 4 _ _ _ _ _ _ _ v refl h2ATf h2BTf)
      (peelGearLocalDyn_count_toff 5 _ _ _ _ _ _ _ v refl h3ATf h3BTf)
      (peelGearLocalDyn_count_toff 6 _ _ _ _ _ _ _ v refl h4ATf h4BTf)
      hMTf hFTf rSys rAnc, ?_⟩
  rw [← hCost, ← htTotal]
  refine Nat.mul_le_mul_left _ ?_
  have hc0 : (topG0LocalDyn 11 (mOutUB wOuter) (mMidUB wInner2) sUbG0 v refl p0A p0B).count .T ≤
      t0A + t0B + 12 * (aRem - 1) + 4 := by
    rw [topG0LocalDyn_count_t]
    omega
  have hc1 := peelGearLocalDyn_count_t_le 3 11 (mOutUB wOuter) (mMidUB wInner2) sUbG1
    (peelTop nStd 3) t1A t1B (by decide) (peelTop_lt_pow hnHi 3 3) v refl h1AT h1BT
  have hc2 := peelGearLocalDyn_count_t_le 4 11 (mOutUB wOuter) (mMidUB wInner2) sUbG2
    (peelTop nStd 2) t2A t2B (by decide) (peelTop_lt_pow hnHi 2 4) v refl h2AT h2BT
  have hc3 := peelGearLocalDyn_count_t_le 5 11 (mOutUB wOuter) (mMidUB wInner2) sUbG3
    (peelTop nStd 1) t3A t3B (by decide) (peelTop_lt_pow hnHi 1 5) v refl h3AT h3BT
  have hc4 := peelGearLocalDyn_count_t_le 6 11 (mOutUB wOuter) (mMidUB wInner2) sUbG4
    (peelTop nStd 0) t4A t4B (by decide) (peelTop_lt_pow hnHi 0 6) v refl h4AT h4BT
  have hTop :=
    genTopCircProg_count_t_le wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
    1036 tWin tIqft (t0A + t0B + 12 * (aRem - 1) + 4)
    (t1A + t1B + 16 * (aRem - 1) + 8 * (3 - 1))
    (t2A + t2B + 16 * (aRem - 1) + 8 * (4 - 1))
    (t3A + t3B + 16 * (aRem - 1) + 8 * (5 - 1))
    (t4A + t4B + 16 * (aRem - 1) + 8 * (6 - 1)) tM tF
    hkOut hkMid hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 w10 hw10_circ hw10_c hw10_t ts v
    approxPhaseGrad11Ray_count_t.le hIqftT hc0 hc1 hc2 hc3 hc4 hMT hFT rSys rAnc
  refine hTop.trans ?_
  dsimp only [aRem, symbolicSevenGearMasterTCount, symbolicSevenGearWalkCtrlTCount]
  omega

theorem realizesEst_p450SymbolicSevenGear_of_pertTransfer {Var : Type} [Fintype Var]
    [DecidableEq Var] {n M nStd kTail tShift : ℕ} [NeZero (2 ^ n)]
    (wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hnHi : nStd ≤ 46)
    (hsUbG0 : sUbG0 ≤ sRem + 14) (hsUbG1 : sUbG1 ≤ sRem + (13 - 0))
    (hsUbG2 : sUbG2 ≤ sRem + (12 - 0)) (hsUbG3 : sUbG3 ≤ sRem + (11 - 0))
    (hsUbG4 : sUbG4 ≤ sRem + (10 - 0)) (hsUbM : sUbM ≤ sRem + (7 - 0))
    (d : TwoGearRegimeData) (wc10 : ThreeGearWindowCirc 10 7 0)
    (w10 : ThreeGearBondDeferSpec M 10 7 0) (hw10_circ : w10.toCirc = wc10)
    (hw10_c : w10.cWinC = cWinPrefixAt d 10)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var) (cIqft : Circuit 16)
    (hIqftToff : cIqft.count .TOFF = 0)
    {δIqft ci wUb d0AUb d0BUb d1AUb d1BUb d2AUb d2BUb d3AUb d3BUb d4AUb d4BUb dMUb dFUb δTotUb : ℝ}
    (hδIqft0 : 0 ≤ δIqft) (hCi : 858 / 10 ^ 11 + δIqft ≤ ci) (hwUb : w10.base.δWin ≤ wUb)
    (hIqftEx : ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), ‖cIqft.eval.1 - (phasedIqftUnitary 16 ζ hζ).1‖ ≤ δIqft)
    (estimate : Fin (2 ^ combAncillasB wOuter wInner2 ko km sRem) → ℝ)
    (rSys : FGSysReg n) (rAnc : FGAncReg wOuter wInner2 ko km sRem n)
    (hdisj : rSys.DisjointWires rAnc)
    {uB : Unitary (2 ^ nUB wOuter wInner2)} {p0A p0B : FGCircAt Var 2 wOuter wInner2 ko km sUbG0}
    {p1A p1B : FGCircAt Var 3 wOuter wInner2 ko km sUbG1}
    {p2A p2B : FGCircAt Var 4 wOuter wInner2 ko km sUbG2}
    {p3A p3B : FGCircAt Var 5 wOuter wInner2 ko km sUbG3}
    {p4A p4B : FGCircAt Var 6 wOuter wInner2 ko km sUbG4}
    {pSuperM : FGCircAt Var 3 wOuter wInner2 ko km sUbM}
    {pRefl2F : FGCircB Var wOuter wInner2 ko km sRem}
    (hWalk : SymbolicSevenGearCert wOuter wInner2 ko km nStd kTail sRem sUbG0 sUbG1 sUbG2 sUbG3
      sUbG4
      sUbM hkOut hkMid v uB p0A p0B p1A p1B p2A p2B p3A p3B p4A p4B pSuperM pRefl2F
      d0AUb d0BUb d1AUb d1BUb d2AUb d2BUb d3AUb d3BUb d4AUb d4BUb dMUb dFUb)
    (hBudLe : (ci + wUb) +
      ((d0AUb + d0BUb + d1AUb + d1BUb + d2AUb + d2BUb + d3AUb + d3BUb + d4AUb + d4BUb) +
        7 * dMUb + 127 * dFUb) ≤ δTotUb)
    (hPertTransfer : SymbolicPertTransferHyp wOuter wInner2 ko km M sRem uB w10.base.uIdeal δTotUb
      estimate) :
    RealizesP450GroundQPEFG rSys rAnc hdisj estimate
      (p450SymbolicSevenGearProg wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
        hkOut hkMid hnHi hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 ts v cIqft
        p0A p0B p1A p1B p2A p2B p3A p3B p4A p4B pSuperM pRefl2F rSys rAnc) := by
  obtain ⟨u0A, u0B, u1A, u2A, u3A, u4A, uSuperM, uRefl2F, δ0A, δ0B, δ1A, δ2A, δ3A, δ4A, δM, δF,
    hc0A, hc0B, hc1A, hc2A, hc3A, hc4A, hcM, hcF, h0A0, h0B0, h1A0, h2A0, h3A0, h4A0, hM0, hF0,
    hi0A, hi0B, hi1A, hi2A, hi3A, hi4A, hiM, hiF, hb0A, hb0B, hb1A, hb2A, hb3A, hb4A, hbM, hbF,
    hsB1, hsB2, hsB3, hsB4⟩ := hWalk.exists_witness
  obtain ⟨P0A, hInit0A, hR10A, hR20A, hErr0A⟩ := hi0A
  obtain ⟨P0B, hInit0B, hR10B, hR20B, hErr0B⟩ := hi0B
  have hCl0 : WalkSubspaceClosed wOuter wInner2 uB (fun x ↦ P0A x ∧ P0B x) :=
    walkSubspaceClosed_inter ⟨hInit0A, hR10A, hR20A⟩ ⟨hInit0B, hR10B, hR20B⟩
  obtain ⟨FG1, P1, δG1, hLoc1, hCl1, hδ10, hδ1Ub, hRel1⟩ := peelGear_unpack (bGear := 3)
    (by decide) (peelTop_lt_pow hnHi 3 3) hkOut hkMid v hc1A h1A0 hi1A hb1A hsB1
  obtain ⟨FG2, P2, δG2, hLoc2, hCl2, hδ20, hδ2Ub, hRel2⟩ := peelGear_unpack (bGear := 4)
    (by decide) (peelTop_lt_pow hnHi 2 4) hkOut hkMid v hc2A h2A0 hi2A hb2A hsB2
  obtain ⟨FG3, P3, δG3, hLoc3, hCl3, hδ30, hδ3Ub, hRel3⟩ := peelGear_unpack (bGear := 5)
    (by decide) (peelTop_lt_pow hnHi 1 5) hkOut hkMid v hc3A h3A0 hi3A hb3A hsB3
  obtain ⟨FG4, P4, δG4, hLoc4, hCl4, hδ40, hδ4Ub, hRel4⟩ := peelGear_unpack (bGear := 6)
    (by decide) (peelTop_lt_pow hnHi 0 6) hkOut hkMid v hc4A h4A0 hi4A hb4A hsB4
  let mOut := mOutUB wOuter
  let mMid := mMidUB wInner2
  let R₁c := QubitisedWalk.reflInUnitary (inAllWalkCat 11 mOut mMid)
  let R₁ := QubitisedWalk.reflInUnitary (rAllInWalk mOut mMid)
  let R₂ := QubitisedWalk.reflPulledUnitary (rMidInWalk mOut mMid) uB
  let W := R₁ * R₂
  let cat₀ := CircuitModular.phaseGradientLowFactor 11 3
  have hLoc0 := topG0LocalDyn_cleanRealizes 11 mOut mMid sUbG0 v
    (combWalkReflCovers 2 11 wOuter wInner2 0 sUbG0 ko km hkOut hkMid) hc0A hc0B
  let PC : FGInvPred mOut mMid := fun x ↦ (P0A x ∧ P0B x) ∧ P1 x ∧ P2 x ∧ P3 x ∧ P4 x
  have hClC : WalkSubspaceClosed wOuter wInner2 uB PC := walkSubspaceClosed_inter hCl0
    (walkSubspaceClosed_inter hCl1 (walkSubspaceClosed_inter hCl2
      (walkSubspaceClosed_inter hCl3 hCl4)))
  have hR₁_sq : R₁ * R₁ = 1 := QubitisedWalk.reflInUnitary_mul_self _
  have hR₂_sq : R₂ * R₂ = 1 := QubitisedWalk.reflPulledUnitary_mul_self _ _
  obtain ⟨hFoldStd, hFoldTop⟩ := ts_qpeAffinePerm_fold ts
  have hTest0 {b m : ℕ} (hm : m < 2 ^ b) (he : m % 2 ≠ 1) :
      (⟨m, hm⟩ : Fin (2 ^ b)).val.testBit 0 = false := by
    change m.testBit 0 = false
    exact Nat.mod_two_eq_zero_iff_testBit_zero.mp (by omega)
  have hCoarse : CoarseGearInvRel wOuter wInner2 nStd kTail uB (topG0Fiber u0A u0B R₁c)
      FG1 FG2 FG3 FG4 (δ0A + δ0B + δG1 + δG2 + δG3 + δG4) := by
    refine ⟨PC, hClC, fun xc hxc ↦ ?_⟩
    let x5 := (QRegister.block 1 5 (by decide) : QRegister 5 6).extractIndex xc
    let x4 := (QRegister.block 2 4 (by decide) : QRegister 4 6).extractIndex xc
    let x3 := (QRegister.block 3 3 (by decide) : QRegister 3 6).extractIndex xc
    let x2 := (QRegister.block 4 2 (by decide) : QRegister 2 6).extractIndex xc
    have hr0_raw := invCatRelTopG0Fiber (invCatRel_reflInUnitary mOut mMid hCl0.2.1)
      ⟨walkSubspaceClosed_refl_pow hCl0 (peelK 4), fun v hv ↦ hErr0A v hv.1⟩
      ⟨walkSubspaceClosed_refl_pow hCl0 (peelTail nStd kTail 4), fun v hv ↦ hErr0B v hv.2⟩ x2
    have hx2_le : x2.val ≤ 2 := by
      rw [qpeBlockHi_extract_val 6 2 4 (by decide) rfl xc]
      omega
    have hId0 := topG0_eq_tailTarget hR₁_sq hR₂_sq (peelK 4) (peelTail nStd kTail 4) x2 hx2_le
    dsimp only at hId0
    have hr0 : InvCatRel PC cat₀ (topG0Fiber u0A u0B R₁c x2) _ (δ0A + δ0B) :=
      invCatRel_restrict_closed (fun v hv ↦ hv.1)
        (fun v hv ↦ hId0 ▸ walkSubspaceClosed_zpow hClC _ v hv) hr0_raw
    have liftP {b : ℕ} {Pi : FGInvPred mOut mMid} {FGi : Fin (2 ^ b) → FGWalkCatU wOuter wInner2}
        {g : ℕ} {htop : peelTop nStd g < 2 ^ b} {δi : ℝ} (x : Fin (2 ^ b))
        (hSub : ∀ v, PC v → Pi v)
        (hri : InvCatRel Pi cat₀ (FGi x) (peelGearFiber (peelTop nStd g) htop
          (R₁ * W ^ peelStepA nStd kTail g) (R₁ * W ^ peelStepB nStd kTail g) R₁ x) δi) :
        InvCatRel PC cat₀ (FGi x) (peelGearFiber (peelTop nStd g) htop
          (R₁ * W ^ peelStepA nStd kTail g) (R₁ * W ^ peelStepB nStd kTail g) R₁ x) δi := by
      refine invCatRel_restrict_closed hSub (fun v hv ↦ ?_) hri
      dsimp only [peelGearFiber]
      by_cases ho : peelTop nStd g % 2 = 1
      · rw [ite_eq_left ho, patFlipTwoStep_ideal_eq_zpow hR₁_sq hR₂_sq _ _ _
          (hTest0 (by omega) (by omega))]
        exact walkSubspaceClosed_zpow hClC _ v hv
      · rw [ite_eq_right ho, singleSigned_ideal_eq_zpow hR₁_sq hR₂_sq _ _ (hTest0 htop ho)]
        exact walkSubspaceClosed_zpow hClC _ v hv
    have hr1 := liftP x3 (fun v hv ↦ hv.2.1) (hRel1 x3)
    have hr2 := liftP x4 (fun v hv ↦ hv.2.2.1) (hRel2 x4)
    have hr3 := liftP x5 (fun v hv ↦ hv.2.2.2.1) (hRel3 x5)
    have hr4 := liftP xc (fun v hv ↦ hv.2.2.2.2) (hRel4 xc)
    have hComb := invCatRel_mul hr4 (invCatRel_mul hr3 (invCatRel_mul hr2 (invCatRel_mul hr1 hr0)))
    have hIdealEq := symbolicSevenGear_ideal_coarse_mul_eq hR₁_sq hR₂_sq ts.hnStd_lo hnHi
      ts.hkTail_lt hFoldStd hFoldTop xc hxc
    dsimp only at hIdealEq
    simp only [mul_assoc] at hIdealEq
    dsimp only [genCoarseFiber]
    rw [← hIdealEq]
    exact ⟨hComb.1, fun v hv ↦ (hComb.2 v hv).trans_eq (by ring)⟩
  exact gen_realizesEst_of_iqft_pertTransfer wOuter wInner2 ko km sRem
    sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM hkOut hkMid hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM
    d wc10 w10 hw10_circ hw10_c ts v cIqft hIqftToff hδIqft0 hCi hwUb hIqftEx estimate
    rSys rAnc hdisj hLoc0 hLoc1 hLoc2 hLoc3 hLoc4 hcM hcF
    (by linarith) hM0 hF0 hCoarse hiM hiF (by linarith) hbM hbF hBudLe hPertTransfer

theorem realizesEst_p450SymbolicSevenGear_of_box {Var : Type} [Fintype Var] [DecidableEq Var]
    {n M nStd kTail tShift : ℕ} [NeZero (2 ^ n)]
    (wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM : ℕ)
    (hkOut : ko ≤ wOuter) (hkMid : km ≤ wInner2) (hnHi : nStd ≤ 46)
    (hsUbG0 : sUbG0 ≤ sRem + 14) (hsUbG1 : sUbG1 ≤ sRem + (13 - 0))
    (hsUbG2 : sUbG2 ≤ sRem + (12 - 0)) (hsUbG3 : sUbG3 ≤ sRem + (11 - 0))
    (hsUbG4 : sUbG4 ≤ sRem + (10 - 0)) (hsUbM : sUbM ≤ sRem + (7 - 0))
    (d : TwoGearRegimeData) (wc10 : ThreeGearWindowCirc 10 7 0)
    (w10 : ThreeGearBondDeferSpec M 10 7 0) (hw10_circ : w10.toCirc = wc10)
    (hw10_c : w10.cWinC = cWinPrefixAt d 10)
    (ts : TailShiftParams M 10 7 nStd kTail tShift) (v : Var) (cIqft : Circuit 16)
    (hIqftToff : cIqft.count .TOFF = 0)
    {δIqft ci wUb d0AUb d0BUb d1AUb d1BUb d2AUb d2BUb d3AUb d3BUb d4AUb d4BUb
      dStdUb dTailUb dMUb dFUb δH eRef eUb gUb effUb kp : ℝ}
    (hδIqft0 : 0 ≤ δIqft) (hCi : 858 / 10 ^ 11 + δIqft ≤ ci) (hwUb : w10.base.δWin ≤ wUb)
    (heRef : eRef ≤ eUb)
    (hIqftEx : ∃ (ζ : ℂ) (hζ : ‖ζ‖ = 1), ‖cIqft.eval.1 - (phasedIqftUnitary 16 ζ hζ).1‖ ≤ δIqft)
    (estimate : Fin (2 ^ combAncillasB wOuter wInner2 ko km sRem) → ℝ)
    (rSys : FGSysReg n) (rAnc : FGAncReg wOuter wInner2 ko km sRem n)
    (hdisj : rSys.DisjointWires rAnc)
    {uB : Unitary (2 ^ nUB wOuter wInner2)} {p0A p0B : FGCircAt Var 2 wOuter wInner2 ko km sUbG0}
    {p1A p1B : FGCircAt Var 3 wOuter wInner2 ko km sUbG1}
    {p2A p2B : FGCircAt Var 4 wOuter wInner2 ko km sUbG2}
    {p3A p3B : FGCircAt Var 5 wOuter wInner2 ko km sUbG3}
    {p4A p4B : FGCircAt Var 6 wOuter wInner2 ko km sUbG4}
    {pSuperM : FGCircAt Var 3 wOuter wInner2 ko km sUbM}
    {pRefl2F : FGCircB Var wOuter wInner2 ko km sRem}
    (hWalk : SymbolicSevenGearCert wOuter wInner2 ko km nStd kTail sRem sUbG0 sUbG1 sUbG2 sUbG3
      sUbG4
      sUbM hkOut hkMid v uB p0A p0B p1A p1B p2A p2B p3A p3B p4A p4B pSuperM pRefl2F
      d0AUb d0BUb d1AUb d1BUb d2AUb d2BUb d3AUb d3BUb d4AUb d4BUb dMUb dFUb)
    (hCoarseUb : d0AUb + d0BUb + d1AUb + d1BUb + d2AUb + d2BUb + d3AUb + d3BUb + d4AUb + d4BUb ≤
      (nStd : ℝ) * dStdUb + dTailUb)
    (hbox : TailShiftRayQuantSuperBox M nStd 10 7 ci wUb dStdUb dTailUb dMUb dFUb δH eUb gUb
      effUb kp)
    (hEstTransfer : TailShiftEstTransferHyp wOuter wInner2 ko km M sRem uB w10.base.uIdeal δH eRef
      gUb kp
      estimate) :
    RealizesP450GroundQPEFG rSys rAnc hdisj estimate
      (p450SymbolicSevenGearProg wOuter wInner2 ko km sRem sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM
        hkOut hkMid hnHi hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM d wc10 ts v cIqft
        p0A p0B p1A p1B p2A p2B p3A p3B p4A p4B pSuperM pRefl2F rSys rAnc) :=
  realizesEst_p450SymbolicSevenGear_of_pertTransfer wOuter wInner2 ko km sRem
    sUbG0 sUbG1 sUbG2 sUbG3 sUbG4 sUbM hkOut hkMid hnHi hsUbG0 hsUbG1 hsUbG2 hsUbG3 hsUbG4 hsUbM
    d wc10 w10 hw10_circ hw10_c ts v cIqft hIqftToff hδIqft0 hCi hwUb hIqftEx estimate rSys rAnc
    hdisj hWalk le_rfl (symbolicPertTransfer_of_box heRef hCoarseUb hbox hEstTransfer)

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.SevenGearBondDefer

end
