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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE46687
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearA
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearB
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearC
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGearD

@[expose] public section

/-!
# Tail-Shifted Three-Gear Dihedral QPE End-to-End Closure

Top-level umbrella module re-exporting `TailShiftThreeGearA`..`D` and providing master
correctness, computable `TailShiftWindowCirc` / `*SuperCircProg` entrypoints, explicit-estimator
`MeasuresLowEnergiesTS` / `RealizesP450GroundQPETS` closures, and
`Ray1036 + Hi14247` / `Ray1036 + Fast12603` `TailShiftRayQuantSuperBox` theorems.
-/

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Circuit Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open WalkQPEBridgeXMeas hiding image_rFullZeroLoc rFullZeroLoc
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open TopIntegrationBridge Cat11CompactPhase2Bridge
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.BlockReflection
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.ApproxIqft16
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.SineWindowFlexM
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.DihedralWalkQPE.MultiGearQPE (
  outRemWidth outZeroPrefixReg combARem combAncillas combQubits combWalkCatReg
  combWalkReflRegs combWalkReflCovers comb_hbScr16 CleanWalkRefl2 WalkRefl2ErrLe
  P450RefVarBound ReordSosHyp RealizesP450GroundQPE tensorWalkCat_smul_right
  approxPhaseGrad11Ray exactPhaseGrad11RayUnitary norm_phaseGrad11RayScalar
  exactPhaseGrad11RayUnitary_mulVec_zero approxPhaseGrad11Ray_count_toff
  approxPhaseGrad11Ray_count_t norm_approxPhaseGrad11Ray_sub_le)
open TwoGearBox hiding m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
open TailShiftBox TwoGearQPEPhase5
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TwoGearBondDefer
open QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftWindow46847
open scoped Matrix BigOperators Matrix.Norms.L2Operator

/-! ## Section 3C: Super-Reflection Builders & Master End-to-End Closures -/

/-! ## Section 3D: Computable `TailShiftWindowCirc` & Explicit-Estimator Closures -/

/-- Collision-free explicit-estimator energy-measurement predicate (`estimate : Fin (2 ^ m) → ℝ`),
definitionally equal (`rfl`) to `CleanDyn.MeasuresLowEnergiesEst` and to
`MeasuresLowEnergies H η Δ ε decoder W` at `estimate = decoder.energy`. -/
abbrev MeasuresLowEnergiesTS {k m : ℕ} (H : Operator (2 ^ k)) (η : ℕ) (Δ ε : ℝ)
    (estimate : Fin (2 ^ m) → ℝ) (W : Unitary (2 ^ (k + m))) : Prop :=
  let sys : QRegister k (k + m) := .block 0 k (by omega)
  let anc : QRegister m (k + m) := .block k m le_rfl
  let IsEigen (E : ℝ) (ψ : Fin (2 ^ k) → ℂ) :=
    H *ᵥ ψ = (E : ℂ) • ψ ∧ electronSectorProjector k η *ᵥ ψ = ψ ∧ ψ ≠ 0
  ∀ T : ℝ, (∀ E' φ, IsEigen E' φ → T ≤ E' + Δ) →
    ∀ E ψ, IsEigen E ψ → ∑ i, Complex.normSq (ψ i) = 1 →
    let out := W.1 *ᵥ sys.tensorState ψ (Pi.single 0 1)
    ∑ a, anc.basisOutcomeProbability a out * (min (estimate a) T - min E T) ^ 2 ≤ ε ^ 2

/-- Explicit ancilla energy estimator on `combAncillasB wOuter wInner2 ko km sRem` for Tail-Shifted
Three-Gear QPE, definitionally equal (`rfl`) to `p450TwoGearEst`. -/
noncomputable abbrev p450TailShiftEst (wOuter wInner2 ko km sRem : ℕ) :
    Fin (2 ^ combAncillasB wOuter wInner2 ko km sRem) → ℝ :=
  fun a ↦ qpeEstimate dfthcLowerBound 97.3864 16
    (rQPEInAnc 16 11 (mOutUB wOuter) (mMidUB wInner2)).extractIndex
    ((QRegister.block 0 (actAncillas 16 11 (mOutUB wOuter) (mMidUB wInner2)) (by
      dsimp [combAncillasB, combAncillas, cat11TotalAncillas, totalAncillas]
      omega)).extractIndex a)

/-- Collision-free explicit-estimator + clean zero-workspace realization predicate for `P450`,
definitionally equal (`rfl`) to `TwoGearQPEPhase5.RealizesP450GroundQPEEst` and to
`p450GroundEnergy_correctness` at `estimate = p450GroundEnergyDecoder.energy`. -/
noncomputable abbrev RealizesP450GroundQPETS {Var : Type} [Fintype Var] [DecidableEq Var]
    {n m : ℕ} [NeZero (2 ^ n)] (rSys : QRegister systemQubits_local n) (rAnc : QRegister m n)
    (hdisj : rSys.DisjointWires rAnc) (estimate : Fin (2 ^ m) → ℝ)
    (prog : DynamicCircuit Var n) : Prop :=
  ∃ W : Unitary (2 ^ (systemQubits_local + m)),
    MeasuresLowEnergiesTS (thcHamiltonian P450.dfthc) p450Eta p450Delta p450Eps estimate W ∧
    RealizesUnitaryFromBasisOutcomesAndZeroWorkspace rSys Finset.univ rAnc hdisj W prog.compile

/-- Explicit-estimator perturbation-to-measurement transfer hypothesis, discharged in one
term via `CleanDyn.measuresLowEnergiesEst_embed_block`,
`measuresLowEnergiesEst_dfthc_of_p450HBlocked`, and
`capped_perturbed_measuresLowEnergies_box_tg_est`. -/
noncomputable abbrev TailShiftEstTransferHyp (wOuter wInner2 ko km M sRem : ℕ)
    (uB : Unitary (2 ^ nUB wOuter wInner2)) (uWinIdeal : Unitary (2 ^ 16)) (δH eRef gUb kp : ℝ)
    (estimate : Fin (2 ^ combAncillasB wOuter wInner2 ko km sRem) → ℝ) : Prop :=
  ∀ (ζ : ℂ) (hζ : ‖ζ‖ = 1)
    (wBlk : Unitary (2 ^ (2 * 58 + actAncillas 16 11 (mOutUB wOuter) (mMidUB wInner2)))) {δWUb : ℝ},
    0 ≤ δWUb → MultiGearQPE.ValidClampedBox M gUb kp → (eRef + 0.1) - dfthcLowerBound ≤ gUb →
    gUb + δH ≤ 11 → 0 ≤ δH →
    kp * (spectralAmpEffNorm 97.3864 gUb / 2) * (π / ((M : ℝ) + 1)) + δH + gUb * δWUb ≤ 0.001 →
    MultiGearQPE.ImplQPEPertHyp wOuter wInner2 M exactPhaseGrad11RayUnitary uB uWinIdeal
      (phasedIqftUnitary 16 ζ hζ) wBlk δWUb →
    let sys : QRegister (2 * 58) (actWidth 16 11 (mOutUB wOuter) (mMidUB wInner2)) :=
      .block 0 (2 * 58) (sys_le_actWidth (mOutUB wOuter) (mMidUB wInner2))
    MeasuresLowEnergiesTS (thcHamiltonian P450.dfthc) p450Eta p450Delta p450Eps estimate
      ((rActLoc 16 11 (mOutUB wOuter) (mMidUB wInner2) 0
        (combARem wOuter wInner2 ko km) (midRemWidth wInner2 km) sRem).embedUnitary
        (sys.embedUnitary p450FswapUninterleave.eval⁻¹ * wBlk *
          sys.embedUnitary p450FswapUninterleave.eval))

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.TailShiftThreeGear
end
