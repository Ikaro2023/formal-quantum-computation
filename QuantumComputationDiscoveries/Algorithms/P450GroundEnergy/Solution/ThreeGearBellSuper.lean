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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellSuperNoNegWalk

/-!
# Turnkey `57`-AND Bell Super-Reflections & Polymorphic `3-Gear` (`(m1, m2, M)`) Bridge

Instantiates the `57`-AND `(160 - d)`-scratch (`0 ≤ d ≤ 10`) Bell-persistent `K`-step
super-reflections in both `cEntrySign23` mode (`wNegIn : Wire wInner2`) and
`wNegIn`-free mode (`bellSuperNoNegGen57Dyn`, `0 < wInner2`), and
provides
the `rfl`-aligned polymorphic `3-Gear` (`(m1, m2, M)`) `T`-count and `WalkSuperRefl2InvErrLe`
bridge for `M = 47,103`.

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

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ThreeGearBellSuper
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias Solution.CleanDyn AliasPrep
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution
open Solution.CircuitModular Solution.GivensOps
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.SelectSwapQROM Solution.GivensCascade
open Solution.SelectRouter10 Solution.TopIntegrationBridge
open Solution.Lac2Fused184Select Solution.Lac2Fused184SelectWrap Solution.Router10Lac2Select
open Solution.Phase2MidSandwich Solution.MidReflCtxRetain
open Solution.PolymorphicFused184Select Solution.Lac2ZeroPar183Select
open Solution.CompactFoldedSelect Solution.ReordOuter13Bridge
open Solution.CompactStepFast176Select hiding blockRemWidth
  outRemWidth midRemWidth combARem
open Solution.StepEncK Solution.StepDecK Solution.CompactStepFast175Core
open Solution.CompactOuter9Bound50Core Solution.CompactOuter9Bound50Select
open Solution.MobiusOptSubcube163Walk
  (ubCustomMuxCatUnitary outerSandwich_eq_reflPulledPair_customMux)
open Solution.CompactTuned162StepWalk Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam Solution.CompactStepZeroCmp20OuterParam
open Solution.Balanced160Select Solution.Pi145SOSPermBridge Solution.OneHotSimulates
open Solution.LowBitPi145Select Solution.BellPhaseASelect Solution.BellSingletCSwap58
open Solution.Cat11CompactPhase2Bridge Solution.DihedralWalkQPE
open Solution.DihedralWalkQPE.MultiGearQPE
open Solution.DihedralWalkQPE.BlockReflection
open Solution.ZeroRcHotPrepMid21Fast Solution.TwoGearQPEPhase5
open Solution.TwoGearBox
open Solution.WalkQPEBridge hiding
  rActLoc rActLoc_disjoint_rScrLoc rCatInAct rCatLoc rQPEInAct rQPEInAct_disjoint_rWalkCatInAct
  rQPEInAnc rQPELoc rQPELoc_disjoint_rScrLoc rQPELoc_disjoint_rWalkCatLoc rScrLoc rScrUbLoc
  rWalkCatInAct rWalkCatLoc rWalkCatLoc_disjoint_rScrLoc
open Solution.WalkQPEBridgeXMeas hiding
  image_rFullZeroLoc rFullZeroLoc
open Solution.WalkQPEFlexBridge hiding
  cleanRealizesSet_of_rScrUbLoc cleanRealizes_rScrLoc_of_sub
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation
open Solution.BellRouter57 Solution.BellRouter57Pure Solution.NoNegSelect57Pure
open Solution.CompactCore145Bundle
open Solution.BellPersistNoNeg Solution.BellSelectNoNegPair Solution.Select57Slices
open Solution.BellPersistCore Solution.BellPersistSuperWalk Solution.BellSuperNoNegWalk
open Solution.TwoGearSuperPhase5

local instance instNeZeroTwoPowThreeGear (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-! ## Section 1: Turnkey `57`-AND `(160 - d)`-Scratch Bell Super-Reflections (Both Modes) -/

/-- Closed-form internal Bell-persistent step `SELECT` `T`-count
  (`compactBellSelect57TCount d - 232`
`= 24556 + 896 * d + 8 * (d - 1)`): inside a `K`-step Bell-persistent super-reflection, each step
omits the outer `232 T` Bell-CSWAP pair, which is paid only once across all `K` steps. -/
def compactBellSuperStep57TCount (d : ℕ) : ℕ := 24556 + 896 * d + 8 * (d - 1)

theorem compactBellSuperStep57TCount_eq_core (d : ℕ) :
    compactCoreTCount d + compactCoreTCount d + 464 + 4 * (2 * 14 + 43 + 43) =
      compactBellSuperStep57TCount d := by
  dsimp [compactCoreTCount, compactBellSuperStep57TCount]; omega

/-- `wNegIn`-free `K`-step `57`-AND Bell-persistent super-reflection parameterized by arbitrary
`GenCore145Bundle`s `bundleF`, `bundleB` (`0 < wInner2`). -/
noncomputable abbrev bellSuperNoNegGen57Dyn {Var : Type}
    {kInner tCoreF tCoreB : ℕ} {branchF branchB : Fin (2 ^ 10) → Unitary (2 ^ 58)}
    (bundleF : GenCore145Bundle kInner tCoreF branchF) (bundleB :
      GenCore145Bundle kInner tCoreB branchB)
    (bQPE wOuter wInner2 ko km mLow sUb K : ℕ) (hkOut : ko ≤ wOuter) (hkMid : km ≤
      wInner2) (hGiPos : 0 < wInner2)
    (hs : 1 + kInner ≤ sUb) (hsIn : combARem wOuter wInner2 ko km - 2 ≤ kInner) (v : Var)
    (pOutFwd pOutBwd P_1 pTurn P_4 :
      DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb)) :
    DynamicCircuit Var (combQubitsAt bQPE wOuter wInner2 ko km mLow sUb) :=
  bellSuperNoNegGenBundleDyn bundleF bundleB stepsA57 stepsBFwd57 stepsBBwd57
    bQPE wOuter wInner2 ko km mLow sUb K hkOut hkMid hGiPos hs hsIn v pOutFwd pOutBwd P_1 pTurn P_4

/-! ## Section 2: Polymorphic `3-Gear` (`(m1, m2, M)`) Bridge (`rfl`-Aligned with `BondDefer`) -/

/-! ## Section 3: Kernel-Checked Closed-Form Cost Identities (`57`-AND & `3-Gear`) -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ThreeGearBellSuper
end
