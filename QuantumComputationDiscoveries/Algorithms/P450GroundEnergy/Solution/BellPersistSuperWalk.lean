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
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.BellPersistCore

/-!
# Bell-Persistent `K`-Step Super-Reflection & Turnkey Two-Gear Walk Reflections

Persists the 58-pair Bell-singlet basis (`bellIso58Unitary`) across all `K - 1` internal walk
boundaries of an uncontrolled `K`-step `StageA` super-reflection
`uRefl2A * (R₀ * uRefl2A) ^ (K - 1)`, using one `dBellExit58Dyn` (`232 T`) and one zero-`T`
`dBellEntry58Dyn` (`0 T`) at each inter-step `R₀` boundary.

Polymorphic in `(bundleF, bundleB : Core145Bundle ...)`, router programs
`(stepsA, stepsBF, stepsBB)`,
inner `PREPARE` / turnaround / unload dynamic circuits `(P_1, pTurn, P_4)`, outer `PREPARE`
circuits `(pOutFwd, pOutBwd)`, QPE width `bQPE`, super-step length `K`, and register widths
`(wOuter, wInner2, ko, km, mLow, sUb)`.

## References
- C. Jones, "Low-overhead constructions for the fault-tolerant Toffoli gate," *Phys. Rev. A*
  **87**, 022328 (2013), DOI: `10.1103/PhysRevA.87.022328`.
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
- G. H. Low, R. King, D. W. Berry, Q. Han, A. E. DePrince III, A. White, R. Babbush, R. D. Somma,
  and N. C. Rubin, "Fast quantum simulation of electronic structure by spectrum amplification,"
  *Phys. Rev. X* **15**, 041016 (2025), DOI: `10.1103/PhysRevX.15.041016`.
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellPersistSuperWalk
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator QProg Matrix HermitianMat Real CoherentAlias Solution.CleanDyn AliasPrep
open QuantumComputation.Specs Solution QuantumComputation.Specs.P450 Solution.CircuitModular
open Solution.BlockEncodingCore Solution.BlockEncodingCircuit
open Solution.LowBitPi145Select Solution.BellPhaseASelect Solution.BellSingletCSwap58
open Solution.Lac2Fused184Select
open Solution.CompactStepFast176Select hiding
  combARem midRemWidth
open Solution.CompactOuter9Bound50Core Solution.PolymorphicFused184Select
open Solution.Phase2MidSandwich Solution.MidReflCtxRetain Solution.TopIntegrationBridge
open Solution.MobiusOptSubcube163Walk
  (ubCustomMuxCatUnitary outerSandwich_eq_reflPulledPair_customMux)
open Solution.CompactTuned162StepWalk Solution.CompactTuned162StepZeroCmp20
open Solution.CompactZeroCmp20OuterParam Solution.SelectSwapQROM Solution.Cat11CompactPhase2Bridge
open Solution.ReordOuter13Bridge Solution.DihedralWalkQPE Solution.DihedralWalkQPE.MultiGearQPE
open Solution.DihedralWalkQPE.BlockReflection
open Solution.TwoGearQPEPhase5 Solution.TwoGearBox
open Solution.BellPersistCore
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance instNeZeroTwoPowBellSuper (k : ℕ) : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

theorem preservesVInv_seq {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    {v : Var} {P Q : DynamicCircuit Var N} (hP : PreservesVInv v P) (hQ : PreservesVInv v Q) :
    PreservesVInv v (.seq P Q) :=
  fun Θ hΘ ↦ hP _ (hQ Θ hΘ)

theorem preservesWires_congr_set {n : ℕ} {A : Operator (2 ^ n)} {S₁ S₂ : Finset (Wire n)}
    (h : S₁ = S₂) (hP : AliasPrep.PreservesWires A S₁) : AliasPrep.PreservesWires A S₂ :=
  h ▸ hP

theorem cleanRealizesSet_congr_set {Var : Type} [Fintype Var] [DecidableEq Var] {N : ℕ}
    [NeZero (2 ^ N)] {v : Var} {S₁ S₂ : Finset (Wire N)} {U : Unitary (2 ^ N)}
    {P : DynamicCircuit Var N} (h : S₁ = S₂) (hC : CleanRealizesSet v S₁ U P) :
    CleanRealizesSet v S₂ U P :=
  h ▸ hC

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.BellPersistSuperWalk
end
