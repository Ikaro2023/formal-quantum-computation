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

public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.MobiusSubcubeWalk

/-!
# Zero-`wCmp` `wInner2 = 20` Walk Register & Wire-Preservation Helpers

Register layout (`mid161Hot128InCtx`), composition disjointness (`compose_disjoint_zc20`),
reflection wire-preservation (`preservesWires_embed_reflMid_zc20`), and Clifford+T `T`-count
helper (`wordCountTMag8To23Word_zc20`) for the `wInner2 = 20` inner walk core.

## References
- R. Babbush *et al.*, *Phys. Rev. X* **8**, 041015 (2018), DOI: 10.1103/PhysRevX.8.041015.
- C. Gidney, *Quantum* **2**, 74 (2018), DOI: 10.22331/q-2018-06-18-74.
- J. Lee *et al.*, *PRX Quantum* **2**, 030305 (2021), DOI: 10.1103/PRXQuantum.2.030305.
- G. H. Low, V. Kliuchnikov, and L. Schaeffer, *Quantum* **8**, 1375 (2024), arXiv:1812.00954.
-/

set_option exponentiation.threshold 512

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution
namespace CompactTuned162StepZeroCmp20

open Operator QProg Matrix Circuit HermitianMat Real
open QuantumComputation.Specs QuantumComputation.Specs.P450
open BlockEncodingCore BlockEncodingCircuit FastUniform CoherentAlias AliasPrep
open Phase2MidSandwich CompactBilinearPrep DyadicPacketInnerPrep RankReducedPrepMid
open MidReflCtxRetain OptFactoredMag30AndCoin9 Cat11CompactPhase2Bridge ReordOuter13Bridge
open ZeroRcHotPrepMid21Fast OptXMeasUnload21 Tuned162ScheduledSympQrom21
open Tuned162StepSympAnfQrom21 OptStepSympAnfQrom21 OptU2Grover184PrepOut13
open TopIntegrationBridge MobiusOptSubcube163Walk CompactTuned162StepWalk
open scoped Matrix BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator Circuit.Notation

local instance (priority := 1000000) instNeZeroTwoPowZeroCmp20 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩

/-- `128`-wire `rHot128` suffix inside `(7 + 128)`. -/
def mid161Hot128InCtx : QRegister 128 (7 + 128) :=
  QRegister.block 7 128 (by decide)

theorem compose_disjoint_zc20 {M A B N : ℕ} (r : QRegister M N)
    {r1 : QRegister A M} {r2 : QRegister B M} (h : r1.DisjointWires r2) :
    (r.compose r1).DisjointWires (r.compose r2) :=
  QRegister.disjoint_iff.mpr fun i j hij ↦ h.ne i j (r.wires.injective hij)

theorem preservesWires_embed_reflMid_zc20 {N M m : ℕ} (rWalk : QRegister M N)
    (r : QRegister m M) (S : Finset (Wire N)) :
    AliasPrep.PreservesWires (rWalk.embedUnitary (QubitisedWalk.reflMidUnitary r)).1 S := by
  intro i j ⟨_, _, hne⟩
  have hij : i ≠ j := fun h ↦ hne (h ▸ rfl)
  change rWalk.embedMatrix (1 - (2 : ℂ) • r.basisOutcomeProjector 0) i j = 0
  rw [QubitisedWalk.embedMatrix_sub_local, QRegister.embedMatrix_one, QRegister.embedMatrix_smul,
    ← CleanDyn.compose_basisOutcomeProjector,
    SelectSwapQROM.basisOutcomeProjector_zero_eq_zeroProjOn,
    Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, SelectSwapQROM.zeroProjOn,
    Matrix.diagonal_apply]
  simp [hij]

@[simp] theorem wordCountTMag8To23Word_zc20 :
    OuterWeights.GroverUniform.wordCountT FastCleanUnif184.mag8To23Word = 40 := rfl

end CompactTuned162StepZeroCmp20
end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution

end
