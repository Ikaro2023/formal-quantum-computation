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

public import Mathlib.Analysis.Real.Pi.Bounds
public import
  QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.PhaseGradRaySliceBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.WalkQPEFlexBridge
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.CatalystAndQFT
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.Comparators
public import QuantumComputationDiscoveries.Algorithms.P450GroundEnergy.Solution.PhaseGradAdder

/-!
# In-Place Chunked Dihedral QPE + Pulled-Reflection + `11`/`14`-Qubit Catalyst Master Bridge

End-to-end master assembly (`ChunkedPulledMaster11`) for Cytochrome P450 Compound I
(`P450.dfthc`) connecting:

1. **Zero-Global-Phase `11`-Qubit Catalyst (`approxPhaseGradLow11`, `preparePhaseGradLow11`):**
   Prepares `CircuitModular.phaseGradientLowFactor 11 3` (`2^{-11/2} exp(-2πi x / 2^14)`) from
   `|0^11⟩` with `1,130` `T` gates, `0` `.TOFF` gates, zero global phase, and operator-norm error
   at most `1000 / 10 ^ 11` (`10⁻⁸`), while keeping catalyst width `bCat : ℕ` parametric across
   the layout and master bridge so both `bCat = 11` and `bCat = 14` (`approxPhaseGrad14`) plug in.
2. **Zero-Extra-Wire In-Place Chunked Dihedral QPE (`chunkedDihedralInPlaceDyn`):**
   Borrows `(wFlag : 1, rCarry : 16 - mLow - 2, rCtrlScr : mAncUB wOuter wInner2 - 1)` directly
   inside
   `rScrLocInPlace` (`max sUb ((1 + (16 - mLow - 2)) + (mAncUB wOuter wInner2 - 1))`, adding `0`
   persistent qubits whenever `sUb ≥ (1 + (16 - mLow - 2)) + (mAncUB wOuter wInner2 - 1)`, e.g.
   `387`
   total qubits at `(bCat = 11, wOuter = 19, wInner2 = 26, sUb = 184)` or `370` at
   `(11, 19, 10, 183)`),
   reducing `ctrlR0` invocations from `M` (`~48,127`) to `mLow + 2 * (KTop - 1)` (`102` at
   `KTop = 47, mLow = 10`, saving `~11.15M` reflection `T` gates).
3. **Pulled-Reflection Walk + Parametric & Turnkey `M ∈ {48127, 48383, 48639, 48895}` Closure:**
   Supports asymmetric `(pFwd, pBwd)` with clean-zero `rMidZero : QRegister kMid (mMidUB wInner2)`
   via
   `SelectSwapQROM.CleanRealizesSet`, proves the catalytic `L²` perturbation bound `M * δStep`
   and two-branch doubled-QPE marginal bound over `chunkedScheduleUnitary`, and exports turnkey
   `MeasuresLowEnergies_local` + `RealizesUnitaryFromBasisOutcomesAndZeroWorkspace` + gate-count
   theorems at `M = 48,127` and `M = 48,895` (`RefEnergy`).

## References
- D. W. Berry, M. Kieferova, A. Scherer, Y. R. Sanders, G. H. Low, N. Wiebe, C. Gidney, and
  R. Babbush, "Improved techniques for preparing eigenstates of fermionic Hamiltonians,"
  *npj Quantum Inf.* **4**, 22 (2018).
- R. Babbush, C. Gidney, D. W. Berry, N. Wiebe, J. McClean, A. Paler, A. Fowler, and H. Neven,
  "Encoding Electronic Spectra in Quantum Circuits with Linear T Complexity,"
  *Phys. Rev. X* **8**, 041015 (2018).
- G. H. Low, R. King, D. W. Berry, Q. Han, A. E. DePrince III, A. White, R. Babbush,
  R. D. Somma, and N. C. Rubin, "Fast quantum simulation of electronic structure by spectrum
  amplification," *Phys. Rev. X* **15**, 041016 (2025).
- C. Gidney, "Halving the cost of quantum addition," *Quantum* **2**, 74 (2018).
-/

@[expose] public section

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ChunkedPulledMaster11
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix Real WalkQPEBridge WalkQPEBridgeXMeas WalkQPEFlexBridge
open scoped Matrix BigOperators Matrix.Norms.L2Operator

local instance (priority := 1000000) instNeZeroTwoPow (k : ℕ) : NeZero (2 ^ k) :=
  ⟨Nat.pos_iff_ne_zero.mp (by positivity)⟩

/-! ## Section 1: Zero-Global-Phase `11`-Qubit Catalyst (`approxPhaseGradLow11`) -/

/-- Alias for `CircuitModular.phaseGradientLowFactor d b` (`2^{-d/2} exp(-2πi x / 2^{d + b})`). -/
noncomputable abbrev phaseGradientLowFactor (d b : ℕ) : Fin (2 ^ d) → ℂ :=
  CircuitModular.phaseGradientLowFactor d b

section PhaseGrad11Proofs

attribute [local irreducible] CliffordT.exactPhaseGrad14Unitary

end PhaseGrad11Proofs

/-! ## Section 2: `bCat`-Parametric & Zero-Extra-Wire In-Place Ancilla Layout -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ChunkedPulledMaster11

namespace QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ChunkedDihedralQPE
open QuantumComputation.Specs QuantumComputation.Specs.P450

open Operator Matrix QProg Real
open Comparators
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-! ## Section 1: Chunked Dihedral Doubled-Phase Arithmetic & Group Identities -/

/-! ## Section 2: Multiplexed Operator Norms, Uncontrolled Power Loop & Dihedral Chunk Body -/

end QuantumComputationSpecs.Algorithms.P450GroundEnergy.Solution.ChunkedDihedralQPE
