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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MomSlot3WrapKern

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section MomSlots01Slot1ProjKinetic_aux
local instance (priority := 1000000) instNeZeroTwoPow_MomSlots01Slot1ProjKinetic_aux (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Slot 1 (`T_p(c)`) Clean-Workspace `DynamicCircuit`, Hadamard Top-Block & Fermionic Norm Bridge

Zero-`.TOFF` clean-workspace `DynamicCircuit Var n` synthesis, QHL verification,
`H^{⊗ mPayload}` top-block collapse, `permElectron` symmetry proof, and fermionic spectral-norm
error bound for **Slot 1 (`T_p(c)`, `coin = 5 = (1, 0, 1)_LSB`)**, unified by `rfl` across:
- `FullSysMomSlots0135Concrete.MomSingleSlotOracle` (`mWork = 230 ≤ 288`, `tSlot = 15016 ≤ 27984`,
  `wSlot = fun _ ↦ lambdaSlot1TpHi`, `eShift = projMidpointOffset`,
  `epsIntr = 1 / 10 ^ 6 ≤ 5 / 10 ^ 6`), and
- `FullSysFullPrepareAndTopConcrete.fullPrep_select_to_both_endpoints` (`wEff B α w 1`
  for all `31 ≤ B`, covering both `B = 31` (`2 ^ 31`) and `B = 33` (`2 ^ 33`) simultaneously):

1. **`rfl`-Exact Symbolic Core Geometry & 3-Bit Coin Projectors (`Section 1`)**:
   - `selWiresSym`, `coreWiresSym`, `selCoin3Sym`, `coreSysSym`, `coreAncSym`, `corePayloadSym`,
     `coreHadamardUnitary`, and `momCoinProj` (`rfl`-identical to both
     `FullSysMomSlots0135Concrete` and `FullSysFullPrepareAndTopConcrete`).
2. **Separable 3-Axis Non-Negative Thresholds & `≤ 2 ^ 42` No-Overflow Theorem (`Section 2`)**:
   - Splits `centeredProjectileKineticOp cfg` across `w ∈ {0, 1, 2}` into `projAxisTerm cfg p w`
     bounded in magnitude by `projAxisBound cfg w > 0` with
     `∑ w : Fin 3, projAxisBound cfg w = projLiteralPrepWeight cfg`.
   - Defines four non-negative integer summands `slot1PadThresh w_eff cfg` and
     `slot1AxisThresh w_eff cfg w u` (`u : Fin 256`) whose sum `slot1TotalThresh w_eff cfg xSys`
     satisfies `slot1TotalThresh w_eff cfg xSys ≤ 2 ^ 42` on **all** `2 ^ systemQubits`
     computational basis states with **zero** rejection branches and **zero** modular wraparound.
3. **Involutive Self-Adjoint Phase Unitary & `8`-Coin `H^{⊗ mPayload}` Collapse (`Section 3`)**:
   - Defines `slot1SelectUnitary hmPay w_eff cfg : Unitary (2 ^ (coreWiresSym mPayload))` with
     `.1 = slot1SelectDiag hmPay w_eff cfg`, proving self-adjointness, involution, `coin ≠ 5`
     identity, `iSlot2 = 0` identity, and `slot1_hadamard_topBlock_all` +
     `slot1_hadamard_topBlock_coin5`.
4. **Unit Norm, `permElectron` Symmetry & `≤ 4 * w_eff / 2 ^ 41` Error Bound (`Section 4`)**:
   - Proves `norm_bUnitTwosSlot1_le_one`, exact zero-error `bUnitTwosSlot1_permElectron`, symbolic
     fermionic error `≤ 4 * w_eff / 2 ^ 41` (`= 7.55 × 10⁻¹⁰` Ha at `lambdaSlot1TpHi`),
     `≤ 1 / 10 ^ 6` Ha, and `wEff_slot1_gt_projLiteralPrepWeight_and_err_le` for all `31 ≤ B`.
5. **Compositional `RevProg`, `8`-Bit Binary-Tree QROM & Clean-Workspace `DynamicCircuit`**:
   - Synthesizes `dSlot1SelectCoreDyn` using `slot1WorkWires = 230` clean workspace qubits
     (`≤ 288`), `count .TOFF = 0`, exact `Configuration`-independent `count .T = 15016`
     (`≤ 27984`), and proves `DynamicCircuit.RealizesEmbeddedUnitaryWithCleanWorkspace`.
-/

public section

namespace MomSlot1GeomPriority288

section ConfigMomSlot1GeomPriority288

set_option maxRecDepth 1024
set_option backward.isDefEq.respectTransparency true
open Operator Matrix QProg Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open SpecsAux.BridgeFermionicComm
open SpecsAux.BridgeFermionicComm.SpecInner
open PosMomSelectDynamic hiding embedMatrix_diagonal
-- Root solution namespace already active.
open scoped Matrix BigOperators Circuit.Notation Matrix.Norms.L2Operator

namespace SsaProg

attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
theorem le_end {M cur endCur : ℕ} (p : SsaProg M cur endCur) : cur ≤ endCur :=
  RawSsa.le_end p.wf

end SsaProg

attribute [local irreducible] basisBits QRegister.extractIndex

end ConfigMomSlot1GeomPriority288

end MomSlot1GeomPriority288

end
end MomSlots01Slot1ProjKinetic_aux

end QuantumComputation.Specs.StoppingPowerSolution
