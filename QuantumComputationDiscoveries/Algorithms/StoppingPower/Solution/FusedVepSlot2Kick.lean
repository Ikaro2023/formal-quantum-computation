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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.GidneyRotZipSum
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.K6SweepAndLoad273

@[expose] public section
set_option allowUnsafeReducibility true
set_option exponentiation.threshold 256

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ProjZ512TwistVepTopBundle288
local instance (priority := 1000000) instNeZeroTwoPow_ProjZ512TwistVepTopBundle288 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Single-Pass Merged `Slot 2 + V_ep` Top Bundle & Reference Twist Unitary (`57,840 T`, `0 .TOFF`)

Packages the `288`-ancilla (`mWorkTwist = 256 ≤ mWork`) single-pass merged `Slot 2 + V_ep`
catalyst circuit and reference twist unitary:
1. `vepSlot2TotalPhaseExp`, `uVepSlot2KickCore`, `vepFusedSlot2AxisDelta`, `uVepFusedSlot2KickCat`,
   `dVepFastFusedSlot2Axis288` (`≤ 16,968 T`, `0 .TOFF`), and `dVepFastFusedSlot2Kick288` /
   `dVepFastFusedSlot2KickInv288` (`≤ 50,904 T`, `0 .TOFF`),
2. `uVepTwistRest`, `uVepFusedTwistRestCat`, `uVepFusedTwistRest`, `dVepFastFusedTwistRest288` /
   `dVepFastFusedTwistRestInv288` (`≤ 57,840 T`, `0 .TOFF`), coin-wire `slotBitProj` commutation,
   and `fastVepTwistOutBundle :`
   `HoistedTwistRestOutBundle (mPayload := mPayload) (mPGTwist := 48) mWork`,
3. `uVepTwistRef`, `fastVepTwistOutBundle_fusedOnP01`, `uVepTwistRef_comm_slot2`,
   `uVepTwistRef_comm_slot1`, `uVepTwistRef_host_eq`, and `uVepTwistRef_vep_eq`.
-/

public section

namespace ProjZ512QftAndTwist288

section ConfigProjZ512TwistVepTopBundle288

set_option maxRecDepth 65536

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation

open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm DyadicQft64Engine
open DyadicQft64WalkCircuit hiding wSlot2
open FullSysCatSegmentBridge
open NuclearTwistAndXor654Concrete
  hiding fullSysCoreWires IntertwinesLocalCat
open NuclearTwistRealizes
open FusedPreDiagFromTwist288

/-- `3`-axis catalyst modular-addition unitary for `dVepFastFusedSlot2Kick288`. -/
noncomputable def uVepFusedSlot2KickCat {mPayload : ℕ} (c : Configuration) (hm : 22 ≤ mPayload) :
    Unitary (2 ^ (fullSysCoreWires mPayload + 48)) :=
  catModAddUnitary (fullSysCoreWires mPayload) 48 (vepFusedSlot2AxisDelta c hm 2) *
    (catModAddUnitary (fullSysCoreWires mPayload) 48 (vepFusedSlot2AxisDelta c hm 1) *
      catModAddUnitary (fullSysCoreWires mPayload) 48 (vepFusedSlot2AxisDelta c hm 0))

theorem uVepFusedSlot2KickCat_intertwinesLocal {mPayload : ℕ} (c : Configuration)
    (hm : 22 ≤ mPayload) (U_cat_48 : Unitary (2 ^ 48))
    (hcol0 : U_cat_48.1.mulVec (Pi.single 0 1) = phaseGradKet 48) :
    NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48 (uVepFusedSlot2KickCat c hm)
      (uTildeFullCore (hm6_of_hm22 hm) * uVepSlot2KickCore c hm) := by
  have hone : NuclearTwistAndXor654Concrete.IntertwinesLocalCat U_cat_48
      (1 : Unitary (2 ^ (fullSysCoreWires mPayload + 48)))
      (DyadicQft64.dyadicDiagUnitary (fullSysCoreWires mPayload) 48 (fun _ ↦ 0)) := by
    rw [dyadicDiagUnitary_zero,
      ← QRegister.embedUnitary_one (QRegister.block 0 (fullSysCoreWires mPayload)
        (fcw_block_le mPayload))]
    exact NuclearTwistAndXor654Concrete.IntertwinesLocalCat.of_core_unitary U_cat_48 1
  have hw (w : Fin 3) := catModAdd_intertwinesLocal U_cat_48 hcol0 (vepFusedSlot2AxisDelta c hm w)
  have h3 := ((hone.mul (hw 0)).mul (hw 1)).mul (hw 2)
  have heff : DyadicQft64.dyadicDiagUnitary _ 48
      (fun γ ↦ (vepFusedSlot2AxisDelta c hm 2 γ : ℤ)) * (DyadicQft64.dyadicDiagUnitary _ 48
      (fun γ ↦ (vepFusedSlot2AxisDelta c hm 1 γ : ℤ)) * (DyadicQft64.dyadicDiagUnitary _ 48
      (fun γ ↦ (vepFusedSlot2AxisDelta c hm 0 γ : ℤ)) * DyadicQft64.dyadicDiagUnitary _ 48
      (fun _ ↦ 0))) = uTildeFullCore (hm6_of_hm22 hm) * uVepSlot2KickCore c hm := by
    rw [uTildeFullCore_eq_dyadicDiag48 (hm6_of_hm22 hm), uVepSlot2KickCore]
    simp only [dyadicDiagUnitary_mul]
    apply dyadicDiagUnitary_congr
    intro γ
    unfold vepSlot2TotalPhaseExp vepFusedSlot2AxisDelta
    have hc1 : ∀ w : Fin 3,
        ((1 - (γ (coreCosetB1Block (hm6_of_hm22 hm) w)).val : ℕ) : ℤ) =
          1 - ((γ (coreCosetB1Block (hm6_of_hm22 hm) w)).val : ℤ) := fun w ↦ by
      have hle : (γ (coreCosetB1Block (hm6_of_hm22 hm) w)).val ≤ 1 := zmod2_val_le_one _
      omega
    push_cast
    rw [Fin.sum_univ_three, Fin.sum_univ_three, hc1 0, hc1 1, hc1 2]
    ring
  convert h3 using 1
  · simp only [uVepFusedSlot2KickCat, mul_one]
  · exact heff.symm

attribute [local irreducible] uProjPlus512_3D

end ConfigProjZ512TwistVepTopBundle288

set_option maxRecDepth 4096

end ProjZ512QftAndTwist288
end
end ProjZ512TwistVepTopBundle288

section FusedVepCore288
local instance (priority := 1000000) instNeZeroTwoPow_FusedVepCore288 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

/-!
# Quantum-Safe `CleanUnitaryWp` Engine, `wrapFlag7Gen`, & `176 T` `Slot 4` Coset Kick

Zero-`.TOFF`, zero-ancilla-overhead (`mWorkTwist = 256`) circuit
primitives replacing symmetric `SplitLifetimeKX2Mux.substCircuit` wrappers with quantum-safe
`DiagOn` clean-ancilla conjugation and asymmetric measurement-based `TempAndStep` uncomputation:

1. **Section 1 (`CleanUnitaryWp`, `DiagOn`, `dAndSandwich`, `dPureConj`, `wrapFlag7Gen`)**:
   Compositional weakest-precondition engine over arbitrary unitaries `Unitary (2 ^ n)` with
   computational-basis block-diagonality `DiagOn`, `4`-`T` `dAndSandwich` (`0 T` uncompute), and
   `28`-`T` `wrapFlag7Gen` (`[vepHighNuc hm]`).
2. **Section 2 (`dFastSlot4CosetKick` / `dFastSlot4CosetKickInv`, `176 T`, `0 .TOFF`)**:
   Hoists `coin = 1` (`8 T` total, `0 .TOFF`) once across all `3` axes and merges `+` and `-`
   coset kicks per axis into a single `56 T` step (`4 T` parity-active + `4 T` sign + `24 T`
   6-bit mask + `0 T` controlled ones'-complement `CNOT` fanout + `24 T` `gidneyAddShiftDyn`),
   saving `-1,120 T` one-way (`-2,240 T/step` vs `1,296 T`) and realizing `uSlot4KickCat hm`
   on `rCore.concat rPGTwist` with clean `rWork`.
-/

public section

namespace FusedVepCore288

section ConfigFusedVepCore288

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536

open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation

open SpecsAux.SpecMirror
open SpecsAux.DyadicSubgridToeplitz512AndShift
open DyadicQft64 hiding dyadicTurn phaseGradKet
open DyadicQft64.PhasePerm
open DyadicQft64WalkCircuit hiding wSlot2
open NuclearTwistAndXor654Concrete
  hiding fullSysCoreWires IntertwinesLocalCat
open NuclearTwistRealizes

theorem DiagOn.one {n : ℕ} (S : Finset (Wire n)) :
    DiagOn S (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) := by
  intro i j hij _ _
  rw [Matrix.one_apply] at hij
  split_ifs at hij with h
  · subst h; rfl
  · exact absurd rfl hij

/-! ### `wrapFlag7Gen`: `28`-`T`, `0`-`.TOFF` Quantum+Classical Wrapper
Replacing `cVepHighNucFlagGen` -/

theorem CleanUnitaryWp.circuit {Var : Type} [Fintype Var] [DecidableEq Var]
    {mW n : ℕ} [NeZero (2 ^ n)] (rW : QRegister mW n) (c : Circuit n) :
    CleanUnitaryWp (Var := Var) rW c.eval (.circuit c) :=
  ⟨GridGuard654ReflAux.StoreConst.circuit c, fun M ↦ by
    rw [DynamicCircuit.compile_circuit, wp_circuit_compile_compat]⟩

/-! ## Section 2: `176 T` `Slot 4` Coset Kick (`dFastSlot4CosetKick` / `Inv`) -/

set_option backward.isDefEq.respectTransparency true

end ConfigFusedVepCore288

set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2000

end FusedVepCore288

end
end FusedVepCore288

end QuantumComputation.Specs.StoppingPowerSolution
