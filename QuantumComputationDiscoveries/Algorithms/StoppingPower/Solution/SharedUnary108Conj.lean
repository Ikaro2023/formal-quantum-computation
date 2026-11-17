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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.DisjointWiresSymm

@[expose] public section

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section ModSharedUnary108ZeroTUncompTwist
@[expose] public section
namespace SharedUnary108ZeroTUncompTwist
section ConfigSharedUnary108ZeroTUncompTwist
set_option maxRecDepth 32768
set_option exponentiation.threshold 256
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt HermitianMat Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open SpecsAux.SpecMirror
open SpecsAux.PhaseGradCatalystCore
open DyadicQft64 hiding dyadicTurn phaseGradKet andSymStep andSymStep_stepFwd
open DyadicQft64.PhasePerm
open NuclearTwistAndXor654Concrete (dXor32All654)
open NuclearTwistRealizes (basisBits_symm_apply)
open WindowedSlot2MulKick288 (bankFwd)
open InterWalkRSum42Hoist
local instance (priority := 1000000) instNeZeroTwoPowSharedUnary108 (k : ℕ) : NeZero (2 ^ k) :=
  ⟨(Nat.two_pow_pos k).ne'⟩
open _root_.QuantumComputation.Specs.StoppingPowerSolution (CliffProg)
open MeasureBranchHadamardSem (ket bit_cases eval_seq_mulVec)
theorem cliff_conj_eval_ket {n : ℕ} (c1 : CliffProg n) (cMid : Circuit n)
    (β : BitAssignment n) (z : ℂ)
    (hMid : cMid.eval.1.mulVec (ket (c1.eval β)) = z • ket (c1.eval β)) :
    (c1.toCircuit ;;ᶜ cMid ;;ᶜ c1.inv.toCircuit).eval.1.mulVec (ket β) = z • ket β := by
  rw [eval_seq_mulVec, CliffProg.toCircuit_eval_ket, eval_seq_mulVec, hMid, Matrix.mulVec_smul,
    CliffProg.toCircuit_eval_ket, CliffProg.inv_eval]
set_option allowUnsafeReducibility true in
theorem embedUnitary_phaseDiagUnitary_mulVec_ket {k n : ℕ}
    (rSub : QRegister k n) (φ : BitAssignment k → ZMod 2) (β : BitAssignment n) :
    (rSub.embedUnitary
      (MomSlot0CircuitHalf.phaseDiagUnitary φ)).1.mulVec (ket β) =
      ((-1 : ℂ) ^ (φ (fun q ↦ β (rSub q))).val) • ket β := by
  have hUeq0 : MomSlot0CircuitHalf.phaseDiagUnitary φ =
      diagSignUnitary (fun x : Fin (2 ^ k) ↦ decide (φ (basisBits k x) = 1)) := by
    apply Subtype.ext
    rw [MomSlot0LocalAndMomCombine288.phaseDiagUnitary_val_eq_diag]
    refine congrArg Matrix.diagonal (funext fun x ↦ ?_)
    change ((-1 : ℂ) ^ (φ (basisBits k x)).val) =
      if decide (φ (basisBits k x) = 1) = true then (-1 : ℂ) else 1
    rcases bit_cases (φ (basisBits k x)) with h0 | h1
    · rw [h0]; norm_num
    · rw [h1]; norm_num
  have hSingle : ket β = Pi.single ((basisBitsEquiv n).symm β) (1 : ℂ) := rfl
  rw [hUeq0, hSingle, embedUnitary_diagSignUnitary_mulVec_single, ← hSingle]
  refine congrArg (· • ket β) ?_
  have hb : basisBits k (rSub.extractIndex ((basisBitsEquiv n).symm β)) = fun q ↦ β (rSub q)
      := funext fun q ↦ (QRegister.basisBits_extractIndex rSub ((basisBitsEquiv n).symm β)
      q).trans (basisBits_symm_apply n β (rSub q))
  rw [hb]
  rcases bit_cases (φ (fun q ↦ β (rSub q))) with h0 | h1
  · rw [h0]; norm_num
  · rw [h1]; norm_num
attribute [local irreducible] bankFwd
attribute [local irreducible] dXor32All654
end ConfigSharedUnary108ZeroTUncompTwist
end SharedUnary108ZeroTUncompTwist
end
end ModSharedUnary108ZeroTUncompTwist

end QuantumComputation.Specs.StoppingPowerSolution
