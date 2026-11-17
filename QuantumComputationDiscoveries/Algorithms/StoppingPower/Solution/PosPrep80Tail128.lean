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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.PosPrep80InnerB

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution
open SpecsAux

section PosPostPrep80InnerAmpS3_p3
local instance (priority := 1000000) instNeZeroTwoPow_PosPostPrep80InnerAmpS3_p3 (k : ℕ) :
    NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩

public section
section PosPostPrep80InnerAmpS3

section ModPosPostPrep80InnerAmpS3
public section
namespace PosPostPrep80InnerAmpS3
section ConfigInnerAmp
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2000000
set_option exponentiation.threshold 256
open Operator QProg Matrix Circuit _root_.DynamicCircuit DynCircuitExt Real
open scoped Matrix BigOperators Matrix.Norms.L2Operator Circuit.Notation
open MeasureBranchHadamardSem (ket)
open ZeroAncillaUSPS3 hiding ket
open PosPostPrep80MergedVepS3
section ConfigInnerAmp2b
set_option exponentiation.threshold 32
open scoped ComplexOrder
open ZeroAncillaUSPS3 hiding ket
section Part45
set_option exponentiation.threshold 28
theorem chIf_mulVec_ket_zero (ctrl t : Wire 128) (hct : ctrl ≠ t) (β : BitAssignment 128)
    (hc : β ctrl = 0) : (chIf ctrl t).eval.1.mulVec (ket β) = ket β := by
  rw [chIf, dite_neg' hct]
  exact chCircuit_mulVec_ket_ctrl_zero ctrl t hct β hc
end Part45
end ConfigInnerAmp2b
section SecBranches
open scoped ComplexOrder
open ZeroAncillaUSPS3 hiding ket
theorem flags2Map128_update_pid0 (δ : BitAssignment 128) (b : ZMod 2) :
    flags2Map128 (Function.update δ (rPid_128 ⟨0, by decide⟩) b) =
      Function.update (flags2Map128 δ) (rPid_128 ⟨0, by decide⟩) b := by
  funext w
  by_cases hw : w = rPid_128 ⟨0, by decide⟩
  · subst hw
    dsimp only [flags2Map128]
    rw [Function.update_self,
      Function.update_of_ne (by decide : rPid_128 ⟨0, Nat.zero_lt_succ 2⟩ ≠ wEnAnc_128),
      Function.update_of_ne (by decide : rPid_128 ⟨0, Nat.zero_lt_succ 2⟩ ≠ wEnS0Tail_128),
      Function.update_of_ne (by decide : rPid_128 ⟨0, Nat.zero_lt_succ 2⟩ ≠ wEnTail_128),
      Function.update_of_ne (by decide : rPid_128 ⟨0, Nat.zero_lt_succ 2⟩ ≠ wEnHead_128),
      Function.update_self]
  · rw [Function.update_of_ne hw]
    exact flags2Map128_congr _ _ w rfl rfl rfl rfl
      (fun _ _ _ _ ↦ by rw [Function.update_of_ne hw])
noncomputable def cEndClose_128 (isMerged218 : Bool) : Circuit 128 :=
  cLeafHeadCoordXor ;;ᶜ cFinishXorToff_128 isMerged218 ;;ᶜ cFlags2_128.inverse ;;ᶜ cOpen_128.inverse
noncomputable def cTailClose_128 (isMerged218 : Bool) : Circuit 128 :=
  cJointTailBhmt_128 wJointTailFast19 false ;;ᶜ cLeafHeadCoordXor ;;ᶜ
  cFinishXorToff_128 isMerged218 ;;ᶜ cFlags2_128.inverse ;;ᶜ cOpen_128.inverse
theorem cTailClose_mulVec_ket (isMerged218 s0 : Bool) (t : HeadTuple) :
    let (u2, sm, nuc, b0, anc, bAux, k, pid) := t
    let k64 : Fin (2 ^ 6) := ⟨k.val, Nat.lt_trans k.isLt (by decide)⟩
    let part8 : Fin (2 ^ 8) := if bAux then ⟨1, by decide⟩ else ⟨0, by decide⟩
    let γH := writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (writeReg (βHead128
        s0 u2) rSm_128 (basisBits 3 sm)) rNuc_128 (basisBits 8 nuc)) rB0_128 (basisBits 3 b0))
        rAnc_128 (basisBits 8 anc)) rPart_128 (basisBits 8 part8)) rK_128 (basisBits 6 k64))
        rPid_128 (basisBits 3 pid)
    (cTailClose_128 isMerged218).eval.1.mulVec (ket γH) =
      ket (padZeroBits posPostHwa (ancBits86 s0 (encHead80 isMerged218 s0 t))) :=
  evolve_head_finish_close isMerged218 s0 t
attribute [local irreducible]
  chIf cIsHeadPm_128 cFlags2_128 cOpen_128 cJointTailBhmt_128 cFinishXorToff_128
  cLeafHeadShell64 cLeafHeadCoordXor
attribute [local irreducible] cEndClose_128 cTailClose_128
def fin256SplitEquiv : Fin (2 ^ 8) ≃ Fin (2 ^ 2) × Fin (2 ^ 6) where
  toFun x := (⟨x.val % 4, by omega⟩, ⟨x.val / 4, by omega⟩)
  invFun p := ⟨p.1.val + 4 * p.2.val, by omega⟩
  left_inv x := Fin.ext (by dsimp; omega)
  right_inv p := Prod.ext (Fin.ext (by dsimp; omega)) (Fin.ext (by dsimp; omega))
def pidSplitEquiv : ZMod 2 × Fin (2 ^ 2) ≃ Fin (2 ^ 3) where
  toFun p := ⟨p.1.val + 2 * p.2.val, by have := ZMod.val_lt p.1; omega⟩
  invFun x := (if x.val % 2 == 1 then 1 else 0, ⟨x.val / 2, by omega⟩)
  left_inv p := by
    rcases p with ⟨b, vLo⟩
    fin_cases b <;> fin_cases vLo <;> decide
  right_inv x := by
    fin_cases x <;> decide
end SecBranches
end ConfigInnerAmp
set_option maxRecDepth 2000
set_option exponentiation.threshold 256
set_option backward.isDefEq.respectTransparency true
end PosPostPrep80InnerAmpS3
end
end ModPosPostPrep80InnerAmpS3
end PosPostPrep80InnerAmpS3
end
set_option exponentiation.threshold 256
end PosPostPrep80InnerAmpS3_p3

set_option exponentiation.threshold 256

end QuantumComputation.Specs.StoppingPowerSolution
