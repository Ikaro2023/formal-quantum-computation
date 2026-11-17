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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.MobiusStage1Copy

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspSlot3OctantOneNegHiA

section
namespace GqspSlot3OctantOneNegHiA
set_option maxRecDepth 4096
open Slot3Norm1s36LatticeBase (n1sShiftIdx n1sNatSumFast)
open GqspSlot3OctantOneNegBaseAndLo (oneNegShellFast
  n1sNatSumFast_add_split)
theorem oneNeg_hi_64_75 :
    Nat.beq (n1sNatSumFast 12 (n1sShiftIdx 64 oneNegShellFast)) 39503432826 = true := by
      decide +kernel
theorem oneNeg_hi_76_84 :
    Nat.beq (n1sNatSumFast 9 (n1sShiftIdx 76 oneNegShellFast)) 37207268412 = true := by
      decide +kernel
theorem oneNeg_hi_85_92 :
    Nat.beq (n1sNatSumFast 8 (n1sShiftIdx 85 oneNegShellFast)) 39492999510 = true := by
      decide +kernel
private theorem nat_beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a
private theorem combine_64_92 (g : ℕ → ℕ) {v0 v1 v2 tot : ℕ}
    (h0 : Nat.beq (n1sNatSumFast 12 (n1sShiftIdx 64 g)) v0 = true)
    (h1 : Nat.beq (n1sNatSumFast 9 (n1sShiftIdx 76 g)) v1 = true)
    (h2 : Nat.beq (n1sNatSumFast 8 (n1sShiftIdx 85 g)) v2 = true)
    (htot : (v0 + v1) + v2 = tot) :
    Nat.beq (n1sNatSumFast 29 (n1sShiftIdx 64 g)) tot = true := by
  refine nat_beq_of_eq ?_
  have e0 := Nat.eq_of_beq_eq_true h0
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  have s21 : n1sNatSumFast 21 (n1sShiftIdx 64 g) = v0 + v1 := by
    rw [n1sNatSumFast_add_split 64 12 9 g, e0, e1]
  rw [n1sNatSumFast_add_split 64 21 8 g, s21, e2, htot]
theorem oneNeg_hi_64_92 :
    Nat.beq (n1sNatSumFast 29 (n1sShiftIdx 64 oneNegShellFast)) 116203700748 = true :=
  combine_64_92 oneNegShellFast oneNeg_hi_64_75 oneNeg_hi_76_84 oneNeg_hi_85_92 rfl
end GqspSlot3OctantOneNegHiA
end
end GqspSlot3OctantOneNegHiA

end QuantumComputation.Specs.StoppingPowerSolution
end
