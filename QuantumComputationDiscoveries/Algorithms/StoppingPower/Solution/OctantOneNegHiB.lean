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

noncomputable section Gqsp2_Slot3OctantOneNegHiB

section
namespace Gqsp2_Slot3OctantOneNegHiB
set_option maxRecDepth 4096
open Slot3Norm1s36LatticeBase (n1sShiftIdx n1sNatSumFast)
open GqspSlot3OctantOneNegBaseAndLo (oneNegShellFast
    n1sNatSumFast_add_split)
set_option maxHeartbeats 400000 in
-- kernel octant shell sum verification
theorem oneNeg_hi_93_99 :
    Nat.beq (n1sNatSumFast 7 (n1sShiftIdx 93 oneNegShellFast)) 40191196008 = true := by
  decide +kernel
set_option maxHeartbeats 400000 in
-- kernel octant shell sum verification
theorem oneNeg_hi_100_105 :
    Nat.beq (n1sNatSumFast 6 (n1sShiftIdx 100 oneNegShellFast)) 39120915024 = true := by
  decide +kernel
set_option maxHeartbeats 400000 in
-- kernel octant shell sum verification
theorem oneNeg_hi_106_111 :
    Nat.beq (n1sNatSumFast 6 (n1sShiftIdx 106 oneNegShellFast)) 43882171506 = true := by
  decide +kernel
private theorem nat_beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a
private theorem combine_93_111 (g : ℕ → ℕ) {v0 v1 v2 tot : ℕ}
    (h0 : Nat.beq (n1sNatSumFast 7 (n1sShiftIdx 93 g)) v0 = true)
    (h1 : Nat.beq (n1sNatSumFast 6 (n1sShiftIdx 100 g)) v1 = true)
    (h2 : Nat.beq (n1sNatSumFast 6 (n1sShiftIdx 106 g)) v2 = true)
    (htot : (v0 + v1) + v2 = tot) :
    Nat.beq (n1sNatSumFast 19 (n1sShiftIdx 93 g)) tot = true := by
  refine nat_beq_of_eq ?_
  have e0 := Nat.eq_of_beq_eq_true h0
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  have s13 : n1sNatSumFast 13 (n1sShiftIdx 93 g) = v0 + v1 := by
    rw [n1sNatSumFast_add_split 93 7 6 g, e0, e1]
  rw [n1sNatSumFast_add_split 93 13 6 g, s13, e2, htot]
theorem oneNeg_hi_93_111 :
    Nat.beq (n1sNatSumFast 19 (n1sShiftIdx 93 oneNegShellFast)) 123194282538 = true :=
  combine_93_111 oneNegShellFast oneNeg_hi_93_99 oneNeg_hi_100_105 oneNeg_hi_106_111 rfl
end Gqsp2_Slot3OctantOneNegHiB
end
end Gqsp2_Slot3OctantOneNegHiB

end QuantumComputation.Specs.StoppingPowerSolution
end
