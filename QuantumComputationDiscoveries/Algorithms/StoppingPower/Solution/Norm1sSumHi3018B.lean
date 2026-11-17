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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatHi3018

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section Gqsp3_Slot3T3018HiC

section
namespace Gqsp3_Slot3T3018HiC
set_option maxRecDepth 4096
open Slot3Norm1s36LatticeBase (n1sShiftIdx n1sNatSumFast)
open Gqsp1_Slot3T3018HiA (hiT3018ShellFast n1sNatSumFast_add_split)
theorem t3018_hi_112_114 :
    Nat.beq (n1sNatSumFast 3 (n1sShiftIdx 112 hiT3018ShellFast)) 427621810 = true := by
      decide +kernel
theorem t3018_hi_115_117 :
    Nat.beq (n1sNatSumFast 3 (n1sShiftIdx 115 hiT3018ShellFast)) 452235506 = true := by
      decide +kernel
theorem t3018_hi_118_120 :
    Nat.beq (n1sNatSumFast 3 (n1sShiftIdx 118 hiT3018ShellFast)) 475946820 = true := by
      decide +kernel
private theorem nat_beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a
private theorem combine_112_120 (g : ℕ → ℕ) {v0 v1 v2 tot : ℕ}
    (h0 : Nat.beq (n1sNatSumFast 3 (n1sShiftIdx 112 g)) v0 = true)
    (h1 : Nat.beq (n1sNatSumFast 3 (n1sShiftIdx 115 g)) v1 = true)
    (h2 : Nat.beq (n1sNatSumFast 3 (n1sShiftIdx 118 g)) v2 = true)
    (htot : (v0 + v1) + v2 = tot) :
    Nat.beq (n1sNatSumFast 9 (n1sShiftIdx 112 g)) tot = true := by
  refine nat_beq_of_eq ?_
  have e0 := Nat.eq_of_beq_eq_true h0
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  have s6 : n1sNatSumFast 6 (n1sShiftIdx 112 g) = v0 + v1 := by
    rw [n1sNatSumFast_add_split 112 3 3 g, e0, e1]
  rw [n1sNatSumFast_add_split 112 6 3 g, s6, e2, htot]
theorem t3018_hi_112_120 : Nat.beq (n1sNatSumFast 9 (n1sShiftIdx 112 hiT3018ShellFast))
    1355804136 = true := combine_112_120 hiT3018ShellFast t3018_hi_112_114 t3018_hi_115_117
    t3018_hi_118_120 rfl
end Gqsp3_Slot3T3018HiC
end
end Gqsp3_Slot3T3018HiC

end QuantumComputation.Specs.StoppingPowerSolution
end
