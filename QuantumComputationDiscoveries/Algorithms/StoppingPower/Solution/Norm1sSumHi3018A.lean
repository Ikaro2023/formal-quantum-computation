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

noncomputable section Gqsp2_Slot3T3018HiB

section
namespace Gqsp2_Slot3T3018HiB
set_option maxRecDepth 4096
open Slot3Norm1s36LatticeBase (n1sShiftIdx n1sNatSumFast)
open Gqsp1_Slot3T3018HiA (hiT3018ShellFast n1sNatSumFast_add_split)
theorem t3018_hi_95_99 :
    Nat.beq (n1sNatSumFast 5 (n1sShiftIdx 95 hiT3018ShellFast)) 525250606 = true := by
  decide +kernel
theorem t3018_hi_100_103 :
    Nat.beq (n1sNatSumFast 4 (n1sShiftIdx 100 hiT3018ShellFast)) 459092356 = true := by
  decide +kernel
theorem t3018_hi_104_107 :
    Nat.beq (n1sNatSumFast 4 (n1sShiftIdx 104 hiT3018ShellFast)) 496306584 = true := by
  decide +kernel
theorem t3018_hi_108_111 :
    Nat.beq (n1sNatSumFast 4 (n1sShiftIdx 108 hiT3018ShellFast)) 533248408 = true := by
  decide +kernel
private theorem nat_beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a
private theorem combine_95_111 (g : ℕ → ℕ) {v0 v1 v2 v3 tot : ℕ}
    (h0 : Nat.beq (n1sNatSumFast 5 (n1sShiftIdx 95 g)) v0 = true)
    (h1 : Nat.beq (n1sNatSumFast 4 (n1sShiftIdx 100 g)) v1 = true)
    (h2 : Nat.beq (n1sNatSumFast 4 (n1sShiftIdx 104 g)) v2 = true)
    (h3 : Nat.beq (n1sNatSumFast 4 (n1sShiftIdx 108 g)) v3 = true)
    (htot : ((v0 + v1) + v2) + v3 = tot) :
    Nat.beq (n1sNatSumFast 17 (n1sShiftIdx 95 g)) tot = true := by
  refine nat_beq_of_eq ?_
  have e0 := Nat.eq_of_beq_eq_true h0
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  have e3 := Nat.eq_of_beq_eq_true h3
  have s9 : n1sNatSumFast 9 (n1sShiftIdx 95 g) = v0 + v1 := by
    rw [n1sNatSumFast_add_split 95 5 4 g, e0, e1]
  have s13 : n1sNatSumFast 13 (n1sShiftIdx 95 g) = (v0 + v1) + v2 := by
    rw [n1sNatSumFast_add_split 95 9 4 g, s9, e2]
  rw [n1sNatSumFast_add_split 95 13 4 g, s13, e3, htot]
theorem t3018_hi_95_111 : Nat.beq (n1sNatSumFast 17 (n1sShiftIdx 95 hiT3018ShellFast))
    2013897954 = true := combine_95_111 hiT3018ShellFast t3018_hi_95_99 t3018_hi_100_103
    t3018_hi_104_107 t3018_hi_108_111 rfl
end Gqsp2_Slot3T3018HiB
end
end Gqsp2_Slot3T3018HiB

end QuantumComputation.Specs.StoppingPowerSolution
end
