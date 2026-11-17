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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.OctantOneNegLoA

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section Gqsp2_Slot3OctantOneNegLo

section
namespace Gqsp2_Slot3OctantOneNegLo
set_option maxRecDepth 4096
open Slot3Norm1s36LatticeBase (n1sShiftIdx n1sNatSumFast)
open GqspSlot3OctantOneNegBaseAndLo (oneNegShellFast
    n1sShiftIdx_zero n1sNatSumFast_add_split)
open Gqsp1_Slot3OctantOneNegLoA (oneNeg_lo_0_47)
set_option maxHeartbeats 400000 in
-- kernel octant shell sum verification
theorem oneNeg_lo_48_63 :
    Nat.beq (n1sNatSumFast 16 (n1sShiftIdx 48 oneNegShellFast)) 38157883014 = true := by
  decide +kernel
private theorem nat_beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a
private theorem chunkLo_eq_of_48_16 (g : ℕ → ℕ) {v0 v1 tot : ℕ}
    (h0 : Nat.beq (n1sNatSumFast 48 g) v0 = true)
    (h1 : Nat.beq (n1sNatSumFast 16 (n1sShiftIdx 48 g)) v1 = true) (htot : v0 + v1 = tot) :
    Nat.beq (n1sNatSumFast 64 g) tot = true := by
  refine nat_beq_of_eq ?_
  have e0 := Nat.eq_of_beq_eq_true h0
  have e1 := Nat.eq_of_beq_eq_true h1
  have h00 : n1sNatSumFast 64 g = n1sNatSumFast 64 (n1sShiftIdx 0 g) :=
    congrArg (n1sNatSumFast 64) (n1sShiftIdx_zero g).symm
  have h48z : n1sNatSumFast 48 (n1sShiftIdx 0 g) = v0 := by
    rw [n1sShiftIdx_zero g, e0]
  rw [h00, n1sNatSumFast_add_split 0 48 16 g, h48z, e1, htot]
theorem oneNeg_chunk_lo : Nat.beq (n1sNatSumFast 64 oneNegShellFast) 82238675022 = true :=
    chunkLo_eq_of_48_16 oneNegShellFast oneNeg_lo_0_47 oneNeg_lo_48_63 rfl
end Gqsp2_Slot3OctantOneNegLo
end
end Gqsp2_Slot3OctantOneNegLo

end QuantumComputation.Specs.StoppingPowerSolution
end
