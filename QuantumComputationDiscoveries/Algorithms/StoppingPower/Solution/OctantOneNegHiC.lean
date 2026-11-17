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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.OctantOneNegHiB
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.OctantOneNegHiA

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspSlot3OctantOneNegHiB

section
namespace GqspSlot3OctantOneNegHiB
set_option maxRecDepth 4096
open Slot3Norm1s36LatticeBase (n1sShiftIdx n1sNatSumFast)
open GqspSlot3OctantOneNegBaseAndLo
  (oneNegShellFast n1sNatSumFast_add_split)
open GqspSlot3OctantOneNegHiA (oneNeg_hi_64_92)
open Gqsp2_Slot3OctantOneNegHiB (oneNeg_hi_93_111)
set_option maxHeartbeats 400000 in
-- Kernel evaluation of shells 112..117 octant lattice sum.
theorem oneNeg_hi_112_117 :
    Nat.beq (n1sNatSumFast 6 (n1sShiftIdx 112 oneNegShellFast)) 49110929424 = true := by
  decide +kernel
set_option maxHeartbeats 400000 in
-- Kernel evaluation of shells 118..122 octant lattice sum.
theorem oneNeg_hi_118_122 :
    Nat.beq (n1sNatSumFast 5 (n1sShiftIdx 118 oneNegShellFast)) 45286414242 = true := by
  decide +kernel
set_option maxHeartbeats 400000 in
-- Kernel evaluation of shells 123..127 octant lattice sum.
theorem oneNeg_hi_123_127 :
    Nat.beq (n1sNatSumFast 5 (n1sShiftIdx 123 oneNegShellFast)) 49588162752 = true := by
  decide +kernel
private theorem nat_beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a
private theorem chunkHi_eq_of_parts (g : ℕ → ℕ) {vA vB v0 v1 v2 tot : ℕ}
    (hA : Nat.beq (n1sNatSumFast 29 (n1sShiftIdx 64 g)) vA = true)
    (hB : Nat.beq (n1sNatSumFast 19 (n1sShiftIdx 93 g)) vB = true)
    (h0 : Nat.beq (n1sNatSumFast 6 (n1sShiftIdx 112 g)) v0 = true)
    (h1 : Nat.beq (n1sNatSumFast 5 (n1sShiftIdx 118 g)) v1 = true)
    (h2 : Nat.beq (n1sNatSumFast 5 (n1sShiftIdx 123 g)) v2 = true)
    (htot : (vA + vB) + ((v0 + v1) + v2) = tot) :
    Nat.beq (n1sNatSumFast 64 (n1sShiftIdx 64 g)) tot = true := by
  refine nat_beq_of_eq ?_
  have eA := Nat.eq_of_beq_eq_true hA
  have eB := Nat.eq_of_beq_eq_true hB
  have e0 := Nat.eq_of_beq_eq_true h0
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  have c11 : n1sNatSumFast 11 (n1sShiftIdx 112 g) = v0 + v1 := by
    rw [n1sNatSumFast_add_split 112 6 5 g, e0, e1]
  have c16 : n1sNatSumFast 16 (n1sShiftIdx 112 g) = (v0 + v1) + v2 := by
    rw [n1sNatSumFast_add_split 112 11 5 g, c11, e2]
  have s48 : n1sNatSumFast 48 (n1sShiftIdx 64 g) = vA + vB := by
    rw [n1sNatSumFast_add_split 64 29 19 g, eA, eB]
  rw [n1sNatSumFast_add_split 64 48 16 g, s48, c16, htot]
theorem oneNeg_chunk_hi : Nat.beq (n1sNatSumFast 64 (n1sShiftIdx 64 oneNegShellFast))
    383383489704 = true := chunkHi_eq_of_parts oneNegShellFast oneNeg_hi_64_92
    oneNeg_hi_93_111 oneNeg_hi_112_117 oneNeg_hi_118_122 oneNeg_hi_123_127 rfl
end GqspSlot3OctantOneNegHiB
end
end GqspSlot3OctantOneNegHiB

end QuantumComputation.Specs.StoppingPowerSolution
end
