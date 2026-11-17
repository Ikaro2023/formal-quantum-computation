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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sSumHi3018A
public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sSumHi3018B

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspSlot3T3018Hi

section
namespace GqspSlot3T3018Hi
set_option maxRecDepth 4096
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36LatticeBase (n1sShiftIdx n1sNatSumFast n1sOctShellFast
  n1sChunkHi)
open Gqsp1_Slot3T3018HiA (hiT3018ShellFast hiT3018ShellFast_eq
  n1sNatSumFast_add_split t3018_hi_64_94)
open Gqsp2_Slot3T3018HiB (t3018_hi_95_111)
open Gqsp3_Slot3T3018HiC (t3018_hi_112_120)
set_option maxHeartbeats 400000 in
-- Kernel evaluation of shells 121..123 octant lattice sum.
theorem t3018_hi_121_123 :
    Nat.beq (n1sNatSumFast 3 (n1sShiftIdx 121 hiT3018ShellFast)) 504321228 = true := by
      decide +kernel
set_option maxHeartbeats 400000 in
-- Kernel evaluation of shells 124..125 octant lattice sum.
theorem t3018_hi_124_125 :
    Nat.beq (n1sNatSumFast 2 (n1sShiftIdx 124 hiT3018ShellFast)) 350453558 = true := by
      decide +kernel
set_option maxHeartbeats 400000 in
-- Kernel evaluation of shells 126..127 octant lattice sum.
theorem t3018_hi_126_127 :
    Nat.beq (n1sNatSumFast 2 (n1sShiftIdx 126 hiT3018ShellFast)) 362930640 = true := by
      decide +kernel
private theorem nat_beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a
private theorem chunkHi_eq_of_parts (t : Norm1sTier) (g : ℕ → ℕ)
    {vA vB vC vD0 vD1 vD2 tot : ℕ} (hg : g = n1sOctShellFast t)
    (hA : Nat.beq (n1sNatSumFast 31 (n1sShiftIdx 64 g)) vA = true)
    (hB : Nat.beq (n1sNatSumFast 17 (n1sShiftIdx 95 g)) vB = true)
    (hC : Nat.beq (n1sNatSumFast 9 (n1sShiftIdx 112 g)) vC = true)
    (hD0 : Nat.beq (n1sNatSumFast 3 (n1sShiftIdx 121 g)) vD0 = true)
    (hD1 : Nat.beq (n1sNatSumFast 2 (n1sShiftIdx 124 g)) vD1 = true)
    (hD2 : Nat.beq (n1sNatSumFast 2 (n1sShiftIdx 126 g)) vD2 = true)
    (htot : ((vA + vB) + vC) + ((vD0 + vD1) + vD2) = tot) : Nat.beq (n1sChunkHi t) tot = true
    := by
  refine nat_beq_of_eq ?_
  unfold n1sChunkHi
  rw [← hg]
  have eA := Nat.eq_of_beq_eq_true hA
  have eB := Nat.eq_of_beq_eq_true hB
  have eC := Nat.eq_of_beq_eq_true hC
  have eD0 := Nat.eq_of_beq_eq_true hD0
  have eD1 := Nat.eq_of_beq_eq_true hD1
  have eD2 := Nat.eq_of_beq_eq_true hD2
  have sD5 : n1sNatSumFast 5 (n1sShiftIdx 121 g) = vD0 + vD1 := by
    rw [n1sNatSumFast_add_split 121 3 2 g, eD0, eD1]
  have sD7 : n1sNatSumFast 7 (n1sShiftIdx 121 g) = (vD0 + vD1) + vD2 := by
    rw [n1sNatSumFast_add_split 121 5 2 g, sD5, eD2]
  have s48 : n1sNatSumFast 48 (n1sShiftIdx 64 g) = vA + vB := by
    rw [n1sNatSumFast_add_split 64 31 17 g, eA, eB]
  have s57 : n1sNatSumFast 57 (n1sShiftIdx 64 g) = (vA + vB) + vC := by
    rw [n1sNatSumFast_add_split 64 48 9 g, s48, eC]
  rw [n1sNatSumFast_add_split 64 57 7 g, s57, sD7, htot]
theorem n1s_chunk_t30_18_hi : Nat.beq (n1sChunkHi .t30_18) 6834173852 = true :=
    chunkHi_eq_of_parts .t30_18 hiT3018ShellFast hiT3018ShellFast_eq t3018_hi_64_94
    t3018_hi_95_111 t3018_hi_112_120 t3018_hi_121_123 t3018_hi_124_125 t3018_hi_126_127 rfl
end GqspSlot3T3018Hi
end
end GqspSlot3T3018Hi

end QuantumComputation.Specs.StoppingPowerSolution
end
