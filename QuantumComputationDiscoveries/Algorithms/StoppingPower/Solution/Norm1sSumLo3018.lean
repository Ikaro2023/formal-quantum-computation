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

public import QuantumComputationDiscoveries.Algorithms.StoppingPower.Solution.Norm1sLatLo3018

@[expose] public section
set_option allowUnsafeReducibility true

namespace QuantumComputation.Specs.StoppingPowerSolution

noncomputable section GqspSlot3T3018Lo

section
namespace GqspSlot3T3018Lo
set_option maxRecDepth 4096
open Slot3Norm1s36_161w (Norm1sTier)
open Slot3Norm1s36LatticeBase
  (n1sShiftIdx n1sNatSumFast n1sOctShellFast n1sChunkLo)
open Gqsp1_Slot3T3018LoA
  (loT3018ShellFast loT3018ShellFast_eq n1sShiftIdx_zero n1sNatSumFast_add_split loT3018_0_31)
theorem loT3018_32_47 :
    Nat.beq (n1sNatSumFast 16 (n1sShiftIdx 32 loT3018ShellFast)) 1040367064 = true := by
  decide +kernel
theorem loT3018_48_55 :
    Nat.beq (n1sNatSumFast 8 (n1sShiftIdx 48 loT3018ShellFast)) 895674776 = true := by
  decide +kernel
theorem loT3018_56_63 :
    Nat.beq (n1sNatSumFast 8 (n1sShiftIdx 56 loT3018ShellFast)) 1221893656 = true := by
  decide +kernel
private theorem nat_beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a
private theorem chunkLo_eq_of_parts (t : Norm1sTier) (g : ℕ → ℕ) {v0 v1 v2 v3 tot : ℕ}
    (hg : g = n1sOctShellFast t) (h0 : Nat.beq (n1sNatSumFast 32 g) v0 = true)
    (h1 : Nat.beq (n1sNatSumFast 16 (n1sShiftIdx 32 g)) v1 = true)
    (h2 : Nat.beq (n1sNatSumFast 8 (n1sShiftIdx 48 g)) v2 = true)
    (h3 : Nat.beq (n1sNatSumFast 8 (n1sShiftIdx 56 g)) v3 = true)
    (htot : v0 + (v1 + (v2 + v3)) = tot) : Nat.beq (n1sChunkLo t) tot = true := by
  refine nat_beq_of_eq ?_
  unfold n1sChunkLo
  rw [← hg]
  have e0 := Nat.eq_of_beq_eq_true h0
  have e1 := Nat.eq_of_beq_eq_true h1
  have e2 := Nat.eq_of_beq_eq_true h2
  have e3 := Nat.eq_of_beq_eq_true h3
  have h48 : n1sNatSumFast 16 (n1sShiftIdx 48 g) = v2 + v3 := by
    rw [n1sNatSumFast_add_split 48 8 8 g, e2, e3]
  have h00 : n1sNatSumFast 64 g = n1sNatSumFast 64 (n1sShiftIdx 0 g) :=
    congrArg (n1sNatSumFast 64) (n1sShiftIdx_zero g).symm
  have h32z : n1sNatSumFast 32 (n1sShiftIdx 0 g) = v0 := by
    rw [n1sShiftIdx_zero g, e0]
  rw [h00, n1sNatSumFast_add_split 0 32 32 g, h32z, n1sNatSumFast_add_split 32 16 16 g, e1, h48,
    htot]
theorem n1s_chunk_t30_18_lo : Nat.beq (n1sChunkLo .t30_18) 5890262600 = true :=
  chunkLo_eq_of_parts .t30_18 loT3018ShellFast loT3018ShellFast_eq
    loT3018_0_31 loT3018_32_47 loT3018_48_55 loT3018_56_63 rfl
end GqspSlot3T3018Lo
end
end GqspSlot3T3018Lo

end QuantumComputation.Specs.StoppingPowerSolution
end
