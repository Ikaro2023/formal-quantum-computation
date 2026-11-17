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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxEval
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiBase
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T0
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T1
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T2
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T3
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T4
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T5
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T6
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T7
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T8
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T9

/-
# Sparse Checkpointed `kMax = 512` Table & Bounds (`RampKickMuxHiCert1024`)

Stitches checkpointed `r in {256, 512}` walks and `RampKickTableValid` (`m = 1024`).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Prepends `g` `false` entries followed by `true` onto `rest`. -/
def rkmPrependGapHi1024 : ℕ → List Bool → List Bool
  | 0, rest => true :: rest
  | g + 1, rest => false :: rkmPrependGapHi1024 g rest
/-- Expands gap counts between `true` entries into a trimmed `List Bool` mask. -/
def rkmGapsToMaskHi1024 : List ℕ → List Bool
  | [] => []
  | g :: gs => rkmPrependGapHi1024 g (rkmGapsToMaskHi1024 gs)
/-- Mask `0` for `(1024, 256)`. -/
def rkmMkHi_m1024_r256_s0 : List Bool := rkmGapsToMaskHi1024 [
  51, 1, 0, 0, 0, 118, 3, 1
  ]
/-- Mask `1` for `(1024, 256)`. -/
def rkmMkHi_m1024_r256_s1 : List Bool := rkmGapsToMaskHi1024 [
  227, 7, 1, 0, 0
  ]
/-- Mask `2` for `(1024, 256)`. -/
def rkmMkHi_m1024_r256_s2 : List Bool := rkmGapsToMaskHi1024 [
  227, 0, 1, 0, 2, 1, 5, 0, 1, 0, 0
  ]
/-- Mask `3` for `(1024, 256)`. -/
def rkmMkHi_m1024_r256_s3 : List Bool := rkmGapsToMaskHi1024 [
  225, 1, 1, 6, 1, 2, 0, 0, 1, 2, 0, 0, 0
  ]
/-- Mask `4` for `(1024, 256)`. -/
def rkmMkHi_m1024_r256_s4 : List Bool := rkmGapsToMaskHi1024 [
  220, 6, 2, 5, 1, 3, 0, 1, 3, 0, 1, 0
  ]
/-- Mask `5` for `(1024, 256)`. -/
def rkmMkHi_m1024_r256_s5 : List Bool := rkmGapsToMaskHi1024 [
  225, 0, 3, 0, 4, 1, 0, 0, 0, 1, 1, 3, 0, 3
  ]
/-- Mask `6` for `(1024, 256)`. -/
def rkmMkHi_m1024_r256_s6 : List Bool := rkmGapsToMaskHi1024 [
  226, 1, 0, 7, 1, 0, 3, 0, 0, 0, 0, 0, 0, 3
  ]
/-- Segment sign-flip masks for `(m = 1024, r = 256)`. -/
def rkmMasksHi_m1024_r256 : List (List Bool) := [
  rkmMkHi_m1024_r256_s0, rkmMkHi_m1024_r256_s1, rkmMkHi_m1024_r256_s2,
  rkmMkHi_m1024_r256_s3, rkmMkHi_m1024_r256_s4, rkmMkHi_m1024_r256_s5,
  rkmMkHi_m1024_r256_s6, []
  ]
/-- Part 0 of `rkmRowHi_m1024_r256`. -/
def rkmRowHi_m1024_r256_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Part 1 of `rkmRowHi_m1024_r256`. -/
def rkmRowHi_m1024_r256_p1 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Part 2 of `rkmRowHi_m1024_r256`. -/
def rkmRowHi_m1024_r256_p2 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 176, 0, 0, 2, 0, 0,
  158, 1, 0, 188, 104, 0, 174, 3906, 137, 11755, 16229, 47385, 1230132, 280182, 714812, 2778652,
  83502306, 50792029, 17655, 799137360, 999061376076
  ]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 256)`. -/
def rkmRowHi_m1024_r256 : List ℕ :=
  rkmRowHi_m1024_r256_p0 ++ (rkmRowHi_m1024_r256_p1 ++ (rkmRowHi_m1024_r256_p2))
/-- Pre-certified segment walks for `(m = 1024, r = 256)`. -/
def rkmWalksHi_m1024_r256 : List RkmSegWalk := [
  ⟨rkmHbHi_m1024_r256_s0_c0, rkmViHi_m1024_r256_s0_c0, rkmVoHi_m1024_r256_s0_c0⟩,
  ⟨rkmHbHi_m1024_r256_s1_c0, rkmViHi_m1024_r256_s1_c0, rkmVoHi_m1024_r256_s1_c0⟩,
  ⟨rkmHbHi_m1024_r256_s2_c0, rkmViHi_m1024_r256_s2_c0, rkmVoHi_m1024_r256_s2_c0⟩,
  ⟨rkmHbHi_m1024_r256_s3_c0, rkmViHi_m1024_r256_s3_c0, rkmVoHi_m1024_r256_s3_c0⟩,
  ⟨rkmHbHi_m1024_r256_s4_c0, rkmViHi_m1024_r256_s4_c0, rkmVoHi_m1024_r256_s4_c0⟩,
  ⟨rkmHbHi_m1024_r256_s5_c0, rkmViHi_m1024_r256_s5_c0, rkmVoHi_m1024_r256_s5_c0⟩,
  ⟨rkmHbHi_m1024_r256_s6_c0, rkmViHi_m1024_r256_s6_c0, rkmVoHi_m1024_r256_s6_c0⟩,
  ⟨rkmHbHi_m1024_r256_s7_c0, rkmViHi_m1024_r256_s7_c0, rkmVoHi_m1024_r256_s7_c0⟩
  ]
/-- Mask `0` for `(1024, 512)`. -/
def rkmMkHi_m1024_r512_s0 : List Bool := rkmGapsToMaskHi1024 [
  150, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 7, 2, 1, 0, 0, 1, 0, 5, 1, 4, 115, 0, 0, 0, 0, 0, 0, 0,
  14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7
  ]
/-- Mask `1` for `(1024, 512)`. -/
def rkmMkHi_m1024_r512_s1 : List Bool := rkmGapsToMaskHi1024 [
  2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 0, 3, 1, 1, 0, 1, 0, 0, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 1, 1,
  0, 0, 1, 2, 1, 4, 0, 1, 0, 1, 0, 1, 3, 2, 1, 2, 1, 1, 1, 2, 0, 1, 1, 4, 2, 1, 8, 2, 0, 3, 2, 0,
  0, 0, 0, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 0, 1, 1, 2, 1, 1, 1, 3, 3, 1, 0, 0, 3, 0, 0, 0, 1, 0, 1,
  0, 5, 1, 9, 0, 8, 2, 5, 0, 7, 1, 5, 6, 2, 5, 0, 0, 2, 1, 5, 0, 0, 0, 1, 0, 0, 0, 0, 2, 2, 0, 2,
  0, 0, 2, 1, 2, 1, 3, 1, 1, 5, 0, 1, 0, 1, 1, 1, 1, 0, 0, 7, 5, 0, 0, 0, 11, 0, 8, 2, 1, 0, 0,
  0, 0, 7, 0, 2, 0, 2, 0, 5, 1, 1, 2, 0, 0, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0,
  0, 1, 2, 0, 0, 1, 3, 0, 2, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 3, 0, 2, 0, 0, 0
  ]
/-- Mask `2` for `(1024, 512)`. -/
def rkmMkHi_m1024_r512_s2 : List Bool := rkmGapsToMaskHi1024 [
  3, 1, 0, 0, 0, 2, 0, 0, 10, 0, 1, 1, 1, 5, 0, 2, 2, 0, 0, 0, 0, 1, 3, 0, 1, 0, 0, 0, 0, 0, 3,
  3, 3, 2, 0, 0, 0, 0, 0, 0, 4, 4, 1, 2, 0, 0, 3, 2, 4, 0, 0, 0, 0, 0, 1, 2, 8, 0, 0, 0, 2, 0, 5,
  4, 0, 0, 0, 3, 0, 0, 4, 0, 6, 0, 0, 4, 0, 1, 2, 0, 6, 4, 1, 1, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 1,
  0, 0, 0, 1, 0, 2, 3, 0, 0, 3, 1, 3, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 6, 0, 1, 7, 0, 3, 6, 3, 1, 3,
  0, 1, 0, 1, 4, 1, 0, 0, 1, 2, 1, 0, 0, 1, 0, 1, 0, 3, 0, 0, 3, 1, 2, 0, 1, 0, 1, 0, 1, 1, 1, 3,
  1, 0, 0, 1, 0, 1, 0, 1, 2, 2, 1, 0, 0, 4, 2, 1, 0, 0, 10, 1, 0, 1, 2, 1, 0, 1, 2, 1, 0, 0, 1,
  4, 0, 2, 1, 1, 2, 3, 3, 0, 1, 3, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 0, 0, 2, 0, 3, 0, 6, 1, 3, 1, 0,
  0, 2, 0, 0, 0, 0
  ]
/-- Mask `3` for `(1024, 512)`. -/
def rkmMkHi_m1024_r512_s3 : List Bool := rkmGapsToMaskHi1024 [
  1, 0, 1, 3, 3, 0, 1, 0, 0, 0, 0, 0, 5, 3, 5, 9, 3, 0, 0, 0, 0, 0, 3, 1, 1, 3, 0, 0, 1, 9, 2, 2,
  0, 1, 8, 2, 1, 0, 0, 1, 3, 3, 1, 0, 7, 0, 1, 2, 4, 0, 0, 5, 1, 0, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 2, 0, 1, 0, 2, 2, 0, 1, 2, 0, 3, 9, 0, 8, 5, 5, 0, 0, 0, 1, 1, 1, 1, 1, 3, 0, 1, 0,
  0, 8, 3, 0, 0, 0, 0, 4, 0, 0, 2, 4, 0, 1, 4, 1, 1, 0, 0, 1, 0, 0, 0, 1, 2, 1, 0, 2, 1, 1, 0, 1,
  10, 2, 0, 0, 0, 0, 10, 0, 0, 0, 3, 1, 2, 3, 0, 7, 2, 0, 3, 1, 0, 0, 0, 0, 0, 6, 2, 0, 3, 1, 1,
  0, 0, 0, 2, 1, 2, 0, 0, 1, 1, 1, 0, 9, 7, 1, 1, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 0, 0, 2, 4, 0, 0,
  0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 2, 1, 1, 0, 0, 0, 5, 2, 0, 0
  ]
/-- Mask `4` for `(1024, 512)`. -/
def rkmMkHi_m1024_r512_s4 : List Bool := rkmGapsToMaskHi1024 [
  1, 0, 2, 0, 0, 12, 1, 0, 10, 3, 0, 0, 0, 0, 0, 4, 0, 3, 0, 5, 4, 0, 0, 0, 0, 4, 0, 13, 2, 1, 1,
  0, 1, 5, 0, 0, 4, 3, 4, 1, 0, 6, 2, 0, 0, 6, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 4, 0, 4, 0,
  2, 10, 0, 3, 2, 0, 9, 2, 1, 1, 0, 4, 0, 0, 2, 1, 2, 2, 7, 2, 3, 0, 0, 0, 0, 3, 4, 4, 4, 2, 2,
  0, 4, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 0, 0, 5, 0, 0, 0, 2, 2, 0, 7, 4, 3, 1,
  1, 2, 0, 0, 6, 0, 1, 0, 3, 1, 0, 3, 1, 2, 3, 1, 3, 1, 0, 1, 0, 0, 0, 4, 5, 0, 0, 0, 0, 0, 3, 6,
  0, 1, 1, 2, 7, 7, 1, 2, 1, 0, 2, 0, 1, 0, 0, 0, 0, 1, 1, 3, 2, 2, 4, 4, 0
  ]
/-- Mask `5` for `(1024, 512)`. -/
def rkmMkHi_m1024_r512_s5 : List Bool := rkmGapsToMaskHi1024 [
  1, 0, 3, 1, 0, 4, 4, 5, 1, 5, 0, 0, 0, 2, 0, 0, 0, 0, 21, 4, 0, 0, 0, 0, 15, 1, 3, 0, 0, 3, 0,
  0, 12, 5, 0, 0, 3, 24, 4, 5, 0, 2, 7, 0, 6, 1, 0, 11, 0, 1, 0, 0, 0, 0, 6, 0, 7, 0, 10, 0, 0,
  0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 12, 2, 2, 0, 0, 3, 1, 0, 1, 0, 1, 0, 5, 2, 2, 2, 5, 0, 0, 0, 0,
  1, 0, 4, 5, 7, 0, 1, 0, 1, 2, 3, 1, 14, 1, 0, 2, 1, 6, 0, 0, 0, 5, 0, 1, 2, 3, 1, 1, 3, 2, 0,
  1, 0, 2, 0, 5, 1, 4, 7, 1, 1, 2, 1, 1, 2, 0, 1, 2, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 3,
  0, 1, 0, 1, 4, 2, 1, 0, 0, 3, 1, 0, 0, 0, 0
  ]
/-- Mask `6` for `(1024, 512)`. -/
def rkmMkHi_m1024_r512_s6 : List Bool := rkmGapsToMaskHi1024 [
  1, 0, 3, 1, 1, 1, 11, 0, 0, 0, 0, 0, 0, 0, 0, 16, 16, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 7,
  0, 14, 5, 0, 16, 0, 0, 0, 4, 14, 13, 0, 5, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 9, 0, 0, 0, 0,
  0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 3, 0, 0, 0, 0, 0, 1, 0, 3, 0, 6, 5, 2, 1, 0,
  0, 0, 1, 0, 4, 3, 0, 0, 1, 1, 0, 0, 0, 0, 7, 1, 0, 0, 0, 5, 0, 2, 2, 0, 0, 10, 8, 0, 0, 0, 0,
  22, 2, 0, 0, 1, 19, 1, 10, 6, 9, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 4, 0, 12, 5, 0, 0, 1, 0,
  0, 1, 0, 7, 2, 1, 4, 2, 2, 7
  ]
/-- Segment sign-flip masks for `(m = 1024, r = 512)`. -/
def rkmMasksHi_m1024_r512 : List (List Bool) := [
  rkmMkHi_m1024_r512_s0, rkmMkHi_m1024_r512_s1, rkmMkHi_m1024_r512_s2,
  rkmMkHi_m1024_r512_s3, rkmMkHi_m1024_r512_s4, rkmMkHi_m1024_r512_s5,
  rkmMkHi_m1024_r512_s6, []
  ]
/-- Part 0 of `rkmRowHi_m1024_r512`. -/
def rkmRowHi_m1024_r512_p0 : List ℕ := [
  0, 0, 0, 0, 0, 8, 49, 0, 37, 36, 11, 19, 14, 36, 0, 2, 340, 592, 542, 65, 11, 169, 1105, 1278,
  1505, 864, 415, 430, 482, 1717, 1018, 368, 744, 200, 68, 0, 187, 1062, 1468, 1170, 1141, 1041,
  1536, 1255, 989, 179, 97, 59, 153, 75, 289, 126, 2, 17, 47, 631, 1400, 1958, 634, 113, 17, 143,
  178, 361, 41, 0, 277, 572, 696, 292, 89, 1, 265, 701, 939, 755, 16, 241, 63, 286, 352, 21, 1,
  73, 506, 221, 8, 47, 35, 45, 557, 158, 135, 452, 260, 75, 0, 25, 21, 320, 1183, 1940, 1483,
  705, 745
  ]
/-- Part 1 of `rkmRowHi_m1024_r512`. -/
def rkmRowHi_m1024_r512_p1 : List ℕ := [
  29, 6, 25, 198, 0, 6, 20, 0, 29, 13, 295, 232, 245, 0, 0, 0, 47, 63, 54, 0, 296, 432, 417,
  1163, 1889, 177, 156, 227, 284, 725, 487, 751, 570, 436, 11, 68, 90, 63, 731, 179, 24, 2, 2, 1,
  12, 552, 262, 66, 198, 120, 313, 409, 965, 1377, 189, 0, 64, 287, 1208, 925, 994, 225, 127, 86,
  206, 1, 100, 3, 58, 128, 0, 2, 117, 190, 384, 86, 61, 3, 1, 12, 6, 8, 234, 43, 12, 216, 1230,
  1062, 637, 1, 120, 696, 1139, 1471, 2170, 1079, 530, 580, 157, 0, 0, 111, 181, 7, 2
  ]
/-- Part 2 of `rkmRowHi_m1024_r512`. -/
def rkmRowHi_m1024_r512_p2 : List ℕ := [
  228, 874, 44, 0, 4, 795, 310, 535, 1326, 793, 399, 260, 5, 212, 112, 886, 1253, 778, 40, 193,
  60, 9, 6, 115, 571, 2293, 107, 1076, 478, 8, 757, 188, 152, 19, 683, 2189, 2391, 1791, 890,
  174, 80, 0, 8176, 4833, 6264, 543, 13, 96, 37, 11, 11, 3, 10, 0, 14, 4, 3, 0, 18, 20, 19, 0, 1,
  0, 7, 0, 33, 31, 3, 0, 0, 19, 9, 59, 38, 38, 0, 0, 7, 0, 19, 32, 6, 31, 44, 17, 0, 23, 49, 74,
  53, 15, 36, 122, 36, 270, 165, 0, 3, 0, 0, 0, 3, 1, 0
  ]
/-- Part 3 of `rkmRowHi_m1024_r512`. -/
def rkmRowHi_m1024_r512_p3 : List ℕ := [
  3, 0, 0, 9, 524, 702, 32, 145, 259, 459, 5, 2, 3, 66, 44, 381, 32, 129, 220, 55, 92, 100, 248,
  353, 518, 415, 174, 596, 20, 1122, 608, 0, 877, 689, 2435, 1445, 32, 193, 375, 1100, 48, 309,
  56, 133, 527, 300, 71, 970, 65, 451, 244, 1099, 1825, 1718, 492, 1244, 2007, 2637, 688, 1800,
  5758, 5515, 3986, 84, 3851, 11483, 7550, 861, 11673, 44, 126, 2, 34, 30, 0, 104, 0, 3, 12, 5,
  3, 0, 0, 0, 1, 2, 6, 0, 23, 0, 30, 0, 66, 71, 316, 152, 66, 4, 26, 118, 70, 8, 0, 432, 445
  ]
/-- Part 4 of `rkmRowHi_m1024_r512`. -/
def rkmRowHi_m1024_r512_p4 : List ℕ := [
  0, 13, 151, 91, 2, 72, 725, 0, 204, 348, 70, 144, 316, 514, 47, 429, 833, 1221, 2844, 311, 308,
  478, 1023, 8071, 179, 24005, 3131, 42079, 22, 0, 0, 69, 0, 32, 107, 106, 37, 80, 19, 23, 303,
  17, 60, 250, 517, 143, 2, 23, 679, 15, 4, 61, 465, 30, 719, 1185, 1783, 65, 33, 33713, 49484,
  52020, 9780, 891, 129, 886, 43, 0, 2, 2897, 344, 6302, 31371, 1307, 18536, 16946, 134134,
  1612781, 1741804, 5088121, 16520857, 161453, 4455981, 47485969, 11123534, 305393, 40985781,
  194265426, 215136414, 680682, 590320951, 998869099984
  ]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 512)`. -/
def rkmRowHi_m1024_r512 : List ℕ :=
  rkmRowHi_m1024_r512_p0 ++ (rkmRowHi_m1024_r512_p1 ++ (rkmRowHi_m1024_r512_p2
  ++ (rkmRowHi_m1024_r512_p3 ++ (rkmRowHi_m1024_r512_p4))))
/-- Pre-certified segment walks for `(m = 1024, r = 512)`. -/
def rkmWalksHi_m1024_r512 : List RkmSegWalk := [
  ⟨rkmHbHi_m1024_r512_s0_c0, rkmViHi_m1024_r512_s0_c0, rkmVoHi_m1024_r512_s0_c2⟩,
  ⟨rkmHbHi_m1024_r512_s1_c0, rkmViHi_m1024_r512_s1_c0, rkmVoHi_m1024_r512_s1_c2⟩,
  ⟨rkmHbHi_m1024_r512_s2_c0, rkmViHi_m1024_r512_s2_c0, rkmVoHi_m1024_r512_s2_c0⟩,
  ⟨rkmHbHi_m1024_r512_s3_c0, rkmViHi_m1024_r512_s3_c0, rkmVoHi_m1024_r512_s3_c0⟩,
  ⟨rkmHbHi_m1024_r512_s4_c0, rkmViHi_m1024_r512_s4_c0, rkmVoHi_m1024_r512_s4_c0⟩,
  ⟨rkmHbHi_m1024_r512_s5_c0, rkmViHi_m1024_r512_s5_c0, rkmVoHi_m1024_r512_s5_c0⟩,
  ⟨rkmHbHi_m1024_r512_s6_c0, rkmViHi_m1024_r512_s6_c0, rkmVoHi_m1024_r512_s6_c0⟩,
  ⟨rkmHbHi_m1024_r512_s7_c0, rkmViHi_m1024_r512_s7_c0, rkmVoHi_m1024_r512_s7_c0⟩
  ]
/-- Part 0 of `rkmVPotHi_m1024`. -/
def rkmVPotHi_m1024_p0 : List ℕ := [
  0, 20084346303087, 21438047432514, 23518310662493, 23787563643073,
  23950189507294, 24060059782687, 24139995860102, 24201319016286, 24250283055852,
  24290624017615, 24324711280527, 24354120079541, 24379938487204, 24402942219855,
  24423699215093, 24442634833627, 24460073958924, 24476269011905, 24491419087356,
  24505678973603, 24519184707120, 24532038314630, 24544326671879, 24556122133231,
  24567485443699, 24578467977526, 24589113478032, 24599485029823, 24609570627816,
  24619415659388, 24629046391967, 24638162770863, 28134398696707, 31578835671199,
  34973709817498, 38321100868013, 41622947060931, 44881058260700, 48097127554596,
  51272741536263, 54409389453490, 57508471369855, 60571305467141, 63599134596546,
  66593132171036, 69554407478056, 72484010480797, 75382936166943, 78252128495956,
  81092483989279, 83904855002173, 86690052711018, 89448849845751, 92181983193524,
  94890155896565, 97574039564546, 100234276219440, 102871480088818, 105486239261779,
  108079117220157, 110650654256296, 113201368787504, 115731758576231, 24896524798686,
  27387681361787, 29859893493579, 32313586921687, 34749171663720, 37167042827087,
  39567581357210, 41951154738142, 44318117649244, 46668812581242, 49003570414689,
  51322710963606, 53626543486823, 55915367169338, 58189471575818, 60449137078179,
  62694635259047, 64926229292724, 67144174305190, 69348717714525, 71540099553040,
  73718552772299, 75884303532139, 78037571474696, 80178569984372, 82307506434631,
  84424582422409, 86529993990909, 88623931841463, 90706581535117, 92778123684540,
  94838734136815, 96888584147645, 98927840547451, 100956665899824, 102975218652761,
  104983653283070, 106982120434333, 108970767048763, 110949736493286, 112919168680155,
  114879200182386, 116829964344274, 118771591387257, 120704208511355, 122627939992413,
  124542907275358, 126449229063662, 128347021405208, 130236397774724, 132117469152961,
  133990344102761, 135855128842170, 137711927314733, 139560841257104, 141401970264088,
  143235411851246, 145061261515163, 146879612791490, 148690557310854, 150494184852742,
  152290583397436, 154079839176090, 155862036719032, 25354990511552
  ]
/-- Part 1 of `rkmVPotHi_m1024`. -/
def rkmVPotHi_m1024_p1 : List ℕ := [
  27123318602103, 28884832300870, 30639609784910, 32387727747832, 34129261438911,
  35864284700879, 37592870006464, 39315088493710, 41031010000138, 42740703095791,
  44444235115205, 46141672188355, 47833079270606, 49518520171719, 51198057583937,
  52871753109195, 54539667285484, 56201859612401, 57858388575913, 59509311672372,
  61154685431797, 62794565440461, 64429006362803, 66058061962688, 67681785124043,
  69300227870890, 70913441386791, 72521476033739, 74124381370499, 75722206170432,
  77314998438810, 78902805429644, 80485673662042, 82063648936110, 83636776348417,
  85205100307031, 86768664546144, 88327512140305, 89881685518264, 91431226476447,
  92976176192069, 94516575235905, 96052463584716, 97583880633359, 99110865206574,
  100633455570468, 102151689443705, 103665604008408, 105175235920783, 106680621321476,
  108181795845667, 109678794632912, 111171652336741, 112660403134016, 114145080734062,
  115625718387572, 117102348895295, 118575004616514, 120043717477321, 121508518978692,
  122969440204369, 124426511828557, 125879764123439, 127329226966512, 128774929847758,
  130216901876639, 131655171788939, 133089767953446, 134520718378477, 135948050718261,
  137371792279175, 138791970025837, 140208610587064, 141621740261701, 143031385024314,
  144437570530761, 145840322123642, 147239664837625, 148635623404661, 150028222259084,
  151417485542598, 152803437109165, 154186100529779, 155565499097146, 156941655830261,
  158314593478889, 159684334527956, 161050901201843, 162414315468593, 163774599044032,
  165131773395804, 166485859747325, 167836879081654, 169184852145288, 170529799451877,
  171871741285868, 173210697706074, 174546688549173, 175879733433134, 177209851760581,
  178537062722088, 179861385299406, 181182838268634, 182501440203323, 183817209477523,
  185130164268769, 186440322561012, 187747702147493, 189052320633560, 190354195439438,
  191653343802939, 192949782782128, 194243529257935, 195534599936718, 196823011352783,
  198108779870853, 199391921688492, 200672452838487, 201950389191186, 203225746456790,
  204498540187610, 205768785780277, 207036498477916, 208301693372280, 209564385405846,
  210824589373874, 212082319926430, 26355915829278
  ]
/-- Part 2 of `rkmVPotHi_m1024`. -/
def rkmVPotHi_m1024_p2 : List ℕ := [
  27608742930212, 28859139714404, 30107120270668, 31352698552219, 32595888378492,
  33836703436930, 35075157284744, 36311263350640, 37545034936519, 38776485219146,
  40005627251791, 41232473965845, 42457038172408, 43679332563847, 44899369715333,
  46117162086350, 47332722022179, 48546061755358, 49757193407120, 50966128988804,
  52172880403245, 53377459446141, 54579877807400, 55780147072462, 56978278723601,
  58174284141208, 59368174605051, 60559961295517, 61749655294833, 62937267588269,
  64122809065319, 65306290520870, 66487722656346, 67667116080837, 68844481312212,
  70019828778211, 71193168817526, 72364511680858, 73533867531965, 74701246448689,
  75866658423971, 77030113366847, 78191621103433, 79351191377892, 80508833853388,
  81664558113025, 82818373660774, 83970289922383, 85120316246276, 86268461904440,
  87414736093295, 88559147934553, 89701706476066, 90842420692662, 91981299486964,
  93118351690204, 94253586063020, 95387011296243, 96518636011676, 97648468762857,
  98776518035813, 99902792249805, 101027299758060, 102150048848494, 103271047744426,
  104390304605279, 105507827527274, 106623624544113, 107737703627651, 108850072688564,
  109960739577002, 111069712083235, 112176997938292, 113282604814590, 114386540326552,
  115488812031220, 116589427428860, 117688393963555, 118785719023794, 119881409943052,
  120975474000359, 122067918420868, 123158750376409, 124247976986039, 125335605316584,
  126421642383174, 127506095149772, 128588970529692, 129670275386117, 130750016532604,
  131828200733586, 132904834704865, 133979925114101, 135053478581294, 136125501679260,
  137196000934098, 138264982825658, 139332453787994, 140398420209819, 141462888434949,
  142525864762744, 143587355448544, 144647366704098, 145705904697987, 146762975556045,
  147818585361769, 148872740156732, 149925445940982, 150976708673445, 152026534272314,
  153074928615440, 154121897540717, 155167446846460, 156211582291778, 157254309596947,
  158295634443774, 159335562475959, 160374099299452, 161411250482803, 162447021557515,
  163481418018383, 164514445323838, 165546108896282, 166576414122420, 167605366353587,
  168632970906073, 169659233061444, 170684158066859
  ]
/-- Part 3 of `rkmVPotHi_m1024`. -/
def rkmVPotHi_m1024_p3 : List ℕ := [
  171707751135382, 172730017446292, 173750962145388, 174770590345291, 175788907125745,
  176805917533909, 177821626584652, 178836039260839, 179849160513617, 180860995262698,
  181871548396637, 182880824773106, 183888829219168, 184895566531548, 185901041476895,
  186905258792050, 187908223184302, 188909939331650, 189910411883053, 190909645458685,
  191907644650182, 192904414020890, 193899958106106, 194894281413321, 195887388422457,
  196879283586103, 197869971329748, 198859456052010, 199847742124865, 200834833893872,
  201820735678397, 202805451771832, 203788986441814, 204771343930441, 205752528454484,
  206732544205600, 207711395350539, 208689086031354, 209665620365601, 210641002446545,
  211615236343358, 212588326101319, 213560275742007, 214531089263499, 215500770640557,
  216469323824822, 217436752745001, 218403061307050, 219368253394362, 220332332867947,
  221295303566613, 222257169307142, 223217933884471, 224177601071862, 225136174621077,
  226093658262550, 227050055705555, 228005370638373, 228959606728461, 229912767622613,
  230864856947124, 231815878307952, 232765835290874, 233714731461647, 234662570366163,
  235609355530604, 236555090461594, 237499778646352, 238443423552841, 239386028629916,
  240327597307472, 241268132996591, 242207639089682, 243146118960629, 244083575964927,
  245020013439827, 245955434704471, 246889843060031, 247823241789845, 248755634159550,
  249687023417216, 250617412793480, 251546805501674, 252475204737956, 253402613681437,
  254329035494310, 255254473321974, 256178930293160, 257102409520052, 258024914098412,
  258946447107699, 259867011611191, 260786610656102, 261705247273701, 262622924479427,
  263539645273006, 264455412638565, 265370229544744, 266284098944811, 267197023776770,
  268109006963474, 269020051412732, 269930160017419, 270839335655583, 271747581190548,
  272654899471025, 273561293331210, 274466765590892, 275371319055554, 276274956516472,
  277177680750819, 278079494521763, 278980400578566, 279880401656681, 280779500477849,
  281677699750196, 282575002168328, 283471410413425, 284366927153334, 285261555042661,
  286155296722866, 287048154822351, 287940131956550, 288831230728021, 289721453726532,
  290610803529150, 291499282700328, 29062664676181
  ]
/-- Bellman `10 ^ 15`-scaled potential table `vPot[0..512]` (`m = 1024`). -/
def rkmVPotHi_m1024 : List ℕ :=
  rkmVPotHi_m1024_p0 ++ (rkmVPotHi_m1024_p1 ++ (rkmVPotHi_m1024_p2 ++ rkmVPotHi_m1024_p3))
/-- Prefix-kick masks for `(m = 1024, r = 64)`. -/
def rkmMasksHi_m1024_r64 : List (List Bool) := [[]]
/-- Part 0 of `rkmRowHi_m1024_r64`. -/
def rkmRowHi_m1024_r64_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Part 1 of `rkmRowHi_m1024_r64`. -/
def rkmRowHi_m1024_r64_p1 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 191, 2772, 277363, 3002978, 433365067,
  2537112682, 997026232428
  ]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 64)`. -/
def rkmRowHi_m1024_r64 : List ℕ := rkmRowHi_m1024_r64_p0 ++ rkmRowHi_m1024_r64_p1
/-- Part 0 of `rkmMkHi_m1024_r128_s0`. -/
def rkmMkHi_m1024_r128_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 1 of `rkmMkHi_m1024_r128_s0`. -/
def rkmMkHi_m1024_r128_s0_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 2 of `rkmMkHi_m1024_r128_s0`. -/
def rkmMkHi_m1024_r128_s0_p2 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, false, false, true, true, true, false, false, true,
  true, true, true, true, true, true
  ]
/-- Mask segment 0 for `(m = 1024, r = 128)`. -/
def rkmMkHi_m1024_r128_s0 : List Bool :=
  rkmMkHi_m1024_r128_s0_p0 ++ (rkmMkHi_m1024_r128_s0_p1 ++ rkmMkHi_m1024_r128_s0_p2)
/-- Part 0 of `rkmMkHi_m1024_r128_s1`. -/
def rkmMkHi_m1024_r128_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 1 of `rkmMkHi_m1024_r128_s1`. -/
def rkmMkHi_m1024_r128_s1_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 2 of `rkmMkHi_m1024_r128_s1`. -/
def rkmMkHi_m1024_r128_s1_p2 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, false, true, true, true, false, false, true, true, true
  ]
/-- Mask segment 1 for `(m = 1024, r = 128)`. -/
def rkmMkHi_m1024_r128_s1 : List Bool :=
  rkmMkHi_m1024_r128_s1_p0 ++ (rkmMkHi_m1024_r128_s1_p1 ++ rkmMkHi_m1024_r128_s1_p2)
/-- Part 0 of `rkmMkHi_m1024_r128_s2`. -/
def rkmMkHi_m1024_r128_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 1 of `rkmMkHi_m1024_r128_s2`. -/
def rkmMkHi_m1024_r128_s2_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 2 of `rkmMkHi_m1024_r128_s2`. -/
def rkmMkHi_m1024_r128_s2_p2 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, true, true, true, false, true, false, true
  ]
/-- Mask segment 2 for `(m = 1024, r = 128)`. -/
def rkmMkHi_m1024_r128_s2 : List Bool :=
  rkmMkHi_m1024_r128_s2_p0 ++ (rkmMkHi_m1024_r128_s2_p1 ++ rkmMkHi_m1024_r128_s2_p2)
/-- Prefix-kick masks for `(m = 1024, r = 128)`. -/
def rkmMasksHi_m1024_r128 : List (List Bool) := [
  rkmMkHi_m1024_r128_s0, rkmMkHi_m1024_r128_s1, rkmMkHi_m1024_r128_s2, []
  ]
/-- Part 0 of `rkmRowHi_m1024_r128`. -/
def rkmRowHi_m1024_r128_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Part 1 of `rkmRowHi_m1024_r128`. -/
def rkmRowHi_m1024_r128_p1 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Part 2 of `rkmRowHi_m1024_r128`. -/
def rkmRowHi_m1024_r128_p2 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 5, 29, 40, 46, 1022, 48, 72074, 6260
  ]
/-- Part 3 of `rkmRowHi_m1024_r128`. -/
def rkmRowHi_m1024_r128_p3 : List ℕ := [
  20432, 108001, 1192601, 196200, 137128089, 2269065, 1201166559, 998657814180
  ]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 128)`. -/
def rkmRowHi_m1024_r128 : List ℕ :=
  rkmRowHi_m1024_r128_p0 ++ (rkmRowHi_m1024_r128_p1 ++ (rkmRowHi_m1024_r128_p2
  ++ rkmRowHi_m1024_r128_p3))

/-- Active anchor chunk `0` (`m = 1024`). -/
def rkmAncPHi_m1024_p0 : List RampKickAnchor := [
  ⟨3, [1], [22430263], [5], rkmMasksHi_m1024_r3, rkmRowHi_m1024_r3⟩,
  ⟨4, [1], [22985270], [5], rkmMasksHi_m1024_r4, rkmRowHi_m1024_r4⟩,
  ⟨5, [1], [23314714], [7], rkmMasksHi_m1024_r5, rkmRowHi_m1024_r5⟩,
  ⟨6, [1, 1], [16172786, 7361113], [6, 3], rkmMasksHi_m1024_r6, rkmRowHi_m1024_r6⟩,
  ⟨7, [1, 1], [15801366, 7889613], [6, 3], rkmMasksHi_m1024_r7, rkmRowHi_m1024_r7⟩,
  ⟨8, [1], [23809654], [11], rkmMasksHi_m1024_r8, rkmRowHi_m1024_r8⟩,
  ⟨9, [1], [23902914], [11], rkmMasksHi_m1024_r9, rkmRowHi_m1024_r9⟩,
  ⟨10, [1], [23978494], [13], rkmMasksHi_m1024_r10, rkmRowHi_m1024_r10⟩,
  ⟨11, [1], [24041276], [13], rkmMasksHi_m1024_r11, rkmRowHi_m1024_r11⟩
  ]
/-- Active anchor chunk `1` (`m = 1024`). -/
def rkmAncPHi_m1024_p1 : List RampKickAnchor := [
  ⟨12, [1, 1, 1, 1, 1, 1, 1, 1],
    [10765766, 10171863, 1252289, 666606, 476146, 345302, 193972, 222558],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r12, rkmRowHi_m1024_r12⟩,
  ⟨13, [1, 1, 1, 1, 1, 1, 1, 1],
    [10751662, 10231863, 1252290, 666606, 476146, 285802, 217972, 258058],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r13, rkmRowHi_m1024_r13⟩,
  ⟨14, [1, 1, 1, 1, 1, 1, 1, 1],
    [10801242, 10510443, 964290, 666606, 476146, 259302, 211572, 290958],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r14, rkmRowHi_m1024_r14⟩,
  ⟨15, [1, 1, 1, 1, 1, 1, 1, 1],
    [10848717, 10495539, 967290, 666606, 476146, 229702, 212772, 319358],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r15, rkmRowHi_m1024_r15⟩,
  ⟨16, [1, 1, 1, 1, 1, 1, 1, 1],
    [10897103, 10481518, 964790, 666606, 476146, 203202, 215172, 343458],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r16, rkmRowHi_m1024_r16⟩,
  ⟨17, [1, 1, 1, 1, 1, 1, 1, 1],
    [10599520, 10387414, 1085290, 966606, 476146, 175202, 222072, 364558],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r17, rkmRowHi_m1024_r17⟩,
  ⟨18, [1, 1, 1, 1, 1, 1, 1, 1],
    [10553396, 10399815, 1085290, 1026606, 488146, 148102, 218772, 382958],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r18, rkmRowHi_m1024_r18⟩,
  ⟨19, [1, 1, 1, 1, 1, 1, 1, 1],
    [10442517, 10294835, 1085290, 966606, 785646, 126702, 225672, 399958],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r19, rkmRowHi_m1024_r19⟩,
  ⟨20, [1, 1, 1, 1, 1, 1, 1, 1],
    [10557928, 11174827, 655970, 687848, 505498, 331736, 214832, 220931],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r20, rkmRowHi_m1024_r20⟩
  ]
/-- Active anchor chunk `2` (`m = 1024`). -/
def rkmAncPHi_m1024_p2 : List RampKickAnchor := [
  ⟨21, [1, 1, 1, 1, 1, 1, 1, 1],
    [10566712, 11186831, 655970, 687848, 493498, 328536, 216632, 234331],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r21, rkmRowHi_m1024_r21⟩,
  ⟨22, [1, 1, 1, 1, 1, 1, 1, 1],
    [10576087, 11196907, 655970, 687848, 481498, 327436, 217832, 246231],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r22, rkmRowHi_m1024_r22⟩,
  ⟨23, [1, 1, 1, 1, 1, 1, 1, 1],
    [10882482, 10776807, 787970, 687848, 469998, 326836, 219132, 257031],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r23, rkmRowHi_m1024_r23⟩,
  ⟨24, [1, 1, 1, 1, 1, 1, 1, 1],
    [10896763, 10774107, 793670, 687848, 457998, 327736, 220336, 266928],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r24, rkmRowHi_m1024_r24⟩,
  ⟨25, [1, 1, 1, 1, 1, 1, 1, 1],
    [10836038, 10790702, 794169, 747847, 446497, 329335, 221136, 276056],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r25, rkmRowHi_m1024_r25⟩,
  ⟨26, [1, 1, 1, 1, 1, 1, 1, 1],
    [10851141, 10730802, 794569, 747847, 481497, 345035, 222136, 284360],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r26, rkmRowHi_m1024_r26⟩,
  ⟨27, [1, 1, 1, 1, 1, 1, 1, 1],
    [10804837, 10717398, 749165, 747847, 595897, 341335, 223736, 292085],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r27, rkmRowHi_m1024_r27⟩,
  ⟨28, [1, 1, 1, 1, 1, 1, 1, 1],
    [10497110, 10390676, 791890, 749411, 700520, 477494, 379723, 499722],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r28, rkmRowHi_m1024_r28⟩,
  ⟨29, [1, 1, 1, 1, 1, 1, 1, 1],
    [10135620, 10211359, 758633, 738928, 727504, 658269, 483431, 786530],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r29, rkmRowHi_m1024_r29⟩
  ]
/-- Active anchor chunk `3` (`m = 1024`). -/
def rkmAncPHi_m1024_p3 : List RampKickAnchor := [
  ⟨30, [1], [24513504], [39], rkmMasksHi_m1024_r30, rkmRowHi_m1024_r30⟩,
  ⟨31, [1], [24526286], [36], rkmMasksHi_m1024_r31, rkmRowHi_m1024_r31⟩,
  ⟨32, [1, 1, 1, 1, 1, 1, 1, 1],
    [11801948, 11831604, 372745, 393642, 31609, 32423, 38767, 36954],
    [18, 18, 1, 1, 1, 1, 1, 1], rkmMasksHi_m1024_r32, rkmRowHi_m1024_r32⟩,
  ⟨64, [1], [24836200], [71], rkmMasksHi_m1024_r64, rkmRowHi_m1024_r64⟩,
  ⟨128, [1, 1, 1, 1],
    [24200000, 862750, 152800, 112000],
    [141, 6, 1, 1], rkmMasksHi_m1024_r128, rkmRowHi_m1024_r128⟩,
  ⟨256, [1, 1, 1, 1, 1, 1, 1, 1],
    [11459120, 12390620, 953164, 575695, 390513, 302340, 172311, 92780],
    [118, 128, 10, 6, 5, 4, 2, 1], rkmMasksHi_m1024_r256, rkmRowHi_m1024_r256⟩,
  ⟨512, [1, 1, 1, 1, 1, 1, 1, 1],
    [13144971, 13456648, 828406, 427576, 222203, 286915, 370292, 300839],
    [253, 259, 16, 9, 5, 6, 8, 6], rkmMasksHi_m1024_r512, rkmRowHi_m1024_r512⟩
  ]
/-- Sorted active multi-segment anchors (`m = 1024, kMax = 512`). -/
def rkmAnchorsHi_m1024 : List RampKickAnchor :=
  rkmAncPHi_m1024_p0 ++ (rkmAncPHi_m1024_p1 ++ (rkmAncPHi_m1024_p2 ++ rkmAncPHi_m1024_p3))

end

public section
/-- Inlined Step-1 hybrid trajectory row certificate `(m = 1024, r = 64)`. -/
theorem rkmTrajHi_m1024_r64 :
    rkmLo12EqHi 1024 8 64 [1]
      [24836200]
      [71] rkmMasksHi_m1024_r64 rkmRowHi_m1024_r64 :=
  rkmCertUltraRow ((by decide +kernel :
    muxNatListEq (rkmEvalT16UltraLo12 1024 8 64 [1]
      [24836200]
      [71] rkmMasksHi_m1024_r64) rkmRowHi_m1024_r64 = true))
/-- Inlined Step-1 hybrid trajectory row certificate `(m = 1024, r = 128)`. -/
theorem rkmTrajHi_m1024_r128 :
    rkmLo12EqHi 1024 8 128 [1, 1, 1, 1]
      [24200000, 862750, 152800, 112000]
      [141, 6, 1, 1] rkmMasksHi_m1024_r128 rkmRowHi_m1024_r128 :=
  rkmCertUltraRow ((by decide +kernel :
    muxNatListEq (rkmEvalT16UltraLo12 1024 8 128 [1, 1, 1, 1]
      [24200000, 862750, 152800, 112000]
      [141, 6, 1, 1] rkmMasksHi_m1024_r128) rkmRowHi_m1024_r128 = true))
private theorem rkmStitchOkHi_m1024_b0 : rkmAllTrueF [
  rkmCheckRowFromWalks 1024 8 256 [1, 1, 1, 1, 1, 1, 1, 1]
    [11459120, 12390620, 953164, 575695, 390513, 302340, 172311, 92780]
    [118, 128, 10, 6, 5, 4, 2, 1] rkmMasksHi_m1024_r256
    rkmWalksHi_m1024_r256 rkmRowHi_m1024_r256,
  muxIntListEq rkmHbHi_m1024_r512_s0_c0 rkmHbHi_m1024_r512_s0_c1,
  muxIntListEq rkmVoHi_m1024_r512_s0_c0 rkmViHi_m1024_r512_s0_c1
  ] = true := by decide +kernel
private theorem rkmStitchOkHi_m1024_b1 : rkmAllTrueF [
  muxIntListEq rkmHbHi_m1024_r512_s0_c0 rkmHbHi_m1024_r512_s0_c2,
  muxIntListEq rkmVoHi_m1024_r512_s0_c1 rkmViHi_m1024_r512_s0_c2,
  muxIntListEq rkmHbHi_m1024_r512_s1_c0 rkmHbHi_m1024_r512_s1_c1,
  muxIntListEq rkmVoHi_m1024_r512_s1_c0 rkmViHi_m1024_r512_s1_c1
  ] = true := by decide +kernel
private theorem rkmStitchOkHi_m1024_b2 : rkmAllTrueF [
  muxIntListEq rkmHbHi_m1024_r512_s1_c0 rkmHbHi_m1024_r512_s1_c2,
  muxIntListEq rkmVoHi_m1024_r512_s1_c1 rkmViHi_m1024_r512_s1_c2,
  rkmCheckRowFromWalks 1024 8 512 [1, 1, 1, 1, 1, 1, 1, 1]
    [13144971, 13456648, 828406, 427576, 222203, 286915, 370292, 300839]
    [253, 259, 16, 9, 5, 6, 8, 6] rkmMasksHi_m1024_r512
    rkmWalksHi_m1024_r512 rkmRowHi_m1024_r512
  ] = true := by decide +kernel
private theorem rkmDim257 :
    Nat.add (highdNatMin (Nat.mul 1 1024) 256) 1 = 257 := by decide +kernel
private theorem rkmDim513 :
    Nat.add (highdNatMin (Nat.mul 1 1024) 512) 1 = 513 := by decide +kernel
private theorem rkmSegChainHi_m1024_r512_s0_u1 :
    muxFastIterFullT16 168 513 rkmHbHi_m1024_r512_s0_c0 rkmViHi_m1024_r512_s0_c0 =
      rkmVoHi_m1024_r512_s0_c1 :=
  rkmChainFastIterT16 rfl
    (rkmAllTrueF_cons (rkmAllTrueF_cons rkmStitchOkHi_m1024_b0).2).1
    (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons rkmStitchOkHi_m1024_b0).2).2).1
    rkmWalkChkHi_m1024_r512_s0_c0 rkmWalkChkHi_m1024_r512_s0_c1
private theorem rkmSegChainHi_m1024_r512_s0_u2 :
    muxFastIterFullT16 253 513 rkmHbHi_m1024_r512_s0_c0 rkmViHi_m1024_r512_s0_c0 =
      rkmVoHi_m1024_r512_s0_c2 :=
  rkmChainFastIterT16 rfl
    (rkmAllTrueF_cons rkmStitchOkHi_m1024_b1).1
    (rkmAllTrueF_cons (rkmAllTrueF_cons rkmStitchOkHi_m1024_b1).2).1
    rkmSegChainHi_m1024_r512_s0_u1 rkmWalkChkHi_m1024_r512_s0_c2
private theorem rkmSegChainHi_m1024_r512_s1_u1 :
    muxFastIterFullT16 172 513 rkmHbHi_m1024_r512_s1_c0 rkmViHi_m1024_r512_s1_c0 =
      rkmVoHi_m1024_r512_s1_c1 :=
  rkmChainFastIterT16 rfl
    (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons rkmStitchOkHi_m1024_b1).2).2).1
    (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
      rkmStitchOkHi_m1024_b1).2).2).2).1
    rkmWalkChkHi_m1024_r512_s1_c0 rkmWalkChkHi_m1024_r512_s1_c1
private theorem rkmSegChainHi_m1024_r512_s1_u2 :
    muxFastIterFullT16 259 513 rkmHbHi_m1024_r512_s1_c0 rkmViHi_m1024_r512_s1_c0 =
      rkmVoHi_m1024_r512_s1_c2 :=
  rkmChainFastIterT16 rfl
    (rkmAllTrueF_cons rkmStitchOkHi_m1024_b2).1
    (rkmAllTrueF_cons (rkmAllTrueF_cons rkmStitchOkHi_m1024_b2).2).1
    rkmSegChainHi_m1024_r512_s1_u1 rkmWalkChkHi_m1024_r512_s1_c2
private theorem rkmSegSndHi_m1024_r256_s0 :
    muxFastIterFullT16 118 (Nat.add (highdNatMin (Nat.mul 1 1024) 256) 1)
      rkmHbHi_m1024_r256_s0_c0 rkmViHi_m1024_r256_s0_c0 =
      rkmVoHi_m1024_r256_s0_c0 := by
  rw [rkmDim257]
  exact rkmWalkChkHi_m1024_r256_s0_c0
private theorem rkmSegSndHi_m1024_r256_s1 :
    muxFastIterFullT16 128 (Nat.add (highdNatMin (Nat.mul 1 1024) 256) 1)
      rkmHbHi_m1024_r256_s1_c0 rkmViHi_m1024_r256_s1_c0 =
      rkmVoHi_m1024_r256_s1_c0 := by
  rw [rkmDim257]
  exact rkmWalkChkHi_m1024_r256_s1_c0
private theorem rkmSegSndHi_m1024_r256_s2 :
    muxFastIterFullT16 10 (Nat.add (highdNatMin (Nat.mul 1 1024) 256) 1)
      rkmHbHi_m1024_r256_s2_c0 rkmViHi_m1024_r256_s2_c0 =
      rkmVoHi_m1024_r256_s2_c0 := by
  rw [rkmDim257]
  exact rkmWalkChkHi_m1024_r256_s2_c0
private theorem rkmSegSndHi_m1024_r256_s3 :
    muxFastIterFullT16 6 (Nat.add (highdNatMin (Nat.mul 1 1024) 256) 1)
      rkmHbHi_m1024_r256_s3_c0 rkmViHi_m1024_r256_s3_c0 =
      rkmVoHi_m1024_r256_s3_c0 := by
  rw [rkmDim257]
  exact rkmWalkChkHi_m1024_r256_s3_c0
private theorem rkmSegSndHi_m1024_r256_s4 :
    muxFastIterFullT16 5 (Nat.add (highdNatMin (Nat.mul 1 1024) 256) 1)
      rkmHbHi_m1024_r256_s4_c0 rkmViHi_m1024_r256_s4_c0 =
      rkmVoHi_m1024_r256_s4_c0 := by
  rw [rkmDim257]
  exact rkmWalkChkHi_m1024_r256_s4_c0
private theorem rkmSegSndHi_m1024_r256_s5 :
    muxFastIterFullT16 4 (Nat.add (highdNatMin (Nat.mul 1 1024) 256) 1)
      rkmHbHi_m1024_r256_s5_c0 rkmViHi_m1024_r256_s5_c0 =
      rkmVoHi_m1024_r256_s5_c0 := by
  rw [rkmDim257]
  exact rkmWalkChkHi_m1024_r256_s5_c0
private theorem rkmSegSndHi_m1024_r256_s6 :
    muxFastIterFullT16 2 (Nat.add (highdNatMin (Nat.mul 1 1024) 256) 1)
      rkmHbHi_m1024_r256_s6_c0 rkmViHi_m1024_r256_s6_c0 =
      rkmVoHi_m1024_r256_s6_c0 := by
  rw [rkmDim257]
  exact rkmWalkChkHi_m1024_r256_s6_c0
private theorem rkmSegSndHi_m1024_r256_s7 :
    muxFastIterFullT16 1 (Nat.add (highdNatMin (Nat.mul 1 1024) 256) 1)
      rkmHbHi_m1024_r256_s7_c0 rkmViHi_m1024_r256_s7_c0 =
      rkmVoHi_m1024_r256_s7_c0 := by
  rw [rkmDim257]
  exact rkmWalkChkHi_m1024_r256_s7_c0
private theorem rkmWalksSndHi_m1024_r256 :
    RkmSegWalksSound 1024 256 [1, 1, 1, 1, 1, 1, 1, 1] [118, 128, 10, 6, 5, 4, 2, 1]
      rkmWalksHi_m1024_r256 := by
  dsimp only [RkmSegWalksSound, rkmWalksHi_m1024_r256]
  exact ⟨rkmSegSndHi_m1024_r256_s0, ⟨rkmSegSndHi_m1024_r256_s1,
    ⟨rkmSegSndHi_m1024_r256_s2, ⟨rkmSegSndHi_m1024_r256_s3,
    ⟨rkmSegSndHi_m1024_r256_s4, ⟨rkmSegSndHi_m1024_r256_s5,
    ⟨rkmSegSndHi_m1024_r256_s6, ⟨rkmSegSndHi_m1024_r256_s7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 1024, r = 256)`. -/
theorem rkmTrajHi_m1024_r256 :
    rkmLo12EqHi 1024 8 256 [1, 1, 1, 1, 1, 1, 1, 1]
      [11459120, 12390620, 953164, 575695, 390513, 302340, 172311, 92780]
      [118, 128, 10, 6, 5, 4, 2, 1] rkmMasksHi_m1024_r256 rkmRowHi_m1024_r256 :=
  rkmCheckRowFromWalks_sound rkmWalksSndHi_m1024_r256
    (rkmAllTrueF_cons rkmStitchOkHi_m1024_b0).1
private theorem rkmSegSndHi_m1024_r512_s0 :
    muxFastIterFullT16 253 (Nat.add (highdNatMin (Nat.mul 1 1024) 512) 1)
      rkmHbHi_m1024_r512_s0_c0 rkmViHi_m1024_r512_s0_c0 =
      rkmVoHi_m1024_r512_s0_c2 := by
  rw [rkmDim513]
  exact rkmSegChainHi_m1024_r512_s0_u2
private theorem rkmSegSndHi_m1024_r512_s1 :
    muxFastIterFullT16 259 (Nat.add (highdNatMin (Nat.mul 1 1024) 512) 1)
      rkmHbHi_m1024_r512_s1_c0 rkmViHi_m1024_r512_s1_c0 =
      rkmVoHi_m1024_r512_s1_c2 := by
  rw [rkmDim513]
  exact rkmSegChainHi_m1024_r512_s1_u2
private theorem rkmSegSndHi_m1024_r512_s2 :
    muxFastIterFullT16 16 (Nat.add (highdNatMin (Nat.mul 1 1024) 512) 1)
      rkmHbHi_m1024_r512_s2_c0 rkmViHi_m1024_r512_s2_c0 =
      rkmVoHi_m1024_r512_s2_c0 := by
  rw [rkmDim513]
  exact rkmWalkChkHi_m1024_r512_s2_c0
private theorem rkmSegSndHi_m1024_r512_s3 :
    muxFastIterFullT16 9 (Nat.add (highdNatMin (Nat.mul 1 1024) 512) 1)
      rkmHbHi_m1024_r512_s3_c0 rkmViHi_m1024_r512_s3_c0 =
      rkmVoHi_m1024_r512_s3_c0 := by
  rw [rkmDim513]
  exact rkmWalkChkHi_m1024_r512_s3_c0
private theorem rkmSegSndHi_m1024_r512_s4 :
    muxFastIterFullT16 5 (Nat.add (highdNatMin (Nat.mul 1 1024) 512) 1)
      rkmHbHi_m1024_r512_s4_c0 rkmViHi_m1024_r512_s4_c0 =
      rkmVoHi_m1024_r512_s4_c0 := by
  rw [rkmDim513]
  exact rkmWalkChkHi_m1024_r512_s4_c0
private theorem rkmSegSndHi_m1024_r512_s5 :
    muxFastIterFullT16 6 (Nat.add (highdNatMin (Nat.mul 1 1024) 512) 1)
      rkmHbHi_m1024_r512_s5_c0 rkmViHi_m1024_r512_s5_c0 =
      rkmVoHi_m1024_r512_s5_c0 := by
  rw [rkmDim513]
  exact rkmWalkChkHi_m1024_r512_s5_c0
private theorem rkmSegSndHi_m1024_r512_s6 :
    muxFastIterFullT16 8 (Nat.add (highdNatMin (Nat.mul 1 1024) 512) 1)
      rkmHbHi_m1024_r512_s6_c0 rkmViHi_m1024_r512_s6_c0 =
      rkmVoHi_m1024_r512_s6_c0 := by
  rw [rkmDim513]
  exact rkmWalkChkHi_m1024_r512_s6_c0
private theorem rkmSegSndHi_m1024_r512_s7 :
    muxFastIterFullT16 6 (Nat.add (highdNatMin (Nat.mul 1 1024) 512) 1)
      rkmHbHi_m1024_r512_s7_c0 rkmViHi_m1024_r512_s7_c0 =
      rkmVoHi_m1024_r512_s7_c0 := by
  rw [rkmDim513]
  exact rkmWalkChkHi_m1024_r512_s7_c0
private theorem rkmWalksSndHi_m1024_r512 :
    RkmSegWalksSound 1024 512 [1, 1, 1, 1, 1, 1, 1, 1] [253, 259, 16, 9, 5, 6, 8, 6]
      rkmWalksHi_m1024_r512 := by
  dsimp only [RkmSegWalksSound, rkmWalksHi_m1024_r512]
  exact ⟨rkmSegSndHi_m1024_r512_s0, ⟨rkmSegSndHi_m1024_r512_s1,
    ⟨rkmSegSndHi_m1024_r512_s2, ⟨rkmSegSndHi_m1024_r512_s3,
    ⟨rkmSegSndHi_m1024_r512_s4, ⟨rkmSegSndHi_m1024_r512_s5,
    ⟨rkmSegSndHi_m1024_r512_s6, ⟨rkmSegSndHi_m1024_r512_s7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 1024, r = 512)`. -/
theorem rkmTrajHi_m1024_r512 :
    rkmLo12EqHi 1024 8 512 [1, 1, 1, 1, 1, 1, 1, 1]
      [13144971, 13456648, 828406, 427576, 222203, 286915, 370292, 300839]
      [253, 259, 16, 9, 5, 6, 8, 6] rkmMasksHi_m1024_r512 rkmRowHi_m1024_r512 :=
  rkmCheckRowFromWalks_sound rkmWalksSndHi_m1024_r512
    (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons rkmStitchOkHi_m1024_b2).2).2).1
private theorem rkm_anc_app_hi_1024 {m0 lMax : ℕ} :
    ∀ {xs ys : List RampKickAnchor},
      RampKickAnchorsSound m0 lMax xs → RampKickAnchorsSound m0 lMax ys →
      RampKickAnchorsSound m0 lMax (xs ++ ys)
  | [], _, _, hy => hy
  | _ :: _, _, ⟨hx0, hxs⟩, hy => ⟨hx0, rkm_anc_app_hi_1024 hxs hy⟩
private theorem rkmAncSndPHi_m1024_p0 : RampKickAnchorsSound 1024 8 rkmAncPHi_m1024_p0 :=
  ⟨rkmTrajHi_m1024_r3, ⟨rkmTrajHi_m1024_r4, ⟨rkmTrajHi_m1024_r5, ⟨rkmTrajHi_m1024_r6,
  ⟨rkmTrajHi_m1024_r7, ⟨rkmTrajHi_m1024_r8, ⟨rkmTrajHi_m1024_r9, ⟨rkmTrajHi_m1024_r10,
  ⟨rkmTrajHi_m1024_r11, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m1024_p1 : RampKickAnchorsSound 1024 8 rkmAncPHi_m1024_p1 :=
  ⟨rkmTrajHi_m1024_r12, ⟨rkmTrajHi_m1024_r13, ⟨rkmTrajHi_m1024_r14, ⟨rkmTrajHi_m1024_r15,
  ⟨rkmTrajHi_m1024_r16, ⟨rkmTrajHi_m1024_r17, ⟨rkmTrajHi_m1024_r18, ⟨rkmTrajHi_m1024_r19,
  ⟨rkmTrajHi_m1024_r20, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m1024_p2 : RampKickAnchorsSound 1024 8 rkmAncPHi_m1024_p2 :=
  ⟨rkmTrajHi_m1024_r21, ⟨rkmTrajHi_m1024_r22, ⟨rkmTrajHi_m1024_r23, ⟨rkmTrajHi_m1024_r24,
  ⟨rkmTrajHi_m1024_r25, ⟨rkmTrajHi_m1024_r26, ⟨rkmTrajHi_m1024_r27, ⟨rkmTrajHi_m1024_r28,
  ⟨rkmTrajHi_m1024_r29, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m1024_p3 : RampKickAnchorsSound 1024 8 rkmAncPHi_m1024_p3 :=
  ⟨rkmTrajHi_m1024_r30, ⟨rkmTrajHi_m1024_r31, ⟨rkmTrajHi_m1024_r32, ⟨rkmTrajHi_m1024_r64,
  ⟨rkmTrajHi_m1024_r128, ⟨rkmTrajHi_m1024_r256, ⟨rkmTrajHi_m1024_r512, trivial⟩⟩⟩⟩⟩⟩⟩
/-- Anchor trajectory soundness bundle (`m = 1024, kMax = 512`). -/
theorem rkmAnchorsSoundHi_m1024 : RampKickAnchorsSound 1024 8 rkmAnchorsHi_m1024 :=
  rkm_anc_app_hi_1024 rkmAncSndPHi_m1024_p0 (rkm_anc_app_hi_1024 rkmAncSndPHi_m1024_p1
    (rkm_anc_app_hi_1024 rkmAncSndPHi_m1024_p2 (rkmAncSndPHi_m1024_p3)))
/-- Kernel Bellman table verification (`m = 1024, kMax = 512`). -/
theorem rkmTableOkHi_m1024 :
    rkmCheckTable 1024 512 8 true rkmVPotHi_m1024 rkmAnchorsHi_m1024 = true := by
  decide +kernel
/-- Unpacked `RampKickTableValid` bundle (`m = 1024, kMax = 512`). -/
theorem rkmValidHi_m1024 :
    RampKickTableValid 1024 512 8 true rkmVPotHi_m1024 rkmAnchorsHi_m1024 :=
  rkmCheckTable_sound rkmTableOkHi_m1024 rkmAnchorsSoundHi_m1024
private theorem rkmBndBatchOkHi_m1024_b0 : rkmAllTrueF [
  rkmCheckAnchorsLMax 2 1 rkmAnchorsHi_m1024,
  rkmCheckAnchorsLMax 2 2 rkmAnchorsHi_m1024,
  checkAltBound12 1024 2 (rkmVPotHi_m1024.getD 2 0) 511663735229 1000000000000,
  rkmCheckAnchorsLMax 4 1 rkmAnchorsHi_m1024,
  rkmCheckAnchorsLMax 4 2 rkmAnchorsHi_m1024
  ] = true := by decide +kernel
/-- Cell `lMax = 1` bound for `(1024, 2)`. -/
theorem rkmCellLMaxHi_m1024_k2 :
    rkmCheckAnchorsLMax 2 1 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b0).1
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(1024, 2)`. -/
theorem rkmCellLMax2Hi_m1024_k2 :
    rkmCheckAnchorsLMax 2 2 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b0).2).1
/-- Relative-cost certificate `511663735229 / 1000000000000` for `(1024, 2)`. -/
theorem rkmBoundHi_m1024_k2 :
    checkAltBound12 1024 2 (rkmVPotHi_m1024.getD 2 0) 511663735229 1000000000000 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b0).2).2).1
/-- Cell `lMax = 1` bound for `(1024, 4)`. -/
theorem rkmCellLMaxHi_m1024_k4 :
    rkmCheckAnchorsLMax 4 1 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    rkmBndBatchOkHi_m1024_b0).2).2).2).1
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(1024, 4)`. -/
theorem rkmCellLMax2Hi_m1024_k4 :
    rkmCheckAnchorsLMax 4 2 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    rkmBndBatchOkHi_m1024_b0).2).2).2).2).1
private theorem rkmBndBatchOkHi_m1024_b1 : rkmAllTrueF [
  checkAltBound12 1024 4 (rkmVPotHi_m1024.getD 4 0) 348072359161 1000000000000,
  rkmCheckAnchorsLMax 8 1 rkmAnchorsHi_m1024,
  rkmCheckAnchorsLMax 8 2 rkmAnchorsHi_m1024,
  checkAltBound12 1024 8 (rkmVPotHi_m1024.getD 8 0) 225566670669 1000000000000,
  rkmCheckAnchorsLMax 16 1 rkmAnchorsHi_m1024
  ] = true := by decide +kernel
/-- Relative-cost certificate `348072359161 / 1000000000000` for `(1024, 4)`. -/
theorem rkmBoundHi_m1024_k4 :
    checkAltBound12 1024 4 (rkmVPotHi_m1024.getD 4 0) 348072359161 1000000000000 = true :=
  (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b1).1
/-- Cell `lMax = 1` bound for `(1024, 8)`. -/
theorem rkmCellLMaxHi_m1024_k8 :
    rkmCheckAnchorsLMax 8 1 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b1).2).1
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(1024, 8)`. -/
theorem rkmCellLMax2Hi_m1024_k8 :
    rkmCheckAnchorsLMax 8 2 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b1).2).2).1
/-- Relative-cost certificate `225566670669 / 1000000000000` for `(1024, 8)`. -/
theorem rkmBoundHi_m1024_k8 :
    checkAltBound12 1024 8 (rkmVPotHi_m1024.getD 8 0) 225566670669 1000000000000 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    rkmBndBatchOkHi_m1024_b1).2).2).2).1
/-- Cell `lMax = 1` bound for `(1024, 16)`. -/
theorem rkmCellLMaxHi_m1024_k16 :
    rkmCheckAnchorsLMax 16 1 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    rkmBndBatchOkHi_m1024_b1).2).2).2).2).1
private theorem rkmBndBatchOkHi_m1024_b2 : rkmAllTrueF [
  rkmCheckAnchorsLMax 16 2 rkmAnchorsHi_m1024,
  checkAltBound12 1024 16 (rkmVPotHi_m1024.getD 16 0) 37360569541 250000000000,
  rkmCheckAnchorsLMax 32 1 rkmAnchorsHi_m1024,
  rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m1024,
  checkAltBound12 1024 32 (rkmVPotHi_m1024.getD 32 0) 12621936221 125000000000
  ] = true := by decide +kernel
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(1024, 16)`. -/
theorem rkmCellLMax2Hi_m1024_k16 :
    rkmCheckAnchorsLMax 16 2 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b2).1
/-- Relative-cost certificate `37360569541 / 250000000000` for `(1024, 16)`. -/
theorem rkmBoundHi_m1024_k16 :
    checkAltBound12 1024 16 (rkmVPotHi_m1024.getD 16 0) 37360569541 250000000000 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b2).2).1
/-- Cell `lMax = 1` bound for `(1024, 32)`. -/
theorem rkmCellLMaxHi_m1024_k32 :
    rkmCheckAnchorsLMax 32 1 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b2).2).2).1
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(1024, 32)`. -/
theorem rkmCellLMax2Hi_m1024_k32 :
    rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    rkmBndBatchOkHi_m1024_b2).2).2).2).1
/-- Relative-cost certificate `12621936221 / 125000000000` for `(1024, 32)`. -/
theorem rkmBoundHi_m1024_k32 :
    checkAltBound12 1024 32 (rkmVPotHi_m1024.getD 32 0) 12621936221 125000000000 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    rkmBndBatchOkHi_m1024_b2).2).2).2).2).1
private theorem rkmBndBatchOkHi_m1024_b3 : rkmAllTrueF [
  rkmCheckAnchorsLMax 64 1 rkmAnchorsHi_m1024,
  rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m1024,
  checkAltBound12 1024 64 (rkmVPotHi_m1024.getD 64 0) 8683495609 125000000000,
  rkmCheckAnchorsLMax 128 1 rkmAnchorsHi_m1024,
  rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m1024
  ] = true := by decide +kernel
/-- Cell `lMax = 1` bound for `(1024, 64)`. -/
theorem rkmCellLMaxHi_m1024_k64 :
    rkmCheckAnchorsLMax 64 1 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b3).1
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(1024, 64)`. -/
theorem rkmCellLMax2Hi_m1024_k64 :
    rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b3).2).1
/-- Relative-cost certificate `8683495609 / 125000000000` for `(1024, 64)`. -/
theorem rkmBoundHi_m1024_k64 :
    checkAltBound12 1024 64 (rkmVPotHi_m1024.getD 64 0) 8683495609 125000000000 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b3).2).2).1
/-- Cell `lMax = 1` bound for `(1024, 128)`. -/
theorem rkmCellLMaxHi_m1024_k128 :
    rkmCheckAnchorsLMax 128 1 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    rkmBndBatchOkHi_m1024_b3).2).2).2).1
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(1024, 128)`. -/
theorem rkmCellLMax2Hi_m1024_k128 :
    rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    rkmBndBatchOkHi_m1024_b3).2).2).2).2).1
private theorem rkmBndBatchOkHi_m1024_b4 : rkmAllTrueF [
  checkAltBound12 1024 128 (rkmVPotHi_m1024.getD 128 0) 24351613583 500000000000,
  rkmCheckAnchorsLMax 256 1 rkmAnchorsHi_m1024,
  rkmCheckAnchorsLMax 256 2 rkmAnchorsHi_m1024,
  checkAltBound12 1024 256 (rkmVPotHi_m1024.getD 256 0) 17563060499 500000000000,
  rkmCheckAnchorsLMax 512 1 rkmAnchorsHi_m1024
  ] = true := by decide +kernel
/-- Relative-cost certificate `24351613583 / 500000000000` for `(1024, 128)`. -/
theorem rkmBoundHi_m1024_k128 :
    checkAltBound12 1024 128 (rkmVPotHi_m1024.getD 128 0) 24351613583 500000000000 = true :=
  (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b4).1
/-- Cell `lMax = 1` bound for `(1024, 256)`. -/
theorem rkmCellLMaxHi_m1024_k256 :
    rkmCheckAnchorsLMax 256 1 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b4).2).1
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(1024, 256)`. -/
theorem rkmCellLMax2Hi_m1024_k256 :
    rkmCheckAnchorsLMax 256 2 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b4).2).2).1
/-- Relative-cost certificate `17563060499 / 500000000000` for `(1024, 256)`. -/
theorem rkmBoundHi_m1024_k256 :
    checkAltBound12 1024 256 (rkmVPotHi_m1024.getD 256 0) 17563060499 500000000000 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    rkmBndBatchOkHi_m1024_b4).2).2).2).1
/-- Cell `lMax = 1` bound for `(1024, 512)`. -/
theorem rkmCellLMaxHi_m1024_k512 :
    rkmCheckAnchorsLMax 512 1 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    rkmBndBatchOkHi_m1024_b4).2).2).2).2).1
private theorem rkmBndBatchOkHi_m1024_b5 : rkmAllTrueF [
  rkmCheckAnchorsLMax 512 2 rkmAnchorsHi_m1024,
  checkAltBound12 1024 512 (rkmVPotHi_m1024.getD 512 0) 6756116497 250000000000
  ] = true := by decide +kernel
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(1024, 512)`. -/
theorem rkmCellLMax2Hi_m1024_k512 :
    rkmCheckAnchorsLMax 512 2 rkmAnchorsHi_m1024 = true :=
  (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b5).1
/-- Relative-cost certificate `6756116497 / 250000000000` for `(1024, 512)`. -/
theorem rkmBoundHi_m1024_k512 :
    checkAltBound12 1024 512 (rkmVPotHi_m1024.getD 512 0) 6756116497 250000000000 = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons rkmBndBatchOkHi_m1024_b5).2).1

/-- Terminal `1`-lane table closure for `RampKickMuxHiCert1024`. -/
theorem laneClosure_FindAllJohnsonRampKickMuxHiCert1024 :
    rkmTrajHi_m1024_r256 = rkmTrajHi_m1024_r256 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi1024T9) rfl).right

end
end QuantumComputation.Specs.DickeSol
