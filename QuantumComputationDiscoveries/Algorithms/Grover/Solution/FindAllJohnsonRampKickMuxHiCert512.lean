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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T0
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T1
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T2
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T3
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T4
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T5
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T6
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T7
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T8
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T9

/-
# Sparse Checkpointed `kMax = 512` Table & Bounds (`FindAllJohnsonRampKickMuxHiCert512`)

Stitches checkpointed `r in {256, 512}` walks and `RampKickTableValid` (`m = 512`).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Prepends `g` `false` entries followed by `true` onto `rest`. -/
def rkmPrependGapHi512 : ℕ → List Bool → List Bool
  | 0, rest => true :: rest
  | g + 1, rest => false :: rkmPrependGapHi512 g rest
/-- Expands gap counts between `true` entries into a trimmed `List Bool` mask. -/
def rkmGapsToMaskHi512 : List ℕ → List Bool
  | [] => []
  | g :: gs => rkmPrependGapHi512 g (rkmGapsToMaskHi512 gs)
/-- Mask `0` for `(512, 256)`. -/
def rkmMkHi_m512_r256_s0 : List Bool := rkmGapsToMaskHi512 [
  75, 0, 0, 0, 0, 2, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3
  ]
/-- Mask `1` for `(512, 256)`. -/
def rkmMkHi_m512_r256_s1 : List Bool := rkmGapsToMaskHi512 [
  1, 1, 1, 1, 1, 0, 1, 3, 2, 1, 1, 2, 4, 2, 4, 1, 10, 0, 15, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 0, 1,
  36, 8, 2, 0, 0, 0, 0, 4, 2, 1, 2, 6, 23, 4, 2, 2, 1, 0, 0, 2, 0, 1, 1, 1, 2, 0, 0, 1, 0, 0, 0,
  1, 1, 4, 0, 0, 3, 0, 0
  ]
/-- Mask `2` for `(512, 256)`. -/
def rkmMkHi_m512_r256_s2 : List Bool := rkmGapsToMaskHi512 [
  1, 1, 2, 7, 7, 0, 3, 0, 0, 5, 2, 1, 0, 2, 0, 4, 2, 2, 0, 1, 3, 10, 11, 14, 2, 3, 1, 1, 13, 22,
  9, 3, 1, 3, 0, 2, 2, 1, 2, 1, 4, 7, 5, 6, 9, 0, 3, 0, 2, 0, 2, 1, 1, 1, 0, 1, 2, 1, 0, 1, 0, 1
  ]
/-- Mask `3` for `(512, 256)`. -/
def rkmMkHi_m512_r256_s3 : List Bool := rkmGapsToMaskHi512 [
  2, 5, 14, 3, 0, 3, 6, 3, 6, 1, 3, 10, 2, 2, 3, 2, 1, 11, 2, 13, 2, 1, 26, 0, 3, 5, 3, 3, 0, 3,
  1, 11, 0, 0, 2, 3, 1, 14, 1, 0, 2, 1, 5, 0, 1, 0, 0, 1, 0, 4, 1, 0, 3, 2, 0, 0, 1, 0, 0, 0, 0,
  0
  ]
/-- Mask `4` for `(512, 256)`. -/
def rkmMkHi_m512_r256_s4 : List Bool := rkmGapsToMaskHi512 [
  3, 9, 6, 9, 0, 4, 12, 5, 0, 8, 13, 0, 29, 4, 3, 0, 20, 8, 4, 6, 4, 0, 9, 0, 4, 1, 3, 15, 1, 9,
  0, 3, 5, 1, 3, 1, 4, 0, 0, 0
  ]
/-- Mask `5` for `(512, 256)`. -/
def rkmMkHi_m512_r256_s5 : List Bool := rkmGapsToMaskHi512 [
  1, 2, 28, 6, 7, 12, 24, 2, 2, 2, 18, 4, 4, 11, 0, 4, 9, 7, 20, 0, 2, 3, 2, 4, 1, 4, 0, 0, 1, 6,
  4, 4, 3, 0, 2, 0, 1, 0, 0, 1, 0, 1, 3, 6
  ]
/-- Mask `6` for `(512, 256)`. -/
def rkmMkHi_m512_r256_s6 : List Bool := rkmGapsToMaskHi512 [
  12, 18, 0, 0, 0, 7, 18, 21, 9, 20, 6, 0, 8, 1, 15, 9, 13, 0, 28, 2, 9, 8, 4, 0, 0, 0, 2, 1, 1,
  1, 0, 0, 1, 0, 0, 2
  ]
/-- Segment sign-flip masks for `(m = 512, r = 256)`. -/
def rkmMasksHi_m512_r256 : List (List Bool) := [
  rkmMkHi_m512_r256_s0, rkmMkHi_m512_r256_s1, rkmMkHi_m512_r256_s2,
  rkmMkHi_m512_r256_s3, rkmMkHi_m512_r256_s4, rkmMkHi_m512_r256_s5,
  rkmMkHi_m512_r256_s6, []
  ]
/-- Part 0 of `rkmRowHi_m512_r256`. -/
def rkmRowHi_m512_r256_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Part 1 of `rkmRowHi_m512_r256`. -/
def rkmRowHi_m512_r256_p1 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Part 2 of `rkmRowHi_m512_r256`. -/
def rkmRowHi_m512_r256_p2 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 376, 613, 3283, 613,
  132, 561, 52145, 41255, 272708, 832301, 3638367, 6699481, 14341, 18350801, 24051085, 24566,
  164213689, 920905512, 5095537, 1178154061, 997677583253
  ]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 256)`. -/
def rkmRowHi_m512_r256 : List ℕ :=
  rkmRowHi_m512_r256_p0 ++ (rkmRowHi_m512_r256_p1 ++ rkmRowHi_m512_r256_p2)
/-- Pre-certified segment walks for `(m = 512, r = 256)`. -/
def rkmWalksHi_m512_r256 : List RkmSegWalk := [
  ⟨rkmHbHi_m512_r256_s0_c0, rkmViHi_m512_r256_s0_c0, rkmVoHi_m512_r256_s0_c0⟩,
  ⟨rkmHbHi_m512_r256_s1_c0, rkmViHi_m512_r256_s1_c0, rkmVoHi_m512_r256_s1_c0⟩,
  ⟨rkmHbHi_m512_r256_s2_c0, rkmViHi_m512_r256_s2_c0, rkmVoHi_m512_r256_s2_c0⟩,
  ⟨rkmHbHi_m512_r256_s3_c0, rkmViHi_m512_r256_s3_c0, rkmVoHi_m512_r256_s3_c0⟩,
  ⟨rkmHbHi_m512_r256_s4_c0, rkmViHi_m512_r256_s4_c0, rkmVoHi_m512_r256_s4_c0⟩,
  ⟨rkmHbHi_m512_r256_s5_c0, rkmViHi_m512_r256_s5_c0, rkmVoHi_m512_r256_s5_c0⟩,
  ⟨rkmHbHi_m512_r256_s6_c0, rkmViHi_m512_r256_s6_c0, rkmVoHi_m512_r256_s6_c0⟩,
  ⟨rkmHbHi_m512_r256_s7_c0, rkmViHi_m512_r256_s7_c0, rkmVoHi_m512_r256_s7_c0⟩
  ]
/-- Mask `0` for `(512, 512)`. -/
def rkmMkHi_m512_r512_s0 : List Bool := rkmGapsToMaskHi512 [
  23, 0, 0, 0, 5, 0, 1, 1, 0, 0, 0, 0, 1, 111, 2, 7, 0, 0
  ]
/-- Mask `1` for `(512, 512)`. -/
def rkmMkHi_m512_r512_s1 : List Bool := rkmGapsToMaskHi512 [
  5, 2, 0, 1, 0, 0, 0, 0, 2, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 2, 0, 6, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 3, 0, 0, 1, 0, 0, 2, 0, 4, 2, 4, 7, 0, 1, 0, 2,
  5, 0, 0, 0, 0, 0, 2, 0, 1, 0, 6, 0, 0, 0, 0, 7, 4, 3, 0, 0, 0, 0, 0, 0, 7, 2, 0, 1, 0, 0, 0, 0,
  1, 0, 0, 0, 0, 0, 0, 8, 0, 0, 1, 0, 0, 2, 3, 0, 5, 0, 0, 0, 0, 1, 0, 0, 0, 0, 94, 0, 0, 0, 0,
  0, 0, 8, 0, 1, 0, 0, 1
  ]
/-- Mask `2` for `(512, 512)`. -/
def rkmMkHi_m512_r512_s2 : List Bool := rkmGapsToMaskHi512 [
  1, 3, 0, 3, 1, 3, 0, 0, 3, 5, 3, 0, 3, 0, 3, 0, 0, 0, 0, 0, 1, 0, 3, 4, 0, 0, 0, 0, 3, 0, 0, 1,
  1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 0, 1, 2, 1, 1, 2, 2, 1, 0, 1, 0, 1,
  0, 1, 1, 2, 1, 0, 2, 1, 1, 0, 1, 0, 1, 1, 0, 1, 7, 0, 1, 6, 2, 0, 1, 1, 0, 2, 0, 0, 2, 0, 2, 4,
  4, 0, 1, 3, 0, 1, 2, 0, 0, 0, 1, 1, 2, 1, 2, 0, 4, 0, 2, 1, 0, 2, 0, 0, 0, 0, 0, 2, 0, 5, 1, 0,
  2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 4, 2, 1, 0, 0, 0, 0, 2, 7, 3, 0, 2, 2, 2, 0, 1, 0, 0, 1, 0, 0,
  0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 4, 1, 0, 0, 0, 0, 0, 2, 0, 0, 1, 3, 3, 0, 0, 0, 0, 6, 0,
  9, 44, 0, 0, 0, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0
  ]
/-- Mask `3` for `(512, 512)`. -/
def rkmMkHi_m512_r512_s3 : List Bool := rkmGapsToMaskHi512 [
  2, 0, 4, 1, 1, 0, 0, 0, 3, 0, 0, 0, 2, 2, 0, 1, 1, 0, 0, 3, 0, 1, 0, 1, 1, 1, 1, 1, 4, 0, 2, 0,
  0, 0, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 0, 0, 4, 1, 0, 0, 1, 0, 0, 0, 0, 3, 2, 5, 1, 2, 0, 0, 1,
  0, 1, 1, 1, 0, 0, 2, 1, 0, 0, 4, 1, 0, 0, 0, 0, 0, 3, 2, 0, 0, 1, 2, 1, 0, 4, 0, 0, 0, 2, 1, 0,
  1, 3, 2, 0, 0, 0, 2, 1, 0, 0, 1, 5, 3, 0, 1, 3, 0, 0, 1, 2, 2, 0, 0, 1, 1, 0, 2, 0, 1, 0, 0, 2,
  1, 0, 0, 0, 2, 2, 1, 0, 0, 0, 1, 2, 6, 1, 0, 0, 2, 0, 0, 1, 1, 3, 1, 0, 0, 1, 23, 0, 2, 0, 5,
  2, 4, 5, 2, 6, 0, 3, 0, 8, 2, 1, 2, 1, 0, 1, 0, 8, 0, 2, 0, 3, 5, 0, 8, 3, 4, 1, 0, 1, 0, 1, 0,
  1, 3, 1, 1, 0, 1, 1, 2, 1, 4, 5, 2, 2, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0, 10, 0
  ]
/-- Mask `4` for `(512, 512)`. -/
def rkmMkHi_m512_r512_s4 : List Bool := rkmGapsToMaskHi512 [
  1, 1, 0, 0, 2, 0, 7, 2, 3, 0, 1, 0, 2, 1, 0, 1, 3, 4, 0, 8, 5, 0, 0, 3, 0, 2, 2, 1, 0, 0, 3, 0,
  3, 2, 2, 7, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 6, 1, 0, 0, 0, 1, 1, 4, 1, 0, 0, 0, 0, 5, 0, 0, 0,
  0, 0, 0, 1, 0, 4, 0, 1, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 1, 0, 0, 2, 0, 0, 2, 0, 1, 0, 0, 0, 1, 0,
  0, 0, 1, 1, 0, 3, 0, 1, 0, 0, 0, 0, 1, 0, 2, 2, 2, 1, 0, 2, 0, 0, 1, 1, 3, 2, 1, 2, 0, 0, 0, 0,
  2, 2, 0, 0, 0, 0, 2, 4, 0, 0, 2, 4, 23, 0, 1, 1, 3, 1, 1, 0, 2, 0, 1, 2, 0, 1, 0, 1, 0, 1, 5,
  0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 2, 0, 8, 2, 1, 15, 2, 6, 1, 7, 1, 0, 2, 1, 2, 4, 2, 1, 2, 0, 0,
  4, 1, 0, 2, 3, 1, 3, 0, 0, 3, 0, 2, 2, 2, 1, 0, 0, 0, 0, 2, 3, 0, 1, 0, 1, 0, 3, 7
  ]
/-- Mask `5` for `(512, 512)`. -/
def rkmMkHi_m512_r512_s5 : List Bool := rkmGapsToMaskHi512 [
  1, 16, 2, 4, 0, 0, 0, 3, 5, 0, 0, 0, 1, 0, 0, 0, 1, 2, 0, 0, 0, 1, 1, 3, 2, 2, 3, 7, 1, 0, 0,
  0, 0, 1, 2, 0, 0, 1, 2, 3, 0, 0, 0, 1, 0, 4, 3, 2, 4, 1, 0, 0, 1, 5, 0, 4, 1, 4, 0, 0, 1, 0, 0,
  3, 0, 4, 1, 2, 0, 1, 0, 2, 0, 0, 3, 0, 3, 0, 2, 3, 0, 1, 0, 6, 0, 0, 1, 0, 2, 1, 0, 2, 0, 0, 3,
  0, 0, 1, 0, 1, 2, 0, 0, 2, 0, 0, 0, 0, 32, 1, 1, 1, 1, 3, 1, 1, 1, 1, 0, 2, 1, 1, 2, 1, 0, 7,
  0, 2, 0, 2, 3, 1, 0, 2, 0, 0, 0, 7, 4, 0, 3, 0, 8, 4, 0, 10, 1, 0, 5, 0, 3, 0, 0, 0, 4, 1, 1,
  0, 1, 1, 2, 0, 10, 0, 3, 4, 0, 0, 6, 0, 1, 2, 0, 2, 0, 0, 1, 11, 1, 0, 0, 1, 1, 2, 1, 1, 1, 1,
  0, 1, 0, 0, 1, 0
  ]
/-- Mask `6` for `(512, 512)`. -/
def rkmMkHi_m512_r512_s6 : List Bool := rkmGapsToMaskHi512 [
  1, 0, 1, 0, 0, 1, 0, 0, 6, 1, 0, 0, 2, 0, 0, 0, 0, 0, 0, 3, 1, 0, 3, 0, 0, 0, 1, 0, 0, 0, 0, 0,
  0, 0, 0, 1, 1, 4, 2, 0, 3, 0, 3, 0, 0, 0, 0, 6, 1, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 1, 5,
  0, 3, 0, 4, 0, 0, 3, 2, 2, 10, 3, 1, 0, 4, 2, 3, 1, 2, 7, 0, 0, 1, 0, 2, 0, 1, 1, 4, 2, 0, 1,
  0, 0, 1, 0, 1, 0, 0, 2, 3, 0, 0, 0, 0, 1, 7, 1, 3, 1, 0, 24, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 3,
  0, 0, 0, 0, 4, 0, 11, 1, 0, 0, 0, 0, 0, 0, 7, 0, 1, 0, 1, 8, 0, 6, 0, 0, 0, 4, 0, 9, 0, 2, 0,
  3, 0, 0, 1, 4, 0, 4, 0, 0, 1, 0, 1, 6, 0, 0, 0, 2, 0, 0, 0, 1, 2, 0, 0, 1, 1, 4, 0, 1, 0, 0, 6,
  0, 3, 0, 0, 1, 0, 1, 5, 1, 0, 1, 3, 0, 0, 0, 5, 9, 0, 11, 0, 1, 0, 0, 0, 0
  ]
/-- Segment sign-flip masks for `(m = 512, r = 512)`. -/
def rkmMasksHi_m512_r512 : List (List Bool) := [
  rkmMkHi_m512_r512_s0, rkmMkHi_m512_r512_s1, rkmMkHi_m512_r512_s2,
  rkmMkHi_m512_r512_s3, rkmMkHi_m512_r512_s4, rkmMkHi_m512_r512_s5,
  rkmMkHi_m512_r512_s6, []
  ]
/-- Part 0 of `rkmRowHi_m512_r512`. -/
def rkmRowHi_m512_r512_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 21, 0, 0, 10, 0, 0, 0, 0, 4, 21, 0, 0, 0, 16, 0, 0, 0, 27,
  18, 34, 0, 0, 4, 0, 0, 0, 0, 3, 0, 2
  ]
/-- Part 1 of `rkmRowHi_m512_r512`. -/
def rkmRowHi_m512_r512_p1 : List ℕ := [
  2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 11, 0, 0, 0, 11, 18, 29, 0, 0, 0, 0, 0, 0, 4, 0,
  0, 0, 6, 0, 0, 0, 5, 0, 4, 0, 6, 1, 14, 1, 1, 0, 0, 0, 1, 21, 14, 0, 0, 0, 8, 4, 0, 0, 16, 3,
  12, 0, 28, 28, 0, 2, 0, 15, 0, 19, 59, 2, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 17, 0, 14,
  15, 35, 0, 0, 0, 0, 0, 0, 2, 0, 0, 17, 26, 23, 2, 3
  ]
/-- Part 2 of `rkmRowHi_m512_r512`. -/
def rkmRowHi_m512_r512_p2 : List ℕ := [
  0, 0, 68, 36, 0, 0, 11, 8, 0, 0, 0, 4, 0, 30, 1, 0, 4, 45, 1, 628, 1556, 6383, 17333, 39434,
  78930, 99895, 135854, 158597, 201725, 273963, 336178, 369402, 377426, 432030, 492163, 508858,
  442047, 405986, 333441, 217113, 119482, 83583, 30097, 3370, 2547, 1255, 118, 192, 96, 146, 298,
  379, 1, 289, 268, 46, 265, 0, 294, 141, 100, 0, 305, 0, 214, 0, 7, 130, 71, 258, 18, 99, 100,
  372, 110, 83, 17, 166, 99, 20, 182, 87, 1, 61, 39, 2, 832, 173, 0, 102, 32, 572, 696, 4228,
  1408, 2329, 308, 2627, 954, 3960, 6, 602, 1720, 996, 0
  ]
/-- Part 3 of `rkmRowHi_m512_r512`. -/
def rkmRowHi_m512_r512_p3 : List ℕ := [
  3286, 2726, 8388, 4907, 207, 19075, 3782, 4421, 0, 12764, 26460, 2475, 97619, 55724, 4906,
  50425, 5398, 7622, 1432, 15837, 3413, 3991, 169, 7868, 33113, 4149, 2307, 2239, 234, 5815,
  7784, 40482, 62740, 64625, 92517, 6479, 63284, 2415, 31165, 500, 140546, 296817, 240318, 90233,
  12370, 22473, 257327, 213871, 1131, 78619, 147797, 3063, 464131, 355373, 54115, 278, 93359,
  906208, 1068711, 269950, 405633, 138177, 1757267, 1662785, 506651, 796671, 1943366, 70421,
  2073493, 925, 1697, 27645, 20451, 2679, 39, 19525, 3964, 3265, 2, 3232, 2322, 6436, 1494, 1321,
  3495, 4449, 45047, 10171, 20604, 10864, 5488, 48, 3810, 26683, 260, 1283, 30668, 68337, 72118,
  135, 47355, 9427, 10130, 22580, 52
  ]
/-- Part 4 of `rkmRowHi_m512_r512`. -/
def rkmRowHi_m512_r512_p4 : List ℕ := [
  8437, 52082, 133774, 35758, 66072, 3371, 180, 38730, 18907, 32015, 5054, 309699, 2081, 581,
  103757, 1932, 26297, 19832, 132723, 209276, 4157, 318051, 39199, 628026, 464227, 959, 7231318,
  1481948, 183, 6498, 11632, 22, 27301, 160, 1220, 16917, 8418, 31647, 6614, 9474, 17260, 1035,
  429, 9387, 122273, 2851, 94738, 29124, 76778, 26217, 83021, 150155, 71, 11353, 505810, 353024,
  211418, 14890, 1964920, 4670549, 7873230, 5986391, 2183938, 7261467, 55336, 422363, 4236040,
  4994367, 3528932, 15223711, 108666, 7543987, 9918902, 18436414, 2820682, 6351853, 17353091,
  27543054, 6109812, 145323371, 36343306, 445926438, 177367669, 31817662, 292647221, 224967429,
  479672076, 78327629, 2731446216, 2352021617, 1145465549, 991670009151
  ]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 512)`. -/
def rkmRowHi_m512_r512 : List ℕ :=
  rkmRowHi_m512_r512_p0 ++ (rkmRowHi_m512_r512_p1 ++ (rkmRowHi_m512_r512_p2
  ++ (rkmRowHi_m512_r512_p3 ++ rkmRowHi_m512_r512_p4)))
/-- Pre-certified segment walks for `(m = 512, r = 512)`. -/
def rkmWalksHi_m512_r512 : List RkmSegWalk := [
  ⟨rkmHbHi_m512_r512_s0_c0, rkmViHi_m512_r512_s0_c0, rkmVoHi_m512_r512_s0_c1⟩,
  ⟨rkmHbHi_m512_r512_s1_c0, rkmViHi_m512_r512_s1_c0, rkmVoHi_m512_r512_s1_c1⟩,
  ⟨rkmHbHi_m512_r512_s2_c0, rkmViHi_m512_r512_s2_c0, rkmVoHi_m512_r512_s2_c1⟩,
  ⟨rkmHbHi_m512_r512_s3_c0, rkmViHi_m512_r512_s3_c0, rkmVoHi_m512_r512_s3_c1⟩,
  ⟨rkmHbHi_m512_r512_s4_c0, rkmViHi_m512_r512_s4_c0, rkmVoHi_m512_r512_s4_c0⟩,
  ⟨rkmHbHi_m512_r512_s5_c0, rkmViHi_m512_r512_s5_c0, rkmVoHi_m512_r512_s5_c0⟩,
  ⟨rkmHbHi_m512_r512_s6_c0, rkmViHi_m512_r512_s6_c0, rkmVoHi_m512_r512_s6_c0⟩,
  ⟨rkmHbHi_m512_r512_s7_c0, rkmViHi_m512_r512_s7_c0, rkmVoHi_m512_r512_s7_c0⟩
  ]
/-- Part 0 of `rkmVPotHi_m512`. -/
def rkmVPotHi_m512_p0 : List ℕ := [
  0, 28403554933222, 30328693038726, 33275405666113, 33664605245648,
  33903136251349, 34067146471162, 34188894595958, 34284383842137, 34362454437033,
  34428387732267, 34485533223114, 34536112535553, 34581670554001, 34623301594533,
  34661802436625, 34697734247236, 34731636920925, 34763748160436, 34794446558978,
  34823923322204, 34852442106566, 34879910181647, 34906677416165, 34932783513226,
  34958307327445, 34983321107047, 35007887170831, 35032057596725, 35055878720281,
  35079594368695, 35102855113689, 35125506664154, 40069930927738, 44941100411803,
  49742177472049, 54476103294253, 59145618961147, 63753284007580, 68301492820539,
  72792489182274, 77228379207205, 81611142884234, 85942644403914, 90224641423266,
  94458793398822, 98646669099930, 102789753398775, 106889453420435, 110947104125181,
  114963973385799, 118941266614658, 122880130988396, 126781659312171, 130646893560366,
  134476828126255, 138272412809346, 142034555565819, 145764125044636, 149461952929377,
  153128836103693, 156765538656346, 160372793740122, 163951305297430, 35817138122409,
  39340165519942, 42836401445786, 46306447969722, 49750884944214, 53170271135519,
  56565145281818, 59936027084043, 63283418134558, 66607802788391, 69909648981309,
  73189408998637, 76447520198406, 79684405692099, 82900474985995, 86096124585861,
  89271738567528, 92427689115664, 95564337032891, 98682032221213, 101781114137578,
  104861912225249, 107924746322535, 110969927050322, 113997756179727, 117008526981113,
  120002524555603, 122980026150153, 125941301457173, 128886612899611, 131816215902352,
  134730359150727, 137629284836873, 140513228894634, 143382421223647, 146237085903215,
  149077441396538, 151903700745811, 154716071758705, 157514757186671, 160299954895516,
  163071858028649, 165830655163382, 168576530460638, 171309663808411, 174030230959288,
  176738403662329, 179434349789596, 182118233457577, 184790215143774, 187450451798668,
  190099096953303, 192736300822681, 195362210405173, 197976969578134, 200580719189889,
  203173597148267, 205755738505833, 208327275541972, 210888337841962, 213439052373170,
  215979543558504, 218509933347231, 221030341283287, 37279236607119
  ]
/-- Part 1 of `rkmVPotHi_m512`. -/
def rkmVPotHi_m512_p1 : List ℕ := [
  39780030175502, 42271186738603, 44752816855478, 47225028987270, 49687929552523,
  52141622980631, 54586211763508, 57021796505541, 59448475971899, 61866347135266,
  64275505221058, 66676043751181, 69068054586395, 71451627967327, 73826852554198,
  76193815465300, 78552602314282, 80903297246280, 83245982972943, 85580740806390,
  87907650692142, 90226791241059, 92538239760332, 94842072283549, 97138363599877,
  99427187282392, 101708615715583, 103982720122063, 106249570588509, 108509236090870,
  110761784518853, 113007282699721, 115245796421427, 117477390455104, 119702128576930,
  121920073589396, 124131287341991, 126335830751326, 128533763820715, 130725145659230,
  132910034500247, 135088487719506, 137260561852686, 139426312612526, 141585794905500,
  143739062848057, 145886169782442, 148027168292118, 150162110216790, 152291046667049,
  154414028038649, 156531104026427, 158642323637875, 160747735206375, 162847386404112,
  164941324254666, 167029595145301, 169112244838955, 171189318485940, 173260860635363,
  175326915246273, 177387525698548, 179442734803519, 181492584814349, 183537117436168,
  185576373835974, 187610394652302, 189639220004675, 191662889502837, 193681442255774,
  195694916880533, 197703351510842, 199706783805537, 201705250956800, 203698789698215,
  205687436312645, 207671226639937, 209650196084460, 211624379622473, 213593811809342,
  215558526786595, 217518558288826, 219473939650455, 221424703812343, 223370883328264,
  225312510371247, 227249616739777, 229182233863875, 231110392811045, 233034124292103,
  234953458666884, 236868425949829, 238779055815465, 240685377603769, 242587420325424,
  244485212666970, 246378782995852, 248268159365368, 250153369519517, 252034440897754,
  253911400639647, 255784275589447, 257653092300567, 259517877039976, 261378655792504,
  263235454265067, 265088297890813, 266937211833184, 268782220989903, 270623349996887,
  272460623232085, 274294064819243, 276123698631601, 277949548295518, 279771637194034,
  281589988470361, 283404625031314, 285215569550678, 287022844472514, 288826472014402,
  290626474170631, 292422872715325, 294215689205519, 296004944984173, 297790661183142,
  299572858726084, 301351558331320, 41145735771575
  ]
/-- Part 2 of `rkmVPotHi_m512`. -/
def rkmVPotHi_m512_p2 : List ℕ := [
  42917500849024, 44685828939575, 46450739967821, 48212253666588, 49970389579507,
  51725167063547, 53476605291499, 55224723254421, 56969539764042, 58711073455121,
  60449342787770, 62184366049738, 63916161358656, 65644746664241, 67370139750471,
  69092358237717, 70811419584843, 72527341091271, 74240139899012, 75949832994665,
  77656437211380, 79359969230794, 81060445584933, 82757882658083, 84452296688632,
  86143703770883, 87832119856838, 89517560757951, 91200042146858, 92879579559076,
  94556188394676, 96229883919934, 97900681268947, 99568595445236, 101233641323313,
  102895833650230, 104555187047104, 106211716010616, 107865434914491, 109516358010950,
  111164499432145, 112809873191570, 114452493185451, 116092373194115, 117729526883340,
  119363967805682, 120995709401785, 122624765001670, 124251147826006, 125874870987361,
  127495947491437, 129114390238284, 130730212023497, 132343425539398, 133954043376199,
  135562078023147, 137167541869655, 138770447206415, 140370806226497, 141968631026430,
  143563933607269, 145156725875647, 146747019644811, 148334826635645, 149920158477677,
  151503026710075, 153083442782623, 154661418056691, 156236963806187, 157810091218494,
  159380811395401, 160949135354015, 162515074027661, 164078638266774, 165639838839775,
  167198686433936, 168755191656234, 170309365034193, 171861217016715, 173410757974898,
  174957998202847, 176502947918469, 178045617264265, 179586016308101, 181124155043978,
  182660043392789, 184193691203064, 185725108251707, 187254304244724, 188781288817939,
  190306071537704, 191828661901598, 193349069339116, 194867303212353, 196383372816673,
  197897287381376, 199409056070351, 200918687982726, 202426192153505, 203931577554198,
  205434853093447, 206936027617638, 208435109911511, 209932108698756, 211427032642610,
  212919890346439, 214410690354316, 215899441151591, 217386151165457, 218870828765503,
  220353482264267, 221834119917777, 223312749926088, 224789380433811, 226264019530638,
  227736675251857, 229207355578865, 230676068439672, 232142821709399, 233607623210770,
  235070480714600, 236531401940277, 237990394556234, 239447466180422, 240902624380772,
  242355876675654, 243807230534330, 245256693377403
  ]
/-- Part 3 of `rkmVPotHi_m512`. -/
def rkmVPotHi_m512_p3 : List ℕ := [
  246704272577260, 248149975458506, 249593809298400, 251035781327281, 252475898728991,
  253914168641291, 255350598156277, 256785194320784, 258217964136791, 259648914561822,
  261078052509336, 262505384849120, 263930918407673, 265354659968587, 266776616272923,
  268196794019585, 269615199865685, 271031840426912, 272446722277888, 273859851952525,
  275271235944377, 276680880706990, 278088792654243, 279494978160690, 280899443561898,
  282302195154779, 283703239197918, 285102581911901, 286500229479636, 287896188046672,
  289290463721515, 290683062575938, 292073990645291, 293463253928805, 294850858389897,
  296236809956464, 297621114521182, 299003777941796, 300384806041411, 301764204608778,
  303141979398575, 304518136131690, 305892680495495, 307265618144123, 308636954698739,
  310006695747806, 311374846847354, 312741413521241, 314106401261413, 315469815528163,
  316831661750384, 318191945325823, 319550671621329, 320907845973101, 322263473686933,
  323617560038454, 324970110273370, 326321129607699, 327670623228007, 329018596291641,
  330365053926956, 331710001233545, 333053443282464, 334395385116455, 335735831750167,
  337074788170373, 338412259336189, 339748250179288, 341082765604109, 342415810488070,
  343747389681776, 345077508009223, 346406170268005, 347733381229512, 349059145639132,
  350383468216450, 351706353655442, 353027806624670, 354347831767474, 355666433702163,
  356983617022203, 358299386296403, 359613746069101, 360926700860347, 362238255166084,
  363548413458327, 364857180185343, 366164559771824, 367470556619064, 368775175105131,
  370078419585039, 371380294390917, 372680803832176, 373979952195677, 375277743745896,
  376574182725085, 377869273353437, 379163019829244, 380455426329056, 381746497007839,
  383036235999131, 384324647415196, 385611735347177, 386897503865247, 388181957018760,
  389465098836399, 390746933326324, 392027464476319, 393306696253935, 394584632606634,
  395861277461931, 397136634727535, 398410708291490, 399683502022310, 400955019769119,
  402225265361786, 403494242611059, 404761955308698, 406028407227609, 407293602121973,
  408557543727377, 409820235760943, 411081681921454, 412341885889482, 413600851327513,
  414858581880069, 416115081173835, 52115641743073
  ]
/-- Bellman `10 ^ 15`-scaled potential table `vPot[0..512]` (`m = 512`). -/
def rkmVPotHi_m512 : List ℕ :=
  rkmVPotHi_m512_p0 ++ (rkmVPotHi_m512_p1 ++ (rkmVPotHi_m512_p2 ++ rkmVPotHi_m512_p3))
/-- Part 0 of `rkmMkHi_m512_r64_s0`. -/
def rkmMkHi_m512_r64_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 1 of `rkmMkHi_m512_r64_s0`. -/
def rkmMkHi_m512_r64_s0_p1 : List Bool := [
  false, false, true, true, true, true, true, false, false, true, true, true, true, true, true
  ]
/-- Mask segment 0 for `(m = 512, r = 64)`. -/
def rkmMkHi_m512_r64_s0 : List Bool := rkmMkHi_m512_r64_s0_p0 ++ rkmMkHi_m512_r64_s0_p1
/-- Part 0 of `rkmMkHi_m512_r64_s1`. -/
def rkmMkHi_m512_r64_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 1 of `rkmMkHi_m512_r64_s1`. -/
def rkmMkHi_m512_r64_s1_p1 : List Bool := [
  false, false, false, false, false, false, false, false, true, false, true, false, false, true,
  false, false, true, true
  ]
/-- Mask segment 1 for `(m = 512, r = 64)`. -/
def rkmMkHi_m512_r64_s1 : List Bool := rkmMkHi_m512_r64_s1_p0 ++ rkmMkHi_m512_r64_s1_p1
/-- Part 0 of `rkmMkHi_m512_r64_s2`. -/
def rkmMkHi_m512_r64_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 1 of `rkmMkHi_m512_r64_s2`. -/
def rkmMkHi_m512_r64_s2_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, true, false, true
  ]
/-- Mask segment 2 for `(m = 512, r = 64)`. -/
def rkmMkHi_m512_r64_s2 : List Bool := rkmMkHi_m512_r64_s2_p0 ++ rkmMkHi_m512_r64_s2_p1
/-- Prefix-kick masks for `(m = 512, r = 64)`. -/
def rkmMasksHi_m512_r64 : List (List Bool) := [
  rkmMkHi_m512_r64_s0, rkmMkHi_m512_r64_s1, rkmMkHi_m512_r64_s2, []
  ]
/-- Part 0 of `rkmRowHi_m512_r64`. -/
def rkmRowHi_m512_r64_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Part 1 of `rkmRowHi_m512_r64`. -/
def rkmRowHi_m512_r64_p1 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 208, 454, 626, 123839, 3577963, 43138, 102880610,
  2581789, 2658421580, 997232365015
  ]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 64)`. -/
def rkmRowHi_m512_r64 : List ℕ := rkmRowHi_m512_r64_p0 ++ rkmRowHi_m512_r64_p1
/-- Part 0 of `rkmMkHi_m512_r128_s0`. -/
def rkmMkHi_m512_r128_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 1 of `rkmMkHi_m512_r128_s0`. -/
def rkmMkHi_m512_r128_s0_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 2 of `rkmMkHi_m512_r128_s0`. -/
def rkmMkHi_m512_r128_s0_p2 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, false, false, true, true, false, false, true, false,
  false, true, true, true, true, true, true
  ]
/-- Mask segment 0 for `(m = 512, r = 128)`. -/
def rkmMkHi_m512_r128_s0 : List Bool :=
  rkmMkHi_m512_r128_s0_p0 ++ (rkmMkHi_m512_r128_s0_p1 ++ rkmMkHi_m512_r128_s0_p2)
/-- Part 0 of `rkmMkHi_m512_r128_s1`. -/
def rkmMkHi_m512_r128_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 1 of `rkmMkHi_m512_r128_s1`. -/
def rkmMkHi_m512_r128_s1_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 2 of `rkmMkHi_m512_r128_s1`. -/
def rkmMkHi_m512_r128_s1_p2 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, true, false, true, false, false, true, false, false, true, true
  ]
/-- Mask segment 1 for `(m = 512, r = 128)`. -/
def rkmMkHi_m512_r128_s1 : List Bool :=
  rkmMkHi_m512_r128_s1_p0 ++ (rkmMkHi_m512_r128_s1_p1 ++ rkmMkHi_m512_r128_s1_p2)
/-- Part 0 of `rkmMkHi_m512_r128_s2`. -/
def rkmMkHi_m512_r128_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 1 of `rkmMkHi_m512_r128_s2`. -/
def rkmMkHi_m512_r128_s2_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false
  ]
/-- Part 2 of `rkmMkHi_m512_r128_s2`. -/
def rkmMkHi_m512_r128_s2_p2 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true
  ]
/-- Mask segment 2 for `(m = 512, r = 128)`. -/
def rkmMkHi_m512_r128_s2 : List Bool :=
  rkmMkHi_m512_r128_s2_p0 ++ (rkmMkHi_m512_r128_s2_p1 ++ rkmMkHi_m512_r128_s2_p2)
/-- Prefix-kick masks for `(m = 512, r = 128)`. -/
def rkmMasksHi_m512_r128 : List (List Bool) := [
  rkmMkHi_m512_r128_s0, rkmMkHi_m512_r128_s1, rkmMkHi_m512_r128_s2, []
  ]
/-- Part 0 of `rkmRowHi_m512_r128`. -/
def rkmRowHi_m512_r128_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Part 1 of `rkmRowHi_m512_r128`. -/
def rkmRowHi_m512_r128_p1 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Part 2 of `rkmRowHi_m512_r128`. -/
def rkmRowHi_m512_r128_p2 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 19,
  45, 21, 26, 25, 429, 239, 15351, 1131, 6329187
  ]
/-- Part 3 of `rkmRowHi_m512_r128`. -/
def rkmRowHi_m512_r128_p3 : List ℕ := [
  666538, 4772417, 26324095, 2844358, 558559198, 27435271, 1444294420, 997928739268
  ]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 128)`. -/
def rkmRowHi_m512_r128 : List ℕ :=
  rkmRowHi_m512_r128_p0 ++ (rkmRowHi_m512_r128_p1 ++ (rkmRowHi_m512_r128_p2
  ++ rkmRowHi_m512_r128_p3))

/-- Active anchor chunk `0` (`m = 512`). -/
def rkmAncPHi_m512_p0 : List RampKickAnchor := [
  ⟨3, [1, 1, 1, 1],
    [19739112, 10637785, 614027, 743963],
    [3, 2, 1, 1], rkmMasksHi_m512_r3, rkmRowHi_m512_r3⟩,
  ⟨4, [1], [32527969], [6], rkmMasksHi_m512_r4, rkmRowHi_m512_r4⟩,
  ⟨5, [1, 1, 1], [11554224, 13861365, 7586665], [4, 4, 3], rkmMasksHi_m512_r5, rkmRowHi_m512_r5⟩,
  ⟨6, [1, 1, 1], [21160335, 7497533, 4662805], [6, 3, 2], rkmMasksHi_m512_r6, rkmRowHi_m512_r6⟩,
  ⟨7, [1], [33551342], [10], rkmMasksHi_m512_r7, rkmRowHi_m512_r7⟩,
  ⟨8, [1], [33727744], [10], rkmMasksHi_m512_r8, rkmRowHi_m512_r8⟩,
  ⟨9, [1, 1, 1, 1, 1, 1, 1, 1],
    [15015400, 14825905, 1342316, 939621, 671158, 155310, 424679, 493863],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r9, rkmRowHi_m512_r9⟩,
  ⟨10, [1, 1, 1, 1, 1, 1, 1, 1],
    [15073419, 14883429, 1342316, 939621, 671158, 80910, 411979, 580963],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r10, rkmRowHi_m512_r10⟩,
  ⟨11, [1, 1, 1, 1, 1, 1, 1, 1],
    [15051402, 14942928, 1402316, 939621, 373658, 288410, 424979, 657963],
    [9, 9, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r11, rkmRowHi_m512_r11⟩
  ]
/-- Active anchor chunk `1` (`m = 512`). -/
def rkmAncPHi_m512_p1 : List RampKickAnchor := [
  ⟨12, [1, 1, 1, 1, 1, 1],
    [14318018, 15806645, 924024, 2019001, 755767, 341846],
    [10, 10, 1, 1, 1, 1], rkmMasksHi_m512_r12, rkmRowHi_m512_r12⟩,
  ⟨13, [1, 1, 1, 1, 1, 1, 1, 1],
    [14903233, 15239249, 1400281, 1195634, 687403, 390909, 202168, 220102],
    [9, 10, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r13, rkmRowHi_m512_r13⟩,
  ⟨14, [1, 1, 1, 1, 1, 1, 1, 1],
    [14966328, 15241747, 1400281, 1159634, 675803, 407109, 239376, 214301],
    [9, 10, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r14, rkmRowHi_m512_r14⟩,
  ⟨15, [1, 1, 1], [33499890, 798682, 65461], [18, 2, 2], rkmMasksHi_m512_r15, rkmRowHi_m512_r15⟩,
  ⟨16, [1, 1, 1, 1],
    [33478996, 425796, 426052, 87375],
    [18, 1, 1, 1], rkmMasksHi_m512_r16, rkmRowHi_m512_r16⟩,
  ⟨17, [1, 1, 1], [33534814, 820478, 112798], [19, 2, 2], rkmMasksHi_m512_r17, rkmRowHi_m512_r17⟩,
  ⟨18, [1, 1, 1, 1, 1, 1, 1, 1],
    [15191245, 15182154, 1385383, 1092635, 638903, 448309, 446375, 129498],
    [12, 12, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r18, rkmRowHi_m512_r18⟩,
  ⟨19, [1, 1, 1, 1, 1, 1, 1, 1],
    [15236562, 15180858, 1084787, 1361635, 643403, 448510, 454646, 147519],
    [12, 12, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r19, rkmRowHi_m512_r19⟩,
  ⟨20, [1, 1, 1, 1, 1, 1, 1, 1],
    [15251576, 15611675, 1025129, 1002981, 630270, 457399, 456014, 163786],
    [13, 13, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r20, rkmRowHi_m512_r20⟩
  ]
/-- Active anchor chunk `2` (`m = 512`). -/
def rkmAncPHi_m512_p2 : List RampKickAnchor := [
  ⟨21, [1, 1, 1],
    [33255192, 1198598, 183763],
    [24, 2, 2], rkmMasksHi_m512_r21, rkmRowHi_m512_r21⟩,
  ⟨22, [1, 1, 1, 1, 1, 1, 1, 1],
    [14970143, 15839963, 1094691, 1025144, 659013, 400136, 484014, 201692],
    [14, 14, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r22, rkmRowHi_m512_r22⟩,
  ⟨23, [1, 1, 1, 1, 1, 1, 1, 1],
    [15073135, 15771434, 1095167, 997144, 640113, 446236, 481434, 205194],
    [14, 14, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r23, rkmRowHi_m512_r23⟩,
  ⟨24, [1, 1, 1, 1, 1, 1, 1, 1],
    [15119169, 15757063, 1097717, 982494, 636963, 446862, 486684, 216848],
    [14, 14, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r24, rkmRowHi_m512_r24⟩,
  ⟨25, [1, 1, 1, 1, 1, 1, 1, 1],
    [15404796, 15503689, 1098863, 961544, 640293, 447991, 491734, 227619],
    [14, 14, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r25, rkmRowHi_m512_r25⟩,
  ⟨26, [1, 1, 1, 1, 1, 1, 1, 1],
    [15501420, 15378609, 1099458, 997543, 673692, 437315, 483030, 237123],
    [14, 14, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r26, rkmRowHi_m512_r26⟩,
  ⟨27, [1, 1, 1, 1, 1, 1, 1, 1],
    [15559051, 15290263, 1101589, 1038469, 671318, 430840, 500500, 246873],
    [14, 14, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r27, rkmRowHi_m512_r27⟩,
  ⟨28, [1, 1, 1, 1, 1, 1, 1, 1],
    [15466109, 15412537, 1041563, 1088563, 676888, 438310, 489806, 255003],
    [14, 14, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r28, rkmRowHi_m512_r28⟩,
  ⟨29, [1, 1, 1, 1, 1, 1, 1, 1],
    [15393350, 15453764, 1089390, 1089090, 677243, 439185, 492805, 263081],
    [14, 14, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r29, rkmRowHi_m512_r29⟩
  ]
/-- Active anchor chunk `3` (`m = 512`). -/
def rkmAncPHi_m512_p3 : List RampKickAnchor := [
  ⟨30, [1, 1, 1, 1],
    [33407023, 1193985, 179705, 145678],
    [33, 3, 2, 2], rkmMasksHi_m512_r30, rkmRowHi_m512_r30⟩,
  ⟨31, [1, 1, 1, 1],
    [33423223, 1204626, 190246, 136153],
    [33, 3, 2, 2], rkmMasksHi_m512_r31, rkmRowHi_m512_r31⟩,
  ⟨32, [1, 1, 1, 1, 1, 1, 1, 1],
    [16339437, 16180995, 886424, 757804, 264667, 203767, 168165, 180458],
    [18, 18, 1, 1, 1, 1, 1, 1], rkmMasksHi_m512_r32, rkmRowHi_m512_r32⟩,
  ⟨64, [1, 1, 1, 1],
    [34000000, 1296000, 350000, 92000],
    [71, 3, 1, 1], rkmMasksHi_m512_r64, rkmRowHi_m512_r64⟩,
  ⟨128, [1, 1, 1, 1],
    [35200000, 1491000, 408000, 118400],
    [140, 6, 2, 1], rkmMasksHi_m512_r128, rkmRowHi_m512_r128⟩,
  ⟨256, [1, 1, 1, 1, 1, 1, 1, 1],
    [18868489, 19077700, 1157373, 620037, 402095, 360075, 458539, 129773],
    [129, 130, 8, 5, 3, 3, 4, 1], rkmMasksHi_m512_r256, rkmRowHi_m512_r256⟩,
  ⟨512, [1, 1, 2, 2, 2, 2, 2, 2],
    [9717284, 11527715, 6267864, 6269338, 723800, 1130188, 369302, 541020],
    [116, 138, 121, 121, 14, 22, 8, 11], rkmMasksHi_m512_r512, rkmRowHi_m512_r512⟩
  ]
/-- Sorted active multi-segment anchors (`m = 512, kMax = 512`). -/
def rkmAnchorsHi_m512 : List RampKickAnchor :=
  rkmAncPHi_m512_p0 ++ (rkmAncPHi_m512_p1 ++ (rkmAncPHi_m512_p2 ++ rkmAncPHi_m512_p3))

end

public section
/-- Inlined Step-1 hybrid trajectory row certificate `(m = 512, r = 64)`. -/
theorem rkmTrajHi_m512_r64 :
    rkmLo12EqHi 512 16 64 [1, 1, 1, 1]
      [34000000, 1296000, 350000, 92000]
      [71, 3, 1, 1] rkmMasksHi_m512_r64 rkmRowHi_m512_r64 :=
  rkmCertUltraRow ((by decide +kernel :
    muxNatListEq (rkmEvalT16UltraLo12 512 16 64 [1, 1, 1, 1]
      [34000000, 1296000, 350000, 92000]
      [71, 3, 1, 1] rkmMasksHi_m512_r64) rkmRowHi_m512_r64 = true))
/-- Inlined Step-1 hybrid trajectory row certificate `(m = 512, r = 128)`. -/
theorem rkmTrajHi_m512_r128 :
    rkmLo12EqHi 512 16 128 [1, 1, 1, 1]
      [35200000, 1491000, 408000, 118400]
      [140, 6, 2, 1] rkmMasksHi_m512_r128 rkmRowHi_m512_r128 :=
  rkmCertUltraRow ((by decide +kernel :
    muxNatListEq (rkmEvalT16UltraLo12 512 16 128 [1, 1, 1, 1]
      [35200000, 1491000, 408000, 118400]
      [140, 6, 2, 1] rkmMasksHi_m512_r128) rkmRowHi_m512_r128 = true))

private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private theorem rkmTl4 {a b c d : Bool} {bs : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: bs) = true) : rkmAllTrueF bs = true :=
  rkmTl (rkmTl (rkmTl (rkmTl h)))
private theorem rkmTl16 {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 : Bool}
    {bs : List Bool}
    (h : rkmAllTrueF (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 ::
      a8 :: a9 :: a10 :: a11 :: a12 :: a13 :: a14 :: a15 :: bs) = true) :
    rkmAllTrueF bs = true :=
  rkmTl4 (rkmTl4 (rkmTl4 (rkmTl4 h)))
private theorem rkmDim257 :
    Nat.add (highdNatMin (Nat.mul 1 512) 256) 1 = 257 := rfl
private theorem rkmDim513_l1 :
    Nat.add (highdNatMin (Nat.mul 1 512) 512) 1 = 513 := rfl
private theorem rkmDim513_l2 :
    Nat.add (highdNatMin (Nat.mul 2 512) 512) 1 = 513 := rfl
private theorem rkmStitchEqOkHi_m512 : rkmAllTrueF [
    muxIntListEq rkmHbHi_m512_r512_s0_c0 rkmHbHi_m512_r512_s0_c1,
    muxIntListEq rkmVoHi_m512_r512_s0_c0 rkmViHi_m512_r512_s0_c1,
    muxIntListEq rkmHbHi_m512_r512_s1_c0 rkmHbHi_m512_r512_s1_c1,
    muxIntListEq rkmVoHi_m512_r512_s1_c0 rkmViHi_m512_r512_s1_c1,
    muxIntListEq rkmHbHi_m512_r512_s2_c0 rkmHbHi_m512_r512_s2_c1,
    muxIntListEq rkmVoHi_m512_r512_s2_c0 rkmViHi_m512_r512_s2_c1,
    muxIntListEq rkmHbHi_m512_r512_s3_c0 rkmHbHi_m512_r512_s3_c1,
    muxIntListEq rkmVoHi_m512_r512_s3_c0 rkmViHi_m512_r512_s3_c1
  ] = true := by decide +kernel
private theorem rkmRowChkOkHi_m512_r256 :
    rkmCheckRowFromWalks 512 16 256 [1, 1, 1, 1, 1, 1, 1, 1]
      [18868489, 19077700, 1157373, 620037, 402095, 360075, 458539, 129773]
      [129, 130, 8, 5, 3, 3, 4, 1] rkmMasksHi_m512_r256
      rkmWalksHi_m512_r256 rkmRowHi_m512_r256 = true := by decide +kernel
private theorem rkmRowChkOkHi_m512_r512 :
    rkmCheckRowFromWalks 512 16 512 [1, 1, 2, 2, 2, 2, 2, 2]
      [9717284, 11527715, 6267864, 6269338, 723800, 1130188, 369302, 541020]
      [116, 138, 121, 121, 14, 22, 8, 11] rkmMasksHi_m512_r512
      rkmWalksHi_m512_r512 rkmRowHi_m512_r512 = true := by decide +kernel
private theorem rkmSegSndHi_m512_r256_s0 :
    muxFastIterFullT16 129 (Nat.add (highdNatMin (Nat.mul 1 512) 256) 1)
      rkmHbHi_m512_r256_s0_c0 rkmViHi_m512_r256_s0_c0 = rkmVoHi_m512_r256_s0_c0 := by
  rw [rkmDim257]; exact rkmWalkChkHi_m512_r256_s0_c0
private theorem rkmSegSndHi_m512_r256_s1 :
    muxFastIterFullT16 130 (Nat.add (highdNatMin (Nat.mul 1 512) 256) 1)
      rkmHbHi_m512_r256_s1_c0 rkmViHi_m512_r256_s1_c0 = rkmVoHi_m512_r256_s1_c0 := by
  rw [rkmDim257]; exact rkmWalkChkHi_m512_r256_s1_c0
private theorem rkmSegSndHi_m512_r256_s2 :
    muxFastIterFullT16 8 (Nat.add (highdNatMin (Nat.mul 1 512) 256) 1)
      rkmHbHi_m512_r256_s2_c0 rkmViHi_m512_r256_s2_c0 = rkmVoHi_m512_r256_s2_c0 := by
  rw [rkmDim257]; exact rkmWalkChkHi_m512_r256_s2_c0
private theorem rkmSegSndHi_m512_r256_s3 :
    muxFastIterFullT16 5 (Nat.add (highdNatMin (Nat.mul 1 512) 256) 1)
      rkmHbHi_m512_r256_s3_c0 rkmViHi_m512_r256_s3_c0 = rkmVoHi_m512_r256_s3_c0 := by
  rw [rkmDim257]; exact rkmWalkChkHi_m512_r256_s3_c0
private theorem rkmSegSndHi_m512_r256_s4 :
    muxFastIterFullT16 3 (Nat.add (highdNatMin (Nat.mul 1 512) 256) 1)
      rkmHbHi_m512_r256_s4_c0 rkmViHi_m512_r256_s4_c0 = rkmVoHi_m512_r256_s4_c0 := by
  rw [rkmDim257]; exact rkmWalkChkHi_m512_r256_s4_c0
private theorem rkmSegSndHi_m512_r256_s5 :
    muxFastIterFullT16 3 (Nat.add (highdNatMin (Nat.mul 1 512) 256) 1)
      rkmHbHi_m512_r256_s5_c0 rkmViHi_m512_r256_s5_c0 = rkmVoHi_m512_r256_s5_c0 := by
  rw [rkmDim257]; exact rkmWalkChkHi_m512_r256_s5_c0
private theorem rkmSegSndHi_m512_r256_s6 :
    muxFastIterFullT16 4 (Nat.add (highdNatMin (Nat.mul 1 512) 256) 1)
      rkmHbHi_m512_r256_s6_c0 rkmViHi_m512_r256_s6_c0 = rkmVoHi_m512_r256_s6_c0 := by
  rw [rkmDim257]; exact rkmWalkChkHi_m512_r256_s6_c0
private theorem rkmSegSndHi_m512_r256_s7 :
    muxFastIterFullT16 1 (Nat.add (highdNatMin (Nat.mul 1 512) 256) 1)
      rkmHbHi_m512_r256_s7_c0 rkmViHi_m512_r256_s7_c0 = rkmVoHi_m512_r256_s7_c0 := by
  rw [rkmDim257]; exact rkmWalkChkHi_m512_r256_s7_c0
private theorem rkmWalksSndHi_m512_r256 :
    RkmSegWalksSound 512 256 [1, 1, 1, 1, 1, 1, 1, 1] [129, 130, 8, 5, 3, 3, 4, 1]
      rkmWalksHi_m512_r256 := by
  dsimp only [RkmSegWalksSound, rkmWalksHi_m512_r256]
  exact ⟨rkmSegSndHi_m512_r256_s0, ⟨rkmSegSndHi_m512_r256_s1,
    ⟨rkmSegSndHi_m512_r256_s2, ⟨rkmSegSndHi_m512_r256_s3,
    ⟨rkmSegSndHi_m512_r256_s4, ⟨rkmSegSndHi_m512_r256_s5,
    ⟨rkmSegSndHi_m512_r256_s6, ⟨rkmSegSndHi_m512_r256_s7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 512, r = 256)`. -/
theorem rkmTrajHi_m512_r256 :
    rkmLo12EqHi 512 16 256 [1, 1, 1, 1, 1, 1, 1, 1]
      [18868489, 19077700, 1157373, 620037, 402095, 360075, 458539, 129773]
      [129, 130, 8, 5, 3, 3, 4, 1] rkmMasksHi_m512_r256 rkmRowHi_m512_r256 :=
  rkmCheckRowFromWalks_sound rkmWalksSndHi_m512_r256 rkmRowChkOkHi_m512_r256
private theorem rkmSegChainHi_m512_r512_s0_u1 : muxFastIterFullT16 116 513
    rkmHbHi_m512_r512_s0_c0 rkmViHi_m512_r512_s0_c0 = rkmVoHi_m512_r512_s0_c1 :=
  rkmChainFastIterT16 rfl (rkmHd rkmStitchEqOkHi_m512)
    (rkmHd (rkmTl rkmStitchEqOkHi_m512))
    rkmWalkChkHi_m512_r512_s0_c0 rkmWalkChkHi_m512_r512_s0_c1
private theorem rkmSegSndHi_m512_r512_s0 :
    muxFastIterFullT16 116 (Nat.add (highdNatMin (Nat.mul 1 512) 512) 1)
      rkmHbHi_m512_r512_s0_c0 rkmViHi_m512_r512_s0_c0 = rkmVoHi_m512_r512_s0_c1 := by
  rw [rkmDim513_l1]; exact rkmSegChainHi_m512_r512_s0_u1
private theorem rkmSegChainHi_m512_r512_s1_u1 : muxFastIterFullT16 138 513
    rkmHbHi_m512_r512_s1_c0 rkmViHi_m512_r512_s1_c0 = rkmVoHi_m512_r512_s1_c1 :=
  rkmChainFastIterT16 rfl (rkmHd (rkmTl (rkmTl rkmStitchEqOkHi_m512)))
    (rkmHd (rkmTl (rkmTl (rkmTl rkmStitchEqOkHi_m512))))
    rkmWalkChkHi_m512_r512_s1_c0 rkmWalkChkHi_m512_r512_s1_c1
private theorem rkmSegSndHi_m512_r512_s1 :
    muxFastIterFullT16 138 (Nat.add (highdNatMin (Nat.mul 1 512) 512) 1)
      rkmHbHi_m512_r512_s1_c0 rkmViHi_m512_r512_s1_c0 = rkmVoHi_m512_r512_s1_c1 := by
  rw [rkmDim513_l1]; exact rkmSegChainHi_m512_r512_s1_u1
private theorem rkmSegChainHi_m512_r512_s2_u1 : muxFastIterFullT16 121 513
    rkmHbHi_m512_r512_s2_c0 rkmViHi_m512_r512_s2_c0 = rkmVoHi_m512_r512_s2_c1 :=
  rkmChainFastIterT16 rfl (rkmHd (rkmTl4 rkmStitchEqOkHi_m512))
    (rkmHd (rkmTl (rkmTl4 rkmStitchEqOkHi_m512)))
    rkmWalkChkHi_m512_r512_s2_c0 rkmWalkChkHi_m512_r512_s2_c1
private theorem rkmSegSndHi_m512_r512_s2 :
    muxFastIterFullT16 121 (Nat.add (highdNatMin (Nat.mul 2 512) 512) 1)
      rkmHbHi_m512_r512_s2_c0 rkmViHi_m512_r512_s2_c0 = rkmVoHi_m512_r512_s2_c1 := by
  rw [rkmDim513_l2]; exact rkmSegChainHi_m512_r512_s2_u1
private theorem rkmSegChainHi_m512_r512_s3_u1 : muxFastIterFullT16 121 513
    rkmHbHi_m512_r512_s3_c0 rkmViHi_m512_r512_s3_c0 = rkmVoHi_m512_r512_s3_c1 :=
  rkmChainFastIterT16 rfl (rkmHd (rkmTl (rkmTl (rkmTl4 rkmStitchEqOkHi_m512))))
    (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 rkmStitchEqOkHi_m512)))))
    rkmWalkChkHi_m512_r512_s3_c0 rkmWalkChkHi_m512_r512_s3_c1
private theorem rkmSegSndHi_m512_r512_s3 :
    muxFastIterFullT16 121 (Nat.add (highdNatMin (Nat.mul 2 512) 512) 1)
      rkmHbHi_m512_r512_s3_c0 rkmViHi_m512_r512_s3_c0 = rkmVoHi_m512_r512_s3_c1 := by
  rw [rkmDim513_l2]; exact rkmSegChainHi_m512_r512_s3_u1
private theorem rkmSegSndHi_m512_r512_s4 :
    muxFastIterFullT16 14 (Nat.add (highdNatMin (Nat.mul 2 512) 512) 1)
      rkmHbHi_m512_r512_s4_c0 rkmViHi_m512_r512_s4_c0 = rkmVoHi_m512_r512_s4_c0 := by
  rw [rkmDim513_l2]; exact rkmWalkChkHi_m512_r512_s4_c0
private theorem rkmSegSndHi_m512_r512_s5 :
    muxFastIterFullT16 22 (Nat.add (highdNatMin (Nat.mul 2 512) 512) 1)
      rkmHbHi_m512_r512_s5_c0 rkmViHi_m512_r512_s5_c0 = rkmVoHi_m512_r512_s5_c0 := by
  rw [rkmDim513_l2]; exact rkmWalkChkHi_m512_r512_s5_c0
private theorem rkmSegSndHi_m512_r512_s6 :
    muxFastIterFullT16 8 (Nat.add (highdNatMin (Nat.mul 2 512) 512) 1)
      rkmHbHi_m512_r512_s6_c0 rkmViHi_m512_r512_s6_c0 = rkmVoHi_m512_r512_s6_c0 := by
  rw [rkmDim513_l2]; exact rkmWalkChkHi_m512_r512_s6_c0
private theorem rkmSegSndHi_m512_r512_s7 :
    muxFastIterFullT16 11 (Nat.add (highdNatMin (Nat.mul 2 512) 512) 1)
      rkmHbHi_m512_r512_s7_c0 rkmViHi_m512_r512_s7_c0 = rkmVoHi_m512_r512_s7_c0 := by
  rw [rkmDim513_l2]; exact rkmWalkChkHi_m512_r512_s7_c0
private theorem rkmWalksSndHi_m512_r512 :
    RkmSegWalksSound 512 512 [1, 1, 2, 2, 2, 2, 2, 2] [116, 138, 121, 121, 14, 22, 8, 11]
      rkmWalksHi_m512_r512 := by
  dsimp only [RkmSegWalksSound, rkmWalksHi_m512_r512]
  exact ⟨rkmSegSndHi_m512_r512_s0, ⟨rkmSegSndHi_m512_r512_s1,
    ⟨rkmSegSndHi_m512_r512_s2, ⟨rkmSegSndHi_m512_r512_s3,
    ⟨rkmSegSndHi_m512_r512_s4, ⟨rkmSegSndHi_m512_r512_s5,
    ⟨rkmSegSndHi_m512_r512_s6, ⟨rkmSegSndHi_m512_r512_s7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 512, r = 512)`. -/
theorem rkmTrajHi_m512_r512 :
    rkmLo12EqHi 512 16 512 [1, 1, 2, 2, 2, 2, 2, 2]
      [9717284, 11527715, 6267864, 6269338, 723800, 1130188, 369302, 541020]
      [116, 138, 121, 121, 14, 22, 8, 11] rkmMasksHi_m512_r512 rkmRowHi_m512_r512 :=
  rkmCheckRowFromWalks_sound rkmWalksSndHi_m512_r512 rkmRowChkOkHi_m512_r512
private theorem rkm_anc_app_hi_512 {m0 lMax : ℕ} :
    ∀ {xs ys : List RampKickAnchor},
      RampKickAnchorsSound m0 lMax xs → RampKickAnchorsSound m0 lMax ys →
      RampKickAnchorsSound m0 lMax (xs ++ ys)
  | [], _, _, hy => hy
  | _ :: _, _, ⟨hx0, hxs⟩, hy => ⟨hx0, rkm_anc_app_hi_512 hxs hy⟩
private theorem rkmAncSndPHi_m512_p0 : RampKickAnchorsSound 512 16 rkmAncPHi_m512_p0 :=
  ⟨rkmTrajHi_m512_r3, ⟨rkmTrajHi_m512_r4, ⟨rkmTrajHi_m512_r5, ⟨rkmTrajHi_m512_r6,
  ⟨rkmTrajHi_m512_r7, ⟨rkmTrajHi_m512_r8, ⟨rkmTrajHi_m512_r9, ⟨rkmTrajHi_m512_r10,
  ⟨rkmTrajHi_m512_r11, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m512_p1 : RampKickAnchorsSound 512 16 rkmAncPHi_m512_p1 :=
  ⟨rkmTrajHi_m512_r12, ⟨rkmTrajHi_m512_r13, ⟨rkmTrajHi_m512_r14, ⟨rkmTrajHi_m512_r15,
  ⟨rkmTrajHi_m512_r16, ⟨rkmTrajHi_m512_r17, ⟨rkmTrajHi_m512_r18, ⟨rkmTrajHi_m512_r19,
  ⟨rkmTrajHi_m512_r20, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m512_p2 : RampKickAnchorsSound 512 16 rkmAncPHi_m512_p2 :=
  ⟨rkmTrajHi_m512_r21, ⟨rkmTrajHi_m512_r22, ⟨rkmTrajHi_m512_r23, ⟨rkmTrajHi_m512_r24,
  ⟨rkmTrajHi_m512_r25, ⟨rkmTrajHi_m512_r26, ⟨rkmTrajHi_m512_r27, ⟨rkmTrajHi_m512_r28,
  ⟨rkmTrajHi_m512_r29, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩
private theorem rkmAncSndPHi_m512_p3 : RampKickAnchorsSound 512 16 rkmAncPHi_m512_p3 :=
  ⟨rkmTrajHi_m512_r30, ⟨rkmTrajHi_m512_r31, ⟨rkmTrajHi_m512_r32, ⟨rkmTrajHi_m512_r64,
  ⟨rkmTrajHi_m512_r128, ⟨rkmTrajHi_m512_r256, ⟨rkmTrajHi_m512_r512, trivial⟩⟩⟩⟩⟩⟩⟩
/-- Anchor trajectory soundness bundle (`m = 512, kMax = 512`). -/
theorem rkmAnchorsSoundHi_m512 : RampKickAnchorsSound 512 16 rkmAnchorsHi_m512 :=
  rkm_anc_app_hi_512 rkmAncSndPHi_m512_p0 (rkm_anc_app_hi_512 rkmAncSndPHi_m512_p1
    (rkm_anc_app_hi_512 rkmAncSndPHi_m512_p2 (rkmAncSndPHi_m512_p3)))
/-- Kernel Bellman table verification (`m = 512, kMax = 512`). -/
theorem rkmTableOkHi_m512 :
    rkmCheckTable 512 512 16 true rkmVPotHi_m512 rkmAnchorsHi_m512 = true := by
  decide +kernel
/-- Unpacked `RampKickTableValid` bundle (`m = 512, kMax = 512`). -/
theorem rkmValidHi_m512 :
    RampKickTableValid 512 512 16 true rkmVPotHi_m512 rkmAnchorsHi_m512 :=
  rkmCheckTable_sound rkmTableOkHi_m512 rkmAnchorsSoundHi_m512
private theorem rkmBoundsAllOkHi_m512 : rkmAllTrueF [
    rkmCheckAnchorsLMax 2 1 rkmAnchorsHi_m512,
    rkmCheckAnchorsLMax 2 2 rkmAnchorsHi_m512,
    checkAltBound12 512 2 (rkmVPotHi_m512.getD 2 0) 255922289023 500000000000,
    rkmCheckAnchorsLMax 4 1 rkmAnchorsHi_m512,
    rkmCheckAnchorsLMax 4 2 rkmAnchorsHi_m512,
    checkAltBound12 512 4 (rkmVPotHi_m512.getD 4 0) 43539968951 125000000000,
    rkmCheckAnchorsLMax 8 1 rkmAnchorsHi_m512,
    rkmCheckAnchorsLMax 8 2 rkmAnchorsHi_m512,
    checkAltBound12 512 8 (rkmVPotHi_m512.getD 8 0) 225952548419 1000000000000,
    rkmCheckAnchorsLMax 16 1 rkmAnchorsHi_m512,
    rkmCheckAnchorsLMax 16 2 rkmAnchorsHi_m512,
    checkAltBound12 512 16 (rkmVPotHi_m512.getD 16 0) 30001403651 200000000000,
    rkmCheckAnchorsLMax 32 1 rkmAnchorsHi_m512,
    rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m512,
    checkAltBound12 512 32 (rkmVPotHi_m512.getD 32 0) 25448093779 250000000000,
    rkmCheckAnchorsLMax 64 1 rkmAnchorsHi_m512,
    rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m512,
    checkAltBound12 512 64 (rkmVPotHi_m512.getD 64 0) 70667825813 1000000000000,
    rkmCheckAnchorsLMax 128 1 rkmAnchorsHi_m512,
    rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m512,
    checkAltBound12 512 128 (rkmVPotHi_m512.getD 128 0) 2531723681 50000000000,
    rkmCheckAnchorsLMax 256 1 rkmAnchorsHi_m512,
    rkmCheckAnchorsLMax 256 2 rkmAnchorsHi_m512,
    checkAltBound12 512 256 (rkmVPotHi_m512.getD 256 0) 19387951311 500000000000,
    rkmCheckAnchorsLMax 512 2 rkmAnchorsHi_m512,
    checkAltBound12 512 512 (rkmVPotHi_m512.getD 512 0) 17133448611 500000000000
  ] = true := by decide +kernel
/-- Cell `lMax = 1` bound for `(512, 2)`. -/
theorem rkmCellLMaxHi_m512_k2 :
    rkmCheckAnchorsLMax 2 1 rkmAnchorsHi_m512 = true :=
  (rkmHd rkmBoundsAllOkHi_m512)
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(512, 2)`. -/
theorem rkmCellLMax2Hi_m512_k2 :
    rkmCheckAnchorsLMax 2 2 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl rkmBoundsAllOkHi_m512))
/-- Relative-cost certificate `255922289023 / 500000000000` for `(512, 2)`. -/
theorem rkmBoundHi_m512_k2 :
    checkAltBound12 512 2 (rkmVPotHi_m512.getD 2 0) 255922289023 500000000000 = true :=
  (rkmHd (rkmTl (rkmTl rkmBoundsAllOkHi_m512)))
/-- Cell `lMax = 1` bound for `(512, 4)`. -/
theorem rkmCellLMaxHi_m512_k4 :
    rkmCheckAnchorsLMax 4 1 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl (rkmTl (rkmTl rkmBoundsAllOkHi_m512))))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(512, 4)`. -/
theorem rkmCellLMax2Hi_m512_k4 :
    rkmCheckAnchorsLMax 4 2 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl4 rkmBoundsAllOkHi_m512))
/-- Relative-cost certificate `43539968951 / 125000000000` for `(512, 4)`. -/
theorem rkmBoundHi_m512_k4 :
    checkAltBound12 512 4 (rkmVPotHi_m512.getD 4 0) 43539968951 125000000000 = true :=
  (rkmHd (rkmTl (rkmTl4 rkmBoundsAllOkHi_m512)))
/-- Cell `lMax = 1` bound for `(512, 8)`. -/
theorem rkmCellLMaxHi_m512_k8 :
    rkmCheckAnchorsLMax 8 1 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl (rkmTl (rkmTl4 rkmBoundsAllOkHi_m512))))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(512, 8)`. -/
theorem rkmCellLMax2Hi_m512_k8 :
    rkmCheckAnchorsLMax 8 2 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 rkmBoundsAllOkHi_m512)))))
/-- Relative-cost certificate `225952548419 / 1000000000000` for `(512, 8)`. -/
theorem rkmBoundHi_m512_k8 :
    checkAltBound12 512 8 (rkmVPotHi_m512.getD 8 0) 225952548419 1000000000000 = true :=
  (rkmHd (rkmTl4 (rkmTl4 rkmBoundsAllOkHi_m512)))
/-- Cell `lMax = 1` bound for `(512, 16)`. -/
theorem rkmCellLMaxHi_m512_k16 :
    rkmCheckAnchorsLMax 16 1 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl (rkmTl4 (rkmTl4 rkmBoundsAllOkHi_m512))))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(512, 16)`. -/
theorem rkmCellLMax2Hi_m512_k16 :
    rkmCheckAnchorsLMax 16 2 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 rkmBoundsAllOkHi_m512)))))
/-- Relative-cost certificate `30001403651 / 200000000000` for `(512, 16)`. -/
theorem rkmBoundHi_m512_k16 :
    checkAltBound12 512 16 (rkmVPotHi_m512.getD 16 0) 30001403651 200000000000 = true :=
  (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 rkmBoundsAllOkHi_m512))))))
/-- Cell `lMax = 1` bound for `(512, 32)`. -/
theorem rkmCellLMaxHi_m512_k32 :
    rkmCheckAnchorsLMax 32 1 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl4 (rkmTl4 (rkmTl4 rkmBoundsAllOkHi_m512))))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(512, 32)`. -/
theorem rkmCellLMax2Hi_m512_k32 :
    rkmCheckAnchorsLMax 32 2 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 rkmBoundsAllOkHi_m512)))))
/-- Relative-cost certificate `25448093779 / 250000000000` for `(512, 32)`. -/
theorem rkmBoundHi_m512_k32 :
    checkAltBound12 512 32 (rkmVPotHi_m512.getD 32 0) 25448093779 250000000000 = true :=
  (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 rkmBoundsAllOkHi_m512))))))
/-- Cell `lMax = 1` bound for `(512, 64)`. -/
theorem rkmCellLMaxHi_m512_k64 :
    rkmCheckAnchorsLMax 64 1 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl4 (rkmTl4 rkmBoundsAllOkHi_m512)))))))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(512, 64)`. -/
theorem rkmCellLMax2Hi_m512_k64 :
    rkmCheckAnchorsLMax 64 2 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl16 rkmBoundsAllOkHi_m512))
/-- Relative-cost certificate `70667825813 / 1000000000000` for `(512, 64)`. -/
theorem rkmBoundHi_m512_k64 :
    checkAltBound12 512 64 (rkmVPotHi_m512.getD 64 0) 70667825813 1000000000000 = true :=
  (rkmHd (rkmTl (rkmTl16 rkmBoundsAllOkHi_m512)))
/-- Cell `lMax = 1` bound for `(512, 128)`. -/
theorem rkmCellLMaxHi_m512_k128 :
    rkmCheckAnchorsLMax 128 1 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl (rkmTl (rkmTl16 rkmBoundsAllOkHi_m512))))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(512, 128)`. -/
theorem rkmCellLMax2Hi_m512_k128 :
    rkmCheckAnchorsLMax 128 2 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl16 rkmBoundsAllOkHi_m512)))))
/-- Relative-cost certificate `2531723681 / 50000000000` for `(512, 128)`. -/
theorem rkmBoundHi_m512_k128 :
    checkAltBound12 512 128 (rkmVPotHi_m512.getD 128 0) 2531723681 50000000000 = true :=
  (rkmHd (rkmTl4 (rkmTl16 rkmBoundsAllOkHi_m512)))
/-- Cell `lMax = 1` bound for `(512, 256)`. -/
theorem rkmCellLMaxHi_m512_k256 :
    rkmCheckAnchorsLMax 256 1 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl (rkmTl4 (rkmTl16 rkmBoundsAllOkHi_m512))))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(512, 256)`. -/
theorem rkmCellLMax2Hi_m512_k256 :
    rkmCheckAnchorsLMax 256 2 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl16 rkmBoundsAllOkHi_m512)))))
/-- Relative-cost certificate `19387951311 / 500000000000` for `(512, 256)`. -/
theorem rkmBoundHi_m512_k256 :
    checkAltBound12 512 256 (rkmVPotHi_m512.getD 256 0) 19387951311 500000000000 = true :=
  (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 (rkmTl16 rkmBoundsAllOkHi_m512))))))
/-- Cell `lMax = 2` bound for `(512, 512)`. -/
theorem rkmCellLMaxHi_m512_k512 :
    rkmCheckAnchorsLMax 512 2 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl4 (rkmTl4 (rkmTl16 rkmBoundsAllOkHi_m512))))
/-- Cold-`r2` `lMax = 2` (`>= 2`) bound for `(512, 512)`. -/
theorem rkmCellLMax2Hi_m512_k512 :
    rkmCheckAnchorsLMax 512 2 rkmAnchorsHi_m512 = true :=
  (rkmHd (rkmTl4 (rkmTl4 (rkmTl16 rkmBoundsAllOkHi_m512))))
/-- Relative-cost certificate `17133448611 / 500000000000` for `(512, 512)`. -/
theorem rkmBoundHi_m512_k512 :
    checkAltBound12 512 512 (rkmVPotHi_m512.getD 512 0) 17133448611 500000000000 = true :=
  (rkmHd (rkmTl (rkmTl4 (rkmTl4 (rkmTl16 rkmBoundsAllOkHi_m512)))))

/-- Terminal `1`-lane table closure for `FindAllJohnsonRampKickMuxHiCert512`. -/
theorem laneClosure_FindAllJohnsonRampKickMuxHiCert512 :
    rkmTrajHi_m512_r256 = rkmTrajHi_m512_r256 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi512T9) rfl).right

end
end QuantumComputation.Specs.DickeSol
