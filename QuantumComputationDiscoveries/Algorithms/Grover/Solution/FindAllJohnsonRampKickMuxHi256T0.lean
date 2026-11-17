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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiBase

/-
# High-`m` Trajectory Part `0` (`FindAllJohnsonRampKickMuxHi256T0`)

Certifies all `30` active `r = 3..32` Krotov rows for `m = 256` (`17345` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Prefix-kick masks for `(m = 256, r = 3)`. -/
def rkmMasksHi_m256_r3 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 3)`. -/
def rkmRowHi_m256_r3 : List ℕ := [805875282, 53487362016, 945703776153]
/-- Prefix-kick masks for `(m = 256, r = 4)`. -/
def rkmMasksHi_m256_r4 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 4)`. -/
def rkmRowHi_m256_r4 : List ℕ := [805354, 402591425, 39730236420, 959866366768]
/-- Prefix-kick masks for `(m = 256, r = 5)`. -/
def rkmMasksHi_m256_r5 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 5)`. -/
def rkmRowHi_m256_r5 : List ℕ := [1857, 34267, 201192171, 31670189727, 968128581920]
/-- Prefix-kick masks for `(m = 256, r = 6)`. -/
def rkmMasksHi_m256_r6 : List (List Bool) := [[], [], [], [], [true], [false, true, true],
  [false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 6)`. -/
def rkmRowHi_m256_r6 : List ℕ := [40, 1, 462, 93639070, 26371249326, 973535110951]
/-- Prefix-kick masks for `(m = 256, r = 7)`. -/
def rkmMasksHi_m256_r7 : List (List Bool) := [[], [], [], [false, true], [false, false, true],
  [false, false, false, true], [false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 7)`. -/
def rkmRowHi_m256_r7 : List ℕ := [0, 0, 0, 9548, 36217295, 22621494260, 977342278732]
/-- Prefix-kick masks for `(m = 256, r = 8)`. -/
def rkmMasksHi_m256_r8 : List (List Bool) := [[], [], [], [false, true, true], [false, false,
  false, true], [false, false, true, false, true], [false, false, true, false, false, true],
  []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 8)`. -/
def rkmRowHi_m256_r8 : List ℕ := [0, 0, 0, 0, 22023, 8479740, 19827775230, 980163722826]
/-- Prefix-kick masks for `(m = 256, r = 9)`. -/
def rkmMasksHi_m256_r9 : List (List Bool) := [[], [], [], [false, false, false, true], [false,
  false, false, false, true], [false, false, false, false, true, true], [false, false, false,
  false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 9)`. -/
def rkmRowHi_m256_r9 : List ℕ := [0, 0, 0, 0, 0, 17058, 35042, 17665993070, 982333954633]
/-- Prefix-kick masks for `(m = 256, r = 10)`. -/
def rkmMasksHi_m256_r10 : List (List Bool) := [[], [false, false, true], [], [false, false,
  false, false, true], [false, false, false, true, true, true], [false, false, false, false,
  true, false, true], [false, false, false, false, false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 10)`. -/
def rkmRowHi_m256_r10 : List ℕ := [0, 0, 0, 0, 1, 0, 2271, 5116495, 15943532198, 984051348820]
/-- Prefix-kick masks for `(m = 256, r = 11)`. -/
def rkmMasksHi_m256_r11 : List (List Bool) := [[], [], [false, false, false, true, true],
  [false, false, false, false, true, true], [false, false, false, false, false, true, true],
  [false, false, false, false, true, true, false, true], [false, false, false, false, true,
  true, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 11)`. -/
def rkmRowHi_m256_r11 : List ℕ := [0, 0, 0, 0, 0, 1, 37, 8050, 20289597, 14538908050,
  985440794034]
/-- Prefix-kick masks for `(m = 256, r = 12)`. -/
def rkmMasksHi_m256_r12 : List (List Bool) := [[], [], [], [false, false, false, false, true,
  false, true, true, true], [false, false, false, false, true, false, true, true, false, true,
  true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 12)`. -/
def rkmRowHi_m256_r12 : List ℕ := [0, 0, 0, 0, 3, 127, 172, 158302, 5011087, 1427306,
  13356911007, 986636491749]
/-- Prefix-kick masks for `(m = 256, r = 13)`. -/
def rkmMasksHi_m256_r13 : List (List Bool) := [[], [], [false, false, false, false, false,
  true, true], [false, false, false, false, true, false, true, false, true, true], [false,
  false, false, false, false, false, true, true, false, true, true], [false, false, false,
  false, false, true, false, false, false, false, true], [false, false, false, false, true,
  true, true, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 13)`. -/
def rkmRowHi_m256_r13 : List ℕ := [0, 0, 0, 0, 0, 0, 7, 9963, 3, 2639, 2880970, 12368793851,
  987628312292]
/-- Prefix-kick masks for `(m = 256, r = 14)`. -/
def rkmMasksHi_m256_r14 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, true, true], [false, false, false, false, false, true, false, true, true, true, true],
  [false, false, false, false, false, false, false, false, false, true, false, true], [false,
  false, false, false, false, false, false, true, true, true, false, true], [false, false,
  false, false, false, true, false, false, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 14)`. -/
def rkmRowHi_m256_r14 : List ℕ := [0, 0, 0, 0, 0, 0, 30, 2, 11686, 865, 1129, 4429973,
  11523794003, 988471762019]
/-- Prefix-kick masks for `(m = 256, r = 15)`. -/
def rkmMasksHi_m256_r15 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, true, true], [false, false, false, false, false, false, true, false, true,
  true, true, true], [false, false, false, false, false, false, false, false, true, true,
  false, false, true], [false, false, false, false, false, false, true, true, false, false,
  false, false, true], [false, false, false, false, false, false, true, true, false, true,
  false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 15)`. -/
def rkmRowHi_m256_r15 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 53, 18, 14320, 3307, 3449, 6078290,
  10792675768, 989201224485]
/-- Prefix-kick masks for `(m = 256, r = 16)`. -/
def rkmMasksHi_m256_r16 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, true, false, true, false, false, true], [], [false, false, false, false, false,
  false, false, false, false, false, false, true, true, true], [false, false, false, false,
  false, false, false, false, true, false, true, false, false, true], [false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, true], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 16)`. -/
def rkmRowHi_m256_r16 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 116, 15, 224940, 31249, 7721300,
  10154397261, 989837624776]
/-- Prefix-kick masks for `(m = 256, r = 17)`. -/
def rkmMasksHi_m256_r17 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, true, false, true, true], [false, false, false, false, false, false, false,
  false, false, true, true, true, true], [false, false, false, false, false, false, false,
  false, true, false, true, true, false, true, true], [false, false, false, false, false,
  false, false, false, false, true], [false, false, false, false, false, false, false, false,
  false, true, false, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 17)`. -/
def rkmRowHi_m256_r17 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 617, 720, 208, 473645, 58973,
  9438702, 9591676690, 990398350050]
/-- Prefix-kick masks for `(m = 256, r = 18)`. -/
def rkmMasksHi_m256_r18 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, false, true, false, true, true], [false, false, false, false, false, false,
  false, false, false, true, false, false, true, true], [false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, true, true], [false, false,
  false, false, false, false, false, false, true, false, true, false, true, false, false,
  true], [false, false, false, false, false, false, false, false, false, false, true, false,
  false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 18)`. -/
def rkmRowHi_m256_r18 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 597, 812, 659712, 22060,
  11120848, 9092860378, 990895335177]
/-- Prefix-kick masks for `(m = 256, r = 19)`. -/
def rkmMasksHi_m256_r19 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, false, false, true, false, true, true], [false, false, false, false, false,
  false, false, false, false, false, true, false, false, true, true], [false, false, false,
  false, false, false, false, false, false, true, true, false, true, false, false, true, true],
  [false, false, false, false, false, false, false, true, false, true, false, true, false,
  true, false, false, true], [false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 19)`. -/
def rkmRowHi_m256_r19 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 10, 390, 3647, 872995,
  71844, 12731607, 8646872131, 991339446935]
/-- Prefix-kick masks for `(m = 256, r = 20)`. -/
def rkmMasksHi_m256_r20 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, false, false, false, true, true, true, true], [false, false, false, false,
  false, false, false, false, false, false, true, true, false, false, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, true, true], [false, false, false, false, false, false, false, false, true,
  false, true, false, false, false, true], [false, false, false, false, false, false, false,
  false, false, false, true, true, true, false, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 20)`. -/
def rkmRowHi_m256_r20 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 4, 42, 1491, 861120,
  195562, 14197451, 8246431193, 991738312679]
/-- Prefix-kick masks for `(m = 256, r = 21)`. -/
def rkmMasksHi_m256_r21 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, true], [false, false, false,
  false, false, false, false, false, false, false, false, true, true, false, false, true,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, true, false, false, true, true], [false, false, false, false, false, false,
  false, false, false, true, true, true, false, false, true, false, true, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, true, true, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 21)`. -/
def rkmRowHi_m256_r21 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 101, 222, 321, 6382,
  1145725, 118040, 15969127, 7883929848, 992098829746]
/-- Prefix-kick masks for `(m = 256, r = 22)`. -/
def rkmMasksHi_m256_r22 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, false, false, true, true], [false, false, false, false, false, false, false,
  false, false, false, true, false, true, false, true, true], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, true,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, true, true, false, false, true, true], [false, false, false, false, false,
  false, false, false, false, false, true, true, false, true, true, true, false, true, true,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, true, true, true, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 22)`. -/
def rkmRowHi_m256_r22 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 7, 9, 3090, 1983,
  1112478, 177257, 17151025, 7555634111, 992425919483]
/-- Prefix-kick masks for `(m = 256, r = 23)`. -/
def rkmMasksHi_m256_r23 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, false, false, false, true, true], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, true], [false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, true,
  false, false, true, true], [false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, true, true, false, false, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, true, true, false,
  true, true, true, false, true, true, true], [false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, true, true, true, true, true, true,
  true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 23)`. -/
def rkmRowHi_m256_r23 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 177, 15152,
  1604783, 214294, 18789712, 7255790977, 992723584327]
/-- Prefix-kick masks for `(m = 256, r = 24)`. -/
def rkmMasksHi_m256_r24 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, false, true, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, true, false, true], [false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, true, false, true, true, false, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, true, true, true, true,
  false, false, false, false, false, false, true], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, false, true,
  false, false, false, true], [false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 24)`. -/
def rkmRowHi_m256_r24 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 96, 751,
  90873, 1187, 944600, 19658396, 6996182917, 992983120520]
/-- Prefix-kick masks for `(m = 256, r = 25)`. -/
def rkmMasksHi_m256_r25 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, false, true, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, false, true, false, true], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, false, true, true, false,
  true, true], [false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, true, true, false, false, false, false, false, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, false, false, true, false, false, false, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, true, false, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 25)`. -/
def rkmRowHi_m256_r25 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89, 669,
  87830, 117214, 2733, 1280, 6745260996, 993254528498]
/-- Prefix-kick masks for `(m = 256, r = 26)`. -/
def rkmMasksHi_m256_r26 : List (List Bool) := [[false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true], [false, false, false, false, false,
  false, false, false, true, false, true, false, true, false, true, true, false, true, false,
  true], [false, false, false, false, false, false, false, true, true, false, false, false,
  false, false, false, true, true, false, true, true, true], [false, false, false, false,
  false, false, true, false, false, false, true, false, false, true, true, true, false, false,
  false, true, false, true, true], [false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, false, false, true, false, true, false, true, true,
  false, true], [false, false, false, false, false, false, false, false, false, false, false,
  false, true, false, false, false, false, false, false, false, true, false, true, true, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, true, true, true, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 26)`. -/
def rkmRowHi_m256_r26 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 10, 0, 5, 34, 202, 5, 160,
  609, 515, 301545, 8733, 1393, 1191167, 6509833763, 993488661125]
/-- Prefix-kick masks for `(m = 256, r = 27)`. -/
def rkmMasksHi_m256_r27 : List (List Bool) := [[false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true], [false, false, false, false,
  false, false, false, false, false, true, false, true, false, true, false, true, true, false,
  true, false, true], [false, false, false, false, false, false, false, false, true, true,
  true, true, true, true, true, true, false, false, true, false, true, true], [false, false,
  false, false, false, false, false, true, false, true, false, true, true, true, true, true,
  true, true, false, true, true, false, true, true], [false, false, false, false, false, false,
  false, false, false, true, true, false, false, false, true, true, false, false, false, false,
  false, false, false, false, true], [false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, true, false, false, true, true, true, true, false,
  true, true, true, true], [false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, true, true, true,
  true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 27)`. -/
def rkmRowHi_m256_r27 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 30, 87, 35, 153, 42,
  17, 585, 1002, 175924, 164913, 26389, 4440496, 6286864252, 993708325304]
/-- Prefix-kick masks for `(m = 256, r = 28)`. -/
def rkmMasksHi_m256_r28 : List (List Bool) := [[false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true], [false, false, false,
  false, false, false, false, false, true, false, true, false, true, false, true, false, true,
  true, false, true, false, true], [false, false, false, false, false, false, false, false,
  false, true, true, true, true, true, true, true, true, true, true, true, false, true, true],
  [false, false, false, false, false, false, false, false, true, false, true, true, true, true,
  true, true, true, true, false, false, true, true, false, true, true], [false, false, false,
  false, false, false, false, false, false, false, true, false, false, true, true, false,
  false, false, false, false, false, false, false, false, false, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, false,
  true, true, true, true, true, true, false, true, true, true, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, true, true,
  false, true, true, true, true, true, true, true, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 28)`. -/
def rkmRowHi_m256_r28 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 5, 73, 0, 310, 59,
  42, 148, 969, 797, 190934, 222950, 7199, 4112194, 6089165698, 993906297793]
/-- Prefix-kick masks for `(m = 256, r = 29)`. -/
def rkmMasksHi_m256_r29 : List (List Bool) := [[false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true], [false, false,
  false, false, false, false, false, false, false, true, false, true, false, false, true,
  false, true, false, true, false, true, false, true], [false, false, false, false, false,
  false, false, false, false, false, true, false, false, true, true, true, true, true, false,
  false, true, false, true, true], [false, false, false, false, false, false, false, false,
  false, true, false, true, false, false, false, false, false, false, false, true, false, true,
  true, false, true, true], [false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, false, false, true, true, true, true, false, false, true,
  true, false, false, true], [false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, true, true, false, false, true, true, false, false,
  true, false, false, true, true], [false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, true, true, true, true, false, false, false,
  false, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 29)`. -/
def rkmRowHi_m256_r29 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 7, 0, 0, 22, 79, 49,
  161, 163, 462, 3, 18743, 215109, 305399, 6512, 6391420, 5904886770, 994088174191]
/-- Prefix-kick masks for `(m = 256, r = 30)`. -/
def rkmMasksHi_m256_r30 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, true, false, false, true, false, true, false, false, true, true, true, false, true,
  false, true], [false, false, false, false, false, false, false, false, false, false, false,
  true, false, true, false, true, true, false, false, true, false, true, true, true], [false,
  false, false, false, false, false, false, true, false, false, true, false, true, false,
  false, false, false, false, false, true, true, false, false, true, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, true, true, true, false, true, false, true, false, true, true, false, true, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, true, false, false, true, true, true, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false,
  true, false, false, false, true, true, true, true, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 30)`. -/
def rkmRowHi_m256_r30 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
  276, 17, 16102, 1714, 6018, 2947528, 2687504, 25570381, 5733154571, 994235615006]
/-- Prefix-kick masks for `(m = 256, r = 31)`. -/
def rkmMasksHi_m256_r31 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, true, false, false, true, false, true, false, false, true, true, true, true,
  false, true], [false, false, false, false, false, false, false, false, false, false, false,
  false, true, false, true, false, true, false, true, true, false, true, false, true, true],
  [false, false, false, false, false, false, false, false, true, false, false, true, false,
  true, false, false, false, false, true, true, false, false, false, false, true, true, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, false, true, true, false, false, true, false, true, false, true, true, false,
  true, true], [false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, true, false, false, true, true, false, false, false,
  true, false, false, false, true], [false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, false, true, false, false, true, true,
  false, false, false, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 31)`. -/
def rkmRowHi_m256_r31 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0,
  39, 14, 517, 14141, 2180, 12893, 4695905, 1603923, 8039930, 5564025551, 994421603973]
/-- Prefix-kick masks for `(m = 256, r = 32)`. -/
def rkmMasksHi_m256_r32 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, true,
  true, false, true, false, true, true, false, true, true], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, true, false, true, false, true, false, false, true, true, true], [false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, true, false, true,
  false, true, true], [false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, true, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 32)`. -/
def rkmRowHi_m256_r32 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 3, 43, 23512, 13543, 3626490, 5348285, 352556, 29739260, 5415392596, 994545502742]

end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem bForceN_eq {α : Type} (x : ℕ) (k : ℕ → α) :
    HighDForce.withForcedNat x k = k x := by
  unfold HighDForce.withForcedNat; rw [n1a]
private theorem bForceL_eq {α β : Type} (xs : List α) (k : List α → β) :
    HighDForce.withForcedList xs k = k xs := by
  cases xs <;> rfl
private theorem bOfNatF_eq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  unfold primOfNatForced; rw [n1a]
private theorem bNegSuccF_eq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  unfold primNegSuccForced; rw [n1a]
private theorem bPrimNegOfNat_eq (x : ℕ) : primNegOfNat x = -(x : ℤ) := by
  cases x with
  | zero => dsimp only [primNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only [primNegOfNat]; rw [bNegSuccF_eq, Int.negSucc_eq]; omega
private theorem bPrimSubNat_eq (u z : ℕ) : primSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold primSubNatNat; simp only [Nat.sub_eq]; cases h : z - u with
  | zero => dsimp only; rw [bOfNatF_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [bNegSuccF_eq, Int.negSucc_eq]; omega
private theorem bPrimMul_eq (a b : ℤ) : primIntMul a b = a * b := by
  cases a <;> cases b <;> dsimp only [primIntMul] <;>
    simp only [bOfNatF_eq, bPrimNegOfNat_eq, Nat.mul_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> push_cast <;> ring
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 => xs
  | v + 1 =>
    match xs with
    | [] => [v]
    | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match x with
    | Int.ofNat n =>
      match uToNatHb xs with
      | some ns => some (uConsNat n ns)
      | none => none
    | Int.negSucc _ => none
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfNatHb ns
private theorem uToNatHb_sound :
    ∀ (hb : List ℤ) (ns : List ℕ), uToNatHb hb = some ns → hb = uOfNatHb ns
  | [], ns, h => by injection h with h'; subst h'; rfl
  | Int.negSucc _ :: _, _, h => by dsimp only [uToNatHb] at h; cases h
  | Int.ofNat n :: xs, ns, h => by
    dsimp only [uToNatHb] at h; revert h; cases hxs : uToNatHb xs with
    | none => intro h; dsimp only at h; cases h
    | some ms =>
      intro h; dsimp only at h; injection h with h'; subst h'
      rw [uConsNat_eq, uOfNatHb, uToNatHb_sound xs ms hxs]
private def bConsZ (x : ℤ) (xs : List ℤ) : List ℤ :=
  match x with
  | Int.ofNat v =>
    match xs with
    | [] => [Int.ofNat v]
    | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v =>
    match xs with
    | [] => [Int.negSucc v]
    | h :: t => Int.negSucc v :: h :: t
private theorem bConsZ_eq (x : ℤ) (xs : List ℤ) : bConsZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem bStrictCons_eq (x : ℤ) (xs : List ℤ) : highdStrictConsInt x xs = x :: xs := by
  cases x with
  | ofNat n =>
    change (match Nat.add 1 n with
      | 0 =>
        match xs with
        | [] => [Int.ofNat 0]
        | h :: t => Int.ofNat 0 :: h :: t
      | v + 1 =>
        match xs with
        | [] => [Int.ofNat v]
        | h :: t => Int.ofNat v :: h :: t) = Int.ofNat n :: xs
    rw [n1a]; cases xs <;> rfl
  | negSucc n =>
    change (match Nat.add 1 n with
      | 0 =>
        match xs with
        | [] => [Int.negSucc 0]
        | h :: t => Int.negSucc 0 :: h :: t
      | v + 1 =>
        match xs with
        | [] => [Int.negSucc v]
        | h :: t => Int.negSucc v :: h :: t) = Int.negSucc n :: xs
    rw [n1a]; cases xs <;> rfl
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bConsZ (primSubNatNat u z) (bDec z us)
private theorem bDec_nil (z : ℕ) : bDec z [] = [] := rfl
private theorem bDec_cons (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by rw [bDec, bConsZ_eq, bPrimSubNat_eq]
private theorem bDec_len (z : ℕ) : ∀ (cs : List ℕ), altIntLen (bDec z cs) = altListLen cs
  | [] => rfl
  | _ :: cs => by rw [bDec_cons, altIntLen, altListLen, bDec_len z cs]
private theorem bZero_eq (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bPrimMul0 (z : ℕ) :
    primIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bPrimMul_eq, bZero_eq]; rfl
private def bEnc1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k =>
    match Nat.sub z (Nat.add k 1) with
    | 0 => none
    | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match bEnc1 z x with
    | none => none
    | some u =>
      match bEnc z xs with
      | none => none
      | some us => some (uConsNat u us)
private theorem bEnc1_sound (z : ℕ) (x : ℤ) (u : ℕ) (h : bEnc1 z x = some u) :
    ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bEnc1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w => intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem bEnc_sound (z : ℕ) :
    ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us → bDec z us = xs
  | [], us, h => by injection h with h'; subst h'; rfl
  | x :: xs, us, h => by
    dsimp only [bEnc] at h; revert h; cases hx : bEnc1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bEnc z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uConsNat_eq, bDec_cons, bEnc1_sound z x u hx, bEnc_sound z xs ws hxs]
private def zTdiv (x : ℤ) (d : ℕ) : ℤ :=
  match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTdivNat_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by dsimp only [muxRawIntTdivNat, zTdiv]; rw [bNeg_eq, ndiv, Nat.add_eq]
private theorem bRawSubNat_eq (m n : ℕ) : muxRawSubNatNat m n = (m : ℤ) - (n : ℤ) := by
  unfold muxRawSubNatNat; simp only [Nat.sub_eq]; cases h : n - m with
  | zero => dsimp only; rw [Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private theorem bRawAdd_eq (a b : ℤ) : muxRawIntAdd a b = a + b := by
  cases a <;> cases b <;> dsimp only [muxRawIntAdd] <;>
    simp only [bOfNatF_eq, bNegSuccF_eq, bRawSubNat_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
private theorem bRawNeg_eq (a : ℤ) : muxRawIntNeg a = -a := by
  cases a <;> dsimp only [muxRawIntNeg] <;>
    simp only [bNeg_eq, bOfNatF_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
private theorem bRawSub_eq (a b : ℤ) : muxRawIntSub a b = a - b := by
  unfold muxRawIntSub; rw [bRawAdd_eq, bRawNeg_eq]; omega
private theorem bRawMul_eq (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a <;> cases b <;> dsimp only [muxRawIntMul] <;>
    simp only [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq] <;>
    push_cast <;> ring
private def bStepVal (v P Q d : ℕ) : ℕ :=
  fN P fun p => fN Q fun q => match Nat.sub q p with
  | 0 => Nat.add v (Nat.div (Nat.sub p q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  unfold bStepVal at hv ⊢; dsimp only [fN] at hv ⊢
  rw [bForceN_eq, bForceN_eq] at hv ⊢
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢
  revert hv; cases h : Q - P with
  | zero =>
    intro _; have hm : (P : ℤ) - (Q : ℤ) = Int.ofNat (P - Q) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; dsimp only [zTdiv]; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k =>
    intro hv; have hm : (P : ℤ) - (Q : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTdiv] at hv ⊢; omega
private abbrev bCellVal (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCellVal z d b0 c0 b v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCellVal z d b0 c0 b v c1) rest) =
      highdStrictConsInt (muxRawIntAdd ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntSub (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ)))) d)) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bStrictCons_eq, bRawAdd_eq, bTdivNat_eq, bRawSub_eq,
    bPrimMul_eq, bRawMul_eq]; refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCellVal at hv ⊢; rw [bStepVal_eq z v _ _ d hv, hpq]
private theorem bCell_nil (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      highdStrictConsInt (muxRawIntAdd ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d)) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bStrictCons_eq, bRawAdd_eq, bTdivNat_eq, bPrimMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  rw [bStepVal_eq z v _ _ d hv, hpq]
private def bAllPos : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAllPos xs)
private theorem bAllPos_uCons {x : ℕ} {xs : List ℕ} (h : bAllPos (uConsNat x xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  rw [uConsNat_eq] at h
  cases x with
  | zero => exact Bool.noConfusion h
  | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHeadOr (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTailN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem bHeadOr_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHeadOr z cs : ℤ) - (z : ℤ)) =
      (match bDec z cs with
      | cn :: _ => cn
      | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq]
  | c :: cs => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) =
      (match bDec z xs with
      | _ :: t => t
      | [] => [])
  | [] => rfl
  | x :: xs => by unfold bTailN; rw [bDec_cons]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs =>
    match bns with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSlide z d rem 0 z [] (bTailN vs) (bTailN cs))
    | b :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal z d b0 c0 b v (bHeadOr z cT)) (bSlide z d rem b c bR vT cT)
      | v :: vT, [] => uConsNat (bCellVal z d b0 c0 b v z) (bSlide z d rem b z bR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal z d b0 c0 b z (bHeadOr z cT)) (bSlide z d rem b c bR [] cT)
      | [], [] => uConsNat (bCellVal z d b0 c0 b z z) (bSlide z d rem b z bR [] [])
private theorem bSlide_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSlide z d rem b0 c0 bns vs cs) = true → bDec z (bSlide z d rem b0 c0 bns vs cs) =
      muxFastSlideLoopAux d rem (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSlide, uOfNatHb, muxFastSlideLoopAux] at h ⊢; have hp := bAllPos_uCons h
      have hi := bSlide_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp.2
      rw [bPrimMul0 z, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi; rw [bHeadOr_eq z vs] at hc; exact hc
    | cons b bR =>
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_nil]; dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSlide_sound z d rem b z bR [] [] hp.2
          rw [bZero_eq z, bDec_nil] at hi; have hc := bCell_hb z d b0 c0 b z z hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfNatHb] at h ⊢
          rw [bDec_nil, bDec_cons z c cT]; dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSlide_sound z d rem b c bR [] cT hp.2
          rw [bDec_nil] at hi; have hc := bCell_hb z d b0 c0 b z (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT, bZero_eq z] at hc; exact hc
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢
          rw [bDec_cons z v vT, bDec_nil]; dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSlide_sound z d rem b z bR vT [] hp.2
          rw [bZero_eq z, bDec_nil] at hi; have hc := bCell_hb z d b0 c0 b v z hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfNatHb] at h ⊢
          rw [bDec_cons z v vT, bDec_cons z c cT]; dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSlide_sound z d rem b c bR vT cT hp.2
          have hc := bCell_hb z d b0 c0 b v (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT] at hc; exact hc
private def bStg (z dg mL : ℕ) (bns vns cns : List ℕ) : Option (List ℕ) :=
  fN (highdNatMin mL (Nat.add (altListLen cns) 1)) fun nL =>
    fN (Nat.mul dg wdScale) fun d =>
      fL (bSlide z d nL 0 z bns vns cns) fun out => cond (bAllPos out) (some out) none
private theorem bStg_sound (z dg mL : ℕ) (bns vns cns out : List ℕ)
    (h : bStg z dg mL bns vns cns = some out) :
    bDec z out = muxFastHornerStage dg mL (uOfNatHb bns) (bDec z vns) (bDec z cns) := by
  unfold bStg at h; dsimp only [fN, fL] at h
  rw [bForceN_eq, bForceN_eq, bForceL_eq] at h; revert h
  set nL := highdNatMin mL (Nat.add (altListLen cns) 1); set d := Nat.mul dg wdScale
  cases hp : bAllPos (bSlide z d nL 0 z bns vns cns) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold muxFastHornerStage
    rw [bDec_len z cns, bForceN_eq, bForceN_eq, ← bPrimMul0 z]
    exact bSlide_sound z d nL 0 z bns vns cns hp
private def bBind (x : Option (List ℕ)) (k : List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  match x with
  | none => none
  | some out => k out
private theorem bBind_sound {z dg mL : ℕ} {bns vns cns out : List ℕ}
    {kB : List ℕ → Option (List ℕ)} {kU : List ℤ → List ℤ}
    (h : bBind (bStg z dg mL bns vns cns) kB = some out)
    (hk : ∀ (mid : List ℕ), kB mid = some out → bDec z out = kU (bDec z mid)) :
    bDec z out = HighDForce.withForcedList
      (muxFastHornerStage dg mL (uOfNatHb bns) (bDec z vns) (bDec z cns)) kU := by
  unfold bBind at h; revert h; cases hs : bStg z dg mL bns vns cns with
  | none => intro h; cases h
  | some mid =>
    intro h; rw [bForceL_eq, ← bStg_sound z dg mL bns vns cns mid hs]; exact hk mid h
private def bStep (z mL : ℕ) (bns vns : List ℕ) : Option (List ℕ) :=
  bBind (bStg z 16 mL bns vns vns) fun c1 => bBind (bStg z 15 mL bns vns c1) fun c2 =>
  bBind (bStg z 14 mL bns vns c2) fun c3 => bBind (bStg z 13 mL bns vns c3) fun c4 =>
  bBind (bStg z 12 mL bns vns c4) fun c5 => bBind (bStg z 11 mL bns vns c5) fun c6 =>
  bBind (bStg z 10 mL bns vns c6) fun c7 => bBind (bStg z 9 mL bns vns c7) fun c8 =>
  bBind (bStg z 8 mL bns vns c8) fun c9 => bBind (bStg z 7 mL bns vns c9) fun ca =>
  bBind (bStg z 6 mL bns vns ca) fun cb => bBind (bStg z 5 mL bns vns cb) fun cc =>
  bBind (bStg z 4 mL bns vns cc) fun cd => bBind (bStg z 3 mL bns vns cd) fun ce =>
  bBind (bStg z 2 mL bns vns ce) fun cf => bStg z 1 mL bns vns cf
private theorem bStep_sound (z mL : ℕ) (bns vns out : List ℕ)
    (h : bStep z mL bns vns = some out) :
    bDec z out = muxFastHornerT16Step mL (uOfNatHb bns) (bDec z vns) := by
  unfold bStep at h; unfold muxFastHornerT16Step
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  exact bStg_sound _ _ _ _ _ _ _ h
private def bIter (z : ℕ) : ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, vns => some vns
  | k + 1, mL, bns, vns =>
    match bStep z mL bns vns with
    | none => none
    | some vNext => bIter z k mL bns vNext
private theorem bIter_sound (z : ℕ) : ∀ (k mL : ℕ) (bns vns out : List ℕ),
    bIter z k mL bns vns = some out →
    bDec z out = muxFastIterFullT16 k mL (uOfNatHb bns) (bDec z vns)
  | 0, _, _, vns, out, h => by injection h with h'; subst h'; rfl
  | k + 1, mL, bns, vns, out, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL bns vns with
    | none => intro h; cases h
    | some vNext =>
      intro h; unfold muxFastIterFullT16
      rw [bForceL_eq, ← bStep_sound z mL bns vns vNext hs]
      exact bIter_sound z k mL bns vNext out h
private def fIter (k mL : ℕ) (hb v : List ℤ) : List ℤ :=
  let z := 2000000000000000
  match uToNatHb hb with
  | none => muxFastIterFullT16 k mL hb v
  | some bns =>
    match bEnc z v with
    | none => muxFastIterFullT16 k mL hb v
    | some vns =>
      match bIter z k mL bns vns with
      | none => muxFastIterFullT16 k mL hb v
      | some out => bDec z out
private theorem fIter_eq (k mL : ℕ) (hb v : List ℤ) :
    fIter k mL hb v = muxFastIterFullT16 k mL hb v := by
  unfold fIter; dsimp only; cases hh : uToNatHb hb with
  | none => rfl
  | some bns =>
    dsimp only; cases hv : bEnc 2000000000000000 v with
    | none => rfl
    | some vns =>
      dsimp only; cases hi : bIter 2000000000000000 k mL bns vns with
      | none => rfl
      | some out =>
        dsimp only; rw [bIter_sound 2000000000000000 k mL bns vns out hi,
          ← uToNatHb_sound hb bns hh, bEnc_sound 2000000000000000 v vns hv]
private def bSlideChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    muxIntListEq (fIter steps maxLen hbF inF) outF
private theorem bSlideChk_sound {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : bSlideChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold bSlideChk at h; dsimp only [fL] at h
  rw [bForceL_eq, bForceL_eq, bForceL_eq, fIter_eq] at h
  exact muxIntListEq_eq_true.mp h
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true :=
  (rkmAllTrueF_cons h).2
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def bEvalSegs (m lM r : ℕ) :
    List ℕ → List ℕ → List ℕ → List (List Bool) → ℕ → ℕ → ℕ → List ℤ → (ℕ × ℕ × List ℤ)
  | [], tR, nR, mR, _, dE, aP, v =>
    match tR, nR, mR with
    | [], [], [] => (dE, aP, v)
    | _, _, _ => (0, 0, [])
  | lS :: lR, t9 :: tR, nS :: nR, mk :: mR, lP, _, aP, v =>
    let mE := Nat.mul lS m; let d := highdNatMin mE r
    cond (Bool.or (primNatBlt lS 1)
      (Bool.or (primNatBlt lS lP)
      (Bool.or (primNatBlt lM lS)
      (Bool.or (primNatBlt mE 1)
      (Bool.or (primNatBlt 8192 mE)
      (Bool.or (primNatBlt d 1)
      (Bool.or (Nat.ble t9 0)
      (Bool.or (primNatBlt 4000000000 t9)
      (Bool.or (Nat.ble nS 0)
      (Bool.or (primNatBlt 16384 nS)
        (primNatBlt (Nat.add d 1) (rkmBoolListLen mk))))))))))))
      (0, 0, [])
      (let hRaw := Nat.div (Nat.mul t9 1000000) nS
      HighDForce.withForcedNat hRaw fun hPt =>
        cond (primNatBlt hPt 1) (0, 0, [])
          (let bRaw := altMaxBHiFrom mE r 0 d
          HighDForce.withForcedNat bRaw fun bHi =>
            let bCap := Nat.mul 2 bHi; let hgR := highdMulCeil15 (Nat.add 2 hPt) bCap
            HighDForce.withForcedNat hgR fun hgHi =>
              cond (Bool.or (primNatBlt 1500000000000000 hgHi)
                  (Bool.not (altCheckHbTight mE r 0 d)))
                (0, 0, [])
                (let hgP := altPow17Ceil15 hgHi
                let trP := Nat.div (Nat.add 299999999999999 (Nat.mul nS hgP)) 300000000000000
                let bCeil := Nat.div (Nat.add 999999999999999 bCap) wdScale
                let sPad := Nat.add (Nat.add trP 256) (Nat.mul nS (Nat.add 256 (Nat.mul 10 bCeil)))
                let npR := Nat.add aP sPad
                HighDForce.withForcedNat npR fun np =>
                  cond (Bool.or (Nat.ble np 0) (primNatBlt 100000000000000 np)) (0, 0, [])
                    (let hbR := altBuildHbFrom mE r hPt 0 d
                    HighDForce.withForcedList hbR fun hbP =>
                      let wR := fIter nS (Nat.add d 1) hbP v
                      HighDForce.withForcedList wR fun vW =>
                        let kR := rkmApplyMaskBits mk vW
                        HighDForce.withForcedList kR fun vN =>
                          bEvalSegs m lM r lR tR nR mR lS d np vN))))
  | _, _, _, _, _, _, _, _ => (0, 0, [])
private theorem bEvalSegs_eq (m lM r : ℕ) :
    ∀ (ls ts ns : List ℕ) (mks : List (List Bool)) (lP dE aP : ℕ) (v : List ℤ),
      bEvalSegs m lM r ls ts ns mks lP dE aP v =
        rkmEvalSegsLoop m lM r ls ts ns mks lP dE aP v := by
  intro ls; induction ls with
  | nil => intros; rfl
  | cons lS lR ih =>
    intro ts ns mks lP dE aP v
    cases ts with
    | nil => rfl
    | cons t9 tR =>
      cases ns with
      | nil => rfl
      | cons nS nR =>
        cases mks with
        | nil => rfl
        | cons mk mR =>
          unfold bEvalSegs rkmEvalSegsLoop
          simp only [bForceN_eq, bForceL_eq, fIter_eq]; rw [ih]
          generalize Nat.add aP _ = np; cases t9 <;> cases nS <;> cases np <;> rfl
private def bEvalLo12 (m lM r : ℕ) (ls ts ns : List ℕ) (mks : List (List Bool)) : List ℕ :=
  let nS := altListLen ls
  cond (Bool.or (Nat.ble nS 0)
    (Bool.or (primNatBlt 8 nS) (Bool.or (primNatBlt r 2) (primNatBlt 1024 r))))
    []
    (match bEvalSegs m lM r ls ts ns mks 1 0 0 [Int.ofNat wdScale] with
    | (dE, aP, vF) =>
      cond (Bool.or (Nat.ble dE 0) (Nat.ble aP 0)) []
        (match altPadRightInts (Nat.add dE 1) vF with
        | [] => []
        | _ :: tl => altVecTailToLo12 aP tl))
private theorem bEvalLo12_eq (m lM r : ℕ) (ls ts ns : List ℕ) (mks : List (List Bool)) :
    bEvalLo12 m lM r ls ts ns mks = rkmEvalT16Lo12 m lM r ls ts ns mks := by
  unfold bEvalLo12 rkmEvalT16Lo12; dsimp only; rw [bEvalSegs_eq]; generalize altListLen ls = nS
  cases rkmEvalSegsLoop m lM r ls ts ns mks 1 0 0 [Int.ofNat wdScale] with
  | mk dE rest =>
    cases rest with
    | mk aP vF => cases nS <;> cases dE <;> cases aP <;> rfl
private theorem bCertRow {m lm r ls ts ns mks y}
    (h : muxNatListEq (bEvalLo12 m lm r ls ts ns mks) y = true) :
    rkmLo12EqHi m lm r ls ts ns mks y :=
  (bEvalLo12_eq m lm r ls ts ns mks).symm.trans (muxNatListEq_eq_true.mp h)
private theorem pbatch_m256_0 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 3 [1]
      [44919386]
      [5] rkmMasksHi_m256_r3) rkmRowHi_m256_r3,
    muxNatListEq (bEvalLo12 256 32 4 [1]
      [46063982]
      [6] rkmMasksHi_m256_r4) rkmRowHi_m256_r4,
    muxNatListEq (bEvalLo12 256 32 5 [1, 1]
      [37014165, 9744260]
      [6, 3] rkmMasksHi_m256_r5) rkmRowHi_m256_r5,
    muxNatListEq (bEvalLo12 256 32 6 [1, 1, 1, 1, 1, 1, 1, 1]
      [16831441, 17069434, 5713791, 3094959, 2264590, 1379868, 718544, 160275]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r6) rkmRowHi_m256_r6,
    muxNatListEq (bEvalLo12 256 32 7 [1, 1, 1, 1, 1, 1, 1, 1]
      [20902411, 20967411, 1904582, 1333212, 597294, 711306, 778246, 389118]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r7) rkmRowHi_m256_r7
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 3)`. -/
theorem rkmTrajHi_m256_r3 :
    rkmLo12EqHi 256 32 3 [1]
      [44919386]
      [5] rkmMasksHi_m256_r3 rkmRowHi_m256_r3 :=
  bCertRow (rkmHd pbatch_m256_0)
/-- Trajectory row certificate `(m = 256, r = 4)`. -/
theorem rkmTrajHi_m256_r4 :
    rkmLo12EqHi 256 32 4 [1]
      [46063982]
      [6] rkmMasksHi_m256_r4 rkmRowHi_m256_r4 :=
  bCertRow (rkmHd (rkmTl pbatch_m256_0))
/-- Trajectory row certificate `(m = 256, r = 5)`. -/
theorem rkmTrajHi_m256_r5 :
    rkmLo12EqHi 256 32 5 [1, 1]
      [37014165, 9744260]
      [6, 3] rkmMasksHi_m256_r5 rkmRowHi_m256_r5 :=
  bCertRow (rkmHd (rkmTl (rkmTl pbatch_m256_0)))
/-- Trajectory row certificate `(m = 256, r = 6)`. -/
theorem rkmTrajHi_m256_r6 :
    rkmLo12EqHi 256 32 6 [1, 1, 1, 1, 1, 1, 1, 1]
      [16831441, 17069434, 5713791, 3094959, 2264590, 1379868, 718544, 160275]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r6 rkmRowHi_m256_r6 :=
  bCertRow (rkmHd (rkmTl (rkmTl (rkmTl pbatch_m256_0))))
/-- Trajectory row certificate `(m = 256, r = 7)`. -/
theorem rkmTrajHi_m256_r7 :
    rkmLo12EqHi 256 32 7 [1, 1, 1, 1, 1, 1, 1, 1]
      [20902411, 20967411, 1904582, 1333212, 597294, 711306, 778246, 389118]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r7 rkmRowHi_m256_r7 :=
  bCertRow (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl pbatch_m256_0)))))
private theorem pbatch_m256_1 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 8 [1, 1, 1, 1, 1, 1, 1, 1]
      [21193512, 20950515, 1904591, 1033212, 681394, 702706, 807447, 584399]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r8) rkmRowHi_m256_r8,
    muxNatListEq (bEvalLo12 256 32 9 [1, 1, 1, 1, 1, 1, 1, 1]
      [21465057, 22402660, 404592, 901213, 602695, 700207, 864748, 740274]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r9) rkmRowHi_m256_r9
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 8)`. -/
theorem rkmTrajHi_m256_r8 :
    rkmLo12EqHi 256 32 8 [1, 1, 1, 1, 1, 1, 1, 1]
      [21193512, 20950515, 1904591, 1033212, 681394, 702706, 807447, 584399]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r8 rkmRowHi_m256_r8 :=
  bCertRow (rkmHd pbatch_m256_1)
/-- Trajectory row certificate `(m = 256, r = 9)`. -/
theorem rkmTrajHi_m256_r9 :
    rkmLo12EqHi 256 32 9 [1, 1, 1, 1, 1, 1, 1, 1]
      [21465057, 22402660, 404592, 901213, 602695, 700207, 864748, 740274]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r9 rkmRowHi_m256_r9 :=
  bCertRow (rkmHd (rkmTl pbatch_m256_1))
private theorem pbatch_m256_2 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 10 [1, 1, 1, 1, 1, 1, 1, 1]
      [21713584, 22402788, 344612, 721737, 636215, 698927, 887372, 864801]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r10) rkmRowHi_m256_r10,
    muxNatListEq (bEvalLo12 256 32 11 [1, 1, 1, 1, 1, 1, 1, 1]
      [20379255, 22413035, 1880859, 570885, 617759, 697271, 907589, 966651]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r11) rkmRowHi_m256_r11
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 10)`. -/
theorem rkmTrajHi_m256_r10 :
    rkmLo12EqHi 256 32 10 [1, 1, 1, 1, 1, 1, 1, 1]
      [21713584, 22402788, 344612, 721737, 636215, 698927, 887372, 864801]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r10 rkmRowHi_m256_r10 :=
  bCertRow (rkmHd pbatch_m256_2)
/-- Trajectory row certificate `(m = 256, r = 11)`. -/
theorem rkmTrajHi_m256_r11 :
    rkmLo12EqHi 256 32 11 [1, 1, 1, 1, 1, 1, 1, 1]
      [20379255, 22413035, 1880859, 570885, 617759, 697271, 907589, 966651]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r11 rkmRowHi_m256_r11 :=
  bCertRow (rkmHd (rkmTl pbatch_m256_2))
private theorem pbatch_m256_3 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 12 [1, 1, 1, 1, 1, 1]
      [20386171, 21888871, 2085265, 2369681, 1629666, 220064]
      [10, 10, 1, 1, 1, 1] rkmMasksHi_m256_r12) rkmRowHi_m256_r12
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 12)`. -/
theorem rkmTrajHi_m256_r12 :
    rkmLo12EqHi 256 32 12 [1, 1, 1, 1, 1, 1]
      [20386171, 21888871, 2085265, 2369681, 1629666, 220064]
      [10, 10, 1, 1, 1, 1] rkmMasksHi_m256_r12 rkmRowHi_m256_r12 :=
  bCertRow (rkmHd pbatch_m256_3)
private theorem pbatch_m256_4 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 13 [1, 1, 1, 1, 1, 1, 1, 1]
      [21225168, 21597189, 2026620, 1815971, 834547, 462559, 481573, 267305]
      [9, 10, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r13) rkmRowHi_m256_r13
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 13)`. -/
theorem rkmTrajHi_m256_r13 :
    rkmLo12EqHi 256 32 13 [1, 1, 1, 1, 1, 1, 1, 1]
      [21225168, 21597189, 2026620, 1815971, 834547, 462559, 481573, 267305]
      [9, 10, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r13 rkmRowHi_m256_r13 :=
  bCertRow (rkmHd pbatch_m256_4)
private theorem pbatch_m256_5 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 14 [1, 1, 1, 1, 1, 1, 1, 1]
      [21225108, 21717154, 1949613, 1852765, 793341, 436097, 540697, 316129]
      [9, 10, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r14) rkmRowHi_m256_r14
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 14)`. -/
theorem rkmTrajHi_m256_r14 :
    rkmLo12EqHi 256 32 14 [1, 1, 1, 1, 1, 1, 1, 1]
      [21225108, 21717154, 1949613, 1852765, 793341, 436097, 540697, 316129]
      [9, 10, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r14 rkmRowHi_m256_r14 :=
  bCertRow (rkmHd pbatch_m256_5)
private theorem pbatch_m256_6 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 15 [1, 1, 1, 1, 1, 1, 1, 1]
      [20618603, 22434745, 1883612, 1853285, 791561, 431525, 569827, 358907]
      [9, 10, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r15) rkmRowHi_m256_r15
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 15)`. -/
theorem rkmTrajHi_m256_r15 :
    rkmLo12EqHi 256 32 15 [1, 1, 1, 1, 1, 1, 1, 1]
      [20618603, 22434745, 1883612, 1853285, 791561, 431525, 569827, 358907]
      [9, 10, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r15 rkmRowHi_m256_r15 :=
  bCertRow (rkmHd pbatch_m256_6)
private theorem pbatch_m256_7 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 16 [1, 1, 1, 1, 1, 1, 1, 1]
      [23544244, 23560881, 32640, 30237, 701579, 780423, 210257, 185853]
      [10, 10, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r16) rkmRowHi_m256_r16
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 16)`. -/
theorem rkmTrajHi_m256_r16 :
    rkmLo12EqHi 256 32 16 [1, 1, 1, 1, 1, 1, 1, 1]
      [23544244, 23560881, 32640, 30237, 701579, 780423, 210257, 185853]
      [10, 10, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r16 rkmRowHi_m256_r16 :=
  bCertRow (rkmHd pbatch_m256_7)
private theorem pbatch_m256_8 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 17 [1, 1, 1, 1, 1, 1, 1, 1]
      [21703388, 21552900, 1737454, 1210405, 1544403, 809549, 156299, 429975]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r17) rkmRowHi_m256_r17
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 17)`. -/
theorem rkmTrajHi_m256_r17 :
    rkmLo12EqHi 256 32 17 [1, 1, 1, 1, 1, 1, 1, 1]
      [21703388, 21552900, 1737454, 1210405, 1544403, 809549, 156299, 429975]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r17 rkmRowHi_m256_r17 :=
  bCertRow (rkmHd pbatch_m256_8)
private theorem pbatch_m256_9 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 18 [1, 1, 1, 1, 1, 1, 1, 1]
      [21748829, 21601024, 1690378, 1211429, 1539007, 717929, 268974, 460266]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r18) rkmRowHi_m256_r18
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 18)`. -/
theorem rkmTrajHi_m256_r18 :
    rkmLo12EqHi 256 32 18 [1, 1, 1, 1, 1, 1, 1, 1]
      [21748829, 21601024, 1690378, 1211429, 1539007, 717929, 268974, 460266]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r18 rkmRowHi_m256_r18 :=
  bCertRow (rkmHd pbatch_m256_9)
private theorem pbatch_m256_10 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 19 [1, 1, 1, 1, 1, 1, 1, 1]
      [20621136, 22520696, 1941262, 1221529, 1512627, 576761, 445438, 487887]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r19) rkmRowHi_m256_r19
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 19)`. -/
theorem rkmTrajHi_m256_r19 :
    rkmLo12EqHi 256 32 19 [1, 1, 1, 1, 1, 1, 1, 1]
      [20621136, 22520696, 1941262, 1221529, 1512627, 576761, 445438, 487887]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r19 rkmRowHi_m256_r19 :=
  bCertRow (rkmHd pbatch_m256_10)
private theorem pbatch_m256_11 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 20 [1, 1, 1, 1, 1, 1, 1, 1]
      [20623614, 22604094, 1899461, 1215708, 1557226, 347964, 653437, 511991]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r20) rkmRowHi_m256_r20
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 20)`. -/
theorem rkmTrajHi_m256_r20 :
    rkmLo12EqHi 256 32 20 [1, 1, 1, 1, 1, 1, 1, 1]
      [20623614, 22604094, 1899461, 1215708, 1557226, 347964, 653437, 511991]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r20 rkmRowHi_m256_r20 :=
  bCertRow (rkmHd pbatch_m256_11)
private theorem pbatch_m256_12 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 21 [1, 1, 1, 1, 1, 1, 1, 1]
      [20630168, 22677348, 1867034, 1221086, 1526825, 479143, 558413, 536837]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r21) rkmRowHi_m256_r21
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 21)`. -/
theorem rkmTrajHi_m256_r21 :
    rkmLo12EqHi 256 32 21 [1, 1, 1, 1, 1, 1, 1, 1]
      [20630168, 22677348, 1867034, 1221086, 1526825, 479143, 558413, 536837]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r21 rkmRowHi_m256_r21 :=
  bCertRow (rkmHd pbatch_m256_12)
private theorem pbatch_m256_13 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 22 [1, 1, 1, 1, 1, 1, 1, 1]
      [20683976, 22689252, 1850042, 1201669, 1593104, 883404, 121364, 554998]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r22) rkmRowHi_m256_r22
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 22)`. -/
theorem rkmTrajHi_m256_r22 :
    rkmLo12EqHi 256 32 22 [1, 1, 1, 1, 1, 1, 1, 1]
      [20683976, 22689252, 1850042, 1201669, 1593104, 883404, 121364, 554998]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r22 rkmRowHi_m256_r22 :=
  bCertRow (rkmHd pbatch_m256_13)
private theorem pbatch_m256_14 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 23 [1, 1, 1, 1, 1, 1, 1, 1]
      [20753972, 22625148, 1885259, 1226989, 1527307, 463379, 597464, 577200]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r23) rkmRowHi_m256_r23
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 23)`. -/
theorem rkmTrajHi_m256_r23 :
    rkmLo12EqHi 256 32 23 [1, 1, 1, 1, 1, 1, 1, 1]
      [20753972, 22625148, 1885259, 1226989, 1527307, 463379, 597464, 577200]
      [11, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r23 rkmRowHi_m256_r23 :=
  bCertRow (rkmHd pbatch_m256_14)
private theorem pbatch_m256_15 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 24 [1, 1, 1, 1, 1, 1, 1, 2]
      [22784895, 22503395, 612690, 1345713, 921198, 974485, 590921, 8]
      [15, 15, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r24) rkmRowHi_m256_r24
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 24)`. -/
theorem rkmTrajHi_m256_r24 :
    rkmLo12EqHi 256 32 24 [1, 1, 1, 1, 1, 1, 1, 2]
      [22784895, 22503395, 612690, 1345713, 921198, 974485, 590921, 8]
      [15, 15, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r24 rkmRowHi_m256_r24 :=
  bCertRow (rkmHd pbatch_m256_15)
private theorem pbatch_m256_16 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 25 [1, 1, 1, 1, 1, 1, 1, 1]
      [22149767, 23188466, 617310, 1336404, 882867, 987714, 463195, 183812]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r25) rkmRowHi_m256_r25
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 25)`. -/
theorem rkmTrajHi_m256_r25 :
    rkmLo12EqHi 256 32 25 [1, 1, 1, 1, 1, 1, 1, 1]
      [22149767, 23188466, 617310, 1336404, 882867, 987714, 463195, 183812]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r25 rkmRowHi_m256_r25 :=
  bCertRow (rkmHd pbatch_m256_16)
private theorem pbatch_m256_17 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 26 [1, 1, 1, 1, 1, 1, 1, 1]
      [22323869, 23033270, 645615, 1320509, 878972, 995914, 439045, 246712]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r26) rkmRowHi_m256_r26
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 26)`. -/
theorem rkmTrajHi_m256_r26 :
    rkmLo12EqHi 256 32 26 [1, 1, 1, 1, 1, 1, 1, 1]
      [22323869, 23033270, 645615, 1320509, 878972, 995914, 439045, 246712]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r26 rkmRowHi_m256_r26 :=
  bCertRow (rkmHd pbatch_m256_17)
private theorem pbatch_m256_18 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 27 [1, 1, 1, 1, 1, 1, 1, 1]
      [23057569, 22350570, 637715, 1330109, 884472, 979314, 419943, 297612]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r27) rkmRowHi_m256_r27
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 27)`. -/
theorem rkmTrajHi_m256_r27 :
    rkmLo12EqHi 256 32 27 [1, 1, 1, 1, 1, 1, 1, 1]
      [23057569, 22350570, 637715, 1330109, 884472, 979314, 419943, 297612]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r27 rkmRowHi_m256_r27 :=
  bCertRow (rkmHd pbatch_m256_18)
private theorem pbatch_m256_19 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 28 [1, 1, 1, 1, 1, 1, 1, 1]
      [23820071, 21636972, 636517, 1334414, 885792, 970934, 423814, 321012]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r28) rkmRowHi_m256_r28
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 28)`. -/
theorem rkmTrajHi_m256_r28 :
    rkmLo12EqHi 256 32 28 [1, 1, 1, 1, 1, 1, 1, 1]
      [23820071, 21636972, 636517, 1334414, 885792, 970934, 423814, 321012]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r28 rkmRowHi_m256_r28 :=
  bCertRow (rkmHd pbatch_m256_19)
private theorem pbatch_m256_20 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 29 [1, 1, 1, 1, 1, 1, 1, 1]
      [24104671, 21394672, 643917, 1333414, 883992, 973434, 420314, 346412]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r29) rkmRowHi_m256_r29
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 29)`. -/
theorem rkmTrajHi_m256_r29 :
    rkmLo12EqHi 256 32 29 [1, 1, 1, 1, 1, 1, 1, 1]
      [24104671, 21394672, 643917, 1333414, 883992, 973434, 420314, 346412]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r29 rkmRowHi_m256_r29 :=
  bCertRow (rkmHd pbatch_m256_20)
private theorem pbatch_m256_21 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 30 [1, 1, 1, 1, 1, 1, 1, 1]
      [21415231, 23193716, 1005606, 1271334, 1543377, 872302, 195070, 674702]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r30) rkmRowHi_m256_r30
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 30)`. -/
theorem rkmTrajHi_m256_r30 :
    rkmLo12EqHi 256 32 30 [1, 1, 1, 1, 1, 1, 1, 1]
      [21415231, 23193716, 1005606, 1271334, 1543377, 872302, 195070, 674702]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r30 rkmRowHi_m256_r30 :=
  bCertRow (rkmHd pbatch_m256_21)
private theorem pbatch_m256_22 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 31 [1, 1, 1, 1, 1, 1, 1, 1]
      [21625274, 22633204, 1420437, 1313793, 1470364, 972071, 420009, 386660]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r31) rkmRowHi_m256_r31
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 31)`. -/
theorem rkmTrajHi_m256_r31 :
    rkmLo12EqHi 256 32 31 [1, 1, 1, 1, 1, 1, 1, 1]
      [21625274, 22633204, 1420437, 1313793, 1470364, 972071, 420009, 386660]
      [15, 16, 1, 1, 1, 1, 1, 1] rkmMasksHi_m256_r31 rkmRowHi_m256_r31 :=
  bCertRow (rkmHd pbatch_m256_22)
private theorem pbatch_m256_23 : rkmAllTrueF [
    muxNatListEq (bEvalLo12 256 32 32 [1, 1, 1, 1, 1, 1]
      [23488193, 23512805, 1464664, 1143840, 168284, 533376]
      [18, 18, 1, 1, 1, 1] rkmMasksHi_m256_r32) rkmRowHi_m256_r32
  ] = true := by
  decide +kernel
/-- Trajectory row certificate `(m = 256, r = 32)`. -/
theorem rkmTrajHi_m256_r32 :
    rkmLo12EqHi 256 32 32 [1, 1, 1, 1, 1, 1]
      [23488193, 23512805, 1464664, 1143840, 168284, 533376]
      [18, 18, 1, 1, 1, 1] rkmMasksHi_m256_r32 rkmRowHi_m256_r32 :=
  bCertRow (rkmHd pbatch_m256_23)

/-- Self-contained `0bar` lane witness for `FindAllJohnsonRampKickMuxHi256T0`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi256T0 :
    rkmTrajHi_m256_r3 = rkmTrajHi_m256_r3 := rfl
end
end QuantumComputation.Specs.DickeSol
