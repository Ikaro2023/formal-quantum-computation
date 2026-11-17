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
# High-`m` Trajectory Part `0` (`FindAllJohnsonRampKickMuxHi512T0`)

Certifies all `30` active `r = 3..32` Krotov rows for `m = 512` (`16895` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Prefix-kick masks for `(m = 512, r = 3)`. -/
def rkmMasksHi_m512_r3 : List (List Bool) := [[], [], [true, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 3)`. -/
def rkmRowHi_m512_r3 : List ℕ := [896804356, 53274040905, 945824718588]
/-- Prefix-kick masks for `(m = 512, r = 4)`. -/
def rkmMasksHi_m512_r4 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 4)`. -/
def rkmRowHi_m512_r4 : List ℕ := [2127671, 497341818, 39483847834, 960016680352]
/-- Prefix-kick masks for `(m = 512, r = 5)`. -/
def rkmMasksHi_m512_r5 : List (List Bool) := [[], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 5)`. -/
def rkmRowHi_m512_r5 : List ℕ := [270, 796057, 292801155, 31403656195, 968302746236]
/-- Prefix-kick masks for `(m = 512, r = 6)`. -/
def rkmMasksHi_m512_r6 : List (List Bool) := [[], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 6)`. -/
def rkmRowHi_m512_r6 : List ℕ := [0, 114, 208913, 176837057, 26091919736, 973731034083]
/-- Prefix-kick masks for `(m = 512, r = 7)`. -/
def rkmMasksHi_m512_r7 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 7)`. -/
def rkmRowHi_m512_r7 : List ℕ := [0, 1, 888, 14093, 106465524, 22332526157, 977560993238]
/-- Prefix-kick masks for `(m = 512, r = 8)`. -/
def rkmMasksHi_m512_r8 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 8)`. -/
def rkmRowHi_m512_r8 : List ℕ := [0, 0, 0, 1753, 23149, 62067635, 19531237543, 980406669800]
/-- Prefix-kick masks for `(m = 512, r = 9)`. -/
def rkmMasksHi_m512_r9 : List (List Bool) := [[], [], [], [], [], [false, false, false, true,
  true], [false, false, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 9)`. -/
def rkmRowHi_m512_r9 : List ℕ := [0, 0, 0, 0, 242, 135673, 33726074, 17363144804, 982602992936]
/-- Prefix-kick masks for `(m = 512, r = 10)`. -/
def rkmMasksHi_m512_r10 : List (List Bool) := [[], [], [], [], [], [false, false, false, false,
  false, true], [false, false, false, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 10)`. -/
def rkmRowHi_m512_r10 : List ℕ := [0, 0, 0, 0, 3, 1390, 304312, 15991741, 15635280217,
  984348422043]
/-- Prefix-kick masks for `(m = 512, r = 11)`. -/
def rkmMasksHi_m512_r11 : List (List Bool) := [[], [], [], [], [false, false, false, false,
  false, true], [false, false, false, false, false, true, true], [false, false, false, false,
  false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 11)`. -/
def rkmRowHi_m512_r11 : List ℕ := [0, 0, 0, 0, 0, 9, 3973, 500802, 5682868, 14225932661,
  985767879371]
/-- Prefix-kick masks for `(m = 512, r = 12)`. -/
def rkmMasksHi_m512_r12 : List (List Bool) := [[], [], [], [false, false, false, false, false,
  false, true, true], [false, false, false, false, false, false, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 12)`. -/
def rkmRowHi_m512_r12 : List ℕ := [0, 0, 0, 0, 0, 0, 36, 9752, 7296, 955377, 13054069364,
  986944957838]
/-- Prefix-kick masks for `(m = 512, r = 13)`. -/
def rkmMasksHi_m512_r13 : List (List Bool) := [[], [], [], [false, false, false, false, false,
  false, true, true], [false, false, false, false, false, false, false, false, true, true],
  [false, false, false, false, false, false, true, true, false, false, true], [false, false,
  false, false, false, false, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 13)`. -/
def rkmRowHi_m512_r13 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 267, 6, 165, 123328, 12064961119,
  987934914740]
/-- Prefix-kick masks for `(m = 512, r = 14)`. -/
def rkmMasksHi_m512_r14 : List (List Bool) := [[], [], [], [false, false, false, false, false,
  false, false, true, true], [false, false, false, false, false, false, false, false, false,
  true, true], [false, false, false, false, false, false, false, true, false, false, false,
  true], [false, false, false, false, false, false, false, false, true, false, false, true],
  []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 14)`. -/
def rkmRowHi_m512_r14 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 390, 13, 846, 2515600, 11218533904,
  988778948847]
/-- Prefix-kick masks for `(m = 512, r = 15)`. -/
def rkmMasksHi_m512_r15 : List (List Bool) := [[false, false, false, false, false, false,
  false, true, false, true, true, true], [false, false, false, false, false, false, false,
  false, false, true, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 15)`. -/
def rkmRowHi_m512_r15 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 12, 8, 31248, 1417904, 188133,
  10481627528, 989516734776]
/-- Prefix-kick masks for `(m = 512, r = 16)`. -/
def rkmMasksHi_m512_r16 : List (List Bool) := [[false, false, false, false, false, false,
  false, false, false, true, true, true, true], [false, false, false, false, false, false,
  false, false, false, false, true, false, false, true], [false, false, false, false, false,
  false, false, false, false, true, true, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 16)`. -/
def rkmRowHi_m512_r16 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 831, 116, 2203, 497640,
  9840318758, 990159180029]
/-- Prefix-kick masks for `(m = 512, r = 17)`. -/
def rkmMasksHi_m512_r17 : List (List Bool) := [[false, false, false, false, false, false,
  false, false, false, true, true, true, true, true], [false, false, false, false, false,
  false, false, false, false, false, false, true, true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 17)`. -/
def rkmRowHi_m512_r17 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 66, 50283, 2039731,
  846914, 9275305495, 990721756989]
/-- Prefix-kick masks for `(m = 512, r = 18)`. -/
def rkmMasksHi_m512_r18 : List (List Bool) := [[], [], [], [false, false, false, false, false,
  false, false, false, false, false, false, true, true], [false, false, false, false, false,
  false, false, false, false, false, false, true, true, true, true], [false, false, false,
  false, false, false, false, false, false, false, true, false, true, false, true, true],
  [false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 18)`. -/
def rkmRowHi_m512_r18 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 40, 2347, 0, 1549, 1405497,
  8773668691, 991224921288]
/-- Prefix-kick masks for `(m = 512, r = 19)`. -/
def rkmMasksHi_m512_r19 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, false, false, true], [false, false, false, false, false, false, false, false,
  false, false, false, true, true, true], [false, false, false, false, false, false, false,
  false, false, false, false, false, true, true, false, true], [false, false, false, false,
  false, false, false, false, false, false, false, true, false, true, true, true, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 19)`. -/
def rkmRowHi_m512_r19 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 44, 2606, 413, 906,
  1949743, 8325270230, 991672775437]
/-- Prefix-kick masks for `(m = 512, r = 20)`. -/
def rkmMasksHi_m512_r20 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, true], [], [false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true], [false, false, false, false, false, false, false,
  false, false, false, false, true, false, true, true, false, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, true, true, true, true, true,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 20)`. -/
def rkmRowHi_m512_r20 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 42, 3292, 513, 310,
  2536741, 7922114752, 992075343661]
/-- Prefix-kick masks for `(m = 512, r = 21)`. -/
def rkmMasksHi_m512_r21 : List (List Bool) := [[false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, true], [false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false,
  true, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 21)`. -/
def rkmRowHi_m512_r21 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 334, 19358, 15106,
  4180713, 2780554, 7557661789, 992435341484]
/-- Prefix-kick masks for `(m = 512, r = 22)`. -/
def rkmMasksHi_m512_r22 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, false, false, true], [], [false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true,
  true, false, true], [false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, false, true, true, true], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, true, false,
  true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 22)`. -/
def rkmRowHi_m512_r22 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 308, 10635, 41,
  133691, 6669185, 7214134487, 992779050858]
/-- Prefix-kick masks for `(m = 512, r = 23)`. -/
def rkmMasksHi_m512_r23 : List (List Bool) := [[], [], [], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, true, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, false, true], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, true, true, true, true,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, true, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 23)`. -/
def rkmRowHi_m512_r23 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 105, 7213,
  1744, 258, 4389829, 6924729476, 993070870547]
/-- Prefix-kick masks for `(m = 512, r = 24)`. -/
def rkmMasksHi_m512_r24 : List (List Bool) := [[], [], [], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, true, true, true], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false,
  true, true, false, true, true], [false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, false,
  true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 24)`. -/
def rkmRowHi_m512_r24 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 238, 98,
  10680, 188, 320, 5019541, 6648141639, 993346826428]
/-- Prefix-kick masks for `(m = 512, r = 25)`. -/
def rkmMasksHi_m512_r25 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true], [false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, true], [false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, true, true, true, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, false, true, true, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 25)`. -/
def rkmRowHi_m512_r25 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 207,
  11134, 2053, 456, 5640244, 6393804097, 993600540908]
/-- Prefix-kick masks for `(m = 512, r = 26)`. -/
def rkmMasksHi_m512_r26 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, true], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, true, true], [false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, true, false, false,
  false, true], [false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, false, true, false, false, false,
  true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 26)`. -/
def rkmRowHi_m512_r26 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45,
  31, 8038, 2677, 1545, 6186574, 6159194754, 993834605388]
/-- Prefix-kick masks for `(m = 512, r = 27)`. -/
def rkmMasksHi_m512_r27 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, true, true, true], [false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, true], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, true, false, true, false, true], [false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 27)`. -/
def rkmRowHi_m512_r27 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0,
  242, 15423, 266, 112, 6834216, 5942084341, 994051064395]
/-- Prefix-kick masks for `(m = 512, r = 28)`. -/
def rkmMasksHi_m512_r28 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, true, true], [false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, false, true, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, false, false, false, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 28)`. -/
def rkmRowHi_m512_r28 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4,
  1, 36, 11076, 4380, 3339, 7343794, 5740661562, 994251974736]
/-- Prefix-kick masks for `(m = 512, r = 29)`. -/
def rkmMasksHi_m512_r29 : List (List Bool) := [[], [], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, true, false, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true, false, false, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, true, false, false, false, true],
  [false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, false,
  false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 29)`. -/
def rkmRowHi_m512_r29 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  8, 16, 43, 13048, 5231, 4621, 7902468, 5553186336, 994438887057]
/-- Prefix-kick masks for `(m = 512, r = 30)`. -/
def rkmMasksHi_m512_r30 : List (List Bool) := [[false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, true], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, true, false, false, true, true], [false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, false, true, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 30)`. -/
def rkmRowHi_m512_r30 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 9, 1019, 118523, 1, 13072878, 1952950, 5376264846, 994608588471]
/-- Prefix-kick masks for `(m = 512, r = 31)`. -/
def rkmMasksHi_m512_r31 : List (List Bool) := [[false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, true, true], [false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, true, false, false, true, true], [false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, false,
  true, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 31)`. -/
def rkmRowHi_m512_r31 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 18, 1384, 138556, 29, 14130501, 1578944, 5213580963, 994770568217]
/-- Prefix-kick masks for `(m = 512, r = 32)`. -/
def rkmMasksHi_m512_r32 : List (List Bool) := [[], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, false,
  true, true, true, true, true, true], [false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, true, false,
  false, false, true, false, true, true, true], [false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, false, true, false, false, false, true, true], [false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, true, true, false, false,
  true], [false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true], [false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, false, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 32)`. -/
def rkmRowHi_m512_r32 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 14, 79, 294, 4925, 578803, 37257, 3967013, 5057409043, 994938001172]

end

public section

private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: pCat xs ys
private def atF : List Bool → Bool
  | [] => true
  | true :: bs => atF bs
  | false :: _ => false
private theorem tl1 : ∀ {b : Bool} {s : List Bool}, atF (b :: s) = true → atF s = true
  | false, _, h => Bool.noConfusion h
  | true, _, h => h
private theorem tl2 {a b : Bool} {s : List Bool} (h : atF (a :: b :: s) = true) :
    atF s = true := tl1 (tl1 h)
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β :=
  HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := Nat.one_add x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem bForceNat_eq {α : Type} (x : ℕ) (k : ℕ → α) :
    HighDForce.withForcedNat x k = k x := by
  unfold HighDForce.withForcedNat
  rw [n1a]
private theorem bForceList_eq {α β : Type} (xs : List α) (k : List α → β) :
    HighDForce.withForcedList xs k = k xs := by cases xs <;> rfl
private theorem bNatBle_le : ∀ {a b : ℕ}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (bNatBle_le h)
private def bNatEq (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem bNatEq_true {a b : ℕ} (h : bNatEq a b = true) : a = b := by
  unfold bNatEq at h
  revert h
  cases h1 : Nat.ble a b with
  | false => exact Bool.noConfusion
  | true =>
    cases h2 : Nat.ble b a with
    | false => exact Bool.noConfusion
    | true => exact fun _ => Nat.le_antisymm (bNatBle_le h1) (bNatBle_le h2)
private def bNatListEq : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => cond (bNatEq x y) (bNatListEq xs ys) false
  | _, _ => false
private theorem bNatListEq_true : ∀ {xs ys : List ℕ}, bNatListEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    unfold bNatListEq at h
    revert h
    cases hx : bNatEq x y with
    | false => exact Bool.noConfusion
    | true => exact fun h => congrArg₂ List.cons (bNatEq_true hx) (bNatListEq_true h)
private def bIntEq : ℤ → ℤ → Bool
  | Int.ofNat a, Int.ofNat b => bNatEq a b
  | Int.negSucc a, Int.negSucc b => bNatEq a b
  | _, _ => false
private theorem bIntEq_true : ∀ {a b : ℤ}, bIntEq a b = true → a = b
  | Int.ofNat _, Int.ofNat _, h => congrArg Int.ofNat (bNatEq_true h)
  | Int.negSucc _, Int.negSucc _, h => congrArg Int.negSucc (bNatEq_true h)
  | Int.ofNat _, Int.negSucc _, h => Bool.noConfusion h
  | Int.negSucc _, Int.ofNat _, h => Bool.noConfusion h
private def bIntListEq : List ℤ → List ℤ → Bool
  | [], [] => true
  | x :: xs, y :: ys => cond (bIntEq x y) (bIntListEq xs ys) false
  | _, _ => false
private theorem bIntListEq_true : ∀ {xs ys : List ℤ}, bIntListEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    unfold bIntListEq at h
    revert h
    cases hx : bIntEq x y with
    | false => exact Bool.noConfusion
    | true => exact fun h => congrArg₂ List.cons (bIntEq_true hx) (bIntListEq_true h)
private theorem bhd_eq {x y : List ℕ} {s : List Bool}
    (h : atF (bNatListEq x y :: s) = true) : x = y := by
  revert h
  cases h0 : bNatListEq x y with
  | false => exact Bool.noConfusion
  | true => exact fun _ => bNatListEq_true h0
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs
  | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat
  rw [n1a]
  cases xs <;> rfl
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | Int.ofNat n :: xs =>
    match uToNatHb xs with | some ns => some (uConsNat n ns) | none => none
  | Int.negSucc _ :: _ => none
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfNatHb ns
private theorem uToNatHb_sound :
    ∀ (hb : List ℤ) (ns : List ℕ), uToNatHb hb = some ns → hb = uOfNatHb ns
  | [], ns, h => by
    injection h with h'
    subst h'
    rfl
  | Int.negSucc _ :: _, _, h => by
    dsimp only [uToNatHb] at h
    cases h
  | Int.ofNat n :: xs, ns, h => by
    dsimp only [uToNatHb] at h
    revert h
    cases hxs : uToNatHb xs with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some ms =>
      intro h
      dsimp only at h
      injection h with h'
      subst h'
      rw [uConsNat_eq, uOfNatHb, uToNatHb_sound xs ms hxs]
private theorem bPrimOfNat_eq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  unfold primOfNatForced
  rw [n1a]
private theorem bPrimNegSucc_eq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  unfold primNegSuccForced
  rw [n1a]
private theorem bPrimNegOfNat_eq : ∀ (x : ℕ), primNegOfNat x = -(x : ℤ)
  | 0 => by
    dsimp only [primNegOfNat]
    rw [Int.ofNat_eq_natCast]
    omega
  | k + 1 => by
    dsimp only [primNegOfNat]
    rw [bPrimNegSucc_eq, Int.negSucc_eq]
    omega
private theorem bPrimSubNat_eq (m n : ℕ) : primSubNatNat m n = (m : ℤ) - (n : ℤ) := by
  unfold primSubNatNat
  simp only [Nat.sub_eq]
  cases h : n - m with
  | zero =>
    dsimp only
    rw [bPrimOfNat_eq, Int.ofNat_eq_natCast]
    omega
  | succ k =>
    dsimp only
    rw [bPrimNegSucc_eq, Int.negSucc_eq]
    omega
private theorem bPrimMul_eq (a b : ℤ) : primIntMul a b = a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      dsimp only [primIntMul]
      simp only [bPrimOfNat_eq, Nat.mul_eq, Int.ofNat_eq_natCast]
      push_cast
      ring
    | negSucc n =>
      dsimp only [primIntMul]
      simp only [bPrimNegOfNat_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
  | negSucc m =>
    cases b with
    | ofNat n =>
      dsimp only [primIntMul]
      simp only [bPrimNegOfNat_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
    | negSucc n =>
      dsimp only [primIntMul]
      simp only [bPrimOfNat_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
private def bConsZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
  | Int.ofNat v => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v =>
    match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t
private theorem bConsZ_eq (x : ℤ) (xs : List ℤ) : bConsZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem bStrictCons_eq (x : ℤ) (xs : List ℤ) :
    highdStrictConsInt x xs = x :: xs := by
  cases x with
  | ofNat n =>
    unfold highdStrictConsInt
    dsimp only
    rw [n1a]
    cases xs <;> rfl
  | negSucc n =>
    unfold highdStrictConsInt
    dsimp only
    rw [n1a]
    cases xs <;> rfl
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bConsZ (primSubNatNat u z) (bDec z us)
private theorem bDec_nil (z : ℕ) : bDec z [] = [] := rfl
private theorem bDec_cons (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by
  rw [bDec, bConsZ_eq, bPrimSubNat_eq]
private theorem bDec_len (z : ℕ) : ∀ (cs : List ℕ), altIntLen (bDec z cs) = altListLen cs
  | [] => rfl
  | _ :: cs => by rw [bDec_cons, altIntLen, altListLen, bDec_len z cs]
private theorem bZero_eq (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]
  omega
private theorem bPrimMul0 (z : ℕ) :
    primIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bPrimMul_eq, bZero_eq]
  rfl
private def bEnc1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k =>
    match Nat.sub z (Nat.add k 1) with | 0 => none | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs => match bEnc1 z x with
    | none => none
    | some u => match bEnc z xs with | none => none | some us => some (uConsNat u us)
private theorem bEnc1_sound (z : ℕ) (x : ℤ) (u : ℕ) (h : bEnc1 z x = some u) :
    ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bEnc1 at h
    injection h with h'
    subst h'
    rw [Nat.add_eq, Int.ofNat_eq_natCast]
    omega
  | negSucc k =>
    unfold bEnc1 at h
    simp only [Nat.sub_eq, Nat.add_eq] at h
    revert h
    cases hz : z - (k + 1) with
    | zero =>
      intro h
      dsimp only at h
      cases h
    | succ w =>
      intro h
      dsimp only at h
      injection h with h'
      subst h'
      rw [Int.negSucc_eq]
      omega
private theorem bEnc_sound (z : ℕ) :
    ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us → bDec z us = xs
  | [], us, h => by
    injection h with h'
    subst h'
    rfl
  | x :: xs, us, h => by
    dsimp only [bEnc] at h
    revert h
    cases hx : bEnc1 z x with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some u =>
      dsimp only
      cases hxs : bEnc z xs with
      | none =>
        intro h
        dsimp only at h
        cases h
      | some ws =>
        intro h
        dsimp only at h
        injection h with h'
        subst h'
        rw [uConsNat_eq, bDec_cons, bEnc1_sound z x u hx, bEnc_sound z xs ws hxs]
private def zTdiv (x : ℤ) (d : ℕ) : ℤ := match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.ofNat_eq_natCast]
    omega
  | k + 1 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.negSucc_eq]
    omega
private theorem bTdivNat_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by
    dsimp only [muxRawIntTdivNat, zTdiv]
    rw [bNeg_eq, ndiv, Nat.add_eq]
private theorem bRawSubNat_eq (m n : ℕ) : muxRawSubNatNat m n = (m : ℤ) - (n : ℤ) := by
  unfold muxRawSubNatNat
  simp only [Nat.sub_eq]
  cases h : n - m with
  | zero =>
    dsimp only
    rw [Int.ofNat_eq_natCast]
    omega
  | succ k =>
    dsimp only
    rw [Int.negSucc_eq]
    omega
private theorem bRawAdd_eq (a b : ℤ) : muxRawIntAdd a b = a + b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      dsimp only [muxRawIntAdd]
      simp only [bPrimOfNat_eq, Nat.add_eq, Int.ofNat_eq_natCast]
      omega
    | negSucc n =>
      dsimp only [muxRawIntAdd]
      simp only [bRawSubNat_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
  | negSucc m =>
    cases b with
    | ofNat n =>
      dsimp only [muxRawIntAdd]
      simp only [bRawSubNat_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
    | negSucc n =>
      dsimp only [muxRawIntAdd]
      simp only [bPrimNegSucc_eq, Nat.add_eq, Int.negSucc_eq]
      omega
private theorem bRawNeg_eq (a : ℤ) : muxRawIntNeg a = -a := by
  cases a with
  | ofNat n =>
    dsimp only [muxRawIntNeg]
    simp only [bNeg_eq, Int.ofNat_eq_natCast]
  | negSucc n =>
    dsimp only [muxRawIntNeg]
    simp only [bPrimOfNat_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
private theorem bRawSub_eq (a b : ℤ) : muxRawIntSub a b = a - b := by
  unfold muxRawIntSub
  rw [bRawAdd_eq, bRawNeg_eq]
  omega
private theorem bRawMul_eq (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
      push_cast
      ring
    | negSucc n =>
      dsimp only [muxRawIntMul]
      simp only [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
  | negSucc m =>
    cases b with
    | ofNat n =>
      dsimp only [muxRawIntMul]
      simp only [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
    | negSucc n =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
private def bStepVal (v P Q d : ℕ) : ℕ :=
  fN P fun p => fN Q fun q => match Nat.sub q p with
  | 0 => Nat.add v (Nat.div (Nat.sub p q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) =
      ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  unfold bStepVal at hv ⊢
  dsimp only [fN] at hv ⊢
  rw [bForceNat_eq, bForceNat_eq] at hv ⊢
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢
  revert hv
  cases h : Q - P with
  | zero =>
    intro _
    have hm : (P : ℤ) - (Q : ℤ) = Int.ofNat (P - Q) := by
      rw [Int.ofNat_eq_natCast]
      omega
    rw [hm]
    dsimp only [zTdiv]
    rw [Int.ofNat_eq_natCast]
    push_cast
    ring
  | succ k =>
    intro hv
    have hm : (P : ℤ) - (Q : ℤ) = Int.negSucc k := by
      rw [Int.negSucc_eq]
      omega
    rw [hm]
    dsimp only [zTdiv] at hv ⊢
    omega
private abbrev bCellVal (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) (Nat.mul b z))
    (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCellVal z d b0 c0 b v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCellVal z d b0 c0 b v c1) rest) =
      highdStrictConsInt (muxRawIntAdd ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntSub (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ)))) d)) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bStrictCons_eq, bRawAdd_eq, bTdivNat_eq, bRawSub_eq,
    bPrimMul_eq, bRawMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
  unfold bCellVal at hv ⊢
  rw [bStepVal_eq z v _ _ d hv, hpq]
private theorem bCell_nil (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      highdStrictConsInt (muxRawIntAdd ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d)) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bStrictCons_eq, bRawAdd_eq, bTdivNat_eq, bPrimMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
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
      (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by
    unfold bHeadOr
    rw [bDec_nil, bZero_eq]
  | c :: cs => by
    unfold bHeadOr
    rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | x :: xs => by
    unfold bTailN
    rw [bDec_cons]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs => match bns with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSlide z d rem 0 z [] (bTailN vs) (bTailN cs))
    | b :: bR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal z d b0 c0 b v (bHeadOr z cT)) (bSlide z d rem b c bR vT cT)
      | v :: vT, [] => uConsNat (bCellVal z d b0 c0 b v z) (bSlide z d rem b z bR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal z d b0 c0 b z (bHeadOr z cT)) (bSlide z d rem b c bR [] cT)
      | [], [] => uConsNat (bCellVal z d b0 c0 b z z) (bSlide z d rem b z bR [] [])
private theorem bSlide_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSlide z d rem b0 c0 bns vs cs) = true →
      bDec z (bSlide z d rem b0 c0 bns vs cs) =
      muxFastSlideLoopAux d rem (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSlide, uOfNatHb, muxFastSlideLoopAux] at h ⊢
      have hp := bAllPos_uCons h
      have hi := bSlide_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp.2
      rw [bPrimMul0 z, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi
      rw [bHeadOr_eq z vs] at hc
      exact hc
    | cons b bR =>
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢
          rw [bDec_nil]
          dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b z bR [] [] hp.2
          rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b z z hp.1 hi
          rw [bZero_eq z] at hc
          exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfNatHb] at h ⊢
          rw [bDec_nil, bDec_cons z c cT]
          dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b c bR [] cT hp.2
          rw [bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b z (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT, bZero_eq z] at hc
          exact hc
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢
          rw [bDec_cons z v vT, bDec_nil]
          dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b z bR vT [] hp.2
          rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b v z hp.1 hi
          rw [bZero_eq z] at hc
          exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfNatHb] at h ⊢
          rw [bDec_cons z v vT, bDec_cons z c cT]
          dsimp only [muxFastSlideLoopAux]
          have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b c bR vT cT hp.2
          have hc := bCell_hb z d b0 c0 b v (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT] at hc
          exact hc
private def bStg (z dg mL : ℕ) (bns vns cns : List ℕ) : Option (List ℕ) :=
  fN (highdNatMin mL (Nat.add (altListLen cns) 1)) fun nL =>
    fN (Nat.mul dg wdScale) fun d =>
      fL (bSlide z d nL 0 z bns vns cns) fun out => cond (bAllPos out) (some out) none
private theorem bStg_sound (z dg mL : ℕ) (bns vns cns out : List ℕ)
    (h : bStg z dg mL bns vns cns = some out) :
    bDec z out = muxFastHornerStage dg mL (uOfNatHb bns) (bDec z vns) (bDec z cns) := by
  unfold bStg at h
  dsimp only [fN, fL] at h
  rw [bForceNat_eq, bForceNat_eq, bForceList_eq] at h
  revert h
  set nL := highdNatMin mL (Nat.add (altListLen cns) 1)
  set d := Nat.mul dg wdScale
  cases hp : bAllPos (bSlide z d nL 0 z bns vns cns) with
  | false =>
    intro h
    dsimp only [cond] at h
    cases h
  | true =>
    intro h
    dsimp only [cond] at h
    injection h with h'
    subst h'
    unfold muxFastHornerStage
    rw [bDec_len z cns, bForceNat_eq, bForceNat_eq, ← bPrimMul0 z]
    exact bSlide_sound z d nL 0 z bns vns cns hp
private def bBind (x : Option (List ℕ)) (k : List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  match x with | none => none | some out => k out
private theorem bBind_sound {z dg mL : ℕ} {bns vns cns out : List ℕ}
    {kB : List ℕ → Option (List ℕ)} {kU : List ℤ → List ℤ}
    (h : bBind (bStg z dg mL bns vns cns) kB = some out)
    (hk : ∀ (mid : List ℕ), kB mid = some out → bDec z out = kU (bDec z mid)) :
    bDec z out = HighDForce.withForcedList
      (muxFastHornerStage dg mL (uOfNatHb bns) (bDec z vns) (bDec z cns)) kU := by
  unfold bBind at h
  revert h
  cases hs : bStg z dg mL bns vns cns with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some mid =>
    intro h
    dsimp only at h
    rw [bForceList_eq, ← bStg_sound z dg mL bns vns cns mid hs]
    exact hk mid h
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
  unfold bStep at h
  unfold muxFastHornerT16Step
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  exact bStg_sound _ _ _ _ _ _ _ h
private def bIter (z : ℕ) : ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, vns => some vns
  | k + 1, mL, bns, vns => match bStep z mL bns vns with
    | none => none
    | some vNext => bIter z k mL bns vNext
private theorem bIter_sound (z : ℕ) : ∀ (k mL : ℕ) (bns vns out : List ℕ),
    bIter z k mL bns vns = some out →
    bDec z out = muxFastIterFullT16 k mL (uOfNatHb bns) (bDec z vns)
  | 0, _, _, vns, out, h => by
    dsimp only [bIter] at h
    injection h with h'
    subst h'
    rfl
  | k + 1, mL, bns, vns, out, h => by
    dsimp only [bIter] at h
    revert h
    cases hs : bStep z mL bns vns with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some vNext =>
      intro h
      dsimp only at h
      unfold muxFastIterFullT16
      rw [bForceList_eq, ← bStep_sound z mL bns vns vNext hs]
      exact bIter_sound z k mL bns vNext out h
private abbrev zB : ℕ := 2000000000000000
private def fIter (k mL : ℕ) (hb v : List ℤ) : List ℤ := match uToNatHb hb with
  | none => muxFastIterFullT16 k mL hb v
  | some bns => match bEnc zB v with
    | none => muxFastIterFullT16 k mL hb v
    | some vns => match bIter zB k mL bns vns with
      | none => muxFastIterFullT16 k mL hb v
      | some out => bDec zB out
private theorem fIter_eq (k mL : ℕ) (hb v : List ℤ) :
    fIter k mL hb v = muxFastIterFullT16 k mL hb v := by
  unfold fIter
  cases hh : uToNatHb hb with
  | none => rfl
  | some bns =>
    dsimp only
    cases hv : bEnc zB v with
    | none => rfl
    | some vns =>
      dsimp only
      cases hi : bIter zB k mL bns vns with
      | none => rfl
      | some out =>
        dsimp only
        rw [bIter_sound zB k mL bns vns out hi, ← uToNatHb_sound hb bns hh,
          bEnc_sound zB v vns hv]
private theorem mIter_add : ∀ (k1 k2 mL : ℕ) (hb v : List ℤ),
    muxFastIterFullT16 (k1 + k2) mL hb v =
      muxFastIterFullT16 k2 mL hb (muxFastIterFullT16 k1 mL hb v)
  | 0, k2, mL, hb, v => congrArg (fun n => muxFastIterFullT16 n mL hb v) (Nat.zero_add k2)
  | k1 + 1, k2, mL, hb, v => by
    have hk : k1 + 1 + k2 = (k1 + k2) + 1 := by omega
    rw [hk]
    dsimp only [muxFastIterFullT16]
    rw [bForceList_eq, bForceList_eq]
    exact mIter_add k1 k2 mL hb (muxFastHornerT16Step mL hb v)
private abbrev WalkCert : Type := Option (ℕ × ℕ × List ℕ × List ℕ × List ℕ)
private def WalkOk : WalkCert → Prop
  | none => True
  | some (kE, mE, bns, vns, out) =>
    muxFastIterFullT16 kE mE (uOfNatHb bns) (bDec zB vns) = bDec zB out
private def WalksOk : List WalkCert → Prop
  | [] => True
  | wc :: wcs => WalkOk wc ∧ WalksOk wcs
private theorem wNil : WalksOk [] := trivial
private theorem wSkip {wcs : List WalkCert} (hw : WalksOk wcs) :
    WalksOk (none :: wcs) := And.intro trivial hw
private theorem wCons {wc : WalkCert} {wcs : List WalkCert}
    (h1 : WalkOk wc) (h2 : WalksOk wcs) : WalksOk (wc :: wcs) := And.intro h1 h2
private def bSlideChk (k mL : ℕ) (bns vns out : List ℕ) : Bool :=
  match bIter zB k mL bns vns with | none => false | some w => bNatListEq w out
private theorem bSlideChk_sound {k mL : ℕ} {bns vns out : List ℕ} {s : List Bool}
    (h : atF (bSlideChk k mL bns vns out :: s) = true) :
    WalkOk (some (k, mL, bns, vns, out)) := by
  unfold bSlideChk at h
  unfold WalkOk
  revert h
  cases hi : bIter zB k mL bns vns with
  | none =>
    intro h
    dsimp only [atF] at h
    cases h
  | some w =>
    intro h
    dsimp only at h
    rw [← bhd_eq h]
    exact (bIter_sound zB k mL bns vns w hi).symm
private theorem mIter_split {k1 k2 kS mL : ℕ} {bns v0 v1 v2 : List ℕ}
    (hk : k1 + k2 = kS) (h1 : WalkOk (some (k1, mL, bns, v0, v1)))
    (h2 : WalkOk (some (k2, mL, bns, v1, v2))) : WalkOk (some (kS, mL, bns, v0, v2)) := by
  unfold WalkOk at h1 h2 ⊢
  dsimp only at h1 h2 ⊢
  rw [← hk, mIter_add, h1, h2]
private def wIter (k mL : ℕ) (hb v : List ℤ) : WalkCert → List ℤ
  | none => fIter k mL hb v
  | some (kE, mE, bns, vns, out) =>
    cond (Bool.and (bNatEq k kE) (Bool.and (bNatEq mL mE)
      (Bool.and (bIntListEq hb (uOfNatHb bns)) (bIntListEq v (bDec zB vns)))))
      (bDec zB out) (muxFastIterFullT16 k mL hb v)
private theorem wIter_eq (k mL : ℕ) (hb v : List ℤ) (wc : WalkCert) (hw : WalkOk wc) :
    wIter k mL hb v wc = muxFastIterFullT16 k mL hb v := by
  cases wc with
  | none => exact fIter_eq k mL hb v
  | some tup =>
    rcases tup with ⟨kE, mE, bns, vns, out⟩
    unfold WalkOk at hw
    dsimp only at hw
    unfold wIter
    dsimp only
    cases hk : bNatEq k kE with
    | false => rfl
    | true =>
      cases hm : bNatEq mL mE with
      | false => rfl
      | true =>
        cases hh : bIntListEq hb (uOfNatHb bns) with
        | false => rfl
        | true =>
          cases hv : bIntListEq v (bDec zB vns) with
          | false => rfl
          | true =>
            dsimp only [Bool.and, cond]
            rw [bNatEq_true hk, bNatEq_true hm, bIntListEq_true hh, bIntListEq_true hv]
            exact hw.symm
private def wHead : List WalkCert → WalkCert
  | [] => none
  | wc :: _ => wc
private def wTail : List WalkCert → List WalkCert
  | [] => []
  | _ :: wcs => wcs
private theorem wHead_ok : ∀ {wcs : List WalkCert}, WalksOk wcs → WalkOk (wHead wcs)
  | [], _ => trivial
  | _ :: _, h => h.1
private theorem wTail_ok : ∀ {wcs : List WalkCert}, WalksOk wcs → WalksOk (wTail wcs)
  | [], _ => trivial
  | _ :: _, h => h.2
private def bEvalSegsW (m lM r : ℕ) :
    List ℕ → List ℕ → List ℕ → List (List Bool) → List WalkCert →
      ℕ → ℕ → ℕ → List ℤ → (ℕ × ℕ × List ℤ)
  | [], tR, nR, mR, _, _, dE, aP, v =>
    match tR, nR, mR with | [], [], [] => (dE, aP, v) | _, _, _ => (0, 0, [])
  | lS :: lR, t9 :: tR, nS :: nR, mk :: mR, wcs, lP, _, aP, v =>
    let mE := Nat.mul lS m
    let d := highdNatMin mE r
    cond (Bool.or (primNatBlt lS 1) (Bool.or (primNatBlt lS lP) (Bool.or (primNatBlt lM lS)
      (Bool.or (primNatBlt mE 1) (Bool.or (primNatBlt 8192 mE) (Bool.or (primNatBlt d 1)
      (Bool.or (Nat.ble t9 0) (Bool.or (primNatBlt 4000000000 t9) (Bool.or (Nat.ble nS 0)
      (Bool.or (primNatBlt 16384 nS)
        (primNatBlt (Nat.add d 1) (rkmBoolListLen mk))))))))))))
      (0, 0, [])
      (fN (Nat.div (Nat.mul t9 1000000) nS) fun hPt =>
        cond (primNatBlt hPt 1) (0, 0, [])
          (fN (altMaxBHiFrom mE r 0 d) fun bHi =>
            let bCap := Nat.mul 2 bHi
            fN (highdMulCeil15 (Nat.add 2 hPt) bCap) fun hgHi =>
              cond (Bool.or (primNatBlt 1500000000000000 hgHi)
                  (Bool.not (altCheckHbTight mE r 0 d))) (0, 0, [])
                (let hgP := altPow17Ceil15 hgHi
                let trP := Nat.div (Nat.add 299999999999999 (Nat.mul nS hgP))
                  300000000000000
                let bCeil := Nat.div (Nat.add 999999999999999 bCap) wdScale
                let sPad := Nat.add (Nat.add trP 256)
                  (Nat.mul nS (Nat.add 256 (Nat.mul 10 bCeil)))
                fN (Nat.add aP sPad) fun np =>
                  cond (Bool.or (Nat.ble np 0) (primNatBlt 100000000000000 np)) (0, 0, [])
                    (fL (altBuildHbFrom mE r hPt 0 d) fun hbP =>
                      fL (wIter nS (Nat.add d 1) hbP v (wHead wcs)) fun vW =>
                        fL (rkmApplyMaskBits mk vW) fun vN =>
                          bEvalSegsW m lM r lR tR nR mR (wTail wcs) lS d np vN))))
  | _, _, _, _, _, _, _, _, _ => (0, 0, [])
private theorem bEvalSegsW_eq (m lM r : ℕ) :
    ∀ (ls ts ns : List ℕ) (mks : List (List Bool)) (wcs : List WalkCert),
      WalksOk wcs → ∀ (lP dE aP : ℕ) (v : List ℤ),
        bEvalSegsW m lM r ls ts ns mks wcs lP dE aP v =
          rkmEvalSegsLoop m lM r ls ts ns mks lP dE aP v := by
  intro ls
  induction ls with
  | nil =>
    intros
    rfl
  | cons lS lR ih =>
    intro ts ns mks wcs hw lP dE aP v
    cases ts with
    | nil => rfl
    | cons t9 tR =>
      cases ns with
      | nil => rfl
      | cons nS nR =>
        cases mks with
        | nil => rfl
        | cons mk mR =>
          have hw0 : ∀ k mL hb u,
              wIter k mL hb u (wHead wcs) = muxFastIterFullT16 k mL hb u :=
            fun k mL hb u => wIter_eq k mL hb u (wHead wcs) (wHead_ok hw)
          have hi0 := ih tR nR mR (wTail wcs) (wTail_ok hw)
          unfold bEvalSegsW rkmEvalSegsLoop
          dsimp only [fN, fL]
          simp only [bForceNat_eq, bForceList_eq, hw0, hi0]
          generalize Nat.add aP _ = np
          cases t9 <;> cases nS <;> cases np <;> rfl
private def bEvalLo12W (m lM r : ℕ) (ls ts ns : List ℕ)
    (mks : List (List Bool)) (wcs : List WalkCert) : List ℕ :=
  let nS := altListLen ls
  cond (Bool.or (Nat.ble nS 0)
    (Bool.or (primNatBlt 8 nS) (Bool.or (primNatBlt r 2) (primNatBlt 1024 r)))) []
    (match bEvalSegsW m lM r ls ts ns mks wcs 1 0 0 [Int.ofNat wdScale] with
    | (dE, aP, vF) => cond (Bool.or (Nat.ble dE 0) (Nat.ble aP 0)) []
        (match altPadRightInts (Nat.add dE 1) vF with
        | [] => []
        | _ :: tl => altVecTailToLo12 aP tl))
private theorem bEvalLo12W_eq (m lM r : ℕ) (ls ts ns : List ℕ)
    (mks : List (List Bool)) (wcs : List WalkCert) (hw : WalksOk wcs) :
    bEvalLo12W m lM r ls ts ns mks wcs = rkmEvalT16Lo12 m lM r ls ts ns mks := by
  unfold bEvalLo12W rkmEvalT16Lo12
  dsimp only
  rw [bEvalSegsW_eq m lM r ls ts ns mks wcs hw]
  generalize altListLen ls = nS
  cases rkmEvalSegsLoop m lM r ls ts ns mks 1 0 0 [Int.ofNat wdScale] with
  | mk dE rest =>
    cases rest with
    | mk aP vF => cases nS <;> cases dE <;> cases aP <;> rfl
private theorem bhW_eq {m lm r : ℕ} {ls ts ns : List ℕ} {mks : List (List Bool)}
    {wcs : List WalkCert} {y : List ℕ} {s : List Bool}
    (h : atF (bNatListEq (bEvalLo12W m lm r ls ts ns mks wcs) y :: s) = true)
    (hw : WalksOk wcs) : rkmLo12EqHi m lm r ls ts ns mks y :=
  (bEvalLo12W_eq m lm r ls ts ns mks wcs hw).symm.trans (bhd_eq h)
private theorem bh0_eq {m lm r : ℕ} {ls ts ns : List ℕ} {mks : List (List Bool)}
    {y : List ℕ} {s : List Bool}
    (h : atF (bNatListEq (bEvalLo12W m lm r ls ts ns mks []) y :: s) = true) :
    rkmLo12EqHi m lm r ls ts ns mks y := bhW_eq h wNil
private abbrev dP_0 : Prop := atF [ bNatListEq (bEvalLo12W 512 16 32 [1,1,1,1,1,1,1,1]
  [16339437,16180995,886424,757804,264667,203767,168165,180458] [18,18,1,1,1,1,1,1]
  rkmMasksHi_m512_r32 []) rkmRowHi_m512_r32, bNatListEq (bEvalLo12W 512 16 31 [1,1,1,1]
  [33423223,1204626,190246,136153] [33,3,2,2] rkmMasksHi_m512_r31 []) rkmRowHi_m512_r31] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bNatListEq (bEvalLo12W 512 16 30 [1,1,1,1]
  [33407023,1193985,179705,145678] [33,3,2,2] rkmMasksHi_m512_r30 []) rkmRowHi_m512_r30, bNatListEq
  (bEvalLo12W 512 16 29 [1,1,1,1,1,1,1,1]
  [15393350,15453764,1089390,1089090,677243,439185,492805,263081] [14,14,1,1,1,1,1,1]
  rkmMasksHi_m512_r29 []) rkmRowHi_m512_r29, bNatListEq (bEvalLo12W 512 16 11 [1,1,1,1,1,1,1,1]
  [15051402,14942928,1402316,939621,373658,288410,424979,657963] [9,9,1,1,1,1,1,1]
  rkmMasksHi_m512_r11 []) rkmRowHi_m512_r11] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bNatListEq (bEvalLo12W 512 16 28 [1,1,1,1,1,1,1,1]
  [15466109,15412537,1041563,1088563,676888,438310,489806,255003] [14,14,1,1,1,1,1,1]
  rkmMasksHi_m512_r28 []) rkmRowHi_m512_r28, bNatListEq (bEvalLo12W 512 16 27 [1,1,1,1,1,1,1,1]
  [15559051,15290263,1101589,1038469,671318,430840,500500,246873] [14,14,1,1,1,1,1,1]
  rkmMasksHi_m512_r27 []) rkmRowHi_m512_r27, bNatListEq (bEvalLo12W 512 16 14 [1,1,1,1,1,1,1,1]
  [14966328,15241747,1400281,1159634,675803,407109,239376,214301] [9,10,1,1,1,1,1,1]
  rkmMasksHi_m512_r14 []) rkmRowHi_m512_r14] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bNatListEq (bEvalLo12W 512 16 26 [1,1,1,1,1,1,1,1]
  [15501420,15378609,1099458,997543,673692,437315,483030,237123] [14,14,1,1,1,1,1,1]
  rkmMasksHi_m512_r26 []) rkmRowHi_m512_r26, bNatListEq (bEvalLo12W 512 16 25 [1,1,1,1,1,1,1,1]
  [15404796,15503689,1098863,961544,640293,447991,491734,227619] [14,14,1,1,1,1,1,1]
  rkmMasksHi_m512_r25 []) rkmRowHi_m512_r25, bNatListEq (bEvalLo12W 512 16 19 [1,1,1,1,1,1,1,1]
  [15236562,15180858,1084787,1361635,643403,448510,454646,147519] [12,12,1,1,1,1,1,1]
  rkmMasksHi_m512_r19 []) rkmRowHi_m512_r19] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bNatListEq (bEvalLo12W 512 16 24 [1,1,1,1,1,1,1,1]
  [15119169,15757063,1097717,982494,636963,446862,486684,216848] [14,14,1,1,1,1,1,1]
  rkmMasksHi_m512_r24 []) rkmRowHi_m512_r24, bNatListEq (bEvalLo12W 512 16 23 [1,1,1,1,1,1,1,1]
  [15073135,15771434,1095167,997144,640113,446236,481434,205194] [14,14,1,1,1,1,1,1]
  rkmMasksHi_m512_r23 []) rkmRowHi_m512_r23, bNatListEq (bEvalLo12W 512 16 22 [1,1,1,1,1,1,1,1]
  [14970143,15839963,1094691,1025144,659013,400136,484014,201692] [14,14,1,1,1,1,1,1]
  rkmMasksHi_m512_r22 []) rkmRowHi_m512_r22] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bNatListEq (bEvalLo12W 512 16 20 [1,1,1,1,1,1,1,1]
  [15251576,15611675,1025129,1002981,630270,457399,456014,163786] [13,13,1,1,1,1,1,1]
  rkmMasksHi_m512_r20 []) rkmRowHi_m512_r20, bNatListEq (bEvalLo12W 512 16 18 [1,1,1,1,1,1,1,1]
  [15191245,15182154,1385383,1092635,638903,448309,446375,129498] [12,12,1,1,1,1,1,1]
  rkmMasksHi_m512_r18 []) rkmRowHi_m512_r18, bNatListEq (bEvalLo12W 512 16 21 [1,1,1]
  [33255192,1198598,183763] [24,2,2] rkmMasksHi_m512_r21 []) rkmRowHi_m512_r21, bNatListEq
  (bEvalLo12W 512 16 13 [1,1,1,1,1,1,1,1]
  [14903233,15239249,1400281,1195634,687403,390909,202168,220102] [9,10,1,1,1,1,1,1]
  rkmMasksHi_m512_r13 []) rkmRowHi_m512_r13, bNatListEq (bEvalLo12W 512 16 3 [1,1,1,1]
  [19739112,10637785,614027,743963] [3,2,1,1] rkmMasksHi_m512_r3 []) rkmRowHi_m512_r3] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bNatListEq (bEvalLo12W 512 16 17 [1,1,1]
  [33534814,820478,112798] [19,2,2] rkmMasksHi_m512_r17 []) rkmRowHi_m512_r17, bNatListEq
  (bEvalLo12W 512 16 16 [1,1,1,1] [33478996,425796,426052,87375] [18,1,1,1] rkmMasksHi_m512_r16 [])
  rkmRowHi_m512_r16, bNatListEq (bEvalLo12W 512 16 12 [1,1,1,1,1,1]
  [14318018,15806645,924024,2019001,755767,341846] [10,10,1,1,1,1] rkmMasksHi_m512_r12 [])
  rkmRowHi_m512_r12, bNatListEq (bEvalLo12W 512 16 15 [1,1,1] [33499890,798682,65461] [18,2,2]
  rkmMasksHi_m512_r15 []) rkmRowHi_m512_r15, bNatListEq (bEvalLo12W 512 16 10 [1,1,1,1,1,1,1,1]
  [15073419,14883429,1342316,939621,671158,80910,411979,580963] [9,9,1,1,1,1,1,1]
  rkmMasksHi_m512_r10 []) rkmRowHi_m512_r10, bNatListEq (bEvalLo12W 512 16 9 [1,1,1,1,1,1,1,1]
  [15015400,14825905,1342316,939621,671158,155310,424679,493863] [9,9,1,1,1,1,1,1]
  rkmMasksHi_m512_r9 []) rkmRowHi_m512_r9, bNatListEq (bEvalLo12W 512 16 4 [1] [32527969] [6]
  rkmMasksHi_m512_r4 []) rkmRowHi_m512_r4, bNatListEq (bEvalLo12W 512 16 5 [1,1,1]
  [11554224,13861365,7586665] [4,4,3] rkmMasksHi_m512_r5 []) rkmRowHi_m512_r5] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bNatListEq (bEvalLo12W 512 16 6 [1,1,1]
  [21160335,7497533,4662805] [6,3,2] rkmMasksHi_m512_r6 []) rkmRowHi_m512_r6, bNatListEq
  (bEvalLo12W 512 16 7 [1] [33551342] [10] rkmMasksHi_m512_r7 []) rkmRowHi_m512_r7, bNatListEq
  (bEvalLo12W 512 16 8 [1] [33727744] [10] rkmMasksHi_m512_r8 []) rkmRowHi_m512_r8] = true
private theorem bk_7 : dP_7 := by decide +kernel
/-- Trajectory row certificate `(m = 512, r = 3)`. -/
theorem rkmTrajHi_m512_r3 :
    rkmLo12EqHi 512 16 3 [1, 1, 1, 1]
      [19739112, 10637785, 614027, 743963]
      [3, 2, 1, 1] rkmMasksHi_m512_r3 rkmRowHi_m512_r3 := bh0_eq (tl2 (tl2 bk_5))
/-- Trajectory row certificate `(m = 512, r = 4)`. -/
theorem rkmTrajHi_m512_r4 :
    rkmLo12EqHi 512 16 4 [1]
      [32527969]
      [6] rkmMasksHi_m512_r4 rkmRowHi_m512_r4 := bh0_eq (tl2 (tl2 (tl2 bk_6)))
/-- Trajectory row certificate `(m = 512, r = 5)`. -/
theorem rkmTrajHi_m512_r5 :
    rkmLo12EqHi 512 16 5 [1, 1, 1]
      [11554224, 13861365, 7586665]
      [4, 4, 3] rkmMasksHi_m512_r5 rkmRowHi_m512_r5 := bh0_eq (tl1 (tl2 (tl2 (tl2 bk_6))))
/-- Trajectory row certificate `(m = 512, r = 6)`. -/
theorem rkmTrajHi_m512_r6 :
    rkmLo12EqHi 512 16 6 [1, 1, 1]
      [21160335, 7497533, 4662805]
      [6, 3, 2] rkmMasksHi_m512_r6 rkmRowHi_m512_r6 := bh0_eq bk_7
/-- Trajectory row certificate `(m = 512, r = 7)`. -/
theorem rkmTrajHi_m512_r7 :
    rkmLo12EqHi 512 16 7 [1]
      [33551342]
      [10] rkmMasksHi_m512_r7 rkmRowHi_m512_r7 := bh0_eq (tl1 bk_7)
/-- Trajectory row certificate `(m = 512, r = 8)`. -/
theorem rkmTrajHi_m512_r8 :
    rkmLo12EqHi 512 16 8 [1]
      [33727744]
      [10] rkmMasksHi_m512_r8 rkmRowHi_m512_r8 := bh0_eq (tl2 bk_7)
/-- Trajectory row certificate `(m = 512, r = 9)`. -/
theorem rkmTrajHi_m512_r9 :
    rkmLo12EqHi 512 16 9 [1, 1, 1, 1, 1, 1, 1, 1]
      [15015400, 14825905, 1342316, 939621, 671158, 155310, 424679, 493863]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r9 rkmRowHi_m512_r9 := bh0_eq (tl1 (tl2 (tl2 bk_6)))
/-- Trajectory row certificate `(m = 512, r = 10)`. -/
theorem rkmTrajHi_m512_r10 :
    rkmLo12EqHi 512 16 10 [1, 1, 1, 1, 1, 1, 1, 1]
      [15073419, 14883429, 1342316, 939621, 671158, 80910, 411979, 580963]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r10 rkmRowHi_m512_r10 := bh0_eq (tl2 (tl2 bk_6))
/-- Trajectory row certificate `(m = 512, r = 11)`. -/
theorem rkmTrajHi_m512_r11 :
    rkmLo12EqHi 512 16 11 [1, 1, 1, 1, 1, 1, 1, 1]
      [15051402, 14942928, 1402316, 939621, 373658, 288410, 424979, 657963]
      [9, 9, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r11 rkmRowHi_m512_r11 := bh0_eq (tl2 bk_1)
/-- Trajectory row certificate `(m = 512, r = 12)`. -/
theorem rkmTrajHi_m512_r12 :
    rkmLo12EqHi 512 16 12 [1, 1, 1, 1, 1, 1]
      [14318018, 15806645, 924024, 2019001, 755767, 341846]
      [10, 10, 1, 1, 1, 1] rkmMasksHi_m512_r12 rkmRowHi_m512_r12 := bh0_eq (tl2 bk_6)
/-- Trajectory row certificate `(m = 512, r = 13)`. -/
theorem rkmTrajHi_m512_r13 :
    rkmLo12EqHi 512 16 13 [1, 1, 1, 1, 1, 1, 1, 1]
      [14903233, 15239249, 1400281, 1195634, 687403, 390909, 202168, 220102]
      [9, 10, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r13 rkmRowHi_m512_r13 := bh0_eq (tl1 (tl2 bk_5))
/-- Trajectory row certificate `(m = 512, r = 14)`. -/
theorem rkmTrajHi_m512_r14 :
    rkmLo12EqHi 512 16 14 [1, 1, 1, 1, 1, 1, 1, 1]
      [14966328, 15241747, 1400281, 1159634, 675803, 407109, 239376, 214301]
      [9, 10, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r14 rkmRowHi_m512_r14 := bh0_eq (tl2 bk_2)
/-- Trajectory row certificate `(m = 512, r = 15)`. -/
theorem rkmTrajHi_m512_r15 :
    rkmLo12EqHi 512 16 15 [1, 1, 1]
      [33499890, 798682, 65461]
      [18, 2, 2] rkmMasksHi_m512_r15 rkmRowHi_m512_r15 := bh0_eq (tl1 (tl2 bk_6))
/-- Trajectory row certificate `(m = 512, r = 16)`. -/
theorem rkmTrajHi_m512_r16 :
    rkmLo12EqHi 512 16 16 [1, 1, 1, 1]
      [33478996, 425796, 426052, 87375]
      [18, 1, 1, 1] rkmMasksHi_m512_r16 rkmRowHi_m512_r16 := bh0_eq (tl1 bk_6)
/-- Trajectory row certificate `(m = 512, r = 17)`. -/
theorem rkmTrajHi_m512_r17 :
    rkmLo12EqHi 512 16 17 [1, 1, 1]
      [33534814, 820478, 112798]
      [19, 2, 2] rkmMasksHi_m512_r17 rkmRowHi_m512_r17 := bh0_eq bk_6
/-- Trajectory row certificate `(m = 512, r = 18)`. -/
theorem rkmTrajHi_m512_r18 :
    rkmLo12EqHi 512 16 18 [1, 1, 1, 1, 1, 1, 1, 1]
      [15191245, 15182154, 1385383, 1092635, 638903, 448309, 446375, 129498]
      [12, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r18 rkmRowHi_m512_r18 := bh0_eq (tl1 bk_5)
/-- Trajectory row certificate `(m = 512, r = 19)`. -/
theorem rkmTrajHi_m512_r19 :
    rkmLo12EqHi 512 16 19 [1, 1, 1, 1, 1, 1, 1, 1]
      [15236562, 15180858, 1084787, 1361635, 643403, 448510, 454646, 147519]
      [12, 12, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r19 rkmRowHi_m512_r19 := bh0_eq (tl2 bk_3)
/-- Trajectory row certificate `(m = 512, r = 20)`. -/
theorem rkmTrajHi_m512_r20 :
    rkmLo12EqHi 512 16 20 [1, 1, 1, 1, 1, 1, 1, 1]
      [15251576, 15611675, 1025129, 1002981, 630270, 457399, 456014, 163786]
      [13, 13, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r20 rkmRowHi_m512_r20 := bh0_eq bk_5
/-- Trajectory row certificate `(m = 512, r = 21)`. -/
theorem rkmTrajHi_m512_r21 :
    rkmLo12EqHi 512 16 21 [1, 1, 1]
      [33255192, 1198598, 183763]
      [24, 2, 2] rkmMasksHi_m512_r21 rkmRowHi_m512_r21 := bh0_eq (tl2 bk_5)
/-- Trajectory row certificate `(m = 512, r = 22)`. -/
theorem rkmTrajHi_m512_r22 :
    rkmLo12EqHi 512 16 22 [1, 1, 1, 1, 1, 1, 1, 1]
      [14970143, 15839963, 1094691, 1025144, 659013, 400136, 484014, 201692]
      [14, 14, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r22 rkmRowHi_m512_r22 := bh0_eq (tl2 bk_4)
/-- Trajectory row certificate `(m = 512, r = 23)`. -/
theorem rkmTrajHi_m512_r23 :
    rkmLo12EqHi 512 16 23 [1, 1, 1, 1, 1, 1, 1, 1]
      [15073135, 15771434, 1095167, 997144, 640113, 446236, 481434, 205194]
      [14, 14, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r23 rkmRowHi_m512_r23 := bh0_eq (tl1 bk_4)
/-- Trajectory row certificate `(m = 512, r = 24)`. -/
theorem rkmTrajHi_m512_r24 :
    rkmLo12EqHi 512 16 24 [1, 1, 1, 1, 1, 1, 1, 1]
      [15119169, 15757063, 1097717, 982494, 636963, 446862, 486684, 216848]
      [14, 14, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r24 rkmRowHi_m512_r24 := bh0_eq bk_4
/-- Trajectory row certificate `(m = 512, r = 25)`. -/
theorem rkmTrajHi_m512_r25 :
    rkmLo12EqHi 512 16 25 [1, 1, 1, 1, 1, 1, 1, 1]
      [15404796, 15503689, 1098863, 961544, 640293, 447991, 491734, 227619]
      [14, 14, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r25 rkmRowHi_m512_r25 := bh0_eq (tl1 bk_3)
/-- Trajectory row certificate `(m = 512, r = 26)`. -/
theorem rkmTrajHi_m512_r26 :
    rkmLo12EqHi 512 16 26 [1, 1, 1, 1, 1, 1, 1, 1]
      [15501420, 15378609, 1099458, 997543, 673692, 437315, 483030, 237123]
      [14, 14, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r26 rkmRowHi_m512_r26 := bh0_eq bk_3
/-- Trajectory row certificate `(m = 512, r = 27)`. -/
theorem rkmTrajHi_m512_r27 :
    rkmLo12EqHi 512 16 27 [1, 1, 1, 1, 1, 1, 1, 1]
      [15559051, 15290263, 1101589, 1038469, 671318, 430840, 500500, 246873]
      [14, 14, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r27 rkmRowHi_m512_r27 := bh0_eq (tl1 bk_2)
/-- Trajectory row certificate `(m = 512, r = 28)`. -/
theorem rkmTrajHi_m512_r28 :
    rkmLo12EqHi 512 16 28 [1, 1, 1, 1, 1, 1, 1, 1]
      [15466109, 15412537, 1041563, 1088563, 676888, 438310, 489806, 255003]
      [14, 14, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r28 rkmRowHi_m512_r28 := bh0_eq bk_2
/-- Trajectory row certificate `(m = 512, r = 29)`. -/
theorem rkmTrajHi_m512_r29 :
    rkmLo12EqHi 512 16 29 [1, 1, 1, 1, 1, 1, 1, 1]
      [15393350, 15453764, 1089390, 1089090, 677243, 439185, 492805, 263081]
      [14, 14, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r29 rkmRowHi_m512_r29 := bh0_eq (tl1 bk_1)
/-- Trajectory row certificate `(m = 512, r = 30)`. -/
theorem rkmTrajHi_m512_r30 :
    rkmLo12EqHi 512 16 30 [1, 1, 1, 1]
      [33407023, 1193985, 179705, 145678]
      [33, 3, 2, 2] rkmMasksHi_m512_r30 rkmRowHi_m512_r30 := bh0_eq bk_1
/-- Trajectory row certificate `(m = 512, r = 31)`. -/
theorem rkmTrajHi_m512_r31 :
    rkmLo12EqHi 512 16 31 [1, 1, 1, 1]
      [33423223, 1204626, 190246, 136153]
      [33, 3, 2, 2] rkmMasksHi_m512_r31 rkmRowHi_m512_r31 := bh0_eq (tl1 bk_0)
/-- Trajectory row certificate `(m = 512, r = 32)`. -/
theorem rkmTrajHi_m512_r32 :
    rkmLo12EqHi 512 16 32 [1, 1, 1, 1, 1, 1, 1, 1]
      [16339437, 16180995, 886424, 757804, 264667, 203767, 168165, 180458]
      [18, 18, 1, 1, 1, 1, 1, 1] rkmMasksHi_m512_r32 rkmRowHi_m512_r32 := bh0_eq bk_0

/-- Self-contained `0bar` lane witness for `FindAllJohnsonRampKickMuxHi512T0`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi512T0 :
    rkmTrajHi_m512_r3 = rkmTrajHi_m512_r3 := rfl

end
end QuantumComputation.Specs.DickeSol
