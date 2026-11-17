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
# High-`m` Coupled Walk & Trajectory Part `2` (`FindAllJohnsonRampKickMuxHi256T2`)

Certifies `(256, 384)` coupled `T_16` walk (`108242` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Prepends `g` `false` entries followed by `true` (`FindAllJohnsonRampKickMuxHi256T2`). -/
def rkmPrependGapHi256T2 : ℕ → List Bool → List Bool
  | 0, acc => true :: acc
  | g + 1, acc => false :: rkmPrependGapHi256T2 g acc
/-- Reconstructs mask bits from gap counts (`FindAllJohnsonRampKickMuxHi256T2`). -/
def rkmGapsToMaskHi256T2 : List ℕ → List Bool
  | [] => []
  | g :: gs => rkmPrependGapHi256T2 g (rkmGapsToMaskHi256T2 gs)
/-- Mask segment `0` for `(m = 256, r = 384)`. -/
def rkmMkHiHiB_m256_r384_s0 : List Bool :=
  rkmGapsToMaskHi256T2
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Mask segment `1` for `(m = 256, r = 384)`. -/
def rkmMkHiHiB_m256_r384_s1 : List Bool :=
  rkmGapsToMaskHi256T2
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Mask segment `2` for `(m = 256, r = 384)`. -/
def rkmMkHiHiB_m256_r384_s2 : List Bool :=
  rkmGapsToMaskHi256T2
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0]
/-- Mask segment `3` for `(m = 256, r = 384)`. -/
def rkmMkHiHiB_m256_r384_s3 : List Bool :=
  rkmGapsToMaskHi256T2
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0]
/-- Mask segment `4` for `(m = 256, r = 384)`. -/
def rkmMkHiHiB_m256_r384_s4 : List Bool :=
  rkmGapsToMaskHi256T2
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Mask segment `5` for `(m = 256, r = 384)`. -/
def rkmMkHiHiB_m256_r384_s5 : List Bool :=
  rkmGapsToMaskHi256T2
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Mask segment `6` for `(m = 256, r = 384)`. -/
def rkmMkHiHiB_m256_r384_s6 : List Bool :=
  rkmGapsToMaskHi256T2
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
     0, 0, 0]
/-- Prefix-kick masks for `(m = 256, r = 384)`. -/
def rkmMasksHiHiB_m256_r384 : List (List Bool) :=
  [rkmMkHiHiB_m256_r384_s0, rkmMkHiHiB_m256_r384_s1, rkmMkHiHiB_m256_r384_s2,
   rkmMkHiHiB_m256_r384_s3, rkmMkHiHiB_m256_r384_s4, rkmMkHiHiB_m256_r384_s5,
   rkmMkHiHiB_m256_r384_s6, []]
/-- Part `0` of `rkmRowHiHiB_m256_r384`. -/
def rkmRowHiHiB_m256_r384_p0 : List ℕ :=
  [10250, 13101, 2371, 2971, 8612, 398, 5552, 4718, 1344, 6074, 520, 11066, 0, 112, 29837, 31227,
   7343, 25303, 51340, 4534, 7767, 3385, 4167, 30161, 12675, 13358, 31243, 2244, 0, 151, 9686,
   32390, 50, 39491, 16247, 4259, 8198, 1079, 2722, 227, 19735, 20908, 9373, 49369, 397, 33878,
   9771, 5349, 6105, 354, 390, 818, 15239, 1908, 28447, 22214, 18157, 51936, 2108, 59502, 2591,
   38503, 12841, 12454, 14421, 743, 5626, 652, 0, 1000, 6032, 54, 17705, 6041, 23079, 25371, 17176,
   54229, 5869, 80768, 0, 93456, 7050, 87818, 26953, 67630, 53261, 41544, 77367, 18424, 92522, 4039,
   95863, 36, 88326, 4728, 73285, 14691, 54907, 26254, 36875, 36504, 21715, 43688, 10653, 47178,
   3825, 47194, 620, 44456, 38, 39878, 973, 34350, 2421, 28603, 3588, 23156, 3966, 18315, 3377,
   14199, 2019, 10786, 528, 7962, 64, 5565]
/-- Part `1` of `rkmRowHiHiB_m256_r384`. -/
def rkmRowHiHiB_m256_r384_p1 : List ℕ :=
  [2397, 3446, 9982, 1570, 25879, 219, 53471, 343, 96054, 4162, 156571, 16711, 235402, 50533,
   316789, 130577, 344260, 257342, 269623, 297486, 219739, 168643, 595173, 275733, 2044106, 3049176,
   1141777, 12203037, 3477560, 5435153, 20598408, 7159448, 1651409, 15863611, 13299473, 1663031,
   338251, 850602, 1198459, 4656335, 9155868, 7612636, 5681067, 6200804, 3023045, 1969, 4832,
   3430990, 4528851, 622402, 6018422, 110184, 9670736, 715865, 8717117, 3368149, 5493205, 6321998,
   1932337, 6929471, 227285, 5093457, 7852, 2738918, 34613, 1399121, 809, 1133859, 48923, 1541157,
   12836, 1971675, 86571, 1529694, 487172, 491628, 546293, 12128, 121139, 18876, 21571, 1458,
   105762, 76954, 20004, 25860, 311, 71279, 119611, 249066, 883723, 48914, 1507769, 38904, 1138052,
   42415, 1062841, 3773, 2140817, 25861, 3971576, 395626, 2587809, 1618629, 3517760, 205327,
   1836952, 2749855, 5988032, 2995147, 2944668, 2760383, 725407, 5225315, 2486265, 8313039, 2582397,
   6268037, 376042, 3667145, 20211, 7578443, 330508, 11018514, 693592, 9114654, 55, 11113140]
/-- Part `2` of `rkmRowHiHiB_m256_r384`. -/
def rkmRowHiHiB_m256_r384_p2 : List ℕ :=
  [160013, 4545612, 47022, 3281200, 11678, 679626, 2507, 85837, 2860, 129024, 1290, 754559, 31591,
   1877061, 265111, 3168255, 1185238, 3938085, 3626429, 3109125, 7580822, 965200, 10291371, 11382,
   8679727, 808809, 6446092, 578605, 3422256, 6313495, 11335171, 4289888, 2805315, 280737, 335402,
   1853, 800147, 2159352, 1037736, 11342777, 1873167, 4533960, 2437249, 4659522, 5911676, 1265197,
   11912600, 66139, 9028860, 3033538, 6732507, 8600767, 3229563, 7283348, 5574, 5368450, 2916625,
   5351053, 9375406, 4743921, 16374808, 1379031, 18157609, 367551, 8980761, 3103958, 522733, 842722,
   221751, 1343045, 1127738, 2411815, 16840698, 5801636, 10320159, 62727119, 34854638, 441601,
   62788339, 18388658, 15991072, 36743298, 228307138, 145548, 9808016, 17511422, 1409124650,
   1223256680, 296346026, 3347667989, 2257315688, 134388122, 161343, 1838471923, 17992861247,
   60965098127, 121421784316, 171087260937, 186094101603, 163944174242, 120453290263, 75236353036,
   40482120966, 18941555254, 7759782242, 2797133973, 890284949, 250791331, 62610581, 13858970,
   2718886, 472158, 72423, 9779, 1156, 118, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 384)`. -/
def rkmRowHiHiB_m256_r384 : List ℕ :=
  rkmRowHiHiB_m256_r384_p0 ++ (rkmRowHiHiB_m256_r384_p1 ++ rkmRowHiHiB_m256_r384_p2)
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi256T2`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi256T2 : (0 : ℕ) = 0 := rfl
end
public section
private abbrev bZ : ℕ := 2000000000000000
private theorem hbZ0 : Nat.ble bZ 0 = false := rfl
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by
  rw [Nat.add_eq]
  exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem hzMul0 (z : ℕ) : Nat.mul 0 z = 0 := by
  rw [Nat.mul_eq]
  omega
private def uC (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x, xs with
  | 0, _ => xs
  | v + 1, [] => [v]
  | v + 1, h :: t => v :: h :: t
private theorem uC_eq (x : ℕ) (l : List ℕ) : uC x l = x :: l := by
  unfold uC
  rw [n1a]
  cases l <;> rfl
private def uOh : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOh ns
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
  | Int.ofNat v => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t
private theorem bCZ_eq (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem bOfF (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  unfold primOfNatForced
  rw [n1a]
private theorem bNsF (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  unfold primNegSuccForced
  rw [n1a]
private theorem bSubF (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat
  rw [bOfF, Nat.sub_eq]
  cases h : z - u with
  | zero =>
    dsimp only
    rw [Nat.sub_eq, Int.ofNat_eq_natCast]
    omega
  | succ k =>
    dsimp only
    rw [Int.negSucc_eq]
    omega
private def bDc (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bCZ (rkmForcedSubNatNat u z) (bDc z us)
private theorem bDc0 (z : ℕ) : bDc z [] = [] := rfl
private theorem bDcS (z u : ℕ) (us : List ℕ) :
    bDc z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDc z us := by
  rw [bDc, bCZ_eq, bSubF]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]
  omega
private theorem bM0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZ0]
  rfl
private def bNL : List ℕ → ℕ
  | [] => 0
  | _ :: us => Nat.add (bNL us) 1
private theorem bNL_eq (z : ℕ) : ∀ (us : List ℕ), bNL us = altIntLen (bDc z us)
  | [] => rfl
  | _ :: us => by
    dsimp only [bNL]
    rw [bDcS]
    dsimp only [altIntLen]
    rw [bNL_eq z us]
private def zTd (x : ℤ) (d : ℕ) : ℤ := match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.ofNat_eq_natCast]
    omega
  | k + 1 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.negSucc_eq]
    omega
private theorem bTdN : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTd x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => by
    dsimp only [muxRawIntTdivNat, zTd]
    rw [bNeg, ndiv, Nat.add_eq]
private theorem bSTdN (m n d : ℕ) : rkmUltraSubNatTdiv m n d = zTd ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, ndiv, Nat.add_eq]
  cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by
      rw [Int.ofNat_eq_natCast]
      omega
    rw [hm]
    rfl
  | succ k =>
    dsimp only
    have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by
      rw [Int.negSucc_eq]
      omega
    rw [hm]
    dsimp only [zTd]
    rw [bNeg]
private theorem bSTd (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTd (a - b) d := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact bSTdN m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]
        omega
      dsimp only [rkmUltraSubTdiv]
      rw [hm]
      dsimp only [zTd]
      rw [ndiv, Nat.add_eq, Nat.add_eq]
  | negSucc m =>
    cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
        omega
      dsimp only [rkmUltraSubTdiv]
      rw [hm]
      dsimp only [zTd]
      rw [bNeg, ndiv, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]
      rw [bSTdN, Nat.add_eq, Nat.add_eq]
      refine congrArg (fun t => zTd t d) ?_
      simp only [Int.negSucc_eq]
      omega
private theorem bMul (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a with
  | ofNat _ =>
    cases b with
    | ofNat _ =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
      push_cast
      ring
    | negSucc _ =>
      dsimp only [muxRawIntMul]
      simp only [bNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
  | negSucc _ =>
    cases b with
    | ofNat _ =>
      dsimp only [muxRawIntMul]
      simp only [bNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
    | negSucc _ =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
private theorem bFAdd (a b : ℤ) : rkmForcedIntAdd a b = a + b := by
  cases a with
  | ofNat _ =>
    cases b with
    | ofNat _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bOfF, Nat.add_eq, Int.ofNat_eq_natCast]
      omega
    | negSucc _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bSubF, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
  | negSucc _ =>
    cases b with
    | ofNat _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bSubF, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
    | negSucc _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bNsF, Nat.add_eq, Int.negSucc_eq]
      omega
private theorem bAC (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons
  rw [bFAdd]
  cases a + b <;> cases xs <;> rfl
private def bSV (v P Q d : ℕ) : ℕ := match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bSV_eq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  unfold bSV at hv ⊢
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢
  revert hv
  cases h : Q - P with
  | zero =>
    intro _
    have hm : (P : ℤ) - (Q : ℤ) = Int.ofNat (P - Q) := by
      rw [Int.ofNat_eq_natCast]
      omega
    rw [hm]
    dsimp only [zTd]
    rw [Int.ofNat_eq_natCast]
    push_cast
    ring
  | succ k =>
    intro hv
    have hm : (P : ℤ) - (Q : ℤ) = Int.negSucc k := by
      rw [Int.negSucc_eq]
      omega
    rw [hm]
    dsimp only [zTd] at hv ⊢
    omega
private theorem bSV_same (z P d : ℕ) : bSV z P P d = z := by
  unfold bSV
  simp only [Nat.sub_eq, Nat.add_eq, ndiv, Nat.sub_self, Nat.zero_div, Nat.add_zero]
private theorem bSV_comm (z A B d : ℕ) : bSV z (Nat.add A B) (Nat.add B A) d = z := by
  have hc : Nat.add B A = Nat.add A B := by
    simp only [Nat.add_eq]
    omega
  rw [hc]
  exact bSV_same z (Nat.add A B) d
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bSV v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bChb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bDc z rest = tailZ) :
    bDc z (uC (bCV z d b0 c0 b v c1) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ)) (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0)
        ((c0 : ℤ) - (z : ℤ))) (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uC_eq, bDcS, ht, bAC, bSTd, bMul, bMul]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
  unfold bCV at hv ⊢
  rw [bSV_eq z v _ _ d hv, hpq]
private theorem bC0 (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDc z rest = tailZ) :
    bDc z (uC (bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uC_eq, bDcS, ht, bAC, bTdN, bMul]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [bSV_eq z v _ _ d hv, hpq]
private def bAP : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAP xs)
private theorem apC {x : ℕ} {xs : List ℕ} (h : bAP (uC x xs) = true) :
    0 < x ∧ bAP xs = true := by
  rw [uC_eq] at h
  cases x with
  | zero => exact Bool.noConfusion h
  | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHO (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem hoEq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHO z cs : ℤ) - (z : ℤ)) = (match bDc z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by
    unfold bHO
    rw [bDc0, bZ0]
  | _ :: _ => by
    unfold bHO
    rw [bDcS]
private theorem tnEq (z : ℕ) : ∀ (xs : List ℕ),
    bDc z (bTN xs) = (match bDc z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | _ :: _ => by
    unfold bTN
    rw [bDcS]
private def rPad (z : ℕ) : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | k + 1, [] => uC z (rPad z k [])
  | k + 1, x :: xs => uC x (rPad z k xs)
private theorem rPad_uC (z r x : ℕ) (xs : List ℕ) :
    rPad z (r + 1) (uC x xs) = uC x (rPad z r xs) := by
  rw [uC_eq]
  rfl
private theorem rPad_hd (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ), bHO z (rPad z k xs) = bHO z xs
  | 0, _ => rfl
  | _ + 1, [] => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
  | _ + 1, _ :: _ => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
private theorem rPad_tl (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ),
    bTN (rPad z k xs) = rPad z (k - 1) (bTN xs)
  | 0, _ => rfl
  | _ + 1, [] => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
  | _ + 1, _ :: _ => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
private theorem rPad_bNL (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ),
    Nat.ble (bNL xs) k = true → bNL (rPad z k xs) = k
  | 0, [], _ => rfl
  | 0, _ :: xs, h => by
    dsimp only [bNL] at h
    rw [Nat.add_eq] at h
    have h1 : bNL xs + 1 ≤ 0 := Nat.le_of_ble_eq_true h
    omega
  | k + 1, [], _ => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bNL]
    rw [rPad_bNL z k [] rfl, Nat.add_eq]
  | k + 1, _ :: xs, h => by
    have hk : Nat.ble (bNL xs) k = true := by
      have h1 := Nat.le_of_ble_eq_true h
      dsimp only [bNL] at h1
      rw [Nat.add_eq] at h1
      exact Nat.ble_eq_true_of_le (by omega)
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bNL]
    rw [rPad_bNL z k xs hk, Nat.add_eq]
private theorem bAP_rPad {z : ℕ} (hz : Nat.ble z 0 = false) :
    ∀ (k : ℕ) (xs : List ℕ), bAP xs = true → bAP (rPad z k xs) = true
  | 0, _, h => h
  | k + 1, [], _ => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bAP]
    rw [hz]
    dsimp only [cond]
    exact bAP_rPad hz k [] rfl
  | k + 1, x :: xs, h => by
    dsimp only [bAP] at h
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bAP]
    revert h
    cases Nat.ble x 0 with
    | true =>
      intro h
      dsimp only [cond] at h
      cases h
    | false =>
      intro h
      dsimp only [cond] at h ⊢
      exact bAP_rPad hz k xs h
private def bEqN (a b : ℕ) : Bool :=
  cond (Nat.ble a b) (Nat.ble b a) false
private theorem bEqN_self (a : ℕ) : bEqN a a = true := by
  have hle : Nat.ble a a = true := Nat.ble_eq_true_of_le (by omega)
  unfold bEqN
  rw [hle]
  rfl
private theorem bEqN_eq (a b : ℕ) (h : bEqN a b = true) : a = b := by
  unfold bEqN at h
  revert h
  cases hab : Nat.ble a b with
  | false =>
    intro h
    dsimp only [cond] at h
    cases h
  | true =>
    cases hba : Nat.ble b a with
    | false =>
      intro h
      dsimp only [cond] at h
      cases h
    | true =>
      intro _
      have h1 := Nat.le_of_ble_eq_true hab
      have h2 := Nat.le_of_ble_eq_true hba
      omega
private def bCT (z x : ℕ) (xs : List ℕ) : List ℕ :=
  match xs with
  | h :: t => x :: h :: t
  | [] => cond (bEqN x z) [] [x]
private def bTrim (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => bCT z x (bTrim z xs)
private theorem bTrim_rPad (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ), bTrim z (rPad z k xs) = bTrim z xs
  | 0, _ => rfl
  | k + 1, [] => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bTrim]
    rw [bTrim_rPad z k []]
    dsimp only [bTrim, bCT]
    rw [bEqN_self z]
    rfl
  | k + 1, x :: xs => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bTrim]
    rw [bTrim_rPad z k xs]
private theorem rPad_bTrim_len (z : ℕ) : ∀ (xs : List ℕ), rPad z (bNL xs) (bTrim z xs) = xs
  | [] => rfl
  | x :: t => by
    have hal : bNL (x :: t) = bNL t + 1 := rfl
    rw [hal]
    dsimp only [bTrim]
    have ih := rPad_bTrim_len z t
    revert ih
    cases bTrim z t with
    | cons _ _ =>
      intro ih
      dsimp only [bCT, rPad]
      rw [uC_eq, ih]
    | nil =>
      intro ih
      dsimp only [bCT]
      cases he : bEqN x z with
      | true =>
        dsimp only [cond, rPad]
        rw [uC_eq, bEqN_eq x z he, ih]
      | false =>
        dsimp only [cond, rPad]
        rw [uC_eq, ih]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, [], vs, cs =>
    uC (bSV (bHO z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d) (bSl z d rem 0 z [] (bTN vs) (bTN cs))
  | rem + 1, b0, c0, b :: bR, vs, cs =>
    uC (bCV z d b0 c0 b (bHO z vs) (bHO z (bTN cs)))
      (bSl z d rem b (bHO z cs) bR (bTN vs) (bTN cs))
private theorem bSl_len (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bNL (bSl z d rem b0 c0 bns vs cs) = rem
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, [], vs, cs => by
    dsimp only [bSl]
    rw [uC_eq]
    dsimp only [bNL]
    rw [bSl_len z d rem 0 z [] (bTN vs) (bTN cs), Nat.add_eq]
  | rem + 1, b0, c0, b :: bR, vs, cs => by
    dsimp only [bSl]
    rw [uC_eq]
    dsimp only [bNL]
    rw [bSl_len z d rem b (bHO z cs) bR (bTN vs) (bTN cs), Nat.add_eq]
private theorem bSl_rPad (z d : ℕ) : ∀ (rem b0 c0 kv kc : ℕ) (bns vs cs : List ℕ),
    bSl z d rem b0 c0 bns (rPad z kv vs) (rPad z kc cs) = bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, kv, kc, [], vs, cs => by
    dsimp only [bSl]
    rw [rPad_hd z kv vs, rPad_tl z kv vs, rPad_tl z kc cs]
    rw [bSl_rPad z d rem 0 z (kv - 1) (kc - 1) [] (bTN vs) (bTN cs)]
  | rem + 1, b0, c0, kv, kc, b :: bR, vs, cs => by
    dsimp only [bSl]
    rw [rPad_hd z kv vs, rPad_tl z kc cs, rPad_hd z (kc - 1) (bTN cs), rPad_hd z kc cs,
      rPad_tl z kv vs]
    rw [bSl_rPad z d rem b (bHO z cs) (kv - 1) (kc - 1) bR (bTN vs) (bTN cs)]
private theorem bSl_zero (z d : ℕ) : ∀ (rem b0 : ℕ) (bns : List ℕ),
    bSl z d rem b0 z bns [] [] = rPad z rem []
  | 0, _, _ => rfl
  | rem + 1, b0, [] => by
    dsimp only [bSl, bHO, bTN, rPad]
    rw [bSV_same z (Nat.mul b0 z) d, bSl_zero z d rem 0 []]
  | rem + 1, b0, b :: bR => by
    dsimp only [bSl, bCV, bHO, bTN, rPad]
    rw [bSV_comm z (Nat.mul b0 z) (Nat.mul b z) d, bSl_zero z d rem b bR]
private theorem bSl_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAP (bSl z d rem b0 c0 bns vs cs) = true → bDc z (bSl z d rem b0 c0 bns vs cs) =
      rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOh bns) (bDc z vs) (bDc z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, [], vs, cs, h => by
    dsimp only [bSl, uOh, rkmUltraSlideLoopAux] at h ⊢
    have hp := apC h
    have hi := bSl_sound z d rem 0 z [] (bTN vs) (bTN cs) hp.2
    rw [bM0, uOh, tnEq z vs, tnEq z cs] at hi
    have hc := bC0 z d b0 c0 (bHO z vs) hp.1 hi
    rw [hoEq z vs] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, [], [], h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDc0]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b z bR [] [] hp.2
    rw [bZ0 z, bDc0] at hi
    have hc := bChb z d b0 c0 b z z hp.1 hi
    rw [bZ0 z] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, [], c :: cT, h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDc0, bDcS z c cT]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b c bR [] cT hp.2
    rw [bDc0] at hi
    have hc := bChb z d b0 c0 b z (bHO z cT) hp.1 hi
    rw [hoEq z cT, bZ0 z] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, v :: vT, [], h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDcS z v vT, bDc0]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b z bR vT [] hp.2
    rw [bZ0 z, bDc0] at hi
    have hc := bChb z d b0 c0 b v z hp.1 hi
    rw [bZ0 z] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, v :: vT, c :: cT, h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDcS z v vT, bDcS z c cT]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b c bR vT cT hp.2
    have hc := bChb z d b0 c0 b v (bHO z cT) hp.1 hi
    rw [hoEq z cT] at hc
    exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uC b (uC (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs => match hbz with
    | [] => match vs, cs with
      | [], [] => uC (bSV z p0 q0 d) []
      | _, _ => uC (bSV (bHO z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTN vs) (bTN cs))
    | [_] => []
    | b :: bz :: bR => match vs, cs with
      | [], [] => uC (bSV z (Nat.add p0 bz) (Nat.add bz q0) d) []
      | v :: vT, c :: cT => uC (bSV v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] => uC (bSV v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT => uC (bSV z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
private theorem bSlZ_rPad (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    rPad z rem (bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs) =
      bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, _, _, bns, vs, cs => by
    cases bns with
    | nil =>
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, bSl_zero z d rem 0 []]
        | cons _ cT =>
          have hrec := bSlZ_rPad z d rem 0 z [] [] cT
          dsimp only [mkHbZ] at hrec
          rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, hrec]
      | cons _ vT =>
        cases cs with
        | nil =>
          have hrec := bSlZ_rPad z d rem 0 z [] vT []
          dsimp only [mkHbZ] at hrec
          rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, hrec]
        | cons _ cT =>
          have hrec := bSlZ_rPad z d rem 0 z [] vT cT
          dsimp only [mkHbZ] at hrec
          rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, hrec]
    | cons b bR =>
      dsimp only [mkHbZ]
      rw [uC_eq, uC_eq]
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSl_zero z d rem b bR]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSlZ_rPad z d rem b c bR [] cT]
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSlZ_rPad z d rem b z bR vT []]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSlZ_rPad z d rem b c bR vT cT]
private def uCN4 (x1 x2 x3 x4 : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x1 with
  | 0 => xs
  | v1 + 1 => match Nat.add 1 x2 with
    | 0 => xs
    | v2 + 1 => match Nat.add 1 x3 with
      | 0 => xs
      | v3 + 1 => match Nat.add 1 x4 with
        | 0 => xs
        | v4 + 1 => match xs with
          | [] => [v1, v2, v3, v4]
          | h :: t => v1 :: v2 :: v3 :: v4 :: h :: t
private theorem uCN4e (x1 x2 x3 x4 : ℕ) (xs : List ℕ) :
    uCN4 x1 x2 x3 x4 xs = uC x1 (uC x2 (uC x3 (uC x4 xs))) := by
  unfold uCN4
  rw [n1a x1, n1a x2, n1a x3, n1a x4, uC_eq, uC_eq, uC_eq, uC_eq]
  cases xs <;> rfl
private def bAP4 : List ℕ → Bool
  | a :: b :: c :: d :: xs => cond (Nat.ble a 0) false (cond (Nat.ble b 0) false
      (cond (Nat.ble c 0) false (cond (Nat.ble d 0) false (bAP4 xs))))
  | xs => bAP xs
private theorem bAP4e : ∀ (xs : List ℕ), bAP4 xs = bAP xs
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: xs => by
    dsimp only [bAP4, bAP]
    rw [bAP4e xs]
private def bChkP (out : List ℕ) : Option (List ℕ) := match out with
  | [] => some []
  | x :: xs => cond (bAP4 (x :: xs)) (some (x :: xs)) none
private theorem bChkPe (out : List ℕ) : bChkP out = cond (bAP out) (some out) none := by
  cases out with
  | nil => rfl
  | cons _ _ =>
    dsimp only [bChkP]
    rw [bAP4e]
private theorem cond_some_eq {α : Type} {b : Bool} {x y : α}
    (h : cond b (some x) none = some y) : b = true ∧ x = y := by
  cases b with
  | false => cases h
  | true =>
    dsimp only [cond] at h
    injection h with h'
    exact ⟨rfl, h'⟩
private inductive HbZ4 : Type
  | tail : List ℕ → HbZ4
  | c4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → HbZ4 → HbZ4
private abbrev hbz4C (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) : List ℕ :=
  b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: t
private def hbz4L : HbZ4 → List ℕ
  | HbZ4.tail l => l
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L r)
private def fH4 {α : Type} (h : HbZ4) (k : HbZ4 → α) : α := match h with
  | HbZ4.tail l => fL l fun lF => k (HbZ4.tail lF)
  | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r => k (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r)
private theorem fH4e {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ =>
    dsimp only [fH4, fL]
    rw [rkmb_forceList_eq]
  | c4 _ _ _ _ _ _ _ _ _ => rfl
private def toH4 : List ℕ → HbZ4
  | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs => match toH4 bs with
    | HbZ4.tail l => HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.tail l)
    | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t =>
      HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t)
  | bs => HbZ4.tail bs
private theorem hbz4L_toH4 : ∀ (xs : List ℕ), hbz4L (toH4 xs) = xs
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | [_, _, _, _, _] => rfl
  | [_, _, _, _, _, _] => rfl
  | [_, _, _, _, _, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: bs => by
    have ih := hbz4L_toH4 bs
    dsimp only [toH4]
    revert ih
    cases toH4 bs with
    | tail _ =>
      intro ih
      dsimp only [hbz4L, hbz4C] at ih ⊢
      rw [ih]
    | c4 _ _ _ _ _ _ _ _ _ =>
      intro ih
      dsimp only [hbz4L, hbz4C] at ih ⊢
      rw [ih]
private def bSlZ4 (z d : ℕ) : HbZ4 → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | HbZ4.tail l, rem, p0, q0, vs, cs => bSlZ z d rem p0 q0 l vs cs
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR, rem, p0, q0, vs, cs => match rem with
    | 0 => []
    | r3 + 1 => match r3 with
      | 0 => bSlZ z d 1 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
      | r2 + 1 => match r2 with
        | 0 => bSlZ z d 2 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
        | r1 + 1 => match r1 with
          | 0 => bSlZ z d 3 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
          | r0 + 1 => match vs, cs with
            | [], [] => uC (bSV z (Nat.add p0 z1) (Nat.add z1 q0) d) []
            | v1 :: v2 :: v3 :: v4 :: vR, c1 :: c2 :: c3 :: c4 :: c5 :: cR =>
              uCN4 (bSV v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                (bSV v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                (bSV v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                (bSV v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 c5) z3) d)
                (bSlZ4 z d bR r0 (Nat.mul b4 c4) z4 vR (c5 :: cR))
            | [], c1 :: c2 :: c3 :: c4 :: c5 :: cR =>
              uCN4 (bSV z (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                (bSV z (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                (bSV z (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                (bSV z (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 c5) z3) d)
                (bSlZ4 z d bR r0 (Nat.mul b4 c4) z4 [] (c5 :: cR))
            | _, _ =>
              bSlZ z d ((((r0 + 1) + 1) + 1) + 1) p0 q0
                (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
private theorem bSlZ4_eq (z d : ℕ) : ∀ (hbz : HbZ4) (rem p0 q0 : ℕ) (vs cs : List ℕ),
    bSlZ4 z d hbz rem p0 q0 vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs
  | HbZ4.tail _, _, _, _, _, _ => rfl
  | HbZ4.c4 _ _ _ _ _ _ b4 z4 bR, rem, _, _, vs, cs => by
    match rem with
    | 0 => rfl
    | r3 + 1 => match r3 with
      | 0 => rfl
      | r2 + 1 => match r2 with
        | 0 => rfl
        | r1 + 1 => match r1 with
          | 0 => rfl
          | r0 + 1 => match vs with
            | [] => match cs with
              | [] => rfl
              | [_] => rfl
              | [_, _] => rfl
              | [_, _, _] => rfl
              | [_, _, _, _] => rfl
              | _ :: _ :: _ :: c4 :: c5 :: cR =>
                dsimp only [bSlZ4, hbz4L, hbz4C, bSlZ, bHO]
                rw [uCN4e]
                exact congrArg (fun r => uC _ (uC _ (uC _ (uC _ r))))
                  (bSlZ4_eq z d bR r0 (Nat.mul b4 c4) z4 [] (c5 :: cR))
            | [_] => rfl
            | [_, _] => rfl
            | [_, _, _] => rfl
            | _ :: _ :: _ :: _ :: vR => match cs with
              | [] => rfl
              | [_] => rfl
              | [_, _] => rfl
              | [_, _, _] => rfl
              | [_, _, _, _] => rfl
              | _ :: _ :: _ :: c4 :: c5 :: cR =>
                dsimp only [bSlZ4, hbz4L, hbz4C, bSlZ, bHO]
                rw [uCN4e]
                exact congrArg (fun r => uC _ (uC _ (uC _ (uC _ r))))
                  (bSlZ4_eq z d bR r0 (Nat.mul b4 c4) z4 vR (c5 :: cR))
private def bDg (z dg mL cL : ℕ) (h4 : HbZ4) (vT cT : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlZ4 z d h4 nL 0 0 vT cT) fun raw => bChkP raw
private theorem bDg_rPad {z dg mL cL : ℕ} {b vT cT outT : List ℕ}
    (h : bDg z dg mL cL (toH4 (mkHbZ z b)) vT cT = some outT) :
    bAP outT = true ∧
      rPad z (rkmNextLen mL cL) outT =
        bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b vT cT := by
  unfold bDg at h
  dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq, bChkPe, bSlZ4_eq, hbz4L_toH4] at h
  rcases cond_some_eq h with ⟨hp, rfl⟩
  have hsl := bSlZ_rPad z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b vT cT
  rw [hzMul0 z] at hsl
  exact ⟨hp, hsl⟩
private theorem bDg_sound {z : ℕ} (hz : Nat.ble z 0 = false) (dg mL vL cL : ℕ)
    (b vT cT outT : List ℕ) (h : bDg z dg mL cL (toH4 (mkHbZ z b)) vT cT = some outT) :
    bDc z (rPad z (rkmNextLen mL cL) outT) =
      rkmUltraHornerStage dg mL cL (uOh b) (bDc z (rPad z vL vT)) (bDc z (rPad z cL cT)) := by
  rcases bDg_rPad h with ⟨hp, hsl⟩
  have hpos : bAP (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b
      (rPad z vL vT) (rPad z cL cT)) = true := by
    rw [bSl_rPad, ← hsl]
    exact bAP_rPad hz _ _ hp
  unfold rkmUltraHornerStage
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bM0 z, hsl,
    ← bSl_rPad z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z vL cL b vT cT]
  exact bSl_sound z _ _ 0 z b (rPad z vL vT) (rPad z cL cT) hpos
private def bDg1 (z mL cL : ℕ) (h4 : HbZ4) (vT cT : List ℕ) : Option (List ℕ) :=
  match bDg z 1 mL cL h4 vT cT with
  | none => none
  | some raw => fL (bTrim z raw) fun outT => some outT
private theorem bDg1_sound {z : ℕ} (hz : Nat.ble z 0 = false) (mL vL cL : ℕ)
    (b vT cT outT : List ℕ) (h : bDg1 z mL cL (toH4 (mkHbZ z b)) vT cT = some outT) :
    bDc z (rPad z (rkmNextLen mL cL) outT) =
      rkmUltraHornerStage 1 mL cL (uOh b) (bDc z (rPad z vL vT)) (bDc z (rPad z cL cT)) := by
  unfold bDg1 at h
  revert h
  cases hd : bDg z 1 mL cL (toH4 (mkHbZ z b)) vT cT with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some raw =>
    intro h
    dsimp only [fL] at h
    rw [rkmb_forceList_eq] at h
    injection h with h'
    subst h'
    rcases bDg_rPad hd with ⟨_, hsl⟩
    have hpad := rPad_bTrim_len z (bSl z (Nat.mul 1 wdScale) (rkmNextLen mL cL) 0 z b vT cT)
    rw [bSl_len] at hpad
    rw [← bTrim_rPad z (rkmNextLen mL cL) raw, hsl, hpad, ← hsl]
    exact bDg_sound hz 1 mL vL cL b vT cT raw hd
private def bBdD (z g m c : ℕ) (h4 : HbZ4) (vT xT : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen m c) fun n => match bDg z g m c h4 vT xT with | none => none | some o => k n o
private theorem bBdD_sound {z : ℕ} (hz : Nat.ble z 0 = false) {endL g m vL c : ℕ}
    {b vT xT outT : List ℕ} {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBdD z g m c (toH4 (mkHbZ z b)) vT xT kB = some outT)
    (hk : ∀ m0, kB (rkmNextLen m c) m0 = some outT →
      bDc z (rPad z endL outT) = kU (rkmNextLen m c) (bDc z (rPad z (rkmNextLen m c) m0))) :
    bDc z (rPad z endL outT) =
      (HighDForce.withForcedNat (rkmNextLen m c) fun nL => HighDForce.withForcedList
        (rkmUltraHornerStage g m c (uOh b) (bDc z (rPad z vL vT)) (bDc z (rPad z c xT))) (kU nL)) :=
  by
  unfold bBdD at h
  dsimp only [fN] at h
  rw [rkmb_forceNat_eq] at h
  revert h
  cases hs : bDg z g m c (toH4 (mkHbZ z b)) vT xT with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some mid =>
    intro h
    rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bDg_sound hz g m vL c b vT xT mid hs]
    exact hk mid h
private def bSpD (z m c : ℕ) (h4 : HbZ4) (vT : List ℕ) : Option (List ℕ) :=
  bBdD z 16 m c h4 vT vT fun l x => bBdD z 15 m l h4 vT x fun l x =>
  bBdD z 14 m l h4 vT x fun l x => bBdD z 13 m l h4 vT x fun l x =>
  bBdD z 12 m l h4 vT x fun l x => bBdD z 11 m l h4 vT x fun l x =>
  bBdD z 10 m l h4 vT x fun l x => bBdD z 9 m l h4 vT x fun l x =>
  bBdD z 8 m l h4 vT x fun l x => bBdD z 7 m l h4 vT x fun l x =>
  bBdD z 6 m l h4 vT x fun l x => bBdD z 5 m l h4 vT x fun l x =>
  bBdD z 4 m l h4 vT x fun l x => bBdD z 3 m l h4 vT x fun l x =>
  bBdD z 2 m l h4 vT x fun l x => bDg1 z m l h4 vT x
private theorem bSpD_sound {z : ℕ} (hz : Nat.ble z 0 = false) (mL cL : ℕ) (b vT outT : List ℕ)
    (h : bSpD z mL cL (toH4 (mkHbZ z b)) vT = some outT) :
    bDc z (rPad z (rkmNextLen16 mL cL) outT) =
      rkmUltraHornerT16Step mL cL (uOh b) (bDc z (rPad z cL vT)) := by
  unfold bSpD at h
  unfold rkmUltraHornerT16Step
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  unfold rkmNextLen16
  exact bDg1_sound hz mL cL _ b vT _ outT h
private def bItD (z : ℕ) : ℕ → ℕ → ℕ → HbZ4 → List ℕ → Option (ℕ × List ℕ)
  | 0, _, c, _, vT => some (c, vT)
  | k + 1, m, c, h4, vT => match bSpD z m c h4 vT with
    | none => none
    | some vN => fN (rkmNextLen16 m c) fun nL => bItD z k m nL h4 vN
private theorem bItD_sound {z : ℕ} (hz : Nat.ble z 0 = false) :
    ∀ (k m c : ℕ) (b vT : List ℕ) (endL : ℕ) (outT : List ℕ),
      bItD z k m c (toH4 (mkHbZ z b)) vT = some (endL, outT) →
        bDc z (rPad z endL outT) = muxUltraIterFullT16Rkm k m c (uOh b) (bDc z (rPad z c vT))
  | 0, _, _, _, _, _, _, h => by
    injection h with h'
    injection h' with hc hv
    subst hc
    subst hv
    rfl
  | k + 1, m, c, b, vT, endL, outT, h => by
    unfold bItD at h
    revert h
    cases hs : bSpD z m c (toH4 (mkHbZ z b)) vT with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some vN =>
      intro h
      dsimp only [fN] at h
      rw [rkmb_forceNat_eq] at h
      unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bSpD_sound hz m c b vT vN hs]
      exact bItD_sound hz k m _ b vN endL outT h
private theorem u2f {s m : ℕ} {b u v : List ℤ}
    (h : muxUltraIterFullT16Rkm s m (altIntLen u) b u = v) : muxFastIterFullT16 s m b u = v := by
  have hc : muxUltraIterFullT16HiChk s 0 m b u v = true := by
    unfold muxUltraIterFullT16HiChk
    dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, h]
    exact muxIntListEq_eq_true.mpr rfl
  exact muxUltraIterFullT16HiChk_sound hc
private def pWOk (k m : ℕ) (bns : List ℕ) (l0 : ℕ) (uT : List ℕ) (l1 : ℕ) (vT : List ℕ) : Prop :=
  muxFastIterFullT16 k m (uOh bns) (bDc bZ (rPad bZ l0 uT)) = bDc bZ (rPad bZ l1 vT)
private def bSlChk (s m : ℕ) (bns : List ℕ) (l0 : ℕ) (uT : List ℕ) (l1 : ℕ) (vT : List ℕ) :
    Bool :=
  fL bns fun bF => fL uT fun uF => fL vT fun vF =>
    cond (Nat.ble (bNL uF) l0)
      (fH4 (toH4 (mkHbZ bZ bF)) fun h4 =>
        match bItD bZ s m l0 h4 uF with
        | none => false
        | some (endL, outT) => cond (muxNatListEq [endL] [l1]) (muxNatListEq outT vF) false)
      false
private theorem bSlSnd {s m : ℕ} {bns : List ℕ} {l0 : ℕ} {uT : List ℕ} {l1 : ℕ} {vT : List ℕ}
    (h : bSlChk s m bns l0 uT l1 vT = true) : pWOk s m bns l0 uT l1 vT := by
  unfold bSlChk at h
  unfold pWOk
  dsimp only [fL] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq] at h
  revert h
  cases hle : Nat.ble (bNL uT) l0 with
  | false =>
    intro h
    dsimp only [cond] at h
    exact Bool.noConfusion h
  | true =>
    intro h
    dsimp only [cond] at h
    rw [fH4e] at h
    revert h
    cases hi : bItD bZ s m l0 (toH4 (mkHbZ bZ bns)) uT with
    | none =>
      intro h
      dsimp only at h
      exact Bool.noConfusion h
    | some p =>
      cases p with
      | mk endL outT =>
        intro h
        dsimp only at h
        revert h
        cases he : muxNatListEq [endL] [l1] with
        | false =>
          intro h
          dsimp only [cond] at h
          exact Bool.noConfusion h
        | true =>
          intro h
          dsimp only [cond] at h
          have hl1 : endL = l1 := (List.cons.inj (muxNatListEq_eq_true.mp he)).1
          have hot : outT = vT := muxNatListEq_eq_true.mp h
          have hit := bItD_sound hbZ0 s m l0 bns uT endL outT hi
          rw [hl1, hot] at hit
          have hln : altIntLen (bDc bZ (rPad bZ l0 uT)) = l0 := by
            rw [← bNL_eq bZ]
            exact rPad_bNL bZ l0 uT hle
          refine u2f ?_
          rw [hln]
          exact hit.symm
private theorem bCh (k1 k2 mL : ℕ) {bns : List ℕ} {l0 : ℕ} {v0 : List ℕ}
    {l1 : ℕ} {v1 : List ℕ} {l2 : ℕ} {v2 : List ℕ}
    (h1 : pWOk k1 mL bns l0 v0 l1 v1) (h2 : bSlChk k2 mL bns l1 v1 l2 v2 = true) :
    pWOk (k1 + k2) mL bns l0 v0 l2 v2 :=
  (muxFastIterFullT16_add k1 k2 mL (uOh bns) (bDc bZ (rPad bZ l0 v0))).trans
    ((congrArg (muxFastIterFullT16 k2 mL (uOh bns)) h1).trans (bSlSnd h2))
private theorem bLift {n m : ℕ} {hb1 hb2 vi1 vi2 vo1 vo2 : List ℤ}
    (hw : muxFastIterFullT16 n m hb1 vi1 = vo1)
    (hhb : muxIntListEq hb1 hb2 = true) (hvi : muxIntListEq vi1 vi2 = true)
    (hvo : muxIntListEq vo1 vo2 = true) : muxFastIterFullT16 n m hb2 vi2 = vo2 := by
  rw [← muxIntListEq_eq_true.mp hhb, ← muxIntListEq_eq_true.mp hvi,
    ← muxIntListEq_eq_true.mp hvo]
  exact hw
private theorem bDm {a b : ℕ} (h : muxNatListEq [a] [b] = true) : a = b :=
  (List.cons.inj (muxNatListEq_eq_true.mp h)).1
private theorem bH {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) : b = true :=
  (rkmAllTrueF_cons h).1
private theorem bT {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: pCat xs ys
private def phbn_r384_0_p0 : List ℕ := [110782921173396,156160680491948,190632254877428,
  219401686646218,244491794786708,266943474390694,287377089525443,306198148241794,323689219473254,
  340056693963339,355456872180831,370011565350026,383817946064962,396955046248930,409488200845066,
  421472179940388,432953453982380,443971868772897,454561908191439,464753662429640,474573581678040,
  484045070741539,493188963851382,502023907965784,510566675271857,518832420273847,526834893047225,
  534586617479719,542099041293984,549382663139354,556447140906274,563301384554974,569953636088146,
  576411538784639,582682197410507,588772230808271,594687818014769,600434738857984,606018409822237,
  611443915840922,616716038569891,621839281607804,626817893058305,631655885769798,636357055539495,
  640924997527417,645363121091651,649674663227272,653862700766849,657930161479745,661879834189762,
  665714378015592,669436330825632,673048116987577,676552054483660,679950361454098,683245162224130,
  686438492863766,689532306323946,692528477188026,695428806073328,698235023713869,700948794752103,
  703571721264711]
private def phbn_r384_0_p1 : List ℕ := [706105346044949,708551155661815,710910583314355,
  713185011497653,715375774495479,717484160713192,719511414863234,721458740014424,723327299515302,
  725118218800804,726832587090806,728471458988305,730035855984361,731526767876325,732945154105341,
  734291945018625,735568043061582,736774323904404,737911637507456,738980809129396,739982640281687,
  740917909632879,741787373865783,742591768490423,743331808615462,744008189680568,744621588152036,
  745172662183810,745662052245893,746090381721995,746458257478147,746766270403891,747014995927530,
  747204994506852,747336812096614,747410980594012,747428018263273,747388430140429,747292708419261,
  747141332819357,746934770937133,746673478580645,746357900088950,745988468636724,745565606524816,
  745089725457346,744561226805952,743980501861723,743347932075333,742663889285862,741928735938749,
  741142825293300,740306501620145,739420100389014,738483948447170,737498364188819,736463657715809,
  735380130989867,734248077976661,733067784781907,731839529779737,730563583733548,729240209909497,
  727869664182824]
private def phbn_r384_0_p2 : List ℕ := [726452195137141,724988044156849,723477445512769,
  721920626441133,720317807215998,718669201215176,716975014979743,715235448267183,713450694098186,
  711620938797153,709746362026387,707827136813993,705863429575447,703855400128821,701803201703603,
  699706980943059,697566877900053,695383026026248,693155552154560,690884576474756,688570212502045,
  686212567038508,683811740127183,681367824998608,678880908009603,676351068574046,673778379085383,
  671162904830580,668504703895195,665803827059237,663060317683433,660274211585497,657445536905963,
  654574313963111,651660555096465,648704264498311,645705438032642,642664063040861,639580118133560,
  636453572967612,633284388007751,630072514271759,626817893058305,623520455656398,620180123035336,
  616796805513941,613370402407758,609900801652812,606387879404369,602831499609027,599231513548334,
  595587759351939,591900061478151,588168230159546,584392060811103,580571333398061,576705811760501,
  572795242891312,568839356163933,564837862505906,560790453513884,556696800505320,552556553501591,
  548369340136790]
private def phbn_r384_0_p3 : List ℕ := [544134764485809,539852405804699,535521817175551,
  531142524047299,526714022662939,522235778362593,517707223750666,513127756714009,508496738276493,
  503813490273657,499077292829166,494287381612547,489442944855148,484543120098331,479586990644540,
  474573581678040,469501856017626,464370709458473,459178965654235,453925370483561,448608585836988,
  443227182750591,437779633801516,432264304667195,426679444734287,421023176624620,415293484483029,
  409488200845066,403604991870227,397641340687091,391594528549076,385461613441163,379239405706162,
  372924440170294,366512944137339,360000800482027,353383504898616,346656116138268,339813197784132,
  332848749744861,325756127167314,318527943836848,311155956292058,303630923747884,295942437376757,
  288078710364359,280026317166340,271769866132747,263291583490727,254570777543565,245583138142083,
  236299805108784,226686105262331,216699801774342,206288604339196,195386519412647,183908303859900,
  171740659534030,158727473266365,144643296427138,129141087606528,111634993464637,90979591392394,
  64209909173665]
private def phbn_r384_0 : List ℕ := pCat phbn_r384_0_p0 (pCat phbn_r384_0_p1 (pCat phbn_r384_0_p2
  phbn_r384_0_p3))
private def phbv_r384_0 : List ℤ := uOh phbn_r384_0
private def pvn_r384_0_0 : List ℕ := [3000000000000000]
private def pvn_r384_0_1_p0 : List ℕ := [2000000064788373,2000000394156558,2000001689769600,
  2000005894376651,2000017744810878,2000047614307410,2000116223959467,2000261732867721,
  2000549411470896,2001083499609103,2002019965049990,2003577835292672,2006045819528142,
  2009780396084915,2015191745069911,2022715084122085,2032767136366777,2045690369790946,
  2061690776945667,2080777619832026,2102715039841112,2126995193671370,2152840426591729,
  2179238159823782,2205007276179642,2228889739001893,2249656948879589,2266217756592099,
  2277714601321925,2283595987118511,2283657073313394,2278044832141422,2267229153755704,
  2251945616278750,2233118737022104,2211776024012487,2188963020336424,2165668025590806,
  2142762729211991,2120962120235680,2100804241224773,2082648017559793,2066685752620921,
  2052966012254426,2041422471319126,2031904710996303,2024207742203669,2018097989385497,
  2013334430616870,2009684431759765,2006934463711456,2004896328992098,2003409759495603,
  2002342316493282,2001587472606457,2001061629549528,2000700664903181,2000456436369267,
  2000293522949541,2000186360086674,2000116833558328,2000072333398602,2000044230044944,
  2000026714796463]
private def pvn_r384_0_1_p1 : List ℕ := [2000015940033264,2000009396682590,2000005473325710,
  2000003150367599,2000001792027300,2000001007488779,2000000559867617,2000000307550161,
  2000000167019302,2000000089674891,2000000047605884,2000000024990035,2000000012972370,
  2000000006659576,2000000003381240,2000000001697983,2000000000843419,2000000000414408,
  2000000000201421,2000000000096847,2000000000046062,2000000000021670,2000000000010082,
  2000000000004636,2000000000002104,2000000000000943,2000000000000415,2000000000000177,
  2000000000000072,2000000000000025,2000000000000007,2000000000000001]
private def pvn_r384_0_1 : List ℕ := pCat pvn_r384_0_1_p0 pvn_r384_0_1_p1
private def pvn_r384_0_2_p0 : List ℕ := [2000000000000003,2000000000000005,2000000000000006,
  2000000000000012,2000000000000017,2000000000000060,2000000000000227,2000000000000835,
  2000000000002957,2000000000009811,2000000000030786,2000000000091792,2000000000261069,
  2000000000710581,2000000001856441,2000000004667184,2000000011316156,2000000026512793,
  2000000060127410,2000000132195296,2000000282151988,2000000585345290,2000001181655128,
  2000002323607381,2000004454855870,2000008334420238,2000015227556710,2000027190307647,
  2000047480974252,2000081136878252,2000135757198063,2000222530257179,2000357533927846,
  2000563318256228,2000870747908467,2001321037530204,2001967856335305,2002879312385907,
  2004139558241417,2005849697134517,2008127624357969,2011106425350631,2014930982918935,
  2019752531275996,2025721038989135,2032975503710546,2041632486655150,2051773482435896,
  2063431979853057,2076581285820435,2091124321034882,2106886619985031,2123613657396352,
  2140973371328249,2158564371308419,2175929838501380,2192576590986672,2207998259252116,
  2221701057531954,2233230303677150,2242195678988917,2248293255313151,2251322551288116,
  2251197290045935]
private def pvn_r384_0_2_p1 : List ℕ := [2247949072346449,2241723791910738,2232771236009519,
  2221428868100525,2208101224472861,2193236634109764,2177303071646884,2160764880241510,
  2144061876665387,2127592012178441,2111698355764551,2096660739432988,2082692003043376,
  2069938434441453,2058483743921261,2048355751750275,2039534903249650,2031963747273830,
  2025556603415456,2020208779657981,2015804863651511,2012225777364873,2009354440356932,
  2007080019789136,2005300848923510,2003926168023044,2002876883707882,2002085558890425,
  2001495840858661,2001061515857216,2000745350339664,2000517846873308,2000356010354869,
  2000242190485699,2000163041028193,2000108615978776,2000071607505940,2000046719893317,
  2000030167095497,2000019278039155,2000012192667327,2000007632193420,2000004728490663,
  2000002899515663,2000001759806280,2000001057175211,2000000628604533,2000000369965917,
  2000000215528328,2000000124282419,2000000070938425,2000000040079584,2000000022414937,
  2000000012408718,2000000006799749,2000000003688386,2000000001980426,2000000001052586,
  2000000000553769,2000000000288382,2000000000148653,2000000000075844,2000000000038297,
  2000000000019134]
private def pvn_r384_0_2_p2 : List ℕ := [2000000000009456,2000000000004619,2000000000002229,
  2000000000001057,2000000000000492,2000000000000224,2000000000000096,2000000000000037,
  2000000000000013,2000000000000003]
private def pvn_r384_0_2 : List ℕ := pCat pvn_r384_0_2_p0 (pCat pvn_r384_0_2_p1 pvn_r384_0_2_p2)
private def pvi_r384_0 : List ℤ := bDc bZ (rPad bZ 1 pvn_r384_0_0)
private def pvo_r384_0 : List ℤ := bDc bZ (rPad bZ 257 pvn_r384_0_2)
private def phbn_r384_1_p0 : List ℕ := [110763552977578,156133378895215,190598926609835,
  219363328614269,244449050247142,266896804620394,287326847342943,306144615570590,323632628835270,
  339997241797174,355394727599047,369946876168908,383750843112097,396885646534740,409416609957454,
  421398493891795,432877760660811,443894249100109,454482437060366,464672409472544,474490611902892,
  483960445064445,493102739545994,501936139045704,510477412818403,518741712718874,526742786418657,
  534493155615929,542004266031937,549286614480537,556349857163679,563202902483866,569853991002840,
  576310764663171,582580326988790,588669295665041,594583848648482,600329764756607,605912459526773,
  611337017003374,616608218006283,621730565346797,626708306385862,631545453270316,636245801133751,
  640812944507645,645250292154027,649561080502047,653748385846352,657815135444441,661764117632546,
  665597991064467,669319293164902,672930447877695,676433772779825,679831485623712,683125710363199,
  686318482712328,689411755280607,692407402323656,695307224143995,698112951173058,700826247762267,
  703448715708214]
private def phbn_r384_1_p1 : List ℕ := [705981897534427,708427279550006,710786294703432,
  713060325248087,715250705234468,717358722842682,719385622567556,721332607267579,723200840087901,
  724991446266698,726705514833418,728344100206681,729908223698961,731398874934560,732817013186884,
  734163568640498,735439443583030,736645513531579,737782628297912,738851612996407,739853268998397,
  740788374836299,741657687060632,742461941052831,743201851796537,743878114609833,744491405840748,
  745042383528162,745531688030102,745959942621293,746327754061668,746635713137462,746884395176379,
  747074360538219,747206155082291,747280310612798,747297345303361,747257764101714,747162059115591,
  747010709980707,746804184211730,746542937537026,746227414217969,745858047353503,745435259170646,
  744959461301539,744431055047649,743850431631654,743217972437541,742534049239380,741799024419244,
  741013251174679,740177073716126,739290827454664,738354839180413,737369427231916,736334901656804,
  735251564364012,734119709267816,732939622423909,731711582157758,730435859185420,729112716727027,
  727742410613082]
private def phbn_r384_1_p2 : List ℕ := [726325189383739,724861294381196,723350959835319,
  721794412942611,720191873938617,718543556163845,716849666123263,715110403539429,713325961399289,
  711496525994668,709622276956459,707703387282515,705740023359219,703732344976702,701680505337664,
  699584651059730,697444922171281,695261452100648,693034367658573,690763789013810,688449829661722,
  686092596385719,683692189211346,681248701352844,678762219151933,676232822008609,673660582303662,
  671045565312641,668387829110950,665687424469721,662944394742100,660158775739538,657330595597651,
  654459874631165,651546625177447,648590851428051,645592549247693,642551705979987,639468300239267,
  636342301687710,633173670796962,629962358593369,626708306385862,623411445475463,620071696845288,
  616688970829836,613263166762256,609794172598164,606281864514479,602726106481585,599126749807031,
  595483632648765,591796579495785,588065400613847,584289891453694,580469832019036,576604986191243,
  572695101007434,568739905888363,564739111812113,560692410429252,556599473114697,552459949951014,
  548273468637395]
private def phbn_r384_1_p3 : List ℕ := [544039633317952,539758023322295,535428191810649,
  531049664314914,526621937166159,522144475797980,517616712913980,513038046506277,508407837710455,
  503725408480616,498990039066281,494200965270606,489357375466859,484458407347188,479503144374302,
  474490611902892,469419772933087,464289523453107,459098687322268,453846010638478,448530155526215,
  443149693271379,437703096718158,432188731829711,426604848298757,420949569075349,415220878656751,
  409416609957454,403534429544980,397571820987934,391526066015052,385394223125668,379173103220239,
  372859241730806,366448866620727,359937861484532,353321722803964,346595510194070,339753788188443,
  332790557744735,325699175171528,318472255545509,311101556846480,303577839904949,295890697713123,
  288028345517376,279977360120547,271722352563607,263245552181098,254526270893833,245540202802784,
  236258492776084,226646473694311,216661916113357,206252538869524,195352359956225,183876151141737,
  171710634087070,158699722916841,144618008416502,129118509849538,111615476300884,90963685415888,
  64198683344980]
private def phbn_r384_1 : List ℕ := pCat phbn_r384_1_p0 (pCat phbn_r384_1_p1 (pCat phbn_r384_1_p2
  phbn_r384_1_p3))
private def phbv_r384_1 : List ℤ := uOh phbn_r384_1
private def pvn_r384_1_0_p0 : List ℕ := [1999999999999997,1999999999999995,1999999999999994,
  1999999999999988,1999999999999983,1999999999999940,1999999999999773,1999999999999165,
  1999999999997043,1999999999990189,1999999999969214,1999999999908208,1999999999738931,
  1999999999289419,1999999998143559,1999999995332816,1999999988683844,1999999973487207,
  1999999939872590,1999999867804704,1999999717848012,1999999414654710,1999998818344872,
  1999997676392619,1999995545144130,1999991665579762,1999984772443290,1999972809692353,
  1999952519025748,1999918863121748,1999864242801937,1999777469742821,1999642466072154,
  1999436681743772,1999129252091533,1998678962469796,1998032143664695,1997120687614093,
  1995860441758583,1994150302865483,1991872375642031,1988893574649369,1985069017081065,
  1980247468724004,1974278961010865,1967024496289454,1958367513344850,1948226517564104,
  1936568020146943,1923418714179565,1908875678965118,1893113380014969,1876386342603648,
  1859026628671751,1841435628691581,1824070161498620,1807423409013328,1792001740747884,
  1778298942468046,1766769696322850,1757804321011083,1751706744686849,1748677448711884,
  1748802709954065]
private def pvn_r384_1_0_p1 : List ℕ := [1752050927653551,1758276208089262,1767228763990481,
  1778571131899475,1791898775527139,1806763365890236,1822696928353116,1839235119758490,
  1855938123334613,1872407987821559,1888301644235449,1903339260567012,1917307996956624,
  1930061565558547,1941516256078739,1951644248249725,1960465096750350,1968036252726170,
  1974443396584544,1979791220342019,1984195136348489,2012225777364873,2009354440356932,
  2007080019789136,2005300848923510,2003926168023044,2002876883707882,2002085558890425,
  2001495840858661,2001061515857216,2000745350339664,2000517846873308,2000356010354869,
  2000242190485699,2000163041028193,2000108615978776,2000071607505940,2000046719893317,
  2000030167095497,2000019278039155,2000012192667327,2000007632193420,2000004728490663,
  2000002899515663,2000001759806280,2000001057175211,2000000628604533,2000000369965917,
  2000000215528328,2000000124282419,2000000070938425,2000000040079584,2000000022414937,
  2000000012408718,2000000006799749,2000000003688386,2000000001980426,2000000001052586,
  2000000000553769,2000000000288382,2000000000148653,2000000000075844,2000000000038297,
  2000000000019134]
private def pvn_r384_1_0_p2 : List ℕ := [2000000000009456,2000000000004619,2000000000002229,
  2000000000001057,2000000000000492,2000000000000224,2000000000000096,2000000000000037,
  2000000000000013,2000000000000003]
private def pvn_r384_1_0 : List ℕ := pCat pvn_r384_1_0_p0 (pCat pvn_r384_1_0_p1 pvn_r384_1_0_p2)
private def pvn_r384_1_1_p0 : List ℕ := [1999999999999997,1999999999999999,1999999999999989,
  1999999999999999,1999999999999998,2000000000000003,1999999999999996,1999999999999994,
  1999999999999993,1999999999999999,1999999999999996,1999999999999999,1999999999999996,
  1999999999999993,1999999999999995,1999999999999989,1999999999999987,1999999999999979,
  1999999999999994,2000000000000001,1999999999999994,1999999999999991,1999999999999993,
  1999999999999992,1999999999999985,2000000000000011,1999999999999868,2000000000000469,
  1999999999998019,2000000000007486,1999999999971763,2000000000100976,1999999999647821,
  2000000001175566,1999999996196716,2000000011810247,1999999964573650,2000000102049045,
  1999999716768745,2000000754305275,1999998069374664,2000004733014422,1999988881886611,
  2000024944059927,1999946581627418,2000108795333255,1999789616697979,2000384447730278,
  1999338231642271,2001065532468238,1998404979792647,2002192277388100,1997271059026798,
  2002986022807593,1997260238564713,2001815454971037,1999655246135809,1998688986628375,
  2002340249477295,1997705646714494,2000773393779552,2001010430045814,1997512037359645,
  2001517233206294]
private def pvn_r384_1_1_p1 : List ℕ := [1999871215414998,1997365937561449,2001146754005341,
  1998955377448419,1996214970572071,1999402882361577,1997446231422029,1993230818103799,
  1994921807579360,1993691763096160,1987380190101181,1985478833719472,1984551155553187,
  1976995585983304,1969186376422701,1965643496255903,1958582744537284,1945715941286442,
  1934843393420714,1926755653554326,1914016574113320,1896518081075072,1881539824392470,
  1869809000772908,1854957641542811,1835900350379835,1818987192299104,1807414506851472,
  1796804772347089,1783243110878672,1769812989232829,1762054744576960,1760300971875166,
  1759912813384607,1757986481715023,1756989481596736,1761307208896523,1771871080696032,
  1785239889674113,1797386385495652,1807496590210959,1818091088567827,1832075505354786,
  1849931696066833,1869352026183092,1887067989230301,1901030454540120,1911367779395789,
  1919833094521686,1928492911020422,1938611259580506,1950246581867184,1962519464898280,
  1974194526471922,1984213302506987,1991983651514326,1997413242618051,2000779627398558,
  2002548002485365,2003214750971082,2003209495401272,2002854453220024,2002363784268885,
  2001863417776487]
private def pvn_r384_1_1_p2 : List ℕ := [2001416672230992,2001047368155280,2000757230997032,
  2000537428534807,2000375421740327,2000258584259382,2000175828335927,2000118119119697,
  2000078435614538,2000051499464212,2000033440192949,2000021476184665,2000013642426674,
  2000008572010474,2000005327611745,2000003275205318,2000001991566528,2000001197826041,
  2000000712568077,2000000419259366,2000000243978962,2000000140418372,2000000079925546,
  2000000044990937,2000000025045468,2000000013787466,2000000007505451,2000000004040088,
  2000000002150360,2000000001131670,2000000000588838,2000000000302914,2000000000154046,
  2000000000077437,2000000000038472,2000000000018885,2000000000009153,2000000000004375,
  2000000000002061,2000000000000953,2000000000000430,2000000000000186,2000000000000076,
  2000000000000028,2000000000000008,2000000000000001]
private def pvn_r384_1_1 : List ℕ := pCat pvn_r384_1_1_p0 (pCat pvn_r384_1_1_p1 pvn_r384_1_1_p2)
private def pvn_r384_1_2_p0 : List ℕ := [1999999999999997,2000000000000005,1999999999999999,
  2000000000000028,1999999999999828,2000000000001036,1999999999994423,2000000000027016,
  1999999999879617,2000000000496800,1999999998089718,2000000006873360,1999999976779541,
  2000000073848749,1999999778452914,2000000627910844,1999998316927770,2000004269392057,
  1999989748133771,2000023300075744,1999949905195721,2000101782327083,1999804868896484,
  2000352207689367,1999403290391778,2000944903426362,1998609703195110,2001884596835219,
  1997676848946821,2002548803394613,1997610942796816,2001731462924159,1999381579976975,
  1999312219148324,2001735275296905,1997950604193661,2001399300436872,1999974427807084,
  1998638705999870,2001918324758964,1998777301323662,1999676101906539,2001632716393093,
  1998328021187025,2000342870563460,2001282737059213,1998237390670763,2000598088185402,
  2001150271137068,1998253953534459,2000523545525006,2001267865235492,1998343479125395,
  2000148023749107,2001542292297253,1998629645828018,1999490487446707,2001748830555905,
  1999295193669175,1998708919925949,2001527843122074,2000377950335804,1998244813275359,
  2000572544098284]
private def pvn_r384_1_2_p1 : List ℕ := [2001474552949244,1998709375950330,1999100322879896,
  2001684473069343,2000238857546632,1998212471673064,2000366612993689,2001690217110090,
  1999150335102441,1998510099766327,2001198116996870,2001265620401706,1998570011275513,
  1998928102167945,2001572824093093,2000941116150324,1998347517080605,1999106879673512,
  2001680191119958,2000930190020478,1998332878174318,1998929833054941,2001570709607251,
  2001256334985436,1998557225480472,1998406763190056,2001043071545477,2001712240325430,
  1999158850693883,1997685849088977,1999639662414550,2001509326068322,1999875493901934,
  1996930018808075,1996751779071160,1998776674445060,1998748624970821,1995222366834474,
  1991529922110665,1990623061522545,1990711904332159,1987819374825883,1981220892706863,
  1974158965727036,1969230547886161,1964885415391671,1957443831492959,1945682242148783,
  1932168455004845,1920022588851086,1909292292769930,1897129408774100,1881239165753094,
  1862551977175341,1844356285690837,1829124887240962,1816443762231751,1803940555482416,
  1790000069120440,1775557515557019,1763459284765025,1756212280815343,1754180740584357,
  1755614005712511]
private def pvn_r384_1_2_p2 : List ℕ := [1758233826196603,1760975128259265,1764605031801083,
  1770962325761050,1781541414975833,1796432625277239,1814208538047237,1832661974122845,
  1849839154682015,1864778989803164,1877661719595436,1889434134018234,1901204814502889,
  1913723275869148,1927129626255725,1940994744681840,1954551855998814,1966981715914683,
  1977641030566915,1986181188238777,1992558521157650,1996969991728864,1999756998898709,
  2001312139400713,2002009000773071,2002161027898409,2002006032571396,2001708599031885,
  2001372227080859,2001054773366865,2000783113308486,2000565045528609,2000397930360109,
  2000274381050045,2000185664154245,2000123502263808,2000080862705098,2000052162158703,
  2000033173598904,2000020809900548,2000012880535525,2000007868320460,2000004744343703,
  2000002823915205,2000001659299701,2000000962494303,2000000551142921,2000000311536194,
  2000000173824640,2000000095730267,2000000052035053,2000000027914056,2000000014777455,
  2000000007719579,2000000003978972,2000000002023463,2000000001015145,2000000000502374,
  2000000000245208,2000000000118028,2000000000056013,2000000000026200,2000000000012073,
  2000000000005477]
private def pvn_r384_1_2_p3 : List ℕ := [2000000000002439,2000000000001063,2000000000000451,
  2000000000000183,2000000000000069,2000000000000022,2000000000000005,2000000000000001]
private def pvn_r384_1_2 : List ℕ := pCat pvn_r384_1_2_p0 (pCat pvn_r384_1_2_p1 (pCat
  pvn_r384_1_2_p2 pvn_r384_1_2_p3))
private def pvn_r384_1_3_p0 : List ℕ := [1999999974156686,2000000190535975,1999999033576541,
  2000003886295568,1999986888219665,2000038227713035,1999902022584755,2000222980708350,
  1999547040110476,2000822275944230,1998669965224207,2001901081691744,1997639089663071,
  2002460697144458,1998020260018790,2000887186184583,2000524984897933,1998331054156615,
  2001927496497678,1998927528768571,1999555999863736,2001636333843903,1998378310478132,
  2000353840508596,2001188175903501,1998303290979667,2000681909894350,2000959420615641,
  1998340610453007,2000692561280872,2000983888584227,1998398321711489,2000460652464492,
  2001193073607179,1998537239801400,2000003163549313,2001455127397920,1998887229435864,
  1999369466644424,2001560021201270,1999553807228768,1998739491853195,2001256849250743,
  2000478801388872,1998456619521027,2000413308272006,2001313602845816,1998881923485189,
  1999262161839152,2001485382105741,2000031424145584,1998497649951773,2000626148637061,
  2001243552609655,1998874625896704,1999182507243992,2001425957334337,2000327667684832,
  1998461640274785,2000147724389371,2001501392400913,1999438911957486,1998636413343075,
  2000891716157927]
private def pvn_r384_1_3_p1 : List ℕ := [2001171019816986,1998861695271376,1999038774379889,
  2001311148556463,2000761535813233,1998574261592552,1999409962690190,2001498256685265,
  2000457689653557,1998457212388186,1999629363822812,2001569785729005,2000332160397698,
  1998414676236766,1999655978041227,2001590743877096,2000407061610736,1998417509350173,
  1999478968738114,2001552075337607,2000683631732562,1998513702118959,1999111221659017,
  2001368029659604,2001124214126095,1998821982922372,1998631199270381,2000898253871361,
  2001590170447846,1999482606157214,1998256091619927,2000038294108146,2001775947002158,
  2000513065118436,1998369854044713,1998920557760348,2001262638658957,2001568929973007,
  1999337066312149,1998138024641760,1999878156528227,2001834343509867,2000967484866379,
  1998599918206489,1998325664810825,2000564660455402,2001997535513822,2000514260810997,
  1998255300269819,1998456169097408,2000837387925522,2002065464884883,2000423322432983,
  1998117681969452,1998217856341012,2000550137174458,2001988437477277,2000551334479897,
  1997884528777076,1997083803145579,1998796389821169,2000452054322576,1999378636515361,
  1995897571630324]
private def pvn_r384_1_3_p2 : List ℕ := [1992792376513925,1991966815274176,1992222705707397,
  1990549869176680,1985308767450091,1977790398009405,1970630673438368,1964927533894835,
  1959063119363284,1950281463703993,1937305642476725,1921452777788885,1905344701996181,
  1890582489402950,1876528840366148,1861153301545292,1843045988927304,1822841496116987,
  1802968689762616,1786073668953885,1773420332659665,1764416408117160,1757453431536709,
  1751315436135394,1746142426168158,1743380820417957,1744879700352411,1751783459416695,
  1763880396405748,1779696404148885,1797171957815357,1814495494474034,1830680026183234,
  1845682227193599,1860115811293149,1874772806622677,1890190141487037,1906416301381241,
  1923012377688490,1939225317879447,1954228803880530,1967336432749480,1978130998151542,
  1986497848469062,1992582480600198,1996706687386686,1999276305001234,2000703530763091,
  2001354530784172,2001523052076246,2001424778773702,2001205030262346,2000952904809585,
  2000716776334741,2000518109192522,2000362267071140,2000246142269251,2000163049990995,
  2000105557937998,2000066910468171,2000041584887457,2000025367302080,2000015200424818,
  2000008952326821]
private def pvn_r384_1_3_p3 : List ℕ := [2000005184420947,2000002953099407,2000001654833922,
  2000000912387738,2000000494966544,2000000264207316,2000000138762073,2000000071700930,
  2000000036447477,2000000018224297,2000000008962302,2000000004334232,2000000002060920,
  2000000000963364,2000000000442605,2000000000199823,2000000000088627,2000000000038598,
  2000000000016493,2000000000006910,2000000000002831,2000000000001130,2000000000000436,
  2000000000000159,2000000000000053,2000000000000015,2000000000000003]
private def pvn_r384_1_3 : List ℕ := pCat pvn_r384_1_3_p0 (pCat pvn_r384_1_3_p1 (pCat
  pvn_r384_1_3_p2 pvn_r384_1_3_p3))
private def pvn_r384_1_4_p0 : List ℕ := [1999729111870878,2000874131601180,1998214535314706,
  2002552958600741,1997541003637833,2001129063344034,2000837839357872,1997976203094904,
  2001380562904582,2000541393137170,1998170387522815,2001102715905699,2000839747409243,
  1998261198159607,2000506486753923,2001326293167338,1998584152262031,1999644489804096,
  2001614777831235,1999358911751486,1998790301968795,2001317199593218,2000473029622580,
  1998451522919373,2000317839717891,2001375417097483,1999037235575839,1999075769497220,
  2001359307841466,2000341483945946,1998511921488132,2000246473345304,2001384762554683,
  1999248626162351,1998887673395401,2001125070508173,2000739648238846,1998647133088600,
  1999671930560940,2001443584589632,1999924862704627,1998580226213791,2000438329296343,
  2001309765157084,1999255958170170,1998857911566985,2000986096331043,2000942109157519,
  1998833653916541,1999269571266698,2001291691560004,2000522520968846,1998628338356839,
  1999670868329042,2001416635083178,2000157072388223,1998563350667870,1999989848996124,
  2001440684797313,1999890078308128,1998563702994256,2000202737157457,2001429478016801,
  1999731456019807]
private def pvn_r384_1_4_p1 : List ℕ := [1998575351507037,2000307760693585,2001424705113448,
  1999679359800956,1998568929640884,2000307075616815,2001443711651213,1999733459616019,
  1998538885376028,2000198162054478,2001480212123483,1999899063213861,1998503712103392,
  1999974097228172,2001502893272725,2000182352553795,1998508162816746,1999633071041147,
  2001453333988369,2000575801493159,1998623583050761,1999198182666520,2001249741718232,
  2001033526859241,1998937096341555,1998745601566309,2000808360245220,2001442505740208,
  1999516033399075,1998428934300606,2000095979311899,2001610267989623,2000337851156630,
  1998469181555293,1999214210889621,2001309450879158,2001201255209997,1999063728065479,
  1998475090763038,2000423138727113,2001691026494693,2000188656029297,1998360895079415,
  1999175843719003,2001330524632018,2001377548084458,1999231876657138,1998274413042173,
  2000013885041888,2001753724795178,2000802799353494,1998606656491072,1998504648635505,
  2000662601642672,2001856147950824,2000303588154974,1998280616297672,1998745913994508,
  2001039042972793,2001870860173464,2000045514222726,1998127340580509,1998803617025604,
  2001152321943368]
private def pvn_r384_1_4_p2 : List ℕ := [2001954305431201,2000106791331651,1998083680923917,
  1998585239060329,2000966062989657,2002125220765877,2000553571293598,1998242239275307,
  1998109985970578,2000336050367386,2002180657444594,2001379155956895,1998865894856245,
  1997602099118605,1999049653899915,2001492365749783,2002050239071762,1999939357575426,
  1997278889513939,1996670900134111,1998330811694154,1999851387084912,1998709296378042,
  1994773911211827,1990265103150950,1987345902853453,1985853256020377,1983349690455338,
  1977307632675528,1967269965824601,1955034893885783,1942851935825147,1931361512882433,
  1919071202070397,1903701545047698,1884168271437086,1861582490676511,1838583986652823,
  1817658575938770,1799758851210177,1784162761124824,1769515704455452,1755202222901504,
  1742092234560430,1732242754435454,1727845024069243,1730114893103639,1738747876169845,
  1752147490979087,1768193149736606,1785088907190422,1801891764877016,1818557132023003,
  1835594361143268,1853571598620737,1872710740949906,1892712369980680,1912821867720336,
  1932053596163202,1949456606703931,1964325246794374,1976305361446242,1985394732297876,
  1991868085105552]
private def pvn_r384_1_4_p3 : List ℕ := [1996167937872860,1998797242569182,2000236294881411,
  2000892104133214,2001077784803619,2001013944464932,2000842784655712,2000647079798190,
  2000468744397847,2000324205617059,2000215695159887,2000138727763291,2000086560256781,
  2000052531636500,2000031067094916,2000017930060118,2000010109589202,2000005573209627,
  2000003005743908,2000001586542450,2000000819824700,2000000414787453,2000000205489426,
  2000000099678582,2000000047339427,2000000022008406,2000000010014129,2000000004458538,
  2000000001941798,2000000000827001,2000000000344300,2000000000140055,2000000000055632,
  2000000000021561,2000000000008143,2000000000002987,2000000000001062,2000000000000361,
  2000000000000114,2000000000000033,2000000000000007]
private def pvn_r384_1_4 : List ℕ := pCat pvn_r384_1_4_p0 (pCat pvn_r384_1_4_p1 (pCat
  pvn_r384_1_4_p2 pvn_r384_1_4_p3))
private def pvn_r384_1_5_p0 : List ℕ := [1996731846971603,1998748496737383,2001995642982064,
  2001452146727423,1998520741231620,1998458025851654,2001141521839079,2001585407374673,
  1999113097913481,1998396088324337,2000681181296155,2001607312625604,1999492233058688,
  1998399171994357,2000357137335286,2001587447787506,1999776785856940,1998431060488649,
  2000101828310401,2001546337118648,2000010025304352,1998479797298826,1999885412375973,
  2001490776725565,2000213565499953,1998541931133543,1999691729030013,2001421915302407,
  2000399708054586,1998617983660307,1999511372743453,2001337962338634,2000575558988522,
  1998710747142493,1999339167497280,2001235312278518,2000744584369031,1998824495727892,
  1999173240861067,2001109146960019,2000907104054164,1998964469622864,1999014840734671,
  2000953937706507,2001060244887023,1999136328291873,1998868553733904,2000764087732947,
  2001197599045243,1999345365331524,1998742724055801,2000534905061021,2001308777647936,
  1999595304544366,1998649869229557,2000264077635202,2001379096536406,1999886519135934,
  1998606805442596,1999953784377903,2001389746818631,2000213581863825,1998634052349610,
  1999613468189789]
private def pvn_r384_1_5_p1 : List ℕ := [2001318965907635,2000562219147098,1998753914356358,
  1999263057163757,2001144891001931,2000906074106412,1998986500434010,1998935979709829,
  2000850845638167,2001204244751016,1999342989530751,1998680634206716,2000433589928140,
  2001401360254188,1999815918847370,1998558101479487,1999914258207062,2001432835748441,
  2000367507128340,1998633122464445,1999349961134004,2001238425403127,2000919339720187,
  1998955413640626,1998841148301173,2000786300010843,2001350089408110,1999530504453985,
  1998526263954606,2000106140519779,2001511268536454,2000285012419657,1998552871033441,
  1999321771915475,2001271377675768,2001041425877484,1999017354660228,1998662058908968,
  2000591049403831,2001529647013079,1999879432846241,1998418461515374,1999610191289007,
  2001467636203602,2000886919317368,1998822284868936,1998692925101510,2000723907299569,
  2001583052003127,1999854260526723,1998345454453491,1999511757270488,2001481360015863,
  2001084259466043,1998942484646544,1998465859578001,2000423184989920,2001733811291099,
  2000329700769095,1998391920230445,1998937245298339,2001137682174347,2001610989636641,
  1999618434508630]
private def pvn_r384_1_5_p2 : List ℕ := [1998181930242408,1999485084625746,2001582859639591,
  2001335353744917,1999093296349657,1998162946006326,1999924645430236,2001822599473495,
  2001099073401297,1998777133347841,1998173454124342,2000162358073225,2001953447614782,
  2001030488808109,1998655849423183,1998100673228216,2000143098098294,2002026225733446,
  2001205833781349,1998755426299229,1997913022776360,1999802502418556,2001985564247371,
  2001643796289160,1999190059989191,1997714456213238,1999079041583408,2001616813762945,
  2002219193612979,2000133356708633,1997840294562566,1998064226548253,2000566342984254,
  2002460398920569,2001558656677425,1998836386700364,1997287815747106,1998582133582279,
  2001254489498699,2002306623828255,2000365381376390,1997027672185615,1995093187411609,
  1995620730427559,1996788549037123,1995569407052284,1990453167342777,1982593886642627,
  1974424921986865,1967169418117465,1959545553802952,1948731559386597,1932636540365488,
  1911526299926767,1887769260901088,1864083371297082,1841776419431309,1820297355376254,
  1798284869643842,1775194301746857,1752289715882330,1732369264592002,1718500249723391,
  1712621470426319]
private def pvn_r384_1_5_p3 : List ℕ := [1714821578670299,1723583122717959,1736701506281936,
  1752291868086146,1769380281445024,1787898317730068,1808231544369926,1830643907510651,
  1854873415180523,1880041099599713,1904843751168248,1927892851656902,1948043049557541,
  1964601552209273,1977382818113608,1986634204940918,1992889571519988,1996809468440113,
  1999049468152211,2000175447180022,2000625702110868,2000708749953131,2000622279004090,
  2000480480580786,2000341038854935,2000227234758474,2000143800382809,2000087054030853,
  2000050655625822,2000028425187722,2000015417994588,2000008097053615,2000004122096993,
  2000002035920278,2000000976088700,2000000454398465,2000000205424243,2000000090179794,
  2000000038434476,2000000015897933,2000000006379233,2000000002481718,2000000000935377,
  2000000000341278,2000000000120413,2000000000041032,2000000000013480,2000000000004255,
  2000000000001283,2000000000000365,2000000000000095,2000000000000020,2000000000000002]
private def pvn_r384_1_5 : List ℕ := pCat pvn_r384_1_5_p0 (pCat pvn_r384_1_5_p1 (pCat
  pvn_r384_1_5_p2 pvn_r384_1_5_p3))
private def pvi_r384_1 : List ℤ := bDc bZ (rPad bZ 257 pvn_r384_1_0)
private def pvo_r384_1 : List ℤ := bDc bZ (rPad bZ 257 pvn_r384_1_5)
private def phbn_r384_2_p0 : List ℕ := [92708167991857,130810390239591,159843434770709,
  184148752477482,205412119132233,224500140031266,241928807492242,258035086840317,273053565449875,
  287155429828221,300470201780690,313098731604584,325121398704019,336603518905133,347599040788661,
  358153149981273,368304151870255,378084863198582,387523660721757,396645284978135,405471465705157,
  414021415060761,422312221314373,430359166535812,438175985502728,445775078614495,453167688434900,
  460364047191911,467373500877865,474204614340467,480865260812642,487362698612958,493703637198562,
  499894294326690,505940445748103,511847468593852,517620379408916,523263867620239,528782325093164,
  534179872322208,539460381714190,544627498349739,549684658549983,554635106526249,559481909349916,
  564227970445598,568876041782382,573428734913886,577888530997650,582257789907228,586538758535734,
  590733578377096,594844292460615,598872851705216,602821120751860,606690883325732,610483847173894,
  614201648618911,617845856764470,621417977385071,624919456528438,628351683856239,631715995746102,
  635013678175490]
private def phbn_r384_2_p1 : List ℕ := [638245969406008,641414062484799,644519107578121,
  647562214150702,650544453003219,653466858179054,656330428750501,659136130493624,661884897460196,
  664577633454355,667215213420986,669798484752224,672328268517911,674805360625403,677230532913612,
  679604534185823,681928091185442,684201909518486,686426674526355,688603052112129,690731689523397,
  692813216094384,694848243949963,696837368673907,698781169943593,700680212133219,702535044887396,
  704346203666918,706114210268326,707839573318797,709522788747789,711164340236759,712764699648200,
  714324327435140,715843673032199,717323175229198,718763262528271,720164353485373,721526857036988,
  722851172812846,724137691435350,725386794806415,726598856382350,727774241437397,728913307316486,
  730016403677747,731083872725281,732116049432658,733113261757602,734075830848267,735004071241518,
  735898291053584,736758792163436,737585870389231,738379815658138,739140912169836,739869438553985,
  740565668021923,741229868512850,741862302834740,742463228800208,743032899357555,743571562717181,
  744079462473581]
private def phbn_r384_2_p2 : List ℕ := [744556837723096,745003923177602,745420949274296,
  745808142281749,746165724402373,746493913871439,746792925052797,747062968531418,747304251202881,
  747516976359937,747701343776242,747857549787393,747985787369339,748086246214296,748159112804233,
  748204570482035,748222799520423,748213977188712,748178277817485,748115872861252,748026930959182,
  747911617993953,747770097148801,747602528962825,747409071384607,747189879824205,746945107203571,
  746674904005451,746379418320809,746058795894834,745713180171563,745342712337173,744947531361979,
  744527774041185,744083575034413,743615066904063,743122380152531,742605643258313,742064982711042,
  741500523045478,740912386874483,740300694921010,739665566049141,739007117294179,738325463891851,
  737620719306612,736892995259101,736142401752750,735369047099585,734573037945228,733754479293113,
  732913474527961,732050125438495,731164532239447,730256793592843,729327006628607,728375266964481,
  727401668725276,726406304561485,725389265667245,724350641797676,723290521285611,722208991057710,
  721106136649991]
private def phbn_r384_2_p3 : List ℕ := [719982042222766,718836790575009,717670463158151,
  716483140089315,715274900164004,714045820868236,712795978390142,711525447631034,710234302215935,
  708922614503598,707590455595988,706237895347265,704865002372244,703471844054344,702058486553034,
  700624994810769,699171432559424,697697862326215,696204345439128,694690942031834,693157711048101,
  691604710245697,690031996199792,688439624305838,686827648781941,685196122670716,683545097840618,
  681874624986746,680184753631118,678475532122406,676747007635130,674999226168300,673232232543494,
  671446070402382,669640782203658,667816409219401,665972991530824,664110568023432,662229176381546,
  660328853082202,658409633388399,656471551341691,654514639754094,652538930199307,650544453003219,
  648531237233681,646499310689537,644448699888877,642379430056503,640291525110573,638185007648405,
  636059898931419,633916218869178,631753986002507,629573217485658,627373929067484,625156135071598,
  622919848375468,620665080388418,618391841028493,616100138698145,613789980258697,611461371003530,
  609114314629959]
private def phbn_r384_2_p4 : List ℕ := [606748813209725,604364867158068,601962475201300,
  599541634342842,597102339827634,594644585104866,592168361788950,589673659618660,587160466414350,
  584628768033173,582078548322202,579509789069368,576922469952094,574316568483532,571692059956289,
  569048917383501,566387111437155,563706610383494,561007380015382,558289383581458,555552581711925,
  552796932340802,550022390624443,547228908856139,544416436376579,541584919479968,538734301315541,
  535864521784239,532975517430266,530067221327243,527139562958655,524192468092251,521225858648063,
  518239652559656,515233763628208,512208101368994,509162570849816,506097072520871,503011502035540,
  499905750061522,496779702081696,493633238184061,490466232840038,487278554670368,484070066197788,
  480840623585589,477590076361097,474318267123044,471025031231696,467710196480526,464373582748113,
  461015001628835,457634256040798,454231139809320,450805437224118,447356922568202,443885359616288,
  440390501100342,436872088139646,433329849632527,429763501606626,426172746524257,422557272539102,
  418916752700070]
private def phbn_r384_2_p5 : List ℕ := [415250844097763,411559186948485,407841403610237,
  404097097524505,400325852077026,396527229369921,392700768896767,388845986111198,384962370878550,
  381049385798824,377106464387823,373133009101742,369128389188618,365091938347986,361022952177633,
  356920685383587,352784348726263,348613105671948,344406068714514,340162295327194,335880783498390,
  331560466798566,327200208917189,322798797599086,318354937898232,313867244653505,309334234074760,
  304754314308277,300125774827266,295446774464895,290715327872910,285929290146902,281086339307514,
  276183956262908,271219401798110,266189690036997,261091557696627,255921428293364,250675370254838,
  245349047626276,239937661713396,234435881547875,228837760454100,223136635178231,217325002926007,
  211394370115767,205335064494198,199135999186454,192784372791756,186265283039059,179561221546672,
  172651401785397,165510847752117,158109130449301,150408570415738,142361602215822,133906768375981,
  124962357698026,115415738752232,105104189451875,93777112345717,81011255533014,65978656415185,
  46534802357693]
private def phbn_r384_2 : List ℕ := pCat phbn_r384_2_p0 (pCat phbn_r384_2_p1 (pCat phbn_r384_2_p2
  (pCat phbn_r384_2_p3 (pCat phbn_r384_2_p4 phbn_r384_2_p5))))
private def phbv_r384_2 : List ℤ := uOh phbn_r384_2
private def pvn_r384_2_0_p0 : List ℕ := [2003268153028397,2001251503262617,1998004357017936,
  1998547853272577,2001479258768380,2001541974148346,1998858478160921,1998414592625327,
  2000886902086519,2001603911675663,1999318818703845,1998392687374396,2000507766941312,
  2001600828005643,1999642862664714,1998412552212494,2000223214143060,2001568939511351,
  1999898171689599,1998453662881352,1999989974695648,2001520202701174,2000114587624027,
  1998509223274435,1999786434500047,2001458068866457,2000308270969987,1998578084697593,
  1999600291945414,2001382016339693,2000488627256547,1998662037661366,1999424441011478,
  2001289252857507,2000660832502720,1998764687721482,1999255415630969,2001175504272108,
  2000826759138933,1998890853039981,1999092895945836,2001035530377136,2000985159265329,
  1999046062293493,1998939755112977,2000863671708127,2001131446266096,1999235912267053,
  1998802400954757,2000654634668476,2001257275944199,1999465094938979,1998691222352064,
  2000404695455634,2001350130770443,1999735922364798,1998620903463594,2000113480864066,
  2001393194557404,2000046215622097,1998610253181369,1999786418136175,2001365947650390,
  2000386531810211]
private def pvn_r384_2_0_p1 : List ℕ := [1998681034092365,1999437780852902,2001246085643642,
  2000736942836243,1998855108998069,1999093925893588,2001013499565990,2001064020290171,
  1999149154361833,1998795755248984,2000657010469249,2001319365793284,1999566410071860,
  1998598639745812,2000184081152630,2001441898520513,2000085741792938,1998567164251559,
  1999632492871660,2001366877535555,2000650038865996,1998761574596873,1999080660279813,
  2001044586359374,2001158851698827,1999213699989157,1998649910591890,2000469495546015,
  2001473736045394,1999893859480221,1998488731463546,1999714987580343,2001447128966559,
  2000678228084525,1998728622324232,1998958574122516,2000982645339772,2001337941091032,
  1999408950596169,1998470352986921,2000120567153759,2001581538484626,2000389808710993,
  1998532363796398,1999113080682632,2001177715131064,2001307074898490,1999276092700431,
  1998416947996873,2000145739473277,2001654545546509,2000488242729512,1998518639984137,
  1998915740533957,2001057515353456,2001534140421999,1999576815010080,1998266188708901,
  1999670299230905,2001608079769555,2001062754701661,1998862317825653,1998389010363359,
  2000381565491370]
private def pvn_r384_2_0_p2 : List ℕ := [2001818069757592,2000514915374254,1998417140360409,
  1998664646255083,2000906703650343,2001837053993674,2000075354569764,1998177400526505,
  1998900926598703,2001222866652159,2001826545875658,1999837641926775,1998046552385218,
  1998969511191891,2001344150576817,2001899326771784,1999856901901706,1997973774266554,
  1998794166218651,2001244573700771,2002086977223640,2000197497581444,1998014435752629,
  1998356203710840,1999190059989191,1997714456213238,1999079041583408,2001616813762945,
  2002219193612979,2000133356708633,1997840294562566,1998064226548253,2000566342984254,
  2002460398920569,2001558656677425,1998836386700364,1997287815747106,1998582133582279,
  2001254489498699,2002306623828255,2000365381376390,1997027672185615,1995093187411609,
  1995620730427559,1996788549037123,1995569407052284,1990453167342777,1982593886642627,
  1974424921986865,1967169418117465,1959545553802952,1948731559386597,1932636540365488,
  1911526299926767,1887769260901088,1864083371297082,1841776419431309,1820297355376254,
  1798284869643842,1775194301746857,1752289715882330,1732369264592002,1718500249723391,
  1712621470426319]
private def pvn_r384_2_0_p3 : List ℕ := [1714821578670299,1723583122717959,1736701506281936,
  1752291868086146,1769380281445024,1787898317730068,1808231544369926,1830643907510651,
  1854873415180523,1880041099599713,1904843751168248,1927892851656902,1948043049557541,
  1964601552209273,1977382818113608,1986634204940918,1992889571519988,1996809468440113,
  1999049468152211,2000175447180022,2000625702110868,2000708749953131,2000622279004090,
  2000480480580786,2000341038854935,2000227234758474,2000143800382809,2000087054030853,
  2000050655625822,2000028425187722,2000015417994588,2000008097053615,2000004122096993,
  2000002035920278,2000000976088700,2000000454398465,2000000205424243,2000000090179794,
  2000000038434476,2000000015897933,2000000006379233,2000000002481718,2000000000935377,
  2000000000341278,2000000000120413,2000000000041032,2000000000013480,2000000000004255,
  2000000000001283,2000000000000365,2000000000000095,2000000000000020,2000000000000002]
private def pvn_r384_2_0 : List ℕ := pCat pvn_r384_2_0_p0 (pCat pvn_r384_2_0_p1 (pCat
  pvn_r384_2_0_p2 pvn_r384_2_0_p3))
private def pvn_r384_2_1_p0 : List ℕ := [2000472416700142,2001343739518151,2002341493809031,
  2002670690196547,2001654229091673,1999624618572884,1998063393113402,1998377204478757,
  2000290508347060,2001796762957798,2001215579239026,1999230581195451,1998253967067227,
  1999501884357887,2001355122184296,2001368694169566,1999537152106552,1998383321326105,
  1999510471880000,2001308755294952,2001194745385737,1999345933928684,1998488261594672,
  1999889078876432,2001436703874394,2000790199570960,1998946063889605,1998743279646313,
  2000488436663833,2001454750993778,2000130442314473,1998612072886140,1999307644313242,
  2001101586818170,2001117887322040,1999335231756478,1998638130837937,2000154745996443,
  2001411004766280,2000354725227106,1998721751687853,1999198669513195,2000995775504278,
  2001138701286402,1999392203359030,1998661834868916,2000163980782639,2001388434805933,
  2000286098956546,1998706127114400,1999302663751502,2001071861407330,2001032272847752,
  1999250308568718,1998736825401813,2000361281076752,2001373129715711,2000056057915903,
  1998643689835155,1999535346430194,2001217532661230,2000829204957116,1999028756971525,
  1998880857551459]
private def pvn_r384_2_1_p1 : List ℕ := [2000640032536556,2001310568080487,1999747218440158,
  1998612262222727,1999842516953840,2001344051656555,2000555933650397,1998817479722332,
  1999091595595814,2000915676511400,2001183875422099,1999435092420073,1998643130627111,
  2000159192400114,2001409634043523,2000266751964017,1998666033446055,1999325117737623,
  2001132519849532,2001026727125176,1999180575689184,1998713352077077,2000420062081362,
  2001425278577892,2000030145126887,1998577105705475,1999511973442947,2001272393982350,
  2000906046349530,1999018473202053,1998763312844218,2000573962866192,2001437599732650,
  1999911182237820,1998522879345258,1999578307041098,2001339586672073,2000896652888501,
  1998970284426675,1998727143037201,2000575214275248,2001492887115701,1999973241335876,
  1998485875533458,1999454614303728,2001317565440895,2001058523733566,1999085056678712,
  1998571626599372,2000352427584552,2001582768770534,2000290800290901,1998523462061548,
  1999089608377871,2001104998342859,2001391519753890,1999487146804538,1998370547225319,
  1999795039026918,2001553441650379,2000912967158401,1998851326545136,1998541898621111,
  2000473362890300]
private def pvn_r384_2_1_p2 : List ℕ := [2001699123344163,2000342530579658,1998458137571966,
  1998863425371454,2001048700030916,2001555829820681,1999973474573524,1998051774140867,
  1999468597348623,2001187616421644,2001542387492291,1999606003267024,1997891304705567,
  1999710347843460,2001668981477734,2001077052345676,1999463898546445,1998291019418983,
  1999208069286629,2001779906138357,2001893080957260,1998839101230775,1997581800780610,
  2000109665561960,2002171531450611,2000848138436361,1998730898902102,1998819701325237,
  2000217121842660,2000697780565756,2000252541469931,2000136590086876,2000299351818174,
  1999743413018529,1998739004030240,1998910504295206,2000811325765138,2002585145762603,
  2001926161798571,1999016855752108,1996653464366845,1997201328727628,1999920888609347,
  2001794705152462,2000893475642690,1998449987360006,1997381669901326,1999018724037213,
  2001675565380730,2002532761060823,2000680681633311,1998058244134874,1997392187038676,
  1999385007015160,2002039976382172,2002702709058064,2000678383293780,1997852789575667,
  1996820404459194,1998406088443267,2000900859345788,2001604576316310,1999156636774119,
  1994556679491682]
private def pvn_r384_2_1_p3 : List ℕ := [1990074198950605,1987102248988016,1984802620913348,
  1980590475929321,1971954385354724,1958124090645306,1940368046211090,1920850137180542,
  1901026993272386,1880778113915008,1858809828849623,1833944309214770,1806364623769862,
  1778022648858299,1752024444142866,1731428759744025,1718157403303961,1712542113450479,
  1713610858136354,1719829760607619,1729859305510412,1742979088367414,1759072427062275,
  1778289447806888,1800621337496080,1825599394854428,1852227164099093,1879132839432348,
  1904847113747437,1928089318531557,1947971668235473,1964081613498987,1976450087041374,
  1985443316759222,1991624452575173,1995623629223029,1998039696436960,1999381192540508,
  2000042703954327,2000306877692231,2000361198076801,2000320425248907,2000248560536843,
  2000177103196214,2000118558391163,2000075496275885,2000046077692693,2000027089017110,
  2000015393629328,2000008476713120,2000004531788488,2000002355545392,2000001191727872,
  2000000587361988,2000000282212726,2000000132258959,2000000060483456,2000000026999480,
  2000000011767716,2000000005008747,2000000002082208,2000000000845505,2000000000335368,
  2000000000129935]
private def pvn_r384_2_1_p4 : List ℕ := [2000000000049169,2000000000018168,2000000000006551,
  2000000000002302,2000000000000787,2000000000000259,2000000000000080,2000000000000021,
  2000000000000004]
private def pvn_r384_2_1 : List ℕ := pCat pvn_r384_2_1_p0 (pCat pvn_r384_2_1_p1 (pCat
  pvn_r384_2_1_p2 (pCat pvn_r384_2_1_p3 pvn_r384_2_1_p4)))
private def pvn_r384_2_2_p0 : List ℕ := [2000003188316159,2000017530999181,2000065290531472,
  2000189228899661,2000449742421053,2000897328449077,2001514604548109,2002150572434311,
  2002507109665364,2002245586194631,2001217809075521,1999697327534895,1998390327374266,
  1998079243263373,1999036424341406,2000653565893721,2001729028879229,2001374294419471,
  1999851294975848,1998492925679550,1998566680482302,2000025624665947,2001434447696900,
  2001344579508668,1999834328926396,1998524571189083,1998867374479654,2000487922348014,
  2001526722667333,2000760611393896,1999093722436524,1998542616773605,1999790948439883,
  2001289521347686,2001145460799582,1999536450522518,1998539074945646,1999460284845508,
  2001089229780427,2001254400044231,1999728615450117,1998579622097022,1999382670947665,
  2001034715643183,2001239877771391,1999706504487528,1998592866611973,1999481466867122,
  2001108335391389,2001137351236008,1999522101665002,1998605206041660,1999727897499036,
  2001247973181573,2000924803467248,1999231880087242,1998683945616859,2000102858643339,
  2001366362303670,2000571970064371,1998913683378675,1998902725943972,2000560775932730,
  2001363451295871]
private def pvn_r384_2_2_p1 : List ℕ := [2000079889430313,1998673087469749,1999307154457145,
  2001010610331424,2001152886381597,1999508293903850,1998625381304002,1999881028089802,
  2001324282458940,2000700688307843,1998979029555681,1998854688060229,2000528709329115,
  2001375164292474,2000058044259722,1998645923902914,1999367570175134,2001090818359139,
  2001093650674818,1999364773989567,1998636839330798,2000068250648048,2001396462207653,
  2000512178971197,1998810829028063,1998992747308011,2000776823134905,2001333009954491,
  1999771297337871,1998566453082793,1999636688740420,2001289917004803,2000899283192093,
  1999076507588527,1998712862961196,2000393247303383,2001457704920484,2000212858452421,
  1998623219646335,1999208728080114,2001052063998973,2001239500962130,1999466408547936,
  1998525207207880,1999911301005332,2001439631534787,2000721769756828,1998835121139066,
  1998818070628319,2000572847308903,2001576168190018,1999918043008515,1998645449342544,
  1999149749191077,2001339758543479,2001138777000925,1999376889289498,1998535902606518,
  1999788222808084,2001686594006962,2000683594684457,1998781845862204,1998825459951423,
  2000371853201557]
private def pvn_r384_2_2_p2 : List ℕ := [2001674198349872,2000336199811754,1998277040189490,
  1999152977311270,2001133557589696,2001273640044714,1999843344603183,1998447165392547,
  1999180450144771,2001494295939898,2001503947271864,1999006281899949,1998260383622409,
  2000145633600816,2001472006098657,2000787908709899,1999256685950882,1998514472424542,
  1999709068897431,2001687640818889,2001366678320929,1998706013113968,1997833334838084,
  2000413311959740,2002422472039175,2000654980741786,1997970470947206,1998483847259933,
  2001123105597191,2001836168528157,1999936612482584,1998492255045898,1999302220040175,
  2000745788718586,2000844590201798,1999973385832797,1999575580980678,1999829610488226,
  1999913653947781,1999745054483270,2000041676692757,2000768294926964,2000782181862548,
  1999544388202630,1998356562281433,1998970944690083,2001142709179566,2002476085922146,
  2001141048796298,1998257683747524,1996899699320741,1998683045875049,2001865466294504,
  2003194053910514,2001429484977449,1998600746533620,1997674351054934,1999323878111742,
  2001349466127251,2001242147718874,1998966849836066,1996958286740567,1997452034787289,
  2000085411891883]
private def pvn_r384_2_2_p3 : List ℕ := [2002276393201026,2001891061898485,1999394172988892,
  1997338427453926,1997805770551537,2000389635388789,2002639291969739,2002429220173825,
  1999940635540120,1997445171305191,1997199469397359,1999432130530958,2002185434196395,
  2003038761334057,2001133619473854,1997786859673728,1995272401013229,1994860820361300,
  1995699929379974,1995331651649873,1991333870015609,1982799478786886,1970620290877018,
  1956505165321255,1941551316943559,1925402036434221,1906519706074000,1883321989302978,
  1855414561301354,1824181055380564,1792449960979317,1763502709045313,1739992664738926,
  1723291645896402,1713473124861510,1709795163230764,1711344643806394,1717511204386697,
  1728118679377942,1743239733922045,1762855311272954,1786551018135130,1813383731648606,
  1841953422884552,1870628663270784,1897829943873992,1922276886921108,1943138792233962,
  1960071288434973,1973157522125700,1982791518826208,1989543903613063,1994041262112140,
  1996876782019495,1998556936102514,1999479912157202,1999936997285100,2000127378597598,
  2000178395453350,2000165786349649,2000130933944404,2000094011990672,2000063141718190,
  2000040261985329]
private def pvn_r384_2_2_p4 : List ℕ := [2000024588333856,2000014463497910,2000008226447676,
  2000004536882583,2000002431154334,2000001267858786,2000000644283809,2000000319350066,
  2000000154523145,2000000073037635,2000000033741671,2000000015242399,2000000006735569,
  2000000002912527,2000000001232701,2000000000510783,2000000000207243,2000000000082343,
  2000000000032038,2000000000012207,2000000000004551,2000000000001658,2000000000000587,
  2000000000000199,2000000000000064,2000000000000018,2000000000000004]
private def pvn_r384_2_2 : List ℕ := pCat pvn_r384_2_2_p0 (pCat pvn_r384_2_2_p1 (pCat
  pvn_r384_2_2_p2 (pCat pvn_r384_2_2_p3 pvn_r384_2_2_p4)))
private def pvn_r384_2_3_p0 : List ℕ := [2000000001526616,2000000012715422,2000000073108533,
  2000000334643662,2000001291661287,2000004335001803,2000012887432962,2000034344226664,
  2000082680376512,2000180660564814,2000359114456879,2000649411724310,2001065738658009,
  2001578155020161,2002086473719023,2002415521257138,2002355663635042,2001757785958712,
  2000655517490295,1999344055119477,1998329265159755,1998109066110522,1998862530135437,
  2000238613511265,2001449503337959,2001712410071508,2000807951960905,1999337458017798,
  1998381914349231,1998702408482047,2000073196536761,2001367827226302,2001460767011558,
  2000244788916002,1998814430985753,1998516467714534,1999656842633846,2001128189240957,
  2001447974649681,2000271865155034,1998817652186527,1998637359387244,1999940574508745,
  2001302329703942,2001195816410090,1999728839288244,1998581383216725,1999096634471215,
  2000678523403497,2001442326737861,2000457691628880,1998916330768576,1998718897528427,
  2000120818952854,2001366974882601,2000872815565400,1999260823205184,1998607275891122,
  1999769134283624,2001232268984232,2001064276493339,1999479546164228,1998593864707142,
  1999605622477731]
private def pvn_r384_2_3_p1 : List ℕ := [2001152063905792,2001124896182981,1999553077124523,
  1998598453842409,1999589101613946,2001153212791711,2001101292460424,1999498228257985,
  1998603950456639,1999692621132338,2001220964194865,2001001918238622,1999341741601070,
  1998629338809377,1999901255490272,2001318847192995,2000815903095468,1999118514414818,
  1998710827802445,2000199033453711,2001397105424666,2000531434501906,1998875586842278,
  1998886259386929,2000557163364304,2001399235398475,2000154302435941,1998666526533963,
  1999190473014801,2000909379356045,2001305800150512,1999665679760691,1998627060507067,
  1999514800281090,2001341529165220,2000887392223000,1999377838488774,1998498563496458,
  2000181827812391,2001393895976156,2000561721279708,1998945312464897,1998720570297685,
  2000724793407035,2001392075979460,2000037665780723,1998704863282751,1999107410674400,
  2001143013503722,2001298712560074,1999400620047158,1998650011767299,1999703815296372,
  2001300929821572,2001074022503481,1998930978761550,1998577091496189,2000473268061667,
  2001394014086285,2000403075588574,1998847854208705,1998767915621035,2000762244452720,
  2001693671051440]
private def pvn_r384_2_3_p2 : List ℕ := [1999785430467136,1998349393051630,1999547551538038,
  2001155729521171,2001098456199779,1999625111678507,1998471098438454,1999514841844578,
  2001586281997694,2001218563485790,1998777342003609,1998352404415388,2000524579221951,
  2001652146174129,2000309692691668,1998797957553349,1998972592837642,2000379316692865,
  2001395619330010,2000625055415680,1998726339203565,1998451344577011,2000664275866496,
  2002126014222470,2000273941440548,1997828447410898,1998737097071815,2001650915670573,
  2001987218146688,1999288169248548,1997797442560671,1999653045518181,2001835104723667,
  2001171672743970,1998970210628776,1998509040496228,2000112871823908,2001244171139400,
  2000538449254501,1999365200892216,1999317247409528,2000054249928782,2000372430158616,
  2000129512702913,2000028982411439,2000162325821405,1999949199314479,1999426759143194,
  1999498692025417,2000483086001602,2001221995432863,2000454698210272,1998774456710552,
  1998269827689764,1999918872776305,2002033272387441,2002025128372845,1999576738939762,
  1997298749191335,1997853472389900,2000825595908340,2003053403855293,2002121495729026,
  1999037908050656]
private def pvn_r384_2_3_p3 : List ℕ := [1997079421080993,1998176657262794,2000915170518981,
  2002270904947107,2000987184591852,1998816716315973,1998395576233474,2000250695266852,
  2002246234082208,2001972466351008,1999399998936229,1996956660046872,1997013842362920,
  1999460759630687,2001842523394944,2001838246575194,1999534219177740,1997275032225701,
  1997340730496851,1999765288745859,2002346551259253,2002735398456666,2000588235201834,
  1997834892898023,1996919548118405,1998661081982134,2001595319835569,2003270890497564,
  2002304187669643,1999465345468060,1996980553405000,1996708428596679,1998661985518480,
  2000954624726652,2001091957290847,1997562556190514,1990577456655749,1981527787539007,
  1971658988871949,1960937789116330,1947863160900536,1930295458635474,1906744698147974,
  1877349135330942,1844041449214441,1809903938039221,1778130245219442,1751131579549773,
  1730149069988458,1715416948308976,1706654880649527,1703570106417068,1706125875874816,
  1714502154354407,1728835522110157,1748907691597161,1773940945558193,1802583972631674,
  1833081082454775,1863551737884774,1892283979857894,1917960888741508,1939776816489638,
  1957440525694155]
private def pvn_r384_2_3_p4 : List ℕ := [1971091852720796,1981171671176487,1988283462090814,
  1993074246538655,1996149145541930,1998022001906764,1999096639254667,1999669748159490,
  1999946146106760,2000058885974068,2000089139963724,2000083107988037,2000064963675769,
  2000045959379013,2000030359031020,2000019024525960,2000011414991805,2000006596902819,
  2000003686846808,2000001998346409,2000001052728311,2000000539887990,2000000269893251,
  2000000131652584,2000000062716330,2000000029197589,2000000013291670,2000000005919567,
  2000000002580218,2000000001101108,2000000000460190,2000000000188401,2000000000075568,
  2000000000029696,2000000000011432,2000000000004309,2000000000001586,2000000000000569,
  2000000000000196,2000000000000064,2000000000000018,2000000000000003]
private def pvn_r384_2_3 : List ℕ := pCat pvn_r384_2_3_p0 (pCat pvn_r384_2_3_p1 (pCat
  pvn_r384_2_3_p2 (pCat pvn_r384_2_3_p3 pvn_r384_2_3_p4)))
private def pvn_r384_2_4_p0 : List ℕ := [2000000000000065,2000000000000745,2000000000005985,
  2000000000038567,2000000000211257,2000000001015251,2000000004365204,2000000017019130,
  2000000060746724,2000000199904399,2000000609723083,2000001730556114,2000004584301588,
  2000011358612310,2000026360769493,2000057345277175,2000116945514736,2000223435123254,
  2000399383025292,2000666283077332,2001033599475525,2001482687923597,2001950118714535,
  2002320088164439,2002438843626622,2002160749465192,2001422122126754,2000316878614213,
  1999127844317204,1998267020936990,1998112342308186,1998794064847705,2000048168671183,
  2001263689085300,2001766760282537,2001226284638548,1999930062177120,1998691004884659,
  1998354745600771,1999190015834390,2000616659675752,2001561254899770,2001265363857245,
  1999940188612073,1998673575757774,1998557593438222,1999717162523289,2001126480246116,
  2001485555286787,2000437767690639,1998972289556578,1998524257523203,1999556576438749,
  2001036924655922,2001437353637086,2000323334076804,1998867342095207,1998643431631460,
  1999910871474970,2001274318825957,2001197891889044,1999754812197841,1998597565849444,
  1999079068083393]
private def pvn_r384_2_4_p1 : List ℕ := [2000646013904709,2001440986318950,2000501112640931,
  1998953574984604,1998690032609447,2000046180833102,2001344177447401,2000951714432878,
  1999354853018997,1998579531565939,1999633835609449,2001155263637931,2001184292395747,
  1999638740416116,1998604242528638,1999366404305162,2001059311463595,2001210429155059,
  1999893223993855,1998505120900011,1999413268951934,2000836149823225,2001405854676709,
  1999769466854488,1998636098793142,1999332427603903,2000900964447359,2001391511756883,
  1999665740280956,1998649968060647,1999409072019838,2000996281910937,2001332957810215,
  1999509354809865,1998594994170479,1999644467502172,2001088195508064,2001197941042109,
  1999354021473418,1998494873518564,1999978880455754,2001253237121768,2000862682100850,
  1999240018486220,1998513089597797,2000199053646693,2001554746181290,2000440479902596,
  1998909876559916,1998903722619170,2000372835704491,2001539970366070,2000327602075175,
  1998464043065662,1999125257736434,2001028263958853,2001219997626404,1999819413665874,
  1998673751230443,1999279474020041,2001154185819018,2001397208798370,1999297168742731,
  1998330605599161]
private def pvn_r384_2_4_p2 : List ℕ := [2000048940121292,2001484738318532,2000653444468329,
  1999092083618842,1998784865980743,2000090891380197,2001473374395529,2000764723728067,
  1998653696293724,1998550056711756,2000861698656770,2001792738222093,1999847243358801,
  1998301666304721,1999423538023363,2001176306424320,2001106186336232,1999654510282050,
  1998737480909894,1999411706012236,2000969584352095,2001379866945280,1999722267802221,
  1998191749785427,1999358021294617,2001740418001704,2001538968222352,1998823284787068,
  1997847799894394,2000261577733465,2002289852710797,2000749124067883,1998104062504989,
  1998439437558352,2001079783242220,2001933549843699,1999908190857870,1998228312275859,
  1999244489621937,2001166904646767,2001201892122445,1999623618895905,1998850849350469,
  1999724814077170,2000716643597458,2000541885404389,1999799572628780,1999608641250367,
  1999928007240535,2000048856220476,1999942748739561,2000111137320695,2000428578916463,
  2000182998876859,1999396632523562,1999172540198808,2000155978051186,2001272636534009,
  2000893763209884,1999152183457547,1998154745694655,1999411532714120,2001669700850686,
  2002168696846632]
private def pvn_r384_2_4_p3 : List ℕ := [2000034309135171,1997595435447100,1997776464685014,
  2000572670869547,2002890924138624,2002066315540590,1998955046566359,1996980534049601,
  1998258796299364,2001281107752624,2002726700089588,2001203006273686,1998643485597375,
  1997938805267557,1999660398915667,2001578212894987,2001351356263462,1999224992964341,
  1997721382671149,1998768871245452,2001505531566148,2003143960576030,2001912756243632,
  1998919377661175,1997016342648957,1997914315601708,2000517162940817,2002094959677015,
  2001021479595425,1998336480552016,1996676198659930,1997711522415971,2000578349849638,
  2002717039705426,2002239638893858,1999612076717819,1997187372842855,1997108653229648,
  1999476549861419,2002320466616543,2003294306285379,2001604856190119,1998606430877219,
  1996675573355842,1997346786934926,2000166361428745,2003050699080502,2003757395815558,
  2001315549427614,1996407542124077,1990525340401804,1984577667130462,1977926133489785,
  1968461358448295,1953627269375032,1931748894358426,1902921999525636,1869058681952710,
  1833182352490176,1798422974395193,1767217902013359,1741013188178735,1720452709304756,
  1705814520239700]
private def pvn_r384_2_4_p4 : List ℕ := [1697397681514047,1695662345442411,1701094438446160,
  1713907997092645,1733755768822381,1759588280322440,1789718732272950,1822063312546799,
  1854469596795886,1885032716250987,1912322440569528,1935485835351848,1954230866449213,
  1968723859214660,1979444159758914,1987035455442546,1992181052723000,1995516169514838,
  1997578362545879,1998789600086735,1999460268699202,1999805488053222,1999966067113043,
  2000029017676126,2000044917783621,2000041191028000,2000031465250425,2000021706412411,
  2000013967996588,2000008522587862,2000004977514965,2000002799413544,2000001522313282,
  2000000802756987,2000000411378010,2000000205205269,2000000099766652,2000000047323695,
  2000000021919547,2000000009920729,2000000004389991,2000000001900205,2000000000804875,
  2000000000333729,2000000000135492,2000000000053868,2000000000020974,2000000000007995,
  2000000000002979,2000000000001083,2000000000000380,2000000000000126,2000000000000037,
  2000000000000008,2000000000000001]
private def pvn_r384_2_4 : List ℕ := pCat pvn_r384_2_4_p0 (pCat pvn_r384_2_4_p1 (pCat
  pvn_r384_2_4_p2 (pCat pvn_r384_2_4_p3 pvn_r384_2_4_p4)))
private def pvn_r384_2_5_p0 : List ℕ := [2000000000000003,2000000000000005,1999999999999999,
  2000000000000005,2000000000000003,2000000000000015,2000000000000034,2000000000000163,
  2000000000000816,2000000000003805,2000000000016696,2000000000068718,2000000000265673,
  2000000000967670,2000000003328655,2000000010836090,2000000033440066,2000000097958961,
  2000000272689540,2000000721920267,2000001818641957,2000004360913091,2000009954246899,
  2000021625055133,2000044690981409,2000087792149485,2000163743196712,2000289497674609,
  2000484120895985,2000763502277628,2001131026848245,2001565016693804,2002006572451179,
  2002354795958773,2002478373398765,2002250343466325,2001604232457631,2000595146311393,
  1999434541497063,1998462932269400,1998041772899162,1998386661584054,1999414162928429,
  2000702009048955,2001633162821333,2001699517274418,2000820468051094,1999467103846790,
  1998450780399012,1998436945464898,1999470041301116,2000865638283666,2001628906873027,
  2001173311229401,1999817520427833,1998612858346920,1998544483189937,1999692514324234,
  2001101268311965,2001533995653184,2000595747500314,1999102529378883,1998474574730239,
  1999268292462906]
private def pvn_r384_2_5_p1 : List ℕ := [2000823421941177,2001480325293632,2000764794086537,
  1999111531536603,1998589808041340,1999296800343774,2001044749836979,2001351420294831,
  2000472191060443,1998833895431850,1998644770864551,1999980210382035,2001218238478557,
  2001265038416264,1999568797253889,1998602964469952,1999203612442693,2000707105583645,
  2001544502367541,2000240257261150,1998830835181108,1998834886676112,2000170289480759,
  2001526642137320,2000731193998351,1999057989516203,1998725366487248,1999813047010307,
  2001334978245159,2001091281324139,1999230952098081,1998623809727719,1999737791979168,
  2001114612134503,2001217251738721,1999491629158725,1998429435539286,1999722681801990,
  2001197023862019,2001034246357696,1999628290054107,1998524209761528,1999501937180327,
  2001371611368773,2001108637363751,1999285420616838,1998672029699867,1999752982479338,
  2001153845306298,2001133341930130,1999337051847172,1998386583653692,1999988690644958,
  2001533807909436,2000692404290452,1999050343225670,1998807413187511,2000074014567111,
  2001364370089797,2000811839561384,1998849710315172,1998551765998627,2000606502833839,
  2001663836231817]
private def pvn_r384_2_5_p2 : List ℕ := [2000111445027347,1998589908314044,1999204498275190,
  2000762888645607,2001247691935496,2000104069764391,1998661963304523,1999033779989902,
  2001041123674913,2001604646080038,1999557621700850,1998140234476539,1999713884428628,
  2001670286337847,2000932733080149,1998911523945894,1998696321141425,2000267868777546,
  2001275919613057,2000574241139380,1999167722653879,1998788836315949,2000069504813546,
  2001465270772143,2000823500339632,1998743922563404,1998387041309573,2000625088111763,
  2002081927120299,2000270572144744,1997909068849787,1998803653096836,2001620868707688,
  2001902442635755,1999215393233181,1997805303368484,1999800837652719,2001994303168662,
  2001066126287628,1998633025187725,1998413972919360,2000508401265759,2001638485974705,
  2000315304876450,1998741583720651,1999141749906410,2000629471479408,2000987950379043,
  1999981605093075,1999255902104112,1999665268486067,2000329658222678,2000331155453681,
  1999978783987836,1999922380507313,2000021369189999,1999849225582864,1999682134827746,
  2000063425308350,2000640755255937,2000430197181933,1999409450455885,1998930735293941,
  1999924990115612]
private def pvn_r384_2_5_p3 : List ℕ := [2001307963478138,2001145372024988,1999333519583461,
  1998089698738124,1999216049232551,2001559771136362,2002192162006309,2000089327024195,
  1997647605783677,1997897164175945,2000729684038212,2002862266185455,2001717957212610,
  1998548291549887,1996999155393733,1998833538777625,2001911066428870,2002750080699865,
  2000548439768527,1997955847227964,1997866114395298,2000125166131001,2001929554042453,
  2001233637175050,1999073292506667,1998191053011345,1999727910718027,2001876895681890,
  2001992374305235,1999671438229542,1997301767292720,1997486498031367,2000209297854400,
  2002811084695592,2002754337622026,2000212643534799,1997815921670681,1997915271510012,
  2000232569868457,2002232036852460,2001724416239121,1999043172622349,1996690985442703,
  1996902829057044,1999528015827333,2002201436812833,2002545687653768,2000310565408311,
  1997539760602361,1996718127485873,1998612221422177,2001662737255248,2003350092313743,
  2002290973712598,1999323896225612,1996786401414250,1996668367041613,1999129635490941,
  2002459743081839,2004386661350412,2003666329471275,2000784761902746,1997337183025163,
  1994597350970107]
private def pvn_r384_2_5_p4 : List ℕ := [1992286137817454,1988330480668753,1979717073495188,
  1963888323521925,1939890928040815,1908734027935960,1872913087866522,1835480935157042,
  1799185101175196,1766032504519632,1737339960451074,1714071688769030,1697171586147699,
  1687674120217753,1686543680439461,1694345969490527,1710927312333393,1735255334118076,
  1765489863472054,1799256616387903,1834029537329027,1867508423505992,1897901112327753,
  1924064829189878,1945508022028456,1962287241480492,1974847783406201,1983854182909566,
  1990043746014716,1994120206966722,1996690575068795,1998238913422332,1999126496099932,
  1999607424933525,1999850752684217,1999963000096333,2000007668657024,2000020432208283,
  2000020016240016,2000015447647874,2000010573252932,2000006694937934,2000004001085458,
  2000002282162133,2000001250954915,2000000661982905,2000000339274405,2000000168798694,
  2000000081670696,2000000038480053,2000000017674476,2000000007920938,2000000003466043,
  2000000001481737,2000000000619150,2000000000252973,2000000000101094,2000000000039522,
  2000000000015113,2000000000005648,2000000000002057,2000000000000730,2000000000000248,
  2000000000000078]
private def pvn_r384_2_5_p5 : List ℕ := [2000000000000022,2000000000000004]
private def pvn_r384_2_5 : List ℕ := pCat pvn_r384_2_5_p0 (pCat pvn_r384_2_5_p1 (pCat
  pvn_r384_2_5_p2 (pCat pvn_r384_2_5_p3 (pCat pvn_r384_2_5_p4 pvn_r384_2_5_p5))))
private def pvn_r384_2_6_p0 : List ℕ := [2000000000000003,2000000000000005,1999999999999999,
  2000000000000005,2000000000000005,1999999999999998,2000000000000001,2000000000000010,
  2000000000000003,2000000000000009,2000000000000006,2000000000000002,2000000000000015,
  2000000000000017,2000000000000012,2000000000000020,2000000000000063,2000000000000185,
  2000000000000776,2000000000003134,2000000000012093,2000000000044763,2000000000158349,
  2000000000535719,2000000001733933,2000000005372760,2000000015945525,2000000045344459,
  2000000123585835,2000000322873538,2000000808596913,2000001940937771,2000004464570468,
  2000009836556016,2000020748275863,2000041862485176,2000080720742720,2000148537078373,
  2000260463718576,2000434195138965,2000686489868977,2001025212328278,2001440403174600,
  2001889171359444,2002294697043120,2002535613559749,2002494133960307,2002050144668442,
  2001225441934492,2000081626474956,1998981957620838,1998130439458260,1998066473408026,
  1998582991750063,1999913881193441,2000996305802703,2001909262960561,2001479796099050,
  2000587272323867,1999070825574581,1998320998889365,1998571760842279,1999674434432896,
  2001204792501935]
private def pvn_r384_2_6_p1 : List ℕ := [2001592908596622,2001081420888023,1999591291027781,
  1998430171563796,1998688012590013,1999764111965448,2001279786383779,2001565383455366,
  2000408033931844,1999100824693387,1998371871332297,1999323577597494,2000955389576354,
  2001450323798192,2000753412976106,1999173572526887,1998366277150339,1999479382597067,
  2000922216900961,2001427780791749,2000545638318116,1998828049316719,1998543491354560,
  1999974285343536,2001204351887156,2001232513543005,1999860074196529,1998442185707447,
  1999065825478662,2000800495658937,2001374753651584,2000484870953502,1998990588857478,
  1998546546821966,2000111582919583,2001543483865925,2000820625625320,1999234724838531,
  1998670178306727,1999601088195420,2001197724426769,2001328283635096,1999486794726461,
  1998406350683424,1999601775752066,2001123714336690,2001136525813206,1999824200026379,
  1998598560779127,1999175433673753,2001105071753762,2001477292187829,1999614197235543,
  1998446237293441,1999532746227754,2001054846838209,2001136622469837,1999819072713492,
  1998606612690196,1999241800507094,2001168256654189,2001454213524076,1999440148711331,
  1998304754609776]
private def pvn_r384_2_6_p2 : List ℕ := [1999787156789518,2001420138517993,2000890592920052,
  1999277059984640,1998742370519354,1999813359553411,2001203877742187,2001050527879448,
  1999249328227657,1998363622326993,2000037082354470,2001798636778774,2000725281566752,
  1998487627534489,1998685914283395,2000873816728412,2001557350073193,1999929919698451,
  1998621624248978,1999327500234887,2000814311950768,2001147673985652,1999994874481391,
  1998778352524878,1999156838910991,2000866207189901,2001511303226183,1999834841308064,
  1998177343773303,1999292900167429,2001688419664889,2001529613480325,1998868784363496,
  1997909024468393,2000280854333525,2002243894093204,2000657404212812,1998055514874752,
  1998544917352459,2001265580611097,2001920671338521,1999620855644432,1998047798420425,
  1999510494394793,2001567152423392,2001125073998971,1999100868744929,1998613628695056,
  2000158898784188,2001251478116366,2000432242738699,1999173138304337,1999281746970971,
  2000311857259506,2000667713641725,2000076128648224,1999609226147432,1999806270743821,
  2000097294001471,2000045058982963,1999999809097014,2000203516035399,2000195748742590,
  1999706416846318]
private def pvn_r384_2_6_p3 : List ℕ := [1999422007181290,2000020984596633,2000851017701744,
  2000600780033860,1999326044577933,1998738562186994,1999901570266439,2001458009947739,
  2001208865135882,1999200280150013,1997993844286711,1999377486085560,2001783024589218,
  2002081381836470,1999666236683565,1997467160904975,1998344059368608,2001372146243624,
  2002849012596397,2000880150083123,1997791730186768,1997310739723607,2000010543470468,
  2002647686639738,2002133038459999,1999203188490892,1997384301485930,1998691160063806,
  2001351458559322,2002149285283732,2000329277189372,1998322357674415,1998616272883831,
  2000726993934450,2001899743984168,2000551068474801,1998237313832810,1997819945841024,
  2000045423539267,2002566636237698,2002538047751002,1999816797143775,1997174828814110,
  1997322725361238,2000038199915926,2002472097095646,2002201046396579,1999718756523145,
  1997798908764365,1998526727419489,2001147793793652,2002890692049070,2001814601880095,
  1998762211267141,1996526400832360,1997144528194961,1999982309904218,2002379640358301,
  2002145111399764,1999531721536738,1996940605523862,1996734364871829,1999173216004060,
  2002242275125001]
private def pvn_r384_2_6_p4 : List ℕ := [2003406665159888,2001719555985035,1998540169106976,
  1996378397588555,1996905453144365,1999728332650498,2002800015867863,2004029513739028,
  2002808322564795,2000341379535304,1998608728255763,1998737093518135,1999883596468836,
  1999306862610990,1993511401012483,1979746843140138,1957054348310360,1926432668205275,
  1890234218649021,1851263133805617,1812074652701328,1774732837312176,1740967066256353,
  1712463306738675,1691013686020709,1678387189898695,1675968256736704,1684336610532728,
  1702982615404145,1730281228816467,1763735842932766,1800406560462544,1837390235928204,
  1872227262818072,1903155649423489,1929190785205428,1950057532691931,1966028251831545,
  1977725139463324,1985934051666964,1991458450847639,1995023776406496,1997228892507390,
  1998533749194007,1999270240488497,1999664658467970,1999863240275477,1999955649271782,
  1999993995736651,2000006887726273,2000009054008824,2000007505433151,2000005236185576,
  2000003309127986,2000001952550003,2000001092434068,2000000584797201,2000000301246190,
  2000000149910246,2000000072265992,2000000033815366,2000000015383072,2000000006811494,
  2000000002938487]
private def pvn_r384_2_6_p5 : List ℕ := [2000000001235992,2000000000507202,2000000000203153,
  2000000000079446,2000000000030339,2000000000011313,2000000000004114,2000000000001456,
  2000000000000497,2000000000000162,2000000000000049,2000000000000012,2000000000000002]
private def pvn_r384_2_6 : List ℕ := pCat pvn_r384_2_6_p0 (pCat pvn_r384_2_6_p1 (pCat
  pvn_r384_2_6_p2 (pCat pvn_r384_2_6_p3 (pCat pvn_r384_2_6_p4 pvn_r384_2_6_p5))))
private def pvi_r384_2 : List ℤ := bDc bZ (rPad bZ 257 pvn_r384_2_0)
private def pvo_r384_2 : List ℤ := bDc bZ (rPad bZ 385 pvn_r384_2_6)
private def phbn_r384_3_p0 : List ℕ := [91669538423970,129344893271711,158052674353567,
  182085694352663,203110842932364,221985016623243,239218426969921,255144264202465,269994487562388,
  283938365717698,297103969413054,309591019098162,321478993669367,332832477205545,343704813889861,
  354140683124683,364177961153795,373849097067133,383182149709298,392201582445069,400928881568957,
  409383044000960,417580966566940,425537760128400,433267005589316,440780964424719,448090753245533,
  455206489645873,462137414912911,468891997940520,475478023756101,481902669361715,488172569047017,
  494293870910369,500272285995553,506113131192464,511821366844647,517401629842386,522858262848011,
  528195340193251,533416690901518,538525919216817,543526422962433,548421410004093,553213913052116,
  557906803003423,562502800996201,567004489326270,571414321354225,575734630515453,579967638530639,
  584115462902091,588180123770615,592163550198572,596067585936947,599893994727469,603644465184941,
  607320615299854,610923996596889,614456097981031,617918349299618,621312124645640,624638745424999,
  627899483208075]
private def phbn_r384_3_p1 : List ℕ := [631095562383963,634228162633840,637298421238405,
  640307435232813,643256263421331,646145928262731,648977417636483,651751686498855,654469658437238,
  657132227130256,659740257720599,662294588106883,664796030160332,667245370871578,669643373432455,
  671990778257245,674288303947490,676536648204151,678736488690602,680888483849666,682993273677678,
  685051480458298,687063709458630,689030549589993,690952574035518,692830340846592,694664393510042,
  696455261487780,698203460730546,699909494167258,701573852171370,703197013005551,704779443245917,
  706321598186942,707823922228132,709286849243452,710710802934436,712096197167863,713443436298815,
  714752915479885,716025020957249,717260130354292,718458612943411,719620829906603,720747134585385,
  721837872720593,722893382682541,723913995692018,724900036032566,725851821254448,726769662370706,
  727653864045674,728504724776309,729322537066655,730107587595762,730860157379361,731580521925562,
  732268951384860,732925710694671,733551059718677,734145253381164,734708541796595,735241170394618,
  735743380040687]
private def phbn_r384_3_p2 : List ℕ := [736215407152494,736657483812387,737069837875926,
  737452693076746,737806269127878,738130781819656,738426443114367,738693461237751,738932040767493,
  739142382718810,739324684627253,739479140628826,739605941537530,739705274920417,739777325170257,
  739822273575906,739840298390452,739831574897223,739796275473738,739734569653667,739646624186877,
  739532603097627,739392667740975,739226976857467,739035686626153,738818950715998,738576920335738,
  738309744282226,738017568987333,737700538563433,737358794847528,736992477444055,736601723766417,
  736186669077269,735747446527614,735284187194728,734797020118958,734286072339430,733751468928685,
  733193333026293,732611785871459,732006946834650,731378933448288,730727861436505,730053844744016,
  729356995564111,728637424365797,727895239920115,727130549325648,726343458033243,725534069869960,
  724702487062276,723848810258556,722973138550802,722075569495710,721156199135036,720215122015294,
  719252431206798,718268218322056,717262573533535,716235585590814,715187341837110,714117928225227,
  713027429332903]
private def phbn_r384_3_p3 : List ℕ := [711915928377586,710783507230634,709630246430960,
  708456225198118,707261521444848,706046211789075,704810371565378,703554074835934,702277394400930,
  700980401808466,699663167363938,698325760138914,696968247979503,695590697514212,694193174161313,
  692775742135695,691338464455232,689881402946634,688404618250816,686908169827760,685392115960871,
  683856513760848,682301419169036,680726886960278,679132970745265,677519722972364,675887194928935,
  674235436742130,672564497379161,670874424647040,669165265191781,667437064497054,665689866882296,
  663923715500246,662138652333926,660334718193034,658511952709746,656670394333924,654810080327702,
  652931046759457,651033328497129,649116959200897,647181971315177,645228396059942,643256263421331,
  641265602141544,639256439707987,637228802341664,635182714984776,633118201287521,631035283594056,
  628933982927604,626814318974677,624676310068382,622519973170789,620345323854313,618152376282098,
  615941143187341,613711635851545,611463864081642,609197836185949,606913558948920,604611037604633,
  602290275808982]
private def phbn_r384_3_p4 : List ℕ := [599951275610498,597594037419768,595218559977374,
  592824840320307,590412873746780,587982653779373,585534172126445,583067418641727,580582381282025,
  578079046062935,575557397012499,573017416122678,570459083298575,567882376305267,565287270712162,
  562673739834737,560041754673547,557391283850354,554722293541253,552034747406615,549328606517713,
  546603829279840,543860371351743,541098185561180,538317221816389,535517427013251,532698744937914,
  529861116164621,527004477948484,524128764112916,521233904931413,518319827003364,515386453123548,
  512433702144938,509461488834415,506469723720975,503458312935966,500427158044862,497376155870062,
  494305198304137,491214172112928,488102958727833,484971434026597,481819468101831,478646925016460,
  475453662545207,472239531901177,469004377446502,465748036385943,462470338442239,459171105511908,
  455850151300077,452507280932803,449142290545224,445754966843704,442345086640011,438912416355342,
  435456711491861,431977716069147,428475162022737,424948768561674,421398241481652,417823272430035,
  414223538118634]
private def phbn_r384_3_p5 : List ℕ := [410598699479740,406948400760392,403272268549393,
  399569910730962,395840915358253,392084849439254,388301257626691,384489660802679,380649554547700,
  376780407482364,372881659468919,368952719657969,364992964364005,361001734751267,356978334309112,
  352922026093259,348832029706141,344707517985913,340547613369370,336351383889075,332117838759182,
  327845923497595,323534514524111,319182413164714,314788338980939,310350922329921,305868696044735,
  301340086105541,296763401148951,292136820635119,287458381458076,282725962743240,277937268524888,
  273089807933109,268180872440945,263207509623687,258166492757654,253054285427325,247867000106583,
  242600349417290,237249588425968,231809445888283,226274041750505,220636787408665,214890264123921,
  209026073470034,203034651554030,196905035709709,190624567953139,184178512966629,177549558518656,
  170717150955985,163656594087041,156337799816901,148723510815476,140766694532972,132406582017129,
  123562377497905,114122711379734,103926684586466,92726507164069,80103668993976,65239483320876,
  46013462947030]
private def phbn_r384_3 : List ℕ := pCat phbn_r384_3_p0 (pCat phbn_r384_3_p1 (pCat phbn_r384_3_p2
  (pCat phbn_r384_3_p3 (pCat phbn_r384_3_p4 phbn_r384_3_p5))))
private def phbv_r384_3 : List ℤ := uOh phbn_r384_3
private def pvn_r384_3_0_p0 : List ℕ := [1999999999999997,1999999999999995,2000000000000001,
  1999999999999995,1999999999999995,2000000000000002,1999999999999999,1999999999999990,
  1999999999999997,1999999999999991,1999999999999994,1999999999999998,1999999999999985,
  1999999999999983,1999999999999988,1999999999999980,1999999999999937,1999999999999815,
  1999999999999224,1999999999996866,1999999999987907,1999999999955237,1999999999841651,
  1999999999464281,1999999998266067,1999999994627240,1999999984054475,1999999954655541,
  1999999876414165,1999999677126462,1999999191403087,1999998059062229,1999995535429532,
  1999990163443984,1999979251724137,1999958137514824,1999919279257280,1999851462921627,
  1999739536281424,1999565804861035,1999313510131023,1998974787671722,1998559596825400,
  1998110828640556,1997705302956880,1997464386440251,1997505866039693,1997949855331558,
  1998774558065508,1999918373525044,2001018042379162,2001869560541740,2001933526591974,
  2001417008249937,2000086118806559,1999003694197297,1998090737039439,1998520203900950,
  1999412727676133,2000929174425419,2001679001110635,2001428239157721,2000325565567104,
  1998795207498065]
private def pvn_r384_3_0_p1 : List ℕ := [1998407091403378,1998918579111977,2000408708972219,
  2001569828436204,2001311987409987,2000235888034552,1998720213616221,1998434616544634,
  1999591966068156,2000899175306613,2001628128667703,2000676422402506,1999044610423646,
  1998549676201808,1999246587023894,2000826427473113,2001633722849661,2000520617402933,
  1999077783099039,1998572219208251,1999454361681884,2001171950683281,2001456508645440,
  2000025714656464,1998795648112844,1998767486456995,2000139925803471,2001557814292553,
  2000934174521338,1999199504341063,1998625246348416,1999515129046498,2001009411142522,
  2001453453178034,1999888417080417,1998456516134075,1999179374374680,2000765275161469,
  2001329821693273,2000398911804580,1998802275573231,1998671716364904,2000513205273539,
  2001593649316576,2000398224247934,1998876285663310,1998863474186794,2000175799973621,
  2001401439220873,2000824566326247,1998894928246238,1998522707812171,2000385802764457,
  2001553762706559,2000467253772246,1998945153161791,1998863377530163,2000180927286508,
  2001393387309804,2000758199492906,1998831743345811,1998545786475924,2000559851288669,
  2001695245390224]
private def pvn_r384_3_0_p2 : List ℕ := [2000212843210482,2001420138517993,2000890592920052,
  1999277059984640,1998742370519354,1999813359553411,2001203877742187,2001050527879448,
  1999249328227657,1998363622326993,2000037082354470,2001798636778774,2000725281566752,
  1998487627534489,1998685914283395,2000873816728412,2001557350073193,1999929919698451,
  1998621624248978,1999327500234887,2000814311950768,2001147673985652,1999994874481391,
  1998778352524878,1999156838910991,2000866207189901,2001511303226183,1999834841308064,
  1998177343773303,1999292900167429,2001688419664889,2001529613480325,1998868784363496,
  1997909024468393,2000280854333525,2002243894093204,2000657404212812,1998055514874752,
  1998544917352459,2001265580611097,2001920671338521,1999620855644432,1998047798420425,
  1999510494394793,2001567152423392,2001125073998971,1999100868744929,1998613628695056,
  2000158898784188,2001251478116366,2000432242738699,1999173138304337,1999281746970971,
  2000311857259506,2000667713641725,2000076128648224,1999609226147432,1999806270743821,
  2000097294001471,2000045058982963,1999999809097014,2000203516035399,2000195748742590,
  1999706416846318]
private def pvn_r384_3_0_p3 : List ℕ := [1999422007181290,2000020984596633,2000851017701744,
  2000600780033860,1999326044577933,1998738562186994,1999901570266439,2001458009947739,
  2001208865135882,1999200280150013,1997993844286711,1999377486085560,2001783024589218,
  2002081381836470,1999666236683565,1997467160904975,1998344059368608,2001372146243624,
  2002849012596397,2000880150083123,1997791730186768,1997310739723607,2000010543470468,
  2002647686639738,2002133038459999,1999203188490892,1997384301485930,1998691160063806,
  2001351458559322,2002149285283732,2000329277189372,1998322357674415,1998616272883831,
  2000726993934450,2001899743984168,2000551068474801,1998237313832810,1997819945841024,
  2000045423539267,2002566636237698,2002538047751002,1999816797143775,1997174828814110,
  1997322725361238,2000038199915926,2002472097095646,2002201046396579,1999718756523145,
  1997798908764365,1998526727419489,2001147793793652,2002890692049070,2001814601880095,
  1998762211267141,1996526400832360,1997144528194961,1999982309904218,2002379640358301,
  2002145111399764,1999531721536738,1996940605523862,1996734364871829,1999173216004060,
  2002242275125001]
private def pvn_r384_3_0_p4 : List ℕ := [2003406665159888,2001719555985035,1998540169106976,
  1996378397588555,1996905453144365,1999728332650498,2002800015867863,2004029513739028,
  2002808322564795,2000341379535304,1998608728255763,1998737093518135,1999883596468836,
  1999306862610990,1993511401012483,1979746843140138,1957054348310360,1926432668205275,
  1890234218649021,1851263133805617,1812074652701328,1774732837312176,1740967066256353,
  1712463306738675,1691013686020709,1678387189898695,1675968256736704,1684336610532728,
  1702982615404145,1730281228816467,1763735842932766,1800406560462544,1837390235928204,
  1872227262818072,1903155649423489,1929190785205428,1950057532691931,1966028251831545,
  1977725139463324,1985934051666964,1991458450847639,1995023776406496,1997228892507390,
  1998533749194007,1999270240488497,1999664658467970,1999863240275477,1999955649271782,
  1999993995736651,2000006887726273,2000009054008824,2000007505433151,2000005236185576,
  2000003309127986,2000001952550003,2000001092434068,2000000584797201,2000000301246190,
  2000000149910246,2000000072265992,2000000033815366,2000000015383072,2000000006811494,
  2000000002938487]
private def pvn_r384_3_0_p5 : List ℕ := [2000000001235992,2000000000507202,2000000000203153,
  2000000000079446,2000000000030339,2000000000011313,2000000000004114,2000000000001456,
  2000000000000497,2000000000000162,2000000000000049,2000000000000012,2000000000000002]
private def pvn_r384_3_0 : List ℕ := pCat pvn_r384_3_0_p0 (pCat pvn_r384_3_0_p1 (pCat
  pvn_r384_3_0_p2 (pCat pvn_r384_3_0_p3 (pCat pvn_r384_3_0_p4 pvn_r384_3_0_p5))))
private def pvn_r384_3_1_p0 : List ℕ := [1999999999999997,1999999999999995,2000000000000001,
  2000000000000002,2000000000000005,1999999999999990,1999999999999998,2000000000000002,
  1999999999999997,2000000000000001,1999999999999999,2000000000000001,1999999999999987,
  1999999999999985,2000000000000005,2000000000000027,1999999999999853,2000000000000539,
  1999999999998013,2000000000006733,1999999999978261,2000000000066620,1999999999804875,
  2000000000546663,1999999998531563,2000000003786828,1999999990614069,2000000022377069,
  1999999948653691,2000000113435939,1999999758675067,2000000494367422,1999999025000808,
  2000001850412382,1999996622567612,2000005922571428,1999990031610578,2000016069946507,
  1999975211933557,2000036408876122,1999949039051179,2000067047772861,1999916133932319,
  2000095007579716,1999895782204521,2000088689623648,1999912062073347,2000010217456623,
  1999948279985584,1999840636538805,1999885341998055,1999568473215060,1999513077093629,
  1999115788711057,1998708242500658,1998360987488830,1997723731685405,1997506759052693,
  1997309419388175,1997470789579186,1998285507019976,1999164139755682,2000475963500175,
  2001603684892829]
private def pvn_r384_3_1_p1 : List ℕ := [2001989074969160,2001915888253597,2000862286795588,
  1999421635909864,1998490652346276,1998063379994084,1998802664091873,2000326961298709,
  2001382936059134,2001773800851806,2001021558006467,1999362853221735,1998404180596986,
  1998555616228109,1999614818944527,2001217311727574,2001743040824066,2000692674075492,
  1999314838388848,1998419568190624,1998789686632298,2000495224938212,2001627485573281,
  2001089681195944,1999751479877415,1998570887603286,1998653742685326,2000325948135799,
  2001611303693613,2001028283064375,1999569894417668,1998585966252141,1998921686069867,
  2000609136767553,2001700171905231,2000641436974744,1998945476331679,1998627881837553,
  1999698870654628,2001117005532660,2001420647884682,1999876436998015,1998359949139314,
  1999081169998301,2000886094586077,2001439106916711,2000229305571751,1999046891124031,
  1998503909061550,2000442083807924,2001290943874281,2001139014040305,1998683832598849,
  1998435227101262,2000572635248044,2001066626071894,2000759124298290,1999651427770793,
  1998253399258182,1999626364677206,2001920028839526,2000971646332727,1998624183899879,
  1998752297685590]
private def pvn_r384_3_1_p2 : List ℕ := [2000501167832570,2001068521492940,2000242606517193,
  1999494747661990,1999532915164055,1999892874973167,2000017472246295,2000210169294091,
  2000776994251249,2000669089558419,1999084552324424,1997919957270647,1999464532750611,
  2002106248314891,2002177866839811,1999805274934298,1998743587661558,2000325632925856,
  2001718504982035,2000779907831074,1999044297208219,1998870760457327,2000206588913686,
  2001202732855345,2000629308537274,1999164987540395,1998729857976232,2000147096872863,
  2001563423197831,2000692510702655,1998567879255893,1998525019786419,2000904769442695,
  2002007890169439,1999896102915492,1997839905215024,1999215018374524,2001891603104437,
  2001558420497912,1998738582610706,1997956603912616,2000412023492963,2002137939090002,
  2000465797399990,1998165345146369,1998820202386238,2001221344712968,2001583839855545,
  1999542096104686,1998385401916810,1999734177934817,2001307494560216,2000781502925735,
  1999213820971100,1999010069046912,2000226063295128,2000890785175667,2000200305023303,
  1999416711305777,1999618584923673,2000233124312943,2000309525089043,1999988968021964,
  1999910634208036]
private def pvn_r384_3_1_p3 : List ℕ := [2000020204965127,1999901431342508,1999760535164225,
  2000076806639758,2000512199091454,2000231675473906,1999398243904299,1999270129225534,
  2000309333729356,2001146531767517,2000386074880222,1998858566942220,1998759831227402,
  2000499928498643,2001789673041690,2000667586969530,1998431672462616,1998142462551376,
  2000425740277288,2002353750425519,2001235681617600,1998353347361391,1997468384889094,
  1999877679605059,2002568157864675,2002045812921896,1998895050222894,1997088513528706,
  1998912200319926,2002064867058406,2002620406819088,1999977011500423,1997494728592452,
  1998174054751960,2000980171470112,2002353070873249,2000749149609378,1998406357649831,
  1998306698040793,2000397855233068,2001831043514249,2000716882620691,1998533863804430,
  1998200811088029,2000327408374360,2002358712987174,2001671271338539,1998826147343545,
  1997031457534410,1998437484459723,2001616717781385,2003138224548667,2001392867829476,
  1998327752927323,1997225305990754,1999106075628461,2001730372117852,2002165629984999,
  1999994701021701,1997698852801032,1997922027638605,2000624823653778,2003112030203133,
  2002813368151642]
private def pvn_r384_3_1_p4 : List ℕ := [1999893437030403,1997074172318654,1996945577817711,
  1999483569418180,2002148570998118,2002351693327175,1999869771406432,1996987726014051,
  1996358711254550,1998620219831888,2001879785854209,2003408654091309,2001969002294671,
  1998787260822798,1996461039085806,1996823294251671,1999535179581076,2002459051287385,
  2003403861299256,2001832244394625,1999259823967198,1998114384246817,1999905138198823,
  2003932433933522,2007298881100301,2006104611861563,1997044630845577,1978540682206169,
  1950967252395520,1916110314583656,1876360032670948,1834130258163616,1791714764401446,
  1751461222971089,1715965989090421,1688029962598097,1670299179384414,1664713255643483,
  1671993117488990,1691380507419211,1720729224820956,1756910384187336,1796393517424927,
  1835832787348214,1872518358202237,1904619877359630,1931219922546685,1952186698256406,
  1967957901594549,1979304565251418,1987124681219749,1992292411808642,1995567822951427,
  1997558327831413,1998716826887284,1999361133542946,1999702225383160,1999872978234601,
  1999952875495501,1999987046138956,1999999745918985,2000003245682917,2000003324625602,
  2000002461712801]
private def pvn_r384_3_1_p5 : List ℕ := [2000001577778274,2000000925203368,2000000508709877,
  2000000265720901,2000000132892433,2000000063957372,2000000029723580,2000000013372318,
  2000000005834462,2000000002472193,2000000001018386,2000000000408175,2000000000159275,
  2000000000060532,2000000000022410,2000000000008078,2000000000002831,2000000000000963,
  2000000000000313,2000000000000095,2000000000000026,2000000000000004]
private def pvn_r384_3_1 : List ℕ := pCat pvn_r384_3_1_p0 (pCat pvn_r384_3_1_p1 (pCat
  pvn_r384_3_1_p2 (pCat pvn_r384_3_1_p3 (pCat pvn_r384_3_1_p4 pvn_r384_3_1_p5))))
private def pvn_r384_3_2_p0 : List ℕ := [1999999999999997,1999999999999995,2000000000000001,
  1999999999999995,2000000000000000,2000000000000013,1999999999999992,2000000000000048,
  1999999999999747,2000000000001088,1999999999995659,2000000000016034,1999999999944514,
  2000000000180867,1999999999442395,2000000001630020,1999999995472344,2000000011971184,
  1999999969829004,2000000072559768,1999999833352871,2000000365693835,1999999233060753,
  2000001537143193,1999997056678843,2000005380843169,1999990617706235,2000015580214414,
  1999975410254997,2000036781616760,1999948057504842,2000068875984295,1999914920418616,
  2000096714677995,1999900883312956,2000088004276245,1999938706599745,2000021026894482,
  2000025466628341,1999933782464632,2000087719508355,1999919862908122,2000042863883386,
  2000012415670415,1999936105259638,2000087862411877,1999929566988053,2000017043172271,
  2000046760185892,1999913656825212,2000077104581892,1999978672801598,1999950796477583,
  2000089713987316,1999928342759153,2000003085432527,2000067415143615,1999904208233736,
  2000040119869168,2000017560003600,1999870246341155,1999999967450998,1999855027024505,
  1999648416983357]
private def pvn_r384_3_2_p1 : List ℕ := [1999627185563904,1999223143376335,1998779511853625,
  1998462377616650,1997799771223549,1997318170015871,1997241693357930,1997220928426785,
  1997815168009117,1999051139015768,2000225397271462,2001425190561267,2002277389443432,
  2001951796475002,2000890909228605,1999625272181084,1998300502733408,1997939331458003,
  1998960331817175,2000351806542853,2001491385478995,2001892479018242,2000816681929111,
  1999080282029062,1998290844075146,1998697097883617,1999947692356692,2001475838984695,
  2001744362420731,2000322710058503,1998746007454537,1998505132008767,1999224877618194,
  2000994411629691,2001613041341509,2000996721852435,1998661119772157,1998644444002191,
  1999291953085878,2000917651919200,2001678514306452,2000396500152953,1999015230786774,
  1998251701309625,1999842838109492,2001722315706807,2000953920762931,1999697630405486,
  1998887246065632,1998683113427759,2000597590110502,2002031403907630,2000289825267676,
  1998459259364176,1998989802782036,2000269275919335,2001126125135711,2001059201382852,
  1999433928184066,1998164079967822,1999626923357025,2001807709566587,2001230128645481,
  1998890454482457]
private def pvn_r384_3_2_p2 : List ℕ := [1998369587141195,2000134932833540,2001451712167499,
  2000668778786485,1999146099794631,1999007169848726,2000189304238610,2000789257723797,
  2000158832598941,1999701877737771,2000035104316819,1999966203773677,1999334831084474,
  1999769662884939,2001220176949505,2001159624068649,1999007701281758,1997867823987215,
  1999720389174022,2002062696595212,2001714973956638,1999403051598020,1998191574905508,
  1999152938434828,2000630602616920,2000826728811891,1999787052241658,1999150529003732,
  2000172564375159,2001796219951231,2001624796788751,1999526976869393,1998492519969982,
  2000239135479855,2002059185660011,2000813782673259,1998244388467290,1998482998225942,
  2001249112802703,2002065666488314,1999546697861883,1997758691911190,1999590291037367,
  2002042402031440,2001177748481695,1998484685928659,1998299048527279,2000780846848746,
  2001891735445149,2000003121103224,1998261768675215,1999323397300577,2001304936827614,
  2001114298623171,1999284694869074,1998745883697928,2000120447187212,2001110933681961,
  2000339638415934,1999228639884957,1999426589009465,2000369138571746,2000563936032924,
  1999954502139813]
private def pvn_r384_3_2_p3 : List ℕ := [1999624815509896,1999903555847411,2000133410868738,
  2000030305350543,2000015339719197,2000176206158655,2000037512789377,1999623205830313,
  1999691527036927,2000398445201747,2000692928478508,1999880175629199,1999016729177845,
  1999550401101257,2000943796540425,2001127827649811,1999571555119703,1998406298478519,
  1999497552489441,2001511084213713,2001532637491757,1999285334283113,1997831022084004,
  1999373986816163,2001961410190237,2001978925365923,1999211723613532,1997359064478112,
  1999044392600246,2002116299073326,2002443943385507,1999507699804806,1997169821033593,
  1998530863080247,2001799791445692,2002700286515131,2000123089909629,1997489173873758,
  1998158658476022,2001098797884577,2002436685604647,2000597138637840,1998180741079249,
  1998334855996820,2000641151678813,2001889604542361,2000462298582859,1998413311065349,
  1998609603977364,2000854781308828,2002124028892440,2000558528732559,1997990765197465,
  1997715403858336,2000314334881575,2002796270449867,2002156268855670,1999010799161281,
  1996916647052060,1998223343085571,2001390273701009,2002844586755079,2001093941441869,
  1998315200957891]
private def pvn_r384_3_2_p4 : List ℕ := [1997726432197293,1999897593516440,2002196032663792,
  2001858834773173,1999133470631084,1997009446398481,1997933171313090,2001142442598381,
  2003449040283226,2002549641179841,1999359627297961,1997026883635969,1997749817628560,
  2000649879537310,2002730487924288,2001843221246036,1998728435166634,1996255678527282,
  1996715408867506,1999742771735697,2002707325211214,2003083742890362,2000623522984339,
  1997481359039335,1996317697059823,1998076245971919,2001267056106637,2003240319097694,
  2002343167906991,1999265020101635,1996608990418173,1997068427238165,2001501849103230,
  2008123038270837,2013171107482772,2012491048129052,2003046424287910,1983644915954395,
  1954775099589823,1917970206059548,1875245205307239,1828916615127510,1781745819175453,
  1737102780953543,1698848589213222,1670832099284899,1656138549334851,1656374817887616,
  1671266602915087,1698708413142430,1735231428797423,1776719512194302,1819154351827085,
  1859204947385343,1894560728841353,1923999469416364,1947249105371915,1964733415339649,
  1977288654744059,1985914432168224,1991591649168787,1995173855553645,1997341089718879,
  1998597649499567]
private def pvn_r384_3_2_p5 : List ℕ := [1999294942835973,1999664391676573,1999850522901453,
  1999939076233879,1999978378337219,1999994271756874,1999999820170916,2000001222977997,
  2000001205773774,2000000849370351,2000000515914412,2000000286028739,2000000148403082,
  2000000073017034,2000000034337517,2000000015512122,2000000006754938,2000000002842322,
  2000000001157686,2000000000457025,2000000000175037,2000000000065079,2000000000023496,
  2000000000008235,2000000000002800,2000000000000918,2000000000000287,2000000000000082,
  2000000000000021,2000000000000003]
private def pvn_r384_3_2 : List ℕ := pCat pvn_r384_3_2_p0 (pCat pvn_r384_3_2_p1 (pCat
  pvn_r384_3_2_p2 (pCat pvn_r384_3_2_p3 (pCat pvn_r384_3_2_p4 pvn_r384_3_2_p5))))
private def pvn_r384_3_3_p0 : List ℕ := [1999999999999996,2000000000000036,1999999999999647,
  2000000000002151,1999999999988864,2000000000050562,1999999999794293,2000000000760314,
  1999999997420390,2000000008093932,1999999976381634,2000000064371980,1999999835589424,
  2000000394476738,1999999109280621,2000001894891561,1999996199963182,2000007183280463,
  1999987209928705,2000021418294030,1999966350256370,2000049409929871,1999932578721292,
  2000084745227347,1999903259235184,2000097808059228,1999916878987380,2000051115326123,
  1999994130767335,1999957985489963,2000077393631840,1999914143162660,2000060880001203,
  1999990460532319,1999952744132868,2000082338795560,1999924172617836,2000028056502976,
  2000036721193362,1999918943205770,2000076087440710,1999978029221682,1999951993742383,
  2000086346059795,1999936047901652,1999994083471589,2000072848598802,1999915283252382,
  2000029414123903,2000051091585795,1999909251209431,2000053891903615,2000030715074035,
  1999910091997712,2000068974167185,2000016074245453,1999912078306036,2000077355271589,
  2000008605793395,1999911997312282,2000080954651850,2000008642389685,1999908655732742,
  2000080270250410]
private def pvn_r384_3_3_p1 : List ℕ := [2000016267633109,1999902494312414,2000074374577533,
  2000031380557829,1999895506562380,2000061123722953,2000052404857459,1999889054475767,
  2000031085172842,2000059412698310,1999846783705981,1999900201942401,1999883845784828,
  1999509733767949,1999238743138925,1998985197584459,1998208678500584,1997640425986175,
  1997172321314759,1996982498693256,1996801993461445,1998132154194217,1999023988741041,
  2000787015172673,2001752860151911,2002560626683922,2001621692110484,2000082765812416,
  1999047296840989,1997707065904026,1998338657737594,1999991926170438,2001284665865199,
  2002018629909262,2001016335920303,1999480104380884,1998359307579724,1998184640798535,
  2000083065168374,2001735723381483,2001322177912446,2000403446867455,1999075311092399,
  1997964493088050,1999400554987737,2001637979080995,2001512496966930,2000108743214143,
  1999068217118532,1998480688621901,1999433605080591,2001552318936582,2001727119707220,
  1999563895426411,1998287680985314,1999176093963938,2000606212880329,2001320251676863,
  2000827170483158,1999201451632927,1998254358918814,1999659013821866,2001720353610939,
  2001416347636151]
private def pvn_r384_3_3_p2 : List ℕ := [1999123655223398,1998110376132864,1999713096920163,
  2001610905593007,2001213463700195,1999184807585511,1998438692458818,1999941830263819,
  2001319995880826,2000601628901534,1999235320518066,1999374080701264,2000296253915764,
  2000237961858652,1999762925648932,2000208210141696,2000649366823919,1999717172428983,
  1998753011979524,1999743662858185,2001486376201247,2001207320033132,1999100641178253,
  1998114926985194,1999569363943859,2001536083997510,2001656447808204,1999883357304233,
  1998256818260079,1998661268629036,2000653914234564,2001685703391143,2000358621416718,
  1998735434204597,1999469830844039,2001384438140264,2001003734664444,1998419453711523,
  1997698126652283,2000326116832202,2002400314761126,2000798544611375,1998364951160251,
  1999264381133720,2002071603921313,2002144469101466,1999321882965861,1998129001756761,
  2000303607108053,2002110357431270,2000618159372575,1998343624830990,1998888610413251,
  2001153601378472,2001445340090049,1999490811845660,1998529195784768,1999919164937712,
  2001257679689354,2000528037714921,1999122469065327,1999239150019029,2000443781249141,
  2000769230832963]
private def pvn_r384_3_3_p3 : List ℕ := [1999930139306510,1999400780309638,1999844221476233,
  2000342825699769,2000194545796670,1999886706940883,1999929018191854,2000012032545099,
  1999869954976847,1999906007774398,2000285185246641,2000341339468476,1999728291759470,
  1999343892279940,2000016020567056,2000880275034804,2000462616092368,1999154650392608,
  1998968300370042,2000442884547741,2001465935804481,2000305554990946,1998483504356413,
  1998789276944369,2001018085044314,2001942420543113,2000001693610818,1997863970139574,
  1998734244412177,2001558781068435,2002297753475718,1999728924520055,1997401979854993,
  1998688323159051,2001896118886872,2002535266553674,1999642508580187,1997200650339201,
  1998595582525501,2001902248764284,2002587103200100,1999777159862325,1997363916134455,
  1998563546965877,2001593655159494,2002313505485607,1999924232634938,1997844358841615,
  1998834283612528,2001305305426780,2001760662669313,1999703427598144,1998171307820446,
  1999361068440366,2001555173799368,2001564760239083,1999223450482949,1997716581461310,
  1999274506903617,2002048600220614,2002404303014134,1999668945516886,1997134748044524,
  1997976345581044]
private def pvn_r384_3_3_p4 : List ℕ := [2001263130140365,2003078739479927,2001303414934382,
  1998126661492559,1997304559533834,1999643622429386,2002181517721259,2001878830391071,
  1999241889577028,1997593504142672,1999024595171867,2001898967127881,2002779844511447,
  2000438302707593,1997309123213590,1996802038024348,1999551246318859,2002738415149922,
  2003127334488714,2000454107612491,1997602880401495,1997526867032219,2000222190970396,
  2002819055206304,2002546298335452,1999493501886924,1996482022431837,1996311654515553,
  1999124650174378,2002338875011176,2003073091473695,2000738224517170,1997486046759730,
  1996245639829284,1998166448146628,2001651739293097,2003697930522990,2002355350182089,
  1998346978853310,1994676575269026,1994613331865141,1999513424843054,2007852727846361,
  2015867319562837,2019158231578379,2014208577699312,1999102060753469,1973418983255138,
  1937789181096929,1893622117283524,1843203197198293,1789951282147001,1738453066493634,
  1694006417624350,1661698977270037,1645320085535669,1646504653341353,1664409095527346,
  1696000263587547,1736817360163053,1781936093265790,1826854427875131,1868103757135930,
  1903512938633402]
private def pvn_r384_3_3_p5 : List ℕ := [1932162667096416,1954133199006636,1970164254142101,
  1981324884340923,1988752910086029,1993485409462654,1996373897853487,1998063196021422,
  1999009502040451,1999516687051198,1999776229634397,1999902596365119,1999960793588472,
  1999985893009639,1999995843693554,1999999329534198,2000000296416976,2000000408071069,
  2000000299983219,2000000180062685,2000000096608524,2000000047975950,2000000022433841,
  2000000009974042,2000000004241630,2000000001732209,2000000000681151,2000000000258392,
  2000000000094681,2000000000033539,2000000000011486,2000000000003798,2000000000001208,
  2000000000000366,2000000000000103,2000000000000024,2000000000000003]
private def pvn_r384_3_3 : List ℕ := pCat pvn_r384_3_3_p0 (pCat pvn_r384_3_3_p1 (pCat
  pvn_r384_3_3_p2 (pCat pvn_r384_3_3_p3 (pCat pvn_r384_3_3_p4 pvn_r384_3_3_p5))))
private def pvn_r384_3_4_p0 : List ℕ := [1999999999973376,2000000000220349,1999999998737109,
  2000000005785898,1999999977544801,2000000076162314,1999999769886639,2000000627153248,
  1999998445026824,2000003527455078,1999992652592355,2000014076514225,1999975195221118,
  2000040123627460,1999940686145339,2000079485064813,1999904812033013,2000099184917606,
  1999915152652809,2000049874826897,2000000147024726,1999949226611691,2000082485603781,
  1999920677893376,2000039001540070,2000021631869512,1999928476478749,2000081183392910,
  1999958136723278,1999975293874788,2000075989898430,1999924392587290,2000020959989640,
  2000050211362673,1999915862736135,2000052200357422,2000022714563217,1999919947704612,
  2000070033898176,2000001418682179,1999927068424944,2000079216911605,1999988123756198,
  1999931993888294,2000083735650059,1999982495662382,1999932516248093,2000085660138050,
  1999984026152410,1999928233352915,2000085192356644,1999992603072683,1999920009721625,
  2000081004050786,2000008279946327,1999909988594359,2000070667406327,2000030642995365,
  1999901613185723,2000051808112830,2000056935095409,1999901449841327,2000019570021654,
  2000088591724734]
private def pvn_r384_3_4_p1 : List ℕ := [1999903911400211,1999995635540162,2000081320258092,
  1999976423198448,1999882154632325,2000188989182646,1999871473573984,2000050588324447,
  1999902626965051,2000243333467500,1999688495038491,2000194962528994,2000001915814196,
  1999904050509091,2000060786833928,1999955717842009,2000136820242408,1999784680845288,
  2000102324039157,2000159393443356,1999694137267758,2000176962367600,2000096483825858,
  1999783274717539,2000108871268853,1999946273131362,1999771375066732,1999625908019556,
  1999084195367388,1998701360990842,1997861741446794,1996838926544919,1996739586739721,
  1996675919937284,1996981922492022,1998942492232270,2000876605490478,2001702209280414,
  2002425647476647,2001971823014320,1999647375215246,1998020093992401,1998191552393374,
  1998920182846375,2000348924315084,2002124071572399,2001908886305788,1999725820716085,
  1998292890137020,1998514266824327,1999555677332713,2001081038537324,2001985836034645,
  2000706404383537,1998453901258638,1998119534613348,1999886710647819,2001416210611405,
  2001364620522588,2000134905308777,1998742839188406,1998512367804554,2000038155365309,
  2001730736027553]
private def pvn_r384_3_4_p2 : List ℕ := [2001333864377525,1999166688156952,1998014362377977,
  1999442055832778,2001628406868699,2001657083713335,1999425386759185,1998005048609692,
  1999427842015920,2001581216684128,2001288585752390,1999212648012724,1998631951034088,
  2000089141249981,2000955950545104,2000181636377003,1999578757611087,2000020869467330,
  2000147929941655,1999544363090181,1999667029129384,2000724508722126,2000864096739610,
  1999507689573120,1998660777427758,1999721375943479,2001265100090586,2001205463117114,
  1999602194478412,1998377463868408,1999043658763528,2001027297088926,2001984528373084,
  2000404537058637,1998062202028066,1998232273206223,2000887558797751,2002188619745153,
  2000212020828344,1998192690672231,1999386143738775,2001599419248133,2000823364961857,
  1998191014052023,1998296044833385,2001366779923196,2002594739275185,2000019549974344,
  1997765246005773,1999199847583307,2001542419526199,2000771689334417,1998310731681394,
  1998402875663545,2000991453982656,2002023158604228,2000204696738468,1998812646881128,
  2000052650818949,2001678281687043,2001036112562393,1999309166051635,1999210547151009,
  2000567312900341]
private def pvn_r384_3_4_p3 : List ℕ := [2001012100352880,1999976474526125,1999253660336202,
  1999821993995415,2000525447149392,2000300045669874,1999750085906805,1999762973420233,
  2000068318642952,2000074303179516,1999979739673932,2000117906475474,2000130595224884,
  1999759070070566,1999634516473680,2000210564130394,2000642162789346,2000019322540760,
  1999157933110568,1999568180626999,2000841470342523,2000935926980618,1999447665612258,
  1998623903355467,1999964606654594,2001567472437790,2000824560018026,1998645677175769,
  1998389019962413,2000678783982940,2002125319078477,2000363739774964,1997883066849087,
  1998488032424265,2001460669203623,2002392706015983,1999752904299148,1997356398675009,
  1998805940554982,2002071907916596,2002375336155759,1999218519790373,1997165823165831,
  1999188321094906,2002351697928390,2002121183444979,1998906625467971,1997346788627198,
  1999564755905863,2002259759668576,2001634417033386,1998785799077480,1997868675919887,
  2000025235871102,2001954065182820,2000902819803145,1998596181107035,1998510192159692,
  2000717254808841,2001856762215297,2000142142315387,1998038992474030,1998725913821514,
  2001434443721497]
private def pvn_r384_3_4_p4 : List ℕ := [2002371381741132,2000013681786731,1997386121325288,
  1998076628112610,2001359648262291,2003037469516554,2000912017860449,1997652369741351,
  1997340664067271,2000269258183949,2002687289121638,2001653138507814,1998672690628524,
  1997604562230375,1999709455653402,2002158133982115,2001723725620318,1998879965670456,
  1997209703376624,1998958770073211,2002234754353202,2003207224464452,2000614831812027,
  1997254137408846,1996795601898929,1999672818234451,2002684574236274,2002608472282207,
  1999698806386657,1997282904527060,1998072731268953,2001268025368650,2003462440280336,
  2002239057497977,1998647580126021,1996109942054080,1997006150165525,2000390355888123,
  2002979006543286,2002309878036295,1999020194077869,1996205330403843,1996580365121469,
  2000045821431119,2003725490227655,2004328800832316,2000826211677829,1995362226156529,
  1991858282610112,1993470070772845,2000668630569856,2010989677999429,2020228287863254,
  2024044643551357,2019033049267525,2002995674276434,1974811989935635,1934451487890343,
  1883346438057077,1824872266818119,1764449277200816,1708922993122486,1665269522210922,
  1639042357353141]
private def pvn_r384_3_4_p5 : List ℕ := [1633118181001964,1647165047140915,1677952117609258,
  1720312344577536,1768388316534933,1816779668858856,1861329231047500,1899455483701116,
  1930087059634410,1953339547364129,1970090985264478,1981580160024144,1989099176573155,
  1993801936782574,1996615786689740,1998227230346938,1999110461147983,1999573476306914,
  1999805304648031,1999915896316547,1999965958515927,1999987320195681,1999995813968640,
  1999998893309959,1999999863247829,2000000092351292,2000000101398056,2000000066497839,
  2000000036146284,2000000017619189,2000000007947901,2000000003370552,2000000001355857,
  2000000000520205,2000000000191034,2000000000067298,2000000000022772,2000000000007402,
  2000000000002306,2000000000000686,2000000000000188,2000000000000046,2000000000000008]
private def pvn_r384_3_4 : List ℕ := pCat pvn_r384_3_4_p0 (pCat pvn_r384_3_4_p1 (pCat
  pvn_r384_3_4_p2 (pCat pvn_r384_3_4_p3 (pCat pvn_r384_3_4_p4 pvn_r384_3_4_p5))))
private def pvn_r384_3_5_p0 : List ℕ := [1999999980983945,2000000116183147,1999999513438922,
  2000001608375002,1999995563818591,2000010499792057,1999978353467959,2000039134165739,
  1999937962625977,2000085561467578,1999899378371422,2000096266948643,1999934587887075,
  2000011775451924,2000046742692589,1999916812241394,2000075833342370,1999975303211199,
  1999957884757259,2000081518082550,1999935871051348,1999999367679392,2000065563561535,
  1999921256978861,2000026789872184,2000048730016122,1999917793510589,2000041588151298,
  2000038242925686,1999917225911526,2000047409385958,2000035539643298,1999916254726731,
  2000046380299555,2000040168450199,1999914717850214,2000038885256322,2000050916259188,
  1999914460795684,2000024329241072,2000065659072403,1999918679147136,2000002235769172,
  2000080858144095,1999931105851229,1999973718025636,2000090932822036,1999955467931935,
  1999941255872833,2000091892280390,1999987408908829,1999921325003750,2000060815618971,
  2000052883608899,1999872468431843,2000080060992435,2000007602761498,2000009401729026,
  1999853968932165,2000258813530454,1999771153166325,2000117053897777,1999922495705767,
  2000139100956204]
private def pvn_r384_3_5_p1 : List ℕ := [1999842767510379,2000015716432353,2000191402715115,
  1999740706761046,2000132343584357,2000028999687321,1999930917513048,2000034597250693,
  1999932644916210,2000154905021384,1999875801083351,1999914495075159,2000270178972771,
  1999806370744601,1999914201156165,2000260217428942,1999845725514928,1999929722204057,
  2000155868219430,1999924212107573,1999994762099148,2000017588533321,1999951413778239,
  2000113138786790,1999930125023790,1999879247777012,2000225792003569,1999964518644217,
  1999743209601461,2000239589582088,2000120536927035,1999650701662455,2000101747330586,
  2000300814929949,1999705784068110,1999867126225534,2000378362820114,1999953818257183,
  1999735320636991,2000313930167757,2000203633861165,1999470839279574,1999280286253718,
  1998795228002904,1997270810953985,1996117413815475,1996089577296934,1996472381636794,
  1997606288589850,2000047674877477,2002249764170171,2002497758190193,2001254469333338,
  1999622435704332,1998125400611229,1997807117015854,1999501200919404,2001761869991705,
  2002168373168697,2000488414938565,1998641906855277,1998218162166566,1999344687527043,
  2001043413705757]
private def pvn_r384_3_5_p2 : List ℕ := [2001795451398830,2000714847681596,1998773967927288,
  1998102440230239,1999610626098362,2001698974788246,2001820335139179,1999586084769891,
  1997756939596668,1998925410294874,2001615995948365,2001981140938730,1999525431461591,
  1997982332389938,1999482615322036,2001403378320341,2000939679774592,1999379096522989,
  1999239040102998,2000116505071711,2000266176055570,1999910672378350,2000141769019318,
  2000430063182740,1999838372871172,1999196464791568,1999751464459650,2000832392237201,
  2000832264694300,1999684360004233,1998855903964966,1999391618231729,2000793138787692,
  2001460347118090,2000271392664164,1998349860364808,1998386612411660,2000878732739376,
  2002490420307400,2000544984666773,1997634530477962,1998182402502951,2001400619424073,
  2002271177173338,1999617805010190,1997977613354361,1999929186426945,2001827905006899,
  2000238347474525,1997945018574832,1999128501396228,2002051293795553,2001890915891642,
  1998851157296796,1997751983314044,2000021584169391,2001682482842908,2000261720174046,
  1998624730601465,1999704570994687,2001595286405130,2001068461193132,1998985802124444,
  1998569942793181]
private def pvn_r384_3_5_p3 : List ℕ := [2000060613104520,2000775691632523,1999787775517415,
  1999095605618989,1999945479735479,2000953611542560,2000730204912897,2000017269484526,
  2000036983118142,2000491862688321,2000497003454424,2000184768971281,2000124151243745,
  2000149617695676,1999937185635339,1999883647081779,2000276746818167,2000418208938413,
  1999800676876662,1999348079067156,2000017549862416,2000868482975952,2000344452579812,
  1999073584762061,1999196860133225,2000766402192351,2001267045569006,1999650339907478,
  1998397468759101,1999706299537539,2001675985528633,2001061403744842,1998611907143372,
  1998215400900087,2000715450095898,2002259368663252,2000259208082642,1997699949756868,
  1998658284369638,2001804705854098,2002258584595166,1999187697732203,1997271425540702,
  1999525415874326,2002559276669340,2001723981434768,1998263950217076,1997429378522685,
  2000460314536426,2002749644864654,2000897158703472,1997786235619243,1998071009132203,
  2001168564083742,2002361090892067,2000013283851020,1997829222887327,1999027073448699,
  2001570091184772,2001540727733544,1999156132800949,1998221021533397,2000145112991105,
  2001837037894029]
private def pvn_r384_3_5_p4 : List ℕ := [2000579352514052,1998279123439925,1998572874328587,
  2001206471166463,2002249579672021,1999934393633054,1997456614858373,1998479079627678,
  2001776340179812,2002795351995089,2000014309511324,1997138245957178,1998043025685284,
  2001498465297250,2002896889065791,2000490615647233,1997612282276751,1998051032367708,
  2001018624154292,2002409057782246,2000409312903166,1997847609624211,1998289851467337,
  2001235512224642,2002761902902820,2000678066464052,1997442153868502,1997118483911408,
  2000282775865868,2003257819181288,2002551812037883,1999013427295072,1996749535283218,
  1998260168357196,2001614346541855,2002841548745056,2000562650506892,1997494985186241,
  1997273554072670,2000334079222885,2003438527053096,2003217826862316,1999775513129802,
  1996545995177837,1996710812915117,1999982285255845,2002966813240188,2002581852715712,
  1999069194472548,1995756951490087,1995941714707557,1999852513248179,2004364657748930,
  2005560847972090,2001878585514683,1995360110028200,1990274892795977,1990395401411683,
  1996891184675342,2007941493309694,2019759055368656,2027939081666360,2028299275042596,
  2017174600161399]
private def pvn_r384_3_5_p5 : List ℕ := [1991693510930434,1950478208605448,1894664904904295,
  1828644440459492,1759877156942938,1697559583818303,1650512827330740,1625054709303401,
  1623612751359202,1644486939242879,1682699634071574,1731506953373795,1784017999641766,
  1834466581515934,1878904632448650,1915318390614268,1943325150785362,1963664041182712,
  1977668170079657,1986837398423782,1992558437959301,1995965017288548,1997902613883444,
  1998955769524525,1999502746530585,1999774020785780,1999902318814501,1999960047880728,
  1999984668696134,1999994561146392,1999998267465563,1999999538201084,1999999921371241,
  2000000012422968,2000000021415704,2000000014105705,2000000007268125,2000000003286682,
  2000000001358775,2000000000523461,2000000000189859,2000000000065217,2000000000021285,
  2000000000006609,2000000000001948,2000000000000541,2000000000000136,2000000000000028,
  2000000000000004]
private def pvn_r384_3_5 : List ℕ := pCat pvn_r384_3_5_p0 (pCat pvn_r384_3_5_p1 (pCat
  pvn_r384_3_5_p2 (pCat pvn_r384_3_5_p3 (pCat pvn_r384_3_5_p4 pvn_r384_3_5_p5))))
private def pvn_r384_3_6_p0 : List ℕ := [1999997930805112,2000008574877468,1999976399210940,
  2000049172478870,1999919384646760,2000103672016859,1999901064523550,2000055312613329,
  2000014988785815,1999925196987225,2000083320887705,1999969750254310,1999953585546553,
  2000083455784064,1999953807829056,1999966054064561,2000081420043080,1999952184666133,
  1999964960558478,2000081373239814,1999959882420412,1999954294064347,2000080786310047,
  1999976393145697,1999938378957491,2000074808466600,2000001645417924,1999923043840460,
  2000058370704955,2000033176998193,1999915924017232,2000028603993352,2000064353425528,
  1999925008944825,1999987444543337,2000085055400609,1999954015074172,1999945899133702,
  2000080108845839,2000007140060276,1999905717062834,2000067262377560,2000029157309028,
  1999952868904828,1999938815146031,2000173278499395,1999835786662414,2000082607232942,
  1999918651970793,2000192365757427,1999733245554796,2000176941600314,2000000903624356,
  1999910282606471,2000056614833610,1999957295088927,2000130177740625,1999804808617198,
  2000082553090308,2000141945271490,1999755970611642,2000125373029517,2000052455271680,
  1999897882896771]
private def pvn_r384_3_6_p1 : List ℕ := [2000053565635144,1999948109329959,2000091742144052,
  1999973996833579,1999847395733582,2000222081898163,1999966548318960,1999775342785612,
  2000235104804822,2000019637182768,1999775739637880,2000152406833913,2000056918093348,
  1999861595891191,2000060631930496,2000014011372012,1999974827463366,2000053768218599,
  1999908745466365,2000012899246934,2000151414058087,1999843058225607,1999917053380105,
  2000263036081724,1999918163219215,1999747243459782,2000251204997497,2000125406961427,
  1999658040520530,2000060326636969,2000320391555266,1999769795245283,1999795531719984,
  2000330642972473,2000041802574772,1999656863827547,2000116561517605,2000279687351221,
  1999766157787444,1999830881603329,2000293620745373,2000043219761072,1999702501413701,
  2000071936363411,2000258122423307,1999841280425961,1999812373878376,2000217014658567,
  2000100579840959,1999725444870099,1999923033630530,2000242259454802,2000087779347013,
  2000076759013134,2000543385839970,2000572692700903,1999610940843541,1998210086958256,
  1996782317977942,1995433502398591,1995007340304258,1996513974043773,1999452007331990,
  2001905142412001]
private def pvn_r384_3_6_p2 : List ℕ := [2002335681189890,2000799999717180,1998740702602035,
  1997861967880583,1998821426251802,2000751864587835,2002005630847151,2001378427066982,
  1999202626058599,1997648136310355,1998821786288516,2001675605978645,2002477055372647,
  1999897967971161,1997497776723779,1998704679953914,2001563858966192,2001857026174793,
  1999605359115849,1998443482787594,1999623886514408,2000810170149372,2000507471190591,
  1999862238081659,1999845848942260,1999881260233351,1999693575331296,1999923045308518,
  2000502582306519,2000485010208142,1999744144703085,1999266708644187,1999669387131182,
  2000514277249528,2000909931203883,2000235895988975,1998947232372200,1998744890674901,
  2000484894857428,2002037804846159,2000705003991380,1997908043367482,1997968885905062,
  2001265239317196,2002845690912131,2000079615492942,1997233730685197,1998750952275959,
  2001995392348510,2001731889242831,1998814480937682,1998355794092406,2000834022331541,
  2001593949502075,1999245804029181,1998052870646903,2000316900132915,2002289165495842,
  2000636237188028,1998067348708495,1998608263064548,2001005406808467,2001315682761318,
  1999559556523804]
private def pvn_r384_3_6_p3 : List ℕ := [1999075524653600,2000513047644512,2001082597418403,
  1999685498670080,1998647703134473,1999553478838148,2000801121627200,2000632676117264,
  1999845576162465,1999888501247207,2000382539842330,2000236553404111,1999669810827431,
  1999520529077070,1999701536576336,1999740612628516,1999861767485052,2000284009612062,
  2000426192848929,2000014331905094,1999930902238878,2000661400428382,2001046271157580,
  2000167704197670,1999316206431927,2000041759696088,2001228173130437,2000667513864377,
  1998998016843072,1999016395171781,2000900038689310,2001505530647152,1999569146431111,
  1998185388124951,1999828814411333,2001945087596074,2000916633484035,1998232060544604,
  1998341637450994,2001266223234543,2002258417000068,1999533599838321,1997435287337598,
  1999476983823225,2002464720586330,2001528755443264,1998080120311374,1997658351568763,
  2000994339281904,2002768443081625,2000143064362410,1997308749893908,1998748743256636,
  2002115308902457,2002082515117250,1998818371440562,1997536690675738,2000128885122096,
  2002358072362050,2000791052280830,1998119585113707,1998587658305430,2001233410308848,
  2001717160721699]
private def pvn_r384_3_6_p4 : List ℕ := [1999401936063041,1998186255903900,2000031305478720,
  2001825877685400,2000548706622599,1998243777737256,1998748950400218,2001434720171271,
  2002028986483083,1999362225949775,1997425867025731,1999341613262484,2002436971647579,
  2002081958579464,1998630961555861,1997039032381757,1999645188736216,2002751970183980,
  2001974351377876,1998500103804657,1997262045997567,1999862775778840,2002464888875315,
  2001428815183394,1998426401874037,1997852080863669,2000484598481483,2002456474315500,
  2000826725580896,1997788933579407,1997652715497151,2000849913727120,2003217923393030,
  2001517654537377,1997767199742733,1996678549348396,1999623599125076,2002938261630027,
  2002595641585743,1999186443481911,1997021126918765,1998706468589303,2002016053371108,
  2002749941895373,1999892123876058,1996819038404880,1997270324572457,2000958577541626,
  2003881215614911,2002826557952442,1998909871356394,1996304157023653,1997724575214459,
  2001583048960688,2003700288242673,2001625993514796,1997130916987067,1994521722957306,
  1996579521940830,2001977325298619,2006363324354382,2005913811110721,2000269022983469,
  1992711982372033]
private def pvn_r384_3_6_p5 : List ℕ := [1987911376187863,1989219396692030,1997263367858712,
  2010105078651525,2024076958539020,2034403153794811,2035533786055536,2021790961612105,
  1988804623375767,1935467134745275,1865447392969458,1787261926672209,1712550251088688,
  1653102254199817,1617779516404082,1610461816532480,1629622765500771,1669436129277637,
  1721789379849228,1778415133673178,1832516135829305,1879594385078707,1917521188816126,
  1946088555397790,1966337556087398,1979904649770802,1988524458746305,1993729455620090,
  1996721329545446,1998360079017113,1999215856473271,1999641958010550,1999844154110856,
  1999935498765855,1999974713811452,1999990666001396,1999996786783161,1999998985822270,
  1999999716433206,1999999935702521,1999999992106115,2000000002642183,2000000002707692,
  2000000001465513,2000000000639417,2000000000245935,2000000000086248,2000000000028014,
  2000000000008489,2000000000002403,2000000000000632,2000000000000150,2000000000000029,
  2000000000000004]
private def pvn_r384_3_6 : List ℕ := pCat pvn_r384_3_6_p0 (pCat pvn_r384_3_6_p1 (pCat
  pvn_r384_3_6_p2 (pCat pvn_r384_3_6_p3 (pCat pvn_r384_3_6_p4 pvn_r384_3_6_p5))))
private def pvn_r384_3_7_p0 : List ℕ := [1999968607415007,2000077107022032,1999888503943414,
  2000094247640342,1999982817121422,1999931753116043,2000086401570602,1999982909994313,
  1999931610029786,2000074889630259,2000006416810659,1999921135040031,2000052570611556,
  2000040427021823,1999919440486205,2000014194820382,2000071202791885,1999940128673077,
  1999966050184189,2000080873030291,1999985752257271,1999926978876232,2000056286368992,
  2000041889066355,1999919951567172,2000001493092367,2000079634002600,1999957348248441,
  1999939915180156,2000077322509897,2000015265641012,1999925929987492,2000000452277852,
  2000108843184977,1999893400143011,2000021667289790,1999981220414825,2000144408852582,
  1999753212318327,2000200283020076,1999907424192741,2000081305648291,1999860079513013,
  2000095919881532,2000086978553332,1999775657308627,2000169981043937,1999975417863728,
  1999970550042816,2000003391662203,1999951532209648,2000164930110859,1999837827274912,
  1999963548329138,2000224731270283,1999821317733952,1999971629480499,2000141215373099,
  1999915242369304,2000015398987198,1999978769529810,1999993966054006,2000120313040743,
  1999846839717987]
private def pvn_r384_3_7_p1 : List ℕ := [1999972914048478,2000231819139756,1999833168997916,
  1999880593581378,2000258257530024,1999927432020651,1999823733994448,2000173665692055,
  2000022013111613,1999871650769971,2000064018509709,2000015505430625,1999970865072016,
  2000049151358166,1999927305492673,1999990754789128,2000146104486668,1999892755699866,
  1999872209703192,2000225369317772,2000017647859509,1999722882051397,2000135527962486,
  2000234954624942,1999730816952356,1999885074120186,2000337490774270,1999959287968811,
  1999675159493410,2000185806056232,2000243142730431,1999713464937204,1999879648848309,
  2000327862618006,1999987845662186,1999688091182037,2000128658880266,2000252065962661,
  1999786671017568,1999833629304664,2000260388469844,2000072270875458,1999728078373984,
  2000016466825079,2000254865818382,1999909106505271,1999781764200117,2000146668348010,
  2000171085695858,1999816830303666,1999878590857648,2000202259639955,2000075873170236,
  1999793690828491,1999961464109613,2000197143472427,2000006192567803,1999813226696788,
  2000020067093794,2000207211036215,2000026722270528,1999807268990322,1999820071593097,
  1999874072841278]
private def pvn_r384_3_7_p2 : List ℕ := [1999893786090311,2000187863481767,2000922257291027,
  2001599065351068,2001202902834584,1999156931565836,1996316108969980,1994503624624107,
  1994793831154266,1996818947458288,1999573454530051,2001709447646378,2001542078035934,
  1998932260316055,1996896096221662,1998486169322070,2002001680716782,2002693940291878,
  1999713979470570,1997474702575277,1998915425015200,2001424677878699,2001477351591051,
  1999735739451428,1998956780848978,1999619095698267,2000289421742016,2000382480195227,
  2000273385139704,2000014759728417,1999621220605253,1999589066774976,2000071875911359,
  2000472188476419,2000363547395712,1999917023805463,1999438336984952,1999395014208285,
  2000255253513274,2001235296833236,2000579304545882,1998593964280977,1998327120682159,
  2000876549149154,2002554892067935,2000267844342128,1997221413914975,1998398532341526,
  2002187984265751,2002555931343231,1998941023986535,1997237332326108,1999964816283982,
  2002320803133198,2000615337168347,1998263081605138,1999324482344274,2001493284615461,
  2000676448740327,1998422253667020,1998948479667509,2001488791217174,2001665587694947,
  1999156936398442]
private def pvn_r384_3_7_p3 : List ℕ := [1998097575841694,1999953479888437,2001446065903193,
  2000459728674818,1999192168800744,1999752095209031,2000686964594467,2000115489601571,
  1999109926860383,1999489431634606,2000612515836706,2000771706218735,2000065383145949,
  1999716261137802,1999839761570547,1999797763005888,1999712135367498,1999973803336347,
  2000194863868555,2000045724546057,2000098123103372,2000568282640577,2000491792195158,
  1999522775735020,1999067929619133,1999963290106200,2000643067944615,1999729612658787,
  1998800811698485,1999860707478370,2001493741294754,2000941782731554,1999075551841933,
  1999264625604135,2001447396234808,2001842829300115,1999475687963955,1998258118592449,
  2000396260960067,2002282297368725,2000476986367681,1997841580008312,1998908644067359,
  2002006993407550,2001835319807404,1998514466634240,1997618965669145,2000768046773745,
  2002712582855270,2000119191586451,1997281351020354,1998965685874154,2002381168180195,
  2001838861318300,1998266873132214,1997604475856008,2000878350698004,2002614026390947,
  2000032814624991,1997522573217349,1999159713146283,2002052384074197,2001423075478181,
  1998531094465198]
private def pvn_r384_3_7_p4 : List ℕ := [1998260137751005,2000871125237538,2001840361658148,
  1999645278945432,1998167308240355,1999921269526000,2001811782142156,2000517330482335,
  1998219102601093,1998930813625032,2001618061629872,2001751301856363,1998868436250910,
  1997596147540421,2000202082093718,2002710620572848,2001062577956822,1997640026057016,
  1997717248960338,2001277267275785,2002959749758181,2000238028743236,1997223922886061,
  1998374129923224,2001831070240350,2002408913640890,1999422427915205,1997498655857287,
  1999453632415672,2002161379029207,2001449316885174,1998419204431803,1997735540666352,
  2000587737736567,2002830918042064,2001020721768296,1997511876734667,1997240065900449,
  2000771506433162,2003420965166029,2001626500112654,1997754464431698,1996867710369755,
  1999993618690333,2002915733441138,2001861712051628,1998390330101154,1997181606736885,
  1999868894059374,2002961695251733,2002359393187678,1998573126678121,1996138925505145,
  1998093232319537,2002313934222167,2004018969909785,2001309923435757,1997291254050580,
  1996505146359631,1999868035054983,2003688512919947,2003637234218821,1999300075864601,
  1994659327457770]
private def pvn_r384_3_7_p5 : List ℕ := [1994251895129217,1998929412791059,2005108954623629,
  2007818829559120,2004566119766502,1996922483880444,1989178748679041,1985751049073178,
  1989305963522521,2000186054467045,2016418745511866,2033580601558222,2044737297064461,
  2041364490124287,2015767875724933,1964355005954998,1890171291493037,1803190978581109,
  1717928872765839,1649288868267559,1608366526026214,1599795881597920,1621384801550591,
  1665766736340179,1723114961922619,1783830596445288,1840428467641665,1888340905804581,
  1925786455300096,1953074965920109,1971739452658182,1983774661163564,1991114140989594,
  1995356660496800,1997684758836978,1998898779608622,1999500664362635,1999784374557716,
  1999911464600555,1999965513065707,1999987297818257,1999995597847590,1999998575244999,
  1999999574693537,1999999885539318,1999999973570260,1999999995490800,1999999999879595,
  2000000000348443,2000000000208563,2000000000086163,2000000000029814,2000000000009128,
  2000000000002520,2000000000000630,2000000000000138,2000000000000025,2000000000000002]
private def pvn_r384_3_7 : List ℕ := pCat pvn_r384_3_7_p0 (pCat pvn_r384_3_7_p1 (pCat
  pvn_r384_3_7_p2 (pCat pvn_r384_3_7_p3 (pCat pvn_r384_3_7_p4 pvn_r384_3_7_p5))))
private def pvi_r384_3 : List ℤ := bDc bZ (rPad bZ 385 pvn_r384_3_0)
private def pvo_r384_3 : List ℤ := bDc bZ (rPad bZ 385 pvn_r384_3_7)
private def phbn_r384_4_p0 : List ℕ := [82831095749684,116873930244644,142813811741096,
  164529655574544,183527635984371,200582030661857,216153858414686,230544184485726,243962603452134,
  256562063714086,268458287901981,279741381783338,290483161189089,300741983236694,310566048857667,
  319995729629298,329065249906037,337803930154878,346237123888926,354386935804517,362272780565986,
  369911823479564,377319332240769,384508960776931,391492980570779,398282470890627,404887476524303,
  411317139564386,417579810286832,423683141045644,429634166264263,435439370964380,441104749781629,
  446635858037144,452037856136687,457315548335014,462473416717431,467515651102166,472446175447880,
  477268671254093,481986598363738,486603213512756,491121586918697,495544617156572,499875044533826,
  504115463145968,508268331768961,512335983723076,516320635824828,520224396528267,524049273343871,
  527797179612098,531469940699140,535069299674200,538596922520515,542054402926266,545443266696175,
  548764975819988,552020932230032,555212481276503,558340914946071,561407474846692,564413354979125,
  567359704313573]
private def phbn_r384_4_p1 : List ℕ := [570247629187996,573078195543016,575852431006871,
  578571326842587,581235839768384,583846893661287,586405381153028,588912165126476,591368080120090,
  593773933647261,596130507436776,598438558600120,600698820730853,602912004940841,605078800837743,
  607199877447796,609275884087602,611307451188337,613295191075545,615239698707392,617141552374100,
  619001314361006,620819531577568,622596736154424,624333446010474,626030165391827,627687385384292,
  629305584400992,630885228646580,632426772559400,633930659232885,635397320817362,636827178903379,
  638220644887576,639578120322080,640899997248310,642186658516042,643438478088529,644655821334413,
  645839045307111,646988499012353,648104523664453,649187452931911,650237613172871,651255323660951,
  652240896801915,653194638341645,654116847565830,655007817491775,655867835052704,656697181274915,
  657496131448118,658264955289283,659003917100278,659713275919607,660393285668486,661044195291540,
  661666248892337,662259685863993,662824741015082,663361644691019,663870622891144,664351897381671,
  664805685804686]
private def phbn_r384_4_p2 : List ℕ := [665232201783350,665631655023476,666004251411621,
  666350193109841,666669678647236,666962903008423,667230057719057,667471330928514,667686907489842,
  667876969037105,668041694060195,668181257977232,668295833204626,668385589224897,668450692652337,
  668491307296593,668507594224237,668499711818420,668467815836649,668412059466774,668332593381249,
  668229565789711,668103122489953,667953406917336,667780560192695,667584721168794,667366026475373,
  667124610562836,666860605744627,666574142238329,666265348205538,665934349790541,665581271157841,
  665206234528561,664809360215770,664390766658751,663950570456250,663488886398745,663005827499738,
  662501505026132,661976028527688,661429505865608,660862043240267,660273745218099,659664714757684,
  659035053235043,658384860468165,657714234740785,657023272825430,656312070005760,655580720098209,
  654829315472951,654057947074201,653266704439873,652455675720600,651624947698144,650774605803189,
  649904734132546,649015415465781,648106731281261,647178761771652,646231585858859,645265281208429,
  644279924243422]
private def phbn_r384_4_p3 : List ℕ := [643275590157764,642252352929075,641210285330999,
  640149458945031,639069944171847,637971810242152,636855125227040,635719956047881,634566368485735,
  633394427190294,632204195688365,630995736391888,629769110605495,628524378533618,627261599287135,
  625980830889572,624682130282848,623365553332567,622031154832869,620678988510820,619309107030354,
  617921561995762,616516403954729,615093682400908,613653445776042,612195741471619,610720615830058,
  609228114145433,607718280663717,606191158582543,604646790050487,603085216165850,601506476974949,
  599910611469896,598297657585861,596667652197819,595020631116758,593356629085343,591675679773029,
  589977815770613,588263068584194,586531468628560,584783045219955,583017826568234,581235839768384,
  579437110791386,577621664474411,575789524510328,573940713436504,572075252622870,570193162259240,
  568294461341856,566379167659127,564447297776551,562498867020774,560533889462778,558552377900146,
  556554343838388,554539797471286,552508747660223,550461201912458,548397166358312,546316645727215,
  544219643322569]
private def phbn_r384_4_p4 : List ℕ := [542106160995396,539976199116695,537829756548476,
  535666830613414,533487417063050,531291510044493,529079102065552,526850183958224,524604744840476,
  522342772076231,520064251233487,517769166040474,515457498339773,513129228040272,510784333066885,
  508422789307916,506044570559938,503649648470092,501237992475648,498809569740711,496364345089922,
  493902280938982,491423337221862,488927471314494,486414637954781,483884789158711,481337874132366,
  478773839179603,476192627605168,473594179612980,470978432199308,468345319040563,465694770375369,
  463026712880598,460341069540999,457637759512037,454916697975531,452177795987654,449420960318813,
  446646093284904,443853092569392,441041851035627,438212256528770,435364191666629,432497533618685,
  429612153872504,426707917986682,423784685329387,420842308801501,417880634543278,414899501623323,
  411898741708636,408878178714309,405837628431387,402776898131229,399695786144598,396594081413507,
  393471563013712,390327999645488,387163149090172,383976757629648,380768559425715,377538275855974,
  374285614802506]
private def phbn_r384_4_p5 : List ℕ := [371010269889273,367711919663717,364390226717588,
  361044836741480,357675377506959,354281457769522,350862666084823,347418569529773,343948712319148,
  340452614307220,336929769362675,333379643603666,329801673478162,326195263672948,322559784832397,
  318894571065707,315198917218402,311472075880565,307713254100435,303921609767479,300096247623809,
  296236214856648,292340496217300,288408008603527,284437595032073,280428017916043,276377951547400,
  272285973667556,268150555988216,263970053499347,259742692370502,255466556214092,251139570433038,
  246759484318025,242323850488389,237830001181448,233275020782452,228655713844172,223968567661587,
  219209708229925,214374848104897,209459224276325,204457523623827,199363792792602,194171328331562,
  188872541560105,183458790700948,177920170068197,172245242114581,166420692248017,160430877419226,
  154257225683281,147877421965356,141264279154946,134384132137886,127194483071361,119640422123926,
  111648943559111,103119415631709,93906452567867,83786155417495,72380365281801,58949330197548,
  41577012611459]
private def phbn_r384_4 : List ℕ := pCat phbn_r384_4_p0 (pCat phbn_r384_4_p1 (pCat phbn_r384_4_p2
  (pCat phbn_r384_4_p3 (pCat phbn_r384_4_p4 phbn_r384_4_p5))))
private def phbv_r384_4 : List ℤ := uOh phbn_r384_4
private def pvn_r384_4_0_p0 : List ℕ := [2000031392584993,1999922892977968,2000111496056586,
  1999905752359658,2000017182878578,2000068246883957,1999913598429398,2000017090005687,
  2000068389970214,1999925110369741,1999993583189341,2000078864959969,1999947429388444,
  1999959572978177,2000080559513795,1999985805179618,1999928797208115,2000059871326923,
  2000033949815811,1999919126969709,2000014247742729,2000073021123768,1999943713631008,
  1999958110933645,2000080048432828,1999998506907633,1999920365997400,2000042651751559,
  2000060084819844,1999922677490103,1999984734358988,2000074070012508,1999999547722148,
  1999891156815023,2000106599856989,1999978332710210,2000018779585175,1999855591147418,
  2000246787681673,1999799716979924,2000092575807259,1999918694351709,2000139920486987,
  1999904080118468,1999913021446668,2000224342691373,1999830018956063,2000024582136272,
  2000029449957184,1999996608337797,2000048467790352,1999835069889141,2000162172725088,
  2000036451670862,1999775268729717,2000178682266048,2000028370519501,1999858784626901,
  2000084757630696,1999984601012802,2000021230470190,2000006033945994,1999879686959257,
  2000153160282013]
private def pvn_r384_4_0_p1 : List ℕ := [2000027085951522,1999768180860244,2000166831002084,
  2000119406418622,1999741742469976,2000072567979349,2000176266005552,1999826334307945,
  1999977986888387,2000128349230029,1999935981490291,1999984494569375,2000029134927984,
  1999950848641834,2000072694507327,2000009245210872,1999853895513332,2000107244300134,
  2000127790296808,1999774630682228,1999982352140491,2000277117948603,1999864472037514,
  1999765045375058,2000269183047644,2000114925879814,1999662509225730,2000040712031189,
  2000324840506590,1999814193943768,1999756857269569,2000286535062796,2000120351151691,
  1999672137381994,2000012154337814,2000311908817963,1999871341119734,1999747934037339,
  2000213328982432,2000166370695336,1999739611530156,1999927729124542,2000271921626016,
  1999983533174921,1999745134181618,2000090893494729,2000218235799883,1999853331651990,
  1999828914304142,2000183169696334,2000121409142352,1999797740360045,1999924126829764,
  2000206309171509,2000038535890387,1999802856527573,1999993807432197,2000186773303212,
  1999979932906206,1999792788963785,1999973277729472,2000192731009678,2000179928406903,
  2000125927158722]
private def pvn_r384_4_0_p2 : List ℕ := [2000106213909689,1999812136518233,1999077742708973,
  1998400934648932,1998797097165416,2000843068434164,2003683891030020,2005496375375893,
  2005206168845734,2003181052541712,2000426545469949,1998290552353622,1998457921964066,
  2001067739683945,2003103903778338,2001513830677930,1997998319283218,1997306059708122,
  2000286020529430,2002525297424723,2001084574984800,1998575322121301,1998522648408949,
  2000264260548572,2001043219151022,2000380904301733,1999710578257984,1999617519804773,
  1999726614860296,1999985240271583,2000378779394747,2000410933225024,1999928124088641,
  1999527811523581,1999636452604288,2000082976194537,2000561663015048,2000604985791715,
  1999744746486726,1998764703166764,1999420695454118,2001406035719023,2001672879317841,
  1999123450850846,1997445107932065,1999732155657872,2002778586085025,2001601467658474,
  1997812015734249,1997444068656769,2001058976013465,2002762667673892,2000035183716018,
  1997679196866802,1999384662831653,2001736918394862,2000675517655726,1998506715384539,
  1999323551259673,2001577746332980,2001051520332491,1998511208782826,1998334412305053,
  2000843063601558]
private def pvn_r384_4_0_p3 : List ℕ := [2001902424158306,2000046520111563,1998553934096807,
  1999540271325182,2000807831199256,2000247904790969,1999313035405533,1999884510398429,
  2000890073139617,2000510568365394,1999387484163294,1999228293781265,1999934616854051,
  2000283738862198,2000160238429453,2000202236994112,2000287864632502,2000026196663653,
  1999805136131445,1999954275453943,1999901876896628,1999431717359423,1999508207804842,
  2000477224264980,2000932070380867,2000036709893800,1999356932055385,2000270387341213,
  2001199188301515,2000139292521630,1998506258705246,1999058217268446,2000924448158067,
  2000735374395865,1998552603765192,1998157170699885,2000524312036045,2001741881407551,
  1999603739039933,1997717702631275,1999523013632319,2002158419991688,2001091355932641,
  1997993006592450,1998164680192596,2001485533365760,2002381034330855,1999231953226255,
  1997287417144730,1999880808413549,2002718648979646,2001034314125846,1997618831819805,
  1998161138681700,2001733126867786,2002395524143992,1999121649301996,1997385973609053,
  1999967185375009,2002477426782651,2000840286853717,1997947615925803,1998576924521819,
  2001468905534802]
private def pvn_r384_4_0_p4 : List ℕ := [2001739862248995,1999128874762462,1998159638341852,
  2000354721054568,2001832691759645,2000078730474000,1998188217857844,2000517330482335,
  1998219102601093,1998930813625032,2001618061629872,2001751301856363,1998868436250910,
  1997596147540421,2000202082093718,2002710620572848,2001062577956822,1997640026057016,
  1997717248960338,2001277267275785,2002959749758181,2000238028743236,1997223922886061,
  1998374129923224,2001831070240350,2002408913640890,1999422427915205,1997498655857287,
  1999453632415672,2002161379029207,2001449316885174,1998419204431803,1997735540666352,
  2000587737736567,2002830918042064,2001020721768296,1997511876734667,1997240065900449,
  2000771506433162,2003420965166029,2001626500112654,1997754464431698,1996867710369755,
  1999993618690333,2002915733441138,2001861712051628,1998390330101154,1997181606736885,
  1999868894059374,2002961695251733,2002359393187678,1998573126678121,1996138925505145,
  1998093232319537,2002313934222167,2004018969909785,2001309923435757,1997291254050580,
  1996505146359631,1999868035054983,2003688512919947,2003637234218821,1999300075864601,
  1994659327457770]
private def pvn_r384_4_0_p5 : List ℕ := [1994251895129217,1998929412791059,2005108954623629,
  2007818829559120,2004566119766502,1996922483880444,1989178748679041,1985751049073178,
  1989305963522521,2000186054467045,2016418745511866,2033580601558222,2044737297064461,
  2041364490124287,2015767875724933,1964355005954998,1890171291493037,1803190978581109,
  1717928872765839,1649288868267559,1608366526026214,1599795881597920,1621384801550591,
  1665766736340179,1723114961922619,1783830596445288,1840428467641665,1888340905804581,
  1925786455300096,1953074965920109,1971739452658182,1983774661163564,1991114140989594,
  1995356660496800,1997684758836978,1998898779608622,1999500664362635,1999784374557716,
  1999911464600555,1999965513065707,1999987297818257,1999995597847590,1999998575244999,
  1999999574693537,1999999885539318,1999999973570260,1999999995490800,1999999999879595,
  2000000000348443,2000000000208563,2000000000086163,2000000000029814,2000000000009128,
  2000000000002520,2000000000000630,2000000000000138,2000000000000025,2000000000000002]
private def pvn_r384_4_0 : List ℕ := pCat pvn_r384_4_0_p0 (pCat pvn_r384_4_0_p1 (pCat
  pvn_r384_4_0_p2 (pCat pvn_r384_4_0_p3 (pCat pvn_r384_4_0_p4 pvn_r384_4_0_p5))))
private def pvn_r384_4_1_p0 : List ℕ := [2000092915593860,1999880374659355,2000042361581904,
  2000068956109139,1999915390796639,1999987857331219,2000086972394783,1999965268461031,
  1999933316604745,2000066157149946,2000034672944623,1999919173606093,2000000936185485,
  2000079848182822,1999965995471553,1999934117838336,2000060150355872,2000042486738596,
  1999923489998500,1999986042403846,2000082444183717,1999982983426019,1999924938389598,
  2000040370793595,2000068416605868,1999922350594267,1999980776340178,2000046401309641,
  2000065388167553,1999837567443315,2000121789747779,1999944569550039,2000119426286445,
  1999758285578244,2000227620195260,1999924521747912,1999977044800006,1999999195288466,
  1999992319107118,2000136825515049,1999775840271691,2000106330759093,2000100481235383,
  1999837267825705,2000074691751036,1999977799771535,2000046846174441,2000003034783305,
  1999847073164902,2000189786752074,2000003431594575,1999789070082246,2000172759372508,
  2000036641802027,1999859913418967,2000070920528152,1999997179568989,2000007636637312,
  2000032234639507,1999871656382908,2000093943124219,2000115563371704,1999772903091095,
  2000035931380007]
private def pvn_r384_4_1_p1 : List ℕ := [2000226405189614,1999808696299504,1999905815654825,
  2000230728396189,1999942577092237,1999852553187254,2000122469531198,2000026544930650,
  1999921156669717,2000038347501303,1999983237909549,1999990349932999,2000084409423427,
  1999915652857462,1999925913752500,2000181177226395,1999986118645484,1999775200909071,
  2000140590378622,2000190729969915,1999744968456909,1999910825238474,2000317654193464,
  1999952796998248,1999687997938698,2000180153472851,2000244257565818,1999720803566333,
  1999864574372102,2000328097108946,2000011621658221,1999674996282292,2000103752082920,
  2000278683643897,1999805593710570,1999796537953929,2000252315757893,2000114707046485,
  1999723354371719,1999974260772860,2000271617100598,1999946282591290,1999755777287949,
  2000117854119667,2000202326904904,1999835681929407,1999846640867341,2000193388900603,
  2000103588637447,1999792911277355,1999942137623789,2000208394273490,2000019658234732,
  1999799393200185,2000008703911355,2000186878474702,1999974110188197,1999829940880474,
  2000031388536015,2000153303119040,1999976034045895,1999860177657203,1999997459128324,
  2000123624176652]
private def pvn_r384_4_1_p2 : List ℕ := [2000051871827326,1999922281129917,1999922738353824,
  2000025815060286,2000002327241422,1999804115737640,1999883310271811,2000552412186810,
  2001058220584034,2000325532558656,1998695699035811,1997657737430862,1997912304016520,
  1999244150630101,2001811129432187,2005189600929391,2006691098728404,2003991243718029,
  1999498660157495,1998317586944388,2001186211093748,2003353534239595,2001658322219374,
  1998750740620643,1998394260447533,2000149978718620,2001182173822219,2000636973926497,
  1999752011434679,1999417035724903,1999617981684616,2000131642738999,2000514378258640,
  2000308098249020,1999786961539059,1999605429071584,1999787084169548,2000033946956971,
  2000405753861215,2000614086481401,1999880210381833,1998787553820574,1999338114462169,
  2001394768378008,2001699511470744,1999062062031488,1997421220019731,1999894559544734,
  2002892554974037,2001389092525866,1997543244096424,1997585615871908,2001444449192723,
  2002794215039058,1999675472785368,1997501727825142,1999587384186587,2001890844072298,
  2000592849506120,1998530381444849,1999508635940067,2001453076231359,2000582383742714,
  1998426697913703]
private def pvn_r384_4_1_p3 : List ℕ := [1998944542246248,2001345985907381,2001565997625857,
  1999362721297109,1998420028624113,1999909612025731,2001037789098432,2000270566990201,
  1999481042830434,2000021038428387,2000524226886189,1999884746017228,1999262740489501,
  1999737361724257,2000474027339197,2000482448196883,2000140410968319,1999972473452531,
  1999744319709589,1999512705960578,1999822854766726,2000362728785753,2000223886293870,
  1999755574424464,2000105969327088,2000798295187160,2000249693525764,1998931204544855,
  1999061348550416,2000594022037698,2000875721298656,1999364433459346,1998959984701676,
  2000831603363364,2001861362475281,1999993729092901,1998264607606044,1999707229170054,
  2001735288000086,2000450208003124,1997758684501691,1998362779132530,2001373209111244,
  2001526476252811,1998424643391704,1997519505080553,2000619512558135,2002478310842324,
  1999831766941221,1997245794777557,1999297363568242,2002540562894451,2001386266650887,
  1997806844985095,1997967819804200,2001586294515691,2002453529227561,1999146105739364,
  1997364453001449,2000088268411022,2002509810860360,2000712516562007,1997582850223612,
  1999207580908148]
private def pvn_r384_4_1_p4 : List ℕ := [2001111767158360,2002393428886375,1997990695960658,
  1998349078655724,2001731353109729,2000721064272969,1999154886096794,1999909877461435,
  2000003212782554,1999387467489674,2000480515281474,2001716434945133,2000034231403932,
  1997360602010307,1998101265173804,2001443258014578,2002126642502166,1999017489623122,
  1997210717528823,1999831163855647,2002836220593681,2001420818096128,1997751387084133,
  1997569556072246,2001123482134618,2002856632472004,2000180190737575,1997380739030040,
  1998739902262663,2001934992029074,2001925473303411,1998882433526061,1997725101552441,
  2000283275486272,2002466333921625,2000719279090233,1997627758974581,1998022851135329,
  2001564511993589,2003073322978804,2000156934889543,1996830797500145,1997818150966341,
  2001811748720351,2003324000333659,2000360325294997,1997073278187751,1997896343832569,
  2001508396190506,2002848170804940,2000119599830705,1997150968414238,1998115158374044,
  2001888155643719,2003507166112287,2000654556565798,1996697973758099,1996500533826676,
  2000404823743219,2003826254089873,2002773341770987,1998538291175548,1996117067347805,
  1998426344066722]
private def pvn_r384_4_1_p5 : List ℕ := [2003005425656007,2004725484029146,2001304139274679,
  1995715387327572,1993255870200215,1996519752313572,2003140394311964,2007955332889484,
  2007122676896877,2000626455009491,1991809995630084,1985239417102986,1984827301096740,
  1992846574402766,2009174710947266,2030251126529536,2048397226102815,2052833904673683,
  2032997028728677,1983094337643588,1905637631644384,1811921120603701,1718962191756676,
  1644230028905568,1600461121431440,1592568461172311,1617462005914016,1666283337162062,
  1727762558681904,1791344440620046,1849210359518131,1896970265999711,1933300331289031,
  1959020918302701,1976077327705520,1986718540291998,1992983615315207,1996472023114139,
  1998311631458880,1999231246347483,1999667198723103,1999863169002255,1999946655228976,
  1999980324438955,1999993155981810,1999997765038236,1999999319425971,1999999808786020,
  1999999951329004,1999999989176239,1999999998082690,1999999999824178,2000000000050061,
  2000000000036965,2000000000014512,2000000000004485,2000000000001180,2000000000000266,
  2000000000000049,2000000000000006]
private def pvn_r384_4_1 : List ℕ := pCat pvn_r384_4_1_p0 (pCat pvn_r384_4_1_p1 (pCat
  pvn_r384_4_1_p2 (pCat pvn_r384_4_1_p3 (pCat pvn_r384_4_1_p4 pvn_r384_4_1_p5))))
private def pvi_r384_4 : List ℤ := bDc bZ (rPad bZ 385 pvn_r384_4_0)
private def pvo_r384_4 : List ℤ := bDc bZ (rPad bZ 385 pvn_r384_4_1)
private def phbn_r384_5_p0 : List ℕ := [83386080459569,117657008672894,143770692501386,
  165632036779815,184757307412604,201925969904570,217602131980512,232088876079920,245597201105034,
  258281080240537,270257011481320,281615704321349,292429455771816,302757013954398,312646902756379,
  322139764252591,331270052107424,340067283240794,348556981039355,356761398305275,364700079784979,
  372390305795638,379847446329352,387085246797457,394116060904046,400951042150717,407600302627362,
  414073045680388,420377677534249,426521901815232,432512800078806,438356900797588,444060238772456,
  449628406546292,455066599100598,460379652879585,465572079999417,470648098350933,475611658184091,
  480466465665185,485216003818781,489863551201592,494412198602235,498864864016744,503224306113167,
  507493136367965,511673830031386,515768736057408,519780086115654,523710002787233,527560507033341,
  531333525014193,535030894326298,538654369717765,542205628334248,545686274541956,549097844368801,
  552441809600150,555719581561555,558932514617324,562081909410692,565169015868634,568195035991950,
  571161126449171]
private def phbn_r384_5_p1 : List ℕ := [574068400990939,576917932699890,579710756089573,
  582447869064673,585130234753611,587758783223569,590334413087092,592857993008530,595330363117918,
  597752336339145,600124699638735,602448215200971,604723621534634,606951634516179,609132948373773,
  611268236616263,613358152910797,615403331912568,617404390049820,619361926267057,621276522729160,
  623148745488888,624979145120102,626768257318818,628516603474097,630224691210596,631893014904496,
  633522056174382,635112284348571,636664156910233,638178119921616,639654608428538,641094046846287,
  642496849327943,643863420116111,645194153878965,646489436031449,647749643042446,648975142728638,
  650166294535771,651323449807983,652446952045791,653537137153341,654594333675439,655618863024900,
  656611039700669,657571171497185,658499559705411,659396499305926,660262279154462,661097182160250,
  661901485457496,662675460570324,663419373571481,664133485235076,664818051183650,665473322029806,
  666099543512652,666696956629289,667265797761552,667806298798216,668318687252861,668803186377580,
  669260015272703]
private def phbn_r384_5_p2 : List ℕ := [669689388992708,670091518648479,670466611506055,
  670814871082015,671136497235644,671431686257995,671700630957984,671943520745622,672160541712512,
  672351876709699,672517705422996,672658204445856,672773547349915,672863904753259,672929444386528,
  672970331156926,672986727210204,672978791990711,672946682299558,672890552350987,672810553826986,
  672706835930225,672579545435372,672428826738833,672254821906981,672057670722919,671837510731836,
  671594477284978,671328703582317,671040320713918,670729457700086,670396241530300,670040797200988,
  669663247752181,669263714303067,668842316086497,668399170482452,667934393050528,667448097561440,
  666940396027601,666411398732776,665861214260862,665289949523794,664697709788623,664084598703772,
  663450718324501,662796169137600,662121050085323,661425458588593,660709490569489,659973240473035,
  659216801288302,658440264568849,657643720452512,656827257680552,655990963616184,655134924262495,
  654259224279763,653363947002191,652449174454069,651514987365368,650561465186787,649588686104245,
  648596727052856]
private def phbn_r384_5_p3 : List ℕ := [647585663730356,646555570610032,645506520953125,
  644438586820739,643351839085250,642246347441222,641122180415839,639979405378858,638818088552083,
  637638295018374,636440088730179,635223532517610,633988688096054,632735616073321,631464375956348,
  630175026157427,628867624000000,627542225723982,626198886490644,624837660387034,623458600429944,
  622061758569426,620647185691842,619214931622465,617765045127606,616297573916284,614812564641423,
  613310062900576,611790113236172,610252759135278,608698043028872,607126006290624,605536689235167,
  603930131115869,602306370122073,600665443375824,599007386928049,597332235754198,595640023749318,
  593930783722568,592204547391147,590461345373626,588701207182675,586924161217160,585130234753611,
  583319453937017,581491843770966,579647428107072,577786229633707,575908269863986,574013569122997,
  572102146534262,570174020005375,568229206212826,566267720585954,564289577290017,562294789208347,
  560283367923541,558255323697682,556210665451526,554149400742633,552071535742398,549977075211937,
  547866022476790]
private def phbn_r384_5_p4 : List ℕ := [545738379400377,543594146356183,541433322198596,
  539255904232351,537061888180522,534851268151005,532624036601408,530380184302302,528119700298741,
  525842571869984,523548784487331,521238321769991,518911165438884,516567295268283,514206689035197,
  511829322466375,509435169182823,507024200641711,504596386075533,502151692428389,499690084289235,
  497211523821952,494715970692060,492203381989901,489673712150114,487126912867184,484562933006863,
  481981718513234,479383212311174,476767354203955,474134080765711,471483325228469,468815017363439,
  466129083356216,463425445675528,460704022935167,457964729748653,455207476576220,452432169563616,
  449638710372234,446826996000000,443996918592426,441148365243213,438281217783686,435395352560336,
  432490640199672,429566945359506,426624126465742,423662035433673,420680517372659,417679410273035,
  414658544673936,411617743310650,408556820739985,405475582941981,402373826896176,399251340130456,
  396107900240336,392943274376342,389757218696895,386549477783918,383319784018043,380067856910044,
  376793402384755]
private def phbn_r384_5_p5 : List ℕ := [373496112013358,370175662189500,366831713244228,
  363463908494192,360071873216957,356655213546603,353213515282024,349746342599463,346253236659844,
  342733714100367,339187265398540,335613353095400,332011409863008,328380836399432,324720999132237,
  321031227709022,317310812250637,313559000339371,309774993710529,305957944611270,302106951785303,
  298221056035815,294299235311746,290340399253856,286343383126875,282306941051830,278229738438177,
  274110343497918,269947217702921,265738705021262,261483019737479,257178232623808,252822255182960,
  248412821625421,243947468172596,239423509187263,234838009519478,230187752311884,225469201323642,
  220678456593384,215811201950095,210862642470489,205827429435226,200699569600854,195472314601835,
  190138024911909,184688000852177,179112270366693,173399319274358,167535743772690,161505796000891,
  155290779578332,148868229914776,142210777740704,135284532379035,128046711243008,120442036594458,
  112397013544052,103810336094005,94535644357049,84347539215884,72865328032368,59344302358926,
  41855586812044]
private def phbn_r384_5 : List ℕ := pCat phbn_r384_5_p0 (pCat phbn_r384_5_p1 (pCat phbn_r384_5_p2
  (pCat phbn_r384_5_p3 (pCat phbn_r384_5_p4 phbn_r384_5_p5))))
private def phbv_r384_5 : List ℤ := uOh phbn_r384_5
private def pvn_r384_5_0_p0 : List ℕ := [1999907084406140,2000119625340645,1999957638418096,
  1999931043890861,2000084609203361,2000012142668781,1999913027605217,2000034731538969,
  2000066683395255,1999933842850054,1999965327055377,2000080826393907,1999999063814515,
  1999920151817178,2000034004528447,2000065882161664,1999939849644128,1999957513261404,
  2000076510001500,2000013957596154,1999917555816283,2000017016573981,2000075061610402,
  1999959629206405,1999931583394132,2000077649405733,2000019223659822,1999953598690359,
  1999934611832447,2000162432556685,1999878210252221,2000055430449961,1999880573713555,
  2000241714421756,1999772379804740,2000075478252088,2000022955199994,2000000804711534,
  2000007680892882,1999863174484951,2000224159728309,1999893669240907,1999899518764617,
  2000162732174295,1999925308248964,2000022200228465,1999953153825559,1999996965216695,
  2000152926835098,1999810213247926,1999996568405425,2000210929917754,1999827240627492,
  1999963358197973,2000140086581033,1999929079471848,2000002820431011,1999992363362688,
  1999967765360493,2000128343617092,1999906056875781,1999884436628296,2000227096908905,
  1999964068619993]
private def pvn_r384_5_0_p1 : List ℕ := [1999773594810386,2000191303700496,2000094184345175,
  1999769271603811,2000057422907763,2000147446812746,1999877530468802,1999973455069350,
  2000078843330283,1999961652498697,2000016762090451,2000009650067001,1999915590576573,
  2000084347142538,2000074086247500,1999818822773605,2000013881354516,2000224799090929,
  1999859409621378,1999809270030085,2000255031543091,2000089174761526,1999682345806536,
  2000047203001752,2000312002061302,1999819846527149,1999755742434182,2000279196433667,
  2000135425627898,1999671902891054,1999988378341779,2000325003717708,1999896247917080,
  1999721316356103,2000194406289430,2000203462046071,1999747684242107,1999885292953515,
  2000276645628281,2000025739227140,1999728382899402,2000053717408710,2000244222712051,
  1999882145880333,1999797673095096,2000164318070593,2000153359132659,1999806611099397,
  1999896411362553,2000207088722645,2000057862376211,1999791605726510,1999980341765268,
  2000200606799815,1999991296088645,1999813121525298,2000025889811803,2000170059119526,
  1999968611463985,1999846696880960,2000023965954105,2000139822342797,2000002540871676,
  1999876375823348]
private def pvn_r384_5_0_p2 : List ℕ := [1999948128172674,2000077718870083,2000077261646176,
  1999974184939714,1999997672758578,2000195884262360,2000116689728189,1999447587813190,
  1998941779415966,1999674467441344,2001304300964189,2002342262569138,2002087695983480,
  2000755849369899,1998188870567813,1994810399070609,1993308901271596,1996008756281971,
  2000501339842505,2001682413055612,1998813788906252,1996646465760405,1998341677780626,
  2001249259379357,2001605739552467,1999850021281380,1998817826177781,1999363026073503,
  2000247988565321,2000582964275097,2000382018315384,1999868357261001,1999485621741360,
  1999691901750980,2000213038460941,2000394570928416,2000212915830452,1999966053043029,
  1999594246138785,1999385913518599,2000119789618167,2001212446179426,2000661885537831,
  1998605231621992,1998300488529256,2000937937968512,2002578779980269,2000105440455266,
  1997107445025963,1998610907474134,2002456755903576,2002414384128092,1998555550807277,
  1997205784960942,2000324527214632,2002498272174858,2000412615813413,1998109155927702,
  1999407150493880,2001469618555151,2000491364059933,1998546923768641,1999417616257286,
  2001573302086297]
private def pvn_r384_5_0_p3 : List ℕ := [2001055457753752,1998654014092619,1998434002374143,
  2000637278702891,2001579971375887,2000090387974269,1998962210901568,1999729433009799,
  2000518957169566,1999978961571613,1999475773113811,2000115253982772,2000737259510499,
  2000262638275743,1999525972660803,1999517551803117,1999859589031681,2000027526547469,
  2000255680290411,2000487294039422,2000177145233274,1999637271214247,1999776113706130,
  2000244425575536,1999894030672912,1999201704812840,1999750306474236,2001068795455145,
  2000938651449584,1999405977962302,1999124278701344,2000635566540654,2001040015298324,
  1999168396636636,1998138637524719,2000006270907099,2001735392393956,2000292770829946,
  1998264711999914,1999549791996876,2002241315498309,2001637220867470,1998626790888756,
  1998473523747189,2001575356608296,2002480494919447,1999380487441865,1997521689157676,
  2000168233058779,2002754205222443,2000702636431758,1997459437105549,1998613733349113,
  2002193155014905,2002032180195800,1998413705484309,1997546470772439,2000853894260636,
  2002635546998551,1999911731588978,1997490189139640,1999287483437993,2002417149776388,
  2000792419091852]
private def pvn_r384_5_0_p4 : List ℕ := [1998888232841640,1997606571113625,2002009304039342,
  2001650921344276,1998268646890271,1999278935727031,2000845113903206,2000090122538565,
  1999996787217446,2000612532510326,1999519484718526,1998283565054867,1999965768596068,
  2002639397989693,2001898734826196,1998556741985422,1997873357497834,2000982510376878,
  2002789282471177,2000168836144353,1997163779406319,1998579181903872,2002248612915867,
  2002430443927754,1998876517865382,1997143367527996,1999819809262425,2002619260969960,
  2001260097737337,1998065007970926,1998074526696589,2001117566473939,2002274898447559,
  1999716724513728,1997533666078375,1999280720909767,2002372241025419,2001977148864671,
  1998435488006411,1996926677021196,1999843065110457,2003169202499855,2002181849033659,
  1998188251279649,1996675999666341,1999639674705003,2002926721812249,2002103656167431,
  1998491603809494,1997151829195060,1999880400169295,2002849031585762,2001884841625956,
  1998111844356281,1996492833887713,1999345443434202,2003302026241901,2003499466173324,
  1999595176256781,1996173745910127,1997226658229013,2001461708824452,2003882932652195,
  2001573655933278]
private def pvn_r384_5_0_p5 : List ℕ := [2003005425656007,2004725484029146,2001304139274679,
  1995715387327572,1993255870200215,1996519752313572,2003140394311964,2007955332889484,
  2007122676896877,2000626455009491,1991809995630084,1985239417102986,1984827301096740,
  1992846574402766,2009174710947266,2030251126529536,2048397226102815,2052833904673683,
  2032997028728677,1983094337643588,1905637631644384,1811921120603701,1718962191756676,
  1644230028905568,1600461121431440,1592568461172311,1617462005914016,1666283337162062,
  1727762558681904,1791344440620046,1849210359518131,1896970265999711,1933300331289031,
  1959020918302701,1976077327705520,1986718540291998,1992983615315207,1996472023114139,
  1998311631458880,1999231246347483,1999667198723103,1999863169002255,1999946655228976,
  1999980324438955,1999993155981810,1999997765038236,1999999319425971,1999999808786020,
  1999999951329004,1999999989176239,1999999998082690,1999999999824178,2000000000050061,
  2000000000036965,2000000000014512,2000000000004485,2000000000001180,2000000000000266,
  2000000000000049,2000000000000006]
private def pvn_r384_5_0 : List ℕ := pCat pvn_r384_5_0_p0 (pCat pvn_r384_5_0_p1 (pCat
  pvn_r384_5_0_p2 (pCat pvn_r384_5_0_p3 (pCat pvn_r384_5_0_p4 pvn_r384_5_0_p5))))
private def pvn_r384_5_1_p0 : List ℕ := [1999860063415902,1999991252387977,2000102675667439,
  2000007474349765,1999907574019774,1999995557467532,2000087650316294,2000000251399341,
  1999915065952583,2000004887532204,2000083039163455,1999989176272825,1999918592921560,
  2000017665609459,2000079078891161,1999976033164106,1999921157315961,2000036401345698,
  2000066236500860,1999973418384240,1999905694736377,2000089640705672,2000001080326119,
  2000034670815448,1999818915086601,2000217133147777,1999879805486468,2000094895432243,
  1999824291037260,2000151600989562,2000038338649684,1999829358451217,2000117888409897,
  1999952950398581,2000081781574696,1999928913113939,1999903139527607,2000225372778617,
  1999886670637529,1999906553456096,2000136602839917,1999950791914424,2000025108708358,
  1999960860071590,1999939181715114,2000183635935984,1999907881374567,1999847703072862,
  2000216053825774,1999988551043675,1999835039283150,2000106993703165,2000025699978311,
  1999952865328573,2000032969391723,1999926516484895,2000045312722286,2000114169065464,
  1999824742822639,1999971206542264,2000237012276920,1999884494692253,1999818070341891,
  2000215908390173]
private def pvn_r384_5_1_p1 : List ℕ := [2000053459675999,1999783968465282,2000063599138411,
  2000132818799177,1999893378074861,1999970764051843,2000066884656059,1999967868244410,
  2000018294663725,2000021776893533,1999904876463514,2000050191808472,2000122143826566,
  1999852218259152,1999914985933606,2000229815823681,1999995745404052,1999733555317064,
  2000117790418746,2000246520178606,1999775345151187,1999823555510748,2000300635366751,
  2000073981097144,1999667047865610,2000039180847846,2000320334790871,1999856524809640,
  1999729821650336,2000224996103057,2000194629986861,1999723419342384,1999893023865972,
  2000297123700619,2000019043357533,1999710035205641,2000060224086540,2000261048429709,
  1999874812441972,1999782691651516,2000173256285196,2000165484836329,1999795731481800,
  1999888593133575,2000219761905549,2000059669583824,1999777706521354,1999986402028288,
  2000214889318403,1999975387954399,1999799354454832,2000053663217177,2000182466595428,
  1999927100891790,1999837090664551,2000082057328762,2000144097591832,1999918944562547,
  1999872320641601,2000069811846140,2000114808237056,1999951939619768,1999893927086864,
  2000015109397184]
private def pvn_r384_5_1_p2 : List ℕ := [2000101069651405,2000030053590112,1999902553159687,
  1999913274301953,2000092053620920,2000148965590632,1999908822287006,1999783981932972,
  2000118756970200,2000337880203126,1999851523406711,1999397474957739,1999953625237489,
  2000809188102212,2000616828753267,1999761340406801,1999447719918742,1999280469103868,
  1998539284213661,1998849350230896,2001906695708554,2005133240498479,2003918276284988,
  1998505565133895,1994430825667701,1995149924719402,1998057466066871,1999134451251073,
  1998109447759884,1997279514962802,1997843619641422,1999187510853067,2000219282266777,
  2000267288381437,1999586805797503,1999234514465764,1999705519899757,2000235040022726,
  2000221887900307,2000143933135149,2000177492693048,1999696086307889,1999143300721042,
  1999961661968418,2001438684537950,2000840093224090,1998393922324122,1998133221737222,
  2001172135280493,2002741224657187,1999804702054567,1996894047933824,1998978813502171,
  2002792599096582,2002044366604824,1998071082854617,1997480638207218,2000900223789165,
  2002370162571183,1999852092236058,1998140928395056,1999897684846012,2001422686703867,
  1999997685916632]
private def pvn_r384_5_1_p3 : List ℕ := [1998646949807213,2000056773957611,2001554578728898,
  2000246559431782,1998380361422256,1999197462860455,2001228037194765,2001154646685362,
  1999476049634407,1999037153350334,2000028784760640,2000427016798560,1999926963326079,
  1999884981152569,2000362994198845,2000267689175495,1999678404450297,1999562137408658,
  1999905312409200,2000100575770878,2000257110246852,2000494235323717,2000186930380843,
  1999379990061191,1999340848849106,2000286706073777,2000582998449587,1999708105253443,
  1999512118059923,2000704121857969,2001041052247733,1999399518445775,1998414878737330,
  1999975180851904,2001425314352479,2000133848455345,1998548597052721,1999925973370415,
  2002032066989800,2000840809112712,1998102510860901,1998605690378891,2001437195643431,
  2001330852327001,1998281017277082,1997885394362810,2001217540733009,2002540405101562,
  1999551275400142,1997690221472891,2000541642536553,2003004389702529,2000827789938670,
  1997386472629847,1999496163908539,2002157753328097,2002277996709974,1997387110425376,
  1998515506208843,2001522023842649,2001959830305225,1999658524121758,1997117683468098,
  2000288335171499]
private def pvn_r384_5_1_p4 : List ℕ := [2003120542186507,1999483930465280,1997438113914762,
  2000549363297063,2001705681168227,1999620950378074,1999143779922196,2000176306145484,
  2000097700016791,1999923149335796,2000602805177781,2000208040913695,1998742909177662,
  1999262095247139,2001688080002907,2001759210934586,1998573353254350,1997125896587477,
  2000147185894074,2003028800730403,2001210846018913,1997867033222592,1998675997013372,
  2002297782057528,2002595157223822,1998897074631229,1997138529291065,2000063120059671,
  2002803960010439,2000969454077413,1997707369819788,1998314833650477,2001596020573421,
  2002083801627581,1999095650153402,1997687580474363,2000219571356711,2002488378107935,
  2000637709154547,1997523082142938,1998231026139121,2001906745804753,2002891306068659,
  1999467417838540,1996644736966285,1998670593081990,2002649322398872,2002825955778372,
  1999022185611044,1996766996851501,1999182429964638,2002605453982011,2002087400220732,
  1998482714430220,1997171381651108,1999977606735476,2003375244858839,2001573361641097,
  1998313008036442,1995818001357760,1999278424254848,2004578489273289,2002557037923370,
  1997961623024434]
private def pvn_r384_5_1_p5 : List ℕ := [1997860473424369,1999627070710299,1999489586211632,
  1999474541717910,2002313374825495,2005923617267221,2005747025248973,2000630950799727,
  1994614677239344,1993006468738647,1997386743585787,2004411021411160,2008808708861065,
  2007239365725518,1999973433437225,1990199606738016,1982585124427643,1982078388491388,
  1992451238240884,2013947470717649,2040874621877461,2061271467662037,2060199300898062,
  2025892517182590,1955780668239781,1859047941523440,1754209183630467,1662864236751497,
  1602616054177186,1582171313768003,1600183833999279,1647518298491664,1711329534227362,
  1779102817382892,1841379110859099,1892771733983506,1931594038157231,1958741773095404,
  1976441642209069,1987253060553589,1993460486769222,1996818214033210,1998531920386925,
  1999357896077373,1999733983433151,1999895730485150,1999961394964667,1999986528832422,
  1999995582858814,1999998644550776,1999999612950847,1999999897997751,1999999975505449,
  1999999994755929,1999999999041848,1999999999867030,1999999999992920,2000000000003419,
  2000000000001608,2000000000000441,2000000000000087,2000000000000010]
private def pvn_r384_5_1 : List ℕ := pCat pvn_r384_5_1_p0 (pCat pvn_r384_5_1_p1 (pCat
  pvn_r384_5_1_p2 (pCat pvn_r384_5_1_p3 (pCat pvn_r384_5_1_p4 pvn_r384_5_1_p5))))
private def pvi_r384_5 : List ℤ := bDc bZ (rPad bZ 385 pvn_r384_5_0)
private def pvo_r384_5 : List ℤ := bDc bZ (rPad bZ 385 pvn_r384_5_1)
private def phbn_r384_6_p0 : List ℕ := [90942189519885,128318610517510,156798610665071,
  180640941466221,201499266703723,220223683891126,237320356316520,253119830523168,267852225279697,
  281685466197498,294746607848165,307134579452813,318928229285127,330191628983755,340977699474218,
  351330765651649,361288403232036,370882803839090,380141803685445,389089672032121,397747724691344,
  406134807852679,414267684274689,422161344922244,429829262942092,437283602520998,444535392065506,
  451594668892017,458470600963017,465171589976222,471705359188992,478079028657705,484299180032464,
  490371912629750,496302892179258,502097393384196,507760337230428,513296323816987,518709661349494,
  524004391832026,529184313906739,534253003219882,539213830634823,544069978564588,548824455656554,
  553480110028609,558039641228157,562505611061877,566880453424259,571166483236123,575365904589983,
  579480818186900,583513228138936,587465048202372,591338107499012,595134155776236,598854868250588,
  602501850074668,606076640462635,609580716505807,613015496706446,616382344254848,619682570072262,
  622917435639837]
private def phbn_r384_6_p1 : List ℕ := [626088155631791,629195900369163,632241798108934,
  635226937181871,638152367991192,641019104883006,643828127898485,646580384416830,649276790697255,
  651918233327524,654505570585880,657039633722661,659521228167324,661951134666151,664330110355456,
  666658889774729,668938185823790,671168690667718,673351076592986,675485996818027,677574086261145,
  679615962268511,681612225304758,683563459608508,685470233814988,687333101547746,689152601981331,
  690929260376656,692663588590668,694356085561812,696007237772690,697617519691212,699187394191460,
  700717312955391,702207716856438,703659036326005,705071691703782,706446093572736,707782643079608,
  709081732241664,710343744240422,711569053703029,712758026971901,713911022363249,715028390415014,
  716110474124761,717157609178017,718170124167512,719148340803769,720092574117461,721003132653905,
  721880318660088,722724428264552,723535751650477,724314573222268,725061171765946,725775820603612,
  726458787742259,727110336017168,727730723230140,728320202282771,728879021305003,729407423779128,
  729905648659461]
private def phbn_r384_6_p2 : List ℕ := [730373930487847,730812499505184,731221581759119,
  731601399208080,731952169821793,732274107678410,732567423058411,732832322535375,733069009063772,
  733277682063872,733458537503884,733611767979450,733737562790561,733836108016024,733907586585553,
  733952178349572,733970060146827,733961405869865,733926386528481,733865170311188,733777922644779,
  733664806252069,733525981207851,733361604993149,733171832547813,732956816321530,732716706323273,
  732451650169273,732161793129541,731847278172996,731508246011239,731144835141022,730757181885444,
  730345420433925,729909682880983,729450099263868,728966797599060,728459903917696,727929542299935,
  727375834908300,726798902020025,726198862058440,725575831623406,724929925520849,724261256791392,
  723569936738131,722856074953560,722119779345680,721361156163305,720580310020584,719777343920766,
  718952359279215,718105455945704,717236732225994,716346284902720,715434209255598,714500599080967,
  713545546710676,712569143030337,711571477496948,710552638155904,709512711657404,708451783272260,
  707369936907132]
private def phbn_r384_6_p3 : List ℕ := [706267255119181,705143819130160,703999708839949,
  702835002839536,701649778423465,700444111601740,699218077111199,697971748426376,696705197769826,
  695418496121954,694111713230321,692784917618448,691438176594120,690071556257185,688685121506853,
  687278936048505,685853062400000,684407561897486,682942494700726,681457919797916,679953895010017,
  678430476994583,676887721249093,675325682113783,673744412773972,672143965261875,670524390457916,
  668885738091514,667228056741352,665551393835119,663855795648718,662141307304931,660407972771542,
  658655834858899,656884935216909,655095314331466,653287011520288,651460064928156,649614511521551,
  647750387082664,645867726202779,643966562274997,642046927486307,640108852808967,638152367991192,
  636177501547129,634184280746085,632172731601014,630142878856215,628094745974234,626028355121939,
  623943727155744,621840881605960,619719836660232,617580609146042,615423214512248,613247666809616,
  611053978670313,608842161286329,606612224386783,604364176214070,602098023498813,599813771433561,
  597511423645199]
private def phbn_r384_6_p4 : List ℕ := [595190982166004,592852447403306,590495818107680,
  588121091339628,585728262434667,583317324966773,580888270710093,578441089598866,575975769685452,
  573492297096409,570990655986503,568470828490584,565932794673194,563376532475834,560802017661755,
  558209223758163,555598121995705,552968681245116,550320867950863,547654646061654,544969976957640,
  542266819374146,539545129321744,536804860002478,534045961722036,531268381797655,528472064461507,
  525656950759348,522822978444138,519970081864364,517098191846766,514207235573127,511297136450809,
  508367813976643,505419183593789,502451156541148,499463639694866,496456535401442,493429741301934,
  490383150146689,487316649600000,484230122034043,481123444311408,477996487555451,474849116907685,
  471681191271316,468492563039993,465283077810751,462052574080045,458800882921673,455527827645309,
  452233223434231,448916876960717,445578585977462,442218138883204,438835314260589,435429880384138,
  432001594695974,428550203246745,425075440098936,421577026689517,418054671148536,414508067569970,
  410936895230752]
private def phbn_r384_6_p5 : List ℕ := [407340817753491,403719482207938,400072518145715,
  396399536562269,392700128779335,388973865240459,385220294211307,381438940375537,377629303315933,
  373790855869315,369923042342326,366025276573647,362096939826378,358137378492272,354145901587124,
  350121778013913,346064233567113,341972447647965,337845549656261,333682615019229,329482660812380,
  325244640920369,320967440678007,316649870922113,312290661373821,307888453257650,303441791047864,
  298949113213631,294408741811628,289818870747022,285177552490045,280482682994122,275731984510793,
  270922985933873,266053000227122,261119098391745,256118079306392,251046434615115,245900307637243,
  240675445012698,235367139456519,229970161548882,224478677891152,218886152156416,213185224469569,
  207367563041408,201423679863347,195342699252097,189112063658080,182717154680492,176140797451136,
  169362601399054,162358066283782,155097342743387,147543469064824,139649785876504,131356006395396,
  122581975922809,113217208521529,103102081763776,91990771776666,79468089096252,64721842810055,
  45648370655490]
private def phbn_r384_6 : List ℕ := pCat phbn_r384_6_p0 (pCat phbn_r384_6_p1 (pCat phbn_r384_6_p2
  (pCat phbn_r384_6_p3 (pCat phbn_r384_6_p4 phbn_r384_6_p5))))
private def phbv_r384_6 : List ℤ := uOh phbn_r384_6
private def pvn_r384_6_0_p0 : List ℕ := [2000139936584098,2000008747612023,1999897324332561,
  1999992525650235,2000092425980226,2000004442532468,1999912349683706,1999999748600659,
  2000084934047417,1999995112467796,1999916960836545,2000010823727175,2000081407078440,
  1999982334390541,1999920921108839,2000023966835894,2000078842684039,1999963598654302,
  1999933763499140,2000026581615760,2000094305263623,1999910359294328,1999998919673881,
  1999965329184552,2000181084913399,1999782866852223,2000120194513532,1999905104567757,
  2000175708962740,1999848399010438,1999961661350316,2000170641548783,1999882111590103,
  2000047049601419,1999918218425304,2000071086886061,2000096860472393,1999774627221383,
  2000113329362471,2000093446543904,1999863397160083,2000049208085576,1999974891291642,
  2000039139928410,2000060818284886,1999816364064016,2000092118625433,2000152296927138,
  1999783946174226,2000011448956325,2000164960716850,1999893006296835,1999974300021689,
  2000047134671427,1999967030608277,2000073483515105,1999954687277714,1999885830934536,
  2000175257177361,2000028793457736,1999762987723080,2000115505307747,2000181929658109,
  1999784091609827]
private def pvn_r384_6_0_p1 : List ℕ := [1999946540324001,2000216031534718,1999936400861589,
  1999867181200823,2000106621925139,2000029235948157,1999933115343941,2000032131755590,
  1999981705336275,1999978223106467,2000095123536486,1999949808191528,1999877856173434,
  2000147781740848,2000085014066394,1999770184176319,2000004254595948,2000266444682936,
  1999882209581254,1999753479821394,2000224654848813,2000176444489252,1999699364633249,
  1999926018902856,2000332952134390,1999960819152154,1999679665209129,2000143475190360,
  2000270178349664,1999775003896943,1999805370013139,2000276580657616,2000106976134028,
  1999702876299381,1999980956642467,2000289964794359,1999939775913460,1999738951570291,
  2000125187558028,2000217308348484,1999826743714804,1999834515163671,2000204268518200,
  2000111406866425,1999780238094451,1999940330416176,2000222293478646,2000013597971712,
  1999785110681597,2000024612045601,2000200645545168,1999946336782823,1999817533404572,
  2000072899108210,2000162909335449,1999917942671238,1999855902408168,2000081055437453,
  2000127679358399,1999930188153860,1999885191762944,2000048060380232,2000106072913136,
  1999984890602816]
private def pvn_r384_6_0_p2 : List ℕ := [1999898930348595,1999969946409888,2000097446840313,
  2000086725698047,1999907946379080,1999851034409368,2000091177712994,2000216018067028,
  1999881243029800,1999662119796874,2000148476593289,2000602525042261,2000046374762511,
  1999190811897788,1999383171246733,2000238659593199,2000552280081258,2000719530896132,
  2001460715786339,2001150649769104,1998093304291446,1994866759501521,1996081723715012,
  2001494434866105,2005569174332299,2004850075280598,2001942533933129,2000865548748927,
  2001890552240116,2002720485037198,2002156380358578,2000812489146933,1999780717733223,
  1999732711618563,2000413194202497,2000765485534236,2000294480100243,1999764959977274,
  1999778112099693,1999856066864851,1999822507306952,2000303913692111,2000856699278958,
  2000038338031582,1998561315462050,1999159906775910,2001606077675878,2001866778262778,
  1998827864719507,1997258775342813,2000195297945433,2003105952066176,2001021186497829,
  1997207400903418,1997955633395176,2001928917145383,2002519361792782,1999099776210835,
  1997629837428817,2000147907763942,2001859071604944,2000102315153988,1998577313296133,
  2000002314083368]
private def pvn_r384_6_0_p3 : List ℕ := [2001353050192787,1999943226042389,1998445421271102,
  1999753440568218,2001619638577744,2000802537139545,1998771962805235,1998845353314638,
  2000523950365593,2000962846649666,1999971215239360,1999572983201440,2000073036673921,
  2000115018847431,1999637005801155,1999732310824505,2000321595549703,2000437862591342,
  2000094687590800,1999899424229122,1999742889753148,1999505764676283,1999813069619157,
  2000620009938809,2000659151150894,1999713293926223,1999417001550413,2000291894746557,
  2000487881940077,1999295878142031,1998958947752267,2000600481554225,2001585121262670,
  2000024819148096,1998574685647521,1999866151544655,2001451402947279,2000074026629585,
  1997967933010200,1999159190887288,2001897489139099,2001394309621109,1998562804356569,
  1998669147672999,2001718982722918,2002114605637190,1998782459266991,1997459594898438,
  2000448724599858,2002309778527109,1999458357463447,1996995610297471,1999172210061330,
  2002613527370153,2000503836091461,1997842246671903,1997722003290026,2002612889574624,
  2001484493791157,1998477976157351,1998040169694775,2000341475878242,2002882316531902,
  1999711664828501]
private def pvn_r384_6_0_p4 : List ℕ := [1996879457813493,2000516069534720,2002561886085238,
  1999450636702937,1998294318831773,2000379049621926,2000856220077804,1999823693854516,
  1999902299983209,2000076850664204,1999397194822219,1999791959086305,2001257090822338,
  2000737904752861,1998311919997093,1998240789065414,2001426646745650,2002874103412523,
  1999852814105926,1996971199269597,1998789153981087,2002132966777408,2001324002986628,
  1997702217942472,1997404842776178,2001102925368771,2002861470708935,1999936879940329,
  1997196039989561,1999030545922587,2002292630180212,2001685166349523,1998403979426579,
  1997916198372419,2000904349846598,2002312419525637,1999780428643289,1997511621892065,
  1999362290845453,2002476917857062,2001768973860879,1998093254195247,1997108693931341,
  2000532582161460,2003355263033715,2001329406918010,1997350677601128,1997174044221628,
  2000977814388956,2003233003148499,2000817570035362,1997394546017989,1997912599779268,
  2001517285569780,2002828618348892,2000022393264524,1996624755141161,1998426638358903,
  2001686991963558,2004181998642240,2000721575745152,1995421510726711,1997442962076630,
  2002038376975566]
private def pvn_r384_6_0_p5 : List ℕ := [2002139526575631,2000372929289701,2000510413788368,
  2000525458282090,1997686625174505,1994076382732779,1994252974751027,1999369049200273,
  2005385322760656,2006993531261353,2002613256414213,1995588978588840,1991191291138935,
  1992760634274482,2000026566562775,2009800393261984,2017414875572357,2017921611508612,
  2007548761759116,1986052529282351,1959125378122539,1938728532337963,1939800699101938,
  1974107482817410,1955780668239781,1859047941523440,1754209183630467,1662864236751497,
  1602616054177186,1582171313768003,1600183833999279,1647518298491664,1711329534227362,
  1779102817382892,1841379110859099,1892771733983506,1931594038157231,1958741773095404,
  1976441642209069,1987253060553589,1993460486769222,1996818214033210,1998531920386925,
  1999357896077373,1999733983433151,1999895730485150,1999961394964667,1999986528832422,
  1999995582858814,1999998644550776,1999999612950847,1999999897997751,1999999975505449,
  1999999994755929,1999999999041848,1999999999867030,1999999999992920,2000000000003419,
  2000000000001608,2000000000000441,2000000000000087,2000000000000010]
private def pvn_r384_6_0 : List ℕ := pCat pvn_r384_6_0_p0 (pCat pvn_r384_6_0_p1 (pCat
  pvn_r384_6_0_p2 (pCat pvn_r384_6_0_p3 (pCat pvn_r384_6_0_p4 pvn_r384_6_0_p5))))
private def pvn_r384_6_1_p0 : List ℕ := [2000110031879794,2000109800805049,1999993576266107,
  1999903386133959,1999963083924448,2000075735327133,2000059958886820,1999944764581738,
  1999927591174858,2000037014812553,2000079113571187,1999977607820366,1999919658500868,
  2000005959928627,2000089314235320,1999988189282693,1999940938131393,1999950813180013,
  2000145255481252,1999922563246298,2000044714448873,1999824150382378,2000251931029941,
  1999861585352717,2000041497577874,1999921619611623,2000047322563973,2000135770679230,
  1999776829019004,2000087747680992,2000045638791189,1999966900659788,2000042769394826,
  1999852279867273,2000128964118534,2000086958974876,1999784033860513,2000084433208008,
  2000083510410825,1999918555703094,2000035907333687,1999932760037990,2000029862084386,
  2000136624621726,1999821391116361,1999960189361239,2000224525075784,1999897340811286,
  1999872461288806,2000142031383988,2000001064061613,1999943253422285,2000032499501818,
  1999943257902950,2000047283418122,2000093163597218,1999834986970008,1999976438050039,
  2000228056508252,1999899380089205,1999804811726926,2000200046926729,2000091656836904,
  1999777110495731]
private def pvn_r384_6_1_p1 : List ℕ := [2000020840264796,2000168206776206,1999913663694373,
  1999925181341491,2000081680121336,1999993238815023,1999980165863698,2000039770741647,
  1999935927478577,1999986718151144,2000131875098479,1999940371053845,1999842951660620,
  2000152082989047,2000130865632314,1999764705863962,1999939168986635,2000287474065743,
  1999964632014052,1999702044312296,2000136920192116,2000267013427179,1999774439843358,
  1999797014871648,2000288821709958,2000118431022228,1999679060133220,1999973377298046,
  2000322058386922,1999939042993386,1999703447877268,2000135946093507,2000251147695434,
  1999806558345813,1999806712453837,2000231660880087,2000129945847659,1999748752514702,
  1999933072444635,2000254479459399,2000008577682469,1999755455902440,2000042214438361,
  2000224963975892,1999916168164488,1999800803427071,2000115662148207,2000170392676305,
  1999862188557343,1999858719455390,2000150838563037,2000114137955464,1999844472244022,
  1999909183002910,2000152702969201,2000072792385740,1999856920812177,1999938789454550,
  2000127142988473,2000056922482438,1999894946444620,1999939513357514,2000076553636549,
  2000072119231626]
private def pvn_r384_6_1_p2 : List ℕ := [1999959113020037,1999908463865121,1999996794594185,
  2000117642673366,2000057127588409,1999851565902155,1999878459013649,2000182472796948,
  2000197009201523,1999777970616231,1999707712616367,2000266595378906,2000435988577788,
  1999725989131967,1999362677942574,2000132419510030,2000739186238901,2000141473183774,
  1999564407886949,2000016519994180,2000076609155452,1998853078676026,1998687664843973,
  2001412811701832,2004033578325656,2002283023271556,1997251034102851,1994391492582731,
  1996379716072885,2000487261094774,2002960147907514,2002991922962246,2002106502562661,
  2001850438392063,2002519826260868,2003072962422624,2002416928878224,2001044682377921,
  2000383169790374,2000549741084691,2000503070260544,2000249077521995,2000531052329657,
  2000638448360036,1999533709453968,1998718882727872,2000189587766060,2002000761083062,
  2000655093190306,1997735557256995,1998280215814853,2001956539902668,2002686443828690,
  1998902085281202,1996797776329584,1999961183262020,2003092188776745,2001058894047761,
  1997554850383332,1998378411123526,2001592483923793,2001626017940363,1999063048000993,
  1998721704329741]
private def pvn_r384_6_1_p3 : List ℕ := [2000710764561059,2000965146662327,1999182767928432,
  1999021451961541,2000900805709498,2001277847835953,1999357263509031,1998492690516962,
  2000068195051769,2001315511469886,2000434124115687,1999273101832690,1999526671822893,
  2000173572393809,2000089547166000,1999937584778479,2000241531811003,2000291243065184,
  1999849959345905,1999665637180154,1999870713445608,1999925776900112,2000024234982957,
  2000510413141114,2000548971871006,1999582977778331,1999021155849261,1999985646644917,
  2000879590653804,2000085578725361,1999215368791712,2000198259425748,2001247703079795,
  1999954605325352,1998269520011284,1999379126955709,2001551848914445,2000897817675147,
  1998667718585374,1999212985070492,2001701304632234,2001295181697561,1998241468388796,
  1998011118538171,2001068968079530,2002035928662035,1998858803493535,1998065337698190,
  2000689920597100,2003283324263193,1999383255327967,1997940381889633,1999362778921610,
  2002763795572500,2000563799533939,1996592262786026,1999067827710297,2001818783071298,
  2001032313724202,1998247449000406,1997428076566178,2001375701721788,2002684016578972,
  1998171060025467]
private def pvn_r384_6_1_p4 : List ℕ := [1997363827045045,2001632781367003,2001957553859134,
  1998664261602557,1998666417952454,2000818242922821,2000699506396319,1999651614340958,
  1999858867874562,1999963142070063,1999590553258016,2000274092233077,2000999482674438,
  1999703259716958,1998344976858938,1999966286992553,2002263059859473,2000851624629758,
  1997521137505717,1997971402019957,2001885599796404,2002910929168560,1999349531356026,
  1997168801197957,1999856855534877,2002520674923724,2000379090172556,1996982236503734,
  1998103485501221,2001912946790998,2002160459116711,1998702413955288,1997501424939474,
  2000462388573782,2002450891696005,2000181474769097,1997670037954687,1999244153288483,
  2002192949030144,2001408024141065,1998067016475677,1997783016219957,2001275851988671,
  2002976652734561,1999956529858305,1996784092135431,1998449293593237,2002541771020587,
  2002860296037192,1999002211030811,1996619781126876,1999450651684655,2002563798345869,
  2002284845311888,1997849922726349,1997591938749304,2000626541861077,2002592162206294,
  2001665223047880,1996992937076932,1996289022616440,2002095474403584,2004509935694612,
  2000140987706618]
private def pvn_r384_6_1_p5 : List ℕ := [1996890324180285,1998471965606590,2000495112038257,
  2000365985959451,2000491354476922,2002065727296865,2002194807933419,1998582142558893,
  1993829317583159,1993030627179924,1997894281380829,2004563438021315,2007314957658713,
  2003802787748625,1996725087087341,1991257596572064,1991248224469973,1997933480060153,
  2007564678249737,2020376960899466,2017257507585674,2016744990002575,1991695765612266,
  1937872103303297,1938778646709629,1978312562582065,1987338702492586,1937246990344301,
  1843025214040121,1735550357973998,1644131459972173,1588742324629137,1577007992142575,
  1604952715801969,1660793001966187,1729985070681711,1799572365059873,1860677085722048,
  1909018654524409,1944054442741874,1967550395186176,1982224963180477,1990797453799876,
  1995495220545849,1997914924061823,1999087750402686,1999622991939188,1999852984690880,
  1999945988701514,1999981343883091,1999993957860315,1999998171733705,1999999485595289,
  1999999866282667,1999999968176851,1999999993159580,1999999998701031,1999999999790973,
  1999999999974242,1999999999998466,2000000000000293,2000000000000115,2000000000000019]
private def pvn_r384_6_1 : List ℕ := pCat pvn_r384_6_1_p0 (pCat pvn_r384_6_1_p1 (pCat
  pvn_r384_6_1_p2 (pCat pvn_r384_6_1_p3 (pCat pvn_r384_6_1_p4 pvn_r384_6_1_p5))))
private def pvi_r384_6 : List ℤ := bDc bZ (rPad bZ 385 pvn_r384_6_0)
private def pvo_r384_6 : List ℤ := bDc bZ (rPad bZ 385 pvn_r384_6_1)
private def phbn_r384_7_p0 : List ℕ := [89681027438797,126539122177313,154624169262439,
  178135860965389,198704928499691,217169680452818,234029260775090,249609632078281,264137721905177,
  277779127119481,290659140333803,302875318845148,314505417480326,325612619349553,336249111485037,
  346458604096064,356278151808592,365739499821462,374870098322119,383693880011932,392231865101114,
  400502638425289,408522730281546,416306923744044,423868505117517,431219469899026,438370693556107,
  445332074210330,452112652685316,458720714166275,465163874806487,471449155923283,477583047894195,
  483571565452007,489420295755582,495134440359947,500718852008044,506178067005957,511516333814257,
  516737638383587,521845726677542,526844124756261,531736156736877,536524960899557,541213504168559,
  545804595164829,550300895999166,554704932951797,559019106164609,563245698455717,567386883351868,
  571444732422157,575421221986156,579318239260682,583137588001765,586880993691753,590550108315734,
  594146514766478,597671730912732,601127213361905,604514360944847,607834517947494,611088977111588,
  614278982424393]
private def phbn_r384_7_p1 : List ℕ := [617405731715347,620470379075790,623474037116335,
  626417779075068,629302640788494,632129622536039,634899690767928,637613779725356,640272792961101,
  642877604767961,645429061521807,647927982945418,650375163298769,652771372500961,655117357188542,
  657413841714605,659661529092666,661861101889040,664013223067112,666118536786656,668177669161096,
  670191228975413,672159808367155,674083983472878,675964315042127,677801349020948,679595617106758,
  681347637276293,683057914288204,684726940161790,686355194633242,687943145590675,689491249489157,
  690999951746839,692469687123239,693900880080654,695293945129613,696649287159229,697967301753246,
  699248375492540,700492886244769,701701203441849,702873688345860,704010694303976,705112566992973,
  706179644653817,707212258316837,708210732017926,709175383006213,710106521943607,711004453096602,
  711869474520704,712701878237823,713501950406956,714269971488463,715006216402236,715710954680016,
  716384450612148,717026963388982,717638747237193,718220051551205,718771121019960,719292195749202,
  719783511379491]
private def phbn_r384_7_p2 : List ℕ := [720245299200109,720677786259033,721081195469142,
  721455745710805,721801651931000,722119125239102,722408372999475,722669598920992,722903003143605,
  723108782322075,723287129706978,723438235223089,723562285545238,723659464171741,723729951495491,
  723773924872795,723791558690044,723783024428292,723748490725815,723688123438730,723602085699740,
  723490537975059,723353638119608,723191541430504,723004400698935,722792366260454,722555586043750,
  722294205617952,722008368238505,721698214891673,721363884337706,721005513152720,720623235769321,
  720217184516026,719787489655503,719334279421676,718857680055731,718357815841037,717834809137041,
  717288780412151,716719848275627,716128129508536,715513739093763,714876790245136,714217394435661,
  713535661424912,712831699285583,712105614429238,711357511631257,710587494055031,709795663275385,
  708982119301283,708146960597808,707290284107442,706412185270666,705512758045881,704592094928682,
  703650286970486,702687423796528,701703593623239,700698883275025,699673378200442,698627162487790,
  697560318880134]
private def phbn_r384_7_p3 : List ℕ := [696472928789753,695365072312038,694236828238840,
  693088274071268,691919486031966,690730539076851,689521506906331,688292461976013,687043475506891,
  685774617495032,684485956720755,683177560757317,681849495979095,680501827569283,679134619527086,
  677747934674435,676341834662208,674916379975960,673471629941175,672007642728016,670524475355597,
  669022183695761,667500822476364,665960445284065,664401104566621,662822851634682,661225736663074,
  659609808691582,657975115625212,656321704233939,654649620151924,652958907876198,651249610764812,
  649521771034431,647775429757372,646010626858083,644227401109032,642425790126020,640605830362885,
  638767557105603,636911004465752,635036205373349,633143191569020,631231993595510,629302640788494,
  627355161266689,625389581921242,623405928404366,621404225117211,619384495196951,617346760503050,
  615291041602692,613217357755346,611125726896434,609016165620081,606888689160904,604743311374816,
  602580044718805,600398900229654,598199887501559,595983014662615,593748288350103,591495713684565,
  589225294242590]
private def phbn_r384_7_p4 : List ℕ := [586937032028271,584630927443289,582306979255547,
  579965184566309,577605538775779,575228035547047,572832666768336,570419422513471,567988291000501,
  565539258548376,563072309531601,560587426332773,558084589292896,555563776659370,553024964531557,
  550468126803778,547893235105649,545300258739595,542689164615423,540059917181790,537412478354419,
  534746807440880,532062861061779,529360593068142,526639954454806,523900893269597,521143354518060,
  518367280063514,515572608522143,512759275152874,509927211741720,507076346480291,504206603838113,
  501317904428415,498410164866967,495483297623588,492537210865838,489571808294450,486586988969970,
  483582647130052,480558671996832,477514947573717,474451352430935,471367759479068,468264035729810,
  465140042043060,461995632859434,458830655917186,455644951952457,452438354381671,449210688964795,
  445961773448096,442691417184871,439399420732526,436085575424229,432749662913182,429391454687414,
  426010711552777,422607183081618,419180607024377,415730708681059,412257200229288,408759780005263,
  405238131733620]
private def phbn_r384_7_p5 : List ℕ := [401691923701762,398120807873779,394524418938575,
  390902373286208,387254267905855,383579679198036,379878161692948,376149246665810,372392440639060,
  368607223760075,364793048041707,360949335451364,357075475832626,353170824641311,349234700475600,
  345266382377130,341265106876851,337230064755851,333160397487172,329055193319771,324913482960094,
  320734234800048,316516349632321,312258654784733,307959897594305,303618738128695,299233741047008,
  294803366473307,290325959733542,285799739779321,281222786088700,276593023793463,271908206732360,
  267165898067847,262363448026789,257497968228966,252566301945327,247564989472872,242490227614349,
  237337821994146,232103130606678,226780996552324,221365667328466,215850697252236,210228828513317,
  204491844865541,198630389877500,192633738686987,186489507889179,180183281807363,173698123749845,
  167013925916678,160106527830212,152946494071520,145497375502759,137713159812085,129534396257532,
  120882041704435,111647142405155,101672289533259,90715068235908,78366046786145,63824297518908,
  45015331200006]
private def phbn_r384_7 : List ℕ := pCat phbn_r384_7_p0 (pCat phbn_r384_7_p1 (pCat phbn_r384_7_p2
  (pCat phbn_r384_7_p3 (pCat phbn_r384_7_p4 phbn_r384_7_p5))))
private def phbv_r384_7 : List ℤ := uOh phbn_r384_7
private def pvn_r384_7_0_p0 : List ℕ := [1999889968120206,1999890199194951,2000006423733893,
  2000096613866041,2000036916075552,1999924264672867,1999940041113180,2000055235418262,
  2000072408825142,1999962985187447,1999920886428813,2000022392179634,2000080341499132,
  1999994040071373,1999910685764680,2000011810717307,2000059061868607,2000049186819987,
  1999854744518748,2000077436753702,1999955285551127,2000175849617622,1999748068970059,
  2000138414647283,1999958502422126,2000078380388377,1999952677436027,1999864229320770,
  2000223170980996,1999912252319008,1999954361208811,2000033099340212,1999957230605174,
  2000147720132727,1999871035881466,1999913041025124,2000215966139487,1999915566791992,
  1999916489589175,2000081444296906,1999964092666313,2000067239962010,1999970137915614,
  1999863375378274,2000178608883639,2000039810638761,1999775474924216,2000102659188714,
  2000127538711194,1999857968616012,1999998935938387,2000056746577715,1999967500498182,
  2000056742097050,1999952716581878,1999906836402782,2000165013029992,2000023561949961,
  1999771943491748,2000100619910795,2000195188273074,1999799953073271,1999908343163096,
  2000222889504269]
private def pvn_r384_7_0_p1 : List ℕ := [1999979159735204,1999831793223794,2000086336305627,
  2000074818658509,1999918319878664,2000006761184977,2000019834136302,1999960229258353,
  2000064072521423,2000013281848856,1999868124901521,2000059628946155,2000157048339380,
  1999847917010953,1999869134367686,2000235294136038,2000060831013365,1999712525934257,
  2000035367985948,2000297955687704,1999863079807884,1999732986572821,2000225560156642,
  2000202985128352,1999711178290042,1999881568977772,2000320939866780,2000026622701954,
  1999677941613078,2000060957006614,2000296552122732,1999864053906493,1999748852304566,
  2000193441654187,2000193287546163,1999768339119913,1999870054152341,2000251247485298,
  2000066927555365,1999745520540601,1999991422317531,2000244544097560,1999957785561639,
  1999775036024108,2000083831835512,2000199196572929,1999884337851793,1999829607323695,
  2000137811442657,2000141280544610,1999849161436963,1999885862044536,2000155527755978,
  2000090816997090,1999847297030799,1999927207614260,2000143079187823,2000061210545450,
  1999872857011527,1999943077517562,2000105053555380,2000060486642486,1999923446363451,
  1999927880768374]
private def pvn_r384_7_0_p2 : List ℕ := [2000040886979963,2000091536134879,2000003205405815,
  1999882357326634,1999942872411591,2000148434097845,2000121540986351,1999817527203052,
  1999802990798477,2000222029383769,2000292287383633,1999733404621094,1999564011422212,
  2000274010868033,2000637322057426,1999867580489970,1999260813761099,1999858526816226,
  2000435592113051,1999983480005820,1999923390844548,2001146921323974,2001312335156027,
  1998587188298168,1995966421674344,1997716976728444,2002748965897149,2005608507417269,
  2003620283927115,1999512738905226,1997039852092486,1997008077037754,1997893497437339,
  1998149561607937,1997480173739132,1996927037577376,1997583071121776,1998955317622079,
  1999616830209626,1999450258915309,1999496929739456,1999750922478005,1999468947670343,
  1999361551639964,2000466290546032,2001281117272128,1999810412233940,1997999238916938,
  1999344906809694,2002264442743005,2001719784185147,1998043460097332,1997313556171310,
  2001097914718798,2003202223670416,2000038816737980,1996907811223255,1998941105952239,
  2002445149616668,2001621588876474,1998407516076207,1998373982059637,2000936951999007,
  2001278295670259]
private def pvn_r384_7_0_p3 : List ℕ := [1999289235438941,1999034853337673,2000817232071568,
  2000978548038459,1999099194290502,1998722152164047,2000642736490969,2001507309483038,
  1999931804948231,1998684488530114,1999565875884313,2000726898167310,2000473328177107,
  1999826427606191,1999910452834000,2000062415221521,1999758468188997,1999708756934816,
  2000150040654095,2000334362819846,2000129286554392,2000074223099888,1999975765017043,
  1999489586858886,1999451028128994,2000417022221669,2000978844150739,2000014353355083,
  1999120409346196,1999914421274639,2000784631208288,1999801740574252,1998752296920205,
  2000045394674648,2001730479988716,2000620873044291,1998448151085555,1999102182324853,
  2001332281414626,2000787014929508,1998298695367766,1998704818302439,2001758531611204,
  2001988881461829,1998931031920470,1997964071337965,2001141196506465,2001934662301810,
  1999310079402900,1996716675736807,2000616744672033,2002059618110367,2000637221078390,
  1997236204427500,1999436200466061,2003407737213974,2000932172289703,1998181216928702,
  1998967686275798,2001752550999594,2002571923433822,1998624298278212,1997315983421028,
  2001828939974533]
private def pvn_r384_7_0_p4 : List ℕ := [2002636172954955,1998367218632997,1998042446140866,
  2001335738397443,2001333582047546,1999181757077179,1999300493603681,2000348385659042,
  2000141132125438,2000036857929937,2000409446741984,1999725907766923,1999000517325562,
  2000296740283042,2001655023141062,2000033713007447,1997736940140527,1999148375370242,
  2002478862494283,2002028597980043,1998114400203596,1997089070831440,2000650468643974,
  2002831198802043,2000143144465123,1997479325076276,1999620909827444,2003017763496266,
  2001896514498779,1998087053209002,1997839540883289,2001297586044712,2002498575060526,
  1999537611426218,1997549108303995,2000181474769097,1997670037954687,1999244153288483,
  2002192949030144,2001408024141065,1998067016475677,1997783016219957,2001275851988671,
  2002976652734561,1999956529858305,1996784092135431,1998449293593237,2002541771020587,
  2002860296037192,1999002211030811,1996619781126876,1999450651684655,2002563798345869,
  2002284845311888,1997849922726349,1997591938749304,2000626541861077,2002592162206294,
  2001665223047880,1996992937076932,1996289022616440,2002095474403584,2004509935694612,
  2000140987706618]
private def pvn_r384_7_0_p5 : List ℕ := [1996890324180285,1998471965606590,2000495112038257,
  2000365985959451,2000491354476922,2002065727296865,2002194807933419,1998582142558893,
  1993829317583159,1993030627179924,1997894281380829,2004563438021315,2007314957658713,
  2003802787748625,1996725087087341,1991257596572064,1991248224469973,1997933480060153,
  2007564678249737,2020376960899466,2017257507585674,2016744990002575,1991695765612266,
  1937872103303297,1938778646709629,1978312562582065,1987338702492586,1937246990344301,
  1843025214040121,1735550357973998,1644131459972173,1588742324629137,1577007992142575,
  1604952715801969,1660793001966187,1729985070681711,1799572365059873,1860677085722048,
  1909018654524409,1944054442741874,1967550395186176,1982224963180477,1990797453799876,
  1995495220545849,1997914924061823,1999087750402686,1999622991939188,1999852984690880,
  1999945988701514,1999981343883091,1999993957860315,1999998171733705,1999999485595289,
  1999999866282667,1999999968176851,1999999993159580,1999999998701031,1999999999790973,
  1999999999974242,1999999999998466,2000000000000293,2000000000000115,2000000000000019]
private def pvn_r384_7_0 : List ℕ := pCat pvn_r384_7_0_p0 (pCat pvn_r384_7_0_p1 (pCat
  pvn_r384_7_0_p2 (pCat pvn_r384_7_0_p3 (pCat pvn_r384_7_0_p4 pvn_r384_7_0_p5))))
private def pvn_r384_7_1_p0 : List ℕ := [1999952542822097,1999898713155453,1999885496494396,
  1999951254339473,2000054558411547,2000092850102740,2000020035479105,1999925440550060,
  1999931261636486,2000036717913997,2000077983298155,2000022874685493,1999894758600682,
  2000000851374456,1999989315688018,2000172778653056,1999823245585775,2000085741140412,
  1999840886579451,2000226626040712,1999932612044415,1999911819060168,2000058232328884,
  1999935396475018,2000173712181185,1999887371927433,1999884376101041,2000176801418668,
  1999952569985766,1999998639498540,1999987593938016,1999901534339053,2000180016211417,
  1999992776925478,1999801232630728,2000127509982320,2000065314973817,1999909411180363,
  2000032904791087,1999947776602786,2000015153051706,2000140526829508,1999855359771654,
  1999903136674423,2000222233345845,1999979997261246,1999815896738718,2000098895454490,
  2000073189350659,1999921815563461,2000018905985183,1999980182556590,1999971327146738,
  2000123493773599,1999956258158096,1999831294442954,2000149089181349,2000134791525010,
  1999772062940638,1999954033241064,2000243972148344,1999949044658950,1999803735451833,
  2000113364125335]
private def pvn_r384_7_1_p1 : List ℕ := [2000111644694966,1999879868740321,1999972668296626,
  2000075057356727,1999974404371135,2000000238497219,2000031692361188,1999922284753436,
  2000007475751596,2000133106247625,1999922228902336,1999848038537650,2000159325730349,
  2000131102250267,1999767085946441,1999923340675993,2000284239913321,2000000417287542,
  1999694252940853,2000084012223634,2000296383076297,1999835782020679,1999739900548550,
  2000230826413636,2000203866052205,1999721808702196,1999864219556581,2000304216080450,
  2000063600773105,1999690340312152,2000006187378841,2000297239016203,1999931191947162,
  1999729246236707,2000121250163615,2000234363994932,1999837923959827,1999807928258290,
  2000191104575491,2000147403750526,1999790939445830,1999896737524950,2000217248984806,
  2000061901063000,1999782715095509,1999975021067526,2000210888103299,1999993661752349,
  1999800261312349,2000031260962578,2000185382069589,1999950741498547,1999830830917913,
  2000059952608965,2000152216835078,1999936971885043,1999864622605287,2000058164032953,
  2000119203587607,1999955011848971,1999896096209835,2000023059388595,2000089280308054,
  2000008114663293]
private def pvn_r384_7_1_p2 : List ℕ := [1999925350452516,1999950988502947,2000058750887788,
  2000099957679106,1999960323515898,1999839084957120,2000014895537301,2000231279795710,
  2000018609551827,1999690031798514,1999935432843179,2000395731919133,2000129315339869,
  1999514776559946,1999775161829473,2000562880636350,2000361395524719,1999413222473325,
  1999492669990835,2000519293537923,2000545463152976,1999531196214546,1999589297609908,
  2000771515115098,2000525143820201,1998570237675910,1998253771048420,2001068579667305,
  2003493324196822,2001864861495708,1997668618854165,1995461413484486,1997324245869042,
  2001285111691951,2003982954465980,2003646883856230,2001289625442838,1999418365522201,
  1999077678875278,1998905218400510,1997842106061744,1996974093762820,1997240859710562,
  1997616461259023,1997509818890389,1998261269496744,1999955568936158,2000069559634966,
  1998147666945056,1997871850585949,2000788965226256,2002453286920453,1999668018866404,
  1996890179675967,1999153871451319,2002952516034318,2001835291468013,1997656201613026,
  1997485601880775,2001390125116412,2002632428593912,1999523214593821,1997743091333037,
  1999911341721843]
private def pvn_r384_7_1_p3 : List ℕ := [2001655007406933,2000186088962108,1998817115376808,
  2000028503319264,2001064868191830,1999778771792567,1998758526457511,2000113339967678,
  2001404203564781,2000294271742972,1998763152025185,1999301982413588,2000701202568469,
  2000739157056551,1999889825572710,1999651908634904,1999862566155947,1999853086399857,
  1999961760153303,2000325252908056,2000277448541681,1999858521309937,1999839144158663,
  2000017714594045,1999732975841654,1999654110062742,2000499105821980,2000940105860394,
  1999778792587497,1998772047659139,1999802715640757,2001066835454043,2000205992805651,
  1998969018223628,2000061477429100,2001463193006878,2000160857347006,1998007078763608,
  1999370971547666,2001608706662573,2001272293344901,1998124390806534,1999546828302956,
  2001355382160591,2001658308440150,1997552914630729,1998269310902536,2001716043457712,
  2001661480039516,1999148251355250,1997714065390949,2001576829490056,2002883273724942,
  1998392976318896,1997496355568543,2000613263035466,2001915018849663,1999857791393284,
  1997247063091596,1999425060870167,2003319454317028,2000832862137304,1996980911736659,
  1999992446393369]
private def pvn_r384_7_1_p4 : List ℕ := [2003333677270064,2000400057447913,1997867916129786,
  2000216888928475,2001811448050493,2000108113465542,1999175565336524,2000050120288246,
  2000293021411826,2000053534080375,2000359240253078,2000035983587145,1999131306135996,
  1999822218942178,2001370098749355,2000514929809576,1998220000991666,1998911273412931,
  2001984500731963,2001904358377082,1998236688945123,1997246631073384,2000982485967473,
  2003208056390891,2000106734814357,1997053822700051,1999100621449732,2002538955222781,
  2000760701557600,1998150026195021,1997487293455209,2003366814263578,2002071244182092,
  1998325052746064,1999470112684314,2000579179959409,2000043098626714,2000894549906822,
  2001469513162740,1998981266497815,1996632056459955,1998631322984569,2002129349508090,
  2001561208892379,1997841367691572,1997568566387045,2001124849851594,2003451503168818,
  1999742783370532,1996995154177635,1998258254551900,2002594747204229,2002932746064252,
  1998202861651681,1997301192454059,2000074709852345,2002317031288882,2001707852703389,
  1997686725846082,1996938031851210,2002178094127252,2004046619395630,1998825638245462,
  1995738785814740]
private def pvn_r384_7_1_p5 : List ℕ := [1999393699170098,2002996831535934,2001761845091139,
  1999276956838072,1999081960855282,1999529054807675,1998841061769251,1998938009986478,
  2001553041710015,2004103781598031,2002408698321653,1996787459937668,1992079915096992,
  1994096178774271,1999335428779475,2007923948823963,2004288239435183,2003998923455492,
  1993938335415105,1984890124721546,2000381548629694,1996868185041687,2004184704653389,
  2037538348545952,2034975126014500,1982785256739633,1942140925057759,1952488744111494,
  1988407371391226,1999598284044646,1957122554811754,1865862489116636,1753088846749315,
  1651543673043379,1586373001900957,1568613704873921,1595099757750294,1652936147613097,
  1725707501619829,1798798268313154,1862371637702560,1911910334371396,1947112022682233,
  1970162317390519,1984163567918776,1992087275650255,1996277196621715,1998351055763120,
  1999312822287223,1999730842564058,1999901062801129,1999965940604705,1999989048591860,
  1999996722447138,1999999091068862,1999999767786871,1999999945765221,1999999988540400,
  1999999997841524,1999999999645533,1999999999951066,1999999999994699,1999999999999619,
  1999999999999990]
private def pvn_r384_7_1 : List ℕ := pCat pvn_r384_7_1_p0 (pCat pvn_r384_7_1_p1 (pCat
  pvn_r384_7_1_p2 (pCat pvn_r384_7_1_p3 (pCat pvn_r384_7_1_p4 pvn_r384_7_1_p5))))
private def pvi_r384_7 : List ℤ := bDc bZ (rPad bZ 385 pvn_r384_7_0)
private def pvo_r384_7 : List ℤ := bDc bZ (rPad bZ 385 pvn_r384_7_1)
private def pwalks_384 : List RkmSegWalk := [
  ⟨phbv_r384_0, pvi_r384_0, pvo_r384_0⟩,
  ⟨phbv_r384_1, pvi_r384_1, pvo_r384_1⟩,
  ⟨phbv_r384_2, pvi_r384_2, pvo_r384_2⟩,
  ⟨phbv_r384_3, pvi_r384_3, pvo_r384_3⟩,
  ⟨phbv_r384_4, pvi_r384_4, pvo_r384_4⟩,
  ⟨phbv_r384_5, pvi_r384_5, pvo_r384_5⟩,
  ⟨phbv_r384_6, pvi_r384_6, pvo_r384_6⟩,
  ⟨phbv_r384_7, pvi_r384_7, pvo_r384_7⟩
  ]
private abbrev dP_0 : Prop := rkmAllTrueF [
    bSlChk 16 257 phbn_r384_1 257 pvn_r384_1_4 257 pvn_r384_1_5
  ] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := rkmAllTrueF [
    bSlChk 24 257 phbn_r384_1 257 pvn_r384_1_0 257 pvn_r384_1_1
  ] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := rkmAllTrueF [
    bSlChk 18 257 phbn_r384_1 257 pvn_r384_1_2 257 pvn_r384_1_3
  ] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := rkmAllTrueF [
    bSlChk 20 257 phbn_r384_1 257 pvn_r384_1_1 257 pvn_r384_1_2
  ] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := rkmAllTrueF [
    bSlChk 11 385 phbn_r384_3 385 pvn_r384_3_0 385 pvn_r384_3_1
  ] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := rkmAllTrueF [
    bSlChk 10 385 phbn_r384_3 385 pvn_r384_3_5 385 pvn_r384_3_6
  ] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := rkmAllTrueF [
    bSlChk 16 257 phbn_r384_1 257 pvn_r384_1_3 257 pvn_r384_1_4
  ] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := rkmAllTrueF [
    bSlChk 10 385 phbn_r384_3 385 pvn_r384_3_4 385 pvn_r384_3_5
  ] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := rkmAllTrueF [
    bSlChk 11 385 phbn_r384_2 385 pvn_r384_2_5 385 pvn_r384_2_6
  ] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := rkmAllTrueF [
    bSlChk 10 385 phbn_r384_3 385 pvn_r384_3_3 385 pvn_r384_3_4
  ] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := rkmAllTrueF [
    bSlChk 13 385 phbn_r384_2 385 pvn_r384_2_1 385 pvn_r384_2_2
  ] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := rkmAllTrueF [
    bSlChk 10 385 phbn_r384_3 385 pvn_r384_3_2 385 pvn_r384_3_3
  ] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := rkmAllTrueF [
    bSlChk 12 385 phbn_r384_2 385 pvn_r384_2_2 385 pvn_r384_2_3
  ] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := rkmAllTrueF [
    bSlChk 11 385 phbn_r384_2 385 pvn_r384_2_4 385 pvn_r384_2_5
  ] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := rkmAllTrueF [
    bSlChk 10 385 phbn_r384_3 385 pvn_r384_3_1 385 pvn_r384_3_2
  ] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := rkmAllTrueF [
    bSlChk 9 385 phbn_r384_3 385 pvn_r384_3_6 385 pvn_r384_3_7
  ] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := rkmAllTrueF [
    bSlChk 11 385 phbn_r384_2 385 pvn_r384_2_3 385 pvn_r384_2_4
  ] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := rkmAllTrueF [
    bSlChk 13 385 phbn_r384_2 257 pvn_r384_2_0 385 pvn_r384_2_1
  ] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := rkmAllTrueF [
    bSlChk 26 257 phbn_r384_0 257 pvn_r384_0_1 257 pvn_r384_0_2
  ] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := rkmAllTrueF [
    bSlChk 51 257 phbn_r384_0 1 pvn_r384_0_0 257 pvn_r384_0_1
  ] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := rkmAllTrueF [
    bSlChk 8 385 phbn_r384_5 385 pvn_r384_5_0 385 pvn_r384_5_1
  ] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := rkmAllTrueF [
    bSlChk 7 385 phbn_r384_4 385 pvn_r384_4_0 385 pvn_r384_4_1
  ] = true
private theorem bk_21 : dP_21 := by decide +kernel
private abbrev dP_22 : Prop := rkmAllTrueF [
    bSlChk 6 385 phbn_r384_7 385 pvn_r384_7_0 385 pvn_r384_7_1,
    bSlChk 5 385 phbn_r384_6 385 pvn_r384_6_0 385 pvn_r384_6_1
  ] = true
private theorem bk_22 : dP_22 := by decide +kernel
private abbrev dP_23 : Prop := rkmAllTrueF [
    muxNatListEq [Nat.add (highdNatMin (Nat.mul 1 256) 384) 1] [257],
    muxNatListEq [Nat.add (highdNatMin (Nat.mul 2 256) 384) 1] [385],
    rkmCheckRowFromWalks 256 32 384 [1, 1, 2, 2, 2, 2, 2, 2]
      [13603415, 16603863, 7422424, 7235899, 653824, 752234, 512749, 606766]
      [77, 94, 71, 70, 7, 8, 5, 6] rkmMasksHiHiB_m256_r384
      pwalks_384 rkmRowHiHiB_m256_r384
  ] = true
private theorem bk_23 : dP_23 := by decide +kernel
private theorem pw_r384_0_1 : pWOk 77 257 phbn_r384_0 1 pvn_r384_0_0 257 pvn_r384_0_2 :=
  bCh 51 26 257 (bSlSnd (bH bk_19))
    (bH bk_18)
private theorem pwalk_r384_0 : muxFastIterFullT16 77 257 phbv_r384_0 pvi_r384_0 = pvo_r384_0 :=
  pw_r384_0_1
private theorem pseg_384_0 :
    muxFastIterFullT16 77 (Nat.add (highdNatMin (Nat.mul 1 256) 384) 1)
      phbv_r384_0 pvi_r384_0 = pvo_r384_0 := by
  rw [bDm (bH bk_23)]
  exact pwalk_r384_0
private theorem pw_r384_1_1 : pWOk 44 257 phbn_r384_1 257 pvn_r384_1_0 257 pvn_r384_1_2 :=
  bCh 24 20 257 (bSlSnd (bH bk_1))
    (bH bk_3)
private theorem pw_r384_1_2 : pWOk 62 257 phbn_r384_1 257 pvn_r384_1_0 257 pvn_r384_1_3 :=
  bCh 44 18 257 pw_r384_1_1
    (bH bk_2)
private theorem pw_r384_1_3 : pWOk 78 257 phbn_r384_1 257 pvn_r384_1_0 257 pvn_r384_1_4 :=
  bCh 62 16 257 pw_r384_1_2
    (bH bk_6)
private theorem pw_r384_1_4 : pWOk 94 257 phbn_r384_1 257 pvn_r384_1_0 257 pvn_r384_1_5 :=
  bCh 78 16 257 pw_r384_1_3
    (bH bk_0)
private theorem pwalk_r384_1 : muxFastIterFullT16 94 257 phbv_r384_1 pvi_r384_1 = pvo_r384_1 :=
  pw_r384_1_4
private theorem pseg_384_1 :
    muxFastIterFullT16 94 (Nat.add (highdNatMin (Nat.mul 1 256) 384) 1)
      phbv_r384_1 pvi_r384_1 = pvo_r384_1 := by
  rw [bDm (bH bk_23)]
  exact pwalk_r384_1
private theorem pw_r384_2_1 : pWOk 26 385 phbn_r384_2 257 pvn_r384_2_0 385 pvn_r384_2_2 :=
  bCh 13 13 385 (bSlSnd (bH bk_17))
    (bH bk_10)
private theorem pw_r384_2_2 : pWOk 38 385 phbn_r384_2 257 pvn_r384_2_0 385 pvn_r384_2_3 :=
  bCh 26 12 385 pw_r384_2_1
    (bH bk_12)
private theorem pw_r384_2_3 : pWOk 49 385 phbn_r384_2 257 pvn_r384_2_0 385 pvn_r384_2_4 :=
  bCh 38 11 385 pw_r384_2_2
    (bH bk_16)
private theorem pw_r384_2_4 : pWOk 60 385 phbn_r384_2 257 pvn_r384_2_0 385 pvn_r384_2_5 :=
  bCh 49 11 385 pw_r384_2_3
    (bH bk_13)
private theorem pw_r384_2_5 : pWOk 71 385 phbn_r384_2 257 pvn_r384_2_0 385 pvn_r384_2_6 :=
  bCh 60 11 385 pw_r384_2_4
    (bH bk_8)
private theorem pwalk_r384_2 : muxFastIterFullT16 71 385 phbv_r384_2 pvi_r384_2 = pvo_r384_2 :=
  pw_r384_2_5
private theorem pseg_384_2 :
    muxFastIterFullT16 71 (Nat.add (highdNatMin (Nat.mul 2 256) 384) 1)
      phbv_r384_2 pvi_r384_2 = pvo_r384_2 := by
  rw [bDm (bH (bT bk_23))]
  exact pwalk_r384_2
private theorem pw_r384_3_1 : pWOk 21 385 phbn_r384_3 385 pvn_r384_3_0 385 pvn_r384_3_2 :=
  bCh 11 10 385 (bSlSnd (bH bk_4))
    (bH bk_14)
private theorem pw_r384_3_2 : pWOk 31 385 phbn_r384_3 385 pvn_r384_3_0 385 pvn_r384_3_3 :=
  bCh 21 10 385 pw_r384_3_1
    (bH bk_11)
private theorem pw_r384_3_3 : pWOk 41 385 phbn_r384_3 385 pvn_r384_3_0 385 pvn_r384_3_4 :=
  bCh 31 10 385 pw_r384_3_2
    (bH bk_9)
private theorem pw_r384_3_4 : pWOk 51 385 phbn_r384_3 385 pvn_r384_3_0 385 pvn_r384_3_5 :=
  bCh 41 10 385 pw_r384_3_3
    (bH bk_7)
private theorem pw_r384_3_5 : pWOk 61 385 phbn_r384_3 385 pvn_r384_3_0 385 pvn_r384_3_6 :=
  bCh 51 10 385 pw_r384_3_4
    (bH bk_5)
private theorem pw_r384_3_6 : pWOk 70 385 phbn_r384_3 385 pvn_r384_3_0 385 pvn_r384_3_7 :=
  bCh 61 9 385 pw_r384_3_5
    (bH bk_15)
private theorem pwalk_r384_3 : muxFastIterFullT16 70 385 phbv_r384_3 pvi_r384_3 = pvo_r384_3 :=
  pw_r384_3_6
private theorem pseg_384_3 :
    muxFastIterFullT16 70 (Nat.add (highdNatMin (Nat.mul 2 256) 384) 1)
      phbv_r384_3 pvi_r384_3 = pvo_r384_3 := by
  rw [bDm (bH (bT bk_23))]
  exact pwalk_r384_3
private theorem pwalk_r384_4 : muxFastIterFullT16 7 385 phbv_r384_4 pvi_r384_4 = pvo_r384_4 :=
  (bSlSnd (bH bk_21))
private theorem pseg_384_4 :
    muxFastIterFullT16 7 (Nat.add (highdNatMin (Nat.mul 2 256) 384) 1)
      phbv_r384_4 pvi_r384_4 = pvo_r384_4 := by
  rw [bDm (bH (bT bk_23))]
  exact pwalk_r384_4
private theorem pwalk_r384_5 : muxFastIterFullT16 8 385 phbv_r384_5 pvi_r384_5 = pvo_r384_5 :=
  (bSlSnd (bH bk_20))
private theorem pseg_384_5 :
    muxFastIterFullT16 8 (Nat.add (highdNatMin (Nat.mul 2 256) 384) 1)
      phbv_r384_5 pvi_r384_5 = pvo_r384_5 := by
  rw [bDm (bH (bT bk_23))]
  exact pwalk_r384_5
private theorem pwalk_r384_6 : muxFastIterFullT16 5 385 phbv_r384_6 pvi_r384_6 = pvo_r384_6 :=
  (bSlSnd (bH (bT bk_22)))
private theorem pseg_384_6 :
    muxFastIterFullT16 5 (Nat.add (highdNatMin (Nat.mul 2 256) 384) 1)
      phbv_r384_6 pvi_r384_6 = pvo_r384_6 := by
  rw [bDm (bH (bT bk_23))]
  exact pwalk_r384_6
private theorem pwalk_r384_7 : muxFastIterFullT16 6 385 phbv_r384_7 pvi_r384_7 = pvo_r384_7 :=
  (bSlSnd (bH bk_22))
private theorem pseg_384_7 :
    muxFastIterFullT16 6 (Nat.add (highdNatMin (Nat.mul 2 256) 384) 1)
      phbv_r384_7 pvi_r384_7 = pvo_r384_7 := by
  rw [bDm (bH (bT bk_23))]
  exact pwalk_r384_7
private theorem pwalks_snd_384 : RkmSegWalksSound 256 384 [1, 1, 2, 2, 2, 2, 2, 2]
    [77, 94, 71, 70, 7, 8, 5, 6] pwalks_384 := by
  dsimp only [RkmSegWalksSound, pwalks_384]
  exact ⟨pseg_384_0, ⟨pseg_384_1, ⟨pseg_384_2, ⟨pseg_384_3,
    ⟨pseg_384_4, ⟨pseg_384_5, ⟨pseg_384_6, ⟨pseg_384_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 256, r = 384)` (`FindAllJohnsonRampKickMuxHi256T2`). -/
theorem rkmTrajHiHiB_m256_r384 : rkmLo12EqHi 256 32 384 [1, 1, 2, 2, 2, 2, 2, 2]
    [13603415, 16603863, 7422424, 7235899, 653824, 752234, 512749, 606766]
    [77, 94, 71, 70, 7, 8, 5, 6] rkmMasksHiHiB_m256_r384 rkmRowHiHiB_m256_r384 :=
  rkmCheckRowFromWalks_sound pwalks_snd_384 (bH (bT (bT bk_23)))
end
end QuantumComputation.Specs.DickeSol
