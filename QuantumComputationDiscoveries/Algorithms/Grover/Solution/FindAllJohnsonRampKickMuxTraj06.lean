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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxKernelB
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxTraj04
/-
# Multi-Segment `T_16` Trajectory Part `06` (`FindAllJohnsonRampKickMuxTraj06`)

Certified kernel trajectory evaluations (`30` rows, `37991` substep-coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Prefix-kick masks for `(m = 2, r = 4)`. -/
def rkmMasks_m2_r4 : List (List Bool) := [
  [], [true], [true, true], [false, true], [false, false, true], [], [false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 4)`. -/
def rkmRow_m2_r4 : List ℕ := [120065348, 2560800, 349958405437, 649790169923]
/-- Prefix-kick masks for `(m = 2, r = 7)`. -/
def rkmMasks_m2_r7 : List (List Bool) := [
  [], [], [false, true], [true, false, true, true], [false, false, false, false, true],
  [false, true], [false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 7)`. -/
def rkmRow_m2_r7 : List ℕ := [
  226690, 654205746, 758308657, 662565450, 2856685535, 433848157371, 561189692146]
/-- Prefix-kick masks for `(m = 2, r = 9)`. -/
def rkmMasks_m2_r9 : List (List Bool) := [
  [], [], [false, true, true], [true, false, false, true, true],
  [false, false, false, true, false, true, true], [true, true, true, true, false, false, true],
  [true, true, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 9)`. -/
def rkmRow_m2_r9 : List ℕ := [
  3402306, 226685019, 9114959, 5879811713, 6822398929, 33558, 8033093612, 466152644443,
  512802043721]
/-- Prefix-kick masks for `(m = 2, r = 11)`. -/
def rkmMasks_m2_r11 : List (List Bool) := [
  [], [], [], [], [false, false, false, true, true],
  [true, true, false, false, true, false, false, true, true], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 11)`. -/
def rkmRow_m2_r11 : List ℕ := [
  3566770, 1723828876, 10810861, 537989041, 817205566, 1068483069, 9709609197, 2338730167,
  11875281344, 438010993752, 533903469455]
/-- Prefix-kick masks for `(m = 4, r = 4)`. -/
def rkmMasks_m4_r4 : List (List Bool) := [
  [], [], [true, true], [false, false, true], [], [false, false, true], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 4)`. -/
def rkmRow_m4_r4 : List ℕ := [191776178, 57591698, 140594193879, 858895860369]
/-- Prefix-kick masks for `(m = 4, r = 9)`. -/
def rkmMasks_m4_r9 : List (List Bool) := [
  [], [], [true, true, true, true, true], [true, false, true, true, false, true, true], [],
  [false, true, true, false, false, true, false, true],
  [true, false, false, true, true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 9)`. -/
def rkmRow_m4_r9 : List ℕ := [
  200416315, 73900579, 405002177, 4853088110, 391460757, 3111378303, 382742443, 233161210412,
  757420748382]
/-- Prefix-kick masks for `(m = 8, r = 12)`. -/
def rkmMasks_m8_r12 : List (List Bool) := [
  [], [true, false, false, true, true, true],
  [true, false, true, false, true, false, false, true, true],
  [true, false, true, false, true, true, true, true, false, true, true],
  [false, false, false, false, true, false, false, false, false, false, true],
  [false, true, false, false, false, true, false, true],
  [false, false, false, false, false, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 12)`. -/
def rkmRow_m8_r12 : List ℕ := [
  240533, 3054284, 37066461, 67965795, 25753562, 57721829, 316857704, 3606092997, 7441688759,
  39146337, 75129697089, 913274714541]
/-- Prefix-kick masks for `(m = 8, r = 13)`. -/
def rkmMasks_m8_r13 : List (List Bool) := [
  [], [true, false, false, true, true, false, true],
  [true, false, true, false, true, false, true, false, true, true],
  [false, true, false, true, false, true, true, true, true, false, true, true],
  [true, true, false, true, true, false, true, false, false, false, false, true],
  [false, false, false, true, false, true, true, false, true],
  [true, true, false, false, false, false, false, false, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 13)`. -/
def rkmRow_m8_r13 : List ℕ := [
  13603, 10285, 33050, 9668736, 3754047, 55814330, 471178741, 1223231525, 4311125203, 11183575188,
  205210228, 75161241282, 907375143250]
/-- Prefix-kick masks for `(m = 8, r = 27)`. -/
def rkmMasks_m8_r27 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 27)`. -/
def rkmRow_m8_r27 : List ℕ := [
  135867, 20328531, 241122, 15182992, 1731839, 7337936, 1326942, 1561499, 756496, 268197687,
  24684437, 3357040008, 7222102853, 2121139139, 97872645446, 289652943246, 330696506967,
  192656662146, 62889247938, 11818632466, 1261125758, 72279058, 1965108, 18554]
/-- Mask chunk for `(m = 8, r = 128)`. -/
def rkmMkP_m8_r128_s3_p0 : List Bool := [
  false, true, false, false, false, false, true, false, true, true, false, false, true, false,
  false, false, false, false, true, true, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, true]
/-- Mask chunk for `(m = 8, r = 128)`. -/
def rkmMkP_m8_r128_s4_p0 : List Bool := [
  true, true, false, true, true, false, true, true, false, false, true, false, true, false, false,
  false, false, true, false, false, true, true, true, true, true, true, false, false, false, true,
  true, true, true, false, false, true, true, true, true, false, true, true, true, false, false,
  false, false, false, false, true, false, false, false, true, true, true, false, false, false,
  true, false, true, true, true]
/-- Mask chunk for `(m = 8, r = 128)`. -/
def rkmMkP_m8_r128_s4_p1 : List Bool := [
  true, true, false, false, false, true, true, true, true, false, false, false, false, true,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, false, false, true, true]
/-- Mask chunk for `(m = 8, r = 128)`. -/
def rkmMkP_m8_r128_s5_p0 : List Bool := [
  false, false, true, false, true, true, true, false, true, false, true, true, false, false,
  false, false, true, false, true, false, false, false, false, true, false, true, true, true,
  false, true, false, true, false, true, false, true, false, true, false, false, false, false,
  false, false, false, false, true, false, false, false, true, true, false, false, false, false,
  false, true, false, false, true, true, false, true]
/-- Mask chunk for `(m = 8, r = 128)`. -/
def rkmMkP_m8_r128_s5_p1 : List Bool := [
  true, false, false, true, false, false, true, true, false, false, true, false, false, true,
  true, false, false, true, false, true, true, false, false, false, false, false, true, true,
  false, false, true, false, false, true, true, false, true, true, true, false, false, false,
  true, true, true, true]
/-- Mask chunk for `(m = 8, r = 128)`. -/
def rkmMkP_m8_r128_s6_p0 : List Bool := [
  true, false, false, true, false, true, false, false, false, true, false, false, false, false,
  false, false, false, false, false, true, false, false, false, false, true, false, false, true,
  false, false, false, true, false, false, false, true, true, false, false, true, true, false,
  false, false, true, false, false, false, true, false, false, false, false, true, false, true,
  false, false, true, false, false, false, false, false]
/-- Mask chunk for `(m = 8, r = 128)`. -/
def rkmMkP_m8_r128_s6_p1 : List Bool := [
  false, false, false, true, false, true, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, false, true, true, false, false, true, true, false, true, true, false,
  false, true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 8, r = 128)`. -/
def rkmMasks_m8_r128 : List (List Bool) := [
  [], [], [false, false, true], rkmMkP_m8_r128_s3_p0,
  rkmMkP_m8_r128_s4_p0 ++ rkmMkP_m8_r128_s4_p1, rkmMkP_m8_r128_s5_p0 ++ rkmMkP_m8_r128_s5_p1,
  rkmMkP_m8_r128_s6_p0 ++ rkmMkP_m8_r128_s6_p1, []]
/-- Row chunk `0` `(m = 8, r = 128)`. -/
def rkmRowP_m8_r128_p0 : List ℕ := [
  25753, 499580, 1412167, 1887430, 196941, 7394571, 1147111, 17036518, 9288553, 3081433, 35887119,
  29438542, 177362, 14410996, 10744908, 5016653, 12128084, 37376, 17429120, 4936387, 14658378,
  30770515, 890710, 33595720, 22932213, 29720000, 5095006, 2058764, 10356339, 564, 2391392,
  313468, 15063252, 6431703, 2995054, 166617, 3802139, 2772473, 37579, 1419943, 95327, 4889050,
  254658, 101295, 1804142, 1048349, 5286960, 2229, 6112612, 1423334, 24600, 6951339, 3224446,
  5141994, 9769561, 734017, 6529428, 868307, 544080, 8467573, 5313434, 6553693, 5150613, 25147158]
/-- Row chunk `1` `(m = 8, r = 128)`. -/
def rkmRowP_m8_r128_p1 : List ℕ := [
  1192124, 3668088, 458502, 24365947, 26360099, 26002696, 46649112, 18218968, 6200997, 976347,
  12915385, 6972, 3612530, 5442929, 442362, 58530223, 68889028, 28244227, 46477124, 258451709,
  105979433, 338122029, 979656, 175682750, 615561630, 151445147, 11473771, 595612535, 497223752,
  41490912, 273775799, 836322109, 252160471, 48179384, 672754464, 252884921, 1706211, 327483989,
  300055073, 195655, 31296, 15101169, 7510794, 1546953269, 239206871, 270310503, 1122955070,
  52741668, 738661229, 1010551669, 865263636, 2212074146, 420890234, 2094141514, 502393697,
  2784777156, 747537764, 6099249260, 2199582587, 7934783798, 32320082465, 3760525788, 69182646788,
  857272724417]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 128)`. -/
def rkmRow_m8_r128 : List ℕ := rkmRowP_m8_r128_p0 ++ rkmRowP_m8_r128_p1
/-- Prefix-kick masks for `(m = 16, r = 4)`. -/
def rkmMasks_m16_r4 : List (List Bool) := [
  [], [true], [true, false, true, true, true], [false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 4)`. -/
def rkmRow_m16_r4 : List ℕ := [1899, 68017304, 49098744750, 950833235023]
/-- Prefix-kick masks for `(m = 16, r = 11)`. -/
def rkmMasks_m16_r11 : List (List Bool) := [
  [true, false, true, true, true], [true, true, false, true, true, false, false, true, true],
  [false, true, false, false, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 11)`. -/
def rkmRow_m16_r11 : List ℕ := [
  1556093, 44385, 17941921, 8299518, 49904344, 127768384, 21369821, 2707089473, 392734485,
  38635465962, 958037803181]
/-- Mask chunk for `(m = 16, r = 21)`. -/
def rkmMkP_m16_r21_s1_p0 : List Bool := [
  false, true, false, false, true, true, false, false, true, true, false, false, true, false,
  true, false, true, true]
/-- Mask chunk for `(m = 16, r = 21)`. -/
def rkmMkP_m16_r21_s2_p0 : List Bool := [
  false, true, false, true, false, true, false, true, false, false, true, false, false, true,
  false, false, true, false, true, true]
/-- Prefix-kick masks for `(m = 16, r = 21)`. -/
def rkmMasks_m16_r21 : List (List Bool) := [[], rkmMkP_m16_r21_s1_p0, rkmMkP_m16_r21_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 21)`. -/
def rkmRow_m16_r21 : List ℕ := [
  0, 24, 838, 3590, 131275, 30250, 3464982, 4868301, 2307609, 6960514, 62988151, 39434328,
  154210299, 1038549324, 82123697, 2568871491, 9772468152, 3058163379, 1284995478, 43058644101,
  938861783963]
/-- Mask chunk for `(m = 16, r = 36)`. -/
def rkmMkP_m16_r36_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, true, true, true, true, true, false,
  false, true, false, false, true, false, false, false, true, false, false, true, true, false,
  false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 16, r = 36)`. -/
def rkmMkP_m16_r36_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, true, true, false, true, false, true, false,
  false, true, false, true, false, true, false, true, false, true, false, false, true, false,
  true, false, true, false, true]
/-- Prefix-kick masks for `(m = 16, r = 36)`. -/
def rkmMasks_m16_r36 : List (List Bool) := [
  [], [], rkmMkP_m16_r36_s2_p0, rkmMkP_m16_r36_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 36)`. -/
def rkmRow_m16_r36 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 2, 9, 33, 178, 179, 12, 1011, 20747, 116414, 475928, 439223, 1080222,
  1803003, 4254131, 907134, 256681, 15586530, 832729, 277314535, 6276118, 2220373653, 49434168,
  10949699060, 74331, 29301117114, 11346562523, 37759493978, 908063879552]
/-- Mask chunk for `(m = 16, r = 52)`. -/
def rkmMkP_m16_r52_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, false, false, true, false, true, true, false, true, true,
  true, true, false, false, true, true, true, true, false, true, false, false, true, true, false,
  false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 16, r = 52)`. -/
def rkmMkP_m16_r52_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  false, true, false, true, false, true, false, false, true, false, true, false, true, false,
  true, false, false, true, false, true, true, false, false, true, false, true, false, true,
  false, true, false, true, false, false, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 52)`. -/
def rkmMasks_m16_r52 : List (List Bool) := [
  [], [], [], rkmMkP_m16_r52_s3_p0, rkmMkP_m16_r52_s4_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 52)`. -/
def rkmRow_m16_r52 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 78, 220, 603, 25, 0, 1102, 12140, 36369,
  53635, 107334, 69866, 1045729, 145026, 91370, 1572093, 1472636, 1254028, 41243, 3344726,
  20223540, 21634, 21832682, 143072878, 102358838, 1302273007, 852287226, 7142675772, 3228203672,
  18284429712, 1512752519, 95095186, 39732596272, 78997248, 42905221188, 884568708552]
/-- Mask chunk for `(m = 32, r = 18)`. -/
def rkmMkP_m32_r18_s1_p0 : List Bool := [
  true, true, false, false, false, true, true, false, false, true, true, false, true, true]
/-- Mask chunk for `(m = 32, r = 18)`. -/
def rkmMkP_m32_r18_s2_p0 : List Bool := [
  true, false, true, false, true, true, false, true, false, true, true, false, true, true, false,
  true, true]
/-- Prefix-kick masks for `(m = 32, r = 18)`. -/
def rkmMasks_m32_r18 : List (List Bool) := [
  [true, true, true], rkmMkP_m32_r18_s1_p0, rkmMkP_m32_r18_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 18)`. -/
def rkmRow_m32_r18 : List ℕ := [
  5, 49, 107, 12828, 13, 5285, 355702, 2977850, 17031540, 108848, 13225947, 1112413773, 20019929,
  140724632, 4549620748, 53492012, 18308171717, 975781838818]
/-- Mask chunk for `(m = 32, r = 23)`. -/
def rkmMkP_m32_r23_s0_p0 : List Bool := [
  false, false, true, false, false, true, true, false, false, true, false, true, true, false,
  false, true, true, true]
/-- Mask chunk for `(m = 32, r = 23)`. -/
def rkmMkP_m32_r23_s1_p0 : List Bool := [
  true, true, false, true, false, true, false, true, false, true, false, true, false, true, true,
  false, true, false, false, true, true]
/-- Mask chunk for `(m = 32, r = 23)`. -/
def rkmMkP_m32_r23_s2_p0 : List Bool := [
  false, true, true, true, true, false, true, false, true, false, true, true, false, false, false,
  true, false, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 32, r = 23)`. -/
def rkmMasks_m32_r23 : List (List Bool) := [
  rkmMkP_m32_r23_s0_p0, rkmMkP_m32_r23_s1_p0, rkmMkP_m32_r23_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 23)`. -/
def rkmRow_m32_r23 : List ℕ := [
  0, 0, 2, 71, 915, 6276, 29931, 97567, 123783, 18012, 6889928, 8720862, 25788192, 2684114,
  83272246, 190719686, 1332569036, 88900517, 31045093, 3703989598, 109798795, 21717631421,
  972697713673]
/-- Mask chunk for `(m = 32, r = 28)`. -/
def rkmMkP_m32_r28_s1_p0 : List Bool := [
  false, false, false, false, false, false, true, true, true, true, true, false, true, true,
  false, false, true, false, false, true, true, false, false, false, true, true]
/-- Mask chunk for `(m = 32, r = 28)`. -/
def rkmMkP_m32_r28_s2_p0 : List Bool := [
  false, false, false, false, false, true, false, false, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 32, r = 28)`. -/
def rkmMasks_m32_r28 : List (List Bool) := [
  [false, false, false, false, true, true, true], rkmMkP_m32_r28_s1_p0, rkmMkP_m32_r28_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 28)`. -/
def rkmRow_m32_r28 : List ℕ := [
  0, 5, 7, 38, 50, 0, 0, 65, 6, 76, 773, 5225, 21666, 126861, 311136, 1650441, 3067712, 18228328,
  27303612, 212143965, 247766368, 1642645827, 2341051355, 10084106, 7629775121, 5665757,
  19144602110, 968715548924]
/-- Prefix-kick masks for `(m = 64, r = 6)`. -/
def rkmMasks_m64_r6 : List (List Bool) := [[], [false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 6)`. -/
def rkmRow_m64_r6 : List ℕ := [24681, 539244, 862605, 134398786, 28223539392, 971640634821]
/-- Mask chunk for `(m = 64, r = 17)`. -/
def rkmMkP_m64_r17_s0_p0 : List Bool := [
  true, true, true, false, false, true, true, false, false, false, true, true, false, false, true,
  true]
/-- Prefix-kick masks for `(m = 64, r = 17)`. -/
def rkmMasks_m64_r17 : List (List Bool) := [rkmMkP_m64_r17_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 17)`. -/
def rkmRow_m64_r17 : List ℕ := [
  0, 0, 0, 0, 0, 13, 131, 1029, 11239, 195725, 1137549, 17058118, 47353178, 782246071, 5981830,
  12033284786, 987112730143]
/-- Mask chunk for `(m = 64, r = 24)`. -/
def rkmMkP_m64_r24_s0_p0 : List Bool := [
  false, true, true, false, false, true, true, false, true, true, false, false, false, true, true,
  true, true, true, true, true]
/-- Mask chunk for `(m = 64, r = 24)`. -/
def rkmMkP_m64_r24_s1_p0 : List Bool := [
  true, false, true, false, true, false, true, false, true, false, false, true, false, true,
  false, true, false, false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 64, r = 24)`. -/
def rkmMasks_m64_r24 : List (List Bool) := [rkmMkP_m64_r24_s0_p0, rkmMkP_m64_r24_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 24)`. -/
def rkmRow_m64_r24 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 6, 0, 2, 17, 18, 6635, 45200, 2112562, 837875, 4595005, 99175899, 31940481,
  32582431, 1698540781, 4578178, 9948384422, 988177200153]
/-- Mask chunk for `(m = 64, r = 30)`. -/
def rkmMkP_m64_r30_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  true, false, false, false, true, true, true, true, true, true, true]
/-- Mask chunk for `(m = 64, r = 30)`. -/
def rkmMkP_m64_r30_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, true, true, true, false, true, false,
  false, false, false, false, false, false, false, false, false, true, true, true, false, false,
  true, true]
/-- Mask chunk for `(m = 64, r = 30)`. -/
def rkmMkP_m64_r30_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, false, false, true, false,
  true, false, true, false, true, true, false, true, false, true, false, true, false, true, false,
  true]
/-- Prefix-kick masks for `(m = 64, r = 30)`. -/
def rkmMasks_m64_r30 : List (List Bool) := [
  rkmMkP_m64_r30_s0_p0, rkmMkP_m64_r30_s1_p0, rkmMkP_m64_r30_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 30)`. -/
def rkmRow_m64_r30 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 21, 27, 18, 193, 1841, 3078, 300947, 14091, 64764, 2510338,
  188023286, 38597, 103601421, 163471724, 11464053, 3659918970, 215455801, 9274436906,
  986380693367]
/-- Mask chunk for `(m = 64, r = 36)`. -/
def rkmMkP_m64_r36_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, true, true, false, false, true, true, false, false, true, false, false, true,
  true, true]
/-- Mask chunk for `(m = 64, r = 36)`. -/
def rkmMkP_m64_r36_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, true, false, true, false, true,
  true, false, false, true, true]
/-- Mask chunk for `(m = 64, r = 36)`. -/
def rkmMkP_m64_r36_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, false, false, true, false, true, false, false, false, true,
  false, false, false, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 64, r = 36)`. -/
def rkmMasks_m64_r36 : List (List Bool) := [
  rkmMkP_m64_r36_s0_p0, rkmMkP_m64_r36_s1_p0, rkmMkP_m64_r36_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 36)`. -/
def rkmRow_m64_r36 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 195, 959, 3546, 9473, 8479, 7426, 456, 362149,
  924740, 259523, 119688, 15267306, 218979550, 1169094, 306538045, 1083699, 70530141, 2529329720,
  14672165, 9415291127, 987425441778]
/-- Mask chunk for `(m = 256, r = 16)`. -/
def rkmMkP_m256_r16_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, true, false, false, true]
/-- Mask chunk for `(m = 256, r = 16)`. -/
def rkmMkP_m256_r16_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 256, r = 16)`. -/
def rkmMkP_m256_r16_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true]
/-- Mask chunk for `(m = 256, r = 16)`. -/
def rkmMkP_m256_r16_s5_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  true]
/-- Prefix-kick masks for `(m = 256, r = 16)`. -/
def rkmMasks_m256_r16 : List (List Bool) := [
  [], rkmMkP_m256_r16_s1_p0, [], rkmMkP_m256_r16_s3_p0, rkmMkP_m256_r16_s4_p0,
  rkmMkP_m256_r16_s5_p0, [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 16)`. -/
def rkmRow_m256_r16 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 2, 48, 162, 7, 175552, 73773, 4410499, 10160209592, 989835130018]
/-- Mask chunk for `(m = 256, r = 23)`. -/
def rkmMkP_m256_r23_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 256, r = 23)`. -/
def rkmMasks_m256_r23 : List (List Bool) := [rkmMkP_m256_r23_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 23)`. -/
def rkmRow_m256_r23 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 4, 27, 41578, 1513776, 92838445, 575112974,
  7293735245, 992036757398]
/-- Mask chunk for `(m = 512, r = 15)`. -/
def rkmMkP_m512_r15_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 512, r = 15)`. -/
def rkmMasks_m512_r15 : List (List Bool) := [
  [false, false, false, false, false, false, false, true, false, true, true, true],
  rkmMkP_m512_r15_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 15)`. -/
def rkmRow_m512_r15 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 75, 1898, 404, 1531178, 1326659, 10482912598, 989514226797]
/-- Mask chunk for `(m = 512, r = 28)`. -/
def rkmMkP_m512_r28_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 512, r = 28)`. -/
def rkmMkP_m512_r28_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, true, true]
/-- Mask chunk for `(m = 512, r = 28)`. -/
def rkmMkP_m512_r28_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false, true]
/-- Prefix-kick masks for `(m = 512, r = 28)`. -/
def rkmMasks_m512_r28 : List (List Bool) := [
  rkmMkP_m512_r28_s0_p0, rkmMkP_m512_r28_s1_p0, rkmMkP_m512_r28_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 28)`. -/
def rkmRow_m512_r28 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1639, 94141, 12887, 10183102,
  1107681, 5737888460, 994250710932]
/-- Mask chunk for `(m = 512, r = 64)`. -/
def rkmMkP_m512_r64_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, true, true, true, true,
  true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 512, r = 64)`. -/
def rkmMkP_m512_r64_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true, false,
  true, false, true, false, false, true, false, false, true, true]
/-- Mask chunk for `(m = 512, r = 64)`. -/
def rkmMkP_m512_r64_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, false, true, false, true]
/-- Prefix-kick masks for `(m = 512, r = 64)`. -/
def rkmMasks_m512_r64 : List (List Bool) := [
  rkmMkP_m512_r64_s0_p0, rkmMkP_m512_r64_s1_p0, rkmMkP_m512_r64_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 64)`. -/
def rkmRow_m512_r64 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1005, 671, 49, 138459,
  3492692, 107634, 98965624, 69703, 2707360194, 997189859291]
/-- Prefix-kick masks for `(m = 1024, r = 22)`. -/
def rkmMasks_m1024_r22 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 22)`. -/
def rkmRow_m1024_r22 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 35, 37, 617842, 6619037, 7074803498,
  992917958657]
/-- Prefix-kick masks for `(m = 1024, r = 27)`. -/
def rkmMasks_m1024_r27 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 27)`. -/
def rkmRow_m1024_r27 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 107, 580, 931996, 27224572,
  5787687246, 994184154114]
/-- Unpacks `j` LSB-first bits of `< 2 ^ 50` word `w` (`FindAllJohnsonRampKickMuxTraj06`). -/
def rkmWbTraj06 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWbTraj06 j (Nat.div w 2)
/-- Concatenates `50`-bit `< 2 ^ 50` chunks (final length `rem`) into a `List Bool` mask. -/
def rkmMaskWordsTraj06 : ℕ → List ℕ → List Bool
  | _, [] => []
  | rem, [w] => rkmWbTraj06 rem w
  | rem, w :: v :: ws => rkmWbTraj06 50 w ++ rkmMaskWordsTraj06 rem (v :: ws)
/-- Krotov masks `(m = 32, r = 96)`. -/
def rkmMasksPack_m32_r96 : List (List Bool) := [rkmWbTraj06 31 1157627904, rkmWbTraj06 4 15,
  rkmMaskWordsTraj06 11 [985162435066109, 1025],
  rkmMaskWordsTraj06 35 [285841308425642, 20602486784],
  rkmMaskWordsTraj06 46 [412622303003972, 65970729357037],
  rkmMaskWordsTraj06 43 [296336936145494, 7036978419029],
  rkmMaskWordsTraj06 45 [9753157699, 19814048616772], []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 96)`. -/
def rkmRowPack_m32_r96 : List ℕ := [2513, 28863, 75528, 1438268, 1792522, 176880, 111467, 82455,
  42258, 1090, 2382095, 2454284, 602774, 29827, 59059, 14620542, 501425, 21511, 503231, 59,
  1360149, 1166348, 1435659, 6978, 2281318, 1348261, 563856, 1619677, 596985, 1279477, 19014091,
  4217822, 1134377, 348415, 4161485, 13424595, 2112735, 157464, 1162781, 255829, 698719, 278480,
  1451174, 12681355, 1494781, 1588717, 20390891, 6712913, 86829, 17190790, 1760848, 2773813,
  39537344, 1457633, 39771385, 59508571, 10750, 12468, 4092749, 71616602, 305208380, 421975130,
  100494702, 16954807, 648365168, 38281217, 8260277, 588119189, 57006573, 215240942, 146418213,
  262885565, 12598769, 346906144, 159414169, 55064721, 961220152, 51143125, 1366054355, 40857014,
  1499910119, 87049112, 3375966713, 27730783, 4252856495, 939749977, 739137746, 3994380759,
  12494430, 6535634134, 382011997, 5653239749, 24372301685, 257500636, 20467433661, 921234241871]
/-- Krotov masks `(m = 4, r = 3)`. -/
def rkmMasksPack_m4_r3 : List (List Bool) := [[], [], rkmWbTraj06 1 1, rkmWbTraj06 2 3,
  rkmWbTraj06 2 2, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 3)`. -/
def rkmRowPack_m4_r3 : List ℕ := [178665173, 115095637055, 884725693777]
/-- Krotov masks `(m = 32, r = 60)`. -/
def rkmMasksPack_m32_r60 : List (List Bool) := [rkmWbTraj06 35 25769803776,
  rkmMaskWordsTraj06 6 [25484076, 32], rkmWbTraj06 45 19372892706113,
  rkmMaskWordsTraj06 2 [654993959866986, 3], rkmMaskWordsTraj06 6 [460735500893062, 63],
  rkmMaskWordsTraj06 8 [152322975567322, 210], rkmMaskWordsTraj06 9 [628966498611796, 258], []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 60)`. -/
def rkmRowPack_m32_r60 : List ℕ := [0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 2, 4, 2, 0, 41, 2, 2, 0, 157,
  25, 0, 0, 28, 261, 201, 79, 0, 0, 224, 1, 31027, 16969, 31126, 1354, 97458, 95966, 9988, 5092,
  14430, 182541, 360964, 74459, 1231622, 616599, 15674719, 27170660, 5011587, 23363072, 1999335,
  99023729, 102793641, 182811215, 151698321, 156425831, 861044321, 1576416657, 195126452,
  20161809094, 976436858369]
/-- Krotov masks `(m = 4, r = 35)`. -/
def rkmMasksPack_m4_r35 : List (List Bool) := [rkmWbTraj06 3 7, [], rkmWbTraj06 4 15, [],
  rkmWbTraj06 4 12, rkmWbTraj06 3 4, rkmWbTraj06 4 8, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 35)`. -/
def rkmRowPack_m4_r35 : List ℕ := [17544517590, 96649146531, 880530967235, 1038974716]
/-- Krotov masks `(m = 16, r = 64)`. -/
def rkmMasksPack_m16_r64 : List (List Bool) := [[], rkmWbTraj06 32 2147483669,
  rkmMaskWordsTraj06 13 [562958329048319, 4113], rkmMaskWordsTraj06 3 [137411348440403, 7],
  rkmMaskWordsTraj06 12 [165659344021930, 3289], rkmMaskWordsTraj06 13 [30923734718543, 4096],
  rkmWbTraj06 48 212386805534723, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 64)`. -/
def rkmRowPack_m16_r64 : List ℕ := [3075, 2015, 1077, 23450, 5154, 3265, 555561, 1652183, 2687,
  1906626, 3249610, 2744790, 1171924, 841656, 3263311, 23400290, 275406, 231425, 5646048, 2791127,
  56311, 424838, 6799171, 7199014, 75568, 44228, 210209, 1843011, 176325, 9163678, 4030487,
  46259198, 1152400, 7838560, 5756651, 167473071, 353222, 453, 101237385, 105641962, 415233424,
  146124477, 55519416, 255691440, 590854304, 319672723, 755717092, 13274098, 853322972, 1579191,
  1141205008, 497459811, 448460882, 679372360, 2077234680, 1786652481, 416312086, 2429035598,
  488138961, 4737435607, 27267143048, 54276179, 40107134720, 913949639855]
/-- Krotov masks `(m = 2, r = 5)`. -/
def rkmMasksPack_m2_r5 : List (List Bool) := [[], [], rkmWbTraj06 1 1, rkmWbTraj06 3 6, [], [], [],
  []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 5)`. -/
def rkmRowPack_m2_r5 : List ℕ := [2572266962, 1084636164, 6982044, 408164051637, 588089108129]
/-- Krotov masks `(m = 64, r = 48)`. -/
def rkmMasksPack_m64_r48 : List (List Bool) := [rkmWbTraj06 42 4398046510175,
  rkmWbTraj06 48 246290664394805, rkmWbTraj06 35 31684665317, rkmWbTraj06 40 1093406633356,
  rkmWbTraj06 43 7380220651050, rkmWbTraj06 45 31300458862054, rkmWbTraj06 47 115065081908723, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 48)`. -/
def rkmRowPack_m64_r48 : List ℕ := [4, 0, 0, 0, 1, 1, 10, 32, 45, 26, 53, 14, 0, 1314, 516, 1827,
  2006, 305, 3395, 79, 387, 6799, 3, 52663, 535, 46882, 35751, 76419, 1655537, 5895, 1018148,
  740733, 1268324, 348171, 13835809, 610894, 181912, 5405660, 3527783, 160856476, 19885110,
  1413206783, 1010593693, 484623341, 4271699394, 263848133, 11970181205, 980376276539]
/-- Krotov masks `(m = 16, r = 6)`. -/
def rkmMasksPack_m16_r6 : List (List Bool) := [[], [], [], [], rkmWbTraj06 2 3, rkmWbTraj06 4 13,
  rkmWbTraj06 5 17, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 6)`. -/
def rkmRowPack_m16_r6 : List ℕ := [1054440, 41371971, 42902890, 251896478, 38376984862,
  961285131270]
/-- Krotov masks `(m = 32, r = 41)`. -/
def rkmMasksPack_m32_r41 : List (List Bool) := [[], rkmWbTraj06 9 398, rkmWbTraj06 29 477338011,
  rkmWbTraj06 36 61818185397, rkmWbTraj06 38 234623683235, rkmWbTraj06 39 292767771658,
  rkmWbTraj06 40 555840481794, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 41)`. -/
def rkmRowPack_m32_r41 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 65, 760, 327,
  475, 2117, 145962, 47048, 710560, 56, 1884195, 152, 149, 10220442, 2219768, 2587834, 78987876,
  134039, 61559151, 53402360, 94633096, 568385969, 889853041, 286347028, 20261705763, 977687170700]
/-- Krotov masks `(m = 2, r = 8)`. -/
def rkmMasksPack_m2_r8 : List (List Bool) := [[], [], rkmWbTraj06 3 7, rkmWbTraj06 5 27,
  rkmWbTraj06 6 32, [], rkmWbTraj06 3 4, []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 8)`. -/
def rkmRowPack_m2_r8 : List ℕ := [69436996, 9108, 498620327, 3942312626, 150785882, 3975285858,
  477545635998, 513361744458]
/-- Krotov masks `(m = 64, r = 80)`. -/
def rkmMasksPack_m64_r80 : List (List Bool) := [rkmWbTraj06 18 150528, rkmWbTraj06 32 3579105279,
  rkmWbTraj06 33 4689821696, rkmMaskWordsTraj06 1 [1125898460463103, 1],
  rkmMaskWordsTraj06 10 [1125867986878446, 1023], rkmMaskWordsTraj06 10 [1125822582030330, 1023],
  rkmWbTraj06 37 112948149982, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 80)`. -/
def rkmRowPack_m64_r80 : List ℕ := [2890314, 33400778, 126327922, 94563882, 16957215, 81595997,
  1895127608, 224341799, 754368373, 3235174433, 4130811377, 13541711223, 24397332778, 20658937155,
  5934232, 927363587647, 1550579554, 98718199, 798969737, 870582159, 100733364, 15463755, 59,
  1671668, 22565, 198, 8051, 39, 529, 0, 6, 707, 34, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Krotov masks `(m = 2, r = 26)`. -/
def rkmMasksPack_m2_r26 : List (List Bool) := [[], [], [], []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 26)`. -/
def rkmRowPack_m2_r26 : List ℕ := [12336898, 20927174, 279370622, 583987250, 792190166, 8239949739,
  1354377747, 38091688613, 226952218535, 358737720626, 252793185860, 91987587591, 18119683356,
  1909768125, 99090434, 1942352]
/-- Krotov masks `(m = 64, r = 31)`. -/
def rkmMasksPack_m64_r31 : List (List Bool) := [[], [], rkmWbTraj06 18 144348,
  rkmWbTraj06 23 7644325, rkmWbTraj06 27 127068821, rkmWbTraj06 29 459936242,
  rkmWbTraj06 30 540494234, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 31)`. -/
def rkmRowPack_m64_r31 : List ℕ := [0, 0, 0, 0, 0, 4, 13, 26, 75, 3, 3, 476, 2199, 1742, 21248,
  14118, 4149, 5905, 7, 804828, 2867653, 12, 7093521, 22575764, 2138052, 1490657, 260627262,
  569341272, 108791349, 9322242584, 989701976542]
/-- Krotov masks `(m = 8, r = 11)`. -/
def rkmMasksPack_m8_r11 : List (List Bool) := [[], rkmWbTraj06 6 57, rkmWbTraj06 9 406,
  rkmWbTraj06 10 630, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 11)`. -/
def rkmRowPack_m8_r11 : List ℕ := [3697988, 28506388, 197955390, 379670457, 778312191, 611659778,
  107117820, 5810921280, 374715062, 81288208620, 910418973332]
/-- Krotov masks `(m = 32, r = 30)`. -/
def rkmMasksPack_m32_r30 : List (List Bool) := [rkmWbTraj06 30 939524174, rkmWbTraj06 26 65489591,
  rkmWbTraj06 29 459889321, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 30)`. -/
def rkmRowPack_m32_r30 : List ℕ := [0, 0, 0, 0, 0, 7, 71, 406, 1817, 2192, 5526, 4114, 4114, 30485,
  39046, 111329, 1842784, 718568, 17477492, 66418678, 437938751, 11672768, 476889637, 2577203768,
  1108299208, 3406848569, 6975754915, 14528380, 18953462874, 965950743852]
/-- Krotov masks `(m = 32, r = 12)`. -/
def rkmMasksPack_m32_r12 : List (List Bool) := [rkmWbTraj06 10 786, rkmWbTraj06 11 1194, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 12)`. -/
def rkmRowPack_m32_r12 : List ℕ := [2, 168, 2162, 59583, 393447, 6102474, 31259856, 103583990,
  234446709, 194112104, 19698324645, 979731714752]
/-- Krotov masks `(m = 8, r = 28)`. -/
def rkmMasksPack_m8_r28 : List (List Bool) := [[], [], rkmWbTraj06 10 908, rkmWbTraj06 26 53967879,
  rkmWbTraj06 22 2696703, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 28)`. -/
def rkmRowPack_m8_r28 : List ℕ := [474, 1266228, 2039260, 547543, 87354, 1586914, 6815157, 1468719,
  990578, 4475690, 6257754, 16365430, 17078463, 25635697, 926786, 28058220, 98782962, 22537799,
  65496623, 3691946673, 23754339, 7760697977, 1968777120, 52308339, 36456466496, 337960470,
  86672445765, 862735223508]
/-- Krotov masks `(m = 32, r = 13)`. -/
def rkmMasksPack_m32_r13 : List (List Bool) := [rkmWbTraj06 13 8191, [], rkmWbTraj06 4 14,
  rkmWbTraj06 8 218, rkmWbTraj06 10 878, rkmWbTraj06 11 1109, rkmWbTraj06 12 2198, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 13)`. -/
def rkmRowPack_m32_r13 : List ℕ := [112, 39, 1621, 97380, 16759, 1861001, 710383, 1113109,
  20034292, 30467315, 282778240, 19081080793, 980581838827]
/-- Krotov masks `(m = 16, r = 24)`. -/
def rkmMasksPack_m16_r24 : List (List Bool) := [[], rkmWbTraj06 18 255546, rkmWbTraj06 22 3582510,
  rkmWbTraj06 23 4915304, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 24)`. -/
def rkmRowPack_m16_r24 : List ℕ := [875, 3345, 156, 27168, 131265, 99978, 48105, 130809, 12103,
  416132, 278349, 7130663, 116687945, 459518992, 189887628, 1210337246, 2165872298, 4057970035,
  266136462, 1708380, 10179992920, 52133793, 47994247366, 933297225150]
/-- Krotov masks `(m = 4, r = 15)`. -/
def rkmMasksPack_m4_r15 : List (List Bool) := [[], [], rkmWbTraj06 8 228, rkmWbTraj06 11 1610,
  rkmWbTraj06 13 4618, rkmWbTraj06 10 631, rkmWbTraj06 14 8463, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 15)`. -/
def rkmRowPack_m4_r15 : List ℕ := [416288, 48915018, 3215884, 257716033, 230289831, 413527340,
  191800813, 914170324, 448735095, 4086488238, 6575890156, 3277143387, 87202360, 170931746191,
  812532395813]
/-- Krotov masks `(m = 4, r = 24)`. -/
def rkmMasksPack_m4_r24 : List (List Bool) := [[], [], [], rkmWbTraj06 12 3564,
  rkmWbTraj06 22 3249160, rkmWbTraj06 20 699503, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 24)`. -/
def rkmRowPack_m4_r24 : List ℕ := [11719148, 124941597, 23343410, 192429144, 5294726, 92152178,
  38147110, 156555319, 24888330, 48421572, 4156506, 763868526, 480534479, 1053047256, 401838417,
  2852988797, 525489921, 9024260793, 2341299, 2840100418, 24625930887, 150683939, 183354287075,
  773187530425]
/-- Krotov masks `(m = 16, r = 60)`. -/
def rkmMasksPack_m16_r60 : List (List Bool) := [rkmWbTraj06 16 37408, rkmWbTraj06 15 28160,
  rkmWbTraj06 15 24623, rkmWbTraj06 16 32841, rkmWbTraj06 16 32775, rkmWbTraj06 14 8320,
  rkmWbTraj06 9 348, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 60)`. -/
def rkmRowPack_m16_r60 : List ℕ := [2297444, 497455367, 40693318, 8070603122, 684996, 347130362,
  69444796, 55464426317, 639175956, 31069922490, 40519892934, 862724413628, 8812700, 137173028,
  86182456, 135832201]
/-- Krotov masks `(m = 8, r = 21)`. -/
def rkmMasksPack_m8_r21 : List (List Bool) := [[], rkmWbTraj06 18 203934, rkmWbTraj06 20 617098,
  []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 21)`. -/
def rkmRowPack_m8_r21 : List ℕ := [1129, 40258, 567631, 1083504, 13545, 5226968, 2535432, 33431362,
  335726656, 882247335, 1128402537, 1363097694, 1628005436, 215074023, 649409284, 2923660826,
  11069724661, 7718759998, 585062944, 84963976506, 886493951918]
/-- Krotov masks `(m = 16, r = 16)`. -/
def rkmMasksPack_m16_r16 : List (List Bool) := [[], [], [], rkmWbTraj06 16 65529,
  rkmWbTraj06 9 441, rkmWbTraj06 13 6730, rkmWbTraj06 15 28086, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 16)`. -/
def rkmRowPack_m16_r16 : List ℕ := [57751, 49853, 280092, 16333478, 3684589, 9320872, 27161270,
  10209247, 385261059, 97322146, 412574292, 6251261424, 4059692685, 436916322, 37653627340,
  950636247174]
/-- Cumulative `2`-lane trajectory head invariant (`Traj04` -> `Traj06`). -/
def rkmTrajLaneProp_06 : Prop :=
  rkmTrajLaneProp_04 ∧ (rkmRow_m2_r4.head? = some 120065348)
/-- Proof of `rkmTrajLaneProp_06` in `O(1)` kernel steps. -/
theorem rkmTrajLaneOk_06 : rkmTrajLaneProp_06 :=
  ⟨rkmTrajLaneOk_04, rfl⟩
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
private theorem bZeroMul (z : ℕ) : Nat.mul 0 z = 0 := by
  rw [Nat.mul_eq]
  exact Nat.zero_mul z
private theorem bForceNat_eq {α : Type} (x : ℕ) (k : ℕ → α) :
    HighDForce.withForcedNat x k = k x := by
  unfold HighDForce.withForcedNat
  rw [n1a]
private theorem bForceList_eq {α β : Type} (xs : List α) (k : List α → β) :
    HighDForce.withForcedList xs k = k xs := by
  cases xs <;> rfl
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
private def bNLE : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => cond (bNatEq x y) (bNLE xs ys) false
  | _, _ => false
private theorem bNLE_true : ∀ {xs ys : List ℕ}, bNLE xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    unfold bNLE at h
    revert h
    cases hx : bNatEq x y with
    | false => exact Bool.noConfusion
    | true => exact fun h => congrArg₂ List.cons (bNatEq_true hx) (bNLE_true h)
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
    (h : atF (bNLE x y :: s) = true) : x = y := by
  revert h
  cases h0 : bNLE x y with
  | false => exact Bool.noConfusion
  | true => exact fun _ => bNLE_true h0
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ :=
  Nat.casesOn (motive := fun _ => List ℕ) (Nat.add 1 x) xs fun v =>
    List.casesOn (motive := fun _ => List ℕ) xs [v] fun h t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat
  rw [n1a]
  cases xs <;> rfl
private def uCN4 (a b c d : ℕ) (xs : List ℕ) : List ℕ :=
  Nat.casesOn (motive := fun _ => List ℕ) (Nat.add 1 a) xs fun v1 =>
    Nat.casesOn (motive := fun _ => List ℕ) (Nat.add 1 b) xs fun v2 =>
      Nat.casesOn (motive := fun _ => List ℕ) (Nat.add 1 c) xs fun v3 =>
        Nat.casesOn (motive := fun _ => List ℕ) (Nat.add 1 d) xs fun v4 =>
          List.casesOn (motive := fun _ => List ℕ) xs [v1, v2, v3, v4] fun h t =>
            v1 :: v2 :: v3 :: v4 :: h :: t
private theorem uCN4e (a b c d : ℕ) (xs : List ℕ) :
    uCN4 a b c d xs = uConsNat a (uConsNat b (uConsNat c (uConsNat d xs))) := by
  rw [uConsNat_eq, uConsNat_eq, uConsNat_eq, uConsNat_eq]
  unfold uCN4
  rw [n1a a, n1a b, n1a c, n1a d]
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
  | [], _, h => by
    injection h with h'
    rw [← h']
    rfl
  | Int.negSucc _ :: _, _, h => by
    dsimp only [uToNatHb] at h
    cases h
  | Int.ofNat n :: xs, _, h => by
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
      rw [← h', uConsNat_eq, uOfNatHb, uToNatHb_sound xs ms hxs]
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
  | _ + 1 => by
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
  | succ _ =>
    dsimp only
    rw [bPrimNegSucc_eq, Int.negSucc_eq]
    omega
private theorem bPrimMul_eq (a b : ℤ) : primIntMul a b = a * b := by
  cases a with
  | ofNat _ =>
    cases b with
    | ofNat _ =>
      dsimp only [primIntMul]
      simp only [bPrimOfNat_eq, Nat.mul_eq, Int.ofNat_eq_natCast]
      push_cast
      ring
    | negSucc _ =>
      dsimp only [primIntMul]
      simp only [bPrimNegOfNat_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
  | negSucc _ =>
    cases b with
    | ofNat _ =>
      dsimp only [primIntMul]
      simp only [bPrimNegOfNat_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
    | negSucc _ =>
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
  | ofNat _ =>
    unfold highdStrictConsInt
    dsimp only
    rw [n1a]
    cases xs <;> rfl
  | negSucc _ =>
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
  | ofNat _ =>
    unfold bEnc1 at h
    injection h with h'
    rw [← h', Nat.add_eq, Int.ofNat_eq_natCast]
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
    | succ _ =>
      intro h
      dsimp only at h
      injection h with h'
      rw [← h', Int.negSucc_eq]
      omega
private theorem bEnc_sound (z : ℕ) :
    ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us → bDec z us = xs
  | [], _, h => by
    injection h with h'
    rw [← h']
    rfl
  | x :: xs, _, h => by
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
        rw [← h', uConsNat_eq, bDec_cons, bEnc1_sound z x u hx, bEnc_sound z xs ws hxs]
private def zTdiv (x : ℤ) (d : ℕ) : ℤ := match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.ofNat_eq_natCast]
    omega
  | _ + 1 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.negSucc_eq]
    omega
private theorem bTdivNat_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => by
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
  | succ _ =>
    dsimp only
    rw [Int.negSucc_eq]
    omega
private theorem bRawAdd_eq (a b : ℤ) : muxRawIntAdd a b = a + b := by
  cases a with
  | ofNat _ =>
    cases b with
    | ofNat _ =>
      dsimp only [muxRawIntAdd]
      simp only [bPrimOfNat_eq, Nat.add_eq, Int.ofNat_eq_natCast]
      omega
    | negSucc _ =>
      dsimp only [muxRawIntAdd]
      simp only [bRawSubNat_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
  | negSucc _ =>
    cases b with
    | ofNat _ =>
      dsimp only [muxRawIntAdd]
      simp only [bRawSubNat_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
    | negSucc _ =>
      dsimp only [muxRawIntAdd]
      simp only [bPrimNegSucc_eq, Nat.add_eq, Int.negSucc_eq]
      omega
private theorem bRawNeg_eq (a : ℤ) : muxRawIntNeg a = -a := by
  cases a with
  | ofNat _ =>
    dsimp only [muxRawIntNeg]
    simp only [bNeg_eq, Int.ofNat_eq_natCast]
  | negSucc _ =>
    dsimp only [muxRawIntNeg]
    simp only [bPrimOfNat_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
private theorem bRawSub_eq (a b : ℤ) : muxRawIntSub a b = a - b := by
  unfold muxRawIntSub
  rw [bRawAdd_eq, bRawNeg_eq]
  omega
private theorem bRawMul_eq (a b : ℤ) : muxRawIntMul a b = a * b := by
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
      simp only [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
  | negSucc _ =>
    cases b with
    | ofNat _ =>
      dsimp only [muxRawIntMul]
      simp only [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
    | negSucc _ =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
private theorem bCA1 (x a : ℕ) (f : ℕ → ℕ) :
    Nat.casesOn (motive := fun _ => ℕ) (Nat.add 1 x) a f = f x := by
  rw [n1a x]
private theorem bCSub (p q a : ℕ) (f : ℕ → ℕ) :
    Nat.casesOn (motive := fun _ => ℕ) (Nat.sub q p) a f =
      (match q - p with | 0 => a | d1 + 1 => f d1) := by
  rw [Nat.sub_eq]
  cases q - p <;> rfl
private def bSV (v P Q d : ℕ) : ℕ :=
  Nat.casesOn (motive := fun _ => ℕ) (Nat.add 1 P) 0 fun p =>
    Nat.casesOn (motive := fun _ => ℕ) (Nat.add 1 Q) 0 fun q =>
      Nat.casesOn (motive := fun _ => ℕ) (Nat.sub q p)
        (Nat.add v (Nat.div (Nat.sub p q) d))
        fun d1 => Nat.sub v (Nat.div (Nat.add d1 1) d)
private theorem bSV_m (v P Q d : ℕ) : bSV v P Q d = (match Q - P with
    | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
    | d1 + 1 => Nat.sub v (Nat.div (Nat.add d1 1) d)) := by
  unfold bSV
  rw [bCA1, bCA1, bCSub]
private theorem bSubZ_eq (v q z : ℕ) (hv : 0 < v - q) :
    ((v - q : ℕ) : ℤ) - (z : ℤ) = ((v : ℤ) - (z : ℤ)) + -((q : ℕ) : ℤ) := by
  omega
private theorem bSV_eq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) =
      ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [bSV_m] at hv ⊢
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢
  revert hv
  cases h : Q - P with
  | zero =>
    intro _
    have hpq : (P : ℤ) - (Q : ℤ) = Int.ofNat (P - Q) := by
      rw [Int.ofNat_eq_natCast]
      omega
    rw [hpq]
    dsimp only [zTdiv]
    rw [Int.ofNat_eq_natCast]
    push_cast
    ring
  | succ d1 =>
    intro hv
    have hpq : (P : ℤ) - (Q : ℤ) = Int.negSucc d1 := by
      rw [Int.negSucc_eq]
      omega
    rw [hpq]
    dsimp only [zTdiv] at hv ⊢
    exact bSubZ_eq v ((d1 + 1) / d) z hv
private theorem bSV_self (z p d : ℕ) : bSV z p p d = z := by
  rw [bSV_m, Nat.sub_self]
  dsimp only
  rw [Nat.sub_eq, Nat.sub_self, ndiv, Nat.zero_div, Nat.add_eq]
  omega
private theorem bSV_comm (z a b d : ℕ) : bSV z (Nat.add a b) (Nat.add b a) d = z := by
  have hab : Nat.add a b = Nat.add b a := by
    simp only [Nat.add_eq]
    omega
  rw [hab]
  exact bSV_self z (Nat.add b a) d
private abbrev bCellVal (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bSV v (Nat.add (Nat.mul b0 c0) (Nat.mul b z))
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
  rw [bSV_eq z v _ _ d hv, hpq]
private theorem bCell_nil (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      highdStrictConsInt (muxRawIntAdd ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d)) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bStrictCons_eq, bRawAdd_eq, bTdivNat_eq, bPrimMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [bSV_eq z v _ _ d hv, hpq]
private def bPos : List ℕ → Bool
  | [] => true
  | x :: xs => Nat.casesOn (motive := fun _ => Bool) x false fun _ => bPos xs
private theorem bPos_uCons {x : ℕ} {xs : List ℕ} (h : bPos (uConsNat x xs) = true) :
    0 < x ∧ bPos xs = true := by
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
  | _ :: _ => by
    unfold bHeadOr
    rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | _ :: _ => by
    unfold bTailN
    rw [bDec_cons]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs => match bns with
    | [] => uConsNat (bSV (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSl z d rem 0 z [] (bTailN vs) (bTailN cs))
    | b :: bR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal z d b0 c0 b v (bHeadOr z cT)) (bSl z d rem b c bR vT cT)
      | v :: vT, [] => uConsNat (bCellVal z d b0 c0 b v z) (bSl z d rem b z bR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal z d b0 c0 b z (bHeadOr z cT)) (bSl z d rem b c bR [] cT)
      | [], [] => uConsNat (bCellVal z d b0 c0 b z z) (bSl z d rem b z bR [] [])
private theorem bSl_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bPos (bSl z d rem b0 c0 bns vs cs) = true →
      bDec z (bSl z d rem b0 c0 bns vs cs) =
      muxFastSlideLoopAux d rem (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSl, uOfNatHb, muxFastSlideLoopAux] at h ⊢
      have hp := bPos_uCons h
      have hi := bSl_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp.2
      rw [bPrimMul0 z, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi
      rw [bHeadOr_eq z vs] at hc
      exact hc
    | cons b bR =>
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSl, uOfNatHb] at h ⊢
          rw [bDec_nil]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPos_uCons h
          have hi := bSl_sound z d rem b z bR [] [] hp.2
          rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b z z hp.1 hi
          rw [bZero_eq z] at hc
          exact hc
        | cons c cT =>
          dsimp only [bSl, uOfNatHb] at h ⊢
          rw [bDec_nil, bDec_cons z c cT]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPos_uCons h
          have hi := bSl_sound z d rem b c bR [] cT hp.2
          rw [bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b z (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT, bZero_eq z] at hc
          exact hc
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSl, uOfNatHb] at h ⊢
          rw [bDec_cons z v vT, bDec_nil]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPos_uCons h
          have hi := bSl_sound z d rem b z bR vT [] hp.2
          rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b v z hp.1 hi
          rw [bZero_eq z] at hc
          exact hc
        | cons c cT =>
          dsimp only [bSl, uOfNatHb] at h ⊢
          rw [bDec_cons z v vT, bDec_cons z c cT]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPos_uCons h
          have hi := bSl_sound z d rem b c bR vT cT hp.2
          have hc := bCell_hb z d b0 c0 b v (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT] at hc
          exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uConsNat b (uConsNat (Nat.mul b z) (mkHbZ z bs))
private def bRepZ (z : ℕ) : ℕ → List ℕ
  | 0 => []
  | r + 1 => uConsNat z (bRepZ z r)
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs => match hbz with
    | [] => uConsNat (bSV (bHeadOr z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTailN vs) (bTailN cs))
    | [_] => uConsNat (bSV (bHeadOr z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTailN vs) (bTailN cs))
    | b :: bz :: bR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bSV v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHeadOr z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] =>
        uConsNat (bSV v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT =>
        uConsNat (bSV z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHeadOr z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
      | [], [] => uConsNat (bSV z (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR [] [])
private theorem bSlZ_rep (z d : ℕ) : ∀ (rem p : ℕ) (l : List ℕ),
    bSlZ z d rem p p l [] [] = bRepZ z rem
  | 0, _, _ => rfl
  | rem + 1, p, [] => by
    dsimp only [bSlZ, bHeadOr, bTailN, bRepZ]
    rw [bSV_self z p d, bSlZ_rep z d rem 0 []]
  | rem + 1, p, [_] => by
    dsimp only [bSlZ, bHeadOr, bTailN, bRepZ]
    rw [bSV_self z p d, bSlZ_rep z d rem 0 []]
  | rem + 1, p, _ :: bz :: bR => by
    dsimp only [bSlZ, bRepZ]
    rw [bSV_comm z p bz d, bSlZ_rep z d rem bz bR]
private theorem bSlZ_eq (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs =
      bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, _, _, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTailN vs) (bTailN cs)
      dsimp only [mkHbZ] at hrec
      rw [bZeroMul z] at hrec
      dsimp only [mkHbZ, bSlZ, bSl]
      rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ]
      rw [uConsNat_eq, uConsNat_eq]
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSl, bCellVal]
          rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCellVal]
          rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSl, bCellVal]
          rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCellVal]
          rw [bSlZ_eq z d rem b c bR vT cT]
private theorem bSlZ_consC (z d rem p0 q0 b bz : ℕ) (bR vs : List ℕ) (c : ℕ) (cT : List ℕ) :
    bSlZ z d (rem + 1) p0 q0 (b :: bz :: bR) vs (c :: cT) =
      uConsNat (bSV (bHeadOr z vs) (Nat.add p0 bz) (Nat.add (Nat.mul b (bHeadOr z cT)) q0) d)
        (bSlZ z d rem (Nat.mul b c) bz bR (bTailN vs) cT) := by
  cases vs <;> rfl
private theorem bSlZ_step2 (z d r p0 q0 b bz : ℕ) (l1 l2 vs cs : List ℕ)
    (h : ∀ p q v c, bSlZ z d r p q l1 v c = bSlZ z d r p q l2 v c) :
    bSlZ z d (r + 1) p0 q0 (b :: bz :: l1) vs cs =
      bSlZ z d (r + 1) p0 q0 (b :: bz :: l2) vs cs := by
  cases vs with
  | nil =>
    cases cs with
    | nil =>
      dsimp only [bSlZ]
      rw [h]
    | cons _ _ =>
      dsimp only [bSlZ]
      rw [h]
  | cons _ _ =>
    cases cs with
    | nil =>
      dsimp only [bSlZ]
      rw [h]
    | cons _ _ =>
      dsimp only [bSlZ]
      rw [h]
private theorem bSlZ1_eq (z d b1 z1 : ℕ) (l : List ℕ) (p0 q0 : ℕ) (vs cs : List ℕ) :
    bSlZ z d 1 p0 q0 [b1, z1] vs cs = bSlZ z d 1 p0 q0 (b1 :: z1 :: l) vs cs :=
  bSlZ_step2 z d 0 p0 q0 b1 z1 [] l vs cs (fun _ _ _ _ => rfl)
private theorem bSlZ2_eq (z d b1 z1 b2 z2 : ℕ) (l : List ℕ) (p0 q0 : ℕ) (vs cs : List ℕ) :
    bSlZ z d 2 p0 q0 [b1, z1, b2, z2] vs cs =
      bSlZ z d 2 p0 q0 (b1 :: z1 :: b2 :: z2 :: l) vs cs :=
  bSlZ_step2 z d 1 p0 q0 b1 z1 [b2, z2] (b2 :: z2 :: l) vs cs
    (fun p q v c => bSlZ1_eq z d b2 z2 l p q v c)
private theorem bSlZ3_eq (z d b1 z1 b2 z2 b3 z3 : ℕ) (l : List ℕ) (p0 q0 : ℕ) (vs cs : List ℕ) :
    bSlZ z d 3 p0 q0 [b1, z1, b2, z2, b3, z3] vs cs =
      bSlZ z d 3 p0 q0 (b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: l) vs cs :=
  bSlZ_step2 z d 2 p0 q0 b1 z1 [b2, z2, b3, z3] (b2 :: z2 :: b3 :: z3 :: l) vs cs
    (fun p q v c => bSlZ2_eq z d b2 z2 b3 z3 l p q v c)
private theorem bSlZ4p_eq (z d b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (l : List ℕ)
    (p0 q0 : ℕ) (vs cs : List ℕ) :
    bSlZ z d 4 p0 q0 [b1, z1, b2, z2, b3, z3, b4, z4] vs cs =
      bSlZ z d 4 p0 q0 (b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: l) vs cs :=
  bSlZ_step2 z d 3 p0 q0 b1 z1 [b2, z2, b3, z3, b4, z4]
    (b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: l) vs cs
    (fun p q v c => bSlZ3_eq z d b2 z2 b3 z3 b4 z4 l p q v c)
private inductive HbZ4 : Type
  | tail : List ℕ → HbZ4
  | c4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → HbZ4 → HbZ4
private abbrev hbz4Cons (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (xs : List ℕ) : List ℕ :=
  b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: xs
private def hbz4L : HbZ4 → List ℕ
  | HbZ4.tail l => l
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4Cons b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L r)
private def c4S (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (r : HbZ4) : HbZ4 :=
  Nat.casesOn (motive := fun _ => HbZ4) (Nat.add 1 z1) r fun u1 =>
    Nat.casesOn (motive := fun _ => HbZ4) (Nat.add 1 z2) r fun u2 =>
      Nat.casesOn (motive := fun _ => HbZ4) (Nat.add 1 z3) r fun u3 =>
        Nat.casesOn (motive := fun _ => HbZ4) (Nat.add 1 z4) r fun u4 =>
          HbZ4.casesOn (motive := fun _ => HbZ4) r
            (fun l => HbZ4.c4 b1 u1 b2 u2 b3 u3 b4 u4 (HbZ4.tail l))
            (fun a1 a2 a3 a4 a5 a6 a7 a8 t =>
              HbZ4.c4 b1 u1 b2 u2 b3 u3 b4 u4 (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t))
private theorem c4Se (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (r : HbZ4) :
    c4S b1 z1 b2 z2 b3 z3 b4 z4 r = HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r := by
  unfold c4S
  rw [n1a z1, n1a z2, n1a z3, n1a z4]
  cases r <;> rfl
private def fH4 {α : Type} (h : HbZ4) (k : HbZ4 → α) : α :=
  HbZ4.casesOn (motive := fun _ => α) h
    (fun l => fL l fun lF => k (HbZ4.tail lF))
    (fun a1 a2 a3 a4 a5 a6 a7 a8 r => k (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r))
private theorem fH4e {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ =>
    dsimp only [fH4, fL]
    rw [bForceList_eq]
  | c4 _ _ _ _ _ _ _ _ _ => rfl
private def mkHbZ4 (z : ℕ) : List ℕ → HbZ4
  | b1 :: b2 :: b3 :: b4 :: bs =>
    c4S b1 (Nat.mul b1 z) b2 (Nat.mul b2 z) b3 (Nat.mul b3 z) b4 (Nat.mul b4 z) (mkHbZ4 z bs)
  | bs => HbZ4.tail (mkHbZ z bs)
private theorem hbz4L_mk (z : ℕ) : ∀ (bns : List ℕ), hbz4L (mkHbZ4 z bns) = mkHbZ z bns
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: bs => by
    dsimp only [mkHbZ4, mkHbZ]
    rw [c4Se]
    dsimp only [hbz4L, hbz4Cons]
    rw [hbz4L_mk z bs]
    simp only [uConsNat_eq]
private def bSlZ4Rem (z d b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (bR : HbZ4)
    (r0 p0 q0 : ℕ) (vs cs : List ℕ) : List ℕ :=
  Nat.casesOn (motive := fun _ => List ℕ) r0
    (bSlZ z d 4 p0 q0 [b1, z1, b2, z2, b3, z3, b4, z4] vs cs)
    fun r0p =>
      bSlZ z d (((((r0p + 1) + 1) + 1) + 1) + 1) p0 q0
        (hbz4Cons b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
private theorem bSlZ4Rem_eq (z d b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (bR : HbZ4)
    (r0 p0 q0 : ℕ) (vs cs : List ℕ) :
    bSlZ4Rem z d b1 z1 b2 z2 b3 z3 b4 z4 bR r0 p0 q0 vs cs =
      bSlZ z d ((((r0 + 1) + 1) + 1) + 1) p0 q0
        (hbz4Cons b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs := by
  cases r0 with
  | zero => exact bSlZ4p_eq z d b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR) p0 q0 vs cs
  | succ _ => rfl
private abbrev bQ4 (d b1 z1 b2 z2 b3 z3 b4 z4 p0 q0 v1 v2 v3 v4 c1 c2 c3 c4 c5 : ℕ)
    (tail : List ℕ) : List ℕ :=
  uCN4
    (bSV v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
    (bSV v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
    (bSV v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
    (bSV v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 c5) z3) d)
    tail
private def bT4 (vs : List ℕ) : List ℕ :=
  List.casesOn (motive := fun _ => List ℕ) vs [] fun _ s1 =>
    List.casesOn (motive := fun _ => List ℕ) s1 [] fun _ s2 =>
      List.casesOn (motive := fun _ => List ℕ) s2 [] fun _ s3 =>
        List.casesOn (motive := fun _ => List ℕ) s3 [] fun _ vR => vR
private theorem bT4_eq (vs : List ℕ) : bT4 vs = bTailN (bTailN (bTailN (bTailN vs))) := by
  cases vs with
  | nil => rfl
  | cons _ s1 =>
    cases s1 with
    | nil => rfl
    | cons _ s2 =>
      cases s2 with
      | nil => rfl
      | cons _ s3 =>
        cases s3 <;> rfl
private def bU4 (z d b1 z1 b2 z2 b3 z3 b4 z4 p0 q0 : ℕ) (vs : List ℕ)
    (c1 c2 c3 c4 c5 : ℕ) (tail : List ℕ) : List ℕ :=
  List.casesOn (motive := fun _ => List ℕ) vs
    (bQ4 d b1 z1 b2 z2 b3 z3 b4 z4 p0 q0 z z z z c1 c2 c3 c4 c5 tail)
    fun v1 vs1 =>
      List.casesOn (motive := fun _ => List ℕ) vs1
        (bQ4 d b1 z1 b2 z2 b3 z3 b4 z4 p0 q0 v1 z z z c1 c2 c3 c4 c5 tail)
        fun v2 vs2 =>
          List.casesOn (motive := fun _ => List ℕ) vs2
            (bQ4 d b1 z1 b2 z2 b3 z3 b4 z4 p0 q0 v1 v2 z z c1 c2 c3 c4 c5 tail)
            fun v3 vs3 =>
              List.casesOn (motive := fun _ => List ℕ) vs3
                (bQ4 d b1 z1 b2 z2 b3 z3 b4 z4 p0 q0 v1 v2 v3 z c1 c2 c3 c4 c5 tail)
                fun v4 _ =>
                  bQ4 d b1 z1 b2 z2 b3 z3 b4 z4 p0 q0 v1 v2 v3 v4 c1 c2 c3 c4 c5 tail
private theorem bU4_eq (z d b1 z1 b2 z2 b3 z3 b4 z4 p0 q0 : ℕ) (vs : List ℕ)
    (c1 c2 c3 c4 c5 : ℕ) (tail : List ℕ) :
    bU4 z d b1 z1 b2 z2 b3 z3 b4 z4 p0 q0 vs c1 c2 c3 c4 c5 tail =
      bQ4 d b1 z1 b2 z2 b3 z3 b4 z4 p0 q0 (bHeadOr z vs)
        (bHeadOr z (bTailN vs)) (bHeadOr z (bTailN (bTailN vs)))
        (bHeadOr z (bTailN (bTailN (bTailN vs)))) c1 c2 c3 c4 c5 tail := by
  cases vs with
  | nil => rfl
  | cons _ vs1 =>
    cases vs1 with
    | nil => rfl
    | cons _ vs2 =>
      cases vs2 with
      | nil => rfl
      | cons _ vs3 =>
        cases vs3 <;> rfl
private def bSlZ4 (z d : ℕ) : HbZ4 → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | HbZ4.tail l, rem, p0, q0, vs, cs => bSlZ z d rem p0 q0 l vs cs
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR, rem, p0, q0, vs, cs =>
    Nat.casesOn (motive := fun _ => List ℕ) rem [] fun r3 =>
      Nat.casesOn (motive := fun _ => List ℕ) r3
        (bSlZ z d 1 p0 q0 [b1, z1] vs cs) fun r2 =>
        Nat.casesOn (motive := fun _ => List ℕ) r2
          (bSlZ z d 2 p0 q0 [b1, z1, b2, z2] vs cs) fun r1 =>
          Nat.casesOn (motive := fun _ => List ℕ) r1
            (bSlZ z d 3 p0 q0 [b1, z1, b2, z2, b3, z3] vs cs) fun r0 =>
            List.casesOn (motive := fun _ => List ℕ) cs
              (List.casesOn (motive := fun _ => List ℕ) vs
                (uCN4 (bSV z (Nat.add p0 z1) (Nat.add z1 q0) d) z z z (bRepZ z r0))
                fun v vT => bSlZ4Rem z d b1 z1 b2 z2 b3 z3 b4 z4 bR r0 p0 q0 (v :: vT) [])
              fun c1 cs1 =>
                List.casesOn (motive := fun _ => List ℕ) cs1
                  (bSlZ4Rem z d b1 z1 b2 z2 b3 z3 b4 z4 bR r0 p0 q0 vs [c1])
                  fun c2 cs2 =>
                    List.casesOn (motive := fun _ => List ℕ) cs2
                      (bSlZ4Rem z d b1 z1 b2 z2 b3 z3 b4 z4 bR r0 p0 q0 vs [c1, c2])
                      fun c3 cs3 =>
                        List.casesOn (motive := fun _ => List ℕ) cs3
                          (bSlZ4Rem z d b1 z1 b2 z2 b3 z3 b4 z4 bR r0 p0 q0 vs [c1, c2, c3])
                          fun c4 cT =>
                            Nat.casesOn (motive := fun _ => List ℕ)
                              (Nat.add 1 (Nat.mul b4 c4)) [] fun p4 =>
                              Nat.casesOn (motive := fun _ => List ℕ)
                                (Nat.add 1 (bHeadOr z cT)) [] fun c5 =>
                                fL (bT4 vs) fun vNext =>
                                  bU4 z d b1 z1 b2 z2 b3 z3 b4 z4 p0 q0 vs c1 c2 c3 c4 c5
                                    (bSlZ4 z d bR r0 p4 z4 vNext cT)
private theorem bSlZ4_eq (z d : ℕ) : ∀ (hbz : HbZ4) (rem p0 q0 : ℕ) (vs cs : List ℕ),
    bSlZ4 z d hbz rem p0 q0 vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs
  | HbZ4.tail _, _, _, _, _, _ => rfl
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR, rem, p0, q0, vs, cs => by
    cases rem with
    | zero => rfl
    | succ r3 =>
      cases r3 with
      | zero => exact bSlZ1_eq z d b1 z1 (b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: hbz4L bR) p0 q0 vs cs
      | succ r2 =>
        cases r2 with
        | zero => exact bSlZ2_eq z d b1 z1 b2 z2 (b3 :: z3 :: b4 :: z4 :: hbz4L bR) p0 q0 vs cs
        | succ r1 =>
          cases r1 with
          | zero => exact bSlZ3_eq z d b1 z1 b2 z2 b3 z3 (b4 :: z4 :: hbz4L bR) p0 q0 vs cs
          | succ r0 =>
            cases cs with
            | nil =>
              cases vs with
              | nil =>
                dsimp only [bSlZ4, hbz4L, hbz4Cons, bSlZ]
                rw [uCN4e, bSV_comm z z1 z2 d, bSV_comm z z2 z3 d,
                  bSV_comm z z3 z4 d, bSlZ_rep z d r0 z4 (hbz4L bR)]
              | cons v vT =>
                exact bSlZ4Rem_eq z d b1 z1 b2 z2 b3 z3 b4 z4 bR r0 p0 q0 (v :: vT) []
            | cons c1 cs1 =>
              cases cs1 with
              | nil => exact bSlZ4Rem_eq z d b1 z1 b2 z2 b3 z3 b4 z4 bR r0 p0 q0 vs [c1]
              | cons c2 cs2 =>
                cases cs2 with
                | nil => exact bSlZ4Rem_eq z d b1 z1 b2 z2 b3 z3 b4 z4 bR r0 p0 q0 vs [c1, c2]
                | cons c3 cs3 =>
                  cases cs3 with
                  | nil =>
                    exact bSlZ4Rem_eq z d b1 z1 b2 z2 b3 z3 b4 z4 bR r0 p0 q0 vs [c1, c2, c3]
                  | cons c4 cT =>
                    dsimp only [bSlZ4, hbz4L, hbz4Cons, fL]
                    rw [n1a (Nat.mul b4 c4), n1a (bHeadOr z cT)]
                    dsimp only
                    rw [bForceList_eq, bU4_eq, bT4_eq]
                    dsimp only [bQ4]
                    rw [uCN4e, bSlZ_consC, bSlZ_consC, bSlZ_consC, bSlZ_consC]
                    dsimp only [bHeadOr]
                    exact congrArg (fun r => uConsNat _ (uConsNat _ (uConsNat _ (uConsNat _ r))))
                      (bSlZ4_eq z d bR r0 (Nat.mul b4 c4) z4
                        (bTailN (bTailN (bTailN (bTailN vs)))) cT)
private def bStg (z dg mL : ℕ) (hbz : HbZ4) (vns cns : List ℕ) : Option (List ℕ) :=
  fN (highdNatMin mL (Nat.add (altListLen cns) 1)) fun nL =>
    fN (Nat.mul dg wdScale) fun d =>
      fL (bSlZ4 z d hbz nL 0 0 vns cns) fun out => cond (bPos out) (some out) none
private theorem bStg_sound (z dg mL : ℕ) (bns vns cns out : List ℕ)
    (h : bStg z dg mL (mkHbZ4 z bns) vns cns = some out) :
    bDec z out = muxFastHornerStage dg mL (uOfNatHb bns) (bDec z vns) (bDec z cns) := by
  unfold bStg at h
  dsimp only [fN, fL] at h
  rw [bForceNat_eq, bForceNat_eq, bForceList_eq] at h
  let nL := highdNatMin mL (Nat.add (altListLen cns) 1)
  let d := Nat.mul dg wdScale
  have hsl := bSlZ_eq z d nL 0 z bns vns cns
  rw [bZeroMul z] at hsl
  rw [bSlZ4_eq, hbz4L_mk, hsl] at h
  revert h
  cases hp : bPos (bSl z d nL 0 z bns vns cns) with
  | false =>
    intro h
    dsimp only [cond] at h
    cases h
  | true =>
    intro h
    dsimp only [cond] at h
    injection h with h'
    rw [← h']
    unfold muxFastHornerStage
    rw [bDec_len z cns, bForceNat_eq, bForceNat_eq, ← bPrimMul0 z]
    exact bSl_sound z d nL 0 z bns vns cns hp
private def bBind (x : Option (List ℕ)) (k : List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  match x with | none => none | some out => k out
private theorem bBind_sound {z dg mL : ℕ} {bns vns cns out : List ℕ}
    {kB : List ℕ → Option (List ℕ)} {kU : List ℤ → List ℤ}
    (h : bBind (bStg z dg mL (mkHbZ4 z bns) vns cns) kB = some out)
    (hk : ∀ (mid : List ℕ), kB mid = some out → bDec z out = kU (bDec z mid)) :
    bDec z out = HighDForce.withForcedList
      (muxFastHornerStage dg mL (uOfNatHb bns) (bDec z vns) (bDec z cns)) kU := by
  unfold bBind at h
  revert h
  cases hs : bStg z dg mL (mkHbZ4 z bns) vns cns with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some mid =>
    intro h
    dsimp only at h
    rw [bForceList_eq, ← bStg_sound z dg mL bns vns cns mid hs]
    exact hk mid h
private def bStep (z mL : ℕ) (hbz : HbZ4) (vns : List ℕ) : Option (List ℕ) :=
  bBind (bStg z 16 mL hbz vns vns) fun c1 => bBind (bStg z 15 mL hbz vns c1) fun c2 =>
  bBind (bStg z 14 mL hbz vns c2) fun c3 => bBind (bStg z 13 mL hbz vns c3) fun c4 =>
  bBind (bStg z 12 mL hbz vns c4) fun c5 => bBind (bStg z 11 mL hbz vns c5) fun c6 =>
  bBind (bStg z 10 mL hbz vns c6) fun c7 => bBind (bStg z 9 mL hbz vns c7) fun c8 =>
  bBind (bStg z 8 mL hbz vns c8) fun c9 => bBind (bStg z 7 mL hbz vns c9) fun ca =>
  bBind (bStg z 6 mL hbz vns ca) fun cb => bBind (bStg z 5 mL hbz vns cb) fun cc =>
  bBind (bStg z 4 mL hbz vns cc) fun cd => bBind (bStg z 3 mL hbz vns cd) fun ce =>
  bBind (bStg z 2 mL hbz vns ce) fun cf => bStg z 1 mL hbz vns cf
private theorem bStep_sound (z mL : ℕ) (bns vns out : List ℕ)
    (h : bStep z mL (mkHbZ4 z bns) vns = some out) :
    bDec z out = muxFastHornerT16Step mL (uOfNatHb bns) (bDec z vns) := by
  unfold bStep at h
  unfold muxFastHornerT16Step
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  exact bStg_sound _ _ _ _ _ _ _ h
private def bItH (z : ℕ) : ℕ → ℕ → HbZ4 → List ℕ → Option (List ℕ)
  | 0, _, _, vns => some vns
  | k + 1, mL, hbz, vns => match bStep z mL hbz vns with
    | none => none
    | some vNext => bItH z k mL hbz vNext
private theorem bItH_sound (z : ℕ) : ∀ (k mL : ℕ) (bns vns out : List ℕ),
    bItH z k mL (mkHbZ4 z bns) vns = some out →
    bDec z out = muxFastIterFullT16 k mL (uOfNatHb bns) (bDec z vns)
  | 0, _, _, _, _, h => by
    dsimp only [bItH] at h
    injection h with h'
    rw [← h']
    rfl
  | k + 1, mL, bns, vns, out, h => by
    dsimp only [bItH] at h
    revert h
    cases hs : bStep z mL (mkHbZ4 z bns) vns with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some vNext =>
      intro h
      dsimp only at h
      unfold muxFastIterFullT16
      rw [bForceList_eq, ← bStep_sound z mL bns vns vNext hs]
      exact bItH_sound z k mL bns vNext out h
private def bIter (z k mL : ℕ) (bns vns : List ℕ) : Option (List ℕ) :=
  fH4 (mkHbZ4 z bns) fun hbz => bItH z k mL hbz vns
private theorem bIter_sound (z k mL : ℕ) (bns vns out : List ℕ)
    (h : bIter z k mL bns vns = some out) :
    bDec z out = muxFastIterFullT16 k mL (uOfNatHb bns) (bDec z vns) := by
  unfold bIter at h
  rw [fH4e] at h
  exact bItH_sound z k mL bns vns out h
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
private def fSp : List ℕ → List ℕ
  | [] => []
  | x :: xs => uConsNat x (fSp xs)
private theorem fSp_eq : ∀ (xs : List ℕ), fSp xs = xs
  | [] => rfl
  | x :: xs => by
    dsimp only [fSp]
    rw [uConsNat_eq, fSp_eq xs]
private def bSlideChk (k mL : ℕ) (bns vns out : List ℕ) : Bool :=
  fL (fSp vns) fun vF => fL (fSp out) fun oF =>
    match bIter zB k mL bns vF with | none => false | some w => bNLE w oF
private theorem bSlideChk_sound {k mL : ℕ} {bns vns out : List ℕ} {s : List Bool}
    (h : atF (bSlideChk k mL bns vns out :: s) = true) :
    WalkOk (some (k, mL, bns, vns, out)) := by
  unfold bSlideChk at h
  dsimp only [fL] at h
  rw [bForceList_eq, bForceList_eq, fSp_eq, fSp_eq] at h
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
    | mk aP _ => cases nS <;> cases dE <;> cases aP <;> rfl
private theorem bhW_eq {m lm r : ℕ} {ls ts ns : List ℕ} {mks : List (List Bool)}
    {wcs : List WalkCert} {y : List ℕ} {s : List Bool}
    (h : atF (bNLE (bEvalLo12W m lm r ls ts ns mks wcs) y :: s) = true)
    (hw : WalksOk wcs) : rkmEvalT16Lo12 m lm r ls ts ns mks = y :=
  (bEvalLo12W_eq m lm r ls ts ns mks wcs hw).symm.trans (bhd_eq h)
private theorem bh0_eq {m lm r : ℕ} {ls ts ns : List ℕ} {mks : List (List Bool)}
    {y : List ℕ} {s : List Bool}
    (h : atF (bNLE (bEvalLo12W m lm r ls ts ns mks []) y :: s) = true) :
    rkmEvalT16Lo12 m lm r ls ts ns mks = y := bhW_eq h wNil
private def wc_rkmTraj_m8_r128_s4_hb_p0 : List ℕ := [151798452589980,213091433329404,
  259042597174215,296876397996913,329413183510795,358110202873095,383839435679374,407173097484386,
  428511464374850,448148016442522,466305844740183,483159460835557,498848591068752,513487291361465,
  527170190955475,539976900654031,551975206250425,563223433780583,573772235538518,583665961799034,
  592943730319431,601640271477584,609786604214989,617410582575455,624537342001044,631189667068865,
  637388297006033,643152181441321,648498696000000,653443825225186,658002318710322,662187825110951,
  666013007769156,669489644959172,672628717195792,675440483600273,677934548963587,680119922862941,
  682005071959015,683597966416233,684906121237515,685936633181380,686696213827437,687191219272022,
  687427676865620,687411309345127,687147556664858,686641595788757,685898358671226,684922548624222,
  683718655242889,682290968040304,680643588923274,678780443625066,676705292197127,674421738649775,
  671933239821459,669243113547006,666354546187336,663270599576102,659994217432537,656528231284326,
  652875365939487,649038244541897]
private def wc_rkmTraj_m8_r128_s4_hb_p1 : List ℕ := [645019393241250,640821245504728,
  636446146094504,631896354732342,627174049469853,622281329780579,617220219387697,611992668839021,
  606600557838829,601045697344031,595329831430147,589454638930568,583421734850431,577232671554350,
  570888939724867,564391969086094,557743128884274,550943728114013,543995015475586,536898179044897,
  529654345633318,522264579809544,514729882549703,507051189474980,499229368627773,491265217727522,
  483159460835557,474912744344007,466525632186465,457998600146920,449332029117436,440526197122829,
  431581269890651,422497289694655,413274162136915,403911640453834,394409306829219,384766550066299,
  374982538800301,365056189210452,354986125896347,344770634191775,334407601661391,323894445806703,
  313228024016504,302404520411387,291419302267478,280266735874082,268939947529830,257430509177390,
  245728018697953,233819530049953,221688764568188,209314995124450,196671426697113,183722774644078,
  170421511603528,156701793428718,142469084942366,127581177375847,111810120000000,94755366114518,
  75602163604054,52156754486150]
private def wc_rkmTraj_m8_r128_s4_hb : List ℕ := pCat wc_rkmTraj_m8_r128_s4_hb_p0
  wc_rkmTraj_m8_r128_s4_hb_p1
private def wc_rkmTraj_m8_r128_s4_v0_p0 : List ℕ := [1999887403574053,2000269025306824,
  1999573510528234,1999496092635532,1999557257578580,1999755094334264,1999975848027457,
  2000267190936504,1999599315390325,1999611542113379,2000249085448865,2000039086720812,
  2000174957241670,1999659214161395,1999567290175368,1999548859474123,1999585812345895,
  1999653012811645,2000270890191568,2000187533914492,2000043037367416,2000350772645382,
  2001458047995516,2004215364450237,2010216443240076,2021749285436908,2041518495665741,
  2071950053157242,2114156432673710,2166877710284202,2225876184814510,2284212319614014,
  2333530001725707,2366042944245235,2376561947850699,2363833211468207,2330721235519511,
  2283233983882889,2228819972128419,2174571301693578,2125886525196617,2085871506945664,
  2055445008294381,2033903738632392,2019641917984134,2010784599313162,2005613001812892,
  2002769489792074,2001295433537764,2000574371354129,2000241344085192,2000096072885424,
  2000036214793189,1999987080814695,1999995641594616,2000001389223427,2000000417923726,
  2000000118505605,2000000031624743,2000000007928003,2000000001862938,2000000000409254,
  2000000000083783,2000000000015920]
private def wc_rkmTraj_m8_r128_s4_v0_p1 : List ℕ := [2000000000002791,2000000000000447,
  2000000000000063,2000000000000007,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m8_r128_s4_v0 : List ℕ := pCat wc_rkmTraj_m8_r128_s4_v0_p0
  wc_rkmTraj_m8_r128_s4_v0_p1
private def wc_rkmTraj_m8_r128_s4_v1_p0 : List ℕ := [2000063735172537,1999689408547927,
  1999952010541833,2000013555045163,1999948402123873,1999724170249071,1999613832700239,
  1999877336250455,2000153767452341,2000107750516566,1999973046512283,2000008336295870,
  2000091142557179,2000089967309618,2000107965650668,2000183350448911,2000129692730628,
  1999841781205623,1999520900918419,1999440398499370,1999616290028006,1999831267906670,
  1999919508679845,1999904641316169,1999895067934159,1999903697326028,1999885658326889,
  1999795175539702,1999726371438690,1999745433849096,1999906467228325,2000108276726542,
  2000234898976569,2000220773917773,2000057750400662,1999850194454104,1999682762733536,
  1999598288960841,1999616394655626,1999683136046922,1999749270582336,1999819902026685,
  1999913022279665,2000072615264197,2000314946027178,2000485265826263,2000235444983801,
  1999165367622476,1997113225518480,1994645274928881,1993558480384154,1997000583909565,
  2008976694015890,2033274399895101,2072040324143130,2124484049116437,2186311598434534,
  2250253050393124,2307576448784090,2350101205093919,2372080607652971,2371390113983759,
  2349706252299807,2311724028083376]
private def wc_rkmTraj_m8_r128_s4_v1_p1 : List ℕ := [2263779724775719,2212371057254403,
  2162980559716856,2119410222524877,2083638107542752,2056072381825759,2036019240106216,
  2022188977476305,2013116856042843,2007443268177612,2004054774130539,2002120097910524,
  2001063571240058,2000511669211019,2000235944346255,2000104242252001,2000044113130087,
  2000017878801538,2000006940748466,2000002581813290,2000000920773598,2000000315104091,
  2000000103583674,2000000032750296,2000000009973420,2000000002929770,2000000000831445,
  2000000000228263,2000000000060687,2000000000015634,2000000000003900,2000000000000939,
  2000000000000216,2000000000000046,2000000000000008,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m8_r128_s4_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m8_r128_s4_v1 : List ℕ := pCat wc_rkmTraj_m8_r128_s4_v1_p0 (pCat
  wc_rkmTraj_m8_r128_s4_v1_p1 wc_rkmTraj_m8_r128_s4_v1_p2)
private def wc_rkmTraj_m8_r128_s4_v2_p0 : List ℕ := [2000004922708072,2000017046608558,
  2000039982199291,2000069399161787,2000099410709034,2000108673378019,2000105558542538,
  2000075245522055,2000060727827399,2000044960719782,2000034260276670,2000000570356004,
  1999918970498789,1999834874316215,1999792519952455,1999836463677235,1999968353831169,
  2000096879018491,2000138967733064,2000077103140136,1999947036256592,1999837575155459,
  1999806533191733,1999818975688178,1999825489521416,1999818687947185,1999821030004355,
  1999875601052185,1999988748972418,2000083006991678,2000078448873650,1999983243802069,
  1999874808977464,1999846454683010,1999950206493538,2000135348494407,2000280679809551,
  2000308560199798,2000227623537974,2000088976151176,1999949916916403,1999845908609533,
  1999766484789155,1999690118224119,1999638569377130,1999655719738513,1999747932064367,
  1999875938289742,1999980547968931,2000002130676336,1999916258027364,1999769891185534,
  1999654838634111,1999638109273333,1999731249170782,1999904352019496,2000094635665082,
  2000215931308077,2000202334766295,2000059506564744,1999873324136877,1999768963190316,
  1999831876298046,2000005710716598]
private def wc_rkmTraj_m8_r128_s4_v2_p1 : List ℕ := [2000048199588459,1999674931997842,
  1998892317772812,1998265959131353,1998762917868288,2001037574990915,2004497809083933,
  2006865928149407,2004901734646010,1996358437280038,1982348783321158,1968691784171720,
  1965031408818727,1981603012568280,2024876185350023,2094081984835131,2180336423182007,
  2268865753651165,2343409819344110,2390981581852970,2405182980813760,2387085671710691,
  2343779403967446,2285527849715716,2222746881790953,2163760231411603,2113749536358344,
  2074799672652066,2046637020602096,2027603228448625,2015522992718694,2008299614226908,
  2004220807623152,2002042197574684,2000940168534934,2000411814341442,2000171599163847,
  2000068003423156,2000025620657181,2000009172683141,2000003118990568,2000001006631205,
  2000000308143814,2000000089394286,2000000024555021,2000000006379623,2000000001565904,
  2000000000362635,2000000000079109,2000000000016223,2000000000003119,2000000000000558,
  2000000000000090,2000000000000011,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m8_r128_s4_v2_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m8_r128_s4_v2 : List ℕ := pCat wc_rkmTraj_m8_r128_s4_v2_p0 (pCat
  wc_rkmTraj_m8_r128_s4_v2_p1 wc_rkmTraj_m8_r128_s4_v2_p2)
private def wc_rkmTraj_m8_r128_s6_hb_p0 : List ℕ := [137042122825646,192645682612161,
  234518900893995,269155120786718,299085472083734,325615885129899,349526683148418,371329207628296,
  391380642519770,409942497201268,427213271715682,443348013381468,458470678892697,472682298071351,
  486066562891579,498693771199197,510623681981000,521907628931587,532590115491490,542710039175123,
  552301645587405,561395281851746,570017998835906,578194037783089,585945227434572,593291311033712,
  600250217815077,606838290111194,613070474657752,618960484779075,624520938706272,629763478193058,
  634698870758882,639337098241450,643687433834387,647758509386786,651558374424552,655094548100125,
  658374065073274,661403516160485,664189084455950,666736577516890,669051456115184,671138859982091,
  673003630910310,674650333525403,676083273994689,677306516904770,678323900507498,679139050507605,
  679755392542460,680176163484977,680404421683917,680443056241368,680294795414629,679962214218798,
  679447741296766,678753665114937,677882139535531,676835188809722,675614712029953,674222487074431,
  672660174071963,670929318410877]
private def wc_rkmTraj_m8_r128_s6_hb_p1 : List ℕ := [669031353311637,666967601978957,
  664739279345558,662347493416232,659793246217470,657077434354586,654200849174862,651164176531841,
  647967996142350,644612780524111,641098893497842,637426588233514,633596004815761,629607167298368,
  625459980212043,621154224483344,616689552715407,612065483772947,607281396604607,602336523224938,
  597229940765777,591960562492210,586527127661281,580928190081598,575162105208302,569227015579879,
  563120834369818,556841226786133,550385589003602,543751024255327,536934315639446,529931895110285,
  522739808016895,515353672420382,507768632257812,499979303215457,491979709915557,483763212692122,
  475322421810212,466649096439123,457734024980519,448566882418510,439136059115765,429428453806853,
  419429221260523,409121461934480,398485836534281,387500082104706,376138397173808,364370650005313,
  352161343671453,339468240159422,326240495588054,312416076259182,297918085021295,282649378327895,
  266484389485088,249256152918898,230734563795934,210587334378498,188303099428665,163019025166970,
  133049349533820,94034599293452]
private def wc_rkmTraj_m8_r128_s6_hb : List ℕ := pCat wc_rkmTraj_m8_r128_s6_hb_p0
  wc_rkmTraj_m8_r128_s6_hb_p1
private def wc_rkmTraj_m8_r128_s6_v0_p0 : List ℕ := [2000069023924536,2000066183159256,
  2000058798027768,1999916014635904,1999952140244758,2000090268439178,2000060719681983,
  2000024338583436,2000022117812972,2000007706587634,1999862667333862,2000023504959910,
  2000052329688854,2000127144567419,1999892126416786,2000059144897619,2000189394815325,
  1999881021263127,2000007248708712,2000185447927268,2000058837532192,1999964175129864,
  1999962300278712,1999929469984406,1999844437121738,1999746832341770,2000329098802885,
  1999770316404487,1999816198667651,1999482358348239,1999023799986502,1998801324210261,
  1998225171078520,1997254694088613,1996092022169359,1994901473300059,1993594078226026,
  1992726699013060,1992564358314804,2006367074123120,1995482056913075,2001572211643592,
  2001786158250207,1995565287081047,2005681425109857,1995754953657390,1998784504075854,
  2002310931731852,1995115111613611,2004428372319667,2001496401187051,2002773776277684,
  2004756491916777,1996563007643203,1999334512113862,2003782836144719,1995723991041681,
  1999015788035777,2003545189975576,1995209522740570,1998573382628455,1995598679567246,
  1995001669903682,1999938263059041]
private def wc_rkmTraj_m8_r128_s6_v0_p1 : List ℕ := [1994262365752366,1995937562129367,
  1996913393265115,1993996337017275,1999130542306724,1994186265832905,1995805874271322,
  1995597950065550,1994237291567919,1997702260330954,1994105055022730,1999819458976250,
  1993878518607666,1998730878804421,1994465653341188,1998095737787542,1995015262547373,
  1998133010463315,2004295779525184,2001708978739055,2004042695293650,2000790639729025,
  2003160366065990,1999570136995672,1997095252950221,1999217558896164,1998591851054469,
  1999124423134712,2000208323653229,2000547856732408,2000647961407373,1996845910224170,
  1998079551243886,1995254408901564,1990804066039274,2002277741186860,2012852287250339,
  2019422771134108,2003619403912979,2026983464922173,2043886932995503,2020302683913737,
  2042518817588895,2108537383024857,2126999216299122,2064913577706192,2071368861473122,
  2239235890024174,2383154048888757,2461701137448943,2462750093115518,2401688872428609,
  2308200507371493,2211374513849759,2130381390204386,2072533807628965,2036402294322953,
  2016446412062017,2006658657110678,2002397620312858,2000758794297616,2000207200525527,
  2000047345911998,2000008547479850]
private def wc_rkmTraj_m8_r128_s6_v0_p2 : List ℕ := [2000001057104757]
private def wc_rkmTraj_m8_r128_s6_v0 : List ℕ := pCat wc_rkmTraj_m8_r128_s6_v0_p0 (pCat
  wc_rkmTraj_m8_r128_s6_v0_p1 wc_rkmTraj_m8_r128_s6_v0_p2)
private def wc_rkmTraj_m8_r128_s6_v1_p0 : List ℕ := [1999986123510406,2000078708491682,
  1999964447839200,2000060159384258,1999996454046739,1999909855725110,2000069401738522,
  2000060159911838,2000087644695560,2000051507101779,2000210804930626,1999731620104879,
  2000091703801348,2000057224253231,1999912507754523,2000148240284544,1999508275159195,
  2000612598969249,1999212045566774,2001815566777252,1997306584028136,2003079221335495,
  1997538638922245,2000737130042960,2001956539308752,1995357410584586,2005086466682065,
  1997844982371801,1997058700286735,2006645591942588,1994379946426926,2000894355643101,
  2003436589392366,1996210019397385,2001457885143665,2000190803517566,1999140794479831,
  2002418482264790,1998281965550631,1997988181457518,2004662783520557,1997422051310838,
  1998899323071133,2001934177727235,1996605587265081,2004190159136038,2001720726189526,
  1993528853294837,2002427380237202,1999460597158986,2000206101391960,2002035845825667,
  1998416487890384,2000411326862538,1990586504473641,1996211937719269,1993350069293745,
  1997264352996028,1992820144498673,1997394042052658,1998635216951887,1999714275777403,
  2001381931754741,1998492502234262]
private def wc_rkmTraj_m8_r128_s6_v1_p1 : List ℕ := [2001556255638879,1996540712876288,
  1998814871925207,1997493059650332,2001025431614464,2003671772566163,2000855645876851,
  2001354827988393,2000677550265992,2001041517616517,2001093720208997,2000765757232869,
  2001230406835005,1997929165596493,1999913615552074,1999945763877729,1996020710116105,
  1997369951199098,1995528119265644,1999349014065848,1992026331356220,1999335362876058,
  1995480956780202,1996214001172524,1994409271846800,1993263798233481,1998258165780563,
  1991488217628852,2002273940940522,1994983092902933,1989203169475180,2004093748725263,
  1988072139706392,1993532223405777,2004901653279959,2008267831129524,1982278523110638,
  2016593533497894,2015494974529125,1967655730019762,2009875541584111,2022807712024740,
  1968987606769384,2000425067032890,2040176465509761,1977930184305303,1950346135477204,
  2022707934938763,2046464100466077,1975248844136456,1950433924075240,2033002134178488,
  2103589607410075,2061837197891017,1976726757646937,1994053115959474,2162336324645500,
  2387350603741411,2530683481347251,2524567524359345,2401487966505555,2243146186439445,
  2115633940673977,2041370858345271]
private def wc_rkmTraj_m8_r128_s6_v1_p2 : List ℕ := [2009751061044593]
private def wc_rkmTraj_m8_r128_s6_v1 : List ℕ := pCat wc_rkmTraj_m8_r128_s6_v1_p0 (pCat
  wc_rkmTraj_m8_r128_s6_v1_p1 wc_rkmTraj_m8_r128_s6_v1_p2)
private def wc_rkmTraj_m8_r128_s6_v2_p0 : List ℕ := [2000041595704938,1999839086805151,
  1999936027106362,2000298764571644,1999090717730343,2001681569743485,1997912398312695,
  2002039239689188,1998718118368368,1999457409810420,2002723120819621,1996877912236727,
  2000806059449976,2003164887823703,1994611404425779,2003320185208008,2001996232766596,
  1994177542260643,2004109163486709,2001119270714462,1995501756450569,2002598198860094,
  2002844595950680,1995305392452318,2001135750122501,2003135796491060,1996616039307850,
  2000898753007137,2001886430121143,1996492391034405,2003419051761368,1999308224044335,
  1995627253008207,2007071749830872,1995270613101670,2000976502714736,1999836201718175,
  2001370760235198,1998830049978724,2000512738976864,2000082330343551,1998393036464939,
  2002696640017254,1998904592022794,2000157122969709,1997332572184509,2002846527565327,
  2001240194071042,1997646893801162,1999517832516058,2000470393250190,2002098025160064,
  1998721710936629,1999099082969988,2000838839758360,1999009351023455,2000815982038420,
  2000908726526860,2000845581199119,1999259868338810,1997064109326276,2001218693506507,
  2000061337986580,2004463982929872]
private def wc_rkmTraj_m8_r128_s6_v2_p1 : List ℕ := [1996529413136955,2000645640016683,
  1997593711088367,2000354576686210,1999359167222945,2001581266052886,2003690913646149,
  1997316947970185,2002976557999467,1995909083457316,1997828460127485,1995485945124495,
  1991492981668291,1996076167078099,1989536943976416,2006525221164116,1993219324370195,
  2001219350502884,1998702676322354,1997348561931095,1996550505611732,2002794912438828,
  1996139706518840,1999255550940599,2009711399481285,1987226624213711,2010816006255418,
  2006171738872660,1981878666823809,2021576713003436,1996898073738091,1983250540602661,
  2025255283940052,1984281921505435,1983440452009119,2026487544695312,1980626373060835,
  1984858149603771,2023581810503266,1975426863135846,1982764869438653,2028402828980239,
  1979972986460358,1974879546294569,2029301450105770,1985468839820974,1955654837827033,
  2031340673272446,2026823949621823,1950849457893239,1995001992755279,2056659053590279,
  1982122864379155,1945204684889488,2044764334777736,2052565645440829,1921159889672928,
  1932625211746131,2104738130399907,2090097127917379,1865645985742939,1889086330957963,
  2329381484689948,2701939304472665]
private def wc_rkmTraj_m8_r128_s6_v2_p2 : List ℕ := [2558583786491903]
private def wc_rkmTraj_m8_r128_s6_v2 : List ℕ := pCat wc_rkmTraj_m8_r128_s6_v2_p0 (pCat
  wc_rkmTraj_m8_r128_s6_v2_p1 wc_rkmTraj_m8_r128_s6_v2_p2)
private def wc_rkmTraj_m8_r128_s5_hb_p0 : List ℕ := [138684165723160,194953969059772,
  237328913520812,272380145657208,302669123336785,329517424601641,353714722531652,375778485525148,
  396070177321358,414854440712061,432332154173723,448660222806496,463964088557346,478345991790665,
  491890627280387,504669135183264,516741990520094,528161142067371,538971626507209,549212807425227,
  558919340758227,568121937249779,576847971891964,585121976387302,592966041029716,600400145626706,
  607442434241474,614109445020877,620416303792846,626376888195176,632003967651005,637309323405897,
  642303851996047,646997654861846,651400116308607,655519971612503,659365366749104,662943910965564,
  666262723211159,669328473273740,672147418333522,674725435534054,677068051078352,679180466282089,
  681067580952473,682734014408549,684184124414264,685422024258220,686451598182322,687276515334604,
  687900242398528,688326055031318,688557048226964,688596145704860,688446108412371,688109542218503,
  687588904866220,686886512242401,686004544016908,684945048695555,683709948125768,682301041488345,
  680720008803808,678968413977375]
private def wc_rkmTraj_m8_r128_s5_hb_p1 : List ℕ := [677047707402399,674959228138276,
  672704205675087,670283761293770,667698909027130,664950556223633,662039503712507,658966445565213,
  655731968444765,652336550530604,648780560002761,645064253064696,641187771479542,637151139589296,
  632954260780752,628596913355522,624078745754224,619399271076593,614557860829815,609553737826419,
  604385968140407,599053452015571,593554913602698,587888889382084,582053715103885,576047511050427,
  569868165390777,563513315357404,556980325925970,550266265620428,543367878993900,536281555248281,
  529003292347873,521528655849256,513852731504002,505970070483371,497874625812445,489559678268554,
  481017749572728,472240500152378,463218608035514,453941624491594,444397800776255,434573878644306,
  424454834988481,414023567775654,403260505987364,392143119912986,380645298926546,368736550252388,
  356380951637470,343535758971830,330149519161365,316159455218245,301487748606942,286036091804019,
  269677413571626,252242747749183,233499232380164,213110598245059,190559352912057,164972324101019,
  134643550899913,95161324731636]
private def wc_rkmTraj_m8_r128_s5_hb : List ℕ := pCat wc_rkmTraj_m8_r128_s5_hb_p0
  wc_rkmTraj_m8_r128_s5_hb_p1
private def wc_rkmTraj_m8_r128_s5_v0_p0 : List ℕ := [1999995077291928,1999982953391442,
  2000039982199291,1999930600838213,1999900589290966,2000108673378019,1999894441457462,
  1999924754477945,2000060727827399,2000044960719782,1999965739723330,2000000570356004,
  2000081029501211,1999834874316215,1999792519952455,1999836463677235,1999968353831169,
  1999903120981509,2000138967733064,2000077103140136,2000052963743408,2000162424844541,
  2000193466808267,2000181024311822,2000174510478584,2000181312052815,1999821030004355,
  1999875601052185,1999988748972418,1999916993008322,1999921551126350,2000016756197931,
  2000125191022536,1999846454683010,1999950206493538,1999864651505593,1999719320190449,
  1999691439800202,1999772376462026,2000088976151176,2000050083083597,2000154091390467,
  2000233515210845,1999690118224119,1999638569377130,1999655719738513,1999747932064367,
  1999875938289742,1999980547968931,1999997869323664,1999916258027364,1999769891185534,
  1999654838634111,2000361890726667,2000268750829218,2000095647980504,2000094635665082,
  2000215931308077,2000202334766295,1999940493435256,1999873324136877,2000231036809684,
  2000168123701954,1999994289283402]
private def wc_rkmTraj_m8_r128_s5_v0_p1 : List ℕ := [1999951800411541,2000325068002158,
  1998892317772812,1998265959131353,1998762917868288,1998962425009085,1995502190916067,
  1993134071850593,1995098265353990,1996358437280038,1982348783321158,1968691784171720,
  1965031408818727,2018396987431720,2024876185350023,2094081984835131,2180336423182007,
  2268865753651165,2343409819344110,2390981581852970,2405182980813760,2387085671710691,
  2343779403967446,2285527849715716,2222746881790953,2163760231411603,2113749536358344,
  2074799672652066,2046637020602096,2027603228448625,2015522992718694,2008299614226908,
  2004220807623152,2002042197574684,2000940168534934,2000411814341442,2000171599163847,
  2000068003423156,2000025620657181,2000009172683141,2000003118990568,2000001006631205,
  2000000308143814,2000000089394286,2000000024555021,1999999993620377,2000000001565904,
  2000000000362635,2000000000079109,1999999999983777,1999999999996881,2000000000000558,
  2000000000000090,2000000000000011,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m8_r128_s5_v0_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m8_r128_s5_v0 : List ℕ := pCat wc_rkmTraj_m8_r128_s5_v0_p0 (pCat
  wc_rkmTraj_m8_r128_s5_v0_p1 wc_rkmTraj_m8_r128_s5_v0_p2)
private def wc_rkmTraj_m8_r128_s5_v1_p0 : List ℕ := [1999945456488997,2000008948794487,
  2000125687112247,1999980698011355,2000003353960503,1999870430087916,1999972862852344,
  2000052446247483,2000053987993572,2000112039483020,1999903176463331,1999907422383104,
  1999996662164264,2000056602033717,2000075834019167,1999832053657062,1999996619834704,
  2000017592251902,1999970456142170,1999965224850776,1999942631517805,2000047958536999,
  1999915739431190,1999874339587467,2000194746629613,2000028054398013,2000041469752193,
  2000022053734559,1999986129423282,2000047348947459,1999731428084852,1999805073564134,
  1999921795097144,2000058819090082,1999762054864728,2000022315719456,2000029387481947,
  1999868549822830,2000048226057494,2000137506403402,2000127744356845,2000337530788314,
  2000042958388417,2000275606652933,2000038003716638,2000140263423259,1999708059915853,
  2000239215931080,1999731798501705,2000151849687733,1999393895278264,2001068806593338,
  1998625642020461,2002536346457371,1995971397960036,2005308346728022,1992660765114687,
  2007879365863222,1990968956916284,2007623122967459,1996513009585041,1999027990169944,
  2004820609988635,1993476586059766]
private def wc_rkmTraj_m8_r128_s5_v1_p1 : List ℕ := [2004185092932117,2000212613577745,
  1994354276378519,2006423349024014,1999027459186731,1992909375474985,2006383702722997,
  2002824548315807,1991059581812059,2000959156723576,2008764436481892,1997051526751122,
  1992446650867891,2003632940286608,2007049638449113,1997483117647790,1993544168200125,
  2000567744863139,2005676728360706,2002538770151405,1997832133556705,1996890307390200,
  1997482039996988,1997500358019186,1999622365043319,2005536375998915,2009609171994628,
  2001871568951415,1978108782509342,1947306580224855,1929687421479315,1946504417111819,
  2008320423054553,2108677589902650,2226160447785543,2333025969555190,2405600162188347,
  2431657257941750,2412327983498157,2359014488631664,2287739594787213,2213683349798739,
  2147714677936724,2095361641533676,2057625874270280,2032646307077895,2017355937935403,
  2008663029679991,2004059930730171,2001785814405080,2000736701348931,2000284690534712,
  2000102888738712,2000034699005757,2000010888060351,2000003166669694,2000000849398969,
  2000000208782100,2000000046640429,2000000009367841,2000000001667281,2000000000257539,
  2000000000033415,2000000000003430]
private def wc_rkmTraj_m8_r128_s5_v1_p2 : List ℕ := [2000000000000238]
private def wc_rkmTraj_m8_r128_s5_v1 : List ℕ := pCat wc_rkmTraj_m8_r128_s5_v1_p0 (pCat
  wc_rkmTraj_m8_r128_s5_v1_p1 wc_rkmTraj_m8_r128_s5_v1_p2)
private def wc_rkmTraj_m8_r128_s5_v2_p0 : List ℕ := [2000069023924536,2000066183159256,
  1999941201972232,1999916014635904,2000047859755242,1999909731560822,1999939280318017,
  2000024338583436,1999977882187028,2000007706587634,2000137332666138,1999976495040090,
  2000052329688854,2000127144567419,1999892126416786,2000059144897619,1999810605184675,
  1999881021263127,1999992751291288,2000185447927268,2000058837532192,1999964175129864,
  1999962300278712,2000070530015594,1999844437121738,2000253167658230,1999670901197115,
  2000229683595513,1999816198667651,2000517641651761,1999023799986502,2001198675789739,
  1998225171078520,2002745305911387,1996092022169359,2005098526699941,1993594078226026,
  2007273300986940,1992564358314804,2006367074123120,1995482056913075,2001572211643592,
  2001786158250207,1995565287081047,2005681425109857,1995754953657390,2001215495924146,
  2002310931731852,1995115111613611,2004428372319667,1998503598812949,1997226223722316,
  2004756491916777,1996563007643203,1999334512113862,2003782836144719,1995723991041681,
  2000984211964223,2003545189975576,1995209522740570,2001426617371545,2004401320432754,
  1995001669903682,2000061736940959]
private def wc_rkmTraj_m8_r128_s5_v2_p1 : List ℕ := [2005737634247634,1995937562129367,
  1996913393265115,2006003662982725,1999130542306724,1994186265832905,2004194125728678,
  2004402049934450,1994237291567919,1997702260330954,2005894944977270,1999819458976250,
  1993878518607666,2001269121195579,2005534346658812,1998095737787542,1995015262547373,
  2001866989536685,2004295779525184,1998291021260945,1995957304706350,2000790639729025,
  2003160366065990,1999570136995672,1997095252950221,1999217558896164,2001408148945531,
  2000875576865288,2000208323653229,2000547856732408,1999352038592627,1996845910224170,
  1998079551243886,2004745591098436,2009195933960726,2002277741186860,1987147712749661,
  1980577228865892,1996380596087021,2026983464922173,2043886932995503,2020302683913737,
  1957481182411105,1891462616975143,1873000783700878,1935086422293808,2071368861473122,
  2239235890024174,2383154048888757,2461701137448943,2462750093115518,2401688872428609,
  2308200507371493,2211374513849759,2130381390204386,2072533807628965,2036402294322953,
  2016446412062017,2006658657110678,2002397620312858,2000758794297616,2000207200525527,
  2000047345911998,2000008547479850]
private def wc_rkmTraj_m8_r128_s5_v2_p2 : List ℕ := [2000001057104757]
private def wc_rkmTraj_m8_r128_s5_v2 : List ℕ := pCat wc_rkmTraj_m8_r128_s5_v2_p0 (pCat
  wc_rkmTraj_m8_r128_s5_v2_p1 wc_rkmTraj_m8_r128_s5_v2_p2)
private def wc_rkmTraj_m512_r64_s0_hb : List ℕ := [183721117117782,257531188810260,
  312590424431297,357674446982757,396211059141404,429971550188860,460015415201572,487037296909407,
  511522388059536,533825661972219,554216167847658,572903572949415,590054952868410,605805886125110,
  620268052633012,633534595902683,645684004270038,656782981701011,666888611158035,676050011265393,
  684309622621283,691704218415505,698265706345502,704021770051392,708996385293479,713210236927398,
  716681056149679,719423892679170,721451332967517,722773672828339,723399050786085,723333546792218,
  722581249608131,721144295013143,719022875985426,716215225059741,712717568130706,708524047986904,
  703626614767561,698014879256704,691675923377639,684594060301437,676750534069923,668123145320639,
  658685785248730,648407853848011,637253529988939,625180848862594,612140524942136,598074432993152,
  582913621042236,566575669533194,548961116084194,529948509794962,509387394752320,487088053753577,
  462805970149104,436217239528943,406877493504274,374148353492219,337053033816911,293953647220330,
  241671612294179,172047064695868]
private def wc_rkmTraj_m512_r64_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTraj_m512_r64_s0_v1_p0 : List ℕ := [2000000000203746,2000000001689222,
  2000000009805582,2000000046010623,2000000185080433,2000000659077807,2000002120268856,
  2000006248536303,2000017041658080,2000043345563240,2000103443965219,2000232757757025,
  2000495757642500,2001002852352764,2001932037048794,2003553302253710,2006251260749306,
  2010538563178911,2017050301003036,2026508953877758,2039651793084426,2057118811287223,
  2079308992176953,2106224419396422,2137332326573665,2171480930998581,2206902405841021,
  2241324045099273,2272187816436789,2296953399163902,2313436965526966,2320124201164544,
  2316396258276535,2302622610430193,2280101819250393,2250863129285094,2217370191891951,
  2182185837995551,2147659771757409,2115689788361198,2087585942122147,2064042504317593,
  2045201052357614,2030774237301735,2020195417001181,2012763337650383,2007760419520051,
  2004534358182951,2002542629504944,2001366244513378,2000702250879420,2000344583230819,
  2000161029922142,2000071469552852,2000030026277767,2000011893785833,2000004420446233,
  2000001532184370,2000000491475392,2000000144419309,2000000038337721,2000000009009490,
  2000000001815050,2000000000295569]
private def wc_rkmTraj_m512_r64_s0_v1_p1 : List ℕ := [2000000000033688]
private def wc_rkmTraj_m512_r64_s0_v1 : List ℕ := pCat wc_rkmTraj_m512_r64_s0_v1_p0
  wc_rkmTraj_m512_r64_s0_v1_p1
private def wc_rkmTraj_m512_r64_s0_v2_p0 : List ℕ := [2000000000000002,2000000000000005,
  1999999999999997,1999999999999997,2000000000000003,2000000000000008,2000000000000004,
  1999999999999993,2000000000000001,2000000000000003,2000000000000001,2000000000000001,
  2000000000000005,1999999999999997,1999999999999994,1999999999999993,2000000000000006,
  2000000000000003,1999999999999994,1999999999999998,2000000000000007,2000000000000011,
  2000000000000000,1999999999999997,2000000000000006,2000000000000005,1999999999999996,
  2000000000000001,2000000000000008,2000000000000010,2000000000000009,2000000000000000,
  2000000000000002,2000000000000014,2000000000000007,2000000000000011,2000000000000010,
  2000000000000012,2000000000000006,2000000000000012,2000000000000006,2000000000000022,
  2000000000000006,1999999999999981,1999999999999917,2000000000000917,2000000000003826,
  1999999999986464,1999999999881559,2000000000047223,2000000002784245,2000000005836171,
  1999999954502279,1999999749216436,2000000227498624,2000005935994521,2000015129952020,
  1999933623284748,1999436515696610,1998922750013346,2006138418964449,2054581551179736,
  2218336272445045,2544068972313970]
private def wc_rkmTraj_m512_r64_s0_v2_p1 : List ℕ := [2808269705563216]
private def wc_rkmTraj_m512_r64_s0_v2 : List ℕ := pCat wc_rkmTraj_m512_r64_s0_v2_p0
  wc_rkmTraj_m512_r64_s0_v2_p1
private def wc_rkmTrajPack_m32_r96_s5_hb_p0 : List ℕ := [173981030983445,243995409056679,
  296318925281631,339256039952241,376051657511070,408383759327352,437257157659732,463331689211785,
  487069210457728,508808540172935,528807358631555,547267316518957,564349921677933,580187040212901,
  594888092260430,608545134011168,621236540346185,633029733184131,643983242184403,654148287777954,
  663570015631124,672288472252768,680339385325206,687754794625880,694563567160430,700791821510443,
  706463280236726,711599564707142,716220443429005,720344042516917,723987025082187,727164744925731,
  729891378836810,732180040962319,734042882055805,735491175898099,736535394770103,737185275528737,
  737449877571145,737337633756163,736856395175305,736013470519772,734815660669136,733269289026184,
  731380228037124,729153922263792,726595408312022,723709331866047,720499962030791,716971203140871,
  713126604155762,708969365723792,704502344962390,699728057967451,694648680029711,689266043499825,
  683581633205274,677596579280120,671311647221717,664727224935065,657843306463762,650659472033935,
  643174863951342,635388157788024]
private def wc_rkmTrajPack_m32_r96_s5_hb_p1 : List ℕ := [627297528168900,618900608314072,
  610194442301344,601175428774838,591839254525293,582180815986598,572194126205390,561872204210601,
  551206942888469,540188950386720,528807358631555,517049590601732,504901075359874,492344896186948,
  479361352041232,465927405259638,452015977824813,437595042848596,422626434225603,407064260694441,
  390852752062841,373923269229719,356190045829169,337543938189044,317842916606039,296896953533068,
  274442668573894,250097732038702,223270949100155,192960425324844,157200911712764,110891583997447]
private def wc_rkmTrajPack_m32_r96_s5_hb : List ℕ := pCat wc_rkmTrajPack_m32_r96_s5_hb_p0
  wc_rkmTrajPack_m32_r96_s5_hb_p1
private def wc_rkmTrajPack_m32_r96_s5_v0_p0 : List ℕ := [1998184298731074,2000122946803018,
  1999827111881397,2000418112800735,1999580146850661,1998955347362039,2000560123675654,
  2003067721094357,2002259732268700,1999890973927388,1998642291049297,1999002738668950,
  2000642515494629,2000541226974856,1998300546434015,2000171598368817,2001532317931510,
  2000463999078152,2000379828825388,2001564209189707,1999751220858908,1999450513174022,
  1999977342060614,1998801054721452,1998297066928975,2001042245010177,1998772421511066,
  1997229766387519,1997884469488382,2000538612591851,2000503327941928,2001533627667005,
  1997230033491905,1996277097861393,1998153853785431,2002297331266202,2000670565799236,
  2001596891519847,2002753741833602,2001898810383029,2002559368291936,2000562500250020,
  2004478350610214,1999670993505464,1996591564276094,1998412787933323,1996573605102737,
  1999459247052238,1999428916047251,2003284001620470,2000376434352531,2000034167773542,
  2000385576099738,2001503973686304,2001510765978231,2001073163708314,2005297390809210,
  2002562833207723,1999241652861240,2000796013870322,1997687682892374,1996553104852130,
  2002577978232443,2004901434014710]
private def wc_rkmTrajPack_m32_r96_s5_v0_p1 : List ℕ := [2004247878219029,2004092122426205,
  2009571800432981,2003008406488433,2010486835031048,2018865287408284,2009473225021237,
  2024787350831197,2070433657161512,2090159766191472,2047526627141045,2063164505929441,
  2211774350304770,2351647398512613,2442966538083218,2466498526257384,2426258369120596,
  2343668156787050,2246576974322501,2158227752168764,2091121341867812,2047216268958631,
  2022056089315256,2009298485547728,2003537906709022,2001213004073777,2000373373586880,
  2000102477219108,1999975204307301,1999994807741691,1999999087876661,1999999873201781,
  2000000012080299]
private def wc_rkmTrajPack_m32_r96_s5_v0 : List ℕ := pCat wc_rkmTrajPack_m32_r96_s5_v0_p0
  wc_rkmTrajPack_m32_r96_s5_v0_p1
private def wc_rkmTrajPack_m32_r96_s5_v1_p0 : List ℕ := [1999190657511012,2000628730374501,
  1999016412028911,2000752657099724,1999702248193529,1999981863715641,2000350353463676,
  1998785040027139,2000751895142113,1999348796704274,1999518171875176,2001738262358976,
  1997845667105061,2000728919001661,1997581813115233,1999262054854321,2001984470585723,
  1999048867184726,1998766310727928,1998941295842147,2000851187578321,2000256795129550,
  1999035575610194,1998269644519323,1998330534459345,1999651732137175,1999865826852314,
  1999363124920359,2003795049177609,1999619983096865,2000515526662366,1998881730836931,
  1998886438354923,1998493779634379,1997472708415185,2002050818007059,2000275418621625,
  1999911284830820,1998526582658426,2004041806160145,2002694591563248,1996510505216178,
  2004968975111446,1995807453435263,2003536554715732,2000632181421728,2001164275919340,
  1995547812580296,2000968453928516,1999447102419387,1997347930218578,2008739057487433,
  1992782654398287,2001288947959833,2004932311865508,1990236278563033,2012265605899710,
  2000823585646164,1988887362259453,2012313481271543,1992005721344613,1992715704202094,
  2016614059539421,1987336565283229]
private def wc_rkmTrajPack_m32_r96_s5_v1_p1 : List ℕ := [1993344744692474,2018994949187946,
  1985664236541190,1991165494240054,2020107820792767,1984007936418087,1983777838462827,
  2027537006110414,2000612941675932,1978921295631180,2022124368608975,2012304857020593,
  1969608583541954,2005534980602044,2031885914387659,1975449761527107,1968538809424009,
  2037729635099324,2027617923590049,1953357090206753,1982573478990437,2064269030876450,
  2015234884451497,1915607965457172,1982308825749974,2121801442822940,2051915623905339,
  1836489703097040,1863472429915798,2245092792425861,2613117632084648,2612649290105381,
  2317601508368087]
private def wc_rkmTrajPack_m32_r96_s5_v1 : List ℕ := pCat wc_rkmTrajPack_m32_r96_s5_v1_p0
  wc_rkmTrajPack_m32_r96_s5_v1_p1
private def wc_rkmTrajPack_m32_r96_s4_hb_p0 : List ℕ := [171719282152674,240823475150850,
  292466787039877,334845720348106,371162995845615,403074781187934,431572826100752,457308389427836,
  480737323521375,502194042521568,521932876865771,540152855785743,557013387526562,572644623936756,
  587154562693993,600634063260863,613160481647039,624800363288003,635611476959117,645644377227077,
  654943622865747,663548739780420,671494991194485,678814000369118,685534259039646,691681546246779,
  697279276158660,702348789065936,706909596485846,710979588893979,714575212781634,717711622350719,
  720402810092606,722661719670626,724500343878850,725929809939254,726960453993363,727601886319213,
  727863048542022,727752263893686,727277281401733,726445314744571,725263076390516,723736807538285,
  721872304292441,719674940435657,717149687098025,714301129570006,711133481458270,707650596341187,
  703855977041854,699752782600251,695343832991359,690631611601892,685618265443863,680305603047416,
  674695089937315,668787841555908,662584613449103,656085788479148,649291360767070,642200915996048,
  634813607621842,627128128434022]
private def wc_rkmTrajPack_m32_r96_s4_hb_p1 : List ℕ := [619142676787335,610854916669959,
  602261930586608,593360163998938,584145359769293,574612480677789,564755617601298,554567880321194,
  544041267115980,533166508227213,521932876865771,510327959511356,498337374648393,485944425474754,
  473129667061740,459870361235279,446139781991531,431906318791040,417132301686789,401772436002577,
  385771676557168,369062276555990,351559584593639,333155875862839,313710967042693,293037300939236,
  270874921094459,246846468094469,220368432629147,190451944866391,155157303991551,109449996319578]
private def wc_rkmTrajPack_m32_r96_s4_hb : List ℕ := pCat wc_rkmTrajPack_m32_r96_s4_hb_p0
  wc_rkmTrajPack_m32_r96_s4_hb_p1
private def wc_rkmTrajPack_m32_r96_s4_v0_p0 : List ℕ := [2000097622319595,2000095272933847,
  2000326115709523,2001497325058546,2002264497295489,2003577746971630,2002778492895460,
  2001549758961633,2001260792753595,2002542246294100,2001738506805227,2001143210723217,
  1997081803347821,1999647296604471,1997575334295517,1998412931314168,2001643291691344,
  2002459950789134,2001431279636158,2002456606945712,2001294674000745,2002319055235671,
  1998998179806264,1997894381559707,1998375544324668,1997908854427647,2001585231549622,
  1998352240107152,1996944471386527,2000098616365393,1996728117088995,2001859290647028,
  2001918019990018,2003838823236959,2002003715733648,2002094312830479,2003819645463771,
  2001635390321908,1998122545736049,1995627778940426,1995697268111238,1998585180140470,
  1997799356815445,1995154359528082,1992875510807556,1990230242175896,1988085106929722,
  1989203102776010,2000666152471877,2026683638253187,2077384001675120,2150433673234758,
  2236369772070502,2319707821682819,2383379307578640,2414060095363100,2406739363484553,
  2366095473771405,2303800866870282,2233603213584208,2167015695140086,2111204355692207,
  2068948579614044,2039752899655086]
private def wc_rkmTrajPack_m32_r96_s4_v0_p1 : List ℕ := [2021268923555990,2010535405565191,
  1995179220133057,2002033595281410,2000789406018029,2000281503595378,2000092061533808,
  2000027561685937,2000007539091477,2000001880200172,2000000426635053,2000000087945065,
  1999999983525667,1999999997181399,2000000000447216,2000000000068009,1999999999989571,
  1999999999998319,2000000000000281,2000000000000045,1999999999999995,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000]
private def wc_rkmTrajPack_m32_r96_s4_v0 : List ℕ := pCat wc_rkmTrajPack_m32_r96_s4_v0_p0
  wc_rkmTrajPack_m32_r96_s4_v0_p1
private def wc_rkmTrajPack_m32_r96_s4_v1_p0 : List ℕ := [1998184298731074,2000122946803018,
  2000172888118603,2000418112800735,1999580146850661,1998955347362039,1999439876324346,
  2003067721094357,1997740267731300,1999890973927388,2001357708950703,1999002738668950,
  2000642515494629,2000541226974856,1998300546434015,2000171598368817,2001532317931510,
  2000463999078152,1999620171174612,1998435790810293,1999751220858908,1999450513174022,
  2000022657939386,2001198945278548,2001702933071025,2001042245010177,2001227578488934,
  2002770233612481,2002115530511618,2000538612591851,2000503327941928,2001533627667005,
  2002769966508095,2003722902138607,2001846146214569,2002297331266202,2000670565799236,
  2001596891519847,1997246258166398,2001898810383029,1997440631708064,1999437499749980,
  1995521649389786,1999670993505464,2003408435723906,2001587212066677,2003426394897263,
  1999459247052238,2000571083952749,2003284001620470,1999623565647469,2000034167773542,
  1999614423900262,1998496026313696,2001510765978231,1998926836291686,1994702609190790,
  1997437166792277,1999241652861240,1999203986129678,2002312317107626,2003446895147870,
  2002577978232443,2004901434014710]
private def wc_rkmTrajPack_m32_r96_s4_v1_p1 : List ℕ := [2004247878219029,1995907877573795,
  1990428199567019,1996991593511567,2010486835031048,2018865287408284,2009473225021237,
  1975212649168803,1929566342838488,1909840233808528,1952473372858955,2063164505929441,
  2211774350304770,2351647398512613,2442966538083218,2466498526257384,2426258369120596,
  2343668156787050,2246576974322501,2158227752168764,2091121341867812,2047216268958631,
  2022056089315256,2009298485547728,2003537906709022,2001213004073777,2000373373586880,
  2000102477219108,2000024795692699,2000005192258309,2000000912123339,2000000126798219,
  2000000012080299]
private def wc_rkmTrajPack_m32_r96_s4_v1 : List ℕ := pCat wc_rkmTrajPack_m32_r96_s4_v1_p0
  wc_rkmTrajPack_m32_r96_s4_v1_p1
private def wc_rkmTrajPack_m32_r96_s3_hb_p0 : List ℕ := [187772058352896,262783647895321,
  318455104781732,363808363058736,402376458137460,435990224098124,465748283970441,492373571845971,
  516373160470464,538119817958209,557897644537059,575929444818027,592394061429434,607437842299650,
  621182505213291,633730696941024,645170025107194,655576047907276,665014534259478,673543201664879,
  681213072716516,688069548244459,694153266581395,699500799102486,704145218823360,708116569427832,
  711442255363445,714147368754677,716254965287032,717786298536130,718761020197339,719197352134564,
  719112234985070,718521457140257,717439767204784,715880972470416,713858025491229,711383100486844,
  708467661010427,705122520083170,701357893805382,697183449297172,692608347692304,687641282801491,
  682290515972215,676563907597496,670468945663439,664012771672549,657202204235136,650043760583164,
  642543676228535,634707922960108,626542225350010,618052075919319,609242749095568,600119314079172,
  590686646722651,580949440514906,570912216752745,560579333972970,549954996710636,539043263642227,
  527848055166500,516373160470464]
private def wc_rkmTrajPack_m32_r96_s3_hb_p1 : List ℕ := [504622244123201,492598852236152,
  480306418224710,467748268202715,454927626038494,441847618098446,428511277701842,414921549308402,
  401081292458281,386993285482453,372660228999900,358084749216642,343269401040412,328216671023622,
  312928980146262,297408686449427,281658087529344,265679422900982,249474876239643,233046577508282,
  216396604977739,199526987146519,182439704566268,165136691578670,147619837969054,129890990541636,
  111951954620986,93804495483972,75450339726171,56891176566433,38128659093065,19164405454862]
private def wc_rkmTrajPack_m32_r96_s3_hb : List ℕ := pCat wc_rkmTrajPack_m32_r96_s3_hb_p0
  wc_rkmTrajPack_m32_r96_s3_hb_p1
private def wc_rkmTrajPack_m32_r96_s3_v0_p0 : List ℕ := [1999736837793362,2000404012490126,
  1999670060971493,1999937738398429,2000226498607968,2000347622767945,2000233086793537,
  1999968998820099,2000278969632368,2000374958662507,2000280228979699,1999949438474339,
  2000213615318978,2000422987606413,2000531389774787,2000538304921953,1999528717088793,
  1999637521011172,2000222919669041,2000010113736289,1999568588711167,1998524543991371,
  1996123883235231,1991043268627667,2018733048059557,2035817202943838,2062937937129350,
  2102017068881895,2152970781632409,2212671938811833,2274652531650999,2329979796204009,
  2369282922285487,2385332226554838,2375201743499279,2341131325907534,2289743063094566,
  2229978470333329,2170623157447817,2118334004206234,2076718340817900,2046489936534572,
  2026326673162752,2013927448668538,2006880164145505,2003172042029116,2001363942907145,
  1999453474098889,1999796131831866,1999929287939842,1999977226861772,2000006798225924,
  2000001877244451,2000000478325482,2000000112123492,2000000024089928,2000000004722207,
  2000000000839658,2000000000134413,2000000000019177,1999999999997598,2000000000000258,
  2000000000000022,2000000000000001]
private def wc_rkmTrajPack_m32_r96_s3_v0_p1 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m32_r96_s3_v0 : List ℕ := pCat wc_rkmTrajPack_m32_r96_s3_v0_p0
  wc_rkmTrajPack_m32_r96_s3_v0_p1
private def wc_rkmTrajPack_m32_r96_s3_v1_p0 : List ℕ := [2000097622319595,1999904727066153,
  2000326115709523,1998502674941454,2002264497295489,1996422253028370,2002778492895460,
  1998450241038367,1998739207246405,2002542246294100,1998261493194773,1998856789276783,
  2002918196652179,1999647296604471,1997575334295517,2001587068685832,2001643291691344,
  1997540049210866,1998568720363842,2002456606945712,2001294674000745,1997680944764329,
  1998998179806264,2002105618440293,2001624455675332,1997908854427647,1998414768450378,
  2001647759892848,2003055528613473,2000098616365393,1996728117088995,1998140709352972,
  2001918019990018,2003838823236959,2002003715733648,1997905687169521,1996180354536229,
  1998364609678092,2001877454263951,2004372221059574,2004302731888762,2001414819859530,
  1997799356815445,1995154359528082,1992875510807556,1990230242175896,1988085106929722,
  1989203102776010,1999333847528123,2026683638253187,2077384001675120,2150433673234758,
  2236369772070502,2319707821682819,2383379307578640,2414060095363100,2406739363484553,
  2366095473771405,2303800866870282,2233603213584208,2167015695140086,2111204355692207,
  2068948579614044,2039752899655086]
private def wc_rkmTrajPack_m32_r96_s3_v1_p1 : List ℕ := [2021268923555990,2010535405565191,
  2004820779866943,2002033595281410,2000789406018029,2000281503595378,2000092061533808,
  2000027561685937,2000007539091477,2000001880200172,2000000426635053,2000000087945065,
  2000000016474333,2000000002818601,2000000000447216,2000000000068009,2000000000010429,
  2000000000001681,2000000000000281,2000000000000045,2000000000000005,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000]
private def wc_rkmTrajPack_m32_r96_s3_v1 : List ℕ := pCat wc_rkmTrajPack_m32_r96_s3_v1_p0
  wc_rkmTrajPack_m32_r96_s3_v1_p1
private def wc_rkmTrajPack_m32_r60_s1_hb : List ℕ := [218802632980621,305241872034845,
  368705701202364,419807506523523,462715695771521,499596018004024,531751173178616,560040240870483,
  585066948497909,607275858267778,627006253710262,644524496091703,660044535628617,673741493758143,
  685760985784338,696225714849309,705240256195646,712894604983927,719266857260344,724425269258135,
  728429861786098,731333685622386,733183830058685,734022233797510,733886341500910,732809638053367,
  730822084520514,727950473868570,724218720096682,719648091075623,714257392767680,708063110399658,
  701079510406862,693318705431073,684790683231449,675503298955027,665462228712558,654670880702166,
  643130258077469,630838765181949,617791945407762,603982134408733,589398006143408,574023980387816,
  557839447596834,540817748153024,522924814570552,504117341093352,484340274782448,463523306443631,
  441575842271976,418379585697625,393777201897526,367554233906053,339408658521628,308895972703881,
  275320608834167,237491587082036,193051910576753,135836908620087]
private def wc_rkmTrajPack_m32_r60_s1_v0 : List ℕ := [2002925129882770,2010854756974005,
  2028063212949153,2058355431051066,2103499973568344,2161673189478429,2226957940308227,
  2290323968762291,2341844015060096,2373333473178650,2380434760581567,2363453842449952,
  2326806929177371,2277459854529622,2223018502153266,2170096596512453,2123338284999652,
  2085164484558406,2056077064517609,2035253185358314,2021180809451588,2012172975986443,
  2006697023405664,2003529121523363,2001782268555654,2000862939804061,2000400708062583,
  2000178491736077,2000076281216267,2000031279498703,2000012306796925,2000004645596370,
  2000001682228822,1999999415776024,1999999805466296,2000000062082292,2000000018980101,
  2000000005555840,2000000001556117,2000000000416729,2000000000106610,2000000000026026,
  2000000000006054,2000000000001338,2000000000000280,2000000000000054,2000000000000009,
  2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m32_r60_s1_v1 : List ℕ := [2000000009670841,1999999964934563,
  2000000083732123,1999999851012807,2000000202252541,1999999799284914,2000000116565238,
  2000000028004167,1999999845807537,2000000172253488,1999999941714814,1999999895583748,
  2000000176926414,1999999913156326,1999999911835213,2000000176800471,1999999917669754,
  1999999897658128,2000000175503127,1999999946914045,1999999852946325,2000000163013623,
  2000000219261369,2000001346287114,2000007734622580,2000030975080918,2000107180861846,
  2000329906102144,2000911125966425,2002285362743476,2005249703404995,2011102813852786,
  2021709926078632,2039378083727745,2066424875768315,2104410919850057,2153170019295798,
  2209956537881940,2269145003946081,2322844860319784,2362484636735298,2380981573957551,
  2374766779624440,2344888017378296,2296730522445966,2238453062908822,2178755223307113,
  2124807217005667,2080999967576730,2048745271649638,2027119178377810,2013896329749322,
  2006527939681216,2002794600152406,2001081850686013,2000374827882899,2000114582526808,
  2000030270829293,2000006688875405,2000001164996227,2000000138442018]
private def wc_rkmTrajPack_m16_r64_s2_hb : List ℕ := [225897898666624,314476186505830,
  379039555381962,430617869333252,473552866305872,510105321192343,541638130792335,569052147010549,
  592981983999888,613896145527882,632153169118336,648035368878838,661770246037940,673544681270889,
  683514687093035,691812314666536,698550672605674,703827655513048,707728767889316,710329299458808,
  711696026230247,711888558636374,710960422905795,708959937928341,705930933333200,701913342841377,
  696943698605543,691055546183324,684279795321641,676645018397721,668177705849427,658902486012215,
  648842315305860,638018643569115,626451558443578,614159911999884,601161432236069,587472821626698,
  573109844537535,558087405025347,542419616301528,526119862940514,509200856750915,491674687092039,
  473552866305872,454846370840329,435565678560403,415720802676990,395321322666592,374376412506940,
  352894866512545,330885123018970,308355286134483,285313145751649,261766195988985,237721652213255,
  213186466776072,188167343583673,162670751605836,136702937418607,110269936865562,83377585913611,
  56031530771620,28237237333328]
private def wc_rkmTrajPack_m16_r64_s2_v0 : List ℕ := [1999999539450326,2000004653350967,
  1999969110951649,2000155741700132,1999364219122434,2002171435811426,2006349705855325,
  2016124240463885,2035970164976556,2071034925161061,2124985999948736,2196828304386276,
  2278430973222223,2354738873911644,2407827285373215,2423611772615190,2397816230347485,
  2337817552443639,2259308429221025,2179776174598587,2112424415731378,2063298840418045,
  2032008314910920,2014490300174593,2005848934119598,2002094121483512,2000660538781460,
  2000181877871116,2000043155846325,2000008656307375,2000001422859199,1999999819092796,
  2000000015425099]
private def wc_rkmTrajPack_m16_r64_s2_v1_p0 : List ℕ := [1999984485049159,1999944810720347,
  1999868473760795,1999760438618550,1999652943867066,1999600089683853,1999651125728265,
  1999813740972467,2000036797670964,2000226680270622,2000297434425198,2000216796225071,
  2000028610126895,1999831220041905,1999726324719627,1999765492002577,1999922920387031,
  2000115276233057,2000250889257496,2000275642962491,2000194045946531,2000050818298129,
  1999879742158455,1999676287499820,1999477911929007,1999515259126486,2000130172582419,
  2001148024758714,2001095557480370,1997626149664891,1990289978312205,1984529455628184,
  1993123377602590,2031538121109960,2108056285329297,2214910344405170,2327643576815996,
  2414689400381426,2451736756147672,2432083375944898,2367402173673783,2279994310090914,
  2192307789012191,2119488033399883,2067330642466660,2034459410771676,2016028584252614,
  2006775529830752,2002600913288108,2000905373190760,2000285190816409,2000081061818869,
  2000020714675432,2000004737097502,2000000963850166,2000000173236019,2000000027256345,
  2000000003711102,2000000000430796,2000000000041795,2000000000003294,2000000000000200,
  2000000000000008,2000000000000000]
private def wc_rkmTrajPack_m16_r64_s2_v1_p1 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m16_r64_s2_v1 : List ℕ := pCat wc_rkmTrajPack_m16_r64_s2_v1_p0
  wc_rkmTrajPack_m16_r64_s2_v1_p1
private def wc_rkmTrajPack_m64_r48_s0_hb : List ℕ := [248667935833479,345257709628437,
  414996631519792,470121760388292,515461400344890,553534943857892,585864044812040,613456162227596,
  637022023889616,657086934715614,674053246019801,688237929746851,699896435999904,709238514854799,
  716439090475006,721645960482846,724985385817748,726566236071534,726483119187882,724818779958759,
  721645960482846,717028856392873,711024262997890,703682478274312,695048010435270,685160123799644,
  674053246019801,661757251126339,648297625342499,633695515388372,617967651215115,601126125812129,
  583178002598056,564124703965005,543961109635736,522674255312111,500241461364003,476627621141405,
  451781206782925,425628243075762,398062921751937,368932374353654,338010644441223,304951076954862,
  269190936923040,229734133829728,184548008510270,128160520643218]
private def wc_rkmTrajPack_m64_r48_s0_v1 : List ℕ := [1999999999999999,1999999999999977,
  1999999999999678,1999999999997969,2000000000004413,2000000000244261,2000000003074318,
  2000000025974037,2000000171551516,2000000940190015,2000004414539715,2000018119240906,
  2000065921077919,2000214775150348,2000631576927666,2001686701086763,2004111329385165,
  2009183826581780,2018863215968158,2035724056577652,2062524983978401,2101324296473682,
  2152267998392234,2212457891549308,2275499003693423,2332240970825073,2372796179329967,
  2389290927132649,2378323627107703,2342092058114305,2287684699076628,2224845393989321,
  2163166885537564,2109805994106476,2068421890478458,2039401519508000,2020920551996990,
  2010213021788407,2004568499759472,2001864756400856,2000690989888007,2000230961110841,
  2000069067749433,2000018282240595,2000004221437666,2000000832580013,2000000135698094,
  2000000017215567,2000000001470664]
private abbrev dP_0 : Prop := atF [ bNLE (bEvalLo12W 32 256 60 [3,3,3,3,3,3,3,3]
  [21911534,33154245,15449612,8716716,7754215,6071261,4530997,2846035] [15,23,11,6,6,5,4,2]
  rkmMasksPack_m32_r60 [none, some (23, 61, wc_rkmTrajPack_m32_r60_s1_hb,
  wc_rkmTrajPack_m32_r60_s1_v0, wc_rkmTrajPack_m32_r60_s1_v1)]) rkmRowPack_m32_r60] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bNLE (bEvalLo12W 16 512 64 [1,2,4,7,7,7,7,7]
  [39273366,22292038,31766892,20789973,18159356,4891556,1411360,682172] [7,7,18,17,15,4,2,1]
  rkmMasksPack_m16_r64 [none, none, some (18, 65, wc_rkmTrajPack_m16_r64_s2_hb,
  wc_rkmTrajPack_m16_r64_s2_v0, wc_rkmTrajPack_m16_r64_s2_v1)]) rkmRowPack_m16_r64] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bNLE (bEvalLo12W 16 512 52 [1,2,4,6,6,6]
  [40527500,31713739,17250000,43172257,7164195,1458793] [7,9,9,27,5,1] rkmMasks_m16_r52 [])
  rkmRow_m16_r52, bNLE (bEvalLo12W 16 512 4 [1,1,1,1,1]
  [108046819,51177636,12678224,14894374,5943115] [21,10,3,3,2] rkmMasks_m16_r4 []) rkmRow_m16_r4,
  bNLE (bEvalLo12W 2 4096 5 [1,2,4,4,4,4,4,4]
  [103311246,106765511,45449484,66907126,24550734,12349231,3808479,1203984] [1,2,1,2,1,1,1,1]
  rkmMasksPack_m2_r5 []) rkmRowPack_m2_r5] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bSlideChk 27 97 wc_rkmTrajPack_m32_r96_s5_hb
  wc_rkmTrajPack_m32_r96_s5_v0 wc_rkmTrajPack_m32_r96_s5_v1, bNLE (bEvalLo12W 8 1024 12
  [1,2,3,3,3,3,3,3] [76835062,93566740,28920308,27161543,6768657,3104681,1447548,541095]
  [3,6,3,3,1,1,1,1] rkmMasks_m8_r12 []) rkmRow_m8_r12] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bNLE (bEvalLo12W 8 1024 128 [1,2,4,9,18,30,30,30]
  [12671202,13576075,16055840,15398439,22362024,12264447,12510177,2843915] [2,4,9,16,40,31,32,8]
  rkmMasks_m8_r128 [none, none, none, none, some (40, 129, wc_rkmTraj_m8_r128_s4_hb,
  wc_rkmTraj_m8_r128_s4_v0, wc_rkmTraj_m8_r128_s4_v2), some (31, 129, wc_rkmTraj_m8_r128_s5_hb,
  wc_rkmTraj_m8_r128_s5_v0, wc_rkmTraj_m8_r128_s5_v2), some (32, 129, wc_rkmTraj_m8_r128_s6_hb,
  wc_rkmTraj_m8_r128_s6_v0, wc_rkmTraj_m8_r128_s6_v2)]) rkmRow_m8_r128, bNLE (bEvalLo12W 4 2048 15
  [1,2,4,7,7,7,7,7] [70144454,49781825,76859869,27216203,25001847,7863623,6960973,3967098]
  [2,3,6,3,3,1,1,1] rkmMasksPack_m4_r15 []) rkmRowPack_m4_r15] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bSlideChk 20 129 wc_rkmTraj_m8_r128_s4_hb
  wc_rkmTraj_m8_r128_s4_v0 wc_rkmTraj_m8_r128_s4_v1, bNLE (bEvalLo12W 512 16 64 [1,1,1,1]
  [34000000,1303137,342379,91212] [67,3,1,1] rkmMasks_m512_r64 [some (67, 65,
  wc_rkmTraj_m512_r64_s0_hb, wc_rkmTraj_m512_r64_s0_v0, wc_rkmTraj_m512_r64_s0_v2)])
  rkmRow_m512_r64] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bSlideChk 20 129 wc_rkmTraj_m8_r128_s4_hb
  wc_rkmTraj_m8_r128_s4_v1 wc_rkmTraj_m8_r128_s4_v2, bNLE (bEvalLo12W 16 512 60 [1,1,1,1,1,1,1,1]
  [14124342,24382147,23848180,6738177,2856,696590,142739,3578416] [3,5,4,2,1,1,1,1]
  rkmMasksPack_m16_r60 []) rkmRowPack_m16_r60] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bNLE (bEvalLo12W 32 256 96 [1,1,2,3,5,5,5,5]
  [10657892,29700259,17163003,16625651,14548317,18951346,5603301,1897952] [5,12,13,17,21,27,8,3]
  rkmMasksPack_m32_r96 [none, none, none, some (17, 97, wc_rkmTrajPack_m32_r96_s3_hb,
  wc_rkmTrajPack_m32_r96_s3_v0, wc_rkmTrajPack_m32_r96_s3_v1), some (21, 97,
  wc_rkmTrajPack_m32_r96_s4_hb, wc_rkmTrajPack_m32_r96_s4_v0, wc_rkmTrajPack_m32_r96_s4_v1), some
  (27, 97, wc_rkmTrajPack_m32_r96_s5_hb, wc_rkmTrajPack_m32_r96_s5_v0,
  wc_rkmTrajPack_m32_r96_s5_v1)]) rkmRowPack_m32_r96, bNLE (bEvalLo12W 64 128 17 [1,1]
  [100673250,3339346] [21,2] rkmMasks_m64_r17 []) rkmRow_m64_r17] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := atF [ bSlideChk 34 65 wc_rkmTraj_m512_r64_s0_hb
  wc_rkmTraj_m512_r64_s0_v0 wc_rkmTraj_m512_r64_s0_v1, bNLE (bEvalLo12W 8 1024 21 [1,4,4,4]
  [84693065,101308018,25802540,6927704] [5,15,4,1] rkmMasksPack_m8_r21 []) rkmRowPack_m8_r21, bNLE
  (bEvalLo12W 64 128 6 [1,1,1] [62458610,29296349,4080022] [6,4,2] rkmMasks_m64_r6 [])
  rkmRow_m64_r6, bNLE (bEvalLo12W 2 4096 26 [1,2,4,8] [40968329,36199282,44712521,42905410]
  [1,2,3,5] rkmMasksPack_m2_r26 []) rkmRowPack_m2_r26] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := atF [ bSlideChk 33 65 wc_rkmTraj_m512_r64_s0_hb
  wc_rkmTraj_m512_r64_s0_v1 wc_rkmTraj_m512_r64_s0_v2, bNLE (bEvalLo12W 32 256 18 [1,1,1,1]
  [93388119,36594109,25852814,10053374] [13,6,5,3] rkmMasks_m32_r18 []) rkmRow_m32_r18, bNLE
  (bEvalLo12W 32 256 12 [1,1,1] [134763407,10191932,6191455] [13,1,1] rkmMasksPack_m32_r12 [])
  rkmRowPack_m32_r12] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := atF [ bNLE (bEvalLo12W 32 256 41 [2,2,2,2,2,2,2,2]
  [39119166,26101514,19221589,15409961,7739417,5433092,6395474,4464361] [15,10,8,6,3,3,3,2]
  rkmMasksPack_m32_r41 []) rkmRowPack_m32_r41, bNLE (bEvalLo12W 1024 8 22 [1] [24389797] [25]
  rkmMasks_m1024_r22 []) rkmRow_m1024_r22, bNLE (bEvalLo12W 8 1024 11 [1,2,2,2,2]
  [120837873,68055839,48622313,31576661,14583457] [5,4,3,2,1] rkmMasksPack_m8_r11 [])
  rkmRowPack_m8_r11, bNLE (bEvalLo12W 16 512 6 [1,1,1,1,1,1,1,1]
  [40222723,44195489,16819254,35279281,17551714,23968355,18088879,9917575] [2,2,1,2,1,1,1,1]
  rkmMasksPack_m16_r6 []) rkmRowPack_m16_r6] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m8_r128_s6_hb
  wc_rkmTraj_m8_r128_s6_v0 wc_rkmTraj_m8_r128_s6_v1, bNLE (bEvalLo12W 16 512 24 [1,2,2,2,2]
  [82696789,69509280,34929926,18901386,9377134] [8,11,6,3,2] rkmMasksPack_m16_r24 [])
  rkmRowPack_m16_r24, bNLE (bEvalLo12W 4 2048 9 [1,2,4,4,4,4,4,4]
  [90460751,86046048,48713340,41767700,15507881,6513309,2735589,1148945] [2,3,3,3,1,1,1,1]
  rkmMasks_m4_r9 []) rkmRow_m4_r9] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m8_r128_s6_hb
  wc_rkmTraj_m8_r128_s6_v1 wc_rkmTraj_m8_r128_s6_v2, bNLE (bEvalLo12W 4 2048 24 [1,2,4,8,11,11,11]
  [38395095,30764077,38961696,40432370,47613211,5809634,6724558] [2,2,4,7,10,2,2]
  rkmMasksPack_m4_r24 []) rkmRowPack_m4_r24, bNLE (bEvalLo12W 4 2048 4 [1,1,2,2,2,2,2,2]
  [124350637,116539180,56472314,46699984,8117216,8499702,3095644,2724168] [2,2,2,1,1,1,1,1]
  rkmMasks_m4_r4 []) rkmRow_m4_r4, bNLE (bEvalLo12W 4 2048 35 [1,1,1,1,1,1,1,1]
  [23283284,37354801,15350138,1393952,13764419,295771,14710,3526417] [1,2,1,1,1,1,1,1]
  rkmMasksPack_m4_r35 []) rkmRowPack_m4_r35] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m8_r128_s5_hb
  wc_rkmTraj_m8_r128_s5_v0 wc_rkmTraj_m8_r128_s5_v1, bNLE (bEvalLo12W 16 512 21 [1,2,2,2]
  [76152515,89075389,24311289,9494391] [8,14,5,3] rkmMasks_m16_r21 []) rkmRow_m16_r21, bNLE
  (bEvalLo12W 2 4096 4 [1,2,3,3,3,3,3,3]
  [134251113,156681400,53434319,48347546,13537314,7060533,2639227,1140600] [2,2,1,1,1,1,1,1]
  rkmMasks_m2_r4 []) rkmRow_m2_r4, bNLE (bEvalLo12W 4 2048 3 [1,1,1,1,1,1]
  [126263759,113792387,61478563,63017453,31096551,22614910] [2,2,1,1,1,1] rkmMasksPack_m4_r3 [])
  rkmRowPack_m4_r3] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := atF [ bSlideChk 21 97 wc_rkmTrajPack_m32_r96_s4_hb
  wc_rkmTrajPack_m32_r96_s4_v0 wc_rkmTrajPack_m32_r96_s4_v1, bNLE (bEvalLo12W 256 32 23 [1,1]
  [48620565,1017972] [27,2] rkmMasks_m256_r23 []) rkmRow_m256_r23, bNLE (bEvalLo12W 2 4096 7
  [1,2,4,6,6,6,6,6] [65919752,76782587,91724923,38878767,34186878,11887027,5541731,1866215]
  [1,2,3,2,2,1,1,1] rkmMasks_m2_r7 []) rkmRow_m2_r7] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := atF [ bSlideChk 15 129 wc_rkmTraj_m8_r128_s5_hb
  wc_rkmTraj_m8_r128_s5_v1 wc_rkmTraj_m8_r128_s5_v2, bNLE (bEvalLo12W 64 128 24 [1,1,1]
  [92979344,11698342,4093797] [26,4,2] rkmMasks_m64_r24 []) rkmRow_m64_r24, bNLE (bEvalLo12W 2
  4096 9 [1,2,4,8,8,8,8,8] [65213720,69876296,90531331,34580000,40326300,11426860,4799280,2015697]
  [1,2,3,2,3,1,1,1] rkmMasks_m2_r9 []) rkmRow_m2_r9] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := atF [ bNLE (bEvalLo12W 64 128 48 [1,1,1,1,1,1,1,1]
  [58324703,16331341,11719221,10369244,9379848,8876018,12931525,7408817] [26,8,6,5,5,4,6,4]
  rkmMasksPack_m64_r48 [some (26, 49, wc_rkmTrajPack_m64_r48_s0_hb, wc_rkmTraj_m512_r64_s0_v0,
  wc_rkmTrajPack_m64_r48_s0_v1)]) rkmRowPack_m64_r48, bNLE (bEvalLo12W 8 1024 28 [1,2,4,6,6,6]
  [47662408,34781619,36518254,57837958,7144035,7263218] [3,4,7,14,2,2] rkmMasksPack_m8_r28 [])
  rkmRowPack_m8_r28, bNLE (bEvalLo12W 2 4096 11 [1,2,4,8,9,9,9,9]
  [56541608,51724585,31682955,16757109,50582801,55904750,10974586,3567869] [1,2,2,1,4,4,1,1]
  rkmMasks_m2_r11 []) rkmRow_m2_r11] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := atF [ bNLE (bEvalLo12W 64 128 36 [1,1,1,1]
  [94312916,13369111,6818970,4429954] [35,6,4,3] rkmMasks_m64_r36 []) rkmRow_m64_r36, bNLE
  (bEvalLo12W 32 256 23 [1,1,1,1] [131878891,24868794,16387633,10411553] [23,5,4,3]
  rkmMasks_m32_r23 []) rkmRow_m32_r23, bNLE (bEvalLo12W 32 256 13 [1,1,1,1,1,1,1,1]
  [51332385,16720317,35403144,14313356,11124967,8137088,9709246,6572887] [5,2,4,2,2,1,1,1]
  rkmMasksPack_m32_r13 []) rkmRowPack_m32_r13] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := atF [ bSlideChk 17 97 wc_rkmTrajPack_m32_r96_s3_hb
  wc_rkmTrajPack_m32_r96_s3_v0 wc_rkmTrajPack_m32_r96_s3_v1, bNLE (bEvalLo12W 1024 8 27 [1]
  [24472289] [35] rkmMasks_m1024_r27 []) rkmRow_m1024_r27, bNLE (bEvalLo12W 16 512 11 [1,1,1,1]
  [149816006,49618046,28617575,17259776] [10,4,3,2] rkmMasks_m16_r11 []) rkmRow_m16_r11] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := atF [ bNLE (bEvalLo12W 64 128 80 [1,1,1,1,1,1,1,1]
  [6229559,10619513,6289694,2103231,3772865,2216417,1414092,1191582] [4,7,4,2,3,2,1,1]
  rkmMasksPack_m64_r80 []) rkmRowPack_m64_r80, bNLE (bEvalLo12W 32 256 30 [1,2,2,2]
  [91420373,33545811,15589570,5413015] [17,10,5,2] rkmMasksPack_m32_r30 []) rkmRowPack_m32_r30,
  bNLE (bEvalLo12W 8 1024 13 [1,2,3,3,3,3,3,3]
  [78289353,102506279,24760990,28920308,7605232,3446545,1489135,541095] [4,7,3,3,1,1,1,1]
  rkmMasks_m8_r13 []) rkmRow_m8_r13] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := atF [ bSlideChk 23 61 wc_rkmTrajPack_m32_r60_s1_hb
  wc_rkmTrajPack_m32_r60_s1_v0 wc_rkmTrajPack_m32_r60_s1_v1, bNLE (bEvalLo12W 32 256 28 [1,2,2,2]
  [88270000,42363122,7779822,3927404] [17,13,4,3] rkmMasks_m32_r28 []) rkmRow_m32_r28, bNLE
  (bEvalLo12W 16 512 16 [1,1,1,1,2,2,2,2]
  [20968205,33019097,21105407,45544089,23189103,26630425,22977581,9203707] [2,3,2,4,3,4,3,2]
  rkmMasksPack_m16_r16 []) rkmRowPack_m16_r16] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := atF [ bNLE (bEvalLo12W 16 512 36 [1,2,4,4,4]
  [48703688,31713739,68737500,5456420,1028067] [7,7,25,2,1] rkmMasks_m16_r36 []) rkmRow_m16_r36,
  bNLE (bEvalLo12W 512 16 28 [1,1,1,1] [33394223,1181122,214520,79032] [31,3,2,2]
  rkmMasks_m512_r28 []) rkmRow_m512_r28, bNLE (bEvalLo12W 512 16 15 [1,1,1]
  [33394223,891005,78734] [18,2,2] rkmMasks_m512_r15 []) rkmRow_m512_r15, bNLE (bEvalLo12W 2 4096
  8 [1,2,4,6,6,6,6,6] [84031614,64596330,97178089,46364063,34488416,14677448,3963305,2829001]
  [1,2,3,2,2,1,1,1] rkmMasksPack_m2_r8 []) rkmRowPack_m2_r8] = true
private theorem bk_21 : dP_21 := by decide +kernel
private abbrev dP_22 : Prop := atF [ bSlideChk 26 49 wc_rkmTrajPack_m64_r48_s0_hb
  wc_rkmTraj_m512_r64_s0_v0 wc_rkmTrajPack_m64_r48_s0_v1, bSlideChk 18 65
  wc_rkmTrajPack_m16_r64_s2_hb wc_rkmTrajPack_m16_r64_s2_v0 wc_rkmTrajPack_m16_r64_s2_v1, bNLE
  (bEvalLo12W 256 32 16 [1,1,1,1,1,1,1,1]
  [23544233,23556393,37153,36642,743519,745567,196663,185861] [10,10,1,1,1,1,1,1]
  rkmMasks_m256_r16 []) rkmRow_m256_r16] = true
private theorem bk_22 : dP_22 := by decide +kernel
private abbrev dP_23 : Prop := atF [ bNLE (bEvalLo12W 64 128 30 [1,1,1,1]
  [93493901,15101047,1000,4858492] [30,6,2,3] rkmMasks_m64_r30 []) rkmRow_m64_r30, bNLE
  (bEvalLo12W 64 128 31 [1,1,1,1,1,1,1,1]
  [24512417,30224301,23696216,8528649,9591674,7737122,5882692,4071452] [8,10,8,3,3,3,2,2]
  rkmMasksPack_m64_r31 []) rkmRowPack_m64_r31, bNLE (bEvalLo12W 8 1024 27 [1,3]
  [85369121,69523641] [6,11] rkmMasks_m8_r27 []) rkmRow_m8_r27] = true
private theorem bk_23 : dP_23 := by decide +kernel
private theorem ws_rkmTraj_m8_r128_s4 : WalkOk (some (40, 129, wc_rkmTraj_m8_r128_s4_hb,
    wc_rkmTraj_m8_r128_s4_v0, wc_rkmTraj_m8_r128_s4_v2)) := mIter_split rfl (bSlideChk_sound bk_5)
    (bSlideChk_sound bk_6)
private theorem ws_rkmTraj_m8_r128_s5 : WalkOk (some (31, 129, wc_rkmTraj_m8_r128_s5_hb,
    wc_rkmTraj_m8_r128_s5_v0, wc_rkmTraj_m8_r128_s5_v2)) := mIter_split rfl
    (bSlideChk_sound bk_13) (bSlideChk_sound bk_15)
private theorem ws_rkmTraj_m8_r128_s6 : WalkOk (some (32, 129, wc_rkmTraj_m8_r128_s6_hb,
    wc_rkmTraj_m8_r128_s6_v0, wc_rkmTraj_m8_r128_s6_v2)) := mIter_split rfl
    (bSlideChk_sound bk_11) (bSlideChk_sound bk_12)
private theorem ws_rkmTraj_m512_r64_s0 : WalkOk (some (67, 65, wc_rkmTraj_m512_r64_s0_hb,
    wc_rkmTraj_m512_r64_s0_v0, wc_rkmTraj_m512_r64_s0_v2)) := mIter_split rfl
    (bSlideChk_sound bk_8) (bSlideChk_sound bk_9)
/-- Kernel trajectory certificate `(m = 8, r = 128)`. -/
theorem rkmTraj_m8_r128 : rkmEvalT16Lo12 8 1024 128 [1, 2, 4, 9, 18, 30, 30, 30] [12671202,
  13576075, 16055840, 15398439, 22362024, 12264447, 12510177, 2843915] [2, 4, 9, 16, 40, 31, 32, 8]
  rkmMasks_m8_r128 = rkmRow_m8_r128 :=
    bhW_eq bk_4 (wSkip (wSkip (wSkip (wSkip (wCons ws_rkmTraj_m8_r128_s4 (wCons
      ws_rkmTraj_m8_r128_s5 (wCons ws_rkmTraj_m8_r128_s6 wNil)))))))
/-- Kernel trajectory certificate `(m = 256, r = 16)`. -/
theorem rkmTraj_m256_r16 : rkmEvalT16Lo12 256 32 16 [1, 1, 1, 1, 1, 1, 1, 1] [23544233, 23556393,
  37153, 36642, 743519, 745567, 196663, 185861] [10, 10, 1, 1, 1, 1, 1, 1] rkmMasks_m256_r16 =
  rkmRow_m256_r16 := bh0_eq (tl2 bk_22)
/-- Kernel trajectory certificate `(m = 2, r = 4)`. -/
theorem rkmTraj_m2_r4 : rkmEvalT16Lo12 2 4096 4 [1, 2, 3, 3, 3, 3, 3, 3] [134251113, 156681400,
  53434319, 48347546, 13537314, 7060533, 2639227, 1140600] [2, 2, 1, 1, 1, 1, 1, 1] rkmMasks_m2_r4 =
  rkmRow_m2_r4 := bh0_eq (tl2 bk_13)
/-- Kernel trajectory certificate `(m = 512, r = 64)`. -/
theorem rkmTraj_m512_r64 : rkmEvalT16Lo12 512 16 64 [1, 1, 1, 1] [34000000, 1303137, 342379, 91212]
  [67, 3, 1, 1] rkmMasks_m512_r64 = rkmRow_m512_r64 :=
    bhW_eq (tl1 bk_5) (wCons ws_rkmTraj_m512_r64_s0 wNil)
/-- Kernel trajectory certificate `(m = 4, r = 4)`. -/
theorem rkmTraj_m4_r4 : rkmEvalT16Lo12 4 2048 4 [1, 1, 2, 2, 2, 2, 2, 2] [124350637, 116539180,
  56472314, 46699984, 8117216, 8499702, 3095644, 2724168] [2, 2, 2, 1, 1, 1, 1, 1] rkmMasks_m4_r4 =
  rkmRow_m4_r4 := bh0_eq (tl2 bk_12)
/-- Kernel trajectory certificate `(m = 16, r = 52)`. -/
theorem rkmTraj_m16_r52 : rkmEvalT16Lo12 16 512 52 [1, 2, 4, 6, 6, 6] [40527500, 31713739, 17250000,
  43172257, 7164195, 1458793] [7, 9, 9, 27, 5, 1] rkmMasks_m16_r52 = rkmRow_m16_r52 := bh0_eq bk_2
/-- Kernel trajectory certificate `(m = 64, r = 6)`. -/
theorem rkmTraj_m64_r6 : rkmEvalT16Lo12 64 128 6 [1, 1, 1] [62458610, 29296349, 4080022] [6, 4, 2]
  rkmMasks_m64_r6 = rkmRow_m64_r6 := bh0_eq (tl2 bk_8)
/-- Kernel trajectory certificate `(m = 64, r = 36)`. -/
theorem rkmTraj_m64_r36 : rkmEvalT16Lo12 64 128 36 [1, 1, 1, 1] [94312916, 13369111, 6818970,
  4429954] [35, 6, 4, 3] rkmMasks_m64_r36 = rkmRow_m64_r36 := bh0_eq bk_17
/-- Kernel trajectory certificate `(m = 2, r = 7)`. -/
theorem rkmTraj_m2_r7 : rkmEvalT16Lo12 2 4096 7 [1, 2, 4, 6, 6, 6, 6, 6] [65919752, 76782587,
  91724923, 38878767, 34186878, 11887027, 5541731, 1866215] [1, 2, 3, 2, 2, 1, 1, 1] rkmMasks_m2_r7
  = rkmRow_m2_r7 := bh0_eq (tl2 bk_14)
/-- Kernel trajectory certificate `(m = 16, r = 36)`. -/
theorem rkmTraj_m16_r36 : rkmEvalT16Lo12 16 512 36 [1, 2, 4, 4, 4] [48703688, 31713739, 68737500,
  5456420, 1028067] [7, 7, 25, 2, 1] rkmMasks_m16_r36 = rkmRow_m16_r36 := bh0_eq bk_21
/-- Kernel trajectory certificate `(m = 2, r = 9)`. -/
theorem rkmTraj_m2_r9 : rkmEvalT16Lo12 2 4096 9 [1, 2, 4, 8, 8, 8, 8, 8] [65213720, 69876296,
  90531331, 34580000, 40326300, 11426860, 4799280, 2015697] [1, 2, 3, 2, 3, 1, 1, 1] rkmMasks_m2_r9
  = rkmRow_m2_r9 := bh0_eq (tl2 bk_15)
/-- Kernel trajectory certificate `(m = 64, r = 30)`. -/
theorem rkmTraj_m64_r30 : rkmEvalT16Lo12 64 128 30 [1, 1, 1, 1] [93493901, 15101047, 1000, 4858492]
  [30, 6, 2, 3] rkmMasks_m64_r30 = rkmRow_m64_r30 := bh0_eq bk_23
/-- Kernel trajectory certificate `(m = 4, r = 9)`. -/
theorem rkmTraj_m4_r9 : rkmEvalT16Lo12 4 2048 9 [1, 2, 4, 4, 4, 4, 4, 4] [90460751, 86046048,
  48713340, 41767700, 15507881, 6513309, 2735589, 1148945] [2, 3, 3, 3, 1, 1, 1, 1] rkmMasks_m4_r9 =
  rkmRow_m4_r9 := bh0_eq (tl2 bk_11)
/-- Kernel trajectory certificate `(m = 512, r = 28)`. -/
theorem rkmTraj_m512_r28 : rkmEvalT16Lo12 512 16 28 [1, 1, 1, 1] [33394223, 1181122, 214520, 79032]
  [31, 3, 2, 2] rkmMasks_m512_r28 = rkmRow_m512_r28 := bh0_eq (tl1 bk_21)
/-- Kernel trajectory certificate `(m = 2, r = 11)`. -/
theorem rkmTraj_m2_r11 : rkmEvalT16Lo12 2 4096 11 [1, 2, 4, 8, 9, 9, 9, 9] [56541608, 51724585,
  31682955, 16757109, 50582801, 55904750, 10974586, 3567869] [1, 2, 2, 1, 4, 4, 1, 1]
  rkmMasks_m2_r11 = rkmRow_m2_r11 := bh0_eq (tl2 bk_16)
/-- Kernel trajectory certificate `(m = 32, r = 28)`. -/
theorem rkmTraj_m32_r28 : rkmEvalT16Lo12 32 256 28 [1, 2, 2, 2] [88270000, 42363122, 7779822,
  3927404] [17, 13, 4, 3] rkmMasks_m32_r28 = rkmRow_m32_r28 := bh0_eq (tl1 bk_20)
/-- Kernel trajectory certificate `(m = 16, r = 4)`. -/
theorem rkmTraj_m16_r4 : rkmEvalT16Lo12 16 512 4 [1, 1, 1, 1, 1] [108046819, 51177636, 12678224,
  14894374, 5943115] [21, 10, 3, 3, 2] rkmMasks_m16_r4 = rkmRow_m16_r4 := bh0_eq (tl1 bk_2)
/-- Kernel trajectory certificate `(m = 1024, r = 27)`. -/
theorem rkmTraj_m1024_r27 : rkmEvalT16Lo12 1024 8 27 [1] [24472289] [35] rkmMasks_m1024_r27 =
  rkmRow_m1024_r27 := bh0_eq (tl1 bk_18)
/-- Kernel trajectory certificate `(m = 16, r = 11)`. -/
theorem rkmTraj_m16_r11 : rkmEvalT16Lo12 16 512 11 [1, 1, 1, 1] [149816006, 49618046, 28617575,
  17259776] [10, 4, 3, 2] rkmMasks_m16_r11 = rkmRow_m16_r11 := bh0_eq (tl2 bk_18)
/-- Kernel trajectory certificate `(m = 32, r = 23)`. -/
theorem rkmTraj_m32_r23 : rkmEvalT16Lo12 32 256 23 [1, 1, 1, 1] [131878891, 24868794, 16387633,
  10411553] [23, 5, 4, 3] rkmMasks_m32_r23 = rkmRow_m32_r23 := bh0_eq (tl1 bk_17)
/-- Kernel trajectory certificate `(m = 8, r = 12)`. -/
theorem rkmTraj_m8_r12 : rkmEvalT16Lo12 8 1024 12 [1, 2, 3, 3, 3, 3, 3, 3] [76835062, 93566740,
  28920308, 27161543, 6768657, 3104681, 1447548, 541095] [3, 6, 3, 3, 1, 1, 1, 1] rkmMasks_m8_r12 =
  rkmRow_m8_r12 := bh0_eq (tl1 bk_3)
/-- Kernel trajectory certificate `(m = 64, r = 24)`. -/
theorem rkmTraj_m64_r24 : rkmEvalT16Lo12 64 128 24 [1, 1, 1] [92979344, 11698342, 4093797] [26, 4,
  2] rkmMasks_m64_r24 = rkmRow_m64_r24 := bh0_eq (tl1 bk_15)
/-- Kernel trajectory certificate `(m = 8, r = 13)`. -/
theorem rkmTraj_m8_r13 : rkmEvalT16Lo12 8 1024 13 [1, 2, 3, 3, 3, 3, 3, 3] [78289353, 102506279,
  24760990, 28920308, 7605232, 3446545, 1489135, 541095] [4, 7, 3, 3, 1, 1, 1, 1] rkmMasks_m8_r13 =
  rkmRow_m8_r13 := bh0_eq (tl2 bk_19)
/-- Kernel trajectory certificate `(m = 256, r = 23)`. -/
theorem rkmTraj_m256_r23 : rkmEvalT16Lo12 256 32 23 [1, 1] [48620565, 1017972] [27, 2]
  rkmMasks_m256_r23 = rkmRow_m256_r23 := bh0_eq (tl1 bk_14)
/-- Kernel trajectory certificate `(m = 8, r = 27)`. -/
theorem rkmTraj_m8_r27 : rkmEvalT16Lo12 8 1024 27 [1, 3] [85369121, 69523641] [6, 11]
  rkmMasks_m8_r27 = rkmRow_m8_r27 := bh0_eq (tl2 bk_23)
/-- Kernel trajectory certificate `(m = 16, r = 21)`. -/
theorem rkmTraj_m16_r21 : rkmEvalT16Lo12 16 512 21 [1, 2, 2, 2] [76152515, 89075389, 24311289,
  9494391] [8, 14, 5, 3] rkmMasks_m16_r21 = rkmRow_m16_r21 := bh0_eq (tl1 bk_13)
/-- Kernel trajectory certificate `(m = 512, r = 15)`. -/
theorem rkmTraj_m512_r15 : rkmEvalT16Lo12 512 16 15 [1, 1, 1] [33394223, 891005, 78734] [18, 2, 2]
  rkmMasks_m512_r15 = rkmRow_m512_r15 := bh0_eq (tl2 bk_21)
/-- Kernel trajectory certificate `(m = 1024, r = 22)`. -/
theorem rkmTraj_m1024_r22 : rkmEvalT16Lo12 1024 8 22 [1] [24389797] [25] rkmMasks_m1024_r22 =
  rkmRow_m1024_r22 := bh0_eq (tl1 bk_10)
/-- Kernel trajectory certificate `(m = 64, r = 17)`. -/
theorem rkmTraj_m64_r17 : rkmEvalT16Lo12 64 128 17 [1, 1] [100673250, 3339346] [21, 2]
  rkmMasks_m64_r17 = rkmRow_m64_r17 := bh0_eq (tl1 bk_7)
/-- Kernel trajectory certificate `(m = 32, r = 18)`. -/
theorem rkmTraj_m32_r18 : rkmEvalT16Lo12 32 256 18 [1, 1, 1, 1] [93388119, 36594109, 25852814,
  10053374] [13, 6, 5, 3] rkmMasks_m32_r18 = rkmRow_m32_r18 := bh0_eq (tl1 bk_9)
/-- Krotov trajectory `(m = 32, r = 96)`. -/
theorem rkmTrajPack_m32_r96 : rkmEvalT16Lo12 32 256 96 [1,1,2,3,5,5,5,5]
  [10657892,29700259,17163003,16625651,14548317,18951346,5603301,1897952] [5,12,13,17,21,27,8,3]
  rkmMasksPack_m32_r96 = rkmRowPack_m32_r96 :=
    bhW_eq bk_7 (wSkip (wSkip (wSkip (wCons (bSlideChk_sound bk_18) (wCons (bSlideChk_sound bk_14)
      (wCons (bSlideChk_sound bk_3) wNil))))))
/-- Krotov trajectory `(m = 4, r = 3)`. -/
theorem rkmTrajPack_m4_r3 : rkmEvalT16Lo12 4 2048 3 [1,1,1,1,1,1]
  [126263759,113792387,61478563,63017453,31096551,22614910] [2,2,1,1,1,1] rkmMasksPack_m4_r3 =
  rkmRowPack_m4_r3 := bh0_eq (tl1 (tl2 bk_13))
/-- Krotov trajectory `(m = 32, r = 60)`. -/
theorem rkmTrajPack_m32_r60 : rkmEvalT16Lo12 32 256 60 [3,3,3,3,3,3,3,3]
  [21911534,33154245,15449612,8716716,7754215,6071261,4530997,2846035] [15,23,11,6,6,5,4,2]
  rkmMasksPack_m32_r60 = rkmRowPack_m32_r60 :=
    bhW_eq bk_0 (wSkip (wCons (bSlideChk_sound bk_20) wNil))
/-- Krotov trajectory `(m = 4, r = 35)`. -/
theorem rkmTrajPack_m4_r35 : rkmEvalT16Lo12 4 2048 35 [1,1,1,1,1,1,1,1]
  [23283284,37354801,15350138,1393952,13764419,295771,14710,3526417] [1,2,1,1,1,1,1,1]
  rkmMasksPack_m4_r35 = rkmRowPack_m4_r35 := bh0_eq (tl1 (tl2 bk_12))
/-- Krotov trajectory `(m = 16, r = 64)`. -/
theorem rkmTrajPack_m16_r64 : rkmEvalT16Lo12 16 512 64 [1,2,4,7,7,7,7,7]
  [39273366,22292038,31766892,20789973,18159356,4891556,1411360,682172] [7,7,18,17,15,4,2,1]
  rkmMasksPack_m16_r64 = rkmRowPack_m16_r64 :=
    bhW_eq bk_1 (wSkip (wSkip (wCons (bSlideChk_sound (tl1 bk_22)) wNil)))
/-- Krotov trajectory `(m = 2, r = 5)`. -/
theorem rkmTrajPack_m2_r5 : rkmEvalT16Lo12 2 4096 5 [1,2,4,4,4,4,4,4]
  [103311246,106765511,45449484,66907126,24550734,12349231,3808479,1203984] [1,2,1,2,1,1,1,1]
  rkmMasksPack_m2_r5 = rkmRowPack_m2_r5 := bh0_eq (tl2 bk_2)
/-- Krotov trajectory `(m = 64, r = 48)`. -/
theorem rkmTrajPack_m64_r48 : rkmEvalT16Lo12 64 128 48 [1,1,1,1,1,1,1,1]
  [58324703,16331341,11719221,10369244,9379848,8876018,12931525,7408817] [26,8,6,5,5,4,6,4]
  rkmMasksPack_m64_r48 = rkmRowPack_m64_r48 := bhW_eq bk_16 (wCons (bSlideChk_sound bk_22) wNil)
/-- Krotov trajectory `(m = 16, r = 6)`. -/
theorem rkmTrajPack_m16_r6 : rkmEvalT16Lo12 16 512 6 [1,1,1,1,1,1,1,1]
  [40222723,44195489,16819254,35279281,17551714,23968355,18088879,9917575] [2,2,1,2,1,1,1,1]
  rkmMasksPack_m16_r6 = rkmRowPack_m16_r6 := bh0_eq (tl1 (tl2 bk_10))
/-- Krotov trajectory `(m = 32, r = 41)`. -/
theorem rkmTrajPack_m32_r41 : rkmEvalT16Lo12 32 256 41 [2,2,2,2,2,2,2,2]
  [39119166,26101514,19221589,15409961,7739417,5433092,6395474,4464361] [15,10,8,6,3,3,3,2]
  rkmMasksPack_m32_r41 = rkmRowPack_m32_r41 := bh0_eq bk_10
/-- Krotov trajectory `(m = 2, r = 8)`. -/
theorem rkmTrajPack_m2_r8 : rkmEvalT16Lo12 2 4096 8 [1,2,4,6,6,6,6,6]
  [84031614,64596330,97178089,46364063,34488416,14677448,3963305,2829001] [1,2,3,2,2,1,1,1]
  rkmMasksPack_m2_r8 = rkmRowPack_m2_r8 := bh0_eq (tl1 (tl2 bk_21))
/-- Krotov trajectory `(m = 64, r = 80)`. -/
theorem rkmTrajPack_m64_r80 : rkmEvalT16Lo12 64 128 80 [1,1,1,1,1,1,1,1]
  [6229559,10619513,6289694,2103231,3772865,2216417,1414092,1191582] [4,7,4,2,3,2,1,1]
  rkmMasksPack_m64_r80 = rkmRowPack_m64_r80 := bh0_eq bk_19
/-- Krotov trajectory `(m = 2, r = 26)`. -/
theorem rkmTrajPack_m2_r26 : rkmEvalT16Lo12 2 4096 26 [1,2,4,8]
  [40968329,36199282,44712521,42905410] [1,2,3,5] rkmMasksPack_m2_r26 = rkmRowPack_m2_r26 :=
    bh0_eq (tl1 (tl2 bk_8))
/-- Krotov trajectory `(m = 64, r = 31)`. -/
theorem rkmTrajPack_m64_r31 : rkmEvalT16Lo12 64 128 31 [1,1,1,1,1,1,1,1]
  [24512417,30224301,23696216,8528649,9591674,7737122,5882692,4071452] [8,10,8,3,3,3,2,2]
  rkmMasksPack_m64_r31 = rkmRowPack_m64_r31 := bh0_eq (tl1 bk_23)
/-- Krotov trajectory `(m = 8, r = 11)`. -/
theorem rkmTrajPack_m8_r11 : rkmEvalT16Lo12 8 1024 11 [1,2,2,2,2]
  [120837873,68055839,48622313,31576661,14583457] [5,4,3,2,1] rkmMasksPack_m8_r11 =
  rkmRowPack_m8_r11 := bh0_eq (tl2 bk_10)
/-- Krotov trajectory `(m = 32, r = 30)`. -/
theorem rkmTrajPack_m32_r30 : rkmEvalT16Lo12 32 256 30 [1,2,2,2]
  [91420373,33545811,15589570,5413015] [17,10,5,2] rkmMasksPack_m32_r30 = rkmRowPack_m32_r30 :=
    bh0_eq (tl1 bk_19)
/-- Krotov trajectory `(m = 32, r = 12)`. -/
theorem rkmTrajPack_m32_r12 : rkmEvalT16Lo12 32 256 12 [1,1,1] [134763407,10191932,6191455]
  [13,1,1] rkmMasksPack_m32_r12 = rkmRowPack_m32_r12 := bh0_eq (tl2 bk_9)
/-- Krotov trajectory `(m = 8, r = 28)`. -/
theorem rkmTrajPack_m8_r28 : rkmEvalT16Lo12 8 1024 28 [1,2,4,6,6,6]
  [47662408,34781619,36518254,57837958,7144035,7263218] [3,4,7,14,2,2] rkmMasksPack_m8_r28 =
  rkmRowPack_m8_r28 := bh0_eq (tl1 bk_16)
/-- Krotov trajectory `(m = 32, r = 13)`. -/
theorem rkmTrajPack_m32_r13 : rkmEvalT16Lo12 32 256 13 [1,1,1,1,1,1,1,1]
  [51332385,16720317,35403144,14313356,11124967,8137088,9709246,6572887] [5,2,4,2,2,1,1,1]
  rkmMasksPack_m32_r13 = rkmRowPack_m32_r13 := bh0_eq (tl2 bk_17)
/-- Krotov trajectory `(m = 16, r = 24)`. -/
theorem rkmTrajPack_m16_r24 : rkmEvalT16Lo12 16 512 24 [1,2,2,2,2]
  [82696789,69509280,34929926,18901386,9377134] [8,11,6,3,2] rkmMasksPack_m16_r24 =
  rkmRowPack_m16_r24 := bh0_eq (tl1 bk_11)
/-- Krotov trajectory `(m = 4, r = 15)`. -/
theorem rkmTrajPack_m4_r15 : rkmEvalT16Lo12 4 2048 15 [1,2,4,7,7,7,7,7]
  [70144454,49781825,76859869,27216203,25001847,7863623,6960973,3967098] [2,3,6,3,3,1,1,1]
  rkmMasksPack_m4_r15 = rkmRowPack_m4_r15 := bh0_eq (tl1 bk_4)
/-- Krotov trajectory `(m = 4, r = 24)`. -/
theorem rkmTrajPack_m4_r24 : rkmEvalT16Lo12 4 2048 24 [1,2,4,8,11,11,11]
  [38395095,30764077,38961696,40432370,47613211,5809634,6724558] [2,2,4,7,10,2,2]
  rkmMasksPack_m4_r24 = rkmRowPack_m4_r24 := bh0_eq (tl1 bk_12)
/-- Krotov trajectory `(m = 16, r = 60)`. -/
theorem rkmTrajPack_m16_r60 : rkmEvalT16Lo12 16 512 60 [1,1,1,1,1,1,1,1]
  [14124342,24382147,23848180,6738177,2856,696590,142739,3578416] [3,5,4,2,1,1,1,1]
  rkmMasksPack_m16_r60 = rkmRowPack_m16_r60 := bh0_eq (tl1 bk_6)
/-- Krotov trajectory `(m = 8, r = 21)`. -/
theorem rkmTrajPack_m8_r21 : rkmEvalT16Lo12 8 1024 21 [1,4,4,4]
  [84693065,101308018,25802540,6927704] [5,15,4,1] rkmMasksPack_m8_r21 = rkmRowPack_m8_r21 :=
    bh0_eq (tl1 bk_8)
/-- Krotov trajectory `(m = 16, r = 16)`. -/
theorem rkmTrajPack_m16_r16 : rkmEvalT16Lo12 16 512 16 [1,1,1,1,2,2,2,2]
  [20968205,33019097,21105407,45544089,23189103,26630425,22977581,9203707] [2,3,2,4,3,4,3,2]
  rkmMasksPack_m16_r16 = rkmRowPack_m16_r16 := bh0_eq (tl2 bk_20)
end
end QuantumComputation.Specs.DickeSol
