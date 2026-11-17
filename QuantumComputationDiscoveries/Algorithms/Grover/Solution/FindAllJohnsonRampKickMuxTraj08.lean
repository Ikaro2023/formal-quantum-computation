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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxTraj06
/-
# Multi-Segment `T_16` Trajectory Part `08` (`FindAllJohnsonRampKickMuxTraj08`)

Certified kernel trajectory evaluations (`30` rows, `37987` substep-coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Mask chunk for `(m = 2, r = 28)`. -/
def rkmMkP_m2_r28_s4_p0 : List Bool := [
  false, true, true, false, false, false, true, true, true, true, true, true, false, false, true,
  true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 2, r = 28)`. -/
def rkmMkP_m2_r28_s5_p0 : List Bool := [
  false, true, true, true, false, false, true, false, true, false, false, true, false, true,
  false, false, false, true]
/-- Prefix-kick masks for `(m = 2, r = 28)`. -/
def rkmMasks_m2_r28 : List (List Bool) := [
  [], [], [], [], rkmMkP_m2_r28_s4_p0, rkmMkP_m2_r28_s5_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 28)`. -/
def rkmRow_m2_r28 : List ℕ := [
  45, 118, 12, 4375, 676, 7079, 13441, 902789, 2121, 137833, 4951101, 26110224, 104146789,
  234197664, 122404526, 147438042, 78474830, 3192533673, 2114146499, 1962030190, 11026211800,
  12517799392, 26158427, 23603150605, 262552956958, 431457502170, 217849038464, 32979679693]
/-- Mask chunk for `(m = 4, r = 17)`. -/
def rkmMkP_m4_r17_s4_p0 : List Bool := [
  false, false, true, false, true, false, false, true, false, false, true, false, false, true,
  true]
/-- Mask chunk for `(m = 4, r = 17)`. -/
def rkmMkP_m4_r17_s6_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, true, false, true, false,
  false, true]
/-- Prefix-kick masks for `(m = 4, r = 17)`. -/
def rkmMasks_m4_r17 : List (List Bool) := [
  [], [], [false, true, false, true, true],
  [true, false, false, false, true, true, false, false, true, true, true], rkmMkP_m4_r17_s4_p0,
  [], rkmMkP_m4_r17_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 17)`. -/
def rkmRow_m4_r17 : List ℕ := [
  3435883, 2470745, 62831, 142151054, 466010398, 240888589, 11942944, 1490313973, 423192562,
  2287853683, 308764223, 1436002493, 4921497757, 7656504336, 89697512, 182718206688, 797799571639]
/-- Mask chunk for `(m = 4, r = 128)`. -/
def rkmMkP_m4_r128_s3_p0 : List Bool := [
  true, false, true, true, true, true, true, false, false, false, true, true, true, false, true,
  true, true, true, true, false, true, true]
/-- Mask chunk for `(m = 4, r = 128)`. -/
def rkmMkP_m4_r128_s4_p0 : List Bool := [
  false, false, true, false, true, false, true, true, true, false, false, true, true, false, true,
  true, false, true, true, true, true, true, false, true, true, true, false, false, false, false,
  true, true, true, true, true, true, false, false, true, false, false, false, false, false,
  false, true, true, true, false, false, false, false, false, false, false, false, false, false,
  false, true, true, true, true, true]
/-- Mask chunk for `(m = 4, r = 128)`. -/
def rkmMkP_m4_r128_s4_p1 : List Bool := [
  true, true, true, true, true, false, false, false, false, true, true, true, true, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, true, true]
/-- Mask chunk for `(m = 4, r = 128)`. -/
def rkmMkP_m4_r128_s5_p0 : List Bool := [
  false, true, false, false, false, true, true, true, true, true, true, false, true, true, false,
  false, true, true, false, true, true, true, false, true, false, true, false, false, true, false,
  true, false, true, false, true, false, true, true, false, false, true, false, false, true, true,
  false, false, true, true, false, false, true, false, false, true, false, false, true, false,
  false, true, false, false, false]
/-- Mask chunk for `(m = 4, r = 128)`. -/
def rkmMkP_m4_r128_s5_p1 : List Bool := [
  true, false, false, true, true, false, true, true, false, false, true, true, false, false, true,
  true, false, false, true, true, false, false, true, true, false, false, true, true, false,
  false, false, true, true, false, false, false, true, true, true, false, false, false, true,
  true, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true]
/-- Mask chunk for `(m = 4, r = 128)`. -/
def rkmMkP_m4_r128_s6_p0 : List Bool := [
  true, true, true, true, false, true, false, true, false, true, false, false, false, false, true,
  false, false, false, false, false, false, true, false, false, true, false, false, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, false, true,
  false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 4, r = 128)`. -/
def rkmMkP_m4_r128_s6_p1 : List Bool := [
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, true, true, true,
  false, false, true, true, false, true, true, false, false, true, false, false, false, true,
  false, false, false, true, true]
/-- Prefix-kick masks for `(m = 4, r = 128)`. -/
def rkmMasks_m4_r128 : List (List Bool) := [
  [], [], [true, false, true, false, true, true], rkmMkP_m4_r128_s3_p0,
  rkmMkP_m4_r128_s4_p0 ++ rkmMkP_m4_r128_s4_p1, rkmMkP_m4_r128_s5_p0 ++ rkmMkP_m4_r128_s5_p1,
  rkmMkP_m4_r128_s6_p0 ++ rkmMkP_m4_r128_s6_p1, []]
/-- Row chunk `0` `(m = 4, r = 128)`. -/
def rkmRowP_m4_r128_p0 : List ℕ := [
  12998, 75, 48485, 299896, 730894, 443323, 414447, 856399, 86701, 970478, 1638386, 158856,
  886373, 1666168, 290584, 1515019, 932080, 2713313, 8571825, 128388, 18338963, 56539172,
  36928309, 15766556, 3196896, 1902684, 154429, 12491324, 55651188, 69031512, 34153727, 25191170,
  44641411, 37590832, 21674895, 15252849, 28708757, 9734431, 2769288, 2478653, 3633475, 4787205,
  2410547, 14856098, 81403980, 147619367, 73104221, 5187157, 6599318, 6933707, 11169188, 84943713,
  88307210, 56014813, 42144106, 9388145, 8527207, 71950810, 115213478, 158237138, 66457696,
  27203084, 15507681, 75813990]
/-- Row chunk `1` `(m = 4, r = 128)`. -/
def rkmRowP_m4_r128_p1 : List ℕ := [
  82006906, 97718896, 59631350, 1323717, 16071499, 14886677, 132524144, 22426183, 68696936,
  141449850, 209651270, 301878647, 30772361, 141164058, 191052886, 827417567, 52933749, 309947,
  309239558, 586481749, 222407777, 1412575, 275690782, 675246899, 299167509, 5819337, 78711581,
  197368207, 3578860, 68754779, 53515271, 16600373, 47021272, 1112348, 310084258, 434068650,
  51778, 1453050, 52072367, 193380828, 2122079813, 775078088, 1282385211, 64753269, 702136721,
  598864772, 1913703926, 1411386258, 1398055, 582471350, 867420240, 2384862387, 1034862, 90688817,
  3507671664, 1135955998, 3344312451, 488650829, 8275743870, 38928213941, 473655393, 65364241,
  309407940405, 613657074568]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 128)`. -/
def rkmRow_m4_r128 : List ℕ := rkmRowP_m4_r128_p0 ++ rkmRowP_m4_r128_p1
/-- Prefix-kick masks for `(m = 8, r = 3)`. -/
def rkmMasks_m8_r3 : List (List Bool) := [[], [true], [true, true], [true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 3)`. -/
def rkmRow_m8_r3 : List ℕ := [20190865, 72674406034, 927305293953]
/-- Prefix-kick masks for `(m = 8, r = 5)`. -/
def rkmMasks_m8_r5 : List (List Bool) := [[false, true, true], [true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 5)`. -/
def rkmRow_m8_r5 : List ℕ := [60606028, 245605653, 710918659, 65810356050, 933162811914]
/-- Prefix-kick masks for `(m = 8, r = 6)`. -/
def rkmMasks_m8_r6 : List (List Bool) := [
  [], [true], [false, false, true, true], [false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 6)`. -/
def rkmRow_m8_r6 : List ℕ := [
  14057908, 21927927, 881043059, 1087247751, 74270093296, 923717671398]
/-- Prefix-kick masks for `(m = 8, r = 29)`. -/
def rkmMasks_m8_r29 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 29)`. -/
def rkmRow_m8_r29 : List ℕ := [
  20441986, 165226, 13185865, 818276, 9886236, 212763, 4927413, 1001975, 1020379, 39932331,
  79692642, 788475365, 126505892, 8849674362, 6293862026, 16882852445, 180502072765, 349214556120,
  286526245681, 120157544033, 27073631169, 3214513027, 182677401, 3747860]
/-- Mask chunk for `(m = 16, r = 18)`. -/
def rkmMkP_m16_r18_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true]
/-- Mask chunk for `(m = 16, r = 18)`. -/
def rkmMkP_m16_r18_s1_p0 : List Bool := [
  true, true, false, true, true, true, false, false, true, true, true, true, false, true, true]
/-- Mask chunk for `(m = 16, r = 18)`. -/
def rkmMkP_m16_r18_s2_p0 : List Bool := [
  true, false, true, false, true, false, false, true, false, false, true, false, false, true,
  false, true, true]
/-- Prefix-kick masks for `(m = 16, r = 18)`. -/
def rkmMasks_m16_r18 : List (List Bool) := [
  rkmMkP_m16_r18_s0_p0, rkmMkP_m16_r18_s1_p0, rkmMkP_m16_r18_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 18)`. -/
def rkmRow_m16_r18 : List ℕ := [
  7, 286, 21791, 17051, 1502831, 48007, 297151, 14109866, 2901821, 2067718, 883345805, 1882933,
  865515428, 7052344178, 2866547819, 874464719, 39939423671, 947495508735]
/-- Mask chunk for `(m = 16, r = 25)`. -/
def rkmMkP_m16_r25_s1_p0 : List Bool := [
  false, false, true, false, true, false, true, false, true, true, true, false, true, true, false,
  false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 16, r = 25)`. -/
def rkmMkP_m16_r25_s2_p0 : List Bool := [
  true, false, true, false, true, false, true, true, false, true, false, true, false, true, false,
  true, false, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 25)`. -/
def rkmMasks_m16_r25 : List (List Bool) := [[], rkmMkP_m16_r25_s1_p0, rkmMkP_m16_r25_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 25)`. -/
def rkmRow_m16_r25 : List ℕ := [
  95, 244, 18733, 18952, 329191, 608980, 151578, 927, 36952, 2110288, 14664834, 57538899,
  157618939, 410163018, 511494912, 1525251864, 760883418, 7878441, 520035378, 2843657687,
  8807720424, 13335891577, 166364172, 52096156542, 918781403587]
/-- Mask chunk for `(m = 16, r = 34)`. -/
def rkmMkP_m16_r34_s1_p0 : List Bool := [
  false, true, false, true, true, false, true, true, false, true, false, true, false, true, true,
  false, false, false, false, false, false, true, false, true, false, true, false, false, false,
  true, true]
/-- Mask chunk for `(m = 16, r = 34)`. -/
def rkmMkP_m16_r34_s2_p0 : List Bool := [
  false, false, false, true, false, true, true, false, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, false, true, true, true, false,
  true, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 34)`. -/
def rkmMasks_m16_r34 : List (List Bool) := [[], rkmMkP_m16_r34_s1_p0, rkmMkP_m16_r34_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 34)`. -/
def rkmRow_m16_r34 : List ℕ := [
  3, 0, 1, 49, 45, 131, 10, 183, 1037, 2353, 3413, 658, 12554, 215851, 953498, 1554115, 652337,
  71464, 11458, 3665647, 158719192, 94943496, 2462695307, 3644743570, 336404636, 603184121,
  87243859, 214746449, 1962578289, 8836545881, 11154408179, 614395751, 46809425190, 923012820562]
/-- Mask chunk for `(m = 16, r = 44)`. -/
def rkmMkP_m16_r44_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, false, false, true, true, false, false, true, true,
  false, false, true, true, false, false, true, true, false, false, false, false, false, true,
  true]
/-- Mask chunk for `(m = 16, r = 44)`. -/
def rkmMkP_m16_r44_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  true, true, false, true, false, false, false, true, false, false, true, true, false, true,
  false, true, false, true, false, true, false, false, true, false, true, false, false, false,
  true]
/-- Prefix-kick masks for `(m = 16, r = 44)`. -/
def rkmMasks_m16_r44 : List (List Bool) := [
  [], [], [], rkmMkP_m16_r44_s3_p0, rkmMkP_m16_r44_s4_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 44)`. -/
def rkmRow_m16_r44 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 66, 17, 0, 17, 492, 1761, 4519, 3555, 9293,
  2896, 179777, 58350, 2113327, 1195124, 18530446, 36429779, 40383079, 54862089, 2561726,
  6087312741, 3289041926, 787879248, 3166237148, 23321302985, 199674883, 41319962623,
  921672250957]
/-- Prefix-kick masks for `(m = 32, r = 11)`. -/
def rkmMasks_m32_r11 : List (List Bool) := [
  [true, false, false, true, true, false, true, true],
  [true, false, false, true, false, true, true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 11)`. -/
def rkmRow_m32_r11 : List ℕ := [
  160, 289, 5932, 1372771, 1217540, 336482, 203056943, 767476854, 79307857, 20499715377,
  978447509703]
/-- Prefix-kick masks for `(m = 32, r = 13)`. -/
def rkmMasks_m32_r13 : List (List Bool) := [
  [false, false, true, false, false, true, true, false, true, true],
  [true, false, true, false, false, true, false, true, true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 13)`. -/
def rkmRow_m32_r13 : List ℕ := [
  0, 900, 1410, 1137, 85487, 9244530, 3749030, 469543, 418774735, 1141359216, 76948048,
  19066253483, 979283112371]
/-- Prefix-kick masks for `(m = 64, r = 4)`. -/
def rkmMasks_m64_r4 : List (List Bool) := [[true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 4)`. -/
def rkmRow_m64_r4 : List ℕ := [143164, 42897564, 41341569343, 958615326286]
/-- Mask chunk for `(m = 64, r = 14)`. -/
def rkmMkP_m64_r14_s1_p0 : List Bool := [
  false, false, false, false, false, true, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 64, r = 14)`. -/
def rkmMasks_m64_r14 : List (List Bool) := [
  [false, false, false, true, false, true, true, false, false, true, true, true],
  rkmMkP_m64_r14_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 14)`. -/
def rkmRow_m64_r14 : List ℕ := [
  0, 0, 0, 0, 0, 531, 3594, 365579, 1637163, 57848241, 5575038, 100112988, 13782368042,
  986052088672]
/-- Mask chunk for `(m = 64, r = 19)`. -/
def rkmMkP_m64_r19_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, true, true, false, false, true, true,
  false, false, true, true]
/-- Mask chunk for `(m = 64, r = 19)`. -/
def rkmMkP_m64_r19_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, false, true, false, true,
  false, true]
/-- Prefix-kick masks for `(m = 64, r = 19)`. -/
def rkmMasks_m64_r19 : List (List Bool) := [rkmMkP_m64_r19_s0_p0, rkmMkP_m64_r19_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 19)`. -/
def rkmRow_m64_r19 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 3, 20, 1907, 6504, 285711, 622484, 23428367, 19791768, 1129366898, 284411,
  11215614449, 987610597240]
/-- Mask chunk for `(m = 64, r = 29)`. -/
def rkmMkP_m64_r29_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, false, false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 64, r = 29)`. -/
def rkmMkP_m64_r29_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 64, r = 29)`. -/
def rkmMasks_m64_r29 : List (List Bool) := [rkmMkP_m64_r29_s0_p0, rkmMkP_m64_r29_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 29)`. -/
def rkmRow_m64_r29 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 65, 277, 2514, 6639, 87400, 160381, 3086246, 5758422,
  85685548, 293791055, 202328172, 1089097311, 64145984, 9399353418, 988856496082]
/-- Mask chunk for `(m = 64, r = 31)`. -/
def rkmMkP_m64_r31_s0_p0 : List Bool := [
  false, false, false, true, true, true, false, false, true, true, true, true, true, false, true,
  true, false, false, true, true, true, false, true, true, true, true, true]
/-- Mask chunk for `(m = 64, r = 31)`. -/
def rkmMkP_m64_r31_s1_p0 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, false, false, true, false,
  true, false, true, false, true, false, true, false, true, true, false, true, false, false, true,
  true]
/-- Prefix-kick masks for `(m = 64, r = 31)`. -/
def rkmMasks_m64_r31 : List (List Bool) := [rkmMkP_m64_r31_s0_p0, rkmMkP_m64_r31_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 31)`. -/
def rkmRow_m64_r31 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 157, 2096, 12006, 30539, 48582, 22396, 718072,
  27563233, 4024682, 45158902, 772110203, 9690939, 106483648, 2970446574, 64459013, 9277976244,
  986721252166]
/-- Mask chunk for `(m = 128, r = 19)`. -/
def rkmMkP_m128_r19_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 19)`. -/
def rkmMasks_m128_r19 : List (List Bool) := [rkmMkP_m128_r19_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 19)`. -/
def rkmRow_m128_r19 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 162, 4007, 49079, 1318946, 8946324, 178200451, 75675940,
  9383337778, 990352467019]
/-- Mask chunk for `(m = 128, r = 26)`. -/
def rkmMkP_m128_r26_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, true, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 128, r = 26)`. -/
def rkmMkP_m128_r26_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, true, true, false, true, false, true, false, false, true, true]
/-- Mask chunk for `(m = 128, r = 26)`. -/
def rkmMkP_m128_r26_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, false, false, false, false, false, false, true]
/-- Prefix-kick masks for `(m = 128, r = 26)`. -/
def rkmMasks_m128_r26 : List (List Bool) := [
  rkmMkP_m128_r26_s0_p0, rkmMkP_m128_r26_s1_p0, rkmMkP_m128_r26_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 26)`. -/
def rkmRow_m128_r26 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 17, 20, 0, 9729, 150372, 6470584, 199092, 11405602,
  274357021, 585956, 7359117533, 992347703532]
/-- Prefix-kick masks for `(m = 256, r = 11)`. -/
def rkmMasks_m256_r11 : List (List Bool) := [
  [false, false, false, false, false, false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 11)`. -/
def rkmRow_m256_r11 : List ℕ := [
  0, 0, 0, 0, 40, 2026, 86275, 7035, 20334434, 14535803893, 985443766133]
/-- Prefix-kick masks for `(m = 256, r = 14)`. -/
def rkmMasks_m256_r14 : List (List Bool) := [
  [false, false, false, false, false, false, false, true, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 14)`. -/
def rkmRow_m256_r14 : List ℕ := [
  0, 0, 0, 0, 0, 0, 6, 215, 2692, 5862, 5281703, 104809224, 11547729187, 988342170871]
/-- Mask chunk for `(m = 256, r = 48)`. -/
def rkmMkP_m256_r48_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, true, false, false,
  false, true, true]
/-- Mask chunk for `(m = 256, r = 48)`. -/
def rkmMkP_m256_r48_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, false, true, false, false, true, false,
  true, false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 256, r = 48)`. -/
def rkmMasks_m256_r48 : List (List Bool) := [rkmMkP_m256_r48_s0_p0, rkmMkP_m256_r48_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 48)`. -/
def rkmRow_m256_r48 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 43, 3, 107, 81, 35958, 637328, 3589084, 3538718, 12040593, 6078510, 311213906, 4533905,
  3885891851, 995772437917]
/-- Mask chunk for `(m = 256, r = 64)`. -/
def rkmMkP_m256_r64_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 256, r = 64)`. -/
def rkmMkP_m256_r64_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true]
/-- Prefix-kick masks for `(m = 256, r = 64)`. -/
def rkmMasks_m256_r64 : List (List Bool) := [[], rkmMkP_m256_r64_s1_p0, rkmMkP_m256_r64_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 64)`. -/
def rkmRow_m256_r64 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 56, 1579, 20533, 202356, 1449384,
  7252230, 23198591, 29219736, 2497779, 137264342, 31458682, 3136715800, 996630715529]
/-- Prefix-kick masks for `(m = 512, r = 6)`. -/
def rkmMasks_m512_r6 : List (List Bool) := [[], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 6)`. -/
def rkmRow_m512_r6 : List ℕ := [0, 113, 210052, 177202392, 26112586054, 973710001291]
/-- Prefix-kick masks for `(m = 512, r = 10)`. -/
def rkmMasks_m512_r10 : List (List Bool) := [[], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 10)`. -/
def rkmRow_m512_r10 : List ℕ := [0, 0, 0, 0, 0, 2552, 317867, 15999248, 15637793297, 984345886849]
/-- Mask chunk for `(m = 512, r = 22)`. -/
def rkmMkP_m512_r22_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, true]
/-- Prefix-kick masks for `(m = 512, r = 22)`. -/
def rkmMasks_m512_r22 : List (List Bool) := [rkmMkP_m512_r22_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 22)`. -/
def rkmRow_m512_r22 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 294, 11309, 232711, 74, 93796781, 7237248435,
  992668709706]
/-- Prefix-kick masks for `(m = 512, r = 29)`. -/
def rkmMasks_m512_r29 : List (List Bool) := [[], [false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 29)`. -/
def rkmRow_m512_r29 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 38, 2977, 99752, 4776097,
  265347552, 5607427631, 994122344859]
/-- Prefix-kick masks for `(m = 1024, r = 9)`. -/
def rkmMasks_m1024_r9 : List (List Bool) := [[], [], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 9)`. -/
def rkmRow_m1024_r9 : List ℕ := [0, 0, 0, 0, 149, 38028, 74714684, 17198991212, 982726255705]
/-- Prefix-kick masks for `(m = 1024, r = 24)`. -/
def rkmMasks_m1024_r24 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 24)`. -/
def rkmRow_m1024_r24 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 59, 20, 745381, 13439389, 6505225858,
  993480588159]
/-- Unpacks `j` LSB-first bits of `< 2 ^ 50` word `w` (`FindAllJohnsonRampKickMuxTraj08`). -/
def rkmWbTraj08 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWbTraj08 j (Nat.div w 2)
/-- Concatenates `50`-bit `< 2 ^ 50` chunks (final length `rem`) into a `List Bool` mask. -/
def rkmMaskWordsTraj08 : ℕ → List ℕ → List Bool
  | _, [] => []
  | rem, [w] => rkmWbTraj08 rem w
  | rem, w :: v :: ws => rkmWbTraj08 50 w ++ rkmMaskWordsTraj08 rem (v :: ws)
/-- Krotov masks `(m = 2, r = 96)`. -/
def rkmMasksPack_m2_r96 : List (List Bool) := [[], [], rkmWbTraj08 2 3,
  rkmMaskWordsTraj08 4 [668503069688803, 11],
  rkmMaskWordsTraj08 36 [1093998013583000, 58099499008],
  rkmMaskWordsTraj08 32 [375848718259540, 3817628262],
  rkmMaskWordsTraj08 40 [287337610691263, 844149904721], []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 96)`. -/
def rkmRowPack_m2_r96 : List ℕ := [66542, 39454, 40219, 16304, 9473, 5102, 1285, 17761, 49574,
  288116, 282868, 548835, 80256, 99426, 87693, 2837965, 141240, 89077, 14542, 864968, 3017302,
  2663283, 2063477, 65176, 1945691, 32836, 950584, 99684, 73470, 5186240, 1564438, 2980845,
  7748621, 14550508, 988091, 5942262, 30869566, 6770980, 19076033, 1644036, 1480763, 50366489,
  980540, 91314479, 153700195, 39578342, 308880, 9824431, 7509983, 33899641, 197598952, 118978746,
  2273600, 37082365, 239446, 174164898, 117890188, 293706402, 31953395, 50503804, 244283276,
  212003611, 5467361, 225749608, 237099919, 33714064, 57060287, 192532731, 856465623, 137670933,
  13083501, 42486465, 2256295704, 124023197, 36817805, 1144565919, 9748721, 653350640, 1167081348,
  365657210, 12370330, 3011421184, 349001919, 532894026, 3414194917, 2215270414, 79687822, 9963486,
  10333165964, 17581084384, 477493960, 2601314937, 64777310210, 369787692537, 398367318749,
  116907477676]
/-- Krotov masks `(m = 2, r = 4)`. -/
def rkmMasksPack_m2_r4 : List (List Bool) := [[], rkmWbTraj08 1 1, rkmWbTraj08 2 3, [],
  rkmWbTraj08 3 4, [], rkmWbTraj08 3 4, []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 4)`. -/
def rkmRowPack_m2_r4 : List ℕ := [44052989, 254898, 350565329906, 649266196491]
/-- Krotov masks `(m = 64, r = 63)`. -/
def rkmMasksPack_m64_r63 : List (List Bool) := [[], rkmWbTraj08 2 3, rkmWbTraj08 24 13078279,
  rkmMaskWordsTraj08 3 [124847840980308, 7], rkmMaskWordsTraj08 8 [644703749931733, 230],
  rkmMaskWordsTraj08 10 [715604367578474, 874], rkmMaskWordsTraj08 12 [749134009107797, 3346], []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 63)`. -/
def rkmRowPack_m64_r63 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 23, 41, 844, 986, 8, 513, 152, 17581, 7439,
  5996, 352036, 2804344, 3351121, 197516, 5117994, 6940225, 112460835, 64785033, 136604987,
  209442674, 649676967, 1828447051, 9020043, 9438914712, 987531848223]
/-- Krotov masks `(m = 4, r = 52)`. -/
def rkmMasksPack_m4_r52 : List (List Bool) := [[], [], [], [], [], rkmWbTraj08 4 11,
  rkmWbTraj08 4 11, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 52)`. -/
def rkmRowPack_m4_r52 : List ℕ := [28112319, 5569780531, 147478908558, 846923113452]
/-- Krotov masks `(m = 64, r = 55)`. -/
def rkmMasksPack_m64_r55 : List (List Bool) := [[], rkmWbTraj08 40 977537545094,
  rkmWbTraj08 47 126878256641366, rkmMaskWordsTraj08 1 [645779851750061, 1],
  rkmMaskWordsTraj08 3 [565346899940684, 4], rkmMaskWordsTraj08 4 [706653830337844, 8],
  rkmMaskWordsTraj08 4 [9483432799008, 8], []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 55)`. -/
def rkmRowPack_m64_r55 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 30, 135, 150,
  15, 463, 45, 232, 717, 2053, 17501, 17378, 35678, 174752, 1157866, 2788166, 2444124, 438194,
  1390625, 2439164, 6811882, 3457502, 17474770, 12426513, 568725, 7693556, 113866151, 21308569,
  522335687, 45278144, 256182032, 46732247, 42141174, 671776808, 245135087, 859986603, 10867488478,
  72748829, 18549818741, 967625859159]
/-- Krotov masks `(m = 2, r = 22)`. -/
def rkmMasksPack_m2_r22 : List (List Bool) := [[], [], []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 22)`. -/
def rkmRowPack_m2_r22 : List ℕ := [17307482, 987801773, 930272682, 47597406998, 325408089334,
  425140487995, 177308341444, 22000957220]
/-- Krotov masks `(m = 64, r = 51)`. -/
def rkmMasksPack_m64_r51 : List (List Bool) := [[], rkmWbTraj08 36 61083950195,
  rkmWbTraj08 43 7912727946537, rkmWbTraj08 48 221196542323286, rkmWbTraj08 50 633398915338922, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 51)`. -/
def rkmRowPack_m64_r51 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 17, 0, 6, 0, 103, 232,
  763, 25, 334, 3031, 5656, 18130, 36002, 85231, 270799, 1917811, 611861, 235560, 2404498, 108805,
  9918372, 3086407, 57492808, 28494267, 47313946, 264633841, 180901344, 82014405, 124440225,
  12183144, 472861309, 13511861, 463054330, 285855335, 7600915369, 9080932393, 50829703,
  13907110414, 967308749848]
/-- Krotov masks `(m = 8, r = 5)`. -/
def rkmMasksPack_m8_r5 : List (List Bool) := [[], [], rkmWbTraj08 2 3, rkmWbTraj08 3 4,
  rkmWbTraj08 4 12, rkmWbTraj08 4 8, rkmWbTraj08 4 8, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 5)`. -/
def rkmRowPack_m8_r5 : List ℕ := [12060212, 3488418, 74843384, 65029493666, 934878125879]
/-- Krotov masks `(m = 64, r = 42)`. -/
def rkmMasksPack_m64_r42 : List (List Bool) := [[], rkmWbTraj08 1 1, rkmWbTraj08 29 477338720,
  rkmWbTraj08 36 61852788438, rkmWbTraj08 39 432368424277, rkmWbTraj08 40 559565574848,
  rkmWbTraj08 41 1102005881515, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 42)`. -/
def rkmRowPack_m64_r42 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 23, 264, 309, 702, 1,
  1665, 6489, 42458, 20011, 112456, 327, 480793, 24041, 760791, 72505, 4482383, 1395236, 904656,
  1648480, 100757034, 5993670, 40904935, 321561249, 41349927, 103807704, 1441589152, 74504656,
  10181197769, 987678379277]
/-- Krotov masks `(m = 4, r = 7)`. -/
def rkmMasksPack_m4_r7 : List (List Bool) := [[], rkmWbTraj08 3 5, rkmWbTraj08 5 26,
  rkmWbTraj08 6 36, rkmWbTraj08 6 33, rkmWbTraj08 1 1, rkmWbTraj08 6 32, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 7)`. -/
def rkmRowPack_m4_r7 : List ℕ := [362659609, 5329826, 567300650, 3946113749, 896620, 153964732044,
  841142029787]
/-- Krotov masks `(m = 64, r = 36)`. -/
def rkmMasksPack_m64_r36 : List (List Bool) := [rkmWbTraj08 34 12750684160,
  rkmWbTraj08 36 34359738937, rkmWbTraj08 23 8276084, rkmWbTraj08 30 970599652,
  rkmWbTraj08 33 6754227114, rkmWbTraj08 34 8741115180, rkmWbTraj08 35 18556300634, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 36)`. -/
def rkmRowPack_m64_r36 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 10, 0, 0, 184, 590, 1260,
  41325, 1720, 153176, 2696, 141859, 57821, 1460598, 212665, 18323502, 4263981, 24100151, 69614310,
  32658817, 102644060, 619013162, 128442797, 9401678334, 989597186200]
/-- Krotov masks `(m = 8, r = 9)`. -/
def rkmMasksPack_m8_r9 : List (List Bool) := [[], rkmWbTraj08 7 102, rkmWbTraj08 8 149, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 9)`. -/
def rkmRowPack_m8_r9 : List ℕ := [6746852, 39012902, 356859694, 919303576, 176491845, 5608560817,
  320390904, 73693446752, 918879019482]
/-- Krotov masks `(m = 32, r = 34)`. -/
def rkmMasksPack_m32_r34 : List (List Bool) := [[], []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 34)`. -/
def rkmRowPack_m32_r34 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 30, 107, 1403, 0,
  21871, 26662, 129157, 857309, 81326, 10304180, 3922949, 61928482, 143706871, 174003954,
  1764733102, 86457985, 13639686750, 900960189, 89870418350, 22169785057, 871172973363]
/-- Krotov masks `(m = 4, r = 11)`. -/
def rkmMasksPack_m4_r11 : List (List Bool) := [[], rkmWbTraj08 2 2, rkmWbTraj08 6 43,
  rkmWbTraj08 9 410, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 11)`. -/
def rkmRowPack_m4_r11 : List ℕ := [3574247, 2155146, 465197292, 1604835579, 21059880, 1443273644,
  8057, 12778176471, 6208031971, 204761668822, 772690087398]
/-- Krotov masks `(m = 16, r = 31)`. -/
def rkmMasksPack_m16_r31 : List (List Bool) := [[], rkmWbTraj08 29 429500993,
  rkmWbTraj08 30 626346506, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 31)`. -/
def rkmRowPack_m16_r31 : List ℕ := [0, 0, 32, 14, 0, 133, 2, 112, 8, 153, 13333, 108682, 17857,
  19504, 42896, 758084, 5728442, 15395066, 74419634, 116540662, 507343751, 503060436, 2257086452,
  1232437228, 5690224242, 2146575533, 898624854, 22709022162, 1157529, 41780689548, 922060732977]
/-- Krotov masks `(m = 2, r = 13)`. -/
def rkmMasksPack_m2_r13 : List (List Bool) := [[], [], [], rkmWbTraj08 6 56, rkmWbTraj08 9 402,
  rkmWbTraj08 11 1544, rkmWbTraj08 11 1276, []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 13)`. -/
def rkmRowPack_m2_r13 : List ℕ := [16217876, 312733162, 30533721, 165326571, 279929818, 252623201,
  1682000194, 2054838967, 9165505060, 462077129, 12348600363, 448145207786, 525083695507]
/-- Krotov masks `(m = 64, r = 26)`. -/
def rkmMasksPack_m64_r26 : List (List Bool) := [[], [], rkmWbTraj08 14 8935, rkmWbTraj08 19 472710,
  rkmWbTraj08 22 4039550, rkmWbTraj08 24 14328990, rkmWbTraj08 25 17283876, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 26)`. -/
def rkmRowPack_m64_r26 : List ℕ := [0, 0, 2, 0, 7, 0, 86, 198, 220, 1563, 35, 5156, 6054, 2825,
  5587, 165487, 27823, 2245085, 3932390, 2553939, 30137, 122481754, 270799725, 125287935,
  9678012297, 989794441306]
/-- Krotov masks `(m = 8, r = 14)`. -/
def rkmMasksPack_m8_r14 : List (List Bool) := [[], rkmWbTraj08 3 6, rkmWbTraj08 12 3279,
  rkmWbTraj08 13 4779, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 14)`. -/
def rkmRowPack_m8_r14 : List ℕ := [1249929, 957996, 11188495, 27006572, 121024987, 391001191,
  598211110, 2372503586, 1489383287, 79164, 15529120507, 119781868, 78309698198, 901028726338]
/-- Krotov masks `(m = 32, r = 52)`. -/
def rkmMasksPack_m32_r52 : List (List Bool) := [rkmWbTraj08 22 3425024, rkmWbTraj08 32 4151099136,
  rkmWbTraj08 32 3987070976, rkmWbTraj08 32 4172824506, rkmWbTraj08 30 758169603,
  rkmWbTraj08 32 3223257187, rkmWbTraj08 32 3394633856, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 52)`. -/
def rkmRowPack_m32_r52 : List ℕ := [64041165, 140857046, 1645289728, 1146876437, 1015012068,
  5058487040, 10108192229, 1272798668, 69193028, 24601721, 8313597635, 43681775051, 1543628658,
  18546403844, 1677828740, 97999462766, 684504855887, 118175322277, 3521017385, 859398677,
  508484556, 62012992, 5181385, 301424, 46194, 43169, 6011, 351, 3, 0, 0, 0]
/-- Krotov masks `(m = 4, r = 14)`. -/
def rkmMasksPack_m4_r14 : List (List Bool) := [[], [], rkmWbTraj08 6 59, rkmWbTraj08 10 822,
  rkmWbTraj08 12 2345, rkmWbTraj08 13 4423, rkmWbTraj08 13 4193, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 14)`. -/
def rkmRowPack_m4_r14 : List ℕ := [10873004, 28629060, 94677640, 5870017, 116356203, 121303038,
  969337133, 246459829, 2002279109, 6068302701, 4538649873, 19223, 170211530502, 815585281153]
/-- Krotov masks `(m = 32, r = 20)`. -/
def rkmMasksPack_m32_r20 : List (List Bool) := [rkmWbTraj08 17 131071, rkmWbTraj08 3 7,
  rkmWbTraj08 13 7203, rkmWbTraj08 17 105045, rkmWbTraj08 18 152149, rkmWbTraj08 19 267603,
  rkmWbTraj08 19 295191, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 20)`. -/
def rkmRowPack_m32_r20 : List ℕ := [26, 35, 161, 17, 1448, 12730, 111228, 89074, 1970981, 107361,
  21388133, 8939137, 13235475, 127074473, 4094806, 210429968, 1001465286, 79272434, 19066725758,
  979465081224]
/-- Krotov masks `(m = 2, r = 20)`. -/
def rkmMasksPack_m2_r20 : List (List Bool) := [[], [], [], rkmWbTraj08 4 11, rkmWbTraj08 16 59391,
  rkmWbTraj08 14 11039, []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 20)`. -/
def rkmRowPack_m2_r20 : List ℕ := [8739, 178914, 432896, 11142874, 2267506, 5258618, 7974745,
  92178422, 478056, 680507255, 450087136, 5239736038, 453875844, 3149561968, 24378197416, 99658822,
  22745117091, 333563400114, 472143968894, 136975967882]
/-- Krotov masks `(m = 8, r = 60)`. -/
def rkmMasksPack_m8_r60 : List (List Bool) := [rkmWbTraj08 7 88, [], [], [],
  rkmWbTraj08 21 1388545, rkmWbTraj08 24 14872620, rkmWbTraj08 21 1527839, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 60)`. -/
def rkmRowPack_m8_r60 : List ℕ := [453209, 17263691, 46363156, 1474811964, 35396443, 1297619451,
  3410767559, 213114502, 395872774, 34215033371, 151717462774, 795470512944, 1490655075,
  7578588624, 403175608, 1841075196, 359322150, 32029509, 465856, 705, 766, 1325, 323, 31, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0]
/-- Krotov masks `(m = 16, r = 112)`. -/
def rkmMasksPack_m16_r112 : List (List Bool) := [rkmWbTraj08 15 20351, rkmWbTraj08 16 46079,
  rkmWbTraj08 16 45052, rkmWbTraj08 10 1019, rkmWbTraj08 11 1024, rkmWbTraj08 11 2027,
  rkmWbTraj08 5 22, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 112)`. -/
def rkmRowPack_m16_r112 : List ℕ := [868461804, 103712380, 16810151, 815604669, 53875, 300196585,
  590971228, 11056867, 2108114263, 1542991718, 365393937, 62310986, 169368856, 6554390,
  202897972856, 789349941224]
/-- Cumulative `2`-lane trajectory head invariant (`Traj06` -> `Traj08`). -/
def rkmTrajLaneProp_08 : Prop :=
  rkmTrajLaneProp_06 ∧ (rkmRow_m2_r28.head? = some 45)
/-- Proof of `rkmTrajLaneProp_08` in `O(1)` kernel steps. -/
theorem rkmTrajLaneOk_08 : rkmTrajLaneProp_08 :=
  ⟨rkmTrajLaneOk_06, rfl⟩
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
private theorem n0m (z : ℕ) : (0 : ℕ) = Nat.mul 0 z := by
  rw [Nat.mul_eq]
  omega
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem bFN {α : Type} (x : ℕ) (k : ℕ → α) :
    HighDForce.withForcedNat x k = k x := by
  unfold HighDForce.withForcedNat
  rw [n1a]
private theorem bFL {α β : Type} (xs : List α) (k : List α → β) :
    HighDForce.withForcedList xs k = k xs := by cases xs <;> rfl
private theorem bBle : ∀ {a b : ℕ}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (bBle h)
private def bNatEq (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem bNatEq_t {a b : ℕ} (h : bNatEq a b = true) : a = b := by
  unfold bNatEq at h
  revert h
  cases h1 : Nat.ble a b with
  | false => exact Bool.noConfusion
  | true =>
    cases h2 : Nat.ble b a with
    | false => exact Bool.noConfusion
    | true => exact fun _ => Nat.le_antisymm (bBle h1) (bBle h2)
private def bNLE : List ℕ → List ℕ → Bool
  | [], [] => true
  | x :: xs, y :: ys => cond (bNatEq x y) (bNLE xs ys) false
  | _, _ => false
private theorem bNLE_t : ∀ {xs ys : List ℕ}, bNLE xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    unfold bNLE at h
    revert h
    cases hx : bNatEq x y with
    | false => exact Bool.noConfusion
    | true => exact fun h => congrArg₂ List.cons (bNatEq_t hx) (bNLE_t h)
private def bIntEq : ℤ → ℤ → Bool
  | Int.ofNat a, Int.ofNat b => bNatEq a b
  | Int.negSucc a, Int.negSucc b => bNatEq a b
  | _, _ => false
private theorem bIntEq_t : ∀ {a b : ℤ}, bIntEq a b = true → a = b
  | Int.ofNat _, Int.ofNat _, h => congrArg Int.ofNat (bNatEq_t h)
  | Int.negSucc _, Int.negSucc _, h => congrArg Int.negSucc (bNatEq_t h)
  | Int.ofNat _, Int.negSucc _, h => Bool.noConfusion h
  | Int.negSucc _, Int.ofNat _, h => Bool.noConfusion h
private def bILE : List ℤ → List ℤ → Bool
  | [], [] => true
  | x :: xs, y :: ys => cond (bIntEq x y) (bILE xs ys) false
  | _, _ => false
private theorem bILE_t : ∀ {xs ys : List ℤ}, bILE xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => Bool.noConfusion h
  | _ :: _, [], h => Bool.noConfusion h
  | x :: xs, y :: ys, h => by
    unfold bILE at h
    revert h
    cases hx : bIntEq x y with
    | false => exact Bool.noConfusion
    | true => exact fun h => congrArg₂ List.cons (bIntEq_t hx) (bILE_t h)
private theorem bhd_eq {x y : List ℕ} {s : List Bool} (h : atF (bNLE x y :: s) = true) : x = y := by
  revert h
  cases h0 : bNLE x y with
  | false => exact Bool.noConfusion
  | true => exact fun _ => bNLE_t h0
private def uC (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs
  | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uC_eq (x : ℕ) (xs : List ℕ) : uC x xs = x :: xs := by
  unfold uC
  rw [n1a]
  cases xs <;> rfl
private def uHb : List ℤ → Option (List ℕ)
  | [] => some []
  | Int.ofNat n :: xs => match uHb xs with | some ns => some (uC n ns) | none => none
  | Int.negSucc _ :: _ => none
private def uOh : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOh ns
private theorem uHb_s : ∀ (hb : List ℤ) (ns : List ℕ), uHb hb = some ns → hb = uOh ns
  | [], ns, h => by
    injection h with h'
    subst h'
    rfl
  | Int.negSucc _ :: _, _, h => by
    dsimp only [uHb] at h
    cases h
  | Int.ofNat n :: xs, ns, h => by
    dsimp only [uHb] at h
    revert h
    cases hxs : uHb xs with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some ms =>
      intro h
      dsimp only at h
      injection h with h'
      subst h'
      rw [uC_eq, uOh, uHb_s xs ms hxs]
private theorem bPOf (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  unfold primOfNatForced
  rw [n1a]
private theorem bPNS (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  unfold primNegSuccForced
  rw [n1a]
private theorem bPNeg : ∀ (x : ℕ), primNegOfNat x = -(x : ℤ)
  | 0 => by
    dsimp only [primNegOfNat]
    rw [Int.ofNat_eq_natCast]
    omega
  | k + 1 => by
    dsimp only [primNegOfNat]
    rw [bPNS, Int.negSucc_eq]
    omega
private theorem bPSub (m n : ℕ) : primSubNatNat m n = (m : ℤ) - (n : ℤ) := by
  unfold primSubNatNat
  simp only [Nat.sub_eq]
  cases h : n - m with
  | zero =>
    dsimp only
    rw [bPOf, Int.ofNat_eq_natCast]
    omega
  | succ k =>
    dsimp only
    rw [bPNS, Int.negSucc_eq]
    omega
private theorem bPMul (a b : ℤ) : primIntMul a b = a * b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      dsimp only [primIntMul]
      simp only [bPOf, Nat.mul_eq, Int.ofNat_eq_natCast]
      push_cast
      ring
    | negSucc n =>
      dsimp only [primIntMul]
      simp only [bPNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
  | negSucc m =>
    cases b with
    | ofNat n =>
      dsimp only [primIntMul]
      simp only [bPNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
    | negSucc n =>
      dsimp only [primIntMul]
      simp only [bPOf, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
  | Int.ofNat v => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t
private theorem bCZ_eq (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem bSC_eq (x : ℤ) (xs : List ℤ) : highdStrictConsInt x xs = x :: xs := by
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
  | u :: us => bCZ (primSubNatNat u z) (bDec z us)
private theorem bDec0 (z : ℕ) : bDec z [] = [] := rfl
private theorem bDecS (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by
  rw [bDec, bCZ_eq, bPSub]
private theorem bDecL (z : ℕ) : ∀ (cs : List ℕ), altIntLen (bDec z cs) = altListLen cs
  | [] => rfl
  | _ :: cs => by rw [bDecS, altIntLen, altListLen, bDecL z cs]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]
  omega
private theorem bPM0 (z : ℕ) : primIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bPMul, bZ0]
  rfl
private def bE1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k => match Nat.sub z (Nat.add k 1) with | 0 => none | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs => match bE1 z x with
    | none => none
    | some u => match bEnc z xs with | none => none | some us => some (uC u us)
private theorem bE1_s (z : ℕ) (x : ℤ) (u : ℕ) (h : bE1 z x = some u) : ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bE1 at h
    injection h with h'
    subst h'
    rw [Nat.add_eq, Int.ofNat_eq_natCast]
    omega
  | negSucc k =>
    unfold bE1 at h
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
private theorem bEnc_s (z : ℕ) : ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us → bDec z us = xs
  | [], us, h => by
    injection h with h'
    subst h'
    rfl
  | x :: xs, us, h => by
    dsimp only [bEnc] at h
    revert h
    cases hx : bE1 z x with
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
        rw [uC_eq, bDecS, bE1_s z x u hx, bEnc_s z xs ws hxs]
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
  | Int.negSucc k, d => by
    dsimp only [muxRawIntTdivNat, zTd]
    rw [bNeg, ndiv, Nat.add_eq]
private theorem bRSubN (m n : ℕ) : muxRawSubNatNat m n = (m : ℤ) - (n : ℤ) := by
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
private theorem bRAdd (a b : ℤ) : muxRawIntAdd a b = a + b := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      dsimp only [muxRawIntAdd]
      simp only [bPOf, Nat.add_eq, Int.ofNat_eq_natCast]
      omega
    | negSucc n =>
      dsimp only [muxRawIntAdd]
      simp only [bRSubN, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
  | negSucc m =>
    cases b with
    | ofNat n =>
      dsimp only [muxRawIntAdd]
      simp only [bRSubN, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
    | negSucc n =>
      dsimp only [muxRawIntAdd]
      simp only [bPNS, Nat.add_eq, Int.negSucc_eq]
      omega
private theorem bRNeg (a : ℤ) : muxRawIntNeg a = -a := by
  cases a with
  | ofNat n =>
    dsimp only [muxRawIntNeg]
    simp only [bNeg, Int.ofNat_eq_natCast]
  | negSucc n =>
    dsimp only [muxRawIntNeg]
    simp only [bPOf, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
private theorem bRSub (a b : ℤ) : muxRawIntSub a b = a - b := by
  unfold muxRawIntSub
  rw [bRAdd, bRNeg]
  omega
private theorem bRMul (a b : ℤ) : muxRawIntMul a b = a * b := by
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
      simp only [bNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
  | negSucc m =>
    cases b with
    | ofNat n =>
      dsimp only [muxRawIntMul]
      simp only [bNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
    | negSucc n =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
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
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bSV v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bChb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bDec z rest = tailZ) :
    bDec z (uC (bCV z d b0 c0 b v c1) rest) =
      highdStrictConsInt (muxRawIntAdd ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntSub (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ)))) d)) tailZ := by
  rw [uC_eq, bDecS, ht, bSC_eq, bRAdd, bTdN, bRSub, bPMul, bRMul]
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
    (hv : 0 < bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDec z rest = tailZ) :
    bDec z (uC (bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      highdStrictConsInt (muxRawIntAdd ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d)) tailZ := by
  rw [uC_eq, bDecS, ht, bSC_eq, bRAdd, bTdN, bPMul]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [bSV_eq z v _ _ d hv, hpq]
private def bPos : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bPos xs)
private theorem bPosC {x : ℕ} {xs : List ℕ} (h : bPos (uC x xs) = true) :
    0 < x ∧ bPos xs = true := by
  rw [uC_eq] at h
  cases x with
  | zero => exact Bool.noConfusion h
  | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHd (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTl : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem bHd_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHd z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by
    unfold bHd
    rw [bDec0, bZ0]
  | c :: cs => by
    unfold bHd
    rw [bDecS]
private theorem bTl_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTl xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | x :: xs => by
    unfold bTl
    rw [bDecS]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs =>
    match bns with
    | [] =>
      uC (bSV (bHd z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSl z d rem 0 z [] (bTl vs) (bTl cs))
    | b :: bR =>
      match vs, cs with
      | v :: vT, c :: cT => uC (bCV z d b0 c0 b v (bHd z cT)) (bSl z d rem b c bR vT cT)
      | v :: vT, [] => uC (bCV z d b0 c0 b v z) (bSl z d rem b z bR vT [])
      | [], c :: cT => uC (bCV z d b0 c0 b z (bHd z cT)) (bSl z d rem b c bR [] cT)
      | [], [] => uC (bCV z d b0 c0 b z z) (bSl z d rem b z bR [] [])
private theorem bSl_len (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    altListLen (bSl z d rem b0 c0 bns vs cs) = rem
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, [], vs, cs => by
    dsimp only [bSl]
    rw [uC_eq, altListLen, Nat.add_eq, bSl_len z d rem 0 z [] (bTl vs) (bTl cs)]
  | rem + 1, b0, c0, b :: bR, vs, cs => by
    cases vs with
    | nil =>
      cases cs with
      | nil =>
        dsimp only [bSl]
        rw [uC_eq, altListLen, Nat.add_eq, bSl_len z d rem b z bR [] []]
      | cons c cT =>
        dsimp only [bSl]
        rw [uC_eq, altListLen, Nat.add_eq, bSl_len z d rem b c bR [] cT]
    | cons v vT =>
      cases cs with
      | nil =>
        dsimp only [bSl]
        rw [uC_eq, altListLen, Nat.add_eq, bSl_len z d rem b z bR vT []]
      | cons c cT =>
        dsimp only [bSl]
        rw [uC_eq, altListLen, Nat.add_eq, bSl_len z d rem b c bR vT cT]
private theorem bSl_s (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bPos (bSl z d rem b0 c0 bns vs cs) = true →
      bDec z (bSl z d rem b0 c0 bns vs cs) =
      muxFastSlideLoopAux d rem (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOh bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSl, uOh, muxFastSlideLoopAux] at h ⊢
      have hp := bPosC h
      have hi := bSl_s z d rem 0 z [] (bTl vs) (bTl cs) hp.2
      rw [bPM0 z, uOh, bTl_eq z vs, bTl_eq z cs] at hi
      have hc := bC0 z d b0 c0 (bHd z vs) hp.1 hi
      rw [bHd_eq z vs] at hc
      exact hc
    | cons b bR =>
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSl, uOh] at h ⊢
          rw [bDec0]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPosC h
          have hi := bSl_s z d rem b z bR [] [] hp.2
          rw [bZ0 z, bDec0] at hi
          have hc := bChb z d b0 c0 b z z hp.1 hi
          rw [bZ0 z] at hc
          exact hc
        | cons c cT =>
          dsimp only [bSl, uOh] at h ⊢
          rw [bDec0, bDecS z c cT]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPosC h
          have hi := bSl_s z d rem b c bR [] cT hp.2
          rw [bDec0] at hi
          have hc := bChb z d b0 c0 b z (bHd z cT) hp.1 hi
          rw [bHd_eq z cT, bZ0 z] at hc
          exact hc
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSl, uOh] at h ⊢
          rw [bDecS z v vT, bDec0]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPosC h
          have hi := bSl_s z d rem b z bR vT [] hp.2
          rw [bZ0 z, bDec0] at hi
          have hc := bChb z d b0 c0 b v z hp.1 hi
          rw [bZ0 z] at hc
          exact hc
        | cons c cT =>
          dsimp only [bSl, uOh] at h ⊢
          rw [bDecS z v vT, bDecS z c cT]
          dsimp only [muxFastSlideLoopAux]
          have hp := bPosC h
          have hi := bSl_s z d rem b c bR vT cT hp.2
          have hc := bChb z d b0 c0 b v (bHd z cT) hp.1 hi
          rw [bHd_eq z cT] at hc
          exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uC b (uC (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | [] => uC (bSV (bHd z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTl vs) (bTl cs))
    | [_] => []
    | b :: bz :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uC (bSV v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHd z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] =>
        uC (bSV v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT =>
        uC (bSV z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHd z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
      | [], [] =>
        uC (bSV z (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR [] [])
private theorem bSlZ_eq (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs =
      bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTl vs) (bTl cs)
      dsimp only [mkHbZ] at hrec
      rw [← n0m z] at hrec
      dsimp only [mkHbZ, bSlZ, bSl]
      rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ]
      rw [uC_eq, uC_eq]
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSl, bCV]
          rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV]
          rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSl, bCV]
          rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV]
          rw [bSlZ_eq z d rem b c bR vT cT]
private def uCN4 (x1 x2 x3 x4 : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x1 with
  | 0 => xs
  | v1 + 1 =>
    match Nat.add 1 x2 with
    | 0 => xs
    | v2 + 1 =>
      match Nat.add 1 x3 with
      | 0 => xs
      | v3 + 1 =>
        match Nat.add 1 x4 with
        | 0 => xs
        | v4 + 1 =>
          match xs with
          | [] => [v1, v2, v3, v4]
          | h :: t => v1 :: v2 :: v3 :: v4 :: h :: t
private theorem uCN4e (x1 x2 x3 x4 : ℕ) (xs : List ℕ) :
    uCN4 x1 x2 x3 x4 xs = uC x1 (uC x2 (uC x3 (uC x4 xs))) := by
  unfold uCN4
  rw [n1a x1, n1a x2, n1a x3, n1a x4, uC_eq, uC_eq, uC_eq, uC_eq]
  cases xs <;> rfl
private def bAP4 : List ℕ → Bool
  | a :: b :: c :: d :: xs =>
    cond (Nat.ble a 0) false (cond (Nat.ble b 0) false
      (cond (Nat.ble c 0) false (cond (Nat.ble d 0) false (bAP4 xs))))
  | xs => bPos xs
private theorem bAP4e : ∀ (xs : List ℕ), bAP4 xs = bPos xs
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: xs => by
    dsimp only [bAP4, bPos]
    rw [bAP4e xs]
private def bChkP (out : List ℕ) : Option (List ℕ) :=
  match out with
  | [] => some []
  | x :: xs => cond (bAP4 (x :: xs)) (some (x :: xs)) none
private theorem bChkPe (out : List ℕ) : bChkP out = cond (bPos out) (some out) none := by
  cases out with
  | nil => rfl
  | cons _ _ =>
    dsimp only [bChkP]
    rw [bAP4e]
private inductive HbZ4 : Type
  | tail : List ℕ → HbZ4
  | c4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → HbZ4 → HbZ4
private abbrev hbz4C (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) : List ℕ :=
  b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: t
private def hbz4L : HbZ4 → List ℕ
  | HbZ4.tail l => l
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L r)
private def fH4 {α : Type} (h : HbZ4) (k : HbZ4 → α) : α :=
  match h with
  | HbZ4.tail l => fL l fun lF => k (HbZ4.tail lF)
  | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r => k (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r)
private theorem fH4e {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ =>
    dsimp only [fH4, fL]
    rw [bFL]
  | c4 _ _ _ _ _ _ _ _ _ => rfl
private def toH4 : List ℕ → HbZ4
  | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs =>
    match toH4 bs with
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
    cases h : toH4 bs with
    | tail _ =>
      rw [h] at ih
      dsimp only [hbz4L, hbz4C] at ih ⊢
      rw [ih]
    | c4 _ _ _ _ _ _ _ _ _ =>
      rw [h] at ih
      dsimp only [hbz4L, hbz4C] at ih ⊢
      rw [ih]
private def bSlZ4Step (z d b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (bR : HbZ4)
    (ih : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _ => []
  | 1, p0, q0, vs, cs => bSlZ z d 1 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
  | 2, p0, q0, vs, cs => bSlZ z d 2 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
  | 3, p0, q0, vs, cs => bSlZ z d 3 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
  | rem + 4, p0, q0, v1 :: v2 :: v3 :: v4 :: vR, c1 :: c2 :: c3 :: c4 :: c5 :: cR =>
    uCN4 (bSV v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
      (bSV v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
      (bSV v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
      (bSV v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 c5) z3) d)
      (ih rem (Nat.mul b4 c4) z4 vR (c5 :: cR))
  | rem + 4, p0, q0, vs, cs =>
    bSlZ z d (rem + 4) p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
private def bSlZ4 (z d : ℕ) : HbZ4 → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | HbZ4.tail l => fun rem p0 q0 vs cs => bSlZ z d rem p0 q0 l vs cs
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
    bSlZ4Step z d b1 z1 b2 z2 b3 z3 b4 z4 bR (bSlZ4 z d bR)
private theorem bSlZ4_eq (z d : ℕ) : ∀ (hbz : HbZ4) (rem p0 q0 : ℕ) (vs cs : List ℕ),
    bSlZ4 z d hbz rem p0 q0 vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs
  | HbZ4.tail _, _, _, _, _, _ => by dsimp only [bSlZ4, hbz4L]
  | HbZ4.c4 _ _ _ _ _ _ b4 z4 bR, rem, _, _, vs, cs => by
    dsimp only [bSlZ4, hbz4L, hbz4C]
    match rem with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | rem1 + 4 =>
      match vs with
      | [] => rfl
      | [_] => rfl
      | [_, _] => rfl
      | [_, _, _] => rfl
      | _ :: _ :: _ :: _ :: vR =>
        match cs with
        | [] => rfl
        | [_] => rfl
        | [_, _] => rfl
        | [_, _, _] => rfl
        | [_, _, _, _] => rfl
        | _ :: _ :: _ :: c4 :: c5 :: cR =>
          dsimp only [bSlZ4Step]
          have hr : rem1 + 4 = (((rem1 + 1) + 1) + 1) + 1 := by omega
          rw [hr]
          dsimp only [bSlZ, bHd]
          rw [uCN4e]
          exact congrArg (fun r => uC _ (uC _ (uC _ (uC _ r))))
            (bSlZ4_eq z d bR rem1 (Nat.mul b4 c4) z4 vR (c5 :: cR))
private abbrev nxL (mL cL : ℕ) : ℕ := highdNatMin mL (Nat.add cL 1)
private def bDg (z dg mL cL : ℕ) (h4 : HbZ4) (v c : List ℕ) : Option (List ℕ) :=
  fN (nxL mL cL) fun nL =>
    fN (Nat.mul dg wdScale) fun d =>
      bChkP (bSlZ4 z d h4 nL 0 0 v c)
private theorem bDg_s (z dg mL cL : ℕ) (b v c out : List ℕ) (hc : altListLen c = cL)
    (h : bDg z dg mL cL (toH4 (mkHbZ z b)) v c = some out) :
    bDec z out = muxFastHornerStage dg mL (uOh b) (bDec z v) (bDec z c) ∧
      altListLen out = nxL mL cL := by
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (nxL mL cL) 0 z b v c
  rw [← n0m z] at hsl
  unfold bDg at h
  dsimp only [fN] at h
  rw [bFN, bFN, bChkPe, bSlZ4_eq, hbz4L_toH4, hsl] at h
  revert h
  cases hp : bPos (bSl z (Nat.mul dg wdScale) (nxL mL cL) 0 z b v c) with
  | false =>
    intro h
    dsimp only [cond] at h
    cases h
  | true =>
    intro h
    dsimp only [cond] at h
    injection h with h'
    subst h'
    refine And.intro ?_ (bSl_len z (Nat.mul dg wdScale) (nxL mL cL) 0 z b v c)
    unfold muxFastHornerStage nxL
    dsimp only
    rw [bDecL z c, hc, bFN, bFN, ← bPM0 z]
    exact bSl_s z (Nat.mul dg wdScale) (nxL mL cL) 0 z b v c hp
private def bBdD (z g m c : ℕ) (h4 : HbZ4) (v x : List ℕ)
    (k : ℕ → List ℕ → Option (ℕ × List ℕ)) : Option (ℕ × List ℕ) :=
  fN (nxL m c) fun n =>
    match bDg z g m c h4 v x with
    | none => none
    | some o => k n o
private theorem bBdD_s {z g m c nOut : ℕ} {b v x out : List ℕ}
    {kB : ℕ → List ℕ → Option (ℕ × List ℕ)} {kU : List ℤ → List ℤ}
    (hc : altListLen x = c)
    (h : bBdD z g m c (toH4 (mkHbZ z b)) v x kB = some (nOut, out))
    (hk : ∀ m0, altListLen m0 = nxL m c → kB (nxL m c) m0 = some (nOut, out) →
      bDec z out = kU (bDec z m0) ∧ altListLen out = nOut) :
    bDec z out = HighDForce.withForcedList
      (muxFastHornerStage g m (uOh b) (bDec z v) (bDec z x)) kU ∧
      altListLen out = nOut := by
  unfold bBdD at h
  dsimp only [fN] at h
  rw [bFN] at h
  revert h
  cases hs : bDg z g m c (toH4 (mkHbZ z b)) v x with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some mid =>
    intro h
    dsimp only at h
    have hd := bDg_s z g m c b v x mid hc hs
    rw [bFL, ← hd.1]
    exact hk mid hd.2 h
private def bDg1 (z m c : ℕ) (h4 : HbZ4) (v x : List ℕ) : Option (ℕ × List ℕ) :=
  fN (nxL m c) fun n =>
    match bDg z 1 m c h4 v x with
    | none => none
    | some o => some (n, o)
private theorem bDg1_s {z m c nOut : ℕ} {b v x out : List ℕ}
    (hc : altListLen x = c)
    (h : bDg1 z m c (toH4 (mkHbZ z b)) v x = some (nOut, out)) :
    bDec z out = muxFastHornerStage 1 m (uOh b) (bDec z v) (bDec z x) ∧
      altListLen out = nOut := by
  unfold bDg1 at h
  dsimp only [fN] at h
  rw [bFN] at h
  revert h
  cases hs : bDg z 1 m c (toH4 (mkHbZ z b)) v x with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some mid =>
    intro h
    dsimp only at h
    injection h with hp
    injection hp with hn ho
    subst hn
    subst ho
    exact bDg_s z 1 m c b v x mid hc hs
private def bSp (z m c : ℕ) (h4 : HbZ4) (v : List ℕ) : Option (ℕ × List ℕ) :=
  bBdD z 16 m c h4 v v fun l x => bBdD z 15 m l h4 v x fun l x =>
  bBdD z 14 m l h4 v x fun l x => bBdD z 13 m l h4 v x fun l x =>
  bBdD z 12 m l h4 v x fun l x => bBdD z 11 m l h4 v x fun l x =>
  bBdD z 10 m l h4 v x fun l x => bBdD z 9 m l h4 v x fun l x =>
  bBdD z 8 m l h4 v x fun l x => bBdD z 7 m l h4 v x fun l x =>
  bBdD z 6 m l h4 v x fun l x => bBdD z 5 m l h4 v x fun l x =>
  bBdD z 4 m l h4 v x fun l x => bBdD z 3 m l h4 v x fun l x =>
  bBdD z 2 m l h4 v x fun l x => bDg1 z m l h4 v x
private theorem bSp_s {z mL cL nOut : ℕ} {b v out : List ℕ} (hv : altListLen v = cL)
    (h : bSp z mL cL (toH4 (mkHbZ z b)) v = some (nOut, out)) :
    bDec z out = muxFastHornerT16Step mL (uOh b) (bDec z v) ∧ altListLen out = nOut := by
  unfold bSp at h
  unfold muxFastHornerT16Step
  refine bBdD_s hv h fun _ hc h => bBdD_s hc h fun _ hc h => bBdD_s hc h fun _ hc h => ?_
  refine bBdD_s hc h fun _ hc h => bBdD_s hc h fun _ hc h => bBdD_s hc h fun _ hc h => ?_
  refine bBdD_s hc h fun _ hc h => bBdD_s hc h fun _ hc h => bBdD_s hc h fun _ hc h => ?_
  refine bBdD_s hc h fun _ hc h => bBdD_s hc h fun _ hc h => bBdD_s hc h fun _ hc h => ?_
  refine bBdD_s hc h fun _ hc h => bBdD_s hc h fun _ hc h => bBdD_s hc h fun _ hc h => ?_
  exact bDg1_s hc h
private def bIt (z : ℕ) : ℕ → ℕ → ℕ → HbZ4 → List ℕ → Option (List ℕ)
  | 0, _, _, _, vns => some vns
  | k + 1, mL, cL, h4, vns =>
    match bSp z mL cL h4 vns with
    | none => none
    | some (nL, vNext) => bIt z k mL nL h4 vNext
private theorem bIt_s (z : ℕ) : ∀ (k mL cL : ℕ) (b vns out : List ℕ),
    altListLen vns = cL →
    bIt z k mL cL (toH4 (mkHbZ z b)) vns = some out →
    bDec z out = muxFastIterFullT16 k mL (uOh b) (bDec z vns)
  | 0, _, _, _, vns, out, _, h => by
    dsimp only [bIt] at h
    injection h with h'
    subst h'
    rfl
  | k + 1, mL, cL, b, vns, out, hv, h => by
    dsimp only [bIt] at h
    revert h
    cases hs : bSp z mL cL (toH4 (mkHbZ z b)) vns with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some res =>
      rcases res with ⟨nL, vNext⟩
      intro h
      dsimp only at h
      have hd := bSp_s hv hs
      unfold muxFastIterFullT16
      rw [bFL, ← hd.1]
      exact bIt_s z k mL nL b vNext out hd.2 h
private abbrev zB : ℕ := 2000000000000000
private def fIter (k mL : ℕ) (hb v : List ℤ) : List ℤ :=
  match uHb hb with
  | none => muxFastIterFullT16 k mL hb v
  | some bns =>
    match bEnc zB v with
    | none => muxFastIterFullT16 k mL hb v
    | some vns =>
      fH4 (toH4 (mkHbZ zB bns)) fun h4 =>
        fN (altListLen vns) fun c0 =>
          match bIt zB k mL c0 h4 vns with
          | none => muxFastIterFullT16 k mL hb v
          | some out => bDec zB out
private theorem fIter_eq (k mL : ℕ) (hb v : List ℤ) :
    fIter k mL hb v = muxFastIterFullT16 k mL hb v := by
  unfold fIter
  dsimp only [fN]
  cases hh : uHb hb with
  | none => rfl
  | some bns =>
    dsimp only
    cases hv : bEnc zB v with
    | none => rfl
    | some vns =>
      dsimp only
      rw [fH4e, bFN]
      cases hi : bIt zB k mL (altListLen vns) (toH4 (mkHbZ zB bns)) vns with
      | none => rfl
      | some out =>
        dsimp only
        rw [bIt_s zB k mL (altListLen vns) bns vns out rfl hi, ← uHb_s hb bns hh,
          bEnc_s zB v vns hv]
private theorem mIter_add : ∀ (k1 k2 mL : ℕ) (hb v : List ℤ),
    muxFastIterFullT16 (k1 + k2) mL hb v =
      muxFastIterFullT16 k2 mL hb (muxFastIterFullT16 k1 mL hb v)
  | 0, k2, mL, hb, v => congrArg (fun n => muxFastIterFullT16 n mL hb v) (Nat.zero_add k2)
  | k1 + 1, k2, mL, hb, v => by
    have hk : k1 + 1 + k2 = (k1 + k2) + 1 := by omega
    rw [hk]
    dsimp only [muxFastIterFullT16]
    rw [bFL, bFL]
    exact mIter_add k1 k2 mL hb (muxFastHornerT16Step mL hb v)
private abbrev WalkCert : Type := Option (ℕ × ℕ × List ℕ × List ℕ × List ℕ)
private def WalkOk : WalkCert → Prop
  | none => True
  | some (kE, mE, bns, vns, out) => muxFastIterFullT16 kE mE (uOh bns) (bDec zB vns) = bDec zB out
private def WalksOk : List WalkCert → Prop
  | [] => True
  | wc :: wcs => WalkOk wc ∧ WalksOk wcs
private theorem wNil : WalksOk [] := trivial
private theorem wSkip {wcs : List WalkCert} (hw : WalksOk wcs) :
    WalksOk (none :: wcs) := And.intro trivial hw
private theorem wCons {wc : WalkCert} {wcs : List WalkCert} (h1 : WalkOk wc) (h2 : WalksOk wcs) :
    WalksOk (wc :: wcs) := And.intro h1 h2
private def bSlideChk (k mL : ℕ) (bns vns out : List ℕ) : Bool :=
  fH4 (toH4 (mkHbZ zB bns)) fun h4 =>
    fN (altListLen vns) fun c0 =>
      match bIt zB k mL c0 h4 vns with
      | none => false
      | some w => bNLE w out
private theorem bSlideChk_sound {k mL : ℕ} {bns vns out : List ℕ} {s : List Bool}
    (h : atF (bSlideChk k mL bns vns out :: s) = true) : WalkOk (some (k, mL, bns, vns, out)) := by
  unfold bSlideChk at h
  dsimp only [fN] at h
  rw [fH4e, bFN] at h
  unfold WalkOk
  revert h
  cases hi : bIt zB k mL (altListLen vns) (toH4 (mkHbZ zB bns)) vns with
  | none =>
    intro h
    dsimp only [atF] at h
    cases h
  | some w =>
    intro h
    dsimp only at h
    rw [← bhd_eq h]
    exact (bIt_s zB k mL (altListLen vns) bns vns w rfl hi).symm
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
      (Bool.and (bILE hb (uOh bns)) (bILE v (bDec zB vns)))))
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
        cases hh : bILE hb (uOh bns) with
        | false => rfl
        | true =>
          cases hv : bILE v (bDec zB vns) with
          | false => rfl
          | true =>
            dsimp only [Bool.and, cond]
            rw [bNatEq_t hk, bNatEq_t hm, bILE_t hh, bILE_t hv]
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
      (Bool.or (primNatBlt 16384 nS) (primNatBlt (Nat.add d 1)
        (rkmBoolListLen mk)))))))))))) (0, 0, [])
      (fN (Nat.div (Nat.mul t9 1000000) nS) fun hPt =>
        cond (primNatBlt hPt 1) (0, 0, [])
          (fN (altMaxBHiFrom mE r 0 d) fun bHi =>
            let bCap := Nat.mul 2 bHi
            fN (highdMulCeil15 (Nat.add 2 hPt) bCap) fun hgHi =>
              cond (Bool.or (primNatBlt 1500000000000000 hgHi)
                  (Bool.not (altCheckHbTight mE r 0 d))) (0, 0, [])
                (let hgP := altPow17Ceil15 hgHi
                let trP := Nat.div (Nat.add 299999999999999 (Nat.mul nS hgP)) 300000000000000
                let bCeil := Nat.div (Nat.add 999999999999999 bCap) wdScale
                let sPad := Nat.add (Nat.add trP 256) (Nat.mul nS (Nat.add 256 (Nat.mul 10 bCeil)))
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
          have hw0 : ∀ k mL hb u, wIter k mL hb u (wHead wcs) = muxFastIterFullT16 k mL hb u :=
            fun k mL hb u => wIter_eq k mL hb u (wHead wcs) (wHead_ok hw)
          have hi0 := ih tR nR mR (wTail wcs) (wTail_ok hw)
          unfold bEvalSegsW rkmEvalSegsLoop
          dsimp only [fN, fL]
          simp only [bFN, bFL, hw0, hi0]
          generalize Nat.add aP _ = np
          cases t9 <;> cases nS <;> cases np <;> rfl
private def bEvalLo12W (m lM r : ℕ) (ls ts ns : List ℕ)
    (mks : List (List Bool)) (wcs : List WalkCert) : List ℕ :=
  let nS := altListLen ls
  cond (Bool.or (Nat.ble nS 0) (Bool.or (primNatBlt 8 nS)
      (Bool.or (primNatBlt r 2) (primNatBlt 1024 r)))) []
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
    {wcs : List WalkCert} {y : List ℕ}
    {s : List Bool} (h : atF (bNLE (bEvalLo12W m lm r ls ts ns mks wcs) y :: s) = true)
    (hw : WalksOk wcs) : rkmEvalT16Lo12 m lm r ls ts ns mks = y :=
  (bEvalLo12W_eq m lm r ls ts ns mks wcs hw).symm.trans (bhd_eq h)
private theorem bh0_eq {m lm r : ℕ} {ls ts ns : List ℕ} {mks : List (List Bool)}
    {y : List ℕ} {s : List Bool}
    (h : atF (bNLE (bEvalLo12W m lm r ls ts ns mks []) y :: s) = true) :
    rkmEvalT16Lo12 m lm r ls ts ns mks = y := bhW_eq h wNil
private def wc_rkmTraj_m4_r128_s4_hb_p0 : List ℕ := [154615794526208,216951474251242,
  263617999088084,301983973684000,334927319863374,363935669843740,389899553215929,413403596604729,
  434856922104960,454559614685859,472739875769702,489576284020728,505211877489517,519763460278159,
  533327978810249,545987024420672,557810095692808,568857015162705,579179754497256,588823836533996,
  597829428606448,606232206655298,614064046464281,621353582660045,628126665262720,634406735938086,
  640215140642490,645571391390309,650493386960683,654997600191422,659099237874841,662812378027417,
  666150088350040,669124528954940,671747041856031,674028229262688,675978022354220,677605741922150,
  678920152033790,679929507681369,680641597226730,681063780325247,681203021908498,681065922719063,
  680658746819115,679987446434581,679057684446385,677874854797931,676444101052160,674770333301107,
  672858243604951,670712320115394,668336860019219,665735981421476,662913634273675,659873610440098,
  656619552984775,653154964752404,649483216308450,645607553296618,641531103265694,637256882012335,
  632787799481590,628126665262720]
private def wc_rkmTraj_m4_r128_s4_hb_p1 : List ℕ := [623276193714128,618239008747934,
  613017648301735,607614568522523,602032147685361,596272689867357,590338428395597,584231529086022,
  577954093288760,571508160754037,564895712331609,558118672515538,551178911845174,544078249172268,
  536818453803381,529401247525978,521828306525952,514101263203709,506221707895402,498191190505373,
  490011222055450,481683276156267,473208790405455,464589167717144,455825777586933,446919957296181,
  437873013059182,428686221116573,419360828778055,409898055417331,400299093421956,390565109100599,
  380697243550086,370696613484405,360564312027739,350301409473440,339908954010756,329387972420998,
  318739470744716,307964434921401,297063831403083,286038607743153,274889693161636,263617999088084,
  252224419683178,240709832340074,229075098166455,217321062448223,205448555095676,193458391073005,
  181351370811869,169128280609777,156789893013988,144336967191545,131770249286099,119090472762076,
  106298358736768,93394616300847,80379942827831,67255024272942,54020535461834,40677140369595,
  27225492390444,13666234598503]
private def wc_rkmTraj_m4_r128_s4_hb : List ℕ := pCat wc_rkmTraj_m4_r128_s4_hb_p0
  wc_rkmTraj_m4_r128_s4_hb_p1
private def wc_rkmTraj_m4_r128_s4_v0_p0 : List ℕ := [1999369906361909,2000914923943829,
  1999384693770658,2000125235419720,2000740972459847,2000738779974733,2000133585785285,
  2000575491855751,2000832451298768,2000458091871228,2000253314751478,2000795267509638,
  2000818055606557,1999668300128986,1999644877097969,1999138507068898,1999049861316338,
  1999386864105543,1999979991565685,1999399817857598,2001061920548247,2001272779392996,
  1998758005635477,1998917989309361,1998995286385878,1998764954492352,1998296510391781,
  1998552108922481,2002083695936264,2013303110903387,2037696740892291,2079757340600163,
  2140236784657366,2214076298716730,2290415751703276,2355193669845942,2395474244102477,
  2403638048256719,2379599820572061,2330237369632339,2266570324696839,2200127590068874,
  2139991585363223,2091367946622960,2055694787985496,2031728443697862,2016898401586570,
  2008414423267156,2003916292886418,2001702767803038,2000691004607648,2000261403567056,
  2000092030028609,2000030089126035,2000009111185163,2000002546455330,2000000654036370,
  2000000153513484,2000000032689183,2000000006253663,2000000001060329,2000000000156190,
  2000000000019359,2000000000001900]
private def wc_rkmTraj_m4_r128_s4_v0_p1 : List ℕ := [2000000000000126]
private def wc_rkmTraj_m4_r128_s4_v0 : List ℕ := pCat wc_rkmTraj_m4_r128_s4_v0_p0
  wc_rkmTraj_m4_r128_s4_v0_p1
private def wc_rkmTraj_m4_r128_s4_v1_p0 : List ℕ := [1999934414024114,1999510985717908,
  1999900863281744,1999470587719387,1999340779000491,1999607807974454,1999148908027339,
  1999778137122108,1999845214495793,1999711762260349,2000680721929456,2000819246125541,
  1999592150916159,1999269423491377,2000076099489379,2000214200342846,1999700432755776,
  1999843330438174,2000427754816865,2000342146335728,1999790344718579,1999851410839282,
  2000569329075044,2000936839149530,2000494671112968,1999912989941256,1999939367087770,
  2000448834570893,2000776771030845,2000624382030068,2000329740392159,2000348030605127,
  2000701698336079,2000990404224442,2000826355837850,2000189279051275,1999410520638749,
  1998896649339577,1998871646847298,1999296797649225,1999933441061598,2000446560056654,
  2000519203834908,2000018262261611,1999193301933467,1998734688847976,1999456410031734,
  2001577542458740,2003996552638081,2004253204034501,1999682908040917,1989533359607354,
  1976953510848743,1969435866476733,1976886336347271,2007777393107878,2065046835859720,
  2143754543532111,2231746077179029,2313131704887117,2373094629606163,2402065694211548,
  2397788514454412,2364864211204469]
private def wc_rkmTraj_m4_r128_s4_v1_p1 : List ℕ := [2312402813298776,2250959315994071,
  2189881022397526,2135730379843036,2091887867623364,2059033576881975,2036051583987651,
  2020957532331231,2011610667594847,2006136314835253,2003096405737549,2001492857615927,
  2000688099945835,2000303373374960,2000127990902422,2000051689924424,2000019988351371,
  2000007402588605,2000002625978956,2000000892361880,2000000290503275,2000000090597726,
  2000000027065393,2000000007744538,2000000002122232,2000000000556821,2000000000139843,
  2000000000033606,2000000000007722,2000000000001693,2000000000000352,2000000000000067,
  2000000000000010,2000000000000001,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m4_r128_s4_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m4_r128_s4_v1 : List ℕ := pCat wc_rkmTraj_m4_r128_s4_v1_p0 (pCat
  wc_rkmTraj_m4_r128_s4_v1_p1 wc_rkmTraj_m4_r128_s4_v1_p2)
private def wc_rkmTraj_m4_r128_s4_v2_p0 : List ℕ := [1999909428803408,1999886079378050,
  2000015589662259,2000257737287593,2000399580395087,2000259029160647,1999929817493159,
  1999735893542179,1999872347363082,2000143564680391,2000169221735554,1999861839352415,
  1999578112167724,1999697372826520,2000116257906232,2000319179569804,1999994941070547,
  1999453427294236,1999293539361435,1999690024474826,2000163128634646,2000126345517337,
  1999564226070824,1999039536187009,1999044405458828,1999479780622145,1999849072549293,
  1999874703077806,1999776628068879,1999917501144303,2000297649574022,2000529161199486,
  2000306857572101,1999798306785358,1999489218113377,1999664604221887,2000110977084861,
  2000355181045324,2000160458826553,1999749276885440,1999548080758949,1999753081230190,
  2000163741314207,2000416912694252,2000349043205998,2000124038375350,2000033190904098,
  2000196216006439,2000458587043257,2000562355477255,2000402721608934,2000121772635427,
  1999970244981734,2000095103049276,2000457084549908,2000911495733062,2001299218561475,
  2001425664973015,2001032920179525,1999986367873308,1998647215170278,1997982414671225,
  1998944668625146,2001341691852346]
private def wc_rkmTraj_m4_r128_s4_v2_p1 : List ℕ := [2003276843726004,2002228647942066,
  1997493013937698,1992007575444174,1991297237663456,1999277770909616,2013644996696174,
  2024917586587071,2021223837220189,1996694827434913,1958051590496120,1924401493314149,
  1919357517969553,1959520838426258,2045702465347887,2161564071263777,2280019968164103,
  2373687029900049,2424199972818456,2426663409751347,2388480594792312,2324386352715935,
  2250549906621219,2180085708672761,2120983551245000,2076219673258510,2045143347028722,
  2025185275473358,2013254774221829,2006588138727631,2003095162968484,2001375288148046,
  2000578175956530,2000230020928509,2000086601617126,2000030851541274,2000010396678973,
  2000003312756359,2000000997487529,2000000283615203,2000000076079785,2000000019234007,
  2000000004577182,2000000001023853,2000000000214918,2000000000042252,2000000000007759,
  2000000000001325,2000000000000206,2000000000000027,2000000000000002,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m4_r128_s4_v2_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m4_r128_s4_v2 : List ℕ := pCat wc_rkmTraj_m4_r128_s4_v2_p0 (pCat
  wc_rkmTraj_m4_r128_s4_v2_p1 wc_rkmTraj_m4_r128_s4_v2_p2)
private def wc_rkmTraj_m4_r128_s5_hb_p0 : List ℕ := [138684162606469,194947051785059,
  237312006224603,272350918901875,302625638962722,329457996509276,353637845144557,375682791320277,
  395954409198702,414717432838844,432172818067838,448477536857222,463757089907824,478113769904522,
  491632318746441,504383919453919,516429086369330,527819804613800,538601144688188,548812501836236,
  558488561791893,567660063483571,576354408684441,584596154650967,592407416154751,599808196534695,
  606816662551980,613449374316714,619721478972285,625646874901224,631238351769475,636507710625239,
  641465867423003,646122942687837,650488339522529,654570811756197,658378523712324,661919102817702,
  665199686067384,668226961193533,671007203249891,673546307211982,675849817101238,677922952065155,
  679770629782306,681397487508086,682807901032706,684006001785486,684995692287785,685780660129984,
  686364390624914,686750178270425,686941137136822,686940210280252,686750178270425,686373666909973,
  685813154213070,685070976702440,684149335076317,683050299290275,681775813092836,680327698048386,
  678707657076042,676917277528621]
private def wc_rkmTraj_m4_r128_s5_hb_p1 : List ℕ := [674958033831737,672831289699166,
  670538299936950,668080211845212,665458066223202,662672797979771,659725236348017,656616104699471,
  653346019949598,649915491542652,646324920000000,642574595011720,638664693046671,634595274451073,
  630366280000000,625977526859770,621428703912042,616719366382213,611848929705337,606816662551980,
  601621678923899,596262929214862,590739190114905,585049053216266,579190912155614,573162948099129,
  566963113343545,560589112766270,554038382809485,547308067624891,540394991934939,533295630079809,
  526006070612997,518521975676765,510838534224966,502950407955610,494851668556753,486535724540384,
  477995235517547,469222011223449,460206891891252,450939605638293,441408597284280,431600821346341,
  421501489673715,411093761033062,400358355538058,389273070525706,377812165361688,365945569174332,
  353637845144557,340846813434756,327521684628073,313600473070906,299006319042829,283642099178187,
  267382238899960,250059718385914,231444299647518,211203421118781,188825174939529,163445614221335,
  133376428265546,94250598352785]
private def wc_rkmTraj_m4_r128_s5_hb : List ℕ := pCat wc_rkmTraj_m4_r128_s5_hb_p0
  wc_rkmTraj_m4_r128_s5_hb_p1
private def wc_rkmTraj_m4_r128_s5_v0_p0 : List ℕ := [1999909428803408,1999886079378050,
  1999984410337741,2000257737287593,1999600419604913,2000259029160647,2000070182506841,
  2000264106457821,2000127652636918,2000143564680391,2000169221735554,2000138160647585,
  2000421887832276,1999697372826520,1999883742093768,1999680820430196,1999994941070547,
  2000546572705764,2000706460638565,2000309975525174,1999836871365354,1999873654482663,
  1999564226070824,2000960463812991,2000955594541172,2000520219377855,1999849072549293,
  1999874703077806,1999776628068879,1999917501144303,1999702350425978,1999470838800514,
  1999693142427899,2000201693214642,2000510781886623,2000335395778113,2000110977084861,
  2000355181045324,1999839541173447,1999749276885440,1999548080758949,1999753081230190,
  2000163741314207,2000416912694252,2000349043205998,1999875961624650,1999966809095902,
  1999803783993561,2000458587043257,2000562355477255,2000402721608934,2000121772635427,
  1999970244981734,2000095103049276,2000457084549908,2000911495733062,2001299218561475,
  2001425664973015,2001032920179525,2000013632126692,2001352784829722,2002017585328775,
  2001055331374854,1998658308147654]
private def wc_rkmTraj_m4_r128_s5_v0_p1 : List ℕ := [1996723156273996,1997771352057934,
  2002506986062302,2007992424555826,2008702762336544,1999277770909616,2013644996696174,
  2024917586587071,2021223837220189,2003305172565087,2041948409503880,2075598506685851,
  2080642482030447,2040479161573742,2045702465347887,2161564071263777,2280019968164103,
  2373687029900049,2424199972818456,2426663409751347,2388480594792312,2324386352715935,
  2250549906621219,2180085708672761,2120983551245000,2076219673258510,2045143347028722,
  2025185275473358,2013254774221829,2006588138727631,2003095162968484,2001375288148046,
  2000578175956530,2000230020928509,2000086601617126,2000030851541274,2000010396678973,
  2000003312756359,2000000997487529,2000000283615203,1999999923920215,2000000019234007,
  2000000004577182,1999999998976147,1999999999785082,2000000000042252,2000000000007759,
  2000000000001325,2000000000000206,2000000000000027,2000000000000002,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m4_r128_s5_v0_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m4_r128_s5_v0 : List ℕ := pCat wc_rkmTraj_m4_r128_s5_v0_p0 (pCat
  wc_rkmTraj_m4_r128_s5_v0_p1 wc_rkmTraj_m4_r128_s5_v0_p2)
private def wc_rkmTraj_m4_r128_s5_v1_p0 : List ℕ := [1999614356492067,1999830025575039,
  2000358113702514,1999951522136980,2000108241327087,2000016339001654,1999576866483966,
  2000039673357494,1999802447573222,2000265579650279,1999791220308778,2000032458076208,
  2000195248840121,1999934608980477,1999745720676005,2000002157434572,2000056794963034,
  1999918768113506,1999958904907739,2000408275330616,2000037539030513,2000006751207354,
  1999972522990761,2000074388375600,2000276804959661,2000016361567539,2000449649291080,
  2000432757981273,2000352777191800,1999689485695709,1999517142686101,1999489447897875,
  1999737313881225,2000522492593568,2000853582180198,2000414538590325,2000024373385697,
  1999545709207828,1999937398763655,2000008641615962,2000514551545668,2000109484037502,
  2000409074752647,2000423143622893,2000645411715728,2000071292185724,2001110371967229,
  1998468913605944,2001939199251498,1997111595630536,2002643941441564,1996305748331966,
  2002999664750912,1996888070532768,2002946393597948,1998736295479138,2001789838940337,
  1999692924624987,1996960747265766,2005944245197389,1992637365809717,2004277039014803,
  2001434470406564,1995668863393433]
private def wc_rkmTraj_m4_r128_s5_v1_p1 : List ℕ := [2002849944153957,1999788887214617,
  1999663722320999,1998184945000808,2000947901786072,2008014824541927,1993757952363363,
  1988878680827611,2013666533525337,2011466314645760,1981580389419933,1990585565155256,
  2021908690222442,2009793584109276,1979095351351902,1992316447899883,2025353722013308,
  2015934455850833,1977116241331456,1971790211937854,2009288586365817,2035254555746420,
  2013822723363238,1973826706443951,1967169152814506,2006381282344282,2054530033428647,
  2066524273013785,2031812262675794,1981572988888422,1962958468619373,2006452790120600,
  2109133575968630,2239768551947831,2357312459433834,2429823073287603,2444736259664263,
  2408538613774425,2339374820134509,2257953940014483,2180829021856941,2117564532592697,
  2071170505254377,2040233535637094,2021282829922817,2010549511389905,2004904320501902,
  2002139215470729,2000875506444699,2000336046068187,2000120853990725,2000040661788321,
  2000012771406130,2000003734032737,2000001012598429,2000000253564266,2000000058315797,
  2000000012236895,2000000002323752,2000000000395168,2000000000059331,2000000000007703,
  2000000000000834,2000000000000068]
private def wc_rkmTraj_m4_r128_s5_v1_p2 : List ℕ := [2000000000000003]
private def wc_rkmTraj_m4_r128_s5_v1 : List ℕ := pCat wc_rkmTraj_m4_r128_s5_v1_p0 (pCat
  wc_rkmTraj_m4_r128_s5_v1_p1 wc_rkmTraj_m4_r128_s5_v1_p2)
private def wc_rkmTraj_m4_r128_s5_v2_p0 : List ℕ := [1999944458175527,2000467191307834,
  1999851852439763,1999690170072166,1999769333175890,1999842144339183,1999683907966214,
  1999964743824228,1999933879590674,1999896547050537,2000021849181076,1999805321744007,
  2000405220968701,2000249503137075,2000009764462819,1999844855032406,1999916772387714,
  2000045692144795,2000019645096045,1999711644832154,1999976527644810,1999694140349660,
  2000295240252946,1999841696114007,2000145713945027,1999529344569883,2000849544540479,
  1999076721525437,2001495025887221,1997580689462549,2002843815768389,1996569777366674,
  2003388767975139,1996867524293045,2002552672999865,1998381639403335,2000766356621044,
  2000748001656165,1998121985107541,2003300980299448,1995555635372509,2004049775024658,
  1996851523666479,2001700757451960,2002613881921147,1996469457177083,2004477360907478,
  1996975729749390,1998262119529562,2003737542357578,1996383368520933,2001149262216411,
  2002380993120669,1997597785965484,2001147612058255,2000437275058893,1999704347054108,
  2000299349185815,1998216250771405,2002195583578885,2000932830796604,1996047769053971,
  2003970825485093,2003249674404505]
private def wc_rkmTraj_m4_r128_s5_v2_p1 : List ℕ := [1992928479445574,2002948152431488,
  2008649307534146,1991204770288433,1994478248743832,2012852430530600,1998722276854264,
  1984442171232374,2007649949225868,2015609116519338,1987437574657455,1986460393286916,
  2016213275977323,2011155433253082,1981888499002820,1991225942537564,2019047067325845,
  2006902803938238,1980027115469455,1993465886806077,2020866139982632,2008164067840217,
  1978726639810732,1988215615527642,2021156569019695,2019008066145797,1983067078325632,
  1972372454523906,2006329471601048,2034003969358932,2013172213784174,1972994236671731,
  1970868152191747,2011813063853609,2041995239254714,2019207368030843,1966430510321262,
  1945412669586955,1986339409443516,2053793677006315,2081774120079733,2037878104635763,
  1954588547337822,1903774551295930,1941905723462811,2071681297223060,2244397961745754,
  2393351323596365,2470490179944709,2464294604886782,2394783758988945,2295808752829234,
  2197849244938478,2119014192025092,2064652670664029,2031767731068593,2014111150425834,
  2005651707232670,2002030939554213,2000649680841841,2000182795308825,2000044400097435,
  2000009027869506,2000001450575336]
private def wc_rkmTraj_m4_r128_s5_v2_p2 : List ℕ := [2000000159678243]
private def wc_rkmTraj_m4_r128_s5_v2 : List ℕ := pCat wc_rkmTraj_m4_r128_s5_v2_p0 (pCat
  wc_rkmTraj_m4_r128_s5_v2_p1 wc_rkmTraj_m4_r128_s5_v2_p2)
private def wc_rkmTraj_m4_r128_s6_hb_p0 : List ℕ := [138530081709123,194730461684866,
  237048347806922,272048331546630,302289415783846,329091962040840,353244946377377,375265400173976,
  395514495876727,414256673419772,431692665364277,447979269282757,463241846442235,477582575878355,
  491086105340287,503823538762600,515855323255013,527233386182138,538002747970599,548202760095229,
  557868069753428,567029381722039,575714067330313,583946656551106,591749239586063,599141797549975,
  606142477020385,612767819708785,619032955929782,624951768624524,630537033249379,635800537741344,
  640753185927063,645405087087498,649765633878401,653843570403208,657647051914675,661183697365371,
  664460635821001,667484547583524,670261700734972,672797983701431,675098934344814,677169766014040,
  679015390924040,680640441178126,682049287704919,683246057343636,684234648279858,685018744006977,
  685601825965573,685987184993241,686177931700492,686177005873678,685987184993241,685611091944492,
  685051201988483,684309849052012,683389231388295,682291416653142,681018346435533,679571840276059,
  677953599201858,676165208802166]
private def wc_rkmTraj_m4_r128_s6_hb_p1 : List ℕ := [674208141864483,672083760587470,
  669793318383054,667337961276684,664718728911263,661936555156937,658992268325511,655886590984836,
  652620139364970,649193422344165,645606839998800,641860681697103,637955123711871,633890226322278,
  629665930369200,625282053222085,620738284108253,616034178747251,611169153223599,606142477020385,
  600953265123726,595600469093526,590082866978940,584399051936978,578547419389011,572526152521977,
  566333205907653,559966286973373,553422835009483,546699997340588,539794602216936,532703127895788,
  525421667276333,517945887320283,510270982326659,502391619924432,494301878388132,485995173553023,
  477464173185471,468700696120231,459695592767150,450438602655834,440918183444029,431121304142656,
  421033193030889,410637027586336,399913549343018,388840580305539,377392408437947,365538996277913,
  353244946377377,340468125761380,327157801441130,313252056630334,298674117001265,283326967094283,
  267085171848252,249781897003321,231187160370003,210968769864903,188615386367789,163264022852622,
  133228244367935,94145884040085]
private def wc_rkmTraj_m4_r128_s6_hb : List ℕ := pCat wc_rkmTraj_m4_r128_s6_hb_p0
  wc_rkmTraj_m4_r128_s6_hb_p1
private def wc_rkmTraj_m4_r128_s6_v0_p0 : List ℕ := [1999944458175527,1999532808692166,
  1999851852439763,1999690170072166,1999769333175890,2000157855660817,2000316092033786,
  2000035256175772,2000066120409326,2000103452949463,1999978150818924,1999805321744007,
  1999594779031299,1999750496862925,2000009764462819,1999844855032406,2000083227612286,
  1999954307855205,2000019645096045,2000288355167846,2000023472355190,2000305859650340,
  2000295240252946,2000158303885993,2000145713945027,2000470655430117,2000849544540479,
  1999076721525437,1998504974112779,1997580689462549,1997156184231611,1996569777366674,
  1996611232024861,1996867524293045,1997447327000135,1998381639403335,1999233643378956,
  1999251998343835,1998121985107541,2003300980299448,2004444364627491,2004049775024658,
  1996851523666479,1998299242548040,1997386118078853,1996469457177083,2004477360907478,
  2003024270250610,2001737880470438,2003737542357578,1996383368520933,1998850737783589,
  2002380993120669,1997597785965484,1998852387941745,2000437275058893,1999704347054108,
  1999700650814185,1998216250771405,2002195583578885,1999067169203396,1996047769053971,
  2003970825485093,2003249674404505]
private def wc_rkmTraj_m4_r128_s6_v0_p1 : List ℕ := [2007071520554426,2002948152431488,
  2008649307534146,2008795229711567,2005521751256168,2012852430530600,2001277723145736,
  2015557828767626,2007649949225868,2015609116519338,2012562425342545,2013539606713084,
  2016213275977323,2011155433253082,2018111500997180,2008774057462436,2019047067325845,
  2006902803938238,2019972884530545,2006534113193923,2020866139982632,2008164067840217,
  2021273360189268,2011784384472358,2021156569019695,2019008066145797,2016932921674368,
  2027627545476094,2006329471601048,2034003969358932,2013172213784174,2027005763328269,
  2029131847808253,2011813063853609,2041995239254714,2019207368030843,2033569489678738,
  2054587330413045,2013660590556484,2053793677006315,2081774120079733,2037878104635763,
  2045411452662178,2096225448704070,2058094276537189,2071681297223060,2244397961745754,
  2393351323596365,2470490179944709,2464294604886782,2394783758988945,2295808752829234,
  2197849244938478,2119014192025092,2064652670664029,2031767731068593,2014111150425834,
  2005651707232670,2002030939554213,2000649680841841,1999817204691175,1999955599902565,
  2000009027869506,2000001450575336]
private def wc_rkmTraj_m4_r128_s6_v0_p2 : List ℕ := [2000000159678243]
private def wc_rkmTraj_m4_r128_s6_v0 : List ℕ := pCat wc_rkmTraj_m4_r128_s6_v0_p0 (pCat
  wc_rkmTraj_m4_r128_s6_v0_p1 wc_rkmTraj_m4_r128_s6_v0_p2)
private def wc_rkmTraj_m4_r128_s6_v1_p0 : List ℕ := [2000136326666121,2000138681578549,
  2000162501084664,2000073924864271,1999931606138213,1999721167266323,1999938391633756,
  2000024365862939,1999780836947741,1999950661847089,1999775745667829,1999395239272763,
  1999980789531965,1999627702928223,2000213827861114,1999851757580992,2000016003973869,
  2000173056852638,1999838931042224,2000303917222400,2000069762223036,2000754512533883,
  1998944137938361,2001071849175573,1998900356453858,2000754532905055,1999131148720178,
  1999498146705951,2000964657512007,1999006132677044,2000523616778837,1999428054304345,
  1999085362562364,2002418989234478,1998016983840176,2000160074802412,2002974598370098,
  1996508854275625,1999671444653282,2003552951514814,1998612939949857,2000810866327553,
  2000957007640332,1998676429262962,2003421357592125,1997945659464175,1998789677837886,
  1994567864798046,1998169939108267,2000405195725482,1993662327880202,2002025175825871,
  1991811625434437,1999883795919377,1990435944745789,2005259062136745,2004357288136595,
  2000346519998224,2004961563689642,1996312750601448,2001300438500372,1992292452723919,
  2005678087257789,1995895529004345]
private def wc_rkmTraj_m4_r128_s6_v1_p1 : List ℕ := [2007639577155677,1993922834345854,
  2007943241765080,1996393647686196,2006262660155554,1993592537699831,2002011811590907,
  1998615582705646,2000524018924211,2002368570643532,1994039850209036,2006995499141816,
  1989326119633415,2008634729117084,1989424292296655,2005530298179972,2002434148737301,
  1998691582719811,2016562099262652,1993698728434384,2016383472594768,2002842767792081,
  2004068504860318,2019851347685152,1996730142832791,2025219214358366,2007173288411190,
  2010860852307813,2028180516466565,2001051666706529,2018164858271923,2026211244195866,
  1995992646634335,2025221262362990,2023890238744753,1983714744293330,2044354490367232,
  2020850165917711,1988726118085724,2044480047564883,2026376137016861,1995683873244386,
  2037710521814614,2036586102330637,2000861949991955,2027791468963698,2056909527138084,
  2019168844772746,1996849416164564,2056411834913350,2114643781167360,2074125102608416,
  1978119309660185,1961890194143199,2093683497424171,2310166798713114,2483082323577031,
  2528711333053447,2450858439990291,2311549935174380,2177264173740692,2082931213384255,
  2031075539569938,2008744745029223]
private def wc_rkmTraj_m4_r128_s6_v1_p2 : List ℕ := [2001585422814293]
private def wc_rkmTraj_m4_r128_s6_v1 : List ℕ := pCat wc_rkmTraj_m4_r128_s6_v1_p0 (pCat
  wc_rkmTraj_m4_r128_s6_v1_p1 wc_rkmTraj_m4_r128_s6_v1_p2)
private def wc_rkmTraj_m4_r128_s6_v2_p0 : List ℕ := [2000048058500663,2000006885520440,
  2000034871541199,1999891286048989,2000420875385334,1999772291993705,1999869451357129,
  2000542460072995,1999651134844946,2000877241820945,1999182105012414,2001088300781413,
  1999092580156821,2000358351641470,2000283912474922,1998853890745497,2000759780039206,
  1999971576490845,1999255598323618,2001211717399309,1998805966851042,1999878938014187,
  2001092911689251,1997881694775521,2000274794428367,2001047367578564,1997970280805152,
  2000615642084283,2002247328848084,1995166159462990,2003120626531861,2001159035740623,
  1996542386869254,2003087017077875,1997187431304861,2005186295270800,1993791028851593,
  2005210775588577,1997747660051066,1999842570171647,2001478554116512,1996002955762256,
  2005387480552667,1994333518347262,2006344219436534,1992977775323979,2003734168126236,
  1996154972594306,2008065030291631,1991279657072589,2005008047602605,1996997689558699,
  2003540429323223,1996708305825716,2001741688815598,2001047944143136,1995425384857757,
  2005247891403714,1996129420045518,2011094381314812,1990994235690569,2006134797961596,
  1992045680745031,2001649746395789]
private def wc_rkmTraj_m4_r128_s6_v2_p1 : List ℕ := [2000679337873206,1994499656068822,
  2008139985441258,1983777373310795,2001775768428338,1989229903494514,1999442513272886,
  2007590553550711,1989879664805398,2014192997409758,1990175085278527,2006172776218224,
  1998634325729226,1991444465542603,2010074892900229,1991530548519095,2006482651433905,
  2004017321393441,1991787473651460,2011920995664513,1994020285254631,1993689456652796,
  2017996829976563,1978562894728426,2015161975116373,2002590824332814,1977898391907508,
  2022596004296738,1983022718328426,1993856886869339,2024911564544908,1979509430509793,
  2009961352245937,2022952261094629,1980927466413522,2015826947500321,2022623969996784,
  1989709094862218,2021122539623923,2024906515014034,1996855901315716,2025054724414108,
  2028980818230364,1995113437771695,2018167041848538,2037261718925026,1997270219999726,
  2003918244066534,2052188269871120,2024431551387918,1978838433019615,2032434031104729,
  2084609565944768,2011834708842919,1946113708025140,2041661046223657,2161266326381979,
  2085216448188178,1898953286519120,1907848247246866,2204321950418807,2534274831217647,
  2614233291871909,2428999277504734]
private def wc_rkmTraj_m4_r128_s6_v2_p2 : List ℕ := [2175132141888193]
private def wc_rkmTraj_m4_r128_s6_v2 : List ℕ := pCat wc_rkmTraj_m4_r128_s6_v2_p0 (pCat
  wc_rkmTraj_m4_r128_s6_v2_p1 wc_rkmTraj_m4_r128_s6_v2_p2)
private def wc_rkmTraj_m256_r64_s0_hb : List ℕ := [178981525333248,250641856140644,
  303928597304882,347418874535558,384467056799186,416808653632836,445483123882824,471172928838293,
  494355469983759,515380588017733,534513909660598,551962833342067,567892975092332,582439040817138,
  595712276237435,607805727085469,618798048691489,628756325584216,637738197784862,645793490414878,
  652965480213073,659291891744115,664805688990286,669535709634304,673507176611504,676742112530022,
  679259676111706,681076435100518,682206586590768,682662133086236,682453020564769,681587243216076,
  680070918216085,677908332804511,675101964969099,671652478149221,667558689498553,662817510338195,
  657423856430814,651370524546534,644648030389137,637244401196857,629144914075565,620331768151931,
  610783674645511,600475343502750,589376837638703,577452755060456,564661183581059,550952349878312,
  536266850037745,520533295212472,503665120993266,485556169596584,466074416753237,445052794400317,
  422275276011949,397454840298696,370196630432926,339931942298365,305788525049717,266300519148196,
  218617222736387,155405675989902]
private def wc_rkmTraj_m256_r64_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTraj_m256_r64_s0_v1_p0 : List ℕ := [2000000000021983,2000000000203357,
  2000000001313677,2000000006842343,2000000030473690,2000000119841937,2000000424681657,
  2000001375140449,2000004110318120,2000011428901409,2000029741669056,2000072789938688,
  2000168210371596,2000368254482174,2000765892819580,2001516848487306,2002866508684377,
  2005178008251297,2008954288218485,2014843390177208,2023614044335520,2036089502821965,
  2053033107373099,2074989779776407,2102102197371376,2133935453338321,2169354472110407,
  2206499137636637,2242889629738845,2275669235194545,2301958902918632,2319265829286631,
  2325867420189660,2321089878345064,2305419875005243,2280424041237510,2248494461180067,
  2212476644586521,2175259017683786,2139404452927826,2106886126076630,2078959132416601,
  2056165732016561,2038445052932941,2025303316889328,2015999306374991,2009709004673460,
  2005648039960054,2003145550361889,2001674603967370,2000850714481840,2000411557377129,
  2000189157464843,2000082367053592,2000033867515937,2000013097366404,2000004740709785,
  2000001596363223,2000000496243123,2000000140966892,2000000036086339,2000000008157651,
  2000000001576969,2000000000245799]
private def wc_rkmTraj_m256_r64_s0_v1_p1 : List ℕ := [2000000000026748]
private def wc_rkmTraj_m256_r64_s0_v1 : List ℕ := pCat wc_rkmTraj_m256_r64_s0_v1_p0
  wc_rkmTraj_m256_r64_s0_v1_p1
private def wc_rkmTrajPack_m2_r96_s5_hb_p0 : List ℕ := [174826571970437,245217929194071,
  297848750631026,341059873465380,378109878955950,410683550606340,439789611599051,466090358641011,
  490049292663706,512006380424406,532220129403237,550892800405731,568186358903920,584233018167800,
  599142463372726,613006953304544,625905017016306,637904192378690,649063094346519,659433003685646,
  669059105785488,677981469625142,686235830724562,693854224126756,700865501161662,707295755090435,
  713168674542149,718505839165513,723326968616359,727650133543012,731491935379890,734867660349995,
  737791411993334,740276225697493,742334168048515,743976423301011,745213368853485,746054641284032,
  746509194234609,746585349215092,746290840220802,745632852910827,744618058972925,743252646199160,
  741542344710580,739492449696153,737107840968264,734392999582158,731352021718236,727988629982428,
  724306182239863,720307678059528,715995762811587,711372729423457,706440517764792,701200711594016,
  695654532959041,689802833901027,683646085261093,677184362334092,670417327048987,663344206279389,
  655963765797460,648274279275638]
private def wc_rkmTrajPack_m2_r96_s5_hb_p1 : List ℕ := [640273491608469,631958575664755,
  623326081379646,614371875846152,605091072750748,595477949098437,585525846661605,575227054927148,
  564572671456184,553552434438156,542154520713838,530365300512656,518169037383823,505547517979492,
  492479590990635,478940586903108,464901579171526,450328431036881,435180547466861,419409213364481,
  402955338149389,385746326510527,367691624236161,348676184378644,328550532084823,307114983244253,
  284093179451960,259084518691911,231470393864500,200203824887555,163233707535734,115242913982301]
private def wc_rkmTrajPack_m2_r96_s5_hb : List ℕ := pCat wc_rkmTrajPack_m2_r96_s5_hb_p0
  wc_rkmTrajPack_m2_r96_s5_hb_p1
private def wc_rkmTrajPack_m2_r96_s5_v0_p0 : List ℕ := [1999924469345494,1999856352280047,
  1999851402274429,2000055579978617,1999911211571734,2000182332466355,2000158270987287,
  1999945837931452,1999983870711952,1999967540524736,1999826176681914,1999709209047819,
  2000278308599991,2000131918270565,1999944031638121,1999818394338926,1999787935635610,
  1999803829162783,2000201838712143,2000247804650480,2000286502864346,2000249272754573,
  2000109184535756,1999908942882274,2000262508580273,1999673616068694,2000263239138053,
  2000124634426959,2000001942871905,1999967441956297,1999973582821269,2000125112772724,
  2000222855114286,2000366772077735,1999341785235818,1998934931024260,1998769443851401,
  1999418975090379,2001111661449981,2003039772250446,1996688077870221,2000143631224422,
  2006105283087258,2011599108525229,2010146436151401,2002878056547100,2025736603688960,
  2047995494634435,2053131426998440,2025639749057934,2040846901235906,2138932856414999,
  2249022542948505,2346340733722599,2409850512702457,2428909133515339,2405165670436252,
  2349819715989651,2278344677819594,2205283213958409,2140920075766521,2090321327745656,
  2054177571824376,2030466530006984]
private def wc_rkmTrajPack_m2_r96_s5_v0_p1 : List ℕ := [2016082999018320,2007977357431089,
  2003720255430117,2001631794546081,2000673270842350,2000261277103372,2000095337458952,
  2000032692676098,2000010528041587,2000003180910943,1999999099325435,1999999761324397,
  1999999940900547,2000000013648929,2000000002933862,2000000000585545,2000000000108207,
  1999999999981546,1999999999997109,2000000000000411,1999999999999949,1999999999999996,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000]
private def wc_rkmTrajPack_m2_r96_s5_v0 : List ℕ := pCat wc_rkmTrajPack_m2_r96_s5_v0_p0
  wc_rkmTrajPack_m2_r96_s5_v0_p1
private def wc_rkmTrajPack_m2_r96_s5_v1_p0 : List ℕ := [2000262647573336,1999984369296731,
  1999847856366655,2000568732681164,1999514073591207,2000430318957049,1999621635839248,
  1999920249245391,2000860947485313,1997787576553882,2002715544564617,1997923023217742,
  2000258099277181,2001695722591056,1996528654215777,2003306378763477,1998871816427947,
  1999243927182254,2001953751180207,1998132438937290,2001004194889506,1999889421198365,
  1998682098463360,2002099166283019,1998856545175531,1999099733122314,2002307353963585,
  1998221301645816,1999085592118133,2002458438868434,1998269600607029,1999007216464642,
  2002624038085441,1998308455974373,1998520702392202,2003155758814943,1998539902354593,
  1997021955735867,2004393402417409,2001238946268265,1994125131352110,2002095332754647,
  2006462754299481,1994501514247677,1993903913181528,2008226834367983,2004739852892521,
  1989321254085150,1996632078341101,2012789219299049,2002714846311567,1985743291351744,
  1997035212101842,2014758414513991,2003438777885866,1984717200448628,1994992557537774,
  2015278120803914,2007550887434006,1985603408540057,1989384562349986,2013098645739506,
  2015442860346110,1990851890257788]
private def wc_rkmTrajPack_m2_r96_s5_v1_p1 : List ℕ := [1979391591145819,2001382816967872,
  2024116156199611,2011525685909785,1979185390378141,1973571335332272,2006620025313628,
  2036668274008271,2020994166566905,1971983050205712,1946776314286284,1982111772596705,
  2049002050942866,2077865169233419,2028296929746573,1933407894330353,1877087261855597,
  1927291677387503,2084368998361550,2283179784269370,2439317554545881,2499134565150437,
  2460389121146884,2359207752615226,2241754672691863,2141635811395700,2072418821030803,
  2032225914595856,2012376054004575,2004036730820274,2001086541956739,2000228175259796,
  2000032449331761]
private def wc_rkmTrajPack_m2_r96_s5_v1 : List ℕ := pCat wc_rkmTrajPack_m2_r96_s5_v1_p0
  wc_rkmTrajPack_m2_r96_s5_v1_p1
private def wc_rkmTrajPack_m2_r96_s4_hb_p0 : List ℕ := [191240448000000,267637597368865,
  324337377139937,370528368000000,409808865034867,444043520167652,474351249398043,501468340333243,
  525911232000000,548059578015587,568202726301777,586567596955205,603336336055866,618657994765209,
  632656539150730,645436512000000,657087139162034,667685374488644,677298201733924,685984404514886,
  693795947877002,700779071261635,706975163643361,712421471917332,717151680000000,721196386520375,
  724583502121136,727338582410333,729485108941417,731044727870685,732037453885407,732481845430580,
  732395156058665,731793465792810,730691795663231,729104208000000,727043894607403,724523254578441,
  721553963212741,718147033261803,714312869530351,710061317702545,705401708129985,700342895209167,
  694893292885209,689060906742626,682853363080185,676277935313060,669341568000000,662050898754563,
  654412278266517,646431788631285,638115260161150,629468286831067,620496240493979,611204283984905,
  601597383219585,591680318381654,581457694282043,570933949965293,560113367629591,549000080920355,
  537598082651115,525911232000000]
private def wc_rkmTrajPack_m2_r96_s4_hb_p1 : List ℕ := [513943261225361,501697781939847,
  489178290978415,476388175892475,463330720099316,450009107713317,436426428083030,422585680056104,
  408489775992050,394141545541165,379543739206309,364699031702882,349610025131023,334279251972944,
  318709177927224,302902204590988,286860672000000,270586861035928,254082995709345,237351245326342,
  220393726546076,203212505336005,185809598831095,168186977102792,150346564843171,132290242969279,
  114019850152336,95537184276129,76844003828659,57942029230804,38832944105523,19518396490885]
private def wc_rkmTrajPack_m2_r96_s4_hb : List ℕ := pCat wc_rkmTrajPack_m2_r96_s4_hb_p0
  wc_rkmTrajPack_m2_r96_s4_hb_p1
private def wc_rkmTrajPack_m2_r96_s4_v0 : List ℕ := [1999807280574989,1999585649602507,
  2000557647342318,2000495118408145,2000218085009179,2000136737989799,2000393142026357,
  2000481736622131,2000481761999265,2000516847827497,1999385680845116,1999324949898429,
  1999400670519813,1999520647058142,1999339115874532,1998587791182896,1997973567132374,
  2000389504049068,2011536162052221,2038793483707110,2087952320952322,2159027474213395,
  2243641155873022,2326125849188943,2388464623611810,2416815296310986,2406362582970645,
  2362275200253976,2296779121094814,2224252668201994,2156759418821301,2101607063104251,
  2061176406737290,2034260923573515,2017864437305714,2008678145688777,2003928681214005,
  2001657494909392,2000651501992187,2000238438074095,2000081175882107,2000025674859302,
  2000007531447758,2000002044508981,2000000512198678,1999999881991911,1999999975106211,
  2000000004781034,2000000000829866,1999999999871095,1999999999982327,1999999999997906,
  2000000000000206,1999999999999986,2000000000000000]
private def wc_rkmTrajPack_m2_r96_s4_v1_p0 : List ℕ := [1999924469345494,1999856352280047,
  1999851402274429,1999944420021383,2000088788428266,2000182332466355,2000158270987287,
  2000054162068548,1999983870711952,2000032459475264,2000173823318086,2000290790952181,
  2000278308599991,2000131918270565,1999944031638121,1999818394338926,1999787935635610,
  1999803829162783,1999798161287857,1999752195349520,1999713497135654,1999750727245427,
  1999890815464244,2000091057117726,2000262508580273,2000326383931306,2000263239138053,
  2000124634426959,2000001942871905,1999967441956297,2000026417178731,2000125112772724,
  2000222855114286,2000366772077735,2000658214764182,2001065068975740,2001230556148599,
  2000581024909621,1998888338550019,1996960227749554,1996688077870221,1999856368775578,
  2006105283087258,2011599108525229,2010146436151401,1997121943452900,1974263396311040,
  1952004505365565,1946868573001560,1974360250942066,2040846901235906,2138932856414999,
  2249022542948505,2346340733722599,2409850512702457,2428909133515339,2405165670436252,
  2349819715989651,2278344677819594,2205283213958409,2140920075766521,2090321327745656,
  2054177571824376,2030466530006984]
private def wc_rkmTrajPack_m2_r96_s4_v1_p1 : List ℕ := [2016082999018320,2007977357431089,
  2003720255430117,2001631794546081,2000673270842350,2000261277103372,2000095337458952,
  2000032692676098,2000010528041587,2000003180910943,2000000900674565,2000000238675603,
  2000000059099453,2000000013648929,2000000002933862,2000000000585545,2000000000108207,
  2000000000018454,2000000000002891,2000000000000411,2000000000000051,2000000000000004,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000]
private def wc_rkmTrajPack_m2_r96_s4_v1 : List ℕ := pCat wc_rkmTrajPack_m2_r96_s4_v1_p0
  wc_rkmTrajPack_m2_r96_s4_v1_p1
private def wc_rkmTrajPack_m64_r63_s0_hb : List ℕ := [202348324186717,282772424494368,
  342164674058656,390287803515323,430969169623288,466193839369949,497153745423738,524633531378593,
  549183619342543,571208567884771,591016537816901,608848973483905,624899405150037,639325891091851,
  652259551725289,663810601647971,674072723127412,683126307020362,691040900099826,697877083576196,
  703687935641439,708520184246131,712415125362536,715409360970809,717535396448229,718822126769621,
  719295233552278,718977509594221,717889123556946,716047834423161,713469163032598,710166526164313,
  706151337146344,701433075724402,696019328825054,689915802834763,683126307020362,675652706675866,
  667494843426139,658650418768089,649114835280336,638880987843055,627938994486081,616275852846397,
  603875003255906,590715772582218,576772663166108,562014437062066,546402924921453,529891457356338,
  512422767868115,493926138838411,474313434648170,453473448972816,431263607841431,407497350637987,
  381924086466052,354195589329075,323805618732321,289970968209223,251364737898544,205386832100709,
  145300328089073]
private def wc_rkmTrajPack_m64_r63_s0_v1 : List ℕ := [2000380746733201,2001667527827620,
  2005096833681930,2012552176890446,2026414014318415,2049044238993914,2081991534593021,
  2125146031060575,2176168999903785,2230485263633558,2281948660194614,2324043993628351,
  2351281607413302,2360365042160695,2350797137615613,2324791204778345,2286581824802352,
  2241395434722985,2194394407098232,2149852843073336,2110700882743829,2078443389760814,
  2053362832022743,2034874408871797,2021909064690601,2013237710324663,2007695909840996,
  2004306424844198,2002320081691299,2001203673220788,2000601441376522,2000289460875505,
  2000134184832741,2000059911754767,2000025761235829,2000010665739588,2000004250895393,
  2000001630427527,2000000601575686,2000000213427606,2000000072769910,2000000023830111,
  2000000007489703,2000000002257423,2000000000651878,2000000000180159,2000000000047590,
  2000000000011998,2000000000002880,2000000000000654,2000000000000139,2000000000000027,
  2000000000000003,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m64_r63_s1_hb : List ℕ := [207945146113670,290593724285748,
  351628724517670,401082908171199,442889494182845,479088455190874,510904691939542,539144550749946,
  564373678044602,587007822217368,607363667605793,625689336747071,642183712825627,657009225906275,
  670300623109659,682171167496882,692717132525529,702021132610722,710154638143590,717179905971071,
  723151482393107,728117387824739,732120060457735,735197114659017,737381954883278,738704275321395,
  739190467927350,738863955933008,737745465851813,735853247868287,733203252118409,729809266480544,
  725683019967896,720834254529726,715270766942012,708998421426126,702021132610722,694340817382624,
  685957312986143,676868257343101,667068925870455,656552016925428,645307375209043,633321638721447,
  620577789764988,607054583401990,592725816724702,577559387766527,561516071439679,544547907511567,
  526596045529794,507587811873049,487432633148858,466016227138648,443192076368980,418768460079552,
  392487856194098,363992407013404,332761869762694,297991374998238,258317321678952,211067697163609,
  149319239861685]
private def wc_rkmTrajPack_m64_r63_s1_v1 : List ℕ := [2000000000000003,2000000000000009,
  2000000000000088,2000000000000733,2000000000005243,2000000000032540,2000000000179449,
  2000000000891790,2000000004036264,2000000016773643,2000000064418520,2000000229827602,
  2000000765030018,2000002384586148,2000006981377448,2000019248962882,2000050095718509,
  2000123305066684,2000287541041909,2000636233632063,2001337552886828,2002674811819465,
  2005093458172648,2009244096546092,2016002748109679,2026442643441161,2041730788526018,
  2062932265047733,2090728487454904,2125090064051224,2164981191326003,2208195647566272,
  2251418837643238,2290567476406411,2321383874050380,2340176674611525,2344535431626057,
  2333831159126856,2309361367103787,2274094502753351,2232082529934447,2187700999833078,
  2144912141159301,2106719254063806,2074905716819022,2050060816961504,2031820186074311,
  2019211665327357,2011001020438885,2005964192953089,2003055225776060,2001475302825824,
  2000669661754669,2000284791509605,2000113021992855,2000041652922832,2000014168936043,
  2000004414427016,2000001246898087,2000000314874379,2000000069658229,2000000013072573,
  2000000001962278,2000000000204038]
private def wc_rkmTrajPack_m64_r55_s0_hb : List ℕ := [243272253721265,338223203973706,
  407113640394418,461867955443803,507185655639547,545516486117128,578338765475193,606630562807580,
  631081492547941,652201070631295,670379501468234,685924227574342,699083130861369,710059917895366,
  719024695529803,726121462679446,731473555035284,735187690053859,737357029941673,738063540000000,
  737379831154782,735370618071135,732093886076837,727601834170645,721941643391541,715156107100125,
  707284150561863,698361260503085,688419840284457,677489502488286,665597307681940,652767955632390,
  639023933097425,624385620329483,608871356427306,592497461471216,575278210746073,557225752970983,
  538349959842860,518658187628175,498154921821744,476841261066628,454714173215704,431765418608837,
  407979972270244,383333666527064,357789575635139,331292282980222,303758401116173,275060041192355,
  244993947204526,213218356000000,179106122549046,141328408088520,96161801660196]
private def wc_rkmTrajPack_m64_r55_s0_v1 : List ℕ := [2000000000135756,2000000001590497,
  2000000012672947,2000000079368076,2000000414709672,2000001868367023,2000007411259873,
  2000026262570851,2000084028178230,2000244732672190,2000653015135832,2001604580886683,
  2003646232582121,2007689470316795,2015093704645733,2027645299295807,2047346425595847,
  2075957437353559,2114322065614143,2161630914964708,2214892998523401,2268913792872722,
  2316967498478854,2352110918833574,2368806634906165,2364339684162105,2339533075781690,
  2298505233880175,2247565717415725,2193651334155129,2142827726032665,2099285056476364,
  2065012470261671,2040073289925340,2023232793696850,2012656461204293,2006471303099561,
  2003101447703619,2001391126039823,2000582953291606,2000227765496178,2000082778648040,
  2000027909950206,2000008702810363,2000002500608344,2000000659277729,2000000158683883,
  2000000034657632,2000000006817682,2000000001196756,2000000000185223,2000000000024870,
  2000000000002829,2000000000000261,2000000000000017,2000000000000000]
private def wc_rkmTrajPack_m64_r51_s1_hb : List ℕ := [251497560717542,349404888491135,
  420255314572988,476402721744788,522718966502516,561745043286228,595015084425898,623544512699413,
  648049527265602,669059423647988,686979619297053,702129557079151,714766769946009,725102840345519,
  733314370622438,739550753454240,743939817229960,746592017503922,747603607548128,747059075427305,
  745033043120572,741591763554270,736794311684984,730693538690405,723336839440765,714766769946009,
  705021541605324,694135411631332,682138983156041,669059423647988,654920605903199,639743171591084,
  623544512699413,606338660700400,588136066134013,568943241513082,548762226333386,527589811796462,
  505416429995628,482224559627177,457986412864702,432660517444841,406186537358711,378477164382604,
  349404888491135,318779249358599,286304969189215,251497560717542,213489913293098,170492128083536,
  117627213226802]
private def wc_rkmTrajPack_m64_r51_s1_v0 : List ℕ := [2000058383634255,2000312775198096,
  2001158825336434,2003427636654444,2008582433799592,2018782129853232,2036653997649814,
  2064670992933985,2104191426531201,2154435113322466,2211825800008823,2270105786744702,
  2321384723428700,2357905557161818,2373976427110808,2367404295443033,2339941913784080,
  2296641431045535,2244410933123045,2190313665137336,2140150162825305,2097662755553660,
  2064423430762301,2040238457925024,2023799259453118,2013328877547986,2007067370130277,
  2003546707953037,2001683868257408,2000755890123049,2000320603619607,2000128370012991,
  2000048473061014,2000017240864492,2000005768130637,2000001812298690,2000000533748627,
  2000000147036680,2000000037793826,2000000009038026,2000000002004129,2000000000410448,
  2000000000077271,2000000000013294,2000000000002073,2000000000000289,2000000000000035,
  2000000000000003,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m64_r51_s1_v1 : List ℕ := [1999999999999999,1999999999999997,
  2000000000000000,1999999999999998,2000000000000005,2000000000000001,1999999999999998,
  2000000000000000,2000000000000007,2000000000000002,1999999999999984,1999999999999928,
  2000000000000313,2000000000001195,1999999999996146,1999999999984150,2000000000038547,
  2000000000190489,1999999999708278,1999999997957523,2000000001225373,2000000019048729,
  2000000006967400,1999999852893106,1999999782762881,2000000834725273,2000002671706078,
  1999998066542218,1999979028340538,1999976820619570,2000089277406372,2000320017782504,
  2000161263562758,1998527829130234,1995372064670453,1995421895519489,2011228440001207,
  2060028763762816,2151952951578656,2276124273669248,2397634783710061,2472599050498196,
  2472963028633645,2402571502561938,2292574836054713,2181418367265227,2095483272601022,
  2042215504271230,2015402752361579,2004498450236616,2000992516910895,2000143320659391]
private abbrev dP_0 : Prop := atF [ bNLE (bEvalLo12W 4 2048 128 [2,4,8,16,32,59,59,59]
  [15675064,15890715,16350142,17402815,22950782,12367946,10760114,4133531] [3,5,9,17,38,31,27,11]
  rkmMasks_m4_r128 [none, none, none, none, some (38, 129, wc_rkmTraj_m4_r128_s4_hb,
  wc_rkmTraj_m4_r128_s4_v0, wc_rkmTraj_m4_r128_s4_v2), some (31, 129, wc_rkmTraj_m4_r128_s5_hb,
  wc_rkmTraj_m4_r128_s5_v0, wc_rkmTraj_m4_r128_s5_v2), some (27, 129, wc_rkmTraj_m4_r128_s6_hb,
  wc_rkmTraj_m4_r128_s6_v0, wc_rkmTraj_m4_r128_s6_v2)]) rkmRow_m4_r128, bNLE (bEvalLo12W 256 32 14
  [1,1] [47833196,993174] [17,2] rkmMasks_m256_r14 []) rkmRow_m256_r14] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bNLE (bEvalLo12W 64 128 55 [1,1,1,1,1,1,1,1]
  [49204236,38015319,15750537,16352668,14072029,7914853,3708183,7054101] [24,19,8,8,7,4,2,4]
  rkmMasksPack_m64_r55 [some (24, 56, wc_rkmTrajPack_m64_r55_s0_hb, wc_rkmTraj_m256_r64_s0_v0,
  wc_rkmTrajPack_m64_r55_s0_v1)]) rkmRowPack_m64_r55, bNLE (bEvalLo12W 64 128 14 [1,1,1]
  [94702425,4684372,2674840] [16,2,2] rkmMasks_m64_r14 []) rkmRow_m64_r14] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bNLE (bEvalLo12W 2 4096 96 [2,4,12,27,48,84,84,84]
  [17717489,17819133,20160138,17506968,21912968,19272818,8402594,4623819] [2,3,7,11,22,28,13,7]
  rkmMasksPack_m2_r96 [none, none, none, none, some (22, 97, wc_rkmTrajPack_m2_r96_s4_hb,
  wc_rkmTrajPack_m2_r96_s4_v0, wc_rkmTrajPack_m2_r96_s4_v1), some (28, 97,
  wc_rkmTrajPack_m2_r96_s5_hb, wc_rkmTrajPack_m2_r96_s5_v0, wc_rkmTrajPack_m2_r96_s5_v1)])
  rkmRowPack_m2_r96, bNLE (bEvalLo12W 8 1024 29 [1,3] [80107915,77247778] [6,13] rkmMasks_m8_r29
  []) rkmRow_m8_r29] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bSlideChk 28 97 wc_rkmTrajPack_m2_r96_s5_hb
  wc_rkmTrajPack_m2_r96_s5_v0 wc_rkmTrajPack_m2_r96_s5_v1, bNLE (bEvalLo12W 128 64 19 [1,1]
  [69709551,1443054] [23,2] rkmMasks_m128_r19 []) rkmRow_m128_r19] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bNLE (bEvalLo12W 256 32 48 [1,1,1] [47500000,3000000,896875]
  [50,4,1] rkmMasks_m256_r48 []) rkmRow_m256_r48, bNLE (bEvalLo12W 8 1024 60 [1,1,1,1,8,8,8,8]
  [2695477,28252591,18956481,22281061,1940877,6434092,187654,1830552] [1,3,2,3,1,4,1,1]
  rkmMasksPack_m8_r60 []) rkmRowPack_m8_r60] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bNLE (bEvalLo12W 256 32 64 [1,1,1,1]
  [25169277,25205117,1235256,895719] [36,36,2,2] rkmMasks_m256_r64 [some (36, 65,
  wc_rkmTraj_m256_r64_s0_hb, wc_rkmTraj_m256_r64_s0_v0, wc_rkmTraj_m256_r64_s0_v1)])
  rkmRow_m256_r64, bNLE (bEvalLo12W 32 256 20 [1,1,1,1,1,1,1,1]
  [46345889,40827264,30374918,22237385,10786560,10792204,5550246,5066751] [7,6,5,4,2,2,1,1]
  rkmMasksPack_m32_r20 []) rkmRowPack_m32_r20] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bSlideChk 19 129 wc_rkmTraj_m4_r128_s4_hb
  wc_rkmTraj_m4_r128_s4_v0 wc_rkmTraj_m4_r128_s4_v1, bNLE (bEvalLo12W 32 256 52 [1,1,1,1,1,1,1,1]
  [13739615,13261486,13162483,9041704,305338,9656,7362627,7761225] [4,4,4,3,1,1,3,3]
  rkmMasksPack_m32_r52 []) rkmRowPack_m32_r52] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bSlideChk 19 129 wc_rkmTraj_m4_r128_s4_hb
  wc_rkmTraj_m4_r128_s4_v1 wc_rkmTraj_m4_r128_s4_v2, bNLE (bEvalLo12W 2 4096 28
  [2,4,8,16,21,21,21] [42553875,30106097,34500000,24395184,45689222,10463252,3800619]
  [2,2,4,5,11,3,1] rkmMasks_m2_r28 []) rkmRow_m2_r28] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := atF [ bNLE (bEvalLo12W 64 128 63 [2,2,2,2,2,2,2,2]
  [21406613,18525226,9415540,15835452,5620185,3508488,4777773,2294496] [19,16,9,14,5,3,5,2]
  rkmMasksPack_m64_r63 [some (19, 64, wc_rkmTrajPack_m64_r63_s0_hb, wc_rkmTraj_m256_r64_s0_v0,
  wc_rkmTrajPack_m64_r63_s0_v1), some (16, 64, wc_rkmTrajPack_m64_r63_s1_hb,
  wc_rkmTrajPack_m64_r63_s0_v1, wc_rkmTrajPack_m64_r63_s1_v1)]) rkmRowPack_m64_r63, bNLE
  (bEvalLo12W 512 16 22 [1,1] [33967692,704465] [26,2] rkmMasks_m512_r22 []) rkmRow_m512_r22] =
  true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := atF [ bSlideChk 36 65 wc_rkmTraj_m256_r64_s0_hb
  wc_rkmTraj_m256_r64_s0_v0 wc_rkmTraj_m256_r64_s0_v1, bNLE (bEvalLo12W 16 512 25 [1,2,2,2]
  [75554117,100393224,30642630,10759911] [9,18,6,3] rkmMasks_m16_r25 []) rkmRow_m16_r25] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := atF [ bNLE (bEvalLo12W 64 128 51 [1,1,1,1,1,1]
  [36410557,48422966,14415708,19253297,15576237,7147668] [17,22,7,9,8,4] rkmMasksPack_m64_r51
  [none, some (22, 52, wc_rkmTrajPack_m64_r51_s1_hb, wc_rkmTrajPack_m64_r51_s1_v0,
  wc_rkmTrajPack_m64_r51_s1_v1)]) rkmRowPack_m64_r51, bNLE (bEvalLo12W 1024 8 24 [1] [24425176]
  [32] rkmMasks_m1024_r24 []) rkmRow_m1024_r24] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := atF [ bNLE (bEvalLo12W 64 128 42 [1,1,1,1,1,1,1,1]
  [31988323,25576932,25670166,14479826,10514772,5872390,6654597,5120627] [13,10,10,6,5,3,3,2]
  rkmMasksPack_m64_r42 []) rkmRowPack_m64_r42, bNLE (bEvalLo12W 64 128 26 [1,1,1,1,1,1,1,1]
  [23794117,30975092,23464264,8465502,7193715,7203624,5429453,3696269] [7,9,7,3,2,2,2,1]
  rkmMasksPack_m64_r26 []) rkmRowPack_m64_r26] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := atF [ bSlideChk 22 97 wc_rkmTrajPack_m2_r96_s4_hb
  wc_rkmTrajPack_m2_r96_s4_v0 wc_rkmTrajPack_m2_r96_s4_v1, bNLE (bEvalLo12W 16 512 31 [1,3,3,3]
  [69336291,88833651,12764193,4274313] [8,23,4,2] rkmMasksPack_m16_r31 []) rkmRowPack_m16_r31] =
  true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m4_r128_s5_hb
  wc_rkmTraj_m4_r128_s5_v0 wc_rkmTraj_m4_r128_s5_v1, bSlideChk 22 52 wc_rkmTrajPack_m64_r51_s1_hb
  wc_rkmTrajPack_m64_r51_s1_v0 wc_rkmTrajPack_m64_r51_s1_v1] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := atF [ bNLE (bEvalLo12W 16 512 44 [1,2,4,6,6,6]
  [45946875,20979859,17250000,43172257,5323682,1824291] [7,6,8,24,3,1] rkmMasks_m16_r44 [])
  rkmRow_m16_r44, bNLE (bEvalLo12W 64 128 31 [1,1,1] [96667412,12772439,4842993] [32,5,3]
  rkmMasks_m64_r31 []) rkmRow_m64_r31] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := atF [ bSlideChk 15 129 wc_rkmTraj_m4_r128_s5_hb
  wc_rkmTraj_m4_r128_s5_v1 wc_rkmTraj_m4_r128_s5_v2, bNLE (bEvalLo12W 32 256 34 [1,2]
  [61244808,73429251] [13,24] rkmMasksPack_m32_r34 []) rkmRowPack_m32_r34] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := atF [ bSlideChk 14 129 wc_rkmTraj_m4_r128_s6_hb
  wc_rkmTraj_m4_r128_s6_v0 wc_rkmTraj_m4_r128_s6_v1, bNLE (bEvalLo12W 16 512 34 [1,3,3,3]
  [59502040,91888523,18457099,6238093] [9,27,6,3] rkmMasks_m16_r34 []) rkmRow_m16_r34] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := atF [ bSlideChk 13 129 wc_rkmTraj_m4_r128_s6_hb
  wc_rkmTraj_m4_r128_s6_v1 wc_rkmTraj_m4_r128_s6_v2, bSlideChk 24 56 wc_rkmTrajPack_m64_r55_s0_hb
  wc_rkmTraj_m256_r64_s0_v0 wc_rkmTrajPack_m64_r55_s0_v1, bNLE (bEvalLo12W 2 4096 13
  [1,2,4,8,12,12,12,12] [49234218,45850523,56107754,57045033,30701500,23680833,5342198,7918713]
  [1,2,3,4,3,2,1,1] rkmMasksPack_m2_r13 []) rkmRowPack_m2_r13] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := atF [ bNLE (bEvalLo12W 64 128 36 [1,1,1,1,1,1,1,1]
  [31584809,34748387,14265954,13299519,9440493,5207603,5880636,4510596] [11,12,5,5,4,2,3,2]
  rkmMasksPack_m64_r36 []) rkmRowPack_m64_r36, bSlideChk 19 64 wc_rkmTrajPack_m64_r63_s0_hb
  wc_rkmTraj_m256_r64_s0_v0 wc_rkmTrajPack_m64_r63_s0_v1, bNLE (bEvalLo12W 4 2048 17
  [1,2,4,8,8,8,8,8] [47742671,50597482,54581000,33184522,34863899,10162843,4149193,1934352]
  [2,3,5,5,5,2,1,1] rkmMasks_m4_r17 []) rkmRow_m4_r17] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := atF [ bNLE (bEvalLo12W 64 128 29 [1,1,1]
  [102645205,6041388,3877904] [34,3,3] rkmMasks_m64_r29 []) rkmRow_m64_r29, bNLE (bEvalLo12W 512
  16 29 [1,1,1] [17445650,8722825,8722825] [17,9,9] rkmMasks_m512_r29 []) rkmRow_m512_r29, bNLE
  (bEvalLo12W 128 64 26 [1,1,1,1] [66792945,4200355,1385073,247602] [28,3,2,2] rkmMasks_m128_r26
  []) rkmRow_m128_r26] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := atF [ bSlideChk 16 64 wc_rkmTrajPack_m64_r63_s1_hb
  wc_rkmTrajPack_m64_r63_s0_v1 wc_rkmTrajPack_m64_r63_s1_v1, bNLE (bEvalLo12W 64 128 19 [1,1,1]
  [101746969,2927294,654772] [24,2,2] rkmMasks_m64_r19 []) rkmRow_m64_r19, bNLE (bEvalLo12W 16 512
  18 [1,2,2,2] [88228214,74784325,22214716,8727476] [8,11,4,3] rkmMasks_m16_r18 [])
  rkmRow_m16_r18, bNLE (bEvalLo12W 16 512 112 [1,1,1,1,1,1,1,1]
  [16028302,12118838,6489024,8690404,461408,430030,6340119,21770666] [4,3,2,3,1,1,2,6]
  rkmMasksPack_m16_r112 []) rkmRowPack_m16_r112, bNLE (bEvalLo12W 2 4096 20 [1,2,4,8,15,15,15]
  [27825880,30551985,39137224,47029691,66598142,9385805,6742027] [1,1,2,4,9,2,1]
  rkmMasksPack_m2_r20 []) rkmRowPack_m2_r20, bNLE (bEvalLo12W 32 256 13 [1,1,1]
  [129129390,16860678,7327749] [14,3,2] rkmMasks_m32_r13 []) rkmRow_m32_r13, bNLE (bEvalLo12W 512
  16 10 [1,1,1] [23091279,6128312,4764132] [10,3,2] rkmMasks_m512_r10 []) rkmRow_m512_r10] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := atF [ bNLE (bEvalLo12W 4 2048 14 [1,2,4,6,6,6,6,6]
  [74083796,53163912,57934292,37266824,28831835,15290977,3879727,2222242] [2,3,4,4,3,2,1,1]
  rkmMasksPack_m4_r14 []) rkmRowPack_m4_r14, bNLE (bEvalLo12W 8 1024 14 [1,2,3,3,3]
  [90375235,55550855,69299269,22098489,7267274] [4,4,6,2,1] rkmMasksPack_m8_r14 [])
  rkmRowPack_m8_r14, bNLE (bEvalLo12W 32 256 11 [1,1,1] [126749737,15816760,6483185] [12,3,2]
  rkmMasks_m32_r11 []) rkmRow_m32_r11, bNLE (bEvalLo12W 256 32 11 [1,1] [47449361,984064] [14,2]
  rkmMasks_m256_r11 []) rkmRow_m256_r11, bNLE (bEvalLo12W 4 2048 11 [1,3,4,4,4]
  [98033563,71531085,40173810,52779552,35226421] [3,4,3,3,2] rkmMasksPack_m4_r11 [])
  rkmRowPack_m4_r11, bNLE (bEvalLo12W 64 128 4 [1,1] [90682223,2203732] [6,2] rkmMasks_m64_r4 [])
  rkmRow_m64_r4, bNLE (bEvalLo12W 8 1024 5 [1,1,1] [244575103,41991475,24957584] [6,2,1]
  rkmMasks_m8_r5 []) rkmRow_m8_r5, bNLE (bEvalLo12W 512 16 6 [1,1,1] [22659237,5998033,4662805]
  [6,3,2] rkmMasks_m512_r6 []) rkmRow_m512_r6, bNLE (bEvalLo12W 8 1024 6 [1,1,1,1,1]
  [102075706,86436784,67079683,50814595,31269323] [4,3,3,3,2] rkmMasks_m8_r6 []) rkmRow_m8_r6,
  bNLE (bEvalLo12W 8 1024 3 [1,1,1,1,1] [162953765,63895887,27308790,9499359,6601059] [17,7,3,1,1]
  rkmMasks_m8_r3 []) rkmRow_m8_r3, bNLE (bEvalLo12W 1024 8 9 [1,1,1,1]
  [11950125,5259375,3825000,2868750] [7,3,2,2] rkmMasks_m1024_r9 []) rkmRow_m1024_r9, bNLE
  (bEvalLo12W 2 4096 4 [1,2,3,3,3,3,3,3]
  [132484861,156761143,55690312,46369939,11922464,6935030,2306269,3366332] [1,2,1,1,1,1,1,1]
  rkmMasksPack_m2_r4 []) rkmRowPack_m2_r4, bNLE (bEvalLo12W 4 2048 52 [1,1,1,1,1,1,1,1]
  [11415517,13843742,29195765,14331851,2902095,15974666,23788,8624794] [1,1,2,1,1,1,1,1]
  rkmMasksPack_m4_r52 []) rkmRowPack_m4_r52, bNLE (bEvalLo12W 2 4096 22 [1,2,4]
  [53822158,47445742,60885837] [1,2,4] rkmMasksPack_m2_r22 []) rkmRowPack_m2_r22, bNLE (bEvalLo12W
  8 1024 5 [1,1,1,1,1,1,1,1]
  [72488919,72274087,72099027,28688427,32852602,11518981,12299711,9486455] [2,2,2,1,1,1,1,1]
  rkmMasksPack_m8_r5 []) rkmRowPack_m8_r5, bNLE (bEvalLo12W 4 2048 7 [1,2,3,3,3,3,3,3]
  [125225276,113107360,49480269,35797624,8209672,1713130,3810038,2114757] [3,3,2,2,1,1,1,1]
  rkmMasksPack_m4_r7 []) rkmRowPack_m4_r7, bNLE (bEvalLo12W 8 1024 9 [1,2,2,2]
  [145040161,87834299,29407999,12734384] [5,5,2,1] rkmMasksPack_m8_r9 []) rkmRowPack_m8_r9] = true
private theorem bk_21 : dP_21 := by decide +kernel
private theorem ws_rkmTraj_m4_r128_s4 : WalkOk (some (38, 129, wc_rkmTraj_m4_r128_s4_hb,
    wc_rkmTraj_m4_r128_s4_v0, wc_rkmTraj_m4_r128_s4_v2)) := mIter_split rfl (bSlideChk_sound bk_6)
    (bSlideChk_sound bk_7)
private theorem ws_rkmTraj_m4_r128_s5 : WalkOk (some (31, 129, wc_rkmTraj_m4_r128_s5_hb,
    wc_rkmTraj_m4_r128_s5_v0, wc_rkmTraj_m4_r128_s5_v2)) := mIter_split rfl
    (bSlideChk_sound bk_13) (bSlideChk_sound bk_15)
private theorem ws_rkmTraj_m4_r128_s6 : WalkOk (some (27, 129, wc_rkmTraj_m4_r128_s6_hb,
    wc_rkmTraj_m4_r128_s6_v0, wc_rkmTraj_m4_r128_s6_v2)) := mIter_split rfl
    (bSlideChk_sound bk_16) (bSlideChk_sound bk_17)
/-- Kernel trajectory certificate `(m = 4, r = 128)`. -/
theorem rkmTraj_m4_r128 : rkmEvalT16Lo12 4 2048 128 [2, 4, 8, 16, 32, 59, 59, 59] [15675064,
  15890715, 16350142, 17402815, 22950782, 12367946, 10760114, 4133531] [3, 5, 9, 17, 38, 31, 27, 11]
  rkmMasks_m4_r128 = rkmRow_m4_r128 :=
    bhW_eq bk_0 (wSkip (wSkip (wSkip (wSkip (wCons ws_rkmTraj_m4_r128_s4 (wCons
      ws_rkmTraj_m4_r128_s5 (wCons ws_rkmTraj_m4_r128_s6 wNil)))))))
/-- Kernel trajectory certificate `(m = 16, r = 18)`. -/
theorem rkmTraj_m16_r18 : rkmEvalT16Lo12 16 512 18 [1, 2, 2, 2] [88228214, 74784325, 22214716,
  8727476] [8, 11, 4, 3] rkmMasks_m16_r18 = rkmRow_m16_r18 := bh0_eq (tl2 bk_20)
/-- Kernel trajectory certificate `(m = 64, r = 4)`. -/
theorem rkmTraj_m64_r4 : rkmEvalT16Lo12 64 128 4 [1, 1] [90682223, 2203732] [6, 2] rkmMasks_m64_r4 =
  rkmRow_m64_r4 := bh0_eq (tl1 (tl2 (tl2 bk_21)))
/-- Kernel trajectory certificate `(m = 256, r = 64)`. -/
theorem rkmTraj_m256_r64 : rkmEvalT16Lo12 256 32 64 [1, 1, 1, 1] [25169277, 25205117, 1235256,
  895719] [36, 36, 2, 2] rkmMasks_m256_r64 = rkmRow_m256_r64 :=
    bhW_eq bk_5 (wCons (bSlideChk_sound bk_9) wNil)
/-- Kernel trajectory certificate `(m = 8, r = 5)`. -/
theorem rkmTraj_m8_r5 : rkmEvalT16Lo12 8 1024 5 [1, 1, 1] [244575103, 41991475, 24957584] [6, 2, 1]
  rkmMasks_m8_r5 = rkmRow_m8_r5 := bh0_eq (tl2 (tl2 (tl2 bk_21)))
/-- Kernel trajectory certificate `(m = 256, r = 48)`. -/
theorem rkmTraj_m256_r48 : rkmEvalT16Lo12 256 32 48 [1, 1, 1] [47500000, 3000000, 896875] [50, 4, 1]
  rkmMasks_m256_r48 = rkmRow_m256_r48 := bh0_eq bk_4
/-- Kernel trajectory certificate `(m = 512, r = 6)`. -/
theorem rkmTraj_m512_r6 : rkmEvalT16Lo12 512 16 6 [1, 1, 1] [22659237, 5998033, 4662805] [6, 3, 2]
  rkmMasks_m512_r6 = rkmRow_m512_r6 := bh0_eq (tl1 (tl2 (tl2 (tl2 bk_21))))
/-- Kernel trajectory certificate `(m = 16, r = 44)`. -/
theorem rkmTraj_m16_r44 : rkmEvalT16Lo12 16 512 44 [1, 2, 4, 6, 6, 6] [45946875, 20979859, 17250000,
  43172257, 5323682, 1824291] [7, 6, 8, 24, 3, 1] rkmMasks_m16_r44 = rkmRow_m16_r44 :=
    bh0_eq bk_14
/-- Kernel trajectory certificate `(m = 8, r = 6)`. -/
theorem rkmTraj_m8_r6 : rkmEvalT16Lo12 8 1024 6 [1, 1, 1, 1, 1] [102075706, 86436784, 67079683,
  50814595, 31269323] [4, 3, 3, 3, 2] rkmMasks_m8_r6 = rkmRow_m8_r6 :=
    bh0_eq (tl2 (tl2 (tl2 (tl2 bk_21))))
/-- Kernel trajectory certificate `(m = 16, r = 34)`. -/
theorem rkmTraj_m16_r34 : rkmEvalT16Lo12 16 512 34 [1, 3, 3, 3] [59502040, 91888523, 18457099,
  6238093] [9, 27, 6, 3] rkmMasks_m16_r34 = rkmRow_m16_r34 := bh0_eq (tl1 bk_16)
/-- Kernel trajectory certificate `(m = 8, r = 3)`. -/
theorem rkmTraj_m8_r3 : rkmEvalT16Lo12 8 1024 3 [1, 1, 1, 1, 1] [162953765, 63895887, 27308790,
  9499359, 6601059] [17, 7, 3, 1, 1] rkmMasks_m8_r3 = rkmRow_m8_r3 :=
    bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 bk_21)))))
/-- Kernel trajectory certificate `(m = 64, r = 31)`. -/
theorem rkmTraj_m64_r31 : rkmEvalT16Lo12 64 128 31 [1, 1, 1] [96667412, 12772439, 4842993] [32, 5,
  3] rkmMasks_m64_r31 = rkmRow_m64_r31 := bh0_eq (tl1 bk_14)
/-- Kernel trajectory certificate `(m = 1024, r = 9)`. -/
theorem rkmTraj_m1024_r9 : rkmEvalT16Lo12 1024 8 9 [1, 1, 1, 1] [11950125, 5259375, 3825000,
  2868750] [7, 3, 2, 2] rkmMasks_m1024_r9 = rkmRow_m1024_r9 :=
    bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 bk_21)))))
/-- Kernel trajectory certificate `(m = 64, r = 29)`. -/
theorem rkmTraj_m64_r29 : rkmEvalT16Lo12 64 128 29 [1, 1, 1] [102645205, 6041388, 3877904] [34, 3,
  3] rkmMasks_m64_r29 = rkmRow_m64_r29 := bh0_eq bk_19
/-- Kernel trajectory certificate `(m = 512, r = 10)`. -/
theorem rkmTraj_m512_r10 : rkmEvalT16Lo12 512 16 10 [1, 1, 1] [23091279, 6128312, 4764132] [10, 3,
  2] rkmMasks_m512_r10 = rkmRow_m512_r10 := bh0_eq (tl2 (tl2 (tl2 bk_20)))
/-- Kernel trajectory certificate `(m = 512, r = 29)`. -/
theorem rkmTraj_m512_r29 : rkmEvalT16Lo12 512 16 29 [1, 1, 1] [17445650, 8722825, 8722825] [17, 9,
  9] rkmMasks_m512_r29 = rkmRow_m512_r29 := bh0_eq (tl1 bk_19)
/-- Kernel trajectory certificate `(m = 256, r = 11)`. -/
theorem rkmTraj_m256_r11 : rkmEvalT16Lo12 256 32 11 [1, 1] [47449361, 984064] [14, 2]
  rkmMasks_m256_r11 = rkmRow_m256_r11 := bh0_eq (tl1 (tl2 bk_21))
/-- Kernel trajectory certificate `(m = 128, r = 26)`. -/
theorem rkmTraj_m128_r26 : rkmEvalT16Lo12 128 64 26 [1, 1, 1, 1] [66792945, 4200355, 1385073,
  247602] [28, 3, 2, 2] rkmMasks_m128_r26 = rkmRow_m128_r26 := bh0_eq (tl2 bk_19)
/-- Kernel trajectory certificate `(m = 32, r = 11)`. -/
theorem rkmTraj_m32_r11 : rkmEvalT16Lo12 32 256 11 [1, 1, 1] [126749737, 15816760, 6483185] [12, 3,
  2] rkmMasks_m32_r11 = rkmRow_m32_r11 := bh0_eq (tl2 bk_21)
/-- Kernel trajectory certificate `(m = 16, r = 25)`. -/
theorem rkmTraj_m16_r25 : rkmEvalT16Lo12 16 512 25 [1, 2, 2, 2] [75554117, 100393224, 30642630,
  10759911] [9, 18, 6, 3] rkmMasks_m16_r25 = rkmRow_m16_r25 := bh0_eq (tl1 bk_9)
/-- Kernel trajectory certificate `(m = 32, r = 13)`. -/
theorem rkmTraj_m32_r13 : rkmEvalT16Lo12 32 256 13 [1, 1, 1] [129129390, 16860678, 7327749] [14, 3,
  2] rkmMasks_m32_r13 = rkmRow_m32_r13 := bh0_eq (tl1 (tl2 (tl2 bk_20)))
/-- Kernel trajectory certificate `(m = 1024, r = 24)`. -/
theorem rkmTraj_m1024_r24 : rkmEvalT16Lo12 1024 8 24 [1] [24425176] [32] rkmMasks_m1024_r24 =
  rkmRow_m1024_r24 := bh0_eq (tl1 bk_10)
/-- Kernel trajectory certificate `(m = 256, r = 14)`. -/
theorem rkmTraj_m256_r14 : rkmEvalT16Lo12 256 32 14 [1, 1] [47833196, 993174] [17, 2]
  rkmMasks_m256_r14 = rkmRow_m256_r14 := bh0_eq (tl1 bk_0)
/-- Kernel trajectory certificate `(m = 2, r = 28)`. -/
theorem rkmTraj_m2_r28 : rkmEvalT16Lo12 2 4096 28 [2, 4, 8, 16, 21, 21, 21] [42553875, 30106097,
  34500000, 24395184, 45689222, 10463252, 3800619] [2, 2, 4, 5, 11, 3, 1] rkmMasks_m2_r28 =
  rkmRow_m2_r28 := bh0_eq (tl1 bk_7)
/-- Kernel trajectory certificate `(m = 64, r = 14)`. -/
theorem rkmTraj_m64_r14 : rkmEvalT16Lo12 64 128 14 [1, 1, 1] [94702425, 4684372, 2674840] [16, 2, 2]
  rkmMasks_m64_r14 = rkmRow_m64_r14 := bh0_eq (tl1 bk_1)
/-- Kernel trajectory certificate `(m = 512, r = 22)`. -/
theorem rkmTraj_m512_r22 : rkmEvalT16Lo12 512 16 22 [1, 1] [33967692, 704465] [26, 2]
  rkmMasks_m512_r22 = rkmRow_m512_r22 := bh0_eq (tl1 bk_8)
/-- Kernel trajectory certificate `(m = 4, r = 17)`. -/
theorem rkmTraj_m4_r17 : rkmEvalT16Lo12 4 2048 17 [1, 2, 4, 8, 8, 8, 8, 8] [47742671, 50597482,
  54581000, 33184522, 34863899, 10162843, 4149193, 1934352] [2, 3, 5, 5, 5, 2, 1, 1] rkmMasks_m4_r17
  = rkmRow_m4_r17 := bh0_eq (tl2 bk_18)
/-- Kernel trajectory certificate `(m = 64, r = 19)`. -/
theorem rkmTraj_m64_r19 : rkmEvalT16Lo12 64 128 19 [1, 1, 1] [101746969, 2927294, 654772] [24, 2, 2]
  rkmMasks_m64_r19 = rkmRow_m64_r19 := bh0_eq (tl1 bk_20)
/-- Kernel trajectory certificate `(m = 8, r = 29)`. -/
theorem rkmTraj_m8_r29 : rkmEvalT16Lo12 8 1024 29 [1, 3] [80107915, 77247778] [6, 13]
  rkmMasks_m8_r29 = rkmRow_m8_r29 := bh0_eq (tl1 bk_2)
/-- Kernel trajectory certificate `(m = 128, r = 19)`. -/
theorem rkmTraj_m128_r19 : rkmEvalT16Lo12 128 64 19 [1, 1] [69709551, 1443054] [23, 2]
  rkmMasks_m128_r19 = rkmRow_m128_r19 := bh0_eq (tl1 bk_3)
/-- Krotov trajectory `(m = 2, r = 96)`. -/
theorem rkmTrajPack_m2_r96 : rkmEvalT16Lo12 2 4096 96 [2,4,12,27,48,84,84,84]
  [17717489,17819133,20160138,17506968,21912968,19272818,8402594,4623819] [2,3,7,11,22,28,13,7]
  rkmMasksPack_m2_r96 = rkmRowPack_m2_r96 :=
    bhW_eq bk_2 (wSkip (wSkip (wSkip (wSkip (wCons (bSlideChk_sound bk_12) (wCons (bSlideChk_sound
      bk_3) wNil))))))
/-- Krotov trajectory `(m = 2, r = 4)`. -/
theorem rkmTrajPack_m2_r4 : rkmEvalT16Lo12 2 4096 4 [1,2,3,3,3,3,3,3]
  [132484861,156761143,55690312,46369939,11922464,6935030,2306269,3366332] [1,2,1,1,1,1,1,1]
  rkmMasksPack_m2_r4 = rkmRowPack_m2_r4 := bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21))))))
/-- Krotov trajectory `(m = 64, r = 63)`. -/
theorem rkmTrajPack_m64_r63 : rkmEvalT16Lo12 64 128 63 [2,2,2,2,2,2,2,2]
  [21406613,18525226,9415540,15835452,5620185,3508488,4777773,2294496] [19,16,9,14,5,3,5,2]
  rkmMasksPack_m64_r63 = rkmRowPack_m64_r63 :=
    bhW_eq bk_8 (wCons (bSlideChk_sound (tl1 bk_18)) (wCons (bSlideChk_sound bk_20) wNil))
/-- Krotov trajectory `(m = 4, r = 52)`. -/
theorem rkmTrajPack_m4_r52 : rkmEvalT16Lo12 4 2048 52 [1,1,1,1,1,1,1,1]
  [11415517,13843742,29195765,14331851,2902095,15974666,23788,8624794] [1,1,2,1,1,1,1,1]
  rkmMasksPack_m4_r52 = rkmRowPack_m4_r52 := bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21))))))
/-- Krotov trajectory `(m = 64, r = 55)`. -/
theorem rkmTrajPack_m64_r55 : rkmEvalT16Lo12 64 128 55 [1,1,1,1,1,1,1,1]
  [49204236,38015319,15750537,16352668,14072029,7914853,3708183,7054101] [24,19,8,8,7,4,2,4]
  rkmMasksPack_m64_r55 = rkmRowPack_m64_r55 :=
    bhW_eq bk_1 (wCons (bSlideChk_sound (tl1 bk_17)) wNil)
/-- Krotov trajectory `(m = 2, r = 22)`. -/
theorem rkmTrajPack_m2_r22 : rkmEvalT16Lo12 2 4096 22 [1,2,4] [53822158,47445742,60885837] [1,2,4]
  rkmMasksPack_m2_r22 = rkmRowPack_m2_r22 :=
    bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21)))))))
/-- Krotov trajectory `(m = 64, r = 51)`. -/
theorem rkmTrajPack_m64_r51 : rkmEvalT16Lo12 64 128 51 [1,1,1,1,1,1]
  [36410557,48422966,14415708,19253297,15576237,7147668] [17,22,7,9,8,4] rkmMasksPack_m64_r51 =
  rkmRowPack_m64_r51 := bhW_eq bk_10 (wSkip (wCons (bSlideChk_sound (tl1 bk_13)) wNil))
/-- Krotov trajectory `(m = 8, r = 5)`. -/
theorem rkmTrajPack_m8_r5 : rkmEvalT16Lo12 8 1024 5 [1,1,1,1,1,1,1,1]
  [72488919,72274087,72099027,28688427,32852602,11518981,12299711,9486455] [2,2,2,1,1,1,1,1]
  rkmMasksPack_m8_r5 = rkmRowPack_m8_r5 := bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21)))))))
/-- Krotov trajectory `(m = 64, r = 42)`. -/
theorem rkmTrajPack_m64_r42 : rkmEvalT16Lo12 64 128 42 [1,1,1,1,1,1,1,1]
  [31988323,25576932,25670166,14479826,10514772,5872390,6654597,5120627] [13,10,10,6,5,3,3,2]
  rkmMasksPack_m64_r42 = rkmRowPack_m64_r42 := bh0_eq bk_11
/-- Krotov trajectory `(m = 4, r = 7)`. -/
theorem rkmTrajPack_m4_r7 : rkmEvalT16Lo12 4 2048 7 [1,2,3,3,3,3,3,3]
  [125225276,113107360,49480269,35797624,8209672,1713130,3810038,2114757] [3,3,2,2,1,1,1,1]
  rkmMasksPack_m4_r7 = rkmRowPack_m4_r7 :=
    bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21))))))))
/-- Krotov trajectory `(m = 64, r = 36)`. -/
theorem rkmTrajPack_m64_r36 : rkmEvalT16Lo12 64 128 36 [1,1,1,1,1,1,1,1]
  [31584809,34748387,14265954,13299519,9440493,5207603,5880636,4510596] [11,12,5,5,4,2,3,2]
  rkmMasksPack_m64_r36 = rkmRowPack_m64_r36 := bh0_eq bk_18
/-- Krotov trajectory `(m = 8, r = 9)`. -/
theorem rkmTrajPack_m8_r9 : rkmEvalT16Lo12 8 1024 9 [1,2,2,2]
  [145040161,87834299,29407999,12734384] [5,5,2,1] rkmMasksPack_m8_r9 = rkmRowPack_m8_r9 :=
    bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21))))))))
/-- Krotov trajectory `(m = 32, r = 34)`. -/
theorem rkmTrajPack_m32_r34 : rkmEvalT16Lo12 32 256 34 [1,2] [61244808,73429251] [13,24]
  rkmMasksPack_m32_r34 = rkmRowPack_m32_r34 := bh0_eq (tl1 bk_15)
/-- Krotov trajectory `(m = 4, r = 11)`. -/
theorem rkmTrajPack_m4_r11 : rkmEvalT16Lo12 4 2048 11 [1,3,4,4,4]
  [98033563,71531085,40173810,52779552,35226421] [3,4,3,3,2] rkmMasksPack_m4_r11 =
  rkmRowPack_m4_r11 := bh0_eq (tl2 (tl2 bk_21))
/-- Krotov trajectory `(m = 16, r = 31)`. -/
theorem rkmTrajPack_m16_r31 : rkmEvalT16Lo12 16 512 31 [1,3,3,3]
  [69336291,88833651,12764193,4274313] [8,23,4,2] rkmMasksPack_m16_r31 = rkmRowPack_m16_r31 :=
    bh0_eq (tl1 bk_12)
/-- Krotov trajectory `(m = 2, r = 13)`. -/
theorem rkmTrajPack_m2_r13 : rkmEvalT16Lo12 2 4096 13 [1,2,4,8,12,12,12,12]
  [49234218,45850523,56107754,57045033,30701500,23680833,5342198,7918713] [1,2,3,4,3,2,1,1]
  rkmMasksPack_m2_r13 = rkmRowPack_m2_r13 := bh0_eq (tl2 bk_17)
/-- Krotov trajectory `(m = 64, r = 26)`. -/
theorem rkmTrajPack_m64_r26 : rkmEvalT16Lo12 64 128 26 [1,1,1,1,1,1,1,1]
  [23794117,30975092,23464264,8465502,7193715,7203624,5429453,3696269] [7,9,7,3,2,2,2,1]
  rkmMasksPack_m64_r26 = rkmRowPack_m64_r26 := bh0_eq (tl1 bk_11)
/-- Krotov trajectory `(m = 8, r = 14)`. -/
theorem rkmTrajPack_m8_r14 : rkmEvalT16Lo12 8 1024 14 [1,2,3,3,3]
  [90375235,55550855,69299269,22098489,7267274] [4,4,6,2,1] rkmMasksPack_m8_r14 = rkmRowPack_m8_r14
  := bh0_eq (tl1 bk_21)
/-- Krotov trajectory `(m = 32, r = 52)`. -/
theorem rkmTrajPack_m32_r52 : rkmEvalT16Lo12 32 256 52 [1,1,1,1,1,1,1,1]
  [13739615,13261486,13162483,9041704,305338,9656,7362627,7761225] [4,4,4,3,1,1,3,3]
  rkmMasksPack_m32_r52 = rkmRowPack_m32_r52 := bh0_eq (tl1 bk_6)
/-- Krotov trajectory `(m = 4, r = 14)`. -/
theorem rkmTrajPack_m4_r14 : rkmEvalT16Lo12 4 2048 14 [1,2,4,6,6,6,6,6]
  [74083796,53163912,57934292,37266824,28831835,15290977,3879727,2222242] [2,3,4,4,3,2,1,1]
  rkmMasksPack_m4_r14 = rkmRowPack_m4_r14 := bh0_eq bk_21
/-- Krotov trajectory `(m = 32, r = 20)`. -/
theorem rkmTrajPack_m32_r20 : rkmEvalT16Lo12 32 256 20 [1,1,1,1,1,1,1,1]
  [46345889,40827264,30374918,22237385,10786560,10792204,5550246,5066751] [7,6,5,4,2,2,1,1]
  rkmMasksPack_m32_r20 = rkmRowPack_m32_r20 := bh0_eq (tl1 bk_5)
/-- Krotov trajectory `(m = 2, r = 20)`. -/
theorem rkmTrajPack_m2_r20 : rkmEvalT16Lo12 2 4096 20 [1,2,4,8,15,15,15]
  [27825880,30551985,39137224,47029691,66598142,9385805,6742027] [1,1,2,4,9,2,1]
  rkmMasksPack_m2_r20 = rkmRowPack_m2_r20 := bh0_eq (tl2 (tl2 bk_20))
/-- Krotov trajectory `(m = 8, r = 60)`. -/
theorem rkmTrajPack_m8_r60 : rkmEvalT16Lo12 8 1024 60 [1,1,1,1,8,8,8,8]
  [2695477,28252591,18956481,22281061,1940877,6434092,187654,1830552] [1,3,2,3,1,4,1,1]
  rkmMasksPack_m8_r60 = rkmRowPack_m8_r60 := bh0_eq (tl1 bk_4)
/-- Krotov trajectory `(m = 16, r = 112)`. -/
theorem rkmTrajPack_m16_r112 : rkmEvalT16Lo12 16 512 112 [1,1,1,1,1,1,1,1]
  [16028302,12118838,6489024,8690404,461408,430030,6340119,21770666] [4,3,2,3,1,1,2,6]
  rkmMasksPack_m16_r112 = rkmRowPack_m16_r112 := bh0_eq (tl1 (tl2 bk_20))
end
end QuantumComputation.Specs.DickeSol
