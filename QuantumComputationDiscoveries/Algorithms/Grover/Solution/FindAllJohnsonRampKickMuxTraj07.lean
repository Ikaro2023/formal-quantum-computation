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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxTraj05
/-
# Multi-Segment `T_16` Trajectory Part `07` (`FindAllJohnsonRampKickMuxTraj07`)

Certified kernel trajectory evaluations (`30` rows, `37988` substep-coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Prefix-kick masks for `(m = 2, r = 6)`. -/
def rkmMasks_m2_r6 : List (List Bool) := [
  [], [], [true], [false, true, true], [false, false, false, true], [], [true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 6)`. -/
def rkmRow_m2_r6 : List ℕ := [
  113120912, 525664370, 1586512176, 3372264167, 430560496508, 563840745828]
/-- Prefix-kick masks for `(m = 4, r = 12)`. -/
def rkmMasks_m4_r12 : List (List Bool) := [
  [], [], [true, true, true, true, false, true],
  [true, false, true, false, true, true, false, true, true],
  [false, true, false, false, false, false, true, false, false, true],
  [true, false, true, true, true, false, false, true, false, false, true],
  [false, false, false, false, false, true, true, true, true, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 12)`. -/
def rkmRow_m4_r12 : List ℕ := [
  176336, 6956380, 10751, 89595615, 1251208288, 1929033609, 212445990, 1589818811, 9491525692,
  70620643, 202160869665, 783197325765]
/-- Mask chunk for `(m = 4, r = 20)`. -/
def rkmMkP_m4_r20_s4_p0 : List Bool := [
  false, true, false, true, false, true, true, true, true, true, true, false, false, true, true,
  false, false, true, true]
/-- Prefix-kick masks for `(m = 4, r = 20)`. -/
def rkmMasks_m4_r20 : List (List Bool) := [
  [], [], [], [], rkmMkP_m4_r20_s4_p0,
  [false, false, true, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 20)`. -/
def rkmRow_m4_r20 : List ℕ := [
  21, 0, 2538, 14028, 6567, 448249, 53270, 17399857, 4433504, 448151, 256103823, 3898079,
  2394303926, 3044933, 13877202818, 267006990, 56597365848, 14631669933, 164729420183,
  747217177008]
/-- Mask chunk for `(m = 4, r = 28)`. -/
def rkmMkP_m4_r28_s4_p0 : List Bool := [
  true, true, true, false, false, true, false, true, true, true, true, false, false, true, true,
  false, false, false, false, true, true, false, false, false, true, true]
/-- Mask chunk for `(m = 4, r = 28)`. -/
def rkmMkP_m4_r28_s5_p0 : List Bool := [
  false, false, false, true, false, true, true, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true]
/-- Prefix-kick masks for `(m = 4, r = 28)`. -/
def rkmMasks_m4_r28 : List (List Bool) := [
  [], [], [], [], rkmMkP_m4_r28_s4_p0, rkmMkP_m4_r28_s5_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 28)`. -/
def rkmRow_m4_r28 : List ℕ := [
  0, 1, 2, 4, 794, 28, 97, 2322, 59582, 179170, 104969, 1715232, 871442, 21361240, 3407707,
  78237278, 298132944, 754746673, 132326821, 4721426654, 518972167, 12011879042, 489361768,
  1082443190, 45134281258, 1206051942, 186231616250, 747312820893]
/-- Mask chunk for `(m = 4, r = 36)`. -/
def rkmMkP_m4_r36_s4_p0 : List Bool := [
  true, true, false, false, true, false, true, true, true, true, true, false, false, true, false,
  true, false, false, false, false, true, true, true, false, false, false, false, false, true]
/-- Mask chunk for `(m = 4, r = 36)`. -/
def rkmMkP_m4_r36_s5_p0 : List Bool := [
  false, false, false, false, false, false, true, false, false, false, false, false, true, true,
  true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 4, r = 36)`. -/
def rkmMasks_m4_r36 : List (List Bool) := [
  [], [], [], [], rkmMkP_m4_r36_s4_p0, rkmMkP_m4_r36_s5_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 36)`. -/
def rkmRow_m4_r36 : List ℕ := [
  25, 0, 9, 7, 13, 0, 54, 585, 13, 5524, 2527, 3076, 743928, 435938, 1586331, 2341209, 35408219,
  513911, 214189399, 25394427, 500312077, 338608488, 359883186, 5819176029, 4868282185,
  3335752562, 39819423046, 12344032275, 18426881859, 188432982118, 333340565744, 258823842806,
  106440136037, 23971009019, 2771055221, 127431336]
/-- Prefix-kick masks for `(m = 8, r = 9)`. -/
def rkmMasks_m8_r9 : List (List Bool) := [
  [], [false, true, true, false, false, true, true],
  [true, false, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 9)`. -/
def rkmRow_m8_r9 : List ℕ := [
  2857888, 15958884, 183614185, 440933138, 6753176, 5153005230, 287406989, 81621944543,
  912287471546]
/-- Mask chunk for `(m = 8, r = 24)`. -/
def rkmMkP_m8_r24_s3_p0 : List Bool := [
  true, true, false, false, true, true, true, true, true, true, true, true, true, true, true,
  false, false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 8, r = 24)`. -/
def rkmMkP_m8_r24_s4_p0 : List Bool := [
  false, false, false, true, true, true, true, false, false, false, true, true, false, true,
  false, true, true, false, true]
/-- Prefix-kick masks for `(m = 8, r = 24)`. -/
def rkmMasks_m8_r24 : List (List Bool) := [
  [], [], [], rkmMkP_m8_r24_s3_p0, rkmMkP_m8_r24_s4_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 24)`. -/
def rkmRow_m8_r24 : List ℕ := [
  0, 3, 0, 69, 572, 264, 17112, 30790, 322914, 15837, 1735275, 22889405, 2802218, 2479407,
  238856478, 107514715, 2024334618, 18414073, 11404815942, 98251942, 36743690619, 11364880519,
  78157051347, 859811895491]
/-- Mask chunk for `(m = 8, r = 44)`. -/
def rkmMkP_m8_r44_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, false, true, false, false, true, true, false, true, false, false, false,
  true, true, false, false, true, true, false, false, true, true, false, false, false, true, true]
/-- Mask chunk for `(m = 8, r = 44)`. -/
def rkmMkP_m8_r44_s5_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, true, false, true, true,
  false, true, false, true, true, false, false, true, false, false, true, false, false, true,
  false, true, false, true, false, true, false, true, false, true]
/-- Prefix-kick masks for `(m = 8, r = 44)`. -/
def rkmMasks_m8_r44 : List (List Bool) := [
  [], [], [], [], rkmMkP_m8_r44_s4_p0, rkmMkP_m8_r44_s5_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 44)`. -/
def rkmRow_m8_r44 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 28, 3, 2753, 47, 977, 1022, 52288, 125825, 161,
  330022, 7014089, 405407, 3444977, 13288018, 15414993, 64974416, 52077918, 295319255, 187467377,
  1343960892, 664423394, 5147237337, 1157423743, 8538304526, 1081985252, 1335210, 42339755367,
  192395717, 120379243291, 818514014426]
/-- Mask chunk for `(m = 16, r = 29)`. -/
def rkmMkP_m16_r29_s1_p0 : List Bool := [
  false, false, false, false, false, true, true, false, false, true, false, false, false, true,
  true, false, false, true, true, false, false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 16, r = 29)`. -/
def rkmMkP_m16_r29_s2_p0 : List Bool := [
  false, false, true, true, true, true, false, false, false, true, false, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 29)`. -/
def rkmMasks_m16_r29 : List (List Bool) := [[], rkmMkP_m16_r29_s1_p0, rkmMkP_m16_r29_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 29)`. -/
def rkmRow_m16_r29 : List ℕ := [
  0, 0, 0, 0, 0, 14, 8, 65, 368, 38, 351, 2009, 23101, 145046, 1121548, 3063927, 17029732,
  30966791, 152546733, 191618331, 917883529, 718307067, 3180296310, 2148203805, 211631626,
  15468203989, 37248285, 42428100037, 934493606813]
/-- Mask chunk for `(m = 16, r = 128)`. -/
def rkmMkP_m16_r128_s2_p0 : List Bool := [
  true, false, true, true, true, true, false, false, true, true, true, true, true, true, true,
  false, false, false, false, true, false, true, true, true, true, true, true, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, true]
/-- Mask chunk for `(m = 16, r = 128)`. -/
def rkmMkP_m16_r128_s3_p0 : List Bool := [
  true, false, true, true, true, true, false, false, false, false, true, false, true, false,
  false, false, true, true, false, true, true, false, false, true, true, true, false, false, true,
  true, false, true, true, true, false, false, true, true, true, false, false, false, true, false,
  true, true, false, true, true, true, true, true, true, false, false, false, true, false, true,
  true, true, false, false, false]
/-- Mask chunk for `(m = 16, r = 128)`. -/
def rkmMkP_m16_r128_s3_p1 : List Bool := [
  false, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, false, false, false, false, false,
  false, false, false, false, false, false, true, true]
/-- Mask chunk for `(m = 16, r = 128)`. -/
def rkmMkP_m16_r128_s4_p0 : List Bool := [
  true, false, false, false, false, true, false, true, true, false, false, true, true, false,
  true, false, true, false, true, false, true, false, true, false, false, true, true, false,
  false, false, true, true, false, true, true, false, false, true, true, false, false, false,
  false, false, false, false, true, false, false, false, true, false, false, true, true, false,
  true, true, false, false, true, true, false, false]
/-- Mask chunk for `(m = 16, r = 128)`. -/
def rkmMkP_m16_r128_s4_p1 : List Bool := [
  true, true, false, false, true, true, false, false, true, true, false, false, true, true, true,
  false, true, true, false, true, true, false, true, false, true, true, true, false, false, false,
  true, true, true, false, false, false, false, true, true, true, true, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, true, true, true]
/-- Mask chunk for `(m = 16, r = 128)`. -/
def rkmMkP_m16_r128_s4_p2 : List Bool := [true]
/-- Mask chunk for `(m = 16, r = 128)`. -/
def rkmMkP_m16_r128_s5_p0 : List Bool := [
  false, true, false, true, true, false, false, false, false, false, false, false, false, true,
  true, true, false, false, false, false, true, false, true, false, false, false, false, true,
  true, true, false, false, false, false, false, false, true, false, false, true, true, false,
  false, false, false, true, true, false, false, false, false, false, false, true, false, false,
  false, false, false, false, true, false, true, false]
/-- Mask chunk for `(m = 16, r = 128)`. -/
def rkmMkP_m16_r128_s5_p1 : List Bool := [
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, true, false, true,
  true, false, false, true, false, false, true, true, false, false, true, true, false, false,
  true, true, false, false, true, true]
/-- Mask chunk for `(m = 16, r = 128)`. -/
def rkmMkP_m16_r128_s6_p0 : List Bool := [
  true, false, true, false, false, false, false, false, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 16, r = 128)`. -/
def rkmMkP_m16_r128_s6_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, false, true, false, true, true, false,
  false, false, false, false, false, false, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 128)`. -/
def rkmMasks_m16_r128 : List (List Bool) := [
  [], [false, true, true], rkmMkP_m16_r128_s2_p0, rkmMkP_m16_r128_s3_p0 ++ rkmMkP_m16_r128_s3_p1,
  rkmMkP_m16_r128_s4_p0 ++ rkmMkP_m16_r128_s4_p1 ++ rkmMkP_m16_r128_s4_p2,
  rkmMkP_m16_r128_s5_p0 ++ rkmMkP_m16_r128_s5_p1, rkmMkP_m16_r128_s6_p0 ++ rkmMkP_m16_r128_s6_p1,
  []]
/-- Row chunk `0` `(m = 16, r = 128)`. -/
def rkmRowP_m16_r128_p0 : List ℕ := [
  481781, 8085, 1965196, 170152, 8437, 1334345, 5447972, 1758719, 63305, 4724883, 56752, 4067722,
  6150402, 29611, 6297422, 1884862, 12941869, 8189, 871505, 227219, 3815122, 27518, 2641989,
  2133079, 1614762, 1170108, 2667148, 482528, 5544813, 2884957, 964042, 286, 899741, 138623,
  3564368, 981937, 194996, 50755, 39407, 9707573, 7782524, 20299952, 6759123, 19112375, 3678420,
  1520497, 386100, 3158684, 13850790, 1492921, 8019253, 10156906, 53668265, 69216740, 59114174,
  1125340, 1208594, 18360414, 28409681, 19310107, 2552062, 11501556, 8577589, 1093178]
/-- Row chunk `1` `(m = 16, r = 128)`. -/
def rkmRowP_m16_r128_p1 : List ℕ := [
  1575831, 12371939, 5629650, 14626461, 74353328, 31541807, 7896187, 101712728, 151350408,
  62062409, 4744, 376085376, 121909346, 134528737, 133606662, 267332749, 350038076, 1045215,
  187770660, 580247084, 62510131, 188873111, 838827313, 762961544, 11206661, 113119758, 150700705,
  99586231, 546524232, 248968749, 85217690, 897821273, 576312204, 57004052, 5175095, 100967882,
  132334145, 7845595, 109026359, 2064541, 191665176, 481885375, 202348641, 150691880, 563584287,
  89632537, 16484889, 5542535408, 2452443, 26425545, 64900470, 5700972715, 88394575, 537342531,
  468268550, 3195288205, 387975064, 10620093256, 697827020, 8728131727, 22257703277, 12170891,
  31553561014, 900348520461]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 128)`. -/
def rkmRow_m16_r128 : List ℕ := rkmRowP_m16_r128_p0 ++ rkmRowP_m16_r128_p1
/-- Prefix-kick masks for `(m = 32, r = 5)`. -/
def rkmMasks_m32_r5 : List (List Bool) := [
  [], [], [false, false, false, true, true, true], [true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 5)`. -/
def rkmRow_m32_r5 : List ℕ := [2900854, 143087, 23094744, 35918775939, 964055034760]
/-- Prefix-kick masks for `(m = 32, r = 9)`. -/
def rkmMasks_m32_r9 : List (List Bool) := [
  [false, true, true, true, true, true], [false, true, false, true, true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 9)`. -/
def rkmRow_m32_r9 : List ℕ := [
  21, 61818, 1955639, 1132198, 54480288, 495362382, 70184310, 23019286249, 976357537007]
/-- Mask chunk for `(m = 32, r = 26)`. -/
def rkmMkP_m32_r26_s0_p0 : List Bool := [
  false, true, true, true, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true]
/-- Mask chunk for `(m = 32, r = 26)`. -/
def rkmMkP_m32_r26_s1_p0 : List Bool := [
  false, true, true, true, false, false, true, false, true, false, true, true, false, true, false,
  false, true, true, false, false, false, true, true]
/-- Prefix-kick masks for `(m = 32, r = 26)`. -/
def rkmMasks_m32_r26 : List (List Bool) := [rkmMkP_m32_r26_s0_p0, rkmMkP_m32_r26_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 26)`. -/
def rkmRow_m32_r26 : List ℕ := [
  0, 0, 0, 6, 21, 235, 1673, 11147, 53929, 243547, 1027354, 3948745, 12944594, 33449721, 62549741,
  81425234, 42817460, 15441455, 611153471, 2808509907, 4203448723, 1269038912, 5941119228,
  21689462301, 31175542358, 932047809798]
/-- Mask chunk for `(m = 64, r = 16)`. -/
def rkmMkP_m64_r16_s1_p0 : List Bool := [
  false, false, false, false, false, false, true, true, false, false, false, true, true]
/-- Mask chunk for `(m = 64, r = 16)`. -/
def rkmMkP_m64_r16_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, true, false, false, true]
/-- Mask chunk for `(m = 64, r = 16)`. -/
def rkmMkP_m64_r16_s3_p0 : List Bool := [
  false, false, false, false, false, false, true, false, true, true, false, false, true, true,
  true]
/-- Mask chunk for `(m = 64, r = 16)`. -/
def rkmMkP_m64_r16_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, true, true,
  true]
/-- Prefix-kick masks for `(m = 64, r = 16)`. -/
def rkmMasks_m64_r16 : List (List Bool) := [
  [], rkmMkP_m64_r16_s1_p0, rkmMkP_m64_r16_s2_p0, rkmMkP_m64_r16_s3_p0, rkmMkP_m64_r16_s4_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 16)`. -/
def rkmRow_m64_r16 : List ℕ := [
  0, 0, 0, 4, 0, 72, 154, 98307, 250347, 1449122, 3671, 29670781, 50364234, 41215660, 12521029987,
  987355917480]
/-- Mask chunk for `(m = 64, r = 32)`. -/
def rkmMkP_m64_r32_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true]
/-- Mask chunk for `(m = 64, r = 32)`. -/
def rkmMkP_m64_r32_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, true, false, true, false, false, true, false,
  true, false, false, true, false, false, false, false, true, true]
/-- Mask chunk for `(m = 64, r = 32)`. -/
def rkmMkP_m64_r32_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, true, true, false, false, true, false,
  false, false, false, false, true, true, false, true, true, true, true]
/-- Mask chunk for `(m = 64, r = 32)`. -/
def rkmMkP_m64_r32_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, false, false, false, false,
  true, false, true, false, true, true, true, false, false, true, false, true, true]
/-- Mask chunk for `(m = 64, r = 32)`. -/
def rkmMkP_m64_r32_s4_p0 : List Bool := [
  false, false, false, false, false, false, true, false, true, false, true, false, false, true,
  true, false, true, true, false, true, false, false, true, true, false, false, false, true, true]
/-- Mask chunk for `(m = 64, r = 32)`. -/
def rkmMkP_m64_r32_s5_p0 : List Bool := [
  false, false, false, false, false, false, false, false, true, false, false, false, true, false,
  true, false, false, true, false, true, false, false, true, false, false, false, true, true,
  true, true]
/-- Mask chunk for `(m = 64, r = 32)`. -/
def rkmMkP_m64_r32_s6_p0 : List Bool := [
  false, false, false, false, false, false, true, false, false, false, true, false, true, false,
  true, false, true, false, true, false, true, false, false, true, false, true, false, true, true,
  true, true]
/-- Prefix-kick masks for `(m = 64, r = 32)`. -/
def rkmMasks_m64_r32 : List (List Bool) := [
  rkmMkP_m64_r32_s0_p0, rkmMkP_m64_r32_s1_p0, rkmMkP_m64_r32_s2_p0, rkmMkP_m64_r32_s3_p0,
  rkmMkP_m64_r32_s4_p0, rkmMkP_m64_r32_s5_p0, rkmMkP_m64_r32_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 32)`. -/
def rkmRow_m64_r32 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 20, 36, 125, 11241, 20936, 29589, 13247, 2318521,
  1392595, 22540, 1744835, 13319258, 2637378, 50975530, 185136621, 145275963, 9317140394,
  990279960594]
/-- Prefix-kick masks for `(m = 128, r = 4)`. -/
def rkmMasks_m128_r4 : List (List Bool) := [[false, false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 4)`. -/
def rkmRow_m128_r4 : List ℕ := [5, 242063641, 40245861982, 959512068819]
/-- Prefix-kick masks for `(m = 128, r = 10)`. -/
def rkmMasks_m128_r10 : List (List Bool) := [
  [false, false, false, false, false, true, true, true],
  [false, false, false, false, true, false, true, true, false, true, true],
  [false, false, true, false, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 10)`. -/
def rkmRow_m128_r10 : List ℕ := [
  0, 0, 0, 349, 5542, 773060, 17639, 1750015, 16555104996, 983442348263]
/-- Mask chunk for `(m = 128, r = 12)`. -/
def rkmMkP_m128_r12_s1_p0 : List Bool := [
  false, false, false, true, true, false, true, false, true, true, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 12)`. -/
def rkmMasks_m128_r12 : List (List Bool) := [
  [false, false, false, false, false, false, false, true, true, true], rkmMkP_m128_r12_s1_p0,
  [false, false, false, false, true, false, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 12)`. -/
def rkmRow_m128_r12 : List ℕ := [
  0, 0, 0, 0, 0, 1361, 10281, 1710377, 158800, 4259361, 13997434275, 985996425371]
/-- Mask chunk for `(m = 128, r = 14)`. -/
def rkmMkP_m128_r14_s1_p0 : List Bool := [
  true, false, true, false, false, true, false, true, false, false, true, false, false, true,
  true]
/-- Prefix-kick masks for `(m = 128, r = 14)`. -/
def rkmMasks_m128_r14 : List (List Bool) := [
  [true, false, true, false, true, false, true, true, true, true, true], rkmMkP_m128_r14_s1_p0,
  []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 14)`. -/
def rkmRow_m128_r14 : List ℕ := [
  0, 0, 0, 0, 0, 0, 261, 21906, 27592, 3255441, 48415973, 19081038, 12192418921, 987736778675]
/-- Mask chunk for `(m = 128, r = 17)`. -/
def rkmMkP_m128_r17_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, true, false,
  false, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 17)`. -/
def rkmMasks_m128_r17 : List (List Bool) := [rkmMkP_m128_r17_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 17)`. -/
def rkmRow_m128_r17 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 36, 1260, 17713, 648496, 5059925, 126937610, 64386081, 10301806916,
  989501141711]
/-- Mask chunk for `(m = 128, r = 31)`. -/
def rkmMkP_m128_r31_s0_p0 : List Bool := [
  false, false, false, false, false, false, true, true, true, false, false, true, true, false,
  false, false, true, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 128, r = 31)`. -/
def rkmMkP_m128_r31_s1_p0 : List Bool := [
  false, false, true, false, true, false, false, true, false, false, true, false, true, false,
  true, true, true, false, true, false, true, false, true, true, false, false, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 31)`. -/
def rkmMasks_m128_r31 : List (List Bool) := [rkmMkP_m128_r31_s0_p0, rkmMkP_m128_r31_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 31)`. -/
def rkmRow_m128_r31 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 230, 2311, 33604, 164639, 11465, 1312187,
  2066869, 11037979, 4697020, 6618729, 863236178, 3976695443, 6599981643, 988534140954]
/-- Prefix-kick masks for `(m = 256, r = 7)`. -/
def rkmMasks_m256_r7 : List (List Bool) := [
  [false, false, true, true, true], [false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 7)`. -/
def rkmRow_m256_r7 : List ℕ := [0, 0, 10509, 408, 36238558, 22621624926, 977342125497]
/-- Mask chunk for `(m = 256, r = 19)`. -/
def rkmMkP_m256_r19_s0_p0 : List Bool := [
  false, true, true, false, false, false, true, true, false, false, true, true, false, true, true,
  false, false, true, true, true]
/-- Prefix-kick masks for `(m = 256, r = 19)`. -/
def rkmMasks_m256_r19 : List (List Bool) := [rkmMkP_m256_r19_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 19)`. -/
def rkmRow_m256_r19 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 137, 2263, 286599, 38946920, 334211007, 8682466356,
  990944086305]
/-- Mask chunk for `(m = 256, r = 24)`. -/
def rkmMkP_m256_r24_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, true, true, true]
/-- Mask chunk for `(m = 256, r = 24)`. -/
def rkmMkP_m256_r24_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, false, true, false, true, true, false, true, true]
/-- Prefix-kick masks for `(m = 256, r = 24)`. -/
def rkmMasks_m256_r24 : List (List Bool) := [rkmMkP_m256_r24_s0_p0, rkmMkP_m256_r24_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 24)`. -/
def rkmRow_m256_r24 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1785, 1186, 3182, 3392014, 51353316, 144842122,
  6825232721, 992975173078]
/-- Prefix-kick masks for `(m = 512, r = 14)`. -/
def rkmMasks_m512_r14 : List (List Bool) := [
  [false, false, false, false, false, false, false, false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 14)`. -/
def rkmRow_m512_r14 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 469, 70419, 1103809, 2900257, 11222874092, 988773050636]
/-- Mask chunk for `(m = 512, r = 20)`. -/
def rkmMkP_m512_r20_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true]
/-- Mask chunk for `(m = 512, r = 20)`. -/
def rkmMkP_m512_r20_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 512, r = 20)`. -/
def rkmMasks_m512_r20 : List (List Bool) := [rkmMkP_m512_r20_s0_p0, rkmMkP_m512_r20_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 20)`. -/
def rkmRow_m512_r20 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 31, 1626, 21440, 314, 2883339, 12332490, 7951715729,
  992033044414]
/-- Mask chunk for `(m = 512, r = 48)`. -/
def rkmMkP_m512_r48_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, true]
/-- Mask chunk for `(m = 512, r = 48)`. -/
def rkmMkP_m512_r48_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  true, false, false, false, false, true, true]
/-- Prefix-kick masks for `(m = 512, r = 48)`. -/
def rkmMasks_m512_r48 : List (List Bool) := [rkmMkP_m512_r48_s0_p0, rkmMkP_m512_r48_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 48)`. -/
def rkmRow_m512_r48 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 4, 361, 6640, 44725, 31883, 369531, 59446, 25473164, 39572299, 3525801058,
  996408638137]
/-- Prefix-kick masks for `(m = 1024, r = 8)`. -/
def rkmMasks_m1024_r8 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 8)`. -/
def rkmRow_m1024_r8 : List ℕ := [0, 0, 0, 6, 137272, 107103428, 19347807818, 980544951314]
/-- Prefix-kick masks for `(m = 1024, r = 31)`. -/
def rkmMasks_m1024_r31 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 31)`. -/
def rkmRow_m1024_r31 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 201, 3061, 1175724,
  50941355, 5059638910, 994888239077]
/-- Mask chunk for `(m = 1024, r = 64)`. -/
def rkmMkP_m1024_r64_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, true, true]
/-- Mask chunk for `(m = 1024, r = 64)`. -/
def rkmMkP_m1024_r64_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 1024, r = 64)`. -/
def rkmMasks_m1024_r64 : List (List Bool) := [
  [], rkmMkP_m1024_r64_s1_p0, rkmMkP_m1024_r64_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 64)`. -/
def rkmRow_m1024_r64 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 307, 7833, 173487,
  9108044, 8947009, 2508706197, 997473050545]
/-- Unpacks `j` LSB-first bits of `< 2 ^ 50` word `w` (`FindAllJohnsonRampKickMuxTraj07`). -/
def rkmWbTraj07 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWbTraj07 j (Nat.div w 2)
/-- Concatenates `50`-bit `< 2 ^ 50` chunks (final length `rem`) into a `List Bool` mask. -/
def rkmMaskWordsTraj07 : ℕ → List ℕ → List Bool
  | _, [] => []
  | rem, [w] => rkmWbTraj07 rem w
  | rem, w :: v :: ws => rkmWbTraj07 50 w ++ rkmMaskWordsTraj07 rem (v :: ws)
/-- Krotov masks `(m = 16, r = 96)`. -/
def rkmMasksPack_m16_r96 : List (List Bool) := [[],rkmWbTraj07 32 3221225475,
  rkmWbTraj07 45 30786325593856,rkmMaskWordsTraj07 36 [315851022578497,53888417792],
  rkmMaskWordsTraj07 46 [167960504021268,65970729356071],
  rkmMaskWordsTraj07 43 [357707815129387,7036978681173],
  rkmMaskWordsTraj07 45 [93803226857731,19814093426705],[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 96)`. -/
def rkmRowPack_m16_r96 : List ℕ := [34986,801675,13907,53021,541188,2461759,149286,93955,566451,
  41309,66201,6334416,7889103,2009637,45332,650299,136012,20874,173381,75394,53657,2490100,95222,
  36743,1211901,1900831,6089,661099,2965306,186430,1709040,24021,3232862,283642,562024,2391641,
  206445,3384130,24722,11819899,529659,412878,50228,14462837,2352,1699155,1258914,7913632,21588,
  9589605,15039079,5459897,1425060,9168982,26702524,2100815,9612642,20489656,1971932,265830462,
  929257,17240388,437606734,116032854,72177367,132136357,1199830887,1015720579,373775614,18408406,
  647878947,181567414,222367213,146346731,6582119,443934636,282105676,185195711,1392597285,
  11535090,1696415598,4475348,2973762850,105455713,2534658924,642700646,693867231,3600546754,
  17161182,9645336937,3273088,9185043069,24899123653,55071944,42019822962,894570105551]
/-- Krotov masks `(m = 16, r = 4)`. -/
def rkmMasksPack_m16_r4 : List (List Bool) := [[],rkmWbTraj07 1 1,rkmWbTraj07 5 29,rkmWbTraj07 3 4,
  []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 4)`. -/
def rkmRowPack_m16_r4 : List ℕ := [1899,68017304,49098744758,950833235057]
/-- Krotov masks `(m = 64, r = 62)`. -/
def rkmMasksPack_m64_r62 : List (List Bool) := [[],[],rkmWbTraj07 32 4168671717,
  rkmMaskWordsTraj07 1 [876187125197476,1],rkmMaskWordsTraj07 7 [178896462304577,115],
  rkmMaskWordsTraj07 9 [93841819585184,437],rkmMaskWordsTraj07 11 [364304573740368,1675],[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 62)`. -/
def rkmRowPack_m64_r62 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,1,7,40,308,1345,3511,6582,17934,345,7423,420805,299923,880965,3560184,2469,136364,
  3682763,141606013,51880580,115302471,219947725,600629816,1770976765,9227755,9451980120,
  987629425262]
/-- Krotov masks `(m = 4, r = 44)`. -/
def rkmMasksPack_m4_r44 : List (List Bool) := [[],[],[],[],[],rkmWbTraj07 4 11,rkmWbTraj07 4 11,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 44)`. -/
def rkmRowPack_m4_r44 : List ℕ := [12054983,5075109127,149011208219,845901366641]
/-- Krotov masks `(m = 32, r = 64)`. -/
def rkmMasksPack_m32_r64 : List (List Bool) := [[],rkmMaskWordsTraj07 11 [67862528,1456],
  rkmMaskWordsTraj07 14 [531277146706805,8192],rkmMaskWordsTraj07 11 [723869138794167,1586],
  rkmMaskWordsTraj07 13 [285230219996688,4694],rkmMaskWordsTraj07 13 [132000657865905,4098],
  rkmMaskWordsTraj07 10 [7938013535,512],[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 64)`. -/
def rkmRowPack_m32_r64 : List ℕ := [58329,244029,306909,22502,33601,16297,321965,63891,152656,34,
  84368,32048,410173,327938,82222,875790,79605,223087,388814,566122,408134,65712,128368,48602,
  48801,18234,34204,13,279251,84837,911715,1057979,92726,232718,59253,19805182,543,6679333,
  2180669,6245556,14083567,22291735,25050370,15453174,11027697,103216752,590493,10870781,37275716,
  223843083,1885529695,650209942,358315052,43182815,1165882897,2141760793,251566305,3266988514,
  19271857,6255411237,10183054862,13564386,19407313114,953851561505]
/-- Krotov masks `(m = 4, r = 4)`. -/
def rkmMasksPack_m4_r4 : List (List Bool) := [[],[],rkmWbTraj07 2 3,rkmWbTraj07 3 4,[],
  rkmWbTraj07 3 4,[],[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 4)`. -/
def rkmRowPack_m4_r4 : List ℕ := [274306110,44606493,142736235932,856739486546]
/-- Krotov masks `(m = 2, r = 64)`. -/
def rkmMasksPack_m2_r64 : List (List Bool) := [[],[],[],rkmWbTraj07 30 536871198,
  rkmMaskWordsTraj07 9 [562951975015966,268],rkmMaskWordsTraj07 11 [124849541704327,1024],
  rkmMaskWordsTraj07 9 [567668701997737,396],[]]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 64)`. -/
def rkmRowPack_m2_r64 : List ℕ := [11923,273054,131059,170047,104238,380507,211710,916787,170279,
  9226224,8511131,8377322,9914991,566675,9903856,24077825,48402138,12195446,120244,6527836,0,
  16228646,20283612,58752612,145567437,173488795,82609871,48535939,418378,13623869,9028240,
  21188352,209329825,409826442,570593094,42463620,287122213,1005522767,3010187,6931,148894430,
  770286872,168327133,155820465,255231050,163796599,1549731862,308832058,677497333,11048709,
  1748824956,1333941413,2293747769,1689807081,24707730,2052451723,52933838,14723740320,
  16513436174,1240949151,5290502369,239350533156,494429652131,211787162433]
/-- Krotov masks `(m = 32, r = 6)`. -/
def rkmMasksPack_m32_r6 : List (List Bool) := [[],[],[],[],rkmWbTraj07 3 7,rkmWbTraj07 4 9,
  rkmWbTraj07 5 17,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 6)`. -/
def rkmRowPack_m32_r6 : List ℕ := [265124,145592,19990,56165109,30906174285,969037228562]
/-- Krotov masks `(m = 64, r = 40)`. -/
def rkmMasksPack_m64_r40 : List (List Bool) := [rkmWbTraj07 39 439419437056,
  rkmWbTraj07 37 100385587200,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 40)`. -/
def rkmRowPack_m64_r40 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,10,890,3001,1557,9296,
  13449,22830,366040,1790414,685905,2627977,13621953,3055828,507880,76496564,27150062,1634433537,
  1778434,9965238986,4747630413,9545115834,973979448023]
/-- Krotov masks `(m = 8, r = 40)`. -/
def rkmMasksPack_m8_r40 : List (List Bool) := [[],[],[],[],[],rkmWbTraj07 1 1,rkmWbTraj07 2 3,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 40)`. -/
def rkmRowPack_m8_r40 : List ℕ := [1723,25620,63591,22170110,185608339,3828158631,179544340234,
  816419631525]
/-- Krotov masks `(m = 64, r = 34)`. -/
def rkmMasksPack_m64_r34 : List (List Bool) := [rkmWbTraj07 30 912667008,rkmWbTraj07 33 7359605032,
  []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 34)`. -/
def rkmRowPack_m64_r34 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,1,12,59,221,694,1148,3328,1786,
  133662,6734,9359824,81353944,5023424,2105724,1129426459,86354824,234040137,3652045022,119898030,
  9257567278,985422676968]
/-- Krotov masks `(m = 8, r = 8)`. -/
def rkmMasksPack_m8_r8 : List (List Bool) := [[],[],[],rkmWbTraj07 1 1,rkmWbTraj07 4 15,
  rkmWbTraj07 6 54,rkmWbTraj07 7 69,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 8)`. -/
def rkmRowPack_m8_r8 : List ℕ := [31564602,48293586,1230670,692443939,1809511369,530104400,
  73690388386,923195068269]
/-- Krotov masks `(m = 16, r = 34)`. -/
def rkmMasksPack_m16_r34 : List (List Bool) := [[],rkmWbTraj07 31 1655017472,
  rkmWbTraj07 33 5005201750,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 34)`. -/
def rkmRowPack_m16_r34 : List ℕ := [0,0,0,0,3,325,230,969,1152,1183,305,1990,401,71460,947075,
  3225377,2751748,65789,1476634,205616,369593213,377160487,4198631120,3087868469,342175,
  2028723683,730836377,162609468,3129459739,7500038766,13226598197,137509719,45121151079,
  919920726351]
/-- Krotov masks `(m = 32, r = 10)`. -/
def rkmMasksPack_m32_r10 : List (List Bool) := [rkmWbTraj07 10 1023,[],rkmWbTraj07 2 2,
  rkmWbTraj07 5 29,rkmWbTraj07 7 101,rkmWbTraj07 8 137,rkmWbTraj07 9 274,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 10)`. -/
def rkmRowPack_m32_r10 : List ℕ := [2099,5467,161786,168526,1553418,5716731,5492749,196428503,
  21608377512,978182093074]
/-- Krotov masks `(m = 4, r = 80)`. -/
def rkmMasksPack_m4_r80 : List (List Bool) := [[],[],rkmWbTraj07 26 62045186,
  rkmWbTraj07 27 132415490,rkmWbTraj07 29 357371906,rkmWbTraj07 30 582795264,
  rkmWbTraj07 32 2884305300,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 80)`. -/
def rkmRowPack_m4_r80 : List ℕ := [3017300,64886991,1798186711,478791413,2792845647,2973568628,
  4385418446,2817886446,444895597,540057159,3816162503,6341348909,78818783319,54448899734,
  435527032840,395368287261,4474598898,2167733047,2333035375,362593970,5604496,1614563,6376921,
  4415784,1233196,195733,19442,1315,61,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Krotov masks `(m = 4, r = 22)`. -/
def rkmMasksPack_m4_r22 : List (List Bool) := [[],[],rkmWbTraj07 2 2,rkmWbTraj07 16 32769,
  rkmWbTraj07 20 827418,rkmWbTraj07 20 851988,rkmWbTraj07 19 262207,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 22)`. -/
def rkmRowPack_m4_r22 : List ℕ := [393860695,107599,67627290,319828347,226486349,11275875792,
  142809657322,338648112109,319482322359,147014706102,34964541768,4454678747,122752247,1178674,
  5143,9,0,0,0,0,0,0]
/-- Krotov masks `(m = 64, r = 25)`. -/
def rkmMasksPack_m64_r25 : List (List Bool) := [[],[],rkmWbTraj07 8 248,rkmWbTraj07 17 115076,
  rkmWbTraj07 21 2059015,rkmWbTraj07 23 7162974,rkmWbTraj07 24 9153078,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 25)`. -/
def rkmRowPack_m64_r25 : List ℕ := [0,0,0,0,0,1,19,40,48,6497,5987,1253,9366,273967,296164,694370,
  550161,14529482,2417945,5444,116750053,224534002,126543997,9826083922,989687296918]
/-- Krotov masks `(m = 8, r = 23)`. -/
def rkmMasksPack_m8_r23 : List (List Bool) := [[],[],rkmWbTraj07 16 40940,rkmWbTraj07 18 237592,
  rkmWbTraj07 21 1097748,rkmWbTraj07 22 3473445,rkmWbTraj07 22 2097353,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 23)`. -/
def rkmRowPack_m8_r23 : List ℕ := [0,99463,4062025,2010800,117631712,55252801,567289777,
  13337900040,113676231335,292132316177,326139886375,184822798062,58253021338,9842511270,
  1013926128,34590843,467853,2941,8,0,0,0,0]
/-- Krotov masks `(m = 32, r = 112)`. -/
def rkmMasksPack_m32_r112 : List (List Bool) := [rkmWbTraj07 20 673528,rkmWbTraj07 22 2939840,
  rkmWbTraj07 28 190446592,rkmWbTraj07 29 451035137,rkmWbTraj07 28 224272386,
  rkmWbTraj07 27 111935496,rkmWbTraj07 29 313098273,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 112)`. -/
def rkmRowPack_m32_r112 : List ℕ := [56554379,3337747285,2206503479,2224124209,8942179627,
  7887398943,533713682,192113093,1151358116,5475474772,2760319,55194925462,390894400,47723322628,
  551789338352,305110064177,3394214729,3034329165,193380000,258356662,212315458,43437727,4296440,
  251701,9628,242,1,0,0,0,0,0]
/-- Krotov masks `(m = 8, r = 26)`. -/
def rkmMasksPack_m8_r26 : List (List Bool) := [[],[],rkmWbTraj07 7 109,rkmWbTraj07 23 6291592,
  rkmWbTraj07 22 2621565,rkmWbTraj07 22 2621920,rkmWbTraj07 23 4194938,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 26)`. -/
def rkmRowPack_m8_r26 : List ℕ := [482048,2278899,3976316,2765921,425312,61040866,12646387,
  3529844,618915,4981609976,82838215145,258022726037,330660450673,219123222714,82747328866,
  18741804243,2566072483,223356631,7305306,100201,654,0,0,0,0,0]
/-- Krotov masks `(m = 8, r = 24)`. -/
def rkmMasksPack_m8_r24 : List (List Bool) := [[],rkmWbTraj07 16 65535,rkmWbTraj07 23 8386781,
  rkmWbTraj07 23 6711174,rkmWbTraj07 6 32,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 24)`. -/
def rkmRowPack_m8_r24 : List ℕ := [5160815,5727332,1592028,37116352,1474,964684,90297,56596751,
  7777572,29629,16452787,10271672,83338662,17782099,416916424,1878406,2462359540,4278950,
  11459617716,21124623,38615504594,9426761894,78409078431,858932406408]
/-- Krotov masks `(m = 4, r = 27)`. -/
def rkmMasksPack_m4_r27 : List (List Bool) := [[],[],rkmWbTraj07 16 65530,rkmWbTraj07 20 983040,
  rkmWbTraj07 24 13893751,rkmWbTraj07 24 11534800,rkmWbTraj07 23 4195072,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 27)`. -/
def rkmRowPack_m4_r27 : List ℕ := [61420726,4320401,181006439,426113178,290635494,190223228,
  283151143,472012408,40664408,730320939,3942439768,74519442944,227762419379,306155458078,
  233031188409,109664349429,34128533877,7051686869,966943868,75087683,2837891,49207,361,0,0,0,0]
/-- Krotov masks `(m = 16, r = 20)`. -/
def rkmMasksPack_m16_r20 : List (List Bool) := [[],rkmWbTraj07 17 114074,rkmWbTraj07 19 430677,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 20)`. -/
def rkmRowPack_m16_r20 : List ℕ := [43,1231,8906,149942,231847,3598113,10559512,2070682,16643524,
  49560339,74039257,231547279,1561496877,178802280,3535161746,10346952166,2784709131,1104084824,
  39632499133,940467882882]
/-- Krotov masks `(m = 32, r = 16)`. -/
def rkmMasksPack_m32_r16 : List (List Bool) := [[],[],rkmWbTraj07 9 461,rkmWbTraj07 12 3946,
  rkmWbTraj07 14 13992,rkmWbTraj07 15 16488,rkmWbTraj07 15 16841,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 16)`. -/
def rkmRowPack_m32_r16 : List ℕ := [0,0,0,307,15702,75051,71034,156391,11373269,2390839,5345720,
  181642704,511792660,68547154,18193561416,981025027613]
/-- Cumulative `2`-lane trajectory head invariant (`Traj05` -> `Traj07`). -/
def rkmTrajLaneProp_07 : Prop :=
  rkmTrajLaneProp_05 ∧ (rkmRow_m2_r6.head? = some 113120912)
/-- Proof of `rkmTrajLaneProp_07` in `O(1)` kernel steps. -/
theorem rkmTrajLaneOk_07 : rkmTrajLaneProp_07 :=
  ⟨rkmTrajLaneOk_05, rfl⟩
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
private def wc_rkmTraj_m16_r128_s4_hb_p0 : List ℕ := [136460782309348,191828468617784,
  233524058314821,268013349383472,297816734419917,324234603937860,348043970984802,369754007909931,
  389720383468756,408203497701978,425401008603964,441467305773584,456525820073529,470677152751505,
  484004640755521,496578283723917,508457587142449,519693666945251,530330837786716,540407832175780,
  549958750445548,559013810985201,567599949911168,575741305633917,583459614295958,590774535388679,
  597703922089809,604264047406771,610469794670345,616334819032149,621871685196035,627091985530733,
  632006441879259,636624993735794,640956874956546,645010680773811,648794426566943,652315599591710,
  655581204666451,658597804649032,661371556404606,663908242854405,666213301605402,668291850585820,
  670148711049200,671788428257698,673215290111629,674433343955383,675446411758730,676258103845954,
  676871831322676,677290817330811,677518107245427,677556577912877,677408946017037,677077775649644,
  676565485151147,675874353280145,675006524762050,673964015261048,672748715813523,671362396755820,
  669806711174388,668083197901926]
private def wc_rkmTraj_m16_r128_s4_hb_p1 : List ℕ := [666193284079096,664138287297502,
  661919417336052,659537777499316,656994365563134,654290074329368,651425691788358,648401900884219,
  645219278874586,641878296272733,638379315356031,634722588220488,630908254356492,626936337715790,
  622806743234076,618519252767230,614073520392067,609469067014303,604705274217118,599781377272900,
  594696457228347,589449431958535,584039046068653,578463859502133,572722234690373,566812322051315,
  560732043610884,554479074481418,548050821883268,541444401337787,534656609589395,527683893728272,
  520522315879323,513167512692092,505614648703339,497858362439902,489892703871917,481711061499236,
  473306076934596,464669544305368,455792291089343,446664036069939,437273218858569,427606793766118,
  417649978535656,407385945313711,396795436844231,385856284612728,374542796598570,362824968886032,
  350667455127341,338028196485755,324856564762758,311090789410676,296654299480108,281450363513030,
  265353947476644,248198794074474,229755774590986,209694010872052,187504306920309,162327489146490,
  132484946589993,93635699149642]
private def wc_rkmTraj_m16_r128_s4_hb : List ℕ := pCat wc_rkmTraj_m16_r128_s4_hb_p0
  wc_rkmTraj_m16_r128_s4_hb_p1
private def wc_rkmTraj_m16_r128_s4_v0_p0 : List ℕ := [2000104035872796,2000156793384514,
  2000081991936704,2000077300049020,2000002856630079,1999970074439094,1999956492071724,
  1999933823883744,2000083145331829,2000143649773673,2000002017199073,1999924862360957,
  1999983838818182,2000035075191356,1999938202204839,1999939364835000,1999936232993060,
  1999889384973647,2000016545438877,2000065262667245,2000059840954351,1999972649536024,
  1999954926082707,2000044237574761,2000014160201193,1999947492875897,2000089531207955,
  2000111578960416,1999884141993941,1999926162536577,2000016130297933,2000026685087218,
  2000004983609777,1999935082195326,2000092864297567,2000055230743583,2000018323828956,
  2000081541873995,2000089751721618,1999931861418125,1999937022907821,1999931874674722,
  2000069920221015,1999935291207251,2000043946045817,2000027418089565,1999951527743671,
  2000102190911461,2000162180109732,2000199551806208,2000161983055662,2000018278311884,
  1999852706655735,2000144074888408,1999835306442867,1999362203849001,2000742018734444,
  2000192144746917,1997747525594086,1995796607387136,1996448228460501,1997939362101735,
  1987447021018474,1976484411765391]
private def wc_rkmTraj_m16_r128_s4_v0_p1 : List ℕ := [1973741464165828,2010489775906876,
  2031209263866378,2099221552787633,2185267315155701,2274315512456347,2349246529545259,
  2396195836558143,2408384605754240,2387174069781934,2340421253090273,2279249204788904,
  2214675236661464,2155202826810828,2105813796514901,2068181472374273,2041594447161676,
  2024057610644351,2013206415522530,2006886260309682,2003412708680415,1998391949254149,
  1999279418936754,2000307106786889,2000124484278919,2000047986211641,2000017588310219,
  2000006128329480,2000002029338469,2000000638449935,2000000190768726,2000000054116011,
  2000000014567811,2000000003719667,1999999999099626,1999999999793516,2000000000044832,
  2000000000009205,2000000000001783,2000000000000323,2000000000000053,2000000000000006,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m16_r128_s4_v0_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m16_r128_s4_v0 : List ℕ := pCat wc_rkmTraj_m16_r128_s4_v0_p0 (pCat
  wc_rkmTraj_m16_r128_s4_v0_p1 wc_rkmTraj_m16_r128_s4_v0_p2)
private def wc_rkmTraj_m16_r128_s4_v1_p0 : List ℕ := [1999996514350729,1999982380722392,
  1999956743992013,1999988440186916,2000040624531427,2000006308674210,2000034556311615,
  2000034011268850,2000018600218609,2000091448713062,2000124155422545,2000075545767635,
  2000003559214723,2000038268072062,2000140450512371,2000078125697907,2000149394695723,
  2000015157160179,1999917840591787,1999932302784567,2000030385895476,1999890678354499,
  2000012161408645,2000050079052626,2000095126407057,2000074401072437,1999892944434373,
  1999998266899517,2000064128149685,2000080281717135,2000023331130871,1999906141872993,
  2000051121922907,1999989626776007,1999884195962157,1999972814354258,1999534016901337,
  2000980230695642,1998381910112659,2002364113845975,1996935670039983,2003725060427739,
  1995629214502485,2004594382674826,1995853327270865,2002711348277352,1999848879545944,
  1997656228271033,2003601442170240,1997228795012886,2000308342382027,2002353929488864,
  1996651273508492,2001511516545652,2001939751260248,1996060704167757,2001299977317794,
  2003634420690131,1996402251944484,1997990136517669,2005023191869940,2000140257503842,
  1995301678344913,1999985708089974]
private def wc_rkmTraj_m16_r128_s4_v1_p1 : List ℕ := [2005420563991072,1999216267704408,
  1995550693652285,1999433943390637,2003527508843607,2002276980955904,1997408476544996,
  1997823371263719,2000722633596909,2001130534954545,2001573049127328,2001189733560564,
  1999360070945773,1997575383380460,1995627669797086,1997336381012267,2006264790399063,
  2015127782463575,2012423053929511,1993828912356064,1963673678459097,1935334367848528,
  1929946670823054,1965085146782989,2042543013086516,2148053513181522,2259292416362796,
  2353065419402021,2410813204822993,2423975341901733,2396345995958972,2340748165767481,
  2272455585050858,2203997254650644,2143348938886325,2094416405198303,2058115303159757,
  2033332106541652,2017784595986255,2008828948000098,2004087274691984,2001772325709156,
  2000724621930732,2000281729514889,2000105154148388,2000038008543911,2000013380445233,
  2000004591904019,2000001529994863,2000000491227446,2000000150622489,2000000043727743,
  2000000011928920,2000000003038353,2000000000718521,2000000000156935,2000000000031482,
  2000000000005761,2000000000000951,2000000000000137,2000000000000016,2000000000000001,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m16_r128_s4_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m16_r128_s4_v1 : List ℕ := pCat wc_rkmTraj_m16_r128_s4_v1_p0 (pCat
  wc_rkmTraj_m16_r128_s4_v1_p1 wc_rkmTraj_m16_r128_s4_v1_p2)
private def wc_rkmTraj_m16_r128_s4_v2_p0 : List ℕ := [2000010145820366,2000004018759373,
  2000001703260679,1999943582976971,2000048626782304,1999983527899344,2000040947293123,
  1999995567966987,2000002752880001,1999967227251970,1999942520963092,2000073922882996,
  1999947532288654,1999937979134623,1999901359089403,2000300465936295,1999430719169612,
  2001093628167668,1998244372746483,2002604751820450,1996537886434584,2004062074802875,
  1995721437612234,2003896507677999,1997454723062666,2001087047095477,2000852139111670,
  1997664299590673,2002916260460856,1997845115398500,2000530176786317,2001758708612442,
  1997224329400084,2002128646584795,2000430421476024,1997769314018291,2002592711185226,
  1999046371388928,1998459123521273,2002308249994765,1999281590236640,1998126595988590,
  2002915160432950,1998716169089732,1998586592455695,2002527462725582,1999310842461148,
  1998045154885231,2002032230935310,2000953613931274,1996968350907198,2001245469549770,
  2002760731349986,1996822003505119,1999017220035455,2003472349904055,1999247801415770,
  1996879450523868,2001446601854809,2002870265347284,1997889049056780,1997169132501452,
  2002899344383045,2002310973383254]
private def wc_rkmTraj_m16_r128_s4_v2_p1 : List ℕ := [1996518440957520,1998454196977228,
  2003387328824686,2001078307209742,1997211625362772,1998839926509432,2002233987658422,
  2001771638436646,1998262169377468,1997666573607568,2001221161265565,2002364607621591,
  1999293501293770,1998139763110595,2000156558867817,2000896073808566,2000231900692580,
  2000416248309813,2000235528684439,1998918540610618,1998678162093184,2000392479672784,
  2002246352325328,2002069602671225,1998763121085170,1994695236985321,1995999456356939,
  2004731818859223,2012095958090658,2006561876210602,1989346011119958,1976731724923989,
  1985098371562673,2014283740215547,2044181511173029,2046992662840987,2007612793463515,
  1939034849822734,1880192885088078,1874767916448645,1944788921114383,2077493215397022,
  2232997851993421,2365082836112979,2441005832425764,2450836197719214,2405271602184195,
  2326568388670328,2238378617438304,2158560071170849,2096422917908892,2053698387745771,
  2027404422109131,2012814806516913,2005486589749683,2002147635590525,2000766822265921,
  2000248904214753,2000073082565167,2000019268399902,2000004511194543,2000000921561221,
  2000000159466396,2000000022086865]
private def wc_rkmTraj_m16_r128_s4_v2_p2 : List ℕ := [2000000002124324]
private def wc_rkmTraj_m16_r128_s4_v2 : List ℕ := pCat wc_rkmTraj_m16_r128_s4_v2_p0 (pCat
  wc_rkmTraj_m16_r128_s4_v2_p1 wc_rkmTraj_m16_r128_s4_v2_p2)
private def wc_rkmTraj_m16_r128_s5_hb_p0 : List ℕ := [137829750679947,193752883102840,
  235866761062062,270702047132342,300804418373916,327487310759065,351535532294890,373463363324466,
  393630040656100,412298576651877,429668612202187,445896085735342,461105666366844,475398964571546,
  488860153329935,501559934513542,513558410564456,524907210209540,535651092665786,545829179004903,
  555475911652988,564621812148727,573294086830451,581517116264061,589312854648063,596701158696970,
  603700060690780,610325996886986,616593999925266,622517861945100,628110273698879,633382943849449,
  638346701800868,643011586759871,647386925216292,651481398629407,655303102788493,658859600061126,
  662157965537664,665204827914269,668006405821481,670568540194538,672896723190238,674996124079628,
  676871612482845,678527779259909,679968955327156,681199228631751,682222459485291,683042294430671,
  683662178793566,684085368050306,684314938127023,684353794730461,684204681798148,683870189144669,
  683352759371158,682654694096614,681778159562239,680725191653269,679497700376881,678097473829353,
  676526181680821,674785378201485]
private def wc_rkmTraj_m16_r128_s5_hb_p1 : List ℕ := [672876504849017,670800892433040,
  668559762868910,666154230529497,663585303200283,660853882639678,657960764743107,654906639305946,
  651692089376855,648317590189275,644783507654927,641090096398835,637237497310748,633225734582695,
  629054712196691,624724209820204,620233878059761,615583233014829,610771650064655,605798356809917,
  600662425078415,595362761889396,589898099253986,584266982669035,578467758137926,572498557523678,
  566357282006076,560041583374289,553548842838021,546876146981666,540020260414730,532977594584762,
  525744172112085,518315585873306,510686951896040,502852854921070,494807285228101,486543564990715,
  478054262002646,469331088070320,460364778653202,451144949394014,441659923930875,431896525700909,
  421839824152255,411472822615181,400776070645716,389727177335841,378300192923740,366464812495769,
  354185335111199,341419280000948,328115511066711,314211638081485,299630321939584,284273860777390,
  268015966226364,250688713104386,232060674087051,211797651665618,189385341611602,163955951145312,
  133814029557222,94575048230935]
private def wc_rkmTraj_m16_r128_s5_hb : List ℕ := pCat wc_rkmTraj_m16_r128_s5_hb_p0
  wc_rkmTraj_m16_r128_s5_hb_p1
private def wc_rkmTraj_m16_r128_s5_v0_p0 : List ℕ := [1999989854179634,2000004018759373,
  2000001703260679,1999943582976971,2000048626782304,2000016472100656,2000040947293123,
  2000004432033013,1999997247119999,1999967227251970,1999942520963092,1999926077117004,
  2000052467711346,1999937979134623,2000098640910597,2000300465936295,2000569280830388,
  2001093628167668,2001755627253517,2002604751820450,2003462113565416,2004062074802875,
  2004278562387766,2003896507677999,1997454723062666,1998912952904523,1999147860888330,
  1997664299590673,2002916260460856,1997845115398500,1999469823213683,1998241291387558,
  1997224329400084,1997871353415205,1999569578523976,1997769314018291,2002592711185226,
  2000953628611072,2001540876478727,2002308249994765,1999281590236640,1998126595988590,
  2002915160432950,1998716169089732,1998586592455695,2002527462725582,2000689157538852,
  1998045154885231,2002032230935310,2000953613931274,2003031649092802,2001245469549770,
  2002760731349986,2003177996494881,2000982779964545,2003472349904055,2000752198584230,
  2003120549476132,2001446601854809,2002870265347284,2002110950943220,2002830867498548,
  2002899344383045,2002310973383254]
private def wc_rkmTraj_m16_r128_s5_v0_p1 : List ℕ := [2003481559042480,2001545803022772,
  2003387328824686,2001078307209742,2002788374637228,2001160073490568,2002233987658422,
  2001771638436646,2001737830622532,2002333426392432,2001221161265565,2002364607621591,
  2000706498706230,2001860236889405,1999843441132183,2000896073808566,1999768099307420,
  1999583751690187,2000235528684439,2001081459389382,2001321837906816,2000392479672784,
  1997753647674672,2002069602671225,2001236878914830,2005304763014679,2004000543643061,
  2004731818859223,2012095958090658,2006561876210602,2010653988880042,2023268275076011,
  2014901628437327,2014283740215547,2044181511173029,2046992662840987,2007612793463515,
  2060965150177266,2119807114911922,2125232083551355,2055211078885617,2077493215397022,
  2232997851993421,2365082836112979,2441005832425764,2450836197719214,2405271602184195,
  2326568388670328,2238378617438304,2158560071170849,2096422917908892,2053698387745771,
  2027404422109131,2012814806516913,2005486589749683,2002147635590525,2000766822265921,
  2000248904214753,2000073082565167,1999980731600098,1999995488805457,1999999078438779,
  1999999840533604,1999999977913135]
private def wc_rkmTraj_m16_r128_s5_v0_p2 : List ℕ := [1999999997875676]
private def wc_rkmTraj_m16_r128_s5_v0 : List ℕ := pCat wc_rkmTraj_m16_r128_s5_v0_p0 (pCat
  wc_rkmTraj_m16_r128_s5_v0_p1 wc_rkmTraj_m16_r128_s5_v0_p2)
private def wc_rkmTraj_m16_r128_s5_v1_p0 : List ℕ := [2000058067882116,1999996379960235,
  2000037923598531,1999998882898456,1999852840036644,2000226116807429,1999634534407085,
  2000470277638821,1999620941997796,1999809327476014,2001391449748053,1997552422030601,
  2002348016766685,1999084484475931,1999163169507704,2000955798676985,2000876824635553,
  1997461715421543,2001661528004040,2000656406331605,1998772541119411,1999852244919157,
  2001359275913742,1998719468142596,2000934205918668,1999916960188256,1998974333489281,
  2000029624348878,2002194052047634,1997993614010734,1999788142482350,2001661225235696,
  1996652795036817,2002412153689321,2000977267887965,1999746339568095,1998092507816962,
  2000241716478422,2000592997934746,1999816325358133,2004718018299957,2005283601964284,
  2004617336239379,2000929677392053,2003624840622623,2001037328336065,2000096507537242,
  1999230094082269,2000159217415280,2001185074577510,1999661751046398,2000504854889434,
  1998709979769725,1999318329973970,1996641788358875,1997581450926551,1997412195203755,
  1999523909676936,2000138798845857,2000760285539262,2000770304862192,2000608640661403,
  2000317337058094,2001013712547163]
private def wc_rkmTraj_m16_r128_s5_v1_p1 : List ℕ := [1999632330091348,2001621190233795,
  1998912304853878,2000898611086438,1999161036631569,1999687028461902,2000951262008922,
  1999357327378268,2002869276632015,2000479700828071,2002336646510358,2003449906536204,
  1999808156353745,2004982891477971,1999800495251513,2003847659059707,2000366776651549,
  2005241678823509,1997033687141658,2011739210445826,1992469478718697,2009428093112427,
  2006005379601382,1991332377759233,2012709777382211,2000839936342397,1996980083993953,
  2004496698579345,2008790198684471,1990246590254698,2005221390593374,2019531899211731,
  1979788202367248,1997401675914733,2030340280188153,1982086093111768,1979714739094910,
  2035222245233825,2005198022291034,1958028315310154,2008066711695737,2043997710795869,
  1985999667339102,1957458544690929,2021291486581412,2059858239764327,2004744759682845,
  1954180534284183,1999687671718409,2084374931566832,2095660714131533,2022343934770138,
  1967151075893292,2028578129611565,2203697153515272,2398764699030059,2511714219619598,
  2501602319668729,2397385626068215,2260442844580070,2142117684160041,2064140673862482,
  2023393502262227,2006530813540259]
private def wc_rkmTraj_m16_r128_s5_v1_p2 : List ℕ := [2001208890615982]
private def wc_rkmTraj_m16_r128_s5_v1 : List ℕ := pCat wc_rkmTraj_m16_r128_s5_v1_p0 (pCat
  wc_rkmTraj_m16_r128_s5_v1_p1 wc_rkmTraj_m16_r128_s5_v1_p2)
private def wc_rkmTraj_m16_r128_s5_v2_p0 : List ℕ := [2000134360076433,1998549705724893,
  2002467008092732,1998756484547659,1999540904123625,2000045784851609,2001662079549728,
  1998774903941189,1999284865328083,2000283799996203,2002013962283238,1998864143097779,
  1998200429221302,2001679312368493,2000365897921551,2000734258469865,1996745722083045,
  2001712004837463,2002147928465219,1997099099966489,2000771469138650,2000318168659847,
  2000216602903133,1998606722112801,2002002438262353,1999677374823428,1998448259095411,
  2000504768802684,2000847719938330,2000716398021690,1997746877385452,2001159032214528,
  2000275832139678,1999724156745232,1999029676911647,2001543923341388,2000230473877875,
  1998485847874398,1999412244973469,2001571649901550,2000430986642126,1999742401734246,
  1998722704733630,2001405413071856,1998920215176655,2000144682424538,1999878163180177,
  2001230862097958,2001157726273659,1997604303188695,1999756550022778,1998940910584805,
  2001123440380776,2001796080663130,1998882891483888,2002815660855199,1995925446773413,
  2001876027537180,1994864619613511,2002650557123279,1997532703054893,2006276630484525,
  1998477717286498,2009306794367253]
private def wc_rkmTraj_m16_r128_s5_v2_p1 : List ℕ := [1999161992328179,2005539089997135,
  2003282509756691,1995140028822471,2009095601008066,1992219207636189,2007372533968636,
  2000702898531157,1996980831869847,2004750432353049,1995085777905408,1996325338286455,
  2001507843249865,1996703240756330,1994598769799846,2007363518203069,1994905239946515,
  1995562952759177,2013367211949982,1989154261673853,2000776620190667,2014377013367629,
  1982274193873143,2006547506396441,2011488911318735,1977309371006760,2013191973779287,
  2011259428194216,1974845039720593,2018049815409874,2014898113454418,1972309124832788,
  2016350980769689,2020540782787911,1971354483705581,2009862808690142,2029000057002228,
  1974160809436809,1997947234790597,2038737151825327,1984455306338958,1975805858846158,
  2037921008179931,2011898994307328,1960853506583026,2013472552991125,2042807581894364,
  1973498683865469,1967385924399310,2044507768974127,2027965375242721,1943763828798473,
  1977082043632944,2069174961211119,2022686934307953,1915860548522007,1974751400703956,
  2123439349810486,2082861548450662,1883352947428836,1884449455972408,2228574718964782,
  2596373369284635,2624826318781935]
private def wc_rkmTraj_m16_r128_s5_v2_p2 : List ℕ := [2341011502734255]
private def wc_rkmTraj_m16_r128_s5_v2 : List ℕ := pCat wc_rkmTraj_m16_r128_s5_v2_p0 (pCat
  wc_rkmTraj_m16_r128_s5_v2_p1 wc_rkmTraj_m16_r128_s5_v2_p2)
private def wc_rkmTraj_m16_r128_s3_hb_p0 : List ℕ := [156129171692288,219074992151113,
  266198288259770,304939788461500,338205583637982,367497866929434,393715884417472,417449985043853,
  439113295384560,459008837636177,477367046853211,494368249625287,510156884057365,524850897528397,
  538548185372175,551331137538392,563269932861560,574424979419848,584848757578073,594587235750647,
  603680974428374,612165998747534,620074496491572,627435382562449,634274759999920,640616299916450,
  646481557202299,651890234855160,656860406847164,661408707252019,665550491705907,669299976020724,
  672670355803830,675673910190457,678322092209987,680625607846068,682594485484249,684238137147826,
  685565412686675,686584647892770,687303707360327,687730022780921,687870627258780,687732186144456,
  687321024812674,686643153749662,685704291264540,684509884096552,683065126153760,681374975588108,
  679444170385593,677277242627881,674878531562557,672252195602624,669402223361660,666332443818660,
  663046535695913,659548036123909,655840348659161,651926750713685,647810400448672,643494343179352,
  638981517333275,634274759999920]
private def wc_rkmTraj_m16_r128_s3_hb_p1 : List ℕ := [629376812105791,624290323245823,
  619017856198909,613561891152771,607924829660996,602108998352965,596116652415537,589949978863628,
  583611099615351,577102074385978,570424903413793,563581530029779,556573843082098,549403679225395,
  542072825084180,534583019298746,526935954461472,519133278950674,511176598668692,503067478690312,
  494807444827218,486397985113727,477840551218653,469136559787829,460287393721459,451294403390191,
  442158907793527,432882195663928,423465526519743,413910131669890,404217215172995,394387954753539,
  384423502677388,374324986588910,364093510311771,353730154615340,343235977948526,332612017142760,
  321859288085703,310978786367208,299971487898924,288838349508878,277580309512290,266198288259770,
  254693188664032,243065896706142,231317281922293,219448197872034,207459482588813,195351959013678,
  183126435412901,170783705780262,158324550224699,145749735343973,133060014584976,120256128591276,
  107338805538448,94308761457735,81166700548536,67913315480194,54549287683545,41075287632657,
  27491975117162,13799999505581]
private def wc_rkmTraj_m16_r128_s3_hb : List ℕ := pCat wc_rkmTraj_m16_r128_s3_hb_p0
  wc_rkmTraj_m16_r128_s3_hb_p1
private def wc_rkmTraj_m16_r128_s3_v0_p0 : List ℕ := [2000007411022365,1999976326582197,
  2000051472617387,2000087255001304,2000120756915504,2000137764452717,1999873844920598,
  1999917631471261,2000014702283884,1999941413266401,1999884171401913,1999860139565256,
  1999875926179216,1999926257906800,1999996798218213,1999930115925145,1999869847192587,
  1999831768460087,1999818174682071,2000174315551442,1999847693605364,2000123405176887,
  2000095107221199,2000074755394413,2000066426209989,2000052009197922,1999931262889830,
  2000612922703416,2002342600430338,2006744761951353,2016220169231237,2033945658811408,
  2063186410608156,2106030726886804,2161874393988781,2226317527847838,2291199192025753,
  2346130611060675,2381203757850989,2389907190262295,2371072897688488,2329067106371897,
  2272222067147148,2210248811700383,2151689820766741,2102264343982213,2064426353580242,
  2037922345743871,2020846374614770,2010694591766146,2005115199577140,2002277965554792,
  2000942912448318,2000361983350868,2000128530932364,2000042065909766,1999987365411353,
  1999996536827347,1999999139983444,2000000191613157,2000000037787080,2000000006465692,
  2000000000929890,2000000000106021]
private def wc_rkmTraj_m16_r128_s3_v0_p1 : List ℕ := [2000000000008299]
private def wc_rkmTraj_m16_r128_s3_v0 : List ℕ := pCat wc_rkmTraj_m16_r128_s3_v0_p0
  wc_rkmTraj_m16_r128_s3_v0_p1
private def wc_rkmTraj_m16_r128_s3_v1_p0 : List ℕ := [1999969966233831,2000040611130738,
  2000064185134990,1999982873825568,1999941101554223,2000028326593816,1999973710263793,
  2000148895362457,1999796193151482,2000022287085429,1999970021702051,2000003443235035,
  2000137244884092,2000201678937217,1999987283282668,2000062041237216,2000106841056460,
  1999926390322067,1999942024917219,2000072658925007,2000045795185211,1999961771812549,
  1999919466331156,1999871331364956,1999853592437480,1999921029550090,1999994707935197,
  1999982074687285,1999919153774404,1999892012746660,1999908232463034,1999913325912710,
  1999884770950990,1999860163725579,1999882104551989,1999952740299114,2000026646080418,
  2000070252183221,2000064201038303,2000075366507834,2000136896122671,2000289990627982,
  2000327002248696,1999894219237500,1998570857145796,1996427047087638,1994815735166119,
  1996865900983033,2007405421914504,2031731162346177,2073426840795164,2132203634366118,
  2202700835962507,2275032957629220,2337213964889687,2378527012858481,2392473573366845,
  2378280152273682,2340569987736468,2287507244626573,2228282161888978,2170901582924125,
  2120878464885333,2080916402979404]
private def wc_rkmTraj_m16_r128_s3_v1_p1 : List ℕ := [2051344050055155,2030925544948952,
  2017701515343908,2009635729000206,2004989197936767,2002456445440710,2001149145113691,
  2000510229319082,2000214762376578,2000085595273507,2000032270320925,2000011499438437,
  2000003871093882,2000001230680155,2000000369476028,2000000104770034,2000000028073189,
  2000000007113447,2000000001706503,2000000000388249,2000000000083971,2000000000017321,
  2000000000003421,2000000000000647,2000000000000116,2000000000000018,2000000000000002,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m16_r128_s3_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m16_r128_s3_v1 : List ℕ := pCat wc_rkmTraj_m16_r128_s3_v1_p0 (pCat
  wc_rkmTraj_m16_r128_s3_v1_p1 wc_rkmTraj_m16_r128_s3_v1_p2)
private def wc_rkmTraj_m16_r128_s3_v2_p0 : List ℕ := [1999895964127204,2000156793384514,
  1999918008063296,1999922699950980,1999997143369921,2000029925560906,1999956492071724,
  1999933823883744,2000083145331829,2000143649773673,1999997982800927,1999924862360957,
  2000016161181818,2000035075191356,1999938202204839,1999939364835000,2000063767006940,
  2000110615026353,2000016545438877,1999934737332755,1999940159045649,1999972649536024,
  1999954926082707,1999955762425239,1999985839798807,2000052507124103,2000089531207955,
  2000111578960416,2000115858006059,2000073837463423,2000016130297933,1999973314912782,
  1999995016390223,2000064917804674,2000092864297567,2000055230743583,1999981676171044,
  1999918458126005,1999910248278382,1999931861418125,1999937022907821,1999931874674722,
  1999930079778985,1999935291207251,1999956053954183,1999972581910435,1999951527743671,
  1999897809088539,1999837819890268,1999800448193792,1999838016944338,1999981721688116,
  2000147293344265,2000144074888408,1999835306442867,1999362203849001,1999257981265556,
  2000192144746917,2002252474405914,2004203392612864,2003551771539499,1997939362101735,
  1987447021018474,1976484411765391]
private def wc_rkmTraj_m16_r128_s3_v2_p1 : List ℕ := [1973741464165828,1989510224093124,
  2031209263866378,2099221552787633,2185267315155701,2274315512456347,2349246529545259,
  2396195836558143,2408384605754240,2387174069781934,2340421253090273,2279249204788904,
  2214675236661464,2155202826810828,2105813796514901,2068181472374273,2041594447161676,
  2024057610644351,2013206415522530,2006886260309682,2003412708680415,2001608050745851,
  2000720581063246,2000307106786889,2000124484278919,2000047986211641,2000017588310219,
  2000006128329480,2000002029338469,2000000638449935,2000000190768726,2000000054116011,
  2000000014567811,2000000003719667,2000000000900374,2000000000206484,2000000000044832,
  2000000000009205,2000000000001783,2000000000000323,2000000000000053,2000000000000006,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m16_r128_s3_v2_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m16_r128_s3_v2 : List ℕ := pCat wc_rkmTraj_m16_r128_s3_v2_p0 (pCat
  wc_rkmTraj_m16_r128_s3_v2_p1 wc_rkmTraj_m16_r128_s3_v2_p2)
private def wc_rkmTraj_m16_r128_s2_hb : List ℕ := [185711547719019,259555998795762,
  314112834822402,358338818383164,395744973596945,428152145197624,456653583175074,481968931811290,
  504603000771422,524926820453486,543223017644791,559713041590771,574574410542792,587952124077014,
  599966490840257,610718661382017,620294639852736,628768257052390,636203415769190,642655814604707,
  648174290480126,652801877260673,656576649545445,659532401399168,661699196457350,663103816423432,
  663770128222531,663719385150197,662970473703221,661540115027847,659443027809572,656692057775346,
  653298277651868,649271060325223,644618127002488,639345571324393,633457859567427,626957806254328,
  619846523612697,612123342324415,603785699822703,594828990926661,585246373729798,575028521203677,
  564163305687639,552635398938741,540425764153751,527511007490373,513862543763756,499445512019945,
  484217348037199,468125876457868,451106714670512,433079664623557,413943571292619,393568775780138,
  371785636369091,348366294257232,322994099478096,295208671478275,264297653348591,229053963472863,
  187111800545247,132339839291470]
private def wc_rkmTraj_m16_r128_s2_v0 : List ℕ := [2000009018842465,1999941055176516,
  1999735780077669,2000937427512168,2002790610620071,2007194329460728,2016382777827891,
  2033395755216631,2061523010928894,2103151330713676,2158232875695156,2222969635970826,
  2289496457423932,2347117004317081,2384993436095714,2395409426363475,2376283352851808,
  2331830251290062,2271090414753031,2205010224178445,2143335826479755,2092485058277253,
  2054938028950602,2029948621747699,2014920578504132,2006757063129249,2002761882694176,
  2001009160330388,2000325235591288,2000090642570386,2000021164771803,2000003905899120,
  2000000493664243]
private def wc_rkmTraj_m16_r128_s2_v1_p0 : List ℕ := [1999992588977635,1999976326582197,
  1999948527382613,1999912744998696,1999879243084496,1999862235547283,1999873844920598,
  1999917631471261,1999985297716116,2000058586733599,2000115828598087,2000139860434744,
  2000124073820784,2000073742093200,2000003201781787,1999930115925145,1999869847192587,
  1999831768460087,1999818174682071,1999825684448558,1999847693605364,1999876594823113,
  1999904892778801,1999925244605587,1999933573790011,1999947990802078,2000068737110170,
  2000612922703416,2002342600430338,2006744761951353,2016220169231237,2033945658811408,
  2063186410608156,2106030726886804,2161874393988781,2226317527847838,2291199192025753,
  2346130611060675,2381203757850989,2389907190262295,2371072897688488,2329067106371897,
  2272222067147148,2210248811700383,2151689820766741,2102264343982213,2064426353580242,
  2037922345743871,2020846374614770,2010694591766146,2005115199577140,2002277965554792,
  2000942912448318,2000361983350868,2000128530932364,2000042065909766,2000012634588647,
  2000003463172653,2000000860016556,2000000191613157,2000000037787080,2000000006465692,
  2000000000929890,2000000000106021]
private def wc_rkmTraj_m16_r128_s2_v1_p1 : List ℕ := [2000000000008299]
private def wc_rkmTraj_m16_r128_s2_v1 : List ℕ := pCat wc_rkmTraj_m16_r128_s2_v1_p0
  wc_rkmTraj_m16_r128_s2_v1_p1
private def wc_rkmTraj_m1024_r64_s0_hb : List ℕ := [178823529411584,250788597275133,
  304555619248891,348652257141394,386407377989090,419540044501065,449077816860817,475693913555772,
  499858197884734,521914139540420,542121831540632,560683760416570,577761104261909,593484499462479,
  607961412729266,621281342110467,633519580457240,644739998241310,654997139873967,664337828379034,
  672802410748593,680425735833351,687237929760226,693265015646573,698529411764000,703050333405015,
  706844117315912,709924482891677,712302740859287,713987957548344,714987080816332,715305032085124,
  714944767629089,713907311137817,712191758583167,709795255488168,706712945767412,702937890328182,
  698460952526980,693270646293977,687352941175776,680691016581893,673264954984150,665051360472693,
  656022884574643,646147635085829,635388435093637,623701887216048,611037180526197,597334551751702,
  582523273328973,566518980622825,549220054881931,530502621544601,510213456711510,488159621615705,
  464092763814703,437684282122498,408483850368375,375845176461351,338780283442816,295633954431488,
  243196603633586,173235294117472]
private def wc_rkmTraj_m1024_r64_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTraj_m1024_r64_s0_v1_p0 : List ℕ := [2000000000947647,2000000007351915,
  2000000039976906,2000000175908082,2000000664278410,2000002223095614,2000006728431771,
  2000018675494127,2000048022608056,2000115288936891,2000259971673627,2000553313830656,
  2001115967876465,2002139944107808,2003912299687888,2006835463395530,2011436426174451,
  2018355179666576,2028302922517570,2041983743725981,2059980207924703,2082612918677528,
  2109794833546868,2140909867492930,2174748795538539,2209531026190044,2243027704642183,
  2272781649575931,2296397173546966,2311853738298675,2317787311848986,2313685830076251,
  2299960536860644,2277879723161514,2249379303867046,2216788675395813,2182524557182226,
  2148807141104184,2117442555498824,2089697179160277,2066268168503810,2047336053870072,
  2032673216724060,2021777936099595,2014006668374787,2008684912981613,2005186474734712,
  2002979582993016,2001644531398705,2000870710665990,2000441459731149,2000213901308927,
  2000098812897624,2000043399351120,2000018062850619,2000007095698725,2000002618178258,
  2000000901924346,2000000287842512,2000000084244342,2000000022298336,2000000005230524,
  2000000001052929,2000000000171512]
private def wc_rkmTraj_m1024_r64_s0_v1_p1 : List ℕ := [2000000000019572]
private def wc_rkmTraj_m1024_r64_s0_v1 : List ℕ := pCat wc_rkmTraj_m1024_r64_s0_v1_p0
  wc_rkmTraj_m1024_r64_s0_v1_p1
private def wc_rkmTraj_m1024_r64_s0_v2_p0 : List ℕ := [2000000000000006,2000000000000005,
  1999999999999999,2000000000000001,2000000000000006,2000000000000005,1999999999999992,
  2000000000000000,2000000000000009,2000000000000007,2000000000000002,1999999999999997,
  2000000000000006,2000000000000007,1999999999999996,1999999999999999,1999999999999998,
  2000000000000005,2000000000000004,2000000000000002,2000000000000002,2000000000000000,
  2000000000000009,2000000000000012,2000000000000007,1999999999999995,1999999999999996,
  2000000000000003,2000000000000006,2000000000000005,2000000000000000,2000000000000002,
  2000000000000005,2000000000000017,2000000000000007,2000000000000009,2000000000000013,
  2000000000000019,2000000000000008,2000000000000021,2000000000000011,2000000000000014,
  2000000000000007,2000000000000031,2000000000000008,2000000000000021,1999999999999996,
  2000000000000202,2000000000001255,1999999999998391,1999999999933366,1999999999714677,
  2000000001373335,2000000020587216,2000000066816504,1999999552336252,1999994137220829,
  1999976184256112,2000056940326557,2001453676571968,2011086972324537,2055064233197797,
  2197416776569314,2508143628748646]
private def wc_rkmTraj_m1024_r64_s0_v2_p1 : List ℕ := [2836456550657971]
private def wc_rkmTraj_m1024_r64_s0_v2 : List ℕ := pCat wc_rkmTraj_m1024_r64_s0_v2_p0
  wc_rkmTraj_m1024_r64_s0_v2_p1
private def wc_rkmTrajPack_m16_r96_s5_hb_p0 : List ℕ := [175921988923685,246717457684128,
  299624702742644,343040830172173,380246945045928,412939748539802,442135262745610,468500685602122,
  492503026122233,514484882993347,534706811208607,553372711098051,570645892309691,586659692065579,
  601524751209400,615334152924190,628167146452704,640091905882423,651167613838222,661446062173704,
  670972900206898,679788621211393,687929351452783,695427488148971,702312220350156,708609958020656,
  714344688373652,719538273988163,724210703911875,728380306476987,732063930690926,735277101643866,
  738034154283411,740348349059806,742231972282191,743696423503351,744752291834491,745409422758339,
  745676976740003,745563480716532,745076873367370,744224544920551,743013372127258,741449748935087,
  739539613304122,737288470536528,734701413427255,731783139488472,728537965451863,724969839209377,
  721082349313201,716878732118567,712361876617325,707534326975307,702398282751110,696955596737364,
  691207770326501,685155946260528,678800898576796,672143019507834,665182303030786,657918324688723,
  650350217218838,642476641417660]
private def wc_rkmTrajPack_m16_r96_s5_hb_p1 : List ℕ := [634295751545956,625805154419683,
  617001861139942,607882230173600,598441900192602,588675710694701,578577607935205,568140533062306,
  557356288518090,546215377673399,534706811208607,522817871791375,510533825928808,497837568176470,
  484709177704923,471125359839528,457058734476589,442476917431278,427341316811531,411605529386303,
  395213162782865,378094812152241,360163754306344,341309627950191,321388818876237,300209179562169,
  277504391301355,252887859077798,225761792607814,195113120176515,158954668177347,112128706798990]
private def wc_rkmTrajPack_m16_r96_s5_hb : List ℕ := pCat wc_rkmTrajPack_m16_r96_s5_hb_p0
  wc_rkmTrajPack_m16_r96_s5_hb_p1
private def wc_rkmTrajPack_m16_r96_s5_v0_p0 : List ℕ := [2000095657720370,2000099681019421,
  1999958250182550,2000042657833062,2000112758169541,1999961005244576,2000052648220250,
  1999883796184546,1999952857302991,1999897613612378,1999913171625297,1999959822844556,
  1999779197221116,2000539046998777,2000514558655677,2000809176480036,1998735262820185,
  1998224931669861,1997655879975277,2002601132643996,2002720041238427,2002493349002144,
  2001851125490734,1999622469825636,1999032933475925,1998236785788267,1998269035530724,
  1998917069912608,1999363299426903,1998108547823676,1998273701539418,1999869862194922,
  1998150846106097,1998009382949826,1999909906854421,1997860100038332,2002018522066651,
  2000989826056739,2002651493350739,1999368666833206,2002323014892344,1998178643129826,
  1998526211701981,1997402110659437,1999050435427826,1997399218291531,1999466110743610,
  1997766082177610,2000169550679012,1998126624839309,1999867930925625,1998051351891841,
  1999576786862813,1998780547834753,1999542090616770,1999375634996956,2000341232479247,
  2000071345365977,1999515091403950,2000101025054684,1998161034569880,2001538298119996,
  2002506215154198,2005931886539131]
private def wc_rkmTrajPack_m16_r96_s5_v0_p1 : List ℕ := [2002245526445536,2007806808575122,
  2013379626708454,2003418386112528,2019062952225108,2033919153971783,2018636144897528,
  2029696347137447,2084470308352966,2102241194288916,2050102101562585,2071982268477342,
  2229298052200042,2370870831784712,2454818716602646,2465109035315127,2412656534300500,
  2324279533375725,2228440905099324,2145321419252572,2083845998101066,2043976754059091,
  2020981061124847,2009097737946870,2003577190268965,2001270404766588,2000405082254562,
  2000114965394065,1999971326259270,1999993835180258,1999998892703285,1999999843229015,
  2000000015160603]
private def wc_rkmTrajPack_m16_r96_s5_v0 : List ℕ := pCat wc_rkmTrajPack_m16_r96_s5_v0_p0
  wc_rkmTrajPack_m16_r96_s5_v0_p1
private def wc_rkmTrajPack_m16_r96_s5_v1_p0 : List ℕ := [1999188620738732,1998917602223431,
  2000483097672120,1999981604607232,2001406655981290,1997535629083732,2002242681226759,
  1998703019084900,2001144567957531,1999202020550412,2000258044327222,1999030927806156,
  2001774873989593,1998931985447176,2000009896514978,1999242804770317,2001154036066369,
  2000165841029506,1998970715667230,2000442127753868,2000277853240172,2000168577886978,
  1999155319733719,2001624814745671,1998872849216816,1999970900283226,1999721587308032,
  2001293089761219,2000238878281154,1998296416555178,2001046087519075,1998594817801992,
  2001612261520953,2000196560014956,2000127657457190,2000464056753914,1997034576124221,
  2002127081432510,1998985512744864,2000499558723523,2002847978599776,1996752829383266,
  2004023676485822,1995094084060802,1999427741319276,1999701895715255,2001935281286287,
  1999069744158886,2005351340812752,1998679529579880,1995838183458995,2007425013729041,
  1988448800964685,2001883249698288,2007405488516838,1985410603728571,2012998530214035,
  2004360407282302,1986159032635901,2018235230375282,1996097748461720,1985297793899112,
  2020250651691769,1991984192655177]
private def wc_rkmTrajPack_m16_r96_s5_v1_p1 : List ℕ := [1986409112607947,2022099991338895,
  1988671450458173,1981108815853148,2022513580139712,1992845496343047,1977241188680559,
  2025461698990299,2006557187768696,1971215267216086,2015786234371550,2020327901235517,
  1967770626740489,1994680945880050,2036285128595262,1982955516791613,1960887673459539,
  2031747197452947,2031664066335133,1949470789641554,1971724192691166,2065438310403019,
  2023305459461364,1911074052127378,1969728153673361,2122752934295336,2070374857865878,
  1853479648518125,1862817326162075,2232446139056819,2606169902908333,2618184295459214,
  2326170270740584]
private def wc_rkmTrajPack_m16_r96_s5_v1 : List ℕ := pCat wc_rkmTrajPack_m16_r96_s5_v1_p0
  wc_rkmTrajPack_m16_r96_s5_v1_p1
private def wc_rkmTrajPack_m16_r96_s3_hb_p0 : List ℕ := [192570651428544,269499193351047,
  326593357480856,373105637142804,412659355937906,447132135673038,477650675146530,504956383331435,
  529569291428496,551871693796254,572154950962089,590647561401548,607532938140728,622961169090197,
  637057082583200,649925948571336,661657613528239,672329566570507,682009257368416,690755878417799,
  698621756215288,705653451828052,711892642118280,717376833057841,722139942857040,726212782978529,
  729623458201912,732397701891346,734559158929972,736129626037377,737129257116181,737576739697602,
  737489447343939,736883571925503,735774238953681,734175608571324,732100964340416,729562791597827,
  726572846852592,723142219457161,719281386588533,715000262414097,710308242184199,705214241883505,
  699726733981667,693853779747319,687603058525168,680981894321785,673997279999904,666655899342064,
  658964147211267,650928148007923,642553772597978,633846653866175,624812201030234,615455612836098,
  605781889740725,595795845177080,585502115985590,574905172087278,564009325465844,552818738518936,
  541337431832734,529569291428496]
private def wc_rkmTrajPack_m16_r96_s3_hb_p1 : List ℕ := [517518075524892,505187420855718,
  492580848578723,479701769807973,466553490799089,453139217814065,439462061689909,425525042133232,
  411331091760929,396883059905378,382183716201001,367235753967608,352041793404661,336604384609454,
  320926010431127,305009089171495,288855977142816,272468971091793,255850310498460,239002179757861,
  221926710251914,204625982318243,187102027122319,169356828438732,151392324347061,133210408847371,
  114812933400053,96201708394362,77378504549741,58345054253730,39103052839998,19654159809803]
private def wc_rkmTrajPack_m16_r96_s3_hb : List ℕ := pCat wc_rkmTrajPack_m16_r96_s3_hb_p0
  wc_rkmTrajPack_m16_r96_s3_hb_p1
private def wc_rkmTrajPack_m16_r96_s3_v0 : List ℕ := [2000128179727579,2000243761854045,
  2000298415630787,2000250907347873,2000111962264482,1999933342894957,1999775219707638,
  1999677906894466,2000348424162458,2000317938609609,2000255288759234,2000180230048284,
  2000090433742433,1999928984842999,2000491124488008,2001641154852611,2004521195386716,
  2010947167059473,2023703866308716,2046298958230386,2082045055047563,2132488591251217,
  2195640945393422,2264917834483191,2329699118703371,2377807268999775,2399205474413380,
  2389387767130057,2350900247040107,2292304314458813,2225141835451775,2160343189976197,
  2105560648518548,2064204923375888,2036047282981182,2018659027967143,2008890305671776,
  2003890782097783,2001559750835124,2000570724921920,2000189740904959,2000056975804617,
  1999984665248215,1999996338230010,1999999235019696,2000000137001501,2000000020368099,
  2000000002370381,2000000000187044]
private def wc_rkmTrajPack_m16_r96_s3_v1_p0 : List ℕ := [2000094634351731,2000106806057762,
  2000074513811011,2000051622687164,2000038626374496,1999993742118926,1999924274663913,
  1999905662413680,1999981714038248,2000090997821240,2000116011441463,2000032118149207,
  1999910248513201,1999887149593782,1999953950939073,2000075505551985,2000117086333347,
  2000091836086288,2000030335388762,1999988370567227,2000013345809777,2000062526199952,
  2000133550812495,2000219307231978,2000283180316749,2000322104117891,2000302520243366,
  2000194531442062,2000043273251038,1999898928788655,1999801090332844,1999796977687361,
  1999876643198791,1999985147865378,2000100704643246,2000211378699612,2000268650508823,
  2000211761140743,2000011164545918,1999762940621960,1999800229577548,2000517087055382,
  2001760851334453,2002267221099400,1999966904110466,1993622268841882,1985250034104549,
  1981693532941397,1993498406895749,2030606869992295,2096669301187486,2185217618342332,
  2280261049559711,2361416202635895,2411133966397654,2420560729905069,2391553239645448,
  2334536576049396,2263849427029859,2192948816000603,2131267085276400,2083293049063101,
  2049390394003666,2027408040416774]
private def wc_rkmTrajPack_m16_r96_s3_v1_p1 : List ℕ := [2014247914064373,2006942909842565,
  2003172444240137,2001359375742818,2000546148118145,2000205661706569,2000072550251138,
  2000023958923162,2000007400686812,2000002136091287,2000000575450522,2000000144497189,
  2000000033768723,2000000007331987,2000000001476120,2000000000274935,2000000000047249,
  2000000000007468,2000000000001079,2000000000000140,2000000000000015,2000000000000001,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000]
private def wc_rkmTrajPack_m16_r96_s3_v1 : List ℕ := pCat wc_rkmTrajPack_m16_r96_s3_v1_p0
  wc_rkmTrajPack_m16_r96_s3_v1_p1
private def wc_rkmTrajPack_m16_r96_s4_hb_p0 : List ℕ := [173619330896649,243488151684225,
  295702889266741,338550739274328,375269860114006,407534744694207,436348116306296,462368439877903,
  486056611700829,507750746158826,527707987818347,546129568140492,563176659199259,578980852954346,
  593651342061930,607279991331265,619945012704961,631713687934011,642644424996827,652788337838993,
  662190478270690,670890809545570,678924985069434,686324978010218,693119595360132,699334901401204,
  704994569375922,710120175702127,714731447789144,718846474068058,722481883008188,725652996490472,
  728373961831151,730657865913298,732516834229497,733962117122807,735004165102648,735652694783378,
  735916746727989,735804736263721,735324498159958,734483325913405,733288006264859,731744849470987,
  729859715769401,727638038402895,725084843506387,722204767105907,719002069431067,715480646699517,
  711644040492579,707495444804551,703037710813023,698273349383019,693204531282926,687833085054012,
  682160492436856,676187881216013,669916015297396,663345281779567,656475674718504,649306775213032,
  641837727352020,634067209460947]
private def wc_rkmTrajPack_m16_r96_s4_hb_p1 : List ℕ := [625993399959620,617613936988587,
  608925870770903,599925607437776,590608842746948,580970483742429,571004555917512,560704092814307,
  550061004173438,539065917667944,527707987818347,515974663750564,503851404819653,491321329475811,
  478364777635048,464958759528721,451076253433665,436685299044431,421747809601543,406217989249835,
  390040183741190,373145896672661,355449539983423,336842196906963,317182133014438,296279715818962,
  273872112482333,249577788163934,222806777108462,192559267783740,156874096869276,110661044522367]
private def wc_rkmTrajPack_m16_r96_s4_hb : List ℕ := pCat wc_rkmTrajPack_m16_r96_s4_hb_p0
  wc_rkmTrajPack_m16_r96_s4_hb_p1
private def wc_rkmTrajPack_m16_r96_s4_v0_p0 : List ℕ := [1999905365648269,2000106806057762,
  2000074513811011,2000051622687164,2000038626374496,1999993742118926,2000075725336087,
  1999905662413680,2000018285961752,1999909002178760,2000116011441463,2000032118149207,
  2000089751486799,2000112850406218,1999953950939073,1999924494448015,2000117086333347,
  2000091836086288,2000030335388762,1999988370567227,2000013345809777,2000062526199952,
  2000133550812495,2000219307231978,2000283180316749,2000322104117891,1999697479756634,
  1999805468557938,2000043273251038,1999898928788655,2000198909667156,2000203022312639,
  2000123356801209,2000014852134622,2000100704643246,2000211378699612,2000268650508823,
  2000211761140743,1999988835454082,1999762940621960,2000199770422452,1999482912944618,
  1998239148665547,1997732778900600,2000033095889534,1993622268841882,1985250034104549,
  1981693532941397,2006501593104251,2030606869992295,2096669301187486,2185217618342332,
  2280261049559711,2361416202635895,2411133966397654,2420560729905069,2391553239645448,
  2334536576049396,2263849427029859,2192948816000603,2131267085276400,2083293049063101,
  2049390394003666,2027408040416774]
private def wc_rkmTrajPack_m16_r96_s4_v0_p1 : List ℕ := [2014247914064373,2006942909842565,
  2003172444240137,2001359375742818,2000546148118145,2000205661706569,2000072550251138,
  2000023958923162,2000007400686812,2000002136091287,2000000575450522,2000000144497189,
  1999999966231277,1999999992668013,2000000001476120,2000000000274935,2000000000047249,
  1999999999992532,2000000000001079,2000000000000140,1999999999999985,1999999999999999,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000]
private def wc_rkmTrajPack_m16_r96_s4_v0 : List ℕ := pCat wc_rkmTrajPack_m16_r96_s4_v0_p0
  wc_rkmTrajPack_m16_r96_s4_v0_p1
private def wc_rkmTrajPack_m16_r96_s4_v1_p0 : List ℕ := [2000095657720370,2000099681019421,
  2000041749817450,2000042657833062,1999887241830459,1999961005244576,2000052648220250,
  1999883796184546,2000047142697009,1999897613612378,1999913171625297,1999959822844556,
  2000220802778884,1999460953001223,2000514558655677,1999190823519964,2001264737179815,
  1998224931669861,2002344120024723,1997398867356004,2002720041238427,1997506650997856,
  2001851125490734,1999622469825636,1999032933475925,2001763214211733,1998269035530724,
  2001082930087392,2000636700573097,1998108547823676,2001726298460582,1999869862194922,
  1998150846106097,2001990617050174,1999909906854421,1997860100038332,2002018522066651,
  2000989826056739,1997348506649261,2000631333166794,2002323014892344,1998178643129826,
  1998526211701981,2002597889340563,2000949564572174,1997399218291531,1999466110743610,
  2002233917822390,2000169550679012,1998126624839309,2000132069074375,2001948648108159,
  2000423213137187,1998780547834753,1999542090616770,2000624365003044,2000341232479247,
  2000071345365977,2000484908596050,1999898974945316,1998161034569880,1998461701880004,
  2002506215154198,2005931886539131]
private def wc_rkmTrajPack_m16_r96_s4_v1_p1 : List ℕ := [2002245526445536,1992193191424878,
  1986620373291546,1996581613887472,2019062952225108,2033919153971783,2018636144897528,
  1970303652862553,1915529691647034,1897758805711084,1949897898437415,2071982268477342,
  2229298052200042,2370870831784712,2454818716602646,2465109035315127,2412656534300500,
  2324279533375725,2228440905099324,2145321419252572,2083845998101066,2043976754059091,
  2020981061124847,2009097737946870,2003577190268965,2001270404766588,2000405082254562,
  2000114965394065,2000028673740730,2000006164819742,2000001107296715,2000000156770985,
  2000000015160603]
private def wc_rkmTrajPack_m16_r96_s4_v1 : List ℕ := pCat wc_rkmTrajPack_m16_r96_s4_v1_p0
  wc_rkmTrajPack_m16_r96_s4_v1_p1
private def wc_rkmTrajPack_m64_r62_s0_hb : List ℕ := [203075631949098,283751887837638,
  343303719609410,391532657192457,432281674745733,467544112500614,498516953879386,525988207142064,
  550510670735794,572490651580875,592237634679737,609994087809547,625954342632200,640277089111846,
  653093945558257,664515515942261,674635781491743,683535354729885,691283936335987,697942200542665,
  703563262521685,708193834391118,711875145383384,714643680601163,716531778160081,717568114190413,
  717778097750102,717184192277073,715806176173296,713661352053530,710764711821844,707129062855394,
  702765119028764,697681558990521,691885052915949,685380257828207,678169780431027,670254105152733,
  661631483675993,652297780510895,642246267016391,631467353487418,619948245218218,607672503410087,
  594619484790878,580763623898718,566073507657488,550510670735794,534028008281304,516567653259847,
  498058087082622,478410123209057,457511183747307,435216898938028,411338331314966,385621684472058,
  357714286152308,327103474414606,292996211789477,254049170795832,207630598345393,146923149648363]
private def wc_rkmTrajPack_m64_r62_s0_v1 : List ℕ := [2000356217058990,2001569843766706,
  2004827443199219,2011959028287462,2025310240036450,2047256087717585,2079426877767450,
  2121860474055148,2172400626309951,2226636511471022,2278512888083955,2321496469464573,
  2349969427195690,2360431050509949,2352159585186111,2327180366006096,2289616267125443,
  2244671026028382,2197560463111747,2152659237078284,2113012167381508,2080226060806910,
  2054657072149447,2035761859660616,2022485042556044,2013591997610529,2007902550473465,
  2004420681664388,2002379907101562,2001233273288100,2000615229486567,2000295470709225,
  2000136610386421,2000060800788004,2000026045135364,2000010736003745,2000004257298583,
  2000001623478722,2000000595103981,2000000209580338,2000000070869516,2000000022994194,
  2000000007152861,2000000002131307,2000000000607658,2000000000165576,2000000000043056,
  2000000000010664,2000000000002509,2000000000000558,2000000000000115,2000000000000020,
  2000000000000002,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000]
private def wc_rkmTrajPack_m64_r62_s1_hb : List ℕ := [197437543959507,275873945538573,
  333772410708710,380662344733684,420280027403254,454563456870034,484676384120729,511384939557023,
  535226574012682,556596313910464,575795051869465,593058523915487,608575666385552,622500763456799,
  634961779255559,646066247000579,655905538672997,664558028711127,672091482660255,678564890224633,
  684029891913560,688531902953753,692111007910305,694802678932168,696638356316060,697645920042843,
  697850073726370,697272657141162,695932899571753,693847623251953,691031403858276,687496693190407,
  683253907668394,678311484991247,672675910146911,666351710863337,659341421473069,651645512955011,
  643262285531215,634187718527402,624415270113068,613935616826820,602736319188566,590801394798002,
  578110773512232,564639599655793,550357332289145,535226574012682,519201527769105,502225933114982,
  484230257067039,465127789214205,444809077219648,423133759532190,399918144248767,374915481236937,
  347782889651885,318021940836453,284861614807896,246995879542312,201866048598252,142844050460170]
private def wc_rkmTrajPack_m64_r62_s1_v1 : List ℕ := [2000000000000693,2000000000008066,
  2000000000064939,2000000000418015,2000000002281527,2000000010905481,2000000046591521,
  2000000180435166,2000000639957319,2000002095059292,2000006369849342,2000018075934824,
  2000048070243201,2000120206076373,2000283459720101,2000631869683786,2001334264177767,
  2002673730736181,2005092545159937,2009231778046539,2015947229897980,2026277552757722,
  2041340592347029,2062144309449184,2089320947167949,2122824436833224,2161662483791515,
  2203753110946128,2245987795463779,2284543664383532,2315421516673873,2335113470729821,
  2341249840306270,2333062497499122,2311540959399466,2279237911521242,2239776415572623,
  2197188950465024,2155253123661329,2116971942500831,2084288851892262,2058053357639373,
  2038188185268024,2023971750729093,2014345201896675,2008174319173326,2004429567516990,
  2002279163031366,2001111553935108,2000512791551989,2000223239937975,2000091454762595,
  2000035139668752,2000012612641868,2000004208302976,2000001297348369,2000000366677910,
  2000000094050158,2000000021587645,2000000004345049,2000000000742578,2000000000101595,
  2000000000009631]
private def wc_rkmTrajPack_m32_r64_s1_hb : List ℕ := [233515754666624,325081129351119,
  391821740467557,445139407333252,489522282423501,527307379753374,559903556495008,588242043587740,
  612978855999888,634598296646552,653470993855581,669888782089695,684086834501835,696258333862495,
  706564553828821,715141998666536,722107591302233,727562527595363,731595195477448,734283423635252,
  735696239935622,735895265027843,734935830182107,732867883725028,729736733333200,725583659395031,
  720446426020992,714359710010873,707355463467464,699463222301769,690710370277099,681122366259489,
  670722940818013,659534267134953,647577110258655,634870957999884,621434136190197,607283910554402,
  592436577073070,576907542405957,560711395698106,543861972886102,526372414453316,508255217443230,
  489522282423501,470184955995996,450254069366164,429739973416030,408652570666592,387001344465618,
  364795385694439,342043417250917,318753816534617,294934636133243,270593622886190,245738235480880,
  220375660720039,194512828582798,168156426189175,141312910765764,113988521700256,86189291763319,
  57921057568449,29189469333328]
private def wc_rkmTrajPack_m32_r64_s1_v0 : List ℕ := [2000466689973620,2002236299890826,
  2007357984466041,2019183769939054,2042011027522109,2079757844014930,2133881103753151,
  2201365517895248,2273961148154292,2339517460951899,2385283912770791,2401947935865089,
  2386662079998154,2343742177202644,2282853446875603,2215657714267139,2152431454442905,
  2099889215167740,2060663385740573,2034113403329569,2017738749261901,2008513102076215,
  2003761027343324,2001524500224154,2000564514059098,2000189896557142,2000057605580777,
  2000015603997843,2000003722876390,2000000766767446,2000000132033424,2000000017924339,
  2000000001661592]
private def wc_rkmTrajPack_m32_r64_s1_v1_p0 : List ℕ := [2000000000000004,1999999999999979,
  2000000000000090,1999999999999711,2000000000000772,1999999999998222,2000000000003558,
  1999999999993807,2000000000009797,1999999999986525,2000000000007870,1999999999977806,
  2000000000091680,2000000000449923,2000000000300298,1999999994746659,1999999976860958,
  1999999980579602,2000000198571340,2000000968262818,2000001658669161,1999996879980104,
  1999971644019831,1999911367597934,1999871971797058,2000183927944664,2001843346968912,
  2007014189265991,2019333215882226,2043518606319958,2083887325458178,2141941525957651,
  2213996047145410,2290319440778098,2356880697969442,2399506458398510,2408779120845101,
  2383367809094912,2330207608749962,2261597276403061,2190798076105668,2128187872746616,
  2079346052617271,2045240659560854,2023748110907103,2011466970003252,2005086953163439,
  2002069970183120,2000771079403755,2000262299494043,2000081239936486,2000022827836658,
  2000005794577038,2000001321910821,2000000269339177,2000000048642108,2000000007713699,
  2000000001061514,2000000000124855,2000000000012298,2000000000000985,2000000000000059,
  2000000000000002,2000000000000000]
private def wc_rkmTrajPack_m32_r64_s1_v1_p1 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m32_r64_s1_v1 : List ℕ := pCat wc_rkmTrajPack_m32_r64_s1_v1_p0
  wc_rkmTrajPack_m32_r64_s1_v1_p1
private def wc_rkmTrajPack_m2_r64_s6_hb : List ℕ := [201472267248459,281468944729630,
  340490649530071,388266952581995,428613583876420,463510324752456,494146417937036,521305086483432,
  545536029001834,567243496995124,586735610230433,604253952004648,619992319929856,634109136013090,
  646735960504363,657983511010106,667946027847162,676704510080158,684329160262617,690881262064633,
  696414643232138,700976829845752,704609966985891,707351559961807,709235075754653,710290434092461,
  710544410233820,710020966184098,708741523102148,706725184669022,703988918901721,700547704106210,
  696414643232138,691601049711384,686116506853016,679968901963549,673164435507669,665707604768938,
  657601160558971,648846034497219,639441233168817,629383693970584,618668095547238,607286613222211,
  595228606482507,582480221005947,569023881352508,554837641405658,539894346574380,524160542451551,
  507595035444056,490146965697538,471753180672620,452334579454881,431790896333692,409993033988750,
  386771387702148,361897276475474,335051772613938,305769629730706,273328689325833,236501614047338,
  192876112744389,136183412926199]
private def wc_rkmTrajPack_m2_r64_s6_v0_p0 : List ℕ := [1999972964743301,1999853354952089,
  1999968053278106,2000129599866062,2000191184271428,2000162983604759,2000843224237364,
  2000297641981333,2000369313699597,2000693203047001,1999713239506796,1999354454815860,
  1999849734226673,2000233661717410,1998159771829059,1997825174790140,1997297616782211,
  1997809111081011,1996878405371090,2000544642068780,2005540036817990,2008027226002989,
  2002521753390935,2011945550947403,2006065928057305,2013386223902702,2012194571310426,
  2011555014529195,2016660607007491,2010579700426329,2018524799164306,2010735538341602,
  2019744381720135,2014219076345332,2019293206102898,2022228392425094,2013165739067709,
  2032026054399313,2002906679378045,2035768095365999,2028336119854579,2025283917686328,
  2067252349996747,2046399167713183,2024945267167787,2077565358678948,2043408564811617,
  2090007929017747,2271805493074603,2425014385922830,2494068842776698,2469129034239492,
  2378814498291840,2265615062626115,2163605777908672,2089071726345294,2042964083475427,
  2018346463175643,2006908689578456,2002277384648876,1999350612453278,2000157199317746,
  2000031320546064,2000004847764145]
private def wc_rkmTrajPack_m2_r64_s6_v0_p1 : List ℕ := [2000000505297550]
private def wc_rkmTrajPack_m2_r64_s6_v0 : List ℕ := pCat wc_rkmTrajPack_m2_r64_s6_v0_p0
  wc_rkmTrajPack_m2_r64_s6_v0_p1
private def wc_rkmTrajPack_m2_r64_s6_v1_p0 : List ℕ := [1999831794116095,2000770627250449,
  1999261478215416,2001068651487141,1998089160892972,2002455918342537,1997117778342525,
  2002779005094625,1999958491526551,1996442708980463,2005555735567511,1994134195350644,
  2003509054205555,2000164322955928,1997885827095596,2002623797378758,1993633726938567,
  2010856403392028,1988938380755489,2008343416341136,1994052273571638,2001266436618408,
  2006127181172053,1991230689947894,2006273982590121,2002106435640603,1990471980505389,
  2018036589898979,1981585862024814,2006095441037761,2010478689011029,1980316174702903,
  2022229616697282,1991153454603787,1986740006211411,2016833994850420,1981356971155925,
  1996124698535644,2015336021611957,1984134319833151,2003610059087919,2019485408869730,
  1990258704477485,2006489420019425,2028767268228922,2001045028568125,2002945811494739,
  2034819235968356,2012184195977596,1989712797589477,2035716084405953,2060293010708072,
  1991746521070902,1956565890189738,2050409471530455,2136017093180852,2053009370883707,
  1895051813913257,1915071631841180,2184331920525756,2494482646426528,2605127941782512,
  2477839945606556,2254147046979487]
private def wc_rkmTrajPack_m2_r64_s6_v1_p1 : List ℕ := [2082360231541345]
private def wc_rkmTrajPack_m2_r64_s6_v1 : List ℕ := pCat wc_rkmTrajPack_m2_r64_s6_v1_p0
  wc_rkmTrajPack_m2_r64_s6_v1_p1
private abbrev dP_0 : Prop := atF [ bNLE (bEvalLo12W 32 256 64 [1,2,4,4,4,4,4,4]
  [40668184,32838153,17130215,16876030,5635382,1144241,1041403,863528] [13,18,15,15,5,1,1,1]
  rkmMasksPack_m32_r64 [none, some (18, 65, wc_rkmTrajPack_m32_r64_s1_hb,
  wc_rkmTrajPack_m32_r64_s1_v0, wc_rkmTrajPack_m32_r64_s1_v1)]) rkmRowPack_m32_r64, bNLE
  (bEvalLo12W 4 2048 27 [1,1,4,7,7,7,7,7]
  [50163741,23969036,51251155,121692,8421970,8276174,4837051,5360458] [2,1,6,1,2,2,1,1]
  rkmMasksPack_m4_r27 []) rkmRowPack_m4_r27] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bNLE (bEvalLo12W 512 16 48 [1,1,1] [33587572,1484924,303173]
  [51,3,1] rkmMasks_m512_r48 []) rkmRow_m512_r48, bNLE (bEvalLo12W 256 32 19 [1,1]
  [48310423,1005130] [23,2] rkmMasks_m256_r19 []) rkmRow_m256_r19] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bSlideChk 27 97 wc_rkmTrajPack_m16_r96_s5_hb
  wc_rkmTrajPack_m16_r96_s5_v0 wc_rkmTrajPack_m16_r96_s5_v1, bNLE (bEvalLo12W 512 16 20 [1,1,1]
  [33393723,1116356,87749] [23,2,2] rkmMasks_m512_r20 []) rkmRow_m512_r20] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bNLE (bEvalLo12W 2 4096 64 [1,3,7,15,30,58,58,58]
  [17714062,22686081,23071912,24344206,27900460,15514387,17537091,6486197] [1,2,4,8,15,13,15,6]
  rkmMasksPack_m2_r64 [none, none, none, none, none, none, some (15, 65,
  wc_rkmTrajPack_m2_r64_s6_hb, wc_rkmTrajPack_m2_r64_s6_v0, wc_rkmTrajPack_m2_r64_s6_v1)])
  rkmRowPack_m2_r64, bNLE (bEvalLo12W 256 32 24 [1,1,1] [47500000,1506750,728475] [26,1,1]
  rkmMasks_m256_r24 []) rkmRow_m256_r24] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bNLE (bEvalLo12W 64 128 62 [2,2,2,2,2,2,2,2]
  [21656117,15514113,15492665,11444016,6461875,3498117,4741889,2271741] [19,14,14,10,6,3,4,2]
  rkmMasksPack_m64_r62 [some (19, 63, wc_rkmTrajPack_m64_r62_s0_hb, wc_rkmTraj_m1024_r64_s0_v0,
  wc_rkmTrajPack_m64_r62_s0_v1), some (14, 63, wc_rkmTrajPack_m64_r62_s1_hb,
  wc_rkmTrajPack_m64_r62_s0_v1, wc_rkmTrajPack_m64_r62_s1_v1)]) rkmRowPack_m64_r62, bNLE
  (bEvalLo12W 32 256 112 [1,1,1,1,1,1,1,1]
  [6211408,7329214,8379450,3331055,488897,4143660,4580583,5224108] [3,4,4,2,1,2,2,3]
  rkmMasksPack_m32_r112 []) rkmRowPack_m32_r112] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bSlideChk 18 129 wc_rkmTraj_m16_r128_s4_hb
  wc_rkmTraj_m16_r128_s4_v0 wc_rkmTraj_m16_r128_s4_v1, bSlideChk 14 63
  wc_rkmTrajPack_m64_r62_s1_hb wc_rkmTrajPack_m64_r62_s0_v1 wc_rkmTrajPack_m64_r62_s1_v1] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bSlideChk 18 129 wc_rkmTraj_m16_r128_s5_hb
  wc_rkmTraj_m16_r128_s5_v0 wc_rkmTraj_m16_r128_s5_v1, bNLE (bEvalLo12W 32 256 26 [1,2,2]
  [86887182,38106168,13406843] [16,11,5] rkmMasks_m32_r26 []) rkmRow_m32_r26] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bSlideChk 34 65 wc_rkmTraj_m1024_r64_s0_hb
  wc_rkmTraj_m1024_r64_s0_v0 wc_rkmTraj_m1024_r64_s0_v1, bSlideChk 15 65
  wc_rkmTrajPack_m2_r64_s6_hb wc_rkmTrajPack_m2_r64_s6_v0 wc_rkmTrajPack_m2_r64_s6_v1] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := atF [ bSlideChk 34 65 wc_rkmTraj_m1024_r64_s0_hb
  wc_rkmTraj_m1024_r64_s0_v1 wc_rkmTraj_m1024_r64_s0_v2, bNLE (bEvalLo12W 4 2048 36
  [1,2,4,8,14,14,14] [34024059,25117587,33637500,32506582,38578828,1453995,406519]
  [2,2,5,8,13,1,1] rkmMasks_m4_r36 []) rkmRow_m4_r36] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := atF [ bSlideChk 17 129 wc_rkmTraj_m16_r128_s4_hb
  wc_rkmTraj_m16_r128_s4_v1 wc_rkmTraj_m16_r128_s4_v2, bNLE (bEvalLo12W 64 128 25
  [1,1,1,1,1,1,1,1] [29408500,14315537,28551416,12117796,8981266,7142578,5337284,3622535]
  [8,4,8,4,3,2,2,1] rkmMasksPack_m64_r25 []) rkmRowPack_m64_r25, bNLE (bEvalLo12W 4 2048 22
  [1,1,3,6,6,6,6,6] [51841578,31700079,64191124,100748,1159203,1848828,1289415,697232]
  [2,1,5,1,1,1,1,1] rkmMasksPack_m4_r22 []) rkmRowPack_m4_r22] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := atF [ bSlideChk 17 129 wc_rkmTraj_m16_r128_s5_hb
  wc_rkmTraj_m16_r128_s5_v1 wc_rkmTraj_m16_r128_s5_v2, bNLE (bEvalLo12W 4 2048 28
  [1,2,4,8,13,13,13] [29840015,34414958,35655750,26505367,58659546,6582451,3415679]
  [2,3,4,5,15,2,1] rkmMasks_m4_r28 []) rkmRow_m4_r28, bNLE (bEvalLo12W 8 1024 23 [1,1,2,3,3,3,3,3]
  [16504451,76610684,39120830,38193,271058,1967444,5411484,617008] [1,5,4,1,1,1,1,1]
  rkmMasksPack_m8_r23 []) rkmRowPack_m8_r23] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := atF [ bSlideChk 21 97 wc_rkmTrajPack_m16_r96_s3_hb
  wc_rkmTrajPack_m16_r96_s3_v0 wc_rkmTrajPack_m16_r96_s3_v1, bSlideChk 18 65
  wc_rkmTrajPack_m32_r64_s1_hb wc_rkmTrajPack_m32_r64_s1_v0 wc_rkmTrajPack_m32_r64_s1_v1] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := atF [ bSlideChk 21 97 wc_rkmTrajPack_m16_r96_s4_hb
  wc_rkmTrajPack_m16_r96_s4_v0 wc_rkmTrajPack_m16_r96_s4_v1, bNLE (bEvalLo12W 1024 8 31 [1]
  [24526307] [36] rkmMasks_m1024_r31 []) rkmRow_m1024_r31] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := atF [ bNLE (bEvalLo12W 16 512 128 [1,2,4,8,15,15,15,15]
  [18499720,20979859,19492500,15856869,13624962,13761647,3431457,1167565] [6,11,19,26,35,35,9,3]
  rkmMasks_m16_r128 [none, none, some (19, 65, wc_rkmTraj_m16_r128_s2_hb,
  wc_rkmTraj_m16_r128_s2_v0, wc_rkmTraj_m16_r128_s2_v1), some (26, 129, wc_rkmTraj_m16_r128_s3_hb,
  wc_rkmTraj_m16_r128_s3_v0, wc_rkmTraj_m16_r128_s3_v2), some (35, 129, wc_rkmTraj_m16_r128_s4_hb,
  wc_rkmTraj_m16_r128_s4_v0, wc_rkmTraj_m16_r128_s4_v2), some (35, 129, wc_rkmTraj_m16_r128_s5_hb,
  wc_rkmTraj_m16_r128_s5_v0, wc_rkmTraj_m16_r128_s5_v2)]) rkmRow_m16_r128, bSlideChk 19 63
  wc_rkmTrajPack_m64_r62_s0_hb wc_rkmTraj_m1024_r64_s0_v0 wc_rkmTrajPack_m64_r62_s0_v1] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := atF [ bNLE (bEvalLo12W 64 128 40 [1,1,1]
  [116833671,5562986,1280343] [44,3,1] rkmMasksPack_m64_r40 []) rkmRowPack_m64_r40, bNLE
  (bEvalLo12W 128 64 31 [1,1,1] [63008009,6800978,3727240] [31,5,3] rkmMasks_m128_r31 [])
  rkmRow_m128_r31] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := atF [ bNLE (bEvalLo12W 8 1024 44 [1,2,4,8,10,10,10]
  [27577610,29670000,24395184,17250000,47292838,5831805,1629471] [3,5,7,8,23,3,1] rkmMasks_m8_r44
  []) rkmRow_m8_r44, bNLE (bEvalLo12W 16 512 34 [1,3,3,3] [66292799,88522892,19217130,6099785]
  [8,24,6,2] rkmMasksPack_m16_r34 []) rkmRowPack_m16_r34] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := atF [ bNLE (bEvalLo12W 16 512 96 [1,2,3,6,10,10,10,10]
  [26046285,17334127,16898415,21062415,14709292,19162770,5440070,1538258] [6,7,10,21,21,27,8,3]
  rkmMasksPack_m16_r96 [none, none, none, some (21, 97, wc_rkmTrajPack_m16_r96_s3_hb,
  wc_rkmTrajPack_m16_r96_s3_v0, wc_rkmTrajPack_m16_r96_s3_v1), some (21, 97,
  wc_rkmTrajPack_m16_r96_s4_hb, wc_rkmTrajPack_m16_r96_s4_v0, wc_rkmTrajPack_m16_r96_s4_v1), some
  (27, 97, wc_rkmTrajPack_m16_r96_s5_hb, wc_rkmTrajPack_m16_r96_s5_v0,
  wc_rkmTrajPack_m16_r96_s5_v1)]) rkmRowPack_m16_r96, bSlideChk 19 65 wc_rkmTraj_m16_r128_s2_hb
  wc_rkmTraj_m16_r128_s2_v0 wc_rkmTraj_m16_r128_s2_v1] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := atF [ bSlideChk 13 129 wc_rkmTraj_m16_r128_s3_hb
  wc_rkmTraj_m16_r128_s3_v0 wc_rkmTraj_m16_r128_s3_v1, bNLE (bEvalLo12W 64 128 34 [1,1,1]
  [98513554,13309357,5187973] [33,5,2] rkmMasksPack_m64_r34 []) rkmRowPack_m64_r34] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := atF [ bSlideChk 13 129 wc_rkmTraj_m16_r128_s3_hb
  wc_rkmTraj_m16_r128_s3_v1 wc_rkmTraj_m16_r128_s3_v2, bNLE (bEvalLo12W 64 128 32
  [1,1,1,1,1,1,1,1] [43806884,43093995,3607668,3552439,6599010,4429755,5689039,4353434]
  [15,14,2,2,3,2,2,2] rkmMasks_m64_r32 []) rkmRow_m64_r32, bNLE (bEvalLo12W 8 1024 9 [1,2,2,2]
  [127798867,100017505,27011348,11305399] [5,6,3,2] rkmMasks_m8_r9 []) rkmRow_m8_r9] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := atF [ bNLE (bEvalLo12W 16 512 29 [1,3,3,3]
  [64173744,88547038,11233221,4342022] [8,24,4,3] rkmMasks_m16_r29 []) rkmRow_m16_r29, bNLE
  (bEvalLo12W 4 2048 80 [1,1,10,20,20,20,20,20]
  [26438868,24834419,9490642,1067257,1456990,1009681,5321915,2149456] [2,2,5,1,2,1,4,2]
  rkmMasksPack_m4_r80 []) rkmRowPack_m4_r80, bNLE (bEvalLo12W 8 1024 24 [1,2,4,6,6,6]
  [48189328,44850000,27810509,61054791,4742075,1707735] [3,5,5,13,2,1] rkmMasks_m8_r24 [])
  rkmRow_m8_r24, bNLE (bEvalLo12W 4 2048 20 [1,2,4,8,9,9,9]
  [42628593,39333965,35362500,24395184,70500000,3966667,929339] [2,3,4,4,11,1,1] rkmMasks_m4_r20
  []) rkmRow_m4_r20] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := atF [ bNLE (bEvalLo12W 8 1024 24 [1,2,4,6,6,6]
  [52249978,37863176,41846521,52723056,5705455,863417] [3,4,7,11,2,1] rkmMasksPack_m8_r24 [])
  rkmRowPack_m8_r24, bNLE (bEvalLo12W 16 512 20 [1,2,2,2] [94129778,75074434,24767509,9490443]
  [8,11,4,2] rkmMasksPack_m16_r20 []) rkmRowPack_m16_r20, bNLE (bEvalLo12W 128 64 17 [1,1]
  [69381935,1331272] [20,2] rkmMasks_m128_r17 []) rkmRow_m128_r17, bNLE (bEvalLo12W 32 256 16
  [1,1,1,1,1,1,1,1] [37649988,44428369,30835885,13781698,14613796,10214694,4632432,4221734]
  [5,6,4,2,2,2,1,1] rkmMasksPack_m32_r16 []) rkmRowPack_m32_r16, bNLE (bEvalLo12W 64 128 16
  [1,1,1,1,1,1] [46642985,46601578,3029804,3389167,1545636,2151937] [9,9,1,1,1,1] rkmMasks_m64_r16
  []) rkmRow_m64_r16, bNLE (bEvalLo12W 1024 8 64 [1,1,1,1] [23750000,735000,214375,142187]
  [68,3,1,1] rkmMasks_m1024_r64 [some (68, 65, wc_rkmTraj_m1024_r64_s0_hb,
  wc_rkmTraj_m1024_r64_s0_v0, wc_rkmTraj_m1024_r64_s0_v2)]) rkmRow_m1024_r64, bNLE (bEvalLo12W 128
  64 14 [1,1,1] [65404369,3548305,1058532] [16,2,2] rkmMasks_m128_r14 []) rkmRow_m128_r14, bNLE
  (bEvalLo12W 512 16 14 [1,1] [33608007,696413] [17,2] rkmMasks_m512_r14 []) rkmRow_m512_r14] =
  true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := atF [ bNLE (bEvalLo12W 8 1024 26 [1,1,2,4,4,4,4,4]
  [41237546,41842717,48025010,3299526,1162021,2183375,3277479,848013] [3,3,5,1,1,1,1,1]
  rkmMasksPack_m8_r26 []) rkmRowPack_m8_r26, bNLE (bEvalLo12W 128 64 12 [1,1,1,1]
  [66690214,1777973,556999,463911] [14,2,2,2] rkmMasks_m128_r12 []) rkmRow_m128_r12, bNLE
  (bEvalLo12W 4 2048 12 [1,2,4,5,5,5,5,5]
  [62011962,58821775,75245067,32884473,26481042,10220492,4292606,1802894] [2,3,5,3,2,1,1,1]
  rkmMasks_m4_r12 []) rkmRow_m4_r12, bNLE (bEvalLo12W 128 64 10 [1,1,1,1]
  [66409023,1708659,434067,336439] [12,2,2,2] rkmMasks_m128_r10 []) rkmRow_m128_r10, bNLE
  (bEvalLo12W 32 256 10 [1,1,1,1,1,1,1,1]
  [34593923,30105611,38926467,11029738,10488084,7478425,8868250,5498883] [3,3,4,1,1,1,1,1]
  rkmMasksPack_m32_r10 []) rkmRowPack_m32_r10, bNLE (bEvalLo12W 128 64 4 [1,1] [65202010,119578]
  [6,2] rkmMasks_m128_r4 []) rkmRow_m128_r4, bNLE (bEvalLo12W 32 256 5 [1,1,1,1,1]
  [72678137,37658633,15927923,7294528,2389674] [4,2,1,1,1] rkmMasks_m32_r5 []) rkmRow_m32_r5, bNLE
  (bEvalLo12W 2 4096 6 [1,2,4,5,5,5,5,5]
  [66751156,72087715,91108337,37449849,37449849,11589212,4867468,2044337] [1,2,3,2,2,1,1,1]
  rkmMasks_m2_r6 []) rkmRow_m2_r6, bNLE (bEvalLo12W 1024 8 8 [1] [23810432] [11] rkmMasks_m1024_r8
  []) rkmRow_m1024_r8, bNLE (bEvalLo12W 256 32 7 [1,1,1] [47226563,306095,50916] [10,2,2]
  rkmMasks_m256_r7 []) rkmRow_m256_r7, bNLE (bEvalLo12W 32 256 9 [1,1,1]
  [124067107,15336274,5541798] [10,3,2] rkmMasks_m32_r9 []) rkmRow_m32_r9, bNLE (bEvalLo12W 16 512
  4 [1,1,1,1,1] [108046819,51177636,12678224,14894374,5943115] [3,2,1,1,1] rkmMasksPack_m16_r4 [])
  rkmRowPack_m16_r4, bNLE (bEvalLo12W 4 2048 44 [1,1,1,1,1,1,1,1]
  [14817684,26275815,18780874,9626964,16956087,8064996,11789,10382784] [1,2,1,1,1,1,1,1]
  rkmMasksPack_m4_r44 []) rkmRowPack_m4_r44, bNLE (bEvalLo12W 4 2048 4 [1,1,2,2,2,2,2,2]
  [122806080,136487217,44082527,45128558,11429408,5467569,6827020,2950095] [2,2,1,1,1,1,1,1]
  rkmMasksPack_m4_r4 []) rkmRowPack_m4_r4, bNLE (bEvalLo12W 32 256 6 [1,1,1,1,1,1,1,1]
  [27566359,29156120,15699371,33260528,15137778,6733037,7619625,3319621] [2,2,1,2,1,1,1,1]
  rkmMasksPack_m32_r6 []) rkmRowPack_m32_r6, bNLE (bEvalLo12W 8 1024 40 [1,1,1,1,1,1,1,1]
  [19458533,10935682,32705802,10098822,5923382,17372313,12304828,8370911] [2,1,3,1,1,2,1,1]
  rkmMasksPack_m8_r40 []) rkmRowPack_m8_r40, bNLE (bEvalLo12W 8 1024 8 [1,1,1,1,2,2,2,2]
  [51917897,21666629,53497923,44872377,30784751,35129397,27441406,13331545] [2,1,2,2,2,2,2,1]
  rkmMasksPack_m8_r8 []) rkmRowPack_m8_r8] = true
private theorem bk_21 : dP_21 := by decide +kernel
private theorem ws_rkmTraj_m16_r128_s3 : WalkOk (some (26, 129, wc_rkmTraj_m16_r128_s3_hb,
    wc_rkmTraj_m16_r128_s3_v0, wc_rkmTraj_m16_r128_s3_v2)) := mIter_split rfl
    (bSlideChk_sound bk_17) (bSlideChk_sound bk_18)
private theorem ws_rkmTraj_m16_r128_s4 : WalkOk (some (35, 129, wc_rkmTraj_m16_r128_s4_hb,
    wc_rkmTraj_m16_r128_s4_v0, wc_rkmTraj_m16_r128_s4_v2)) := mIter_split rfl
    (bSlideChk_sound bk_5) (bSlideChk_sound bk_9)
private theorem ws_rkmTraj_m16_r128_s5 : WalkOk (some (35, 129, wc_rkmTraj_m16_r128_s5_hb,
    wc_rkmTraj_m16_r128_s5_v0, wc_rkmTraj_m16_r128_s5_v2)) := mIter_split rfl
    (bSlideChk_sound bk_6) (bSlideChk_sound bk_10)
private theorem ws_rkmTraj_m1024_r64_s0 : WalkOk (some (68, 65, wc_rkmTraj_m1024_r64_s0_hb,
    wc_rkmTraj_m1024_r64_s0_v0, wc_rkmTraj_m1024_r64_s0_v2)) := mIter_split rfl
    (bSlideChk_sound bk_7) (bSlideChk_sound bk_8)
/-- Kernel trajectory certificate `(m = 16, r = 128)`. -/
theorem rkmTraj_m16_r128 : rkmEvalT16Lo12 16 512 128 [1, 2, 4, 8, 15, 15, 15, 15] [18499720,
  20979859, 19492500, 15856869, 13624962, 13761647, 3431457, 1167565] [6, 11, 19, 26, 35, 35, 9, 3]
  rkmMasks_m16_r128 = rkmRow_m16_r128 :=
    bhW_eq bk_13 (wSkip (wSkip (wCons (bSlideChk_sound (tl1 bk_16)) (wCons ws_rkmTraj_m16_r128_s3
      (wCons ws_rkmTraj_m16_r128_s4 (wCons ws_rkmTraj_m16_r128_s5 wNil))))))
/-- Kernel trajectory certificate `(m = 4, r = 20)`. -/
theorem rkmTraj_m4_r20 : rkmEvalT16Lo12 4 2048 20 [1, 2, 4, 8, 9, 9, 9] [42628593, 39333965,
  35362500, 24395184, 70500000, 3966667, 929339] [2, 3, 4, 4, 11, 1, 1] rkmMasks_m4_r20 =
  rkmRow_m4_r20 := bh0_eq (tl1 (tl2 bk_19))
/-- Kernel trajectory certificate `(m = 128, r = 4)`. -/
theorem rkmTraj_m128_r4 : rkmEvalT16Lo12 128 64 4 [1, 1] [65202010, 119578] [6, 2] rkmMasks_m128_r4
  = rkmRow_m128_r4 := bh0_eq (tl1 (tl2 (tl2 bk_21)))
/-- Kernel trajectory certificate `(m = 1024, r = 64)`. -/
theorem rkmTraj_m1024_r64 : rkmEvalT16Lo12 1024 8 64 [1, 1, 1, 1] [23750000, 735000, 214375, 142187]
  [68, 3, 1, 1] rkmMasks_m1024_r64 = rkmRow_m1024_r64 :=
    bhW_eq (tl1 (tl2 (tl2 bk_20))) (wCons ws_rkmTraj_m1024_r64_s0 wNil)
/-- Kernel trajectory certificate `(m = 32, r = 5)`. -/
theorem rkmTraj_m32_r5 : rkmEvalT16Lo12 32 256 5 [1, 1, 1, 1, 1] [72678137, 37658633, 15927923,
  7294528, 2389674] [4, 2, 1, 1, 1] rkmMasks_m32_r5 = rkmRow_m32_r5 :=
    bh0_eq (tl2 (tl2 (tl2 bk_21)))
/-- Kernel trajectory certificate `(m = 512, r = 48)`. -/
theorem rkmTraj_m512_r48 : rkmEvalT16Lo12 512 16 48 [1, 1, 1] [33587572, 1484924, 303173] [51, 3, 1]
  rkmMasks_m512_r48 = rkmRow_m512_r48 := bh0_eq bk_1
/-- Kernel trajectory certificate `(m = 2, r = 6)`. -/
theorem rkmTraj_m2_r6 : rkmEvalT16Lo12 2 4096 6 [1, 2, 4, 5, 5, 5, 5, 5] [66751156, 72087715,
  91108337, 37449849, 37449849, 11589212, 4867468, 2044337] [1, 2, 3, 2, 2, 1, 1, 1] rkmMasks_m2_r6
  = rkmRow_m2_r6 := bh0_eq (tl1 (tl2 (tl2 (tl2 bk_21))))
/-- Kernel trajectory certificate `(m = 8, r = 44)`. -/
theorem rkmTraj_m8_r44 : rkmEvalT16Lo12 8 1024 44 [1, 2, 4, 8, 10, 10, 10] [27577610, 29670000,
  24395184, 17250000, 47292838, 5831805, 1629471] [3, 5, 7, 8, 23, 3, 1] rkmMasks_m8_r44 =
  rkmRow_m8_r44 := bh0_eq bk_15
/-- Kernel trajectory certificate `(m = 1024, r = 8)`. -/
theorem rkmTraj_m1024_r8 : rkmEvalT16Lo12 1024 8 8 [1] [23810432] [11] rkmMasks_m1024_r8 =
  rkmRow_m1024_r8 := bh0_eq (tl2 (tl2 (tl2 (tl2 bk_21))))
/-- Kernel trajectory certificate `(m = 64, r = 32)`. -/
theorem rkmTraj_m64_r32 : rkmEvalT16Lo12 64 128 32 [1, 1, 1, 1, 1, 1, 1, 1] [43806884, 43093995,
  3607668, 3552439, 6599010, 4429755, 5689039, 4353434] [15, 14, 2, 2, 3, 2, 2, 2] rkmMasks_m64_r32
  = rkmRow_m64_r32 := bh0_eq (tl1 bk_18)
/-- Kernel trajectory certificate `(m = 256, r = 7)`. -/
theorem rkmTraj_m256_r7 : rkmEvalT16Lo12 256 32 7 [1, 1, 1] [47226563, 306095, 50916] [10, 2, 2]
  rkmMasks_m256_r7 = rkmRow_m256_r7 := bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 bk_21)))))
/-- Kernel trajectory certificate `(m = 128, r = 31)`. -/
theorem rkmTraj_m128_r31 : rkmEvalT16Lo12 128 64 31 [1, 1, 1] [63008009, 6800978, 3727240] [31, 5,
  3] rkmMasks_m128_r31 = rkmRow_m128_r31 := bh0_eq (tl1 bk_14)
/-- Kernel trajectory certificate `(m = 32, r = 9)`. -/
theorem rkmTraj_m32_r9 : rkmEvalT16Lo12 32 256 9 [1, 1, 1] [124067107, 15336274, 5541798] [10, 3, 2]
  rkmMasks_m32_r9 = rkmRow_m32_r9 := bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 bk_21)))))
/-- Kernel trajectory certificate `(m = 1024, r = 31)`. -/
theorem rkmTraj_m1024_r31 : rkmEvalT16Lo12 1024 8 31 [1] [24526307] [36] rkmMasks_m1024_r31 =
  rkmRow_m1024_r31 := bh0_eq (tl1 bk_12)
/-- Kernel trajectory certificate `(m = 8, r = 9)`. -/
theorem rkmTraj_m8_r9 : rkmEvalT16Lo12 8 1024 9 [1, 2, 2, 2] [127798867, 100017505, 27011348,
  11305399] [5, 6, 3, 2] rkmMasks_m8_r9 = rkmRow_m8_r9 := bh0_eq (tl2 bk_18)
/-- Kernel trajectory certificate `(m = 16, r = 29)`. -/
theorem rkmTraj_m16_r29 : rkmEvalT16Lo12 16 512 29 [1, 3, 3, 3] [64173744, 88547038, 11233221,
  4342022] [8, 24, 4, 3] rkmMasks_m16_r29 = rkmRow_m16_r29 := bh0_eq bk_19
/-- Kernel trajectory certificate `(m = 128, r = 10)`. -/
theorem rkmTraj_m128_r10 : rkmEvalT16Lo12 128 64 10 [1, 1, 1, 1] [66409023, 1708659, 434067, 336439]
  [12, 2, 2, 2] rkmMasks_m128_r10 = rkmRow_m128_r10 := bh0_eq (tl1 (tl2 bk_21))
/-- Kernel trajectory certificate `(m = 4, r = 36)`. -/
theorem rkmTraj_m4_r36 : rkmEvalT16Lo12 4 2048 36 [1, 2, 4, 8, 14, 14, 14] [34024059, 25117587,
  33637500, 32506582, 38578828, 1453995, 406519] [2, 2, 5, 8, 13, 1, 1] rkmMasks_m4_r36 =
  rkmRow_m4_r36 := bh0_eq (tl1 bk_8)
/-- Kernel trajectory certificate `(m = 4, r = 12)`. -/
theorem rkmTraj_m4_r12 : rkmEvalT16Lo12 4 2048 12 [1, 2, 4, 5, 5, 5, 5, 5] [62011962, 58821775,
  75245067, 32884473, 26481042, 10220492, 4292606, 1802894] [2, 3, 5, 3, 2, 1, 1, 1] rkmMasks_m4_r12
  = rkmRow_m4_r12 := bh0_eq (tl2 bk_21)
/-- Kernel trajectory certificate `(m = 32, r = 26)`. -/
theorem rkmTraj_m32_r26 : rkmEvalT16Lo12 32 256 26 [1, 2, 2] [86887182, 38106168, 13406843] [16, 11,
  5] rkmMasks_m32_r26 = rkmRow_m32_r26 := bh0_eq (tl1 bk_6)
/-- Kernel trajectory certificate `(m = 128, r = 12)`. -/
theorem rkmTraj_m128_r12 : rkmEvalT16Lo12 128 64 12 [1, 1, 1, 1] [66690214, 1777973, 556999, 463911]
  [14, 2, 2, 2] rkmMasks_m128_r12 = rkmRow_m128_r12 := bh0_eq (tl1 bk_21)
/-- Kernel trajectory certificate `(m = 4, r = 28)`. -/
theorem rkmTraj_m4_r28 : rkmEvalT16Lo12 4 2048 28 [1, 2, 4, 8, 13, 13, 13] [29840015, 34414958,
  35655750, 26505367, 58659546, 6582451, 3415679] [2, 3, 4, 5, 15, 2, 1] rkmMasks_m4_r28 =
  rkmRow_m4_r28 := bh0_eq (tl1 bk_10)
/-- Kernel trajectory certificate `(m = 512, r = 14)`. -/
theorem rkmTraj_m512_r14 : rkmEvalT16Lo12 512 16 14 [1, 1] [33608007, 696413] [17, 2]
  rkmMasks_m512_r14 = rkmRow_m512_r14 := bh0_eq (tl1 (tl2 (tl2 (tl2 bk_20))))
/-- Kernel trajectory certificate `(m = 256, r = 24)`. -/
theorem rkmTraj_m256_r24 : rkmEvalT16Lo12 256 32 24 [1, 1, 1] [47500000, 1506750, 728475] [26, 1, 1]
  rkmMasks_m256_r24 = rkmRow_m256_r24 := bh0_eq (tl1 bk_3)
/-- Kernel trajectory certificate `(m = 128, r = 14)`. -/
theorem rkmTraj_m128_r14 : rkmEvalT16Lo12 128 64 14 [1, 1, 1] [65404369, 3548305, 1058532] [16, 2,
  2] rkmMasks_m128_r14 = rkmRow_m128_r14 := bh0_eq (tl2 (tl2 (tl2 bk_20)))
/-- Kernel trajectory certificate `(m = 8, r = 24)`. -/
theorem rkmTraj_m8_r24 : rkmEvalT16Lo12 8 1024 24 [1, 2, 4, 6, 6, 6] [48189328, 44850000, 27810509,
  61054791, 4742075, 1707735] [3, 5, 5, 13, 2, 1] rkmMasks_m8_r24 = rkmRow_m8_r24 :=
    bh0_eq (tl2 bk_19)
/-- Kernel trajectory certificate `(m = 64, r = 16)`. -/
theorem rkmTraj_m64_r16 : rkmEvalT16Lo12 64 128 16 [1, 1, 1, 1, 1, 1] [46642985, 46601578, 3029804,
  3389167, 1545636, 2151937] [9, 9, 1, 1, 1, 1] rkmMasks_m64_r16 = rkmRow_m64_r16 :=
    bh0_eq (tl2 (tl2 bk_20))
/-- Kernel trajectory certificate `(m = 512, r = 20)`. -/
theorem rkmTraj_m512_r20 : rkmEvalT16Lo12 512 16 20 [1, 1, 1] [33393723, 1116356, 87749] [23, 2, 2]
  rkmMasks_m512_r20 = rkmRow_m512_r20 := bh0_eq (tl1 bk_2)
/-- Kernel trajectory certificate `(m = 128, r = 17)`. -/
theorem rkmTraj_m128_r17 : rkmEvalT16Lo12 128 64 17 [1, 1] [69381935, 1331272] [20, 2]
  rkmMasks_m128_r17 = rkmRow_m128_r17 := bh0_eq (tl2 bk_20)
/-- Kernel trajectory certificate `(m = 256, r = 19)`. -/
theorem rkmTraj_m256_r19 : rkmEvalT16Lo12 256 32 19 [1, 1] [48310423, 1005130] [23, 2]
  rkmMasks_m256_r19 = rkmRow_m256_r19 := bh0_eq (tl1 bk_1)
/-- Krotov trajectory `(m = 16, r = 96)`. -/
theorem rkmTrajPack_m16_r96 : rkmEvalT16Lo12 16 512 96 [1,2,3,6,10,10,10,10]
  [26046285,17334127,16898415,21062415,14709292,19162770,5440070,1538258] [6,7,10,21,21,27,8,3]
  rkmMasksPack_m16_r96 = rkmRowPack_m16_r96 :=
    bhW_eq bk_16 (wSkip (wSkip (wSkip (wCons (bSlideChk_sound bk_11) (wCons (bSlideChk_sound
      bk_12) (wCons (bSlideChk_sound bk_2) wNil))))))
/-- Krotov trajectory `(m = 16, r = 4)`. -/
theorem rkmTrajPack_m16_r4 : rkmEvalT16Lo12 16 512 4 [1,1,1,1,1]
  [108046819,51177636,12678224,14894374,5943115] [3,2,1,1,1] rkmMasksPack_m16_r4 = rkmRowPack_m16_r4
  := bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21))))))
/-- Krotov trajectory `(m = 64, r = 62)`. -/
theorem rkmTrajPack_m64_r62 : rkmEvalT16Lo12 64 128 62 [2,2,2,2,2,2,2,2]
  [21656117,15514113,15492665,11444016,6461875,3498117,4741889,2271741] [19,14,14,10,6,3,4,2]
  rkmMasksPack_m64_r62 = rkmRowPack_m64_r62 :=
    bhW_eq bk_4 (wCons (bSlideChk_sound (tl1 bk_13)) (wCons (bSlideChk_sound (tl1 bk_5)) wNil))
/-- Krotov trajectory `(m = 4, r = 44)`. -/
theorem rkmTrajPack_m4_r44 : rkmEvalT16Lo12 4 2048 44 [1,1,1,1,1,1,1,1]
  [14817684,26275815,18780874,9626964,16956087,8064996,11789,10382784] [1,2,1,1,1,1,1,1]
  rkmMasksPack_m4_r44 = rkmRowPack_m4_r44 := bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21))))))
/-- Krotov trajectory `(m = 32, r = 64)`. -/
theorem rkmTrajPack_m32_r64 : rkmEvalT16Lo12 32 256 64 [1,2,4,4,4,4,4,4]
  [40668184,32838153,17130215,16876030,5635382,1144241,1041403,863528] [13,18,15,15,5,1,1,1]
  rkmMasksPack_m32_r64 = rkmRowPack_m32_r64 :=
    bhW_eq bk_0 (wSkip (wCons (bSlideChk_sound (tl1 bk_11)) wNil))
/-- Krotov trajectory `(m = 4, r = 4)`. -/
theorem rkmTrajPack_m4_r4 : rkmEvalT16Lo12 4 2048 4 [1,1,2,2,2,2,2,2]
  [122806080,136487217,44082527,45128558,11429408,5467569,6827020,2950095] [2,2,1,1,1,1,1,1]
  rkmMasksPack_m4_r4 = rkmRowPack_m4_r4 := bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21)))))))
/-- Krotov trajectory `(m = 2, r = 64)`. -/
theorem rkmTrajPack_m2_r64 : rkmEvalT16Lo12 2 4096 64 [1,3,7,15,30,58,58,58]
  [17714062,22686081,23071912,24344206,27900460,15514387,17537091,6486197] [1,2,4,8,15,13,15,6]
  rkmMasksPack_m2_r64 = rkmRowPack_m2_r64 :=
    bhW_eq bk_3 (wSkip (wSkip (wSkip (wSkip (wSkip (wSkip (wCons (bSlideChk_sound (tl1 bk_7))
      wNil)))))))
/-- Krotov trajectory `(m = 32, r = 6)`. -/
theorem rkmTrajPack_m32_r6 : rkmEvalT16Lo12 32 256 6 [1,1,1,1,1,1,1,1]
  [27566359,29156120,15699371,33260528,15137778,6733037,7619625,3319621] [2,2,1,2,1,1,1,1]
  rkmMasksPack_m32_r6 = rkmRowPack_m32_r6 :=
    bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21)))))))
/-- Krotov trajectory `(m = 64, r = 40)`. -/
theorem rkmTrajPack_m64_r40 : rkmEvalT16Lo12 64 128 40 [1,1,1] [116833671,5562986,1280343] [44,3,1]
  rkmMasksPack_m64_r40 = rkmRowPack_m64_r40 := bh0_eq bk_14
/-- Krotov trajectory `(m = 8, r = 40)`. -/
theorem rkmTrajPack_m8_r40 : rkmEvalT16Lo12 8 1024 40 [1,1,1,1,1,1,1,1]
  [19458533,10935682,32705802,10098822,5923382,17372313,12304828,8370911] [2,1,3,1,1,2,1,1]
  rkmMasksPack_m8_r40 = rkmRowPack_m8_r40 :=
    bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21))))))))
/-- Krotov trajectory `(m = 64, r = 34)`. -/
theorem rkmTrajPack_m64_r34 : rkmEvalT16Lo12 64 128 34 [1,1,1] [98513554,13309357,5187973] [33,5,2]
  rkmMasksPack_m64_r34 = rkmRowPack_m64_r34 := bh0_eq (tl1 bk_17)
/-- Krotov trajectory `(m = 8, r = 8)`. -/
theorem rkmTrajPack_m8_r8 : rkmEvalT16Lo12 8 1024 8 [1,1,1,1,2,2,2,2]
  [51917897,21666629,53497923,44872377,30784751,35129397,27441406,13331545] [2,1,2,2,2,2,2,1]
  rkmMasksPack_m8_r8 = rkmRowPack_m8_r8 :=
    bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21))))))))
/-- Krotov trajectory `(m = 16, r = 34)`. -/
theorem rkmTrajPack_m16_r34 : rkmEvalT16Lo12 16 512 34 [1,3,3,3]
  [66292799,88522892,19217130,6099785] [8,24,6,2] rkmMasksPack_m16_r34 = rkmRowPack_m16_r34 :=
    bh0_eq (tl1 bk_15)
/-- Krotov trajectory `(m = 32, r = 10)`. -/
theorem rkmTrajPack_m32_r10 : rkmEvalT16Lo12 32 256 10 [1,1,1,1,1,1,1,1]
  [34593923,30105611,38926467,11029738,10488084,7478425,8868250,5498883] [3,3,4,1,1,1,1,1]
  rkmMasksPack_m32_r10 = rkmRowPack_m32_r10 := bh0_eq (tl2 (tl2 bk_21))
/-- Krotov trajectory `(m = 4, r = 80)`. -/
theorem rkmTrajPack_m4_r80 : rkmEvalT16Lo12 4 2048 80 [1,1,10,20,20,20,20,20]
  [26438868,24834419,9490642,1067257,1456990,1009681,5321915,2149456] [2,2,5,1,2,1,4,2]
  rkmMasksPack_m4_r80 = rkmRowPack_m4_r80 := bh0_eq (tl1 bk_19)
/-- Krotov trajectory `(m = 4, r = 22)`. -/
theorem rkmTrajPack_m4_r22 : rkmEvalT16Lo12 4 2048 22 [1,1,3,6,6,6,6,6]
  [51841578,31700079,64191124,100748,1159203,1848828,1289415,697232] [2,1,5,1,1,1,1,1]
  rkmMasksPack_m4_r22 = rkmRowPack_m4_r22 := bh0_eq (tl2 bk_9)
/-- Krotov trajectory `(m = 64, r = 25)`. -/
theorem rkmTrajPack_m64_r25 : rkmEvalT16Lo12 64 128 25 [1,1,1,1,1,1,1,1]
  [29408500,14315537,28551416,12117796,8981266,7142578,5337284,3622535] [8,4,8,4,3,2,2,1]
  rkmMasksPack_m64_r25 = rkmRowPack_m64_r25 := bh0_eq (tl1 bk_9)
/-- Krotov trajectory `(m = 8, r = 23)`. -/
theorem rkmTrajPack_m8_r23 : rkmEvalT16Lo12 8 1024 23 [1,1,2,3,3,3,3,3]
  [16504451,76610684,39120830,38193,271058,1967444,5411484,617008] [1,5,4,1,1,1,1,1]
  rkmMasksPack_m8_r23 = rkmRowPack_m8_r23 := bh0_eq (tl2 bk_10)
/-- Krotov trajectory `(m = 32, r = 112)`. -/
theorem rkmTrajPack_m32_r112 : rkmEvalT16Lo12 32 256 112 [1,1,1,1,1,1,1,1]
  [6211408,7329214,8379450,3331055,488897,4143660,4580583,5224108] [3,4,4,2,1,2,2,3]
  rkmMasksPack_m32_r112 = rkmRowPack_m32_r112 := bh0_eq (tl1 bk_4)
/-- Krotov trajectory `(m = 8, r = 26)`. -/
theorem rkmTrajPack_m8_r26 : rkmEvalT16Lo12 8 1024 26 [1,1,2,4,4,4,4,4]
  [41237546,41842717,48025010,3299526,1162021,2183375,3277479,848013] [3,3,5,1,1,1,1,1]
  rkmMasksPack_m8_r26 = rkmRowPack_m8_r26 := bh0_eq bk_21
/-- Krotov trajectory `(m = 8, r = 24)`. -/
theorem rkmTrajPack_m8_r24 : rkmEvalT16Lo12 8 1024 24 [1,2,4,6,6,6]
  [52249978,37863176,41846521,52723056,5705455,863417] [3,4,7,11,2,1] rkmMasksPack_m8_r24 =
  rkmRowPack_m8_r24 := bh0_eq bk_20
/-- Krotov trajectory `(m = 4, r = 27)`. -/
theorem rkmTrajPack_m4_r27 : rkmEvalT16Lo12 4 2048 27 [1,1,4,7,7,7,7,7]
  [50163741,23969036,51251155,121692,8421970,8276174,4837051,5360458] [2,1,6,1,2,2,1,1]
  rkmMasksPack_m4_r27 = rkmRowPack_m4_r27 := bh0_eq (tl1 bk_0)
/-- Krotov trajectory `(m = 16, r = 20)`. -/
theorem rkmTrajPack_m16_r20 : rkmEvalT16Lo12 16 512 20 [1,2,2,2]
  [94129778,75074434,24767509,9490443] [8,11,4,2] rkmMasksPack_m16_r20 = rkmRowPack_m16_r20 :=
    bh0_eq (tl1 bk_20)
/-- Krotov trajectory `(m = 32, r = 16)`. -/
theorem rkmTrajPack_m32_r16 : rkmEvalT16Lo12 32 256 16 [1,1,1,1,1,1,1,1]
  [37649988,44428369,30835885,13781698,14613796,10214694,4632432,4221734] [5,6,4,2,2,2,1,1]
  rkmMasksPack_m32_r16 = rkmRowPack_m32_r16 := bh0_eq (tl1 (tl2 bk_20))
end
end QuantumComputation.Specs.DickeSol
