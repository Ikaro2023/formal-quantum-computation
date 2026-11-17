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
/-
# Multi-Segment `T_16` Trajectory Part `01` (`FindAllJohnsonRampKickMuxTraj01`)

Certified kernel trajectory evaluations (`30` rows, `37994` substep-coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Prefix-kick masks for `(m = 2, r = 19)`. -/
def rkmMasks_m2_r19 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 19)`. -/
def rkmRow_m2_r19 : List ℕ := [333836326141, 632772615263]
/-- Mask chunk for `(m = 2, r = 64)`. -/
def rkmMkP_m2_r64_s3_p0 : List Bool := [
  false, true, true, true, true, false, false, false, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true]
/-- Mask chunk for `(m = 2, r = 64)`. -/
def rkmMkP_m2_r64_s4_p0 : List Bool := [
  false, true, false, true, true, false, false, false, false, true, false, false, true, false,
  false, false, true, true, false, true, true, true, true, false, false, false, false, true, true,
  true, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, true, true, false, false, true,
  false, true]
/-- Mask chunk for `(m = 2, r = 64)`. -/
def rkmMkP_m2_r64_s5_p0 : List Bool := [
  false, true, false, false, false, false, false, true, false, true, false, true, false, true,
  false, true, false, true, false, false, true, false, false, true, false, false, true, true,
  false, false, true, true, false, false, true, true, false, false, false, true, true, false,
  false, false, true, true, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false]
/-- Mask chunk for `(m = 2, r = 64)`. -/
def rkmMkP_m2_r64_s5_p1 : List Bool := [true]
/-- Mask chunk for `(m = 2, r = 64)`. -/
def rkmMkP_m2_r64_s6_p0 : List Bool := [
  false, false, true, true, false, true, false, true, false, false, false, false, false, true,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, false, true, true, false, false, true, false, false, true, true,
  false, false, false, true, true]
/-- Prefix-kick masks for `(m = 2, r = 64)`. -/
def rkmMasks_m2_r64 : List (List Bool) := [
  [], [], [], rkmMkP_m2_r64_s3_p0, rkmMkP_m2_r64_s4_p0,
  rkmMkP_m2_r64_s5_p0 ++ rkmMkP_m2_r64_s5_p1, rkmMkP_m2_r64_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 64)`. -/
def rkmRow_m2_r64 : List ℕ := [
  249341, 206463, 127641, 3491436, 6458644, 18607234, 10811155, 3983968, 29743199, 152149000,
  33007178, 172241417, 34019626, 18943476, 12850729, 50604484, 38218500, 61819, 53425401,
  247340368, 280336155, 115172006, 16504884, 252620180, 460709955, 231465088, 509036, 247625223,
  371865720, 122519125, 8979508, 354407841, 249486670, 22118790, 33564232, 62401363, 358195,
  441627389, 202111003, 23339399, 437865454, 321548282, 106463027, 48026661, 31087031, 6147585,
  1481058915, 675088915, 650614558, 45356, 885794816, 1153901203, 3429738670, 1350572825, 9046949,
  2276706311, 314977019, 18252349843, 12406110112, 1348827600, 14843157075, 281310172409,
  474026912471, 180249274781]
/-- Prefix-kick masks for `(m = 4, r = 18)`. -/
def rkmMasks_m4_r18 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 18)`. -/
def rkmRow_m4_r18 : List ℕ := [
  288265407, 7823373, 238437653, 75576427, 477884819, 1380877913, 7955365075, 1003351379,
  106366450818, 329483881703, 345144283428, 164491176467, 38373665831, 4291971494, 205413576,
  3050394]
/-- Mask chunk for `(m = 8, r = 18)`. -/
def rkmMkP_m8_r18_s1_p0 : List Bool := [
  false, true, true, true, false, false, false, true, false, false, true, true, false, false,
  true, true]
/-- Mask chunk for `(m = 8, r = 18)`. -/
def rkmMkP_m8_r18_s2_p0 : List Bool := [
  true, false, true, false, true, false, true, false, true, false, true, false, true, false,
  false, false, true]
/-- Prefix-kick masks for `(m = 8, r = 18)`. -/
def rkmMasks_m8_r18 : List (List Bool) := [[], rkmMkP_m8_r18_s1_p0, rkmMkP_m8_r18_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 18)`. -/
def rkmRow_m8_r18 : List ℕ := [
  3982, 40313, 1272339, 7320656, 7314921, 9612832, 1638159, 9563654, 77285244, 506247652,
  545852617, 2860241289, 522584448, 1541022718, 24999855332, 63306190, 99782519624, 869064313632]
/-- Mask chunk for `(m = 8, r = 22)`. -/
def rkmMkP_m8_r22_s1_p0 : List Bool := [
  false, false, false, false, false, false, true, false, true, false, false, true, false, true,
  true, false, false, true, true]
/-- Mask chunk for `(m = 8, r = 22)`. -/
def rkmMkP_m8_r22_s2_p0 : List Bool := [
  false, true, false, false, true, false, true, false, true, false, true, false, true, false,
  true, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 8, r = 22)`. -/
def rkmMasks_m8_r22 : List (List Bool) := [[], rkmMkP_m8_r22_s1_p0, rkmMkP_m8_r22_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 22)`. -/
def rkmRow_m8_r22 : List ℕ := [
  394, 1729, 8193, 2899, 1174790, 3589585, 69337, 13771, 70146431, 363794610, 954332718,
  996802140, 1288963987, 969768460, 201209125, 819020645, 3329407571, 11148809831, 9033176382,
  725849635, 90206303292, 879887554161]
/-- Prefix-kick masks for `(m = 16, r = 5)`. -/
def rkmMasks_m16_r5 : List (List Bool) := [[true, true, true], [true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 5)`. -/
def rkmRow_m16_r5 : List ℕ := [64949256, 16716457, 126994192, 41468594813, 958321166476]
/-- Prefix-kick masks for `(m = 16, r = 13)`. -/
def rkmMasks_m16_r13 : List (List Bool) := [
  [true, false, false, false, true, true, false, false, true, true],
  [false, true, false, true, false, true, false, true, false, false, true],
  [true, false, false, true, false, false, true, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 13)`. -/
def rkmRow_m16_r13 : List ℕ := [
  6463, 149511, 1190769, 5856239, 47946603, 171365324, 230747107, 44214644, 33726686, 1843273550,
  1025821329, 49903849365, 946691852278]
/-- Mask chunk for `(m = 16, r = 20)`. -/
def rkmMkP_m16_r20_s1_p0 : List Bool := [
  true, true, false, true, true, false, false, true, true, false, true, true, true, true, false,
  true, true]
/-- Mask chunk for `(m = 16, r = 20)`. -/
def rkmMkP_m16_r20_s2_p0 : List Bool := [
  true, false, true, false, true, false, true, false, false, true, false, false, true, false,
  false, true, false, true, true]
/-- Prefix-kick masks for `(m = 16, r = 20)`. -/
def rkmMasks_m16_r20 : List (List Bool) := [[], rkmMkP_m16_r20_s1_p0, rkmMkP_m16_r20_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 20)`. -/
def rkmRow_m16_r20 : List ℕ := [
  20, 609, 4752, 75655, 148331, 1781670, 7014520, 744166, 6772011, 40038765, 42270714, 106025859,
  1371518859, 106795128, 2615490237, 9516043908, 2941243529, 1085861358, 40312838583,
  941845331094]
/-- Mask chunk for `(m = 16, r = 22)`. -/
def rkmMkP_m16_r22_s1_p0 : List Bool := [
  true, false, false, true, false, true, false, false, true, true, false, false, true, true, true,
  true, true]
/-- Mask chunk for `(m = 16, r = 22)`. -/
def rkmMkP_m16_r22_s2_p0 : List Bool := [
  false, true, false, false, true, false, true, false, true, true, true, false, true, true, false,
  true, true, false, true, true]
/-- Mask chunk for `(m = 16, r = 22)`. -/
def rkmMkP_m16_r22_s3_p0 : List Bool := [
  false, true, false, true, false, true, false, true, true, false, true, true, false, false, true,
  false, false, false, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 22)`. -/
def rkmMasks_m16_r22 : List (List Bool) := [
  [], rkmMkP_m16_r22_s1_p0, rkmMkP_m16_r22_s2_p0, rkmMkP_m16_r22_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 22)`. -/
def rkmRow_m16_r22 : List ℕ := [
  165, 2505, 622, 217, 341, 87243, 338089, 136808, 1626551, 278352, 174178, 75139581, 106652157,
  908730, 162656908, 1152814880, 216794029, 1787782241, 6771731144, 204660044, 44028203925,
  945490011021]
/-- Mask chunk for `(m = 16, r = 23)`. -/
def rkmMkP_m16_r23_s1_p0 : List Bool := [
  true, false, true, true, false, true, true, false, false, true, true, false, false, true, true,
  true, true, true]
/-- Mask chunk for `(m = 16, r = 23)`. -/
def rkmMkP_m16_r23_s2_p0 : List Bool := [
  true, false, true, false, true, false, true, false, true, false, false, true, false, true, true,
  false, true, true, false, true, true]
/-- Mask chunk for `(m = 16, r = 23)`. -/
def rkmMkP_m16_r23_s3_p0 : List Bool := [
  false, false, false, true, false, true, false, true, true, false, true, false, false, true,
  true, true, false, false, false, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 23)`. -/
def rkmMasks_m16_r23 : List (List Bool) := [
  [], rkmMkP_m16_r23_s1_p0, rkmMkP_m16_r23_s2_p0, rkmMkP_m16_r23_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 23)`. -/
def rkmRow_m16_r23 : List ℕ := [
  12, 71, 285, 902, 53, 17584, 1124563, 3580985, 12615123, 3247323, 24305267, 10749110, 38783335,
  186240892, 323475191, 116715, 1051292622, 231490822, 1992441557, 7983838501, 189471416,
  45020955488, 942926251881]
/-- Mask chunk for `(m = 16, r = 40)`. -/
def rkmMkP_m16_r40_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, true, true, true, false,
  false, false, true, false, false, true, true, false, false, true, true, false, false, true,
  true, false, false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 16, r = 40)`. -/
def rkmMkP_m16_r40_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, false, true, false, true,
  false, false, false, true, false, true, false, true, true, false, false, true, false, true,
  false, true, false, true, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 40)`. -/
def rkmMasks_m16_r40 : List (List Bool) := [
  [], [], [], rkmMkP_m16_r40_s3_p0, rkmMkP_m16_r40_s4_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 40)`. -/
def rkmRow_m16_r40 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1, 296, 149, 0, 290, 982, 4562, 380, 90657, 45035, 578769,
  859, 314434, 2160613, 3754093, 20594274, 33222152, 195476663, 286364958, 1587012732, 1624379151,
  6720072036, 1537877197, 136951265, 15648108003, 331865999, 43283269895, 928587853607]
/-- Mask chunk for `(m = 32, r = 24)`. -/
def rkmMkP_m32_r24_s0_p0 : List Bool := [
  true, false, false, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, true]
/-- Mask chunk for `(m = 32, r = 24)`. -/
def rkmMkP_m32_r24_s1_p0 : List Bool := [
  false, true, false, true, true, false, true, false, false, false, true, false, false, false,
  false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 32, r = 24)`. -/
def rkmMkP_m32_r24_s2_p0 : List Bool := [
  false, false, true, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 32, r = 24)`. -/
def rkmMasks_m32_r24 : List (List Bool) := [
  rkmMkP_m32_r24_s0_p0, rkmMkP_m32_r24_s1_p0, rkmMkP_m32_r24_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 24)`. -/
def rkmRow_m32_r24 : List ℕ := [
  0, 0, 0, 4, 83, 722, 5137, 26107, 71858, 192336, 839132, 2384823, 17577795, 57876450, 121291411,
  448107062, 54240544, 47220599, 17769163, 9947764784, 4212414652, 224708893, 23321598612,
  961525909500]
/-- Mask chunk for `(m = 32, r = 27)`. -/
def rkmMkP_m32_r27_s0_p0 : List Bool := [
  false, true, true, true, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, true]
/-- Mask chunk for `(m = 32, r = 27)`. -/
def rkmMkP_m32_r27_s1_p0 : List Bool := [
  false, false, false, true, true, false, false, true, true, true, false, true, true, false, true,
  false, false, true, true, false, false, false, true, true]
/-- Prefix-kick masks for `(m = 32, r = 27)`. -/
def rkmMasks_m32_r27 : List (List Bool) := [rkmMkP_m32_r27_s0_p0, rkmMkP_m32_r27_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 27)`. -/
def rkmRow_m32_r27 : List ℕ := [
  0, 0, 2, 0, 0, 13, 308, 4144, 31021, 150984, 593146, 2072116, 6798714, 19772740, 45793266,
  76228881, 82563093, 25000088, 50659513, 836817745, 3384896448, 4793617817, 1355291610,
  6938194230, 21129875254, 34949555441, 926302082942]
/-- Mask chunk for `(m = 32, r = 32)`. -/
def rkmMkP_m32_r32_s0_p0 : List Bool := [
  false, false, false, false, false, true, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, true]
/-- Mask chunk for `(m = 32, r = 32)`. -/
def rkmMkP_m32_r32_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, true, false, true, false, true, false, true,
  false, true, false, false, false, true, true, false, false, true, true, true, true, true]
/-- Mask chunk for `(m = 32, r = 32)`. -/
def rkmMkP_m32_r32_s2_p0 : List Bool := [
  true, false, false, true, false, false, false, false, false, true, true, false, true, false,
  true, false, false, true, false, false, false, true, false, true, true, false, true, true,
  false, true, true]
/-- Prefix-kick masks for `(m = 32, r = 32)`. -/
def rkmMasks_m32_r32 : List (List Bool) := [
  rkmMkP_m32_r32_s0_p0, rkmMkP_m32_r32_s1_p0, rkmMkP_m32_r32_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 32)`. -/
def rkmRow_m32_r32 : List ℕ := [
  20, 34, 3, 32, 1774, 105, 0, 2843, 3047, 4044, 137, 4704, 2377, 753, 283172, 202748, 473472,
  1128611, 2287398, 43458, 27841056, 70034983, 377756000, 24861501, 526743216, 2495535461,
  1103389402, 3534553018, 6812161616, 10301580, 18806363649, 966206019192]
/-- Prefix-kick masks for `(m = 32, r = 34)`. -/
def rkmMasks_m32_r34 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 34)`. -/
def rkmRow_m32_r34 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 22, 84, 1102, 0, 17758, 21741, 108137, 723631, 70448,
  8952728, 3454847, 55260053, 130172422, 159081577, 1640841096, 79991328, 13008432775, 883331189,
  87895888006, 22109730919, 874023919437]
/-- Prefix-kick masks for `(m = 64, r = 5)`. -/
def rkmMasks_m64_r5 : List (List Bool) := [[], [true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 5)`. -/
def rkmRow_m64_r5 : List ℕ := [250329, 210, 10797372, 33421056012, 966567893099]
/-- Prefix-kick masks for `(m = 64, r = 7)`. -/
def rkmMasks_m64_r7 : List (List Bool) := [
  [false, false, false, true, true], [false, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 7)`. -/
def rkmRow_m64_r7 : List ℕ := [300, 886, 1250, 26035844, 12702481, 24470943481, 975490315686]
/-- Prefix-kick masks for `(m = 64, r = 8)`. -/
def rkmMasks_m64_r8 : List (List Bool) := [
  [], [true, false, false, true, true, true], [false, true, false, true, false, true],
  [true, false, true, true, false, false, true], [true, true, true, false, false, true],
  [false, true, false, false, false, true, true], [false, false, true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 8)`. -/
def rkmRow_m64_r8 : List ℕ := [0, 2161, 5736, 4314522, 227559, 939889, 21724462305, 978270047746]
/-- Prefix-kick masks for `(m = 64, r = 10)`. -/
def rkmMasks_m64_r10 : List (List Bool) := [
  [false, false, true, false, false, false, true, true],
  [false, true, false, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 10)`. -/
def rkmRow_m64_r10 : List ℕ := [
  0, 10, 229, 24433, 306263, 2427299, 17008222, 47684982, 17958166600, 981974381864]
/-- Mask chunk for `(m = 128, r = 16)`. -/
def rkmMkP_m128_r16_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 128, r = 16)`. -/
def rkmMkP_m128_r16_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, true, false, true, false, true, false, true,
  true]
/-- Prefix-kick masks for `(m = 128, r = 16)`. -/
def rkmMasks_m128_r16 : List (List Bool) := [rkmMkP_m128_r16_s0_p0, rkmMkP_m128_r16_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 16)`. -/
def rkmRow_m128_r16 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 1, 14, 13235, 73586, 8850615, 112047, 64093797, 10940139449, 988986717026]
/-- Mask chunk for `(m = 128, r = 128)`. -/
def rkmMkP_m128_r128_s1_p0 : List Bool := [
  true, false, false, true, false, false, false, true, true, false, false, true, false, false,
  true, false, true, false, false, true, false, false, false, false, false, true, true, true,
  true, false, false, true, true, true, true, false, false, false, true, true, false, false, true,
  false, false, true, true, true, true, true, true, true, true, true]
/-- Mask chunk for `(m = 128, r = 128)`. -/
def rkmMkP_m128_r128_s2_p0 : List Bool := [
  false, false, false, false, false, true, true, true, true, false, false, false, false, false,
  false, false, false, false, true, false, false, false, true, false, false, true, false, false,
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true, false,
  true, true, false, false, true, true, false, true]
/-- Mask chunk for `(m = 128, r = 128)`. -/
def rkmMkP_m128_r128_s2_p1 : List Bool := [
  true, true, false, false, false, true, false, false, false, false, true, true, true, false,
  false, true, true, false, true, false, false, true, true, true, true, false, false, false,
  false, false, false, false, true, true, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, true, true, true]
/-- Mask chunk for `(m = 128, r = 128)`. -/
def rkmMkP_m128_r128_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, true,
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  false, true, false, true, false, false, false, false, false, false, false, true, false, false,
  false, false, false, false, false, false, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 128, r = 128)`. -/
def rkmMkP_m128_r128_s3_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, false, false, true, false, false,
  true, true, false, false, true, true, false, false, false, true, true, false, false, true,
  false, false, true, true, true]
/-- Mask chunk for `(m = 128, r = 128)`. -/
def rkmMkP_m128_r128_s4_p0 : List Bool := [
  false, false, false, false, false, true, false, false, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, false, false, false, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 128, r = 128)`. -/
def rkmMkP_m128_r128_s4_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, false, false, false, false, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, true, false, false, true, false, false, true, false, true, false, true, false, false,
  false, true]
/-- Mask chunk for `(m = 128, r = 128)`. -/
def rkmMkP_m128_r128_s5_p0 : List Bool := [
  false, true, true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, false, false, false,
  false, false, false, false, false, false, false, true, false, false, true, false, false, false,
  false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 128, r = 128)`. -/
def rkmMkP_m128_r128_s5_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, false, false, true, false,
  false, true, false, true, false, true, false, true, true, true]
/-- Mask chunk for `(m = 128, r = 128)`. -/
def rkmMkP_m128_r128_s6_p0 : List Bool := [
  false, false, false, false, true, false, true, false, true, true, true, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 128, r = 128)`. -/
def rkmMkP_m128_r128_s6_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, false, false, false, false, false, false, true, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, true,
  false, false, true, true, true, true, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 128)`. -/
def rkmMasks_m128_r128 : List (List Bool) := [
  [true, true], rkmMkP_m128_r128_s1_p0, rkmMkP_m128_r128_s2_p0 ++ rkmMkP_m128_r128_s2_p1,
  rkmMkP_m128_r128_s3_p0 ++ rkmMkP_m128_r128_s3_p1,
  rkmMkP_m128_r128_s4_p0 ++ rkmMkP_m128_r128_s4_p1,
  rkmMkP_m128_r128_s5_p0 ++ rkmMkP_m128_r128_s5_p1,
  rkmMkP_m128_r128_s6_p0 ++ rkmMkP_m128_r128_s6_p1, []]
/-- Row chunk `0` `(m = 128, r = 128)`. -/
def rkmRowP_m128_r128_p0 : List ℕ := [
  730, 3611, 4791, 18703, 114937, 17507, 213511, 179282, 33915, 574, 104, 86, 33174, 970, 2889,
  41110, 60232, 1172, 56132, 1218, 7208, 90834, 436, 59241, 3592, 914, 74999, 59504, 142770, 9206,
  81536, 8586, 12189, 287, 38691, 150617, 69462, 62976, 32251, 63892, 1517, 507, 1567, 5046,
  84582, 74426, 27525, 295153, 57748, 1193, 6, 74001, 195506, 32110, 29082, 9219, 27525, 111363,
  20159, 4879, 168743, 75509, 35847, 9184]
/-- Row chunk `1` `(m = 128, r = 128)`. -/
def rkmRowP_m128_r128_p1 : List ℕ := [
  57861, 224135, 32157, 113107, 523350, 482639, 16309, 210770, 179636, 87308, 1223187, 1175697,
  352246, 905, 35009, 42460, 701057, 1339246, 531408, 485, 220061, 56348, 452582, 1166164, 303837,
  1247, 59281, 1759, 243254, 43283, 324285, 525671, 187062, 374245, 525296, 20323, 1233516,
  608320, 292243, 1329716, 3611047, 4934111, 25297, 2216709, 1261, 112137, 277262, 11982020,
  6898103, 14301779, 32452697, 249092260, 1463580, 209971119, 213392778, 1669729530, 226708500,
  1409418729, 1843677758, 14349983195, 344370597, 160211078, 7298680197, 971928080666]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 128)`. -/
def rkmRow_m128_r128 : List ℕ := rkmRowP_m128_r128_p0 ++ rkmRowP_m128_r128_p1
/-- Prefix-kick masks for `(m = 256, r = 13)`. -/
def rkmMasks_m256_r13 : List (List Bool) := [
  [false, false, false, false, false, false, true, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 13)`. -/
def rkmRow_m256_r13 : List ℕ := [
  0, 0, 0, 0, 0, 3, 181, 3570, 25981, 2404999, 71202321, 12382177332, 987544185398]
/-- Mask chunk for `(m = 256, r = 18)`. -/
def rkmMkP_m256_r18_s0_p0 : List Bool := [
  false, false, false, true, true, false, false, true, true, false, false, true, false, false,
  true, true]
/-- Prefix-kick masks for `(m = 256, r = 18)`. -/
def rkmMasks_m256_r18 : List (List Bool) := [rkmMkP_m256_r18_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 18)`. -/
def rkmRow_m256_r18 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16, 190, 367, 151414, 29420330, 281402476, 9120647748,
  990568377093]
/-- Prefix-kick masks for `(m = 256, r = 28)`. -/
def rkmMasks_m256_r28 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 28)`. -/
def rkmRow_m256_r28 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 58, 4550, 38235, 2381328, 18313080,
  1281250508, 6093139558, 992604871887]
/-- Prefix-kick masks for `(m = 256, r = 31)`. -/
def rkmMasks_m256_r31 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 31)`. -/
def rkmRow_m256_r31 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 97, 10039, 53059, 4015284,
  20837686, 1659339610, 5664731012, 992651012287]
/-- Prefix-kick masks for `(m = 512, r = 3)`. -/
def rkmMasks_m512_r3 : List (List Bool) := [[], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 3)`. -/
def rkmRow_m512_r3 : List ℕ := [897326550, 53288301486, 945809931644]
/-- Prefix-kick masks for `(m = 512, r = 8)`. -/
def rkmMasks_m512_r8 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 8)`. -/
def rkmRow_m512_r8 : List ℕ := [0, 0, 0, 1751, 23471, 61809301, 19506981268, 980431184081]
/-- Mask chunk for `(m = 512, r = 19)`. -/
def rkmMkP_m512_r19_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, false, true,
  true]
/-- Mask chunk for `(m = 512, r = 19)`. -/
def rkmMkP_m512_r19_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, true, true]
/-- Prefix-kick masks for `(m = 512, r = 19)`. -/
def rkmMasks_m512_r19 : List (List Bool) := [rkmMkP_m512_r19_s0_p0, rkmMkP_m512_r19_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 19)`. -/
def rkmRow_m512_r19 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 1109, 16912, 0, 2623209, 7355614, 8366557809, 991623444747]
/-- Prefix-kick masks for `(m = 1024, r = 12)`. -/
def rkmMasks_m1024_r12 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 12)`. -/
def rkmRow_m1024_r12 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 712, 31425, 23222310, 12895838659, 987080906561]
/-- Prefix-kick masks for `(m = 1024, r = 14)`. -/
def rkmMasks_m1024_r14 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 14)`. -/
def rkmRow_m1024_r14 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 825, 122248, 8451611, 11055036363, 988936388528]
/-- Unpacks `j` LSB-first bits of `< 2 ^ 50` word `w` (`FindAllJohnsonRampKickMuxTraj01`). -/
def rkmWbTraj01 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWbTraj01 j (Nat.div w 2)
/-- Concatenates `50`-bit `< 2 ^ 50` chunks (final length `rem`) into a `List Bool` mask. -/
def rkmMaskWordsTraj01 : ℕ → List ℕ → List Bool
  | _, [] => []
  | rem, [w] => rkmWbTraj01 rem w
  | rem, w :: v :: ws => rkmWbTraj01 50 w ++ rkmMaskWordsTraj01 rem (v :: ws)
/-- Krotov masks `(m = 32, r = 128)`. -/
def rkmMasksPack_m32_r128 : List (List Bool) := [rkmWbTraj01 30 1073741823,
  rkmMaskWordsTraj01 5 [16192,30],rkmMaskWordsTraj01 14 [343870508769327,70368781668267,8960],
  rkmMaskWordsTraj01 28 [955848546014833,626256911057429,234881507],
  rkmMaskWordsTraj01 25 [5780154962132,375441698592888,26843947],
  rkmMaskWordsTraj01 19 [296043662082097,280246702342,483604],
  rkmMaskWordsTraj01 27 [75131867234401,74788606591056,76234756],[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 128)`. -/
def rkmRowPack_m32_r128 : List ℕ := [389,108,3545,5680,17954,21273,9839,2035,40122,19308,195543,0,
  56111,112556,97138,122662,24673,7782,10080,23139,22228,4104,169682,31040,567745,294894,206240,
  56056,607022,861025,1699836,1047319,40767,16187,185048,8007,66225,53458,25125,197270,56220,
  67966,483467,43992,191249,135877,1858997,41162,3136,86725,114149,609,30520,5631,4067,77864,
  353289,190624,93102,2,228173,150732,73961,443410,58519,441371,1653251,315453,81468,99772,339852,
  1563805,1300,144977,50432,5409225,380989,279490,4695,32343281,10201687,3278064,801875,20397,
  4383790,419165,811583,6488,2202388,9469848,1164864,62426995,17793266,35750198,1461765,34586170,
  108763486,231354798,2321293,845472387,139619575,4516015,464180916,840138823,564404,82995691,
  365028030,200817203,586697403,166360732,616236856,921549424,375310019,1179643489,2870759701,
  136100414,4292812,3232471676,4349866104,316577883,785613749,5751471170,156464903,6647280128,
  20684867898,279496358,19912079972,927501459738]
/-- Krotov masks `(m = 64, r = 3)`. -/
def rkmMasksPack_m64_r3 : List (List Bool) := [[],[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 3)`. -/
def rkmRowPack_m64_r3 : List ℕ := [358695305,54875822904,944765248965]
/-- Krotov masks `(m = 64, r = 56)`. -/
def rkmMasksPack_m64_r56 : List (List Bool) := [rkmWbTraj01 31 1073741824,
  rkmMaskWordsTraj01 6 [1125899890458623,63],rkmWbTraj01 37 124118401794,
  rkmWbTraj01 45 32086985127592,rkmMaskWordsTraj01 1 [992675907435562,1],
  rkmMaskWordsTraj01 4 [692678019050862,13],rkmWbTraj01 48 229755139042320,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 56)`. -/
def rkmRowPack_m64_r56 : List ℕ := [0,0,0,0,0,0,0,3,10,31,121,457,1464,2103,431,60,199,4430,2857,
  2245,713,72,1459,11673,135,9258,19395,28,551831,2630564,5045425,3834819,13339653,71303279,
  101661949,1354,21710964,52883891,164233937,108085071,363083097,19538363,102505049,21591735,
  104116974,84587515,1624700556,768898621,793897,754606818,3600275686,92732711,21604988258,
  12364307113,10775121164,947172810254]
/-- Krotov masks `(m = 64, r = 6)`. -/
def rkmMasksPack_m64_r6 : List (List Bool) := [[],rkmWbTraj01 4 14,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 6)`. -/
def rkmRowPack_m64_r6 : List ℕ := [25956,597842,574725,134975917,28223162433,971640662656]
/-- Krotov masks `(m = 16, r = 48)`. -/
def rkmMasksPack_m16_r48 : List (List Bool) := [[],[],rkmWbTraj01 29 469762062,
  rkmWbTraj01 46 44049187176191,rkmWbTraj01 36 61049377429,rkmWbTraj01 46 56241969999354,
  rkmWbTraj01 47 70369583033241,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 48)`. -/
def rkmRowPack_m16_r48 : List ℕ := [12521,4626,240446,118592,101077,14296,47954,30271,37680,88492,
  116619,1294050,264040,291445,25093,11169578,2541872,15666386,20084641,144361,27617916,3636328,
  45934225,10050768,115650062,5289753,292558341,570832101,277095030,147194502,837252581,40789577,
  870753486,79399748,652169725,577362279,85862294,1540328385,138509011,2945579469,777238,
  3634240275,1183950506,1168719032,31759221327,76252597,41075624839,911785052515]
/-- Krotov masks `(m = 8, r = 52)`. -/
def rkmMasksPack_m8_r52 : List (List Bool) := [rkmWbTraj01 8 255,rkmWbTraj01 7 64,[],
  rkmWbTraj01 6 32,rkmWbTraj01 7 127,rkmWbTraj01 8 128,rkmWbTraj01 8 255,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 52)`. -/
def rkmRowPack_m8_r52 : List ℕ := [5893013684,50825566569,40984559937,868944964173,46829705,
  1236695993,25285250006,6369039649]
/-- Krotov masks `(m = 64, r = 112)`. -/
def rkmMasksPack_m64_r112 : List (List Bool) := [rkmMaskWordsTraj01 14 [1925624,16368],
  rkmMaskWordsTraj01 14 [1125899687116416,16383],rkmMaskWordsTraj01 14 [1125899346659328,16383],
  rkmMaskWordsTraj01 14 [1125884075249664,16383],rkmMaskWordsTraj01 14 [1125886262206464,16383],
  rkmMaskWordsTraj01 14 [1125890626715648,16383],rkmMaskWordsTraj01 14 [4288348160,16382],[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 112)`. -/
def rkmRowPack_m64_r112 : List ℕ := [11926057,168306009,309879329,14866767508,6115016456,
  2267766526,3207037594,5530600936,297507035,2224595109,9021406800,18782156276,22925484104,
  947504967,556471356625,347882089136,1886838305,4823634951,984697560,85394447,6598472,82820,
  76619,110826,32798,8,4832,3061,492,10,3,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0]
/-- Krotov masks `(m = 8, r = 112)`. -/
def rkmMasksPack_m8_r112 : List (List Bool) := [[],[],[],[],rkmWbTraj01 8 255,rkmWbTraj01 7 68,
  rkmWbTraj01 8 187,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 112)`. -/
def rkmRowPack_m8_r112 : List ℕ := [64,163905,2651986,15905233,155014545,4117992379,156583791580,
  839124479958]
/-- Krotov masks `(m = 16, r = 36)`. -/
def rkmMasksPack_m16_r36 : List (List Bool) := [[],rkmWbTraj01 25 33554426,
  rkmWbTraj01 35 27486169286,rkmWbTraj01 33 5715430496,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 36)`. -/
def rkmRowPack_m16_r36 : List ℕ := [7828,57799,568,207562,9241,74,162,1234,105363,37338,11828,
  2825,152790,2192,33410,364,112719,12762,576682,1685881,3412276,8794581,2172974,1450814,14610956,
  1389155,302061527,4269401,2369124151,34933285,11265816700,15902877,29114446373,13520143865,
  38228293674,905109944202]
/-- Krotov masks `(m = 16, r = 9)`. -/
def rkmMasksPack_m16_r9 : List (List Bool) := [[],[],rkmWbTraj01 3 7,rkmWbTraj01 6 50,
  rkmWbTraj01 7 75,rkmWbTraj01 8 130,rkmWbTraj01 8 128,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 9)`. -/
def rkmRowPack_m16_r9 : List ℕ := [176,7372843,1156185,1242812,57823799,96154400,156249793,
  35026002804,964653985256]
/-- Krotov masks `(m = 64, r = 29)`. -/
def rkmMasksPack_m64_r29 : List (List Bool) := [rkmWbTraj01 29 331350016,rkmWbTraj01 29 268435456,
  rkmWbTraj01 18 206292,rkmWbTraj01 23 7563786,rkmWbTraj01 26 52761689,rkmWbTraj01 27 68225630,
  rkmWbTraj01 28 144927072,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 29)`. -/
def rkmRowPack_m64_r29 : List ℕ := [0,0,0,0,0,0,6,34,0,69,27,4,109,2255,2362,796,38277,98199,
  429026,382242,441091,18457744,23040613,3093367,64321191,172934092,161017163,9412321572,
  990143419280]
/-- Krotov masks `(m = 2, r = 12)`. -/
def rkmMasksPack_m2_r12 : List (List Bool) := [[],[],[],[],rkmWbTraj01 6 56,rkmWbTraj01 10 806,[],
  []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 12)`. -/
def rkmRowPack_m2_r12 : List ℕ := [7959080,1345306,2283146133,34264102,1379829071,903141566,
  1437449499,12537793752,2298518147,9611248964,432029762390,537177937310]
/-- Krotov masks `(m = 2, r = 32)`. -/
def rkmMasksPack_m2_r32 : List (List Bool) := [[],[],rkmWbTraj01 3 7,rkmWbTraj01 32 3221342082,
  rkmWbTraj01 23 6712747,rkmWbTraj01 28 214865563,rkmWbTraj01 29 288428916,[]]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 32)`. -/
def rkmRowPack_m2_r32 : List ℕ := [151266,1669827,0,434317,491345,33539624,93641111,79992510,
  69256070,70246584,98132457,180472017,295629214,138708897,153383931,138507074,121581,256212772,
  83963825,1540228121,38046821,752443584,2539952559,944165420,811,98131054,11966555316,
  10277479199,3377255083,54187194439,502764447011,409819321250]
/-- Krotov masks `(m = 2, r = 17)`. -/
def rkmMasksPack_m2_r17 : List (List Bool) := [[],[],[],[]]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 17)`. -/
def rkmRowPack_m2_r17 : List ℕ := [116939,164380,19714,2652323,14070247,55904340,417328242,
  270175614,5396593184,33284989,28061657932,20977411316,46950474733,353830625225,392815806715,
  137173569494,14000140703]
/-- Krotov masks `(m = 4, r = 36)`. -/
def rkmMasksPack_m4_r36 : List (List Bool) := [[],[],rkmWbTraj01 1 1,rkmWbTraj01 29 402660584,
  rkmWbTraj01 23 4236905,rkmWbTraj01 22 2105892,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 36)`. -/
def rkmRowPack_m4_r36 : List ℕ := [3903317,18513793,38707581,341788,57515473,19540051,39782499,
  56293200,29389708,112048680,42644316,126716175,61007314,208001821,198114026,88655016,674558917,
  15785533,1147311678,691353724,1561654525,4451412617,22381564,9587004342,17241675353,28164987,
  68074582708,234030200802,308356605534,222239235866,97955853371,27410880298,4855534401,522743695,
  30886144,759298]
/-- Krotov masks `(m = 8, r = 27)`. -/
def rkmMasksPack_m8_r27 : List (List Bool) := [[],[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 27)`. -/
def rkmRowPack_m8_r27 : List ℕ := [46911299,36945586,42076,32513476,14941674,16080126,908249,
  3746681,496223420,1704710397,1072856081,55634065577,214155843071,320465042688,250926571038,
  115550853723,33059690927,6016880373,698387096,50872274,2239375,55528,677,1]
/-- Krotov masks `(m = 64, r = 22)`. -/
def rkmMasksPack_m64_r22 : List (List Bool) := [[],[],rkmWbTraj01 7 112,rkmWbTraj01 14 14561,
  rkmWbTraj01 18 223558,rkmWbTraj01 20 887514,rkmWbTraj01 21 1141238,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 22)`. -/
def rkmRowPack_m64_r22 : List ℕ := [0,0,0,0,0,0,1,81,370,1239,43601,27909,2050,46058,7549466,
  2671146,89698,75677370,130580314,128032387,10372950880,989282327134]
/-- Krotov masks `(m = 16, r = 15)`. -/
def rkmMasksPack_m16_r15 : List (List Bool) := [rkmWbTraj01 15 32754,rkmWbTraj01 12 3569,
  rkmWbTraj01 14 13456,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 15)`. -/
def rkmRowPack_m16_r15 : List ℕ := [14134,25138,213378,399108,5346440,1649443,24132111,1313888086,
  719116,509557661,6146823427,3043755838,530604195,37959283536,950463431608]
/-- Krotov masks `(m = 4, r = 23)`. -/
def rkmMasksPack_m4_r23 : List (List Bool) := [[],rkmWbTraj01 1 1,rkmWbTraj01 19 471997,
  rkmWbTraj01 21 1201525,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 23)`. -/
def rkmRowPack_m4_r23 : List ℕ := [3666,50785,82890,210795,398339,497610,568174,104,1392097,
  552395,26334446,298680795,105058956,3577648550,2357053753,1960786170,560804280,1124067352,
  13115021678,7098943631,5825261329,235710542937,728236038743]
/-- Krotov masks `(m = 4, r = 17)`. -/
def rkmMasksPack_m4_r17 : List (List Bool) := [[],[],rkmWbTraj01 5 26,rkmWbTraj01 11 1842,
  rkmWbTraj01 15 25749,[],rkmWbTraj01 16 32769,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 17)`. -/
def rkmRowPack_m4_r17 : List ℕ := [1545,8974412,570462,408805314,607308265,311142548,6398288,
  1344975939,127159455,2138675631,875359582,191604573,8084054640,7522405194,26119966,171894320116,
  806452051499]
/-- Krotov masks `(m = 16, r = 19)`. -/
def rkmMasksPack_m16_r19 : List (List Bool) := [[],rkmWbTraj01 16 57036,rkmWbTraj01 18 215317,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 19)`. -/
def rkmRowPack_m16_r19 : List ℕ := [387,192,169252,117230,7053641,250231,3804207,3059104,27592037,
  40154157,71611639,1633717753,117797850,2645279998,9479464571,2846563663,953349886,38609904554,
  943560109436]
/-- Krotov masks `(m = 4, r = 19)`. -/
def rkmMasksPack_m4_r19 : List (List Bool) := [[],[],rkmWbTraj01 15 29530,rkmWbTraj01 17 74377,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 19)`. -/
def rkmRowPack_m4_r19 : List ℕ := [2158513,3159296,39360039,44790992,57847036,909985,65814590,
  70564804,69849904,1091430747,4120551186,1446078148,255255654,942871325,9095411553,7299813410,
  7093223420,214783044839,753517102650]
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
private def uMulZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uConsNat (Nat.mul b z) (uMulZ z bs)
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | Int.negSucc _ :: _ => none
  | Int.ofNat n :: xs =>
    match uToNatHb xs with | some ns => some (uConsNat n ns) | none => none
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfNatHb ns
private theorem uToNatHb_sound :
    ∀ (hb : List ℤ) (ns : List ℕ), uToNatHb hb = some ns → hb = uOfNatHb ns
  | [], _, h => by
    injection h with h'
    subst h'
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
  cases a <;> cases b <;>
    dsimp only [primIntMul] <;>
    simp only [bPrimOfNat_eq, bPrimNegOfNat_eq, Nat.mul_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;>
    push_cast <;> ring
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
  | [], _, h => by
    injection h with h'
    subst h'
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
  | succ k =>
    dsimp only
    rw [Int.negSucc_eq]
    omega
private theorem bRawAdd_eq (a b : ℤ) : muxRawIntAdd a b = a + b := by
  cases a <;> cases b <;>
    dsimp only [muxRawIntAdd] <;>
    simp only [bPrimOfNat_eq, bPrimNegSucc_eq, bRawSubNat_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;>
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
  cases a <;> cases b <;>
    dsimp only [muxRawIntMul] <;>
    simp only [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq] <;>
    push_cast <;> ring
private def bStepVal (v P Q d : ℕ) : ℕ := match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) =
      ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  unfold bStepVal at hv ⊢
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
private abbrev bCellVal (d b0 bz0 c0 b bz v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) bz) (Nat.add (Nat.mul b c1) bz0) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCellVal d b0 (Nat.mul b0 z) c0 b (Nat.mul b z) v c1)
    (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCellVal d b0 (Nat.mul b0 z) c0 b (Nat.mul b z) v c1) rest) =
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
  | _ :: _ => by
    unfold bHeadOr
    rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | _ :: _ => by
    unfold bTailN
    rw [bDec_cons]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _, _, _ => []
  | rem + 1, b0, bz0, c0, bns, bzs, vs, cs => match bns, bzs with
    | b :: bR, bz :: bzR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal d b0 bz0 c0 b bz v (bHeadOr z cT))
          (bSlide z d rem b bz c bR bzR vT cT)
      | v :: vT, [] =>
        uConsNat (bCellVal d b0 bz0 c0 b bz v z) (bSlide z d rem b bz z bR bzR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal d b0 bz0 c0 b bz z (bHeadOr z cT))
          (bSlide z d rem b bz c bR bzR [] cT)
      | [], [] =>
        uConsNat (bCellVal d b0 bz0 c0 b bz z z) (bSlide z d rem b bz z bR bzR [] [])
    | _, _ => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) bz0 d)
        (bSlide z d rem 0 0 z [] [] (bTailN vs) (bTailN cs))
private theorem bSlide_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSlide z d rem b0 (Nat.mul b0 z) c0 bns (uMulZ z bns) vs cs) = true →
      bDec z (bSlide z d rem b0 (Nat.mul b0 z) c0 bns (uMulZ z bns) vs cs) =
      muxFastSlideLoopAux d rem (primIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSlide, uMulZ, uOfNatHb, muxFastSlideLoopAux] at h ⊢
      have hp := bAllPos_uCons h
      have hp2 : bAllPos (bSlide z d rem 0 (Nat.mul 0 z) z [] (uMulZ z [])
          (bTailN vs) (bTailN cs)) = true := by
        dsimp only [uMulZ]
        rw [← n0m z]
        exact hp.2
      have hi := bSlide_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp2
      dsimp only [uMulZ] at hi
      rw [← n0m z, bPrimMul0 z, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi
      rw [bHeadOr_eq z vs] at hc
      exact hc
    | cons b bR =>
      rw [uMulZ, uConsNat_eq] at h ⊢
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
private theorem bSlide_len (z d : ℕ) : ∀ (rem b0 bz0 c0 : ℕ) (bns bzs vs cs : List ℕ),
    altListLen (bSlide z d rem b0 bz0 c0 bns bzs vs cs) = rem
  | 0, _, _, _, _, _, _, _ => rfl
  | rem + 1, _, _, _, bns, bzs, vs, cs => by
    cases bns with
    | nil =>
      dsimp only [bSlide]
      rw [uConsNat_eq, altListLen, Nat.add_eq, bSlide_len]
    | cons _ _ =>
      cases bzs with
      | nil =>
        dsimp only [bSlide]
        rw [uConsNat_eq, altListLen, Nat.add_eq, bSlide_len]
      | cons _ _ =>
        cases vs with
        | nil =>
          cases cs with
          | nil =>
            dsimp only [bSlide]
            rw [uConsNat_eq, altListLen, Nat.add_eq, bSlide_len]
          | cons _ _ =>
            dsimp only [bSlide]
            rw [uConsNat_eq, altListLen, Nat.add_eq, bSlide_len]
        | cons _ _ =>
          cases cs with
          | nil =>
            dsimp only [bSlide]
            rw [uConsNat_eq, altListLen, Nat.add_eq, bSlide_len]
          | cons _ _ =>
            dsimp only [bSlide]
            rw [uConsNat_eq, altListLen, Nat.add_eq, bSlide_len]
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uConsNat b (uConsNat (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs => match hbz with
    | [] =>
      uConsNat (bStepVal (bHeadOr z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTailN vs) (bTailN cs))
    | [_] => []
    | b :: bz :: bR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bStepVal v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHeadOr z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] =>
        uConsNat (bStepVal v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT =>
        uConsNat (bStepVal z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHeadOr z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
      | [], [] =>
        uConsNat (bStepVal z (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR [] [])
private theorem bSlZ_eq (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs =
      bSlide z d rem b0 (Nat.mul b0 z) c0 bns (uMulZ z bns) vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, _, _, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTailN vs) (bTailN cs)
      dsimp only [mkHbZ, uMulZ] at hrec
      rw [← n0m z] at hrec
      dsimp only [mkHbZ, uMulZ, bSlZ, bSlide]
      rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ, uMulZ]
      rw [uConsNat_eq, uConsNat_eq, uConsNat_eq]
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSlide, bCellVal]
          rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT =>
          dsimp only [bSlZ, bSlide, bCellVal]
          rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSlide, bCellVal]
          rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT =>
          dsimp only [bSlZ, bSlide, bCellVal]
          rw [bSlZ_eq z d rem b c bR vT cT]
private def uCN4 (x1 x2 x3 x4 : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x1 with
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
    uCN4 x1 x2 x3 x4 xs = uConsNat x1 (uConsNat x2 (uConsNat x3 (uConsNat x4 xs))) := by
  unfold uCN4
  rw [n1a x1, n1a x2, n1a x3, n1a x4, uConsNat_eq, uConsNat_eq, uConsNat_eq, uConsNat_eq]
  cases xs <;> rfl
private def bAP4 : List ℕ → Bool
  | a :: b :: c :: d :: xs =>
    cond (Nat.ble a 0) false (cond (Nat.ble b 0) false
      (cond (Nat.ble c 0) false (cond (Nat.ble d 0) false (bAP4 xs))))
  | xs => bAllPos xs
private theorem bAP4e : ∀ (xs : List ℕ), bAP4 xs = bAllPos xs
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: xs => by
    dsimp only [bAP4, bAllPos]
    rw [bAP4e xs]
private def bChkP (out : List ℕ) : Option (List ℕ) := match out with
  | [] => some []
  | x :: xs => cond (bAP4 (x :: xs)) (some (x :: xs)) none
private theorem bChkPe (out : List ℕ) :
    bChkP out = cond (bAllPos out) (some out) none := by
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
private def fH4 {α : Type} (h : HbZ4) (k : HbZ4 → α) : α := match h with
  | HbZ4.tail l => fL l fun lF => k (HbZ4.tail lF)
  | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r => k (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r)
private theorem fH4e {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ =>
    dsimp only [fH4, fL]
    rw [bForceList_eq]
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
    uCN4 (bStepVal v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
      (bStepVal v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
      (bStepVal v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
      (bStepVal v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 c5) z3) d)
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
          dsimp only [bSlZ, bHeadOr]
          rw [uCN4e]
          exact congrArg (fun r => uConsNat _ (uConsNat _ (uConsNat _ (uConsNat _ r))))
            (bSlZ4_eq z d bR rem1 (Nat.mul b4 c4) z4 vR (c5 :: cR))
private def bNL : ℕ → ℕ → ℕ → ℕ
  | 0, _, l => l
  | s + 1, mL, l => bNL s mL (highdNatMin mL (Nat.add l 1))
private def bStg (z dg mL cL : ℕ) (h4 : HbZ4) (vns cns : List ℕ) : Option (List ℕ) :=
  fN (highdNatMin mL (Nat.add cL 1)) fun nL =>
    fN (Nat.mul dg wdScale) fun d => bChkP (bSlZ4 z d h4 nL 0 0 vns cns)
private theorem bStg_sound (z dg mL cL : ℕ) (bns vns cns out : List ℕ)
    (hc : altListLen cns = cL)
    (h : bStg z dg mL cL (toH4 (mkHbZ z bns)) vns cns = some out) :
    bDec z out = muxFastHornerStage dg mL (uOfNatHb bns) (bDec z vns) (bDec z cns) ∧
      altListLen out = highdNatMin mL (Nat.add cL 1) := by
  unfold bStg at h
  dsimp only [fN] at h
  rw [bForceNat_eq, bForceNat_eq] at h
  set nL := highdNatMin mL (Nat.add cL 1)
  set d := Nat.mul dg wdScale
  have hsl := bSlZ_eq z d nL 0 z bns vns cns
  rw [← n0m z] at hsl
  rw [bChkPe, bSlZ4_eq, hbz4L_toH4, hsl] at h
  revert h
  cases hp : bAllPos (bSlide z d nL 0 0 z bns (uMulZ z bns) vns cns) with
  | false =>
    intro h
    dsimp only [cond] at h
    cases h
  | true =>
    intro h
    dsimp only [cond] at h
    injection h with h'
    subst h'
    refine And.intro ?_ (bSlide_len z d nL 0 0 z bns (uMulZ z bns) vns cns)
    unfold muxFastHornerStage
    rw [bDec_len z cns, hc, bForceNat_eq, bForceNat_eq, ← bPrimMul0 z]
    have hp0 : bAllPos (bSlide z d nL 0 (Nat.mul 0 z) z bns (uMulZ z bns) vns cns) = true := by
      rw [← n0m z]
      exact hp
    have hs := bSlide_sound z d nL 0 z bns vns cns hp0
    rw [← n0m z] at hs
    exact hs
private def bBdD (z dg mL cL : ℕ) (h4 : HbZ4) (vns cns : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (highdNatMin mL (Nat.add cL 1)) fun nL =>
    match bStg z dg mL cL h4 vns cns with | none => none | some o => k nL o
private theorem bBdD_sound {z dg mL cL : ℕ} {bns vns cns out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : List ℤ → List ℤ} {endL : ℕ}
    (hc : altListLen cns = cL)
    (h : bBdD z dg mL cL (toH4 (mkHbZ z bns)) vns cns kB = some out)
    (hk : ∀ (mid : List ℕ), altListLen mid = highdNatMin mL (Nat.add cL 1) →
      kB (highdNatMin mL (Nat.add cL 1)) mid = some out →
      bDec z out = kU (bDec z mid) ∧ altListLen out = endL) :
    bDec z out = HighDForce.withForcedList
      (muxFastHornerStage dg mL (uOfNatHb bns) (bDec z vns) (bDec z cns)) kU ∧
      altListLen out = endL := by
  unfold bBdD at h
  dsimp only [fN] at h
  rw [bForceNat_eq] at h
  revert h
  cases hs : bStg z dg mL cL (toH4 (mkHbZ z bns)) vns cns with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some mid =>
    intro h
    dsimp only at h
    have hst := bStg_sound z dg mL cL bns vns cns mid hc hs
    rw [bForceList_eq, ← hst.1]
    exact hk mid hst.2 h
private def bStep (z mL cL : ℕ) (h4 : HbZ4) (vns : List ℕ) : Option (List ℕ) :=
  bBdD z 16 mL cL h4 vns vns fun l x => bBdD z 15 mL l h4 vns x fun l x =>
  bBdD z 14 mL l h4 vns x fun l x => bBdD z 13 mL l h4 vns x fun l x =>
  bBdD z 12 mL l h4 vns x fun l x => bBdD z 11 mL l h4 vns x fun l x =>
  bBdD z 10 mL l h4 vns x fun l x => bBdD z 9 mL l h4 vns x fun l x =>
  bBdD z 8 mL l h4 vns x fun l x => bBdD z 7 mL l h4 vns x fun l x =>
  bBdD z 6 mL l h4 vns x fun l x => bBdD z 5 mL l h4 vns x fun l x =>
  bBdD z 4 mL l h4 vns x fun l x => bBdD z 3 mL l h4 vns x fun l x =>
  bBdD z 2 mL l h4 vns x fun l x => bStg z 1 mL l h4 vns x
private theorem bStep_sound (z mL cL : ℕ) (bns vns out : List ℕ)
    (hc : altListLen vns = cL)
    (h : bStep z mL cL (toH4 (mkHbZ z bns)) vns = some out) :
    bDec z out = muxFastHornerT16Step mL (uOfNatHb bns) (bDec z vns) ∧
      altListLen out = bNL 16 mL cL := by
  unfold bStep at h
  unfold muxFastHornerT16Step
  refine bBdD_sound hc h fun _ hc h => bBdD_sound hc h fun _ hc h => ?_
  refine bBdD_sound hc h fun _ hc h => bBdD_sound hc h fun _ hc h => ?_
  refine bBdD_sound hc h fun _ hc h => bBdD_sound hc h fun _ hc h => ?_
  refine bBdD_sound hc h fun _ hc h => bBdD_sound hc h fun _ hc h => ?_
  refine bBdD_sound hc h fun _ hc h => bBdD_sound hc h fun _ hc h => ?_
  refine bBdD_sound hc h fun _ hc h => bBdD_sound hc h fun _ hc h => ?_
  refine bBdD_sound hc h fun _ hc h => bBdD_sound hc h fun _ hc h => ?_
  refine bBdD_sound hc h fun _ hc h => bStg_sound z 1 mL _ bns vns _ out hc h
private def bIter (z : ℕ) : ℕ → ℕ → ℕ → HbZ4 → List ℕ → Option (List ℕ)
  | 0, _, _, _, vns => some vns
  | k + 1, mL, cL, h4, vns => match bStep z mL cL h4 vns with
    | none => none
    | some vNext => fN (bNL 16 mL cL) fun nL => bIter z k mL nL h4 vNext
private theorem bIter_sound (z : ℕ) : ∀ (k mL cL : ℕ) (bns vns out : List ℕ),
    altListLen vns = cL → bIter z k mL cL (toH4 (mkHbZ z bns)) vns = some out →
      bDec z out = muxFastIterFullT16 k mL (uOfNatHb bns) (bDec z vns)
  | 0, _, _, _, _, _, _, h => by
    dsimp only [bIter] at h
    injection h with h'
    subst h'
    rfl
  | k + 1, mL, cL, bns, vns, out, hc, h => by
    dsimp only [bIter] at h
    revert h
    cases hs : bStep z mL cL (toH4 (mkHbZ z bns)) vns with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some vNext =>
      intro h
      dsimp only [fN] at h
      rw [bForceNat_eq] at h
      have hst := bStep_sound z mL cL bns vns vNext hc hs
      unfold muxFastIterFullT16
      rw [bForceList_eq, ← hst.1]
      exact bIter_sound z k mL (bNL 16 mL cL) bns vNext out hst.2 h
private abbrev zB : ℕ := 2000000000000000
private def fIter (k mL : ℕ) (hb v : List ℤ) : List ℤ := match uToNatHb hb with
  | none => muxFastIterFullT16 k mL hb v
  | some bns => match bEnc zB v with
    | none => muxFastIterFullT16 k mL hb v
    | some vns => fN (altListLen vns) fun cL =>
      fH4 (toH4 (mkHbZ zB bns)) fun h4 => match bIter zB k mL cL h4 vns with
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
      dsimp only [fN]
      rw [bForceNat_eq, fH4e]
      cases hi : bIter zB k mL (altListLen vns) (toH4 (mkHbZ zB bns)) vns with
      | none => rfl
      | some out =>
        dsimp only
        rw [bIter_sound zB k mL (altListLen vns) bns vns out rfl hi,
          ← uToNatHb_sound hb bns hh, bEnc_sound zB v vns hv]
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
  fL bns fun bF => fL vns fun vF => fL out fun oF => fN (altListLen vF) fun cL =>
    fH4 (toH4 (mkHbZ zB bF)) fun h4 =>
      match bIter zB k mL cL h4 vF with | none => false | some w => bNatListEq w oF
private theorem bSlideChk_sound {k mL : ℕ} {bns vns out : List ℕ} {s : List Bool}
    (h : atF (bSlideChk k mL bns vns out :: s) = true) :
    WalkOk (some (k, mL, bns, vns, out)) := by
  unfold bSlideChk at h
  dsimp only [fL, fN] at h
  simp only [bForceList_eq, bForceNat_eq, fH4e] at h
  unfold WalkOk
  revert h
  cases hi : bIter zB k mL (altListLen vns) (toH4 (mkHbZ zB bns)) vns with
  | none =>
    intro h
    dsimp only [atF] at h
    cases h
  | some w =>
    intro h
    dsimp only at h
    rw [← bhd_eq h]
    exact (bIter_sound zB k mL (altListLen vns) bns vns w rfl hi).symm
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
    (hw : WalksOk wcs) : rkmEvalT16Lo12 m lm r ls ts ns mks = y :=
  (bEvalLo12W_eq m lm r ls ts ns mks wcs hw).symm.trans (bhd_eq h)
private theorem bh0_eq {m lm r : ℕ} {ls ts ns : List ℕ} {mks : List (List Bool)}
    {y : List ℕ} {s : List Bool}
    (h : atF (bNatListEq (bEvalLo12W m lm r ls ts ns mks []) y :: s) = true) :
    rkmEvalT16Lo12 m lm r ls ts ns mks = y := bhW_eq h wNil
private def wc_rkmTraj_m128_r128_s1_hb : List ℕ := pCat [155034394947328, 217538839719061,
  264331707579323, 302801552631500, 335834088266751, 364920974256682, 390955151175186,
  414522828441046, 436034235789360, 455790270627024, 474019752199428, 490901742647315,
  506579667276583, 521170646419924, 534771888969681, 547465207157752, 559320287725113,
  570397115168878, 580747801861885, 590417993888320, 599447967329089, 607873494712446,
  615726538121309, 623035809706531, 629827229473520, 636124302553054, 641948432692643,
  647319184732685, 652254505910736, 656770913662486, 660883655950495, 664606848905479,
  667953595607283, 670936089089922, 673565702074211, 675853065473508, 677808137354388,
  679440263743101, 680758232434432, 681770320769835, 682484338197043, 682907664296658,
  683047282856824, 682909812490702, 682501534219526, 681828416384036, 680896137196604,
  679710105203975, 678275477894560, 676597178653774, 674679912244886, 672528178970636,
  670146287651831, 667538367542711, 664708379288720, 661660125020077, 658397257663895,
  654923289548326, 651241600364168, 647355444542246, 643267958098743, 638982164995159,
  634500983054810, 629827229473520] [624963625958436, 619912803525549, 614677306983563,
  609259599129141, 603662064676190, 597887013939782, 591936686293420, 585813253416685,
  579518822348815, 573055438362371, 566425087669979, 559629699975998, 552671150883998,
  545551264170015, 538271813930758, 530834526615187, 523241082947232, 515493119746793,
  507592231655632, 499539972774241, 491337858215323, 482987365579106, 474489936355314,
  465846977256267, 457059861485282, 448129929944217, 439058492383758, 429846828499782,
  420496188978904, 411007796496111, 401382846667178, 391622508958390, 381727927555932,
  371700222197136, 361540488965665, 351249801052540, 340829209484832, 330279743823718,
  319602412833460, 308798205122842, 297868089760426, 286813016864969, 275633918172228,
  264331707579323, 252907281667749, 241361520206078, 229695286633322, 217909428523874,
  206004778034898, 193982152336986, 181842354028849, 169586171536791, 157214379499629,
  144727739139746, 132126998620869, 119412893393179, 106586146526288, 93647469030632,
  80597560167770, 67437107750050, 54166788430121, 40787267980689, 27299201564948, 13703233998051]
private def wc_rkmTraj_m128_r128_s1_v0 : List ℕ := pCat [1999998049413742, 1999988833776051,
  2000044801329041, 2000145466251789, 2000405387396637, 2001001388021238, 2002237668646907,
  2004587117404698, 2008715329359595, 2015467445667076, 2025799573180612, 2040646038489442,
  2060730589210550, 2086350080237862, 2117176715215742, 2152132502785867, 2189382370448299,
  2226470014988935, 2260588015123204, 2288939965834234, 2309127461011475, 2319486284963123,
  2319306758648354, 2308899577968198, 2289502900586508, 2263059332723676, 2231914615073282,
  2198498629035234, 2165043747300094, 2133379238618209, 2104819179224797, 2080140966277523,
  2059636395448668, 2043209378972732, 2030493528880936, 2020967227093972, 2014050991402137,
  2009179601184294, 2005847896970276, 2003633569416130, 2002202495664997, 2001302645514974,
  2000751866877802, 2000423570521214, 2000232937877825, 2000125065344682, 2000065563605916,
  2000033562788788, 2000016778654155, 2000008191980827, 2000003906401023, 2000001819444747,
  2000000827728571, 2000000367817068, 2000000159651698, 2000000067687884, 2000000028030914,
  2000000011338115, 2000000004479248, 2000000001728258, 2000000000651215, 2000000000239615,
  2000000000086084, 2000000000030191] (pCat [2000000000010332, 2000000000003447, 2000000000001118,
  2000000000000352, 2000000000000104, 2000000000000027, 2000000000000006, 2000000000000001,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m128_r128_s1_v1 : List ℕ := pCat [2000000766924678, 2000002064732018,
  2000003815139144, 2000005540814107, 2000006615114697, 2000006527305249, 2000005101346689,
  2000002564725551, 1999999451396828, 1999996403451067, 1999993967990287, 1999992465574415,
  1999991958988015, 1999992306313867, 1999993259474309, 1999994571715190, 1999996097648063,
  1999997898218533, 2000000395497987, 2000004659936731, 2000012961472317, 2000029781686874,
  2000063568013721, 2000129602810089, 2000254433149159, 2000482313780485, 2000883988205900,
  2001567793637895, 2002692460121675, 2004480066565048, 2007226492887604, 2011305571701076,
  2017162334520753, 2025290701488670, 2036192108980880, 2050314175564176, 2067972512618747,
  2089263673145825, 2113982009601890, 2141556561811684, 2171024688054394, 2201056056998810,
  2230033705221370, 2256189035256046, 2277776759035622, 2293266353697409, 2301521029072409,
  2301935208508926, 2294507507468626, 2279837075459620, 2259044604306319, 2233632308938903,
  2205306919668367, 2175794248615539, 2146672623427307, 2119246237339773, 2094470124201583,
  2072928372720263, 2054858509378711, 2040209189105700, 2028716006745918, 2019981081262203,
  2013545159088697, 2008945169235253] (pCat [2005754354448570, 2003605517430182, 2002200168219553,
  2001307406860639, 2000756443230248, 2000426080326607, 2000233609037154, 2000124651850627,
  2000064720367875, 2000032691340424, 2000016061431996, 2000007673607411, 2000003564315475,
  2000001609179979, 2000000705941364, 2000000300846084, 2000000124508862, 2000000050026097,
  2000000019506757, 2000000007379179, 2000000002707059, 2000000000962663, 2000000000331698,
  2000000000110681, 2000000000035744, 2000000000011161, 2000000000003364, 2000000000000975,
  2000000000000268, 2000000000000068, 2000000000000014, 2000000000000002, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m128_r128_s1_v2 : List ℕ := pCat [2000000000000691, 2000000000004886,
  2000000000024149, 2000000000096454, 2000000000329911, 2000000000997953, 2000000002724135,
  2000000006804112, 2000000015707437, 2000000033769859, 2000000068015028, 2000000128931792,
  2000000230897521, 2000000391823074, 2000000631566815, 2000000968791501, 2000001416259654,
  2000001975057910, 2000002628805489, 2000003339359214, 2000004045674246, 2000004667158078,
  2000005112032549, 2000005290030163, 2000005127491239, 2000004581973569, 2000003653171161,
  2000002387438593, 2000000874465865, 1999999236345303, 1999997610967781, 1999996132923772,
  1999994915544062, 1999994037306060, 1999993534710799, 1999993402241838, 1999993598554678,
  1999994056964546, 1999994697810406, 1999995440429897, 1999996213256479, 1999996962021330,
  1999997658712642, 1999998319321085, 1999999049876352, 2000000164380508, 2000002465891339,
  2000007868896562, 2000020685263003, 2000050109696858, 2000114713831368, 2000250033425372,
  2000520478104274, 2001036584548681, 2001977781075418, 2003619062505923, 2006357200063095,
  2010728637571326, 2017407930944134, 2027173936487267, 2040832709007845, 2059092666652598,
  2082399261894778, 2110751464384428] (pCat [2143536939443102, 2179431548799932, 2216406548638861,
  2251870842570851, 2282947350468751, 2306848287233428, 2321283691816927, 2324821082640274,
  2317118439903546, 2298978331739925, 2272211403284880, 2239341089727829, 2203215679969596,
  2166609439688453, 2131888428551306, 2100792809342543, 2074354620764381, 2052938338405090,
  2036369165824345, 2024104712492567, 2015408801220779, 2009497606104583, 2005642933780663,
  2003230686287992, 2001781652613226, 2000946050215693, 2000483478463218, 2000237686318205,
  2000112349232104, 2000051030635672, 2000022259882813, 2000009318809328, 2000003741408808,
  2000001439506547, 2000000530316717, 2000000186900342, 2000000062952875, 2000000020243879,
  2000000006207929, 2000000001813145, 2000000000503679, 2000000000132875, 2000000000033227,
  2000000000007855, 2000000000001747, 2000000000000362, 2000000000000067, 2000000000000009,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m128_r128_s2_hb : List ℕ := pCat [137711842178821, 193612444800705,
  235726864038345, 270577439806632, 300706236722271, 327424642561488, 351516131498884,
  373494037113080, 393716883350034, 412447122240585, 429883939571069, 446182894470148,
  461468333266192, 475841586962915, 489386583038982, 502173805017865, 514263159052954,
  525706095751863, 536547211355942, 546825476712382, 556575194854581, 565826757200467,
  574607247956860, 582940932481313, 590849655792371, 598353170695189, 605469410183817,
  612214715296119, 618604027035375, 624651049065997, 630368386455728, 635767664644966,
  640859631985262, 645654248538954, 650160763323617, 654387781784481, 658343324959922,
  662034881550852, 665469453900177, 668653598722700, 671593463290846, 674294817670886,
  676763083513253, 679003359825075, 681020446090293, 682818863050297, 684402871413951,
  685776488728794, 686943504613724, 687907494526789, 688671832218871, 689239701004513,
  689614103964308, 689797873178729, 689793678080689, 689604033003103, 689231303988121,
  688677714916226, 687945353005919, 687036173728041, 685952005172816, 684694551902340,
  683265398316329, 681666011554465] [679897743954512, 677961835081479, 675859413339414,
  673591497173822, 671158995869279, 668562709943314, 665803331134221, 662881441976903,
  659797514957199, 656551911231292, 653144878892708, 649576550764961, 645846941693117,
  641955945302171, 637903330184241, 633688735469918, 629311665731573, 624771485157881,
  620067410928975, 615198505710367, 610163669170650, 604961628412758, 599590927190725,
  594049913762918, 588336727207977, 582449282000341, 576385250607242, 570142043827206,
  563716788539664, 557106302474389, 550307065535409, 543315187123534, 536126368790453,
  528735861419811, 521138415959624, 513328226516128, 505298864348913, 497043200963775,
  488553318059886, 479820401519585, 470834615888294, 461584954816766, 452059061640248,
  442243012522933, 432121052217059, 421675269200845, 410885192356368, 399727284793817,
  388174300928612, 376194458876198, 363750359016924, 350797546744361, 337282565148282,
  323140257553061, 308289933683067, 292629753686543, 276028199938986, 258310547558802,
  239236202760886, 218458016260800, 195442175501308, 169288660319515, 138240359613131,
  97756616233104]
private def wc_rkmTraj_m128_r128_s2_v0 : List ℕ := pCat [1999999999999309, 2000000000004886,
  2000000000024149, 1999999999903546, 2000000000329911, 2000000000997953, 2000000002724135,
  1999999993195888, 1999999984292563, 2000000033769859, 2000000068015028, 1999999871068208,
  2000000230897521, 2000000391823074, 1999999368433185, 2000000968791501, 1999998583740346,
  2000001975057910, 2000002628805489, 1999996660640786, 2000004045674246, 2000004667158078,
  2000005112032549, 2000005290030163, 2000005127491239, 1999995418026431, 1999996346828839,
  1999997612561407, 1999999125534135, 1999999236345303, 1999997610967781, 2000003867076228,
  2000005084455938, 2000005962693940, 2000006465289201, 1999993402241838, 1999993598554678,
  1999994056964546, 2000005302189594, 2000004559570103, 1999996213256479, 1999996962021330,
  2000002341287358, 1999998319321085, 1999999049876352, 1999999835619492, 1999997534108661,
  1999992131103438, 1999979314736997, 1999949890303142, 1999885286168632, 1999749966574628,
  1999479521895726, 1998963415451319, 2001977781075418, 2003619062505923, 2006357200063095,
  2010728637571326, 2017407930944134, 2027173936487267, 2040832709007845, 2059092666652598,
  2082399261894778, 2110751464384428] (pCat [2143536939443102, 2179431548799932, 2216406548638861,
  2251870842570851, 2282947350468751, 2306848287233428, 2321283691816927, 2324821082640274,
  2317118439903546, 2298978331739925, 2272211403284880, 2239341089727829, 2203215679969596,
  2166609439688453, 2131888428551306, 2100792809342543, 2074354620764381, 2052938338405090,
  2036369165824345, 2024104712492567, 2015408801220779, 2009497606104583, 2005642933780663,
  2003230686287992, 2001781652613226, 2000946050215693, 2000483478463218, 2000237686318205,
  2000112349232104, 2000051030635672, 2000022259882813, 2000009318809328, 2000003741408808,
  2000001439506547, 2000000530316717, 2000000186900342, 2000000062952875, 2000000020243879,
  2000000006207929, 2000000001813145, 2000000000503679, 2000000000132875, 2000000000033227,
  2000000000007855, 2000000000001747, 2000000000000362, 2000000000000067, 2000000000000009,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m128_r128_s2_v1 : List ℕ := pCat [1999999977156643, 2000000119371756,
  1999999671512852, 2000000495583500, 1999999847297055, 1999998937963609, 2000002517328124,
  1999997349647193, 2000000924262605, 2000000730016325, 1999999809210613, 1999998639057809,
  2000000759716506, 2000001883513677, 1999997745089162, 1999998387946117, 2000004824337154,
  1999997006598680, 2000000374362319, 1999998692418476, 2000001135759398, 2000002039733009,
  1999998663020172, 1999996841099942, 2000005127080583, 1999992642300333, 2000015093392774,
  1999968558164086, 2000062050120183, 1999891056902595, 2000175650290151, 1999742603175284,
  2000323073969704, 1999661539705086, 2000277245442829, 1999884300560270, 1999898212631846,
  2000264201538018, 1999731140695678, 2000072815362753, 2000194170106458, 1999727928647429,
  2000096087128787, 2000195817552458, 1999741318512772, 2000008783830195, 2000271296184787,
  1999832075216127, 1999798484544826, 2000245670582223, 2000112846660313, 1999715227239647,
  1999940420742975, 2000309625579438, 2000065323438268, 1999687048331228, 1999884949744520,
  2000298620151911, 2000215823723537, 1999774333210251, 1999660988490191, 2000040018445906,
  2000384219144429, 2000247919072327] (pCat [1999800541209894, 1999546835653528, 1999745311088389,
  2000201540458657, 2000524512876683, 2000477246953172, 2000105947530630, 1999630383941287,
  1999262926242152, 1999102339353609, 1999137436027846, 1999319240407245, 1999651956738802,
  2000280181152401, 2001571968897543, 2004196850714948, 2009179189936188, 2017885537212398,
  2031896304215357, 2052729106834507, 2081426233628047, 2118081471017275, 2161438669064090,
  2208716997515826, 2255784374063997, 2297710410028812, 2329609063940908, 2347573547174588,
  2349456750560038, 2335283706371285, 2307189281607980, 2268915152800863, 2225023078018669,
  2180044479760824, 2137774056558496, 2100842225170205, 2070602129317298, 2047279030261921,
  2030278348770095, 2018539952345026, 2010850744137382, 2006067461093831, 2003239899119597,
  2001651083259189, 2000802430269167, 2000371604913919, 2000163820232225, 2000068671308544,
  2000027336235445, 2000010318195262, 2000003686492464, 2000001244192604, 2000000395729164,
  2000000118286034, 2000000033117205, 2000000008650178, 2000000002097630, 2000000000469377,
  2000000000096165, 2000000000017851, 2000000000002956, 2000000000000425, 2000000000000049,
  2000000000000003] [2000000000000000])
private def wc_rkmTraj_m128_r128_s2_v2 : List ℕ := pCat [2000001994237918, 1999997867077675,
  1999999130932913, 2000000434888594, 2000002957088148, 1999996790685879, 2000002786632662,
  1999994927079224, 2000008682646984, 1999979629813539, 2000048539095714, 1999910879192091,
  2000140379207944, 1999793775060717, 2000269595274797, 1999705889849915, 2000252551995072,
  1999864080742327, 1999965255474837, 2000188382803354, 1999763895016004, 2000142540637542,
  2000041741203674, 1999802410879280, 2000199846873722, 1999968546904771, 1999835994064568,
  2000203091840242, 1999956958961663, 1999837157447153, 2000194613360472, 1999996338620538,
  1999806109276890, 2000153732422606, 2000081935993260, 1999788719749722, 2000055594572625,
  2000177442581374, 1999842098921960, 1999908577834349, 2000205735852013, 1999994810733560,
  1999793099016939, 2000086274586647, 2000178227869115, 1999855462903804, 1999862499990270,
  2000183973356988, 2000100818932828, 1999791051322471, 1999922049240755, 2000220545772259,
  2000069047399618, 1999778488582120, 1999930396400595, 2000220226760756, 2000083416667968,
  1999782256514244, 1999882751528651, 2000201571393278, 2000164256631137, 1999836116375112,
  1999786345646104, 2000104461169718] (pCat [2000268803225227, 2000012884114321, 1999735005743476,
  1999857557297065, 2000194579713832, 2000253882676733, 1999951318145790, 1999704446674949,
  1999845152223878, 2000193897545962, 2000315825253845, 2000063355614068, 1999728538131744,
  1999683899641062, 1999976279107605, 2000306404595474, 2000353508736188, 2000075778066777,
  1999717016527517, 1999570610702344, 1999744802706074, 2000110657694682, 2000426369197667,
  2000506831931074, 2000317951584858, 1999964038832727, 1999610499345523, 1999397008198899,
  1999367532686075, 1999422199276179, 1999314468277642, 1998761550923019, 1997749720228867,
  1997038497625124, 1998693242501075, 2006292983576334, 2024424245563234, 2057300906295559,
  2106809123330969, 2170739625417485, 2242129553725410, 2310306676777690, 2363505616466525,
  2392168399908195, 2391668801240397, 2363427629601506, 2314091813285268, 2253254712015666,
  2190699230767706, 2134154921027766, 2088160917108241, 2054085403191647, 2030939439678508,
  2016474765354282, 2008146364790450, 2003728825050888, 2001573430540084, 2000608756680560,
  2000214417747548, 2000068094850574, 2000019237861482, 2000004739939928, 2000000986685089,
  2000000163686094] [2000000018750031])
private def wc_rkmTraj_m128_r128_s3_hb : List ℕ := pCat [137711842178821, 193612444800705,
  235726864038345, 270577439806632, 300706236722271, 327424642561488, 351516131498884,
  373494037113080, 393716883350034, 412447122240585, 429883939571069, 446182894470148,
  461468333266192, 475841586962915, 489386583038982, 502173805017865, 514263159052954,
  525706095751863, 536547211355942, 546825476712382, 556575194854581, 565826757200467,
  574607247956860, 582940932481313, 590849655792371, 598353170695189, 605469410183817,
  612214715296119, 618604027035375, 624651049065997, 630368386455728, 635767664644966,
  640859631985262, 645654248538954, 650160763323617, 654387781784481, 658343324959922,
  662034881550852, 665469453900177, 668653598722700, 671593463290846, 674294817670886,
  676763083513253, 679003359825075, 681020446090293, 682818863050297, 684402871413951,
  685776488728794, 686943504613724, 687907494526789, 688671832218871, 689239701004513,
  689614103964308, 689797873178729, 689793678080689, 689604033003103, 689231303988121,
  688677714916226, 687945353005919, 687036173728041, 685952005172816, 684694551902340,
  683265398316329, 681666011554465] [679897743954512, 677961835081479, 675859413339414,
  673591497173822, 671158995869279, 668562709943314, 665803331134221, 662881441976903,
  659797514957199, 656551911231292, 653144878892708, 649576550764961, 645846941693117,
  641955945302171, 637903330184241, 633688735469918, 629311665731573, 624771485157881,
  620067410928975, 615198505710367, 610163669170650, 604961628412758, 599590927190725,
  594049913762918, 588336727207977, 582449282000341, 576385250607242, 570142043827206,
  563716788539664, 557106302474389, 550307065535409, 543315187123534, 536126368790453,
  528735861419811, 521138415959624, 513328226516128, 505298864348913, 497043200963775,
  488553318059886, 479820401519585, 470834615888294, 461584954816766, 452059061640248,
  442243012522933, 432121052217059, 421675269200845, 410885192356368, 399727284793817,
  388174300928612, 376194458876198, 363750359016924, 350797546744361, 337282565148282,
  323140257553061, 308289933683067, 292629753686543, 276028199938986, 258310547558802,
  239236202760886, 218458016260800, 195442175501308, 169288660319515, 138240359613131,
  97756616233104]
private def wc_rkmTraj_m128_r128_s3_v0 : List ℕ := pCat [2000001994237918, 1999997867077675,
  1999999130932913, 2000000434888594, 2000002957088148, 2000003209314121, 1999997213367338,
  2000005072920776, 1999991317353016, 1999979629813539, 2000048539095714, 1999910879192091,
  2000140379207944, 1999793775060717, 2000269595274797, 1999705889849915, 2000252551995072,
  1999864080742327, 2000034744525163, 2000188382803354, 1999763895016004, 2000142540637542,
  1999958258796326, 1999802410879280, 2000199846873722, 2000031453095229, 1999835994064568,
  2000203091840242, 2000043041038337, 1999837157447153, 2000194613360472, 1999996338620538,
  1999806109276890, 2000153732422606, 2000081935993260, 1999788719749722, 2000055594572625,
  2000177442581374, 1999842098921960, 1999908577834349, 2000205735852013, 1999994810733560,
  1999793099016939, 2000086274586647, 2000178227869115, 1999855462903804, 1999862499990270,
  2000183973356988, 2000100818932828, 1999791051322471, 1999922049240755, 2000220545772259,
  2000069047399618, 2000221511417880, 2000069603599405, 2000220226760756, 1999916583332032,
  2000217743485756, 1999882751528651, 2000201571393278, 1999835743368863, 2000163883624888,
  1999786345646104, 1999895538830282] (pCat [1999731196774773, 1999987115885679, 1999735005743476,
  1999857557297065, 2000194579713832, 1999746117323267, 1999951318145790, 1999704446674949,
  1999845152223878, 2000193897545962, 1999684174746155, 1999936644385932, 2000271461868256,
  1999683899641062, 1999976279107605, 1999693595404526, 1999646491263812, 2000075778066777,
  2000282983472483, 1999570610702344, 1999744802706074, 1999889342305318, 1999573630802333,
  1999493168068926, 1999682048415142, 1999964038832727, 1999610499345523, 1999397008198899,
  1999367532686075, 1999422199276179, 1999314468277642, 1998761550923019, 2002250279771133,
  2002961502374876, 2001306757498925, 2006292983576334, 2024424245563234, 2057300906295559,
  2106809123330969, 2170739625417485, 2242129553725410, 2310306676777690, 2363505616466525,
  2392168399908195, 2391668801240397, 2363427629601506, 2314091813285268, 2253254712015666,
  2190699230767706, 2134154921027766, 2088160917108241, 2054085403191647, 2030939439678508,
  2016474765354282, 2008146364790450, 2003728825050888, 1998426569459916, 1999391243319440,
  1999785582252452, 1999931905149426, 1999980762138518, 2000004739939928, 2000000986685089,
  2000000163686094] [2000000018750031])
private def wc_rkmTraj_m128_r128_s3_v1 : List ℕ := pCat [2000046609309199, 1999849420902333,
  2000280926511113, 1999683904301056, 2000185816727681, 2000052563573940, 1999778236432432,
  2000199173854464, 2000001301813854, 1999819704242348, 2000136942376714, 2000065002299149,
  1999835451986348, 2000028411655682, 2000157689880670, 1999856889405902, 1999919875069025,
  2000212232528448, 1999975126178922, 1999801056392823, 2000122435694568, 2000137382176579,
  1999821143141359, 1999946265295245, 2000187392569455, 1999967953584049, 1999816572320767,
  2000104463344170, 2000107550427674, 1999916497212037, 1999876167638784, 2000250194418429,
  1999843066815576, 1999954315212221, 1999887319303304, 2000376731301718, 1999798852587275,
  2000014911380718, 1999968420512691, 2000305674237789, 1999698858017082, 1999961653838495,
  2000118432304624, 2000042943765763, 1999821703639100, 1999950498597188, 2000260478036689,
  1999904633562474, 2000027653410983, 1999916089350336, 2000168060185413, 2000080435904478,
  1999778129988464, 2000142055231434, 2000004243972310, 1999901930057926, 2000266715878089,
  1999673315827559, 2000125164218965, 2000037583663918, 1999983138945413, 2000081034792727,
  1999879093687053, 1999919780448164] (pCat [2000206448888904, 1999845025910910, 2000017555306561,
  2000301479966498, 1999699680828245, 1999935187269253, 2000091817796396, 1999862772210528,
  2000106198216569, 2000013822061132, 2000230492560870, 1999966358183222, 2000439577277257,
  1999561235414750, 2000384293411287, 2000293423319079, 1999883299690070, 2000158326106546,
  1999823619864828, 2000103161957963, 1999877945222743, 1999298004093899, 2000541130777307,
  2000053472383023, 1999127858565963, 2000455361271741, 1999938145118897, 1998928379115194,
  2000570736146781, 2000671122873140, 1998909682875889, 1999686907404082, 2000952220158853,
  1999537827481779, 1998761898665662, 2000613365942360, 2001271643243879, 1999157296782429,
  1997928372230691, 1999931828867256, 2001868046695144, 2001042354257579, 1997368070648595,
  1996543410730720, 1998321808771259, 2004893272516873, 2005924805246595, 2000907131288481,
  1985065132646375, 1971974062329125, 1983079032271923, 2035821033860386, 2139534788286625,
  2272609752215932, 2394228663657773, 2467804950520143, 2469885718652011, 2404349946459231,
  2301936767188292, 2196751416174503, 2110183209293136, 2051019940303467, 2018432976530284,
  2004764185826884] [2000736352328508])
private def wc_rkmTraj_m128_r128_s3_v2 : List ℕ := pCat [2000191881647635, 2000351432841569,
  2000242452062019, 1999889667983871, 1999744596724064, 1999929118361456, 2000155534242451,
  2000150650627204, 1999930801822544, 1999834160563323, 1999981430109352, 2000221458049252,
  1999998815725304, 1999914895115320, 1999759555118712, 2000324812660252, 1999950804035153,
  2000073932051748, 1999647371903296, 2000264823416872, 2000054963563366, 2000028948558025,
  1999731908213740, 2000067968924994, 2000221590640295, 1999907413567776, 1999931196726282,
  1999891106327618, 2000245945065026, 1999950740836654, 1999861679533505, 1999995557964215,
  2000116994139492, 2000094985796275, 1999779987173458, 1999921429008090, 2000407549586140,
  1999721977380686, 2000002765925521, 1999952380067452, 2000123121881237, 2000166576907296,
  1999678516110247, 1999989178581996, 2000263202000003, 1999838248987879, 1999929054469934,
  2000139240678877, 1999948315136660, 2000116378733098, 1999891979058816, 1999809303056053,
  2000338039342097, 1999692294081553, 2000198212082567, 1999866596891431, 2000109699059658,
  1999938057613863, 2000282734829321, 1999738397760086, 1999947873478206, 2000347713230991,
  1999656153824999, 2000099599560905] (pCat [2000010715287990, 1999801462149312, 2000325360825193,
  1999758878222330, 2000098838591614, 2000143482264487, 1999712856201393, 2000316346196309,
  1999916903123389, 1999996413106193, 2000164796239892, 1999538895567138, 2000425073020290,
  2000167312798830, 1999326191296800, 2000612914524290, 2000097759213757, 1999173145630685,
  2000592884849575, 2000224509271742, 1999319828579328, 2000659111106625, 2000037736085430,
  1999272954251339, 2000340263758423, 2000467888173596, 1998918324393764, 2000821809103892,
  2000200244479937, 1999613832998412, 1999480189687859, 2001744359816866, 1999298540971478,
  1999704460052215, 2000725921007138, 2000176469696237, 1999241853541333, 1999646577224300,
  2001594633164031, 1998992626420485, 1998572592895004, 2000752651783077, 2000954327770912,
  1999762749269920, 1997708860346842, 2000167806648630, 2002678463345286, 1999860360621330,
  1997113770836694, 1997374822016057, 2003260519896398, 2007427203304750, 1996582253970945,
  1983472788030839, 1994497252900805, 2027921925834146, 2036525272716036, 1971747038138216,
  1883484192966262, 1919275637084380, 2154359591383711, 2466427446075484, 2628676208870951,
  2523879820940399] [2255930756100100])
private def wc_rkmTraj_m128_r128_s0_hb : List ℕ := pCat [154720456000000, 217098331570095,
  263796445594065, 302188390625000, 335154036590585, 364182022706254, 390163481374081,
  413683434960339, 435151282500000, 454867312093780, 473059879636512, 489907684674692,
  505553862083247, 520115295030505, 533688995564378, 546356610250000, 558187684715263,
  569242081990880, 579571808924050, 589222419167318, 598234107244008, 606642573244320,
  614479714529129, 621774185108238, 628551852500000, 634836174238166, 640648510728444,
  646008387193150, 650933714527345, 655440976719520, 659545390855670, 663261044481866,
  666601014144697, 669577468187736, 672201756302453, 674484487875000, 676435600807232,
  678064422200040, 679379722053248, 680389760946999, 681102332515180, 681524801395013,
  681664137232731, 681526945239043, 681119493716350, 680447738919718, 679517347563350,
  678333717241881, 676901995000000, 675227094253446, 673313710238515, 671166334145001,
  668789266068507, 666186626901684, 663362369269815, 660320287603946, 657064027434145,
  653597093976232, 649922860077253, 646044573577931, 641965364144131, 637688249613943,
  633216141902197, 628551852500000] [623698097603142, 618657502899903, 613432608045844,
  608025870850554, 602439671198984, 596676314727900, 590738036276158, 584627003125768,
  578345318049290, 571895022177684, 565278097701568, 558496470417721, 551552012131684,
  544446542926415, 537181833306141, 529759606223827, 522181539000000, 514449265140058,
  506564376056673, 498528422703340, 490342917124715, 482009333928941, 473529111686777,
  464903654262002, 456134332077248, 447222483319095, 438169415086032, 428976404482599,
  419644699662818, 410175520825803, 400570061166251, 390829487782321, 380954942543262,
  370947542918981, 360808382773611, 350538533125000, 340139042871929, 329610939490750,
  318955229703016, 308172900115614, 297264917834778, 286232231055309, 275075769626234,
  263796445594065, 252395153724751, 240872772005366, 229230162126490, 217468169946209,
  205587625936599, 193589345613511, 181474129950426, 169242765777109, 156896026163766,
  144434670791331, 131859446308528, 119171086676276, 106370313500000, 93457836350366,
  80434353072952, 67300550087313, 54057102675900, 40704675263256, 27243921685893, 13675485453234]
private def wc_rkmTraj_m128_r128_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTraj_m128_r128_s0_v1 : List ℕ := pCat [2044407142139197, 2113592843646500,
  2203817354700455, 2296186916256562, 2369720934536528, 2409404187057602, 2410427789312531,
  2377760057337798, 2322506439467504, 2257391326802445, 2193219067682370, 2137106606472032,
  2092340030729278, 2059227911460659, 2036284744134521, 2021284373964693, 2011980383876962,
  2006482903255755, 2003378122483223, 2001697556817383, 2000823726077969, 2000386418499781,
  2000175430604986, 2000077150080880, 2000032894496365, 2000013608300494, 2000005466205169,
  2000002133290081, 2000000809379526, 2000000298694644, 2000000107273025, 2000000037509265,
  2000000012774751, 2000000004239338, 2000000001371283, 2000000000432491, 2000000000133036,
  2000000000039919, 2000000000011686, 2000000000003336, 2000000000000927, 2000000000000249,
  2000000000000062, 2000000000000014, 2000000000000002, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000] (pCat [2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m128_r128_s0_v2 : List ℕ := pCat [2000001950586258, 2000011166223949,
  2000044801329041, 2000145466251789, 2000405387396637, 2001001388021238, 2002237668646907,
  2004587117404698, 2008715329359595, 2015467445667076, 2025799573180612, 2040646038489442,
  2060730589210550, 2086350080237862, 2117176715215742, 2152132502785867, 2189382370448299,
  2226470014988935, 2260588015123204, 2288939965834234, 2309127461011475, 2319486284963123,
  2319306758648354, 2308899577968198, 2289502900586508, 2263059332723676, 2231914615073282,
  2198498629035234, 2165043747300094, 2133379238618209, 2104819179224797, 2080140966277523,
  2059636395448668, 2043209378972732, 2030493528880936, 2020967227093972, 2014050991402137,
  2009179601184294, 2005847896970276, 2003633569416130, 2002202495664997, 2001302645514974,
  2000751866877802, 2000423570521214, 2000232937877825, 2000125065344682, 2000065563605916,
  2000033562788788, 2000016778654155, 2000008191980827, 2000003906401023, 2000001819444747,
  2000000827728571, 2000000367817068, 2000000159651698, 2000000067687884, 2000000028030914,
  2000000011338115, 2000000004479248, 2000000001728258, 2000000000651215, 2000000000239615,
  2000000000086084, 2000000000030191] (pCat [2000000000010332, 2000000000003447, 2000000000001118,
  2000000000000352, 2000000000000104, 2000000000000027, 2000000000000006, 2000000000000001,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m2_r64_s6_hb : List ℕ := [189619999864656, 264910610231621,
  320460169528880, 365425874744613, 403398983029305, 436242808586848, 465076633037484,
  490637603767718, 513443081562802, 533873536504144, 552218962202278, 568706730023737,
  583519236800006, 596805584843586, 608689594940983, 619275471372038, 628651910457644,
  636895146226601, 644071251336805, 650237904245313, 655445766104234, 659739567116504,
  663158973039861, 665739282810639, 667511994604983, 668505268024722, 668744303185977,
  668251652450503, 667047476807177, 665149756100313, 662574460147617, 659335686107047,
  655445766104234, 650915348021290, 645753451397677, 639967499543217, 633563328159908,
  626545169963845, 618915613941124, 610675536905622, 601824003883365, 592358132438856,
  582272914263003, 571560984991518, 560212330074506, 548213910215763, 535549183908210,
  522197496087651, 508133289621011, 493325078166467, 477734091479226, 461312461702790,
  444000751453190, 425724513186914, 406389379652852, 385873848104281, 364018291377496,
  340607481384384, 315341252398568, 287781727678930, 257249232069521, 222588630366398,
  181529542363187, 128171976685947]
private def wc_rkmTraj_m2_r64_s6_v0 : List ℕ := pCat [1999690394568928, 1999701608347069,
  1999675644947309, 1999542036726479, 2000495362923044, 2000333892703477, 2001550832268272,
  2000451719116800, 2001178160657124, 2001727433221958, 2001381624600433, 2002146203574160,
  2002247732561449, 2003493000439223, 2004907463896171, 2004970414426647, 2004048876316735,
  2001966343517357, 2001370310776547, 2002636866678414, 2006270902117089, 2007489119707898,
  2004917465518319, 2013010935649351, 2004465833058732, 2015463703371024, 2012016340957530,
  2014183541940636, 2017090172178961, 2013007278949588, 2019301505465854, 2013185852835944,
  2020001098721684, 2016133375429693, 2019203744916605, 2023615914254459, 2012981916561315,
  2033348399040099, 2003805382155201, 2036107922065638, 2028694299401656, 2026068710328719,
  2068746597535528, 2047460777465579, 2024502358562554, 2076668306700326, 2040919530832333,
  2094038282085453, 2276040576386690, 2427803406573086, 2494509125663203, 2467434159888168,
  2375944455754481, 2262627886174687, 2161194316819232, 2087457096889781, 2042041561187226,
  2017890722659606, 2006713126848009, 2002204642611300, 1999373862831541, 2000150921363412,
  2000029931141056, 2000004609833882] [1999999522031410]
private def wc_rkmTraj_m2_r64_s6_v1 : List ℕ := pCat [2000290714152151, 2000723345365635,
  2000295196601470, 2000168154502388, 1998151299558380, 2002788651208356, 1996346979338961,
  2003792269864754, 1997804342370790, 1998340569970410, 2004577477336369, 1994746374810470,
  2002906172827713, 2000716421813827, 1996480208672840, 2004346145590044, 1992495048270672,
  2009532863393767, 1988350722665337, 2009412210185929, 1995342604111579, 1999736785847081,
  2005726796251531, 1991611281325748, 2006142894742941, 2003673018279572, 1989410007883182,
  2020148961102909, 1982063973681036, 2005747578375615, 2010598440590421, 1981661749770744,
  2025398076596355, 1997075733089831, 1992692774601787, 2022837175805067, 1987690757936083,
  2000382636399413, 2019375935631568, 1987771548713726, 2004524355548882, 2020495356322605,
  1992025856782838, 2006283445998744, 2028442329146340, 2002833939295605, 2004858804145342,
  2035980404726981, 2013734081199553, 1991171745038944, 2036839284798463, 2062073244831144,
  1993449911294620, 1956161584808112, 2049328686828051, 2137746727717821, 2057002028526375,
  1896479260077205, 1911078868236023, 2177872509357600, 2490611817401444, 2605565198670057,
  2480531710959925, 2256479481389959] [2083360266845975]
private def wc_rkmTrajPack_m32_r128_s2_hb : List ℕ := pCat [168481417846016, 236407231859077,
  287258713718033, 329065269230500, 364962906272699, 396572664829656, 424864935336299,
  450476772518871, 473853987691920, 495323576821453, 515134205959329, 533480468333489,
  550518229349807, 566374767859645, 581155724240513, 594950006768744, 607833346516329,
  619870930780100, 631119391938091, 641628335221358, 651441530086468, 660597851818370,
  669132034754880, 677075281416487, 684455759999440, 691299014369416, 697628304743794,
  703464892933873, 708828282844131, 713736424562259, 718205888594124, 722252015443480,
  725889044695491, 729130226955997, 731987921367162, 734473680922476, 736598327408783,
  738372017486831, 739804301167284, 740904173732931, 741680121989727, 742140165591655,
  742291894070890, 742142500110898, 741698809521937, 740967308313193, 739954167200989,
  738665263846370, 737106203076320, 735282335309728, 733198773380985, 730860407929917,
  728271921506090, 725437801517665, 722362352139596, 719049705282680, 715503830713363,
  711728545404180, 707727522185906, 703504297764832, 699062280161824, 694404755623919,
  689534895053994, 684455759999440] [679170308236684, 673681398984834, 667991797778461,
  662104181026716, 656021140283431, 649745186250565, 643278752535336, 636624199179562,
  629783815978086, 622759825601697, 615554386538642, 608169595867615, 600607491874049,
  592870056520543, 584959217781396, 576876851850395, 568624785230304, 560204796711806,
  551618619249097, 542867941738724, 533954410707810, 524879631917332, 515645171885692,
  506252559337442, 496703286581706, 486998810824454, 477140555418568, 467129911055293,
  456968236900473, 446656861678713, 436197084708407, 425590176890363, 414837381652601,
  403939915853699, 392898970646946, 381715712307380, 370391283023684, 358926801656783,
  347323364466855, 335582045810396, 323703898808848, 311689955990221, 299541229905062,
  287258713718033, 274843381776287, 262296190155775, 249618077186530, 236809963957937,
  223872754804927, 210807337775987, 197614585083823, 184295353539474, 170850484970629,
  157280806624859, 143587131558424, 129770259011319, 115830974769136, 101770051512326,
  87588249153415, 73286315162665, 58864984882693, 44324981832494, 29667018001324, 14891794132855]
private def wc_rkmTrajPack_m32_r128_s2_v0 : List ℕ := pCat [2000000000001365, 1999999999988543,
  2000000000052391, 1999999999708126, 2000000000501569, 1999999995444935, 2000000004530582,
  1999999934285340, 2000000191764262, 2000000895429287, 2000002948061182, 2000009926627337,
  2000029734435682, 2000083803048050, 1999780438811308, 1999462158360484, 1998764773859318,
  1997336111322238, 1994594056994863, 1989660244462241, 1981334801378797, 1968158747893174,
  1948612424087183, 1921467545725064, 1886256444731359, 1843754973005266, 1796315804772479,
  1747878181901001, 1703544823573758, 1668745724990119, 1648161778164717, 1644697812553374,
  1658814460889646, 1688429333345548, 1729415785027892, 1776536257847571, 1824522514895941,
  1869000943312977, 1907051851288218, 1937338305879546, 1959877863495380, 1975611464563762,
  1985933970120423, 1992307511623279, 1996013869455611, 1998044529108143, 1999092747813148,
  1999602380239779, 1999835611779530, 1999935991680548, 1999976571091063, 2000008044042250,
  2000002584090977, 2000000774416620, 2000000215760752, 1999999944343861, 1999999986773839,
  1999999997122179, 1999999999431126, 1999999999898879, 1999999999984064, 1999999999997821,
  1999999999999751, 1999999999999979] [1999999999999999]
private def wc_rkmTrajPack_m32_r128_s2_v1 : List ℕ := pCat [1999963687575126, 2000031229364920,
  2000012370490435, 1999970891418293, 1999991551541942, 2000026552923245, 2000011195260668,
  1999976984278070, 1999982704990975, 2000016309815907, 2000023750249333, 1999995298964164,
  1999973948083680, 1999989184450225, 2000018962719173, 2000024215625936, 1999999173040742,
  1999975120220191, 1999979040562332, 2000007018915785, 2000026481933573, 2000022201511108,
  1999992216770199, 1999974664762869, 1999971051661089, 1999999704590326, 2000021526486894,
  2000033586022301, 2000022694214497, 1999993162816979, 1999973101579492, 1999960426196423,
  1999967123145241, 1999992356498671, 2000015313822411, 2000038175052815, 2000055284112918,
  2000055954158269, 2000051854588247, 2000045861090425, 2000033185045189, 2000028462768196,
  2000043940988592, 2000075767199636, 2000105469969086, 2000035273496642, 1999571539186083,
  1998106571078150, 1994593041330228, 1987465861515449, 1974747020250576, 1954402461990505,
  1924907642776869, 1885915444322693, 1838843081959949, 1787120071271382, 1735894564387473,
  1691192461089793, 1658732797027897, 1642723262764057, 1644975616043662, 1664593874280999,
  1698307665796782, 1741310961789771] (pCat [1788320781691549, 1834550436222350, 1876379816204644,
  1911638633622342, 1939539407709766, 1960373752797650, 1975110069683278, 1985011030758871,
  1991343727395278, 1995205817800812, 1997454119450842, 1998704245728024, 1999368301791891,
  1999705231418865, 1999868452136991, 1999943901653467, 1999977158949779, 1999991127760990,
  1999996714703187, 1999998841124949, 1999999610831812, 1999999875659410, 1999999962224239,
  1999999989093189, 1999999997008882, 1999999999221257, 1999999999807618, 1999999999954925,
  1999999999989992, 1999999999997896, 1999999999999584, 1999999999999924, 1999999999999988,
  1999999999999999, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTrajPack_m32_r128_s2_v2 : List ℕ := pCat [1999999824534689, 2000000378099223,
  1999998240251922, 2000000559649098, 1999993618145213, 1999995019182826, 1999985696168337,
  1999979218197482, 1999975664245428, 1999968870351377, 1999974109413620, 1999986211828110,
  1999998457975847, 2000015863960821, 2000025095263017, 2000018159498554, 2000005821132159,
  1999990158219001, 1999976729312398, 1999980870582877, 1999997910207472, 2000012504014027,
  2000020851755029, 2000017056064925, 1999997959648907, 1999980746353235, 1999980132759565,
  1999991194294497, 2000007387631968, 2000021685957688, 2000019621713126, 2000000454448742,
  1999983056406017, 1999979163778927, 1999987237423812, 2000004855309360, 2000022177749378,
  2000022339331348, 2000004707299252, 1999986178518307, 1999977740561320, 1999981109998611,
  1999997368879670, 2000018634740663, 2000027096513117, 2000016323070901, 1999997474356356,
  1999981414594619, 1999972981508964, 1999978491744730, 1999998836917861, 2000020644836051,
  2000029659477676, 2000025186872036, 2000012219294986, 1999992413978545, 1999971574438643,
  1999962347838649, 1999970562307974, 1999988267297043, 2000004160925615, 2000012699449897,
  2000015837240728, 2000029549243334] (pCat [2000081856510459, 2000170645918497, 2000201771044166,
  2000001137742407, 1999480408547760, 1998904275471280, 1999037408876836, 2000874676549721,
  2004803528676734, 2009433618889710, 2010766803961761, 2002514700687221, 1977946057755951,
  1932790928560696, 1867949176333423, 1790590999096071, 1712876870874286, 1648637532723399,
  1609321389693230, 1600818004804053, 1622287626791247, 1667185336432129, 1725781963095516,
  1788055537053459, 1845952382088609, 1894503847222178, 1931825079572276, 1958377764608319,
  1975972020505934, 1986875955515951, 1993215051070060, 1996679246129899, 1998461341205361,
  1999325166717713, 1999719929929154, 1999890059043451, 1999959203410930, 1999985699439683,
  1999995268644816, 1999998523939058, 1999999566254765, 1999999880093877, 1999999968859692,
  1999999992414133, 1999999998269656, 1999999999631148, 1999999999926686, 1999999999986452,
  1999999999997682, 1999999999999638, 1999999999999950, 1999999999999996, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTrajPack_m32_r128_s3_hb : List ℕ := pCat [151235973710059, 212566784324122,
  258731019595326, 296897986170467, 329862767239432, 359067709347972, 385374784577226,
  409348928940480, 431384827440600, 451771493225160, 470728340127034, 488426780601530,
  505003879054596, 520571368874843, 535221826016207, 549033025468511, 562071095560349,
  574392853029413, 586047565334855, 597078303469965, 607522996165150, 617415262492653,
  626785077424452, 635659309676202, 644062160653966, 652015525923956, 659539295338931,
  666651604120420, 673369044377294, 679706844443390, 685679021837742, 691298514449682,
  696577293628170, 701526462139258, 706156339396170, 710476535925647, 714496018684065,
  718223168556993, 721665831150500, 724831361800039, 727726665574065, 730358232927732,
  732732171561649, 734854234957633, 736729847994302, 738364129987569, 739761915452652,
  740927772843327, 741866021489539, 742580746925103, 743075814772075, 743354883326914,
  743421414975002, 743278686544158, 742929798693878, 742377684424995, 741625116783889,
  740674715826086, 739528954895927, 738190166271655, 736660546218827, 734942159489055,
  733036943295800, 730946710794088] [728673154086526, 726217846773826, 723582246064085,
  720767694451299, 717775420969908, 714606542028577, 711262061822792, 707742872322192,
  704049752824788, 700183369066260, 696144271868336, 691932895305774, 687549554366531,
  682994442074372, 678267626037144, 673369044377294, 668298500993602, 663055660094544,
  657640039933831, 652051005667351, 646287761237627, 640349340176613, 634234595199816,
  627942186443727, 621470568173761, 614817973760506, 607982398687027, 600961581308007,
  593752981030978, 586353753528808, 578760722518296, 570970347548924, 562978687134131,
  554781356419379, 546373478409356, 537749627561322, 528903764279821, 519829158502523,
  510518300124299, 500962793434486, 491153231996201, 481079049413842, 470728340127034,
  460087642608477, 449141674943416, 437873009453470, 426261668380871, 414284616030119,
  401915113167209, 389121885286649, 375868034912433, 362109594889634, 347793566753141,
  332855201400513, 317214131343294, 300768700977375, 283387350687745, 264894938777086,
  245049815357087, 223502633361509, 199715197889167, 172778464488239, 140914605445198,
  99521511834011]
private def wc_rkmTrajPack_m32_r128_s3_v0 : List ℕ := pCat [2000000175465311, 1999999621900777,
  2000001759748078, 1999999440350902, 1999993618145213, 2000004980817174, 1999985696168337,
  1999979218197482, 1999975664245428, 1999968870351377, 1999974109413620, 1999986211828110,
  1999998457975847, 1999984136039179, 2000025095263017, 2000018159498554, 2000005821132159,
  2000009841780999, 2000023270687602, 1999980870582877, 1999997910207472, 2000012504014027,
  2000020851755029, 1999982943935075, 2000002040351093, 2000019253646765, 2000019867240435,
  1999991194294497, 1999992612368032, 2000021685957688, 2000019621713126, 1999999545551258,
  2000016943593983, 2000020836221073, 2000012762576188, 1999995144690640, 1999977822250622,
  1999977660668652, 2000004707299252, 2000013821481693, 1999977740561320, 1999981109998611,
  1999997368879670, 1999981365259337, 1999972903486883, 1999983676929099, 1999997474356356,
  1999981414594619, 2000027018491036, 1999978491744730, 2000001163082139, 1999979355163949,
  2000029659477676, 1999974813127964, 2000012219294986, 2000007586021455, 1999971574438643,
  2000037652161351, 2000029437692026, 2000011732702957, 1999995839074385, 1999987300550103,
  2000015837240728, 2000029549243334] (pCat [2000081856510459, 2000170645918497, 2000201771044166,
  2000001137742407, 2000519591452240, 2001095724528720, 2000962591123164, 1999125323450279,
  2004803528676734, 2009433618889710, 2010766803961761, 1997485299312779, 1977946057755951,
  1932790928560696, 1867949176333423, 1790590999096071, 1712876870874286, 1648637532723399,
  1609321389693230, 1600818004804053, 1622287626791247, 1667185336432129, 1725781963095516,
  1788055537053459, 1845952382088609, 1894503847222178, 1931825079572276, 1958377764608319,
  1975972020505934, 1986875955515951, 1993215051070060, 1996679246129899, 2001538658794639,
  1999325166717713, 1999719929929154, 1999890059043451, 1999959203410930, 1999985699439683,
  1999995268644816, 1999998523939058, 1999999566254765, 1999999880093877, 1999999968859692,
  1999999992414133, 2000000001730344, 2000000000368852, 1999999999926686, 1999999999986452,
  1999999999997682, 2000000000000362, 1999999999999950, 1999999999999996, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTrajPack_m32_r128_s3_v1 : List ℕ := pCat [1999995380541803, 1999995433903336,
  2000013192555517, 1999992986048032, 2000007553142989, 1999990137343160, 2000001452625648,
  1999991912399246, 2000017551937323, 1999998810947144, 1999991157112520, 1999997005106505,
  2000009440949673, 2000003598864533, 1999989472475481, 1999990366689456, 2000016312227187,
  2000011902505781, 1999992897013222, 1999989574000041, 1999991105747452, 1999999968775183,
  1999988848714033, 1999966141103595, 1999970657270622, 1999981450661498, 2000007565540144,
  1999953517039827, 1999980035988995, 1999973764562348, 2000037597552744, 1999988496824310,
  2000018101834877, 2000001333746039, 1999999997153834, 2000024297987769, 2000008700718515,
  2000011708567253, 1999971545032642, 2000013072789887, 2000033221380275, 1999968975258605,
  2000021940197939, 1999982153405400, 2000049360783634, 1999940587675164, 2000146059417212,
  1999756291487717, 2000336251637943, 1999526678655635, 2000689591240107, 1999146873640371,
  2001064090020856, 1998868997558506, 2001137497836568, 1999015964421792, 2000740772905111,
  1999509508053804, 2000244782382649, 2000003136913016, 1999655809595117, 2000726919366296,
  1999202417556514, 2000068475904531] (pCat [2000927213848793, 1998838770148896, 1999943663667842,
  2001363561609411, 1999059976745345, 1999027908473699, 2001474185211473, 2000438102031694,
  1998426290326225, 1999740477923126, 2001649578317914, 1999986175851074, 1999018779969329,
  1999049793846223, 2001619664124778, 2000027270724457, 2000592199283343, 1998648481600857,
  1999379500742480, 1999830226269533, 2000281184840168, 2003242233562199, 2002443190360270,
  1998543203253744, 1993518464393677, 1989935200109240, 1996934850178398, 2016101421368768,
  2037137777083141, 2046307780173087, 2027706325869840, 1969536305922051, 1876185291579225,
  1767372800359083, 1667187120588277, 1596680108067205, 1569539286666106, 1587536639090664,
  1640196992537306, 1710913924874751, 1784372816110024, 1850255680573360, 1903301349559676,
  1942108530498282, 1967942267009337, 1983582697207622, 1992206122771898, 1996554238251840,
  1998572761500469, 1999442749982089, 1999793921851365, 1999927659373719, 1999975922858048,
  1999992434218105, 1999997770066052, 1999999388354040, 1999999845208620, 1999999964186510,
  1999999992500896, 1999999998595628, 1999999999768306, 1999999999967027, 1999999999996085,
  1999999999999637] [1999999999999979])
private def wc_rkmTrajPack_m32_r128_s3_v2 : List ℕ := pCat [2000021518986070, 1999998380575608,
  2000000605609872, 1999999188022822, 1999995263766215, 1999990389705880, 1999997392669125,
  2000003314156118, 2000000425969441, 1999992099456763, 2000010269858566, 1999982896601636,
  2000027358962398, 1999989302984353, 2000024149304493, 1999974920163410, 1999991648635356,
  2000002088604158, 1999997592335906, 2000022597392103, 1999990216837384, 1999989775973608,
  2000016159613997, 1999953811145367, 2000079503687451, 1999913419264092, 2000150747016315,
  1999747530626364, 2000329586016410, 1999527187446785, 2000683448232361, 1999140229003310,
  2000987584801282, 1998920521361158, 2001096477317202, 1999008350217553, 2000812920732622,
  1999492322785055, 2000125330008921, 2000147160363920, 1999641531101867, 2000445506677000,
  1999560960695009, 2000240296312536, 1999925129224249, 1999762981668345, 2000417267041403,
  1999529195745682, 2000178224651743, 2000227058281122, 1999446426346411, 2000485865984521,
  2000094361552099, 1999253148321876, 2000886701411873, 1999734461913895, 1999566432809579,
  2000394394134831, 2000600985980216, 1998427590394170, 2001353268096904, 1999895329527991,
  1999383900240847, 1999985833167005] (pCat [2000991460496010, 1999428594587261, 1998983101420446,
  2001640042224462, 1999659332844721, 1998941449293006, 2000704240106606, 2000549185857529,
  1999730618473629, 1999052625715207, 2000644012626675, 2001056468050451, 1998768004379139,
  1999570864797576, 2001061687014142, 2000023690920604, 1999608238226042, 1999680283890521,
  1999958387124967, 2000744444246012, 1999971004750943, 1999207280009892, 2000126247326076,
  2000204764631158, 1999874428093013, 2000710068659042, 2000239887721325, 1998441388841330,
  1998886472879388, 2001395916420623, 2002781680051501, 2001214415300173, 1996721671772837,
  1993374526196699, 1997989252674282, 2009606027795339, 2015333048862086, 2003630078396897,
  1979581105790261, 1964263023367257, 1979155649197180, 2027142237039651, 2082847458195169,
  2102621891265759, 2051683659829549, 1929024463875713, 1770316936410611, 1627836963098862,
  1543766511152363, 1533840002619471, 1587048218968698, 1676631188363119, 1773881063365144,
  1858065853372053, 1919837277688617, 1959242850751338, 1981364000717697, 1992355390541414,
  1997198653497913, 1999089160398112, 1999740019897053, 1999935969271526, 1999986785865663,
  1999997840195720] [1999999757369757])
private def wc_rkmTrajPack_m32_r128_s4_hb : List ℕ := pCat [151503484973546, 212942779582757,
  259188671701881, 297423149287806, 330446239567324, 359702840357141, 386056448423528,
  410072999057541, 432147875394119, 452570601796986, 471560980205565, 489290726275264,
  505897146856150, 521492172974600, 536168544336003, 550004173501193, 563065305768770,
  575408858375777, 587084185927301, 598134435602048, 608597603220038, 618507367320056,
  627893755894815, 636783685186258, 645201399408703, 653168832857977, 660705910568677,
  667830799840520, 674560122131056, 680909132710510, 686891873892572, 692521306451549,
  697809422911725, 702767345678093, 707405412417207, 711733250655225, 715759843209579,
  719493585790229, 722942337880816, 726113467827154, 729013892911618, 731650115069897,
  734028252806102, 736154069779005, 738033000462931, 739670173229009, 741070431143912,
  742238350742247, 743178258994138, 743894248660028, 744390192199615, 744669754380275,
  744736403711774, 744593422818094, 744243917843281, 743690826976159, 742936928168163,
  741984846109266, 740837058518739, 739495901800239, 737963576104151, 736242149834288,
  734333563630720, 732239633855642] [729962055604710, 727502405262072, 724862142613385,
  722042612527293, 719045046212192, 715870562051490, 712520166016927, 708994751655888,
  705295099644832, 701421876897014, 697375635208476, 693156809421780, 688765715082045,
  684202545554463, 679467368566468, 674560122131056, 669480609800137, 664228495188226,
  658803295696906, 653204375359132, 647430936709334, 641482011569943, 635356450627113,
  629052911647338, 622569846161887, 615905484416474, 609057818348507, 602024582312194,
  594803231221184, 587390915717202, 579784453898732, 571980299052786, 563974502720973,
  555762672292674, 547339922145986, 538700817141286, 529839307000079, 520748649755676,
  511421322018821, 501848913228238, 492022000308620, 481929998174173, 471560980205565,
  460901461064296, 449936131804448, 438647533920978, 427015654318789, 415017416556071,
  402626034101563, 389810177130382, 376532882901025, 362750106487989, 348408755680699,
  333443966846330, 317775230339717, 301300710744907, 283888615739829, 265363493830658,
  245483267690651, 223897972316763, 200068460830610, 173084080832055, 141163859926269,
  99697548822577]
private def wc_rkmTrajPack_m32_r128_s4_v0 : List ℕ := pCat [1999978481013930, 1999998380575608,
  2000000605609872, 1999999188022822, 2000004736233785, 2000009610294120, 2000002607330875,
  2000003314156118, 2000000425969441, 2000007900543237, 1999989730141434, 1999982896601636,
  1999972641037602, 1999989302984353, 1999975850695507, 1999974920163410, 2000008351364644,
  1999997911395842, 1999997592335906, 1999977402607897, 1999990216837384, 1999989775973608,
  2000016159613997, 1999953811145367, 1999920496312549, 1999913419264092, 1999849252983685,
  1999747530626364, 1999670413983590, 1999527187446785, 1999316551767639, 2000859770996690,
  2000987584801282, 2001079478638842, 1998903522682798, 1999008350217553, 1999187079267378,
  1999492322785055, 1999874669991079, 2000147160363920, 2000358468898133, 2000445506677000,
  2000439039304991, 2000240296312536, 1999925129224249, 2000237018331655, 1999582732958597,
  1999529195745682, 1999821775348257, 1999772941718878, 2000553573653589, 2000485865984521,
  1999905638447901, 1999253148321876, 1999113298588127, 1999734461913895, 1999566432809579,
  2000394394134831, 2000600985980216, 2001572409605830, 2001353268096904, 1999895329527991,
  1999383900240847, 1999985833167005] (pCat [1999008539503990, 2000571405412739, 1998983101420446,
  2001640042224462, 1999659332844721, 2001058550706994, 1999295759893394, 1999450814142471,
  1999730618473629, 2000947374284793, 2000644012626675, 2001056468050451, 2001231995620861,
  2000429135202424, 2001061687014142, 2000023690920604, 2000391761773958, 2000319716109479,
  2000041612875033, 1999255555753988, 1999971004750943, 1999207280009892, 1999873752673924,
  2000204764631158, 1999874428093013, 1999289931340958, 1999760112278675, 1998441388841330,
  1998886472879388, 1998604083579377, 1997218319948499, 1998785584699827, 1996721671772837,
  1993374526196699, 1997989252674282, 1990393972204661, 1984666951137914, 1996369921603103,
  1979581105790261, 1964263023367257, 1979155649197180, 1972857762960349, 1917152541804831,
  1897378108734241, 1948316340170451, 1929024463875713, 1770316936410611, 1627836963098862,
  1543766511152363, 1533840002619471, 1587048218968698, 1676631188363119, 1773881063365144,
  1858065853372053, 1919837277688617, 1959242850751338, 1981364000717697, 1992355390541414,
  1997198653497913, 1999089160398112, 1999740019897053, 2000064030728474, 2000013214134337,
  2000002159804280] [1999999757369757])
private def wc_rkmTrajPack_m32_r128_s4_v1 : List ℕ := pCat [1999994996513208, 2000002877063354,
  1999988744338095, 1999991862557139, 1999994048882810, 1999979270208656, 2000006061392956,
  1999985559123657, 1999998779838283, 1999999841800076, 1999985280205718, 2000031308408630,
  1999903505760653, 2000166089050197, 1999757659023490, 2000355637567167, 1999579625124823,
  2000376473170263, 1999792041119836, 2000003941421725, 2000149439692301, 1999872809286634,
  2000050551266068, 2000009548584487, 1999932792397258, 2000176906818963, 1999806620271979,
  1999982945674860, 2000089369091660, 2000009420510659, 1999860245883563, 1999784407525021,
  2000490294355785, 2000004314476105, 1999424306726334, 2000127072218370, 2000080360010290,
  2000539384346147, 1999774031740611, 1999581117923699, 1999470293386703, 2000488761677021,
  2000661804170648, 2000517041264193, 1999083919335778, 1999945347187031, 1997951959520791,
  2000708020367941, 1999123339359178, 2001329983968162, 2000221821612413, 2000718618016500,
  2000088371312426, 1999630986727591, 1999267956817339, 1999229686664777, 1999809110141738,
  1999745630823990, 1999535482352392, 1999446033961962, 2001275810990897, 2000332253362571,
  2000458046848758, 2000010338022011] (pCat [1999814775506561, 1999684249938306, 1999851743562322,
  1999298915547867, 2000736492742709, 2000674766768027, 2000353178840320, 1999527274386021,
  1999017384731989, 1999011183668913, 1999771874981245, 1999400787337768, 2000681704209098,
  2001625221176887, 2000663101139394, 2000645722677676, 1999810284845941, 1998781471994368,
  2000827967945216, 1999489946526782, 2000411721344013, 2001963567713247, 1996860354937031,
  2003027866226360, 1997458697543230, 1999211953557946, 2004359295878810, 1996288076141015,
  2001809031560291, 2004688380697244, 1994841518477745, 2003955062861033, 2004067673221000,
  1994703156838406, 1997253805693929, 2014749045367079, 1982730785578124, 1999868587493713,
  2022887268135706, 1977117100136336, 1992308724161960, 2030889337002698, 1985954297428709,
  1970496967447991, 2025770701533701, 2020521094324068, 1960482975424042, 1971335296109812,
  2033561909747278, 2025044853768254, 1945462486058242, 1912618034195552, 1975625605412840,
  2042946308685565, 1995004408309823, 1815786798536023, 1602369119177987, 1474465336808206,
  1484128838828553, 1599334162013136, 1748106437571041, 1871496336205901, 1947735907376696,
  1983933789455527] [1996779136921281])
private def wc_rkmTrajPack_m32_r128_s4_v2 : List ℕ := pCat [1999995802189059, 2000047675745436,
  1999825859805913, 2000306304362371, 1999592470312800, 2000382870437952, 1999816948242401,
  1999909855061530, 2000225555662055, 1999882835088844, 1999875241390467, 2000247988339936,
  1999862178976795, 1999901672337687, 2000171248490539, 1999899319493349, 1999985058351944,
  2000084411950903, 1999771334124913, 2000320225454518, 1999666678544446, 2000263204228573,
  1999829691654472, 2000100358816709, 1999747225450234, 2000628932028927, 1999038063982657,
  2000919915371958, 1999133418819207, 2001120306254505, 1998902820377080, 2000405571006488,
  2000201170159732, 1999808192082524, 2000158345322915, 1999698905424697, 2000111614936277,
  2000121401516471, 2000256423888840, 1999538741025334, 2000090954357456, 1999769510140358,
  2000721708743230, 1999801703169438, 1999819336492487, 1999636330452771, 2000000869072149,
  2000417094746448, 2000471105726938, 1999340216325196, 2000016761202573, 1999531549150034,
  1999957135186283, 2000828663661444, 2000419903657200, 1999433450898553, 1999657417818882,
  1999563787985623, 2000022645361448, 2000266471343411, 2000271504438550, 2000989565902483,
  2000326957722503, 1998886742356881] (pCat [1999297207835192, 1999174334032776, 1999547751729031,
  2001347935175857, 1997939408173000, 2002848266774951, 1998806524356237, 2000852848338070,
  2000531518832045, 1997628301841420, 2002266045003720, 1997084868292623, 1999075437412698,
  2002609877342697, 1996090565819573, 2005236234178329, 1997426547564503, 2000406310314348,
  2000315309830322, 2000118121676704, 1995925093104705, 2007249222009053, 1995628889501149,
  1999456053582247, 2008702981423607, 1985075712900939, 2008002848270799, 2002791375185085,
  1985418975365280, 2018620132321571, 1994251218740332, 1987708246785983, 2021902721105410,
  1987496676649223, 1991489355946086, 2024126398544302, 1983867214548551, 1990854862595519,
  2026083085650575, 1984462042043882, 1985553421879130, 2029161824651210, 1992738524103339,
  1976529852826939, 2028207137332302, 2009285809245405, 1964272860218341, 2011137104326627,
  2035311425975753, 1970918361199069, 1970591937687607, 2044630865917111, 2022007632539005,
  1938265065420521, 1979851186332843, 2079247592271235, 2021419792861484, 1883061566323808,
  1933901418273569, 2131403322194689, 2115149549513478, 1758286528309421, 1393372353106872,
  1376480995756589] [1665290108037882])
private def wc_rkmTrajPack_m32_r128_s1_hb : List ℕ := [205680879328010, 287465732329927,
  347888997038760, 396870545572762, 438298938104878, 474190812537190, 505756974670436,
  533794451240661, 558862333468073, 581371548187641, 601635112693387, 619898288392514,
  636357681853034, 651173884275084, 664480140944549, 676388479003634, 686994150522045,
  696378925233796, 704613577314390, 711759794566708, 717871665285290, 722996850713337,
  727177519564203, 730451099736336, 732850887570557, 734406544573548, 735144504051182,
  735088304639430, 734258863676578, 732674700312916, 730352115915875, 727305337497441,
  723546628420830, 719086369426905, 713933111974532, 708093604946045, 701572794871085,
  694373798914518, 686497848900393, 677944203539649, 668710024715888, 658790212058841,
  648177187960326, 636860622468145, 624827083849383, 612059595634207, 598537074015626,
  584233609640595, 569117543594910, 553150266369622, 536284636865197, 518462869372709,
  499613658298633, 479648181994717, 458454408362691, 435888736445100, 411763283162207,
  385825688338332, 357725253030184, 326952092536390, 292717251095853, 253683851108411,
  207231699598033, 146570177514111]
private def wc_rkmTrajPack_m32_r128_s1_v0 : List ℕ := [1998453246609753, 1993630376340480,
  1981853430115560, 1958724028355489, 1920540235693449, 1866374124967299, 1799781477415035,
  1729107442515683, 1665870910130126, 1621629805830280, 1604529675901570, 1616941405502199,
  1655085104098521, 1710624178680978, 1773405801134014, 1834206616468848, 1886577197543447,
  1927434179089089, 1956593833355168, 1975742378154618, 1987349734639601, 1993854663214945,
  1997225716010410, 1998839762773502, 1999552342527546, 1999841506489735, 1999948872452241,
  1999985116566782, 1999996142382291, 1999999127233932, 2000000166980049, 2000000025483873,
  2000000002688046]
private def wc_rkmTrajPack_m32_r128_s1_v1 : List ℕ := pCat [2000000000001365, 1999999999988543,
  2000000000052391, 1999999999708126, 2000000000501569, 1999999995444935, 1999999995469418,
  1999999934285340, 1999999808235738, 1999999104570713, 1999997051938818, 1999990073372663,
  1999970265564318, 1999916196951950, 1999780438811308, 1999462158360484, 1998764773859318,
  1997336111322238, 1994594056994863, 1989660244462241, 1981334801378797, 1968158747893174,
  1948612424087183, 1921467545725064, 1886256444731359, 1843754973005266, 1796315804772479,
  1747878181901001, 1703544823573758, 1668745724990119, 1648161778164717, 1644697812553374,
  1658814460889646, 1688429333345548, 1729415785027892, 1776536257847571, 1824522514895941,
  1869000943312977, 1907051851288218, 1937338305879546, 1959877863495380, 1975611464563762,
  1985933970120423, 1992307511623279, 1996013869455611, 1998044529108143, 1999092747813148,
  1999602380239779, 1999835611779530, 1999935991680548, 1999976571091063, 1999991955957750,
  1999997415909023, 1999999225583380, 1999999784239248, 1999999944343861, 1999999986773839,
  1999999997122179, 1999999999431126, 1999999999898879, 1999999999984064, 1999999999997821,
  1999999999999751, 1999999999999979] [1999999999999999]
private def wc_rkmTrajPack_m64_r56_s1_hb : List ℕ := [239932174152285, 333634617553829,
  401659312834593, 455761186301623, 500572270669703, 538506820138848, 571021562231385,
  599080178132272, 623362074003334, 644369183801972, 662485881427564, 678015002454712,
  691200709272104, 702243652873317, 711311394635064, 718545789066319, 724068349411058,
  727984234112002, 730385265836813, 731352256441922, 730956823995365, 729262831396081,
  726327538518416, 722202534255306, 716934497116535, 710565820525654, 703135129965554,
  694677712546685, 685225874677662, 674809239803303, 663454995288863, 651188095217875,
  638031423943480, 624005923535622, 609130686662804, 593423014801268, 576898439821379,
  559570704762197, 541451696692516, 522551320555203, 502877297153713, 482434859917205,
  461226312022993, 439250384844265, 416501305148089, 392967422048224, 368629146250738,
  343455774866637, 317400432164993, 290391660847231, 262318681032679, 233003711562873,
  202145018033790, 169183629930204, 132923213321558, 89974565307107]
private def wc_rkmTrajPack_m64_r56_s1_v0 : List ℕ := [2184812123740707, 2349453988169994,
  2459182845557644, 2484016877661155, 2433970360317443, 2341714379028081, 2241098233058305,
  2154533968003340, 2090882288526738, 2049410876664635, 2024979750267367, 2011797455950587,
  2005224545785676, 2002176193426629, 2000854735326172, 2000317220320732, 2000111440486034,
  2000037111464167, 2000011729490513, 2000003521976929, 2000001005494411, 2000000273109271,
  2000000070610652, 2000000017383431, 2000000004075980, 2000000000910348, 2000000000193668,
  2000000000039239, 2000000000007569, 2000000000001388, 1999999999999760, 2000000000000039,
  2000000000000005, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000]
private def wc_rkmTrajPack_m64_r56_s1_v1 : List ℕ := [1999999999999866, 1999999999999842,
  1999999999999992, 2000000000000127, 2000000000000013, 1999999999999889, 2000000000000008,
  2000000000000097, 1999999999999955, 1999999999999929, 2000000000000076, 2000000000000000,
  1999999999999929, 2000000000000389, 2000000000000345, 1999999999995061, 1999999999988977,
  2000000000047767, 2000000000214279, 1999999999796614, 1999999997224419, 1999999996990041,
  2000000022536855, 2000000076216288, 1999999953741140, 1999999203992762, 1999998484284848,
  2000002846912012, 2000019911020656, 2000033637627029, 1999948213417352, 1999590064078055,
  1999019639705896, 1999441396321994, 2004585350241269, 2021533772482861, 2059303492298347,
  2124252704604154, 2213886445770994, 2313214935829869, 2397686187230480, 2442801837545493,
  2435396811949178, 2379645067415743, 2294179297017463, 2202677813126077, 2124037500540120,
  2067272370257248, 2032210096419164, 2013539404675925, 2004957862334617, 2001564710145307,
  2000419282467998, 2000093326567087, 2000016671980209, 2000002247022848, 2000000197107518]
private abbrev dP_0 : Prop := atF [ bNatListEq (bEvalLo12W 2 4096 64 [1,3,7,15,30,58,58,58]
  [18699679,22184902,22954891,24409365,28094556,15378415,17605775,6014002] [1,2,4,8,16,14,16,6]
  rkmMasks_m2_r64 [none, none, none, none, none, none, some (16, 65, wc_rkmTraj_m2_r64_s6_hb,
  wc_rkmTraj_m2_r64_s6_v0, wc_rkmTraj_m2_r64_s6_v1)]) rkmRow_m2_r64, bNatListEq (bEvalLo12W 1024 8
  14 [1,1] [20553616,3627109] [16,3] rkmMasks_m1024_r14 []) rkmRow_m1024_r14] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bSlideChk 20 129 wc_rkmTrajPack_m32_r128_s2_hb
  wc_rkmTrajPack_m32_r128_s2_v0 wc_rkmTrajPack_m32_r128_s2_v1, bNatListEq (bEvalLo12W 16 512 13
  [1,1,1,1] [191960317,25750043,30985127,22582771] [13,3,3,3] rkmMasks_m16_r13 []) rkmRow_m16_r13]
  = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bSlideChk 19 129 wc_rkmTrajPack_m32_r128_s2_hb
  wc_rkmTrajPack_m32_r128_s2_v1 wc_rkmTrajPack_m32_r128_s2_v2, bNatListEq (bEvalLo12W 256 32 18
  [1,1] [48224498,1003342] [21,2] rkmMasks_m256_r18 []) rkmRow_m256_r18] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bSlideChk 19 129 wc_rkmTraj_m128_r128_s1_hb
  wc_rkmTraj_m128_r128_s1_v0 wc_rkmTraj_m128_r128_s1_v1, bNatListEq (bEvalLo12W 4 2048 19
  [1,3,7,7,7] [60292114,61429099,79729952,26849916,16222793] [2,5,10,4,2] rkmMasksPack_m4_r19 [])
  rkmRowPack_m4_r19, bNatListEq (bEvalLo12W 64 128 7 [1,1,1] [93199702,2483081,1205182] [10,2,2]
  rkmMasks_m64_r7 []) rkmRow_m64_r7] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bSlideChk 19 129 wc_rkmTraj_m128_r128_s1_hb
  wc_rkmTraj_m128_r128_s1_v1 wc_rkmTraj_m128_r128_s1_v2, bNatListEq (bEvalLo12W 4 2048 17
  [1,2,4,8,8,8,8,8] [58421155,44373706,55604127,32069021,34891761,11178356,3236904,2742026]
  [2,2,5,4,5,2,1,1] rkmMasksPack_m4_r17 []) rkmRowPack_m4_r17, bNatListEq (bEvalLo12W 8 1024 52
  [1,1,1,1,1,1,1,1] [21021499,2403702,18861336,9185697,5321366,207753,740819,4296202]
  [2,1,2,1,1,1,1,1] rkmMasksPack_m8_r52 []) rkmRowPack_m8_r52] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bNatListEq (bEvalLo12W 16 512 48 [1,1,2,3,5,5,5,5]
  [22281663,27438406,22518257,26744883,20699296,26957388,7425181,2742036] [4,4,6,10,11,14,4,2]
  rkmMasksPack_m16_r48 []) rkmRowPack_m16_r48, bNatListEq (bEvalLo12W 8 1024 18 [1,3,3,3]
  [82769832,131710082,26891107,7119226] [5,15,4,2] rkmMasks_m8_r18 []) rkmRow_m8_r18, bNatListEq
  (bEvalLo12W 8 1024 112 [1,1,1,1,1,1,1,1]
  [13595015,21178233,6581905,4798156,11428497,256614,49852,10846585] [2,3,1,1,2,1,1,2]
  rkmMasksPack_m8_r112 []) rkmRowPack_m8_r112] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bNatListEq (bEvalLo12W 32 256 128 [1,2,4,7,7,7,7,7]
  [26925892,17043556,25667091,12950726,12526267,2424443,1439567,1359247] [13,15,39,29,28,6,4,4]
  rkmMasksPack_m32_r128 [none, some (15, 65, wc_rkmTrajPack_m32_r128_s1_hb,
  wc_rkmTrajPack_m32_r128_s1_v0, wc_rkmTrajPack_m32_r128_s1_v1), some (39, 129,
  wc_rkmTrajPack_m32_r128_s2_hb, wc_rkmTrajPack_m32_r128_s2_v0, wc_rkmTrajPack_m32_r128_s2_v2),
  some (29, 129, wc_rkmTrajPack_m32_r128_s3_hb, wc_rkmTrajPack_m32_r128_s3_v0,
  wc_rkmTrajPack_m32_r128_s3_v2), some (28, 129, wc_rkmTrajPack_m32_r128_s4_hb,
  wc_rkmTrajPack_m32_r128_s4_v0, wc_rkmTrajPack_m32_r128_s4_v2)]) rkmRowPack_m32_r128, bNatListEq
  (bEvalLo12W 16 512 19 [1,2,2,2] [99102917,69667618,24183424,9298222] [9,10,4,2]
  rkmMasksPack_m16_r19 []) rkmRowPack_m16_r19, bNatListEq (bEvalLo12W 2 4096 17 [1,3,6,12]
  [40647609,51262295,53416384,78341954] [1,2,4,8] rkmMasksPack_m2_r17 []) rkmRowPack_m2_r17] =
  true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bSlideChk 17 129 wc_rkmTraj_m128_r128_s2_hb
  wc_rkmTraj_m128_r128_s2_v0 wc_rkmTraj_m128_r128_s2_v1, bNatListEq (bEvalLo12W 4 2048 23
  [1,4,8,8,8] [56701056,58319562,78221747,24697977,14432628] [2,6,12,4,3] rkmMasksPack_m4_r23 [])
  rkmRowPack_m4_r23, bNatListEq (bEvalLo12W 16 512 9 [1,1,1,1,1,1,1,1]
  [36337013,72306961,36366061,29036499,17229594,18783241,9112309,7913963] [2,4,2,2,1,1,1,1]
  rkmMasksPack_m16_r9 []) rkmRowPack_m16_r9] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := atF [ bSlideChk 17 129 wc_rkmTraj_m128_r128_s3_hb
  wc_rkmTraj_m128_r128_s3_v0 wc_rkmTraj_m128_r128_s3_v1, bNatListEq (bEvalLo12W 512 16 19 [1,1,1]
  [33394223,1077834,84594] [21,2,2] rkmMasks_m512_r19 []) rkmRow_m512_r19, bNatListEq (bEvalLo12W
  256 32 13 [1,1] [47717451,990464] [16,2] rkmMasks_m256_r13 []) rkmRow_m256_r13] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := atF [ bNatListEq (bEvalLo12W 128 64 128 [1,1,2,2,2,2,2,2]
  [19340057,23012918,12552501,12552501,1850239,1964435,875712,684131] [32,38,33,33,5,6,3,2]
  rkmMasks_m128_r128 [some (32, 129, wc_rkmTraj_m128_r128_s0_hb, wc_rkmTraj_m128_r128_s0_v0,
  wc_rkmTraj_m128_r128_s0_v2), some (38, 129, wc_rkmTraj_m128_r128_s1_hb,
  wc_rkmTraj_m128_r128_s1_v0, wc_rkmTraj_m128_r128_s1_v2), some (33, 129,
  wc_rkmTraj_m128_r128_s2_hb, wc_rkmTraj_m128_r128_s2_v0, wc_rkmTraj_m128_r128_s2_v2), some (33,
  129, wc_rkmTraj_m128_r128_s3_hb, wc_rkmTraj_m128_r128_s3_v0, wc_rkmTraj_m128_r128_s3_v2)])
  rkmRow_m128_r128, bNatListEq (bEvalLo12W 16 512 23 [1,2,2,2,2]
  [75487778,78770980,27088242,16715596,9326700] [8,13,6,4,3] rkmMasks_m16_r23 []) rkmRow_m16_r23,
  bNatListEq (bEvalLo12W 512 16 8 [1,1] [26657373,7071068] [9,3] rkmMasks_m512_r8 [])
  rkmRow_m512_r8] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m128_r128_s0_hb
  wc_rkmTraj_m128_r128_s0_v0 wc_rkmTraj_m128_r128_s0_v1, bNatListEq (bEvalLo12W 16 512 22
  [1,2,2,2,2] [77505030,75471474,26075159,15970557,8824642] [8,13,5,4,3] rkmMasks_m16_r22 [])
  rkmRow_m16_r22, bNatListEq (bEvalLo12W 64 128 3 [1,1] [54247413,36064030] [3,2]
  rkmMasksPack_m64_r3 []) rkmRowPack_m64_r3] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m128_r128_s0_hb
  wc_rkmTraj_m128_r128_s0_v1 wc_rkmTraj_m128_r128_s0_v2, bNatListEq (bEvalLo12W 64 128 22
  [1,1,1,1,1,1,1,1] [18732709,35621117,19098689,9741258,8756243,6900964,5090690,3399240]
  [5,9,5,3,2,2,2,1] rkmMasksPack_m64_r22 []) rkmRowPack_m64_r22, bNatListEq (bEvalLo12W 4 2048 18
  [1,4] [91507064,91267631] [4,9] rkmMasks_m4_r18 []) rkmRow_m4_r18] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m128_r128_s2_hb
  wc_rkmTraj_m128_r128_s2_v1 wc_rkmTraj_m128_r128_s2_v2, bNatListEq (bEvalLo12W 8 1024 22
  [1,4,4,4] [79458416,106171455,26234746,7071544] [6,17,5,3] rkmMasks_m8_r22 []) rkmRow_m8_r22,
  bNatListEq (bEvalLo12W 1024 8 12 [1,1] [18793801,5300816] [13,4] rkmMasks_m1024_r12 [])
  rkmRow_m1024_r12] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m128_r128_s3_hb
  wc_rkmTraj_m128_r128_s3_v1 wc_rkmTraj_m128_r128_s3_v2, bNatListEq (bEvalLo12W 16 512 20
  [1,2,2,2] [87542311,79302625,24193615,9382837] [9,12,5,3] rkmMasks_m16_r20 []) rkmRow_m16_r20,
  bNatListEq (bEvalLo12W 8 1024 27 [1,3] [89171930,50939757] [6,8] rkmMasksPack_m8_r27 [])
  rkmRowPack_m8_r27] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := atF [ bNatListEq (bEvalLo12W 64 128 56 [1,1,1,1,2,2,2,2]
  [15203815,62120678,9435543,8971100,8805140,7358587,1155190,4804524] [8,31,5,5,7,6,1,4]
  rkmMasksPack_m64_r56 [none, some (31, 57, wc_rkmTrajPack_m64_r56_s1_hb,
  wc_rkmTrajPack_m64_r56_s1_v0, wc_rkmTrajPack_m64_r56_s1_v1)]) rkmRowPack_m64_r56, bNatListEq
  (bEvalLo12W 4 2048 36 [1,2,4,8,14,14,14]
  [37927621,27505932,31394810,30958100,32445574,228721,87212] [2,2,4,7,11,1,1] rkmMasksPack_m4_r36
  []) rkmRowPack_m4_r36, bNatListEq (bEvalLo12W 64 128 8 [1,1,1,1,1,1,1,1]
  [46054954,46054954,1944773,1958698,565202,568612,323012,319783] [5,5,1,1,1,1,1,1]
  rkmMasks_m64_r8 []) rkmRow_m64_r8] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := atF [ bSlideChk 15 129 wc_rkmTrajPack_m32_r128_s3_hb
  wc_rkmTrajPack_m32_r128_s3_v0 wc_rkmTrajPack_m32_r128_s3_v1, bNatListEq (bEvalLo12W 32 256 24
  [1,1,1,1] [88359193,61143018,26547531,12072400] [15,11,6,3] rkmMasks_m32_r24 []) rkmRow_m32_r24,
  bNatListEq (bEvalLo12W 2 4096 19 [1] [128089838] [4] rkmMasks_m2_r19 []) rkmRow_m2_r19] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := atF [ bSlideChk 14 129 wc_rkmTrajPack_m32_r128_s3_hb
  wc_rkmTrajPack_m32_r128_s3_v1 wc_rkmTrajPack_m32_r128_s3_v2, bSlideChk 15 65
  wc_rkmTrajPack_m32_r128_s1_hb wc_rkmTrajPack_m32_r128_s1_v0 wc_rkmTrajPack_m32_r128_s1_v1,
  bNatListEq (bEvalLo12W 64 128 6 [1,1,1] [69923319,21787634,4124028] [6,2,1] rkmMasksPack_m64_r6
  []) rkmRowPack_m64_r6] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := atF [ bSlideChk 14 129 wc_rkmTrajPack_m32_r128_s4_hb
  wc_rkmTrajPack_m32_r128_s4_v0 wc_rkmTrajPack_m32_r128_s4_v1, bNatListEq (bEvalLo12W 2 4096 32
  [2,4,8,16,30,30,30,30] [41278082,30610977,35102617,45624077,17174439,18082797,6766819,6013097]
  [2,2,4,9,6,6,3,2] rkmMasksPack_m2_r32 []) rkmRowPack_m2_r32, bNatListEq (bEvalLo12W 2 4096 12
  [1,2,4,8,10,10,10,10] [51098588,46622494,59376895,28410540,27800269,53662058,11184798,3519716]
  [1,2,3,2,2,4,1,1] rkmMasksPack_m2_r12 []) rkmRowPack_m2_r12] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := atF [ bSlideChk 14 129 wc_rkmTrajPack_m32_r128_s4_hb
  wc_rkmTrajPack_m32_r128_s4_v1 wc_rkmTrajPack_m32_r128_s4_v2, bNatListEq (bEvalLo12W 32 256 27
  [1,2,2] [86462068,39262321,13306994] [16,12,5] rkmMasks_m32_r27 []) rkmRow_m32_r27, bNatListEq
  (bEvalLo12W 64 128 10 [1,1,1] [93522097,3801533,2023636] [12,2,2] rkmMasks_m64_r10 [])
  rkmRow_m64_r10] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := atF [ bSlideChk 31 57 wc_rkmTrajPack_m64_r56_s1_hb
  wc_rkmTrajPack_m64_r56_s1_v0 wc_rkmTrajPack_m64_r56_s1_v1, bSlideChk 16 65
  wc_rkmTraj_m2_r64_s6_hb wc_rkmTraj_m2_r64_s6_v0 wc_rkmTraj_m2_r64_s6_v1, bNatListEq (bEvalLo12W
  16 512 5 [1,1,1] [173102907,18242131,8373408] [7,2,2] rkmMasks_m16_r5 []) rkmRow_m16_r5] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := atF [ bNatListEq (bEvalLo12W 64 128 112 [1,1,1,1,1,1,1,1]
  [4946799,6714892,5124341,1524217,1566963,2597664,2584360,1777369] [4,6,5,2,2,3,3,2]
  rkmMasksPack_m64_r112 []) rkmRowPack_m64_r112, bNatListEq (bEvalLo12W 256 32 28 [1] [50000192]
  [37] rkmMasks_m256_r28 []) rkmRow_m256_r28, bNatListEq (bEvalLo12W 64 128 5 [1,1,1]
  [69942874,21318558,3313295] [6,3,2] rkmMasks_m64_r5 []) rkmRow_m64_r5] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := atF [ bNatListEq (bEvalLo12W 16 512 40 [1,2,4,5,5,5]
  [45946875,22041963,16398282,47292838,7152212,1772174] [7,6,7,22,4,1] rkmMasks_m16_r40 [])
  rkmRow_m16_r40, bNatListEq (bEvalLo12W 64 128 29 [1,1,1,1,1,1,1,1]
  [32094989,26669467,21926273,9515188,8553004,4621038,5252993,3936923] [10,8,7,3,3,2,2,2]
  rkmMasksPack_m64_r29 []) rkmRowPack_m64_r29, bNatListEq (bEvalLo12W 512 16 3 [1,1,1]
  [21584876,5713644,4435946] [4,2,2] rkmMasks_m512_r3 []) rkmRow_m512_r3] = true
private theorem bk_21 : dP_21 := by decide +kernel
private abbrev dP_22 : Prop := atF [ bNatListEq (bEvalLo12W 32 256 34 [1,2] [59656090,74417929]
  [14,27] rkmMasks_m32_r34 []) rkmRow_m32_r34, bNatListEq (bEvalLo12W 256 32 31 [1] [50202833]
  [36] rkmMasks_m256_r31 []) rkmRow_m256_r31, bNatListEq (bEvalLo12W 128 64 16 [1,1,1]
  [67175144,2130867,1176527] [18,1,1] rkmMasks_m128_r16 []) rkmRow_m128_r16] = true
private theorem bk_22 : dP_22 := by decide +kernel
private abbrev dP_23 : Prop := atF [ bNatListEq (bEvalLo12W 16 512 36 [1,2,4,4,4]
  [48133412,35367547,66830174,5624473,917496] [6,8,23,2,1] rkmMasksPack_m16_r36 [])
  rkmRowPack_m16_r36, bNatListEq (bEvalLo12W 32 256 32 [1,2,2,2]
  [80941462,41533382,15393427,5351505] [17,14,5,2] rkmMasks_m32_r32 []) rkmRow_m32_r32, bNatListEq
  (bEvalLo12W 16 512 15 [1,2,2,2] [128532067,42488801,23176375,9018751] [9,5,3,1]
  rkmMasksPack_m16_r15 []) rkmRowPack_m16_r15] = true
private theorem bk_23 : dP_23 := by decide +kernel
private theorem ws_rkmTraj_m128_r128_s0 : WalkOk (some (32, 129, wc_rkmTraj_m128_r128_s0_hb,
    wc_rkmTraj_m128_r128_s0_v0, wc_rkmTraj_m128_r128_s0_v2)) := mIter_split rfl
    (bSlideChk_sound bk_10) (bSlideChk_sound bk_11)
private theorem ws_rkmTraj_m128_r128_s1 : WalkOk (some (38, 129, wc_rkmTraj_m128_r128_s1_hb,
    wc_rkmTraj_m128_r128_s1_v0, wc_rkmTraj_m128_r128_s1_v2)) := mIter_split rfl
    (bSlideChk_sound bk_3) (bSlideChk_sound bk_4)
private theorem ws_rkmTraj_m128_r128_s2 : WalkOk (some (33, 129, wc_rkmTraj_m128_r128_s2_hb,
    wc_rkmTraj_m128_r128_s2_v0, wc_rkmTraj_m128_r128_s2_v2)) := mIter_split rfl
    (bSlideChk_sound bk_7) (bSlideChk_sound bk_12)
private theorem ws_rkmTraj_m128_r128_s3 : WalkOk (some (33, 129, wc_rkmTraj_m128_r128_s3_hb,
    wc_rkmTraj_m128_r128_s3_v0, wc_rkmTraj_m128_r128_s3_v2)) := mIter_split rfl
    (bSlideChk_sound bk_8) (bSlideChk_sound bk_13)
private theorem ws_rkmTrajPack_m32_r128_s2 : WalkOk (some (39, 129, wc_rkmTrajPack_m32_r128_s2_hb,
    wc_rkmTrajPack_m32_r128_s2_v0, wc_rkmTrajPack_m32_r128_s2_v2)) := mIter_split rfl
    (bSlideChk_sound bk_1) (bSlideChk_sound bk_2)
private theorem ws_rkmTrajPack_m32_r128_s3 : WalkOk (some (29, 129, wc_rkmTrajPack_m32_r128_s3_hb,
    wc_rkmTrajPack_m32_r128_s3_v0, wc_rkmTrajPack_m32_r128_s3_v2)) := mIter_split rfl
    (bSlideChk_sound bk_15) (bSlideChk_sound bk_16)
private theorem ws_rkmTrajPack_m32_r128_s4 : WalkOk (some (28, 129, wc_rkmTrajPack_m32_r128_s4_hb,
    wc_rkmTrajPack_m32_r128_s4_v0, wc_rkmTrajPack_m32_r128_s4_v2)) := mIter_split rfl
    (bSlideChk_sound bk_17) (bSlideChk_sound bk_18)
/-- Kernel trajectory certificate `(m = 128, r = 128)`. -/
theorem rkmTraj_m128_r128 : rkmEvalT16Lo12 128 64 128 [1, 1, 2, 2, 2, 2, 2, 2] [19340057, 23012918,
  12552501, 12552501, 1850239, 1964435, 875712, 684131] [32, 38, 33, 33, 5, 6, 3, 2]
  rkmMasks_m128_r128 = rkmRow_m128_r128 :=
    bhW_eq bk_9 (wCons ws_rkmTraj_m128_r128_s0 (wCons ws_rkmTraj_m128_r128_s1 (wCons
      ws_rkmTraj_m128_r128_s2 (wCons ws_rkmTraj_m128_r128_s3 wNil))))
/-- Kernel trajectory certificate `(m = 256, r = 18)`. -/
theorem rkmTraj_m256_r18 : rkmEvalT16Lo12 256 32 18 [1, 1] [48224498, 1003342] [21, 2]
  rkmMasks_m256_r18 = rkmRow_m256_r18 := bh0_eq (tl1 bk_2)
/-- Kernel trajectory certificate `(m = 2, r = 19)`. -/
theorem rkmTraj_m2_r19 : rkmEvalT16Lo12 2 4096 19 [1] [128089838] [4] rkmMasks_m2_r19 =
  rkmRow_m2_r19 := bh0_eq (tl2 bk_15)
/-- Kernel trajectory certificate `(m = 2, r = 64)`. -/
theorem rkmTraj_m2_r64 : rkmEvalT16Lo12 2 4096 64 [1, 3, 7, 15, 30, 58, 58, 58] [18699679, 22184902,
  22954891, 24409365, 28094556, 15378415, 17605775, 6014002] [1, 2, 4, 8, 16, 14, 16, 6]
  rkmMasks_m2_r64 = rkmRow_m2_r64 :=
    bhW_eq bk_0 (wSkip (wSkip (wSkip (wSkip (wSkip (wSkip (wCons (bSlideChk_sound (tl1 bk_19))
      wNil)))))))
/-- Kernel trajectory certificate `(m = 512, r = 3)`. -/
theorem rkmTraj_m512_r3 : rkmEvalT16Lo12 512 16 3 [1, 1, 1] [21584876, 5713644, 4435946] [4, 2, 2]
  rkmMasks_m512_r3 = rkmRow_m512_r3 := bh0_eq (tl2 bk_21)
/-- Kernel trajectory certificate `(m = 16, r = 40)`. -/
theorem rkmTraj_m16_r40 : rkmEvalT16Lo12 16 512 40 [1, 2, 4, 5, 5, 5] [45946875, 22041963, 16398282,
  47292838, 7152212, 1772174] [7, 6, 7, 22, 4, 1] rkmMasks_m16_r40 = rkmRow_m16_r40 :=
    bh0_eq bk_21
/-- Kernel trajectory certificate `(m = 16, r = 5)`. -/
theorem rkmTraj_m16_r5 : rkmEvalT16Lo12 16 512 5 [1, 1, 1] [173102907, 18242131, 8373408] [7, 2, 2]
  rkmMasks_m16_r5 = rkmRow_m16_r5 := bh0_eq (tl2 bk_19)
/-- Kernel trajectory certificate `(m = 32, r = 34)`. -/
theorem rkmTraj_m32_r34 : rkmEvalT16Lo12 32 256 34 [1, 2] [59656090, 74417929] [14, 27]
  rkmMasks_m32_r34 = rkmRow_m32_r34 := bh0_eq bk_22
/-- Kernel trajectory certificate `(m = 64, r = 5)`. -/
theorem rkmTraj_m64_r5 : rkmEvalT16Lo12 64 128 5 [1, 1, 1] [69942874, 21318558, 3313295] [6, 3, 2]
  rkmMasks_m64_r5 = rkmRow_m64_r5 := bh0_eq (tl2 bk_20)
/-- Kernel trajectory certificate `(m = 32, r = 32)`. -/
theorem rkmTraj_m32_r32 : rkmEvalT16Lo12 32 256 32 [1, 2, 2, 2] [80941462, 41533382, 15393427,
  5351505] [17, 14, 5, 2] rkmMasks_m32_r32 = rkmRow_m32_r32 := bh0_eq (tl1 bk_23)
/-- Kernel trajectory certificate `(m = 512, r = 8)`. -/
theorem rkmTraj_m512_r8 : rkmEvalT16Lo12 512 16 8 [1, 1] [26657373, 7071068] [9, 3] rkmMasks_m512_r8
  = rkmRow_m512_r8 := bh0_eq (tl2 bk_9)
/-- Kernel trajectory certificate `(m = 256, r = 31)`. -/
theorem rkmTraj_m256_r31 : rkmEvalT16Lo12 256 32 31 [1] [50202833] [36] rkmMasks_m256_r31 =
  rkmRow_m256_r31 := bh0_eq (tl1 bk_22)
/-- Kernel trajectory certificate `(m = 64, r = 7)`. -/
theorem rkmTraj_m64_r7 : rkmEvalT16Lo12 64 128 7 [1, 1, 1] [93199702, 2483081, 1205182] [10, 2, 2]
  rkmMasks_m64_r7 = rkmRow_m64_r7 := bh0_eq (tl2 bk_3)
/-- Kernel trajectory certificate `(m = 256, r = 28)`. -/
theorem rkmTraj_m256_r28 : rkmEvalT16Lo12 256 32 28 [1] [50000192] [37] rkmMasks_m256_r28 =
  rkmRow_m256_r28 := bh0_eq (tl1 bk_20)
/-- Kernel trajectory certificate `(m = 64, r = 8)`. -/
theorem rkmTraj_m64_r8 : rkmEvalT16Lo12 64 128 8 [1, 1, 1, 1, 1, 1, 1, 1] [46054954, 46054954,
  1944773, 1958698, 565202, 568612, 323012, 319783] [5, 5, 1, 1, 1, 1, 1, 1] rkmMasks_m64_r8 =
  rkmRow_m64_r8 := bh0_eq (tl2 bk_14)
/-- Kernel trajectory certificate `(m = 32, r = 27)`. -/
theorem rkmTraj_m32_r27 : rkmEvalT16Lo12 32 256 27 [1, 2, 2] [86462068, 39262321, 13306994] [16, 12,
  5] rkmMasks_m32_r27 = rkmRow_m32_r27 := bh0_eq (tl1 bk_18)
/-- Kernel trajectory certificate `(m = 4, r = 18)`. -/
theorem rkmTraj_m4_r18 : rkmEvalT16Lo12 4 2048 18 [1, 4] [91507064, 91267631] [4, 9] rkmMasks_m4_r18
  = rkmRow_m4_r18 := bh0_eq (tl2 bk_11)
/-- Kernel trajectory certificate `(m = 32, r = 24)`. -/
theorem rkmTraj_m32_r24 : rkmEvalT16Lo12 32 256 24 [1, 1, 1, 1] [88359193, 61143018, 26547531,
  12072400] [15, 11, 6, 3] rkmMasks_m32_r24 = rkmRow_m32_r24 := bh0_eq (tl1 bk_15)
/-- Kernel trajectory certificate `(m = 64, r = 10)`. -/
theorem rkmTraj_m64_r10 : rkmEvalT16Lo12 64 128 10 [1, 1, 1] [93522097, 3801533, 2023636] [12, 2, 2]
  rkmMasks_m64_r10 = rkmRow_m64_r10 := bh0_eq (tl2 bk_18)
/-- Kernel trajectory certificate `(m = 16, r = 23)`. -/
theorem rkmTraj_m16_r23 : rkmEvalT16Lo12 16 512 23 [1, 2, 2, 2, 2] [75487778, 78770980, 27088242,
  16715596, 9326700] [8, 13, 6, 4, 3] rkmMasks_m16_r23 = rkmRow_m16_r23 := bh0_eq (tl1 bk_9)
/-- Kernel trajectory certificate `(m = 1024, r = 12)`. -/
theorem rkmTraj_m1024_r12 : rkmEvalT16Lo12 1024 8 12 [1, 1] [18793801, 5300816] [13, 4]
  rkmMasks_m1024_r12 = rkmRow_m1024_r12 := bh0_eq (tl2 bk_12)
/-- Kernel trajectory certificate `(m = 16, r = 22)`. -/
theorem rkmTraj_m16_r22 : rkmEvalT16Lo12 16 512 22 [1, 2, 2, 2, 2] [77505030, 75471474, 26075159,
  15970557, 8824642] [8, 13, 5, 4, 3] rkmMasks_m16_r22 = rkmRow_m16_r22 := bh0_eq (tl1 bk_10)
/-- Kernel trajectory certificate `(m = 256, r = 13)`. -/
theorem rkmTraj_m256_r13 : rkmEvalT16Lo12 256 32 13 [1, 1] [47717451, 990464] [16, 2]
  rkmMasks_m256_r13 = rkmRow_m256_r13 := bh0_eq (tl2 bk_8)
/-- Kernel trajectory certificate `(m = 8, r = 22)`. -/
theorem rkmTraj_m8_r22 : rkmEvalT16Lo12 8 1024 22 [1, 4, 4, 4] [79458416, 106171455, 26234746,
  7071544] [6, 17, 5, 3] rkmMasks_m8_r22 = rkmRow_m8_r22 := bh0_eq (tl1 bk_12)
/-- Kernel trajectory certificate `(m = 1024, r = 14)`. -/
theorem rkmTraj_m1024_r14 : rkmEvalT16Lo12 1024 8 14 [1, 1] [20553616, 3627109] [16, 3]
  rkmMasks_m1024_r14 = rkmRow_m1024_r14 := bh0_eq (tl1 bk_0)
/-- Kernel trajectory certificate `(m = 16, r = 20)`. -/
theorem rkmTraj_m16_r20 : rkmEvalT16Lo12 16 512 20 [1, 2, 2, 2] [87542311, 79302625, 24193615,
  9382837] [9, 12, 5, 3] rkmMasks_m16_r20 = rkmRow_m16_r20 := bh0_eq (tl1 bk_13)
/-- Kernel trajectory certificate `(m = 16, r = 13)`. -/
theorem rkmTraj_m16_r13 : rkmEvalT16Lo12 16 512 13 [1, 1, 1, 1] [191960317, 25750043, 30985127,
  22582771] [13, 3, 3, 3] rkmMasks_m16_r13 = rkmRow_m16_r13 := bh0_eq (tl1 bk_1)
/-- Kernel trajectory certificate `(m = 512, r = 19)`. -/
theorem rkmTraj_m512_r19 : rkmEvalT16Lo12 512 16 19 [1, 1, 1] [33394223, 1077834, 84594] [21, 2, 2]
  rkmMasks_m512_r19 = rkmRow_m512_r19 := bh0_eq (tl1 bk_8)
/-- Kernel trajectory certificate `(m = 128, r = 16)`. -/
theorem rkmTraj_m128_r16 : rkmEvalT16Lo12 128 64 16 [1, 1, 1] [67175144, 2130867, 1176527] [18, 1,
  1] rkmMasks_m128_r16 = rkmRow_m128_r16 := bh0_eq (tl2 bk_22)
/-- Kernel trajectory certificate `(m = 8, r = 18)`. -/
theorem rkmTraj_m8_r18 : rkmEvalT16Lo12 8 1024 18 [1, 3, 3, 3] [82769832, 131710082, 26891107,
  7119226] [5, 15, 4, 2] rkmMasks_m8_r18 = rkmRow_m8_r18 := bh0_eq (tl1 bk_5)
/-- Krotov trajectory `(m = 32, r = 128)`. -/
theorem rkmTrajPack_m32_r128 : rkmEvalT16Lo12 32 256 128 [1,2,4,7,7,7,7,7]
  [26925892,17043556,25667091,12950726,12526267,2424443,1439567,1359247] [13,15,39,29,28,6,4,4]
  rkmMasksPack_m32_r128 = rkmRowPack_m32_r128 :=
    bhW_eq bk_6 (wSkip (wCons (bSlideChk_sound (tl1 bk_16)) (wCons ws_rkmTrajPack_m32_r128_s2
      (wCons ws_rkmTrajPack_m32_r128_s3 (wCons ws_rkmTrajPack_m32_r128_s4 wNil)))))
/-- Krotov trajectory `(m = 64, r = 3)`. -/
theorem rkmTrajPack_m64_r3 : rkmEvalT16Lo12 64 128 3 [1,1] [54247413,36064030] [3,2]
  rkmMasksPack_m64_r3 = rkmRowPack_m64_r3 := bh0_eq (tl2 bk_10)
/-- Krotov trajectory `(m = 64, r = 56)`. -/
theorem rkmTrajPack_m64_r56 : rkmEvalT16Lo12 64 128 56 [1,1,1,1,2,2,2,2]
  [15203815,62120678,9435543,8971100,8805140,7358587,1155190,4804524] [8,31,5,5,7,6,1,4]
  rkmMasksPack_m64_r56 = rkmRowPack_m64_r56 :=
    bhW_eq bk_14 (wSkip (wCons (bSlideChk_sound bk_19) wNil))
/-- Krotov trajectory `(m = 64, r = 6)`. -/
theorem rkmTrajPack_m64_r6 : rkmEvalT16Lo12 64 128 6 [1,1,1] [69923319,21787634,4124028] [6,2,1]
  rkmMasksPack_m64_r6 = rkmRowPack_m64_r6 := bh0_eq (tl2 bk_16)
/-- Krotov trajectory `(m = 16, r = 48)`. -/
theorem rkmTrajPack_m16_r48 : rkmEvalT16Lo12 16 512 48 [1,1,2,3,5,5,5,5]
  [22281663,27438406,22518257,26744883,20699296,26957388,7425181,2742036] [4,4,6,10,11,14,4,2]
  rkmMasksPack_m16_r48 = rkmRowPack_m16_r48 := bh0_eq bk_5
/-- Krotov trajectory `(m = 8, r = 52)`. -/
theorem rkmTrajPack_m8_r52 : rkmEvalT16Lo12 8 1024 52 [1,1,1,1,1,1,1,1]
  [21021499,2403702,18861336,9185697,5321366,207753,740819,4296202] [2,1,2,1,1,1,1,1]
  rkmMasksPack_m8_r52 = rkmRowPack_m8_r52 := bh0_eq (tl2 bk_4)
/-- Krotov trajectory `(m = 64, r = 112)`. -/
theorem rkmTrajPack_m64_r112 : rkmEvalT16Lo12 64 128 112 [1,1,1,1,1,1,1,1]
  [4946799,6714892,5124341,1524217,1566963,2597664,2584360,1777369] [4,6,5,2,2,3,3,2]
  rkmMasksPack_m64_r112 = rkmRowPack_m64_r112 := bh0_eq bk_20
/-- Krotov trajectory `(m = 8, r = 112)`. -/
theorem rkmTrajPack_m8_r112 : rkmEvalT16Lo12 8 1024 112 [1,1,1,1,1,1,1,1]
  [13595015,21178233,6581905,4798156,11428497,256614,49852,10846585] [2,3,1,1,2,1,1,2]
  rkmMasksPack_m8_r112 = rkmRowPack_m8_r112 := bh0_eq (tl2 bk_5)
/-- Krotov trajectory `(m = 16, r = 36)`. -/
theorem rkmTrajPack_m16_r36 : rkmEvalT16Lo12 16 512 36 [1,2,4,4,4]
  [48133412,35367547,66830174,5624473,917496] [6,8,23,2,1] rkmMasksPack_m16_r36 = rkmRowPack_m16_r36
  := bh0_eq bk_23
/-- Krotov trajectory `(m = 16, r = 9)`. -/
theorem rkmTrajPack_m16_r9 : rkmEvalT16Lo12 16 512 9 [1,1,1,1,1,1,1,1]
  [36337013,72306961,36366061,29036499,17229594,18783241,9112309,7913963] [2,4,2,2,1,1,1,1]
  rkmMasksPack_m16_r9 = rkmRowPack_m16_r9 := bh0_eq (tl2 bk_7)
/-- Krotov trajectory `(m = 64, r = 29)`. -/
theorem rkmTrajPack_m64_r29 : rkmEvalT16Lo12 64 128 29 [1,1,1,1,1,1,1,1]
  [32094989,26669467,21926273,9515188,8553004,4621038,5252993,3936923] [10,8,7,3,3,2,2,2]
  rkmMasksPack_m64_r29 = rkmRowPack_m64_r29 := bh0_eq (tl1 bk_21)
/-- Krotov trajectory `(m = 2, r = 12)`. -/
theorem rkmTrajPack_m2_r12 : rkmEvalT16Lo12 2 4096 12 [1,2,4,8,10,10,10,10]
  [51098588,46622494,59376895,28410540,27800269,53662058,11184798,3519716] [1,2,3,2,2,4,1,1]
  rkmMasksPack_m2_r12 = rkmRowPack_m2_r12 := bh0_eq (tl2 bk_17)
/-- Krotov trajectory `(m = 2, r = 32)`. -/
theorem rkmTrajPack_m2_r32 : rkmEvalT16Lo12 2 4096 32 [2,4,8,16,30,30,30,30]
  [41278082,30610977,35102617,45624077,17174439,18082797,6766819,6013097] [2,2,4,9,6,6,3,2]
  rkmMasksPack_m2_r32 = rkmRowPack_m2_r32 := bh0_eq (tl1 bk_17)
/-- Krotov trajectory `(m = 2, r = 17)`. -/
theorem rkmTrajPack_m2_r17 : rkmEvalT16Lo12 2 4096 17 [1,3,6,12]
  [40647609,51262295,53416384,78341954] [1,2,4,8] rkmMasksPack_m2_r17 = rkmRowPack_m2_r17 :=
    bh0_eq (tl2 bk_6)
/-- Krotov trajectory `(m = 4, r = 36)`. -/
theorem rkmTrajPack_m4_r36 : rkmEvalT16Lo12 4 2048 36 [1,2,4,8,14,14,14]
  [37927621,27505932,31394810,30958100,32445574,228721,87212] [2,2,4,7,11,1,1] rkmMasksPack_m4_r36 =
  rkmRowPack_m4_r36 := bh0_eq (tl1 bk_14)
/-- Krotov trajectory `(m = 8, r = 27)`. -/
theorem rkmTrajPack_m8_r27 : rkmEvalT16Lo12 8 1024 27 [1,3] [89171930,50939757] [6,8]
  rkmMasksPack_m8_r27 = rkmRowPack_m8_r27 := bh0_eq (tl2 bk_13)
/-- Krotov trajectory `(m = 64, r = 22)`. -/
theorem rkmTrajPack_m64_r22 : rkmEvalT16Lo12 64 128 22 [1,1,1,1,1,1,1,1]
  [18732709,35621117,19098689,9741258,8756243,6900964,5090690,3399240] [5,9,5,3,2,2,2,1]
  rkmMasksPack_m64_r22 = rkmRowPack_m64_r22 := bh0_eq (tl1 bk_11)
/-- Krotov trajectory `(m = 16, r = 15)`. -/
theorem rkmTrajPack_m16_r15 : rkmEvalT16Lo12 16 512 15 [1,2,2,2]
  [128532067,42488801,23176375,9018751] [9,5,3,1] rkmMasksPack_m16_r15 = rkmRowPack_m16_r15 :=
    bh0_eq (tl2 bk_23)
/-- Krotov trajectory `(m = 4, r = 23)`. -/
theorem rkmTrajPack_m4_r23 : rkmEvalT16Lo12 4 2048 23 [1,4,8,8,8]
  [56701056,58319562,78221747,24697977,14432628] [2,6,12,4,3] rkmMasksPack_m4_r23 =
  rkmRowPack_m4_r23 := bh0_eq (tl1 bk_7)
/-- Krotov trajectory `(m = 4, r = 17)`. -/
theorem rkmTrajPack_m4_r17 : rkmEvalT16Lo12 4 2048 17 [1,2,4,8,8,8,8,8]
  [58421155,44373706,55604127,32069021,34891761,11178356,3236904,2742026] [2,2,5,4,5,2,1,1]
  rkmMasksPack_m4_r17 = rkmRowPack_m4_r17 := bh0_eq (tl1 bk_4)
/-- Krotov trajectory `(m = 16, r = 19)`. -/
theorem rkmTrajPack_m16_r19 : rkmEvalT16Lo12 16 512 19 [1,2,2,2]
  [99102917,69667618,24183424,9298222] [9,10,4,2] rkmMasksPack_m16_r19 = rkmRowPack_m16_r19 :=
    bh0_eq (tl1 bk_6)
/-- Krotov trajectory `(m = 4, r = 19)`. -/
theorem rkmTrajPack_m4_r19 : rkmEvalT16Lo12 4 2048 19 [1,3,7,7,7]
  [60292114,61429099,79729952,26849916,16222793] [2,5,10,4,2] rkmMasksPack_m4_r19 =
  rkmRowPack_m4_r19 := bh0_eq (tl1 bk_3)
end
end QuantumComputation.Specs.DickeSol
