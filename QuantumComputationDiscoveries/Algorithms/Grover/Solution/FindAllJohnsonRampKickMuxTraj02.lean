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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxTraj00
/-
# Multi-Segment `T_16` Trajectory Part `02` (`FindAllJohnsonRampKickMuxTraj02`)

Certified kernel trajectory evaluations (`30` rows, `38000` substep-coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Prefix-kick masks for `(m = 2, r = 5)`. -/
def rkmMasks_m2_r5 : List (List Bool) := [
  [], [], [true], [false, true, true], [], [], [true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 5)`. -/
def rkmRow_m2_r5 : List ℕ := [1826712739, 909831344, 541085711, 418704380607, 577999154079]
/-- Prefix-kick masks for `(m = 2, r = 13)`. -/
def rkmMasks_m2_r13 : List (List Bool) := [
  [], [], [], [false, false, false, false, true, true],
  [false, true, false, false, true, false, false, true, true],
  [true, false, false, true, false, false, false, false, false, true, true],
  [true, true, true, true, true, true, true, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 13)`. -/
def rkmRow_m2_r13 : List ℕ := [
  1529379, 57239532, 292727776, 436712036, 311650548, 897068346, 105974745, 5385490305,
  7150223231, 136911235, 12283027026, 450453965148, 522483330852]
/-- Mask chunk for `(m = 2, r = 36)`. -/
def rkmMkP_m2_r36_s4_p0 : List Bool := [
  false, false, false, false, true, false, true, false, true, false, true, true, true, true, true,
  false, true, false, false, true, true, false, false, true, true, true, false, false, true, true,
  true]
/-- Mask chunk for `(m = 2, r = 36)`. -/
def rkmMkP_m2_r36_s5_p0 : List Bool := [
  false, false, false, false, false, false, false, true, false, true, false, false, true, true,
  false, true, true, false, false, false, false, true, false, true]
/-- Prefix-kick masks for `(m = 2, r = 36)`. -/
def rkmMasks_m2_r36 : List (List Bool) := [
  [], [], [], [], rkmMkP_m2_r36_s4_p0, rkmMkP_m2_r36_s5_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 36)`. -/
def rkmRow_m2_r36 : List ℕ := [
  0, 0, 0, 0, 0, 0, 28, 165, 53, 597, 2551, 99289, 20666, 11817, 33146, 2028122, 705260, 2204147,
  946873, 76244030, 133881, 656534582, 25575561, 1365113351, 249789351, 160834777, 11215487581,
  41305760, 21468181450, 30184244745, 4919317808, 96645220709, 350610964412, 343353484444,
  124171144782, 14850369146]
/-- Prefix-kick masks for `(m = 4, r = 7)`. -/
def rkmMasks_m4_r7 : List (List Bool) := [
  [], [true, false, true], [false, true, false, true, true],
  [false, false, true, false, false, true], [false, false, true, false, false, true],
  [true, false, false, false, true], [true, true, true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 7)`. -/
def rkmRow_m4_r7 : List ℕ := [
  414177888, 13906405, 1575751001, 1634575742, 6225847, 149379602555, 846975741925]
/-- Prefix-kick masks for `(m = 4, r = 13)`. -/
def rkmMasks_m4_r13 : List (List Bool) := [
  [], [], [false, false, false, false, true, true, true],
  [true, false, true, false, false, true, false, false, true, true],
  [false, true, false, false, true, false, false, false, false, false, true],
  [false, true, false, true, true, false, true, true, true, false, false, true],
  [true, false, false, false, false, true, true, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 13)`. -/
def rkmRow_m4_r13 : List ℕ := [
  2771704, 8178094, 112965401, 398011035, 202661430, 237252205, 401313708, 136223120, 1939976980,
  15219355121, 32068414, 176252769002, 805056453680]
/-- Mask chunk for `(m = 4, r = 19)`. -/
def rkmMkP_m4_r19_s2_p0 : List Bool := [
  false, false, true, true, true, true, false, false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 4, r = 19)`. -/
def rkmMkP_m4_r19_s3_p0 : List Bool := [
  false, true, false, false, true, false, true, false, true, false, false, true, true, false,
  true, true, false, true, true, true]
/-- Prefix-kick masks for `(m = 4, r = 19)`. -/
def rkmMasks_m4_r19 : List (List Bool) := [
  [], [true], rkmMkP_m4_r19_s2_p0, rkmMkP_m4_r19_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 19)`. -/
def rkmRow_m4_r19 : List ℕ := [
  22791, 26959, 4347, 650636, 8943374, 60368977, 491967029, 471937206, 1243232781, 1966208190,
  687747843, 7352157, 14722427, 1575817081, 10041352662, 5204613202, 7354971597, 220680560087,
  750189495393]
/-- Mask chunk for `(m = 4, r = 23)`. -/
def rkmMkP_m4_r23_s2_p0 : List Bool := [
  false, true, false, true, false, true, false, true, true, true, false, false, true, true, false,
  false, true, true, true]
/-- Mask chunk for `(m = 4, r = 23)`. -/
def rkmMkP_m4_r23_s3_p0 : List Bool := [
  true, false, true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 4, r = 23)`. -/
def rkmMasks_m4_r23 : List (List Bool) := [
  [], [true], rkmMkP_m4_r23_s2_p0, rkmMkP_m4_r23_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 23)`. -/
def rkmRow_m4_r23 : List ℕ := [
  45, 269, 205, 37828, 280047, 911263, 1963684, 403704, 581420, 746534, 28030940, 304185659,
  113853730, 3675138794, 2316676845, 1799564750, 605301525, 1196389348, 12685729357, 7542605338,
  5626802789, 235134610104, 728966185483]
/-- Mask chunk for `(m = 4, r = 64)`. -/
def rkmMkP_m4_r64_s3_p0 : List Bool := [
  true, false, true, true, true, true, true, true, true, true, false, true, true, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true]
/-- Mask chunk for `(m = 4, r = 64)`. -/
def rkmMkP_m4_r64_s4_p0 : List Bool := [
  false, true, true, false, false, true, true, true, true, true, false, false, false, true, true,
  false, false, false, true, true, true, false, false, false, false, false, false, true, true,
  true, false, true, true, false, true, true, true, true, false, false, false, true, true, true,
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, true]
/-- Mask chunk for `(m = 4, r = 64)`. -/
def rkmMkP_m4_r64_s5_p0 : List Bool := [
  false, false, false, false, false, false, true, false, false, true, false, true, true, false,
  true, false, true, false, true, false, false, false, false, false, false, true, false, true,
  true, false, false, true, false, false, true, false, false, true, false, false, true, true,
  false, true, true, false, false, true, true, true, true, false, false, false, true, true]
/-- Mask chunk for `(m = 4, r = 64)`. -/
def rkmMkP_m4_r64_s6_p0 : List Bool := [
  false, false, false, false, true, false, true, false, false, false, false, false, false, false,
  false, true, false, false, false, false, true, false, false, true, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, true, true, true, true, false, true, true, true,
  true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 4, r = 64)`. -/
def rkmMasks_m4_r64 : List (List Bool) := [
  [], [], [], rkmMkP_m4_r64_s3_p0, rkmMkP_m4_r64_s4_p0, rkmMkP_m4_r64_s5_p0, rkmMkP_m4_r64_s6_p0,
  []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 64)`. -/
def rkmRow_m4_r64 : List ℕ := [
  5581, 2476, 31561, 366076, 1179739, 2939717, 830695, 12497, 545987, 1157855, 295, 937022,
  1190491, 407956, 41719, 181292, 16971, 260756, 789211, 2283023, 1704331, 3475345, 66434676,
  219602815, 196925145, 101007547, 20012361, 70437, 8596760, 32778780, 19345665, 1474191, 877856,
  56707504, 197099362, 434637700, 489378253, 385307679, 52974110, 15232028, 110675120, 5928068,
  333226792, 382004102, 43972512, 32375152, 82178500, 400364, 764951006, 325773824, 2264242,
  1555233501, 10526341, 1625529410, 795895543, 481256607, 252805789, 2758919963, 1093376064,
  25897376955, 6315997922, 2719168874, 206925722597, 745167613641]
/-- Prefix-kick masks for `(m = 8, r = 19)`. -/
def rkmMasks_m8_r19 : List (List Bool) := [
  [false, false, false, false, false, false, true, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 19)`. -/
def rkmRow_m8_r19 : List ℕ := [
  13979163960, 73366723390, 222826692737, 248359604326, 375949800328, 60427773754, 4078119328,
  65007154]
/-- Mask chunk for `(m = 8, r = 36)`. -/
def rkmMkP_m8_r36_s3_p0 : List Bool := [
  false, false, false, false, true, false, false, false, true, false, false, true, true, false,
  false, true, true, false, false, true, true, false, false, true, true, false, false, true, true,
  false, false, true, true, true]
/-- Mask chunk for `(m = 8, r = 36)`. -/
def rkmMkP_m8_r36_s4_p0 : List Bool := [
  false, true, false, false, true, true, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true]
/-- Prefix-kick masks for `(m = 8, r = 36)`. -/
def rkmMasks_m8_r36 : List (List Bool) := [
  [], [], [], rkmMkP_m8_r36_s3_p0, rkmMkP_m8_r36_s4_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 36)`. -/
def rkmRow_m8_r36 : List ℕ := [
  0, 0, 1, 21, 0, 4, 18, 461, 737, 3940, 11746, 37108, 85947, 236582, 384737, 1079225, 1236177,
  4462135, 3748295, 19600138, 11246560, 87020547, 28510131, 414499292, 100024490, 2001341764,
  460949000, 9131081654, 2011251202, 27265495688, 3139899830, 625571821, 40862401777, 47211773,
  87759316620, 826023289674]
/-- Prefix-kick masks for `(m = 16, r = 9)`. -/
def rkmMasks_m16_r9 : List (List Bool) := [
  [true, true], [true, true, true, false, false, true, true],
  [true, false, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 9)`. -/
def rkmRow_m16_r9 : List ℕ := [
  143565, 1450894, 15922233, 90471611, 117256374, 877371176, 410500968, 35195311245, 963291553827]
/-- Prefix-kick masks for `(m = 32, r = 8)`. -/
def rkmMasks_m32_r8 : List (List Bool) := [
  [true, true, true], [true, false, true, true, false, false, true, true, true],
  [true, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 8)`. -/
def rkmRow_m32_r8 : List ℕ := [
  22667, 1219876, 357879, 26281382, 17474559, 119898243, 24906819817, 974927924884]
/-- Mask chunk for `(m = 32, r = 30)`. -/
def rkmMkP_m32_r30_s0_p0 : List Bool := [
  false, false, true, true, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, true,
  true]
/-- Mask chunk for `(m = 32, r = 30)`. -/
def rkmMkP_m32_r30_s1_p0 : List Bool := [
  false, false, false, false, true, false, true, false, true, false, true, false, true, false,
  true, true, false, true, true, false, false, true, true, true, true, true]
/-- Mask chunk for `(m = 32, r = 30)`. -/
def rkmMkP_m32_r30_s2_p0 : List Bool := [
  true, false, false, false, true, true, true, false, true, false, false, true, false, true,
  false, true, false, true, false, true, false, true, true, false, true, true, false, true, true]
/-- Prefix-kick masks for `(m = 32, r = 30)`. -/
def rkmMasks_m32_r30 : List (List Bool) := [
  rkmMkP_m32_r30_s0_p0, rkmMkP_m32_r30_s1_p0, rkmMkP_m32_r30_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 30)`. -/
def rkmRow_m32_r30 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 313, 623, 3722, 8336, 3066, 187716, 21950, 2467164, 691833, 38672850,
  62536011, 25297371, 105160330, 338596120, 2761040543, 865310295, 3037229262, 6982238170,
  67163566, 22841623747, 962871746494]
/-- Prefix-kick masks for `(m = 64, r = 13)`. -/
def rkmMasks_m64_r13 : List (List Bool) := [
  [false, false, false, false, true, true, false, false, true, true, true],
  [false, false, false, false, true, false, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 13)`. -/
def rkmRow_m64_r13 : List ℕ := [
  0, 0, 0, 0, 272, 2378, 207695, 1358117, 23875631, 13814166, 80065859, 14571678590, 985308997161]
/-- Mask chunk for `(m = 64, r = 23)`. -/
def rkmMkP_m64_r23_s0_p0 : List Bool := [
  false, true, true, true, true, false, false, true, true, false, true, true, false, false, true,
  true, false, false, true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 64, r = 23)`. -/
def rkmMasks_m64_r23 : List (List Bool) := [rkmMkP_m64_r23_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 23)`. -/
def rkmRow_m64_r23 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 151, 1977, 37706, 215854, 2642243, 8970241, 95774807,
  145027817, 1843565825, 51779308, 10122430572, 987729553191]
/-- Mask chunk for `(m = 64, r = 25)`. -/
def rkmMkP_m64_r25_s0_p0 : List Bool := [
  false, false, true, true, false, false, true, false, false, true, true, false, false, false,
  true, true, true, true, true, true, true]
/-- Mask chunk for `(m = 64, r = 25)`. -/
def rkmMkP_m64_r25_s1_p0 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, true, false, true, false, true,
  false, true, false, false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 64, r = 25)`. -/
def rkmMasks_m64_r25 : List (List Bool) := [rkmMkP_m64_r25_s0_p0, rkmMkP_m64_r25_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 25)`. -/
def rkmRow_m64_r25 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 55, 17, 12983, 103702, 3570155, 821914, 7009059, 139063343,
  29936357, 42714325, 1870844196, 9440467, 9786552875, 988109930182]
/-- Mask chunk for `(m = 64, r = 34)`. -/
def rkmMkP_m64_r34_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, true, true, false, false, true, true, true,
  true, false, false, true, true, false, false, true, true, false, false, true, true, false, true,
  true]
/-- Mask chunk for `(m = 64, r = 34)`. -/
def rkmMkP_m64_r34_s1_p0 : List Bool := [
  false, false, false, true, false, true, false, false, true, false, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, true, false, true,
  true, false, true, true]
/-- Prefix-kick masks for `(m = 64, r = 34)`. -/
def rkmMasks_m64_r34 : List (List Bool) := [rkmMkP_m64_r34_s0_p0, rkmMkP_m64_r34_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 34)`. -/
def rkmRow_m64_r34 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 23, 112, 451, 1540, 3758, 11032, 8371, 221718, 540063,
  9133793, 133668474, 19470474, 3981770, 1076601061, 82820651, 161011036, 3600675830, 175015879,
  9121459049, 985615374249]
/-- Mask chunk for `(m = 128, r = 20)`. -/
def rkmMkP_m128_r20_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, true, false, false, false,
  true, true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 20)`. -/
def rkmMasks_m128_r20 : List (List Bool) := [rkmMkP_m128_r20_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 20)`. -/
def rkmRow_m128_r20 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 319, 6692, 72943, 1659083, 9912729, 195753289, 47321191,
  8981065437, 990764207997]
/-- Mask chunk for `(m = 128, r = 27)`. -/
def rkmMkP_m128_r27_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, true, false, false, false, true, true, true]
/-- Mask chunk for `(m = 128, r = 27)`. -/
def rkmMkP_m128_r27_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, false, true, false, false, false, false, false, false, true, false, true, true]
/-- Mask chunk for `(m = 128, r = 27)`. -/
def rkmMkP_m128_r27_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, false, true, false, true, false, true, false, true, true, false, true]
/-- Prefix-kick masks for `(m = 128, r = 27)`. -/
def rkmMasks_m128_r27 : List (List Bool) := [
  rkmMkP_m128_r27_s0_p0, rkmMkP_m128_r27_s1_p0, rkmMkP_m128_r27_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 27)`. -/
def rkmRow_m128_r27 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 54, 50, 867, 85210, 1361230, 16488788, 2357480,
  44689597, 141739569, 486222940, 8558951237, 990748102368]
/-- Prefix-kick masks for `(m = 256, r = 3)`. -/
def rkmMasks_m256_r3 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 3)`. -/
def rkmRow_m256_r3 : List ℕ := [815255910, 53756659499, 945425036584]
/-- Prefix-kick masks for `(m = 256, r = 4)`. -/
def rkmMasks_m256_r4 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 4)`. -/
def rkmRow_m256_r4 : List ℕ := [788225, 398794737, 39581934038, 960018482966]
/-- Prefix-kick masks for `(m = 256, r = 9)`. -/
def rkmMasks_m256_r9 : List (List Bool) := [
  [false, false, false, true, true, true, true], [false, false, false, true, true, false, true],
  []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 9)`. -/
def rkmRow_m256_r9 : List ℕ := [0, 0, 0, 178, 58029, 392783, 26036, 17666483868, 982333038964]
/-- Mask chunk for `(m = 256, r = 15)`. -/
def rkmMkP_m256_r15_s0_p0 : List Bool := [
  true, true, true, true, true, true, true, false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 256, r = 15)`. -/
def rkmMasks_m256_r15 : List (List Bool) := [rkmMkP_m256_r15_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 15)`. -/
def rkmRow_m256_r15 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 8, 235, 1591, 497, 9388071, 143197237, 10812263106, 989035148985]
/-- Mask chunk for `(m = 256, r = 21)`. -/
def rkmMkP_m256_r21_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, false, false, true, true]
/-- Prefix-kick masks for `(m = 256, r = 21)`. -/
def rkmMasks_m256_r21 : List (List Bool) := [rkmMkP_m256_r21_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 21)`. -/
def rkmRow_m256_r21 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 25, 13732, 742174, 62621865, 449183662, 7921294257,
  991566143802]
/-- Prefix-kick masks for `(m = 256, r = 25)`. -/
def rkmMasks_m256_r25 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 25)`. -/
def rkmRow_m256_r25 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 32, 1786, 26870, 1282477, 16240230,
  942880842, 6813943342, 992225623806]
/-- Prefix-kick masks for `(m = 512, r = 40)`. -/
def rkmMasks_m512_r40 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 40)`. -/
def rkmRow_m512_r40 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  8, 614, 9077, 610701, 7102328, 645855888, 4154581708, 995191837553]
/-- Prefix-kick masks for `(m = 1024, r = 11)`. -/
def rkmMasks_m1024_r11 : List (List Bool) := [[true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 11)`. -/
def rkmRow_m1024_r11 : List ℕ := [
  0, 0, 0, 0, 0, 0, 562, 5276, 35138727, 14060796075, 985904059076]
/-- Prefix-kick masks for `(m = 1024, r = 17)`. -/
def rkmMasks_m1024_r17 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 17)`. -/
def rkmRow_m1024_r17 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 621, 299072, 323082, 9123177496, 990876199162]
/-- Prefix-kick masks for `(m = 1024, r = 18)`. -/
def rkmMasks_m1024_r18 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 18)`. -/
def rkmRow_m1024_r18 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 497, 362099, 13347, 8627381784, 991372241645]
/-- Mask chunk for `(m = 1024, r = 128)`. -/
def rkmMkP_m1024_r128_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 1024, r = 128)`. -/
def rkmMkP_m1024_r128_s1_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 1024, r = 128)`. -/
def rkmMkP_m1024_r128_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 1024, r = 128)`. -/
def rkmMkP_m1024_r128_s2_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, true, false, false, true, false, true, false, true, true]
/-- Prefix-kick masks for `(m = 1024, r = 128)`. -/
def rkmMasks_m1024_r128 : List (List Bool) := [
  [], rkmMkP_m1024_r128_s1_p0 ++ rkmMkP_m1024_r128_s1_p1,
  rkmMkP_m1024_r128_s2_p0 ++ rkmMkP_m1024_r128_s2_p1, []]
/-- Row chunk `0` `(m = 1024, r = 128)`. -/
def rkmRowP_m1024_r128_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Row chunk `1` `(m = 1024, r = 128)`. -/
def rkmRowP_m1024_r128_p1 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 9, 1015, 27870, 19739,
  17450844, 3576136, 127253484, 1636362560, 998215283753]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 128)`. -/
def rkmRow_m1024_r128 : List ℕ := rkmRowP_m1024_r128_p0 ++ rkmRowP_m1024_r128_p1
/-- Unpacks `j` LSB-first bits of `< 2 ^ 50` word `w` (`FindAllJohnsonRampKickMuxTraj02`). -/
def rkmWbTraj02 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWbTraj02 j (Nat.div w 2)
/-- Concatenates `50`-bit `< 2 ^ 50` chunks (final length `rem`) into a `List Bool` mask. -/
def rkmMaskWordsTraj02 : ℕ → List ℕ → List Bool
  | _, [] => []
  | rem, [w] => rkmWbTraj02 rem w
  | rem, w :: v :: ws => rkmWbTraj02 50 w ++ rkmMaskWordsTraj02 rem (v :: ws)
/-- Krotov masks `(m = 8, r = 128)`. -/
def rkmMasksPack_m8_r128 : List (List Bool) := [[],[],rkmWbTraj02 3 5,
  rkmMaskWordsTraj02 15 [3945219,16432],rkmMaskWordsTraj02 15 [571187565561034,142143288,25088],
  rkmMaskWordsTraj02 10 [375116715350128,443183065624007,967],
  rkmMaskWordsTraj02 26 [71320555046761,375295590486057,53700309],[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 128)`. -/
def rkmRowPack_m8_r128 : List ℕ := [15894,177144,313551,155212,37049,4382,321817,1232039,157845,
  234979,639951,1322119,814387,234490,656,3916429,32368,1186598,7175088,1263410,161016,1022520,
  70512,4309886,1020571,210757,1905116,4790475,3337727,1380,776150,7072331,310933,2456655,36964,
  3163272,1188623,557,13414890,4838855,3179295,3284388,1626769,9733921,345123,6147190,248055,
  260497,86,99041,2025627,418266,1841026,1803787,3549555,1195316,529391,151441,1061038,10283525,
  24872125,7173773,4438663,9024937,5966101,2380445,14995118,558556,135361,3886733,11340396,
  15267205,129739,32812976,4881,1942943,1442055,10858440,3205275,6057460,34388871,130526515,
  106720204,17351816,44293768,52421132,30155565,795931,13946680,4837954,2259332,176679246,
  57039242,5921631,488386611,212279617,32601072,592946029,704081606,7957858,519996126,825963215,
  51147683,1985900143,44940371,35699676,139624155,1087014406,575866699,19604735,1648262589,
  52162956,1214867828,569433462,1071777147,2004741316,813151746,1886831774,802878270,2327859590,
  1151090958,5777686818,2877340067,8820296939,29583689565,3151240949,86433129906,841538589579]
/-- Krotov masks `(m = 2, r = 3)`. -/
def rkmMasksPack_m2_r3 : List (List Bool) := [[],rkmWbTraj02 2 3,[],[]]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 3)`. -/
def rkmRowPack_m2_r3 : List ℕ := [90076905,277287989537,717222031267]
/-- Krotov masks `(m = 64, r = 96)`. -/
def rkmMasksPack_m64_r96 : List (List Bool) := [rkmWbTraj02 13 7680,[],
  rkmMaskWordsTraj02 11 [263882790667202,1098],rkmMaskWordsTraj02 12 [1117748984538673,3487],
  rkmMaskWordsTraj02 17 [8003175715071,81920],rkmMaskWordsTraj02 23 [640046032487751,5265016],
  rkmMaskWordsTraj02 14 [844111313625027,12350],[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 96)`. -/
def rkmRowPack_m64_r96 : List ℕ := [0,5,0,1,1,0,0,0,0,0,32,0,46,38,0,28,53,16,154,1,12334,999,
  1126,213298,4250171,9254521,912459,26768240,62536222,56360646,10600480,22109652,3669495,1779005,
  50058724,1868638,1239762,20261976,6713203,13386880,2387219,38537320,21474120,2347553,186571665,
  13282619,78367978,118316502,23448194,10806585163,25044623,84203943151,1971866750,39457418035,
  431946487126,75236378587,4389953672,243367756887,535088924,95717873262,491342,11157045198,
  47120376,351984718,4635262,2675912,819637,88309,7360,88,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0]
/-- Krotov masks `(m = 2, r = 6)`. -/
def rkmMasksPack_m2_r6 : List (List Bool) := [[],[],rkmWbTraj02 2 3,rkmWbTraj02 3 5,rkmWbTraj02 4 9,
  [],rkmWbTraj02 4 9,[]]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 6)`. -/
def rkmRowPack_m2_r6 : List ℕ := [13963795,39277662,11607151,570863735,426895074254,572465454208]
/-- Krotov masks `(m = 64, r = 44)`. -/
def rkmMasksPack_m64_r44 : List (List Bool) := [rkmWbTraj02 43 7066413826048,
  rkmWbTraj02 36 48506863616,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 44)`. -/
def rkmRowPack_m64_r44 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,41,1590,5374,387,5484,
  9716,29933,139465,2933,41915,1034612,375787,9106999,45538245,2555434,64674706,215632582,
  125306326,2610105087,178803622,12710549697,8887979793,10281926973,964866171877]
/-- Krotov masks `(m = 16, r = 7)`. -/
def rkmMasksPack_m16_r7 : List (List Bool) := [[],[],[],rkmWbTraj02 2 2,rkmWbTraj02 3 4,
  rkmWbTraj02 5 26,rkmWbTraj02 6 33,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 7)`. -/
def rkmRowPack_m16_r7 : List ℕ := [214993,5955018,58069442,118383446,336391158,36144110675,
  963336791694]
/-- Krotov masks `(m = 8, r = 44)`. -/
def rkmMasksPack_m8_r44 : List (List Bool) := [[],[],rkmWbTraj02 7 65,rkmWbTraj02 44 17592178065467,
  rkmWbTraj02 42 3515736070874,rkmWbTraj02 40 731389745152,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 44)`. -/
def rkmRowPack_m8_r44 : List ℕ := [83880,175853,1963884,4325857,1115437,10330,3667301,2564126,
  1354953,7062581,85664,22692756,1825592,78,204172,32508089,8986285,2866800,6392276,14908077,
  7889893,6191358,44550234,33386407,2905838,135174943,103040788,2622610,260681729,14334986,
  103750208,17760901,36286941,3361412169,6586859,6438958578,783079,12297318819,2807114164,
  569629099,36918264405,236384081,86441307027,850040869514]
/-- Krotov masks `(m = 2, r = 9)`. -/
def rkmMasksPack_m2_r9 : List (List Bool) := [[],[],rkmWbTraj02 3 6,rkmWbTraj02 5 25,
  rkmWbTraj02 7 105,rkmWbTraj02 7 75,rkmWbTraj02 7 68,[]]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 9)`. -/
def rkmRowPack_m2_r9 : List ℕ := [133984826,71985,20303119,4076142482,8558999954,33886944,
  4788560869,448360867975,533975021727]
/-- Krotov masks `(m = 16, r = 35)`. -/
def rkmMasksPack_m16_r35 : List (List Bool) := [[],rkmWbTraj02 32 2214592570,
  rkmWbTraj02 28 242468990,rkmWbTraj02 33 6755273402,rkmWbTraj02 34 9462779138,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 35)`. -/
def rkmRowPack_m16_r35 : List ℕ := [37,364,1918,940,1099,5371,236,28637,30854,76765,1697250,
  2491533,10409619,3233183,1688441,5932170,18549232,19314603,16234005,23902595,284989522,
  207265792,455165251,635299532,744240940,2662326185,722633223,412400929,2450269440,3121941647,
  164404936,15257475932,20986386,47702351164,925054649290]
/-- Krotov masks `(m = 4, r = 18)`. -/
def rkmMasksPack_m4_r18 : List (List Bool) := [[],[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 18)`. -/
def rkmRowPack_m4_r18 : List ℕ := [103989991,212965112,37733674,426721936,84628201,5323704392,
  277181148,52513326855,257325787417,364251723371,231222480721,74344677494,12385025939,1025212296,
  37236638,427650]
/-- Krotov masks `(m = 16, r = 32)`. -/
def rkmMasksPack_m16_r32 : List (List Bool) := [[],rkmWbTraj02 32 2181038922,
  rkmWbTraj02 24 14766483,rkmWbTraj02 30 862822585,rkmWbTraj02 31 1074894704,
  rkmWbTraj02 31 1074230115,rkmWbTraj02 16 37408,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 32)`. -/
def rkmRowPack_m16_r32 : List ℕ := [2066,37072,242247,63504,42845,75083,370791,19559,1140,1956231,
  1373909,28582,19634713,7458815,7965851,11043266,76151151,83645742,841973348,7848051,448973642,
  192629867,299661358,833795431,23196080,1916193289,151333016,1384275219,15470014401,317950,
  38651056401,939568602138]
/-- Krotov masks `(m = 64, r = 11)`. -/
def rkmMasksPack_m64_r11 : List (List Bool) := [rkmWbTraj02 9 460,rkmWbTraj02 10 596,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 11)`. -/
def rkmRowPack_m64_r11 : List ℕ := [0,0,32,530,56736,499756,11606458,5591650,60742082,16609193274,
  983312309355]
/-- Krotov masks `(m = 64, r = 28)`. -/
def rkmMasksPack_m64_r28 : List (List Bool) := [rkmWbTraj02 26 52428799,rkmWbTraj02 28 268435454,
  rkmWbTraj02 14 11625,rkmWbTraj02 21 1852363,rkmWbTraj02 25 26917753,rkmWbTraj02 26 39260445,
  rkmWbTraj02 27 68495299,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 28)`. -/
def rkmRowPack_m64_r28 : List ℕ := [2,0,0,3,35,3,29,165,414,1229,0,1359,71,12,753,303,204916,
  57967,8803925,45434,13449982,22039857,2392,100221984,184315127,155271983,9477160886,
  990038420664]
/-- Krotov masks `(m = 4, r = 21)`. -/
def rkmMasksPack_m4_r21 : List (List Bool) := [[],[],rkmWbTraj02 12 4085,rkmWbTraj02 14 12288,
  rkmWbTraj02 2 2,rkmWbTraj02 19 262162,rkmWbTraj02 18 131072,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 21)`. -/
def rkmRowPack_m4_r21 : List ℕ := [525023466,91392438,14302,121139793,2051831738,83628613771,
  295232675493,355243655151,197654834814,56296384247,8377197891,589384550,13608360,122963,508,0,0,
  0,0,0,0]
/-- Krotov masks `(m = 32, r = 26)`. -/
def rkmMasksPack_m32_r26 : List (List Bool) := [rkmWbTraj02 26 67104381,rkmWbTraj02 23 7550058,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 26)`. -/
def rkmRowPack_m32_r26 : List ℕ := [23,35,19,638,97,1889,26378,68017,337194,1242774,5445334,
  18659367,60159748,163058445,344027715,504414603,378930691,15483206,583399654,3009816341,
  3639669214,771107219,7611131318,27090077790,22066898395,933736043412]
/-- Krotov masks `(m = 2, r = 18)`. -/
def rkmMasksPack_m2_r18 : List (List Bool) := [[],[],[],[]]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 18)`. -/
def rkmRowPack_m2_r18 : List ℕ := [72070,297177,860,257774,13911236,899835,332028689,42629235,
  3030974908,3217438036,8132015538,38255694211,111669427,179478577329,421574398145,275993127790,
  65099135338,4716871212]
/-- Krotov masks `(m = 32, r = 23)`. -/
def rkmMasksPack_m32_r23 : List (List Bool) := [[],rkmWbTraj02 23 8388607,rkmWbTraj02 3 7,
  rkmWbTraj02 17 110636,rkmWbTraj02 19 470153,rkmWbTraj02 21 1787317,rkmWbTraj02 22 2132698,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 23)`. -/
def rkmRowPack_m32_r23 : List ℕ := [0,0,0,1,16,185,151,94,2515,5106,1951230,561775,2507488,
  21606143,94100180,620424206,19567,4906670,148917072,1839181517,186337805,20633902876,
  976445575124]
/-- Krotov masks `(m = 8, r = 25)`. -/
def rkmMasksPack_m8_r25 : List (List Bool) := [[],[],rkmWbTraj02 16 49234,rkmWbTraj02 17 114692,
  rkmWbTraj02 20 720938,rkmWbTraj02 21 1310871,rkmWbTraj02 22 2097506,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 25)`. -/
def rkmRowPack_m8_r25 : List ℕ := [11803,5569220,9964723,26428045,1140261,210086898,11955371,
  123033000,14553227106,126425920566,305747697476,321111120811,172305163096,50321230126,
  8405084387,712033565,29968846,241953,851,0,0,0,0,0,0]
/-- Krotov masks `(m = 64, r = 23)`. -/
def rkmMasksPack_m64_r23 : List (List Bool) := [rkmWbTraj02 22 3375104,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 23)`. -/
def rkmRowPack_m64_r23 : List ℕ := [0,0,0,0,0,0,0,0,0,1,80,4204,37561,157442,598374,1977338,
  9827257,97476008,151391309,1871257765,40123203,10152141822,987675007255]
/-- Krotov masks `(m = 32, r = 14)`. -/
def rkmMasksPack_m32_r14 : List (List Bool) := [[],[],rkmWbTraj02 5 29,rkmWbTraj02 10 869,
  rkmWbTraj02 12 3501,rkmWbTraj02 9 344,rkmWbTraj02 13 4178,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 14)`. -/
def rkmRowPack_m32_r14 : List ℕ := [984,1367,32875,8599,129,310307,10953647,2187407,709228,
  118063585,265105136,239633059,18652674869,980710318679]
/-- Krotov masks `(m = 8, r = 20)`. -/
def rkmMasksPack_m8_r20 : List (List Bool) := [[],rkmWbTraj02 7 98,rkmWbTraj02 14 14741,
  rkmWbTraj02 18 206249,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 20)`. -/
def rkmRowPack_m8_r20 : List ℕ := [215380,1494,2064050,24358318,3202237,5722618,10724231,
  501626696,463307925,78136611,1805019659,2665014,1290489138,1267896555,86036200,2075110348,
  18520959113,13041024831,91539366445,869281846118]
/-- Krotov masks `(m = 64, r = 17)`. -/
def rkmMasksPack_m64_r17 : List (List Bool) := [[],[],rkmWbTraj02 4 15,rkmWbTraj02 10 899,
  rkmWbTraj02 13 7888,rkmWbTraj02 15 27840,rkmWbTraj02 16 35378,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 17)`. -/
def rkmRowPack_m64_r17 : List ℕ := [0,1,0,29,0,92,215,74,79,1342387,804264,343422,34019411,
  40947125,110191072,12044374071,987767977565]
/-- Cumulative `2`-lane trajectory head invariant (`Traj00` -> `Traj02`). -/
def rkmTrajLaneProp_02 : Prop :=
  (rkmRow_m2_r14.head? = some 34432848) ∧ (rkmRow_m2_r5.head? = some 1826712739)
/-- Proof of `rkmTrajLaneProp_02` in `O(1)` kernel steps. -/
theorem rkmTrajLaneOk_02 : rkmTrajLaneProp_02 :=
  ⟨rfl, rfl⟩
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
private def wc_rkmTraj_m1024_r128_s0_hb : List ℕ := pCat [130279067563891, 183431684190765,
  223661393416083, 257109161272402, 286164402794576, 312057734562293, 335523159522429,
  357040788985875, 376945367284136, 395481506866570, 412834517712233, 429148851899059,
  444539754615727, 459100952953569, 472909916092977, 486031564394717, 498520952914918,
  510425256434595, 521785266433370, 532636539323628, 543010290527757, 552934100053253,
  562432476050438, 571527309853353, 580238247035856, 588582992709539, 596577564785021,
  604236505652017, 611573060333525, 618599327383952, 625326387457498, 631764413451412,
  637922765344173, 643810072240632, 649434303660955, 654802831735827, 659922485673190,
  664799599624318, 669440054885849, 673849317219671, 678032469946529, 681994243365942,
  685739040970022, 689270962848423, 692593826623074, 695711186202494, 698626348604351,
  701342389060357, 703862164588205, 706188326190368, 708323329818214, 710269446221653,
  712028769788762, 713603226466226, 714994580839558, 716204442441732, 717234271349754,
  718085383120662, 718758953111313, 719256020219902, 719577490081399, 719724137743818,
  719696609847425, 719495426324461] [719120981632786, 718573545532757, 717853263412836,
  716960156165541, 715894119611613, 714654923466394, 713242209838511, 711655491246836,
  709894148137387, 707957425877227, 705844431197396, 703554128051494, 701085332850480,
  698436709027582, 695606760879682, 692593826623074, 689396070591847, 686011474496145,
  682437827644887, 678672716022948, 674713510095836, 670557351195183, 666201136315249,
  661641501123471, 656874800956063, 651897089531594, 646704095070225, 641291193452059,
  635653377982890, 629785225256888, 623680856510113, 617333893741959, 610737409738198,
  603883870952126, 596765071980091, 589372060092055, 581695047930586, 573723312050709,
  565445074408780, 556847363180169, 547915848336854, 538634646168168, 528986085269108,
  518950424290389, 508505508708425, 497626349685030, 486284602222676, 474447911478661,
  462079084020508, 449135022963876, 435565339005122, 421310507707178, 406299377163997,
  390445721485531, 373643350640132, 355758959104517, 336621284069477, 316003933740607,
  293596671782201, 268953944868483, 241393702116129, 209770988247212, 171859959480257,
  121932894880562]
private def wc_rkmTraj_m1024_r128_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTraj_m1024_r128_s0_v1 : List ℕ := pCat [2015641832868732, 2045944233954032,
  2095001357610916, 2159676031338279, 2231378577086329, 2298524731450865, 2349994559804434,
  2378154040561540, 2380421709852971, 2359133244782648, 2320126716474724, 2270789040595580,
  2218257590272373, 2168203059304653, 2124307419090531, 2088318753623789, 2060457733942933,
  2039950895988321, 2025527721958403, 2015796536764520, 2009478948829959, 2005522452714023,
  2003127169979420, 2001722854331614, 2000924303401259, 2000483288956365, 2000246463686112,
  2000122674284013, 2000059632859271, 2000028327280879, 2000013156722639, 2000005977686830,
  2000002658058004, 2000001157258729, 2000000493522437, 2000000206232642, 2000000084476226,
  2000000033929732, 2000000013366816, 2000000005166552, 2000000001959811, 2000000000729752,
  2000000000266797, 2000000000095788, 2000000000033778, 2000000000011699, 2000000000003976,
  2000000000001325, 2000000000000432, 2000000000000136, 2000000000000040, 2000000000000009,
  2000000000000001, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
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
private def wc_rkmTraj_m1024_r128_s0_v2 : List ℕ := pCat [2000000030907845, 2000000196652433,
  2000000880709105, 2000003205708201, 2000010058569495, 2000028097615304, 2000071313834042,
  2000166783038100, 2000363133562560, 2000741860090293, 2001430872646512, 2002618606191236,
  2004565789785994, 2007610887836775, 2012164683176642, 2018689878332425, 2027663217223177,
  2039520473185452, 2054588353492734, 2073011234611247, 2094683747546680, 2119201662351444,
  2145842619976389, 2173584854615865, 2201166557118536, 2227181909299386, 2250203371375460,
  2268914869314085, 2282238158149694, 2289435342704409, 2290174172799571, 2284548542438134,
  2273053445185658, 2256520172928631, 2236022652163789, 2212768734689904, 2187990739984536,
  2162847814373827, 2138349329654928, 2115304388980159, 2094298345826446, 2075693730241401,
  2059650530541713, 2046159545371626, 2035082412530865, 2026192685397328, 2019213634630989,
  2013849971276284, 2009812143311652, 2006833064517111, 2004677998839008, 2003148832222830,
  2002084161436586, 2001356591525242, 2000868444890297, 2000546822673497, 2000338683296049,
  2000206353741809, 2000123687829724, 2000072938849605, 2000042318086967, 2000024156990176,
  2000013568145256, 2000007498370882] (pCat [2000004077432406, 2000002181631762, 2000001148547916,
  2000000594955798, 2000000303235371, 2000000152062797, 2000000075023805, 2000000036415804,
  2000000017388960, 2000000008168173, 2000000003774111, 2000000001715180, 2000000000766607,
  2000000000336940, 2000000000145615, 2000000000061867, 2000000000025835, 2000000000010600,
  2000000000004268, 2000000000001683, 2000000000000648, 2000000000000241, 2000000000000085,
  2000000000000028, 2000000000000007, 2000000000000001, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m1024_r128_s0_ck3 : List ℕ := pCat [2000000000000000, 2000000000000002,
  2000000000000001, 2000000000000007, 2000000000000007, 2000000000000011, 2000000000000048,
  2000000000000181, 2000000000000668, 2000000000002383, 2000000000008051, 2000000000025843,
  2000000000079083, 2000000000231271, 2000000000648331, 2000000001746542, 2000000004531219,
  2000000011343205, 2000000027445838, 2000000064282168, 2000000145935865, 2000000321526174,
  2000000688220742, 2000001432604904, 2000002902711751, 2000005729514319, 2000011025435690,
  2000020698494253, 2000037933593374, 2000067905868910, 2000118802441021, 2000203234479273,
  2000340115827884, 2000557061055975, 2000893307895772, 2001403090933638, 2002159282582882,
  2003256976746734, 2004816530906810, 2006985423715643, 2009938157009034, 2013873370237239,
  2019007380902566, 2025563551117760, 2033757228383116, 2043776515419733, 2055759756123589,
  2069771315576079, 2085777884521523, 2103628036386494, 2123037989760967, 2143586384109412,
  2164720308097010, 2185773837815268, 2205999028170501, 2224607805426270, 2240821734232834,
  2253925401358597, 2263318376969532, 2268560533859528, 2269405990703363, 2265822059682373,
  2257991183328609, 2246295721591567] (pCat [2231287335264078, 2213644343581381, 2194121593839735,
  2173497930327789, 2152526248538440, 2131890428043486, 2112172296047562, 2093830378960944,
  2077190763335121, 2062449103185138, 2049681823985324, 2038863966875038, 2029890905431945,
  2022601308950983, 2016799136068516, 2012273015387695, 2008811999269652, 2006217272294524,
  2004309891754829, 2002934997893131, 2001963147822638, 2001289512182804, 2000831654499726,
  2000526522954972, 2000327155368580, 2000199458216678, 2000119289589958, 2000069966448177,
  2000040233656779, 2000022676107129, 2000012522303735, 2000006773043766, 2000003586769884,
  2000001858947542, 2000000942509176, 2000000467256478, 2000000226389896, 2000000107140574,
  2000000049498283, 2000000022309414, 2000000009802723, 2000000004196018, 2000000001748238,
  2000000000708338, 2000000000278815, 2000000000106496, 2000000000039417, 2000000000014114,
  2000000000004877, 2000000000001618, 2000000000000512, 2000000000000151, 2000000000000040,
  2000000000000007, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m1024_r128_s0_ck4 : List ℕ := pCat [2000000000000000, 2000000000000002,
  2000000000000000, 1999999999999999, 2000000000000003, 2000000000000002, 2000000000000002,
  1999999999999992, 1999999999999997, 1999999999999997, 2000000000000003, 2000000000000003,
  2000000000000008, 2000000000000006, 1999999999999997, 1999999999999998, 2000000000000005,
  2000000000000003, 2000000000000002, 1999999999999999, 2000000000000003, 2000000000000003,
  2000000000000011, 2000000000000010, 2000000000000006, 2000000000000013, 2000000000000014,
  2000000000000010, 2000000000000012, 2000000000000014, 2000000000000013, 2000000000000019,
  2000000000000017, 2000000000000040, 2000000000000081, 2000000000000205, 2000000000000524,
  2000000000001387, 2000000000003633, 2000000000009376, 2000000000023734, 2000000000058909,
  2000000000143404, 2000000000342395, 2000000000801854, 2000000001842338, 2000000004153509,
  2000000009189685, 2000000019956942, 2000000042545985, 2000000089053847, 2000000183033336,
  2000000369437370, 2000000732369284, 2000001426066152, 2000002727766589, 2000005125859578,
  2000009463428363, 2000017166404994, 2000030597260618, 2000053589280295, 2000092232072983,
  2000155993977642, 2000259277820228] (pCat [2000423507550911, 2000679827192621, 2001072451259132,
  2001662627920786, 2002533054864236, 2003792419724403, 2005579527148737, 2008066240122747,
  2011458236488622, 2015992411075952, 2021929701349542, 2029542247526566, 2039094177106707,
  2050815964523842, 2064873251221012, 2081332151430824, 2100124276705007, 2121015785994302,
  2143585464466461, 2167216908990872, 2191109160428536, 2214308493179451, 2235761631020747,
  2254387667423599, 2269162857455094, 2279209754766202, 2283880441157423, 2282823283275770,
  2276023979815190, 2263814566924765, 2246848148651776, 2226041769228734, 2202494254588757,
  2177389244219874, 2151895411638545, 2127075740563154, 2103815762527823, 2082777296264513,
  2064380132728812, 2048810048883523, 2036048202486541, 2025914842865457, 2018119563989903,
  2012310927428149, 2008119863379909, 2005193360299237, 2003217109794273, 2001927603845441,
  2001115454107178, 2000622348210905, 2000334142151177, 2000172264490806, 2000085061643580,
  2000040111955123, 2000018001956104, 2000007657482497, 2000003071898077, 2000001155049812,
  2000000403890770, 2000000129997386, 2000000037976131, 2000000009866018, 2000000002207112,
  2000000000400842] [2000000000051166])
private def wc_rkmTraj_m1024_r128_s0_ck5 : List ℕ := pCat [2000000000000000, 2000000000000002,
  2000000000000000, 1999999999999999, 2000000000000000, 2000000000000000, 2000000000000006,
  2000000000000003, 1999999999999997, 2000000000000002, 2000000000000000, 2000000000000001,
  1999999999999993, 2000000000000001, 1999999999999995, 2000000000000009, 2000000000000015,
  2000000000000003, 1999999999999992, 2000000000000001, 2000000000000005, 2000000000000006,
  2000000000000002, 1999999999999995, 1999999999999996, 1999999999999991, 1999999999999987,
  1999999999999994, 2000000000000009, 2000000000000011, 2000000000000013, 1999999999999997,
  1999999999999988, 2000000000000001, 2000000000000011, 2000000000000005, 1999999999999994,
  2000000000000001, 2000000000000015, 2000000000000002, 2000000000000000, 2000000000000000,
  1999999999999997, 1999999999999998, 2000000000000004, 2000000000000009, 2000000000000013,
  1999999999999997, 1999999999999993, 2000000000000009, 2000000000000021, 2000000000000008,
  2000000000000007, 2000000000000020, 2000000000000009, 2000000000000000, 2000000000000009,
  2000000000000014, 2000000000000012, 2000000000000011, 2000000000000016, 2000000000000022,
  2000000000000025, 2000000000000015] (pCat [2000000000000013, 2000000000000012, 2000000000000022,
  2000000000000030, 2000000000000034, 2000000000000032, 2000000000000045, 2000000000000092,
  2000000000000232, 2000000000000727, 2000000000002310, 2000000000007238, 2000000000022266,
  2000000000066957, 2000000000196584, 2000000000563132, 2000000001574012, 2000000004292761,
  2000000011423357, 2000000029660236, 2000000075139684, 2000000185720844, 2000000447839890,
  2000001053469201, 2000002417215690, 2000005409438566, 2000011805158411, 2000025119117977,
  2000052103879283, 2000105336421257, 2000207505004909, 2000398205351288, 2000744198189194,
  2001354048622657, 2002397677620008, 2004130374088170, 2006919016145173, 2011265526799512,
  2017819129622983, 2027365450921085, 2040778240703600, 2058920336145295, 2082486539247704,
  2111793781945151, 2146543012103245, 2185599483633512, 2226857036160821, 2267258446893918,
  2303029091459519, 2330140301977364, 2344955943766741, 2344945829605019, 2329296670386800,
  2299241046323306, 2257973615210496, 2210127572499778, 2160915057427198, 2115147007276401,
  2076394926455581, 2046514404337685, 2025629270209154, 2012522118641290, 2005253256116991,
  2001784195444953] [2000424893021535])
private def wc_rkmTraj_m1024_r128_s0_ck6 : List ℕ := pCat [2000000000000000, 2000000000000002,
  1999999999999999, 2000000000000007, 1999999999999998, 1999999999999995, 2000000000000001,
  2000000000000002, 1999999999999999, 1999999999999992, 2000000000000002, 2000000000000010,
  2000000000000003, 1999999999999992, 1999999999999993, 1999999999999996, 2000000000000002,
  1999999999999991, 2000000000000002, 2000000000000000, 2000000000000001, 2000000000000006,
  2000000000000011, 2000000000000001, 1999999999999993, 1999999999999988, 1999999999999994,
  2000000000000014, 2000000000000023, 2000000000000005, 1999999999999994, 1999999999999999,
  1999999999999984, 1999999999999984, 2000000000000005, 2000000000000016, 2000000000000007,
  1999999999999989, 1999999999999997, 2000000000000004, 2000000000000016, 2000000000000006,
  1999999999999979, 1999999999999982, 2000000000000023, 2000000000000032, 1999999999999999,
  1999999999999993, 2000000000000011, 1999999999999989, 1999999999999975, 1999999999999984,
  2000000000000008, 2000000000000010, 1999999999999983, 1999999999999989, 2000000000000017,
  2000000000000013, 1999999999999993, 1999999999999998, 2000000000000002, 1999999999999991,
  2000000000000001, 2000000000000006] (pCat [2000000000000016, 2000000000000013, 1999999999999998,
  1999999999999986, 1999999999999991, 2000000000000010, 2000000000000019, 1999999999999997,
  1999999999999989, 2000000000000001, 2000000000000013, 1999999999999996, 1999999999999991,
  2000000000000006, 2000000000000008, 2000000000000014, 2000000000000020, 2000000000000015,
  2000000000000001, 1999999999999994, 1999999999999997, 2000000000000022, 2000000000000030,
  2000000000000006, 2000000000000012, 2000000000000020, 2000000000000008, 2000000000000009,
  2000000000000019, 2000000000000022, 2000000000000031, 2000000000000032, 2000000000000023,
  2000000000000037, 2000000000000029, 2000000000000028, 2000000000000031, 2000000000000037,
  2000000000000043, 2000000000000052, 2000000000000016, 1999999999999939, 2000000000000010,
  2000000000002344, 2000000000009703, 1999999999992052, 1999999999763956, 1999999999126274,
  2000000000872894, 2000000021947514, 2000000089726516, 2000000014766939, 1999998282340999,
  1999990172043307, 1999976778015427, 2000051322393055, 2000790119471045, 2004465300324698,
  2017715557637863, 2055199936782664, 2139880107445425, 2289848044712623, 2483129632482209,
  2617333625383360] [2527754847665303])
private def wc_rkmTraj_m4_r64_s4_hb : List ℕ := [201729188212026, 281508043824594,
  340143806106307, 387413505713179, 427156287810569, 461366543003025, 491243800487119,
  517579092031539, 540928360066966, 561701044075360, 580209705045267, 596699820859299,
  611368673402921, 624377855462687, 635861855817297, 645934132432115, 654691520040627,
  662217500032230, 668584673019807, 673856659910690, 678089585102579, 681333248639369,
  683632063090479, 685025809823890, 685550254736119, 685237653201920, 684117166620099,
  682215207550634, 679555726457728, 676160450083708, 672049079197179, 667239451686798,
  661747675567247, 655588235321935, 648774074048592, 641316653036998, 633225989640445,
  624510673557247, 615177860869260, 605233244340611, 594680997501822, 583523688856301,
  571762161045881, 559395367857673, 546420159342100, 532831001741655, 518619613950354,
  503774495141556, 488280307926753, 472117066186394, 455259053649702, 437673363473783,
  419317891851074, 400138524357044, 380065092566721, 359005391205296, 336836008175298,
  313387651006612, 288420370055705, 261578736389332, 232302959421605, 199628323358047,
  161633262888093, 113259287742954]
private def wc_rkmTraj_m4_r64_s4_v0 : List ℕ := [1999965757155805, 2000056593002502,
  1999956984295801, 1999994308732599, 1999997238238466, 1999928694629310, 1999834053558304,
  1999802873825091, 1999863452065711, 1999964134947823, 1999881384835596, 2000542114543904,
  2001329324693221, 2001300500731969, 2003658987477962, 2021302388697602, 2060882880462610,
  2127800505497104, 2217635017151207, 2314040827656678, 2393354216546027, 2434241840983148,
  2426908786924651, 2376542884536346, 2299594886731962, 2215898143163095, 2141334887894718,
  2084228199989733, 2045759805540459, 2022681174420388, 2010258480543822, 2004232235559562,
  2001591127752797, 2000544245695001, 2000168981351643, 2000047475910569, 2000012019569953,
  2000002727092983, 2000000550479574, 1999999902110746, 1999999984874484, 2000000001990188,
  2000000000215926, 2000000000018210, 2000000000001032]
private def wc_rkmTraj_m4_r64_s4_v1 : List ℕ := pCat [1999771824970760, 1999693887678781,
  1999865164560313, 2000135786299217, 2000195140886374, 1999974055744501, 1999776864722264,
  1999892750544765, 2000179245215053, 2000225298781696, 1999922972095959, 1999657692364104,
  1999808404008656, 2000208756606546, 2000328987906368, 1999973468824214, 1999573637878737,
  1999660971313648, 2000180166042309, 2000525934503777, 2000269407825860, 1999682495521470,
  1999427755754262, 1999795492733145, 2000389318117865, 2000593938877656, 2000237486193307,
  1999687781679523, 1999369367653898, 1999408207898735, 1999831597497783, 2000777114767860,
  2001963083744305, 2001965939133495, 1999051895546094, 1993988557574234, 1991856890426832,
  1998771464464190, 2014070490456446, 2025526169648307, 2015787816407696, 1978733484802874,
  1932546138679031, 1915250355964679, 1961887955266397, 2079031384366276, 2236182313529195,
  2380836329724958, 2466191512795276, 2472762551005155, 2412157659884984, 2314909780953804,
  2213185040312709, 2128672396303838, 2069462717630420, 2033568670435521, 2014505844040173,
  2005587581181978, 2001908264197593, 2000573045271188, 2000149443223332, 2000033206457153,
  2000006093820456, 2000000871531086] [2000000084184425]
private def wc_rkmTrajPack_m8_r128_s4_hb : List ℕ := pCat [164797529548626, 231339260588612,
  281225396792933, 322299049406879, 357622083210289, 388776537130120, 416709061680348,
  442040873402933, 465206525543334, 486524630006138, 506237381976709, 524534237109882,
  541566887041965, 557459154735615, 572313772893321, 586217169693216, 599242935683045,
  611454391578302, 622906527220958, 633647490767981, 643719749778521, 653161008724372,
  662004942816584, 670281791346329, 678018842198861, 685240831081004, 691970273198511,
  698227740908705, 704032097777520, 709400697165095, 714349551728475, 718893478909318,
  723046226459697, 726820581272122, 730228464164492, 733281012785511, 735988654420812,
  738361170171854, 740407751731569, 742137051779773, 743557228857577, 744675987445834,
  745500613862161, 746038008499517, 746294714853258, 746276945719936, 745990606897777,
  745441318673773, 744634435344279, 743575062983683, 742268075648183, 740718130178122,
  738929679742135, 736906986248915, 734654131737364, 732175028842870, 729473430426061,
  726552938440538, 723417012107388, 720068975456686, 716512024289501, 712749232607970,
  708783558555749, 704617849906472] [700254849133606, 695697198091354, 690947442332763,
  686008035088136, 680881340923904, 675569639099483, 670075126637142, 664399921117496,
  658546063211028, 652515518953750, 646310181772985, 639931874266989, 633382349739913,
  626663293491236, 619776323856297, 612722992991906, 605504787398051, 598123128163509,
  590579370919493, 582874805481351, 575010655153584, 566988075667940, 558808153717928,
  550471905045522, 541980272026882, 533334120693185, 524534237109882, 515581323022106,
  506475990655223, 497218756536411, 487810034174962, 478250125404012, 468539210142993,
  458677334285718, 448664395350610, 438500125442769, 428184070966817, 417715568386888,
  407093715145290, 396317334609570, 385384933598571, 374294650612715, 363044192320810,
  351630755075228, 340050927151050, 328300565900650, 316374641882447, 304267038949740,
  291970294780057, 279475259589563, 266770640486582, 253842382810932, 240672813893597,
  227239431663804, 213513146540647, 199455652324360, 185015351704960, 170120762051802,
  154669252781994, 138506437250945, 121384844444400, 102869627329645, 82076263478996,
  56623135097486]
private def wc_rkmTrajPack_m8_r128_s4_v0 : List ℕ := pCat [2000086595092463, 2000227681486109,
  1999597515000864, 1999456623978149, 1999423761504140, 1999538244077904, 1999779116916602,
  2000070957028132, 1999683132122545, 1999560430088157, 2000409690193876, 2000250265223016,
  1999980011171244, 2000213206381044, 1999604584871014, 1999500969009834, 1999476957411061,
  1999514575755721, 2000412972146797, 2000331103616394, 2000249045482037, 2000125249651883,
  2000211583306230, 2001207751536851, 2003788560930523, 2009552387163462, 2020813929523088,
  2040324281966129, 2070563712496937, 2112689618061997, 2165463689984300, 2224642626208092,
  2283260728121062, 2332926600574885, 2365818385980140, 2376713728176690, 2364326842365690,
  2331491228337664, 2284188794696655, 2229853776869489, 2175581144390685, 2126789555058287,
  2086616398675334, 2056014344784408, 2034308095425339, 2019909274922306, 2010949362747235,
  2005707698549929, 2002820251398000, 2001320797711463, 2000586170026377, 2000246442041824,
  2000098111480732, 2000036964881645, 1999986829295023, 1999995566030693, 2000001408876385,
  2000000421977558, 2000000118952574, 2000000031501457, 2000000007820076, 2000000001815006,
  2000000000392609, 2000000000078844] [1999999999985373, 2000000000002490, 2000000000000384,
  2000000000000052, 2000000000000005, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000]
private def wc_rkmTrajPack_m8_r128_s4_v1 : List ℕ := pCat [1999996450617164, 1999949715241142,
  1999884235423612, 1999811088412792, 2000168124255040, 1999925188162860, 1999546228630256,
  1999936555815324, 2000362692856466, 2000222106435503, 1999989679660943, 1999999123506797,
  2000086538976115, 2000165260287453, 2000248790306158, 2000214075044248, 1999971516921716,
  1999668868563856, 1999527032204332, 1999586212178467, 1999707982096302, 1999760447997152,
  1999735404813662, 1999710990475547, 1999736963408121, 1999785482006124, 1999778495929999,
  1999709724682269, 1999637768501767, 1999696871334840, 1999896049203465, 2000184955440848,
  2000383635487575, 2000391426464864, 2000204665726401, 1999905835854816, 1999656347188097,
  1999535033147466, 1999557758996220, 1999690083114679, 1999833487189997, 1999941292241633,
  2000033947731230, 2000151574452699, 2000350233082862, 2000585277455345, 2000580105534375,
  1999894384533948, 1998169062827146, 1995545610944578, 1993229931555370, 1993860815532637,
  2001295018425940, 2019724207274286, 2052301828609444, 2099666254410073, 2158956907239796,
  2223862734275830, 2285813319837389, 2335933843736677, 2367127960403411, 2375650310857832,
  2361721755323768, 2329081796930114] (pCat [2283745130650392, 2232453840475464, 2181306065645872,
  2134861868867767, 2095807160019691, 2065087303232970, 2042332777981089, 2026384889035408,
  2015770572442891, 2009043707754000, 2004976375035728, 2002627142335818, 2001330137258316,
  2000645551409975, 2000300157957654, 2000133641500964, 2000056957559286, 2000023233206257,
  2000009070756382, 2000003390724481, 2000001214248646, 2000000416920479, 2000000137404461,
  2000000043522799, 2000000013269092, 2000000003899916, 2000000001106715, 2000000000303667,
  2000000000080653, 2000000000020747, 2000000000005168, 2000000000001243, 2000000000000286,
  2000000000000062, 2000000000000011, 2000000000000001, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTrajPack_m8_r128_s4_v2 : List ℕ := pCat [2000006771540024, 2000026287411259,
  2000056879618528, 2000077902260761, 2000055799687506, 1999984093997977, 1999894243085241,
  1999873993112425, 1999948875673978, 2000105884911102, 2000204588881982, 2000169716925895,
  1999999869122080, 1999805510666001, 1999738198302290, 1999821506286979, 1999988251510914,
  2000125527956400, 2000142972941847, 2000065213725137, 1999955595528475, 1999852663745866,
  1999792947085953, 1999783793784151, 1999818531699246, 1999910041386053, 2000034090264173,
  2000124366258878, 2000140938208044, 2000078365447206, 1999968902479650, 1999897429907580,
  1999931658105746, 2000056991857505, 2000209598086617, 2000313950685254, 2000307202996049,
  2000196200388474, 2000057611820104, 1999953758194147, 1999891782147670, 1999849456072046,
  1999793585876268, 1999708136859950, 1999633973634262, 1999637178393904, 1999727789020158,
  1999845296247278, 1999910567068279, 1999868036349979, 1999717357922917, 1999537326066291,
  1999447163386394, 1999518507517662, 1999734659888455, 2000019195568733, 2000269846307754,
  2000383032881893, 2000302200557283, 2000067650893927, 1999811387227797, 1999690526302043,
  1999787605334946, 2000009927273275] (pCat [2000072174607248, 1999680051918446, 1998888585893292,
  1998347868399015, 1999067526863465, 2001616167022329, 2005174187993677, 2007207517517328,
  2004395539184688, 1994761426890426, 1980040147488990, 1966793371668177, 1965145848710849,
  1985217861650581, 2032683058300095, 2105535737984928, 2193679249231443, 2281621255010819,
  2353137064932330, 2395980082295391, 2404892523410953, 2382082554288685, 2335441798540536,
  2275548856480324, 2212684108333249, 2154746445706115, 2106398042853796, 2069264926618524,
  2042757454481306, 2025056986406904, 2013952043952367, 2007385939659387, 2003718851183598,
  2001781334651198, 2000811797474763, 2000351956857347, 2000145142458961, 2000056917000335,
  2000021216356598, 2000007514187364, 2000002527204708, 2000000806630011, 2000000244159967,
  2000000070031073, 2000000019016424, 2000000004883646, 2000000001184767, 2000000000271156,
  2000000000058455, 2000000000011845, 2000000000002249, 2000000000000396, 2000000000000062,
  2000000000000007, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTrajPack_m8_r128_s6_hb : List ℕ := pCat [146993006763605, 206634044652214,
  251547755350831, 288698975720018, 320802625604636, 349259461385689, 374906467009871,
  398292113424674, 419799520372625, 439709185915488, 458234023554204, 475540338881975,
  491761089319444, 507004640652252, 521360761884763, 534904855320390, 547701019157328,
  559804314525410, 571262476342925, 582117226545299, 592405297374646, 602159239515565,
  611408068049737, 620177784422211, 628491802399852, 636371298819710, 643835504791488,
  650901949294938, 657586664376079, 663904359109273, 669868567958907, 675491778008126,
  680785538626036, 685760556450181, 690426778018057, 694793461953407, 698869242273212,
  702662184109586, 706179832922051, 709429258098564, 712417091699308, 715149562979057,
  717632529226515, 719871503378404, 721871678799016, 723637951559880, 725174940507152,
  726487005364639, 727578263086816, 728452602647591, 729113698426247, 729565022331074,
  729809854783234, 729851294667903, 729692268346227, 729335537809949, 728783708050247,
  728039233703336, 727104425027383, 725981453258215, 724672355384917, 723179038380743,
  721503282919550, 719646746603191] [717610966720937, 715397362557866, 713007237265226,
  710441779302101, 707702063453995, 704789051430404, 701703592039810, 698446420936861,
  695018159932703, 691419315855451, 687650278943523, 683711320750032, 679602591531421,
  675324117088062, 670875795018462, 666257390341848, 661468530436223, 656508699230170,
  651377230576636, 646073300725319, 640595919796877, 634943922146549, 629115955486485,
  623110468614639, 616925697572685, 610559650025368, 604010087617813, 597274506024439,
  590350112351420, 583233799492216, 575922116959725, 568411237625828, 560696919684999,
  552774463017596, 544638658952905, 536283732212142, 527703273534234, 518890161134668,
  509836468696079, 500533357005687, 490970945593833, 481138159725982, 471022546767400,
  460610054145355, 449884758688691, 438828533747850, 427420635766178, 415637185233788,
  403450507185767, 390828281964317, 377732435143589, 364117661729952, 349929425973270,
  335101189792945, 319550472391984, 303173076449935, 285834317641249, 267355106710454,
  247488630483372, 225878473190399, 201976138410676, 174856140395983, 142710310761897,
  100862626796441]
private def wc_rkmTrajPack_m8_r128_s6_v0 : List ℕ := pCat [2000006376213585, 1999945245795649,
  1999742031938905, 1999960146592119, 1999953100936937, 1999889359327359, 1999836283974061,
  2000026565835695, 2000068643962818, 1999950079761742, 2000042849853852, 1999994422308539,
  2000124606703695, 2000206342769958, 2000073653697863, 2000113718213250, 2000248882302677,
  2000056446590304, 2000019867589928, 2000105785360223, 2000082271272571, 2000060390678393,
  1999852496702778, 1999868803986181, 1999783649886210, 1999713465201386, 1999956912572661,
  1999885560942682, 1999796056761057, 1999796844613298, 1999378467631009, 1999148379133820,
  1998678595695487, 1997924767855887, 1996927729220555, 1995588859499575, 1994734434151012,
  1994033390017239, 1994090466484057, 2005018158884579, 2003502917452730, 2001241467375356,
  1998349931914384, 1996200854321914, 1995218006978221, 1996775671482612, 1999571487143159,
  2002119208023315, 2003708387606314, 2003292133936468, 2001164233943396, 2002430830228101,
  1996194748914533, 1997420058901857, 1999185054860033, 2003143069209630, 2003152499584652,
  1999626806458114, 1997341882807186, 1996509715679490, 1998808254516525, 1996585922835318,
  1996090691046250, 1999851481096251] (pCat [1995434558867739, 1996629116804331, 1997591109278589,
  1994878173718682, 1999305443923343, 1995059337145489, 1996387087974123, 1995963124276791,
  1995162528918054, 1997686223385271, 1995077708396746, 2000088771867426, 1994697118504343,
  1999129708281491, 1994991201825951, 1998627572070471, 1995271995475376, 1998823252663629,
  2004193805963803, 2000826262638528, 1996132169026077, 1999860968644579, 1997131620733538,
  2000500808415946, 1997530647815375, 1998165304543529, 1999629872134087, 1998571634031400,
  2001498543879339, 2000582850663482, 2002071945180366, 1995839892879343, 1998901657506709,
  1993527619706584, 1990347069288461, 2000606962040350, 2015100419076810, 2019774033960390,
  2001166307124504, 2030481331404962, 2045280920755302, 2017607517939281, 2048390000896485,
  2114191403650038, 2128755428382508, 2061130994046010, 2079391259154634, 2248181195986348,
  2389590530926950, 2463689397942496, 2460352105903688, 2396414434352938, 2301992013744584,
  2205767082863495, 2126149481962238, 2069774455757994, 2034824091772224, 2015649656484802,
  2006303400328572, 2002258310564977, 2000711203797302, 2000193273788105, 2000043955949972,
  2000007898868119] [2000000972465690])
private def wc_rkmTrajPack_m8_r128_s6_v1 : List ℕ := pCat [1999935616238161, 1999904910491752,
  2000011119834078, 1999996886878112, 2000004122740973, 2000078492899798, 2000130223686276,
  2000047081829211, 1999837514370043, 1999914651235172, 1999964996012931, 1999860623608136,
  1999934125942020, 2000056480390951, 1999885362686848, 2000017193876724, 1999696486916894,
  2000071934965293, 1999502727588171, 2000930705500944, 1998585629099628, 2001473471700518,
  1998662852360735, 2000587661809719, 2000418398816542, 1998854169227721, 2000887288084768,
  2000302438880305, 1998621868022545, 2001499091086676, 1999846823881239, 1999959021952316,
  1999085810803394, 2002451273780674, 1998593852463436, 1999069873638221, 2001926014072992,
  1999969907108191, 1999749736520098, 1999165434198977, 2000525369240458, 2001417353400091,
  1998993426961607, 1998696340375527, 1998995210017170, 2002436474246776, 2001366609499204,
  1996892246927596, 2000595133295198, 1997131077301557, 2001521489715474, 2003330584536751,
  1999049936662757, 2001891294534415, 1992386977131468, 1993419238578048, 1991419800497371,
  1999671895808126, 1997251608334544, 2001029993326331, 2000827598230332, 2002128774135482,
  1999434310995410, 1994651112576726] (pCat [1993878346805212, 1997190771299397, 1999309490298114,
  2004613563919985, 2000943237374088, 2003382237644196, 1999039489713931, 1997160476208384,
  2002304437070733, 1999154821660257, 2002219056212857, 2001204885626030, 2001410313993203,
  1997020086762664, 2000920731092403, 1998903867560011, 1997183848160636, 1997086107659470,
  1996798750926226, 1999991215983004, 1992317426495823, 1999989987877472, 1996597550620845,
  1997954547482367, 1993530528903190, 1993324329947499, 2000798785825009, 1990735671584538,
  2005563041161223, 1991472865953456, 1989605841120948, 2006788414958436, 1990795235021267,
  1993451489904220, 2007034633549382, 2004482397765864, 1977634931898320, 2015612406335693,
  2012269118650951, 1965012634181957, 2009533839822929, 2021899949383872, 1968760063787125,
  2002031340885490, 2041503384590398, 1977525854911844, 1949127269293412, 2022229227418656,
  2046713873549002, 1974768035032860, 1948864245194860, 2031997201936340, 2104557660681037,
  2064146942398050, 1978736061614051, 1994954335523458, 2162467023760715, 2387287810955218,
  2530608716474581, 2524385523046367, 2401164360425545, 2242791332349723, 2115373221143922,
  2041240412454634] [2009710818329207])
private def wc_rkmTrajPack_m8_r128_s6_v2 : List ℕ := pCat [1999994172888373, 2000064716016530,
  1999942619614835, 2000208417078765, 1999515923340148, 2000803462578552, 1998811316546108,
  2001193816706060, 1998862186272377, 2000376628966645, 2000537725844738, 1999249581455621,
  1999779340621447, 2001349127351018, 1997973457061721, 2001329739734835, 2000001126263211,
  1999557259105709, 2000327542175237, 1999998995065180, 2000580133502161, 1999015490821677,
  2000300889710182, 2001272819015092, 1998127978800091, 1999900848793233, 2001607509046120,
  1998740560154172, 2000227355979014, 1999300745744429, 2001465995456569, 1999761064728964,
  1997082663534429, 2004063929228005, 1996516797756873, 2002713413026066, 1997708799194155,
  2000420501904775, 2000474707329790, 2000959092968230, 1997922348963865, 2000055228976965,
  2001432785739682, 1999970406997572, 1999092150284335, 1999961643054359, 1998737724383564,
  2003123234177031, 1998936987418925, 1999122097499898, 1999702416283178, 2000290072953691,
  2003070772134017, 1996812266088330, 2001506764094920, 1998748289242129, 2000471213595386,
  2000635672217671, 2001421353211526, 2000374140747424, 1998721537346804, 1997443765884926,
  1999193371349340, 2006317671295282] (pCat [1998262437877891, 2000893132200703, 1995685522625960,
  1999182731932494, 1999006360619378, 2001291852961907, 2004728701843536, 1998781367945719,
  2006828873291489, 1993765872475770, 1996375797561129, 1990318477779325, 1994508386075247,
  2000979106902464, 1995266010625513, 2010619215651262, 1992334668862087, 1996585393873199,
  1997428570516728, 1995594670844925, 1997312975883578, 2004951716185560, 1995600599924066,
  2000183824686234, 2008293873845055, 1984824174470842, 2012028867239253, 2006191158574979,
  1979498386921999, 2021966819236663, 1998533094935992, 1981923002077153, 2024875455946359,
  1985253681400691, 1983009412272057, 2028379586113031, 1981957321511556, 1982522974706381,
  2025205509971918, 1979308320673357, 1982245527426632, 2028268574921267, 1980609870825407,
  1973074579966498, 2031503543419065, 1990826394756173, 1955187028066958, 2029541828641888,
  2029090503383878, 1948549673250443, 1987322824016173, 2054919522967156, 1984748657127484,
  1942497395152210, 2041706116278187, 2056936841839775, 1924364796441212, 1926653743053978,
  2099597196256282, 2094874525361023, 1870735570142980, 1883656567595423, 2320333094276716,
  2701146361343656] [2563987674889375])
private def wc_rkmTrajPack_m8_r128_s5_hb : List ℕ := pCat [148484155463136, 208730212992098,
  254099544150313, 291627639550219, 324056960137340, 352802472057495, 378709649916572,
  402332528544027, 424058114183652, 444169750368084, 462882510467618, 480364387137816,
  496749686566103, 512147873838719, 526649628608345, 540331118085849, 553257090704066,
  565483166152272, 577057563588537, 588022428190259, 598414864824317, 608267754380893,
  617610406280845, 626469085737020, 634867444033757, 642826872833380, 650366798332726,
  657504927331673, 664257454510951, 670639238158937, 676663950038378, 682344203905782,
  687691666291108, 692717152443794, 697430709802507, 701841690913721, 705958817380920,
  709790236151749, 713343569229525, 716625957716558, 719644100950979, 722404291379313,
  724912445708656, 727174132800897, 729194598703641, 730978789155886, 732531369858986,
  733856744763319, 734959072587191, 735842281755627, 736510083922106, 736965986215174,
  737213302333740, 737255162599156, 737094523058607, 736734173722449, 736176746007806,
  735424719451584, 734480427748023, 733346064158726, 732023686336712, 730515220600243,
  728822465686956, 726947096013999] [724890664465446, 722654604724101, 720240233160837,
  717648750290884, 714881241802747, 711938679161843, 708821919787263, 705531706796395,
  702068668308257, 698433316292404, 694626044945971, 690647128576803, 686496718965593,
  682174842174445, 677681394763067, 673016139366959, 668178699584115, 663168554107910,
  657985030033660, 652627295254650, 647094349849857, 641385016349806, 635497928748567,
  629431520108153, 623184008576029, 616753381605987, 610137378136496, 603333468437216,
  596338831282226, 589150328045404, 581764473236695, 574177400904248, 566384826212173,
  558382001361162, 550163664841915, 541723982789193, 533056480924124, 524153965216314,
  515008428941049, 505610943217469, 495951527344959, 486018994242989, 475800764952921,
  465282644347790, 454448547726197, 443280164555484, 431756540849069, 419853554854930,
  407543250863587, 394792981355279, 381564285663806, 367811399205765, 353479233001213,
  338500573983888, 322792104642615, 306248570642719, 288733921373539, 270067250835280,
  249999242094220, 228169863773978, 204025055313313, 176629942511453, 144158014288668,
  101885812715896]
private def wc_rkmTrajPack_m8_r128_s5_v0 : List ℕ := pCat [2000006771540024, 1999973712588741,
  2000056879618528, 1999922097739239, 2000055799687506, 1999984093997977, 2000105756914759,
  2000126006887575, 1999948875673978, 2000105884911102, 1999795411118018, 2000169716925895,
  1999999869122080, 1999805510666001, 1999738198302290, 1999821506286979, 1999988251510914,
  1999874472043600, 2000142972941847, 2000065213725137, 2000044404471525, 2000147336254134,
  2000207052914047, 2000216206215849, 2000181468300754, 2000089958613947, 1999965909735827,
  2000124366258878, 1999859061791956, 1999921634552794, 2000031097520350, 2000102570092420,
  2000068341894254, 2000056991857505, 1999790401913383, 1999686049314746, 1999692797003951,
  1999803799611526, 1999942388179896, 1999953758194147, 2000108217852330, 2000150543927954,
  2000206414123732, 1999708136859950, 1999633973634262, 1999637178393904, 1999727789020158,
  1999845296247278, 1999910567068279, 2000131963650021, 1999717357922917, 1999537326066291,
  1999447163386394, 2000481492482338, 2000265340111545, 1999980804431267, 2000269846307754,
  2000383032881893, 1999697799442717, 1999932349106073, 2000188612772203, 2000309473697957,
  1999787605334946, 1999990072726725] (pCat [1999927825392752, 2000319948081554, 1998888585893292,
  1998347868399015, 1999067526863465, 1998383832977671, 1994825812006323, 1992792482482672,
  1995604460815312, 1994761426890426, 1980040147488990, 1966793371668177, 1965145848710849,
  2014782138349419, 2032683058300095, 2105535737984928, 2193679249231443, 2281621255010819,
  2353137064932330, 2395980082295391, 2404892523410953, 2382082554288685, 2335441798540536,
  2275548856480324, 2212684108333249, 2154746445706115, 2106398042853796, 2069264926618524,
  2042757454481306, 2025056986406904, 2013952043952367, 2007385939659387, 2003718851183598,
  2001781334651198, 2000811797474763, 2000351956857347, 2000145142458961, 2000056917000335,
  2000021216356598, 2000007514187364, 2000002527204708, 2000000806630011, 2000000244159967,
  2000000070031073, 2000000019016424, 1999999995116354, 2000000001184767, 2000000000271156,
  2000000000058455, 1999999999988155, 1999999999997751, 2000000000000396, 2000000000000062,
  2000000000000007, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTrajPack_m8_r128_s5_v1 : List ℕ := pCat [2000018169041771, 2000223955191945,
  1999876850081012, 1999929750328197, 2000145937303364, 1999913211673959, 1999981287267533,
  2000011409391458, 1999991737168698, 2000079736530421, 1999936168818841, 2000004353226962,
  1999981838909370, 2000131535435359, 1999910876666898, 1999836967642715, 1999993592093130,
  2000117828340265, 2000077397032140, 2000079827513977, 2000098887661349, 1999884130535102,
  2000045897071764, 2000004250827143, 2000074684600411, 2000009755967971, 2000106239218304,
  2000143956205013, 1999843094692797, 1999967632180267, 1999701344537616, 1999981507458777,
  1999785162728205, 2000010204410730, 1999787343505750, 1999993893943839, 1999948719611355,
  1999977940868251, 2000014356878861, 2000240627415331, 1999899080867382, 2000312854792017,
  2000055431598735, 2000379419745728, 2000187166807364, 2000090563038461, 1999618654968021,
  2000220696304030, 2000108302120071, 1999822506295605, 1999818235706560, 2001058212911122,
  1998796444631569, 2001841302578544, 1996857526296452, 2004471617488161, 1993684656255275,
  2006353601123123, 1992781788232401, 2006008699069476, 1997552239892144, 1998834604348295,
  2004238661190741, 1994864139379565] (pCat [2002612240838823, 2000420074309954, 1995856709080377,
  2004968539307045, 1999122088726331, 1994116305184193, 2004986039628844, 2002284203096655,
  1992466955236065, 2000577349684091, 2007543938115317, 1997723961594342, 1993144187160538,
  2002727909260833, 2006663196240146, 1998550902132423, 1993873341731289, 1999278900498578,
  2004860059384650, 2003584130724105, 1999228934102673, 1996613220279023, 1995793856089349,
  1996461693661211, 2000579331325705, 2007733064379784, 2010980792652723, 2000786967201030,
  1974523753959123, 1942751710931962, 1926396240309990, 1946301602862805, 2011811013456899,
  2115038815821894, 2233546173164535, 2339335130259688, 2409237491727357, 2431978171522368,
  2409655530720657, 2354322704686617, 2282210030042820, 2208331052442816, 2143189058152645,
  2091924893243699, 2055246530440067, 2031130996458709, 2016463163554908, 2008174653535856,
  2003811320385483, 2001667896818939, 2000684566156539, 2000263208625631, 2000094647449095,
  2000031760405012, 2000009916795557, 2000002870234414, 2000000766278584, 2000000187509178,
  2000000041712373, 2000000008345480, 2000000001480043, 2000000000227876, 2000000000029481,
  2000000000003017] [2000000000000208])
private def wc_rkmTrajPack_m8_r128_s5_v2 : List ℕ := pCat [2000006376213585, 1999945245795649,
  1999742031938905, 1999960146592119, 2000046899063063, 2000110640672641, 2000163716025939,
  2000026565835695, 2000068643962818, 1999950079761742, 2000042849853852, 2000005577691461,
  1999875393296305, 2000206342769958, 1999926346302137, 2000113718213250, 1999751117697323,
  2000056446590304, 2000019867589928, 2000105785360223, 1999917728727429, 2000060390678393,
  1999852496702778, 2000131196013819, 1999783649886210, 2000286534798614, 1999956912572661,
  2000114439057318, 1999796056761057, 2000203155386702, 1999378467631009, 2000851620866180,
  1998678595695487, 2002075232144113, 1996927729220555, 2004411140500425, 1994734434151012,
  2005966609982761, 1994090466484057, 2005018158884579, 1996497082547270, 2001241467375356,
  2001650068085616, 1996200854321914, 2004781993021779, 1996775671482612, 2000428512856841,
  2002119208023315, 1996291612393686, 2003292133936468, 1998835766056604, 1997569169771899,
  2003805251085467, 1997420058901857, 1999185054860033, 2003143069209630, 1996847500415348,
  2000373193541886, 2002658117192814, 1996509715679490, 2001191745483475, 2003414077164682,
  1996090691046250, 2000148518903749] (pCat [2004565441132261, 1996629116804331, 1997591109278589,
  2005121826281318, 1999305443923343, 1995059337145489, 2003612912025877, 2004036875723209,
  1995162528918054, 1997686223385271, 2004922291603254, 2000088771867426, 1994697118504343,
  2000870291718509, 2005008798174049, 1998627572070471, 1995271995475376, 2001176747336371,
  2004193805963803, 1999173737361472, 1996132169026077, 1999860968644579, 2002868379266462,
  2000500808415946, 1997530647815375, 1998165304543529, 2000370127865913, 2001428365968600,
  2001498543879339, 2000582850663482, 1997928054819634, 1995839892879343, 1998901657506709,
  2006472380293416, 2009652930711539, 2000606962040350, 1984899580923190, 1980225966039610,
  1998833692875496, 2030481331404962, 2045280920755302, 2017607517939281, 1951609999103515,
  1885808596349962, 1871244571617492, 1938869005953990, 2079391259154634, 2248181195986348,
  2389590530926950, 2463689397942496, 2460352105903688, 2396414434352938, 2301992013744584,
  2205767082863495, 2126149481962238, 2069774455757994, 2034824091772224, 2015649656484802,
  2006303400328572, 2002258310564977, 2000711203797302, 2000193273788105, 2000043955949972,
  2000007898868119] [2000000972465690])
private def wc_rkmTrajPack_m64_r96_s2_hb : List ℕ := [216673687229634, 302431933266736,
  365511435827016, 416405980114741, 459235139203705, 496138463826105, 528402473551345,
  556875350986933, 582153046790675, 604674343149050, 624774101429504, 642715229869038,
  658708945653125, 672928190898245, 685516840731886, 696596216400000, 706269811465779,
  714626797522581, 721744674594993, 727691308488344, 732526519876338, 736303339717557,
  739069012255124, 740865804222848, 741731663209311, 741700757079453, 740803918426956,
  739069012255124, 736521240810032, 733183396277835, 729076069604701, 724217821789535,
  718625322483517, 712313459493878, 705295421747078, 697582757350920, 689185407549323,
  680111716535780, 670368416230426, 659960584174595, 648891571588517, 637162897286034,
  624774101429504, 611722550876592, 598003184886764, 583608185877567, 568526554236264,
  552743558112705, 536240017406686, 518991363826477, 500966392649787, 482125581086052,
  462418783139863, 441782003830534, 420132772842696, 397363312196132, 373330083508553,
  347837091309391, 320607737817915, 291233989743558, 259075732065519, 223033995600982,
  180927799639335, 127036209665116]
private def wc_rkmTrajPack_m64_r96_s2_v0 : List ℕ := pCat [2088406456126654, 2201069223817120,
  2319018846769519, 2407648745819093, 2444888337346301, 2428195187349107, 2370882886159641,
  2293133256713216, 2213556627033611, 2144512710454818, 2091378512485700, 2054251194652629,
  2030359940518134, 2016066678722165, 2008062372030038, 2003845066325757, 2001746175927128,
  2000756350427854, 2000312897828674, 2000123771022966, 2000046857018537, 2000016989908987,
  2000005903606193, 2000001966701522, 2000000628321775, 2000000192542245, 2000000056598365,
  2000000015959184, 2000000004316256, 2000000001119497, 2000000000278394, 2000000000066357,
  2000000000015153, 2000000000003313, 2000000000000692, 2000000000000136, 2000000000000025,
  2000000000000003, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000] [2000000000000000]
private def wc_rkmTrajPack_m64_r96_s2_v1 : List ℕ := pCat [2000000000013436, 2000000000092713,
  2000000000454824, 2000000001881032, 2000000007169332, 2000000026526403, 2000000096887084,
  2000000345936027, 2000001185345504, 2000003841006673, 2000011678869401, 2000033233994395,
  2000088541000447, 2000221224551422, 2000519518448364, 2001149247585890, 2002399773995877,
  2004738884320698, 2008864193489761, 2015728198289725, 2026505489434172, 2042469919035856,
  2064763038029466, 2094065724163555, 2130228094393268, 2171954949379233, 2216665385116964,
  2260627833976839, 2299409616494345, 2328586148852823, 2344560302658045, 2345285070898884,
  2330690701574598, 2302694316005447, 2264790697791565, 2221343560226074, 2176773557485995,
  2134848062515746, 2098222042167005, 2068286910511147, 2045292186263296, 2028643277314435,
  2017260456703883, 2009903420013363, 2005405636931045, 2002804203886401, 2001380975332489,
  2000644793573146, 2000285023729760, 2000119081360566, 2000046933182480, 2000017411437419,
  2000006064575926, 2000001977349751, 2000000601390405, 2000000169900375, 2000000044359068,
  2000000010636075, 2000000002323376, 2000000000457566, 2000000000080089, 2000000000012200,
  2000000000001562, 2000000000000155] [2000000000000009]
private abbrev dP_0 : Prop := atF [ bSlideChk 22 129 wc_rkmTraj_m1024_r128_s0_hb
  wc_rkmTraj_m1024_r128_s0_v0 wc_rkmTraj_m1024_r128_s0_v1, bNatListEq (bEvalLo12W 4 2048 7
  [1,2,3,3,3,3,3,3] [100324624,134641704,45398435,34602103,9950443,4020378,1755259,709195]
  [2,4,2,2,1,1,1,1] rkmMasks_m4_r7 []) rkmRow_m4_r7] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bSlideChk 22 129 wc_rkmTraj_m1024_r128_s0_hb
  wc_rkmTraj_m1024_r128_s0_v1 wc_rkmTraj_m1024_r128_s0_v2, bNatListEq (bEvalLo12W 8 1024 19 [1,1]
  [70095459,26075094] [5,3] rkmMasks_m8_r19 []) rkmRow_m8_r19] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bSlideChk 22 129 wc_rkmTraj_m1024_r128_s0_hb
  wc_rkmTraj_m1024_r128_s0_v2 wc_rkmTraj_m1024_r128_s0_ck3] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bSlideChk 22 129 wc_rkmTraj_m1024_r128_s0_hb
  wc_rkmTraj_m1024_r128_s0_ck3 wc_rkmTraj_m1024_r128_s0_ck4] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bSlideChk 22 129 wc_rkmTraj_m1024_r128_s0_hb
  wc_rkmTraj_m1024_r128_s0_ck4 wc_rkmTraj_m1024_r128_s0_ck5] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bSlideChk 22 129 wc_rkmTraj_m1024_r128_s0_hb
  wc_rkmTraj_m1024_r128_s0_ck5 wc_rkmTraj_m1024_r128_s0_ck6] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bNatListEq (bEvalLo12W 64 128 96 [1,1,1,1,2,2,2,2]
  [2407052,11495891,27642707,17183461,6841,5683076,2721,478701] [2,9,20,13,1,7,1,1]
  rkmMasksPack_m64_r96 [none, none, some (20, 65, wc_rkmTrajPack_m64_r96_s2_hb,
  wc_rkmTrajPack_m64_r96_s2_v0, wc_rkmTrajPack_m64_r96_s2_v1)]) rkmRowPack_m64_r96, bNatListEq
  (bEvalLo12W 4 2048 13 [1,2,4,6,6,6,6,6]
  [59742462,61629685,76356963,31720891,24173774,7480804,3918594,1645808] [2,3,6,3,3,1,1,1]
  rkmMasks_m4_r13 []) rkmRow_m4_r13, bNatListEq (bEvalLo12W 2 4096 3 [1,2,2,2]
  [162349218,245512918,18317255,9330790] [2,3,1,1] rkmMasksPack_m2_r3 []) rkmRowPack_m2_r3] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bNatListEq (bEvalLo12W 4 2048 64 [1,2,5,11,23,29,29,29]
  [18800986,20062782,23657362,23741775,30233100,14424107,12348740,4431369] [2,3,6,11,23,13,11,4]
  rkmMasks_m4_r64 [none, none, none, none, some (23, 65, wc_rkmTraj_m4_r64_s4_hb,
  wc_rkmTraj_m4_r64_s4_v0, wc_rkmTraj_m4_r64_s4_v1)]) rkmRow_m4_r64, bNatListEq (bEvalLo12W 32 256
  14 [1,1,1,1,1,1,1,1] [33535682,49580417,21275247,19622382,13968139,7838272,2863333,6877497]
  [4,6,3,2,2,1,1,1] rkmMasksPack_m32_r14 []) rkmRowPack_m32_r14, bNatListEq (bEvalLo12W 2 4096 6
  [1,2,4,5,5,5,5,5] [99205924,83754727,76675552,29671325,33941734,17758523,4800941,6719709]
  [1,2,2,1,1,1,1,1] rkmMasksPack_m2_r6 []) rkmRowPack_m2_r6] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := atF [ bNatListEq (bEvalLo12W 8 1024 128 [1,2,4,9,18,30,30,30]
  [13603651,12476160,16113899,16271941,21849272,12283935,12579904,2686133] [2,4,8,16,36,29,30,7]
  rkmMasksPack_m8_r128 [none, none, none, none, some (36, 129, wc_rkmTrajPack_m8_r128_s4_hb,
  wc_rkmTrajPack_m8_r128_s4_v0, wc_rkmTrajPack_m8_r128_s4_v2), some (29, 129,
  wc_rkmTrajPack_m8_r128_s5_hb, wc_rkmTrajPack_m8_r128_s5_v0, wc_rkmTrajPack_m8_r128_s5_v2), some
  (30, 129, wc_rkmTrajPack_m8_r128_s6_hb, wc_rkmTrajPack_m8_r128_s6_v0,
  wc_rkmTrajPack_m8_r128_s6_v2)]) rkmRowPack_m8_r128, bNatListEq (bEvalLo12W 64 128 17
  [1,1,1,1,1,1,1,1] [27845559,23157974,22863337,9341079,6588930,6535566,4699873,2974535]
  [6,5,5,2,2,2,1,1] rkmMasksPack_m64_r17 []) rkmRowPack_m64_r17] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := atF [ bNatListEq (bEvalLo12W 64 128 44 [1,1,1]
  [121181129,3312803,4647746] [49,2,2] rkmMasksPack_m64_r44 []) rkmRowPack_m64_r44, bNatListEq
  (bEvalLo12W 8 1024 20 [1,3,4,4,4] [84246448,51425618,33129155,34259272,20499045] [5,6,5,5,3]
  rkmMasksPack_m8_r20 []) rkmRowPack_m8_r20, bNatListEq (bEvalLo12W 256 32 9 [1,1,1]
  [47226735,752229,102447] [11,2,2] rkmMasks_m256_r9 []) rkmRow_m256_r9] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := atF [ bSlideChk 18 129 wc_rkmTrajPack_m8_r128_s4_hb
  wc_rkmTrajPack_m8_r128_s4_v0 wc_rkmTrajPack_m8_r128_s4_v1, bNatListEq (bEvalLo12W 256 32 21
  [1,1] [48471510,1010402] [25,2] rkmMasks_m256_r21 []) rkmRow_m256_r21] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := atF [ bSlideChk 18 129 wc_rkmTrajPack_m8_r128_s4_hb
  wc_rkmTrajPack_m8_r128_s4_v1 wc_rkmTrajPack_m8_r128_s4_v2, bNatListEq (bEvalLo12W 128 64 20
  [1,1] [69910336,1459788] [24,2] rkmMasks_m128_r20 []) rkmRow_m128_r20] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := atF [ bNatListEq (bEvalLo12W 512 16 40 [1] [35174751] [52]
  rkmMasks_m512_r40 []) rkmRow_m512_r40, bNatListEq (bEvalLo12W 64 128 23 [1,1]
  [103983474,4081407] [25,1] rkmMasksPack_m64_r23 []) rkmRowPack_m64_r23, bNatListEq (bEvalLo12W
  64 128 11 [1,1,1] [93635950,4202992,2218841] [12,1,1] rkmMasksPack_m64_r11 [])
  rkmRowPack_m64_r11] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := atF [ bSlideChk 15 129 wc_rkmTrajPack_m8_r128_s5_hb
  wc_rkmTrajPack_m8_r128_s5_v0 wc_rkmTrajPack_m8_r128_s5_v1, bNatListEq (bEvalLo12W 32 256 23
  [1,1,1,1,2,2,2,2] [5679971,28480304,52786535,39615426,6966350,9401931,7400716,4472759]
  [1,5,9,7,2,3,2,2] rkmMasksPack_m32_r23 []) rkmRowPack_m32_r23, bNatListEq (bEvalLo12W 1024 8 11
  [1,1] [20435323,3606233] [12,3] rkmMasks_m1024_r11 []) rkmRow_m1024_r11] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := atF [ bSlideChk 15 129 wc_rkmTrajPack_m8_r128_s6_hb
  wc_rkmTrajPack_m8_r128_s6_v0 wc_rkmTrajPack_m8_r128_s6_v1, bNatListEq (bEvalLo12W 64 128 23
  [1,1] [103999748,4070036] [28,2] rkmMasks_m64_r23 []) rkmRow_m64_r23, bNatListEq (bEvalLo12W 4
  2048 21 [1,1,3,6,6,6,6,6] [50014757,38014072,60365437,69258,1056144,388543,1319418,512657]
  [2,2,5,1,1,1,1,1] rkmMasksPack_m4_r21 []) rkmRowPack_m4_r21] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := atF [ bSlideChk 15 129 wc_rkmTrajPack_m8_r128_s6_hb
  wc_rkmTrajPack_m8_r128_s6_v1 wc_rkmTrajPack_m8_r128_s6_v2, bNatListEq (bEvalLo12W 4 2048 23
  [1,4,8,8,8] [57570663,56704524,78961419,24834904,14295799] [3,7,13,5,4] rkmMasks_m4_r23 [])
  rkmRow_m4_r23, bNatListEq (bEvalLo12W 2 4096 18 [1,3,6,12] [40006001,49861866,51231933,78699628]
  [1,2,4,9] rkmMasksPack_m2_r18 []) rkmRowPack_m2_r18, bNatListEq (bEvalLo12W 32 256 8 [1,1,1,1]
  [113200996,16453430,8645830,4586646] [8,2,1,1] rkmMasks_m32_r8 []) rkmRow_m32_r8] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := atF [ bNatListEq (bEvalLo12W 8 1024 44 [1,2,4,8,10,10,10]
  [33686902,23894884,29551141,22809142,40205217,3850449,4837310] [3,4,8,10,19,2,3]
  rkmMasksPack_m8_r44 []) rkmRowPack_m8_r44, bNatListEq (bEvalLo12W 256 32 25 [1] [49783411] [31]
  rkmMasks_m256_r25 []) rkmRow_m256_r25, bNatListEq (bEvalLo12W 16 512 9 [1,1,1,1]
  [136883334,52544824,23473342,14153637] [8,4,3,2] rkmMasks_m16_r9 []) rkmRow_m16_r9] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := atF [ bSlideChk 14 129 wc_rkmTrajPack_m8_r128_s5_hb
  wc_rkmTrajPack_m8_r128_s5_v1 wc_rkmTrajPack_m8_r128_s5_v2, bNatListEq (bEvalLo12W 32 256 26
  [1,2,2] [102721401,27743375,15397111] [18,8,5] rkmMasksPack_m32_r26 []) rkmRowPack_m32_r26,
  bNatListEq (bEvalLo12W 2 4096 13 [1,2,4,8,12,12,12,12]
  [45805282,47474363,52069917,62151016,28920308,25433869,7303394,3918594] [1,2,3,5,3,3,1,1]
  rkmMasks_m2_r13 []) rkmRow_m2_r13] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := atF [ bNatListEq (bEvalLo12W 64 128 34 [1,1,1]
  [98351801,13477328,5202565] [35,6,3] rkmMasks_m64_r34 []) rkmRow_m64_r34, bNatListEq (bEvalLo12W
  64 128 25 [1,1,1] [93472319,11829995,4199067] [27,4,3] rkmMasks_m64_r25 []) rkmRow_m64_r25,
  bNatListEq (bEvalLo12W 1024 8 17 [1] [24276827] [20] rkmMasks_m1024_r17 []) rkmRow_m1024_r17,
  bNatListEq (bEvalLo12W 256 32 3 [1] [44908175] [5] rkmMasks_m256_r3 []) rkmRow_m256_r3] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := atF [ bSlideChk 23 65 wc_rkmTraj_m4_r64_s4_hb
  wc_rkmTraj_m4_r64_s4_v0 wc_rkmTraj_m4_r64_s4_v1, bNatListEq (bEvalLo12W 128 64 27 [1,1,1,1]
  [66787321,4755464,873,1224641] [29,3,2,2] rkmMasks_m128_r27 []) rkmRow_m128_r27, bNatListEq
  (bEvalLo12W 8 1024 25 [1,1,2,4,4,4,4,4]
  [72319132,14681508,48761869,5461,251761,2364773,1804030,284036] [5,1,5,1,1,1,1,1]
  rkmMasksPack_m8_r25 []) rkmRowPack_m8_r25, bNatListEq (bEvalLo12W 16 512 7 [1,1,1,1,1,1,1,1]
  [64463342,43382148,20590604,18604182,9740885,24833666,19558259,11415810] [3,2,1,1,1,1,1,1]
  rkmMasksPack_m16_r7 []) rkmRowPack_m16_r7] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := atF [ bNatListEq (bEvalLo12W 16 512 35 [1,2,3,3,3,3]
  [57406177,28883921,51971781,28541699,12291176,5972266] [7,6,15,8,4,2] rkmMasksPack_m16_r35 [])
  rkmRowPack_m16_r35, bNatListEq (bEvalLo12W 64 128 28 [1,1,1,1,1,1,1,1]
  [33481532,28288148,14397804,11433425,10517999,4605518,5179357,3862497] [10,8,4,4,3,2,2,2]
  rkmMasksPack_m64_r28 []) rkmRowPack_m64_r28, bNatListEq (bEvalLo12W 4 2048 19 [1,3,7,7,7]
  [57169081,60625881,81410814,25829029,16353713] [3,5,11,5,3] rkmMasks_m4_r19 []) rkmRow_m4_r19,
  bNatListEq (bEvalLo12W 2 4096 5 [1,2,4,4,4,4,4,4]
  [90129973,100889708,56823848,66369043,21931455,9211209,3868706,1624856] [1,2,2,2,1,1,1,1]
  rkmMasks_m2_r5 []) rkmRow_m2_r5] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := atF [ bNatListEq (bEvalLo12W 8 1024 36 [1,2,4,8,8,8]
  [44088109,34500000,32506582,56047500,8873493,2904580] [4,5,8,20,4,2] rkmMasks_m8_r36 [])
  rkmRow_m8_r36, bNatListEq (bEvalLo12W 2 4096 36 [2,4,8,16,27,27,27]
  [31574976,30106097,24753750,31713739,52382339,3478139,971833] [2,3,4,7,17,2,1] rkmMasks_m2_r36
  []) rkmRow_m2_r36, bNatListEq (bEvalLo12W 1024 8 18 [1] [24302985] [21] rkmMasks_m1024_r18 [])
  rkmRow_m1024_r18, bNatListEq (bEvalLo12W 256 32 4 [1] [46070109] [6] rkmMasks_m256_r4 [])
  rkmRow_m256_r4] = true
private theorem bk_21 : dP_21 := by decide +kernel
private abbrev dP_22 : Prop := atF [ bSlideChk 20 65 wc_rkmTrajPack_m64_r96_s2_hb
  wc_rkmTrajPack_m64_r96_s2_v0 wc_rkmTrajPack_m64_r96_s2_v1, bNatListEq (bEvalLo12W 16 512 32
  [1,2,4,4,4,4,4,4] [65019026,38776081,26718022,22786501,7746746,2707959,330279,939757]
  [8,8,9,8,3,1,1,1] rkmMasksPack_m16_r32 []) rkmRowPack_m16_r32, bNatListEq (bEvalLo12W 256 32 15
  [1,1] [47941087,995405] [18,2] rkmMasks_m256_r15 []) rkmRow_m256_r15, bNatListEq (bEvalLo12W 2
  4096 9 [1,2,4,8,8,8,8,8] [77132972,57901824,93604557,34441630,39893014,10440199,5248501,4252308]
  [1,2,3,2,2,1,1,1] rkmMasksPack_m2_r9 []) rkmRowPack_m2_r9] = true
private theorem bk_22 : dP_22 := by decide +kernel
private abbrev dP_23 : Prop := atF [ bNatListEq (bEvalLo12W 1024 8 128 [1,1,1,1]
  [23750000,1050000,286250,231562] [132,6,2,2] rkmMasks_m1024_r128 [some (132, 129,
  wc_rkmTraj_m1024_r128_s0_hb, wc_rkmTraj_m1024_r128_s0_v0, wc_rkmTraj_m1024_r128_s0_ck6)])
  rkmRow_m1024_r128, bNatListEq (bEvalLo12W 32 256 30 [1,2,2,2]
  [81365582,40233647,14363187,5076887] [17,13,6,3] rkmMasks_m32_r30 []) rkmRow_m32_r30, bNatListEq
  (bEvalLo12W 64 128 13 [1,1,1] [94453625,4429054,2524638] [16,2,2] rkmMasks_m64_r13 [])
  rkmRow_m64_r13, bNatListEq (bEvalLo12W 4 2048 18 [1,4] [93685581,82794052] [3,7]
  rkmMasksPack_m4_r18 []) rkmRowPack_m4_r18] = true
private theorem bk_23 : dP_23 := by decide +kernel
private theorem ws_rkmTraj_m1024_r128_s0_m1 : WalkOk (some (44, 129, wc_rkmTraj_m1024_r128_s0_hb,
    wc_rkmTraj_m1024_r128_s0_v0, wc_rkmTraj_m1024_r128_s0_v2)) := mIter_split rfl
    (bSlideChk_sound bk_0) (bSlideChk_sound bk_1)
private theorem ws_rkmTraj_m1024_r128_s0_m2 : WalkOk (some (66, 129, wc_rkmTraj_m1024_r128_s0_hb,
    wc_rkmTraj_m1024_r128_s0_v0, wc_rkmTraj_m1024_r128_s0_ck3)) := mIter_split rfl
    ws_rkmTraj_m1024_r128_s0_m1 (bSlideChk_sound bk_2)
private theorem ws_rkmTraj_m1024_r128_s0_m3 : WalkOk (some (88, 129, wc_rkmTraj_m1024_r128_s0_hb,
    wc_rkmTraj_m1024_r128_s0_v0, wc_rkmTraj_m1024_r128_s0_ck4)) := mIter_split rfl
    ws_rkmTraj_m1024_r128_s0_m2 (bSlideChk_sound bk_3)
private theorem ws_rkmTraj_m1024_r128_s0_m4 : WalkOk (some (110, 129, wc_rkmTraj_m1024_r128_s0_hb,
    wc_rkmTraj_m1024_r128_s0_v0, wc_rkmTraj_m1024_r128_s0_ck5)) := mIter_split rfl
    ws_rkmTraj_m1024_r128_s0_m3 (bSlideChk_sound bk_4)
private theorem ws_rkmTraj_m1024_r128_s0 : WalkOk (some (132, 129, wc_rkmTraj_m1024_r128_s0_hb,
    wc_rkmTraj_m1024_r128_s0_v0, wc_rkmTraj_m1024_r128_s0_ck6)) := mIter_split rfl
    ws_rkmTraj_m1024_r128_s0_m4 (bSlideChk_sound bk_5)
private theorem ws_rkmTrajPack_m8_r128_s4 : WalkOk (some (36, 129, wc_rkmTrajPack_m8_r128_s4_hb,
    wc_rkmTrajPack_m8_r128_s4_v0, wc_rkmTrajPack_m8_r128_s4_v2)) := mIter_split rfl
    (bSlideChk_sound bk_10) (bSlideChk_sound bk_11)
private theorem ws_rkmTrajPack_m8_r128_s5 : WalkOk (some (29, 129, wc_rkmTrajPack_m8_r128_s5_hb,
    wc_rkmTrajPack_m8_r128_s5_v0, wc_rkmTrajPack_m8_r128_s5_v2)) := mIter_split rfl
    (bSlideChk_sound bk_13) (bSlideChk_sound bk_17)
private theorem ws_rkmTrajPack_m8_r128_s6 : WalkOk (some (30, 129, wc_rkmTrajPack_m8_r128_s6_hb,
    wc_rkmTrajPack_m8_r128_s6_v0, wc_rkmTrajPack_m8_r128_s6_v2)) := mIter_split rfl
    (bSlideChk_sound bk_14) (bSlideChk_sound bk_15)
/-- Kernel trajectory certificate `(m = 1024, r = 128)`. -/
theorem rkmTraj_m1024_r128 : rkmEvalT16Lo12 1024 8 128 [1, 1, 1, 1] [23750000, 1050000, 286250,
  231562] [132, 6, 2, 2] rkmMasks_m1024_r128 = rkmRow_m1024_r128 :=
    bhW_eq bk_23 (wCons ws_rkmTraj_m1024_r128_s0 wNil)
/-- Kernel trajectory certificate `(m = 1024, r = 18)`. -/
theorem rkmTraj_m1024_r18 : rkmEvalT16Lo12 1024 8 18 [1] [24302985] [21] rkmMasks_m1024_r18 =
  rkmRow_m1024_r18 := bh0_eq (tl2 bk_21)
/-- Kernel trajectory certificate `(m = 256, r = 3)`. -/
theorem rkmTraj_m256_r3 : rkmEvalT16Lo12 256 32 3 [1] [44908175] [5] rkmMasks_m256_r3 =
  rkmRow_m256_r3 := bh0_eq (tl1 (tl2 bk_18))
/-- Kernel trajectory certificate `(m = 4, r = 64)`. -/
theorem rkmTraj_m4_r64 : rkmEvalT16Lo12 4 2048 64 [1, 2, 5, 11, 23, 29, 29, 29] [18800986, 20062782,
  23657362, 23741775, 30233100, 14424107, 12348740, 4431369] [2, 3, 6, 11, 23, 13, 11, 4]
  rkmMasks_m4_r64 = rkmRow_m4_r64 :=
    bhW_eq bk_7 (wSkip (wSkip (wSkip (wSkip (wCons (bSlideChk_sound bk_19) wNil)))))
/-- Kernel trajectory certificate `(m = 256, r = 4)`. -/
theorem rkmTraj_m256_r4 : rkmEvalT16Lo12 256 32 4 [1] [46070109] [6] rkmMasks_m256_r4 =
  rkmRow_m256_r4 := bh0_eq (tl1 (tl2 bk_21))
/-- Kernel trajectory certificate `(m = 512, r = 40)`. -/
theorem rkmTraj_m512_r40 : rkmEvalT16Lo12 512 16 40 [1] [35174751] [52] rkmMasks_m512_r40 =
  rkmRow_m512_r40 := bh0_eq bk_12
/-- Kernel trajectory certificate `(m = 2, r = 5)`. -/
theorem rkmTraj_m2_r5 : rkmEvalT16Lo12 2 4096 5 [1, 2, 4, 4, 4, 4, 4, 4] [90129973, 100889708,
  56823848, 66369043, 21931455, 9211209, 3868706, 1624856] [1, 2, 2, 2, 1, 1, 1, 1] rkmMasks_m2_r5 =
  rkmRow_m2_r5 := bh0_eq (tl1 (tl2 bk_20))
/-- Kernel trajectory certificate `(m = 64, r = 34)`. -/
theorem rkmTraj_m64_r34 : rkmEvalT16Lo12 64 128 34 [1, 1, 1] [98351801, 13477328, 5202565] [35, 6,
  3] rkmMasks_m64_r34 = rkmRow_m64_r34 := bh0_eq bk_18
/-- Kernel trajectory certificate `(m = 8, r = 19)`. -/
theorem rkmTraj_m8_r19 : rkmEvalT16Lo12 8 1024 19 [1, 1] [70095459, 26075094] [5, 3] rkmMasks_m8_r19
  = rkmRow_m8_r19 := bh0_eq (tl1 bk_1)
/-- Kernel trajectory certificate `(m = 8, r = 36)`. -/
theorem rkmTraj_m8_r36 : rkmEvalT16Lo12 8 1024 36 [1, 2, 4, 8, 8, 8] [44088109, 34500000, 32506582,
  56047500, 8873493, 2904580] [4, 5, 8, 20, 4, 2] rkmMasks_m8_r36 = rkmRow_m8_r36 := bh0_eq bk_21
/-- Kernel trajectory certificate `(m = 4, r = 7)`. -/
theorem rkmTraj_m4_r7 : rkmEvalT16Lo12 4 2048 7 [1, 2, 3, 3, 3, 3, 3, 3] [100324624, 134641704,
  45398435, 34602103, 9950443, 4020378, 1755259, 709195] [2, 4, 2, 2, 1, 1, 1, 1] rkmMasks_m4_r7 =
  rkmRow_m4_r7 := bh0_eq (tl1 bk_0)
/-- Kernel trajectory certificate `(m = 32, r = 30)`. -/
theorem rkmTraj_m32_r30 : rkmEvalT16Lo12 32 256 30 [1, 2, 2, 2] [81365582, 40233647, 14363187,
  5076887] [17, 13, 6, 3] rkmMasks_m32_r30 = rkmRow_m32_r30 := bh0_eq (tl1 bk_23)
/-- Kernel trajectory certificate `(m = 32, r = 8)`. -/
theorem rkmTraj_m32_r8 : rkmEvalT16Lo12 32 256 8 [1, 1, 1, 1] [113200996, 16453430, 8645830,
  4586646] [8, 2, 1, 1] rkmMasks_m32_r8 = rkmRow_m32_r8 := bh0_eq (tl1 (tl2 bk_15))
/-- Kernel trajectory certificate `(m = 2, r = 36)`. -/
theorem rkmTraj_m2_r36 : rkmEvalT16Lo12 2 4096 36 [2, 4, 8, 16, 27, 27, 27] [31574976, 30106097,
  24753750, 31713739, 52382339, 3478139, 971833] [2, 3, 4, 7, 17, 2, 1] rkmMasks_m2_r36 =
  rkmRow_m2_r36 := bh0_eq (tl1 bk_21)
/-- Kernel trajectory certificate `(m = 256, r = 9)`. -/
theorem rkmTraj_m256_r9 : rkmEvalT16Lo12 256 32 9 [1, 1, 1] [47226735, 752229, 102447] [11, 2, 2]
  rkmMasks_m256_r9 = rkmRow_m256_r9 := bh0_eq (tl2 bk_9)
/-- Kernel trajectory certificate `(m = 128, r = 27)`. -/
theorem rkmTraj_m128_r27 : rkmEvalT16Lo12 128 64 27 [1, 1, 1, 1] [66787321, 4755464, 873, 1224641]
  [29, 3, 2, 2] rkmMasks_m128_r27 = rkmRow_m128_r27 := bh0_eq (tl1 bk_19)
/-- Kernel trajectory certificate `(m = 16, r = 9)`. -/
theorem rkmTraj_m16_r9 : rkmEvalT16Lo12 16 512 9 [1, 1, 1, 1] [136883334, 52544824, 23473342,
  14153637] [8, 4, 3, 2] rkmMasks_m16_r9 = rkmRow_m16_r9 := bh0_eq (tl2 bk_16)
/-- Kernel trajectory certificate `(m = 64, r = 25)`. -/
theorem rkmTraj_m64_r25 : rkmEvalT16Lo12 64 128 25 [1, 1, 1] [93472319, 11829995, 4199067] [27, 4,
  3] rkmMasks_m64_r25 = rkmRow_m64_r25 := bh0_eq (tl1 bk_18)
/-- Kernel trajectory certificate `(m = 1024, r = 11)`. -/
theorem rkmTraj_m1024_r11 : rkmEvalT16Lo12 1024 8 11 [1, 1] [20435323, 3606233] [12, 3]
  rkmMasks_m1024_r11 = rkmRow_m1024_r11 := bh0_eq (tl2 bk_13)
/-- Kernel trajectory certificate `(m = 256, r = 25)`. -/
theorem rkmTraj_m256_r25 : rkmEvalT16Lo12 256 32 25 [1] [49783411] [31] rkmMasks_m256_r25 =
  rkmRow_m256_r25 := bh0_eq (tl1 bk_16)
/-- Kernel trajectory certificate `(m = 2, r = 13)`. -/
theorem rkmTraj_m2_r13 : rkmEvalT16Lo12 2 4096 13 [1, 2, 4, 8, 12, 12, 12, 12] [45805282, 47474363,
  52069917, 62151016, 28920308, 25433869, 7303394, 3918594] [1, 2, 3, 5, 3, 3, 1, 1] rkmMasks_m2_r13
  = rkmRow_m2_r13 := bh0_eq (tl2 bk_17)
/-- Kernel trajectory certificate `(m = 64, r = 23)`. -/
theorem rkmTraj_m64_r23 : rkmEvalT16Lo12 64 128 23 [1, 1] [103999748, 4070036] [28, 2]
  rkmMasks_m64_r23 = rkmRow_m64_r23 := bh0_eq (tl1 bk_14)
/-- Kernel trajectory certificate `(m = 4, r = 13)`. -/
theorem rkmTraj_m4_r13 : rkmEvalT16Lo12 4 2048 13 [1, 2, 4, 6, 6, 6, 6, 6] [59742462, 61629685,
  76356963, 31720891, 24173774, 7480804, 3918594, 1645808] [2, 3, 6, 3, 3, 1, 1, 1] rkmMasks_m4_r13
  = rkmRow_m4_r13 := bh0_eq (tl1 bk_6)
/-- Kernel trajectory certificate `(m = 4, r = 23)`. -/
theorem rkmTraj_m4_r23 : rkmEvalT16Lo12 4 2048 23 [1, 4, 8, 8, 8] [57570663, 56704524, 78961419,
  24834904, 14295799] [3, 7, 13, 5, 4] rkmMasks_m4_r23 = rkmRow_m4_r23 := bh0_eq (tl1 bk_15)
/-- Kernel trajectory certificate `(m = 64, r = 13)`. -/
theorem rkmTraj_m64_r13 : rkmEvalT16Lo12 64 128 13 [1, 1, 1] [94453625, 4429054, 2524638] [16, 2, 2]
  rkmMasks_m64_r13 = rkmRow_m64_r13 := bh0_eq (tl2 bk_23)
/-- Kernel trajectory certificate `(m = 256, r = 21)`. -/
theorem rkmTraj_m256_r21 : rkmEvalT16Lo12 256 32 21 [1, 1] [48471510, 1010402] [25, 2]
  rkmMasks_m256_r21 = rkmRow_m256_r21 := bh0_eq (tl1 bk_10)
/-- Kernel trajectory certificate `(m = 256, r = 15)`. -/
theorem rkmTraj_m256_r15 : rkmEvalT16Lo12 256 32 15 [1, 1] [47941087, 995405] [18, 2]
  rkmMasks_m256_r15 = rkmRow_m256_r15 := bh0_eq (tl2 bk_22)
/-- Kernel trajectory certificate `(m = 128, r = 20)`. -/
theorem rkmTraj_m128_r20 : rkmEvalT16Lo12 128 64 20 [1, 1] [69910336, 1459788] [24, 2]
  rkmMasks_m128_r20 = rkmRow_m128_r20 := bh0_eq (tl1 bk_11)
/-- Kernel trajectory certificate `(m = 1024, r = 17)`. -/
theorem rkmTraj_m1024_r17 : rkmEvalT16Lo12 1024 8 17 [1] [24276827] [20] rkmMasks_m1024_r17 =
  rkmRow_m1024_r17 := bh0_eq (tl2 bk_18)
/-- Kernel trajectory certificate `(m = 4, r = 19)`. -/
theorem rkmTraj_m4_r19 : rkmEvalT16Lo12 4 2048 19 [1, 3, 7, 7, 7] [57169081, 60625881, 81410814,
  25829029, 16353713] [3, 5, 11, 5, 3] rkmMasks_m4_r19 = rkmRow_m4_r19 := bh0_eq (tl2 bk_20)
/-- Krotov trajectory `(m = 8, r = 128)`. -/
theorem rkmTrajPack_m8_r128 : rkmEvalT16Lo12 8 1024 128 [1,2,4,9,18,30,30,30]
  [13603651,12476160,16113899,16271941,21849272,12283935,12579904,2686133] [2,4,8,16,36,29,30,7]
  rkmMasksPack_m8_r128 = rkmRowPack_m8_r128 :=
    bhW_eq bk_8 (wSkip (wSkip (wSkip (wSkip (wCons ws_rkmTrajPack_m8_r128_s4 (wCons
      ws_rkmTrajPack_m8_r128_s5 (wCons ws_rkmTrajPack_m8_r128_s6 wNil)))))))
/-- Krotov trajectory `(m = 2, r = 3)`. -/
theorem rkmTrajPack_m2_r3 : rkmEvalT16Lo12 2 4096 3 [1,2,2,2] [162349218,245512918,18317255,9330790]
  [2,3,1,1] rkmMasksPack_m2_r3 = rkmRowPack_m2_r3 := bh0_eq (tl2 bk_6)
/-- Krotov trajectory `(m = 64, r = 96)`. -/
theorem rkmTrajPack_m64_r96 : rkmEvalT16Lo12 64 128 96 [1,1,1,1,2,2,2,2]
  [2407052,11495891,27642707,17183461,6841,5683076,2721,478701] [2,9,20,13,1,7,1,1]
  rkmMasksPack_m64_r96 = rkmRowPack_m64_r96 :=
    bhW_eq bk_6 (wSkip (wSkip (wCons (bSlideChk_sound bk_22) wNil)))
/-- Krotov trajectory `(m = 2, r = 6)`. -/
theorem rkmTrajPack_m2_r6 : rkmEvalT16Lo12 2 4096 6 [1,2,4,5,5,5,5,5]
  [99205924,83754727,76675552,29671325,33941734,17758523,4800941,6719709] [1,2,2,1,1,1,1,1]
  rkmMasksPack_m2_r6 = rkmRowPack_m2_r6 := bh0_eq (tl2 bk_7)
/-- Krotov trajectory `(m = 64, r = 44)`. -/
theorem rkmTrajPack_m64_r44 : rkmEvalT16Lo12 64 128 44 [1,1,1] [121181129,3312803,4647746] [49,2,2]
  rkmMasksPack_m64_r44 = rkmRowPack_m64_r44 := bh0_eq bk_9
/-- Krotov trajectory `(m = 16, r = 7)`. -/
theorem rkmTrajPack_m16_r7 : rkmEvalT16Lo12 16 512 7 [1,1,1,1,1,1,1,1]
  [64463342,43382148,20590604,18604182,9740885,24833666,19558259,11415810] [3,2,1,1,1,1,1,1]
  rkmMasksPack_m16_r7 = rkmRowPack_m16_r7 := bh0_eq (tl1 (tl2 bk_19))
/-- Krotov trajectory `(m = 8, r = 44)`. -/
theorem rkmTrajPack_m8_r44 : rkmEvalT16Lo12 8 1024 44 [1,2,4,8,10,10,10]
  [33686902,23894884,29551141,22809142,40205217,3850449,4837310] [3,4,8,10,19,2,3]
  rkmMasksPack_m8_r44 = rkmRowPack_m8_r44 := bh0_eq bk_16
/-- Krotov trajectory `(m = 2, r = 9)`. -/
theorem rkmTrajPack_m2_r9 : rkmEvalT16Lo12 2 4096 9 [1,2,4,8,8,8,8,8]
  [77132972,57901824,93604557,34441630,39893014,10440199,5248501,4252308] [1,2,3,2,2,1,1,1]
  rkmMasksPack_m2_r9 = rkmRowPack_m2_r9 := bh0_eq (tl1 (tl2 bk_22))
/-- Krotov trajectory `(m = 16, r = 35)`. -/
theorem rkmTrajPack_m16_r35 : rkmEvalT16Lo12 16 512 35 [1,2,3,3,3,3]
  [57406177,28883921,51971781,28541699,12291176,5972266] [7,6,15,8,4,2] rkmMasksPack_m16_r35 =
  rkmRowPack_m16_r35 := bh0_eq bk_20
/-- Krotov trajectory `(m = 4, r = 18)`. -/
theorem rkmTrajPack_m4_r18 : rkmEvalT16Lo12 4 2048 18 [1,4] [93685581,82794052] [3,7]
  rkmMasksPack_m4_r18 = rkmRowPack_m4_r18 := bh0_eq (tl1 (tl2 bk_23))
/-- Krotov trajectory `(m = 16, r = 32)`. -/
theorem rkmTrajPack_m16_r32 : rkmEvalT16Lo12 16 512 32 [1,2,4,4,4,4,4,4]
  [65019026,38776081,26718022,22786501,7746746,2707959,330279,939757] [8,8,9,8,3,1,1,1]
  rkmMasksPack_m16_r32 = rkmRowPack_m16_r32 := bh0_eq (tl1 bk_22)
/-- Krotov trajectory `(m = 64, r = 11)`. -/
theorem rkmTrajPack_m64_r11 : rkmEvalT16Lo12 64 128 11 [1,1,1] [93635950,4202992,2218841] [12,1,1]
  rkmMasksPack_m64_r11 = rkmRowPack_m64_r11 := bh0_eq (tl2 bk_12)
/-- Krotov trajectory `(m = 64, r = 28)`. -/
theorem rkmTrajPack_m64_r28 : rkmEvalT16Lo12 64 128 28 [1,1,1,1,1,1,1,1]
  [33481532,28288148,14397804,11433425,10517999,4605518,5179357,3862497] [10,8,4,4,3,2,2,2]
  rkmMasksPack_m64_r28 = rkmRowPack_m64_r28 := bh0_eq (tl1 bk_20)
/-- Krotov trajectory `(m = 4, r = 21)`. -/
theorem rkmTrajPack_m4_r21 : rkmEvalT16Lo12 4 2048 21 [1,1,3,6,6,6,6,6]
  [50014757,38014072,60365437,69258,1056144,388543,1319418,512657] [2,2,5,1,1,1,1,1]
  rkmMasksPack_m4_r21 = rkmRowPack_m4_r21 := bh0_eq (tl2 bk_14)
/-- Krotov trajectory `(m = 32, r = 26)`. -/
theorem rkmTrajPack_m32_r26 : rkmEvalT16Lo12 32 256 26 [1,2,2] [102721401,27743375,15397111]
  [18,8,5] rkmMasksPack_m32_r26 = rkmRowPack_m32_r26 := bh0_eq (tl1 bk_17)
/-- Krotov trajectory `(m = 2, r = 18)`. -/
theorem rkmTrajPack_m2_r18 : rkmEvalT16Lo12 2 4096 18 [1,3,6,12]
  [40006001,49861866,51231933,78699628] [1,2,4,9] rkmMasksPack_m2_r18 = rkmRowPack_m2_r18 :=
    bh0_eq (tl2 bk_15)
/-- Krotov trajectory `(m = 32, r = 23)`. -/
theorem rkmTrajPack_m32_r23 : rkmEvalT16Lo12 32 256 23 [1,1,1,1,2,2,2,2]
  [5679971,28480304,52786535,39615426,6966350,9401931,7400716,4472759] [1,5,9,7,2,3,2,2]
  rkmMasksPack_m32_r23 = rkmRowPack_m32_r23 := bh0_eq (tl1 bk_13)
/-- Krotov trajectory `(m = 8, r = 25)`. -/
theorem rkmTrajPack_m8_r25 : rkmEvalT16Lo12 8 1024 25 [1,1,2,4,4,4,4,4]
  [72319132,14681508,48761869,5461,251761,2364773,1804030,284036] [5,1,5,1,1,1,1,1]
  rkmMasksPack_m8_r25 = rkmRowPack_m8_r25 := bh0_eq (tl2 bk_19)
/-- Krotov trajectory `(m = 64, r = 23)`. -/
theorem rkmTrajPack_m64_r23 : rkmEvalT16Lo12 64 128 23 [1,1] [103983474,4081407] [25,1]
  rkmMasksPack_m64_r23 = rkmRowPack_m64_r23 := bh0_eq (tl1 bk_12)
/-- Krotov trajectory `(m = 32, r = 14)`. -/
theorem rkmTrajPack_m32_r14 : rkmEvalT16Lo12 32 256 14 [1,1,1,1,1,1,1,1]
  [33535682,49580417,21275247,19622382,13968139,7838272,2863333,6877497] [4,6,3,2,2,1,1,1]
  rkmMasksPack_m32_r14 = rkmRowPack_m32_r14 := bh0_eq (tl1 bk_7)
/-- Krotov trajectory `(m = 8, r = 20)`. -/
theorem rkmTrajPack_m8_r20 : rkmEvalT16Lo12 8 1024 20 [1,3,4,4,4]
  [84246448,51425618,33129155,34259272,20499045] [5,6,5,5,3] rkmMasksPack_m8_r20 = rkmRowPack_m8_r20
  := bh0_eq (tl1 bk_9)
/-- Krotov trajectory `(m = 64, r = 17)`. -/
theorem rkmTrajPack_m64_r17 : rkmEvalT16Lo12 64 128 17 [1,1,1,1,1,1,1,1]
  [27845559,23157974,22863337,9341079,6588930,6535566,4699873,2974535] [6,5,5,2,2,2,1,1]
  rkmMasksPack_m64_r17 = rkmRowPack_m64_r17 := bh0_eq (tl1 bk_8)
end
end QuantumComputation.Specs.DickeSol
