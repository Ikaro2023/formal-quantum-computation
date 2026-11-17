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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T8
/-
# Multi-Segment `T_16` Trajectory Part `00` (`FindAllJohnsonRampKickMuxTraj00`)

Certified kernel trajectory evaluations (`29` rows, `37989` substep-coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Prefix-kick masks for `(m = 2, r = 14)`. -/
def rkmMasks_m2_r14 : List (List Bool) := [[], [], [false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 14)`. -/
def rkmRow_m2_r14 : List ℕ := [
  34432848, 30793471, 2934616, 127783993, 325373930, 611126562, 5020897354, 491482242,
  33978067263, 6347222223, 122163752364, 449314397555, 322420685995, 59118285182]
/-- Prefix-kick masks for `(m = 2, r = 16)`. -/
def rkmMasks_m2_r16 : List (List Bool) := [
  [], [], [], [false, false, false, false, true, true, true],
  [true, false, true, false, false, true, false, false, true, true],
  [true, false, true, false, false, false, false, false, false, false, false, true],
  [false, false, true, false, false, true, true, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 16)`. -/
def rkmRow_m2_r16 : List ℕ := [
  4978364, 7218815, 267255442, 367474644, 75638716, 562701158, 221794598, 37856025, 7203677945,
  2120346280, 2745112453, 1088724964, 81343428427, 451633910058, 379843201533, 72471541568]
/-- Prefix-kick masks for `(m = 4, r = 10)`. -/
def rkmMasks_m4_r10 : List (List Bool) := [
  [], [false, true], [true, true, false, false, true, true],
  [false, true, false, false, true, false, false, true], [true, true],
  [false, false, false, false, true, true, true, false, true],
  [false, false, false, false, false, true, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 10)`. -/
def rkmRow_m4_r10 : List ℕ := [
  114048286, 61484311, 1126974, 6834588, 7007209336, 1678995309, 10040201881, 1624140,
  241288732131, 739762564718]
/-- Prefix-kick masks for `(m = 4, r = 11)`. -/
def rkmMasks_m4_r11 : List (List Bool) := [
  [], [], [false, false, false, false, false, true],
  [false, true, false, true, false, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 11)`. -/
def rkmRow_m4_r11 : List ℕ := [
  4527606, 103114362, 499669850, 1190181668, 157282466, 2251500387, 3015963, 8896801122,
  7178570680, 207653212068, 772046697557]
/-- Mask chunk for `(m = 4, r = 24)`. -/
def rkmMkP_m4_r24_s4_p0 : List Bool := [
  false, false, false, false, false, true, true, true, false, true, true, true, true, false,
  false, true, true, false, false, false, true, true]
/-- Mask chunk for `(m = 4, r = 24)`. -/
def rkmMkP_m4_r24_s5_p0 : List Bool := [
  false, true, true, true, false, true, true, false, true, false, false, true, false, true, false,
  true, false, true, false, true]
/-- Prefix-kick masks for `(m = 4, r = 24)`. -/
def rkmMasks_m4_r24 : List (List Bool) := [
  [], [], [], [], rkmMkP_m4_r24_s4_p0, rkmMkP_m4_r24_s5_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 24)`. -/
def rkmRow_m4_r24 : List ℕ := [
  0, 35, 20, 310, 17556, 2778, 25257, 291658, 32958, 446701, 22956371, 48507645, 41455773,
  588138161, 210080530, 3347526094, 791840627, 10834829641, 654261945, 1185558791, 36195819349,
  285443671, 180616622058, 765176141688]
/-- Mask chunk for `(m = 8, r = 16)`. -/
def rkmMkP_m8_r16_s2_p0 : List Bool := [
  true, true, false, false, true, true, false, false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 8, r = 16)`. -/
def rkmMkP_m8_r16_s3_p0 : List Bool := [
  true, true, false, false, true, false, true, false, true, false, true, false, false, false,
  true]
/-- Prefix-kick masks for `(m = 8, r = 16)`. -/
def rkmMasks_m8_r16 : List (List Bool) := [
  [], [true], rkmMkP_m8_r16_s2_p0, rkmMkP_m8_r16_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 16)`. -/
def rkmRow_m8_r16 : List ℕ := [
  11, 16443, 457, 372972, 4109817, 39692230, 112504874, 594191448, 630709352, 2838965403,
  1229943262, 1238533943, 19520785334, 87601053, 85158783522, 888543787535]
/-- Mask chunk for `(m = 8, r = 28)`. -/
def rkmMkP_m8_r28_s3_p0 : List Bool := [
  false, false, true, true, false, true, false, false, true, true, true, true, true, true, true,
  true, true, true, false, false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 8, r = 28)`. -/
def rkmMkP_m8_r28_s4_p0 : List Bool := [
  false, true, false, true, false, true, false, true, false, false, true, false, true, true, true,
  false, true, true, false, true]
/-- Prefix-kick masks for `(m = 8, r = 28)`. -/
def rkmMasks_m8_r28 : List (List Bool) := [
  [], [], [], rkmMkP_m8_r28_s3_p0, rkmMkP_m8_r28_s4_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 28)`. -/
def rkmRow_m8_r28 : List ℕ := [
  4, 0, 0, 42, 28, 14, 1230, 45479, 62508, 76295, 1641060, 528531, 8565649, 3598, 84267985,
  29583258, 87491222, 618908424, 101687048, 1943468332, 4394205, 3347002216, 4841068554,
  1853875246, 70749439267, 3019965641, 215473884395, 697834039254]
/-- Mask chunk for `(m = 16, r = 15)`. -/
def rkmMkP_m16_r15_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true]
/-- Mask chunk for `(m = 16, r = 15)`. -/
def rkmMkP_m16_r15_s2_p0 : List Bool := [
  true, false, true, false, true, false, true, true, false, false, true, false, true, true]
/-- Prefix-kick masks for `(m = 16, r = 15)`. -/
def rkmMasks_m16_r15 : List (List Bool) := [
  rkmMkP_m16_r15_s0_p0,
  [true, true, false, true, false, true, false, false, true, false, true, true],
  rkmMkP_m16_r15_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 15)`. -/
def rkmRow_m16_r15 : List ℕ := [
  0, 24, 19129, 584726, 8772845, 12249026, 6777, 84987702, 96073588, 314174808, 6618218243,
  2371400212, 1008269582, 44762421807, 944722821395]
/-- Prefix-kick masks for `(m = 32, r = 6)`. -/
def rkmMasks_m32_r6 : List (List Bool) := [
  [], [true], [true, true, false, false, true, true, true], [false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 6)`. -/
def rkmRow_m32_r6 : List ℕ := [172926, 7612406, 1621198, 54868258, 30903348367, 969032306327]
/-- Mask chunk for `(m = 32, r = 14)`. -/
def rkmMkP_m32_r14_s1_p0 : List Bool := [
  false, true, false, true, false, false, true, false, true, true, false, true, true]
/-- Prefix-kick masks for `(m = 32, r = 14)`. -/
def rkmMasks_m32_r14 : List (List Bool) := [
  [false, true, false, true, false, false, true, true, false, true, true], rkmMkP_m32_r14_s1_p0,
  []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 14)`. -/
def rkmRow_m32_r14 : List ℕ := [
  9, 3, 5851, 3268, 1485, 277328, 20965051, 4947187, 430679, 584365903, 1360104409, 78585895,
  18647657709, 979302655101]
/-- Mask chunk for `(m = 32, r = 40)`. -/
def rkmMkP_m32_r40_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, true, true, true, true, true, true, false,
  false, false, true, true, false, false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 32, r = 40)`. -/
def rkmMkP_m32_r40_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, false, false, false, false, false,
  false, true, false, true, false, true, false, true, false, true]
/-- Prefix-kick masks for `(m = 32, r = 40)`. -/
def rkmMasks_m32_r40 : List (List Bool) := [
  [], [], rkmMkP_m32_r40_s2_p0, rkmMkP_m32_r40_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 40)`. -/
def rkmRow_m32_r40 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 20, 329, 2453, 6014, 9611, 11611,
  816, 17450, 682866, 399364, 11730814, 5919994, 148996254, 47845744, 1507194695, 105955117,
  9761873650, 2048134521, 21543601166, 964817616574]
/-- Prefix-kick masks for `(m = 64, r = 9)`. -/
def rkmMasks_m64_r9 : List (List Bool) := [
  [], [false, true, true, false, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 9)`. -/
def rkmRow_m64_r9 : List ℕ := [
  1, 202, 4056, 268528, 2025474, 115891362, 25115332, 19625884097, 980230810865]
/-- Mask chunk for `(m = 64, r = 21)`. -/
def rkmMkP_m64_r21_s0_p0 : List Bool := [
  false, true, true, true, true, false, false, true, false, false, true, true, false, false, true,
  true, false, false, true, true]
/-- Prefix-kick masks for `(m = 64, r = 21)`. -/
def rkmMasks_m64_r21 : List (List Bool) := [rkmMkP_m64_r21_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 21)`. -/
def rkmRow_m64_r21 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 59, 760, 14471, 95005, 1254296, 5032616, 57980084, 107664679,
  1432033076, 9645972, 10602993483, 987783285235]
/-- Mask chunk for `(m = 64, r = 28)`. -/
def rkmMkP_m64_r28_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, false, true, false, false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 64, r = 28)`. -/
def rkmMkP_m64_r28_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, true, false, true, false, true, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 64, r = 28)`. -/
def rkmMasks_m64_r28 : List (List Bool) := [rkmMkP_m64_r28_s0_p0, rkmMkP_m64_r28_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 28)`. -/
def rkmRow_m64_r28 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 186, 1187, 3240, 49520, 90728, 2026409, 3859162,
  65300326, 225249899, 211651407, 909492582, 72618381, 9476508781, 989033147746]
/-- Prefix-kick masks for `(m = 128, r = 6)`. -/
def rkmMasks_m128_r6 : List (List Bool) := [
  [false, true, true, true], [true, false, true, false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 6)`. -/
def rkmRow_m128_r6 : List ℕ := [160, 76981, 7735, 6159545, 26955843855, 973037911657]
/-- Mask chunk for `(m = 128, r = 18)`. -/
def rkmMkP_m128_r18_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, true, true, true, true, true, true,
  true]
/-- Mask chunk for `(m = 128, r = 18)`. -/
def rkmMkP_m128_r18_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, false, false, false, true,
  false, true, true]
/-- Mask chunk for `(m = 128, r = 18)`. -/
def rkmMkP_m128_r18_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, true, false, true, false,
  false, false, true]
/-- Prefix-kick masks for `(m = 128, r = 18)`. -/
def rkmMasks_m128_r18 : List (List Bool) := [
  rkmMkP_m128_r18_s0_p0, rkmMkP_m128_r18_s1_p0, rkmMkP_m128_r18_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 18)`. -/
def rkmRow_m128_r18 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 150, 17180, 240496, 33008340, 94520116, 29928631, 9787515114,
  990054769662]
/-- Mask chunk for `(m = 128, r = 25)`. -/
def rkmMkP_m128_r25_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 128, r = 25)`. -/
def rkmMkP_m128_r25_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  true, true, false, true, false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 25)`. -/
def rkmMasks_m128_r25 : List (List Bool) := [rkmMkP_m128_r25_s0_p0, rkmMkP_m128_r25_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 25)`. -/
def rkmRow_m128_r25 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 5, 42, 9371, 106579, 4400487, 1229824, 16126613,
  212548728, 9034720, 7588578563, 992167964580]
/-- Mask chunk for `(m = 128, r = 28)`. -/
def rkmMkP_m128_r28_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, false, false, false, true, true]
/-- Mask chunk for `(m = 128, r = 28)`. -/
def rkmMkP_m128_r28_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, true, false, false, true, false, true, false, false, true, true]
/-- Mask chunk for `(m = 128, r = 28)`. -/
def rkmMkP_m128_r28_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 28)`. -/
def rkmMasks_m128_r28 : List (List Bool) := [
  rkmMkP_m128_r28_s0_p0, rkmMkP_m128_r28_s1_p0, rkmMkP_m128_r28_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 28)`. -/
def rkmRow_m128_r28 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 435, 109, 394, 7453, 499402, 17145999, 25005789,
  9540831, 401744586, 37480, 7078279314, 992467737596]
/-- Mask chunk for `(m = 128, r = 32)`. -/
def rkmMkP_m128_r32_s1_p0 : List Bool := [
  false, false, true, false, true, true, true, false, false, false, true, true, false, false,
  true, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 128, r = 32)`. -/
def rkmMkP_m128_r32_s2_p0 : List Bool := [
  false, false, false, true, false, false, false, false, false, true, false, true, false, true,
  true, true, false, true, false, false, true, false, true, false, false, true, true, true]
/-- Mask chunk for `(m = 128, r = 32)`. -/
def rkmMkP_m128_r32_s3_p0 : List Bool := [
  false, false, false, false, true, false, true, false, false, false, true, false, false, true,
  false, false, true, true, false, false, false, true, false, false, true, false, true, false,
  true]
/-- Mask chunk for `(m = 128, r = 32)`. -/
def rkmMkP_m128_r32_s4_p0 : List Bool := [
  false, false, false, false, true, false, true, false, true, false, false, false, false, false,
  false, false, true, true, false, false, false, true, true, false, true, true, true, true, false,
  true]
/-- Mask chunk for `(m = 128, r = 32)`. -/
def rkmMkP_m128_r32_s5_p0 : List Bool := [
  false, false, false, false, false, true, false, false, false, false, false, false, false, false,
  false, false, false, true, false, false, true, true, false, true, false, true]
/-- Mask chunk for `(m = 128, r = 32)`. -/
def rkmMkP_m128_r32_s6_p0 : List Bool := [
  false, false, false, true, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, false, false, false, false, false, false, true,
  false, false, true]
/-- Prefix-kick masks for `(m = 128, r = 32)`. -/
def rkmMasks_m128_r32 : List (List Bool) := [
  [], rkmMkP_m128_r32_s1_p0, rkmMkP_m128_r32_s2_p0, rkmMkP_m128_r32_s3_p0, rkmMkP_m128_r32_s4_p0,
  rkmMkP_m128_r32_s5_p0, rkmMkP_m128_r32_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 32)`. -/
def rkmRow_m128_r32 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 146, 429, 4284, 20640, 328151,
  2878775, 7958288, 1844978, 65235351, 28414786, 67069590, 6287357348, 993538886480]
/-- Mask chunk for `(m = 128, r = 48)`. -/
def rkmMkP_m128_r48_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, false, true,
  false, false, true, true, true, false, false, true, true, false, false, true, true, true, true,
  false, false, false, false, false, false, true, false, true, true, false, true, true, true,
  true]
/-- Mask chunk for `(m = 128, r = 48)`. -/
def rkmMkP_m128_r48_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, true, false, true, false, false, true, true, true, false, true,
  false, true, true, true, false, true, false, false, false, true, true, false, false, false,
  true, true, false, false, true, true]
/-- Mask chunk for `(m = 128, r = 48)`. -/
def rkmMkP_m128_r48_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, false, false, false, false, false, false, true, false, false, false,
  false, true, false, true]
/-- Prefix-kick masks for `(m = 128, r = 48)`. -/
def rkmMasks_m128_r48 : List (List Bool) := [
  rkmMkP_m128_r48_s0_p0, rkmMkP_m128_r48_s1_p0, rkmMkP_m128_r48_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 48)`. -/
def rkmRow_m128_r48 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 2, 86,
  948, 1495, 57, 2620, 108719, 590827, 2108859, 41586, 7887755, 516992127, 168077129, 303957,
  225947712, 1311084226, 158965492, 5954734370, 991653150477]
/-- Prefix-kick masks for `(m = 256, r = 5)`. -/
def rkmMasks_m256_r5 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 5)`. -/
def rkmRow_m256_r5 : List ℕ := [1855, 34957, 201810811, 31703441115, 968094711204]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s1_p0 : List Bool := [
  true, false, false, false, false, false, false, true, false, false, false, false, false, true,
  true, true, false, false, false, false, false, true, false, false, false, false, false, false,
  true, false, true, true, true, true, true, true, true, false, false, false, false, false, false,
  false, true, true, false, false, true, true, true, true, false, true, true, false, false, false,
  true, true, true, false, false, false]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s1_p1 : List Bool := [
  false, false, false, true, true, true, true, true, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, true, true, true, true, true, true, true, true, true]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s1_p2 : List Bool := [true]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s2_p0 : List Bool := [
  true, true, true, true, true, false, false, true, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, true, true, true, false, true, true,
  false, false, false, false, true, false, true, false, true, false, false, false, true, false,
  false, true, false, true, false, false, false, false]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s2_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  true, false, false, false, true, false, true, true, false, false, true, true, false, false,
  true, false, false, true, true, true]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s3_p0 : List Bool := [
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  true, true, false, false, false, false, false, false, false, true, false, true, false, false,
  false, false, false, false, true, false, false, true, false, false, true, false, false, true,
  false, false, false, true, true, false, false, true, true, true, true, true, false, true, true,
  false, false, true, false, false, false, false]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s3_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, true, true, false, true, false, true, false, true,
  false, false, true, false, true, true, true]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s4_p0 : List Bool := [
  true, false, false, true, false, false, false, false, false, false, false, false, false, false,
  true, true, false, false, false, true, false, false, false, false, false, true, false, false,
  false, false, false, false, false, false, false, true, true, false, true, false, true, false,
  false, false, true, false, false, true, true, true, true, true, true, false, false, false,
  false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s4_p1 : List Bool := [
  false, false, true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, false, false, false, true, false, false, false, false, true,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, true, false, false,
  true, false, true, false, true, true, true, true]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s5_p0 : List Bool := [
  true, true, false, true, false, false, false, false, false, false, true, false, false, false,
  false, true, true, false, false, true, false, false, false, true, false, true, false, true,
  false, false, false, false, false, false, false, false, true, false, true, false, false, true,
  false, false, false, true, false, true, true, true, false, true, false, true, false, false,
  false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s5_p1 : List Bool := [
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, false, false, false, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true, true,
  true, true, true, true, true, true]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s6_p0 : List Bool := [
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, false, false, false, true, false, false, false, true, false, false, false,
  true, false, false, false, true, false, false, true, false, false, false, false, true, false,
  false, true, false, false, false, true, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 256, r = 128)`. -/
def rkmMkP_m256_r128_s6_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, false, false, true, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, false, false, false, true, true]
/-- Prefix-kick masks for `(m = 256, r = 128)`. -/
def rkmMasks_m256_r128 : List (List Bool) := [
  [false, true, true, false, false, false, true],
  rkmMkP_m256_r128_s1_p0 ++ rkmMkP_m256_r128_s1_p1 ++ rkmMkP_m256_r128_s1_p2,
  rkmMkP_m256_r128_s2_p0 ++ rkmMkP_m256_r128_s2_p1,
  rkmMkP_m256_r128_s3_p0 ++ rkmMkP_m256_r128_s3_p1,
  rkmMkP_m256_r128_s4_p0 ++ rkmMkP_m256_r128_s4_p1,
  rkmMkP_m256_r128_s5_p0 ++ rkmMkP_m256_r128_s5_p1,
  rkmMkP_m256_r128_s6_p0 ++ rkmMkP_m256_r128_s6_p1, []]
/-- Row chunk `0` `(m = 256, r = 128)`. -/
def rkmRowP_m256_r128_p0 : List ℕ := [
  0, 0, 0, 2, 2, 4, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 5, 0,
  0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 7, 12, 113, 990, 3647, 1532, 3369, 1233,
  1432, 1824, 945, 1, 170, 493, 1576]
/-- Row chunk `1` `(m = 256, r = 128)`. -/
def rkmRowP_m256_r128_p1 : List ℕ := [
  499, 1185, 2332, 619, 117, 76, 632, 1302, 1382, 1271, 525, 4, 409, 1210, 1497, 1279, 544, 0,
  562, 1210, 1295, 1875, 148, 28, 78, 2317, 3291, 162, 186, 10, 468, 94, 29, 152, 45, 10, 21, 199,
  391, 113, 0, 62, 140, 1438, 8307, 3366, 831, 1117, 811, 2043, 52013, 162917, 508194, 19,
  3851197, 111045, 34287078, 3395024, 68101348, 1972204243, 238560329, 24517286, 2335119391,
  995319053520]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 128)`. -/
def rkmRow_m256_r128 : List ℕ := rkmRowP_m256_r128_p0 ++ rkmRowP_m256_r128_p1
/-- Mask chunk for `(m = 512, r = 18)`. -/
def rkmMkP_m512_r18_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, true]
/-- Mask chunk for `(m = 512, r = 18)`. -/
def rkmMkP_m512_r18_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, true, true]
/-- Prefix-kick masks for `(m = 512, r = 18)`. -/
def rkmMasks_m512_r18 : List (List Bool) := [rkmMkP_m512_r18_s0_p0, rkmMkP_m512_r18_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 18)`. -/
def rkmRow_m512_r18 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 669, 13135, 948, 2412648, 1490748, 8797875237, 991198206073]
/-- Mask chunk for `(m = 512, r = 24)`. -/
def rkmMkP_m512_r24_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 512, r = 24)`. -/
def rkmMkP_m512_r24_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 512, r = 24)`. -/
def rkmMasks_m512_r24 : List (List Bool) := [rkmMkP_m512_r24_s0_p0, rkmMkP_m512_r24_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 24)`. -/
def rkmRow_m512_r24 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 801, 3032, 13716, 6971628, 27295916,
  6679996995, 993285717096]
/-- Mask chunk for `(m = 512, r = 31)`. -/
def rkmMkP_m512_r31_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, true, true, true]
/-- Mask chunk for `(m = 512, r = 31)`. -/
def rkmMkP_m512_r31_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, true, false,
  false, true, true]
/-- Prefix-kick masks for `(m = 512, r = 31)`. -/
def rkmMasks_m512_r31 : List (List Bool) := [rkmMkP_m512_r31_s0_p0, rkmMkP_m512_r31_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 31)`. -/
def rkmRow_m512_r31 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 50, 717, 127739, 124385,
  13840703, 16679461, 5179583201, 994789642406]
/-- Prefix-kick masks for `(m = 1024, r = 4)`. -/
def rkmMasks_m1024_r4 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 4)`. -/
def rkmRow_m1024_r4 : List ℕ := [3026167, 547737677, 39345763150, 960103467444]
/-- Prefix-kick masks for `(m = 1024, r = 7)`. -/
def rkmMasks_m1024_r7 : List (List Bool) := [[], [], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 7)`. -/
def rkmRow_m1024_r7 : List ℕ := [0, 0, 117, 355106, 156122925, 22234827790, 977608693878]
/-- Prefix-kick masks for `(m = 1024, r = 15)`. -/
def rkmMasks_m1024_r15 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 15)`. -/
def rkmRow_m1024_r15 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 798, 177941, 4303362, 10327982601, 989667534845]
/-- Prefix-kick masks for `(m = 1024, r = 28)`. -/
def rkmMasks_m1024_r28 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 28)`. -/
def rkmRow_m1024_r28 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 127, 984, 993388, 32619497,
  5584608551, 994381776063]
/-- Unpacks `j` LSB-first bits of `< 2 ^ 50` word `w` (`FindAllJohnsonRampKickMuxTraj00`). -/
def rkmWbTraj00 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWbTraj00 j (Nat.div w 2)
/-- Concatenates `50`-bit `< 2 ^ 50` chunks (final length `rem`) into a `List Bool` mask. -/
def rkmMaskWordsTraj00 : ℕ → List ℕ → List Bool
  | _, [] => []
  | rem, [w] => rkmWbTraj00 rem w
  | rem, w :: v :: ws => rkmWbTraj00 50 w ++ rkmMaskWordsTraj00 rem (v :: ws)
/-- Krotov masks `(m = 64, r = 128)`. -/
def rkmMasksPack_m64_r128 : List (List Bool) := [rkmMaskWordsTraj00 1 [0,1],
  rkmMaskWordsTraj00 47 [92358976733184,70368744177684],
  rkmMaskWordsTraj00 28 [826482884864547,1089087148840413,204996608],
  rkmMaskWordsTraj00 23 [639398858688754,516037457302054,7464550],
  rkmMaskWordsTraj00 26 [5775978676584,303533939085380,40725493],
  rkmMaskWordsTraj00 27 [18990537851082,22821552228,71365888],
  rkmMaskWordsTraj00 21 [17936123428864,74772159434772,1114368],[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 128)`. -/
def rkmRowPack_m64_r128 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,43,
  162,1,0,6,55,38,2,236,1086,298,1,650,6036,19,151,205,4685,3126,63,98,141,24,2176,75,208,1752,34,
  53,7895,11678,1164,2122,13166,3453,2694,3936,2971,1212,2130,5493,1593,0,10,2260,182,620,61499,
  2812,527,52985,243361,22930,1236388,1700330,806863,894460,1198489,74793,1577983,4238,151339,
  22956410,676690,48146,309497,604982,1516743,10400139,3962556,227516,11062325,7275363,2166997,
  23481496,7925719,5843023,26351622,47573376,1077097,10546652,1667102,14721874,3514615,54716169,
  323235884,329144534,36041330,312952003,1690605996,48022389,3661037116,2742018879,239282922,
  2675439288,7862945935,43170188,9369136335,970400214795]
/-- Krotov masks `(m = 2, r = 19)`. -/
def rkmMasksPack_m2_r19 : List (List Bool) := [[]]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 19)`. -/
def rkmRowPack_m2_r19 : List ℕ := [345418005319,617454486468]
/-- Krotov masks `(m = 8, r = 80)`. -/
def rkmMasksPack_m8_r80 : List (List Bool) := [[],[],rkmWbTraj00 32 3221225476,
  rkmMaskWordsTraj00 11 [6920365659,1564],rkmMaskWordsTraj00 30 [620012489839978,1040187469],
  rkmMaskWordsTraj00 30 [288417340318720,939526417],[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 80)`. -/
def rkmRowPack_m8_r80 : List ℕ := [1009548,7198651,15680851,75910351,3160007,3634,16425475,
  51777201,17284987,11686470,82565259,2404811,14459112,5897796,5437341,198833879,516430,575271,
  2454897,15120465,30367892,2714620,85532190,132752340,3533228,65559310,52917170,2457380,1443644,
  1318246,37953843,144032938,42881820,3136932,27129225,34845871,23643452,940,123991094,51575902,
  114973,2434840,97398686,1645917,182476307,25424568,91903275,75817978,76161789,3864534,627858445,
  303852928,71517114,1434000,252150600,1319146272,1201810720,259501923,3858396884,4372079814,
  570946442,13010885507,25917006716,6844965462,10527479638,98312067858,212715248364,250248465171,
  194917878236,108857761866,45302973301,14366658324,3394732948,748085268,43383696,7537,176747,
  22345,924,3]
/-- Krotov masks `(m = 4, r = 6)`. -/
def rkmMasksPack_m4_r6 : List (List Bool) := [[],rkmWbTraj00 4 12,rkmWbTraj00 5 18,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 6)`. -/
def rkmRowPack_m4_r6 : List ℕ := [370000401,89709207,2539340873,599096684,164863796230,
  831475910698]
/-- Krotov masks `(m = 8, r = 48)`. -/
def rkmMasksPack_m8_r48 : List (List Bool) := [[],[],rkmWbTraj00 3 6,rkmWbTraj00 47 114349216163768,
  rkmWbTraj00 36 61147868501,rkmWbTraj00 46 56232166934746,rkmWbTraj00 47 70369282097179,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 48)`. -/
def rkmRowPack_m8_r48 : List ℕ := [3141415,3629147,1299171,17940046,2199424,993829,5741173,
  4971914,6393206,12196202,42725321,25717895,565162,5901063,37226937,54522768,34256651,7801839,
  7726643,109635901,44116798,293957629,288394441,243088219,289581694,199285171,30367147,840775716,
  186512729,247966118,907038467,104850361,489937767,68384573,1206188946,29464997,286662145,
  1560338147,1037507657,2054210908,55111329,4786456382,1560284258,5698951238,31586080509,107236,
  84957431168,860562359275]
/-- Krotov masks `(m = 8, r = 31)`. -/
def rkmMasksPack_m8_r31 : List (List Bool) := [rkmWbTraj00 8 159,rkmWbTraj00 7 127,[],
  rkmWbTraj00 8 255,rkmWbTraj00 8 255,rkmWbTraj00 3 4,rkmWbTraj00 3 4,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 31)`. -/
def rkmRowPack_m8_r31 : List ℕ := [605151,32084149,3230172606,26461123719,145744246878,
  267550489201,520178712549,36768461754]
/-- Krotov masks `(m = 32, r = 40)`. -/
def rkmMasksPack_m32_r40 : List (List Bool) := [rkmWbTraj00 31 2122317823,rkmWbTraj00 32 4294964519,
  rkmWbTraj00 39 439783870995,rkmWbTraj00 37 91680082966,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 40)`. -/
def rkmRowPack_m32_r40 : List ℕ := [2458137,2901,1736728,6860867,13192140,5769011,121942,950280,
  533865,235623,414813,200553,761792,4086,13055333,6477,2098709,1857423,9793078,16,5532866,
  1455645,137041,493259,672793,692051,66217,1813802,27528463,225333,171638623,17586168,679129547,
  62440934,3781293257,6843402,14720071208,5230165769,18844997347,956387159788]
/-- Krotov masks `(m = 64, r = 9)`. -/
def rkmMasksPack_m64_r9 : List (List Bool) := [[],rkmWbTraj00 8 198,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 9)`. -/
def rkmRowPack_m64_r9 : List ℕ := [1,202,4051,267881,2012586,115720094,24490592,19626779072,
  980230725441]
/-- Krotov masks `(m = 64, r = 32)`. -/
def rkmMasksPack_m64_r32 : List (List Bool) := [rkmWbTraj00 32 3758096384,rkmWbTraj00 24 12911936,
  rkmWbTraj00 25 23967648,rkmWbTraj00 27 110611520,rkmWbTraj00 29 403649856,
  rkmWbTraj00 30 1036028672,rkmWbTraj00 31 2119595072,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 32)`. -/
def rkmRowPack_m64_r32 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,196,1477,113,22568,31042,5647,19664,
  120877,1643183,302948,1753798,4840498,20046334,16049172,266387,39167481,138665755,175020079,
  9277589350,990324452825]
/-- Krotov masks `(m = 8, r = 10)`. -/
def rkmMasksPack_m8_r10 : List (List Bool) := [[],rkmWbTraj00 4 14,rkmWbTraj00 8 205,
  rkmWbTraj00 9 297,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 10)`. -/
def rkmRowPack_m8_r10 : List ℕ := [14779605,84727254,41885499,416556498,116124057,184029169,
  7246499446,239243160,76139376640,915509992802]
/-- Krotov masks `(m = 32, r = 56)`. -/
def rkmMasksPack_m32_r56 : List (List Bool) := [rkmWbTraj00 29 469876736,rkmWbTraj00 31 1476395053,
  rkmWbTraj00 22 2901093,rkmWbTraj00 31 1674824061,rkmWbTraj00 36 46843645135,
  rkmWbTraj00 38 206881485357,rkmWbTraj00 40 816112380191,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 56)`. -/
def rkmRowPack_m32_r56 : List ℕ := [4599658,2161425,327582,4828422,11616,4715587,114357,23503860,
  1177071,26667,78920891,58874871,596280,436374,179981396,228199818,34147113,41351617,1357438230,
  5793790849,46447143470,5646070209,34665982901,577004402298,9220629609,158146679117,1234462655,
  74743286872,60437003463,19943981107,3991757185,691224315,9578687,649382,187985,12339,445,5,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Krotov masks `(m = 32, r = 11)`. -/
def rkmMasksPack_m32_r11 : List (List Bool) := [rkmWbTraj00 11 2047,[],[],rkmWbTraj00 6 58,
  rkmWbTraj00 8 202,rkmWbTraj00 9 276,rkmWbTraj00 10 549,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 11)`. -/
def rkmRowPack_m32_r11 : List ℕ := [0,18362,24004,406308,299575,1582484,9282957,10637891,
  226599819,20527096197,979224052320]
/-- Krotov masks `(m = 32, r = 27)`. -/
def rkmMasksPack_m32_r27 : List (List Bool) := [rkmWbTraj00 27 134214081,rkmWbTraj00 24 13007304,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 27)`. -/
def rkmRowPack_m32_r27 : List ℕ := [76,859,980,17569,28594,164,3887,334,105153,91768,1749416,
  6939353,25420948,79307433,187910205,382351358,486445079,301012086,2296,868223754,3555002513,
  3780895203,656884039,8718437999,25712374173,22075208010,933161586196]
/-- Krotov masks `(m = 8, r = 12)`. -/
def rkmMasksPack_m8_r12 : List (List Bool) := [[],rkmWbTraj00 6 57,rkmWbTraj00 9 402,
  rkmWbTraj00 11 1685,rkmWbTraj00 11 1183,rkmWbTraj00 11 1154,rkmWbTraj00 1 1,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 12)`. -/
def rkmRowPack_m8_r12 : List ℕ := [1054881,52165685,63436332,41016347,1695244,213429842,11397903,
  5916678975,8614576252,255324,76370242684,908714015051]
/-- Krotov masks `(m = 32, r = 24)`. -/
def rkmMasksPack_m32_r24 : List (List Bool) := [rkmWbTraj00 17 66048,rkmWbTraj00 14 10789,
  rkmWbTraj00 18 240677,rkmWbTraj00 22 3298630,rkmWbTraj00 23 4750181,rkmWbTraj00 24 15339235,
  rkmWbTraj00 24 10494027,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 24)`. -/
def rkmRowPack_m32_r24 : List ℕ := [19,3,12,116,0,165,97,233,123624,69576,190486,7297273,7899709,
  5570616,134805946,421171409,1721065,648273290,55497917,183792849,6160048249,1006617,20258587431,
  972113942912]
/-- Krotov masks `(m = 16, r = 30)`. -/
def rkmMasksPack_m16_r30 : List (List Bool) := [rkmWbTraj00 14 9216,rkmWbTraj00 16 38912,
  rkmWbTraj00 16 57345,rkmWbTraj00 16 57345,[],[],rkmWbTraj00 4 8,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 30)`. -/
def rkmRowPack_m16_r30 : List ℕ := [76,190209,1224228,798799,45442488,700996957,5929147122,
  29971826826,95077752957,196356345537,263819039684,230197190789,127434947517,42359689474,
  7560528135,544867588]
/-- Krotov masks `(m = 64, r = 21)`. -/
def rkmMasksPack_m64_r21 : List (List Bool) := [[],[],[],rkmWbTraj00 13 7216,rkmWbTraj00 17 111751,
  rkmWbTraj00 19 449114,rkmWbTraj00 20 565672,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 21)`. -/
def rkmRowPack_m64_r21 : List ℕ := [0,0,0,0,0,2,281,1019,10053,4899,2877,123498,215679,5402048,
  2342059,142072,65342803,106563489,125797503,10620931023,989073120427]
/-- Krotov masks `(m = 8, r = 17)`. -/
def rkmMasksPack_m8_r17 : List (List Bool) := [[],rkmWbTraj00 16 65535,rkmWbTraj00 13 6863,
  rkmWbTraj00 15 26927,rkmWbTraj00 16 33086,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 17)`. -/
def rkmRowPack_m8_r17 : List ℕ := [99438,3296816,1097542,172151,5904026,44819664,2069501,5534813,
  352919320,1924467100,521182,1571363318,9337565416,3480425543,530926488,89563628432,893174964995]
/-- Krotov masks `(m = 8, r = 22)`. -/
def rkmMasksPack_m8_r22 : List (List Bool) := [[],rkmWbTraj00 19 420098,rkmWbTraj00 21 1234258,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 22)`. -/
def rkmRowPack_m8_r22 : List ℕ := [27,1423,13090,10889,1313602,4589752,4007,34159,90740419,
  442575954,1100171162,1092354809,1426032410,938083013,228447906,934408179,3656239788,10807472335,
  9718696987,608896692,89042756871,879907155872]
/-- Krotov masks `(m = 64, r = 15)`. -/
def rkmMasksPack_m64_r15 : List (List Bool) := [[],[],rkmWbTraj00 1 1,rkmWbTraj00 8 255,
  rkmWbTraj00 11 1943,rkmWbTraj00 13 6954,rkmWbTraj00 14 8880,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 15)`. -/
def rkmRowPack_m64_r15 : List ℕ := [0,0,0,13,14,365,1343,516311,549093,217620,23479550,22217188,
  96817851,13117499819,986738700670]
/-- Krotov masks `(m = 8, r = 34)`. -/
def rkmMasksPack_m8_r34 : List (List Bool) := [[],rkmWbTraj00 16 65535,rkmWbTraj00 24 8390454,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 34)`. -/
def rkmRowPack_m8_r34 : List ℕ := [309756,504433,32228,11689072,35822554,71223924,805809,66360128,
  50590251,105733173,79925199,255103924,92077814,1235386505,121906748,2953246844,6137061218,
  439415599,52289074116,192152743251,290621199013,249401126053,136959363096,50967965354,
  13205870990,2406926588,308772917,27717243,1720303,72355,1993,33,0,0]
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
private def wc_rkmTraj_m256_r128_s0_hb : List ℕ := pCat [135812532451390, 190942158832965,
  232475739670236, 266845659334327, 296558922508261, 322908830422325, 346668051643575,
  368342839898645, 388286774402472, 406758687470355, 423955017735622, 440029178868987,
  455103802225095, 469278821259285, 482637005929752, 495247867657352, 507170486375027,
  518455603088096, 529147198970434, 539283707386704, 548898958265854, 558022923870025,
  566682314863018, 574901061936689, 582700708824989, 590100735904107, 597118828837800,
  603771103289765, 610072294198263, 616035916227962, 621674400598610, 626999212413543,
  632020951783985, 636749441403960, 641193802729400, 645362522519985, 649263511188627,
  652904154152730, 656291357179493, 659431586554083, 662330904766278, 664995002302099,
  667429226037047, 669638604653189, 671627871440402, 673401484790403, 674963646648732,
  676318319153263, 677469239656799, 678419934304983, 679173730318218, 679733767107052,
  680103006333850, 680284241019279, 680280103779665, 680093074270464, 679725485901578,
  679179531881924, 678457270643268, 677560630686767, 676491414889784, 675251304305242,
  673841861480956, 672264533321945] [670520653514647, 668611444528101, 666538019203502,
  664301381940045, 661902429481532, 659341951304823, 656620629607818, 653739038891151,
  650697645124176, 647496804482043, 644136761636591, 640617647579447, 636939476950932,
  633102144843157, 629105423039798, 624948955648524, 620632254074603, 616154691275762,
  611515495228718, 606713741526619, 601748345013734, 596618050348681, 591321421369912,
  585856829116470, 580222438332661, 574416192256309, 568435795455778, 562278694439633,
  555942055713134, 549422740895649, 542717278440061, 535821831405986, 528732160628938,
  521443582491959, 513950920337535, 506248448346282, 498329826442416, 490188024447306,
  481815233268638, 473202760352294, 464340905893429, 455218815341406, 445824302453512,
  436143635430275, 426161276318935, 415859560631859, 405218299586998, 394214280913274,
  382820634794838, 371006017680114, 358733545761749, 345959377547370, 332630793399799,
  318683535278602, 304038025781400, 288593829622795, 272221243057902, 254747950995469,
  235936677898911, 215445062336470, 192746654047185, 166953845867821, 136333760619300,
  96408365500308]
private def wc_rkmTraj_m256_r128_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTraj_m256_r128_s0_v1 : List ℕ := pCat [2092267454798601, 2204283516274209,
  2317919825646267, 2401563260734515, 2436617992632785, 2422043929424907, 2370142459249220,
  2298699713823954, 2224085998469593, 2157510690005604, 2104375760918879, 2065531045527702,
  2039141299901443, 2022318132361777, 2012183830284405, 2006384161401513, 2003217842167897,
  2001563131930258, 2000733040799673, 2000332362563160, 2000145890854037, 2000062072245702,
  2000025626583978, 2000010276236006, 2000004006038313, 2000001519453565, 2000000561144457,
  2000000201917406, 2000000070836609, 2000000024242553, 2000000008097817, 2000000002641443,
  2000000000841777, 2000000000262189, 2000000000079846, 2000000000023780, 2000000000006927,
  2000000000001972, 2000000000000547, 2000000000000147, 2000000000000037, 2000000000000007,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
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
private def wc_rkmTraj_m256_r128_s0_v2 : List ℕ := pCat [2000054490907705, 2000256274659981,
  2000846978977334, 2002271316259248, 2005241793729475, 2010751690662455, 2020003917699522,
  2034236893860399, 2054459558527025, 2081143889910802, 2113951091143115, 2151574353901804,
  2191761103324791, 2231535038287910, 2267585985771476, 2296750311938516, 2316480618756328,
  2325207401480063, 2322524560194719, 2309174845508064, 2286856819041955, 2257909522561762,
  2224947563994278, 2190516787204574, 2156823422449586, 2125564842397174, 2097865211684622,
  2074299998610206, 2054982268407395, 2039680917774222, 2027944640992442, 2019212694318140,
  2012901798083710, 2008465825892257, 2005430217833907, 2003406070216252, 2002089906333811,
  2001254801682478, 2000737440594275, 2000424328740680, 2000239118319889, 2000131996398121,
  2000071391541298, 2000037840488156, 2000019659635701, 2000010013373461, 2000005000844215,
  2000002449235504, 2000001176530737, 2000000554393102, 2000000256286523, 2000000116244987,
  2000000051737567, 2000000022597458, 2000000009686557, 2000000004075361, 2000000001682967,
  2000000000682212, 2000000000271464, 2000000000106036, 2000000000040657, 2000000000015301,
  2000000000005649, 2000000000002043] (pCat [2000000000000720, 2000000000000247, 2000000000000082,
  2000000000000023, 2000000000000005, 2000000000000000, 2000000000000000, 2000000000000000,
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
private def wc_rkmTraj_m256_r128_s0_ck3 : List ℕ := pCat [2000000000072463, 2000000000575286,
  2000000003207395, 2000000014500694, 2000000056383345, 2000000194731662, 2000000609668370,
  2000001754778899, 2000004691189949, 2000011740261206, 2000027674921827, 2000061755170225,
  2000130985210143, 2000264988985087, 2000512813896950, 2000951720965806, 2001697559690884,
  2002915654296147, 2004830309927502, 2007730233493728, 2011966586268799, 2017940321518883,
  2026076164674272, 2036782207701026, 2050396555483441, 2067125469635862, 2086980450793233,
  2109723975653354, 2134834453989215, 2161499883372732, 2188646516631774, 2215003952603337,
  2239202204866541, 2259890600441636, 2275863988089370, 2286179663243522, 2290249162583462,
  2287892577101493, 2279348630143749, 2265240389886304, 2246502881003161, 2224283881739324,
  2199832042432284, 2174386832292746, 2149082912315987, 2124877950046901, 2102508472728846,
  2082473962537548, 2065045745604013, 2050294767134791, 2038131230291590, 2028349192055954,
  2020670254477667, 2014782077638670, 2010369191023193, 2007135186563058, 2004816642167838,
  2003189964614470, 2002072764743227, 2001321458495687, 2000826627106760, 2000507373962307,
  2000305573417971, 2000180582197211] (pCat [2000104714311845, 2000059580669735, 2000033263360525,
  2000018221248843, 2000009793275601, 2000005164149837, 2000002671594450, 2000001355874408,
  2000000675022953, 2000000329637889, 2000000157885033, 2000000074163813, 2000000034162418,
  2000000015429961, 2000000006832672, 2000000002966006, 2000000001261970, 2000000000526206,
  2000000000214988, 2000000000086044, 2000000000033726, 2000000000012941, 2000000000004855,
  2000000000001777, 2000000000000632, 2000000000000215, 2000000000000069, 2000000000000020,
  2000000000000004, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m256_r128_s1_hb : List ℕ := pCat [135812532451390, 190942158832965,
  232475739670236, 266845659334327, 296558922508261, 322908830422325, 346668051643575,
  368342839898645, 388286774402472, 406758687470355, 423955017735622, 440029178868987,
  455103802225095, 469278821259285, 482637005929752, 495247867657352, 507170486375027,
  518455603088096, 529147198970434, 539283707386704, 548898958265854, 558022923870025,
  566682314863018, 574901061936689, 582700708824989, 590100735904107, 597118828837800,
  603771103289765, 610072294198263, 616035916227962, 621674400598610, 626999212413543,
  632020951783985, 636749441403960, 641193802729400, 645362522519985, 649263511188627,
  652904154152730, 656291357179493, 659431586554083, 662330904766278, 664995002302099,
  667429226037047, 669638604653189, 671627871440402, 673401484790403, 674963646648732,
  676318319153263, 677469239656799, 678419934304983, 679173730318218, 679733767107052,
  680103006333850, 680284241019279, 680280103779665, 680093074270464, 679725485901578,
  679179531881924, 678457270643268, 677560630686767, 676491414889784, 675251304305242,
  673841861480956, 672264533321945] [670520653514647, 668611444528101, 666538019203502,
  664301381940045, 661902429481532, 659341951304823, 656620629607818, 653739038891151,
  650697645124176, 647496804482043, 644136761636591, 640617647579447, 636939476950932,
  633102144843157, 629105423039798, 624948955648524, 620632254074603, 616154691275762,
  611515495228718, 606713741526619, 601748345013734, 596618050348681, 591321421369912,
  585856829116470, 580222438332661, 574416192256309, 568435795455778, 562278694439633,
  555942055713134, 549422740895649, 542717278440061, 535821831405986, 528732160628938,
  521443582491959, 513950920337535, 506248448346282, 498329826442416, 490188024447306,
  481815233268638, 473202760352294, 464340905893429, 455218815341406, 445824302453512,
  436143635430275, 426161276318935, 415859560631859, 405218299586998, 394214280913274,
  382820634794838, 371006017680114, 358733545761749, 345959377547370, 332630793399799,
  318683535278602, 304038025781400, 288593829622795, 272221243057902, 254747950995469,
  235936677898911, 215445062336470, 192746654047185, 166953845867821, 136333760619300,
  96408365500308]
private def wc_rkmTraj_m256_r128_s1_v0 : List ℕ := pCat [2000000000072463, 1999999999424714,
  1999999996792605, 2000000014500694, 2000000056383345, 2000000194731662, 1999999390331630,
  2000001754778899, 2000004691189949, 2000011740261206, 2000027674921827, 2000061755170225,
  2000130985210143, 2000264988985087, 2000512813896950, 2000951720965806, 2001697559690884,
  2002915654296147, 2004830309927502, 2007730233493728, 2011966586268799, 2017940321518883,
  2026076164674272, 2036782207701026, 2050396555483441, 2067125469635862, 2086980450793233,
  2109723975653354, 2134834453989215, 2161499883372732, 2188646516631774, 2215003952603337,
  2239202204866541, 2259890600441636, 2275863988089370, 2286179663243522, 2290249162583462,
  2287892577101493, 2279348630143749, 2265240389886304, 2246502881003161, 2224283881739324,
  2199832042432284, 2174386832292746, 2149082912315987, 2124877950046901, 2102508472728846,
  2082473962537548, 2065045745604013, 2050294767134791, 2038131230291590, 2028349192055954,
  2020670254477667, 2014782077638670, 2010369191023193, 2007135186563058, 2004816642167838,
  2003189964614470, 2002072764743227, 2001321458495687, 2000826627106760, 2000507373962307,
  2000305573417971, 2000180582197211] (pCat [2000104714311845, 2000059580669735, 2000033263360525,
  2000018221248843, 2000009793275601, 2000005164149837, 2000002671594450, 2000001355874408,
  2000000675022953, 2000000329637889, 2000000157885033, 2000000074163813, 2000000034162418,
  2000000015429961, 2000000006832672, 2000000002966006, 2000000001261970, 2000000000526206,
  2000000000214988, 2000000000086044, 2000000000033726, 2000000000012941, 2000000000004855,
  2000000000001777, 2000000000000632, 2000000000000215, 2000000000000069, 2000000000000020,
  2000000000000004, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m256_r128_s1_v1 : List ℕ := pCat [1999999546867362, 2000000291712466,
  2000000272746158, 1999999791303922, 1999999696314202, 2000000042687400, 2000000306978452,
  2000000190509137, 1999999875010103, 1999999697576017, 1999999795745425, 2000000051850188,
  2000000260133719, 2000000296121312, 2000000167182054, 1999999962583589, 1999999778199434,
  1999999670148314, 1999999648510254, 1999999695736558, 1999999791069869, 1999999931614935,
  2000000151635948, 2000000549631464, 2000001338636678, 2000002942070994, 2000006168160728,
  2000012512342408, 2000024659661977, 2000047287072564, 2000088295545302, 2000160627719597,
  2000284838042989, 2000492564266964, 2000830983752529, 2001368206903233, 2002199349603206,
  2003452735232764, 2005295323227269, 2007936090803013, 2011625782644471, 2016651290257603,
  2023323039125705, 2031954244681533, 2042831799036849, 2056179843674227, 2072118642705332,
  2090622965953017, 2111485508055754, 2134291565465219, 2158410967776082, 2183011939660977,
  2207099177170586, 2229575210924925, 2249320567801553, 2265284944822606, 2276579213028966,
  2282557101887566, 2282876164277237, 2277530057111707, 2266847931346702, 2251461179615791,
  2232242173266093, 2210223186902436] (pCat [2186505885131469, 2162172244217743, 2138206638388309,
  2115436369387375, 2094494694503704, 2075807025165906, 2059597986163988, 2045914853102477,
  2034661724615556, 2025638628239651, 2018580427241495, 2013191610069995, 2009174495262360,
  2006249797375956, 2004169674108013, 2002724203360288, 2001742699914332, 2001091418353449,
  2000669083908938, 2000401440120317, 2000235687623864, 2000135377997255, 2000076062118679,
  2000041793179519, 2000022452269859, 2000011790365862, 2000006050531817, 2000003033460399,
  2000001485362905, 2000000710130714, 2000000331365962, 2000000150863223, 2000000066987772,
  2000000028997656, 2000000012231804, 2000000005025376, 2000000002009881, 2000000000782076,
  2000000000295893, 2000000000108772, 2000000000038818, 2000000000013431, 2000000000004498,
  2000000000001453, 2000000000000448, 2000000000000130, 2000000000000034, 2000000000000006,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m256_r128_s1_v2 : List ℕ := pCat [1999999975603350, 1999999924589487,
  1999999843119060, 1999999749759827, 1999999682680642, 1999999684038472, 1999999775315042,
  1999999938184753, 2000000115197379, 2000000233807823, 2000000242524837, 2000000139098431,
  1999999974036437, 1999999826541749, 1999999765604277, 1999999816967099, 1999999952703961,
  2000000107302012, 2000000210342634, 2000000218631694, 2000000132885887, 1999999993299466,
  1999999858804155, 1999999781315675, 1999999786465813, 1999999867451368, 1999999991970522,
  2000000117061147, 2000000204801824, 2000000233187767, 2000000199642662, 2000000117844712,
  2000000010599845, 1999999901991858, 1999999811300054, 1999999749863391, 1999999720828142,
  1999999720929473, 1999999743222889, 1999999779887721, 1999999824689049, 1999999875268925,
  1999999936126731, 2000000024086930, 2000000179571828, 2000000489652698, 2000001133466640,
  2000002468299909, 2000005186905090, 2000010595074078, 2000021084580065, 2000040910859487,
  2000077425663361, 2000142957095078, 2000257562173669, 2000452882517042, 2000777286872033,
  2001302354888054, 2002130515315358, 2003403280099429, 2005309019723524, 2008088650595275,
  2012037050000914, 2017497629641380] (pCat [2024847475682607, 2034470995805150, 2046721243941348,
  2061870044167947, 2080050549826887, 2101198584944356, 2125001465624618, 2150864330206473,
  2177903705199500, 2204975713295980, 2230741998774244, 2253770604390158, 2272662651515564,
  2286190029245936, 2293425696385018, 2293847649963081, 2287400528881186, 2274504857823376,
  2256012021432160, 2233111614347505, 2207205127000570, 2179764566794435, 2152195765632543,
  2125723766087686, 2101312542723711, 2079624662014659, 2061019758993316, 2045585188364681,
  2033188733212796, 2023542107003565, 2016264919323595, 2010941175906371, 2007163473963465,
  2004563106839662, 2002826773458697, 2001702222014950, 2000995913247120, 2000565815016440,
  2000311977349922, 2000166837471998, 2000086474539622, 2000043409246402, 2000021087274876,
  2000009904066386, 2000004492966922, 2000001966557770, 2000000829487733, 2000000336712706,
  2000000131341591, 2000000049147688, 2000000017608761, 2000000006027368, 2000000001966084,
  2000000000609356, 2000000000178818, 2000000000049470, 2000000000012830, 2000000000003095,
  2000000000000683, 2000000000000133, 2000000000000020, 2000000000000001, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTraj_m256_r128_s1_ck3 : List ℕ := pCat [1999999999999255, 1999999999995100,
  1999999999977480, 1999999999916612, 1999999999736334, 1999999999265284, 1999999998160003,
  1999999995803581, 1999999991203043, 1999999982936510, 1999999969228532, 1999999948241123,
  1999999918637799, 1999999880392247, 1999999835678723, 1999999789534577, 1999999749895687,
  1999999726649941, 1999999729584541, 1999999765497630, 1999999835195564, 1999999931418137,
  2000000038734585, 2000000136024416, 2000000201354053, 2000000218122075, 2000000180631806,
  2000000097102884, 1999999988720166, 1999999884526313, 1999999813405268, 1999999795543816,
  1999999836131466, 1999999923463031, 2000000032210715, 2000000130917824, 2000000191353581,
  2000000196767264, 2000000146494676, 2000000055625974, 1999999950069448, 1999999858764345,
  1999999805544802, 1999999803046570, 1999999850201717, 1999999933642000, 2000000032165570,
  2000000122670606, 2000000185789353, 2000000209821447, 2000000192260834, 2000000138969423,
  2000000061641232, 1999999974493811, 1999999891104877, 1999999822062762, 1999999773744069,
  1999999748192555, 1999999743833553, 1999999756649557, 1999999781454370, 1999999812995837,
  1999999846748757, 1999999879404729] (pCat [1999999909243272, 1999999936883109, 1999999967638526,
  2000000018462396, 2000000136513206, 2000000445145712, 2000001250788704, 2000003277338156,
  2000008152483289, 2000019363145705, 2000044032513616, 2000096045718997, 2000201238344184,
  2000405496359666, 2000786581962174, 2001470132775809, 2002649398905762, 2004606750342351,
  2007732830443380, 2012536753686798, 2019638617429370, 2029734830710460, 2043528513926844,
  2061622393121144, 2084380324306695, 2111774704951256, 2143248000752571, 2177623803206449,
  2213102498512551, 2247366320320147, 2277798477155499, 2301794763852286, 2317120113938374,
  2322244723691521, 2316591203837006, 2300638438529926, 2275856979287809, 2244487524897364,
  2209208290283838, 2172759382178916, 2137596938592386, 2105636539451490, 2078119355754070,
  2055604027338368, 2038060952170249, 2025029651389365, 2015796260988497, 2009555189929095,
  2005532222836654, 2003060844845776, 2001615365469103, 2000811474932503, 2000387075534027,
  2000174821219803, 2000074508442966, 2000029845180095, 2000011180537127, 2000003893287393,
  2000001250424162, 2000000366646740, 2000000096785201, 2000000022537869, 2000000004483099,
  2000000000718211] [2000000000080242])
private def wc_rkmTraj_m256_r128_s2_hb : List ℕ := pCat [135812532451390, 190942158832965,
  232475739670236, 266845659334327, 296558922508261, 322908830422325, 346668051643575,
  368342839898645, 388286774402472, 406758687470355, 423955017735622, 440029178868987,
  455103802225095, 469278821259285, 482637005929752, 495247867657352, 507170486375027,
  518455603088096, 529147198970434, 539283707386704, 548898958265854, 558022923870025,
  566682314863018, 574901061936689, 582700708824989, 590100735904107, 597118828837800,
  603771103289765, 610072294198263, 616035916227962, 621674400598610, 626999212413543,
  632020951783985, 636749441403960, 641193802729400, 645362522519985, 649263511188627,
  652904154152730, 656291357179493, 659431586554083, 662330904766278, 664995002302099,
  667429226037047, 669638604653189, 671627871440402, 673401484790403, 674963646648732,
  676318319153263, 677469239656799, 678419934304983, 679173730318218, 679733767107052,
  680103006333850, 680284241019279, 680280103779665, 680093074270464, 679725485901578,
  679179531881924, 678457270643268, 677560630686767, 676491414889784, 675251304305242,
  673841861480956, 672264533321945] [670520653514647, 668611444528101, 666538019203502,
  664301381940045, 661902429481532, 659341951304823, 656620629607818, 653739038891151,
  650697645124176, 647496804482043, 644136761636591, 640617647579447, 636939476950932,
  633102144843157, 629105423039798, 624948955648524, 620632254074603, 616154691275762,
  611515495228718, 606713741526619, 601748345013734, 596618050348681, 591321421369912,
  585856829116470, 580222438332661, 574416192256309, 568435795455778, 562278694439633,
  555942055713134, 549422740895649, 542717278440061, 535821831405986, 528732160628938,
  521443582491959, 513950920337535, 506248448346282, 498329826442416, 490188024447306,
  481815233268638, 473202760352294, 464340905893429, 455218815341406, 445824302453512,
  436143635430275, 426161276318935, 415859560631859, 405218299586998, 394214280913274,
  382820634794838, 371006017680114, 358733545761749, 345959377547370, 332630793399799,
  318683535278602, 304038025781400, 288593829622795, 272221243057902, 254747950995469,
  235936677898911, 215445062336470, 192746654047185, 166953845867821, 136333760619300,
  96408365500308]
private def wc_rkmTraj_m256_r128_s2_v0 : List ℕ := pCat [2000000000000745, 1999999999995100,
  1999999999977480, 1999999999916612, 1999999999736334, 1999999999265284, 1999999998160003,
  2000000004196419, 1999999991203043, 1999999982936510, 1999999969228532, 1999999948241123,
  1999999918637799, 2000000119607753, 2000000164321277, 2000000210465423, 1999999749895687,
  1999999726649941, 1999999729584541, 1999999765497630, 1999999835195564, 2000000068581863,
  2000000038734585, 2000000136024416, 2000000201354053, 2000000218122075, 2000000180631806,
  2000000097102884, 2000000011279834, 1999999884526313, 2000000186594732, 2000000204456184,
  2000000163868534, 2000000076536969, 1999999967789285, 1999999869082176, 1999999808646419,
  2000000196767264, 2000000146494676, 2000000055625974, 1999999950069448, 1999999858764345,
  1999999805544802, 1999999803046570, 2000000149798283, 2000000066358000, 2000000032165570,
  2000000122670606, 1999999814210647, 1999999790178553, 1999999807739166, 1999999861030577,
  2000000061641232, 2000000025506189, 2000000108895123, 1999999822062762, 1999999773744069,
  1999999748192555, 2000000256166447, 2000000243350443, 2000000218545630, 1999999812995837,
  1999999846748757, 1999999879404729] (pCat [1999999909243272, 1999999936883109, 1999999967638526,
  1999999981537604, 1999999863486794, 1999999554854288, 1999998749211296, 1999996722661844,
  1999991847516711, 2000019363145705, 2000044032513616, 2000096045718997, 2000201238344184,
  2000405496359666, 2000786581962174, 2001470132775809, 2002649398905762, 2004606750342351,
  2007732830443380, 2012536753686798, 2019638617429370, 2029734830710460, 2043528513926844,
  2061622393121144, 2084380324306695, 2111774704951256, 2143248000752571, 2177623803206449,
  2213102498512551, 2247366320320147, 2277798477155499, 2301794763852286, 2317120113938374,
  2322244723691521, 2316591203837006, 2300638438529926, 2275856979287809, 2244487524897364,
  2209208290283838, 2172759382178916, 2137596938592386, 2105636539451490, 2078119355754070,
  2055604027338368, 2038060952170249, 2025029651389365, 2015796260988497, 2009555189929095,
  2005532222836654, 2003060844845776, 2001615365469103, 2000811474932503, 2000387075534027,
  1999825178780197, 1999925491557034, 1999970154819905, 1999988819462873, 1999996106712607,
  1999998749575838, 1999999633353260, 1999999903214799, 1999999977462131, 1999999995516901,
  1999999999281789] [1999999999919758])
private def wc_rkmTraj_m256_r128_s2_v1 : List ℕ := pCat [1999999993462699, 2000000019598834,
  1999999957600701, 2000000072183595, 1999999910633353, 2000000068080807, 1999999980926429,
  1999999992513238, 1999999992337547, 2000000028566321, 1999999978539888, 1999999972259088,
  2000000091068757, 1999999931087558, 1999999973156044, 2000000008351442, 2000000074818504,
  2000000045746352, 1999999821702851, 2000000015312038, 2000000036007576, 2000000089347883,
  2000000069516122, 1999999958013918, 1999999967247104, 1999999771487749, 1999999890377272,
  2000000049478674, 2000000027980102, 2000000157388134, 2000000164473790, 2000000187509514,
  2000000050461785, 1999999698326072, 1999999994488296, 1999999794485441, 1999999782835332,
  1999999729496867, 1999999932681619, 1999999737423787, 1999999961361988, 2000000055617493,
  2000000236184469, 2000000249564262, 2000000117419179, 2000000152548477, 1999999799271539,
  2000000237885896, 1999999617166702, 2000001112759946, 1999998855756683, 2000002151123745,
  1999997407935849, 2000002889771062, 1999997193928862, 2000001654331481, 2000000182502461,
  1999998423885376, 2000002585530380, 1999998284840200, 1999999564485246, 2000002066653540,
  1999997658450691, 1999999751542320] (pCat [2000002517389622, 1999998480496306, 1999998969591225,
  2000002265775818, 1999999345161634, 1999997513994971, 2000001461641374, 2000002173652884,
  1999998058236237, 1999997813900198, 2000001765120704, 2000002107317611, 1999998322384497,
  1999997278544538, 2000000806797506, 2000003370014513, 2000001202700705, 1999997264227394,
  1999996453487864, 1999999575652583, 2000003290583059, 2000004215301586, 2000001811482277,
  1999997958074162, 1999994878977108, 1999993659105679, 1999994059691370, 1999995028254606,
  1999995288126644, 1999993998998111, 1999993552869111, 2000006941305484, 2000079253045451,
  2000324196543048, 2001002864365222, 2002602873489224, 2005998125380186, 2012446209871029,
  2023760928487465, 2041805142426694, 2068644645158432, 2105017965550641, 2150956084964696,
  2203428189520969, 2258277845041142, 2308639695436127, 2347582731427068, 2369176337836662,
  2369328759295232, 2348167210063456, 2309037050946288, 2257674075538545, 2201675270134055,
  2147960346928022, 2101274628992153, 2064407403690822, 2038046799054620, 2020816050202691,
  2010377987379567, 2004562243870986, 2001690564386611, 2000498611769969, 2000106999511041,
  2000013452595548] [2000000114156894])
private def wc_rkmTraj_m256_r128_s2_v2 : List ℕ := pCat [1999999878470532, 1999999942695816,
  2000000054337399, 1999999993798811, 2000000019472514, 2000000041382169, 1999999887668027,
  2000000028148867, 2000000064720664, 1999999952339033, 2000000042509266, 1999999964714024,
  1999999953350112, 2000000073723332, 2000000020951893, 1999999918632420, 2000000075272892,
  1999999849967784, 2000000178264701, 1999999984528152, 1999999978726138, 1999999911160817,
  1999999998092844, 2000000065252551, 1999999999107771, 2000000190772620, 1999999562496596,
  2000000565540729, 1999999184396471, 2000001116461698, 1999998375532114, 2000002224036070,
  1999997698392422, 2000002233961832, 1999997985404281, 2000001036262399, 2000000152591435,
  1999998686869874, 2000001974740699, 1999998370750816, 2000000848340091, 2000000663217688,
  1999998234900806, 2000001600704454, 1999999219124874, 1999998927384451, 2000001766112610,
  1999998802235923, 1999999833040597, 2000001772467424, 1999998622442896, 2000000048425960,
  2000001554352129, 1999998455092045, 1999999883465606, 2000001598899456, 1999998417532165,
  1999999090200980, 2000001538407580, 1999998983759995, 1999998619808950, 2000001820202239,
  2000000480831671, 1999998259822929] (pCat [2000000739982509, 2000001400033953, 1999998548222237,
  1999999351513482, 2000002021939800, 2000000289395129, 1999998305589931, 2000000613448972,
  2000001811885616, 1999998880204320, 1999998314020996, 2000001268374559, 2000002356995518,
  1999998301341242, 1999998941080752, 1999999363808717, 2000004571286372, 1999994874021513,
  2000004663005429, 1999990166050872, 2000017364255543, 1999978881921662, 2000026606964448,
  1999961083746289, 2000048047797008, 1999948808099822, 2000056896785139, 1999941182936039,
  2000045270746047, 1999971294270048, 2000010189581087, 2000019587317520, 1999957592627347,
  2000047966523670, 1999952186888327, 2000026173210009, 2000011347091050, 1999965118600153,
  2000053328164330, 1999956786110335, 2000004071451043, 2000023375653664, 1999931929938913,
  2000034911301712, 2000029904168873, 2000066610542760, 2000159740248225, 1999666685945442,
  1998575129816201, 1997472317308157, 1998983727867294, 2009958195074913, 2039954620702993,
  2097600029117426, 2184925844359138, 2290592195104214, 2389652274928742, 2452445978703937,
  2457278069106601, 2401414801042916, 2303833375717659, 2195525091668288, 2103988860931911,
  2043050701039007] [2011937818417533])
private def wc_rkmTraj_m256_r128_s2_ck3 : List ℕ := pCat [1999999987984549, 2000000009767439,
  2000000076499225, 1999999920905053, 1999999945200091, 1999999793632839, 2000000119773441,
  1999999978065288, 1999999743131579, 2000000273446170, 1999999456633085, 2000000862279131,
  1999998660676570, 2000001875076218, 1999997862537928, 2000002227777123, 1999998083345384,
  2000001125975014, 1999999955970132, 1999998815227371, 2000001867310717, 1999998421268661,
  2000000595602785, 2000000726019417, 1999998365541285, 2000001440073036, 1999999576699563,
  1999999142504484, 2000001713253726, 1999998849514055, 1999999573624731, 2000001438706415,
  1999998706408437, 2000000161306883, 2000001200814930, 1999998518765482, 2000000389626996,
  2000001143416135, 1999998418049440, 2000000269227356, 2000001201707989, 1999998645666145,
  2000000232461868, 2000001270343470, 1999998628586120, 1999999828798412, 2000001422859734,
  1999998892983539, 1999999441457179, 2000001602218550, 1999999462682149, 1999998830278408,
  2000001580185458, 1999999910066225, 1999998653941887, 2000000317478232, 2000001785738987,
  1999997185353607, 2000002012313878, 1999998669139727, 2000003804748937, 1999992412921065,
  2000010553909021, 1999987547429017] (pCat [2000015186003738, 1999978210260501, 2000029331683626,
  1999964854864978, 2000039273027659, 1999956139636648, 2000049291949085, 1999948751091541,
  2000047316414025, 1999962014894490, 2000027829896286, 1999984583914311, 1999997364870667,
  2000021458617137, 1999963934478292, 2000041204532683, 1999959332560962, 2000034541318058,
  1999981317307074, 1999994697047860, 2000026611358228, 1999961707663253, 2000041574781546,
  1999965144411344, 2000016383701078, 2000011292950274, 1999965572675818, 2000043182838603,
  1999962092465949, 2000021943398122, 2000006329088862, 1999964256227221, 2000047494327595,
  1999962769181543, 2000014730315293, 2000015201489020, 1999955574334936, 2000051005690992,
  1999971822201345, 1999994770877868, 2000035778717497, 1999944783887271, 2000041958528716,
  2000000143459654, 1999963664496274, 2000052787503400, 1999946571847585, 2000016520750045,
  2000064763212357, 1999896120587675, 1999958008527856, 2000124937118230, 2000371724462188,
  1999819993210224, 1998099706116858, 1999563092546666, 2006872468818231, 2008364963677986,
  1983377112989229, 1944768566957249, 1979190919592940, 2181625257114521, 2496148829789503,
  2676273875131952] [2509530308188675])
private def wc_rkmTraj_m128_r48_s0_hb : List ℕ := [211183094319292, 294373921109196,
  355269857060070, 404133455769000, 444995611961314, 479949953788161, 510254831949471,
  536738999748558, 559983742744238, 580415938284567, 598360188104537, 614070114112190,
  627748186340052, 639558839324094, 649637459345992, 658096723410558, 665031178456211,
  670520614506098, 674632588055701, 677424331208170, 678944205691920, 679232811105886,
  678323823302734, 676244615653998, 673016699296862, 668656005941008, 663173026798683,
  656572812516757, 648854830679544, 640012668609036, 630033558800234, 618897691081613,
  606577257603463, 593035151140242, 578223199285029, 562079759090183, 544526404940115,
  525463292259778, 504762524472646, 482258398062942, 457732556969545, 430890418507554,
  401321682300037, 368429459332602, 331290849931364, 288344807380356, 236539894342806,
  167995122823271]
private def wc_rkmTraj_m128_r48_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTraj_m128_r48_s0_v1 : List ℕ := [2000000000000003, 2000000000000003,
  2000000000000003, 2000000000000006, 2000000000000000, 2000000000000003, 2000000000000004,
  2000000000000002, 2000000000000005, 2000000000000007, 2000000000000007, 1999999999999999,
  2000000000000000, 1999999999999998, 2000000000000005, 2000000000000004, 1999999999999999,
  1999999999999987, 1999999999999981, 2000000000000129, 2000000000000219, 1999999999998326,
  1999999999998180, 2000000000020007, 2000000000013932, 1999999999784965, 1999999999894982,
  2000000002122602, 2000000000933100, 1999999980572162, 1999999989369757, 2000000165217278,
  2000000135663617, 1999998707091337, 1999998327925550, 2000009028714358, 2000018607036481,
  1999948238661867, 1999819249091920, 2000174701646867, 2001458318246219, 2000833853279416,
  1991583770753190, 1978986244206943, 2009907622960069, 2162867260108834, 2443265193421356,
  2669533199547128, 2572801936487250]
private def wc_rkmTrajPack_m64_r128_s1_hb : List ℕ := pCat [165972959179264, 232887450406491,
  282981823012586, 324165935897000, 359529106053143, 390668238390190, 418539275552160,
  443769787388747, 466798947691680, 487948883902737, 507464559775201, 525537671309089,
  542321763286828, 557942219551169, 572503107638390, 586092012101776, 598783536480879,
  610641897522533, 621722884425855, 632075363867623, 641742453636856, 650762450218497,
  659169570803417, 666994553349105, 674265146665760, 681006514305718, 687241570173424,
  692991259520789, 698274795865737, 703109862043619, 707512781848057, 711498667383612,
  715081546227435, 718274471701906, 721089618938407, 723538368922104, 725631382318184,
  727378664568559, 728789623497255, 729873120459556, 730637515904448, 731090710084196,
  731240179533185, 731093009845629, 730655925204775, 729935315051972, 728937258229989,
  727667544889508, 726131696409280, 724334983547749, 722282443016170, 719978892639410,
  717428945250253, 714637021445469, 711607361316715, 708344035256266, 704850953926159,
  701131877469407, 697190424033345, 693030077667525, 688654195652029, 684066015306155,
  679268660322358, 674265146665760] [669058388075530, 663651201200900, 658046310401401,
  652246352238100, 646253879680125, 640071366048504, 633701208717361, 627145732590709,
  620407193371466, 613487780637882, 606389620741257, 599114779537642, 591665264965177,
  584043029477739, 576249972344719, 568287941825936, 560158737230016, 551864110863874,
  543405769880381, 534785378030713, 526004557327453, 517064889623984, 507967918115382,
  498715148765577, 489308051665242, 479748062324539, 470036582904564, 460174983391064,
  450164602713758, 440006749814351, 429702704666159, 419253719248008, 408661018474970,
  397925801088257, 387049240506509, 376032485640520, 364876661673338, 353582870807575,
  342152192981589, 330585686556174, 318884388973226, 307049317387821, 295081469275011,
  282981823012586, 270751338441002, 258390957401540, 245901604253777, 233284186373335,
  220539594630829, 207668703852914, 194672373266237, 181551446925091, 168306754123498,
  154939109792438, 141449314882873, 127838156735203, 114106409435744, 100254834160788,
  86284179508801, 72195181821230, 57988565492442, 43665043269221, 29225316540275, 14670075616156]
private def wc_rkmTrajPack_m64_r128_s1_v0 : List ℕ := pCat [2000002632899645, 2000015759649500,
  2000065775840675, 2000221003778737, 2000633953078013, 2001603191139132, 2003647360614156,
  2007569762581112, 2014477669257658, 2025714038161755, 2042669215950982, 2066470866311522,
  2097597015282587, 2135504742735572, 2178394567357110, 2223219866130962, 2265996479834695,
  2302382896519715, 2328414207022676, 2341215916594005, 2339519665847578, 2323855135547538,
  2296382688699830, 2260427927600465, 2219850338807333, 2178403648107487, 2139223616232923,
  2104524121327652, 2075517044265476, 2052516898928026, 2035160204163184, 2022664564671843,
  2014067149446427, 2008406604402031, 2004836799909097, 2002678920544093, 2001428040345448,
  2000732466156658, 2000361376812054, 2000171430488918, 2000078157150294, 2000034226785130,
  2000014388227841, 2000005802017877, 2000002242453923, 2000000829913848, 2000000293794424,
  2000000099363520, 2000000032061294, 2000000009854104, 1999999997120320, 2000000000798452,
  2000000000209536, 2000000000051893, 2000000000012086, 2000000000002632, 2000000000000532,
  2000000000000097, 2000000000000014, 2000000000000001, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000] [2000000000000000]
private def wc_rkmTrajPack_m64_r128_s1_v1 : List ℕ := pCat [1999999999999998, 1999999999999999,
  2000000000000002, 2000000000000003, 2000000000000005, 2000000000000008, 2000000000000008,
  2000000000000016, 2000000000000046, 2000000000000298, 2000000000001351, 2000000000007347,
  2000000000031457, 2000000000140263, 2000000000545099, 2000000002087349, 2000000007305069,
  2000000024648147, 2000000077775982, 2000000234815600, 2000000670815417, 2000001830637215,
  2000004757370460, 2000011819921621, 2000028072271349, 2000063847291955, 2000139163262347,
  2000290993571950, 2000584230844939, 2001127131982273, 2002091118792712, 2003733280813663,
  2006417792762725, 2010629623369841, 2016971574891251, 2026134646514116, 2038833215283753,
  2055701829998549, 2077159333320280, 2103257351677483, 2133541298424168, 2166958928296598,
  2201850525264299, 2236044032688126, 2267058465009128, 2292393803504689, 2309861952390852,
  2317898341740253, 2315792697175819, 2303791880435353, 2283054326271114, 2255467348561724,
  2223366863251143, 2189216572717886, 2155306549075798, 2123520076353057, 2095197075826540,
  2071098958228881, 2051459556335983, 2036094081832658, 2024534182609917, 2016160911832280,
  2010315883855046, 2006380806427428] (pCat [2003824282938017, 2002220757477829, 2001249381224649,
  2000680914326716, 2000359459072984, 2000183787599227, 2000090998942926, 2000043625939514,
  2000020247201542, 2000009095066821, 2000003953292421, 2000001662249550, 2000000675880485,
  2000000265652241, 2000000100889227, 2000000037005864, 2000000013103635, 2000000004477230,
  2000000001475465, 2000000000468773, 2000000000143526, 2000000000042331, 2000000000012018,
  2000000000003281, 2000000000000859, 2000000000000212, 2000000000000048, 2000000000000009,
  2000000000000001, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTrajPack_m64_r128_s1_v2 : List ℕ := pCat [1999999999932131, 2000000000242850,
  1999999999431646, 2000000000982847, 1999999998719338, 2000000001190410, 1999999999411828,
  1999999999700167, 2000000000937917, 1999999999147582, 2000000000085574, 2000000000722984,
  1999999999160807, 2000000000144380, 2000000000673457, 1999999999233816, 2000000000031542,
  2000000000719976, 1999999999366020, 1999999999809416, 2000000000771122, 1999999999600119,
  1999999999537281, 2000000000724558, 1999999999952875, 1999999999317437, 2000000000492046,
  2000000000362721, 1999999999291219, 2000000000062380, 2000000000665680, 1999999999567676,
  1999999999572931, 2000000000650757, 2000000000097370, 1999999999306842, 2000000000225747,
  2000000000587955, 1999999999523536, 1999999999611858, 2000000000629523, 2000000000151687,
  1999999999289959, 1999999999964887, 2000000000492705, 2000000000096235, 2000000002438479,
  2000000010023242, 2000000015579950, 1999999983131489, 1999999800002728, 1999999238335487,
  1999998143783624, 1999997478245906, 2000002657498414, 2000031894862698, 2000133665804553,
  2000418080106904, 2001105459840280, 2002590149313593, 2005507732347437, 2010780881603744,
  2019607750588313, 2033354570672160] (pCat [2053328316238384, 2080438836976686, 2114806895599674,
  2155419468123661, 2199955316399335, 2244884680623792, 2285883156013828, 2318506907289345,
  2338985862416331, 2344938906478868, 2335824066473881, 2313007522670841, 2279443667429926,
  2239065591643408, 2196054677100585, 2154169673592980, 2116273096811131, 2084118123297577,
  2058381813150598, 2038874802072199, 2024835025066807, 2015221201913714, 2008949170279955,
  2005046697871519, 2002729251282245, 2001415115858905, 2000703286939401, 2000334906584004,
  2000152757236477, 2000066708345851, 2000027877114681, 2000011142125559, 2000004256737493,
  2000001553392565, 2000000541074373, 2000000179740784, 2000000056892746, 2000000017141769,
  2000000004910981, 2000000001336205, 2000000000344818, 2000000000084269, 2000000000019466,
  2000000000004239, 2000000000000865, 2000000000000163, 2000000000000027, 2000000000000003,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTrajPack_m64_r128_s2_hb : List ℕ := pCat [145723698973900, 204876510090560,
  249441079515733, 286319206566929, 318200849152752, 346473689512557, 371966783107134,
  395223328449408, 416622707840489, 436442642354558, 454893906091418, 472141108363379,
  488315829771190, 503525296595814, 517858319083658, 531389481377918, 544182174877077,
  556290843503584, 567762678037456, 578638916588029, 588955857884837, 598745661470352,
  608036987267637, 616855512354303, 625224352657463, 633164410169180, 640694661196687,
  647832397473542, 654593429246922, 660992257438725, 667042220459563, 672755620099539,
  678143830032268, 683217389780732, 687986086455699, 692459026153566, 696644696564014,
  700551022068711, 704185412395776, 707554805719294, 710665706950259, 713524221848256,
  716136087486751, 718506699525027, 720641136673398, 722544182682823, 724220346143462,
  725673878337400, 726908789357561, 727928862676477, 728737668324510, 729338574816403,
  729734759947215, 729929220563377, 729924781401180, 729724103073443, 729329689274900,
  728743893267877, 727968923701942, 727006849814130, 725859606050057, 724528996140543,
  723016696663169, 721324260113477] [719453117506102, 717404580521982, 715179843213921,
  712779983278975, 710205962902451, 707458629174723, 704538714078321, 701446834039106,
  698183489031396, 694749061222868, 691143813140735, 687367885335974, 683421293517313,
  679303925121017, 675015535276261, 670555742118824, 665924021397886, 661119700311622,
  656141950496948, 650989780086741, 645662024734055, 640157337486689, 634474177376595,
  628610796566428, 622565225869371, 616335258427291, 609918431295251, 603312004636138,
  596512938175779, 589517864504509, 582323058732746, 574924403912407, 567317351518266,
  559496876137903, 551457423337807, 543192849446513, 534696351709678, 525960386908601,
  516976576068256, 507735592279581, 498227027876834, 488439236178807, 478359141629567,
  467972010326602, 457261170406796, 446207668284410, 434789841864310, 422982784917730,
  410757666755144, 398080856472308, 384912778598952, 371206392230077, 356905130417114,
  341940045772278, 326225753587545, 309654489129930, 292087083287907, 273338645963093,
  253154586005152, 231167557534279, 206812691624402, 179137606365488, 146282964715185,
  103443941285471]
private def wc_rkmTrajPack_m64_r128_s2_v0 : List ℕ := pCat [1999999999932131, 2000000000242850,
  1999999999431646, 2000000000982847, 1999999998719338, 2000000001190410, 1999999999411828,
  1999999999700167, 2000000000937917, 1999999999147582, 2000000000085574, 2000000000722984,
  1999999999160807, 2000000000144380, 2000000000673457, 1999999999233816, 2000000000031542,
  2000000000719976, 1999999999366020, 1999999999809416, 2000000000771122, 1999999999600119,
  1999999999537281, 2000000000724558, 1999999999952875, 1999999999317437, 2000000000492046,
  2000000000362721, 1999999999291219, 2000000000062380, 2000000000665680, 1999999999567676,
  1999999999572931, 2000000000650757, 2000000000097370, 1999999999306842, 2000000000225747,
  2000000000587955, 1999999999523536, 1999999999611858, 2000000000629523, 2000000000151687,
  2000000000710041, 1999999999964887, 1999999999507295, 2000000000096235, 1999999997561521,
  2000000010023242, 2000000015579950, 1999999983131489, 1999999800002728, 1999999238335487,
  2000001856216376, 1999997478245906, 1999997342501586, 2000031894862698, 2000133665804553,
  2000418080106904, 2001105459840280, 2002590149313593, 2005507732347437, 2010780881603744,
  2019607750588313, 2033354570672160] (pCat [2053328316238384, 2080438836976686, 2114806895599674,
  2155419468123661, 2199955316399335, 2244884680623792, 2285883156013828, 2318506907289345,
  2338985862416331, 2344938906478868, 2335824066473881, 2313007522670841, 2279443667429926,
  2239065591643408, 2196054677100585, 2154169673592980, 2116273096811131, 2084118123297577,
  2058381813150598, 2038874802072199, 2024835025066807, 2015221201913714, 2008949170279955,
  2005046697871519, 2002729251282245, 2001415115858905, 2000703286939401, 2000334906584004,
  2000152757236477, 2000066708345851, 2000027877114681, 2000011142125559, 1999995743262507,
  2000001553392565, 2000000541074373, 2000000179740784, 2000000056892746, 2000000017141769,
  2000000004910981, 2000000001336205, 2000000000344818, 2000000000084269, 2000000000019466,
  2000000000004239, 2000000000000865, 2000000000000163, 2000000000000027, 2000000000000003,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000, 2000000000000000,
  2000000000000000] [2000000000000000])
private def wc_rkmTrajPack_m64_r128_s2_v1 : List ℕ := pCat [1999999998475076, 1999999998871426,
  2000000000557158, 2000000001101904, 1999999999782447, 1999999998976700, 2000000000065787,
  2000000000952729, 1999999999993745, 1999999999101937, 2000000000000453, 2000000000856154,
  1999999999970810, 1999999999178652, 2000000000081989, 2000000000786165, 1999999999853029,
  1999999999242363, 2000000000250493, 2000000000650292, 1999999999812721, 1999999999049779,
  2000000001153226, 1999999998692981, 2000000004119935, 1999999988732779, 2000000024285270,
  1999999952148509, 2000000088377042, 1999999853729641, 2000000206875530, 1999999766357586,
  2000000166739077, 2000000060187707, 1999999531357385, 2000000959490887, 1999998724505454,
  2000001094966582, 1999999711319911, 1999999195505402, 2000001407487089, 1999999126886156,
  1999999479585456, 2000001462407161, 1999999190570731, 1999999143953963, 2000001468318269,
  1999999943925509, 1999998523777141, 2000000729626017, 2000001234497108, 1999998921617200,
  1999998956604155, 2000001184803134, 2000001030853926, 1999998899725319, 1999998797877245,
  2000000785540433, 2000001445729234, 1999999841692511, 1999998511862844, 1999999270656831,
  2000000938266008, 2000001410791231] (pCat [2000000296319920, 1999998950275776, 1999998710749503,
  1999999668206567, 2000000788723002, 2000000847247153, 1999999241088901, 1999997385006785,
  1999999049303089, 2000010961954054, 2000033529373788, 2000052158110431, 2000010948807886,
  1999830848229224, 1999437356111824, 1998938862267372, 1998805939678944, 2000192946614538,
  2005037798837630, 2016010592022398, 2035994681449888, 2067224479988841, 2110294304674139,
  2163300824190724, 2221626395176090, 2278510297649686, 2326330347181965, 2358318957923699,
  2370121873804716, 2360709343205987, 2332438050200136, 2290277640363637, 2240496292969545,
  2189276895188072, 2141639922129644, 2100855941173419, 2068373361397644, 2044145816227178,
  2027151578726107, 2015910287805898, 2008883951373919, 2004726720702805, 2002394961085362,
  2001154137626115, 2000527906240483, 2000228627890675, 2000093524373133, 2000036067083127,
  2000013098209803, 2000004478754258, 2000001442890623, 2000000438469821, 2000000125822804,
  2000000034109453, 2000000008727273, 2000000002101565, 2000000000473904, 2000000000099342,
  2000000000019168, 2000000000003357, 2000000000000523, 2000000000000068, 2000000000000007,
  2000000000000000] [2000000000000000])
private def wc_rkmTrajPack_m64_r128_s2_v2 : List ℕ := pCat [1999999999997577, 1999999999984220,
  1999999999942874, 1999999999800657, 1999999999632478, 1999999998937945, 1999999999501653,
  1999999996441886, 2000000004401683, 1999999987084858, 2000000027286515, 1999999951903182,
  2000000080022219, 1999999890685394, 2000000112753678, 1999999940957095, 1999999909056081,
  2000000346363425, 1999999353944709, 2000000854184399, 1999999198897553, 2000000388421833,
  2000000275819490, 1999999155943593, 2000000907776080, 1999999674234298, 1999999453019054,
  2000001013504651, 1999999399803549, 1999999599450017, 2000001043059195, 1999999384366888,
  1999999498422713, 2000001078422366, 1999999613257612, 1999999199335073, 2000000989806634,
  2000000128814746, 1999998906850710, 2000000532215130, 2000000811234233, 1999999037837699,
  1999999637759374, 2000001132136599, 1999999917738447, 1999998888717743, 2000000427060105,
  2000001011335306, 1999999315744279, 1999999151963883, 2000000752386424, 2000000880873397,
  1999998976229919, 1999999496702912, 2000000473039656, 2000001371363047, 1999998382449589,
  2000000213775636, 1999999266044827, 2000002641553481, 1999997830064750, 2000000590987219,
  1999998647225665, 2000001952467926] (pCat [2000000322131459, 1999998381081761, 2000000416994464,
  1999999055721262, 2000002133935725, 1999999971672214, 1999998392220995, 2000000401174527,
  1999999083980352, 2000001513701817, 2000001154604367, 1999998319674132, 2000000054617763,
  1999999219743265, 1999999401408780, 2000002198790901, 2000000713345058, 2000000357287683,
  2000000124049473, 1999994442873268, 1999993153785933, 2000003270180151, 2000021782178767,
  2000034935905420, 2000002230992068, 1999897082973144, 1999792574362707, 1999878524080892,
  2000339769569263, 2001080926195734, 2001433489645721, 2000223538578553, 1996537325917000,
  1991067360316845, 1987358493268801, 1991963588613981, 2012781485098605, 2055789238024282,
  2121514666737442, 2203096073418255, 2287206172510270, 2357760997528474, 2400943663682115,
  2409421201621941, 2384079694898855, 2332849883792751, 2267489237879006, 2199855620168906,
  2139059536468864, 2090191027830162, 2054542088954391, 2030744700096258, 2016138720601664,
  2007876217986771, 2003565048309879, 2001491658545774, 2000574411610060, 2000202417400951,
  2000064790919963, 2000018652441848, 2000004764431053, 2000001058605692, 2000000198244960,
  2000000029526040] [2000000003031723])
private def wc_rkmTrajPack_m64_r128_s3_hb : List ℕ := pCat [146642478218638, 206168244287064,
  251013790668812, 288124432115114, 320207086559010, 348658185493743, 374312011525417,
  397715188001236, 419249489205126, 439194387226104, 457761985082123, 475117929937403,
  491394632000547, 506699993607835, 521123384948987, 534739860415784, 547613211085698,
  559798224146870, 571342387914374, 582287200501370, 592669189498719, 602520717212896,
  611870624266070, 620744749628297, 629166354971236, 637156474072765, 644734202884602,
  651916942163658, 658720601839775, 665159774262301, 671247881939734, 676997304224228,
  682419486499735, 687525034740303, 692323797763847, 696824939080163, 701036999893308,
  704967954547705, 708625259489369, 712015896637157, 715146411915140, 718022949579356,
  720651282875174, 723036841481191, 725184736128685, 727099780729881, 728786512301329,
  730249208929198, 731491905989807, 732518410810257, 733332315929740, 733937011101282,
  734335694155753, 734531380834521, 734526913683670, 734324970091026, 733928069536969,
  733338580121004, 732558724418103, 731590584711715, 730436107644024, 729097108318263,
  727575273882736, 725872166621377] [723989226571281, 721927773683459, 719689009539146,
  717274018630212, 714683769208487, 711919113705199, 708980788717984, 705869414559232,
  702585494355568, 699129412684214, 695501433727602, 691701698922874, 687730224077801,
  683586895918940, 679271468031570, 674783556143840, 670122632699557, 665288020654924,
  660278886424074, 655094231886222, 649732885353285, 644193491380608, 638474499284431,
  632574150207397, 626490462547087, 620221215531255, 613763930686245, 607115850900434,
  600273916730901, 593234739536663, 585994570942933, 578549268044513, 570894253637998,
  563024470626042, 554934329554760, 546617648017206, 538067580368074, 529276535829119,
  520236082596378, 510936834955181, 501368319620073, 491518816478216, 481375167533074,
  470922545985758, 460144174858047, 449020981062973, 437531165927183, 425649666189620,
  413347469384979, 400590732568165, 387339630747927, 373546826429159, 359155396012051,
  344095957399644, 328282587538411, 311606842245147, 293928674955362, 275062029849614,
  254750710595522, 232625055219384, 208116633330185, 180267058306660, 147205270097120,
  104096149175582]
private def wc_rkmTrajPack_m64_r128_s3_v0 : List ℕ := pCat [2000000000002423, 2000000000015780,
  1999999999942874, 1999999999800657, 1999999999632478, 2000000001062055, 1999999999501653,
  1999999996441886, 2000000004401683, 2000000012915142, 2000000027286515, 2000000048096818,
  2000000080022219, 2000000109314606, 1999999887246322, 2000000059042905, 2000000090943919,
  1999999653636575, 1999999353944709, 2000000854184399, 1999999198897553, 2000000388421833,
  1999999724180510, 2000000844056407, 2000000907776080, 2000000325765702, 1999999453019054,
  1999998986495349, 1999999399803549, 1999999599450017, 2000001043059195, 2000000615633112,
  1999999498422713, 1999998921577634, 2000000386742388, 2000000800664927, 2000000989806634,
  1999999871185254, 1999998906850710, 1999999467784870, 1999999188765767, 2000000962162301,
  2000000362240626, 1999998867863401, 1999999917738447, 2000001111282257, 1999999572939895,
  1999998988664694, 1999999315744279, 2000000848036117, 1999999247613576, 2000000880873397,
  2000001023770081, 2000000503297088, 1999999526960344, 2000001371363047, 2000001617550411,
  1999999786224364, 2000000733955173, 2000002641553481, 2000002169935250, 2000000590987219,
  2000001352774335, 2000001952467926] (pCat [1999999677868541, 2000001618918239, 2000000416994464,
  2000000944278738, 2000002133935725, 1999999971672214, 1999998392220995, 1999999598825473,
  1999999083980352, 1999998486298183, 2000001154604367, 1999998319674132, 1999999945382237,
  2000000780256735, 2000000598591220, 2000002198790901, 1999999286654942, 1999999642712317,
  2000000124049473, 1999994442873268, 2000006846214067, 2000003270180151, 2000021782178767,
  2000034935905420, 2000002230992068, 2000102917026856, 1999792574362707, 2000121475919108,
  1999660230430737, 1998919073804266, 1998566510354279, 2000223538578553, 2003462674083000,
  2008932639683155, 2012641506731199, 2008036411386019, 2012781485098605, 2055789238024282,
  2121514666737442, 2203096073418255, 2287206172510270, 2357760997528474, 2400943663682115,
  2409421201621941, 2384079694898855, 2332849883792751, 2267489237879006, 2199855620168906,
  2139059536468864, 2090191027830162, 2054542088954391, 2030744700096258, 2016138720601664,
  2007876217986771, 2003565048309879, 1998508341454226, 1999425588389940, 1999797582599049,
  2000064790919963, 2000018652441848, 2000004764431053, 2000001058605692, 1999999801755040,
  1999999970473960] [2000000003031723])
private def wc_rkmTrajPack_m64_r128_s3_v1 : List ℕ := pCat [1999999997501467, 2000000013569430,
  1999999953801130, 2000000111995674, 1999999780414088, 2000000381425526, 1999999411576881,
  2000000737690011, 1999999377533957, 2000000132230532, 2000000440795449, 1999999467824047,
  2000000102514975, 2000000098740220, 2000000268605916, 1999999551520163, 2000000046943611,
  2000000147834464, 2000000109591478, 1999999971243017, 1999999714587138, 2000000259172517,
  1999999589846139, 2000000571011063, 2000000067046118, 1999999475562683, 1999999897290762,
  2000000548375757, 1999999760660691, 2000000781194291, 1999999240515577, 2000000305458975,
  1999999945015427, 1999999934249547, 1999999801854929, 2000000486944384, 2000000317278331,
  1999998709441948, 1999998990832699, 2000000172841614, 2000000591001196, 2000000963366858,
  2000000988511210, 2000001174812671, 1999997987975556, 1999999062015930, 2000000544102319,
  2000001399751907, 1999999524826403, 1999998445923698, 2000000756166435, 1999999275320065,
  1999999399140155, 2000001245665688, 2000001091439783, 1999998248011306, 2000001365812213,
  2000000449385560, 1999999074594896, 2000000107262241, 1999998533831671, 2000000266191652,
  2000001555597443, 1999998452703761] (pCat [1999999676386901, 2000004022522618, 1999989381501065,
  2000020809199271, 1999961014783942, 2000060298718520, 1999915549472534, 2000106341047268,
  1999882022063559, 2000114551866627, 1999910139413633, 2000051704386973, 1999987898077349,
  1999993100841334, 1999996039721712, 2000050781922316, 1999902349522582, 2000147728915914,
  1999767528850828, 2000449096245932, 1999160050243788, 2001288418836907, 1998580477290096,
  2000857988186944, 2000384173276115, 1998391495997713, 2001792303241705, 1999507891746567,
  1998556416618759, 2002209800188669, 1999349672748633, 1997951784855985, 2002576472247327,
  2000738403702112, 1996236945162224, 2000655541675602, 2004735987535011, 1998549788121930,
  1993800832251706, 2000615812504892, 2008531944483741, 2003169172778889, 1991536372712396,
  1988275623839608, 2002247312440899, 2016008756237181, 2015836482355606, 1991477396162962,
  1963491309379425, 1963903113242995, 2018313240498786, 2133380363700584, 2278464382884811,
  2405141194881662, 2474650551318885, 2468137058948146, 2395893934386261, 2291770530706902,
  2189201566252400, 2106910535141306, 2051075786750523, 2019787118253261, 2005920410764542,
  2001280333089416] [2000174155128892])
private def wc_rkmTrajPack_m64_r128_s3_v2 : List ℕ := pCat [1999999222875977, 2000000520256172,
  2000000376217146, 1999999225982537, 2000000211072348, 2000000342421230, 1999999880663739,
  1999999935232171, 1999999572254304, 2000000614316104, 1999999911079979, 1999999980930108,
  1999999630244683, 2000000327490940, 1999999635190151, 2000000894408888, 1999999362316070,
  1999999644028044, 2000000494543213, 1999999957684673, 1999999958600042, 2000000091983279,
  1999999905609806, 2000000044814947, 1999999527209485, 2000000697427899, 1999999616596847,
  2000000380859129, 1999999820826524, 1999999639114840, 2000000156040598, 1999999715947676,
  2000001151289875, 1999999353956491, 1999999600629769, 1999999935781514, 2000000723937790,
  1999999580663420, 1999999869271014, 2000000156648526, 2000000253568317, 2000000767137141,
  1999996863851965, 2000003638215525, 1999996170308470, 2000007584074424, 1999984386289079,
  2000028452116650, 1999957389430137, 2000057403682387, 1999923861060828, 2000093719057723,
  1999897256239321, 2000106426320164, 1999900741943605, 2000078374754297, 1999944666818509,
  2000030343103638, 1999983479055708, 2000029113265457, 1999930207000042, 2000141793098891,
  1999757372904103, 2000366961608813] (pCat [1999497056475113, 2000640306541125, 1999240362458731,
  2000823628830976, 1999226435692042, 2000543615330714, 1999886402100022, 1999549970951195,
  2000958672225983, 1998848550813090, 2000835897515129, 1999955115073411, 1999125620548869,
  2001387724511749, 1998906158107300, 2000053872056038, 2001115072956372, 1998424433024513,
  2000883762335206, 2000554118788363, 1998366685837028, 2001366364639606, 2000185458663147,
  1998246028006037, 2001826723742215, 1999853248006345, 1998305006410374, 2001578009265879,
  2000775031457807, 1997060595822168, 2002165901658670, 2001003929977023, 1997459943155488,
  1999929227381856, 2003494525930727, 1997838088812225, 1997007621311679, 2004188325995998,
  2001315107974269, 1995358300674253, 1999114318444545, 2005736758795686, 2000799245440105,
  1992353341901293, 1999499453647198, 2009047574505442, 2002016470406338, 1989662440385418,
  1992968859290175, 2011756792347818, 2015947877735077, 1989962004347023, 1970777514487350,
  1997050209836519, 2045042409900080, 2043008759536747, 1957456467657161, 1870644740271849,
  1924816039436164, 2158937659487584, 2443045058066333, 2592761013590834, 2527702365793268,
  2322501760348444] [2121336451792200])
private def wc_rkmTrajPack_m64_r128_s0_hb : List ℕ := [209248404204101, 292451811514640,
  353923114819222, 403754245936863, 445901211928105, 482415629181632, 514529304866070,
  543053090107543, 568555773536356, 591455409493502, 612070444542785, 630650394138620,
  647395274980406, 662468463714856, 676005516760879, 688120404366025, 698910030742531,
  708457583916481, 716835065638019, 724105233681975, 730323114501735, 735537196022452,
  739790378371767, 743120738633212, 745562150671024, 747144790469280, 747895549818261,
  747838375630438, 746994548054314, 745382907453944, 743020037943186, 739920413300857,
  736096509597616, 731558887627772, 726316247174828, 720375454180158, 713741540970717,
  706417678778446, 698405120793323, 689703112868662, 680308767661076, 670216896334619,
  659419789847864, 647906939076093, 635664679313634, 622675739634609, 608918670534418,
  594367113263543, 578988859785449, 562744630911127, 545586467880958, 527455582695698,
  508279432969759, 487967656447709, 466406277839967, 443449205437436, 418905297337475,
  392517816189395, 363929980193744, 332623060723733, 297794417618854, 258083985201812,
  210826123376491, 149112430134204]
private def wc_rkmTrajPack_m64_r128_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTrajPack_m64_r128_s0_v1 : List ℕ := pCat [2000002632899645, 2000015759649500,
  2000065775840675, 2000221003778737, 2000633953078013, 2001603191139132, 2003647360614156,
  2007569762581112, 2014477669257658, 2025714038161755, 2042669215950982, 2066470866311522,
  2097597015282587, 2135504742735572, 2178394567357110, 2223219866130962, 2265996479834695,
  2302382896519715, 2328414207022676, 2341215916594005, 2339519665847578, 2323855135547538,
  2296382688699830, 2260427927600465, 2219850338807333, 2178403648107487, 2139223616232923,
  2104524121327652, 2075517044265476, 2052516898928026, 2035160204163184, 2022664564671843,
  2014067149446427, 2008406604402031, 2004836799909097, 2002678920544093, 2001428040345448,
  2000732466156658, 2000361376812054, 2000171430488918, 2000078157150294, 2000034226785130,
  2000014388227841, 2000005802017877, 2000002242453923, 2000000829913848, 2000000293794424,
  2000000099363520, 2000000032061294, 2000000009854104, 2000000002879680, 2000000000798452,
  2000000000209536, 2000000000051893, 2000000000012086, 2000000000002632, 2000000000000532,
  2000000000000097, 2000000000000014, 2000000000000001, 2000000000000000, 2000000000000000,
  2000000000000000, 2000000000000000] [2000000000000000]
private def wc_rkmTrajPack_m8_r80_s4_hb : List ℕ := pCat [189224093779366, 264815158736522,
  320914802538964, 366614051614342, 405472691993646, 439335193697974, 469308178968586,
  496119689013286, 520280239832021, 542165004260168, 562059797601172, 580188658337384,
  596731313066911, 611834730030659, 625621042239842, 638193147454459, 649638769135527,
  660033467189419, 669442913469746, 677924640883330, 685529408103269, 692302278608327,
  698283484045645, 703509122433311, 708011728245171, 711820741933629, 714962899658519,
  717462559061293, 719341973296061, 720621522825077, 721319912447387, 721454339474879,
  721040637772488, 720093401447560, 718626091241165, 716651126093174, 714179961887083,
  711223159003108, 707790439998401, 703890738475715, 699532239984100, 694722415607506,
  689468048731408, 683775255327082, 677649497951878, 671095593526350, 664117714809894,
  656719385349988, 648903467520000, 640672143079356, 632026885478977, 622968422882816,
  613496690568889, 603610770991062, 593308819300692, 582587971510047, 571444231679344,
  559872333458921, 547865569922181, 535415583746304, 522512107235799, 509142638141316,
  495292032253141, 480941986653672] [466070377208037, 450650398607805, 434649432173236,
  418027530766589, 400735352988479, 382711284723912, 363877325534349, 344133031664142,
  323346273191044, 301338502931709, 277859973671370, 252545057056500, 224823919040468,
  193723797594225, 157323647259567, 110605758753463]
private def wc_rkmTrajPack_m8_r80_s4_v0 : List ℕ := pCat [1999997147891002, 1999992000489504,
  2000015561680760, 1999975068625398, 1999965733296670, 2000041642942600, 1999960173269802,
  2000032584741435, 2000013342240527, 1999990410112440, 1999993915967659, 2000029685136224,
  2000044355736995, 1999952881913560, 1999966778897592, 1999998877755836, 1999985447578785,
  1999996786523337, 1999985188824358, 1999948557247482, 1999886039335804, 1999839034169474,
  1999951532497169, 1999638978358520, 1999223095941256, 1999703147090554, 1998249040283792,
  1995798869331827, 1996589819469699, 1995518534155499, 1981399875905692, 2029270108100379,
  2019514330487097, 2026569114067887, 2112970703205546, 2225896277107320, 2337564478724146,
  2417920129618401, 2447376083539366, 2423587358805713, 2359654024629114, 2276334870815465,
  2193336167068722, 2123719022995676, 2072637492472514, 2039211735465426, 2019489189746859,
  2008924901303668, 2003766242894923, 2001464022487230, 2000523778194039, 2000172234300312,
  1999948041962149, 1999985655409998, 1999996386880302, 2000000827081800, 2000000171225422,
  2000000031860972, 2000000005286479, 1999999999226027, 1999999999901447, 2000000000010685,
  2000000000000951, 2000000000000064] [2000000000000002]
private def wc_rkmTrajPack_m8_r80_s4_v1 : List ℕ := pCat [1999057056377236, 2002855024459515,
  1994722959502427, 2006413727930115, 1995785483342667, 1998697241294255, 2006251667415758,
  1994026486720334, 1999502997274833, 2006914974452410, 1994290089445774, 1997417555092140,
  2008068560207223, 1997019602415519, 1993626047411791, 2007041207548196, 2002541025264432,
  1991419135455162, 2001529114922386, 2007996956741187, 1995108143205538, 1993892438980660,
  2007038216081489, 2003837195564285, 1991818732804574, 1998310987038390, 2008625738170466,
  1999939456555369, 1991375622336803, 2001294655078831, 2008508768709969, 1997979788716960,
  1991422596135544, 2002176976733166, 2008834736044910, 1998229736128993, 1990733446941208,
  2000663170464909, 2009704553914261, 2001242788854443, 1990106010370800, 1995945865102932,
  2009324207301629, 2007747222879917, 1992917798669330, 1988328436757740, 2002289417381544,
  2014434120636478, 2005560238741028, 1986445555578088, 1984424452780036, 2005704268749257,
  2023884785492143, 2011730645209281, 1978208312381629, 1963683720027284, 1994430457450249,
  2046689893953897, 2063161022562166, 2009207113090656, 1913618977586381, 1853357457035329,
  1895249136085146, 2045309713025867] [2245255289567301, 2412898017736590, 2490824611263385,
  2470006463048675, 2380899678004687, 2267572885659586, 2165020596137110, 2089941742545335,
  2043431010372538, 2018567033132619, 2007001004535613, 2002311806272238, 2000660809373003,
  2000160520754858, 2000032136858136, 2000005006096309, 2000000526068631]
private abbrev dP_0 : Prop := atF [ bSlideChk 20 129 wc_rkmTrajPack_m64_r128_s1_hb
  wc_rkmTrajPack_m64_r128_s1_v0 wc_rkmTrajPack_m64_r128_s1_v1, bNatListEq (bEvalLo12W 2 4096 16
  [1,2,4,8,12,12,12,12] [43040543,46429612,49517930,57791243,26499879,23008787,7500710,4091764]
  [1,2,3,5,3,3,1,1] rkmMasks_m2_r16 []) rkmRow_m2_r16, bNatListEq (bEvalLo12W 256 32 5 [1,1]
  [37012278,9744785] [6,3] rkmMasks_m256_r5 []) rkmRow_m256_r5] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bSlideChk 52 49 wc_rkmTraj_m128_r48_s0_hb
  wc_rkmTraj_m128_r48_s0_v0 wc_rkmTraj_m128_r48_s0_v1, bNatListEq (bEvalLo12W 32 256 14 [1,1,1]
  [130424992,17403742,7735480] [15,3,2] rkmMasks_m32_r14 []) rkmRow_m32_r14] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bSlideChk 19 129 wc_rkmTrajPack_m64_r128_s1_hb
  wc_rkmTrajPack_m64_r128_s1_v1 wc_rkmTrajPack_m64_r128_s1_v2, bNatListEq (bEvalLo12W 64 128 15
  [1,1,1,1,1,1,1,1] [31867570,15599023,25713745,9324196,6491012,6407991,4540094,2768165]
  [6,3,5,2,2,2,1,1] rkmMasksPack_m64_r15 []) rkmRowPack_m64_r15, bNatListEq (bEvalLo12W 64 128 9
  [1,1,1] [9002258,87657309,1935260] [1,10,1] rkmMasksPack_m64_r9 []) rkmRowPack_m64_r9] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bNatListEq (bEvalLo12W 64 128 128 [1,2,4,4,4,4,4,4]
  [26586736,25284943,11672751,11746347,3628988,1692955,550153,674371] [23,39,29,29,9,5,2,2]
  rkmMasksPack_m64_r128 [some (23, 65, wc_rkmTrajPack_m64_r128_s0_hb,
  wc_rkmTrajPack_m64_r128_s0_v0, wc_rkmTrajPack_m64_r128_s0_v1), some (39, 129,
  wc_rkmTrajPack_m64_r128_s1_hb, wc_rkmTrajPack_m64_r128_s1_v0, wc_rkmTrajPack_m64_r128_s1_v2),
  some (29, 129, wc_rkmTrajPack_m64_r128_s2_hb, wc_rkmTrajPack_m64_r128_s2_v0,
  wc_rkmTrajPack_m64_r128_s2_v2), some (29, 129, wc_rkmTrajPack_m64_r128_s3_hb,
  wc_rkmTrajPack_m64_r128_s3_v0, wc_rkmTrajPack_m64_r128_s3_v2)]) rkmRowPack_m64_r128, bNatListEq
  (bEvalLo12W 16 512 15 [1,2,2,2] [102936110,60234633,19880397,7859335] [9,8,4,2] rkmMasks_m16_r15
  []) rkmRow_m16_r15, bNatListEq (bEvalLo12W 4 2048 10 [1,2,4,4,4,4,4,4]
  [87754070,100899568,48070000,45695000,15507881,6513309,2735589,1148945] [2,4,3,3,1,1,1,1]
  rkmMasks_m4_r10 []) rkmRow_m4_r10, bNatListEq (bEvalLo12W 64 128 9 [1,1,1]
  [5812409,90844833,1937585] [2,11,2] rkmMasks_m64_r9 []) rkmRow_m64_r9] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bNatListEq (bEvalLo12W 8 1024 48 [1,2,3,6,10,10,10,10]
  [36757877,19352683,22859783,32496292,20203184,27379063,7127025,1796185] [3,3,5,12,11,14,4,1]
  rkmMasksPack_m8_r48 []) rkmRowPack_m8_r48, bNatListEq (bEvalLo12W 8 1024 16 [1,2,3,3,3]
  [78641893,47202104,88950569,23971254,7153857] [5,5,10,4,2] rkmMasks_m8_r16 []) rkmRow_m8_r16,
  bNatListEq (bEvalLo12W 4 2048 11 [1,3,4,4,4] [92789315,49243729,62782381,50353145,33691222]
  [3,4,5,4,3] rkmMasks_m4_r11 []) rkmRow_m4_r11] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m256_r128_s0_hb
  wc_rkmTraj_m256_r128_s0_v0 wc_rkmTraj_m256_r128_s0_v1, bNatListEq (bEvalLo12W 32 256 24
  [1,1,2,2,2,2,2,2] [13310609,110046776,2785014,16073109,7535617,3189203,1000,1573490]
  [3,18,1,4,2,1,1,1] rkmMasksPack_m32_r24 []) rkmRowPack_m32_r24, bNatListEq (bEvalLo12W 128 64 6
  [1,1,1] [65625042,670128,818504] [8,2,2] rkmMasks_m128_r6 []) rkmRow_m128_r6] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m256_r128_s0_hb
  wc_rkmTraj_m256_r128_s0_v1 wc_rkmTraj_m256_r128_s0_v2, bNatListEq (bEvalLo12W 512 16 24 [1,1,1]
  [33587572,893925,260729] [26,1,1] rkmMasks_m512_r24 []) rkmRow_m512_r24, bNatListEq (bEvalLo12W
  2 4096 19 [1] [126704623] [3] rkmMasksPack_m2_r19 []) rkmRowPack_m2_r19] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m256_r128_s0_hb
  wc_rkmTraj_m256_r128_s0_v2 wc_rkmTraj_m256_r128_s0_ck3, bNatListEq (bEvalLo12W 64 128 21
  [1,1,1,1,1,1,1,1] [19698368,24059238,19461534,19613230,8666141,6824334,5012135,3320588]
  [5,6,5,5,2,2,2,1] rkmMasksPack_m64_r21 []) rkmRowPack_m64_r21, bNatListEq (bEvalLo12W 2 4096 14
  [1,3,6,12] [46875806,58441172,64082137,64830665] [2,3,5,7] rkmMasks_m2_r14 []) rkmRow_m2_r14] =
  true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m256_r128_s1_hb
  wc_rkmTraj_m256_r128_s1_v0 wc_rkmTraj_m256_r128_s1_v1, bNatListEq (bEvalLo12W 64 128 21 [1,1]
  [102840962,3833634] [26,2] rkmMasks_m64_r21 []) rkmRow_m64_r21, bNatListEq (bEvalLo12W 32 256 11
  [1,1,1,1,1,1,1,1] [40833490,28743336,18490634,27549596,10720099,7689423,9142455,5878335]
  [4,3,2,3,1,1,1,1] rkmMasksPack_m32_r11 []) rkmRowPack_m32_r11] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m256_r128_s1_hb
  wc_rkmTraj_m256_r128_s1_v1 wc_rkmTraj_m256_r128_s1_v2, bNatListEq (bEvalLo12W 4 2048 24
  [1,2,4,8,11,11,11] [42628593,38374600,25372593,24395184,63769649,8824319,3257225]
  [2,3,3,4,13,2,1] rkmMasks_m4_r24 []) rkmRow_m4_r24, bNatListEq (bEvalLo12W 8 1024 12
  [1,2,3,3,3,3,3,3] [112063555,67475138,30512618,29481799,6606949,3900635,636480,749748]
  [5,4,3,3,1,1,1,1] rkmMasksPack_m8_r12 []) rkmRowPack_m8_r12] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m256_r128_s1_hb
  wc_rkmTraj_m256_r128_s1_v2 wc_rkmTraj_m256_r128_s1_ck3, bNatListEq (bEvalLo12W 8 1024 22
  [1,4,4,4] [81251148,105407412,26506096,7064682] [5,16,4,2] rkmMasksPack_m8_r22 [])
  rkmRowPack_m8_r22, bNatListEq (bEvalLo12W 16 512 30 [1,1,1,1,1,1,1,1]
  [9245186,22740712,33936063,59832,7194974,13922649,7179134,3342192] [2,3,4,1,1,2,1,1]
  rkmMasksPack_m16_r30 []) rkmRowPack_m16_r30] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m256_r128_s2_hb
  wc_rkmTraj_m256_r128_s2_v0 wc_rkmTraj_m256_r128_s2_v1, bNatListEq (bEvalLo12W 128 64 18
  [1,1,1,1] [66788945,2829854,1300136,20791] [20,2,2,2] rkmMasks_m128_r18 []) rkmRow_m128_r18,
  bNatListEq (bEvalLo12W 1024 8 15 [1] [24216172] [18] rkmMasks_m1024_r15 []) rkmRow_m1024_r15] =
  true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m256_r128_s2_hb
  wc_rkmTraj_m256_r128_s2_v1 wc_rkmTraj_m256_r128_s2_v2, bNatListEq (bEvalLo12W 512 16 18 [1,1,1]
  [33393723,1026616,93470] [20,2,2] rkmMasks_m512_r18 []) rkmRow_m512_r18, bNatListEq (bEvalLo12W
  8 1024 17 [1,2,3,3,3,3] [81252162,44619830,68455947,28903593,19863207,9988781] [4,4,7,3,2,1]
  rkmMasksPack_m8_r17 []) rkmRowPack_m8_r17] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m256_r128_s2_hb
  wc_rkmTraj_m256_r128_s2_v2 wc_rkmTraj_m256_r128_s2_ck3, bNatListEq (bEvalLo12W 8 1024 34
  [1,2,3,6] [62633444,28760653,31518066,18199467] [5,4,6,5] rkmMasksPack_m8_r34 [])
  rkmRowPack_m8_r34, bNatListEq (bEvalLo12W 128 64 48 [1,1,1,1] [70049799,5320190,1627992,476305]
  [52,4,2,1] rkmMasks_m128_r48 [some (52, 49, wc_rkmTraj_m128_r48_s0_hb,
  wc_rkmTraj_m128_r48_s0_v0, wc_rkmTraj_m128_r48_s0_v1)]) rkmRow_m128_r48, bNatListEq (bEvalLo12W
  32 256 6 [1,1,1,1,1] [74922567,36562354,15878177,7813809,3315633] [5,3,2,2,2] rkmMasks_m32_r6
  []) rkmRow_m32_r6] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := atF [ bSlideChk 25 81 wc_rkmTrajPack_m8_r80_s4_hb
  wc_rkmTrajPack_m8_r80_s4_v0 wc_rkmTrajPack_m8_r80_s4_v1, bNatListEq (bEvalLo12W 8 1024 28
  [1,2,4,6,6,6] [55979797,36116074,29810915,61054791,5570035,3555154] [4,4,6,15,2,1]
  rkmMasks_m8_r28 []) rkmRow_m8_r28, bNatListEq (bEvalLo12W 1024 8 4 [1,1] [16092275,6893241]
  [5,3] rkmMasks_m1024_r4 []) rkmRow_m1024_r4] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := atF [ bSlideChk 15 129 wc_rkmTrajPack_m64_r128_s2_hb
  wc_rkmTrajPack_m64_r128_s2_v0 wc_rkmTrajPack_m64_r128_s2_v1, bNatListEq (bEvalLo12W 32 256 27
  [1,2,2] [99242066,30789680,15288325] [18,9,5] rkmMasksPack_m32_r27 []) rkmRowPack_m32_r27,
  bNatListEq (bEvalLo12W 1024 8 7 [1,1,1,1] [7109689,7106689,5685352,3788339] [4,4,3,3]
  rkmMasks_m1024_r7 []) rkmRow_m1024_r7] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := atF [ bSlideChk 15 129 wc_rkmTrajPack_m64_r128_s3_hb
  wc_rkmTrajPack_m64_r128_s3_v0 wc_rkmTrajPack_m64_r128_s3_v1, bNatListEq (bEvalLo12W 128 64 25
  [1,1,1] [66753945,4102851,1562041] [27,3,2] rkmMasks_m128_r25 []) rkmRow_m128_r25, bNatListEq
  (bEvalLo12W 4 2048 6 [1,2,2,2] [142339940,153251738,56136001,21746804] [3,4,2,1]
  rkmMasksPack_m4_r6 []) rkmRowPack_m4_r6] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := atF [ bNatListEq (bEvalLo12W 32 256 40 [1,2,3,3,3]
  [38937231,21864375,48266584,2608602,733754] [10,9,25,2,1] rkmMasks_m32_r40 []) rkmRow_m32_r40,
  bNatListEq (bEvalLo12W 1024 8 28 [1] [24486601] [33] rkmMasks_m1024_r28 []) rkmRow_m1024_r28,
  bNatListEq (bEvalLo12W 8 1024 10 [1,2,2,2,2] [130996812,46099904,56994141,30603334,13318644]
  [5,3,3,2,1] rkmMasksPack_m8_r10 []) rkmRowPack_m8_r10] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := atF [ bSlideChk 14 129 wc_rkmTrajPack_m64_r128_s2_hb
  wc_rkmTrajPack_m64_r128_s2_v1 wc_rkmTrajPack_m64_r128_s2_v2, bNatListEq (bEvalLo12W 32 256 56
  [1,1,1,1,2,2,2,2] [28961350,26556803,19335872,38153,556066,1000,3025806,1046003]
  [9,8,6,1,1,1,2,1] rkmMasksPack_m32_r56 []) rkmRowPack_m32_r56] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := atF [ bSlideChk 14 129 wc_rkmTrajPack_m64_r128_s3_hb
  wc_rkmTrajPack_m64_r128_s3_v1 wc_rkmTrajPack_m64_r128_s3_v2, bNatListEq (bEvalLo12W 128 64 28
  [1,1,1,1] [66753945,4618759,1080763,583981] [30,3,2,2] rkmMasks_m128_r28 []) rkmRow_m128_r28] =
  true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := atF [ bNatListEq (bEvalLo12W 32 256 40 [1,2,3,3,3]
  [58811128,18733865,40815195,2872173,1346433] [14,7,20,2,1] rkmMasksPack_m32_r40 [])
  rkmRowPack_m32_r40, bNatListEq (bEvalLo12W 64 128 28 [1,1,1] [102020592,5929658,3811516]
  [33,3,3] rkmMasks_m64_r28 []) rkmRow_m64_r28, bNatListEq (bEvalLo12W 8 1024 31 [1,1,1,1,1,1,1,1]
  [23153048,4693343,34892076,10899506,14664175,5195019,10725,10957636] [2,1,3,1,1,1,1,1]
  rkmMasksPack_m8_r31 []) rkmRowPack_m8_r31] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := atF [ bNatListEq (bEvalLo12W 256 32 128 [1,1,1,1,1,1,1,1]
  [18006368,18006368,18006368,1335375,1452126,559149,499241,195260] [48,48,48,4,4,2,2,1]
  rkmMasks_m256_r128 [some (48, 129, wc_rkmTraj_m256_r128_s0_hb, wc_rkmTraj_m256_r128_s0_v0,
  wc_rkmTraj_m256_r128_s0_ck3), some (48, 129, wc_rkmTraj_m256_r128_s1_hb,
  wc_rkmTraj_m256_r128_s1_v0, wc_rkmTraj_m256_r128_s1_ck3), some (48, 129,
  wc_rkmTraj_m256_r128_s2_hb, wc_rkmTraj_m256_r128_s2_v0, wc_rkmTraj_m256_r128_s2_ck3)])
  rkmRow_m256_r128, bNatListEq (bEvalLo12W 512 16 31 [1,1,1] [33394723,1257830,302329] [34,3,2]
  rkmMasks_m512_r31 []) rkmRow_m512_r31] = true
private theorem bk_21 : dP_21 := by decide +kernel
private abbrev dP_22 : Prop := atF [ bNatListEq (bEvalLo12W 8 1024 80 [1,2,4,8,15,15,15]
  [28402233,18628893,20908754,24575958,24140754,1825910,79943] [3,4,8,16,25,2,1]
  rkmMasksPack_m8_r80 [none, none, none, none, some (25, 81, wc_rkmTrajPack_m8_r80_s4_hb,
  wc_rkmTrajPack_m8_r80_s4_v0, wc_rkmTrajPack_m8_r80_s4_v1)]) rkmRowPack_m8_r80, bNatListEq
  (bEvalLo12W 64 128 32 [1,1,1,1,1,1,1,1]
  [46242028,40764053,2631067,4653370,6381930,4399655,5706687,4353434] [15,13,1,2,2,2,2,2]
  rkmMasksPack_m64_r32 []) rkmRowPack_m64_r32] = true
private theorem bk_22 : dP_22 := by decide +kernel
private abbrev dP_23 : Prop := atF [ bSlideChk 23 65 wc_rkmTrajPack_m64_r128_s0_hb
  wc_rkmTrajPack_m64_r128_s0_v0 wc_rkmTrajPack_m64_r128_s0_v1, bNatListEq (bEvalLo12W 128 64 32
  [1,1,1,1,1,1,1,1] [31681777,31660798,2853885,2512953,1150655,1171128,1198045,1651189]
  [17,17,2,2,1,1,1,1] rkmMasks_m128_r32 []) rkmRow_m128_r32] = true
private theorem bk_23 : dP_23 := by decide +kernel
private theorem ws_rkmTraj_m256_r128_s0_m1 : WalkOk (some (32, 129, wc_rkmTraj_m256_r128_s0_hb,
    wc_rkmTraj_m256_r128_s0_v0, wc_rkmTraj_m256_r128_s0_v2)) := mIter_split rfl
    (bSlideChk_sound bk_5) (bSlideChk_sound bk_6)
private theorem ws_rkmTraj_m256_r128_s0 : WalkOk (some (48, 129, wc_rkmTraj_m256_r128_s0_hb,
    wc_rkmTraj_m256_r128_s0_v0, wc_rkmTraj_m256_r128_s0_ck3)) := mIter_split rfl
    ws_rkmTraj_m256_r128_s0_m1 (bSlideChk_sound bk_7)
private theorem ws_rkmTraj_m256_r128_s1_m1 : WalkOk (some (32, 129, wc_rkmTraj_m256_r128_s1_hb,
    wc_rkmTraj_m256_r128_s1_v0, wc_rkmTraj_m256_r128_s1_v2)) := mIter_split rfl
    (bSlideChk_sound bk_8) (bSlideChk_sound bk_9)
private theorem ws_rkmTraj_m256_r128_s1 : WalkOk (some (48, 129, wc_rkmTraj_m256_r128_s1_hb,
    wc_rkmTraj_m256_r128_s1_v0, wc_rkmTraj_m256_r128_s1_ck3)) := mIter_split rfl
    ws_rkmTraj_m256_r128_s1_m1 (bSlideChk_sound bk_10)
private theorem ws_rkmTraj_m256_r128_s2_m1 : WalkOk (some (32, 129, wc_rkmTraj_m256_r128_s2_hb,
    wc_rkmTraj_m256_r128_s2_v0, wc_rkmTraj_m256_r128_s2_v2)) := mIter_split rfl
    (bSlideChk_sound bk_11) (bSlideChk_sound bk_12)
private theorem ws_rkmTraj_m256_r128_s2 : WalkOk (some (48, 129, wc_rkmTraj_m256_r128_s2_hb,
    wc_rkmTraj_m256_r128_s2_v0, wc_rkmTraj_m256_r128_s2_ck3)) := mIter_split rfl
    ws_rkmTraj_m256_r128_s2_m1 (bSlideChk_sound bk_13)
private theorem ws_rkmTrajPack_m64_r128_s1 : WalkOk (some (39, 129, wc_rkmTrajPack_m64_r128_s1_hb,
    wc_rkmTrajPack_m64_r128_s1_v0, wc_rkmTrajPack_m64_r128_s1_v2)) := mIter_split rfl
    (bSlideChk_sound bk_0) (bSlideChk_sound bk_2)
private theorem ws_rkmTrajPack_m64_r128_s2 : WalkOk (some (29, 129, wc_rkmTrajPack_m64_r128_s2_hb,
    wc_rkmTrajPack_m64_r128_s2_v0, wc_rkmTrajPack_m64_r128_s2_v2)) := mIter_split rfl
    (bSlideChk_sound bk_15) (bSlideChk_sound bk_18)
private theorem ws_rkmTrajPack_m64_r128_s3 : WalkOk (some (29, 129, wc_rkmTrajPack_m64_r128_s3_hb,
    wc_rkmTrajPack_m64_r128_s3_v0, wc_rkmTrajPack_m64_r128_s3_v2)) := mIter_split rfl
    (bSlideChk_sound bk_16) (bSlideChk_sound bk_19)
/-- Kernel trajectory certificate `(m = 256, r = 128)`. -/
theorem rkmTraj_m256_r128 : rkmEvalT16Lo12 256 32 128 [1, 1, 1, 1, 1, 1, 1, 1] [18006368, 18006368,
  18006368, 1335375, 1452126, 559149, 499241, 195260] [48, 48, 48, 4, 4, 2, 2, 1] rkmMasks_m256_r128
  = rkmRow_m256_r128 :=
    bhW_eq bk_21 (wCons ws_rkmTraj_m256_r128_s0 (wCons ws_rkmTraj_m256_r128_s1 (wCons
      ws_rkmTraj_m256_r128_s2 wNil)))
/-- Kernel trajectory certificate `(m = 1024, r = 4)`. -/
theorem rkmTraj_m1024_r4 : rkmEvalT16Lo12 1024 8 4 [1, 1] [16092275, 6893241] [5, 3]
  rkmMasks_m1024_r4 = rkmRow_m1024_r4 := bh0_eq (tl2 bk_14)
/-- Kernel trajectory certificate `(m = 128, r = 48)`. -/
theorem rkmTraj_m128_r48 : rkmEvalT16Lo12 128 64 48 [1, 1, 1, 1] [70049799, 5320190, 1627992,
  476305] [52, 4, 2, 1] rkmMasks_m128_r48 = rkmRow_m128_r48 :=
    bhW_eq (tl2 bk_13) (wCons (bSlideChk_sound bk_1) wNil)
/-- Kernel trajectory certificate `(m = 256, r = 5)`. -/
theorem rkmTraj_m256_r5 : rkmEvalT16Lo12 256 32 5 [1, 1] [37012278, 9744785] [6, 3] rkmMasks_m256_r5
  = rkmRow_m256_r5 := bh0_eq (tl2 bk_0)
/-- Kernel trajectory certificate `(m = 32, r = 40)`. -/
theorem rkmTraj_m32_r40 : rkmEvalT16Lo12 32 256 40 [1, 2, 3, 3, 3] [38937231, 21864375, 48266584,
  2608602, 733754] [10, 9, 25, 2, 1] rkmMasks_m32_r40 = rkmRow_m32_r40 := bh0_eq bk_17
/-- Kernel trajectory certificate `(m = 128, r = 6)`. -/
theorem rkmTraj_m128_r6 : rkmEvalT16Lo12 128 64 6 [1, 1, 1] [65625042, 670128, 818504] [8, 2, 2]
  rkmMasks_m128_r6 = rkmRow_m128_r6 := bh0_eq (tl2 bk_5)
/-- Kernel trajectory certificate `(m = 128, r = 32)`. -/
theorem rkmTraj_m128_r32 : rkmEvalT16Lo12 128 64 32 [1, 1, 1, 1, 1, 1, 1, 1] [31681777, 31660798,
  2853885, 2512953, 1150655, 1171128, 1198045, 1651189] [17, 17, 2, 2, 1, 1, 1, 1] rkmMasks_m128_r32
  = rkmRow_m128_r32 := bh0_eq (tl1 bk_23)
/-- Kernel trajectory certificate `(m = 32, r = 6)`. -/
theorem rkmTraj_m32_r6 : rkmEvalT16Lo12 32 256 6 [1, 1, 1, 1, 1] [74922567, 36562354, 15878177,
  7813809, 3315633] [5, 3, 2, 2, 2] rkmMasks_m32_r6 = rkmRow_m32_r6 := bh0_eq (tl1 (tl2 bk_13))
/-- Kernel trajectory certificate `(m = 512, r = 31)`. -/
theorem rkmTraj_m512_r31 : rkmEvalT16Lo12 512 16 31 [1, 1, 1] [33394723, 1257830, 302329] [34, 3, 2]
  rkmMasks_m512_r31 = rkmRow_m512_r31 := bh0_eq (tl1 bk_21)
/-- Kernel trajectory certificate `(m = 1024, r = 7)`. -/
theorem rkmTraj_m1024_r7 : rkmEvalT16Lo12 1024 8 7 [1, 1, 1, 1] [7109689, 7106689, 5685352, 3788339]
  [4, 4, 3, 3] rkmMasks_m1024_r7 = rkmRow_m1024_r7 := bh0_eq (tl2 bk_15)
/-- Kernel trajectory certificate `(m = 64, r = 28)`. -/
theorem rkmTraj_m64_r28 : rkmEvalT16Lo12 64 128 28 [1, 1, 1] [102020592, 5929658, 3811516] [33, 3,
  3] rkmMasks_m64_r28 = rkmRow_m64_r28 := bh0_eq (tl1 bk_20)
/-- Kernel trajectory certificate `(m = 64, r = 9)`. -/
theorem rkmTraj_m64_r9 : rkmEvalT16Lo12 64 128 9 [1, 1, 1] [5812409, 90844833, 1937585] [2, 11, 2]
  rkmMasks_m64_r9 = rkmRow_m64_r9 := bh0_eq (tl1 (tl2 bk_3))
/-- Kernel trajectory certificate `(m = 128, r = 28)`. -/
theorem rkmTraj_m128_r28 : rkmEvalT16Lo12 128 64 28 [1, 1, 1, 1] [66753945, 4618759, 1080763,
  583981] [30, 3, 2, 2] rkmMasks_m128_r28 = rkmRow_m128_r28 := bh0_eq (tl1 bk_19)
/-- Kernel trajectory certificate `(m = 4, r = 10)`. -/
theorem rkmTraj_m4_r10 : rkmEvalT16Lo12 4 2048 10 [1, 2, 4, 4, 4, 4, 4, 4] [87754070, 100899568,
  48070000, 45695000, 15507881, 6513309, 2735589, 1148945] [2, 4, 3, 3, 1, 1, 1, 1] rkmMasks_m4_r10
  = rkmRow_m4_r10 := bh0_eq (tl2 bk_3)
/-- Kernel trajectory certificate `(m = 1024, r = 28)`. -/
theorem rkmTraj_m1024_r28 : rkmEvalT16Lo12 1024 8 28 [1] [24486601] [33] rkmMasks_m1024_r28 =
  rkmRow_m1024_r28 := bh0_eq (tl1 bk_17)
/-- Kernel trajectory certificate `(m = 2, r = 14)`. -/
theorem rkmTraj_m2_r14 : rkmEvalT16Lo12 2 4096 14 [1, 3, 6, 12] [46875806, 58441172, 64082137,
  64830665] [2, 3, 5, 7] rkmMasks_m2_r14 = rkmRow_m2_r14 := bh0_eq (tl2 bk_7)
/-- Kernel trajectory certificate `(m = 128, r = 25)`. -/
theorem rkmTraj_m128_r25 : rkmEvalT16Lo12 128 64 25 [1, 1, 1] [66753945, 4102851, 1562041] [27, 3,
  2] rkmMasks_m128_r25 = rkmRow_m128_r25 := bh0_eq (tl1 bk_16)
/-- Kernel trajectory certificate `(m = 4, r = 11)`. -/
theorem rkmTraj_m4_r11 : rkmEvalT16Lo12 4 2048 11 [1, 3, 4, 4, 4] [92789315, 49243729, 62782381,
  50353145, 33691222] [3, 4, 5, 4, 3] rkmMasks_m4_r11 = rkmRow_m4_r11 := bh0_eq (tl2 bk_4)
/-- Kernel trajectory certificate `(m = 8, r = 28)`. -/
theorem rkmTraj_m8_r28 : rkmEvalT16Lo12 8 1024 28 [1, 2, 4, 6, 6, 6] [55979797, 36116074, 29810915,
  61054791, 5570035, 3555154] [4, 4, 6, 15, 2, 1] rkmMasks_m8_r28 = rkmRow_m8_r28 :=
    bh0_eq (tl1 bk_14)
/-- Kernel trajectory certificate `(m = 2, r = 16)`. -/
theorem rkmTraj_m2_r16 : rkmEvalT16Lo12 2 4096 16 [1, 2, 4, 8, 12, 12, 12, 12] [43040543, 46429612,
  49517930, 57791243, 26499879, 23008787, 7500710, 4091764] [1, 2, 3, 5, 3, 3, 1, 1] rkmMasks_m2_r16
  = rkmRow_m2_r16 := bh0_eq (tl1 bk_0)
/-- Kernel trajectory certificate `(m = 512, r = 24)`. -/
theorem rkmTraj_m512_r24 : rkmEvalT16Lo12 512 16 24 [1, 1, 1] [33587572, 893925, 260729] [26, 1, 1]
  rkmMasks_m512_r24 = rkmRow_m512_r24 := bh0_eq (tl1 bk_6)
/-- Kernel trajectory certificate `(m = 1024, r = 15)`. -/
theorem rkmTraj_m1024_r15 : rkmEvalT16Lo12 1024 8 15 [1] [24216172] [18] rkmMasks_m1024_r15 =
  rkmRow_m1024_r15 := bh0_eq (tl2 bk_11)
/-- Kernel trajectory certificate `(m = 64, r = 21)`. -/
theorem rkmTraj_m64_r21 : rkmEvalT16Lo12 64 128 21 [1, 1] [102840962, 3833634] [26, 2]
  rkmMasks_m64_r21 = rkmRow_m64_r21 := bh0_eq (tl1 bk_8)
/-- Kernel trajectory certificate `(m = 32, r = 14)`. -/
theorem rkmTraj_m32_r14 : rkmEvalT16Lo12 32 256 14 [1, 1, 1] [130424992, 17403742, 7735480] [15, 3,
  2] rkmMasks_m32_r14 = rkmRow_m32_r14 := bh0_eq (tl1 bk_1)
/-- Kernel trajectory certificate `(m = 4, r = 24)`. -/
theorem rkmTraj_m4_r24 : rkmEvalT16Lo12 4 2048 24 [1, 2, 4, 8, 11, 11, 11] [42628593, 38374600,
  25372593, 24395184, 63769649, 8824319, 3257225] [2, 3, 3, 4, 13, 2, 1] rkmMasks_m4_r24 =
  rkmRow_m4_r24 := bh0_eq (tl1 bk_9)
/-- Kernel trajectory certificate `(m = 16, r = 15)`. -/
theorem rkmTraj_m16_r15 : rkmEvalT16Lo12 16 512 15 [1, 2, 2, 2] [102936110, 60234633, 19880397,
  7859335] [9, 8, 4, 2] rkmMasks_m16_r15 = rkmRow_m16_r15 := bh0_eq (tl1 bk_3)
/-- Kernel trajectory certificate `(m = 128, r = 18)`. -/
theorem rkmTraj_m128_r18 : rkmEvalT16Lo12 128 64 18 [1, 1, 1, 1] [66788945, 2829854, 1300136, 20791]
  [20, 2, 2, 2] rkmMasks_m128_r18 = rkmRow_m128_r18 := bh0_eq (tl1 bk_11)
/-- Kernel trajectory certificate `(m = 8, r = 16)`. -/
theorem rkmTraj_m8_r16 : rkmEvalT16Lo12 8 1024 16 [1, 2, 3, 3, 3] [78641893, 47202104, 88950569,
  23971254, 7153857] [5, 5, 10, 4, 2] rkmMasks_m8_r16 = rkmRow_m8_r16 := bh0_eq (tl1 bk_4)
/-- Kernel trajectory certificate `(m = 512, r = 18)`. -/
theorem rkmTraj_m512_r18 : rkmEvalT16Lo12 512 16 18 [1, 1, 1] [33393723, 1026616, 93470] [20, 2, 2]
  rkmMasks_m512_r18 = rkmRow_m512_r18 := bh0_eq (tl1 bk_12)
/-- Krotov trajectory `(m = 64, r = 128)`. -/
theorem rkmTrajPack_m64_r128 : rkmEvalT16Lo12 64 128 128 [1,2,4,4,4,4,4,4]
  [26586736,25284943,11672751,11746347,3628988,1692955,550153,674371] [23,39,29,29,9,5,2,2]
  rkmMasksPack_m64_r128 = rkmRowPack_m64_r128 :=
    bhW_eq bk_3 (wCons (bSlideChk_sound bk_23) (wCons ws_rkmTrajPack_m64_r128_s1 (wCons
      ws_rkmTrajPack_m64_r128_s2 (wCons ws_rkmTrajPack_m64_r128_s3 wNil))))
/-- Krotov trajectory `(m = 2, r = 19)`. -/
theorem rkmTrajPack_m2_r19 : rkmEvalT16Lo12 2 4096 19 [1] [126704623] [3] rkmMasksPack_m2_r19 =
  rkmRowPack_m2_r19 := bh0_eq (tl2 bk_6)
/-- Krotov trajectory `(m = 8, r = 80)`. -/
theorem rkmTrajPack_m8_r80 : rkmEvalT16Lo12 8 1024 80 [1,2,4,8,15,15,15]
  [28402233,18628893,20908754,24575958,24140754,1825910,79943] [3,4,8,16,25,2,1] rkmMasksPack_m8_r80
  = rkmRowPack_m8_r80 :=
    bhW_eq bk_22 (wSkip (wSkip (wSkip (wSkip (wCons (bSlideChk_sound bk_14) wNil)))))
/-- Krotov trajectory `(m = 4, r = 6)`. -/
theorem rkmTrajPack_m4_r6 : rkmEvalT16Lo12 4 2048 6 [1,2,2,2]
  [142339940,153251738,56136001,21746804] [3,4,2,1] rkmMasksPack_m4_r6 = rkmRowPack_m4_r6 :=
    bh0_eq (tl2 bk_16)
/-- Krotov trajectory `(m = 8, r = 48)`. -/
theorem rkmTrajPack_m8_r48 : rkmEvalT16Lo12 8 1024 48 [1,2,3,6,10,10,10,10]
  [36757877,19352683,22859783,32496292,20203184,27379063,7127025,1796185] [3,3,5,12,11,14,4,1]
  rkmMasksPack_m8_r48 = rkmRowPack_m8_r48 := bh0_eq bk_4
/-- Krotov trajectory `(m = 8, r = 31)`. -/
theorem rkmTrajPack_m8_r31 : rkmEvalT16Lo12 8 1024 31 [1,1,1,1,1,1,1,1]
  [23153048,4693343,34892076,10899506,14664175,5195019,10725,10957636] [2,1,3,1,1,1,1,1]
  rkmMasksPack_m8_r31 = rkmRowPack_m8_r31 := bh0_eq (tl2 bk_20)
/-- Krotov trajectory `(m = 32, r = 40)`. -/
theorem rkmTrajPack_m32_r40 : rkmEvalT16Lo12 32 256 40 [1,2,3,3,3]
  [58811128,18733865,40815195,2872173,1346433] [14,7,20,2,1] rkmMasksPack_m32_r40 =
  rkmRowPack_m32_r40 := bh0_eq bk_20
/-- Krotov trajectory `(m = 64, r = 9)`. -/
theorem rkmTrajPack_m64_r9 : rkmEvalT16Lo12 64 128 9 [1,1,1] [9002258,87657309,1935260] [1,10,1]
  rkmMasksPack_m64_r9 = rkmRowPack_m64_r9 := bh0_eq (tl2 bk_2)
/-- Krotov trajectory `(m = 64, r = 32)`. -/
theorem rkmTrajPack_m64_r32 : rkmEvalT16Lo12 64 128 32 [1,1,1,1,1,1,1,1]
  [46242028,40764053,2631067,4653370,6381930,4399655,5706687,4353434] [15,13,1,2,2,2,2,2]
  rkmMasksPack_m64_r32 = rkmRowPack_m64_r32 := bh0_eq (tl1 bk_22)
/-- Krotov trajectory `(m = 8, r = 10)`. -/
theorem rkmTrajPack_m8_r10 : rkmEvalT16Lo12 8 1024 10 [1,2,2,2,2]
  [130996812,46099904,56994141,30603334,13318644] [5,3,3,2,1] rkmMasksPack_m8_r10 =
  rkmRowPack_m8_r10 := bh0_eq (tl2 bk_17)
/-- Krotov trajectory `(m = 32, r = 56)`. -/
theorem rkmTrajPack_m32_r56 : rkmEvalT16Lo12 32 256 56 [1,1,1,1,2,2,2,2]
  [28961350,26556803,19335872,38153,556066,1000,3025806,1046003] [9,8,6,1,1,1,2,1]
  rkmMasksPack_m32_r56 = rkmRowPack_m32_r56 := bh0_eq (tl1 bk_18)
/-- Krotov trajectory `(m = 32, r = 11)`. -/
theorem rkmTrajPack_m32_r11 : rkmEvalT16Lo12 32 256 11 [1,1,1,1,1,1,1,1]
  [40833490,28743336,18490634,27549596,10720099,7689423,9142455,5878335] [4,3,2,3,1,1,1,1]
  rkmMasksPack_m32_r11 = rkmRowPack_m32_r11 := bh0_eq (tl2 bk_8)
/-- Krotov trajectory `(m = 32, r = 27)`. -/
theorem rkmTrajPack_m32_r27 : rkmEvalT16Lo12 32 256 27 [1,2,2] [99242066,30789680,15288325] [18,9,5]
  rkmMasksPack_m32_r27 = rkmRowPack_m32_r27 := bh0_eq (tl1 bk_15)
/-- Krotov trajectory `(m = 8, r = 12)`. -/
theorem rkmTrajPack_m8_r12 : rkmEvalT16Lo12 8 1024 12 [1,2,3,3,3,3,3,3]
  [112063555,67475138,30512618,29481799,6606949,3900635,636480,749748] [5,4,3,3,1,1,1,1]
  rkmMasksPack_m8_r12 = rkmRowPack_m8_r12 := bh0_eq (tl2 bk_9)
/-- Krotov trajectory `(m = 32, r = 24)`. -/
theorem rkmTrajPack_m32_r24 : rkmEvalT16Lo12 32 256 24 [1,1,2,2,2,2,2,2]
  [13310609,110046776,2785014,16073109,7535617,3189203,1000,1573490] [3,18,1,4,2,1,1,1]
  rkmMasksPack_m32_r24 = rkmRowPack_m32_r24 := bh0_eq (tl1 bk_5)
/-- Krotov trajectory `(m = 16, r = 30)`. -/
theorem rkmTrajPack_m16_r30 : rkmEvalT16Lo12 16 512 30 [1,1,1,1,1,1,1,1]
  [9245186,22740712,33936063,59832,7194974,13922649,7179134,3342192] [2,3,4,1,1,2,1,1]
  rkmMasksPack_m16_r30 = rkmRowPack_m16_r30 := bh0_eq (tl2 bk_10)
/-- Krotov trajectory `(m = 64, r = 21)`. -/
theorem rkmTrajPack_m64_r21 : rkmEvalT16Lo12 64 128 21 [1,1,1,1,1,1,1,1]
  [19698368,24059238,19461534,19613230,8666141,6824334,5012135,3320588] [5,6,5,5,2,2,2,1]
  rkmMasksPack_m64_r21 = rkmRowPack_m64_r21 := bh0_eq (tl1 bk_7)
/-- Krotov trajectory `(m = 8, r = 17)`. -/
theorem rkmTrajPack_m8_r17 : rkmEvalT16Lo12 8 1024 17 [1,2,3,3,3,3]
  [81252162,44619830,68455947,28903593,19863207,9988781] [4,4,7,3,2,1] rkmMasksPack_m8_r17 =
  rkmRowPack_m8_r17 := bh0_eq (tl2 bk_12)
/-- Krotov trajectory `(m = 8, r = 22)`. -/
theorem rkmTrajPack_m8_r22 : rkmEvalT16Lo12 8 1024 22 [1,4,4,4]
  [81251148,105407412,26506096,7064682] [5,16,4,2] rkmMasksPack_m8_r22 = rkmRowPack_m8_r22 :=
    bh0_eq (tl1 bk_10)
/-- Krotov trajectory `(m = 64, r = 15)`. -/
theorem rkmTrajPack_m64_r15 : rkmEvalT16Lo12 64 128 15 [1,1,1,1,1,1,1,1]
  [31867570,15599023,25713745,9324196,6491012,6407991,4540094,2768165] [6,3,5,2,2,2,1,1]
  rkmMasksPack_m64_r15 = rkmRowPack_m64_r15 := bh0_eq (tl1 bk_2)
/-- Krotov trajectory `(m = 8, r = 34)`. -/
theorem rkmTrajPack_m8_r34 : rkmEvalT16Lo12 8 1024 34 [1,2,3,6]
  [62633444,28760653,31518066,18199467] [5,4,6,5] rkmMasksPack_m8_r34 = rkmRowPack_m8_r34 :=
    bh0_eq (tl1 bk_13)
end
end QuantumComputation.Specs.DickeSol
