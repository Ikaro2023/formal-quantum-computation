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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxTraj02
/-
# Multi-Segment `T_16` Trajectory Part `04` (`FindAllJohnsonRampKickMuxTraj04`)

Certified kernel trajectory evaluations (`30` rows, `38001` substep-coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Prefix-kick masks for `(m = 2, r = 10)`. -/
def rkmMasks_m2_r10 : List (List Bool) := [[], [], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 10)`. -/
def rkmRow_m2_r10 : List ℕ := [
  14830867, 22092322, 1806079602, 29290388, 21373272421, 11438900272, 95159088241, 463094758489,
  348018226629, 59041604864]
/-- Prefix-kick masks for `(m = 2, r = 12)`. -/
def rkmMasks_m2_r12 : List (List Bool) := [
  [], [], [], [], [false, false, false, true, true, true],
  [false, true, true, false, false, true, false, false, true, true], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 12)`. -/
def rkmRow_m2_r12 : List ℕ := [
  34665587, 247468, 1973563920, 50444011, 879681182, 805320734, 1586487952, 10766758354,
  1729411448, 10850419693, 430427917822, 540679221874]
/-- Prefix-kick masks for `(m = 2, r = 15)`. -/
def rkmMasks_m2_r15 : List (List Bool) := [[], [], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 15)`. -/
def rkmRow_m2_r15 : List ℕ := [
  162767, 54361, 3018129, 3570150, 110188525, 219589536, 1106514182, 4724008885, 2149383689,
  39014383040, 2450810239, 153427147458, 455599093958, 292141018760, 49050999561]
/-- Prefix-kick masks for `(m = 2, r = 18)`. -/
def rkmMasks_m2_r18 : List (List Bool) := [[], [], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 18)`. -/
def rkmRow_m2_r18 : List ℕ := [
  1961, 177635, 59765, 543170, 2639554, 37012325, 36769271, 655707994, 101080847, 6193578716,
  323556708, 28326598732, 25537212035, 42828058649, 355642668607, 393812356552, 133538648366,
  12963328826]
/-- Mask chunk for `(m = 2, r = 44)`. -/
def rkmMkP_m2_r44_s5_p0 : List Bool := [
  false, false, false, false, false, true, true, true, true, true, false, true, true, true, false,
  false, false, true, true, false, false, true, true, false, true, true, false, false, true, true,
  true, false, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 2, r = 44)`. -/
def rkmMkP_m2_r44_s6_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, false, true,
  false, false, true, false, true, false, true, true, false, false, true, false, true, false,
  false, true, false, false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 2, r = 44)`. -/
def rkmMasks_m2_r44 : List (List Bool) := [
  [], [], [], [], [], rkmMkP_m2_r44_s5_p0, rkmMkP_m2_r44_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 44)`. -/
def rkmRow_m2_r44 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 25, 214, 67, 12, 1035, 8082, 60862, 153425, 241055, 82845,
  452144, 952935, 3715010, 18400614, 24295782, 102894812, 66500245, 19238760, 159975652,
  180486186, 247186397, 2130519801, 2512422222, 7181674254, 1825539794, 624059131, 39526732875,
  8842498962, 6006814798, 137284533917, 399967299714, 318441265134, 74831991804]
/-- Prefix-kick masks for `(m = 4, r = 5)`. -/
def rkmMasks_m4_r5 : List (List Bool) := [[], [false, true, true], [true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 5)`. -/
def rkmRow_m4_r5 : List ℕ := [112905779, 1556279023, 514968349, 150081139105, 847664594469]
/-- Mask chunk for `(m = 8, r = 14)`. -/
def rkmMkP_m8_r14_s3_p0 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 8, r = 14)`. -/
def rkmMasks_m8_r14 : List (List Bool) := [
  [], [true, true], [false, true, true, true, false, false, true, true, false, false, true, true],
  rkmMkP_m8_r14_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 14)`. -/
def rkmRow_m8_r14 : List ℕ := [
  23424, 57878, 307806, 14660150, 44079766, 252049459, 391559066, 1735130893, 1277025950, 89098,
  12867719773, 114236993, 81278895464, 902024158685]
/-- Mask chunk for `(m = 8, r = 15)`. -/
def rkmMkP_m8_r15_s2_p0 : List Bool := [
  false, true, true, true, true, false, false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 8, r = 15)`. -/
def rkmMkP_m8_r15_s3_p0 : List Bool := [
  false, true, false, true, false, true, false, true, false, true, false, false, false, true]
/-- Prefix-kick masks for `(m = 8, r = 15)`. -/
def rkmMasks_m8_r15 : List (List Bool) := [[], [], rkmMkP_m8_r15_s2_p0, rkmMkP_m8_r15_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 15)`. -/
def rkmRow_m8_r15 : List ℕ := [
  2426, 2585, 13594, 101034, 2794208, 9688631, 106290501, 136162642, 928345157, 1043801587,
  589795632, 11926764191, 667636853, 86989816508, 897598784093]
/-- Mask chunk for `(m = 16, r = 16)`. -/
def rkmMkP_m16_r16_s0_p0 : List Bool := [
  false, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true]
/-- Mask chunk for `(m = 16, r = 16)`. -/
def rkmMkP_m16_r16_s1_p0 : List Bool := [
  false, false, true, true, true, false, true, true, true, true, false, true, true]
/-- Mask chunk for `(m = 16, r = 16)`. -/
def rkmMkP_m16_r16_s2_p0 : List Bool := [
  true, false, true, false, true, true, false, false, true, false, false, true, false, true, true]
/-- Prefix-kick masks for `(m = 16, r = 16)`. -/
def rkmMasks_m16_r16 : List (List Bool) := [
  rkmMkP_m16_r16_s0_p0, rkmMkP_m16_r16_s1_p0, rkmMkP_m16_r16_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 16)`. -/
def rkmRow_m16_r16 : List ℕ := [
  2220, 17462, 624698, 135624, 192, 6553309, 3694940, 6419835, 1300719658, 4760360, 775161260,
  6919879349, 2935859843, 573077462, 37622637547, 949850456077]
/-- Mask chunk for `(m = 16, r = 24)`. -/
def rkmMkP_m16_r24_s1_p0 : List Bool := [
  true, true, true, false, false, true, true, false, false, true, true, false, false, true, true,
  true, true, true]
/-- Mask chunk for `(m = 16, r = 24)`. -/
def rkmMkP_m16_r24_s2_p0 : List Bool := [
  true, false, false, true, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, true, false, true, true]
/-- Mask chunk for `(m = 16, r = 24)`. -/
def rkmMkP_m16_r24_s3_p0 : List Bool := [
  false, true, true, true, true, true, true, false, false, false, false, false, true, false,
  false, false, true, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 24)`. -/
def rkmMasks_m16_r24 : List (List Bool) := [
  [], rkmMkP_m16_r24_s1_p0, rkmMkP_m16_r24_s2_p0, rkmMkP_m16_r24_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 24)`. -/
def rkmRow_m16_r24 : List ℕ := [
  0, 7, 16, 19, 154, 844, 0, 880, 27739, 196628, 205906, 12825156, 49066114, 354767616, 402339110,
  1053617104, 1891898732, 3240155794, 277833244, 16271257, 9274438000, 99504136, 48141304805,
  935185546415]
/-- Mask chunk for `(m = 16, r = 31)`. -/
def rkmMkP_m16_r31_s1_p0 : List Bool := [
  false, false, false, false, false, true, false, false, true, false, true, false, true, true,
  false, true, true, false, false, true, true, false, false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 16, r = 31)`. -/
def rkmMkP_m16_r31_s2_p0 : List Bool := [
  false, false, false, true, true, false, false, true, false, true, false, true, false, true,
  true, false, true, false, true, false, true, false, true, false, true, false, true, false,
  false, true]
/-- Prefix-kick masks for `(m = 16, r = 31)`. -/
def rkmMasks_m16_r31 : List (List Bool) := [[], rkmMkP_m16_r31_s1_p0, rkmMkP_m16_r31_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 31)`. -/
def rkmRow_m16_r31 : List ℕ := [
  1, 0, 2, 9, 0, 41, 3, 3, 464, 6479, 12259, 69065, 16351, 924, 19206, 246161, 2962973, 8287251,
  47032711, 74366850, 365054834, 363564027, 1805524983, 1012701844, 5007362274, 2256651295,
  676945988, 21119909349, 18910715, 41995069229, 925245284126]
/-- Mask chunk for `(m = 16, r = 64)`. -/
def rkmMkP_m16_r64_s2_p0 : List Bool := [
  true, true, false, false, false, true, false, false, true, false, true, true, false, false,
  true, true, false, false, false, false, true, false, false, false, true, true, false, true,
  true, true, false, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, false, false, false, true, false,
  false, false, false, true, false, false, true]
/-- Mask chunk for `(m = 16, r = 64)`. -/
def rkmMkP_m16_r64_s3_p0 : List Bool := [
  false, true, false, false, true, false, true, true, false, true, true, false, false, true, true,
  false, true, false, false, true, false, false, false, true, true, false, false, true, false,
  false, true, true, false, false, true, true, false, false, true, true, false, false, true, true,
  true, true, true, false, false, false, true, true, true]
/-- Mask chunk for `(m = 16, r = 64)`. -/
def rkmMkP_m16_r64_s4_p0 : List Bool := [
  true, true, false, false, true, false, true, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, true, true, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, false, true, false, false, true, false, false, true, false, false, true, true, false,
  true, true, false, false, true, true]
/-- Mask chunk for `(m = 16, r = 64)`. -/
def rkmMkP_m16_r64_s5_p0 : List Bool := [
  true, false, false, true, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, true, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true]
/-- Mask chunk for `(m = 16, r = 64)`. -/
def rkmMkP_m16_r64_s6_p0 : List Bool := [
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, true, true, false, false, false, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 64)`. -/
def rkmMasks_m16_r64 : List (List Bool) := [
  [], [false, false, false, true], rkmMkP_m16_r64_s2_p0, rkmMkP_m16_r64_s3_p0,
  rkmMkP_m16_r64_s4_p0, rkmMkP_m16_r64_s5_p0, rkmMkP_m16_r64_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 64)`. -/
def rkmRow_m16_r64 : List ℕ := [
  266910, 719180, 952497, 911544, 11635163, 1943209, 23951879, 10750, 106905, 95075, 10689378,
  16441097, 3390695, 6369911, 8191108, 122949, 6265436, 16647479, 2103825, 9852862, 11370664,
  14227772, 17721492, 103736129, 17950864, 848892, 5103256, 153571891, 31557396, 1682520,
  50175013, 397606235, 234159463, 36768217, 44380751, 278032957, 30484309, 74166543, 135930390,
  9259180, 300105583, 11355604, 134450034, 691130738, 188712129, 71084442, 635362051, 7772265,
  1634938674, 1138605, 851915855, 1419284316, 106942518, 545721858, 1186355555, 2792901390,
  67798999, 3014435722, 338248289, 3879914484, 26647923177, 133775662, 33392999799, 920176096736]
/-- Prefix-kick masks for `(m = 32, r = 10)`. -/
def rkmMasks_m32_r10 : List (List Bool) := [
  [false, false, true, true, false, true, true],
  [false, false, true, false, true, true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 10)`. -/
def rkmRow_m32_r10 : List ℕ := [
  89, 1121, 440320, 548578, 193967, 135700711, 607058678, 76885642, 21593673343, 977585497447]
/-- Mask chunk for `(m = 32, r = 20)`. -/
def rkmMkP_m32_r20_s1_p0 : List Bool := [
  true, false, false, true, true, false, false, false, true, false, false, true, true, false,
  true, true]
/-- Mask chunk for `(m = 32, r = 20)`. -/
def rkmMkP_m32_r20_s2_p0 : List Bool := [
  true, false, true, false, true, false, true, true, false, true, false, true, true, false, true,
  true, false, true, true]
/-- Prefix-kick masks for `(m = 32, r = 20)`. -/
def rkmMasks_m32_r20 : List (List Bool) := [
  [true, true, false, true, true], rkmMkP_m32_r20_s1_p0, rkmMkP_m32_r20_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 20)`. -/
def rkmRow_m32_r20 : List ℕ := [
  16, 306, 187, 1946, 81, 160527, 1214, 380980, 5478637, 25622703, 40643872, 5185602, 5424,
  1533260380, 97993484, 436218511, 6172104212, 109189292, 19032177019, 972541575264]
/-- Mask chunk for `(m = 32, r = 44)`. -/
def rkmMkP_m32_r44_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true, false,
  false, true, true, false, false, true, true, true, false, false, true, true, false, false, true,
  true]
/-- Mask chunk for `(m = 32, r = 44)`. -/
def rkmMkP_m32_r44_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, false, true, false, false, true, true,
  false, true, false, true, false, true, true]
/-- Prefix-kick masks for `(m = 32, r = 44)`. -/
def rkmMasks_m32_r44 : List (List Bool) := [
  [], [], rkmMkP_m32_r44_s2_p0, rkmMkP_m32_r44_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 44)`. -/
def rkmRow_m32_r44 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 43, 5, 2301, 623,
  55515, 34865, 225390, 532427, 2583051, 342242, 14189984, 35246059, 95884285, 611857383,
  1098238044, 6012053334, 23098486182, 37099230162, 931931036875]
/-- Mask chunk for `(m = 64, r = 18)`. -/
def rkmMkP_m64_r18_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, true, true, true, true, false, false, true,
  true, true]
/-- Mask chunk for `(m = 64, r = 18)`. -/
def rkmMkP_m64_r18_s1_p0 : List Bool := [
  false, false, false, false, false, false, true, false, false, true, false, true, false, true,
  false, false, true]
/-- Prefix-kick masks for `(m = 64, r = 18)`. -/
def rkmMasks_m64_r18 : List (List Bool) := [rkmMkP_m64_r18_s0_p0, rkmMkP_m64_r18_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 18)`. -/
def rkmRow_m64_r18 : List ℕ := [
  0, 0, 0, 0, 0, 1, 0, 41, 268, 13381, 49714, 2326441, 12273401, 49108322, 119051110, 101700062,
  11610694525, 988104782511]
/-- Mask chunk for `(m = 64, r = 26)`. -/
def rkmMkP_m64_r26_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, true, true, false, false, false, true, true]
/-- Mask chunk for `(m = 64, r = 26)`. -/
def rkmMkP_m64_r26_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  true, true, false, true, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 64, r = 26)`. -/
def rkmMasks_m64_r26 : List (List Bool) := [rkmMkP_m64_r26_s0_p0, rkmMkP_m64_r26_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 26)`. -/
def rkmRow_m64_r26 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 63, 629, 0, 5103, 69077, 869917, 1909296, 36241077,
  145599420, 118604381, 695628294, 78611407, 9685328973, 989237131966]
/-- Prefix-kick masks for `(m = 128, r = 5)`. -/
def rkmMasks_m128_r5 : List (List Bool) := [
  [true, true, true], [true, true, false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 5)`. -/
def rkmRow_m128_r5 : List ℕ := [26505, 2292, 69146171, 32226660463, 967704164504]
/-- Mask chunk for `(m = 128, r = 22)`. -/
def rkmMkP_m128_r22_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 22)`. -/
def rkmMasks_m128_r22 : List (List Bool) := [rkmMkP_m128_r22_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 22)`. -/
def rkmRow_m128_r22 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1050, 17017, 158684, 2808779, 14348716, 251390994,
  34249196, 8316323608, 991380701580]
/-- Mask chunk for `(m = 128, r = 29)`. -/
def rkmMkP_m128_r29_s0_p0 : List Bool := [
  false, false, false, false, true, true, true, false, false, true, true, false, false, false,
  false, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 128, r = 29)`. -/
def rkmMkP_m128_r29_s1_p0 : List Bool := [
  true, false, true, true, false, true, false, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, true, false, false, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 29)`. -/
def rkmMasks_m128_r29 : List (List Bool) := [rkmMkP_m128_r29_s0_p0, rkmMkP_m128_r29_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 29)`. -/
def rkmRow_m128_r29 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 73, 782, 11132, 83447, 71, 768070, 1261327,
  8121388, 4441012, 3468773, 676152266, 3574247118, 6902494249, 988828949641]
/-- Prefix-kick masks for `(m = 128, r = 34)`. -/
def rkmMasks_m128_r34 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 34)`. -/
def rkmRow_m128_r34 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11, 271, 376, 28567, 2509,
  2290021, 192912, 155851365, 68676716, 10334543155, 6134174989, 983304238269]
/-- Prefix-kick masks for `(m = 256, r = 8)`. -/
def rkmMasks_m256_r8 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 8)`. -/
def rkmRow_m256_r8 : List ℕ := [0, 0, 35, 6392, 1422713, 8037763, 19835727047, 980154805954]
/-- Mask chunk for `(m = 256, r = 20)`. -/
def rkmMkP_m256_r20_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, true, true]
/-- Prefix-kick masks for `(m = 256, r = 20)`. -/
def rkmMasks_m256_r20 : List (List Bool) := [rkmMkP_m256_r20_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 20)`. -/
def rkmRow_m256_r20 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 77, 6444, 480203, 49999089, 390199819, 8284659461,
  991274654457]
/-- Prefix-kick masks for `(m = 256, r = 29)`. -/
def rkmMasks_m256_r29 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 29)`. -/
def rkmRow_m256_r29 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 70, 5969, 43418, 2846402,
  19353521, 1398985358, 5995167589, 992583596862]
/-- Prefix-kick masks for `(m = 512, r = 4)`. -/
def rkmMasks_m512_r4 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 4)`. -/
def rkmRow_m512_r4 : List ℕ := [2091303, 492404310, 39310114265, 960195387861]
/-- Mask chunk for `(m = 512, r = 13)`. -/
def rkmMkP_m512_r13_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, true, true, true, true]
/-- Prefix-kick masks for `(m = 512, r = 13)`. -/
def rkmMasks_m512_r13 : List (List Bool) := [rkmMkP_m512_r13_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 13)`. -/
def rkmRow_m512_r13 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 96, 36277, 905663, 194097, 12064327672, 987934535920]
/-- Mask chunk for `(m = 512, r = 23)`. -/
def rkmMkP_m512_r23_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, true, true, true]
/-- Mask chunk for `(m = 512, r = 23)`. -/
def rkmMkP_m512_r23_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 512, r = 23)`. -/
def rkmMasks_m512_r23 : List (List Bool) := [rkmMkP_m512_r23_s0_p0, rkmMkP_m512_r23_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 23)`. -/
def rkmRow_m512_r23 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 74, 3685, 39123, 2864, 3832794, 21526614,
  6985210094, 992989383972]
/-- Mask chunk for `(m = 512, r = 128)`. -/
def rkmMkP_m512_r128_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 512, r = 128)`. -/
def rkmMkP_m512_r128_s0_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, false, false, true, false, false, true, true, false,
  false, true, true, true, true, true, true]
/-- Mask chunk for `(m = 512, r = 128)`. -/
def rkmMkP_m512_r128_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 512, r = 128)`. -/
def rkmMkP_m512_r128_s1_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, false, false, true, false,
  true, false, true, false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 512, r = 128)`. -/
def rkmMkP_m512_r128_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 512, r = 128)`. -/
def rkmMkP_m512_r128_s2_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, false, true, false, true, false, true, true,
  true, false, false, false, true]
/-- Prefix-kick masks for `(m = 512, r = 128)`. -/
def rkmMasks_m512_r128 : List (List Bool) := [
  rkmMkP_m512_r128_s0_p0 ++ rkmMkP_m512_r128_s0_p1,
  rkmMkP_m512_r128_s1_p0 ++ rkmMkP_m512_r128_s1_p1,
  rkmMkP_m512_r128_s2_p0 ++ rkmMkP_m512_r128_s2_p1, []]
/-- Row chunk `0` `(m = 512, r = 128)`. -/
def rkmRowP_m512_r128_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Row chunk `1` `(m = 512, r = 128)`. -/
def rkmRowP_m512_r128_p1 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 114, 0, 42, 264, 3296, 12360, 831, 6326817,
  639373, 4708520, 26795859, 2693592, 567532369, 23172017, 1573639833, 997794457411]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 128)`. -/
def rkmRow_m512_r128 : List ℕ := rkmRowP_m512_r128_p0 ++ rkmRowP_m512_r128_p1
/-- Prefix-kick masks for `(m = 1024, r = 3)`. -/
def rkmMasks_m1024_r3 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 3)`. -/
def rkmRow_m1024_r3 : List ℕ := [948372258, 53285924746, 945760391901]
/-- Prefix-kick masks for `(m = 1024, r = 10)`. -/
def rkmMasks_m1024_r10 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 10)`. -/
def rkmRow_m1024_r10 : List ℕ := [0, 0, 0, 0, 0, 363, 2441, 51626188, 15465492769, 984482878011]
/-- Unpacks `j` LSB-first bits of `< 2 ^ 50` word `w` (`FindAllJohnsonRampKickMuxTraj04`). -/
def rkmWbTraj04 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWbTraj04 j (Nat.div w 2)
/-- Concatenates `50`-bit `< 2 ^ 50` chunks (final length `rem`) into a `List Bool` mask. -/
def rkmMaskWordsTraj04 : ℕ → List ℕ → List Bool
  | _, [] => []
  | rem, [w] => rkmWbTraj04 rem w
  | rem, w :: v :: ws => rkmWbTraj04 50 w ++ rkmMaskWordsTraj04 rem (v :: ws)
/-- Krotov masks `(m = 4, r = 128)`. -/
def rkmMasksPack_m4_r128 : List (List Bool) := [[],[],rkmWbTraj04 7 127,
  rkmMaskWordsTraj04 14 [3665983,12416],rkmMaskWordsTraj04 11 [617666880313932,260701244,1408],
  rkmMaskWordsTraj04 27 [463255311580804,109071553676504,117440967],
  rkmMaskWordsTraj04 24 [375908847535015,375299901822323,12862622],[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 128)`. -/
def rkmRowPack_m4_r128 : List ℕ := [307426,76720,142407,8605,461596,168291,940239,2844741,105904,
  21,554246,173687,34625,2213993,1294025,364244,211156,12150,1250180,1216223,698676,6059111,
  1484059,235017,3657053,1436223,6025667,1015479,3210082,1186271,5745774,4306925,683646,148694,
  1301444,106537,1282220,4475674,6366020,11576301,6203963,3964806,1101310,1000386,2938557,3117417,
  13966066,3581294,2495510,7470991,32365,4692122,8554823,2664061,70589252,14371247,39518481,
  15940801,74499022,151498307,103279682,60150168,35554614,62874491,385186,3492346,3841453,
  47812061,161398,7638981,15760952,20532094,60565222,72157110,31089598,110642365,35076900,
  65284965,68195338,12761733,101901309,74261480,34077306,24477094,57547137,74365222,186664018,
  84499981,12815294,79340466,179064010,115169243,51611656,364064750,125884935,31518483,668167346,
  1408632256,21736646,224984336,478476904,87864267,8620940,71043023,2643549021,400643,763397138,
  947883573,324135337,1626940891,1638745337,35336319,75148,2127203801,500132275,1980265388,
  968194029,215678196,2756784336,983511135,4647211786,609493476,1401901219,45654092153,790997903,
  4176570242,220377570704,698944105971]
/-- Krotov masks `(m = 16, r = 3)`. -/
def rkmMasksPack_m16_r3 : List (List Bool) := [rkmWbTraj04 1 1,rkmWbTraj04 2 3,rkmWbTraj04 4 13,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 3)`. -/
def rkmRowPack_m16_r3 : List ℕ := [716869,61430587392,938568572367]
/-- Krotov masks `(m = 64, r = 53)`. -/
def rkmMasksPack_m64_r53 : List (List Bool) := [[],rkmWbTraj04 37 122198745881,
  rkmWbTraj04 44 15825723823269,rkmWbTraj04 49 452288689362249,
  rkmMaskWordsTraj04 1 [145841340179625,1],rkmMaskWordsTraj04 2 [176234677572820,2],
  rkmMaskWordsTraj04 2 [44023421378900,2],[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 53)`. -/
def rkmRowPack_m64_r53 : List ℕ := [0,0,0,0,0,0,0,0,0,40,0,1,6,1,1,4,0,0,5,98,51,407,2627,4621,
  8585,29164,10153,174674,108283,19704,285444,8321711,6234244,7438348,7345703,24553377,34024006,
  32357109,4169380,115038382,117928,287366562,18338507,286096094,36341967,36730072,365377085,
  22447605,810064369,9628032575,58099896,15927023612,972283835829]
/-- Krotov masks `(m = 32, r = 5)`. -/
def rkmMasksPack_m32_r5 : List (List Bool) := [[],rkmWbTraj04 1 1,rkmWbTraj04 3 6,rkmWbTraj04 4 9,
  []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 5)`. -/
def rkmRowPack_m32_r5 : List ℕ := [2929432,144895,23029138,35918399621,964055477543]
/-- Krotov masks `(m = 32, r = 46)`. -/
def rkmMasksPack_m32_r46 : List (List Bool) := [[],rkmWbTraj04 15 28209,rkmWbTraj04 35 30482314090,
  rkmWbTraj04 40 879237611572,rkmWbTraj04 43 6986413025626,rkmWbTraj04 44 8935145251350,
  rkmWbTraj04 45 19830625970853,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 46)`. -/
def rkmRowPack_m32_r46 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,110,20,1346,952,1795,788,
  315,1586,135533,235282,226173,28603,11490,49,3520635,67497717,1081910,365445,190506394,6739233,
  81931647,663904339,50489130,155677556,2289663251,190232225,22895527597,973402217564]
/-- Krotov masks `(m = 8, r = 6)`. -/
def rkmMasksPack_m8_r6 : List (List Bool) := [[],[],rkmWbTraj04 3 6,rkmWbTraj04 4 9,
  rkmWbTraj04 5 16,rkmWbTraj04 5 16,rkmWbTraj04 5 16,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 6)`. -/
def rkmRowPack_m8_r6 : List ℕ := [283551,25081439,50874404,110978839,72997348651,926815262218]
/-- Krotov masks `(m = 16, r = 44)`. -/
def rkmMasksPack_m16_r44 : List (List Bool) := [[],rkmWbTraj04 27 67108867,rkmWbTraj04 26 61950302,
  rkmWbTraj04 42 3875683005620,rkmWbTraj04 43 5302858554628,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 44)`. -/
def rkmRowPack_m16_r44 : List ℕ := [10710,83935,112249,468107,110667,229862,8602,5970476,5152332,
  6179434,52391,3005453,2986224,256697,1114363,15269663,18172789,2830591,11008213,3138358,6838196,
  293813,638278,431043,38973192,137445810,54391666,2175,27220749,113302202,5882813,315773119,
  222199053,750199,562521575,166182463,12779834667,11010903086,227362054,18129754,18753252867,
  22054802,40690751113,914768702875]
/-- Krotov masks `(m = 8, r = 35)`. -/
def rkmMasksPack_m8_r35 : List (List Bool) := [rkmWbTraj04 8 223,rkmWbTraj04 8 192,
  rkmWbTraj04 8 254,rkmWbTraj04 1 1,rkmWbTraj04 8 251,rkmWbTraj04 3 7,rkmWbTraj04 8 247,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 35)`. -/
def rkmRowPack_m8_r35 : List ℕ := [275759025,2086358,12873042485,301205300,38730393131,
  134946159466,809601313577,3269850948]
/-- Krotov masks `(m = 4, r = 48)`. -/
def rkmMasksPack_m4_r48 : List (List Bool) := [[],[],[],rkmWbTraj04 32 4294960266,
  rkmWbTraj04 43 5428839134563,rkmWbTraj04 38 168148310089,rkmWbTraj04 38 137441051520,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 48)`. -/
def rkmRowPack_m4_r48 : List ℕ := [31134477,2020724,21473422,37460455,3658725,74257988,10761,
  96787074,2830127,30416619,54592868,44731364,56436450,21689376,40802789,22996469,13470133,
  50517377,37909085,55951595,226608172,44393,194274696,162602741,126945545,291182439,66629051,
  310065736,747308610,1034143021,646228635,868474555,8099639457,601127434,4172132054,29044972634,
  36280289,14281276899,130098322399,273387308830,278814954995,169527365333,66287482889,
  17072739233,2871138174,301917690,17907908,454053]
/-- Krotov masks `(m = 4, r = 9)`. -/
def rkmMasksPack_m4_r9 : List (List Bool) := [[],rkmWbTraj04 1 1,rkmWbTraj04 5 27,rkmWbTraj04 7 109,
  [],rkmWbTraj04 8 136,[],[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 9)`. -/
def rkmRowPack_m4_r9 : List ℕ := [6551099,183961541,18635348,678817777,4230262591,2223412093,
  192429670,161761537173,830704312076]
/-- Krotov masks `(m = 64, r = 30)`. -/
def rkmMasksPack_m64_r30 : List (List Bool) := [rkmWbTraj04 26 58720256,rkmWbTraj04 30 536870914,
  rkmWbTraj04 18 230827,rkmWbTraj04 24 14841732,rkmWbTraj04 27 105535863,rkmWbTraj04 28 136455708,
  rkmWbTraj04 29 289972549,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 30)`. -/
def rkmRowPack_m64_r30 : List ℕ := [0,0,0,0,0,1,53,14,16,220,0,51,57,5152,168,12123,20536,3665,
  370359,641744,482384,105227,18717817,26130740,4663665,72466804,214501088,163452649,9353934573,
  990144490329]
/-- Krotov masks `(m = 4, r = 10)`. -/
def rkmMasksPack_m4_r10 : List (List Bool) := [[],[],rkmWbTraj04 6 50,rkmWbTraj04 8 146,
  rkmWbTraj04 5 16,rkmWbTraj04 9 287,rkmWbTraj04 5 28,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 10)`. -/
def rkmRowPack_m4_r10 : List ℕ := [28922623,190429893,153750045,4093727,3452815453,4941972498,
  1947793696,227561971,167364274486,821679829753]
/-- Krotov masks `(m = 4, r = 32)`. -/
def rkmMasksPack_m4_r32 : List (List Bool) := [[],[],[],rkmWbTraj04 31 1073807080,
  rkmWbTraj04 25 30198058,rkmWbTraj04 30 843797962,[],[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 32)`. -/
def rkmRowPack_m4_r32 : List ℕ := [1887,446617,2536774,17520581,19188734,3130114,4124442,63699030,
  1676102,631426,18099826,223709,91886223,334701596,147295057,1367574723,1604466255,358257422,
  162392838,77996120,1240549088,878317603,446507914,718906129,4654618511,208666365,1251187507,
  15978571776,10760283138,3770942875,192595786718,763219811309]
/-- Krotov masks `(m = 16, r = 11)`. -/
def rkmMasksPack_m16_r11 : List (List Bool) := [[],rkmWbTraj04 5 23,rkmWbTraj04 7 117,
  rkmWbTraj04 9 437,rkmWbTraj04 10 549,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 11)`. -/
def rkmRowPack_m16_r11 : List ℕ := [4421,51559,4251341,10607186,15510951,26854416,60287600,
  1300295832,587237775,38635344083,959359554756]
/-- Krotov masks `(m = 16, r = 28)`. -/
def rkmMasksPack_m16_r28 : List (List Bool) := [[],rkmWbTraj04 26 58720355,rkmWbTraj04 23 7616760,
  rkmWbTraj04 27 113945421,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 28)`. -/
def rkmRowPack_m16_r28 : List ℕ := [16172,46683,1011,5,587850,4031403,6570670,7158770,26512625,
  3094599,16324521,90902420,186646174,328476319,479249220,468968336,39005438,34737002,2023548465,
  760779739,33384351,5782883573,665825161,2969633839,13806769882,110819124,37790029292,
  934363992928]
/-- Krotov masks `(m = 16, r = 56)`. -/
def rkmMasksPack_m16_r56 : List (List Bool) := [rkmWbTraj04 16 54400,rkmWbTraj04 16 37376,
  rkmWbTraj04 16 59009,rkmWbTraj04 16 38273,rkmWbTraj04 14 10240,rkmWbTraj04 16 41217,
  rkmWbTraj04 14 9246,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 56)`. -/
def rkmRowPack_m16_r56 : List ℕ := [1020985,454083577,422683245,41238091859,337907829,14597299339,
  66443877676,866253943800,1686102537,44098302,1114252650,7339944308,1984070,15631002,16199189,
  344040]
/-- Krotov masks `(m = 32, r = 48)`. -/
def rkmMasksPack_m32_r48 : List (List Bool) := [rkmWbTraj04 18 148544,rkmWbTraj04 32 4118059008,
  rkmWbTraj04 32 3819143170,rkmWbTraj04 32 3934289936,rkmWbTraj04 32 4026335265,
  rkmWbTraj04 27 88801304,rkmWbTraj04 32 3866509893,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 48)`. -/
def rkmRowPack_m32_r48 : List ℕ := [24255985,625072940,80241348,2785892613,50192556,603948,
  484160879,5678439499,1572923035,926377717,7628211388,8947070148,312934111103,15578959215,
  294315007,503887950751,619441353,137380517846,3103862,154285898,299037463,41107511,1664194,
  117776,29,680,15,0,0,0,0,0]
/-- Krotov masks `(m = 16, r = 14)`. -/
def rkmMasksPack_m16_r14 : List (List Bool) := [rkmWbTraj04 5 30,rkmWbTraj04 11 1778,
  rkmWbTraj04 13 6721,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 14)`. -/
def rkmRowPack_m16_r14 : List ℕ := [100903,1469104,1955955,12897652,6731835,89946631,955709649,
  880988,228589169,5586531573,3514625326,403221010,38495820362,950701469728]
/-- Krotov masks `(m = 16, r = 23)`. -/
def rkmMasksPack_m16_r23 : List (List Bool) := [[],rkmWbTraj04 18 255589,rkmWbTraj04 21 1796781,
  rkmWbTraj04 22 2155870,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 23)`. -/
def rkmRowPack_m16_r23 : List ℕ := [1636,2976,154,243,40669,138201,587885,1149711,529034,3801588,
  3779114,12531445,198331859,219961931,626531100,17829665,886294314,428534002,2311978656,
  9227876526,85869704,44699920643,941274308548]
/-- Krotov masks `(m = 8, r = 15)`. -/
def rkmMasksPack_m8_r15 : List (List Bool) := [[],rkmWbTraj04 2 3,rkmWbTraj04 13 6552,
  rkmWbTraj04 14 8874,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 15)`. -/
def rkmRowPack_m8_r15 : List ℕ := [102328,27776,252452,3049966,40147074,102819967,513535319,
  642794537,2507432888,1648947739,1030972024,16717482772,95089963,80684855275,896012489661]
/-- Krotov masks `(m = 64, r = 19)`. -/
def rkmMasksPack_m64_r19 : List (List Bool) := [[],[],[],rkmWbTraj04 10 902,rkmWbTraj04 15 27814,
  rkmWbTraj04 17 112043,rkmWbTraj04 18 142009,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 19)`. -/
def rkmRowPack_m64_r19 : List ℕ := [0,0,1,13,0,53,4664,9531,0,43831,358670,2973412,1763405,217989,
  48359647,67671892,117505248,11253984837,988507106574]
/-- Krotov masks `(m = 4, r = 30)`. -/
def rkmMasksPack_m4_r30 : List (List Bool) := [[],[],rkmWbTraj04 15 32765,rkmWbTraj04 23 7831552,
  rkmWbTraj04 25 27263009,rkmWbTraj04 26 58720326,rkmWbTraj04 28 178258737,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 30)`. -/
def rkmRowPack_m4_r30 : List ℕ := [25966980,879685,88447417,94293393,210808800,430868249,27455692,
  94596860,1590900,1881865984,926049990,1224155114,1616372614,8290474845,95434013342,240146287038,
  293154166064,215105718042,100607754126,32374805172,7107346684,1007875047,88345942,4673712,
  146803,2677,26,0,0,0]
/-- Cumulative `2`-lane trajectory head invariant (`Traj02` -> `Traj04`). -/
def rkmTrajLaneProp_04 : Prop :=
  rkmTrajLaneProp_02 ∧ (rkmRow_m2_r10.head? = some 14830867)
/-- Proof of `rkmTrajLaneProp_04` in `O(1)` kernel steps. -/
theorem rkmTrajLaneOk_04 : rkmTrajLaneProp_04 :=
  ⟨rkmTrajLaneOk_02, rfl⟩
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
private def wc_rkmTraj_m512_r128_s0_hb_p0 : List ℕ := [139708527131648,196612106941671,
  239614964260957,275313078200141,306274366143083,333822118878071,358746062118127,381563054323834,
  402633674747642,422221575600259,440526616652380,457704693269368,473880264050675,489154619927606,
  503611542589810,517321295256413,530343510617702,542729327551799,554523002847370,565763147730524,
  576483690908615,586714638744769,596482682565754,605811689143957,614723100749261,623236264384837,
  631368704974936,639136353759042,646553740564485,653634156708347,660389793833649,666831862885176,
  672970696585787,678815838119528,684376118216234,689659722429187,694674250077400,699426766068284,
  703923846610596,708171619660861,712175800810700,715941725211217,719474376039048,722778409932798,
  725858179765557,728717755066432,731360940359818,733791291653771,736012131277285,738026561239360,
  739837475259826,741447569602181,742859352821764,744075154527910,745097133245998,745927283454169,
  746567441859744,747019292971737,747284374018235,747364079250556,747259663669960,746972246207108,
  746502812379307,745852216445888]
private def wc_rkmTraj_m512_r128_s0_hb_p1 : List ℕ := [745021183077575,744010308551533,
  742820061479689,741450783074015,739902686948507,738175858453712,736270253535592,734185697106411,
  731921880910928,729478360866579,726854553851291,724049733907162,721063027822214,717893410045818,
  714539696885897,711000539927644,707274418603968,703359631836985,699254288657405,694956297694217,
  690463355410433,685772932941106,680882261367136,675788315231555,670487794073400,664977101716811,
  659252323008319,653309197641875,647143090646914,640748959037085,634121314022961,627254178076854,
  620141035996352,612774778938410,605147640178469,597251121077071,589075905393605,580611759651435,
  571847416701405,562770438911315,553367056471704,543621975075307,533518145588156,523036486125808,
  512155543946694,500851080432959,489095556629736,476857488561449,464100629591191,450782919434517,
  436855112786340,422258959286182,406924740969497,390767865725966,373684032144518,355542156107966,
  336173643410528,315355393344302,292781366384077,268011601735083,240371965024013,208729739581982,
  170880875125065,121148571727761]
private def wc_rkmTraj_m512_r128_s0_hb : List ℕ := pCat wc_rkmTraj_m512_r128_s0_hb_p0
  wc_rkmTraj_m512_r128_s0_hb_p1
private def wc_rkmTraj_m512_r128_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTraj_m512_r128_s0_v1_p0 : List ℕ := [2008245822571503,2026156041973173,
  2058375965213835,2105846185344900,2165370175957402,2229921528912142,2290330048152803,
  2337672945448726,2365472301029262,2370997193975145,2355407284007177,2322914674322109,
  2279409138194349,2231036875256978,2183097148379076,2139423147941287,2102232947802850,
  2072323859005024,2049447176179162,2032720756376189,2020985079949566,2013059536356383,
  2007894927994473,2004640888398891,2002655077865999,2001479562465539,2000803703730586,
  2000425858559922,2000220250946918,2000111252079684,2000054912619393,2000026498920239,
  2000012507736614,2000005777127559,2000002612178543,2000001156682998,2000000501762561,
  2000000213302583,2000000088887356,2000000036320608,2000000014556283,2000000005723205,
  2000000002208105,2000000000836147,2000000000310823,2000000000113443,2000000000040657,
  2000000000014309,2000000000004944,2000000000001675,2000000000000555,2000000000000179,
  2000000000000054,2000000000000014,2000000000000002,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m512_r128_s0_v1_p1 : List ℕ := [2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m512_r128_s0_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m512_r128_s0_v1 : List ℕ := pCat wc_rkmTraj_m512_r128_s0_v1_p0 (pCat
  wc_rkmTraj_m512_r128_s0_v1_p1 wc_rkmTraj_m512_r128_s0_v1_p2)
private def wc_rkmTraj_m512_r128_s0_v2_p0 : List ℕ := [2000000001683603,2000000011877517,
  2000000058938983,2000000237534650,2000000824632742,2000002546848999,2000007141745813,
  2000018440229288,2000044294632267,2000099761484799,2000211974414787,2000427050335666,
  2000819097333573,2001500891895426,2002635072738709,2004443842632776,2007214353206256,
  2011296422800909,2017089285341631,2025014922126753,2035477282634459,2048809233672664,
  2065212020078386,2084694795058518,2107023701819170,2131690437879067,2157908823332751,
  2184644614054571,2210679071720488,2234701423655936,2255420335354356,2271680888392202,
  2282572074343034,2287510822663794,2286291911357308,2279098131070955,2266470837170502,
  2249246481155235,2228468939440103,2205289837110573,2180869381890134,2156288664531716,
  2132481444418333,2110189793695028,2089944307323274,2072066472467865,2056688600803818,
  2043785605059427,2033212783257002,2024744448411546,2018109419051996,2013020770619774,
  2009198588755737,2006385587503227,2004356266894831,2002920767776922,2001924773964164,
  2001246781036296,2000793875538264,2000496920584500,2000305781375480,2000184985772071,
  2000110021949897,2000064334101230]
private def wc_rkmTraj_m512_r128_s0_v2_p1 : List ℕ := [2000036985197408,2000020904515770,
  2000011616496696,2000006346397921,2000003408689175,2000001799878159,2000000934283596,
  2000000476732975,2000000239116774,2000000117884668,2000000057119908,2000000027199905,
  2000000012727993,2000000005852265,2000000002643718,2000000001173229,2000000000511411,
  2000000000218932,2000000000092029,2000000000037977,2000000000015378,2000000000006107,
  2000000000002376,2000000000000903,2000000000000333,2000000000000117,2000000000000037,
  2000000000000010,2000000000000001,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m512_r128_s0_v2_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m512_r128_s0_v2 : List ℕ := pCat wc_rkmTraj_m512_r128_s0_v2_p0 (pCat
  wc_rkmTraj_m512_r128_s0_v2_p1 wc_rkmTraj_m512_r128_s0_v2_p2)
private def wc_rkmTraj_m512_r128_s0_ck3_p0 : List ℕ := [2000000000000003,2000000000000000,
  2000000000000004,2000000000000002,2000000000000005,2000000000000007,2000000000000004,
  2000000000000004,2000000000000003,2000000000000005,2000000000000011,2000000000000040,
  2000000000000120,2000000000000402,2000000000001313,2000000000004122,2000000000012508,
  2000000000036652,2000000000103671,2000000000283489,2000000000750377,2000000001925004,
  2000000004791221,2000000011581327,2000000027211860,2000000062202044,2000000138428611,
  2000000300139776,2000000634418260,2000001308093560,2000002632390414,2000005172852678,
  2000009930757777,2000018633605343,2000034186151266,2000061348909734,2000107725917301,
  2000185154124963,2000311587513083,2000513552629807,2000829210341120,2001311983000645,
  2002034591264953,2003093189962304,2004611105836179,2006741480996698,2009667946613605,
  2013602335511571,2018778440777900,2025440990010245,2033829368394821,2044156199340458,
  2056581651593848,2071185213506129,2087937540004286,2106675683277636,2127085399688829,
  2148694137421986,2170877659862812,2192882040850727,2213861074889524,2232927176243543,
  2249211874490304,2261930367478298]
private def wc_rkmTraj_m512_r128_s0_ck3_p1 : List ℕ := [2270443564056965,2274310858649988,
  2273327620732124,2267542993225943,2257255861777984,2242989450643827,2225447529453255,
  2205457298619029,2183905359887476,2161673604954118,2139581358447251,2118338831188829,
  2098515129602696,2080522042128353,2064612897980100,2050894227587917,2039346915624762,
  2029853087345346,2022225066986081,2016233276414521,2011630743228334,2008172792264956,
  2005631356551073,2003804057232393,2002518709283462,2001634198541053,2001038768993747,
  2000646702379393,2000394218483650,2000235224984924,2000137341331829,2000078439990677,
  2000043805466010,2000023910987363,2000012751342920,2000006640487006,2000003375282359,
  2000001673592202,2000000809026003,2000000381040561,2000000174732869,2000000077955143,
  2000000033808335,2000000014240317,2000000005819709,2000000002305116,2000000000883824,
  2000000000327586,2000000000117191,2000000000040388,2000000000013378,2000000000004246,
  2000000000001284,2000000000000364,2000000000000094,2000000000000020,2000000000000003,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m512_r128_s0_ck3_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m512_r128_s0_ck3 : List ℕ := pCat wc_rkmTraj_m512_r128_s0_ck3_p0 (pCat
  wc_rkmTraj_m512_r128_s0_ck3_p1 wc_rkmTraj_m512_r128_s0_ck3_p2)
private def wc_rkmTraj_m512_r128_s0_ck4_p0 : List ℕ := [2000000000000003,2000000000000004,
  1999999999999999,1999999999999997,2000000000000000,2000000000000008,1999999999999997,
  2000000000000003,2000000000000002,1999999999999997,1999999999999995,2000000000000004,
  2000000000000005,2000000000000001,2000000000000003,2000000000000004,2000000000000000,
  2000000000000000,2000000000000012,2000000000000011,2000000000000006,2000000000000000,
  1999999999999993,2000000000000002,2000000000000005,2000000000000001,2000000000000002,
  2000000000000011,2000000000000001,1999999999999990,2000000000000004,2000000000000004,
  2000000000000010,2000000000000010,2000000000000011,2000000000000016,2000000000000010,
  2000000000000010,2000000000000014,2000000000000016,2000000000000019,2000000000000019,
  2000000000000037,2000000000000070,2000000000000174,2000000000000496,2000000000001425,
  2000000000004045,2000000000011314,2000000000030969,2000000000082917,2000000000217094,
  2000000000555780,2000000001391524,2000000003407705,2000000008163532,2000000019133534,
  2000000043880157,2000000098479795,2000000216310738,2000000465053598,2000000978723275,
  2000002016428570,2000004067259865]
private def wc_rkmTraj_m512_r128_s0_ck4_p1 : List ℕ := [2000008032365087,2000015532089087,
  2000029408976118,2000054526603766,2000098998052169,2000176011841012,2000306448673441,
  2000522485218966,2000872341642257,2001426223425153,2002283310458905,2003579339155339,
  2005493905058368,2008256111990990,2012146677789706,2017494191747808,2024663062727321,
  2034030978377336,2045954575493122,2060723586059415,2078505925046675,2099288792495868,
  2122823441279952,2148583217109047,2175745149946366,2203204201332053,2229625963799597,
  2253538320683695,2273455983945926,2288025087304014,2296169556696988,2297218207759379,
  2290992419856321,2277839067902097,2258601521221818,2234531476238933,2207154179706015,
  2178107167123512,2148976392437623,2121152836781216,2095727684358734,2073436216908871,
  2054651566061747,2039421324564398,2027534301116885,2018602219409990,2012141877987553,
  2007646463544099,2004639198323587,2002707103319943,2001516424047019,2000813667572626,
  2000417154127312,2000203752787631,2000094488166863,2000041432227756,2000017093286501,
  2000006594216853,2000002360220754,2000000775777322,2000000230897759,2000000060975592,
  2000000013834086,2000000002542391]
private def wc_rkmTraj_m512_r128_s0_ck4_p2 : List ℕ := [2000000000327758]
private def wc_rkmTraj_m512_r128_s0_ck4 : List ℕ := pCat wc_rkmTraj_m512_r128_s0_ck4_p0 (pCat
  wc_rkmTraj_m512_r128_s0_ck4_p1 wc_rkmTraj_m512_r128_s0_ck4_p2)
private def wc_rkmTraj_m512_r128_s0_ck5_p0 : List ℕ := [2000000000000003,2000000000000004,
  2000000000000005,1999999999999999,1999999999999999,1999999999999998,2000000000000000,
  2000000000000007,2000000000000010,2000000000000006,2000000000000007,1999999999999995,
  1999999999999992,1999999999999998,2000000000000007,2000000000000013,1999999999999995,
  1999999999999982,2000000000000006,2000000000000004,1999999999999998,2000000000000002,
  2000000000000009,2000000000000005,1999999999999993,1999999999999999,2000000000000005,
  2000000000000010,1999999999999994,1999999999999983,1999999999999990,2000000000000007,
  2000000000000018,2000000000000003,1999999999999991,2000000000000000,2000000000000009,
  2000000000000000,1999999999999981,1999999999999998,2000000000000010,2000000000000006,
  2000000000000015,2000000000000009,2000000000000004,1999999999999998,1999999999999991,
  2000000000000001,2000000000000008,1999999999999999,2000000000000009,2000000000000006,
  1999999999999999,1999999999999998,1999999999999999,1999999999999997,1999999999999993,
  2000000000000006,2000000000000015,2000000000000009,2000000000000002,2000000000000001,
  2000000000000015,2000000000000015]
private def wc_rkmTraj_m512_r128_s0_ck5_p1 : List ℕ := [2000000000000005,2000000000000012,
  2000000000000023,2000000000000021,2000000000000010,2000000000000011,2000000000000027,
  2000000000000022,2000000000000016,2000000000000023,2000000000000022,2000000000000027,
  2000000000000029,2000000000000021,2000000000000027,2000000000000030,2000000000000027,
  2000000000000031,2000000000000047,2000000000000017,1999999999999591,1999999999997462,
  1999999999990034,1999999999974769,1999999999993297,2000000000381982,2000000002892878,
  2000000014972624,2000000064292906,2000000243566654,2000000837585652,2000002656567497,
  2000007849376859,2000021752292710,2000056808423202,2000140309570665,2000328606085878,
  2000731218317078,2001548319675764,2003123267791617,2006006891139784,2011021070056714,
  2019296176646150,2032243333308515,2051415065329849,2078216518404931,2113463117207707,
  2156841525259926,2206407241105085,2258315205840633,2306989171534011,2345856911077909,
  2368607094347689,2370703481401481,2350711970072548,2310957378242637,2257189156471767,
  2197268171076512,2139262650414341,2089586196485955,2051794689791810,2026376825916979,
  2011459157666573,2004005052316545]
private def wc_rkmTraj_m512_r128_s0_ck5_p2 : List ℕ := [2000975491421708]
private def wc_rkmTraj_m512_r128_s0_ck5 : List ℕ := pCat wc_rkmTraj_m512_r128_s0_ck5_p0 (pCat
  wc_rkmTraj_m512_r128_s0_ck5_p1 wc_rkmTraj_m512_r128_s0_ck5_p2)
private def wc_rkmTraj_m512_r128_s0_ck6_p0 : List ℕ := [2000000000000003,2000000000000004,
  2000000000000006,2000000000000002,2000000000000005,2000000000000002,2000000000000005,
  2000000000000020,2000000000000002,1999999999999998,2000000000000004,2000000000000005,
  2000000000000004,1999999999999999,1999999999999997,2000000000000007,2000000000000004,
  1999999999999988,1999999999999987,1999999999999993,2000000000000008,2000000000000009,
  1999999999999993,1999999999999980,1999999999999994,2000000000000006,2000000000000024,
  2000000000000018,1999999999999995,2000000000000010,2000000000000012,1999999999999990,
  1999999999999997,2000000000000001,1999999999999997,1999999999999995,2000000000000006,
  2000000000000019,2000000000000018,1999999999999991,1999999999999961,1999999999999987,
  2000000000000029,2000000000000012,1999999999999991,1999999999999999,1999999999999995,
  1999999999999996,2000000000000003,2000000000000010,2000000000000013,1999999999999993,
  2000000000000000,2000000000000006,1999999999999996,1999999999999999,1999999999999987,
  1999999999999990,2000000000000007,1999999999999994,2000000000000007,2000000000000032,
  2000000000000009,1999999999999970]
private def wc_rkmTraj_m512_r128_s0_ck6_p1 : List ℕ := [1999999999999975,2000000000000012,
  2000000000000004,1999999999999989,2000000000000000,2000000000000015,2000000000000026,
  2000000000000004,1999999999999987,2000000000000013,2000000000000000,1999999999999980,
  2000000000000015,2000000000000017,2000000000000009,1999999999999998,1999999999999995,
  2000000000000000,1999999999999997,1999999999999991,2000000000000004,2000000000000006,
  1999999999999991,2000000000000001,2000000000000014,2000000000000008,2000000000000004,
  2000000000000013,2000000000000014,2000000000000020,2000000000000009,2000000000000013,
  2000000000000020,2000000000000024,2000000000000011,2000000000000021,2000000000000113,
  2000000000000204,1999999999999271,1999999999997620,2000000000005423,2000000000028763,
  1999999999974851,1999999999695566,1999999999914511,2000000002812183,2000000004199391,
  1999999978883987,1999999932242611,2000000099035560,2000000775112018,2000000342815497,
  1999993527501785,1999985037597655,2000029047242549,2000195508608152,2000183520780911,
  1998704138309287,1994875904289701,1996410990671294,2034289829837949,2162543029093506,
  2403683247062857,2646015915431516]
private def wc_rkmTraj_m512_r128_s0_ck6_p2 : List ℕ := [2626152022033570]
private def wc_rkmTraj_m512_r128_s0_ck6 : List ℕ := pCat wc_rkmTraj_m512_r128_s0_ck6_p0 (pCat
  wc_rkmTraj_m512_r128_s0_ck6_p1 wc_rkmTraj_m512_r128_s0_ck6_p2)
private def wc_rkmTraj_m16_r64_s2_hb : List ℕ := [218318826666624,303925235505924,366322446909309,
  416170263333252,457664753619904,492990841687576,523465697956743,549959949963102,573086919999888,
  593299393123626,610943877610730,626293215683657,639567275705838,650946668342479,660582171752639,
  668601406666536,675113686805553,680213622322784,683983848968134,686497130429857,687818002323201,
  688004075098774,687107079133414,685173712175953,682246333333200,678363536514907,673560628188084,
  667870028427569,661321609931250,653942986448119,645759759638687,636795731536223,627073088352549,
  616612560265574,605433560958957,593554309999884,580991940596555,567762594840911,553881508190462,
  539363084657841,524220963943860,508468081558780,492116722818920,475178571475012,457664753619904,
  439585877432088,420952069235024,401773006287629,382057946666592,361815756554672,341054935209438,
  319783637852919,298009696693464,275740640265932,252983711254612,229745882944404,206033874429447,
  181854164694063,157213005668437,132116434350527,106570284076082,80580195010219,54151623926559,
  27289853333328]
private def wc_rkmTraj_m16_r64_s2_v0 : List ℕ := [2000000061315646,2000000711061754,
  2000005464714059,1999968607274484,2000145602180429,2000562451642446,2001856003349521,
  2005313330544142,2013356548716977,2029745425285472,2059093062614575,2105288216514424,
  2168956150191591,2244984556480390,2321779319420389,2383555504644975,2415422171607521,
  2409117925720235,2366425527918014,2298371592181550,2220691606405788,2148060120756795,
  2089906606824106,2049269503171405,2024271688942681,2010693033145842,2004183740059869,
  2001440071452655,2000430310809677,2000109448241516,2000022958231337,2000003746800195,
  2000000412238167]
private def wc_rkmTraj_m16_r64_s2_v1_p0 : List ℕ := [2000000555831729,2000002027961915,
  2000004995964321,2000009519300058,2000014704917902,2000018659910367,2000019158978606,
  2000014823378920,2000006168068051,1999995759045466,1999987347647616,1999984189393208,
  1999987567992640,1999995964341495,2000005808464361,2000013128698339,2000015429882258,
  2000012317213427,2000004698265393,1999994594280318,1999987067632129,1999989838014479,
  1999999837192452,1999983742379651,1999904492498086,1999836339143921,2000047464439561,
  2000737974321998,2001333790659745,2000056460010306,1995143357195854,1988199555347173,
  1987575817854343,2007731140153285,2062267427449901,2153594536546992,2266551823812975,
  2371974272513763,2439322150138870,2450732252056047,2407947405075271,2328944684990613,
  2237871272813285,2154955824432506,2091204831903024,2048593483360776,2023458384766927,
  2010262351178088,2004066138675708,2001457342872877,2000471561030024,2000137384369269,
  2000035910704367,2000008383818379,2000001738328753,2000000317841386,2000000050791679,
  2000000007013381,2000000000824490,2000000000080905,2000000000006444,2000000000000397,
  2000000000000017,2000000000000000]
private def wc_rkmTraj_m16_r64_s2_v1_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m16_r64_s2_v1 : List ℕ := pCat wc_rkmTraj_m16_r64_s2_v1_p0
  wc_rkmTraj_m16_r64_s2_v1_p1
private def wc_rkmTraj_m16_r64_s3_hb : List ℕ := [190844434202256,266579815044000,322428419959345,
  367611139004897,405744840000000,438706450630328,467623630993261,493239184707933,516074544864861,
  536513256751818,554847723793645,571307262750837,586075880000000,599304037501407,611116725383730,
  621619169573501,630900971632454,639039177945332,646100598697140,652143589172494,657219437907708,
  661373462168210,664645881968319,667072523990983,668685393012193,669513138734928,669581438978792,
  668913315097894,667529391741267,665448110240974,662685902746125,659257332528574,655175204532922,
  650450649129802,645093181081077,639110734877189,632509676808183,625294793332101,617469254457847,
  609034549908469,599990394707633,590334599449410,580062898751483,569168729089005,557642944123112,
  545473451424732,532644748625464,519137328696611,504926912000000,489983444938529,474269778112533,
  457739895182670,440336497210211,421987638041921,402601920170661,382061429614149,360210970279989,
  336840933212655,311658525248562,284235986737076,253908409677943,219544246645625,178916657064615,
  126231728000000]
private def wc_rkmTraj_m16_r64_s3_v0_p0 : List ℕ := [1999999444168271,1999997972038085,
  2000004995964321,2000009519300058,2000014704917902,1999981340089633,2000019158978606,
  2000014823378920,1999993831931949,1999995759045466,2000012652352384,2000015810606792,
  1999987567992640,1999995964341495,1999994191535639,1999986871301661,2000015429882258,
  2000012317213427,2000004698265393,1999994594280318,2000012932367871,1999989838014479,
  1999999837192452,1999983742379651,2000095507501914,2000163660856079,2000047464439561,
  1999262025678002,1998666209340255,1999943539989694,1995143357195854,1988199555347173,
  2012424182145657,2007731140153285,2062267427449901,2153594536546992,2266551823812975,
  2371974272513763,2439322150138870,2450732252056047,2407947405075271,2328944684990613,
  2237871272813285,2154955824432506,2091204831903024,2048593483360776,2023458384766927,
  2010262351178088,2004066138675708,1998542657127123,1999528438969976,2000137384369269,
  2000035910704367,2000008383818379,1999998261671247,2000000317841386,2000000050791679,
  2000000007013381,2000000000824490,1999999999919095,2000000000006444,2000000000000397,
  1999999999999983,2000000000000000]
private def wc_rkmTraj_m16_r64_s3_v0_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m16_r64_s3_v0 : List ℕ := pCat wc_rkmTraj_m16_r64_s3_v0_p0
  wc_rkmTraj_m16_r64_s3_v0_p1
private def wc_rkmTraj_m16_r64_s3_v1_p0 : List ℕ := [2000002554408315,2000000042996741,
  2000031205190539,1999978952290879,2000068915457626,1999813806405045,2000452174629832,
  1998962791765194,2002053616780164,1996442545763027,2005272234034352,1993624112121296,
  2005935233945290,1996659646031114,1999096413417109,2004586637519637,1994847564517568,
  2001819021815820,2003009764486574,1995017812595559,2001994044424193,2003006930421891,
  1995549608940899,2000529395652412,2004009220952430,1996739279159634,1998382704445315,
  2003581690004056,2000321865864000,1995806488938501,2002095440124248,2002584251974122,
  1997781135042718,1997796330659379,2002477389151565,2002514024493668,1996289123800944,
  1997854941308403,2004259142358526,2002603096378971,1995877872309625,1994603458435269,
  2003714181378920,2010973650778948,1999417063796933,1981204886113551,1987245783584791,
  2021068909285100,2044988726212841,2014863840731814,1934486119084289,1876039319251629,
  1925638316784111,2099341085791075,2321649193705792,2485161254444935,2525587331673410,
  2450585521506342,2316375348693195,2183932806568885,2088378050788135,2034667670625575,
  2010816700238866,2002544575829471]
private def wc_rkmTraj_m16_r64_s3_v1_p1 : List ℕ := [2000392818062403]
private def wc_rkmTraj_m16_r64_s3_v1 : List ℕ := pCat wc_rkmTraj_m16_r64_s3_v1_p0
  wc_rkmTraj_m16_r64_s3_v1_p1
private def wc_rkmTrajPack_m4_r128_s4_hb_p0 : List ℕ := [169856570514176,238336797978709,
  289603331846677,331751114285500,367941749404225,399809508186817,428332701437184,454153583549982,
  477721604571120,499366429421917,519338753777373,537834759143830,555011583107389,570997543374940,
  585899142565353,599806014628184,612794508755731,624930344306381,636270615894103,646865333630008,
  656758624218875,665989680247420,674593519556637,682601599343346,690042317713840,696941427023940,
  703322377341932,709206604018944,714613770151172,719561972335705,724067916327599,728147067840468,
  731813782683591,735081419614828,737962438652201,740468487085236,742610475028672,744398642042363,
  745842616084578,746951465857994,747733747438247,748197545936084,748350512829773,748199899509775,
  747752587498909,747015115745449,745993705331375,744694281891457,743122495999520,741283741744806,
  739183173692882,736825722401189,734216108638468,731358856439299,728258305109501,724918620284707,
  721343804132767,717537704780514,713504025036527,709246330473849,704768056929759,700072517473786,
  695162908889856,690042317713840]
private def wc_rkmTrajPack_m4_r128_s4_hb_p1 : List ℕ := [684713725863667,679180015895516,
  673443975916370,667508304180350,661375613393662,655048434750724,648529221721962,641820353611958,
  634924138904961,627842818413294,620578568242881,613133502588863,605509676373246,597709087735496,
  589733680386121,581585345832484,573265925485344,564777212653951,556120954436948,547298853515729,
  538312569856445,529163722326363,519853890229874,510384614769051,500757400433305,490973716322389,
  481034997406651,470942645728218,460698031546505,450302494431227,439757344305869,429063862444389,
  418223302423718,407236891034488,396105829152234,384831292571180,373414432802604,361856377839621,
  350158232890133,338321081079582,326345984125032,314233982982031,301986098465608,289603331846677,
  277086665425058,264437063080234,251655470800927,238742817194496,225700013977091,212527956445491,
  199227523931440,185799580239304,172244974067810,158564539416556,144759095978005,130829449515582,
  116776392228496,102600703103849,88303148256608,73884481257918,59345443452294,44686764264125,
  29909161493956,15013341604958]
private def wc_rkmTrajPack_m4_r128_s4_hb : List ℕ := pCat wc_rkmTrajPack_m4_r128_s4_hb_p0
  wc_rkmTrajPack_m4_r128_s4_hb_p1
private def wc_rkmTrajPack_m4_r128_s4_v0_p0 : List ℕ := [2003324227590081,2003455427617349,
  2000667025909626,1997632910732696,1997284855059074,1999740292779404,1997635843227519,
  1997418879777017,1999690773819430,2002240211281006,2002790253887531,2000947868715316,
  2001711385183879,2003121798647221,2002306791404913,1999886925606465,1997423115545852,
  1996321229358968,1997090791517990,2000717275671917,2001930006503833,2004108148122865,
  1994677522019620,1994379712784423,1994566431132879,1994848412104474,1995572853507573,
  1998620280972699,2007853227136432,2028606116533742,2065882229252497,2121666888743247,
  2192566369815991,2269215017473529,2338217823380399,2386104481277231,2403647013943405,
  2388655884859580,2346155482275520,2286132270256691,2220079025125371,2157827555376006,
  2105694502173672,2066174308010197,2038765625099206,2021258994301795,2010916141610140,
  2005248022252764,2002361395472226,2000993817979072,2000390832779256,2000143433116873,
  2000049038366064,2000015584716570,2000004591317917,2000001249509760,2000000312747471,
  1999999928409622,2000000014877783,2000000002779633,2000000000460562,2000000000066334,
  1999999999991959,1999999999999228]
private def wc_rkmTrajPack_m4_r128_s4_v0_p1 : List ℕ := [2000000000000049]
private def wc_rkmTrajPack_m4_r128_s4_v0 : List ℕ := pCat wc_rkmTrajPack_m4_r128_s4_v0_p0
  wc_rkmTrajPack_m4_r128_s4_v0_p1
private def wc_rkmTrajPack_m4_r128_s4_v1_p0 : List ℕ := [1999771330872562,1999669121980171,
  1998745697272523,2001389201171499,1998960331788508,2001781052547838,1999778782862601,
  1998974647729743,2001050478312651,2000267983101599,2000033865551828,2002545491087007,
  2003524286595678,2002594519763324,2002455365683998,2002048644644542,2000017422999168,
  1998823836116341,2000185941815296,2001652834947106,2000803473054258,1998902154249438,
  1998201136688596,1998460282641438,1998152497692998,1997385808782005,1997664934027354,
  1999328527949133,2000773040852739,2000474505075700,1998948295718732,1998227831470851,
  1999672958665791,2002598895474332,2004950320128833,2005078876890762,2002936997045764,
  1999892529681014,1997633883903130,1997128595371706,1998243243922039,2000027760070726,
  2001325742632546,2001380306019685,2000226521959454,1998717596918559,1998074084497956,
  1999022629813614,2000926074616956,2001569852834691,1998126381326228,1989171771714468,
  1976802983548290,1967484212787475,1970664306864364,1995343756870462,2045987418843851,
  2119716181340435,2206206375389829,2290455666505557,2357255538718912,2395537515980740,
  2401001548102675,2376342044021333]
private def wc_rkmTrajPack_m4_r128_s4_v1_p1 : List ℕ := [2329420354185391,2270404822349186,
  2209009519011195,2152617327484209,2105546831540679,2069278593492689,2043232968724774,
  2025687274603806,2014548987515000,2007863248618927,2004058816413817,2002002345383984,
  2000944673804601,2000426423560605,2000184240833082,2000076215602402,2000030192918137,
  2000011455773948,2000004163179283,2000001449111910,2000000483086247,2000000154220256,
  2000000047139120,2000000013792970,2000000003862503,2000000001034902,2000000000265226,
  2000000000064992,2000000000015219,2000000000003402,2000000000000723,2000000000000144,
  2000000000000025,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m4_r128_s4_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m4_r128_s4_v1 : List ℕ := pCat wc_rkmTrajPack_m4_r128_s4_v1_p0 (pCat
  wc_rkmTrajPack_m4_r128_s4_v1_p1 wc_rkmTrajPack_m4_r128_s4_v1_p2)
private def wc_rkmTrajPack_m4_r128_s4_v2_p0 : List ℕ := [1999350953546348,1998642933953634,
  1998406354165498,1999085648750302,2000331153968886,2001127702816464,2000780833770719,
  1999735387961118,1999168634331711,1999673603291081,2000554115783272,2000646170957544,
  1999733240268927,1998820248501279,1998909848415723,1999798556245284,2000392258436187,
  2000104306406631,1999538592962038,1999623119251363,2000368813065356,2000874205005600,
  2000530890708397,1999820340806577,1999659833235099,2000168305848931,2000483316590016,
  1999902724262129,1998910350440939,1998756736261079,2000041809615808,2001967962152699,
  2003135402504864,2002952665207717,2002085100469563,2001547353176589,2001581624887346,
  2001585001446332,2001042570578062,2000278415666965,2000122432786379,2000883106178990,
  2001816809982805,2001742705303439,2000217607589896,1998084567628286,1996822754489444,
  1997283313266114,1998955236500576,2000390398816673,2000383143227186,1998903799372752,
  1997081737052355,1996352683584193,1997481029390396,2000116250077813,2003041282132145,
  2004834588810278,2004584018867975,2002405549040436,1999552001579112,1997873187987805,
  1998633569028310,2001310274613119]
private def wc_rkmTrajPack_m4_r128_s4_v2_p1 : List ℕ := [2003469621008860,2002385154188181,
  1997625858645540,1992491341877577,1992399836209194,2000534702674342,2013725843387326,
  2022299160424236,2015316915294376,1988628449980811,1950480255434914,1920350674591795,
  1920766600952734,1966320643761314,2055896149741793,2172170811965815,2288305720035609,
  2378070387742106,2424514781995065,2423838060381526,2383933398074559,2319459382618821,
  2246173584227727,2176701886901893,2118645209250665,2074756180296882,2044308211909440,
  2024749751110890,2013047530968016,2006498724203422,2003060681175498,2001363772065107,
  2000575111342086,2000229572758795,2000086745110493,2000031020927437,2000010495727812,
  2000003358279273,2000001015551221,2000000290025946,2000000078149080,2000000019846971,
  2000000004744645,2000000001066166,2000000000224818,2000000000044397,2000000000008190,
  2000000000001404,2000000000000220,2000000000000029,2000000000000002,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m4_r128_s4_v2_p2 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m4_r128_s4_v2 : List ℕ := pCat wc_rkmTrajPack_m4_r128_s4_v2_p0 (pCat
  wc_rkmTrajPack_m4_r128_s4_v2_p1 wc_rkmTrajPack_m4_r128_s4_v2_p2)
private def wc_rkmTrajPack_m4_r128_s5_hb_p0 : List ℕ := [148759800551882,209110283371101,
  254553123089572,292137671775326,324611901228586,353393674734250,379330230089644,402976778726800,
  424721163779731,444847352682627,463570901041856,481060185107016,497449823416181,512849540390038,
  527350234569381,541028260540843,553948529115670,566166802221578,577731424807208,588684654247099,
  599063696252177,608901522985765,618227527005999,627068049695375,635446812500893,643385272037709,
  650902914912796,658017504356147,664745287976624,671101173897651,677098880975941,682751067625717,
  688069442863942,693064862488876,697747412754557,702126483470529,706210832112123,710008640251534,
  713527563398522,716774775160253,719757006483691,722480580624258,724951444385878,727175196095903,
  729157110710534,730902162389578,732415044831775,733700189621742,734761782805586,735603779883338,
  736229919381676,736643735149266,736848567498865,736847573304604,736643735149266,736239869604465,
  735638634716278,734842536759738,733853936317513,732675053730934,731307973965127,729754650924199,
  728016911247206,726096457610821]
private def wc_rkmTrajPack_m4_r128_s5_hb_p1 : List ℕ := [723994871560163,721713615885108,
  719254036555473,716617364224663,713804715307750,710817092636284,707655385688546,704320370390227,
  700812708476738,697132946404316,693281513792880,689258721378981,685064758452237,680699689743122,
  676163451723920,671455848277774,666576545683073,661525066851587,656300784748744,650902914912796,
  645330506976235,639582435077169,633657387030104,627553852104084,621270107230777,614804201435021,
  608153938244462,601316855791986,594290204272982,587070920356963,579655598077119,572040455628506,
  564221297391447,556193470355533,547951813944015,539490602018273,530803475564517,521883364212033,
  512722394280247,503311780467838,493641697535481,483701127330941,473477675170621,462957347795350,
  452124282670312,440960415018207,429445064236504,417554414601350,405260855377999,392532130995317,
  379330230089644,365609908387143,351316686534298,336384075515394,320729631621892,304249175312076,
  286808008804448,268226978005440,248259117748956,226547705311229,202543641864037,175320213322696,
  143066450373328,101098063032914]
private def wc_rkmTrajPack_m4_r128_s5_hb : List ℕ := pCat wc_rkmTrajPack_m4_r128_s5_hb_p0
  wc_rkmTrajPack_m4_r128_s5_hb_p1
private def wc_rkmTrajPack_m4_r128_s5_v0_p0 : List ℕ := [1999350953546348,1998642933953634,
  2001593645834502,2000914351249698,2000331153968886,2001127702816464,1999219166229281,
  1999735387961118,1999168634331711,2000326396708919,2000554115783272,1999353829042456,
  2000266759731073,1998820248501279,1998909848415723,2000201443754716,1999607741563813,
  2000104306406631,2000461407037962,2000376880748637,1999631186934644,1999125794994400,
  1999469109291603,2000179659193423,1999659833235099,1999831694151069,1999516683409984,
  1999902724262129,1998910350440939,1998756736261079,1999958190384192,1998032037847301,
  1996864597495136,1997047334792283,2002085100469563,2001547353176589,2001581624887346,
  2001585001446332,1998957429421938,1999721584333035,1999877567213621,2000883106178990,
  2001816809982805,2001742705303439,1999782392410104,2001915432371714,1996822754489444,
  1997283313266114,1998955236500576,1999609601183327,2000383143227186,1998903799372752,
  2002918262947645,2003647316415807,2002518970609604,1999883749922187,2003041282132145,
  2004834588810278,2004584018867975,2002405549040436,2000447998420888,2002126812012195,
  2001366430971690,1998689725386881]
private def wc_rkmTrajPack_m4_r128_s5_v0_p1 : List ℕ := [1996530378991140,1997614845811819,
  2002374141354460,1992491341877577,1992399836209194,1999465297325658,2013725843387326,
  2022299160424236,2015316915294376,2011371550019189,2049519744565086,2079649325408205,
  2079233399047266,2033679356238686,2055896149741793,2172170811965815,2288305720035609,
  2378070387742106,2424514781995065,2423838060381526,2383933398074559,2319459382618821,
  2246173584227727,2176701886901893,2118645209250665,2074756180296882,2044308211909440,
  2024749751110890,2013047530968016,2006498724203422,2003060681175498,2001363772065107,
  2000575111342086,2000229572758795,2000086745110493,2000031020927437,2000010495727812,
  2000003358279273,2000001015551221,2000000290025946,2000000078149080,2000000019846971,
  2000000004744645,1999999998933834,1999999999775182,2000000000044397,1999999999991810,
  2000000000001404,2000000000000220,2000000000000029,2000000000000002,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m4_r128_s5_v0_p2 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m4_r128_s5_v0 : List ℕ := pCat wc_rkmTrajPack_m4_r128_s5_v0_p0 (pCat
  wc_rkmTrajPack_m4_r128_s5_v0_p1 wc_rkmTrajPack_m4_r128_s5_v0_p2)
private def wc_rkmTrajPack_m4_r128_s5_v1_p0 : List ℕ := [1999645186466989,2000842243924490,
  2001575975481480,2000047633797636,1999223864307324,1999888419822319,1998955261054656,
  1998729881246383,1999573483393796,2000333117857416,1999448067733111,1999736961106658,
  2000389155338721,2000352060380295,2001416336806365,1999991284538199,2001349698873880,
  2000416354207835,2000288318577107,2000125421647407,1998671766109773,2000391862536528,
  1999311639857577,2000618032853982,2000096175045942,2000030885077428,1999046791874264,
  2002012389906966,1999240033416359,1997826893966681,2000779862782270,1998489239355167,
  2000402389545006,1998974413322454,1999876951577434,2001073053934634,2000955578145205,
  1998878050341077,1998900647528065,2000366350046593,2000119818714065,2000305486198852,
  1999787591142455,1998760090035994,1999928195777660,1997734421112543,2002907374751195,
  2000457614540456,2000711991540595,1996607820073526,1998040818527214,1998220140847667,
  1998021527715110,1995933996096936,2004582525134748,1998123750685484,2004114059779122,
  1997641021969572,1997079650590292,2004164309013590,1998090876963471,2002425938898939,
  1998313692770995,2003498490762376]
private def wc_rkmTrajPack_m4_r128_s5_v1_p1 : List ℕ := [2005384421639545,1995845561210437,
  1999510368698044,1998613850828768,1997116001502704,2003797938451212,1995532479356993,
  1993453641089666,2011797591928799,2005818910789609,1983306495471510,1998993830490392,
  2026432805993142,2007944078727415,1977433455387313,1994311699177265,2028852143606023,
  2019286759607459,1980588539497399,1974233399041781,2007895806915417,2028847177878499,
  2004393301808820,1964622390916487,1960249567678216,2002119740501400,2052568642242070,
  2066517669350459,2033329458863904,1983732225727053,1964498857517399,2006305409148914,
  2107019998752053,2236360327816973,2353862628618886,2427545964594411,2444310156633874,
  2409949063396086,2342081592879564,2261212191092627,2183980168403363,2120193424802098,
  2073122943742731,2041546680563587,2022090993634064,2011007692570895,2005144645881394,
  2002256167071336,2000928418330851,2000358347125196,2000129632493457,2000043899089497,
  2000013893337497,2000004100157002,2000001125040509,2000000285930300,2000000066979960,
  2000000014370489,2000000002800737,2000000000490505,2000000000076064,2000000000010224,
  2000000000001150,2000000000000100]
private def wc_rkmTrajPack_m4_r128_s5_v1_p2 : List ℕ := [2000000000000004]
private def wc_rkmTrajPack_m4_r128_s5_v1 : List ℕ := pCat wc_rkmTrajPack_m4_r128_s5_v1_p0 (pCat
  wc_rkmTrajPack_m4_r128_s5_v1_p1 wc_rkmTrajPack_m4_r128_s5_v1_p2)
private def wc_rkmTrajPack_m4_r128_s5_v2_p0 : List ℕ := [1999838058462957,2000247018129053,
  2000195873583300,1999270900494185,1999930116054102,1998636509930542,1999499870963151,
  2001497723878578,1999812422253998,2001533511179281,2000012230814622,2000525140922308,
  2000441805138895,2000748727749749,2000883519986427,1998703404125369,2001099656320602,
  1998044667126740,1999066950346103,2000809282136603,1998921317028418,1998913162851662,
  2000342975741948,1999483341038537,1999150748922031,1999198892201999,2001789304772801,
  1998249627995315,2001544605618427,1998496474054392,2001882411790475,2000908081772671,
  2001830956541642,1998872772468343,2001625029099799,1998125868100477,2003564233211741,
  1997263685052350,1999785587277793,2000893204760599,1997445330897179,2004547189002162,
  1995863239592269,2001187959792761,2002213913457391,1997614081617740,2002215660742256,
  1998273211520481,1999687608793455,1999287443697450,1996836820171518,2002835595873328,
  2000290538717365,1998954546990473,2000873194541778,1996409908034771,2001565507875491,
  2004014230963323,1995676892794308,2000249851736395,2003658224320148,1995240042480645,
  1998468443875680,2002528449350887]
private def wc_rkmTrajPack_m4_r128_s5_v2_p1 : List ℕ := [1997350252666376,2003424664403110,
  2005848548970958,1992066366144895,1995443365082958,2008567074759657,1995230809651867,
  1986003884292266,2007631310073055,2011919249310408,1987354738724491,1990325418623360,
  2015665642927430,2005714578622993,1980392642599754,1996366208602229,2023914947146036,
  2006888160021873,1978164006596785,1993651367859557,2022562145278601,2008637741061439,
  1976694490637872,1984651555483947,2018406387974368,2019140968209423,1985922126050031,
  1975379031271239,2007074557800147,2032843026125229,2012775331899113,1975532474576301,
  1976118907471315,2017711413254002,2046212229735617,2020019661583730,1962906258847232,
  1937795125563426,1976558396312862,2045089687290591,2077037766280460,2037782388674414,
  1957105879731707,1905578270963119,1940581038738864,2067112895047979,2238515426247814,
  2388700805282499,2468771383043581,2465724276233443,2398391213383717,2300197111865447,
  2201870586837649,2122072022220171,2066656124942827,2032919018145681,2014696364967451,
  2005915628375145,2002136420295072,2000686853176612,2000194233851187,2000047422552814,
  2000009694020454,2000001566364920]
private def wc_rkmTrajPack_m4_r128_s5_v2_p2 : List ℕ := [2000000173458737]
private def wc_rkmTrajPack_m4_r128_s5_v2 : List ℕ := pCat wc_rkmTrajPack_m4_r128_s5_v2_p0 (pCat
  wc_rkmTrajPack_m4_r128_s5_v2_p1 wc_rkmTrajPack_m4_r128_s5_v2_p2)
private def wc_rkmTrajPack_m4_r128_s6_hb_p0 : List ℕ := [149358288754368,209951572732554,
  255577237403451,293312995682797,325917874969819,354815442875757,380856345792358,404598028869977,
  426429895607316,446637055892095,465435932550772,482995579241749,499451156098389,514912828983024,
  529471862138099,543204917338875,556177166544801,568444596024149,580055745226231,591053041534822,
  601473840346309,611351246477129,620714770737117,629590860485025,638003332603622,645973730032001,
  653521617775355,660664830528442,667419681267258,673801138093368,679822975056983,685497901499469,
  690837673545331,695853190667713,700554579699520,704951268227237,709052048959139,712865136383400,
  716398216809311,719658492704787,722652722096638,725387253679913,727868058183627,730100756458240,
  732090644682076,733842717026910,735361686075100,736652001240346,737717865409993,738563249997783,
  739191908571177,739607389196168,739813045624209,739812047430121,739607389196168,739201898825553,
  738598245058165,737798944252245,736806366487521,735622741038169,734250161257515,732690588910583,
  730945857985338,729017678008634]
private def wc_rkmTrajPack_m4_r128_s6_hb_p1 : List ℕ := [726907636888440,724617203299707,
  722147728627335,719500448475877,716676483751950,713676841321681,710502414241884,707153981559946,
  703632207673560,699937641237458,696070713600000,692031736747887,687820900732284,683438270544088,
  678883782400000,674157239394147,669258306462295,664186504596801,658941204240415,653521617775355,
  647926791010609,642155593554733,636206707943070,630078617366712,623769591825105,617277672493953,
  610600654064087,603736064763847,596681143725648,589432815294659,581987659801234,574341880225529,
  566491264068111,558431139598652,550156325478446,541661072531557,532938996160708,523982997549774,
  514785171340909,505336696887896,495627709422657,485647146464892,475382563464896,464819910866030,
  453943262315563,442734480358255,431172801189685,419234313270934,406891294784164,394111360388108,
  380856345792358,367080824696991,352730098567973,337737410891975,322019986274165,305473226039254,
  287961890491645,269306104767705,249257910114777,227459148647574,203358512411688,176025558980204,
  143642033174611,101504799246561]
private def wc_rkmTrajPack_m4_r128_s6_hb : List ℕ := pCat wc_rkmTrajPack_m4_r128_s6_hb_p0
  wc_rkmTrajPack_m4_r128_s6_hb_p1
private def wc_rkmTrajPack_m4_r128_s6_v0_p0 : List ℕ := [1999838058462957,2000247018129053,
  1999804126416700,1999270900494185,1999930116054102,1998636509930542,1999499870963151,
  1998502276121422,1999812422253998,1998466488820719,1999987769185378,1999474859077692,
  1999558194861105,1999251272250251,1999116480013573,1998703404125369,1998900343679398,
  1998044667126740,1999066950346103,1999190717863397,1998921317028418,1998913162851662,
  1999657024258052,1999483341038537,1999150748922031,1999198892201999,2001789304772801,
  2001750372004685,2001544605618427,1998496474054392,2001882411790475,2000908081772671,
  2001830956541642,1998872772468343,1998374970900201,1998125868100477,1996435766788259,
  1997263685052350,2000214412722207,2000893204760599,2002554669102821,2004547189002162,
  2004136760407731,2001187959792761,2002213913457391,2002385918382260,2002215660742256,
  2001726788479519,2000312391206545,1999287443697450,1996836820171518,2002835595873328,
  2000290538717365,2001045453009527,1999126805458222,1996409908034771,1998434492124509,
  1995985769036677,1995676892794308,2000249851736395,1996341775679852,1995240042480645,
  1998468443875680,2002528449350887]
private def wc_rkmTrajPack_m4_r128_s6_v0_p1 : List ℕ := [2002649747333624,2003424664403110,
  2005848548970958,2007933633855105,2004556634917042,2008567074759657,2004769190348133,
  2013996115707734,2007631310073055,2011919249310408,2012645261275509,2009674581376640,
  2015665642927430,2005714578622993,2019607357400246,2003633791397771,2023914947146036,
  2006888160021873,2021835993403215,2006348632140443,2022562145278601,2008637741061439,
  2023305509362128,2015348444516053,2018406387974368,2019140968209423,2014077873949969,
  2024620968728761,2007074557800147,2032843026125229,2012775331899113,2024467525423699,
  2023881092528685,2017711413254002,2046212229735617,2020019661583730,2037093741152768,
  2062204874436574,2023441603687138,2045089687290591,2077037766280460,2037782388674414,
  2042894120268293,2094421729036881,2059418961261136,2067112895047979,2238515426247814,
  2388700805282499,2468771383043581,2465724276233443,2398391213383717,2300197111865447,
  2201870586837649,2122072022220171,2066656124942827,2032919018145681,2014696364967451,
  2005915628375145,2002136420295072,2000686853176612,1999805766148813,1999952577447186,
  1999990305979546,2000001566364920]
private def wc_rkmTrajPack_m4_r128_s6_v0_p2 : List ℕ := [2000000173458737]
private def wc_rkmTrajPack_m4_r128_s6_v0 : List ℕ := pCat wc_rkmTrajPack_m4_r128_s6_v0_p0 (pCat
  wc_rkmTrajPack_m4_r128_s6_v0_p1 wc_rkmTrajPack_m4_r128_s6_v0_p2)
private def wc_rkmTrajPack_m4_r128_s6_v1_p0 : List ℕ := [2000943300734817,1998797108666519,
  2000254616312872,1999663294650633,1999966858935050,2000086486162343,2000575950745231,
  1999618583978498,1999962054655584,2000068179574342,2000210155723564,1999459871536624,
  2000535730647203,1998824370297380,2000469890325195,1998506191143447,2000657344331576,
  1998631077521132,1999138394996734,1999302003202930,1998976042179361,1999772012327515,
  1999449026442267,1998580893726017,2000157881281087,1999962116048243,1999933178408061,
  1999053458555094,1998850942334722,1999422900654633,1999741017076093,1999702455260787,
  1995763418173972,1999926626752354,1999372553990905,2000546742284954,1998190873946939,
  1998257063033747,1999762198536277,1997179976548169,1999867341312274,2002007665187802,
  1998285231923480,2001139760518578,1999903313269618,2000194577846683,2001498603332751,
  2001172377353835,2000847377382392,2003756665877822,1998528967624001,2001801306738331,
  1996180538902610,1998322467306320,1992899021766411,2000618453099926,2002604868627055,
  1996793686875458,2005888293243449,1995985752986316,2010144658497235,1994002974850312,
  2013039159985161,1995881236295364]
private def wc_rkmTrajPack_m4_r128_s6_v1_p1 : List ℕ := [2009351132295966,1990485903185685,
  2007033786238369,1996722371155075,2005680688410733,1996345361683393,2003786564032401,
  1998554585524739,1997130151131620,2003251213215291,1991703577797560,2005433175236852,
  1987738822700378,2003074822212467,1988318992044598,2003612238232235,1998392955930060,
  1997488277183084,2011609761181662,1993349386359588,2014523818163990,2000691028735848,
  2004839158821081,2016495861118318,2000252464371674,2022220503431417,2005310454484663,
  2006087636951383,2026359506724544,1998711608233238,2016055045026205,2029871034514290,
  1993387005701282,2019987775232412,2033365340490673,1986893594202713,2039615356858390,
  2024176742208518,1991223996352875,2041264532855312,2024787515138292,1995869057507646,
  2036534719327923,2033237986148208,1996248309001256,2026563795321095,2062805634447442,
  2028009493173582,2001269307202009,2055421849991665,2113253230670491,2075326595266308,
  1979265876494793,1958917650085376,2086273164673165,2302202264931999,2478834594627096,
  2529676572438258,2455395642277751,2316900912932123,2181445229807164,2085390244341725,
  2032183904312210,2009096820442278]
private def wc_rkmTrajPack_m4_r128_s6_v1_p2 : List ℕ := [2001646398230236]
private def wc_rkmTrajPack_m4_r128_s6_v1 : List ℕ := pCat wc_rkmTrajPack_m4_r128_s6_v1_p0 (pCat
  wc_rkmTrajPack_m4_r128_s6_v1_p1 wc_rkmTrajPack_m4_r128_s6_v1_p2)
private def wc_rkmTrajPack_m4_r128_s6_v2_p0 : List ℕ := [2001073592050619,2000552519757851,
  2001220252901997,1999765346697408,2001071046590844,1998497941742761,2000905828215370,
  1999764003901922,1999706761221766,2000032279731114,1999378017358081,1999485479256781,
  2000757826271958,1999637362733132,1999836166946256,2000764160493666,1999376043932310,
  2000781768006495,1998888648475587,2001277902172620,1998844244310096,2000546128356560,
  2000885083276700,1998882472701810,2000226966038421,1999921716371646,1999042770132290,
  2001379011561784,1998566153336863,2000586684798447,1998588038489327,1998596166870078,
  2000517027239716,2001748678127887,1994746107892420,2001512677273330,1997968986582158,
  2001179914334713,1999517507279882,1997855042038557,2002230989373242,1994463286220771,
  2007385899406499,1991166799498842,2009635591582699,1989835623491981,2005684639585696,
  1991243875455076,2007240856173008,1992328895005291,2004638341823752,1996163487082877,
  2000816756655271,1995930633016180,1999457550279300,2001761688007304,1994786366040694,
  2003971557147738,1993685363244769,2009718726855384,1989669812587701,2005874844575863,
  1996492924488437,2003412206438778]
private def wc_rkmTrajPack_m4_r128_s6_v2_p1 : List ℕ := [2002695209262659,2000594074353809,
  2008609232362184,1989643864537319,2005836792976181,1991160734374735,2001492986243711,
  2001690511192917,1989409364652510,2008668314337983,1991344989538351,2007120120730686,
  2004364773261303,1997819250401824,2012216567135791,1991947275715473,2006087799594241,
  2004518941932948,1992471298260340,2012287192371642,1994758181393580,1993346582874586,
  2021595745825425,1976515877445445,2012561782095745,2004955448922154,1973170231542373,
  2019492105090880,1983913212962170,1987823972958325,2021698671339060,1981023962737980,
  2003718412398623,2016654899820140,1983850208680610,2017363963685528,2018821794443626,
  1988611792903126,2021204454902864,2021289660246320,1993491805384477,2023745136353811,
  2026051134500842,1992361650957358,2019913079736072,2040768179325250,1997746431379028,
  2003161584168494,2054245336815571,2027798765608109,1978163420091128,2026568282064072,
  2078819024120222,2011570434951347,1950989887263499,2047189498007813,2164528734055143,
  2086457349845872,1898947438767063,1906612807149215,2202433675363402,2533167775390714,
  2614685712392149,2430284604855679]
private def wc_rkmTrajPack_m4_r128_s6_v2_p2 : List ℕ := [2176000121272365]
private def wc_rkmTrajPack_m4_r128_s6_v2 : List ℕ := pCat wc_rkmTrajPack_m4_r128_s6_v2_p0 (pCat
  wc_rkmTrajPack_m4_r128_s6_v2_p1 wc_rkmTrajPack_m4_r128_s6_v2_p2)
private def wc_rkmTrajPack_m64_r53_s1_hb : List ℕ := [239324368194119,332618149955454,
  400221632792480,453877772299592,498215995455516,535650172337885,567637325350898,595141638684216,
  618843059239174,639244032197466,656729385851368,671602342566401,684107380131378,694445392539681,
  702784111586949,709265489318963,714011062721918,717125938382204,718701808626460,718819272353424,
  717549646506842,714956397523210,711096284429034,706020279638331,699774315694030,692399893567596,
  683934578986143,674412406482050,663864205703654,652317860460765,639798507619288,626328680001221,
  611928394623895,596615184659963,580404070111436,563307457968090,545334956993175,526493084380991,
  506784829981630,486209026309164,464759445246951,442423498353117,419180344316181,394998080241631,
  369829464545340,343605185300287,316222815278857,287527708941369,257277633761782,225071044623933,
  190181703224756,151094043973946,103630491300384]
private def wc_rkmTrajPack_m64_r53_s1_v0 : List ℕ := [2000006444593703,2000040030177132,
  2000171794548179,2000588068332747,2001702591451755,2004304840183395,2009698641170532,
  2019740654838417,2036665006476511,2062612237767292,2098885296478745,2145108809290340,
  2198600795119105,2254290983712771,2305384610877824,2344702707386390,2366339960170285,
  2367111126969107,2347301194109824,2310482676760504,2262503030456727,2210022649204913,
  2159086849947743,2114124273515068,2077549389011869,2049918438514316,2030436731966657,
  2017575558910156,2009608636209783,2004971303901249,2002432735940798,2001125224717475,
  2000491526488051,2000202580509842,2000078686762695,2000028766884268,2000009883708709,
  2000003185928373,2000000961578159,2000000271133129,2000000071235793,2000000017386925,
  2000000003928552,2000000000818349,2000000000156390,2000000000027254,2000000000004297,
  2000000000000605,2000000000000074,2000000000000007,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m64_r53_s1_v1 : List ℕ := [2000000000000001,1999999999999999,
  2000000000000003,2000000000000001,1999999999999998,1999999999999993,2000000000000000,
  2000000000000007,2000000000000001,2000000000000001,2000000000000005,1999999999999957,
  1999999999999925,2000000000000573,2000000000001147,1999999999993157,1999999999984233,
  2000000000068683,2000000000199072,1999999999439697,1999999997752364,2000000003294541,
  2000000022035788,1999999993927194,1999999820429721,1999999839750873,2000001106558671,
  2000002638014193,1999996402436901,1999976875690450,1999982631273019,2000110177980371,
  2000328347455039,2000077734048575,1998317670987943,1995264162680556,1996005889424956,
  2013076680202545,2062910901786662,2154412269532791,2276229099716973,2394635681449989,
  2468016688400363,2469855054415768,2403423877499510,2297630648075495,2188782022339910,
  2102634630069183,2047500246916842,2018495976467191,2005945897317270,2001529004003495,
  2000296528081001,2000037531448842]
private abbrev dP_0 : Prop := atF [ bSlideChk 22 129 wc_rkmTraj_m512_r128_s0_hb
  wc_rkmTraj_m512_r128_s0_v0 wc_rkmTraj_m512_r128_s0_v1, bNLE (bEvalLo12W 8 1024 35
  [1,1,1,1,1,1,1,1] [26980642,15681990,30572585,15806,12899791,6024,12341847,8105670]
  [2,2,3,1,1,1,1,1] rkmMasksPack_m8_r35 []) rkmRowPack_m8_r35] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bSlideChk 22 129 wc_rkmTraj_m512_r128_s0_hb
  wc_rkmTraj_m512_r128_s0_v1 wc_rkmTraj_m512_r128_s0_v2, bNLE (bEvalLo12W 4 2048 9
  [1,2,4,4,4,4,4,4] [102384955,82177345,45305282,40013990,15929604,11180102,4940587,3132777]
  [2,3,3,2,1,1,1,1] rkmMasksPack_m4_r9 []) rkmRowPack_m4_r9] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bSlideChk 22 129 wc_rkmTraj_m512_r128_s0_hb
  wc_rkmTraj_m512_r128_s0_v2 wc_rkmTraj_m512_r128_s0_ck3] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bNLE (bEvalLo12W 64 128 53 [1,1,1,1,1,1,1,1]
  [39049000,45201379,14087020,17783014,13097889,7212839,3410652,6308260] [19,22,7,9,7,4,2,3]
  rkmMasksPack_m64_r53 [none, some (22, 54, wc_rkmTrajPack_m64_r53_s1_hb,
  wc_rkmTrajPack_m64_r53_s1_v0, wc_rkmTrajPack_m64_r53_s1_v1)]) rkmRowPack_m64_r53, bNLE
  (bEvalLo12W 512 16 4 [1] [32533060] [6] rkmMasks_m512_r4 []) rkmRow_m512_r4] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bNLE (bEvalLo12W 4 2048 128 [2,4,8,16,32,59,59,59]
  [17978321,14291865,15692525,17222121,23222578,12410595,10741832,4558460] [3,4,8,15,35,29,25,11]
  rkmMasksPack_m4_r128 [none, none, none, none, some (35, 129, wc_rkmTrajPack_m4_r128_s4_hb,
  wc_rkmTrajPack_m4_r128_s4_v0, wc_rkmTrajPack_m4_r128_s4_v2), some (29, 129,
  wc_rkmTrajPack_m4_r128_s5_hb, wc_rkmTrajPack_m4_r128_s5_v0, wc_rkmTrajPack_m4_r128_s5_v2), some
  (25, 129, wc_rkmTrajPack_m4_r128_s6_hb, wc_rkmTrajPack_m4_r128_s6_v0,
  wc_rkmTrajPack_m4_r128_s6_v2)]) rkmRowPack_m4_r128, bNLE (bEvalLo12W 1024 8 3 [1] [22427643] [5]
  rkmMasks_m1024_r3 []) rkmRow_m1024_r3] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bSlideChk 21 129 wc_rkmTraj_m512_r128_s0_hb
  wc_rkmTraj_m512_r128_s0_ck3 wc_rkmTraj_m512_r128_s0_ck4, bNLE (bEvalLo12W 32 256 10 [1,1,1]
  [125643854,15322183,6022740] [11,3,2] rkmMasks_m32_r10 []) rkmRow_m32_r10] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bSlideChk 21 129 wc_rkmTraj_m512_r128_s0_hb
  wc_rkmTraj_m512_r128_s0_ck4 wc_rkmTraj_m512_r128_s0_ck5, bNLE (bEvalLo12W 2 4096 12
  [1,2,4,8,10,10,10,10] [56553953,51724585,31744002,15545439,51961038,52592143,10411408,3122094]
  [1,2,2,1,4,4,1,1] rkmMasks_m2_r12 []) rkmRow_m2_r12] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bSlideChk 21 129 wc_rkmTraj_m512_r128_s0_hb
  wc_rkmTraj_m512_r128_s0_ck5 wc_rkmTraj_m512_r128_s0_ck6, bNLE (bEvalLo12W 4 2048 10
  [1,2,4,4,4,4,4,4] [96011954,72914238,62136589,40407045,21832135,4027870,3398516,4979856]
  [2,3,4,3,2,1,1,1] rkmMasksPack_m4_r10 []) rkmRowPack_m4_r10] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := atF [ bNLE (bEvalLo12W 32 256 46 [2,2,2,2,2,2,2,2]
  [35821436,29980832,23089546,11960817,11361426,6488910,7158927,5049739] [15,13,10,5,5,3,3,3]
  rkmMasksPack_m32_r46 []) rkmRowPack_m32_r46, bNLE (bEvalLo12W 16 512 11 [1,1,1,1,1,1]
  [110074263,40650992,18431132,31223454,27420674,17517143] [7,3,2,2,2,1] rkmMasksPack_m16_r11 [])
  rkmRowPack_m16_r11] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := atF [ bSlideChk 18 129 wc_rkmTrajPack_m4_r128_s4_hb
  wc_rkmTrajPack_m4_r128_s4_v0 wc_rkmTrajPack_m4_r128_s4_v1, bNLE (bEvalLo12W 256 32 20 [1,1]
  [48392722,1007354] [24,2] rkmMasks_m256_r20 []) rkmRow_m256_r20] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := atF [ bSlideChk 17 129 wc_rkmTrajPack_m4_r128_s4_hb
  wc_rkmTrajPack_m4_r128_s4_v1 wc_rkmTrajPack_m4_r128_s4_v2, bNLE (bEvalLo12W 32 256 20 [1,1,1,1]
  [95044224,38109783,27758478,11210967] [14,7,5,3] rkmMasks_m32_r20 []) rkmRow_m32_r20, bNLE
  (bEvalLo12W 1024 8 10 [1] [23978903] [13] rkmMasks_m1024_r10 []) rkmRow_m1024_r10] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := atF [ bNLE (bEvalLo12W 32 256 44 [1,2,3,3,3]
  [34438708,22425000,52756498,1484552,434815] [9,10,29,1,1] rkmMasks_m32_r44 []) rkmRow_m32_r44,
  bNLE (bEvalLo12W 16 512 23 [1,2,2,2,2] [85330479,71981622,28159490,17014146,9377387]
  [8,11,5,3,2] rkmMasksPack_m16_r23 []) rkmRowPack_m16_r23, bNLE (bEvalLo12W 256 32 8 [1,1]
  [37857422,10000000] [9,3] rkmMasks_m256_r8 []) rkmRow_m256_r8] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := atF [ bNLE (bEvalLo12W 16 512 64 [1,2,4,7,7,7,7,7]
  [32100765,30176264,30701085,20287242,18097153,4610411,1698308,892294] [6,11,18,18,16,4,2,1]
  rkmMasks_m16_r64 [none, none, some (18, 65, wc_rkmTraj_m16_r64_s2_hb, wc_rkmTraj_m16_r64_s2_v0,
  wc_rkmTraj_m16_r64_s2_v1), some (18, 65, wc_rkmTraj_m16_r64_s3_hb, wc_rkmTraj_m16_r64_s3_v0,
  wc_rkmTraj_m16_r64_s3_v1)]) rkmRow_m16_r64, bNLE (bEvalLo12W 128 64 22 [1,1] [70261260,1532380]
  [26,2] rkmMasks_m128_r22 []) rkmRow_m128_r22, bNLE (bEvalLo12W 16 512 14 [1,2,2,2]
  [138842912,33933045,23092176,9054537] [10,4,3,1] rkmMasksPack_m16_r14 []) rkmRowPack_m16_r14] =
  true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := atF [ bSlideChk 15 129 wc_rkmTrajPack_m4_r128_s5_hb
  wc_rkmTrajPack_m4_r128_s5_v0 wc_rkmTrajPack_m4_r128_s5_v1, bNLE (bEvalLo12W 32 256 48
  [1,1,1,1,1,1,1,1] [8936623,20873133,16674005,866043,3949774,431303,7594169,2193190]
  [3,6,5,1,2,1,2,1] rkmMasksPack_m32_r48 []) rkmRowPack_m32_r48, bNLE (bEvalLo12W 512 16 13 [1,1]
  [33544007,694966] [17,1] rkmMasks_m512_r13 []) rkmRow_m512_r13] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := atF [ bNLE (bEvalLo12W 16 512 44 [1,2,4,6,6,6]
  [45638375,27533384,30957242,29654083,6077538,1997846] [7,7,13,16,4,2] rkmMasksPack_m16_r44 [])
  rkmRowPack_m16_r44, bNLE (bEvalLo12W 512 16 23 [1,1,1] [33393723,1199982,114262] [26,2,2]
  rkmMasks_m512_r23 []) rkmRow_m512_r23, bNLE (bEvalLo12W 2 4096 15 [1,3,6,12]
  [42930725,55499707,59522990,72222200] [2,3,5,8] rkmMasks_m2_r15 []) rkmRow_m2_r15] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := atF [ bSlideChk 14 129 wc_rkmTrajPack_m4_r128_s5_hb
  wc_rkmTrajPack_m4_r128_s5_v1 wc_rkmTrajPack_m4_r128_s5_v2, bNLE (bEvalLo12W 16 512 24
  [1,2,2,2,2] [74254705,75427704,33960827,18585047,9352818] [9,13,7,4,3] rkmMasks_m16_r24 [])
  rkmRow_m16_r24, bNLE (bEvalLo12W 16 512 56 [1,1,1,1,1,1,1,1]
  [10465888,24943318,14050507,11859,1020407,1059641,3426055,4081146] [2,4,3,1,1,1,1,1]
  rkmMasksPack_m16_r56 []) rkmRowPack_m16_r56] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := atF [ bSlideChk 13 129 wc_rkmTrajPack_m4_r128_s6_hb
  wc_rkmTrajPack_m4_r128_s6_v0 wc_rkmTrajPack_m4_r128_s6_v1, bNLE (bEvalLo12W 16 512 28
  [1,2,3,3,3] [69617521,32222852,42932993,26219461,7244171] [8,6,10,7,2] rkmMasksPack_m16_r28 [])
  rkmRowPack_m16_r28, bNLE (bEvalLo12W 8 1024 15 [1,2,3,3,3]
  [83979808,51141881,79488350,22913454,7184664] [4,4,8,3,1] rkmMasksPack_m8_r15 [])
  rkmRowPack_m8_r15, bNLE (bEvalLo12W 32 256 5 [1,1,1,1,1]
  [72155490,53312560,796748,7294900,2389248] [4,3,1,1,1] rkmMasksPack_m32_r5 [])
  rkmRowPack_m32_r5] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := atF [ bNLE (bEvalLo12W 2 4096 44 [2,4,8,16,32,41,41,41]
  [27300439,25117587,25599000,25858895,17250000,32698776,4598091,1464626] [2,2,4,7,8,17,3,1]
  rkmMasks_m2_r44 []) rkmRow_m2_r44, bNLE (bEvalLo12W 64 128 26 [1,1,1]
  [100928941,5632231,3658057] [29,3,2] rkmMasks_m64_r26 []) rkmRow_m64_r26, bNLE (bEvalLo12W 2
  4096 18 [1,3,6,12] [37643061,48492854,50126702,86415384] [2,3,5,10] rkmMasks_m2_r18 [])
  rkmRow_m2_r18, bNLE (bEvalLo12W 8 1024 6 [1,1,1,1,1,1,1,1]
  [74949642,54007194,96111277,33645748,38251715,15083670,14767277,11118787] [2,2,3,1,1,1,1,1]
  rkmMasksPack_m8_r6 []) rkmRowPack_m8_r6] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := atF [ bSlideChk 12 129 wc_rkmTrajPack_m4_r128_s6_hb
  wc_rkmTrajPack_m4_r128_s6_v1 wc_rkmTrajPack_m4_r128_s6_v2, bNLE (bEvalLo12W 4 2048 32
  [1,2,4,8,14,14,14,14] [37878134,26887516,32532454,46036883,26170131,24249277,6305214,3066058]
  [2,2,4,9,8,7,2,1] rkmMasksPack_m4_r32 []) rkmRowPack_m4_r32, bNLE (bEvalLo12W 8 1024 14
  [1,2,3,3,3] [79739025,58160709,72704878,21123565,7032986] [5,5,8,3,2] rkmMasks_m8_r14 [])
  rkmRow_m8_r14] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := atF [ bNLE (bEvalLo12W 4 2048 48 [1,2,4,8,16,18,18,18]
  [30662115,22442716,26090374,29220921,8672334,32061707,628900,328736] [2,2,4,8,4,15,1,1]
  rkmMasksPack_m4_r48 []) rkmRowPack_m4_r48, bNLE (bEvalLo12W 256 32 29 [1] [50066278] [34]
  rkmMasks_m256_r29 []) rkmRow_m256_r29, bNLE (bEvalLo12W 4 2048 30 [1,1,4,8,8,8,8,8]
  [48192166,22393159,47030448,819873,4043835,3513818,10417262,16170271] [2,1,6,1,1,1,2,3]
  rkmMasksPack_m4_r30 []) rkmRowPack_m4_r30, bNLE (bEvalLo12W 4 2048 5 [1,2,2,2]
  [165557139,124364642,47341732,19204317] [4,4,2,2] rkmMasks_m4_r5 []) rkmRow_m4_r5] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := atF [ bNLE (bEvalLo12W 128 64 34 [1] [74074495] [39]
  rkmMasks_m128_r34 []) rkmRow_m128_r34, bNLE (bEvalLo12W 128 64 29 [1,1,1]
  [62833237,6637940,3657131] [29,4,3] rkmMasks_m128_r29 []) rkmRow_m128_r29, bNLE (bEvalLo12W 8
  1024 15 [1,2,3,3,3] [56165345,60295304,87086287,19799409,7479293] [4,6,9,3,2] rkmMasks_m8_r15
  []) rkmRow_m8_r15, bNLE (bEvalLo12W 2 4096 10 [1,2,4,8] [52073720,54661845,77370736,76237400]
  [2,3,4,5] rkmMasks_m2_r10 []) rkmRow_m2_r10] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := atF [ bNLE (bEvalLo12W 16 512 31 [1,3,3,3]
  [66151503,90391155,12382273,4427308] [9,25,5,3] rkmMasks_m16_r31 []) rkmRow_m16_r31, bNLE
  (bEvalLo12W 64 128 30 [1,1,1,1,1,1,1,1]
  [32809620,27189090,19635418,11062227,8658424,4696923,5327527,4016647] [10,8,6,4,3,2,2,2]
  rkmMasksPack_m64_r30 []) rkmRowPack_m64_r30, bNLE (bEvalLo12W 16 512 16 [1,2,2,2]
  [116091497,52491799,22971107,8883011] [10,7,4,3] rkmMasks_m16_r16 []) rkmRow_m16_r16, bNLE
  (bEvalLo12W 128 64 5 [1,1,1] [65437084,512237,422961] [7,2,2] rkmMasks_m128_r5 [])
  rkmRow_m128_r5] = true
private theorem bk_21 : dP_21 := by decide +kernel
private abbrev dP_22 : Prop := atF [ bSlideChk 22 54 wc_rkmTrajPack_m64_r53_s1_hb
  wc_rkmTrajPack_m64_r53_s1_v0 wc_rkmTrajPack_m64_r53_s1_v1, bNLE (bEvalLo12W 512 16 128 [1,1,1,1]
  [35200000,1489509,408816,115125] [129,6,2,1] rkmMasks_m512_r128 [some (129, 129,
  wc_rkmTraj_m512_r128_s0_hb, wc_rkmTraj_m512_r128_s0_v0, wc_rkmTraj_m512_r128_s0_ck6)])
  rkmRow_m512_r128, bNLE (bEvalLo12W 64 128 18 [1,1,1] [96786840,4816542,3054960] [20,2,2]
  rkmMasks_m64_r18 []) rkmRow_m64_r18, bNLE (bEvalLo12W 16 512 3 [1,1,1,1]
  [168739447,12356396,2180926,1334011] [4,1,1,1] rkmMasksPack_m16_r3 []) rkmRowPack_m16_r3] = true
private theorem bk_22 : dP_22 := by decide +kernel
private abbrev dP_23 : Prop := atF [ bSlideChk 18 65 wc_rkmTraj_m16_r64_s2_hb
  wc_rkmTraj_m16_r64_s2_v0 wc_rkmTraj_m16_r64_s2_v1, bSlideChk 18 65 wc_rkmTraj_m16_r64_s3_hb
  wc_rkmTraj_m16_r64_s3_v0 wc_rkmTraj_m16_r64_s3_v1, bNLE (bEvalLo12W 64 128 19 [1,1,1,1,1,1,1,1]
  [21137943,26316980,12826269,20210004,10130415,6681822,4858814,3152428] [5,6,3,5,3,2,1,1]
  rkmMasksPack_m64_r19 []) rkmRowPack_m64_r19] = true
private theorem bk_23 : dP_23 := by decide +kernel
private theorem ws_rkmTraj_m512_r128_s0_m1 : WalkOk (some (44, 129, wc_rkmTraj_m512_r128_s0_hb,
    wc_rkmTraj_m512_r128_s0_v0, wc_rkmTraj_m512_r128_s0_v2)) := mIter_split rfl
    (bSlideChk_sound bk_0) (bSlideChk_sound bk_1)
private theorem ws_rkmTraj_m512_r128_s0_m2 : WalkOk (some (66, 129, wc_rkmTraj_m512_r128_s0_hb,
    wc_rkmTraj_m512_r128_s0_v0, wc_rkmTraj_m512_r128_s0_ck3)) := mIter_split rfl
    ws_rkmTraj_m512_r128_s0_m1 (bSlideChk_sound bk_2)
private theorem ws_rkmTraj_m512_r128_s0_m3 : WalkOk (some (87, 129, wc_rkmTraj_m512_r128_s0_hb,
    wc_rkmTraj_m512_r128_s0_v0, wc_rkmTraj_m512_r128_s0_ck4)) := mIter_split rfl
    ws_rkmTraj_m512_r128_s0_m2 (bSlideChk_sound bk_5)
private theorem ws_rkmTraj_m512_r128_s0_m4 : WalkOk (some (108, 129, wc_rkmTraj_m512_r128_s0_hb,
    wc_rkmTraj_m512_r128_s0_v0, wc_rkmTraj_m512_r128_s0_ck5)) := mIter_split rfl
    ws_rkmTraj_m512_r128_s0_m3 (bSlideChk_sound bk_6)
private theorem ws_rkmTraj_m512_r128_s0 : WalkOk (some (129, 129, wc_rkmTraj_m512_r128_s0_hb,
    wc_rkmTraj_m512_r128_s0_v0, wc_rkmTraj_m512_r128_s0_ck6)) := mIter_split rfl
    ws_rkmTraj_m512_r128_s0_m4 (bSlideChk_sound bk_7)
private theorem ws_rkmTrajPack_m4_r128_s4 : WalkOk (some (35, 129, wc_rkmTrajPack_m4_r128_s4_hb,
    wc_rkmTrajPack_m4_r128_s4_v0, wc_rkmTrajPack_m4_r128_s4_v2)) := mIter_split rfl
    (bSlideChk_sound bk_9) (bSlideChk_sound bk_10)
private theorem ws_rkmTrajPack_m4_r128_s5 : WalkOk (some (29, 129, wc_rkmTrajPack_m4_r128_s5_hb,
    wc_rkmTrajPack_m4_r128_s5_v0, wc_rkmTrajPack_m4_r128_s5_v2)) := mIter_split rfl
    (bSlideChk_sound bk_13) (bSlideChk_sound bk_15)
private theorem ws_rkmTrajPack_m4_r128_s6 : WalkOk (some (25, 129, wc_rkmTrajPack_m4_r128_s6_hb,
    wc_rkmTrajPack_m4_r128_s6_v0, wc_rkmTrajPack_m4_r128_s6_v2)) := mIter_split rfl
    (bSlideChk_sound bk_16) (bSlideChk_sound bk_18)
/-- Kernel trajectory certificate `(m = 512, r = 128)`. -/
theorem rkmTraj_m512_r128 : rkmEvalT16Lo12 512 16 128 [1, 1, 1, 1] [35200000, 1489509, 408816,
  115125] [129, 6, 2, 1] rkmMasks_m512_r128 = rkmRow_m512_r128 :=
    bhW_eq (tl1 bk_22) (wCons ws_rkmTraj_m512_r128_s0 wNil)
/-- Kernel trajectory certificate `(m = 16, r = 16)`. -/
theorem rkmTraj_m16_r16 : rkmEvalT16Lo12 16 512 16 [1, 2, 2, 2] [116091497, 52491799, 22971107,
  8883011] [10, 7, 4, 3] rkmMasks_m16_r16 = rkmRow_m16_r16 := bh0_eq (tl2 bk_21)
/-- Kernel trajectory certificate `(m = 1024, r = 3)`. -/
theorem rkmTraj_m1024_r3 : rkmEvalT16Lo12 1024 8 3 [1] [22427643] [5] rkmMasks_m1024_r3 =
  rkmRow_m1024_r3 := bh0_eq (tl1 bk_4)
/-- Kernel trajectory certificate `(m = 16, r = 64)`. -/
theorem rkmTraj_m16_r64 : rkmEvalT16Lo12 16 512 64 [1, 2, 4, 7, 7, 7, 7, 7] [32100765, 30176264,
  30701085, 20287242, 18097153, 4610411, 1698308, 892294] [6, 11, 18, 18, 16, 4, 2, 1]
  rkmMasks_m16_r64 = rkmRow_m16_r64 :=
    bhW_eq bk_12 (wSkip (wSkip (wCons (bSlideChk_sound bk_23) (wCons (bSlideChk_sound (tl1 bk_23))
      wNil))))
/-- Kernel trajectory certificate `(m = 512, r = 4)`. -/
theorem rkmTraj_m512_r4 : rkmEvalT16Lo12 512 16 4 [1] [32533060] [6] rkmMasks_m512_r4 =
  rkmRow_m512_r4 := bh0_eq (tl1 bk_3)
/-- Kernel trajectory certificate `(m = 32, r = 44)`. -/
theorem rkmTraj_m32_r44 : rkmEvalT16Lo12 32 256 44 [1, 2, 3, 3, 3] [34438708, 22425000, 52756498,
  1484552, 434815] [9, 10, 29, 1, 1] rkmMasks_m32_r44 = rkmRow_m32_r44 := bh0_eq bk_11
/-- Kernel trajectory certificate `(m = 128, r = 5)`. -/
theorem rkmTraj_m128_r5 : rkmEvalT16Lo12 128 64 5 [1, 1, 1] [65437084, 512237, 422961] [7, 2, 2]
  rkmMasks_m128_r5 = rkmRow_m128_r5 := bh0_eq (tl1 (tl2 bk_21))
/-- Kernel trajectory certificate `(m = 2, r = 44)`. -/
theorem rkmTraj_m2_r44 : rkmEvalT16Lo12 2 4096 44 [2, 4, 8, 16, 32, 41, 41, 41] [27300439, 25117587,
  25599000, 25858895, 17250000, 32698776, 4598091, 1464626] [2, 2, 4, 7, 8, 17, 3, 1]
  rkmMasks_m2_r44 = rkmRow_m2_r44 := bh0_eq bk_17
/-- Kernel trajectory certificate `(m = 4, r = 5)`. -/
theorem rkmTraj_m4_r5 : rkmEvalT16Lo12 4 2048 5 [1, 2, 2, 2] [165557139, 124364642, 47341732,
  19204317] [4, 4, 2, 2] rkmMasks_m4_r5 = rkmRow_m4_r5 := bh0_eq (tl1 (tl2 bk_19))
/-- Kernel trajectory certificate `(m = 128, r = 34)`. -/
theorem rkmTraj_m128_r34 : rkmEvalT16Lo12 128 64 34 [1] [74074495] [39] rkmMasks_m128_r34 =
  rkmRow_m128_r34 := bh0_eq bk_20
/-- Kernel trajectory certificate `(m = 256, r = 8)`. -/
theorem rkmTraj_m256_r8 : rkmEvalT16Lo12 256 32 8 [1, 1] [37857422, 10000000] [9, 3]
  rkmMasks_m256_r8 = rkmRow_m256_r8 := bh0_eq (tl2 bk_11)
/-- Kernel trajectory certificate `(m = 16, r = 31)`. -/
theorem rkmTraj_m16_r31 : rkmEvalT16Lo12 16 512 31 [1, 3, 3, 3] [66151503, 90391155, 12382273,
  4427308] [9, 25, 5, 3] rkmMasks_m16_r31 = rkmRow_m16_r31 := bh0_eq bk_21
/-- Kernel trajectory certificate `(m = 2, r = 10)`. -/
theorem rkmTraj_m2_r10 : rkmEvalT16Lo12 2 4096 10 [1, 2, 4, 8] [52073720, 54661845, 77370736,
  76237400] [2, 3, 4, 5] rkmMasks_m2_r10 = rkmRow_m2_r10 := bh0_eq (tl1 (tl2 bk_20))
/-- Kernel trajectory certificate `(m = 128, r = 29)`. -/
theorem rkmTraj_m128_r29 : rkmEvalT16Lo12 128 64 29 [1, 1, 1] [62833237, 6637940, 3657131] [29, 4,
  3] rkmMasks_m128_r29 = rkmRow_m128_r29 := bh0_eq (tl1 bk_20)
/-- Kernel trajectory certificate `(m = 1024, r = 10)`. -/
theorem rkmTraj_m1024_r10 : rkmEvalT16Lo12 1024 8 10 [1] [23978903] [13] rkmMasks_m1024_r10 =
  rkmRow_m1024_r10 := bh0_eq (tl2 bk_10)
/-- Kernel trajectory certificate `(m = 256, r = 29)`. -/
theorem rkmTraj_m256_r29 : rkmEvalT16Lo12 256 32 29 [1] [50066278] [34] rkmMasks_m256_r29 =
  rkmRow_m256_r29 := bh0_eq (tl1 bk_19)
/-- Kernel trajectory certificate `(m = 2, r = 12)`. -/
theorem rkmTraj_m2_r12 : rkmEvalT16Lo12 2 4096 12 [1, 2, 4, 8, 10, 10, 10, 10] [56553953, 51724585,
  31744002, 15545439, 51961038, 52592143, 10411408, 3122094] [1, 2, 2, 1, 4, 4, 1, 1]
  rkmMasks_m2_r12 = rkmRow_m2_r12 := bh0_eq (tl1 bk_6)
/-- Kernel trajectory certificate `(m = 64, r = 26)`. -/
theorem rkmTraj_m64_r26 : rkmEvalT16Lo12 64 128 26 [1, 1, 1] [100928941, 5632231, 3658057] [29, 3,
  2] rkmMasks_m64_r26 = rkmRow_m64_r26 := bh0_eq (tl1 bk_17)
/-- Kernel trajectory certificate `(m = 32, r = 10)`. -/
theorem rkmTraj_m32_r10 : rkmEvalT16Lo12 32 256 10 [1, 1, 1] [125643854, 15322183, 6022740] [11, 3,
  2] rkmMasks_m32_r10 = rkmRow_m32_r10 := bh0_eq (tl1 bk_5)
/-- Kernel trajectory certificate `(m = 16, r = 24)`. -/
theorem rkmTraj_m16_r24 : rkmEvalT16Lo12 16 512 24 [1, 2, 2, 2, 2] [74254705, 75427704, 33960827,
  18585047, 9352818] [9, 13, 7, 4, 3] rkmMasks_m16_r24 = rkmRow_m16_r24 := bh0_eq (tl1 bk_15)
/-- Kernel trajectory certificate `(m = 2, r = 15)`. -/
theorem rkmTraj_m2_r15 : rkmEvalT16Lo12 2 4096 15 [1, 3, 6, 12] [42930725, 55499707, 59522990,
  72222200] [2, 3, 5, 8] rkmMasks_m2_r15 = rkmRow_m2_r15 := bh0_eq (tl2 bk_14)
/-- Kernel trajectory certificate `(m = 512, r = 23)`. -/
theorem rkmTraj_m512_r23 : rkmEvalT16Lo12 512 16 23 [1, 1, 1] [33393723, 1199982, 114262] [26, 2, 2]
  rkmMasks_m512_r23 = rkmRow_m512_r23 := bh0_eq (tl1 bk_14)
/-- Kernel trajectory certificate `(m = 512, r = 13)`. -/
theorem rkmTraj_m512_r13 : rkmEvalT16Lo12 512 16 13 [1, 1] [33544007, 694966] [17, 1]
  rkmMasks_m512_r13 = rkmRow_m512_r13 := bh0_eq (tl2 bk_13)
/-- Kernel trajectory certificate `(m = 128, r = 22)`. -/
theorem rkmTraj_m128_r22 : rkmEvalT16Lo12 128 64 22 [1, 1] [70261260, 1532380] [26, 2]
  rkmMasks_m128_r22 = rkmRow_m128_r22 := bh0_eq (tl1 bk_12)
/-- Kernel trajectory certificate `(m = 2, r = 18)`. -/
theorem rkmTraj_m2_r18 : rkmEvalT16Lo12 2 4096 18 [1, 3, 6, 12] [37643061, 48492854, 50126702,
  86415384] [2, 3, 5, 10] rkmMasks_m2_r18 = rkmRow_m2_r18 := bh0_eq (tl2 bk_17)
/-- Kernel trajectory certificate `(m = 32, r = 20)`. -/
theorem rkmTraj_m32_r20 : rkmEvalT16Lo12 32 256 20 [1, 1, 1, 1] [95044224, 38109783, 27758478,
  11210967] [14, 7, 5, 3] rkmMasks_m32_r20 = rkmRow_m32_r20 := bh0_eq (tl1 bk_10)
/-- Kernel trajectory certificate `(m = 8, r = 14)`. -/
theorem rkmTraj_m8_r14 : rkmEvalT16Lo12 8 1024 14 [1, 2, 3, 3, 3] [79739025, 58160709, 72704878,
  21123565, 7032986] [5, 5, 8, 3, 2] rkmMasks_m8_r14 = rkmRow_m8_r14 := bh0_eq (tl2 bk_18)
/-- Kernel trajectory certificate `(m = 256, r = 20)`. -/
theorem rkmTraj_m256_r20 : rkmEvalT16Lo12 256 32 20 [1, 1] [48392722, 1007354] [24, 2]
  rkmMasks_m256_r20 = rkmRow_m256_r20 := bh0_eq (tl1 bk_9)
/-- Kernel trajectory certificate `(m = 8, r = 15)`. -/
theorem rkmTraj_m8_r15 : rkmEvalT16Lo12 8 1024 15 [1, 2, 3, 3, 3] [56165345, 60295304, 87086287,
  19799409, 7479293] [4, 6, 9, 3, 2] rkmMasks_m8_r15 = rkmRow_m8_r15 := bh0_eq (tl2 bk_20)
/-- Kernel trajectory certificate `(m = 64, r = 18)`. -/
theorem rkmTraj_m64_r18 : rkmEvalT16Lo12 64 128 18 [1, 1, 1] [96786840, 4816542, 3054960] [20, 2, 2]
  rkmMasks_m64_r18 = rkmRow_m64_r18 := bh0_eq (tl2 bk_22)
/-- Krotov trajectory `(m = 4, r = 128)`. -/
theorem rkmTrajPack_m4_r128 : rkmEvalT16Lo12 4 2048 128 [2,4,8,16,32,59,59,59]
  [17978321,14291865,15692525,17222121,23222578,12410595,10741832,4558460] [3,4,8,15,35,29,25,11]
  rkmMasksPack_m4_r128 = rkmRowPack_m4_r128 :=
    bhW_eq bk_4 (wSkip (wSkip (wSkip (wSkip (wCons ws_rkmTrajPack_m4_r128_s4 (wCons
      ws_rkmTrajPack_m4_r128_s5 (wCons ws_rkmTrajPack_m4_r128_s6 wNil)))))))
/-- Krotov trajectory `(m = 16, r = 3)`. -/
theorem rkmTrajPack_m16_r3 : rkmEvalT16Lo12 16 512 3 [1,1,1,1] [168739447,12356396,2180926,1334011]
  [4,1,1,1] rkmMasksPack_m16_r3 = rkmRowPack_m16_r3 := bh0_eq (tl1 (tl2 bk_22))
/-- Krotov trajectory `(m = 64, r = 53)`. -/
theorem rkmTrajPack_m64_r53 : rkmEvalT16Lo12 64 128 53 [1,1,1,1,1,1,1,1]
  [39049000,45201379,14087020,17783014,13097889,7212839,3410652,6308260] [19,22,7,9,7,4,2,3]
  rkmMasksPack_m64_r53 = rkmRowPack_m64_r53 :=
    bhW_eq bk_3 (wSkip (wCons (bSlideChk_sound bk_22) wNil))
/-- Krotov trajectory `(m = 32, r = 5)`. -/
theorem rkmTrajPack_m32_r5 : rkmEvalT16Lo12 32 256 5 [1,1,1,1,1]
  [72155490,53312560,796748,7294900,2389248] [4,3,1,1,1] rkmMasksPack_m32_r5 = rkmRowPack_m32_r5
  := bh0_eq (tl1 (tl2 bk_16))
/-- Krotov trajectory `(m = 32, r = 46)`. -/
theorem rkmTrajPack_m32_r46 : rkmEvalT16Lo12 32 256 46 [2,2,2,2,2,2,2,2]
  [35821436,29980832,23089546,11960817,11361426,6488910,7158927,5049739] [15,13,10,5,5,3,3,3]
  rkmMasksPack_m32_r46 = rkmRowPack_m32_r46 := bh0_eq bk_8
/-- Krotov trajectory `(m = 8, r = 6)`. -/
theorem rkmTrajPack_m8_r6 : rkmEvalT16Lo12 8 1024 6 [1,1,1,1,1,1,1,1]
  [74949642,54007194,96111277,33645748,38251715,15083670,14767277,11118787] [2,2,3,1,1,1,1,1]
  rkmMasksPack_m8_r6 = rkmRowPack_m8_r6 := bh0_eq (tl1 (tl2 bk_17))
/-- Krotov trajectory `(m = 16, r = 44)`. -/
theorem rkmTrajPack_m16_r44 : rkmEvalT16Lo12 16 512 44 [1,2,4,6,6,6]
  [45638375,27533384,30957242,29654083,6077538,1997846] [7,7,13,16,4,2] rkmMasksPack_m16_r44 =
  rkmRowPack_m16_r44 := bh0_eq bk_14
/-- Krotov trajectory `(m = 8, r = 35)`. -/
theorem rkmTrajPack_m8_r35 : rkmEvalT16Lo12 8 1024 35 [1,1,1,1,1,1,1,1]
  [26980642,15681990,30572585,15806,12899791,6024,12341847,8105670] [2,2,3,1,1,1,1,1]
  rkmMasksPack_m8_r35 = rkmRowPack_m8_r35 := bh0_eq (tl1 bk_0)
/-- Krotov trajectory `(m = 4, r = 48)`. -/
theorem rkmTrajPack_m4_r48 : rkmEvalT16Lo12 4 2048 48 [1,2,4,8,16,18,18,18]
  [30662115,22442716,26090374,29220921,8672334,32061707,628900,328736] [2,2,4,8,4,15,1,1]
  rkmMasksPack_m4_r48 = rkmRowPack_m4_r48 := bh0_eq bk_19
/-- Krotov trajectory `(m = 4, r = 9)`. -/
theorem rkmTrajPack_m4_r9 : rkmEvalT16Lo12 4 2048 9 [1,2,4,4,4,4,4,4]
  [102384955,82177345,45305282,40013990,15929604,11180102,4940587,3132777] [2,3,3,2,1,1,1,1]
  rkmMasksPack_m4_r9 = rkmRowPack_m4_r9 := bh0_eq (tl1 bk_1)
/-- Krotov trajectory `(m = 64, r = 30)`. -/
theorem rkmTrajPack_m64_r30 : rkmEvalT16Lo12 64 128 30 [1,1,1,1,1,1,1,1]
  [32809620,27189090,19635418,11062227,8658424,4696923,5327527,4016647] [10,8,6,4,3,2,2,2]
  rkmMasksPack_m64_r30 = rkmRowPack_m64_r30 := bh0_eq (tl1 bk_21)
/-- Krotov trajectory `(m = 4, r = 10)`. -/
theorem rkmTrajPack_m4_r10 : rkmEvalT16Lo12 4 2048 10 [1,2,4,4,4,4,4,4]
  [96011954,72914238,62136589,40407045,21832135,4027870,3398516,4979856] [2,3,4,3,2,1,1,1]
  rkmMasksPack_m4_r10 = rkmRowPack_m4_r10 := bh0_eq (tl1 bk_7)
/-- Krotov trajectory `(m = 4, r = 32)`. -/
theorem rkmTrajPack_m4_r32 : rkmEvalT16Lo12 4 2048 32 [1,2,4,8,14,14,14,14]
  [37878134,26887516,32532454,46036883,26170131,24249277,6305214,3066058] [2,2,4,9,8,7,2,1]
  rkmMasksPack_m4_r32 = rkmRowPack_m4_r32 := bh0_eq (tl1 bk_18)
/-- Krotov trajectory `(m = 16, r = 11)`. -/
theorem rkmTrajPack_m16_r11 : rkmEvalT16Lo12 16 512 11 [1,1,1,1,1,1]
  [110074263,40650992,18431132,31223454,27420674,17517143] [7,3,2,2,2,1] rkmMasksPack_m16_r11 =
  rkmRowPack_m16_r11 := bh0_eq (tl1 bk_8)
/-- Krotov trajectory `(m = 16, r = 28)`. -/
theorem rkmTrajPack_m16_r28 : rkmEvalT16Lo12 16 512 28 [1,2,3,3,3]
  [69617521,32222852,42932993,26219461,7244171] [8,6,10,7,2] rkmMasksPack_m16_r28 =
  rkmRowPack_m16_r28 := bh0_eq (tl1 bk_16)
/-- Krotov trajectory `(m = 16, r = 56)`. -/
theorem rkmTrajPack_m16_r56 : rkmEvalT16Lo12 16 512 56 [1,1,1,1,1,1,1,1]
  [10465888,24943318,14050507,11859,1020407,1059641,3426055,4081146] [2,4,3,1,1,1,1,1]
  rkmMasksPack_m16_r56 = rkmRowPack_m16_r56 := bh0_eq (tl2 bk_15)
/-- Krotov trajectory `(m = 32, r = 48)`. -/
theorem rkmTrajPack_m32_r48 : rkmEvalT16Lo12 32 256 48 [1,1,1,1,1,1,1,1]
  [8936623,20873133,16674005,866043,3949774,431303,7594169,2193190] [3,6,5,1,2,1,2,1]
  rkmMasksPack_m32_r48 = rkmRowPack_m32_r48 := bh0_eq (tl1 bk_13)
/-- Krotov trajectory `(m = 16, r = 14)`. -/
theorem rkmTrajPack_m16_r14 : rkmEvalT16Lo12 16 512 14 [1,2,2,2]
  [138842912,33933045,23092176,9054537] [10,4,3,1] rkmMasksPack_m16_r14 = rkmRowPack_m16_r14 :=
    bh0_eq (tl2 bk_12)
/-- Krotov trajectory `(m = 16, r = 23)`. -/
theorem rkmTrajPack_m16_r23 : rkmEvalT16Lo12 16 512 23 [1,2,2,2,2]
  [85330479,71981622,28159490,17014146,9377387] [8,11,5,3,2] rkmMasksPack_m16_r23 =
  rkmRowPack_m16_r23 := bh0_eq (tl1 bk_11)
/-- Krotov trajectory `(m = 8, r = 15)`. -/
theorem rkmTrajPack_m8_r15 : rkmEvalT16Lo12 8 1024 15 [1,2,3,3,3]
  [83979808,51141881,79488350,22913454,7184664] [4,4,8,3,1] rkmMasksPack_m8_r15 = rkmRowPack_m8_r15
  := bh0_eq (tl2 bk_16)
/-- Krotov trajectory `(m = 64, r = 19)`. -/
theorem rkmTrajPack_m64_r19 : rkmEvalT16Lo12 64 128 19 [1,1,1,1,1,1,1,1]
  [21137943,26316980,12826269,20210004,10130415,6681822,4858814,3152428] [5,6,3,5,3,2,1,1]
  rkmMasksPack_m64_r19 = rkmRowPack_m64_r19 := bh0_eq (tl2 bk_23)
/-- Krotov trajectory `(m = 4, r = 30)`. -/
theorem rkmTrajPack_m4_r30 : rkmEvalT16Lo12 4 2048 30 [1,1,4,8,8,8,8,8]
  [48192166,22393159,47030448,819873,4043835,3513818,10417262,16170271] [2,1,6,1,1,1,2,3]
  rkmMasksPack_m4_r30 = rkmRowPack_m4_r30 := bh0_eq (tl2 bk_19)
end
end QuantumComputation.Specs.DickeSol
