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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxTraj01
/-
# Multi-Segment `T_16` Trajectory Part `03` (`FindAllJohnsonRampKickMuxTraj03`)

Certified kernel trajectory evaluations (`30` rows, `38003` substep-coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Prefix-kick masks for `(m = 2, r = 3)`. -/
def rkmMasks_m2_r3 : List (List Bool) := [[], [true, true], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 3)`. -/
def rkmRow_m2_r3 : List ℕ := [101015545, 277085464285, 717485346153]
/-- Prefix-kick masks for `(m = 2, r = 8)`. -/
def rkmMasks_m2_r8 : List (List Bool) := [
  [], [], [true, true, true], [true, true, false, true, true],
  [false, true, false, false, false, true], [false, false, true],
  [false, false, true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 8)`. -/
def rkmRow_m2_r8 : List ℕ := [
  39782767, 33096, 2038809471, 2448317125, 506330227, 5321870570, 490024170043, 499548457510]
/-- Prefix-kick masks for `(m = 2, r = 26)`. -/
def rkmMasks_m2_r26 : List (List Bool) := [[], [], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 26)`. -/
def rkmRow_m2_r26 : List ℕ := [
  12376474, 24526193, 275944632, 428638546, 1046238852, 7666590265, 424627706, 47036026263,
  239146110368, 356287312809, 242712634602, 86348881290, 16733560610, 1741841418, 89488533,
  1740011]
/-- Mask chunk for `(m = 2, r = 52)`. -/
def rkmMkP_m2_r52_s5_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, true, true, false, true, true, false, false, true, true, false, false, false,
  false, true, false, false, true, true, false, false, true, true, true, false, false, false,
  false, false, true, true, true]
/-- Mask chunk for `(m = 2, r = 52)`. -/
def rkmMkP_m2_r52_s6_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, false, true, false, true, false, false, false, true, false, true, true, false,
  true, true, false, false, false, true, false, true, false, false, false, false, false, false,
  false, false, true, true]
/-- Prefix-kick masks for `(m = 2, r = 52)`. -/
def rkmMasks_m2_r52 : List (List Bool) := [
  [], [], [], [], [], rkmMkP_m2_r52_s5_p0, rkmMkP_m2_r52_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 52)`. -/
def rkmRow_m2_r52 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 50, 237, 2, 63, 249, 1017, 13067, 109,
  105532, 82903, 575174, 1071454, 5252790, 50, 781441, 55279709, 8463134, 290353870, 96821568,
  6714252, 393847509, 191697651, 503401040, 7082298259, 868650408, 6342640761, 5725438537,
  4936511460, 45255198607, 6429321250, 16067137073, 191515464012, 401207322803, 260391928194,
  52623623533]
/-- Prefix-kick masks for `(m = 4, r = 3)`. -/
def rkmMasks_m4_r3 : List (List Bool) := [[true], [false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 3)`. -/
def rkmRow_m4_r3 : List ℕ := [960304744, 116910107640, 882124497792]
/-- Mask chunk for `(m = 4, r = 15)`. -/
def rkmMkP_m4_r15_s4_p0 : List Bool := [
  false, true, false, true, false, false, false, false, false, true, false, false, true]
/-- Mask chunk for `(m = 4, r = 15)`. -/
def rkmMkP_m4_r15_s6_p0 : List Bool := [
  false, false, false, false, false, false, false, true, true, true, false, true, false, true]
/-- Prefix-kick masks for `(m = 4, r = 15)`. -/
def rkmMasks_m4_r15 : List (List Bool) := [
  [], [], [false, false, false, false, false, true, true, true],
  [false, true, false, true, false, false, true, false, false, true, true], rkmMkP_m4_r15_s4_p0,
  [true, true, true, false, false, true, false, false, true, true], rkmMkP_m4_r15_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 15)`. -/
def rkmRow_m4_r15 : List ℕ := [
  20017, 1338002, 68993882, 945266346, 11571328, 418297515, 193416117, 641444618, 219729779,
  6321980540, 2985918870, 8796033538, 105142247, 230859691976, 748431111995]
/-- Mask chunk for `(m = 4, r = 16)`. -/
def rkmMkP_m4_r16_s4_p0 : List Bool := [
  true, false, true, false, true, false, true, true, false, true, true, false, true, true]
/-- Mask chunk for `(m = 4, r = 16)`. -/
def rkmMkP_m4_r16_s6_p0 : List Bool := [
  true, true, false, false, false, false, false, true, true, false, true, false, false, false,
  true]
/-- Prefix-kick masks for `(m = 4, r = 16)`. -/
def rkmMasks_m4_r16 : List (List Bool) := [
  [], [], [false, true, true],
  [true, true, true, true, false, false, true, false, true, true, true], rkmMkP_m4_r16_s4_p0,
  [false, true, true], rkmMkP_m4_r16_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 16)`. -/
def rkmRow_m4_r16 : List ℕ := [
  43517, 27899577, 2309872, 19567541, 553353621, 1466123314, 182123906, 1385020, 4019400044,
  42945092, 3407180948, 5839771736, 3614932159, 344818053, 198764538603, 781713079310]
/-- Mask chunk for `(m = 4, r = 32)`. -/
def rkmMkP_m4_r32_s3_p0 : List Bool := [
  false, false, false, true, true, true, true, true, true, false, true, true, true, false, true,
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true]
/-- Mask chunk for `(m = 4, r = 32)`. -/
def rkmMkP_m4_r32_s4_p0 : List Bool := [
  false, true, false, true, false, true, false, false, true, false, false, true, false, false,
  true, true, false, false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 4, r = 32)`. -/
def rkmMkP_m4_r32_s5_p0 : List Bool := [
  false, true, false, true, false, false, false, false, false, false, true, false, true, false,
  true, false, true, true, false, true, false, false, true, false, false, true, false, false,
  true, true]
/-- Prefix-kick masks for `(m = 4, r = 32)`. -/
def rkmMasks_m4_r32 : List (List Bool) := [
  [], [], [], rkmMkP_m4_r32_s3_p0, rkmMkP_m4_r32_s4_p0, rkmMkP_m4_r32_s5_p0, [true, true, true],
  []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 32)`. -/
def rkmRow_m4_r32 : List ℕ := [
  1157, 13339, 243826830, 39846576, 42328001, 113705608, 101013771, 6544927, 5886246, 100815068,
  6240588, 724, 45865318, 436463525, 12705754, 1578878951, 1175096744, 289071448, 31965139,
  21716390, 1487573872, 534496642, 926338897, 610094029, 5021711494, 511851249, 1535921371,
  15984159236, 8001110513, 2786538833, 214267720512, 744080209798]
/-- Prefix-kick masks for `(m = 8, r = 11)`. -/
def rkmMasks_m8_r11 : List (List Bool) := [
  [], [true, false, false, true, true, true],
  [false, true, true, false, true, false, false, true, true],
  [false, true, true, false, true, true, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 11)`. -/
def rkmRow_m8_r11 : List ℕ := [
  2747004, 12923092, 130270803, 330113341, 675429664, 582085108, 151937034, 5086412641, 405530589,
  82031013002, 910591526367]
/-- Mask chunk for `(m = 8, r = 20)`. -/
def rkmMkP_m8_r20_s2_p0 : List Bool := [
  false, true, false, false, false, false, true, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 8, r = 20)`. -/
def rkmMkP_m8_r20_s3_p0 : List Bool := [
  false, false, true, true, false, true, false, true, true, false, true, false, false, true,
  false, false, true, true]
/-- Prefix-kick masks for `(m = 8, r = 20)`. -/
def rkmMasks_m8_r20 : List (List Bool) := [
  [], [true, false, true, false, true, true], rkmMkP_m8_r20_s2_p0, rkmMkP_m8_r20_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 20)`. -/
def rkmRow_m8_r20 : List ℕ := [
  45689, 180454, 5817519, 2054132, 1493302, 3545212, 791883, 236881275, 235994816, 223918249,
  1373561447, 1319739, 938378533, 1163313630, 71980807, 1757288202, 16102892336, 13241993416,
  93150967891, 871487397592]
/-- Mask chunk for `(m = 8, r = 64)`. -/
def rkmMkP_m8_r64_s3_p0 : List Bool := [
  true, false, false, false, true, true, true, true, true, true, false, true, true, false, true,
  true, false, true, true, true, true, true, false, true, true, true, true, true, true, false,
  false, false, true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, true, true,
  false, false, true]
/-- Mask chunk for `(m = 8, r = 64)`. -/
def rkmMkP_m8_r64_s4_p0 : List Bool := [
  false, false, false, false, false, true, true, false, true, true, false, false, true, false,
  true, false, true, true, false, true, true, false, true, true, false, false, true, false, false,
  true, true, false, false, true, true, false, false, false, true, false, true, true, true, true,
  false, false, false, true, true, true, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false]
/-- Mask chunk for `(m = 8, r = 64)`. -/
def rkmMkP_m8_r64_s4_p1 : List Bool := [true]
/-- Mask chunk for `(m = 8, r = 64)`. -/
def rkmMkP_m8_r64_s5_p0 : List Bool := [
  true, false, true, true, false, false, false, true, true, false, false, false, false, true,
  false, false, true, true, false, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, false, false, false, false, false, false, true, true, false,
  true, true, false, true, true, false, true, true, false, true, true, false, false, true, true,
  false, false, true, true]
/-- Mask chunk for `(m = 8, r = 64)`. -/
def rkmMkP_m8_r64_s6_p0 : List Bool := [
  true, true, true, false, false, false, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true]
/-- Prefix-kick masks for `(m = 8, r = 64)`. -/
def rkmMasks_m8_r64 : List (List Bool) := [
  [], [], [true, true, true, false, true, true, true, true], rkmMkP_m8_r64_s3_p0,
  rkmMkP_m8_r64_s4_p0 ++ rkmMkP_m8_r64_s4_p1, rkmMkP_m8_r64_s5_p0, rkmMkP_m8_r64_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 64)`. -/
def rkmRow_m8_r64 : List ℕ := [
  18589, 1085269, 254012, 4972, 907701, 120431, 5318051, 330454, 20390793, 781462, 11113031,
  3582407, 5237037, 57456, 1408130, 18114898, 2683725, 6656, 1835885, 3386190, 4694926, 3256321,
  48246, 46015459, 98471474, 204864387, 173911215, 30617405, 175219937, 240677894, 177047406,
  43452009, 223655060, 4908260, 116631725, 349047703, 3400792, 606408321, 269640878, 50270465,
  101590664, 121940393, 1312968208, 38583670, 74002906, 744903290, 64858266, 446552018,
  1176724606, 98909580, 561928569, 393260110, 1249057921, 1319620324, 908349580, 1197393380,
  1205984875, 3600444042, 621993, 18527382075, 18688505314, 10847490804, 111724140403,
  822695902513]
/-- Prefix-kick masks for `(m = 16, r = 8)`. -/
def rkmMasks_m16_r8 : List (List Bool) := [
  [], [true], [true, false, true, true], [false, true, true, false, true, true],
  [true, true, false, true, true, true], [false, true, false, true, true, true, true],
  [false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 8)`. -/
def rkmRow_m16_r8 : List ℕ := [
  839469, 262348, 3124608, 153497271, 55439164, 265243900, 35508111036, 964013475510]
/-- Prefix-kick masks for `(m = 16, r = 10)`. -/
def rkmMasks_m16_r10 : List (List Bool) := [
  [true, true, true], [false, true, true, true, false, false, true, true],
  [false, true, false, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 10)`. -/
def rkmRow_m16_r10 : List ℕ := [
  16749, 1994431, 2453585, 35573477, 174619272, 81426339, 1630372143, 413896159, 36262666513,
  961396696601]
/-- Mask chunk for `(m = 16, r = 35)`. -/
def rkmMkP_m16_r35_s1_p0 : List Bool := [
  false, false, false, false, true, true, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true]
/-- Mask chunk for `(m = 16, r = 35)`. -/
def rkmMkP_m16_r35_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, true, true, true, true, false, false, true,
  true, true, true, true, false, false, true, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 16, r = 35)`. -/
def rkmMkP_m16_r35_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, true, false, true, false, true, false, false,
  true, false, true, false, true, false, false, true, false, true, false, true, false, false,
  true, false, false, true, true]
/-- Mask chunk for `(m = 16, r = 35)`. -/
def rkmMkP_m16_r35_s4_p0 : List Bool := [
  false, false, false, false, false, false, true, false, true, true, false, true, false, false,
  false, true, false, false, true, false, false, false, true, false, false, false, false, false,
  true, true, false, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 35)`. -/
def rkmMasks_m16_r35 : List (List Bool) := [
  [], rkmMkP_m16_r35_s1_p0, rkmMkP_m16_r35_s2_p0, rkmMkP_m16_r35_s3_p0, rkmMkP_m16_r35_s4_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 35)`. -/
def rkmRow_m16_r35 : List ℕ := [
  6178, 558, 14398, 3973, 714, 14712, 9844, 34936, 26394, 203265, 25081, 3509395, 1604087, 906321,
  44909, 9706460, 5651922, 4964975, 3423215, 1376803, 254309099, 34557225, 483688806, 1129837741,
  1118113885, 1328157659, 228018923, 2670012, 1245544192, 2929265851, 68624881, 14313297435,
  2705081, 49228924580, 927600755743]
/-- Prefix-kick masks for `(m = 32, r = 12)`. -/
def rkmMasks_m32_r12 : List (List Bool) := [
  [false, true, false, false, true, false, false, false, true, true],
  [false, true, false, true, false, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 12)`. -/
def rkmRow_m32_r12 : List ℕ := [
  2, 174, 2250, 59323, 394808, 6382489, 31974402, 118974431, 217326757, 197164140, 19696256625,
  979731464502]
/-- Mask chunk for `(m = 32, r = 17)`. -/
def rkmMkP_m32_r17_s0_p0 : List Bool := [
  false, false, true, true, false, true, true, false, false, true, true, false, true, true]
/-- Mask chunk for `(m = 32, r = 17)`. -/
def rkmMkP_m32_r17_s1_p0 : List Bool := [
  true, false, true, false, true, false, true, true, false, true, false, true, true, false, true,
  true]
/-- Prefix-kick masks for `(m = 32, r = 17)`. -/
def rkmMasks_m32_r17 : List (List Bool) := [rkmMkP_m32_r17_s0_p0, rkmMkP_m32_r17_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 17)`. -/
def rkmRow_m32_r17 : List ℕ := [
  0, 8, 9, 4521, 5493, 465775, 12948, 1270, 4728099, 174034912, 7578623, 249326, 1368079216,
  2174810608, 94493745, 18247741508, 977927793767]
/-- Mask chunk for `(m = 64, r = 15)`. -/
def rkmMkP_m64_r15_s0_p0 : List Bool := [
  false, false, false, false, true, true, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 64, r = 15)`. -/
def rkmMkP_m64_r15_s1_p0 : List Bool := [
  false, false, false, false, false, true, false, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 64, r = 15)`. -/
def rkmMasks_m64_r15 : List (List Bool) := [rkmMkP_m64_r15_s0_p0, rkmMkP_m64_r15_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 15)`. -/
def rkmRow_m64_r15 : List ℕ := [
  0, 0, 0, 0, 9, 3, 998, 9945, 616739, 2529448, 76355242, 9708280, 93239149, 12727053101,
  987090486918]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s1_p0 : List Bool := [
  false, false, true, false, false, true, true, false, false, false, false, true, true, false,
  false, false, true, true, false, false, true, false, true, true, false, false, true, false,
  false, true, true, false, true, false, false, true, true, false, false, true, true, false,
  false, false, true, false, true, true, true, true, false, true, false, false, true, false, true,
  true, true, false, false, false, false, false]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s1_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, true]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s2_p0 : List Bool := [
  true, false, true, true, false, true, false, true, true, true, false, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, false, false, true,
  false, true, false, true, true, false, false, true, true, false, false, false, false, true,
  true, false, true, false, true, false, true, false, true, true, true, false, false, false,
  false, false, false, false, false, false, true]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s2_p1 : List Bool := [
  true, true, true, false, true, true, false, true, true, false, false, true, false, false, true,
  true, false, true, false, false, true, true, true, true, true, false, false, true, true, true,
  true, false, true, true, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, true,
  false, false, false, false, true, true]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s2_p2 : List Bool := [true]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s3_p0 : List Bool := [
  false, false, true, false, false, true, false, true, false, false, false, false, false, false,
  false, false, true, false, true, false, true, false, true, false, false, true, true, false,
  true, true, false, true, false, false, true, false, true, false, true, false, true, false, true,
  false, true, false, false, true, false, true, true, false, false, false, false, false, false,
  false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s3_p1 : List Bool := [
  false, false, false, true, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, false, true, true, false, false, true, true, false, true, true,
  false, false, true, true, true, false, false, true, false, true, true, true, false, false, true,
  true, true]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, true, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  false, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s4_p1 : List Bool := [
  false, false, false, false, false, true, false, false, false, true, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, false, true, false, true, false, true, true, false, true, false, true,
  true, false, true, true, false, false, true]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s5_p0 : List Bool := [
  false, true, false, false, true, true, false, false, false, true, false, false, true, false,
  false, false, false, false, true, false, true, false, false, false, false, true, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s5_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, true, true, true,
  false, false, false, true, false, true, false, false, false, true]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s6_p0 : List Bool := [
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 64, r = 128)`. -/
def rkmMkP_m64_r128_s6_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true]
/-- Prefix-kick masks for `(m = 64, r = 128)`. -/
def rkmMasks_m64_r128 : List (List Bool) := [
  rkmMkP_m64_r128_s0_p0, rkmMkP_m64_r128_s1_p0 ++ rkmMkP_m64_r128_s1_p1,
  rkmMkP_m64_r128_s2_p0 ++ rkmMkP_m64_r128_s2_p1 ++ rkmMkP_m64_r128_s2_p2,
  rkmMkP_m64_r128_s3_p0 ++ rkmMkP_m64_r128_s3_p1, rkmMkP_m64_r128_s4_p0 ++ rkmMkP_m64_r128_s4_p1,
  rkmMkP_m64_r128_s5_p0 ++ rkmMkP_m64_r128_s5_p1, rkmMkP_m64_r128_s6_p0 ++ rkmMkP_m64_r128_s6_p1,
  []]
/-- Row chunk `0` `(m = 64, r = 128)`. -/
def rkmRowP_m64_r128_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 26, 108, 464, 1899,
  7093, 23073, 64844, 157339, 329277, 602175, 986849, 1463123, 2000527, 2513660, 2824761, 2722841,
  2133728, 1260363, 454500, 29872, 114233, 642781, 1230103, 1346398, 842697, 187183, 38034,
  679080, 1475711, 1333691, 374491, 41262, 973862, 1915697, 1170527, 30857, 745653, 2334491,
  1975601, 190953]
/-- Row chunk `1` `(m = 64, r = 128)`. -/
def rkmRowP_m64_r128_p1 : List ℕ := [
  576907, 2287361, 1842852, 99592, 801349, 2199590, 702076, 896568, 7143827, 8736733, 2594449,
  7371, 1095585, 701651, 65509, 1059315, 49968, 3726301, 11712736, 8895267, 2725115, 925022,
  3421470, 9826422, 10130950, 4325079, 2827065, 8298624, 17117336, 15215791, 10285751, 13121541,
  15669180, 6130695, 168230, 1407073, 15553065, 41188764, 20186467, 465619, 14544, 3604393,
  20266240, 532492, 45358345, 4235949, 37595980, 10515045, 365915293, 118302017, 3009580,
  167499294, 209831947, 496141537, 1483775303, 451630564, 3553013797, 1605318562, 383630686,
  2118178890, 8873801571, 614982540, 15749977608, 963393448993]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 128)`. -/
def rkmRow_m64_r128 : List ℕ := rkmRowP_m64_r128_p0 ++ rkmRowP_m64_r128_p1
/-- Prefix-kick masks for `(m = 128, r = 3)`. -/
def rkmMasks_m128_r3 : List (List Bool) := [[true, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 3)`. -/
def rkmRow_m128_r3 : List ℕ := [638177636, 53938163254, 945422697018]
/-- Mask chunk for `(m = 128, r = 21)`. -/
def rkmMkP_m128_r21_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 21)`. -/
def rkmMasks_m128_r21 : List (List Bool) := [rkmMkP_m128_r21_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 21)`. -/
def rkmRow_m128_r21 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 592, 10817, 108037, 2140922, 11669884, 220053644, 36028451,
  8624427712, 991105559596]
/-- Mask chunk for `(m = 128, r = 23)`. -/
def rkmMkP_m128_r23_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, true, false,
  false, true, true, false, true, true]
/-- Mask chunk for `(m = 128, r = 23)`. -/
def rkmMkP_m128_r23_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, true, false, true, true, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 23)`. -/
def rkmMasks_m128_r23 : List (List Bool) := [rkmMkP_m128_r23_s0_p0, rkmMkP_m128_r23_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 23)`. -/
def rkmRow_m128_r23 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 95366, 174533, 31592, 35161355, 159523856,
  25538658, 8049350567, 991730123648]
/-- Prefix-kick masks for `(m = 256, r = 6)`. -/
def rkmMasks_m256_r6 : List (List Bool) := [[], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 6)`. -/
def rkmRow_m256_r6 : List ℕ := [0, 4997, 141488, 93049000, 26335044840, 973571759607]
/-- Mask chunk for `(m = 256, r = 22)`. -/
def rkmMkP_m256_r22_s0_p0 : List Bool := [
  false, true, true, true, false, false, true, true, true, false, false, true, false, false,
  false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 256, r = 22)`. -/
def rkmMasks_m256_r22 : List (List Bool) := [rkmMkP_m256_r22_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 22)`. -/
def rkmRow_m256_r22 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 0, 24718, 1078022, 76727986, 510542911,
  7599404169, 991812221673]
/-- Prefix-kick masks for `(m = 512, r = 5)`. -/
def rkmMasks_m512_r5 : List (List Bool) := [[], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 5)`. -/
def rkmRow_m512_r5 : List ℕ := [274, 800402, 293609525, 31439730072, 968265859641]
/-- Mask chunk for `(m = 512, r = 17)`. -/
def rkmMkP_m512_r17_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 512, r = 17)`. -/
def rkmMkP_m512_r17_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  true, true]
/-- Prefix-kick masks for `(m = 512, r = 17)`. -/
def rkmMasks_m512_r17 : List (List Bool) := [rkmMkP_m512_r17_s0_p0, rkmMkP_m512_r17_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 17)`. -/
def rkmRow_m512_r17 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 385, 7890, 107, 2078117, 833224, 9279993079, 990717086706]
/-- Prefix-kick masks for `(m = 512, r = 27)`. -/
def rkmMasks_m512_r27 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 27)`. -/
def rkmRow_m512_r27 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 2261, 62872, 4314781, 212566241,
  5975577632, 993807475246]
/-- Mask chunk for `(m = 512, r = 30)`. -/
def rkmMkP_m512_r30_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, true, true, true]
/-- Mask chunk for `(m = 512, r = 30)`. -/
def rkmMkP_m512_r30_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  true, true]
/-- Mask chunk for `(m = 512, r = 30)`. -/
def rkmMkP_m512_r30_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, true, false, false, true,
  false, true]
/-- Prefix-kick masks for `(m = 512, r = 30)`. -/
def rkmMasks_m512_r30 : List (List Bool) := [
  rkmMkP_m512_r30_s0_p0, rkmMkP_m512_r30_s1_p0, rkmMkP_m512_r30_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 30)`. -/
def rkmRow_m512_r30 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 893, 114861, 22324,
  12724466, 2691042, 5347246705, 994637198409]
/-- Prefix-kick masks for `(m = 1024, r = 26)`. -/
def rkmMasks_m1024_r26 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 26)`. -/
def rkmRow_m1024_r26 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 89, 294, 870582, 22188673,
  6011294043, 993965645115]
/-- Prefix-kick masks for `(m = 1024, r = 29)`. -/
def rkmMasks_m1024_r29 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 29)`. -/
def rkmRow_m1024_r29 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 150, 1515, 1055244,
  38332186, 5402066670, 994558542755]
/-- Mask chunk for `(m = 1024, r = 32)`. -/
def rkmMkP_m1024_r32_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, false, false, false, true]
/-- Mask chunk for `(m = 1024, r = 32)`. -/
def rkmMkP_m1024_r32_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, true, false, false, true,
  true, true]
/-- Mask chunk for `(m = 1024, r = 32)`. -/
def rkmMkP_m1024_r32_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, true,
  true, false, true, true]
/-- Mask chunk for `(m = 1024, r = 32)`. -/
def rkmMkP_m1024_r32_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true, true,
  true, false, false, true]
/-- Mask chunk for `(m = 1024, r = 32)`. -/
def rkmMkP_m1024_r32_s5_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, false, true, true]
/-- Mask chunk for `(m = 1024, r = 32)`. -/
def rkmMkP_m1024_r32_s6_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, true, true]
/-- Prefix-kick masks for `(m = 1024, r = 32)`. -/
def rkmMasks_m1024_r32 : List (List Bool) := [
  [], rkmMkP_m1024_r32_s1_p0, rkmMkP_m1024_r32_s2_p0, rkmMkP_m1024_r32_s3_p0,
  rkmMkP_m1024_r32_s4_p0, rkmMkP_m1024_r32_s5_p0, rkmMkP_m1024_r32_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 32)`. -/
def rkmRow_m1024_r32 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 89, 106, 42058,
  1960840, 144406, 4899466394, 995098384125]
/-- Unpacks `j` LSB-first bits of `< 2 ^ 50` word `w` (`FindAllJohnsonRampKickMuxTraj03`). -/
def rkmWbTraj03 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWbTraj03 j (Nat.div w 2)
/-- Concatenates `50`-bit `< 2 ^ 50` chunks (final length `rem`) into a `List Bool` mask. -/
def rkmMaskWordsTraj03 : ℕ → List ℕ → List Bool
  | _, [] => []
  | rem, [w] => rkmWbTraj03 rem w
  | rem, w :: v :: ws => rkmWbTraj03 50 w ++ rkmMaskWordsTraj03 rem (v :: ws)
/-- Krotov masks `(m = 16, r = 128)`. -/
def rkmMasksPack_m16_r128 : List (List Bool) := [[], rkmWbTraj03 3 6,
  rkmMaskWordsTraj03 7 [33030265, 112],
  rkmMaskWordsTraj03 5 [993058703932029, 844528009381739, 20],
  rkmMaskWordsTraj03 28 [23597197683026, 124857262640345, 260046878],
  rkmMaskWordsTraj03 25 [313984657988624, 375298897301855, 26843446],
  rkmMaskWordsTraj03 27 [25883961212933, 281549132091712, 67125248], []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 128)`. -/
def rkmRowPack_m16_r128 : List ℕ := [359137, 316391, 224959, 500661, 2249003, 172108, 28698, 80278,
  1081623, 106994, 1360201, 51774, 704, 2425394, 8648230, 11004674, 73041, 117485, 730151, 379028,
  371516, 787281, 201103, 124750, 4339951, 2471870, 5128396, 5586617, 440015, 2519138, 853057,
  6460874, 444719, 113664, 1068294, 59595, 740161, 404815, 1701639, 2078024, 29787, 400805,
  5136294, 1121260, 55748, 3382219, 7805, 20821233, 472772, 1850718, 3927, 1071312, 215210, 441689,
  81024, 192630, 396463, 1316044, 9473847, 8569596, 11013741, 15927426, 85961, 365252, 10311766,
  156054, 525852, 14308050, 211992, 780155, 1852504, 15741752, 12726053, 808113, 15934296,
  77193922, 969134, 101861754, 799069, 133428098, 20066421, 26916043, 3562809, 3292302, 1376410,
  855462, 6107150, 8090, 2962795, 117108553, 196808820, 185391910, 20070938, 837165362, 9887830,
  1085955357, 79822465, 3434292, 1968477108, 13775885, 28097590, 163775107, 28995009, 486325517,
  17719759, 324246314, 743426633, 4678209, 1373964866, 19342069, 2361499516, 862114, 2616284652,
  1034991, 2872017343, 78735427, 1516037222, 1419028510, 526663254, 3621559021, 194400172,
  10265642735, 646744242, 9365511557, 20948610009, 20299081, 41291237414, 893944310455]
/-- Krotov masks `(m = 32, r = 3)`. -/
def rkmMasksPack_m32_r3 : List (List Bool) := [[], rkmWbTraj03 1 1, rkmWbTraj03 4 14, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 3)`. -/
def rkmRowPack_m32_r3 : List ℕ := [39699766, 56965914325, 942994352156]
/-- Krotov masks `(m = 8, r = 64)`. -/
def rkmMasksPack_m8_r64 : List (List Bool) := [[], [], rkmWbTraj03 4 9,
  rkmMaskWordsTraj03 11 [4798175359, 1736], rkmMaskWordsTraj03 1 [987818400306334, 1],
  rkmMaskWordsTraj03 11 [956258751735146, 1638], rkmMaskWordsTraj03 12 [1098840441881969, 2048],
  []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 64)`. -/
def rkmRowPack_m8_r64 : List ℕ := [87829, 15730, 297284, 197115, 6411, 476077, 876064, 1872, 51624,
  461234, 2188602, 6316235, 201755, 197887, 1730026, 10686604, 954764, 645464, 12775867, 36159960,
  584006, 825, 1882887, 1727798, 1627295, 13514302, 1049766, 13096396, 21583976, 842526, 62629377,
  19107, 25185, 14716318, 67151475, 7105507, 858525, 38858288, 38695860, 167877408, 13754986,
  33071383, 571622908, 2357277661, 23869815, 781252388, 101264849, 73196480, 21497317, 2366100082,
  1788670503, 271488150, 436311916, 452241706, 1452703982, 221216296, 1361431640, 3686112470,
  389418423, 12258808406, 19804231947, 9949915786, 89620230263, 851435936770]
/-- Krotov masks `(m = 16, r = 5)`. -/
def rkmMasksPack_m16_r5 : List (List Bool) := [[], [], [], rkmWbTraj03 1 1, rkmWbTraj03 3 6, [],
  rkmWbTraj03 4 8, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 5)`. -/
def rkmRowPack_m16_r5 : List ℕ := [20678158, 10023795, 157712632, 42329503662, 957481891056]
/-- Krotov masks `(m = 16, r = 52)`. -/
def rkmMasksPack_m16_r52 : List (List Bool) := [[], rkmWbTraj03 29 268435471,
  rkmWbTraj03 25 31472694, rkmWbTraj03 50 1013320012899025,
  rkmMaskWordsTraj03 1 [46916709335744, 1], []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 52)`. -/
def rkmRowPack_m16_r52 : List ℕ := [2109, 26074, 185535, 822097, 47556, 3293, 14675, 85, 15429,
  3582, 255707, 1485072, 11664, 1124, 4516, 604168, 14335, 1060301, 312292, 97849, 2528289, 343493,
  380813, 840367, 1508369, 70367, 632060, 1290676, 255730, 1988746, 63355, 1685306, 2631048,
  4703973, 5549639, 1369032, 5835961, 47397806, 20543728, 246039143, 99322450, 1310225613,
  608393382, 5948999426, 2309116520, 16063297036, 2393192064, 18750939, 29573901880, 1099,
  40389857786, 900934309116]
/-- Krotov masks `(m = 2, r = 10)`. -/
def rkmMasksPack_m2_r10 : List (List Bool) := [[], [], [], []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 10)`. -/
def rkmRowPack_m2_r10 : List ℕ := [15339036, 35571974, 1914364891, 1242173, 22835006598,
  9676269435, 105691619300, 468511001223, 336299740634, 55017986817]
/-- Krotov masks `(m = 64, r = 38)`. -/
def rkmMasksPack_m64_r38 : List (List Bool) := [[], rkmWbTraj03 6 51, rkmWbTraj03 26 59663129,
  rkmWbTraj03 32 3864746576, rkmWbTraj03 35 27024643492, rkmWbTraj03 36 34972411458,
  rkmWbTraj03 37 69948594896, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 38)`. -/
def rkmRowPack_m64_r38 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 56, 0, 0, 102, 1055,
  171, 0, 26980, 86432, 263047, 408029, 1904394, 169951, 1182814, 517, 44572139, 3980285, 29318646,
  114812708, 46115299, 105164700, 847028563, 105787369, 9579235433, 989119940489]
/-- Krotov masks `(m = 32, r = 8)`. -/
def rkmMasksPack_m32_r8 : List (List Bool) := [[], [], [], rkmWbTraj03 3 7, rkmWbTraj03 5 25,
  rkmWbTraj03 6 34, rkmWbTraj03 7 68, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 8)`. -/
def rkmRowPack_m32_r8 : List ℕ := [10331, 34541, 964405, 1451791, 959821, 128571295, 24908056405,
  974959951314]
/-- Krotov masks `(m = 64, r = 33)`. -/
def rkmMasksPack_m64_r33 : List (List Bool) := [rkmWbTraj03 29 456338624,
  rkmWbTraj03 32 3679802516, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 33)`. -/
def rkmRowPack_m64_r33 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 31, 130, 440, 870,
  2417, 173, 75096, 2199, 5535962, 63668729, 4846126, 5809706, 1035375981, 59145157, 176055309,
  3391683695, 98498468, 9218084304, 985941214517]
/-- Krotov masks `(m = 64, r = 10)`. -/
def rkmMasksPack_m64_r10 : List (List Bool) := [rkmWbTraj03 8 228, rkmWbTraj03 9 298, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 10)`. -/
def rkmRowPack_m64_r10 : List ℕ := [0, 7, 214, 26337, 279943, 7976489, 2853026, 49969888,
  17959555101, 981979338883]
/-- Krotov masks `(m = 8, r = 96)`. -/
def rkmMasksPack_m8_r96 : List (List Bool) := [rkmWbTraj03 7 127, [], [], [], rkmWbTraj03 13 4096,
  rkmWbTraj03 29 268517392, rkmWbTraj03 17 65881, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 96)`. -/
def rkmRowPack_m8_r96 : List ℕ := [971850, 46861599, 665204862, 326422, 3212647985, 3393288,
  3430417764, 1052015647, 1940235988, 2192497368, 1110891952, 7245834677, 81076928952,
  104382117404, 661552969504, 120813046490, 6499296906, 2308125032, 1704417162, 608600981,
  127657302, 21038958, 3539541, 697429, 152469, 32488, 6182, 1014, 142, 16, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Krotov masks `(m = 16, r = 26)`. -/
def rkmMasksPack_m16_r26 : List (List Bool) := [rkmWbTraj03 16 49151, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 26)`. -/
def rkmRowPack_m16_r26 : List ℕ := [3061128, 67074927, 780483973, 5467618036, 24680280671,
  74759335408, 155789928285, 226472168308, 231057081988, 164860147064, 81823303076, 27227027831,
  6157669816, 804500745, 49238368, 1025355]
/-- Krotov masks `(m = 64, r = 27)`. -/
def rkmMasksPack_m64_r27 : List (List Bool) := [rkmWbTraj03 26 60817407, rkmWbTraj03 27 134217724,
  rkmWbTraj03 15 19298, rkmWbTraj03 20 947213, rkmWbTraj03 24 13476591, rkmWbTraj03 25 19619923,
  rkmWbTraj03 26 34266976, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 27)`. -/
def rkmRowPack_m64_r27 : List ℕ := [0, 0, 44, 11, 104, 131, 477, 3, 964, 1999, 2705, 118, 4, 1029,
  68, 44831, 160193, 6895471, 1156, 10241795, 15244689, 197524, 90047598, 148975638, 156468591,
  9565483552, 990006230838]
/-- Krotov masks `(m = 16, r = 12)`. -/
def rkmMasksPack_m16_r12 : List (List Bool) := [rkmWbTraj03 9 486, rkmWbTraj03 10 730,
  rkmWbTraj03 11 1066, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 12)`. -/
def rkmRowPack_m16_r12 : List ℕ := [3489, 265868, 66024, 1210581, 316791, 500248953, 265866001,
  128350611, 799932238, 996777907, 42839641697, 954467319615]
/-- Krotov masks `(m = 4, r = 28)`. -/
def rkmMasksPack_m4_r28 : List (List Bool) := [[], [], [], rkmWbTraj03 10 897,
  rkmWbTraj03 26 53674951, rkmWbTraj03 22 2801091, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 28)`. -/
def rkmRowPack_m4_r28 : List ℕ := [24878521, 482078, 390932, 7120074, 9809839, 14157979, 581887,
  3098148, 16227449, 9177770, 4673444, 9623110, 272484, 52526516, 30430748, 227857580, 8698594,
  1025856389, 382944, 3936646755, 26754007, 10164492394, 478036997, 1764911457, 36879353843,
  308874852, 183061903875, 761932408499]
/-- Krotov masks `(m = 8, r = 13)`. -/
def rkmMasksPack_m8_r13 : List (List Bool) := [[], rkmWbTraj03 7 78, rkmWbTraj03 10 789,
  rkmWbTraj03 12 3557, rkmWbTraj03 12 2203, rkmWbTraj03 3 4, rkmWbTraj03 12 2049, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 13)`. -/
def rkmRowPack_m8_r13 : List ℕ := [561, 1008, 16379169, 27985485, 346639126, 578845628, 83804445,
  165749060, 7796420497, 8155321320, 172668, 76405478929, 906423184714]
/-- Krotov masks `(m = 2, r = 28)`. -/
def rkmMasksPack_m2_r28 : List (List Bool) := [[], [], rkmWbTraj03 2 2, rkmWbTraj03 28 150997501,
  rkmWbTraj03 22 3800281, rkmWbTraj03 20 696566, []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 28)`. -/
def rkmRowPack_m2_r28 : List ℕ := [96233513, 28678496, 89034115, 205771242, 45663678, 24593207,
  32948556, 258013651, 10824190, 831468, 7441068, 50017989, 16879565, 2962566, 768619120,
  133256026, 817006202, 229042630, 3023539802, 1009147259, 3736451062, 20528880978, 5389850,
  464130499, 144265816367, 445759344942, 317604201459, 60759047994]
/-- Krotov masks `(m = 8, r = 29)`. -/
def rkmMasksPack_m8_r29 : List (List Bool) := [[], []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 29)`. -/
def rkmRowPack_m8_r29 : List ℕ := [35063682, 180388, 24362408, 9887509, 10688135, 13505035,
  4055899, 1304837, 8712294, 389956504, 2601525370, 1278542, 33495642403, 175748715493,
  311112622025, 277649025802, 143273225135, 45364307467, 9014491102, 1121644708, 85144097, 3720675,
  83121, 704]
/-- Krotov masks `(m = 64, r = 20)`. -/
def rkmMasksPack_m64_r20 : List (List Bool) := [rkmWbTraj03 20 524288, [], [], rkmWbTraj03 12 3585,
  rkmWbTraj03 16 55899, rkmWbTraj03 18 221862, rkmWbTraj03 19 285430, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 20)`. -/
def rkmRowPack_m64_r20 : List ℕ := [0, 0, 0, 0, 0, 10, 85, 163, 10960, 17399, 3998, 11765, 4192166,
  2111799, 209325, 56643906, 85276992, 123445251, 10918519425, 988809556508]
/-- Krotov masks `(m = 8, r = 16)`. -/
def rkmMasksPack_m8_r16 : List (List Bool) := [[], [], [], rkmWbTraj03 3 4, rkmWbTraj03 10 922,
  rkmWbTraj03 14 12874, rkmWbTraj03 15 16709, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 16)`. -/
def rkmRowPack_m8_r16 : List ℕ := [699242, 3734614, 18394, 128200663, 160480818, 30001122,
  1284698087, 171040482, 97438915, 2437202913, 3645648, 761757094, 12284137978, 119010722,
  84357308302, 898160533616]
/-- Krotov masks `(m = 32, r = 18)`. -/
def rkmMasksPack_m32_r18 : List (List Bool) := [rkmWbTraj03 17 131071, [], rkmWbTraj03 5 31,
  rkmWbTraj03 9 458, rkmWbTraj03 13 6283, rkmWbTraj03 16 52053, rkmWbTraj03 17 74808, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 18)`. -/
def rkmRowPack_m32_r18 : List ℕ := [3, 132, 13, 13954, 273817, 1361423, 382857, 577621, 4053800,
  11606843, 1574658, 176565970, 6921402, 83925693, 1485159341, 167458828, 18378456509,
  979681666942]
/-- Krotov masks `(m = 8, r = 18)`. -/
def rkmMasksPack_m8_r18 : List (List Bool) := [[], rkmWbTraj03 16 52382, rkmWbTraj03 17 70933, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 18)`. -/
def rkmRowPack_m8_r18 : List ℕ := [17490, 110117, 1778324, 6113557, 13099294, 2738655, 5154,
  13931592, 90727285, 547784294, 589270927, 2980257276, 545202093, 1532496042, 25321817469,
  57003895, 99781068160, 868516570809]
/-- Cumulative `2`-lane trajectory head invariant (`Traj01` -> `Traj03`). -/
def rkmTrajLaneProp_03 : Prop :=
  (rkmRow_m2_r19.head? = some 333836326141) ∧ (rkmRow_m2_r3.head? = some 101015545)
/-- Proof of `rkmTrajLaneProp_03` in `O(1)` kernel steps. -/
theorem rkmTrajLaneOk_03 : rkmTrajLaneProp_03 :=
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
private def wc_rkmTraj_m64_r128_s1_hb_p0 : List ℕ := [154189527040000,216353350625893,
  262891218346603,301151420000000,334003943133732,362932318642777,388824620975454,412263864972174,
  433658044800000,453306418109936,471436557185129,488226548357977,503819035330799,518330500183012,
  531857622062102,544481767360000,556272243056206,567288706759232,577582986852860,587200480670594,
  596181244806765,604560856845395,612371104690388,619640544024254,626394953600000,632657710455984,
  638450101698893,643791585549522,648700011441032,653191806796501,657282136483929,660985039707453,
  664313548141011,667279788372054,669895071145166,672169969440000,674114387056133,675737619088164,
  677048405441340,678054978349317,678765104701840,679186123864106,679324981565750,679188260351457,
  678782207013714,678112757368481,677185558684420,676005990034122,674579180800000,672910027537227,
  671003209370222,668863202077095,666494290997512,663900582883129,661086016795650,658054374145389,
  654809287952645,651354251404958,647692625775326,643827647759386,639762436283441,635499998829756,
  631043237320818,626394953600000]
private def wc_rkmTraj_m64_r128_s1_hb_p1 : List ℕ := [621557854542364,616534556826044,
  611327591391680,605939407614796,600372377213679,594628797913219,588710896883339,582620833968941,
  576360704726843,569932543283788,563338325028435,556579969149120,549659341028214,542578254502992,
  535338474002132,527941716566222,520389653760000,512683913483432,504826081688197,496817704005637,
  488660287291771,480355301094568,471904179048279,463308320199275,454569090267528,445687822847584,
  436665820552576,427504356104611,418204673374623,408767988374571,399195490204657,389488341958102,
  379647681585788,369674622722983,359570255480183,349335647200000,338971843181881,328479867376353,
  317860723050368,307115393425235,296244842288526,285250014581279,274131836961708,262891218346603,
  251529050431492,240046208190604,228443550357595,216721919887957,204882144403974,192925036623020,
  180851394770008,168662002974668,156357631654385,143939037883222,131406965747749,118762146690272,
  106005299840000,93137132332680,80158339619208,67069605763666,53871603731247,40564995666496,
  27150433162261,13628557519741]
private def wc_rkmTraj_m64_r128_s1_hb : List ℕ := pCat wc_rkmTraj_m64_r128_s1_hb_p0
  wc_rkmTraj_m64_r128_s1_hb_p1
private def wc_rkmTraj_m64_r128_s1_v0_p0 : List ℕ := [2000131204662139,2000620352186296,
  2002046897398586,2005441586011569,2012360454412091,2024772323374971,2044700675027809,
  2073640829776953,2111887225792396,2157993536506889,2208597930198526,2258755438650648,
  2302755092932263,2335225940619689,2352226376781346,2352011362190291,2335279759277431,
  2304872245266561,2265051980387490,2220599096502049,2175962154116661,2134647182802952,
  2098923951564582,2069830647238485,2047391567762984,2030938299279013,2019436835737726,
  2011755691201055,2006846877268998,2003841115659650,2002075932455140,2001080944651883,
  2000542306895310,2000262137584358,2000122073442772,2000054759575384,2000023656948888,
  2000009840173797,2000003939576031,2000001517492117,2000000562120728,2000000200134053,
  2000000068442498,2000000022466173,2000000007072464,2000000002133246,1999999999384157,
  1999999999830050,1999999999955231,2000000000011236,2000000000002679,2000000000000603,
  2000000000000126,2000000000000023,2000000000000003,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m64_r128_s1_v0_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m64_r128_s1_v0 : List ℕ := pCat wc_rkmTraj_m64_r128_s1_v0_p0
  wc_rkmTraj_m64_r128_s1_v0_p1
private def wc_rkmTraj_m64_r128_s1_v1_p0 : List ℕ := [2000000000001031,2000000000010564,
  2000000000075572,2000000000435133,2000000002137947,2000000009257273,2000000036052315,
  2000000128071975,2000000419287900,2000001275014728,2000003623653449,2000009673290969,
  2000024354764258,2000058032536297,2000131252386189,2000282476141489,2000579750853855,
  2001136877449183,2002133671962349,2003838219937305,2006626689060907,2010993707251526,
  2017544340028098,2026958430253355,2039920570886655,2057014926970093,2078593077404524,
  2104633467968831,2134619994647451,2167471517162117,2201550779994722,2234769453723132,
  2264787234174056,2289281286342486,2306243537215829,2314252915007811,2312671268927597,
  2301725662500603,2282462675787448,2256586402028030,2226214284439802,2193598377630241,
  2160861482758630,2129788665426330,2101698417263639,2077399077446060,2057219799262351,
  2041094552716495,2028673577748214,2019438629860876,2012804313501585,2008195379129141,
  2005096989730289,2003080314760320,2001808892176267,2001032193459679,2000572308123325,
  2000308321408823,2000161384713726,2000082069545396,2000040544771857,2000019457567648,
  2000009069905259,2000004106033716]
private def wc_rkmTraj_m64_r128_s1_v1_p1 : List ℕ := [2000001804963454,2000000770237543,
  2000000318953609,2000000128102132,2000000049868995,2000000018802398,2000000006859951,
  2000000002419584,2000000000824229,2000000000270906,2000000000085831,2000000000026192,
  2000000000007688,2000000000002168,2000000000000585,2000000000000149,2000000000000035,
  2000000000000007,2000000000000001,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m64_r128_s1_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m64_r128_s1_v1 : List ℕ := pCat wc_rkmTraj_m64_r128_s1_v1_p0 (pCat
  wc_rkmTraj_m64_r128_s1_v1_p1 wc_rkmTraj_m64_r128_s1_v1_p2)
private def wc_rkmTraj_m64_r128_s1_v2_p0 : List ℕ := [1999999999999629,2000000000002022,
  1999999999992641,2000000000020796,1999999999951962,2000000000092722,1999999999849754,
  2000000000202166,1999999999782329,2000000000168396,1999999999946873,1999999999915623,
  2000000000167850,1999999999862422,2000000000007310,2000000000125868,1999999999851218,
  2000000000035958,2000000000109778,1999999999857143,2000000000024937,2000000000119801,
  1999999999876497,2000000000001996,2000000000226938,2000000000313532,2000000001572413,
  2000000006406905,2000000022172811,2000000073405683,2000000229444381,2000000675657416,
  2000001884818702,2000004994412857,2000012594062339,2000030277814276,2000069514642290,
  2000152627195781,2000320873847683,2000646653314327,2001250492602491,2002322508757696,
  2004146267804863,2007120421030551,2011770580923298,2018741473024721,2028758728650268,
  2042552136142533,2060738671956664,2083674002222920,2111293597717445,2142975778996165,
  2177464677472283,2212887532061026,2246886334864817,2276860348694435,2300288724914462,
  2315078934042944,2319874511371035,2314259504500328,2298817082539925,2275031063293024,
  2245053099494053,2211385645304026]
private def wc_rkmTraj_m64_r128_s1_v2_p1 : List ℕ := [2176544603673309,2142763160876123,
  2111782056476404,2084747370632568,2062212131768612,2044218881375898,2030430279704215,
  2020274210337372,2013076411646847,2008163927362871,2004933183082796,2002884807067946,
  2001632314141391,2000893544261514,2000473122271438,2000242262805813,2000119938359628,
  2000057395758059,2000026542000697,2000011857415038,2000005115716935,2000002130721173,
  2000000856403246,2000000332026250,2000000124108439,2000000044703088,2000000015507173,
  2000000005177450,2000000001662622,2000000000513152,2000000000152098,2000000000043253,
  2000000000011787,2000000000003072,2000000000000761,2000000000000177,2000000000000037,
  2000000000000005,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m64_r128_s1_v2_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m64_r128_s1_v2 : List ℕ := pCat wc_rkmTraj_m64_r128_s1_v2_p0 (pCat
  wc_rkmTraj_m64_r128_s1_v2_p1 wc_rkmTraj_m64_r128_s1_v2_p2)
private def wc_rkmTraj_m64_r128_s1_ck3_p0 : List ℕ := [1999999999706406,2000000000062761,
  2000000000195837,1999999999910400,1999999999847574,2000000000111521,2000000000116604,
  1999999999871269,1999999999918312,2000000000140381,2000000000046330,1999999999854422,
  1999999999989126,2000000000143719,1999999999976457,1999999999865359,2000000000055450,
  2000000000118685,1999999999916720,1999999999903290,2000000000105660,2000000000070020,
  1999999999878491,1999999999959778,2000000000130245,2000000000009117,1999999999868251,
  2000000000021531,2000000000126447,1999999999949905,1999999999884836,2000000000075311,
  2000000000099078,1999999999903773,1999999999920465,2000000000112416,2000000000057968,
  1999999999876224,1999999999964311,2000000000130713,2000000000013906,1999999999866118,
  2000000000006248,2000000000134313,1999999999978991,1999999999877216,2000000000039845,
  2000000000043959,1999999999624738,1999999999362890,2000000000819147,2000000007496873,
  2000000023679783,2000000037821427,1999999968819335,1999999568472527,1999998376967746,
  1999996161378502,1999995025080516,2000005690205762,2000062160229989,2000250298660335,
  2000755266929231,2001928225309273]
private def wc_rkmTraj_m64_r128_s1_ck3_p1 : List ℕ := [2004362771164926,2008957082590909,
  2016923204373769,2029698616608551,2048726473238169,2075104901787297,2109158097787635,
  2150036203496621,2195482566369822,2241893463451274,2284728963962200,2319229255077851,
  2341283933985078,2348234913162466,2339397010616715,2316157121824540,2281636243404044,
  2240023152928200,2195770246374188,2152856611592730,2114274334523960,2081807509180061,
  2056084459477591,2036820938211898,2023148466700385,2013933862292753,2008029058113240,
  2004427907438850,2002336389954892,2001179102512180,2000568902295689,2000262299264290,
  2000115503407061,2000048547411851,2000019463209125,2000007437200215,2000002706351288,
  2000000936983446,2000000308320865,2000000096316346,2000000028528161,2000000008000494,
  2000000002121077,2000000000530693,2000000000125062,2000000000027693,2000000000005743,
  2000000000001108,2000000000000195,2000000000000029,2000000000000003,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m64_r128_s1_ck3_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m64_r128_s1_ck3 : List ℕ := pCat wc_rkmTraj_m64_r128_s1_ck3_p0 (pCat
  wc_rkmTraj_m64_r128_s1_ck3_p1 wc_rkmTraj_m64_r128_s1_ck3_p2)
private def wc_rkmTraj_m64_r128_s3_hb_p0 : List ℕ := [134350288425444,188886354217477,
  229972758131092,263972629399840,293365980701260,319432188762769,342935603110641,364377026822193,
  384106232253851,402379264967737,419390448614023,435291545114359,450203865496302,464226267268106,
  477440629234001,489915714410716,501709966639093,512873580614543,523450063981677,533477436307130,
  542989163285338,552014894478025,560581052965010,568711311785112,576426982718756,583747336404020,
  590689868089568,597270519927619,603503868210728,609403282096094,614981058961053,620248540468355,
  625216212601688,629893792297713,634290302804971,638414139509292,642273127655059,645874573143577,
  649225307390168,652331727059865,655199829369826,657835243538685,660243258874084,662428849916103,
  664396698993013,666151216494651,667696559125744,669036646365270,670175175327316,671115634192802,
  671861314359162,672415321436054,672780585198705,672959868596345,672955775900882,672770760070225,
  672407129391301,671867053459547,671152568544345,670265582383382,669207878443098,667981119677133,
  666586851809919,665026506168175]
private def wc_rkmTraj_m64_r128_s3_hb_p1 : List ℕ := [663301402079024,661412748849627,
  659361647339623,657149091134208,654775967322268,652243056880656,649551034662296,646700468982380,
  643691820793343,640525442435526,637201575946475,633720350907477,630081781801229,626285764849345,
  622332074292623,618220358070496,613950132848751,609520778336253,604931530821812,600181475851327,
  595269539952543,590194481299881,584954879194420,579549122213634,573975394861356,568231662519820,
  562315654471464,556224844717367,549956430269991,543507306538506,536874039352676,530052833083056,
  523039494206699,515829389533443,508417398140958,500797855857671,492964490869081,484910348687928,
  476627704299550,468107958739387,459341516636859,450317640308317,441024274715884,431447835905363,
  421572953215469,411382152345668,400855461879165,389969919462947,378698944578671,367011531139360,
  354871192452165,342234559050080,329049478909042,315252385831512,300764559195991,285486645067188,
  269290336173153,252005172676403,233396433699557,213125443891583,190671421089560,165156314673000,
  134865904719685,95370371774990]
private def wc_rkmTraj_m64_r128_s3_hb : List ℕ := pCat wc_rkmTraj_m64_r128_s3_hb_p0
  wc_rkmTraj_m64_r128_s3_hb_p1
private def wc_rkmTraj_m64_r128_s3_v0_p0 : List ℕ := [2000000000080132,1999999999880590,
  1999999999970276,2000000000036691,2000000000051975,2000000000154379,1999999999843852,
  2000000000056831,2000000000046149,2000000000230403,2000000000065967,2000000000421396,
  2000000000777123,2000000002183040,2000000004984013,2000000011747649,2000000025071743,
  2000000050725204,2000000096291548,2000000171671759,2000000286274982,2000000445387132,
  2000000641814518,2000000850332617,2000001020259674,2000001082343131,2000000966375634,
  1999999362951253,1999999866929654,2000000407521248,2000000774384180,2000000771118614,
  2000000350876500,2000000290423976,2000000756530984,1999999311497817,1999999927927141,
  1999999363676422,1999999198813591,2000000194638852,2000000650566793,1999999161654730,
  1999999925984773,1999999169301958,1999999253258436,2000000326733370,2000001024262311,
  2000000308982672,1999999089823615,1999999182678989,2000000572885078,2000001118014396,
  2000000181551315,1999998754842904,1999999847021783,1999998708514391,2000000409717817,
  2000001281267997,1999999524533239,1999998550768199,2000000674876513,2000001221216677,
  2000000026360667,2000002229654660]
private def wc_rkmTraj_m64_r128_s3_v0_p1 : List ℕ := [1999999054702735,1999999548404233,
  1999997867338137,1999996430974460,1999999025379514,2000001044003237,2000003604666463,
  2000001073238168,2000002033516658,1999999852187392,1999999197961084,1999995717588699,
  1999999451371962,1999998257597281,2000001076393733,2000002782514993,2000003769116985,
  1999996840812908,1999999115854796,1999998110993498,2000006558622680,1999998064382182,
  1999979969027229,1999982641890992,2000023878197746,1999896333692201,1999857699818947,
  1999966092275565,1999489019565797,1998966442244780,1999138404186871,1998997736960685,
  2004932750025748,2009378423125378,2009954006924500,2000192166072740,2028304981530286,
  2078700741749107,2149664835878634,2232325889519519,2312418451684709,2374423561744186,
  2406415801469982,2403602478497139,2369191769256991,2312528422977049,2245618000663533,
  2179596619973833,2122346648035651,2077706423641598,2046021675009336,2025405022372299,
  2013056787662068,2006235340355367,2002758823996052,2001126423777805,1999577754878234,
  1999855618473535,2000044671835571,2000012377786036,2000003029290984,2000000642020021,
  1999999885784735,1999999983895034]
private def wc_rkmTraj_m64_r128_s3_v0_p2 : List ℕ := [1999999998438145]
private def wc_rkmTraj_m64_r128_s3_v0 : List ℕ := pCat wc_rkmTraj_m64_r128_s3_v0_p0 (pCat
  wc_rkmTraj_m64_r128_s3_v0_p1 wc_rkmTraj_m64_r128_s3_v0_p2)
private def wc_rkmTraj_m64_r128_s3_v1_p0 : List ℕ := [1999999999856044,2000000000218771,
  1999999999995840,2000000000076458,2000000000305527,1999999998632618,2000000004807967,
  1999999986143958,2000000034841005,1999999924804120,2000000137163839,1999999792183501,
  2000000248525280,1999999788856813,2000000086374972,2000000042832120,1999999977931849,
  1999999778689356,2000000516371439,1999999462540866,2000000191283256,2000000156343116,
  1999999913445021,1999999729287204,2000000433385362,1999999672796896,2000000197046927,
  2000000103716398,1999999415592467,2000000381484765,2000000602060862,1999999253145870,
  1999999874410022,2000000071219605,2000000595231513,1999999682624212,2000000458520040,
  1999999482590594,1999999426684714,2000000735778334,2000000613446740,2000001549631268,
  2000000413419995,2000001073792686,2000000076501718,2000001292919986,1999999365892103,
  1999999875223699,2000001988772778,1999998258539249,2000001374087250,2000001097898026,
  2000001549135001,1999999255441134,2000000653334667,1999998113239066,2000000883051692,
  1999999937117984,2000001573916471,1999998198909675,1999999703331908,1999998194057277,
  2000001906981250,1999998864688713]
private def wc_rkmTraj_m64_r128_s3_v1_p1 : List ℕ := [2000002019821690,1999995282275705,
  2000003574825541,1999997023011654,2000004862278952,1999992552232214,2000012218073795,
  1999981977694655,2000028029931099,1999945311654652,2000111490315611,1999783032928858,
  2000391290432181,1999358742091001,2000937857627937,1998755340242893,2001517540252732,
  1998266974616115,2001919640936077,1997959077871661,2001939370721430,1998632061117585,
  2000175600264390,2001315225142138,1997716731777139,2001827064287642,2000191059554270,
  1997616210568780,2002490268523474,2000267746647772,1996796775317825,2002174196884893,
  2002406792600587,1996155413692709,1998608845289218,2004944420546907,2001113058136597,
  1994104011380000,1997659646760210,2006422714200106,2005765908012712,1995480962552605,
  1989288060006965,1996686630854892,2010742473717104,2016118114383931,2001362632544092,
  1974649769948292,1959241633517981,1986311027937510,2071060681729277,2201283731695899,
  2340609095703739,2442562277771021,2476696276933364,2440232700508779,2353248578575844,
  2247962062670177,2153028091449585,2082793543379415,2038583342125016,2014998324911561,
  2004655476299992,2001083329960484]
private def wc_rkmTraj_m64_r128_s3_v1_p2 : List ℕ := [2000164679176618]
private def wc_rkmTraj_m64_r128_s3_v1 : List ℕ := pCat wc_rkmTraj_m64_r128_s3_v1_p0 (pCat
  wc_rkmTraj_m64_r128_s3_v1_p1 wc_rkmTraj_m64_r128_s3_v1_p2)
private def wc_rkmTraj_m64_r128_s3_v2_p0 : List ℕ := [2000000066003763,1999999824502851,
  2000000274244482,1999999722147661,2000000194881540,1999999830590904,2000000296477126,
  1999999579559255,2000000292828888,2000000008748632,1999999916882209,1999999821390099,
  2000000308936764,2000000011310346,1999999718532059,1999999895379289,2000000749593897,
  1999999259263531,2000000090963999,2000000334002430,1999999767567766,2000000144036092,
  1999999594294905,2000000775924695,1999999129189443,2000000435082503,2000000260150537,
  1999999565742014,2000000168924680,1999999356863573,2000001769965670,1999998066518247,
  2000001076753312,1999999376509297,2000000520814087,1999999682058428,2000000914958184,
  1999998028556401,2000001887721485,1999998888280835,2000000774283278,1999999009232149,
  2000002343187227,1999996157343947,2000003543738827,1999996197341286,2000006764450528,
  1999989909285193,2000014500738898,1999976768530600,2000037806034585,1999936871978315,
  2000104509997369,1999833138480774,2000260583737881,1999607467056288,2000565958728006,
  1999216919619867,2001030509098505,1998715305206660,2001514817921008,1998319456354055,
  2001750361149710,1998309392419832]
private def wc_rkmTraj_m64_r128_s3_v2_p1 : List ℕ := [2001490914237740,1998868519843795,
  2000619849339322,2000006455787134,1999335470616388,2001211699173411,1998557849895820,
  2001191489509332,1999564362666928,1999404006601819,2001445890676433,1998391680669124,
  2000864454278562,2000475718030507,1998377179876373,2001745925134979,1999392326886024,
  1998911136971255,2002044290947768,1998649225357018,1999395769409877,2002171339469267,
  1998233156047667,1999532880343096,2002395988334832,1998173961974905,1999058696757289,
  2002892569485323,1998518056396898,1998101826748487,2002917458311044,2000201462625488,
  1996472588130031,2002091444597168,2002562224922639,1996602464084339,1998523904158347,
  2004339729708465,2000362343745769,1994856475752172,2000823578798252,2005521582936047,
  1998854023471260,1993578209945576,2000638300038406,2008195243620542,2000798457829337,
  1989761226373398,1995299405359567,2011874088982467,2013098267842079,1989238063594876,
  1972479885358022,1999284956499603,2046156890148100,2040266882096026,1953017055043011,
  1869026957467989,1925946189849692,2161763997877025,2446645427085367,2593533740031886,
  2524548882163974,2319495650122769]
private def wc_rkmTraj_m64_r128_s3_v2_p2 : List ℕ := [2120869262177745]
private def wc_rkmTraj_m64_r128_s3_v2 : List ℕ := pCat wc_rkmTraj_m64_r128_s3_v2_p0 (pCat
  wc_rkmTraj_m64_r128_s3_v2_p1 wc_rkmTraj_m64_r128_s3_v2_p2)
private def wc_rkmTraj_m64_r128_s2_hb_p0 : List ℕ := [133582572491325,187807003621585,
  228658628084186,262464214374190,291689603668117,317606861969224,340975971092206,362294872382507,
  381911339497376,400079954881432,416993931763993,432804164855725,447631271978313,461573545739966,
  474712397066031,487116196041712,498843052543046,509942874438616,520458920757917,530428993812919,
  539886368065520,548860523651374,557377732661273,565461532859531,573133114244968,580411637337731,
  587314497413634,593857545526883,600055274676934,605920977625801,611466881480092,616704263093056,
  621643548528475,626294399197657,630665786787721,634766058710867,638602995495794,642183861295799,
  645515448489546,648604117189695,651455830343595,654076185002912,656470440250676,658643542201022,
  660600146426059,662344638113400,663881150215169,665213579813323,666345602895585,667280687710409,
  668022106847245,668572948169411,668936124710560,669114383631642,669110314323011,668926355725671,
  668564802936342,668027813152770,667317411008514,666435493339901,665383833422135,664164084706264,
  662777784084008,661226354703077]
private def wc_rkmTraj_m64_r128_s2_hb_p1 : List ℕ := [659511108351582,657633247426356,
  655593866496413,653393953469319,651034390364880,648515953697225,645839314462975,643005037729808,
  640013581816142,636865297048947,633560424082697,630099091758215,626481314475438,622706989049000,
  618775891009753,614687670308903,610441846374148,606037802458873,601474779215952,596751867416736,
  591867999723097,586821941405603,581612279883612,576237412942726,570695535461043,564984624447184,
  559102422159117,553046417032197,546813822095961,540401550500097,533806187698199,527023959750133,
  520050697095940,512881793020831,505512155864888,497936153823234,490147550920309,482139432408778,
  473904117416920,465433056117118,456716707969478,447744396648546,438504136002373,428982419699360,
  419163964910569,409031397188615,398564859239084,387741519922408,376534950608921,364914322389286,
  352843357066041,340278932997707,327169196171786,313450943626154,299045904571435,283855292809112,
  267751534251645,250565143117767,232062739792253,211907584211792,189581870111538,164212564303122,
  134095242406742,94825398221807]
private def wc_rkmTraj_m64_r128_s2_hb : List ℕ := pCat wc_rkmTraj_m64_r128_s2_hb_p0
  wc_rkmTraj_m64_r128_s2_hb_p1
private def wc_rkmTraj_m64_r128_s2_v0_p0 : List ℕ := [1999999999706406,2000000000062761,
  1999999999804163,1999999999910400,1999999999847574,1999999999888479,1999999999883396,
  1999999999871269,1999999999918312,2000000000140381,2000000000046330,2000000000145578,
  2000000000010874,2000000000143719,1999999999976457,1999999999865359,1999999999944550,
  1999999999881315,1999999999916720,1999999999903290,1999999999894340,2000000000070020,
  2000000000121509,2000000000040222,2000000000130245,2000000000009117,2000000000131749,
  2000000000021531,2000000000126447,2000000000050095,2000000000115164,2000000000075311,
  1999999999900922,1999999999903773,1999999999920465,1999999999887584,1999999999942032,
  1999999999876224,1999999999964311,1999999999869287,1999999999986094,1999999999866118,
  2000000000006248,2000000000134313,2000000000021009,1999999999877216,1999999999960155,
  1999999999956041,2000000000375262,2000000000637110,2000000000819147,1999999992503127,
  2000000023679783,2000000037821427,2000000031180665,1999999568472527,2000001623032254,
  2000003838621498,2000004974919484,2000005690205762,2000062160229989,2000250298660335,
  2000755266929231,2001928225309273]
private def wc_rkmTraj_m64_r128_s2_v0_p1 : List ℕ := [2004362771164926,2008957082590909,
  2016923204373769,2029698616608551,2048726473238169,2075104901787297,2109158097787635,
  2150036203496621,2195482566369822,2241893463451274,2284728963962200,2319229255077851,
  2341283933985078,2348234913162466,2339397010616715,2316157121824540,2281636243404044,
  2240023152928200,2195770246374188,2152856611592730,2114274334523960,2081807509180061,
  2056084459477591,2036820938211898,2023148466700385,2013933862292753,2008029058113240,
  2004427907438850,2002336389954892,2001179102512180,2000568902295689,2000262299264290,
  2000115503407061,2000048547411851,2000019463209125,1999992562799785,1999997293648712,
  2000000936983446,2000000308320865,2000000096316346,2000000028528161,2000000008000494,
  2000000002121077,2000000000530693,2000000000125062,2000000000027693,2000000000005743,
  2000000000001108,2000000000000195,2000000000000029,2000000000000003,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m64_r128_s2_v0_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m64_r128_s2_v0 : List ℕ := pCat wc_rkmTraj_m64_r128_s2_v0_p0 (pCat
  wc_rkmTraj_m64_r128_s2_v0_p1 wc_rkmTraj_m64_r128_s2_v0_p2)
private def wc_rkmTraj_m64_r128_s2_v1_p0 : List ℕ := [1999999999830274,1999999999867707,
  1999999999774680,1999999999987715,1999999999882226,1999999999898665,2000000000005418,
  1999999999930794,1999999999953332,1999999999955128,1999999999891731,1999999999819686,
  2000000000055958,1999999999886056,1999999999941248,1999999999855274,1999999999831952,
  1999999999881649,1999999999909293,1999999999950581,1999999999961344,1999999999897843,
  2000000000125010,2000000000052640,2000000000148724,2000000000047887,2000000000111775,
  1999999999883470,2000000000380436,1999999999110447,2000000002265019,1999999994417062,
  2000000012080978,1999999973972052,2000000052209480,1999999900126283,2000000179360339,
  1999999697441970,2000000477033958,1999999301363791,2000000943072907,1999998845457443,
  2000001243358664,1999998902365748,2000000633491688,2000000110129122,1999999138961336,
  2000001136876447,1999999441007667,1999999390089761,2000001307352340,1999999431300218,
  1999998985753865,2000001371415644,2000000339389919,1999998294693134,2000000212243040,
  2000001855124051,1999999554060101,1999997945579011,2000000252204728,2000002315902627,
  2000000520395201,1999997707236041]
private def wc_rkmTraj_m64_r128_s2_v1_p1 : List ℕ := [1999998120576254,2000001199632445,
  2000002999195041,2000001478106880,1999998359654775,1999996545614109,1999997094429533,
  1999998890560467,2000000864657135,2000004592900943,2000014431171888,2000031969598403,
  2000043369292112,2000004186344075,1999841031166764,1999500033357679,1999082082942324,
  1999060573095879,2000553277261050,2005477978476318,2016500382469528,2036514970742888,
  2067848786338873,2111137078710660,2164535104341768,2223375538482425,2280742961257706,
  2328839279447746,2360694134948919,2371850107773364,2361335543114313,2331675516145441,
  2288097598499002,2237144653188323,2185182700328549,2137295020692650,2096713111156787,
  2064762779768903,2041234905445852,2024963384188927,2014371704168667,2007871409389092,
  2004101640936194,2002030712147135,2000952028288598,2000420424386454,2000173845125116,
  2000066950422893,2000023929901837,2000007931927355,2000002444240278,2000000704460641,
  2000000191649882,2000000049738873,2000000012419320,2000000002989943,2000000000689610,
  2000000000150273,2000000000030378,2000000000005582,2000000000000909,2000000000000126,
  2000000000000013,2000000000000000]
private def wc_rkmTraj_m64_r128_s2_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m64_r128_s2_v1 : List ℕ := pCat wc_rkmTraj_m64_r128_s2_v1_p0 (pCat
  wc_rkmTraj_m64_r128_s2_v1_p1 wc_rkmTraj_m64_r128_s2_v1_p2)
private def wc_rkmTraj_m64_r128_s2_v2_p0 : List ℕ := [1999999999919868,1999999999880590,
  2000000000029724,1999999999963309,2000000000051975,1999999999845621,1999999999843852,
  1999999999943169,1999999999953851,1999999999769597,2000000000065967,1999999999578604,
  2000000000777123,1999999997816960,2000000004984013,1999999988252351,2000000025071743,
  1999999949274796,2000000096291548,1999999828328241,2000000286274982,1999999554612868,
  2000000641814518,1999999149667383,2000001020259674,1999998917656869,2000000966375634,
  1999999362951253,2000000133070346,2000000407521248,1999999225615820,2000000771118614,
  1999999649123500,1999999709576024,2000000756530984,1999999311497817,2000000072072859,
  2000000636323578,1999999198813591,2000000194638852,2000000650566793,1999999161654730,
  2000000074015227,2000000830698042,1999999253258436,1999999673266630,2000001024262311,
  1999999691017328,1999999089823615,2000000817321011,2000000572885078,1999998881985604,
  1999999818448685,2000001245157096,1999999847021783,1999998708514391,2000000409717817,
  2000001281267997,1999999524533239,1999998550768199,2000000674876513,2000001221216677,
  2000000026360667,1999997770345340]
private def wc_rkmTraj_m64_r128_s2_v2_p1 : List ℕ := [2000000945297265,2000000451595767,
  2000002132661863,1999996430974460,2000000974620486,1999998955996763,2000003604666463,
  1999998926761832,1999997966483342,1999999852187392,1999999197961084,2000004282411301,
  1999999451371962,1999998257597281,1999998923606267,1999997217485007,2000003769116985,
  2000003159187092,1999999115854796,1999998110993498,1999993441377320,2000001935617818,
  2000020030972771,2000017358109008,1999976121802254,1999896333692201,1999857699818947,
  2000033907724435,2000510980434203,2001033557755220,2000861595813129,1998997736960685,
  1995067249974252,1990621576874622,1990045993075500,2000192166072740,2028304981530286,
  2078700741749107,2149664835878634,2232325889519519,2312418451684709,2374423561744186,
  2406415801469982,2403602478497139,2369191769256991,2312528422977049,2245618000663533,
  2179596619973833,2122346648035651,2077706423641598,2046021675009336,2025405022372299,
  2013056787662068,2006235340355367,2002758823996052,2001126423777805,2000422245121766,
  2000144381526465,2000044671835571,2000012377786036,2000003029290984,2000000642020021,
  2000000114215265,2000000016104966]
private def wc_rkmTraj_m64_r128_s2_v2_p2 : List ℕ := [2000000001561855]
private def wc_rkmTraj_m64_r128_s2_v2 : List ℕ := pCat wc_rkmTraj_m64_r128_s2_v2_p0 (pCat
  wc_rkmTraj_m64_r128_s2_v2_p1 wc_rkmTraj_m64_r128_s2_v2_p2)
private def wc_rkmTraj_m64_r128_s0_hb : List ℕ := [185457354131315,259200730255090,
  313682891346036,357848340375860,395203295732051,427566109858369,456028536353424,481309234482589,
  503912322950317,524208324304957,542479478487022,558946931632212,573787959012917,587147361736421,
  599145283776494,609882737232327,619445608535758,627907627430495,635332609237498,641776176320605,
  647287098755224,651908351503771,655677957050547,658629663204488,660793492451355,662196189837000,
  662861589618570,662810916001065,662063029630288,660634628765335,658540411945429,655793207314870,
  652404072444506,648382367391241,643735802793710,638470463951943,632590811029192,626099654695804,
  618998105657010,611285495510826,602959265197998,594014815840990,584445314898204,574241448107617,
  563391104408369,551878976538119,539686053750357,526788974223220,513159191897969,498761893536751,
  483554573177810,467485126878773,450489260152211,432486884718028,413376984008272,393030076596632,
  371276752964012,347889466191018,322551999727368,294804603167789,263935894645098,228740444741969,
  186855690354650,132158698490271]
private def wc_rkmTraj_m64_r128_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTraj_m64_r128_s0_v1_p0 : List ℕ := [2000131204662139,2000620352186296,
  2002046897398586,2005441586011569,2012360454412091,2024772323374971,2044700675027809,
  2073640829776953,2111887225792396,2157993536506889,2208597930198526,2258755438650648,
  2302755092932263,2335225940619689,2352226376781346,2352011362190291,2335279759277431,
  2304872245266561,2265051980387490,2220599096502049,2175962154116661,2134647182802952,
  2098923951564582,2069830647238485,2047391567762984,2030938299279013,2019436835737726,
  2011755691201055,2006846877268998,2003841115659650,2002075932455140,2001080944651883,
  2000542306895310,2000262137584358,2000122073442772,2000054759575384,2000023656948888,
  2000009840173797,2000003939576031,2000001517492117,2000000562120728,2000000200134053,
  2000000068442498,2000000022466173,2000000007072464,2000000002133246,2000000000615843,
  2000000000169950,2000000000044769,2000000000011236,2000000000002679,2000000000000603,
  2000000000000126,2000000000000023,2000000000000003,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m64_r128_s0_v1_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m64_r128_s0_v1 : List ℕ := pCat wc_rkmTraj_m64_r128_s0_v1_p0
  wc_rkmTraj_m64_r128_s0_v1_p1
private def wc_rkmTraj_m8_r64_s3_hb : List ℕ := [215836882823424,300470080590637,362157933222540,
  411439057882152,452461820667030,487386306325406,517514711108715,543707764878295,566571817411488,
  586554506306393,603998400581888,619173240670794,632296395376886,643546422104387,653072384900345,
  661000453646736,667438699338779,672480656559997,676208021620972,678692731000546,679998586644887,
  680182544063820,679295745540648,677384357943785,674490258823200,670651603336210,665903296570476,
  660277390035257,653803416822553,646508676756187,638418480445807,629556359332763,619944247406323,
  609602639174674,598550727618234,586806525176184,574386970278927,561308021508046,547584741117713,
  533231369369448,518261390901982,502687594169043,486522124822104,469776533785913,452461820667030,
  434588473045538,416166502124426,397205475147301,377714544940992,357702476893615,337177673639465,
  316148197688443,294621792208929,272605900148108,250107681852268,227134031330960,203691591292723,
  179786767065951,155425739506158,130614476980069,105358746507521,79664124133772,53536004597453,
  26979610352928]
private def wc_rkmTraj_m8_r64_s3_v0 : List ℕ := [1999985276534181,1999993340199220,
  2000008597625790,1999991834414753,1999994481911834,1999973949204207,1999829992058932,
  1999073891056424,2003718531968534,2011745012382189,2030643944714008,2067649732118173,
  2128285217070473,2211234725879852,2304468800943001,2386547900604622,2434318873079164,
  2433417516193958,2385141286563630,2305286394035152,2216065616352429,2136561655946248,
  2077027328459206,2038710778672606,2017286424042870,2006830907329065,2002374488681934,
  2000719909266155,2000188019272316,2000041509284239,2000007511170229,2000001051670831,
  2000000098789496]
private def wc_rkmTraj_m8_r64_s3_v1_p0 : List ℕ := [2000300872815663,2000504904887803,
  2000426600490339,2000054804264320,1999676990654539,1999626211013695,1999939280610092,
  2000302322631730,2000358718899147,2000060813251356,1999704731205355,1999629200795828,
  1999895321444409,2000250996986700,2000380681346907,2000182450100127,1999829403098091,
  1999597220225864,1999645035569487,1999941090189260,2000334202058727,2000608376244492,
  2000474659008428,1999744704321688,1998836315378683,1999024383352638,2001380858084126,
  2004509779613871,2003542167629537,1993438555544762,1976106176655798,1965517994232993,
  1983963891062157,2048854284464663,2158423695405912,2287541719423175,2398037030631867,
  2457131959516220,2452082134886050,2392897690787695,2303833835591344,2210775724291628,
  2131890655138878,2074717754621330,2038414669554183,2017949288017590,2007626577803611,
  2002946365198936,2001034115229276,2000329262889435,2000094903113354,2000024690947948,
  2000005777170880,2000001210039738,2000000225569061,2000000037155511,2000000005359215,
  2000000000669144,2000000000071253,2000000000006340,2000000000000456,2000000000000024,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m8_r64_s3_v1_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m8_r64_s3_v1 : List ℕ := pCat wc_rkmTraj_m8_r64_s3_v1_p0
  wc_rkmTraj_m8_r64_s3_v1_p1
private def wc_rkmTraj_m8_r64_s4_hb : List ℕ := [189999992832171,265479950386568,321196238250017,
  366320158638885,404447910932786,437445069336556,466432084911619,492146745620828,515106765612969,
  535692799301164,554194918847722,570840504575205,585811914446193,599258177691238,611303016559442,
  622050517084052,631589241439629,639995276131624,647334534559165,653664525205070,659035729099403,
  663492686402677,667074862871640,669817347228768,671751416785118,672904999023470,673303049930226,
  672967864819258,671919333652329,670175150044680,667750980985519,664660602614450,660916006041859,
  656527476084248,651503644828150,645851521077121,639576495922282,632682323858520,625171077994560,
  617043076918205,608296779607871,598928643337096,588932937676677,578301505286627,567023456958686,
  555084783953906,542467864529299,529150832819642,515106765612969,500302623908221,484697857973587,
  468242541005538,450874827043762,432517414690221,413072503776162,392414386690138,370378171130069,
  346741853261980,321196238250017,293290853522156,262327314261790,227120038158197,185341316651625,
  130948458204771]
private def wc_rkmTraj_m8_r64_s4_v0_p0 : List ℕ := [1999699127184337,2000504904887803,
  2000426600490339,2000054804264320,2000323009345461,2000373788986305,2000060719389908,
  1999697677368270,1999641281100853,1999939186748644,1999704731205355,2000370799204172,
  2000104678555591,2000250996986700,1999619318653093,1999817549899873,1999829403098091,
  2000402779774136,2000354964430513,2000058909810740,1999665797941273,1999391623755508,
  2000474659008428,2000255295678312,2001163684621317,2000975616647362,1998619141915874,
  1995490220386129,1996457832370463,1993438555544762,1976106176655798,1965517994232993,
  2016036108937843,2048854284464663,2158423695405912,2287541719423175,2398037030631867,
  2457131959516220,2452082134886050,2392897690787695,2303833835591344,2210775724291628,
  2131890655138878,2074717754621330,2038414669554183,2017949288017590,2007626577803611,
  2002946365198936,2001034115229276,2000329262889435,2000094903113354,2000024690947948,
  2000005777170880,1999998789960262,2000000225569061,2000000037155511,1999999994640785,
  1999999999330856,2000000000071253,2000000000006340,1999999999999544,2000000000000024,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m8_r64_s4_v0_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m8_r64_s4_v0 : List ℕ := pCat wc_rkmTraj_m8_r64_s4_v0_p0
  wc_rkmTraj_m8_r64_s4_v0_p1
private def wc_rkmTraj_m8_r64_s4_v1_p0 : List ℕ := [1999688030492331,2000351535389801,
  1999994500787519,1999833551572784,2000115314309667,1999554330214015,2000206260656521,
  1999226642085841,2000293544446186,1998495711723564,2002502596477587,1995736001202814,
  2006700909833493,1992172264621489,2007846972795694,1994914088505791,2000348374122562,
  2005241125541962,1992909860367462,2004153619018283,2003547884754768,1992882626197718,
  2003905942247930,2004795929624058,1993129531514712,1999685611172818,2006072455651133,
  1996562300574439,1995367331821885,2004709444689765,2003258989058785,1995710078223122,
  1997709644609782,2002835810682578,2001189906210899,1998729097519963,2000330647099300,
  2000176780467413,1997397985483873,1999782007925660,2006260855747076,2003691194300999,
  1989509172590393,1983953690310683,2005643802833698,2038553072301979,2038061792528113,
  1979224871629792,1896465174537972,1867213769471718,1949672219105641,2131960050885632,
  2337556637560616,2478284050117911,2507939937621206,2438573953420958,2318445308645809,
  2197511087206188,2105286609470897,2048208210760639,2018828026147787,2006178692648187,
  2001656478088897,2000343164686465]
private def wc_rkmTraj_m8_r64_s4_v1_p1 : List ℕ := [2000047695952404]
private def wc_rkmTraj_m8_r64_s4_v1 : List ℕ := pCat wc_rkmTraj_m8_r64_s4_v1_p0
  wc_rkmTraj_m8_r64_s4_v1_p1
private def wc_rkmTrajPack_m16_r128_s4_hb_p0 : List ℕ := [148899111206006,209313533147176,
  254809654025517,292442625926600,324962573912806,353788418412662,379767996806331,403456892236179,
  425243192478653,445411032901896,464176087923026,481706819672056,498137909670220,513579128916306,
  528121410477526,541841134422619,554803230131231,567063472728143,578670216125305,589665723279574,
  600087202751572,609967627320840,619336388316726,628219824353178,636641652810720,644623325133096,
  652184321805840,659342399112486,666113796991625,672513415254801,678554963872046,684251091850434,
  689613498323361,694653028764700,699379758691821,703803066787946,707931699030063,711773825133384,
  715337088401774,718628649894160,721655227670732,724423131762965,726938295412863,729206303045128,
  731232415368037,733021591942015,734578511507245,735907590321442,737012998724919,737898676121130,
  738568344536187,739025520899705,739273528171096,739315505419752,739154416953864,738793060580786,
  738234075071437,737479946892066,736533016258687,735395482562221,734069409206028,732556727891686,
  730859242383607,728978631778286]
private def wc_rkmTrajPack_m16_r128_s4_hb_p1 : List ℕ := [726916453299509,724674144636667,
  722253025839380,719654300777854,716879058174673,713928272210123,710802802699451,707503394836770,
  704030678496446,700385167078793,696567255882573,692577219982215,688415211582582,684081256818610,
  679575251960933,674896958981706,670046000427029,665021853533423,659823843515698,654451135941724,
  648902728096082,643177439218730,637273899486276,631190537581751,624925566673029,618476968589618,
  611842475951192,605019551957795,598005367499271,590796775178254,583390279764092,575782004501097,
  567967652578919,559942462929988,551701159341125,543237891643692,534546167465718,525618772672275,
  516447678162953,507023930104126,497337519902986,487377229215440,477130443929531,466582929248408,
  455718555520157,444518961041269,432963133266880,421026883034007,408682176507782,395896274931264,
  382630610155576,368839289703019,354467070641273,339446552069571,323694183636543,307104416862388,
  289540820927646,270821984270276,250697893212223,228807510228763,204595226373838,177123554835133,
  144560880141413,102170544126945]
private def wc_rkmTrajPack_m16_r128_s4_hb : List ℕ := pCat wc_rkmTrajPack_m16_r128_s4_hb_p0
  wc_rkmTrajPack_m16_r128_s4_hb_p1
private def wc_rkmTrajPack_m16_r128_s4_v0_p0 : List ℕ := [2000397063268843,2000593600027156,
  2000383685469337,2000131793327870,1999594615646863,2000167642819007,2000354414891041,
  2000239681573180,2000182634111508,2000389205856909,1999788259065899,1999661067809221,
  1999862270745122,2000370862741556,2000149362810285,1999596356933659,1999720919057002,
  1999758050915426,1999796895373485,1999680867091296,2000379395901295,1999855925912779,
  2000433262139123,1999904773948191,1999745406091622,1999965201465196,2000384316893069,
  2000334141208158,1999858326081574,1999598942726525,1999866828330300,1999772305392178,
  1999842344117875,1999763743786624,1999581542429709,1999858908580387,1999735033106193,
  2000304865695382,2000086882586174,2000485607090282,1999518719942260,1999893472302299,
  2000242115783800,1999786939623541,2000175265985493,2000565946013429,2000597116299233,
  1999796401099711,2000366138391227,2000754818602066,2000727294667032,2000309861885917,
  2000215156220977,1999527959145375,2000244479382908,2000311010315010,2000643526059620,
  1999882048877912,1998638057806266,1997222175164673,1997924463299182,1997290945413322,
  1988430598769446,1979090432369879]
private def wc_rkmTrajPack_m16_r128_s4_v0_p1 : List ℕ := [1976585144102127,2010056203470481,
  2026281217868740,2087118539013896,2166495577867735,2251951617717787,2328073793650622,
  2381120661596230,2402850878868032,2392221121080517,2354662971576734,2299624059126392,
  2237543987959065,2177341564813787,2125013414941915,2083392928947940,2052734202564638,
  2031656343984093,2018060214648524,2009800730014425,2005062343484679,1997509977610914,
  1998833347959059,2000520752069115,2000221454054490,2000089715029071,2000034618114688,
  2000012720193281,2000004449426020,2000001481078418,2000000468962248,2000000141183789,
  2000000040392421,2000000010975972,1999999997168923,1999999999307315,2000000000160646,
  2000000000035283,1999999999992671,2000000000001435,1999999999999737,2000000000000043,
  2000000000000005,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m16_r128_s4_v0_p2 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m16_r128_s4_v0 : List ℕ := pCat wc_rkmTrajPack_m16_r128_s4_v0_p0 (pCat
  wc_rkmTrajPack_m16_r128_s4_v0_p1 wc_rkmTrajPack_m16_r128_s4_v0_p2)
private def wc_rkmTrajPack_m16_r128_s4_v1_p0 : List ℕ := [1999765698954820,1999985122952053,
  1999950294772597,1999975946867957,2000345124547935,1999842502678090,2000200934527789,
  1999749862077465,2000345226003363,2000441538958239,2000431850573525,2000607474903865,
  2000333137848359,1999859950366182,2000051441413561,2000391868313163,1999937749136618,
  2000056914656714,1999484344200933,2000177107901536,2000095084873047,2000376976793448,
  2000518575034489,2000181867277718,2000330150514335,1999604237135476,2000030954556279,
  2000092061636181,2000057151118638,1999821161185759,2000203590260416,1999922926675625,
  2000345734102248,2000018408476063,1999830395628278,1999271046569692,1999517742855708,
  2000556623457659,1999090191278314,2001197363139922,1998268243365267,2002847934986849,
  1995598893632482,2004599674475612,1995725785436671,2003899406489233,1998215597771592,
  1999298935779369,2002965906018436,1996547789673537,2002037060366877,2000767239284767,
  1996826134245703,2002772482205355,1999668341485780,1996065927741351,2002567811277475,
  2001347666746771,1996336174525949,2001013677290048,2003592393447181,1996789592190014,
  1997492341436841,2003037771179031]
private def wc_rkmTrajPack_m16_r128_s4_v1_p1 : List ℕ := [2003406285539197,1995706306296893,
  1997657991226331,2002616623360804,2003276566316005,1999786417785131,1996690281221502,
  2000565829934201,2002586373972517,2000915803014171,2000925849233421,1999797253443113,
  1998514778099983,1998484127073419,1997752014329948,2001047269137045,2009677604779467,
  2013024309916086,2003130712940861,1981651276713512,1955047168675269,1937122289286441,
  1947868926177116,1999110128911518,2085368958040790,2189742696405422,2292178103607688,
  2372793729559186,2415867130156994,2415964642414723,2379820903792957,2321307027795229,
  2254382310718863,2189247123997926,2132103424177393,2086143582518910,2052235724562857,
  2029370332270883,2015308583069059,2007416450007590,2003358634176846,2001434281558941,
  2000584186329541,2000229800067729,2000088252485464,2000033278807864,2000012305768959,
  2000004429348338,2000001535700123,2000000507467384,2000000158389312,2000000046363960,
  2000000012658324,2000000003208810,2000000000752127,2000000000162324,2000000000032101,
  2000000000005780,2000000000000938,2000000000000133,2000000000000016,2000000000000001,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m16_r128_s4_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m16_r128_s4_v1 : List ℕ := pCat wc_rkmTrajPack_m16_r128_s4_v1_p0 (pCat
  wc_rkmTrajPack_m16_r128_s4_v1_p1 wc_rkmTrajPack_m16_r128_s4_v1_p2)
private def wc_rkmTrajPack_m16_r128_s4_v2_p0 : List ℕ := [2000385667897085,2000007427250803,
  1999654473709569,1999973847574969,1999778553918416,2000239460738038,1999772786453219,
  1999719196529871,2000372567624350,1999713528631383,1999989747696099,1999723892167361,
  1999943365234593,1999996288596932,2000182459006264,2000050906151035,1999664875300728,
  2000989234820560,1998652981986563,2002235459448589,1996989178298993,2003384954008605,
  1995678659614400,2004038337427417,1997459302651393,2001785765370175,2000875022878915,
  1997973441904256,2003470773227029,1997783237102150,2000507204573872,2002129954358237,
  1997674299586947,2002013003809863,2000339932339924,1997985216908975,2002178617017173,
  1998413355368535,1998937851595764,2002528750049347,1999435779803646,1998170246393325,
  2003338968727791,1998771711905676,1999036750849063,2002572288807261,1999290519203314,
  1998327089865346,2001530596169010,2000774415850220,1997140195358575,2001441509839621,
  2002998553170692,1997047720580011,1999283924317814,2002797482168840,1998788638164899,
  1997615310443489,2001203719444337,2001958940651840,1998182520999922,1997747487171102,
  2002510457143538,2001328435209577]
private def wc_rkmTrajPack_m16_r128_s4_v2_p1 : List ℕ := [1996499388384745,1999709243916543,
  2003528367496891,1999748064134748,1997078250154465,1999936269667662,2002553607426265,
  2001399459368161,1998109264279914,1997887324155029,2001563014016063,2001981718584377,
  1998179722126451,1997823170525885,2000838553116032,2000987070138746,1999460877702617,
  1999886595877018,2000252597946932,1999287120670281,1999247460320516,2000322438625660,
  2001081498731419,2001258142908591,1999807988943266,1996686991954162,1996819370965277,
  2003706230230914,2010396224972660,2006036668233139,1991288349027958,1980413977427241,
  1987333249375785,2012039413680286,2038363943773467,2042694803607035,2009816724435106,
  1948079293873081,1891246729376089,1881146524989670,1942001888687559,2065504306253977,
  2216040669246017,2349556793263380,2432556934578723,2452039293140388,2415021282546320,
  2341252052713488,2253870928893962,2171835465078486,2106151787839155,2059951362406915,
  2030981134466257,2014653001936376,2006341003247226,2002508454061995,2000905642477070,
  2000297599446325,2000088626860163,2000023758837663,2000005672464131,2000001185415263,
  2000000210477583,2000000029991565]
private def wc_rkmTrajPack_m16_r128_s4_v2_p2 : List ℕ := [2000000002973296]
private def wc_rkmTrajPack_m16_r128_s4_v2 : List ℕ := pCat wc_rkmTrajPack_m16_r128_s4_v2_p0 (pCat
  wc_rkmTrajPack_m16_r128_s4_v2_p1 wc_rkmTrajPack_m16_r128_s4_v2_p2)
private def wc_rkmTrajPack_m16_r128_s5_hb_p0 : List ℕ := [150209833195018,211156068326008,
  257052680285639,295016925915511,327823138947638,356902730215570,383111000401890,407008423309732,
  428986502956097,449331875882385,468262115034179,485947165471889,502522894284816,518100038758656,
  532770332421884,546610827698064,559687025524086,572055191999335,583764106683271,594856404563091,
  605369621737157,615337021236220,624788253114220,633749887837397,642245851564503,650297784571024,
  657925338824385,665146426912283,671977431729467,678433384246829,684528115119873,690274384701746,
  695683995110420,700767887289786,705536225449498,709998470831002,714163446399956,718039393787550,
  721634023579761,724954559872543,728007779863505,730800049129766,733337353142190,735625325483786,
  737669273171542,739474199423667,741044824166132,742385602531876,743500741571684,744394215366604,
  745069778706822,745530979480611,745781169898573,745823516662550,745661010174803,745296472871093,
  744732566750782,743971800167870,743016533938710,741868986814915,740531240363478,739005243290264,
  737292815237777,735395650083183]
private def wc_rkmTrajPack_m16_r128_s5_hb_p1 : List ℕ := [733315318758123,731053271607611,
  728610840301338,725989239306880,723189566930577,720212805928183,717059823683684,713731371950953,
  710228086148985,706550484197429,702698964874765,698673805676831,694475160148315,690103054654211,
  685557384552049,680837909718685,675944249377583,670875876163511,665632109351308,660212107163546,
  654614858058153,648839170881145,642883663750916,636746751518584,630426631622980,623921268128158,
  617228373694607,610345389191546,603269460604865,595997412831438,588525719872965,580850470847635,
  572967331121344,564871497716022,556557647973293,548019880226934,539251644954231,530245664516014,
  520993839133692,511487136155258,501715458884742,491667490225747,481330505027413,470690143187499,
  459730133068761,448431951334163,436774400470613,424733078383920,412279704464312,399381251763681,
  385998812627290,372086090597327,357587356451626,342434615975986,326543583345993,309807780964725,
  292089577046019,273205963106790,252904724660516,230821646058580,206396227467015,178682729609342,
  145833413757078,103069926116078]
private def wc_rkmTrajPack_m16_r128_s5_hb : List ℕ := pCat wc_rkmTrajPack_m16_r128_s5_hb_p0
  wc_rkmTrajPack_m16_r128_s5_hb_p1
private def wc_rkmTrajPack_m16_r128_s5_v0_p0 : List ℕ := [2000385667897085,1999992572749197,
  1999654473709569,1999973847574969,2000221446081584,2000239460738038,2000227213546781,
  1999719196529871,1999627432375650,1999713528631383,1999989747696099,2000276107832639,
  1999943365234593,2000003711403068,1999817540993736,1999949093848965,2000335124699272,
  2000989234820560,2001347018013437,2002235459448589,2003010821701007,2003384954008605,
  1995678659614400,1995961662572583,1997459302651393,1998214234629825,1999124977121085,
  1997973441904256,2003470773227029,2002216762897850,2000507204573872,2002129954358237,
  1997674299586947,1997986996190137,1999660067660076,1997985216908975,1997821382982827,
  2001586644631465,2001062148404236,2002528750049347,2000564220196354,1998170246393325,
  1996661031272209,1998771711905676,2000963249150937,2002572288807261,1999290519203314,
  1998327089865346,2001530596169010,2000774415850220,2002859804641425,2001441509839621,
  2002998553170692,2002952279419989,2000716075682186,2002797482168840,2001211361835101,
  2002384689556511,2001203719444337,2001958940651840,2001817479000078,2002252512828898,
  2002510457143538,2001328435209577]
private def wc_rkmTrajPack_m16_r128_s5_v0_p1 : List ℕ := [1996499388384745,2000290756083457,
  1996471632503109,1999748064134748,1997078250154465,2000063730332338,2002553607426265,
  2001399459368161,2001890735720086,2002112675844971,2001563014016063,2001981718584377,
  1998179722126451,2002176829474115,1999161446883968,2000987070138746,1999460877702617,
  2000113404122982,2000252597946932,2000712879329719,2000752539679484,1999677561374340,
  2001081498731419,2001258142908591,1999807988943266,2003313008045838,2003180629034723,
  2003706230230914,2010396224972660,2006036668233139,2008711650972042,2019586022572759,
  2012666750624215,2012039413680286,2038363943773467,2042694803607035,2009816724435106,
  2051920706126919,2108753270623911,2118853475010330,2057998111312441,2065504306253977,
  2216040669246017,2349556793263380,2432556934578723,2452039293140388,2415021282546320,
  2341252052713488,2253870928893962,2171835465078486,2106151787839155,2059951362406915,
  2030981134466257,2014653001936376,2006341003247226,2002508454061995,2000905642477070,
  2000297599446325,2000088626860163,1999976241162337,1999994327535869,1999998814584737,
  1999999789522417,1999999970008435]
private def wc_rkmTrajPack_m16_r128_s5_v0_p2 : List ℕ := [2000000002973296]
private def wc_rkmTrajPack_m16_r128_s5_v0 : List ℕ := pCat wc_rkmTrajPack_m16_r128_s5_v0_p0 (pCat
  wc_rkmTrajPack_m16_r128_s5_v0_p1 wc_rkmTrajPack_m16_r128_s5_v0_p2)
private def wc_rkmTrajPack_m16_r128_s5_v1_p0 : List ℕ := [2000040933595641,2000030601097633,
  1999772746311921,2000233881772835,1999947584103263,2000703522796399,1999433009058692,
  2001109476627164,1999743692241210,1999590276132223,2001394238015006,1998539657046819,
  2000045144922979,2001251448140836,1997902382390925,2000592109256377,2000524616804424,
  1999980348011614,2000055979706889,2000604162061742,1998966676831174,2001863583158456,
  2000010008025500,1997165453650892,1999961412887665,2002448403228868,2000186587171826,
  1997588150311855,2000353609674953,1999384215803286,2001435050810992,2001677566149974,
  1998769862550174,1999467967620706,1996603843599289,2000300885214661,2001351815881512,
  2002151453079562,2002098813347851,2003011600320914,2002095742342125,2002643572385390,
  1998297129902414,2000445423556578,1995197842614952,1997613622836740,1996689775411128,
  1999794218871190,2000652320860041,1997888070868406,2001084156628247,2003575433633405,
  2002016236402919,2001781999367876,1995964533791343,1998268090121512,1996448718597625,
  2001194660500108,2000821902396299,2000787720957092,2000606075620756,1999518320499976,
  1999483111464456,1998728736008818]
private def wc_rkmTrajPack_m16_r128_s5_v1_p1 : List ℕ := [2000260099421094,2000809946059693,
  1998683390785794,1998375170086623,1999921094047440,2001030353839399,1999392243486067,
  1999897081141619,2002840121637549,2001044418866960,2003348719008051,2002162200447807,
  2000797859501975,2004030112509710,1998379382562635,2003402563436725,2002480982071068,
  2003686586543937,2000379250735282,2008204494691944,1993271025302581,2005590668341966,
  1997587542108747,1990266042591353,2009714432344186,1992050249920156,2000279911935251,
  2004918616043346,2003984112206200,1991972883894157,2007505852595711,2011520462400419,
  1979823895166582,2006753186289708,2021621199088184,1974405714022050,1993340135262621,
  2035642254562951,1989831615665010,1964851082224078,2023339151223548,2032964393013165,
  1971078798453931,1969957527169384,2037601285367440,2048782147710516,1984173248780970,
  1957413012004785,2021476438529902,2092355058433082,2077696294476055,2000250731405648,
  1968663008011503,2058855967844230,2244528937105954,2427305045905639,2517019625957489,
  2487545867603117,2375234429532247,2240218088216183,2128469533746604,2056950880868967,
  2020427254886813,2005608287907472]
private def wc_rkmTrajPack_m16_r128_s5_v1_p2 : List ℕ := [2001019390913726]
private def wc_rkmTrajPack_m16_r128_s5_v1 : List ℕ := pCat wc_rkmTrajPack_m16_r128_s5_v1_p0 (pCat
  wc_rkmTrajPack_m16_r128_s5_v1_p1 wc_rkmTrajPack_m16_r128_s5_v1_p2)
private def wc_rkmTrajPack_m16_r128_s5_v2_p0 : List ℕ := [1999230774302295,1999529020510126,
  2000372625445389,2001311775717055,1998171419431644,1999918477304761,2001130638489270,
  2000774927709697,1998949087069950,1998783833409739,2001847584295773,2000048784391790,
  1998861379990992,1999909761918429,2000023217134176,2001720504822269,1997679307811385,
  2001097744582631,2000801490672109,1999292543380395,1998916525461743,2002990152813806,
  1998836932454574,2000813649758645,1997797119067186,2001391531653057,2001817711569360,
  1999517823687914,1999349323281079,1998801520030085,1999923883530974,2002596343221985,
  1997872956547824,2001201947984221,1997652061333187,2000215623980975,2000662018520625,
  2000624282480378,2001669903198367,1999616238857345,1998854256745446,1998595565526180,
  2000944046104067,2001867887808750,1999750605169366,1999608834739212,1999334588035807,
  1998696174292204,1999163259702716,2000370847879422,2002517762078559,2000501397970887,
  1999635192249098,1999383632680842,1998920323981641,2001153219402031,1995937254095476,
  2001039103716356,1996086672584087,2004523163433876,2002738843082574,2004715535943825,
  1998396945349095,2005220897373086]
private def wc_rkmTrajPack_m16_r128_s5_v2_p1 : List ℕ := [1998764978878851,2001289540788307,
  2000598077183520,1991449581487072,2004482136602625,1987099245835010,2005720565062388,
  2001569258522923,1999402950063554,2005361696046619,1996386903671985,1999553148965862,
  2000304596843395,1998842025172646,1996632767256485,2004803223731122,1997215855847721,
  1996028814748971,2010519714174223,1990142074224490,1999488282280112,2012543996453305,
  1983517897331148,2005018549999456,2010308527276448,1978075402312926,2011002745437008,
  2011160796248702,1977853615350331,2016771585913619,2013226402640075,1973922883758273,
  2014676636434158,2017920433737649,1974094858910026,2012537969326467,2028564425527832,
  1974259129471724,1995510308674627,2032335162512119,1980819980228260,1974254439376129,
  2032909016644871,2008101454559166,1962227871655889,2013140703777229,2038790891088020,
  1972583899014455,1969021611997417,2043043081729346,2026070276196861,1945478036773651,
  1978381344810148,2067501757199160,2022126538650829,1916788651799206,1972815485176498,
  2119998934319545,2082240191064401,1881876803108026,1875820420551504,2217045991855818,
  2592477350250030,2630286749190100]
private def wc_rkmTrajPack_m16_r128_s5_v2_p2 : List ℕ := [2347491951559026]
private def wc_rkmTrajPack_m16_r128_s5_v2 : List ℕ := pCat wc_rkmTrajPack_m16_r128_s5_v2_p0 (pCat
  wc_rkmTrajPack_m16_r128_s5_v2_p1 wc_rkmTrajPack_m16_r128_s5_v2_p2)
private def wc_rkmTrajPack_m16_r128_s3_hb_p0 : List ℕ := [164887855407360,231364870751860,
  281131734630420,322046592592500,357178564187669,388114114024772,415802934952839,440868493873624,
  463747093333200,484758754757378,504146840366915,522101792885067,538776153243854,554294485547188,
  568760176955000,582260239407240,594868788697852,606649621735194,617658162977821,627942959620256,
  637546847554541,646507872889531,654860029109757,662633853213025,669856912592400,676554206285071,
  682748498388165,688460597216996,693709590674685,698513045989130,702887180231685,706847006706472,
  710406461280662,713578511936169,716375254205380,718807994666460,720887324286930,722623183094777,
  724024917407227,725101330645490,725860728599317,726310959870430,726459452112870,726313244596404,
  725879017542682,725163118619942,724171586928483,722910174763939,721384367407200,719599401157362,
  717560279796496,715271789651323,712738513396693,709964842728241,706954990016608,703712999042517,
  700242754900742,696547993151104,692632308286087,688499161577105,684151888354897,679593704773701,
  674827714103788,669856912592400]
private def wc_rkmTrajPack_m16_r128_s3_hb_p1 : List ℕ := [664684194929159,659312359348512,
  653744112398576,647982073403018,642028778640075,635886685260613,629558174965119,623045557457767,
  616351073694063,609476898937158,602425145636616,595197866142264,587797055264674,580224652692904,
  572482545279233,564572569199864,556496511999840,548256114529784,539853072781483,531289039628784,
  522565626479818,513684404846074,504646907833473,495454631560201,486109036505722,476611548795069,
  466963561422241,457166435416245,447221500953098,437130058416862,426893379412598,416512707733901,
  405989260287551,395324227977589,384518776551037,373574047407300,362491158373166,351271204445228,
  339915258501386,328424371983044,316799575549478,305041879705770,293152275405644,281131734630420,
  268981210945275,256701640033887,244293940212523,231759012924533,219097743216168,206311000194610,
  193399637469025,180364493575418,167206392386023,153926143503937,140524542643638,127002371998023,
  113360400592560,99599384627097,85720067805885,71723181656294,57609445836720,43379568434127,
  29034246251658,14574165086731]
private def wc_rkmTrajPack_m16_r128_s3_hb : List ℕ := pCat wc_rkmTrajPack_m16_r128_s3_hb_p0
  wc_rkmTrajPack_m16_r128_s3_hb_p1
private def wc_rkmTrajPack_m16_r128_s3_v0_p0 : List ℕ := [2000033066496369,1999912802195303,
  1999846357772248,2000204584129958,2000209465259311,2000152666557253,2000044774734450,
  2000079863828233,2000177955192499,2000215926061761,2000182753807056,2000091707871863,
  1999972168714823,1999856914256345,1999771088266145,1999726521768392,1999722102691828,
  1999747942361598,1999790609137524,2000162513871142,2000118828869920,2000069984792142,
  1999961276462415,1999618073659540,1998605391594749,2003980908161805,2009735183085131,
  2021036547017512,2040819010354863,2071859277472914,2115613420710961,2170930928909790,
  2233224805064625,2294680247122008,2345741687981465,2377540909918201,2384417341039103,
  2365545993555676,2325038276757231,2270538546243659,2210950848388852,2154191545866754,
  2105695432776993,2067964155728073,2040998385824802,2023199266175949,2012310607506424,
  2006123139269263,2002852706439882,2001243724478216,2000506820858008,2000192748836335,
  2000068284152233,2000022481729053,1999993140802084,1999998067581912,1999999499538467,
  2000000118471321,2000000025446411,2000000004910665,2000000000839908,2000000000124798,
  2000000000015601,2000000000001545]
private def wc_rkmTrajPack_m16_r128_s3_v0_p1 : List ℕ := [2000000000000102]
private def wc_rkmTrajPack_m16_r128_s3_v0 : List ℕ := pCat wc_rkmTrajPack_m16_r128_s3_v0_p0
  wc_rkmTrajPack_m16_r128_s3_v0_p1
private def wc_rkmTrajPack_m16_r128_s3_v1_p0 : List ℕ := [1999936924923215,1999935076791157,
  1999974971747366,2000050482108117,2000037889106323,2000165800379691,1999921442456930,
  2000261929361809,1999584852180180,2000385868183811,1999296432666365,2000334383058398,
  1999905883956929,1999628065989194,2000604568234906,2000088553821122,1999623654823225,
  2000426598358195,2000376070859462,1999591756991146,1999872639473963,2000547503696834,
  2000246511416108,1999714605237611,2000042638917432,2000609080430834,2000405243950867,
  1999762376705691,1999647322707356,2000144046463094,2000461091707692,2000094640595594,
  1999400174767976,1999084016780779,1999416450710890,2000094791148411,2000578904955027,
  2000605587448095,2000245014435659,1999803325629573,1999506256610075,1999308663583479,
  1998909448847779,1997931049575542,1996432779091145,1995543556554867,1997901098919799,
  2007590552089198,2029217353104958,2066202822872496,2118944243315931,2183630354089776,
  2252371284030038,2314850908921732,2360988374542804,2383603559484396,2380139129650132,
  2352938327899327,2308141165016736,2253740752310026,2197552107270712,2145713513475139,
  2101995257862635,2067851502717484]
private def wc_rkmTrajPack_m16_r128_s3_v1_p1 : List ℕ := [2042954351388905,2025907731946206,
  2014902229717532,2008180557239265,2004287328508167,2002145166682136,2001024347330585,
  2000466510010049,2000202459188101,2000083652911942,2000032878255397,2000012282412648,
  2000004358494350,2000001468511868,2000000469680617,2000000142592928,2000000041100332,
  2000000011252093,2000000002928032,2000000000725000,2000000000171068,2000000000038540,
  2000000000008311,2000000000001719,2000000000000340,2000000000000063,2000000000000010,
  2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m16_r128_s3_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m16_r128_s3_v1 : List ℕ := pCat wc_rkmTrajPack_m16_r128_s3_v1_p0 (pCat
  wc_rkmTrajPack_m16_r128_s3_v1_p1 wc_rkmTrajPack_m16_r128_s3_v1_p2)
private def wc_rkmTrajPack_m16_r128_s3_v2_p0 : List ℕ := [1999602936731157,2000593600027156,
  1999616314530663,1999868206672130,2000405384353137,1999832357180993,1999645585108959,
  2000239681573180,2000182634111508,1999610794143091,1999788259065899,2000338932190779,
  2000137729254878,1999629137258444,1999850637189715,2000403643066341,2000279080942998,
  1999758050915426,1999796895373485,2000319132908704,2000379395901295,1999855925912779,
  1999566737860877,1999904773948191,2000254593908378,2000034798534804,1999615683106931,
  1999665858791842,2000141673918426,2000401057273475,2000133171669700,1999772305392178,
  1999842344117875,2000236256213376,2000418457570291,2000141091419613,1999735033106193,
  1999695134304618,2000086882586174,2000485607090282,2000481280057740,2000106527697701,
  1999757884216200,1999786939623541,2000175265985493,2000565946013429,2000597116299233,
  2000203598900289,1999633861608773,1999245181397934,1999272705332968,1999690138114083,
  2000215156220977,2000472040854625,2000244479382908,1999688989684990,1999356473940380,
  1999882048877912,2001361942193734,2002777824835327,2002075536700818,1997290945413322,
  1988430598769446,1979090432369879]
private def wc_rkmTrajPack_m16_r128_s3_v2_p1 : List ℕ := [1976585144102127,1989943796529519,
  2026281217868740,2087118539013896,2166495577867735,2251951617717787,2328073793650622,
  2381120661596230,2402850878868032,2392221121080517,2354662971576734,2299624059126392,
  2237543987959065,2177341564813787,2125013414941915,2083392928947940,2052734202564638,
  2031656343984093,2018060214648524,2009800730014425,2005062343484679,2002490022389086,
  2001166652040941,2000520752069115,2000221454054490,2000089715029071,2000034618114688,
  2000012720193281,2000004449426020,2000001481078418,2000000468962248,2000000141183789,
  2000000040392421,2000000010975972,2000000002831077,2000000000692685,2000000000160646,
  2000000000035283,2000000000007329,2000000000001435,2000000000000263,2000000000000043,
  2000000000000005,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m16_r128_s3_v2_p2 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m16_r128_s3_v2 : List ℕ := pCat wc_rkmTrajPack_m16_r128_s3_v2_p0 (pCat
  wc_rkmTrajPack_m16_r128_s3_v2_p1 wc_rkmTrajPack_m16_r128_s3_v2_p2)
private def wc_rkmTrajPack_m8_r64_s3_hb : List ℕ := [235764032000000,328210993268318,
  395594179458129,449425186000000,494235377063845,532384267312048,565294278319073,593905606866480,
  618880584000000,640708175477582,659762578017008,676338435847769,690673186357482,702961872270137,
  713367319977119,722027348000000,729060004993126,734567461124330,738638955319464,741353065595768,
  742779484416743,742980425712024,742011753478346,739923896942168,736762600000000,732569540485644,
  727382846100431,721237527510541,714165844451924,706197617205772,697360493184818,687680176371714,
  677180625812198,665884228170778,653811948420586,640983462000000,627417271180713,613130807921017,
  598140525098323,582461977706892,566109895355285,549098247191750,531440300215539,513148671791006,
  494235377063845,474711871880406,454589091728409,433877487147625,412587056000000,390727372938473,
  368307616370900,345336593178741,321822761418721,297774251208433,273198883973433,248104190212989,
  222497425923984,196385587807022,169775427365358,142673463995423,115085997157402,87019117705161,
  58478718446800,29470504000000]
private def wc_rkmTrajPack_m8_r64_s3_v0 : List ℕ := [1999952884700236,1999995589962854,
  1999966110770138,1999996321383418,2000034754534885,2000070253002587,2000448668421033,
  2002146640522994,2007538065413038,2021373001300976,2050789591378820,2102826665220459,
  2179428490139780,2272375662327228,2362345731363020,2424847300734190,2440969033344110,
  2406548551699674,2333767244112405,2244441666757762,2159868941752821,2093397897206669,
  2048714627913963,2022650851449048,2009364341776667,2003428405505039,2001105041423680,
  2000310924092748,2000075427847814,2000015481565417,2000002606762394,2000000339917244,
  2000000029762315]
private def wc_rkmTrajPack_m8_r64_s3_v1_p0 : List ℕ := [2000000349908990,2000000806407213,
  2000000960251677,2000000281902906,1999998632499324,1999996144049354,1999992524906757,
  1999987110697600,1999980365438987,1999975210271523,1999975934568561,1999984724193714,
  1999998280562650,2000007845817650,2000005049507419,1999990140182049,1999971605958342,
  1999954857117964,1999943357614303,1999965874631217,2000069161495488,2000199125281317,
  2000091704281290,1999514455230970,1998902547264260,1999577661440386,2002459014544921,
  2005688352578588,2003965334842083,1992456968890292,1974103956733610,1964071420457677,
  1984925731874919,2052971062880815,2164626044109613,2293514269178779,2401601469562283,
  2457391661029186,2449620904468905,2389133022048710,2300147295465841,2207974962832968,
  2130152436770931,2073828012608795,2038047708240733,2017838437836402,2007612632453809,
  2002956520601227,2001044058077751,2000334743853154,2000097229746423,2000025510762799,
  2000006023798867,2000001274126185,2000000240007123,2000000039972457,2000000005832847,
  2000000000737187,2000000000079498,2000000000007167,2000000000000524,2000000000000029,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m8_r64_s3_v1_p1 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m8_r64_s3_v1 : List ℕ := pCat wc_rkmTrajPack_m8_r64_s3_v1_p0
  wc_rkmTrajPack_m8_r64_s3_v1_p1
private abbrev dP_0 : Prop := atF [ bNLE (bEvalLo12W 16 512 128 [1,2,4,8,15,15,15,15]
  [20842079,18635863,17406591,17390516,13592567,13712219,3438145,1017601] [6,9,16,27,32,32,8,3]
  rkmMasksPack_m16_r128 [none, none, none, some (27, 129, wc_rkmTrajPack_m16_r128_s3_hb,
  wc_rkmTrajPack_m16_r128_s3_v0, wc_rkmTrajPack_m16_r128_s3_v2), some (32, 129,
  wc_rkmTrajPack_m16_r128_s4_hb, wc_rkmTrajPack_m16_r128_s4_v0, wc_rkmTrajPack_m16_r128_s4_v2),
  some (32, 129, wc_rkmTrajPack_m16_r128_s5_hb, wc_rkmTrajPack_m16_r128_s5_v0,
  wc_rkmTrajPack_m16_r128_s5_v2)]) rkmRowPack_m16_r128, bNLE (bEvalLo12W 4 2048 15
  [1,2,4,7,7,7,7,7] [55991019,63017616,74717665,27462898,26775003,8637892,3627913,1505655]
  [2,3,6,3,3,1,1,1] rkmMasks_m4_r15 []) rkmRow_m4_r15] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bNLE (bEvalLo12W 8 1024 64 [1,2,4,8,15,15,15,15]
  [29706502,20556738,23373568,29470504,17494370,16982910,3927764,4194691] [3,4,8,16,15,15,4,4]
  rkmMasksPack_m8_r64 [none, none, none, some (16, 65, wc_rkmTrajPack_m8_r64_s3_hb,
  wc_rkmTrajPack_m8_r64_s3_v0, wc_rkmTrajPack_m8_r64_s3_v1)]) rkmRowPack_m8_r64, bNLE (bEvalLo12W
  8 1024 29 [1,3] [84012673,55960906] [6,9] rkmMasksPack_m8_r29 []) rkmRowPack_m8_r29] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bNLE (bEvalLo12W 16 512 52 [1,2,4,6,6,6]
  [37512446,26009589,28129987,38779971,6559489,1816682] [6,8,13,24,4,2] rkmMasksPack_m16_r52 [])
  rkmRowPack_m16_r52, bNLE (bEvalLo12W 32 256 18 [1,1,1,1,1,1,1,1]
  [38779271,32405439,25007098,11602943,16341483,20662049,12829724,8170656] [5,5,4,2,3,3,2,2]
  rkmMasksPack_m32_r18 []) rkmRowPack_m32_r18] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bNLE (bEvalLo12W 64 128 128 [1,2,4,4,4,4,4,4]
  [22539370,30115142,10331250,11875000,3727238,1701892,718442,307545] [22,50,28,32,10,5,2,1]
  rkmMasks_m64_r128 [some (22, 65, wc_rkmTraj_m64_r128_s0_hb, wc_rkmTraj_m64_r128_s0_v0,
  wc_rkmTraj_m64_r128_s0_v1), some (50, 129, wc_rkmTraj_m64_r128_s1_hb, wc_rkmTraj_m64_r128_s1_v0,
  wc_rkmTraj_m64_r128_s1_ck3), some (28, 129, wc_rkmTraj_m64_r128_s2_hb, wc_rkmTraj_m64_r128_s2_v0,
  wc_rkmTraj_m64_r128_s2_v2), some (32, 129, wc_rkmTraj_m64_r128_s3_hb, wc_rkmTraj_m64_r128_s3_v0,
  wc_rkmTraj_m64_r128_s3_v2)]) rkmRow_m64_r128, bNLE (bEvalLo12W 8 1024 20 [1,3,4,4,4]
  [74451371,54928241,35104171,33039607,20040182] [5,8,6,6,4] rkmMasks_m8_r20 []) rkmRow_m8_r20,
  bNLE (bEvalLo12W 8 1024 13 [1,2,3,3,3,3,3,3]
  [104278958,77334622,30855755,30300772,6630946,1385692,2978476,1375205] [4,5,3,3,1,1,1,1]
  rkmMasksPack_m8_r13 []) rkmRowPack_m8_r13] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bSlideChk 17 129 wc_rkmTraj_m64_r128_s1_hb
  wc_rkmTraj_m64_r128_s1_v0 wc_rkmTraj_m64_r128_s1_v1, bNLE (bEvalLo12W 128 64 21 [1,1]
  [70092364,1491294] [25,2] rkmMasks_m128_r21 []) rkmRow_m128_r21, bNLE (bEvalLo12W 8 1024 18
  [1,3,3,3] [83600712,131261687,27035018,7084983] [4,14,3,1] rkmMasksPack_m8_r18 [])
  rkmRowPack_m8_r18] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bSlideChk 17 129 wc_rkmTraj_m64_r128_s1_hb
  wc_rkmTraj_m64_r128_s1_v1 wc_rkmTraj_m64_r128_s1_v2, bNLE (bEvalLo12W 64 128 20
  [1,1,1,1,1,1,1,1] [17050267,21045576,24898230,19474280,8588921,6748195,4935400,3239261]
  [4,5,6,5,2,2,2,1] rkmMasksPack_m64_r20 []) rkmRowPack_m64_r20, bNLE (bEvalLo12W 512 16 17
  [1,1,1] [33394223,992702,81052] [19,2,2] rkmMasks_m512_r17 []) rkmRow_m512_r17] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bNLE (bEvalLo12W 2 4096 52 [2,4,8,16,32,48,48,48]
  [22635565,20560262,22518981,27810509,22985625,30220580,3268926,1353622] [2,2,4,8,11,19,3,1]
  rkmMasks_m2_r52 []) rkmRow_m2_r52, bNLE (bEvalLo12W 256 32 22 [1,1] [48545681,1015335] [26,2]
  rkmMasks_m256_r22 []) rkmRow_m256_r22, bNLE (bEvalLo12W 8 1024 16 [1,1,2,2,3,3,3,3]
  [31948968,55460632,22772589,24045213,42273936,43861210,22243933,8743651] [2,3,2,2,5,5,3,1]
  rkmMasksPack_m8_r16 []) rkmRowPack_m8_r16] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m64_r128_s1_hb
  wc_rkmTraj_m64_r128_s1_v2 wc_rkmTraj_m64_r128_s1_ck3, bNLE (bEvalLo12W 1024 8 29 [1] [24500227]
  [34] rkmMasks_m1024_r29 []) rkmRow_m1024_r29, bNLE (bEvalLo12W 16 512 5 [1,1,1,1,1,1,1,1]
  [44438321,55521138,28616739,23187748,22982538,9673018,6982645,8174169] [2,2,1,1,1,1,1,1]
  rkmMasksPack_m16_r5 []) rkmRowPack_m16_r5] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m64_r128_s3_hb
  wc_rkmTraj_m64_r128_s3_v0 wc_rkmTraj_m64_r128_s3_v1, bNLE (bEvalLo12W 64 128 27
  [1,1,1,1,1,1,1,1] [35151992,25211725,18145236,8645963,10406438,4527937,5107901,3787451]
  [10,7,5,3,3,2,2,2] rkmMasksPack_m64_r27 []) rkmRowPack_m64_r27, bNLE (bEvalLo12W 128 64 3 [1,1]
  [61371801,2264837] [26,1] rkmMasks_m128_r3 []) rkmRow_m128_r3] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m64_r128_s3_hb
  wc_rkmTraj_m64_r128_s3_v1 wc_rkmTraj_m64_r128_s3_v2, bNLE (bEvalLo12W 512 16 27 [1] [34833724]
  [32] rkmMasks_m512_r27 []) rkmRow_m512_r27, bNLE (bEvalLo12W 2 4096 3 [1,2,2,2]
  [158132021,248431486,17637144,9291468] [2,3,1,1] rkmMasks_m2_r3 []) rkmRow_m2_r3] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := atF [ bSlideChk 16 129 wc_rkmTrajPack_m16_r128_s4_hb
  wc_rkmTrajPack_m16_r128_s4_v0 wc_rkmTrajPack_m16_r128_s4_v1, bNLE (bEvalLo12W 4 2048 28
  [1,2,4,8,13,13,13] [30483680,27355728,35000317,35268193,54582295,4624528,5473497]
  [2,2,4,7,14,2,2] rkmMasksPack_m4_r28 []) rkmRowPack_m4_r28, bNLE (bEvalLo12W 16 512 12 [1,1,1,1]
  [187252792,22599231,27261744,19773485] [11,2,2,2] rkmMasksPack_m16_r12 []) rkmRowPack_m16_r12,
  bNLE (bEvalLo12W 64 128 10 [1,1,1] [93223545,4091991,2031730] [11,1,1] rkmMasksPack_m64_r10 [])
  rkmRowPack_m64_r10] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := atF [ bSlideChk 16 129 wc_rkmTrajPack_m16_r128_s4_hb
  wc_rkmTrajPack_m16_r128_s4_v1 wc_rkmTrajPack_m16_r128_s4_v2, bNLE (bEvalLo12W 1024 8 26 [1]
  [24457258] [30] rkmMasks_m1024_r26 []) rkmRow_m1024_r26, bNLE (bEvalLo12W 8 1024 11 [1,2,2,2,2]
  [111790357,75007087,47327869,30881891,14331445] [5,6,4,3,2] rkmMasks_m8_r11 []) rkmRow_m8_r11,
  bNLE (bEvalLo12W 32 256 8 [1,1,1,1,1,1,1,1]
  [37881641,36400522,13027007,25540425,10053010,7087821,8299091,4597688] [3,3,1,2,1,1,1,1]
  rkmMasksPack_m32_r8 []) rkmRowPack_m32_r8] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := atF [ bSlideChk 16 129 wc_rkmTrajPack_m16_r128_s5_hb
  wc_rkmTrajPack_m16_r128_s5_v0 wc_rkmTrajPack_m16_r128_s5_v1, bNLE (bEvalLo12W 128 64 23 [1,1,1]
  [66783945,3709982,1509461] [26,3,2] rkmMasks_m128_r23 []) rkmRow_m128_r23, bNLE (bEvalLo12W 4
  2048 16 [1,2,4,7,7,7,7,7]
  [49827523,56395548,57446564,35906624,33229715,10832664,4549718,2159983] [2,3,5,5,4,2,1,1]
  rkmMasks_m4_r16 []) rkmRow_m4_r16] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := atF [ bSlideChk 16 129 wc_rkmTrajPack_m16_r128_s5_hb
  wc_rkmTrajPack_m16_r128_s5_v1 wc_rkmTrajPack_m16_r128_s5_v2, bNLE (bEvalLo12W 2 4096 28
  [2,4,8,16,21,21,21] [41880369,31559512,37233662,31242267,38045846,7972773,10315487]
  [2,2,4,6,9,2,3] rkmMasksPack_m2_r28 []) rkmRowPack_m2_r28, bNLE (bEvalLo12W 32 256 17 [1,1,1]
  [134702639,19313947,8983035] [18,4,3] rkmMasks_m32_r17 []) rkmRow_m32_r17] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := atF [ bNLE (bEvalLo12W 8 1024 64 [1,2,4,8,15,15,15,15]
  [26184101,23076348,24758964,28665836,17344547,17206000,5192508,2483469] [3,5,9,17,16,16,5,3]
  rkmMasks_m8_r64 [none, none, none, some (17, 65, wc_rkmTraj_m8_r64_s3_hb,
  wc_rkmTraj_m8_r64_s3_v0, wc_rkmTraj_m8_r64_s3_v1), some (16, 65, wc_rkmTraj_m8_r64_s4_hb,
  wc_rkmTraj_m8_r64_s4_v0, wc_rkmTraj_m8_r64_s4_v1)]) rkmRow_m8_r64, bSlideChk 16 65
  wc_rkmTrajPack_m8_r64_s3_hb wc_rkmTrajPack_m8_r64_s3_v0 wc_rkmTrajPack_m8_r64_s3_v1, bNLE
  (bEvalLo12W 256 32 6 [1,1,1] [32119375,8502188,6612813] [6,2,2] rkmMasks_m256_r6 [])
  rkmRow_m256_r6] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := atF [ bNLE (bEvalLo12W 64 128 38 [1,1,1,1,1,1,1,1]
  [34496653,27686684,20739197,12184884,9743183,5398411,6125233,4686595] [13,10,8,5,4,2,3,2]
  rkmMasksPack_m64_r38 []) rkmRowPack_m64_r38, bSlideChk 16 65 wc_rkmTraj_m8_r64_s4_hb
  wc_rkmTraj_m8_r64_s4_v0 wc_rkmTraj_m8_r64_s4_v1, bNLE (bEvalLo12W 32 256 12 [1,1,1]
  [134708127,10240390,6198277] [14,2,2] rkmMasks_m32_r12 []) rkmRow_m32_r12] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := atF [ bSlideChk 14 129 wc_rkmTraj_m64_r128_s2_hb
  wc_rkmTraj_m64_r128_s2_v0 wc_rkmTraj_m64_r128_s2_v1, bNLE (bEvalLo12W 8 1024 96
  [1,1,1,1,12,12,12,12] [13844892,14418871,21556395,6018473,2311005,2101479,3056494,1394380]
  [2,2,3,1,3,3,3,2] rkmMasksPack_m8_r96 []) rkmRowPack_m8_r96, bNLE (bEvalLo12W 4 2048 3 [1,1,1]
  [304403310,70489808,42759528] [4,1,1] rkmMasks_m4_r3 []) rkmRow_m4_r3, bNLE (bEvalLo12W 2 4096
  10 [1,2,4,8] [52841708,54970565,77839424,74956175] [1,2,3,4] rkmMasksPack_m2_r10 [])
  rkmRowPack_m2_r10] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := atF [ bSlideChk 14 129 wc_rkmTraj_m64_r128_s2_hb
  wc_rkmTraj_m64_r128_s2_v1 wc_rkmTraj_m64_r128_s2_v2, bSlideChk 17 65 wc_rkmTraj_m8_r64_s3_hb
  wc_rkmTraj_m8_r64_s3_v0 wc_rkmTraj_m8_r64_s3_v1, bNLE (bEvalLo12W 16 512 26 [1,1]
  [61440750,24374119] [7,3] rkmMasksPack_m16_r26 []) rkmRowPack_m16_r26, bNLE (bEvalLo12W 16 512 8
  [1,1,1,1,1,1,1,1] [67062672,67108112,25452051,25926168,10530504,10609064,6408516,6405300]
  [4,4,2,2,1,1,1,1] rkmMasks_m16_r8 []) rkmRow_m16_r8] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := atF [ bSlideChk 14 129 wc_rkmTrajPack_m16_r128_s3_hb
  wc_rkmTrajPack_m16_r128_s3_v0 wc_rkmTrajPack_m16_r128_s3_v1, bNLE (bEvalLo12W 4 2048 32
  [1,2,4,8,14,14,14,14] [28091247,32700285,34805631,45809763,25542155,24313578,6346733,2618495]
  [2,3,5,10,8,8,2,1] rkmMasks_m4_r32 []) rkmRow_m4_r32, bNLE (bEvalLo12W 16 512 10 [1,1,1,1]
  [139757620,54335065,25837173,15604146] [9,4,3,2] rkmMasks_m16_r10 []) rkmRow_m16_r10, bNLE
  (bEvalLo12W 32 256 3 [1,1,1,1] [86394154,36789145,2456108,2975855] [3,2,1,1] rkmMasksPack_m32_r3
  []) rkmRowPack_m32_r3] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := atF [ bSlideChk 13 129 wc_rkmTrajPack_m16_r128_s3_hb
  wc_rkmTrajPack_m16_r128_s3_v1 wc_rkmTrajPack_m16_r128_s3_v2, bNLE (bEvalLo12W 512 16 30
  [1,1,1,1] [33398723,1209885,230985,87678] [33,3,2,2] rkmMasks_m512_r30 []) rkmRow_m512_r30, bNLE
  (bEvalLo12W 2 4096 26 [1,2,4,8] [40434655,36115107,44041242,42878551] [2,3,4,6] rkmMasks_m2_r26
  []) rkmRow_m2_r26, bNLE (bEvalLo12W 2 4096 8 [1,2,4,6,6,6,6,6]
  [70652723,75201565,99811244,42453672,35017328,13194600,5541731,2272327] [1,2,4,2,2,1,1,1]
  rkmMasks_m2_r8 []) rkmRow_m2_r8] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := atF [ bNLE (bEvalLo12W 16 512 35 [1,2,3,3,3,3]
  [43051324,39590868,51411708,27670940,12420874,5752543] [7,10,16,9,5,3] rkmMasks_m16_r35 [])
  rkmRow_m16_r35, bNLE (bEvalLo12W 64 128 33 [1,1,1] [97917597,13084576,5071924] [32,5,2]
  rkmMasksPack_m64_r33 []) rkmRowPack_m64_r33, bNLE (bEvalLo12W 512 16 5 [1,1,1]
  [11553700,13860840,7586665] [4,4,3] rkmMasks_m512_r5 []) rkmRow_m512_r5] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := atF [ bSlideChk 22 65 wc_rkmTraj_m64_r128_s0_hb
  wc_rkmTraj_m64_r128_s0_v0 wc_rkmTraj_m64_r128_s0_v1, bNLE (bEvalLo12W 1024 8 32
  [1,1,1,1,1,1,1,1] [11808428,11807788,391437,391438,32137,32337,38286,37859] [18,18,1,1,1,1,1,1]
  rkmMasks_m1024_r32 []) rkmRow_m1024_r32, bNLE (bEvalLo12W 64 128 15 [1,1,1]
  [95135686,4809186,2798324] [17,2,2] rkmMasks_m64_r15 []) rkmRow_m64_r15] = true
private theorem bk_21 : dP_21 := by decide +kernel
private theorem ws_rkmTraj_m64_r128_s1_m1 : WalkOk (some (34, 129, wc_rkmTraj_m64_r128_s1_hb,
    wc_rkmTraj_m64_r128_s1_v0, wc_rkmTraj_m64_r128_s1_v2)) := mIter_split rfl
    (bSlideChk_sound bk_4) (bSlideChk_sound bk_5)
private theorem ws_rkmTraj_m64_r128_s1 : WalkOk (some (50, 129, wc_rkmTraj_m64_r128_s1_hb,
    wc_rkmTraj_m64_r128_s1_v0, wc_rkmTraj_m64_r128_s1_ck3)) := mIter_split rfl
    ws_rkmTraj_m64_r128_s1_m1 (bSlideChk_sound bk_7)
private theorem ws_rkmTraj_m64_r128_s2 : WalkOk (some (28, 129, wc_rkmTraj_m64_r128_s2_hb,
    wc_rkmTraj_m64_r128_s2_v0, wc_rkmTraj_m64_r128_s2_v2)) := mIter_split rfl
    (bSlideChk_sound bk_16) (bSlideChk_sound bk_17)
private theorem ws_rkmTraj_m64_r128_s3 : WalkOk (some (32, 129, wc_rkmTraj_m64_r128_s3_hb,
    wc_rkmTraj_m64_r128_s3_v0, wc_rkmTraj_m64_r128_s3_v2)) := mIter_split rfl
    (bSlideChk_sound bk_8) (bSlideChk_sound bk_9)
private theorem ws_rkmTrajPack_m16_r128_s3 : WalkOk (some (27, 129, wc_rkmTrajPack_m16_r128_s3_hb,
    wc_rkmTrajPack_m16_r128_s3_v0, wc_rkmTrajPack_m16_r128_s3_v2)) := mIter_split rfl
    (bSlideChk_sound bk_18) (bSlideChk_sound bk_19)
private theorem ws_rkmTrajPack_m16_r128_s4 : WalkOk (some (32, 129, wc_rkmTrajPack_m16_r128_s4_hb,
    wc_rkmTrajPack_m16_r128_s4_v0, wc_rkmTrajPack_m16_r128_s4_v2)) := mIter_split rfl
    (bSlideChk_sound bk_10) (bSlideChk_sound bk_11)
private theorem ws_rkmTrajPack_m16_r128_s5 : WalkOk (some (32, 129, wc_rkmTrajPack_m16_r128_s5_hb,
    wc_rkmTrajPack_m16_r128_s5_v0, wc_rkmTrajPack_m16_r128_s5_v2)) := mIter_split rfl
    (bSlideChk_sound bk_12) (bSlideChk_sound bk_13)
theorem rkmTraj_m64_r128 : rkmEvalT16Lo12 64 128 128 [1, 2, 4, 4, 4, 4, 4, 4] [22539370, 30115142,
  10331250, 11875000, 3727238, 1701892, 718442, 307545] [22, 50, 28, 32, 10, 5, 2, 1]
  rkmMasks_m64_r128 = rkmRow_m64_r128 :=
    bhW_eq bk_3 (wCons (bSlideChk_sound bk_21) (wCons ws_rkmTraj_m64_r128_s1 (wCons
      ws_rkmTraj_m64_r128_s2 (wCons ws_rkmTraj_m64_r128_s3 wNil))))
theorem rkmTraj_m512_r17 : rkmEvalT16Lo12 512 16 17 [1, 1, 1] [33394223, 992702, 81052] [19, 2, 2]
  rkmMasks_m512_r17 = rkmRow_m512_r17 := bh0_eq (tl2 bk_5)
theorem rkmTraj_m4_r3 : rkmEvalT16Lo12 4 2048 3 [1, 1, 1] [304403310, 70489808, 42759528] [4, 1, 1]
  rkmMasks_m4_r3 = rkmRow_m4_r3 := bh0_eq (tl2 bk_16)
theorem rkmTraj_m8_r64 : rkmEvalT16Lo12 8 1024 64 [1, 2, 4, 8, 15, 15, 15, 15] [26184101, 23076348,
  24758964, 28665836, 17344547, 17206000, 5192508, 2483469] [3, 5, 9, 17, 16, 16, 5, 3]
  rkmMasks_m8_r64 = rkmRow_m8_r64 :=
    bhW_eq bk_14 (wSkip (wSkip (wSkip (wCons (bSlideChk_sound (tl1 bk_17)) (wCons (bSlideChk_sound
      (tl1 bk_15)) wNil)))))
theorem rkmTraj_m2_r3 : rkmEvalT16Lo12 2 4096 3 [1, 2, 2, 2] [158132021, 248431486, 17637144,
  9291468] [2, 3, 1, 1] rkmMasks_m2_r3 = rkmRow_m2_r3 := bh0_eq (tl2 bk_9)
theorem rkmTraj_m2_r52 : rkmEvalT16Lo12 2 4096 52 [2, 4, 8, 16, 32, 48, 48, 48] [22635565, 20560262,
  22518981, 27810509, 22985625, 30220580, 3268926, 1353622] [2, 2, 4, 8, 11, 19, 3, 1]
  rkmMasks_m2_r52 = rkmRow_m2_r52 := bh0_eq bk_6
theorem rkmTraj_m512_r5 : rkmEvalT16Lo12 512 16 5 [1, 1, 1] [11553700, 13860840, 7586665] [4, 4, 3]
  rkmMasks_m512_r5 = rkmRow_m512_r5 := bh0_eq (tl2 bk_20)
theorem rkmTraj_m16_r35 : rkmEvalT16Lo12 16 512 35 [1, 2, 3, 3, 3, 3] [43051324, 39590868, 51411708,
  27670940, 12420874, 5752543] [7, 10, 16, 9, 5, 3] rkmMasks_m16_r35 = rkmRow_m16_r35 :=
    bh0_eq bk_20
theorem rkmTraj_m256_r6 : rkmEvalT16Lo12 256 32 6 [1, 1, 1] [32119375, 8502188, 6612813] [6, 2, 2]
  rkmMasks_m256_r6 = rkmRow_m256_r6 := bh0_eq (tl2 bk_14)
theorem rkmTraj_m1024_r32 : rkmEvalT16Lo12 1024 8 32 [1, 1, 1, 1, 1, 1, 1, 1] [11808428, 11807788,
  391437, 391438, 32137, 32337, 38286, 37859] [18, 18, 1, 1, 1, 1, 1, 1] rkmMasks_m1024_r32 =
  rkmRow_m1024_r32 := bh0_eq (tl1 bk_21)
theorem rkmTraj_m128_r3 : rkmEvalT16Lo12 128 64 3 [1, 1] [61371801, 2264837] [26, 1]
  rkmMasks_m128_r3 = rkmRow_m128_r3 := bh0_eq (tl2 bk_8)
theorem rkmTraj_m512_r30 : rkmEvalT16Lo12 512 16 30 [1, 1, 1, 1] [33398723, 1209885, 230985, 87678]
  [33, 3, 2, 2] rkmMasks_m512_r30 = rkmRow_m512_r30 := bh0_eq (tl1 bk_19)
theorem rkmTraj_m2_r8 : rkmEvalT16Lo12 2 4096 8 [1, 2, 4, 6, 6, 6, 6, 6] [70652723, 75201565,
  99811244, 42453672, 35017328, 13194600, 5541731, 2272327] [1, 2, 4, 2, 2, 1, 1, 1] rkmMasks_m2_r8
  = rkmRow_m2_r8 := bh0_eq (tl1 (tl2 bk_19))
theorem rkmTraj_m4_r32 : rkmEvalT16Lo12 4 2048 32 [1, 2, 4, 8, 14, 14, 14, 14] [28091247, 32700285,
  34805631, 45809763, 25542155, 24313578, 6346733, 2618495] [2, 3, 5, 10, 8, 8, 2, 1]
  rkmMasks_m4_r32 = rkmRow_m4_r32 := bh0_eq (tl1 bk_18)
theorem rkmTraj_m16_r8 : rkmEvalT16Lo12 16 512 8 [1, 1, 1, 1, 1, 1, 1, 1] [67062672, 67108112,
  25452051, 25926168, 10530504, 10609064, 6408516, 6405300] [4, 4, 2, 2, 1, 1, 1, 1] rkmMasks_m16_r8
  = rkmRow_m16_r8 := bh0_eq (tl1 (tl2 bk_17))
theorem rkmTraj_m1024_r29 : rkmEvalT16Lo12 1024 8 29 [1] [24500227] [34] rkmMasks_m1024_r29 =
  rkmRow_m1024_r29 := bh0_eq (tl1 bk_7)
theorem rkmTraj_m2_r26 : rkmEvalT16Lo12 2 4096 26 [1, 2, 4, 8] [40434655, 36115107, 44041242,
  42878551] [2, 3, 4, 6] rkmMasks_m2_r26 = rkmRow_m2_r26 := bh0_eq (tl2 bk_19)
theorem rkmTraj_m512_r27 : rkmEvalT16Lo12 512 16 27 [1] [34833724] [32] rkmMasks_m512_r27 =
  rkmRow_m512_r27 := bh0_eq (tl1 bk_9)
theorem rkmTraj_m16_r10 : rkmEvalT16Lo12 16 512 10 [1, 1, 1, 1] [139757620, 54335065, 25837173,
  15604146] [9, 4, 3, 2] rkmMasks_m16_r10 = rkmRow_m16_r10 := bh0_eq (tl2 bk_18)
theorem rkmTraj_m1024_r26 : rkmEvalT16Lo12 1024 8 26 [1] [24457258] [30] rkmMasks_m1024_r26 =
  rkmRow_m1024_r26 := bh0_eq (tl1 bk_11)
theorem rkmTraj_m8_r11 : rkmEvalT16Lo12 8 1024 11 [1, 2, 2, 2, 2] [111790357, 75007087, 47327869,
  30881891, 14331445] [5, 6, 4, 3, 2] rkmMasks_m8_r11 = rkmRow_m8_r11 := bh0_eq (tl2 bk_11)
theorem rkmTraj_m128_r23 : rkmEvalT16Lo12 128 64 23 [1, 1, 1] [66783945, 3709982, 1509461] [26, 3,
  2] rkmMasks_m128_r23 = rkmRow_m128_r23 := bh0_eq (tl1 bk_12)
theorem rkmTraj_m32_r12 : rkmEvalT16Lo12 32 256 12 [1, 1, 1] [134708127, 10240390, 6198277] [14, 2,
  2] rkmMasks_m32_r12 = rkmRow_m32_r12 := bh0_eq (tl2 bk_15)
theorem rkmTraj_m256_r22 : rkmEvalT16Lo12 256 32 22 [1, 1] [48545681, 1015335] [26, 2]
  rkmMasks_m256_r22 = rkmRow_m256_r22 := bh0_eq (tl1 bk_6)
theorem rkmTraj_m4_r15 : rkmEvalT16Lo12 4 2048 15 [1, 2, 4, 7, 7, 7, 7, 7] [55991019, 63017616,
  74717665, 27462898, 26775003, 8637892, 3627913, 1505655] [2, 3, 6, 3, 3, 1, 1, 1] rkmMasks_m4_r15
  = rkmRow_m4_r15 := bh0_eq (tl1 bk_0)
theorem rkmTraj_m128_r21 : rkmEvalT16Lo12 128 64 21 [1, 1] [70092364, 1491294] [25, 2]
  rkmMasks_m128_r21 = rkmRow_m128_r21 := bh0_eq (tl1 bk_4)
theorem rkmTraj_m64_r15 : rkmEvalT16Lo12 64 128 15 [1, 1, 1] [95135686, 4809186, 2798324] [17, 2, 2]
  rkmMasks_m64_r15 = rkmRow_m64_r15 := bh0_eq (tl2 bk_21)
theorem rkmTraj_m8_r20 : rkmEvalT16Lo12 8 1024 20 [1, 3, 4, 4, 4] [74451371, 54928241, 35104171,
  33039607, 20040182] [5, 8, 6, 6, 4] rkmMasks_m8_r20 = rkmRow_m8_r20 := bh0_eq (tl1 bk_3)
theorem rkmTraj_m4_r16 : rkmEvalT16Lo12 4 2048 16 [1, 2, 4, 7, 7, 7, 7, 7] [49827523, 56395548,
  57446564, 35906624, 33229715, 10832664, 4549718, 2159983] [2, 3, 5, 5, 4, 2, 1, 1] rkmMasks_m4_r16
  = rkmRow_m4_r16 := bh0_eq (tl2 bk_12)
theorem rkmTraj_m32_r17 : rkmEvalT16Lo12 32 256 17 [1, 1, 1] [134702639, 19313947, 8983035] [18, 4,
  3] rkmMasks_m32_r17 = rkmRow_m32_r17 := bh0_eq (tl2 bk_13)
theorem rkmTrajPack_m16_r128 : rkmEvalT16Lo12 16 512 128 [1,2,4,8,15,15,15,15]
  [20842079,18635863,17406591,17390516,13592567,13712219,3438145,1017601] [6,9,16,27,32,32,8,3]
  rkmMasksPack_m16_r128 = rkmRowPack_m16_r128 :=
    bhW_eq bk_0 (wSkip (wSkip (wSkip (wCons ws_rkmTrajPack_m16_r128_s3 (wCons
      ws_rkmTrajPack_m16_r128_s4 (wCons ws_rkmTrajPack_m16_r128_s5 wNil))))))
theorem rkmTrajPack_m32_r3 : rkmEvalT16Lo12 32 256 3 [1,1,1,1] [86394154,36789145,2456108,2975855]
  [3,2,1,1] rkmMasksPack_m32_r3 = rkmRowPack_m32_r3 := bh0_eq (tl1 (tl2 bk_18))
theorem rkmTrajPack_m8_r64 : rkmEvalT16Lo12 8 1024 64 [1,2,4,8,15,15,15,15]
  [29706502,20556738,23373568,29470504,17494370,16982910,3927764,4194691] [3,4,8,16,15,15,4,4]
  rkmMasksPack_m8_r64 = rkmRowPack_m8_r64 :=
    bhW_eq bk_1 (wSkip (wSkip (wSkip (wCons (bSlideChk_sound (tl1 bk_14)) wNil))))
theorem rkmTrajPack_m16_r5 : rkmEvalT16Lo12 16 512 5 [1,1,1,1,1,1,1,1]
  [44438321,55521138,28616739,23187748,22982538,9673018,6982645,8174169] [2,2,1,1,1,1,1,1]
  rkmMasksPack_m16_r5 = rkmRowPack_m16_r5 := bh0_eq (tl2 bk_7)
theorem rkmTrajPack_m16_r52 : rkmEvalT16Lo12 16 512 52 [1,2,4,6,6,6]
  [37512446,26009589,28129987,38779971,6559489,1816682] [6,8,13,24,4,2] rkmMasksPack_m16_r52 =
  rkmRowPack_m16_r52 := bh0_eq bk_2
theorem rkmTrajPack_m2_r10 : rkmEvalT16Lo12 2 4096 10 [1,2,4,8]
  [52841708,54970565,77839424,74956175] [1,2,3,4] rkmMasksPack_m2_r10 = rkmRowPack_m2_r10 :=
    bh0_eq (tl1 (tl2 bk_16))
theorem rkmTrajPack_m64_r38 : rkmEvalT16Lo12 64 128 38 [1,1,1,1,1,1,1,1]
  [34496653,27686684,20739197,12184884,9743183,5398411,6125233,4686595] [13,10,8,5,4,2,3,2]
  rkmMasksPack_m64_r38 = rkmRowPack_m64_r38 := bh0_eq bk_15
theorem rkmTrajPack_m32_r8 : rkmEvalT16Lo12 32 256 8 [1,1,1,1,1,1,1,1]
  [37881641,36400522,13027007,25540425,10053010,7087821,8299091,4597688] [3,3,1,2,1,1,1,1]
  rkmMasksPack_m32_r8 = rkmRowPack_m32_r8 := bh0_eq (tl1 (tl2 bk_11))
theorem rkmTrajPack_m64_r33 : rkmEvalT16Lo12 64 128 33 [1,1,1] [97917597,13084576,5071924] [32,5,2]
  rkmMasksPack_m64_r33 = rkmRowPack_m64_r33 := bh0_eq (tl1 bk_20)
theorem rkmTrajPack_m64_r10 : rkmEvalT16Lo12 64 128 10 [1,1,1] [93223545,4091991,2031730] [11,1,1]
  rkmMasksPack_m64_r10 = rkmRowPack_m64_r10 := bh0_eq (tl1 (tl2 bk_10))
theorem rkmTrajPack_m8_r96 : rkmEvalT16Lo12 8 1024 96 [1,1,1,1,12,12,12,12]
  [13844892,14418871,21556395,6018473,2311005,2101479,3056494,1394380] [2,2,3,1,3,3,3,2]
  rkmMasksPack_m8_r96 = rkmRowPack_m8_r96 := bh0_eq (tl1 bk_16)
theorem rkmTrajPack_m16_r26 : rkmEvalT16Lo12 16 512 26 [1,1] [61440750,24374119] [7,3]
  rkmMasksPack_m16_r26 = rkmRowPack_m16_r26 := bh0_eq (tl2 bk_17)
theorem rkmTrajPack_m64_r27 : rkmEvalT16Lo12 64 128 27 [1,1,1,1,1,1,1,1]
  [35151992,25211725,18145236,8645963,10406438,4527937,5107901,3787451] [10,7,5,3,3,2,2,2]
  rkmMasksPack_m64_r27 = rkmRowPack_m64_r27 := bh0_eq (tl1 bk_8)
theorem rkmTrajPack_m16_r12 : rkmEvalT16Lo12 16 512 12 [1,1,1,1]
  [187252792,22599231,27261744,19773485] [11,2,2,2] rkmMasksPack_m16_r12 = rkmRowPack_m16_r12 :=
    bh0_eq (tl2 bk_10)
theorem rkmTrajPack_m4_r28 : rkmEvalT16Lo12 4 2048 28 [1,2,4,8,13,13,13]
  [30483680,27355728,35000317,35268193,54582295,4624528,5473497] [2,2,4,7,14,2,2]
  rkmMasksPack_m4_r28 = rkmRowPack_m4_r28 := bh0_eq (tl1 bk_10)
theorem rkmTrajPack_m8_r13 : rkmEvalT16Lo12 8 1024 13 [1,2,3,3,3,3,3,3]
  [104278958,77334622,30855755,30300772,6630946,1385692,2978476,1375205] [4,5,3,3,1,1,1,1]
  rkmMasksPack_m8_r13 = rkmRowPack_m8_r13 := bh0_eq (tl2 bk_3)
theorem rkmTrajPack_m2_r28 : rkmEvalT16Lo12 2 4096 28 [2,4,8,16,21,21,21]
  [41880369,31559512,37233662,31242267,38045846,7972773,10315487] [2,2,4,6,9,2,3]
  rkmMasksPack_m2_r28 = rkmRowPack_m2_r28 := bh0_eq (tl1 bk_13)
theorem rkmTrajPack_m8_r29 : rkmEvalT16Lo12 8 1024 29 [1,3] [84012673,55960906] [6,9]
  rkmMasksPack_m8_r29 = rkmRowPack_m8_r29 := bh0_eq (tl1 bk_1)
theorem rkmTrajPack_m64_r20 : rkmEvalT16Lo12 64 128 20 [1,1,1,1,1,1,1,1]
  [17050267,21045576,24898230,19474280,8588921,6748195,4935400,3239261] [4,5,6,5,2,2,2,1]
  rkmMasksPack_m64_r20 = rkmRowPack_m64_r20 := bh0_eq (tl1 bk_5)
theorem rkmTrajPack_m8_r16 : rkmEvalT16Lo12 8 1024 16 [1,1,2,2,3,3,3,3]
  [31948968,55460632,22772589,24045213,42273936,43861210,22243933,8743651] [2,3,2,2,5,5,3,1]
  rkmMasksPack_m8_r16 = rkmRowPack_m8_r16 := bh0_eq (tl2 bk_6)
theorem rkmTrajPack_m32_r18 : rkmEvalT16Lo12 32 256 18 [1,1,1,1,1,1,1,1]
  [38779271,32405439,25007098,11602943,16341483,20662049,12829724,8170656] [5,5,4,2,3,3,2,2]
  rkmMasksPack_m32_r18 = rkmRowPack_m32_r18 := bh0_eq (tl1 bk_2)
theorem rkmTrajPack_m8_r18 : rkmEvalT16Lo12 8 1024 18 [1,3,3,3]
  [83600712,131261687,27035018,7084983] [4,14,3,1] rkmMasksPack_m8_r18 = rkmRowPack_m8_r18 :=
    bh0_eq (tl2 bk_4)
end
end QuantumComputation.Specs.DickeSol
