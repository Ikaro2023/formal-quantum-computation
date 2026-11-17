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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxTraj08
/-
# Multi-Segment `T_16` Trajectory Part `10` (`FindAllJohnsonRampKickMuxTraj10`)

Certified kernel trajectory evaluations (`31` rows, `37988` substep-coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Prefix-kick masks for `(m = 2, r = 22)`. -/
def rkmMasks_m2_r22 : List (List Bool) := [[], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 22)`. -/
def rkmRow_m2_r22 : List ℕ := [
  41702376, 1195492291, 1586600446, 128284626283, 409147753277, 347142692916, 102531236702,
  9353863253]
/-- Mask chunk for `(m = 2, r = 24)`. -/
def rkmMkP_m2_r24_s5_p0 : List Bool := [
  false, false, false, false, false, false, true, false, false, true, true, true, true, true,
  false, false, true, true, true]
/-- Mask chunk for `(m = 2, r = 24)`. -/
def rkmMkP_m2_r24_s6_p0 : List Bool := [
  true, true, false, false, false, true, true, true, false, false, false, true, false, false,
  true, false, true]
/-- Prefix-kick masks for `(m = 2, r = 24)`. -/
def rkmMasks_m2_r24 : List (List Bool) := [
  [], [], [], [], [], rkmMkP_m2_r24_s5_p0, rkmMkP_m2_r24_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 24)`. -/
def rkmRow_m2_r24 : List ℕ := [
  30, 1, 5433, 149424, 3444, 89853, 118238, 5139078, 24281, 8323471, 425040552, 174785789,
  146198376, 65112679, 8103950213, 70988575, 4595469721, 31192990753, 1931891614, 31490236026,
  278074699956, 420762146774, 195819774837, 27132860514]
/-- Mask chunk for `(m = 4, r = 14)`. -/
def rkmMkP_m4_r14_s5_p0 : List Bool := [
  false, true, false, false, false, false, true, false, false, false, false, false, true]
/-- Mask chunk for `(m = 4, r = 14)`. -/
def rkmMkP_m4_r14_s6_p0 : List Bool := [
  false, false, false, false, false, false, true, false, true, false, true, false, true]
/-- Prefix-kick masks for `(m = 4, r = 14)`. -/
def rkmMasks_m4_r14 : List (List Bool) := [
  [], [], [false, true, true, true, true, true],
  [false, true, false, false, true, true, false, false, true, true],
  [true, true, false, true, false, true, false, false, true, false, false, true],
  rkmMkP_m4_r14_s5_p0, rkmMkP_m4_r14_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 14)`. -/
def rkmRow_m4_r14 : List ℕ := [
  5041105, 8622453, 30891144, 59707896, 638297940, 6847858, 289593048, 65929093, 4580293541,
  1300177044, 16073156187, 198842104, 179424368527, 797314957060]
/-- Mask chunk for `(m = 4, r = 48)`. -/
def rkmMkP_m4_r48_s5_p0 : List Bool := [
  false, false, true, true, true, false, false, false, true, false, false, true, true, false,
  true, true, true, false, false, false, true, true, false, false, true, true, true, false, false,
  false, false, false, true, true, true]
/-- Mask chunk for `(m = 4, r = 48)`. -/
def rkmMkP_m4_r48_s6_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  false, true, true, false, true, true, true, false, true, true, false, true, false, false, false,
  false, false, false, false, false, false, false, false, false, true]
/-- Prefix-kick masks for `(m = 4, r = 48)`. -/
def rkmMasks_m4_r48 : List (List Bool) := [
  [], [], [], [], [], rkmMkP_m4_r48_s5_p0, rkmMkP_m4_r48_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 48)`. -/
def rkmRow_m4_r48 : List ℕ := [
  0, 0, 0, 2, 0, 2, 0, 3, 0, 2, 0, 211, 64, 25, 0, 7894, 703, 59580, 11392, 231470, 247, 532545,
  5695572, 10916, 25433967, 2787532, 36748, 79017235, 479641835, 1681889, 997126682, 3254015,
  2160123403, 4604773611, 406254943, 6884898352, 52347207901, 426760653, 9205857890, 117940638457,
  274660255493, 284760511362, 167912651536, 61076928428, 13930592036, 1933632444, 148565478,
  4815980]
/-- Prefix-kick masks for `(m = 8, r = 8)`. -/
def rkmMasks_m8_r8 : List (List Bool) := [
  [true], [true, true, false, false, true, true], [false, true, false, true, false, false, true],
  []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 8)`. -/
def rkmRow_m8_r8 : List ℕ := [
  13645211, 177194257, 591100497, 258049205, 4013753771, 370525346, 73442538975, 921132121508]
/-- Prefix-kick masks for `(m = 8, r = 10)`. -/
def rkmMasks_m8_r10 : List (List Bool) := [
  [], [true, false, true, true], [true, false, true, true, false, false, true, true],
  [false, true, true, false, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 10)`. -/
def rkmRow_m8_r10 : List ℕ := [
  58083167, 82510970, 164409040, 413731444, 28088505, 209356196, 6615509220, 264698591,
  77641038424, 914522550605]
/-- Mask chunk for `(m = 8, r = 32)`. -/
def rkmMkP_m8_r32_s2_p0 : List Bool := [
  true, true, true, true, false, false, true, false, false, false, true, true, false, false, true,
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, true]
/-- Mask chunk for `(m = 8, r = 32)`. -/
def rkmMkP_m8_r32_s3_p0 : List Bool := [
  true, true, false, true, false, true, false, true, true, false, true, true, false, false, true,
  true, true, false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 8, r = 32)`. -/
def rkmMkP_m8_r32_s4_p0 : List Bool := [
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, true, false, false, true, false, false, true, false, false,
  true, true]
/-- Mask chunk for `(m = 8, r = 32)`. -/
def rkmMkP_m8_r32_s5_p0 : List Bool := [
  false, true, false, false, false, false, false, false, false, false, false, false, false, true,
  false, true, false, false, false, true, false, false, false, false, false, false, false, false,
  false, false, true]
/-- Mask chunk for `(m = 8, r = 32)`. -/
def rkmMkP_m8_r32_s6_p0 : List Bool := [
  true, true, true, false, false, false, true, false, false, false, false, false, true, false,
  false, false, false, false, false, false, false, false, true, false, false, true, true, true,
  false, false, true]
/-- Prefix-kick masks for `(m = 8, r = 32)`. -/
def rkmMasks_m8_r32 : List (List Bool) := [
  [], [], rkmMkP_m8_r32_s2_p0, rkmMkP_m8_r32_s3_p0, rkmMkP_m8_r32_s4_p0, rkmMkP_m8_r32_s5_p0,
  rkmMkP_m8_r32_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 32)`. -/
def rkmRow_m8_r32 : List ℕ := [
  499869, 6414364, 470937, 9730049, 20635924, 12309603, 3492451, 33198978, 147612002, 62326415,
  3521698, 6398041, 16339068, 12675632, 191173378, 4138527, 501239837, 788969907, 278579631,
  15098955, 1355116268, 9005235, 2986444757, 1013198854, 2131872499, 991794840, 1246661125,
  4915323495, 13004666937, 442314349, 91649865251, 878138786283]
/-- Mask chunk for `(m = 8, r = 80)`. -/
def rkmMkP_m8_r80_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, false, true, true, true, true,
  true, false, false, true, true, true, false, false, true, true, true, true, true, false, false,
  true, false, false, true, true, true, false, false, false, false, false, true, false, false,
  false, false, false, true, false, false, false, true]
/-- Mask chunk for `(m = 8, r = 80)`. -/
def rkmMkP_m8_r80_s4_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, false, true]
/-- Mask chunk for `(m = 8, r = 80)`. -/
def rkmMkP_m8_r80_s5_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, true, false, true,
  false, false, true, true, false, true, false, true, true, false, false, false, false, false,
  false, true, false, false, true, false, false, true, false, false, false, false, false, false,
  false, false, false, false, true, false, true, true]
/-- Prefix-kick masks for `(m = 8, r = 80)`. -/
def rkmMasks_m8_r80 : List (List Bool) := [
  [], [], [], [], rkmMkP_m8_r80_s4_p0 ++ rkmMkP_m8_r80_s4_p1, rkmMkP_m8_r80_s5_p0, []]
/-- Row chunk `0` `(m = 8, r = 80)`. -/
def rkmRowP_m8_r80_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 26, 0, 23, 15, 36,
  315, 39, 279, 6965, 54043, 13941, 3351, 21560, 110463, 28673, 562068, 298040, 704643, 519450,
  965898, 267593, 6680433, 1098546, 70639, 2002300, 1902798, 276744917, 3856957, 42183215,
  1241413511, 191815881, 1724584222, 1297099519, 3051243740, 973438244, 1946082511, 588979241,
  11219138347]
/-- Row chunk `1` `(m = 8, r = 80)`. -/
def rkmRowP_m8_r80_p1 : List ℕ := [
  33178533186, 20369462239, 891320895, 67922487464, 196308451994, 260398423408, 212299350488,
  120827005884, 46791744445, 15029351383, 3048566957, 342809513, 20005189, 578635, 10617, 214]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 80)`. -/
def rkmRow_m8_r80 : List ℕ := rkmRowP_m8_r80_p0 ++ rkmRowP_m8_r80_p1
/-- Mask chunk for `(m = 8, r = 104)`. -/
def rkmMkP_m8_r104_s5_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, false, false, true, false,
  false, true, true, true, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 8, r = 104)`. -/
def rkmMkP_m8_r104_s5_p1 : List Bool := [
  true, true, false, false, false, true, true, false, true, true, false, false, false, false,
  false, false, false, false, true, false, false, true]
/-- Mask chunk for `(m = 8, r = 104)`. -/
def rkmMkP_m8_r104_s6_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, true, false, false, true, false, false,
  false, true, false, true, false, true, false, true, false, true, false]
/-- Mask chunk for `(m = 8, r = 104)`. -/
def rkmMkP_m8_r104_s6_p1 : List Bool := [
  false, false, false, true, true, false, true, false, false, false, false, false, false, true,
  false, false, false, true, true, true, false, true, true]
/-- Prefix-kick masks for `(m = 8, r = 104)`. -/
def rkmMasks_m8_r104 : List (List Bool) := [
  [], [], [], [], [], rkmMkP_m8_r104_s5_p0 ++ rkmMkP_m8_r104_s5_p1,
  rkmMkP_m8_r104_s6_p0 ++ rkmMkP_m8_r104_s6_p1, []]
/-- Row chunk `0` `(m = 8, r = 104)`. -/
def rkmRowP_m8_r104_p0 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 1, 489, 9, 12, 382, 9564, 804, 3704, 134,
  82038, 37, 7000, 63897, 2055224]
/-- Row chunk `1` `(m = 8, r = 104)`. -/
def rkmRowP_m8_r104_p1 : List ℕ := [
  44895, 44733, 95895, 4029392, 439681, 1812256, 11713187, 63750271, 817819, 6767729, 9257413,
  417880138, 126985751, 49436, 269788320, 951567994, 390613122, 1118111843, 1723115497,
  11329104191, 737782658, 2327685244, 299199181, 11602700446, 38472300130, 28064062908, 3289228,
  52305496401, 175785984084, 250116988265, 216998658252, 129107336131, 55384913728, 17494463507,
  4083066551, 696290469, 84344732, 6870369, 337093, 7517]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 104)`. -/
def rkmRow_m8_r104 : List ℕ := rkmRowP_m8_r104_p0 ++ rkmRowP_m8_r104_p1
/-- Prefix-kick masks for `(m = 16, r = 6)`. -/
def rkmMasks_m16_r6 : List (List Bool) := [
  [true, true, true, true], [false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 6)`. -/
def rkmRow_m16_r6 : List ℕ := [8984283, 170303409, 590731, 276242674, 37581467673, 961962395651]
/-- Mask chunk for `(m = 16, r = 28)`. -/
def rkmMkP_m16_r28_s1_p0 : List Bool := [
  true, true, true, true, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, true, false, false, true,
  true]
/-- Mask chunk for `(m = 16, r = 28)`. -/
def rkmMkP_m16_r28_s2_p0 : List Bool := [
  false, false, false, false, false, true, false, false, false, true, true, true, false, false,
  false, false, true, true, false, false, true, true, true]
/-- Mask chunk for `(m = 16, r = 28)`. -/
def rkmMkP_m16_r28_s3_p0 : List Bool := [
  false, true, true, false, true, false, false, true, true, true, false, true, false, true, false,
  true, false, true, false, true, false, false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 16, r = 28)`. -/
def rkmMasks_m16_r28 : List (List Bool) := [
  [], rkmMkP_m16_r28_s1_p0, rkmMkP_m16_r28_s2_p0, rkmMkP_m16_r28_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 28)`. -/
def rkmRow_m16_r28 : List ℕ := [
  3617, 275, 1834, 8896, 73948, 30685, 14966, 9256, 565035, 171998, 26073, 516889, 9225264,
  29760693, 92027302, 144975455, 43218370, 8478808, 1662829694, 950520744, 44705855, 4421915547,
  106546716, 889363683, 13917251371, 5025012, 39748720366, 937924011089]
/-- Prefix-kick masks for `(m = 32, r = 7)`. -/
def rkmMasks_m32_r7 : List (List Bool) := [
  [], [false, true, true], [false, false, true, false, false, true, true, true],
  [false, true, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 7)`. -/
def rkmRow_m32_r7 : List ℕ := [
  83444, 68467, 12742259, 5126865, 89012851, 27426312360, 972466644331]
/-- Mask chunk for `(m = 32, r = 16)`. -/
def rkmMkP_m32_r16_s5_p0 : List Bool := [
  false, true, false, true, false, true, true, true, true, false, true, false, true, true]
/-- Mask chunk for `(m = 32, r = 16)`. -/
def rkmMkP_m32_r16_s6_p0 : List Bool := [
  true, false, true, false, true, true, false, true, false, true, true, false, false, false, true]
/-- Prefix-kick masks for `(m = 32, r = 16)`. -/
def rkmMasks_m32_r16 : List (List Bool) := [
  [], [], [false, false, false, true],
  [true, false, true, false, true, false, false, true, true, true],
  [true, true, false, true, true, false, true, false, true, true, false, true],
  rkmMkP_m32_r16_s5_p0, rkmMkP_m32_r16_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 16)`. -/
def rkmRow_m32_r16 : List ℕ := [
  2, 94, 11335, 252614, 14224, 242730, 3457125, 2800644, 78323879, 31103690, 42093310, 117610789,
  511432300, 430776320, 17186909273, 981594971524]
/-- Mask chunk for `(m = 32, r = 80)`. -/
def rkmMkP_m32_r80_s1_p0 : List Bool := [
  true, false, true, true, false, false, false, false, false, false, false, false, false, false,
  true, true, true, true, true, true, true, false, false, false, false, true, true, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, false, false, false, false, false, true]
/-- Mask chunk for `(m = 32, r = 80)`. -/
def rkmMkP_m32_r80_s2_p0 : List Bool := [
  false, false, false, false, false, true, true, true, true, false, false, false, true, true,
  true, false, true, false, false, false, true, true, false, false, true, true, false, true, true,
  true, false, false, true, false, false, false, false, true, true, true, true, false, false,
  true, false, false, false, true, false, false, true, false, true, false, true, false, false,
  false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 32, r = 80)`. -/
def rkmMkP_m32_r80_s2_p1 : List Bool := [
  false, false, true, true, false, false, false, true, true, true]
/-- Mask chunk for `(m = 32, r = 80)`. -/
def rkmMkP_m32_r80_s3_p0 : List Bool := [
  true, false, true, true, false, false, true, false, true, true, false, false, false, false,
  true, true, true, true, true, false, false, true, true, true, true, false, true, false, true,
  false, false, true, false, false, true, true, false, false, true, false, true, false, false,
  true, true, true, false, true, true, false, true, false, false, false, true, false, false,
  false, true, false, true, false, false, true]
/-- Mask chunk for `(m = 32, r = 80)`. -/
def rkmMkP_m32_r80_s3_p1 : List Bool := [
  false, true, false, true, false, true, false, true, false, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 32, r = 80)`. -/
def rkmMasks_m32_r80 : List (List Bool) := [
  [true, true], rkmMkP_m32_r80_s1_p0, rkmMkP_m32_r80_s2_p0 ++ rkmMkP_m32_r80_s2_p1,
  rkmMkP_m32_r80_s3_p0 ++ rkmMkP_m32_r80_s3_p1, []]
/-- Row chunk `0` `(m = 32, r = 80)`. -/
def rkmRowP_m32_r80_p0 : List ℕ := [
  300425, 170669, 50982, 40597, 12294, 22545, 11, 5600, 392773, 461607, 27388, 51441, 1012723,
  1134993, 1619967, 1004768, 42499, 18030, 43198, 60, 66243, 944, 20, 486, 35710, 20495, 85689,
  25089, 57057, 53298, 209987, 60, 73123, 217288, 52603, 25140, 2132, 440190, 65568, 743713,
  295957, 1049, 446084, 316662, 3679220, 2244768, 589266, 524684, 4222627, 2579726, 44688248,
  58033656, 12196738, 8229266, 112031941, 10525022, 5878159, 49083641, 49671299, 2491568,
  267648181, 298898285, 13369710, 7995108]
/-- Row chunk `1` `(m = 32, r = 80)`. -/
def rkmRowP_m32_r80_p1 : List ℕ := [
  28772416, 599065241, 1253270153, 1196029931, 29714078, 272215339, 8094121063, 182327959,
  1582913757, 358007132, 1525492375, 1857408631, 41433635281, 7631361954, 44390629085,
  888600774881]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 80)`. -/
def rkmRow_m32_r80 : List ℕ := rkmRowP_m32_r80_p0 ++ rkmRowP_m32_r80_p1
/-- Mask chunk for `(m = 64, r = 20)`. -/
def rkmMkP_m64_r20_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, true, false, false, true,
  true, false, false, true, true]
/-- Mask chunk for `(m = 64, r = 20)`. -/
def rkmMkP_m64_r20_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, true, false, true, false, true, false,
  true, false, true]
/-- Prefix-kick masks for `(m = 64, r = 20)`. -/
def rkmMasks_m64_r20 : List (List Bool) := [rkmMkP_m64_r20_s0_p0, rkmMkP_m64_r20_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 20)`. -/
def rkmRow_m64_r20 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 30, 393, 8046, 55466, 805018, 3432742, 43617636, 87290529, 1285125305,
  68228, 10890176005, 987689420341]
/-- Mask chunk for `(m = 64, r = 40)`. -/
def rkmMkP_m64_r40_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, false, false, false, true, true, false, true, true,
  false, true, false, true, true, false, false, true, false, false, true, true]
/-- Mask chunk for `(m = 64, r = 40)`. -/
def rkmMkP_m64_r40_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, true, false, true, true, true, false, true, false, false, false,
  true, true, false, false, false, false, true, false, true]
/-- Prefix-kick masks for `(m = 64, r = 40)`. -/
def rkmMasks_m64_r40 : List (List Bool) := [rkmMkP_m64_r40_s0_p0, rkmMkP_m64_r40_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 40)`. -/
def rkmRow_m64_r40 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 29, 0, 679, 340, 5033, 7088, 989,
  41498, 1211410, 1107549, 3765572, 2132770, 150988823, 6091942, 1253074936, 9438, 5101133825,
  1563282527, 41409496655, 24119988490, 926387659339]
/-- Mask chunk for `(m = 64, r = 64)`. -/
def rkmMkP_m64_r64_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  true]
/-- Mask chunk for `(m = 64, r = 64)`. -/
def rkmMkP_m64_r64_s1_p0 : List Bool := [
  true, true, false, true, false, true, true, false, false, false, true, false, false, false,
  true, false, true, false, false, true, true, true, true, true, true, true, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, false, true,
  true, false, false, true, false, true]
/-- Mask chunk for `(m = 64, r = 64)`. -/
def rkmMkP_m64_r64_s2_p0 : List Bool := [
  true, true, false, true, false, false, false, false, false, false, false, true, false, false,
  true, false, false, true, true, false, true, true, false, false, true, true, false, false,
  false, false, true, true, true, false, false, true, true, true, false, false, false, false,
  true, true, true, true, true, true, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true]
/-- Mask chunk for `(m = 64, r = 64)`. -/
def rkmMkP_m64_r64_s2_p1 : List Bool := [true]
/-- Mask chunk for `(m = 64, r = 64)`. -/
def rkmMkP_m64_r64_s3_p0 : List Bool := [
  false, false, true, false, true, true, false, false, true, true, false, false, true, false,
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, true,
  false, true, true, false, true, true, false, true, false, false, true, true, false, false, true,
  true, true, true, true]
/-- Mask chunk for `(m = 64, r = 64)`. -/
def rkmMkP_m64_r64_s4_p0 : List Bool := [
  false, false, false, true, false, false, false, true, true, false, false, false, true, false,
  false, false, false, true, false, false, false, false, false, true, false, false, false, false,
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, false, true, true, true, false, true, true, false, true, false, true,
  false, false, false, true, true]
/-- Mask chunk for `(m = 64, r = 64)`. -/
def rkmMkP_m64_r64_s5_p0 : List Bool := [
  false, false, false, false, false, true, true, true, false, false, false, true, true, false,
  false, false, false, false, false, false, false, false, true, true, false, false, false, false,
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, true, true, false,
  true, true, true, false, true, true, true]
/-- Mask chunk for `(m = 64, r = 64)`. -/
def rkmMkP_m64_r64_s6_p0 : List Bool := [
  false, false, false, false, false, true, true, true, false, false, false, false, false, true,
  true, false, true, true, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 64, r = 64)`. -/
def rkmMasks_m64_r64 : List (List Bool) := [
  rkmMkP_m64_r64_s0_p0, rkmMkP_m64_r64_s1_p0, rkmMkP_m64_r64_s2_p0 ++ rkmMkP_m64_r64_s2_p1,
  rkmMkP_m64_r64_s3_p0, rkmMkP_m64_r64_s4_p0, rkmMkP_m64_r64_s5_p0, rkmMkP_m64_r64_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 64)`. -/
def rkmRow_m64_r64 : List ℕ := [
  294397, 354354, 6463713, 22095499, 354392, 151653, 3449771, 70034, 945592, 4209247, 38050,
  208363, 2187667, 670878, 2992961, 3717108, 361636, 223337, 173328, 1172724, 80182, 366125,
  341541, 7859085, 116291, 5553138, 3724274, 3780974, 2005295, 6932176, 44, 13317, 105388,
  1399893, 781514, 207807, 98967, 7644404, 8431415, 848634, 2821839, 1350, 273335, 53172972,
  2384285, 14604221, 24496723, 1319965, 101557787, 156298234, 936211, 111311135, 11955392,
  9997743, 2024487537, 620518436, 1630273723, 8198908, 1695627210, 3565612013, 4209343150,
  2694531012, 18756323130, 964203395595]
/-- Prefix-kick masks for `(m = 128, r = 8)`. -/
def rkmMasks_m128_r8 : List (List Bool) := [
  [false, false, false, true, true, true],
  [false, false, true, false, true, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 8)`. -/
def rkmRow_m128_r8 : List ℕ := [0, 73, 3330, 274938, 3039, 1305821, 20430791233, 979567621473]
/-- Prefix-kick masks for `(m = 128, r = 11)`. -/
def rkmMasks_m128_r11 : List (List Bool) := [
  [], [true, false, false, false, true, true, false, false, false, true, true, true],
  [false, false, false, false, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 11)`. -/
def rkmRow_m128_r11 : List ℕ := [
  0, 0, 0, 2, 978, 17462, 1120987, 113857, 12669295, 15162254307, 984823822965]
/-- Prefix-kick masks for `(m = 256, r = 26)`. -/
def rkmMasks_m256_r26 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 26)`. -/
def rkmRow_m256_r26 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 40, 2476, 30663, 1590668, 17048337,
  1048723741, 6590199720, 992342403698]
/-- Mask chunk for `(m = 256, r = 32)`. -/
def rkmMkP_m256_r32_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, true, true, false, false, false, true, true, false, true,
  true]
/-- Mask chunk for `(m = 256, r = 32)`. -/
def rkmMkP_m256_r32_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, true, false, true, false, false, true, false,
  true, true, true]
/-- Mask chunk for `(m = 256, r = 32)`. -/
def rkmMkP_m256_r32_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, true, false,
  false, false, true, true]
/-- Mask chunk for `(m = 256, r = 32)`. -/
def rkmMkP_m256_r32_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true]
/-- Prefix-kick masks for `(m = 256, r = 32)`. -/
def rkmMasks_m256_r32 : List (List Bool) := [
  [], rkmMkP_m256_r32_s1_p0, rkmMkP_m256_r32_s2_p0, rkmMkP_m256_r32_s3_p0, rkmMkP_m256_r32_s4_p0,
  []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 32)`. -/
def rkmRow_m256_r32 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 175, 788, 65273, 745567,
  7408174, 5010521, 4665247, 13264071, 5418301346, 994550537866]
/-- Prefix-kick masks for `(m = 512, r = 11)`. -/
def rkmMasks_m512_r11 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 11)`. -/
def rkmRow_m512_r11 : List ℕ := [
  0, 0, 0, 0, 0, 6, 2402, 528008, 5661574, 14221531906, 985772275906]
/-- Mask chunk for `(m = 512, r = 16)`. -/
def rkmMkP_m512_r16_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, true]
/-- Mask chunk for `(m = 512, r = 16)`. -/
def rkmMkP_m512_r16_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, false, false, false, false,
  true]
/-- Prefix-kick masks for `(m = 512, r = 16)`. -/
def rkmMasks_m512_r16 : List (List Bool) := [[], rkmMkP_m512_r16_s1_p0, rkmMkP_m512_r16_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 16)`. -/
def rkmRow_m512_r16 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 60, 3, 1938765, 2238877, 9737050656, 990258771211]
/-- Mask chunk for `(m = 512, r = 21)`. -/
def rkmMkP_m512_r21_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true]
/-- Mask chunk for `(m = 512, r = 21)`. -/
def rkmMkP_m512_r21_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 512, r = 21)`. -/
def rkmMasks_m512_r21 : List (List Bool) := [rkmMkP_m512_r21_s0_p0, rkmMkP_m512_r21_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 21)`. -/
def rkmRow_m512_r21 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 45, 2225, 26727, 927, 3184973, 15700501, 7611720859,
  992369363075]
/-- Mask chunk for `(m = 512, r = 26)`. -/
def rkmMkP_m512_r26_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 512, r = 26)`. -/
def rkmMkP_m512_r26_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, false, true, true]
/-- Mask chunk for `(m = 512, r = 26)`. -/
def rkmMkP_m512_r26_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, true]
/-- Prefix-kick masks for `(m = 512, r = 26)`. -/
def rkmMasks_m512_r26 : List (List Bool) := [
  rkmMkP_m512_r26_s0_p0, rkmMkP_m512_r26_s1_p0, rkmMkP_m512_r26_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 26)`. -/
def rkmRow_m512_r26 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 134, 72632, 3897, 8805177, 9157248,
  6236024796, 993745935114]
/-- Prefix-kick masks for `(m = 1024, r = 5)`. -/
def rkmMasks_m1024_r5 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 5)`. -/
def rkmRow_m1024_r5 : List ℕ := [2637, 1536431, 341905353, 31157278835, 968499276663]
/-- Prefix-kick masks for `(m = 1024, r = 13)`. -/
def rkmMasks_m1024_r13 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 13)`. -/
def rkmRow_m1024_r13 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 799, 72259, 14570363, 11902823832, 988082532370]
/-- Prefix-kick masks for `(m = 1024, r = 16)`. -/
def rkmMasks_m1024_r16 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 16)`. -/
def rkmRow_m1024_r16 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 727, 237365, 1684749, 9689046160, 990309030493]
/-- Prefix-kick masks for `(m = 1024, r = 20)`. -/
def rkmMasks_m1024_r20 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 20)`. -/
def rkmRow_m1024_r20 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 230, 489802, 1957841, 7766948248, 992230603109]
/-- Mask chunk for `(m = 1024, r = 23)`. -/
def rkmMkP_m1024_r23_s0_p0 : List Bool := [
  false, false, true, true, true, false, false, true, true, true, false, false, true, true, false,
  false, true, true, true, true]
/-- Prefix-kick masks for `(m = 1024, r = 23)`. -/
def rkmMasks_m1024_r23 : List (List Bool) := [rkmMkP_m1024_r23_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 23)`. -/
def rkmRow_m1024_r23 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 227, 8829, 639009, 9757674, 6778307629,
  993211285586]
/-- Mask chunk for `(m = 1024, r = 25)`. -/
def rkmMkP_m1024_r25_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true, true]
/-- Prefix-kick masks for `(m = 1024, r = 25)`. -/
def rkmMasks_m1024_r25 : List (List Bool) := [rkmMkP_m1024_r25_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 25)`. -/
def rkmRow_m1024_r25 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 17, 2, 28483, 725154, 17616499,
  6236088676, 993745539989]
/-- Unpacks `j` LSB-first bits of `< 2 ^ 50` word `w` (`FindAllJohnsonRampKickMuxTraj10`). -/
def rkmWbTraj10 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWbTraj10 j (Nat.div w 2)
/-- Concatenates `50`-bit `< 2 ^ 50` chunks (final length `rem`) into a `List Bool` mask. -/
def rkmMaskWordsTraj10 : ℕ → List ℕ → List Bool
  | _, [] => []
  | rem, [w] => rkmWbTraj10 rem w
  | rem, w :: v :: ws => rkmWbTraj10 50 w ++ rkmMaskWordsTraj10 rem (v :: ws)
/-- Krotov masks `(m = 4, r = 96)`. -/
def rkmMasksPack_m4_r96 : List (List Bool) := [[], [], rkmWbTraj10 3 7,
  rkmMaskWordsTraj10 5 [6597070783235, 23], rkmMaskWordsTraj10 34 [132461700407701, 13831110656],
  rkmMaskWordsTraj10 45 [441290487827012, 22832047069414],
  rkmMaskWordsTraj10 35 [88258576204881, 30468543825], []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 96)`. -/
def rkmRowPack_m4_r96 : List ℕ := [62915, 880896, 334224, 46983, 56526, 1503, 1702263, 4099982,
  1542061, 650918, 3004469, 1570871, 5885429, 3279819, 5148, 66438, 1651971, 116599, 801531,
  3434520, 69894, 189519, 530425, 2587896, 17923152, 4388263, 2010201, 4141944, 18953193, 10291876,
  23801429, 30120695, 64330461, 84214908, 18299411, 1760933, 12080578, 12383735, 44906940,
  11360785, 1062288, 110906703, 89963249, 6230971, 9852040, 5488656, 122669404, 191419837, 9949809,
  2121305, 16344557, 204688426, 78845398, 2004312, 79557365, 316110523, 914731, 81860809,
  248564306, 386593, 143621268, 719548650, 1358957, 1041678819, 40299847, 338233944, 531948,
  1147115, 8343957, 10208093, 209705239, 694340120, 5185199, 3484400, 624965988, 73979837,
  2177118539, 1718070494, 1190433200, 2313590727, 81748022, 429594013, 400305618, 875367214,
  9146616257, 7793617413, 106362343, 1069047544, 16232778266, 145276132844, 304516760246,
  294013024067, 154190659001, 45203536289, 6941640398, 433525055]
/-- Krotov masks `(m = 32, r = 4)`. -/
def rkmMasksPack_m32_r4 : List (List Bool) := [rkmWbTraj10 2 3, rkmWbTraj10 3 7, rkmWbTraj10 3 5,
  rkmWbTraj10 5 27, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 4)`. -/
def rkmRowPack_m32_r4 : List ℕ := [47597, 66880, 43647993245, 956351241359]
/-- Krotov masks `(m = 32, r = 80)`. -/
def rkmMasksPack_m32_r80 : List (List Bool) := [rkmWbTraj10 1 1, rkmWbTraj10 22 3145727,
  rkmMaskWordsTraj10 24 [664431906136113, 14891369],
  rkmMaskWordsTraj10 28 [931649505633313, 155886932], []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 80)`. -/
def rkmRowPack_m32_r80 : List ℕ := [10, 7, 119, 42, 0, 0, 16, 13, 30, 114, 9, 0, 103, 178, 20, 109,
  36, 16, 3, 300, 14, 82, 343, 0, 42, 9, 78, 0, 15, 10, 1, 117, 277, 353, 3570, 4961, 8843, 11731,
  560, 36736, 214399, 230398, 2675, 695708, 1453468, 929550, 20889, 2371137, 773797, 4366222,
  412914, 6637841, 2458897, 634414, 1270296, 229365, 57479, 20304335, 1339654, 2060502, 2929586,
  29443971, 235553917, 304637636, 45437821, 118985, 392208927, 125781064, 4562222570, 198086742,
  270533514, 2168259937, 533996891, 8209301740, 7255039778, 200022120, 23442219481, 11782201727,
  22878952461, 917316513254]
/-- Krotov masks `(m = 4, r = 60)`. -/
def rkmMasksPack_m4_r60 : List (List Bool) := [[], [], [], [], rkmWbTraj10 2 3, rkmWbTraj10 4 10,
  rkmWbTraj10 4 9, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 60)`. -/
def rkmRowPack_m4_r60 : List ℕ := [87670798, 5917326844, 145881865782, 848112688806]
/-- Krotov masks `(m = 64, r = 59)`. -/
def rkmMasksPack_m64_r59 : List (List Bool) := [[], rkmWbTraj10 5 24, rkmWbTraj10 26 60584422,
  rkmWbTraj10 48 265599059122468, rkmMaskWordsTraj10 4 [447323259905369, 14],
  rkmMaskWordsTraj10 7 [759533060410197, 100], rkmMaskWordsTraj10 8 [317781778367648, 130], []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 59)`. -/
def rkmRowPack_m64_r59 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 67, 0, 118, 446, 1053, 334, 4304, 3102, 18074, 121522,
  5045, 1374552, 1637874, 170507, 19438145, 2734009, 4991774, 99916089, 4666518, 195381007,
  978396792, 61706562, 9507954653, 989121475136]
/-- Krotov masks `(m = 8, r = 4)`. -/
def rkmMasksPack_m8_r4 : List (List Bool) := [[], [], [], rkmWbTraj10 1 1, rkmWbTraj10 2 2,
  rkmWbTraj10 3 4, rkmWbTraj10 3 4, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 4)`. -/
def rkmRowPack_m8_r4 : List ℕ := [48326, 110475216, 64972975490, 934916464154]
/-- Krotov masks `(m = 32, r = 53)`. -/
def rkmMasksPack_m32_r53 : List (List Bool) := [[], rkmWbTraj10 7 99, rkmWbTraj10 36 64886683878,
  rkmWbTraj10 44 15613739849730, rkmWbTraj10 48 226111595563268,
  rkmMaskWordsTraj10 1 [662535560057128, 1], rkmMaskWordsTraj10 2 [35846227710098, 2], []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 53)`. -/
def rkmRowPack_m32_r53 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 7, 1, 20, 149, 45, 518, 79, 168, 3059, 413, 634, 28337, 1914, 16930, 20346, 901300, 190196,
  2817291, 1209084, 21374311, 26834206, 712978, 42538212, 160345561, 16696942, 323436296,
  1935445235, 111170737, 19178215531, 978178037775]
/-- Krotov masks `(m = 8, r = 7)`. -/
def rkmMasksPack_m8_r7 : List (List Bool) := [[], []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 7)`. -/
def rkmRowPack_m8_r7 : List ℕ := [79406547, 18137771, 3803797903, 4384071160, 53487627970,
  91972264719, 846254434332]
/-- Krotov masks `(m = 32, r = 44)`. -/
def rkmMasksPack_m32_r44 : List (List Bool) := [rkmWbTraj10 31 1086324736,
  rkmWbTraj10 43 8787503087979, rkmWbTraj10 43 7038736101626, rkmWbTraj10 41 1645237180928, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 44)`. -/
def rkmRowPack_m32_r44 : List ℕ := [101588, 127838, 2841850, 546591, 58664, 1358643, 3948038,
  3054959, 3556494, 4522383, 274945, 673109, 185418, 1612385, 490261, 3547470, 3035127, 1681048,
  443269, 1810084, 29021, 799321, 4706219, 2201275, 319573, 1382235, 232115, 2692542, 2015141, 331,
  9932, 27982303, 26748298, 49696714, 227584970, 171873422, 816749112, 5803460, 4002106609,
  98041358, 15220442532, 5965750842, 17811907972, 955527053067]
/-- Krotov masks `(m = 4, r = 8)`. -/
def rkmMasksPack_m4_r8 : List (List Bool) := [[], [], [], [], rkmWbTraj10 4 13, rkmWbTraj10 6 54,
  rkmWbTraj10 7 68, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 8)`. -/
def rkmRowPack_m4_r8 : List ℕ := [92216718, 84448870, 89031343, 2332237506, 3067096885, 283651182,
  165223967939, 828825851702]
/-- Krotov masks `(m = 32, r = 35)`. -/
def rkmMasksPack_m32_r35 : List (List Bool) := [rkmWbTraj10 30 805306425, rkmWbTraj10 30 968055463,
  rkmWbTraj10 33 7359589566, rkmWbTraj10 34 8740855616, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 35)`. -/
def rkmRowPack_m32_r35 : List ℕ := [45, 41, 35, 54, 1, 149, 228, 481, 2186, 558, 1196, 2, 6334,
  3021, 26650, 93716, 9529, 90495, 820250, 1859575, 241118, 2864638, 4111516, 373047, 10573002,
  661176397, 56863228, 2404811746, 1400537155, 43884182, 1622857978, 4093994429, 52445370,
  18810375662, 970831975206]
/-- Krotov masks `(m = 16, r = 8)`. -/
def rkmMasksPack_m16_r8 : List (List Bool) := [[], [], rkmWbTraj10 3 6, rkmWbTraj10 5 27,
  rkmWbTraj10 6 34, rkmWbTraj10 7 68, rkmWbTraj10 7 65, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 8)`. -/
def rkmRowPack_m16_r8 : List ℕ := [649267, 1194763, 860367, 24794069, 21009555, 129314646,
  34993133718, 964829040149]
/-- Krotov masks `(m = 4, r = 112)`. -/
def rkmMasksPack_m4_r112 : List (List Bool) := [[], [], rkmWbTraj10 30 615243811,
  rkmWbTraj10 49 281474997944325, rkmWbTraj10 31 1146355776,
  rkmMaskWordsTraj10 15 [357892096, 16384], rkmWbTraj10 31 1677787400, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 112)`. -/
def rkmRowPack_m4_r112 : List ℕ := [2533952388, 1615888418, 260296643, 129590325, 62088247,
  2731429632, 302666250, 2807975356, 21633784303, 233335505, 27551235519, 24509114894, 76639210959,
  167227802777, 475602082744, 195235348619, 836476417, 85217349, 181454, 12919, 162, 1638, 303,
  164, 55, 13, 70, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
/-- Krotov masks `(m = 2, r = 14)`. -/
def rkmMasksPack_m2_r14 : List (List Bool) := [[], [], rkmWbTraj10 3 4, []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 14)`. -/
def rkmRowPack_m2_r14 : List ℕ := [43840124, 34653921, 980751, 162928246, 294140172, 837470096,
  4956970729, 995740220, 35069949161, 3917434264, 137610430227, 453184442676, 308458726390,
  54415054363]
/-- Krotov masks `(m = 4, r = 40)`. -/
def rkmMasksPack_m4_r40 : List (List Bool) := [[], [], [], rkmWbTraj10 30 805313664,
  rkmWbTraj10 31 2121468005, rkmWbTraj10 16 36355, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 40)`. -/
def rkmRowPack_m4_r40 : List ℕ := [10985890, 279912, 11024393, 173714, 10463705, 2859714, 5936033,
  4053296, 16286737, 12164716, 10481169, 954014, 147913817, 4698058, 3787787, 4975100, 76079444,
  10396402, 240267434, 247230, 95876649, 500069149, 44799733, 872985706, 590887095, 8232982,
  793909791, 16537275418, 537774651, 14029632166, 2223517422, 2466650185, 68562190675,
  251279468875, 330163121436, 215397659811, 77823793314, 15762527534, 1663308710, 70547563]
/-- Krotov masks `(m = 64, r = 12)`. -/
def rkmMasksPack_m64_r12 : List (List Bool) := [rkmWbTraj10 10 920, rkmWbTraj10 11 1192, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 12)`. -/
def rkmRowPack_m64_r12 : List ℕ := [0, 0, 0, 102, 1173, 112073, 847445, 16399002, 9597216,
  71030329, 15496181435, 984405831084]
/-- Krotov masks `(m = 16, r = 29)`. -/
def rkmMasksPack_m16_r29 : List (List Bool) := [[], rkmWbTraj10 27 107373996,
  rkmWbTraj10 28 156587673, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 29)`. -/
def rkmRowPack_m16_r29 : List ℕ := [121, 138, 1, 20, 41, 252, 7, 3028, 351, 86, 648, 25155, 272336,
  1100339, 5899549, 13894195, 60502471, 98792765, 400520790, 456870102, 1850302648, 1295143871,
  5015775711, 2694957175, 467184142, 19417206223, 6478913, 39835935212, 928379132986]
/-- Krotov masks `(m = 4, r = 13)`. -/
def rkmMasksPack_m4_r13 : List (List Bool) := [[], [], rkmWbTraj10 7 116, rkmWbTraj10 10 805,
  rkmWbTraj10 11 1041, rkmWbTraj10 12 2297, rkmWbTraj10 12 2532, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 13)`. -/
def rkmRowPack_m4_r13 : List ℕ := [2187440, 1668755, 268299655, 112248771, 3186540, 1397192887,
  649481705, 2103816, 3689999110, 3805132298, 23285856, 167443490907, 822600425600]
/-- Krotov masks `(m = 16, r = 25)`. -/
def rkmMasksPack_m16_r25 : List (List Bool) := [[], rkmWbTraj10 22 3356257, rkmWbTraj10 24 9743061,
  []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 25)`. -/
def rkmRowPack_m16_r25 : List ℕ := [0, 5, 12258, 2724, 281009, 671836, 151365, 0, 121171, 2708209,
  16125032, 66070445, 173269096, 440738565, 558627289, 1581358130, 784036354, 7825449, 558474471,
  2979610185, 8638968107, 13719292735, 152809519, 52136258830, 918182586748]
/-- Krotov masks `(m = 2, r = 16)`. -/
def rkmMasksPack_m2_r16 : List (List Bool) := [[], [], [], rkmWbTraj10 7 112, rkmWbTraj10 10 805,
  rkmWbTraj10 12 3320, rkmWbTraj10 9 500, []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 16)`. -/
def rkmRowPack_m2_r16 : List ℕ := [993864, 64854, 376611016, 44932506, 129360063, 157531882,
  338373950, 63829860, 4423155637, 5745066951, 1146169665, 2527104208, 72207367346, 445509316074,
  390625917342, 76703210717]
/-- Krotov masks `(m = 16, r = 22)`. -/
def rkmMasksPack_m16_r22 : List (List Bool) := [[], rkmWbTraj10 17 127796, rkmWbTraj10 20 898388,
  rkmWbTraj10 21 1068368, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 22)`. -/
def rkmRowPack_m16_r22 : List ℕ := [4, 57, 353, 3750, 25277, 127414, 292021, 6123, 6422363,
  3994090, 806522, 41172098, 458465336, 9003654, 113072806, 1087044499, 409595004, 2016456718,
  8247094798, 102703858, 42344463811, 945159249081]
/-- Krotov masks `(m = 16, r = 80)`. -/
def rkmMasksPack_m16_r80 : List (List Bool) := [rkmWbTraj10 9 511, rkmWbTraj10 13 8191, [],
  rkmWbTraj10 1 1, rkmWbTraj10 7 116, rkmWbTraj10 11 1796, rkmWbTraj10 13 7973, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 80)`. -/
def rkmRowPack_m16_r80 : List ℕ := [11871, 6771, 5633, 165931, 29470, 41091, 150394, 61226, 351795,
  2069596, 38453, 10097938, 213808306, 2201281278, 158305180892, 839266688495]
/-- Krotov masks `(m = 2, r = 24)`. -/
def rkmMasksPack_m2_r24 : List (List Bool) := [[], [], [], rkmWbTraj10 4 12,
  rkmWbTraj10 24 14679842, rkmWbTraj10 19 475033, rkmWbTraj10 17 88316, []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 24)`. -/
def rkmRowPack_m2_r24 : List ℕ := [13898824, 448747, 4878640, 44406763, 1164841, 32104808,
  56780403, 121322782, 13709048, 125836495, 279094699, 186611073, 2439046220, 618704652,
  3387364091, 1669027765, 16805422, 19844061210, 3309719704, 33152696, 92598092398, 425820108820,
  369315341590, 80060818671]
/-- Krotov masks `(m = 16, r = 17)`. -/
def rkmMasksPack_m16_r17 : List (List Bool) := [rkmWbTraj10 1 1, rkmWbTraj10 14 14224,
  rkmWbTraj10 16 53866, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 17)`. -/
def rkmRowPack_m16_r17 : List ℕ := [1289, 30373, 30622, 2407718, 17621, 262180, 9288214, 11208585,
  94520, 1600884641, 34593345, 1338252147, 7862871420, 2959853531, 676054620, 37738836364,
  947765312522]
/-- Cumulative `2`-lane trajectory head invariant (`Traj08` -> `Traj10`). -/
def rkmTrajLaneProp_10 : Prop :=
  rkmTrajLaneProp_08 ∧ (rkmRow_m2_r22.head? = some 41702376)
/-- Proof of `rkmTrajLaneProp_10` in `O(1)` kernel steps. -/
theorem rkmTrajLaneOk_10 : rkmTrajLaneProp_10 :=
  ⟨rkmTrajLaneOk_08, rfl⟩
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
private def wc_rkmTraj_m8_r104_s5_hb_p0 : List ℕ := [163223753297517,229001787092807,
  278224874951187,318674422849297,353389792141735,383942130749716,411271975692954,435996773331329,
  458548592133437,479244321254993,498324911243886,515978886165753,532357217806920,547583156060464,
  561758964153652,574970674779813,587291536154351,598784564798082,609504473445862,619499151942031,
  628810821986752,637476949709468,645530975581098,653002904593185,659919788168483,666306121201339,
  672184171858682,677574257587560,682494977697592,686963410595314,690995282021774,694605109331442,
  697806325841073,700611388494265,703031871474949,705078547920039,706761461497680,708089989310385,
  709072897334861,709718389409664,710034150618019,710027385778718,709704853646968,709072897334861,
  708137471384068,706904165858611,705378227770788,703564580106694,701467838677800,699092326990459,
  696442089295078,693520901950093,690332283212192,686879501542772,683165582500926,679193314274808,
  674965251885637,670483720081445,665750814920512,660768404026969,655538125482731,650061385300352,
  644339353400084,638372957990688]
private def wc_rkmTraj_m8_r104_s5_hb_p1 : List ℕ := [632162878226752,625709534984551,
  619013079562804,612073380072808,604890005232732,597462205221403,589788889175227,581868598824617,
  573699477659549,565279234882008,556605103239327,547673789627321,538481417093429,529023456541146,
  519294646015369,509288894902975,498999169671287,488417356828910,477534097543726,466338586668753,
  454818326629171,442958823447100,430743207723513,418151757041338,405161287030463,391744364684804,
  377868276873316,363493654980382,348572605610018,333046113425125,316840339219234,299861182110630,
  281985999823302,263050439504175,242826324573455,220981857019934,197003075838446,170017418717713,
  138310230832527,97422842467454]
private def wc_rkmTraj_m8_r104_s5_hb : List ℕ := pCat wc_rkmTraj_m8_r104_s5_hb_p0
  wc_rkmTraj_m8_r104_s5_hb_p1
private def wc_rkmTraj_m8_r104_s5_v0_p0 : List ℕ := [2000000001020179,1999999999897940,
  2000000014575470,2000000032700743,2000000117482756,2000000273637966,2000000549912528,
  2000000924143780,2000001239763893,2000001286111007,2000000881475279,2000000071390463,
  1999999272996578,1999999032700420,1999999549457411,2000000413828216,2000000861697496,
  2000000465202354,1999999629818421,1999999213820144,1999999567556065,2000000176710283,
  2000000451018978,2000000620880415,2000001329101801,2000002323358469,2000002605725605,
  2000002874428909,2000006265094278,2000012468333923,2000009980839895,1999983189205112,
  1999942155632829,1999945548867880,2000060254149239,2000247518485190,2000283607185548,
  1999889004114514,1999099086113786,1998585940624944,1999439590077145,2002194713026204,
  2005628062721772,2006477246304218,2001007998427211,1988121355970431,1972218178500701,
  1963553107964056,1974968031291339,2016110651142025,2088029922366596,2181120210372393,
  2277657558784433,2357750307676896,2405898211921074,2415357478148272,2388900151822949,
  2336354560803267,2270533585124019,2203364261017424,2143422664022604,2095182333293811,
  2059584962233307,2035254022416112]
private def wc_rkmTraj_m8_r104_s5_v0_p1 : List ℕ := [2019745543829887,2010483156661797,
  2005281428054910,2002527183711737,2001149388115497,2000497161157905,2000204611255462,
  2000080152219300,2000029892483335,2000010615332156,2000003589677260,2000001155884506,
  2000000354372944,2000000103420541,2000000028722960,2000000007588676,2000000001906406,
  2000000000455129,2000000000103187,2000000000022197,2000000000004524,2000000000000869,
  2000000000000156,2000000000000024,2000000000000002,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def wc_rkmTraj_m8_r104_s5_v0 : List ℕ := pCat wc_rkmTraj_m8_r104_s5_v0_p0
  wc_rkmTraj_m8_r104_s5_v0_p1
private def wc_rkmTraj_m8_r104_s5_v1_p0 : List ℕ := [2000000000485096,2000000001702480,
  2000000003702745,2000000005490343,2000000005258027,2000000002045443,1999999997594713,
  1999999995689012,1999999998321846,2000000002653534,2000000003538211,1999999999878685,
  1999999996571057,1999999998175581,2000000002321677,2000000002858566,1999999999027904,
  1999999996828240,1999999999813430,2000000003506804,2000000002377682,1999999997328308,
  1999999990464299,1999999978576723,1999999967093269,1999999997740452,2000000150991570,
  2000000495748411,2000001007078028,2000001511037757,2000001714610799,2000001346052048,
  2000000381413900,1999999252632487,1999998798806553,1999999668292436,2000001303379550,
  2000001648481628,1999999075218885,1999995723676080,1999997511464086,2000006771684340,
  2000013527630726,2000001256330860,1999972034535435,1999963080497970,2000013689626436,
  2000093936750469,2000088871151794,1999920018819557,1999717316036453,1999791633501281,
  2000283288795731,2000790003221691,2000542162331018,1999268680779021,1997972819219628,
  1998454298845249,2001424790331389,2004847032614503,2004734948577142,1998771586408119,
  1989951732543429,1986204933166587]
private def wc_rkmTraj_m8_r104_s5_v1_p1 : List ℕ := [1994654890976201,2014166507151261,
  2032661370106781,2033114936009975,2005556432265671,1956994182733727,1911624757142211,
  1899961067491535,1942983852981089,2040652006746441,2171114844850736,2300326088720584,
  2396142513556920,2439623218928172,2429062682192177,2376741579004225,2301646138312852,
  2222157191899514,2151391615352320,2095856704757900,2056557961260587,2031160159444498,
  2016051807423124,2007737555814385,2003491104857121,2001474108205940,2000582160047743,
  2000214807210023,2000073941783884,2000023696082317,2000007051000065,2000001941455264,
  2000000492502029,2000000114458994,2000000024191479,2000000004604407,2000000000778482,
  2000000000114595,2000000000014219,2000000000001398,2000000000000091]
private def wc_rkmTraj_m8_r104_s5_v1 : List ℕ := pCat wc_rkmTraj_m8_r104_s5_v1_p0
  wc_rkmTraj_m8_r104_s5_v1_p1
private def wc_rkmTraj_m8_r104_s5_v2_p0 : List ℕ := [2000000000000004,2000000000000006,
  2000000000000007,2000000000000001,2000000000000004,2000000000000001,2000000000000002,
  2000000000000005,1999999999999992,1999999999999894,1999999999999533,1999999999998907,
  2000000000000819,2000000000020356,2000000000107728,2000000000382738,2000000001049210,
  2000000002316160,2000000004159715,2000000006005505,2000000006671562,2000000004993310,
  2000000001047279,1999999996917253,1999999995618151,1999999998304068,2000000002411231,
  2000000003638832,2000000000668648,1999999997114366,1999999997309441,2000000000777333,
  2000000003204713,2000000002341748,1999999998983875,1999999993504396,1999999990825471,
  2000000005884323,2000000036116264,2000000024771364,1999999928011356,1999999870155761,
  2000000059934429,2000000326985580,2000000058234753,1999999324766353,1999999664985431,
  2000001715991453,2000001915788298,1999996375799816,1999991348292741,2000000903121261,
  2000021131440370,2000017589608863,1999972762918951,1999945533957159,2000014559172054,
  2000119709152958,2000064184049612,1999821138340537,1999741460865896,2000130243180461,
  2000573218439991,2000218491139737]
private def wc_rkmTraj_m8_r104_s5_v2_p1 : List ℕ := [1999158481159609,1998938143633115,
  2000582836502606,2002295273571088,2000961579291479,1997010320157233,1995789667042885,
  2001078361004439,2007755553363324,2005569287387021,1993158536992591,1984571282371331,
  1994906189362869,2018281221020259,2027406596138265,2002970323395096,1962537491693391,
  1951055794086847,1994688583213491,2064591894494332,2093709761698409,2037031428205514,
  1919541295931269,1825477897289897,1836940684192061,1974050685922786,2183050953497199,
  2375057241331446,2480211773001291,2479046847657149,2398173591174008,2283934927880189,
  2176190307835388,2095733096656568,2045583589573975,2018946199152678,2006811090003130,
  2002083111183538,2000526452179302,2000103921267941,2000013906605340]
private def wc_rkmTraj_m8_r104_s5_v2 : List ℕ := pCat wc_rkmTraj_m8_r104_s5_v2_p0
  wc_rkmTraj_m8_r104_s5_v2_p1
private def wc_rkmTraj_m32_r80_s2_hb_p0 : List ℕ := [180913603768777,253251280785186,
  306983086096862,350793559514161,388082346336294,420610450596176,449434121771457,475248062700450,
  498539268856756,519665519218791,538899291608379,556454098792361,572501163442237,587180447829338,
  600608216852901,612882382871748,624086381152813,634292042710746,643561765279122,651950181813613,
  659505462097473,666270341689718,672282945032046,677577450931364,682184635770805,686132320745513,
  689445742939673,692147865356205,694259637547454,695800215914103,696787150793040,697236545970873,
  697163195116325,696580698734809,695501564548900,693937293652996,691898454344755,689394745174332,
  686435048455254,683027475233154,679179402498464,674897503247351,670187769833763,665055530907956,
  659505462097473,653541590449701,647167292515619,640385285806270,633197613190722,625605619619186,
  617609920338537,609210359508267,600405957807983,591194847233399,581574190780123,571540084077555,
  561087435209662,550209817876097,538899291608379,527146180820663,514938801837661,502263123398438,
  489102341023860,475436338348850]
private def wc_rkmTraj_m32_r80_s2_hb_p1 : List ℕ := [461240997945695,446487308512254,
  431140191619444,415156934501525,398485056865418,381059343472911,362797610178150,343594479337647,
  323311895336935,301764030052449,278691923654187,253717824902883,226255047459702,195305405378492,
  158903986287339,111934581529574]
private def wc_rkmTraj_m32_r80_s2_hb : List ℕ := pCat wc_rkmTraj_m32_r80_s2_hb_p0
  wc_rkmTraj_m32_r80_s2_hb_p1
private def wc_rkmTraj_m32_r80_s2_v0_p0 : List ℕ := [1999997999607340,2000008795222910,
  1999973278674029,1999935316284258,2000132081676175,2000234411590069,2000367843765611,
  2000515251081661,2000646446329992,2000724086768858,2000714211259906,2000597868290928,
  2000379239904100,2000086717189569,2000233800703635,2000530990295989,2000761177967449,
  2000898011675077,2000936138922280,2000888879884272,2000781997011913,1999354070706625,
  1999494341732229,1999640991283472,1999879051631027,1999500440255172,1997785355650894,
  2006437521791862,2015500830211606,2032580539300597,2061074569016655,2103353891239737,
  2159164321492619,2224348060932045,2290694455084626,2347405001948928,2383927524704993,
  2393152330961310,2373646046641285,2329971408330344,2271019028531097,2207157825220297,
  2147415206142658,2097674694834225,2060253518888783,2034594626074030,2018476863352906,
  2009172906164428,2004228650981154,2001807803809002,2000715584598737,2000261748923857,
  2000088267315989,2000027363485304,2000007771527953,2000002013670798,1999999526429298,
  1999999899559297,2000000019055261,2000000003199264,2000000000468460,2000000000058574,
  2000000000006047,1999999999999518]
private def wc_rkmTraj_m32_r80_s2_v0_p1 : List ℕ := [2000000000000024]
private def wc_rkmTraj_m32_r80_s2_v0 : List ℕ := pCat wc_rkmTraj_m32_r80_s2_v0_p0
  wc_rkmTraj_m32_r80_s2_v0_p1
private def wc_rkmTraj_m32_r80_s2_v1_p0 : List ℕ := [2000070222961747,1999960351511351,
  1999896648751738,2000484940680920,1999102165792091,2001083910711379,1999522149643170,
  1999580697370889,2000834529392568,1999595372541528,1999583398329547,2000612381933075,
  1999836993032112,1999507773969515,2000486478224030,2000250878502392,1999471234642847,
  2000069384294264,2000536851306160,1999723706137812,1999499670479209,2000404918263973,
  2000436051801319,1999394681520303,1999360996895666,2000520990083060,2000785842731303,
  1999686902490474,1999152499291559,2000099237628650,2001012544919079,2000584967969895,
  1999713175615321,1999912169062386,2001011453151431,2001541906986543,2000835790615411,
  1999780524588989,1999534939212186,2000167806007432,2000813099043830,2000806062096394,
  2000350600569528,2000146892346914,2000565800639624,2001235971768441,2001390785857633,
  2000689496954459,1999817016613634,2000084997843280,2001870477081650,2003046897802302,
  1999490317088121,1988778819123651,1975267145261379,1972147736601958,1996940232870898,
  2061471965580237,2162365417238175,2278882296909617,2380475695882823,2439924878915663,
  2444458053843568,2399130511328328]
private def wc_rkmTraj_m32_r80_s2_v1_p1 : List ℕ := [2321961116490722,2234874749932071,
  2155635358305285,2093923671575896,2051691462808242,2025949641902292,2011872522054695,
  2004940917265956,2001864424750413,2000634935688802,2000193867100799,2000052584452178,
  2000012504281741,2000002556017904,2000000435135714,2000000058195513,2000000005297626]
private def wc_rkmTraj_m32_r80_s2_v1 : List ℕ := pCat wc_rkmTraj_m32_r80_s2_v1_p0
  wc_rkmTraj_m32_r80_s2_v1_p1
private def wc_rkmTraj_m32_r80_s2_v2_p0 : List ℕ := [1999977785914559,1999904009512846,
  1999733080316379,1999461454311305,1999195783348026,1999161021442547,1999547811128937,
  2000265450287463,2000849246992653,2000786147561560,2000066112976364,1999352685409676,
  1999377241819241,2000085722102517,2000619542528189,2000339166659124,1999669664439520,
  1999551374666664,2000117777888480,2000484970652213,2000069039657029,1999512321513627,
  1999721163694734,2000405424942917,2000471203783404,1999779807827743,1999446450245080,
  2000054698872737,2000634902619646,2000199224792728,1999421499712581,1999606193566993,
  2000507884918983,2000641855389489,1999714047929754,1999182208677544,1999918742734019,
  2000759447716408,2000363571222949,1999380669386930,1999387308273014,2000348917821314,
  2000729894750238,1999986326887713,1999363633240253,1999825855745996,2000566137993370,
  2000386789778233,1999565280980823,1999339426324746,2000060112117423,2000736621412412,
  2000346058099551,1999242014654664,1999034421027998,2000420937426954,2001394994112638,
  1999897054406711,1998426128383789,2001134026247314,2004710097215388,2000827406837460,
  1992834224636802,1996666189494073]
private def wc_rkmTraj_m32_r80_s2_v2_p1 : List ℕ := [2012593819551038,2013214774126362,
  1985209709648572,1967852124492403,2006446369936007,2066706522925126,2050847041852001,
  1931240052156625,1827687688156365,1898214624274375,2158276328320501,2447464039970991,
  2580940441782785,2508017792321679,2320955542081392,2144539533131463,2041217678903590]
private def wc_rkmTraj_m32_r80_s2_v2 : List ℕ := pCat wc_rkmTraj_m32_r80_s2_v2_p0
  wc_rkmTraj_m32_r80_s2_v2_p1
private def wc_rkmTraj_m64_r64_s1_hb : List ℕ := [215955516631552,300635232669478,362356991762488,
  411665203578896,452710514347721,487654196098426,517799160828975,544006611497152,566883231157824,
  586876903451160,604330385687617,619513566561674,632643934352931,643900144608913,653431343309077,
  661363769684128,667805554130040,672850282641214,676579696432256,679065771521582,680372344923825,
  680556403454156,679669117506015,677756679323236,674860989473600,671020224086242,666269307434253,
  660640308643865,654162777039815,646864027451157,638769384399403,629902392259860,620284997077717,
  609937704625880,598879718434105,587129060842032,574702679590199,561616542031755,547885718699773,
  533524457682873,518546251031558,502963894228676,486789539601502,470034744423702,452710514347721,
  434827342718096,416395246240429,397423797416923,377922154105216,357899086511284,337363001887892,
  316321967176465,294783729801383,272755736800814,250245152456699,227258874567851,203803549493947,
  179885586084041,155511168590926,130686268661815,105416656486364,79707911174677,53565430430583,
  26994439578944]
private def wc_rkmTraj_m64_r64_s1_v0_p0 : List ℕ := [2001217081889549,2004987707012670,
  2014198306769851,2032410862377567,2062911530058090,2107215378925344,2163688702233902,
  2226992443650338,2288793408197088,2339653524078286,2371467385724914,2379562659433358,
  2363731797071422,2327926321209026,2278868960401536,2224181754921347,2170676438304704,
  2123251603199433,2084532730252911,2055124995704726,2034210865876224,2020221054535900,
  2011390418932440,2006117715165279,2003134154262125,2001531987422001,2000714616732246,
  2000318136397608,2000135168698455,2000054805539460,2000021202378698,2000007824315716,
  2000002753360643,2000000923530025,2000000295112983,2000000089787060,2000000025991107,
  2000000007152784,2000000001869698,1999999999536267,1999999999890994,2000000000024251,
  2000000000005096,2000000000001007,2000000000000185,2000000000000030,2000000000000004,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m64_r64_s1_v0_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m64_r64_s1_v0 : List ℕ := pCat wc_rkmTraj_m64_r64_s1_v0_p0
  wc_rkmTraj_m64_r64_s1_v0_p1
private def wc_rkmTraj_m64_r64_s1_v1_p0 : List ℕ := [2000000000000002,2000000000000001,
  2000000000000004,1999999999999992,2000000000000041,1999999999999870,2000000000000395,
  1999999999998928,2000000000002636,1999999999994718,2000000000016869,1999999999988581,
  1999999999989214,1999999999155383,1999999995671720,1999999986174177,2000000003173815,
  2000000335342501,2000002533253895,2000012942370815,2000053110561159,2000185752694017,
  2000570149186426,2001562554520922,2003867207369395,2008712585006230,2017974305128657,
  2034109609650846,2059752633170694,2096897254143316,2145785164028290,2203863804870753,
  2265343271980267,2321807991844446,2363971372188445,2384126503602610,2378421930239424,
  2348049738734428,2298848476545946,2239498606968647,2179064996586843,2124825236075749,
  2081062118484383,2048989621258019,2027517417487060,2014343886657038,2006926270398460,
  2003091636094174,2001272515269425,2000481587793114,2000167020566495,2000052874023236,
  2000015208512307,2000003952969114,2000000922362966,2000000191675767,2000000035129587,
  2000000005609303,2000000000768218,2000000000088396,2000000000008304,2000000000000608,
  2000000000000031,2000000000000000]
private def wc_rkmTraj_m64_r64_s1_v1_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m64_r64_s1_v1 : List ℕ := pCat wc_rkmTraj_m64_r64_s1_v1_p0
  wc_rkmTraj_m64_r64_s1_v1_p1
private def wc_rkmTraj_m64_r64_s0_hb : List ℕ := [207955230117632,289497902005042,348933117255184,
  396414657411736,435939403893409,469588562261625,498616776845857,523853346485314,545882479058784,
  565135465912326,581942366571543,596563071436283,609207011716903,620046224488805,629224330470562,
  636862892235248,643066034380967,647923875916046,651515129870643,653909105840114,655167275933506,
  655344515832848,654490100273552,652648510261920,649860094117600,646161613697122,641586699469210,
  636166232527473,629928667512578,622900307348619,615105538385067,606567032772469,597305923542984,
  587341956812801,576693624697852,565378281882312,553412248260845,540810899660151,527588748310442,
  513759514465751,499336190350175,484331097425195,468755937823060,452621840666756,435939403893409,
  418718732111188,400969470946894,382700838279879,363921652705856,344640359529812,324865054549487,
  304603505858451,283863173870058,262651229739553,240974572340939,218839843937225,196253444667093,
  173221545957425,149750102959226,125844866094112,101511391789333,76755052471320,51581045880605,
  25994403764704]
private def wc_rkmTraj_m64_r64_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTraj_m64_r64_s0_v1_p0 : List ℕ := [2001217081889549,2004987707012670,
  2014198306769851,2032410862377567,2062911530058090,2107215378925344,2163688702233902,
  2226992443650338,2288793408197088,2339653524078286,2371467385724914,2379562659433358,
  2363731797071422,2327926321209026,2278868960401536,2224181754921347,2170676438304704,
  2123251603199433,2084532730252911,2055124995704726,2034210865876224,2020221054535900,
  2011390418932440,2006117715165279,2003134154262125,2001531987422001,2000714616732246,
  2000318136397608,2000135168698455,2000054805539460,2000021202378698,2000007824315716,
  2000002753360643,2000000923530025,2000000295112983,2000000089787060,2000000025991107,
  2000000007152784,2000000001869698,2000000000463733,2000000000109006,2000000000024251,
  2000000000005096,2000000000001007,2000000000000185,2000000000000030,2000000000000004,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m64_r64_s0_v1_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m64_r64_s0_v1 : List ℕ := pCat wc_rkmTraj_m64_r64_s0_v1_p0
  wc_rkmTraj_m64_r64_s0_v1_p1
private def wc_rkmTraj_m8_r80_s4_hb_p0 : List ℕ := [189171349406632,264741344090834,
  320825350664086,366511861518983,405359670430839,439212733292702,469177363885666,495981400483136,
  520135216783700,542013881046963,561903128908137,580026936401029,596564980026707,611664187060113,
  625446656469073,638015257331839,649457688657365,659849489290439,669256312779282,677735675993978,
  685338323459139,692109306092525,698088844327095,703313026118969,707814376873322,711622328836322,
  714763610715357,717262573362424,719141463728783,720420656595833,721118851548840,721253241106107,
  720839654719036,719892682427005,718425781219036,716451366573340,713980891180197,711024912476221,
  707593150308495,703694535789618,699337252186997,694528768502091,689275866229573,683584659635949,
  677460609755937,670908532167420,663932598466678,656536331219035,648722592000000,640493561960855,
  631850714141810,622794776503851,613325684343034,603442520368981,593143440247284,582425580788519,
  571284947166732,559716274500205,547712857731833,535266341868315,522366462076183,509000719590965,
  495153974424250,480807928760194]
private def wc_rkmTraj_m8_r80_s4_hb_p1 : List ℕ := [465940464630815,450524784199397,
  434528277878341,417911009664782,400623651912769,382604607681641,363775898274723,344037107934085,
  323256143567408,301254507759635,277782522910601,252474662582122,224761251563254,193669798972889,
  157279794825529,110574928475724]
private def wc_rkmTraj_m8_r80_s4_hb : List ℕ := pCat wc_rkmTraj_m8_r80_s4_hb_p0
  wc_rkmTraj_m8_r80_s4_hb_p1
private def wc_rkmTraj_m8_r80_s4_v0_p0 : List ℕ := [2000002837218948,2000001181487858,
  1999998295344828,1999998731308801,2000001418032821,2000001837199601,2000000638949508,
  2000002916068176,2000009210045666,2000014173405616,2000014260584896,2000010422273057,
  2000003589250007,1999994388907668,1999988057765750,1999993226376286,2000011594359899,
  2000025834118656,1999998417743789,1999909477805323,1999849933215738,2000065605564305,
  2000717013139430,2001301635045449,2000303373918652,1996098198287826,1989502994937838,
  1986544906919345,1998594907981750,2037918827826731,2110054716592973,2207679134348971,
  2310668280394754,2393315114662704,2434897682429172,2427694747165823,2378501226049789,
  2303874842529689,2222610033434469,2149448319372513,2092244915397418,2052475929858429,
  2027563443626866,2013385357166002,2006014905470103,2002502320267217,2000963901162646,
  2000343726065681,2000113410631242,2000034592341749,2000009742227184,2000002529207932,
  2000000604033647,2000000132362513,2000000026527905,2000000004843373,2000000000801577,
  2000000000119501,2000000000015916,2000000000001872,2000000000000189,2000000000000014,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m8_r80_s4_v0_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m8_r80_s4_v0 : List ℕ := pCat wc_rkmTraj_m8_r80_s4_v0_p0
  wc_rkmTraj_m8_r80_s4_v0_p1
private def wc_rkmTraj_m8_r80_s4_v1_p0 : List ℕ := [2000000001378901,2000000003385450,
  2000000004397615,2000000002434103,1999999998484156,1999999996755332,1999999999441844,
  2000000002685779,2000000001559488,1999999997994970,1999999998050955,2000000001532923,
  2000000002063413,1999999998550441,1999999997334969,2000000001161639,2000000006481406,
  2000000010544414,2000000002847495,1999999952954115,1999999853137605,1999999811178906,
  2000000068948790,2000000849956005,2000002119315581,2000003385903546,2000003599899515,
  2000001576865810,1999997780155713,1999996250297374,2000001568428395,2000009265960336,
  2000003736135938,1999981031297075,1999974477845471,2000021724927644,2000078108865416,
  2000021920481680,1999849807445223,1999819411578380,2000151956282047,2000505115780526,
  2000146982549183,1999124920286909,1998889006859810,2000632440154293,2002754082972263,
  2001621495474046,1996645780971260,1993547294124676,1998963661925449,2010118095590052,
  2013364801113354,1998585749324008,1975884884329311,1971976440492577,2002869875104100,
  2049156740292308,2064528800929608,2016741076973698,1924584173181247,1853821915117639,
  1871863134467046,1998237114689009]
private def wc_rkmTraj_m8_r80_s4_v1_p1 : List ℕ := [2190159745932642,2370973637293280,
  2475969342446978,2482690305329159,2411113959020797,2302394733357654,2194911265808949,
  2110936305740785,2055937552743768,2024985750730305,2009855221630199,2003410075496425,
  2001023699522046,2000261877604532,2000055388234943,2000009147472550,2000001023084359]
private def wc_rkmTraj_m8_r80_s4_v1 : List ℕ := pCat wc_rkmTraj_m8_r80_s4_v1_p0
  wc_rkmTraj_m8_r80_s4_v1_p1
private def wc_rkmTrajPack_m4_r96_s4_hb_p0 : List ℕ := [193337365333248,270572195791013,
  327893678513718,374591145333168,414302345997693,448912378005488,479552426070201,506966851061057,
  531677754666432,554068953337660,574432967644764,592999205822682,609951811150622,625441469109379,
  639593505032225,652513607999712,664291982206343,675006425289160,684724655467150,693506100909182,
  701403296448160,708462988532661,714727019959968,720233046030783,725015119999680,729104176004169,
  732528430722137,735313719974308,737483782785172,739060502657259,740064113735310,740513377954353,
  740425738048968,739817450356884,738703700611228,737098705333008,735015800972286,732467522575903,
  729465673461059,726021387132106,722145182480592,717847013146844,713136311788100,708022029887733,
  702512673648262,696616336434007,690340728164739,683693202007327,676680778666368,669310168535665,
  661587791939165,653519797661380,645112079942925,636370294095692,627299870874029,617906029722519,
  608193791007282,598167987325811,587833273979965,577194138687618,566254910600492,555019768688690,
  543492749546228,531677754666432]
private def wc_rkmTrajPack_m4_r96_s4_hb_p1 : List ℕ := [519578557231202,507198808453871,
  494542043511568,481611687099598,468411058637336,454943377152403,441211765867508,427219256512126,
  412968793379273,398463237145853,383705368473500,368697891405388,353443436573223,337944564227427,
  322203767102527,306223473128729,290006047999872,273553797607084,256868970346816,239953759311212,
  222810304368219,205440694138260,187846967873824,170031117247838,151995088056283,133740781840124,
  115270057431284,96584732427022,77686584596847,58577353225745,39258740397299,19732412220021]
private def wc_rkmTrajPack_m4_r96_s4_hb : List ℕ := pCat wc_rkmTrajPack_m4_r96_s4_hb_p0
  wc_rkmTrajPack_m4_r96_s4_hb_p1
private def wc_rkmTrajPack_m4_r96_s4_v0 : List ℕ := [2000216440966559,2000378013237871,
  1999594921904614,1999709465115786,1999867008399937,1999975964969848,2000037270354903,
  2000097594734373,1999861372011570,1999941883494170,1999782538272033,1999381911862258,
  1999063305387015,1999052587774128,1999431084261874,2000070146443476,2000220689721197,
  2001976595356259,2005239501698392,2006958519802590,1999970247364614,2025184460875618,
  2076293847817384,2153329918345491,2245769477623190,2334666706066069,2399355124106354,
  2425300646538264,2409077817456735,2358354545018799,2287650273170801,2212545457285099,
  2145075851968008,2091720098946612,2053821454905898,2029358953280585,2014904069818032,
  2007046431313670,2003103885135439,2001273931367753,2000487063140924,1999826627956151,
  1999942596740215,2000017656586742,2000005036836558,2000001329679867,2000000323949775,
  2000000072583412,2000000014890498,2000000002781239,1999999999530512,1999999999929079,
  1999999999990547,2000000000001087,1999999999999897,2000000000000007,2000000000000000]
private def wc_rkmTrajPack_m4_r96_s4_v1_p0 : List ℕ := [1999517597479797,2001108251951006,
  1998058355293213,2001722397410552,1999496541583332,1998704356898979,2001273480120645,
  1999916701734026,1998329549088872,2000647617033198,2001435181317598,1999040125091486,
  1999015989122122,2001512420548406,2001399824449940,1998782440776055,1998915439344476,
  2001358597618323,2001738931258142,1998910970112712,1997667958386547,2000009332163010,
  2002188770582296,2001045986349129,1998043548307027,1997459153353740,2000275953532339,
  2002747720092395,2001899081849646,1998753215350630,1996677171560502,1998129121730553,
  2002008991000749,2004550834446890,2003084532383382,1998083765180962,1992626925049484,
  1990989761079749,1996145459420969,2006809338977393,2016807023681067,2017869860164006,
  2004465945090205,1978664811956341,1952346867402248,1943999080548039,1970441854936035,
  2037965604442287,2138074552409685,2249965158917096,2348134380315987,2411393858402584,
  2429412470829103,2404420946093151,2348184520961998,2276454238869865,2203686388829752,
  2139866794655841,2089775450289249,2053962031543159,2030404841968820,2016065908348519,
  2007961693910670,2003699956555816]
private def wc_rkmTrajPack_m4_r96_s4_v1_p1 : List ℕ := [2001612178446620,2000658579262652,
  2000252217414805,2000090564645103,2000030497004131,2000009634303366,2000002856557883,
  2000000795342864,2000000208065685,2000000051170399,2000000011835940,2000000002575457,
  2000000000527144,2000000000101428,2000000000018320,2000000000003098,2000000000000487,
  2000000000000068,2000000000000007,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000]
private def wc_rkmTrajPack_m4_r96_s4_v1 : List ℕ := pCat wc_rkmTrajPack_m4_r96_s4_v1_p0
  wc_rkmTrajPack_m4_r96_s4_v1_p1
private def wc_rkmTrajPack_m4_r96_s5_hb_p0 : List ℕ := [173798698090008,243776196958573,
  296097581185551,339054648906859,375886822906001,408268981184586,437203916246500,463350030896968,
  487168100963988,508996094407131,529090998839811,547653885897079,564845768792528,580798083462566,
  595619870200446,609402845366484,622225076310675,634153703822107,645246998235331,655555938816495,
  665125445292414,673995351060970,682201181538996,689774783422941,696744838414474,703137286362248,
  708975676620612,714281461963069,719074246105871,723371993452927,727191207832318,730547085593356,
  733453647355814,735923851867128,737969694769158,739602294559901,740831967625072,741668293885550,
  742120174341323,742195881576852,741903104116273,741248985371368,740240157804430,738882772827071,
  737182526870713,735144683991835,732774095312493,730075215542055,727052116777873,723708499739217,
  720047702549013,716072707140608,711786143330998,707190290566583,702287077311762,697078078013424,
  691564507534582,685747212906914,679626662203277,673202930275838,666475681041213,659444145918523,
  652107097936441,644462820917159]
private def wc_rkmTrajPack_m4_r96_s5_hb_p1 : List ℕ := [636509073013874,628243043717196,
  619661303246559,610759742993952,601533505374400,591976901040635,582083310911372,571845069806630,
  561253327628454,550297882899488,538966981973491,527247075214647,515122518692925,502575206143884,
  489584110615324,476124707634836,462168240727522,447680773837750,432621950607298,416943342354317,
  400586205915115,383478372794896,365529821185601,346626180545641,326618854843060,305309333988496,
  282422884396264,257561259346462,230109488772876,199026748199244,162273992645198,114565355760735]
private def wc_rkmTrajPack_m4_r96_s5_hb : List ℕ := pCat wc_rkmTrajPack_m4_r96_s5_hb_p0
  wc_rkmTrajPack_m4_r96_s5_hb_p1
private def wc_rkmTrajPack_m4_r96_s5_v0_p0 : List ℕ := [2000482402520203,2001108251951006,
  2001941644706787,2001722397410552,2000503458416668,1998704356898979,2001273480120645,
  2000083298265974,2001670450911128,2000647617033198,2001435181317598,1999040125091486,
  1999015989122122,1998487579451594,1998600175550060,1998782440776055,2001084560655524,
  2001358597618323,2001738931258142,2001089029887288,2002332041613453,2000009332163010,
  2002188770582296,1998954013650871,1998043548307027,1997459153353740,1999724046467661,
  2002747720092395,2001899081849646,2001246784649370,1996677171560502,1998129121730553,
  1997991008999251,2004550834446890,2003084532383382,2001916234819038,2007373074950516,
  2009010238920251,2003854540579031,2006809338977393,2016807023681067,2017869860164006,
  2004465945090205,2021335188043659,2047653132597752,2056000919451961,2029558145063965,
  2037965604442287,2138074552409685,2249965158917096,2348134380315987,2411393858402584,
  2429412470829103,2404420946093151,2348184520961998,2276454238869865,2203686388829752,
  2139866794655841,2089775450289249,2053962031543159,2030404841968820,2016065908348519,
  2007961693910670,2003699956555816]
private def wc_rkmTrajPack_m4_r96_s5_v0_p1 : List ℕ := [2001612178446620,2000658579262652,
  2000252217414805,1999909435354897,1999969502995869,2000009634303366,2000002856557883,
  1999999204657136,1999999791934315,2000000051170399,2000000011835940,2000000002575457,
  2000000000527144,1999999999898572,1999999999981680,1999999999996902,2000000000000487,
  2000000000000068,1999999999999993,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000]
private def wc_rkmTrajPack_m4_r96_s5_v0 : List ℕ := pCat wc_rkmTrajPack_m4_r96_s5_v0_p0
  wc_rkmTrajPack_m4_r96_s5_v0_p1
private def wc_rkmTrajPack_m4_r96_s5_v1_p0 : List ℕ := [2001916196416391,2000241743421866,
  2000748192421997,1998668531566256,2000719494126597,1999329355527878,1999775484673430,
  2001466653438976,1998766253880799,2001711335953206,1998924532670628,1999882186195408,
  1998937404891191,2000288987438528,2001258933961759,2000945001078144,1999798838167043,
  2003223064718617,1999376291695676,2002859820857365,2000344885764072,1999600428695594,
  2001993745997552,1997678303983893,2002996171923851,1996485492464558,2002186776662011,
  2002161075450714,1996660341912862,2003350976202939,2002240815590885,2000103546807298,
  2001534493454915,1998860944068012,2000826339923303,1999066974459334,1993359601342323,
  2002389524245530,2007208928871004,1992049931574100,1991171336902599,2009722997300318,
  2007833163599331,1991505989979657,1999280895706228,2014796137925869,2002109090658582,
  1982957535429260,1994586685014349,2016390821857548,2009129592441831,1986327651251175,
  1987649979344526,2010691584642166,2017123655687155,1995088117974049,1976709028280525,
  1989617596640415,2018660416765995,2027447236916688,2004317685307087,1975601769367305,
  1975610240171774,2009832089910352]
private def wc_rkmTrajPack_m4_r96_s5_v1_p1 : List ℕ := [2049125987179499,2056837613551439,
  2021006945733203,1965424673146110,1934166008922948,1963145275231321,2058579897142182,
  2194725729984571,2328943734470961,2422409550241039,2454862300510143,2428155969916270,
  2360152815105604,2274361517716442,2190922406155690,2122048258451064,2071915799500307,
  2039122527443848,2019650952526973,2009103772964559,2003882130383845,2001519689121268,
  2000544308405526,2000177685927811,2000052622895936,2000014059453032,2000003364725677,
  2000000714586304,2000000132941071,2000000021255788,2000000002832508,2000000000297133,
  2000000000021290]
private def wc_rkmTrajPack_m4_r96_s5_v1 : List ℕ := pCat wc_rkmTrajPack_m4_r96_s5_v1_p0
  wc_rkmTrajPack_m4_r96_s5_v1_p1
private def wc_rkmTrajPack_m4_r96_s6_hb_p0 : List ℕ := [165716803941599,232440246566697,
  282328609754578,323288110876912,358407534810672,389283875276002,416873293455848,441803575460160,
  464514070365706,485327030126673,504487492055858,522187177662629,538579612810197,553790121471316,
  567922673405816,581064720028854,593290698444250,604664627296011,615242067262739,625071627000003,
  634196137401493,642653579553718,650477826889569,657699245187440,664345182407843,670440372158457,
  676007268714141,681066327262997,685636239919741,689734135717175,693375751031190,696575575558586,
  699346977939771,701702314321434,703653022530511,705209704038548,706382195504207,707179631368008,
  707610498720395,707682685458529,707403522578907,706779821314195,705817905707471,704523641120692,
  702902459092871,700959378894146,698699026062290,696125648156157,693243127914603,690054993968031,
  686564429211758,682774276914863,678687044603995,674304905727956,669629699074727,664662925877108,
  659405744505201,653858962602470,648023026475700,641898007496320,635483585209317,628779026773950,
  621783162274855,614494355339008]
private def wc_rkmTrajPack_m4_r96_s6_hb_p1 : List ℕ := [606910468368767,599028821547548,
  590846144584608,582358519928227,573561315878251,564449107650398,555015583960361,545253436070262,
  535154225424669,524708224929874,513904227501408,502729313581378,491168566705424,479204722576933,
  466817732027798,453984211009514,440676740265406,426862961816160,412504395933351,397554865939801,
  381958360315015,365646066504963,348532148847577,330507555199055,311430599460679,291112002553144,
  269289806405098,245584283352712,219409060339034,189771712751191,154728014188448,109237898832067]
private def wc_rkmTrajPack_m4_r96_s6_hb : List ℕ := pCat wc_rkmTrajPack_m4_r96_s6_hb_p0
  wc_rkmTrajPack_m4_r96_s6_hb_p1
private def wc_rkmTrajPack_m4_r96_s6_v0_p0 : List ℕ := [2001916196416391,2000241743421866,
  1999251807578003,1998668531566256,2000719494126597,1999329355527878,2000224515326570,
  2001466653438976,1998766253880799,1998288664046794,1998924532670628,2000117813804592,
  1998937404891191,2000288987438528,2001258933961759,2000945001078144,2000201161832957,
  2003223064718617,2000623708304324,2002859820857365,2000344885764072,1999600428695594,
  1998006254002448,2002321696016107,2002996171923851,2003514507535442,2002186776662011,
  2002161075450714,2003339658087138,1996649023797061,1997759184409115,1999896453192702,
  1998465506545085,1998860944068012,2000826339923303,2000933025540666,2006640398657677,
  2002389524245530,1992791071128996,1992049931574100,2008828663097401,2009722997300318,
  2007833163599331,1991505989979657,2000719104293772,2014796137925869,2002109090658582,
  2017042464570740,2005413314985651,2016390821857548,2009129592441831,2013672348748825,
  2012350020655474,2010691584642166,2017123655687155,2004911882025951,2023290971719475,
  2010382403359585,2018660416765995,2027447236916688,2004317685307087,2024398230632695,
  2024389759828226,2009832089910352]
private def wc_rkmTrajPack_m4_r96_s6_v0_p1 : List ℕ := [2049125987179499,2056837613551439,
  2021006945733203,2034575326853890,2065833991077052,2036854724768679,2058579897142182,
  2194725729984571,2328943734470961,2422409550241039,2454862300510143,2428155969916270,
  2360152815105604,2274361517716442,2190922406155690,2122048258451064,2071915799500307,
  2039122527443848,2019650952526973,2009103772964559,1996117869616155,2001519689121268,
  2000544308405526,2000177685927811,1999947377104064,1999985940546968,2000003364725677,
  2000000714586304,1999999867058929,2000000021255788,1999999997167492,2000000000297133,
  2000000000021290]
private def wc_rkmTrajPack_m4_r96_s6_v0 : List ℕ := pCat wc_rkmTrajPack_m4_r96_s6_v0_p0
  wc_rkmTrajPack_m4_r96_s6_v0_p1
private def wc_rkmTrajPack_m4_r96_s6_v1_p0 : List ℕ := [1999582377497945,2001446126245361,
  1999942071655474,2001678956058647,1998245116804594,2000807030515411,2000020634482881,
  2000516043415815,2002128236169856,2001095681739611,2001690683261602,1998383826982746,
  2000282958451719,2001499266828800,2000739734266057,1998519472877282,2001234629962832,
  1996884924150000,2001048486709095,1998750273005396,2000428961928886,1999307590814883,
  2000893883857101,2003921117433754,1991545988473758,2009939439585555,1993526275940421,
  2002388820009047,1997873630186584,1995907739902935,2005086713481360,1995223700994274,
  2004020774516372,1994807828963559,2001939768833322,1996907065822806,2004431354997129,
  2003745979256163,1991386526555634,2012484757999104,2001769773608092,1996250894384856,
  1998912278297550,1993665804516156,2014969332627230,1997775690041847,1989373284456776,
  2010882837716893,2003717114366637,2006815623130855,2006635128957879,1984617223940892,
  1996900192804110,2013563060966972,1987414531291291,2009487105521587,2006968513646275,
  1978225845996726,2011906000174627,2008322043434314,1982381017745629,2013059008749066,
  2009479117618277,1981022744855112]
private def wc_rkmTrajPack_m4_r96_s6_v1_p1 : List ℕ := [2006900366741298,2019638269620118,
  1989029358822250,2001034403843812,2026301958440256,2014497213032140,1995034952727944,
  2019450758708335,2022368966441004,2001266076724751,2005983379356068,2035255188526355,
  2037570772682822,1992956974387547,1976169472117422,2031767761997426,2091775068164352,
  2077522063948211,1991565427634541,1920809385402561,1965669661012478,2138330391813442,
  2348571386771696,2490147120565205,2513974466081279,2435151552481202,2305044687146933,
  2177858653595947,2085859562367132,2033916668428184,2010706637852317,2002566398165555,
  2000407108592570]
private def wc_rkmTrajPack_m4_r96_s6_v1 : List ℕ := pCat wc_rkmTrajPack_m4_r96_s6_v1_p0
  wc_rkmTrajPack_m4_r96_s6_v1_p1
private def wc_rkmTrajPack_m32_r80_s2_hb_p0 : List ℕ := [191114748745845,267531318201386,
  324292889790697,370573697011169,409965080390262,444327341399398,474776288078040,502045795356718,
  526650318840974,548967811532361,569286115413858,587830782560815,604782690348740,620289693078039,
  634474611457285,647440878813027,659276635062576,670057761543933,679850174401195,688711587169323,
  696692885773046,703839215494166,710190850490870,715783896804705,720650866201549,724821148625602,
  728321404200275,731175890739474,733406739074433,735034185774582,736076770784704,736551505932918,
  736474019056060,735858677548955,734718694405031,733066219228961,730912416231230,728267530832509,
  725140946191846,721541230711040,717476177345645,712952835360941,707977535000730,702555905380976,
  696692885773046,690392730296772,683659005896145,676494583314046,668901620610459,660881538573076,
  652434987140594,643561801685154,634260947665586,624530451746762,614367316954599,603767418763411,
  592725378140146,581234406425743,569286115413858,556870283943013,543974569532484,530584149742984,
  516681272544037,502244687272469]
private def wc_rkmTrajPack_m32_r80_s2_hb_p1 : List ℕ := [487248916595224,471663313354740,
  455450821160448,438566318809063,420954366810039,402546072644486,383254618062926,362968683510392,
  341542428853684,318779547710057,294406478325089,268024169263855,239012852803515,206318058454694,
  167864078661723,118246217970081]
private def wc_rkmTrajPack_m32_r80_s2_hb : List ℕ := pCat wc_rkmTrajPack_m32_r80_s2_hb_p0
  wc_rkmTrajPack_m32_r80_s2_hb_p1
private def wc_rkmTrajPack_m32_r80_s2_v0_p0 : List ℕ := [2000000289940496,2000001181752460,
  2000003352531682,2000007642412490,2000014845184364,2000025372336498,2000038933487647,
  2000054386850959,2000069862804677,2000083156675354,2000092263805347,2000095879446596,
  2000093681820346,2000086341859931,2000075258954162,2000062180223491,2000048829172816,
  2000036736152178,2000027234698037,2000020732437115,1999988376575724,1999968948134624,
  2000216716354658,2000847237301918,2002610358417963,2006828161249258,2015653227878724,
  2032013815401129,2059086020962169,2099201569257243,2152401247604312,2215195649271988,
  2280261531378937,2337577297671027,2376891357297170,2390710317418010,2376613697921625,
  2337921577194856,2282473487046837,2220112719270286,2159952705370864,2108419218314750,
  2068548540597079,2040420162224491,2022220709987188,2011382810863291,2005429503280603,
  2002409275854404,2000993405933008,2000380074178937,2000134701837956,2000044132549335,
  2000013334294633,2000003704633069,2000000943124433,2000000219081779,2000000046196472,
  2000000008785737,2000000001494705,2000000000225048,2000000000029548,2000000000003309,
  2000000000000304,2000000000000021]
private def wc_rkmTrajPack_m32_r80_s2_v0_p1 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m32_r80_s2_v0 : List ℕ := pCat wc_rkmTrajPack_m32_r80_s2_v0_p0
  wc_rkmTrajPack_m32_r80_s2_v0_p1
private def wc_rkmTrajPack_m32_r80_s2_v1_p0 : List ℕ := [2000004751700622,1999989081268316,
  2000012766554020,1999995220921542,1999992304726766,2000010305473256,2000001304338749,
  1999989102703339,2000003167401740,2000009914494716,1999994227387000,1999991087028122,
  2000007055593177,2000008503433176,1999992610745281,1999991149503985,2000006865141056,
  2000009866549154,1999994667531079,1999988795123207,2000002554306397,2000012252998712,
  2000001737174010,1999988356006829,1999993543908628,2000009537810320,2000012937413884,
  1999999989890964,1999990812333398,2000000442471917,2000019592508110,2000028723800515,
  2000023254579747,2000017815342243,2000027573406322,2000051074324036,2000073269667495,
  2000082555097566,2000080978128469,2000076319697273,2000068864480983,2000057324197299,
  2000062523390258,2000120801906715,2000207386750754,2000164916472434,1999821687117404,
  1999346786012567,1999470982679397,2000964072329122,2003315821972143,2003787612149852,
  1998627197774653,1986957869882548,1975072965198372,1977055924113952,2009212855418461,
  2080338812068456,2183820710293388,2297359580814922,2391379162194057,2441498985813599,
  2438064289172119,2388090442136208]
private def wc_rkmTrajPack_m32_r80_s2_v1_p1 : List ℕ := [2309878292574838,2224364974255462,
  2147885726479533,2088946113987073,2048869998876108,2024529714551174,2011237172640853,
  2004688776726087,2001776277584869,2000608134656271,2000186941259850,2000051129904755,
  2000012281612293,2000002540927945,2000000438769010,2000000059666981,2000000005537390]
private def wc_rkmTrajPack_m32_r80_s2_v1 : List ℕ := pCat wc_rkmTrajPack_m32_r80_s2_v1_p0
  wc_rkmTrajPack_m32_r80_s2_v1_p1
private def wc_rkmTrajPack_m32_r80_s2_v2_p0 : List ℕ := [2000000002612040,2000000018033065,
  2000000083520830,2000000298375574,2000000867247703,2000002102484316,2000004294458148,
  2000007381178705,2000010520434073,2000011959319169,2000009728498328,2000003245462927,
  1999994849385681,1999989466703738,1999991416155310,2000000113683309,2000008893293741,
  2000009783654669,2000001298439506,1999991353656123,1999990345287997,1999999876975359,
  2000009698293586,2000008384161820,1999997037418235,1999989144950629,1999994678141827,
  2000007048865727,2000010494474980,2000000247590809,1999989530452827,1999992703257123,
  2000005799837783,2000011150745479,2000001234828429,1999989513294465,1999992241927300,
  2000005698217610,2000011251798988,2000001503356561,1999989812693693,1999991195491954,
  2000004278030228,2000014269529846,2000005733277150,1999982361541946,1999981014542607,
  2000022065540725,2000036644636646,1999963595138208,1999933566979051,2000077877957489,
  2000131921364915,1999825999668373,1999708014727657,2000357987896676,2000680995422161,
  1999370440280078,1998454300239591,2000922755749964,2003481006147426,1999474271474749,
  1993071158668692,1998147717799844]
private def wc_rkmTrajPack_m32_r80_s2_v2_p1 : List ℕ := [2012662116069027,2010738541639379,
  1982843769676494,1968337358586801,2008093951631369,2065544598738212,2046883335738994,
  1929453189094350,1831922301930968,1906415340205206,2165095013448140,2450006610732542,
  2580504535563530,2507236807569764,2320984149841006,2144994043540796,2041514705527513]
private def wc_rkmTrajPack_m32_r80_s2_v2 : List ℕ := pCat wc_rkmTrajPack_m32_r80_s2_v2_p0
  wc_rkmTrajPack_m32_r80_s2_v2_p1
private def wc_rkmTrajPack_m64_r59_s0_hb : List ℕ := [212604709322038,296942762573921,
  359108113358723,409374611515768,451771759064903,488390210699889,520485649209499,548884845197917,
  574167829379960,596760916679857,616988793298305,635105775485414,651315613429439,665784596851339,
  678650544094838,690029154968699,700018615571742,708703008984298,716154888776697,722437252012773,
  727605072616385,731706506835522,734783849892942,736874300728383,738010576346627,738221406397020,
  737531930757290,735964017118714,733536511229196,730265429106173,726164097873321,721243249678389,
  715511071241891,708973209826783,701632734681367,693490051165475,684542762683165,674785473041889,
  664209518711964,652802616356760,640548405489399,627425858511274,613408519671610,598463519046083,
  582550284886391,565618843396317,547607541952289,528439947428304,508020532786498,486228529304549,
  462908903124234,437858633580996,410804923974338,381368682372853,348998930691542,312843638853905,
  271460217637935,222024069444232,157223302826485]
private def wc_rkmTrajPack_m64_r59_s0_v1 : List ℕ := [2000017795261913,2000096456952720,
  2000364405507844,2001107780102613,2002873682418131,2006568638372256,2013500359014214,
  2025297672975428,2043658631489045,2069926527391122,2104567917131425,2146697660738612,
  2193827557058386,2241981343730875,2286219900089006,2321487642571753,2343575180968934,
  2349942133945184,2340179957247186,2316004225117901,2280806437413460,2238915239045673,
  2194777090110290,2152255116989182,2114177840985226,2082178965973988,2056788672432710,
  2037687816888396,2024024762816704,2014712372351113,2008655361751938,2004891559734775,
  2002655321237847,2001384232664296,2000692793941325,2000332772327401,2000153336750766,
  2000067743737456,2000028677464071,2000011623550469,2000004507015455,2000001670163187,
  2000000590812708,2000000199245080,2000000063960260,2000000019509782,2000000005643204,
  2000000001544159,2000000000398590,2000000000096730,2000000000021978,2000000000004650,
  2000000000000908,2000000000000160,2000000000000024,2000000000000002,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m32_r53_s0_hb : List ℕ := [222155895386260,309572777461502,
  373502861633928,424757213879932,467585728402627,504198130911562,535924356367008,563641814081879,
  587967253590481,609354827226890,628151046062260,644627787553087,659003223430508,671455678556231,
  682133141977482,691159991192668,698641866743755,704669281710917,709320342907527,712662833583507,
  714755827322244,715650950813037,715393378550871,714022618894697,711573134423792,708074827736067,
  703553415164894,698030704311445,691524786081570,684050147561368,675617708160389,666234777646982,
  655904930653572,644627787553087,632398685809627,619208218306084,605041604747474,589877847494052,
  573688601648930,556436656903662,538073878751360,518538377350020,497750542033415,475607357493018,
  451974023128820,426671160166111,399454430544817,369980278736686,337744240826886,301959166664145,
  261281657592072,213062597783036,150400252161188]
private def wc_rkmTrajPack_m32_r53_s0_v1 : List ℕ := [2001163646369690,2004751175860229,
  2013494106487684,2030776386832515,2059771246279788,2102064110579788,2156354584400151,
  2217873399129433,2278938565263352,2330609831086930,2364913928248198,2376856932210941,
  2365537195598331,2334055048105036,2288381211142297,2235680753168952,2182677036313123,
  2134497786347809,2094184622773125,2062798554524269,2039903926875369,2024182388397834,
  2013984868764967,2007721359781450,2004071483649711,2002050843110884,2000986921560791,
  2000453739573517,2000199279353009,2000083591430336,2000033478869324,2000012796970560,
  2000004665931226,2000001621727806,2000000536885418,2000000169137903,2000000050649650,
  2000000014398857,2000000003880101,2000000000989374,2000000000238225,2000000000054033,
  2000000000011510,2000000000002294,2000000000000423,2000000000000070,2000000000000009,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private abbrev dP_0 : Prop := atF [ bNLE (bEvalLo12W 8 1024 104 [1,2,4,8,16,20,20,20]
  [17900607,18810276,19467357,16634230,11099809,23408761,1243517,435150] [3,5,9,14,15,37,2,1]
  rkmMasks_m8_r104 [none, none, none, none, none, some (37, 105, wc_rkmTraj_m8_r104_s5_hb,
  wc_rkmTraj_m8_r104_s5_v0, wc_rkmTraj_m8_r104_s5_v2)]) rkmRow_m8_r104] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bNLE (bEvalLo12W 32 256 80 [1,2,4,4,4]
  [37672593,27964751,37544000,10702039,3969736] [15,20,42,12,5] rkmMasks_m32_r80 [none, none, some
  (42, 81, wc_rkmTraj_m32_r80_s2_hb, wc_rkmTraj_m32_r80_s2_v0, wc_rkmTraj_m32_r80_s2_v2)])
  rkmRow_m32_r80] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bNLE (bEvalLo12W 32 256 80 [1,2,4,4,4]
  [39093742,24917588,38716678,9847754,5294897] [14,16,41,11,6] rkmMasksPack_m32_r80 [none, none,
  some (41, 81, wc_rkmTrajPack_m32_r80_s2_hb, wc_rkmTrajPack_m32_r80_s2_v0,
  wc_rkmTrajPack_m32_r80_s2_v2)]) rkmRowPack_m32_r80, bNLE (bEvalLo12W 16 512 80 [1,1,1,1,1,1,1,1]
  [13879474,13478652,25447496,12035258,6113151,7342721,4271941,3779842] [3,3,5,3,2,2,1,1]
  rkmMasksPack_m16_r80 []) rkmRowPack_m16_r80] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bNLE (bEvalLo12W 64 128 64 [1,1,2,2,2,2,2,2]
  [27619054,32055897,17485035,17485035,2618530,2975601,1218924,1218924] [17,19,17,17,3,3,2,2]
  rkmMasks_m64_r64 [some (17, 65, wc_rkmTraj_m64_r64_s0_hb, wc_rkmTraj_m64_r64_s0_v0,
  wc_rkmTraj_m64_r64_s0_v1), some (19, 65, wc_rkmTraj_m64_r64_s1_hb, wc_rkmTraj_m64_r64_s1_v0,
  wc_rkmTraj_m64_r64_s1_v1)]) rkmRow_m64_r64, bNLE (bEvalLo12W 512 16 16 [1,1,1,1]
  [33587572,639291,144227,50000] [18,1,1,1] rkmMasks_m512_r16 []) rkmRow_m512_r16] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bNLE (bEvalLo12W 64 128 59 [2,2,2,2,2,2,2,2]
  [25688053,15982896,9526033,12319566,6500866,5278876,2969895,1929494] [21,13,8,10,6,5,3,2]
  rkmMasksPack_m64_r59 [some (21, 60, wc_rkmTrajPack_m64_r59_s0_hb, wc_rkmTraj_m64_r64_s0_v0,
  wc_rkmTrajPack_m64_r59_s0_v1)]) rkmRowPack_m64_r59, bNLE (bEvalLo12W 32 256 16 [1,1,1,1,1,1,1,1]
  [45171987,44673513,13120863,12847745,11807741,13663535,11432096,7763496] [6,6,2,2,2,2,2,1]
  rkmMasks_m32_r16 []) rkmRow_m32_r16] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bNLE (bEvalLo12W 32 256 53 [3,3,3,3,3,3,3,3]
  [24915768,25113353,16784651,8580460,6583242,7492968,4299041,2551025] [16,16,11,6,5,5,3,2]
  rkmMasksPack_m32_r53 [some (16, 54, wc_rkmTrajPack_m32_r53_s0_hb, wc_rkmTraj_m64_r64_s0_v0,
  wc_rkmTrajPack_m32_r53_s0_v1)]) rkmRowPack_m32_r53, bNLE (bEvalLo12W 512 16 21 [1,1,1]
  [33393723,1146428,95734] [24,2,2] rkmMasks_m512_r21 []) rkmRow_m512_r21] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bSlideChk 28 81 wc_rkmTraj_m8_r80_s4_hb
  wc_rkmTraj_m8_r80_s4_v0 wc_rkmTraj_m8_r80_s4_v1, bNLE (bEvalLo12W 512 16 26 [1,1,1,1]
  [33393723,1021183,222478,168754] [29,2,2,2] rkmMasks_m512_r26 []) rkmRow_m512_r26] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bNLE (bEvalLo12W 64 128 40 [1,1,1] [118992250,2566867,752594]
  [47,1,1] rkmMasks_m64_r40 []) rkmRow_m64_r40, bNLE (bEvalLo12W 8 1024 32 [1,2,4,7,7,7,7,7]
  [37434841,39062360,49606189,25440596,23975606,8049403,2749419,1102573] [3,5,11,8,8,3,1,1]
  rkmMasks_m8_r32 []) rkmRow_m8_r32] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := atF [ bNLE (bEvalLo12W 32 256 44 [1,2,3,3,3]
  [51516654,19245568,45671799,3280418,973092] [13,8,24,2,1] rkmMasksPack_m32_r44 [])
  rkmRowPack_m32_r44, bSlideChk 17 65 wc_rkmTraj_m64_r64_s0_hb wc_rkmTraj_m64_r64_s0_v0
  wc_rkmTraj_m64_r64_s0_v1] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := atF [ bSlideChk 19 105 wc_rkmTraj_m8_r104_s5_hb
  wc_rkmTraj_m8_r104_s5_v0 wc_rkmTraj_m8_r104_s5_v1, bNLE (bEvalLo12W 4 2048 40 [1,2,4,8,15,15,15]
  [32465837,25264303,29326333,31369223,38243178,579432,5298078] [2,2,4,8,14,1,2]
  rkmMasksPack_m4_r40 []) rkmRowPack_m4_r40, bNLE (bEvalLo12W 512 16 11 [1] [34081402] [14]
  rkmMasks_m512_r11 []) rkmRow_m512_r11] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := atF [ bSlideChk 18 105 wc_rkmTraj_m8_r104_s5_hb
  wc_rkmTraj_m8_r104_s5_v1 wc_rkmTraj_m8_r104_s5_v2, bNLE (bEvalLo12W 256 32 32 [1,1,1,1,1,1]
  [23534193,23537905,1314360,1230536,353183,341629] [18,18,1,1,1,1] rkmMasks_m256_r32 [])
  rkmRow_m256_r32] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := atF [ bSlideChk 18 97 wc_rkmTrajPack_m4_r96_s4_hb
  wc_rkmTrajPack_m4_r96_s4_v0 wc_rkmTrajPack_m4_r96_s4_v1, bNLE (bEvalLo12W 32 256 35 [1,2,2,2,2]
  [78603477,41737972,13307343,7275143,4567755] [17,14,5,3,2] rkmMasksPack_m32_r35 [])
  rkmRowPack_m32_r35] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := atF [ bSlideChk 18 97 wc_rkmTrajPack_m4_r96_s5_hb
  wc_rkmTrajPack_m4_r96_s5_v0 wc_rkmTrajPack_m4_r96_s5_v1, bNLE (bEvalLo12W 4 2048 112
  [1,1,14,28,28,28,28,28] [22639971,21667069,10978452,527523,678885,1515592,417437,932728]
  [2,2,8,1,1,2,1,2] rkmMasksPack_m4_r112 []) rkmRowPack_m4_r112, bNLE (bEvalLo12W 64 128 12
  [1,1,1] [94050225,4309710,2381636] [13,1,1] rkmMasksPack_m64_r12 []) rkmRowPack_m64_r12] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := atF [ bSlideChk 21 81 wc_rkmTraj_m32_r80_s2_hb
  wc_rkmTraj_m32_r80_s2_v0 wc_rkmTraj_m32_r80_s2_v1, bNLE (bEvalLo12W 4 2048 48
  [1,2,4,8,16,18,18,18] [24080388,27254300,24466873,27810509,10384500,32801977,1551053,889519]
  [2,3,4,8,5,16,1,1] rkmMasks_m4_r48 []) rkmRow_m4_r48] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := atF [ bSlideChk 21 81 wc_rkmTraj_m32_r80_s2_hb
  wc_rkmTraj_m32_r80_s2_v1 wc_rkmTraj_m32_r80_s2_v2, bSlideChk 21 60 wc_rkmTrajPack_m64_r59_s0_hb
  wc_rkmTraj_m64_r64_s0_v0 wc_rkmTrajPack_m64_r59_s0_v1, bNLE (bEvalLo12W 1024 8 13 [1] [24140564]
  [18] rkmMasks_m1024_r13 []) rkmRow_m1024_r13] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := atF [ bSlideChk 21 81 wc_rkmTrajPack_m32_r80_s2_hb
  wc_rkmTrajPack_m32_r80_s2_v0 wc_rkmTrajPack_m32_r80_s2_v1, bSlideChk 19 65
  wc_rkmTraj_m64_r64_s1_hb wc_rkmTraj_m64_r64_s1_v0 wc_rkmTraj_m64_r64_s1_v1, bNLE (bEvalLo12W 4
  2048 14 [1,2,4,6,6,6,6,6]
  [58134444,55688380,64859315,35399105,32807265,10572107,3951853,1659779] [2,3,5,4,4,1,1,1]
  rkmMasks_m4_r14 []) rkmRow_m4_r14] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := atF [ bNLE (bEvalLo12W 8 1024 80 [1,2,4,8,15,15,15]
  [23598013,21580139,22199617,19382100,27030108,3565229,835315] [3,5,9,13,28,4,1] rkmMasks_m8_r80
  [none, none, none, none, some (28, 81, wc_rkmTraj_m8_r80_s4_hb, wc_rkmTraj_m8_r80_s4_v0,
  wc_rkmTraj_m8_r80_s4_v1)]) rkmRow_m8_r80, bNLE (bEvalLo12W 16 512 28 [1,2,3,3,3]
  [47818132,40008833,48822352,24118460,6988463] [7,9,13,7,3] rkmMasks_m16_r28 []) rkmRow_m16_r28,
  bNLE (bEvalLo12W 2 4096 24 [1,2,4,8,16,18,18,18]
  [28571613,26875562,34243345,42932435,15341358,50490723,8924918,7683510] [1,1,2,5,3,9,2,2]
  rkmMasksPack_m2_r24 []) rkmRowPack_m2_r24] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := atF [ bSlideChk 17 97 wc_rkmTrajPack_m4_r96_s6_hb
  wc_rkmTrajPack_m4_r96_s6_v0 wc_rkmTrajPack_m4_r96_s6_v1, bNLE (bEvalLo12W 16 512 29 [1,3,3,3]
  [73911391,83670715,12090970,4318798] [8,20,3,2] rkmMasksPack_m16_r29 []) rkmRowPack_m16_r29,
  bNLE (bEvalLo12W 16 512 22 [1,2,2,2,2] [89123555,67323532,27409019,16361807,9019242]
  [8,10,5,3,2] rkmMasksPack_m16_r22 []) rkmRowPack_m16_r22] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := atF [ bSlideChk 20 81 wc_rkmTrajPack_m32_r80_s2_hb
  wc_rkmTrajPack_m32_r80_s2_v1 wc_rkmTrajPack_m32_r80_s2_v2, bNLE (bEvalLo12W 4 2048 96
  [1,2,6,14,24,42,42,42] [18267857,19623003,21304676,17942660,18125378,12316825,11091626,4615239]
  [2,3,7,12,18,18,17,7] rkmMasksPack_m4_r96 [none, none, none, none, some (18, 97,
  wc_rkmTrajPack_m4_r96_s4_hb, wc_rkmTrajPack_m4_r96_s4_v0, wc_rkmTrajPack_m4_r96_s4_v1), some
  (18, 97, wc_rkmTrajPack_m4_r96_s5_hb, wc_rkmTrajPack_m4_r96_s5_v0, wc_rkmTrajPack_m4_r96_s5_v1),
  some (17, 97, wc_rkmTrajPack_m4_r96_s6_hb, wc_rkmTrajPack_m4_r96_s6_v0,
  wc_rkmTrajPack_m4_r96_s6_v1)]) rkmRowPack_m4_r96] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := atF [ bSlideChk 16 54 wc_rkmTrajPack_m32_r53_s0_hb
  wc_rkmTraj_m64_r64_s0_v0 wc_rkmTrajPack_m32_r53_s0_v1, bNLE (bEvalLo12W 256 32 26 [1] [49855494]
  [31] rkmMasks_m256_r26 []) rkmRow_m256_r26, bNLE (bEvalLo12W 1024 8 25 [1,1] [23945420,496437]
  [29,2] rkmMasks_m1024_r25 []) rkmRow_m1024_r25, bNLE (bEvalLo12W 1024 8 23 [1,1]
  [23912511,495463] [27,2] rkmMasks_m1024_r23 []) rkmRow_m1024_r23] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := atF [ bNLE (bEvalLo12W 16 512 25 [1,2,2,2]
  [76979844,99490539,30776310,10746970] [8,17,5,2] rkmMasksPack_m16_r25 []) rkmRowPack_m16_r25,
  bNLE (bEvalLo12W 64 128 20 [1,1,1] [102258344,3665139,69471] [24,2,2] rkmMasks_m64_r20 [])
  rkmRow_m64_r20, bNLE (bEvalLo12W 1024 8 20 [1] [24349636] [23] rkmMasks_m1024_r20 [])
  rkmRow_m1024_r20, bNLE (bEvalLo12W 2 4096 24 [1,2,4,8,16,18,18,18]
  [31211236,22344939,42194036,37061239,18101226,49350000,7911124,2210459] [1,1,3,4,3,9,2,1]
  rkmMasks_m2_r24 []) rkmRow_m2_r24, bNLE (bEvalLo12W 16 512 17 [1,2,2,2]
  [111498849,57471348,23447181,9028134] [9,7,3,2] rkmMasksPack_m16_r17 []) rkmRowPack_m16_r17,
  bNLE (bEvalLo12W 1024 8 16 [1] [24247995] [19] rkmMasks_m1024_r16 []) rkmRow_m1024_r16, bNLE
  (bEvalLo12W 128 64 11 [1,1,1,1] [56052784,10503317,1895937,748513] [11,3,2,2] rkmMasks_m128_r11
  []) rkmRow_m128_r11] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := atF [ bNLE (bEvalLo12W 2 4096 16 [1,2,4,8,12,12,12,12]
  [46689155,41893053,49422253,59202398,25935300,21413489,7921805,5882988] [1,2,3,5,3,3,1,1]
  rkmMasksPack_m2_r16 []) rkmRowPack_m2_r16, bNLE (bEvalLo12W 4 2048 13 [1,2,4,6,6,6,6,6]
  [77253892,56026260,70970791,32946965,18189557,14128667,3742041,2729746] [2,3,5,3,2,2,1,1]
  rkmMasksPack_m4_r13 []) rkmRowPack_m4_r13, bNLE (bEvalLo12W 8 1024 10 [1,2,2,2,2]
  [124197936,54162353,53378895,29826025,13050983] [5,4,4,3,2] rkmMasks_m8_r10 []) rkmRow_m8_r10,
  bNLE (bEvalLo12W 2 4096 14 [1,3,6,12] [47438247,58830241,63879817,64052698] [1,2,4,6]
  rkmMasksPack_m2_r14 []) rkmRowPack_m2_r14, bNLE (bEvalLo12W 1024 8 5 [1] [23317052] [7]
  rkmMasks_m1024_r5 []) rkmRow_m1024_r5, bNLE (bEvalLo12W 2 4096 22 [1,2,4]
  [55313573,47436647,54281177] [2,3,4] rkmMasks_m2_r22 []) rkmRow_m2_r22, bNLE (bEvalLo12W 16 512
  6 [1,1,1] [176770137,19274273,10119497] [8,2,2] rkmMasks_m16_r6 []) rkmRow_m16_r6, bNLE
  (bEvalLo12W 32 256 7 [1,1,1,1,1] [77719761,38852871,11944135,8222498,4021626] [5,3,1,1,1]
  rkmMasks_m32_r7 []) rkmRow_m32_r7, bNLE (bEvalLo12W 128 64 8 [1,1,1] [66121382,1705270,319395]
  [10,2,2] rkmMasks_m128_r8 []) rkmRow_m128_r8, bNLE (bEvalLo12W 8 1024 8 [1,2,2,2]
  [167181012,67815506,28625439,12669963] [6,4,3,2] rkmMasks_m8_r8 []) rkmRow_m8_r8, bNLE
  (bEvalLo12W 32 256 4 [1,1,1,1,1] [125158640,6137295,610204,606544,353886] [5,1,1,1,1]
  rkmMasksPack_m32_r4 []) rkmRowPack_m32_r4, bNLE (bEvalLo12W 4 2048 60 [1,1,1,1,1,1,1,1]
  [12902371,14149758,29340260,11554616,14154075,197083,9042,7200276] [1,1,2,1,1,1,1,1]
  rkmMasksPack_m4_r60 []) rkmRowPack_m4_r60, bNLE (bEvalLo12W 8 1024 4 [1,1,1,1,1,1,1,1]
  [75309509,76367293,32028507,26557672,25637271,30293046,13091718,10965552] [2,2,1,1,1,1,1,1]
  rkmMasksPack_m8_r4 []) rkmRowPack_m8_r4, bNLE (bEvalLo12W 8 1024 7 [1,2] [165016940,95258849]
  [5,4] rkmMasksPack_m8_r7 []) rkmRowPack_m8_r7, bNLE (bEvalLo12W 4 2048 8 [1,1,2,2,3,3,3,3]
  [30396927,81719325,24752466,48838827,47527620,49664948,37431095,12421030] [1,2,1,2,2,2,2,1]
  rkmMasksPack_m4_r8 []) rkmRowPack_m4_r8, bNLE (bEvalLo12W 16 512 8 [1,1,1,1,1,1,1,1]
  [53209192,49679527,47243500,20558617,15911430,17592953,8255461,7088420] [3,3,3,1,1,1,1,1]
  rkmMasksPack_m16_r8 []) rkmRowPack_m16_r8] = true
private theorem bk_21 : dP_21 := by decide +kernel
private theorem ws_rkmTraj_m8_r104_s5 : WalkOk (some (37, 105, wc_rkmTraj_m8_r104_s5_hb,
    wc_rkmTraj_m8_r104_s5_v0, wc_rkmTraj_m8_r104_s5_v2)) := mIter_split rfl (bSlideChk_sound bk_9)
    (bSlideChk_sound bk_10)
private theorem ws_rkmTraj_m32_r80_s2 : WalkOk (some (42, 81, wc_rkmTraj_m32_r80_s2_hb,
    wc_rkmTraj_m32_r80_s2_v0, wc_rkmTraj_m32_r80_s2_v2)) := mIter_split rfl
    (bSlideChk_sound bk_13) (bSlideChk_sound bk_14)
private theorem ws_rkmTrajPack_m32_r80_s2 : WalkOk (some (41, 81, wc_rkmTrajPack_m32_r80_s2_hb,
    wc_rkmTrajPack_m32_r80_s2_v0, wc_rkmTrajPack_m32_r80_s2_v2)) := mIter_split rfl
    (bSlideChk_sound bk_15) (bSlideChk_sound bk_18)
/-- Kernel trajectory certificate `(m = 1024, r = 20)`. -/
theorem rkmTraj_m1024_r20 : rkmEvalT16Lo12 1024 8 20 [1] [24349636] [23] rkmMasks_m1024_r20 =
  rkmRow_m1024_r20 := bh0_eq (tl2 bk_20)
/-- Kernel trajectory certificate `(m = 1024, r = 5)`. -/
theorem rkmTraj_m1024_r5 : rkmEvalT16Lo12 1024 8 5 [1] [23317052] [7] rkmMasks_m1024_r5 =
  rkmRow_m1024_r5 := bh0_eq (tl2 (tl2 bk_21))
/-- Kernel trajectory certificate `(m = 8, r = 104)`. -/
theorem rkmTraj_m8_r104 : rkmEvalT16Lo12 8 1024 104 [1, 2, 4, 8, 16, 20, 20, 20] [17900607,
  18810276, 19467357, 16634230, 11099809, 23408761, 1243517, 435150] [3, 5, 9, 14, 15, 37, 2, 1]
  rkmMasks_m8_r104 = rkmRow_m8_r104 :=
    bhW_eq bk_0 (wSkip (wSkip (wSkip (wSkip (wSkip (wCons ws_rkmTraj_m8_r104_s5 wNil))))))
/-- Kernel trajectory certificate `(m = 2, r = 22)`. -/
theorem rkmTraj_m2_r22 : rkmEvalT16Lo12 2 4096 22 [1, 2, 4] [55313573, 47436647, 54281177] [2, 3, 4]
  rkmMasks_m2_r22 = rkmRow_m2_r22 := bh0_eq (tl1 (tl2 (tl2 bk_21)))
/-- Kernel trajectory certificate `(m = 32, r = 80)`. -/
theorem rkmTraj_m32_r80 : rkmEvalT16Lo12 32 256 80 [1, 2, 4, 4, 4] [37672593, 27964751, 37544000,
  10702039, 3969736] [15, 20, 42, 12, 5] rkmMasks_m32_r80 = rkmRow_m32_r80 :=
    bhW_eq bk_1 (wSkip (wSkip (wCons ws_rkmTraj_m32_r80_s2 wNil)))
/-- Kernel trajectory certificate `(m = 16, r = 6)`. -/
theorem rkmTraj_m16_r6 : rkmEvalT16Lo12 16 512 6 [1, 1, 1] [176770137, 19274273, 10119497] [8, 2, 2]
  rkmMasks_m16_r6 = rkmRow_m16_r6 := bh0_eq (tl2 (tl2 (tl2 bk_21)))
/-- Kernel trajectory certificate `(m = 64, r = 64)`. -/
theorem rkmTraj_m64_r64 : rkmEvalT16Lo12 64 128 64 [1, 1, 2, 2, 2, 2, 2, 2] [27619054, 32055897,
  17485035, 17485035, 2618530, 2975601, 1218924, 1218924] [17, 19, 17, 17, 3, 3, 2, 2]
  rkmMasks_m64_r64 = rkmRow_m64_r64 :=
    bhW_eq bk_3 (wCons (bSlideChk_sound (tl1 bk_8)) (wCons (bSlideChk_sound (tl1 bk_15)) wNil))
/-- Kernel trajectory certificate `(m = 32, r = 7)`. -/
theorem rkmTraj_m32_r7 : rkmEvalT16Lo12 32 256 7 [1, 1, 1, 1, 1] [77719761, 38852871, 11944135,
  8222498, 4021626] [5, 3, 1, 1, 1] rkmMasks_m32_r7 = rkmRow_m32_r7 :=
    bh0_eq (tl1 (tl2 (tl2 (tl2 bk_21))))
/-- Kernel trajectory certificate `(m = 8, r = 80)`. -/
theorem rkmTraj_m8_r80 : rkmEvalT16Lo12 8 1024 80 [1, 2, 4, 8, 15, 15, 15] [23598013, 21580139,
  22199617, 19382100, 27030108, 3565229, 835315] [3, 5, 9, 13, 28, 4, 1] rkmMasks_m8_r80 =
  rkmRow_m8_r80 :=
    bhW_eq bk_16 (wSkip (wSkip (wSkip (wSkip (wCons (bSlideChk_sound bk_6) wNil)))))
/-- Kernel trajectory certificate `(m = 128, r = 8)`. -/
theorem rkmTraj_m128_r8 : rkmEvalT16Lo12 128 64 8 [1, 1, 1] [66121382, 1705270, 319395] [10, 2, 2]
  rkmMasks_m128_r8 = rkmRow_m128_r8 := bh0_eq (tl2 (tl2 (tl2 (tl2 bk_21))))
/-- Kernel trajectory certificate `(m = 64, r = 40)`. -/
theorem rkmTraj_m64_r40 : rkmEvalT16Lo12 64 128 40 [1, 1, 1] [118992250, 2566867, 752594] [47, 1, 1]
  rkmMasks_m64_r40 = rkmRow_m64_r40 := bh0_eq bk_7
/-- Kernel trajectory certificate `(m = 8, r = 8)`. -/
theorem rkmTraj_m8_r8 : rkmEvalT16Lo12 8 1024 8 [1, 2, 2, 2] [167181012, 67815506, 28625439,
  12669963] [6, 4, 3, 2] rkmMasks_m8_r8 = rkmRow_m8_r8 :=
    bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 bk_21)))))
/-- Kernel trajectory certificate `(m = 4, r = 48)`. -/
theorem rkmTraj_m4_r48 : rkmEvalT16Lo12 4 2048 48 [1, 2, 4, 8, 16, 18, 18, 18] [24080388, 27254300,
  24466873, 27810509, 10384500, 32801977, 1551053, 889519] [2, 3, 4, 8, 5, 16, 1, 1] rkmMasks_m4_r48
  = rkmRow_m4_r48 := bh0_eq (tl1 bk_13)
/-- Kernel trajectory certificate `(m = 512, r = 11)`. -/
theorem rkmTraj_m512_r11 : rkmEvalT16Lo12 512 16 11 [1] [34081402] [14] rkmMasks_m512_r11 =
  rkmRow_m512_r11 := bh0_eq (tl2 bk_9)
/-- Kernel trajectory certificate `(m = 256, r = 32)`. -/
theorem rkmTraj_m256_r32 : rkmEvalT16Lo12 256 32 32 [1, 1, 1, 1, 1, 1] [23534193, 23537905, 1314360,
  1230536, 353183, 341629] [18, 18, 1, 1, 1, 1] rkmMasks_m256_r32 = rkmRow_m256_r32 :=
    bh0_eq (tl1 bk_10)
/-- Kernel trajectory certificate `(m = 8, r = 10)`. -/
theorem rkmTraj_m8_r10 : rkmEvalT16Lo12 8 1024 10 [1, 2, 2, 2, 2] [124197936, 54162353, 53378895,
  29826025, 13050983] [5, 4, 4, 3, 2] rkmMasks_m8_r10 = rkmRow_m8_r10 := bh0_eq (tl2 bk_21)
/-- Kernel trajectory certificate `(m = 8, r = 32)`. -/
theorem rkmTraj_m8_r32 : rkmEvalT16Lo12 8 1024 32 [1, 2, 4, 7, 7, 7, 7, 7] [37434841, 39062360,
  49606189, 25440596, 23975606, 8049403, 2749419, 1102573] [3, 5, 11, 8, 8, 3, 1, 1] rkmMasks_m8_r32
  = rkmRow_m8_r32 := bh0_eq (tl1 bk_7)
/-- Kernel trajectory certificate `(m = 128, r = 11)`. -/
theorem rkmTraj_m128_r11 : rkmEvalT16Lo12 128 64 11 [1, 1, 1, 1] [56052784, 10503317, 1895937,
  748513] [11, 3, 2, 2] rkmMasks_m128_r11 = rkmRow_m128_r11 := bh0_eq (tl2 (tl2 (tl2 bk_20)))
/-- Kernel trajectory certificate `(m = 16, r = 28)`. -/
theorem rkmTraj_m16_r28 : rkmEvalT16Lo12 16 512 28 [1, 2, 3, 3, 3] [47818132, 40008833, 48822352,
  24118460, 6988463] [7, 9, 13, 7, 3] rkmMasks_m16_r28 = rkmRow_m16_r28 := bh0_eq (tl1 bk_16)
/-- Kernel trajectory certificate `(m = 1024, r = 13)`. -/
theorem rkmTraj_m1024_r13 : rkmEvalT16Lo12 1024 8 13 [1] [24140564] [18] rkmMasks_m1024_r13 =
  rkmRow_m1024_r13 := bh0_eq (tl2 bk_14)
/-- Kernel trajectory certificate `(m = 512, r = 26)`. -/
theorem rkmTraj_m512_r26 : rkmEvalT16Lo12 512 16 26 [1, 1, 1, 1] [33393723, 1021183, 222478, 168754]
  [29, 2, 2, 2] rkmMasks_m512_r26 = rkmRow_m512_r26 := bh0_eq (tl1 bk_6)
/-- Kernel trajectory certificate `(m = 4, r = 14)`. -/
theorem rkmTraj_m4_r14 : rkmEvalT16Lo12 4 2048 14 [1, 2, 4, 6, 6, 6, 6, 6] [58134444, 55688380,
  64859315, 35399105, 32807265, 10572107, 3951853, 1659779] [2, 3, 5, 4, 4, 1, 1, 1] rkmMasks_m4_r14
  = rkmRow_m4_r14 := bh0_eq (tl2 bk_15)
/-- Kernel trajectory certificate `(m = 256, r = 26)`. -/
theorem rkmTraj_m256_r26 : rkmEvalT16Lo12 256 32 26 [1] [49855494] [31] rkmMasks_m256_r26 =
  rkmRow_m256_r26 := bh0_eq (tl1 bk_19)
/-- Kernel trajectory certificate `(m = 1024, r = 16)`. -/
theorem rkmTraj_m1024_r16 : rkmEvalT16Lo12 1024 8 16 [1] [24247995] [19] rkmMasks_m1024_r16 =
  rkmRow_m1024_r16 := bh0_eq (tl1 (tl2 (tl2 bk_20)))
/-- Kernel trajectory certificate `(m = 1024, r = 25)`. -/
theorem rkmTraj_m1024_r25 : rkmEvalT16Lo12 1024 8 25 [1, 1] [23945420, 496437] [29, 2]
  rkmMasks_m1024_r25 = rkmRow_m1024_r25 := bh0_eq (tl2 bk_19)
/-- Kernel trajectory certificate `(m = 512, r = 16)`. -/
theorem rkmTraj_m512_r16 : rkmEvalT16Lo12 512 16 16 [1, 1, 1, 1] [33587572, 639291, 144227, 50000]
  [18, 1, 1, 1] rkmMasks_m512_r16 = rkmRow_m512_r16 := bh0_eq (tl1 bk_3)
/-- Kernel trajectory certificate `(m = 1024, r = 23)`. -/
theorem rkmTraj_m1024_r23 : rkmEvalT16Lo12 1024 8 23 [1, 1] [23912511, 495463] [27, 2]
  rkmMasks_m1024_r23 = rkmRow_m1024_r23 := bh0_eq (tl1 (tl2 bk_19))
/-- Kernel trajectory certificate `(m = 32, r = 16)`. -/
theorem rkmTraj_m32_r16 : rkmEvalT16Lo12 32 256 16 [1, 1, 1, 1, 1, 1, 1, 1] [45171987, 44673513,
  13120863, 12847745, 11807741, 13663535, 11432096, 7763496] [6, 6, 2, 2, 2, 2, 2, 1]
  rkmMasks_m32_r16 = rkmRow_m32_r16 := bh0_eq (tl1 bk_4)
/-- Kernel trajectory certificate `(m = 512, r = 21)`. -/
theorem rkmTraj_m512_r21 : rkmEvalT16Lo12 512 16 21 [1, 1, 1] [33393723, 1146428, 95734] [24, 2, 2]
  rkmMasks_m512_r21 = rkmRow_m512_r21 := bh0_eq (tl1 bk_5)
/-- Kernel trajectory certificate `(m = 2, r = 24)`. -/
theorem rkmTraj_m2_r24 : rkmEvalT16Lo12 2 4096 24 [1, 2, 4, 8, 16, 18, 18, 18] [31211236, 22344939,
  42194036, 37061239, 18101226, 49350000, 7911124, 2210459] [1, 1, 3, 4, 3, 9, 2, 1] rkmMasks_m2_r24
  = rkmRow_m2_r24 := bh0_eq (tl1 (tl2 bk_20))
/-- Kernel trajectory certificate `(m = 64, r = 20)`. -/
theorem rkmTraj_m64_r20 : rkmEvalT16Lo12 64 128 20 [1, 1, 1] [102258344, 3665139, 69471] [24, 2, 2]
  rkmMasks_m64_r20 = rkmRow_m64_r20 := bh0_eq (tl1 bk_20)
/-- Krotov trajectory `(m = 4, r = 96)`. -/
theorem rkmTrajPack_m4_r96 : rkmEvalT16Lo12 4 2048 96 [1,2,6,14,24,42,42,42]
  [18267857,19623003,21304676,17942660,18125378,12316825,11091626,4615239] [2,3,7,12,18,18,17,7]
  rkmMasksPack_m4_r96 = rkmRowPack_m4_r96 :=
    bhW_eq (tl1 bk_18) (wSkip (wSkip (wSkip (wSkip (wCons (bSlideChk_sound bk_11) (wCons
      (bSlideChk_sound bk_12) (wCons (bSlideChk_sound bk_17) wNil)))))))
/-- Krotov trajectory `(m = 32, r = 4)`. -/
theorem rkmTrajPack_m32_r4 : rkmEvalT16Lo12 32 256 4 [1,1,1,1,1]
  [125158640,6137295,610204,606544,353886] [5,1,1,1,1] rkmMasksPack_m32_r4 = rkmRowPack_m32_r4 :=
    bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 bk_21)))))
/-- Krotov trajectory `(m = 32, r = 80)`. -/
theorem rkmTrajPack_m32_r80 : rkmEvalT16Lo12 32 256 80 [1,2,4,4,4]
  [39093742,24917588,38716678,9847754,5294897] [14,16,41,11,6] rkmMasksPack_m32_r80 =
  rkmRowPack_m32_r80 := bhW_eq bk_2 (wSkip (wSkip (wCons ws_rkmTrajPack_m32_r80_s2 wNil)))
/-- Krotov trajectory `(m = 4, r = 60)`. -/
theorem rkmTrajPack_m4_r60 : rkmEvalT16Lo12 4 2048 60 [1,1,1,1,1,1,1,1]
  [12902371,14149758,29340260,11554616,14154075,197083,9042,7200276] [1,1,2,1,1,1,1,1]
  rkmMasksPack_m4_r60 = rkmRowPack_m4_r60 := bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21))))))
/-- Krotov trajectory `(m = 64, r = 59)`. -/
theorem rkmTrajPack_m64_r59 : rkmEvalT16Lo12 64 128 59 [2,2,2,2,2,2,2,2]
  [25688053,15982896,9526033,12319566,6500866,5278876,2969895,1929494] [21,13,8,10,6,5,3,2]
  rkmMasksPack_m64_r59 = rkmRowPack_m64_r59 :=
    bhW_eq bk_4 (wCons (bSlideChk_sound (tl1 bk_14)) wNil)
/-- Krotov trajectory `(m = 8, r = 4)`. -/
theorem rkmTrajPack_m8_r4 : rkmEvalT16Lo12 8 1024 4 [1,1,1,1,1,1,1,1]
  [75309509,76367293,32028507,26557672,25637271,30293046,13091718,10965552] [2,2,1,1,1,1,1,1]
  rkmMasksPack_m8_r4 = rkmRowPack_m8_r4 := bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21))))))
/-- Krotov trajectory `(m = 32, r = 53)`. -/
theorem rkmTrajPack_m32_r53 : rkmEvalT16Lo12 32 256 53 [3,3,3,3,3,3,3,3]
  [24915768,25113353,16784651,8580460,6583242,7492968,4299041,2551025] [16,16,11,6,5,5,3,2]
  rkmMasksPack_m32_r53 = rkmRowPack_m32_r53 := bhW_eq bk_5 (wCons (bSlideChk_sound bk_19) wNil)
/-- Krotov trajectory `(m = 8, r = 7)`. -/
theorem rkmTrajPack_m8_r7 : rkmEvalT16Lo12 8 1024 7 [1,2] [165016940,95258849] [5,4]
  rkmMasksPack_m8_r7 = rkmRowPack_m8_r7 := bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21)))))))
/-- Krotov trajectory `(m = 32, r = 44)`. -/
theorem rkmTrajPack_m32_r44 : rkmEvalT16Lo12 32 256 44 [1,2,3,3,3]
  [51516654,19245568,45671799,3280418,973092] [13,8,24,2,1] rkmMasksPack_m32_r44 =
  rkmRowPack_m32_r44 := bh0_eq bk_8
/-- Krotov trajectory `(m = 4, r = 8)`. -/
theorem rkmTrajPack_m4_r8 : rkmEvalT16Lo12 4 2048 8 [1,1,2,2,3,3,3,3]
  [30396927,81719325,24752466,48838827,47527620,49664948,37431095,12421030] [1,2,1,2,2,2,2,1]
  rkmMasksPack_m4_r8 = rkmRowPack_m4_r8 := bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21)))))))
/-- Krotov trajectory `(m = 32, r = 35)`. -/
theorem rkmTrajPack_m32_r35 : rkmEvalT16Lo12 32 256 35 [1,2,2,2,2]
  [78603477,41737972,13307343,7275143,4567755] [17,14,5,3,2] rkmMasksPack_m32_r35 =
  rkmRowPack_m32_r35 := bh0_eq (tl1 bk_11)
/-- Krotov trajectory `(m = 16, r = 8)`. -/
theorem rkmTrajPack_m16_r8 : rkmEvalT16Lo12 16 512 8 [1,1,1,1,1,1,1,1]
  [53209192,49679527,47243500,20558617,15911430,17592953,8255461,7088420] [3,3,3,1,1,1,1,1]
  rkmMasksPack_m16_r8 = rkmRowPack_m16_r8 :=
    bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_21))))))))
/-- Krotov trajectory `(m = 4, r = 112)`. -/
theorem rkmTrajPack_m4_r112 : rkmEvalT16Lo12 4 2048 112 [1,1,14,28,28,28,28,28]
  [22639971,21667069,10978452,527523,678885,1515592,417437,932728] [2,2,8,1,1,2,1,2]
  rkmMasksPack_m4_r112 = rkmRowPack_m4_r112 := bh0_eq (tl1 bk_12)
/-- Krotov trajectory `(m = 2, r = 14)`. -/
theorem rkmTrajPack_m2_r14 : rkmEvalT16Lo12 2 4096 14 [1,3,6,12]
  [47438247,58830241,63879817,64052698] [1,2,4,6] rkmMasksPack_m2_r14 = rkmRowPack_m2_r14 :=
    bh0_eq (tl1 (tl2 bk_21))
/-- Krotov trajectory `(m = 4, r = 40)`. -/
theorem rkmTrajPack_m4_r40 : rkmEvalT16Lo12 4 2048 40 [1,2,4,8,15,15,15]
  [32465837,25264303,29326333,31369223,38243178,579432,5298078] [2,2,4,8,14,1,2]
  rkmMasksPack_m4_r40 = rkmRowPack_m4_r40 := bh0_eq (tl1 bk_9)
/-- Krotov trajectory `(m = 64, r = 12)`. -/
theorem rkmTrajPack_m64_r12 : rkmEvalT16Lo12 64 128 12 [1,1,1] [94050225,4309710,2381636] [13,1,1]
  rkmMasksPack_m64_r12 = rkmRowPack_m64_r12 := bh0_eq (tl2 bk_12)
/-- Krotov trajectory `(m = 16, r = 29)`. -/
theorem rkmTrajPack_m16_r29 : rkmEvalT16Lo12 16 512 29 [1,3,3,3]
  [73911391,83670715,12090970,4318798] [8,20,3,2] rkmMasksPack_m16_r29 = rkmRowPack_m16_r29 :=
    bh0_eq (tl1 bk_17)
/-- Krotov trajectory `(m = 4, r = 13)`. -/
theorem rkmTrajPack_m4_r13 : rkmEvalT16Lo12 4 2048 13 [1,2,4,6,6,6,6,6]
  [77253892,56026260,70970791,32946965,18189557,14128667,3742041,2729746] [2,3,5,3,2,2,1,1]
  rkmMasksPack_m4_r13 = rkmRowPack_m4_r13 := bh0_eq (tl1 bk_21)
/-- Krotov trajectory `(m = 16, r = 25)`. -/
theorem rkmTrajPack_m16_r25 : rkmEvalT16Lo12 16 512 25 [1,2,2,2]
  [76979844,99490539,30776310,10746970] [8,17,5,2] rkmMasksPack_m16_r25 = rkmRowPack_m16_r25 :=
    bh0_eq bk_20
/-- Krotov trajectory `(m = 2, r = 16)`. -/
theorem rkmTrajPack_m2_r16 : rkmEvalT16Lo12 2 4096 16 [1,2,4,8,12,12,12,12]
  [46689155,41893053,49422253,59202398,25935300,21413489,7921805,5882988] [1,2,3,5,3,3,1,1]
  rkmMasksPack_m2_r16 = rkmRowPack_m2_r16 := bh0_eq bk_21
/-- Krotov trajectory `(m = 16, r = 22)`. -/
theorem rkmTrajPack_m16_r22 : rkmEvalT16Lo12 16 512 22 [1,2,2,2,2]
  [89123555,67323532,27409019,16361807,9019242] [8,10,5,3,2] rkmMasksPack_m16_r22 =
  rkmRowPack_m16_r22 := bh0_eq (tl2 bk_17)
/-- Krotov trajectory `(m = 16, r = 80)`. -/
theorem rkmTrajPack_m16_r80 : rkmEvalT16Lo12 16 512 80 [1,1,1,1,1,1,1,1]
  [13879474,13478652,25447496,12035258,6113151,7342721,4271941,3779842] [3,3,5,3,2,2,1,1]
  rkmMasksPack_m16_r80 = rkmRowPack_m16_r80 := bh0_eq (tl1 bk_2)
/-- Krotov trajectory `(m = 2, r = 24)`. -/
theorem rkmTrajPack_m2_r24 : rkmEvalT16Lo12 2 4096 24 [1,2,4,8,16,18,18,18]
  [28571613,26875562,34243345,42932435,15341358,50490723,8924918,7683510] [1,1,2,5,3,9,2,2]
  rkmMasksPack_m2_r24 = rkmRowPack_m2_r24 := bh0_eq (tl2 bk_16)
/-- Krotov trajectory `(m = 16, r = 17)`. -/
theorem rkmTrajPack_m16_r17 : rkmEvalT16Lo12 16 512 17 [1,2,2,2]
  [111498849,57471348,23447181,9028134] [9,7,3,2] rkmMasksPack_m16_r17 = rkmRowPack_m16_r17 :=
    bh0_eq (tl2 (tl2 bk_20))
end
end QuantumComputation.Specs.DickeSol
