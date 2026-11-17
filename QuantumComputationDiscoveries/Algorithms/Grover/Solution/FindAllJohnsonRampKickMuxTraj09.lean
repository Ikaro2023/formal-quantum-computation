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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxTraj07
/-
# Multi-Segment `T_16` Trajectory Part `09` (`FindAllJohnsonRampKickMuxTraj09`)

Certified kernel trajectory evaluations (`30` rows, `37990` substep-coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Mask chunk for `(m = 2, r = 32)`. -/
def rkmMkP_m2_r32_s3_p0 : List Bool := [
  true, true, true, true, false, false, false, true, false, true, true, false, false, false, true,
  true, true]
/-- Mask chunk for `(m = 2, r = 32)`. -/
def rkmMkP_m2_r32_s4_p0 : List Bool := [
  true, true, false, true, false, true, false, true, true, false, true, true, false, true, true,
  false, false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 2, r = 32)`. -/
def rkmMkP_m2_r32_s5_p0 : List Bool := [
  false, true, true, false, true, true, false, false, false, false, false, false, false, true,
  false, true, false, true, false, false, false, false, false, true, false, false, true, true]
/-- Mask chunk for `(m = 2, r = 32)`. -/
def rkmMkP_m2_r32_s6_p0 : List Bool := [
  false, false, true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true, false, false, true, false, false, false,
  true]
/-- Prefix-kick masks for `(m = 2, r = 32)`. -/
def rkmMasks_m2_r32 : List (List Bool) := [
  [], [], [true, true, false, true], rkmMkP_m2_r32_s3_p0, rkmMkP_m2_r32_s4_p0,
  rkmMkP_m2_r32_s5_p0, rkmMkP_m2_r32_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 32)`. -/
def rkmRow_m2_r32 : List ℕ := [
  563501, 74023, 3650209, 2804076, 22841102, 374286895, 461259475, 84261294, 253989, 12958368,
  65104771, 133390396, 10447818, 108656562, 133694745, 44068298, 338576965, 858961, 1390314331,
  1351977353, 660370064, 1502776905, 1034794914, 51537, 1107794426, 5934439551, 14758132784,
  552383560, 3247699156, 227574518449, 518168170331, 220918823785]
/-- Mask chunk for `(m = 2, r = 128)`. -/
def rkmMkP_m2_r128_s3_p0 : List Bool := [
  true, true, true, false, true, true, true, false, true, true, true, true, true, true, true,
  true, true, false, false, false, false, false, false, true, true, true, true, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, true]
/-- Mask chunk for `(m = 2, r = 128)`. -/
def rkmMkP_m2_r128_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, true, true, true, true,
  true, true, true, false, false, true, true, true, true, false, true, false, true, true, false,
  false, true, false, false, false, false, true, false, false, true, true, false, false, true,
  false, true, true, false, false, false, true, true, true, false, false, false, true, false,
  true, true, true, false, true, true, true]
/-- Mask chunk for `(m = 2, r = 128)`. -/
def rkmMkP_m2_r128_s4_p1 : List Bool := [
  false, false, false, false, true, true, true, true, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, false, false, true, true, false, false, false, false,
  true, false, false, true]
/-- Mask chunk for `(m = 2, r = 128)`. -/
def rkmMkP_m2_r128_s5_p0 : List Bool := [
  true, true, false, true, false, true, true, true, true, false, false, false, false, false, true,
  true, false, false, true, true, true, false, false, true, false, true, true, false, true, false,
  false, true, false, false, true, false, false, true, false, false, true, false, true, false,
  true, true, false, false, true, true, false, false, false, false, false, false, true, false,
  false, true, false, false, false, false]
/-- Mask chunk for `(m = 2, r = 128)`. -/
def rkmMkP_m2_r128_s5_p1 : List Bool := [
  true, false, false, false, false, false, true, true, false, false, true, true, false, false,
  true, true, false, false, true, true, true, false, false, true, true, true, false, false, true,
  true, true, false, false, false, false, true, true, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  false, true, true, false, false, true, true]
/-- Mask chunk for `(m = 2, r = 128)`. -/
def rkmMkP_m2_r128_s6_p0 : List Bool := [
  true, false, true, false, false, true, false, true, false, false, false, false, true, false,
  false, false, false, false, true, true, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, false, false, false, false, false,
  false, false, false, false, true, false, false, false, false, true, false, false, false, false,
  false, false, false, true, false, false, false, false]
/-- Mask chunk for `(m = 2, r = 128)`. -/
def rkmMkP_m2_r128_s6_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, false, true, false, false, false, true, true, false, false,
  false, true, true]
/-- Prefix-kick masks for `(m = 2, r = 128)`. -/
def rkmMasks_m2_r128 : List (List Bool) := [
  [], [], [], rkmMkP_m2_r128_s3_p0, rkmMkP_m2_r128_s4_p0 ++ rkmMkP_m2_r128_s4_p1,
  rkmMkP_m2_r128_s5_p0 ++ rkmMkP_m2_r128_s5_p1, rkmMkP_m2_r128_s6_p0 ++ rkmMkP_m2_r128_s6_p1, []]
/-- Row chunk `0` `(m = 2, r = 128)`. -/
def rkmRowP_m2_r128_p0 : List ℕ := [
  905, 378, 193423, 81701, 379762, 84259, 32578, 569, 913645, 989707, 164209, 127540, 1296390,
  6341, 88, 5259, 20845, 18090, 1262184, 1958189, 833776, 358559, 274549, 1279409, 4940236,
  8357213, 350495, 648940, 48661, 7369587, 9352473, 159371, 8222143, 10262020, 1330224, 636437,
  7995304, 27986718, 68704990, 73181526, 6182746, 11298204, 11440287, 3627562, 548722, 4475288,
  96925389, 135715789, 382102, 68103272, 70357428, 20619099, 7371812, 8345767, 18167275, 20989775,
  168337788, 92870757, 874448, 67321965, 53444360, 72835142, 29100846, 25449979]
/-- Row chunk `1` `(m = 2, r = 128)`. -/
def rkmRowP_m2_r128_p1 : List ℕ := [
  24438980, 133513901, 37419274, 10485001, 145467442, 134896053, 30943328, 169589, 149285136,
  421941232, 119505508, 48555121, 361677527, 264182083, 27734319, 92148823, 349244328, 219316327,
  3322040, 457131673, 150833835, 16273385, 168118053, 275954823, 55603079, 191120665, 378310954,
  3085687, 131271395, 212071647, 7413532, 263606280, 230048647, 8308058, 85527419, 14468354,
  104613022, 615671548, 44673040, 29207716, 26037635, 219569983, 967988032, 33483813, 27915722,
  428837746, 267947314, 1768646480, 912260319, 1382089265, 5702191036, 404169449, 2855507197,
  759503928, 3102374520, 20173040061, 4923364113, 916855486, 9485863486, 159758860070,
  360490738296, 298100504799, 106220066774, 13819987182]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 128)`. -/
def rkmRow_m2_r128 : List ℕ := rkmRowP_m2_r128_p0 ++ rkmRowP_m2_r128_p1
/-- Prefix-kick masks for `(m = 4, r = 8)`. -/
def rkmMasks_m4_r8 : List (List Bool) := [
  [], [], [false, true, false, false, true, true], [false, true, false, true, false, false, true],
  []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 8)`. -/
def rkmRow_m4_r8 : List ℕ := [
  62807162, 529908103, 970203634, 192353735, 8964808784, 181315285, 166468924881, 822624972014]
/-- Mask chunk for `(m = 4, r = 40)`. -/
def rkmMkP_m4_r40_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, true, false, false, false, false, true,
  true, false, false, true, false, false, true, true, false, false, false, true, true, true,
  false, false, true]
/-- Mask chunk for `(m = 4, r = 40)`. -/
def rkmMkP_m4_r40_s5_p0 : List Bool := [
  false, false, false, false, true, false, true, false, true, false, false, true, true, false,
  false, true, false, false, false, false, false, false, true]
/-- Prefix-kick masks for `(m = 4, r = 40)`. -/
def rkmMasks_m4_r40 : List (List Bool) := [
  [], [], [], [], rkmMkP_m4_r40_s4_p0, rkmMkP_m4_r40_s5_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 40)`. -/
def rkmRow_m4_r40 : List ℕ := [
  66, 93, 1, 52, 6, 56, 3, 357, 0, 1084, 20, 12552, 491, 27354, 1, 103149, 6707143, 870362,
  7600226, 918965, 201028236, 3305564, 191961877, 547854707, 2126049, 4613905757, 1392419778,
  24341221, 43662737924, 4352679537, 107782441, 55474052782, 227155046159, 316488523812,
  225403001823, 93351329044, 23297792534, 3432119928, 272804261, 8943607]
/-- Prefix-kick masks for `(m = 8, r = 4)`. -/
def rkmMasks_m8_r4 : List (List Bool) := [
  [], [], [], [true], [false, true], [false, false, true], [false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 4)`. -/
def rkmRow_m8_r4 : List ℕ := [18188776, 145511012, 65179485255, 934632421348]
/-- Prefix-kick masks for `(m = 8, r = 34)`. -/
def rkmMasks_m8_r34 : List (List Bool) := [
  [], [], [true, true, false, false, false, false, false, false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 34)`. -/
def rkmRow_m8_r34 : List ℕ := [
  924199, 1598597, 2318, 2729935, 1428321, 2583432, 3538457, 2950826, 5572123, 8658041, 3504801,
  30249340, 1067313, 86572954, 115173764, 82443163, 1046864016, 248127926, 2624611061,
  10184936348, 1339327173, 25893737369, 156591688071, 288134638883, 275498984041, 159920349814,
  60183399207, 15118013222, 2555736154, 288332645, 21136563, 953627, 23714, 244]
/-- Prefix-kick masks for `(m = 16, r = 3)`. -/
def rkmMasks_m16_r3 : List (List Bool) := [[true], [true, true], [true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 3)`. -/
def rkmRow_m16_r3 : List ℕ := [716869, 61430587387, 938568572346]
/-- Prefix-kick masks for `(m = 16, r = 12)`. -/
def rkmMasks_m16_r12 : List (List Bool) := [
  [false, true, true, false, false, true, true, true, true],
  [false, true, false, true, true, false, true, true, false, true],
  [false, true, false, true, false, true, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 12)`. -/
def rkmRow_m16_r12 : List ℕ := [
  3361, 262838, 64644, 1131949, 438000, 505851172, 256758741, 128973220, 806856034, 1010784908,
  43036961151, 954251913812]
/-- Mask chunk for `(m = 16, r = 14)`. -/
def rkmMkP_m16_r14_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true]
/-- Mask chunk for `(m = 16, r = 14)`. -/
def rkmMkP_m16_r14_s2_p0 : List Bool := [
  true, false, true, true, false, true, true, false, false, true, false, true, true]
/-- Prefix-kick masks for `(m = 16, r = 14)`. -/
def rkmMasks_m16_r14 : List (List Bool) := [
  rkmMkP_m16_r14_s0_p0, [true, false, true, false, true, true, false, true, false, true, true],
  rkmMkP_m16_r14_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 14)`. -/
def rkmRow_m16_r14 : List ℕ := [
  4777, 14062, 16635, 59213, 8621268, 2478411, 81855930, 49212506, 203179636, 5313009481,
  2184363963, 681281258, 42912852149, 948563050591]
/-- Mask chunk for `(m = 16, r = 17)`. -/
def rkmMkP_m16_r17_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true]
/-- Mask chunk for `(m = 16, r = 17)`. -/
def rkmMkP_m16_r17_s1_p0 : List Bool := [
  false, false, true, false, true, false, false, true, true, true, true, false, true, true]
/-- Mask chunk for `(m = 16, r = 17)`. -/
def rkmMkP_m16_r17_s2_p0 : List Bool := [
  false, true, false, true, false, true, true, false, false, true, false, false, true, false,
  true, true]
/-- Prefix-kick masks for `(m = 16, r = 17)`. -/
def rkmMasks_m16_r17 : List (List Bool) := [
  rkmMkP_m16_r17_s0_p0, rkmMkP_m16_r17_s1_p0, rkmMkP_m16_r17_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 17)`. -/
def rkmRow_m16_r17 : List ℕ := [
  151, 9432, 16278, 790518, 177167, 8056, 7878206, 3379112, 5516654, 1117900629, 3242604,
  797420226, 6783291697, 2941490360, 752943168, 39041420314, 948544515261]
/-- Mask chunk for `(m = 16, r = 19)`. -/
def rkmMkP_m16_r19_s1_p0 : List Bool := [
  false, false, true, true, false, false, true, true, false, true, true, true, true, false, true,
  true]
/-- Mask chunk for `(m = 16, r = 19)`. -/
def rkmMkP_m16_r19_s2_p0 : List Bool := [
  true, false, true, false, true, false, true, false, true, false, false, true, false, false,
  true, false, true, true]
/-- Prefix-kick masks for `(m = 16, r = 19)`. -/
def rkmMasks_m16_r19 : List (List Bool) := [[], rkmMkP_m16_r19_s1_p0, rkmMkP_m16_r19_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 19)`. -/
def rkmRow_m16_r19 : List ℕ := [
  43, 795, 8630, 60486, 350431, 944415, 3468269, 833585, 26637429, 7876641, 3315784, 1048785256,
  19028884, 1426557929, 8172625626, 3091841519, 1158591346, 40565095377, 944473977356]
/-- Mask chunk for `(m = 16, r = 26)`. -/
def rkmMkP_m16_r26_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 26)`. -/
def rkmMasks_m16_r26 : List (List Bool) := [rkmMkP_m16_r26_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 26)`. -/
def rkmRow_m16_r26 : List ℕ := [
  8942444, 161302269, 1578389391, 9454560570, 36982179731, 98151869138, 180871628444,
  234382309572, 214552218783, 138334692224, 62131098329, 19041600178, 3834754310, 480788555,
  32608946, 856595]
/-- Mask chunk for `(m = 16, r = 27)`. -/
def rkmMkP_m16_r27_s1_p0 : List Bool := [
  true, true, false, false, true, false, true, true, true, false, false, true, true, false, false,
  true, false, true, false, true, false, false, false, true, true]
/-- Mask chunk for `(m = 16, r = 27)`. -/
def rkmMkP_m16_r27_s2_p0 : List Bool := [
  false, true, true, true, true, true, true, false, true, false, true, false, true, true, false,
  false, true, false, true, false, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 16, r = 27)`. -/
def rkmMasks_m16_r27 : List (List Bool) := [[], rkmMkP_m16_r27_s1_p0, rkmMkP_m16_r27_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 27)`. -/
def rkmRow_m16_r27 : List ℕ := [
  20, 77, 8, 17, 19, 28, 26, 154, 2911, 24633, 81445, 805116, 452, 1080958, 128276, 5969887,
  144465406, 856778429, 767416132, 1308418764, 3811907519, 2824570463, 113006337, 15502693076,
  17702338, 40693231376, 933951715675]
/-- Mask chunk for `(m = 16, r = 32)`. -/
def rkmMkP_m16_r32_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true]
/-- Mask chunk for `(m = 16, r = 32)`. -/
def rkmMkP_m16_r32_s1_p0 : List Bool := [
  true, false, true, false, true, false, true, true, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, true]
/-- Mask chunk for `(m = 16, r = 32)`. -/
def rkmMkP_m16_r32_s2_p0 : List Bool := [
  false, true, true, true, false, true, false, true, false, false, true, true, true, false, true,
  true, false, true, false, false, false, true, true, true]
/-- Mask chunk for `(m = 16, r = 32)`. -/
def rkmMkP_m16_r32_s3_p0 : List Bool := [
  false, false, false, true, true, false, false, false, false, true, false, false, true, false,
  true, false, true, false, true, true, false, true, true, false, true, true, false, false, true,
  true]
/-- Mask chunk for `(m = 16, r = 32)`. -/
def rkmMkP_m16_r32_s4_p0 : List Bool := [
  true, false, true, false, true, false, false, true, false, false, true, false, false, false,
  false, false, false, false, true, true, true, false, true, true, true, false, false, false,
  false, false, true]
/-- Mask chunk for `(m = 16, r = 32)`. -/
def rkmMkP_m16_r32_s5_p0 : List Bool := [
  false, false, false, false, false, false, true, false, false, false, false, false, false, true,
  false, false, false, false, false, false, false, false, true, true, false, true, false, false,
  false, false, true]
/-- Mask chunk for `(m = 16, r = 32)`. -/
def rkmMkP_m16_r32_s6_p0 : List Bool := [
  false, false, true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true, false,
  false, true]
/-- Prefix-kick masks for `(m = 16, r = 32)`. -/
def rkmMasks_m16_r32 : List (List Bool) := [
  rkmMkP_m16_r32_s0_p0, rkmMkP_m16_r32_s1_p0, rkmMkP_m16_r32_s2_p0, rkmMkP_m16_r32_s3_p0,
  rkmMkP_m16_r32_s4_p0, rkmMkP_m16_r32_s5_p0, rkmMkP_m16_r32_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 32)`. -/
def rkmRow_m16_r32 : List ℕ := [
  9356, 296, 8313, 38784, 988614, 183675, 364289, 202821, 7318, 773793, 225903, 3050, 130679,
  1465942, 1928824, 10225322, 13790975, 8301774, 74556127, 1031529162, 164951940, 353474919,
  155711756, 630450372, 67605747, 450095843, 399080748, 1139660787, 16170861688, 701313987,
  50136300752, 928485755836]
/-- Prefix-kick masks for `(m = 32, r = 4)`. -/
def rkmMasks_m32_r4 : List (List Bool) := [
  [true, true], [true, true, true], [true, false, true], [true, true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 4)`. -/
def rkmRow_m32_r4 : List ℕ := [47597, 66880, 43647993245, 956351241359]
/-- Mask chunk for `(m = 32, r = 19)`. -/
def rkmMkP_m32_r19_s0_p0 : List Bool := [
  false, true, true, false, true, true, false, true, true, false, false, true, false, false, true,
  true, false, false, true, true]
/-- Prefix-kick masks for `(m = 32, r = 19)`. -/
def rkmMasks_m32_r19 : List (List Bool) := [rkmMkP_m32_r19_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 19)`. -/
def rkmRow_m32_r19 : List ℕ := [
  0, 4, 64, 179, 20, 10255, 158039, 922707, 3298858, 4047423, 4726022, 2730915, 20169052,
  605349886, 294714669, 7820091790, 1403309561, 18419279800, 971421190558]
/-- Mask chunk for `(m = 32, r = 21)`. -/
def rkmMkP_m32_r21_s0_p0 : List Bool := [
  false, true, true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true]
/-- Mask chunk for `(m = 32, r = 21)`. -/
def rkmMkP_m32_r21_s1_p0 : List Bool := [
  true, true, true, false, true, false, true, true, false, true, false, false, false, true, false,
  true, true]
/-- Mask chunk for `(m = 32, r = 21)`. -/
def rkmMkP_m32_r21_s2_p0 : List Bool := [
  false, true, false, true, false, true, false, true, true, false, true, false, true, true, false,
  true, true, false, true, true]
/-- Prefix-kick masks for `(m = 32, r = 21)`. -/
def rkmMasks_m32_r21 : List (List Bool) := [
  rkmMkP_m32_r21_s0_p0, rkmMkP_m32_r21_s1_p0, rkmMkP_m32_r21_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 21)`. -/
def rkmRow_m32_r21 : List ℕ := [
  0, 0, 85, 879, 27567, 72916, 383366, 83658, 1904595, 18331460, 31474183, 75648442, 34066084,
  102135177, 493745437, 29103552, 272321028, 4765961942, 4284111, 19818769603, 974351685673]
/-- Mask chunk for `(m = 64, r = 33)`. -/
def rkmMkP_m64_r33_s0_p0 : List Bool := [
  false, false, false, false, false, false, true, true, false, false, true, true, false, false,
  false, false, true, true, false, false, true, true, false, false, true, true, false, true, true]
/-- Mask chunk for `(m = 64, r = 33)`. -/
def rkmMkP_m64_r33_s1_p0 : List Bool := [
  false, false, true, false, true, false, false, true, false, true, true, false, true, false,
  true, false, true, false, true, false, true, false, true, false, true, true, false, true, true,
  false, true, true]
/-- Prefix-kick masks for `(m = 64, r = 33)`. -/
def rkmMasks_m64_r33 : List (List Bool) := [rkmMkP_m64_r33_s0_p0, rkmMkP_m64_r33_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 33)`. -/
def rkmRow_m64_r33 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 48, 204, 734, 1843, 5281, 3285, 103520, 264077,
  5103628, 90925253, 12042100, 8064672, 998889298, 57857551, 130022262, 3404160556, 114035200,
  9256584918, 985921934936]
/-- Prefix-kick masks for `(m = 128, r = 7)`. -/
def rkmMasks_m128_r7 : List (List Bool) := [
  [false, false, true, true, true], [false, true, false, true, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 7)`. -/
def rkmRow_m128_r7 : List ℕ := [19, 1477, 140663, 14928, 51574, 23219163244, 976780628014]
/-- Mask chunk for `(m = 128, r = 15)`. -/
def rkmMkP_m128_r15_s0_p0 : List Bool := [
  false, false, true, true, false, true, false, true, true, false, false, false, false, false,
  true, true]
/-- Mask chunk for `(m = 128, r = 15)`. -/
def rkmMkP_m128_r15_s1_p0 : List Bool := [
  false, false, false, false, false, false, true, true, false, true, false, false, true, false,
  true, true]
/-- Prefix-kick masks for `(m = 128, r = 15)`. -/
def rkmMasks_m128_r15 : List (List Bool) := [rkmMkP_m128_r15_s0_p0, rkmMkP_m128_r15_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 15)`. -/
def rkmRow_m128_r15 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 138, 46, 73379, 130323, 89417653, 3743900, 11463163405, 988443470935]
/-- Mask chunk for `(m = 128, r = 24)`. -/
def rkmMkP_m128_r24_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, false, true, true, false, true, true]
/-- Mask chunk for `(m = 128, r = 24)`. -/
def rkmMkP_m128_r24_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  true, false, true, false, true, true, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 24)`. -/
def rkmMasks_m128_r24 : List (List Bool) := [rkmMkP_m128_r24_s0_p0, rkmMkP_m128_r24_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 24)`. -/
def rkmRow_m128_r24 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 175, 4040, 185743, 1968580, 240745, 23475418,
  184670741, 19410725, 7788434596, 991981608777]
/-- Mask chunk for `(m = 128, r = 40)`. -/
def rkmMkP_m128_r40_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, true, false, true, true, false, true,
  false, true, true, false, true, true, false, false, false, false, false, true, true, false,
  false, true, false, false, true, true, true, true, true]
/-- Mask chunk for `(m = 128, r = 40)`. -/
def rkmMkP_m128_r40_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, true, false, true, false, true, false,
  true, false, true, false, false, true, false, false, true, false, true, false, true, false,
  false, false, false, false, false, false, true, false, false, true, true]
/-- Mask chunk for `(m = 128, r = 40)`. -/
def rkmMkP_m128_r40_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  true, true, true, true, false, false, false, false, false, false, true, false, false, false,
  false, false, false, false, true, true, true]
/-- Prefix-kick masks for `(m = 128, r = 40)`. -/
def rkmMasks_m128_r40 : List (List Bool) := [
  rkmMkP_m128_r40_s0_p0, rkmMkP_m128_r40_s1_p0, rkmMkP_m128_r40_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 40)`. -/
def rkmRow_m128_r40 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 107, 1234, 11023, 16429,
  119456, 928986, 2136185, 12200214, 5935576, 145305844, 1873551, 78280303, 862055410, 809303,
  5245818923, 993644506395]
/-- Mask chunk for `(m = 128, r = 56)`. -/
def rkmMkP_m128_r56_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, true, false,
  false, false, true, true, true, true, true, true, true, false, false, true, false, false, false,
  true, false, false, true, false, true, true, false, false, false, true, false, false, false,
  false, false, true, true, true, true, false, true, true]
/-- Mask chunk for `(m = 128, r = 56)`. -/
def rkmMkP_m128_r56_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, false, true, false, true, true, false,
  true, true, false, false, true, false, true, false, false, false, false, true, false, false,
  false, false, false, false, false, true, true, false, true, true, true, false, true, true]
/-- Mask chunk for `(m = 128, r = 56)`. -/
def rkmMkP_m128_r56_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, true, false, true, false,
  false, false, false, false, true, true, false, false, true, false, false, false, false, false,
  false, false, true, true, false, true, true, false, true, false, true]
/-- Prefix-kick masks for `(m = 128, r = 56)`. -/
def rkmMasks_m128_r56 : List (List Bool) := [
  rkmMkP_m128_r56_s0_p0, rkmMkP_m128_r56_s1_p0, rkmMkP_m128_r56_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 56)`. -/
def rkmRow_m128_r56 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 5, 0, 84, 361, 2908, 20911, 31349, 5036, 156333, 20145, 6826, 1335909, 19551, 3703843,
  774369871, 295336755, 13471732, 204369230, 2254910602, 18649911, 5707174046, 990726412536]
/-- Mask chunk for `(m = 128, r = 64)`. -/
def rkmMkP_m128_r64_s1_p0 : List Bool := [
  false, false, false, true, true, false, false, true, false, true, true, false, false, true,
  false, false, false, true, false, false, true, true, true, true, false, false, false, false,
  true, true, true, true, true]
/-- Mask chunk for `(m = 128, r = 64)`. -/
def rkmMkP_m128_r64_s2_p0 : List Bool := [
  true, true, false, false, false, false, false, false, false, false, false, false, false, true,
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, false, false, false, true, false, false, false, false, false,
  false, true, true, false, false, true, true, false, true, false, false, true, true, false,
  false, true, true, true, true, true]
/-- Mask chunk for `(m = 128, r = 64)`. -/
def rkmMkP_m128_r64_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, true, false, true, true, false, true,
  false, true, false, true, false, false, true, true]
/-- Mask chunk for `(m = 128, r = 64)`. -/
def rkmMkP_m128_r64_s4_p0 : List Bool := [
  false, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, false, false, false, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, true, false, true,
  false, true, true, true, true, true, true, true]
/-- Mask chunk for `(m = 128, r = 64)`. -/
def rkmMkP_m128_r64_s5_p0 : List Bool := [
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, false, false, false, false, true, false,
  false, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, true, true,
  true, false, false, true]
/-- Mask chunk for `(m = 128, r = 64)`. -/
def rkmMkP_m128_r64_s6_p0 : List Bool := [
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, false, false, false, false, false, false, true, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, true, true, true, false, true]
/-- Prefix-kick masks for `(m = 128, r = 64)`. -/
def rkmMasks_m128_r64 : List (List Bool) := [
  [], rkmMkP_m128_r64_s1_p0, rkmMkP_m128_r64_s2_p0, rkmMkP_m128_r64_s3_p0, rkmMkP_m128_r64_s4_p0,
  rkmMkP_m128_r64_s5_p0, rkmMkP_m128_r64_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 64)`. -/
def rkmRow_m128_r64 : List ℕ := [
  7, 372, 5, 21, 135, 27, 8, 10, 25, 81, 0, 51, 17, 2, 9, 70, 4, 42, 196, 0, 12, 0, 179, 0, 0, 0,
  0, 12, 285, 81, 0, 14, 6, 5, 6, 0, 105, 163, 115, 3, 5, 117, 139, 40, 9, 2, 68, 133, 3718,
  11056, 11962, 1020, 12887, 110154, 552262, 6837904, 3381175, 2012052, 2630154, 1532038996,
  927834112, 874973490, 4665317098, 991984266720]
/-- Prefix-kick masks for `(m = 256, r = 10)`. -/
def rkmMasks_m256_r10 : List (List Bool) := [
  [false, false, false, false, false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 10)`. -/
def rkmRow_m256_r10 : List ℕ := [
  0, 0, 0, 13, 1356, 113340, 408446, 5403599, 15947187924, 984046885182]
/-- Prefix-kick masks for `(m = 256, r = 12)`. -/
def rkmMasks_m256_r12 : List (List Bool) := [
  [false, false, false, false, false, false, false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 12)`. -/
def rkmRow_m256_r12 : List ℕ := [
  0, 0, 0, 0, 0, 94, 2806, 55185, 660493, 42626425, 13376736990, 986579917818]
/-- Mask chunk for `(m = 256, r = 17)`. -/
def rkmMkP_m256_r17_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, true, false, false, true,
  true]
/-- Prefix-kick masks for `(m = 256, r = 17)`. -/
def rkmMasks_m256_r17 : List (List Bool) := [rkmMkP_m256_r17_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 17)`. -/
def rkmRow_m256_r17 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 227, 22, 64484, 21342845, 231599140, 9624936832, 990122056104]
/-- Prefix-kick masks for `(m = 512, r = 7)`. -/
def rkmMasks_m512_r7 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 7)`. -/
def rkmRow_m512_r7 : List ℕ := [0, 1, 889, 13559, 105861518, 22288867439, 977605256494]
/-- Prefix-kick masks for `(m = 512, r = 12)`. -/
def rkmMasks_m512_r12 : List (List Bool) := [
  [], [false, false, false, false, false, false, false, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 12)`. -/
def rkmRow_m512_r12 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 2624, 394960, 943665, 13053449186, 986945209286]
/-- Prefix-kick masks for `(m = 1024, r = 30)`. -/
def rkmMasks_m1024_r30 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 30)`. -/
def rkmRow_m1024_r30 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 174, 2200, 1116178,
  44435982, 5227937190, 994726506579]
/-- Unpacks `j` LSB-first bits of `< 2 ^ 50` word `w` (`FindAllJohnsonRampKickMuxTraj09`). -/
def rkmWbTraj09 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWbTraj09 j (Nat.div w 2)
/-- Concatenates `50`-bit `< 2 ^ 50` chunks (final length `rem`) into a `List Bool` mask. -/
def rkmMaskWordsTraj09 : ℕ → List ℕ → List Bool
  | _, [] => []
  | rem, [w] => rkmWbTraj09 rem w
  | rem, w :: v :: ws => rkmWbTraj09 50 w ++ rkmMaskWordsTraj09 rem (v :: ws)
/-- Krotov masks `(m = 8, r = 104)`. -/
def rkmMasksPack_m8_r104 : List (List Bool) := [[], [], [], [], [],
  rkmMaskWordsTraj09 36 [422212465065984, 38668925426],
  rkmMaskWordsTraj09 37 [149533581377536, 118247265617], []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 104)`. -/
def rkmRowPack_m8_r104 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 1, 489,
  9, 12, 382, 9564, 804, 3704, 134, 82038, 37, 7000, 63897, 2055224, 44895, 44733, 95895, 4029392,
  439681, 1812256, 11713187, 63750270, 817819, 6767728, 9257413, 417880138, 126985751, 49436,
  269788320, 951567994, 390613122, 1118111842, 1723115496, 11329104189, 737782658, 2327685244,
  299199180, 11602700444, 38472300127, 28064062906, 3289228, 52305496396, 175785984077,
  250116988257, 216998658245, 129107336125, 55384913724, 17494463505, 4083066550, 696290469,
  84344732, 6870369, 337093, 7517]
/-- Krotov masks `(m = 64, r = 4)`. -/
def rkmMasksPack_m64_r4 : List (List Bool) := [[], [], [], [], [], rkmWbTraj09 1 1,
  rkmWbTraj09 2 2, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 4)`. -/
def rkmRowPack_m64_r4 : List ℕ := [95375, 43093437, 41358965781, 958597845363]
/-- Krotov masks `(m = 64, r = 64)`. -/
def rkmMasksPack_m64_r64 : List (List Bool) := [rkmWbTraj09 39 412323151872,
  rkmMaskWordsTraj09 11 [1919798, 2016], rkmMaskWordsTraj09 14 [254199761685742, 8192],
  rkmMaskWordsTraj09 11 [886837285992300, 1844], rkmMaskWordsTraj09 12 [695036975250913, 3745],
  rkmMaskWordsTraj09 13 [283914649746304, 8118], rkmMaskWordsTraj09 5 [144680943388288, 16], []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 64)`. -/
def rkmRowPack_m64_r64 : List ℕ := [5441, 12879, 29249, 279701, 74531, 11870, 4801, 45427, 9235,
  119890, 17270, 18934, 19483, 4541, 148588, 389552, 93615, 1380767, 1004, 924, 15797, 792050,
  21190, 163854, 85043, 556369, 15258, 1504692, 678904, 8736, 3205, 162160, 1408019, 1813110,
  1718577, 2404574, 776132, 847970, 31269, 902746, 731579, 11277223, 2010992, 4441702, 10847704,
  3431287, 499682, 31083120, 18426673, 11614192, 11509744, 25872721, 32186280, 80278022, 188309482,
  379915611, 41381133, 2257078244, 475255033, 246923690, 6565756647, 984371649, 9339341231,
  979260826014]
/-- Krotov masks `(m = 4, r = 56)`. -/
def rkmMasksPack_m4_r56 : List (List Bool) := [[], [], [], rkmWbTraj09 2 3, rkmWbTraj09 2 3, [],
  [], []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 56)`. -/
def rkmRowPack_m4_r56 : List ℕ := [41225890, 5775199672, 146822379544, 847361109466]
/-- Krotov masks `(m = 64, r = 60)`. -/
def rkmMasksPack_m64_r60 : List (List Bool) := [rkmWbTraj09 39 535830724608,
  rkmWbTraj09 49 422212465065986, rkmMaskWordsTraj09 9 [992014013057263, 511],
  rkmMaskWordsTraj09 10 [170356559810664, 512], rkmMaskWordsTraj09 4 [540799047963924, 12],
  rkmMaskWordsTraj09 7 [376960478497860, 65], rkmMaskWordsTraj09 9 [1080089402239760, 258], []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 60)`. -/
def rkmRowPack_m64_r60 : List ℕ := [0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 24, 2, 0, 92, 87, 32, 266, 1642,
  2092, 40, 368, 38018, 109683, 9960, 31479, 90312, 3650, 11403, 278757, 418283, 67118, 85067,
  209154, 3961, 2600110, 2825997, 675820, 65380008, 358555, 16195988, 1102609, 2872124, 54043406,
  14034389, 111684, 29099915, 33082850, 615825869, 3233153492, 101525107, 125438237, 5631657457,
  1018794774, 11202548839, 3953688483, 2166896687, 812151140, 122942082, 9793736802, 960997893331]
/-- Krotov masks `(m = 4, r = 5)`. -/
def rkmMasksPack_m4_r5 : List (List Bool) := [[], rkmWbTraj09 3 6, rkmWbTraj09 4 9, []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 5)`. -/
def rkmRowPack_m4_r5 : List ℕ := [287779768, 1320895261, 543708151, 144079112215, 853663626417]
/-- Krotov masks `(m = 4, r = 64)`. -/
def rkmMasksPack_m4_r64 : List (List Bool) := [[], [], rkmWbTraj09 1 1,
  rkmWbTraj09 42 3298534942719, rkmMaskWordsTraj09 14 [33258904586038, 8192],
  rkmMaskWordsTraj09 6 [733534836138269, 49], rkmMaskWordsTraj09 12 [926515356769999, 3291], []]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 64)`. -/
def rkmRowPack_m4_r64 : List ℕ := [3997, 3377, 67803, 919825, 833632, 155354, 14634, 300161,
  246080, 573150, 786219, 154032, 142914, 3497570, 110279, 1394315, 1087367, 115257, 2694691,
  72818, 3572737, 398398, 4550352, 170191, 6941, 1890992, 778285, 18468646, 40385812, 31756931,
  1324981, 169703681, 98953449, 67192218, 35800066, 82035757, 5061300, 10596610, 7560783,
  276997237, 177700193, 329035466, 6595137, 235773566, 314503852, 160216846, 121222487, 305313634,
  525739158, 141581153, 212699032, 2584100439, 66491364, 751623340, 1771291139, 534555147,
  1168843902, 407051355, 3811388273, 20152351861, 12246455309, 1934937609, 189124085380,
  762045806097]
/-- Krotov masks `(m = 8, r = 19)`. -/
def rkmMasksPack_m8_r19 : List (List Bool) := [[], []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 19)`. -/
def rkmRowPack_m8_r19 : List ℕ := [59184741, 1981190954, 23040505834, 117463637812, 287940921141,
  344546234354, 188397585940, 36570432467]
/-- Krotov masks `(m = 2, r = 52)`. -/
def rkmMasksPack_m2_r52 : List (List Bool) := [[], [], [], rkmWbTraj09 10 960,
  rkmWbTraj09 50 1020346657201063, rkmWbTraj09 47 124133241005462, rkmWbTraj09 45 27546284757530,
  []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 52)`. -/
def rkmRowPack_m2_r52 : List ℕ := [2031263, 342831, 193322, 161495, 462386, 2521903, 1698095,
  11988060, 331960, 670179, 2960432, 2156732, 10431412, 6066684, 25168821, 36283406, 29756,
  39746668, 18441004, 46234459, 5047273, 5060301, 65886341, 168509, 129358880, 20967, 14881198,
  28341016, 47688049, 17937707, 81224106, 530232526, 44240837, 1960226619, 353878700, 596983450,
  1723760, 100946840, 56136718, 1958445323, 737639143, 72637529, 1586880506, 1662670705,
  19984694898, 627194939, 18424234776, 311015991, 4185612, 147482537906, 509857140447,
  293042078332]
/-- Krotov masks `(m = 2, r = 7)`. -/
def rkmMasksPack_m2_r7 : List (List Bool) := [[], [], rkmWbTraj09 2 3, rkmWbTraj09 4 13,
  rkmWbTraj09 5 17, rkmWbTraj09 2 3, [], []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 7)`. -/
def rkmRowPack_m2_r7 : List ℕ := [16453, 306888495, 1935431287, 52335529, 1807481519, 428253004081,
  567643831149]
/-- Krotov masks `(m = 2, r = 44)`. -/
def rkmMasksPack_m2_r44 : List (List Bool) := [[], [], [], rkmWbTraj09 32 4294966159,
  rkmWbTraj09 44 14293613772781, rkmWbTraj09 39 482734090967, rkmWbTraj09 37 108045269984, []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 44)`. -/
def rkmRowPack_m2_r44 : List ℕ := [754259, 1690315, 236201, 7066295, 587436, 5172155, 11524719,
  15935414, 88826, 5139610, 5383970, 17538123, 19310791, 34956156, 81748453, 799974997, 270959297,
  60210597, 658642, 2109715, 10365170, 183161402, 216407412, 211454328, 9534189, 420551, 5920654,
  100841143, 53856945, 318842026, 70406637, 33299631, 503889012, 349215589, 1236763721, 10829,
  13068611305, 3531038269, 20988883106, 4626902918, 248175149, 104241038044, 505839387329,
  342810527227]
/-- Krotov masks `(m = 8, r = 56)`. -/
def rkmMasksPack_m8_r56 : List (List Bool) := [rkmWbTraj09 8 255, [], [], rkmWbTraj09 2 2,
  rkmWbTraj09 3 5, rkmWbTraj09 4 9, rkmWbTraj09 4 14, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 56)`. -/
def rkmRowPack_m8_r56 : List ℕ := [1113, 1036752, 7188230, 1662033, 25300683, 3714575045,
  151785881774, 844464308151]
/-- Krotov masks `(m = 8, r = 36)`. -/
def rkmMasksPack_m8_r36 : List (List Bool) := [[], [], rkmWbTraj09 9 307,
  rkmWbTraj09 34 13822660850, rkmWbTraj09 32 2829792683, []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 36)`. -/
def rkmRowPack_m8_r36 : List ℕ := [19, 204, 721, 23225, 12040, 786, 6746, 218, 115000, 289680,
  54519, 1561, 139070, 5162, 14796, 3299, 866220, 559036, 2061067, 17665100, 30686884, 101300512,
  24587669, 107439578, 296750438, 4824043, 396220321, 3756655009, 15683233, 9697028421, 3587866193,
  905188027, 38696596334, 254293445, 85762758934, 856340301533]
/-- Krotov masks `(m = 2, r = 11)`. -/
def rkmMasksPack_m2_r11 : List (List Bool) := [[], [], [], rkmWbTraj09 2 2, rkmWbTraj09 5 25,
  rkmWbTraj09 9 411, [], []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 11)`. -/
def rkmRowPack_m2_r11 : List ℕ := [7482265, 1821472754, 34049369, 339605834, 922044925, 1237965759,
  13666703936, 3257715750, 7978534590, 428865681485, 541852077341]
/-- Krotov masks `(m = 2, r = 36)`. -/
def rkmMasksPack_m2_r36 : List (List Bool) := [[], [], rkmWbTraj09 1 1, rkmWbTraj09 31 1073742848,
  rkmWbTraj09 31 1939471744, rkmWbTraj09 29 346644320, []]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 36)`. -/
def rkmRowPack_m2_r36 : List ℕ := [13703, 2178859, 264496, 54128578, 5153015, 5956000, 12178,
  1484232, 1258434, 2322697, 33936111, 3152021, 2942546, 12277968, 5544026, 10453499, 7212141,
  6937093, 8661779, 110393037, 28550, 389290407, 347678950, 34076089, 1806771111, 627717470,
  5180535411, 1444184572, 64277128, 28582130447, 8032169532, 671234989, 102163024250, 413695733938,
  356123195702, 80563663453]
/-- Krotov masks `(m = 16, r = 10)`. -/
def rkmMasksPack_m16_r10 : List (List Bool) := [[], [], [], rkmWbTraj09 4 14, rkmWbTraj09 7 103,
  rkmWbTraj09 8 150, rkmWbTraj09 9 261, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 10)`. -/
def rkmRowPack_m16_r10 : List ℕ := [968260, 334363, 10324695, 10748816, 5763980, 34772878,
  243636968, 707442014, 36306602189, 962679401231]
/-- Krotov masks `(m = 32, r = 25)`. -/
def rkmMasksPack_m32_r25 : List (List Bool) := [rkmWbTraj09 9 511, rkmWbTraj09 14 14782,
  rkmWbTraj09 17 127538, rkmWbTraj09 20 890291, rkmWbTraj09 22 3462931, rkmWbTraj09 23 4537027,
  rkmWbTraj09 24 8539499, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 25)`. -/
def rkmRowPack_m32_r25 : List ℕ := [26, 460, 737, 2284, 1441, 54, 4041, 2193, 119599, 428993,
  1987386, 1516777, 1139984, 274067, 5048339, 133945745, 37328330, 25070276, 208501247, 729704,
  49673003, 1495508560, 482120367, 25096332224, 972460263756]
/-- Krotov masks `(m = 64, r = 13)`. -/
def rkmMasksPack_m64_r13 : List (List Bool) := [rkmWbTraj09 11 1840, rkmWbTraj09 12 2384, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 13)`. -/
def rkmRowPack_m64_r13 : List ℕ := [0, 0, 0, 0, 278, 2411, 206971, 1391107, 21932559, 15911589,
  80380244, 14571057007, 985309117679]
/-- Krotov masks `(m = 64, r = 24)`. -/
def rkmMasksPack_m64_r24 : List (List Bool) := [[], [], rkmWbTraj09 10 976, rkmWbTraj09 16 58064,
  rkmWbTraj09 20 894570, rkmWbTraj09 22 3583438, rkmWbTraj09 23 4574533, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 24)`. -/
def rkmRowPack_m64_r24 : List ℕ := [0, 0, 0, 0, 0, 20, 12, 1, 1, 1175, 101, 10829, 118456, 337485,
  241852, 406820, 11608115, 2959124, 11797, 100918983, 188891276, 125469919, 9975088314,
  989593935384]
/-- Krotov masks `(m = 64, r = 14)`. -/
def rkmMasksPack_m64_r14 : List (List Bool) := [rkmWbTraj09 12 3688, rkmWbTraj09 13 4768, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 14)`. -/
def rkmRowPack_m64_r14 : List ℕ := [0, 0, 0, 0, 3, 684, 4710, 363141, 2216246, 28715689, 24491395,
  87276748, 13796659243, 986060271967]
/-- Krotov masks `(m = 32, r = 22)`. -/
def rkmMasksPack_m32_r22 : List (List Bool) := [rkmWbTraj09 16 58968, rkmWbTraj09 20 825003,
  rkmWbTraj09 21 1184086, []]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 22)`. -/
def rkmRowPack_m32_r22 : List ℕ := [0, 0, 0, 58, 1174, 5288, 1802, 115160, 620552, 308235, 1555113,
  362406, 46926423, 275863135, 9758335, 301088466, 74545779, 2829190, 4903712868, 45651802,
  20613457785, 973723196130]
/-- Krotov masks `(m = 16, r = 13)`. -/
def rkmMasksPack_m16_r13 : List (List Bool) := [[], rkmWbTraj09 13 8191, [], rkmWbTraj09 8 218,
  rkmWbTraj09 10 878, rkmWbTraj09 11 1118, rkmWbTraj09 12 2155, []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 13)`. -/
def rkmRowPack_m16_r13 : List ℕ := [35033, 19911, 461827, 22277873, 2507392, 47444635, 31004461,
  64041396, 198835271, 796776389, 585348838, 39187719066, 959063525089]
/-- Krotov masks `(m = 16, r = 21)`. -/
def rkmMasksPack_m16_r21 : List (List Bool) := [[], rkmWbTraj09 18 226098, rkmWbTraj09 20 861354,
  []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 21)`. -/
def rkmRowPack_m16_r21 : List ℕ := [2, 118, 3335, 15938, 472888, 95104, 10743950, 11339922,
  11272807, 40491659, 77471483, 131254326, 515660497, 1390408057, 236387218, 4362756464,
  11086595809, 2790817201, 1293344544, 41040789794, 937000078579]
/-- Krotov masks `(m = 64, r = 16)`. -/
def rkmMasksPack_m64_r16 : List (List Bool) := [rkmWbTraj09 15 32767, rkmWbTraj09 13 7349,
  rkmWbTraj09 14 9504, rkmWbTraj09 15 32016, rkmWbTraj09 15 30993, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 16)`. -/
def rkmRowPack_m64_r16 : List ℕ := [0, 167, 73, 3961, 988, 292, 23, 0, 13000, 17629, 1919281,
  10776621, 2651048, 57109372, 12520436186, 987407071164]
/-- Krotov masks `(m = 64, r = 18)`. -/
def rkmMasksPack_m64_r18 : List (List Bool) := [rkmWbTraj09 18 262143, [], rkmWbTraj09 5 24,
  rkmWbTraj09 11 2045, rkmWbTraj09 14 15542, rkmWbTraj09 16 56154, rkmWbTraj09 17 71084, []]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 18)`. -/
def rkmRowPack_m64_r18 : List ℕ := [0, 0, 0, 0, 4, 131, 1134, 1147, 3551, 3840, 1994930, 882114,
  412470, 40152782, 53569141, 115668701, 11611392509, 988175917338]
/-- Krotov masks `(m = 16, r = 18)`. -/
def rkmMasksPack_m16_r18 : List (List Bool) := [[], rkmWbTraj09 15 28454, rkmWbTraj09 17 107669,
  []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 18)`. -/
def rkmRowPack_m16_r18 : List ℕ := [674, 8470, 102577, 172110, 4968019, 13925, 1197647, 16000418,
  22620555, 15750233, 1651103000, 71639307, 1963302249, 8709685720, 2850137994, 784924851,
  38039191551, 945869180415]
/-- Cumulative `2`-lane trajectory head invariant (`Traj07` -> `Traj09`). -/
def rkmTrajLaneProp_09 : Prop :=
  rkmTrajLaneProp_07 ∧ (rkmRow_m2_r32.head? = some 563501)
/-- Proof of `rkmTrajLaneProp_09` in `O(1)` kernel steps. -/
theorem rkmTrajLaneOk_09 : rkmTrajLaneProp_09 :=
  ⟨rkmTrajLaneOk_07, rfl⟩
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
private def wc_rkmTraj_m2_r128_s4_hb_p0 : List ℕ := [152925568000000,214579807515621,
  260736183965574,298682750000000,331265966622461,359957203575865,385637255373580,408884357628191,
  430103160000000,449590466994064,467571985383919,484224341650351,499689010182818,514081518206149,
  527497752346541,540018412000000,551712236006379,562638392934660,572848286308682,582386941320133,
  591294086201910,599605006893007,607351230717966,614561079275868,621260120000000,627471538296904,
  633216446773537,638514144143140,643382333519261,647837307662197,651894107126890,655566656031977,
  658867879225058,661809803886639,664403648042184,666659898000000,668588376373886,670198302062482,
  671498343326206,672496664915491,673200970051489,673618537935408,673756257359695,673620656909036,
  673217932168227,672553970294746,671634372264122,670464473054333,669049360000000,667393889517090,
  665502702373191,663380237656500,661030745577880,658458299224145,655666805366785,652660014418241,
  649441529617352,646014815516474,642383205834776,638549910735287,634518023577103,630290527188842,
  625870299704662,621260120000000]
private def wc_rkmTraj_m2_r128_s4_hb_p1 : List ℕ := [616462672760478,611480553214174,
  606316271554500,600972257078377,595450862062078,589754365395038,583884975990092,577844835986949,
  571636023764229,565260556774050,558720394211944,552017439533821,545153542830695,538130503071025,
  530950070219693,523613947241955,516123792000000,508481219049186,500687801340453,492745071834925,
  484654525036263,476417618445909,468035773945985,459510379114267,450842788475324,442034324691643,
  433086279698266,423999915784240,414776466623947,405417138261160,395923110048510,386295535544831,
  376535543372725,366644238038502,356622700716548,346471990000000,336193142619526,325787174131885,
  315255079579809,304597834124711,293816393653576,282911695361345,271884658310011,260736183965574,
  249467156713944,238078444356802,226570898588391,214945355454126,203202635791908,191343545656914,
  179368876730655,167279406715007,155075899711909,142759106589353,130329765334308,117788601393126,
  105136328000000,92373646493976,79501246625034,66519806849682,53429994616526,40232466642220,
  26927869178221,13516838268700]
private def wc_rkmTraj_m2_r128_s4_hb : List ℕ := pCat wc_rkmTraj_m2_r128_s4_hb_p0
  wc_rkmTraj_m2_r128_s4_hb_p1
private def wc_rkmTraj_m2_r128_s4_v0_p0 : List ℕ := [1999999773507097,1999999762684724,
  1999999977617550,1999999869192058,1999999906487181,1999999313467119,1999998484476690,
  2000002761280085,1999995268053427,1999992933716485,1999991576569409,1999992666768046,
  1999996479617989,2000001542406554,2000005258554998,2000005429815670,2000001929852683,
  2000002464196926,2000003749654688,2000001532802670,2000003689780644,2000021025083188,
  2000039894917792,2000020919286065,2000311420841164,2000890360646434,2001291155310703,
  2000136530614758,2006759996307730,2023487719132370,2055423695366469,2105488803727096,
  2171949309339509,2247236535705303,2319074997268263,2373832212963552,2400792716014995,
  2395506944291426,2360821560552553,2305356957669880,2240350409480948,2176316518923298,
  2120735527068896,2077264619202952,2046247537238718,2025904898920144,2013581776936557,
  2006664779525142,2003059984310206,2001313646034994,2000526801622379,2000197086367197,
  2000068669423914,2000022234054742,2000006671514764,1999998151276420,1999999528965954,
  1999999890270524,2000000023200864,2000000004409010,2000000000742888,2000000000108783,
  2000000000013407,2000000000001308]
private def wc_rkmTraj_m2_r128_s4_v0_p1 : List ℕ := [2000000000000085]
private def wc_rkmTraj_m2_r128_s4_v0 : List ℕ := pCat wc_rkmTraj_m2_r128_s4_v0_p0
  wc_rkmTraj_m2_r128_s4_v0_p1
private def wc_rkmTraj_m2_r128_s4_v1_p0 : List ℕ := [1999997892309088,2000000447923713,
  2000002251600531,1999997279824548,2000008524221701,1999970998190083,2000067503923939,
  1999866202897605,2000231579459784,1999670354146002,2000364101905296,1999728716075532,
  2000033527970223,2000232693247707,1999689657862259,2000091826614128,2000237921760125,
  1999704467914572,1999953103581287,2000341579905088,1999885185782238,1999677309038711,
  2000213133115522,2000314004182039,1999751063078689,1999656869784821,2000222587204509,
  2000403729860555,1999867264787915,1999504161991446,1999902265084801,2000473513343627,
  2000406862085018,1999780976348394,1999378845237626,1999673057865613,2000366251016561,
  2000783792204979,2000541711567371,1999777087621792,1998955014816167,1998609194137921,
  1999168871084633,2000794074688165,2003060719072815,2004660797571396,2003607264735839,
  1998267389570034,1989000451784169,1979542827183467,1977031289389499,1990084942289452,
  2025439842113134,2084561246799814,2161882135936427,2245658084549971,2321206466697866,
  2375201922657943,2399322926955923,2391991171611805,2357869094405060,2305677989768237,
  2245386353203058,2185780905340945]
private def wc_rkmTraj_m2_r128_s4_v1_p1 : List ℕ := [2133022318492320,2090282351038975,
  2058190245403892,2035674034180928,2020830064919301,2011597228435316,2006162268216500,
  2003127179022892,2001516335771194,2000702708608611,2000311248768687,2000131743402806,
  2000053273843542,2000020572948648,2000007583812326,2000002667429536,2000000894801067,
  2000000286166960,2000000087222143,2000000025329692,2000000007007113,2000000001846264,
  2000000000463298,2000000000110721,2000000000025200,2000000000005460,2000000000001124,
  2000000000000218,2000000000000038,2000000000000005,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m2_r128_s4_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m2_r128_s4_v1 : List ℕ := pCat wc_rkmTraj_m2_r128_s4_v1_p0 (pCat
  wc_rkmTraj_m2_r128_s4_v1_p1 wc_rkmTraj_m2_r128_s4_v1_p2)
private def wc_rkmTraj_m2_r128_s4_v2_p0 : List ℕ := [2000379664166944,1999725956200531,
  1999856891981107,2000275963869817,2000051594080715,1999735642053507,1999991913956242,
  2000251157745417,1999985724567112,1999752205281044,2000015182310199,2000245873365422,
  1999998161877926,1999752991576849,1999978798506092,2000248130497782,2000062297499704,
  1999756278346179,1999884268760146,2000222663322396,2000175447399619,1999820819198247,
  1999763365753549,2000107298883470,2000285649138227,1999998095731771,1999702177658814,
  1999871822040556,2000248506962211,2000253097703797,1999870989458744,1999667876038294,
  1999949209515372,2000316315989740,2000245898418612,1999828593814373,1999630902853922,
  1999921631181999,2000325934045521,2000323613177916,1999910527492320,1999591861977013,
  1999754426734508,2000212785168378,2000447053647182,2000198239527492,1999731335964031,
  1999525239170358,1999775542285586,2000232265093458,2000485567853150,2000348408442276,
  1999954065255964,1999560672755299,1999358176916353,1999470058286463,2000011949551797,
  2000952605491697,2001811357068936,2001627492077288,1999617074492366,1996282448079334,
  1993960159675004,1995775068650013]
private def wc_rkmTraj_m2_r128_s4_v2_p1 : List ℕ := [2003095793975211,2013140300865733,
  2018975819683442,2012946673993934,1992131572379638,1962517115722800,1938756734700005,
  1938792762611287,1975740478882759,2051200808246461,2153456550013433,2261358724952759,
  2351829227641689,2407427438279481,2420924035753576,2395668897954998,2342526797508597,
  2275306619601963,2206633434333135,2145444036973411,2096318290483914,2060162855730944,
  2035514682618980,2019843451731613,2010507024887413,2005277136761272,2002515786802376,
  2001138987949219,2000489857676606,2000200167247944,2000077712876797,2000028662717205,
  2000010040625101,2000003339396243,2000001053989050,2000000315512040,2000000089518382,
  2000000024053772,2000000006115598,2000000001469731,2000000000333488,2000000000071349,
  2000000000014368,2000000000002714,2000000000000478,2000000000000076,2000000000000010,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m2_r128_s4_v2_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m2_r128_s4_v2 : List ℕ := pCat wc_rkmTraj_m2_r128_s4_v2_p0 (pCat
  wc_rkmTraj_m2_r128_s4_v2_p1 wc_rkmTraj_m2_r128_s4_v2_p2)
private def wc_rkmTraj_m2_r128_s5_hb_p0 : List ℕ := [139208882339826,195662339735799,
  238155348763515,273287074561856,303630320395585,330512729719199,354727725995912,376795318513685,
  397078804818581,415844214190990,433293511505374,449584477584224,464843276740784,479172756728581,
  492658131367863,505370990566387,517372203775308,528714069362256,539441936775225,549595451772364,
  559209526789113,568315107329757,576939784596604,585108290561717,592842902006247,600163773244187,
  607089212381103,613635912428969,619819146003653,625652930400651,631150168391109,636322768974386,
  641181751473913,645737335704559,649999020424764,653975651880913,657675483929181,661106230962411,
  664275114662225,667188905428564,669853959202008,672276250282094,674461400652497,676414706247471,
  678141160530348,679645475701730,680932101810397,682005244002311,682868878111260,683526764767614,
  683982462178546,684239337713264,684300578409795,684169200505131,683848058077784,683339850880716,
  682647131432865,681772311428968,680717667519829,679485346508484,678077370001737,676495638551138,
  674741935312600,672817929249389]
private def wc_rkmTraj_m2_r128_s5_hb_p1 : List ℕ := [670725177899087,668465129721284,
  666039126039114,663448402584291,660694090651879,657777217867771,654698708568472,651459383789436,
  648059960854741,644501052557212,640783165914296,636906700480812,632871946195194,628679080730925,
  624328166319319,619819146003653,615151839277725,610325937053941,605340995897049,600196431449127,
  594891510959434,589425344818620,583796876980373,578004874134279,572047913470812,565924368852355,
  559632395171851,553169910642085,546534576712053,539723775250690,532734582569778,525563739774309,
  518207618825760,510662183576615,502922944876246,494984908650013,486842515603306,478489570884254,
  469919161631347,461123559805622,452094107020232,442821077175718,433293511505374,423499019014359,
  413423533087298,403051011987760,392363066695842,381338493437431,369952679425043,358176837268695,
  345977003776491,333312708296203,320135167083373,306384780229581,291987571497757,276849969479694,
  260850876882749,243829080211635,225562146866198,205728511722434,183832780008602,159038199336824,
  129708324336849,91607030333557]
private def wc_rkmTraj_m2_r128_s5_hb : List ℕ := pCat wc_rkmTraj_m2_r128_s5_hb_p0
  wc_rkmTraj_m2_r128_s5_hb_p1
private def wc_rkmTraj_m2_r128_s5_v0_p0 : List ℕ := [2000379664166944,1999725956200531,
  1999856891981107,2000275963869817,2000051594080715,1999735642053507,1999991913956242,
  2000251157745417,1999985724567112,1999752205281044,1999984817689801,1999754126634578,
  2000001838122074,2000247008423151,2000021201493908,1999751869502218,1999937702500296,
  1999756278346179,1999884268760146,1999777336677604,1999824552600381,2000179180801753,
  2000236634246451,2000107298883470,1999714350861773,1999998095731771,2000297822341186,
  2000128177959444,2000248506962211,2000253097703797,2000129010541256,1999667876038294,
  1999949209515372,2000316315989740,2000245898418612,2000171406185627,1999630902853922,
  1999921631181999,1999674065954479,1999676386822084,1999910527492320,1999591861977013,
  2000245573265492,2000212785168378,1999552946352818,1999801760472508,1999731335964031,
  1999525239170358,1999775542285586,1999767734906542,1999514432146850,1999651591557724,
  1999954065255964,1999560672755299,1999358176916353,2000529941713537,2000011949551797,
  1999047394508303,1998188642931064,1998372507922712,1999617074492366,2003717551920666,
  2006039840324996,2004224931349987]
private def wc_rkmTraj_m2_r128_s5_v0_p1 : List ℕ := [2003095793975211,2013140300865733,
  2018975819683442,2012946673993934,2007868427620362,2037482884277200,2061243265299995,
  2061207237388713,2024259521117241,2051200808246461,2153456550013433,2261358724952759,
  2351829227641689,2407427438279481,2420924035753576,2395668897954998,2342526797508597,
  2275306619601963,2206633434333135,2145444036973411,2096318290483914,2060162855730944,
  2035514682618980,2019843451731613,2010507024887413,2005277136761272,2002515786802376,
  2001138987949219,2000489857676606,2000200167247944,1999922287123203,1999971337282795,
  1999989959374899,2000003339396243,2000001053989050,1999999684487960,1999999910481618,
  2000000024053772,2000000006115598,2000000001469731,2000000000333488,1999999999928651,
  2000000000014368,2000000000002714,1999999999999522,2000000000000076,2000000000000010,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m2_r128_s5_v0_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m2_r128_s5_v0 : List ℕ := pCat wc_rkmTraj_m2_r128_s5_v0_p0 (pCat
  wc_rkmTraj_m2_r128_s5_v0_p1 wc_rkmTraj_m2_r128_s5_v0_p2)
private def wc_rkmTraj_m2_r128_s5_v1_p0 : List ℕ := [2000044736689086,2000072193621468,
  2000303279343419,2000225798378699,2000355330768485,2000170906042558,1999936958324593,
  1999606216505253,1999855286092207,2000262354946407,2000041246351639,2000017854350762,
  2000052040970359,1999931870998663,2000010914188734,1999809099966995,1999996032883148,
  2000138680613270,2000060922024429,2000214541635347,1999894769639421,1999954898843054,
  1999657608061888,1999812790148433,2000314768354895,1999874993579238,1999897414817326,
  1999981126261679,2000019615407260,2000372331238081,1999840880386557,1999614031991407,
  1999990578651579,1999721206886305,1999644062368890,2000111115972634,1999927784408704,
  2000204963527974,2000015263103741,2000025093304982,1999390525467666,2000154931740992,
  2000355176105386,2000343287799643,1999798533022600,2000712369770218,1999308249100708,
  2000708963718560,1999170683523891,2001522083303137,1997974843894134,2002750232250896,
  1997861845160179,2002534567435970,1997007754707789,2001650823294279,2000128568934800,
  1996931437892480,2003551080142449,1997850663585381,1999834575340270,2001000755210889,
  1999045771482521,2001709724901154]
private def wc_rkmTraj_m2_r128_s5_v1_p1 : List ℕ := [1995995905019871,1998780388493307,
  2009070911695480,1996485326748703,1986304761728833,2006536262530992,2015127441238619,
  1991318614571981,1983485187422980,2008560365646707,2018277293520388,1992541760248798,
  1974733604806375,1995536293156687,2024924311226324,2021477145098203,1990223316300547,
  1972468926507078,1992500898635432,2033034676112028,2056488381897486,2041779905948016,
  2001461004858650,1970089012440749,1980404066797152,2044794408663000,2150519582822261,
  2268317899056503,2366598185083118,2423106166785851,2430450281408211,2395156159748421,
  2332125581566994,2258009402711852,2186429554045221,2125881215202287,2079743496248196,
  2047554493996847,2026753138206779,2014198096130102,2007090046770007,2003316232944830,
  2001444785716567,2000583068014133,2000216898341657,2000074063582769,2000023130984800,
  2000006584678349,2000001702355774,2000000398086943,2000000083845732,2000000015863643,
  2000000002709122,2000000000429608,2000000000068559,2000000000012456,2000000000002670,
  2000000000000601,2000000000000124,2000000000000020,2000000000000002,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m2_r128_s5_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m2_r128_s5_v1 : List ℕ := pCat wc_rkmTraj_m2_r128_s5_v1_p0 (pCat
  wc_rkmTraj_m2_r128_s5_v1_p1 wc_rkmTraj_m2_r128_s5_v1_p2)
private def wc_rkmTraj_m2_r128_s5_v2_p0 : List ℕ := [2000128220046653,2000026341323178,
  1999950994137308,2000019884501776,2000005634359576,1999863961263080,2000101272133163,
  2000225152933585,1999880787539254,2000081687902696,2000085929629101,2000223162360991,
  2000572263226737,2000255285101599,2000152943633517,2000095224503743,1999692902193361,
  1999982386999808,2000039954537055,1999773341081806,1999925268631410,2000292416850350,
  1999774430075298,2000297516306878,1999893684039791,2000135427104756,1999851625311568,
  2000305068320406,1999208374389881,2000409398882722,1999385322557793,2001581505743998,
  1998381450068189,2001864988922852,1997861358453031,2002227097866424,1997604115846500,
  2002147428839548,1998598015894555,1999660630849126,2001378428503089,1997846484814957,
  2002419556577793,1997956278196657,2000895625583436,2001423484298201,1997292379633024,
  2002256611311790,1998982954615309,1998080414693582,2002392509943705,1998791156968250,
  1999802219154354,2001085996888911,1998199601436315,2001250831554764,2000129165938868,
  1997390057963120,2003020965420319,2000835082440816,1995450091625138,2003536437142798,
  2003760853578695,1992745143563437]
private def wc_rkmTraj_m2_r128_s5_v2_p1 : List ℕ := [1999460830434167,2009643459674680,
  1996534979619654,1990211070187012,2007961425979263,2009747799508904,1989039641691199,
  1990535179153637,2012614140240016,2009083407989633,1986251364294560,1990110334105303,
  2013442308203294,2011105451872115,1987309663941606,1986249227847845,2010377666729146,
  2016997340217743,1993411807868774,1978039062884681,1996781223645048,2022286856679302,
  2016398304807377,1985860229523294,1971821488040505,1993859599372826,2025193507903451,
  2026769731764347,1994078157907299,1962205752240078,1967848697336705,2011652115656126,
  2057091970732579,2063077130527953,2019250648446493,1955650126473428,1922204825806699,
  1956071571806158,2059996282164843,2203091406551003,2339188076261487,2429140879584975,
  2455067576109554,2422043328613825,2350176917689224,2263522514404071,2181465585736217,
  2115011888578288,2067335476830163,2036486857722339,2018308259576873,2008501426165512,
  2003647201575559,2001442037263012,2000523766903666,2000174063411126,2000052670060658,
  2000014424180664,2000003547999009,2000000776093666,2000000148921143,2000000024574276,
  2000000003378799,2000000000365242]
private def wc_rkmTraj_m2_r128_s5_v2_p2 : List ℕ := [2000000000026905]
private def wc_rkmTraj_m2_r128_s5_v2 : List ℕ := pCat wc_rkmTraj_m2_r128_s5_v2_p0 (pCat
  wc_rkmTraj_m2_r128_s5_v2_p1 wc_rkmTraj_m2_r128_s5_v2_p2)
private def wc_rkmTraj_m2_r128_s6_hb_p0 : List ℕ := [137248301441870,192906683348881,
  234801232131848,269438172041855,299354071666321,325857876282211,349731834987569,371488633397760,
  391486452472772,409987574807317,427191120856248,443252649298888,458296547583828,472424214984170,
  485719665191367,498253479859944,510085671171883,521267800938507,531844579918238,541855095508902,
  551333768448481,560311108413001,568814318017612,576867780915854,584493460148615,591711226181885,
  598539129274738,604993627339205,611089777895691,616841400823828,622261217175562,627360968227072,
  632151518108565,636642942701755,640844606987091,644765232622778,648412957219872,651795386523759,
  654919640507815,657792394219470,660419914083925,662808090260270,664962465553657,666888261311809,
  668590400671447,670073529467793,671342035076324,672400063418842,673251534334549,673900155490098,
  674349434979816,674602692747779,674663070946618,674533543333443,674216923790685,673715874048702,
  673032910677434,672170411405950,671130620821309,669915655491543,668527508551685,666968053786421,
  665239049238171,663342140364965]
private def wc_rkmTraj_m2_r128_s6_hb_p1 : List ℕ := [661278862768439,659050644508464,
  656658808017337,654104571623052,651389050687815,648513258364711,645478105972133,642284402982292,
  638932856616662,635424071037657,631758546122028,627936675797367,623958745918693,619824931657184,
  615535294367702,611089777895691,606488204277147,601730268777587,596815534206979,591743424437346,
  586513217037813,581124034928050,575574836934823,569864407117333,563991342704524,557954040460871,
  551750681265313,545379212649973,538837328999378,532122449055525,525231690306644,518161839755137,
  510909320458813,503470153114185,495839911794626,488013672760719,479985955013481,471750650947687,
  463300945060734,454629218153302,445726933780964,436584502824063,427191120856248,417534571394156,
  407600985932886,397374548663559,386837129552338,375967823453430,364742364219309,353132369893939,
  341104355613995,328618420705154,315626468480252,302069738420135,287875296149395,272950888094667,
  257177122465390,240395056254298,222385389542852,202831086044787,181243727996653,156798347608800,
  127881546772613,90316861266959]
private def wc_rkmTraj_m2_r128_s6_hb : List ℕ := pCat wc_rkmTraj_m2_r128_s6_hb_p0
  wc_rkmTraj_m2_r128_s6_hb_p1
private def wc_rkmTraj_m2_r128_s6_v0_p0 : List ℕ := [1999871779953347,1999973658676822,
  1999950994137308,1999980115498224,2000005634359576,2000136038736920,1999898727866837,
  1999774847066415,2000119212460746,2000081687902696,2000085929629101,2000223162360991,
  2000572263226737,2000255285101599,1999847056366483,1999904775496257,1999692902193361,
  1999982386999808,1999960045462945,2000226658918194,2000074731368590,2000292416850350,
  1999774430075298,1999702483693122,1999893684039791,1999864572895244,2000148374688432,
  2000305068320406,2000791625610119,2000409398882722,1999385322557793,1998418494256002,
  1998381450068189,2001864988922852,2002138641546969,2002227097866424,1997604115846500,
  1997852571160452,1998598015894555,1999660630849126,1998621571496911,1997846484814957,
  1997580443422207,1997956278196657,1999104374416564,1998576515701799,1997292379633024,
  2002256611311790,2001017045384691,2001919585306418,2002392509943705,1998791156968250,
  1999802219154354,2001085996888911,1998199601436315,2001250831554764,1999870834061132,
  1997390057963120,2003020965420319,1999164917559184,1995450091625138,2003536437142798,
  2003760853578695,1992745143563437]
private def wc_rkmTraj_m2_r128_s6_v0_p1 : List ℕ := [2000539169565833,2009643459674680,
  1996534979619654,1990211070187012,2007961425979263,2009747799508904,2010960358308801,
  2009464820846363,2012614140240016,2009083407989633,2013748635705440,2009889665894697,
  2013442308203294,2011105451872115,2012690336058394,2013750772152155,2010377666729146,
  2016997340217743,2006588192131226,2021960937115319,2003218776354952,2022286856679302,
  2016398304807377,2014139770476706,2028178511959495,2006140400627174,2025193507903451,
  2026769731764347,2005921842092701,2037794247759922,2032151302663295,2011652115656126,
  2057091970732579,2063077130527953,2019250648446493,2044349873526572,2077795174193301,
  2043928428193842,2059996282164843,2203091406551003,2339188076261487,2429140879584975,
  2455067576109554,2422043328613825,2350176917689224,2263522514404071,2181465585736217,
  2115011888578288,2067335476830163,2036486857722339,2018308259576873,2008501426165512,
  2003647201575559,2001442037263012,1999476233096334,2000174063411126,2000052670060658,
  2000014424180664,1999996452000991,1999999223906334,2000000148921143,2000000024574276,
  1999999996621201,1999999999634758]
private def wc_rkmTraj_m2_r128_s6_v0_p2 : List ℕ := [2000000000026905]
private def wc_rkmTraj_m2_r128_s6_v0 : List ℕ := pCat wc_rkmTraj_m2_r128_s6_v0_p0 (pCat
  wc_rkmTraj_m2_r128_s6_v0_p1 wc_rkmTraj_m2_r128_s6_v0_p2)
private def wc_rkmTraj_m2_r128_s6_v1_p0 : List ℕ := [1999958344108970,1999915455113163,
  2000061394584740,1999928373845389,1999825536450655,2000057694997853,1999858495365796,
  2000213863808826,1999870394400708,1999837499983440,1999821733672158,2000037297676297,
  2000288094709237,1999909703173189,1999917146650010,2000145764573184,1999665041632909,
  2000537982888206,1999302400259203,2000749647596562,1998975006196264,2000421687885132,
  1999887860550049,2000197108530951,2000430441946696,2000224256938595,2000226984628506,
  2000516578020681,1999662944745236,2000469637585781,1998990901094928,2000559536643235,
  1999424949299372,2000293835189510,2000882238280245,1998519182752139,2000274967231540,
  2002153744312881,1998945659702837,1999430744772033,1999282154970169,1997295826849170,
  2003336985393264,2002560661398612,1999340925969442,1999554365716218,1997919053807211,
  1997536575554640,2003330375002339,1999547291444334,1999784834614216,2001482822468058,
  2002570764723189,1994776214261640,2004967478464122,1998190065694413,1994431461431917,
  2002011237558707,2004184280661559,1990150654820802,1998011926429608,2004256554936317,
  1991815276139315,1998214745504874]
private def wc_rkmTraj_m2_r128_s6_v1_p1 : List ℕ := [2000113296771012,2009314241281158,
  1989663539776598,2006129640978965,1998600042799435,2005861189958795,1996714618449172,
  1993932641173385,2009772551767386,1994185185863339,2005959525579848,1994268618296397,
  1993487715854037,2010834845723566,1993531780300547,2006793482479255,2000448946987887,
  1987803572568505,2008733125960960,1992578533289467,1998203173677964,2020185450399115,
  1993391491465626,2010867191746794,2024498634947226,1996409748893892,2011473867670161,
  2031135610349788,1989636042933178,2019038746415429,2034877127844891,1987962312802695,
  2011168374375265,2038206688990947,2000320764228349,2001720102503699,2038408086152734,
  2023542427947199,1998407331381641,2022079869466692,2041801487301124,2014660772318679,
  1995536995479984,2034384154926218,2085901758782082,2077944219938069,2008233239123147,
  1956677507386910,1996554589264414,2136146655266374,2313696636399351,2448481229397686,
  2494024866473840,2450263206498309,2350609353248181,2237946981528187,2142426016600846,
  2075245378913962,2034755701824891,2013837511698226,2004679648106319,2001322577334484,
  2000304482455386,2000054151967539]
private def wc_rkmTraj_m2_r128_s6_v1_p2 : List ℕ := [2000006461250520]
private def wc_rkmTraj_m2_r128_s6_v1 : List ℕ := pCat wc_rkmTraj_m2_r128_s6_v1_p0 (pCat
  wc_rkmTraj_m2_r128_s6_v1_p1 wc_rkmTraj_m2_r128_s6_v1_p2)
private def wc_rkmTraj_m2_r128_s6_v2_p0 : List ℕ := [1999917243903608,2000249592686721,
  1999932498618939,1999867890291378,1999938619343986,2000198417035552,1999445164053657,
  2000824490163901,1999081728602123,2000725012714572,1999701669703385,1999931899485474,
  2000032713314432,1999760156422964,1999613796410581,2000861304727932,1999328901777873,
  2000564008109635,1999633523225377,1999816175504344,2000231797417987,1999397371419900,
  2000254075498002,2000357178942013,1999443742741311,2000275969245154,2000687599366263,
  1998191058471057,2001592062249178,2000083879858921,1998732487094655,2000866003821792,
  2001248567629579,1996739379638604,2002575610200580,1998669302756769,2000556386685337,
  1998850183891753,2002221046380952,1997006225705071,2002932394312432,2001209806277361,
  1997560680609331,2001006731494717,2000664823670581,1999152520803097,1999193767696362,
  2007061769839498,1987592261228477,2006684199457225,1999476489492985,2002556593535113,
  1996664687389650,2005160621692907,1996663082403976,1990873057136935,2012456911460659,
  1994967781969824,2001057494378706,1999994920662180,2001607113922269,2003262124385571,
  1987652957228235,2009654035810006]
private def wc_rkmTraj_m2_r128_s6_v2_p1 : List ℕ := [1998728508547678,1994092441685852,
  2008120667198525,1995149878297361,2006272366423056,1997052481147094,1992015068240797,
  2014546059383953,1991031444938329,1999816921506239,2002682309642749,1989812339966725,
  2005782767735190,1997607546220730,1982890358593556,2017111645486597,1994499252191925,
  1991989671221723,2018308292332079,1982051251115603,2002498307686313,2019555543790868,
  1980637993858793,2005625968968914,2009222221136504,1978383024716025,2011687114568440,
  2012844957989608,1980570915135405,2007630620835457,2010523465019831,1977830983839744,
  1999040067723263,2017286466227577,1990777836531943,2000327779201195,2025052874256213,
  2005717114083278,1996842410622876,2026526114887958,2024594828516706,1995205848507225,
  2009310848304172,2037319466084820,2014695847160247,1985840278792818,2018428082484685,
  2061828585858173,2029882379484195,1965086595612566,1982280112385639,2079708646203538,
  2126206461862291,2041452955187287,1914055416703022,1909388436217446,2088389880417080,
  2347483334278703,2524960172328334,2536965761110275,2415584027441475,2251152959446058,
  2117862652231574,2041126876708608]
private def wc_rkmTraj_m2_r128_s6_v2_p2 : List ℕ := [2009333744095640]
private def wc_rkmTraj_m2_r128_s6_v2 : List ℕ := pCat wc_rkmTraj_m2_r128_s6_v2_p0 (pCat
  wc_rkmTraj_m2_r128_s6_v2_p1 wc_rkmTraj_m2_r128_s6_v2_p2)
private def wc_rkmTraj_m128_r64_s0_hb : List ℕ := [192367370274326,268858374939672,
  325370504669005,371181528592253,409928304433222,443496935223396,473019852565371,499242492484859,
  522687756809811,543739973509245,562691898593823,579772917955357,595166912023524,609024077097369,
  621469033634229,632606557376097,642525734825433,651303042846552,659004674476304,665688324530352,
  671404580224278,676198017738659,680108076249962,683169760987760,685414213055418,686869174001189,
  687559366130595,687506804448221,686731052334835,685249430215423,683077184286883,680227620661534,
  676712208907868,672540657832208,667720965366392,662259443544633,656160718712861,649427706265107,
  642061558290735,634061581483549,625425121435472,616147407917888,606221353813299,595637297816550,
  584382677616808,572441615613445,559794392732335,546416776705862,532279157868362,517345425864176,
  501571490988036,484903307939756,467274186662599,448601054841076,428779132097929,407674112616087,
  385110274791838,360851593460781,334570070056888,305788824184342,273769968366577,237263159697816,
  193817807563817,137082842611083]
private def wc_rkmTraj_m128_r64_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTraj_m128_r64_s0_v1_p0 : List ℕ := [2000008204884519,2000046133121892,
  2000180914841969,2000571296167961,2001540578503163,2003663425740344,2007839085811353,
  2015306005384664,2027547261282393,2046052854738656,2071947018494939,2105546971925597,
  2145972413058782,2190946261594476,2236898551499066,2279407821508834,2313910965467557,
  2336520702899839,2344745578539299,2337929148672276,2317305416740809,2285677000758059,
  2246822199019611,2204795305227933,2163287906069831,2125175017259831,2092300857417058,
  2065490656351867,2044726832954353,2029408454803620,2018619301679185,2011352367346630,
  2006665913756619,2003769428598727,2002052581701251,2001076155442673,2000543141823485,
  2000263816538544,2000123282054066,2000055403290828,2000023933504160,2000009932882200,
  2000003957938049,2000001513120621,2000000554536966,2000000194639754,2000000065360012,
  2000000020972171,2000000006421289,2000000001873091,2000000000519589,2000000000136771,
  2000000000034076,2000000000008011,2000000000001769,2000000000000363,2000000000000067,
  2000000000000010,2000000000000001,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m128_r64_s0_v1_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m128_r64_s0_v1 : List ℕ := pCat wc_rkmTraj_m128_r64_s0_v1_p0
  wc_rkmTraj_m128_r64_s0_v1_p1
private def wc_rkmTraj_m128_r64_s1_hb : List ℕ := [191410321044980,267520774388330,
  323751749937881,369334858882208,407888865170287,441290488259612,470666525778621,496758705125246,
  520087326632229,541034806193865,559892443326848,576888482702468,592205889924650,605994114049020,
  618377155532169,629459268845029,639329097274725,648062737204601,655726052353729,662376450499596,
  668064267180716,672833856806172,676724462338107,679770914851154,682004200518198,683451922870179,
  684138681216378,684086381034265,683314488374597,681840237491302,679678798729741,676843412002832,
  673345489816679,669194692675204,664398978719639,658964628581119,652896245588984,646196730632854,
  638867230070316,630907054044455,622313561353168,613082005500261,603205334627442,592673935495632,
  581475308292900,569593654411463,557009352881799,543698291994540,529631009395424,514771574381864,
  499076116599814,482490859630517,464949445207741,446369214310079,426645907854396,405645888210112,
  383194308008192,359056316335884,332905546456791,304267490508517,272407932087401,236082748883772,
  192853542246378,136400840103639]
private def wc_rkmTraj_m128_r64_s1_v1_p0 : List ℕ := [2000000000000003,2000000000000002,
  2000000000000000,2000000000000003,2000000000000002,2000000000000004,2000000000000003,
  2000000000000005,2000000000000005,2000000000000001,2000000000000001,2000000000000002,
  2000000000000007,2000000000000005,1999999999999999,2000000000000003,2000000000000004,
  2000000000000009,2000000000000000,1999999999999967,2000000000000169,2000000000002066,
  2000000000009401,2000000000015000,1999999999894468,1999999998979719,1999999995230988,
  1999999987209315,2000000000789768,2000000236673729,2000001667129569,2000008012559854,
  2000031330679147,2000105764879576,2000317178118163,2000859051323967,2002123708962260,
  2004827321472341,2010142510270103,2019775079079468,2035885169410348,2060745938758577,
  2096087208221214,2142201638776231,2197066496191637,2255871543967694,2311336012689546,
  2354979656770457,2379127451033112,2379039196232762,2354380113288108,2309424957794398,
  2251872246956051,2190710916702129,2133943635032422,2086953896443147,2051945089962819,
  2028393737970869,2014096718917999,2006294370467274,2002493403072793,2000858905217221,
  2000249203881740,2000057437027815]
private def wc_rkmTraj_m128_r64_s1_v1_p1 : List ℕ := [2000009110108307]
private def wc_rkmTraj_m128_r64_s1_v1 : List ℕ := pCat wc_rkmTraj_m128_r64_s1_v1_p0
  wc_rkmTraj_m128_r64_s1_v1_p1
private def wc_rkmTraj_m128_r56_s0_hb : List ℕ := [204530522952343,285533674009309,
  345145257482078,393262075932309,433767138042975,468675659748474,499198265812986,526132160142442,
  550036648158221,571322779148276,590303546614768,607224018031240,622280424726573,635632795061501,
  647413618789044,657733969128441,666687938584135,674355922312496,680807093014358,686101295375409,
  690290514964157,693420029087526,695529315576770,696652774020457,696820299037672,696057734579850,
  694387230544260,691827517242930,688394108867358,684099443582081,678952964948739,672961146778537,
  666127461025135,658452285763892,649932747444897,640562488202836,630331344724176,619224919547729,
  607224018031240,594303913530111,580433388011564,565573472820479,549675780434421,532680265705974,
  514512171894397,495077780253751,474258349566083,451901219476185,427806281900839,401704501322175,
  373221921985002,341815039278478,306643566217989,266285347265067,217957256618368,154459481989781]
private def wc_rkmTraj_m128_r56_s0_v1 : List ℕ := [2000000000072793,2000000000724524,
  2000000004997661,2000000027584156,2000000129201808,2000000530354362,2000001947018974,
  2000006482556193,2000019774934760,2000055697288788,2000145724697909,2000355894682501,
  2000814557919219,2001752921833195,2003556643449959,2006819738941851,2012382455284622,
  2021325272967893,2034886984583793,2054281988001216,2080414857248423,2113527645165086,
  2152857803621181,2196415355880373,2240988521216628,2282445998201329,2316325617200786,
  2338605240398153,2346476761506285,2338920262545498,2316918216384526,2283248426152651,
  2241915176608045,2197377455843150,2153776883779544,2114345161079741,2081096495341737,
  2054816806920522,2035282715953712,2021601710703905,2012564808595181,2006933291284932,
  2003623333662016,2001789812522495,2000833742486353,2000365251529336,2000149991935518,
  2000057510222532,2000020489116025,2000006741893918,2000002033168976,2000000556272766,
  2000000136166538,2000000029222349,2000000005324282,2000000000776564,2000000000078524]
private def wc_rkmTraj_m128_r56_s0_v2 : List ℕ := [2000000000000000,1999999999999999,
  2000000000000001,2000000000000003,2000000000000005,1999999999999998,1999999999999996,
  2000000000000003,2000000000000002,2000000000000004,2000000000000001,2000000000000002,
  2000000000000007,2000000000000005,1999999999999996,1999999999999991,1999999999999990,
  2000000000000002,2000000000000004,1999999999999998,2000000000000003,2000000000000002,
  1999999999999989,2000000000000046,2000000000000088,1999999999999415,1999999999999474,
  2000000000005763,2000000000001672,1999999999948848,2000000000007496,2000000000416653,
  1999999999814120,1999999996827056,2000000001967192,2000000022959629,1999999984854712,
  1999999840347511,2000000088102405,2000001070887072,1999999692369978,1999993122334010,
  1999999034914091,2000041275336821,2000031168279188,1999781219977979,1999634611552706,
  2000877210372750,2003038813909527,1999174574175615,1982198177901916,1972975268648726,
  2039736208323072,2244017994541120,2522103436091567,2658811254527462,2480826241722647]
private def wc_rkmTrajPack_m8_r104_s5_hb_p0 : List ℕ := [167757746444699,235362947845425,
  285953343699880,327526490150723,363206175256845,394607189937276,422696197240053,448107794812831,
  471286053026114,492556663512161,512167269889637,530311633003781,547144918301650,562793799284462,
  577363379824686,590942082412686,603605189936520,615417469375912,626435153263909,636707461718307,
  646277789264273,655184642757065,663462391569575,671141874165332,678250893395501,684814624568160,
  690855954410430,696395764742889,701453171522645,706045727556416,710189595411389,713899695701882,
  717189834892337,720072815952562,722560534571599,724664063140163,726393724317184,727759155680242,
  728769366705398,729432789115612,729757321468644,729750368717140,729418877359508,728769366705398,
  727807956700416,726540392688141,724972067431212,723108040665337,720953056418973,718511558295873,
  715787702886730,712785371448829,709508179968208,705959487696859,702142404237183,698059795227005,
  693714286660357,689108267861603,684243893112865,679123081916723,673747517857367,668118646003254,
  662237668772421,656105540157208]
private def wc_rkmTrajPack_m8_r104_s5_hb_p1 : List ℕ := [649722958177606,643090355400898,
  636207887328546,629075418408272,621692505378191,614058377588769,606171913874642,598031615458737,
  589635574261304,580981435851052,572066356107184,562886950450398,553439234235007,543718552556271,
  533719497293664,523435808650370,512860257717799,501984505629799,490798933586691,479292436298523,
  467452169035617,455263235209597,442708296827020,429767083625894,416415767225824,402626152592784,
  388364617897641,373590700952123,358255177988136,342297394353659,325641459753158,308190659391533,
  289818944262888,270357396157115,249571500256093,227120241937193,202475383500660,174740124793235,
  142152181689010,100129032536011]
private def wc_rkmTrajPack_m8_r104_s5_hb : List ℕ := pCat wc_rkmTrajPack_m8_r104_s5_hb_p0
  wc_rkmTrajPack_m8_r104_s5_hb_p1
private def wc_rkmTrajPack_m8_r104_s5_v0_p0 : List ℕ := [2000000001020174,1999999999897940,
  2000000014575467,2000000032700740,2000000117482756,2000000273637965,2000000549912527,
  2000000924143781,2000001239763895,2000001286111010,2000000881475283,2000000071390463,
  1999999272996576,1999999032700416,1999999549457409,2000000413828216,2000000861697497,
  2000000465202352,1999999629818421,1999999213820148,1999999567556057,2000000176710280,
  2000000451018986,2000000620880417,2000001329101797,2000002323358470,2000002605725606,
  2000002874428908,2000006265094281,2000012468333925,2000009980839901,1999983189205113,
  1999942155632825,1999945548867884,2000060254149243,2000247518485193,2000283607185548,
  1999889004114510,1999099086113785,1998585940624946,1999439590077143,2002194713026201,
  2005628062721769,2006477246304226,2001007998427230,1988121355970465,1972218178500730,
  1963553107964051,1974968031291280,2016110651141893,2088029922366417,2181120210372193,
  2277657558784249,2357750307676768,2405898211921021,2415357478148295,2388900151823032,
  2336354560803390,2270533585124152,2203364261017547,2143422664022705,2095182333293889,
  2059584962233361,2035254022416147]
private def wc_rkmTrajPack_m8_r104_s5_v0_p1 : List ℕ := [2019745543829909,2010483156661814,
  2005281428054918,2002527183711738,2001149388115498,2000497161157905,2000204611255462,
  2000080152219301,2000029892483337,2000010615332160,2000003589677263,2000001155884506,
  2000000354372944,2000000103420541,2000000028722960,2000000007588676,2000000001906406,
  2000000000455129,2000000000103187,2000000000022197,2000000000004524,2000000000000869,
  2000000000000156,2000000000000024,2000000000000002,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m8_r104_s5_v0 : List ℕ := pCat wc_rkmTrajPack_m8_r104_s5_v0_p0
  wc_rkmTrajPack_m8_r104_s5_v0_p1
private def wc_rkmTrajPack_m8_r104_s5_v1_p0 : List ℕ := [2000000000640444,2000000002113187,
  2000000004267009,2000000005724860,2000000004596910,2000000000596506,1999999996486723,
  1999999996113634,1999999999953951,2000000003593870,2000000002533330,1999999998203722,
  1999999996560498,1999999999888361,2000000003227803,2000000001550747,1999999997533226,
  1999999997593776,2000000001796622,2000000003620518,1999999999734589,1999999992915879,
  1999999984168617,1999999974412456,1999999987535831,2000000088548306,2000000356708594,
  2000000810814658,2000001335568579,2000001675315804,2000001535780468,2000000784179431,
  1999999668908306,1999998878653792,1999999181216853,2000000579401674,2000001649404403,
  2000000426772196,1999997204333217,1999996319808955,2000002234828018,2000010880674944,
  2000007979934061,1999985657907899,1999965057121878,1999987560075921,2000058264063600,
  2000098647905628,2000004028866925,1999803027241501,1999735344078273,2000044375214825,
  2000584248539246,2000717228127716,1999884661120054,1998495898000913,1998075227638380,
  1999966060872660,2003418442002277,2005161327845759,2001827394108187,1993857098925466,
  1987177735611327,1989824494318877]
private def wc_rkmTrajPack_m8_r104_s5_v1_p1 : List ℕ := [2004858936475184,2025073435010966,
  2034954114934483,2020364469661055,1980069019593454,1930785712961803,1901232514679865,
  1917953650342145,1991184324526170,2108863944114323,2241667599405289,2355533612794636,
  2424716931735874,2439379483663750,2405620924985696,2339817797347218,2261086428768398,
  2185262273178054,2122004748501162,2074827004499382,2042844792404483,2022942017723414,
  2011500905668764,2005400720258906,2002376006401800,2000979027067411,2000377562520328,
  2000136126073777,2000045810330681,2000014359555619,2000004181138858,2000001126991714,
  2000000279965735,2000000063736823,2000000013200009,2000000002462484,2000000000408168,
  2000000000058914,2000000000007168,2000000000000689,2000000000000043]
private def wc_rkmTrajPack_m8_r104_s5_v1 : List ℕ := pCat wc_rkmTrajPack_m8_r104_s5_v1_p0
  wc_rkmTrajPack_m8_r104_s5_v1_p1
private def wc_rkmTrajPack_m8_r104_s5_v2_p0 : List ℕ := [2000000000000006,2000000000000006,
  1999999999999998,2000000000000007,2000000000000007,2000000000000003,2000000000000006,
  2000000000000001,1999999999999994,1999999999999897,1999999999999523,1999999999998906,
  2000000000000831,2000000000020355,2000000000107729,2000000000382732,2000000001049203,
  2000000002316162,2000000004159721,2000000006005503,2000000006671552,2000000004993308,
  2000000001047280,1999999996917256,1999999995618157,1999999998304064,2000000002411224,
  2000000003638830,2000000000668648,1999999997114361,1999999997309440,2000000000777332,
  2000000003204715,2000000002341742,1999999998983881,1999999993504397,1999999990825469,
  2000000005884325,2000000036116261,2000000024771361,1999999928011365,1999999870155761,
  2000000059934422,2000000326985585,2000000058234754,1999999324766346,1999999664985429,
  2000001715991453,2000001915788292,1999996375799810,1999991348292741,2000000903121264,
  2000021131440376,2000017589608862,1999972762918955,1999945533957168,2000014559172053,
  2000119709152951,2000064184049616,1999821138340541,1999741460865898,2000130243180455,
  2000573218439993,2000218491139744]
private def wc_rkmTrajPack_m8_r104_s5_v2_p1 : List ℕ := [1999158481159611,1998938143633105,
  2000582836502591,2002295273571085,2000961579291505,1997010320157258,1995789667042860,
  2001078361004388,2007755553363308,2005569287387094,1993158536992681,1984571282371324,
  1994906189362728,2018281221020131,2027406596138339,2002970323395361,1962537491693589,
  1951055794086716,1994688583213067,2064591894493976,2093709761698517,2037031428206139,
  1919541295931986,1825477897290157,1836940684191565,1974050685921704,2183050953496013,
  2375057241330625,2480211773001051,2479046847657420,2398173591174548,2283934927880758,
  2176190307835835,2095733096656855,2045583589574134,2018946199152755,2006811090003158,
  2002083111183545,2000526452179306,2000103921267942,2000013906605343]
private def wc_rkmTrajPack_m8_r104_s5_v2 : List ℕ := pCat wc_rkmTrajPack_m8_r104_s5_v2_p0
  wc_rkmTrajPack_m8_r104_s5_v2_p1
private def wc_rkmTrajPack_m8_r104_s4_hb_p0 : List ℕ := [170755970121901,239381019904297,
  290603090180000,332582911880961,368510686951272,400036869970906,428150263388216,453500518693034,
  476542607255838,497610488447680,516958303397292,534785065416669,551250284702664,566484298083622,
  580595348682716,593674586909878,605799695126072,617037573634216,627446369879536,637077037695111,
  645974553581043,654178878266697,661725726108810,668647187456745,674972237071084,680727153205108,
  685935865896727,690620248619127,694800364202699,698494673531291,701720213701020,704492750948495,
  706826912593474,708736301417285,710233595253973,711330634062905,712038496347787,712367566463936,
  712327594095335,711927746972000,711176657726056,710082465643740,708652853954043,706895083198117,
  704816021142962,702422169635394,699719688735344,696714418419259,693411898103292,689817384200611,
  685935865896727,681772079300174,677330520102602,672615454861649,667630931001435,662380785608609,
  656868653086266,651097971713335,645071989142882,638793766858827,632266183596544,625491937718319,
  618473548519290,611213356422886]
private def wc_rkmTrajPack_m8_r104_s4_hb_p1 : List ℕ := [603713522006419,595976023776757,
  588002654592241,579795016599329,571354514519796,562682347085319,553779496369276,544646714708318,
  535284508836023,525693120763914,515872504836533,505822300250777,495541798156548,485029902234642,
  474285081362747,463305312609843,452088012313059,440629952346625,428927157829472,416974781348858,
  404766947173905,392296556704298,379555043256364,366532059784783,353215076569460,339588856128610,
  325634757773333,311329801101279,296645380724948,281545463420874,265983994262350,249901051509998,
  233216939665062,215822712785919,197564128110663,178212533173212,157406963294668,134523090972329,
  108311489053706,75464190250802]
private def wc_rkmTrajPack_m8_r104_s4_hb : List ℕ := pCat wc_rkmTrajPack_m8_r104_s4_hb_p0
  wc_rkmTrajPack_m8_r104_s4_hb_p1
private def wc_rkmTrajPack_m8_r104_s4_v0_p0 : List ℕ := [2000001596589312,2000000632621389,
  1999999036422080,1999999294245796,2000000784746305,2000001008267339,2000000114965061,
  2000000637508240,2000002941498449,2000004479318665,2000003843762574,2000002301476739,
  2000000844440609,1999998961157101,1999997291931801,1999998060930429,2000000774827587,
  1999999998622672,1999993520844559,1999996735072691,2000042365082910,2000130352377702,
  2000119925620126,1999665654384421,1998448571537541,1996942491166762,1997575623910976,
  2005510501937447,2027924414613681,2071226024933517,2137050381291618,2219200610285109,
  2303763674482128,2373056192136614,2411792260608977,2412482026742915,2377521585064930,
  2317334679196746,2245945013351355,2176290231381774,2117144953048852,2072298639341968,
  2041501675779235,2022181328104465,2011046175601062,2005127738287319,2002219189059788,
  2000895288396253,2000336555449379,2000117807705042,2000038359767699,2000011603076508,
  2000003254621953,2000000844671130,2000000202261960,2000000044529519,2000000008973357,
  2000000001645756,2000000000272687,2000000000040414,2000000000005282,2000000000000594,
  2000000000000054,2000000000000003]
private def wc_rkmTrajPack_m8_r104_s4_v0_p1 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m8_r104_s4_v0 : List ℕ := pCat wc_rkmTrajPack_m8_r104_s4_v0_p0
  wc_rkmTrajPack_m8_r104_s4_v0_p1
private def wc_rkmTrajPack_m64_r64_s1_hb : List ℕ := [234892384000000,326997557726715,
  394131620167760,447763607000000,492408129394672,530415978604490,563204317340172,591709866362627,
  616592508000000,638339400244985,657323356365067,673837931254558,688119684466481,700362937628399,
  710729915142935,719357926000000,726364582413857,731851676816934,735908118208032,738612194092008,
  740033339270935,740233537662065,739268446726212,737188309246918,734038700000000,729861142731294,
  724693624179431,718571025571944,711525487376657,703586719625592,694782267515673,685137739998832,
  674677007541333,663422374041491,651394726962408,638613669000000,625097634020834,610863989535154,
  595929127592105,580308545677259,564016918942043,547068164889085,529475501467941,511251499395052,
  492408129394672,472956804959507,452908421147466,432273389861415,411061672000000,389282806817518,
  366945938788144,344059842233240,320632943939076,296673343965223,272188834820483,247186919162964,
  221674826163255,195659526654315,169147747178280,142145983028587,114660510375558,86697397554440,
  58262515586914,29361548000000]
private def wc_rkmTrajPack_m64_r64_s1_v0_p0 : List ℕ := [2006133949493292,2021282548268760,
  2051323290830587,2099305835356558,2163481922480341,2236428069701179,2306484413915572,
  2361070691351805,2390481836720712,2390590943812967,2363510686412395,2316247146950687,
  2258169829422871,2198387494559097,2143874223256463,2098686373550464,2064140486724603,
  2039562069706724,2023188007454327,2012928911468054,2006863939906866,1996527607572876,
  1998325063627411,2000770722377049,2000338449708281,2000141875527953,2000056782688876,
  2000021699868917,2000007918262608,2000002758645172,2000000917444429,2000000291185743,
  2000000088169579,2000000025458952,2000000007006676,2000000001836835,2000000000458361,
  1999999999891216,1999999999975470,2000000000005249,2000000000001063,2000000000000202,
  2000000000000035,2000000000000005,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m64_r64_s1_v0_p1 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m64_r64_s1_v0 : List ℕ := pCat wc_rkmTrajPack_m64_r64_s1_v0_p0
  wc_rkmTrajPack_m64_r64_s1_v0_p1
private def wc_rkmTrajPack_m64_r64_s1_v1_p0 : List ℕ := [2001148587332454,1999060215691751,
  1999645965774270,2001073222000516,1999814908487271,1999013781554161,2000602154735012,
  2000764292994638,1999106871649003,1999524636080992,2001064272884713,2000173310448741,
  1998862802465536,2000104388256595,2001142474777752,1999663995281128,1998887105817857,
  2000511916397894,2001078508796153,1999371114318174,1998942285380013,2000721727251824,
  2001225221239515,1999780005362684,2000179885081780,2004063087795965,2009396836641671,
  2016865321521129,2032062867531337,2059609170634302,2099223656262738,2148794412039032,
  2207058125924735,2270462238281802,2329631421391471,2372037123753759,2388637199778756,
  2377632383956899,2343104540416470,2291864010455734,2231644146862880,2170439462246824,
  2115476865488965,2071660070319609,2040598056273636,2020973355179604,2009886343243394,
  2004261099791657,2001684713827370,2000613355668674,2000206373359446,2000064318644094,
  2000018561567477,2000004940688663,2000001203587727,2000000265335292,2000000052193610,
  2000000009010628,2000000001339115,2000000000167360,2000000000017065,2000000000001357,
  2000000000000076,2000000000000002]
private def wc_rkmTrajPack_m64_r64_s1_v1_p1 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m64_r64_s1_v1 : List ℕ := pCat wc_rkmTrajPack_m64_r64_s1_v1_p0
  wc_rkmTrajPack_m64_r64_s1_v1_p1
private def wc_rkmTrajPack_m64_r64_s2_hb : List ℕ := [203414336222157,284297944075083,
  344055362087294,392497148288956,433469012057743,468965368536143,500183680799264,527912192581739,
  552703834082125,574965003841911,595005269796131,613067190643047,629345206403820,643998138610553,
  657157764225068,668934875883244,679423676004851,688705033245360,696848941869570,703916409898824,
  709960929590484,715029636974796,719164236078231,722401742354751,724775085229242,726313599347261,
  727043426727385,726987846616707,726167545850562,724600839503625,722303849307028,719290645495246,
  715573356292822,711162248047893,706065777984749,700290620615016,693841667959026,686722002831400,
  678932843481846,670473456790093,661341035914954,651530536690749,641034465012320,629842604760519,
  617941672216198,605314877985254,591941370598081,577795526215122,562846034794144,547054712291689,
  530374937089347,512749560259794,494108061976280,474362599379130,453402374931012,431085370115005,
  407225772267934,381574002149411,353783225415882,323349176146186,289491592640857,250888329299702,
  204948066906591,144955017045848]
private def wc_rkmTrajPack_m64_r64_s2_v0_p0 : List ℕ := [2001148587332454,2000939784308249,
  2000354034225730,2001073222000516,2000185091512729,2000986218445839,2000602154735012,
  2000764292994638,2000893128350997,2000475363919008,2001064272884713,1999826689551259,
  1998862802465536,2000104388256595,1998857525222248,1999663995281128,2001112894182143,
  2000511916397894,1998921491203847,2000628885681826,2001057714619987,2000721727251824,
  2001225221239515,1999780005362684,2000179885081780,2004063087795965,2009396836641671,
  2016865321521129,2032062867531337,2059609170634302,2099223656262738,2148794412039032,
  2207058125924735,2270462238281802,2329631421391471,2372037123753759,2388637199778756,
  2377632383956899,2343104540416470,2291864010455734,2231644146862880,2170439462246824,
  2115476865488965,2071660070319609,2040598056273636,2020973355179604,2009886343243394,
  2004261099791657,2001684713827370,2000613355668674,2000206373359446,2000064318644094,
  2000018561567477,2000004940688663,2000001203587727,1999999734664708,1999999947806390,
  1999999990989372,1999999998660885,1999999999832640,1999999999982935,2000000000001357,
  2000000000000076,2000000000000002]
private def wc_rkmTrajPack_m64_r64_s2_v0_p1 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m64_r64_s2_v0 : List ℕ := pCat wc_rkmTrajPack_m64_r64_s2_v0_p0
  wc_rkmTrajPack_m64_r64_s2_v0_p1
private def wc_rkmTrajPack_m64_r64_s2_v1_p0 : List ℕ := [1999761264364406,1999971050797747,
  1999001853407158,1999683007813967,2000402346688213,2000278135039188,2000133558210792,
  1999799007369584,2000675540683793,2001128539906231,1999816780251514,1999636464434034,
  2001139121129823,2001217329387021,1999910907300791,1999907458680100,2000879585909875,
  2000789998350261,2000120905915304,2000299770167278,2000743423641927,2000529070343703,
  2000315112569821,2000544688333686,2000420623005601,2000075596752274,2000828918465964,
  2002136927353357,2001627553660615,1999420949529202,1998698897389101,2000390689269125,
  2001300780933799,1999619160389897,1998159692391496,1999365781630832,2001051762229556,
  2000482435093390,1999197289447103,1999928650688352,2001569054946842,2001352507566282,
  1999955701429961,1999940077048383,2000143074619934,1996484355738346,1989981343225517,
  1991704021698331,2018146802945779,2081130755420065,2179375194828379,2295315917991848,
  2398770413149864,2458100398757519,2454921116432007,2393354920847867,2296984351713182,
  2195780992364520,2112399447623451,2055881121101793,2023822137390643,2008564221945113,
  2002522486141896,2000575551486345]
private def wc_rkmTrajPack_m64_r64_s2_v1_p1 : List ℕ := [2000088312659301]
private def wc_rkmTrajPack_m64_r64_s2_v1 : List ℕ := pCat wc_rkmTrajPack_m64_r64_s2_v1_p0
  wc_rkmTrajPack_m64_r64_s2_v1_p1
private def wc_rkmTrajPack_m64_r60_s2_hb : List ℕ := [241437810234137,335931670612217,
  404678508098477,459485713148914,505003411792055,543654074302389,576898710284318,605703422291645,
  630749059165150,652538445688275,671456521119786,687806489635419,701832762828892,713736170253707,
  723684413275293,731819469838972,738262975889775,743120223791634,746483190928457,748432872841155,
  749041107702078,748372022166406,746483190928457,743426576702282,739249299610688,733994272463631,
  727700729447670,720404669231460,712139228685445,702934999820845,692820299832225,681821402040135,
  669962733905435,657267047001181,643755562789656,629448097190544,614363166184295,598518074022867,
  581928984970481,564610978818177,546578089644661,527843326347284,508418672217223,488315059092704,
  467542309090800,446109033092460,424022469186173,401288234666723,377909949215557,353888659418579,
  329221945679031,303902500909020,277915790265897,251236025214538,223818840373262,195586980364855,
  166399527343262,135976330033271,103670764267654,67483919502778]
private def wc_rkmTrajPack_m64_r60_s2_v0 : List ℕ := [2000000000000901,1999999999999490,
  2000000000024639,2000000000215558,2000000001618965,2000000010264562,2000000056252211,
  2000000271321687,2000001166526279,2000004514910566,2000015854361455,2000050833220098,
  2000149594683315,2000405836549518,2001018717656305,2002373487362753,2005146563261047,
  2010409945921279,2019680925025794,2034838127749432,2057825526672215,2090114015853911,
  2131991126529943,2181876133836773,2235948898437998,2288365343458886,2332174064013014,
  2360783686446840,2369569643400079,2357087059803581,2325455897075366,2279778465508723,
  2226807006972925,2173334911998707,2124830454374057,2084669281543012,2054052245198253,
  2032451774249358,2018305971207326,2009691765096488,2004809744782525,2002234204698305,
  2000969814049003,2000392644887782,2000147952795664,2000051759580902,2000016764092164,
  1999994989451449,1999998623165483,2000000346321224,2000000079334006,2000000016451013,
  2000000003065625,2000000000508834,2000000000074393,2000000000009442,2000000000001018,
  2000000000000089,2000000000000005,2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m64_r60_s2_v1 : List ℕ := [2000000000000050,1999999999999628,
  2000000000001922,1999999999991969,2000000000028940,1999999999907180,2000000000270393,
  1999999999274891,2000000001807356,1999999995783375,2000000009257604,1999999980798552,
  2000000037738355,1999999929564700,2000000125009950,1999999788870742,2000000339351856,
  1999999481296370,2000000752818857,1999998965423225,2000001340420977,1999998373209006,
  2000001831497213,1999998120939468,2000001690756851,1999998777012208,2000000543064078,
  2000000210269508,1999998894419700,2000002164956672,1999998078292891,1999998953034975,
  2000000448248809,2000009744867386,2000000031868407,1999952574657493,1999991397783533,
  2000182111348303,2000142747320672,1999391443329299,1998939254851710,2001261836370284,
  2005326296695815,2002325069239270,1984513513955316,1965771088507478,1987823785849175,
  2089713262603788,2261475666121986,2433728542403277,2523397845063187,2494491732236507,
  2377284601054625,2235645255737461,2120929241749984,2050797669334767,2017271139790737,
  2004655701412214,2000960229276559,2000141893034769,2000012863521448]
private def wc_rkmTrajPack_m4_r64_s4_hb : List ℕ := [220020833607418,307033578127433,
  370986094918754,422541939682998,465888369242587,503200614099565,535786969875928,564510194562717,
  589976640260591,612632872074634,632819792230560,650805137136984,666804077068869,680992857119538,
  693518160738533,704503733608571,714055190881194,722263583559227,729208095262596,734958115677491,
  739574858239992,743112638576254,745619896332679,747140020023458,747712018591402,747371072143587,
  746148986267154,744074568461483,741173940881454,737470800325739,732986633915608,727740896977119,
  721751158107309,715033215159438,707601184837081,699467567674016,690643289339661,681137718396888,
  670958659800000,660112322500314,648603258460154,636434269080082,623606273407857,610118130366007,
  595966404385600,581145059939748,565645065039289,549453876028603,532554764812793,514925933045650,
  496539332652509,477359072986760,457339232509134,436420790009557,414527214592863,391557940338936,
  367378364849366,341803845184139,314572674442722,285297195435425,253366858977748,217729474381884,
  176289239819611,123528990146909]
private def wc_rkmTrajPack_m4_r64_s4_v0 : List ℕ := [2000021042999057,2000082319123524,
  2000215626507672,2000418125194969,2000620957146279,2000716548556796,2000649814803522,
  2000490630914896,2000385370469723,2000403166366026,2000426805289966,1999692215054864,
  1999719161332659,2001162239315143,2003469521560286,2005132788073465,2000824671077984,
  2025777257303181,2080253097690052,2165825844831598,2269663862609850,2366836444239969,
  2430383526876311,2443394728763843,2405828716565140,2332643760374570,2245550641923701,
  2163890854975970,2099177899214502,2054512112716879,2027239708496751,2012377547076798,
  2005111785707486,2001916401474675,2000650890468877,2000199702040276,2000055130315625,
  2000013621376680,2000002990692496,2000000577854009,1999999903075385,1999999986167956,
  2000000001626415,2000000000148558,2000000000009125]
private def wc_rkmTrajPack_m4_r64_s4_v1_p0 : List ℕ := [1998105820834113,1999499778903712,
  2001354842349750,2000824984546026,1998999182042689,1998953155402067,2000645845241881,
  2001177701350624,1999716399350121,1998766526266407,1999902594697260,2001211512863974,
  2000517131853387,1998930775469084,1999025790578145,2000720659886120,2001391726973707,
  1999923615980520,1998433663350374,1999162118877884,2001203633308129,2001743346586428,
  1999918441023661,1997983112063621,1998408333248477,2000847267825945,2002632049004291,
  2001825590820059,1999162477392132,1997172257756915,1997951626393249,2001568011313312,
  2005635176063149,2006176535643719,2000439284934442,1990914713569853,1986427588866745,
  1995985648489041,2017868806295949,2034677057259468,2023712612229962,1978385316582665,
  1922585653733239,1901969670446684,1954851326866665,2083966536717572,2250906119717997,
  2397072759492077,2475210493568410,2470325015757667,2399752050376634,2297546836118419,
  2196112914791699,2115184562267158,2060481887049902,2028418127648695,2011935151444122,
  2004466606970690,2001481542099210,2000431960854447,2000109338876839,2000023573853613,
  2000004196403736,2000000581999668]
private def wc_rkmTrajPack_m4_r64_s4_v1_p1 : List ℕ := [2000000054500311]
private def wc_rkmTrajPack_m4_r64_s4_v1 : List ℕ := pCat wc_rkmTrajPack_m4_r64_s4_v1_p0
  wc_rkmTrajPack_m4_r64_s4_v1_p1
private abbrev dP_0 : Prop := atF [ bNLE (bEvalLo12W 64 128 60 [1,1,1,1,2,2,2,2]
  [11324158,40253566,42858045,2673923,8497583,6746878,6024646,2918214] [6,21,22,2,7,6,5,3]
  rkmMasksPack_m64_r60 [none, none, some (22, 61, wc_rkmTrajPack_m64_r60_s2_hb,
  wc_rkmTrajPack_m64_r60_s2_v0, wc_rkmTrajPack_m64_r60_s2_v1)]) rkmRowPack_m64_r60] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bNLE (bEvalLo12W 2 4096 128 [4,8,16,32,64,112,112,112]
  [17533351,13714491,16350142,17402815,20310427,11098690,10942379,3188915] [3,4,9,17,34,27,27,8]
  rkmMasks_m2_r128 [none, none, none, none, some (34, 129, wc_rkmTraj_m2_r128_s4_hb,
  wc_rkmTraj_m2_r128_s4_v0, wc_rkmTraj_m2_r128_s4_v2), some (27, 129, wc_rkmTraj_m2_r128_s5_hb,
  wc_rkmTraj_m2_r128_s5_v0, wc_rkmTraj_m2_r128_s5_v2), some (27, 129, wc_rkmTraj_m2_r128_s6_hb,
  wc_rkmTraj_m2_r128_s6_v0, wc_rkmTraj_m2_r128_s6_v2)]) rkmRow_m2_r128, bNLE (bEvalLo12W 32 256 19
  [1,1] [157647716,11463454] [25,3] rkmMasks_m32_r19 []) rkmRow_m32_r19] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bNLE (bEvalLo12W 64 128 64 [1,1,2,2,2,2,2,2]
  [24274507,36701935,16855741,16698049,3276394,3011253,607844,2198013] [14,20,15,15,3,3,1,2]
  rkmMasksPack_m64_r64 [none, some (20, 65, wc_rkmTrajPack_m64_r64_s1_hb,
  wc_rkmTrajPack_m64_r64_s1_v0, wc_rkmTrajPack_m64_r64_s1_v1), some (15, 65,
  wc_rkmTrajPack_m64_r64_s2_hb, wc_rkmTrajPack_m64_r64_s2_v0, wc_rkmTrajPack_m64_r64_s2_v1)])
  rkmRowPack_m64_r64, bNLE (bEvalLo12W 8 1024 34 [1,2,3,6] [46555112,34618791,36007254,27573105]
  [5,6,7,9] rkmMasks_m8_r34 []) rkmRow_m8_r34] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bNLE (bEvalLo12W 4 2048 64 [1,2,5,11,23,29,29,29]
  [22041141,18960720,24428663,25495969,28673447,14313989,12967080,4352280] [2,2,6,11,20,12,11,4]
  rkmMasksPack_m4_r64 [none, none, none, none, some (20, 65, wc_rkmTrajPack_m4_r64_s4_hb,
  wc_rkmTrajPack_m4_r64_s4_v0, wc_rkmTrajPack_m4_r64_s4_v1)]) rkmRowPack_m4_r64, bNLE (bEvalLo12W
  32 256 21 [1,1,1,1] [95329042,39274943,29080766,12435339] [15,7,6,3] rkmMasks_m32_r21 [])
  rkmRow_m32_r21] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bNLE (bEvalLo12W 2 4096 52 [2,4,8,16,32,48,48,48]
  [23357832,19345049,22820310,27599922,23303197,30386055,3698277,5656857] [2,2,4,8,11,19,3,4]
  rkmMasksPack_m2_r52 []) rkmRowPack_m2_r52, bNLE (bEvalLo12W 16 512 21 [1,2,2,2]
  [88745581,80824007,25406054,9728542] [8,12,4,2] rkmMasksPack_m16_r21 []) rkmRowPack_m16_r21,
  bNLE (bEvalLo12W 512 16 12 [1,1,1] [392924,33610389,161997] [2,15,2] rkmMasks_m512_r12 [])
  rkmRow_m512_r12] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bSlideChk 17 129 wc_rkmTraj_m2_r128_s4_hb
  wc_rkmTraj_m2_r128_s4_v0 wc_rkmTraj_m2_r128_s4_v1, bNLE (bEvalLo12W 32 256 25 [1,1,1,1,1,1,1,1]
  [96013897,12716744,11215637,16144095,16460912,13013005,16071561,11950541] [16,3,2,3,3,3,3,2]
  rkmMasksPack_m32_r25 []) rkmRowPack_m32_r25] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bSlideChk 17 129 wc_rkmTraj_m2_r128_s4_hb
  wc_rkmTraj_m2_r128_s4_v1 wc_rkmTraj_m2_r128_s4_v2, bNLE (bEvalLo12W 16 512 27 [1,3,3,3]
  [76168539,79811202,11367851,4262961] [9,19,4,2] rkmMasks_m16_r27 []) rkmRow_m16_r27] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bNLE (bEvalLo12W 128 64 64 [1,1,1,1,1,1,1,1]
  [25504551,25377663,25377663,1683970,1913602,881112,881112,352663] [24,24,24,2,2,1,1,1]
  rkmMasks_m128_r64 [some (24, 65, wc_rkmTraj_m128_r64_s0_hb, wc_rkmTraj_m128_r64_s0_v0,
  wc_rkmTraj_m128_r64_s0_v1), some (24, 65, wc_rkmTraj_m128_r64_s1_hb, wc_rkmTraj_m128_r64_s0_v1,
  wc_rkmTraj_m128_r64_s1_v1)]) rkmRow_m128_r64, bNLE (bEvalLo12W 2 4096 36 [2,4,8,16,27,27,27]
  [29635099,25016280,30147855,31541681,51638305,7003802,4160924] [2,2,4,7,16,3,2]
  rkmMasksPack_m2_r36 []) rkmRowPack_m2_r36] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := atF [ bNLE (bEvalLo12W 128 64 40 [1,1,1,1]
  [68962886,4667052,1589136,424452] [44,3,1,1] rkmMasks_m128_r40 []) rkmRow_m128_r40, bNLE
  (bEvalLo12W 4 2048 40 [1,2,4,8,15,15,15]
  [28718410,25952925,33278700,29571886,38226346,2030652,547059] [2,2,5,7,15,1,1] rkmMasks_m4_r40
  []) rkmRow_m4_r40] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := atF [ bSlideChk 18 105 wc_rkmTrajPack_m8_r104_s5_hb
  wc_rkmTrajPack_m8_r104_s5_v0 wc_rkmTrajPack_m8_r104_s5_v1, bNLE (bEvalLo12W 1024 8 30 [1]
  [24513437] [39] rkmMasks_m1024_r30 []) rkmRow_m1024_r30] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := atF [ bSlideChk 18 105 wc_rkmTrajPack_m8_r104_s5_hb
  wc_rkmTrajPack_m8_r104_s5_v1 wc_rkmTrajPack_m8_r104_s5_v2, bSlideChk 15 65
  wc_rkmTrajPack_m64_r64_s2_hb wc_rkmTrajPack_m64_r64_s2_v0 wc_rkmTrajPack_m64_r64_s2_v1, bNLE
  (bEvalLo12W 64 128 14 [1,1,1] [94908036,4503472,2650129] [15,1,1] rkmMasksPack_m64_r14 [])
  rkmRowPack_m64_r14] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := atF [ bSlideChk 14 129 wc_rkmTraj_m2_r128_s5_hb
  wc_rkmTraj_m2_r128_s5_v0 wc_rkmTraj_m2_r128_s5_v1, bSlideChk 20 65 wc_rkmTrajPack_m64_r64_s1_hb
  wc_rkmTrajPack_m64_r64_s1_v0 wc_rkmTrajPack_m64_r64_s1_v1] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := atF [ bSlideChk 14 129 wc_rkmTraj_m2_r128_s6_hb
  wc_rkmTraj_m2_r128_s6_v0 wc_rkmTraj_m2_r128_s6_v1, bSlideChk 20 65 wc_rkmTrajPack_m4_r64_s4_hb
  wc_rkmTrajPack_m4_r64_s4_v0 wc_rkmTrajPack_m4_r64_s4_v1] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := atF [ bSlideChk 30 57 wc_rkmTraj_m128_r56_s0_hb
  wc_rkmTraj_m128_r64_s0_v0 wc_rkmTraj_m128_r56_s0_v1, bSlideChk 22 61
  wc_rkmTrajPack_m64_r60_s2_hb wc_rkmTrajPack_m64_r60_s2_v0 wc_rkmTrajPack_m64_r60_s2_v1] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := atF [ bNLE (bEvalLo12W 2 4096 44 [2,4,8,16,32,41,41,41]
  [25330757,22153585,26403216,30862265,23430542,25793650,4639741,7151611] [2,2,4,8,10,13,3,4]
  rkmMasksPack_m2_r44 []) rkmRowPack_m2_r44, bNLE (bEvalLo12W 8 1024 36 [1,2,4,8,8,8]
  [36439371,27984012,36785184,58107238,4119620,6857179] [3,4,8,20,2,3] rkmMasksPack_m8_r36 [])
  rkmRowPack_m8_r36] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := atF [ bSlideChk 13 129 wc_rkmTraj_m2_r128_s5_hb
  wc_rkmTraj_m2_r128_s5_v1 wc_rkmTraj_m2_r128_s5_v2, bNLE (bEvalLo12W 16 512 32 [1,2,4,4,4,4,4,4]
  [48992572,49905622,26783825,22471979,6233666,2618138,1244103,468168] [7,11,10,8,3,1,1,1]
  rkmMasks_m16_r32 []) rkmRow_m16_r32, bNLE (bEvalLo12W 256 32 10 [1,1] [47289600,980261] [14,1]
  rkmMasks_m256_r10 []) rkmRow_m256_r10] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := atF [ bSlideChk 13 129 wc_rkmTraj_m2_r128_s6_hb
  wc_rkmTraj_m2_r128_s6_v1 wc_rkmTraj_m2_r128_s6_v2, bNLE (bEvalLo12W 2 4096 32
  [2,4,8,16,30,30,30,30] [36601246,35231968,37276652,43417892,17606817,18146001,6161571,2587859]
  [2,3,5,10,6,6,2,1] rkmMasks_m2_r32 []) rkmRow_m2_r32, bNLE (bEvalLo12W 128 64 56 [1,1,1,1]
  [71265797,5899699,1656506,717299] [59,5,2,1] rkmMasks_m128_r56 [some (59, 57,
  wc_rkmTraj_m128_r56_s0_hb, wc_rkmTraj_m128_r64_s0_v0, wc_rkmTraj_m128_r56_s0_v2)])
  rkmRow_m128_r56] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := atF [ bSlideChk 29 57 wc_rkmTraj_m128_r56_s0_hb
  wc_rkmTraj_m128_r56_s0_v1 wc_rkmTraj_m128_r56_s0_v2, bNLE (bEvalLo12W 64 128 33 [1,1,1]
  [97811461,13184626,5078024] [34,6,3] rkmMasks_m64_r33 []) rkmRow_m64_r33] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := atF [ bSlideChk 15 105 wc_rkmTrajPack_m8_r104_s4_hb
  wc_rkmTrajPack_m8_r104_s4_v0 wc_rkmTrajPack_m8_r104_s5_v0, bNLE (bEvalLo12W 128 64 24 [1,1,1]
  [66753945,3917057,1541165] [27,3,2] rkmMasks_m128_r24 []) rkmRow_m128_r24, bNLE (bEvalLo12W 32
  256 22 [1,1,1,1] [124955781,28711322,15928547,9731795] [19,5,3,2] rkmMasksPack_m32_r22 [])
  rkmRowPack_m32_r22] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := atF [ bNLE (bEvalLo12W 8 1024 104 [1,2,4,8,16,20,20,20]
  [17900607,18810276,19467357,16634230,11099809,23408761,1243517,435150] [3,5,9,13,15,36,2,1]
  rkmMasksPack_m8_r104 [none, none, none, none, some (15, 105, wc_rkmTrajPack_m8_r104_s4_hb,
  wc_rkmTrajPack_m8_r104_s4_v0, wc_rkmTrajPack_m8_r104_s5_v0), some (36, 105,
  wc_rkmTrajPack_m8_r104_s5_hb, wc_rkmTrajPack_m8_r104_s5_v0, wc_rkmTrajPack_m8_r104_s5_v2)])
  rkmRowPack_m8_r104, bNLE (bEvalLo12W 64 128 24 [1,1,1,1,1,1,1,1]
  [21530466,20745706,32900183,8782160,8927328,7062192,5255012,3547696] [6,6,9,3,3,2,2,1]
  rkmMasksPack_m64_r24 []) rkmRowPack_m64_r24, bNLE (bEvalLo12W 16 512 19 [1,2,2,2]
  [86522535,77944849,22921899,9034210] [9,12,4,3] rkmMasks_m16_r19 []) rkmRow_m16_r19, bNLE
  (bEvalLo12W 16 512 26 [1,1] [56240969,27324466] [7,4] rkmMasks_m16_r26 []) rkmRow_m16_r26] =
  true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := atF [ bSlideChk 24 65 wc_rkmTraj_m128_r64_s0_hb
  wc_rkmTraj_m128_r64_s0_v0 wc_rkmTraj_m128_r64_s0_v1, bSlideChk 24 65 wc_rkmTraj_m128_r64_s1_hb
  wc_rkmTraj_m128_r64_s0_v1 wc_rkmTraj_m128_r64_s1_v1] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := atF [ bNLE (bEvalLo12W 64 128 18 [1,1,1,1,1,1,1,1]
  [22926465,23416214,28097805,9119127,6651279,6601669,4778126,3067857] [5,5,6,2,2,2,1,1]
  rkmMasksPack_m64_r18 []) rkmRowPack_m64_r18, bNLE (bEvalLo12W 16 512 17 [1,2,2,2]
  [100864743,64368165,22447058,8742997] [9,9,4,3] rkmMasks_m16_r17 []) rkmRow_m16_r17, bNLE
  (bEvalLo12W 16 512 18 [1,2,2,2] [105157578,63637815,23788642,9133624] [9,8,3,2]
  rkmMasksPack_m16_r18 []) rkmRowPack_m16_r18, bNLE (bEvalLo12W 256 32 17 [1,1] [48134621,1000973]
  [20,2] rkmMasks_m256_r17 []) rkmRow_m256_r17, bNLE (bEvalLo12W 64 128 16 [1,1,1,1,1,1]
  [33242821,58994738,3791766,3769351,1635779,1925225] [6,11,1,1,1,1] rkmMasksPack_m64_r16 [])
  rkmRowPack_m64_r16, bNLE (bEvalLo12W 128 64 15 [1,1,1] [68979756,796691,478399] [18,2,2]
  rkmMasks_m128_r15 []) rkmRow_m128_r15, bNLE (bEvalLo12W 16 512 14 [1,2,2,2]
  [108158836,54736901,19843128,7798218] [9,7,4,2] rkmMasks_m16_r14 []) rkmRow_m16_r14, bNLE
  (bEvalLo12W 16 512 13 [1,1,1,1,2,2,2,2]
  [12364206,52074433,33977545,66819726,15836784,11934902,13268587,8329385] [1,4,3,5,2,2,2,1]
  rkmMasksPack_m16_r13 []) rkmRowPack_m16_r13] = true
private theorem bk_21 : dP_21 := by decide +kernel
private abbrev dP_22 : Prop := atF [ bNLE (bEvalLo12W 16 512 12 [1,1,1,1]
  [187270860,22572186,27249562,19759673] [12,3,3,3] rkmMasks_m16_r12 []) rkmRow_m16_r12, bNLE
  (bEvalLo12W 64 128 13 [1,1,1] [94476634,4406045,2524638] [14,1,1] rkmMasksPack_m64_r13 [])
  rkmRowPack_m64_r13, bNLE (bEvalLo12W 256 32 12 [1,1] [47590535,986992] [15,2] rkmMasks_m256_r12
  []) rkmRow_m256_r12, bNLE (bEvalLo12W 16 512 10 [1,1,1,1,1,1,1,1]
  [59153312,27353731,30449350,30359989,30600861,18754733,22985899,15871384] [4,2,2,2,2,1,2,1]
  rkmMasksPack_m16_r10 []) rkmRowPack_m16_r10, bNLE (bEvalLo12W 2 4096 11 [1,2,4,8,9,9,9,9]
  [57117679,47818482,64098561,26479493,20599418,59188792,12708696,4560714] [1,1,3,2,2,4,1,1]
  rkmMasksPack_m2_r11 []) rkmRowPack_m2_r11, bNLE (bEvalLo12W 32 256 4 [1,1,1,1,1]
  [125158640,6137295,610204,606544,353886] [5,1,1,1,1] rkmMasks_m32_r4 []) rkmRow_m32_r4, bNLE
  (bEvalLo12W 8 1024 4 [1,1,1,1,1,1,1,1]
  [75129092,76367293,31900996,32046470,20829972,29361204,12655589,11901950] [2,2,1,1,1,1,1,1]
  rkmMasks_m8_r4 []) rkmRow_m8_r4, bNLE (bEvalLo12W 512 16 7 [1] [33552601] [10] rkmMasks_m512_r7
  []) rkmRow_m512_r7, bNLE (bEvalLo12W 128 64 7 [1,1,1] [65979409,1589207,113664] [9,2,2]
  rkmMasks_m128_r7 []) rkmRow_m128_r7, bNLE (bEvalLo12W 16 512 3 [1,1,1,1]
  [168739447,12356396,2180926,1334011] [25,2,1,1] rkmMasks_m16_r3 []) rkmRow_m16_r3, bNLE
  (bEvalLo12W 4 2048 8 [1,2,3,3,3] [105353409,73173805,98739360,40153405,10635594] [3,4,5,3,2]
  rkmMasks_m4_r8 []) rkmRow_m4_r8, bNLE (bEvalLo12W 64 128 4 [1,1,1,1,1,1,1,1]
  [17213855,32874057,12898944,9655011,8679927,6325533,3090502,2146720] [1,2,1,1,1,1,1,1]
  rkmMasksPack_m64_r4 []) rkmRowPack_m64_r4, bNLE (bEvalLo12W 4 2048 56 [1,1,1,1,1,1,1,1]
  [15063345,31837721,15942575,16543364,19185,3941338,6352069,2982257] [1,2,1,1,1,1,1,1]
  rkmMasksPack_m4_r56 []) rkmRowPack_m4_r56, bNLE (bEvalLo12W 4 2048 5 [1,2,2,2]
  [172964209,118133911,49349757,20600281] [3,3,1,1] rkmMasksPack_m4_r5 []) rkmRowPack_m4_r5, bNLE
  (bEvalLo12W 8 1024 19 [1,1] [86581911,34958815] [5,2] rkmMasksPack_m8_r19 []) rkmRowPack_m8_r19,
  bNLE (bEvalLo12W 2 4096 7 [1,2,4,6,6,6,6,6]
  [84335979,74341023,80185312,42962523,33060481,17224340,3565130,1124849] [1,2,3,2,2,1,1,1]
  rkmMasksPack_m2_r7 []) rkmRowPack_m2_r7, bNLE (bEvalLo12W 8 1024 56 [1,1,1,1,1,1,1,1]
  [20420962,29944138,19909782,9733573,3048683,1542871,286212,13631944] [2,3,2,1,1,1,1,2]
  rkmMasksPack_m8_r56 []) rkmRowPack_m8_r56] = true
private theorem bk_22 : dP_22 := by decide +kernel
private theorem ws_rkmTraj_m2_r128_s4 : WalkOk (some (34, 129, wc_rkmTraj_m2_r128_s4_hb,
    wc_rkmTraj_m2_r128_s4_v0, wc_rkmTraj_m2_r128_s4_v2)) := mIter_split rfl (bSlideChk_sound bk_5)
    (bSlideChk_sound bk_6)
private theorem ws_rkmTraj_m2_r128_s5 : WalkOk (some (27, 129, wc_rkmTraj_m2_r128_s5_hb,
    wc_rkmTraj_m2_r128_s5_v0, wc_rkmTraj_m2_r128_s5_v2)) := mIter_split rfl
    (bSlideChk_sound bk_11) (bSlideChk_sound bk_15)
private theorem ws_rkmTraj_m2_r128_s6 : WalkOk (some (27, 129, wc_rkmTraj_m2_r128_s6_hb,
    wc_rkmTraj_m2_r128_s6_v0, wc_rkmTraj_m2_r128_s6_v2)) := mIter_split rfl
    (bSlideChk_sound bk_12) (bSlideChk_sound bk_16)
private theorem ws_rkmTraj_m128_r56_s0 : WalkOk (some (59, 57, wc_rkmTraj_m128_r56_s0_hb,
    wc_rkmTraj_m128_r64_s0_v0, wc_rkmTraj_m128_r56_s0_v2)) := mIter_split rfl
    (bSlideChk_sound bk_13) (bSlideChk_sound bk_17)
private theorem ws_rkmTrajPack_m8_r104_s5 : WalkOk (some (36, 105, wc_rkmTrajPack_m8_r104_s5_hb,
    wc_rkmTrajPack_m8_r104_s5_v0, wc_rkmTrajPack_m8_r104_s5_v2)) := mIter_split rfl
    (bSlideChk_sound bk_9) (bSlideChk_sound bk_10)
/-- Kernel trajectory certificate `(m = 32, r = 4)`. -/
theorem rkmTraj_m32_r4 : rkmEvalT16Lo12 32 256 4 [1, 1, 1, 1, 1] [125158640, 6137295, 610204,
  606544, 353886] [5, 1, 1, 1, 1] rkmMasks_m32_r4 = rkmRow_m32_r4 :=
    bh0_eq (tl1 (tl2 (tl2 bk_22)))
/-- Kernel trajectory certificate `(m = 2, r = 128)`. -/
theorem rkmTraj_m2_r128 : rkmEvalT16Lo12 2 4096 128 [4, 8, 16, 32, 64, 112, 112, 112] [17533351,
  13714491, 16350142, 17402815, 20310427, 11098690, 10942379, 3188915] [3, 4, 9, 17, 34, 27, 27, 8]
  rkmMasks_m2_r128 = rkmRow_m2_r128 :=
    bhW_eq bk_1 (wSkip (wSkip (wSkip (wSkip (wCons ws_rkmTraj_m2_r128_s4 (wCons
      ws_rkmTraj_m2_r128_s5 (wCons ws_rkmTraj_m2_r128_s6 wNil)))))))
/-- Kernel trajectory certificate `(m = 8, r = 4)`. -/
theorem rkmTraj_m8_r4 : rkmEvalT16Lo12 8 1024 4 [1, 1, 1, 1, 1, 1, 1, 1] [75129092, 76367293,
  31900996, 32046470, 20829972, 29361204, 12655589, 11901950] [2, 2, 1, 1, 1, 1, 1, 1]
  rkmMasks_m8_r4 = rkmRow_m8_r4 := bh0_eq (tl2 (tl2 (tl2 bk_22)))
/-- Kernel trajectory certificate `(m = 128, r = 64)`. -/
theorem rkmTraj_m128_r64 : rkmEvalT16Lo12 128 64 64 [1, 1, 1, 1, 1, 1, 1, 1] [25504551, 25377663,
  25377663, 1683970, 1913602, 881112, 881112, 352663] [24, 24, 24, 2, 2, 1, 1, 1] rkmMasks_m128_r64
  = rkmRow_m128_r64 :=
    bhW_eq bk_7 (wCons (bSlideChk_sound bk_20) (wCons (bSlideChk_sound (tl1 bk_20)) wNil))
/-- Kernel trajectory certificate `(m = 512, r = 7)`. -/
theorem rkmTraj_m512_r7 : rkmEvalT16Lo12 512 16 7 [1] [33552601] [10] rkmMasks_m512_r7 =
  rkmRow_m512_r7 := bh0_eq (tl1 (tl2 (tl2 (tl2 bk_22))))
/-- Kernel trajectory certificate `(m = 128, r = 56)`. -/
theorem rkmTraj_m128_r56 : rkmEvalT16Lo12 128 64 56 [1, 1, 1, 1] [71265797, 5899699, 1656506,
  717299] [59, 5, 2, 1] rkmMasks_m128_r56 = rkmRow_m128_r56 :=
    bhW_eq (tl2 bk_16) (wCons ws_rkmTraj_m128_r56_s0 wNil)
/-- Kernel trajectory certificate `(m = 128, r = 7)`. -/
theorem rkmTraj_m128_r7 : rkmEvalT16Lo12 128 64 7 [1, 1, 1] [65979409, 1589207, 113664] [9, 2, 2]
  rkmMasks_m128_r7 = rkmRow_m128_r7 := bh0_eq (tl2 (tl2 (tl2 (tl2 bk_22))))
/-- Kernel trajectory certificate `(m = 128, r = 40)`. -/
theorem rkmTraj_m128_r40 : rkmEvalT16Lo12 128 64 40 [1, 1, 1, 1] [68962886, 4667052, 1589136,
  424452] [44, 3, 1, 1] rkmMasks_m128_r40 = rkmRow_m128_r40 := bh0_eq bk_8
/-- Kernel trajectory certificate `(m = 16, r = 3)`. -/
theorem rkmTraj_m16_r3 : rkmEvalT16Lo12 16 512 3 [1, 1, 1, 1] [168739447, 12356396, 2180926,
  1334011] [25, 2, 1, 1] rkmMasks_m16_r3 = rkmRow_m16_r3 :=
    bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 bk_22)))))
/-- Kernel trajectory certificate `(m = 64, r = 33)`. -/
theorem rkmTraj_m64_r33 : rkmEvalT16Lo12 64 128 33 [1, 1, 1] [97811461, 13184626, 5078024] [34, 6,
  3] rkmMasks_m64_r33 = rkmRow_m64_r33 := bh0_eq (tl1 bk_17)
/-- Kernel trajectory certificate `(m = 4, r = 8)`. -/
theorem rkmTraj_m4_r8 : rkmEvalT16Lo12 4 2048 8 [1, 2, 3, 3, 3] [105353409, 73173805, 98739360,
  40153405, 10635594] [3, 4, 5, 3, 2] rkmMasks_m4_r8 = rkmRow_m4_r8 :=
    bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 bk_22)))))
/-- Kernel trajectory certificate `(m = 16, r = 32)`. -/
theorem rkmTraj_m16_r32 : rkmEvalT16Lo12 16 512 32 [1, 2, 4, 4, 4, 4, 4, 4] [48992572, 49905622,
  26783825, 22471979, 6233666, 2618138, 1244103, 468168] [7, 11, 10, 8, 3, 1, 1, 1] rkmMasks_m16_r32
  = rkmRow_m16_r32 := bh0_eq (tl1 bk_15)
/-- Kernel trajectory certificate `(m = 256, r = 10)`. -/
theorem rkmTraj_m256_r10 : rkmEvalT16Lo12 256 32 10 [1, 1] [47289600, 980261] [14, 1]
  rkmMasks_m256_r10 = rkmRow_m256_r10 := bh0_eq (tl2 bk_15)
/-- Kernel trajectory certificate `(m = 1024, r = 30)`. -/
theorem rkmTraj_m1024_r30 : rkmEvalT16Lo12 1024 8 30 [1] [24513437] [39] rkmMasks_m1024_r30 =
  rkmRow_m1024_r30 := bh0_eq (tl1 bk_9)
/-- Kernel trajectory certificate `(m = 16, r = 26)`. -/
theorem rkmTraj_m16_r26 : rkmEvalT16Lo12 16 512 26 [1, 1] [56240969, 27324466] [7, 4]
  rkmMasks_m16_r26 = rkmRow_m16_r26 := bh0_eq (tl1 (tl2 bk_19))
/-- Kernel trajectory certificate `(m = 4, r = 40)`. -/
theorem rkmTraj_m4_r40 : rkmEvalT16Lo12 4 2048 40 [1, 2, 4, 8, 15, 15, 15] [28718410, 25952925,
  33278700, 29571886, 38226346, 2030652, 547059] [2, 2, 5, 7, 15, 1, 1] rkmMasks_m4_r40 =
  rkmRow_m4_r40 := bh0_eq (tl1 bk_8)
/-- Kernel trajectory certificate `(m = 256, r = 12)`. -/
theorem rkmTraj_m256_r12 : rkmEvalT16Lo12 256 32 12 [1, 1] [47590535, 986992] [15, 2]
  rkmMasks_m256_r12 = rkmRow_m256_r12 := bh0_eq (tl2 bk_22)
/-- Kernel trajectory certificate `(m = 2, r = 32)`. -/
theorem rkmTraj_m2_r32 : rkmEvalT16Lo12 2 4096 32 [2, 4, 8, 16, 30, 30, 30, 30] [36601246, 35231968,
  37276652, 43417892, 17606817, 18146001, 6161571, 2587859] [2, 3, 5, 10, 6, 6, 2, 1]
  rkmMasks_m2_r32 = rkmRow_m2_r32 := bh0_eq (tl1 bk_16)
/-- Kernel trajectory certificate `(m = 512, r = 12)`. -/
theorem rkmTraj_m512_r12 : rkmEvalT16Lo12 512 16 12 [1, 1, 1] [392924, 33610389, 161997] [2, 15, 2]
  rkmMasks_m512_r12 = rkmRow_m512_r12 := bh0_eq (tl2 bk_4)
/-- Kernel trajectory certificate `(m = 16, r = 27)`. -/
theorem rkmTraj_m16_r27 : rkmEvalT16Lo12 16 512 27 [1, 3, 3, 3] [76168539, 79811202, 11367851,
  4262961] [9, 19, 4, 2] rkmMasks_m16_r27 = rkmRow_m16_r27 := bh0_eq (tl1 bk_6)
/-- Kernel trajectory certificate `(m = 16, r = 12)`. -/
theorem rkmTraj_m16_r12 : rkmEvalT16Lo12 16 512 12 [1, 1, 1, 1] [187270860, 22572186, 27249562,
  19759673] [12, 3, 3, 3] rkmMasks_m16_r12 = rkmRow_m16_r12 := bh0_eq bk_22
/-- Kernel trajectory certificate `(m = 128, r = 24)`. -/
theorem rkmTraj_m128_r24 : rkmEvalT16Lo12 128 64 24 [1, 1, 1] [66753945, 3917057, 1541165] [27, 3,
  2] rkmMasks_m128_r24 = rkmRow_m128_r24 := bh0_eq (tl1 bk_18)
/-- Kernel trajectory certificate `(m = 16, r = 14)`. -/
theorem rkmTraj_m16_r14 : rkmEvalT16Lo12 16 512 14 [1, 2, 2, 2] [108158836, 54736901, 19843128,
  7798218] [9, 7, 4, 2] rkmMasks_m16_r14 = rkmRow_m16_r14 := bh0_eq (tl2 (tl2 (tl2 bk_21)))
/-- Kernel trajectory certificate `(m = 32, r = 21)`. -/
theorem rkmTraj_m32_r21 : rkmEvalT16Lo12 32 256 21 [1, 1, 1, 1] [95329042, 39274943, 29080766,
  12435339] [15, 7, 6, 3] rkmMasks_m32_r21 = rkmRow_m32_r21 := bh0_eq (tl1 bk_3)
/-- Kernel trajectory certificate `(m = 128, r = 15)`. -/
theorem rkmTraj_m128_r15 : rkmEvalT16Lo12 128 64 15 [1, 1, 1] [68979756, 796691, 478399] [18, 2, 2]
  rkmMasks_m128_r15 = rkmRow_m128_r15 := bh0_eq (tl1 (tl2 (tl2 bk_21)))
/-- Kernel trajectory certificate `(m = 8, r = 34)`. -/
theorem rkmTraj_m8_r34 : rkmEvalT16Lo12 8 1024 34 [1, 2, 3, 6] [46555112, 34618791, 36007254,
  27573105] [5, 6, 7, 9] rkmMasks_m8_r34 = rkmRow_m8_r34 := bh0_eq (tl1 bk_2)
/-- Kernel trajectory certificate `(m = 256, r = 17)`. -/
theorem rkmTraj_m256_r17 : rkmEvalT16Lo12 256 32 17 [1, 1] [48134621, 1000973] [20, 2]
  rkmMasks_m256_r17 = rkmRow_m256_r17 := bh0_eq (tl1 (tl2 bk_21))
/-- Kernel trajectory certificate `(m = 32, r = 19)`. -/
theorem rkmTraj_m32_r19 : rkmEvalT16Lo12 32 256 19 [1, 1] [157647716, 11463454] [25, 3]
  rkmMasks_m32_r19 = rkmRow_m32_r19 := bh0_eq (tl1 bk_1)
/-- Kernel trajectory certificate `(m = 16, r = 17)`. -/
theorem rkmTraj_m16_r17 : rkmEvalT16Lo12 16 512 17 [1, 2, 2, 2] [100864743, 64368165, 22447058,
  8742997] [9, 9, 4, 3] rkmMasks_m16_r17 = rkmRow_m16_r17 := bh0_eq (tl1 bk_21)
/-- Kernel trajectory certificate `(m = 16, r = 19)`. -/
theorem rkmTraj_m16_r19 : rkmEvalT16Lo12 16 512 19 [1, 2, 2, 2] [86522535, 77944849, 22921899,
  9034210] [9, 12, 4, 3] rkmMasks_m16_r19 = rkmRow_m16_r19 := bh0_eq (tl2 bk_19)
/-- Krotov trajectory `(m = 8, r = 104)`. -/
theorem rkmTrajPack_m8_r104 : rkmEvalT16Lo12 8 1024 104 [1,2,4,8,16,20,20,20]
  [17900607,18810276,19467357,16634230,11099809,23408761,1243517,435150] [3,5,9,13,15,36,2,1]
  rkmMasksPack_m8_r104 = rkmRowPack_m8_r104 :=
    bhW_eq bk_19 (wSkip (wSkip (wSkip (wSkip (wCons (bSlideChk_sound bk_18) (wCons
      ws_rkmTrajPack_m8_r104_s5 wNil))))))
/-- Krotov trajectory `(m = 64, r = 4)`. -/
theorem rkmTrajPack_m64_r4 : rkmEvalT16Lo12 64 128 4 [1,1,1,1,1,1,1,1]
  [17213855,32874057,12898944,9655011,8679927,6325533,3090502,2146720] [1,2,1,1,1,1,1,1]
  rkmMasksPack_m64_r4 = rkmRowPack_m64_r4 := bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 bk_22))))))
/-- Krotov trajectory `(m = 64, r = 64)`. -/
theorem rkmTrajPack_m64_r64 : rkmEvalT16Lo12 64 128 64 [1,1,2,2,2,2,2,2]
  [24274507,36701935,16855741,16698049,3276394,3011253,607844,2198013] [14,20,15,15,3,3,1,2]
  rkmMasksPack_m64_r64 = rkmRowPack_m64_r64 :=
    bhW_eq bk_2 (wSkip (wCons (bSlideChk_sound (tl1 bk_11)) (wCons (bSlideChk_sound (tl1 bk_10))
      wNil)))
/-- Krotov trajectory `(m = 4, r = 56)`. -/
theorem rkmTrajPack_m4_r56 : rkmEvalT16Lo12 4 2048 56 [1,1,1,1,1,1,1,1]
  [15063345,31837721,15942575,16543364,19185,3941338,6352069,2982257] [1,2,1,1,1,1,1,1]
  rkmMasksPack_m4_r56 = rkmRowPack_m4_r56 := bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_22))))))
/-- Krotov trajectory `(m = 64, r = 60)`. -/
theorem rkmTrajPack_m64_r60 : rkmEvalT16Lo12 64 128 60 [1,1,1,1,2,2,2,2]
  [11324158,40253566,42858045,2673923,8497583,6746878,6024646,2918214] [6,21,22,2,7,6,5,3]
  rkmMasksPack_m64_r60 = rkmRowPack_m64_r60 :=
    bhW_eq bk_0 (wSkip (wSkip (wCons (bSlideChk_sound (tl1 bk_13)) wNil)))
/-- Krotov trajectory `(m = 4, r = 5)`. -/
theorem rkmTrajPack_m4_r5 : rkmEvalT16Lo12 4 2048 5 [1,2,2,2]
  [172964209,118133911,49349757,20600281] [3,3,1,1] rkmMasksPack_m4_r5 = rkmRowPack_m4_r5 :=
    bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_22)))))))
/-- Krotov trajectory `(m = 4, r = 64)`. -/
theorem rkmTrajPack_m4_r64 : rkmEvalT16Lo12 4 2048 64 [1,2,5,11,23,29,29,29]
  [22041141,18960720,24428663,25495969,28673447,14313989,12967080,4352280] [2,2,6,11,20,12,11,4]
  rkmMasksPack_m4_r64 = rkmRowPack_m4_r64 :=
    bhW_eq bk_3 (wSkip (wSkip (wSkip (wSkip (wCons (bSlideChk_sound (tl1 bk_12)) wNil)))))
/-- Krotov trajectory `(m = 8, r = 19)`. -/
theorem rkmTrajPack_m8_r19 : rkmEvalT16Lo12 8 1024 19 [1,1] [86581911,34958815] [5,2]
  rkmMasksPack_m8_r19 = rkmRowPack_m8_r19 :=
    bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_22)))))))
/-- Krotov trajectory `(m = 2, r = 52)`. -/
theorem rkmTrajPack_m2_r52 : rkmEvalT16Lo12 2 4096 52 [2,4,8,16,32,48,48,48]
  [23357832,19345049,22820310,27599922,23303197,30386055,3698277,5656857] [2,2,4,8,11,19,3,4]
  rkmMasksPack_m2_r52 = rkmRowPack_m2_r52 := bh0_eq bk_4
/-- Krotov trajectory `(m = 2, r = 7)`. -/
theorem rkmTrajPack_m2_r7 : rkmEvalT16Lo12 2 4096 7 [1,2,4,6,6,6,6,6]
  [84335979,74341023,80185312,42962523,33060481,17224340,3565130,1124849] [1,2,3,2,2,1,1,1]
  rkmMasksPack_m2_r7 = rkmRowPack_m2_r7 :=
    bh0_eq (tl1 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_22))))))))
/-- Krotov trajectory `(m = 2, r = 44)`. -/
theorem rkmTrajPack_m2_r44 : rkmEvalT16Lo12 2 4096 44 [2,4,8,16,32,41,41,41]
  [25330757,22153585,26403216,30862265,23430542,25793650,4639741,7151611] [2,2,4,8,10,13,3,4]
  rkmMasksPack_m2_r44 = rkmRowPack_m2_r44 := bh0_eq bk_14
/-- Krotov trajectory `(m = 8, r = 56)`. -/
theorem rkmTrajPack_m8_r56 : rkmEvalT16Lo12 8 1024 56 [1,1,1,1,1,1,1,1]
  [20420962,29944138,19909782,9733573,3048683,1542871,286212,13631944] [2,3,2,1,1,1,1,2]
  rkmMasksPack_m8_r56 = rkmRowPack_m8_r56 :=
    bh0_eq (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 (tl2 bk_22))))))))
/-- Krotov trajectory `(m = 8, r = 36)`. -/
theorem rkmTrajPack_m8_r36 : rkmEvalT16Lo12 8 1024 36 [1,2,4,8,8,8]
  [36439371,27984012,36785184,58107238,4119620,6857179] [3,4,8,20,2,3] rkmMasksPack_m8_r36 =
  rkmRowPack_m8_r36 := bh0_eq (tl1 bk_14)
/-- Krotov trajectory `(m = 2, r = 11)`. -/
theorem rkmTrajPack_m2_r11 : rkmEvalT16Lo12 2 4096 11 [1,2,4,8,9,9,9,9]
  [57117679,47818482,64098561,26479493,20599418,59188792,12708696,4560714] [1,1,3,2,2,4,1,1]
  rkmMasksPack_m2_r11 = rkmRowPack_m2_r11 := bh0_eq (tl2 (tl2 bk_22))
/-- Krotov trajectory `(m = 2, r = 36)`. -/
theorem rkmTrajPack_m2_r36 : rkmEvalT16Lo12 2 4096 36 [2,4,8,16,27,27,27]
  [29635099,25016280,30147855,31541681,51638305,7003802,4160924] [2,2,4,7,16,3,2]
  rkmMasksPack_m2_r36 = rkmRowPack_m2_r36 := bh0_eq (tl1 bk_7)
/-- Krotov trajectory `(m = 16, r = 10)`. -/
theorem rkmTrajPack_m16_r10 : rkmEvalT16Lo12 16 512 10 [1,1,1,1,1,1,1,1]
  [59153312,27353731,30449350,30359989,30600861,18754733,22985899,15871384] [4,2,2,2,2,1,2,1]
  rkmMasksPack_m16_r10 = rkmRowPack_m16_r10 := bh0_eq (tl1 (tl2 bk_22))
/-- Krotov trajectory `(m = 32, r = 25)`. -/
theorem rkmTrajPack_m32_r25 : rkmEvalT16Lo12 32 256 25 [1,1,1,1,1,1,1,1]
  [96013897,12716744,11215637,16144095,16460912,13013005,16071561,11950541] [16,3,2,3,3,3,3,2]
  rkmMasksPack_m32_r25 = rkmRowPack_m32_r25 := bh0_eq (tl1 bk_5)
/-- Krotov trajectory `(m = 64, r = 13)`. -/
theorem rkmTrajPack_m64_r13 : rkmEvalT16Lo12 64 128 13 [1,1,1] [94476634,4406045,2524638] [14,1,1]
  rkmMasksPack_m64_r13 = rkmRowPack_m64_r13 := bh0_eq (tl1 bk_22)
/-- Krotov trajectory `(m = 64, r = 24)`. -/
theorem rkmTrajPack_m64_r24 : rkmEvalT16Lo12 64 128 24 [1,1,1,1,1,1,1,1]
  [21530466,20745706,32900183,8782160,8927328,7062192,5255012,3547696] [6,6,9,3,3,2,2,1]
  rkmMasksPack_m64_r24 = rkmRowPack_m64_r24 := bh0_eq (tl1 bk_19)
/-- Krotov trajectory `(m = 64, r = 14)`. -/
theorem rkmTrajPack_m64_r14 : rkmEvalT16Lo12 64 128 14 [1,1,1] [94908036,4503472,2650129] [15,1,1]
  rkmMasksPack_m64_r14 = rkmRowPack_m64_r14 := bh0_eq (tl2 bk_10)
/-- Krotov trajectory `(m = 32, r = 22)`. -/
theorem rkmTrajPack_m32_r22 : rkmEvalT16Lo12 32 256 22 [1,1,1,1]
  [124955781,28711322,15928547,9731795] [19,5,3,2] rkmMasksPack_m32_r22 = rkmRowPack_m32_r22 :=
    bh0_eq (tl2 bk_18)
/-- Krotov trajectory `(m = 16, r = 13)`. -/
theorem rkmTrajPack_m16_r13 : rkmEvalT16Lo12 16 512 13 [1,1,1,1,2,2,2,2]
  [12364206,52074433,33977545,66819726,15836784,11934902,13268587,8329385] [1,4,3,5,2,2,2,1]
  rkmMasksPack_m16_r13 = rkmRowPack_m16_r13 := bh0_eq (tl1 (tl2 (tl2 (tl2 bk_21))))
/-- Krotov trajectory `(m = 16, r = 21)`. -/
theorem rkmTrajPack_m16_r21 : rkmEvalT16Lo12 16 512 21 [1,2,2,2]
  [88745581,80824007,25406054,9728542] [8,12,4,2] rkmMasksPack_m16_r21 = rkmRowPack_m16_r21 :=
    bh0_eq (tl1 bk_4)
/-- Krotov trajectory `(m = 64, r = 16)`. -/
theorem rkmTrajPack_m64_r16 : rkmEvalT16Lo12 64 128 16 [1,1,1,1,1,1]
  [33242821,58994738,3791766,3769351,1635779,1925225] [6,11,1,1,1,1] rkmMasksPack_m64_r16 =
  rkmRowPack_m64_r16 := bh0_eq (tl2 (tl2 bk_21))
/-- Krotov trajectory `(m = 64, r = 18)`. -/
theorem rkmTrajPack_m64_r18 : rkmEvalT16Lo12 64 128 18 [1,1,1,1,1,1,1,1]
  [22926465,23416214,28097805,9119127,6651279,6601669,4778126,3067857] [5,5,6,2,2,2,1,1]
  rkmMasksPack_m64_r18 = rkmRowPack_m64_r18 := bh0_eq bk_21
/-- Krotov trajectory `(m = 16, r = 18)`. -/
theorem rkmTrajPack_m16_r18 : rkmEvalT16Lo12 16 512 18 [1,2,2,2]
  [105157578,63637815,23788642,9133624] [9,8,3,2] rkmMasksPack_m16_r18 = rkmRowPack_m16_r18 :=
    bh0_eq (tl2 bk_21)
end
end QuantumComputation.Specs.DickeSol
