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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiBase
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxLowHiT0

/-
# Low-`m` High-`r` Krotov Trajectory Part `1` (`FindAllJohnsonRampKickMuxLowHiT1`)

Certifies segments `4, 5, 6` and stitches the full `8`-segment `rkmEvalT16Lo12`
trajectory for `(m, r) = (2, 512)`.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Part `0` of `rkmMkPack_m2_r512_s2`. -/
def rkmMkPack_m2_r512_s2_p0 : List Bool := [
  false, true, true, false, true, false, false, false, true, false, true, true, false, false, true,
  false, false, true, false, false, false, false, true, false, false, true, false, true, true,
  true, true, true, true, true, true, true, true, true, true, true, true, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, true, true, true
  ]
/-- Part `1` of `rkmMkPack_m2_r512_s2`. -/
def rkmMkPack_m2_r512_s2_p1 : List Bool := [true, false, false, false, false, false, true]
/-- Sign-kick mask segment `2` for `(m = 2, r = 512)`. -/
def rkmMkPack_m2_r512_s2 : List Bool :=
  rkmMkPack_m2_r512_s2_p0 ++ rkmMkPack_m2_r512_s2_p1
/-- Part `0` of `rkmMkPack_m2_r512_s3`. -/
def rkmMkPack_m2_r512_s3_p0 : List Bool := [
  false, false, false, true, true, true, false, false, false, false, false, false, false, false,
  true, true, true, true, false, false, true, true, true, true, true, true, false, false, false,
  false, true, true, false, true, true, false, true, true, true, true, false, false, false, true,
  false, true, true, false, false, false, true, true, true, false, false, true, true, true, true,
  false, false, false, false, false, true, true, true, true, false, false, false, true, true,
  false, false, false, true, true, false, false, true, true, true, false, false, false, false,
  true, false, false, false, true, false, false, true, false
  ]
/-- Part `1` of `rkmMkPack_m2_r512_s3`. -/
def rkmMkPack_m2_r512_s3_p1 : List Bool := [
  true, false, true, true, true, true, false, true, true, true, false, true, true, true, true,
  true, true, false, false, false, false, true, true, true, true, true, true, true, true, true,
  false, false, false, false, false, false, true, true, true, true, true, true, false, true, true,
  true, true, true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, false, false, false
  ]
/-- Part `2` of `rkmMkPack_m2_r512_s3`. -/
def rkmMkPack_m2_r512_s3_p2 : List Bool := [
  false, false, false, true, true, true, true, false, false, false, false, false, false, true,
  true, false, false, false, true, false, false, true, true, true
  ]
/-- Sign-kick mask segment `3` for `(m = 2, r = 512)`. -/
def rkmMkPack_m2_r512_s3 : List Bool :=
  rkmMkPack_m2_r512_s3_p0 ++ (rkmMkPack_m2_r512_s3_p1 ++ rkmMkPack_m2_r512_s3_p2)
/-- Part `0` of `rkmMkPack_m2_r512_s4`. -/
def rkmMkPack_m2_r512_s4_p0 : List Bool := [
  false, false, true, false, false, false, true, false, false, false, true, false, false, false,
  false, false, true, false, false, false, false, false, false, true, false, true, false, false,
  true, true, false, false, true, true, false, false, false, false, false, true, false, true,
  false, false, false, false, false, false, true, true, true, false, false, false, false, false,
  true, false, false, true, true, false, false, true, true, false, true, false, false, false,
  false, false, true, false, false, true, true, false, false, true, true, false, false, true,
  false, false, true, true, false, false, true, true, false, false, true, false
  ]
/-- Part `1` of `rkmMkPack_m2_r512_s4`. -/
def rkmMkPack_m2_r512_s4_p1 : List Bool := [
  false, true, true, false, false, false, false, true, true, false, true, false, false, true, true,
  false, false, true, true, false, false, false, true, false, true, true, false, false, true,
  false, true, true, false, false, false, false, false, false, true, false, false, false, true,
  false, true, false, true, false, true, false, true, false, false, false, true, false, false,
  true, false, true, false, false, false, false, true, false, true, true, false, false, true, true,
  true, false, false, true, false, false, false, false, false, false, true, true, false, false,
  true, true, true, false, false, false, false, true, true, false
  ]
/-- Part `2` of `rkmMkPack_m2_r512_s4`. -/
def rkmMkPack_m2_r512_s4_p2 : List Bool := [
  false, false, false, false, false, true, true, false, true, false, false, false, false, false,
  true, false, false, true, false, true, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, false, false,
  false, false, false, false, false, true, true, true, true, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, true, true, false, false, false,
  false, false, false, true, true, true, true, true, true, false, false, false, true, true, true,
  true, false, false, false, false, true, true, true, true, true, false
  ]
/-- Part `3` of `rkmMkPack_m2_r512_s4`. -/
def rkmMkPack_m2_r512_s4_p3 : List Bool := [
  false, false, false, false, true, true, true, true, true, true, false, false, false, false,
  false, false, true, true, true, true, true, true, true, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, true, true, true, true, false, false, false, false,
  false, false, false, false, true, true, true, true, false, false, false, true
  ]
/-- Sign-kick mask segment `4` for `(m = 2, r = 512)`. -/
def rkmMkPack_m2_r512_s4 : List Bool :=
  rkmMkPack_m2_r512_s4_p0 ++ (rkmMkPack_m2_r512_s4_p1 ++ (rkmMkPack_m2_r512_s4_p2
    ++ rkmMkPack_m2_r512_s4_p3))
/-- Part `0` of `rkmMkPack_m2_r512_s5`. -/
def rkmMkPack_m2_r512_s5_p0 : List Bool := [
  false, false, true, true, true, true, false, true, true, true, true, true, false, false, true,
  true, false, false, false, false, false, false, true, true, false, true, false, false, false,
  false, false, true, false, false, true, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, true, true, false, false, false, true,
  true, false, false, false, true, false, false, false, true, true, true, true, false, true, true,
  true, false, false, false, false, false, true, false, false, false, true, false, true, true,
  false, false, true, false, true, true, false, true, true, false
  ]
/-- Part `1` of `rkmMkPack_m2_r512_s5`. -/
def rkmMkPack_m2_r512_s5_p1 : List Bool := [
  false, false, false, true, true, false, false, false, true, false, false, true, true, true,
  false, true, false, false, false, true, true, false, true, false, false, true, false, false,
  true, true, false, false, true, false, false, true, false, false, true, false, false, true, true,
  true, false, false, false, false, false, false, false, true, false, false, true, true, false,
  false, false, false, false, false, false, false, true, false, false, false, false, false, false,
  false, false, false, true, false, true, true, false, false, true, false, true, false, true,
  false, false, true, false, false, false, false, true, true, true, false
  ]
/-- Part `2` of `rkmMkPack_m2_r512_s5`. -/
def rkmMkPack_m2_r512_s5_p2 : List Bool := [
  false, false, false, true, false, false, false, false, true, true, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, false, false, false,
  true, false, false, false, false, false, false, true, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, false, false, false, false, false, true, false, true, false, false, false, false, false,
  false, false, false, false, true, true, false, false, false, false, false, false
  ]
/-- Part `3` of `rkmMkPack_m2_r512_s5`. -/
def rkmMkPack_m2_r512_s5_p3 : List Bool := [
  false, false, true, false, false, true, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, false, false, false, false, true, false, false, false, true, true, false, false, false,
  false, false, false, false, false, false, true, false, false, false, false, false, false, false,
  false, false, true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false
  ]
/-- Part `4` of `rkmMkPack_m2_r512_s5`. -/
def rkmMkPack_m2_r512_s5_p4 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, true, false, false, false, true, true, true, true, false, false, false, true,
  true, true, true, false, false, false, false, true, true, true, true, false, false, false, false,
  false, true, true, true, true, true, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true, true, false
  ]
/-- Part `5` of `rkmMkPack_m2_r512_s5`. -/
def rkmMkPack_m2_r512_s5_p5 : List Bool := [
  false, true, true, true, false, false, true, true, true, false, true, true, false, false, true,
  true
  ]
/-- Sign-kick mask segment `5` for `(m = 2, r = 512)`. -/
def rkmMkPack_m2_r512_s5 : List Bool :=
  rkmMkPack_m2_r512_s5_p0 ++ (rkmMkPack_m2_r512_s5_p1 ++ (rkmMkPack_m2_r512_s5_p2
    ++ (rkmMkPack_m2_r512_s5_p3 ++ (rkmMkPack_m2_r512_s5_p4 ++ rkmMkPack_m2_r512_s5_p5))))
/-- Part `0` of `rkmMkPack_m2_r512_s6`. -/
def rkmMkPack_m2_r512_s6_p0 : List Bool := [
  false, true, true, true, true, false, false, false, true, true, true, true, true, true, true,
  true, false, true, false, false, true, true, false, true, true, false, true, true, false, false,
  true, false, false, false, true, false, false, true, false, false, false, false, false, false,
  false, false, false, true, false, false, false, true, false, false, true, true, false, false,
  false, false, true, false, true, false, false, false, false, false, false, false, true, false,
  false, false, false, false, false, false, false, false, true, false, false, false, false, false,
  true, false, false, false, true, false, false, false, false, false
  ]
/-- Part `1` of `rkmMkPack_m2_r512_s6`. -/
def rkmMkPack_m2_r512_s6_p1 : List Bool := [
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, false, false, false, false, false, true, false, true, false,
  false, false, false, false, false, false, true, false, false, false, false, false, false, true,
  false, false, false, true, false, false, false, false, true, false, false, false, true, false,
  false, false, true, false, false, false, false, false, true, false, false, false, false, false,
  true, false, false, false, true, false, false, false, false, false, false, false, false, false,
  true, false, true, false, false, false, false, true, false, false, false, false
  ]
/-- Part `2` of `rkmMkPack_m2_r512_s6`. -/
def rkmMkPack_m2_r512_s6_p2 : List Bool := [
  false, false, false, false, false, false, false, false, true, false, false, false, false, false,
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  true, false, false, false, true, false, false, false, false, false, true, false, false, false,
  false, false, false, false, false, false, true, false, false, true, false, false, false, false,
  false, false, true, false, false, false, false, false, false, false, false, false, false, true,
  false, false, false, false, false, false, false, false, true, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, false
  ]
/-- Part `3` of `rkmMkPack_m2_r512_s6`. -/
def rkmMkPack_m2_r512_s6_p3 : List Bool := [
  false, false, true, false, false, false, false, false, false, false, false, false, true, true,
  false, false, false, false, false, false, false, false, true, false, false, false, false, false,
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, false, false, true, false, false, true, false, false, false,
  false, false, false, false, false, false, true, false, false, false, false, false, false, false,
  false, false, false, true, false, false, false, false, false, false, false, false, true, false,
  false, false, false, false, false, false, false, false, true, false, false, false
  ]
/-- Part `4` of `rkmMkPack_m2_r512_s6`. -/
def rkmMkPack_m2_r512_s6_p4 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, false, false, false, false, false, false, false, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, false, false, false, false, false, true, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, false, false, false
  ]
/-- Part `5` of `rkmMkPack_m2_r512_s6`. -/
def rkmMkPack_m2_r512_s6_p5 : List Bool := [
  false, true, true, false, false, false, false, true, true, true
  ]
/-- Sign-kick mask segment `6` for `(m = 2, r = 512)`. -/
def rkmMkPack_m2_r512_s6 : List Bool :=
  rkmMkPack_m2_r512_s6_p0 ++ (rkmMkPack_m2_r512_s6_p1 ++ (rkmMkPack_m2_r512_s6_p2
    ++ (rkmMkPack_m2_r512_s6_p3 ++ (rkmMkPack_m2_r512_s6_p4 ++ rkmMkPack_m2_r512_s6_p5))))
/-- Multi-segment sign-kick masks for `(m = 2, r = 512)`. -/
def rkmMasksPack_m2_r512 : List (List Bool) := [
  [], [true, true, true, true, true, true], rkmMkPack_m2_r512_s2, rkmMkPack_m2_r512_s3,
  rkmMkPack_m2_r512_s4, rkmMkPack_m2_r512_s5, rkmMkPack_m2_r512_s6, []
  ]
/-- Hit-row chunk `0` for `(m = 2, r = 512)`. -/
def rkmRowPack_m2_r512_p0 : List ℕ := [
  2074, 8350, 1420, 659, 4876, 887, 2010, 93, 16443, 9137, 48013, 10852, 16889, 42474, 99139, 2090,
  6181, 8143, 13979, 559, 8659, 132176, 38475, 8491, 285, 40109, 33429, 8892, 15757, 240, 4784,
  19427, 234, 20627, 146706, 73415, 56, 9174, 5742, 6361, 23170, 131084, 61279, 2087, 111527,
  183747, 262269, 276182, 43698, 79525, 8167, 11181, 13436, 83293, 20378, 32973, 571, 51197, 46771,
  44742, 187332, 1031, 102455, 11233, 14214, 44747, 252441, 73329, 5160, 238115, 1627, 51652,
  71232, 61831, 24405, 117431, 118107, 9053, 47511, 3129, 189, 7237, 2043, 6896, 13138, 42162,
  124039, 28, 140744, 41052, 190647, 130592, 374374, 132956, 4084, 43485
  ]
/-- Hit-row chunk `1` for `(m = 2, r = 512)`. -/
def rkmRowPack_m2_r512_p1 : List ℕ := [
  212, 5684, 176143, 26343, 3286, 414364, 104111, 123199, 346838, 48316, 516510, 147842, 109851,
  94439, 798, 41054, 224872, 98979, 285036, 8016, 67428, 626302, 12088, 580170, 1891534, 1414573,
  596306, 468, 1281195, 256460, 42407, 393776, 92601, 619773, 513787, 176303, 28124, 3643, 1896046,
  858498, 211826, 20990, 940248, 207812, 592804, 244801, 185703, 42982, 94769, 486042, 1718247,
  9156, 122034, 1051564, 63254, 404635, 1289723, 129260, 239589, 145848, 51476, 156030, 597494,
  90198, 214864, 91411, 2163251, 224428, 8011, 456507, 153504, 3384, 406568, 46380, 231238, 74714,
  27396, 86731, 379482, 235416, 3732742, 2744308, 188305, 410092, 24664, 400257, 1639857, 6749,
  780445, 677642, 277245, 139591, 246114, 1656289, 1462935, 3806
  ]
/-- Hit-row chunk `2` for `(m = 2, r = 512)`. -/
def rkmRowPack_m2_r512_p2 : List ℕ := [
  2202396, 1355659, 10682, 1356471, 241035, 86057, 417312, 9171, 442752, 386426, 123409, 1059033,
  1201301, 1584666, 181650, 443871, 31471, 399466, 1361506, 649867, 47417, 4028679, 3668217,
  316825, 110195, 1341354, 39760, 1261515, 342985, 41677, 924510, 3559469, 21643, 4791348, 6190377,
  81933, 64560, 64386, 33665, 4912, 38042, 23529, 1670434, 5026967, 6166927, 3894, 1906707,
  3238327, 24370, 10158, 2558508, 43407, 1037007, 122450, 1361504, 19397, 3492482, 45158, 350200,
  11973, 383255, 79189, 32936, 2616326, 1339, 1057639, 576094, 1409447, 1675078, 646229, 669085,
  1871033, 2189636, 503938, 432212, 975064, 1342363, 591659, 1163092, 34558, 229678, 89546,
  1151761, 30082, 1940465, 50681, 376886, 20049, 1155878, 74933, 856944, 4105405, 2064959, 45, 348,
  3008368
  ]
/-- Hit-row chunk `3` for `(m = 2, r = 512)`. -/
def rkmRowPack_m2_r512_p3 : List ℕ := [
  4276280, 4392850, 657652, 1052738, 581486, 1020666, 71412, 4571361, 2768423, 4761949, 3146585,
  2261532, 135313, 6112804, 5380671, 301937, 154859, 1241178, 201009, 40270, 3266023, 757334, 385,
  1505242, 4431624, 5706577, 754446, 181524, 909239, 5839686, 1838752, 4457795, 10119236, 914618,
  2858617, 799381, 21966, 74382, 15579, 829887, 1751698, 23386031, 19131635, 21010974, 3001204,
  2073061, 6834, 2864270, 6061132, 13292399, 47865, 43436945, 43718544, 8210101, 15971810,
  11980239, 1123373, 13800251, 4480691, 1707648, 597972, 724264, 2226810, 17185814, 2858694,
  4258505, 84392503, 39379228, 7510354, 63222667, 37089998, 113192, 28106139, 1414773, 955919,
  915201, 1244389, 921930, 29047703, 541697, 33803200, 35971317, 10249648, 119860464, 52634009,
  9335077, 46937970, 8988661, 35219683, 7581882, 377796, 5916, 55816516, 4390684, 70322575,
  184925502
  ]
/-- Hit-row chunk `4` for `(m = 2, r = 512)`. -/
def rkmRowPack_m2_r512_p4 : List ℕ := [
  15018817, 61470158, 80415896, 110944, 51842902, 49305453, 1665993, 1038564, 18884092, 3149649,
  17451987, 2373467, 54230522, 100561045, 2659422, 11484213, 52560720, 387044616, 297224796,
  9238009, 155958174, 3258563, 114614139, 39440079, 59652970, 231362642, 70639218, 14368562,
  10936762, 18286612, 131481788, 80457253, 50053240, 341833821, 70416326, 171365790, 178591980,
  120454, 159516525, 79867163, 76652531, 123725161, 143886, 79326825, 30026229, 312600, 25446507,
  97932700, 32510523, 25748299, 166986744, 5890966, 325606902, 391614752, 32481075, 321158617,
  65076592, 74503904, 161713809, 100718641, 447557877, 248588200, 6436862, 101725524, 48883727,
  24823262, 559463, 7375141, 195128590, 438152502, 1994333, 429558679, 129329237, 533314930,
  462810821, 60999108, 423519345, 108921172, 73799927, 7990, 364052143, 75779582, 197827387,
  952575473, 289862647, 255867430, 838306849, 150715719, 268175212, 1410034, 2228651, 297806278,
  10617236, 136709633, 326720561, 199289508
  ]
/-- Hit-row chunk `5` for `(m = 2, r = 512)`. -/
def rkmRowPack_m2_r512_p5 : List ℕ := [
  672953007, 968480982, 433363849, 446714238, 68032771, 655453746, 38782612, 71533118, 140418440,
  99169058, 172461, 133526202, 247011114, 98115331, 720756865, 133332044, 1402776434, 482851678,
  6267404230, 518164412, 3910206076, 190738835, 16272124450, 22764895049, 11507359, 15841745851,
  643184, 101166012443, 324758759483, 326759292462, 138337926299, 21464243033
  ]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 2, r = 512)`. -/
def rkmRowPack_m2_r512 : List ℕ :=
  rkmRowPack_m2_r512_p0 ++ (rkmRowPack_m2_r512_p1 ++ (rkmRowPack_m2_r512_p2
    ++ (rkmRowPack_m2_r512_p3 ++ (rkmRowPack_m2_r512_p4 ++ rkmRowPack_m2_r512_p5))))

end

public section

private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => List.cons x (pCat xs ys)
private def pNatCat : List (List ℕ) → List ℕ
  | [] => []
  | ws :: wss => pCat ws (pNatCat wss)
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private theorem bNatBle_le : ∀ {a b : ℕ}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (bNatBle_le h)
private def bNatEq (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem bNatEq_true {a b : ℕ} (h : bNatEq a b = true) : a = b := by
  unfold bNatEq at h; revert h
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
    unfold bNLE at h; revert h
    cases hx : bNatEq x y with
    | false => exact Bool.noConfusion
    | true => exact fun h => congrArg₂ List.cons (bNatEq_true hx) (bNLE_true h)
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β :=
  HighDForce.withForcedList xs k
private abbrev bZ : ℕ := 2000000000000000
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem n0m (z : ℕ) : (0 : ℕ) = Nat.mul 0 z := by rw [Nat.mul_eq]; omega
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem nmod (x y : ℕ) : Nat.mod x y = x % y := rfl
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 => xs
  | v + 1 =>
    match xs with
    | [] => [v]
    | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => List.cons (Int.ofNat n) (uOfNatHb ns)
private def bConsZ (x : ℤ) (xs : List ℤ) : List ℤ :=
  match x with
  | Int.ofNat v =>
    match xs with
    | [] => [Int.ofNat v]
    | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v =>
    match xs with
    | [] => [Int.negSucc v]
    | h :: t => Int.negSucc v :: h :: t
private theorem bConsZ_eq (x : ℤ) (xs : List ℤ) : bConsZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem bOfNatF_eq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  simp [primOfNatForced, Nat.one_add]
private theorem bNegSuccF_eq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  simp [primNegSuccForced, Nat.one_add]
private theorem bSub_eq (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat; rw [bOfNatF_eq, Nat.sub_eq]; cases h : z - u with
  | zero => dsimp only; rw [Nat.sub_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bConsZ (rkmForcedSubNatNat u z) (bDec z us)
private theorem bDec_nil (z : ℕ) : bDec z [] = [] := rfl
private theorem bDec_cons (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by rw [bDec, bConsZ_eq, bSub_eq]
private theorem bDec_len (z : ℕ) : ∀ (cs : List ℕ), altIntLen (bDec z cs) = altListLen cs
  | [] => rfl
  | u :: cs => by rw [bDec_cons z u cs, altIntLen, altListLen, bDec_len z cs]
private theorem bZero_eq (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bMul0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZero_eq]; rfl
private def zTdiv (x : ℤ) (d : ℕ) : ℤ :=
  match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTdivNat_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => by dsimp only [muxRawIntTdivNat, zTdiv]; rw [bNeg_eq, ndiv, Nat.add_eq]
private theorem bSubNatTdiv_eq (m n d : ℕ) :
    rkmUltraSubNatTdiv m n d = zTdiv ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    dsimp only; have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTdiv]; rw [bNeg_eq]
private theorem bSubTdiv_eq (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTdiv (a - b) d := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact bSubNatTdiv_eq m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
      rw [hm]; rfl
  | negSucc m =>
    cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTdiv]; rw [bNeg_eq, ndiv, Nat.add_eq]
      rw [Nat.add_eq]; exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [bSubNatTdiv_eq, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTdiv t d) (by simp only [Int.negSucc_eq]; omega)
private theorem bMul_eq (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a <;> cases b <;>
    simp only [muxRawIntMul, bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast,
      Int.negSucc_eq] <;> push_cast <;> ring
private theorem bForcedAdd_eq (a b : ℤ) : rkmForcedIntAdd a b = a + b := by
  cases a <;> cases b <;>
    simp only [rkmForcedIntAdd, bOfNatF_eq, bNegSuccF_eq, bSub_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
private theorem bAddCons_eq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bForcedAdd_eq]; cases a + b <;> cases xs <;> rfl
private abbrev bStepVal (v P Q d : ℕ) : ℕ :=
  Nat.sub (Nat.add v (Nat.div (Nat.sub P Q) d)) (Nat.div (Nat.sub Q P) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSubNatTdiv_eq]; unfold bStepVal at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv
  cases hd : Q - P with
  | zero =>
    intro _; dsimp only; rw [Nat.zero_div, Nat.sub_zero, Int.ofNat_eq_natCast]; push_cast; ring
  | succ k =>
    intro hv; dsimp only at hv ⊢
    have hpq : P - Q = 0 := by omega
    rw [hpq, Nat.zero_div, Nat.add_zero] at hv ⊢; rw [bNeg_eq]; omega
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCV z d b0 c0 b v c1) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bAddCons_eq, bSubTdiv_eq, bMul_eq, bMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCV at hv ⊢; rw [bStepVal_eq z v _ _ d hv, hpq]
private theorem bCell_nil (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bAddCons_eq, bTdivNat_eq, bMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
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
    ((bHeadOr z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq]
  | _ :: _ => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | _ :: _ => by unfold bTailN; rw [bDec_cons]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs =>
    match bns with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSl z d rem 0 z [] (bTailN vs) (bTailN cs))
    | b :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCV z d b0 c0 b v (bHeadOr z cT)) (bSl z d rem b c bR vT cT)
      | v :: vT, [] => uConsNat (bCV z d b0 c0 b v z) (bSl z d rem b z bR vT [])
      | [], c :: cT => uConsNat (bCV z d b0 c0 b z (bHeadOr z cT)) (bSl z d rem b c bR [] cT)
      | [], [] => uConsNat (bCV z d b0 c0 b z z) (bSl z d rem b z bR [] [])
private theorem bSl_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSl z d rem b0 c0 bns vs cs) = true →
      bDec z (bSl z d rem b0 c0 bns vs cs) =
        rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSl, uOfNatHb, rkmUltraSlideLoopAux] at h ⊢; have hp := bAllPos_uCons h
      have hi := bSl_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp.2
      rw [bMul0, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi; rw [bHeadOr_eq z vs] at hc; exact hc
    | cons b bR =>
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_nil, rkmUltraSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSl_sound z d rem b z bR [] [] hp.2
          rw [bZero_eq z, bDec_nil] at hi; have hc := bCell_hb z d b0 c0 b z z hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_nil, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSl_sound z d rem b c bR [] cT hp.2; rw [bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b z (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT, bZero_eq z] at hc; exact hc
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_cons z v vT, bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSl_sound z d rem b z bR vT [] hp.2
          rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b v z hp.1 hi; rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uOfNatHb] at h ⊢; rw [bDec_cons z v vT, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSl_sound z d rem b c bR vT cT hp.2
          have hc := bCell_hb z d b0 c0 b v (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT] at hc; exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uConsNat b (uConsNat (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | [] =>
      uConsNat (bStepVal (bHeadOr z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTailN vs) (bTailN cs))
    | [_] => []
    | b :: bz :: bR =>
      match vs, cs with
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
    bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs = bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTailN vs) (bTailN cs)
      dsimp only [mkHbZ] at hrec; rw [← n0m z] at hrec; dsimp only [mkHbZ, bSlZ, bSl]; rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ]; rw [uConsNat_eq, uConsNat_eq]; cases vs with
      | nil =>
        cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT =>
        cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR vT cT]
private theorem bSlZ_pfx (z d : ℕ) : ∀ (rem : ℕ) (l t : List ℕ) (p0 q0 : ℕ) (vs cs : List ℕ),
    2 * rem ≤ l.length → bSlZ z d rem p0 q0 (l ++ t) vs cs = bSlZ z d rem p0 q0 l vs cs
  | 0, _, _, _, _, _, _, _ => rfl
  | rem + 1, [], _, _, _, _, _, h => by change 2 * (rem + 1) ≤ 0 at h; omega
  | rem + 1, [_], _, _, _, _, _, h => by change 2 * (rem + 1) ≤ 1 at h; omega
  | rem + 1, b :: bz :: l, t, p0, q0, vs, cs, h => by
    change 2 * (rem + 1) ≤ l.length + 2 at h
    have hl : 2 * rem ≤ l.length := by omega
    have ha : (b :: bz :: l) ++ t = b :: bz :: (l ++ t) := rfl
    rw [ha]; cases vs with
    | nil =>
      cases cs with
      | nil => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t bz bz [] [] hl]
      | cons c cT => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t (Nat.mul b c) bz [] cT hl]
    | cons v vT =>
      cases cs with
      | nil => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t bz bz vT [] hl]
      | cons c cT => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t (Nat.mul b c) bz vT cT hl]
private inductive HbZ4 : Type
  | tail : List ℕ → HbZ4
  | c4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → HbZ4 → HbZ4
private abbrev hbz4P (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) : List ℕ := [b1, z1, b2, z2, b3, z3, b4, z4]
private abbrev hbz4C (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) : List ℕ :=
  b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: t
private theorem hbz4C_app (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) :
    hbz4C b1 z1 b2 z2 b3 z3 b4 z4 t = hbz4P b1 z1 b2 z2 b3 z3 b4 z4 ++ t := rfl
private theorem hbz4P_len (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) :
    (hbz4P b1 z1 b2 z2 b3 z3 b4 z4).length = 8 := rfl
private def hbz4L : HbZ4 → List ℕ
  | HbZ4.tail l => l
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L r)
private def fH4 {α : Type} (h : HbZ4) (k : HbZ4 → α) : α :=
  match h with
  | HbZ4.tail l => fL l fun lF => k (HbZ4.tail lF)
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => k (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r)
private theorem fH4_eq {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ => dsimp only [fH4, fL]; rw [rkmb_forceList_eq]
  | c4 _ _ _ _ _ _ _ _ _ => rfl
private def toH4 : List ℕ → HbZ4
  | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs =>
    match toH4 bs with
    | HbZ4.tail l => HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.tail l)
    | HbZ4.c4 a1 w1 a2 w2 a3 w3 a4 w4 t =>
      HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.c4 a1 w1 a2 w2 a3 w3 a4 w4 t)
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
    dsimp only [toH4]; cases h : toH4 bs with
    | tail _ => have ih := hbz4L_toH4 bs; rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
    | c4 _ _ _ _ _ _ _ _ _ =>
      have ih := hbz4L_toH4 bs; rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
private def takeH4 : ℕ → HbZ4 → List ℕ
  | 0, _ => []
  | _ + 1, HbZ4.tail l => l
  | k + 1, HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r =>
    hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (takeH4 k r)
private theorem takeH4_spec : ∀ (k : ℕ) (hbz : HbZ4),
    takeH4 k hbz = hbz4L hbz ∨
      ∃ t, hbz4L hbz = takeH4 k hbz ++ t ∧ 8 * k ≤ (takeH4 k hbz).length
  | 0, hbz => Or.inr ⟨hbz4L hbz, rfl, Nat.zero_le _⟩
  | _ + 1, HbZ4.tail _ => Or.inl rfl
  | k + 1, HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => by
    dsimp only [takeH4, hbz4L]
    cases takeH4_spec k r with
    | inl heq => exact Or.inl (congrArg (hbz4C b1 z1 b2 z2 b3 z3 b4 z4) heq)
    | inr hex =>
      cases hex with
      | intro t hp =>
        refine Or.inr ⟨t, ?_, ?_⟩
        · rw [hbz4C_app, hbz4C_app, hp.1, List.append_assoc]
        · rw [hbz4C_app, List.length_append, hbz4P_len]; omega
private theorem bSlZ_takeH4 (z d k : ℕ) (hbz : HbZ4) (rem p0 q0 : ℕ)
    (vs cs : List ℕ) (h : rem ≤ 4 * k) :
    bSlZ z d rem p0 q0 (takeH4 k hbz) vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs := by
  cases takeH4_spec k hbz with
  | inl heq => rw [heq]
  | inr hex =>
    cases hex with
    | intro t hp =>
      rw [hp.1]; exact (bSlZ_pfx z d rem (takeH4 k hbz) t p0 q0 vs cs (by omega)).symm
private inductive Q4 : Type
  | tail : List ℕ → Q4
  | c4 : ℕ → ℕ → ℕ → ℕ → Q4 → Q4
private def q4L : Q4 → List ℕ
  | Q4.tail xs => xs
  | Q4.c4 x1 x2 x3 x4 r => List.cons x1 (List.cons x2 (List.cons x3 (List.cons x4 (q4L r))))
private def q4S (x1 x2 x3 x4 : ℕ) (r : Q4) : Q4 :=
  match Nat.add 1 x1 with
  | 0 => r
  | v1 + 1 =>
    match Nat.add 1 x2 with
    | 0 => r
    | v2 + 1 =>
      match Nat.add 1 x3 with
      | 0 => r
      | v3 + 1 =>
        match Nat.add 1 x4 with
        | 0 => r
        | v4 + 1 =>
          match r with
          | Q4.tail xs => Q4.c4 v1 v2 v3 v4 (Q4.tail xs)
          | Q4.c4 y1 y2 y3 y4 yr => Q4.c4 v1 v2 v3 v4 (Q4.c4 y1 y2 y3 y4 yr)
private theorem q4S_eq (x1 x2 x3 x4 : ℕ) (r : Q4) : q4S x1 x2 x3 x4 r = Q4.c4 x1 x2 x3 x4 r := by
  unfold q4S; rw [n1a x1, n1a x2, n1a x3, n1a x4]; cases r <;> rfl
private def toQ4 : List ℕ → Q4
  | x1 :: x2 :: x3 :: x4 :: xs => q4S x1 x2 x3 x4 (toQ4 xs)
  | [] => Q4.tail []
  | [x1] => fN x1 fun y1 => Q4.tail [y1]
  | [x1, x2] => fN x1 fun y1 => fN x2 fun y2 => Q4.tail [y1, y2]
  | [x1, x2, x3] => fN x1 fun y1 => fN x2 fun y2 => fN x3 fun y3 => Q4.tail [y1, y2, y3]
private theorem q4L_toQ4 : ∀ (xs : List ℕ), q4L (toQ4 xs) = xs
  | [] => rfl
  | [_] => by dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq]; rfl
  | [_, _] => by dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq, rkmb_forceNat_eq]; rfl
  | [_, _, _] =>
    by dsimp only [toQ4, fN]; rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq]; rfl
  | x1 :: x2 :: x3 :: x4 :: xs => by
    dsimp only [toQ4]; rw [q4S_eq]; dsimp only [q4L]; rw [q4L_toQ4 xs]
private def q4Hd (z : ℕ) : Q4 → ℕ
  | Q4.c4 x _ _ _ _ => x
  | Q4.tail xs => bHeadOr z xs
private theorem q4Hd_eq (z : ℕ) (w : Q4) : q4Hd z w = bHeadOr z (q4L w) := by
  cases w <;> rfl
private def q4AP : Q4 → Bool
  | Q4.tail xs => bAllPos xs
  | Q4.c4 x1 x2 x3 x4 r =>
    match Nat.add (Nat.add (Nat.sub 1 x1) (Nat.sub 1 x2))
        (Nat.add (Nat.sub 1 x3) (Nat.sub 1 x4)) with
    | 0 => q4AP r
    | _ + 1 => false
private theorem pos1_false {x : ℕ} (h : (1 - x) = 0) : Nat.ble x 0 = false := by
  cases x with
  | zero => cases h
  | succ _ => rfl
private theorem q4AP_pos : ∀ (w : Q4), q4AP w = true → bAllPos (q4L w) = true
  | Q4.tail _, h => h
  | Q4.c4 x1 x2 x3 x4 r, h => by
    dsimp only [q4AP] at h; revert h
    cases hs : Nat.add (Nat.add (Nat.sub 1 x1) (Nat.sub 1 x2))
        (Nat.add (Nat.sub 1 x3) (Nat.sub 1 x4)) with
    | succ _ => intro h; dsimp only at h; cases h
    | zero =>
      intro h; dsimp only at h; simp only [Nat.add_eq, Nat.sub_eq] at hs
      have h1 : 1 - x1 = 0 := by omega
      have h2 : 1 - x2 = 0 := by omega
      have h3 : 1 - x3 = 0 := by omega
      have h4 : 1 - x4 = 0 := by omega
      dsimp only [q4L, bAllPos]
      rw [pos1_false h1, pos1_false h2, pos1_false h3, pos1_false h4]
      exact q4AP_pos r h
private def bChkV (out : Q4) : Option Q4 :=
  match out with
  | Q4.tail xs => cond (bAllPos xs) (some (Q4.tail xs)) none
  | Q4.c4 x1 x2 x3 x4 r =>
    cond (q4AP (Q4.c4 x1 x2 x3 x4 r)) (some (Q4.c4 x1 x2 x3 x4 r)) none
private theorem bChkV_eq (out : Q4) : bChkV out = cond (q4AP out) (some out) none := by
  cases out <;> rfl
private def bSlQ4 (z d rT : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Q4 → Q4
  | 0, p0, q0, hbz, vs, cs => toQ4 (bSlZ z d rT p0 q0 (takeH4 1 hbz) (q4L vs) (q4L cs))
  | q + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | HbZ4.tail l =>
      toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0 l (q4L vs) (q4L cs))
    | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
      match vs with
      | Q4.tail vxs =>
        toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
          (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)) vxs (q4L cs))
      | Q4.c4 v1 v2 v3 v4 vR =>
        match cs with
        | Q4.tail cxs =>
          toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
            (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR))
            (v1 :: v2 :: v3 :: v4 :: q4L vR) cxs)
        | Q4.c4 c1 c2 c3 c4 cR =>
          match Nat.add 1 (Nat.mul b4 c4) with
          | 0 => Q4.tail []
          | bc4 + 1 =>
            q4S (bStepVal v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
              (bStepVal v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
              (bStepVal v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
              (bStepVal v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
              (bSlQ4 z d rT q bc4 z4 bR vR cR)
private theorem bSlQ4_eq (z d rT : ℕ) (hr : rT ≤ 4) :
    ∀ (q p0 q0 : ℕ) (hbz : HbZ4) (vs cs : Q4),
    q4L (bSlQ4 z d rT q p0 q0 hbz vs cs) =
      bSlZ z d (4 * q + rT) p0 q0 (hbz4L hbz) (q4L vs) (q4L cs)
  | 0, p0, q0, hbz, vs, cs => by
    dsimp only [bSlQ4]; rw [q4L_toQ4]
    have h0 : 4 * 0 + rT = rT := by omega
    rw [h0]; exact bSlZ_takeH4 z d 1 hbz rT p0 q0 (q4L vs) (q4L cs) hr
  | q + 1, p0, q0, hbz, vs, cs => by
    have hrem : Nat.add (Nat.mul 4 (Nat.add q 1)) rT = 4 * (q + 1) + rT := by
      simp only [Nat.add_eq, Nat.mul_eq]
    have hq2 : Nat.add q 2 = q + 2 := by rw [Nat.add_eq]
    have hle : 4 * (q + 1) + rT ≤ 4 * (q + 2) := by omega
    cases hbz with
    | tail l => dsimp only [bSlQ4, hbz4L]; rw [q4L_toQ4, hrem]
    | c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
      cases vs with
      | tail vxs =>
        dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
        exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
          (4 * (q + 1) + rT) p0 q0 vxs (q4L cs) hle
      | c4 v1 v2 v3 v4 vR =>
        cases cs with
        | tail cxs =>
          dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
          exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
            (4 * (q + 1) + rT) p0 q0 (v1 :: v2 :: v3 :: v4 :: q4L vR) cxs hle
        | c4 c1 c2 c3 c4 cR =>
          dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq]
          have h4 : 4 * (q + 1) + rT = ((((4 * q + rT) + 1) + 1) + 1) + 1 := by omega
          rw [h4]; dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHeadOr]
          rw [uConsNat_eq, uConsNat_eq, uConsNat_eq, uConsNat_eq]
          rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR vR cR]
private def bStg (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.div nL 4) fun q4 => fN (Nat.mod nL 4) fun rT =>
    fN (Nat.mul dg wdScale) fun d => bChkV (bSlQ4 z d rT q4 0 0 h4 vs cs)
private theorem bStg_sound (bns : List ℕ) {z dg mL cL : ℕ} {vs cs out : Q4}
    (h : bStg z dg mL cL (toH4 (mkHbZ z bns)) vs cs = some out) :
    bDec z (q4L out) =
      rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z (q4L vs)) (bDec z (q4L cs)) := by
  unfold bStg at h; dsimp only [fN] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, bChkV_eq] at h
  have hr : Nat.mod (rkmNextLen mL cL) 4 ≤ 4 := by rw [nmod]; omega
  have hqr : 4 * Nat.div (rkmNextLen mL cL) 4 + Nat.mod (rkmNextLen mL cL) 4 =
      rkmNextLen mL cL := by rw [ndiv, nmod]; omega
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns (q4L vs) (q4L cs)
  rw [← n0m z] at hsl
  have heq : q4L (bSlQ4 z (Nat.mul dg wdScale) (Nat.mod (rkmNextLen mL cL) 4)
      (Nat.div (rkmNextLen mL cL) 4) 0 0 (toH4 (mkHbZ z bns)) vs cs) =
      bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns (q4L vs) (q4L cs) := by
    rw [bSlQ4_eq _ _ _ hr, hqr, hbz4L_toH4, hsl]
  revert h
  cases hv : q4AP (bSlQ4 z (Nat.mul dg wdScale) (Nat.mod (rkmNextLen mL cL) 4)
      (Nat.div (rkmNextLen mL cL) 4) 0 0 (toH4 (mkHbZ z bns)) vs cs) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; dsimp only [cond] at h; injection h with h'
    have hp := q4AP_pos _ hv
    rw [heq] at hp; rw [← h', heq]
    unfold rkmUltraHornerStage; rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]
    exact bSl_sound z _ _ 0 z bns (q4L vs) (q4L cs) hp
private def bBind (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4)
    (k : ℕ → Q4 → Option Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL =>
    match bStg z dg mL cL h4 vs cs with
    | none => none
    | some out => k nL out
private theorem bBind_sound (bns : List ℕ) {z dg mL cL : ℕ} {vs cs out : Q4}
    {kB : ℕ → Q4 → Option Q4} {kU : ℕ → List ℤ → List ℤ}
    (h : bBind z dg mL cL (toH4 (mkHbZ z bns)) vs cs kB = some out)
    (hk : ∀ (mid : Q4), kB (rkmNextLen mL cL) mid = some out →
      bDec z (q4L out) = kU (rkmNextLen mL cL) (bDec z (q4L mid))) :
    bDec z (q4L out) = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z (q4L vs)) (bDec z (q4L cs)))
        (kU nL)) := by
  unfold bBind at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
  revert h; cases hs : bStg z dg mL cL (toH4 (mkHbZ z bns)) vs cs with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound bns hs]
    exact hk mid h
private def bStep (z mL c : ℕ) (h4 : HbZ4) (vs : Q4) : Option Q4 :=
  bBind z 16 mL c h4 vs vs fun l1 c1 => bBind z 15 mL l1 h4 vs c1 fun l2 c2 =>
  bBind z 14 mL l2 h4 vs c2 fun l3 c3 => bBind z 13 mL l3 h4 vs c3 fun l4 c4 =>
  bBind z 12 mL l4 h4 vs c4 fun l5 c5 => bBind z 11 mL l5 h4 vs c5 fun l6 c6 =>
  bBind z 10 mL l6 h4 vs c6 fun l7 c7 => bBind z 9 mL l7 h4 vs c7 fun l8 c8 =>
  bBind z 8 mL l8 h4 vs c8 fun l9 c9 => bBind z 7 mL l9 h4 vs c9 fun la ca =>
  bBind z 6 mL la h4 vs ca fun lb cb => bBind z 5 mL lb h4 vs cb fun lc cc =>
  bBind z 4 mL lc h4 vs cc fun ld cd => bBind z 3 mL ld h4 vs cd fun le ce =>
  bBind z 2 mL le h4 vs ce fun lf cf => bStg z 1 mL lf h4 vs cf
private theorem bStep_sound (bns : List ℕ) {z mL cL : ℕ} {vs out : Q4}
    (h : bStep z mL cL (toH4 (mkHbZ z bns)) vs = some out) :
    bDec z (q4L out) = rkmUltraHornerT16Step mL cL (uOfNatHb bns) (bDec z (q4L vs)) := by
  unfold bStep at h; unfold rkmUltraHornerT16Step
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  refine bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => bBind_sound bns h fun _ h => ?_
  exact bStg_sound bns h
private def bIter (z : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Option Q4
  | 0, _, _, _, vs => some vs
  | k + 1, mL, cL, h4, vs =>
    match bStep z mL cL h4 vs with
    | none => none
    | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL h4 vNext
private theorem bIter_sound (bns : List ℕ) (z : ℕ) : ∀ (k mL cL : ℕ) (vs out : Q4),
    bIter z k mL cL (toH4 (mkHbZ z bns)) vs = some out →
    bDec z (q4L out) = muxUltraIterFullT16Rkm k mL cL (uOfNatHb bns) (bDec z (q4L vs))
  | 0, _, _, _, _, h => by injection h with h'; rw [← h']; rfl
  | k + 1, mL, cL, vs, out, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL cL (toH4 (mkHbZ z bns)) vs with
    | none => intro h; dsimp only at h; cases h
    | some vNext =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bStep_sound bns hs]
      exact bIter_sound bns z k mL (rkmNextLen16 mL cL) vNext out h
private def fQ4 {α : Type} (v : Q4) (k : Q4 → α) : α :=
  match v with
  | Q4.tail xs => k (Q4.tail xs)
  | Q4.c4 x1 x2 x3 x4 r => k (Q4.c4 x1 x2 x3 x4 r)
private theorem fQ4_eq {α : Type} (v : Q4) (k : Q4 → α) : fQ4 v k = k v := by
  cases v <;> rfl
private def fSp : List ℕ → List ℕ
  | [] => []
  | x :: xs => uConsNat x (fSp xs)
private theorem fSp_eq : ∀ (xs : List ℕ), fSp xs = xs
  | [] => rfl
  | x :: xs => by dsimp only [fSp]; rw [uConsNat_eq, fSp_eq xs]
private def bSlideChk (k mL : ℕ) (bns vns out : List ℕ) : Bool :=
  fL (fSp bns) fun bF => fL (fSp vns) fun vF => fL (fSp out) fun oF =>
    fN (altListLen vF) fun cL =>
      fH4 (toH4 (mkHbZ bZ bF)) fun h4 =>
        fQ4 (toQ4 vF) fun vs0 =>
          match bIter bZ k mL cL h4 vs0 with
          | none => false
          | some w => bNLE (q4L w) oF
private abbrev pWOk (k mL : ℕ) (bns : List ℕ) (vi : List ℤ) (vo : List ℕ) : Prop :=
  muxFastIterFullT16 k mL (uOfNatHb bns) vi = bDec bZ vo
private theorem bSlSndNN {k mL : ℕ} {bns vns out : List ℕ}
    (h : bSlideChk k mL bns vns out = true) : pWOk k mL bns (bDec bZ vns) out := by
  unfold bSlideChk fL fN at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, fH4_eq, fQ4_eq,
    fSp_eq bns, fSp_eq vns, fSp_eq out] at h
  revert h
  cases hi : bIter bZ k mL (altListLen vns) (toH4 (mkHbZ bZ bns)) (toQ4 vns) with
  | none => intro h; exact Bool.noConfusion h
  | some w =>
    intro h; change bNLE (q4L w) out = true at h
    have hw := bIter_sound bns bZ k mL (altListLen vns) (toQ4 vns) w hi
    rw [bNLE_true h, q4L_toQ4 vns, ← bDec_len bZ vns] at hw
    have h2 :
        muxUltraIterFullT16HiChk k 0 mL (uOfNatHb bns) (bDec bZ vns) (bDec bZ out) = true := by
      unfold muxUltraIterFullT16HiChk; dsimp only
      rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq]
      exact muxIntListEq_eq_true.mpr hw.symm
    exact muxUltraIterFullT16HiChk_sound h2
private theorem pChnN {k1 k2 mL : ℕ} {bns : List ℕ} {vi : List ℤ} {vm vo : List ℕ}
    (kS : ℕ) (h1 : pWOk k1 mL bns vi vm) (h2 : bSlideChk k2 mL bns vm vo = true)
    (hk : k1 + k2 = kS) : pWOk kS mL bns vi vo := by
  unfold pWOk at h1 ⊢; rw [← hk, muxFastIterFullT16_add, h1]; exact bSlSndNN h2
private theorem bSeg_mk {n d mL : ℕ} {bns v0 vl : List ℕ} {hb vi vo : List ℤ}
    (hd : d = mL) (hw : pWOk n mL bns (bDec bZ v0) vl)
    (hhb : hb = uOfNatHb bns) (hvi : vi = bDec bZ v0) (hvo : vo = bDec bZ vl) :
    muxFastIterFullT16 n d hb vi = vo := by
  rw [hd, hhb, hvi, hvo]; exact hw
private def pb_m2_r512_4 : List ℕ := pNatCat
  [
   [85213691697152,120274986704050,147017902724977,169428785444728,189054985316912,
    206691684227986,222812194694076,237725511880804,251646683293152,264732587613228,
    277101884501873,288846938294955,300041342564122,310744880971621,321006917945971,
    330868787292848,340365518753170,349527114002964,358379508071630,366945306146604,
    375244356806296,383294204027591,391110447931515,398707035848068,406096499494240,
    413290149992716,420298239554935,427130096547933,433794239119023,440298471403251,
    446649965474365,452855331543235,458920678403500,464851665733793,470653549560860,
    476331221947752,481889245780739,487331885376440,492663133508242,497886735352115,
    503006209771292,508024868293360,512945832079027,517772047136966,522506298001859,
    527151220061661,531709310694029,536182939349918,540574356703808,544885702974319,
    549119015505571,553276235688242,557359215289467,561369722252341,565309446018493,
    569180002420965,572982938189173,576719735103007,580391813829010,584000537467972,
    587547214840120,591033103531332,594459412721350,597827305812832],
   [601137902878176,604392282939388,607591486094738,610736515504681,613828339248270,
    616867892060307,619856076958478,622793766768919,625681805557875,628521009976460,
    631312170524903,634056052742115,636753398325926,639404926188889,642011333454143,
    644573296395456,647091471325248,649566495434086,651998987584864,654389549064639,
    656738764296858,659047201516523,661315413410616,663543937725972,665733297846601,
    667884003342319,669996550490440,672071422772114,674109091344821,676110015492416,
    678074643054007,680003410832901,681896744986716,683755061399739,685578766038499,
    687368255291480,689123916293833,690846127237902,692535257670300,694191668776267,
    695815713651956,697407737565278,698968078205893,700497065924893,701995023964698,
    703462268679652,704899109747776,706305850374108,707682787486048,709030211921074,
    710348408607211,711637656736580,712898229932355,714130396409441,715334419129149,
    716510555948147,717659059761952,718780178643190,719874155974884,720941230578955,
    721981636840175,722995604825756,723983360400752,724945125339482],
   [725881117433111,726791550593568,727676634953950,728536576965556,729371579491691,
    730181841898367,730967560142032,731728926854446,732466131424812,733179360079271,
    733868795957876,734534619189125,735177006962164,735796133596734,736392170610967,
    736965286787088,737515648235124,738043418454686,738548758394887,739031826512478,
    739492778828263,739931768981844,740348948284780,740744465772189,741118468252871,
    741471100357995,741802504588390,742112821360516,742402189051131,742670744040715,
    742918620755694,743145951709499,743352867542499,743539497060852,743705967274303,
    743852403432970,743978929063146,744085666002155,744172734432286,744240252913839,
    744288338417312,744317106354752,744326670610309,744317143569993,744288636150690,
    744241257828436,744175116665987,744090319339691,743986971165708,743865176125566,
    743725036891105,743566654848799,743390130123504,743195561601614,742983046953679,
    742752682656473,742504564014543,742238785181247,741955439179304,741654617920856,
    741336412227073,741000911847302,740648205477773,740278380779886],
   [739891524398080,739487721977288,739067058180021,738629616703048,738175480293721,
    737704730765934,737217449015727,736713715036552,736193607934211,735657205941462,
    735104586432316,734535825936024,733951000150769,733350183957067,732733451430880,
    732100875856459,731452529738918,730788484816544,730108812072850,729413581748389,
    728702863352313,727976725673707,727235236792684,726478464091265,725706474264033,
    724919333328574,724117106635716,723299858879557,722467654107301,721620555728899,
    720758626526498,719881928663715,718990523694720,718084472573149,717163835660853,
    716228672736466,715279043003819,714315005100194,713336617104418,712343936544813,
    711337020406986,710315925141486,709280706671310,708231420399277,707168121215261,
    706090863503296,704999701148552,703894687544179,702775875598034,701643317739285,
    700497065924893,699337171645984,698163685934108,696976659367379,695776142076520,
    694562183750790,693334833643814,692094140579314,690840152956732,689572918756766,
    688292485546804,686998900486266,685692210331862,684372461442752],
   [683039699785619,681693970939669,680335320101531,678963792090083,677579431351202,
    676182281962427,674772387637549,673349791731130,671914537242936,670466666822313,
    669006222772480,667533247054757,666047781292730,664549866776335,663039544465896,
    661516854996082,659981838679808,658434535512079,656874985173763,655303227035315,
    653719300160437,652123243309678,650515094943992,648894893228223,647262676034550,
    645618480945869,643962345259138,642294305988649,640614399869275,638922663359648,
    637219132645300,635503843641754,633776831997568,632038133097334,630287782064635,
    628525813764956,626752262808548,624967163553260,623170550107320,621362456332081,
    619542915844725,617711962020928,615869627997486,614015946674906,612150950719956,
    610274672568181,608387144426383,606488398275066,604578465870845,602657378748821,
    600725168224927,598781865398233,596827501153229,594862106162067,592885710886778,
    590898345581456,588900040294411,586890824870295,584870728952199,582839781983715,
    580798013210983,578745451684695,576682126262085,574608065608882],
   [572523298201245,570427852327667,568321756090857,566205037409592,564077724020550,
    561939843480119,559791423166174,557632490279842,555463071847236,553283194721169,
    551092885582847,548892170943537,546681077146217,544459630367201,542227856617748,
    539985781745646,537733431436777,535470831216663,533198006451994,530914982352133,
    528621783970602,526318436206555,524004963806227,521681391364367,519347743325651,
    517004043986082,514650317494370,512286587853294,509912878921046,507529214412567,
    505135617900856,502732112818266,500318722457793,497895469974335,495462378385947,
    493019470575077,490566769289785,488104297144951,485632076623469,483150130077422,
    480658479729248,478157147672888,475646155874927,473125526175713,470595280290472,
    468055439810398,465506026203745,462947060816895,460378564875419,457800559485123,
    455213065633081,452616104188666,450009695904551,447393861417718,444768621250443,
    442133995811269,439490005395982,436836670188558,434174010262109,431502045579823,
    428820795995878,426130281256363,423430521000177,420721534759924],
   [418003341962795,415275961931440,412539413884834,409793716939132,407038890108509,
    404274952306002,401501922344329,398719818936715,395928660697694,393128466143911,
    390319253694913,387501041673934,384673848308665,381837691732024,378992589982911,
    376138561006960,373275622657277,370403792695181,367523088790923,364633528524407,
    361735129385902,358827908776746,355911884010040,352987072311337,350053490819325,
    347111156586503,344160086579846,341200297681465,338231806689264,335254630317587,
    332268785197856,329274287879207,326271154829118,323259402434027,320239046999953,
    317210104753097,314172591840453,311126524330396,308071918213278,305008789402013,
    301937153732651,298857026964955,295768424782967,292671362795571,289565856537044,
    286451921467615,283329572974002,280198826369957,277059696896798,273912199723940,
    270756349949418,267592162600404,264419652633727,261238834936376,258049724326005,
    254852335551437,251646683293152,248432782163780,245210646708587,241980291405952,
    238741730667848,235494978840306,232240050203889,228976958974149],
   [225705719302089,222426345274614,219138850914980,215843250183244,212539556976699,
    209227785130315,205907948417169,202580060548878,199244135176018,195900185888551,
    192548226216239,189188269629056,185820329537600,182444419293500,179060552189811,
    175668741461422,172269000285444,168861341781601,165445779012624,162022324984626,
    158590992647490,155151794895244,151704744566433,148249854444491,144787137258109,
    141316605681595,137838272335242,134352149785677,130858250546222,127356587077241,
    123847171786489,120330017029459,116805135109722,113272538279266,109732238738831,
    106184248638248,102628580076759,99065245103354,95494255717090,91915623867415,88329361454485,
    84735480329482,81133992294926,77524909104987,73908242465792,70284004035731,66652205425761,
    63012858199703,59365973874542,55711563920725,52049639762448,48380212777949,44703294299798,
    41018895615177,37327027966169,33627702550035,29920930519492,26206722982994,22485091004996,
    18756045606237,15019597763999,11275758412382,7524538442563,3765948703062]]
private def pv_m2_r512_4_0 : List ℕ := pNatCat
  [
   [1999982358005967,1999998912049076,2000025302471992,1999970380915830,1999989921259744,
    2000008488789077,1999985648092113,1999979507547094,1999965812668635,1999961076129168,
    1999981039284238,2000010588233989,2000021307026654,2000006272996042,2000005569231988,
    1999995008640900,1999968006157978,1999956441994282,2000030521260018,2000004304504502,
    2000019616509971,2000035545823913,2000048210498429,2000051525494471,2000039410848937,
    2000021268250764,1999987178079760,1999978214893730,1999965840052708,1999972949634647,
    2000000496910730,1999977165790265,2000024165640509,1999993736742770,2000008670380737,
    1999996997203526,1999984021462378,1999971316084125,1999973605168802,1999985366663102,
    2000003483046683,1999997577025868,1999993290243522,2000011675450356,1999988556231622,
    2000001826446554,1999990063096496,2000011944531814,2000000223707512,1999983447018531,
    2000022969479315,2000011111170202,1999990376640317,2000021288268983,2000015609056547,
    2000000195143865,2000013100432341,2000016029447554,2000012441327971,1999988443569577,
    1999982527335724,1999976394646758,1999979751492567,1999994005643398],
   [1999989121675292,1999979426985454,1999980493804130,1999987857115209,2000006820793349,
    2000007997225471,2000011703767716,1999989880736617,1999999249415220,1999989645311152,
    1999985851360981,1999993876694930,1999989693469977,1999974343693788,2000030351016693,
    2000021672919564,1999994054999077,2000006756727983,2000010399144731,1999993917958312,
    2000000829175661,2000005405216711,2000006283825693,1999993724108209,2000010046639237,
    2000019701473631,2000031794929428,1999960970750425,2000035394684921,2000020196350220,
    2000001725633704,1999977422602958,2000035018013622,1999964648329614,2000025386414706,
    2000011443469130,2000000624815896,1999996959228949,1999999893889596,2000006713285173,
    2000012601410742,2000014500795209,1999988718237330,2000004536301767,1999997831138544,
    1999994640134535,1999996325638926,2000001623131394,2000007628647606,1999988874936919,
    1999990546900617,1999998893563806,2000013665329420,1999967376787187,1999947787065685,
    1999931079692804,1999919618426349,1999914389677450,1999915418809418,1999922196924572,
    1999933879174796,1999949461382127,2000032014316032,2000011633547233],
   [1999991542255658,1999976269594031,1999973242888184,1999991159910723,1999964395812894,
    1999897546540299,1999829167650825,1999801503968250,1999876493781126,2000123624435198,
    1999405713016170,2001282681015717,2002077941417040,2002717018887142,2002751282130827,
    2001540443182313,2001715444587996,2007901365119790,2017874144148425,2032324056047350,
    2051632496765646,2075751256195886,2104128047256796,2135696621166281,2168939138007975,
    2202015735537901,2232944220977270,2259804035090984,2280934798837856,2295101385952314,
    2301603938286435,2300320999014915,2291684911097207,2276598704041817,2256311160259731,
    2232270612879419,2205978108932901,2178857450132754,2152154378117894,2126871074216484,
    2103736364919183,2083207421813211,2065495773522531,2050609173192433,2038401054525407,
    2028620551728386,2020957887426868,2015081920704636,2010668467403826,2007419452673520,
    2005073946360477,2003412675369599,2002257776782313,2001469455051870,2000940943466207,
    2000592837219812,2000367531914751,2000224210356610,2000134592689137,1999920496167092,
    1999953789221356,2000026428231378,2000014870913186,2000008232320238],
   [2000004483205145,2000002401600205,2000001265379809,1999999344291580,1999999665857345,
    1999999832564800,1999999917506628,2000000039958976,2000000019028318,2000000008907329,
    2000000004098535,2000000001853618,2000000000823946,1999999999640051,1999999999845466,
    2000000000065195,2000000000027023,2000000000011002,1999999999995605,2000000000001721,
    2000000000000656,1999999999999758,1999999999999916,1999999999999973,2000000000000006,
    2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000]]
private def pv_m2_r512_4_1 : List ℕ := pNatCat
  [
   [1999998630197990,1999965962954045,1999998831330425,2000025542072299,1999999989929780,
    1999986769628970,1999992182386208,1999995715977620,1999999734813106,1999996505930437,
    2000001374817132,1999978970546243,1999973318302953,1999939832625553,1999996567140102,
    1999989733915082,1999981202196971,2000017962270887,2000030724403971,2000013894699200,
    1999981317940805,1999977912555635,1999984905950067,1999975543165006,2000011750957537,
    1999978430827307,2000022494741771,2000017667888928,2000031761571503,2000053775428325,
    2000053045034439,2000038390168373,2000024829122229,2000003535206807,1999980336255613,
    1999984339551203,1999964552482284,1999993299361505,1999982026495329,1999989258623075,
    2000009470998130,2000007807430291,2000015991092835,1999990018609176,1999973323768230,
    1999995685359796,1999975066615971,1999965536126388,2000007269198481,1999999260171614,
    1999986740066755,1999995522121819,2000007110976092,1999999075934622,1999989097996124,
    2000000853054078,2000004781715001,1999992433648363,2000001341849107,2000000384611397,
    2000012864781990,2000003579095977,2000010542561105,1999999431739051],
   [2000007453986503,2000018562724963,2000025620081876,2000009158775967,2000012458950429,
    1999978197392069,1999982761069447,2000004064066360,1999984069460886,1999980047455677,
    1999996389501344,1999964634518664,1999974840573899,1999997590380959,2000018691782368,
    1999973909840974,2000017551773769,1999988378668985,2000030622582265,1999975541464384,
    1999992183653892,1999978192738209,2000005686200362,1999953299882950,2000029597262313,
    2000025446198180,1999971405957189,2000011074921994,2000025864716018,2000003208346068,
    1999988526246047,2000006012646334,1999993463404275,2000008131107735,2000012151142582,
    1999999722276137,2000008290176015,2000003814803859,2000016960232446,2000015538780752,
    2000019288962295,1999992471600488,1999998039375798,2000001435787515,2000013363130200,
    2000009403109639,1999995069782357,1999998925891953,2000014683108822,1999988128705242,
    2000011086860289,2000004579336603,2000024351737562,2000000046524132,1999978975757552,
    2000017059683663,1999996883361168,2000014135917883,1999962192318763,2000073668999446,
    1999836636145225,2000237465608121,1999704884223300,2000357618873004],
   [1999731754832527,2000021088940210,2000137221319339,1999759806239071,1999891960725015,
    2000307618913652,1999397945292864,2000001060817690,2000325631749547,1999640411934879,
    1999933262608240,2000174460343021,1999845109330937,2000073885865349,2000254242968747,
    1999678303311590,1999523640897672,2000369047511786,2000811943468378,1999829730152379,
    1998466182879912,1998412738987099,1999985428050957,2001976278059394,2002950382989979,
    2002340892281211,2000603854854721,1998783089719833,1998060508667026,1999539069504657,
    2004198612482649,2012884770545305,2026252345866845,2044661870036750,2068067401785762,
    2095937434500990,2127237439895945,2160484862822626,2193872037196914,2225438121193335,
    2253268585054042,2275682307787197,2291408229907311,2299661813089544,2300264757721011,
    2293486020525280,2280221496842823,2261478776058291,2238795189470892,2213460949414436,
    2186947051555813,2160554985781979,2135157266030770,2111679616921902,2090630977589385,
    2072152729929156,2056442065496860,2043452368654473,2032845871606510,2024363204641326,
    2017813206046885,2012859518008273,2009106686184706,2006296468834698],
   [2004286127660437,2002915701166429,2001984166701540,2001321823117792,2000835542351391,
    2000489046336385,2000262370589345,2000130207737356,2000062232002006,2000031120302001,
    2000017742688399,2000011446148009,2000007596466839,2000004752807529,2000002670281982,
    2000001309638927,2000000544320559,2000000181194906,2000000041190802,2000000001833531,
    1999999997354639,2000000000145813,2000000002034547,2000000002235169,2000000001650361,
    2000000000988335,2000000000515093,2000000000243102,2000000000107013,2000000000045071,
    2000000000018554,2000000000007559,2000000000003049,2000000000001204,2000000000000455,
    2000000000000162,2000000000000053,2000000000000015,2000000000000003,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000]]
private def pv_m2_r512_4_2 : List ℕ := pNatCat
  [
   [2000014789154222,1999999296717172,1999971393321848,1999974791204542,2000001339699682,
    2000009861216440,2000015921043105,1999991733276274,2000007441107823,1999979092770845,
    2000004628889921,1999996646111938,1999979045279042,2000013420927934,2000018822064672,
    1999987571205246,1999973002246732,1999962592170267,1999999617055743,1999951270664791,
    1999976666006276,1999980092309581,1999996805269459,2000027601899970,2000020940462942,
    2000004440690081,1999996154133310,1999996018479439,1999971837367673,1999994335921949,
    1999981248593696,1999989508640770,1999996684750341,1999988032571063,2000016185506555,
    2000027467288440,2000033132677663,2000055106827813,2000048030933785,2000038002578831,
    2000035665240437,1999992444695294,1999992787656227,2000003989932595,1999974258971434,
    1999962863679949,1999986866237777,1999997889293295,1999996582098028,1999995656128927,
    2000024124361787,2000004857606069,1999990157370338,1999978442412919,1999989550413929,
    1999981292700055,1999982263118344,1999983294765331,2000000166415793,1999988591340202,
    1999998901240510,1999998572765965,1999990232659163,2000003827876736],
   [2000007565679062,1999978974320624,2000009885231428,1999988604355524,2000005773956004,
    1999994724508571,2000039273106772,1999966144666436,2000012815035106,1999997326723390,
    2000023562066383,2000003061932061,2000041218271416,2000006345575722,2000005087969643,
    1999992184181447,1999982229930243,2000032873074182,1999984989333275,1999960985414178,
    1999996758618929,1999993623820263,1999956106638732,1999988454663492,2000012234110251,
    1999972162396721,1999993190835328,2000014504114189,2000021093020535,1999994104690474,
    1999989755458775,1999980794409884,1999993205273606,1999992375109737,1999987572205511,
    1999990592652594,2000005792348867,1999999110656234,2000023090063574,1999998257355009,
    2000006832811978,2000000166081756,1999984890340802,2000030420290695,1999978375375174,
    2000045767852971,1999914730582068,2000120404268202,1999849521178714,2000250208340335,
    1999725178227764,2000287291111468,1999804466578661,2000087401872197,2000034190327444,
    1999909108675354,2000071405658053,2000099507216694,1999729517510731,2000287251725187,
    1999916129887282,1999780322181123,2000393852134446,1999819121556330],
   [1999804093735104,2000371460480656,1999858629249342,1999786604301259,2000319106935007,
    1999979997354420,1999713483113089,2000149971654343,2000145484250811,1999831235760049,
    1999998935483822,2000126586308379,1999900866498437,1999955325336095,2000200037865252,
    1999972671731794,1999618917393241,1999875337967103,2000323140620047,2000087883873373,
    1999467509544977,1999506598626267,2000281371086987,2000717551776193,2000141468104662,
    1999226380115127,1999127800233795,2000068056866229,2001117510499058,2001179748581770,
    2000099853928169,1998651071652594,1997973087218233,1998508647364481,2000094167351786,
    2001781614359972,2002845569030059,2002694842645981,2001334892543292,1999248286250094,
    1997049403219118,1995785901382068,1996429184806217,1999977041543819,2007521060691632,
    2019740341784782,2037095765299562,2059721756249339,2087044344630128,2118068940929228,
    2151446601777206,2185308563855825,2217646686873807,2246624240363356,2270504544331750,
    2287854449802162,2297876572703709,2300335573977764,2295396551797167,2283714806207491,
    2266431855327831,2244895672742783,2220447854054171,2194429358662831],
   [2168153069065999,2142730824412630,2118951111063976,2097329905106483,2078209842129368,
    2061773018938999,2048004485416542,2036710552869588,2027605883797204,2020398286741009,
    2014818119192531,2010605534018240,2007498443204022,2005243146732865,2003618022661990,
    2002450426013394,2001617216224363,2001033024503344,2000635860814699,2000376910846171,
    2000216010417514,2000120777010290,2000066752193903,2000036978830080,2000020718709669,
    2000011731938978,2000006643045473,2000003702453381,2000001999680851,2000001033845609,
    2000000507594025,2000000235880362,2000000104009447,2000000044032102,2000000018382145,
    2000000007914375,2000000003690671,2000000001898509,2000000001046953,2000000000590008,
    2000000000327497,2000000000175650,2000000000090399,2000000000044613,2000000000021160,
    2000000000009675,2000000000004277,2000000000001830,2000000000000759,2000000000000303,
    2000000000000115,2000000000000042,2000000000000013,2000000000000002,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_3 : List ℕ := pNatCat
  [
   [2000006008373873,2000013638585174,2000016891682639,1999988660519891,1999991592944392,
    1999961545082009,1999992026875846,1999997476926583,1999994363107180,2000018488200612,
    2000013964649719,1999981747993486,2000010647185542,1999991853360580,2000015198644522,
    1999973419364343,1999975948180753,2000016705335026,2000012392370750,2000005821369137,
    1999993884334141,1999994079967939,1999974465144876,1999996302089171,1999977764169119,
    1999956127601846,1999970487072310,1999969630317485,1999990226715265,2000012434366516,
    2000008576912296,2000015627744078,2000019186148433,1999990411033463,1999996684740214,
    1999993913783078,1999980221219324,1999992707060330,1999991238204339,1999971116609791,
    1999993881243794,1999998228617836,2000001992965204,1999999108288972,2000042103499510,
    2000055403494806,2000044448172493,2000029042447135,2000044320049490,2000029949764283,
    2000012726248255,1999991000327827,1999993307106669,1999988609049088,1999973919530692,
    1999965147745357,2000006115520545,1999980143185222,2000023768063133,1999995001383150,
    2000019130450160,1999976054593281,2000024002689692,1999964178991116],
   [1999987288787965,1999985093724148,1999992533239066,1999973592473794,1999998606515319,
    2000003527020265,1999968655754251,2000010844575334,2000000949099827,1999998684187445,
    2000001570571187,1999980066795621,1999994280273278,2000013046481032,1999996884828099,
    1999988203894068,2000036424433520,1999991104146033,1999965243746040,2000006530604188,
    2000036924152704,2000005684149633,2000010223321099,2000023133990304,2000013222852968,
    1999991543864968,2000014081664483,2000005370464014,2000007755694065,1999988033183398,
    1999964958168262,2000022612448955,1999943439075388,2000048181081780,1999874756557708,
    2000110508734420,1999817869678946,2000225719023875,1999755895536996,2000249419590914,
    1999801315557544,2000110143824656,1999981859093710,1999929263290016,2000056711017659,
    1999989355801583,1999859330051541,2000196886297477,1999863486141462,1999999244319717,
    2000183877937861,1999729734984637,2000164920674437,2000115784487381,1999696646551605,
    2000235888559427,2000063092929485,1999689165034542,2000235129050908,2000094039159697,
    1999707817172512,2000185978732610,2000170741426597,1999724266127890],
   [2000043573390838,2000238300395418,1999837006218700,1999905192064512,2000218643837038,
    1999982714576270,1999811838711750,2000094506303577,2000132258632382,1999887189282817,
    1999951428020569,2000119420769753,1999981844236819,1999895314277434,2000106833879618,
    2000129239086352,1999851497945557,1999816400658730,2000186526272589,2000239752692275,
    1999855001423573,1999621226148850,2000061548763556,2000445926424062,2000186204126627,
    1999606093263833,1999553761518819,2000193503646198,2000575871195173,2000180629300550,
    1999411051646245,1999172161651084,1999858745441894,2000678663918198,2000768310078674,
    2000025781637904,1999075526528006,1998873741685258,1999672711672821,2000804910861885,
    2001464132209747,2001135474167057,1999910629080657,1998566100074690,1997887752956396,
    1998197689922949,1999440523153470,2001154764412413,2002586252417006,2003157143920651,
    2002626207899615,2000956570781765,1998426808302124,1995730177993349,1993759354404278,
    1993473201120151,1995975889744022,2002406335015870,2013637031278041,2030153789430126,
    2052077357642378,2079050417478261,2110095251096899,2143705274663762],
   [2178085720731362,2211305069090017,2241384831884311,2266494556490203,2285213318672673,
    2296671769335844,2300532734601876,2296936849669244,2286488200305311,2270214594924999,
    2249431635755256,2225551183079717,2199931456234631,2173806940565435,2148256969908364,
    2124165027042523,2102170660269473,2082649842138035,2065744441027314,2051424925565242,
    2039553038801497,2029923211877466,2022284093510127,2016353703042128,2011838374347992,
    2008455570331681,2005954040808664,2004125239775219,2002804596026970,2001865610516666,
    2001211319398326,2000766620019007,2000472897076898,2000284734316646,2000167811037050,
    2000097178308876,2000055525535569,2000031415247397,2000017635780016,2000009822140357,
    2000005414986316,2000002943936931,2000001571463545,2000000820307346,2000000417504303,
    2000000206903472,2000000099906125,2000000047152085,2000000021882754,2000000010075718,
    2000000004654054,2000000002180463,2000000001044053,2000000000511595,2000000000255200,
    2000000000128374,2000000000064454,2000000000032017,2000000000015635,2000000000007474,
    2000000000003489,2000000000001586,2000000000000700,2000000000000296],
   [2000000000000120,2000000000000045,2000000000000014,2000000000000004,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_4 : List ℕ := pNatCat
  [
   [2000003660861696,1999991434942723,2000021565241133,2000004350992588,2000012620079486,
    2000017956369970,1999996137616224,1999968370183244,2000003705531591,1999967951068339,
    1999985731245081,1999991777106859,1999996143154433,2000025251548516,2000000933267683,
    1999990492872667,1999994355447932,2000024958748792,2000005642301070,1999983896307735,
    1999993128486313,1999979808774147,1999990605986992,2000015884225602,2000010064840644,
    1999997909426731,2000004868218435,1999989029335384,1999995727426534,2000004382495801,
    1999982104881283,1999967196733951,1999979025672242,1999955028663585,1999971050938294,
    1999982824677894,1999998169099971,1999997872524349,2000019037956025,2000017024159839,
    2000005764559818,1999989713659348,2000008548223907,2000002296103015,1999985389076805,
    1999974315582786,2000003738958685,1999981367442699,2000001885043029,1999947165244851,
    2000008443070396,1999992998106108,2000031094818609,2000000434293335,2000056965551673,
    2000037298859514,2000041844700619,2000044543222773,2000029315381766,2000022093261235,
    2000012008548489,2000020424883860,1999967253739116,1999978081768534],
   [1999996636949335,1999966341984241,1999988995601891,2000005191417453,2000003037775783,
    1999998251456002,2000018261016748,1999990984359585,2000001631359268,1999994134475761,
    1999970219735472,1999985857052361,2000013825417295,1999970969014196,1999969272820442,
    2000002495021371,2000006526008854,1999977216142732,1999984131939916,2000051423180677,
    1999943809770248,2000048313629473,1999884409747712,2000144702263668,1999840021156504,
    2000203938666274,1999772982175134,2000230272576268,1999786699187830,2000129456923069,
    1999948121220182,1999998481711728,2000079298615391,1999961595357097,1999980612747534,
    2000119353834048,1999882032573230,2000100061129928,2000039429276737,1999827576648171,
    2000206038249179,1999902507774502,1999900336720130,2000218243478860,1999776120671613,
    1999976619433642,2000187263035904,1999736740350152,2000064371839143,2000194864050955,
    1999718526736607,2000067760095839,2000234806382077,1999743440080312,1999986711969801,
    2000233041274277,1999789705960379,1999896613740435,2000251177942684,1999913610628024,
    1999809581399271,2000193493821128,2000066488675939,1999787306088159],
   [2000060405403276,2000179519723961,1999881755922139,1999890693566006,2000154803248486,
    2000016022094387,1999865303241356,2000027040622457,2000152741316391,1999927817784810,
    1999917723568282,2000092335134774,2000065203174967,1999915440030403,1999975526089792,
    2000150633737308,1999990899536560,1999827995631956,2000019082798556,2000210343387020,
    2000050012552039,1999741922794973,1999870618144157,2000280999483533,2000237723869016,
    1999809999721019,1999659957499086,2000031838642237,2000431861630893,2000210627423610,
    1999633923740537,1999557457430063,2000082315108306,2000519673776767,2000325522440744,
    1999679645855235,1999371071662820,1999852697794140,2000569301848677,2000688128546967,
    2000077045774040,1999307008009221,1999105002189358,1999729835977563,2000627267407965,
    2000940415830951,2000390224198055,1999433494136454,1998775788544915,1998921939035907,
    1999865916990545,2001009601775778,2001586600688248,2001244109372135,2000170436625353,
    1998857816842924,1997900018918357,1997794516548557,1998670928282772,2000212681203306,
    2001883246540374,2003156087224982,2003568946681861,2002783839151782],
   [2000751206596555,1997798639845279,1994550725670285,1991838398768831,1990700146209801,
    1992347941551741,1997984779443039,2008570509697494,2024681264397066,2046451783533246,
    2073506809492421,2104888902419631,2139086262553846,2174202810515492,2208191180559999,
    2239051486422467,2264981945357319,2284522895785522,2296701569758463,2301127271017912,
    2297987992716518,2287956127419739,2272056290427221,2251541460132598,2227786095364354,
    2202181721249929,2176029052699366,2150442133742314,2126287887811737,2104171925760628,
    2084461608441077,2067326399869121,2052778557191620,2040707682447333,2030911175546174,
    2023124550910281,2017052498891125,2012397826818351,2008884131377967,2006269578459350,
    2004351918463203,2002967050109229,2001984189304631,2001300171434643,2000834319015930,
    2000524305425639,2000322866159015,2000195048204314,2000115772514049,2000067631771272,
    2000038947294052,2000022137609692,2000012428250474,2000006891611820,2000003772149675,
    2000002035773865,2000001081819133,2000000565320569,2000000290212227,2000000146291802,
    2000000072432008,2000000035265943,2000000016921124,2000000008026250],
   [2000000003778570,2000000001773324,2000000000833163,2000000000393159,2000000000186631,
    2000000000089080,2000000000042653,2000000000020413,2000000000009720,2000000000004585,
    2000000000002135,2000000000000974,2000000000000433,2000000000000186,2000000000000074,
    2000000000000026,2000000000000007,2000000000000001,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_5 : List ℕ := pNatCat
  [
   [2000014084082484,1999987597913512,1999996508715532,2000004069395662,2000018149117663,
    1999981781260043,2000021529461451,2000026216106815,2000000123845173,2000011703472038,
    1999991385125558,1999992702766112,1999988780182211,1999987762280800,1999976831776100,
    1999966041221296,2000002983838798,2000019200752695,1999998412646818,1999990753639969,
    2000005127450176,1999995935885371,2000007182245016,2000019724855033,2000007184816529,
    1999984221018061,1999997772987877,1999975059621439,1999990473758117,2000006761064529,
    2000011973709815,1999994942364323,2000003818045248,2000000165999289,2000002482645059,
    1999994028470862,2000010107384415,1999990472047679,1999993543312926,1999951353968720,
    2000000468755892,1999944403437317,1999980039395001,1999954721155186,2000009966014121,
    1999997372406231,2000010797231562,1999995129012249,2000004837013101,2000032547932783,
    1999995602161259,1999990272401805,1999989037310430,2000009494301575,1999993429079641,
    1999980655809088,2000001720600481,1999966188097707,1999978280349207,1999995511430155,
    1999989722086218,1999979768860190,2000030091693304,2000031117076238],
   [2000022576180144,2000040171717935,2000046767971318,2000030283542494,2000046082541595,
    2000035036798042,2000000403778767,2000035772566869,1999963488407081,2000030402554767,
    1999886109369184,2000128229944448,1999822550827683,2000154190368683,1999802811961521,
    2000244847603762,1999785349323393,2000161509985415,1999896601847836,2000043738565559,
    2000011099564125,1999919524786983,2000041584009245,2000009794497536,1999902306358907,
    2000073496025575,1999925852840616,1999971090300647,2000130821922747,1999836602927214,
    2000080320948503,2000051297877317,1999804383968731,2000172559983444,1999958431489747,
    1999870990825752,2000235239508990,1999868660906983,1999893070260753,2000226430718244,
    1999836915893695,1999946700544089,2000238045321289,1999820699259055,1999944744482701,
    2000263650268989,1999854146516921,1999904224784740,2000270862211242,1999908201012316,
    1999818582401287,2000235985758520,2000034792991113,1999767014477024,2000121280823770,
    2000107823036836,1999784437644434,1999967862242861,2000192956545919,1999864917649118,
    1999858395000525,2000150279988328,2000068902228343,1999833631893171],
   [2000014155795564,2000161336384005,1999905407799345,1999881473516920,2000089697443532,
    2000059733982946,1999886646985400,1999949651367052,2000120364281515,1999991075371855,
    1999879787612624,2000052339767325,2000104753466738,1999954865307120,1999912924047882,
    2000052750454993,2000096098734980,1999911584404656,1999891401140149,2000131255302440,
    2000135387013285,1999874568873789,1999834510277749,2000097710050078,2000249067289634,
    2000005225551752,1999713913038583,1999897643402856,2000298465143262,2000244189273115,
    1999809585680588,1999655092656137,2000000433485525,2000379175544704,2000255474698660,
    1999742297960435,1999548818113215,1999991256232579,2000481001539967,2000366393268408,
    1999800190619159,1999458417636823,1999738927894558,2000359403386492,2000621057890899,
    2000170458378071,1999476220070866,1999313866165391,1999868286670066,2000589700745489,
    2000808462300314,2000311653260851,1999485231462593,1999029989465896,1999374460419673,
    2000252010797188,2000933678901846,2000883864122959,2000142206722960,1999197193191911,
    1998648363908216,1998883162807696,1999832122522059,2000966917333158],
   [2001635821556175,2001477543436287,2000566779348047,1999282818844453,1998127716724639,
    1997582765929469,1997943575127478,1999173267816165,2000909513515246,2002629139314257,
    2003814800276818,2004028696203458,2002962045225955,2000540934273606,1997041114496975,
    1993111878234653,1989700362015596,1987951736692449,1989123408382588,1994469667929171,
    2005055506644493,2021539710616825,2044016895267376,2071968583553061,2104302416799866,
    2139436878740869,2175421202050814,2210107425331660,2241374047837976,2267359791266516,
    2286648680439822,2298371116255504,2302225084729286,2298443423532543,2287727880898959,
    2271155325542341,2250056049632618,2225873013397253,2200023114025756,2173784510887002,
    2148224766871962,2124170019417848,2102204765225165,2082689452903941,2065786937457648,
    2051494021800066,2039677075198838,2030110447508333,2022514749716204,2016591054660044,
    2012047635236963,2008617666579776,2006068384074039,2004203636189873,2002862257101466,
    2001914376756943,2001257097116401,2000810275216661,2000512676539867,2000318529016364,
    2000194447672487,2000116717398913,2000068947427591,2000040115976990],
   [2000023006727192,2000013012773478,2000007261001937,2000003997212983,2000002170574133,
    2000001162249230,2000000613408327,2000000318975573,2000000163385425,2000000082434658,
    2000000040980532,2000000020086899,2000000009718382,2000000004648163,2000000002201885,
    2000000001035292,2000000000484221,2000000000225740,2000000000105058,2000000000048849,
    2000000000022691,2000000000010519,2000000000004857,2000000000002226,2000000000001006,
    2000000000000446,2000000000000192,2000000000000078,2000000000000030,2000000000000008,
    2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_6 : List ℕ := pNatCat
  [
   [2000017295458082,2000001423465567,2000011326186590,1999977276131028,1999992170912786,
    2000024259753667,1999993626428536,1999994748212455,2000001801656999,2000007244746313,
    2000016521374667,2000010216840394,2000017251349025,2000011699231657,1999994557527324,
    1999989892258420,2000014276236588,1999999619555437,1999973731794726,1999964226312193,
    1999993209988023,1999981055548727,2000000929417064,2000008977795628,2000001669633344,
    1999985095048317,2000002672818515,1999996422486449,2000008921705243,2000002051655780,
    2000033929157645,1999986504036402,2000012568208575,1999957907475057,2000013965227032,
    1999977676284907,2000002418307866,1999997765836658,2000011116427330,2000001847486367,
    1999984574989842,2000011990983645,1999999282872593,2000012084696729,1999999348079346,
    1999988410316158,2000003527722476,1999989431753988,1999984843955821,1999943028946376,
    1999963555786839,1999988875590653,1999982456262791,1999965698562443,2000000945032764,
    2000005320197706,1999997857425722,2000019838198739,2000014668444722,1999994792073850,
    1999975788724750,2000055461106137,1999934325455935,2000080856170107],
   [1999877373545403,2000148142849906,1999795214209838,2000196854328943,1999762199228180,
    2000167179766356,1999828117132526,2000119655595334,1999944725969473,1999993414052702,
    2000100190252628,1999975190941925,2000034252308935,2000080090529662,1999988249254535,
    2000102390251509,2000008174016228,1999940580610453,2000151320216121,1999903058563126,
    1999966277882092,2000098495386870,1999828097707673,2000083116873145,2000039539460115,
    1999817831022882,2000179211778399,1999991487105686,1999841901599516,2000195922916919,
    1999922594010980,1999875500019099,2000218137667038,1999883244469433,1999865683943659,
    2000208703954947,1999876883737930,1999853852838204,2000225088437370,1999925747221001,
    1999842741920959,2000204308824544,1999967500006135,1999767520288912,2000188611385248,
    2000076637287347,1999781418458366,2000066537376677,2000182877354364,1999798881589623,
    1999939689955436,2000216900999624,1999928357031981,1999838771258270,2000132167373799,
    2000094709586164,1999834491424778,2000021897476567,2000189228459786,1999911907010957,
    1999886937351076,2000139860596142,2000085656957115,1999879987862902],
   [1999968281825784,2000141719560067,1999985579321207,1999855750767454,2000044965060143,
    2000078822941036,1999894140084620,1999912383523991,2000065448590612,2000049157636865,
    1999920825740606,1999957812100190,2000103457148487,2000027275830292,1999872380390389,
    1999984542956058,2000117012608894,1999985723328658,1999869761106993,1999989543132088,
    2000115000129289,2000016140627292,1999853252303834,1999948324200533,2000186075973871,
    2000116292902104,1999812320109282,1999817248263658,2000144706662084,2000248321113737,
    1999959577977463,1999718527414427,1999893666625238,2000259374384273,2000274477290908,
    1999868999857521,1999634807791157,1999953228046006,2000371873226350,2000284338104704,
    1999815127872337,1999591693094427,1999899576493061,2000364834345028,2000406892926765,
    1999930160235283,1999498174527062,1999671445649686,2000268888309894,2000574399896906,
    2000230297974291,1999629498190767,1999417006161649,1999815223777835,2000441935688978,
    2000673270586788,2000233574040176,1999508575029810,1999204808470586,1999638822313594,
    2000425202067940,2000877129905915,2000626862720212,1999873604773724],
   [1999179784987465,1999067671281276,1999655211619308,2000541801789785,2001079435791424,
    2000862003745223,2000017406301538,1999072922676444,1998579108032535,1998814067707604,
    1999689403655233,2000806016939187,2001622844310532,2001713489652183,2000989758808423,
    1999736180425361,1998442568586757,1997583938771424,1997484016207921,1998262867240243,
    1999806206922274,2001754424370874,2003563567918887,2004646221202862,2004525529735235,
    2002937403788315,1999885158005983,1995689706028553,1991041030283699,1987001206258106,
    1984910860841563,1986207898192382,1992215187340892,2003949485232144,2021968271062288,
    2046252209739506,2076134526990225,2110307736274719,2146931135859594,2183828522650283,
    2218731886728459,2249518305121950,2274404225157051,2292084820164200,2301818625545639,
    2303457224462559,2297416634509211,2284591007027198,2266220695581258,2243738165063476,
    2218618852042284,2192258088864851,2165883855669505,2140504707061214,2116886654853319,
    2095552098152468,2076795577651977,2060712590012188,2047237809373855,2036188269331427,
    2027306464655082,2020298733694858,2014865732474948,2010723773304627],
   [2007617584390533,2005326184258640,2003663948931106,2002478758727257,2001648636179722,
    2001077780268141,2000692508549327,2000437373650867,2000271593751985,2000165877477179,
    2000099690777114,2000058985101500,2000034377190653,2000019744333869,2000011179664754,
    2000006242455052,2000003437954333,2000001867645448,2000001000766917,2000000528916986,
    2000000275692976,2000000141719917,2000000071849324,2000000035931543,2000000017731125,
    2000000008638384,2000000004157980,2000000001979205,2000000000932692,2000000000435669,
    2000000000201978,2000000000093044,2000000000042631,2000000000019437,2000000000008819,
    2000000000003978,2000000000001780,2000000000000787,2000000000000340,2000000000000142,
    2000000000000056,2000000000000020,2000000000000005,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_7 : List ℕ := pNatCat
  [
   [2000017822944478,1999998549347391,2000004859116331,2000028446733367,1999996842371494,
    1999979364941559,1999995541970749,2000001270027970,2000008971961866,2000001856953431,
    1999996268339382,1999992037944432,2000008841768590,1999998909579422,2000004029026769,
    2000004922468233,2000035010651171,2000012264766793,1999993600550119,1999995259139147,
    2000022033028847,1999998269249953,2000012014336917,1999980672095888,2000006122163746,
    1999944810271106,2000001314905557,1999970125726158,2000009015235305,1999992850836666,
    1999996098867907,2000007234914234,1999989752262601,1999995780638510,1999982327161360,
    2000014847312773,2000019969428790,2000001961519753,2000017024006916,1999996335300113,
    2000002761020150,1999981729759758,1999987101061632,1999992350828252,2000001184005513,
    2000003000670675,2000002534388366,1999988372146406,1999986542808090,2000036454247841,
    1999981301363265,2000022459481965,1999930719499414,2000129043470542,1999865291459593,
    2000162504273609,1999800374143440,2000185284534101,1999751468403418,2000166944055793,
    1999840169043668,2000039963703161,1999951508560906,1999957212601205],
   [2000055279588531,1999946607054862,2000028801731566,2000034905655293,1999932705205102,
    2000059513591034,2000024358415225,1999913525631231,2000091665571721,1999958086678304,
    1999974272379470,2000097444298066,1999854051440613,2000045993877837,2000066719199299,
    1999799891210112,2000091807188977,2000022834611891,1999850442745494,2000158862075215,
    1999962614265241,1999889324753599,2000233398132301,1999960014889074,1999906573641997,
    2000245520126956,1999966694957399,1999910792853164,2000232217893523,1999931866207604,
    1999872568787333,2000197151144449,1999950601160673,1999789850862041,2000184839229616,
    2000007076078667,1999802159889092,2000133166725695,2000100554705287,1999787797246349,
    2000044672635271,2000192153904337,1999818883152929,1999937434240183,2000213376470861,
    1999927982083343,1999802042816545,2000113385089733,2000094708622458,1999809636581934,
    1999995363318999,2000184990903875,1999893994443675,1999853921905457,2000126372517462,
    2000056398515059,1999857803269564,1999990761872524,2000142097716290,1999957104998567,
    1999860136862413,2000092435643448,2000105958798698,1999870871816622],
   [1999928777271099,2000114173514520,2000029633382409,1999904857322703,1999999904521016,
    2000106020869165,2000003152435775,1999906157204204,2000038661332966,2000118430908949,
    1999961633424574,1999918827879256,2000078730533369,2000081920359898,1999929890847512,
    1999932927538644,2000057549668399,2000047260610687,1999907212125092,1999889640090841,
    2000053957738622,2000106334954786,1999926986955213,1999863583638257,2000069524252622,
    2000157438554113,1999944584173544,1999814118731241,2000000887067014,2000189434623053,
    2000062658882909,1999799368394993,1999810396515007,2000121047638944,2000269610663779,
    1999990485610030,1999696295730762,1999866194028799,2000258155910525,2000276018941837,
    1999891345140842,1999656325902361,1999893899500253,2000286122935807,2000313275544953,
    1999917092346619,1999601570147731,1999808604395935,2000302747030144,2000436097548908,
    2000015091537400,1999570728204477,1999657991761503,2000167000875458,2000501465516297,
    2000283519208456,1999742307838421,1999456823668157,1999757110284460,2000355928985154,
    2000614637320123,2000228542209801,1999582370048101,1999343561403941],
   [1999757236379462,2000424965397084,2000729447479759,2000396449630213,1999696118241621,
    1999205014300935,1999349539631800,2000052256034098,2000764859338748,2000906986379001,
    2000351316971081,1999518193303513,1999017986836864,1999192678066300,1999919414865332,
    2000737759606758,2001138831007028,2000847606480242,1999983581042880,1999011814991181,
    1998481040127690,1998701023306807,1999578173864662,2000701352859671,2001574411959582,
    2001827290661257,2001326382252714,2000201505480006,1998812398191974,1997645482471957,
    1997150016823866,1997578916381447,1998910993211878,2000871950061578,2003007026449218,
    2004756679689364,2005534729981492,2004837739897134,2002389581698802,1998279254531662,
    1993036369087537,1987618688083010,1983324683207521,1981656286614391,1984144622718995,
    1992142766991692,2006602805537979,2027878790769501,2055607054881402,2088697828799132,
    2125437966750367,2163675786100810,2201049085968462,2235223161507083,2264114841864141,
    2286082664403871,2300063272614480,2305636700533726,2303012941548191,2292947202335029,
    2276605033047920,2255405164643347,2230865790490805,2204472091864716],
   [2177573696361992,2151313947204864,2126589285656859,2104035671833872,2084038244861610,
    2066759464874214,2052179855659007,2040144782213630,2030410975545789,2022687826282885,
    2016670426476313,2012063365550733,2008595891317602,2006029994078381,2004163285320059,
    2002828408999136,2001890370108552,2001242772730746,2000803628872311,2000511160235562,
    2000319855808386,2000196942709243,2000119353429338,2000071216290868,2000041852652766,
    2000024233460087,2000013829205805,2000007780235491,2000004316235459,2000002361644094,
    2000001274613849,2000000678636828,2000000356466618,2000000184734374,2000000094461542,
    2000000047663752,2000000023736730,2000000011669743,2000000005665779,2000000002717762,
    2000000001288724,2000000000604493,2000000000280686,2000000000129118,2000000000058885,
    2000000000026641,2000000000011960,2000000000005327,2000000000002351,2000000000001024,
    2000000000000439,2000000000000183,2000000000000072,2000000000000026,2000000000000007,
    2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_8 : List ℕ := pNatCat
  [
   [2000013365673715,2000016207282760,1999992527946727,1999994586852648,2000021699150276,
    2000018809509946,2000008432980047,1999990848369213,1999993503730638,1999984364041524,
    2000005741574592,2000001880795836,2000010958667474,1999990430290098,1999998176098194,
    1999998771410436,2000018904338854,1999970059066071,2000010890042366,1999990389868745,
    2000050877496765,1999991511312447,2000015895813297,2000004981730445,1999998604560240,
    2000012839980682,1999999375090426,2000020544943948,2000004540303511,1999993532084270,
    1999986170058238,1999966522438479,1999996519807337,1999976725093430,1999985110011254,
    1999994838037588,2000006776598794,2000002685074931,1999989268034911,1999990461787135,
    1999983517718113,2000020741204172,1999962105894418,2000070676835734,1999926637143566,
    2000130573065618,1999851362918629,2000201741530294,1999768796957095,2000184914850485,
    1999817424806453,2000165049896351,1999885365930692,2000012687077441,2000038485033026,
    1999943153569149,2000056779512853,1999970553547115,1999990728769095,2000031764620053,
    1999954484982440,2000037666818078,2000054324959727,1999914693126489],
   [2000060199033513,1999996729248528,1999892247407277,2000095080143471,1999921895457311,
    1999912627041944,2000086503167878,1999862408446406,2000008182591869,2000101329806110,
    1999824731380469,2000072979673358,2000112501960366,1999822226607411,2000090866104917,
    2000077088897803,1999836286355521,2000119261621168,2000055911586571,1999804886753374,
    2000148100446855,2000068920416394,1999786471399515,2000068964145499,2000101963862221,
    1999777805139125,2000053893200182,2000119011456533,1999797268129509,2000017046901686,
    2000187845102342,1999868881495303,1999932134887516,2000245052849249,1999976550513482,
    1999872986660520,2000220884199556,2000075614167126,1999838245270454,2000105492510926,
    2000160782437711,1999838403562450,1999911224203793,2000188367395466,1999960938715491,
    1999799831207496,2000117663800508,2000119699837217,1999832319696600,1999953890094185,
    2000156990844875,1999984802318045,1999865808355815,2000075215940844,2000121783777451,
    1999872438020952,1999893036948226,2000122647414895,2000018419306016,1999855154657362,
    2000019413843319,2000115401014814,1999938463055589,1999880587563699],
   [2000046133758195,2000091218014900,1999933133283888,1999905120054957,2000071129464384,
    2000072144655928,1999911735349933,1999955388408513,2000096707173562,2000012854340127,
    1999892697485165,1999987865966649,2000089292722586,2000006850743034,1999918888940199,
    1999994132807720,2000094352235416,2000026379174976,1999910184688920,1999988170410661,
    2000128994286689,2000041518587150,1999881838090627,1999973963330893,2000149429387824,
    2000066964402135,1999868681296251,1999898673782798,2000088540858049,2000105012389762,
    1999906945232789,1999811999043668,2000004880262879,2000205870695057,2000069170652692,
    1999782097134273,1999823535435282,2000162329654348,2000262737774858,1999950279380185,
    1999695181162091,1999874337937222,2000222395609686,2000246166048018,1999910061937769,
    1999671416644086,1999874115861644,2000271896173438,2000319914056978,1999921388896494,
    1999606769705726,1999818226387125,2000284520572774,2000388601726216,1999995661540690,
    1999603009827967,1999689686242240,2000153292654758,2000459023114740,2000248374831206,
    1999739083299729,1999504673588100,1999839364906941,2000394317162062],
   [2000544887039078,2000104002326134,1999541420997659,1999455623388126,1999932919267439,
    2000491814658225,2000590341315311,2000131050032507,1999525529457840,1999325010336610,
    1999739224718519,2000433137722784,2000797372182078,2000487850814469,1999744889657800,
    1999183500754910,1999259770036537,1999910369620253,2000643535977585,2000932673117262,
    2000575560541864,1999803436621387,1999122454215747,1998994491688252,1999535582190865,
    2000425513306894,2001108640525689,2001153945126469,2000516468249512,1999534048380557,
    1998707507319775,1998440273183294,1998874057395713,1999851567336850,2000983535291323,
    2001796200614254,2001921063987847,2001251014859378,1999983546776492,1998534094842662,
    1997380880003928,1996924204153798,1997398582013244,1998824174692563,2000977735316840,
    2003393847622473,2005425821339855,2006375152005362,2005659960670659,2002974468347516,
    1998405149507856,1992493082094080,1986240603081060,1981052228648965,1978595033883443,
    1980579062885195,1988488985380998,2003323059979396,2025397299530449,2054252008843512,
    2088669296837010,2126788728729127,2166298647581291,2204677762530147],
   [2239458639480098,2268480297292553,2290095373669013,2303303149895962,2307793808476517,
    2303907238953656,2292524987975833,2274921925402583,2252604188045719,2227154582343696,
    2200099522740695,2172805368815241,2146407532423125,2121772509321743,2099490317569113,
    2079892396674738,2063088082607387,2049011792639859,2037473315706788,2028204999476590,
    2020901704783560,2015251586667263,2010957584429417,2007750713389765,2005396833232911,
    2003698661811352,2002494603919988,2001655644883564,2001081233448072,2000694802375417,
    2000439361164951,2000273435454960,2000167508710407,2000101033194412,2000060012599663,
    2000035114551382,2000020244834307,2000011503660874,2000006444020698,2000003559344157,
    2000001938901710,2000001041795181,2000000552213080,2000000288787258,2000000149019114,
    2000000075883211,2000000038136731,2000000018919182,2000000009266324,2000000004481951,
    2000000002141481,2000000001011135,2000000000471998,2000000000217930,2000000000099574,
    2000000000045042,2000000000020176,2000000000008954,2000000000003934,2000000000001708,
    2000000000000731,2000000000000306,2000000000000121,2000000000000045],
   [2000000000000015,2000000000000004,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_9 : List ℕ := pNatCat
  [
   [2000001023846396,2000013599780313,2000021159269630,1999999348311353,1999994334304182,
    1999990286061659,2000016393989283,2000009895437108,2000022797838868,2000004705040091,
    2000009435669780,1999981968610347,2000005362941286,1999965975069152,2000029831483531,
    1999986973031059,2000016838088816,1999981307490870,1999995609029407,2000025594938920,
    1999992752612310,1999994362530640,1999984931038943,1999995955252693,2000017259197954,
    2000001061264057,2000024509067127,2000005324297601,2000009930379891,2000008832178359,
    1999995011605169,2000006094635811,2000006111564769,2000039288826178,1999970761023615,
    2000056953664291,1999903138209140,2000117143345821,1999823233751350,2000166436622903,
    1999763451486732,2000208816123218,1999809565842842,2000133971626118,1999926879324184,
    2000008949614482,2000022724236693,1999919007824375,2000073586315173,1999964509393840,
    1999965457723676,2000058500828214,1999998199876184,2000014998079398,2000029848262077,
    1999934602321815,2000042713220105,2000016948674323,1999910132783528,2000088661445847,
    1999969836515743,1999906634971627,2000124932418437,1999942266422710],
   [1999952766674085,2000123762481505,1999883753965885,1999987613038313,2000128959343939,
    1999867578749770,2000046559821537,2000129988546881,1999831101774388,2000030268796954,
    2000151406617383,1999813650596859,2000008904460950,2000100187051010,1999822093726086,
    1999981005341389,2000128945138057,1999805597586449,1999962889296164,2000196398546312,
    1999855218819757,1999910806283845,2000192606430082,1999953579070312,1999862311447813,
    2000158779601294,2000022377698062,1999811811076617,2000133729989142,2000123064394950,
    1999795977093775,2000007705078021,2000175212362888,1999873732941110,1999866337279704,
    2000147126689631,2000004784913305,1999794723369106,2000065194240214,2000144934260721,
    1999832941092507,1999935093846542,2000211292944927,2000008789807684,1999855940190474,
    2000110790559795,2000177746137185,1999932511144521,1999944350731906,2000173463449076,
    2000070282822046,1999850115292548,2000004163165315,2000137233111219,1999925614035988,
    1999875989658481,2000092350559918,2000075508341098,1999885225851443,1999935197884760,
    2000099204920840,2000042554689639,1999905754619931,1999989349949256],
   [2000117384448036,1999992480002076,1999860095757978,2000000330598312,2000105846792284,
    1999961747522862,1999897776229593,2000034544431414,2000063290580150,1999940621752719,
    1999929116063537,2000039919913256,2000051517978353,1999942799559635,1999923531353357,
    2000047285864884,2000084840611934,1999950539153414,1999906609799408,2000051339645306,
    2000090651252206,1999931961054707,1999891016726168,2000056304848018,2000112060438293,
    1999956734692455,1999880181119196,2000021450098094,2000140459992343,2000035720807560,
    1999873398264081,1999930639909011,2000138871525700,2000151695127186,1999918918317494,
    1999826348405125,2000055639475068,2000229545188495,2000029431880433,1999752219014594,
    1999835177693996,2000152349810396,2000223066127010,1999942460144128,1999716492029117,
    1999875740802004,2000215934108336,2000264854989559,1999931475471569,1999669121095048,
    1999863798517484,2000260933391489,2000295782413229,1999901247986146,1999615653112790,
    1999830107927814,2000261673335151,2000353632662393,1999996101351241,1999634846968902,
    1999712144005944,2000147479575461,2000430341070636,2000207890821373],
   [1999715703294408,1999532751998591,1999899063977097,2000405761488364,2000464307131717,
    1999999037627973,1999528260033030,1999566725791819,2000072015951300,2000521721811129,
    2000463228776770,1999947218893317,1999465284948193,1999488145432378,2000020972417783,
    2000577022015795,2000620372148701,2000081362999640,1999439381541704,1999278359260048,
    1999750212190609,2000455275079775,2000810962014079,2000534387616030,1999837460999025,
    1999238781043986,1999181585447144,1999725804128467,2000502904840479,2000964697081163,
    2000769055734432,2000029653764377,1999238145662253,1998918234400462,1999277608788349,
    2000099864102957,2000909162781101,2001254706727461,2000936832638799,2000086087785679,
    1999093794586420,1998433998075127,1998444711964638,1999164657613699,2000311640067971,
    2001415380241847,2002026020911923,2001885687803879,2000997361546372,1999600022905712,
    1998094861659644,1996951832894993,1996600001195192,1997306920438852,1999076036805069,
    2001602902706084,2004312363174876,2006465602907705,2007306526163161,2006221006554522,
    2002894397035920,1997452509558945,1990557455316550,1983419398588416],
   [1977695572905701,1975278970124400,1978014308993856,1987399435845227,2004329193726947,
    2028922731301163,2060455916575089,2097404961818413,2137595083709124,2178435466457024,
    2217208148714320,2251367507026815,2278804258295106,2298036108339683,2308304104172921,
    2309573487683593,2302454171991952,2288065256868619,2267870126591153,2243505848804239,
    2216625529333404,2188766839314141,2161254824024640,2135142345549734,2111187072225906,
    2089860065517195,2071378212981465,2055751432211748,2042835820536331,2032385454897436,
    2024097797115581,2017650023033229,2012725598288768,2009031825102898,2006309857342583,
    2004338943140485,2002936579529133,2001956014799151,2001282229520501,2000827234316964,
    2000525270958723,2000328299814038,2000201997936883,2000122372301581,2000073006470264,
    2000042901417017,2000024837527817,2000014169901253,2000007967830865,2000004416890352,
    2000002414228110,2000001301366851,2000000691907681,2000000362897786,2000000187786466,
    2000000095883049,2000000048313818,2000000024027641,2000000011795784,2000000005717344,
    2000000002736548,2000000001293770,2000000000604329,2000000000278985],
   [2000000000127328,2000000000057468,2000000000025659,2000000000011331,2000000000004948,
    2000000000002132,2000000000000903,2000000000000375,2000000000000151,2000000000000057,
    2000000000000019,2000000000000004,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_10 : List ℕ := pNatCat
  [
   [1999998981955480,1999993651329960,2000013219934035,2000009534356324,2000025097326481,
    1999998111620180,2000004297878622,1999980094284468,2000015965489040,1999978383933150,
    2000039196343058,1999993112393418,2000023532475249,2000016011501574,1999996116249089,
    2000009709522210,1999975737125157,1999985815448069,2000014528283957,1999999007377542,
    2000008006026723,1999980935420393,1999997561200761,2000014894762486,1999999585999319,
    2000016181429659,1999971711967326,2000028947718713,1999923590428209,2000104146129528,
    1999862502048598,2000182512931468,1999806954557016,2000236480655659,1999805908132042,
    2000166211457779,1999894574284207,2000030879670948,2000051724762417,1999944058231270,
    2000078457476057,1999961247471200,2000016017656773,2000038369590515,1999938832965166,
    2000007521351319,2000012420750472,1999917142559319,2000014776234413,2000018722830818,
    1999944668073669,2000052990832931,1999962670494704,1999951367214539,2000109058892299,
    1999916812577454,1999935900116147,2000115895024564,1999910282969073,1999987165858749,
    2000144924576983,1999893710772536,2000003264729905,2000115634033653],
   [1999877570677037,2000009045942737,2000138329746014,1999831391693462,2000004935670113,
    2000135826707109,1999853978717901,1999975769769431,2000179528836403,1999882327539897,
    1999907257167980,2000173677488627,1999914409012170,1999907311962498,2000181844061935,
    1999960234075005,1999854200732315,2000161145636158,2000071493379377,1999801509487507,
    2000057126341508,2000148747350826,1999816121877317,1999939224035135,2000149938392082,
    1999875323047783,1999857802726876,2000144325599295,2000007940764863,1999799631881651,
    2000053866758254,2000168251726541,1999864866989105,1999898757431702,2000184199558211,
    2000001896653345,1999822867553106,2000096584932939,2000139724347144,1999862645647819,
    1999931648141536,2000164293035126,2000015590689110,1999819413917547,2000009082348302,
    2000144681990389,1999908009342987,1999841823234424,2000095695013899,2000078071023564,
    1999852976933753,1999957348243590,2000144327030210,2000011948576823,1999896371315435,
    2000055938450687,2000146199268276,2000000667217256,1999944914536952,2000099699647062,
    2000130253674370,1999945735582392,1999915566610978,2000085357797162],
   [2000068203957743,1999898016950147,1999946819751414,2000096141514463,2000019152911477,
    1999886440556072,1999967058227825,2000088540338156,2000033568104621,1999938824701045,
    1999983874285039,2000064449355188,2000008760033131,1999912618890787,1999971860685910,
    2000081410950289,2000012118024526,1999889358203721,1999967182824080,2000098572520890,
    2000018279408901,1999882859859632,1999955387510816,2000089679638944,2000032836154363,
    1999900816999927,1999939742100574,2000085056812124,2000087001408421,1999932544540369,
    1999875947684889,2000028028513549,2000142426787822,2000003839613643,1999829347200996,
    1999934392795053,2000164268386521,2000124725494307,1999869308525332,1999828298798454,
    2000081051407299,2000222446567288,2000025955338524,1999795257061054,1999886776730106,
    2000179326162144,2000250715415991,1999977956920889,1999729666231117,1999866482603599,
    2000208550011296,2000254348146941,1999907485144144,1999652546301430,1999865234006247,
    2000256123527434,2000280641523265,1999909439318365,1999652683539669,1999852697952930,
    2000245804612104,2000326944937828,1999987140541444,1999639202496829],
   [1999716575957931,2000143872503301,2000405763799545,2000163951677464,1999693646511640,
    1999571486679082,1999965756159410,2000416169095824,2000388456986200,1999911073850766,
    1999526943538282,1999661780101465,2000166337557343,2000504232439697,2000321093283526,
    1999795914453058,1999457429838150,1999662302453543,2000232045179756,2000608405829284,
    2000400980090293,1999790395818585,1999364298142927,1999540468871874,2000162279731139,
    2000659888114990,2000586644961632,2000005057443225,1999404121921082,1999277879097333,
    1999737153408214,2000435432786941,2000834699712265,2000610948528587,1999907412211916,
    1999239618927282,1999110217066009,1999627820220501,2000429521244753,2000957095756827,
    2000855113920878,2000193094134897,1999387870711890,1998926948350186,1999088192704558,
    1999800536199924,2000690014682364,2001274809091520,2001216423998591,2000502177119181,
    1999457420011528,1998577786558989,1998280339956965,1998714716821536,1999720597066612,
    2000919411204641,2001866586034064,2002195994906964,2001725990557217,2000518852800291,
    1998883003370855,1997305592152909,1996322434065711,1996362077520853],
   [1997614017897286,1999956369735781,2002951126507721,2005898934812863,2007946859744176,
    2008247818551260,2006162053592089,2001468026465394,1994528711304927,1986357874826550,
    1978554244535440,1973107831151296,1972114604442300,1977452445151121,1990473087557233,
    2011758059528612,2040976463464689,2076869195510709,2117366050333621,2159819611991467,
    2201317709436238,2239021551817885,2270474546559912,2293837468998777,2308024604567405,
    2312736161644411,2308399148895429,2296039368301114,2277111317390988,2253312265219644,
    2226403373350082,2198055727382405,2169733229465052,2142617996769624,2117577844317191,
    2095170355972001,2075674629661673,2059140351681192,2045444290987936,2034346109921836,
    2025537883411043,2018684261132282,2013452340606318,2009531827004104,2006646925924821,
    2004561764892378,2003081131922465,2002048109575091,2001339886766273,2000862721949642,
    2000546749415516,2000341082262786,2000209475510942,2000126669183537,2000075429487586,
    2000044240420754,2000025561420108,2000014551914129,2000008164064029,2000004514645527,
    2000002461208691,2000001322979400,2000000701302348,2000000366664031],
   [2000000189104364,2000000096219215,2000000048306412,2000000023932431,2000000011702189,
    2000000005648189,2000000002691430,2000000001266388,2000000000588499,2000000000270155,
    2000000000122533,2000000000054920,2000000000024328,2000000000010650,2000000000004604,
    2000000000001961,2000000000000821,2000000000000336,2000000000000132,2000000000000047,
    2000000000000014,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_11 : List ℕ := pNatCat
  [
   [2000006012403051,1999987684134384,2000006186380003,1999985910685239,2000019687918239,
    1999990209115376,2000044917919459,1999988479761405,2000018270253200,2000005078828541,
    1999979075734331,2000006856929246,1999994715860863,1999994932365245,2000022923706632,
    1999997089879219,2000015092488542,2000023059972441,2000006367779466,2000026749003996,
    1999952713438473,2000038353536470,1999911953983951,2000136035882939,1999831112141438,
    2000200655798362,1999771807108919,2000204403694024,1999830185447050,2000114828256136,
    1999984665507835,1999954076073176,2000078182175596,1999914216285808,2000037072295105,
    2000001480848740,1999953061530735,2000041529120808,1999994955855742,1999997055628046,
    2000061848445189,1999971548924472,1999973891025310,2000072596401936,1999960929531499,
    1999983202326469,2000082422031019,1999947643269340,2000016880486269,2000075633024778,
    1999912755769745,2000045535627847,2000079378431431,1999838276485975,2000023205255596,
    2000083374734440,1999865573966076,2000008396689644,2000098508824217,1999849363115072,
    2000038957587366,2000112564708332,1999855224130738,2000000804515516],
   [2000114259428566,1999856125378986,1999957132120677,2000187518622749,1999907026156099,
    1999906372668975,2000190147231442,1999962003574532,1999863160883264,2000147468412031,
    2000044219897355,1999835964603047,2000061836563623,2000103292318971,1999826384989115,
    1999992535854014,2000199905396579,1999887027308557,1999858592396346,2000172652969927,
    2000024136388719,1999821601501015,2000063784066531,2000129146283342,1999873158239699,
    1999948189569739,2000180772505622,1999981033368141,1999830149856926,2000120680833027,
    2000136189330643,1999818551202581,1999921240813828,2000161615508120,1999960266903291,
    1999811093000435,2000041978996831,2000098021123479,1999864861807855,1999894579357114,
    2000139580446041,2000051008999126,1999827634894125,1999988038559279,2000172046339726,
    1999960994444486,1999846083071093,2000081635098157,2000129504039535,1999910942088572,
    1999921283661117,2000107132305257,2000056048837800,1999889620975125,1999951783696420,
    2000093843796907,2000006076039884,1999865416884531,1999971058729703,2000099955389578,
    1999972757342345,1999871063074294,2000027694134959,2000113286007647],
   [1999961887355359,1999917556964460,2000077986972603,2000120433629720,1999994953060714,
    1999976820353203,2000090137622902,2000099139789136,1999975207183934,1999936189813076,
    2000041752967068,2000081473530802,1999968911948006,1999919096633243,2000025165750116,
    2000056926612161,1999936319340345,1999919071752126,2000064820579252,2000094018251740,
    1999949641366544,1999911116391558,2000043081476402,2000087726074937,1999963716558738,
    1999896341278457,1999999098738341,2000089004208680,2000008086922014,1999890206388112,
    1999945496779374,2000094728089826,2000071614580070,1999889117536889,1999862874799011,
    2000064475822159,2000155639615600,1999967560868391,1999818493323242,1999971854293452,
    2000176261368859,2000090001705836,1999848727732015,1999835790705911,2000072903410942,
    2000197556316164,2000015568090076,1999790736333339,1999866945791037,2000158213820014,
    2000240875443342,1999966700882312,1999721539186296,1999884619018023,2000244784698595,
    2000281603816130,1999933450672575,1999698543790263,1999910861814590,2000266396170144,
    2000266718196517,1999906725062061,1999660418603928,1999844039328517],
   [2000217734783684,2000300191227043,1999975442746824,1999647776692417,1999747017254534,
    2000175319602205,2000400722506427,2000122107826686,1999670803120571,1999608607920124,
    2000020335174342,2000406314460119,2000300874033843,1999828659381581,1999537789076784,
    1999758719925058,2000247907582111,2000473749685537,2000188933369706,1999686286622638,
    1999496173748623,1999836711768609,2000372157829791,2000543442841134,2000151403504198,
    1999581727164793,1999416668293240,1999835179976223,2000431990392228,2000629723011466,
    2000241151436540,1999627484842288,1999344081909029,1999643569520381,2000273800035742,
    2000703539773304,2000562287467552,1999943329670827,1999337458437071,1999243942666578,
    1999762277460616,2000500298364580,2000883110893455,2000609129692303,1999878392615846,
    1999223871251024,1999107987505879,1999605903566261,2000383039304385,2000936367966291,
    2000912201580979,2000310325812007,1999477620042521,1998907226950273,1998953874248368,
    1999624173823076,2000566959166668,2001271789257790,2001352947637219,2000748111245729,
    1999729905050922,1998753160724550,1998243860317152,1998433229303625],
   [1999285215675732,2000516411316207,2001688904421401,2002351683357962,2002194385058513,
    2001163606421711,1999497682677112,1997667388379504,1996248193381844,1995768495784928,
    1996570673966223,1998704169963259,2001862343445961,2005380875836460,2008320199569154,
    2009641620266123,2008455862491370,2004289800503437,1997301506434437,1988383602603184,
    1979123502148293,1971622528641823,1968203315828510,1971053065702113,1981860624039631,
    2001508724282019,2029877152673944,2065795535074023,2107156942971508,2151171673726697,
    2194713447841053,2234695619616948,2268415758977790,2293820626380890,2309664193085794,
    2315552616056943,2311887485144969,2299730292521461,2280616944497597,2256352155930798,
    2228810794917124,2199767657233863,2170769752288551,2143057131683358,2117530827889722,
    2094760676470347,2075022330728903,2058351742622381,2044606370181508,2033524662342351,
    2024778187451626,2018013469799545,2012882777283078,2009064605301329,2006275455060807,
    2004274839999587,2002865435183046,2001890059630123,2001226863366911,2000783754382853,
    2000492789331556,2000304987693723,2000185820177734,2000111467903745],
   [2000065843980962,2000038305327957,2000021950780237,2000012392558643,2000006893902960,
    2000003779501576,2000002042392400,2000001088044380,2000000571506614,2000000296022353,
    2000000151221982,2000000076198931,2000000037877497,2000000018576627,2000000008990031,
    2000000004293600,2000000002023990,2000000000941857,2000000000432730,2000000000196323,
    2000000000087963,2000000000038925,2000000000017011,2000000000007340,2000000000003122,
    2000000000001306,2000000000000534,2000000000000210,2000000000000079,2000000000000026,
    2000000000000007,2000000000000001,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_12 : List ℕ := pNatCat
  [
   [2000015397813254,1999983636283278,2000019654210567,1999970204660298,2000021977422961,
    1999984695418451,1999987434325504,2000022843455651,2000002815858339,2000004059642992,
    2000031237880813,2000001544352571,2000001973754976,2000021237916441,1999961571318948,
    2000045168764079,1999914358812036,2000124958626695,1999833433270818,2000212580386148,
    1999773589712822,2000224439592087,1999867716106246,2000100640054841,2000011022413014,
    1999918909794403,2000089108506798,1999921523477591,2000017751078362,2000040220963390,
    1999948929855878,2000025674267016,1999999297863663,1999955304391326,2000034116872151,
    2000013049047176,1999963530133125,2000047424106470,2000000625365695,1999939322814839,
    2000067612411004,1999993046036367,1999910701598608,2000063304772208,2000006723536226,
    1999927450159915,2000107504861583,1999987973582522,1999925713591346,2000110440114798,
    2000008474585291,1999863536463051,2000126177925169,2000053248478861,1999853977961281,
    2000085997075692,2000079738931661,1999889527390193,2000061099479917,2000110673039208,
    1999852705153350,1999981958473755,2000150508897291,1999867986670827],
   [1999910931058413,2000160510313530,1999933655093403,1999848630842311,2000136218688204,
    2000065666887709,1999832188938108,2000027755979236,2000128677829508,1999850063182706,
    1999924696109002,2000176535163858,1999953536030398,1999855401618194,2000147096230024,
    2000076162849117,1999823544568298,2000019843119599,2000191309587868,1999931998820537,
    1999850927223062,2000117029230866,2000074283124911,1999832508363297,2000002021696413,
    2000169104160587,1999910090122632,1999860286297463,2000145302541433,2000076093881708,
    1999818035521129,1999967891617765,2000173350939361,1999985388745519,1999842063902123,
    2000057191231386,2000146285187124,1999917848581098,1999900621338323,2000140082599683,
    2000076165601332,1999835946073418,1999958255735160,2000153659197383,1999972587492047,
    1999813411414235,2000001457803639,2000108153660060,1999927845317869,1999865729654747,
    2000044204620834,2000092155925816,1999929185507232,1999905822664987,2000072313307343,
    2000075561784821,1999908035925735,1999936976301742,2000110431645622,2000058125915019,
    1999896778790411,1999972791144399,2000114280007314,2000020485466046],
   [1999893104877252,1999980257543889,2000081241542243,1999992840495080,1999893827758027,
    1999964834231023,2000060595177213,2000003313867595,1999909798265067,1999969001001532,
    2000076664877360,2000025484883364,1999923645508871,1999997443215950,2000127042939130,
    2000073196291820,1999960525316306,2000018455604588,2000113901834696,2000036659558355,
    1999930181072782,1999996931158353,2000100990758259,2000037130299996,1999908615253169,
    1999928506197466,2000051888243559,2000066110986634,1999949871618694,1999910594680751,
    2000034135677292,2000115034391928,1999996697204995,1999873467102786,1999973250187260,
    2000130288792893,2000053050132979,1999857825689518,1999887232122261,2000103207507197,
    2000139655064745,1999929664047333,1999816884207858,1999982444991135,2000159596723420,
    2000068244616248,1999848035703110,1999840425519438,2000072700848536,2000203833338441,
    2000021948254036,1999783164248655,1999857984242564,2000159198252614,2000233158280396,
    1999942845193311,1999708876453437,1999891989007169,2000238614135757,2000246292031411,
    1999901520372778,1999693147139609,1999910485025031,2000252188976759],
   [2000258230666017,1999927156366442,1999703338371680,1999890620061860,2000256272191172,
    2000321752864518,1999980604499507,1999658351518651,1999777617573017,2000195401602836,
    2000366218383393,2000050168548609,1999638187796054,1999654817567492,2000087740810306,
    2000408308800041,2000231681315130,1999773419762433,1999572748722165,1999860168101357,
    2000309031422636,2000413023321579,2000044975378824,1999597951811169,1999566204990761,
    2000006227515194,2000455991826040,2000421734482956,1999921059764593,1999480897884160,
    1999576106792801,2000118987931798,2000553164930455,2000436073531544,1999882849167606,
    1999432980346446,1999516139108728,2000056620518005,2000562006399464,2000574053049813,
    2000070042571126,1999482057582231,1999328343603843,1999765407650134,2000440347778520,
    2000780762219807,2000482957348573,1999775685341074,1999229661025017,1999284354798822,
    1999899813670011,2000607444290643,2000883850923050,2000532462750654,1999800719373909,
    1999188784813375,1999110823434364,1999631287063447,2000427384230336,2000991584006744,
    2000950480247730,2000303380835478,1999427578730676,1998845979856365],
   [1998910025166938,1999600307104452,2000555107848058,2001282841914487,2001415562099076,
    2000870669362605,1999867756883887,1998823679787593,1998183390427001,1998247438329656,
    1999051577499815,2000341781394564,2001658361352817,2002498853350573,2002495063367190,
    2001538752710706,1999821574762252,1997792709163863,1996057277207318,1995237149636156,
    1995810138986228,1997949918040166,2001405590200329,2005469437745838,2009068342732550,
    2010979086468963,2010126238439408,2005892860632649,1998368654466247,1988474943519233,
    1977932079248618,1969064738178069,1964470373823840,1966603482597896,1977349060725253,
    1997666262950061,2027372796396604,2065112438165382,2108509390933230,2154475134571806,
    2199606361426866,2240602122130129,2274634135654123,2299621600489409,2314384447143763,
    2318671261028711,2313076472820908,2298874128774906,2277802168342788,2251831960667779,
    2222953722075298,2193000671249789,2163525088805491,2135729687671541,2110449498734641,
    2088173900606523,2069095818716371,2053175168832030,2040205568512007,2029876282993450,
    2021824502280974,2015675796325723,2011072672315621,2007692499662220],
   [2005256761691745,2003533795553386,2002337060810911,2001520676176135,2000973590032932,
    2000613375078987,2000380302535963,2000232077359955,2000139408433992,2000082443188997,
    2000048005446715,2000027527052810,2000015546327710,2000008648907215,2000004740525010,
    2000002560289776,2000001362741622,2000000714927412,2000000369738353,2000000188525023,
    2000000094785338,2000000046996430,2000000022982265,2000000011086054,2000000005275568,
    2000000002476976,2000000001147591,2000000000524711,2000000000236792,2000000000105481,
    2000000000046380,2000000000020129,2000000000008619,2000000000003636,2000000000001509,
    2000000000000612,2000000000000240,2000000000000090,2000000000000030,2000000000000007,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_13 : List ℕ := pNatCat
  [
   [2000030077348004,1999973932650652,2000024723078511,1999997637358688,1999980522430407,
    2000011870944846,2000008835452102,1999977778905399,1999990677057950,2000030430082026,
    1999940381372553,2000092333032973,1999879548482795,2000192604280233,1999789244816068,
    2000246680121004,1999812664792068,2000125404705666,1999980623137770,1999928189773744,
    2000098998744679,1999910466628237,2000033506946766,2000035079375378,1999929262132838,
    2000036531570809,2000021095615125,1999978277381953,2000052290629539,2000027967311241,
    1999966520541598,2000025008049503,2000010740222224,1999940274124309,2000038491397814,
    2000031228633203,1999934039294363,2000030033256833,2000047145156803,1999890222636558,
    2000035134772927,2000068665004468,1999918493360623,2000002460945767,2000095265988207,
    1999911192247112,1999991084217831,2000130710705414,1999891388751227,1999924934605785,
    2000138007806177,1999962947978961,1999873775841798,2000114973119984,2000067341885709,
    1999865087212018,2000060509050764,2000107072001246,1999859163710412,2000008943381270,
    2000164281205495,1999901443158476,1999896458177607,2000157870484274],
   [2000037484172742,1999854682284994,2000081060490808,2000149071590758,1999860582533746,
    1999930015200547,2000176295772708,1999964170709152,1999831127262694,2000095481718554,
    2000069787599044,1999826424689412,1999979156570326,2000166902619235,1999951207822801,
    1999847927852184,2000101510180757,2000103832536355,1999823504083967,1999918745075973,
    2000180207405699,2000002643010214,1999824615880081,2000063283913631,2000134767286824,
    1999887897450847,1999930480619169,2000166111608011,2000047302451409,1999834278885208,
    1999989966521877,2000164688696379,1999972352496370,1999829984354645,2000052296788676,
    2000153468917355,1999912585460165,1999869588605916,2000111444976311,2000084360140629,
    1999856174353303,1999943888212799,2000146131077632,2000020489825297,1999849878110733,
    1999995033891009,2000147885463688,2000010445636760,1999879662614180,2000014332291119,
    2000130258167814,1999989990676922,1999881211095001,2000019583781861,2000096003005272,
    1999932010715201,1999867192268893,2000030644069585,2000066483730778,1999905412082569,
    1999899641495832,2000062739191613,2000062596762085,1999918343253682],
   [1999926748962678,2000059890347111,2000058940629028,1999941401827129,1999938749955765,
    2000056731753898,2000075265744805,1999960650189840,1999934058532388,2000050842846753,
    2000079591560376,1999953500404648,1999916394353863,2000036086195189,2000060888231642,
    1999931337368452,1999902900018723,2000028529781941,2000059806915262,1999945124420250,
    1999913577681182,2000020292431203,2000063074986426,1999979094443783,1999947249120730,
    2000051496480116,2000130340517925,2000051513094112,1999941934881871,1999989164210303,
    2000118649954007,2000098496394375,1999944903957483,1999920100140676,2000067038238928,
    2000107818871599,1999941955689017,1999852528092035,2000007504509658,2000145173057692,
    2000027069426904,1999856412104075,1999927405057398,2000126945717612,2000128420954974,
    1999924079193763,1999831059862292,1999994401973858,2000165082827359,2000075068045561,
    1999848976523295,1999834693445357,2000073396612920,2000204076517598,2000002805460083,
    1999758542390840,1999856511536864,2000169244581013,2000224181713441,1999926613072956,
    1999718658189262,1999916755804784,2000238265748135,2000219843858344],
   [1999885256180060,1999699895649345,1999917394102541,2000242309845667,2000237355863405,
    1999905772425324,1999688364518173,1999884492085689,2000245791629208,2000287824393628,
    1999937888575322,1999656647180031,1999834999693418,2000257755558414,2000373459101299,
    2000024722884555,1999659402337923,1999745045909566,2000169574416339,2000396130720115,
    2000139213383343,1999702974293485,1999601473081991,1999953100685293,2000352911667956,
    2000339678275573,1999919148999262,1999564812401922,1999691320571246,2000177422307868,
    2000482017301404,2000247153145557,1999714592493764,1999469711806892,1999790660068646,
    2000337582909876,2000525859654467,2000155799195767,1999612306032443,1999450875159393,
    1999834330156449,2000387963360062,2000577297309174,2000215916803101,1999633449041371,
    1999370681208231,1999685482037294,2000310132705285,2000681710235884,2000448926730532,
    1999799499613677,1999302469279831,1999402854414660,2000027957802833,2000655260596167,
    2000764408125706,2000265556697403,1999552675921414,1999174727928982,1999415837726721,
    2000100966320295,2000738594915620,2000872202473158,2000394258939885],
   [1999619744399318,1999075086116003,1999142280427329,1999797437705654,2000623413004969,
    2001086751202921,2000884880916511,2000129721140114,1999262162012674,1998778258253883,
    1998951791413167,1999705535683725,2000671247932356,2001378280972146,2001470885091063,
    2000864795196065,1999786737956056,1998683366968602,1998035749533212,1998157466697132,
    1999063545688011,2000462390339867,2001863147303212,2002744160445378,2002718722002323,
    2001655422371580,1999735724223666,1997442162094436,1995470579690402,1994566328918034,
    1995307227077774,1997886391980106,2001965555303450,2006659497961373,2010676819624988,
    2012596831118893,2011224313530846,2005943068339983,1996986780465540,1985559021824766,
    1973760812958270,1964321690236203,1960173375733901,1963944045180843,1977473967602303,
    2001451512068037,2035241740215883,2076936194942320,2123605242447834,2171696168646055,
    2217499123825776,2257600633959559,2289257392933400,2310645534670736,2320966467632368,
    2320414672190715,2310032173238417,2291486713894406,2266815283287892,2238172114675280,
    2207612157790955,2176929671093857,2147559537535201,2120538414188652],
   [2096515353240107,2075797616998074,2058416755933655,2044201782184320,2032849404679509,
    2023984835246577,2017209924410092,2012137944933627,2008416082184378,2005737670137899,
    2003846585358025,2002536162726861,2001644695918582,2001049167657548,2000658415130410,
    2000406534234399,2000246993903189,2000147679210682,2000086906356285,2000050343139722,
    2000028710791954,2000016122304978,2000008915545567,2000004855896592,2000002605271963,
    2000001377080288,2000000717211169,2000000368106723,2000000186206518,2000000092846186,
    2000000045638696,2000000022118349,2000000010569921,2000000004981251,2000000002315261,
    2000000001061459,2000000000480053,2000000000214192,2000000000094289,2000000000040951,
    2000000000017540,2000000000007409,2000000000003081,2000000000001257,2000000000000501,
    2000000000000192,2000000000000068,2000000000000021,2000000000000005,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_4_14 : List ℕ := pNatCat
  [
   [2000043848179291,1999993774945004,1999987164264105,2000016751207628,2000011218194281,
    2000004752620834,1999936757971582,2000114658836703,1999847352547415,2000199057348815,
    1999757535469973,2000221606752842,1999847026077616,2000026555508647,2000072396302829,
    1999881496291422,2000096672059410,1999992862760522,1999956048683294,2000081761644861,
    1999983747360804,1999984109998920,2000060009213768,1999984985811315,1999962506995420,
    2000032190618115,2000005078531216,1999960443234676,2000035517868504,2000006689236068,
    1999942589395060,2000017553550234,2000056029405810,1999933657961459,2000042694422264,
    2000087190702414,1999944155060077,1999977834442768,2000094770280405,1999954243178912,
    1999914969892721,2000114391833833,2000004881890747,1999891788642660,2000081468325033,
    2000040597145059,1999867475526651,2000022011138443,2000130077791017,1999900565172751,
    1999906158167672,2000156603360528,2000014428305192,1999855321682380,2000088995503803,
    2000089612140502,1999859802414045,1999985265797861,2000127837884729,1999919753282581,
    1999879407417093,2000137795174748,2000084818502070,1999833426253042],
   [1999996135406316,2000182543554052,1999934376065094,1999870172543772,2000144723037927,
    2000074566676899,1999831816230253,1999993778384351,2000167142021408,1999965144246148,
    1999882853006150,2000114128137923,2000113443104894,1999863176617338,1999941833730452,
    2000179943638405,2000010494520608,1999802043197899,2000026314526290,2000152576868218,
    1999889870064333,1999850613316086,2000120767682294,2000099946122536,1999866692318428,
    1999940210421482,2000126887128421,1999998828057282,1999837506163005,2000010927532827,
    2000158173811955,1999949127168591,1999823488260450,2000063511073334,2000162940636904,
    1999920270701169,1999875854851685,2000118955700634,2000114202933006,1999884703824887,
    1999922607433199,2000119338225478,2000048583112458,1999872032975834,1999959545850949,
    2000127710489613,2000035603245366,1999866883799942,1999956753014656,2000124861944062,
    2000033505841568,1999869720692518,1999965877525105,2000115348900571,2000009736035233,
    1999884127273738,2000006719749864,2000116828718167,1999993270118969,1999906749509677,
    2000032272222277,2000105525972810,1999984354020860,1999910406369335],
   [2000009738916204,2000071428465816,1999969336066874,1999887455602679,1999970491766226,
    2000059233816144,1999985946924989,1999894223362150,1999971652385829,2000077042273190,
    2000005253641240,1999899589856067,1999974614001132,2000084840573537,2000016424421883,
    1999914691279653,1999985396451837,2000088323039820,2000028100372102,1999930870174445,
    1999981251867725,2000075751075964,2000036877246208,1999935460046164,1999945082857335,
    2000036102799083,2000038270396998,1999939086042209,1999912631453674,2000019037652198,
    2000075509109840,1999962790062369,1999865367132236,1999972475730231,2000123331877903,
    2000067938610732,1999919044865014,1999960827496360,2000133018375703,2000132113674014,
    1999956868905108,1999914355126381,2000080451381769,2000168932740121,2000019076653126,
    1999860445228069,1999935847517118,2000117034698865,2000110198630189,1999913770128619,
    1999829685356994,2000004614191563,2000184740691449,2000084598635322,1999843212700415,
    1999839283380458,2000096807408424,2000215933391100,1999991440120283,1999758183712177,
    1999884050585302,2000188570265820,2000208688532039,1999905030444465],
   [1999722256415485,1999927064153447,2000223887633885,2000189117711605,1999869524256955,
    1999709407572577,1999936803486249,2000251420494318,2000225239448499,1999882452226419,
    1999682957615272,1999908224110235,2000263307076872,2000259982386556,1999888624749238,
    1999650439429031,1999878630893731,2000275276111039,2000308669596777,1999928939485749,
    1999632106564001,1999804394446326,2000228783414683,2000375612750421,2000068865740044,
    1999689922947267,1999703181975025,2000100093854422,2000411321964101,2000257147777726,
    1999797486221698,1999560017057692,1999830268553260,2000304238209106,2000426014678869,
    2000037076888263,1999575345615274,1999575991542846,2000052117220398,2000476709001206,
    2000378317594564,1999861460479682,1999480101490296,1999635826995334,2000164799296060,
    2000524145929217,2000348361849752,1999806874926417,1999431454706295,1999599329504395,
    2000166474183327,2000595778641056,2000464665727965,1999876346456945,1999376662365565,
    1999443488460492,2000032021789203,2000611424533625,2000655015636281,2000117651257912,
    1999465682425929,1999257697814052,1999669769340005,2000366717071935],
   [2000791656491100,2000608694763339,1999951746128799,1999313382985049,1999175923625442,
    1999656757950061,2000419274935969,2000912637358587,2000769591659139,2000073872126593,
    1999301996721726,1998985810896193,1999345697881423,2000152446129972,2000894434815242,
    2001111419361120,2000667331053714,1999809255193531,1999010620444283,1998711007379295,
    1999092687044526,1999993331861992,2000984861848578,2001577305953928,2001452552070483,
    2000617660901695,1999405492878361,1998327334248787,1997854341099050,1998229283360549,
    1999379126953998,2000942464554105,2002383071304418,2003148554785683,2002838799208833,
    2001351807157054,1998968706088209,1996338044609486,1994337857870480,1993833247421836,
    1995390539045131,1999034371879997,2004129224690420,2009435270849307,2013343162134182,
    2014246881306392,2010977295865997,2003197359125064,1991658266875086,1978238345156085,
    1965732052449362,1957415938780700,1956475250021698,1965411449182155,1985555899096303,
    2016787873887364,2057505839921931,2104844975188458,2155085987738983,2204170218470381,
    2248227029560295,2284029375113459,2309316732123979,2322954574066606],
   [2324929932574431,2316208117916514,2298492835612660,2273939190277017,2244866854893258,
    2213511137388384,2181835963249505,2151418278457339,2123400854882663,2098501679817774,
    2077063575037511,2059126975530503,2044510860341592,2032890435590158,2023864221639809,
    2017006899728470,2011907185444447,2008191974221380,2005539111188602,2003681548977707,
    2002405582451704,2001545485218475,2000976377409523,2000606640190586,2000370729926542,
    2000222869339144,2000131814623535,2000076710199287,2000043931470264,2000024762203901,
    2000013738908141,2000007504524224,2000004036087514,2000002137579560,2000001114975083,
    2000000572855091,2000000289944719,2000000144586873,2000000071045490,2000000034402277,
    2000000016418304,2000000007723351,2000000003581495,2000000001637368,2000000000738062,
    2000000000328046,2000000000143779,2000000000062141,2000000000026482,2000000000011121,
    2000000000004599,2000000000001869,2000000000000743,2000000000000284,2000000000000103,
    2000000000000033,2000000000000007,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def phb_m2_r512_4 : List ℤ := uOfNatHb pb_m2_r512_4
private def pvi_m2_r512_4 : List ℤ := bDec bZ pv_m2_r512_4_0
private def pvo_m2_r512_4 : List ℤ := bDec bZ pv_m2_r512_4_14
private def pb_m2_r512_5 : List ℕ := pNatCat
  [
   [76467165062972,107974939587528,132038468690574,152230130769492,169935960156846,
    185867929484389,200449642451453,213957525865294,226583880346607,238468931960042,
    249718700504738,260415677184431,270625561635961,280401702775679,289788133513525,
    298821708220306,307533647477006,315950679507651,324095900054089,331989431244051,
    339648934099085,347090012587835,354326536042884,361370899254612,368234234374943,
    374926585123880,381457051192676,387833908854344,394064712409269,400156380065543,
    406115267080394,411947228401561,417657672596430,423251608507588,428733685800609,
    434108230355143,439379275280049,444550588197205,449625695329258,454607902838038,
    459500315788341,464305855052833,469027272425319,473667164169552,478227983197430,
    482712050042637,487121562772520,491458605961352,495725158831616,499923102655871,
    504054227499844,508120238377169,512122760877464,516063346321927,519943476494150,
    523764567988264,527527976211669,531234999075387,534886880401398,538484813073111,
    542029941952306,545523366583428,548966143703905,552359289577304],
   [555703782164386,559000563145673,562250539807776,565454586804579,568613547803294,
    571728237024493,574799440684365,577827918346704,580814404191459,583759608206071,
    586664217305289,589528896384655,592354289312415,595141019864211,597889692604550,
    600600893718725,603275191798554,605913138585044,608515269670851,611082105165151,
    613614150323391,616111896144139,618575819935135,621006385850465,623404045400642,
    625769237937258,628102391113737,630403921323625,632674234117738,634913724601422,
    637122777813051,639301769084863,641451064387116,643571020656517,645661986109775,
    647724300543120,649758295618532,651764295137406,653742615302322,655693564967541,
    657617445878829,659514552903148,661385174248743,663229591676112,665048080700313,
    666840910785046,668608345528907,670350642844216,672068055128757,673760829430780,
    675429207607599,677073426478060,678693717969199,680290309257329,681863422903840,
    683413276985927,684940085222500,686444057095471,687925397966641,689384309190371,
    690820988222221,692235628723736,693628420663551,694999550414953],
   [696349200850074,697677551430834,698984778296791,700271054350007,701536549337067,
    702781429928355,704005859794710,705209999681554,706394007480610,707558038299282,
    708702244527812,709826775904284,710931779577570,712017400168283,713083779827831,
    714131058295626,715159372954533,716168858884607,717159648915199,718131873675484,
    719085661643460,720021139193490,720938430642422,721837658294358,722718942484093,
    723582401619299,724428152221481,725256308965745,726066984719442,726860290579689,
    727636335909843,728395228374943,729137073976152,729861977084244,730570040472166,
    731261365346695,731936051379226,732594196735732,733235898105890,733861250731442,
    734470348433776,735063283640777,735640147412966,736201029468936,736746018210130,
    737275200744954,737788662912273,738286489304287,738768763288813,739235567031002,
    739686981514481,740123086561972,740543960855370,740949681955317,741340326320283,
    741715969325157,742076685279380,742422547444615,742753628051981,743069998318855,
    743371728465257,743658887729829,743931544385421,744189765754286],
   [744433618222911,744663167256480,744878477412977,745079612356951,745266634872949,
    745439606878606,745598589437436,745743642771298,745874826272563,745992198515992,
    746095817270315,746185739509541,746262021423983,746324718431027,746373885185630,
    746409575590569,746431842806442,746440739261422,746436316660780,746418625996166,
    746387717554677,746343640927693,746286445019499,746216178055700,746132887591421,
    746036620519310,745927423077343,745805340856427,745670418807825,745522701250381,
    745362231877576,745189053764392,745003209374011,744804740564332,744593688594333,
    744370094130249,744133997251605,743885437457077,743624453670201,743351084244928,
    743065366971027,742767339079338,742457037246880,742134497601812,741799755728257,
    741452846670984,741093804939945,740722664514695,740339458848656,739944220873264,
    739536983001987,739117777134199,738686634658948,738243586458585,737788662912273,
    737321893899377,736843308802726,736352936511767,735850805425588,735336943455833,
    734811378029495,734274136091603,733725244107781,733164728066707],
   [732592613482454,732008925396717,731413688380939,730806926538310,730188663505678,
    729558922455333,728917726096689,728265096677863,727601055987139,726925625354327,
    726238825652017,725540677296723,724831200249924,724110414018993,723378337658026,
    722634989768559,721880388500178,721114551551031,720337496168218,719549239148087,
    718749796836417,717939185128490,717117419469060,716284514852211,715440485821101,
    714585346467605,713719110431837,712841790901569,711953400611528,711053951842592,
    710143456420860,709221925716611,708289370643150,707345801655529,706391228749157,
    705425661458283,704449108854362,703461579544295,702463081668545,701453622899128,
    700433210437476,699401851012167,698359550876526,697306315806094,696242151095957,
    695167061557937,694081051517652,692984124811417,691876284783018,690757534280322,
    689627875651751,688487310742592,687335840891156,686173466924777,685000189155653,
    683816007376511,682620920856113,681414928334588,680198028018584,678970217576239,
    677731494131977,676481854261106,675221293984230,673949808761458],
   [672667393486420,671374042480066,670069749484265,668754507655177,667428309556411,
    666091147151949,664743011798843,663383894239665,662013784594721,660632672353999,
    659240546368873,657837394843530,656423205326127,654997964699668,653561659172591,
    652114274269056,650655794818931,649186204947461,647705488064612,646213626854086,
    644710603261985,643196398485133,641670992959020,640134366345383,638586497519388,
    637027364556425,635456944718478,633875214440082,632282149313833,630677724075448,
    629061912588359,627434687827824,625796021864532,624145885847702,622484249987645,
    620811083537773,619126354776037,617430030985783,615722078435989,614002462360873,
    612271146938847,610528095270796,608773269357654,607006630077247,605228137160392,
    603437749166207,601635423456614,599821116170003,597994782194014,596156375137431,
    594305847301114,592443149647975,590568231771925,588681041865778,586781526688046,
    584869631528610,582945300173194,581008474866615,579059096274741,577097103445120,
    575122433766220,573135022925209,571134804864239,569121711735146],
   [567095673852511,565056619645014,563004475604996,560939166236159,558860613999320,
    556768739256130,554663460210668,552544692848817,550412350875317,548266345648384,
    546106586111795,543932978724304,541745427386281,539543833363418,537328095207391,
    535098108673299,532853766633747,530594958989395,528321572575798,526033491066354,
    523730594871157,521412761031557,519079863110181,516731771076213,514368351185648,
    511989465856277,509594973537107,507184728571922,504758581056656,502316376690241,
    499857956618566,497383157271155,494891810190146,492383741851132,489858773475393,
    487316720832998,484757394036249,482180597322880,479586128828380,476973780346788,
    474343337079229,471694577369418,469027272425319,466341186026053,463636074213096,
    460911684964742,458167757852697,455404023679617,452620204096277,449816011196959,
    446991147091542,444145303452628,441278161035930,438389389171946,435478645226825,
    432545574030106,429589807266820,426610962831227,423608644139170,420582439395805,
    417531920815106,414456643787221,411356145989382,408229946435617],
   [405077544460068,401898418628163,398692025569297,395457798724032,392195146998028,
    388903453314134,385582073053042,382230332371907,378847526389040,375432917221455,
    371985731860454,368505159868616,364990350879564,361440411879469,357854404246613,
    354231340522186,350570180881954,346869829274246,343129129184955,339346858984599,
    335521726805988,331652364893373,327737323354942,323775063239930,319763948849004,
    315702239171643,311588078326383,307419484858375,303194339722950,298910372752659,
    294565147367347,290156043240425,285680236577500,281134677593003,276516064682759,
    271820814680545,267045028448111,262184450872044,257234424115298,252189832679823,
    247045038456928,241793803441933,236429197124500,230943484670834,225327990794522,
    219572932528958,213667211755061,207598154978815,201351182984626,194909385794906,
    188252967496372,181358508666400,174197967353649,166737295588545,158934473514973,
    150736630251929,142075672444377,132861350096975,122969643093645,112221911831643,
    100343848555688,86873476629501,70909611245601,50124649570333]]
private def pv_m2_r512_5_0 : List ℕ := pNatCat
  [
   [2000043848179291,1999993774945004,2000012835735895,2000016751207628,2000011218194281,
    2000004752620834,2000063242028418,2000114658836703,1999847352547415,2000199057348815,
    2000242464530027,2000221606752842,1999847026077616,2000026555508647,2000072396302829,
    1999881496291422,1999903327940590,1999992862760522,1999956048683294,2000081761644861,
    1999983747360804,1999984109998920,2000060009213768,2000015014188685,1999962506995420,
    1999967809381885,2000005078531216,1999960443234676,1999964482131496,1999993310763932,
    1999942589395060,2000017553550234,1999943970594190,2000066342038541,2000042694422264,
    2000087190702414,1999944155060077,1999977834442768,2000094770280405,2000045756821088,
    1999914969892721,1999885608166167,2000004881890747,1999891788642660,2000081468325033,
    2000040597145059,1999867475526651,2000022011138443,1999869922208983,2000099434827249,
    2000093841832328,2000156603360528,2000014428305192,1999855321682380,2000088995503803,
    2000089612140502,2000140197585955,1999985265797861,2000127837884729,2000080246717419,
    2000120592582907,2000137795174748,2000084818502070,2000166573746958],
   [2000003864593684,2000182543554052,2000065623934906,1999870172543772,2000144723037927,
    2000074566676899,1999831816230253,1999993778384351,1999832857978592,1999965144246148,
    1999882853006150,1999885871862077,1999886556895106,1999863176617338,1999941833730452,
    1999820056361595,1999989505479392,1999802043197899,2000026314526290,1999847423131782,
    1999889870064333,1999850613316086,1999879232317706,1999900053877464,1999866692318428,
    1999940210421482,1999873112871579,2000001171942718,1999837506163005,2000010927532827,
    1999841826188045,1999949127168591,1999823488260450,1999936488926666,1999837059363096,
    1999920270701169,1999875854851685,2000118955700634,2000114202933006,2000115296175113,
    2000077392566801,2000119338225478,1999951416887542,1999872032975834,1999959545850949,
    1999872289510387,1999964396754634,1999866883799942,1999956753014656,1999875138055938,
    1999966494158432,1999869720692518,1999965877525105,2000115348900571,1999990263964767,
    1999884127273738,1999993280250136,1999883171281833,1999993270118969,1999906749509677,
    1999967727777723,2000105525972810,2000015645979140,2000089593630665],
   [2000009738916204,2000071428465816,1999969336066874,1999887455602679,1999970491766226,
    2000059233816144,2000014053075011,1999894223362150,1999971652385829,2000077042273190,
    1999994746358760,1999899589856067,2000025385998868,2000084840573537,1999983575578117,
    1999914691279653,2000014603548163,2000088323039820,1999971899627898,1999930870174445,
    1999981251867725,2000075751075964,1999963122753792,1999935460046164,1999945082857335,
    1999963897200917,2000038270396998,2000060913957791,1999912631453674,2000019037652198,
    2000075509109840,1999962790062369,2000134632867764,1999972475730231,1999876668122097,
    1999932061389268,1999919044865014,1999960827496360,1999866981624297,1999867886325986,
    2000043131094892,1999914355126381,2000080451381769,1999831067259879,2000019076653126,
    1999860445228069,1999935847517118,2000117034698865,2000110198630189,1999913770128619,
    2000170314643006,1999995385808437,2000184740691449,2000084598635322,2000156787299585,
    2000160716619542,1999903192591576,2000215933391100,1999991440120283,1999758183712177,
    1999884050585302,1999811429734180,1999791311467961,1999905030444465],
   [1999722256415485,1999927064153447,2000223887633885,2000189117711605,1999869524256955,
    2000290592427423,2000063196513751,2000251420494318,1999774760551501,1999882452226419,
    1999682957615272,1999908224110235,2000263307076872,2000259982386556,2000111375250762,
    1999650439429031,1999878630893731,1999724723888961,2000308669596777,2000071060514251,
    1999632106564001,1999804394446326,2000228783414683,2000375612750421,2000068865740044,
    1999689922947267,1999703181975025,2000100093854422,2000411321964101,2000257147777726,
    1999797486221698,1999560017057692,1999830268553260,2000304238209106,2000426014678869,
    2000037076888263,1999575345615274,1999575991542846,1999947882779602,2000476709001206,
    2000378317594564,1999861460479682,1999480101490296,1999635826995334,2000164799296060,
    2000524145929217,2000348361849752,2000193125073583,2000568545293705,2000400670495605,
    1999833525816673,2000595778641056,2000464665727965,1999876346456945,1999376662365565,
    1999443488460492,2000032021789203,2000611424533625,2000655015636281,2000117651257912,
    1999465682425929,1999257697814052,1999669769340005,1999633282928065],
   [1999208343508900,1999391305236661,2000048253871201,1999313382985049,1999175923625442,
    1999656757950061,2000419274935969,2000912637358587,2000769591659139,1999926127873407,
    2000698003278274,2001014189103807,2000654302118577,1999847553870028,1999105565184758,
    2001111419361120,2000667331053714,1999809255193531,2000989379555717,2001288992620705,
    2000907312955474,2000006668138008,2000984861848578,2001577305953928,2001452552070483,
    2000617660901695,2000594507121639,2001672665751213,2002145658900950,2001770716639451,
    2000620873046002,2000942464554105,2002383071304418,2003148554785683,2002838799208833,
    2001351807157054,2001031293911791,2003661955390514,2005662142129520,2006166752578164,
    2004609460954869,2000965628120003,2004129224690420,2009435270849307,2013343162134182,
    2014246881306392,2010977295865997,2003197359125064,2008341733124914,2021761654843915,
    2034267947550638,2042584061219300,2043524749978302,2034588550817845,2014444100903697,
    2016787873887364,2057505839921931,2104844975188458,2155085987738983,2204170218470381,
    2248227029560295,2284029375113459,2309316732123979,2322954574066606],
   [2324929932574431,2316208117916514,2298492835612660,2273939190277017,2244866854893258,
    2213511137388384,2181835963249505,2151418278457339,2123400854882663,2098501679817774,
    2077063575037511,2059126975530503,2044510860341592,2032890435590158,2023864221639809,
    2017006899728470,2011907185444447,2008191974221380,2005539111188602,2003681548977707,
    2002405582451704,2001545485218475,2000976377409523,2000606640190586,2000370729926542,
    2000222869339144,2000131814623535,2000076710199287,2000043931470264,2000024762203901,
    1999986261091859,1999992495475776,1999995963912486,1999997862420440,1999998885024917,
    2000000572855091,2000000289944719,2000000144586873,2000000071045490,2000000034402277,
    2000000016418304,2000000007723351,2000000003581495,1999999998362632,1999999999261938,
    1999999999671954,1999999999856221,2000000000062141,2000000000026482,2000000000011121,
    1999999999995401,2000000000001869,2000000000000743,2000000000000284,2000000000000103,
    2000000000000033,2000000000000007,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_1 : List ℕ := pNatCat
  [
   [2000041322125167,2000015466628436,2000004039069437,2000010300720741,1999977592378989,
    2000124003412221,1999841169936776,2000073424718651,2000067172904574,2000126237438223,
    1999883351126540,1999882255668881,2000205195989850,2000283873618723,2000049594731864,
    2000097210035165,2000060832387818,2000025547986181,2000036343881667,1999934181741043,
    1999894650112551,1999951306598976,2000012034468337,1999989922852708,1999945551676698,
    2000065899403699,1999987820426635,2000061642086411,1999970562732696,2000020225914651,
    1999978082341565,1999988608928223,1999987828326356,1999941062538555,2000014071477565,
    1999976904962335,1999971570729431,1999857869279373,2000052476403995,2000150125009222,
    1999891903230526,2000096453833853,1999942967911578,2000047773377220,2000086049644584,
    2000021638753477,2000033702772878,1999845721182086,1999996642037149,1999911032629323,
    2000016755897769,2000021146710080,2000049857922623,1999916501925870,1999783942645849,
    2000041573166138,2000060920697458,2000154033799540,2000017134266536,1999939704943384,
    2000092831258012,1999988705620082,1999983047053866,2000237273973097],
   [1999897102323938,2000067131888016,2000169872684579,2000071115295833,2000073394332460,
    2000053198639962,2000240980500363,2000054848774781,2000178043845639,1999955315600575,
    2000145974332469,2000064101054882,2000062874215392,2000047867732908,1999943380032914,
    1999984533400027,1999911130214553,1999989667510169,1999816192450085,1999983629568787,
    1999826194716327,1999974486142719,1999808285659148,1999915205653522,1999863754833298,
    1999969588847058,1999869028970929,1999954417400876,1999865560802031,1999913388590579,
    1999856735711975,1999873610203654,1999892260749089,1999886671307996,1999892267459000,
    1999864744126491,2000042427697862,1999844906044986,1999919709348155,1999922977362555,
    1999987873115329,1999858041880680,1999859092057972,1999864096780791,1999834502376967,
    1999888225415533,1999993299737410,1999971334739340,2000219590427183,2000103355343999,
    2000020116757311,2000118183562997,1999962255595780,1999977831447426,1999858595952201,
    1999958526002789,1999991826734120,1999903644455454,1999858474408453,1999856158440154,
    1999947567663913,1999972526065902,1999962013908537,1999982614994732],
   [2000031091183209,1999983271007105,1999903977653402,1999898675226720,1999986631317830,
    1999957541222713,1999871288674115,2000009990116841,2000143358918412,2000110683274043,
    1999935557829694,2000005089959332,2000061182498938,2000007363638734,1999904252441011,
    1999966037789096,2000063786625667,2000009113383546,1999878879844565,1999982518016413,
    2000081814588443,1999937772638415,2000041380522192,1999935321731428,1999972590142578,
    2000128043771233,1999956180255478,1999929443926411,2000041740952387,1999961571384621,
    2000110954386965,1999895082768751,2000076211611589,1999846567254850,1999999958308062,
    2000015241310878,2000013697481308,1999940931528540,1999969691950564,1999916822201266,
    2000224136699481,1999930469485022,2000032785683228,2000087095145242,1999903830880147,
    2000043752402542,1999882474964650,1999985118934656,1999834471236512,1999809732122643,
    2000096964196695,1999975180690021,1999872174095568,2000077890671144,1999806921390223,
    1999897045973840,1999993195316708,2000096274770842,1999812752780361,2000202132305851,
    1999821533728078,2000209842879655,2000102206785556,2000027621800507],
   [2000045487901147,2000193579044453,2000328714612974,1999894019149727,2000095957904073,
    1999970774867996,2000151678092143,1999711574035230,1999799869063686,1999793177630915,
    1999716869281611,2000016790650153,1999944686393428,1999838401211279,2000051578217382,
    2000177989948120,2000249803227009,2000319798810389,2000056728745320,1999615068381499,
    1999607006627468,2000069319017007,2000363550496780,2000149104676828,1999782608940913,
    1999800487237671,2000067052942439,2000246410957671,1999932425882666,1999656687749844,
    1999650916495215,2000039246295031,2000401094665598,2000238453945660,1999791865530399,
    1999618317092335,1999880332630249,2000316948566399,2000413916361184,2000147414416606,
    1999450841421864,1999817469319668,1999920002152457,2000397590733522,2000606380654912,
    1999653028200175,1999290984942170,1999979900355885,2000334800563912,2000117235854715,
    2000094975962297,2000024341269378,1999818895211143,1999517845005561,1999837670151751,
    2000217000388650,2000546562843649,2000045174055679,2000160306223864,2000150686173445,
    2000425954317129,2000980279204368,2000820731365350,1999341395303530],
   [1999379780239949,1999912531634951,1999990852716078,2000563593443478,1999871618186524,
    2000564104849602,2000259609549713,1999414803530428,1999655427769832,1999003588697455,
    2000213304373448,2000175774689698,1998820682344118,1998439592018761,1999944428048979,
    2000280707163485,1999236652319152,1999708060899944,2000711792086330,2001038588871578,
    2000367878108922,2000431774599314,2000910497679156,2000373286267421,1999719952671346,
    1999711009806028,2000419771814230,2001278242382593,2000524849829903,1999738379641933,
    2000922416070913,2000684514263877,2002051582653349,2000538451195782,1999877983654150,
    2000845683352402,2002385872594462,2001194861478311,2002187090488404,1999841036778669,
    1999345963056283,2004011375682952,2003215935630650,2001723543862350,2000509761516576,
    1999879120751688,2002484518786028,2003892093676698,2010030899697177,2003189218806021,
    1994968968393654,2002399350475339,2008912092833685,2008967255803062,2013105177932868,
    2014701565683504,2004105596821451,1993758959312936,2001630471498761,2025081491790499,
    2044734299277377,2046259288645790,2031619260731766,2013626423369027],
   [2005262276682802,2013507872756313,2038947528036519,2078068758316527,2125596878980890,
    2175964967122533,2224073282852599,2265690659783665,2297697311327902,2318216342809199,
    2326622874340225,2323425683638119,2310042032310214,2288506799961490,2261163686626395,
    2230382959714550,2198333494060673,2166833657517059,2137261071127427,2110561352686013,
    2087237542046196,2067495241188243,2051205282713462,2038135573072036,2027879348564278,
    2020008510643539,2014117441633011,2009786073332282,2006657714562257,2004458871645475,
    2002942800341459,2001903497760001,2001204588367296,2000753251240514,2000470379365160,
    2000291259749808,2000173820897095,2000096001803561,2000046691823960,2000018489393919,
    2000004761700253,1999999599065946,1999998551495275,1999998928231187,1999999485317660,
    1999999846763344,2000000007568384,2000000051976500,2000000048224631,2000000032181082,
    2000000017806853,2000000008438924,2000000003415199,2000000001147304,2000000000296199,
    2000000000043557,1999999999993386,1999999999993106,1999999999998128,2000000000000531,
    2000000000000986,2000000000000759,2000000000000451,2000000000000233],
   [2000000000000106,2000000000000042,2000000000000014,2000000000000003,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_2 : List ℕ := pNatCat
  [
   [2000024913453692,2000041778634902,1999965546800514,2000126921072931,1999860246587404,
    2000066540163116,2000037981358046,2000042267477318,1999957944273218,1999896833885690,
    2000025424621173,2000247357095344,2000017573412030,1999830328322583,1999951121125012,
    2000056742074483,2000133462779483,2000169967720240,2000113388368585,2000100435603081,
    2000037429216095,2000168366450873,2000009170227597,1999985425806340,1999928348907085,
    1999958964329127,1999980107757444,1999933983855166,1999997623576290,1999952220851813,
    2000030697608650,2000009569256217,2000016338332939,2000056168394820,1999890997823470,
    2000165226667184,1999937530846603,1999889052471294,2000067078653958,1999982835141664,
    2000051747468032,1999864876256377,1999977045116478,1999930730464098,2000004787824036,
    2000061547427261,1999998173304454,2000017798094168,1999909941600823,2000101565446027,
    2000048914509202,2000014315227862,2000104374071301,2000003219460591,1999903511742093,
    1999955690536459,1999807838839965,2000193273878437,2000087813053004,1999829461792322,
    1999998591963036,1999851197258644,1999972288505276,1999957514877566],
   [2000216309435842,1999936165231557,2000008182656342,2000030264911555,2000042352867871,
    2000074304614769,1999932302535066,2000081873775108,2000037094629926,2000149806472191,
    1999950483831342,2000135320288450,2000005508651345,2000190862919467,2000100695588466,
    2000149109505140,2000040078242773,2000123267866461,2000069084732599,2000145194609944,
    2000052293013405,2000051152629928,2000053055644193,2000004253842569,1999994976355262,
    1999902390109457,1999989032752288,1999875583831220,1999994470944164,1999840425859803,
    1999901257462817,1999900373823835,1999873638609311,1999865050072377,1999951267397985,
    1999939975408473,1999885808877415,1999852686223476,2000005525828857,1999847070698813,
    1999839264232674,1999925857876963,1999802275538864,1999991477258112,1999873564658521,
    1999863634978772,1999939332043640,1999939950038383,1999940839530570,1999905234482895,
    1999962559427151,1999934543552695,1999828634360101,1999783974572827,1999849640589983,
    1999908928809004,1999948312532918,1999991242804071,2000093970637077,2000167613864902,
    2000095897846306,2000019455969624,1999947685344833,2000032587971128],
   [2000006255120344,1999944066454487,1999895059551198,1999960976970177,1999913205454115,
    1999810515328759,1999874007743774,2000024857550535,2000003782506705,1999895329346029,
    1999982636190907,2000018796364951,2000071826546434,1999824355217431,1999820325997585,
    2000045541674844,1999942197958282,1999914622597830,2000113050615480,1999957918482288,
    2000191329595697,1999923611478709,2000024471812716,1999953074532484,2000089749147822,
    1999988534699118,1999923619388392,1999940279769729,2000099052905856,1999896214254426,
    2000063961388783,1999915522173417,1999961150109607,2000106394843961,1999891335217217,
    2000127998772813,1999930605317618,1999907232738123,2000067070275132,2000047707332325,
    2000039108805970,1999940598678652,1999895072747489,2000156411170356,1999846002132526,
    2000055580814933,1999969198722896,1999989151646495,1999761652978089,2000269503849551,
    1999861778447200,2000029365492951,2000097855561358,1999936726887538,2000131493081109,
    1999980596044590,2000070994336410,1999765945620872,2000022374795812,1999771293240263,
    2000019505861471,2000038969819309,1999930738677816,1999875784597347],
   [1999852504017714,2000122313146644,1999919253669166,1999746825686799,2000059611767273,
    2000073880907063,1999946985831117,2000010978896448,1999985966799022,2000031784206962,
    2000195446920370,2000146167905200,2000012194158133,2000131583933708,2000204772989673,
    2000162111431240,2000030559540113,2000002034226918,1999799038056893,1999755963339852,
    1999908688425705,1999979847719348,1999798191638979,1999557803977158,1999749279973139,
    2000325865778116,2000497238510151,2000289993310754,1999729225763678,1999823195408936,
    1999858757452476,2000325854498564,2000058404125719,1999691543402463,1999951028988836,
    2000005760903202,2000325171141605,2000300867095199,1999599618612765,1999466107867993,
    2000021301053639,2000087892564966,2000301344399175,2000143867541509,1999690915831086,
    1999323408575372,2000268144012412,2000611330232444,2000295847475605,1999551152849578,
    1999600271374038,2000069010515489,2000317059775325,2000041076907727,2000221694375213,
    2000086976464688,1999263264712110,2000180430338017,1999866306607857,2000152248172615,
    2000628012125193,1999717215401944,1999865843898856,1999173531992355],
   [2000233750176038,2000627610312986,1999782976945932,1999584376062813,1999921984668416,
    2000411169361014,2000875628511704,2000932649895545,1999945609848618,2000168228345415,
    2000414485406231,1999343755356967,1999166158834838,2000538656048959,2001274991577862,
    2000052982658001,1999167373503525,2000058151421118,2000621454101859,1999445548837554,
    1999836460536591,1999042651093402,2000236210567674,1999038696763327,1998905742363137,
    1999436018985209,2000129759785269,1999107777084788,2000206309516147,2000196624411971,
    2000604931038012,2002318859514072,1999114356832857,1999621388651707,2001342069290704,
    1999407361690416,2001569422891012,1999386381732555,2000054649031637,2000036790818349,
    2001627771397375,2002804478511868,1997904877219280,1999625175094209,2003444852796143,
    2000165272464904,2001263514877693,2003801470705447,1998032264163783,1996969035894023,
    2005600606957078,2007009751575948,1999000654635593,1996664356148811,2001340373432231,
    2003284016582132,2003143867854418,2005973622198010,2006836034263993,2000052497019918,
    1993144562610099,1997974883978702,2012610078037800,2021818157821008],
   [2015101840241335,1998560453404362,1988106583273097,1994106230787990,2013408163084279,
    2033668897581256,2043291657929425,2038410720029172,2023492983404179,2007568076441373,
    1999565047727352,2005374650978825,2026817789576174,2062301516356344,2107834312091855,
    2158308250014929,2208429076277355,2253418034794679,2289560884867729,2314405385275129,
    2326858749521666,2327128376345504,2316435254958001,2296736431066369,2270424119126834,
    2239964756315890,2207653909780676,2175475497161489,2144972732596329,2117200308478763,
    2092783213227798,2071987572662567,2054775847135632,2040890416589939,2029955242818920,
    2021546754206600,2015228500609476,2010578507229118,2007219521705006,2004838413622052,
    2003186054274250,2002065645281667,2001321833258493,2000835147077286,2000518778641896,
    2000313844138758,2000182433908733,2000100317800302,2000051303120014,2000023917627245,
    2000009878662839,2000003427038041,2000000864637182,2000000053988926,1999999904714741,
    1999999939158487,1999999988485950,2000000014177600,2000000019962147,2000000016418130,
    2000000010747413,2000000006068760,2000000003054949,2000000001393003],
   [2000000000580217,2000000000221890,2000000000078351,2000000000025876,2000000000008279,
    2000000000002768,2000000000001073,2000000000000499,2000000000000255,2000000000000130,
    2000000000000061,2000000000000025,2000000000000008,2000000000000001,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_3 : List ℕ := pNatCat
  [
   [1999978429115363,2000118920255132,1999879490598328,2000102986255156,2000045026523480,
    1999985867781904,1999968165099107,1999998663315298,1999989115045791,2000124551369549,
    2000074521791171,1999836845947105,1999873445804427,2000100640941458,2000137117864934,
    2000117956319682,1999920224758078,1999967870265741,1999889492001386,2000000335611970,
    2000120368996999,2000114508367667,2000123758602973,2000045603475097,2000138680819071,
    2000128962469254,2000081466471363,2000101556043789,1999913022901601,2000081719183806,
    1999903142269048,1999939929933884,2000079015921860,1999819596098619,2000009852910107,
    2000000442471549,2000040445059918,1999947710244816,1999970832607955,2000110599948694,
    1999999692974060,2000032800968730,1999918130545658,2000002928256792,2000023865767888,
    1999985814237248,2000043057475347,2000007757870807,1999797678859841,2000041474233404,
    1999951544657831,1999979087264824,2000119241067329,1999827742200683,2000110928730701,
    1999976401545051,1999982374807449,1999933820193407,2000230974122917,2000119319792008,
    1999905559120383,2000003482045913,1999863243850517,2000001023255378],
   [1999960185011107,2000168249988847,1999945784025710,1999982385785434,1999782004791439,
    2000002283018628,1999985579338635,2000020844356837,1999947263585980,2000056656778915,
    2000021624231977,2000062893097734,2000004869438649,1999975657923601,2000046597072083,
    2000017208893735,2000113742127341,1999993800966730,2000071160789223,1999967231142715,
    2000131434387584,2000099126391181,2000101519275729,2000106406482458,2000092390734742,
    2000093359892829,2000143362676481,2000060736389177,2000104945430447,2000088846554071,
    2000121403181303,2000043955874477,1999951275303841,2000128623244349,1999892613944401,
    1999942457574874,2000016789880041,1999913014230663,1999928980919414,1999870532140205,
    1999876281195662,1999913742781988,1999915539002774,1999875092920445,1999883912546469,
    1999944996519819,1999960674159518,1999884876446998,1999859983678925,1999916198891386,
    1999889821572939,1999879084049110,1999845622932562,1999932313689743,1999907361985800,
    1999879569613017,1999865546594463,1999939688742633,1999992881091631,1999972110888663,
    1999913110415509,1999872171481821,1999908562097490,1999843635310747],
   [1999791497424168,1999749797215004,2000000537760783,2000044562631551,2000008239370321,
    2000079539357936,2000106380391214,2000054572504173,2000078890127423,1999808365631328,
    2000230629743691,1999984606121313,1999902109987368,1999849789145174,1999974772410893,
    1999914542916188,1999888882555219,1999820530877243,2000012504108972,1999943599568248,
    2000074645471822,1999950568174043,1999886506891641,2000120732179610,1999796089157627,
    1999917559916383,1999902324284090,1999952048029777,2000110554632123,1999964787623498,
    1999962582604689,2000136241007114,1999928945065900,2000145558303021,1999885681210410,
    2000097965994631,1999878322882991,2000062971512204,1999938914114458,2000149585416374,
    1999768151038469,1999949912634782,2000219154499253,1999808608315450,2000121295399043,
    1999924414226720,2000008984546934,1999883697419906,2000178919425118,1999951151570233,
    1999976620113941,2000037967510904,1999910795727227,2000081140781213,1999997728750560,
    1999970969934088,1999959217452447,1999927957228996,2000034834357285,1999931534704866,
    1999963884567474,2000093770896818,1999888642081763,1999960003570667],
   [2000257305840868,2000115059872488,1999842659580472,1999958983267501,1999977233175342,
    1999965429802630,1999917445164064,1999919359372497,1999912819139464,2000022944815818,
    2000009039040375,1999826291972683,1999850311123737,2000027721371396,1999963725228037,
    1999977742883745,1999854246033539,2000063756703540,1999901504158305,2000103920474347,
    2000037904353539,2000103187960772,2000025778417469,1999914316322280,2000409532478563,
    2000320057502172,2000065853319199,1999920254596974,1999798712158797,2000093768291572,
    2000389236083451,1999660048918885,1999496605439157,1999502825798349,1999888148069099,
    2000200236291234,2000478244488673,1999799129720025,1999808229567633,2000235535749609,
    2000260781793363,1999946318335098,1999854435945050,1999785188370423,1999742658962788,
    2000452986217576,2000257753360295,2000372643272251,1999318489110652,1999217094776732,
    2000790347293331,2000018489414865,2000196028401258,1999601245883997,1999580772038865,
    2000084585002245,2000105349733227,2000423917390254,2000005026370369,1999691073730079,
    1999897642083862,2000047012023774,1999793396454869,2000455357528088],
   [2000561308237355,1999538573254593,1999497345205360,1999851989592726,2000200744780714,
    2000569625925424,2000261431164175,1999146882137031,1999857889955516,2000213337035923,
    2000867021470190,1998771927427896,2000020785140311,2000249297153405,1999823320471702,
    1999397229578407,2000711982823300,2001258154735729,2001091696396545,1999612433507317,
    1999018789642930,2001097070166040,1999609619942301,1999735228373091,2001191963878758,
    1998796040260072,2001631504133831,1999253811900463,1999554188771524,2001002170077621,
    1999621597012100,1999757221563508,1998685331673350,2000142650189941,2000134729496950,
    1997881927569029,1999912491629853,1999310878447358,1998285317991235,2002645709121619,
    2001356377797434,1997127541712902,2001119412373682,2003144140174847,1998651141162256,
    1999358936689823,2002088608819087,1998776252783478,1998413138551737,2003897718297028,
    2002919938176535,1996261160747933,1997408571027721,2004482740467080,2004725720079888,
    1999132526529963,1997844691068983,2000878349487986,2001806560182626,2001363684966186,
    2003332160241997,2004439583526085,1999946162322426,1994541201625785],
   [1997324910165168,2007543589192064,2013278900325007,2006377405618074,1993289019130140,
    1988325669463331,1997896450032719,2013915952875182,2022213671300205,2015726108167958,
    2000005258129533,1987650702486384,1988251435563624,2002270375286939,2021971250901420,
    2037098982918442,2040774849776242,2032298732332496,2016516663903059,2001154087754044,
    1993762174342642,1999556371815693,2020538381269874,2055587715161896,2101168800347686,
    2152343553845967,2203749516906630,2250387586172924,2288227312108157,2314585123671564,
    2328226656938646,2329260830670590,2318916772895095,2299230234108595,2272672764330807,
    2241806062150904,2209022360643750,2176368834132518,2145437799138636,2117325971696290,
    2092665442193553,2071702781971195,2054390809407202,2040472996576142,2029559468053153,
    2021196621241318,2014925400253929,2010320811663273,2007011184695683,2004682947127622,
    2003078752720896,2001993791426267,2001271234838473,2000796115799705,2000487525937741,
    2000290163772236,2000166672482519,2000091724727211,2000048012007831,2000023729343719,
    2000010989717223,2000004730129422,2000001876129183,2000000682165457],
   [2000000230390487,2000000078244302,2000000032682578,2000000019211587,2000000013465096,
    2000000009327508,2000000005975087,2000000003506668,2000000001895938,2000000000951647,
    2000000000446571,2000000000197132,2000000000082358,2000000000032794,2000000000012563,
    2000000000004692,2000000000001739,2000000000000651,2000000000000250,2000000000000096,
    2000000000000035,2000000000000010,2000000000000002,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_4 : List ℕ := pNatCat
  [
   [1999888473267301,2000148839922322,1999991859352378,1999955928704212,2000001249949202,
    2000078990007320,2000017783163245,2000014500562693,2000040709991897,1999946067050997,
    1999878859099618,2000110159256576,2000113320308035,2000103500935821,1999875739709143,
    1999855555831335,1999995943866092,2000029344038658,2000136054606779,2000089794616151,
    2000032453349657,1999979709992323,1999822670867351,2000032574329231,1999966926170508,
    2000086901069306,2000150315184577,1999934066731952,2000203573005051,2000084404685937,
    2000087957503920,2000155484283480,2000093119266641,2000066215580576,1999925396437902,
    2000078644437419,2000004995475517,1999935822999799,1999925838337999,1999957979208021,
    1999991831986734,2000049584569369,1999850157244393,2000026672602788,2000068386939066,
    1999889403975221,2000211188333181,1999908349082141,2000016223910936,1999955518252349,
    1999994165462904,2000017779112312,2000072749502533,2000054087151892,1999778721838024,
    2000075139145395,1999952245109808,1999968954095504,1999858629700891,2000148675545495,
    1999980905354594,2000003011232513,1999887205935573,1999986040164568],
   [2000009814030647,2000102575845188,2000093205717769,2000117232880781,2000001488191234,
    1999840605107625,1999959659711366,1999983126084159,2000137957391916,1999978379734410,
    2000007856523703,1999895370865282,1999975157140545,1999949821731980,1999930560294722,
    1999962838486269,1999985643755832,1999992569192137,2000091167266891,2000000695385165,
    1999992692944281,2000002847959145,1999993643169412,2000108642101556,1999987335007099,
    2000088205110221,1999971680891107,1999987436285872,2000157454903272,2000002005919614,
    2000049256710481,2000150740317917,2000096341298029,2000068665784271,2000104235997553,
    2000110591245228,2000101401200870,2000096117333105,2000097376954544,2000119598110314,
    2000085439825881,2000069429111087,1999970789681614,2000018029349764,2000027011519697,
    2000002407659259,1999918755140006,1999916399538673,1999958500584369,1999924929940961,
    1999871279111892,1999852178363736,1999933081977014,1999904378546917,1999926012061357,
    1999876570947794,1999961169382347,1999920359757418,1999894410294957,1999860891702033,
    1999879135656633,1999885466665585,2000042484797781,1999685787666490],
   [1999966478304325,1999839030569552,1999967125664149,1999916334681028,1999871794789307,
    1999977487632618,2000111935448962,1999829480555603,1999850211957720,1999840541787998,
    1999866304374985,1999782698285756,1999733008918707,2000139196648182,1999970099998807,
    2000068294800826,2000020452296129,1999962949521916,2000173201161189,2000087436407203,
    1999902022996156,2000125049063739,1999875359034926,2000140547410121,1999786026265324,
    1999940264997086,1999831698910425,2000011624456938,1999810591974773,1999963842151866,
    1999994605547343,1999983232997137,2000158096977230,1999698953902218,2000117624132870,
    1999824662592222,1999881445774156,1999982181186622,2000053707854773,1999841125419247,
    1999979726231307,2000201044437379,1999932294130371,2000040125096547,2000018829902027,
    1999943897084114,2000072878298967,2000014760509389,2000001156629110,1999948412922713,
    1999919023116657,2000041508844402,1999986366021660,2000016274198319,2000017364378977,
    1999892386157421,1999964684310668,2000140578695054,1999917332099443,1999963829127818,
    2000095945237587,1999963692214104,1999904166696851,2000102457567425],
   [2000091342152811,1999902418283734,1999880290728389,2000087044061805,1999972840983503,
    2000065160208459,1999808518332759,1999944642072303,1999960495140069,2000156540654360,
    2000045345736732,1999923048206590,2000155614606348,2000002706259011,2000032509015481,
    1999858177116527,1999885478805005,2000071889074665,1999959794984239,1999837035442717,
    2000143631380841,1999741670214618,1999948430088790,1999972013210818,2000005309895871,
    1999899985384424,1999948579815921,1999715871460040,2000103288674543,2000304436978597,
    1999829531280983,1999767582226452,1999956547624300,2000283948139794,2000212822504475,
    2000498181318715,1999675394989412,1999785923358508,2000519754268925,2000157982597855,
    2000556531296231,1999238660062853,1999711866074836,1999934529835587,1999516790524994,
    2000259839202366,1999974900785187,1999683244329235,1999883725368790,2000485102050558,
    2000528422864521,1999841096870251,1999298559515183,1999853906306445,2000398969880810,
    2000242312525739,2000348838498205,1999658740810255,1999466994395084,2000131894465002,
    2000567663350463,1999561704180888,2000345168718505,1999457276010175],
   [2000084051310325,1999446040490174,2000526860469981,2000167748433159,2000070916167043,
    1999962347386309,1999448484143245,1999516640857112,2000910842285078,2000965623279489,
    1998937152777975,1999697815669021,2000224816007509,1999996612927525,2000894121764158,
    1998148137707425,2001623491750129,1999977236906322,1998730831701009,2000864005617035,
    1999736509606688,2000811119695691,1999555245832103,1998627971175330,2000106764467904,
    2000061613661439,2000954079612075,2000251472289827,2000113443180912,2001640700505251,
    1999109692566455,1999042010980305,2001943047896645,1999529295470274,1998996241243187,
    2001801384266244,1999392083236119,1998813487602676,2002624579100740,2000116897127359,
    1996836728042404,2001192898408730,2002447958081850,1997646330091873,1998033934896456,
    2001065234981290,1998676919085666,1997639851680823,2001631577481556,2001396658954892,
    1997086308918382,1999034549839011,2004420175647017,2002378131225002,1996441442323542,
    1997510336014207,2003013111675866,2003250455480202,1999149007266050,1998196645793554,
    2000393729114517,2000889349798685,2000308866367232,2001920756223708],
   [2003374670082977,2000351570840341,1995866306709188,1997505251617603,2005286883498378,
    2009551724680333,2003501267101107,1993155671046778,1990905839671739,2000602504756184,
    2012583787813152,2014198784662881,2003256879836674,1990062690668411,1987132936804023,
    1997647940362925,2013225722553904,2021666874763241,2016779877879226,2002387481180394,
    1988725951876955,1985132577231338,1994445508283809,2012165385556464,2029761512933047,
    2039357117128129,2037211551141473,2024803209046033,2007694381581840,1993206921416965,
    1988069654463265,1996763075936590,2020764659547086,2058604583807804,2106511536278084,
    2159356244569606,2211621421434394,2258235121319417,2295195042630861,2319939658475112,
    2331447020901416,2330098380997320,2317389450359493,2295570868882988,2267274118601535,
    2235165864660958,2201671604597589,2168796681324841,2138045752418092,2110418888133751,
    2086457206206158,2066318235510199,2049868002605471,2036777712003342,2026612055143757,
    2018899010451303,2013177580942062,2009026263988107,2006077870806099,2004025602900326,
    2002623239998377,2001680886001446,2001057472229545,2000651523698674],
   [2000391804903647,2000229100243270,2000129739725138,2000070883336739,2000037231147881,
    2000018742180942,2000009020225934,2000004144542018,2000001818954909,2000000765899089,
    2000000313121816,2000000127386667,2000000053642659,2000000024387422,2000000012165462,
    2000000006499859,2000000003561440,2000000001929965,2000000001012693,2000000000509567,
    2000000000245111,2000000000112739,2000000000049688,2000000000021048,2000000000008604,
    2000000000003410,2000000000001317,2000000000000496,2000000000000179,2000000000000062,
    2000000000000020,2000000000000004,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_5 : List ℕ := pNatCat
  [
   [1999833138462104,2000014276107725,2000071473225200,2000063770565039,1999967426783060,
    1999957519417579,2000017040129305,2000070137286713,1999940612126930,2000086562027156,
    2000066987694667,2000017513267163,1999944706440368,1999848589409429,2000027145455637,
    2000140454521378,2000090694374593,2000088935946413,1999854882547399,1999955554369898,
    1999933328714152,1999897040647977,2000194707208883,2000019228254283,2000124886563434,
    2000089600432691,1999860710121533,1999949629648812,1999943652490292,2000044226834205,
    1999970834917518,2000047646704459,2000103121754571,2000054103045209,2000009870997827,
    2000179802458934,2000119939495407,2000116993707575,2000150579179194,1999870559503191,
    2000250211290061,1999989630456499,1999960886885993,1999999592799663,1999939370359334,
    1999989425239823,1999931784440849,2000086647429590,1999816159173708,2000054324163738,
    1999937478205372,2000018592517034,1999978412309166,2000185182591420,1999939845540401,
    1999900004150779,1999994403090839,2000093760120868,2000000218001803,1999975218716304,
    2000032843609251,1999999141235584,2000036705397892,1999838075250265],
   [1999977638743341,1999950804037643,2000054965271493,1999983492911496,2000021924485094,
    1999977787832680,1999897878051703,1999911766371333,2000024484052869,2000105394822253,
    2000188428202140,2000038254111498,1999930055413823,1999981173365028,1999915952345494,
    2000075644839865,1999999864960550,2000030593262477,2000013148816078,1999927637625439,
    2000053548231890,1999919433750891,1999892725918641,1999982517526548,1999919604005841,
    1999982766771553,2000090680457297,2000001314946411,1999931175267532,2000023138755018,
    2000038621690737,2000036351351876,1999995152179304,2000059764693632,2000021984542193,
    2000017500485102,2000014005555799,2000026189735246,2000063332973818,2000069015660917,
    2000078388692363,2000056564569090,2000125186525555,2000096687537787,2000102094852100,
    2000027593546946,2000133639000533,2000146475759082,2000135296432769,2000041112971420,
    2000092746376189,2000032274061021,2000164659603374,1999869415753157,2000124895634354,
    1999916201876594,2000014387563623,1999990214509281,1999871124266772,1999897242801736,
    1999995765490461,1999823838485368,1999909254016083,1999870220675799],
   [1999913261331239,2000060527256822,1999803783985337,1999916201850614,1999846382821305,
    2000028773186692,1999901703255705,1999740993616147,1999977226124270,1999996652884012,
    1999706489663017,1999992148520340,1999716862276652,2000092889065340,1999848538163783,
    1999975732426852,1999941949186772,2000079914083026,1999907341641067,1999776096967922,
    1999809532229780,1999698610236643,2000098716680510,1999693663214367,2000039594795424,
    1999932221716024,2000043139324513,2000108911744203,1999966897575683,2000020182811842,
    2000137410887759,2000099670709889,1999864156270996,2000102280092693,2000032352775952,
    1999790471355600,2000001715808561,1999897430455225,1999776643718269,1999947303404438,
    2000000383025365,2000041869972404,1999949338632429,1999941869485028,1999972099578775,
    1999940307453689,1999917302031291,1999960595463657,1999822595797528,1999966153173724,
    2000062938289067,1999960395387419,2000021272360219,2000068090996017,1999892876603443,
    2000049451766344,2000111048721796,2000066587783508,1999798310621147,2000115918578980,
    1999966259089203,1999952889333629,2000000709419031,2000038397351322],
   [2000008475850203,1999829887950548,2000083477735559,1999991780461112,2000049656346078,
    1999971192095249,1999879405825993,2000018824216571,2000182306124036,1999895916189453,
    2000068197359940,1999791000726707,2000142035036588,2000113362364939,1999894243880435,
    1999885683654686,2000090513689522,1999879857003421,1999898249657047,2000085287122344,
    1999874172882352,2000175047184137,2000037603729510,2000077104241175,1999942692612498,
    2000099027002950,1999833612017460,1999795594723650,2000539893545771,1999489512812826,
    2000089745440146,1999816784129316,1999916073019318,2000360039225997,1999615531624484,
    1999960515430373,1999713555471126,1999912893265103,2000498802372678,1999980926873575,
    1999394607462896,1999846495394610,2000284633401934,2000205222414474,2000168376627608,
    1999864078244454,2000054719533675,1999841670357230,2000470583466140,2000557862782677,
    2000336390333575,1999040212617170,2000464812810791,1999680083526823,2000206336743748,
    1999534334911770,1999506508361437,1999634340544987,2000437557273095,2000741853901574,
    1999807993422787,1999539643547256,1999880762796135,2000173984629293],
   [1999978244758994,2000406050800786,2000209970272339,1998836334802907,2001352217519579,
    1998820710390772,2000484892224058,2000630736944325,1999347814066651,2000608652829029,
    1998174919734408,2000495446404912,2001651818107701,1999054246042409,1999636194512864,
    1999741088657909,2000388553415993,2000240845124139,1999385698195087,2000731402367043,
    2000047351150977,1999550734699059,2000185311099603,1999283403673650,2000860318053250,
    2001006683242114,1997959312503211,1999997306787368,2001738351326778,1998784629473902,
    2000119952349313,2001752315424025,1998205977174011,1998731539314130,2001505830371422,
    1999006866253910,1999122957468844,2002845139485249,2000394885433642,1997531419512776,
    2001519774809563,2002524219046088,1998011004006131,1998627815669886,2002288995260319,
    2000437172621893,1998383857055033,2001122967481973,2001363506291044,1997967574894258,
    1999252872766686,2003205707455187,2000893197387311,1996095506894480,1998110814268026,
    2002765454594677,2000859625225674,1996053514798829,1997166279677115,2001924131578344,
    2002508158971553,1999531416308800,1998841320516767,2000437188590143],
   [2000471525139942,1999653223770970,2001004107301246,2002586593014959,2000317882264819,
    1996357563129749,1997351577415427,2003734237186693,2007225840249072,2001961617234178,
    1993636089069786,1993072665850717,2002271471401808,2011140342196708,2009153844566904,
    1997732379172019,1988907885874825,1992302173850062,2005095879468462,2015124681545878,
    2012887519974952,2000220155888057,1988130187777823,1986933517712421,1997901412135998,
    2012916841939459,2021223666876741,2017222742666662,2003766376404181,1989601767417931,
    1983600193675367,1989746169096598,2005520993176729,2023832669393564,2036778635959095,
    2039129077002794,2030163284158970,2013555216002905,1995805873239928,1984077655213051,
    1984232851652922,1999562575005240,2030332032545202,2074028269957722,2126096448659147,
    2180924064081291,2232840451574040,2276946966286946,2309675348005955,2329052103322185,
    2334696956392669,2327608124075209,2309804124502008,2283904022082968,2252724825432599,
    2218952092711023,2184908602437349,2152421259803791,2122774038528335,2096730290779915,
    2074605036983697,2056365458049579,2041738154561020,2030306450704805],
   [2021588587448834,2015094778251263,2010365426090969,2006994151417194,2004638978133345,
    2003024455807465,2001937260357825,2001217781331798,2000750021465010,2000451641352505,
    2000265283055048,2000151625433799,2000084135081257,2000045229866824,2000023516507675,
    2000011810990965,2000005726941667,2000002682022779,2000001215433922,2000000535234781,
    2000000230759507,2000000098557409,2000000042366180,2000000018644426,2000000008502800,
    2000000004023864,2000000001956156,2000000000961133,2000000000469719,2000000000225572,
    2000000000105620,2000000000048019,2000000000021158,2000000000009032,2000000000003738,
    2000000000001501,2000000000000582,2000000000000216,2000000000000074,2000000000000023,
    2000000000000005,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_6 : List ℕ := pNatCat
  [
   [1999864621154799,1999904794525247,1999948661078210,2000040984296461,2000056751532940,
    2000096581948057,1999918734880327,1999985164927084,2000044657338552,1999979942253280,
    2000012183423623,1999993045106586,1999990659673187,2000174713482727,2000023955396551,
    1999987282351676,1999940472470578,1999787954791756,2000120261011113,2000058401272410,
    2000051146313489,2000181071768866,1999939375287248,1999957910711596,1999912508598868,
    1999933138254460,1999929963815580,2000037510052715,2000132424297334,2000155413923448,
    1999990171096163,1999955046617157,2000095758647048,1999783352103386,2000077869816303,
    1999922813763197,1999987501052577,2000159888769907,1999930331647595,2000032903421696,
    2000021716021452,2000263772711689,1999987568091711,2000167449423098,2000063244055096,
    2000110640414222,2000044309052266,2000160101325948,1999995903472088,1999952373110673,
    2000032111290227,1999995225710905,1999932665623685,1999952231070762,2000106612333367,
    1999872644088143,1999924021350473,1999903514783697,2000098100213743,2000060795215473,
    1999994612917566,1999959215053862,2000005158377871,2000031844715972],
   [1999990317533356,1999945287506175,2000048575560459,2000059453836319,2000000265390782,
    2000049756757040,1999899652478327,1999990497039037,1999923314685477,1999917504075707,
    2000062923527232,2000022245986837,2000072449775348,1999918748801996,1999828220892071,
    1999960838546495,1999981822920230,2000081639726541,2000168989455065,2000042134092743,
    1999955838666647,2000038326794490,1999962496336556,1999985084866199,2000021624738154,
    2000033579904454,1999972358622935,2000011963051879,2000071369212857,1999973912567679,
    1999908039957661,1999895747901890,1999979365496870,1999957955096041,2000008997547574,
    1999959868438165,2000016404378640,1999976280188839,2000022327685356,1999970821564394,
    2000059410483980,1999981094099449,2000138045162979,1999884604022626,2000113162761109,
    1999948933012794,2000086983384750,2000028444537457,1999957427142598,2000098068341977,
    2000154311262847,2000008163710830,2000111737516572,2000052016945144,2000039741965173,
    2000233403873716,1999996869595452,2000162476741768,2000072478368857,2000139826365547,
    2000114509214115,2000021632655825,2000045163262509,2000114691379871],
   [1999938174915266,2000193964975555,1999712859079527,2000146346685644,2000001811664338,
    1999898816789731,1999810604164083,1999918281282330,1999992783396512,1999851301746067,
    1999965658259014,1999751750276638,2000162695286309,1999762949290689,1999946237141377,
    1999877376841509,1999892885670557,2000030557759045,1999806819517783,1999856042844334,
    1999925201225079,1999923785137411,1999792671178323,1999857705289464,1999888235201359,
    1999955651140197,2000173723458186,1999895257280718,1999818259866028,2000065763701524,
    1999795961287382,1999728359522874,1999873636511919,1999875994380763,1999846789215889,
    1999948521698196,1999974833519484,2000011325257866,1999958855722862,2000090650923686,
    2000106339767196,1999982467932404,2000031221117540,2000125872414451,1999959277332053,
    2000090739437939,1999869962863156,1999861179880889,1999824393956377,2000047328438330,
    1999861077109109,1999916929846497,2000090455952721,1999870100910812,2000010678586953,
    1999995515483295,2000005592389666,1999753667675804,1999902839020304,2000040646894878,
    1999957442562860,1999870827496194,2000114660011263,1999843879371413],
   [2000129953218697,1999937472575930,2000068105352419,2000102440917236,1999942041125137,
    1999932222068620,2000032640315750,2000028838596830,2000006203541765,2000070482210541,
    1999689078479069,2000159391001378,2000102277066419,1999917976864949,1999910850923901,
    1999941674807021,2000188630625793,1999752452696497,2000372266402606,1999601760884742,
    2000146763999282,2000205180451966,1999585056669811,2000395267382905,1999868634766049,
    1999969285656493,2000046067573268,1999851261181129,2000091981689146,1999811618177495,
    1999818726503968,2000245795366408,2000137227032859,1999849046702204,2000215326413726,
    1999737217347664,2000105691089558,2000112074112428,2000283602645862,1999331393406915,
    2000122268707176,1999798737623416,2000799157487352,1999358378473433,1999769306855005,
    2000020268312648,1999841420952878,2000158908174276,2000210429311799,1999810586187053,
    1999367813669753,2000017557395235,2000374758303378,2000103272793279,2000051158316486,
    1999392888913514,2000400432618973,1999491265929696,2001697497885262,1999240493208138,
    1999694412503312,2001138145505613,1999164486280285,2001215518648420],
   [1999301651499592,1998977211195939,2000352697106790,1999237410933004,2000956854756403,
    1999984231858529,1999204373108222,2000782204680382,1999626496412164,1999575323291424,
    2000342381530720,2000606016535318,2000267997953942,1998533568292379,1999990852559044,
    2001469958012609,1999649448445435,1999900441137413,1999866365786119,1999071221010306,
    2001012994434685,2000123552597948,1998586536399430,2001425725233588,2000481547920727,
    1997591918926607,2000761859875406,2001684105916889,1998480739428398,2000086837327906,
    2001268084250026,1998373589905867,1999855768038718,2002246824051976,1998951163983450,
    1998379610168256,2001796471054768,2000047641020998,1997762100904499,2001547200654365,
    2002531879668179,1997963440254559,1998038284349460,2001693312981446,2000233072991655,
    1997910560512074,2000555899768337,2001849332464116,1999076955872014,1999400445789052,
    2002424524942504,2000703281697923,1997226162829189,1999677369118512,2003537217224772,
    2000879945090757,1996630752163419,1998891105027963,2003294587617043,2001867910561049,
    1997783775680474,1998340723524060,2001667084018768,2001556689161506],
   [1998766992194238,1998081888635362,1999297965444192,1999191585110565,1998607176967034,
    2000278242217222,2002246765553880,2000498500712976,1996891798411915,1997599086710082,
    2003081637498002,2005836760269415,2000871873259975,1993878259425517,1994460718942757,
    2003040700741639,2009369649632427,2005146410706807,1994651084853010,1990044037131658,
    1997201427232242,2008885064540717,2012677477220323,2004309693809921,1991991177459182,
    1987903833086660,1996250606004517,2009601765293894,2016132645915560,2010167921463582,
    1996621449809395,1986404867021642,1987572340388775,1999496668171465,2013926400964580,
    2021206240208911,2016707511204393,2003313536607711,1989104939012634,1982412259408339,
    1987395442795636,2002320450624321,2020869946582486,2035321230011948,2039867784532072,
    2032726146550290,2016504664745931,1997088342172643,1981712567658001,1976948959933859,
    1987152065673791,2013655848671807,2054752519367131,2106292315446589,2162646461125701,
    2217772596928587,2266174698365983,2303618615816640,2327532491752977,2337086600616318,
    2333004894452949,2317198519896425,2292321034912103,2261329936798621],
   [2227112617027100,2192208927413308,2158641736356980,2127850417349684,2100709243460844,
    2077604369948759,2058541163370428,2043257837693148,2031329091132637,2022251361067940,
    2015507196322528,2010609623606481,2007128975253492,2004705360988514,2003050315268000,
    2001941211677122,2001211732106590,2000741024516790,2000443335740088,2000259079312800,
    2000147656318937,2000081950158754,2000044234799527,2000023197770179,2000011811252718,
    2000005837188425,2000002800981235,2000001306446085,2000000593575421,2000000263625566,
    2000000115049413,2000000049683397,2000000021410594,2000000009287055,2000000004082201,
    2000000001823453,2000000000825974,2000000000377085,2000000000172108,2000000000077906,
    2000000000034743,2000000000015187,2000000000006485,2000000000002698,2000000000001090,
    2000000000000424,2000000000000156,2000000000000053,2000000000000015,2000000000000003,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_7 : List ℕ := pNatCat
  [
   [1999922220252879,1999923195998932,1999875978942228,1999963242807392,1999909317243077,
    2000010371075897,2000123499894912,2000035399939942,1999969900723084,2000042156760410,
    1999931950720239,2000030454360997,2000084423956430,1999873045499762,2000049589050459,
    1999981085279970,1999967865070008,2000240738091301,2000033621411601,1999977310203443,
    1999939254293290,1999916826076722,1999910930661688,2000018210164783,2000096008661462,
    2000085182486517,2000130740361327,1999900521608690,2000169314406415,1999860238354301,
    1999804905942626,2000043469384331,1999883723434189,2000153214336436,2000038379825786,
    2000144742070272,1999941551097238,2000147930148184,1999952403654729,1999894268191136,
    1999917960369936,2000075874967659,2000004804221677,1999946664004656,2000039596233137,
    1999977958222554,2000046361108090,2000053827349630,2000211944011519,1999984368481833,
    2000088556794871,2000141895338922,2000127464850632,2000058026946759,2000068761037819,
    2000106613245327,2000051469642742,1999935073989712,1999953931518981,2000036821801136,
    2000041931974036,2000035935746125,1999819882260009,1999943381230159],
   [1999997261924802,1999968055500058,2000048819738136,1999945923984134,2000038962623478,
    2000047900666209,1999958812303305,2000007033133792,1999958382480201,1999998167266891,
    2000054382150191,2000002944550785,2000015570547815,2000116059816673,1999952295775430,
    1999910660931926,1999931148577351,1999931392643808,2000007587995762,2000098947677811,
    2000075986713195,1999896025470071,1999893947371459,1999897377916176,1999966681876930,
    1999982345066531,2000129562494158,2000060687895030,2000040501986901,1999966425484786,
    2000083833660084,1999958655611436,2000059793144611,1999858483613669,2000113932808237,
    1999962176952465,2000105347832688,2000016439519893,1999933228514717,1999987408291585,
    1999943229175946,1999910508835561,2000001873586502,1999932943985630,1999969579880990,
    2000102553920178,1999814427297816,2000067460691569,1999996274639157,2000023373300861,
    2000026896326603,1999988583733508,1999996813661144,2000138530836304,1999894069400045,
    2000162972886708,1999787757468052,2000186287894785,2000020654443653,2000022171002280,
    2000127298293297,1999979342008099,2000119459925172,2000061811087011],
   [2000182912107294,1999850707750518,2000308583635038,2000070788333357,2000125548216257,
    2000058872495627,2000026641445377,2000279060785366,2000011032492003,1999987264300498,
    2000045465496027,2000077770828505,2000056031762530,1999986730440458,1999927897763769,
    1999942168347205,2000039840844355,1999837333733880,1999818502408122,2000043312050174,
    1999859996891541,1999939790458217,1999947161121696,1999794473386407,1999959604470856,
    2000060622310442,1999768767678646,1999844442579880,2000008954740905,1999984684013614,
    1999837378001999,1999829089857593,1999843765152175,1999892471702223,1999760398829549,
    2000070330102924,1999931108253520,1999991814072743,1999990695976348,1999987134633919,
    1999842021782737,1999795454636616,1999936121995147,1999709450684757,1999948424780830,
    1999853931794871,1999840942072653,1999943811209435,2000102780146302,1999947991198601,
    1999990284721929,1999986114791566,2000216786054373,1999890867283415,2000220451890253,
    2000071460719078,1999852160874379,1999957806106744,1999935731666537,1999947457773404,
    1999862565101765,1999892372205789,1999891963587133,2000168511722353],
   [1999839475767558,2000037410211975,2000005006367421,1999761795657441,2000095846757889,
    1999737906732280,2000136254703005,1999759766706868,2000187907461225,1999713808002925,
    1999891163864133,2000486949512294,1999611065468172,2000221286757377,1999916053071007,
    1999879744631040,2000366348985593,1999809817415274,1999908119247100,2000069236104688,
    1999996848820303,1999997346613724,2000038441838089,1999796145107984,2000286327942915,
    1999647551305645,2000186477324630,1999940415021345,2000210048941627,1999494928374222,
    2000551682194891,1999608059705653,2000229421750718,1999875552295712,2000005783228117,
    2000173843491085,1999837624697921,2000248630383473,1999815612535585,1999537488202448,
    2000160901769019,2000375475119861,1999940044587252,1999368962421092,2000625788712199,
    1999618903299268,2000762176260526,1999363337403092,2000366638180452,1999632353269511,
    1999518237185709,2001482458510726,1998797816916118,2000411557014432,1999881174127928,
    1998906941500121,2001397040031555,1999627211168017,1999771150476357,1999866990656667,
    1999205987613693,2001004049727570,1999890510813477,1999545143755875],
   [2000176606070585,1999400090957802,2000481415349693,2000478423781113,1999631977091988,
    1999848488695050,2000032880203591,2001152570108610,2000297715345784,1999071583780426,
    2000845264190327,1999854770224297,1998344256037518,2000672278202616,2000544346781154,
    1999482335502628,2000430647547362,1998981421877116,1999395897218513,2002229895869670,
    1999665738565627,1997991658911185,2001462263483721,2000494548880074,1998142843120202,
    2001237504118118,2001340562789066,1998170485152664,1999982494060510,2001189771513379,
    1998620963324952,2000012058552075,2001974511997128,1998657441877041,1998185266217198,
    2001980672960492,2000698389344061,1997808260238975,2000598508423642,2001903366326405,
    1998261028549911,1998603327412859,2002434364691390,2000977036917869,1997724375936113,
    1999642247262479,2001475712017672,1999237562583262,1999138435094551,2001947727084141,
    2000886694603681,1997735578080102,1999394029370735,2002283722768345,1999732870150628,
    1996690513429860,1999835189067005,2003571157029484,2000924817049994,1997106507138029,
    1999159848060207,2002908774673458,2001621260533110,1998197279194518],
   [1998673571727315,2001354790469035,2001284715033173,1999416350005445,1999521186399828,
    2000763285726260,2000277305976770,1999346201892233,2000606662009493,2001983109414354,
    1999749584446485,1996014037271423,1996706620731185,2001899824715066,2004273844105372,
    1999631292539615,1994005179809143,1995889256643715,2003989236294939,2008030063048745,
    2002156028346669,1993086439545836,1992122113112429,2001110166367068,2009876074325903,
    2008097769509874,1997301984736973,1989204407205598,1992793408646767,2004741538898617,
    2013073363720203,2009454403226929,1997250040739748,1987925429232877,1990154785351594,
    2002175549435859,2013794662851819,2015363741688377,2005583271949873,1992051285302743,
    1984998779645561,1989698537784716,2003112553703974,2016483375075578,2021344732179221,
    2014706955902221,2000440913805187,1986643033684792,1981039934443066,1987125990226450,
    2002802625017396,2021714403683483,2036227114512502,2040551862786552,2032813669931718,
    2015527897798097,1994614948112255,1977523495319032,1971169742023303,1980281802904658,
    2006482814086241,2048179404562791,2101123499005008,2159406335613414],
   [2216611233678957,2266877409261806,2305695111971593,2330343373504308,2339971115040778,
    2335388413099081,2318667918091032,2292660793843366,2260517509683095,2225280543851551,
    2189589052605778,2155508531133826,2124475324582407,2097330241539753,2074409232093896,
    2055660958091038,2040767846148298,2029255337309281,2020581160683636,2014201706863093,
    2009616104454996,2006390843923903,2004169058955647,2002669015056324,2001676088493727,
    2001031743092763,2000621995465301,2000366861015524,2000211470620226,2000119008425577,
    2000065323292935,2000034943638744,2000018205847933,2000009235019076,2000004560619381,
    2000002193357407,2000001028113718,2000000470351916,2000000210461939,2000000092380470,
    2000000039932133,2000000017077720,2000000007263166,2000000003087006,2000000001316145,
    2000000000563913,2000000000242663,2000000000104589,2000000000044958,2000000000019180,
    2000000000008081,2000000000003345,2000000000001355,2000000000000532,2000000000000200,
    2000000000000070,2000000000000021,2000000000000004,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_8 : List ℕ := pNatCat
  [
   [1999948098863600,1999992287492397,1999894960322698,1999921105378111,1999962091429729,
    1999908338516818,1999852248661023,2000033976607103,2000060810068337,1999972154534482,
    2000149620724130,1999986126231493,1999898454750127,2000120261788543,1999939587512503,
    2000006435816697,2000072023336365,1999976625394673,1999900529643735,1999957296131880,
    2000107074791440,2000008089285486,2000208236435887,1999962903124188,2000042710417537,
    2000031981470806,1999699672566093,2000083858257298,1999947948831289,2000066231455271,
    1999974338570927,2000184669878560,2000043749414820,2000067447754423,2000016725969559,
    1999901024558960,1999847831251515,1999928324528652,2000081544619161,1999927607059452,
    2000054693364291,2000077642626100,2000193137097649,1999975078949295,1999986737550433,
    2000005121054942,1999925885037406,1999959018727366,2000050953910561,2000013512894388,
    1999928158465911,1999949820980437,2000023474482509,2000112261354524,1999978156301573,
    2000074251990411,2000093569853448,2000085122223447,2000147632766523,1999994581880623,
    2000115687973493,2000199332159090,2000082791223763,2000047109895791],
   [1999940504740897,2000001829458324,2000094947124440,2000039738581693,1999962184730078,
    1999989206665394,1999903882328188,1999972434306364,1999990290995124,1999904843314352,
    1999996130421916,2000045217459432,2000019987506750,1999955317202156,2000053455029747,
    1999981209389529,1999982757321525,1999950110992818,2000040276204497,1999956906094179,
    2000101474841128,2000059083475845,2000116391275812,1999817940296327,1999989140671718,
    1999852262438596,2000055820755268,2000017337986455,2000063726496965,2000074442584684,
    1999887327838744,1999871237283704,1999936179375589,1999945760093268,2000016901998803,
    2000078869366369,1999903934175590,2000182858092271,1999980813847052,2000053171682552,
    2000033404231742,1999927134761732,1999946163510294,2000141893613399,1999876988956123,
    2000191218590626,1999876234572730,2000159393213676,1999929739181955,1999888898777609,
    2000045047248230,1999845687620384,2000097559769004,1999888061399118,2000009829751340,
    1999844361470235,2000170817625150,1999873070410934,2000001607408006,2000066423940527,
    1999873566080554,2000156614628325,2000020350598297,1999998493496663],
   [1999978048535426,1999981139362963,2000102705720872,2000010556021876,1999942976627752,
    2000053601832064,2000168446031278,2000033235549602,1999957032633883,2000118682158771,
    2000047031625681,2000174651665121,2000085495279112,1999950952204019,2000187066681300,
    2000232617005689,1999983519043048,2000125986914418,2000099158000900,2000038397842313,
    2000108524720339,2000092513358520,1999902169902010,2000143851642467,2000032094158010,
    2000007621386112,1999783566498322,1999991252571645,2000054709913718,1999828853004701,
    1999874452555765,1999905649164063,2000039183134044,1999804758778819,2000001003246766,
    1999869524381672,1999839654030439,1999948539856097,2000018469061746,1999830246777356,
    2000025747858660,1999792509604602,1999904102982800,1999746114032859,1999925722514687,
    1999858957692494,1999827394521883,2000179544202225,1999949127525138,1999889050694901,
    1999953296284268,2000009086249734,1999739891345632,1999934041511426,1999790259897752,
    1999772026363153,1999982832479317,1999688838353808,2000259047673208,1999710962258604,
    2000027063238327,1999914830107634,2000130282781009,2000161894240402],
   [1999828924164747,2000410681871920,1999700287783720,2000187691997918,2000113839249664,
    1999541122152627,2000217419390147,1999814845789808,1999790522747027,2000080085649856,
    2000010864048429,1999904415379935,2000169549389080,1999540383599594,2000267514358142,
    1999781726834723,2000196466696120,1999553028905480,2000153608862144,1999664039850112,
    2000459586225793,1999569407266481,2000047769666729,2000215546765240,1999748242889088,
    2000205233467125,1999969689547087,2000033601682506,1999978903819245,1999834014926926,
    2000318047042961,1999750563377271,2000187642956746,1999624490093934,2000610042554455,
    1999175773280748,2000643198070784,1999879452651487,1999575570021820,2000500881187650,
    1999493916242255,2000936215640035,1998883856613459,2000074969411310,2001032238866261,
    1998908485639217,2000991266950578,1999555755351634,1999330324812989,2001006403265512,
    1999371595921264,2000203130627330,1999941582576752,1999403255841336,2000643029830773,
    1999896496569240,2000270082164761,2000091418635754,1999112624716088,2000401371550013,
    2000464330139230,2000004319478219,1999887076500764,1999334696666140],
   [2000237228815194,2000219161210661,1999878642031498,2000484180203491,1998984359800209,
    1999460900779540,2001616150673682,1999431279174717,1998781943604242,2001033315383094,
    1999749711121578,1999463458530569,2000894825609685,1999300652300912,1999675933417685,
    2001142626340279,1998918170422653,1999927086945974,2002816161673016,1999405099197784,
    1997710590898393,2001467964888078,2000682175951851,1998295763567491,2000714236784406,
    2000622027779319,1998118196256430,2000339911194682,2001569733679709,1998744516001201,
    1999617297821196,2001635707088275,1998863221641033,1998432809533767,2002194377120488,
    2001081177860572,1997641484694888,1999939094449881,2002025848929687,1998975315691066,
    1998584529749447,2001843055556676,2000697148113662,1997665899613432,1999753459988515,
    2002093248790714,1999660137430128,1998411512909949,2000823965249586,2000735128590639,
    1998432766991084,1999949055371779,2002456290610727,1999968967468323,1997111496658519,
    1999876829487368,2002756330837677,1999926744308426,1997233731956249,2000316612775698,
    2003295696692153,2000380649844786,1996869521396591,1998744554221472],
   [2001961525891550,2000911993980365,1998374072841639,1999120357538233,2001249602746437,
    2000928875946085,1999569089683706,2000063913983776,2000942391344313,1999894448665312,
    1998927252383564,2000548260466541,2002198912712082,2000232239750211,1997123787184656,
    1998467384951384,2003429522698737,2004642722911591,1999202487597501,1994074108360157,
    1996685131584039,2003870548371991,2005556868140666,1998636395245391,1991820272970881,
    1994480256247921,2004167372661779,2009224759867897,2003209203683343,1992978838930722,
    1990633638266034,1999302772539988,2009535310850308,2009985642807590,1999887621890091,
    1989730140284456,1990096425088558,2000884191337524,2011692818157144,2012199204501627,
    2001877391036813,1990105136042304,1987395270814297,1996246983874904,2009426266343685,
    2016334433577418,2011531872797418,1998611651873306,1987064345613733,1985204235041845,
    1994538282543971,2009169841930320,2019983112573113,2020391473873886,2010028967160421,
    1994583560212605,1982421355584554,1980208685566261,1989813015528443,2007718024472206,
    2026825975217999,2039538452258647,2040717671260051,2029461855552896],
   [2009276887025590,1986856271539731,1970071259455731,1965867655174511,1978634562054277,
    2009366180239263,2055678370371318,2112530462577128,2173373972478060,2231413917456472,
    2280712860836165,2316961930695863,2337850214904661,2343055371738936,2333939870791460,
    2313067212927763,2283655275931157,2249066116779268,2212400609913938,2176230618038866,
    2142469196508961,2112356548643061,2086528175877884,2065130361303556,2047953238690052,
    2034559583740658,2024395543539852,2016876480105853,2011446494427490,2007613963581923,
    2004967650847373,2003178814268937,2001994531636415,2001226559600768,2000738847280691,
    2000435652737184,2000251260547715,2000141639232248,2000077985725151,2000041913473233,
    2000021977976342,2000011240205750,2000005606003316,2000002726867293,2000001294085670,
    2000000599580295,2000000271506103,2000000120341234,2000000052314288,2000000022360724,
    2000000009425345,2000000003930698,2000000001627132,2000000000670511,2000000000275614,
    2000000000113103,2000000000046309,2000000000018882,2000000000007645,2000000000003061,
    2000000000001203,2000000000000461,2000000000000168,2000000000000056],
   [2000000000000016,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_9 : List ℕ := pNatCat
  [
   [1999943385551034,2000007809955622,1999991980915915,1999943625492159,1999888861530266,
    1999977433896542,2000021692059384,1999812567903667,1999898025426209,2000037298606312,
    1999838199957902,2000041149218226,2000121099739938,1999998385330511,2000018541852198,
    2000013469905739,2000072910541773,1999851188836523,2000089286352355,2000052619400888,
    1999948944975177,2000160271915920,1999748790328485,2000039328836755,1999984117065322,
    2000037980031098,1999981534449365,2000182154315355,2000132954567652,1999970940083373,
    1999973227639921,1999930909512675,1999970292999606,1999864792176735,2000061592073821,
    1999964361261646,2000031050385811,2000068649585400,2000179754767669,2000114923410338,
    1999915758432594,1999935244105299,2000001451580755,1999923277578484,1999866517654025,
    1999994798088811,1999996664869912,2000079442121214,2000061045806923,2000113452857318,
    2000117282632340,1999894533808272,1999979229261354,2000020468273356,1999991077054118,
    2000046054705731,1999907147073891,1999947620766850,2000034990517895,2000001705788462,
    1999962647945180,2000022141869321,2000028863666613,2000131605905755],
   [2000095018180451,1999963492959976,2000081232442402,2000125256070097,2000169979188542,
    2000126150618030,2000101389806619,1999948856834869,2000067948510132,2000060274179951,
    2000081333807800,1999936622766423,2000101307924108,1999939840787415,2000029800461335,
    1999846232714485,2000048762486238,1999897098743398,1999966403367527,2000032021288777,
    1999972088108940,2000020039956962,1999990318948553,2000038185447181,2000023202098009,
    1999942345442384,1999860134625741,2000118025687563,1999938934909591,2000163303521950,
    2000069842868318,1999995141998567,1999954601238051,1999946414815410,1999764492100525,
    2000214422203713,1999905555651481,2000165507062089,1999976477536384,1999889999801292,
    2000022119483387,1999801434510903,2000107488219057,1999817037379445,2000039629689033,
    1999967892930275,2000157572119037,1999961700732728,2000072254915687,2000058140528833,
    1999873078878577,2000145636925993,1999886185316822,1999973134836637,2000139554735979,
    2000013558942451,2000040270774502,1999989755822213,1999966902355553,1999986928988174,
    1999979157407692,1999981196377944,1999923597933837,1999957861963313],
   [1999924970313634,2000092198279857,1999960586281531,1999832561988816,2000043572668923,
    2000083759453400,1999935868330772,2000064017407529,1999952071250460,2000040263294045,
    2000114331432307,1999964588544480,1999819457419746,2000201899089363,2000013799478941,
    2000024098134418,2000008169667819,2000024459157617,2000099806789047,2000036188505348,
    2000149747973553,1999921606114097,2000121202612165,2000130842812425,2000172528481200,
    1999962285541141,2000124119541657,2000228775094574,2000122759789958,1999869834979379,
    2000233602131221,2000026860948258,2000120545764489,2000054164397851,1999993410891321,
    2000038441661609,1999939003875376,2000104171500310,1999825958430793,1999922450317965,
    1999956410720695,1999926168716796,1999872704526129,2000044225222274,1999904650830043,
    1999666665076233,2000207873873448,1999675976237546,2000097500039411,1999810340841946,
    2000028317857672,2000020395239725,1999663307040218,2000026130855371,1999601114164561,
    2000071360489453,1999734007980604,1999935247706891,2000238069027446,1999555364880066,
    2000247374049879,1999982319859124,1999789692327977,1999993216296371],
   [1999837442459349,1999520325497130,2000341697184327,1999494614389867,2000129986196910,
    1999629685600034,2000180229333232,1999681305174960,2000268884060220,1999712653148762,
    2000331416602087,1999990023586935,1999940227978589,2000311834580009,1999794740437630,
    2000218727938241,1999878530945956,1999563246311700,2000267878437837,1999815763068356,
    2000196040340831,1999467951199711,2000455953524486,1999545847029354,2000424438814171,
    1999540788267716,2000130944128017,2000120759524168,1999183504746760,2000925488947329,
    1999193132638669,2000229908809338,2000041760630866,1999549058351765,2000822499347839,
    1999001772596063,2000776857376552,2000119577536565,1998867836516625,2001320377779458,
    1999548434301347,1999612015564680,2000580767381928,1999431268835081,2000520944807978,
    1999900270099451,1999520160732323,2000367226003682,1999780530547825,2000367240655213,
    1999992036845150,1999393873807263,2000350984525873,1999928583492909,2000046672439420,
    2000347940008368,1999594497235960,2000038109295935,1999988206492217,2000117015568560,
    2000589368323476,1999047339367708,1999549541801005,2000999823693758],
   [1999501134309868,2000107299758743,2000838640988370,1998521450530127,1999911128444670,
    2001819839612960,1999246053939133,1999272021828271,2000748063434177,1999390365354988,
    2000264211704130,2000874024999596,1998491657514151,1999971334701249,2001663098513066,
    1998525830207646,1999143757165910,2002178949629549,1999226562459537,1997866314902948,
    2001672569388437,2000998819006697,1998324978852625,2000191624901898,2000402970759142,
    1998595064162723,2000871864961517,2001893013298590,1998774031154236,1999383929118483,
    2001911343348119,1999579225126141,1998399282755380,2001554739564834,2000797880760129,
    1997434109749131,1999641335273123,2002382208445662,1999532116589008,1998179592259562,
    2001119573447192,2000852822079083,1998196858793999,1999889397035015,2002121563160487,
    1999645274104977,1998109509425786,2000793892404868,2001389290176516,1998877425900954,
    1999369958007601,2001538037741624,1999854960873604,1997843366452038,2000513653389184,
    2002603503983536,1999324249287673,1996973044095658,2000346421090624,2002883401560317,
    1999808017518508,1997415033102761,2000309498004182,2002630412846801],
   [1999868460469455,1997267723747083,1999410582392784,2002119303471345,2001007720059959,
    1998974545550865,1999602165532117,2000780052650227,1999907592869264,1998988652545803,
    1999991055145290,2000668615321709,1999306445545733,1998686857304770,2000874529443714,
    2002466175883284,2000103769859402,1997153068483712,1998955684180202,2003518937002532,
    2003564673859259,1997970691750290,1994621153584172,1999120079869402,2005856016615488,
    2005294527394369,1997604947115043,1993043664503046,1998064820842917,2006214328804120,
    2006383185486440,1997496222787249,1990292543770646,1993938264865226,2004535654928744,
    2009699191051292,2003290097065473,1992579919221335,1989822200750246,1998422371340320,
    2009298183615784,2010874145422213,2001344438230789,1990320560435912,1988858235058835,
    1998546684055504,2010295091753444,2013220837993661,2004645595618757,1992146814770412,
    1986571342552120,1992759340843635,2005846400258015,2015572459235926,2014450597451758,
    2003233359800018,1989962948722413,1983977937062767,1989541979968490,2003335517029182,
    2016935708954116,2022159786607737,2015791252488644,2001123226750202],
   [1985903196692777,1978200592746331,1982491171450190,1997753426669141,2018146518638142,
    2035627659915022,2043198317439797,2037478984164344,2019809251574459,1995728406743334,
    1973235928265233,1960519529370605,1963857210768758,1986216491272856,2026790178328070,
    2081424920846793,2143691996838509,2206254446735321,2262195076347058,2306053279888365,
    2334434427837855,2346169553406991,2342093042700440,2324561018442175,2296851086888004,
    2262570299415469,2225163170907376,2187568414612672,2152033381161896,2120066443334594,
    2092492024964460,2069568918888797,2051136352752354,2036760224844937,2025861179497192,
    2017814876080285,2012021890003730,2007949698956895,2005152101459749,2003272458324471,
    2002036826722413,2001241935792670,2000741541907213,2000433366908714,2000247760751859,
    2000138495669114,2000075656930370,2000040371687265,2000021036040211,2000010700397707,
    2000005312890700,2000002574951362,2000001218436591,2000000563130814,2000000254370019,
    2000000112399732,2000000048643696,2000000020649205,2000000008613528,2000000003538001,
    2000000001434177,2000000000575024,2000000000228497,2000000000090127],
   [2000000000035315,2000000000013742,2000000000005303,2000000000002022,2000000000000757,
    2000000000000275,2000000000000094,2000000000000027,2000000000000006,2000000000000001,
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
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_10 : List ℕ := pNatCat
  [
   [1999949303948989,1999974773394837,1999986840083571,2000015940163983,2000034430595029,
    1999882296964423,1999870786017934,2000115657790001,1999935748934234,1999847881564655,
    2000006481884662,1999904421408830,1999923922480999,1999824403216580,2000063056958000,
    2000075702082646,1999850074844001,2000233001043467,1999914582368647,2000078619447410,
    2000006954063148,1999961146112452,1999935453471038,2000077488908298,2000126781641635,
    1999925875251063,2000003850805856,1999961633506238,2000031986309904,1999845443727572,
    1999988546099708,2000072597157131,2000087058566295,2000100412387760,2000075635743121,
    2000070170424163,1999962607781267,1999912256488652,1999963210901138,2000040974459730,
    1999860217907125,1999900719816130,2000061298651353,2000095093271659,2000146253684791,
    2000022124765154,2000060291119061,2000096586593100,1999900346872511,1999960365939867,
    1999957946062999,1999898383152510,1999919678995821,1999971797009510,2000018135598949,
    2000156775532711,2000113032374760,1999973856741389,2000032298748224,1999983351113033,
    2000056913743768,2000011358920875,1999975304792867,1999902783935288],
   [2000079153657400,1999964789485607,1999986857686934,1999878692569628,2000069476567822,
    1999943582498705,2000171985314464,2000004707820231,2000030439150917,1999960997616267,
    2000085820451639,2000214388651495,2000066196239059,2000120391062754,2000098837953756,
    2000071933544563,2000014463609818,2000111837192425,1999968906592706,2000156318332964,
    1999935404428528,2000073191688710,2000026038229407,1999944379818473,1999865865730987,
    2000128840852376,1999785806410750,2000112339462677,1999881222116388,1999934906593894,
    2000174556007023,1999883785943528,2000162424571271,1999848322677470,2000051395525662,
    1999850646185931,2000004576460169,2000027978483922,2000128970267004,2000113480376749,
    1999964280305866,2000064548038910,1999758400306564,1999986720600772,2000088414333661,
    1999929227557674,2000106937219821,2000004175029061,1999944650652102,2000042463374283,
    1999936767815291,1999890186467778,1999903643578156,2000011198614080,1999949766432073,
    2000025156876321,2000021423551347,2000056224857862,2000089753667188,1999987372566413,
    1999941203804970,2000066315382264,1999884446812952,2000073565923966],
   [2000123552995486,1999989616222600,1999902920023294,2000168957666819,1999946194340488,
    2000026652813382,1999981130639395,1999816008531224,2000093400886947,1999997660995593,
    1999964912826693,1999806640620667,2000094611742275,1999985689559029,1999952883010766,
    1999912234288877,2000051368761469,1999997357549347,2000110424599438,1999939159317518,
    2000055671830861,1999861524868500,2000123894861274,2000129130741793,1999799141701394,
    2000070076470406,2000074605902125,2000121305043165,1999899754827804,2000064982451757,
    2000119732340021,2000035563377944,2000068837516573,2000014339090994,2000161434358789,
    1999948671560327,2000449311046242,1999793721961998,2000187405878304,2000175807986749,
    1999934268546428,2000283625234401,1999901656203194,2000273400335779,1999850654353913,
    2000146578406616,2000167317054162,1999779052186826,2000193992700428,1999666276685328,
    2000168513441971,1999925674826506,1999776920504375,2000041241017924,2000119939123588,
    1999418247204851,2000440514911242,1999451811843382,2000156257684936,1999813010784664,
    2000160259402369,1999730757852529,2000177448127566,1999624482135923],
   [1999851590053865,2000009492247207,1999658622468246,2000078144289540,1999682686523189,
    1999971288975758,2000292681796927,1999588797749127,2000369244410658,1999513123455981,
    2000242225230349,1999523224329592,2000230506041539,1999443565766583,2000164006239196,
    1999912186484664,1999391814829800,2000507991020368,1999299368650388,2000675769966572,
    1999467046120835,1999832811386244,2000910829795026,1999219003617789,2000782936524762,
    1999655482158335,1999837576755330,2000540791292528,1999028350279717,2000870374204419,
    1999582353746193,1999288698893753,2001148441416033,1999152808826433,1999956725286543,
    2000596044857938,1999317905641420,2000188475743533,1999878575032319,1999953920234514,
    2000149726831694,1999403249633038,2000239764252323,2000071693869600,1999760167640037,
    2000253668050857,1999611620029487,2000151806826304,2000402246326824,1999580520046736,
    2000081239406974,1999954838233280,2000001774375853,2000511560538321,1999435409068006,
    1999929764271308,2000475900032128,1999222288396573,2000523280326645,2000771656637370,
    1998571433377731,2000150030301269,2001038478643630,1998986914920108],
   [2000319750340102,2000723095567279,1998535945791822,2000397504154072,2001464986005552,
    1999005727267837,1999680429804950,2000408535875393,1999078159947191,2000841180649760,
    2000998411956569,1997947715216282,1999916016726222,2002182170245443,1998787196939414,
    1998838253486136,2002056073754640,1999749411532586,1998164759545825,2001365917566540,
    2000864719136165,1998413615750228,2000237323945067,2000757186384805,1998885848756195,
    2000470362930450,2001232741486792,1998188437466843,1998933190703686,2002181431090267,
    2000193437421100,1998079279334033,2000786221356454,2000924075542276,1997907995253850,
    1999605202274873,2002468865225201,1999871019381420,1998077975869828,2001135377882370,
    2001696613468025,1998841419871387,1999474312100400,2001489922863689,1999502632890100,
    1998126344724455,2000856266203666,2001581715122272,1998740675938994,1998773575568187,
    2001290416707818,2000386605399333,1998398579969717,2000311276670283,2001945219007184,
    1999169561851217,1997709759471508,2001149651801348,2002698023575355,1998961662562909,
    1997175655241450,2000758131750626,2002655817112532,1999448286465818],
   [1997593751163586,2000374086388427,2002052389290362,1999545243230200,1997888581240472,
    2000069359050135,2001869811107532,2000418894203664,1998919590761731,1999711781774651,
    2000369091217928,1999482253308262,1999462845318720,2001022274699930,2001143409962100,
    1999119811700356,1998663118312566,2001072539360725,2002029571259313,1998989621102488,
    1996546614651258,1999343646885906,2003667305602825,2002500564736965,1996962829519697,
    1995563069723062,2001291344274538,2006235966900941,2002754214761155,1995088721601258,
    1993971765890951,2001455105718789,2007576804519200,2003842390729231,1994965852392188,
    1992797961998672,2000616612315588,2008601471660847,2006269937792963,1995785625788933,
    1989461655556366,1994870195702202,2005825222776756,2009702879646973,2002009727887750,
    1991329465938302,1989574718946175,1998950916643144,2009794507665564,2010931072300917,
    2001133290700907,1990075896727521,1988556875886875,1998148179523376,2010044516250348,
    2013467485750113,2005341156814632,1992672927639905,1986219934990403,1991458922654673,
    2004405917469517,2015125249326069,2015513291644270,2005170467213884],
   [1991343002347084,1983591733789544,1987324095929109,2000501042593557,2015227826955345,
    2022727998245437,2018437000839578,2004364465566201,1987780393187550,1977333636518905,
    1978811268642284,1992559722152267,2013503855119367,2033429978595586,2044338617968563,
    2041468928040268,2024958495777960,1999753038685708,1974022642607514,1956764531406227,
    1955394787086409,1973987617471582,2012519195615777,2067141409113520,2131249762193460,
    2196969852892139,2256670568103012,2304189779401254,2335587279804494,2349378284747428,
    2346316273027510,2328866548377231,2300536284365779,2265210227848881,2226598911689114,
    2187855283552423,2151369881189119,2118721895448700,2090745644435745,2067667125270776,
    2049269589013519,2035056482144640,2024391252703304,2016604009141155,2011063371889086,
    2007217445236740,2004610716737614,2002884381821498,2001766826370369,2001059506130006,
    2000621809057607,2000357030311246,2000200486398977,2000110060671783,2000059046128767,
    2000030947513992,2000015842543385,2000007919769028,2000003865919793,2000001842710315,
    2000000857807581,2000000390100391,2000000173384183,2000000075362841],
   [2000000032060463,2000000013362367,2000000005462867,2000000002193726,2000000000866621,
    2000000000337324,2000000000129566,2000000000049171,2000000000018453,2000000000006846,
    2000000000002507,2000000000000900,2000000000000313,2000000000000102,2000000000000029,
    2000000000000007,2000000000000001,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_11 : List ℕ := pNatCat
  [
   [1999967956336429,1999965991163399,1999985922331544,1999955653203723,1999949624154766,
    2000137069780598,2000020424638930,1999797090560631,2000007096679151,1999986498160343,
    2000012859817976,1999953097796111,1999805187294255,2000204463018834,1999791004607790,
    1999893600720788,1999943595574345,1999921183530145,1999946867964433,1999985341545783,
    2000070672528226,1999917073986193,2000105751883517,2000064428808972,2000059227283056,
    1999898690345736,1999944557595829,2000089415133971,2000030352764150,2000000161506852,
    2000009397640848,2000064630969520,2000004111969298,1999963099447173,1999887015138142,
    1999968763120990,2000015058831263,1999925049355838,2000103216208703,2000166309567653,
    2000068740096785,2000047035517762,1999935271293582,2000058697223500,2000064021150961,
    1999887154155195,1999867477302861,1999967654633158,1999956673677180,1999988711007993,
    2000102325339855,2000038949941174,2000144839727923,2000055771431009,2000030303018277,
    1999984452485249,2000079763574915,1999883968208329,1999953952391892,1999806226818143,
    1999987754597635,1999954836684503,2000193641977459,1999988824363650],
   [2000020137627856,2000061888657355,2000041615695505,2000078042362632,1999945821276125,
    2000026509314469,1999964193969776,2000019363299136,2000006504309413,2000068320923175,
    1999777057325847,2000017886549261,1999970014000783,2000095700336114,2000009347394053,
    2000036828578513,1999893374646621,2000187402139727,1999882882803195,2000150984787222,
    2000217837754721,1999922357836115,2000296898805472,1999928995091674,2000199344111263,
    1999992374855617,2000067777181366,2000040443511278,2000086992409332,2000097791013842,
    1999950812228453,2000060499134608,1999915717075695,2000070753190907,1999941110280050,
    1999880952497653,2000064204376156,1999851293261395,1999970101325320,2000116734035196,
    1999954046970550,2000070922039192,2000025462175459,1999914786924963,1999860891024635,
    1999986422329427,2000002937594843,2000107293459839,2000146016813758,2000023419165202,
    1999920257237378,2000015285172745,1999897628456910,2000043298022413,1999938438504004,
    2000000356140453,2000064807289527,2000096252141185,1999876635668250,2000052552242611,
    2000001886606272,1999770448237299,2000087283267099,1999870168282046],
   [1999951343599419,1999963229311645,2000126143784880,2000013177270678,2000088410683123,
    1999937689870375,1999961549536388,1999995330058566,2000169666565930,1999861530182285,
    2000001613395768,2000055293793328,2000110375179798,2000065704092779,1999827288025922,
    2000146596363448,1999934778697608,1999993821324243,2000003101547753,1999918253942693,
    1999937114204790,1999994785148537,2000133711717199,1999721597761731,2000026936123040,
    1999886747032029,2000274185919810,1999768754403323,1999989320305074,2000214455560079,
    1999750868152791,2000294709335310,1999785760764861,2000044063106462,2000063791681357,
    1999978602596741,2000143056379561,1999712424585302,2000368425584701,1999869280262264,
    2000095222273162,2000054764075588,2000022853158998,1999930408951367,2000389430528487,
    1999626650802111,2000693276507440,1999596735822926,2000265655661681,2000161160776930,
    2000147105025233,1999879144159985,2000295279493511,2000017052181526,1999982153608860,
    2000339297398918,1999824438305375,2000160807415653,2000090969769803,1999686261888767,
    2000393630191744,1999453283072694,2000444618947429,1999550105972893],
   [2000254052549952,1999734729060248,2000044564220063,1999699926525207,1999812741128809,
    2000400530278420,1999335668999964,2000646974960342,1999356138295150,2000113633064319,
    2000212389863247,1999202519345329,2000601932617520,1999068092184047,2000276938881749,
    2000126162849050,1999134016037950,2000957761204015,1999413573674272,2000042845809210,
    2000186428518921,1999208608953367,2000892040352269,1999271356212335,1999547401038737,
    2000760872612843,1998965535592134,2000188683275437,2000308815165637,1999172600040998,
    2000213378502246,2000006188401060,2000036882677958,2000128244123449,1999834945595379,
    2000456318600959,1999804821684569,1999828165753264,2000437532405343,1999630058353842,
    1999933922416276,2000055345874240,1999689424809943,2000386171636156,1999786136522015,
    1999644651422364,2000411834201547,1999711138662469,2000061551991872,2000154953261334,
    1999154393390647,2000499693238746,2000396601415030,1998813599794083,2000512047782603,
    2000451848689497,1998838436848072,2000837553565777,2000552972275670,1998482691309602,
    2000603423298256,2000867204054281,1998926644489690,2000533394084047],
   [2000443518214390,1998626043603241,2000658556457421,2000968307982375,1998819539147010,
    2000209448690708,2000495308882901,1998806134767012,2000958819069182,2001175661042623,
    1997682580643570,1999634915776489,2002558319083215,1999254805276217,1998434138238339,
    2001582024562269,2000131803356622,1998430680298805,2001011744916062,2000729771400235,
    1998516924466149,2000243228886333,2000904416848767,1998895804355245,2000193547399592,
    2001390302237690,1998652926328007,1998974402393330,2002209681512548,2000377836665626,
    1997661654217221,2000405460083476,2001744372525664,1998814253613595,1999242418412773,
    2001748233324304,1999633909400159,1997769284598399,2000844974019376,2001917087212517,
    1998852267311821,1998814664216635,2001161803155043,1999947970724838,1998415502791405,
    2000601953066586,2001365509209018,1998794942318724,1999016628794880,2001884305247848,
    2001108570775417,1998538442141660,1999795451058477,2001553890040619,1999423066109812,
    1998204840736901,2001074051754479,2001902333420992,1998397031396593,1997661002040910,
    2001521112353441,2002387081444961,1998548103104586,1997540825469458],
   [2001125798276053,2002275845566075,1999194917997103,1998117553327628,2000731269162044,
    2001629256090005,1999335836116722,1998539958780578,2000531294726998,2001286692735274,
    1999681520999874,1999025680239252,2000092248933841,2000201889755771,1999303475113391,
    1999987004476499,2001520062350483,2000605465278278,1998152659320037,1998553757269105,
    2001600809440769,2001995208823074,1998575509637875,1997163668419627,2000920768114343,
    2004164162712424,2001054618730419,1995673948053889,1996454516317878,2002815395326704,
    2005211464368539,1999457793332157,1993667019533003,1996714763617854,2004947824967520,
    2006877734863277,1999447520977103,1992671545507255,1995966602909948,2005144842702207,
    2007905389853418,2000282948631584,1992037374269799,1994051493302904,2004296546238592,
    2010237319785846,2004320966687365,1993194079503307,1989714764188252,1997818146859448,
    2008127385506646,2008857233266020,1999038746348372,1989358806787501,1990365386864478,
    2001282062945221,2011063743399584,2009881914100702,1998883261930102,1988754266211498,
    1989219362509536,1999979386538619,2011324055971600,2013146517006354],
   [2003791291535762,1991161084052067,1985793048975478,1992223915834950,2005638600588779,
    2015916513036986,2015373544798079,2004228471424378,1990151581747670,1982768983724447,
    1987250477494017,2001178390655988,2016306097588124,2023657330335268,2018687539543387,
    2003648895948110,1986206109449178,1975414366377523,1977301941650546,1992149398651381,
    2014482177687806,2035481497736666,2046579838601789,2042737074982122,2024245252888290,
    1996612408269715,1968796804039972,1950548329637949,1949756900662972,1970545197025369,
    2012500373272204,2071062097807854,2138786441123595,2207046118684358,2267713621995912,
    2314472662587477,2343563246065010,2353932651140477,2346896437283737,2325487921307273,
    2293689634769175,2255709884159238,2215412553805269,2175948717510561,2139588626722732,
    2107719150152513,2080955606272549,2059315166108430,2042406928871461,2029606581265702,
    2020197244075677,2013469933093292,2008785584234013,2005605524770130,2003499121958522,
    2002137016789082,2001276819907148,2000746201979886,2000426475743723,2000238304735111,
    2000130152561577,2000069460257649,2000036213779338,2000018440396307],
   [2000009169624189,2000004452147634,2000002110603515,2000000976967302,2000000441617239,
    2000000194986480,2000000084120780,2000000035476635,2000000014634494,2000000005909117,
    2000000002337475,2000000000906716,2000000000345267,2000000000129201,2000000000047560,
    2000000000017230,2000000000006142,2000000000002150,2000000000000735,2000000000000242,
    2000000000000073,2000000000000019,2000000000000003,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_12 : List ℕ := pNatCat
  [
   [1999989068810883,1999972118758439,1999953654912759,2000036041221435,1999982730711460,
    1999814116709495,2000064527386484,2000131060228196,1999949070299780,2000091829510942,
    1999719960800848,2000068792731040,2000081628560910,1999876658189826,1999942432788847,
    1999979697829684,2000063534484241,1999866713155370,1999993046546825,1999917038346123,
    1999887355328267,1999900509239260,1999937758170484,2000027681396687,1999929219350198,
    1999928501593238,2000029583116016,2000141378299555,2000044149842066,1999971142053567,
    1999983931048903,1999969717119366,2000065675983693,1999995617148855,1999926304220223,
    2000111868111461,2000048823892475,2000008814208348,2000008719389474,1999971150034252,
    1999988390107215,1999941291898028,1999862867567797,1999929766728171,2000182358571054,
    2000051514810005,2000059777168263,2000017628723822,2000101058754331,2000011326285439,
    2000131633033734,1999892637492461,2000011856096306,1999878474757684,1999979308784358,
    1999852093351254,2000003824345878,2000062256785463,2000016583291337,2000143319335609,
    2000010050632718,2000072518855118,2000047574455677,2000139371465431],
   [1999963119019528,1999952511431216,1999754786923328,2000035479150139,1999902880669052,
    2000024446009912,2000000360622951,2000089561604562,1999903911237659,2000195558171190,
    2000028949919067,1999990484455953,2000127233872589,1999724976764493,2000283235872694,
    1999951951835744,2000016841493969,1999963091272599,1999917928400545,1999968198082380,
    1999943703933939,2000084823009966,1999960325289289,2000073902057318,1999936934424794,
    1999972447713106,2000091693885522,1999969249958796,2000129721997155,2000071225364125,
    2000045289792689,2000255076089356,2000009599253367,2000034027614060,2000120125129600,
    2000063259253908,2000031274764307,2000137045743939,2000039989482426,2000003476919865,
    2000039079015292,2000073102907534,1999913967384924,2000073138548614,1999917051262886,
    1999945341325936,1999924613701049,1999952724108575,1999955609782874,2000096596846499,
    2000086997533987,1999952388892965,2000088719207561,1999690759987710,2000001911401537,
    2000050312848965,2000018822918909,2000011414740214,2000175004448977,1999963348311668,
    2000015803817665,1999959889625084,2000011215544837,1999860345240439],
   [2000059886246845,2000029230680469,1999964325574390,2000144663018430,1999882034423334,
    2000070338587807,1999956904888170,2000000070223003,1999905622720320,1999741183326043,
    2000087972063586,2000027599310807,2000082790635117,1999789482537529,2000243523682857,
    1999894364244685,2000093184164823,1999990644994021,1999878790933578,2000160472862828,
    1999773420065785,2000389714245566,1999834132368227,1999877076208929,2000304921773135,
    1999868943336393,2000162629460130,1999695883390285,2000210682854422,1999871000501514,
    2000087686259848,1999917490478538,1999976338229646,1999728818756854,2000465990934477,
    1999385144876645,2000405323505822,1999710764725064,2000137079759640,2000065079692577,
    1999884918005488,1999984326073393,2000155227612072,1999920118657230,1999902909765747,
    2000282910607320,1999769791878757,1999903850171773,2000469286867947,1999538944223070,
    2000538697956551,1999505313122683,2000427232993044,1999820561728730,2000179366261624,
    2000041855082592,1999978998867619,2000308997856667,1999744741502217,2000628963794165,
    1999499456313104,2000576973543036,1999955752176534,1999727781595393],
   [2000841168591244,1999302432257323,2000692876019572,1999860680280574,1999819634221959,
    2000726835391503,1999085261129573,2000609697482829,1999806198042814,1999636403754715,
    2000843375208929,1999045263514972,2000263554006876,2000079838334055,1999337799165116,
    2000664022848765,1999261836443662,2000084545159735,2000604131796600,1998994299198223,
    2000432315130670,2000210593398981,1999246434706311,2000154506573752,1999748587862915,
    1999804983911312,1999994777222125,1999875888302658,2000167715132444,1999592201371941,
    2000064091770318,2000394646232134,1999414122240387,1999997732898710,2000075300079964,
    1999560319423272,2000183497953690,1999714885223794,1999729908431601,2000194718053991,
    1999363635793101,2000044886547713,2000402544961021,1999401372133674,2000361167287367,
    2000250135573434,1999395816209250,2000874184508394,2000017202724389,1998839725689999,
    2001017963958513,2000228480563695,1998682563168164,2000844254965095,2000217498566039,
    1998781768113524,2000976973739478,2000288775591270,1998600566671998,2000754683178187,
    2000465412119304,1998836598459967,2000605577957341,2000161783059832],
   [1998683890501541,2000898188870713,2000655774341892,1998530229752184,2000484543527677,
    2000732308503629,1998542274808193,2000755895181739,2001565271838575,1997920776615727,
    1999236211654699,2002539253725741,1999651228164110,1998076823957065,2001088209398310,
    2000582432004212,1998873483392696,2000752294345841,2000521065342544,1998527072278547,
    2000276611725635,2001142008358552,1998911169077409,1999837367292558,2001521404974145,
    1999054962417149,1998697069082567,2001908131123828,2000683104261015,1997630858205853,
    2000047044938224,2002077294179701,1999124441219298,1998596124090003,2001370218681525,
    2000361248742655,1998373436152029,2000690960106516,2001711077337782,1998682939630225,
    1998554820459090,2001492334393084,2000840419144163,1998706406600491,2000085559963099,
    2001005091877697,1998844206487578,1998963841543082,2001633882060463,2000809064139745,
    1998155096550227,1999524109788739,2001696699144151,1999729754220620,1998114288087083,
    2000508638021282,2001445344277947,1998732432149688,1998675513111027,2002123544441542,
    2001955244794966,1998102075789815,1998172300456603,2001982998734898],
   [2001948263543825,1998250985225316,1998058603022979,2001303433427316,2001550907786157,
    1998804662735087,1998611499204513,2000890489224150,2000954298099304,1999074453875006,
    1999213860636836,2000874876282605,2000675413266256,1999314112306446,1999634253512561,
    2000638024460789,1999945477210814,1999125537772421,2000456637963518,2001597025176891,
    1999661396052793,1997503827560905,1999322982253029,2002587050906253,2001613385049729,
    1997668245050079,1997553443988543,2001959934901964,2003510357273272,1998899856832412,
    1995190542987237,1998903745706101,2004973649659459,2003931845234445,1996795932486995,
    1994211353721416,2000448048725794,2006495476216485,2003099014518127,1994610136782233,
    1993112967917741,2001143102354875,2007806862786071,2003854189725642,1994554778765337,
    1992597920761305,2000903254809147,2008618659791762,2005419820271898,1995046071600369,
    1990597227948787,1997977872321510,2008516656200005,2009587738366225,1999789026829013,
    1990443194897487,1992220948481724,2002947406107771,2010351313518518,2005953698824657,
    1994291657520775,1987772648534067,1993389444378885,2005578398617535],
   [2012164848753032,2006658056864385,1994425229807041,1987198108928532,1991872109674749,
    2004327153297637,2013486654650295,2011280300628755,1999479411359648,1987894652917281,
    1986092643804348,1995776380047318,2009715062608476,2017495579300559,2013278698909351,
    1999825383252105,1986313444477583,1981969014685484,1990055962300448,2005992507559492,
    2020360097406697,2024568557474354,2015708959406708,1998023843139167,1980550540147058,
    1972493628230437,1978779574521711,1997831796503854,2022335606834467,2042377191877237,
    2049454462589919,2039730894435676,2015425760944537,1984066449508839,1956098315245124,
    1941799749516437,1948506929672084,1978888537927711,2030582282589551,2097077517241992,
    2169423518382443,2238216857578607,2295365669998176,2335290262389422,2355426541120534,
    2356085815880510,2339849678052951,2310728557997254,2273297621281786,2231967417976528,
    2190475037228312,2151615126835632,2117181281645438,2088061078428526,2064420492150888,
    2045920239809928,2031921401188997,2021654754104585,2014343532180906,2009280549350912,
    2005867284044922,2003625174755053,2002189210780863,2001292149557089],
   [2000745370513677,2000420153998468,2000231391119919,2000124480529222,2000065400911680,
    2000033551155571,2000016803281746,2000008214439998,2000003919313189,2000001824993051,
    2000000829327558,2000000367811466,2000000159223980,2000000067291062,2000000027770778,
    2000000011195753,2000000004411072,2000000001699375,2000000000640549,2000000000236383,
    2000000000085459,2000000000030283,2000000000010520,2000000000003578,2000000000001188,
    2000000000000380,2000000000000114,2000000000000030,2000000000000006,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_13 : List ℕ := pNatCat
  [
   [1999992970035715,2000012019402688,1999979174572990,1999891931143650,2000052981800385,
    2000131284032909,1999759653152606,2000043891632201,1999887179670331,1999973020440488,
    2000224283657703,2000004240368901,1999929538448093,1999855668986831,2000085300410608,
    2000008352689591,1999912227170560,1999971044422266,1999963777462226,2000006774829272,
    1999954266442054,1999978163862769,1999996311936337,1999970590317451,1999877748185886,
    1999846710895555,1999995313846261,1999983573806806,1999894331272611,1999946462295689,
    1999884536140002,2000034810908773,2000136772512787,2000005311812405,1999988097748669,
    2000021386116114,2000043888435618,1999963055995639,2000035733545521,1999897821113376,
    2000070063301207,2000050826877128,2000056778077819,1999893792091404,2000167059810443,
    2000002901535102,2000035898895860,1999854806143680,1999904056925265,1999942075160281,
    1999995160603292,2000115548216440,1999938608467166,2000090116428207,2000048157526314,
    2000105691966000,2000008148539384,2000141601666844,1999941020122956,2000088722038597,
    1999875563610909,1999978598251553,1999848730138001,1999953825699021],
   [1999945091201420,2000144331356542,1999989977385625,1999889486051888,2000279500841197,
    1999869765575386,2000315161098955,2000003417369837,1999965153495171,2000024060434752,
    1999809525946869,1999957249074449,1999966518195555,2000019053804128,1999857359255212,
    2000013960382210,2000095441172336,2000037959465418,2000125686604613,1999947833178523,
    1999993676447033,2000082314002085,1999939306411344,2000146776746138,2000016549935099,
    1999953341081882,2000000702517368,1999918042158958,1999906937885860,2000099407242794,
    1999982701856167,1999958400972697,1999983522132395,2000093131339952,1999883264647095,
    2000044865561058,2000016125487291,2000010196650257,2000102233172631,2000128666304228,
    2000103662834618,2000020846541195,2000189967794296,1999926335125707,2000212612265291,
    2000025078905723,2000054708741128,2000110985423535,2000066069104296,1999944166920621,
    2000171875287202,1999963550727509,2000007062623516,2000041653005183,2000010231588396,
    1999834450830517,1999823451184267,2000125296096109,1999910250970357,2000158564310118,
    2000041229750896,1999925035456685,1999997434654701,1999821678666499],
   [2000059305711374,1999852522211398,2000154132464657,1999939988727936,2000176086080529,
    1999942996391502,2000097433078661,2000027753048088,1999686515881154,2000276065219207,
    1999848788291095,2000091990286171,1999891419774829,1999934325647018,2000409018581770,
    1999672459668185,2000242172689973,1999768326000398,1999983484719761,1999842010867779,
    2000156378596942,1999768683309294,2000092970575171,1999751529697693,2000582515900260,
    1999470997897196,2000327191209349,1999840411165889,1999976306121444,2000213049278950,
    1999841608256552,1999950015671494,2000126798930765,2000063224729167,2000010355407047,
    2000048189249194,1999963964907657,1999833619199147,2000562196236369,1999239801856212,
    2000581274633884,1999691245271792,2000062209205731,1999958821060026,1999884676515052,
    2000117070166575,1999630877699988,2000410148549923,1999580439352739,2000387344731093,
    1999642099407227,2000069666040001,2000378843766446,1999363373678542,2000752725238814,
    1999354531616810,2000173897776959,2000411783118314,1999282100932421,2000818393032909,
    1999453875966682,2000155931104715,2000390837443940,1999281867130398],
   [2000880362108467,1999530955578538,1999943549175164,2000717371771594,1999277721012749,
    2000709255253684,1999984421493825,1999631866632401,2000852711689075,1999485460730236,
    2000255316229538,2000406803516343,1999418574382872,2000813857591086,2000064864845746,
    1999463929617863,2000511637383648,1999955115233613,1999856949743218,2000052943921057,
    2000044857964610,2000143403751413,1999572701034116,2000082035853926,2000136912037124,
    1999417943871862,2000258183327321,1999988535766154,1999474055069022,2000403408640734,
    1999963333582438,1999783491845110,2000127607083177,1999449634313670,2000081964897284,
    2000131014914833,1999206238731667,2000302011980826,2000091262867385,1999252488528810,
    2000659416121036,1999977791262771,1999187487750244,2000805575613726,1999673539821363,
    1999056174179189,2001170133996093,1999670623892923,1998620128408892,2001041602679548,
    1999927788339940,1998689401534206,2000865652986318,1999966596312546,1998940636746713,
    2001128707979090,2000170585126060,1998866063799642,2000978283255997,2000289090070666,
    1998934023910111,2000866655342416,2000109070005940,1998632357978408],
   [2001027895996228,2000628157631856,1998285845518912,2000541342452509,2001138509456642,
    1998384991840357,2000148885738844,2001720718873180,1998305042392488,1998750892784314,
    2002218084605013,2000082538581689,1998004234074636,2000605629248470,2000756985940877,
    1999117043940062,2000491898591414,2000412427157786,1998658780939020,2000424321300288,
    2001444304190634,1998824381629882,1999232526371260,2001555361102375,1999613625321320,
    1998508088630049,2001527839290755,2001057233115269,1997787219800892,1999611755875290,
    2002191930650587,1999522090273827,1998248795663468,2001101240336014,2000922951686090,
    1998611536559943,2000129799926242,2001476557242402,1999009203905767,1998705093042821,
    2001497993206523,2000844659607392,1998300280043885,1999615682377205,2001348922197937,
    1999640987555536,1999149032345093,2001197591892630,2000456904743016,1998156587504787,
    1999809815587142,2002139793312607,2000021930624001,1998073758005982,2000377747163512,
    2001505628315700,1998921834570283,1998639318781340,2001540229397812,2001148019301634,
    1998011883697003,1998919575073902,2002227544502823,2000938922567726],
   [1997333645626269,1998499051829319,2002102544136698,2001362741525023,1998350985856495,
    1999089158324418,2001691780425291,2001035572435294,1998899944147501,1999487121006597,
    2001039202839857,2000248335951470,1999000269492596,1999878531354408,2000814664813273,
    1999793592389673,1999092581210749,2000257162536430,2000711577098202,1999289345571603,
    1999088878531256,2001136143991594,2001512129354839,1998750072592264,1997622510548521,
    2000823287484263,2003210024185574,2000259030256822,1996562346831703,1998555838575287,
    2003162477613641,2002405881108538,1997072265558528,1996120058760760,2001862192446861,
    2005354189124322,2000445800300812,1994211360311106,1996458180566729,2004258252614107,
    2005880689812022,1998581428582916,1993127230641029,1997912589823552,2006298524440220,
    2006031991550843,1997034704065881,1991771279874050,1997705681982388,2006768729507372,
    2006481048524686,1997095079025630,1991284977229268,1997116006361846,2007282229264035,
    2008614123887808,1999081234379804,1990403596633990,1993383673533121,2004635211232314,
    2010827005573143,2004698883485683,1993455762142411,1990103665906807],
   [1998443818887408,2008983545072274,2009783129445025,1999602881427333,1989053959243472,
    1989160441754096,1999922581210999,2010570652933907,2010575039149622,1999936271311735,
    1988880089504185,1987928293810707,1998172100364987,2010551235193043,2014160597891375,
    2005746909213034,1992255111369892,1984813342624416,1989646190146771,2003312196275835,
    2015599149561711,2017319809917704,2006949312701925,1991504481126481,1981531088629519,
    1984020089234188,1997988012956769,2015250430423645,2025483687866899,2022269977072877,
    2006654051308068,1986501458636862,1972348195280299,1972115393913591,1987323513157008,
    2012417990180748,2037228118836998,2051240814366162,2047805595741150,2026672496242520,
    1994112023963035,1960836371634216,1938655472926229,1937066813475982,1960803458082479,
    2008904026123830,2075329761704294,2150719593577210,2224649567953950,2287763789359350,
    2333314229594899,2357895589357159,2361400333579956,2346387869739982,2317137763375651,
    2278649002441210,2235783504228391,2192664975760770,2152361190406384,2116815741641061,
    2086960675731382,2062932034981191,2044319333308640,2030398874154067],
   [2020322096701486,2013248599549730,2008426560375941,2005230549613337,2003169221444431,
    2001874635254758,2001082568013505,2000610314561311,2000335873060194,2000180411958284,
    2000094571211393,2000048371021344,2000024136412957,2000011747715067,2000005576561831,
    2000002581437428,2000001165201694,2000000512817385,2000000220060202,2000000092077093,
    2000000037568870,2000000014949570,2000000005802755,2000000002197605,2000000000812270,
    2000000000293108,2000000000103291,2000000000035557,2000000000011953,2000000000003919,
    2000000000001247,2000000000000382,2000000000000109,2000000000000027,2000000000000004,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_14 : List ℕ := pNatCat
  [
   [1999991851715157,1999981706498876,2000036752646799,2000085527188684,1999735481898475,
    2000068075777891,2000102211825770,1999908328365254,2000083988765419,1999932684741537,
    1999897452567377,1999848454020937,2000021645197063,2000195606774588,2000031958246431,
    1999949129766846,1999935813140660,2000001581049371,2000016675884821,1999971951484663,
    1999962124793517,1999951040400799,1999998139572387,1999999541774861,1999879394302438,
    2000018821270811,2000059971808025,1999955846536536,1999969940118275,1999876226105224,
    1999900790747723,1999942910736066,2000072427346854,1999834795424358,1999915005967105,
    1999869386885711,2000034890659462,1999951855993117,2000136869472792,1999914465963641,
    2000035104602914,2000090027738332,2000021820178919,1999985970689396,1999890492082315,
    2000105434333475,1999966958920995,2000048082409774,1999942969875697,2000047620644506,
    1999978338376471,2000227696922849,1999959739317248,2000012809522312,1999870114389102,
    1999965412143102,1999924354808308,1999985866444806,2000008834801621,1999923064697963,
    2000209622145852,1999793791975180,2000276659036058,2000013859205870],
   [1999954773545708,2000221878150286,1999982945949049,2000071260679203,1999919637487699,
    1999883435664796,1999902414289517,2000005972457450,1999997787895867,1999900616401157,
    2000063172314510,1999977243777459,1999959530444535,2000210284059713,2000081710953760,
    2000158889985357,2000011599574496,1999905795165924,2000023753234790,2000002981308110,
    1999860405658202,1999988192714517,1999866474606600,1999966117999017,2000020518135932,
    2000120084611835,1999961097816128,2000074791448820,2000058414232339,1999892867528657,
    2000072271121410,2000077004020605,2000124219223794,1999893596745185,2000130233497532,
    1999862082802173,2000000218041047,2000005876290836,1999946037337119,1999963187371309,
    2000089168042390,1999893416456470,2000078037875891,1999984772213004,1999887540622436,
    2000050189803420,2000002261716357,2000090044253842,1999982594758196,2000228977510588,
    2000016716496726,1999980226025181,2000272286163209,1999935721976404,2000158480448643,
    1999982584651224,2000237067957960,1999953489926570,2000099156463299,2000000346245496,
    2000033519130921,2000214053095976,1999881385747295,2000239051102275],
   [1999694945127096,1999954670866276,2000053733660913,1999709400046861,2000361463526794,
    1999772768978022,2000302491221794,1999744388132368,2000058061944718,1999947066619464,
    2000019140866590,1999603371561685,2000408431572546,1999756986728467,2000403044422508,
    1999626490848423,2000302246566538,1999934406131891,1999851774768347,2000290086776015,
    1999746045835527,1999870130726413,2000178643110579,1999994307119977,2000111777827464,
    1999914075679809,2000149640802779,1999656340477248,2000584241496733,1999241025474795,
    2000345399613837,1999784103488650,1999878596342385,2000369975352854,1999599829657198,
    2000227351989514,1999791631398712,2000447366843311,1999565218636776,2000144115927051,
    2000104989186818,1999672006789831,2000566892645094,1999391997867710,2000575958595000,
    1999832515119184,1999706328606243,2000771735969942,1999160808682254,2000553266748507,
    1999923317560280,1999607507763983,2000756283801220,1999178225630543,2000369603296135,
    2000008541339848,1999479901303477,2000765762653307,1999230988125749,2000173036604649,
    2000396097560661,1999253225736495,2000713327035126,1999734765051183],
   [1999719334643646,2000612631470446,1999353785270182,2000323311333914,2000230789135390,
    1999425487392344,2000560804450638,1999854464364821,1999756657220378,2000515603147064,
    1999714916333923,1999919477674291,2000268267784415,2000063347907412,1999997444831144,
    1999809313917500,2000482610895732,2000179586857331,1999560075905561,2000518355032050,
    2000069656704818,1999675260644843,2000612634395646,1999976818314364,1999924674235974,
    2000473031680413,1999709905643942,2000118598352746,2000240291098338,1999607164945620,
    2000506511699839,1999965837815236,1999311350445409,2000749487298725,1999893196287019,
    1999168965578833,2000687655533909,1999634979019589,1999308740550874,2001048042502434,
    1999549235539949,1999224772850188,2001195364284142,1999444322889307,1998966523569260,
    2001224813790645,1999531042033083,1998707002064949,2001059588146723,1999891258836841,
    1999018066842470,2000957951310600,1999754513886524,1999011002585759,2001097649342182,
    1999876984555295,1998793975010285,2000943169258405,2000014478943503,1998710991402213,
    2000861115566822,2000037038980394,1998309070285206,2000903458254361],
   [2000844989734326,1998167798959267,2000347016220640,2001608577051958,1998598876434630,
    1999631663660249,2001904474955202,1999061717995722,1998549156721048,2001766981782125,
    2000455586109384,1998194047944910,2000299345041254,2000852107535318,1999307400829484,
    2000330420319467,2000352231659500,1998594656640701,2000251704497680,2001611086319806,
    1998810356964920,1998656545707988,2001572136771777,2000228377801180,1998217889544720,
    2000801668759180,2001312809118688,1998212143745476,1999337850046490,2002221686770471,
    1999942796634561,1997985046105496,2000692536748005,2001284054564986,1998841802763249,
    1999675158726019,2001368954706596,1999440642330480,1998759569324019,2001228982104255,
    2000812488174268,1998306096620053,1999600275084585,2001654076683167,1999870378919902,
    1998752646362490,2000751215120838,2000702105630502,1998712446370514,1999937634938688,
    2001769545663866,1999534250599652,1997864911970066,2000634938251215,2001971764654125,
    1999141085719618,1998473852010041,2001187424988018,2000962768724202,1998324965394279,
    1999463291647596,2002209003947603,2000449095238227,1997572019388636],
   [1999594328140637,2002430972378314,2000290018095493,1997513377397081,1999549174087913,
    2002202607419344,2000541883459947,1998282599492029,1999516041687469,2001026564039439,
    1999803544048106,1998824246388129,2000125494316692,2000832272249673,1999709372349680,
    1999550453250386,2000836906910278,2000706454261126,1999287437924968,1999613723347322,
    2001072397858452,2000368913701294,1998569488850341,1999494292762185,2001782292770125,
    2000735437366466,1997612250685608,1998286191157087,2002312086355113,2002683851528703,
    1998190663870452,1996410465561078,2000800466152519,2004100919784924,2000434221956589,
    1995789069300737,1998304411575963,2004194365606626,2003439998270950,1996533558342129,
    1994462916754135,2001144862088418,2006527318010520,2002009920706777,1994166149079809,
    1994995272585087,2003488281224269,2006873597201786,1999811234015310,1992593851234037,
    1996059129896475,2005578254407223,2007575877660718,1998994732894232,1991722014440263,
    1995905434190289,2005819084750044,2007779311714724,1998855806978879,1990859548961191,
    1994599186757097,2005620125610790,2009953473476678,2001978105172939],
   [1991452489230236,1991285373170561,2001737780437662,2010332954111893,2006947906687699,
    1995647480781435,1989644764903348,1995945736622745,2007530326252860,2011424573038053,
    2003037458021701,1990979182404864,1987731436046113,1996630974271143,2008684314667892,
    2011863434759652,2002998064201711,1990604181228681,1986511172088183,1994772051182252,
    2008148138733632,2014832656271102,2008871873333175,1995121281917537,1984952086869022,
    1986840050086080,1999690282789339,2013893133624944,2018761611326383,2010412277828157,
    1994414422009384,1981750309206441,1981309528205274,1994089828891988,2012657759230663,
    2025809928395497,2025278535861169,2010478502384027,1988811545780950,1971699283229903,
    1968710519233471,1982832715504258,2009040456310936,2036546071361301,2053449549919066,
    2051652447192712,2030067810755232,1995077855241129,1958353999608118,1933072597044236,
    1929949648512246,1954351403981854,2005189923949608,2075648500588514,2155242145996283,
    2232443783789511,2297116834661682,2342214384909804,2364515310064589,2364456721513123,
    2345317388115061,2312084484379119,2270311955594543,2225190712204718],
   [2180940606209353,2140535070928561,2105700622419277,2077100283265608,2054607246167072,
    2037592310485214,2025174606447885,2016410943580909,2010419411806404,2006445681523090,
    2003886323546016,2002284224492037,2001308928333961,2000731283229025,2000398324370333,
    2000211513183109,2000109481110240,2000055231003599,2000027152053712,2000013005571451,
    2000006068682252,2000002758237544,2000001220901120,2000000526243992,2000000220854612,
    2000000090240851,2000000035896565,2000000013900905,2000000005240504,2000000001923330,
    2000000000687235,2000000000239081,2000000000080980,2000000000026698,2000000000008560,
    2000000000002664,2000000000000799,2000000000000228,2000000000000059,2000000000000012,
    2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_15 : List ℕ := pNatCat
  [
   [1999999298853214,2000015182715605,1999857629450646,2000185231920879,2000078481577871,
    1999777357823645,2000009630667827,1999989759218178,2000003857590359,2000012151228903,
    2000011014821014,2000096769937865,1999933200837043,1999813168825604,1999878863453851,
    2000025023498609,2000120339850684,2000062554420668,1999986403562003,1999988402204466,
    1999941519366143,2000040096728358,2000025685203349,1999888205415865,2000014767707458,
    1999998000463535,1999999676302082,1999881919976162,2000031748417327,1999887169521500,
    2000074353324569,2000010895656570,2000062367757660,1999803290667353,1999956282223859,
    1999959256161477,1999937181355731,2000043843908943,1999860317229583,1999916511813430,
    1999812555363238,2000060730552682,1999955203155658,2000001755457119,1999896931632006,
    2000160079881213,1999971432867667,2000097605763039,1999968470966344,1999965009447197,
    2000004814144308,2000017744793466,2000109600494661,1999800700513866,2000147422457567,
    1999823691606419,2000185129816509,2000148958034033,1999880381591335,2000193055739719,
    1999888352182123,1999903490934901,1999991795892990,1999958803051169],
   [1999941102222259,1999953210037336,2000040130050821,1999991769399371,2000061001708680,
    2000074038205729,1999908089144108,2000199322404084,2000116285319715,2000036563079663,
    2000057646850104,1999954262196588,1999895778668993,2000004389350301,1999861296935647,
    2000053153384756,1999974948187180,1999910156700136,1999890153503447,2000071952152153,
    2000103386289722,2000062364805767,2000216260038330,1999951515698546,2000076054089815,
    1999997324170822,2000116526989383,1999815252679809,1999992155283646,1999943755734873,
    1999849993338221,1999944342336148,2000115284230550,1999957600345529,2000101441109286,
    2000005773727978,1999894879209637,2000129868549800,1999976981598813,2000103088823890,
    2000031020063118,2000067874398537,1999988819081070,1999915628312613,2000184327013224,
    1999729862276358,2000105003413887,1999952150559819,2000036623204587,1999932012664321,
    2000062057230938,2000027305543214,1999784850314843,2000161126945436,1999836713236914,
    2000178383414611,1999972568647336,1999955451010347,2000381129926757,1999703425088467,
    2000427471087093,1999789647735987,2000238404763793,2000016791771951],
   [2000226863714478,1999910776038287,2000233897447771,1999694960691231,2000526805380080,
    1999683191630736,2000366612877325,1999999220758750,1999975526118461,1999948366528492,
    1999705387826059,2000245725513949,1999901867442882,1999790316344427,2000350047558058,
    1999848925282065,2000151722758318,1999759197152333,2000262260001981,1999339040958514,
    2000557123380333,1999694818783744,2000060378867612,2000247946274106,1999520576195630,
    2000605161822214,1999730960688288,2000173992230167,1999729507317999,2000114492108560,
    1999964709254904,1999860217676524,2000455806527302,1999328125490477,2000633940018213,
    1999896603295746,1999823075226635,2000365645933601,1999217145114991,2000722216274225,
    1999566692578950,1999719630965884,2000646924358889,1999165188050729,2000629210521111,
    1999884080573389,1999651804287300,2000671526676631,1999239520438279,2000454143389952,
    2000078635461645,1999447372607591,2000775404915535,1999444021323018,2000151826597493,
    2000517291347853,1999222337937319,2000552651093215,1999970307034719,1999659969046026,
    2000610253931998,1999482242044695,2000053109333227,2000336696588158],
   [1999437582189142,2000323825274482,1999993065512228,1999588842287986,2000293406201599,
    1999889248526567,1999916854727540,2000097523016622,1999981996619263,2000051377550051,
    1999723799372801,2000271165153185,2000201225990389,1999360178714189,2000384837825083,
    2000344054999021,1999406516844487,2000325554061674,2000123832882067,1999684203062506,
    2000417276768397,1999803125970252,1999887472330076,2000449882380167,1999630977986793,
    2000274317808170,2000463550622514,1999353128224983,2000495067734011,2000422517128676,
    1999137215637229,2000734175937293,2000574408294008,1999106130814064,2000724762558779,
    2000370758481444,1999041893911488,2000944149971969,2000302729345283,1998734256545146,
    2000964478684349,2000525344651693,1998646218602004,2000729135536550,2000524980844746,
    1998554960658413,2000452758660120,2000614618063746,1998848389580654,2000449735217080,
    2000510501617789,1998839084897360,2000575813032480,2000648592028310,1998505175471042,
    2000170321732593,2000849869916038,1998626504837142,2000042474474204,2001126908794245,
    1998605045371760,1999707106651475,2001678163905915,1998892199127337],
   [1998822820881056,2001774134378098,1999810361645770,1998256015393759,2001156898993942,
    2000502600704155,1998033338314475,2000336008424056,2001258565550728,1998552964851072,
    1999346130017777,2001278710906570,1999753204176840,1999535218967647,2000748977586893,
    1999407971852983,1999494702313166,2001624367472459,1999882742872305,1997931837101133,
    2000825344866294,2001648777700411,1998478541388804,1999217991887030,2001723803101282,
    1999574125595255,1998396896961317,2001335946220255,2000945122418742,1997969143080819,
    1999622522463446,2001876726258840,1999540543427000,1998500899650801,2000841103178409,
    2000519767091186,1998789546601855,2000377724969185,2001248566492672,1998891061735627,
    1998982803534652,2001510431213040,2000530145622102,1998391731647178,2000061312749732,
    2001424667616837,1999398732499817,1999067309831094,2001106805394318,2000244774451198,
    1998337869081818,2000269118006365,2001958066943942,1999306659280847,1997978172619871,
    2000985674458655,2001848530007914,1998886690067389,1998690556414304,2001362555518118,
    2000635564863109,1998131716481904,1999731023985348,2002245347520403],
   [2000076032560515,1997506898823053,1999887210035344,2002424214405751,2000141150408584,
    1997848818460069,1999951869029088,2001926292859588,2000087935050200,1998468040452133,
    1999886019878618,2000902771591715,1999758330507066,1999448944150649,2000625826190543,
    2000444929837638,1999139649411580,1999514226872057,2000673980269156,1999893989955230,
    1998731758554888,1999968234486451,2001419500043910,2000040929671726,1998520285926008,
    2000315458988846,2002259686698624,2000135679566038,1997394982854569,1999450657537268,
    2003090345604143,2001456156841069,1996776984269184,1997282156780542,2002560663879082,
    2003541400622447,1998206620843367,1995653132050241,2000598956555574,2004803062055868,
    2000787592985009,1994942016190154,1997337734067588,2004686543452726,2005031511928453,
    1997178028636888,1993252688088262,1999689068355662,2006756271959623,2003463841582134,
    1994693971410653,1993887183394723,2002495658670796,2007614289840483,2001326414160941,
    1992640374048368,1994335962380249,2004268080843049,2008372199454405,2000763081060586,
    1992069850565913,1994486002702267,2004802138418820,2008840347512537],
   [2000793973099762,1991087533704029,1992550935507691,2003600096836380,2010318576675476,
    2004240944637918,1992901396459906,1990261605503311,1999529965523620,2009512897141641,
    2008298771701738,1997344367132735,1989508451953208,1994017518260247,2006021699245100,
    2012213079105691,2005581077601556,1992895894960277,1987302806390774,1994517169242854,
    2007143189691066,2012424984808244,2005005431104910,1991975565120883,1985817439156758,
    1992565196402260,2006369458130470,2014994664334767,2010736310823575,1996988494967151,
    1985179165510578,1985207950850315,1997505915546423,2012853390972638,2019590052489217,
    2012352516229191,1995893133296861,1981607177903588,1979634202931582,1992091869933813,
    2011744360161606,2026581124011546,2027134518058591,2012057767979614,1988917661464901,
    1970094338173205,1966286260292302,1981079920676773,2009150698246329,2038666733648636,
    2056500431934089,2053796129334480,2029591596128801,1991259756683689,1951918789534564,
    1926051874415922,1925024594564936,1953955684378869,2010711483171162,2086992722274836,
    2170860201455593,2249763559013135,2313199523071187,2354424361591429],
   [2371027348959862,2364504328127630,2339174314996554,2300840485010158,2255539105442231,
    2208597695481368,2164088697418312,2124654747005745,2091614308472497,2065232740954685,
    2045053365828910,2030211131302738,2019684529896226,2012470199705284,2007684651020521,
    2004608253983908,2002689816165375,2001528460568976,2000845604902992,2000455479167019,
    2000238857322570,2000121937901859,2000060591864244,2000029302103608,2000013788503980,
    2000006312316272,2000002810799017,2000001217181074,2000000512483754,2000000209759233,
    2000000083444351,2000000032257391,2000000012115532,2000000004420423,2000000001566466,
    2000000000539062,2000000000180103,2000000000058402,2000000000018368,2000000000005595,
    2000000000001645,2000000000000461,2000000000000119,2000000000000027,2000000000000004,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_5_16 : List ℕ := pNatCat
  [
   [1999959269082713,2000125171239715,1999902673230701,1999826153437489,2000187032729161,
    2000097575055939,1999955189973990,1999948867938949,1999915831909688,2000012222791503,
    1999994306288532,1999938299885979,2000012037067030,2000096577310010,2000080501934179,
    1999978921082596,1999815175887124,1999868138374715,1999971897649545,1999979115102049,
    2000147941448124,2000014685757484,2000002517537650,1999918604788705,2000127992000423,
    1999921562320599,2000018199489970,1999927509544177,2000048699235485,1999940747678205,
    2000000092415426,2000054962687318,1999817520372416,1999994247643921,1999942321123178,
    2000116856712163,1999960990268354,2000056687299521,1999863569038052,1999972040631270,
    1999849732801208,2000103598153013,1999982436008582,1999861497013209,1999926739871184,
    1999851766226853,2000059085832382,1999787171420444,2000117809590694,1999812672858467,
    2000005791552316,2000180065398811,1999876705189638,2000176501589961,1999922670154479,
    1999911196782375,2000143422778108,2000023327698381,1999958650916317,1999971401249074,
    1999990358628633,1999955576268053,1999989422741946,2000188049643386],
   [1999991413378027,2000090943167545,2000035155531710,1999908835090889,2000006302886968,
    2000031192176303,1999810314751220,2000009439261699,1999947169451676,2000030974530107,
    2000018327986367,1999962895186960,1999996980543873,2000042306606286,2000159072333836,
    1999967754814484,2000246476133575,2000015136471225,2000014738746772,1999873003973737,
    2000041662027988,1999939286643726,1999981933026766,2000009042974271,1999895359368712,
    1999792808661479,2000084633137310,2000059062460751,1999953931509690,2000217466073970,
    1999994666943845,2000109072384023,2000076620073542,2000008986722133,2000098865202931,
    1999893902302642,2000080008947840,1999668448159086,2000082689938412,1999918260462503,
    1999971797457396,2000092066955065,1999984349014929,2000022601473925,1999845624126884,
    2000255408359926,1999872301208439,2000046488652284,2000211200736829,1999797294904622,
    2000369633927981,1999619078163074,2000351964238615,1999758872122772,2000026447124782,
    1999916162068530,2000178174504174,1999753520447258,2000330865481933,1999588630638178,
    2000334647473716,1999708919615894,2000078900141977,2000057585275745],
   [1999798086193263,2000257011815057,1999992752672030,2000061216832671,2000116597799959,
    1999810982452616,2000498505668969,1999713154860191,2000357777007317,1999902266691802,
    2000410337710330,1999474779281339,2000382834440021,2000204550805403,1999721195252713,
    2000682169276257,1999486895191200,2000362561038535,1999815156247989,1999935688754951,
    1999999071942763,1999795586793567,2000249168264884,1999703485892004,2000625002902985,
    1999507874788630,1999969256744206,2000322573062370,1999324395499733,2000694123869603,
    1999458454568108,1999983337124075,2000416017395019,1999426400554483,2000859781265233,
    1999450272973710,1999875535840182,2000692668795222,1999195747607535,2000494830759702,
    1999775481158293,1999726194443650,2000735106073329,1999348679574176,2000423094672325,
    2000130491416951,1999389693752787,2000722796511545,1999490176896937,1999851867829463,
    2000467971506174,1999268174559719,2000397893355000,2000122950285105,1999506257890759,
    2000512582773648,1999728214633115,1999926368887834,2000380929651016,1999514137249286,
    2000167447309147,2000223779621202,1999739962179522,2000212916660008],
   [1999981406402821,1999956823274307,2000054396013681,1999994583941209,2000229921260118,
    1999729082852732,2000025763838573,2000391277784526,1999445841519399,2000123356610363,
    2000483204122284,1999273017569904,2000062767581992,2000400772526102,1999516062387637,
    2000172883131318,2000014291634670,1999734351607149,2000474033150504,1999672677190086,
    1999780447682660,2000619207573879,1999465125146968,1999966918330475,2000723869287224,
    1999186447224197,2000074855455884,2000906292672189,1999069739898931,2000073366485366,
    2000919275876574,1998994467461549,2000134487954697,2000974134683343,1999015238585408,
    2000307797994268,2001063878569221,1998770776616962,2000127874063823,2001340022224267,
    1999005913494541,1999932733370138,2001284895892438,1999210283810384,1999886407458916,
    2001173855616998,1999241634478207,1999807754879144,2001084397650825,1999202306202149,
    1999829181519712,2001316325452442,1999077999319519,1999272383011586,2001376466356289,
    1999368776212012,1998908104282474,2001326193673665,1999702673271741,1998627180263398,
    2001456969117710,2000393305833041,1998041641389991,2000713808542754],
   [2001172158627819,1998178750800182,1999699367923880,2001496447862250,1998920146841786,
    1999093309497715,2001430236415307,1999691774239706,1998681113624423,2000909603946051,
    2000413829473436,1998979685580521,2000369669765595,2000186249419901,1998887385897556,
    2000600525732810,2000723323388512,1998035520271242,1999454134503115,2002127810670601,
    1999524073763553,1997963396012755,2001172630830443,2001244386002622,1998472383391254,
    1999971298055437,2001610882848640,1998993232744380,1998732803512845,2001629312618680,
    2000575945636727,1998160715360490,2000072199145642,2001426970460944,1999276461181805,
    1999247104039899,2001031199279983,1999768360938428,1998721736638712,2000889311792460,
    2001001353684833,1998447239003821,1999206324570343,2001541209601567,2000103279614710,
    1998541156366234,2000492391345963,2001054423728169,1998917858433161,1999466194870955,
    2001505897745787,1999903294924371,1998174315890231,2000664788541569,2002019022509753,
    1998998535677574,1998079185087956,2001180488045791,2001486221549061,1998586856729223,
    1999026635367979,2001583938440243,2000333038085622,1998119117840746],
   [2000186470109084,2002277720412174,1999683778960894,1997577831367706,2000241207479048,
    2002225567271042,1999766145407647,1998070039119167,2000196327986310,2001471244932027,
    1999698400904416,1998903029884017,2000343640755763,2000671250267075,1999609702312318,
    1999881024790428,2000721933238273,1999828748403374,1998932408907609,2000166444050474,
    2001079836253323,1999657515500188,1998911646943242,2000685783352109,2001319381534609,
    1998990857924053,1998091542354342,2000736299014738,2001888384291246,1998886712004436,
    1997365570781359,2000913518408737,2003457410538215,1999940808823895,1996311165427937,
    1999391448647354,2004120992976018,2001939900021884,1996235768236108,1996959284738395,
    2003089505414986,2003917030496397,1997633177385897,1994973116165118,2000947524309771,
    2005747673486845,2000918166314319,1993958670290185,1996486377881399,2005000068424025,
    2005990044025678,1997568416481992,1992812506206874,1999249006237580,2006921527471588,
    2003825465888139,1994570425917572,1993384636615967,2002360205849923,2008145584442639,
    2001913722894014,1992563198937310,1993714501080013,2003870541604459],
   [2008572151678487,2001085302934717,1991920922615783,1994031265467376,2004769161368579,
    2009511918416472,2001552242107108,1991126483005126,1991841305007708,2002900209178220,
    2010270285364456,2004693640127735,1993221386229474,1990133015464200,1999240721850598,
    2009468079504181,2008464220345810,1997323145607073,1989101929443220,1993532422285862,
    2005940948521286,2012645023929234,2006151348314448,1993188511612974,1987306219992454,
    1994558250916954,2007422214380873,2012728148321239,2004943371397511,1991472992133824,
    1985281637326549,1992509012622949,2006861589478492,2015517573462949,2010640930788602,
    1996142294687624,1984187381730414,1984952072656244,1998358087796138,2014244104893857,
    2020347747909139,2011607277704799,1993854208647436,1979576559094941,1979171107987946,
    1993877881887733,2014947628799110,2029206725931689,2027201175390761,2008896121444838,
    1983785872964972,1965695774143094,1965400446121776,1985016075585292,2016838811210480,
    2046881037034795,2061152286682530,2051727177761882,2020080545353116,1976603901271038,
    1936864279349421,1916318123353424,1925494221088583,1967170503227126],
   [2036139580324529,2121218121051038,2208532995893432,2284943220615121,2340673072779570,
    2370666539082770,2374633548670365,2356100645504738,2320939291537302,2275834424024103,
    2227031112452845,2179528671728105,2136738043842216,2100513693212004,2071424298807954,
    2049127395799078,2032743364615679,2021165090552936,2013277419196850,2008087934632794,
    2004785952301620,2002751895343725,2001537836967544,2000835309087049,2000441014874778,
    2000226313629646,2000112869875593,2000054700802752,2000025756069120,2000011779964492,
    2000005232195530,2000002256250307,2000000944351681,2000000383527322,2000000151091990,
    2000000057720414,2000000021375389,2000000007670813,2000000002666543,2000000000897551,
    2000000000292396,2000000000092138,2000000000028062,2000000000008247,2000000000002331,
    2000000000000628,2000000000000157,2000000000000034,2000000000000005,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def phb_m2_r512_5 : List ℤ := uOfNatHb pb_m2_r512_5
private def pvi_m2_r512_5 : List ℤ := bDec bZ pv_m2_r512_5_0
private def pvo_m2_r512_5 : List ℤ := bDec bZ pv_m2_r512_5_16
private def pb_m2_r512_6 : List ℕ := pNatCat
  [
   [75819560048704,107060493338152,130920226967739,150940884647606,168496762302297,
    184293802824579,198752022388607,212145506726403,224664927853155,236449324250546,
    247603817829668,258210201171298,268333617498104,278026963911261,287333900403350,
    296290969223296,304929126543109,313274874223878,321351112408229,329177792808382,
    336772426873634,344150486421680,351325723324894,358310427401430,365115636524349,
    371751309352786,378226468512164,384549320183240,390727354688577,396767431645545,
    402675852488320,408458422578734,414120504678693,419667065210595,425102714461714,
    430431741675570,435658145804377,440785662561800,445817788306692,450757801200801,
    455608780011942,460373620875736,465055052280881,469655648503217,474177841680781,
    478623932694520,482996100996216,487296413505758,491526832683473,495689223869312,
    499785361968826,503816937555787,507785562452598,511692774842223,515540043958939,
    519328774399658,523060310092752,526735937957159,530356891280853,533924352844642,
    537439457814406,540903296422478,544316916456716,547681325573888],
   [550997493452348,554266353797468,557488806211995,560665717942317,563797925510576,
    566886236241662,569931429693253,572934258996350,575895452113089,578815713017984,
    581695722808262,584536140748425,587337605253760,590100734817115,592826128882904,
    595514368671983,598166017960729,600781623817425,603361717298757,605906814109067,
    608417415224763,610894007486117,613337064158520,615747045465109,618124399092530,
    620469560671477,622782954233553,625064992645841,627316078024525,629536602128777,
    631726946736060,633887483999900,636018576791131,638120579023542,640193835964773,
    642238684533299,644255453582236,646244464170685,648206029823288,650140456778599,
    652048044226883,653929084537854,655783863478906,657612660424289,659415748555709,
    661193395054759,662945861287606,664673402982293,666376270399031,668054708493807,
    669708957075627,671339250957707,672945820102877,674528889763482,676088680616024,
    677625408890791,679139286496693,680630521141529,682099316447878,683545872064818,
    684970383775646,686373043601777,687754039902989,689113557474164],
   [690451777638676,691768878338574,693065034221679,694340416725735,695595194159731,
    696829531782512,698043591878778,699237533832589,700411514198472,701565686770217,
    702700202647466,703815210300160,704910855630960,705987282035677,707044630461831,
    708083039465374,709102645265664,710103581798757,711085980769064,712049971699452,
    712995681979834,713923236914299,714832759766849,715724371805784,716598192346778,
    717454338794701,718292926684228,719114069719279,719917879811320,720704467116583,
    721473940072220,722226405431447,722961968297696,723680732157821,724382798914378,
    725068268917016,725737240993011,726389812476957,727026079239665,727646135716267,
    728250074933571,728837988536687,729409966814937,729966098727083,730506471925890,
    731031172782040,731540286407420,732033896677816,732512086254997,732974936608252,
    733422528035355,733854939683002,734272249566727,734674534590308,735061870564681,
    735434332226382,735791993255521,736134926293302,736463202959117,736776893867196,
    737076068642864,737360795938375,737631143448371,737887177924952],
   [738128965192373,738356570161388,738570056843235,738769488363287,738954926974362,
    739126434069713,739284070195703,739427895064167,739557967564480,739674345775328,
    739777086976197,739866247658577,739941883536904,740004049559229,740052799917633,
    740088188058389,740110266691873,740119087802242,740114702656870,740097161815557,
    740066515139516,740022811800133,739966100287522,739896428418860,739813843346526,
    739718391566032,739610118923760,739489070624506,739355291238838,739208824710262,
    739049714362215,738878002904874,738693732441798,738496944476391,738287679918203,
    738065979089067,737831881729071,737585427002373,737326653502865,737055599259676,
    736772301742531,736476797866959,736169123999360,735849315961921,735517409037401,
    735173437973772,734817436988722,734449439774027,734069479499792,733677588818556,
    733273799869273,732858144281161,732430653177432,731991357178891,731540286407420,
    731077470489333,730602938558614,730116719260044,729618840752196,729109330710330,
    728588216329159,728055524325510,727511280940871,726955511943819],
   [726388242632346,725809497836070,725219301918333,724617678778198,724004651852329,
    723380244116766,722744478088600,722097375827526,721438958937300,720769248567090,
    720088265412715,719396029717779,718692561274708,717977879425664,717252003063374,
    716514950631835,715766740126925,715007389096903,714236914642804,713455333418727,
    712662661632017,711858915043337,711044108966641,710218258269024,709381377370479,
    708533480243535,707674580412789,706804690954322,705923824495013,705031993211731,
    704129208830418,703215482625060,702290825416534,701355247571349,700408759000262,
    699451369156776,698483087035519,697503921170499,696513879633238,695512970030777,
    694501199503558,693478574723175,692445101889994,691400786730641,690345634495357,
    689279649955215,688202837399197,687115200631130,686016742966478,684907467228993,
    683787375747205,682656470350775,681514752366679,680362222615245,679198881406026,
    678024728533504,676839763272636,675643984374220,674437390060090,673219978018135,
    671991745397132,670752688801393,669502804285223,668242087347181],
   [666970532924141,665688135385151,664394888525080,663090785558049,661775819110645,
    660449981214909,659113263301090,657765656190163,656407150086103,655037734567911,
    653657398581378,652266130430590,650863917769159,649450747591180,648026606221890,
    646591479308046,645145351807995,643688207981424,642220031378802,640740804830483,
    639250510435469,637749129549830,636236642774748,634713029944207,633178270112279,
    631632341540036,630075221682031,628506887172376,626927313810376,625336476545712,
    623734349463169,622120905766877,620496117764062,618859956848282,617212393482138,
    615553397179435,613882936486784,612200978964607,610507491167553,608802438624274,
    607085785816556,605357496157787,603617531970715,601865854464495,600102423710985,
    598327198620271,596540136915378,594741195106161,592930328462323,591107490985534,
    589272635380623,587425713025800,585566673941868,583695466760399,581812038690810,
    579916335486326,578008301408753,576087879192040,574155010004558,572209633410068,
    570251687327296,568281107988080,566297829894021,564301785771563],
   [562292906525460,560271121190531,558236356881659,556188538741929,554127589888842,
    552053431358510,549965982047747,547865158653958,545750875612720,543623045032964,
    541481576629625,539326377653667,537157352819331,534974404228497,532777431292011,
    530566330647830,528340996075828,526101318409102,523847185441603,521578481831906,
    519295089002921,516996885037339,514683744568596,512355538667112,510012134721570,
    507653396314952,505279183095069,502889350639277,500483750313055,498062229122122,
    495624629557710,493170789434633,490700541721706,488213714364115,485710130097223,
    483189606251357,480651954546987,478096980879770,475524485094799,472934260749421,
    470326094863904,467699767659185,465055052280881,462391714508683,459709512450165,
    457008196218008,454287507589501,451547179647150,448786936399084,446006492377877,
    443205552216257,440383810198070,437540949782727,434676643101186,431790550421384,
    428882319580817,425951585383802,422997968960671,420021077085965,417020501452355,
    413995817896759,410946585574754,407872346079010,404772622497055],
   [401646918403201,398494716778935,395315478855492,392108642871657,388873622739108,
    385609806606753,382316555314606,378993200726637,375639043930842,372253353293412,
    368835362352304,365384267533742,361899225673151,358379351319691,354823713800887,
    351231334020779,347601180961464,343932167853800,340223147978268,336472910051438,
    332680173147022,328843581092875,324961696276408,321032992780322,317055848758118,
    313028537944000,308949220174074,304815930774553,300626568647083,296378882850399,
    292070457439891,287698694280673,283260793493236,278753731120828,274174233520759,
    269518747872856,264783408060903,259963995008301,255055890325503,250054021837922,
    244952799186346,239746037196133,234426864051852,228987610426480,223419674505128,
    217713356173718,211857651303810,205839993733967,199645927720850,193258686498486,
    186658641806370,179822572562376,172722674304134,165325187416368,157588447911649,
    149460032675641,140872425040020,131736139342079,121928205799551,111271497719218,
    99494030474658,86137739937473,70309073488452,49700140902155]]
private def pv_m2_r512_6_0 : List ℕ := pNatCat
  [
   [1999959269082713,2000125171239715,2000097326769299,2000173846562511,1999812967270839,
    1999902424944061,1999955189973990,2000051132061051,2000084168090312,1999987777208497,
    2000005693711468,2000061700114021,2000012037067030,2000096577310010,1999919498065821,
    2000021078917404,1999815175887124,1999868138374715,1999971897649545,1999979115102049,
    2000147941448124,2000014685757484,1999997482462350,2000081395211295,2000127992000423,
    2000078437679401,2000018199489970,1999927509544177,2000048699235485,1999940747678205,
    2000000092415426,1999945037312682,1999817520372416,1999994247643921,2000057678876822,
    2000116856712163,1999960990268354,2000056687299521,1999863569038052,1999972040631270,
    1999849732801208,2000103598153013,1999982436008582,1999861497013209,1999926739871184,
    1999851766226853,2000059085832382,2000212828579556,2000117809590694,1999812672858467,
    2000005791552316,1999819934601189,2000123294810362,2000176501589961,1999922670154479,
    1999911196782375,1999856577221892,1999976672301619,1999958650916317,1999971401249074,
    1999990358628633,2000044423731947,1999989422741946,2000188049643386],
   [1999991413378027,1999909056832455,1999964844468290,2000091164909111,1999993697113032,
    2000031192176303,2000189685248780,1999990560738301,2000052830548324,2000030974530107,
    2000018327986367,1999962895186960,1999996980543873,2000042306606286,1999840927666164,
    1999967754814484,2000246476133575,2000015136471225,1999985261253228,1999873003973737,
    1999958337972012,2000060713356274,1999981933026766,2000009042974271,2000104640631288,
    1999792808661479,1999915366862690,1999940937539249,1999953931509690,1999782533926030,
    2000005333056155,2000109072384023,2000076620073542,2000008986722133,2000098865202931,
    2000106097697358,1999919991052160,1999668448159086,2000082689938412,1999918260462503,
    2000028202542604,2000092066955065,1999984349014929,1999977398526075,2000154375873116,
    1999744591640074,1999872301208439,1999953511347716,2000211200736829,1999797294904622,
    2000369633927981,2000380921836926,1999648035761385,1999758872122772,1999973552875218,
    1999916162068530,2000178174504174,2000246479552742,2000330865481933,1999588630638178,
    1999665352526284,2000291080384106,2000078900141977,2000057585275745],
   [2000201913806737,2000257011815057,1999992752672030,1999938783167329,2000116597799959,
    1999810982452616,1999501494331031,1999713154860191,2000357777007317,2000097733308198,
    1999589662289670,2000525220718661,2000382834440021,2000204550805403,1999721195252713,
    2000682169276257,1999486895191200,2000362561038535,1999815156247989,2000064311245049,
    1999999071942763,1999795586793567,1999750831735116,2000296514107996,2000625002902985,
    1999507874788630,1999969256744206,2000322573062370,1999324395499733,2000694123869603,
    1999458454568108,1999983337124075,1999583982604981,1999426400554483,2000859781265233,
    1999450272973710,1999875535840182,2000692668795222,1999195747607535,2000494830759702,
    1999775481158293,1999726194443650,1999264893926671,1999348679574176,1999576905327675,
    1999869508583049,1999389693752787,2000722796511545,2000509823103063,1999851867829463,
    1999532028493826,1999268174559719,1999602106645000,2000122950285105,1999506257890759,
    1999487417226352,1999728214633115,1999926368887834,2000380929651016,1999514137249286,
    1999832552690853,1999776220378798,2000260037820478,2000212916660008],
   [1999981406402821,1999956823274307,2000054396013681,2000005416058791,2000229921260118,
    1999729082852732,2000025763838573,2000391277784526,2000554158480601,1999876643389637,
    2000483204122284,1999273017569904,2000062767581992,2000400772526102,1999516062387637,
    2000172883131318,2000014291634670,1999734351607149,2000474033150504,1999672677190086,
    1999780447682660,2000619207573879,2000534874853032,1999966918330475,2000723869287224,
    1999186447224197,2000074855455884,2000906292672189,2000930260101069,2000073366485366,
    2000919275876574,1998994467461549,2000134487954697,2000974134683343,1999015238585408,
    1999692202005732,2001063878569221,1998770776616962,2000127874063823,2001340022224267,
    1999005913494541,1999932733370138,2001284895892438,1999210283810384,1999886407458916,
    2001173855616998,1999241634478207,1999807754879144,1998915602349175,1999202306202149,
    1999829181519712,2001316325452442,1999077999319519,1999272383011586,2001376466356289,
    1999368776212012,1998908104282474,2001326193673665,1999702673271741,1998627180263398,
    2001456969117710,2000393305833041,1998041641389991,2000713808542754],
   [2001172158627819,1998178750800182,1999699367923880,2001496447862250,2001079853158214,
    1999093309497715,2001430236415307,1999691774239706,1998681113624423,2000909603946051,
    2000413829473436,1998979685580521,1999630330234405,2000186249419901,2001112614102444,
    2000600525732810,2000723323388512,1998035520271242,1999454134503115,2002127810670601,
    1999524073763553,1997963396012755,2001172630830443,2001244386002622,2001527616608746,
    2000028701944563,2001610882848640,1998993232744380,1998732803512845,2001629312618680,
    2000575945636727,1998160715360490,2000072199145642,2001426970460944,2000723538818195,
    1999247104039899,2001031199279983,2000231639061572,1998721736638712,2000889311792460,
    2001001353684833,1998447239003821,1999206324570343,2001541209601567,2000103279614710,
    1998541156366234,2000492391345963,2001054423728169,1998917858433161,1999466194870955,
    2001505897745787,1999903294924371,1998174315890231,2000664788541569,1997980977490247,
    1998998535677574,1998079185087956,2001180488045791,2001486221549061,1998586856729223,
    1999026635367979,2001583938440243,2000333038085622,1998119117840746],
   [2000186470109084,2002277720412174,1999683778960894,1997577831367706,2000241207479048,
    2002225567271042,1999766145407647,1998070039119167,1999803672013690,2001471244932027,
    1999698400904416,1998903029884017,2000343640755763,2000671250267075,1999609702312318,
    2000118975209572,2000721933238273,1999828748403374,1998932408907609,1999833555949526,
    1998920163746677,1999657515500188,1998911646943242,2000685783352109,2001319381534609,
    1998990857924053,1998091542354342,2000736299014738,2001888384291246,1998886712004436,
    2002634429218641,2000913518408737,2003457410538215,1999940808823895,1996311165427937,
    1999391448647354,2004120992976018,2001939900021884,1996235768236108,1996959284738395,
    1996910494585014,2003917030496397,1997633177385897,1994973116165118,2000947524309771,
    2005747673486845,2000918166314319,1993958670290185,1996486377881399,2005000068424025,
    2005990044025678,1997568416481992,1992812506206874,1999249006237580,2006921527471588,
    2003825465888139,1994570425917572,1993384636615967,2002360205849923,2008145584442639,
    2001913722894014,1992563198937310,1993714501080013,2003870541604459],
   [2008572151678487,2001085302934717,1991920922615783,1994031265467376,2004769161368579,
    2009511918416472,2001552242107108,1991126483005126,1991841305007708,2002900209178220,
    2010270285364456,2004693640127735,1993221386229474,1990133015464200,1999240721850598,
    2009468079504181,2008464220345810,1997323145607073,1989101929443220,1993532422285862,
    2005940948521286,2012645023929234,2006151348314448,1993188511612974,1987306219992454,
    1994558250916954,2007422214380873,2012728148321239,2004943371397511,2008527007866176,
    2014718362673451,2007490987377051,2006861589478492,2015517573462949,2010640930788602,
    2003857705312376,2015812618269586,2015047927343756,2001641912203862,2014244104893857,
    2020347747909139,2011607277704799,2006145791352564,2020423440905059,2020828892012054,
    2006122118112267,2014947628799110,2029206725931689,2027201175390761,2008896121444838,
    2016214127035028,2034304225856906,2034599553878224,2014983924414708,2016838811210480,
    2046881037034795,2061152286682530,2051727177761882,2020080545353116,2023396098728962,
    2063135720650579,2083681876646576,2074505778911417,2032829496772874],
   [2036139580324529,2121218121051038,2208532995893432,2284943220615121,2340673072779570,
    2370666539082770,2374633548670365,2356100645504738,2320939291537302,2275834424024103,
    2227031112452845,2179528671728105,2136738043842216,2100513693212004,2071424298807954,
    2049127395799078,2032743364615679,2021165090552936,2013277419196850,2008087934632794,
    2004785952301620,2002751895343725,2001537836967544,2000835309087049,2000441014874778,
    2000226313629646,2000112869875593,2000054700802752,1999974243930880,1999988220035508,
    1999994767804470,2000002256250307,2000000944351681,1999999616472678,1999999848908010,
    1999999942279586,2000000021375389,2000000007670813,1999999997333457,1999999999102449,
    1999999999707604,2000000000092138,1999999999971938,1999999999991753,2000000000002331,
    2000000000000628,1999999999999843,1999999999999966,2000000000000005,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_6_1 : List ℕ := pNatCat
  [
   [1999907098884661,2000067413617086,1999930977140441,2000174214364207,2000179034676047,
    2000050717513880,1999965824212043,1999883200046888,1999868370787638,2000059179804247,
    1999962796488482,2000107011110695,1999958882928113,2000007989439334,2000079467613873,
    1999961776651958,2000097572737951,2000048682306242,2000015045441264,1999993934334182,
    1999903922734389,1999796338263927,1999937751798021,1999954467666352,2000084758711168,
    2000006665450361,1999937204570525,2000107027170036,2000035987110799,2000139801138780,
    2000051614608867,2000108493267312,1999875723268520,2000091172161641,2000007521521838,
    2000050582701633,1999908720131711,1999828899153006,2000008466110060,1999903531541019,
    2000016135765463,2000082399810454,2000132723846540,1999874120320640,2000064933448990,
    1999843041978045,1999887976009883,2000162904821306,1999967528274041,1999942749148816,
    1999831305692903,1999826706412430,1999944281022817,2000171404197022,2000124291815329,
    2000068967761414,1999803794172415,1999943495586248,2000035422709277,2000046772716084,
    2000066808354681,2000026849641353,1999956599322084,1999823169308966],
   [2000066434612006,1999954406671815,1999832112820855,1999955999423079,2000030253451277,
    2000059128900357,2000032218913073,2000054993203307,2000082560769378,1999841575908061,
    2000058467193583,2000034181355246,1999930388970959,2000079192363494,2000160015491493,
    2000007352988845,2000062544863153,1999927055806876,2000191933287243,2000072538963247,
    1999901510559324,1999850230534936,2000040663706676,2000015313610250,2000025877821937,
    2000101906337803,2000088116287020,1999822279346273,1999992174175919,1999946485661159,
    2000171030580335,1999908821511964,1999934345472091,2000133459477363,2000028629031571,
    1999695239594119,2000065091383240,1999817209170159,1999964890403393,1999836185452555,
    2000039233001233,1999987469774874,2000157438345083,2000295108462318,1999780209343305,
    1999888413266193,2000256927297067,1999653645561351,1999873300235719,2000111655738488,
    2000080942837885,1999941596373215,1999929091194874,2000333004240502,1999876456247624,
    1999623838855856,1999988907090515,1999996855422420,1999945646377995,2000229349216244,
    2000480037712966,1999965990433503,1999537405279641,1999870081409381],
   [1999979784539375,2000373099079487,1999756088407581,2000521584914673,1999765182211497,
    1999980763077186,1999452138247125,2000777502102095,1999756403874553,1999675425324193,
    2000481617181721,2000359199160504,2000102741578108,1999908634440458,2000034407451878,
    1999810468783290,1999813057460557,2000006583241288,1999187772187044,2000828407469801,
    1999518216292531,1999984192197721,2000861502934444,1999777712898970,2000358311321584,
    1999816416728774,2000057900929900,2000891796587511,1999100957460234,2000584103003497,
    1999657971420013,1999525855181637,2000395487027825,2000381710171809,1999672663684131,
    2000148305472244,1999809685173761,2000306809871627,1999996623409069,1999945780256513,
    2000133402730594,1999509019869060,1999566289570706,2000319297438145,1999791236890761,
    1999612431216842,2000111811002933,1999908904734403,2000435338638186,1999750477225703,
    2000064727734843,2000008989094750,1999802323210550,1999309205151278,1998925033374375,
    1999320227295435,2000247618656843,2000301041392241,2000263467241796,1999591164136862,
    1999949245509561,1999891372066939,2000004586902740,1999154903014301],
   [1999783049455004,1999341608167294,1999892853620788,2000328617590829,1999226832814144,
    1999849200980705,2000078630277191,1999511189232538,2000421540122182,1999772306931121,
    1999809495928240,2000350830952867,2000347627879114,1999520381012854,2000398845797085,
    1999258834237092,2000340325547661,2000538246311315,2000218100830943,1999693860564947,
    2000862879048292,1999592725428469,1999959680725829,2000484355656557,1999241471167984,
    2000004258729899,2001003030369400,1999110217610527,2000012657033869,2000312183994622,
    1998750584727812,2001011113802460,2001522197998456,1998886696943874,1999847674575806,
    2001045427511387,1998690177268405,2001278153158461,2000935684392977,1999899178173481,
    2000135006018596,2001003184172545,1999838953793142,1999813320626474,2000586116955244,
    1999375231373820,1999898314402662,2000560553196422,1998998018001725,2000264497940894,
    2001538064635001,1998678376758483,1999051235683919,2001936144263342,2000353025259823,
    1998969791426053,2001630613587206,1998959172831143,1998522413936806,2000207893296007,
    2000725082899844,1998222007355622,1999799109865593,2001823281105375],
   [1998826762812671,1998856521730894,2001534222396215,1999463805769995,1999486854802024,
    2000001742128631,2000470252564004,1999475075374849,2000420643323406,2000438107984001,
    1998689299688772,1999219814190610,2001166474371700,1999267283315456,2001785965207770,
    2000120850155771,1999150703915624,2000185930268298,2001894599646511,2000160984985748,
    1997378670922519,1999600903297634,2002077687976251,1999396638767773,1999943643390454,
    2000753512399450,1999939041674883,1999687462930874,2000992777292967,2000311131775497,
    1997503443630975,1999345271436002,2002320884659307,2000659462627714,1999718053695876,
    2001467799016612,2000785070481816,1999446438366177,2000789578693616,2000731072138930,
    1998246034862277,1999671398774547,2001407307960690,2001199626414330,1997624827341302,
    2002070824896727,2000562120356152,1999352286134028,2000284565661331,2000395429086566,
    1999992492765079,1999191028262046,2000018052688215,2000943139983232,1999432666174117,
    1999079366970972,2000995980591104,2000394749155998,1998337912729146,2000145611323576,
    2002461642180658,2000128998678696,1997204962581400,1999251815794414],
   [2000473616226084,1998351529589488,1997921359508760,2001021278831802,2001613953175675,
    1998613599750554,1998044204512410,2001344433342280,2001434099851180,1999295073542855,
    1998557043199440,2001279135635166,1999976241046294,1999828439704274,2000013783152801,
    1999911821806034,2000059599415509,1999451325110496,2000429331599000,1999625531277266,
    2000490825375693,1997853792104093,2002457378756402,1999433678742462,1999027669848778,
    2001495574312166,2000530742979325,1999571854565126,1998053653110419,1999296848653734,
    1999518503144836,2002539602682424,1996453636940392,2000490993912501,2001549339020181,
    1999145739327885,1998130934402753,1998285184916945,2002915759226891,2005758312612323,
    2000231193932504,1995634613010940,2000238255162535,2005277660299423,2001561274562231,
    1996105888908202,1998615462511408,2003658081381460,2000620094587682,1993321806244148,
    1994306304383238,2003119134245947,2005991237389076,1998321655166472,1992644733101958,
    1998467756282799,2006753182734213,2004331409588671,1995014527740021,1993597342935981,
    2002439464246946,2007700858895735,2000955919878430,1992358622077488],
   [1995134178177137,2005386135233654,2007863406581969,1998730450898363,1991272922363298,
    1996396471416805,2006770899764444,2007455703339204,1997298668150655,1990563170148746,
    1996897866145282,2007920721214722,2008701274443936,1997977569557275,1989749877210841,
    1994732530874247,2006338390142692,2009838672992330,2000309180409305,1990984111807404,
    1991442237771882,2004784040178755,2010298473898143,2004564747958553,1994919587192924,
    1986343181451384,1996725268162529,2014729531357541,2009922818109332,1994358568351128,
    1996073464536885,1997944307712815,1989192592494135,2005113617653822,2009612869131240,
    2001980782089144,2007239681193776,2016379033318257,2008889571213305,2001623226935980,
    2017680248258400,2014703254888886,2003682420682889,2006918463460790,2019943209237069,
    2011211219179475,2003415806344613,2015857064446857,2023495980699440,2012161298584088,
    1999083755305371,2020418298349679,2029593459061230,2016169402187873,2008536128227743,
    2015269164017578,2040547014597114,2030222744104211,2003771346998928,2011539929158956,
    2033850179944498,2066748266472346,2051530143431947,2008506884134865],
   [2016614468739915,2065807491697856,2087560360245867,2061293459775592,2024239779404657,
    2018178105694221,2056922583745684,2129289615451312,2214201816287872,2291847485229094,
    2348529510337574,2377656968695792,2378899441776618,2356487474511839,2317212860387704,
    2268560410915452,2217282426401783,2168555978158847,2125696444854394,2090292404124525,
    2062578605850303,2041905141055089,2027129193407770,2017019474655916,2010310514322147,
    2006087571046477,2003465552769049,2001901415583096,2001030823712965,2000552337960657,
    2000272830747203,2000110323207268,2000031747949438,2000004740694118,1999999470365383,
    1999999494705228,1999999789209943,1999999874161342,1999999923547983,1999999966422464,
    1999999989286149,1999999997023447,1999999999011151,1999999999587326,1999999999827274,
    1999999999935785,1999999999979702,1999999999994702,1999999999998870,1999999999999799,
    1999999999999971,1999999999999998,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_6_2 : List ℕ := pNatCat
  [
   [1999864344410101,2000064033197170,1999961890512008,1999921269414417,2000029743503011,
    2000153541255557,2000081672407252,2000219852780404,1999986646342353,1999963813667880,
    1999937316580961,1999836660563019,2000032376963186,1999999794635882,1999989424711939,
    2000029197660522,2000039980167427,1999952222947503,2000068635630793,2000000710005173,
    2000017107552502,2000105556561273,2000009223829471,2000138777106305,1999905847717286,
    1999899993772343,1999784965561403,2000030666583798,1999906226836280,2000003588197781,
    2000023811945724,1999927477675391,2000051402986409,1999978843171141,2000173895565110,
    2000099741176950,2000066362994281,1999895032967886,2000149226140253,2000053233845347,
    1999938416085052,2000154662862131,1999892759152851,1999891671012414,1999941444251235,
    1999915662634726,1999897799625703,2000122379464322,2000060058462276,2000090583789110,
    1999933380247229,1999893996518435,1999958162597651,1999966603098762,2000121140376077,
    2000043042387755,1999933323411535,1999694991171420,1999850246396390,2000066520405263,
    2000021548465333,2000100515457052,2000093250356344,1999868995825090],
   [1999920696388058,1999956735978660,2000164072823816,1999997412108096,1999935367986996,
    2000075987298479,2000028602175293,1999854263847385,2000085117619710,1999852148016789,
    1999893265223923,1999916204775696,2000020725973548,2000037887572666,2000033630134270,
    1999988914034099,2000115554888050,2000006895895822,1999935585344391,1999826786137048,
    2000221371925820,2000022426832430,2000005112277152,1999985060013644,2000083976039576,
    2000066615783724,2000161878453361,1999915867126290,2000249946141468,1999783161282266,
    1999840387956132,2000078117869702,2000131921387805,2000007147498725,1999923333091667,
    2000114481833084,2000020835309391,1999790520084754,2000196839830167,1999848821979282,
    1999969303174453,2000303602658942,1999826917037956,1999893999496113,2000071745580152,
    2000082135374854,1999775429911331,1999659464423984,2000102244846714,1999983948007388,
    1999781710479948,2000163513872583,2000260961845874,2000070347967997,1999648599968248,
    2000408346054357,1999682921479801,2000105649887333,1999533681063972,2000437335240612,
    1999707220930886,2000180216000704,1999997329517147,2000294632765369],
   [1999970281604098,1999192655469216,2000100317665852,2000251260359608,1999856668403641,
    2000374003799754,2000248193218644,2000072738501436,1999009851936394,2000600901060813,
    1999930118853635,1999955936628083,2000445720681414,1999353296585808,2000564389412824,
    2000224250579287,1999125106781600,2000628428056541,1999437388615016,2000523546069780,
    1999890163922520,2000074391211212,2000705994011391,1999869391744155,1999585664680703,
    2000668335517387,1999581488541456,1999617760262281,1999936381501992,1999724798859480,
    2000028085333579,2000191825776960,2000210934942691,2000121459278412,1999780458366912,
    2000232429608264,2000795644258857,1999692257041115,2000231688043185,1999883850493097,
    1999797231020574,1999971179173551,2000184453165943,2000140129660126,1999825112993609,
    1999728412790436,2000359564099354,2000113526986514,2000229491424321,1999691403297716,
    2000114749695965,1999883209192204,2000093216599329,1999411718970914,1999915084465842,
    1999953677623822,1999886162651346,2000088956778240,1999366561442457,2000239087626687,
    2000968940649921,1999788258323776,2000082958932800,1999024181141165],
   [1999073290644178,1999763083260467,2000038092589525,1999164887941843,2000500501973813,
    1999635164006027,2000361945163877,2000145150882186,1999649750983148,1999240987898090,
    2000134967361766,1999411056899489,1999695316125924,2000096746706580,1999151732536210,
    1999798407478388,2000629414384996,1998990471987237,1999763282208536,2000508206665458,
    1999229262821209,2000740271732678,2000456473721576,1998981402414949,2000147656917791,
    2000894647961719,1998383035780858,2001247443358080,2000267623909000,1999141086273311,
    2001102621379984,2000725084195247,1998960160816664,1999828642867970,2000787957735636,
    1999711833156011,2000260641035988,2000480443400788,1998738594976394,1999630137254378,
    2000917515127014,1999720378145804,2000520413716682,2000457226983074,1999188604024360,
    1999846802091155,2001655884957285,1998419673615510,2000609382470735,2001939886536593,
    1999408951464361,1999487465687765,2001726535694430,2000589646605818,1998796568248253,
    2000377164887310,2000786459961822,1998115826194535,2001367398285076,2000952643102252,
    1998313808168523,1999419575548345,2001412439413068,1999961109609969],
   [1999731396746783,2000715009097102,2001234662718253,1998188315300211,2000653247923686,
    1999414334231868,1999043720157150,2000506307433968,1999690497695156,1999251857797130,
    2000228432577793,2000201339839649,1999868488948806,1999355430450325,2000622005952914,
    1998993410969009,1999538659571414,2002286985141148,2000029157008863,1997566290042785,
    1999598725648459,2001697473065425,1999762923149110,1998603104999617,2000682254902126,
    2000752218703227,1999903882327679,2001505396769683,2000516849593685,1998153282914891,
    1999382807823360,2002304096996339,1998830754537753,1999257849394375,1999805209410025,
    2002016773350727,1999327781838032,2000832119495874,2000842851158034,1997304897062309,
    1999754153651980,2001574524823954,1999452471167214,1999422057035453,2001269347719624,
    2001672918155822,2000351024039729,1999859525116116,2000685327700957,2000187487789799,
    1998997984466829,2000352600861179,2000970063324781,1999498035301617,1999421782059753,
    2001672019723439,2000755390226495,1998682526891689,2000290680630680,2001808320746250,
    1999101483580762,1998331836074186,2000883381110727,2002154253238357],
   [1998360465180999,1998506401080386,2000579870879702,2001427207295808,1998759811573134,
    1999754836062631,2002734901273261,1999574423108808,1997860153902800,1998039370416902,
    2001174688891539,1998543217405826,2000154611945355,1998130691226189,2000639472642388,
    2000280295127230,1998661244635825,2001580010089853,1999216776342254,1999519880799705,
    2000160827559711,2001732966612770,1997561300295747,2001439232917153,1999487118651511,
    2000304160178481,2000351206249303,1998061188007331,2001354134490173,2000923154363888,
    1997747804507213,1999391427640183,2001519322414369,2001319293098694,1999908782253799,
    1998560928463435,1999975179865337,2001556365377794,1998603221831202,1996306501576711,
    2000767045704249,2004585336048785,1999653566625451,1993856115029884,1997607732794753,
    2004638632427820,2003244142150540,1997231690381105,1998296765835737,2004428955987671,
    2003865943787620,1997061591458716,1996501409401312,2004147961271623,2006753883154339,
    1998371322965142,1991462616381065,1996763889944330,2005353812555006,2003163328426496,
    1994032836957488,1993300964805528,2002625460487704,2007227503910254],
   [1999807421421437,1992341268637407,1996978412271143,2006704575403962,2006266888549758,
    1996055177472083,1991540039832780,1999825888282906,2008341422272963,2004753637623875,
    1993497096150740,1992515454103394,2001382135790620,2009918755324609,2002787370461978,
    1992089450987627,1992437611753874,2001433845609911,2011287234980688,2004572733971191,
    1990943275947260,1992503098786441,2001444573444476,2007500112530503,2006771419481981,
    1998243985734258,1981614653929506,2000748897937913,2016849626587246,2002106777248429,
    1994518259844978,1995316965848900,1994573093576887,1998229039394452,2014907493155120,
    2004398166553072,1992747160450329,1998737766492653,2000703449788746,1990292338225959,
    1997137437781943,2012818079057009,2004382715763444,2001473203864291,2010105455943535,
    2018812470572188,2005185878018188,2001945959399972,2021932366995139,2012800795862191,
    2001956765204845,2006377864635940,2019582615391970,2025315678281041,1998485278088848,
    2005123795447014,2025017686681236,2023518819956463,2011625175309626,2000871176766493,
    2018803341789839,2047359271966670,2030016005738807,1990626775283258],
   [2000355854983482,2047906960849018,2062700397226262,2030857816528995,2005534054584480,
    2023504792004668,2063476238270445,2082396841095968,2063932451034255,2027726522968990,
    2006762491645753,2023145919706923,2078950044304389,2160462681718425,2247463673135953,
    2321333114428323,2369657013727813,2387610077443701,2376894742317111,2343761980764754,
    2296335618941325,2242846676507608,2189937338968704,2142225074879232,2102239081608982,
    2070666853881624,2047027867617607,2030191914273122,2018716539353634,2011191394485753,
    2006457235711209,2003613740411854,2001969810955077,2001036707779754,2000513869311590,
    2000232544139237,2000093575140559,2000032862238145,2000009900189428,2000002463130088,
    2000000433007971,1999999997305047,1999999950133298,1999999969250459,1999999986416643,
    1999999994883404,1999999998229390,1999999999409189,1999999999805948,1999999999937964,
    1999999999981251,1999999999994794,1999999999998700,1999999999999714,1999999999999948,
    1999999999999994,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_6_3 : List ℕ := pNatCat
  [
   [1999852303663996,1999964445362251,2000025194980373,2000039735548500,1999852144874246,
    2000018850841222,1999974689248733,1999991534973188,2000189938701391,2000096120050521,
    2000133456407335,2000113530574232,2000006987006503,1999870412909512,1999973501754438,
    1999935529565392,1999912473934306,2000072744760313,1999923249956021,2000084023570806,
    1999947305259814,2000065294307744,1999953582208360,2000071820791382,1999986458895717,
    1999942306769182,2000182282917144,2000056049222787,2000114773310484,1999928859169610,
    1999954560599282,1999847387404236,1999947290682694,1999914858756804,1999917834885865,
    2000144928390518,1999832394604393,1999903912732722,2000081897216074,2000078538070977,
    2000005208466293,2000172155902764,2000002771760750,2000004822834328,2000070635926948,
    2000039556650710,2000097180006969,1999994014781093,2000067832894003,1999975052981461,
    1999922055066318,1999853066630198,1999873769174318,2000022682706908,2000026713792803,
    2000045226446733,2000191154538795,1999876596355549,1999851937978796,1999930163750771,
    2000098040861412,2000105911581112,2000034949125913,1999909909349696],
   [1999955393299738,1999635802598330,1999944398963553,2000129192714468,2000043778806766,
    1999973597218949,2000022333272873,1999920120164497,2000007379936715,1999945518730131,
    2000106027716301,1999938844124765,2000076580927499,1999927968898674,2000104201945298,
    2000050066690635,1999923567174737,1999783992969055,2000134263075511,1999799556524687,
    1999979083229028,1999883846582988,2000047130532180,2000222119639476,1999940899707583,
    1999910968139450,2000065924297608,1999972498558601,2000021857853749,1999906377696080,
    2000224977704114,1999974765693268,1999719886655527,2000317085021403,2000103457561137,
    2000028615573901,2000176343041271,1999909699166394,1999904983066166,2000023970393128,
    2000059061967796,1999969793821285,1999834136219081,2000387163971777,1999880804149277,
    2000030888931902,1999578510150717,2000628522513582,1999607521860631,2000085515945407,
    1999864486972101,2000355433208748,1999812110777702,1999901566095752,2000287022541389,
    1999782781271280,1999881229151978,1999744648207027,1999852859615334,2000329374696530,
    1999444294662854,2000388808282149,2000063541921098,2000236562669280],
   [1999544551009383,2000192457645503,2000581686861435,1999030805833963,2000077001571624,
    2000371836217592,1999294047795175,2000998551194105,1999517393852242,2000394882564593,
    1999863636338917,1999185773878704,2000058669085586,2000317156176947,2000109298910998,
    2000359838706966,1999460655104044,2000265527238098,2000279864004937,1999326994201953,
    2000158768389593,2000356117013208,1999764924241093,2000043579312355,2000329392761386,
    1999870425493327,2000034234846897,1999493360895021,2000331903897238,1999927938648779,
    1999908072984704,2000445761842460,2000090148068268,1999909905407234,2000480305362837,
    2000142794188084,1999941343392812,1999358481049280,2000037254865398,1999784525220663,
    2000092817511260,1999859272916099,2000169963281853,1999766732599656,2000038439789882,
    2000444890110542,2000280402561909,2000389878905459,1999740435253211,1999787967411814,
    2000606684505498,1999619265637513,2000321417341309,1999660392924968,1999870508101678,
    2000253574144855,2000314188715152,1999242319876371,2000764108153429,1999917098273803,
    2000184032264697,1999971190300703,1999581777754368,1999744050917295],
   [2000596819256723,1999713753245274,1999371524785871,1999741316266693,1999591563902400,
    2000397219438046,2001023131229183,1999638205130549,1999888113923365,2000343372435579,
    1998754318974784,2000003879099824,1999572391759810,1998860133409821,1999967497904838,
    2001017525670445,1998726076019058,2000863286662567,1999956056447519,1998815866855844,
    2000955890454140,1999521051730996,1998617148686129,2000493632408621,2000050203713869,
    1998939497308405,2000259222495795,2000006578706159,1998663880379723,2000191277514176,
    2000925630673123,1998951681328101,2000268442913140,2000382136322245,1999752456481212,
    1999697844874075,2000697132009446,1998558782658758,2000687483701252,2001204811177777,
    1999205804554977,2000543312030914,2000337693076445,1998681336000751,2000914660596081,
    2001303838666479,1999448484136230,1998515453972207,2001626044953007,1999376291524701,
    1998502300472462,2001579309481220,2000748507484985,1998418133630180,2001026275285484,
    1999963288497552,1999674112642955,1999713362446230,2001813878684520,1999068995918057,
    1999324058562073,2002440073309326,2000392323492709,1999322620938820],
   [2000772574755702,1999716625810229,2000171866445844,2000240063041787,2000287143009776,
    1999570338502554,1999868516735308,2000264965681632,1998920721988023,2000456354229392,
    2001324098531095,1999624797878213,2000090537106823,2000950325312580,1999341416198698,
    1998945843952625,2000783229157097,2000407939394776,1997492096095830,1999930285583348,
    2001811144940458,2000343412100010,1997118573827238,2001023767121202,1999697584926542,
    2000151263441772,2000538347954415,2000205042221253,1998900544965481,1999336067517118,
    2002274014459930,1999046572133162,1997436496754054,2001200602320054,2000758987250178,
    1999623899377718,2001115209342246,2000355293676663,1999159575446848,2000692300595962,
    2001076357969284,1999202803242808,1998173921211913,2000426871983038,2001518476147803,
    2000121416220061,1999614202282515,2000943180455933,2000174144169067,1998774423094159,
    1999643937765630,2000691358177693,1998736923634181,2000171925527344,2001824516584115,
    2001306462802647,1998821651711113,2001035936839232,2001756955163054,1998953475372621,
    1999047471260303,2000650912854455,2002088902697950,1997657936797463],
   [2000033352300199,2001576307354110,2002037356269499,1997291228932018,2000549939438703,
    2001608930699657,1998922181069929,2000330036018759,1999411422191516,2001988493231284,
    1998545584963370,1998616781434042,1999471717693061,2002845106484469,1998851174341574,
    2001159478027703,2000401782054928,1997822790294505,2000729057131025,1999172589657806,
    1998802525519860,1999539557143394,1998615239375963,2000566859640343,2000217931045569,
    1998243075809788,2000367920157263,2001246850008101,1999127669847204,1999179058583849,
    2000691051346197,2000863264475057,1999762307034163,1998666732026730,1999867851065777,
    2002040959009103,2000393387261237,1997172677601386,1999047833462758,2002734285528144,
    2000492779320301,1996698065719679,1999965256953990,2004888440259489,2001266495067703,
    1994486400731378,1996716316304187,2004229868718300,2003746697459755,1996508200835251,
    1995593726405746,2001825028082269,2002881038497047,1996739455007386,1995705884152030,
    2003343305116970,2006751619964216,1999294533576598,1993422493260333,1999848931120391,
    2008517490569095,2005132434351495,1994877279758502,1994362407510996],
   [2002944256699578,2005939685375348,1996607129684639,1991651890860476,1997579924854264,
    2007241027496294,2003080974741221,1993268419948894,1993786585753579,2002736091485728,
    2009274184774586,2000024650467276,1990778397397637,1997026790927310,2005364263060934,
    2007859981955696,1997539210561666,1990819772755569,1995766606446518,2012690046087596,
    2004179670403977,1993026331255989,1996235377772085,1993697588007449,2007230638513248,
    2013039966174308,1995173841549810,1982075067927635,2004953773232381,2011888308222673,
    2000629431823662,1997420602345190,1993641152103530,1992752614455646,2006779267200404,
    2014919868136534,1993201859154750,1991057180212299,2000627922935390,2000215445810369,
    1998521510877061,2005473243774586,2012805884370019,1991027837311017,1990499867681731,
    2006350762474943,1995541111385481,1995519762436204,2000393918872185,2015310370438713,
    2007509009925936,1995024675951654,2016270632564228,2022151683814626,2004314188499185,
    2000470900750324,2011471492429983,2023169657145452,2016037116381732,1996049731710039,
    2005737080486474,2034786740390856,2024650504248564,1989626744461312],
   [1997699832243208,2040465266389914,2047142403174121,2008640750524359,1987539947115411,
    2014898644393688,2050277955692657,2048516405114744,2018993512848004,2004545392235250,
    2026067521595555,2063451919644403,2081901456082871,2065838507774664,2028865181041798,
    2000375078999131,2005142812210596,2051428955457395,2130171453704255,2221930350314239,
    2305684925112119,2365297529170527,2392742086055856,2388058270450080,2357139029827590,
    2308933461580201,2252826731892801,2196679432433436,2145927919753064,2103549560966590,
    2070439636561777,2046007895624126,2028872216502902,2017421098677356,2010126443264234,
    2005684075099516,2003080256944467,2001602277227131,2000791157065567,2000365847725560,
    2000156462453259,2000061258886668,2000021765316638,2000006944753016,2000001953530882,
    2000000464266501,2000000081727963,2000000003589259,1999999994712611,1999999996758635,
    1999999998661699,1999999999533556,1999999999853432,1999999999957451,1999999999988534,
    1999999999997150,1999999999999359,1999999999999875,1999999999999982,1999999999999999,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_6_4 : List ℕ := pNatCat
  [
   [1999894009677517,1999926341321870,1999867619977245,2000079487571716,2000038541456023,
    1999901042725619,2000030388116418,1999942641554198,1999919850912175,1999967859330664,
    2000078406577513,2000038401567834,2000062057203304,2000262148123318,2000031291188662,
    2000141732341806,1999953889022749,2000006460743746,1999901189285623,1999938357081564,
    2000001769622484,1999867769616574,2000101735909376,1999947841649625,2000002755904902,
    1999977974287786,2000076029937354,2000023420025868,1999925559428693,2000053795670853,
    1999897100648613,2000136087153189,2000148904267151,2000022245254509,2000027537501799,
    2000136786612621,1999840998997535,1999821419513648,2000014803430367,1999929423305864,
    1999993587085883,1999923449592686,1999954826695089,1999914640687473,1999952833434976,
    2000060723184171,2000070124971761,2000052902824895,2000074198566553,1999965423839245,
    2000146901487984,1999992863555511,2000002460037101,2000108149889620,2000125091790686,
    1999972438010679,2000079203257707,1999897426253678,1999960888890313,1999769575932633,
    1999869082603594,2000149989668251,2000144437187728,1999923649993809],
   [2000080390933739,1999872980071631,1999914299300970,1999885560912732,2000229632664450,
    2000092789816903,2000049507270448,1999844779258837,1999879574774623,1999772947593551,
    2000076290556220,1999843136085719,2000121097720119,2000060954648008,1999834435504270,
    2000020934913324,2000033036492516,1999978863376522,2000035249274846,1999829212433796,
    2000124091238774,2000100091208006,1999973919769673,2000016893007552,1999892761435994,
    2000231520522938,1999880652134775,1999661511256538,2000123576035043,1999932143041696,
    1999802512757285,2000194673303819,2000013407817952,2000113876219920,1999684697862846,
    2000328385735773,1999671856258590,2000378370877524,1999729025176779,2000306456652817,
    1999567474875292,2000112061079434,2000270250273356,2000017962296538,1999986586294482,
    2000027975904982,2000384298674470,1999818960751513,1999613604087748,2000471407959600,
    1999712812883349,2000305328093128,1999680338116979,2000246367121091,2000089879359876,
    1999748240511710,2000126778369569,1999897699786892,2000252754388997,1999850123276411,
    1999377907519904,2001318811981789,1999081442011474,2000110087420003],
   [2000511390971558,1999568430486363,1999933395404513,1999797914257867,1999732754339697,
    2000433571085675,1999529914336548,2000002788211994,2000349949028040,1999787952189890,
    2000309781751598,1999969405189326,1999888956496498,2000140662070137,1999571455968070,
    1999383035164351,2000930932403351,2000169060245134,1999929808014564,1999818076695116,
    1999865409258864,1999929828644614,1999678061361902,2000022790058431,2000535474067595,
    1999639201920158,2000193398436634,2000050819810300,2000091686499312,1999603579513179,
    2000177912621568,1999945232512436,1999987252778758,2000152034965162,2000248439633126,
    2000041082348476,1999572401665992,2000062414683263,2000216244682772,1999617999266730,
    2000311392149760,1999526895446517,2000543777894974,2000169097433864,2000277256904228,
    2000209182644304,2000231851498944,1999100133579218,2000445757388691,1999728265400088,
    1999991550550897,2000063218163392,1999434125696354,1999744681114449,2000669470569721,
    2000071882518152,1999956906927260,2000342994115359,2000004587765219,2000213523238463,
    2000384107864978,1999560450723961,1999892169752338,2000812455958277],
   [1999250458527240,2000247718083353,1999801941056526,1999795270300243,2000496537118880,
    2000870654404658,1998669755270600,2000437523773487,2000409298758197,1999221369618300,
    2001265670455857,1999520436383552,1998555155547620,2000537573135539,1999713151881675,
    1999429244634645,2001008500368682,2000021922460989,1999658203234849,2000883282006973,
    2000122046502341,1998136493393056,2000380654761941,1999604002422220,1999099734958923,
    1999893661497024,2000672747803276,1998845490128854,2000443527492673,2000832220911930,
    1998691720330035,2000002621687423,2000159987313322,1998737432581841,2000923462882378,
    1999502278314107,1998999802138465,1999840920777343,2000576184771123,1998690558248361,
    1999797402701585,2000872084473599,1999203053446402,1999482064947480,2002431293396055,
    1998023401907830,1998958834675621,2001135649138831,2000630734212447,1999120998514898,
    2000416220069276,2001000637636931,1998588089987792,2000127071057163,2001866647009265,
    1998816956230881,2000391835100212,2000951257829509,1998851984546894,1999286159547690,
    2000725050590172,2000657310106663,1999163611154906,2000014456600597],
   [2000447681371987,1999772056478731,2000528740441878,1999875742958781,1999026725480021,
    2000845715904270,2000730661973417,2000057586531431,2000206665563911,2001682285019086,
    1998941686290703,2000188033833286,2000581511282401,2001173686478360,1998305150138738,
    2001046692380135,2000933629605943,1997562762228105,1999884188492643,2001650875480900,
    2000480579631138,1998601512802359,2000487037611462,2001852748165075,1999157265912569,
    1999938808376196,2000208554167337,1997873805241957,2000299652522575,2002167292371791,
    1998546507339970,1998289016968659,2000695093550139,2000525456916294,1999264001109252,
    1999888837893124,2000008012470826,1999753691781989,2000466752176835,2001024082032950,
    1998902792045433,1998459075198100,2000052942081811,2001637175287757,1998819550834022,
    1999280500211497,2001192140460165,2001163343914692,1999732525218457,2000112864234326,
    2000986162216095,1997828306236341,2000240462249217,2000491885096006,2000996241944800,
    1998265393951400,2001862552343574,2001124690807701,1999210902424180,1998312552081961,
    2000329968818391,2001715364140114,1996482174157051,2001478916486045],
   [2001898624234605,2000840520362691,1998415775462224,2001782754745431,2000716852427099,
    2000603165640219,1998345255460905,2000084685014197,2002334196368569,1997851968463799,
    2000574523634247,2002099488357046,1999162584103585,2000113927702353,1999703112010400,
    2000040094838250,2001512159486433,1999996094408960,1999607381137672,1999446611553026,
    1998624147421440,2000648583723036,2001374218909122,1999373822715763,1999985168019231,
    2001353551782322,1999924049960120,1998678086038466,1999274563145841,1999905648472498,
    1999555655389772,1998539039101287,1998828331482784,2000847933931164,2000703968233036,
    1998026134785846,1998675149864728,2002340069007946,2001450778427961,1997162540998614,
    1998366950734440,2003181758041871,2001759754069856,1996561635085658,1998252217673412,
    2003954398953072,2001942987503357,1995042339539235,1996401380684450,2004427725461052,
    2004874002093453,1997260807776936,1995390616976827,2002059832777628,2003788104588168,
    1997813821548770,1995436356600287,2002756420059390,2004618692510057,1997592034480026,
    1991616864660988,1999743766244825,2007559408056884,2002513953388777],
   [1993916887186205,1994945929251136,2006504419826606,2007085559596137,1997362341256844,
    1995646689531038,2001415814308868,2008881172584664,1999726057798426,1991559456808304,
    1994653661653579,2007464033801189,2002871811077382,1995133691187811,1993550608973197,
    1996109151487629,2012829270401769,2002108889125480,1988689556364302,1996584040237999,
    2007749429891797,2002201606337026,2002397187742402,1994510183353575,1988551709282725,
    2009707752285509,2014111848720539,1992179977576608,1985619607807132,2005363394095193,
    2005451080460145,2004049258934651,2000893247381697,1987524661474538,1997267735547376,
    2011324060529583,2009603570599790,1989033234888008,1990849963210461,2008846486669698,
    1995469218179237,2004041992952264,2008192538245265,1996170548063993,1989384446512155,
    1996224851381613,2011866257702541,2001007938865788,1994329590266189,2010590021675052,
    2002273656638863,1985589897564933,1995035206403817,2006701141613237,2003437431022580,
    1994925150610988,1998798671109528,2018501500145133,2020202853813782,1996184384469737,
    1997048807797549,2027263755533068,2025518244476346,1992123346729932],
   [1994230905897117,2031865153840205,2035957902064819,1998223257010835,1984565152884550,
    2018795795335846,2047052641386592,2029043150364083,1995908027836607,1996535419565459,
    2028438535229136,2049048988755111,2035094270114649,2007956971186542,2003418092357294,
    2031323181318373,2068538286219558,2083489219071204,2063600138984565,2023309566559990,
    1991963985955832,1995230540806719,2042553161814964,2125159705285968,2222439133482339,
    2311292210613086,2373758008162402,2400928624282900,2393148739878057,2357530728050289,
    2304429640222111,2244323414668231,2185731940518243,2134241265024247,2092501102229556,
    2060878520371812,2038322282157817,2023108999673564,2013371544959499,2007431021745719,
    2003961593985232,2002017833181342,2000975549954270,2000444199167016,2000189019320346,
    2000074643219745,2000027180939514,2000009067664832,2000002748610606,2000000747405056,
    2000000177999037,2000000035136939,2000000004785903,1999999999926232,1999999999651399,
    1999999999841910,1999999999948620,1999999999986066,1999999999996717,1999999999999327,
    1999999999999886,1999999999999987,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r512_6_5 : List ℕ := pNatCat
  [
   [1999915921501727,2000000379384023,1999889885451096,1999822181282895,2000040113196668,
    2000020733087639,1999983632743319,1999977835942013,2000011450177314,2000042845033041,
    1999802409508507,2000055094366865,1999927380981602,1999993509427317,1999994593047798,
    2000032354590151,2000193326272619,2000028413303649,2000224970308484,2000067593720168,
    2000035361986093,2000016805204094,1999970446117172,1999988629285197,1999824208747704,
    2000052007698560,1999964620185749,1999948051416752,1999999175868136,2000003780493976,
    1999926986462503,2000101879438995,2000115939512297,1999824750305359,2000004951264325,
    2000038258139525,1999992932229025,1999999522755212,2000098528322582,2000162823504173,
    2000098388004285,1999959715654039,2000016715913681,1999848726326504,1999976779512200,
    1999944404621095,1999965616789794,1999973029189850,1999978125034490,1999774321952944,
    2000035250009346,1999973442763122,1999998361181021,2000022825012729,2000058489520504,
    2000056608752324,2000122201945975,1999859706556037,2000157417420297,2000045880796303,
    2000037741590383,1999959671474601,2000250618228158,2000082140441164],
   [2000006035995391,1999793683637604,2000001662001862,1999760343328052,1999976916866771,
    2000102522760579,2000036284560587,2000151274044215,1999920594041045,1999729583158420,
    2000060553190613,1999968023251381,2000098048774761,2000158802366561,1999978694603146,
    2000069362204832,1999736919389004,1999865542584052,2000007980692058,1999916107431455,
    2000061868977002,1999910367221277,1999785843531980,2000421547229893,1999722170757831,
    2000048385789079,1999733451952819,2000486774702080,1999538825036147,2000257624579139,
    1999873192887885,2000185603621722,1999941910596883,1999993190515627,2000214873830385,
    1999764367897972,1999911920122239,1999972086020524,1999776095924675,2000164290013072,
    1999727894634638,2000583053376399,1999479840658826,1999928623029080,2000309227397060,
    1999986932659415,2000033447703180,1999762752917122,2000139071098874,2000243605343538,
    1999339235333693,2000664808490993,1999427164165787,2000722711390893,2000012040102715,
    1999411017177839,2000838940524756,1999845651251395,1999313569163054,2000698290325178,
    1999905193568608,1999840851571210,2000117435714261,1999830907328273],
   [2000431692105392,1999743690394032,1999802678428809,2000317414109385,2000005809533327,
    1999582023205563,2000374731016537,1999727170767397,2000346946293909,2000207473112850,
    1999562376752756,2000130273156461,2000190818842939,1999478026452180,1999974932423771,
    1999864831537429,2000367077164924,1999426804758088,1999861675457653,2000421345709284,
    2000502374052141,1999747590649269,1999844339085162,1999956442439257,1999593198243927,
    1999979489593836,2000351459332852,2000161062892178,2000149805162138,1999572821268331,
    2000450136781795,1999306023378869,2000094104633138,2000008324088560,2000058649617559,
    1999813387816693,2000436658942502,1999723834548647,2000485702246503,1999487674907643,
    1999730399990045,2000450168228853,1999900331027736,1999963670273675,2000374426792270,
    1999741611427876,1999971102088743,2000325360979297,1999722966913545,1999951881521786,
    1999986727197150,1999615303272167,1999874032079373,2001144530775325,1999661637087347,
    2000452769101715,1999829280307070,1999836845379019,2000282165135032,2000469879682285,
    1998966040546033,2000073216615613,2000313036846597,1998976098565449],
   [2000857835655474,1999774792055118,1999287185093560,2001447892698225,1999922794873221,
    1999245121979572,2000986882803241,1999759311929214,2000037625358725,2000684109922420,
    1999707346958611,1998715401849927,2001268363632313,1999866645389812,1999811297943871,
    2000469277151815,1999804672413791,1999125502916906,2001056530836708,2000748165205215,
    1998856493016345,2000402645801156,2000539487564979,1998178213408898,2000711558117030,
    1999531126460991,1999401432218049,2000754617976483,2000712634106980,1999544860519496,
    2000495479528094,1999749179671286,1999351330595220,1999485308134866,2000729583578795,
    1997629775763810,2000440311011717,2001172506919154,1998598912008263,2000123885982616,
    2000817294603935,1998974667563256,1999302103167164,2001010750312657,2000012080881027,
    1997652133568361,2001136713953521,2000792306321218,1997790229913292,2000049546354706,
    2000143780822360,1999106437011417,2000363457128190,2000918892217793,1999239434342381,
    1999072602198513,2000712509159491,1999969106756114,1999113528064893,2001197982734465,
    1999981810797873,1999615570001210,1999502927733134,2000863783494208],
   [1999608945921494,2001599282785434,1999360571290727,1999568474676920,2000120228607434,
    2000791282639999,1999461115146117,1998839752852271,2001632205784524,1999444636813250,
    1999208800451270,2001543496578954,1999923550410319,1998633237584381,1999970239476351,
    2001483381489147,1999492675259415,1999206750884513,2002377101232978,2000626348739520,
    1997942129853912,2001261079134403,2001388931068139,1999493647864707,2000608776108403,
    2000216426179955,1998531890964509,2000573644245167,2001112744807704,1998876741402956,
    1998541992557751,2001753247308676,2001233480027177,2000029189894284,1999217494741559,
    2000217097270354,1999709350351411,1999898922805980,2000868406227891,1998766304856672,
    1999273757766716,1999956586697910,2002022335383117,1997425327730960,1999311086378186,
    2000597947191095,2001272024486771,1998839628643143,2000242556826785,2000774721137189,
    1998279325795844,2000838685710297,1999312438872032,2000627129633131,1997268382465982,
    2001695542454403,2001736008557922,1999458816760129,1998870977609661,2002729206751591,
    1999483603326264,1997525436429198,2001036080654039,2000326829272467],
   [2000690572447299,1999005693130467,2000675626318955,2002829197864327,1997585941379100,
    1998550922370845,2001673470405760,1999084658693056,1999374381927612,2000670590337244,
    2000601791721197,2000960207900086,2000060030460416,2000485180781227,2001254441992829,
    1999523071866734,1999400121019730,2000491752342038,2000016089446535,2000687671687912,
    2001227752305585,1999241864646501,1998901195390436,2001061776991915,2001433206408979,
    2000066534062826,1999549663056907,1999933857468185,2000121277465492,1999396997915345,
    1998970600343839,2000608501264455,2001779161556421,1999765761633225,1998665798098238,
    2001250379583273,2001641210546367,1997689664227073,1997140501745747,2001545180823519,
    2001652014121143,1996755589763500,1997005874840245,2002725273853147,2002256179683372,
    1996664640350673,1997041661999172,2003918504605310,2002629524618406,1996272767952167,
    1995981159408602,2004565127897031,2004459103434382,1996679815240952,1994897033027932,
    2001538291270643,2004832977819907,1997408639908283,1996388622433576,2003190962531558,
    2004203056976601,1998140491251752,1992087828772205,2002986287823255],
   [2007233991777567,2000714929150673,1990958657504955,1997319532251788,2005161080600386,
    2004180226306379,1995417599654616,1991222142770115,2008269837504016,2003920567527886,
    1997133628187439,1996336977209053,2000866880125492,2008227058537987,2006777085243339,
    1989257572216120,1993690758010841,2012164328365907,2000931252724491,1993114217546088,
    1995819129326309,1998248118996007,2002855970340324,2009591419297579,1991007266044389,
    1986197920698474,2013020679614064,2008625297507327,1994233579307279,1991572181999294,
    1998646685810052,2007011733269887,2005018719201834,2002850838040230,1982249416610571,
    2000029186188403,2017771522527916,1997440132049599,1991083638991124,1997844735887021,
    2003745345197529,2001110154972397,2002424888196658,2006208479598104,1989170181629306,
    1990137026587140,2013315118356631,2006504185272673,1992175448830197,2000233013303736,
    2002361834131605,1993826353838242,1994711757591905,2006270705854587,2012489384001039,
    1998743423204621,1986722934715546,2002547152187471,2011797356154421,1988077081417729,
    1981672260570021,2013864790789398,2022806096709518,1992753103159284],
   [1989776309051283,2024967515068002,2030849358505152,1995917627295008,1986400867756780,
    2021372088084890,2040321494757774,2012085781400200,1984550312555793,2001434687571124,
    2035732012213734,2037699128456125,2008732030058941,1992746883924088,2011863016187832,
    2040675742353451,2043639164815865,2018884540315412,1997425168223646,2006972929376174,
    2044022755931452,2079074809688847,2083623802632721,2052708420825846,2007345208216779,
    1979626759890755,1993852333557333,2055316117032349,2150293348874024,2254119110177562,
    2341733401929755,2395784161209251,2409961485479490,2387969827778616,2339963558029652,
    2278341138269729,2214295535643833,2155854261561947,2107422683502361,2070336932359678,
    2043837015667964,2026050335731859,2014777791195552,2008002982094176,2004130921595373,
    2002025496190579,2000938924440117,2000409203258231,2000166717600211,2000063147448266,
    2000022117132209,2000007123462893,2000002096386190,2000000559041041,2000000133417422,
    2000000027899466,2000000004898636,2000000000644273,2000000000032946,1999999999986434,
    1999999999994228,1999999999998611,1999999999999762,1999999999999973],
   [2000000000000000]]
private def pv_m2_r512_6_6 : List ℕ := pNatCat
  [
   [1999920246801395,1999959204148957,2000064647169644,1999907391220507,1999842982736744,
    1999925147810634,1999927564631228,2000119961625758,1999858326054803,2000024775579855,
    2000062823399355,1999966330927696,2000034813937542,1999849253195220,2000052747048715,
    1999942383377079,1999912026926340,2000010352045369,1999943141030503,2000077840867890,
    1999984339465583,2000176604130723,2000153583537643,2000063765413479,2000088823538568,
    2000137580961704,2000017895660951,1999905198688643,2000074160816224,1999879818294270,
    1999903570663847,2000070161948064,1999997579593650,1999861325039690,1999964160602645,
    2000015244908162,2000124398693050,1999918250737308,2000028981752068,2000018530036000,
    1999994486801093,1999916919612758,2000032007015557,1999907770559387,2000153863381417,
    2000118105975468,2000071600607900,2000084982046625,2000093950216023,1999829585668922,
    2000030744955326,1999865656054378,2000077248612455,1999948866704170,1999939260267542,
    1999835629579341,2000075051293310,1999848206497745,1999939084204955,1999918539030344,
    2000147971652595,2000023095741933,1999884614684506,2000152738517977],
   [2000106071878165,1999925819008363,2000100608379068,1999915197238246,2000061920063126,
    2000239099221330,1999981121422634,2000197928072606,2000033091734356,1999909868044582,
    1999855066205380,1999768127454160,1999982511206451,2000239723353150,1999788924229081,
    2000396838405637,1999596532430154,2000191667858816,1999633713565208,2000223360452422,
    1999730905420594,2000486608181072,2000044182404201,1999744138244107,2000045352639802,
    1999973787225975,1999997037099129,1999764988926538,1999837642097817,2000324492096195,
    1999595669155519,2000301400621544,1999713114550596,2000214188670373,1999880245169094,
    1999818026215392,2000340279211701,1999756922067339,1999844029650085,2000411952476076,
    1999594333310418,2000490005911923,1999470340874352,2000733181189453,1999803040261183,
    1999370322599653,2000446237734875,1999692243940417,2000022829432803,2000332085892285,
    1999213359465988,2000447548936807,2000367888331528,1999154156734065,2000454955920856,
    2000227466341488,1999826825979609,1999891146463105,2000058149727101,1999957349882814,
    2000148221882341,1999477634580986,2000494815003703,2000320313793846],
   [1999618888106703,2000195211158903,2000209924456589,1999719641161033,2000391002049825,
    1999572210426248,2000212717877229,2000103964366580,2000030635228601,1999750257231672,
    2000106572795838,2000287983485144,1999950990859317,1999687877323800,2000015239153828,
    2000282541566632,1999843378171483,1999556048374827,2000777771392538,1999878973767178,
    2000132335984729,1999425548572391,2000418452549814,1999950380713504,1999866387420657,
    1999740345534556,2000096375510376,1999238333281925,2000414655549353,2000285085989577,
    2000051398187869,2000281291287716,1999668402698933,1999793481134366,2000034335788132,
    1999620696161606,2000257262507815,2000516145057389,1999583414011233,2000143616004704,
    2000111656180702,1999904033222846,1999519706894210,2000405588870886,1999261574863933,
    2000589902290345,2000172250808072,1999768069161352,2000067758189013,2000160098058740,
    1999468513392439,2000141973905067,2000548164578445,1999247318394926,2000592754152376,
    1999922272528704,1999399583166917,2001304464447451,1999761993246217,1998889692562564,
    2000774949468798,1999234035804666,2000158024671164,2000779759848216],
   [1999800573578110,1999314341560275,2001482433986287,1999611331850565,1999749122071235,
    2000650780167976,1999596112466246,1999652532106860,2000600522027303,1999373218645801,
    1999132308418385,2000675548315547,2000693779120152,1998650705059814,2001306223946195,
    1999608216725214,1999381431310828,2001479337302468,2000406652207322,1998763944803989,
    2000652042847667,1999698089865622,2000194245785652,2000013591658514,2000655426505455,
    1998809366235690,2000464317681480,2000646402429013,1998810206845605,2001094034882416,
    2000561535070091,1998890630542648,2001011688199921,1999991285838737,1998542125438508,
    1999379507700988,2001180460275827,1999527975693554,1998973389148270,2002100147339271,
    1999717262702625,1998852926290045,2001551911169137,1999646831269980,1997888335470349,
    2000255455744965,2000586086598445,1999108751436423,1999234626658053,2001152511111066,
    1998950890324492,2000299301672573,2000095104309679,1999712824346828,1998525251036224,
    2001475714462403,1999632021930518,1999215631691583,1999824351159006,1999218588446125,
    1999775144013154,1999543344337956,2000555651261060,1999580362215745],
   [2000017328314558,2000288240952822,1998215226335167,2000619228982386,2001467274309599,
    1998990845821324,1999198105104007,2000771608452130,2000194313062435,1999212464636801,
    2000622936200618,2001480169697524,1998491323746473,1999939391618836,2002211111466051,
    1998901722193457,1998356139322868,2001782361040777,1999862147482043,1998904725085139,
    2000734281205649,2001005780821467,1998825979294554,2000209621598730,1999785691824907,
    1999309123395404,2000977817065616,2001103006880131,1999812865379923,1998349411515518,
    2002140546989285,2000674390579995,2000399495307291,1998762965326581,2001681950357291,
    1999996033743647,2000129309354543,2000172155857453,1998735425415230,1999404218863240,
    2000433903905295,2002866110812810,1997367768465878,2000665898905534,2000724593526892,
    2001148421273221,1998375744629238,1999863313971723,2000516807608613,1999847351993810,
    1999388004203337,2000716447363459,1999524306050345,1997168239283544,2002327758294762,
    2000590275815188,1997623713053491,2000844375751850,2000803140530506,2000486518344587,
    1998623527367902,1999042671941656,2001926598895219,1998172121211279],
   [1998130968613855,2002699786816093,2000627744664489,1998927680918635,2000823501084327,
    2000781548892775,1999675836583705,1998788826486716,1999642822128328,2001216996566692,
    2000194659404023,1999895386539997,2001185335883389,2000051872228529,1999036082990648,
    1999992940417996,1999708822283508,1999394457022740,2000425855226016,2000227630831657,
    1999837009876493,2001170344168629,2001586126145201,1999998753972981,1999016286334729,
    1999852540087621,2001201522350320,2001044971681304,1999409874804711,1999362013164074,
    2000995554244599,2000565753742286,1998915071614666,2000709679184752,2002455811348886,
    1999808505278590,1997162210790507,2000721525280723,2002037435315798,1998713074136427,
    1996951229326762,2002781721316851,2003222527777956,1998097650889703,1996952774819700,
    2002471208272663,2003071290376529,1995712611237291,1996521267492984,2002673361813664,
    2002636134109348,1996167058310701,1994795476024374,2005098579214124,2002873036204206,
    1997114021622868,1994484595479407,2003433458248229,2004327211150005,1997783248602570,
    1995958919748449,2002807454266204,2005234148754900,1992875622245379],
   [1997656885002118,2001614841991194,2007817657853227,1999034701162704,1989638362426524,
    2001125866982818,2010063410241327,1998535990709727,1994107630133152,1999795227086786,
    2000787752681481,2006711456147863,1993734455564479,1990831371656713,2007970312512832,
    2008101714290920,1989377007071317,1994944761459941,2008059522314999,2000964294126335,
    2006252638571726,1996644953186440,1991079245471019,2010906801657793,2007744568140174,
    1992562321219072,1986153366550850,2009285777999089,2005961154532859,1994516205072777,
    1997615263381291,1990480207669606,2006560938332007,2013463800963862,1991450380365095,
    1986666874098400,2004503047956269,2013919988097533,1996328816263829,1990094762378006,
    2004279913477962,1999627675592919,1999392178206764,2009725378916258,1994713323390037,
    1986713487121974,2006494735421654,2011291130545020,1997325692710140,1993293315781119,
    1999895357435172,2002374259377758,1996871670681014,1999648672219712,2011261995520285,
    2001495604501546,1981819111361082,1996364285013912,2018299261850036,2000294963354568,
    1983894697458636,2008856763926783,2019859599911508,1987435761953735],
   [1976156284992907,2008753638452756,2018732462664586,1988277522029794,1982763338001838,
    2018632693713681,2032170347169115,2001126951440666,1983399509786289,2011183828040821,
    2037975487017005,2021359544411755,1990400741784521,1993786468249935,2024937514288843,
    2037833686056418,2016628965197923,1994156891061769,2002782623442638,2032303746827368,
    2046346688157367,2028183441368922,1999038187299658,1993407566530456,2023224887237030,
    2067045073553543,2090022784032244,2072829471057326,2025697783232973,1980615013887659,
    1971090204920350,2014026405760748,2103122932331219,2214406247731691,2318154472130037,
    2390298708615205,2418944018928836,2405064848817112,2358905764052459,2294678453770772,
    2225883701475752,2162497936881802,2110117338721410,2070489181017970,2042713978868897,
    2024536612667103,2013367869585954,2006902207217973,2003370384199609,2001551252885720,
    2000670089230952,2000270338359021,2000101331788241,2000035098341671,2000011169331743,
    2000003244796971,2000000854036682,2000000201703520,2000000042188214,2000000007664700,
    2000000001172179,2000000000142344,2000000000011945,2000000000000358],
   [1999999999999952]]
private def pv_m2_r512_6_7 : List ℕ := pNatCat
  [
   [1999963586335553,1999890468026631,1999995289379227,2000084463225885,1999917669219152,
    2000018076284114,1999775592270840,1999897347708301,2000065798214510,1999894367220726,
    2000035404157238,1999905313387473,2000021228937648,2000104028061968,1999922455688848,
    2000030064313631,1999925962666327,2000024191120269,1999950865818331,1999913282348388,
    1999991010104785,1999979923055539,1999939130376007,1999920742734637,2000169002048836,
    2000058310104493,2000027298125417,2000181131073005,2000154970856013,1999995719226398,
    2000149314568918,2000044663917127,2000027680895675,1999849003064637,1999983945207369,
    2000037830754545,2000029791381829,1999814140622208,2000013216660549,1999948220587458,
    1999996887023307,2000017376134910,2000040045355134,1999901833866166,2000190001238384,
    1999900966756999,2000000583502766,1999911856119856,2000014380345102,1999931629987098,
    2000138343505167,1999999499126152,2000208519991150,2000111495089916,1999994577714047,
    1999946035144581,1999947848875566,2000082998603511,1999972276624377,1999794723015585,
    2000127309801678,1999995679077380,1999763422312126,2000024735774124],
   [1999836865351550,2000018071269589,2000019778697161,1999891399108598,1999993831988952,
    2000183390972251,1999863524218015,2000360332730676,1999576678426653,2000412451966371,
    1999711484179747,2000226833511010,1999868059406304,2000401442052218,2000042146000729,
    2000072587804634,2000096372176079,1999617231485191,1999956998162094,2000075258980765,
    1999776447428905,2000258467572431,1999851867041802,2000458545932013,1999452264323448,
    1999901714754318,2000104297551663,1999966104480735,2000179369800174,1999896764813655,
    2000023000443776,2000450482966134,1999289188274356,2000570753724570,1999518655809730,
    2000080166916699,1999920987463935,1999762640390700,2000461733740064,1999492528640573,
    1999942964720905,2000606771428674,1999332947817150,2000092171666985,2000378190116537,
    1999431033859580,2000513675926429,1999668999689203,1999670028900188,2000636786592281,
    2000253370784214,1999390857269107,2000318031615364,1999964925653105,1999960540559775,
    1999826048059241,1999796508454109,2000323272533988,2000035532658462,1999268041994956,
    2000631201357280,1999832144969296,1999885527188979,2000052639148585],
   [2000119996487712,2000060306839450,1999964402544125,1999804929293867,1999916186838345,
    2000132153123236,2000124468626962,1999768682125566,2000274503323247,1999936682997160,
    2000577554631155,1999271360210813,2000318788813385,2000196032458677,2000094299201332,
    1999541596741569,2000230469330362,2000113136859619,2000194460486133,1999458627967413,
    2000379116499335,2000379216023069,1999447911627710,2000039691578309,2000013908218996,
    1999838915630044,2000355305677102,2000060058437655,1999795164120528,2000261342591323,
    1999609055911941,2000424799137558,2000085294349754,1999886234490607,1999265244409812,
    2000438587476540,1999299695380240,2000069291835857,2000586350840178,1999990383826041,
    2000019013758736,2000014747268505,1999647695698089,1999730428132783,2000615932078173,
    1999366028609525,2000099508568426,2000768817609391,1999351998985466,2000302185644468,
    2000396749090757,1998660869262468,2000868438312433,1999691023156664,1999607759788163,
    2000679787135617,2000329519290986,1998805594958275,2000777738117748,2000038214422139,
    1999454135926263,2000731596770326,1999633509756868,1999140147896036],
   [2001082009968829,2000308400749463,1999708692685344,1999768901728309,2000614091242270,
    1998671824683695,2000792462734928,2000291118238337,1998757267838881,2000697805714261,
    2001125882186945,1998597783353734,2001066948423985,2000051779651997,1999855665812408,
    2000171462449858,2000640367818576,1999003216001281,1999270540161028,2001092224881532,
    1999368784224098,1999905023302285,2000681507574485,1998518408885764,2000807501907586,
    2001032417533438,1999413054455058,2000159352582494,2000504515083970,1999709500197550,
    1999303521832037,2001469370032240,1999796563825906,1998493199724222,2001557228189873,
    2000256389881598,1998028233434998,2001163122068252,2000724337973969,1999500938847718,
    1999974546722050,2001764124484137,1998130585862114,1999607918434828,2000439828167909,
    2000002501472436,1998406470992016,2000968877523192,2000534277253228,1999539949741808,
    2001256843538451,1999418322610215,1999391587801638,1999922206168508,2000116339465088,
    1999273630930622,1998920461204615,2000770162034447,1999632536962134,1999869677484750,
    2000378062317549,1998807169506195,1999946747174178,2000848755695628],
   [1999174861144047,1999751395194485,2000540176613401,1999590698906650,1997946183705794,
    2000012303962008,2001525218316300,1998902120539339,1998828753455372,2001599097139807,
    1998667262865941,1999023993682407,2001725921354911,2000247649733482,1997802938117484,
    2000876777133757,2001060561372279,1998497979740189,2000458009282530,2000348168368767,
    2000535562883740,1999248833073756,2001625585246130,1998939775167174,2000437810068690,
    1999987088773416,1999956228453884,1998929703949847,2000626421947794,2002089492099337,
    1998276245148486,1999530142155005,1999425976986375,2002128285346566,1998187207508914,
    2001052506065148,1999652120108255,1999765319906017,2001011710642434,2001279680764114,
    1998913331366812,1999457319710833,2002209653946847,2001194099210248,1999372103950947,
    1998222908211956,2001686864891492,1999859733015898,1998160243632746,2002155744692644,
    1999308299574960,1999319066775328,2002249626559664,1999872192143836,1999063375193163,
    1999298571791467,2001161013605872,2001384962420487,1997437832396622,1999690716037409,
    2002146337645055,1998099033303278,1998540213300455,2001481178435606],
   [1999969938356189,1998905709647976,2000202724749806,2001219663317512,2000130856728115,
    1998404555994929,1999608969850996,2000605925300851,1998930852721621,1999433475417767,
    2001297209558013,2000565371585702,2000050704666043,2000527751359859,1999615907629167,
    1999252105135798,2000120887166551,2000070330241218,2000112164985547,2000979508912716,
    2000661170627396,1999618696182300,1999565829945867,2000233358465069,2000113064244868,
    1999227894930679,1998571211264043,2000689517693464,2002042490451914,2000726307426343,
    1998501309482998,2001010073363897,2001262760365605,1999438957508156,1998991958911843,
    2002474178596854,2001078546744290,1997019245565767,1999616811679432,2003104765999812,
    2001281825378611,1996918486142619,2000449153962507,2004518151881438,1998074218541623,
    1996696459900810,1999499362625463,2005399016841600,1997882645070238,1996427146310005,
    2002318807892536,2004900264256808,1997827464999555,1994578783716838,2003132795913587,
    2002745965956953,1999285638792064,1991292225408209,2003582600542677,2004499793327923,
    1996265823067835,1996805636070265,2001032086594647,2003461716024097],
   [1998896142307651,1993575812500495,2002913481214861,2010548704286117,1992192868635529,
    1993599861659961,2003248987837187,2004535386699052,2002031164170636,1994503949496577,
    1994355605667209,2007927115757787,2007208655162561,1985937246316367,2001114479714096,
    2011030689405784,1994937538457847,1998221556719255,1995200452231096,2002434611296992,
    2004891785868879,2000807663680905,1987839703927723,1997460648510673,2017709708791307,
    1995538757432080,1990980982966074,2004793221086420,2004688277623825,2006650948625986,
    1996896559708921,1989512578612554,2001811719991721,2012346341329766,1998825891418831,
    1981433577965420,2000800618034879,2015979946420093,1995055683890427,1992069594549873,
    2002845474557400,1997242801489969,2002547085921678,2008221371973875,1993066125942708,
    1990458866788925,2006738259846846,2009845517583801,1996413997275149,1990160646447916,
    2001160853986997,2007108331775145,1996809628507147,1998524541457536,2009472826434423,
    1995407690937471,1983482276415186,2008450025623627,2019670094418756,1990032572853478,
    1983655966157190,2012547897065399,2009221182475439,1980744237200183],
   [1993729005079068,2024719726066997,2008799576446507,1977710103281849,1992608116606359,
    2019525613956190,2002027851984363,1974345335844679,1992392654409569,2026812127026844,
    2019527550217485,1987976480996244,1989829994736040,2023083451593143,2034276745637143,
    2008268040004815,1988253985597306,2004825282137731,2032176434257355,2030934717080084,
    2004879671663959,1992224885662306,2012240096353164,2041375580402056,2044349096830273,
    2016620686827876,1989054954419473,1994536152829561,2035017718842403,2079951822781786,
    2093087139919741,2061701215074237,2005815810762267,1964201361548339,1970390023101628,
    2035028759250610,2142909881640385,2262730185758823,2361827135388590,2418125844437897,
    2425115390684065,2389957606995964,2327638039801635,2254601909289462,2184191011654484,
    2124625254094054,2079121311644385,2047239465557351,2026557409755019,2014060655412746,
    2007003373065750,2003274109149539,2001431744211102,2000583045215935,2000219954339448,
    2000076413786959,2000024282248572,2000007002999255,2000001815715333,2000000418164139,
    2000000084160440,2000000014457329,2000000002042104,2000000000221683],
   [2000000000015765]]
private def pv_m2_r512_6_8 : List ℕ := pNatCat
  [
   [2000012254056853,1999950380043508,1999841062045344,2000072970982167,1999952166981107,
    2000012814934278,2000133094083698,1999823064643375,1999911109668979,1999905603599960,
    1999889103578229,2000080770202177,1999888818747651,1999962379379917,1999962476047824,
    2000010903200434,2000065154309927,1999973714685458,1999992864356476,1999972532373611,
    2000067239518084,1999908384799690,1999915275502816,2000050004385157,2000006855489330,
    1999797364433037,2000030586923106,1999974035344108,2000010630825341,1999974248838562,
    2000135245752845,2000087893105272,2000134515594257,1999985991037130,2000204510363755,
    2000162764555527,2000037541230528,1999872660013252,2000117616896360,1999871824174987,
    2000103672916080,1999945289283505,1999941876084413,1999876254739985,2000079574464131,
    1999886921127018,2000011244049186,1999981756582255,1999990331313047,2000089802731071,
    2000010736778869,1999974675357261,2000009670725490,1999912105595514,2000017805495319,
    1999929845965840,1999847906726030,2000343588063326,2000074555942215,1999991795872262,
    2000093733460272,2000100535539706,1999870424765691,2000232851702807],
   [1999560450618617,2000428650232237,1999645057321151,2000276047845939,1999695938956844,
    2000020623937213,1999877183929318,2000023890133014,1999933072890149,1999766520052525,
    2000158312113632,1999995229455337,1999825818993049,2000396886331281,1999686345097567,
    2000336452423003,1999785173418510,2000109921765711,1999888533805661,1999929795114169,
    2000473024859699,2000110413660489,1999834241019635,2000487628076982,1999484236157760,
    2000429105289498,1999263816383725,2000118214812324,2000415745156855,1999716691872738,
    2000263553013043,1999751513015831,1999916375365994,2000203217223842,1999444496289018,
    2000346501399461,2000303892707445,1999267962771437,2000778617205215,1999951896141905,
    1999621407313998,2000264546242589,1999931972274698,1999620892282064,2000452425198374,
    1999525914461678,1999859601584965,2000471483121718,1999808620803346,1999568713683953,
    2000312358108895,1999881500312674,2000471069330376,1999375080527474,1999846490185773,
    2000480151323963,1999807783205590,1999788916606041,2000364793705268,2000151432120879,
    1999884139140213,1999819386942872,2000211489879165,1999743639330086],
   [2000301466476449,1999437425766610,2000393187056146,1999699281701517,2000195980870843,
    1999726329782361,1999922478776507,2000105895883601,2000440118563567,1999537397977323,
    2000048396635925,2000167428107542,1999979894355630,1999838451568668,1999602527381695,
    2000539523097377,2000228391968410,1999448069946892,2000226405916867,2000519101009167,
    1999541715269812,2000314458801284,1999759146143011,2000317114643550,1999861220291859,
    2000122591793904,1999568650247132,2000533530149439,1999876748552829,1999955142576090,
    2000473020506530,1999448873090446,1999778818546505,2000334502957735,2000185642320829,
    1999596471898852,2000407070587287,1999823825317814,1999689380995298,2000706979348680,
    1999863187659724,1999713503319383,2000989036910449,1998495890273242,2000072966832718,
    2000225186218199,1999581067540115,2000274884281514,2000693686544015,1999090581746514,
    2000457159695679,2000369188115884,1998898551716507,2000336152767984,2000519787454762,
    1998979613204176,2000877455994043,2000154996397341,1999863222861216,1999648832001436,
    2000537037233282,1998905778401035,2000270187339114,2000983048789099],
   [1999183027600700,1999416055238171,2001409926918613,1998694260824193,2000819394849617,
    2000386481777890,1998805067348292,1999955878364484,2000837751649963,1999930277794411,
    1999462340042375,2000938411385110,1999880427798979,1999117785310309,2001246951987147,
    1998993429113919,1999411407485761,2001168319135255,1999445717872646,2000041367292448,
    2000290618002703,1999865410186005,2000002972108089,2001165609241328,2000130837217907,
    1998566913745626,2000599131719585,2000792976522939,1998222290335709,2001237756544120,
    1999949707214107,1998695066509294,1999763074082501,2002181322230939,1998525645911591,
    2000017768800568,2001213347335357,1999875774284461,1999010802535720,2000928370159433,
    2000659325781436,1998433826536158,2001322648687987,2000311250879711,1998732610132044,
    2000113209514460,2000253808742235,2000349162469235,1999965585081218,2000728368767638,
    1999809767673756,1999579795543594,2000873264871649,1999129697701134,1998717861324032,
    2000628374434988,1999770315250688,2000224668475265,2000543096313084,1999837707014563,
    1999899435434631,2000726041914062,1999797994307424,1998704787626191],
   [1999401115419537,2001363063706632,1998490523787970,1999297547575241,2001706336889724,
    1999314472568008,1997904067570962,2001096385342719,2001163113525310,1997940016697065,
    2001442566358512,1999581266052562,1998670335562362,1998803312919898,2002051703505514,
    1998705340572373,1999242423204683,2000215258658788,1999678488513808,1999925475597030,
    1999492382190299,2000992285032271,1998245863569862,2001539789353412,1999086822446823,
    2000160590789008,1998915794541992,2001689605165229,1999698991314971,1998689230765327,
    2001390694583857,2001409915820793,1999111708729584,1999097570331334,2000658246143150,
    1999417550471664,2001047827738668,2000323117868092,1999301229838037,1999444753586634,
    2000004051707864,2002238759057125,1997866145317637,1998298422548369,2003183768761728,
    1999571328132633,1999076961072182,2000873837763869,1999649747221490,2000655489654786,
    2000880661011673,2000964469593561,2000108087594498,1998673221807308,2001643124800492,
    2000829978190358,1996931053036381,2000266701180581,2002562694922553,1999259738434476,
    1999081264824632,2001142611938006,2000647815652420,1999179471408940],
   [1999682063836395,2001269189538145,2000074236139141,1998424354954821,2000287148773730,
    2000844715963212,1998616535270741,1999078442830218,2000615467604688,1999936588667874,
    1999867316104996,2000570508129785,1999972333353081,1999709738606580,1999730596692509,
    1999173729637773,1999156017214161,2000338077193951,2000329503868320,2000515243617863,
    2000286417605414,2000665252304016,1999543811265241,1999470399915290,1999060154534405,
    2001168220879622,2000968428552338,1999290585271007,1999510650228344,2001767246023667,
    2001393961527610,1997384853834217,1999009231632928,2001434790336717,1999514633667784,
    1998939823971242,2000730192936260,2003924024331355,1996895147353744,1999036760965550,
    2002300157504242,2003082658657493,1997111534893073,1998171665279339,2004078256519390,
    2000544006959746,1996875218240042,1998298117304381,2007335725564212,1998498216137316,
    1997451325147224,1999160532063329,2004493260954593,2000287021278589,1992732121052869,
    2002159600732306,2006407061789230,1997519541055815,1995775100330910,2002685472429614,
    2002495311388332,2002057964555476,1991942947228799,2000448283138727],
   [2007517417789780,1993773815742505,1994676054170624,2005670033116052,2003126763512144,
    1994381734360988,1997706150128957,1997698736451592,2008739004707045,2005051189310479,
    1982891590512425,2004943839695491,2008770112193696,1996223355250588,1993784552114280,
    2002919116213661,2004051591501924,1997560941090629,2000653163492809,1992629672157080,
    2006273563547381,2011116735647628,1985965700991657,1994959232220325,2010582763410043,
    2002481297480910,1994272931976969,1993891281748744,2001341042570347,2005759392381406,
    2001976964451794,1990853091669859,1994443561397046,2017595135401759,2006681869489643,
    1982037188734833,2001091009928792,2014130081831386,1996873509591544,1994620048396957,
    1998428133012660,1996163089388415,2004122032729368,2005646695222154,1992982593008883,
    1991501662670933,2005319282102652,2010095582524140,1995271202906661,1988567913505585,
    2005144645232590,2009010925629531,1993263323685876,1998208289460503,2008670424690252,
    1991606457085548,1989240675938381,2016783435370831,2011330659423624,1979503868750158,
    1991290957127495,2019741666188640,2002104750692236,1982190618395246],
   [2006749373965925,2018529905346937,1987019342679219,1978515100176125,2012649622464733,
    2020600708659732,1989148058021253,1984345715542741,2014663112581415,2016727431436515,
    1982813420078628,1975098832344561,2008044547283144,2024509748561527,2000064442941248,
    1981995186771292,2003825542338150,2031047791244326,2022266324309800,1994885615138940,
    1993342238979743,2020070023371224,2035292953342525,2017448377569022,1992726981408184,
    1997162292890672,2028407236098441,2049383210378375,2034039775873141,1997878567314237,
    1981188440071952,2007314482395087,2059582808538298,2096200280404201,2085844286200590,
    2032549781257479,1972711211175203,1950673671870287,1992303493877006,2092595497706419,
    2221229320622335,2339170513736827,2415576167650250,2437228923582170,2408655580274969,
    2345852652241613,2268182048802899,2192006425050024,2127583563386854,2078950669422002,
    2045591523981247,2024586941982219,2012375848216868,2005803247138559,2002526878788668,
    2001017029372945,2000376153189459,2000126913485996,2000038711368104,2000010553213445,
    2000002532521397,2000000523601628,2000000090194864,2000000012185581],
   [2000000001115768]]
private def pv_m2_r512_6_9 : List ℕ := pNatCat
  [
   [2000001607751179,2000087160158964,1999855714146101,1999908700196761,2000063700163917,
    1999851493403632,2000011376347336,2000133195235383,1999952350275913,2000059754914109,
    1999881466081677,1999856663073343,1999942997386921,1999937473471488,2000009991361520,
    1999919500505572,1999956741244287,1999912522259965,2000021173538688,2000053345715137,
    1999998513948377,1999883254914749,2000156561853513,1999983621333230,1999933336982349,
    1999929290981936,2000089555727510,1999931934072026,1999986025331339,1999879318056750,
    2000019642674212,1999934277744436,1999979671096637,1999832402120385,2000233975038349,
    1999995553819610,2000031596879207,2000031621485267,2000190454390130,2000071200778576,
    2000218088783405,2000058524807045,1999943448490662,2000051981423053,2000024107160433,
    1999999961653126,2000025483427746,1999904271063665,1999967442311975,2000028403944519,
    1999841372087513,2000100077003985,1999836721039198,1999984678238404,2000094931670123,
    2000109622567273,1999656220046437,2000492707150107,1999638417760744,2000323774637849,
    1999565725157701,2000098340070536,1999959951834894,2000075258586922],
   [2000066736341659,2000025209165014,2000179816117767,2000044059131571,2000018733955125,
    2000166998027553,1999563065923181,2000483460729408,1999751388116418,2000058589033489,
    1999955285658184,1999908234236475,2000044445590269,1999870430564755,1999851469943327,
    2000258782424967,1999310825377649,2000613971320612,1999578377142209,2000032254488510,
    2000182970767485,1999809448313549,2000515954902726,1999663404212672,1999767268784478,
    2000388744091407,1999745357067288,2000121941344093,2000249410624991,1999804146484247,
    2000907915050077,1999537794749302,1999702627102863,2000400358344317,1999639076829818,
    1999683139395804,2000732541806078,1999657422643955,1999902661044447,2000268047540026,
    1999729173883592,1999817920337176,2000405573409886,1999320784594387,2000377271747741,
    2000170543667773,1999898793503571,2000061019818205,1999878615619948,2000253544896211,
    2000133119316423,1999332448917610,2000106329678857,2000269909710292,2000097857118083,
    1999205115157791,2000507178052228,1999748997546661,2000251039782001,1999683759893272,
    2000190797651594,1999988707707940,1999904456972731,1999706658592708],
   [2000215185733677,1999903646515671,2000206734580174,2000092424984416,1999703527427547,
    2000369629357439,2000011634680060,1999801545088256,1999880500111246,2000045104002424,
    2000175648012502,2000065526871036,1999084800684633,2000728820570711,1999900621979369,
    1999736371628333,1999806146964523,2000611935785279,1999803395267987,1999959630713778,
    1999964737756893,1999745593382356,2000446502125713,1999608144756389,1999904542406635,
    2000315978885948,2000101273002335,1999690369730010,2000384314086456,2000057963873479,
    1999634926842167,2000439902267385,2000414524199918,1998903317561106,2000921361201960,
    1999448763324004,2000104369021724,2000737074002550,1999540092828697,1999620275349287,
    2000763129947113,1999330062446630,1999924791072003,2000813514114748,1999418829219700,
    1999697276118744,2000865192726442,1998833197836195,2000873710722911,2000518150397349,
    1999701681736481,1999533435336127,2000528864618456,1999199450279329,1999673485323986,
    2000528734453037,2000036900617623,1999144355031954,2001619850635165,1998988642332745,
    1999680910635239,2001110481559376,1998886444153601,1999647560871921],
   [2000797237221872,2000034657036794,1999830426761150,2000407296182179,1999947898302414,
    1998725777426631,2001273345170398,2000245533018519,1998465324317323,2000988583143080,
    1999757212092868,1999709065729990,2000808810816021,1999821278204167,1999313453147593,
    2000295566788606,2000198684165529,1999543245897993,1999873972730954,2001197014419595,
    1998640490739313,2001240875654975,2000211089205994,1998852408038445,1999532751989274,
    2001894998572529,1998666069886935,1999478241859198,2001185633687573,1999191627399096,
    1999733499214854,2001370939695590,2000759013261220,1998082005647255,2000844464587659,
    2001177830718725,1998433919132823,2000585727513057,2000317724830062,1999067865388894,
    1999653361527026,2000595598785526,1999988496865638,1999333042468715,2000845610102702,
    2000485616318318,1999141128039916,2000733272998852,1999780947563826,1999806634915350,
    2001055146480730,2000007516540929,1999074227631144,2000284260477937,1999944956005319,
    2000074470310516,1999699625683923,2000679360533780,1999863878015193,2000390335092964,
    2001257591361670,1998645680677961,1998996995783666,2000852214871622],
   [2000406738674017,1997095976253305,2002238031275265,2000373298542314,1999112796352861,
    2000135349591261,2001927549240589,1998369268225647,1998941935175151,2001331910586332,
    1998524128304863,2000240330184552,1999842658467351,2000917026933966,1997162689106009,
    2001126007990390,1999939093144794,2000484937927372,1999525576702143,1999911628627655,
    1999479348060691,1999312338236112,2000755807857416,1999200116504055,1998984456563971,
    2000429725646583,2000539595848205,1997846189827482,2000403230431611,2001260875790546,
    1998689144725434,1999866492000055,1999750553256607,2000815087468499,1999674164086152,
    1998833681985374,2001105761249672,1998735775934111,2000854383346038,2002767697471368,
    1997495395342559,1999040393004458,2002128660296990,2000052526044254,1999228428577639,
    1999511023873642,2000962378615541,2000565971457029,1998920714764111,2000579210622761,
    1999679582828663,1998541843899131,2001977098053046,2000874304642555,1997460207930558,
    2000197444131875,2002201947162495,1999684436526150,1998988706457467,2001328584692858,
    2001930280952391,1999541616773310,1999099098320738,2001010154056185],
   [1999923028274965,1998588102503489,2000812265324517,2001245522554003,1999088817022044,
    1999819162387377,2000981304786642,2000161359520685,1999643009161503,2000367741209194,
    1999872192110889,2000320056083333,1999803450764814,1999702069716097,1999149240647143,
    2000099175203065,1999360474008813,1999915593911640,2000151172503187,2000482376328923,
    2000477070993422,1999324723724600,1999505824904332,1999553298506476,1999763141965633,
    1998863682872705,1999947287948183,2003047044838206,1999007795661376,1999183417216531,
    1999285261660313,2002941477133960,1997860234975743,1998483403753656,2002129350051894,
    2001222877465753,1998926909339836,1999405808157179,2003929490052373,1997294555582617,
    1997759776684028,1999225963658919,2005532447015436,1996974038452892,1997093289688956,
    2004040506615711,2001484770861791,1998286955659668,1997719099426833,2004208271389455,
    2003092527471124,1994754799340712,1997408845703458,2008098398211390,1997717040397559,
    1996981382003666,2001568374072878,2003120379632312,2002740650889143,1992879539354150,
    1999199873925316,2007626049501248,1998455681006595,1991677154738338],
   [2006533019441347,2004088139417628,1993732190471353,2003354255276847,1996109142144884,
    2006927559842014,1998735801885021,1988092513280568,2005474355381443,2009416811377307,
    1993709754588680,1988524121923057,2008693178893965,2003134430655218,1995274398108788,
    2001646939686062,1995197151918296,2006005796224299,2003732585599944,1987641752993702,
    2002484178571152,2010810582305099,1995850270756639,1990394836985509,2002987942868651,
    2008224969162471,1998684482623239,1995943708829815,1996020844767004,2003314768276254,
    2011388366210152,1990491886567978,1986378272627507,2015209135627680,2006752593864970,
    1983112623475608,1997402392311315,2009586042290299,2001929562713508,1999063383216637,
    1998073170598789,1999076232476229,2006135859434234,2005841334086491,1994534901323848,
    1990312013018588,2004245318636445,2010879216446398,1992284139118501,1987521909638555,
    2008875051086840,2006910793699111,1989351668263977,2000866648689866,2008135683476740,
    1988955069883426,1996310491877373,2019455842842284,1998753919737980,1976633141467268,
    2005226767383197,2021115820165383,1990763613803174,1985390794137483],
   [2014024732986285,2007148197583182,1980339522042684,1997572976813302,2024056781330057,
    2001742571645101,1975918767802611,1998235577761276,2020333009616694,1997988020686139,
    1980134005871381,2005590002276301,2025142422998001,1999303437556782,1973529350143278,
    1991926311473134,2019136609923312,2008320990365856,1982575900634645,1989854103123991,
    2020605985514729,2027197616146286,2002811366788101,1989334457843062,2009615899665153,
    2033896598992705,2026378243860796,1997524247120847,1988713164410939,2015714111461724,
    2047783236352864,2045712154765873,2008934642321869,1977292721287062,1988985779086368,
    2041454273585259,2092904557929809,2099178511454121,2050764964420073,1980573536755006,
    1940674693600224,1968640567078652,2066756379614031,2204057993705163,2335177047331014,
    2422133638539627,2447645576631482,2416327364475155,2347082014572139,2262767941541266,
    2182138207246769,2116184957144480,2068408534251532,2037221839408544,2018707137851010,
    2008665858831465,2003685774580927,2001431056244262,2000503204501619,2000158538851706,
    2000044101533298,2000010605790217,2000002133500382,2000000338242219],
   [2000000036572994]]
private def phb_m2_r512_6 : List ℤ := uOfNatHb pb_m2_r512_6
private def pvi_m2_r512_6 : List ℤ := bDec bZ pv_m2_r512_6_0
private def pvo_m2_r512_6 : List ℤ := bDec bZ pv_m2_r512_6_9
private def pwalks_m2_r512 : List RkmSegWalk := [
  ⟨rkmHbPack_m2_r512_s0, rkmViPack_m2_r512_s0, rkmVoPack_m2_r512_s0⟩,
  ⟨rkmHbPack_m2_r512_s1, rkmViPack_m2_r512_s1, rkmVoPack_m2_r512_s1⟩,
  ⟨rkmHbPack_m2_r512_s2, rkmViPack_m2_r512_s2, rkmVoPack_m2_r512_s2⟩,
  ⟨rkmHbPack_m2_r512_s3, rkmViPack_m2_r512_s3, rkmVoPack_m2_r512_s3⟩,
  ⟨phb_m2_r512_4, pvi_m2_r512_4, pvo_m2_r512_4⟩,
  ⟨phb_m2_r512_5, pvi_m2_r512_5, pvo_m2_r512_5⟩,
  ⟨phb_m2_r512_6, pvi_m2_r512_6, pvo_m2_r512_6⟩,
  ⟨rkmHbPack_m2_r512_s7, rkmViPack_m2_r512_s7, rkmVoPack_m2_r512_s7⟩
  ]
private abbrev dP_0 : Prop :=
  bSlideChk 9 513 pb_m2_r512_4 pv_m2_r512_4_2 pv_m2_r512_4_3 = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop :=
  bSlideChk 9 513 pb_m2_r512_4 pv_m2_r512_4_3 pv_m2_r512_4_4 = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop :=
  bSlideChk 9 513 pb_m2_r512_4 pv_m2_r512_4_4 pv_m2_r512_4_5 = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop :=
  bSlideChk 9 513 pb_m2_r512_4 pv_m2_r512_4_5 pv_m2_r512_4_6 = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop :=
  bSlideChk 9 513 pb_m2_r512_4 pv_m2_r512_4_6 pv_m2_r512_4_7 = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop :=
  bSlideChk 9 513 pb_m2_r512_4 pv_m2_r512_4_1 pv_m2_r512_4_2 = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_4 pv_m2_r512_4_10 pv_m2_r512_4_11,
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_6 pv_m2_r512_5_7
  ] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_4 pv_m2_r512_4_11 pv_m2_r512_4_12,
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_7 pv_m2_r512_5_8
  ] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_4 pv_m2_r512_4_12 pv_m2_r512_4_13,
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_8 pv_m2_r512_5_9
  ] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_4 pv_m2_r512_4_13 pv_m2_r512_4_14,
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_9 pv_m2_r512_5_10
  ] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_4 pv_m2_r512_4_7 pv_m2_r512_4_8,
    bSlideChk 8 513 pb_m2_r512_6 pv_m2_r512_6_0 pv_m2_r512_6_1
  ] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_4 pv_m2_r512_4_8 pv_m2_r512_4_9,
    bSlideChk 8 513 pb_m2_r512_6 pv_m2_r512_6_1 pv_m2_r512_6_2
  ] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_4 pv_m2_r512_4_9 pv_m2_r512_4_10,
    bSlideChk 8 513 pb_m2_r512_6 pv_m2_r512_6_2 pv_m2_r512_6_3
  ] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_0 pv_m2_r512_5_1,
    bSlideChk 8 513 pb_m2_r512_6 pv_m2_r512_6_3 pv_m2_r512_6_4
  ] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_1 pv_m2_r512_5_2,
    bSlideChk 8 513 pb_m2_r512_6 pv_m2_r512_6_4 pv_m2_r512_6_5
  ] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_10 pv_m2_r512_5_11,
    bSlideChk 8 513 pb_m2_r512_6 pv_m2_r512_6_5 pv_m2_r512_6_6
  ] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_11 pv_m2_r512_5_12,
    bSlideChk 7 513 pb_m2_r512_5 pv_m2_r512_5_14 pv_m2_r512_5_15
  ] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_12 pv_m2_r512_5_13,
    bSlideChk 7 513 pb_m2_r512_5 pv_m2_r512_5_15 pv_m2_r512_5_16
  ] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_13 pv_m2_r512_5_14,
    bSlideChk 7 513 pb_m2_r512_6 pv_m2_r512_6_6 pv_m2_r512_6_7
  ] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_2 pv_m2_r512_5_3,
    bSlideChk 7 513 pb_m2_r512_6 pv_m2_r512_6_7 pv_m2_r512_6_8
  ] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_3 pv_m2_r512_5_4,
    bSlideChk 7 513 pb_m2_r512_6 pv_m2_r512_6_8 pv_m2_r512_6_9
  ] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := rkmAllTrueF [
    bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_4 pv_m2_r512_5_5,
    bSlideChk 9 513 pb_m2_r512_4 pv_m2_r512_4_0 pv_m2_r512_4_1
  ] = true
private theorem bk_21 : dP_21 := by decide +kernel
private abbrev dP_22 : Prop :=
  bSlideChk 8 513 pb_m2_r512_5 pv_m2_r512_5_5 pv_m2_r512_5_6 = true
private theorem bk_22 : dP_22 := by decide +kernel
private abbrev dT_0 : Prop :=
  rkmCheckRowFromWalks 2 4096 512 [8, 24, 64, 144, 256, 448, 448, 448]
    [10277869, 10634078, 7977165, 8864612, 9902763, 7112570, 3861992, 3096805]
    [6, 16, 30, 67, 119, 126, 69, 55] rkmMasksPack_m2_r512 pwalks_m2_r512 rkmRowPack_m2_r512 = true
private theorem ptail_0 : dT_0 := by decide +kernel
private theorem pdim_m2_r512_l256 :
    Nat.add (highdNatMin (Nat.mul 256 2) 512) 1 = 513 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m2_r512_l448 :
    Nat.add (highdNatMin (Nat.mul 448 2) 512) 1 = 513 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pw_m2_r512_4_0 :
    pWOk 9 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_1 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_21))
private theorem pw_m2_r512_4_1 :
    pWOk 18 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_2 :=
  pChnN 18 pw_m2_r512_4_0
    bk_5
    (rfl : 9 + 9 = 18)
private theorem pw_m2_r512_4_2 :
    pWOk 27 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_3 :=
  pChnN 27 pw_m2_r512_4_1
    bk_0
    (rfl : 18 + 9 = 27)
private theorem pw_m2_r512_4_3 :
    pWOk 36 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_4 :=
  pChnN 36 pw_m2_r512_4_2
    bk_1
    (rfl : 27 + 9 = 36)
private theorem pw_m2_r512_4_4 :
    pWOk 45 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_5 :=
  pChnN 45 pw_m2_r512_4_3
    bk_2
    (rfl : 36 + 9 = 45)
private theorem pw_m2_r512_4_5 :
    pWOk 54 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_6 :=
  pChnN 54 pw_m2_r512_4_4
    bk_3
    (rfl : 45 + 9 = 54)
private theorem pw_m2_r512_4_6 :
    pWOk 63 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_7 :=
  pChnN 63 pw_m2_r512_4_5
    bk_4
    (rfl : 54 + 9 = 63)
private theorem pw_m2_r512_4_7 :
    pWOk 71 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_8 :=
  pChnN 71 pw_m2_r512_4_6
    (rkmHd
    bk_10)
    (rfl : 63 + 8 = 71)
private theorem pw_m2_r512_4_8 :
    pWOk 79 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_9 :=
  pChnN 79 pw_m2_r512_4_7
    (rkmHd
    bk_11)
    (rfl : 71 + 8 = 79)
private theorem pw_m2_r512_4_9 :
    pWOk 87 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_10 :=
  pChnN 87 pw_m2_r512_4_8
    (rkmHd
    bk_12)
    (rfl : 79 + 8 = 87)
private theorem pw_m2_r512_4_10 :
    pWOk 95 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_11 :=
  pChnN 95 pw_m2_r512_4_9
    (rkmHd
    bk_6)
    (rfl : 87 + 8 = 95)
private theorem pw_m2_r512_4_11 :
    pWOk 103 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_12 :=
  pChnN 103 pw_m2_r512_4_10
    (rkmHd
    bk_7)
    (rfl : 95 + 8 = 103)
private theorem pw_m2_r512_4_12 :
    pWOk 111 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_13 :=
  pChnN 111 pw_m2_r512_4_11
    (rkmHd
    bk_8)
    (rfl : 103 + 8 = 111)
private theorem pwalk_m2_r512_4 :
    pWOk 119 513 pb_m2_r512_4 (bDec bZ pv_m2_r512_4_0) pv_m2_r512_4_14 :=
  pChnN 119 pw_m2_r512_4_12
    (rkmHd
    bk_9)
    (rfl : 111 + 8 = 119)
private theorem pseg_m2_r512_4 : muxFastIterFullT16 119
      (Nat.add (highdNatMin (Nat.mul 256 2) 512) 1)
      phb_m2_r512_4 pvi_m2_r512_4 = pvo_m2_r512_4 :=
  bSeg_mk pdim_m2_r512_l256 pwalk_m2_r512_4 rfl rfl rfl
private theorem pw_m2_r512_5_0 :
    pWOk 8 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_1 :=
  bSlSndNN (rkmHd
    bk_13)
private theorem pw_m2_r512_5_1 :
    pWOk 16 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_2 :=
  pChnN 16 pw_m2_r512_5_0
    (rkmHd
    bk_14)
    (rfl : 8 + 8 = 16)
private theorem pw_m2_r512_5_2 :
    pWOk 24 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_3 :=
  pChnN 24 pw_m2_r512_5_1
    (rkmHd
    bk_19)
    (rfl : 16 + 8 = 24)
private theorem pw_m2_r512_5_3 :
    pWOk 32 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_4 :=
  pChnN 32 pw_m2_r512_5_2
    (rkmHd
    bk_20)
    (rfl : 24 + 8 = 32)
private theorem pw_m2_r512_5_4 :
    pWOk 40 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_5 :=
  pChnN 40 pw_m2_r512_5_3
    (rkmHd
    bk_21)
    (rfl : 32 + 8 = 40)
private theorem pw_m2_r512_5_5 :
    pWOk 48 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_6 :=
  pChnN 48 pw_m2_r512_5_4
    bk_22
    (rfl : 40 + 8 = 48)
private theorem pw_m2_r512_5_6 :
    pWOk 56 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_7 :=
  pChnN 56 pw_m2_r512_5_5
    (rkmHd
    (rkmTl
    bk_6))
    (rfl : 48 + 8 = 56)
private theorem pw_m2_r512_5_7 :
    pWOk 64 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_8 :=
  pChnN 64 pw_m2_r512_5_6
    (rkmHd
    (rkmTl
    bk_7))
    (rfl : 56 + 8 = 64)
private theorem pw_m2_r512_5_8 :
    pWOk 72 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_9 :=
  pChnN 72 pw_m2_r512_5_7
    (rkmHd
    (rkmTl
    bk_8))
    (rfl : 64 + 8 = 72)
private theorem pw_m2_r512_5_9 :
    pWOk 80 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_10 :=
  pChnN 80 pw_m2_r512_5_8
    (rkmHd
    (rkmTl
    bk_9))
    (rfl : 72 + 8 = 80)
private theorem pw_m2_r512_5_10 :
    pWOk 88 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_11 :=
  pChnN 88 pw_m2_r512_5_9
    (rkmHd
    bk_15)
    (rfl : 80 + 8 = 88)
private theorem pw_m2_r512_5_11 :
    pWOk 96 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_12 :=
  pChnN 96 pw_m2_r512_5_10
    (rkmHd
    bk_16)
    (rfl : 88 + 8 = 96)
private theorem pw_m2_r512_5_12 :
    pWOk 104 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_13 :=
  pChnN 104 pw_m2_r512_5_11
    (rkmHd
    bk_17)
    (rfl : 96 + 8 = 104)
private theorem pw_m2_r512_5_13 :
    pWOk 112 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_14 :=
  pChnN 112 pw_m2_r512_5_12
    (rkmHd
    bk_18)
    (rfl : 104 + 8 = 112)
private theorem pw_m2_r512_5_14 :
    pWOk 119 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_15 :=
  pChnN 119 pw_m2_r512_5_13
    (rkmHd
    (rkmTl
    bk_16))
    (rfl : 112 + 7 = 119)
private theorem pwalk_m2_r512_5 :
    pWOk 126 513 pb_m2_r512_5 (bDec bZ pv_m2_r512_5_0) pv_m2_r512_5_16 :=
  pChnN 126 pw_m2_r512_5_14
    (rkmHd
    (rkmTl
    bk_17))
    (rfl : 119 + 7 = 126)
private theorem pseg_m2_r512_5 : muxFastIterFullT16 126
      (Nat.add (highdNatMin (Nat.mul 448 2) 512) 1)
      phb_m2_r512_5 pvi_m2_r512_5 = pvo_m2_r512_5 :=
  bSeg_mk pdim_m2_r512_l448 pwalk_m2_r512_5 rfl rfl rfl
private theorem pw_m2_r512_6_0 :
    pWOk 8 513 pb_m2_r512_6 (bDec bZ pv_m2_r512_6_0) pv_m2_r512_6_1 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_10))
private theorem pw_m2_r512_6_1 :
    pWOk 16 513 pb_m2_r512_6 (bDec bZ pv_m2_r512_6_0) pv_m2_r512_6_2 :=
  pChnN 16 pw_m2_r512_6_0
    (rkmHd
    (rkmTl
    bk_11))
    (rfl : 8 + 8 = 16)
private theorem pw_m2_r512_6_2 :
    pWOk 24 513 pb_m2_r512_6 (bDec bZ pv_m2_r512_6_0) pv_m2_r512_6_3 :=
  pChnN 24 pw_m2_r512_6_1
    (rkmHd
    (rkmTl
    bk_12))
    (rfl : 16 + 8 = 24)
private theorem pw_m2_r512_6_3 :
    pWOk 32 513 pb_m2_r512_6 (bDec bZ pv_m2_r512_6_0) pv_m2_r512_6_4 :=
  pChnN 32 pw_m2_r512_6_2
    (rkmHd
    (rkmTl
    bk_13))
    (rfl : 24 + 8 = 32)
private theorem pw_m2_r512_6_4 :
    pWOk 40 513 pb_m2_r512_6 (bDec bZ pv_m2_r512_6_0) pv_m2_r512_6_5 :=
  pChnN 40 pw_m2_r512_6_3
    (rkmHd
    (rkmTl
    bk_14))
    (rfl : 32 + 8 = 40)
private theorem pw_m2_r512_6_5 :
    pWOk 48 513 pb_m2_r512_6 (bDec bZ pv_m2_r512_6_0) pv_m2_r512_6_6 :=
  pChnN 48 pw_m2_r512_6_4
    (rkmHd
    (rkmTl
    bk_15))
    (rfl : 40 + 8 = 48)
private theorem pw_m2_r512_6_6 :
    pWOk 55 513 pb_m2_r512_6 (bDec bZ pv_m2_r512_6_0) pv_m2_r512_6_7 :=
  pChnN 55 pw_m2_r512_6_5
    (rkmHd
    (rkmTl
    bk_18))
    (rfl : 48 + 7 = 55)
private theorem pw_m2_r512_6_7 :
    pWOk 62 513 pb_m2_r512_6 (bDec bZ pv_m2_r512_6_0) pv_m2_r512_6_8 :=
  pChnN 62 pw_m2_r512_6_6
    (rkmHd
    (rkmTl
    bk_19))
    (rfl : 55 + 7 = 62)
private theorem pwalk_m2_r512_6 :
    pWOk 69 513 pb_m2_r512_6 (bDec bZ pv_m2_r512_6_0) pv_m2_r512_6_9 :=
  pChnN 69 pw_m2_r512_6_7
    (rkmHd
    (rkmTl
    bk_20))
    (rfl : 62 + 7 = 69)
private theorem pseg_m2_r512_6 : muxFastIterFullT16 69
      (Nat.add (highdNatMin (Nat.mul 448 2) 512) 1)
      phb_m2_r512_6 pvi_m2_r512_6 = pvo_m2_r512_6 :=
  bSeg_mk pdim_m2_r512_l448 pwalk_m2_r512_6 rfl rfl rfl
private theorem pwalks_snd_m2_r512 :
    RkmSegWalksSound 2 512 [8, 24, 64, 144, 256, 448, 448, 448]
      [6, 16, 30, 67, 119, 126, 69, 55] pwalks_m2_r512 := by
  dsimp only [RkmSegWalksSound, pwalks_m2_r512]
  exact ⟨rkmSegPack_m2_r512_s0,
    ⟨rkmSegPack_m2_r512_s1,
    ⟨rkmSegPack_m2_r512_s2,
    ⟨rkmSegPack_m2_r512_s3,
    ⟨pseg_m2_r512_4,
    ⟨pseg_m2_r512_5,
    ⟨pseg_m2_r512_6,
    ⟨rkmSegPack_m2_r512_s7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 2, r = 512)`. -/
theorem rkmTrajPack_m2_r512 :
    rkmEvalT16Lo12 2 4096 512 [8, 24, 64, 144, 256, 448, 448, 448]
      [10277869, 10634078, 7977165, 8864612, 9902763, 7112570, 3861992, 3096805]
      [6, 16, 30, 67, 119, 126, 69, 55]
      rkmMasksPack_m2_r512 = rkmRowPack_m2_r512 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m2_r512 ptail_0

/-- Module export witness for `FindAllJohnsonRampKickMuxLowHiT1`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxLowHiT1 : True := trivial

end

end QuantumComputation.Specs.DickeSol
