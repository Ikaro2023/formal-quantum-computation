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
public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxTraj03
/-
# Multi-Segment `T_16` Trajectory Part `05` (`FindAllJohnsonRampKickMuxTraj05`)

Certified kernel trajectory evaluations (`30` rows, `37999` substep-coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Prefix-kick masks for `(m = 2, r = 17)`. -/
def rkmMasks_m2_r17 : List (List Bool) := [[], [], [], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 17)`. -/
def rkmRow_m2_r17 : List ℕ := [
  45718, 187805, 64861, 173354, 20997879, 373608, 432344241, 37784251, 3947447888, 2669437769,
  14320648878, 38903062064, 8031893769, 276254369860, 439666564158, 192323029302, 23391574262]
/-- Mask chunk for `(m = 2, r = 20)`. -/
def rkmMkP_m2_r20_s4_p0 : List Bool := [
  true, true, true, false, true, true, false, false, false, true, true, false, false, true, true,
  true]
/-- Mask chunk for `(m = 2, r = 20)`. -/
def rkmMkP_m2_r20_s5_p0 : List Bool := [
  true, true, true, false, true, false, true, false, true, false, false, true, false, true]
/-- Prefix-kick masks for `(m = 2, r = 20)`. -/
def rkmMasks_m2_r20 : List (List Bool) := [
  [], [], [], [], rkmMkP_m2_r20_s4_p0, rkmMkP_m2_r20_s5_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 2, r = 20)`. -/
def rkmRow_m2_r20 : List ℕ := [
  7023, 163223, 39143, 225243, 5344070, 11592440, 74705776, 67815659, 11271306, 313112185,
  1788265, 9501559053, 769402960, 2691263269, 30150379119, 821001210, 26647573262, 336103346903,
  461308079291, 131521329552]
/-- Prefix-kick masks for `(m = 4, r = 6)`. -/
def rkmMasks_m4_r6 : List (List Bool) := [
  [], [false, false, true, true], [false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 4, r = 6)`. -/
def rkmRow_m4_r6 : List ℕ := [
  319191468, 72431136, 2491053764, 553487017, 166180969864, 830332872805]
/-- Prefix-kick masks for `(m = 8, r = 7)`. -/
def rkmMasks_m8_r7 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 7)`. -/
def rkmRow_m8_r7 : List ℕ := [
  77356441, 18475593, 3730490115, 4355824729, 52962274222, 91730386665, 847124950071]
/-- Mask chunk for `(m = 8, r = 17)`. -/
def rkmMkP_m8_r17_s2_p0 : List Bool := [
  true, true, false, false, true, true, false, false, true, true, true, true, true]
/-- Mask chunk for `(m = 8, r = 17)`. -/
def rkmMkP_m8_r17_s3_p0 : List Bool := [
  false, true, false, true, false, true, false, false, true, false, true, true, false, true, true]
/-- Mask chunk for `(m = 8, r = 17)`. -/
def rkmMkP_m8_r17_s4_p0 : List Bool := [
  false, true, false, true, false, true, false, false, true, false, true, true, false, false,
  false, true]
/-- Prefix-kick masks for `(m = 8, r = 17)`. -/
def rkmMasks_m8_r17 : List (List Bool) := [
  [], [], rkmMkP_m8_r17_s2_p0, rkmMkP_m8_r17_s3_p0, rkmMkP_m8_r17_s4_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 17)`. -/
def rkmRow_m8_r17 : List ℕ := [
  12560, 9140, 468928, 1070707, 2219096, 28806946, 115756, 105762394, 2766453744, 2925928,
  368115655, 39519525, 5521146111, 2611240870, 55583368, 99075838782, 889420709944]
/-- Mask chunk for `(m = 8, r = 21)`. -/
def rkmMkP_m8_r21_s1_p0 : List Bool := [
  false, true, true, true, true, true, false, false, false, true, true, true, true, true, false,
  false, true, true]
/-- Mask chunk for `(m = 8, r = 21)`. -/
def rkmMkP_m8_r21_s2_p0 : List Bool := [
  false, true, false, true, false, false, false, true, false, true, false, true, false, true,
  true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 8, r = 21)`. -/
def rkmMasks_m8_r21 : List (List Bool) := [[], rkmMkP_m8_r21_s1_p0, rkmMkP_m8_r21_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 8, r = 21)`. -/
def rkmRow_m8_r21 : List ℕ := [
  6, 13850, 4965, 620058, 70163, 959755, 485917, 11661231, 139455706, 451742672, 690955099,
  786010640, 1202224778, 104231619, 365932602, 2110407394, 11995470497, 6040354540, 1169153411,
  90429984985, 884500259795]
/-- Prefix-kick masks for `(m = 16, r = 7)`. -/
def rkmMasks_m16_r7 : List (List Bool) := [
  [], [true, true, true, true], [false, true, true, false, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 16, r = 7)`. -/
def rkmRow_m16_r7 : List ℕ := [
  521794, 1241979, 263665532, 1319689715, 124247622, 36080968822, 962209131414]
/-- Prefix-kick masks for `(m = 32, r = 3)`. -/
def rkmMasks_m32_r3 : List (List Bool) := [[], [true], [false, true, true, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 3)`. -/
def rkmRow_m32_r3 : List ℕ := [39699766, 56965914325, 942994352156]
/-- Mask chunk for `(m = 32, r = 15)`. -/
def rkmMkP_m32_r15_s1_p0 : List Bool := [
  false, true, false, true, false, false, false, true, false, true, true, false, true, true]
/-- Prefix-kick masks for `(m = 32, r = 15)`. -/
def rkmMasks_m32_r15 : List (List Bool) := [
  [false, true, true, false, true, false, false, true, true, false, true, true],
  rkmMkP_m32_r15_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 15)`. -/
def rkmRow_m32_r15 : List ℕ := [
  0, 94, 6, 19134, 14922, 10924, 823706, 44595210, 5799734, 369359, 797690696, 1600522019,
  81471832, 18366086791, 979102595439]
/-- Mask chunk for `(m = 32, r = 22)`. -/
def rkmMkP_m32_r22_s0_p0 : List Bool := [
  false, false, false, true, true, false, true, false, false, true, true, false, false, true,
  true, true]
/-- Mask chunk for `(m = 32, r = 22)`. -/
def rkmMkP_m32_r22_s1_p0 : List Bool := [
  true, true, false, true, false, true, false, true, false, true, true, false, true, false, false,
  true, false, false, true, true]
/-- Mask chunk for `(m = 32, r = 22)`. -/
def rkmMkP_m32_r22_s2_p0 : List Bool := [
  false, true, true, false, true, false, true, false, true, false, false, false, true, false,
  false, false, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 32, r = 22)`. -/
def rkmMasks_m32_r22 : List (List Bool) := [
  rkmMkP_m32_r22_s0_p0, rkmMkP_m32_r22_s1_p0, rkmMkP_m32_r22_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 22)`. -/
def rkmRow_m32_r22 : List ℕ := [
  0, 0, 1, 143, 1878, 10599, 3078, 8207, 258882, 415853, 1953016, 58014, 47407037, 275068443,
  8195840, 328169823, 75062240, 3727690, 4875761129, 44546376, 20585211389, 973754140086]
/-- Mask chunk for `(m = 32, r = 25)`. -/
def rkmMkP_m32_r25_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, true, false, false, true,
  true, false, false, false, false, true]
/-- Mask chunk for `(m = 32, r = 25)`. -/
def rkmMkP_m32_r25_s1_p0 : List Bool := [
  false, false, false, false, true, false, true, false, true, false, true, false, true, false,
  true, false, true, false, false, false, true, true]
/-- Mask chunk for `(m = 32, r = 25)`. -/
def rkmMkP_m32_r25_s2_p0 : List Bool := [
  false, false, false, false, false, true, false, true, false, true, false, true, false, true,
  false, true, false, true, true, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 32, r = 25)`. -/
def rkmMasks_m32_r25 : List (List Bool) := [
  rkmMkP_m32_r25_s0_p0, rkmMkP_m32_r25_s1_p0, rkmMkP_m32_r25_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 25)`. -/
def rkmRow_m32_r25 : List ℕ := [
  0, 0, 0, 0, 0, 0, 3, 17, 16, 126, 3668, 231756, 1252061, 17956921, 97356169, 770669, 358400390,
  79493459, 402191882, 1313396, 11445847361, 4065318421, 286363877, 25340320162, 957903179304]
/-- Mask chunk for `(m = 32, r = 35)`. -/
def rkmMkP_m32_r35_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, true, true, false, false, true, true, false, false, true, true, true, false, false, true,
  true, true]
/-- Mask chunk for `(m = 32, r = 35)`. -/
def rkmMkP_m32_r35_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, true, false, true, false, true, false, true,
  false, true, false, true, false, true, false, true, false, true, false, true, true, false, true,
  false, false, true, true]
/-- Mask chunk for `(m = 32, r = 35)`. -/
def rkmMkP_m32_r35_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, true, true, true,
  true, true, true, true, true, true, true, true, true, true, true, false, false, true, false,
  false, false, false, false, true]
/-- Prefix-kick masks for `(m = 32, r = 35)`. -/
def rkmMasks_m32_r35 : List (List Bool) := [
  [], rkmMkP_m32_r35_s1_p0, rkmMkP_m32_r35_s2_p0, rkmMkP_m32_r35_s3_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 35)`. -/
def rkmRow_m32_r35 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 52, 35, 1907, 314, 23539, 44098, 72557, 1435992,
  5368011, 118396, 42940893, 296258766, 11036386, 1463758805, 1008079834, 4061981, 1081832036,
  3308713182, 23447967, 20300230440, 972452574155]
/-- Mask chunk for `(m = 32, r = 64)`. -/
def rkmMkP_m32_r64_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 32, r = 64)`. -/
def rkmMkP_m32_r64_s1_p0 : List Bool := [
  false, true, true, true, true, false, false, true, true, false, true, true, false, false, true,
  false, true, false, true, false, false, true, true, false, false, true, true, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, false, false, false, false, false, true]
/-- Mask chunk for `(m = 32, r = 64)`. -/
def rkmMkP_m32_r64_s2_p0 : List Bool := [
  false, true, false, false, false, false, true, true, true, true, true, false, true, true, true,
  true, true, true, false, true, true, true, true, true, false, false, false, false, true, true,
  false, true, false, true, true, false, true, true, false, false, true, false, false, false,
  false, false, true, true, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true]
/-- Mask chunk for `(m = 32, r = 64)`. -/
def rkmMkP_m32_r64_s2_p1 : List Bool := [true]
/-- Mask chunk for `(m = 32, r = 64)`. -/
def rkmMkP_m32_r64_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, false, false, false, true, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  true, false, false, true, true, false, true, true, false, false, true, true, false, true, true,
  true, false, false, true, true]
/-- Mask chunk for `(m = 32, r = 64)`. -/
def rkmMkP_m32_r64_s4_p0 : List Bool := [
  true, true, false, true, true, true, false, false, false, false, true, false, true, false,
  false, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, true, false, true, false, true, false, true,
  false, true, false, false, true, false, false, true]
/-- Mask chunk for `(m = 32, r = 64)`. -/
def rkmMkP_m32_r64_s5_p0 : List Bool := [
  false, true, false, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, false, false, true]
/-- Mask chunk for `(m = 32, r = 64)`. -/
def rkmMkP_m32_r64_s6_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, false, true]
/-- Prefix-kick masks for `(m = 32, r = 64)`. -/
def rkmMasks_m32_r64 : List (List Bool) := [
  rkmMkP_m32_r64_s0_p0, rkmMkP_m32_r64_s1_p0, rkmMkP_m32_r64_s2_p0 ++ rkmMkP_m32_r64_s2_p1,
  rkmMkP_m32_r64_s3_p0, rkmMkP_m32_r64_s4_p0, rkmMkP_m32_r64_s5_p0, rkmMkP_m32_r64_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 64)`. -/
def rkmRow_m32_r64 : List ℕ := [
  475, 2822, 9366, 3910, 12795, 6270, 4428, 557, 434, 31, 25151, 27363, 98203, 240618, 884498,
  1622492, 2168204, 6307674, 4815251, 5673229, 5187047, 9499255, 10597405, 10706189, 250663,
  984767, 4531109, 5840270, 32463, 6809090, 6920193, 2381908, 13060361, 13556118, 7956870,
  57118065, 40166751, 154332, 7019397, 18605663, 53388578, 67740721, 47988561, 110805402,
  83452535, 11331419, 77159771, 19967697, 272857288, 615597, 705565637, 39451095, 1140610146,
  330016055, 2082959813, 1029559526, 1117212418, 894586851, 780128438, 7655021064, 10224302549,
  2335787019, 13589758485, 957086448035]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, true, false, false, false, false, false, true,
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s2_p0 : List Bool := [
  false, true, false, false, false, false, false, true, true, false, true, true, true, true,
  false, false, false, true, false, false, false, true, false, false, false, false, false, true,
  true, true, true, true, true, true, true, true, true, true, true, false, false, false, true,
  false, true, false, true, false, false, true, true, true, true, true, false, true, false, false,
  true, false, true, false, true, false]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s2_p1 : List Bool := [
  false, true, false, false, true, true, true, true, false, false, false, true, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s3_p0 : List Bool := [
  true, false, true, true, false, false, true, false, false, true, true, false, true, false,
  false, true, true, true, true, false, false, true, false, true, true, false, false, true, false,
  true, false, true, false, true, true, false, true, false, false, false, false, false, false,
  false, false, false, false, false, true, true, false, false, false, false, false, false, false,
  false, true, true, false, false, true, false]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s3_p1 : List Bool := [
  false, true, false, false, false, false, true, true, false, true, false, true, true, true, true,
  false, true, false, false, true, true, false, false, false, true, true, false, false, false,
  true, true, true, false, false, false, true, true, true, false, false, false, true, true, true,
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s3_p2 : List Bool := [true]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s4_p0 : List Bool := [
  true, false, true, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, false, true, false, false, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, false, false, false,
  false, false, false, true, false, false, false, false]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s4_p1 : List Bool := [
  false, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, true, false, false, false, false,
  false, false, false, false, false, false, false, false, true, true, false, true, true, false,
  true, false, true, true, false, true, true, false, false, true, true, false, false, true, true,
  false, false, true, true]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s5_p0 : List Bool := [
  false, true, false, true, false, true, false, false, false, false, false, false, false, false,
  false, true, false, false, false, false, true, false, false, false, false, false, false, true,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, true,
  false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s5_p1 : List Bool := [
  false, false, false, true, false, false, false, true, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, true, true,
  true, false, true]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s6_p0 : List Bool := [
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false]
/-- Mask chunk for `(m = 32, r = 128)`. -/
def rkmMkP_m32_r128_s6_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, false,
  false, false, false, true, false, false, true, false, false, true]
/-- Prefix-kick masks for `(m = 32, r = 128)`. -/
def rkmMasks_m32_r128 : List (List Bool) := [
  rkmMkP_m32_r128_s0_p0, rkmMkP_m32_r128_s1_p0, rkmMkP_m32_r128_s2_p0 ++ rkmMkP_m32_r128_s2_p1,
  rkmMkP_m32_r128_s3_p0 ++ rkmMkP_m32_r128_s3_p1 ++ rkmMkP_m32_r128_s3_p2,
  rkmMkP_m32_r128_s4_p0 ++ rkmMkP_m32_r128_s4_p1, rkmMkP_m32_r128_s5_p0 ++ rkmMkP_m32_r128_s5_p1,
  rkmMkP_m32_r128_s6_p0 ++ rkmMkP_m32_r128_s6_p1, []]
/-- Row chunk `0` `(m = 32, r = 128)`. -/
def rkmRowP_m32_r128_p0 : List ℕ := [
  35, 1496, 22730, 21765, 37472, 1481413, 516400, 6846225, 1017450, 1604701, 1380961, 2887351,
  9168393, 22650, 4166052, 307482, 12369109, 5406451, 848790, 12752794, 2663316, 22762, 477518,
  68366, 1507395, 1637413, 1621, 1673869, 1441876, 254733, 1864566, 130620, 383637, 350115,
  1827099, 1081470, 23886, 59039, 8229, 143811, 1057346, 2280086, 805059, 121818, 2103420,
  2024859, 146073, 4073, 76379, 1972146, 7972561, 3224420, 919045, 3195265, 169985, 15570064,
  11702012, 3888696, 7068434, 3472941, 7386, 1084586, 8883784, 4919382]
/-- Row chunk `1` `(m = 32, r = 128)`. -/
def rkmRowP_m32_r128_p1 : List ℕ := [
  761076, 1970, 614319, 65665, 7590203, 22342587, 14951449, 22314386, 1104, 35938142, 53500809,
  72276624, 30882427, 14502039, 82819606, 177239096, 126133435, 9531413, 155897856, 364077261,
  99182769, 78170, 116278048, 245353077, 22808507, 12095470, 224190568, 119123047, 5134628,
  170803125, 80369492, 159970, 32487746, 2611808, 43001568, 186624174, 227101221, 245309768,
  29185343, 134770839, 184532655, 1303, 83948660, 760905786, 241342140, 482302627, 10510850,
  1828416074, 697137977, 441183, 572241930, 145766107, 9545707958, 1519731142, 74141889,
  164660897, 1916956039, 2282774406, 306803990, 7091583519, 21564954014, 7277030556, 27635179430,
  912265649132]
/-- Certified `10 ^ 12`-scaled hit row `(m = 32, r = 128)`. -/
def rkmRow_m32_r128 : List ℕ := rkmRowP_m32_r128_p0 ++ rkmRowP_m32_r128_p1
/-- Prefix-kick masks for `(m = 64, r = 3)`. -/
def rkmMasks_m64_r3 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 3)`. -/
def rkmRow_m64_r3 : List ℕ := [358695305, 54875822904, 944765248963]
/-- Prefix-kick masks for `(m = 64, r = 11)`. -/
def rkmMasks_m64_r11 : List (List Bool) := [
  [false, false, true, true, false, false, true, true, true],
  [false, false, true, false, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 11)`. -/
def rkmRow_m64_r11 : List ℕ := [
  0, 0, 38, 582, 55410, 585634, 5091835, 18419684, 58838246, 16608279144, 983308729316]
/-- Prefix-kick masks for `(m = 64, r = 12)`. -/
def rkmMasks_m64_r12 : List (List Bool) := [
  [false, false, false, true, true, false, false, true, true, true],
  [false, false, false, true, false, true, false, true, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 12)`. -/
def rkmRow_m64_r12 : List ℕ := [
  0, 0, 0, 118, 1292, 109566, 997054, 8098842, 23912723, 68544266, 15495918720, 984402417295]
/-- Mask chunk for `(m = 64, r = 22)`. -/
def rkmMkP_m64_r22_s0_p0 : List Bool := [
  false, false, true, true, true, true, false, false, true, false, false, true, true, false,
  false, true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 64, r = 22)`. -/
def rkmMasks_m64_r22 : List (List Bool) := [rkmMkP_m64_r22_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 22)`. -/
def rkmRow_m64_r22 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99, 1256, 23743, 145023, 1838021, 6768938, 74918022, 125415705,
  1628014065, 26288811, 10349955076, 987786630958]
/-- Mask chunk for `(m = 64, r = 44)`. -/
def rkmMkP_m64_r44_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, false, false, false, true, true, false, true, false,
  false, false, false, true, true, false, false, true, false, false, true, true, false, false,
  true, true]
/-- Mask chunk for `(m = 64, r = 44)`. -/
def rkmMkP_m64_r44_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, true, false, true, false, false, true, false, true, false, false,
  true, false, true, false, true, false, true, false, false, false, false, true, false, true]
/-- Prefix-kick masks for `(m = 64, r = 44)`. -/
def rkmMasks_m64_r44 : List (List Bool) := [rkmMkP_m64_r44_s0_p0, rkmMkP_m64_r44_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 64, r = 44)`. -/
def rkmRow_m64_r44 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 10, 1, 1, 6, 510, 1812, 448, 61769,
  216942, 68966, 5058, 35446, 7689553, 2622006, 46323853, 5295523, 3183018, 421107570, 75126458,
  5141798163, 53068900, 28656090716, 1724550089, 55080198725, 908782553151]
/-- Prefix-kick masks for `(m = 128, r = 9)`. -/
def rkmMasks_m128_r9 : List (List Bool) := [
  [false, false, false, false, true, true, true],
  [false, false, false, true, false, true, true, false, true, true],
  [false, false, false, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 9)`. -/
def rkmRow_m128_r9 : List ℕ := [0, 0, 154, 3766, 478765, 1093, 783498, 18269969823, 981728762781]
/-- Mask chunk for `(m = 128, r = 13)`. -/
def rkmMkP_m128_r13_s1_p0 : List Bool := [
  false, false, false, false, false, true, false, true, false, true, true, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 13)`. -/
def rkmMasks_m128_r13 : List (List Bool) := [
  [false, false, false, false, true, true, false, false, true, true, true], rkmMkP_m128_r13_s1_p0,
  [false, false, false, false, false, false, false, false, false, false, false, true], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 13)`. -/
def rkmRow_m128_r13 : List ℕ := [
  0, 0, 0, 0, 0, 0, 2438, 13381, 2394055, 321327, 5609047, 13019238560, 986972420996]
/-- Mask chunk for `(m = 128, r = 30)`. -/
def rkmMkP_m128_r30_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true, true, true, false, true, true]
/-- Mask chunk for `(m = 128, r = 30)`. -/
def rkmMkP_m128_r30_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true, false, true, false, true, false, true, false, false,
  true, true]
/-- Mask chunk for `(m = 128, r = 30)`. -/
def rkmMkP_m128_r30_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, true]
/-- Prefix-kick masks for `(m = 128, r = 30)`. -/
def rkmMasks_m128_r30 : List (List Bool) := [
  rkmMkP_m128_r30_s0_p0, rkmMkP_m128_r30_s1_p0, rkmMkP_m128_r30_s2_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 128, r = 30)`. -/
def rkmRow_m128_r30 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 106, 329, 384, 87815, 22872721,
  25326902, 10133547, 504805345, 4111026, 6596560028, 992836101107]
/-- Mask chunk for `(m = 256, r = 27)`. -/
def rkmMkP_m256_r27_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 256, r = 27)`. -/
def rkmMasks_m256_r27 : List (List Bool) := [rkmMkP_m256_r27_s0_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 27)`. -/
def rkmRow_m256_r27 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10, 1615, 189434, 4407966, 175673960,
  855857549, 6326803704, 992637065030]
/-- Prefix-kick masks for `(m = 256, r = 30)`. -/
def rkmMasks_m256_r30 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 30)`. -/
def rkmRow_m256_r30 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15, 83, 7792, 48010, 3395833,
  20058194, 1527062019, 5813168433, 992636258768]
/-- Prefix-kick masks for `(m = 512, r = 9)`. -/
def rkmMasks_m512_r9 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 9)`. -/
def rkmRow_m512_r9 : List ℕ := [0, 0, 0, 0, 2336, 141412, 33555194, 17342025585, 982624275312]
/-- Mask chunk for `(m = 512, r = 25)`. -/
def rkmMkP_m512_r25_s0_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, true, true, true]
/-- Mask chunk for `(m = 512, r = 25)`. -/
def rkmMkP_m512_r25_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, true, false, false, true, true]
/-- Prefix-kick masks for `(m = 512, r = 25)`. -/
def rkmMasks_m512_r25 : List (List Bool) := [rkmMkP_m512_r25_s0_p0, rkmMkP_m512_r25_s1_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 25)`. -/
def rkmRow_m512_r25 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 172, 6461, 50408, 21159, 4168136, 54681581,
  6489324350, 993451746839]
/-- Mask chunk for `(m = 512, r = 32)`. -/
def rkmMkP_m512_r32_s1_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, false, true, true, true, false, false, true]
/-- Mask chunk for `(m = 512, r = 32)`. -/
def rkmMkP_m512_r32_s2_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, true, false, false, true, false, true, true, true,
  true]
/-- Mask chunk for `(m = 512, r = 32)`. -/
def rkmMkP_m512_r32_s3_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true, false, false, true, true, true,
  false, true, true]
/-- Mask chunk for `(m = 512, r = 32)`. -/
def rkmMkP_m512_r32_s4_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, false, true,
  false, false, true]
/-- Mask chunk for `(m = 512, r = 32)`. -/
def rkmMkP_m512_r32_s5_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, true, false, true, false,
  true, false, false, true]
/-- Mask chunk for `(m = 512, r = 32)`. -/
def rkmMkP_m512_r32_s6_p0 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  true, false, false, true]
/-- Prefix-kick masks for `(m = 512, r = 32)`. -/
def rkmMasks_m512_r32 : List (List Bool) := [
  [], rkmMkP_m512_r32_s1_p0, rkmMkP_m512_r32_s2_p0, rkmMkP_m512_r32_s3_p0, rkmMkP_m512_r32_s4_p0,
  rkmMkP_m512_r32_s5_p0, rkmMkP_m512_r32_s6_p0, []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 512, r = 32)`. -/
def rkmRow_m512_r32 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 398, 22, 6832, 552043,
  143705, 1758042, 5059947537, 994937590022]
/-- Prefix-kick masks for `(m = 1024, r = 6)`. -/
def rkmMasks_m1024_r6 : List (List Bool) := [[], []]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 6)`. -/
def rkmRow_m1024_r6 : List ℕ := [0, 811, 757876, 226422493, 25878808722, 973894009989]
/-- Prefix-kick masks for `(m = 1024, r = 19)`. -/
def rkmMasks_m1024_r19 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 19)`. -/
def rkmRow_m1024_r19 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 360, 425801, 600360, 8170610300, 991828362480]
/-- Prefix-kick masks for `(m = 1024, r = 21)`. -/
def rkmMasks_m1024_r21 : List (List Bool) := [[]]
/-- Certified `10 ^ 12`-scaled hit row `(m = 1024, r = 21)`. -/
def rkmRow_m1024_r21 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26, 118, 553902, 3985427, 7404937826, 992590521818]
/-- Unpacks `j` LSB-first bits of `< 2 ^ 50` word `w` (`FindAllJohnsonRampKickMuxTraj05`). -/
def rkmWbTraj05 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWbTraj05 j (Nat.div w 2)
/-- Concatenates `50`-bit `< 2 ^ 50` chunks (final length `rem`) into a `List Bool` mask. -/
def rkmMaskWordsTraj05 : ℕ → List ℕ → List Bool
  | _, [] => []
  | rem, [w] => rkmWbTraj05 rem w
  | rem, w :: v :: ws => rkmWbTraj05 50 w ++ rkmMaskWordsTraj05 rem (v :: ws)
/-- Krotov masks `(m = 2, r = 128)`. -/
def rkmMasksPack_m2_r128 : List (List Bool) := [[],[],rkmWbTraj05 1 1,
  rkmMaskWordsTraj05 6 [126361600,32],rkmMaskWordsTraj05 9 [564866372349249,668503077829511,289],
  rkmMaskWordsTraj05 28 [340670757770055,594729275451221,160169987],
  rkmMaskWordsTraj05 21 [374750221530971,93820699362775,1623112],[]]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 128)`. -/
def rkmRowPack_m2_r128 : List ℕ := [7374,62002,20805,177671,107823,43200,191640,290662,53105,
  91574,77941,296252,142848,10755,451350,692114,8687,154449,65668,826321,68895,88062,760,1024126,
  1420059,1043580,44881,349925,750228,285825,216821,863,910829,17610,964779,2119980,418691,133254,
  5930257,4461954,5909643,9911519,8094529,21598866,1880499,1854139,1060336,2472664,8214353,
  3755285,1051620,11252,10294840,3066,2064063,14378049,13833374,5466472,58636668,14172553,
  56605510,43605945,39175430,28467343,11617090,5822333,33066762,85245783,24814114,6567104,7235155,
  97194614,106441354,45946576,19249,41234289,99661760,56053159,2730814,127625364,165120639,
  34697110,2032028,144021603,186584185,4126573,168510722,814899658,2491962,160013761,414645205,
  522102294,451445364,601236849,91479499,104271476,190675494,4510643,272028183,355565058,
  841493938,19485118,10276899,12952863,76188364,1016868340,3965830,7986974,630623985,12161719,
  883319760,498754470,3610194940,397952656,1421599072,5574515377,149562720,1332501511,1700048757,
  595372,11201780943,23790230161,7642430,713661288,74970459799,373415689107,383272625605,
  108608556677]
/-- Krotov masks `(m = 8, r = 3)`. -/
def rkmMasksPack_m8_r3 : List (List Bool) := [[],rkmWbTraj05 1 1,rkmWbTraj05 2 3,rkmWbTraj05 4 13,
  []]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 3)`. -/
def rkmRowPack_m8_r3 : List ℕ := [20190865,72674406039,927305293972]
/-- Krotov masks `(m = 64, r = 58)`. -/
def rkmMasksPack_m64_r58 : List (List Bool) := [[],rkmWbTraj05 6 57,rkmWbTraj05 41 2077794820323,
  rkmWbTraj05 48 249783715672064,rkmMaskWordsTraj05 3 [231212405962305,7],
  rkmMaskWordsTraj05 6 [375665041173293,50],rkmMaskWordsTraj05 7 [6915606533313,65],[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 58)`. -/
def rkmRowPack_m64_r58 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  6,0,37,0,34,307,0,369,3573,3149,358,1527,31253,24164,4352662,1779836,1186887,21885697,3344961,
  1872368,101901468,6255768,168249070,904318035,65048678,9535335323,989184402226]
/-- Krotov masks `(m = 64, r = 5)`. -/
def rkmMasksPack_m64_r5 : List (List Bool) := [[],[],[],[],[],rkmWbTraj05 2 3,rkmWbTraj05 3 4,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 5)`. -/
def rkmRowPack_m64_r5 : List ℕ := [430,22856,10839065,33427339945,966561794342]
/-- Krotov masks `(m = 64, r = 46)`. -/
def rkmMasksPack_m64_r46 : List (List Bool) := [[],rkmWbTraj05 14 15929,rkmWbTraj05 35 30482340277,
  rkmWbTraj05 40 879204057098,rkmWbTraj05 43 6986413025545,rkmWbTraj05 44 8935145220765,
  rkmWbTraj05 45 19830558861989,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 46)`. -/
def rkmRowPack_m64_r46 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,74,9,889,796,2249,915,
  1319,4031,263476,422061,241095,163057,88522,15614,915405,64297504,249532,1561201,206461012,
  2512674,33164444,687757967,14987782,70659463,2179912609,49042549,11282600161,985404672338]
/-- Krotov masks `(m = 64, r = 7)`. -/
def rkmMasksPack_m64_r7 : List (List Bool) := [rkmWbTraj05 5 28,rkmWbTraj05 6 37,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 7)`. -/
def rkmRowPack_m64_r7 : List ℕ := [1032,31183,1654242,82263,13552892,24465228426,975519449883]
/-- Krotov masks `(m = 64, r = 41)`. -/
def rkmMasksPack_m64_r41 : List (List Bool) := [[],rkmWbTraj05 1 1,rkmWbTraj05 29 477338720,
  rkmWbTraj05 35 30917431890,rkmWbTraj05 38 216180042390,rkmWbTraj05 39 279783428233,
  rkmWbTraj05 40 551018900117,[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 41)`. -/
def rkmRowPack_m64_r41 : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,41,129,73,820,254,2742,5558,
  4706,438863,522319,582813,132205,6468277,3634621,2981168,112507,102616247,3755252,29847421,
  249614763,48816156,95496633,1243206946,84130097,9990764725,988136863668]
/-- Krotov masks `(m = 32, r = 7)`. -/
def rkmMasksPack_m32_r7 : List (List Bool) := [[],[],[],rkmWbTraj05 2 3,rkmWbTraj05 4 12,
  rkmWbTraj05 5 17,rkmWbTraj05 6 34,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 7)`. -/
def rkmRowPack_m32_r7 : List ℕ := [12133,558855,530102,241907,92382780,27429534812,972476738016]
/-- Krotov masks `(m = 16, r = 40)`. -/
def rkmMasksPack_m16_r40 : List (List Bool) := [[],rkmWbTraj05 27 100663309,rkmWbTraj05 24 16558360,
  rkmWbTraj05 38 213015177860,rkmWbTraj05 39 320688545322,[]]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 40)`. -/
def rkmRowPack_m16_r40 : List ℕ := [25189,13607,1814055,558240,1085,2106,312180,975872,20435,
  914047,1993453,9475195,12029083,85467,8889310,11156943,7743438,3587104,7693435,17464517,
  36916073,3171499,57343129,287354023,232853744,16649188,246475146,416492506,232438760,1406369025,
  514198564,3872335237,1102167817,7446558398,1947178231,73347369,21798034438,7324881,39423146875,
  920794852008]
/-- Krotov masks `(m = 32, r = 9)`. -/
def rkmMasksPack_m32_r9 : List (List Bool) := [rkmWbTraj05 6 62,rkmWbTraj05 8 218,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 9)`. -/
def rkmRowPack_m32_r9 : List ℕ := [152,79172,717868,425675,71506288,478644456,72278079,
  23015950240,976360397952]
/-- Krotov masks `(m = 32, r = 32)`. -/
def rkmMasksPack_m32_r32 : List (List Bool) := [rkmWbTraj05 21 1179648,rkmWbTraj05 30 805306368,
  rkmWbTraj05 28 201326593,rkmWbTraj05 30 536871160,rkmWbTraj05 32 2148392972,
  rkmWbTraj05 28 261826896,rkmWbTraj05 31 1840606027,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 32)`. -/
def rkmRowPack_m32_r32 : List ℕ := [1,401,1880,3573,2255,744,410,87958,43883,14259,394246,256507,
  17862944,15131632,24599425,4056413,1245306,8367596,165972554,9327695,18324463,119752265,
  244888414,3767493,712176875,1416130767,1515920364,2395732872,5920863741,7884663,18848298525,
  968548887939]
/-- Krotov masks `(m = 64, r = 8)`. -/
def rkmMasksPack_m64_r8 : List (List Bool) := [[],rkmWbTraj05 6 58,rkmWbTraj05 6 42,
  rkmWbTraj05 7 65,rkmWbTraj05 6 59,rkmWbTraj05 7 114,[],[]]
/-- `10 ^ 12`-scaled hit row `(m = 64, r = 8)`. -/
def rkmRowPack_m64_r8 : List ℕ := [1,1466,106,3996823,73229,5131829,21719687328,978271109136]
/-- Krotov masks `(m = 8, r = 32)`. -/
def rkmMasksPack_m8_r32 : List (List Bool) := [[],[],rkmWbTraj05 31 1208024831,
  rkmWbTraj05 25 30199513,rkmWbTraj05 30 843797673,rkmWbTraj05 31 1073742192,
  rkmWbTraj05 31 1106256576,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 32)`. -/
def rkmRowPack_m8_r32 : List ℕ := [202991,831769,2318,3829081,2415,5051,92046,8543614,488067,2819,
  7238040,46809014,86571,920046,69063320,92447914,580970097,962567514,583168774,30982266,
  1144488894,547949220,1148026752,1122103259,2168661186,1581202057,216723,7542831068,16051686507,
  1152729,81446050046,884856995880]
/-- Krotov masks `(m = 2, r = 15)`. -/
def rkmMasksPack_m2_r15 : List (List Bool) := [[],[],[],[]]
/-- `10 ^ 12`-scaled hit row `(m = 2, r = 15)`. -/
def rkmRowPack_m2_r15 : List ℕ := [192603,115131,3660148,920105,148664307,136558592,1661291129,
  4153037461,4293430750,39881715837,238961288,183281042344,456976551725,267334039377,41889741259]
/-- Krotov masks `(m = 32, r = 28)`. -/
def rkmMasksPack_m32_r28 : List (List Bool) := [rkmWbTraj05 11 1950,rkmWbTraj05 26 51983149,
  rkmWbTraj05 27 78293398,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 28)`. -/
def rkmRowPack_m32_r28 : List ℕ := [227,1506,80,3267,1127,141,1969,3895,234,11115,2659,8252,2913,
  227309,511278,3625268,6387310,31912389,51539909,335018887,378308799,2220418997,2864420677,
  10482221,8935955973,1163510,19328019453,965831970072]
/-- Krotov masks `(m = 4, r = 12)`. -/
def rkmMasksPack_m4_r12 : List (List Bool) := [[],[],rkmWbTraj05 6 56,rkmWbTraj05 9 402,
  rkmWbTraj05 10 520,rkmWbTraj05 11 1026,rkmWbTraj05 11 1181,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 12)`. -/
def rkmRowPack_m4_r12 : List ℕ := [214353,62788408,36314941,34289427,927231516,580147802,17421861,
  2953354226,3646058868,4472085,169198126542,822538724708]
/-- Krotov masks `(m = 16, r = 27)`. -/
def rkmMasksPack_m16_r27 : List (List Bool) := [[],rkmWbTraj05 25 25860563,rkmWbTraj05 26 39138687,
  []]
/-- `10 ^ 12`-scaled hit row `(m = 16, r = 27)`. -/
def rkmRowPack_m16_r27 : List ℕ := [44,162,141,26,47,226,76,295,5753,43422,176637,1094825,3963,
  1491492,208135,6544398,220110431,1109218974,900176619,1595699178,4498511564,3128161251,
  163838104,16793053468,12736017,39002769309,932566154946]
/-- Krotov masks `(m = 8, r = 30)`. -/
def rkmMasksPack_m8_r30 : List (List Bool) := [rkmWbTraj05 7 127,[],rkmWbTraj05 16 47119,
  rkmWbTraj05 17 65537,rkmWbTraj05 19 409600,rkmWbTraj05 21 1574959,rkmWbTraj05 20 1046560,[]]
/-- `10 ^ 12`-scaled hit row `(m = 8, r = 30)`. -/
def rkmRowPack_m8_r30 : List ℕ := [293402,481892,4551541,19497313,123865841,846094244,10437628667,
  83228443306,190507763786,686415191292,366480273,15736506196,10433788888,1731702816,140698051,
  6755244,191514,3204,19,0,0,0,0,0,0,0,0,0,0,0]
/-- Krotov masks `(m = 32, r = 21)`. -/
def rkmMasksPack_m32_r21 : List (List Bool) := [rkmWbTraj05 20 1048575,rkmWbTraj05 10 883,
  rkmWbTraj05 15 29547,rkmWbTraj05 18 206166,rkmWbTraj05 19 266854,rkmWbTraj05 20 599692,
  rkmWbTraj05 20 600132,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 21)`. -/
def rkmRowPack_m32_r21 : List ℕ := [0,29,3,429,173,39274,4891,204188,98706,1121118,711809,
  16881489,396768,43138646,102449425,38565465,158206336,977998988,88989638,19683328946,
  978887863422]
/-- Krotov masks `(m = 4, r = 16)`. -/
def rkmMasksPack_m4_r16 : List (List Bool) := [[],[],rkmWbTraj05 6 50,rkmWbTraj05 11 1690,
  rkmWbTraj05 14 14037,rkmWbTraj05 6 35,rkmWbTraj05 15 16611,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 16)`. -/
def rkmRowPack_m4_r16 : List ℕ := [1946706,32545571,99688952,404821514,53696741,77937145,
  235031617,68697490,503088777,2010103820,3392361663,7783414813,5084754638,59770557,170661744098,
  809523024594]
/-- Krotov masks `(m = 32, r = 19)`. -/
def rkmMasksPack_m32_r19 : List (List Bool) := [[],[],rkmWbTraj05 11 1995,rkmWbTraj05 15 30995,
  rkmWbTraj05 17 111782,rkmWbTraj05 18 132933,rkmWbTraj05 18 137249,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 19)`. -/
def rkmRowPack_m32_r19 : List ℕ := [0,1,619,40,457,297,55194,917224,3970900,2230987,2758705,
  44599594,20902761,16813683,338879165,1183855348,65844602,18628150737,979691019499]
/-- Krotov masks `(m = 32, r = 15)`. -/
def rkmMasksPack_m32_r15 : List (List Bool) := [[],[],rkmWbTraj05 7 115,rkmWbTraj05 11 2002,
  rkmWbTraj05 13 7018,rkmWbTraj05 14 8951,rkmWbTraj05 14 8442,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 15)`. -/
def rkmRowPack_m32_r15 : List ℕ := [1,22,20,13878,26152,31571,22642,12410149,5953297,1593622,
  167602278,368240482,69010167,18323683562,981051412025]
/-- Krotov masks `(m = 4, r = 20)`. -/
def rkmMasksPack_m4_r20 : List (List Bool) := [[],[],rkmWbTraj05 2 3,rkmWbTraj05 7 124,
  rkmWbTraj05 19 419528,rkmWbTraj05 6 48,[]]
/-- `10 ^ 12`-scaled hit row `(m = 4, r = 20)`. -/
def rkmRowPack_m4_r20 : List ℕ := [12080675,13561204,9567913,12097791,8742429,251134,25682039,
  46759145,36983077,157108,367751914,37422985,2586520135,76469130,13610184317,424707193,
  54991859951,9012043056,168387444486,750338267964]
/-- Krotov masks `(m = 32, r = 17)`. -/
def rkmMasksPack_m32_r17 : List (List Bool) := [rkmWbTraj05 13 8191,rkmWbTraj05 17 131071,
  rkmWbTraj05 11 1817,rkmWbTraj05 14 15785,rkmWbTraj05 16 55988,[]]
/-- `10 ^ 12`-scaled hit row `(m = 32, r = 17)`. -/
def rkmRowPack_m32_r17 : List ℕ := [55,116,1382,0,4494,38050,1153959,3392290,223966,109954619,
  9520192,47910157,624204608,1467604743,126570105,18239411641,979370009404]
/-- Cumulative `2`-lane trajectory head invariant (`Traj03` -> `Traj05`). -/
def rkmTrajLaneProp_05 : Prop :=
  rkmTrajLaneProp_03 ∧ (rkmRow_m2_r17.head? = some 45718)
/-- Proof of `rkmTrajLaneProp_05` in `O(1)` kernel steps. -/
theorem rkmTrajLaneOk_05 : rkmTrajLaneProp_05 :=
  ⟨rkmTrajLaneOk_03, rfl⟩
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
private def wc_rkmTraj_m32_r128_s2_hb_p0 : List ℕ := [156114519414528,219054432587513,
  266173306309142,304911170731500,338173844007920,367463378302075,393678935303899,417410808552584,
  439072085853360,458965760965044,477322247316467,494321854574121,510109007287858,524801641767607,
  538497644159961,551279396682552,563217071583808,574371071272770,584793871189125,594531435433279,
  603624320689551,612108548713362,620016304267429,627376499540128,634215235121520,640556179902603,
  646420886750774,651829056814653,656798762370181,661346635930008,665488031689229,669237164125630,
  672607227608200,675610500119808,678258433615004,680561733072708,682530425937334,684173923348887,
  685501074326710,686520213880486,687239205866362,687665481278469,687806072560998,687667644438978,
  687256521693515,686578714246770,685639939871216,684445644794937,683001022438560,681311030488722,
  679380406486771,677213682089053,674815196135926,672189106650137,669339401870945,666269910418005,
  662984310668370,659486139420579,655778799911732,651865569246269,647749605288996,643433953069349,
  638921550739115,634215235121520]
private def wc_rkmTraj_m32_r128_s2_hb_p1 : List ℕ := [629317746885841,624231735378354,
  618959763137445,613504310118076,607867777648455,602052492139616,596060708566774,589894613739602,
  583556329377075,577047915001168,570371370662447,563528639509520,556521610213285,549352119256024,
  542021953094575,534532850206067,526886503024032,519084559772091,511128626201876,503020267241292,
  494761008558834,486352338049168,477795707244875,469092532658838,460244197061481,451252050696724,
  442117412440283,432841570903677,423425785487051,413871287383770,404179280539461,394350942568080,
  384387425627355,374289857255829,364059341173577,353696958048540,343203766230296,332580802452971,
  321829082508888,310949601894467,299943336429771,288811242853031,277554259391408,266173306309142,
  254669286434209,243043085664528,231295573454691,219427603284140,207440013107678,195333625789122,
  183109249518889,170767678216247,158309691916921,145736057146730,133047527281858,120244842896365,
  107328732097488,94299910849273,81159083285033,67906942009105,54544168388374,41071432833986,
  27489395073656,13798704414961]
private def wc_rkmTraj_m32_r128_s2_hb : List ℕ := pCat wc_rkmTraj_m32_r128_s2_hb_p0
  wc_rkmTraj_m32_r128_s2_hb_p1
private def wc_rkmTraj_m32_r128_s2_v0_p0 : List ℕ := [1999999999999991,2000000000000079,
  2000000000000017,2000000000003020,2000000000016714,2000000000130034,2000000000744174,
  1999999996017150,2000000018861427,2000000081387538,2000000320637480,2000001161843755,
  2000003890747084,1999987907550331,1999964992856786,2000094688794049,2000239939161050,
  2000570920128320,2001278222119220,2002697566508362,2005374755965701,2010124459020609,
  2018052890591552,2030503980373547,2048889809264454,2074387364447745,2107527653207461,
  2147761228336413,2193134747270263,2240228130589187,2284459527396477,2320765245312081,
  2344532329709331,2352552409965119,2343727043354968,2319312287178626,2282628086928759,
  2238324356012430,2191425439297009,2146420387576064,2106618596390744,2073878302272408,
  2048689797896200,2030502749490251,2018151684639125,2010252219240337,2005490737823651,
  2002785347084865,2001336635475952,2000605890450914,2000258989877358,2000104187817337,
  2000039353774306,2000013918697289,1999995405563823,2000001409850358,2000000400241706,
  2000000104487049,2000000024891411,2000000005356461,2000000001026825,2000000000171825,
  2000000000024300,2000000000002737]
private def wc_rkmTraj_m32_r128_s2_v0_p1 : List ℕ := [2000000000000210]
private def wc_rkmTraj_m32_r128_s2_v0 : List ℕ := pCat wc_rkmTraj_m32_r128_s2_v0_p0
  wc_rkmTraj_m32_r128_s2_v0_p1
private def wc_rkmTraj_m32_r128_s2_v1_p0 : List ℕ := [1999990422715223,2000014786169889,
  1999994004980287,1999990468838726,2000009130185656,2000007167877408,1999990492606600,
  1999992727290177,2000008575010043,2000009000184975,1999993948564742,1999988813567034,
  2000001362437080,2000011946823514,2000005188966331,1999991082570691,1999988799064514,
  2000000938742957,2000012062503929,2000009129142748,1999995743346700,1999986964019569,
  1999990977392013,2000004677311474,2000012795634087,2000012312423335,1999998045377955,
  1999990111618886,1999982909399037,1999993708672578,2000002652809920,2000013812127771,
  2000018008463212,2000010620461675,2000003959124912,1999991680769645,1999982207796985,
  1999980270636112,1999977397912273,1999979929986706,1999986490690298,1999988423223342,
  1999988831364154,1999981299019329,1999952888669987,1999916566189328,1999936045109163,
  2000197602989805,2001144292204853,2003607706883893,2008898526032973,2018800667365478,
  2035357832359990,2060404191170776,2094923427672921,2138402877606930,2188398485132635,
  2240539532763913,2289098185844417,2328037533644811,2352259359258161,2358694533410117,
  2346923656484647,2319159868723662]
private def wc_rkmTraj_m32_r128_s2_v1_p1 : List ℕ := [2279629284880187,2233571697991239,
  2186174426488089,2141718210297713,2103094726644064,2071716395977952,2047732156823150,
  2030410714600921,2018554262699410,2010844186200961,2006072511821808,2003258241534030,
  2001674995459999,2000824874661544,2000389050692928,2000175693841016,2000075950669896,
  2000031422569002,2000012440103084,2000004712458217,2000001708102751,2000000592454720,
  2000000196665151,2000000062489097,2000000019009352,2000000005537275,2000000001544746,
  2000000000412754,2000000000105633,2000000000025888,2000000000006070,2000000000001359,
  2000000000000288,2000000000000057,2000000000000008,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m32_r128_s2_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m32_r128_s2_v1 : List ℕ := pCat wc_rkmTraj_m32_r128_s2_v1_p0 (pCat
  wc_rkmTraj_m32_r128_s2_v1_p1 wc_rkmTraj_m32_r128_s2_v1_p2)
private def wc_rkmTraj_m32_r128_s2_v2_p0 : List ℕ := [1999999934486385,1999999811369043,
  1999999027973292,1999998486154698,1999995166410737,1999994657560219,1999988532852259,
  1999990704171715,1999988129516922,1999994374822968,2000001278605994,2000005478185085,
  2000011213124450,2000007144424217,1999999530684705,1999994620594550,1999989622125229,
  1999993282047167,2000003084952875,2000007692192855,2000008604887558,2000004198381648,
  1999993775726552,1999989614035979,1999994547241314,2000001167772739,2000008137023476,
  2000010332373972,2000002077574408,1999992556300040,1999990674298628,1999994112834171,
  2000001735636380,2000010319818405,2000009966885405,2000000636901718,1999992725213472,
  1999990184347681,1999992824232367,2000001889624657,2000011021204888,2000010625424806,
  2000002643916386,1999994764697808,1999989462749466,1999989300793521,1999997409162656,
  2000008125713559,2000012252233190,2000009263728933,2000003045861324,1999994530454366,
  1999986939862590,1999986739138336,1999994057899591,2000002600845944,2000009393405680,
  2000014597335018,2000014814748297,2000006978315256,1999996206319390,1999991892882602,
  1999997125404579,2000002818518950]
private def wc_rkmTraj_m32_r128_s2_v2_p1 : List ℕ := [1999987526590073,1999931462984762,
  1999858649441358,1999878645022184,2000143292135313,2000660365145816,2001047494273852,
  2000476071160227,1998088637073595,1993956753574330,1990217106360050,1991634466132750,
  2004845937781380,2036113027374798,2088308082153983,2158529650306121,2237680489249550,
  2312497206745515,2369343947268368,2398239256539744,2395525834233786,2364293531623889,
  2312690521449347,2251061454582665,2189100483152504,2133913550959109,2089317749975314,
  2056185885122588,2033369547674663,2018726152264225,2009934897945886,2004984808944709,
  2002365805431973,2001062084226425,2000450948436714,2000181033987034,2000068687480254,
  2000024617358717,2000008328321295,2000002657504883,2000000799061471,2000000226152676,
  2000000060172291,2000000015029610,2000000003518477,2000000000770586,2000000000157554,
  2000000000029996,2000000000005299,2000000000000863,2000000000000126,2000000000000015,
  2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m32_r128_s2_v2_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m32_r128_s2_v2 : List ℕ := pCat wc_rkmTraj_m32_r128_s2_v2_p0 (pCat
  wc_rkmTraj_m32_r128_s2_v2_p1 wc_rkmTraj_m32_r128_s2_v2_p2)
private def wc_rkmTraj_m32_r128_s3_hb_p0 : List ℕ := [138684157872796,194924823456593,
  237257662234108,272256964901213,302485836973509,329266917576802,353390639498015,375375051937564,
  395582083052519,414276759370642,431660284493773,447889844516131,463091128195803,477366595619005,
  490801139406826,503466079620906,515422056275241,526721170607562,537408601128747,547523844158926,
  557101680536988,566172939123344,574765107119906,582902823275727,590608280403379,597901556848559,
  604800891707508,611322915070700,617482841986445,623294636914401,628771153990890,633924257326300,
  638764924708577,643303337430715,647548958447183,651510600659928,655196486813603,658614302222943,
  661771241348657,664674049070802,667329057372309,669742218033599,671919131847223,673865074785303,
  675585021489150,677083666397520,678365442785481,679434539948405,680294918733843,680950325597104,
  681404305333294,681660212618889,681721222478916,681590339781165,681270407846182,680764116250663,
  680074007892255,679202485375218,678151816768903,676924140784334,675521471408207,673945702028264,
  672198609079110,670281855233137]
private def wc_rkmTraj_m32_r128_s3_hb_p1 : List ℕ := [668196992157049,665945462850711,
  663528603581368,660947645422847,658203715405989,655297837283223,652230931906921,649003817217786,
  645617207836059,642071714244749,638367841550185,634505987801130,630486441843145,626309380680004,
  621974866308448,617482841986445,612833127888178,608025416091110,603059264831440,597934091953889,
  592649167469694,587203605122737,581596352847297,575826181981716,569891675079509,563791212132510,
  557522954988485,551084829707162,544474506552316,537689377261484,530726529166799,523582715657111,
  516254322369177,508737328369061,501027261427232,493119146293375,485007444627707,476685984928807,
  468147880392035,459385432107971,450390014326100,441151937607860,431660284493773,421902710694768,
  411865202617211,401531778991299,390884120111446,379901102127597,368558205026034,356826749925996,
  344672901654128,332056342105516,318928471417825,305229914334461,290886973459339,275806430085937,
  259867643377487,242910007505857,224711928293165,204953052701056,183139853265055,158438731594668,
  129219410625216,91261733041027]
private def wc_rkmTraj_m32_r128_s3_hb : List ℕ := pCat wc_rkmTraj_m32_r128_s3_hb_p0
  wc_rkmTraj_m32_r128_s3_hb_p1
private def wc_rkmTraj_m32_r128_s3_v0_p0 : List ℕ := [1999999934486385,2000000188630957,
  1999999027973292,1999998486154698,1999995166410737,1999994657560219,1999988532852259,
  2000009295828285,2000011870483078,1999994374822968,1999998721394006,1999994521814915,
  1999988786875550,1999992855575783,1999999530684705,1999994620594550,1999989622125229,
  2000006717952833,2000003084952875,2000007692192855,2000008604887558,1999995801618352,
  1999993775726552,1999989614035979,1999994547241314,2000001167772739,2000008137023476,
  1999989667626028,1999997922425592,2000007443699960,2000009325701372,2000005887165829,
  1999998264363620,1999989680181595,1999990033114595,1999999363098282,2000007274786528,
  2000009815652319,2000007175767633,2000001889624657,2000011021204888,2000010625424806,
  1999997356083614,1999994764697808,2000010537250534,1999989300793521,2000002590837344,
  2000008125713559,2000012252233190,1999990736271067,1999996954138676,2000005469545634,
  2000013060137410,2000013260861664,1999994057899591,1999997399154056,2000009393405680,
  2000014597335018,1999985185251703,2000006978315256,2000003793680610,1999991892882602,
  2000002874595421,2000002818518950]
private def wc_rkmTraj_m32_r128_s3_v0_p1 : List ℕ := [1999987526590073,2000068537015238,
  1999858649441358,1999878645022184,1999856707864687,1999339634854184,1998952505726148,
  1999523928839773,1998088637073595,1993956753574330,1990217106360050,2008365533867250,
  2004845937781380,2036113027374798,2088308082153983,2158529650306121,2237680489249550,
  2312497206745515,2369343947268368,2398239256539744,2395525834233786,2364293531623889,
  2312690521449347,2251061454582665,2189100483152504,2133913550959109,2089317749975314,
  2056185885122588,2033369547674663,2018726152264225,2009934897945886,2004984808944709,
  2002365805431973,2001062084226425,2000450948436714,2000181033987034,2000068687480254,
  2000024617358717,2000008328321295,2000002657504883,2000000799061471,2000000226152676,
  2000000060172291,2000000015029610,1999999996481523,1999999999229414,2000000000157554,
  2000000000029996,2000000000005299,2000000000000863,2000000000000126,2000000000000015,
  2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTraj_m32_r128_s3_v0_p2 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m32_r128_s3_v0 : List ℕ := pCat wc_rkmTraj_m32_r128_s3_v0_p0 (pCat
  wc_rkmTraj_m32_r128_s3_v0_p1 wc_rkmTraj_m32_r128_s3_v0_p2)
private def wc_rkmTraj_m32_r128_s3_v1_p0 : List ℕ := [1999996905703735,1999998566969855,
  2000004640377071,2000001160555317,1999992319195977,2000001376309284,2000003880334119,
  2000002741922640,2000001907269971,1999987573256270,1999999963437888,2000007035573273,
  2000008602155068,1999995970596019,1999996121475339,1999999516895400,1999991425728577,
  1999990367959811,1999996729925494,1999996450691693,2000001504035341,2000006445153845,
  2000008932884894,1999996286579492,2000001456248460,1999996777363180,2000003533411889,
  1999987057775391,2000001829021416,1999995884097956,1999994543676157,1999993846381668,
  1999984325527541,1999991105794723,2000001443638597,2000015072560570,1999998951588821,
  2000010113571823,1999999572999869,1999996993879440,1999986683421763,2000016388291282,
  1999994296316725,2000004804115734,1999961052106922,2000038981228677,1999934195186096,
  2000097109424814,1999865261201995,2000251763367809,1999551301937392,2000824344506457,
  1998592276805622,2002143536047885,1997029393225553,2003698301005148,1995944719337422,
  2003657529013405,1997732661829955,2000085984768534,2002253778764130,1996546624399560,
  2002481713651735,2000384578714719]
private def wc_rkmTraj_m32_r128_s3_v1_p1 : List ℕ := [1996986581648448,2002922816835734,
  2000145500812548,1996927761162019,2002348131895219,2001349532988241,1996852584603053,
  2000406032189062,2002863224511180,1998558800725596,1997700814543749,2001836043217862,
  2001932305335180,1998225839320885,1998196334863146,2001448444289149,2001824370071378,
  1999013326228289,1998102115491171,2000548352078336,2002256692463309,2000168521580713,
  1996819595853144,1997284244310258,2002887533759692,2008564624261928,2006306924575649,
  1992012699994704,1970870422705730,1957406026532251,1969478520792593,2019151877875216,
  2105431699878650,2212960920497559,2317419063223442,2394726085698243,2429451142133921,
  2418828223115868,2371470325987147,2302444215197122,2227507213410735,2158841373973027,
  2103274195982342,2062679324553810,2035571609998242,2018898620253826,2009405925336580,
  2004386683008489,2001916848252056,2000784423805313,2000300372039556,2000107491416972,
  2000035887997345,2000011152906072,2000003216407954,2000000857381161,2000000210168239,
  2000000047064441,2000000009547518,2000000001735435,2000000000278530,2000000000038654,
  2000000000004487,2000000000000408]
private def wc_rkmTraj_m32_r128_s3_v1_p2 : List ℕ := [2000000000000023]
private def wc_rkmTraj_m32_r128_s3_v1 : List ℕ := pCat wc_rkmTraj_m32_r128_s3_v1_p0 (pCat
  wc_rkmTraj_m32_r128_s3_v1_p1 wc_rkmTraj_m32_r128_s3_v1_p2)
private def wc_rkmTraj_m32_r128_s3_v2_p0 : List ℕ := [1999999630276848,1999996696030001,
  2000006874254848,2000000036087647,1999994779684810,1999995484074226,1999997970763010,
  1999996954474109,2000004247455352,1999996931448550,2000006981937692,1999999675326731,
  2000007848814252,1999989901182807,1999990873253070,2000000569953565,2000001673465685,
  2000013500601970,1999996088289658,2000003147606184,1999993188896235,2000006034167909,
  1999981435793841,2000015970761288,1999978439427970,2000047016113650,1999922260270684,
  2000132447523796,1999790655255417,2000352549435864,1999433469844647,2000883273757342,
  1998662923870196,2001869425618909,1997503167060211,2003054490516305,1996610709315452,
  2003273226063935,1997406991276571,2001378574258571,2000197625644885,1998312846561641,
  2002572364977263,1997562049882870,2001220536909105,2000596066490909,1997888372210439,
  2002441042837339,1998743208427424,1999173630321982,2002308983555043,1997895121016634,
  2000202667254003,2001902048098049,1997643268177766,2000640092848004,2001722168110366,
  1997625041645455,2000547194175678,2001902896401481,1997802152276824,1999930445191298,
  2002219697057160,1998370719946130]
private def wc_rkmTraj_m32_r128_s3_v2_p1 : List ℕ := [1998957483155812,2002309614137007,
  1999549429682820,1997998268314996,2001574936259829,2001156887007150,1997911446796916,
  1999794877227812,2002105199070260,1999413399039712,1998140946754837,2001109257053007,
  2001527794619751,1998608414350546,1998777232410605,2001526795733241,2001040025626485,
  1998462496021641,1999042425434107,2001503812437357,2001006384576815,1998575242641784,
  1998826359853809,2001313902271646,2001507029697717,1998901382485149,1997943847884144,
  2000598997202390,2002868425547494,2000711549477159,1996506204398438,1996542237346866,
  2002395947468183,2007354991018912,2003435076990156,1991947556712557,1985200365512997,
  1995080199389789,2018354894727959,2034198247268042,2019701857277831,1972144828245675,
  1918656911535917,1902999755995895,1957762485733542,2082015665678882,2239888746546049,
  2379715688958272,2459829219360525,2465260299716863,2408328995281919,2316969070483329,
  2220070773455886,2137547673498884,2077654359348862,2039644103266328,2018285548891261,
  2007598243220157,2002829950973182,2000937217680319,2000272673836237,2000068401544637,
  2000014346185964,2000002374858341]
private def wc_rkmTraj_m32_r128_s3_v2_p2 : List ℕ := [2000000269020986]
private def wc_rkmTraj_m32_r128_s3_v2 : List ℕ := pCat wc_rkmTraj_m32_r128_s3_v2_p0 (pCat
  wc_rkmTraj_m32_r128_s3_v2_p1 wc_rkmTraj_m32_r128_s3_v2_p2)
private def wc_rkmTraj_m32_r128_s4_hb_p0 : List ℕ := [137576358926016,193367778171546,
  235362465317821,270082196105718,300069602150765,326636757433812,350567780822282,372376583377330,
  392422202200282,410967546806311,428212213597545,444312133077139,459391990010537,473553426040257,
  486880655671315,499444429265894,511304902449980,522513760280414,533115820385418,543150263591399,
  552651592910437,561650390944253,570173925328994,578246638001181,585890544498816,593125562783233,
  599969786258103,606439712173948,612550434042381,618315804775975,623748575833147,628860516554635,
  633662517038615,638164677250656,642376384555834,646306381459280,649962825022960,653353339171876,
  656485060897909,659364681203506,661998481492179,664392366001960,666551890786679,668482289674376,
  670188497569290,671675171411342,672946709062923,674007266355618,674860772498016,675510944019014,
  675961297398154,676215160515001,676275683032711,676145845816413,675828469474412,675326222099263,
  674641626276132,673777065417451,672734789475398,671516920077129,670125455121762,668562272872795,
  666829135574804,664927692618873]
private def wc_rkmTraj_m32_r128_s4_hb_p1 : List ℕ := [662859483277107,660625939022793,
  658228385449169,655668043796337,652946032092496,650063365912415,647020958752765,643819622020597,
  640460064627820,636942892180947,633268605751556,629437600208824,625450162091036,621306466988071,
  617006576401447,612550434042381,607937861521494,603168553375909,598242071370604,593157838000513,
  587915129107970,582513065516207,576950603563328,571226524402132,565339421908595,559287689015059,
  553069502252314,546682804246575,540125283871377,533394353698868,526487124327361,519400375079398,
  512130520463008,504673571663180,497025092174228,489180146487773,481133240503887,472878252018654,
  464408349238726,455715894753011,446792331712860,437628048078241,428212213597545,418532582586984,
  408575253392489,398324372401475,387761766244829,376866479808272,365614188942167,353976443850563,
  341919679633006,329403900242664,316380894029361,302791760021726,288563389513104,273603308421207,
  257791839579479,240969660067441,222916945785354,203315902651589,181676945463093,157173134552569,
  128187215389727,90532740967997]
private def wc_rkmTraj_m32_r128_s4_hb : List ℕ := pCat wc_rkmTraj_m32_r128_s4_hb_p0
  wc_rkmTraj_m32_r128_s4_hb_p1
private def wc_rkmTraj_m32_r128_s4_v0_p0 : List ℕ := [2000000369723152,1999996696030001,
  1999993125745152,1999999963912353,1999994779684810,1999995484074226,2000002029236990,
  1999996954474109,2000004247455352,2000003068551450,1999993018062308,1999999675326731,
  1999992151185748,1999989901182807,1999990873253070,1999999430046435,1999998326534315,
  1999986499398030,2000003911710342,2000003147606184,1999993188896235,1999993965832091,
  1999981435793841,1999984029238712,2000021560572030,2000047016113650,1999922260270684,
  1999867552476204,1999790655255417,1999647450564136,1999433469844647,1999116726242658,
  1998662923870196,1998130574381091,2002496832939789,2003054490516305,2003389290684548,
  2003273226063935,1997406991276571,2001378574258571,2000197625644885,1998312846561641,
  2002572364977263,1997562049882870,2001220536909105,2000596066490909,1997888372210439,
  2002441042837339,2001256791572576,2000826369678018,2002308983555043,1997895121016634,
  2000202667254003,2001902048098049,1997643268177766,2000640092848004,2001722168110366,
  1997625041645455,1999452805824322,1998097103598519,1997802152276824,1999930445191298,
  1997780302942840,1998370719946130]
private def wc_rkmTraj_m32_r128_s4_v0_p1 : List ℕ := [1998957483155812,1997690385862993,
  1999549429682820,1997998268314996,2001574936259829,2001156887007150,2002088553203084,
  2000205122772188,2002105199070260,2000586600960288,1998140946754837,1998890742946993,
  1998472205380249,2001391585649454,2001222767589395,2001526795733241,1998959974373515,
  1998462496021641,1999042425434107,1998496187562643,1998993615423185,1998575242641784,
  1998826359853809,2001313902271646,1998492970302283,2001098617514851,1997943847884144,
  2000598997202390,2002868425547494,1999288450522841,2003493795601562,2003457762653134,
  2002395947468183,2007354991018912,2003435076990156,2008052443287443,2014799634487003,
  2004919800610211,2018354894727959,2034198247268042,2019701857277831,2027855171754325,
  2081343088464083,2097000244004105,2042237514266458,2082015665678882,2239888746546049,
  2379715688958272,2459829219360525,2465260299716863,2408328995281919,2316969070483329,
  2220070773455886,2137547673498884,2077654359348862,2039644103266328,2018285548891261,
  2007598243220157,2002829950973182,2000937217680319,2000272673836237,1999931598455363,
  1999985653814036,1999997625141659]
private def wc_rkmTraj_m32_r128_s4_v0_p2 : List ℕ := [1999999730979014]
private def wc_rkmTraj_m32_r128_s4_v0 : List ℕ := pCat wc_rkmTraj_m32_r128_s4_v0_p0 (pCat
  wc_rkmTraj_m32_r128_s4_v0_p1 wc_rkmTraj_m32_r128_s4_v0_p2)
private def wc_rkmTraj_m32_r128_s4_v1_p0 : List ℕ := [1999999475890370,1999997956692513,
  1999995224412282,2000005152311261,2000007144088269,1999996599163199,1999998954190687,
  2000002015416837,1999993693975861,2000006708129888,1999993323668832,1999984927008423,
  2000040153813985,1999902478013420,2000189632127167,1999694058651383,2000339758958266,
  1999764508595556,1999902504284513,2000628031720766,1998859865788887,2001135784625290,
  1999799018785434,1998569524487965,2002706032522786,1997599339060363,2000444046893490,
  2001723122565312,1997519933775898,2001407493034864,2000481027584496,1998098698960878,
  2001973793702062,1999341194028946,1998797567227191,2001846523934207,1999207104435085,
  1999670087955198,2001167816315675,1997656467335487,2001267430649157,2002006769299979,
  1997919252074605,2000070454939170,1999507331315697,1998571673485213,2004192063830351,
  1999866443817440,1999404623711157,1997823354530479,1998669686949147,1997576942062257,
  1998867566358586,2001152753471961,2002310806180820,2002688158364182,2000336345110319,
  2002026076462410,2000475218215405,2001533090073788,2000614739873133,1999981917478904,
  2000347206139428,1999396521993429]
private def wc_rkmTraj_m32_r128_s4_v1_p1 : List ℕ := [1998737470729117,1999859028326555,
  2001538324446808,2001474718530073,1999641389647269,2002137297164245,1999147463236910,
  2001106607139273,1999595306694917,2001127525292472,2001548467675943,1998603613541821,
  2000487001432455,1998107358983119,1999841361889088,1999997625537860,1996475398291500,
  2000335215533832,1997569285708778,1997524606842563,1999183165671056,1994201118491297,
  2002838617521079,2001641448158122,2000322654405125,2004003137761196,1995879498261442,
  2002142021861496,2000077253373817,1996639078984312,2003047707702012,2004530292355975,
  1992358121240885,2003650006759709,2006341139786541,1980806589709174,2012146647242116,
  2006934211456454,1974340842526124,2013963671841199,2015015282190630,1970426286277543,
  2001536706730044,2032762561911518,1985796959146502,1971821067037291,2028552629343654,
  2038246626195744,1977981532505102,1963662807928933,2034661399096902,2087201340900681,
  2040719940610748,1958813221118089,1972515386875617,2130492428518272,2353300753859680,
  2511682387858140,2531874671043620,2431346306421964,2281259346028352,2148325351360174,
  2062286886974414,2019779424950687]
private def wc_rkmTraj_m32_r128_s4_v1_p2 : List ℕ := [2004102597814358]
private def wc_rkmTraj_m32_r128_s4_v1 : List ℕ := pCat wc_rkmTraj_m32_r128_s4_v1_p0 (pCat
  wc_rkmTraj_m32_r128_s4_v1_p1 wc_rkmTraj_m32_r128_s4_v1_p2)
private def wc_rkmTraj_m32_r128_s4_v2_p0 : List ℕ := [2000003753753996,1999975999471818,
  2000071031582723,1999845487660952,2000205751862396,1999899550455513,1999821968069414,
  2000463358844271,1999604439109899,1999677393923949,2001354073946051,1998225385491849,
  2000791599232954,2001140914678196,1997751131394335,2001150186401627,2001368974930209,
  1997332573087456,2001141360647488,2001584360261852,1997655091869820,2000335989409118,
  2001999811491980,1997836772238362,2000324691254035,2001420318899095,1998491974635752,
  1999919535776377,2002146844374465,1996911986302760,2002079690231399,1999956012560223,
  1998646746146870,2001285672100581,1999773285790230,1999345203830050,2000209308322405,
  2001170588964551,1998336963332445,2000698833499523,2000085268980117,2000022390240461,
  2000117482217408,1999688879717229,1999945448280182,1999707008711817,2000612069042874,
  2001123309444027,1998209069854119,1999622870306578,1999931576765645,2002410863678936,
  1998990733943604,1999768014353027,1998919866279651,1999567588305352,2001931259471354,
  1999113881781696,2001437298183265,1999810533470497,1998569026840997,1998950914931433,
  1998812071082941,2003141906423911]
private def wc_rkmTraj_m32_r128_s4_v2_p1 : List ℕ := [2000507833018038,2000979690130964,
  2001509607189428,1996232890556325,1999848301817543,1996237210313246,1999911667430657,
  2001647188624323,1997181103824724,2004392861734428,1998301666090096,2003123277267128,
  2002026523888290,2000409949310687,2003019445800678,1998888717170675,1998066517119231,
  2001549919349584,2000208981237648,1998343603611962,2005554021056819,1992725970179945,
  2007242442244888,2000994720985933,1990458864208312,2015782471543793,1992041395795776,
  1996580181578494,2014257856610418,1982637893973290,2006107499585095,2012051252476856,
  1977979682982182,2008824546895555,2004801114425700,1974770483812914,2014552258846028,
  2009765997183243,1975845209904595,2013873653312887,2013467239919929,1972875060984797,
  2008217142509186,2024997542540217,1974728393281486,1990524095090812,2034124001241108,
  1989525772732066,1964288683230450,2026459507283498,2028266707273291,1954809916285261,
  1975726208008123,2060850329500824,2021897096610558,1921037950909621,1976856956356350,
  2117511655964232,2068565073135806,1866402795270545,1875191971564555,2230703547319477,
  2602356506670913,2626902436475940]
private def wc_rkmTraj_m32_r128_s4_v2_p2 : List ℕ := [2339528564350313]
private def wc_rkmTraj_m32_r128_s4_v2 : List ℕ := pCat wc_rkmTraj_m32_r128_s4_v2_p0 (pCat
  wc_rkmTraj_m32_r128_s4_v2_p1 wc_rkmTraj_m32_r128_s4_v2_p2)
private def wc_rkmTraj_m32_r128_s1_hb : List ℕ := [184300113189025,257583335794095,
  311725532003443,355615391714680,392737254757341,424898127182883,453182950123680,478305898461462,
  500767945235160,520937300958288,539094444413837,555459141801057,570207562207015,583483603190195,
  595406659034360,606077111530250,615580311184369,623989527671969,631368178110863,637771537785221,
  643248072448587,647840488902610,651586572373945,654519860087556,656670187190987,658064131842873,
  658725379576261,658675022158591,657931802546555,656512314803277,654431165750122,651701103484665,
  648333116579284,644336506684780,639718936325943,634486452830955,628643488531961,622192836560920,
  615135600692342,607471116695024,599196841478062,590308204860595,580798416935608,570658221561424,
  559875583249355,548435290253310,536318450452508,523501847801226,509957114366138,495649654141563,
  480537226399981,464568052323979,447678238619245,429788196750956,410797540487493,390577596357606,
  368960011945771,345718660209484,320539297767662,292965043025462,262288953088889,227313120336027,
  185689723891949,131334037438197]
private def wc_rkmTraj_m32_r128_s1_v0 : List ℕ := [2009945411730510,2033182356621914,
  2076645991423185,2141449363306372,2221087803555854,2302081856155241,2368006412170770,
  2405101190518646,2406810450822546,2375318504069627,2319811392706888,2252715462259001,
  2185760182164944,2127309970223464,2081487657465342,2048767945061516,2027306823928957,
  2014308161797475,2007013898491808,2003214297276350,2001375430905754,2000548600010000,
  2000203469726427,2000069952038862,2000022200779227,2000006469414160,2000001718699800,
  2000000412285922,2000000088109320,2000000016446100,2000000002597436,2000000000327421,
  1999999999971462]
private def wc_rkmTraj_m32_r128_s1_v1_p0 : List ℕ := [1999999999999991,2000000000000079,
  2000000000000017,2000000000003020,2000000000016714,2000000000130034,2000000000744174,
  2000000003982850,2000000018861427,2000000081387538,2000000320637480,2000001161843755,
  2000003890747084,2000012092449669,2000035007143214,2000094688794049,2000239939161050,
  2000570920128320,2001278222119220,2002697566508362,2005374755965701,2010124459020609,
  2018052890591552,2030503980373547,2048889809264454,2074387364447745,2107527653207461,
  2147761228336413,2193134747270263,2240228130589187,2284459527396477,2320765245312081,
  2344532329709331,2352552409965119,2343727043354968,2319312287178626,2282628086928759,
  2238324356012430,2191425439297009,2146420387576064,2106618596390744,2073878302272408,
  2048689797896200,2030502749490251,2018151684639125,2010252219240337,2005490737823651,
  2002785347084865,2001336635475952,2000605890450914,2000258989877358,2000104187817337,
  2000039353774306,2000013918697289,2000004594436177,2000001409850358,2000000400241706,
  2000000104487049,2000000024891411,2000000005356461,2000000001026825,2000000000171825,
  2000000000024300,2000000000002737]
private def wc_rkmTraj_m32_r128_s1_v1_p1 : List ℕ := [2000000000000210]
private def wc_rkmTraj_m32_r128_s1_v1 : List ℕ := pCat wc_rkmTraj_m32_r128_s1_v1_p0
  wc_rkmTraj_m32_r128_s1_v1_p1
private def wc_rkmTraj_m32_r64_s1_hb : List ℕ := [218056913920000,303560622456216,365882977168265,
  415670992160000,457115702333381,492399410397026,522837706588300,549300173968391,572399399040000,
  592587623662439,610210940413048,625541864190906,638799999587747,650165740593762,659789684482456,
  667799298880000,674303766366283,679397583592484,683163287172044,685673553500072,686992840769722,
  687178690317494,686282770460322,684351722924680,681427856000000,677549717295690,672752570922295,
  667068798060935,660528235571817,653158464076268,644985054520999,636031780384453,626320801262095,
  615872822462253,604707234378377,592842234720000,580294936140955,567081461367836,553217027580478,
  538716021511308,523592066497860,507858082531921,491526340191360,474608509210149,457115702333381,
  439058515013128,420447061424503,401291007216807,381599599360000,361381693400257,340645778398758,
  319399999793873,297652180397809,275409839713590,252680211736602,229470261386033,205786699695260,
  181635997875895,157024400357808,131957936896491,106442433829555,80483524555724,54086659302237,
  27257114240000]
private def wc_rkmTraj_m32_r64_s1_v0 : List ℕ := [2007761510658883,2027320913978486,
  2066206739044504,2127457210036269,2206618280688247,2291085961871336,2363460455722173,
  2407606789213030,2414451258116934,2384739206247904,2327777513881399,2257287735786038,
  2186626085809904,2125368794237096,2078116483685292,2045192284203053,2024286820499913,
  2012124831803877,2005620760352357,2002417360180117,1999036813278954,1999645140176168,
  1999879425720719,2000037656525581,2000010762804694,2000002799415693,2000000657755825,
  2000000138237204,2000000025632133,2000000004109641,2000000000551775,2000000000058497,
  2000000000004238]
private def wc_rkmTraj_m32_r64_s1_v1_p0 : List ℕ := [1999564167192355,1999627422200231,
  2000100052474523,2000345014225645,2000024953283019,1999695301263849,1999910851714794,
  2000270993402566,2000126472267432,1999754243494446,1999849333453899,2000227530314857,
  2000168495040925,1999785781288252,1999816236082074,2000203649484194,2000198914023244,
  1999806406845899,1999784312410914,2000181601426824,2000235265000228,1999835035756920,
  1999741870135655,2000142363789602,2000290642477269,1999895496283858,1999629161085796,
  1999848337825237,2000025271771503,2000248571033946,2002715824534023,2011400452034524,
  2030952123309023,2066032528162189,2119956018176118,2191565653455879,2272333584459492,
  2347074571841539,2398991797003694,2416148916707578,2395672223296929,2343998496020643,
  2273817401074161,2199496021511906,2132861199097811,2080724799520632,2044646373057968,
  2022423561382497,2010202118277889,2004193817129539,2001553180730829,2000516564730583,
  2000153703688782,2000040734043960,2000009562997121,2000001975641203,2000000356205797,
  2000000055462580,2000000007356212,2000000000815961,2000000000073761,2000000000005226,
  2000000000000270,2000000000000008]
private def wc_rkmTraj_m32_r64_s1_v1_p1 : List ℕ := [2000000000000000]
private def wc_rkmTraj_m32_r64_s1_v1 : List ℕ := pCat wc_rkmTraj_m32_r64_s1_v1_p0
  wc_rkmTraj_m32_r64_s1_v1_p1
private def wc_rkmTrajPack_m2_r128_s4_hb_p0 : List ℕ := [169705009548288,238124132933142,
  289344922292274,331455096774000,367613439426215,399452762992630,427950505342239,453748347793862,
  477295339354560,498920850789627,518875354081339,537354855685652,554516352976696,570488049165021,
  585376351838498,599270814967392,612247719618539,624372726509736,635702879310118,646288143507379,
  656172606432571,665395425701339,673991587908680,681992522182539,689426601289920,696319554608129,
  702694811281237,708573787533871,713976128917082,718919915880583,723421839273088,727497351008341,
  731160794086106,734425515344385,737303963683275,739807775999568,741947852673038,743734424126906,
  745177109728527,746284970088686,747066553648535,747529938304576,747682768707753,747532289778201,
  747085376898438,746348563182115,745328064160215,744029800180134,742459416773760,740622303217254,
  738523609476826,736168261710441,733560976474555,730706273767006,727608489021703,724271784157332,
  720700157770659,716897454554877,712867374014596,708613478541340,704139200906633,699447851223792,
  694542623424290,689426601289920]
private def wc_rkmTrajPack_m2_r128_s4_hb_p1 : List ℕ := [684102764077882,678573991772284,
  672843069992317,666912694584480,660785475923694,654463942945823,647950546932090,641247665064053,
  634357603766127,627282601851188,620024833483445,612586410971568,604969387403983,597175759137238,
  589207468147493,581066404254341,572754407225472,564273268769989,555624734427620,546810505360476,
  537832240053540,528691555929585,519390030883808,509929204743082,500310580654385,490535626406608,
  480605775689692,470522429294739,460286956258499,449900694955403,439364954140110,428681013943310,
  417850126823384,406873518476314,395752388706106,384487912257840,373081239615312,361533497765143,
  349845790929073,338019201266082,326054789545877,313953595795174,301716639918142,289344922292274,
  276839424340893,264201109083425,251430921664499,238529789862887,225498624581228,212338320317436,
  199049755618638,185633793518441,172091281958285,158423054193601,144629929185451,130712711978287,
  116672194064448,102509153735955,88224356424180,73818555027866,59292490230034,44646890804219,
  29882473910478,14999945381615]
private def wc_rkmTrajPack_m2_r128_s4_hb : List ℕ := pCat wc_rkmTrajPack_m2_r128_s4_hb_p0
  wc_rkmTrajPack_m2_r128_s4_hb_p1
private def wc_rkmTrajPack_m2_r128_s4_v0_p0 : List ℕ := [1999999928665753,1999999082640901,
  1999997329421789,1999995067276832,1999992888407436,1999991350916850,1999991203936980,
  1999993210831735,1999996993892462,2000000091940288,1999999027760837,1999992245796048,
  1999982443280491,2000024228750541,1999977812822947,1999988919627813,2000002605566244,
  2000009157759635,2000003577187860,2000006390769217,2000000006965353,2000036768135428,
  2000063119962346,2000066246071491,2000554222005212,2001365604651602,2001609302182670,
  2001200032134113,2011454613844894,2034694973193705,2075550082065215,2134985332885469,
  2208211762174921,2284642593264175,2350401679556212,2392547090239954,2403205048825513,
  2381828919202124,2334767260698356,2272619060912494,2206730247206320,2146263851994144,
  2096695530544873,2059799175653830,2034620978169309,2018773343098389,2009536301858005,
  2004537441812174,2002021479696120,2000842679315017,2000328367757052,2000119449008194,
  2000040492369828,2000012763572377,2000003730533554,1999998992488136,2000000250317354,
  2000000056890741,2000000011741184,2000000002178907,2000000000358675,2000000000051332,
  2000000000006183,2000000000000589]
private def wc_rkmTrajPack_m2_r128_s4_v0_p1 : List ℕ := [2000000000000037]
private def wc_rkmTrajPack_m2_r128_s4_v0 : List ℕ := pCat wc_rkmTrajPack_m2_r128_s4_v0_p0
  wc_rkmTrajPack_m2_r128_s4_v0_p1
private def wc_rkmTrajPack_m2_r128_s4_v1_p0 : List ℕ := [1999994509735649,2000012823190472,
  1999985865345106,2000000669410105,2000024196641592,1999948257968816,2000095079523284,
  1999815873773135,2000308217455674,1999612091196588,2000344152002137,1999840330630325,
  1999886677153937,2000327026461803,1999738455539732,1999899738595355,2000363440057890,
  1999833595239228,1999721785680211,2000326704117536,2000138205708438,1999572297844981,
  1999933725444802,2000467916845346,2000044772750463,1999483904504410,1999871610269642,
  2000522178729042,2000290943173185,1999542048770398,1999468438951348,2000203477111318,
  2000705065439487,2000272865223390,1999432716053277,1999182252819599,1999833189027939,
  2000756661733817,2001090166262253,2000485069333744,1999283935239374,1998246450592987,
  1998166417891902,1999542570201948,2002221537430026,2005041628891339,2005854987486721,
  2002350993451220,1993672461529035,1982137501839348,1973925390831315,1977843802592182,
  2002262430591734,2051394158010488,2122646362944320,2206398522833114,2288454805483577,
  2354184563473397,2392672590792528,2399353743570273,2376407028086795,2331151466969648,
  2273361308511181,2212579670187634]
private def wc_rkmTrajPack_m2_r128_s4_v1_p1 : List ℕ := [2156221448608969,2108764071129845,
  2071886799857014,2045182895938671,2027044832850581,2015435004328219,2008407823147552,
  2004375010288925,2002176126599846,2001035190903658,2000471135949367,2000205194050100,
  2000085533178261,2000034125701657,2000013031989552,2000004763402907,2000001666465132,
  2000000558018784,2000000178849349,2000000054870268,2000000016115214,2000000004531407,
  2000000001220063,2000000000314586,2000000000077686,2000000000018372,2000000000004159,
  2000000000000900,2000000000000184,2000000000000034,2000000000000005,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m2_r128_s4_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m2_r128_s4_v1 : List ℕ := pCat wc_rkmTrajPack_m2_r128_s4_v1_p0 (pCat
  wc_rkmTrajPack_m2_r128_s4_v1_p1 wc_rkmTrajPack_m2_r128_s4_v1_p2)
private def wc_rkmTrajPack_m2_r128_s4_v2_p0 : List ℕ := [2000409167785850,1999728614805810,
  1999799976439039,2000265020379587,2000095581205286,1999723695936573,1999940293080528,
  2000275828270190,2000053199318699,1999735778952466,1999947606186813,2000256793351015,
  2000059775885874,1999738432051994,1999913450328936,2000265415229086,2000140780863336,
  1999748593727533,1999789658336961,2000205031978053,2000276655177239,1999874897070249,
  1999675371169255,2000018434057481,2000342858146830,2000110204066328,1999684709563005,
  1999748130929780,2000218266542580,2000375784680610,1999964927506321,1999582001083283,
  1999795469684729,2000315918033000,2000411033359485,1999937102664804,1999530341370538,
  1999738522378407,2000299080731720,2000492161644060,2000062588029489,1999528949458867,
  1999535636278769,2000085121114269,2000556458555487,2000424304072691,1999823351066665,
  1999372597878485,1999521528514472,2000129506813367,2000651616189361,2000654500489061,
  2000135772861048,1999440493855560,1998994023941762,1999123491264654,1999967075136693,
  2001307854999949,2002379119940200,2002019241630394,1999483929371735,1995571791039171,
  1993013505910105,1995175146461756]
private def wc_rkmTrajPack_m2_r128_s4_v2_p1 : List ℕ := [2003331786043542,2014291109534861,
  2020613289060681,2014323835620809,1992539503130035,1961597349642448,1936606425416072,
  1935846008525078,1972538286301474,2048193495965371,2150920223938561,2259417148268053,
  2350518520694059,2406744289598365,2420836093358853,2396102298261506,2343358014496812,
  2276374864925224,2207770954212858,2146509647390867,2097219631004619,2060861115600305,
  2036014623256206,2020176386390645,2010714235874866,2005398112027698,2002582236850166,
  2001173409684900,2000506704359881,2000207968328128,2000081134224103,2000030084817535,
  2000010601030927,2000003548777478,2000001128145346,2000000340397671,2000000097426442,
  2000000026431532,2000000006791422,2000000001651113,2000000000379399,2000000000082295,
  2000000000016822,2000000000003232,2000000000000578,2000000000000094,2000000000000012,
  2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m2_r128_s4_v2_p2 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m2_r128_s4_v2 : List ℕ := pCat wc_rkmTrajPack_m2_r128_s4_v2_p0 (pCat
  wc_rkmTrajPack_m2_r128_s4_v2_p1 wc_rkmTrajPack_m2_r128_s4_v2_p2)
private def wc_rkmTrajPack_m2_r128_s6_hb_p0 : List ℕ := [147708964009887,207609464370056,
  252697092656768,289973958430927,322169960090192,350693806877408,376387368620150,399802406326118,
  421324400456429,441235624015092,459750373833400,477036064816487,493226564859067,508431001589124,
  522739791975007,536228897197715,548962903391545,560997302257689,572380212277302,583153699974911,
  593354809536087,603016375994783,612167675269609,620834949464584,629041835579090,636809718547694,
  644158024367219,651104465323431,657665246576729,663855241317395,669688140158607,675176579262138,
  680332250790305,685165998578940,689687901379808,693907345590294,697833089046277,701473317180724,
  704835692630479,707927399195488,710755180909481,713325376862183,715643952315078,717716526571683,
  719548397995746,721144566514410,722509753896027,723648422052387,724564789581329,725262846736970,
  725746368990287,726018929321746,726083909369627,725944509542076,725603758187379,725064519905170,
  724329503070958,723401266637343,722282226267217,720974659847216,719480712423271,717802400594436,
  715941616395962,713900130697859]
private def wc_rkmTrajPack_m2_r128_s6_hb_p1 : List ℕ := [711679596140813,709281549627223,
  706707414381293,703958501588402,701036011620387,697941034849886,694674552053305,691237434398450,
  687630443009139,683854228095273,679909327632740,675796165573135,671515049558509,667066168111074,
  662449587261978,657665246576729,652712954527430,647592383153630,642303061943957,636844370859651,
  631215532408276,625415602661016,619443461089468,613297799077396,606977106938654,600479659243811,
  593803498223741,586946414977490,579905928162345,572679259784395,565263307635286,557654613832179,
  549849328808849,541843169970980,533631374060816,525208642065974,516569075241822,507706100479399,
  498612382818501,489279722346809,479698931997164,469859691795362,459750373833400,449357830523421,
  438667136343797,427661270051132,416320719793644,404622987096704,392541956318269,380047082312944,
  367102328099434,353664751891171,339682591212709,325092606990647,309816306005624,293754403387774,
  276778407654799,258717261630084,239334950999174,218290275900900,195057592803902,168749057295747,
  137628302801000,97200547257902]
private def wc_rkmTrajPack_m2_r128_s6_hb : List ℕ := pCat wc_rkmTrajPack_m2_r128_s6_hb_p0
  wc_rkmTrajPack_m2_r128_s6_hb_p1
private def wc_rkmTrajPack_m2_r128_s6_v0_p0 : List ℕ := [1999997977019775,1999863893086627,
  1999964555053994,1999963284779938,1999896330598656,1999818288081885,1999740075444850,
  1999854894523240,2000155782286925,2000323260046394,1999988264264496,1999931181173358,
  1999509949995538,2000022291457616,1999557174118391,2000050902308901,1999768207813684,
  1999627308749005,1999766846489520,1999667117654676,1999875115980713,2000027751891513,
  2000178639034434,2000187724778017,2000110194010695,1999787665979749,2000466398720055,
  2000494461634535,2000758713613729,2000731982526164,1999124484431305,1998533090147839,
  1998450924252117,1998150748518786,2002191892499233,2002458411316029,2002184740274826,
  2001455503163798,2000432090260932,2001096924691384,1998247065527349,1997214345448726,
  1997458627324257,1998541083150222,1999394560764458,1998111032270739,1996782941514096,
  2002462280431709,1999826253900242,1997602555853669,1998043967235808,1998886924738463,
  2000416605092910,2001495029303515,2001582696317981,2000998212978734,1999341327777020,
  1997618727121271,1997864534202961,1999787809684179,2004460018465680,2003530153105453,
  2003676553687752,2007488219725505]
private def wc_rkmTrajPack_m2_r128_s6_v0_p1 : List ℕ := [2000874969269199,2008946742791685,
  2004607070083252,2010730747544011,2008270879866120,2010623534118260,2011058415901066,
  2009920779610156,2012943901678509,2009508579777007,2014240275354203,2010488585264752,
  2013997590494176,2012020319476952,2012784759001170,2014289633682818,2010614618031002,
  2017774332905025,2006366010100949,2022456397744499,2003455695075390,2022772421171254,
  2016699967221880,2014906894971944,2029593198803440,2007165240414403,2024965949637127,
  2026919443387748,2005965072422619,2038057140983143,2032113343084624,2012372212828784,
  2058270612662876,2064246689570086,2020306228921230,2043068490872747,2075884861129147,
  2041288673508715,2063035994508153,2205886145324456,2341087142013586,2429822207115810,
  2454656876742360,2420956002048571,2348858044437668,2262283934451231,2180464346909456,
  2114295843885307,2066886998849309,2036250431630468,2018213039625886,2008482217211494,
  2003657872440036,2001457761383749,1999464621667304,1999819468386276,2000055634458864,
  2000015577238977,2000003933196432,1999999113177311,1999999823845049,2000000030224199,
  2000000004340705,1999999999507557]
private def wc_rkmTrajPack_m2_r128_s6_v0_p2 : List ℕ := [2000000000038257]
private def wc_rkmTrajPack_m2_r128_s6_v0 : List ℕ := pCat wc_rkmTrajPack_m2_r128_s6_v0_p0 (pCat
  wc_rkmTrajPack_m2_r128_s6_v0_p1 wc_rkmTrajPack_m2_r128_s6_v0_p2)
private def wc_rkmTrajPack_m2_r128_s6_v1_p0 : List ℕ := [1999987839902866,2000142592295590,
  1999842543613530,2000328111310340,1999777845597046,2000012875925853,2000108548570502,
  1999782226878160,2000040971079368,1999963049003469,1999922580822391,1999814704176976,
  2000218312110257,2000044322213104,1999945969321576,1999887666524585,1999938194125371,
  1999222280976064,2000442905081394,1999426231568002,1999858504077796,2001011136484074,
  1999213400398321,2000620967121663,2000046575623285,1999658142864711,1999842138184299,
  2000354864228842,1999057992293582,2000725481687851,1999034647764882,2000596357784530,
  2000054082472869,1998471543956470,2000602321047014,1999736181175245,1998965535165018,
  2000477582923590,2000172295822687,1999799040675504,2001056627994080,1999064498998638,
  1997432720608250,2001738997270949,2000945504585732,2004347190226974,1995800337457152,
  2003424779877562,1997852145486971,1999343173487967,1998307527929608,1996462956580367,
  2002497421840629,2000883059401879,2003049276296835,1999217472446417,2003943172324345,
  2000362053743927,2000458818910680,2000113129446755,1996483115398386,2000230236444658,
  1993368766558511,2004548228022333]
private def wc_rkmTrajPack_m2_r128_s6_v1_p1 : List ℕ := [1993672216712378,2007002059851167,
  1991700201102681,2002593898465268,1994285745660860,1997620065536621,2006346835006470,
  1994327450476173,2009623658089427,1993745011179127,1998107975591838,2003906190759671,
  1989372996122451,2009660314451408,1997453921117063,1998632736921275,2012477748863793,
  1992154636473541,2009761968539517,2010975427753386,1993421160184618,2020908967416352,
  2009310689014264,1996340753947327,2026115311170197,2011303458733205,1994223425279806,
  2035219255979405,2005895296939439,1995604536829733,2040083280674389,2011047091514917,
  1991072416778109,2031296597784018,2022274559067970,1993281291874525,2020159008424244,
  2037647360240862,2009792762267517,2005843110145826,2035691379969014,2033993246648192,
  1999638422191280,2002458093262858,2056959402487612,2095310646816993,2058594454678525,
  1981124950243816,1951815700641957,2029778206891739,2195818565450626,2370972367092444,
  2479633334406280,2490381426825139,2418379133783561,2306099851073062,2195449556402107,
  2109743683958542,2053882162321428,2022743513156724,2008068361690064,2002346426364717,
  2000542772860294,2000094984437917]
private def wc_rkmTrajPack_m2_r128_s6_v1_p2 : List ℕ := [2000011044476216]
private def wc_rkmTrajPack_m2_r128_s6_v1 : List ℕ := pCat wc_rkmTrajPack_m2_r128_s6_v1_p0 (pCat
  wc_rkmTrajPack_m2_r128_s6_v1_p1 wc_rkmTrajPack_m2_r128_s6_v1_p2)
private def wc_rkmTrajPack_m2_r128_s6_v2_p0 : List ℕ := [1999723090920662,1999684664721161,
  2000221405159288,2000070517187427,2000154198287076,1999677781823390,2000191103099287,
  1999846739738037,2000097973017170,2000555551083592,1998977837585979,2000848011920457,
  1999988365682952,1999805588605042,1999672682206125,2000989991617879,1999027505507756,
  2000008176429936,2000940544010285,1999073699462535,2000239766162637,2000173822386675,
  1999259161231898,2000626509885619,1999618555405813,2000121859595869,1999397082518437,
  2002398741713587,1996324782237315,2003586353077270,1997568903975710,2000854595043766,
  1999296280007469,1998993568803129,2002295206540267,1996653678401285,2002815392636771,
  1998736105303914,2000102400848195,2000370460588823,2000657302075561,1999935082513320,
  1997117674203468,2004639647237159,1995376254987545,2005029225534422,1992908265500488,
  2006271854033335,1996069839744972,2004460323250635,1995650486688756,1997578236394947,
  2004801791438393,1995045368260592,2006543072732971,1993485392240889,2003433847028736,
  2000796886938516,1993436299676967,2007101482039513,1992187299466118,2006168886448175,
  2002456540287655,1995597582084568]
private def wc_rkmTrajPack_m2_r128_s6_v2_p1 : List ℕ := [2009184628087205,1990807481949825,
  2001888557645129,2002074644803244,1990037444844325,2009827296376258,1993254479461468,
  2000029583709777,2010031783397442,1993482836494374,2007102025444423,2005498548195666,
  1983323993222483,2012585051157406,1994727390463685,1990409594253207,2019778565285335,
  1982846068525088,1995596491581716,2013497721110285,1978839379080875,2007532140352758,
  2012471047000115,1980520288953818,2010482691139743,2006405946372063,1979088212888142,
  2011005848788783,2008053851101943,1981056418071183,2008730061317209,2013908940782715,
  1986383919040477,2005985494160392,2020003336908056,1996273792980582,2004301646876528,
  2026216790303912,2006421945946878,1997358255442401,2026830353403757,2025309203015828,
  1996314447220120,2010083382168408,2038983313419960,2015118496149065,1982383545131888,
  2017134358616330,2067130376627427,2033979987176131,1960751994656656,1976528411494182,
  2083335465313848,2134373714278158,2038460476260984,1899423318574271,1904834279911163,
  2111482910658355,2387464273546455,2551553492432298,2528861867362193,2376680294045379,
  2202696743882762,2079660251313971]
private def wc_rkmTrajPack_m2_r128_s6_v2_p2 : List ℕ := [2020083843971749]
private def wc_rkmTrajPack_m2_r128_s6_v2 : List ℕ := pCat wc_rkmTrajPack_m2_r128_s6_v2_p0 (pCat
  wc_rkmTrajPack_m2_r128_s6_v2_p1 wc_rkmTrajPack_m2_r128_s6_v2_p2)
private def wc_rkmTrajPack_m2_r128_s5_hb_p0 : List ℕ := [150165184013510,211061756671646,
  256899137251701,294795871860501,327527253778115,356525417364780,382646231717003,406450632955403,
  428330511611241,448572834544470,467395462081443,484968593033077,501428321353980,516885589331555,
  531432317458109,545145730056481,558091487249643,570326003498133,581898197434785,592850835099149,
  603221576676440,613043803207199,622347277432872,631158677831679,639502034457484,647399087850247,
  654869587037437,661931538838539,668601417886015,674894344693169,680824237531387,686403942686407,
  691645346746952,696559473868626,701156570400547,705446178824447,709437202608339,713137963298962,
  716556250953469,719699368829641,722574173106268,725187108284409,727544238820576,729651277460451,
  731513610673113,733136321528398,734524210311910,735681813131592,736613418735421,737323083730579,
  737814646369520,738091739047021,738157799633883,738016081757138,737669664122813,737121458965341,
  736374219697215,735430547823295,734292899176005,732963589520457,731444799572082,729738579463516,
  727846852692251,725771419575707]
private def wc_rkmTrajPack_m2_r128_s5_hb_p1 : List ℕ := [723513960235968,721076037132249,
  718459097155236,715664473293721,712693385880264,709546943419069,706226142995659,702731870264297,
  699064899005364,695225890240959,691215390892851,687033831962435,682681526207475,678158665285076,
  673465316324404,668601417886015,663566775257137,658361055023735,652983778850409,647434316387909,
  641711877215047,635815501706621,629744050701209,623496193821880,617070396278251,610464903949098,
  603677726509986,596706618328628,589549056800607,582202217737361,574662947344592,566927730239085,
  558992652841021,550853361341763,542505013276383,533942221516383,525158989228200,516148634000082,
  506903698900379,497415847662228,487675740448742,477672885677127,467395462081443,456830103445478,
  445961636054372,434772755622204,423243625838881,411351374107570,399069450514935,386366801987053,
  373206792291559,359545765572326,345331098607041,330498500733608,314968173486115,298639181008346,
  281380895161293,263019414296023,243314799467754,221920177077570,198301162782982,171555148401325,
  139916893697771,98816873864336]
private def wc_rkmTrajPack_m2_r128_s5_hb : List ℕ := pCat wc_rkmTrajPack_m2_r128_s5_hb_p0
  wc_rkmTrajPack_m2_r128_s5_hb_p1
private def wc_rkmTrajPack_m2_r128_s5_v0_p0 : List ℕ := [1999590832214150,1999728614805810,
  1999799976439039,2000265020379587,2000095581205286,1999723695936573,2000059706919472,
  2000275828270190,1999946800681301,1999735778952466,2000052393813187,1999743206648985,
  2000059775885874,2000261567948006,1999913450328936,2000265415229086,2000140780863336,
  1999748593727533,1999789658336961,1999794968021947,1999723344822761,2000125102929751,
  2000324628830745,2000018434057481,1999657141853170,1999889795933672,1999684709563005,
  1999748130929780,1999781733457420,1999624215319390,1999964927506321,1999582001083283,
  1999795469684729,1999684081967000,1999588966640515,2000062897335196,2000469658629462,
  2000261477621593,2000299080731720,1999507838355940,1999937411970511,1999528949458867,
  1999535636278769,2000085121114269,2000556458555487,2000424304072691,1999823351066665,
  1999372597878485,1999521528514472,1999870493186633,1999348383810639,1999345499510939,
  1999864227138952,1999440493855560,1998994023941762,1999123491264654,1999967075136693,
  1998692145000051,1997620880059800,1997980758369606,1999483929371735,2004428208960829,
  2006986494089895,2004824853538244]
private def wc_rkmTrajPack_m2_r128_s5_v0_p1 : List ℕ := [2003331786043542,2014291109534861,
  2020613289060681,2014323835620809,2007460496869965,2038402650357552,2063393574583928,
  2064153991474922,2027461713698526,2048193495965371,2150920223938561,2259417148268053,
  2350518520694059,2406744289598365,2420836093358853,2396102298261506,2343358014496812,
  2276374864925224,2207770954212858,2146509647390867,2097219631004619,2060861115600305,
  2036014623256206,2020176386390645,2010714235874866,2005398112027698,2002582236850166,
  2001173409684900,2000506704359881,2000207968328128,2000081134224103,1999969915182465,
  1999989398969073,2000003548777478,2000001128145346,1999999659602329,1999999902573558,
  2000000026431532,2000000006791422,2000000001651113,2000000000379399,1999999999917705,
  2000000000016822,2000000000003232,1999999999999422,2000000000000094,2000000000000012,
  2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m2_r128_s5_v0_p2 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m2_r128_s5_v0 : List ℕ := pCat wc_rkmTrajPack_m2_r128_s5_v0_p0 (pCat
  wc_rkmTrajPack_m2_r128_s5_v0_p1 wc_rkmTrajPack_m2_r128_s5_v0_p2)
private def wc_rkmTrajPack_m2_r128_s5_v1_p0 : List ℕ := [1999948825501264,1999799304187789,
  1999952170225446,1999907141684111,1999945502902180,2000062492712774,1999557023757415,
  1999391809632039,1999841918275814,2000153865675235,1999892999959043,2000008786086642,
  2000055824497552,1999960896419647,1999859734863523,1999791148492244,2000378084691402,
  1999979403385462,1999990122473914,2000127254484985,2000065313124058,1999783477025277,
  2000082930272047,1999626872568001,2000181864471495,1999870862525538,1999747626548804,
  2000152917749902,2000186619253452,2000315302639525,2000214737707332,1999935121039808,
  1999788777043429,1999805718100915,1999735597040545,1999848962810974,2000293075982123,
  1999831222267849,2000036187623768,2000073293460638,2000044026227081,2000080966436951,
  1999354905077159,2000007368320261,1999397991644198,2000714283197215,1999148361243607,
  2000267490504736,1998665875568637,2001609234711924,1996888340559325,2001816121064807,
  1997897703347405,2002907555519068,1998211622282978,2000903222404283,2001343962084818,
  1995949953665085,2003531388351808,1997963429113461,1999085594622468,2002239197952991,
  1999548234494435,2001218497371097]
private def wc_rkmTrajPack_m2_r128_s5_v1_p1 : List ℕ := [1996318322293576,1998709763632219,
  2009257034707236,1997236094261957,1985536576217692,2005495321858423,2016200168793957,
  1992115873010330,1981533518926740,2006553936132098,2018961393191796,1993707635544856,
  1973457503997238,1993074446633180,2024729740658395,2023894955994670,1992641901618141,
  1972432674357867,1990780112539491,2032051089781016,2057952137644534,2045462448191832,
  2005397290694427,1972331321222300,1979995769570851,2041844861131994,2146138256474336,
  2263961187951557,2363357432014879,2421586819113481,2430785531038622,2396967315901465,
  2334746024188909,2260840721037511,2189075013186138,2128092034521470,2081392399851112,
  2048654650887440,2027429108497654,2014603813968173,2007342123471174,2003479027893911,
  2001548726747498,2000645223663665,2000250639467171,2000090494759662,2000030295979907,
  2000009388697553,2000002690625642,2000000712877625,2000000174744874,2000000039719571,
  2000000008410976,2000000001672740,2000000000316103,2000000000057522,2000000000010175,
  2000000000001745,2000000000000283,2000000000000040,2000000000000003,2000000000000000,
  2000000000000000,2000000000000000]
private def wc_rkmTrajPack_m2_r128_s5_v1_p2 : List ℕ := [2000000000000000]
private def wc_rkmTrajPack_m2_r128_s5_v1 : List ℕ := pCat wc_rkmTrajPack_m2_r128_s5_v1_p0 (pCat
  wc_rkmTrajPack_m2_r128_s5_v1_p1 wc_rkmTrajPack_m2_r128_s5_v1_p2)
private def wc_rkmTrajPack_m2_r128_s5_v2_p0 : List ℕ := [2000002022980225,2000136106913373,
  2000035444946006,1999963284779938,1999896330598656,1999818288081885,2000259924555150,
  1999854894523240,1999844217713075,1999676739953606,1999988264264496,1999931181173358,
  2000490050004462,2000022291457616,1999557174118391,1999949097691099,1999768207813684,
  1999627308749005,1999766846489520,1999667117654676,1999875115980713,2000027751891513,
  2000178639034434,1999812275221983,1999889805989305,2000212334020251,1999533601279945,
  2000494461634535,1999241286386271,2000731982526164,1999124484431305,2001466909852161,
  1998450924252117,2001849251481214,1997808107500767,2002458411316029,1997815259725174,
  2001455503163798,1999567909739068,1998903075308616,2001752934472651,1997214345448726,
  2002541372675743,1998541083150222,2000605439235542,2001888967729261,1996782941514096,
  2002462280431709,2000173746099758,1997602555853669,2001956032764192,1998886924738463,
  1999583394907090,2001495029303515,1998417303682019,2000998212978734,2000658672222980,
  1997618727121271,2002135465797039,2000212190315821,1995539981534320,2003530153105453,
  2003676553687752,1992511780274495]
private def wc_rkmTrajPack_m2_r128_s5_v2_p1 : List ℕ := [1999125030730801,2008946742791685,
  1995392929916748,1989269252455989,2008270879866120,2010623534118260,1988941584098934,
  1990079220389844,2012943901678509,2009508579777007,1985759724645797,1989511414735248,
  2013997590494176,2012020319476952,1987215240998830,1985710366317182,2010614618031002,
  2017774332905025,1993633989899051,1977543602255501,1996544304924610,2022772421171254,
  2016699967221880,1985093105028056,1970406801196560,1992834759585597,2024965949637127,
  2026919443387748,1994034927577381,1961942859016857,1967886656915376,2012372212828784,
  2058270612662876,2064246689570086,2020306228921230,1956931509127253,1924115138870853,
  1958711326491285,2063035994508153,2205886145324456,2341087142013586,2429822207115810,
  2454656876742360,2420956002048571,2348858044437668,2262283934451231,2180464346909456,
  2114295843885307,2066886998849309,2036250431630468,2018213039625886,2008482217211494,
  2003657872440036,2001457761383749,2000535378332696,2000180531613724,2000055634458864,
  2000015577238977,2000003933196432,2000000886822689,2000000176154951,2000000030224199,
  2000000004340705,2000000000492443]
private def wc_rkmTrajPack_m2_r128_s5_v2_p2 : List ℕ := [2000000000038257]
private def wc_rkmTrajPack_m2_r128_s5_v2 : List ℕ := pCat wc_rkmTrajPack_m2_r128_s5_v2_p0 (pCat
  wc_rkmTrajPack_m2_r128_s5_v2_p1 wc_rkmTrajPack_m2_r128_s5_v2_p2)
private def wc_rkmTrajPack_m64_r58_s0_hb : List ℕ := [214527454385965,299583702563870,
  362246177339608,412886083173870,455571578803895,492413570822631,524679994049150,553205723232081,
  578576483657720,601222767664295,621472423758908,639582217837392,655757829178183,670167083259335,
  682949027943384,694220347519032,704080011386286,712612716606368,719891484699692,725979651631684,
  730932413371445,734798039784982,737618836646201,739431913129823,740269796586317,740160925375112,
  739130042566873,737198507448121,734384537320963,730703388639715,726167483747067,720786487130252,
  714567333028261,707514204227520,699628459837648,690908507583971,681349613504350,670943638656887,
  659678688206806,647538652599478,634502612752637,620544070264532,605629947896807,589719282425517,
  572761497041218,554694086503792,535439462423248,514900565132582,492954608753215,469443900161819,
  444161877951790,416830944266486,387065313279196,354304290533786,317680895342743,275727427356740,
  225570639958181,159774353500146]
private def wc_rkmTrajPack_m64_r58_s0_v0 : List ℕ := [3000000000000000]
private def wc_rkmTrajPack_m64_r58_s0_v1 : List ℕ := [2000014076084422,2000077528984295,
  2000297550750676,2000918683295993,2002419779106615,2005614658913857,2011710851715960,
  2022263860239900,2038971371030240,2063292072525015,2095942425100405,2136398674744543,
  2182575958909814,2230841408261369,2276435670863463,2314250040067921,2339781245790568,
  2350013839767886,2343992134055492,2322936520201536,2289896683986933,2249064961915579,
  2204952212698273,2161635962881462,2122235129176711,2088676861036237,2061733911499550,
  2041251640022861,2026462497528934,2016297672701900,2009636601159248,2005470030286074,
  2002980248955071,2001558139740734,2000781463728932,2000375819211943,2000173218908210,
  2000076470228717,2000032311498877,2000013056405137,2000005040426463,2000001856936144,
  2000000651996793,2000000217849888,2000000069147040,2000000020807115,2000000005921617,
  2000000001589435,2000000000401026,2000000000094728,2000000000020844,2000000000004244,
  2000000000000791,2000000000000131,2000000000000018,2000000000000001,2000000000000000,
  2000000000000000,2000000000000000]
private abbrev dP_0 : Prop := atF [ bNLE (bEvalLo12W 32 256 64 [1,2,4,4,4,4,4,4]
  [33135635,42589241,14610594,16827373,5725160,1826377,864171,357256] [12,25,14,16,6,2,1,1]
  rkmMasks_m32_r64 [none, some (25, 65, wc_rkmTraj_m32_r64_s1_hb, wc_rkmTraj_m32_r64_s1_v0,
  wc_rkmTraj_m32_r64_s1_v1)]) rkmRow_m32_r64, bNLE (bEvalLo12W 1024 8 6 [1,1] [16474801,7060629]
  [6,3] rkmMasks_m1024_r6 []) rkmRow_m1024_r6, bNLE (bEvalLo12W 64 128 8 [1,1,1,1,1,1,1,1]
  [46054954,46202567,2156919,1521157,678778,370940,484890,319783] [5,5,1,1,1,1,1,1]
  rkmMasksPack_m64_r8 []) rkmRowPack_m64_r8] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := atF [ bNLE (bEvalLo12W 64 128 58 [2,2,2,2,2,2,2,2]
  [26142866,16364866,16412230,5284598,5612792,5235214,2946706,1911300] [21,13,14,5,5,5,3,2]
  rkmMasksPack_m64_r58 [some (21, 59, wc_rkmTrajPack_m64_r58_s0_hb, wc_rkmTrajPack_m64_r58_s0_v0,
  wc_rkmTrajPack_m64_r58_s0_v1)]) rkmRowPack_m64_r58, bNLE (bEvalLo12W 2 4096 20
  [1,2,4,8,15,15,15] [36292134,30986865,43289255,36157307,70278282,11522892,4496953]
  [1,1,3,4,10,2,1] rkmMasks_m2_r20 []) rkmRow_m2_r20] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := atF [ bNLE (bEvalLo12W 64 128 46 [1,1,1,1,1,1,1,1]
  [35298943,29854345,23746667,11953995,11361380,6484712,7347300,5667126] [15,13,10,5,5,3,4,3]
  rkmMasksPack_m64_r46 []) rkmRowPack_m64_r46, bNLE (bEvalLo12W 4 2048 20 [1,2,4,8,9,9,9]
  [39323058,34662322,45668184,22524151,68702187,2765292,2268666] [2,2,4,4,11,1,1]
  rkmMasksPack_m4_r20 []) rkmRowPack_m4_r20] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := atF [ bSlideChk 21 129 wc_rkmTraj_m32_r128_s2_hb
  wc_rkmTraj_m32_r128_s2_v0 wc_rkmTraj_m32_r128_s2_v1, bNLE (bEvalLo12W 8 1024 17 [1,2,3,3,3,3]
  [62403531,53902972,70748002,27728118,20905270,8411781] [4,6,9,4,4,2] rkmMasks_m8_r17 [])
  rkmRow_m8_r17] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := atF [ bNLE (bEvalLo12W 2 4096 128 [4,8,16,32,64,112,112,112]
  [19383898,13076285,15672316,17171273,20550216,11085372,11776375,4358179] [3,4,8,15,31,25,27,10]
  rkmMasksPack_m2_r128 [none, none, none, none, some (31, 129, wc_rkmTrajPack_m2_r128_s4_hb,
  wc_rkmTrajPack_m2_r128_s4_v0, wc_rkmTrajPack_m2_r128_s4_v2), some (25, 129,
  wc_rkmTrajPack_m2_r128_s5_hb, wc_rkmTrajPack_m2_r128_s5_v0, wc_rkmTrajPack_m2_r128_s5_v2), some
  (27, 129, wc_rkmTrajPack_m2_r128_s6_hb, wc_rkmTrajPack_m2_r128_s6_v0,
  wc_rkmTrajPack_m2_r128_s6_v2)]) rkmRowPack_m2_r128, bNLE (bEvalLo12W 32 256 19 [1,1,1,1,1,1,1,1]
  [46536469,32779480,33209109,18576074,16119692,11387428,5238684,4911056] [7,5,5,3,3,2,1,1]
  rkmMasksPack_m32_r19 []) rkmRowPack_m32_r19] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := atF [ bSlideChk 20 129 wc_rkmTraj_m32_r128_s2_hb
  wc_rkmTraj_m32_r128_s2_v1 wc_rkmTraj_m32_r128_s2_v2, bNLE (bEvalLo12W 8 1024 21 [1,4,4,4]
  [77237274,104723725,24528771,6873850] [5,16,5,2] rkmMasks_m8_r21 []) rkmRow_m8_r21, bNLE
  (bEvalLo12W 32 256 7 [1,1,1,1,1,1,1,1]
  [22011883,52418319,13574115,23984656,9856063,6904692,7983613,4027424] [2,4,1,2,1,1,1,1]
  rkmMasksPack_m32_r7 []) rkmRowPack_m32_r7] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := atF [ bNLE (bEvalLo12W 64 128 44 [1,1,1] [120412500,4412625,1467197]
  [51,2,1] rkmMasks_m64_r44 []) rkmRow_m64_r44, bNLE (bEvalLo12W 32 256 21 [1,1,1,1,1,1,1,1]
  [68757365,35524846,18995972,18732748,11053617,11307539,5847462,5258032] [10,6,3,3,2,2,1,1]
  rkmMasksPack_m32_r21 []) rkmRowPack_m32_r21, bNLE (bEvalLo12W 4 2048 6 [1,2,2,2]
  [135409879,158316321,54966802,21207387] [3,5,3,2] rkmMasks_m4_r6 []) rkmRow_m4_r6] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := atF [ bNLE (bEvalLo12W 32 256 128 [1,2,4,7,7,7,7,7]
  [23014539,21380602,25002716,12694908,12593502,2961393,1326201,767356] [12,21,41,31,31,8,4,2]
  rkmMasks_m32_r128 [none, some (21, 65, wc_rkmTraj_m32_r128_s1_hb, wc_rkmTraj_m32_r128_s1_v0,
  wc_rkmTraj_m32_r128_s1_v1), some (41, 129, wc_rkmTraj_m32_r128_s2_hb, wc_rkmTraj_m32_r128_s2_v0,
  wc_rkmTraj_m32_r128_s2_v2), some (31, 129, wc_rkmTraj_m32_r128_s3_hb, wc_rkmTraj_m32_r128_s3_v0,
  wc_rkmTraj_m32_r128_s3_v2), some (31, 129, wc_rkmTraj_m32_r128_s4_hb, wc_rkmTraj_m32_r128_s4_v0,
  wc_rkmTraj_m32_r128_s4_v2)]) rkmRow_m32_r128, bNLE (bEvalLo12W 1024 8 21 [1] [24370369] [28]
  rkmMasks_m1024_r21 []) rkmRow_m1024_r21, bNLE (bEvalLo12W 32 256 15 [1,1,1,1,1,1,1,1]
  [55689378,15160999,37589301,16882911,14258608,9839340,4433898,4053657] [7,2,5,2,2,2,1,1]
  rkmMasksPack_m32_r15 []) rkmRowPack_m32_r15] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := atF [ bNLE (bEvalLo12W 64 128 41 [1,1,1,1,1,1,1,1]
  [32379501,25903570,26030523,12725431,10292332,5749658,6507920,5003226] [13,10,10,5,4,3,3,2]
  rkmMasksPack_m64_r41 []) rkmRowPack_m64_r41, bNLE (bEvalLo12W 64 128 22 [1,1]
  [103415168,3950321] [27,2] rkmMasks_m64_r22 []) rkmRow_m64_r22, bNLE (bEvalLo12W 1024 8 19 [1]
  [24327295] [22] rkmMasks_m1024_r19 []) rkmRow_m1024_r19] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m32_r128_s3_hb
  wc_rkmTraj_m32_r128_s3_v0 wc_rkmTraj_m32_r128_s3_v1, bNLE (bEvalLo12W 512 16 25 [1,1,1]
  [33393723,1281832,97586] [28,2,2] rkmMasks_m512_r25 []) rkmRow_m512_r25, bNLE (bEvalLo12W 4 2048
  12 [1,2,4,5,5,5,5,5] [82998459,59325628,60597053,37725105,21505840,17508324,5016457,2600393]
  [2,3,4,3,2,2,1,1] rkmMasksPack_m4_r12 []) rkmRowPack_m4_r12, bNLE (bEvalLo12W 8 1024 7 [1,2]
  [163965750,95899128] [6,5] rkmMasks_m8_r7 []) rkmRow_m8_r7] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := atF [ bSlideChk 16 129 wc_rkmTraj_m32_r128_s4_hb
  wc_rkmTraj_m32_r128_s4_v0 wc_rkmTraj_m32_r128_s4_v1, bNLE (bEvalLo12W 16 512 27 [1,3,3,3]
  [79422212,78222542,11650122,4323700] [9,18,3,1] rkmMasksPack_m16_r27 []) rkmRowPack_m16_r27,
  bNLE (bEvalLo12W 4 2048 16 [1,2,4,7,7,7,7,7]
  [65280649,47893713,58369479,35110346,32429153,12012896,4003892,3711493] [2,3,5,4,4,2,1,1]
  rkmMasksPack_m4_r16 []) rkmRowPack_m4_r16] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := atF [ bSlideChk 16 129 wc_rkmTrajPack_m2_r128_s4_hb
  wc_rkmTrajPack_m2_r128_s4_v0 wc_rkmTrajPack_m2_r128_s4_v1, bNLE (bEvalLo12W 32 256 22 [1,1,1,1]
  [125078580,28588523,15928547,9735689] [20,6,4,3] rkmMasks_m32_r22 []) rkmRow_m32_r22, bNLE
  (bEvalLo12W 32 256 15 [1,1,1] [131786955,17984688,8143106] [16,3,2] rkmMasks_m32_r15 [])
  rkmRow_m32_r15] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := atF [ bSlideChk 15 129 wc_rkmTraj_m32_r128_s3_hb
  wc_rkmTraj_m32_r128_s3_v1 wc_rkmTraj_m32_r128_s3_v2, bNLE (bEvalLo12W 32 256 25 [1,1,1,1]
  [134618255,18082668,27749065,12934564] [26,4,6,4] rkmMasks_m32_r25 []) rkmRow_m32_r25, bNLE
  (bEvalLo12W 64 128 3 [1,1] [62136419,28175024] [3,2] rkmMasks_m64_r3 []) rkmRow_m64_r3, bNLE
  (bEvalLo12W 64 128 5 [1,1,1,1,1,1,1,1]
  [23859108,26226284,11838164,12612846,8459352,5015260,3260752,3302462] [2,2,1,1,1,1,1,1]
  rkmMasksPack_m64_r5 []) rkmRowPack_m64_r5] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := atF [ bSlideChk 15 129 wc_rkmTraj_m32_r128_s4_hb
  wc_rkmTraj_m32_r128_s4_v1 wc_rkmTraj_m32_r128_s4_v2, bNLE (bEvalLo12W 32 256 28 [1,2,2,2]
  [95445712,38098428,8110050,3994524] [17,11,3,2] rkmMasksPack_m32_r28 []) rkmRowPack_m32_r28,
  bNLE (bEvalLo12W 8 1024 30 [1,1,2,4,4,4,4,4]
  [27036205,61257152,26461758,1286,59326,1960280,395323,1211961] [2,4,3,1,1,1,1,1]
  rkmMasksPack_m8_r30 []) rkmRowPack_m8_r30] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := atF [ bSlideChk 15 129 wc_rkmTrajPack_m2_r128_s4_hb
  wc_rkmTrajPack_m2_r128_s4_v1 wc_rkmTrajPack_m2_r128_s4_v2, bNLE (bEvalLo12W 256 32 27 [1,1]
  [48897959,1034066] [31,2] rkmMasks_m256_r27 []) rkmRow_m256_r27, bNLE (bEvalLo12W 128 64 13
  [1,1,1,1] [66831663,1807081,604431,514977] [15,2,2,2] rkmMasks_m128_r13 []) rkmRow_m128_r13] =
  true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := atF [ bSlideChk 14 129 wc_rkmTrajPack_m2_r128_s6_hb
  wc_rkmTrajPack_m2_r128_s6_v0 wc_rkmTrajPack_m2_r128_s6_v1, bNLE (bEvalLo12W 256 32 30 [1]
  [50135297] [35] rkmMasks_m256_r30 []) rkmRow_m256_r30, bNLE (bEvalLo12W 2 4096 17 [1,3,6,12]
  [39063885,50442447,52710533,82785312] [2,3,5,10] rkmMasks_m2_r17 []) rkmRow_m2_r17] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := atF [ bSlideChk 13 129 wc_rkmTrajPack_m2_r128_s6_hb
  wc_rkmTrajPack_m2_r128_s6_v1 wc_rkmTrajPack_m2_r128_s6_v2, bSlideChk 21 59
  wc_rkmTrajPack_m64_r58_s0_hb wc_rkmTrajPack_m64_r58_s0_v0 wc_rkmTrajPack_m64_r58_s0_v1, bNLE
  (bEvalLo12W 64 128 11 [1,1,1] [93842513,4002614,2212656] [13,2,2] rkmMasks_m64_r11 [])
  rkmRow_m64_r11, bNLE (bEvalLo12W 8 1024 3 [1,1,1,1,1]
  [162953765,63895887,27308790,9499359,6601059] [3,1,1,1,1] rkmMasksPack_m8_r3 [])
  rkmRowPack_m8_r3] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := atF [ bSlideChk 13 129 wc_rkmTrajPack_m2_r128_s5_hb
  wc_rkmTrajPack_m2_r128_s5_v0 wc_rkmTrajPack_m2_r128_s5_v1, bNLE (bEvalLo12W 8 1024 32
  [1,2,4,7,7,7,7,7] [53408817,29210577,48961952,25589576,23965257,8625227,2559420,1331363]
  [4,4,10,8,7,3,1,1] rkmMasksPack_m8_r32 []) rkmRowPack_m8_r32, bNLE (bEvalLo12W 32 256 17
  [1,1,1,1,1,1] [34121268,52383873,31543984,16685745,19243705,9135893] [5,7,4,2,3,2]
  rkmMasksPack_m32_r17 []) rkmRowPack_m32_r17] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := atF [ bNLE (bEvalLo12W 16 512 40 [1,2,4,5,5,5]
  [48350083,31967207,27305988,32076340,7172554,2409027] [7,8,11,14,4,2] rkmMasksPack_m16_r40 [])
  rkmRowPack_m16_r40, bNLE (bEvalLo12W 128 64 30 [1,1,1,1] [66783945,4916251,1377368,383588]
  [32,4,2,2] rkmMasks_m128_r30 []) rkmRow_m128_r30, bNLE (bEvalLo12W 64 128 12 [1,1,1]
  [94222734,4143839,2374998] [14,2,2] rkmMasks_m64_r12 []) rkmRow_m64_r12, bNLE (bEvalLo12W 64 128
  7 [1,1,1] [92020818,3663412,1205181] [8,1,1] rkmMasksPack_m64_r7 []) rkmRowPack_m64_r7] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := atF [ bNLE (bEvalLo12W 32 256 35 [1,2,2,2,2]
  [68438423,47997055,12866758,7372170,4169600] [16,18,6,4,3] rkmMasks_m32_r35 []) rkmRow_m32_r35,
  bNLE (bEvalLo12W 32 256 32 [1,1,1,1,2,2,2,2]
  [13470292,27642816,17528409,26381849,18333450,20694850,15596629,5599028] [3,6,4,6,6,7,5,2]
  rkmMasksPack_m32_r32 []) rkmRowPack_m32_r32, bNLE (bEvalLo12W 2 4096 15 [1,3,6,12]
  [43914293,55840362,59979771,70482964] [1,2,4,7] rkmMasksPack_m2_r15 []) rkmRowPack_m2_r15, bNLE
  (bEvalLo12W 512 16 9 [1,1] [25401646,8467211] [10,4] rkmMasks_m512_r9 []) rkmRow_m512_r9] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := atF [ bSlideChk 25 65 wc_rkmTraj_m32_r64_s1_hb
  wc_rkmTraj_m32_r64_s1_v0 wc_rkmTraj_m32_r64_s1_v1, bSlideChk 21 65 wc_rkmTraj_m32_r128_s1_hb
  wc_rkmTraj_m32_r128_s1_v0 wc_rkmTraj_m32_r128_s1_v1, bNLE (bEvalLo12W 32 256 3 [1,1,1,1]
  [86394154,36789145,2456108,2975855] [3,2,1,1] rkmMasks_m32_r3 []) rkmRow_m32_r3, bNLE
  (bEvalLo12W 32 256 9 [1,1,1] [124350136,15061557,5533486] [9,2,1] rkmMasksPack_m32_r9 [])
  rkmRowPack_m32_r9] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := atF [ bSlideChk 12 129 wc_rkmTrajPack_m2_r128_s5_hb
  wc_rkmTrajPack_m2_r128_s5_v1 wc_rkmTrajPack_m2_r128_s5_v2, bNLE (bEvalLo12W 512 16 32
  [1,1,1,1,1,1,1,1] [16353637,16330495,743524,722004,254567,225787,175344,176358]
  [18,18,1,1,1,1,1,1] rkmMasks_m512_r32 []) rkmRow_m512_r32, bNLE (bEvalLo12W 128 64 9 [1,1,1,1]
  [66268505,1665366,351218,256054] [11,2,2,2] rkmMasks_m128_r9 []) rkmRow_m128_r9, bNLE
  (bEvalLo12W 16 512 7 [1,1,1,1] [112514407,55577418,31655941,12848169] [6,4,3,2] rkmMasks_m16_r7
  []) rkmRow_m16_r7] = true
private theorem bk_21 : dP_21 := by decide +kernel
private theorem ws_rkmTraj_m32_r128_s2 : WalkOk (some (41, 129, wc_rkmTraj_m32_r128_s2_hb,
    wc_rkmTraj_m32_r128_s2_v0, wc_rkmTraj_m32_r128_s2_v2)) := mIter_split rfl
    (bSlideChk_sound bk_3) (bSlideChk_sound bk_5)
private theorem ws_rkmTraj_m32_r128_s3 : WalkOk (some (31, 129, wc_rkmTraj_m32_r128_s3_hb,
    wc_rkmTraj_m32_r128_s3_v0, wc_rkmTraj_m32_r128_s3_v2)) := mIter_split rfl
    (bSlideChk_sound bk_9) (bSlideChk_sound bk_12)
private theorem ws_rkmTraj_m32_r128_s4 : WalkOk (some (31, 129, wc_rkmTraj_m32_r128_s4_hb,
    wc_rkmTraj_m32_r128_s4_v0, wc_rkmTraj_m32_r128_s4_v2)) := mIter_split rfl
    (bSlideChk_sound bk_10) (bSlideChk_sound bk_13)
private theorem ws_rkmTrajPack_m2_r128_s4 : WalkOk (some (31, 129, wc_rkmTrajPack_m2_r128_s4_hb,
    wc_rkmTrajPack_m2_r128_s4_v0, wc_rkmTrajPack_m2_r128_s4_v2)) := mIter_split rfl
    (bSlideChk_sound bk_11) (bSlideChk_sound bk_14)
private theorem ws_rkmTrajPack_m2_r128_s5 : WalkOk (some (25, 129, wc_rkmTrajPack_m2_r128_s5_hb,
    wc_rkmTrajPack_m2_r128_s5_v0, wc_rkmTrajPack_m2_r128_s5_v2)) := mIter_split rfl
    (bSlideChk_sound bk_17) (bSlideChk_sound bk_21)
private theorem ws_rkmTrajPack_m2_r128_s6 : WalkOk (some (27, 129, wc_rkmTrajPack_m2_r128_s6_hb,
    wc_rkmTrajPack_m2_r128_s6_v0, wc_rkmTrajPack_m2_r128_s6_v2)) := mIter_split rfl
    (bSlideChk_sound bk_15) (bSlideChk_sound bk_16)
/-- Kernel trajectory certificate `(m = 32, r = 128)`. -/
theorem rkmTraj_m32_r128 : rkmEvalT16Lo12 32 256 128 [1, 2, 4, 7, 7, 7, 7, 7] [23014539, 21380602,
  25002716, 12694908, 12593502, 2961393, 1326201, 767356] [12, 21, 41, 31, 31, 8, 4, 2]
  rkmMasks_m32_r128 = rkmRow_m32_r128 :=
    bhW_eq bk_7 (wSkip (wCons (bSlideChk_sound (tl1 bk_20)) (wCons ws_rkmTraj_m32_r128_s2 (wCons
      ws_rkmTraj_m32_r128_s3 (wCons ws_rkmTraj_m32_r128_s4 wNil)))))
/-- Kernel trajectory certificate `(m = 1024, r = 19)`. -/
theorem rkmTraj_m1024_r19 : rkmEvalT16Lo12 1024 8 19 [1] [24327295] [22] rkmMasks_m1024_r19 =
  rkmRow_m1024_r19 := bh0_eq (tl2 bk_8)
/-- Kernel trajectory certificate `(m = 64, r = 3)`. -/
theorem rkmTraj_m64_r3 : rkmEvalT16Lo12 64 128 3 [1, 1] [62136419, 28175024] [3, 2] rkmMasks_m64_r3
  = rkmRow_m64_r3 := bh0_eq (tl2 bk_12)
/-- Kernel trajectory certificate `(m = 32, r = 64)`. -/
theorem rkmTraj_m32_r64 : rkmEvalT16Lo12 32 256 64 [1, 2, 4, 4, 4, 4, 4, 4] [33135635, 42589241,
  14610594, 16827373, 5725160, 1826377, 864171, 357256] [12, 25, 14, 16, 6, 2, 1, 1]
  rkmMasks_m32_r64 = rkmRow_m32_r64 := bhW_eq bk_0 (wSkip (wCons (bSlideChk_sound bk_20) wNil))
/-- Kernel trajectory certificate `(m = 32, r = 3)`. -/
theorem rkmTraj_m32_r3 : rkmEvalT16Lo12 32 256 3 [1, 1, 1, 1] [86394154, 36789145, 2456108, 2975855]
  [3, 2, 1, 1] rkmMasks_m32_r3 = rkmRow_m32_r3 := bh0_eq (tl2 bk_20)
/-- Kernel trajectory certificate `(m = 64, r = 44)`. -/
theorem rkmTraj_m64_r44 : rkmEvalT16Lo12 64 128 44 [1, 1, 1] [120412500, 4412625, 1467197] [51, 2,
  1] rkmMasks_m64_r44 = rkmRow_m64_r44 := bh0_eq bk_6
/-- Kernel trajectory certificate `(m = 1024, r = 6)`. -/
theorem rkmTraj_m1024_r6 : rkmEvalT16Lo12 1024 8 6 [1, 1] [16474801, 7060629] [6, 3]
  rkmMasks_m1024_r6 = rkmRow_m1024_r6 := bh0_eq (tl1 bk_0)
/-- Kernel trajectory certificate `(m = 32, r = 35)`. -/
theorem rkmTraj_m32_r35 : rkmEvalT16Lo12 32 256 35 [1, 2, 2, 2, 2] [68438423, 47997055, 12866758,
  7372170, 4169600] [16, 18, 6, 4, 3] rkmMasks_m32_r35 = rkmRow_m32_r35 := bh0_eq bk_19
/-- Kernel trajectory certificate `(m = 4, r = 6)`. -/
theorem rkmTraj_m4_r6 : rkmEvalT16Lo12 4 2048 6 [1, 2, 2, 2] [135409879, 158316321, 54966802,
  21207387] [3, 5, 3, 2] rkmMasks_m4_r6 = rkmRow_m4_r6 := bh0_eq (tl2 bk_6)
/-- Kernel trajectory certificate `(m = 512, r = 32)`. -/
theorem rkmTraj_m512_r32 : rkmEvalT16Lo12 512 16 32 [1, 1, 1, 1, 1, 1, 1, 1] [16353637, 16330495,
  743524, 722004, 254567, 225787, 175344, 176358] [18, 18, 1, 1, 1, 1, 1, 1] rkmMasks_m512_r32 =
  rkmRow_m512_r32 := bh0_eq (tl1 bk_21)
/-- Kernel trajectory certificate `(m = 8, r = 7)`. -/
theorem rkmTraj_m8_r7 : rkmEvalT16Lo12 8 1024 7 [1, 2] [163965750, 95899128] [6, 5] rkmMasks_m8_r7 =
  rkmRow_m8_r7 := bh0_eq (tl1 (tl2 bk_9))
/-- Kernel trajectory certificate `(m = 128, r = 30)`. -/
theorem rkmTraj_m128_r30 : rkmEvalT16Lo12 128 64 30 [1, 1, 1, 1] [66783945, 4916251, 1377368,
  383588] [32, 4, 2, 2] rkmMasks_m128_r30 = rkmRow_m128_r30 := bh0_eq (tl1 bk_18)
/-- Kernel trajectory certificate `(m = 16, r = 7)`. -/
theorem rkmTraj_m16_r7 : rkmEvalT16Lo12 16 512 7 [1, 1, 1, 1] [112514407, 55577418, 31655941,
  12848169] [6, 4, 3, 2] rkmMasks_m16_r7 = rkmRow_m16_r7 := bh0_eq (tl1 (tl2 bk_21))
/-- Kernel trajectory certificate `(m = 256, r = 30)`. -/
theorem rkmTraj_m256_r30 : rkmEvalT16Lo12 256 32 30 [1] [50135297] [35] rkmMasks_m256_r30 =
  rkmRow_m256_r30 := bh0_eq (tl1 bk_15)
/-- Kernel trajectory certificate `(m = 512, r = 9)`. -/
theorem rkmTraj_m512_r9 : rkmEvalT16Lo12 512 16 9 [1, 1] [25401646, 8467211] [10, 4]
  rkmMasks_m512_r9 = rkmRow_m512_r9 := bh0_eq (tl1 (tl2 bk_19))
/-- Kernel trajectory certificate `(m = 32, r = 25)`. -/
theorem rkmTraj_m32_r25 : rkmEvalT16Lo12 32 256 25 [1, 1, 1, 1] [134618255, 18082668, 27749065,
  12934564] [26, 4, 6, 4] rkmMasks_m32_r25 = rkmRow_m32_r25 := bh0_eq (tl1 bk_12)
/-- Kernel trajectory certificate `(m = 128, r = 9)`. -/
theorem rkmTraj_m128_r9 : rkmEvalT16Lo12 128 64 9 [1, 1, 1, 1] [66268505, 1665366, 351218, 256054]
  [11, 2, 2, 2] rkmMasks_m128_r9 = rkmRow_m128_r9 := bh0_eq (tl2 bk_21)
/-- Kernel trajectory certificate `(m = 256, r = 27)`. -/
theorem rkmTraj_m256_r27 : rkmEvalT16Lo12 256 32 27 [1, 1] [48897959, 1034066] [31, 2]
  rkmMasks_m256_r27 = rkmRow_m256_r27 := bh0_eq (tl1 bk_14)
/-- Kernel trajectory certificate `(m = 64, r = 11)`. -/
theorem rkmTraj_m64_r11 : rkmEvalT16Lo12 64 128 11 [1, 1, 1] [93842513, 4002614, 2212656] [13, 2, 2]
  rkmMasks_m64_r11 = rkmRow_m64_r11 := bh0_eq (tl2 bk_16)
/-- Kernel trajectory certificate `(m = 512, r = 25)`. -/
theorem rkmTraj_m512_r25 : rkmEvalT16Lo12 512 16 25 [1, 1, 1] [33393723, 1281832, 97586] [28, 2, 2]
  rkmMasks_m512_r25 = rkmRow_m512_r25 := bh0_eq (tl1 bk_9)
/-- Kernel trajectory certificate `(m = 64, r = 12)`. -/
theorem rkmTraj_m64_r12 : rkmEvalT16Lo12 64 128 12 [1, 1, 1] [94222734, 4143839, 2374998] [14, 2, 2]
  rkmMasks_m64_r12 = rkmRow_m64_r12 := bh0_eq (tl2 bk_18)
/-- Kernel trajectory certificate `(m = 32, r = 22)`. -/
theorem rkmTraj_m32_r22 : rkmEvalT16Lo12 32 256 22 [1, 1, 1, 1] [125078580, 28588523, 15928547,
  9735689] [20, 6, 4, 3] rkmMasks_m32_r22 = rkmRow_m32_r22 := bh0_eq (tl1 bk_11)
/-- Kernel trajectory certificate `(m = 2, r = 17)`. -/
theorem rkmTraj_m2_r17 : rkmEvalT16Lo12 2 4096 17 [1, 3, 6, 12] [39063885, 50442447, 52710533,
  82785312] [2, 3, 5, 10] rkmMasks_m2_r17 = rkmRow_m2_r17 := bh0_eq (tl2 bk_15)
/-- Kernel trajectory certificate `(m = 64, r = 22)`. -/
theorem rkmTraj_m64_r22 : rkmEvalT16Lo12 64 128 22 [1, 1] [103415168, 3950321] [27, 2]
  rkmMasks_m64_r22 = rkmRow_m64_r22 := bh0_eq (tl1 bk_8)
/-- Kernel trajectory certificate `(m = 128, r = 13)`. -/
theorem rkmTraj_m128_r13 : rkmEvalT16Lo12 128 64 13 [1, 1, 1, 1] [66831663, 1807081, 604431, 514977]
  [15, 2, 2, 2] rkmMasks_m128_r13 = rkmRow_m128_r13 := bh0_eq (tl2 bk_14)
/-- Kernel trajectory certificate `(m = 1024, r = 21)`. -/
theorem rkmTraj_m1024_r21 : rkmEvalT16Lo12 1024 8 21 [1] [24370369] [28] rkmMasks_m1024_r21 =
  rkmRow_m1024_r21 := bh0_eq (tl1 bk_7)
/-- Kernel trajectory certificate `(m = 32, r = 15)`. -/
theorem rkmTraj_m32_r15 : rkmEvalT16Lo12 32 256 15 [1, 1, 1] [131786955, 17984688, 8143106] [16, 3,
  2] rkmMasks_m32_r15 = rkmRow_m32_r15 := bh0_eq (tl2 bk_11)
/-- Kernel trajectory certificate `(m = 8, r = 21)`. -/
theorem rkmTraj_m8_r21 : rkmEvalT16Lo12 8 1024 21 [1, 4, 4, 4] [77237274, 104723725, 24528771,
  6873850] [5, 16, 5, 2] rkmMasks_m8_r21 = rkmRow_m8_r21 := bh0_eq (tl1 bk_5)
/-- Kernel trajectory certificate `(m = 2, r = 20)`. -/
theorem rkmTraj_m2_r20 : rkmEvalT16Lo12 2 4096 20 [1, 2, 4, 8, 15, 15, 15] [36292134, 30986865,
  43289255, 36157307, 70278282, 11522892, 4496953] [1, 1, 3, 4, 10, 2, 1] rkmMasks_m2_r20 =
  rkmRow_m2_r20 := bh0_eq (tl1 bk_1)
/-- Kernel trajectory certificate `(m = 8, r = 17)`. -/
theorem rkmTraj_m8_r17 : rkmEvalT16Lo12 8 1024 17 [1, 2, 3, 3, 3, 3] [62403531, 53902972, 70748002,
  27728118, 20905270, 8411781] [4, 6, 9, 4, 4, 2] rkmMasks_m8_r17 = rkmRow_m8_r17 :=
    bh0_eq (tl1 bk_3)
/-- Krotov trajectory `(m = 2, r = 128)`. -/
theorem rkmTrajPack_m2_r128 : rkmEvalT16Lo12 2 4096 128 [4,8,16,32,64,112,112,112]
  [19383898,13076285,15672316,17171273,20550216,11085372,11776375,4358179] [3,4,8,15,31,25,27,10]
  rkmMasksPack_m2_r128 = rkmRowPack_m2_r128 :=
    bhW_eq bk_4 (wSkip (wSkip (wSkip (wSkip (wCons ws_rkmTrajPack_m2_r128_s4 (wCons
      ws_rkmTrajPack_m2_r128_s5 (wCons ws_rkmTrajPack_m2_r128_s6 wNil)))))))
/-- Krotov trajectory `(m = 8, r = 3)`. -/
theorem rkmTrajPack_m8_r3 : rkmEvalT16Lo12 8 1024 3 [1,1,1,1,1]
  [162953765,63895887,27308790,9499359,6601059] [3,1,1,1,1] rkmMasksPack_m8_r3 = rkmRowPack_m8_r3
  := bh0_eq (tl1 (tl2 bk_16))
/-- Krotov trajectory `(m = 64, r = 58)`. -/
theorem rkmTrajPack_m64_r58 : rkmEvalT16Lo12 64 128 58 [2,2,2,2,2,2,2,2]
  [26142866,16364866,16412230,5284598,5612792,5235214,2946706,1911300] [21,13,14,5,5,5,3,2]
  rkmMasksPack_m64_r58 = rkmRowPack_m64_r58 :=
    bhW_eq bk_1 (wCons (bSlideChk_sound (tl1 bk_16)) wNil)
/-- Krotov trajectory `(m = 64, r = 5)`. -/
theorem rkmTrajPack_m64_r5 : rkmEvalT16Lo12 64 128 5 [1,1,1,1,1,1,1,1]
  [23859108,26226284,11838164,12612846,8459352,5015260,3260752,3302462] [2,2,1,1,1,1,1,1]
  rkmMasksPack_m64_r5 = rkmRowPack_m64_r5 := bh0_eq (tl1 (tl2 bk_12))
/-- Krotov trajectory `(m = 64, r = 46)`. -/
theorem rkmTrajPack_m64_r46 : rkmEvalT16Lo12 64 128 46 [1,1,1,1,1,1,1,1]
  [35298943,29854345,23746667,11953995,11361380,6484712,7347300,5667126] [15,13,10,5,5,3,4,3]
  rkmMasksPack_m64_r46 = rkmRowPack_m64_r46 := bh0_eq bk_2
/-- Krotov trajectory `(m = 64, r = 7)`. -/
theorem rkmTrajPack_m64_r7 : rkmEvalT16Lo12 64 128 7 [1,1,1] [92020818,3663412,1205181] [8,1,1]
  rkmMasksPack_m64_r7 = rkmRowPack_m64_r7 := bh0_eq (tl1 (tl2 bk_18))
/-- Krotov trajectory `(m = 64, r = 41)`. -/
theorem rkmTrajPack_m64_r41 : rkmEvalT16Lo12 64 128 41 [1,1,1,1,1,1,1,1]
  [32379501,25903570,26030523,12725431,10292332,5749658,6507920,5003226] [13,10,10,5,4,3,3,2]
  rkmMasksPack_m64_r41 = rkmRowPack_m64_r41 := bh0_eq bk_8
/-- Krotov trajectory `(m = 32, r = 7)`. -/
theorem rkmTrajPack_m32_r7 : rkmEvalT16Lo12 32 256 7 [1,1,1,1,1,1,1,1]
  [22011883,52418319,13574115,23984656,9856063,6904692,7983613,4027424] [2,4,1,2,1,1,1,1]
  rkmMasksPack_m32_r7 = rkmRowPack_m32_r7 := bh0_eq (tl2 bk_5)
/-- Krotov trajectory `(m = 16, r = 40)`. -/
theorem rkmTrajPack_m16_r40 : rkmEvalT16Lo12 16 512 40 [1,2,4,5,5,5]
  [48350083,31967207,27305988,32076340,7172554,2409027] [7,8,11,14,4,2] rkmMasksPack_m16_r40 =
  rkmRowPack_m16_r40 := bh0_eq bk_18
/-- Krotov trajectory `(m = 32, r = 9)`. -/
theorem rkmTrajPack_m32_r9 : rkmEvalT16Lo12 32 256 9 [1,1,1] [124350136,15061557,5533486] [9,2,1]
  rkmMasksPack_m32_r9 = rkmRowPack_m32_r9 := bh0_eq (tl1 (tl2 bk_20))
/-- Krotov trajectory `(m = 32, r = 32)`. -/
theorem rkmTrajPack_m32_r32 : rkmEvalT16Lo12 32 256 32 [1,1,1,1,2,2,2,2]
  [13470292,27642816,17528409,26381849,18333450,20694850,15596629,5599028] [3,6,4,6,6,7,5,2]
  rkmMasksPack_m32_r32 = rkmRowPack_m32_r32 := bh0_eq (tl1 bk_19)
/-- Krotov trajectory `(m = 64, r = 8)`. -/
theorem rkmTrajPack_m64_r8 : rkmEvalT16Lo12 64 128 8 [1,1,1,1,1,1,1,1]
  [46054954,46202567,2156919,1521157,678778,370940,484890,319783] [5,5,1,1,1,1,1,1]
  rkmMasksPack_m64_r8 = rkmRowPack_m64_r8 := bh0_eq (tl2 bk_0)
/-- Krotov trajectory `(m = 8, r = 32)`. -/
theorem rkmTrajPack_m8_r32 : rkmEvalT16Lo12 8 1024 32 [1,2,4,7,7,7,7,7]
  [53408817,29210577,48961952,25589576,23965257,8625227,2559420,1331363] [4,4,10,8,7,3,1,1]
  rkmMasksPack_m8_r32 = rkmRowPack_m8_r32 := bh0_eq (tl1 bk_17)
/-- Krotov trajectory `(m = 2, r = 15)`. -/
theorem rkmTrajPack_m2_r15 : rkmEvalT16Lo12 2 4096 15 [1,3,6,12]
  [43914293,55840362,59979771,70482964] [1,2,4,7] rkmMasksPack_m2_r15 = rkmRowPack_m2_r15 :=
    bh0_eq (tl2 bk_19)
/-- Krotov trajectory `(m = 32, r = 28)`. -/
theorem rkmTrajPack_m32_r28 : rkmEvalT16Lo12 32 256 28 [1,2,2,2] [95445712,38098428,8110050,3994524]
  [17,11,3,2] rkmMasksPack_m32_r28 = rkmRowPack_m32_r28 := bh0_eq (tl1 bk_13)
/-- Krotov trajectory `(m = 4, r = 12)`. -/
theorem rkmTrajPack_m4_r12 : rkmEvalT16Lo12 4 2048 12 [1,2,4,5,5,5,5,5]
  [82998459,59325628,60597053,37725105,21505840,17508324,5016457,2600393] [2,3,4,3,2,2,1,1]
  rkmMasksPack_m4_r12 = rkmRowPack_m4_r12 := bh0_eq (tl2 bk_9)
/-- Krotov trajectory `(m = 16, r = 27)`. -/
theorem rkmTrajPack_m16_r27 : rkmEvalT16Lo12 16 512 27 [1,3,3,3]
  [79422212,78222542,11650122,4323700] [9,18,3,1] rkmMasksPack_m16_r27 = rkmRowPack_m16_r27 :=
    bh0_eq (tl1 bk_10)
/-- Krotov trajectory `(m = 8, r = 30)`. -/
theorem rkmTrajPack_m8_r30 : rkmEvalT16Lo12 8 1024 30 [1,1,2,4,4,4,4,4]
  [27036205,61257152,26461758,1286,59326,1960280,395323,1211961] [2,4,3,1,1,1,1,1]
  rkmMasksPack_m8_r30 = rkmRowPack_m8_r30 := bh0_eq (tl2 bk_13)
/-- Krotov trajectory `(m = 32, r = 21)`. -/
theorem rkmTrajPack_m32_r21 : rkmEvalT16Lo12 32 256 21 [1,1,1,1,1,1,1,1]
  [68757365,35524846,18995972,18732748,11053617,11307539,5847462,5258032] [10,6,3,3,2,2,1,1]
  rkmMasksPack_m32_r21 = rkmRowPack_m32_r21 := bh0_eq (tl1 bk_6)
/-- Krotov trajectory `(m = 4, r = 16)`. -/
theorem rkmTrajPack_m4_r16 : rkmEvalT16Lo12 4 2048 16 [1,2,4,7,7,7,7,7]
  [65280649,47893713,58369479,35110346,32429153,12012896,4003892,3711493] [2,3,5,4,4,2,1,1]
  rkmMasksPack_m4_r16 = rkmRowPack_m4_r16 := bh0_eq (tl2 bk_10)
/-- Krotov trajectory `(m = 32, r = 19)`. -/
theorem rkmTrajPack_m32_r19 : rkmEvalT16Lo12 32 256 19 [1,1,1,1,1,1,1,1]
  [46536469,32779480,33209109,18576074,16119692,11387428,5238684,4911056] [7,5,5,3,3,2,1,1]
  rkmMasksPack_m32_r19 = rkmRowPack_m32_r19 := bh0_eq (tl1 bk_4)
/-- Krotov trajectory `(m = 32, r = 15)`. -/
theorem rkmTrajPack_m32_r15 : rkmEvalT16Lo12 32 256 15 [1,1,1,1,1,1,1,1]
  [55689378,15160999,37589301,16882911,14258608,9839340,4433898,4053657] [7,2,5,2,2,2,1,1]
  rkmMasksPack_m32_r15 = rkmRowPack_m32_r15 := bh0_eq (tl2 bk_7)
/-- Krotov trajectory `(m = 4, r = 20)`. -/
theorem rkmTrajPack_m4_r20 : rkmEvalT16Lo12 4 2048 20 [1,2,4,8,9,9,9]
  [39323058,34662322,45668184,22524151,68702187,2765292,2268666] [2,2,4,4,11,1,1]
  rkmMasksPack_m4_r20 = rkmRowPack_m4_r20 := bh0_eq (tl1 bk_2)
/-- Krotov trajectory `(m = 32, r = 17)`. -/
theorem rkmTrajPack_m32_r17 : rkmEvalT16Lo12 32 256 17 [1,1,1,1,1,1]
  [34121268,52383873,31543984,16685745,19243705,9135893] [5,7,4,2,3,2] rkmMasksPack_m32_r17 =
  rkmRowPack_m32_r17 := bh0_eq (tl2 bk_17)
end
end QuantumComputation.Specs.DickeSol
