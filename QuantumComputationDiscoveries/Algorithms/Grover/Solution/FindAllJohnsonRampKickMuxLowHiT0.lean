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

/-
# Low-`m` High-`r` Krotov Trajectory Part `0` (`FindAllJohnsonRampKickMuxLowHiT0`)

Certifies sawtooth `rkmEvalT16Lo12` walks for `(m, r) ∈ {(2, 256), (4, 192), (4, 256), (4, 384)}`
together with `(2, 512)` segments `0, 1, 2, 3, 7`.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Sign-kick mask segment `2` for `(m = 2, r = 256)`. -/
def rkmMkPack_m2_r256_s2 : List Bool := [
  false, false, true, true, true, true, true, true, true, true, false, false, false, true, true,
  true, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true
  ]
/-- Part `0` of `rkmMkPack_m2_r256_s3`. -/
def rkmMkPack_m2_r256_s3_p0 : List Bool := [
  true, false, true, true, false, false, false, false, false, true, true, false, false, false,
  false, false, true, true, false, false, true, true, true, false, true, true, true, false, false,
  false, true, false, true, true, false, false, false, false, true, false, false, false, true,
  false, false, true, true, false, false, false, false, true, false, false, false, true, true,
  true, true, true, false, true, true, true, true, true, false, false, true, true, true, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false
  ]
/-- Part `1` of `rkmMkPack_m2_r256_s3`. -/
def rkmMkPack_m2_r256_s3_p1 : List Bool := [
  false, false, false, false, false, false, false, false, false, true, true, true, false, false,
  false, false, false, true, false, false, false, false, false, true
  ]
/-- Sign-kick mask segment `3` for `(m = 2, r = 256)`. -/
def rkmMkPack_m2_r256_s3 : List Bool :=
  rkmMkPack_m2_r256_s3_p0 ++ rkmMkPack_m2_r256_s3_p1
/-- Part `0` of `rkmMkPack_m2_r256_s4`. -/
def rkmMkPack_m2_r256_s4_p0 : List Bool := [
  true, true, false, false, false, true, false, true, true, false, false, true, false, false,
  false, true, false, false, false, true, false, true, false, false, true, true, false, false,
  false, true, false, true, true, true, true, false, false, true, true, false, false, true, false,
  false, false, false, true, false, false, true, true, true, false, true, false, true, true, true,
  false, false, false, true, true, true, false, true, true, true, false, true, true, true, true,
  true, false, false, false, true, true, false, false, false, false, false, false, true, false,
  false, true, true, false, false, true, true, true, false
  ]
/-- Part `1` of `rkmMkPack_m2_r256_s4`. -/
def rkmMkPack_m2_r256_s4_p1 : List Bool := [
  false, true, true, true, false, false, true, true, true, false, false, false, true, true, false,
  false, false, true, true, true, false, false, false, true, true, true, false, false, false,
  false, true, true, true, false, false, false, true, true, true, true, false, false, false, false,
  true, true, true, true, true, false, false, false, false, true, true, true, true, true, true,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, true, true, true, true, false
  ]
/-- Part `2` of `rkmMkPack_m2_r256_s4`. -/
def rkmMkPack_m2_r256_s4_p2 : List Bool := [
  false, false, false, true, true, false, false, false, true, true, true, true
  ]
/-- Sign-kick mask segment `4` for `(m = 2, r = 256)`. -/
def rkmMkPack_m2_r256_s4 : List Bool :=
  rkmMkPack_m2_r256_s4_p0 ++ (rkmMkPack_m2_r256_s4_p1 ++ rkmMkPack_m2_r256_s4_p2)
/-- Part `0` of `rkmMkPack_m2_r256_s5`. -/
def rkmMkPack_m2_r256_s5_p0 : List Bool := [
  true, true, false, true, false, false, true, false, true, false, false, true, false, true, false,
  false, true, false, true, false, true, false, false, false, false, false, true, true, true,
  false, true, false, true, false, true, true, false, false, false, true, true, false, false,
  false, false, true, false, false, true, true, true, false, true, false, true, true, false, false,
  true, false, true, false, false, true, true, true, false, false, false, true, false, false,
  false, true, false, false, false, false, true, false, true, false, false, true, false, true,
  false, false, false, false, true, false, true, false, false, true
  ]
/-- Part `1` of `rkmMkPack_m2_r256_s5`. -/
def rkmMkPack_m2_r256_s5_p1 : List Bool := [
  false, true, false, false, true, false, true, true, false, true, false, false, false, false,
  true, true, false, false, false, true, false, true, false, false, false, false, false, false,
  true, true, false, false, false, true, true, false, false, false, true, false, true, false, true,
  true, true, false, false, true, false, false, false, false, true, false, true, false, false,
  false, false, false, false, false, false, false, true, false, false, false, false, false, false,
  false, false, false, true, false, false, false, false, false, false, false, false, false, true,
  true, true, false, false, true, true, false, false, false, true, true
  ]
/-- Part `2` of `rkmMkPack_m2_r256_s5`. -/
def rkmMkPack_m2_r256_s5_p2 : List Bool := [
  false, false, false, true, true, false, false, false, true, true, true, false, false, true, true,
  true, false, false, false, false, true, true, true, false, false, false, false, true, true, true,
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  false, true, true
  ]
/-- Sign-kick mask segment `5` for `(m = 2, r = 256)`. -/
def rkmMkPack_m2_r256_s5 : List Bool :=
  rkmMkPack_m2_r256_s5_p0 ++ (rkmMkPack_m2_r256_s5_p1 ++ rkmMkPack_m2_r256_s5_p2)
/-- Part `0` of `rkmMkPack_m2_r256_s6`. -/
def rkmMkPack_m2_r256_s6_p0 : List Bool := [
  false, true, true, false, false, true, false, true, false, true, true, true, false, false, false,
  false, false, true, true, false, false, false, false, false, false, false, false, true, false,
  true, false, false, true, false, false, true, false, false, false, true, true, false, false,
  false, true, true, false, true, false, false, true, false, true, false, false, false, false,
  true, false, false, true, false, false, false, false, true, false, false, false, false, true,
  false, false, false, true, false, false, true, false, false, true, false, false, false, false,
  true, false, false, false, false, true, false, false, false, false, false
  ]
/-- Part `1` of `rkmMkPack_m2_r256_s6`. -/
def rkmMkPack_m2_r256_s6_p1 : List Bool := [
  true, false, false, false, true, false, false, false, true, false, false, false, false, false,
  true, false, true, false, false, true, false, false, false, false, true, false, false, false,
  false, true, false, false, false, false, true, false, false, false, false, true, false, true,
  false, false, true, false, false, false, false, true, false, false, false, false, true, false,
  false, false, false, true, false, false, false, false, false, false, false, false, false, true,
  false, false, false, false, true, false, false, false, false, true, false, false, false, false,
  false, false, false, false, false, true, false, false, false, false, true, false
  ]
/-- Part `2` of `rkmMkPack_m2_r256_s6`. -/
def rkmMkPack_m2_r256_s6_p2 : List Bool := [
  false, false, false, true, false, false, false, false, true, false, false, false, false, true,
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, false, false, false, true, false, false, false, true, false,
  false, true, true, false, false, false, true, true, false, false, false, true, true
  ]
/-- Sign-kick mask segment `6` for `(m = 2, r = 256)`. -/
def rkmMkPack_m2_r256_s6 : List Bool :=
  rkmMkPack_m2_r256_s6_p0 ++ (rkmMkPack_m2_r256_s6_p1 ++ rkmMkPack_m2_r256_s6_p2)
/-- Multi-segment sign-kick masks for `(m = 2, r = 256)`. -/
def rkmMasksPack_m2_r256 : List (List Bool) := [
  [], [], rkmMkPack_m2_r256_s2, rkmMkPack_m2_r256_s3, rkmMkPack_m2_r256_s4, rkmMkPack_m2_r256_s5,
  rkmMkPack_m2_r256_s6, []
  ]
/-- Hit-row chunk `0` for `(m = 2, r = 256)`. -/
def rkmRowPack_m2_r256_p0 : List ℕ := [
  82662, 83320, 1159, 389159, 604, 14633, 18091, 56512, 34, 13888, 121900, 155343, 12861, 268103,
  698152, 0, 601266, 374, 22689, 1854184, 98042, 61309, 38583, 307328, 172565, 70668, 434876,
  287228, 45088, 658417, 174344, 25279, 277850, 167146, 45922, 103603, 418100, 33883, 1583, 444010,
  164393, 49932, 127, 1247020, 1316436, 441803, 1972705, 1972139, 143508, 119124, 4488, 1531919,
  2679240, 282905, 159, 1314353, 212845, 719536, 2588318, 49537, 1160292, 281306, 1120680, 997979,
  13460, 417513, 702828, 192460, 553029, 1162072, 1551845, 2153315, 2957283, 596284, 529665,
  1834383, 10512, 819369, 639377, 1296799, 1454618, 525871, 247636, 21949, 6710913, 2508865,
  8821108, 369068, 1046216, 6695298, 183487, 958777, 111931, 1372703, 4464572, 5194657
  ]
/-- Hit-row chunk `1` for `(m = 2, r = 256)`. -/
def rkmRowPack_m2_r256_p1 : List ℕ := [
  2408362, 6928766, 7731726, 2640193, 13706637, 2547107, 844637, 21257353, 68963933, 22109722,
  5434970, 14450490, 12320544, 10640527, 30196353, 9402793, 3055226, 6961504, 108021, 97669,
  3371878, 5086, 11780907, 24505121, 5760216, 32820142, 2175394, 689590, 53385148, 23201044,
  18499227, 50759113, 8474172, 11430093, 5083125, 25399943, 14378897, 1723248, 474393, 71491591,
  61566695, 133092, 1013893, 9232240, 32213524, 90082232, 314016, 1185845, 64956895, 35350920,
  6751712, 1240297, 13076916, 1795840, 40682638, 631699, 1017212, 1872444, 15395596, 41161817,
  26134669, 45637307, 38097, 189307182, 968290, 88690518, 260906317, 1003620, 42362166, 8168884,
  94011813, 11849066, 6993674, 60278122, 41449189, 79421146, 44462665, 1396664, 636639262,
  23823955, 9929331, 25362530, 13074286, 1541745, 234802, 4034821, 31011398, 161458520, 11982498,
  446718441, 57251890, 97362495, 54517842, 37707268, 35634325, 424812424
  ]
/-- Hit-row chunk `2` for `(m = 2, r = 256)`. -/
def rkmRowPack_m2_r256_p2 : List ℕ := [
  189005149, 172682308, 6139805, 3276009, 303484108, 25278018, 35547388, 33769959, 169362956,
  49284897, 67798851, 707983386, 43125, 56169205, 618993976, 8610740, 538109736, 248945264,
  6583455, 311083924, 234332141, 283272, 1378790890, 120086669, 85796, 34499978, 793383236,
  815186750, 105914336, 2237038, 74163915, 104509491, 221409786, 407755712, 369660719, 32183080,
  75441807, 236749741, 1113344082, 464549452, 193022152, 367074701, 304416217, 74383188,
  1111050714, 174815212, 615346971, 7325639204, 33590910, 111361544, 1867242481, 955998574,
  2614145237, 387904396, 404842307, 6501648872, 27747346908, 2838264069, 4722093470, 6853155155,
  184947236223, 401742646146, 273850220661, 59931780495
  ]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 2, r = 256)`. -/
def rkmRowPack_m2_r256 : List ℕ :=
  rkmRowPack_m2_r256_p0 ++ (rkmRowPack_m2_r256_p1 ++ rkmRowPack_m2_r256_p2)

/-- Sign-kick mask segment `2` for `(m = 4, r = 192)`. -/
def rkmMkPack_m4_r192_s2 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, false, false, false, false, false,
  false, false, false, false, true, false, true
  ]
/-- Sign-kick mask segment `3` for `(m = 4, r = 192)`. -/
def rkmMkPack_m4_r192_s3 : List Bool := [
  false, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, true
  ]
/-- Sign-kick mask segment `4` for `(m = 4, r = 192)`. -/
def rkmMkPack_m4_r192_s4 : List Bool := [
  true, true, false, true, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  true, false, false, false, false, false, false, false, true
  ]
/-- Sign-kick mask segment `6` for `(m = 4, r = 192)`. -/
def rkmMkPack_m4_r192_s6 : List Bool := [
  true, false, false, true, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  true
  ]
/-- Multi-segment sign-kick masks for `(m = 4, r = 192)`. -/
def rkmMasksPack_m4_r192 : List (List Bool) := [
  [], [], rkmMkPack_m4_r192_s2, rkmMkPack_m4_r192_s3, rkmMkPack_m4_r192_s4,
  [true, false, false, false, true], rkmMkPack_m4_r192_s6, []
  ]
/-- Hit-row chunk `0` for `(m = 4, r = 192)`. -/
def rkmRowPack_m4_r192_p0 : List ℕ := [
  845165, 167305928, 50441138, 352927855, 899521165, 1115221108, 767826377, 154507344, 69233954,
  865040680, 1334758515, 1325218955, 118869279, 204368478, 849824392, 3098413900, 1159754455,
  16713127, 380596443, 3261317458, 2829440254, 8435527291, 920225301, 4167975944, 20941533866,
  77800583641, 103697253684, 99890935901, 128351905308, 162462761680, 148459089456, 96362171965,
  53091981498, 30394827588, 19242299759, 12350625349, 7128461983, 3412370846, 1303818634,
  391596100, 91551610, 16483689, 2309666, 292031, 56593, 26430, 18177, 11276, 5611, 2264, 765, 222,
  56, 12, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Hit-row chunk `1` for `(m = 4, r = 192)`. -/
def rkmRowPack_m4_r192_p1 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 4, r = 192)`. -/
def rkmRowPack_m4_r192 : List ℕ :=
  rkmRowPack_m4_r192_p0 ++ rkmRowPack_m4_r192_p1

/-- Sign-kick mask segment `3` for `(m = 4, r = 256)`. -/
def rkmMkPack_m4_r256_s3 : List Bool := [
  false, false, false, false, false, false, false, true, true, true, true, true, false, true, true,
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true, true, true, true, false, false, false,
  false, false, false, true, false, true
  ]
/-- Part `0` of `rkmMkPack_m4_r256_s4`. -/
def rkmMkPack_m4_r256_s4_p0 : List Bool := [
  false, false, false, false, false, true, false, true, true, false, true, false, false, false,
  false, true, true, true, true, false, false, true, false, false, true, false, false, true, true,
  true, false, false, false, true, true, true, true, false, true, true, true, true, true, false,
  true, false, false, false, true, true, true, true, true, true, false, true, true, true, false,
  true, true, true, true, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, true, false, false, false, false, false
  ]
/-- Part `1` of `rkmMkPack_m4_r256_s4`. -/
def rkmMkPack_m4_r256_s4_p1 : List Bool := [
  false, false, true, true, true, false, false, false, false, true, true, true, true, false, false,
  false, false, true
  ]
/-- Sign-kick mask segment `4` for `(m = 4, r = 256)`. -/
def rkmMkPack_m4_r256_s4 : List Bool :=
  rkmMkPack_m4_r256_s4_p0 ++ rkmMkPack_m4_r256_s4_p1
/-- Part `0` of `rkmMkPack_m4_r256_s5`. -/
def rkmMkPack_m4_r256_s5_p0 : List Bool := [
  true, false, false, true, false, true, false, false, true, false, true, false, true, false,
  false, true, false, false, false, false, true, false, false, false, false, true, false, true,
  false, false, false, true, false, true, true, false, false, false, false, false, true, true,
  false, true, true, false, false, true, true, false, true, true, true, true, false, true, true,
  false, true, true, false, false, false, false, true, false, true, false, false, true, false,
  false, false, false, false, false, false, false, false, false, false, true, true, false, false,
  true, false, false, false, false, false, true, true, false, false, true
  ]
/-- Part `1` of `rkmMkPack_m4_r256_s5`. -/
def rkmMkPack_m4_r256_s5_p1 : List Bool := [
  false, false, false, false, false, true, false, true, false, false, false, false, false, false,
  true, false, false, false, false, false, true, false, false, false, false, false, true, true,
  true, true, false, false, false, false, true, true, true, true, false, false, false, false,
  false, true, true, true, true, false, false, false, false, false, true, true, true, true, true,
  true, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, true, true,
  true, true, true, false, false, false, false, true, true, true, false
  ]
/-- Part `2` of `rkmMkPack_m4_r256_s5`. -/
def rkmMkPack_m4_r256_s5_p2 : List Bool := [
  false, false, false, false, false, true, true, true, false, true
  ]
/-- Sign-kick mask segment `5` for `(m = 4, r = 256)`. -/
def rkmMkPack_m4_r256_s5 : List Bool :=
  rkmMkPack_m4_r256_s5_p0 ++ (rkmMkPack_m4_r256_s5_p1 ++ rkmMkPack_m4_r256_s5_p2)
/-- Part `0` of `rkmMkPack_m4_r256_s6`. -/
def rkmMkPack_m4_r256_s6_p0 : List Bool := [
  false, true, true, true, false, true, false, false, true, false, true, false, true, true, false,
  true, true, false, false, false, false, false, false, true, true, true, false, false, false,
  false, true, true, false, true, false, true, false, false, false, false, true, false, false,
  false, false, true, false, false, false, true, false, false, false, false, false, true, true,
  false, false, false, true, false, false, false, false, true, false, false, false, false, true,
  false, false, false, false, true, false, false, false, false, true, false, false, false, false,
  true, false, false, false, false, true, false, false, false, false, true
  ]
/-- Part `1` of `rkmMkPack_m4_r256_s6`. -/
def rkmMkPack_m4_r256_s6_p1 : List Bool := [
  false, false, false, false, true, false, false, false, false, true, false, false, false, false,
  true, false, false, false, true, true, false, false, false, false, false, false, false, false,
  false, true, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, true, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, true, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false
  ]
/-- Part `2` of `rkmMkPack_m4_r256_s6`. -/
def rkmMkPack_m4_r256_s6_p2 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true, true, true, true, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, true, false, false,
  false, true, false, false, false, true
  ]
/-- Sign-kick mask segment `6` for `(m = 4, r = 256)`. -/
def rkmMkPack_m4_r256_s6 : List Bool :=
  rkmMkPack_m4_r256_s6_p0 ++ (rkmMkPack_m4_r256_s6_p1 ++ rkmMkPack_m4_r256_s6_p2)
/-- Multi-segment sign-kick masks for `(m = 4, r = 256)`. -/
def rkmMasksPack_m4_r256 : List (List Bool) := [
  [], [], [], rkmMkPack_m4_r256_s3, rkmMkPack_m4_r256_s4, rkmMkPack_m4_r256_s5,
  rkmMkPack_m4_r256_s6, []
  ]
/-- Hit-row chunk `0` for `(m = 4, r = 256)`. -/
def rkmRowPack_m4_r256_p0 : List ℕ := [
  229, 13729, 47691, 125982, 66411, 23264, 6664, 399, 1309, 1994, 86003, 28434, 110602, 1908, 9679,
  42557, 309523, 168948, 123413, 793, 3577, 4193, 194728, 315104, 2797, 66235, 98191, 613863,
  13285, 67, 73634, 438948, 30800, 3191, 4103, 113267, 98098, 21032, 184210, 14671, 98838, 243502,
  25762, 400573, 865551, 2033076, 1979, 1119503, 1054430, 1802546, 1306456, 53596, 1799327,
  4182350, 2847980, 1910298, 11650, 3196664, 1648019, 718945, 72688, 65184, 921509, 115256, 131585,
  387932, 1306133, 342008, 4113050, 5856159, 362067, 1240371, 828452, 111323, 584094, 1036133,
  26758, 296744, 4155923, 2892809, 157309, 1855345, 383014, 2387472, 59094, 3101423, 1500447,
  9643134, 1892479, 195662, 591423, 349366, 10869, 659944, 1346125, 3054833
  ]
/-- Hit-row chunk `1` for `(m = 4, r = 256)`. -/
def rkmRowPack_m4_r256_p1 : List ℕ := [
  1398000, 11541042, 6301, 2405733, 3338479, 1734648, 298663, 3154355, 6521700, 21394, 342957,
  735249, 908207, 1066736, 1300592, 2635623, 652836, 3711865, 16324807, 938729, 2731528, 3138621,
  17701, 8735644, 4600193, 405833, 3964253, 1958, 666384, 4670865, 875767, 10690167, 2158190,
  162493, 1993418, 8005, 3256570, 684, 395318, 3020584, 493796, 295122, 2605906, 741950, 2796857,
  6864072, 1540484, 10613053, 439964, 19003472, 9094871, 7543099, 8117118, 23436125, 76441031,
  23224104, 31083, 2226345, 75157899, 35909924, 74226636, 127026418, 260575, 98702565, 5664705,
  39973386, 3568418, 23990037, 2493326, 28849966, 4060194, 27179858, 17753272, 31507786, 28045997,
  17746431, 48655563, 7107754, 69997670, 331658, 105623849, 2839909, 212479176, 29386, 283421784,
  25150366, 165470424, 28420415, 54650382, 13447601, 314765577, 30383781, 151121543, 12531043,
  200151158, 43833530
  ]
/-- Hit-row chunk `2` for `(m = 4, r = 256)`. -/
def rkmRowPack_m4_r256_p2 : List ℕ := [
  160462826, 64134675, 146899179, 112676927, 108456948, 177588601, 57890057, 253362162, 10046877,
  290970922, 2692483, 314138064, 72575155, 229461596, 224120575, 88898301, 423138449, 777064,
  427471786, 139516770, 391721920, 402495878, 29537898, 757109935, 199653803, 615107190, 984246053,
  131186313, 751094734, 392291763, 8741225, 3907042054, 1252620773, 5655392306, 3572216107,
  1447160383, 1882552270, 3092332, 70964870, 753346045, 401242345, 8470184695, 10242054190,
  1997634922, 10948079, 1131912294, 23171872239, 94742022562, 181210945409, 220954686043,
  194362994124, 127944244387, 65820429752, 27681910371, 9463932609, 2505403899, 494070008,
  72366458, 8038247, 688780, 45106, 2149, 65, 0
  ]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 4, r = 256)`. -/
def rkmRowPack_m4_r256 : List ℕ :=
  rkmRowPack_m4_r256_p0 ++ (rkmRowPack_m4_r256_p1 ++ rkmRowPack_m4_r256_p2)

/-- Sign-kick mask segment `2` for `(m = 4, r = 384)`. -/
def rkmMkPack_m4_r384_s2 : List Bool := [
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, false, false, false, false, false, false, false, false,
  false, false, false, false, false, false, true
  ]
/-- Multi-segment sign-kick masks for `(m = 4, r = 384)`. -/
def rkmMasksPack_m4_r384 : List (List Bool) := [
  [true, true, true], [], rkmMkPack_m4_r384_s2, [], [false, true], [false, true], [], []
  ]
/-- Hit-row chunk `0` for `(m = 4, r = 384)`. -/
def rkmRowPack_m4_r384_p0 : List ℕ := [
  1894, 21461, 173155, 1024050, 4694714, 17322133, 52689949, 134150966, 288356039, 524644545,
  804706406, 1026724062, 1058203834, 826390281, 414404251, 65517775, 37893348, 384644940,
  851510931, 1039501721, 752877208, 231879050, 4058539, 415927758, 1250271373, 1832313506,
  1612297928, 734729757, 34687715, 364432207, 1772164974, 3273050053, 3539777910, 2113985575,
  257886005, 782125362, 6913340344, 19694292123, 41891310058, 58641744149, 97813994111,
  85207546216, 133557382811, 101606648850, 93663382777, 104990113511, 72164859318, 43349077349,
  39139367963, 36664535573, 23118668419, 9352957402, 2916853828, 1039444033, 583451145, 435431007,
  320157181, 206533748, 116498407, 59034494, 27623111, 12179756, 5126794, 2075768, 811777, 307316,
  112763, 40134, 13863, 4649, 1513, 478, 146, 43, 11, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0
  ]
/-- Hit-row chunk `1` for `(m = 4, r = 384)`. -/
def rkmRowPack_m4_r384_p1 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Hit-row chunk `2` for `(m = 4, r = 384)`. -/
def rkmRowPack_m4_r384_p2 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Hit-row chunk `3` for `(m = 4, r = 384)`. -/
def rkmRowPack_m4_r384_p3 : List ℕ := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
  ]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 4, r = 384)`. -/
def rkmRowPack_m4_r384 : List ℕ :=
  rkmRowPack_m4_r384_p0 ++ (rkmRowPack_m4_r384_p1 ++ (rkmRowPack_m4_r384_p2
    ++ rkmRowPack_m4_r384_p3))

/-- Concatenates two natural lists without `++` elaboration overhead. -/
def rkmNatCat2Pack : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => List.cons x (rkmNatCat2Pack xs ys)
/-- Concatenates `<= 64`-element `< 2 ^ 58` natural chunks. -/
def rkmNatChunksPack : List (List ℕ) → List ℕ
  | [] => []
  | cs :: css => rkmNatCat2Pack cs (rkmNatChunksPack css)
/-- Maps `< 2 ^ 58` naturals into non-negative `List ℤ`. -/
def rkmHbOfNatsPack : List ℕ → List ℤ
  | [] => []
  | n :: ns => List.cons (Int.ofNat n) (rkmHbOfNatsPack ns)
/-- Strict `List ℤ` cons helper for decoded checkpoints. -/
def rkmConsIntPack : ℤ → List ℤ → List ℤ
  | Int.ofNat v, [] => [Int.ofNat v]
  | Int.ofNat v, h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v, [] => [Int.negSucc v]
  | Int.negSucc v, h :: t => Int.negSucc v :: h :: t
/-- Decodes `2 * 10 ^ 15`-biased `< 2 ^ 58` naturals into `List ℤ`. -/
def rkmDecOfNatsPack : List ℕ → List ℤ
  | [] => []
  | u :: us => rkmConsIntPack (rkmForcedSubNatNat u 2000000000000000) (rkmDecOfNatsPack us)

/-- Raw `< 2 ^ 58` natural words for `rkmHbPack_m2_r512_s0`. -/
def rkmHbNatPack_m2_r512_s0 : List ℕ := rkmNatChunksPack
  [
   [310082170284551,424182649706197,501408343579330,557368455769390,598121349560371,
    626697223554764,644771899342344,653271573215579,652624449160548,642857678692551,
    623599343864267,593986140027528,552418859874768,495971522700990,418752219529151,
    305506186347972]]
/-- Coupling vector for `(m = 2, r = 512)` segment `0`. -/
def rkmHbPack_m2_r512_s0 : List ℤ := rkmHbOfNatsPack rkmHbNatPack_m2_r512_s0
/-- Raw `< 2 ^ 58` natural words for `rkmViPack_m2_r512_s0`. -/
def rkmViNatPack_m2_r512_s0 : List ℕ := [3000000000000000]
/-- Input state vector for `(m = 2, r = 512)` segment `0`. -/
def rkmViPack_m2_r512_s0 : List ℤ := rkmDecOfNatsPack rkmViNatPack_m2_r512_s0
/-- Raw `< 2 ^ 58` natural words for `rkmVoPack_m2_r512_s0`. -/
def rkmVoNatPack_m2_r512_s0 : List ℕ := rkmNatChunksPack
  [
   [2165441226854035,2332941991435937,2458175843628886,2496747776898703,2448894783483819,
    2348163257344242,2235722717404081,2140706591705428,2074441682043433,2034964558091412,
    2014555497272228,2005342165868716,2001711524167563,2000470621848942,2000107859413718,
    2000019474871375,2000002404466748]]
/-- Post-walk vector for `(m = 2, r = 512)` segment `0`. -/
def rkmVoPack_m2_r512_s0 : List ℤ := rkmDecOfNatsPack rkmVoNatPack_m2_r512_s0

/-- Raw `< 2 ^ 58` natural words for `rkmHbPack_m2_r512_s1`. -/
def rkmHbNatPack_m2_r512_s1 : List ℕ := rkmNatChunksPack
  [
   [208384519879650,291329344304661,352642365253287,402350919558682,444378512685676,
    480754864313801,512694641216931,540994021075243,566208484809339,588743534159176,
    608905439834877,626931660388748,643010083136333,657291728915715,669899438755352,
    680933985078635,690478472119815,698601563776635,705359884721771,710799822904071,
    714958887137790,717866724910794,719545872853070,720012289550266,719275703894990,
    717339799578581,714202246026802,709854576877125,704281907973899,697462476823296,
    689366973341264,679957616002555,669186905911892,656995960394549,643312281820616,
    628046747091571,611089492085099,592304183628400,571519863120999,548518999598138,
    523019372937076,494645398414658,462880234644934,426980081986093,385806049881800,
    337448761075646,278206158594702,198589805125771]]
/-- Coupling vector for `(m = 2, r = 512)` segment `1`. -/
def rkmHbPack_m2_r512_s1 : List ℤ := rkmHbOfNatsPack rkmHbNatPack_m2_r512_s1
/-- Raw `< 2 ^ 58` natural words for `rkmViPack_m2_r512_s1`. -/
def rkmViNatPack_m2_r512_s1 : List ℕ := rkmNatChunksPack
  [
   [2165441226854035,2332941991435937,2458175843628886,2496747776898703,2448894783483819,
    2348163257344242,2235722717404081,2140706591705428,2074441682043433,2034964558091412,
    2014555497272228,2005342165868716,2001711524167563,2000470621848942,2000107859413718,
    2000019474871375,2000002404466748]]
/-- Input state vector for `(m = 2, r = 512)` segment `1`. -/
def rkmViPack_m2_r512_s1 : List ℤ := rkmDecOfNatsPack rkmViNatPack_m2_r512_s1
/-- Raw `< 2 ^ 58` natural words for `rkmVoPack_m2_r512_s1`. -/
def rkmVoNatPack_m2_r512_s1 : List ℕ := rkmNatChunksPack
  [
   [2000000080911495,2000000505483085,2000002811314749,2000011615613594,2000041457395697,
    2000129707066105,2000363159693349,2000923300420446,2002152356625401,2004634767623659,
    2009272850520552,2017316642923996,2030295557413786,2049803991276079,2077124518794658,
    2112732504041941,2155799328107155,2203866206171983,2252861754154782,2297564057795854,
    2332472654451261,2352902439714436,2356004128311019,2341407970915226,2311292625272831,
    2269862609565162,2222403833811902,2174204367502196,2129636612466341,2091605817448204,
    2061426510105535,2039054060725282,2023518808462336,2013399057904951,2007211230619593,
    2003659849003206,2001747949991413,2000783641491458,2000328783623120,2000128616418735,
    2000046696199964,2000015644177315,2000004800340033,2000001335798044,2000000332520119,
    2000000072579191,2000000013454857,2000000001998060,2000000000205912]]
/-- Post-walk vector for `(m = 2, r = 512)` segment `1`. -/
def rkmVoPack_m2_r512_s1 : List ℤ := rkmDecOfNatsPack rkmVoNatPack_m2_r512_s1

/-- Raw `< 2 ^ 58` natural words for `rkmHbPack_m2_r512_s2`. -/
def rkmHbNatPack_m2_r512_s2 : List ℕ := rkmNatChunksPack
  [
   [136143616000000,191595199935038,233500762995358,268287976172981,298459231880212,
    325304054791279,349592019365427,371826795501902,392359761633293,411447842416021,
    429285797843866,446025545335141,461788367707150,476672971273234,490760999884474,
    504120923869201,516810854283728,528880625106900,540373363836841,551326696465668,
    561773685949525,571743572985904,581262367824978,590353328236060,599037349351444,
    607333284501164,615258211429911,622827654863309,630055773874341,636955520628537,
    643538775677500,649816463898850,655798654357678,661494646726743,666913046404131,
    672061830074196,676948403145834,681579650252799,685961979800204,690101363378886,
    694003370736994,697673200889780,701115709859279,704335435461696,707336619498833,
    710123227658539,712698967386010,715067303951446,717231474908716,719194503113553,
    720959208447387,722528218373766,723903977437785,725088755804662,726084656921165,
    726893624372787,727517448000000,727957769328578,728216086361506,728293757773302,
    728192006541642,727911923045684,727454467655511,726820472832509],
   [726010644756144,725025564488510,723865688684068,722531349848160,721022756144043,
    719339990744393,717483010719289,715451645448668,713245594542971,710864425251188,
    708307569330641,705574319347532,702663824371439,699575085020478,696306947806576,
    692858098722124,689227056000000,685412161968344,681411573909303,677223253816913,
    672844956933021,668274218921159,663508341516116,658544376460828,653379107511455,
    648009030254949,642430329439933,636638853469633,630630085642987,624399111654393,
    617940582770634,611248673991253,604317036360797,597138742430974,589706223658990,
    582011198263265,574044587723607,565796419688708,557255714510729,548410351925737,
    539246913485411,529750495143891,519904482806133,509690281495858,499086985876289,
    488070975820942,476615415080280,464689623048269,452258277985298,439280392849761,
    425707978917969,411484272190820,396541333681421,380796729797347,364148820563225,
    346469866705866,327595576000000,307308540548416,285310529967784,261172809844192,
    234238447539839,203403629662860,166520546185765,118057250812692]]
/-- Coupling vector for `(m = 2, r = 512)` segment `2`. -/
def rkmHbPack_m2_r512_s2 : List ℤ := rkmHbOfNatsPack rkmHbNatPack_m2_r512_s2
/-- Raw `< 2 ^ 58` natural words for `rkmViPack_m2_r512_s2`. -/
def rkmViNatPack_m2_r512_s2 : List ℕ := rkmNatChunksPack
  [
   [1999999919088505,1999999494516915,1999997188685251,1999988384386406,1999958542604303,
    1999870292933895,2000363159693349,2000923300420446,2002152356625401,2004634767623659,
    2009272850520552,2017316642923996,2030295557413786,2049803991276079,2077124518794658,
    2112732504041941,2155799328107155,2203866206171983,2252861754154782,2297564057795854,
    2332472654451261,2352902439714436,2356004128311019,2341407970915226,2311292625272831,
    2269862609565162,2222403833811902,2174204367502196,2129636612466341,2091605817448204,
    2061426510105535,2039054060725282,2023518808462336,2013399057904951,2007211230619593,
    2003659849003206,2001747949991413,2000783641491458,2000328783623120,2000128616418735,
    2000046696199964,2000015644177315,2000004800340033,2000001335798044,2000000332520119,
    2000000072579191,2000000013454857,2000000001998060,2000000000205912]]
/-- Input state vector for `(m = 2, r = 512)` segment `2`. -/
def rkmViPack_m2_r512_s2 : List ℤ := rkmDecOfNatsPack rkmViNatPack_m2_r512_s2
/-- Raw `< 2 ^ 58` natural words for `rkmVoPack_m2_r512_s2`. -/
def rkmVoNatPack_m2_r512_s2 : List ℕ := rkmNatChunksPack
  [
   [2000005444490687,2000015853374905,2000031022028821,2000046354586604,2000054517258810,
    2000049011551356,2000028363527386,1999998265266757,1999969915799464,1999955024458899,
    1999960027007246,1999982663434459,2000012805433358,2000037107844303,2000045078781439,
    2000033587636969,2000007827272806,1999978612143438,1999957576394968,1999952549223997,
    1999964964174989,1999990010477834,2000019013210406,2000042772659273,2000054505014743,
    2000051475291316,2000035082758678,2000009735155547,1999981147676297,1999954704575298,
    1999934318947374,1999921953527204,1999917732661670,1999920441342390,1999928180414980,
    1999939006016564,1999951494447009,1999965316416617,1999982067688237,2000006792050059,
    2000050855617918,2000137074461038,2000308189607239,2000639769345426,2001258161028410,
    2002362950916893,2004251358487854,2007339204155451,2012170101439388,2019402389594815,
    2029763432204804,2043964560762034,2062577713144702,2085885930966198,2113731925751465,
    2145398181861815,2179554534287268,2214302049425503,2247325166030002,2276140528888866,
    2298406663396944,2312240601236552,2316481576097176,2310850466408074],
   [2295974955100286,2273278765563951,2244761189250508,2212713295221389,2179425213940702,
    2146934008002324,2116846736897332,2090253488193671,2067725901807740,2049382368369561,
    2034993798304978,2024103547312530,2016139988411435,2010507819453586,2006652072627150,
    2004095221199154,2002451928951764,2001427827538581,2000808725663021,2000445551041518,
    2000238764874951,2000124456834929,2000063100594649,2000031117004697,2000014924058002,
    2000006960936322,2000003157170212,2000001392280548,2000000596888320,2000000248728686,
    2000000100726366,2000000039632493,2000000015147625,2000000005622159,2000000002025780,
    2000000000708372,2000000000240291,2000000000079034,2000000000025190,2000000000007772,
    2000000000002317,2000000000000664,2000000000000181,2000000000000046,2000000000000009,
    2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
/-- Post-walk vector for `(m = 2, r = 512)` segment `2`. -/
def rkmVoPack_m2_r512_s2 : List ℤ := rkmDecOfNatsPack rkmVoNatPack_m2_r512_s2

/-- Raw `< 2 ^ 58` natural words for `rkmHbPack_m2_r512_s3`. -/
def rkmHbNatPack_m2_r512_s3 : List ℕ := rkmNatChunksPack
  [
   [101612268895488,143311592083076,175042560062922,201570160345139,224745473096626,
    245520492766805,264462291720656,281941344832529,298215672035266,313473634033300,
    327857802428519,341479231158469,354426465517880,366771483599121,378573758475255,
    389883120769195,400741828454341,411186097004964,421247252667550,430952616571436,
    440326192778819,449389210995789,458160559841461,466657136535003,474894131929771,
    482885264952842,490642977029405,498178594550109,505502465587458,512624075689975,
    519552146546828,526294720528084,532859233501162,539252577855721,545481157303355,
    551550934730272,557467474152545,563235977640849,568861317934696,574348067347299,
    579700523465408,584922732069253,590018507632550,594991451708599,599844969463728,
    604582284581956,609206452733377,613720373772430,618126802809900,622428360283597,
    626627541136579,630726723198029,634728174850117,638634062054067,642446454799903,
    646167333036815,649798592134520,653342047920336,656799441331675,660172442719386,
    663462655833522,666671621519813,669800821152179,672851679824005],
   [675825569318672,678723810877727,681547677783375,684298397770281,686977155280336,
    689585093572701,692123316700343,694592891363274,696994848647743,699330185659865,
    701599867061419,703804826514847,705945968043967,708024167316278,710040272852329,
    711995107167125,713889467848172,715724128574384,717499840079747,719217331065330,
    720877309062975,722480461253707,724027455243726,725518939800593,726955545552045,
    728337885649702,729666556399764,730942137862632,732165194423281,733336275334066,
    734455915231516,735524634628603,736542940383829,737511326148423,738430272792819,
    739300248813539,740121710721517,740895103412839,741620860522800,742299404764147,
    742931148250292,743516492804253,744055830254033,744549542715076,744998002860451,
    745401574179316,745760611224234,746075459847846,746346457429380,746573933091469,
    746758207907690,746899595101238,746998400235115,747054921394188,747069449359463,
    747042267774879,746973653306939,746863875797447,746713198409625,746521877767857,
    746290164091300,746018301321582,745706527244797,745355073607995],
   [744964166230350,744534025109188,744064864521026,743556893117792,743010314018352,
    742425324895496,741802118058496,741140880531364,740441794126908,739705035516705,
    738930776297063,738119183051081,737270417406874,736384636092036,735461990984422,
    734502629159286,733506692932853,732474319902359,731405642982599,730300790439034,
    729159885917472,727983048470352,726770392579655,725522028176449,724238060657076,
    722918590895988,721563715255216,720173525590481,718748109253908,717287549093343,
    715791923448227,714261306142012,712695766471055,711095369189968,709460174493355,
    707790237993875,706085610696579,704346338969429,702572464509921,700764024307735,
    698921050603291,697043570842129,695131607624968,693185178653351,691204296670713,
    689188969398734,687139199468837,685054984348627,682936316263126,680783182110589,
    678595563372690,676373436018872,674116770404609,671825531163325,669499677091703,
    667139161028090,664743929723679,662313923706147,659849077135380,657349317650904,
    654814566210628,652244736920440,649639736854205,646999465863662],
   [644323816377676,641612673190281,638865913236892,636083405358035,633265010049874,
    630410579200788,627519955813188,624592973709673,621629457222615,618629220866142,
    615592068989424,612517795410112,609406183026635,606257003408006,603070016359661,
    599844969463728,596581597592018,593279622389848,589938751728703,586558679125518,
    583139083126218,579679626650923,576179956297999,572639701603901,569058474255475,
    565435867251048,561771454006362,558064787400971,554315398760346,550522796768456,
    546686466305088,542805867201597,538880432908128,534909569064674,530892651967495,
    526829026921557,522718006468640,518558868479630,514350854098229,510093165521899,
    505784963604183,501425365260740,497013440659292,492548210171286,488028641060344,
    483453643879413,478822068544943,474132700052233,469384253791350,464575370417407,
    459704610222628,454770446950054,449771260980071,444705331810607,439570829739847,
    434365806646056,429088185742253,423735750163428,418306130220111,412796789123356,
    407205006951702,401527862588843,395762213309873,389904671631823],
   [383951578967746,377898975529090,371742565803462,365477678787544,359099221969077,
    352601627815621,345978791225284,339223996003726,332329827922198,325288071240528,
    318089584686423,310724151681332,303180297966703,295445067524839,287503744522238,
    279339504494660,270932971458419,262261647973350,253299170590901,244014320530172,
    234369683471383,224319793307574,213808494144927,202765076270226,191098408565041,
    178687629957065,165366557420495,150895690872467,134907089730239,116780813695602,
    95307063826043,67360054113516]]
/-- Coupling vector for `(m = 2, r = 512)` segment `3`. -/
def rkmHbPack_m2_r512_s3 : List ℤ := rkmHbOfNatsPack rkmHbNatPack_m2_r512_s3
/-- Raw `< 2 ^ 58` natural words for `rkmViPack_m2_r512_s3`. -/
def rkmViNatPack_m2_r512_s3 : List ℕ := rkmNatChunksPack
  [
   [2000005444490687,1999984146625095,1999968977971179,2000046354586604,1999945482741190,
    2000049011551356,2000028363527386,1999998265266757,2000030084200536,1999955024458899,
    2000039972992754,2000017336565541,2000012805433358,2000037107844303,1999954921218561,
    2000033587636969,2000007827272806,2000021387856562,1999957576394968,1999952549223997,
    1999964964174989,1999990010477834,1999980986789594,2000042772659273,2000054505014743,
    1999948524708684,2000035082758678,1999990264844453,2000018852323703,2000045295424702,
    2000065681052626,2000078046472796,2000082267338330,2000079558657610,2000071819585020,
    2000060993983436,2000048505552991,2000034683583383,2000017932311763,1999993207949941,
    1999949144382082,2000137074461038,2000308189607239,2000639769345426,2001258161028410,
    2002362950916893,2004251358487854,2007339204155451,2012170101439388,2019402389594815,
    2029763432204804,2043964560762034,2062577713144702,2085885930966198,2113731925751465,
    2145398181861815,2179554534287268,2214302049425503,2247325166030002,2276140528888866,
    2298406663396944,2312240601236552,2316481576097176,2310850466408074],
   [2295974955100286,2273278765563951,2244761189250508,2212713295221389,2179425213940702,
    2146934008002324,2116846736897332,2090253488193671,2067725901807740,2049382368369561,
    2034993798304978,2024103547312530,2016139988411435,2010507819453586,2006652072627150,
    2004095221199154,2002451928951764,2001427827538581,2000808725663021,2000445551041518,
    2000238764874951,2000124456834929,2000063100594649,2000031117004697,2000014924058002,
    2000006960936322,2000003157170212,1999998607719452,2000000596888320,1999999751271314,
    1999999899273634,1999999960367507,1999999984852375,2000000005622159,2000000002025780,
    2000000000708372,2000000000240291,2000000000079034,1999999999974810,2000000000007772,
    2000000000002317,2000000000000664,2000000000000181,2000000000000046,2000000000000009,
    2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
/-- Input state vector for `(m = 2, r = 512)` segment `3`. -/
def rkmViPack_m2_r512_s3 : List ℤ := rkmDecOfNatsPack rkmViNatPack_m2_r512_s3
/-- Raw `< 2 ^ 58` natural words for `rkmVoPack_m2_r512_s3`. -/
def rkmVoNatPack_m2_r512_s3 : List ℕ := rkmNatChunksPack
  [
   [1999982358005967,1999998912049076,2000025302471992,2000029619084170,2000010078740256,
    1999991511210923,1999985648092113,1999979507547094,1999965812668635,1999961076129168,
    1999981039284238,2000010588233989,2000021307026654,2000006272996042,1999994430768012,
    2000004991359100,2000031993842022,2000043558005718,2000030521260018,2000004304504502,
    1999980383490029,1999964454176087,1999951789501571,1999948474505529,1999960589151063,
    1999978731749236,1999987178079760,1999978214893730,1999965840052708,1999972949634647,
    1999999503089270,2000022834209735,2000024165640509,2000006263257230,1999991329619263,
    1999996997203526,2000015978537622,2000028683915875,2000026394831198,2000014633336898,
    2000003483046683,1999997577025868,1999993290243522,1999988324549644,1999988556231622,
    1999998173553446,2000009936903504,2000011944531814,2000000223707512,1999983447018531,
    1999977030520685,1999988888829798,2000009623359683,2000021288268983,2000015609056547,
    1999999804856135,1999986899567659,1999983970552446,1999987558672029,1999988443569577,
    1999982527335724,1999976394646758,1999979751492567,1999994005643398],
   [2000010878324708,2000020573014546,2000019506195870,2000012142884791,2000006820793349,
    2000007997225471,2000011703767716,2000010119263383,2000000750584780,1999989645311152,
    1999985851360981,1999993876694930,2000010306530023,2000025656306212,2000030351016693,
    2000021672919564,2000005945000923,1999993243272017,1999989600855269,1999993917958312,
    2000000829175661,2000005405216711,2000006283825693,2000006275891791,2000010046639237,
    2000019701473631,2000031794929428,2000039029249575,2000035394684921,2000020196350220,
    1999998274366296,1999977422602958,1999964981986378,1999964648329614,1999974613585294,
    1999988556530870,1999999375184104,2000003040771051,1999999893889596,1999993286714827,
    1999987398589258,1999985499204791,1999988718237330,1999995463698233,2000002168861456,
    2000005359865465,2000003674361074,1999998376868606,1999992371352394,1999988874936919,
    1999990546900617,1999998893563806,2000013665329420,2000032623212813,2000052212934315,
    2000068920307196,2000080381573651,2000085610322550,2000084581190582,2000077803075428,
    2000066120825204,2000050538617873,2000032014316032,2000011633547233],
   [1999991542255658,1999976269594031,1999973242888184,1999991159910723,2000035604187106,
    2000102453459701,2000170832349175,2000198496031750,2000123506218874,1999876375564802,
    1999405713016170,1998717318984283,1997922058582960,1997282981112858,1997248717869173,
    1998459556817687,2001715444587996,2007901365119790,2017874144148425,2032324056047350,
    2051632496765646,2075751256195886,2104128047256796,2135696621166281,2168939138007975,
    2202015735537901,2232944220977270,2259804035090984,2280934798837856,2295101385952314,
    2301603938286435,2300320999014915,2291684911097207,2276598704041817,2256311160259731,
    2232270612879419,2205978108932901,2178857450132754,2152154378117894,2126871074216484,
    2103736364919183,2083207421813211,2065495773522531,2050609173192433,2038401054525407,
    2028620551728386,2020957887426868,2015081920704636,2010668467403826,2007419452673520,
    2005073946360477,2003412675369599,2002257776782313,2001469455051870,2000940943466207,
    2000592837219812,2000367531914751,2000224210356610,2000134592689137,2000079503832908,
    2000046210778644,2000026428231378,2000014870913186,2000008232320238],
   [2000004483205145,2000002401600205,2000001265379809,2000000655708420,2000000334142655,
    2000000167435200,2000000082493372,2000000039958976,2000000019028318,2000000008907329,
    2000000004098535,2000000001853618,2000000000823946,2000000000359949,2000000000154534,
    2000000000065195,2000000000027023,2000000000011002,2000000000004395,2000000000001721,
    2000000000000656,2000000000000242,2000000000000084,2000000000000027,2000000000000006,
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
/-- Post-walk vector for `(m = 2, r = 512)` segment `3`. -/
def rkmVoPack_m2_r512_s3 : List ℤ := rkmDecOfNatsPack rkmVoNatPack_m2_r512_s3

/-- Raw `< 2 ^ 58` natural words for `rkmHbPack_m2_r512_s7`. -/
def rkmHbNatPack_m2_r512_s7 : List ℕ := rkmNatChunksPack
  [
   [76272881001025,107700602101179,131702991757313,151843351841146,169504195116479,
    185395685269553,199940349727978,213413912967195,226008187019814,237863041670906,
    249084227349649,259754025670131,269937969342744,279689271737503,289051853887666,
    298062476526242,306752280910479,315147927354629,323272452920001,331145928608998,
    338785970570903,346208143128553,353426280376005,360452745611556,367298642703099,
    373973989852041,380487863629581,386848519280779,393063491912421,399139682155149,
    405083429119065,410900572875939,416596508251333,422176231361609,427644380058695,
    433005269231258,438262921741029,443421095637296,448483308183449,453452857141183,
    458332839686096,463126169269643,467835590694006,472463693626475,477012924746709,
    481485598692493,485883907946430,490209931786411,494465644406203,498652922298520,
    502773550980978,506829231135194,510821584220568,514752157616776,518622429342564,
    522433812392852,526187658731286,529885262971218,533527865774387,537116656993379,
    540652778581168,544137327288527,547571357167978,550955881901016],
   [554291876963645,557580281643811,560822000922936,564017907232626,567168842096544,
    570275617666529,573339018161191,576359801214462,579338699140920,582276420124106,
    585173649333489,588031049975277,590849264281806,593628914443859,596370603489895,
    599074916115858,601742419468912,604373663888231,606969183605659,609529497408907,
    612055109269692,614546508939077,617004172512082,619428562963492,621820130656646,
    624179313826851,626506539040970,628802221634596,631066766128144,633300566623092,
    635504007179529,637677462176066,639821296653123,641935866640519,644021519470231,
    646078594075150,648107421274586,650108324047237,652081617792287,654027610579279,
    655946603387316,657838890334176,659704758895840,661544490116922,663358358812464,
    665146633761525,666909577892965,668647448463812,670360497230568,672048970613797,
    673713109856312,675353151175263,676969325908416,678561860654886,680130977410589,
    681676893698641,683199822694944,684699973349169,686177550501346,687632754994241,
    689065783781730,690476830033313,691866083234961,693233729286434],
   [694579950595229,695904926167300,697208831694677,698491839640122,699754119318935,
    700995836978032,702217155872406,703418236339064,704599235868566,705760309174225,
    706901608259099,708023282480825,709125478614405,710208340913007,711272011166869,
    712316628760360,713342330727286,714349251804501,715337524483867,716307279062664,
    717258643692460,718191744426530,719106705265867,720003648203825,720882693269461,
    721743958569601,722587560329697,723413612933498,724222228961582,725013519228800,
    725787592820642,726544557128597,727284517884504,728007579193960,728713843568789,
    729403411958627,730076383781631,730732856954355,731372927920814,731996691680765,
    732604241817216,733195670523219,733771068627932,734330525621995,734874129682244,
    735401967695765,735914125283329,736410686822206,736891735468398,737357353178292,
    737807620729760,738242617742711,738662422699129,739067112962596,739456764797318,
    739831453386676,740191252851308,740536236266739,740866475680565,741182042129219,
    741483005654308,741769435318558,742041399221351,742298964513893],
   [742542197414001,742771163220526,742985926327426,743186550237497,743373097575762,
    743545630102542,743704208726202,743848893515592,743979743712184,744096817741913,
    744200173226734,744289866995898,744365955096955,744428492806486,744477534640584,
    744513134365074,744535345005486,744544218856786,744539807492872,744522161775840,
    744491331865020,744447367225790,744390316638184,744320228205277,744237149361367,
    744141126879961,744032206881555,743910434841221,743775855596012,743628513352169,
    743468451692159,743295713581521,743110341375547,742912376825788,742701861086391,
    742478834720271,742243337705118,741995409439253,741735088747317,741462413885812,
    741177422548495,740880151871609,740570638438988,740248918286997,739915026909349,
    739568999261772,739210869766540,738840672316870,738458440281189,738064206507264,
    737658003326206,737239862556343,736809815506969,736367892981972,735914125283329,
    735448542214487,734971173083624,734482046706784,733981191410899,733468635036698,
    732944404941490,732408528001840,731861030616132,731301938707013],
   [730731277723730,730149072644355,729555347977898,728950127766312,728333435586389,
    727705294551542,727065727313488,726414756063816,725752402535453,725078688004013,
    724393633289055,723697258755221,722989584313270,722270629421015,721540413084137,
    720798953856912,720046269842812,719282378695018,718507297616810,717721043361861,
    716923632234418,716115080089379,715295402332256,714464613919035,713622729355926,
    712769762698998,711905727553710,711030637074327,710144503963220,709247340470065,
    708339158390913,707419969067155,706489783384366,705548611771036,704596464197178,
    703633350172817,702659278746359,701674258502837,700678297562031,699671403576465,
    698653583729274,697624844731940,696585192821899,695534633760019,694473172827932,
    693400814825235,692317564066555,691223424378460,690118399096240,689002491060528,
    687875702613777,686738035596585,685589491343865,684430070680849,683259773918940,
    682078600851393,680886550748827,679683622354573,678469813879833,677245122998673,
    676009546842821,674763081996288,673505724489787,672237469794963],
   [670958312818418,669668247895533,668367268784077,667055368657598,665732540098599,
    664398775091480,663054065015252,661698400636010,660331772099158,658954168921390,
    657565579982406,656165993516362,654755397103053,653333777658809,651901121427109,
    650457413968894,649002640152574,647536784143728,646059829394475,644571758632510,
    643072553849808,641562196290967,640040666441185,638507944013873,636964007937872,
    635408836344275,633842406552838,632264695057969,630675677514279,629075328721675,
    627463622609996,625840532223161,624206029702822,622560086271501,620902672215196,
    619233756865438,617553308580779,615861294727687,614157681660842,612442434702794,
    610715518122969,608976895116005,607226527779379,605464377090318,603690402881954,
    601904563818694,600106817370796,598297119788088,596475426072831,594641689951677,
    592795863846678,590937898845337,589067744669635,587185349644014,585290660662260,
    583383623153258,581464181045560,579532276730723,577587851025369,575630843131913,
    573661190597899,571678829273902,569683693269908,567675714910139],
   [565654824686230,563620951208706,561574021156672,559513959225647,557440688073457,
    555354128264093,553254198209458,551140814108894,549013889886395,546873337125395,
    544719065001020,542550980209692,540368986895944,538172986576328,535962878060275,
    533738557367745,531499917643526,529246849068014,526979238764287,524696970701299,
    522399925592993,520087980793124,517761010185569,515418884069885,513061469041878,
    510688627868902,508300219359609,505896098227860,503476114950456,501040115618372,
    498587941781106,496119430283771,493634413096517,491132717135820,488614164077190,
    486078570158780,483525745975349,480955496262014,478367619667152,475761908513802,
    473138148548838,470496118679150,467835590694006,465156328972704,462458090176559,
    459740622924189,457003667448984,454246955237564,451470208647919,448673140505829,
    445855453678037,443016840620529,440156982900137,437275550687510,434372202219342,
    431446583227574,428498326333034,425527050400815,422532359854385,419513843945166,
    416471075974032,413403612460773,410310992257267,407192735599610],
   [404048343094011,400877294630732,397679048219741,394453038741083,391198676602244,
    387915346293912,384602404834597,381259180093521,377884968979923,374479035485596,
    371040608565864,367568879842426,364063001109476,360522081622109,356945185143413,
    353331326723466,349679469179967,345988519246041,342257323345997,338484662954208,
    334669249485798,330809718660145,326904624269253,322952431272448,318951508126303,
    314900118243770,310796410458720,306638408350689,302423998258973,298150915784054,
    293816730536522,289418828847387,284954394096814,280420384247983,275813506085275,
    271130185546400,266366533399850,261518305343399,256580855374406,251549080992030,
    246417358412613,241179465480696,235828489294643,230356714672951,224755488370954,
    219015052278131,213124336472964,207070699661636,200839599670717,194414169486669,
    187774663492704,180897721769129,173755373612236,166313657559878,158530660517950,
    150353645937218,141714693470935,132523782426571,122657207792339,111936783844327,
    100088899775087,86652752716157,70729447546678,49997295293315]]
/-- Coupling vector for `(m = 2, r = 512)` segment `7`. -/
def rkmHbPack_m2_r512_s7 : List ℤ := rkmHbOfNatsPack rkmHbNatPack_m2_r512_s7
/-- Raw `< 2 ^ 58` natural words for `rkmViPack_m2_r512_s7`. -/
def rkmViNatPack_m2_r512_s7 : List ℕ := rkmNatChunksPack
  [
   [2000001607751179,1999912839841036,2000144285853899,2000091299803239,1999936299836083,
    1999851493403632,2000011376347336,2000133195235383,2000047649724087,1999940245085891,
    2000118533918323,2000143336926657,2000057002613079,2000062526528512,1999990008638480,
    2000080499494428,1999956741244287,2000087477740035,2000021173538688,2000053345715137,
    2000001486051623,2000116745085251,2000156561853513,2000016378666770,2000066663017651,
    1999929290981936,1999910444272490,2000068065927974,1999986025331339,1999879318056750,
    1999980357325788,1999934277744436,1999979671096637,1999832402120385,1999766024961651,
    1999995553819610,2000031596879207,1999968378514733,2000190454390130,2000071200778576,
    2000218088783405,2000058524807045,1999943448490662,2000051981423053,2000024107160433,
    1999999961653126,2000025483427746,2000095728936335,1999967442311975,2000028403944519,
    1999841372087513,1999899922996015,1999836721039198,1999984678238404,1999905068329877,
    1999890377432727,1999656220046437,2000492707150107,1999638417760744,2000323774637849,
    2000434274842299,2000098340070536,2000040048165106,2000075258586922],
   [2000066736341659,2000025209165014,2000179816117767,2000044059131571,2000018733955125,
    2000166998027553,2000436934076819,2000483460729408,1999751388116418,2000058589033489,
    1999955285658184,1999908234236475,2000044445590269,1999870430564755,1999851469943327,
    2000258782424967,2000689174622351,2000613971320612,1999578377142209,2000032254488510,
    2000182970767485,1999809448313549,1999484045097274,1999663404212672,1999767268784478,
    2000388744091407,2000254642932712,2000121941344093,2000249410624991,1999804146484247,
    2000907915050077,1999537794749302,1999702627102863,2000400358344317,1999639076829818,
    1999683139395804,1999267458193922,1999657422643955,1999902661044447,2000268047540026,
    1999729173883592,1999817920337176,2000405573409886,1999320784594387,2000377271747741,
    2000170543667773,2000101206496429,2000061019818205,1999878615619948,2000253544896211,
    2000133119316423,1999332448917610,2000106329678857,2000269909710292,2000097857118083,
    1999205115157791,1999492821947772,1999748997546661,1999748960217999,1999683759893272,
    2000190797651594,1999988707707940,1999904456972731,1999706658592708],
   [2000215185733677,1999903646515671,1999793265419826,2000092424984416,1999703527427547,
    2000369629357439,2000011634680060,1999801545088256,1999880500111246,1999954895997576,
    2000175648012502,2000065526871036,1999084800684633,1999271179429289,1999900621979369,
    1999736371628333,1999806146964523,2000611935785279,2000196604732013,1999959630713778,
    1999964737756893,1999745593382356,1999553497874287,1999608144756389,1999904542406635,
    2000315978885948,1999898726997665,1999690369730010,2000384314086456,2000057963873479,
    1999634926842167,2000439902267385,1999585475800082,1998903317561106,2000921361201960,
    1999448763324004,2000104369021724,2000737074002550,2000459907171303,1999620275349287,
    2000763129947113,1999330062446630,2000075208927997,2000813514114748,1999418829219700,
    1999697276118744,2000865192726442,1998833197836195,2000873710722911,2000518150397349,
    1999701681736481,1999533435336127,1999471135381544,1999199450279329,2000326514676014,
    2000528734453037,2000036900617623,1999144355031954,2001619850635165,2001011357667255,
    1999680910635239,2001110481559376,1998886444153601,1999647560871921],
   [2000797237221872,2000034657036794,1999830426761150,2000407296182179,1999947898302414,
    1998725777426631,2001273345170398,2000245533018519,2001534675682677,2000988583143080,
    1999757212092868,1999709065729990,2000808810816021,1999821278204167,1999313453147593,
    2000295566788606,2000198684165529,1999543245897993,2000126027269046,2001197014419595,
    1998640490739313,2001240875654975,2000211089205994,1998852408038445,1999532751989274,
    2001894998572529,1998666069886935,1999478241859198,1998814366312427,1999191627399096,
    1999733499214854,2001370939695590,1999240986738780,1998082005647255,2000844464587659,
    2001177830718725,1998433919132823,2000585727513057,1999682275169938,1999067865388894,
    1999653361527026,2000595598785526,1999988496865638,1999333042468715,2000845610102702,
    2000485616318318,1999141128039916,2000733272998852,2000219052436174,1999806634915350,
    2001055146480730,1999992483459071,1999074227631144,2000284260477937,1999944956005319,
    2000074470310516,1999699625683923,2000679360533780,2000136121984807,2000390335092964,
    2001257591361670,1998645680677961,1998996995783666,2000852214871622],
   [2000406738674017,1997095976253305,2002238031275265,2000373298542314,1999112796352861,
    1999864650408739,2001927549240589,1998369268225647,1998941935175151,2001331910586332,
    1998524128304863,2000240330184552,1999842658467351,2000917026933966,2002837310893991,
    2001126007990390,1999939093144794,2000484937927372,1999525576702143,1999911628627655,
    1999479348060691,1999312338236112,2000755807857416,1999200116504055,1998984456563971,
    2000429725646583,2000539595848205,1997846189827482,1999596769568389,2001260875790546,
    1998689144725434,1999866492000055,1999750553256607,2000815087468499,2000325835913848,
    1998833681985374,2001105761249672,1998735775934111,2000854383346038,2002767697471368,
    1997495395342559,1999040393004458,2002128660296990,2000052526044254,2000771571422361,
    2000488976126358,2000962378615541,2000565971457029,1998920714764111,2000579210622761,
    1999679582828663,1998541843899131,2001977098053046,2000874304642555,2002539792069442,
    2000197444131875,2002201947162495,1999684436526150,1998988706457467,2001328584692858,
    2001930280952391,1999541616773310,1999099098320738,2001010154056185],
   [2000076971725035,1998588102503489,2000812265324517,2001245522554003,1999088817022044,
    1999819162387377,2000981304786642,2000161359520685,1999643009161503,2000367741209194,
    2000127807889111,2000320056083333,1999803450764814,1999702069716097,1999149240647143,
    2000099175203065,1999360474008813,2000084406088360,2000151172503187,2000482376328923,
    1999522929006578,1999324723724600,1999505824904332,1999553298506476,1999763141965633,
    1998863682872705,1999947287948183,2003047044838206,1999007795661376,1999183417216531,
    2000714738339687,2002941477133960,1997860234975743,1998483403753656,2002129350051894,
    2001222877465753,1998926909339836,1999405808157179,2003929490052373,1997294555582617,
    1997759776684028,2000774036341081,2005532447015436,1996974038452892,1997093289688956,
    2004040506615711,2001484770861791,1998286955659668,1997719099426833,2004208271389455,
    1996907472528876,1994754799340712,1997408845703458,2008098398211390,1997717040397559,
    1996981382003666,2001568374072878,2003120379632312,2002740650889143,1992879539354150,
    2000800126074684,2007626049501248,1998455681006595,1991677154738338],
   [2006533019441347,2004088139417628,1993732190471353,2003354255276847,1996109142144884,
    2006927559842014,1998735801885021,1988092513280568,2005474355381443,2009416811377307,
    1993709754588680,1988524121923057,2008693178893965,2003134430655218,1995274398108788,
    2001646939686062,2004802848081704,2006005796224299,2003732585599944,1987641752993702,
    2002484178571152,2010810582305099,1995850270756639,1990394836985509,2002987942868651,
    2008224969162471,2001315517376761,1995943708829815,1996020844767004,2003314768276254,
    2011388366210152,1990491886567978,1986378272627507,2015209135627680,2006752593864970,
    1983112623475608,1997402392311315,2009586042290299,2001929562713508,1999063383216637,
    1998073170598789,1999076232476229,2006135859434234,2005841334086491,1994534901323848,
    1990312013018588,1995754681363555,2010879216446398,1992284139118501,1987521909638555,
    2008875051086840,2006910793699111,1989351668263977,2000866648689866,2008135683476740,
    1988955069883426,2003689508122627,2019455842842284,1998753919737980,1976633141467268,
    2005226767383197,2021115820165383,1990763613803174,1985390794137483],
   [2014024732986285,2007148197583182,2019660477957316,1997572976813302,2024056781330057,
    2001742571645101,1975918767802611,1998235577761276,2020333009616694,1997988020686139,
    1980134005871381,2005590002276301,2025142422998001,1999303437556782,1973529350143278,
    1991926311473134,2019136609923312,2008320990365856,1982575900634645,1989854103123991,
    2020605985514729,2027197616146286,2002811366788101,1989334457843062,2009615899665153,
    2033896598992705,2026378243860796,2002475752879153,2011286835589061,2015714111461724,
    2047783236352864,2045712154765873,2008934642321869,2022707278712938,2011014220913632,
    2041454273585259,2092904557929809,2099178511454121,2050764964420073,2019426463244994,
    2059325306399776,2031359432921348,2066756379614031,2204057993705163,2335177047331014,
    2422133638539627,2447645576631482,2416327364475155,2347082014572139,2262767941541266,
    2182138207246769,2116184957144480,2068408534251532,2037221839408544,2018707137851010,
    2008665858831465,2003685774580927,2001431056244262,2000503204501619,2000158538851706,
    2000044101533298,2000010605790217,2000002133500382,2000000338242219],
   [2000000036572994]]
/-- Input state vector for `(m = 2, r = 512)` segment `7`. -/
def rkmViPack_m2_r512_s7 : List ℤ := rkmDecOfNatsPack rkmViNatPack_m2_r512_s7
/-- Raw `< 2 ^ 58` natural words for `rkmVoPack_m2_r512_s7`. -/
def rkmVoNatPack_m2_r512_s7 : List ℕ := rkmNatChunksPack
  [
   [1999930085705918,1999954345844034,2000091485538823,2000037806683509,2000025805096268,
    1999930065583416,2000029904960829,2000044945667385,1999990180254410,2000128336472002,
    1999904305010936,2000219219756769,1999895720502743,2000130061311151,1999793804900630,
    2000314964070063,1999954167974394,1999921269896091,2000090346797388,1999881664314330,
    2000023778791647,1999906837111063,1999636339263881,2000196251776919,1999907745769798,
    1999982978994140,2000200374339004,2000182938290355,1999905596179156,2000125630526512,
    2000015623741617,2000069273776376,1999860515773795,2000015456317383,2000143724832502,
    1999616877974189,2000271053805903,2000007704241365,1999904115010474,1999924118698120,
    2000079866088835,2000152320208519,1999637844772390,2000247647621728,2000045797760958,
    1999665943175612,2000428757981915,1999487777709097,2000525630034616,2000209142189268,
    1999717897200503,2000090475955467,2000105845013692,1999883981264145,2000288705933818,
    1999857144856576,2000181686172409,2000024029247278,2000226368946508,1999783630868473,
    1999788375068111,2000432918673248,2000032228700208,1999679812923179],
   [2000106090765856,2000119326099408,1999788363314172,2000502535258325,1999729104592416,
    1999928056614383,2000488070431821,1999959549032326,1999772626390253,2000266994128377,
    2000248760815895,1999843675132835,1999657217854376,2000343767552536,2000095255441644,
    1999781928204842,2000056051607948,2000013886116996,2000085178015283,2000045317587120,
    1999916847904475,1999885273977318,2000205436129597,1999647708267148,1999994493773665,
    1999624741138256,2000202715014779,1999563268226421,2000361475047264,1999388039092964,
    2000364731247457,2000064015242822,2000208632388839,2000014726401710,2000075499435735,
    1999580206332642,2000162408927912,2000057435977764,2000643810788517,1999677237257768,
    2000351097459531,1999410970291584,1999780088515453,2000718785822815,2000384602800592,
    1999668461042850,1999692590584118,2000028373185819,2000202719459017,2000474306669019,
    1999685290396002,1999466012316283,2000089637887728,2000259770209594,1999208508188595,
    1999889947483973,2000761788222866,1998624570589650,2001189457535155,1999227691867510,
    2000021754908547,2001131998202455,1999493481207501,1999793967457796],
   [2000627615321390,2000304404417184,1999212643782582,2000716888954805,1999580015311990,
    1999832195308498,1999939532097412,2001377068882082,1999073348878765,2000460346171845,
    2000144982286360,2000969763292738,1999544036057905,2000770037352373,1999505126706840,
    1999568967195296,2000207423114001,1999692052932914,1999302733166510,2001310918279707,
    1999904207062458,1999650565051583,2001025557134171,2000251605519548,1999363790963752,
    2001135758770136,1999640372290592,1999510422112156,2000382000866786,2000226985613935,
    1999604893560191,1999226923185507,2000300431348062,1999536365120857,1999697557097789,
    2001470898533000,1999526162034522,2000089608362235,2000675752345222,1999608103152602,
    2000058280929520,2000637726235314,1999784538536524,1999519027986590,2000273440525598,
    1999834381105685,1999705396867168,1999383879173300,2000485296435566,1998067870604278,
    2001656694144423,1999565958134287,1999359516295218,2000157152592715,2000632758692541,
    1998719332095437,2000082258203606,2000883527426338,1999176710296553,2000526640736720,
    2000373719894837,2000496198864665,1998712932093883,2001209617800545],
   [2000061801393220,1998515853698760,2001164426824277,2000103459124743,1998835224572394,
    1999508946741247,2000293456575733,1999353903795653,1999904129659594,2000665495714611,
    1999378268304268,1999648603442512,2001029192717080,1998903861819200,1998741065650322,
    2000426304021853,2000666335735821,2000177504801723,1999367867442899,2001166935068635,
    1999193757016391,1999782143576975,2002007255735836,1998084642058287,1999437028349321,
    2000332056981349,1998841732555966,1999800498127955,2001123270810075,1999414251063445,
    1999795748336252,2000961613918097,1998113245557543,2000147218617502,2002189013576546,
    1997511854316882,1999713659437264,2000254187370704,2000253845339409,2000183583076890,
    2000070194394127,1999804854888220,2000153494171009,1998707448128961,2002242188705563,
    1997516571312734,2000062509088800,2001380934624220,1998200365922492,2000156212565629,
    2000100892305035,2001599632620940,2000208445744322,1998981565503941,2000350029237215,
    1998833065640847,1999860624628220,2001868917309198,2000212605618267,1999408122970053,
    2000109526640924,2000619175340608,2000281505833450,2000181584177119],
   [1998382395088021,1999963287394563,2001028515007709,1999240892273785,1998812699548723,
    2001294347079813,1999196017010060,1999181924302517,2001367956089762,2001479840727875,
    1999290014286131,2000657527675150,2000987552375350,1998841296905047,1999230707041870,
    2001078566668758,1999813999490179,1999520652511717,1999700657221904,2001073300427958,
    1999826454948984,2001393104866076,1999774773329863,2000614009822843,2000141698262766,
    2001075216668839,1999726159966988,1999074188166554,2002026278644128,1998562904441505,
    2000006881658926,1999981195579583,2001734563751343,1997931984369055,2002096011627150,
    2000811057007199,1998973870509620,1999237347913888,2001010379588538,1999732668027998,
    1997861827116505,2001663956933509,1997817712228361,2001773960495995,1998496062084191,
    2000367949080311,1997527492731651,2002319726061226,1999450412280484,1999606378788289,
    1998885819171812,2000448439980203,1999799223713565,1998192686881003,2000870348769625,
    1999980231268624,2001226982125956,1997894758892123,2002388943131665,1999131312021243,
    2000426156824354,2000953639646303,1997583357001117,2001356104847393],
   [1997888552021921,2003181173452200,1999043544148329,2001690843344902,1999105819829764,
    2000148314396868,1999727167752570,1999875080357670,1999088919458302,1998676383757985,
    2004836009220566,1995625928893056,2004583871519455,1998267502631777,1998560088108078,
    2000082777996990,1998307485532174,2002462035512761,1996354027010653,1999781116324795,
    2006590769650789,1993387901397458,2002865426164608,2003996573377648,1996538653066259,
    2001059992050322,2003714967544858,1997883136832721,1998693130803003,2000773385908373,
    2000851136413340,2001492348951475,1995854323675316,2001690866236599,2002063713311217,
    1990813362202813,2006275385709251,2002740601362097,1992048633171977,2006090254458453,
    2000336540330515,1994698379076761,2001189541315942,2000977810603373,2000956760459054,
    1998884379124353,1999039728776456,2005389690710241,1999263899677480,1994185849473539,
    2005997707864514,2003201605842749,1989051821067358,2007255028543007,2003055434512423,
    1993148772258229,2002998208342446,2005934715940092,1997246379525449,1999385249049292,
    2000077024234078,2007471143756788,1997904505265284,1991614045768382],
   [2013598830184251,1996124489450778,1992159610708420,2008967589657810,1999666815947535,
    1992799699856277,2007021882760268,2001290832596602,1998980801336723,1995654318264540,
    2001774824105495,2004177656233611,1998459294900717,1992635763875826,2010028111581354,
    1998369127655425,1996611064823909,1992750024193332,2019673548041173,1982759692749016,
    1996960491994394,2012488420053490,1998194752020792,1989294102102881,2006280232302502,
    2007723632091142,1984789291942941,2008404812599099,2003790687238560,1996692823682531,
    2004276383549084,1988533350619677,2008969895313839,2007074930076758,1981511152966862,
    2008391542217300,2013090774251683,1986636070422994,2000347165731865,2012630083697460,
    1991063058395589,1991244758309037,2011123279784623,1999620576909522,1991093340658112,
    2005479718049643,1999440794125424,1994955448258916,2009896193761890,1994298101427721,
    1994925623147923,2012922433637761,1997572770020494,1981955320507562,2019789357030485,
    2005699315702667,1982079002571924,2008067104975884,2008631662967985,1987283226995873,
    1989964033687645,2021155662272664,1984233221417544,2002537196029318],
   [2010086005786161,1993008211548074,2004982393447447,2000748071797532,2002715819891150,
    1986031057910139,2020932191157582,1998587692302415,1979274104033061,2011372399875338,
    2023093710849166,1978486863079313,1992189708822801,2020579684170473,1989563370796209,
    1991409213030363,1999910506477928,2019080249036300,1991294754561271,1985934789041636,
    2030863919949069,1982974548408017,1984004044792756,2028953627656721,1987723268401503,
    1983623845395924,2001187547631504,1998507034367705,2017257163125002,1996741491300079,
    1988307611968229,2018075511689255,1985882907877987,1974058563678674,2031120525599328,
    2020817491463378,1978864286079828,2008248296623704,2025601929427035,1993772332650062,
    1991542176059460,2011849927249676,2009958464793163,1999584616007538,1988444547612128,
    1984283314232299,2009905416891796,2026847013894201,1988452951873204,1962546244334234,
    2021973984800787,2079167037501892,2022763323515776,1937468260891483,1986189078324851,
    2127562336054833,2150880498315881,1996607651474722,1874135904063976,1999197912835745,
    2318066148937723,2569876189837524,2571628730092781,2371938166323800],
   [2146506900501216]]
/-- Post-walk vector for `(m = 2, r = 512)` segment `7`. -/
def rkmVoPack_m2_r512_s7 : List ℤ := rkmDecOfNatsPack rkmVoNatPack_m2_r512_s7

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
private theorem rkmConsInt_eq (x : ℤ) (xs : List ℤ) : rkmConsIntPack x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem rkmHbOfNats_eq : ∀ (ns : List ℕ), rkmHbOfNatsPack ns = uOfNatHb ns
  | [] => rfl
  | n :: ns => congrArg (Int.ofNat n :: ·) (rkmHbOfNats_eq ns)
private theorem rkmDecOfNats_eq : ∀ (us : List ℕ), rkmDecOfNatsPack us = bDec bZ us
  | [] => rfl
  | u :: us => by
    dsimp only [rkmDecOfNatsPack, bDec]
    rw [rkmConsInt_eq, bConsZ_eq, rkmDecOfNats_eq us]
private def pb_m2_r256_0 : List ℕ := pNatCat
  [
   [364176449985671,480818301508038,544126644563263,572429675856274,571297271827682,
    540903753559844,476081059856402,359162965678955]]
private def pv_m2_r256_0_0 : List ℕ := [3000000000000000]
private def pv_m2_r256_0_1 : List ℕ := pNatCat
  [
   [2541872454246927,2624280807644744,2474636748301350,2272163517756194,2123095279188749,
    2044436772492297,2012652604722516,2002717010478258,2000385018238184]]
private def phb_m2_r256_0 : List ℤ := uOfNatHb pb_m2_r256_0
private def pvi_m2_r256_0 : List ℤ := bDec bZ pv_m2_r256_0_0
private def pvo_m2_r256_0 : List ℤ := bDec bZ pv_m2_r256_0_1
private def pb_m2_r256_1 : List ℕ := pNatCat
  [
   [275238012319236,380304807462186,454644179434041,511897151585826,557420683808175,
    593980374366659,623215270529747,646177656713952,663574816739148,675891392145718,
    683456256221433,686480413717716,685078000784726,679276056419407,669015410769882,
    654142816715820,634392272728532,609350304333166,578393912635403,540576276282088,
    494399990635022,437309294881125,364308793279262,262582869940975]]
private def pv_m2_r256_1_0 : List ℕ := pNatCat
  [
   [2541872454246927,2624280807644744,2474636748301350,2272163517756194,2123095279188749,
    2044436772492297,2012652604722516,2002717010478258,2000385018238184]]
private def pv_m2_r256_1_1 : List ℕ := pNatCat
  [
   [2001900047873316,2008134041389294,2023901510983531,2055347289547580,2107180341119041,
    2178938372382667,2262413554500720,2342279413980815,2400466895096098,2422725120986832,
    2404167772427712,2350893933349091,2277006811568368,2198899396606589,2129803927313924,
    2076856642646931,2041166256850357,2019860744052565,2008578096691692,2003288330066492,
    2001104905016724,2000319331211467,2000076975274703,2000014611479841,2000001894049018]]
private def phb_m2_r256_1 : List ℤ := uOfNatHb pb_m2_r256_1
private def pvi_m2_r256_1 : List ℤ := bDec bZ pv_m2_r256_1_0
private def pvo_m2_r256_1 : List ℤ := bDec bZ pv_m2_r256_1_1
private def pb_m2_r256_2 : List ℕ := pNatCat
  [
   [189380053333248,265203729798820,321586341718397,367603331494789,406803951334867,
    441024540984190,471364950113760,498547289874968,523076697982057,545323340294431,
    565568276001741,584030953036434,600886609443731,616277777317754,630322165570231,
    643118225735208,654749182886391,665286019051690,674789723041382,683313014733344,
    690901685172702,697595650658392,703429790325065,708434617276694,712636819859073,
    716059700157125,718723529982475,720645839637364,721841651043595,722323664030392,
    722102402420323,721186324852178,719581903899600,717293675883781,714324262759419,
    710674366510605,706342735569617,701326101810466,695619085610113,689214065243042,
    682101005391250,674267237695490,665697183886047,656372008888549,646269187079930,
    635361959096717,623618648559280,611001796677981,597467056237739,582961762169376,
    567423059290105,550775411180145,532927224182522,513766172923586,493152562744386,
    470909619206303,446808765002739,420546303386221,391704437006231,359681420986193,
    323554328162009,281772135001403,231318518625300,164434486478197]]
private def pv_m2_r256_2_0 : List ℕ := pNatCat
  [
   [2001900047873316,2008134041389294,2023901510983531,2055347289547580,2107180341119041,
    2178938372382667,2262413554500720,2342279413980815,2400466895096098,2422725120986832,
    2404167772427712,2350893933349091,2277006811568368,2198899396606589,2129803927313924,
    2076856642646931,2041166256850357,2019860744052565,2008578096691692,2003288330066492,
    2001104905016724,2000319331211467,2000076975274703,2000014611479841,2000001894049018]]
private def pv_m2_r256_2_1 : List ℕ := pNatCat
  [
   [2000000045956594,2000000209972307,2000000658171678,2000001546789759,2000003000274649,
    2000004655589442,2000005988831686,2000005906897088,2000003950132951,2000000464868149,
    1999996891733372,1999995330636882,1999997027465523,2000001902942599,2000010335029111,
    2000028294167254,2000078367517707,2000220559948441,2000589691695844,2001458637752316,
    2003331421702656,2007052674809832,2013891950685493,2025532302606684,2043881323608519,
    2070652347740674,2106744422994342,2151564288347737,2202532677849290,2255037655298170,
    2302997383093514,2339987907153549,2360657015461259,2361993968399777,2344040168234414,
    2309812691218468,2264490718169393,2214160793489041,2164529293318796,2119959212489303,
    2083019764117878,2054539713398375,2034010033199093,2020127697366253,2011301885629069,
    2006018617772528,2003037997397676,2001452471605245,2000657146430646,2000281036998416,
    2000113453295045,2000043162014370,2000015443426260,2000005184215047,2000001627898462,
    2000000476417501,2000000129356337,2000000032398782,2000000007429900,2000000001544748,
    2000000000287215,2000000000046806,2000000000006471,2000000000000713],
   [2000000000000053]]
private def phb_m2_r256_2 : List ℤ := uOfNatHb pb_m2_r256_2
private def pvi_m2_r256_2 : List ℤ := bDec bZ pv_m2_r256_2_0
private def pvo_m2_r256_2 : List ℤ := bDec bZ pv_m2_r256_2_1
private def pb_m2_r256_3 : List ℕ := pNatCat
  [
   [142575721411584,200538358540637,244267679600742,280507295907287,311884390587840,
    339753731355568,364924411703823,387926367396583,409129597229932,428804870831181,
    447157628634108,464348273053791,480504992006051,495732225477508,510116460582867,
    523730319775334,536635520094545,548885063242031,560524888018618,571595138457704,
    582131151784470,592164238504565,601722305829630,610830361354714,619510924028154,
    627784362510327,635669176055189,643182229449700,650338950901159,657153499794222,
    663638909757951,669807211356459,675669537851225,681236216812310,686516849831241,
    691520382175093,696255163893230,700729003625886,704949216152707,708922664548444,
    712655797673806,716154683615417,719425039594956,722472258789858,725301434443333,
    727917381587517,730324656658286,732527575242131,734530228163251,736336496091618,
    737950062829456,739374427413622,740612915154239,741668687715228,742544752329608,
    743243970231446,743769064376726,744122626517052,744307123682778,744324904125763,
    744178202766270,743869146183568,743399757185353,742771958987186],
   [741987579029624,741048352457582,739955925283619,738711857254284,737317624436321,
    735774621537387,734084163973985,732247489697459,730265760787216,728140064818714,
    725871416012198,723460756166703,720908955382402,718216812572925,715385055767876,
    712414342204340,709305258204697,706058318836542,702673967348951,699152574377606,
    695494436909565,691699776996484,687768740203015,683701393774824,679497724508095,
    675157636299615,670680947353329,666067387015773,661316592208737,656428103423020,
    651401360231946,646235696277409,640930333674427,635484376772342,629896805201789,
    624166466125977,618292065602618,612272158948469,606105139981589,599789228996581,
    593322459304521,586702662141369,579927449715253,572994196123035,565900015818357,
    558641739255089,551215885259121,543618629594744,535845769085167,527892680514827,
    519754273376896,511424935323683,502898468918036,494168017953887,485225981191290,
    476063910804996,466672392133150,457040900374517,447157628634108,437009280036450,
    426580814335519,415855136287054,404812708615477,393431066093018],
   [381684198094324,369541753455771,356968001018265,343920447565204,330347964458238,
    316188191466474,301363845250186,285777309442560,269302415686720,251771398888979,
    232953037693806,212513390351267,189938452634216,164360732747680,134084874935708,
    94725044247560]]
private def pv_m2_r256_3_0 : List ℕ := pNatCat
  [
   [2000000045956594,2000000209972307,1999999341828322,1999998453210241,1999996999725351,
    1999995344410558,1999994011168314,1999994093102912,1999996049867049,1999999535131851,
    1999996891733372,1999995330636882,1999997027465523,1999998097057401,1999989664970889,
    1999971705832746,1999921632482293,2000220559948441,2000589691695844,2001458637752316,
    2003331421702656,2007052674809832,2013891950685493,2025532302606684,2043881323608519,
    2070652347740674,2106744422994342,2151564288347737,2202532677849290,2255037655298170,
    2302997383093514,2339987907153549,2360657015461259,2361993968399777,2344040168234414,
    2309812691218468,2264490718169393,2214160793489041,2164529293318796,2119959212489303,
    2083019764117878,2054539713398375,2034010033199093,2020127697366253,2011301885629069,
    2006018617772528,2003037997397676,2001452471605245,2000657146430646,2000281036998416,
    2000113453295045,2000043162014370,2000015443426260,2000005184215047,2000001627898462,
    2000000476417501,2000000129356337,2000000032398782,2000000007429900,2000000001544748,
    1999999999712785,2000000000046806,2000000000006471,2000000000000713],
   [2000000000000053]]
private def pv_m2_r256_3_1 : List ℕ := pNatCat
  [
   [1999998382038228,2000005634865632,1999985288061564,2000027026224378,1999965218669149,
    2000023330506775,2000007124336004,1999971701253222,2000012424228228,2000020969342856,
    1999980976004137,1999984850088448,2000020537868794,2000014580063861,1999980723600676,
    1999981168282382,2000013702110863,2000024566098545,1999996893011301,1999969392025334,
    1999977000413481,2000008305830166,2000026302628306,2000012681011154,1999982854536040,
    1999965190491821,1999973898335563,2000000675793608,2000025823912580,2000034115274097,
    2000022767320429,1999999254475097,1999974241277494,1999955743841991,1999947187271426,
    1999948300459671,1999956072294435,1999963716826319,1999958337725229,1999922303532663,
    1999848104197502,1999779248049084,1999886491537683,2000575906055169,2002603143543863,
    2007143702196713,2015755189771889,2030178655192304,2051968709742825,2082008290213067,
    2120030003638325,2164301416557809,2211613036303313,2257632325281930,2297577274467889,
    2327058483624074,2342879377145428,2343592909342475,2329685791650073,2303369752254131,
    2268064510891822,2227725374773311,2186183488555727,2146633290118269],
   [2111339252354814,2081567146384377,2057693834904118,2039423889781716,2026040556116705,
    2016635094598796,2010282271161640,2006152180144935,2003564653315712,2002000837885346,
    2001088324067597,2000573839007292,2000293380008926,2000145476493601,2000069981128842,
    2000032665547317,2000014798107566,2000006507397773,2000002778192661,2000001151678160,
    2000000463622469,2000000181260852,2000000068830708,2000000025387670,2000000009095804,
    2000000003165512,2000000001070119,2000000000351396,2000000000112076,2000000000034714,
    2000000000010440,2000000000003047,2000000000000859,2000000000000233,2000000000000060,
    2000000000000013,2000000000000002,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000]]
private def pv_m2_r256_3_2 : List ℕ := pNatCat
  [
   [1999975787838850,1999967888931558,1999983975730450,2000011481865212,2000023793968966,
    2000009413986930,1999985531761835,1999978985704406,1999996277435401,2000017117085548,
    2000018139972911,1999998944169610,1999981409960806,1999984627228749,2000004334813038,
    2000018761762853,2000012747441830,1999993331177560,1999981191996492,1999988639121784,
    2000007575346347,2000018704370253,2000011164078521,1999992647058184,1999981116808017,
    1999987431887752,2000005678922867,2000019303469420,2000016235031928,1999999096517956,
    1999982284948968,1999979562662651,1999993093280251,2000012399849628,2000023009626029,
    2000017294979373,1999999410682817,1999981560174946,1999975224122294,1999983816107504,
    2000001283009602,2000016669345704,2000021002905962,2000012129939188,1999995123782260,
    1999978813859062,1999970952833709,1999974708006011,1999987900218774,2000004765207292,
    2000018917060346,2000025990295707,2000024896737533,2000017337445256,2000005908886820,
    1999991820603861,1999973849000090,1999950255192406,1999924199157887,1999910218018033,
    1999935519834886,2000028002834503,2000186784333402,2000342586241925],
   [2000331701118198,1999919677886038,1998907640782146,1997327519657748,1995685867872028,
    1995166818560707,1997679242978020,2005653737244790,2021566535258718,2047270049748497,
    2083304171493762,2128406222528398,2179404982867058,2231580360101647,2279430059829539,
    2317658836381198,2342139677101166,2350610767827639,2342957560016324,2321051535447122,
    2288233358729474,2248603179290394,2206299285714929,2164913590949943,2127128815084208,
    2094592685823755,2067989360338063,2047238152029375,2031744859875420,2020644718422771,
    2012998599322701,2007926967311293,2004683687725128,2002682040641500,2001488833418802,
    2000801344028383,2000418269392381,2000211745202542,2000103975892532,2000049526770001,
    2000022884859262,2000010257846815,2000004460146038,2000001881041648,2000000769417464,
    2000000305199528,2000000117379834,2000000043762875,2000000015813225,2000000005536314,
    2000000001877465,2000000000616482,2000000000195924,2000000000060235,2000000000017901,
    2000000000005135,2000000000001419,2000000000000375,2000000000000093,2000000000000020,
    2000000000000003,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000]]
private def phb_m2_r256_3 : List ℤ := uOfNatHb pb_m2_r256_3
private def pvi_m2_r256_3 : List ℤ := bDec bZ pv_m2_r256_3_0
private def pvo_m2_r256_3 : List ℤ := bDec bZ pv_m2_r256_3_2
private def pb_m2_r256_4 : List ℕ := pNatCat
  [
   [119942894932992,168962271581073,206124163124346,237074628265992,264009834199405,
    288060631271012,309901437033052,329973377440684,348584038399008,365958226852356,
    382266298341373,397641102090275,412188683223719,425995344424025,439132476430761,
    451659963732048,463628648297894,475082151857370,486058250023647,496589926232215,
    506706192360182,516432736320506,525792439316346,534805793515106,543491242665120,
    551865462387544,559943592739367,567739432644552,575265603586904,582533688319167,
    589554349109620,596337429109670,602892039705988,609226636162717,615349083423329,
    621266713598232,626986376391632,632514483503376,637857047866189,643019718436934,
    648007811144974,652826336506157,657480024333127,661973345908231,666310533931833,
    670495600514104,674532353440957,678424410913204,682175214931392,685788043476120,
    689266021614439,692612131646413,695829222391891,698920017705364,701887124296350,
    704733038923696,707460155024347,710070768830304,712567085021552,714951221957520,
    717225216525119,719391028637341,721450545412946,723405585064608],
   [725257900520155,727009182799136,728661064164737,730215121069183,731672876909058,
    733035804605407,734305329022175,735482829235260,736569640663417,737567057071210,
    738476332453368,739298682809076,740035287814021,740687292397365,741255808230218,
    741741915131663,742146662397888,742471070059546,742716130072075,742882807443318,
    742972041302477,742984745914123,742921811640702,742784105856728,742572473817624,
    742287739485954,741930706317597,741502158010232,741002859216345,740433556222808,
    739794977598945,739087834814868,738312822831755,737470620665625,736561891926060,
    735587285331240,734547435200560,733442961926036,732274472423595,731042560565318,
    729747807593613,728390782518249,726972042497098,725492133201441,723951589166564,
    722350934128403,720690681346893,718971333916682,717193385065809,715357318442913,
    713463608393518,711512720225907,709505110467058,707441227109099,705321509846723,
    703146390305956,700916292264672,698631631865221,696292817819516,693900251606897,
    691454327665110,688955433574658,686403950236846,683800252045755],
   [681144707054413,678437677135404,675679518136138,672870580029005,670011207056614,
    667101737872331,664142505676275,661133838346984,658076058568896,654969483955820,
    651814427170559,648611196040806,645360093671497,642061418553708,638715464670270,
    635322521598192,631882874608024,628396804760279,624864588999004,621286500242617,
    617662807472111,613993775816699,610279666637023,606520737605977,602717242787262,
    598869432711724,594977554451569,591041851692524,587062564804005,583039930907379,
    578974183942363,574865554731637,570714271043722,566520557654186,562284636405235,
    558006726263727,553687043377680,549325801131311,544923210198652,540479478595795,
    535994811731808,531469412458354,526903481118071,522297215591736,517650811344258,
    512964461469534,508238356734206,503472685620345,498667634367103,493823387011357,
    488940125427384,484018029365577,479057276490259,474058042416594,469020500746638,
    463944823104546,458831179170968,453679736716651,448490661635263,443264117975486,
    438000267972361,432699272077946,427361288991271,421986475687639],
   [416574987447263,411126977883286,405642598969176,400122001065528,394565332946282,
    388972741824381,383344373376868,377680371769457,371980879680577,366246038324905,
    360475987476413,354670865490925,348830809328205,342955954573595,337046435459196,
    331102384884627,325123934437349,319111214412587,313064353832841,306983480467011,
    300868720849137,294720200296767,288538042928961,282322371683940,276073308336390,
    269790973514429,263475486716239,257126966326385,250745529631817,244331292837560,
    237884371082115,231404878452557,224892927999360,218348631750933,211772100727893,
    205163444957060,198522773485211,191850194392560,185145814806007,178409740912136,
    171642077969980,164842930323552,158012401414150,151150593792450,144257609130367,
    137333548232720,130378511048680,123392596683023,116375903407183,109328528670106,
    102250569108927,95142120559454,88003278066468,80834135893856,73634787534561,66405325720369,
    59145842431529,51856428906204,44537175649772,37188172443966,29809508355863,22401271746724,
    14963550280686,7496430933312]]
private def pv_m2_r256_4_0 : List ℕ := pNatCat
  [
   [2000024212161150,1999967888931558,2000016024269550,1999988518134788,2000023793968966,
    2000009413986930,1999985531761835,1999978985704406,1999996277435401,1999982882914452,
    1999981860027089,1999998944169610,1999981409960806,1999984627228749,2000004334813038,
    2000018761762853,1999987252558170,2000006668822440,1999981191996492,1999988639121784,
    1999992424653653,1999981295629747,1999988835921479,1999992647058184,2000018883191983,
    2000012568112248,1999994321077133,2000019303469420,2000016235031928,1999999096517956,
    2000017715051032,1999979562662651,2000006906719749,1999987600150372,2000023009626029,
    2000017294979373,1999999410682817,1999981560174946,2000024775877706,1999983816107504,
    2000001283009602,2000016669345704,1999978997094038,2000012129939188,1999995123782260,
    2000021186140938,2000029047166291,1999974708006011,1999987900218774,2000004765207292,
    2000018917060346,1999974009704293,2000024896737533,2000017337445256,2000005908886820,
    2000008179396139,2000026150999910,2000049744807594,2000075800842113,2000089781981967,
    1999935519834886,1999971997165497,1999813215666598,1999657413758075],
   [1999668298881802,2000080322113962,1998907640782146,1997327519657748,2004314132127972,
    2004833181439293,2002320757021980,2005653737244790,2021566535258718,2047270049748497,
    2083304171493762,2128406222528398,2179404982867058,2231580360101647,2279430059829539,
    2317658836381198,2342139677101166,2350610767827639,2342957560016324,2321051535447122,
    2288233358729474,2248603179290394,2206299285714929,2164913590949943,2127128815084208,
    2094592685823755,2067989360338063,2047238152029375,2031744859875420,2020644718422771,
    2012998599322701,2007926967311293,2004683687725128,2002682040641500,2001488833418802,
    2000801344028383,2000418269392381,2000211745202542,2000103975892532,2000049526770001,
    2000022884859262,1999989742153185,1999995539853962,1999998118958352,2000000769417464,
    2000000305199528,2000000117379834,2000000043762875,2000000015813225,1999999994463686,
    2000000001877465,2000000000616482,2000000000195924,2000000000060235,2000000000017901,
    1999999999994865,2000000000001419,2000000000000375,2000000000000093,2000000000000020,
    2000000000000003,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000]]
private def pv_m2_r256_4_1 : List ℕ := pNatCat
  [
   [2000035770648835,2000025991015419,2000012733332310,2000007115457300,1999992014019850,
    2000014456883112,1999998584860653,2000001143534153,1999976638725587,1999982422489859,
    2000018832936516,2000006152840414,2000000621161474,2000011021437146,2000013817522145,
    1999998061065781,2000011914661127,1999966646102082,2000009456656235,1999986480626209,
    1999991255492677,1999993192145784,2000001566176839,1999971705814118,1999976902609089,
    1999996062518514,1999981389117267,2000019870545219,1999990618463950,1999977698930115,
    2000034522236642,1999985992306291,2000002567289839,1999996621283161,1999998098130180,
    1999973326004991,1999980829573769,1999999287955886,1999980992982737,2000020961105667,
    1999964850704614,2000005391339347,2000010693257087,1999988870166927,2000114910237616,
    1999769947019166,2000441782297470,1999384821871517,2000732507253562,1999234956077465,
    2000592206316566,1999865579569739,1999640414198200,2000587943122715,1999698451325798,
    1999666644561102,2000754521513390,1999686835111384,1999354065021364,2000916142129544,
    2000077317432145,1998848021322855,2000581487596907,2001052743169556],
   [1998927095659555,1999191920965405,2001407550933138,2000670884052582,1998396297338861,
    1999239079760851,2001665963788153,2001142374949114,1998541172341526,1998273124896347,
    2000776648742966,2002197922950191,2000493877559469,1998071717308990,1998109251695170,
    2000541717100863,2002563555242009,2002003996085058,1999405706386577,1997101116270245,
    1997027051233317,1999252275626228,2002257756299198,2003966337920887,2002978488885763,
    1999147103281036,1993732642205304,1989222993471801,1988842486435101,1995986599871542,
    2013473420756031,2042767325690968,2083462704551808,2133079218229439,2187294700878414,
    2240656421189054,2287525621645136,2323022730518372,2343822290880969,2348602595287348,
    2338048716580827,2314503713952807,2281413924648671,2242678907147995,2202035146595898,
    2162606207149837,2126670318012708,2095610395269052,2069993303556709,2049738206031290,
    2034330098579271,2023026228788141,2015016735408990,2009529610562479,2005890160946541,
    2003548365812092,2002083153549929,2001190148975797,2000659916001530,2000353823212053,
    2000182706685735,2000090531408630,2000042925201955,2000019447064442],
   [2000008420132285,2000003492462065,2000001394769563,2000000540875968,2000000206128554,
    2000000078333274,2000000030100986,2000000011797987,2000000004716638,2000000001908057,
    2000000000771844,2000000000308648,2000000000120939,2000000000046169,2000000000017116,
    2000000000006152,2000000000002141,2000000000000720,2000000000000233,2000000000000070,
    2000000000000019,2000000000000004,2000000000000000,2000000000000000,2000000000000000,
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
private def pv_m2_r256_4_2 : List ℕ := pNatCat
  [
   [1999990521346788,2000013279787836,2000015479094377,2000000548647230,2000021247756836,
    2000012775018067,2000032985551563,1999994967761992,2000036971319982,2000019847017080,
    1999994613920886,1999997969403272,2000000311863489,2000014345174935,2000008741298779,
    2000009918235424,2000024504379501,1999957804624883,2000001880776061,2000007238263699,
    1999976095406239,2000003561200858,1999995459856487,1999988071334536,2000029811245258,
    1999932650314293,2000182750626478,1999697638279735,2000459426324910,1999442596523175,
    2000646981915262,1999376675657666,2000404140588573,1999906196181010,1999766498346138,
    2000422534289546,1999639469990971,2000048134267260,2000260989182609,1999597097006795,
    2000160848576084,2000196068532691,1999562231898423,2000220214356851,2000254197442138,
    1999470587751482,2000159429490296,2000455757989122,1999467445713256,1999921102362306,
    2000657771031065,1999632399235591,1999499341650949,2000686417017150,2000139895252345,
    1999149848370805,2000228463766671,2000810282060488,1999414189924933,1999276892242107,
    2000809170145968,2000565189404487,1999045882827920,1999579098997439],
   [2001084453462139,2000358830648680,1998859458492381,1999636942581755,2001192244609750,
    2000481615709939,1998813845302811,1999318311796163,2001099517118723,2000973680259326,
    1999141650509169,1998728451761508,2000450369722383,2001505408807177,2000194075782253,
    1998538210951730,1999034468991768,2000958222232061,2001569478684245,2000022407142796,
    1998413680295953,1998854424197363,2000764647360265,2001777957658359,2000697829058421,
    1998784212639355,1998175548937727,1999527025248269,2001428153744020,2001969985251464,
    2000625119501849,1998615840162150,1997701683710789,1998684437835050,2000848355104222,
    2002596429798477,2002642200574259,2000847610461092,1998231748898205,1996325445801210,
    1996351859761013,1998623844967034,2002351603746447,2005889136356548,2007306350254165,
    2005095445912246,1998830028499899,1989619944579672,1980204335209220,1974571335822473,
    1977134288239849,1991660338943558,2020238475866417,2062567189808135,2115764393052434,
    2174771267895309,2233256505165263,2284782391178685,2323933835482010,2347154942965126,
    2353148426564029,2342817284528966,2318830374085276,2284959218651095],
   [2245356351184238,2203924995226930,2163876384637904,2127505952381862,2096165262892870,
    2070375319069533,2050018680299825,2034555272997785,2023221615358391,2015189635154771,
    2009676050624914,2006004599962740,2003630375236771,2002138209444240,2001226427000445,
    2000684727927981,2000371902271576,2000196386284798,2000100767172703,2000050216880287,
    2000024297683293,2000011413212808,2000005204961812,2000002305361067,2000000992278942,
    2000000415421484,2000000169365018,2000000067342993,2000000026162523,2000000009951352,
    2000000003714269,2000000001363467,2000000000493318,2000000000176238,2000000000062243,
    2000000000021740,2000000000007507,2000000000002555,2000000000000855,2000000000000279,
    2000000000000087,2000000000000025,2000000000000005,2000000000000000,2000000000000000,
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
private def pv_m2_r256_4_3 : List ℕ := pNatCat
  [
   [2000016295895141,1999975533220360,1999995862563422,2000000336066276,1999986217679669,
    1999988446584643,2000029221543588,1999994930868573,2000012492745844,1999983940130857,
    2000042297365317,1999886764894661,2000275390735520,1999608832450434,2000527513036724,
    1999402859116661,2000586060118199,1999659717488340,2000033314440917,2000314070811534,
    1999611571197866,2000299809179842,2000014007006631,1999698986989034,2000334705986090,
    1999926237012678,1999759025420194,2000343922849095,1999951249131138,1999736134312155,
    2000303956575916,2000006787806523,1999679632781550,2000264218501726,2000128262111707,
    1999594424550479,2000133694782452,2000328105744340,1999622731909917,1999876292454066,
    2000478959982619,1999834538484594,1999561538202881,2000419302463766,2000305893134647,
    1999433550502822,1999941299849331,2000642906785404,1999826303674028,1999381298972075,
    2000379003455674,2000530442729189,1999444934311532,1999591825394188,2000690250569075,
    2000277486863730,1999204016973858,1999810740974008,2000842352674663,2000093399430337,
    1999086555930224,1999928843281375,2000930386581682,2000038036339503],
   [1999007833610796,1999898112134587,2001006305393592,2000196766447607,1998995148011543,
    1999670761643069,2000983309542269,2000505429130612,1999081796506392,1999274583366932,
    2000764530174942,2000946376949340,1999480725859115,1998838317408922,2000103201090091,
    2001204342131990,2000348392067718,1998900190287649,1999158995520267,2000739960269443,
    2001224136597471,1999876380571468,1998694632363295,1999405801185034,2000994633235899,
    2001221771395762,1999764069959093,1998597252616694,1999282620069585,2000926399615326,
    2001415821266930,2000138497813271,1998679412604493,1998801362787668,2000348881543789,
    2001521526466268,2000989714255622,1999343867223934,1998369395845443,1999103495274833,
    2000793856751359,2001739295069311,2001007044464803,1999283175967175,1998153366093524,
    1998640522262618,2000353715654658,2001882285161503,2001973007585250,2000494229908013,
    1998492840327601,1997403292852207,1998052682301870,2000140758704000,2002451129001179,
    2003568933295804,2002659474319325,1999929200404854,1996593342863008,1994383059333765,
    1994787612304138,1998319146155379,2004087170130577,2009878973321865],
   [2012789165603865,2010260388381356,2001227799497930,1986963408538920,1971258654168084,
    1959781818809668,1958734840549956,1973191128859645,2005615739214945,2055011916362622,
    2116936606485840,2184361147302770,2249112852181291,2303492185120993,2341653504663715,
    2360451599749617,2359638465983784,2341476903018826,2309964599379296,2269910082368028,
    2226077248684406,2182544796202138,2142342146446421,2107349573596041,2078401446699458,
    2055511127726542,2038139564174455,2025448196737551,2016501049021207,2010403291661536,
    2006379873015813,2003806815515021,2002210550970119,2001249305761553,2000687187059506,
    2000367878283909,2000191657739784,2000097163970966,2000047929812580,2000023003854336,
    2000010741778923,2000004880191524,2000002157289840,2000000927985975,2000000388519209,
    2000000158353224,2000000062852042,2000000024302731,2000000009158612,2000000003365647,
    2000000001206771,2000000000422448,2000000000144476,2000000000048303,2000000000015795,
    2000000000005050,2000000000001576,2000000000000477,2000000000000137,2000000000000035,
    2000000000000007,2000000000000000,2000000000000000,2000000000000000],
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
private def pv_m2_r256_4_4 : List ℕ := pNatCat
  [
   [2000027536152917,1999947366664608,2000181759512391,1999680937913208,2000544171695788,
    1999350238547681,2000451668737098,1999958228605402,1999653542713687,2000424357326550,
    1999851556332883,1999740411202964,2000357035392154,1999911693422437,1999702492674912,
    2000284478105359,2000094229067076,1999700012366763,2000123030364549,2000213573115991,
    1999737480106439,1999923663224363,2000323210671156,1999934862585906,1999712065333478,
    2000202453208169,2000232067519702,1999713514504177,1999897195286830,2000350420712224,
    1999983426599970,1999652107474870,2000163753155713,2000353619115701,1999751255599734,
    1999744309975997,2000394491483392,2000210567805156,1999548508957537,1999883752828614,
    2000504761308955,2000027331742296,1999467546349769,2000080479338988,2000574672916171,
    1999849180574312,1999425537695011,2000239120508170,2000600927790864,1999722118055877,
    1999400857435609,2000317686293185,2000601340792483,1999644416484092,1999378782399319,
    2000371782427310,2000638309497299,1999609420918907,1999306837998537,2000356910681551,
    2000730173566056,1999680812294766,1999213243862009,2000255669869082],
   [2000867281749432,1999878012908362,1999102243946801,1999985090942392,2000921129827632,
    2000190107908021,1999097254686388,1999613564821759,2000836959742022,2000602976499566,
    1999303686444893,1999191706302300,2000470676963835,2000955442031894,1999808949539263,
    1998953923267524,1999829940439395,2000992682921789,2000516307229152,1999156354184461,
    1999108379762450,2000469422060361,2001101546401319,2000012288175857,1998881561620345,
    1999446686442458,2000860277975680,2001000206329788,1999651101636435,1998797454931655,
    1999690409976089,2001045918180876,2000922597551080,1999481157274018,1998721836060471,
    1999690014377359,2001076067115186,2001025790754582,1999605323632621,1998669020032644,
    1999429412770777,2000930400953148,2001295898927102,2000073003542453,1998749419439382,
    1998912820257949,2000368174922378,2001420599936421,2000866003656834,1999328861619358,
    1998508775076289,1999300816604103,2000870010421190,2001577999972721,2000685601631130,
    1999069813031363,1998314967305454,1999165299375938,2000847686976802,2001828090410185,
    2001208428587814,1999486907313488,1998093520290790,1998195119567689],
   [1999781438986953,2001697333380819,2002509859804160,2001530632825093,1999293882882175,
    1997222323386981,1996741900401223,1998399608188657,2001478087666085,2004297539897186,
    2005052450780758,2002795868991642,1998111134445565,1993106777678729,1990624468918276,
    1992902680251976,2000251064122188,2010390858840508,2018908456114578,2020811151781880,
    2012664818089177,1994472548664131,1970481658552517,1948486941133111,1937774464315105,
    1946378166504779,1978581090981421,2033487847216544,2105088986977652,2183714647482685,
    2258343340627271,2319035468468844,2358830214010268,2374706519265708,2367539076270463,
    2341259464975243,2301587783177707,2254716922358129,2206242559616422,2160492243514939,
    2120270357950066,2086938175672814,2060702579884542,2040987159555845,2026788619100718,
    2016961450896523,2010410559945746,2006197541483327,2003580050739868,2002007399445239,
    2001092873444603,2000577810574935,2000296718994744,2000148011539754,2000071724586634,
    2000033766367867,2000015443976266,2000006862827494,2000002962957245,2000001242898527,
    2000000506577229,2000000200618242,2000000077202134,2000000028869992],
   [2000000010491853,2000000003705794,2000000001272252,2000000000424589,2000000000137754,
    2000000000043447,2000000000013317,2000000000003962,2000000000001140,2000000000000315,
    2000000000000080,2000000000000018,2000000000000002,2000000000000000,2000000000000000,
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
private def phb_m2_r256_4 : List ℤ := uOfNatHb pb_m2_r256_4
private def pvi_m2_r256_4 : List ℤ := bDec bZ pv_m2_r256_4_0
private def pvo_m2_r256_4 : List ℤ := bDec bZ pv_m2_r256_4_4
private def pb_m2_r256_5 : List ℕ := pNatCat
  [
   [107967015865419,152219733722307,185856187139956,213945112693425,238456335658066,
    260403284249249,280389836445177,298810648499561,315940674988364,331980706649138,
    347082773876179,361365337234290,374922878103285,387832224645350,400156877534506,
    411950058695283,423256916039641,434116153611646,444561260403981,454621452519553,
    464322406505425,473686837865864,482734962980192,491484871965302,499952832643769,
    508153540592024,516100326538526,523805329696828,531279643645868,538533439902842,
    545576073230405,552416171880969,559061715336793,565520101605567,571798205741297,
    577902430953260,583838753422137,589612761747769,595229691796386,600694457588436,
    606011678764977,611185705086143,616220638345671,621120352028037,625888508986931,
    630528577383995,635043845093248,639437432748555,643712305587678,647871284226292,
    651917054478180,655852176323164,659679092111748,663400134084655,667017531276118,
    670533415861737,673949829004716,677268726248230,680491982496366,683621396621458,
    686658695731580,689605539128409,692463521982511,695234178750365],
   [697918986354993,700519367149877,703036691683959,705472281283787,707827410467353,
    710103309202832,712301165024189,714422125014555,716467297667298,718437754633835,
    720334532366435,722158633663584,723911029124811,725592658521307,727204432088158,
    728747231743526,730221912239683,731629302250409,732970205398937,734245401230256,
    735455646131336,736601674202542,737684198083261,738703909734548,739661481181401,
    740557565217044,741392796071478,742167790046370,742883146118192,743539446511426,
    744137257243486,744677128642923,745159595842347,745585179247433,745954384983250,
    746267705319109,746525619073010,746728591996715,746877077142416,746971515211877,
    747012334888901,746999953155890,746934775595240,746817196676254,746647600028210,
    746426358700184,746153835408190,745830382770155,745456343529229,745032050765881,
    744557828099198,744033989877810,743460841360787,742838678888875,742167790046370,
    741448453813954,740680940712750,739865512939855,739002424495604,738091921302749,
    737134241317783,736129614634574,735078263580465,733980402805010],
   [732836239361445,731645972781041,730409795140414,729127891121881,727800438066947,
    726427606022953,725009557782945,723546448918774,722038427807457,720485635650766,
    718888206488065,717246267202318,715559937519262,713829329999643,712054550024471,
    710235695773162,708372858194490,706466120970188,704515560471073,702521245705515,
    700483238260077,698401592232104,696276354154049,694107562909276,691895249639077,
    689639437640594,687340142255332,684997370747903,682611122174621,680181387241542,
    677708148151490,675191378439594,672631042796808,670027096880859,667379487114005,
    664688150466958,661953014228256,659173995758327,656351002227425,653483930336541,
    650572666020350,647617084131144,644617048102651,641572409592523,638483008102214,
    635348670572816,632169210955355,628944429753892,625674113539649,622358034434223,
    618995949559802,615587600454106,612132712447572,608630994000104,605082135994466,
    601485810983116,597841672385016,594149353628608,590408467236829,586618603849589,
    582779331178769,578890192890258,574950707407048,570960366626783],
   [566918634546508,562824945786618,558678704005145,554479280192631,550226010836728,
    545918195944534,541555096909287,537135934206565,532659884903408,528126079961849,
    523533601316108,518881478700220,514168686199958,509394138499638,504556686790595,
    499655114303772,494688131423838,489654370336429,484552379153346,479380615452688,
    474137439161726,468821104699515,463429752283648,457961398290566,452413924541186,
    446785066362549,441072399251101,435273323933072,429385049581185,423404574902989,
    417328666762733,411153835933408,404876309495321,398491999298265,391996465780840,
    385384876285717,378651956814400,371791935916989,364798479094588,357664611681423,
    350382627638387,342943980984910,335339155658268,327557508327359,319587076968459,
    311414345635891,303023952533079,294398323751078,285517208173584,276357078895277,
    266890351162620,257084343099979,246899867689791,236289282400524,225193717147893,
    213539013534321,201229557947418,188138497266709,174091348512152,158836567735859,
    141987594046605,122892930249334,100280862660149,70864829318313]]
private def pv_m2_r256_5_0 : List ℕ := pNatCat
  [
   [1999972463847083,2000052633335392,2000181759512391,1999680937913208,2000544171695788,
    2000649761452319,2000451668737098,2000041771394598,2000346457286313,2000424357326550,
    1999851556332883,2000259588797036,2000357035392154,1999911693422437,1999702492674912,
    1999715521894641,2000094229067076,1999700012366763,2000123030364549,1999786426884009,
    1999737480106439,2000076336775637,2000323210671156,1999934862585906,2000287934666522,
    1999797546791831,2000232067519702,1999713514504177,1999897195286830,1999649579287776,
    1999983426599970,2000347892525130,1999836246844287,1999646380884299,2000248744400266,
    1999744309975997,2000394491483392,1999789432194844,2000451491042463,1999883752828614,
    2000504761308955,1999972668257704,1999467546349769,2000080479338988,2000574672916171,
    1999849180574312,2000574462304989,2000239120508170,2000600927790864,2000277881944123,
    2000599142564391,1999682313706815,2000601340792483,2000355583515908,1999378782399319,
    1999628217572690,1999361690502701,2000390579081093,1999306837998537,2000356910681551,
    2000730173566056,2000319187705234,2000786756137991,1999744330130918],
   [2000867281749432,2000121987091638,2000897756053199,2000014909057608,2000921129827632,
    1999809892091979,2000902745313612,2000386435178241,1999163040257978,1999397023500434,
    1999303686444893,1999191706302300,2000470676963835,1999044557968106,2000191050460737,
    1998953923267524,1999829940439395,2000992682921789,2000516307229152,1999156354184461,
    1999108379762450,1999530577939639,2001101546401319,2000012288175857,2001118438379655,
    2000553313557542,2000860277975680,2001000206329788,2000348898363565,2001202545068345,
    2000309590023911,2001045918180876,2000922597551080,2000518842725982,2001278163939529,
    2000309985622641,2001076067115186,2001025790754582,2000394676367379,2001330979967356,
    2000570587229223,2000930400953148,2001295898927102,2000073003542453,2001250580560618,
    2001087179742051,2000368174922378,2001420599936421,2000866003656834,2000671138380642,
    2001491224923711,2000699183395897,2000870010421190,2001577999972721,2000685601631130,
    2000930186968637,2001685032694546,2000834700624062,2000847686976802,2001828090410185,
    2001208428587814,1999486907313488,2001906479709210,2001804880432311],
   [2000218561013047,2001697333380819,2002509859804160,2001530632825093,2000706117117825,
    2002777676613019,2003258099598777,2001600391811343,2001478087666085,2004297539897186,
    2005052450780758,2002795868991642,2001888865554435,2006893222321271,2009375531081724,
    2007097319748024,1999748935877812,2010390858840508,2018908456114578,2020811151781880,
    2012664818089177,2005527451335869,2029518341447483,2051513058866889,2062225535684895,
    2053621833495221,2021418909018579,2033487847216544,2105088986977652,2183714647482685,
    2258343340627271,2319035468468844,2358830214010268,2374706519265708,2367539076270463,
    2341259464975243,2301587783177707,2254716922358129,2206242559616422,2160492243514939,
    2120270357950066,2086938175672814,2060702579884542,2040987159555845,2026788619100718,
    2016961450896523,2010410559945746,2006197541483327,2003580050739868,2002007399445239,
    2001092873444603,2000577810574935,2000296718994744,2000148011539754,2000071724586634,
    2000033766367867,2000015443976266,2000006862827494,1999997037042755,1999998757101473,
    1999999493422771,1999999799381758,1999999922797866,2000000028869992],
   [2000000010491853,2000000003705794,2000000001272252,1999999999575411,1999999999862246,
    2000000000043447,2000000000013317,2000000000003962,1999999999998860,1999999999999685,
    1999999999999920,1999999999999982,2000000000000002,2000000000000000,2000000000000000,
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
private def pv_m2_r256_5_1 : List ℕ := pNatCat
  [
   [2000327762508065,1999962112687068,1999740476193341,1999941130980378,1999971980074659,
    1999989204639697,2000537364077337,1999943735342256,1999840002695470,1999541633465719,
    1999999456280678,2000152245473471,2000608566911176,1999779854202853,2000373740193653,
    2000457837631391,2000393866008831,2000271716377756,2000305505942306,1999939318286002,
    2000521034742969,1999661546441794,2000726935005378,2000199368365669,2000230485722128,
    2000050607790912,1999993536944440,1999722823684671,2000087310034224,1999755544784347,
    2000499721983821,1999371174349012,1999807059490345,2000017487205077,1999938843271599,
    1999829298719458,1999731542578061,2000442700208947,1999355240684845,2000637098517864,
    2000488530812183,1999617838579769,2000245647850417,1999352034230042,2000696935552408,
    1999316630360197,2000344553822247,1999581355320999,2000078273647644,1999846754842709,
    2000447618928379,1999658640925206,1999424413178784,2000098388661011,2000421964035396,
    1999686163761712,2000640946562532,1999309017030580,2001028212061437,2000058385998108,
    1999406410593490,2000099363217320,2000095319365748,1999760668291817],
   [2000682576458287,1999568503599949,2000659218003389,2000048222126661,2000283125481090,
    2000730753687513,1999957031746944,2000813305587050,2000241710708862,2000718640622413,
    1999919908016383,1999023121152202,2000143717674274,1999494182465376,1999865114016369,
    1999935256385809,1999904050633595,2000507837141092,1999633241490433,2000655915390065,
    2001197188468017,1999740414190990,2000012031830181,1999813464599352,2000872234454915,
    2001847273627328,2000219006489521,2000130808084926,2000151335622527,1999781552785197,
    2000804843190614,1999943908267314,1998999553871378,1999537396948705,1998992219949669,
    1999297554549449,2000620214866453,1999632123750720,2000066586209464,2000069827582812,
    1999620691601285,1999345262361010,1999754833770639,1999759201960380,1999648109824780,
    2001025087284436,1999855734208888,2000394760358595,2001384351390227,2000292189083759,
    2000212654390984,2001634637313799,2000339264564315,2000503426863769,2001043072679962,
    2001635152819774,1999092794645539,2002066327584763,2000444552774236,2001252415034850,
    1999683155504717,2001846792488787,2001841912590610,1998212218098277],
   [2003121987448605,1999831663833102,2001309050573858,2000965136319902,1999091540506877,
    2004193216791846,1998854524939244,1999513789941738,2004753854872421,1998406537306453,
    2001935877957263,1999907863018407,2000103496820761,2006385654970222,1997618634744699,
    1997041252096086,2007525305958043,2002112758345647,1995514133005518,2001038692891257,
    2003477506073028,2002530349966686,2002380499798324,1997358431940482,1996615662729971,
    2007935587160925,2011444839753300,1995966307150327,1987148137423547,2003551020220989,
    2021160333152108,2011669303727941,1987891613619419,1984102208283772,2006937201959196,
    2028403913801131,2023301001245509,1998018809321096,1980251033657436,1989038149049080,
    2018603673677602,2046763462299827,2054291211808267,2037894565202360,2010065468360186,
    1990138771895373,1994205465214274,2028981620851752,2090852639445649,2168630459016291,
    2247894100848171,2315169443414279,2360848299330097,2380488830067770,2374657892140062,
    2347729550130506,2306200157211579,2257049055875980,2206476024973010,2159153357958749,
    2117989711296403,2084285946995851,2058105944038713,2038708896549194],
   [2024945357684607,2015563780236996,2009407720582042,2005513329342631,2003135286219799,
    2001731496949078,2000928848290122,2000483510810864,2000243566613616,2000118199636372,
    2000054930892286,2000024279705703,2000010132185098,2000003960989850,2000001437977005,
    2000000479544556,2000000144629654,2000000038416444,2000000008499029,2000000001323091,
    2000000000010222,1999999999909090,1999999999958375,1999999999988536,1999999999998412,
    2000000000000411,2000000000000424,2000000000000206,2000000000000075,2000000000000022,
    2000000000000004,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r256_5_2 : List ℕ := pNatCat
  [
   [2000121499288952,1999793705258729,2000452020876082,2000100778293436,2000392401297800,
    1999773960883916,2000146144543891,2000024313335152,2000209204094170,1999409326665560,
    2000389429669412,1999529021408701,1999747188385592,1999974613470896,2000395272596091,
    2000081485858631,2000733847039788,1999673500796930,1999705874382845,2000019571071738,
    1999590677691144,2000336318029105,1999668695446730,2000032805165312,2000261844377816,
    1999674850317372,2000830619356124,1999150426891836,2001115953621773,2000170811738767,
    2000234432360711,2000158867431108,2000622398066484,2000094952009998,1999956765842282,
    1999823057996849,2000707816433125,1999931147567021,2000795209716135,1999736983568858,
    2000726286430923,1999932691583781,1999558893532507,2000431107456034,2000435365267927,
    1999325250047820,2000567157194602,1999525344726714,1999690704083700,2000593165194858,
    1999373578656035,2000374929922785,1999676467954785,1999330131538510,2000040265938258,
    1999899121105642,2000633421148565,1999611646211908,1999743345951208,2000558838213957,
    2000040723130761,2000413965527810,1999669007733831,1999525704372695],
   [2000509932146749,1999654325632530,2000037401092558,2000104958519540,1999641501919561,
    2000353502529356,1999715704714957,1999889982353086,2000246063099675,1999061385934048,
    2000065760286681,2000576585684594,1999822036581186,2000096319230889,2000254451376390,
    1999889075449365,2000716066300172,1999386473165760,1999720225871808,2000639103674656,
    1999569738217204,2000140252296206,2000221301036266,2000251795924818,1999734690952380,
    2000152735618338,1999896224399970,2000863731914970,2001292474034721,2000300522442580,
    1999332507468544,2001216592297902,1999488304118014,2001073391716124,1999252930677747,
    1999505126202751,1998539175857814,2000957121142198,2000141481848435,1999793581287997,
    2001595773021825,1997799071761756,2001170243180132,1999905908265754,2000771253864491,
    2000542218887364,1999435174946773,2002425083728106,1998517610208912,2000949086118300,
    2002895186803806,1997482771750052,2002682493986113,1999110948534762,1998723220852271,
    2000984769957766,1997075727765110,2002045523301935,1999445016618273,1997567928020663,
    2003373660818120,1998296433670074,1998185072138142,2002078157812077],
   [1997941887717675,1999842138579057,2000906316722486,1997896201121510,2002124698615390,
    2001102484573304,1996871547072378,2002888643358305,2003028297005005,1996330899853855,
    2001108388478855,2005049332242861,1998199899604494,1998025570956904,2003974499790107,
    2001912292961130,1998504510084153,2000626948390006,2001586286346782,2001272007093202,
    2001942013857428,1999580882100994,1998230760984735,2003439696268184,2004840087277775,
    1996896436616481,1995509999443208,2006115520342680,2008307728514333,1995470376470256,
    1991177733686076,2005332113686470,2013257665313813,1999662366086907,1987275186708841,
    1998018900920844,2015103816129886,2010512324380213,1990506304188452,1985631796536701,
    2003733056299835,2018875090045788,2009545506876348,1988314147304942,1983482042496519,
    2001620003890352,2020488836823855,2017519005706569,1996073200034786,1980091983916005,
    1987130483783108,2010762459543384,2028454460996504,2023688293596522,2000255728221311,
    1977766074395984,1975057589781830,1996165825967943,2028435569608436,2051905179944959,
    2052092175252214,2028134732928924,1992755646490130,1965616451719855],
   [1964427052506582,1998074827650834,2064097344014652,2150525825272526,2240511583956779,
    2317587679021413,2369772909288999,2391583485041710,2383924456890308,2352466422746390,
    2305358923359722,2251047473304067,2196686586907696,2147322551281103,2105764697297231,
    2072923904994540,2048369773584695,2030906424579982,2019045640699176,2011330120323371,
    2006511807125483,2003617707630862,2001943328545798,2001009285244063,2000506590246856,
    2000245551917438,2000114817173784,2000051721892838,2000022413051009,2000009328314792,
    2000003722951119,2000001422554390,2000000519616737,2000000181170791,2000000060209160,
    2000000019045861,2000000005726763,2000000001634599,2000000000442344,2000000000113363,
    2000000000027490,2000000000006304,2000000000001365,2000000000000277,2000000000000050,
    2000000000000007,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r256_5_3 : List ℕ := pNatCat
  [
   [2000596911875707,1999812190566269,2000426417620321,1999568013259578,2000248755224009,
    1999907251672033,1999947966174570,1999673140099391,2000158026281024,2000781024736322,
    1999806598267541,1999835669553842,2000852946121800,1999234599598233,2000928628971685,
    1999506930304850,2000249054473820,2000141998216619,1999886794447655,1999871835179955,
    2000660396927064,1999404758886573,2000250777460121,1999398022005313,1999917325824212,
    1999478888989926,1999993081976845,2000568112829644,2000383554538240,1999647269522144,
    2000440084232355,2000291946506894,1999580975279085,2000558822067090,1999207919924889,
    1999674758939395,2001004191146384,1999238613047372,1999781499485924,2000286313994246,
    1999801776329635,2000258956764098,1999764892692764,2000010930872590,2000360939787330,
    1999845084440516,2000596440159587,2000235525413364,2000143226511060,2000904650920314,
    1999845052324872,1999839391595770,2000428209733205,1999737571320379,2000519606860087,
    2000258483972047,2000132423947489,2000639826288274,2000152443794843,1999575156280413,
    2000554740818855,2000227941224371,2000231488125441,2000648761799957],
   [1998852607237296,2000202508533948,2000414217651791,2000023042527348,1999927532231584,
    2000126728262990,1999435425874422,2000368887627975,1999431795474991,2000352526016680,
    1999228638192591,2000628500167056,1998577983169779,2000812711217440,2000386347477305,
    1999471424928485,2000413703000443,1999609627946350,2001077448712583,1998962463275817,
    2001112701631997,1998755566128784,2000117388209527,2001242939661822,1998162706432383,
    2001302383074621,1999891991557241,1999303561174198,2001087706569027,1998040792194209,
    2001612909205987,1998786155089999,1999876075666626,2001209107239227,1997327550642468,
    2003174633787178,1999733566857464,1998019027197027,2002419591701903,1997811456041234,
    2000685597139007,2001732459610162,1998302640858456,2001148128900474,1998592558469367,
    1999623091380102,2002649853094225,1997852600305276,2000368800083748,2001897626419153,
    1997652289732030,2002015672736774,2002518386978939,1998154630129804,2001133863102191,
    2000394742166592,1998096889723491,2001330881688432,1999704737715163,1998715023765517,
    2002051805140997,1998828963624959,1997944722303395,2003116015066863],
   [1999963567594483,1997035703309821,2002787256546219,2001510629165001,1996470541527459,
    2001360516627314,2003831052248152,1998474741794441,1999552604655901,2003483624527342,
    2000047966532044,1997775694048744,2000613240212097,2000550712493630,1998930219300884,
    1999802115592389,1999771657887197,1999641548910585,2001190226044836,1999520045032315,
    1996898518293141,2000566992838155,2003278605257144,1997465465222716,1995351017094510,
    2003408755082990,2005069194612452,1995591414475785,1995001625048051,2006275906067388,
    2006610695420513,1994149537695920,1993915716783536,2007725963660156,2008800524021802,
    1993949639969548,1991173986718610,2006730184735484,2012387181029833,1997168444936151,
    1987853863037148,2001314563450008,2014620893351577,2004775828016856,1987945153645410,
    1992124143083102,2010961263119217,2014427331442063,1996714363116079,1984833215021704,
    1996924423484488,2015496118805413,2013783208142408,1994068356555762,1983599877616993,
    1996740028425160,2016327858852887,2016995293925442,1997512498174251,1981492114945638,
    1988291197616825,2010640496296371,2023722142488069,2012886774062532],
   [1988862696946426,1976027369447419,1987933169735949,2014682094122757,2032568030461680,
    2025253289617116,1997417604855195,1970630411540586,1966491707570933,1990785187908267,
    2029619523439424,2058818371903667,2059184988460863,2027900992123447,1980145418561850,
    1941339462861060,1935158402266510,1973533788059209,2052707778998228,2155895361714405,
    2260233848071263,2344544156879266,2394990812554209,2407266363084793,2385526874841951,
    2339327759128614,2280060729265782,2218048954299381,2160856177874162,2112811074207551,
    2075407620569067,2048139774187249,2029397153023700,2017193014207377,2009639282680624,
    2005183983753642,2002675322998718,2001325079664803,2000629820679518,2000287183038325,
    2000125554961200,2000052592632888,2000021088203320,2000008085720533,2000002961032834,
    2000001034281221,2000000344093975,2000000108861821,2000000032695737,2000000009304885,
    2000000002504026,2000000000635730,2000000000151869,2000000000034031,2000000000007122,
    2000000000001383,2000000000000244,2000000000000038,2000000000000003,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m2_r256_5_4 : List ℕ := pNatCat
  [
   [2000791555647804,2000224527221480,2000078868771506,2000036593143894,2000688342167259,
    1999208322750832,2001221500098547,1999926273336065,1999510970024785,1999775522217202,
    2000911656183388,1999516622049905,2000399539332855,1999881162279591,1999533720458799,
    1999838066075318,2000148963243188,2000075839029425,1999925511915154,2000309657069566,
    1999885317476221,2000338257165274,2000434846497492,1999242460732476,2000572833990302,
    2000711363020230,1999218906664223,2000335025262303,2000565087129334,1999421983431202,
    2000277296458532,2000157054505627,1999617316443097,2000349955642539,2000382601626408,
    2000194082216273,2000052775694579,1998928173425658,2000032088646332,2000214582751309,
    1999422409606390,1999855523014101,2000048835918255,1999874415116626,2000325979863738,
    2000767207909828,1999375224780699,2000617315397251,1999860687313130,1999981575981443,
    2000197039125133,2000049225484221,1999099808951479,2001071826282658,1999081945080580,
    2000376449054344,1999556312742906,2000290413307892,1999836453671523,1999895733538368,
    2000602704114894,1998526854572122,2001342097183377,1999348004275666],
   [2000516931162499,2000147241616026,2000158959869382,2001137053406850,1999578744729991,
    2000791364557667,1999115724003299,1999702116869292,2002321681042978,1998091515084291,
    2001549936367421,2000147049842359,1998755968644607,2002065200101407,1998584873113519,
    2001556346292501,2000359690979458,1998829473056741,2001841638806825,1998045896504007,
    2001405600979202,2001123466080703,1997147763937091,2002377195344811,1999584599623048,
    1998699337318704,2002414055762555,1998041751183158,1999877933919917,2001419033645394,
    1998059058401168,2000736811639930,1999743629359954,1998998434797817,2001701369020956,
    1998399228932509,1999804271070378,2002468742897869,1998032344117518,2000071121113713,
    2001859870439830,1997605222231206,2000578487058387,2001940546096956,1997768361435004,
    2000187845559206,2001231039126735,1998824670645447,2001187779357508,2000192114832580,
    1997641666236140,2000928549259113,2000409067728437,1998484656852523,2001986253664031,
    2000181778237427,1996885582762581,2001860045440268,2002128891266550,1997123288834108,
    2000499291683174,2002598580081862,1997387290187094,1999075102172880],
   [2003446725866209,1999237487238772,1997365568934674,2001583838116501,2000588375472551,
    1998126728842737,2001157981116057,2002136449458888,1999616292226499,2000035366018671,
    2000911476731639,1999958298953610,2000435334470971,2000296770373010,1998737215590313,
    2000254078779473,2001386418801021,1998168657672798,1998561049064104,2003260573465274,
    2000880227095876,1995586875969284,2000150030434915,2005018527269587,1998378513899015,
    1995091665318035,2004338800691317,2006591383846134,1995967292342035,1995207825911130,
    2006408863523141,2004876774139979,1992490209255982,1995351953490368,2008266155913190,
    2004183573095766,1990699761685158,1995504360620679,2009494214661847,2004254022764187,
    1989311988638839,1994067032438308,2009908516844796,2006382692027382,1989834901200653,
    1991680456764231,2009242243455573,2010559831582401,1993178144235984,1988532634515688,
    2005335574716918,2014272689194640,1999669466494926,1986504071619524,1997386540053953,
    2014490873347663,2009570540751750,1990294285594666,1987461323087787,2005855335059225,
    2017163384425619,2003955828971310,1985808985184338,1989598261198482],
   [2010157977171470,2018259033019564,2002194927252515,1983700809295600,1987990487897380,
    2010182699511864,2021978405908794,2007904250868587,1984450018890033,1979824227132273,
    2000479859287926,2023750941310893,2023395310122910,1998307460227619,1973779171556267,
    1975560017251185,2004113809410907,2033900523945745,2036931552667898,2008005243915148,
    1969639969628380,1953800825908692,1976485708797740,2025134449527881,2067228196001649,
    2072519774083721,2033030259489794,1968421820671328,1915048033620068,1906758152432408,
    1958750435887274,2062082952717134,2189566722432487,2308166919721455,2391244095740545,
    2425772545891491,2413125449775140,2365001549795927,2297416756114709,2225394887630162,
    2159791690793398,2106412544088582,2066765927778682,2039551842813378,2022154828075387,
    2011745329436509,2005896033094503,2002802669222653,2001261092659237,2000536736500652,
    2000215832477377,2000081871788231,2000029237175076,2000009804336238,2000003077646008,
    2000000900853519,2000000244702703,2000000061313241,2000000014062035,2000000002922140,
    2000000000542552,2000000000088190,2000000000012143,2000000000001330],
   [2000000000000098]]
private def phb_m2_r256_5 : List ℤ := uOfNatHb pb_m2_r256_5
private def pvi_m2_r256_5 : List ℤ := bDec bZ pv_m2_r256_5_0
private def pvo_m2_r256_5 : List ℤ := bDec bZ pv_m2_r256_5_4
private def pb_m2_r256_6 : List ℕ := pNatCat
  [
   [107118090860533,151022857647164,184394833750579,212262901192229,236581396869669,
    258355780596567,278185182168440,296461154728671,313456490935409,329370402745162,
    344353725164896,358523987325540,371974927717008,384782770415622,397010516801155,
    408710970323826,419928923905777,430702777268216,441065756085969,451046846741040,
    460671523890474,469962324430661,478939305783208,487620415825711,496021794469816,
    504158021743309,512042323557557,519686743677684,527102288455835,534299049432418,
    541286307815290,548072624014484,554665914771041,561073519923464,567302260468458,
    573358489268032,579248135513245,584976743861794,590549509011245,595971306343997,
    601246719177711,606380063071149,611375407566390,616236595691404,620967261499532,
    625570845882890,630050610863541,634409652538376,638650912830031,642777190176191,
    646791149272576,650695329970353,654492155416266,658183939513055,661772893768462,
    665261133593178,668650684101112,671943485459359,675141397829976,678246205941090,
    681259623320841,684183296224117,687018807278948,689767678876662],
   [692431376327503,695011310801246,697508842070456,699925281072332,702261892303562,
    704519896061305,706700470542163,708804753809960,710833845642183,712788809264048,
    714670672978390,716480431698872,718219048393375,719887455443840,721486555928341,
    723017224830679,724480310182361,725876634141459,727206994012461,728472163210936,
    729672892176521,730809909237484,731883921429856,732895615273931,733845657510694,
    734734695800576,735563359386743,736332259724994,737041991082157,737693131104790,
    738286241359816,738821867848650,739300541496253,739722778616444,740089081354725,
    740399938109781,740655823934754,740857200919283,741004518553295,741098214073396,
    741138712792726,741126428415028,741061763333681,740945108916345,740776845775893,
    740557344028183,740286963537257,739966054148473,739594955910056,739173999283520,
    738703505343397,738183785966649,737615144012152,736997873490575,736332259724994,
    735618579502515,734857101217203,734048085004548,733191782867725,732288438795840,
    731338288874380,730341561388023,729298476915997,728209248420100],
   [727074081325551,725893173594742,724666715794022,723394891153589,722077875620542,
    720715837905171,719308939520509,717857334815176,716361170999524,714820588165085,
    713235719297293,711606690281456,709933619901928,708216619834412,706455794631324,
    704651241700116,702803051274447,700911306378074,698976082781326,696997448949973,
    694975465986334,692910187562396,690801659844735,688649921410983,686455003157573,
    684216928198468,681935711754543,679611361033290,677243875098444,674833244729138,
    672379452268131,669882471458640,667342267269249,664758795706339,662132003613441,
    659461828456854,656748198096834,653991030543588,651190233697273,648345705071102,
    645457331496626,642524988810149,639548541519195,636527842447806,633462732359405,
    630353039555816,627198579450934,623999154117422,620754551804650,617464546425984,
    614128897013316,610747347136607,607319624285970,603845439213638,600324485232907,
    596756437470895,593140952071666,589477665345950,585766192863345,582006128482484,
    578197043314252,574338484612609,570429974587101,566471009130486],
   [562461056454305,558399555624429,554285914987819,550119510480802,545899683808110,
    541625740480755,537296947699507,532912532069202,528471677127455,523973520669382,
    519417151847790,514801608025737,510125871355575,505388865055259,500589449348997,
    495726417034966,490798488637847,485804307098150,480742431943608,475611332880105,
    470409382730504,465134849639046,459785888446455,454360531126043,448856676153583,
    443272076662829,437604327213656,431850848969911,426008873048086,420075421754344,
    414047287374493,407921008116682,401692840726999,395358729199618,388914268880604,
    382354665110930,375674685360595,368868603559557,361930135015933,354852359904477,
    347627632777266,340247474849221,332702444880688,324981983227140,317074221920070,
    308965751287224,300641330319038,292083523287015,283272238305695,274184133457535,
    264791840882896,255062935677787,244958538945037,234431382757670,223423059916167,
    211859995116938,199647326540035,186659198487993,172722499908700,157587664698571,
    140871171424348,121926645494902,99492372479687,70307632056788]]
private def pv_m2_r256_6_0 : List ℕ := pNatCat
  [
   [1999208444352196,1999775472778520,2000078868771506,1999963406856106,2000688342167259,
    1999208322750832,1998778499901453,1999926273336065,2000489029975215,1999775522217202,
    2000911656183388,2000483377950095,2000399539332855,2000118837720409,1999533720458799,
    1999838066075318,1999851036756812,2000075839029425,2000074488084846,2000309657069566,
    2000114682523779,2000338257165274,2000434846497492,1999242460732476,2000572833990302,
    2000711363020230,2000781093335777,1999664974737697,1999434912870666,1999421983431202,
    1999722703541468,2000157054505627,2000382683556903,2000349955642539,1999617398373592,
    1999805917783727,2000052775694579,1998928173425658,2000032088646332,1999785417248691,
    2000577590393610,1999855523014101,2000048835918255,1999874415116626,2000325979863738,
    1999232792090172,1999375224780699,2000617315397251,2000139312686870,2000018424018557,
    1999802960874867,2000049225484221,2000900191048521,2001071826282658,2000918054919420,
    1999623550945656,1999556312742906,2000290413307892,2000163546328477,1999895733538368,
    1999397295885106,1998526854572122,2001342097183377,2000651995724334],
   [1999483068837501,1999852758383974,2000158959869382,2001137053406850,1999578744729991,
    1999208635442333,1999115724003299,1999702116869292,2002321681042978,2001908484915709,
    2001549936367421,2000147049842359,1998755968644607,2002065200101407,2001415126886481,
    2001556346292501,1999640309020542,1998829473056741,2001841638806825,2001954103495993,
    2001405600979202,1998876533919297,1997147763937091,2002377195344811,1999584599623048,
    1998699337318704,1997585944237445,1998041751183158,2000122066080083,2001419033645394,
    1998059058401168,1999263188360070,1999743629359954,2001001565202183,2001701369020956,
    1998399228932509,2000195728929622,2002468742897869,2001967655882482,1999928878886287,
    2001859870439830,2002394777768794,2000578487058387,2001940546096956,1997768361435004,
    2000187845559206,1998768960873265,2001175329354553,2001187779357508,2000192114832580,
    1997641666236140,1999071450740887,2000409067728437,2001515343147477,2001986253664031,
    2000181778237427,1996885582762581,2001860045440268,2002128891266550,1997123288834108,
    1999500708316826,1997401419918138,1997387290187094,1999075102172880],
   [2003446725866209,2000762512761228,2002634431065326,2001583838116501,2000588375472551,
    1998126728842737,1998842018883943,2002136449458888,2000383707773501,2000035366018671,
    1999088523268361,2000041701046390,1999564665529029,2000296770373010,1998737215590313,
    1999745921220527,2001386418801021,1998168657672798,1998561049064104,2003260573465274,
    1999119772904124,1995586875969284,1999849969565085,2005018527269587,1998378513899015,
    1995091665318035,2004338800691317,2006591383846134,1995967292342035,1995207825911130,
    2006408863523141,2004876774139979,2007509790744018,1995351953490368,2008266155913190,
    2004183573095766,1990699761685158,1995504360620679,2009494214661847,2004254022764187,
    1989311988638839,1994067032438308,1990091483155204,2006382692027382,1989834901200653,
    1991680456764231,2009242243455573,2010559831582401,1993178144235984,1988532634515688,
    2005335574716918,2014272689194640,2000330533505074,2013495928380476,2002613459946047,
    2014490873347663,2009570540751750,2009705714405334,2012538676912213,2005855335059225,
    2017163384425619,2003955828971310,2014191014815662,2010401738801518],
   [2010157977171470,2018259033019564,2002194927252515,2016299190704400,2012009512102620,
    2010182699511864,2021978405908794,2007904250868587,2015549981109967,2020175772867727,
    1999520140712074,2023750941310893,2023395310122910,2001692539772381,2026220828443733,
    2024439982748815,2004113809410907,2033900523945745,2036931552667898,2008005243915148,
    2030360030371620,2046199174091308,2023514291202260,2025134449527881,2067228196001649,
    2072519774083721,2033030259489794,2031578179328672,2084951966379932,2093241847567592,
    2041249564112726,2062082952717134,2189566722432487,2308166919721455,2391244095740545,
    2425772545891491,2413125449775140,2365001549795927,2297416756114709,2225394887630162,
    2159791690793398,2106412544088582,2066765927778682,2039551842813378,2022154828075387,
    2011745329436509,2005896033094503,2002802669222653,2001261092659237,2000536736500652,
    2000215832477377,2000081871788231,2000029237175076,2000009804336238,2000003077646008,
    1999999099146481,2000000244702703,2000000061313241,2000000014062035,1999999997077860,
    1999999999457448,2000000000088190,2000000000012143,2000000000001330],
   [2000000000000098]]
private def pv_m2_r256_6_1 : List ℕ := pNatCat
  [
   [2000187974920384,1999373578828693,1999564872567643,1999513812373159,2000330563804747,
    1999630141730367,1998854347594011,1999899419236671,2000468148226706,2000567852585585,
    2000341462362615,1999731293922800,1999958045666206,1999027628313003,1999951851834717,
    1999518205193111,1999413015071778,1999885606557989,2000101382767622,2000187534256077,
    2000368096355051,2000724669918296,2000795909076492,1999708653265566,2000367172238935,
    1999539185650270,2000585026361583,1999740398902018,1999407272234328,1999670520833888,
    2000394869558290,2000405760109584,2000131622695960,2000471326286211,1999666578192481,
    1999594208432686,2000165760437956,2000130957298893,2001089268642805,2000764860242435,
    1999975619228434,1999816973318426,2000138912077993,1999589416459652,1999645318824906,
    1999199280840086,2000773004813723,2000374251972443,1999625747646496,2000641571865159,
    1999323036224323,1999986082555159,2000173292547826,1998958668090579,1999740415491119,
    1999792951853426,2000326209845431,2000610607304501,1999582929849066,2000592669282377,
    1998379508413458,2000119714739263,2001230532323130,1999695537340731],
   [1999704147741841,1998661731726149,1999616637915123,2001869841447530,1999164886029663,
    2001160586497677,1999167248080670,2001130251386058,2001227673907297,2000144358053136,
    2000221104104079,1999921119419782,1998682015754219,2001225184204229,2000406746959124,
    1998504006946483,2000321343426037,1998364595605108,2000466380410594,2002518475030835,
    2001036732481216,1999304755870886,1996990296056155,1999617828687532,2000557828297745,
    2003076041423663,1997672770572782,2000208717540636,2000607550382729,2001830517745886,
    2002606587493047,2000184076868763,1998116141114586,2001265074475480,2002597925879882,
    2001206688852895,1999004760467153,2000197856456963,2001928965787751,2001766225253819,
    2000499704857798,1998171026710761,2002089062589763,1998120513205374,1999687460839811,
    1999208345653385,1998160964927472,1998507737215460,2001365959332564,1998086179840128,
    1998563472131482,2001434594712200,1998357039329034,2000561775207348,2001245967669685,
    1999789386130497,1997778696138258,2001911808416425,2004122871880855,2002411074165927,
    2000389288761886,2000066441915921,1999932937267322,2000869462907217],
   [2002324482136799,2000885942830403,1997216896031619,2000162467122593,2000312791979822,
    1999841861172777,2000355185863972,1999123260852078,1999855165133793,2000657377950082,
    2001134512911274,1999374605930200,2004917955328314,1997999643434186,1998750821325699,
    1992754881472495,2004081125287342,1996825368778244,1997374751498095,2007390838033039,
    1999463287178002,1998290128208166,1999383925421903,2006534884808794,1996714687683308,
    2000470062293129,1995494497063264,2010511754809451,1996483533929561,1991173191308937,
    2007971154911007,2002490953850512,1992965559184153,1999989349159580,2001183348076724,
    2006423176679740,1990771651650196,2002484000616344,1998666384981999,2004038367104068,
    1991660527831799,1998632280866996,2017610466808819,1990396343456174,1991472407057543,
    1999601226338784,2013955652599848,1998446345376322,1997073436693167,2012138146816626,
    1999317689052046,2002573750305086,1993091707180158,2007268828915927,2010999357088420,
    1993648239986562,1996692383648962,1987906759025842,1995715367009065,2005074728241629,
    1989905058073980,2004165764190344,1996496045909996,1992451251605201],
   [2007358323467399,1992796427105041,2005217384956309,2013039607782414,1993437521034605,
    2015408483293731,2017122719635623,1995507997902440,2021630347918729,2012082475702692,
    1997114574763936,2022512266120402,2014800384573003,1999740410051359,2020507211169403,
    2013629239299573,1998093200443792,2020812087366874,2025590650320975,2000087087452940,
    2009842328258056,2030566084198000,2013484524327863,1992776075505346,2034698735218293,
    2032023042704900,1983575382512160,2015628714699111,2059600366025374,2020292263553683,
    1989682640267170,2030654883904602,2060203864010219,2031347000470489,2009402373016145,
    2043129123228751,2089898365696566,2087516652395962,2036467039091965,1994095434704481,
    2015069967544865,2109156404670722,2242415554995103,2364744438565364,2437548318808216,
    2447039491318933,2402394502285530,2325424841680717,2239338621077657,2161326729885262,
    2100161400396091,2057449885674228,2030490168087997,2014977942823272,2006803585524528,
    2002852656134138,2001101185076363,2000389191245224,2000124548231626,2000035494843737,
    2000008832288863,2000001876866028,2000000330495484,2000000045613621],
   [2000000004279234]]
private def pv_m2_r256_6_2 : List ℕ := pNatCat
  [
   [2000417154174130,2000233317923135,1999905920914493,2000077285512215,2000611916594345,
    1999393845653831,1999623553968643,1999268817664851,1999546536761656,2000348790649347,
    2000353173516950,1999489817545227,1999922685390057,1999013179189470,1999859287877994,
    1999112474923366,1999860518951598,2000574710445145,2000263618147419,2000296147579996,
    2000158535390814,2000196220196068,2000017402285311,1999702517586612,1999969772011706,
    1999203142222301,1999740835178707,1999982605579345,1999543385824174,1998920232213894,
    2000030575259946,2000018826531787,2000321049644181,2000837615510857,1999774203341153,
    2000547160334066,2000299586426563,2000125433415700,2000948587002380,1999740545730732,
    1999727221282019,2000815703952819,1998596277862655,1999829582531503,1999895368945772,
    2000560986186023,2000838254324389,1999621104788167,1999986430777429,2000247566048523,
    1998593316480809,2001712581254176,1998757344671639,2000521838961271,2000880473490226,
    2000489229188366,2000849129986913,1999928314692746,1999629108129605,2000314884022025,
    1999345814138271,1999473840456830,2001082147026651,1998920418354727],
   [2000169333360470,2000505260671933,1999252570600776,2002446795689034,1998601554740395,
    1999144871842151,1998657664718518,2001385368714859,1999238724543863,2001035178903282,
    1999462014741903,1998606450330339,2000647575661076,2000432104330646,2000020993387195,
    2000584291585835,1998775908379637,1999828614201489,2000657897341311,1998994231644350,
    2000635344001346,1999343016671107,1999817826244458,1998205017199513,2003182005062552,
    2000689450297561,2000157213080031,1999235319075315,1999224911860538,2001676018862531,
    2002513383678837,2000213583006824,1997743912023761,1998278592386787,1998438528446134,
    2004092364868326,2000630845775077,1997184845710907,2000404782200771,2001744651515567,
    1999917043161036,1999861501588934,1998671578811247,1998374748613982,2001051849072663,
    2001676683352062,1998569072233958,2000449333572184,2001521511119021,2001065676990218,
    2000056348719250,2001033198296578,2001656062497576,1998366124774771,2002357003879203,
    2000843369490317,2001014969266076,1998349388782700,2005125806209121,1998166138881892,
    2003259689446714,1997503403644530,1999899774700776,2000851823745727],
   [1998817860826674,2001808434765502,1993278173566259,2002282636418372,1997266337273273,
    2003082048378429,1998995132201780,1999504610905865,1993211664692178,2006162788723667,
    1998953973010386,1997480100496750,2006012147878687,1999468312573429,1999200303591812,
    2003634873464717,1999003903656017,2008306258556164,1990796719122421,2005271706489592,
    2001965302105400,1997871665688784,1998102070825813,2004640601658500,2001434003889464,
    1986119896133612,2009743281746779,2000878708234294,2002049052630954,1997804695422268,
    2001281911006250,2005923310713709,1989553402820287,1998793607115098,2001323734624266,
    2005126791095988,1989220822452395,2002494462255721,2012291816922665,1988345492034770,
    2000980704955943,2007289583194937,1999879770501823,1995887496379957,1996243925674986,
    2015052713462240,1992794274557232,1990413225351194,2008151669679321,1999336710193952,
    2005056592017775,1993574533208269,1996412360797534,2008664572036858,1989368252815754,
    2002232838648494,2009211978250686,1991855776828962,2005052429421865,1988936173633379,
    1996873611338073,2018629903578788,1992571286682550,1999872618571271],
   [2008791752326434,1989281810832257,2011058012411463,2013268723431248,1992006411066566,
    2005756182502355,2000954637582124,1984920931148566,2006650919123406,1997897136766229,
    1988153244000176,2001553160425872,2002279204223698,1985891019446873,2001199767547759,
    2011243672722089,1983939222159018,2008043174358940,2028369873195802,1987604695336417,
    2003677072588143,2035821474071142,1996884808976071,1997811773560311,2038332306189777,
    2008682443252420,1984785970406176,2029034802116090,2033434845321471,1989310691847477,
    2001755728093892,2042123852976122,2022678259946452,1989186475652369,2011491706310511,
    2040731602217274,2019619189221696,1993948464402251,2017464173754284,2051972264758556,
    2037625834756465,1995425339049068,1995757234738856,2054293859553536,2107891464349607,
    2092191086033170,2016626455846782,1956616957300787,1984153014646000,2109875781768826,
    2280870606042173,2422401123144597,2483540682611813,2456997935061282,2370033276638567,
    2261687835634127,2163274772943837,2090259443993798,2044198243337899,2019085820845882,
    2007198824325037,2002331754914102,2000629483783689,2000133709911529],
   [2000019361685756]]
private def pv_m2_r256_6_3 : List ℕ := pNatCat
  [
   [2000262974786129,1999644326231183,2000351809505228,2000469273991945,2000569977006835,
    1999375461500310,2000427537767229,1999988013594439,1999822336718995,2000426734635840,
    2000246221114453,2000236543345796,2000453455078320,1999487396382043,1999481016519797,
    1999191061614991,1999810790755049,1999911322123162,1999892962938853,1999855780933841,
    2000082060550579,2000600937234713,1999410770966874,1999674810326876,1999914907299916,
    1998938297652036,1999114403661824,2000452347788783,1999142644368373,2000611845610661,
    1999907343649613,1999618112853860,2000818129893300,2000819549737304,1999119591451215,
    2001365980691462,1998670940700458,2000460236106547,1999883957488953,1999538474112330,
    2000870110430794,1998860058711806,1998834048958539,2000192859778696,1999601058497632,
    1999156454266817,2000445360686162,1999906442359484,1999779638834515,2001569021860519,
    1998262673573593,2001902926051973,1999090098480983,2000858938101246,2001075306983158,
    2000667855712722,1999150351355891,1999838788492589,2000030035037915,1999152473484783,
    2000485428355156,2000214195397521,1999267745178302,2001012314094499],
   [2000836510137670,1998260312784634,2001597992535135,1998874373567310,2000237783204563,
    1998879942288744,2000776094039138,2000317076843376,2001239032055689,2000501073887583,
    1998965160075223,2001190768214417,2000129363040555,2000364412298338,2000063777901680,
    1999707850934587,1997522271678378,2001255469293463,2001079402133568,1999780444512204,
    2000769974915748,1999258211658360,1999445905307851,2000629161986501,1998966982954868,
    2000716192790247,2000615842598401,1998363051786940,1998883532309800,2001551241780777,
    1999831977140740,1999582946779589,2001551370105044,1997071123623409,2000370053881314,
    2001013031315081,2003523818848631,1995939701360508,1999549261195946,1997311264015060,
    2003648160716306,1999998955019324,2001055901538403,1997118343093534,1997283019748832,
    2006557583926310,1997255728556163,2003278378875688,1997245882812118,2003763680913247,
    1997278436622206,2001989052799020,1998120552412593,2000261415330493,1998143717001560,
    2002836921634089,1999567046925801,1999456238375932,2001849569426607,1998000680768893,
    1999986989516098,2003995332304260,1990652146260948,2008259082517558],
   [1995148114582834,2001459977007733,2001720921071444,1997649678564780,2002940871682276,
    1998578414476831,2006513609136390,1994010285936456,2002374727548121,1998881950699606,
    2006883123593223,1998016086112604,1995577982230741,2010626300161703,1993100357848109,
    2003630675440052,2003396027078986,2000281964191668,1993269154771119,2001174321213468,
    2004843353754080,1993109692940238,2002321415225404,1998986157525569,2000669455083425,
    1996114521878734,1994788588958001,2013154824041892,1989850936314621,1995517010872567,
    2010392657069095,1999471329763374,1999127481502949,1998185854388218,2010488654693579,
    1994247621874115,1994506058034081,2017051309072144,1993790955645322,1994767084878931,
    2006531241674849,1994820424710942,2002079297370558,1992943901241236,2009162215791080,
    2007296966614576,1984423116614065,2010617639320307,2002562093020481,1990163173498861,
    2004296761099790,1992255607913590,2006459030386054,2003480193299834,1986698344964076,
    2009982858925894,2002531866048117,1988928660696083,2015099083866508,1996314174108353,
    1994353370310403,2005016678128565,1994609127749570,2005207022992174],
   [2007452788947040,1989491042238215,1994875893412069,2009263553268440,1995467077119094,
    2002629769421930,2007231894425044,1981183405580378,2004674657234411,2013081414454449,
    1982520572400418,2008696155351185,2007268987700238,1978438301805989,2017185165242436,
    2015474771057316,1980859339182655,2016073863633336,2014926920908875,1975648682924796,
    2005594171712607,2014225881054141,1976351536251306,1998309356013800,2016058350228487,
    1976830351239062,1986361988671230,2023881574046473,1997231548681314,1980612787446246,
    2021113754140998,2023771192629489,1989210271424172,2005292360022394,2034910921582377,
    2010405486084096,1990368146522126,2020679881606463,2033559612722886,2001552927110062,
    1996406571684890,2033972681625107,2038360582546361,1995207897928220,1986102612746638,
    2037954908951932,2066829489948013,2017340488953080,1961267084217518,1994924425053023,
    2093495692921746,2134601564720111,2055194386389420,1936341325996092,1920131910547920,
    2065753755051977,2298402548232010,2482839112709702,2531066418881362,2448587425392992,
    2303214335208362,2165559073106975,2072028055395208,2023838495255366],
   [2005244631277607]]
private def phb_m2_r256_6 : List ℤ := uOfNatHb pb_m2_r256_6
private def pvi_m2_r256_6 : List ℤ := bDec bZ pv_m2_r256_6_0
private def pvo_m2_r256_6 : List ℤ := bDec bZ pv_m2_r256_6_3
private def pb_m2_r256_7 : List ℕ := pNatCat
  [
   [104023102656423,146659318685501,179067070430937,206129939242643,229745794902335,
    250891046236701,270147512243102,287895432827815,304399718786531,319853826197823,
    334404231957310,348165069399085,361227368604817,373665151290656,385539598522685,
    396901988088610,407795818698134,418258380580285,428321939412648,438014644066873,
    447361233154743,456383592408798,465101199726843,473531484414223,481690120048321,
    489591265392747,497247764219501,504671312310366,511872598008365,518861421276654,
    525646795158969,532237032727400,538639821982728,544862290691772,550911062770578,
    556792307526416,562511782836833,568074873156426,573486623091143,578751767157811,
    583874756247217,588859781227666,593710794059002,598431526731683,603025508299492,
    607496080236038,611846410313016,616079505171057,620198221731137,624205277575022,
    628103260406751,631894636692973,635581759567886,639166876078090,642652133833714,
    646039587124392,649331202551939,652528864225747,655634378561771,658649478721570,
    661575828723911,664415027258053,667168611224781,669838059028613],
   [672424793642239,674930185462173,677355554972754,679702175233960,681971274207082,
    684164036930945,686281607560238,688325091276441,690295556080911,692194034478847,
    694021525062087,695778993998023,697467376431275,699087577804255,700640475102189,
    702126918027765,703547730110118,704903709752510,706195631222726,707424245589855,
    708590281610907,709694446570387,710737427075769,711719889811556,712642482254428,
    713505833351810,714310554165997,715057238485853,715746463407914,716378789888660,
    716954763269528,717474913776187,717939756993458,718349794317184,718705513384256,
    719007388481944,719255880937566,719451439489497,719594500640446,719685488993838,
    719724817574140,719712888131859,719650091433922,719536807540116,719373406066173,
    719160246434107,718897678110326,718586040832023,718225664822328,717816870994654,
    717359971146649,716855268144144,716303056095439,715703620516286,715057238485853,
    714364178793971,713624702079932,712839060963071,712007500165374,711130256626316,
    710207559610106,709239630805543,708226684418604,707168927257935],
   [706066558813354,704919771327478,703728749860580,702493672348743,701214709655386,
    699892025616213,698525777077622,697116113928602,695663179126123,694167108714018,
    692628031835343,691046070738171,689421340774792,687753950394236,686044001128064,
    684291587569308,682496797344486,680659711078532,678780402352523,676858937654032,
    674895376319933,672889770471458,670842164941279,668752597192398,666621097228548,
    664447687495855,662232382775414,659975190066470,657676108459809,655335129000984,
    652952234542930,650527399587507,648060590115470,645551763404318,643000867833444,
    640407842675948,637772617876437,635095113814068,632375241050061,629612900058803,
    626807980941648,623960363122392,621069915023373,618136493721024,615159944579627,
    612140100861923,609076783315096,605969799730569,602818944475875,599623997996752,
    596384726287442,593100880326999,589772195479229,586398390853667,582979168624781,
    579514213306318,576003190977452,572445748457074,568841512422218,565190088466256,
    561491060092067,557743987634909,553948407109240,550103828973107],
   [546209736803141,542265585872413,538270801622656,534224778021415,530126875793701,
    525976420516562,521772700563707,517514964885861,513202420610878,508834230445765,
    504409509860648,499927324032283,495386684521932,490786545659268,486125800600309,
    481403277023199,476617732420798,471767848943458,466852227738815,461869382727901,
    456817733747991,451695598982242,446501186583998,441232585389231,435887754593547,
    430464512249935,424960522419217,419373280776162,413700098439262,407938083749891,
    402084121675097,396134850445395,390086634961589,383935536408984,377677277398348,
    371307201803866,364820228280255,358210796202165,351472802462793,344599527173032,
    337583545786685,330416624498206,323089594855898,315592202317530,307912921818601,
    300038731135672,291954829621255,283644285321460,275087586870399,266262066774048,
    257141147918773,247693342260966,237880894240578,227657901653972,216967644874585,
    205738674427388,193878869357318,181266010345189,167731988077251,153034447222074,
    136800947521411,118403790237290,96617715951086,68276217100392]]
private def pv_m2_r256_7_0 : List ℕ := pNatCat
  [
   [2000262974786129,2000355673768817,1999648190494772,2000469273991945,2000569977006835,
    2000624538499690,2000427537767229,2000011986405561,1999822336718995,1999573265364160,
    1999753778885547,1999763456654204,2000453455078320,1999487396382043,1999481016519797,
    1999191061614991,1999810790755049,2000088677876838,2000107037061147,1999855780933841,
    2000082060550579,2000600937234713,1999410770966874,1999674810326876,1999914907299916,
    1998938297652036,1999114403661824,1999547652211217,1999142644368373,1999388154389339,
    1999907343649613,1999618112853860,1999181870106700,2000819549737304,1999119591451215,
    1998634019308538,1998670940700458,2000460236106547,1999883957488953,2000461525887670,
    1999129889569206,1998860058711806,1998834048958539,2000192859778696,2000398941502368,
    2000843545733183,2000445360686162,2000093557640516,1999779638834515,2001569021860519,
    2001737326426407,2001902926051973,2000909901519017,2000858938101246,2001075306983158,
    2000667855712722,1999150351355891,2000161211507411,2000030035037915,1999152473484783,
    1999514571644844,2000214195397521,1999267745178302,2001012314094499],
   [2000836510137670,2001739687215366,2001597992535135,1998874373567310,2000237783204563,
    1998879942288744,1999223905960862,2000317076843376,2001239032055689,2000501073887583,
    2001034839924777,2001190768214417,2000129363040555,1999635587701662,2000063777901680,
    1999707850934587,2002477728321622,2001255469293463,2001079402133568,1999780444512204,
    2000769974915748,2000741788341640,1999445905307851,2000629161986501,1998966982954868,
    2000716192790247,1999384157401599,1998363051786940,1998883532309800,2001551241780777,
    1999831977140740,1999582946779589,1998448629894956,1997071123623409,2000370053881314,
    2001013031315081,1996476181151369,1995939701360508,1999549261195946,1997311264015060,
    1996351839283694,1999998955019324,2001055901538403,1997118343093534,1997283019748832,
    2006557583926310,2002744271443837,2003278378875688,2002754117187882,2003763680913247,
    1997278436622206,1998010947200980,1998120552412593,2000261415330493,1998143717001560,
    2002836921634089,2000432953074199,1999456238375932,2001849569426607,1998000680768893,
    1999986989516098,1996004667695740,1990652146260948,2008259082517558],
   [1995148114582834,2001459977007733,1998279078928556,1997649678564780,2002940871682276,
    1998578414476831,2006513609136390,2005989714063544,2002374727548121,2001118049300394,
    2006883123593223,1998016086112604,2004422017769259,2010626300161703,1993100357848109,
    2003630675440052,2003396027078986,1999718035808332,1993269154771119,2001174321213468,
    2004843353754080,1993109692940238,1997678584774596,1998986157525569,2000669455083425,
    1996114521878734,1994788588958001,1986845175958108,1989850936314621,1995517010872567,
    2010392657069095,1999471329763374,1999127481502949,1998185854388218,2010488654693579,
    1994247621874115,1994506058034081,1982948690927856,1993790955645322,1994767084878931,
    2006531241674849,1994820424710942,1997920702629442,1992943901241236,2009162215791080,
    2007296966614576,1984423116614065,1989382360679693,2002562093020481,1990163173498861,
    2004296761099790,1992255607913590,2006459030386054,2003480193299834,1986698344964076,
    2009982858925894,2002531866048117,2011071339303917,2015099083866508,1996314174108353,
    1994353370310403,2005016678128565,2005390872250430,2005207022992174],
   [2007452788947040,1989491042238215,1994875893412069,1990736446731560,1995467077119094,
    2002629769421930,2007231894425044,1981183405580378,1995325342765589,2013081414454449,
    1982520572400418,2008696155351185,2007268987700238,2021561698194011,2017185165242436,
    2015474771057316,1980859339182655,2016073863633336,1985073079091125,1975648682924796,
    2005594171712607,2014225881054141,1976351536251306,1998309356013800,2016058350228487,
    1976830351239062,1986361988671230,2023881574046473,2002768451318686,1980612787446246,
    2021113754140998,2023771192629489,1989210271424172,2005292360022394,2034910921582377,
    2010405486084096,2009631853477874,2020679881606463,2033559612722886,2001552927110062,
    2003593428315110,2033972681625107,2038360582546361,2004792102071780,2013897387253362,
    2037954908951932,2066829489948013,2017340488953080,2038732915782482,2005075574946977,
    2093495692921746,2134601564720111,2055194386389420,2063658674003908,2079868089452080,
    2065753755051977,2298402548232010,2482839112709702,2531066418881362,2448587425392992,
    2303214335208362,2165559073106975,2072028055395208,2023838495255366],
   [2005244631277607]]
private def pv_m2_r256_7_1 : List ℕ := pNatCat
  [
   [1999750409187893,2000475457275360,2000354927552818,1999982909617349,1999993894560995,
    1999814279814269,2000293147976434,2000017480550490,2000817819796268,2000350053948626,
    2000489705882055,2000464179375901,2000221175151102,1999925666477448,1999414741606617,
    1999870193707000,1999731954266666,2000161365440165,2000528089457697,1999428484030850,
    1999113393161158,1999993802194585,1999592484078120,1999522528133029,1999492375491248,
    2000722255086555,1999268957932269,2000418039275434,2000214372120820,2000258975716258,
    1999348977559733,2000589343520033,1999636395077996,1999027472359357,1999092974382908,
    2000001416183472,1999275912045343,1999088508171211,1998907118945689,1999895039098082,
    1999823985783530,2000626355662819,1999638939774719,1998819660159527,1998679384200739,
    1999450965426216,1999569544319285,2000538638148451,2000041428058651,1999633580392468,
    1998916887222174,1998722986915204,1998761098230995,2001262504976328,2000432825377155,
    1998969918280497,2000699947480962,1999368511103404,2000944674068167,2000473597804227,
    2000924781052110,2001843872619927,2001450467837624,2000849128061955],
   [2001682023817385,2000956884805476,2000079717939042,1999864434069172,2001272155085385,
    1998957660598696,2000067061215251,1999164037536707,1998955608113559,1999893042990009,
    2000152882024503,2002056877101146,2000729324806181,2001841196747123,1999512556886546,
    1999799737669471,1999882167342100,1999500413286090,1998754584667113,2000705596849221,
    2001136617549224,2001272124939097,2001535297737705,1998900578066840,1999456856189189,
    2001264740677761,2000323052749506,1999835170621432,2001977154137523,2001043427715095,
    2000281558352193,2002288768443495,1998494773585581,2000522724926348,2000746491194226,
    2003926385578761,1995719064613470,1998183874663121,2001697832956295,2001253517320776,
    1996682644438881,2001958976135798,1999973515292494,1997655425789640,1998042299329844,
    2002220266567536,2000945228290198,1995169241156851,1998267762143708,1999900060019898,
    1993951254449278,2003900951671679,1992003127166178,2002243892056590,1995795970410364,
    1995403982910075,2005729376219889,1997901391075153,2005285384345510,2005318554904645,
    2003235095665988,1998655931157826,1999589204975404,1999825662801035],
   [2000927645893624,1997092278219727,1995108910217897,2009402506879087,1995947473084527,
    2003130788786142,2002645584837164,1992947507267169,1997996137094818,1999967553261068,
    1999287855437752,1995240362572241,2004667988507962,1996055964602791,1993112708895127,
    2001246535248878,2007935082547606,1997053457131373,2003812226815847,2003396935289192,
    2007313484640999,1996469007539352,2007042061140614,2002448251987627,2007924565464271,
    1997722597634991,2006419483297055,1995098655058904,2003807586988183,2001800474940891,
    2001939329626497,1987594290712788,2001123910739518,2005408773446794,2004418996420687,
    1995335389502117,1987283965830410,1993089350636994,1997959005039575,1987479847898064,
    2004667026352557,1987432771592554,2003810600903146,2018905005812934,1995938779836678,
    1996395031845377,1983851460886993,2002662328380036,1999455973638581,1981774452092601,
    1997654713875229,2000438936040940,1997814063601353,2004051958043023,2001778667348137,
    1992577817272172,2001894787732843,1985919635731700,1994080691607899,2001711556953821,
    2003070198893207,1994273326069831,1995047629162208,1992937127993759],
   [2003904750569406,2021646055371544,1990583855113363,2017685653334405,1994626953613264,
    1995765822274449,2008954018960991,2022668333480893,1986189091184324,2006833042464644,
    1987668836742306,1999879080067248,2002990153148183,1986064917506018,1997730290291247,
    2015270204709836,1979626305206370,1981474710448804,2018499228291259,1994105812798448,
    1999905277265336,2039814841700499,2014970762184081,1986009700273483,2015472326174343,
    1998094540496316,1970553815366249,2006538415181236,2016848744714085,1971652495390434,
    1998814765478480,2007721865242215,1989209070072428,1983918668371131,2014872600467815,
    2006958899604637,1991481545241289,2007860980971434,2025498746299780,1992152430195858,
    2014575129682649,2024649986205927,2040034222960999,1977651308901241,2033413655524476,
    2024280071246461,2022731156346662,2019504636417296,1986496077418463,2067119064574838,
    2070385563093092,1969058747296799,2050374075628563,2041771583535190,2087367850575014,
    2138814750841596,2049727932605509,1976261459736068,2106847077576727,2373408091810406,
    2559934690183469,2543483638237857,2374766401115464,2183270255069727],
   [2056819392772872]]
private def pv_m2_r256_7_2 : List ℕ := pNatCat
  [
   [1999676257629551,1999712470431923,2000288672944668,2000034083352095,2000623845384974,
    1999975366393934,2000120990836893,2000134526686780,1999762255537512,1999993985286977,
    1999882128604262,2000349161516839,2000394155793124,2000113432314671,2000517805756002,
    2000835573760820,1999998887618918,2000775432172811,2000019399617875,2000150650438418,
    1998638297356006,2000313136958519,2000247627338317,2000196447731807,1999445609514877,
    2000415429233320,1999734145399080,1999340529945635,1999464044060477,2000212361392615,
    1999188552423921,1999582435181377,1999840983349843,2000527134242410,1999591145656575,
    1999785684550755,2000321893974644,2000646625102119,1999815906196165,2000039825376780,
    1999333640755824,1999594526956062,1999776524618993,2000011333831658,1998883281311767,
    1998852620997097,1999335298874512,1998595451398479,2001404346837160,1999621156138212,
    1999654836985368,2000067024222003,1998762274388627,1998363143319294,1999468093063627,
    2000012703100012,2001146470695476,1999538629035743,1999151726535235,1998391156840081,
    2000222590398486,1998922813010625,1999469598022595,2001058639950610],
   [1999000992701720,2000116042863670,1999353828830263,2000838366921915,1999561277611792,
    2000743677924336,2001078012908231,2001245749130168,2001467436037064,2001719693428073,
    2000772212990595,2000727799526843,2001354412168161,1999897448377297,2000905208671891,
    2000799629257310,1998861210678764,1998793906105403,1999274811431562,1999502350294097,
    2000148174672984,2002590560983971,1998416042016847,2002970052943953,2000607528751230,
    2001022865516619,1997412454493903,2000428373329472,1999020809888222,2000334580529843,
    2001171642565344,2002112971400785,1997720802899324,2001551907998059,2002632272953051,
    1997219383815288,1998375114713565,2003702265463892,2001595984177374,2000919059847686,
    1995389412365743,2008304470425656,1995297884523812,2002331320324390,2003801397947752,
    1996489918807449,2003261999969353,1994504861300953,2003066415429553,2001747938592948,
    1997361515772545,1999671313758454,2000312540672613,1998163714574076,1999928653183754,
    2003432350506563,1995049717334680,2002400063043147,1994271095516582,2001474940015281,
    1999169566065020,1992693468116642,2004816764098742,1995698909357992],
   [1992875439160739,1997088938828052,2003380859969744,1997745403152695,2005039853457599,
    2003791969510376,2001312743869122,2000688781078208,2008455287845931,1992153537424475,
    1999635162842203,1998993058995274,2003038478089997,1994324286263288,2009491183797384,
    1999439609343070,1998911016323189,1991940398155317,2005945681820487,1997401576278667,
    1998886295473324,1996383780226689,2001340107973460,1993621687895302,1999205186400312,
    2001008587567488,1998631608871663,2003923740188574,2006415765397768,1994887774254388,
    2006755556819903,1999804795142759,2013758912416181,2000984035746243,1990582417846155,
    2016152612509101,1998998173180868,2006508640299499,1997141855981001,1990304013314342,
    2003442265216180,2002644573641142,2007763916467660,1993561877720926,1991088127969796,
    2006668050876458,1998818176354421,1974768270810624,1995119003182560,1996848897975836,
    2005036140438360,2003615856125291,1998758311311012,2000484582638892,2002008704490074,
    1994431194267109,1987293349309435,2003461592509478,1978864267417084,2007566515684344,
    1990132738640080,2007383637678556,2006140642284190,1994030532862408],
   [1979389004000627,2013747932144320,1986859118160209,2002477880998221,2001809992889262,
    1982579186956092,1994972257232257,2005962180914269,2005811210411252,2013013970163375,
    1992979661861622,1991765976420832,2026607974958372,1999792312856150,1992505370419852,
    2024879607302405,1997065575816780,1976802789815541,2015778017149308,1997434157542019,
    1982362410865168,2015307928838424,1999467747394651,1962867908642957,2010958424129852,
    2000292930410176,1994126313947169,2028167077173808,2028551493206623,1989708513112179,
    2001495691458349,2008611865201307,1989776993856166,1985120137255318,2020192979719801,
    1980773419375586,1994326968850490,1991314257879825,2015386691903204,1966633171167269,
    2021553427049944,2013893259018339,1980840788592378,2017447545311648,2008624586681148,
    2033332445122627,2013221788179635,1975193794086730,2085589965767708,1994204215548161,
    1989447184257407,2043211618974446,2030919244353483,2051128730200607,2019695306434312,
    1979879288739806,2080632820441808,2166575366773688,2053275378551725,1931282491985355,
    2082783803315813,2430054940063665,2633831735259724,2523307021946120],
   [2244809699923814]]
private def phb_m2_r256_7 : List ℤ := uOfNatHb pb_m2_r256_7
private def pvi_m2_r256_7 : List ℤ := bDec bZ pv_m2_r256_7_0
private def pvo_m2_r256_7 : List ℤ := bDec bZ pv_m2_r256_7_2
private def pwalks_m2_r256 : List RkmSegWalk := [
  ⟨phb_m2_r256_0, pvi_m2_r256_0, pvo_m2_r256_0⟩,
  ⟨phb_m2_r256_1, pvi_m2_r256_1, pvo_m2_r256_1⟩,
  ⟨phb_m2_r256_2, pvi_m2_r256_2, pvo_m2_r256_2⟩,
  ⟨phb_m2_r256_3, pvi_m2_r256_3, pvo_m2_r256_3⟩,
  ⟨phb_m2_r256_4, pvi_m2_r256_4, pvo_m2_r256_4⟩,
  ⟨phb_m2_r256_5, pvi_m2_r256_5, pvo_m2_r256_5⟩,
  ⟨phb_m2_r256_6, pvi_m2_r256_6, pvo_m2_r256_6⟩,
  ⟨phb_m2_r256_7, pvi_m2_r256_7, pvo_m2_r256_7⟩
  ]
private def pb_m4_r192_0 : List ℕ := pNatCat
  [
   [526563565003119,643224390436206,641538347194356,522433590924692]]
private def pv_m4_r192_0_0 : List ℕ := [3000000000000000]
private def pv_m4_r192_0_1 : List ℕ := pNatCat
  [
   [2558370630060046,2650351526194574,2462245159956767,2218264487346879,2062890043110817]]
private def phb_m4_r192_0 : List ℤ := uOfNatHb pb_m4_r192_0
private def pvi_m4_r192_0 : List ℤ := bDec bZ pv_m4_r192_0_0
private def pvo_m4_r192_0 : List ℤ := bDec bZ pv_m4_r192_0_1
private def pb_m4_r192_1 : List ℕ := pNatCat
  [
   [432786426774718,528670808337418,527285037124738,429391971018814]]
private def pv_m4_r192_1_0 : List ℕ := pNatCat
  [
   [2558370630060046,2650351526194574,2462245159956767,2218264487346879,2062890043110817]]
private def pv_m4_r192_1_1 : List ℕ := pNatCat
  [
   [2107460365493582,2310237622342827,2544101831609104,2631133063331321,2444779878974640]]
private def phb_m4_r192_1 : List ℤ := uOfNatHb pb_m4_r192_1
private def pvi_m4_r192_1 : List ℤ := bDec bZ pv_m4_r192_1_0
private def pvo_m4_r192_1 : List ℤ := bDec bZ pv_m4_r192_1_1
private def pb_m4_r192_2 : List ℕ := pNatCat
  [
   [169147526769999,237341075085993,288390384324953,330355691333079,366384642742508,
    398104004168109,426487363619285,452173682840661,475609940975111,497123841983371,
    516964455098176,535326563971638,552366069272796,568210167495218,582964324308326,
    596717198375605,609544208525715,621510175930918,632671319242422,643076786865635,
    652769851529252,661788854100470,670167958263522,677937760505615,685125787983357,
    691756908490137,697853670772611,703436589111015,708524382891100,713134179522639,
    717281687272280,720981343218278,724246440488878,727089238134833,729521056351544,
    731552359265242,733192827099184,734451419216491,735336429278605,735855533548779,
    736015833198551,735823891333652,735285765338262,734407035038046,733192827099184,
    731647836009526,729776341926727,727582225624486,725068980720451,722239723326185,
    719097199219929,715643788605316,711881508482942,707812012625580,703436589111015,
    698756155327832,693771250327982,688482024354220,682888225319214,676989181954383,
    670783783278334,664270453954417,657447125011203,650311199284352],
   [642859510798174,635088277133136,626993043612802,618568617878236,609808993084035,
    600707257526791,591255487975175,581444623271874,571264313866862,560702741743046,
    549746403601098,538379848025245,526585354429455,514342537548139,501627855580880,
    488413992048370,474669069745134,460355637921728,445429347763310,429837190875432,
    413515111257398,396384695748772,378348468288111,359282994273246,339028405914914,
    317371780448620,294019292627370,268546207741827,240298406633858,208171644301654,
    170007961323459,120226693943054]]
private def pv_m4_r192_2_0 : List ℕ := pNatCat
  [
   [2107460365493582,2310237622342827,2544101831609104,2631133063331321,2444779878974640]]
private def pv_m4_r192_2_1 : List ℕ := pNatCat
  [
   [2018425831442836,2037359129073626,2045955354509315,2033841547775060,2003644776210874,
    1971819761739725,1958337732005877,1972630198153793,2006274782136142,2037797172178013,
    2046205884687740,2024222382843894,1983119713244241,1947003653877382,1940681235433060,
    1978109126434767,2056915438870340,2160479087404938,2265258045333877,2349315109354785,
    2398534973915408,2408906005871000,2385195493614807,2337528556718392,2277587297030255,
    2215662661252991,2159067622485463,2111815546527789,2075143124080257,2048400924813044,
    2029944853848425,2017827010712843,2010228043817940,2005662943605490,2003029211785683,
    2001567089230484,2000784729579604,2000380669750652,2000179010749435,2000081654126042,
    2000036147723634,2000015538034740,2000006487955642,2000002632563062,2000001038368256,
    2000000398244746,2000000148553262,2000000053906302,2000000019032639,2000000006539184,
    2000000002186568,2000000000711627,2000000000225429,2000000000069508,2000000000020856,
    2000000000006088,2000000000001727,2000000000000475,2000000000000124,2000000000000030,
    2000000000000006,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000]]
private def phb_m4_r192_2 : List ℤ := uOfNatHb pb_m4_r192_2
private def pvi_m4_r192_2 : List ℤ := bDec bZ pv_m4_r192_2_0
private def pvo_m4_r192_2 : List ℤ := bDec bZ pv_m4_r192_2_1
private def pb_m4_r192_3 : List ℕ := pNatCat
  [
   [6148992000000,8650696277775,10539425241008,12105828000000,13463114852912,14669656039943,
    15760306656796,16757893312967,17678352000000,18533344095053,19331717047537,20080378617078,
    20784849326641,21449627184919,22078437306923,22674408000000,23240198214821,23778091862994,
    24290068976455,24777860314403,25242989903544,25686808626221,26110521062154,26515207173802,
    26901840000000,27271300223367,27624388263274,27961834391091,28284307250579,28592421081456,
    28886741880407,29167792685273,29436058130884,29691988396106,29936002639100,30168492000000,
    30389822236071,30600336043158,30800355108092,30990181929433,31170101437859,31340382442688,
    31501278926894,31653031209704,31795866993049,31930002305816,32055642357936,32172982314656,
    32282208000000,32383496537220,32477016933056,32562930611738,32641391903973,32712548495489,
    32776541839186,32833507534457,32883575676861,32926871180933,32963514078646,32993619795739,
    33017299407917,33034659878676,33045804280380,33050832000000],
   [33049838930817,33042917651252,33030157591870,33011645191507,32987464043392,32957695032029,
    32922416461561,32881704176255,32835631673704,32784270211274,32727688906288,32665954830405,
    32599133098591,32527286953076,32450477842620,32368765497428,32282208000000,32190861852172,
    32094782038624,31994022087050,31888634125240,31778668935231,31664176004747,31545203576062,
    31421798692465,31294007242466,31161874001870,31025442673853,30884755927156,30739855432495,
    30590781897311,30437575098921,30280273916190,30118916359792,29953539601130,29784180000000,
    29610873131065,29433653809194,29252556113727,29067613411733,28878858380294,28686323027886,
    28490038714881,28290036173232,28086345525367,27878996302342,27668017461286,27453437402162,
    27235283983891,27013584539864,26788365892867,26559654369446,26327475813746,26091855600838,
    25852818649565,25610389434924,25364592000000,25115449967487,24862986550798,24607224564791,
    24348186436118,24085894213233,23820369576043,23551633845251],
   [23279707991372,23004612643461,22726368097548,22444994324799,22160510979415,21872937406276,
    21582292648341,21288595453811,20991864283079,20692117315446,20389372455645,20083647340156,
    19774959343332,19463325583342,19148762927928,18831288000000,18510917183059,18187666626465,
    17861552250550,17532589751579,17200794606577,16866182078010,16528767218339,16188564874444,
    15845589691923,15499856119273,15151378411957,14800170636356,14446246673619,14089620223405,
    13730304807523,13368313773480,13003660297933,12636357390048,12266417894772,11893854496025,
    11518679719801,11140905937196,10760545367359,10377610080360,9992112000000,9604062906534,
    9213474439345,8820358099530,8424725252445,8026587130173,7625954833933,7222839336442,
    6817251484206,6409201999765,5998701483886,5585760417697,5170389164778,4752597973200,
    4332396977517,3909796200712,3484805556102,3057434849193,2627693779501,2195591942324,
    1761138830479,1324343836003,885216251807,443765273305]]
private def pv_m4_r192_3_0 : List ℕ := pNatCat
  [
   [2018425831442836,2037359129073626,2045955354509315,2033841547775060,2003644776210874,
    1971819761739725,1958337732005877,1972630198153793,2006274782136142,2037797172178013,
    2046205884687740,2024222382843894,1983119713244241,1947003653877382,1940681235433060,
    1978109126434767,2056915438870340,2160479087404938,2265258045333877,2349315109354785,
    1601465026084592,2408906005871000,2385195493614807,2337528556718392,2277587297030255,
    2215662661252991,2159067622485463,2111815546527789,2075143124080257,2048400924813044,
    2029944853848425,2017827010712843,1989771956182060,2005662943605490,1996970788214317,
    2001567089230484,2000784729579604,2000380669750652,2000179010749435,2000081654126042,
    2000036147723634,2000015538034740,2000006487955642,2000002632563062,2000001038368256,
    2000000398244746,2000000148553262,2000000053906302,2000000019032639,2000000006539184,
    2000000002186568,2000000000711627,2000000000225429,2000000000069508,2000000000020856,
    2000000000006088,2000000000001727,2000000000000475,2000000000000124,2000000000000030,
    2000000000000006,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000]]
private def pv_m4_r192_3_1 : List ℕ := pNatCat
  [
   [2018196985501057,2037074334113897,2045918333051661,2034276809981888,2004432027072564,
    1972485121795425,1958366514174313,1971878074483286,2005148260971544,2037039755770628,
    2046419329226105,2025440747759221,1984710169798883,1947948418176886,1940066253780831,
    1975549700591123,2052718198414824,2155503147606435,2260331990647643,2365591201274124,
    1600252302713774,2388914918099295,2386594298734460,2340203781855693,2280728651095855,
    2218796395630459,2161871099660702,2114122520649894,2076914826892598,2049682653625518,
    2030815180518219,2018997565442160,1990145345114522,2005455424557051,1997090619576554,
    2001454014649384,2000818442665408,2000399420158828,2000188360607100,2000086158102183,
    2000038248431586,2000016487425916,2000006903977389,2000002809420930,2000001111345207,
    2000000427485485,2000000159934680,2000000058211092,2000000020615263,2000000007104872,
    2000000002383192,2000000000778098,2000000000247287,2000000000076500,2000000000023032,
    2000000000006746,2000000000001921,2000000000000530,2000000000000139,2000000000000034,
    2000000000000007,2000000000000000,2000000000000000,2000000000000000],
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
private def phb_m4_r192_3 : List ℤ := uOfNatHb pb_m4_r192_3
private def pvi_m4_r192_3 : List ℤ := bDec bZ pv_m4_r192_3_0
private def pvo_m4_r192_3 : List ℤ := bDec bZ pv_m4_r192_3_1
private def pb_m4_r192_4 : List ℕ := pNatCat
  [
   [99237120000000,139611530572998,170093278276009,195373080000000,217278009831901,
    236750091201068,254351842210453,270451656083818,285306720000000,299105234152537,
    311989985424042,324072456504818,335441741802537,346170433610108,356318650673096,
    365936880000000,375068033763586,383748971470282,392011648384767,399883996818287,
    407390612675518,414553297525419,421391491793700,427922624737760,434162400000000,
    440125030707859,445823434639224,451269397470158,456473710283348,461446286147555,
    466196259548716,470732071670213,475061543918343,479191941622788,483130029477473,
    486882120000000,490454116059950,493851548344054,497079608479638,500143178418996,
    503046856590650,505794981244242,508391651350609,510840745364641,513145938113640,
    515310716036484,517338390967439,519232112632028,520994880000000,522629551621432,
    524138855055885,525525395490641,526791663632294,527940042945698,528972816305556,
    529892172118266,530700209965109,531398945812070,531990316826611,532476185837323,
    532858345468562,533138521978788,533318378828369,533399520000000],
   [533383493092555,533271792207158,533065860642419,532767093414186,532376839613691,
    531896404616714,531327052155199,530670006261762,529926453096578,529097542665314,
    528184390436029,527188078862273,526109658819029,524950150957574,523710546984845,
    522391810872444,520994880000000,519520666237245,517970056968817,516343916065482,
    514643084805211,512868382747264,511020608562225,509100540820690,507108938743136,
    505046542913300,502914075957249,500712243190161,498441733232681,496103218598632,
    493697356255680,491224788160506,488686141769888,486082030529025,483413054338351,
    480679800000000,477882841644993,475022741142205,472100048490020,469115302191610,
    466069029614661,462961747336337,459793961474235,456566168004025,453278853064422,
    449932493250136,446527555893356,443064499334337,439543773181602,435965818562247,
    432331068362818,428639947461193,424892872949880,421090254351130,417232493824225,
    413319986365295,409353120000000,405332275969381,401257828909193,397130147022980,
    392949592249184,388716520422523,384431281429900,380094219361042],
   [375705672654122,371265974236546,366775451661114,362234427237736,357643218160892,
    353002136632993,348311489983813,343571580786150,338782706967854,333945161920366,
    329059234603908,324125209649443,319143367457533,314113984294209,309037332383969,
    303913680000000,298743291551740,293526427669868,288263345288816,282954297726894,
    277599534764117,272199302717806,266753844516052,261263399769112,255728204838809,
    250148492906006,244524494036225,238856435243462,233144540552274,227389031058184,
    221590124986467,215748037749370,209862982001815,203935167695636,197964802132399,
    191952090014853,185897233497048,179800432233169,173661883425129,167481781868954,
    161260320000000,154997687937039,148694073525256,142349662378170,135964637918541,
    129539181418265,123073472037315,116567686861730,110022000940699,103436587322765,
    96811617091165,90147259398342,83443681499646,76701048786253,69919524817321,63099271351406,
    56240448377160,49343214143328,42407725188073,35434136367632,28422600884338,21373270314016,
    14286294632773,7161822243200]]
private def pv_m4_r192_4_0 : List ℕ := pNatCat
  [
   [2018196985501057,1962925665886103,2045918333051661,2034276809981888,2004432027072564,
    1972485121795425,1958366514174313,1971878074483286,2005148260971544,2037039755770628,
    2046419329226105,2025440747759221,1984710169798883,1947948418176886,1940066253780831,
    1975549700591123,2052718198414824,2155503147606435,2260331990647643,2365591201274124,
    2399747697286226,2388914918099295,2386594298734460,2340203781855693,2280728651095855,
    2218796395630459,2161871099660702,2114122520649894,2076914826892598,2049682653625518,
    2030815180518219,2018997565442160,1990145345114522,2005455424557051,1997090619576554,
    2001454014649384,1999181557334592,2000399420158828,2000188360607100,2000086158102183,
    2000038248431586,2000016487425916,2000006903977389,2000002809420930,2000001111345207,
    2000000427485485,2000000159934680,2000000058211092,2000000020615263,2000000007104872,
    2000000002383192,2000000000778098,2000000000247287,2000000000076500,2000000000023032,
    2000000000006746,2000000000001921,2000000000000530,2000000000000139,2000000000000034,
    2000000000000007,2000000000000000,2000000000000000,2000000000000000],
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
private def pv_m4_r192_4_1 : List ℕ := pNatCat
  [
   [2030373601674194,1958473366744038,2009233672912881,2036392899901785,2032852240407431,
    2009649868296763,1980594918364792,1961484948890076,1963578213970932,1986902531428870,
    2019362360094261,2042906785609687,2043323739358975,2018251347677776,1978522218002012,
    1946002332260356,1933875769864074,1973548909126128,2028907820040777,2116699205482234,
    2246176127985266,2323171818293444,2367246043653409,2390734985974764,2386993549138600,
    2356479829743496,2307497420642501,2251577640803907,2192124593934105,2149894759773213,
    2091376384848112,2079022324693918,2046862660500123,2023732480498529,2008235458766899,
    2002661371684029,2000752932829713,1999967004155740,1999925358912133,2000093913930406,
    2000163625058623,2000136049181029,2000084196212330,2000044358218474,2000021231819562,
    2000009563329155,2000004130069255,2000001726095414,2000000701120023,2000000277305065,
    2000000106886911,2000000040167254,2000000014719995,2000000005261473,2000000001834557,
    2000000000624061,2000000000207121,2000000000067071,2000000000021191,2000000000006530,
    2000000000001960,2000000000000571,2000000000000160,2000000000000041],
   [2000000000000009,2000000000000001,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000]]
private def phb_m4_r192_4 : List ℤ := uOfNatHb pb_m4_r192_4
private def pvi_m4_r192_4 : List ℤ := bDec bZ pv_m4_r192_4_0
private def pvo_m4_r192_4 : List ℤ := bDec bZ pv_m4_r192_4_1
private def pb_m4_r192_5 : List ℕ := pNatCat
  [
   [36012288000000,50663810549072,61725371757461,70899192000000,78848300576772,85914549599576,
    92302071996984,98144554466790,103535328000000,108542688810483,113218453016436,117603076716847,
    121728891497602,125622240470623,129304940205952,132795312000000,136108928307149,
    139259165121797,142257618731649,145114425529592,147838511155575,150437787209414,
    152919308452566,155289399810999,157553760000000,159717546839935,161785448080082,
    163761740639811,165650340509201,167454845054715,169178569101875,170824575882737,
    172395703717641,173894589131557,175323686973092,176685288000000,177981534312325,
    179214432948195,180385867904025,181497610797857,182551330359417,183548600901781,
    184490909905827,185379664829109,186216199234506,187001778320371,187737603922564,
    188424819049092,189064512000000,189657720118257,190205433211511,190708596679578,
    191168114378221,191584851246115,191959635718638,192293261949445,192586491858328,
    192840057021814,193054660421132,193230978060580,193369660467951,193471334087430,
    193536602574322,193566048000000],
   [193560231974639,193519696694546,193444965920239,193336545890837,193194926179821,
    193020580496709,192813967438838,192575531196999,192305702218408,192004897830122,
    191673522825800,191311970018425,190920620761390,190499845440170,190050003936589,
    189571446067560,189064512000000,188529532643506,187966830022248,187376717627415,
    186759500751469,186115476805339,185444935619636,184748159730859,184025424653518,
    183276999139012,182503145422059,181704119455402,180880171133488,180031544505734,
    179158477979995,178261204516768,177339951814664,176394942487609,175426394234258,
    174434520000000,173419528131992,172381622527563,171321002776346,170237864296458,
    169132398465047,168004792743475,166855230797418,165683892612132,164490954603133,
    163276589722494,162040967561005,160784254446360,159506613537580,158208204915856,
    156889185671949,155549709990347,154189929230297,152809992003860,151410044251145,
    149990229312812,148550688000000,147091558661767,145612977250172,144115077383079,
    142597990404801,141061845444666,139506769473586,137932887358732],
   [136340321916375,134729193962975,133099622364596,131451724084701,129785614230409,
    128101406097261,126399211212560,124679139377343,122941298707036,121185795670842,
    119412735129914,117622220374353,115814353159085,113989233738651,112146960900953,
    110287632000000,108411342987676,106518188444590,104608261610013,102681654410956,
    100738457490416,98778760234807,96802650800620,94810216140335,92801542027602,90776713081728,
    88735812791492,86678923538298,84606126618710,82517502266372,80413129673338,78293087010840,
    76157451449499,74006299179012,71839705427313,69657744479251,67460489694772,65248013526645,
    63020387537729,60777682417808,58519968000000,56247313276753,53959786415453,51657454773631,
    49340384913812,47008642617992,44662292901766,42301400028118,39926027520878,37536238177856,
    35132094083673,32713656622278,30280986489184,27834143703410,25373187619154,22898176937188,
    20409169716003,17906223382694,15389394743597,12858739994696,10314314731784,7756173960411,
    5184372105601,2598963021366]]
private def pv_m4_r192_5_0 : List ℕ := pNatCat
  [
   [1969626398325806,2041526633255962,2009233672912881,1963607100098215,1967147759592569,
    2009649868296763,1980594918364792,1961484948890076,1963578213970932,1986902531428870,
    2019362360094261,2042906785609687,2043323739358975,2018251347677776,1978522218002012,
    1946002332260356,1933875769864074,1973548909126128,2028907820040777,2116699205482234,
    2246176127985266,2323171818293444,2367246043653409,2390734985974764,2386993549138600,
    2356479829743496,2307497420642501,2251577640803907,1807875406065895,2149894759773213,
    2091376384848112,2079022324693918,2046862660500123,2023732480498529,2008235458766899,
    2002661371684029,1999247067170287,1999967004155740,1999925358912133,2000093913930406,
    2000163625058623,2000136049181029,2000084196212330,2000044358218474,2000021231819562,
    2000009563329155,2000004130069255,2000001726095414,2000000701120023,2000000277305065,
    2000000106886911,2000000040167254,2000000014719995,2000000005261473,2000000001834557,
    2000000000624061,2000000000207121,2000000000067071,2000000000021191,2000000000006530,
    2000000000001960,2000000000000571,2000000000000160,2000000000000041],
   [2000000000000009,2000000000000001,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000]]
private def pv_m4_r192_5_1 : List ℕ := pNatCat
  [
   [1968160670948276,2039830494447363,2013447514973938,1966752641290632,1963959946939599,
    2008414485141762,1984838541796406,1963572651665288,1961547934699544,1981263673779642,
    2012955893859028,2039503146889427,2045489839042921,2025782761461435,1987857224518460,
    1952789689589328,1931572849402157,1961687554607954,2009977119985353,2085986418541290,
    2214546375783186,2302892276023842,2354984473673364,2385603970506619,2390244153116434,
    2367632312441434,2318105799366573,2331885318083980,1834704440245501,2103974231297317,
    2098587897395054,2086406195933889,2056306283158696,2030848550535190,2012346021999099,
    2004533804080309,1999887301803479,1999900590264681,1999898757521234,2000049434505911,
    2000150671771910,2000147891866517,2000101028096185,2000056863830828,2000028479424054,
    2000013241394500,2000005854317198,2000002493583641,2000001030031213,2000000413926108,
    2000000162057794,2000000061856908,2000000023026798,2000000008361861,2000000002962557,
    2000000001024188,2000000000345527,2000000000113761,2000000000036553,2000000000011460,
    2000000000003503,2000000000001042,2000000000000300,2000000000000081],
   [2000000000000020,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
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
private def phb_m4_r192_5 : List ℤ := uOfNatHb pb_m4_r192_5
private def pvi_m4_r192_5 : List ℤ := bDec bZ pv_m4_r192_5_0
private def pvo_m4_r192_5 : List ℤ := bDec bZ pv_m4_r192_5_1
private def pb_m4_r192_6 : List ℕ := pNatCat
  [
   [3234048000000,4549813529720,5543186122511,6367032000000,7080893854445,7715471377531,
    8289096525544,8813774900506,9297888000000,9747569098141,10167471490311,10561228296573,
    10931743023104,11281381387084,11612102604066,11925552000000,12223128043791,12506031953421,
    12775305122069,13031857838500,13276491661003,13509917082997,13732767650375,13945611366874,
    14148960000000,14343276742721,14528982573739,14706461577578,14876065425865,15038117176545,
    15192914514256,15340732529530,15481826114925,15616432040967,15744770762911,15867048000000,
    15983456121413,16094175367231,16199374927893,16299213901810,16393842147608,16483401044921,
    16568024175501,16647837934686,16722962081774,16793510236657,16859590329016,16921305005560,
    16978752000000,17032024469897,17081211303953,17126397402864,17167663936505,17205088579842,
    17238745729696,17268706704252,17295039926967,17317811096348,17337083342931,17352917374615,
    17365371611408,17374502310510,17380363682593,17383008000000],
   [17382485697579,17378845466736,17372134343266,17362397789475,17349679771027,17334022828936,
    17315468147084,17294055615588,17269823890335,17242810448969,17213051643587,17180582750369,
    17145438016383,17107650703729,17067253131240,17024276713878,16978752000000,16930708706613,
    16880175752781,16827181291272,16771752738573,16713916803379,16653699513644,16591126242277,
    16526221731589,16459010116533,16389514946840,16317759208093,16243765341816,16167555264627,
    16089150386508,16008571628246,15925839438091,15840973807667,15753994287186,15664920000000,
    15573769656518,15480561567541,15385313657017,15288043474278,15188768205760,15087504686246,
    14984269409650,14879078539371,14771947918231,14662893078019,14551929248670,14439071367077,
    14324334085576,14207731780100,14089278558029,13968988265751,13846874495932,13722950594533,
    13597229667560,13469724587580,13340448000000,13209412329118,13076629783977,12942112363996,
    12805871864422,12667919881586,12528267817987,12386926887198],
   [12243908118612,12099222362033,11952880292109,11804892412630,11655269060678,11504020410645,
    11351156478132,11196687123712,11040622056585,10882970838112,10723742885245,10562947473852,
    10400593741931,10236690692744,10071247197839,9904272000000,9735773716088,9565760839823,
    9394241744466,9221224685430,9046717802822,8870729123899,8693266565469,8514337936212,
    8333950938948,8152113172829,7968832135483,7784115225091,7597969742410,7410402892744,
    7221421787857,7031033447839,6839244802922,6646062695246,6451493880583,6255545030008,
    6058222731540,5859533491729,5659483737207,5458079816199,5255328000000,5051234484408,
    4845805391129,4639046769140,4430964596021,4221564779261,4010853157521,3798835501874,
    3585517517016,3370904842442,3155003053599,2937817663014,2719354121386,2499617818665,
    2278614085096,2056348192243,1832825353993,1608050727528,1382029414286,1154766460891,
    926266860070,696535551540,465577422889,233397310421]]
private def pv_m4_r192_6_0 : List ℕ := pNatCat
  [
   [2031839329051724,2039830494447363,2013447514973938,1966752641290632,2036040053060401,
    2008414485141762,1984838541796406,1963572651665288,1961547934699544,1981263673779642,
    2012955893859028,2039503146889427,2045489839042921,2025782761461435,1987857224518460,
    1952789689589328,1931572849402157,1961687554607954,2009977119985353,2085986418541290,
    2214546375783186,2302892276023842,2354984473673364,2385603970506619,2390244153116434,
    2367632312441434,2318105799366573,2331885318083980,1834704440245501,2103974231297317,
    2098587897395054,2086406195933889,2056306283158696,2030848550535190,2012346021999099,
    2004533804080309,1999887301803479,1999900590264681,1999898757521234,2000049434505911,
    2000150671771910,2000147891866517,2000101028096185,2000056863830828,2000028479424054,
    2000013241394500,2000005854317198,2000002493583641,2000001030031213,2000000413926108,
    2000000162057794,2000000061856908,2000000023026798,2000000008361861,2000000002962557,
    2000000001024188,2000000000345527,2000000000113761,2000000000036553,2000000000011460,
    2000000000003503,2000000000001042,2000000000000300,2000000000000081],
   [2000000000000020,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
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
private def pv_m4_r192_6_1 : List ℕ := pNatCat
  [
   [2031710448873110,2039871240005258,2013813551993583,1966599596643482,2035766982724866,
    2008784277368178,1985205953220906,1963788044541572,1961404269034407,1980782038990791,
    2012371047319687,2039150778677572,2045619883753311,2026413020864577,1988695923134997,
    1953470113707955,1931488021270613,1960735667053487,2008410516597638,2083326831399605,
    2211641219136400,2300933783190761,2353771847449124,2385027215112173,2390409247090013,
    2368589351880314,2318512634136032,2338916133240380,1838119526398629,2100056194753586,
    2098804399937071,2087035483290865,2057153792145029,2031530811718617,2012760142878198,
    2004732636191666,1999962397302557,1999901033457261,1999896391908615,2000045332758683,
    2000149013131075,2000148670874444,2000102520253988,2000058069842213,2000029211484257,
    2000013623914151,2000006037152959,2000002576089025,2000001065766061,2000000428904689,
    2000000168157524,2000000064274533,2000000023960212,2000000008713067,2000000003091375,
    2000000001070257,2000000000361593,2000000000119226,2000000000038366,2000000000012046,
    2000000000003688,2000000000001099,2000000000000317,2000000000000086],
   [2000000000000021,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
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
private def phb_m4_r192_6 : List ℤ := uOfNatHb pb_m4_r192_6
private def pvi_m4_r192_6 : List ℤ := bDec bZ pv_m4_r192_6_0
private def pvo_m4_r192_6 : List ℤ := bDec bZ pv_m4_r192_6_1
private def pb_m4_r192_7 : List ℕ := pNatCat
  [
   [129619814400000,182355359375321,222169478122943,255189009600000,283800409641195,
    309234114015658,332224862829725,353253837533346,372656966400000,390680069483277,
    407509649668623,423291321476344,438141456689367,452154872645535,465410094201697,
    477973065600000,489899837115477,501238553256774,512030952795401,522313519871562,
    532118380735988,541474011782616,550405805368379,558936526937393,567086688000000,
    574874853211651,582317895290661,589431208246287,596228886987117,602723879592792,
    608928117187186,614852625328310,620507620044526,625902591037724,631046374098085,
    635947214400000,640612822050930,645050421027020,649266792437702,653268312906464,
    657060988728648,660650486363672,664042159733933,667241074732141,670252031280270,
    673079583234380,675728056388518,678201564796353,680504025600000,682639172530655,
    684610568224595,686421615480009,688075567564689,689575537671281,690924507605334,
    692125335781434,693180764594120,694093427222759,694865853923033,695500477851975,
    695999640468467,696365596546744,696600518836521,696706502400000],
   [696685568652946,696539669134364,696270689026915,695880450448121,695370715530491,
    694743189307044,693999522417177,693141313646511,692170112313102,691087420511338,
    689894695223876,688593350311057,687184758386477,685670252586660,684051128242115,
    682328644456491,680504025600000,678578462722780,676553114893454,674429110467706,
    672207548291354,669889498842051,667476005313442,664968084645318,662366728503067,
    659672904209469,656887555631665,654011604025956,651045948842877,647991468494826,
    644849021088398,641619445123398,638303560160401,634902167458581,631416050585449,
    627845976000000,624192693610704,620456937309667,616639425484208,612740861507029,
    608761934206076,604703318315119,600565674906035,596349651803689,592055883984292,
    587684993958026,583237592136717,578714277187263,574115636371501,569442245873142,
    564694671112404,559873467048878,554979178473199,550012340288012,544973477778730,
    539863106874525,534681734400000,529429858317944,524107967963567,518716544270566,
    513256059989396,507726979898059,502129761005739,496464852749567],
   [490732697184828,484933729168846,479068376538837,473137060283951,467140194711753,
    461078187609354,454951440399412,448760348291198,442505300426925,436186680023522,
    429804864510021,423360225660740,416853129724406,410283937549376,403653004705106,
    396960681600000,390207313595775,383393241118478,376518799766251,369584320413998,
    362590129315030,355536548199821,348423894371956,341252480801391,334022616215098,
    326734605185199,319388748214674,311985341820714,304524678615815,297007047386680,
    289432733171002,281802017332200,274115177632179,266372488302171,258574220111731,
    250720640435931,242812013320830,234848599547257,226830656692976,218758439193269,
    210632198400000,202452182639200,194218637267221,185931804725501,177591924593987,
    169199233643253,160753965885351,152256352623441,143706622500230,135105001545250,
    126451713221027,117746978468155,108991015749316,100184041092279,91326268131898,82417908151148,
    73459170121223,64450260740716,55391384473918,46282743588254,37124538190882,27916966264476,
    18660223702217,9354504342018]]
private def pv_m4_r192_7_0 : List ℕ := pNatCat
  [
   [1968289551126890,2039871240005258,2013813551993583,2033400403356518,2035766982724866,
    2008784277368178,1985205953220906,1963788044541572,1961404269034407,1980782038990791,
    2012371047319687,2039150778677572,2045619883753311,2026413020864577,1988695923134997,
    1953470113707955,1931488021270613,1960735667053487,2008410516597638,2083326831399605,
    2211641219136400,2300933783190761,2353771847449124,2385027215112173,2390409247090013,
    2368589351880314,2318512634136032,2338916133240380,2161880473601371,2100056194753586,
    2098804399937071,2087035483290865,2057153792145029,2031530811718617,2012760142878198,
    2004732636191666,1999962397302557,1999901033457261,1999896391908615,2000045332758683,
    2000149013131075,2000148670874444,2000102520253988,2000058069842213,2000029211484257,
    2000013623914151,2000006037152959,2000002576089025,2000001065766061,2000000428904689,
    2000000168157524,2000000064274533,2000000023960212,2000000008713067,2000000003091375,
    2000000001070257,2000000000361593,2000000000119226,2000000000038366,2000000000012046,
    2000000000003688,2000000000001099,2000000000000317,2000000000000086],
   [2000000000000021,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
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
private def pv_m4_r192_7_1 : List ℕ := pNatCat
  [
   [1954600203053520,2000919330316623,2012934680325784,2007102193563426,2018786375226476,
    2029992019382876,2033394927402404,2027709681228950,2012430099370753,1991679304563340,
    1970588425062020,1963465651924475,1963596442088584,1989097280048672,2014295751382168,
    2029151748695217,2055663399214744,2034055168832187,1995911829711867,1980491117824742,
    1942892053322862,1946807515929744,1908154872337364,2030335216555063,2064559864268421,
    2144711900531558,2278927560843727,2322020580595786,2316055274489500,2358262342458071,
    2403066697315429,2385303893343224,2310422570998054,2230416974112377,2174341125201786,
    2138716617738056,2111133368399818,2084430220612665,2058415502771543,2036108429871354,
    2019788788252603,2009568261626497,2004060012141968,2001519760121019,2000540401158774,
    2000237897606260,2000162577576864,2000134829604989,2000106196510217,2000074918891067,
    2000047597315422,2000027677960705,2000014958642479,2000007608846097,2000003679231059,
    2000001704552923,2000000761211966,2000000329176547,2000000138307810,2000000056599614,
    2000000022597902,2000000008812859,2000000003359698,2000000001252694],
   [2000000000456982,2000000000163141,2000000000056999,2000000000019491,2000000000006521,
    2000000000002131,2000000000000679,2000000000000209,2000000000000061,2000000000000016,
    2000000000000003,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
private def phb_m4_r192_7 : List ℤ := uOfNatHb pb_m4_r192_7
private def pvi_m4_r192_7 : List ℤ := bDec bZ pv_m4_r192_7_0
private def pvo_m4_r192_7 : List ℤ := bDec bZ pv_m4_r192_7_1
private def pwalks_m4_r192 : List RkmSegWalk := [
  ⟨phb_m4_r192_0, pvi_m4_r192_0, pvo_m4_r192_0⟩,
  ⟨phb_m4_r192_1, pvi_m4_r192_1, pvo_m4_r192_1⟩,
  ⟨phb_m4_r192_2, pvi_m4_r192_2, pvo_m4_r192_2⟩,
  ⟨phb_m4_r192_3, pvi_m4_r192_3, pvo_m4_r192_3⟩,
  ⟨phb_m4_r192_4, pvi_m4_r192_4, pvo_m4_r192_4⟩,
  ⟨phb_m4_r192_5, pvi_m4_r192_5, pvo_m4_r192_5⟩,
  ⟨phb_m4_r192_6, pvi_m4_r192_6, pvo_m4_r192_6⟩,
  ⟨phb_m4_r192_7, pvi_m4_r192_7, pvo_m4_r192_7⟩
  ]
private def pb_m4_r256_0 : List ℕ := pNatCat
  [
   [416613693770081,550050637902044,622474658312310,654853002415382,653557545157753,
    618787707863961,544631287631461,410878325061419]]
private def pv_m4_r256_0_0 : List ℕ := [3000000000000000]
private def pv_m4_r256_0_1 : List ℕ := pNatCat
  [
   [2702984256310219,2603810897418897,2342308140955836,2146380450687024,2049380354168685,
    2013297720655617,2002824871697929,2000452643529821,2000047869025060]]
private def phb_m4_r256_0 : List ℤ := uOfNatHb pb_m4_r256_0
private def pvi_m4_r256_0 : List ℤ := bDec bZ pv_m4_r256_0_0
private def pvo_m4_r256_0 : List ℤ := bDec bZ pv_m4_r256_0_1
private def pb_m4_r256_1 : List ℕ := pNatCat
  [
   [278777984000000,380986175167020,449904153590915,499620709254008,535617051877776,
    560644192301257,576232200518705,583236131789884,582063796671299,572764372432202,
    555031997027606,528125535349588,490653706723639,440054312246809,371147730704189,
    270487382817948]]
private def pv_m4_r256_1_0 : List ℕ := pNatCat
  [
   [2702984256310219,2603810897418897,2342308140955836,2146380450687024,2049380354168685,
    2013297720655617,2002824871697929,2000452643529821,2000047869025060]]
private def pv_m4_r256_1_1 : List ℕ := pNatCat
  [
   [2132825577390440,2289623743148732,2428073882429479,2493854407066575,2470198171803399,
    2380194004434947,2265350876266020,2161325703659327,2085822777427266,2039982825890167,
    2016270004533152,2005746654866478,2001742696875619,2000445766171350,2000093347694020,
    2000015122660342,2000001645057937]]
private def phb_m4_r256_1 : List ℤ := uOfNatHb pb_m4_r256_1
private def pvi_m4_r256_1 : List ℤ := bDec bZ pv_m4_r256_1_0
private def pvo_m4_r256_1 : List ℤ := bDec bZ pv_m4_r256_1_1
private def pb_m4_r256_2 : List ℕ := pNatCat
  [
   [256291908248416,356045792403537,428132341329112,485097658180981,531868427957929,
    570997610570527,604012075506039,631909077657559,655379177279838,674920030554009,
    690899947059713,703595795291777,713216710464982,719919401862307,723818181558152,
    724991468876423,723485773650124,719317713999680,712474326885131,702911696155502,
    690551693624078,675276345597161,656918919036534,635250124667680,609956569402760,
    580606116672889,546589579940446,507016020092156,460507111169657,404738116379811,
    335189177027923,240273663982890]]
private def pv_m4_r256_2_0 : List ℕ := pNatCat
  [
   [2132825577390440,2289623743148732,2428073882429479,2493854407066575,2470198171803399,
    2380194004434947,2265350876266020,2161325703659327,2085822777427266,2039982825890167,
    2016270004533152,2005746654866478,2001742696875619,2000445766171350,2000093347694020,
    2000015122660342,2000001645057937]]
private def pv_m4_r256_2_1 : List ℕ := pNatCat
  [
   [2000245918499167,2001250975448825,2004383756300512,2012161531261894,2028313739857944,
    2057088626417909,2101642387824329,2161894770708762,2232825186036058,2304362074521056,
    2363485433461863,2398056285207028,2400843457751151,2371932829998176,2318444573549231,
    2251812000428707,2183986004069502,2124212496420349,2077454045433826,2044572256497622,
    2023641499324914,2011537300085410,2005168008901426,2002118301540607,2000791319858154,
    2000268002923961,2000081722237967,2000022226913058,2000005321531831,2000001099874317,
    2000000190185023,2000000025962710,2000000002425385]]
private def phb_m4_r256_2 : List ℤ := uOfNatHb pb_m4_r256_2
private def pvi_m4_r256_2 : List ℤ := bDec bZ pv_m4_r256_2_0
private def pvo_m4_r256_2 : List ℤ := bDec bZ pv_m4_r256_2_1
private def pb_m4_r256_3 : List ℕ := pNatCat
  [
   [187000951466496,261872087012113,317546387919473,362985285629924,401693444589366,
    435484135380371,465443390725646,492284250198246,516505505680016,538472672792532,
    558463279897195,576694018094479,593337923987833,608535739100696,622403693617303,
    635039002266533,646523844600536,656928310929892,666312623888137,674728841055521,
    682222178223551,688832050239508,694592898066162,699534851484206,703684263564987,
    707064143659145,709694508912072,711592669400204,712773458331265,713249415991873,
    713030933998243,712126364726849,710542099439117,708282617468344,705350507830716,
    701746463691594,697469249206175,692515637304560,686880315945648,680555759152453,
    673532057676444,665796702305640,657334310473566,648126283722960,638150379410673,
    627380174339849,615784390067875,603326038384115,589961329188878,575638259022075,
    560294762324111,543856251607442,526232283867638,507311944827422,486957294753020,
    464993779948650,441195694628170,415263157258465,386783619101207,355162894747327,
    319489651378064,278232350316683,228412561478339,162368765263882]]
private def pv_m4_r256_3_0 : List ℕ := pNatCat
  [
   [2000245918499167,2001250975448825,2004383756300512,2012161531261894,2028313739857944,
    2057088626417909,2101642387824329,2161894770708762,2232825186036058,2304362074521056,
    2363485433461863,2398056285207028,2400843457751151,2371932829998176,2318444573549231,
    2251812000428707,2183986004069502,2124212496420349,2077454045433826,2044572256497622,
    2023641499324914,2011537300085410,2005168008901426,2002118301540607,2000791319858154,
    2000268002923961,2000081722237967,2000022226913058,2000005321531831,2000001099874317,
    2000000190185023,2000000025962710,2000000002425385]]
private def pv_m4_r256_3_1 : List ℕ := pNatCat
  [
   [2000000028214406,2000000015885901,2000000039807904,2000000139883593,2000000285298750,
    2000000429120033,2000000536050671,2000000543724760,2000000377600023,2000000069993078,
    1999999873613540,2000000357074040,2000002878874571,2000011424707809,2000037706797910,
    2000113044852416,2000312865777948,2000801521008044,2001903890189366,2004202083739186,
    2008637408796794,2016571186765960,2029733431674627,2049985240270271,2078859409990456,
    2116930280220925,2163175226566435,2214574375673140,2266191685953700,2311858059944419,
    2345363279738666,2361844727287890,2358943342296967,2337348754835714,2300563201062714,
    2253987428448579,2203651197973037,2154988991510611,2111984092804550,2076827495987171,
    2050050066216877,2030959990684917,2018181981313406,2010134781193532,2005359912189613,
    2002688143824559,2001277669058878,2000575049846493,2000244841654420,2000098500550534,
    2000037388718289,2000013367207308,2000004491977405,2000001415287692,2000000416816123,
    2000000114320495,2000000029065941,2000000006810913,2000000001459953,2000000000283445,
    2000000000049160,2000000000007463,2000000000000958,2000000000000096],
   [2000000000000006]]
private def phb_m4_r256_3 : List ℤ := uOfNatHb pb_m4_r256_3
private def pvi_m4_r256_3 : List ℤ := bDec bZ pv_m4_r256_3_0
private def pvo_m4_r256_3 : List ℤ := bDec bZ pv_m4_r256_3_1
private def pb_m4_r256_4 : List ℕ := pNatCat
  [
   [146472761147473,205929634908576,250723279175199,287790970519649,319836494016131,
    348254664994100,373878800500414,397254891246261,418764269668061,438686084407046,
    457232193003165,474568050908444,490825915086167,506113562991555,520520261381495,
    534120977783360,546979429445850,559150340149002,570681143247158,581613288825528,
    591983262199662,601823388221434,611162474134239,620026329003333,628438187578414,
    636419059293861,643988018000639,651162444316847,657958229758926,664389949787729,
    670471011377176,676213779552146,681629686450243,686729325770663,691522534932765,
    696018466840931,700225652814034,704152057967366,707805130117203,711191843101863,
    714318735269472,717191943764995,719817235152122,722200032825395,724345441601174,
    726258269820291,727943049248365,729404053020312,730645311842097,731670628634400,
    732483591778578,733087587104518,733485808742071,733681268942329,733676806961547,
    733475097088870,733078655888749,732489848719964,731710895585182,730743876357918,
    729590735427402,728253285796154,726733212659851,725032076494316],
   [723151315670010,721092248610296,718856075505757,716443879593122,713856628003614,
    711095172181895,708160247873099,705052474671695,701772355122014,698320273356186,
    694696493250891,690901156079578,686934277631723,682795744764980,678485311349817,
    674002593559121,669347064447268,664518047754040,659514710858322,654336056794506,
    648980915230566,643447932290576,637735559085461,631842038793486,625765392105643,
    619503400819903,613053589331078,606413203718496,599579188080090,592548157696731,
    585316368531822,577879682474970,570233527620207,562372852723032,554292074798531,
    545985018594983,537444846389909,528663976190271,519633985950677,510345500819040,
    500788059631190,490949955838594,480818046673158,470377522495831,459611625745271,
    448501305408801,437024788041821,425157039390307,412869080566611,400127107793862,
    386891342172370,373114500993209,358739726537252,343697717007098,327902648792501,
    311246203218425,293588495803653,274743686060953,254455874167464,232355825978778,
    207875768978336,180058425736241,147034901677243,103975673214099]]
private def pv_m4_r256_4_0 : List ℕ := pNatCat
  [
   [2000000028214406,2000000015885901,2000000039807904,2000000139883593,2000000285298750,
    2000000429120033,2000000536050671,1999999456275240,1999999622399977,1999999930006922,
    2000000126386460,1999999642925960,2000002878874571,1999988575292191,1999962293202090,
    1999886955147584,2000312865777948,2000801521008044,2001903890189366,2004202083739186,
    2008637408796794,2016571186765960,2029733431674627,2049985240270271,2078859409990456,
    2116930280220925,2163175226566435,2214574375673140,2266191685953700,2311858059944419,
    2345363279738666,2361844727287890,2358943342296967,2337348754835714,2300563201062714,
    2253987428448579,2203651197973037,2154988991510611,2111984092804550,2076827495987171,
    2050050066216877,2030959990684917,2018181981313406,2010134781193532,2005359912189613,
    2002688143824559,2001277669058878,2000575049846493,2000244841654420,1999901499449466,
    1999962611281711,1999986632792692,1999995508022595,1999998584712308,2000000416816123,
    2000000114320495,2000000029065941,2000000006810913,2000000001459953,2000000000283445,
    1999999999950840,2000000000007463,1999999999999042,2000000000000096],
   [2000000000000006]]
private def pv_m4_r256_4_1 : List ℕ := pNatCat
  [
   [2000050649219034,2000036973931371,1999987392434006,1999962345841799,1999988723073379,
    2000026806603312,2000028371444293,1999990226419436,1999973371475904,1999977171296760,
    2000035117667005,2000005837560596,2000030539518015,1999942588588966,2000001886384626,
    1999997499963215,2000020300482362,2000041124378710,1999964436673721,1999976693062163,
    1999997560023742,1999991527593569,2000043531478742,2000027685454831,1999964615704968,
    1999979353001783,1999990032449798,1999985109638363,2000035588080983,2000047396637761,
    1999986931162433,1999969766146296,1999986347219253,1999972119981348,1999989255865711,
    2000048258630107,2000049078616810,1999999520234883,1999986786384316,1999987688101376,
    1999955229809180,1999949082701073,2000004482231763,2000045379437754,2000033299015107,
    2000028199174427,2000047976725581,2000032318028798,1999974006989177,1999940620420992,
    1999949037948435,1999943301719544,1999912359139324,1999923006035828,2000010932576232,
    2000116171017268,2000142008424464,2000002853730021,1999593716234212,1998819987264285,
    1997809090981762,1997206998540971,1998352969007137,2003226067866504],
   [2014178067932350,2033476715765870,2062676105564099,2101926185003216,2149469219017724,
    2201585090903997,2253086793128263,2298242696754642,2331856749901264,2350221941148708,
    2351734255469565,2337056990476805,2308832779744610,2271043814227330,2228199773438049,
    2184559506484507,2143554090090567,2107493891693653,2077549442727583,2053930483764724,
    2036164098259562,2023384771809590,2014579242224085,2008760807686754,2005071868228361,
    2002827340979461,2001516793693507,2000782628495803,2000388155696044,2000184934435547,
    2000084592178040,2000037125882757,2000015623519607,2000006299945332,2000002432309626,
    2000000898355376,2000000317092478,2000000106834220,2000000034307462,2000000010481834,
    2000000003039945,2000000000834426,2000000000215916,2000000000052379,2000000000011816,
    2000000000002446,2000000000000456,2000000000000075,2000000000000010,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def phb_m4_r256_4 : List ℤ := uOfNatHb pb_m4_r256_4
private def pvi_m4_r256_4 : List ℤ := bDec bZ pv_m4_r256_4_0
private def pvo_m4_r256_4 : List ℤ := bDec bZ pv_m4_r256_4_1
private def pb_m4_r256_5 : List ℕ := pNatCat
  [
   [120395144000000,169599349998471,206901361811379,237968526812500,265005292923862,
    289146774404432,311069931722470,331217554114662,349898387250000,367338085715612,
    383707647383932,399140422392030,413742855711579,427601575432316,440788241475199,
    453362964125000,465376777053232,476873466466290,487890950411673,498462336690121,
    508616746569084,518379964818732,527774958916640,536822298296676,545540496250000,
    553946291273808,562054880511227,569880114915566,577434663560396,584730152871655,
    591777285320091,598585941171076,605165266166096,611523747450175,617669279621844,
    623609222437500,629350451428409,634899402469966,640262111166880,645444247775611,
    650451148269427,655287842056512,659959076783438,664469340591688,668822882141176,
    673023728669881,677075702321112,680982434938240,684747381500000,688373832346737,
    691864924328682,695223650990769,698452871894427,701555321164540,704533615339319,
    707390260591732,710127659383266,712748116603947,715253845246587,717646971657968,
    719929540405156,722103518791067,724170801049912,726133212250000],
   [727992511928639,729750397481430,731408507326065,732968423858841,734431676220364,
    735799742885382,737074054090340,738255994110994,739346903401343,740348080604139,
    741260784442343,742086235500108,742825617901134,743480080891577,744050740334147,
    744538680119422,744944953500000,745270584352597,745516568372856,745683874207216,
    745773444525901,745786197040749,745723025471351,745584800462688,745372370457249,
    745086562524380,744728183149419,744298018985005,743796837566776,743225387995505,
    742584401587613,741874592495835,741096658301728,740251280581564,739339125447090,
    738360844062500,737317073138915,736208435407562,735035540072766,733798983245823,
    732499348360740,731137206572755,729713117140526,728227627792807,726681275080369,
    725074584713912,723408071888638,721682241596132,719897588924166,718054599344994,
    716153748992679,714195504929964,712180325405178,710108660099622,707980950365872,
    705797629457416,703559122750000,701265847955051,698918215325547,696516627854621,
    694061481467258,691553165205350,688992061406404,686378545876167],
   [683712988055425,680995751181216,678227192442684,675407663131803,672537508789164,
    669617069345035,666646679255879,663626667636513,660557358388067,657439070321926,
    654272117279797,651056808250052,647793447480492,644482334587667,641123764662880,
    637718028375000,634265412070201,630766197868745,627220663758905,623629083688151,
    619991727651675,616308861778372,612580748414353,608807646204077,604989810169202,
    601127491785209,597220939055899,593270396585824,589276105650724,585238304266039,
    581157227253565,577033106306306,572866170051594,568656644112522,564404751167758,
    560110711009784,555774740601612,551397054132032,546977863069428,542517376214228,
    538015799750000,533473337293266,528890189942066,524266556323292,519602632638859,
    514898612710735,510154688024852,505371047773960,500547878899433,495685366132066,
    490783692031899,485843037027080,480863579451824,475845495583456,470788959678605,
    465694144008543,460561218893706,455390352737426,450181712058881,444935461525302,
    439651763983445,434330780490358,428972670343452,423577591109910],
   [418145698655435,412677147172375,407172089207218,401630675687500,396053055948118,
    390439377757088,384789787340732,379104429408348,373383447176337,367626982391833,
    361835175355829,356008164945826,350146088638001,344249082528922,338317281356820,
    332350818522416,326349826109327,320314434904059,314244774415598,308140972894600,
    302003157352207,295831453578481,289625986160478,283386878499962,277114252830774,
    270808230235865,264468930663989,258096472946087,251690974811340,245252552902931,
    238781322793492,232277399000270,225740895000000,219171923243497,212570595169985,
    205937021221147,199271310854920,192573572559043,185843913864340,179082441357775,
    172289260695265,165464476614254,158608192946072,151720512628064,144801537715503,
    137851369393297,130870107987478,123857852976502,116814703002336,109740755881364,
    102636108615093,95500857400684,88335097641287,81138923956215,73912430190930,66655709426867,
    59368853991088,52051955465775,44705104697558,37328391806696,29921906196097,22485736560192,
    15019970893657,7524696500000]]
private def pv_m4_r256_5_0 : List ℕ := pNatCat
  [
   [2000050649219034,2000036973931371,1999987392434006,1999962345841799,1999988723073379,
    1999973193396688,2000028371444293,2000009773580564,2000026628524096,1999977171296760,
    1999964882332995,2000005837560596,2000030539518015,1999942588588966,2000001886384626,
    2000002500036785,1999979699517638,1999958875621290,2000035563326279,1999976693062163,
    1999997560023742,2000008472406431,2000043531478742,2000027685454831,2000035384295032,
    1999979353001783,1999990032449798,2000014890361637,1999964411919017,1999952603362239,
    1999986931162433,1999969766146296,1999986347219253,2000027880018652,2000010744134289,
    1999951741369893,1999950921383190,1999999520234883,2000013213615684,2000012311898624,
    2000044770190820,2000050917298927,1999995517768237,2000045379437754,1999966700984893,
    2000028199174427,2000047976725581,2000032318028798,2000025993010823,2000059379579008,
    2000050962051565,2000056698280456,2000087640860676,2000076993964172,2000010932576232,
    1999883828982732,1999857991575536,1999997146269979,1999593716234212,2001180012735715,
    2002190909018238,2002793001459029,2001647030992863,2003226067866504],
   [2014178067932350,2033476715765870,2062676105564099,2101926185003216,2149469219017724,
    2201585090903997,2253086793128263,2298242696754642,2331856749901264,2350221941148708,
    2351734255469565,2337056990476805,2308832779744610,2271043814227330,2228199773438049,
    2184559506484507,2143554090090567,2107493891693653,2077549442727583,2053930483764724,
    2036164098259562,2023384771809590,2014579242224085,2008760807686754,2005071868228361,
    2002827340979461,1998483206306493,2000782628495803,2000388155696044,2000184934435547,
    2000084592178040,2000037125882757,2000015623519607,2000006299945332,1999997567690374,
    1999999101644624,1999999682907522,2000000106834220,2000000034307462,2000000010481834,
    2000000003039945,1999999999165574,1999999999784084,1999999999947621,1999999999988184,
    2000000000002446,2000000000000456,2000000000000075,2000000000000010,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m4_r256_5_1 : List ℕ := pNatCat
  [
   [2000025023965157,1999976140185455,2000009659988635,2000004929371464,2000052743331630,
    2000002222831560,2000048575132718,2000026080364960,2000039061949801,1999978177221126,
    2000002661472648,2000022492144893,1999997211819926,1999941612466314,1999943908893771,
    2000009765282606,2000034171200694,1999994321446947,2000000024753586,2000019866476622,
    1999996580018688,1999999461898145,2000000186335059,2000001247357140,1999959444766106,
    2000032681799067,1999994518772246,2000007357788965,1999956882993782,1999977492094950,
    2000031031136519,1999994145930469,1999956126381725,2000021863593929,1999950603398393,
    2000027041643895,1999876417738069,2000186540549314,1999809062812485,2000227518527840,
    1999877175255345,1999995757763568,2000207713397991,1999736481852646,2000331271415653,
    1999825240870496,1999901453295132,2000183415828381,1999781897459119,2000030933316385,
    2000075050802687,1999861617625602,2000131873109678,2000007081038657,1999760067713458,
    2000133048697663,2000131245458776,1999655645918611,1999926826440659,2000473212241308,
    2000029083154131,1999500085037454,1999924485255922,2000755138179898],
   [2000009968273197,1999609321684037,1999116309652977,2001199106283715,2000197327584266,
    2000618995161569,1998360393184124,1999437775208491,2000823463879767,2001068218210359,
    2001696232711197,1999391179890327,1997829505006759,1998492479419217,1998975231477426,
    2001137326807041,2003725658408814,2003416634133999,2001544254074832,1998743095813041,
    1993844716319754,1989599491270336,1990281380906229,1997551321416892,2013265122806351,
    2040605433116038,2080029460369386,2128110131117425,2180616392856813,2233607022178308,
    2281910432912951,2319468044520595,2341999199081627,2348449853036616,2339967448817191,
    2318502364164218,2286635799788619,2247935173383411,2206616151863594,2166508028147901,
    2130194343113180,2098885531866788,2072842811525665,2051868070283191,2035572438342514,
    2023440295085284,2014832864652877,2009028473308819,2005305097617909,2003024306850342,
    2001681820160707,2000916676502819,2000491123380653,2000258730967529,2000133737019937,
    2000067562430965,2000033205562774,2000015807552877,2000007262849261,2000003212373032,
    2000001365728143,2000000557804963,2000000218933364,2000000082664005],
   [2000000030078873,2000000010572753,2000000003600590,2000000001191967,2000000000384910,
    2000000000121633,2000000000037705,2000000000011480,2000000000003432,2000000000001005,
    2000000000000284,2000000000000077,2000000000000018,2000000000000003,2000000000000000,
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
private def pv_m4_r256_5_2 : List ℕ := pNatCat
  [
   [2000051241209017,1999992115638793,2000015727301756,2000017537899473,2000010901921868,
    2000010186063302,2000002640418386,1999990388722756,1999972943729547,2000009381500689,
    1999986634348368,2000038823599350,1999993471144359,2000011257891317,1999979431205311,
    2000020839387406,2000039541869543,2000115083902965,1999904445163661,2000129319470335,
    1999851460437288,2000172984319610,1999945156753991,2000021500973324,2000143098917048,
    1999754253964302,2000249950417912,1999807584577336,1999906342631541,2000221975014296,
    1999778007173033,2000060727966421,2000083758332430,1999801995828636,2000158049525016,
    2000074111352767,1999813915119802,2000128716015325,2000016488575352,1999895714096524,
    2000006442033846,2000202132393998,1999658683060237,2000357370032963,1999668829167933,
    2000387721348443,1999408275690197,2000678106306665,1999435993347991,2000207341328166,
    2000178678410733,1999702567485905,2000218479336111,1999603556710507,2000413975174289,
    2000013821497561,1999373466336821,2000545926356238,2000089623811024,1999639920064079,
    2000107898594577,1999885096292741,2000341948307244,2000266450392232],
   [1999277957223579,2000053891962345,2000795771628214,1999765135357131,1999470079306563,
    2000015073384888,2000087522129562,2000377872614666,2000258739500501,1999251151364887,
    1999461878006996,2000798921197633,2000668945141783,1999481309786874,1999324092482563,
    1999841511789232,2000181774708797,2000657614708135,2000672922484354,1999510301571114,
    1998670376578402,1999622715280574,2001049005881693,2001144107623790,2000302466754338,
    1999590344958386,1999020149685099,1998716197305271,1999508797699670,2001235528297505,
    2002256436211482,2001535803561025,1999861034762352,1998447892524093,1997598038134132,
    1997353999265631,1998363383616934,2001094126216208,2004607903221890,2006878252288802,
    2006276272541945,2002392295085759,1995714477529348,1987329094508764,1979373434962125,
    1975478826591047,1980146506497999,1997156573847933,2028105894109447,2071921753704230,
    2125264350807381,2183231307010585,2240021505607301,2289645967461276,2326835072331824,
    2348006128165085,2351919361404144,2339727591988894,2314429451217961,2280005000542532,
    2240574824480896,2199801820716690,2160581742597586,2124955468452799],
   [2094150709115410,2068688223679011,2048521298905069,2033193578805739,2022000749986367,
    2014138064550628,2008817067833898,2005342357018326,2003148868616717,2001807729819329,
    2001011997974099,2000553007170962,2000295204838689,2000154019411654,2000078556404123,
    2000039167272007,2000019084848168,2000009084455713,2000004222178108,2000001915014493,
    2000000847199213,2000000365412034,2000000153605255,2000000062912811,2000000025102055,
    2000000009756331,2000000003693858,2000000001362495,2000000000489694,2000000000171532,
    2000000000058573,2000000000019501,2000000000006331,2000000000002001,2000000000000614,
    2000000000000181,2000000000000050,2000000000000011,2000000000000001,2000000000000000,
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
private def pv_m4_r256_5_3 : List ℕ := pNatCat
  [
   [2000005638373142,2000038915248487,1999996867903905,2000062213488804,1999981478345639,
    2000066350675314,1999909543453946,2000148441173145,1999876508566776,2000054619740859,
    2000102333667283,1999795268824570,2000218877739554,1999936197725870,1999911577178157,
    2000227863814035,1999843471780455,1999979774754716,2000202624928697,1999840722549983,
    1999858344241131,2000291141466974,1999731248492598,2000155607128198,1999882246122371,
    2000393588977904,1999321658944313,2000643915669718,1999540080497928,2000218474481698,
    1999990745335091,1999969894213650,2000261524183927,1999572979207374,2000463233614214,
    1999926909044595,1999646452929197,2000468626332815,1999789221410270,1999988493452957,
    2000277328947082,1999755878895956,2000184595444426,1999992215821731,1999736106775685,
    2000372507673145,1999881628333390,1999633714257375,2000414848376572,1999966226068792,
    1999571675308018,2000282051586143,2000136897932234,1999752938767553,2000095144127122,
    1999994717262079,1999932359058700,2000286548636447,1999852719377642,1999580271716554,
    2000389665147653,2000381457526634,1999490435214853,1999770814103582],
   [2000482004039948,2000087598919072,1999669453168760,1999945382313168,2000054647047037,
    2000077622101356,2000254248285233,1999884313087492,1999461673298004,2000091558396345,
    2000694407016746,1999954657387347,1999231884810712,1999883312790268,2000623664502735,
    2000235537844326,1999638929630465,1999684954443527,1999939542985733,2000168901198381,
    2000458136528494,2000271618212001,1999500267588107,1999327796710347,2000282575372926,
    2000950722942597,2000220458193587,1999179619475184,1999296026599250,2000205981429443,
    2000664407124957,2000424346211557,1999986270985953,1999546277202696,1999249630985871,
    1999596549233071,2000592544289408,2001178677518017,2000472030975861,1999135466850579,
    1998645391296987,1999445977749492,2000598129422434,2001125970713525,2000942508825674,
    2000376500579134,1999548650670949,1998641224001050,1998306268137296,1999178391563406,
    2000983076338390,2002520790884223,2002679907758926,2001315991642046,1999133373266904,
    1997005906539410,1995651912794847,1995789846305840,1998111142463366,2002674761232115,
    2008210736453899,2012159366080212,2011686675831139,2005100398494018],
   [1992854975069761,1977744929041140,1964398102795343,1958353459199824,1964900819670095,
    1987793956086914,2028073109538572,2083391642736888,2148195892588452,2214806222920903,
    2275069648977263,2322037461215136,2351172312988026,2360836604529502,2352095832804426,
    2328055983379554,2293004166110956,2251573792701179,2208070951055568,2166021345010403,
    2127942887441485,2095315209256991,2068697428867548,2047936204257090,2032406902645961,
    2021240823763497,2013507701407294,2008340465410019,2005004058872091,2002919432450229,
    2001657402398052,2000916225478974,2000493500849639,2000259131330164,2000132708411634,
    2000066310999144,2000032337370972,2000015393655665,2000007153983600,2000003245964927,
    2000001437885874,2000000621819820,2000000262497007,2000000108156913,2000000043491028,
    2000000017064929,2000000006533020,2000000002439928,2000000000888886,2000000000315845,
    2000000000109450,2000000000036980,2000000000012177,2000000000003906,2000000000001216,
    2000000000000366,2000000000000104,2000000000000026,2000000000000005,2000000000000000,
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
private def pv_m4_r256_5_4 : List ℕ := pNatCat
  [
   [1999860088793401,2000080043981131,2000054736510590,1999818820239376,2000088809414302,
    2000189275142532,1999767914223181,2000025459072349,2000046850348360,2000299126922232,
    1999398036275221,2000624818669582,1999642779668669,2000314969814276,1999687852172236,
    2000106617290086,2000410084478620,1999391616768943,2000260508052972,2000234757848600,
    1999699553842285,2000195891391245,1999854237403145,2000010081904451,2000315055010092,
    1999614845232884,2000022325642097,2000429279355501,1999637837415504,1999909215336549,
    2000391503865977,1999811516169496,1999922670852184,2000251215612342,1999841164933795,
    1999976602122378,2000163522364151,1999715771105585,1999980813740590,2000375276876370,
    1999797493948693,1999767032652223,2000375349663702,2000008006648617,1999617739965496,
    2000175415166807,2000222997323313,1999719090409493,1999947959606044,2000230970294587,
    1999941974977448,1999987591049319,2000179565475700,1999864295014662,1999877063464585,
    2000308611282105,2000025556867967,1999602625606259,2000137096651064,2000494180581066,
    1999830632510694,1999583400291309,2000243770620013,2000374177777754],
   [1999827983443154,1999775244524414,2000090730023485,2000065944373446,2000011469526124,
    2000076895640794,1999835859252564,1999705122773946,2000200388400833,2000423058860178,
    1999767249456529,1999459278254033,2000197701318562,2000612029602598,1999910453572135,
    1999401788672655,1999933964143124,2000462197398608,2000199913355227,1999798198273020,
    1999794977936743,1999922365278995,2000074666054209,2000296100198600,2000166255564164,
    1999607792568305,1999515763185724,2000274656105583,2000739150703267,2000040340264339,
    1999210719236768,1999558463825085,2000522232628641,2000659554980043,1999911798813503,
    1999419305846789,1999668289253272,2000126641184419,2000342868949559,2000305967661972,
    1999994446229967,1999516784751020,1999453811412813,2000161210857915,2000910155844188,
    2000634472323305,1999511939766713,1998913475829339,1999592015565872,2000699787853388,
    2000971507946218,2000269957696411,1999467190707735,1999231121042322,1999520782238791,
    2000057421685125,2000639107649774,2000923777392020,2000479265267571,1999397299400517,
    1998556929734305,1998857463045002,2000199617565682,2001488710500498],
   [2001695191688147,2000745894987269,1999367024261072,1998322430050514,1998005615485350,
    1998588075099630,2000128851197427,2002272061455294,2003958853339051,2003798435505761,
    2001065352742748,1996538337761266,1992420091698739,1991300916442795,1994796244184120,
    2002575705161091,2012155141220884,2019483276057907,2020203288328176,2011348787920725,
    1992997152997237,1969183904398778,1947468236454999,1937040923843046,1945948567508847,
    1978463257039903,2033582919569774,2105152122743759,2183440845765245,2257533349545738,
    2317729867172860,2357322804352876,2373429454061426,2366887102496204,2341444066441089,
    2302581733728499,2256295552130657,2208084394326975,2162287020847645,2121794611285228,
    2088083227412471,2061461913082602,2041421524308656,2026987526651143,2017013321682156,
    2010385940640702,2006143970477370,2003524451592459,2001961749671933,2001060117184403,
    2000556479300980,2000283878924594,2000140795088039,2000067915678807,2000031872448204,
    2000014555770070,2000006470209680,2000002799834343,2000001179571153,2000000483862400,
    2000000193257512,2000000075155896,2000000028456630,2000000010489800],
   [2000000003764205,2000000001314771,2000000000446926,2000000000147826,2000000000047563,
    2000000000014878,2000000000004519,2000000000001329,2000000000000376,2000000000000099,
    2000000000000023,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
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
private def phb_m4_r256_5 : List ℤ := uOfNatHb pb_m4_r256_5
private def pvi_m4_r256_5 : List ℤ := bDec bZ pv_m4_r256_5_0
private def pvo_m4_r256_5 : List ℤ := bDec bZ pv_m4_r256_5_4
private def pb_m4_r256_6 : List ℕ := pNatCat
  [
   [107965312054405,152217331565901,185853254171807,213941736458225,238452572614994,
    260399174864728,280385411655923,298805933014281,315935689176749,331975467712228,
    347077296615850,361359634583006,374916961502516,387826104324151,400150562719840,
    411943557774223,423250236686790,434109302890822,444554244850520,454614278207734,
    464315079104331,473679362686106,482727345013351,491477115917481,499944942964353,
    508145521498486,516092182037971,523797063604793,531271259602824,538524941388745,
    545567463577586,552407454285596,559052892869112,565511177219077,571789182281003,
    577893311163118,583829539951796,589603457158684,595220298567384,600684978120798,
    606002115387082,611176060057728,616210913861742,621110550222473,625878631935810,
    630518627108662,635033823563163,639427341883934,643702147261940,647861060268346,
    651906766674551,655841826419977,659668681816587,663389665068298,667007005174167,
    670522834276148,673939193505232,677258038373735,680481243756156,683610608496440,
    686647859675408,689594656568551,692452594321261,695223207365803],
   [697907972601892,700508312360563,703025597169130,705461148333290,707816240350922,
    710092103170790,712289924308119,714410850827939,716455991206125,718426417077180,
    720323164877020,722147237388305,723899605195247,725581208054205,727192956185903,
    728735731494585,730210388719034,731617756519953,732958638507893,734233814215541,
    735444040017931,736590050003843,737672556801417,738692252360790,739649808696355,
    740545878591032,741381096264815,742156078009645,742871422792542,743527712828799,
    744125514126900,744665377006709,745147836592392,745573413281410,745942613190848,
    746255928582247,746513838266050,746716807986670,746865290789149,746959727368298,
    747000546401153,746988164863536,746922988331443,746805411267952,746635817296287,
    746414579459637,746142060468291,745818612934612,745444579596344,745020293528694,
    744546078345647,744022248390870,743449108918617,742826956264956,742156078009645,
    741436753128965,740669252139767,739853837235014,738990762411030,738080273586687,
    737122608714723,736117997885375,735066663422477,733968819972194],
   [732824674584498,731634426787510,730398268654813,729116384865813,727788952759213,
    726416142379672,724998116517667,723535030742594,722027033429128,720474265776814,
    718876861822898,717234948448345,715548645377000,713818065167835,712043313200195,
    710224487651948,708361679470432,706454972336059,704504442618441,702510159324861,
    700472184040908,698390570863073,696265366323076,694096609303667,691884330945646,
    689628554545789,687329295445357,684986560908847,682600349992590,680170653402787,
    677697453342545,675180723347408,672620428108888,670016523285412,667368955300084,
    664677661124611,661942568048677,659163593434015,656340644452343,653473617806283,
    650562399432310,647606864184692,644606875499309,641562285036158,638472932299223,
    635338644232327,632159234789433,628934504477751,625664239871870,622348213096982,
    618986181279110,615577885960052,612123052474578,608621389287195,605072587285544,
    601476319027251,597832237936746,594139977448258,590399150090836,586609346510853,
    582770134427009,578881057512397,574941634197606,570951356388300],
   [566909688089983,562816063931971,558669887581708,554470530039660,550217327803952,
    545909580892728,541546550710882,537127457746292,532651479078988,528117745684713,
    523525339512177,518873290310726,514160572182324,509386099828414,504548724458458,
    499647229322603,494680324825869,489646643175476,484544732506137,479373050420294,
    474129956871098,468813706305150,463422438969393,457954171271572,452406785066029,
    446778015715545,441065438754825,435266454951119,429378273521193,423397893219956,
    417322080962679,411147347577418,404869920204019,398485710756788,391990279744387,
    385378794585750,378645981365609,371786068725141,364792722265416,357658967430725,
    350377098303568,342938569038241,335333863722187,327552339192268,319582033613529,
    311409431253588,303019170558291,294393677896022,285512702470059,276352717746356,
    266886139406685,257080286091162,246895971400627,236285553555389,225190163400182,
    213535643707710,201226382374449,188135528281772,174088601203128,158834061160204,
    141985353362034,122890990894741,100279280143147,70863711011247]]
private def pv_m4_r256_6_0 : List ℕ := pNatCat
  [
   [2000139911206599,2000080043981131,2000054736510590,2000181179760624,2000088809414302,
    1999810724857468,1999767914223181,2000025459072349,1999953149651640,2000299126922232,
    2000601963724779,2000624818669582,2000357220331331,2000314969814276,1999687852172236,
    1999893382709914,2000410084478620,1999391616768943,2000260508052972,2000234757848600,
    2000300446157715,2000195891391245,1999854237403145,2000010081904451,2000315055010092,
    2000385154767116,2000022325642097,1999570720644499,1999637837415504,1999909215336549,
    2000391503865977,2000188483830504,1999922670852184,1999748784387658,2000158835066205,
    1999976602122378,2000163522364151,1999715771105585,1999980813740590,2000375276876370,
    2000202506051307,2000232967347777,2000375349663702,1999991993351383,2000382260034504,
    2000175415166807,2000222997323313,2000280909590507,2000052040393956,2000230970294587,
    2000058025022552,2000012408950681,1999820434524300,2000135704985338,1999877063464585,
    1999691388717895,1999974443132033,1999602625606259,1999862903348936,1999505819418934,
    1999830632510694,1999583400291309,2000243770620013,2000374177777754],
   [2000172016556846,1999775244524414,1999909269976515,2000065944373446,2000011469526124,
    1999923104359206,1999835859252564,1999705122773946,2000200388400833,2000423058860178,
    1999767249456529,1999459278254033,2000197701318562,2000612029602598,1999910453572135,
    1999401788672655,1999933964143124,1999537802601392,1999800086644773,1999798198273020,
    1999794977936743,2000077634721005,2000074666054209,2000296100198600,2000166255564164,
    1999607792568305,1999515763185724,1999725343894417,1999260849296733,2000040340264339,
    1999210719236768,2000441536174915,2000522232628641,2000659554980043,1999911798813503,
    1999419305846789,1999668289253272,1999873358815581,2000342868949559,1999694032338028,
    1999994446229967,1999516784751020,1999453811412813,2000161210857915,2000910155844188,
    2000634472323305,2000488060233287,1998913475829339,1999592015565872,2000699787853388,
    2000971507946218,2000269957696411,2000532809292265,1999231121042322,1999520782238791,
    2000057421685125,2000639107649774,2000923777392020,1999520734732429,2000602700599483,
    2001443070265695,2001142536954998,2000199617565682,2001488710500498],
   [2001695191688147,2000745894987269,2000632975738928,2001677569949486,2001994384514650,
    2001411924900370,2000128851197427,2002272061455294,2003958853339051,2003798435505761,
    2001065352742748,2003461662238734,2007579908301261,2008699083557205,2005203755815880,
    2002575705161091,2012155141220884,2019483276057907,2020203288328176,2011348787920725,
    2007002847002763,2030816095601222,2052531763545001,2062959076156954,2054051432491153,
    2021536742960097,2033582919569774,2105152122743759,2183440845765245,2257533349545738,
    2317729867172860,2357322804352876,2373429454061426,2366887102496204,2341444066441089,
    2302581733728499,2256295552130657,2208084394326975,2162287020847645,2121794611285228,
    2088083227412471,2061461913082602,2041421524308656,2026987526651143,2017013321682156,
    2010385940640702,2006143970477370,2003524451592459,2001961749671933,2001060117184403,
    2000556479300980,1999716121075406,1999859204911961,1999932084321193,1999968127551796,
    1999985444229930,2000006470209680,2000002799834343,2000001179571153,2000000483862400,
    1999999806742488,1999999924844104,1999999971543370,2000000010489800],
   [2000000003764205,2000000001314771,2000000000446926,2000000000147826,2000000000047563,
    1999999999985122,1999999999995481,1999999999998671,2000000000000376,1999999999999901,
    2000000000000023,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
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
private def pv_m4_r256_6_1 : List ℕ := pNatCat
  [
   [1999979234690109,2000070818330028,1999978935873444,2000177288565872,2000087168661788,
    1999995153078365,2000015576295864,1999731618458217,2000606819239218,1999955862825293,
    1999886112839658,2000429059037063,2000022033056855,1999717684039035,2000037698079949,
    1999988038850882,1999855441409481,1999559844797434,1999929289475933,2000074794263481,
    2000527017338590,2000377886429019,2000533006079053,2000247039242053,2000291712168567,
    2000433456720585,2000250959530246,1999924705838391,2000010188220110,1999562230794038,
    1999895535092333,2000384610673997,2000117735907910,2000354449484145,1999921301761054,
    1999705667758363,1999957380492147,2000351770733527,2000657377043238,2000118909396365,
    2000213012515989,1999539478275302,2000047103055513,1999942727545825,1999988498427263,
    1999925755655406,2000013431277261,1999958283568060,1999988606815895,2000175446072089,
    2000144223733479,1999848854577348,1999879161712465,1999967380142649,1999979014352531,
    1999938314007169,2000082549786110,2000179098646561,2000174476686021,2000075604435495,
    2000417511427619,2000020809183750,2000177232115892,2000270867063584],
   [2000389113640767,2000237042764643,1999884495343850,2000445818873882,2000219072112396,
    2000029449816173,2000094790245976,2000209298618960,1999310857545819,2000524905137823,
    2000092330447572,2000262124902106,1999193342158562,1999292877344523,2000208396362202,
    1999734534968485,1999738875196011,1999503626933243,2000158302234135,2000128147581052,
    2000385640175142,1999838998129867,1999821149125248,1999876503360333,2000131955868558,
    1999922149390855,2000342260925984,1999464477012752,1999990141934544,1999877080962245,
    2000105146395036,2000097332658881,2000107400520057,1999705624962457,2000455883316143,
    2000295381628404,1999252236502356,1999989643828561,1999233783225777,2000045592861043,
    1999939422871809,1999589621867708,1999796813540515,2000530269207630,2000357283413268,
    2000137441764765,1999686109659111,1999613122875777,1999015386350252,1999301362822249,
    1999625276352787,2001314255808240,1999858695083316,1999498821344840,1999813312236480,
    2000140506767893,2000181005944583,2000292930067105,2000996105374138,1998255725894759,
    1999145691336192,1999653733451035,2000870854530117,2001331601171004],
   [1998068466862970,2001107382255765,1999452418514230,1999914422787339,2001045535411279,
    1998409913325873,2003180291203448,1999683224555281,1996978285618426,2003763926487377,
    1998214026060024,2000694674657532,2000653467943592,1995596093826704,2004579965276629,
    2003646217889092,1994052354522281,2000253788721356,2005821959648984,2000892903368765,
    1999775610544243,1999691354347238,1998214744760617,2004706168958056,2008950135320607,
    1997164229147763,1988078492915758,2002041728127678,2019432927740915,2011043024946533,
    1987658639906378,1983861455826966,2007582642925741,2029336444310786,2023754174891268,
    1997514970334714,1980444294235835,1991017782728241,2021693269647834,2049379541107482,
    2054815202961505,2036704323076570,2009242206325897,1991602792373146,1999173939327773,
    2037309960868884,2100773044632917,2178075662637960,2255393814312264,2319723863866239,
    2362165104071417,2379217571681358,2371794040579679,2343997358272592,2302131437922678,
    2253191143621266,2203225565676631,2156555042757387,2115865895865925,2082515014635064,
    2056716030523249,2037758256026422,2024390604612887,2015253752615785],
   [2009172631465023,2005248714125060,2002823168685243,2001408851343994,2000642957235399,
    2000263473376904,2000094174997247,2000027639436131,2000005494544631,1999999840550563,
    1999999157958236,1999999482748344,1999999781826269,1999999928738759,1999999982750258,
    1999999998113472,2000000001051516,2000000000995983,2000000000570849,2000000000278586,
    2000000000125032,2000000000052709,2000000000020919,2000000000007794,2000000000002716,
    2000000000000881,2000000000000264,2000000000000071,2000000000000016,2000000000000003,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m4_r256_6_2 : List ℕ := pNatCat
  [
   [1999969270612845,1999753471799342,2000296605639482,1999950921873625,1999779586525782,
    2000136177360160,2000273893406400,1999621293267920,1999931131909938,2000159013606873,
    2000474101611758,1999962486803528,1999845143877617,1999941871445853,2000127186569052,
    2000048438127697,2000027906020311,1999864925786448,1999953880845075,2000444528764142,
    2000036616103746,2000033086732312,2000294141000557,1999725967106120,2000189870636496,
    2000014876320098,2000334465599382,1999811543254025,1999893456929827,1999794773323063,
    1999536826716963,1999765136756732,2000060100485046,2000093777975571,2000196518394264,
    2000233755983480,2000263063612339,2000203846666506,2000391994106559,2000478926065595,
    2000574635753863,2000344566428535,2000282866139765,1999651936541141,1999660909365513,
    1999934291949799,2000190963894939,2000494600944094,1999941615762359,2000143915472556,
    1999732274088942,1999909324316214,1999737872374759,2000552965871929,2000048777685916,
    2000568537647184,1999897017101479,2000140138842045,2000462877568299,1999541321012943,
    2000344282140745,1999930824162356,1999878990663625,1999692565166602],
   [2000158352169108,2000040122886982,2000040221071890,1999810508151148,2000363909007709,
    1999953453167987,2000027600252128,1999663435083468,2000317782841578,1999649235317898,
    1999811916489112,2000301554569587,2000199947537685,1999918191334585,1999778778176549,
    2000309364134918,2000273724071300,2000768867766621,1999368595155462,2000145713499846,
    2000421006870876,2000368606923364,2000609256853341,2000052137365128,1999613161341231,
    2000498586237535,2000036099787504,2000277427137829,2000005499439017,2000246096986512,
    1999650732997881,2000487058136203,1999893732435078,1999681639344958,1999679206849855,
    1999075081846384,2000256593967122,1999648816012631,2000277325744098,1999496483832630,
    1999857399172187,2000413496536061,1999684193338530,2000725171264630,1998542228064331,
    2001159683979248,2000279017521299,1998774993104022,2001001721637836,1998911301265966,
    2000501116748439,2000026899168926,1998858309157098,2002830981311677,1997466947492669,
    2000784484124122,2001321487437427,1997712228577220,2002310620155167,1998000187158236,
    1998626557004529,2002120213258556,1997055727565380,2001676788377194],
   [2003141752599595,1996581450818209,2000044554054435,2000775576025182,1997974074844221,
    2002043539505922,1999758835463250,1996379265392353,2002212115602657,2001081640077164,
    1996507138768960,2002089415141125,2003645029124934,1996261640130057,1997730321925203,
    2003030304177678,2000436377669484,1997942422898507,2000173974282648,2000076600850378,
    1999660102019079,2001888753117681,1999434718646809,1995919425854298,2001509193102944,
    2006695902475461,1999055557025606,1991663616706932,2000443885749908,2010729815470063,
    2001958725601001,1987906629353758,1993993447462575,2011478207509944,2011392140596845,
    1992773439539164,1984624647003163,2000651347813710,2018085985513669,2011532870283428,
    1989685110318203,1982184678844236,1999095313314844,2019297184459465,2018282082944210,
    1997014791465214,1979392036720260,1985008693706554,2008798706490239,2027704729578093,
    2024148714190259,2001445582544006,1979094646582147,1975966328703285,1996402880557909,
    2028159273198867,2051519569383242,2052186266905549,2029471259896776,1995875867494824,
    1970214101336036,1969211238112448,2001386263658664,2064741895343114],
   [2148218277601312,2235854013185133,2311828246156816,2364474640854371,2388193865588407,
    2383332879640362,2354767046830055,2309955505915323,2257006124157590,2203101366297929,
    2153517911669069,2111318992120455,2077605724995231,2052077506670995,2033640984283118,
    2020898463897157,2012461885629533,2007116093523734,2003881101615624,2002016475513459,
    2000995588186713,2000466018547439,2000206341680512,2000086225178368,2000033919153057,
    2000012522882102,2000004322366891,2000001387380637,2000000411003640,2000000111126692,
    2000000026961993,2000000005723508,2000000001032421,2000000000165186,2000000000038256,
    2000000000020150,2000000000012289,2000000000006434,2000000000002895,2000000000001148,
    2000000000000409,2000000000000130,2000000000000036,2000000000000007,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m4_r256_6_3 : List ℕ := pNatCat
  [
   [2000238704033878,2000058422279224,2000223696012034,1999683464123523,1999736171425652,
    1999902213637318,2000151680809550,2000215367895226,1999989986088441,1999855927490967,
    1999785068121978,1999840224281207,2000596902015467,1999873909262415,2000085241610442,
    1999916749742918,1999692086771243,1999841020356697,2000103812229817,2000324262800279,
    2000221256748590,1999849908918827,2000034896250406,2000088400386230,2000058791444251,
    1999916554720322,2000202027348785,2000021603517358,1999889383746209,1999909180293155,
    1999840647289310,2000324340085980,1999827731057489,2000370786747990,1999988436756028,
    2000275044059357,1999774223589106,2000187277143023,1999900769758575,2000105290235091,
    2000395473918456,1999815475280575,2000618100756162,1999633053113880,1999893373379588,
    1999841644530803,1999687438128273,1999637161066712,2000010618238149,1999678636278376,
    2000444823676485,2000003917492838,1999975015212569,1999732626093853,2000342070311020,
    2000397713527735,2000347895668070,2000884714559638,2000461115056250,2000457640857772,
    1999600238057163,2000044721453204,1999825914015253,2000345153478301],
   [1999883457298877,2000307411534434,2000491987885733,1999661873488662,1999630581131774,
    2000369111063948,1999588158246428,2000368366479005,1999797905956094,2000204215061114,
    2000332153986938,2000174700557329,1999990608779818,2000297662114565,2000609858844623,
    1999357350289396,2000421048234852,1999775413403298,2000098424763524,2000213431825093,
    1999208266142116,2000396497110352,1999635563681809,2001063959954195,1999481057949211,
    1999767991294785,2000276110844195,1999367724668225,2001179067245956,1999275714861484,
    1999535232742440,2000914998194801,1998146682700158,2002150380341625,1999208784233084,
    1999670704196810,2001424568164733,1997910198246600,2001972085881299,1999636660593156,
    1999636832297688,2002045457260960,1997554664308091,2001891410039483,2001454255058851,
    1997304714846229,2002074610993242,1999734042868892,1999044462855966,2002431059840339,
    1998404181149786,2000219067131630,2002088660065877,1997220806726804,2000702526314187,
    2001468887980487,1996903097078818,2000645985790112,2001597387150534,1997463825416644,
    2000707580753419,2000964359874387,1997788479033634,2001285745185154],
   [2001015552701520,1997836442637924,2001369518849914,2001185470040169,1996711229585480,
    2000649767928112,2003493696678306,1997324824828066,1997344431633480,2003072599308282,
    2000921399216199,1998201768746186,2001398065404551,2000895440152929,1997512738940376,
    1999175435071567,2001202483324316,1999744935963330,1999977349686302,2000643579967716,
    1998293397129131,1999272656569183,2003645898062538,2000698389431404,1994558094147746,
    1998926838441811,2005720721046648,1999794805112948,1992584121066536,2000224981766395,
    2008835714102601,2000478223238989,1989984240913584,1998047084232991,2010642460630135,
    2003840769940145,1988988433276247,1993149142157653,2009825037626531,2009772715055007,
    1992309293910155,1986770146159247,2003057251820957,2015358319113556,2003948372866343,
    1986186524081197,1989298682206774,2009051689780557,2016468344520458,2000394737259480,
    1983061136067086,1988386133059296,2009551085134446,2019120339430281,2004981289816026,
    1984651082624787,1982799753750904,2002116591497839,2021174346501851,2018902843574442,
    1997077676245547,1977771004925020,1980608289003937,2003875602951142],
   [2026892016927418,2029204691047415,2008009763876530,1979720988917496,1966625817910460,
    1980438502599903,2014466888164972,2048363322416707,2061039202012625,2043246203244395,
    2002793254283968,1960475218548284,1940022862786688,1957788153149797,2016788768353496,
    2106700641748537,2208547194868748,2301409638869795,2368499738495200,2400831596997391,
    2397925372036041,2366047844293506,2315146219190636,2255730239706748,2196594513750132,
    2143712617398181,2100157281505212,2066659370283991,2042405686304777,2025792796594691,
    2014997289714542,2008332198687524,2004420266359787,2002237413644380,2001079704552964,
    2000496336427854,2000217178720165,2000090383656341,2000035748210820,2000013426460738,
    2000004784598151,2000001616279901,2000000517083322,2000000156511374,2000000044776383,
    2000000012097893,2000000003085626,2000000000743269,2000000000169454,2000000000036748,
    2000000000007648,2000000000001545,2000000000000305,2000000000000057,2000000000000008,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
    2000000000000000,2000000000000000,2000000000000000,2000000000000000],
   [2000000000000000]]
private def pv_m4_r256_6_4 : List ℕ := pNatCat
  [
   [2000245454592061,2000094034194368,1999998285013060,1999936318473401,2000306154091839,
    1999895997138692,2000414781167449,2000230033234839,1999813307492311,1999939736828073,
    1999992790482624,1999600987479076,1999766132609827,1999938795864770,2000243582693083,
    2000230712579862,2000017756777453,2000042868854177,1999627057010797,2000234469594550,
    1999563353080867,2000074310079618,1999967861198719,2000388477796286,2000292048821243,
    1999835590364587,2000036449088709,1999407961088112,2000344021866579,1999674373981477,
    1999987963676816,2000195695875717,2000143203827601,1999938782402716,2000372985052410,
    1999610726473831,2000182210339229,2000154216126644,1999913162693798,2000199551522690,
    1999990828266021,2000246584197198,1999619047221882,2000245901207888,1999684422640331,
    2000055108481017,1999955089701281,2000159141266751,2000010854541459,2000211489489358,
    2000214596503894,2000060182674557,1999540582385617,2000464000628680,1999769362094087,
    2000288628845188,2000125988161954,1999775622450016,2000737834786738,2000110936179718,
    1999994727844835,1999617742032234,2000239853096833,1999464579335313],
   [1999425577065152,2000492288781486,1999334912139075,2000865564973705,1999354918893360,
    1999791282585861,2000095902991116,1999586672659544,2000428815810141,1999834308542217,
    2001079555572195,2001002252607160,1999351852162667,2001622314229873,1998711356187252,
    2000792150505034,2000430873212632,1998569104445325,2002225366984176,1998716421825148,
    2000578169437905,2000839613949938,1997951330464066,2002102832331596,1999140606817656,
    1999294554178248,2001408924657188,1998027670007249,2001687890594378,2000454475787129,
    1998276062904533,2002212233602488,1998960342080180,1999711516312531,2002747382508265,
    1997685307729251,2000104527367286,2001558979410856,1997833134282884,2001165356648961,
    2000862372689917,1998045397946034,2001375128958446,1999752582314432,1998751477066609,
    2002668289314092,1998980289521750,1997893613094530,2002524781607566,1999422770745192,
    1998297439571156,2002052345583348,1999384745677793,1998611761396363,2002022052552688,
    1999559911594639,1998648852742091,2001832314533694,1999514241092191,1998809310121100,
    2002556209456467,1999896584700399,1997941062885741,2002473547381003],
   [2000923603822905,1997067927345049,2001288223914339,2002563440284084,1997767849586858,
    1999466439271814,2003172332167258,1999553785236214,1997590436245264,2001116567986450,
    2000970568589065,1998700738231215,1999980318577490,1999989733719196,1998533089081735,
    2000598760203652,2001279292378593,1998311654668077,1999316617363461,2002025318095116,
    1999162816552619,1997982520302131,2002914537587513,2002037975215499,1994865905143074,
    1997275851507436,2006059805822389,2002643866600077,1993446873023601,1998341644617075,
    2007729971587114,2001154482111009,1991230721721795,1998858004919026,2009049903350724,
    2000451383951090,1989656429379703,1998969581716935,2011299608651685,2002540915819967,
    1988516632584854,1995499417145495,2010697241822147,2005835649981687,1989311644068737,
    1991140913122612,2008831048943586,2011462265114772,1993954041459641,1986086122328494,
    2001582390733847,2014953830759122,2004007764119418,1986045464536750,1989584341090270,
    2009265276037281,2014859877147526,1997754204381125,1983311892591098,1992948798616123,
    2013366431182695,2015968450930546,1996773698027110,1981418028543950],
   [1990444038969983,2012516234375520,2019539554455013,2002234001240084,1981164957391148,
    1981599614930647,2004042915988639,2024145163257230,2019816750654115,1994609880350332,
    1973682273975981,1978509027488835,2006193995383812,2032226807988707,2032607846381821,
    2004858627429522,1970344662617974,1957249752819076,1978798531858040,2023321876418841,
    2062249960391407,2069032030680471,2035884996141825,1978604753790223,1928137393665922,
    1915020830398504,1955399825901589,2044968585748258,2162278173626517,2278330453593184,
    2367298295319403,2413943292534639,2415784772508722,2380685667745662,2322050747556057,
    2253969436838791,2187821584262149,2130801015732702,2086020131795050,2053519649062782,
    2031538056641316,2017612023699168,2009321743431067,2004675396430432,2002221171389025,
    2000998862840540,2000424842208433,2000170729727788,2000064749039187,2000023141766547,
    2000007782069079,2000002457575776,2000000727221241,2000000201109488,2000000051813647,
    2000000012389740,2000000002737069,2000000000555424,2000000000102777,2000000000017171,
    2000000000002552,2000000000000327,2000000000000033,2000000000000001],
   [2000000000000000]]
private def pv_m4_r256_6_5 : List ℕ := pNatCat
  [
   [2000222397755866,1999833135035617,2000121566605378,2000306754111287,2000201467872316,
    1999851224869671,1999989161972118,2000343434011928,1999826475568565,2000187151014509,
    1999584141622377,2000248086280034,2000254325628911,1999955344929932,2000452511323052,
    1999760404484617,2000462032313296,1999892118067982,2000235872519951,2000061465627607,
    1999778073188023,1999472133755868,2000025220770488,1999703439983663,1999878269780305,
    2000513090167259,1999592526791601,2000271094053237,2000048686828107,2000360706433397,
    1999755980086178,1999937348415556,1999713686467591,1999745720694592,1999915860326713,
    2000408330013721,1999866962064619,2000337614476403,1999980133600083,2000208779938911,
    2000061236315787,1999445884095845,2000372717920149,1999499987607334,1999937188004724,
    2000252131444822,1999799617867215,2000309749172449,1999676367740365,2000702640854563,
    1999342638961034,2000356116603309,2000130793611532,1999457719317456,2000872075423090,
    1999817269661267,1999624246891027,2000781458170196,1999377864477006,2000928080056960,
    1998961706535577,1999972805081835,2000723252512329,1998686778222081],
   [2001680557272410,1998894725792419,1999937038994120,2001728822368434,1998038456087003,
    2001336081734309,1999874385064523,1998918637610043,2001910644874356,1998143034585192,
    2000563367924637,2001446409957739,1998473176018494,2001781808473517,1999762890073537,
    1998808145426358,2001892799031301,1998079153721247,1999804946222711,2001417061205540,
    1998068089800632,2001367976081796,2000431391973335,1997543775327385,2001627319246419,
    1999687756382924,1997934447558209,2002148426601475,1999773893876955,1999412328832681,
    2002639066207589,1999051606052794,1999462473329413,2002060536483923,1998867500382967,
    2000242169597559,2001504736153253,1998090959781151,2000729894026237,2002115590713780,
    1997965301433317,2000145843500866,2001857020466156,1997887777137062,1999905318967610,
    2002191650945251,1998424890395369,1999393780863557,2001451783224795,1998861447046038,
    2000459579671180,2001960402399294,1998323325065091,1999682385921483,2002315519833236,
    1998801228934811,1999101363178669,2002279187508964,1998960682854185,1997992643957270,
    2002443655051974,2000563648049502,1997247527223122,2001225385985386],
   [2002071902727195,1997785786950855,1999448454832119,2002207721177782,1999018308258951,
    1998492062759380,2001528736641634,2000300146165976,1998827427321735,2000582109494023,
    2000083664360082,1999174189338439,2001066737526043,2000271784102602,1998284015520741,
    2001281343388882,2002548024533546,1998003034243900,1998246251970318,2003201714474161,
    2000794284165682,1996549881565461,2001490095542419,2004240153064877,1996979267076394,
    1996395250701457,2005499206609553,2003470520937738,1992876576268244,1997024471711373,
    2007893901729092,2001651802138004,1991189995387158,1999119975564120,2008417109097422,
    1998892069365580,1991150845522916,2002639822014685,2009534332171176,1996441597133203,
    1989705203705239,2003635335193647,2010319621536457,1995851978708283,1989072378108911,
    2004207047377023,2011971621983048,1996840399758996,1987678969627425,2002009298578551,
    2012329225584473,1998720794726196,1986640121749417,1999117768947486,2013838488082127,
    2003938824277455,1986658857605858,1992468158119534,2011316895522239,2010462750666668,
    1991045095345926,1985898506526666,2004040030953867,2015772614276549],
   [2001732798389889,1984312044126184,1991489969754277,2012430395749709,2014604977601270,
    1994066337593746,1981317783754364,1995584879875874,2016706987075152,2014514491735035,
    1991589764693017,1979396209943371,1995160298967556,2018830099751612,2019379243046374,
    1994724120943869,1974642681990980,1984425710852609,2014266377264079,2030215309779339,
    2012856479527888,1979456657731399,1965848358401848,1988634584542799,2027489212923759,
    2044565137131064,2020752985510096,1974196227014238,1945180119034541,1962004758914408,
    2017062497465489,2071605562658960,2084011897243417,2039635119548424,1961546604569650,
    1896755867668913,1888973783990976,1955583941534919,2080990412042135,2226979829796095,
    2351526462426408,2425289004619232,2439087600177515,2401803519837612,2332531850051180,
    2251901042752890,2175993130162047,2113956887008377,2068593410959210,2038447425251253,
    2020081681832455,2009772862890302,2004427418956511,2001864211880689,2000727851832118,
    2000262675819388,2000087260706462,2000026538422018,2000007336214280,2000001825619447,
    2000000403488955,2000000077645373,2000000012603146,2000000001627663],
   [2000000000144902]]
private def phb_m4_r256_6 : List ℤ := uOfNatHb pb_m4_r256_6
private def pvi_m4_r256_6 : List ℤ := bDec bZ pv_m4_r256_6_0
private def pvo_m4_r256_6 : List ℤ := bDec bZ pv_m4_r256_6_5
private def pb_m4_r256_7 : List ℕ := pNatCat
  [
   [102297010683075,144225748965553,176095747474126,202709552573648,225933542024229,
    246727922757060,265664859441994,283118282530645,299348707060585,314546379025552,
    328855344778452,342387843798779,355233395673998,367464793851857,379142204199465,
    390316053634141,401029119076179,411318071984705,421214642641555,430746512834238,
    439938010678040,448810658747835,457383611737810,465674009742710,473697266262728,
    481467305120124,488996756965665,496297123508911,503378915737443,510251771000179,
    516924552784245,523405436219999,529701981738518,535821198833077,541769601506749,
    547553256697316,553177826739836,558648606742755,563970557605097,569148335282185,
    574186316809608,579088623515117,583859141782294,588501541675366,593019293689283,
    597415683851407,601693827369481,605856680993890,609907054239712,613847619594924,
    617680921824881,621409386469280,625035327615936,628560955025414,631988380671791,
    635319624757150,638556621250790,641701222998411,644755206441474,647720275982576,
    650598068028835,653390154741897,656098047520211,658723200236608],
   [661267012251890,663730831223101,666115955723317,668423637688184,670655084702998,
    672811462142819,674893895176973,676903470648275,678841238836360,680708215113704,
    682505381502159,684233688137161,685894054646147,687487371447203,689014500973431,
    690476278828103,691873514875244,693206994269933,694477478432252,695685705968540,
    696832393543283,697918236704767,698943910667346,699910071052991,700817354594574,
    701666379803174,702457747601516,703192041925512,703869830295736,704491664360518,
    705058080412252,705569599878388,706026729788464,706429963218484,706779779713813,
    707076645691702,707321014824503,707513328404518,707654015691411,707743494243014,
    707782170230334,707770438737489,707708684047275,707597279913010,707436589817265,
    707226967218037,706968755782914,706662289611711,706307893448048,705905882880310,
    705456564532378,704960236244521,704417187244797,703827698311296,703192041925512,
    702510482417154,701783276100632,701010671403481,700192908986929,699330221858828,
    698422835479130,697470967858070,696474829647231,695434624223610],
   [694350547766821,693222789329531,692051530901243,690836947465483,689579207050474,
    688278470773336,686934892877860,685548620765875,684119795022213,682648549433287,
    681135010999234,679579299939624,677981529692663,676341806907852,674660231431999,
    672936896288524,671171887649924,669365284803298,667517160108764,665627578950644,
    663696599681216,661724273556844,659710644666277,657655749850878,655559618616521,
    653422273036872,651243727647761,649023989332290,646763057196333,644460922434027,
    642117568182835,639732969367715,637307092533916,634839895667847,632331328005459,
    629781329827517,627189832241079,624556756946480,621882015989029,619165511494578,
    616407135388065,613606769094052,610764283218190,607879537208493,604952378995170,
    601982644607689,598970157767641,595914729455833,592816157451931,589674225844813,
    586488704511662,583259348563623,579985897755703,576668075858354,573305589987966,
    569898129893260,566445367194278,562946954570368,559402524893243,555811690300805,
    552174041207014,548489145242642,544756546121221,540975762423941],
   [537146286296627,533267582051196,529339084663229,525360198156381,521330293863378,
    517248708552205,513114742404837,508927656834424,504686672125226,500390964877748,
    496039665239433,491631853898887,487166558818884,482642751680274,478059344005325,
    473415182924931,468709046549313,463939638896363,459105584325368,454205421416393,
    449237596226907,444200454847048,439092235162902,433911057723059,428654915586911,
    423321663013261,417909002823994,412414472249028,406835427024414,401169023473835,
    395412198253177,389561645375982,383613790061533,377564758853276,371410345338203,
    365145970651235,358766637763642,352266878319486,345640690482967,338881465870462,
    331981903133885,324933905094124,317728455434831,310355469771003,302803614277595,
    295060082813507,287110320323605,278937675811873,270522961671389,261843886537838,
    252874314300994,243583279409442,233933652794438,223880293923773,213367424339622,
    202324780153254,190661769005055,178258199604039,164948752133500,150495092749364,
    134530961225742,116439074450859,95014504167092,67143285787078]]
private def pv_m4_r256_7_0 : List ℕ := pNatCat
  [
   [2000222397755866,2000166864964383,1999878433394622,1999693245888713,2000201467872316,
    2000148775130329,1999989161972118,2000343434011928,2000173524431435,2000187151014509,
    2000415858377623,2000248086280034,1999745674371089,2000044655070068,2000452511323052,
    2000239595515383,1999537967686704,1999892118067982,2000235872519951,2000061465627607,
    1999778073188023,1999472133755868,2000025220770488,2000296560016337,2000121730219695,
    1999486909832741,1999592526791601,2000271094053237,2000048686828107,2000360706433397,
    2000244019913822,2000062651584444,1999713686467591,2000254279305408,1999915860326713,
    1999591669986279,1999866962064619,2000337614476403,1999980133600083,2000208779938911,
    1999938763684213,1999445884095845,2000372717920149,1999499987607334,1999937188004724,
    1999747868555178,1999799617867215,2000309749172449,1999676367740365,1999297359145437,
    1999342638961034,2000356116603309,2000130793611532,1999457719317456,2000872075423090,
    2000182730338733,2000375753108973,2000781458170196,1999377864477006,2000928080056960,
    2001038293464423,1999972805081835,2000723252512329,1998686778222081],
   [2001680557272410,2001105274207581,1999937038994120,2001728822368434,1998038456087003,
    2001336081734309,2000125614935477,1998918637610043,2001910644874356,1998143034585192,
    2000563367924637,1998553590042261,1998473176018494,2001781808473517,1999762890073537,
    1998808145426358,1998107200968699,1998079153721247,1999804946222711,2001417061205540,
    1998068089800632,1998632023918204,2000431391973335,1997543775327385,2001627319246419,
    1999687756382924,2002065552441791,2002148426601475,1999773893876955,1999412328832681,
    2002639066207589,2000948393947206,1999462473329413,2002060536483923,1998867500382967,
    2000242169597559,1998495263846747,1998090959781151,2000729894026237,2002115590713780,
    1997965301433317,1999854156499134,2001857020466156,1997887777137062,1999905318967610,
    2002191650945251,2001575109604631,1999393780863557,2001451783224795,1998861447046038,
    1999540420328820,1998039597600706,1998323325065091,1999682385921483,2002315519833236,
    1998801228934811,1999101363178669,2002279187508964,1998960682854185,1997992643957270,
    2002443655051974,1999436351950498,1997247527223122,2001225385985386],
   [2002071902727195,1997785786950855,1999448454832119,2002207721177782,1999018308258951,
    1998492062759380,2001528736641634,2000300146165976,1998827427321735,2000582109494023,
    2000083664360082,1999174189338439,1998933262473957,2000271784102602,1998284015520741,
    2001281343388882,2002548024533546,1998003034243900,1998246251970318,2003201714474161,
    2000794284165682,1996549881565461,2001490095542419,2004240153064877,1996979267076394,
    1996395250701457,2005499206609553,2003470520937738,1992876576268244,1997024471711373,
    2007893901729092,2001651802138004,1991189995387158,1999119975564120,2008417109097422,
    1998892069365580,1991150845522916,2002639822014685,2009534332171176,1996441597133203,
    1989705203705239,2003635335193647,1989680378463543,1995851978708283,1989072378108911,
    2004207047377023,2011971621983048,1996840399758996,1987678969627425,2002009298578551,
    2012329225584473,1998720794726196,1986640121749417,1999117768947486,2013838488082127,
    2003938824277455,1986658857605858,1992468158119534,2011316895522239,2010462750666668,
    1991045095345926,1985898506526666,2004040030953867,2015772614276549],
   [2001732798389889,1984312044126184,1991489969754277,2012430395749709,2014604977601270,
    1994066337593746,1981317783754364,1995584879875874,2016706987075152,2014514491735035,
    1991589764693017,1979396209943371,1995160298967556,2018830099751612,2019379243046374,
    1994724120943869,1974642681990980,1984425710852609,2014266377264079,2030215309779339,
    2012856479527888,1979456657731399,1965848358401848,1988634584542799,2027489212923759,
    2044565137131064,2020752985510096,1974196227014238,1945180119034541,1962004758914408,
    2017062497465489,2071605562658960,2084011897243417,2039635119548424,2038453395430350,
    2103244132331087,2111026216009024,2044416058465081,2080990412042135,2226979829796095,
    2351526462426408,2425289004619232,2439087600177515,2401803519837612,2332531850051180,
    2251901042752890,2175993130162047,2113956887008377,2068593410959210,2038447425251253,
    2020081681832455,2009772862890302,2004427418956511,1998135788119311,2000727851832118,
    2000262675819388,2000087260706462,1999973461577982,2000007336214280,2000001825619447,
    2000000403488955,1999999922354627,2000000012603146,2000000001627663],
   [2000000000144902]]
private def pv_m4_r256_7_1 : List ℕ := pNatCat
  [
   [2000077178863531,2000015205131448,1999882810162587,2000218399825599,2000354955989795,
    2000257720611544,1999847454682932,1999918340568704,1999979965603906,1999963788492951,
    1999955311258685,1999706720040267,2000168641507267,2000332586037270,1999956282516498,
    1999901597762116,1999793687356045,2000556363961179,2000411048663598,2000351317960683,
    1999971790168511,1999940161051964,1999935221693076,2000441296217569,2000561356997047,
    1999947087924930,1999742620492980,1999686628911083,2000783509145861,1999884718537026,
    1999991683882183,2000271373826193,1999337453058356,1999824481851080,2000056514955291,
    2000064081082190,2000336567898500,1999686777606222,1999854955104055,1999570787482598,
    1999878853838964,2000314401939031,1999506525026641,2000160523918587,2000632924238460,
    1999069634701657,2001425874765082,2000044517024176,1998941919289743,2001026869669960,
    1998657395948269,2001143018243710,1999768474897009,1998658595167962,2002045094152057,
    1998312389134634,2001382150344039,2000107957497449,1998212063509327,2001283766823547,
    1999152078352095,2000269624114986,2000255329328728,1999040032249799],
   [2000339510180849,2000362762642611,1999377142624561,1998857123199989,2000584829781723,
    1997971919762973,2002419964948710,1999398264642785,1998886265453031,2000910208566775,
    1999666332405094,2000764275564466,2001017921503324,2000163596977234,1999455241724355,
    2002038622954564,1998299159227797,2000396638394770,2001362125518706,2000618897065886,
    2001545159643172,1999756888992588,1998238899423046,2001224942497917,2003105354265279,
    1998624310926382,2000442353285265,1999230944240730,1999408912552202,1999895721745335,
    2000812384387631,1998839758797427,2001747822870617,1998817614377876,1996602774505356,
    2000079403629913,2001551057549137,1998172834645430,1998682924802641,2000546516315950,
    1998223934800513,1997446223398599,2000146287540680,1999414359223050,2000857481980565,
    2000953014016467,1998967155571202,2001140449971981,2001623474891775,1999192002211367,
    2001926634865403,2004040411484188,1999031104449791,1998347251560469,2001771630131044,
    1999866933432662,1997044373029854,2002144820813642,2000637066119039,1998008942039407,
    2000044281506318,2000816338572116,1997838766939709,1999064160447083],
   [2003269596637683,2001469092886123,1999596879289354,2001411899488605,1999910506039944,
    1998195388303007,1999973812020450,1999371241291779,1998262002577219,2000702721313871,
    2000543266934642,1998385703323550,2000861380380601,2001672395418306,1997380047890931,
    1998758822651918,2003257782701096,1999336687029706,1995640688246647,2003015785067422,
    2002746484931608,1997150929724016,1995158898243476,2008743070623142,1995180846089303,
    1999823678230849,1998507890995207,2008669380030665,1994007496567809,1991384497407022,
    2011270614173428,2000510481461260,1990065069086866,2002380078854916,2006322465451007,
    1998110959519011,1995102022880667,2001579041805561,2005371230912518,1997984992980484,
    1994786554958001,2004213477715807,2005613194222540,1994704138288101,1995787334116297,
    2006975368454762,2002666051821364,1991633524484391,1999424086334907,2010277360835778,
    1998314782286045,1985423320093752,1999828558861778,2016835149836042,2005015028605551,
    1987136454786053,1994668905413526,2007392604132470,1996332888276730,1982258351583323,
    1994487837003025,2012293164684166,2003539935960581,1985852506719600],
   [1993379295973387,2012667406682778,2008008427241392,1987879788399275,1989385046678092,
    2010414280992191,2013326251745477,1992391433934631,1984082631443330,2003169695522974,
    2017057884232907,2001640893644243,1982276045160002,1991480880250755,2015148004262474,
    2014970671573386,1990571395990725,1979429656243739,2000881527737227,2020675405241541,
    2011811736149435,1980208019537078,1979937685657111,2005434892426693,2027515645147197,
    2014129904837651,1975198630998568,1968627289616312,2011453673827195,2027406122015519,
    2019806371048611,2002956570839406,1937493649493698,1964607602619943,2075202356812649,
    2059768033493151,1961958424344534,1956611596949841,2001758517686287,1991575920589611,
    1972552835555284,2020031048973324,2092033620723670,2101203048879942,2044694923753033,
    1996691197312219,2033643918666292,2152223114601332,2307801935366929,2425688803767365,
    2470058187423198,2440866200570326,2357692961457296,2256554939791816,2166378830257503,
    2097282760080017,2050054024218590,2022227700031978,2008506862170676,2002835194953676,
    2000829942750886,2000212399599168,2000046391199306,2000008180223654],
   [2000001008039618]]
private def phb_m4_r256_7 : List ℤ := uOfNatHb pb_m4_r256_7
private def pvi_m4_r256_7 : List ℤ := bDec bZ pv_m4_r256_7_0
private def pvo_m4_r256_7 : List ℤ := bDec bZ pv_m4_r256_7_1
private def pwalks_m4_r256 : List RkmSegWalk := [
  ⟨phb_m4_r256_0, pvi_m4_r256_0, pvo_m4_r256_0⟩,
  ⟨phb_m4_r256_1, pvi_m4_r256_1, pvo_m4_r256_1⟩,
  ⟨phb_m4_r256_2, pvi_m4_r256_2, pvo_m4_r256_2⟩,
  ⟨phb_m4_r256_3, pvi_m4_r256_3, pvo_m4_r256_3⟩,
  ⟨phb_m4_r256_4, pvi_m4_r256_4, pvo_m4_r256_4⟩,
  ⟨phb_m4_r256_5, pvi_m4_r256_5, pvo_m4_r256_5⟩,
  ⟨phb_m4_r256_6, pvi_m4_r256_6, pvo_m4_r256_6⟩,
  ⟨phb_m4_r256_7, pvi_m4_r256_7, pvo_m4_r256_7⟩
  ]
private def pb_m4_r384_0 : List ℕ := pNatCat
  [
   [272419472653846,333209636047304,332774352208902,271353247534564]]
private def pv_m4_r384_0_0 : List ℕ := [3000000000000000]
private def pv_m4_r384_0_1 : List ℕ := pNatCat
  [
   [2963461834465784,2264114030184057,2044277920301052,2004942120938323,2000337345826315]]
private def phb_m4_r384_0 : List ℤ := uOfNatHb pb_m4_r384_0
private def pvi_m4_r384_0 : List ℤ := bDec bZ pv_m4_r384_0_0
private def pvo_m4_r384_0 : List ℤ := bDec bZ pv_m4_r384_0_1
private def pb_m4_r384_1 : List ℕ := pNatCat
  [
   [547042205809507,669114188220739,668240100077211,544901132209079]]
private def pv_m4_r384_1_0 : List ℕ := pNatCat
  [
   [1036538165534216,1735885969815943,1955722079698948,2004942120938323,2000337345826315]]
private def pv_m4_r384_1_1 : List ℕ := pNatCat
  [
   [1885286829180447,1691327036677717,1456554368584161,1364888249757159,1560839664185307]]
private def phb_m4_r384_1 : List ℤ := uOfNatHb pb_m4_r384_1
private def pvi_m4_r384_1 : List ℤ := bDec bZ pv_m4_r384_1_0
private def pvo_m4_r384_1 : List ℤ := bDec bZ pv_m4_r384_1_1
private def pb_m4_r384_2 : List ℕ := pNatCat
  [
   [120950422588914,170381419430656,207854902756123,239064202200047,266223806448673,
    290473954341239,312494627756774,332730564135754,351491844090082,369005077666344,
    385441969000061,400936403114754,415595237560363,429505423014506,442738874057943,
    455355903227335,467407705238140,478938194394174,489985390104785,500582479544775,
    510758645050845,520539717051956,529948695575064,539006171342383,547730669170869,
    556138930545907,564246148069934,572066161462867,579611622569373,586894135175276,
    593924374191878,600712187821414,607266685590866,613596314578764,619708925719988,
    625611831727236,631311857893031,636815386816465,642128397922190,647256502496150,
    652204974846057,656978780099297,661582599072442,666020850581614,670297711509029,
    674417134895943,678382866294503,682198458579150,685867285391406,689392553368993,
    692777313290896,696024470253328,699136792977377,702116922336873,704967379184463,
    707690571544773,710288801235614,712764269971313,715119084996238,717355264291364,
    719474741392094,721479369851536,723370927379884,725151119687382],
   [726821584055615,728383892659382,729839555659241,731190024082863,732436692511609,
    733580901587188,734623940351886,735567048434590,736411418093755,737158196127414,
    737808485659479,738363347810708,738823803262039,739190833717267,739465383271471,
    739648359691022,739740635610530,739743049651585,739656407467780,739481482720066,
    739219017986182,738869725607538,738434288476658,737913360767995,737307568614671,
    736617510733462,735843759000117,734986858976887,734047330393945,733025667586189,
    731922339886728,730737791978206,729472444202929,728126692832605,726700910298378,
    725195445381644,723610623366026,721946746150716,720204092325256,718382917205678,
    716483452831773,714505907925119,712450467807319,710317294277776,708106525450124,
    705818275546307,703452634647064,701009668397449,698489417665745,695891898153971,
    693217099957921,690464987074424,687635496853261,684728539390877,681743996862702,
    678681722790579,675541541241386,672323245952555,669026599379739,665651331661369,
    662197139494304,658663684914181,655050593973374,651357455308772],
   [647583818590711,643729192843501,639793044626954,635774796067148,631673822723396,
    627489451276891,623220957024898,618867561162491,614428427831726,609902660915782,
    605289300552898,600587319341838,595795618207115,590913021888178,585938274012143,
    580870031704322,575706859684705,570447223791400,565089483863843,559631885908982,
    554072553462438,548409478043535,542640508587670,536763339721285,530775498723162,
    524674330990147,518456983794808,512120388085878,505661238038146,499075968005055,
    492360726462234,485511346450762,478523311931272,471391719339230,464111233481426,
    456676036725479,449079770196754,441315465395375,433375464259626,425251325202814,
    416933712000000,408412261544320,399675425353054,390710278170085,381502284922385,
    372035014403703,362289784017278,352245214155166,341876662452435,331155495829269,
    320048139615917,308514814234439,296507824046658,283969187658417,270827270726299,
    256991854581734,242346649054085,226737416496840,209952082696420,191685032764442,
    171466821347851,148506648510120,121261716065192,85747295751460]]
private def pv_m4_r384_2_0 : List ℕ := pNatCat
  [
   [1885286829180447,1691327036677717,1456554368584161,1364888249757159,1560839664185307]]
private def pv_m4_r384_2_1 : List ℕ := pNatCat
  [
   [1947684318232715,1969617416790833,2019793305486040,2041722318501616,2014716473933994,
    1968723899146393,1948891125463104,1973064833841112,2019123669161865,2044755454813974,
    2017666781333463,1933811086356877,1815920689842463,1698777966694750,1612716841853620,
    1573631325870804,1581578841083627,1625429873234201,1689525942906885,1759217776365071,
    1823931377603070,1877882431448943,1919283494561766,1948960905035467,1969026839119835,
    1981912452141792,1989812057521986,1994454092586961,1997077220760200,1998506431265899,
    1999258938337038,1999642550304136,1999832202583899,1999923264200767,1999965782647453,
    1999985110185259,1999993672160268,1999997371867925,1999998932560730,1999999575770142,
    1999999834932948,1999999937086647,1999999976500670,1999999991394196,1999999996908771,
    1999999998910460,1999999999623050,1999999999871946,1999999999957274,1999999999985997,
    1999999999995494,1999999999998577,1999999999999561,1999999999999869,1999999999999963,
    1999999999999991,1999999999999999,2000000000000000,2000000000000000,2000000000000000,
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
private def pv_m4_r384_2_2 : List ℕ := pNatCat
  [
   [1999878558409076,1999482193108628,1998467257321013,1996371313165504,1992733757820699,
    1987338762831326,1980510957457562,1973330431142390,1967606965636812,1965507570144272,
    1968866227150633,1978372400397438,1992955426515012,2009681474227528,2024331764487233,
    2032577691817445,2031409629244235,2020325114562656,2001814243465633,1980896158154594,
    1963783778158049,1956062276731609,1960944116982061,1978146339210645,2003735964219222,
    2030984217020079,2051968528114903,2059460551649776,2048592125751865,2017895818321036,
    1969521772685641,1908664149474627,1842419094426884,1778397512176869,1723419160805975,
    1682538402991657,1658532497410357,1651859799354869,1660998348612955,1683021163997459,
    1714254392641828,1750888571314903,1789456660858158,1827140270314482,1861906306610121,
    1892504032900658,1918365916619746,1939456898723740,1956109776857160,1968873474636488,
    1978389522570890,1985302359979896,1990202135018639,1993594643461526,1995891435230464,
    1997413210623773,1998400701273296,1999028695535298,1999420323279301,1999659938497317,
    1999803846151905,1999888718826619,1999937892825198,1999965891747486],
   [1999981563838103,1999990190101380,1999994860445485,1999997348252384,1999998652407314,
    1999999325356422,1999999667229505,1999999838254794,1999999922519558,1999999963416834,
    1999999982972525,1999999992186472,1999999996464779,1999999998422749,1999999999306032,
    1999999999698862,1999999999871117,1999999999945594,1999999999977347,1999999999990700,
    1999999999996236,1999999999998502,1999999999999416,1999999999999781,1999999999999921,
    1999999999999973,1999999999999993,1999999999999999,2000000000000000,2000000000000000,
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
private def phb_m4_r384_2 : List ℤ := uOfNatHb pb_m4_r384_2
private def pvi_m4_r384_2 : List ℤ := bDec bZ pv_m4_r384_2_0
private def pvo_m4_r384_2 : List ℤ := bDec bZ pv_m4_r384_2_2
private def pb_m4_r384_3 : List ℕ := pNatCat
  [
   [84156288000000,118705029046887,145003784474730,166997634000000,186218980903070,
    203455850128911,219177599789855,233690840473506,247209096000000,259888231938570,
    271846215653289,283174929890441,293947629926192,304223861335803,314052822145768,
    323475732000000,332527545130404,341238216659589,349633656971652,357736463313792,
    365566489134915,373141293143251,380476497793981,387586078609693,394482600000000,
    401177409215022,407680797188116,414002132936393,420149976654834,426132175499816,
    431955945200517,437627939984868,443154312806421,448540767470932,453792603958666,
    458914758000000,463911835772693,468788144438089,473547719111909,478194346766969,
    482731587485056,487162793409653,491491125697295,495719569720704,499850948739819,
    503887936225894,507833066997910,511688747308734,515457264000000,519140792829075,
    522741406058131,526261079383989,529701698277676,533065063794219,536352897906019,
    539566848406896,542708493428447,545779345605714,548780855924998,551714417283106,
    554581367784146,557382993797272,560120532796297,562795176000000],
   [565408070830036,567960323201692,570452999661229,572887129382272,575263706032469,
    577583689520654,579848007633763,582057557571942,584213207389516,586315797348820,
    588366141193277,590365027345577,592313220036290,594211460367816,596060467318183,
    597860938688804,599613552000000,601318965337790,602977818155167,604590732030821,
    606158311388081,607681144176588,609159802519060,610594843325320,611986808875606,
    613336227375026,614643613480904,615909468804622,617134282389464,618318531165862,
    619462680385336,620567184034357,621632485229249,622659016593201,623647200616369,
    624597450000000,625510167985429,626385748668782,627224577302118,628027030581735,
    628793476924314,629524276731512,630219782643605,630880339782726,631506285986233,
    632097952030671,632655661846821,633179732726248,633670475519764,634128194828195,
    634553189185817,634945751236800,635306167904996,635634720557360,635931685161320,
    636197332436346,636431928000000,636635732508695,636809001793414,636951986990593,
    637064934668397,637148086948569,637201681624055,637225952272584],
   [637221128366361,637187435378052,637125094883199,637034324659231,636915338781187,
    636768347714304,636593558403584,636391174360468,636161395746728,635904419455682,
    635620439190849,635309645542133,634972226059628,634608365325148,634218245021561,
    633802044000000,633359938345051,632892101437980,632398704018064,631879914242116,
    631335897742254,630766817681981,630172834810636,629554107516281,628910791877068,
    628243041711150,627551008625175,626834842061428,626094689343653,625330695721605,
    624543004414382,623731756652569,622897091719234,622039146989823,621158057970985,
    620253958338357,619326979973353,618377252998984,617404905814744,616410065130581,
    615392856000000,614353401852308,613291824524046,612208244289613,611102779891122,
    609975548567513,608826666082931,607656246754411,606464403478873,605251247759459,
    604016889731233,602761438186253,601485000598044,600187683145484,598869590736120,
    597530827028937,596171494456586,594791694247099,593391526445090,591971089932476,
    590530482448708,589069800610558,587589139931432,586088594840271],
   [584568258700003,583028223825602,581468581501731,579889422000000,578290834595842,
    576672907585024,575035728299788,573379383124650,571703957511858,570009535996513,
    568296202211371,566564038901327,564813127937602,563043550331614,561255386248580,
    559448715020817,557623615160778,555780164373811,553918439570669,552038516879747,
    550140471659087,548224378508130,546290311279233,544338343088960,542368546329145,
    540380992677732,538375753109407,536352897906019,534312496666797,532254618318364,
    530179331124569,528086702696111,525976800000000,523849689368816,521705436509809,
    519544106513818,517365763864019,515170472444521,512958295548789,510729295887915,
    508483535598742,506221076251825,503941978859260,501646303882360,499334111239198,
    497005460312006,494660409954451,492299018498771,489921343762789,487527443056797,
    485117373190327,482691190478794,480248950750022,477790709350668,475316521152516,
    472826440558676,470320521509674,467798817489427,465261381531128,462708266223028,
    460139523714110,457555205719683,454955363526868,452340048000000],
   [449709309585932,447063198319266,444401763827477,441725055335966,439033121673029,
    436326011274740,433603772189755,430866452084042,428114098245530,425346757588687,
    422564476659021,419767301637508,416955278344958,414128452246300,411286868454809,
    408430571736257,405559606513010,402674016868054,399773846548955,396859138971766,
    393929937224872,390986284072768,388028221959787,385055793013769,382069039049676,
    379068001573145,376052721783995,373023240579682,369979598558690,366921836023890,
    363849992985831,360764109165996,357664224000000,354550376640746,351422605961537,
    348280950559135,345125448756780,341956138607167,338773057895378,335576244141768,
    332365734604816,329141566283931,325903775922220,322652400009216,319387474783565,
    316109036235679,312817120110352,309511761909332,306192996893867,302860860087210,
    299515386277089,296156610018145,292784565634332,289399287221295,286000808648700,
    282589163562544,279164385387431,275726507328811,272275562375200,268811583300357,
    265334602665444,261844652821150,258341765909786,254825973867359],
   [251297308425608,247755801114027,244201483261847,240634386000000,237054540263058,
    233461976791144,229856726131819,226238818641941,222608284489508,218965153655471,
    215309455935525,211641220941879,207960478105000,204267256675337,200561585725027,
    196843494149569,193113010669490,189370163831979,185614982012506,181847493416424,
    178067726080539,174275707874678,170471466503220,166655029506622,162826424262918,
    158985677989203,155132817743097,151267870424196,147390862775496,143501821384812,
    139600772686169,135687742961182,131762758340417,127825844804741,123877028186647,
    119916334171571,115943788299189,111959415964702,107963242420102,103955292775428,
    99935592000000,95904164923647,91861036237918,87806230497272,83739772120265,79661685390718,
    75571994458868,71470723342515,67357895928147,63233535972055,59097667101440,54950312815500,
    50791496486509,46621241360884,42439570560238,38246507082424,34042073802561,29826293474060,
    25599188729624,21360782082252,17111095926220,12850152538054,8577974077500,4294582588473]]
private def pv_m4_r384_3_0 : List ℕ := pNatCat
  [
   [1999878558409076,1999482193108628,1998467257321013,1996371313165504,1992733757820699,
    1987338762831326,1980510957457562,1973330431142390,1967606965636812,1965507570144272,
    1968866227150633,1978372400397438,1992955426515012,2009681474227528,2024331764487233,
    2032577691817445,2031409629244235,2020325114562656,2001814243465633,1980896158154594,
    1963783778158049,1956062276731609,1960944116982061,1978146339210645,2003735964219222,
    2030984217020079,2051968528114903,2059460551649776,2048592125751865,2017895818321036,
    1969521772685641,1908664149474627,1842419094426884,1778397512176869,1723419160805975,
    1682538402991657,1658532497410357,1651859799354869,1660998348612955,1683021163997459,
    1714254392641828,1750888571314903,1789456660858158,1827140270314482,1861906306610121,
    1892504032900658,1918365916619746,1939456898723740,2043890223142840,1968873474636488,
    1978389522570890,1985302359979896,1990202135018639,1993594643461526,1995891435230464,
    1997413210623773,1998400701273296,1999028695535298,1999420323279301,1999659938497317,
    1999803846151905,1999888718826619,1999937892825198,1999965891747486],
   [1999981563838103,1999990190101380,1999994860445485,1999997348252384,1999998652407314,
    1999999325356422,1999999667229505,1999999838254794,1999999922519558,1999999963416834,
    1999999982972525,1999999992186472,1999999996464779,1999999998422749,1999999999306032,
    1999999999698862,1999999999871117,1999999999945594,1999999999977347,1999999999990700,
    1999999999996236,1999999999998502,1999999999999416,1999999999999781,1999999999999921,
    1999999999999973,1999999999999993,1999999999999999,2000000000000000,2000000000000000,
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
private def pv_m4_r384_3_1 : List ℕ := pNatCat
  [
   [1999941893482438,1999738784833191,1999182936353519,1997950198105305,1995634864427732,
    1991873250646501,1986549562593287,1980029515051895,1973318074642395,1968021974790423,
    1966039326066187,1968997579647989,1977585350351064,1991018376736645,2006891403036145,
    2021571241253376,2031103485127459,2032401081706840,2024340085036668,2008371735509658,
    1988388471371237,1969815207560647,1958154145281491,1957399296928411,1968789497345846,
    1990269787515938,2016818238401444,2041542701655882,2057241445434160,2058013956234471,
    2040525321228625,2004650557285494,1953405965845398,1892255375269528,1828011721221249,
    1767612476002024,1717029838837746,1680502457835479,1660174437237494,1656128701113239,
    1666732333838050,1689136040299633,1720060968630925,1754980118747219,1796078527119462,
    1817654402955375,1894813237574909,1842483560813168,1934967944561870,1988980236823726,
    1987549356802051,1980377357570020,1980996251712952,1985325128064280,1989734975801533,
    1993140271911097,1995534450243667,1997150505588453,1998214298178969,1998900234263459,
    1999334094903881,1999603465423478,1999767711276195,1999866104436516],
   [1999924037328564,1999957574363145,1999976668510638,1999987363447002,1999993258326866,
    1999996456473837,1999998164713166,1999999063215057,1999999528689727,1999999766242939,
    1999999885693803,1999999944884314,1999999973792158,1999999987709058,1999999994314335,
    1999999997405452,1999999998831939,1999999999481169,1999999999772609,1999999999901661,
    1999999999958033,1999999999982330,1999999999992660,1999999999996995,1999999999998792,
    1999999999999525,1999999999999818,1999999999999934,1999999999999978,1999999999999994,
    1999999999999999,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000]]
private def phb_m4_r384_3 : List ℤ := uOfNatHb pb_m4_r384_3
private def pvi_m4_r384_3 : List ℤ := bDec bZ pv_m4_r384_3_0
private def pvo_m4_r384_3 : List ℤ := bDec bZ pv_m4_r384_3_1
private def pb_m4_r384_4 : List ℕ := pNatCat
  [
   [84693504000000,119462788715237,145929423603209,168063672000000,187407719361268,
    204754621029819,220576731289675,235182617992921,248787168000000,261547241856036,
    273581559975847,284982591643964,295824059765379,306165890027603,316057594515265,
    325540656000000,334650251845852,343416528395499,351865561433309,360020092457173,
    367900101651511,375523259811472,382905289118985,390060254310104,397000800000000,
    403738345874549,410283248559809,416644936880497,422832025676039,428852412195538,
    434713358230151,440421560485417,445983211192584,451404050567944,456689412424461,
    461844264000000,466873240876094,471780677709072,476570635373025,481246925015106,
    485813129443066,490272622198969,494628584618755,498884021132428,503041773022352,
    507104530826021,511074845543565,514955138788289,518747712000000,522454754825123,
    526078352754222,529620494096082,533083076357731,536467912091321,539776734261557,
    543011201181032,546172901055428,549263356175772,552284026790812,555236314688979,
    558121566516242,560941076853357,563696091073614,566387808000000],
   [569017382378795,571585927184951,574094515773085,576544183886604,578935931536283,
    581270724758586,583549497263023,585773151977063,587942562496303,590058574446932,
    592122006766950,594133652911982,596094281991102,598004639837578,599865450019069,
    601677414791441,603441216000000,605157515931691,606826958121488,608450168115961,
    610027754196807,611560308066872,613048405501050,614492606964228,615893458198315,
    617251490780245,618567222652684,619841158629075,621073790874536,622265599364007,
    623417052318968,624528606623935,625600708223887,626633792503685,627628284650474,
    628584600000000,629503144367710,630384314365464,631228497704595,632036073486063,
    632807412478355,633542877383772,634242823093686,634907596933336,635537538896679,
    636132981871793,636694251857287,637221668170172,637715543645592,638176184828809,
    638603892159808,638998960150868,639361677557433,639692327542580,639991187835388,
    640258530883479,640494624000000,640699729505276,640874104863400,641018002813952,
    641131671499076,641215354586112,641269291385971,641293716967435],
   [641288862267558,641254954198321,641192215749708,641100866089339,640981120658813,
    640833191266882,640657286179592,640453610207511,640222364790152,639963748077713,
    639677955010230,639365177394246,639025603977091,638659420518868,638266809862224,
    637847952000000,637403024140827,636932200772757,636435653724992,635913552227783,
    635366062970567,634793350158411,634195575566806,633572898594892,632925476317155,
    632253463533651,631557012818820,630836274568918,630091397048138,629322526433444,
    628529806858181,627713380454487,626873387394550,626009965930760,625123252434778,
    624213381435567,623280485656414,622324696050977,621346141838393,620344950537471,
    619321248000000,618275158443206,617206804481379,616116307156695,615003785969265,
    613869358906429,612713142471319,611535251710718,610335800242229,609114900280781,
    607872662664490,606609196879895,605324611086583,604019012141229,602692505621065,
    601345195846787,599977185904930,598588577669722,597179471824415,595749967882144,
    594300164206287,592830158030372,591340045477521,589829921579465],
   [588299880295121,586750014528760,585180416147765,583591176000000,581982383930792,
    580354128799548,578706498496001,577039579956106,575353459177601,573648221235219,
    571923950295592,570180729631822,568418641637756,566637767841956,564838188921375,
    563019984714754,561183234235733,559328015685697,557454406466362,555562483192093,
    553652321701984,551723997071684,549777583624992,547813154945216,545830783886305,
    543830542583763,541812502465349,539776734261557,537723308015907,535652293095020,
    533563758198508,531457771368669,529334400000000,527193710848518,525035770040918,
    522860643083550,520668394871223,518459089695852,516232791254939,513989562659897,
    511729466444221,509452564571506,507158918443321,504848588906938,502521636262919,
    500178120272566,497818100165242,495441634645551,493048781900398,490639599605922,
    488214144934298,485772474560433,483314644668534,480840710958564,478350728652584,
    475844752500990,473322836788638,470785035340865,468231401529404,465661988278203,
    463076848069143,460476032947661,457859594528270,455227584000000],
   [452580052131736,449917049277477,447238625381498,444544829983433,441835712223277,
    439111320846295,436371704207867,433616910278239,430846986647204,428061980528710,
    425261938765392,422446907833025,419616933844918,416772062556227,413912339368210,
    411037809332405,408148517154750,405244507199635,402325823493894,399392509730727,
    396444609273575,393482165159924,390505220105051,387513816505724,384507996443829,
    381487801689960,378453273706936,375404453653282,372341382386647,369264100467177,
    366172648160830,363067065442653,359947392000000,356813667235710,353665930271234,
    350504219949719,347328574839044,344139033234815,340935633163317,337718412384417,
    334487408394438,331242658428974,327984199465686,324712068227037,321426301183005,
    318126934553751,314814004312245,311487546186864,308147595663948,304794187990321,
    301427358175781,298047140995551,294653570992694,291246682480504,287826509544859,
    284393086046535,280946445623504,277486621693185,274013647454676,270527555890953,
    267028379771030,263516151652110,259990903881687,256452668599630],
   [252901477740243,249337363034288,245760356010987,242170488000000,238567790133370,
    234952293347453,231324028384808,227683025796082,224029315941849,220362928994447,
    216683894939773,212992243579065,209288004530662,205571207231737,201841880940007,
    198100054735429,194345757521868,190579018028746,186799864812670,183008326259042,
    179204430583643,175388205834208,171559679891969,167718880473189,163865835130670,
    160000571255249,156123116077271,152233496668046,148331739941286,144417872654529,
    140491921410545,136553912658717,132603872696419,128641827670366,124667803577956,
    120681826268588,116683921444973,112674114664423,108652431340127,104618896742414,
    100573536000000,96516374101215,92447435895227,88366746093240,84274329269689,80170209863409,
    76054412178804,71926960386991,67787878526939,63637190506589,59474920103967,55301090968280,
    51115726621000,46918850456938,42710485745306,38490655630763,34259383134455,30016691155038,
    25762602469695,21497139735136,17220325488592,12932182148793,8632732016942,4321997277674]]
private def pv_m4_r384_4_0 : List ℕ := pNatCat
  [
   [1999941893482438,1999738784833191,1999182936353519,1997950198105305,1995634864427732,
    1991873250646501,1986549562593287,1980029515051895,1973318074642395,1968021974790423,
    1966039326066187,1968997579647989,1977585350351064,1991018376736645,2006891403036145,
    2021571241253376,2031103485127459,2032401081706840,2024340085036668,2008371735509658,
    1988388471371237,1969815207560647,1958154145281491,1957399296928411,1968789497345846,
    1990269787515938,2016818238401444,2041542701655882,2057241445434160,2058013956234471,
    2040525321228625,2004650557285494,1953405965845398,1892255375269528,1828011721221249,
    1767612476002024,1717029838837746,1680502457835479,1660174437237494,1656128701113239,
    1666732333838050,1689136040299633,1720060968630925,1754980118747219,1796078527119462,
    1817654402955375,1894813237574909,1842483560813168,1934967944561870,1988980236823726,
    1987549356802051,1980377357570020,1980996251712952,1985325128064280,1989734975801533,
    1993140271911097,1995534450243667,1997150505588453,1998214298178969,1998900234263459,
    1999334094903881,1999603465423478,1999767711276195,1999866104436516],
   [1999924037328564,1999957574363145,1999976668510638,1999987363447002,1999993258326866,
    1999996456473837,1999998164713166,1999999063215057,1999999528689727,1999999766242939,
    1999999885693803,1999999944884314,1999999973792158,1999999987709058,1999999994314335,
    1999999997405452,1999999998831939,1999999999481169,1999999999772609,1999999999901661,
    1999999999958033,1999999999982330,1999999999992660,1999999999996995,1999999999998792,
    1999999999999525,1999999999999818,1999999999999934,1999999999999978,1999999999999994,
    1999999999999999,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000]]
private def pv_m4_r384_4_1 : List ℕ := pNatCat
  [
   [1999960487714135,1999817774235030,1999414681550807,1998490313538243,1996689827848795,
    1993642839031529,1989119523261052,1983237917224505,1976650259918491,1970605956558850,
    1966798507060174,1966965198595621,1972308956535676,1982914274644139,1997384969068751,
    2012902849308458,2025787250482066,2032459775052896,2030550662423421,2019791904206091,
    2002371841088500,1982575748364576,1965759224061312,1956919321139723,1959266048850971,
    1973207039388369,1996039317820766,2022436563571211,2045596547383423,2058740852354463,
    2056584523981483,2036428940903621,1998654643079790,1946557220146218,1885628237320531,
    1822494384285506,1763771386522528,1715065861344255,1680289884220395,1661340840701480,
    1658246177676384,1668981970524661,1692629458874981,1718126018866297,1769277431643522,
    1766013161090347,1872565589357835,1835852283773216,1867135470076925,1943934283643932,
    1980773132283414,1983530051205902,1980499626923777,1981559352660030,1985393676313267,
    1989530368786736,1992891012100665,1995324305190973,1996992915713211,1998102090707115,
    1998822855542985,1999282086299480,1999569311972419,1999745769618074],
   [1999852300833201,1999915527034342,1999952428949146,1999973615848874,1999985585374219,
    1999992241051878,1999995884560769,1999997848637094,1999998891434112,1999999436852529,
    1999999717931572,1999999860679779,1999999932133770,1999999967392101,1999999984545029,
    1999999992773399,1999999996666026,1999999998482282,1999999999318201,1999999999697736,
    1999999999867745,1999999999942887,1999999999975659,1999999999989762,1999999999995755,
    1999999999998268,1999999999999306,1999999999999729,1999999999999899,1999999999999964,
    1999999999999989,1999999999999998,2000000000000000,2000000000000000,2000000000000000,
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
private def phb_m4_r384_4 : List ℤ := uOfNatHb pb_m4_r384_4
private def pvi_m4_r384_4 : List ℤ := bDec bZ pv_m4_r384_4_0
private def pvo_m4_r384_4 : List ℤ := bDec bZ pv_m4_r384_4_1
private def pb_m4_r384_5 : List ℕ := pNatCat
  [
   [1327104000000,1871920953408,2286639619745,2633472000000,2936583353490,3208400452851,
    3456324848732,3685191641957,3898368000000,4098311847578,4286883473025,4465531822854,
    4635412097377,4797463301544,4952461264462,5101056000000,5243798719505,5381161800789,
    5513553838088,5641331179074,5764806903043,5884257902339,5999930535533,6112045189864,
    6220800000000,6326373906592,6428929192688,6528613603162,6625562128150,6719898513519,
    6811736547830,6901181165044,6988329394265,7073271181753,7156090105637,7236864000000,
    7315665502039,7392562533608,7467618726532,7540893799543,7612443893411,7682321869818,
    7750577578675,7817258097869,7882407948844,7946069290949,8008282097057,8069084312611,
    8128512000000,8186599469865,8243379400780,8298882948530,8353139846081,8406178495201,
    8458026050562,8508708497078,8558250721120,8606676576214,8654008943710,8700269788920,
    8745480213098,8789660501664,8832830168983,8875008000000],
   [8916212088998,8956459875728,8995768179109,9034153228713,9071630694197,9108215712860,
    9143922915454,9178766450392,9212760006471,9245916834221,9278249765984,9309771234805,
    9340493292230,9370427625086,9399585571310,9427978134891,9455616000000,9482509544333,
    9508668851755,9534103724263,9558823693321,9582838030609,9606155758227,9628785658374,
    9650736282546,9672015960284,9692632807485,9712594734317,9731909452757,9750584483768,
    9768627164141,9786044653023,9802843938146,9819031841766,9834615026351,9849600000000,
    9863993121632,9877800605955,9891028528206,9903682828704,9915769317203,9927293677063,
    9938261469249,9948678136172,9958549005363,9967879293009,9976674107341,9984938451894,
    9992677228636,9999895240974,10006597196649,10012787710519,10018471307234,10023652423815,
    10028335412136,10032524541310,10036224000000,10039437898629,10042170271531,10044425079004,
    10046206209311,10047517480592,10048362642729,10048745379130],
   [10048669308459,10048137986313,10047154906830,10045723504256,10043847154449,10041529176346,
    10038772833369,10035581334795,10031957837078,10027905445132,10023427213566,10018526147892,
    10013205205683,10007467297707,10001315289014,9994752000000,9987780207433,9980402645453,
    9972622006536,9964440942432,9955862065082,9946887947493,9937521124607,9927764094125,
    9917619317325,9907089219845,9896176192449,9884882591768,9873210741028,9861162930747,
    9848741419421,9835948434187,9822786171473,9809256797623,9795362449512,9781105235139,
    9766487234210,9751510498704,9736177053417,9720488896504,9704448000000,9688056310323,
    9671315748778,9654228212034,9636795572597,9619019679267,9600902357591,9582445410291,
    9563650617698,9544519738163,9525054508462,9505256644194,9485127840164,9464669770761,
    9443884090328,9422772433515,9401336415637,9379577633011,9357497663292,9335098065800,
    9312380381839,9289346135008,9265996831509,9242333960439],
   [9218358994087,9194073388216,9169478582340,9144576000000,9119367049025,9093853121797,
    9068035595504,9041915832388,9015495179989,8988774971385,8961756525424,8934441146953,
    8906830127042,8878924743202,8850726259599,8822235927266,8793454984306,8764384656095,
    8735026155478,8705380682964,8675449426912,8645233563719,8614734258002,8583952662773,
    8552889919617,8521547158859,8489925499738,8458026050562,8425849908880,8393398161629,
    8360671885299,8327672146076,8294400000000,8260856493101,8227042661552,8192959531804,
    8158608120726,8123989435739,8089104474949,8053954227282,8018539672605,7982861781856,
    7946921517166,7910719831980,7874257671179,7837535971190,7800555660109,7763317657805,
    7725822876039,7688072218566,7650066581244,7611806852141,7573293911634,7534528632514,
    7495511880081,7456244512248,7416727379629,7376961325640,7336947186590,7296685791769,
    7256177963541,7215424517433,7174426262217,7133184000000],
   [7091698526302,7049970630148,7008001094136,6965790694529,6923340201325,6880650378338,
    6837721983271,6794555767794,6751152477614,6707512852550,6663637626603,6619527528024,
    6575183279384,6530605597645,6485795194220,6440752775044,6395479040637,6349974686165,
    6304240401507,6258276871313,6212084775066,6165664787141,6119017576865,6072143808573,
    6025044141668,5977719230673,5930169725290,5882396270451,5834399506375,5786180068620,
    5737738588131,5689075691297,5640192000000,5591088131660,5541764699293,5492222311550,
    5442461572769,5392483083024,5342287438167,5291875229876,5241247045698,5190403469098,
    5139345079496,5088072452314,5036586159018,4984886767160,4932974840417,4880850938636,
    4828515617868,4775969430414,4723212924860,4670246646115,4617071135451,4563686930542,
    4510094565493,4456294570888,4402287473815,4348073797909,4293654063382,4239028787061,
    4184198482420,4129163659613,4073924825509,4018482483724],
   [3962837134651,3906989275496,3850939400306,3794688000000,3738235562401,3681582572266,
    3624729511316,3567676858263,3510425088843,3452974675841,3395326089119,3337479795649,
    3279436259534,3221195942041,3162759301622,3104126793946,3045298871921,2986275985724,
    2927058582820,2867647107996,2808042003378,2748243708459,2688252660125,2628069292675,
    2567694037847,2507127324843,2446369580347,2385421228553,2324282691185,2262954387520,
    2201436734411,2139730146305,2077835035269,2015751811008,1953480880889,1891022649958,
    1828377520964,1765545894377,1702528168408,1639324739031,1575936000000,1512362342868,
    1448604157011,1384661829640,1320535745824,1256226288506,1191733838526,1127058774630,
    1062201473499,997162309757,931941655993,866539882779,800957358685,735194450294,669251522224,
    603128937140,536827055771,470346236927,403686837516,336849212556,269833715195,202640696722,
    135270506585,67723492408]]
private def pv_m4_r384_5_0 : List ℕ := pNatCat
  [
   [1999960487714135,2000182225764970,1999414681550807,1998490313538243,1996689827848795,
    1993642839031529,1989119523261052,1983237917224505,1976650259918491,1970605956558850,
    1966798507060174,1966965198595621,1972308956535676,1982914274644139,1997384969068751,
    2012902849308458,2025787250482066,2032459775052896,2030550662423421,2019791904206091,
    2002371841088500,1982575748364576,1965759224061312,1956919321139723,1959266048850971,
    1973207039388369,1996039317820766,2022436563571211,2045596547383423,2058740852354463,
    2056584523981483,2036428940903621,1998654643079790,1946557220146218,1885628237320531,
    1822494384285506,1763771386522528,1715065861344255,1680289884220395,1661340840701480,
    1658246177676384,1668981970524661,1692629458874981,1718126018866297,1769277431643522,
    1766013161090347,1872565589357835,1835852283773216,1867135470076925,1943934283643932,
    1980773132283414,1983530051205902,1980499626923777,1981559352660030,1985393676313267,
    1989530368786736,1992891012100665,1995324305190973,1996992915713211,1998102090707115,
    1998822855542985,1999282086299480,1999569311972419,1999745769618074],
   [1999852300833201,1999915527034342,1999952428949146,1999973615848874,1999985585374219,
    1999992241051878,1999995884560769,1999997848637094,1999998891434112,1999999436852529,
    1999999717931572,1999999860679779,1999999932133770,1999999967392101,1999999984545029,
    1999999992773399,1999999996666026,1999999998482282,1999999999318201,1999999999697736,
    1999999999867745,1999999999942887,1999999999975659,1999999999989762,1999999999995755,
    1999999999998268,1999999999999306,1999999999999729,1999999999999899,1999999999999964,
    1999999999999989,1999999999999998,2000000000000000,2000000000000000,2000000000000000,
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
private def pv_m4_r384_5_1 : List ℕ := pNatCat
  [
   [1999960245190995,2000183265291498,1999418467321086,1998497677380369,1996704493221656,
    1993667988734393,1989157018834065,1983286326530126,1976703078571542,1970651060182603,
    1966819789579360,1966946720625477,1972240864678962,1982798652541253,1997239180521216,
    2012758261944142,2025682564697732,2032430150471729,2030615703987216,2019946548438839,
    2002583757359993,1982791054316785,1965915677561603,1956963609075200,1959170254808497,
    1972979391314078,1995725890829012,2022113204557454,2045353042278685,2058661418118327,
    2056729506140627,2036822007035183,1999278088168756,1947355826291948,1886520104655015,
    1823385779024574,1764572183296930,1715702530907570,1680714107509512,1661532202520568,
    1658213871800608,1668742956030046,1692272480811074,1717547353619820,1768919242695680,
    1765207874727596,1872017444528845,1835905152371220,1866270646297566,1943009508518680,
    1980446120471036,1983531973019008,1980517158517309,1981519598732834,1985327312622873,
    1989467244718409,1992841826281057,1995289238120262,1996969015750437,1998086250185975,
    1998812581438000,1999275550255329,1999565229688245,1999743264943219],
   [1999850790602190,1999914631796446,1999951907057430,1999973316552777,1999985416477216,
    1999992147240503,1999995833262110,1999997821014121,1999998876784063,1999999429198391,
    1999999713991349,1999999858680900,1999999931134317,1999999966899479,1999999984305642,
    1999999992658694,1999999996611825,1999999998457022,1999999999306589,1999999999692471,
    1999999999865390,1999999999941847,1999999999975207,1999999999989568,1999999999995673,
    1999999999998234,1999999999999292,1999999999999724,1999999999999897,1999999999999964,
    1999999999999989,1999999999999998,2000000000000000,2000000000000000,2000000000000000,
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
private def phb_m4_r384_5 : List ℤ := uOfNatHb pb_m4_r384_5
private def pvi_m4_r384_5 : List ℤ := bDec bZ pv_m4_r384_5_0
private def pvo_m4_r384_5 : List ℤ := bDec bZ pv_m4_r384_5_1
private def pb_m4_r384_6 : List ℕ := pNatCat
  [
   [81643008000000,115159970412611,140673328366154,162010344000000,180657656236230,
    197379756100001,212631984588768,226711795538144,239826336000000,252126816706394,
    263727681992713,274718070578930,285169050013769,295138387577525,304673812025424,
    313815312000000,322596797844766,331047330089518,339192045319369,347052865927495,
    354649052450766,361997639216511,369113782124112,376011039325069,382701600000000,
    389196472519812,395505640484947,401638193112118,407602434950915,413405978806823,
    419055824915345,424558428779655,429919759598821,435145350837664,440240344195531,
    445209528000000,450057370867934,454788051329736,459405483994676,463913342739766,
    468315081326961,472613951789872,476813020878882,480915184810242,484923182528828,
    488839607664185,492666919334357,496407451930828,500063424000000,503636946321474,
    507130029270483,510544589540780,513882456294863,517145376800268,520335021603666,
    523452989288442,526500810856185,529479953767947,532391825677144,535237777882503,
    538019108526412,540737065561335,543392849504630,545987616000000],
   [548522478202000,550998508998380,553416743083603,555778178895603,558083780426705,
    560334478918608,562531174450415,564674737427898,566766009981428,568805807279381,
    570794918763192,572734109309755,574624120326321,576465670782690,578259458185016,
    580006159495266,581706432000000,583360914131870,584970226246966,586534971360882,
    588055735846186,589533090093735,590967589140125,592359773263381,593710168548850,
    595019287427091,596287629185479,597515680455054,598703915674100,599852797529790,
    600962777379171,602034295650665,603067782227176,604063656811846,605022329277402,
    605944200000000,606829660178402,607679092139275,608492869629343,609271358095081,
    610014914950616,610723889834412,611398624855341,612039454828662,612646707502407,
    613220703774668,613761757902218,614270177700886,614746264738101,615190314517958,
    615602616659175,615983455066270,616333108094275,616651848707281,616939944631102,
    617197658500328,617425248000000,617622966002175,617791060697588,617929775722628,
    618039350281840,618120019266139,618172013366918,618195559186240],
   [618190879343251,618158192577003,618097713845812,618009654423306,617894221991293,
    617751620729584,617582051402888,617385711444890,617162795039644,616913493200360,
    616637993845713,616336481873744,616009139233470,615656144994276,615277675413170,
    614873904000000,614445001580685,613991136358555,613512473973857,613009177561496,
    612481407807080,611929323001325,611353079092883,610752829739645,610128726358580,
    609480918174145,608809552265343,608114773611449,607396725136467,606655547752350,
    605891380401039,605104360095347,604294621958731,603462299263999,602607523470969,
    601730424263130,600831129583333,599909765668539,598966457083663,598001326754533,
    597014496000000,596006084563226,594976210642172,593924990919310,592852540590587,
    591758973393667,590644401635467,589508936219007,588352686669602,587175761160419,
    585978266537399,584760308343587,583521990842872,582263417043159,580984688718991,
    579685906433636,578367169560652,577028576304951,575670223723374,574292207744783,
    572894623189699,571477563789484,570041122205094,568585390045399],
   [567110457885101,565616415282235,564103350795302,562571352000000,561020505505602,
    559450896970971,557862611120222,556255731758046,554630341784708,552986523210715,
    551324357171178,549643923939865,547945302942956,546228572772511,544493811199657,
    542741095187496,540970500903751,539182103733145,537375978289532,535552198427779,
    533710837255401,531851967143967,529975659740279,528081985977313,526171016084963,
    524242819600551,522297465379145,520335021603666,518355555794800,516359134820718,
    514345824906605,512315691644007,510268800000000,508205214326180,506124998367488,
    504028215270860,501914927593720,499785197312313,497639085829880,495476653984684,
    493297962057884,491103069781267,488892036344835,486664920404260,484421780088194,
    482162673005454,479887656252074,477596786418233,475290119595058,472967711381301,
    470629616889910,468275890754470,465906587135541,463521759726882,461121461761562,
    458705746017975,456274664825740,453828270071510,451366613204672,448889745242955,
    446397716777946,443890577980504,441368378606089,438831168000000],
   [436278995102526,433711908454012,431129956199836,428533186095312,425921645510506,
    423295381434976,420654440482431,417998868895323,415328712549354,412644016957916,
    409944827276463,407231188306802,404503144501331,401760739967194,399004018470383,
    396233023439767,393447797971063,390648384830741,387834826459873,385007164977916,
    382165442186444,379309699572814,376439978313785,373556319279072,370658763034855,
    367747349847230,364822119685608,361883112226063,358930366854631,355963922670557,
    352983818489501,349990092846684,346982784000000,343961929933072,340927568358274,
    337879736719697,334818472196081,331743811703697,328655791899196,325554449182411,
    322439819699116,319311939343754,316170843762121,313016568354009,309849148275817,
    306668618443126,303475013533230,300268367987638,297048716014541,293816091591243,
    290570528466554,287312060163160,284040719979953,280756540994328,277459556064453,
    274149797831507,270827298721886,267492090949380,264144206517318,260783677220693,
    257410534648245,254024810184527,250626535011939,247215740112736],
   [243792456271009,240356714074639,236908543917227,233447976000000,229975040333684,
    226489766740368,222992184855324,219482324128822,215960213827910,212425883038174,
    208879360665477,205320675437676,201749855906315,198166930448294,194571927267527,
    190964874396566,187345799698215,183714730867117,180071695431326,176416720753855,
    172749834034211,169071062309901,165380432457931,161677971196275,157963705085339,
    154237660529394,150499863778001,146750340927413,142989117921964,139216220555436,
    135431674472418,131635505169640,127827737997293,124008398160340,120177510719801,
    116335100594031,112481192559978,108615811254431,104738981175243,100850726682557,
    96951072000000,93040041215870,89117658284317,85183947026497,81238931131717,77282634158577,
    73315079536081,69336290564750,65346290417715,61345102141801,57332748658593,53309252765502,
    49274637136800,45228924324663,41172136760192,37104296754420,33025426499314,28935548068767,
    24834683419571,20722854392385,16600082712692,12466389991744,8321797727499,4166327305540]]
private def pv_m4_r384_6_0 : List ℕ := pNatCat
  [
   [1999960245190995,1999816734708502,1999418467321086,1998497677380369,1996704493221656,
    1993667988734393,1989157018834065,1983286326530126,1976703078571542,1970651060182603,
    1966819789579360,1966946720625477,1972240864678962,1982798652541253,1997239180521216,
    2012758261944142,2025682564697732,2032430150471729,2030615703987216,2019946548438839,
    2002583757359993,1982791054316785,1965915677561603,1956963609075200,1959170254808497,
    1972979391314078,1995725890829012,2022113204557454,2045353042278685,2058661418118327,
    2056729506140627,2036822007035183,1999278088168756,1947355826291948,1886520104655015,
    1823385779024574,1764572183296930,1715702530907570,1680714107509512,1661532202520568,
    1658213871800608,1668742956030046,1692272480811074,1717547353619820,1768919242695680,
    1765207874727596,1872017444528845,1835905152371220,1866270646297566,1943009508518680,
    1980446120471036,1983531973019008,1980517158517309,1981519598732834,1985327312622873,
    1989467244718409,1992841826281057,1995289238120262,1996969015750437,1998086250185975,
    1998812581438000,1999275550255329,1999565229688245,1999743264943219],
   [1999850790602190,1999914631796446,1999951907057430,1999973316552777,1999985416477216,
    1999992147240503,1999995833262110,1999997821014121,1999998876784063,1999999429198391,
    1999999713991349,1999999858680900,1999999931134317,1999999966899479,1999999984305642,
    1999999992658694,1999999996611825,1999999998457022,1999999999306589,1999999999692471,
    1999999999865390,1999999999941847,1999999999975207,1999999999989568,1999999999995673,
    1999999999998234,1999999999999292,1999999999999724,1999999999999897,1999999999999964,
    1999999999999989,1999999999999998,2000000000000000,2000000000000000,2000000000000000,
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
private def pv_m4_r384_6_1 : List ℕ := pNatCat
  [
   [1999972868104667,1999871063702986,1999582847972013,1998894305320985,1997507635677939,
    1995071622506880,1991297065310516,1986128571415780,1979931350383203,1973612897435147,
    1968588742306692,1966531837204203,1968917398546731,1976468333644595,1988683039842004,
    2003647560291476,2018275067815098,2028985832234097,2032681029354868,2027733484812534,
    2014672303153448,1996302647549572,1977162201845054,1962420657945367,1956508562823888,
    1961855663948031,1978095460590884,2001961353439122,2027905094088257,2049272435471283,
    2059731959605464,2054606419048610,2031805776974370,1992183113625885,1939287131491161,
    1878624010059445,1816635069083769,1759619345572749,1712853792574874,1679802033428043,
    1662746198943931,1658960678581097,1676127022112995,1682433404551001,1749646078571448,
    1721205876101127,1825760432254165,1839310995580162,1829325366691193,1882901878507913,
    1946220383445724,1975804781445488,1980795162153276,1980260305976260,1981873920985967,
    1985484333624194,1989409790505414,1992703886204560,1995150464360371,1996855959956042,
    1998001835024563,1998752430755628,1999234049297900,1999537348309301],
   [1999724978166447,1999839063283264,1999907269916433,1999947379088337,1999970585825866,
    1999983800619931,1999991208530976,1999995297604999,1999997520635366,1999998711185438,
    1999999339412061,1999999666097988,1999999833539787,1999999918142831,1999999960289364,
    1999999980993285,1999999991023619,1999999995816588,1999999998075872,1999999999126535,
    1999999999608621,1999999999826891,1999999999924419,1999999999967423,1999999999986141,
    1999999999994185,1999999999997596,1999999999999023,1999999999999612,1999999999999852,
    1999999999999946,1999999999999982,1999999999999996,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000]]
private def phb_m4_r384_6 : List ℤ := uOfNatHb pb_m4_r384_6
private def pvi_m4_r384_6 : List ℤ := bDec bZ pv_m4_r384_6_0
private def pvo_m4_r384_6 : List ℤ := bDec bZ pv_m4_r384_6_1
private def pb_m4_r384_7 : List ℕ := pNatCat
  [
   [80980479999744,114225454318998,139531772938263,160695639999492,179191630441135,
    195778031490590,210906489081056,224872043228524,237880159999248,250080823059475,
    261587548035831,272488750293048,282854920671051,292743357672202,302201402735806,
    311268719999016,319978944624989,328360901319105,336439522684630,344236553215865,
    351771097151607,359060050586661,366118446431218,372959732813209,379595999998800,
    386038167026643,392296136480876,398378923819774,404294766202018,410051214655645,
    415655212609674,421113163181268,426430987129811,431614173016396,436667820815796,
    441596679998604,446405182919131,451097474199263,455677436681455,460148714429434,
    464514733178087,468778718570974,472943712471983,477012587594752,480988060657785,
    484872704243482,488668957514297,492379135918269,496005439998432,499549963405541,
    503014700200756,506401551523979,509712331694166,512948773799885,516112534831422,
    519205200399756,522228289082493,525183256432328,528071498679656,530894356157498,
    533653116473896,536349017454256,538983249873812,541556959998288],
   [544071251949059,546527189907458,548925800171464,551268073076748,553554964792898,
    555787399004643,557966268487001,560092436582451,562166738587532,564189983055574,
    566162953021748,568086407156015,569961080849154,571787687236568,573566918164192,
    575299445100488,576985919998176,578626976109066,580223228755096,581775276058427,
    583283699633247,584749065241729,586171923416379,587552810050901,588892246961488,
    590190742420361,591448791663206,592666877372082,593845470135236,594985028885163,
    596086001316176,597148824282646,598173924179004,599161717302526,600112610199849,
    601026999998100,601905274721486,602747813594119,603554987329788,604327158409396,
    605064681346673,605767902942790,606437162530427,607072792207836,607675117063395,
    608244455391127,608781118897631,609285412900830,609757636520952,610198082864092,
    610607039198732,610984787125522,611331602740660,611647756793149,611933514836227,
    612189137373217,612414879998064,612610993530783,612777724148057,612915313509181,
    613023998877569,613104013238009,613155585409851,613178940156294],
   [613174298289944,613141876774799,613081888824800,612994543999104,612880048294194,
    612738604232974,612570410950959,612375664279673,612154556827377,611907278057222,
    611634014362932,611334949142115,611010262867281,610660133154678,610284734831000,
    609884239998072,609458818095572,609008635961870,608533857893053,608034645700196,
    607511158764952,606963554093520,606391986369036,605796608002469,605177569182045,
    604535017921277,603869100105629,603179959537880,602467737982212,601732575207089,
    600974609026944,600193975342740,599390808181417,598565239734281,597717400394361,
    596847418792775,595955421834123,595041534730962,594105881037371,593148582681640,
    592169759998128,591169531758287,590148015200909,589105326061594,588041578601482,
    586956885635264,585851358558491,584725107374212,583578240718953,582410865888060,
    581223088860427,580015014322623,578786745692442,577538385141887,576270033619606,
    574981790872802,573673755468624,572346024815057,570998695181330,569631861717849,
    568245618475672,566840058425539,565415273476465,563971354493922],
   [562508391317601,561026472778783,559525686717318,558006119998236,556467858527979,
    554910987270295,553335590261766,551741750627015,550129550593576,548499071506445,
    546850393842328,545183597223574,543498760431826,541795961421375,540075277332239,
    538336784502969,536580558483191,534806674045888,533015205199425,531206225199342,
    529379806559891,527536021065350,525674939781111,523796633064535,521901170575603,
    519988621287347,518059053496079,516112534831422,514149132266134,512168912125755,
    510171940098056,508158281242314,506127999998400,504081160195700,502017825061870,
    499938057231411,497841918754098,495729471103243,493600775183804,491455891340344,
    489294879364844,487117798504371,484924707468606,482715664437231,480490727067189,
    478249952499806,475993397367783,473721117802075,471433169438631,469129607425024,
    466810486426964,464475860634687,462125783769244,459760309088672,457379489394057,
    454983377035499,452572023917967,450145481507055,447703800834642,445247032504453,
    442775226697525,440288433177585,437786701296329,435270079998624],
   [432738617827610,430192362929730,427631363059667,425055665585202,422465317491997,
    419860365388290,417240855509525,414606833722899,411958345531835,409295436080387,
    406618150157575,403926532201643,401220626304259,398500476214641,395766125343622,
    393017616767650,390254993232721,387478297158259,384687570640929,381882855458391,
    379064193073002,376231624635452,373385190988352,370524932669762,367650889916671,
    364763102668418,361861610570064,358946452975714,356017668951788,353075297280246,
    350119376461758,347149944718835,344167039998912,341170699977376,338160962060567,
    335137863388721,332101440838872,329051731027721,325988770314451,322912594803512,
    319823240347358,316720742549152,313605136765424,310476458108700,307334741450089,
    304180021421831,301012332419817,297831708606066,294638183911171,291431792036712,
    288212566457630,284980540424577,281735746966225,278478218891549,275207988792075,
    271925089044101,268629551810884,265321409044801,262000692489477,258667433681890,
    255321663954439,251963414436994,248592716058912,245209599551027],
   [241814095447621,238406234088355,234986045620189,231553559999268,228108806992783,
    224651816180818,221182616958157,217701238536084,214207709944145,210702060031899,
    207184317470640,203654510755100,200112668205127,196558817967348,192992988016801,
    189415206158557,185825500029314,182223897098976,178610424672208,174985109889974,
    171347979731057,167699061013559,164038380396377,160365964380674,156681839311319,
    152986031378313,149278566618204,145559470915476,141828770003925,138086489468020,
    134332654744244,130567291122422,126790423747032,123002077618499,119202277594474,
    115391048391102,111568414584268,107734400610832,103889030769853,100032329223790,
    96164319999696,92285026990396,88394473955653,84492684523315,80579682190453,76655490324489,
    72720132164303,68773630821333,64816009280663,60847290402092,56867496921201,52876651450397,
    48874776479956,44861894379043,40838027396730,36803197662999,32757427189732,28700737871692,
    24633151487492,20554689700557,16465374060069,12365226001906,8254266849570,4132517815104]]
private def pv_m4_r384_7_0 : List ℕ := pNatCat
  [
   [1999972868104667,1999871063702986,1999582847972013,1998894305320985,1997507635677939,
    1995071622506880,1991297065310516,1986128571415780,1979931350383203,1973612897435147,
    1968588742306692,1966531837204203,1968917398546731,1976468333644595,1988683039842004,
    2003647560291476,2018275067815098,2028985832234097,2032681029354868,2027733484812534,
    2014672303153448,1996302647549572,1977162201845054,1962420657945367,1956508562823888,
    1961855663948031,1978095460590884,2001961353439122,2027905094088257,2049272435471283,
    2059731959605464,2054606419048610,2031805776974370,1992183113625885,1939287131491161,
    1878624010059445,1816635069083769,1759619345572749,1712853792574874,1679802033428043,
    1662746198943931,1658960678581097,1676127022112995,1682433404551001,1749646078571448,
    1721205876101127,1825760432254165,1839310995580162,1829325366691193,1882901878507913,
    1946220383445724,1975804781445488,1980795162153276,1980260305976260,1981873920985967,
    1985484333624194,1989409790505414,1992703886204560,1995150464360371,1996855959956042,
    1998001835024563,1998752430755628,1999234049297900,1999537348309301],
   [1999724978166447,1999839063283264,1999907269916433,1999947379088337,1999970585825866,
    1999983800619931,1999991208530976,1999995297604999,1999997520635366,1999998711185438,
    1999999339412061,1999999666097988,1999999833539787,1999999918142831,1999999960289364,
    1999999980993285,1999999991023619,1999999995816588,1999999998075872,1999999999126535,
    1999999999608621,1999999999826891,1999999999924419,1999999999967423,1999999999986141,
    1999999999994185,1999999999997596,1999999999999023,1999999999999612,1999999999999852,
    1999999999999946,1999999999999982,1999999999999996,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000]]
private def pv_m4_r384_7_1 : List ℕ := pNatCat
  [
   [1999992059245006,1999956460509294,1999853496044791,1999583876025731,1998988042022646,
    1997833267086824,1995838009359299,1992741211832032,1988417640334987,1983018946762437,
    1977094875689903,1971632648650573,1967957460994933,1967469951093109,1971252991449194,
    1979643074723922,1991905691021535,2006155761180777,2019612370831356,2029180664035677,
    2032241308387179,2027438611798566,2015227579157286,1997985414254871,1979605689188891,
    1964640819552246,1957194464938192,1959846566354870,1972894097247895,1994110368365748,
    2019090111398459,2042097093656957,2057210580207332,2059496036523884,2045978102663755,
    2016058833344432,1972033491904009,1916853496912653,1859663642676404,1795326328978903,
    1757839421077484,1687247707472173,1708096679655550,1634544960932230,1681242017722998,
    1693955256381825,1675978216834330,1731364817357091,1791795583794682,1802163275748732,
    1808520139376524,1847951752487873,1903289307024514,1945992090962895,1967759586254651,
    1975845262798586,1979133012530961,1982107059558638,1985628714096443,1989206553373593,
    1992316605357572,1994744226718800,1996510045323078,1997735753346839],
   [1998559243078381,1999099008930143,1999445633619797,1999664192183610,1999799658503654,
    1999882250700825,1999931805155244,1999961074231477,1999978097454605,1999987849402731,
    1999993353152598,1999996413967333,1999998091663389,1999998998164747,1999999481088295,
    1999999734784586,1999999866229071,1999999933406878,1999999967277524,1999999984127168,
    1999999992398595,1999999996405799,1999999998321909,1999999999226316,1999999999647728,
    1999999999841590,1999999999929645,1999999999969141,1999999999986636,1999999999994288,
    1999999999997593,1999999999999003,1999999999999596,1999999999999841,1999999999999942,
    1999999999999980,1999999999999995,2000000000000000,2000000000000000,2000000000000000,
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
private def phb_m4_r384_7 : List ℤ := uOfNatHb pb_m4_r384_7
private def pvi_m4_r384_7 : List ℤ := bDec bZ pv_m4_r384_7_0
private def pvo_m4_r384_7 : List ℤ := bDec bZ pv_m4_r384_7_1
private def pwalks_m4_r384 : List RkmSegWalk := [
  ⟨phb_m4_r384_0, pvi_m4_r384_0, pvo_m4_r384_0⟩,
  ⟨phb_m4_r384_1, pvi_m4_r384_1, pvo_m4_r384_1⟩,
  ⟨phb_m4_r384_2, pvi_m4_r384_2, pvo_m4_r384_2⟩,
  ⟨phb_m4_r384_3, pvi_m4_r384_3, pvo_m4_r384_3⟩,
  ⟨phb_m4_r384_4, pvi_m4_r384_4, pvo_m4_r384_4⟩,
  ⟨phb_m4_r384_5, pvi_m4_r384_5, pvo_m4_r384_5⟩,
  ⟨phb_m4_r384_6, pvi_m4_r384_6, pvo_m4_r384_6⟩,
  ⟨phb_m4_r384_7, pvi_m4_r384_7, pvo_m4_r384_7⟩
  ]
private def pv_m2_r512_3_1 : List ℕ := pNatCat
  [
   [1999953177426104,2000048539078116,2000046930564733,1999937548053813,1999996287289247,
    2000024949509389,1999951593715291,2000036864324223,1999975996808853,1999980508918784,
    1999991660344861,2000007291981529,2000015035839918,2000011466963512,2000051718554902,
    1999977032768020,2000032865412928,1999976429060697,1999967536888201,2000050495597782,
    2000040233652218,1999991292401084,1999997431119368,2000019339679387,1999997823680855,
    2000013269027069,2000000982521665,2000055153731636,2000000205634661,2000002192770119,
    1999976603902562,1999937024607150,1999972697947804,1999982808415187,1999974612351145,
    2000013762053636,2000032686216821,2000000115126290,1999987604832739,2000008942738864,
    2000009163930081,1999986000198533,1999989339493751,2000029432119554,2000064156733838,
    2000064507997164,2000047705582587,2000045943775162,2000067170879725,2000092314818219,
    2000098866013468,2000079932883748,2000044931115296,2000008926369278,1999982793460177,
    1999969998871776,1999968919285663,1999977344620851,1999997149231504,2000039276141008,
    2000130516613033,2000323785734207,2000712959120223,2001452016124177],
   [2002776422014699,2005022243092899,2008636639266207,2014170943617693,2022250063066623,
    2033509770490784,2048509038331291,2067612606125750,2090881909189508,2117960593336657,
    2148031599281612,2179796853014024,2211572053046221,2241415427324773,2267333553348101,
    2287510104640657,2300508861466776,2305451558880681,2302111026121238,2290913475526860,
    2272869756558452,2249431228922733,2222300931583430,2193244018060072,2163914973855969,
    2135718939558950,2109728283556963,2086655184738689,2066866459167641,2050430065514733,
    2037183655608501,2026810476642657,2018908751681824,2013048029640446,2008811486011588,
    2005824298313087,2003768658351604,2002387643379926,2001481635212137,2000900918966490,
    2000536951631047,2000313653586583,2000179434930148,2000100376160065,2000054776303884,
    2000029071122828,2000014951269445,2000007422029444,2000003541244614,2000001616620197,
    2000000702600002,2000000289022129,2000000111715947,2000000040174235,2000000013242202,
    2000000003902326,2000000000979563,2000000000185766,2000000000015143,1999999999995055,
    1999999999999101,2000000000002046,2000000000002357,2000000000001677],
   [2000000000000964,2000000000000485,2000000000000220,2000000000000090,2000000000000033,
    2000000000000010,2000000000000002,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000]]
private def pv_m2_r512_3_2 : List ℕ := pNatCat
  [
   [1999995201620984,1999975479682304,1999895947720868,1999998613029486,2000057461404894,
    2000012951014349,2000029925973007,1999978165122055,2000028456591171,2000000969237130,
    1999957008730636,2000008403202504,2000004421205532,1999988625741619,1999987370499483,
    2000039165394141,1999967236856315,1999977143971925,1999997848770706,1999996724632732,
    1999997653205651,1999967907336223,1999995894535109,2000055926746421,2000037537873809,
    1999999878388164,2000003224528501,1999997742445272,1999986343512992,2000004857114621,
    2000018110127929,2000004661950491,2000006459819317,2000028281143647,2000023393088971,
    1999991937847053,1999982834922347,2000004613220575,2000019254491672,2000014718977914,
    2000017044448427,2000033540858128,2000035824740024,2000007078502541,1999970841731012,
    1999958743414880,1999970625524942,1999981660770064,1999979166117467,1999975350697756,
    1999987166658257,2000009998888347,2000025365329961,2000016919610268,1999994853584698,
    1999975216318525,1999977347401015,1999994624484096,2000016556401778,2000028226531511,
    2000026850689586,2000022612854079,2000022909845772,2000035609230536],
   [2000057654015820,2000079149948198,2000093878757884,2000095112022245,2000082284630278,
    2000061495177786,2000036812205986,2000013291243828,1999996091462138,1999984943443969,
    1999978589671845,1999976402352786,1999974391182587,1999968615070178,1999959753953627,
    1999953863602934,1999970612208937,2000059611582746,2000316876816178,2000904561234826,
    2002075556729277,2004191479555180,2007724485723959,2013240976029384,2021361899565957,
    2032693198596373,2047731182647283,2066757803796417,2089741746022464,2116261627633144,
    2145470564111695,2176118204124161,2206634316855860,2235265011407356,2260244394263842,
    2279979009168488,2293218238933791,2299184203157498,2297642096874628,2288903750438742,
    2273768586342328,2253414638846118,2229257994384185,2202801982808690,2175496879127099,
    2148626471654641,2123230946825707,2100068374438293,2079611363543892,2062071764196973,
    2047444433838287,2035560756476016,2026143556340897,2018856977385531,2013347323915569,
    2009273218958049,2006325304446663,2004236898415442,2002787584451136,2001801802883196,
    2001144321571263,2000714127208600,2000437889724760,2000263773137466],
   [2000156035354477,2000090599981991,2000051602950652,2000028810092962,2000015753902404,
    2000008430165264,2000004410765098,2000002254510040,2000001124849088,2000000547396231,
    2000000259631743,2000000119941306,2000000053934606,2000000023594900,2000000010037523,
    2000000004151075,2000000001668738,2000000000652286,2000000000248144,2000000000092048,
    2000000000033408,2000000000011930,2000000000004225,2000000000001501,2000000000000539,
    2000000000000197,2000000000000071,2000000000000023,2000000000000006,2000000000000001,
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
    2000000000000000,2000000000000000,2000000000000000]]
private def pv_m2_r512_3_3 : List ℕ := pNatCat
  [
   [1999974871593879,1999981591269068,2000062120838262,2000015943496948,1999962436656723,
    1999971903822265,1999922109840207,1999948278047332,1999971369072026,2000035743993680,
    2000020543599286,1999978250300341,2000021538028278,2000042112555961,2000008582290831,
    1999999915643146,2000004596964551,2000000863741687,2000004507154175,1999994123406755,
    1999969931716103,1999983537130544,2000024225902880,2000022637689110,1999983222659119,
    1999973564137420,2000000748568288,2000013724180620,1999999329623567,1999986185947562,
    1999981765119955,1999974213107795,1999973788828956,1999996961113204,2000027413249231,
    2000032281546107,2000014462494386,2000003054452775,2000012129243995,2000016273073537,
    2000003094191962,1999984115412554,1999987285150191,2000007376160755,2000021615349324,
    2000018761450994,2000008434375330,2000008775266659,2000014456695812,2000010849730624,
    1999996104396699,1999982931339158,1999989478095471,2000014157736053,2000036346219163,
    2000041163440905,2000028369604358,2000010728509692,2000001829353318,1999999895295287,
    1999994366284834,1999981174805057,1999965055684150,1999956914180090],
   [1999965867132780,1999988009065671,2000009455573061,2000018976127250,2000013309106731,
    1999997569987994,1999983314923529,1999979826192529,1999987127684426,1999999220252753,
    2000009645726228,2000013619788450,2000010705073341,2000006205958891,2000006785339724,
    2000015482605099,2000031722061909,2000052693428177,2000073208917876,2000087293102333,
    2000091659715951,2000086542765651,2000073654436425,2000055306676200,2000034983926734,
    2000016477322252,2000002053305254,1999992440822311,1999988103249542,1999988958715779,
    1999992492685754,1999992687624963,1999980590539939,1999945753640863,1999879728655770,
    1999785054332333,1999691847405687,1999680727264143,1999908837267140,2000634985651709,
    2002238080645527,2005220417348246,2010187065383668,2017796294811754,2028682129187444,
    2043356307951533,2062102217045647,2084877579175683,2111244849057359,2140346521436279,
    2170936162828328,2201466291131715,2230223935659874,2255496236696134,2275743192312884,
    2289753266150268,2296760256148794,2296506270552060,2289244683120126,2275686596590676,
    2256902542282639,2234196386643838,2208970167069369,2182597162776903],
   [2156316752722742,2131159533085882,2107905759555428,2087075319504484,2068943783530367,
    2053576986571630,2040876055004270,2030625543390192,2022538917335004,2016297534572032,
    2011581137658681,2008089420690572,2005555350906266,2003751603702834,2002491763931704,
    2001627947872570,2001046307544091,2000661582742345,2000411540085436,2000251834730363,
    2000151580046605,2000089725372359,2000052220172687,2000029874238618,2000016794365160,
    2000009274761526,2000005030075252,2000002678175075,2000001399458243,2000000717476500,
    2000000360795656,2000000177914215,2000000086011759,2000000040758544,2000000018928847,
    2000000008614349,2000000003841330,2000000001678389,2000000000718581,2000000000301501,
    2000000000124001,2000000000050005,2000000000019779,2000000000007677,2000000000002924,
    2000000000001091,2000000000000398,2000000000000140,2000000000000047,2000000000000013,
    2000000000000003,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000]]
private def pv_m2_r512_3_4 : List ℕ := pNatCat
  [
   [2000015131010108,2000013240571212,1999945303974106,1999966593076353,1999991731427854,
    2000005982570454,2000031807601183,2000026923319202,2000004412237901,2000015749282501,
    2000026749270514,1999984365828294,1999930207796045,1999927957649831,1999960908429669,
    1999980693679236,1999984363675320,1999989440602997,1999993017647963,1999993280257075,
    2000005406091609,2000026865675061,2000030470609833,2000007000042499,1999991547913939,
    2000006620362492,2000032440045753,2000026591444342,1999995328476133,1999972674877406,
    1999980235160810,2000000136568151,2000006824114878,2000003108325118,1999999274765424,
    1999998054603929,1999993838069134,1999987402942085,1999992609065843,2000009549277389,
    2000019203721971,2000007738744818,1999981484703549,1999963938317521,1999970396761037,
    1999988956472074,1999999802813448,1999999187308073,1999997866934098,2000006733371859,
    2000022559159660,2000029425390976,2000019497883385,2000002850169409,1999993551928564,
    1999995804939804,2000002861398111,2000004641029526,1999999598385398,1999997493846186,
    2000006210916273,2000020834241654,2000029051336430,2000022705364043],
   [2000004198291296,1999985830873115,1999980757256284,1999991323055104,2000008054441749,
    2000020022547622,2000023299671839,2000021082223739,2000019532709900,2000022279598122,
    2000026105590394,2000023149165576,2000008923321532,1999987197599528,1999967136700452,
    1999957423640429,1999962049252487,1999978142259522,1999996871625046,2000008705882046,
    2000009470144017,2000001738995143,1999991545971508,1999984688591378,1999984597167772,
    1999990990604720,1999999859422758,2000006040548780,2000006785611629,2000003075026192,
    1999998185687063,1999995843445554,1999999241974562,2000010100084207,2000027511621161,
    2000047928837308,2000066861078616,2000080795616889,2000087789703506,2000087095514939,
    2000079039788378,2000065220930588,2000048147376077,2000030250911192,2000013332797696,
    1999999083466661,1999989914444521,1999988855615809,1999998132654140,2000016915365047,
    2000038729394510,2000048909194869,2000023306357311,1999930929935679,1999743828012993,
    1999456372139153,1999113560703977,1998845002537164,1998898480425076,1999664652827763,
    2001683085864160,2005620507149583,2012215839164547,2022193001600491],
   [2036150193618240,2054441294314255,2077069323938826,2103612484184321,2133199808427003,
    2164546285518997,2196047601360567,2225924205814770,2252395476925575,2273859316179520,
    2289051722401192,2297164749489862,2297908683820920,2291513558126157,2278674375131762,
    2260452031195672,2238146810044656,2213162991726663,2186881748808205,2160555754919625,
    2135233809689366,2111718373645249,2090554145799641,2072042335915965,2056273343513052,
    2043170083588190,2032534889620891,2024094362790018,2017538305770830,2012550634688758,
    2008831665284910,2006112291710865,2004161286493179,2002787285355517,2001837059269740,
    2001191512804528,2000760573499512,2000477826516586,2000295455304622,2000179803514340,
    2000107688387531,2000063470453857,2000036809830543,2000021003635378,2000011789786497,
    2000006509325860,2000003534433444,2000001887085534,2000000990572749,2000000511141794,
    2000000259237141,2000000129210811,2000000063284376,2000000030454133,2000000014398283,
    2000000006687438,2000000003051197,2000000001367500,2000000000602039,2000000000260352,
    2000000000110595,2000000000046147,2000000000018912,2000000000007609],
   [2000000000003006,2000000000001163,2000000000000437,2000000000000159,2000000000000055,
    2000000000000016,2000000000000003,2000000000000000,2000000000000000,2000000000000000,
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
    2000000000000000,2000000000000000,2000000000000000]]
private def pv_m2_r512_7_1 : List ℕ := pNatCat
  [
   [2000069432672670,1999903404845262,1999938061557159,2000034437837651,2000141603317515,
    2000096872618010,1999968630819634,1999825963283045,1999956542895250,2000122291426407,
    1999994952180975,2000034667778814,1999943196304405,2000123932409399,2000069662571064,
    2000098803989814,2000068778526280,2000055801107948,2000072549311793,1999943866815646,
    2000061583866920,2000085927598865,1999973352709648,2000021727312848,2000063092058957,
    1999962183688435,2000150118692497,2000160233176871,2000054612591150,2000019297366753,
    1999966900595888,1999970810143863,2000146533881366,1999838935228927,1999947538140324,
    2000025138238609,1999979227759925,2000008052604468,1999850366053904,1999847280045821,
    1999886174246299,1999955928926462,1999802871091486,2000045552146101,2000047436192319,
    2000179837925892,2000058111382036,2000204621898121,1999900185783570,2000299812316122,
    1999667709423584,2000342894544927,1999855967768833,1999903337674609,2000393135239073,
    1999941844551175,1999799687394501,2000042672498535,2000037019772153,1999760968037629,
    1999905660185213,2000035133679789,1999790782115068,1999899306807171],
   [1999714305231017,2000143948575353,2000025078630113,2000158779640598,2000439596872108,
    2000030345078435,1999894538442948,2000293236489186,2000136960714678,2000167177590607,
    1999745813256591,2000103926828210,2000043863124959,2000202999439741,2000521849170413,
    2000329807170677,1999679790977114,2000171737509648,2000568661623923,1999739669443886,
    1999920816146888,1999232748408585,2000397257362278,2000310531530578,1999959471592033,
    2000689755884131,1999792384823852,2000418330651563,2000543793028210,1999839778296994,
    1999350370786270,1999707379266272,2000141604864370,1999477700101042,2000303195425951,
    1999668852521855,2000429735389876,2000602006161383,1999714775313118,2000020717738936,
    2000448672791108,2000054622172613,2000245976740151,1999562533641269,1999814062367139,
    1999511559739403,1999489453133977,1999761111088920,2000228015932378,1999799646088023,
    1999614868630296,1999818392216421,2000427588242173,1999790187495473,1999701698001010,
    2000174227240731,2000456014264864,2000277925140091,1999470794969133,2000166867572171,
    1999956813875000,1999976792686531,2000266041824190,2000020872767177],
   [1999791469893762,1999696699860559,1999333716269640,1999733833957718,1999860347476501,
    1999742685481489,1999836473406618,1999971865320526,1999733648629170,2000296390177468,
    2000035461192067,1999345096979377,1999935836943930,2000468223638951,1999943513898708,
    1999753447002074,1999898950841922,1999965291212169,2000155041898068,2000109248537203,
    2000131482271672,1999978369523651,1999438781974119,1998981789729255,2000475222056910,
    1998742174695581,2000025261967224,2000588771866114,2000049920088310,1999867722784219,
    2000771501630704,1999026583517255,1999623250725907,2000455653875184,1999500606118236,
    1999458413645112,2000779023518053,1998880315714208,2000807465128786,2000263319521610,
    1999381014930189,2000456891008047,2000088653180558,1998880548736610,2000072120090355,
    1999811736954105,2000138231290949,2000150202392701,2000613409339346,2000151938397137,
    1999343887745914,2001236951974450,1999396021271286,2000133200337609,2001086862308803,
    1998767630708162,1999494923248321,2000619096956483,2000933732965743,1999493417673568,
    2000873611390309,1998706857434932,1999748766450064,2000650966886686],
   [1999356277508542,1999193782212216,2000053528879150,1999968906889438,2000534251920533,
    2001226147628923,2000120458071998,2000563747305034,1999792368237906,2000211280367738,
    1998849303420456,2001891063929941,2000251990515229,1999104489743094,1999430455535766,
    2000666941924322,1998606188914270,2001636361231760,2000909015279154,1999808137789238,
    2000915919226489,2001319053915103,1999397746556054,1999784139806325,2000808283162859,
    2000178711236600,1998579683668850,2000983945387299,1999506285243359,1999929201745316,
    2001776940557307,1999412016634912,1998400261686448,2000707028782882,2001611759724796,
    1999898765375460,1998744955161093,2000064312500937,1999174893486893,1999117956001507,
    2000692937849022,1999320156808685,1998507036426786,2000610183212684,1999659194275871,
    2000001604065607,2000158586107367,1999755832981497,1999607014044575,1999580959555930,
    2000277367991810,1998679176723613,2000415075639480,2000200687659001,2000473909872061,
    1998711263405183,2001636445429789,1998701658326161,2000437666913072,2001705846109986,
    1999444824918485,1998938196010629,2001487030936547,2001132559858507],
   [1996858440023767,2001113391920371,2000977416772249,1998615141706321,2001022932133480,
    2001003956508008,1999779672157073,2000221433414165,1999440608414520,2000175342699892,
    1999905504768905,1998580645986367,2000515395286750,2000412459517013,2000179906141997,
    1999705329174223,1999967484284118,2000544497337036,2000489510348534,1999043943123505,
    1997794297013494,2001091417302693,1999612051852183,1999792275634923,2002976206899418,
    2000909095572914,2000792056814861,1999794128610125,2000929305211610,2000900625320781,
    1997682436663960,2000626529140166,2000782167343633,1998009683097460,2001242959821513,
    1999287732278740,1998323888690089,2001313773044235,1999653537985975,1998219536299286,
    1999377841560135,2000572151675215,2001923647430257,1997288539048164,2000483364285973,
    1999868876828488,2000673813580758,2000022403270772,2000575005509419,2000141450277077,
    1998949101476357,2000418484169919,2000899076958511,1999642397356738,2000428997390120,
    2001853447420483,2000740654022784,1999432199829051,2000696961943939,2000215849006297,
    1997554509180286,1999766782177277,2002650745285205,2001330532185000],
   [2000214197896435,2001848917070245,2000614207557693,2000039396090194,2000675050985348,
    2001696767647423,2000072743964311,2000204425778881,1999806479218077,2000260658574861,
    2000086693498672,1999905821529221,1999926127709840,2000274798344794,2000465679848202,
    1999895117782304,1999789713888074,2000866780001675,1999306561827936,2001423522962747,
    1999130219901542,2000714912294060,1999998300884414,1999203827057463,1998578304526457,
    2000684481768434,2001354786786705,1997381822045840,2000861049262483,2001106161622266,
    2000874414718342,1995328072916866,2001142906334006,2001105529233166,1998853389124077,
    1998012447977197,2001705642498619,2003132770045958,1995950627969933,2001922541985814,
    2002284562716776,1999703559686664,1994735367055986,2004689135580841,2002282552735656,
    1999458076383705,1995827620551375,2003130428013274,2003081593936429,1993779871991397,
    2002757124249549,2002765237358307,1999193392559955,1996727963210449,2001406887493297,
    2005309147601206,2001368012385909,1992806729004888,1996761378723218,2010574127070551,
    1989228491345875,1997490819552734,2006439198265756,1998862850639336],
   [2001156952689995,1995965669710701,2002353286773966,2005103550660264,1997913891097090,
    1992237920843602,2008786631877148,2005255816509493,1987939537133464,1999800056908979,
    2013277254802421,1995322546621986,1995981433773826,1998449036388398,2002589471730954,
    2004754534766035,1993636295345177,1995471666380454,2008100280404547,1999807757623611,
    1988490601001705,1999853222725812,2012778754965366,2000902069967919,1996784707791978,
    2001180719274305,2002161633545026,2009180249071879,1995487320714235,1985187933247245,
    2011592243863216,2011403359330746,1984769646752955,1996858335864961,2014470015664295,
    2001116995678894,1991215090474414,1999678198419557,2003205752269218,2005205835173877,
    1994384918065874,1996631932136074,1996751806563151,2004149225387444,2007564107483921,
    1990687172977734,1992574987140609,2015268716371906,2008119373495590,1985022959116855,
    2004652756699181,2006421900280071,1989057396787896,1994897332943612,2006867747188406,
    1990895122797481,1992370480624974,2014981156799350,2005909661068541,1968317100781920,
    2014014556953144,2010982598387264,2007155981055698,1984809630724237],
   [2000161073700766,2016760279957812,1992858182022212,1990466016860304,2009620283886753,
    1998124895814191,1988878893929863,2018960171067714,2033061982497781,2000653660987208,
    1984142668654574,2009493795882513,2016648232438793,1987052625568514,1980273258297562,
    2012329955458904,2024019002442450,1994777970826254,1978317300320091,2000883815485486,
    2017785243631754,1997041585516775,1979626280999100,1990971452857047,2029691428914823,
    2010962993130473,1994621561785935,2001188452984225,2005051930393956,2042400479341234,
    2010527875349347,1997416140761412,2016368539192276,2025803761080544,2040614666151335,
    2041339459321705,2025579795517846,1972823472779898,2036084854930993,2092240183661678,
    2064514175149745,2070944628881086,2074046975840644,2027849734642397,1995182591296507,
    2042321194318199,2165106545107631,2309753307807060,2419033164564205,2460989581776812,
    2434783918474511,2361348363667190,2268805287611942,2180631236835389,2110207320640777,
    2061181250931898,2030891888494527,2014146345856958,2005842552786299,2002157182169057,
    2000702661236079,2000197915745676,2000046677285385,2000008689501069],
   [2000001105566180]]
private def pv_m2_r512_7_2 : List ℕ := pNatCat
  [
   [2000093110533946,2000017138597856,1999962210569448,1999903659418077,1999950516883164,
    2000006394705697,2000086610308669,2000227987215442,1999968016177529,1999948520752004,
    1999856320087877,1999997741510207,2000057256996556,2000001573900185,2000021452162167,
    1999946425969491,2000044837035794,2000084898183175,2000016799798855,2000068468029942,
    2000181096044265,2000003349172837,2000026134457436,2000076742381562,2000006400079836,
    1999993830595073,2000142950963104,1999941858470054,2000058155694531,1999974822880361,
    1999930323688064,2000200396586714,2000133922047391,2000069246939089,1999987169380324,
    2000093569654293,1999983765838445,2000138148622081,1999880256422459,1999985179987123,
    1999870941700198,2000248636519002,1999728674550981,2000233859492266,1999700436269156,
    2000040855416997,1999984725435252,1999599754053258,2000061953983068,1999900291897019,
    1999792465689218,2000179224554195,2000193281513885,1999938738134955,2000024898635852,
    2000410477196975,1999877066361551,1999977449611783,1999990464329156,2000094635011889,
    2000113738241020,1999922697065109,2000091406291121,2000228029176742],
   [1999699197800717,2000097049572903,1999922184485184,1999959088472346,1999871652180594,
    2000005418188990,1999938498045582,1999649511787897,1999689849743586,2000074256451765,
    2000358755920456,1999657005691697,2000577809131366,1999873178963342,1999966118583635,
    2000525495430494,1999996986523822,2000451983845685,1999394517006921,1999823283298042,
    2000646082030403,2000092865529340,2000072936612080,1999970702618123,2000472075025139,
    1999955280542627,2000830366074150,1999976096749245,1999328953950391,2000077514064092,
    2000028946206291,1999878377505747,2000235398879222,1999557951552987,2000543857951058,
    2000656620931359,2000305282514118,1999957384914223,2000097368920910,2000012387858057,
    1999892294187034,1999363293329620,1999751845091934,2000011920437720,2000176050617577,
    1999975664210691,1999973897162678,2000447193995366,1999823522189545,2000212349846424,
    2000365969625573,2000540642330932,1999920873553748,1999267027450244,1999866969637411,
    2000122313963723,1999376556627735,1999625632779456,1999893144802351,1999996518312915,
    1999915038693742,1999757185711255,1999628880405436,2000117969334366],
   [2000058712614898,2000064914187714,2000388093283119,1999954247902496,1999713763530971,
    2000127587623017,1999988038333312,2000006031415422,2000555478556176,1999990316668902,
    1999545742083209,1999625720430958,2000263132990286,1999224916952963,1999978178316055,
    1998999861395154,2000442514382651,2000097552352495,1999494959594816,1999914658844175,
    2000311125837914,1999075048401141,2000445680851908,2000464287616268,1999432075108113,
    1999581608407730,2000817444041284,1998824294345880,2000724515300665,2000534284721353,
    1999379598246839,2000506039372225,2000047987496932,1998787481523937,2000066747505024,
    1999068572760793,1999512808357608,2000657971504021,1999925276322747,2000102952221047,
    1999659449589770,2000735901425068,1999324065856284,1999536772826999,2000798633542730,
    1998707166725301,2000265413828828,1999979776283393,1999759998106936,1999703455856599,
    2001405096480518,1999221778495946,1999688257580689,2000613091791085,1998857464329884,
    1999483975853089,2000643089864057,2000064154397042,1999897182323514,2000514307532773,
    1999019205250223,2001020938560301,2000490828372736,2000727796188329],
   [1998709961402211,2000313161242661,1999597889132429,2000528106093351,2000373384161411,
    2000329769326432,1998848950702887,2001391856072688,1999958661407260,1998823014882082,
    2000600768935588,1999806091212866,1998107682669191,2000336997426036,2000509010035953,
    2000607801927983,2000419211764801,2001143212158201,1998937221839733,1999576209503124,
    2002011098097031,1999783273438454,1999612276602455,2001030003770820,1999227784351578,
    1999269861759646,2000199779746677,2000069752882325,1999830765716805,2001236052298031,
    2001243639483990,1999296753343912,2000034898634542,2002622016765291,1999597505465731,
    1998850119279372,2000254471698326,1999733708593607,2000817883602730,2000261277006848,
    2000090777984204,1998485569815419,2001026908651709,2000112559046647,2001035828044410,
    1999325284888309,2000744975710396,1998777429818457,2000014114351140,2000685268595060,
    1998209902900646,1999741500870201,1999926404149111,1999444786776082,1998752925941152,
    2001451810087358,1999341246868392,1998762328018608,2002184743057260,1998802087100525,
    1997543723934030,2001856929057652,2000190948603375,1998431174847207],
   [2000434994677779,2000029329564624,2000329738774057,1999420945807222,2000152665952724,
    2000810542646233,1999914621976087,2000238821944091,2000575940809062,2000448970048544,
    1998741134725892,2000188167431423,1999945184839525,1999853811449327,2001163204964113,
    1998662780353730,2001559914498238,2001315208604415,1998382843310891,1999939488992076,
    2000004199225778,2000317786976332,1999405620829248,1998733390201196,2001898373597164,
    1998991474553490,1999567754612040,2002833924316560,1998973424749519,1998243828990983,
    2000420298427766,1997948115066802,2000895282049964,1999793342240482,2001753686474791,
    1999870642297240,2001963486953574,2001739118346981,1999012979774156,1999805579838329,
    2001249074997821,2000441494651427,1998400979312337,1999306740290033,2001199110671469,
    1999951597192315,1998953159368247,1999554982491903,1999268378213238,1999303708706373,
    2000438652174235,2000591279468837,1998416165987531,1999364035237767,2001051706864851,
    1999856603076257,1998967462400902,2001809029129614,2000128010720762,1998726568947609,
    2000134108752036,2001346369998280,1998833184062797,1999735087799704],
   [2001670789192867,2001539669597192,2000708355491603,2000186099955542,1999426198556591,
    1999026841684696,1999295412333880,2001201674344216,2000520993602988,2002077826147590,
    1999439600998168,2001572862803914,2000848099568219,2000878409266113,2000992352201127,
    2000385338432444,2000914147457701,1999775259439745,2001135764142263,1998146858296406,
    2001909925873222,1999331799376326,2000208868651591,1999236390787915,2002061438317891,
    1999359610458491,1997852278495906,2002810121828544,2000528680593504,2000006586129315,
    1997170736793059,2004096151775902,1998732600267852,1997676941336502,1998742669559465,
    2004617861442719,1996892463284132,1998956886817286,2003054596128743,1998975085917967,
    1998203535039592,1997316916507722,2005241296573779,1996936765428957,1995458802212997,
    2004552717108671,2003062228459933,1996771544499371,1998437095618079,2004150796391236,
    1997380415902989,2002512047852483,1995632712788132,2006522038425900,2001980863988577,
    1988104315093267,2008413790787313,2004307227038995,1994360539486324,1997294677239888,
    2003978498190131,2001019677454129,2000618863464981,1997824193494386],
   [2002512444056971,2004871686139393,1993716287304189,1991458412046249,2011906946960555,
    1996882350638314,1989294398212168,2007713136684513,2004450616933054,1995038440693466,
    1997651357220798,2002324372319571,2006391099176322,1997839770837386,1992447080040049,
    2002661454736990,2009852467400028,1994874657358567,1992896707586363,2010066206543668,
    2000716046088571,1991790371655743,2001788560093909,2001663438566455,2004446769016000,
    1999160230284164,1984720177268965,2004084956704902,2013890394135404,1989346505913142,
    1991509654784192,2018393145149784,2004045068848866,1992435999251326,1997424451367953,
    2008963359300435,2001192412803536,1991647010278919,2000971349262613,2003686493700379,
    2002840098682718,2001237679941248,1994954362833801,1995481371472160,2016300108269934,
    1998034335926850,1982947081586555,2006743248151710,2011364940973733,1987228297201790,
    1997118716039530,2006314643041379,2001013252489912,1988317863780753,2025426385051197,
    1986602471716830,1995623080401904,2012480037356878,1999795832409077,1983908617103207,
    1990709094697442,2017522736641946,2003846616024246,1977627642289373],
   [1999460298915555,2014837609433018,1993621328721301,1995243875690367,2013037085079652,
    1999070446202184,1989144077920337,2012124417060979,2012286550729699,1979337493680572,
    1982140208211098,2020678260527783,2023486852762076,1995140655387295,2000239858416548,
    2024261156900438,2012436600982160,1976978348660690,1991299311625875,2013619384792607,
    2019530969437350,1984193399174442,1985052247218099,2024568937179844,1998589195936723,
    1993590251492416,1978579393564069,2002185960409078,2027250300102545,1995582911360634,
    1990004500028652,2006386242284369,2029049242346786,2006367456774569,2022806986034464,
    1998850673688579,1991437920296582,2066430499213002,2052688406634272,1991812953544918,
    2003392656701827,2032386941741087,2041159527601205,2068882700247117,2100242818376611,
    2079489673139707,2013899012660545,1977034105465380,2029065880843997,2164109444589923,
    2323112473223122,2439608489067453,2476532015272204,2435914927922899,2346304915716991,
    2242643426000451,2151143163562728,2083939950316271,2041508553979358,2018175760917160,
    2006972947337105,2002302003047497,2000634270294591,2000137665671352],
   [2000020398319189]]
private def pv_m2_r512_7_3 : List ℕ := pNatCat
  [
   [2000066605067633,2000053128224523,2000054406513641,2000016453567579,1999909596642503,
    2000018973417528,1999843182404742,1999953431933428,2000046397101647,2000121708672533,
    2000187573403443,2000015466634299,1999953950310711,1999919483215532,1999926714661820,
    2000000555905178,2000090649745718,1999930758129159,1999975341754066,2000056134930619,
    2000023600724052,1999904058714534,2000143749133995,2000041906972019,2000038164681093,
    2000173881496720,1999986831764769,2000084016504595,2000030352365982,2000040322248441,
    1999932733786714,2000219843337714,1999960969256852,2000089875047074,1999773681801116,
    2000204819492305,1999802548862114,2000374035521444,1999973547371348,1999960996020913,
    2000234513804522,1999896978464682,2000203907075858,2000088743795276,1999763075964638,
    2000092424089408,2000057998053902,1999924635653573,1999876378178690,2000279734157282,
    1999812429582660,1999868942536866,2000151768693314,1999890388840833,1999707732454170,
    1999902461530791,1999819119096378,2000187228574695,1999707884078409,2000003375547913,
    2000247559462599,2000104661689310,2000032684764535,2000063432750267],
   [2000177998259035,1999844674102953,2000158211129789,1999794821515872,2000439443873903,
    1999820066774568,1999872367705249,2000639510009657,1999492589185660,2000062457199824,
    1999989386978770,1999914370452355,2000318113459711,1999578866089224,2000092422061469,
    1999655967747755,1999772862526296,1999654127810898,2000529636972488,2000094073406165,
    1999402795774812,2000230926009963,2000472473374218,1999941624792734,2000698384590869,
    1999703520181545,1999747941800293,2000200184514222,2000249008071727,2000084036160808,
    2000016109898149,1999679322811619,2000339281575772,2000598607165056,2000419237346473,
    1999984368549666,1999826861655829,2000373075395987,1999952019871408,1999939951919324,
    1999448623924588,1999957109536548,2000375498472898,2000058304421419,2000140193658514,
    2000436070113598,2000450372497658,2000387004445866,1999729893328159,1999970654900925,
    1999995779762321,1999425162154691,1999556270608170,2000413455861632,2000147270454988,
    1999660917599221,1999829132111381,2000086077631029,2000496773733310,2000424154817135,
    1999974112262850,2000161449430444,2000410910578081,1999606636101754],
   [1999904944026081,1999555232123239,1999857220654667,1999335886160624,2000621225281301,
    1999281928419994,1999908957150858,1999836473397765,1999650323024637,1999825177281877,
    2000298760128931,1999940620590323,2000694203266337,1999381261278881,1999638525428794,
    2000388638245436,2000685053552413,1998989867579821,2000853623700766,2000259784679870,
    1999197006214244,2000683062607657,1999890956304796,1998598574196577,2000459996148582,
    1999552733008357,1999438466147368,2000720002864729,1999123392045152,1999932770939135,
    1999834630137535,2000017112886624,2000054419288036,1999756127913161,2000605311193992,
    1998711892106531,2000721315562143,1999831324061774,1999500144878624,2000155216056785,
    2001130206943583,1999566299354458,1999963917466738,2000359854917410,1998465455678907,
    1999805411806240,2000137967766118,1999169096021958,1999741264669915,2001301345552721,
    1998717469140676,2000638419677400,1999851522816368,2000245190673437,1999276089490343,
    2000414105190438,1999179026040215,1999990693515902,1999687677251190,2000197025697059,
    1999732873893178,2001221343122758,1999821953379824,1998803844904878],
   [2000172148305367,1999948677490281,1999429376263701,2001267063740382,1998735426943076,
    1999204848788471,2001060697922751,2000913856305901,1999567820912781,2000075844023320,
    2000904618252106,1998943287217825,1999831527410550,2001322824820018,1999010325581606,
    2000143218261408,2000897442191174,1999315233012140,2000103044387589,2001421228104828,
    1999598091255595,1998629808189038,1999195302751547,2000228643353342,1999387171066281,
    2000671406000468,2001370201554389,1998376696364445,2000945028354888,2000682353092162,
    2000001322001405,1999263491386777,2002422336502529,1999698718300131,1999698486691416,
    1998912219278773,2000332380149966,2000124907533502,1999953069331242,2000494059654609,
    1998789720395131,2001752126431326,2001368881594160,2000400938593098,1999841851852073,
    2000246585138567,1999582620354829,2000207357712977,2001820591458038,1998692739072236,
    1998945860380056,2001812218705501,1998948753793649,1999559723813904,2002491273349162,
    1998561259293738,1999682567849882,2001657436826367,1999465633555590,1998901994364687,
    1999952608823614,2000667126579297,1998591577685147,1998825694310662],
   [1999807109553161,2000629788724223,1999704775388964,1998980716397206,2001230646958336,
    1998728830740828,1999722945162759,2000414967283841,1998778248073127,2000729211067526,
    1999343662043394,1999353482854762,2001351990806366,1998816323646256,1999825152789017,
    2000211387012493,2000931763895992,2000923939776954,1998533028192368,2000781807132194,
    2002111857789767,1996554398335130,2001287168821656,1999919173570127,1999917780482105,
    2000170474533713,2001224846547161,2000134609704451,1999103768964605,2000938290126194,
    2000020295303763,1999419582236637,2000010984427340,1999154488430547,1999217115376614,
    2000981827794619,2001577149781040,1999685970600828,1999050272228641,2000772108015483,
    1999491672487470,1997801015415082,1999120424218256,2001626943212670,2000566460445206,
    2000142060830238,2001010560799981,2001539999210179,2000010699713093,2001462131989765,
    2000030463837619,1998519949270980,2000270532045498,2001829017595311,1998964027082730,
    1998774846106055,2000683251890503,1999304988763193,1998572083969955,2000819896050431,
    1999958018549020,1999194778250046,1998452637335661,2001366526200181],
   [1999095216935906,2000355821435042,1999612741897261,2000476306612790,2000866633274436,
    1999218454686121,2000217268261003,1998782832449490,2000622341560004,1999560002933125,
    2003324098874166,1999929501704667,2001238862623309,1998862956201503,1999444996169347,
    1999981059433406,2000127534255431,2000927478822312,1998885883059979,2003495523305516,
    1998768391747479,2001521840102028,2000411956883150,2003261851545616,1998077794704143,
    2001431285416437,2001477517410000,2000844610623760,1997148216923647,2000872037776337,
    2004389340001939,1995259925643965,2000885239613617,2001437366729077,2000810886090350,
    1997447142961861,2000190693121932,2004634382122218,1997027463215834,1999087593361345,
    2002539356588896,2001679420923094,1991756585273221,2005711353317754,2001108975762653,
    1996580250820841,2001888928347522,1996449620483921,2007209894084675,1994991093674973,
    1994823274858364,2006573161937288,1998990418723002,1992894113669348,2006571083612143,
    2003091934669290,1994449143188951,1998336886822554,2004706808745282,2000495463258386,
    2001239334817927,1993554237669279,2003746011487710,2007916401143673],
   [1989590138301052,2000689376794748,2010173306145389,1991987583088808,1995474132389921,
    2007110329984403,2003519808227849,1996229971032450,1999184402654882,2003707201998758,
    2001474345695919,1994285951501438,1993509736803147,2008645307889877,2002835137494147,
    1986494830701192,2003935844266604,2009334717121716,1993678837061642,1999670263140784,
    2000960009756225,2001186045956196,2002923546223546,1994075696119503,1997495769485004,
    2017092451845307,1992355080913846,1986410599886059,2010572899859658,2009514643767872,
    1990980374326106,1992543106569831,2010136289105553,2000423788747370,1988806568504838,
    1998465596482756,2008712310258776,1997907171581124,2002868870315025,1999783421060400,
    2000224866469088,2010538333260584,1997527620617319,1983792364037747,2014831513794175,
    2005578487095531,1992475163905258,1987784205642069,2025525236850112,1987606177664095,
    1997331149599923,2011359729653375,1989725951610541,1999982870402045,2008190633423877,
    1996040636570886,1988427968289352,2004299556341300,2013116519753031,1988792391999993,
    1991311223283460,2022396591191331,2006414133521617,1978237907464049],
   [1999250370021192,2012267517726386,1990967149253271,1993463818574333,2008034987175479,
    1992470016885167,1988406334453174,2013311107319765,2009138956949334,1980941821134347,
    1997736181240580,2024718661656437,2008623766498885,1971522158319622,1997422688713916,
    2012930520270864,2000252241820898,1992794208798971,2009591721943438,2042846558419891,
    1989134699888239,1986732219410538,2008625873824662,2010112472023475,2003591615410534,
    1980106356469150,2009623594518581,2018134020346709,1999411523364487,1968460319094912,
    2008883827882775,2010811366496488,1990166657059965,2012680531724710,1984656628371516,
    2002812036182126,2050317479056504,2002665997076773,1971187636438457,2024378955234805,
    2051275035458800,2028738498852067,2017746964811894,2014045578860392,2004706731418215,
    2026658642629991,2085038785226153,2115366560103359,2069603958186751,1988264970642825,
    1962960147583952,2047573121997898,2214840675303807,2384621006342457,2482986012708079,
    2482234573101069,2402567987509804,2287745785962605,2177989582483723,2095476338012671,
    2044173925063158,2017380308201112,2005656344687945,2001440356580235],
   [2000249138552361]]
private def pv_m2_r512_7_4 : List ℕ := pNatCat
  [
   [2000036533914307,2000050695214560,1999999710269916,2000144061864887,1999980364957397,
    2000003020037173,2000042489127370,1999938825361984,1999951567408335,1999882754926523,
    1999900195201578,2000005248626167,2000144726719410,2000088722281988,2000143379556178,
    2000051002519423,1999949425390033,1999836861540425,2000065773186878,2000025048375623,
    1999864704533750,2000100797863880,1999963404615156,2000018281937025,1999946509584029,
    2000102642176786,1999828000180269,2000207352250551,1999901109253980,2000243955467787,
    1999836295738149,2000309936345357,2000012817580357,1999907224837328,2000205318673036,
    1999839009288500,2000129722422088,2000241027786837,1999848898408756,2000075846960900,
    1999921788650280,1999965244311987,2000012313136435,2000280568729124,1999895401555886,
    1999917892364576,2000287312423966,2000123705977154,1999814313674797,2000324688541352,
    1999934303678605,2000006830969811,1999928023735845,1999987453228096,2000190938559193,
    1999833314681247,1999944267222585,1999982728908402,2000351360479049,1999635944086644,
    2000016865364921,1999906924667753,1999785882641247,2000198990190470],
   [1999327658368596,2000244035758391,2000079687512913,1999506056670066,2000527743906644,
    1999917791573597,2000225140625749,1999866327969123,2000186622513784,2000046504336345,
    2000039295438270,1999891168893106,1999976628417486,2000346945509022,2000158442644513,
    1999507405282225,2000629163338056,1999783693953270,1999546887657961,2000365408983030,
    2000294457310881,1999803111053552,1999953788280270,1999538324128900,1999792604577407,
    2000164296967644,1999944486702071,1999944521823267,1999538674383165,2000058374007917,
    2000095840047561,2000539036424507,2000263278357334,1999727866011505,1999973592143313,
    2000254539229185,2000319664895910,2000188110587813,1999475122762216,1999912050163638,
    2000339893695351,2000323346303709,2000131075958412,2000062592851822,2000298242377729,
    2000593056080556,2000058541888128,1999641182744751,2000202808102282,2000013152327900,
    1999526144932246,1999813376944632,2000373909817142,1999913078034053,2000435703306540,
    1999947827384727,2000935405545251,2000217195360650,2000266495368979,1999045943103265,
    2000250996199064,2000062040653389,1999692304483772,1999915771634828],
   [2000005427982077,1999348930955313,2000539368142419,1999797635410186,2000254489881559,
    2000118548468422,2000560608363745,2000009710415908,2000636762438412,1999568414393193,
    1999574171794881,2000566956909539,1999184936407703,1999225080114010,2001246257238543,
    1999363458479925,1998853248875395,2000729037620316,1998925462007492,2000205941068256,
    2000565465466655,1999439632839328,2000293627088855,1999591165919022,2000616300450861,
    1999269994032939,2000679755666218,1999717418941169,1999912091635909,2000646364819304,
    2000276187465128,1999549758551671,2000030981647418,2000026762763465,1998679224684681,
    2000643432043097,1999989341164897,1999147702689201,1999586251250562,2000922012180319,
    1998300264493144,2000967419469421,1999701412358340,1999741829043171,2000048105888258,
    2000638627620777,1998747528586787,2000031868527339,2000003100262036,2000177471908449,
    1999935527799533,2000794849700943,2000132123150926,1999622817889910,1999930439532439,
    1999522286922894,1998876110924296,2000860650537976,1998945030256533,1999599520182828,
    2000954837603728,1999458330339492,1999738834286784,2000485467540387],
   [2000067775784658,1999573395246422,2000051059711723,1999787313671787,1998149468000652,
    2000964911785440,2001492930369477,1998824587827295,1999729218947583,2000729002937263,
    1999079314707263,2000362142845804,2000429719095774,1999059008655290,1999437577979300,
    2000046603524962,2000716826213218,1998675041540727,2001896057295300,1999973315075739,
    1999428377815966,1999705019159838,2001535025444196,1998807229405763,2000578003443721,
    2000203756357178,1998771483841467,2000621973404719,2001145389352812,2001145638178280,
    1998359564224527,2000285480520277,1999791707245909,1998861870827486,1999767850273486,
    2000149257053021,2000399036731442,2000218032780873,2000075307252798,1998957876160243,
    2000515503658734,2002219751407999,1999556539482505,1999601167581857,2001542397813994,
    1998333923047375,2000697773350998,2001466498988864,1997217399873524,1999816006451872,
    2001429202636898,2000216738125888,2000337535009483,2001530770305682,1999798689676899,
    1999245947869194,2001715671832926,2000309539814731,2000029924747338,1999130124286507,
    2000716139748027,2000820068637467,1997954007220193,2000954647618545],
   [2001132460376811,1999099684055496,2000963652077370,1999299911474090,2000684861184120,
    2000584323472298,1999046038711669,2000055036404953,1999562902226054,1998488064042636,
    2000777402309463,1998105482308173,2002009284380616,1998278512372902,1999198846654605,
    2001890416752604,1998958914994919,1998372181212932,2000506748861275,2000928085608949,
    1998622570282355,1999589832925828,2000772816166551,1999080791906245,1999706528242838,
    2000664275181632,1999792575764172,2000213318682868,2000945713486426,2000518033592384,
    1999327434029610,2000082206291990,1999673964338244,1999478684371347,2000431645847785,
    2001327051673372,1999032719597290,1999631045952776,2001321254241116,2001546428837995,
    1998464337155824,1999312627734173,2000727124088032,1999227884454303,1998834156290872,
    2001130641717369,2000832649704012,2000174118814010,2000798419117495,1999467027525885,
    1997247517771654,2000998901341410,1999771423306674,1999184193998770,1998957014260207,
    2002609694254934,2000722777803489,2000243432119213,2001745282821018,1999627664582704,
    2000488500576606,1999419435764333,2001960552869212,1999073118044676],
   [2000395432666106,1998181545377968,2001247080379306,1999150599577293,1999421358035202,
    2000116580121319,1998895103471132,2000515390194033,1998436082986213,2001292479324658,
    1997414298219908,2002105066917387,1999002338620777,2001703607693573,1999381782242890,
    2000091871079094,1997287494186558,2001023210803302,2001527433915464,1999967959734919,
    2001720949373360,2000045988248000,2002209574087757,1995678467950387,2002174904951045,
    2001704960850387,1996777062807474,2001165346589674,2001937045594576,2001685281472782,
    1996594126108107,2003974373411534,2001828671591795,2000793798367683,1996632486110754,
    2005882066487195,2000388190221100,1993265063259624,2008623740440173,1996585459885292,
    1999447363201897,2000845121051698,1999883862759373,2002062303913594,1996536566796441,
    1999222568505384,2008287058006124,1995314572503257,1996031707687970,2006231654857851,
    2000614282800722,1992013299973992,2005361200166758,2001323186853163,1996046945384376,
    2002057932370445,1999046821303043,2003478497130229,1997439449836050,1990835579464867,
    2009599535102604,2002552783031296,1989425858272187,2003418228474355],
   [2006684246930861,1994107408945995,1997659469317697,2006845883895558,1999233783176497,
    1996122417922910,2000418517731280,2003996017976987,2003849277985581,1991743489941020,
    1998673747605837,2011750042618811,1991125509047181,1994917283755831,2011722140622045,
    2001677408512225,1993322321434832,2002720454178970,1997411596119411,2005148594735773,
    1996287143052284,1990284508403095,2010087576447902,2002011898798068,1988334731406048,
    2002415574116595,2014056263906473,1992265267142189,1989048749697480,2008457993300193,
    2011395788297748,1987982430795166,1998103898862490,2009006258359213,1997404364827043,
    1996309043692693,2004740435219745,1994783060334140,2012198522782241,1989366088256659,
    1995789401021260,1998731762917687,2015209486098371,1979392277908883,2000223614352157,
    2024834695208319,1987261232378728,1996868250707657,2010492736830805,1996508854334670,
    1998648766787782,2004405483410882,1997659300651351,1994824360053815,2008904056395638,
    2006037513986486,1985636479246602,2001782937965524,2018274159317478,1988956993772472,
    1985460138776350,2016950667892910,2003719744902922,1979331241898830],
   [2002810035844061,2014831786669252,1995664804752993,1998907135832931,2010395304843827,
    1989140482356460,1994058148296369,2011509111696035,2003695729264821,1973624650331736,
    2002680684439844,2021593172828369,1985517153707836,1986693417058997,2001224363491995,
    2030471631019531,1986960413149591,1987500736241883,2020753098769686,1991152212640981,
    1984122593546022,1995165517992207,2030023024172697,2013093435504521,1996458403576287,
    1995368556931318,2026453198096925,2000123831302819,1971794849110102,2022544476449486,
    2007802307445345,1995693711835512,2005932092570110,1976620607043726,2003744520814352,
    2027525797829006,1974441358950288,1976929588432112,2035290209036392,2025697475652168,
    1986358762831274,1995741256459154,2019478547036912,2028250997336197,2038171343574571,
    2032895574446958,1998532153461949,1986384636225407,2041626816692334,2114827982642805,
    2114373501961132,2027721662317183,1947184391819408,1976723005622952,2133293545162485,
    2337525353926082,2483181883123334,2511170613017953,2432808740692531,2302740822013130,
    2176728742250939,2085682865184679,2033762430506261,2010271483267621],
   [2002100942214179]]
private def pv_m2_r512_7_5 : List ℕ := pNatCat
  [
   [1999993132319758,2000094811249943,1999951112682602,2000024940396165,2000119344150028,
    2000016514239412,2000036754862547,2000025872707006,2000030987256552,1999980152859845,
    2000052270933876,1999920569100563,1999891994243445,1999859283202451,1999988641611810,
    2000011537911042,1999948288430110,2000300972907379,2000082495391538,2000055608673767,
    1999870012500019,2000173149390114,1999751143573061,2000167996282825,1999809096950365,
    2000136770705054,1999893466012888,1999978762843225,2000200018904897,1999759597774276,
    2000039614190170,2000141835623051,1999790347165688,2000180414259300,1999982638341438,
    2000020883915443,2000090172905050,2000224783023472,1999949297639490,1999982824619046,
    2000087442220454,2000044358734770,1999851314523993,2000459735070669,1999965632400796,
    1999765355475656,2000124857029392,1999972480222256,2000116511144749,1999834017897845,
    2000186656484185,1999942768466427,2000195617854690,1999896605082836,1999997589271517,
    2000559503078580,1999635924491332,2000156275183976,2000069817984832,1999798671769288,
    2000571540747070,1999374727237249,2000128772718331,2000174551397149],
   [1999986623075401,1999863930660130,2000116334179944,2000047658143034,1999875766448220,
    1999815664065384,2000122064412349,1999624883844824,2000164019761992,1999547423851887,
    1999818677028353,2000461127765922,1999791178885055,1999668253213998,2000609701919515,
    2000074419982741,1999707890448009,2000321016219387,1999954640753873,2000057673308743,
    1999806030676454,2000208706946045,2000185014375955,2000153038689579,2000031312462305,
    1999676662372168,1999930313722487,2000298081510274,2000090278252182,2000262099664079,
    1999756121998369,1999633516810488,1999925650082124,2000061940660214,2000105599270030,
    1999841097103675,1999409054980055,1999689398847304,2000361601264655,2000250508659657,
    2000129877681704,1999731151838971,2000025336346380,2000302147145604,2000815122541138,
    1999315041563148,2000224883642009,1999932120816727,2000366522299802,1999489227019894,
    2000283501119036,2000126885110022,2000296955278119,2000221009420134,2000222498031441,
    2000156573527366,2000910273663543,1999219963621288,2000064481453216,2000124723069369,
    2000021613744035,1999445602173943,2000019707055556,1999875748617628],
   [2000371387956543,2000918603502715,2000053232874750,2000103016891120,2000454503086927,
    1999452757085231,2000131633282994,2000788500231470,1998426135265383,2000478983684367,
    2000694108027438,1998345919101790,2000727576184920,1999805826042993,2000271109937659,
    1999663034221045,2000841015979808,2000212077664816,2000226564158696,2000396317600526,
    1999395609076442,1999745981852379,2000158904774533,2000224795838077,1999245537144729,
    2000516436365675,1999006882719196,1999652984956761,1999943496794350,2000537020959678,
    1998415701305931,2001353452232960,1999533587137822,1999551301465687,2000528798317310,
    2000286442380034,1998759673060008,2000757021272715,2000168518435564,2000019491322138,
    2000455849402935,2000242209902413,1999389988907220,2000040634099388,2000108585450338,
    1999764262195899,1999041481157866,2000766197741128,1999375602866946,1999322323163898,
    2000468297294768,1999021960415142,2000115193863720,2000666967801458,1999336259756014,
    2000075816346956,2000129721574554,1999511012081385,1999009528087723,2000687823483457,
    2000392390682174,1999450712238536,2000958616720440,2000535624780507],
   [1998693270644855,2000654451970423,2000083714397057,1997925492844953,2000783427032176,
    2000032147754567,1999799585590803,1998348747694811,2001395761625680,1999727837974274,
    2000449794421834,2000139126543666,1999611873184160,1998268501875769,2000828578162614,
    2000720881937411,1998347692704228,2001148149994312,1999763960797712,1999664542300169,
    1999831948652962,2000969242503534,1999664161502786,1999058426921530,2000471013398033,
    1999089917630273,1999480312042187,2001008666248051,2000519454331780,1999036695876415,
    1999812359928317,2001178202791716,2000318733220675,1999644311835332,2000504284534192,
    1998467434153260,2000441104902926,2001475603430128,1998162353412352,2001823690191839,
    2001517683591246,1998296858800036,1999733835474806,1999931852826437,1998945807277022,
    2000278811379799,2001575002487451,1997825352443266,1999469859615772,2001363407554217,
    1999979298653573,2000474940342391,1999838632349640,2000740196849528,2000475078237196,
    1999589248050857,2002319539064184,1998362052041717,1998261613635622,2001082091223988,
    2000127228736721,1999778705986335,2000831630735452,1999441268014700],
   [2002410075312498,1998439636814332,2001326523323460,2000593896418367,1999978171063404,
    2001084491748725,1998601541959843,2000433346236156,2000775662883993,1999037628024769,
    2000203030834958,2001169473580997,1999260680392616,1999321753516543,2002070410430563,
    2000473215757797,1998257204770827,2000599285412088,2000388518223295,1998721185635753,
    1999040924147529,2000345756462895,1999406991234718,1999876206720295,2000015469242614,
    1999689493896562,1999061107393192,2000597083723924,1999508830517212,1999444935158099,
    1999991513466542,2000237507008593,1999119195502920,1999620689542666,2000489029445322,
    1999304036529714,1999021621436002,2002030544685624,2001177230830679,1998852585227565,
    1999030315807182,2002200204497748,1998646319463752,2000077927352752,1999999616541187,
    1999893729673066,1999922168897174,2001061269791655,2000737362522059,1998636619594187,
    2002568006377223,1998916811394759,1998710456421584,1998358105534424,2002261422551908,
    1999383972563645,2000880897585952,2000122960219129,2000254522994207,2000113739888339,
    1998245395471730,2000881827832389,1997427831104322,2000664195336234],
   [1998883333777700,2003296214526051,1998852542721196,2001659569968778,1999760066265506,
    2001228933290694,2000217158227655,2001055741810985,1999676235531177,1999582655419063,
    2001419321180588,1997744824680072,2001729559201273,1998104473237526,2000652197710422,
    1998915430945580,2000099614907170,2001237691893044,1995204437729805,2001952405638398,
    2000512974172710,2000502701932830,1998259476258712,2003687971112887,1996795392096811,
    1998230366105576,2001068376602293,2001293751569929,2001835541664035,1994763999043708,
    2009315103896010,1996535282637865,1996004287927033,2005844581410064,1997984783769451,
    1998049958247256,2002466017412610,1999111679783590,2002525519686164,1997503940937737,
    2002407276149685,2004351201604248,1997334701595035,1998089802222058,2008668932023709,
    1996833415405006,1994161144778231,2009303446771386,1998648448512302,1995539804847418,
    2003625312787815,1998287994084821,2002373259719534,1997708278157123,1998989195129217,
    2007587391829640,1995136638092972,1995287912092172,2009135471060238,1999514867740585,
    1989547010250893,2005257057989353,2006638160526171,1993396971873525],
   [1999567510101308,2002956528229859,1998461526224985,1998755311735673,1995959683420544,
    2007382470754949,1998479942651052,1990315784382704,2007597192334357,2007436497131216,
    1986255789959017,2004309697293881,2006261436051533,1994824212029080,2001379865256671,
    1998752137600517,2005244404420706,2000980540727544,1990732478263044,2000601074688473,
    2011625317138249,1992879849796047,1995394616797341,2010117941235659,2004631659280541,
    1985680256991206,2002682201035989,2012081570201992,1990749399326122,1986617637416503,
    2017315069269561,1994083724801084,2002278357216633,1992911826092666,2006378830363262,
    1997675032323238,2004697781590582,1992566576687218,2002053280016956,2015826049135543,
    1978583720822842,2001308902583200,2020344866075339,1987062739431474,1994694400865596,
    2011772207189763,1997540251858512,1991088822808878,2001071940925126,2000634970435169,
    1996492000332558,2007508829316789,2003129632568307,1989988123981712,2008983614310954,
    2011628348751665,1983333196923311,1997467275867564,2020453671486470,1991527103482003,
    1986332799995875,2016222490206672,2007017150022537,1982283901974008],
   [2007258480100061,2007672552027467,1993771746240256,1995737918954404,2006343033051831,
    1988881274024994,1995256952977612,2027048060192991,1987996482799199,1991349151008264,
    2005244777774740,2018446749928576,1985113991653302,1977105342371025,2028220011604828,
    1996456386512988,1981281503502174,1996694640634820,2016180239739750,1990650139718773,
    1997493787092012,2012156642630619,2013492722516708,1983644366319799,1970768936371523,
    2030019966315364,2004418283770727,1986433195244200,2027884214208231,2006743518984103,
    2001853262866025,2004553343557973,1982818608114953,2017907960628554,2024203576452261,
    1971084273907235,1990521944452086,2031443812689987,1994209512535672,1968766422911784,
    2003769836517989,2021392802329692,2007185543618931,2000121029005908,1997237544130861,
    2002811418868514,2035138199470203,2055314666225884,2016398029650068,1967781051096402,
    1999377917299194,2095812940598040,2138100870093238,2060430184168756,1945360362132526,
    1938638026984311,2096112907947493,2332730757634868,2506174777898854,2532170825046010,
    2427839082526487,2271152618939181,2134917381539977,2050573451910601],
   [2012516123157088]]
private def pv_m2_r512_7_6 : List ℕ := pNatCat
  [
   [1999936396184270,2000066511580337,2000073998939887,1999942277669676,2000005407919833,
    2000036103594493,2000087671298350,1999998527728709,2000078762850329,2000025421012005,
    2000014702268693,2000031400482345,1999960887699788,2000196589034610,1999848152420639,
    1999993825405898,1999820597800251,2000140197577440,1999608883977124,2000104023119791,
    1999976493167172,2000149496713264,2000184469479313,1999929318187565,2000210133062247,
    1999992794838306,1999787597072797,2000263114188156,1999836470239039,1999922956933162,
    2000036832413525,2000039556743430,1999900598745291,2000083745341220,1999979475594328,
    1999985027278551,1999854923103242,2000254057768764,1999894303892738,1999776777708907,
    2000341118820324,1999863248250865,2000092240212329,2000072339341654,2000298627744715,
    1999855017144379,1999857197476089,2000233112623445,1999879802483321,2000422407344210,
    1999863642320521,1999792238232470,2000604402905721,1999439578049266,2000259998128458,
    1999939885672391,1999974890744159,2000217087167703,1999908284639862,1999768541586510,
    2000326213395872,2000159490464891,2000076981196724,1999696235213624],
   [2000452075856301,2000000355006392,1999905436721783,2000195018891542,1999849635224112,
    1999974506947835,2000239683862137,1999681157495960,1999952414858891,2000629805550435,
    1999498920592639,1999903030213737,2000287493242607,2000052026238773,1999682816538184,
    1999822967388018,2000082387969544,1999816359427349,1999693423237025,2000061813550334,
    1999846983667646,2000121588983424,2000023294354190,1999913321613238,2000252016559929,
    2000177974637360,1999949999569916,1999907219702789,1999922556568446,1999992802269454,
    2000447570183227,2000056970759111,2000125588853941,1999667397006519,2000051735271904,
    1999658587853351,2000901470673181,1999784961014075,2000171209265126,1999513465948386,
    1999947495030603,2000087171309258,2000528874738459,1999635420151824,1999319068883911,
    1999636694012292,2000678597961047,1999450302455832,2000204180468466,1999645873828968,
    2000154771021779,2000357884651600,2000049317494692,1999850812920148,2000516359557073,
    2000314441345487,1999461067189535,2000111265630292,2000357782716998,1999739574160897,
    1999921118509277,2000333178482201,1999580974828718,2001074774851357],
   [2000467772632910,1998886432786879,2001778441532382,1999190103892540,2000197926772774,
    2000564331071837,1999493542861297,1999020047108921,2000252984406882,2000643276069480,
    1999493479016038,2000607277144935,2000453798855136,2000382606531468,1999644167507527,
    2000830062087262,1999330228601235,2000560190030468,1999673007805566,2000122874991875,
    1999010176566894,2001120684496988,1999021216268969,1999602332739034,2000475703572699,
    1999857350058515,1999799702692431,2001697944680959,1999609633353911,1999528415711577,
    2000687037551917,1999903401908511,1999479952456095,2000760404237130,1999625201545081,
    1999606012946390,1999578057204800,2000253129535615,1999373738725534,1999497229922828,
    2000559191567653,1999034704027350,2000159076193496,2000965581559451,1998977650809466,
    2000028516987613,2000031933458130,1999755144614414,2000174700803374,2000477121082993,
    1999877436104934,2000057834832531,2000706289742927,1999700346848318,1999194119908056,
    2000690073652305,2000206916230615,1998228466738257,2001601518992863,1998841735039821,
    1999479721144625,1999661096437939,2000655775105655,1998758028854488],
   [2000804884004342,2000556284623426,1999017879013542,1999326783206542,2000461395090955,
    2000099199894657,1998231666861252,2001699522407483,1999977763005126,1999994586506446,
    2000848899491724,1999385235660578,1999195122646564,2000376589067266,2000794925280996,
    1998401995407682,1999126855282425,2000483396628224,1999606211364533,2000056840191178,
    2000966359454170,1999611421735520,1999288690011664,1999870051282240,2000450770748648,
    1999013370598395,1999893745352156,2001321634146509,1997922924214190,2000385688501231,
    2001131045656432,1999153361456794,2001235163115215,1999189631102588,1998383243909637,
    2000847358968811,2001084660275063,1997932642486200,2000132262982891,2001202923311502,
    1998561415517237,2001037220881875,2000873124811055,1999157531071054,2000936887017643,
    1999300866301046,1999832351050008,1998825017818059,2001038607421290,2002297007940357,
    1999252251882672,1998965697952231,2001773864910757,1997722442722158,2001450138313056,
    1999599870592441,1999531599973853,1999312078031009,1999079049197746,2002095916148601,
    1999109267569455,1999123739630676,2000786139853012,2000358191222367],
   [2001184681704772,2000515321226031,1999628557855959,2000481461317619,1999953377288926,
    1998603564185659,2000003920128037,2001472897453650,1998891482768627,1999977485349838,
    2001548304352829,1999932869138442,1999416870961277,2002169396500824,2000533830828060,
    1999078197066239,2000006390000807,2001406706138201,1999413873992939,1999737240840338,
    2000246264280719,1999893990847737,2000071569138227,2000598131836245,2000040943605051,
    2000256081973863,2000603440703416,2000467932569097,1998532225617930,2000225746131019,
    1999587260759128,1999680615433011,1998569399426229,2001626798599521,1998911586406657,
    1998467434694113,2001481586572496,1999662877696371,1998815370661293,1998907227921105,
    2002541621323316,1998085321912008,2000245020625886,1998834820698377,1999792119403377,
    1999492141072373,2001688425130194,1999217089870586,1999335191051559,2002364309941226,
    1998887016900596,2000544741170247,1998420334488750,2002583219643669,1997801191390481,
    2000530976358133,1998866302616663,2002573443090779,1999752711916643,2000803384386972,
    1999971470387873,1999063662609227,1999308457443928,1999791995211729],
   [2001254308192950,1998117710402472,2002564822337064,1998956077047996,2001653443404439,
    1999538562345139,1997965670816794,2000237343871286,1997656468645292,2002549505988902,
    1997643215404112,2002089322128211,2000031372997265,2000758789099631,1999624616825307,
    2003243751928445,1998954871976686,1998324561168901,2005051579324904,1996404120643133,
    2002039531470046,1996498458675266,2003612144810548,1999137343219754,1995837673737341,
    2006107559284230,1996476292280186,1994024373492279,2006670003312562,1997915122398309,
    1999253050964330,2001227639317493,2000425890795925,1998630132358881,1998312987881360,
    1999711064323866,2003533988134421,1997934922308333,1998466493077771,2008033579905284,
    1995142338699119,1996248371652448,2009788075912489,1994298762331281,1997284835839742,
    2005138142555891,1998548325547949,2000563746216590,1998735974357821,2002416143321640,
    2004863159967865,1995586714303138,1999886515549973,2007962570199265,1995862009203134,
    1995798315829536,2010137306007216,1998347248211094,1990847681088716,2008126882135329,
    2000958870181725,1996820262858420,1998365966308277,2003264386548286],
   [2003989518341580,1995933583080527,1995758128341381,2010340289713779,1992886594871689,
    1994074421078149,2014373354910586,1994054156411236,1994207738980596,2005000836720051,
    2001403658811502,1997072594598309,1998008055432562,1998605728951382,2006918752398160,
    1994600183721752,1995705135416460,2007483115783574,2003377926801279,1987499098146328,
    2003583895999722,2009935550091006,1998013712291624,1984999341625463,2022120510972463,
    1990061479200115,1993281429252934,2003608760522621,2010066397836338,1991584662462738,
    1998660174594004,2007941337228780,1996249391021306,2007197131701023,1987559902777043,
    1998849888801154,2015773187102107,1982950231788623,1998396288366329,2017423753289358,
    1988532732777628,1991297079724873,2013446896825682,2001895126241945,1990306936359768,
    2004180213912679,2004621615756579,1993399568749183,2003516154680495,2003151406287115,
    1993408685238230,2008629479654922,2004208504453175,1980859108173164,2004229244173152,
    2013035363675798,1985000008360017,1993506607772220,2024069752858250,1992427856628724,
    1989894985651580,2013196297133973,2004398272921520,1987915902808757],
   [2002491002657054,2013007372723731,1983126748155535,2013808948156269,1998633753617690,
    1991608597438381,2007029349164578,2009756684406768,1994993229562403,1973145834770176,
    2024890626850150,2005117208646463,1979637473439020,2002475393669679,2025355949412313,
    1987559607711737,1988664274503052,2010969322829366,2002318569256153,1993428225289617,
    1985388655119281,2020893459827316,1988320453571848,1971815717747622,2035181567616912,
    2007386069233945,1983352441182240,2005898748140154,1989588096631406,2000797431346696,
    2004295679766755,1990896691316408,2028691030572741,2020046198990273,1971714692808418,
    2005764700432018,2033544228395621,1988145191504630,1983144492790746,2020076451889865,
    2010390078555283,1983918737390415,1988085031013882,1999768588192477,2009921422401911,
    2016043209540962,1995512877665628,1977861188497201,2016713968069306,2066889609565029,
    2036955201008978,1961228592477919,1970905513300080,2083604026169853,2152711697806184,
    2069585541946862,1927489286012732,1921409855518729,2121920080601264,2399557217629971,
    2561796918739878,2525618754570017,2355509785449418,2172470899205765],
   [2053470370458579]]
private abbrev dP_0 : Prop := rkmAllTrueF [
    bSlideChk 16 257 pb_m2_r256_5 pv_m2_r256_5_0 pv_m2_r256_5_1,
    bSlideChk 15 257 pb_m2_r256_4 pv_m2_r256_4_0 pv_m2_r256_4_1,
    bSlideChk 16 49 rkmHbNatPack_m2_r512_s1 rkmViNatPack_m2_r512_s1 rkmVoNatPack_m2_r512_s1
  ] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := rkmAllTrueF [
    bSlideChk 16 257 pb_m2_r256_5 pv_m2_r256_5_1 pv_m2_r256_5_2,
    bSlideChk 14 289 rkmHbNatPack_m2_r512_s3 rkmViNatPack_m2_r512_s3 pv_m2_r512_3_1,
    bSlideChk 15 65 pb_m4_r256_3 pv_m4_r256_3_0 pv_m4_r256_3_1
  ] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := rkmAllTrueF [
    bSlideChk 16 257 pb_m2_r256_5 pv_m2_r256_5_2 pv_m2_r256_5_3,
    bSlideChk 21 193 pb_m4_r384_2 pv_m4_r384_2_0 pv_m4_r384_2_1,
    bSlideChk 5 193 pb_m4_r192_7 pv_m4_r192_7_0 pv_m4_r192_7_1
  ] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := rkmAllTrueF [
    bSlideChk 16 257 pb_m4_r256_5 pv_m4_r256_5_1 pv_m4_r256_5_2,
    bSlideChk 17 145 pb_m2_r256_3 pv_m2_r256_3_1 pv_m2_r256_3_2,
    bSlideChk 18 65 pb_m2_r256_2 pv_m2_r256_2_0 pv_m2_r256_2_1,
    bSlideChk 8 25 pb_m2_r256_1 pv_m2_r256_1_0 pv_m2_r256_1_1
  ] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := rkmAllTrueF [
    bSlideChk 16 257 pb_m4_r256_5 pv_m4_r256_5_2 pv_m4_r256_5_3,
    bSlideChk 9 257 pb_m2_r256_7 pv_m2_r256_7_0 pv_m2_r256_7_1,
    bSlideChk 20 97 pb_m4_r192_2 pv_m4_r192_2_0 pv_m4_r192_2_1
  ] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := rkmAllTrueF [
    bSlideChk 16 257 pb_m4_r256_5 pv_m4_r256_5_3 pv_m4_r256_5_4,
    bSlideChk 17 145 pb_m2_r256_3 pv_m2_r256_3_0 pv_m2_r256_3_1,
    bSlideChk 8 257 pb_m2_r256_7 pv_m2_r256_7_1 pv_m2_r256_7_2
  ] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := rkmAllTrueF [
    bSlideChk 8 513 rkmHbNatPack_m2_r512_s7 rkmViNatPack_m2_r512_s7 pv_m2_r512_7_1,
    bSlideChk 14 257 pb_m2_r256_6 pv_m2_r256_6_0 pv_m2_r256_6_1,
    bSlideChk 1 193 pb_m4_r192_6 pv_m4_r192_6_0 pv_m4_r192_6_1
  ] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := rkmAllTrueF [
    bSlideChk 8 513 rkmHbNatPack_m2_r512_s7 pv_m2_r512_7_1 pv_m2_r512_7_2,
    bSlideChk 14 257 pb_m2_r256_6 pv_m2_r256_6_1 pv_m2_r256_6_2,
    bSlideChk 1 193 pb_m4_r192_5 pv_m4_r192_5_0 pv_m4_r192_5_1
  ] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := rkmAllTrueF [
    bSlideChk 8 513 rkmHbNatPack_m2_r512_s7 pv_m2_r512_7_2 pv_m2_r512_7_3,
    bSlideChk 14 257 pb_m2_r256_6 pv_m2_r256_6_2 pv_m2_r256_6_3,
    bSlideChk 1 193 pb_m4_r192_3 pv_m4_r192_3_0 pv_m4_r192_3_1
  ] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := rkmAllTrueF [
    bSlideChk 8 513 rkmHbNatPack_m2_r512_s7 pv_m2_r512_7_3 pv_m2_r512_7_4,
    bSlideChk 14 257 pb_m4_r256_6 pv_m4_r256_6_3 pv_m4_r256_6_4,
    bSlideChk 6 17 rkmHbNatPack_m2_r512_s0 rkmViNatPack_m2_r512_s0 rkmVoNatPack_m2_r512_s0
  ] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := rkmAllTrueF [
    bSlideChk 8 513 rkmHbNatPack_m2_r512_s7 pv_m2_r512_7_4 pv_m2_r512_7_5,
    bSlideChk 14 257 pb_m4_r256_6 pv_m4_r256_6_4 pv_m4_r256_6_5,
    bSlideChk 4 17 pb_m4_r256_1 pv_m4_r256_1_0 pv_m4_r256_1_1
  ] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := rkmAllTrueF [
    bSlideChk 8 513 rkmHbNatPack_m2_r512_s7 pv_m2_r512_7_5 pv_m2_r512_7_6,
    bSlideChk 7 513 rkmHbNatPack_m2_r512_s7 pv_m2_r512_7_6 rkmVoNatPack_m2_r512_s7,
    bSlideChk 7 33 pb_m4_r256_2 pv_m4_r256_2_0 pv_m4_r256_2_1
  ] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := rkmAllTrueF [
    bSlideChk 14 289 rkmHbNatPack_m2_r512_s3 pv_m2_r512_3_1 pv_m2_r512_3_2,
    bSlideChk 16 257 pb_m4_r256_5 pv_m4_r256_5_0 pv_m4_r256_5_1,
    bSlideChk 1 385 pb_m4_r384_4 pv_m4_r384_4_0 pv_m4_r384_4_1
  ] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := rkmAllTrueF [
    bSlideChk 20 193 pb_m4_r384_2 pv_m4_r384_2_1 pv_m4_r384_2_2,
    bSlideChk 30 129 rkmHbNatPack_m2_r512_s2 rkmViNatPack_m2_r512_s2 rkmVoNatPack_m2_r512_s2,
    bSlideChk 3 385 pb_m4_r384_7 pv_m4_r384_7_0 pv_m4_r384_7_1
  ] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := rkmAllTrueF [
    bSlideChk 15 257 pb_m2_r256_4 pv_m2_r256_4_1 pv_m2_r256_4_2,
    bSlideChk 15 257 pb_m4_r256_6 pv_m4_r256_6_2 pv_m4_r256_6_3,
    bSlideChk 3 9 pb_m2_r256_0 pv_m2_r256_0_0 pv_m2_r256_0_1,
    bSlideChk 2 5 pb_m4_r192_1 pv_m4_r192_1_0 pv_m4_r192_1_1,
    bSlideChk 1 5 pb_m4_r384_0 pv_m4_r384_0_0 pv_m4_r384_0_1
  ] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := rkmAllTrueF [
    bSlideChk 15 257 pb_m2_r256_4 pv_m2_r256_4_2 pv_m2_r256_4_3,
    bSlideChk 15 257 pb_m4_r256_7 pv_m4_r256_7_0 pv_m4_r256_7_1,
    bSlideChk 2 9 pb_m4_r256_0 pv_m4_r256_0_0 pv_m4_r256_0_1,
    bSlideChk 3 5 pb_m4_r384_1 pv_m4_r384_1_0 pv_m4_r384_1_1,
    bSlideChk 2 5 pb_m4_r192_0 pv_m4_r192_0_0 pv_m4_r192_0_1
  ] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := rkmAllTrueF [
    bSlideChk 15 257 pb_m2_r256_4 pv_m2_r256_4_3 pv_m2_r256_4_4,
    bSlideChk 13 289 rkmHbNatPack_m2_r512_s3 pv_m2_r512_3_2 pv_m2_r512_3_3,
    bSlideChk 3 193 pb_m4_r192_4 pv_m4_r192_4_0 pv_m4_r192_4_1
  ] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := rkmAllTrueF [
    bSlideChk 15 257 pb_m2_r256_5 pv_m2_r256_5_3 pv_m2_r256_5_4,
    bSlideChk 13 289 rkmHbNatPack_m2_r512_s3 pv_m2_r512_3_3 pv_m2_r512_3_4,
    bSlideChk 1 385 pb_m4_r384_6 pv_m4_r384_6_0 pv_m4_r384_6_1
  ] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := rkmAllTrueF [
    bSlideChk 15 257 pb_m4_r256_6 pv_m4_r256_6_0 pv_m4_r256_6_1,
    bSlideChk 13 289 rkmHbNatPack_m2_r512_s3 pv_m2_r512_3_4 rkmVoNatPack_m2_r512_s3,
    bSlideChk 1 385 pb_m4_r384_5 pv_m4_r384_5_0 pv_m4_r384_5_1
  ] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := rkmAllTrueF [
    bSlideChk 15 257 pb_m4_r256_6 pv_m4_r256_6_1 pv_m4_r256_6_2,
    bSlideChk 30 129 pb_m4_r256_4 pv_m4_r256_4_0 pv_m4_r256_4_1,
    bSlideChk 2 385 pb_m4_r384_3 pv_m4_r384_3_0 pv_m4_r384_3_1
  ] = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dT_0 : Prop :=
  rkmCheckRowFromWalks 2 4096 256 [4, 12, 32, 72, 128, 224, 224, 224]
    [12070858, 14045681, 13315785, 12623892, 14055808, 10042519, 6642371, 2610897]
    [3, 8, 18, 34, 60, 63, 42, 17] rkmMasksPack_m2_r256 pwalks_m2_r256 rkmRowPack_m2_r256 = true
private theorem ptail_0 : dT_0 := by decide +kernel
private abbrev dT_1 : Prop :=
  rkmCheckRowFromWalks 4 2048 192 [1, 1, 24, 48, 48, 48, 48, 48]
    [19000726, 15616835, 12458892, 16013, 775290, 93782, 8422, 1687758]
    [2, 2, 20, 1, 3, 1, 1, 5] rkmMasksPack_m4_r192 pwalks_m4_r192 rkmRowPack_m4_r192 = true
private theorem ptail_1 : dT_1 := by decide +kernel
private abbrev dT_2 : Prop :=
  rkmCheckRowFromWalks 4 2048 256 [2, 4, 8, 16, 32, 64, 112, 112]
    [9205949, 8711812, 9910783, 10957087, 12137330, 15049393, 11636386, 2265506]
    [2, 4, 7, 15, 30, 64, 73, 15] rkmMasksPack_m4_r256 pwalks_m4_r256 rkmRowPack_m4_r256 = true
private theorem ptail_2 : dT_2 := by decide +kernel
private abbrev dT_3 : Prop :=
  rkmCheckRowFromWalks 4 2048 384 [1, 1, 48, 96, 96, 96, 96, 96]
    [3475462, 20937098, 9131561, 219157, 110278, 1728, 106306, 316330]
    [1, 3, 41, 2, 1, 1, 1, 3] rkmMasksPack_m4_r384 pwalks_m4_r384 rkmRowPack_m4_r384 = true
private theorem ptail_3 : dT_3 := by decide +kernel
private theorem pdim_m2_r256_l4 :
    Nat.add (highdNatMin (Nat.mul 4 2) 256) 1 = 9 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m2_r256_l12 :
    Nat.add (highdNatMin (Nat.mul 12 2) 256) 1 = 25 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m2_r256_l32 :
    Nat.add (highdNatMin (Nat.mul 32 2) 256) 1 = 65 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m2_r256_l72 :
    Nat.add (highdNatMin (Nat.mul 72 2) 256) 1 = 145 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m2_r256_l128 :
    Nat.add (highdNatMin (Nat.mul 128 2) 256) 1 = 257 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m2_r256_l224 :
    Nat.add (highdNatMin (Nat.mul 224 2) 256) 1 = 257 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r192_l1 :
    Nat.add (highdNatMin (Nat.mul 1 4) 192) 1 = 5 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r192_l24 :
    Nat.add (highdNatMin (Nat.mul 24 4) 192) 1 = 97 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r192_l48 :
    Nat.add (highdNatMin (Nat.mul 48 4) 192) 1 = 193 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r256_l2 :
    Nat.add (highdNatMin (Nat.mul 2 4) 256) 1 = 9 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r256_l4 :
    Nat.add (highdNatMin (Nat.mul 4 4) 256) 1 = 17 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r256_l8 :
    Nat.add (highdNatMin (Nat.mul 8 4) 256) 1 = 33 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r256_l16 :
    Nat.add (highdNatMin (Nat.mul 16 4) 256) 1 = 65 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r256_l32 :
    Nat.add (highdNatMin (Nat.mul 32 4) 256) 1 = 129 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r256_l64 :
    Nat.add (highdNatMin (Nat.mul 64 4) 256) 1 = 257 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r256_l112 :
    Nat.add (highdNatMin (Nat.mul 112 4) 256) 1 = 257 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r384_l1 :
    Nat.add (highdNatMin (Nat.mul 1 4) 384) 1 = 5 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r384_l48 :
    Nat.add (highdNatMin (Nat.mul 48 4) 384) 1 = 193 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m4_r384_l96 :
    Nat.add (highdNatMin (Nat.mul 96 4) 384) 1 = 385 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m2_r512_l8 :
    Nat.add (highdNatMin (Nat.mul 8 2) 512) 1 = 17 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m2_r512_l24 :
    Nat.add (highdNatMin (Nat.mul 24 2) 512) 1 = 49 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m2_r512_l64 :
    Nat.add (highdNatMin (Nat.mul 64 2) 512) 1 = 129 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m2_r512_l144 :
    Nat.add (highdNatMin (Nat.mul 144 2) 512) 1 = 289 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pdim_m2_r512_l448 :
    Nat.add (highdNatMin (Nat.mul 448 2) 512) 1 = 513 := by
  rw [rkmb_natMin_eq, Nat.add_eq, Nat.mul_eq]; omega
private theorem pwalk_m2_r256_0 :
    pWOk 3 9 pb_m2_r256_0 (bDec bZ pv_m2_r256_0_0) pv_m2_r256_0_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_14)))
private theorem pseg_m2_r256_0 : muxFastIterFullT16 3
      (Nat.add (highdNatMin (Nat.mul 4 2) 256) 1)
      phb_m2_r256_0 pvi_m2_r256_0 = pvo_m2_r256_0 :=
  bSeg_mk pdim_m2_r256_l4 pwalk_m2_r256_0 rfl rfl rfl
private theorem pwalk_m2_r256_1 :
    pWOk 8 25 pb_m2_r256_1 (bDec bZ pv_m2_r256_1_0) pv_m2_r256_1_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl (rkmTl
    bk_3))))
private theorem pseg_m2_r256_1 : muxFastIterFullT16 8
      (Nat.add (highdNatMin (Nat.mul 12 2) 256) 1)
      phb_m2_r256_1 pvi_m2_r256_1 = pvo_m2_r256_1 :=
  bSeg_mk pdim_m2_r256_l12 pwalk_m2_r256_1 rfl rfl rfl
private theorem pwalk_m2_r256_2 :
    pWOk 18 65 pb_m2_r256_2 (bDec bZ pv_m2_r256_2_0) pv_m2_r256_2_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_3)))
private theorem pseg_m2_r256_2 : muxFastIterFullT16 18
      (Nat.add (highdNatMin (Nat.mul 32 2) 256) 1)
      phb_m2_r256_2 pvi_m2_r256_2 = pvo_m2_r256_2 :=
  bSeg_mk pdim_m2_r256_l32 pwalk_m2_r256_2 rfl rfl rfl
private theorem pw_m2_r256_3_0 :
    pWOk 17 145 pb_m2_r256_3 (bDec bZ pv_m2_r256_3_0) pv_m2_r256_3_1 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_5))
private theorem pwalk_m2_r256_3 :
    pWOk 34 145 pb_m2_r256_3 (bDec bZ pv_m2_r256_3_0) pv_m2_r256_3_2 :=
  pChnN 34 pw_m2_r256_3_0
    (rkmHd
    (rkmTl
    bk_3))
    (rfl : 17 + 17 = 34)
private theorem pseg_m2_r256_3 : muxFastIterFullT16 34
      (Nat.add (highdNatMin (Nat.mul 72 2) 256) 1)
      phb_m2_r256_3 pvi_m2_r256_3 = pvo_m2_r256_3 :=
  bSeg_mk pdim_m2_r256_l72 pwalk_m2_r256_3 rfl rfl rfl
private theorem pw_m2_r256_4_0 :
    pWOk 15 257 pb_m2_r256_4 (bDec bZ pv_m2_r256_4_0) pv_m2_r256_4_1 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_0))
private theorem pw_m2_r256_4_1 :
    pWOk 30 257 pb_m2_r256_4 (bDec bZ pv_m2_r256_4_0) pv_m2_r256_4_2 :=
  pChnN 30 pw_m2_r256_4_0
    (rkmHd
    bk_14)
    (rfl : 15 + 15 = 30)
private theorem pw_m2_r256_4_2 :
    pWOk 45 257 pb_m2_r256_4 (bDec bZ pv_m2_r256_4_0) pv_m2_r256_4_3 :=
  pChnN 45 pw_m2_r256_4_1
    (rkmHd
    bk_15)
    (rfl : 30 + 15 = 45)
private theorem pwalk_m2_r256_4 :
    pWOk 60 257 pb_m2_r256_4 (bDec bZ pv_m2_r256_4_0) pv_m2_r256_4_4 :=
  pChnN 60 pw_m2_r256_4_2
    (rkmHd
    bk_16)
    (rfl : 45 + 15 = 60)
private theorem pseg_m2_r256_4 : muxFastIterFullT16 60
      (Nat.add (highdNatMin (Nat.mul 128 2) 256) 1)
      phb_m2_r256_4 pvi_m2_r256_4 = pvo_m2_r256_4 :=
  bSeg_mk pdim_m2_r256_l128 pwalk_m2_r256_4 rfl rfl rfl
private theorem pw_m2_r256_5_0 :
    pWOk 16 257 pb_m2_r256_5 (bDec bZ pv_m2_r256_5_0) pv_m2_r256_5_1 :=
  bSlSndNN (rkmHd
    bk_0)
private theorem pw_m2_r256_5_1 :
    pWOk 32 257 pb_m2_r256_5 (bDec bZ pv_m2_r256_5_0) pv_m2_r256_5_2 :=
  pChnN 32 pw_m2_r256_5_0
    (rkmHd
    bk_1)
    (rfl : 16 + 16 = 32)
private theorem pw_m2_r256_5_2 :
    pWOk 48 257 pb_m2_r256_5 (bDec bZ pv_m2_r256_5_0) pv_m2_r256_5_3 :=
  pChnN 48 pw_m2_r256_5_1
    (rkmHd
    bk_2)
    (rfl : 32 + 16 = 48)
private theorem pwalk_m2_r256_5 :
    pWOk 63 257 pb_m2_r256_5 (bDec bZ pv_m2_r256_5_0) pv_m2_r256_5_4 :=
  pChnN 63 pw_m2_r256_5_2
    (rkmHd
    bk_17)
    (rfl : 48 + 15 = 63)
private theorem pseg_m2_r256_5 : muxFastIterFullT16 63
      (Nat.add (highdNatMin (Nat.mul 224 2) 256) 1)
      phb_m2_r256_5 pvi_m2_r256_5 = pvo_m2_r256_5 :=
  bSeg_mk pdim_m2_r256_l224 pwalk_m2_r256_5 rfl rfl rfl
private theorem pw_m2_r256_6_0 :
    pWOk 14 257 pb_m2_r256_6 (bDec bZ pv_m2_r256_6_0) pv_m2_r256_6_1 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_6))
private theorem pw_m2_r256_6_1 :
    pWOk 28 257 pb_m2_r256_6 (bDec bZ pv_m2_r256_6_0) pv_m2_r256_6_2 :=
  pChnN 28 pw_m2_r256_6_0
    (rkmHd
    (rkmTl
    bk_7))
    (rfl : 14 + 14 = 28)
private theorem pwalk_m2_r256_6 :
    pWOk 42 257 pb_m2_r256_6 (bDec bZ pv_m2_r256_6_0) pv_m2_r256_6_3 :=
  pChnN 42 pw_m2_r256_6_1
    (rkmHd
    (rkmTl
    bk_8))
    (rfl : 28 + 14 = 42)
private theorem pseg_m2_r256_6 : muxFastIterFullT16 42
      (Nat.add (highdNatMin (Nat.mul 224 2) 256) 1)
      phb_m2_r256_6 pvi_m2_r256_6 = pvo_m2_r256_6 :=
  bSeg_mk pdim_m2_r256_l224 pwalk_m2_r256_6 rfl rfl rfl
private theorem pw_m2_r256_7_0 :
    pWOk 9 257 pb_m2_r256_7 (bDec bZ pv_m2_r256_7_0) pv_m2_r256_7_1 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_4))
private theorem pwalk_m2_r256_7 :
    pWOk 17 257 pb_m2_r256_7 (bDec bZ pv_m2_r256_7_0) pv_m2_r256_7_2 :=
  pChnN 17 pw_m2_r256_7_0
    (rkmHd
    (rkmTl (rkmTl
    bk_5)))
    (rfl : 9 + 8 = 17)
private theorem pseg_m2_r256_7 : muxFastIterFullT16 17
      (Nat.add (highdNatMin (Nat.mul 224 2) 256) 1)
      phb_m2_r256_7 pvi_m2_r256_7 = pvo_m2_r256_7 :=
  bSeg_mk pdim_m2_r256_l224 pwalk_m2_r256_7 rfl rfl rfl
private theorem pwalks_snd_m2_r256 :
    RkmSegWalksSound 2 256 [4, 12, 32, 72, 128, 224, 224, 224]
      [3, 8, 18, 34, 60, 63, 42, 17] pwalks_m2_r256 := by
  dsimp only [RkmSegWalksSound, pwalks_m2_r256]
  exact ⟨pseg_m2_r256_0,
    ⟨pseg_m2_r256_1,
    ⟨pseg_m2_r256_2,
    ⟨pseg_m2_r256_3,
    ⟨pseg_m2_r256_4,
    ⟨pseg_m2_r256_5,
    ⟨pseg_m2_r256_6,
    ⟨pseg_m2_r256_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 2, r = 256)`. -/
theorem rkmTrajPack_m2_r256 :
    rkmEvalT16Lo12 2 4096 256 [4, 12, 32, 72, 128, 224, 224, 224]
      [12070858, 14045681, 13315785, 12623892, 14055808, 10042519, 6642371, 2610897]
      [3, 8, 18, 34, 60, 63, 42, 17]
      rkmMasksPack_m2_r256 = rkmRowPack_m2_r256 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m2_r256 ptail_0

private theorem pwalk_m4_r192_0 :
    pWOk 2 5 pb_m4_r192_0 (bDec bZ pv_m4_r192_0_0) pv_m4_r192_0_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl (rkmTl (rkmTl
    bk_15)))))
private theorem pseg_m4_r192_0 : muxFastIterFullT16 2
      (Nat.add (highdNatMin (Nat.mul 1 4) 192) 1)
      phb_m4_r192_0 pvi_m4_r192_0 = pvo_m4_r192_0 :=
  bSeg_mk pdim_m4_r192_l1 pwalk_m4_r192_0 rfl rfl rfl
private theorem pwalk_m4_r192_1 :
    pWOk 2 5 pb_m4_r192_1 (bDec bZ pv_m4_r192_1_0) pv_m4_r192_1_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl (rkmTl
    bk_14))))
private theorem pseg_m4_r192_1 : muxFastIterFullT16 2
      (Nat.add (highdNatMin (Nat.mul 1 4) 192) 1)
      phb_m4_r192_1 pvi_m4_r192_1 = pvo_m4_r192_1 :=
  bSeg_mk pdim_m4_r192_l1 pwalk_m4_r192_1 rfl rfl rfl
private theorem pwalk_m4_r192_2 :
    pWOk 20 97 pb_m4_r192_2 (bDec bZ pv_m4_r192_2_0) pv_m4_r192_2_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_4)))
private theorem pseg_m4_r192_2 : muxFastIterFullT16 20
      (Nat.add (highdNatMin (Nat.mul 24 4) 192) 1)
      phb_m4_r192_2 pvi_m4_r192_2 = pvo_m4_r192_2 :=
  bSeg_mk pdim_m4_r192_l24 pwalk_m4_r192_2 rfl rfl rfl
private theorem pwalk_m4_r192_3 :
    pWOk 1 193 pb_m4_r192_3 (bDec bZ pv_m4_r192_3_0) pv_m4_r192_3_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_8)))
private theorem pseg_m4_r192_3 : muxFastIterFullT16 1
      (Nat.add (highdNatMin (Nat.mul 48 4) 192) 1)
      phb_m4_r192_3 pvi_m4_r192_3 = pvo_m4_r192_3 :=
  bSeg_mk pdim_m4_r192_l48 pwalk_m4_r192_3 rfl rfl rfl
private theorem pwalk_m4_r192_4 :
    pWOk 3 193 pb_m4_r192_4 (bDec bZ pv_m4_r192_4_0) pv_m4_r192_4_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_16)))
private theorem pseg_m4_r192_4 : muxFastIterFullT16 3
      (Nat.add (highdNatMin (Nat.mul 48 4) 192) 1)
      phb_m4_r192_4 pvi_m4_r192_4 = pvo_m4_r192_4 :=
  bSeg_mk pdim_m4_r192_l48 pwalk_m4_r192_4 rfl rfl rfl
private theorem pwalk_m4_r192_5 :
    pWOk 1 193 pb_m4_r192_5 (bDec bZ pv_m4_r192_5_0) pv_m4_r192_5_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_7)))
private theorem pseg_m4_r192_5 : muxFastIterFullT16 1
      (Nat.add (highdNatMin (Nat.mul 48 4) 192) 1)
      phb_m4_r192_5 pvi_m4_r192_5 = pvo_m4_r192_5 :=
  bSeg_mk pdim_m4_r192_l48 pwalk_m4_r192_5 rfl rfl rfl
private theorem pwalk_m4_r192_6 :
    pWOk 1 193 pb_m4_r192_6 (bDec bZ pv_m4_r192_6_0) pv_m4_r192_6_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_6)))
private theorem pseg_m4_r192_6 : muxFastIterFullT16 1
      (Nat.add (highdNatMin (Nat.mul 48 4) 192) 1)
      phb_m4_r192_6 pvi_m4_r192_6 = pvo_m4_r192_6 :=
  bSeg_mk pdim_m4_r192_l48 pwalk_m4_r192_6 rfl rfl rfl
private theorem pwalk_m4_r192_7 :
    pWOk 5 193 pb_m4_r192_7 (bDec bZ pv_m4_r192_7_0) pv_m4_r192_7_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_2)))
private theorem pseg_m4_r192_7 : muxFastIterFullT16 5
      (Nat.add (highdNatMin (Nat.mul 48 4) 192) 1)
      phb_m4_r192_7 pvi_m4_r192_7 = pvo_m4_r192_7 :=
  bSeg_mk pdim_m4_r192_l48 pwalk_m4_r192_7 rfl rfl rfl
private theorem pwalks_snd_m4_r192 :
    RkmSegWalksSound 4 192 [1, 1, 24, 48, 48, 48, 48, 48]
      [2, 2, 20, 1, 3, 1, 1, 5] pwalks_m4_r192 := by
  dsimp only [RkmSegWalksSound, pwalks_m4_r192]
  exact ⟨pseg_m4_r192_0,
    ⟨pseg_m4_r192_1,
    ⟨pseg_m4_r192_2,
    ⟨pseg_m4_r192_3,
    ⟨pseg_m4_r192_4,
    ⟨pseg_m4_r192_5,
    ⟨pseg_m4_r192_6,
    ⟨pseg_m4_r192_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 4, r = 192)`. -/
theorem rkmTrajPack_m4_r192 :
    rkmEvalT16Lo12 4 2048 192 [1, 1, 24, 48, 48, 48, 48, 48]
      [19000726, 15616835, 12458892, 16013, 775290, 93782, 8422, 1687758]
      [2, 2, 20, 1, 3, 1, 1, 5]
      rkmMasksPack_m4_r192 = rkmRowPack_m4_r192 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m4_r192 ptail_1

private theorem pwalk_m4_r256_0 :
    pWOk 2 9 pb_m4_r256_0 (bDec bZ pv_m4_r256_0_0) pv_m4_r256_0_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_15)))
private theorem pseg_m4_r256_0 : muxFastIterFullT16 2
      (Nat.add (highdNatMin (Nat.mul 2 4) 256) 1)
      phb_m4_r256_0 pvi_m4_r256_0 = pvo_m4_r256_0 :=
  bSeg_mk pdim_m4_r256_l2 pwalk_m4_r256_0 rfl rfl rfl
private theorem pwalk_m4_r256_1 :
    pWOk 4 17 pb_m4_r256_1 (bDec bZ pv_m4_r256_1_0) pv_m4_r256_1_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_10)))
private theorem pseg_m4_r256_1 : muxFastIterFullT16 4
      (Nat.add (highdNatMin (Nat.mul 4 4) 256) 1)
      phb_m4_r256_1 pvi_m4_r256_1 = pvo_m4_r256_1 :=
  bSeg_mk pdim_m4_r256_l4 pwalk_m4_r256_1 rfl rfl rfl
private theorem pwalk_m4_r256_2 :
    pWOk 7 33 pb_m4_r256_2 (bDec bZ pv_m4_r256_2_0) pv_m4_r256_2_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_11)))
private theorem pseg_m4_r256_2 : muxFastIterFullT16 7
      (Nat.add (highdNatMin (Nat.mul 8 4) 256) 1)
      phb_m4_r256_2 pvi_m4_r256_2 = pvo_m4_r256_2 :=
  bSeg_mk pdim_m4_r256_l8 pwalk_m4_r256_2 rfl rfl rfl
private theorem pwalk_m4_r256_3 :
    pWOk 15 65 pb_m4_r256_3 (bDec bZ pv_m4_r256_3_0) pv_m4_r256_3_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_1)))
private theorem pseg_m4_r256_3 : muxFastIterFullT16 15
      (Nat.add (highdNatMin (Nat.mul 16 4) 256) 1)
      phb_m4_r256_3 pvi_m4_r256_3 = pvo_m4_r256_3 :=
  bSeg_mk pdim_m4_r256_l16 pwalk_m4_r256_3 rfl rfl rfl
private theorem pwalk_m4_r256_4 :
    pWOk 30 129 pb_m4_r256_4 (bDec bZ pv_m4_r256_4_0) pv_m4_r256_4_1 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_19))
private theorem pseg_m4_r256_4 : muxFastIterFullT16 30
      (Nat.add (highdNatMin (Nat.mul 32 4) 256) 1)
      phb_m4_r256_4 pvi_m4_r256_4 = pvo_m4_r256_4 :=
  bSeg_mk pdim_m4_r256_l32 pwalk_m4_r256_4 rfl rfl rfl
private theorem pw_m4_r256_5_0 :
    pWOk 16 257 pb_m4_r256_5 (bDec bZ pv_m4_r256_5_0) pv_m4_r256_5_1 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_12))
private theorem pw_m4_r256_5_1 :
    pWOk 32 257 pb_m4_r256_5 (bDec bZ pv_m4_r256_5_0) pv_m4_r256_5_2 :=
  pChnN 32 pw_m4_r256_5_0
    (rkmHd
    bk_3)
    (rfl : 16 + 16 = 32)
private theorem pw_m4_r256_5_2 :
    pWOk 48 257 pb_m4_r256_5 (bDec bZ pv_m4_r256_5_0) pv_m4_r256_5_3 :=
  pChnN 48 pw_m4_r256_5_1
    (rkmHd
    bk_4)
    (rfl : 32 + 16 = 48)
private theorem pwalk_m4_r256_5 :
    pWOk 64 257 pb_m4_r256_5 (bDec bZ pv_m4_r256_5_0) pv_m4_r256_5_4 :=
  pChnN 64 pw_m4_r256_5_2
    (rkmHd
    bk_5)
    (rfl : 48 + 16 = 64)
private theorem pseg_m4_r256_5 : muxFastIterFullT16 64
      (Nat.add (highdNatMin (Nat.mul 64 4) 256) 1)
      phb_m4_r256_5 pvi_m4_r256_5 = pvo_m4_r256_5 :=
  bSeg_mk pdim_m4_r256_l64 pwalk_m4_r256_5 rfl rfl rfl
private theorem pw_m4_r256_6_0 :
    pWOk 15 257 pb_m4_r256_6 (bDec bZ pv_m4_r256_6_0) pv_m4_r256_6_1 :=
  bSlSndNN (rkmHd
    bk_18)
private theorem pw_m4_r256_6_1 :
    pWOk 30 257 pb_m4_r256_6 (bDec bZ pv_m4_r256_6_0) pv_m4_r256_6_2 :=
  pChnN 30 pw_m4_r256_6_0
    (rkmHd
    bk_19)
    (rfl : 15 + 15 = 30)
private theorem pw_m4_r256_6_2 :
    pWOk 45 257 pb_m4_r256_6 (bDec bZ pv_m4_r256_6_0) pv_m4_r256_6_3 :=
  pChnN 45 pw_m4_r256_6_1
    (rkmHd
    (rkmTl
    bk_14))
    (rfl : 30 + 15 = 45)
private theorem pw_m4_r256_6_3 :
    pWOk 59 257 pb_m4_r256_6 (bDec bZ pv_m4_r256_6_0) pv_m4_r256_6_4 :=
  pChnN 59 pw_m4_r256_6_2
    (rkmHd
    (rkmTl
    bk_9))
    (rfl : 45 + 14 = 59)
private theorem pwalk_m4_r256_6 :
    pWOk 73 257 pb_m4_r256_6 (bDec bZ pv_m4_r256_6_0) pv_m4_r256_6_5 :=
  pChnN 73 pw_m4_r256_6_3
    (rkmHd
    (rkmTl
    bk_10))
    (rfl : 59 + 14 = 73)
private theorem pseg_m4_r256_6 : muxFastIterFullT16 73
      (Nat.add (highdNatMin (Nat.mul 112 4) 256) 1)
      phb_m4_r256_6 pvi_m4_r256_6 = pvo_m4_r256_6 :=
  bSeg_mk pdim_m4_r256_l112 pwalk_m4_r256_6 rfl rfl rfl
private theorem pwalk_m4_r256_7 :
    pWOk 15 257 pb_m4_r256_7 (bDec bZ pv_m4_r256_7_0) pv_m4_r256_7_1 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_15))
private theorem pseg_m4_r256_7 : muxFastIterFullT16 15
      (Nat.add (highdNatMin (Nat.mul 112 4) 256) 1)
      phb_m4_r256_7 pvi_m4_r256_7 = pvo_m4_r256_7 :=
  bSeg_mk pdim_m4_r256_l112 pwalk_m4_r256_7 rfl rfl rfl
private theorem pwalks_snd_m4_r256 :
    RkmSegWalksSound 4 256 [2, 4, 8, 16, 32, 64, 112, 112]
      [2, 4, 7, 15, 30, 64, 73, 15] pwalks_m4_r256 := by
  dsimp only [RkmSegWalksSound, pwalks_m4_r256]
  exact ⟨pseg_m4_r256_0,
    ⟨pseg_m4_r256_1,
    ⟨pseg_m4_r256_2,
    ⟨pseg_m4_r256_3,
    ⟨pseg_m4_r256_4,
    ⟨pseg_m4_r256_5,
    ⟨pseg_m4_r256_6,
    ⟨pseg_m4_r256_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 4, r = 256)`. -/
theorem rkmTrajPack_m4_r256 :
    rkmEvalT16Lo12 4 2048 256 [2, 4, 8, 16, 32, 64, 112, 112]
      [9205949, 8711812, 9910783, 10957087, 12137330, 15049393, 11636386, 2265506]
      [2, 4, 7, 15, 30, 64, 73, 15]
      rkmMasksPack_m4_r256 = rkmRowPack_m4_r256 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m4_r256 ptail_2

private theorem pwalk_m4_r384_0 :
    pWOk 1 5 pb_m4_r384_0 (bDec bZ pv_m4_r384_0_0) pv_m4_r384_0_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl (rkmTl (rkmTl
    bk_14)))))
private theorem pseg_m4_r384_0 : muxFastIterFullT16 1
      (Nat.add (highdNatMin (Nat.mul 1 4) 384) 1)
      phb_m4_r384_0 pvi_m4_r384_0 = pvo_m4_r384_0 :=
  bSeg_mk pdim_m4_r384_l1 pwalk_m4_r384_0 rfl rfl rfl
private theorem pwalk_m4_r384_1 :
    pWOk 3 5 pb_m4_r384_1 (bDec bZ pv_m4_r384_1_0) pv_m4_r384_1_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl (rkmTl
    bk_15))))
private theorem pseg_m4_r384_1 : muxFastIterFullT16 3
      (Nat.add (highdNatMin (Nat.mul 1 4) 384) 1)
      phb_m4_r384_1 pvi_m4_r384_1 = pvo_m4_r384_1 :=
  bSeg_mk pdim_m4_r384_l1 pwalk_m4_r384_1 rfl rfl rfl
private theorem pw_m4_r384_2_0 :
    pWOk 21 193 pb_m4_r384_2 (bDec bZ pv_m4_r384_2_0) pv_m4_r384_2_1 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_2))
private theorem pwalk_m4_r384_2 :
    pWOk 41 193 pb_m4_r384_2 (bDec bZ pv_m4_r384_2_0) pv_m4_r384_2_2 :=
  pChnN 41 pw_m4_r384_2_0
    (rkmHd
    bk_13)
    (rfl : 21 + 20 = 41)
private theorem pseg_m4_r384_2 : muxFastIterFullT16 41
      (Nat.add (highdNatMin (Nat.mul 48 4) 384) 1)
      phb_m4_r384_2 pvi_m4_r384_2 = pvo_m4_r384_2 :=
  bSeg_mk pdim_m4_r384_l48 pwalk_m4_r384_2 rfl rfl rfl
private theorem pwalk_m4_r384_3 :
    pWOk 2 385 pb_m4_r384_3 (bDec bZ pv_m4_r384_3_0) pv_m4_r384_3_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_19)))
private theorem pseg_m4_r384_3 : muxFastIterFullT16 2
      (Nat.add (highdNatMin (Nat.mul 96 4) 384) 1)
      phb_m4_r384_3 pvi_m4_r384_3 = pvo_m4_r384_3 :=
  bSeg_mk pdim_m4_r384_l96 pwalk_m4_r384_3 rfl rfl rfl
private theorem pwalk_m4_r384_4 :
    pWOk 1 385 pb_m4_r384_4 (bDec bZ pv_m4_r384_4_0) pv_m4_r384_4_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_12)))
private theorem pseg_m4_r384_4 : muxFastIterFullT16 1
      (Nat.add (highdNatMin (Nat.mul 96 4) 384) 1)
      phb_m4_r384_4 pvi_m4_r384_4 = pvo_m4_r384_4 :=
  bSeg_mk pdim_m4_r384_l96 pwalk_m4_r384_4 rfl rfl rfl
private theorem pwalk_m4_r384_5 :
    pWOk 1 385 pb_m4_r384_5 (bDec bZ pv_m4_r384_5_0) pv_m4_r384_5_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_18)))
private theorem pseg_m4_r384_5 : muxFastIterFullT16 1
      (Nat.add (highdNatMin (Nat.mul 96 4) 384) 1)
      phb_m4_r384_5 pvi_m4_r384_5 = pvo_m4_r384_5 :=
  bSeg_mk pdim_m4_r384_l96 pwalk_m4_r384_5 rfl rfl rfl
private theorem pwalk_m4_r384_6 :
    pWOk 1 385 pb_m4_r384_6 (bDec bZ pv_m4_r384_6_0) pv_m4_r384_6_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_17)))
private theorem pseg_m4_r384_6 : muxFastIterFullT16 1
      (Nat.add (highdNatMin (Nat.mul 96 4) 384) 1)
      phb_m4_r384_6 pvi_m4_r384_6 = pvo_m4_r384_6 :=
  bSeg_mk pdim_m4_r384_l96 pwalk_m4_r384_6 rfl rfl rfl
private theorem pwalk_m4_r384_7 :
    pWOk 3 385 pb_m4_r384_7 (bDec bZ pv_m4_r384_7_0) pv_m4_r384_7_1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_13)))
private theorem pseg_m4_r384_7 : muxFastIterFullT16 3
      (Nat.add (highdNatMin (Nat.mul 96 4) 384) 1)
      phb_m4_r384_7 pvi_m4_r384_7 = pvo_m4_r384_7 :=
  bSeg_mk pdim_m4_r384_l96 pwalk_m4_r384_7 rfl rfl rfl
private theorem pwalks_snd_m4_r384 :
    RkmSegWalksSound 4 384 [1, 1, 48, 96, 96, 96, 96, 96]
      [1, 3, 41, 2, 1, 1, 1, 3] pwalks_m4_r384 := by
  dsimp only [RkmSegWalksSound, pwalks_m4_r384]
  exact ⟨pseg_m4_r384_0,
    ⟨pseg_m4_r384_1,
    ⟨pseg_m4_r384_2,
    ⟨pseg_m4_r384_3,
    ⟨pseg_m4_r384_4,
    ⟨pseg_m4_r384_5,
    ⟨pseg_m4_r384_6,
    ⟨pseg_m4_r384_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 4, r = 384)`. -/
theorem rkmTrajPack_m4_r384 :
    rkmEvalT16Lo12 4 2048 384 [1, 1, 48, 96, 96, 96, 96, 96]
      [3475462, 20937098, 9131561, 219157, 110278, 1728, 106306, 316330]
      [1, 3, 41, 2, 1, 1, 1, 3]
      rkmMasksPack_m4_r384 = rkmRowPack_m4_r384 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m4_r384 ptail_3

private theorem pwalk_m2_r512_0 :
    pWOk 6 17 rkmHbNatPack_m2_r512_s0 (bDec bZ rkmViNatPack_m2_r512_s0) rkmVoNatPack_m2_r512_s0 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_9)))
/-- Certified `(m = 2, r = 512)` segment `0` trajectory walk. -/
theorem rkmSegPack_m2_r512_s0 : muxFastIterFullT16 6
      (Nat.add (highdNatMin (Nat.mul 8 2) 512) 1)
      rkmHbPack_m2_r512_s0 rkmViPack_m2_r512_s0 = rkmVoPack_m2_r512_s0 :=
  bSeg_mk pdim_m2_r512_l8 pwalk_m2_r512_0
    (rkmHbOfNats_eq rkmHbNatPack_m2_r512_s0) (rkmDecOfNats_eq rkmViNatPack_m2_r512_s0)
    (rkmDecOfNats_eq rkmVoNatPack_m2_r512_s0)

private theorem pwalk_m2_r512_1 :
    pWOk 16 49 rkmHbNatPack_m2_r512_s1 (bDec bZ rkmViNatPack_m2_r512_s1) rkmVoNatPack_m2_r512_s1 :=
  bSlSndNN (rkmHd
    (rkmTl (rkmTl
    bk_0)))
/-- Certified `(m = 2, r = 512)` segment `1` trajectory walk. -/
theorem rkmSegPack_m2_r512_s1 : muxFastIterFullT16 16
      (Nat.add (highdNatMin (Nat.mul 24 2) 512) 1)
      rkmHbPack_m2_r512_s1 rkmViPack_m2_r512_s1 = rkmVoPack_m2_r512_s1 :=
  bSeg_mk pdim_m2_r512_l24 pwalk_m2_r512_1
    (rkmHbOfNats_eq rkmHbNatPack_m2_r512_s1) (rkmDecOfNats_eq rkmViNatPack_m2_r512_s1)
    (rkmDecOfNats_eq rkmVoNatPack_m2_r512_s1)

private theorem pwalk_m2_r512_2 :
    pWOk 30 129 rkmHbNatPack_m2_r512_s2 (bDec bZ rkmViNatPack_m2_r512_s2) rkmVoNatPack_m2_r512_s2 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_13))
/-- Certified `(m = 2, r = 512)` segment `2` trajectory walk. -/
theorem rkmSegPack_m2_r512_s2 : muxFastIterFullT16 30
      (Nat.add (highdNatMin (Nat.mul 64 2) 512) 1)
      rkmHbPack_m2_r512_s2 rkmViPack_m2_r512_s2 = rkmVoPack_m2_r512_s2 :=
  bSeg_mk pdim_m2_r512_l64 pwalk_m2_r512_2
    (rkmHbOfNats_eq rkmHbNatPack_m2_r512_s2) (rkmDecOfNats_eq rkmViNatPack_m2_r512_s2)
    (rkmDecOfNats_eq rkmVoNatPack_m2_r512_s2)

private theorem pw_m2_r512_3_0 :
    pWOk 14 289 rkmHbNatPack_m2_r512_s3 (bDec bZ rkmViNatPack_m2_r512_s3) pv_m2_r512_3_1 :=
  bSlSndNN (rkmHd
    (rkmTl
    bk_1))
private theorem pw_m2_r512_3_1 :
    pWOk 28 289 rkmHbNatPack_m2_r512_s3 (bDec bZ rkmViNatPack_m2_r512_s3) pv_m2_r512_3_2 :=
  pChnN 28 pw_m2_r512_3_0
    (rkmHd
    bk_12)
    (rfl : 14 + 14 = 28)
private theorem pw_m2_r512_3_2 :
    pWOk 41 289 rkmHbNatPack_m2_r512_s3 (bDec bZ rkmViNatPack_m2_r512_s3) pv_m2_r512_3_3 :=
  pChnN 41 pw_m2_r512_3_1
    (rkmHd
    (rkmTl
    bk_16))
    (rfl : 28 + 13 = 41)
private theorem pw_m2_r512_3_3 :
    pWOk 54 289 rkmHbNatPack_m2_r512_s3 (bDec bZ rkmViNatPack_m2_r512_s3) pv_m2_r512_3_4 :=
  pChnN 54 pw_m2_r512_3_2
    (rkmHd
    (rkmTl
    bk_17))
    (rfl : 41 + 13 = 54)
private theorem pwalk_m2_r512_3 :
    pWOk 67 289 rkmHbNatPack_m2_r512_s3 (bDec bZ rkmViNatPack_m2_r512_s3) rkmVoNatPack_m2_r512_s3 :=
  pChnN 67 pw_m2_r512_3_3
    (rkmHd
    (rkmTl
    bk_18))
    (rfl : 54 + 13 = 67)
/-- Certified `(m = 2, r = 512)` segment `3` trajectory walk. -/
theorem rkmSegPack_m2_r512_s3 : muxFastIterFullT16 67
      (Nat.add (highdNatMin (Nat.mul 144 2) 512) 1)
      rkmHbPack_m2_r512_s3 rkmViPack_m2_r512_s3 = rkmVoPack_m2_r512_s3 :=
  bSeg_mk pdim_m2_r512_l144 pwalk_m2_r512_3
    (rkmHbOfNats_eq rkmHbNatPack_m2_r512_s3) (rkmDecOfNats_eq rkmViNatPack_m2_r512_s3)
    (rkmDecOfNats_eq rkmVoNatPack_m2_r512_s3)

private theorem pw_m2_r512_7_0 :
    pWOk 8 513 rkmHbNatPack_m2_r512_s7 (bDec bZ rkmViNatPack_m2_r512_s7) pv_m2_r512_7_1 :=
  bSlSndNN (rkmHd
    bk_6)
private theorem pw_m2_r512_7_1 :
    pWOk 16 513 rkmHbNatPack_m2_r512_s7 (bDec bZ rkmViNatPack_m2_r512_s7) pv_m2_r512_7_2 :=
  pChnN 16 pw_m2_r512_7_0
    (rkmHd
    bk_7)
    (rfl : 8 + 8 = 16)
private theorem pw_m2_r512_7_2 :
    pWOk 24 513 rkmHbNatPack_m2_r512_s7 (bDec bZ rkmViNatPack_m2_r512_s7) pv_m2_r512_7_3 :=
  pChnN 24 pw_m2_r512_7_1
    (rkmHd
    bk_8)
    (rfl : 16 + 8 = 24)
private theorem pw_m2_r512_7_3 :
    pWOk 32 513 rkmHbNatPack_m2_r512_s7 (bDec bZ rkmViNatPack_m2_r512_s7) pv_m2_r512_7_4 :=
  pChnN 32 pw_m2_r512_7_2
    (rkmHd
    bk_9)
    (rfl : 24 + 8 = 32)
private theorem pw_m2_r512_7_4 :
    pWOk 40 513 rkmHbNatPack_m2_r512_s7 (bDec bZ rkmViNatPack_m2_r512_s7) pv_m2_r512_7_5 :=
  pChnN 40 pw_m2_r512_7_3
    (rkmHd
    bk_10)
    (rfl : 32 + 8 = 40)
private theorem pw_m2_r512_7_5 :
    pWOk 48 513 rkmHbNatPack_m2_r512_s7 (bDec bZ rkmViNatPack_m2_r512_s7) pv_m2_r512_7_6 :=
  pChnN 48 pw_m2_r512_7_4
    (rkmHd
    bk_11)
    (rfl : 40 + 8 = 48)
private theorem pwalk_m2_r512_7 :
    pWOk 55 513 rkmHbNatPack_m2_r512_s7 (bDec bZ rkmViNatPack_m2_r512_s7) rkmVoNatPack_m2_r512_s7 :=
  pChnN 55 pw_m2_r512_7_5
    (rkmHd
    (rkmTl
    bk_11))
    (rfl : 48 + 7 = 55)
/-- Certified `(m = 2, r = 512)` segment `7` trajectory walk. -/
theorem rkmSegPack_m2_r512_s7 : muxFastIterFullT16 55
      (Nat.add (highdNatMin (Nat.mul 448 2) 512) 1)
      rkmHbPack_m2_r512_s7 rkmViPack_m2_r512_s7 = rkmVoPack_m2_r512_s7 :=
  bSeg_mk pdim_m2_r512_l448 pwalk_m2_r512_7
    (rkmHbOfNats_eq rkmHbNatPack_m2_r512_s7) (rkmDecOfNats_eq rkmViNatPack_m2_r512_s7)
    (rkmDecOfNats_eq rkmVoNatPack_m2_r512_s7)

/-- Module export witness for `FindAllJohnsonRampKickMuxLowHiT0`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxLowHiT0 : True := trivial

end

end QuantumComputation.Specs.DickeSol
