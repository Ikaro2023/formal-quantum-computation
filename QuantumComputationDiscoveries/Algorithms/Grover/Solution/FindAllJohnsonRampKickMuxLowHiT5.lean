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
# Low-`m` High-`r` Krotov Trajectory Part `5` (`FindAllJohnsonRampKickMuxLowHiT5`)

Certifies multi-segment sawtooth `rkmEvalT16Lo12` trajectories for
`(m, r) ∈ {(8, 256), (16, 256), (32, 256)}`.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Sign-kick mask segment `3` for `(m = 8, r = 256)`. -/
def rkmMkPack_m8_r256_s3 : List Bool :=
  [true, false, true, false, true, true, false, true, true, false, false, true, true, true,
    true, true, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, true, true, true, true,
    false, false, false, false, false, false, false, true]
/-- Sign-kick mask segment `4` for `(m = 8, r = 256)`. -/
def rkmMkPack_m8_r256_s4 : List Bool :=
  [false, false, true, false, true, true, false, true, false, false, true, false, true, false,
    true, true, true, true, false, false, false, true, true, false, true, false, true, true,
    true, true, true, false, false, true, false, true, true, false, false, true, true, true,
    false, false, false, false, true, false, true, true, true, true, true, true, true, true,
    true, true, false, true, true, true, true, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, true, false, false, false, false, false,
    false, false, true, true, true, false, false, false, false, true, true, true, false, false,
    true, false, false, true]
/-- Sign-kick mask segment `5` for `(m = 8, r = 256)`. -/
def rkmMkPack_m8_r256_s5 : List Bool :=
  [true, false, false, true, false, true, false, false, true, false, true, false, true, false,
    false, true, false, false, false, false, true, false, false, false, false, true, false,
    true, false, false, true, true, false, true, true, true, false, false, false, false, true,
    true, false, true, true, false, false, true, true, false, true, true, true, true, false,
    false, true, false, true, true, false, false, false, false, true, false, true, false,
    false, true, true, false, false, false, false, true, false, false, false, false, false,
    true, true, false, false, true, false, false, false, false, false, true, true, false,
    false, true, false, false, false, false, false, true, false, true, false, false, false,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, false, true, true, true, true, false, false, false, false, true, true, true, true,
    false, false, false, false, false, true, true, true, true, false, false, false, false,
    false, true, true, true, true, true, true, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, true, true, true, true, true, false, false, false,
    false, true, true, true, false, false, false, false, true, false, true, true, true, false,
    true]
/-- Sign-kick mask segment `6` for `(m = 8, r = 256)`. -/
def rkmMkPack_m8_r256_s6 : List Bool :=
  [false, true, true, true, false, false, false, false, true, false, true, false, true, true,
    false, false, true, false, false, false, false, false, false, true, true, true, false,
    false, false, false, true, true, false, true, false, true, false, false, false, false,
    true, false, false, false, false, false, false, false, false, true, false, false, false,
    false, false, false, true, false, false, false, false, false, false, false, false, true,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, true, false, false, false, false, true, false, false, false, false, true, false,
    false, false, false, true, false, false, false, false, true, false, false, false, false,
    true, false, false, false, false, true, false, false, false, true, true, false, false,
    false, false, true, false, false, false, false, true, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, true, false, false, false, false, false, false,
    false, false, false, true, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, true, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, true, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, true, true, true, true, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, true, false, false,
    false, true, false, false, false, true]
/-- Multi-segment sign-kick masks for `(m = 8, r = 256)`. -/
def rkmMasksPack_m8_r256 : List (List Bool) :=
  [[], [], [], rkmMkPack_m8_r256_s3, rkmMkPack_m8_r256_s4, rkmMkPack_m8_r256_s5,
    rkmMkPack_m8_r256_s6, []]
/-- Hit-row chunk `0` for `(m = 8, r = 256)`. -/
def rkmRowPack_m8_r256_p0 : List ℕ :=
  [20932, 41660, 23347, 20517, 28966, 144321, 848, 20796, 42444, 1298, 113641, 100802, 1519,
    17838, 16237, 154337, 50793, 39341, 41644, 79704, 331826, 4776, 144833, 153988, 138430,
    489991, 36190, 385876, 105354, 3912, 61015, 202276]
/-- Hit-row chunk `1` for `(m = 8, r = 256)`. -/
def rkmRowPack_m8_r256_p1 : List ℕ :=
  [31378, 23473, 137594, 36362, 129698, 136669, 796468, 636765, 34703, 456722, 1408622, 81015,
    45732, 1624224, 3238193, 576165, 324720, 1708496, 3779163, 1741872, 1581, 1904867, 3293350,
    2950600, 1021674, 644807, 1199329, 672687, 131787, 1591724, 115229, 1520132]
/-- Hit-row chunk `2` for `(m = 8, r = 256)`. -/
def rkmRowPack_m8_r256_p2 : List ℕ :=
  [3071744, 3326222, 1531195, 4697, 325903, 2314691, 245725, 31465, 84934, 38, 596503, 4855154,
    2752787, 846951, 444160, 887988, 131401, 118477, 112, 289809, 1635302, 11278732, 49221,
    924100, 124720, 2972612, 46542, 2093760, 2502143, 399427, 621238, 180737]
/-- Hit-row chunk `3` for `(m = 8, r = 256)`. -/
def rkmRowPack_m8_r256_p3 : List ℕ :=
  [721249, 11912181, 614894, 5911482, 51860, 396846, 1992037, 34077, 9529, 773579, 625401,
    4959496, 3324806, 1387050, 12518, 2079904, 2787342, 1536174, 5154145, 1220920, 16973300,
    686, 8808, 8846081, 189395, 6074455, 2757014, 301636, 3244832, 32762, 2291747, 7959674]
/-- Hit-row chunk `4` for `(m = 8, r = 256)`. -/
def rkmRowPack_m8_r256_p4 : List ℕ :=
  [520849, 319026, 140807, 2498856, 2154224, 2755126, 3710448, 9856179, 20278249, 1948293,
    9737452, 16035036, 19265216, 1277314, 42482551, 36384380, 163957, 24333379, 4552094,
    5992144, 2613391, 2306410, 1577571, 11929819, 10498935, 2035399, 17715192, 23038, 14537358,
    3871132, 154386623, 128253491]
/-- Hit-row chunk `5` for `(m = 8, r = 256)`. -/
def rkmRowPack_m8_r256_p5 : List ℕ :=
  [3437045, 533810, 16515577, 10509469, 29715022, 105411581, 34879043, 84833124, 109496501,
    80905297, 139594725, 26029723, 14841980, 62681027, 2344043, 35456613, 44659984, 14596194,
    123161030, 88929151, 8315201, 9525473, 52500590, 36778859, 27003834, 6939356, 57695327,
    785, 150888259, 317458, 276987937, 25556968]
/-- Hit-row chunk `6` for `(m = 8, r = 256)`. -/
def rkmRowPack_m8_r256_p6 : List ℕ :=
  [296229782, 105001493, 203113102, 225086405, 17507454, 22864561, 206744502, 271871368,
    22124180, 169006831, 29605339, 298202998, 587399, 404786832, 96708627, 239924117,
    145173759, 116232617, 477516407, 19548845, 513825712, 39926245, 361977322, 475006385,
    87763517, 1221137173, 1261874, 1031721226, 111666370, 13771775, 1086712574, 2160433346]
/-- Hit-row chunk `7` for `(m = 8, r = 256)`. -/
def rkmRowPack_m8_r256_p7 : List ℕ :=
  [2285383859, 5451375358, 1168149961, 5384427145, 16007, 1081735799, 16100091, 77727446,
    1642295853, 218182040, 3906916345, 11595941708, 4650591283, 24425413, 9537438, 7965443907,
    60242509864, 152305311360, 221578753519, 217298748495, 154012743396, 83709876009,
    36185861079, 12355850505, 3224806144, 625649632, 89266726, 9354414, 714004, 38300, 1308,
    20]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 8, r = 256)`. -/
def rkmRowPack_m8_r256 : List ℕ :=
  rkmRowPack_m8_r256_p0 ++ rkmRowPack_m8_r256_p1 ++ rkmRowPack_m8_r256_p2 ++ rkmRowPack_m8_r256_p3
    ++ rkmRowPack_m8_r256_p4 ++ rkmRowPack_m8_r256_p5 ++ rkmRowPack_m8_r256_p6
    ++ rkmRowPack_m8_r256_p7

/-- Sign-kick mask segment `1` for `(m = 16, r = 256)`. -/
def rkmMkPack_m16_r256_s1 : List Bool :=
  [true, true, false, true, true, true, true, true, true, true, true, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    true, true, true, false, false, false, false, false, true]
/-- Sign-kick mask segment `2` for `(m = 16, r = 256)`. -/
def rkmMkPack_m16_r256_s2 : List Bool :=
  [false, true, true, true, false, false, true, true, true, true, true, false, false, false,
    false, true, true, true, true, true, false, false, true, true, true, true, false, true,
    false, false, true, true, true, true, false, true, true, true, true, true, false, false,
    false, false, false, false, true, true, true, true, true, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    true, true, true, false, false, false, false, false, false, false, false, false, false,
    false, true, false, true]
/-- Sign-kick mask segment `3` for `(m = 16, r = 256)`. -/
def rkmMkPack_m16_r256_s3 : List Bool :=
  [true, false, true, true, false, false, false, true, false, false, false, false, false,
    false, true, false, true, false, false, true, true, false, false, true, true, false, false,
    true, false, false, true, false, false, false, true, true, true, false, false, false, true,
    false, false, true, false, true, false, true, true, true, false, false, false, false, true,
    true, false, false, false, false, false, true, false, true, false, true, false, false,
    false, false, true, false, true, false, true, false, true, true, true, false, true, true,
    false, false, true, false, true, true, true, true, true, false, true, false, true, true,
    false, false, false, false, false, false, false, false, true, true, false, false, false,
    false, true, true, true, true, true, true, true, true, false, false, true, true, false,
    false, true, true, true, true, true, false, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, true,
    true, false, false, false, false, true, true, true, false, true]
/-- Sign-kick mask segment `4` for `(m = 16, r = 256)`. -/
def rkmMkPack_m16_r256_s4 : List Bool :=
  [false, true, true, true, true, false, true, false, true, false, false, true, true, true,
    false, false, false, false, true, false, false, false, false, false, true, true, false,
    false, true, true, true, false, true, true, true, false, true, false, true, false, false,
    false, true, true, false, false, false, false, true, false, true, false, false, true,
    false, false, true, false, true, false, true, true, false, false, false, true, false,
    false, false, false, true, true, false, false, true, true, false, false, true, true, true,
    false, false, false, false, false, false, false, true, true, false, false, true, false,
    true, true, false, false, false, false, false, false, false, false, false, true, true,
    false, false, false, true, false, false, false, false, false, false, false, false, false,
    true, true, false, true, false, true, false, false, false, false, true, true, false, false,
    true, false, false, false, true, true, true, false, true, true, false, false, true, true,
    false, false, false, true, true, false, false, false, true, false, false, false, true,
    true, false, false, true, true, true, false, false, true, true, true, false, false, false,
    false, true, false, true, false, false, false, false, false, true, true, false, true, true,
    true, true, false, false, false, false, true, true, true, true, true, true, true, true,
    true, true, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, true, true, true, true, true, true, true]
/-- Sign-kick mask segment `5` for `(m = 16, r = 256)`. -/
def rkmMkPack_m16_r256_s5 : List Bool :=
  [false, false, false, false, false, false, false, false, false, false, true, false, false,
    false, false, true, false, false, false, false, true, false, false, false, false, true,
    false, false, false, false, true, false, true, false, false, true, false, false, true,
    false, false, false, true, false, false, false, false, false, false, false, false, false,
    true, true, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, true, false, true, false, false, false, false, false, false, false,
    false, false, true, false, false, false, false, false, false, false, false, true, true,
    false, true, false, false, false, false, false, false, false, true, true, false, false,
    true, true, true, false, false, false, true, true, false, false, false, true, false, false,
    false, false, true, false, false, false, false, true, false, false, false, false, true,
    false, true, false, false, true, false, true, false, false, true, false, false, false,
    false, true, false, false, false, false, true, false, false, false, false, false, false,
    false, false, true, false, false, false, false, false, true, false, false, false, false,
    true, false, false, false, false, true, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, true, false, false, false, false, true,
    false, false, false, false, true, false, false, false, false, true, false, false, false,
    false, true, false, false, false, false, false, false, false, false, false, true, false,
    false, false, true, true, false, false, true, true, false, false, true, true, false, false,
    true, true, false, false, true, true, false, false, false, true, true, false, false, true,
    true, true]
/-- Sign-kick mask segment `6` for `(m = 16, r = 256)`. -/
def rkmMkPack_m16_r256_s6 : List Bool :=
  [true, true, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, true, false, false, false, true, true,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, true, false, false, false, false, true, false, false, false, false, true, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, true, true, false, false, false, false, false, false, false,
    false, false, true, false, false, false, false, false, false, false, false, false, true,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, true, false, false, false, false, true, false, false, false, false, true, false,
    false, false, false, true, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, true, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, true, false, false, false, false, true,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, true, false, false, false, false, false, false, false, false, false, true, false,
    false, false, false, true, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, true, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, true,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, true, false, false, false, false, false, false, false, true, false, true, false,
    false, true, false, false, true, false, false, true]
/-- Multi-segment sign-kick masks for `(m = 16, r = 256)`. -/
def rkmMasksPack_m16_r256 : List (List Bool) :=
  [[], rkmMkPack_m16_r256_s1, rkmMkPack_m16_r256_s2, rkmMkPack_m16_r256_s3,
    rkmMkPack_m16_r256_s4, rkmMkPack_m16_r256_s5, rkmMkPack_m16_r256_s6, []]
/-- Hit-row chunk `0` for `(m = 16, r = 256)`. -/
def rkmRowPack_m16_r256_p0 : List ℕ :=
  [3054, 2868, 35, 18670, 2248, 799, 14173, 55213, 206517, 82346, 332715, 131783, 23361, 58234,
    2477, 1810, 664, 5117, 178475, 90361, 26402, 163234, 1274, 55387, 102073, 515976, 57170,
    4661, 63410, 18577, 49651, 37943]
/-- Hit-row chunk `1` for `(m = 16, r = 256)`. -/
def rkmRowPack_m16_r256_p1 : List ℕ :=
  [3059, 198056, 280332, 55721, 52349, 44441, 321263, 190892, 770, 4159, 413260, 68016, 88501,
    231376, 112, 38273, 82538, 650679, 28707, 1497, 534217, 280387, 63422, 780912, 461726,
    126950, 122040, 193361, 26480, 369197, 240623, 119202]
/-- Hit-row chunk `2` for `(m = 16, r = 256)`. -/
def rkmRowPack_m16_r256_p2 : List ℕ :=
  [40884, 16246, 12, 1, 4427, 10161, 65127, 113784, 195143, 54355, 4, 70979, 61309, 33573, 253,
    50755, 25250, 3219, 25346, 6669, 168648, 19777, 80333, 436538, 161681, 102, 135572, 7353,
    210091, 432999, 108143, 580236]
/-- Hit-row chunk `3` for `(m = 16, r = 256)`. -/
def rkmRowPack_m16_r256_p3 : List ℕ :=
  [403961, 877178, 7959, 285317, 690737, 24151, 2781451, 1460596, 2117, 94153, 241631, 1226029,
    676140, 694982, 67373, 620251, 633073, 304641, 51300, 701161, 206161, 1918889, 670346,
    722030, 553252, 333150, 2145060, 253977, 1395579, 3820317, 6073498, 2082038]
/-- Hit-row chunk `4` for `(m = 16, r = 256)`. -/
def rkmRowPack_m16_r256_p4 : List ℕ :=
  [424078, 1444298, 85352, 48982, 68566, 204514, 8864629, 10158800, 568237, 1862, 7575803,
    6461340, 560166, 10752433, 29713094, 126583, 13846765, 8, 8996671, 10265902, 3507078,
    5724739, 547078, 1754073, 22824302, 4283400, 28021944, 38407, 3793432, 10072284, 11335965,
    17457016]
/-- Hit-row chunk `5` for `(m = 16, r = 256)`. -/
def rkmRowPack_m16_r256_p5 : List ℕ :=
  [131460, 2968760, 303, 7449315, 111658, 9939521, 819110, 19831662, 21596470, 94508, 1557985,
    4389127, 54516671, 716986, 10117667, 24984375, 5881362, 8184332, 5403798, 2156489, 276773,
    11813994, 13998365, 1270480, 1251809, 61806, 22089823, 36021482, 63518623, 24767131,
    7074938, 26865463]
/-- Hit-row chunk `6` for `(m = 16, r = 256)`. -/
def rkmRowPack_m16_r256_p6 : List ℕ :=
  [13026250, 44203063, 153520045, 588880, 15821722, 17489707, 1567892, 1975491, 25401737,
    93801698, 378309810, 107598505, 190707795, 57947664, 117692679, 190506932, 326866930,
    713637206, 31252462, 108017735, 71663180, 13311143, 249237101, 129975092, 8546, 53600836,
    57443378, 162554698, 29372387, 62887341, 1651195, 205882592]
/-- Hit-row chunk `7` for `(m = 16, r = 256)`. -/
def rkmRowPack_m16_r256_p7 : List ℕ :=
  [385282976, 35713816, 48945861, 36994154, 6429184, 287491305, 2774107888, 3229219, 16385948,
    71610172, 429624, 1888378231, 252777514, 166833438, 88664, 2400202722, 63354623,
    3452040282, 52639, 5453180071, 2384760936, 86271164, 6105474836, 502021773, 6397254942,
    9117182163, 36938748, 12998187113, 25248900209, 28052898, 42284795329, 873185830099]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 16, r = 256)`. -/
def rkmRowPack_m16_r256 : List ℕ :=
  rkmRowPack_m16_r256_p0 ++ rkmRowPack_m16_r256_p1 ++ rkmRowPack_m16_r256_p2
    ++ rkmRowPack_m16_r256_p3 ++ rkmRowPack_m16_r256_p4 ++ rkmRowPack_m16_r256_p5
    ++ rkmRowPack_m16_r256_p6 ++ rkmRowPack_m16_r256_p7

/-- Sign-kick mask segment `1` for `(m = 32, r = 256)`. -/
def rkmMkPack_m32_r256_s1 : List Bool :=
  [false, true, true, false, false, false, false, false, false, true, true, true, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, true, true]
/-- Sign-kick mask segment `2` for `(m = 32, r = 256)`. -/
def rkmMkPack_m32_r256_s2 : List Bool :=
  [false, true, true, true, false, false, false, true, false, true, true, false, true, true,
    false, false, false, true, true, true, true, false, false, false, true, true, true, false,
    false, true, false, true, true, false, true, true, false, false, false, false, false,
    false, true, false, false, false, false, false, true, false, true, true, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, true,
    true, true, true, true, true, false, false, false, false, false, false, false, false,
    false, false, false, false, true]
/-- Sign-kick mask segment `3` for `(m = 32, r = 256)`. -/
def rkmMkPack_m32_r256_s3 : List Bool :=
  [true, true, true, true, true, true, true, true, true, true, false, false, true, true, true,
    false, false, true, true, false, false, true, true, false, true, false, true, false, true,
    true, true, true, false, true, true, false, true, false, false, false, true, true, true,
    false, false, true, true, true, false, false, true, false, true, false, false, false, true,
    true, true, false, false, true, true, false, true, true, true, true, true, true, true,
    true, true, true, false, true, false, true, true, true, true, true, false, false, true,
    false, true, true, true, true, true, false, false, true, false, true, true, false, false,
    false, false, true, false, false, false, false, true, true, false, false, false, false,
    false, false, true, false, true, false, true, true, true, true, false, false, true, true,
    true, true, true, false, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, true, true, false,
    false, false, false, true, true, true]
/-- Sign-kick mask segment `4` for `(m = 32, r = 256)`. -/
def rkmMkPack_m32_r256_s4 : List Bool :=
  [true, false, true, true, false, false, false, true, false, false, false, true, false, true,
    false, true, false, true, false, true, false, false, false, false, true, true, false, true,
    true, false, true, true, false, true, false, true, true, true, false, true, false, false,
    false, true, false, false, false, false, true, false, true, true, false, true, false, true,
    false, false, true, false, true, false, true, false, false, true, false, false, false,
    false, false, true, false, false, true, false, false, false, true, true, true, false, true,
    false, false, true, false, false, true, true, true, false, true, false, true, false, false,
    false, false, false, true, false, true, false, false, true, true, false, true, false,
    false, true, false, false, false, true, false, false, false, true, false, false, false,
    false, false, true, true, false, true, false, false, true, false, false, true, false,
    false, false, true, true, false, false, true, true, false, true, true, true, false, false,
    false, true, true, false, false, true, true, false, false, false, false, true, false,
    false, true, false, true, false, false, true, true, true, false, false, false, true, true,
    false, false, false, true, false, false, false, false, false, false, true, true, true,
    true, false, false, false, false, true, true, true, true, true, true, true, true, true,
    true, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, true, true, true, true, true, true, true, true]
/-- Sign-kick mask segment `5` for `(m = 32, r = 256)`. -/
def rkmMkPack_m32_r256_s5 : List Bool :=
  [true, false, false, false, false, false, true, false, false, false, false, false, false,
    false, false, true, false, false, false, false, true, false, false, false, false, true,
    false, false, false, false, true, false, false, false, false, true, false, false, false,
    false, true, false, true, false, false, true, false, false, false, false, false, false,
    false, false, false, false, false, true, false, true, true, false, false, false, false,
    false, false, false, false, false, false, false, false, false, false, true, false, false,
    false, false, true, false, false, false, false, false, false, true, false, true, true,
    false, false, false, true, false, false, false, false, false, true, false, true, false,
    false, true, false, true, false, false, false, false, true, false, false, true, false,
    false, false, false, true, false, false, false, false, true, false, false, false, false,
    true, false, false, false, false, false, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, false, false, false, false, false, true, true, false, false, false, true, false,
    false, false, false, false, false, false, false, false, true, false, false, false, false,
    true, false, false, false, false, false, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, true,
    false, true, false, true, true, false, false, true, true, false, false, true, true, false,
    false, true, true, false, false, true, true, false, false, false, true, true, false, false,
    true, true, true]
/-- Sign-kick mask segment `6` for `(m = 32, r = 256)`. -/
def rkmMkPack_m32_r256_s6 : List Bool :=
  [false, true, false, false, false, false, false, false, false, false, false, false, false,
    false, true, false, false, true, false, false, true, false, true, false, false, true,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, true, false, false, false, false, true, false, true, false, false, false, false,
    false, false, false, true, false, false, true, false, true, false, false, false, true,
    false, false, false, false, false, false, false, false, false, false, false, false, false,
    true, false, true, false, false, true, true, false, false, false, false, false, true,
    false, false, false, false, true, false, false, false, false, true, false, false, false,
    false, true, false, false, false, false, true, false, false, false, false, true, false,
    false, false, false, true, false, false, false, false, false, false, false, false, false,
    false, false, true, false, false, true, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, true, false, false, false, false, true,
    false, false, false, false, false, false, false, false, false, true, false, false, false,
    false, true, false, false, false, false, false, false, false, false, false, true, false,
    false, false, false, true, false, false, false, false, true, false, false, false, false,
    false, false, false, false, false, true, false, false, false, false, true, false, false,
    false, false, false, false, false, false, false, false, false, false, false, false, true,
    false, false, false, false, true, false, false, false, false, true, false, false, false,
    false, true, false, false, false, false, false, false, false, true, false, false, false,
    false, true, false, false, true, false, false, true]
/-- Multi-segment sign-kick masks for `(m = 32, r = 256)`. -/
def rkmMasksPack_m32_r256 : List (List Bool) :=
  [[], rkmMkPack_m32_r256_s1, rkmMkPack_m32_r256_s2, rkmMkPack_m32_r256_s3,
    rkmMkPack_m32_r256_s4, rkmMkPack_m32_r256_s5, rkmMkPack_m32_r256_s6, []]
/-- Hit-row chunk `0` for `(m = 32, r = 256)`. -/
def rkmRowPack_m32_r256_p0 : List ℕ :=
  [54947, 339872, 261371, 92841, 36569, 43031, 703685, 165695, 3190, 848989, 27493, 283727,
    1093822, 105193, 5917, 91612, 735579, 6359, 12718, 20033, 31833, 19, 6043, 12745, 891450,
    9488, 3955, 171001, 21979, 664842, 55534, 0]
/-- Hit-row chunk `1` for `(m = 32, r = 256)`. -/
def rkmRowPack_m32_r256_p1 : List ℕ :=
  [1192808, 43584, 342607, 313164, 294898, 491719, 493297, 268968, 15710, 13319, 644813, 6754,
    1730440, 32205, 161330, 214378, 130943, 1736, 940954, 19261, 8041, 590340, 2360, 323841,
    24200, 4541, 966977, 421058, 30, 816235, 150551, 1453]
/-- Hit-row chunk `2` for `(m = 32, r = 256)`. -/
def rkmRowPack_m32_r256_p2 : List ℕ :=
  [52528, 454, 50759, 28414, 98199, 8287, 324391, 12045, 43042, 92867, 5835, 526100, 8853, 405,
    62566, 92020, 21556, 251185, 113, 96931, 49251, 207882, 44802, 373067, 1656, 37340, 599015,
    13599, 170937, 1380128, 272615, 58631]
/-- Hit-row chunk `3` for `(m = 32, r = 256)`. -/
def rkmRowPack_m32_r256_p3 : List ℕ :=
  [1443667, 149763, 585401, 657099, 100219, 2430797, 246648, 668, 3334782, 138, 378485, 386454,
    874272, 2681966, 2152061, 5017, 86775, 1871492, 3958276, 23216, 282004, 2321, 14010,
    15143756, 5061608, 1290306, 10223540, 863712, 2612128, 85580, 2812995, 5902587]
/-- Hit-row chunk `4` for `(m = 32, r = 256)`. -/
def rkmRowPack_m32_r256_p4 : List ℕ :=
  [503081, 1622011, 1442097, 3157183, 666501, 1840039, 9812562, 90719, 2820488, 1025070,
    2923288, 3695430, 3684266, 14641400, 4242577, 1090524, 3874322, 12223212, 3335461, 6851931,
    5354872, 10947, 2852293, 17253596, 51024608, 995760, 10914023, 8737045, 37521, 54603921,
    605212, 814052]
/-- Hit-row chunk `5` for `(m = 32, r = 256)`. -/
def rkmRowPack_m32_r256_p5 : List ℕ :=
  [924161, 8750530, 14219670, 2940199, 1826787, 1133958, 6348854, 1635490, 32184432, 2792280,
    13789359, 12179364, 16953612, 39014480, 7078841, 9688895, 2860493, 9227388, 98202, 4718948,
    2344279, 10778150, 1505792, 587308, 4081368, 5091009, 1208068, 86993882, 4320449, 17601333,
    92357157, 5215973]
/-- Hit-row chunk `6` for `(m = 32, r = 256)`. -/
def rkmRowPack_m32_r256_p6 : List ℕ :=
  [15538438, 182440315, 28690036, 6493982, 664662, 34929335, 21536232, 4802897, 24217218,
    77240, 464114051, 18532252, 35848991, 222155173, 5622845, 713080575, 450396148, 366046514,
    167528160, 160415671, 399764, 179125597, 238261302, 2763048, 6740275, 596602, 123449963,
    126921494, 3276893, 7828157, 2227418, 295376076]
/-- Hit-row chunk `7` for `(m = 32, r = 256)`. -/
def rkmRowPack_m32_r256_p7 : List ℕ :=
  [317608483, 115460877, 2566568, 73638949, 14840789, 976604824, 1927238591, 310713053,
    12962903, 44761104, 59258657, 1004268454, 834309348, 115784584, 144315880, 2525952755,
    83986361, 2868228645, 680056, 3789890713, 3997120272, 12449820, 4853889534, 937195773,
    4504128503, 10952359531, 21411299, 8779286708, 28350464166, 431081505, 20937454305,
    896348572511]
/-- Certified `10 ^ 12`-scaled hit row for `(m = 32, r = 256)`. -/
def rkmRowPack_m32_r256 : List ℕ :=
  rkmRowPack_m32_r256_p0 ++ rkmRowPack_m32_r256_p1 ++ rkmRowPack_m32_r256_p2
    ++ rkmRowPack_m32_r256_p3 ++ rkmRowPack_m32_r256_p4 ++ rkmRowPack_m32_r256_p5
    ++ rkmRowPack_m32_r256_p6 ++ rkmRowPack_m32_r256_p7

end

public section

private abbrev bZ : ℕ := 2000000000000000
private theorem hbZ0 : Nat.ble bZ 0 = false := rfl
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β :=
  HighDForce.withForcedList xs k
private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: pCat xs ys
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem hzMul0 (z : ℕ) : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem nmod (x y : ℕ) : Nat.mod x y = x % y := rfl
private def uC (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 => xs
  | v + 1 =>
    match xs with
    | [] => [v]
    | h :: t => v :: h :: t
private theorem uC_eq (x : ℕ) (xs : List ℕ) : uC x xs = x :: xs := by
  unfold uC; rw [n1a]; cases xs <;> rfl
private def uOfHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfHb ns
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ :=
  match x with
  | Int.ofNat v =>
    match xs with
    | [] => [Int.ofNat v]
    | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v =>
    match xs with
    | [] => [Int.negSucc v]
    | h :: t => Int.negSucc v :: h :: t
private theorem bCZ_eq (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem bOfF_eq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  simp [primOfNatForced, Nat.one_add]
private theorem bNsF_eq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  simp [primNegSuccForced, Nat.one_add]
private theorem bSub_eq (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat; rw [bOfF_eq, Nat.sub_eq]; cases h : z - u with
  | zero => dsimp only; rw [Nat.sub_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bCZ (rkmForcedSubNatNat u z) (bDec z us)
private theorem bDec_nil (z : ℕ) : bDec z [] = [] := rfl
private theorem bDec_cons (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by
  rw [bDec, bCZ_eq, bSub_eq]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bM0 (z : ℕ) :
    muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZ0]; rfl
private def bNL : List ℕ → ℕ
  | [] => 0
  | _ :: us => Nat.add (bNL us) 1
private theorem bNL_eq (z : ℕ) : ∀ (us : List ℕ), bNL us = altIntLen (bDec z us)
  | [] => rfl
  | _ :: us => by dsimp only [bNL]; rw [bDec_cons]; dsimp only [altIntLen]; rw [bNL_eq z us]
private def zTd : ℤ → ℕ → ℤ
  | Int.ofNat m, d => Int.ofNat (m / d)
  | Int.negSucc k, d => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTdN_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTd x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => by
    dsimp only [muxRawIntTdivNat, zTd]; rw [bNeg_eq, ndiv, Nat.add_eq]
private theorem bSubNTd_eq (m n d : ℕ) :
    rkmUltraSubNatTdiv m n d = zTd ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    dsimp only; have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTd]; rw [bNeg_eq]
private theorem bSubTd_eq (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTd (a - b) d := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact bSubNTd_eq m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
      rw [hm]; rfl
  | negSucc m =>
    cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTd]
      rw [bNeg_eq, ndiv, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [bSubNTd_eq, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTd t d) (by simp only [Int.negSucc_eq]; omega)
private theorem bMul_eq (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a <;> cases b <;>
    simp only [muxRawIntMul, bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast,
      Int.negSucc_eq] <;> push_cast <;> ring
private theorem bFAdd_eq (a b : ℤ) : rkmForcedIntAdd a b = a + b := by
  cases a <;> cases b <;>
    simp only [rkmForcedIntAdd, bOfF_eq, bNsF_eq, bSub_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
private theorem bAC_eq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bFAdd_eq]; cases a + b <;> cases xs <;> rfl
private theorem bBle : ∀ {a b : ℕ}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (bBle h)
private theorem bBleOfLe {a b : ℕ} (h : a ≤ b) : Nat.ble a b = true := Nat.ble_eq_true_of_le h
private abbrev bStepVal (v P Q d : ℕ) : ℕ :=
  Nat.sub (Nat.add v (Nat.div (Nat.sub P Q) d)) (Nat.div (Nat.sub Q P) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) =
      ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSubNTd_eq]; unfold bStepVal at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv
  cases hd : Q - P with
  | zero =>
    intro _; dsimp only; rw [Nat.zero_div, Nat.sub_zero, Int.ofNat_eq_natCast]; push_cast; ring
  | succ k =>
    intro hv; dsimp only at hv ⊢
    have hpq : P - Q = 0 := by omega
    rw [hpq, Nat.zero_div, Nat.add_zero] at hv ⊢; rw [bNeg_eq]
    generalize (k + 1) / d = q at hv ⊢; omega
private theorem bStepVal_same (z P d : ℕ) : bStepVal z P P d = z := by
  unfold bStepVal
  simp only [Nat.sub_eq, Nat.add_eq, ndiv, Nat.sub_self, Nat.zero_div, Nat.add_zero, Nat.sub_zero]
private theorem bStepVal_comm (z A B d : ℕ) :
    bStepVal z (Nat.add A B) (Nat.add B A) d = z := by
  have hc : Nat.add B A = Nat.add A B := by simp only [Nat.add_eq]; omega
  rw [hc]; exact bStepVal_same z (Nat.add A B) d
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bC_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bDec z rest = tZ) :
    bDec z (uC (bCV z d b0 c0 b v c1) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tZ := by
  rw [uC_eq, bDec_cons, ht, bAC_eq, bSubTd_eq, bMul_eq, bMul_eq]
  refine congrArg (· :: tZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCV at hv ⊢; rw [bStepVal_eq z v _ _ d hv, hpq]
private theorem bC_nil (z d b0 c0 v : ℕ) {rest : List ℕ} {tZ : List ℤ}
    (hv : 0 < bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDec z rest = tZ) :
    bDec z (uC (bStepVal v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tZ := by
  rw [uC_eq, bDec_cons, ht, bAC_eq, bTdN_eq, bMul_eq]
  refine congrArg (· :: tZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  rw [bStepVal_eq z v _ _ d hv, hpq]
private def bAllPos : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAllPos xs)
private theorem bAllPos_uC {x : ℕ} {xs : List ℕ} (h : bAllPos (uC x xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  rw [uC_eq] at h
  cases x with
  | zero => exact Bool.noConfusion h
  | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHO (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem bHOe (z : ℕ) : ∀ (cs : List ℕ),
    ((bHO z cs : ℤ) - (z : ℤ)) =
      (match bDec z cs with
       | cn :: _ => cn
       | [] => Int.ofNat 0)
  | [] => by unfold bHO; rw [bDec_nil, bZ0]
  | _ :: _ => by unfold bHO; rw [bDec_cons]
private theorem bTNe (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTN xs) =
      (match bDec z xs with
       | _ :: t => t
       | [] => [])
  | [] => rfl
  | _ :: _ => by unfold bTN; rw [bDec_cons]
private def zPad (z : ℕ) : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | k + 1, [] => uC z (zPad z k [])
  | k + 1, x :: xs => uC x (zPad z k xs)
private theorem zPad_uC (z r x : ℕ) (xs : List ℕ) :
    zPad z (r + 1) (uC x xs) = uC x (zPad z r xs) := by
  rw [uC_eq]; rfl
private theorem zPad_hd (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ), bHO z (zPad z k xs) = bHO z xs
  | 0, _ => rfl
  | _ + 1, [] => by dsimp only [zPad]; rw [uC_eq]; rfl
  | _ + 1, _ :: _ => by dsimp only [zPad]; rw [uC_eq]; rfl
private theorem zPad_tl (z : ℕ) :
    ∀ (k : ℕ) (xs : List ℕ), bTN (zPad z k xs) = zPad z (k - 1) (bTN xs)
  | 0, _ => rfl
  | _ + 1, [] => by dsimp only [zPad]; rw [uC_eq]; rfl
  | _ + 1, _ :: _ => by dsimp only [zPad]; rw [uC_eq]; rfl
private theorem zPad_bNL (z : ℕ) :
    ∀ (k : ℕ) (xs : List ℕ), Nat.ble (bNL xs) k = true → bNL (zPad z k xs) = k
  | 0, [], _ => rfl
  | 0, _ :: xs, h => by
    dsimp only [bNL] at h; rw [Nat.add_eq] at h; have h1 := bBle h; omega
  | k + 1, [], _ => by
    dsimp only [zPad]; rw [uC_eq]; dsimp only [bNL]; rw [zPad_bNL z k [] rfl, Nat.add_eq]
  | k + 1, _ :: xs, h => by
    have hk : Nat.ble (bNL xs) k = true := by
      have h1 := bBle h; dsimp only [bNL] at h1; rw [Nat.add_eq] at h1
      exact bBleOfLe (by omega)
    dsimp only [zPad]; rw [uC_eq]; dsimp only [bNL]; rw [zPad_bNL z k xs hk, Nat.add_eq]
private theorem bAllPos_zPad {z : ℕ} (hz : Nat.ble z 0 = false) :
    ∀ (k : ℕ) (xs : List ℕ), bAllPos xs = true → bAllPos (zPad z k xs) = true
  | 0, _, h => h
  | k + 1, [], _ => by
    dsimp only [zPad]; rw [uC_eq]; dsimp only [bAllPos]; rw [hz]; dsimp only [cond]
    exact bAllPos_zPad hz k [] rfl
  | k + 1, x :: xs, h => by
    dsimp only [bAllPos] at h; dsimp only [zPad]; rw [uC_eq]; dsimp only [bAllPos]
    revert h
    cases Nat.ble x 0 with
    | true => intro h; dsimp only [cond] at h; cases h
    | false => intro h; dsimp only [cond] at h ⊢; exact bAllPos_zPad hz k xs h
private def bEqN (a b : ℕ) : Bool := cond (Nat.ble a b) (Nat.ble b a) false
private theorem bEqN_self (a : ℕ) : bEqN a a = true := by
  have hle : Nat.ble a a = true := bBleOfLe (Nat.le_refl a)
  unfold bEqN; rw [hle]; rfl
private theorem bEqN_eq (a b : ℕ) (h : bEqN a b = true) : a = b := by
  unfold bEqN at h; revert h
  cases hab : Nat.ble a b with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    cases hba : Nat.ble b a with
    | false => intro h; dsimp only [cond] at h; cases h
    | true => intro _; exact Nat.le_antisymm (bBle hab) (bBle hba)
private def bCT (z x : ℕ) (xs : List ℕ) : List ℕ :=
  match xs with
  | h :: t => x :: h :: t
  | [] => cond (bEqN x z) [] [x]
private def bTrim (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => bCT z x (bTrim z xs)
private theorem bTrim_zPad (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ), bTrim z (zPad z k xs) = bTrim z xs
  | 0, _ => rfl
  | k + 1, [] => by
    dsimp only [zPad]; rw [uC_eq]; dsimp only [bTrim]; rw [bTrim_zPad z k []]
    dsimp only [bTrim, bCT]; rw [bEqN_self z]; rfl
  | k + 1, x :: xs => by
    dsimp only [zPad]; rw [uC_eq]; dsimp only [bTrim]; rw [bTrim_zPad z k xs]
private theorem zPad_bTrim_len (z : ℕ) : ∀ (xs : List ℕ), zPad z (bNL xs) (bTrim z xs) = xs
  | [] => rfl
  | x :: t => by
    have hal : bNL (x :: t) = bNL t + 1 := rfl
    rw [hal]; dsimp only [bTrim]; have ih := zPad_bTrim_len z t; revert ih
    cases bTrim z t with
    | cons _ _ => intro ih; dsimp only [bCT, zPad]; rw [uC_eq, ih]
    | nil =>
      intro ih; dsimp only [bCT]
      cases he : bEqN x z with
      | true => dsimp only [cond, zPad]; rw [uC_eq, bEqN_eq x z he, ih]
      | false => dsimp only [cond, zPad]; rw [uC_eq, ih]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, [], vs, cs =>
    uC (bStepVal (bHO z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
      (bSl z d rem 0 z [] (bTN vs) (bTN cs))
  | rem + 1, b0, c0, b :: bR, vs, cs =>
    uC (bCV z d b0 c0 b (bHO z vs) (bHO z (bTN cs)))
      (bSl z d rem b (bHO z cs) bR (bTN vs) (bTN cs))
private theorem bSl_len (z d : ℕ) :
    ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ), bNL (bSl z d rem b0 c0 bns vs cs) = rem
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, [], vs, cs => by
    dsimp only [bSl]; rw [uC_eq]; dsimp only [bNL]
    rw [bSl_len z d rem 0 z [] (bTN vs) (bTN cs), Nat.add_eq]
  | rem + 1, b0, c0, b :: bR, vs, cs => by
    dsimp only [bSl]; rw [uC_eq]; dsimp only [bNL]
    rw [bSl_len z d rem b (bHO z cs) bR (bTN vs) (bTN cs), Nat.add_eq]
private theorem bSl_zPad (z d : ℕ) : ∀ (rem b0 c0 kv kc : ℕ) (bns vs cs : List ℕ),
    bSl z d rem b0 c0 bns (zPad z kv vs) (zPad z kc cs) = bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, kv, kc, [], vs, cs => by
    dsimp only [bSl]; rw [zPad_hd z kv vs, zPad_tl z kv vs, zPad_tl z kc cs]
    rw [bSl_zPad z d rem 0 z (kv - 1) (kc - 1) [] (bTN vs) (bTN cs)]
  | rem + 1, b0, c0, kv, kc, b :: bR, vs, cs => by
    dsimp only [bSl]
    rw [zPad_hd z kv vs, zPad_tl z kc cs, zPad_hd z (kc - 1) (bTN cs), zPad_hd z kc cs,
      zPad_tl z kv vs]
    rw [bSl_zPad z d rem b (bHO z cs) (kv - 1) (kc - 1) bR (bTN vs) (bTN cs)]
private theorem bSl_zero (z d : ℕ) :
    ∀ (rem b0 : ℕ) (bns : List ℕ), bSl z d rem b0 z bns [] [] = zPad z rem []
  | 0, _, _ => rfl
  | rem + 1, b0, [] => by
    dsimp only [bSl, bHO, bTN, zPad]; rw [bStepVal_same z (Nat.mul b0 z) d, bSl_zero z d rem 0 []]
  | rem + 1, b0, b :: bR => by
    dsimp only [bSl, bCV, bHO, bTN, zPad]
    rw [bStepVal_comm z (Nat.mul b0 z) (Nat.mul b z) d, bSl_zero z d rem b bR]
private theorem bSl_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSl z d rem b0 c0 bns vs cs) = true →
      bDec z (bSl z d rem b0 c0 bns vs cs) =
        rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (uOfHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, [], vs, cs, h => by
    dsimp only [bSl, uOfHb, rkmUltraSlideLoopAux] at h ⊢
    have hp := bAllPos_uC h
    have hi := bSl_sound z d rem 0 z [] (bTN vs) (bTN cs) hp.2
    rw [bM0 z, uOfHb, bTNe z vs, bTNe z cs] at hi
    have hc := bC_nil z d b0 c0 (bHO z vs) hp.1 hi
    rw [bHOe z vs] at hc; exact hc
  | rem + 1, b0, c0, b :: bR, [], [], h => by
    dsimp only [bSl, bHO, bTN, uOfHb] at h ⊢; rw [bDec_nil]
    dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uC h
    have hi := bSl_sound z d rem b z bR [] [] hp.2
    rw [bZ0 z, bDec_nil] at hi
    have hc := bC_hb z d b0 c0 b z z hp.1 hi; rw [bZ0 z] at hc; exact hc
  | rem + 1, b0, c0, b :: bR, [], c :: cT, h => by
    dsimp only [bSl, bHO, bTN, uOfHb] at h ⊢
    rw [bDec_nil, bDec_cons z c cT]; dsimp only [rkmUltraSlideLoopAux]
    have hp := bAllPos_uC h
    have hi := bSl_sound z d rem b c bR [] cT hp.2; rw [bDec_nil] at hi
    have hc := bC_hb z d b0 c0 b z (bHO z cT) hp.1 hi
    rw [bHOe z cT, bZ0 z] at hc; exact hc
  | rem + 1, b0, c0, b :: bR, v :: vT, [], h => by
    dsimp only [bSl, bHO, bTN, uOfHb] at h ⊢
    rw [bDec_cons z v vT, bDec_nil]; dsimp only [rkmUltraSlideLoopAux]
    have hp := bAllPos_uC h
    have hi := bSl_sound z d rem b z bR vT [] hp.2; rw [bZ0 z, bDec_nil] at hi
    have hc := bC_hb z d b0 c0 b v z hp.1 hi; rw [bZ0 z] at hc; exact hc
  | rem + 1, b0, c0, b :: bR, v :: vT, c :: cT, h => by
    dsimp only [bSl, bHO, bTN, uOfHb] at h ⊢
    rw [bDec_cons z v vT, bDec_cons z c cT]; dsimp only [rkmUltraSlideLoopAux]
    have hp := bAllPos_uC h
    have hi := bSl_sound z d rem b c bR vT cT hp.2
    have hc := bC_hb z d b0 c0 b v (bHO z cT) hp.1 hi
    rw [bHOe z cT] at hc; exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uC b (uC (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | [] =>
      match vs, cs with
      | [], [] => uC (bStepVal z p0 q0 d) []
      | _, _ => uC (bStepVal (bHO z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTN vs) (bTN cs))
    | [_] => []
    | b :: bz :: bR =>
      match vs, cs with
      | [], [] => uC (bStepVal z (Nat.add p0 bz) (Nat.add bz q0) d) []
      | v :: vT, c :: cT =>
        uC (bStepVal v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] =>
        uC (bStepVal v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT =>
        uC (bStepVal z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
private theorem bSlZ_zPad (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    zPad z rem (bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs) =
      bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, _, _, bns, vs, cs => by
    cases bns with
    | nil =>
      cases vs with
      | nil =>
        cases cs with
        | nil => dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]; rw [zPad_uC, bSl_zero z d rem 0 []]
        | cons _ cT =>
          have hrec := bSlZ_zPad z d rem 0 z [] [] cT
          dsimp only [mkHbZ] at hrec; rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]; rw [zPad_uC, hrec]
      | cons _ vT =>
        cases cs with
        | nil =>
          have hrec := bSlZ_zPad z d rem 0 z [] vT []
          dsimp only [mkHbZ] at hrec; rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]; rw [zPad_uC, hrec]
        | cons _ cT =>
          have hrec := bSlZ_zPad z d rem 0 z [] vT cT
          dsimp only [mkHbZ] at hrec; rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]; rw [zPad_uC, hrec]
    | cons b bR =>
      dsimp only [mkHbZ]; rw [uC_eq, uC_eq]; cases vs with
      | nil =>
        cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV, bHO, bTN]; rw [zPad_uC, bSl_zero z d rem b bR]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]; rw [zPad_uC, bSlZ_zPad z d rem b c bR [] cT]
      | cons v vT =>
        cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV, bHO, bTN]; rw [zPad_uC, bSlZ_zPad z d rem b z bR vT []]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]; rw [zPad_uC, bSlZ_zPad z d rem b c bR vT cT]
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
      | nil => rfl
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
private theorem fH4e {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
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
    rcases takeH4_spec k r with heq | ⟨t, happ, hlen⟩
    · exact Or.inl (congrArg (hbz4C b1 z1 b2 z2 b3 z3 b4 z4) heq)
    · refine Or.inr ⟨t, ?_, ?_⟩
      · rw [hbz4C_app, hbz4C_app, happ, List.append_assoc]
      · rw [hbz4C_app, List.length_append, hbz4P_len]; omega
private theorem bSlZ_takeH4 (z d k : ℕ) (hbz : HbZ4) (rem p0 q0 : ℕ)
    (vs cs : List ℕ) (h : rem ≤ 4 * k) :
    bSlZ z d rem p0 q0 (takeH4 k hbz) vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs := by
  rcases takeH4_spec k hbz with heq | ⟨t, happ, hlen⟩
  · rw [heq]
  · rw [happ]; exact (bSlZ_pfx z d rem (takeH4 k hbz) t p0 q0 vs cs (by omega)).symm
private inductive Q4 : Type
  | tail : List ℕ → Q4
  | c4 : ℕ → ℕ → ℕ → ℕ → Q4 → Q4
private def q4L : Q4 → List ℕ
  | Q4.tail xs => xs
  | Q4.c4 x1 x2 x3 x4 r => x1 :: x2 :: x3 :: x4 :: q4L r
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
private def fQ4 {α : Type} (v : Q4) (k : Q4 → α) : α :=
  match v with
  | Q4.tail xs => k (Q4.tail xs)
  | Q4.c4 x1 x2 x3 x4 r => k (Q4.c4 x1 x2 x3 x4 r)
private theorem fQ4e {α : Type} (v : Q4) (k : Q4 → α) : fQ4 v k = k v := by
  cases v <;> rfl
private def q4Hd (z : ℕ) : Q4 → ℕ
  | Q4.c4 x _ _ _ _ => x
  | Q4.tail xs => bHO z xs
private theorem q4Hd_eq (z : ℕ) (w : Q4) : q4Hd z w = bHO z (q4L w) := by
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
private theorem cond_some_eq {α : Type} {b : Bool} {x y : α}
    (h : cond b (some x) none = some y) : b = true ∧ x = y := by
  cases b with
  | false => cases h
  | true => dsimp only [cond] at h; injection h with h'; exact ⟨rfl, h'⟩
private def bSlQ4 (z d rT : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Q4 → Q4
  | 0, p0, q0, hbz, vs, cs => toQ4 (bSlZ z d rT p0 q0 (takeH4 1 hbz) (q4L vs) (q4L cs))
  | q + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | HbZ4.tail l =>
      toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0 l (q4L vs) (q4L cs))
    | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
      match vs with
      | Q4.tail [] =>
        match cs with
        | Q4.tail [] =>
          fN (bStepVal z (Nat.add p0 z1) (Nat.add z1 q0) d) fun y => Q4.tail [y]
        | Q4.tail (c1 :: cxs) =>
          toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
            (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)) [] (c1 :: cxs))
        | Q4.c4 c1 c2 c3 c4 cR =>
          match Nat.add 1 (Nat.mul b4 c4) with
          | 0 => Q4.tail []
          | bc4 + 1 =>
            q4S (bStepVal z (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
              (bStepVal z (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
              (bStepVal z (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
              (bStepVal z (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
              (bSlQ4 z d rT q bc4 z4 bR (Q4.tail []) cR)
      | Q4.tail (v1 :: vt1) =>
        match cs with
        | Q4.tail cxs =>
          toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
            (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)) (v1 :: vt1) cxs)
        | Q4.c4 c1 c2 c3 c4 cR =>
          match vt1 with
          | [] =>
            match Nat.add 1 (Nat.mul b4 c4) with
            | 0 => Q4.tail []
            | bc4 + 1 =>
              q4S (bStepVal v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                (bStepVal z (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                (bStepVal z (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                (bStepVal z (Nat.add (Nat.mul b3 c3) z4)
                  (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
                (bSlQ4 z d rT q bc4 z4 bR (Q4.tail []) cR)
          | v2 :: vt2 =>
            match vt2 with
            | [] =>
              match Nat.add 1 (Nat.mul b4 c4) with
              | 0 => Q4.tail []
              | bc4 + 1 =>
                q4S (bStepVal v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                  (bStepVal v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                  (bStepVal z (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                  (bStepVal z (Nat.add (Nat.mul b3 c3) z4)
                    (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
                  (bSlQ4 z d rT q bc4 z4 bR (Q4.tail []) cR)
            | v3 :: vt3 =>
              match vt3 with
              | [] =>
                match Nat.add 1 (Nat.mul b4 c4) with
                | 0 => Q4.tail []
                | bc4 + 1 =>
                  q4S (bStepVal v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                    (bStepVal v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                    (bStepVal v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                    (bStepVal z (Nat.add (Nat.mul b3 c3) z4)
                      (Nat.add (Nat.mul b4 (q4Hd z cR)) z3) d)
                    (bSlQ4 z d rT q bc4 z4 bR (Q4.tail []) cR)
              | v4 :: vt4 =>
                toQ4 (bSlZ z d (Nat.add (Nat.mul 4 (Nat.add q 1)) rT) p0 q0
                  (takeH4 (Nat.add q 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR))
                  (v1 :: v2 :: v3 :: v4 :: vt4) (c1 :: c2 :: c3 :: c4 :: q4L cR))
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
    have h4 : 4 * (q + 1) + rT = ((((4 * q + rT) + 1) + 1) + 1) + 1 := by omega
    cases hbz with
    | tail l => dsimp only [bSlQ4, hbz4L]; rw [q4L_toQ4, hrem]
    | c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
      cases vs with
      | tail vxs =>
        cases vxs with
        | nil =>
          cases cs with
          | tail cxs =>
            cases cxs with
            | nil =>
              dsimp only [bSlQ4, fN]; rw [rkmb_forceNat_eq, h4]
              dsimp only [hbz4L, hbz4C, q4L, bSlZ]; rw [uC_eq]
            | cons c1 ct =>
              dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
              exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
                (4 * (q + 1) + rT) p0 q0 [] (c1 :: ct) hle
          | c4 c1 c2 c3 c4 cR =>
            dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq, h4]
            dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO]
            rw [uC_eq, uC_eq, uC_eq, uC_eq]
            rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR (Q4.tail []) cR]; rfl
        | cons v1 vt1 =>
          cases cs with
          | tail cxs =>
            dsimp only [bSlQ4, q4L]; rw [q4L_toQ4, hrem, hq2]
            exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
              (4 * (q + 1) + rT) p0 q0 (v1 :: vt1) cxs hle
          | c4 c1 c2 c3 c4 cR =>
            cases vt1 with
            | nil =>
              dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq, h4]
              dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO]
              rw [uC_eq, uC_eq, uC_eq, uC_eq]
              rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR (Q4.tail []) cR]; rfl
            | cons v2 vt2 =>
              cases vt2 with
              | nil =>
                dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq, h4]
                dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO]
                rw [uC_eq, uC_eq, uC_eq, uC_eq]
                rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR (Q4.tail []) cR]; rfl
              | cons v3 vt3 =>
                cases vt3 with
                | nil =>
                  dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq, h4]
                  dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO]
                  rw [uC_eq, uC_eq, uC_eq, uC_eq]
                  rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR (Q4.tail []) cR]; rfl
                | cons v4 vt4 =>
                  dsimp only [bSlQ4, q4L]; rw [q4L_toQ4, hrem, hq2]
                  exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
                    (4 * (q + 1) + rT) p0 q0 (v1 :: v2 :: v3 :: v4 :: vt4)
                    (c1 :: c2 :: c3 :: c4 :: q4L cR) hle
      | c4 v1 v2 v3 v4 vR =>
        cases cs with
        | tail cxs =>
          dsimp only [bSlQ4]; rw [q4L_toQ4, hrem, hq2]
          exact bSlZ_takeH4 z d (q + 2) (HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR)
            (4 * (q + 1) + rT) p0 q0 (v1 :: v2 :: v3 :: v4 :: q4L vR) cxs hle
        | c4 c1 c2 c3 c4 cR =>
          dsimp only [bSlQ4]; rw [n1a (Nat.mul b4 c4)]; dsimp only; rw [q4S_eq, q4Hd_eq, h4]
          dsimp only [hbz4L, hbz4C, q4L, bSlZ, bHO]
          rw [uC_eq, uC_eq, uC_eq, uC_eq]
          rw [bSlQ4_eq z d rT hr q (Nat.mul b4 c4) z4 bR vR cR]
private def bStg (z dg mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4) : Option Q4 :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.div nL 4) fun q4 => fN (Nat.mod nL 4) fun rT =>
    fN (Nat.mul dg wdScale) fun d => bChkV (bSlQ4 z d rT q4 0 0 h4 vs cs)
private theorem bStg_zPad {z dg mL cL : ℕ} {b : List ℕ} {vs cs out : Q4}
    (h : bStg z dg mL cL (toH4 (mkHbZ z b)) vs cs = some out) :
    bAllPos (q4L out) = true ∧
      zPad z (rkmNextLen mL cL) (q4L out) =
        bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b (q4L vs) (q4L cs) := by
  unfold bStg at h; dsimp only [fN] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceNat_eq, bChkV_eq] at h
  rcases cond_some_eq h with ⟨hv, rfl⟩
  have hp := q4AP_pos _ hv
  refine ⟨hp, ?_⟩
  have hr : Nat.mod (rkmNextLen mL cL) 4 ≤ 4 := by rw [nmod]; omega
  have hqr : 4 * Nat.div (rkmNextLen mL cL) 4 + Nat.mod (rkmNextLen mL cL) 4 =
      rkmNextLen mL cL := by rw [ndiv, nmod]; omega
  have hsl := bSlZ_zPad z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b (q4L vs) (q4L cs)
  rw [hzMul0 z] at hsl
  rw [bSlQ4_eq _ _ _ hr, hqr, hbz4L_toH4]
  exact hsl
private theorem bStg_sound {z : ℕ} (hz : Nat.ble z 0 = false) (dg mL vL cL : ℕ)
    (b : List ℕ) (vs cs out : Q4)
    (h : bStg z dg mL cL (toH4 (mkHbZ z b)) vs cs = some out) :
    bDec z (zPad z (rkmNextLen mL cL) (q4L out)) =
      rkmUltraHornerStage dg mL cL (uOfHb b)
        (bDec z (zPad z vL (q4L vs))) (bDec z (zPad z cL (q4L cs))) := by
  rcases bStg_zPad h with ⟨hp, hsl⟩
  have hpos : bAllPos (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b
      (zPad z vL (q4L vs)) (zPad z cL (q4L cs))) = true := by
    rw [bSl_zPad, ← hsl]; exact bAllPos_zPad hz _ _ hp
  unfold rkmUltraHornerStage
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, hsl,
    ← bSl_zPad z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z vL cL b (q4L vs) (q4L cs)]
  have hs := bSl_sound z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b
    (zPad z vL (q4L vs)) (zPad z cL (q4L cs)) hpos
  rw [bM0 z] at hs; exact hs
private def bStg1 (z mL cL : ℕ) (h4 : HbZ4) (vs cs : Q4) : Option Q4 :=
  match bStg z 1 mL cL h4 vs cs with
  | none => none
  | some raw => fL (bTrim z (q4L raw)) fun tr => some (toQ4 tr)
private theorem bStg1_sound {z : ℕ} (hz : Nat.ble z 0 = false) (mL vL cL : ℕ)
    (b : List ℕ) (vs cs out : Q4)
    (h : bStg1 z mL cL (toH4 (mkHbZ z b)) vs cs = some out) :
    bDec z (zPad z (rkmNextLen mL cL) (q4L out)) =
      rkmUltraHornerStage 1 mL cL (uOfHb b)
        (bDec z (zPad z vL (q4L vs))) (bDec z (zPad z cL (q4L cs))) := by
  unfold bStg1 at h; revert h
  cases hd : bStg z 1 mL cL (toH4 (mkHbZ z b)) vs cs with
  | none => intro h; dsimp only at h; cases h
  | some raw =>
    intro h; dsimp only [fL] at h; rw [rkmb_forceList_eq] at h
    injection h with h'; subst h'; rw [q4L_toQ4]
    rcases bStg_zPad hd with ⟨_, hsl⟩
    have hpad := zPad_bTrim_len z
      (bSl z (Nat.mul 1 wdScale) (rkmNextLen mL cL) 0 z b (q4L vs) (q4L cs))
    rw [bSl_len] at hpad
    rw [← bTrim_zPad z (rkmNextLen mL cL) (q4L raw), hsl, hpad, ← hsl]
    exact bStg_sound hz 1 mL vL cL b vs cs raw hd
private def bBdD (z g m c : ℕ) (h4 : HbZ4) (vs cs : Q4)
    (k : ℕ → Q4 → Option Q4) : Option Q4 :=
  fN (rkmNextLen m c) fun n =>
    match bStg z g m c h4 vs cs with
    | none => none
    | some o => k n o
private theorem bBdD_sound {z : ℕ} (hz : Nat.ble z 0 = false) {endL g m vL c : ℕ}
    {b : List ℕ} {vs cs out : Q4} {kB : ℕ → Q4 → Option Q4} {kU : ℕ → List ℤ → List ℤ}
    (h : bBdD z g m c (toH4 (mkHbZ z b)) vs cs kB = some out)
    (hk : ∀ (m0 : Q4), kB (rkmNextLen m c) m0 = some out →
      bDec z (zPad z endL (q4L out)) =
        kU (rkmNextLen m c) (bDec z (zPad z (rkmNextLen m c) (q4L m0)))) :
    bDec z (zPad z endL (q4L out)) =
      (HighDForce.withForcedNat (rkmNextLen m c) fun nL => HighDForce.withForcedList
        (rkmUltraHornerStage g m c (uOfHb b)
          (bDec z (zPad z vL (q4L vs))) (bDec z (zPad z c (q4L cs)))) (kU nL)) := by
  unfold bBdD at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; revert h
  cases hs : bStg z g m c (toH4 (mkHbZ z b)) vs cs with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound hz g m vL c b vs cs mid hs]
    exact hk mid h
private def bSpD (z m c : ℕ) (h4 : HbZ4) (vs : Q4) : Option Q4 :=
  bBdD z 16 m c h4 vs vs fun l x => bBdD z 15 m l h4 vs x fun l x =>
  bBdD z 14 m l h4 vs x fun l x => bBdD z 13 m l h4 vs x fun l x =>
  bBdD z 12 m l h4 vs x fun l x => bBdD z 11 m l h4 vs x fun l x =>
  bBdD z 10 m l h4 vs x fun l x => bBdD z 9 m l h4 vs x fun l x =>
  bBdD z 8 m l h4 vs x fun l x => bBdD z 7 m l h4 vs x fun l x =>
  bBdD z 6 m l h4 vs x fun l x => bBdD z 5 m l h4 vs x fun l x =>
  bBdD z 4 m l h4 vs x fun l x => bBdD z 3 m l h4 vs x fun l x =>
  bBdD z 2 m l h4 vs x fun l x => bStg1 z m l h4 vs x
private theorem bSpD_sound {z : ℕ} (hz : Nat.ble z 0 = false) (mL cL : ℕ)
    (b : List ℕ) (vs out : Q4)
    (h : bSpD z mL cL (toH4 (mkHbZ z b)) vs = some out) :
    bDec z (zPad z (rkmNextLen16 mL cL) (q4L out)) =
      rkmUltraHornerT16Step mL cL (uOfHb b) (bDec z (zPad z cL (q4L vs))) := by
  unfold bSpD at h; unfold rkmUltraHornerT16Step
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  unfold rkmNextLen16; exact bStg1_sound hz mL cL _ b vs _ out h
private def bItD (z : ℕ) : ℕ → ℕ → ℕ → HbZ4 → Q4 → Option (ℕ × Q4)
  | 0, _, c, _, vs => some (c, vs)
  | k + 1, m, c, h4, vs =>
    match bSpD z m c h4 vs with
    | none => none
    | some vN => fN (rkmNextLen16 m c) fun nL => bItD z k m nL h4 vN
private theorem bItD_sound {z : ℕ} (hz : Nat.ble z 0 = false) :
    ∀ (k m c : ℕ) (b : List ℕ) (vs : Q4) (endL : ℕ) (outV : Q4),
      bItD z k m c (toH4 (mkHbZ z b)) vs = some (endL, outV) →
        bDec z (zPad z endL (q4L outV)) =
          muxUltraIterFullT16Rkm k m c (uOfHb b) (bDec z (zPad z c (q4L vs)))
  | 0, _, _, _, _, _, _, h => by
    injection h with h'; injection h' with hc hv; subst hc; subst hv; rfl
  | k + 1, m, c, b, vs, endL, outV, h => by
    unfold bItD at h; revert h
    cases hs : bSpD z m c (toH4 (mkHbZ z b)) vs with
    | none => intro h; dsimp only at h; cases h
    | some vN =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
      unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bSpD_sound hz m c b vs vN hs]
      exact bItD_sound hz k m _ b vN endL outV h
private theorem u2f {s m : ℕ} {b u v : List ℤ}
    (h : muxUltraIterFullT16Rkm s m (altIntLen u) b u = v) :
    muxFastIterFullT16 s m b u = v := by
  have hc : muxUltraIterFullT16HiChk s 0 m b u v = true := by
    unfold muxUltraIterFullT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, h]
    exact muxIntListEq_eq_true.mpr rfl
  exact muxUltraIterFullT16HiChk_sound hc
private def bWalkOk (k mL : ℕ) (bns : List ℕ) (l0 : ℕ) (uT : List ℕ) (l1 : ℕ) (vT : List ℕ) :
    Prop :=
  muxFastIterFullT16 k mL (uOfHb bns) (bDec bZ (zPad bZ l0 uT)) = bDec bZ (zPad bZ l1 vT)
private def bSlideChk (steps mL : ℕ) (bns : List ℕ) (l0 : ℕ) (uT : List ℕ)
    (l1 : ℕ) (vT : List ℕ) : Bool :=
  fL bns fun bF => fL uT fun uF => fL vT fun vF =>
    cond (Nat.ble (bNL uF) l0)
      (fH4 (toH4 (mkHbZ bZ bF)) fun h4 =>
        fQ4 (toQ4 uF) fun uV =>
          match bItD bZ steps mL l0 h4 uV with
          | none => false
          | some (endL, outV) =>
            cond (muxNatListEq [endL] [l1]) (muxNatListEq (q4L outV) vF) false)
      false
private theorem bSlideChk_s {steps mL : ℕ} {bns : List ℕ} {l0 : ℕ} {uT : List ℕ}
    {l1 : ℕ} {vT : List ℕ} (h : bSlideChk steps mL bns l0 uT l1 vT = true) :
    bWalkOk steps mL bns l0 uT l1 vT := by
  unfold bSlideChk at h; unfold bWalkOk; dsimp only [fL] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq] at h
  revert h; cases hle : Nat.ble (bNL uT) l0 with
  | false => intro h; dsimp only [cond] at h; exact Bool.noConfusion h
  | true =>
    intro h; dsimp only [cond] at h; rw [fH4e, fQ4e] at h; revert h
    cases hi : bItD bZ steps mL l0 (toH4 (mkHbZ bZ bns)) (toQ4 uT) with
    | none => intro h; dsimp only at h; exact Bool.noConfusion h
    | some p =>
      cases p with
      | mk endL outV =>
        intro h; dsimp only at h; revert h
        cases he : muxNatListEq [endL] [l1] with
        | false => intro h; dsimp only [cond] at h; exact Bool.noConfusion h
        | true =>
          intro h; dsimp only [cond] at h
          have hl1 : endL = l1 := (List.cons.inj (muxNatListEq_eq_true.mp he)).1
          have hot : q4L outV = vT := muxNatListEq_eq_true.mp h
          have hit := bItD_sound hbZ0 steps mL l0 bns (toQ4 uT) endL outV hi
          rw [q4L_toQ4, hl1, hot] at hit
          have hln : altIntLen (bDec bZ (zPad bZ l0 uT)) = l0 := by
            rw [← bNL_eq bZ]; exact zPad_bNL bZ l0 uT hle
          exact u2f (by rw [hln]; exact hit.symm)
private theorem bWalk1 {k mL : ℕ} {bns : List ℕ} {l0 : ℕ} {v0 : List ℕ} {l1 : ℕ} {v1 : List ℕ}
    (h : bSlideChk k mL bns l0 v0 l1 v1 = true) : bWalkOk k mL bns l0 v0 l1 v1 :=
  bSlideChk_s h
private theorem bChn {a b ab mL : ℕ} {bns : List ℕ} {l0 : ℕ} {v0 : List ℕ}
    {l1 : ℕ} {v1 : List ℕ} {l2 : ℕ} {v2 : List ℕ} (hab : a + b = ab)
    (h1 : bWalkOk a mL bns l0 v0 l1 v1) (h2 : bSlideChk b mL bns l1 v1 l2 v2 = true) :
    bWalkOk ab mL bns l0 v0 l2 v2 := by
  unfold bWalkOk at h1 ⊢; subst hab
  exact (muxFastIterFullT16_add a b mL (uOfHb bns) (bDec bZ (zPad bZ l0 v0))).trans
    ((congrArg (muxFastIterFullT16 b mL (uOfHb bns)) h1).trans (bSlideChk_s h2))
private theorem bSeg_mk {n d ml : ℕ} {bns : List ℕ} {l0 : ℕ} {v0 : List ℕ} {l1 : ℕ} {v1 : List ℕ}
    (hd : d = ml) (hw : bWalkOk n ml bns l0 v0 l1 v1) :
    muxFastIterFullT16 n d (uOfHb bns) (bDec bZ (zPad bZ l0 v0)) = bDec bZ (zPad bZ l1 v1) := by
  subst hd; exact hw
private theorem rkmHd {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) :
    b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) :
    rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def phb_m8_r256_0 : List ℕ :=
  [414516222724037, 547281369142735, 619340765710531, 651556098754939, 650267163568308,
    615672377474440, 541889302973590, 408809729133943]
private def pvn_m8_r256_0_0 : List ℕ := [3000000000000000]
private def pvn_m8_r256_0_1 : List ℕ :=
  [2705514982401804, 2602745770548229, 2339878637850713, 2144565269547869, 2048507642954941,
    2012992989583879, 2002745410916556, 2000437564943108, 2000046027691046]
private def phb_m8_r256_1 : List ℕ :=
  [272795552000000, 372810408009321, 440249442100588, 488899106077109, 524122985721894,
    548613056597810, 563866554184834, 570720184697104, 569573007286554, 560473143903559,
    543121296145137, 516792233281184, 480124530804130, 430610973280259, 363183091499064,
    264682862850667]
private def pvn_m8_r256_1_1 : List ℕ :=
  [2141189563908805, 2302460429325678, 2439172904325394, 2497693141428782, 2465421879338863,
    2369593743432460, 2253300176468599, 2151198407584587, 2078958458238787, 2036102246842059,
    2014414878288965, 2004994412214942, 2001485283472557, 2000372460073932, 2000076441481926,
    2000012133342066, 2000001292836716]
private def phb_m8_r256_2 : List ℕ :=
  [256661523872616, 356559269745457, 428749779482591, 485797249810509, 532635470828440,
    571821084240414, 604883161533835, 632820395809475, 656324343225002, 675893377664665,
    691896339871867, 704610497631926, 714245287767440, 720957645562279, 724862047947895,
    726037027341922, 724529160652292, 720355089965527, 713501833546803, 703925411910741,
    691547584196766, 676250206573463, 657866305545799, 636166261165928, 610836228380974,
    581443447409138, 547377853164331, 507747221650669, 461171239134159, 405321816163957,
    335672575656225, 240620178630577]
private def pvn_m8_r256_2_1 : List ℕ :=
  [2000283112379520, 2001421594718038, 2004915418025184, 2013458694965485, 2030932809358317,
    2061585641760087, 2108297194527692, 2170411248955738, 2242177683651569, 2312934934100711,
    2369518113979593, 2400230337348607, 2398744378407504, 2366169307182826, 2310383235533345,
    2243076477577225, 2175960079174540, 2117739888164672, 2072795160273983, 2041552640454747,
    2021870762467368, 2010595717784940, 2004713803777690, 2001919749002687, 2000712859860987,
    2000240089697069, 2000072835094638, 2000019716380717, 2000004700116492, 2000000967629370,
    2000000166724376, 2000000022687372, 2000000002113353]
private def phb_m8_r256_3 : List ℕ :=
  [189072827733248, 264773497714841, 321064641808363, 367006979597677, 406144005443885,
    440309080053464, 470600268844172, 497738511508057, 522228126289553, 544438678539050,
    564650771492278, 583083497077862, 599911809057581, 615278008300000, 629299612761198,
    642074914260241, 653687002857284, 664206745428216, 673695031842989, 682204496453597,
    689780856019725, 696463962085289, 702288637201562, 707285344972020, 711480730446752,
    714898057908406, 717557566282251, 719476757431644, 720670628908774, 721151859940310,
    720930957276337, 720016365833449, 718414547685028, 716130031793124, 713165435858918,
    709521460727694, 705196856862110, 700188361437961, 694490603559408, 688095973865435,
    680994453318033, 673173394109456, 664617243242151, 655307196197325, 645220763894554,
    634331230381285, 622606970665528, 610010586725921, 596497803290546, 582016040727190,
    566502545821152, 549881904693127, 532062672275792, 512932705417595, 492352536082053,
    470145676606435, 446083920498278, 419864063688261, 391068986606023, 359097920567715,
    323029435646390, 281315024488889, 230943257506587, 164167729325689]
private def pvn_m8_r256_3_1_p0 : List ℕ :=
  [2000000022194424, 2000000016066078, 2000000039038256, 2000000127160349, 2000000261954187,
    2000000402586900, 2000000509273905, 2000000521530349, 2000000373765138, 2000000094796577,
    1999999919264986, 2000000411139433, 2000002960982192, 2000011605680712, 2000038046797420,
    2000113312694056, 2000311704400653, 2000794425318456, 2001879122582752, 2004133799940738,
    2008476259743818, 2016234813996021, 2029102207575296, 2048910818895551, 2077192802202053,
    2114570381105536, 2160128495312785, 2211005643906433, 2262441173978698, 2308405898171371,
    2342740409269018, 2360511491159586, 2359173655336356, 2339159332301706, 2303711983024010,
    2258039822796312, 2208088896296805, 2159324233437797, 2115846002714056, 2080002453048664,
    2052476548047190, 2032692018359668, 2019340307109490, 2010862095946123, 2005789287110248,
    2002926675661662, 2001402417725197, 2000636472439338, 2000273305791933, 2000110907846141,
    2000042470899553, 2000015320844656, 2000005195549095, 2000001652145139, 2000000491148017,
    2000000135990479, 2000000034908790, 2000000008259785, 2000000001787968, 2000000000350583,
    2000000000061416, 2000000000009417, 2000000000001221, 2000000000000124]
private def pvn_m8_r256_3_1_p1 : List ℕ := [2000000000000007]
private def pvn_m8_r256_3_1 : List ℕ :=
  pCat pvn_m8_r256_3_1_p0
      pvn_m8_r256_3_1_p1
private def phb_m8_r256_4_p0 : List ℕ :=
  [146417960560734, 205852589424272, 250629474820722, 287683297844409, 319716831988903,
    348124370734425, 373738919354759, 397106264286855, 418607595297323, 438521956588117,
    457061126435865, 474390498389918, 490642279931599, 505924208192812, 520325516532625,
    533921144430437, 546774785296092, 558941142435547, 570467631456668, 581395686936733,
    591761780540861, 601598225027067, 610933816860949, 619794355451687, 628203066856045,
    636180952648039, 643747079542439, 650918821654645, 657712064555526, 664141378252745,
    670220164704204, 675960784308593, 681374664926354, 686472396293208, 691263812147992,
    695758061970666, 699963673888238, 703888610035971, 707540315443654, 710925761340445,
    714051483628248, 716923617155905, 719547926329635, 721929832514897, 724074438618160,
    725986551181287, 727670700274408, 729131157433706, 730371951857119, 731396885042522,
    732209544028734, 732813313378881, 733211386027781, 733406773099536, 733402312788138,
    733200678382185, 732804385504593, 732215798629178, 731437136928029, 730470479496505,
    729317769996374, 727980820751846, 726461316328108, 724760816617154]
private def phb_m8_r256_4_p1 : List ℕ :=
  [722880759451303, 720822462760647, 718587126286736, 716175832861023, 713589549252893,
    710829126588452, 707895300337567, 704788689862895, 701509797520747, 698059007299537,
    694436582977218, 690642665774384, 686677271474603, 682540286977861, 678231466246712,
    673750425597644, 669096638282183, 664269428293123, 659267963320863, 654091246772795,
    648738108754753, 643207195897344, 637496959890988, 631605644571237, 625531271369613,
    619271622913993, 612824224525400, 606186323313500, 599354864519547, 592326464690752,
    585097381191295, 577663477458993, 570020183298389, 562162449354831, 554084694732192,
    545780746489131, 537243769461399, 528466184492648, 519439572688467, 510154562704230,
    500600697289656, 490766274276039, 480638155812456, 470201537800659, 459439668948898,
    448333505372146, 436861281772010, 424997973260659, 412714611792457, 399977406237713,
    386746592579414, 372974905798751, 358605509449060, 343569127661166, 327779968934443,
    311129755119659, 293478654071281, 274640894831505, 254360673318554, 232268893531434,
    207797995377159, 179991059576824, 146979890774056, 103936772275426]
private def phb_m8_r256_4 : List ℕ :=
  pCat phb_m8_r256_4_p0
      phb_m8_r256_4_p1
private def pvn_m8_r256_4_0_p0 : List ℕ :=
  [1999999977805576, 2000000016066078, 1999999960961744, 2000000127160349, 1999999738045813,
    1999999597413100, 2000000509273905, 1999999478469651, 1999999626234862, 2000000094796577,
    1999999919264986, 1999999588860567, 1999997039017808, 1999988394319288, 1999961953202580,
    1999886687305944, 2000311704400653, 2000794425318456, 2001879122582752, 2004133799940738,
    2008476259743818, 2016234813996021, 2029102207575296, 2048910818895551, 2077192802202053,
    2114570381105536, 2160128495312785, 2211005643906433, 2262441173978698, 2308405898171371,
    2342740409269018, 2360511491159586, 2359173655336356, 2339159332301706, 2303711983024010,
    2258039822796312, 2208088896296805, 2159324233437797, 2115846002714056, 2080002453048664,
    2052476548047190, 2032692018359668, 2019340307109490, 2010862095946123, 2005789287110248,
    2002926675661662, 2001402417725197, 2000636472439338, 2000273305791933, 1999889092153859,
    1999957529100447, 1999984679155344, 1999994804450905, 2000001652145139, 2000000491148017,
    2000000135990479, 2000000034908790, 2000000008259785, 2000000001787968, 2000000000350583,
    1999999999938584, 2000000000009417, 2000000000001221, 2000000000000124]
private def pvn_m8_r256_4_0_p1 : List ℕ := [2000000000000007]
private def pvn_m8_r256_4_0 : List ℕ :=
  pCat pvn_m8_r256_4_0_p0
      pvn_m8_r256_4_0_p1
private def pvn_m8_r256_4_1_p0 : List ℕ :=
  [2000003859015465, 1999985862021168, 2000032853761259, 1999949680334713, 2000042583750447,
    1999999020330368, 1999961360454339, 2000026899764715, 2000023630174732, 1999965374169416,
    1999983577399167, 2000035532659873, 2000018262588496, 1999967652322609, 1999973259018226,
    2000022699710281, 2000037157717974, 1999997175840905, 1999960760803231, 1999974025161176,
    2000020787014152, 2000041064819049, 2000026330743554, 1999968411023727, 1999968186382664,
    1999942300036692, 2000039465139945, 2000004835122986, 2000091773095208, 2000013596600477,
    2000000310181765, 1999984569890021, 1999899917668358, 1999942762877528, 1999932780638948,
    1999905719443560, 1999969820215301, 1999947453836320, 1999880564425792, 1999888722260664,
    1999917634461215, 2000195247764292, 2001325511334552, 2004071657375299, 2009600014619182,
    2019601083042387, 2035820319373923, 2059590720228124, 2091569979191677, 2131296595200823,
    2176718442438103, 2224239015055887, 2269309120075677, 2307174940335680, 2333610379471270,
    2345663531819287, 2342265683069999, 2324406610078839, 2294782729204503, 2257124274053350,
    2215482076361163, 2173629590916118, 2134621099640372, 2100527311976067]
private def pvn_m8_r256_4_1_p1 : List ℕ :=
  [2072375465871189, 2050285474912203, 2033734045063319, 2021848308477219, 2013649557189049,
    2008213237668910, 2004750687199611, 2002635799427953, 2001399782022195, 2000710151128310,
    2000343583128451, 2000158288089818, 2000069345991864, 2000028855043323, 2000011390492553,
    2000004260724669, 2000001508550565, 2000000505084064, 2000000159857954, 2000000047880176,
    2000000013633345, 2000000003733832, 2000000001007953, 2000000000279361, 2000000000083253,
    2000000000027238, 2000000000009555, 2000000000003431, 2000000000001210, 2000000000000409,
    2000000000000129, 2000000000000037, 2000000000000009, 2000000000000001]
private def pvn_m8_r256_4_1 : List ℕ :=
  pCat pvn_m8_r256_4_1_p0
      pvn_m8_r256_4_1_p1
private def pvn_m8_r256_4_2_p0 : List ℕ :=
  [2000049693910567, 2000035207361314, 1999985868368618, 1999962250722167, 1999990057787727,
    2000028151924095, 2000028574518989, 1999988871088034, 1999972797767624, 1999976159215289,
    2000037693367012, 2000003960543329, 2000033582065089, 1999938277423108, 2000003935331359,
    1999996970301645, 2000019531899105, 2000045096285362, 1999961307352393, 1999977061750190,
    1999998794020945, 1999987702360918, 2000045591560343, 2000029269675248, 1999961858521340,
    1999981705794389, 1999991377245207, 1999981739638058, 2000036562649957, 2000049194055250,
    1999984169356456, 1999969977079115, 1999989548658150, 1999970792851921, 1999987073611192,
    2000049805096896, 2000048597336110, 1999995730214372, 1999986407048199, 1999990298835843,
    1999955086193270, 1999948086113873, 2000007066151931, 2000048111098336, 2000031769934551,
    2000025685425551, 2000048247788330, 2000032189367665, 1999970225719086, 1999936807705546,
    1999949495290924, 1999945741427797, 1999912266205650, 1999920327434934, 2000006836487609,
    2000107187508300, 2000125087947275, 1999987419775262, 1999604654959687, 1998886084477652,
    1997945779996245, 1997400418462567, 1998543691584123, 2003294460945960]
private def pvn_m8_r256_4_2_p1 : List ℕ :=
  [2013945636040919, 2032738521582251, 2061261716763359, 2099766585013112, 2146642597846740,
    2198325508296390, 2249753851978365, 2295259364388845, 2329628115223297, 2349053447239614,
    2351771354335919, 2338263762060925, 2311014075724990, 2273900216314106, 2231395297889942,
    2187782245049680, 2146557389834088, 2110114835364064, 2079708080631861, 2055616232151570,
    2037415866802615, 2024270148429886, 2015176412076508, 2009145228279339, 2005308243544533,
    2002966294521115, 2001594969784405, 2000824777518843, 2000409968324700, 2000195790331526,
    2000089799526803, 2000039539212583, 2000016706869578, 2000006772163452, 2000002632604851,
    2000000981156506, 2000000350479768, 2000000119963917, 2000000039338094, 2000000012356528,
    2000000003717898, 2000000001071743, 2000000000296113, 2000000000078473, 2000000000019968,
    2000000000004884, 2000000000001148, 2000000000000257, 2000000000000053, 2000000000000009,
    2000000000000001]
private def pvn_m8_r256_4_2 : List ℕ :=
  pCat pvn_m8_r256_4_2_p0
      pvn_m8_r256_4_2_p1
private def phb_m8_r256_5_p0 : List ℕ :=
  [120316144000000, 169488063544510, 206765598797689, 237812378375000, 264831403700049,
    288957044200879, 310865816142808, 331000218216338, 349668793500000, 367097048512554,
    383455868922308, 398878517365620, 413471368967885, 427320994975855, 440499008289211,
    453065479750000, 465071409542835, 476560555142800, 487570809716609, 498135259340569,
    508283006173550, 518039818066462, 527428647426250, 536470050189680, 545182527500000,
    553582806871059, 561686075474037, 569506175173625, 577055766730294, 584346468941040,
    591388977253943, 598193165451214, 604768173273154, 611122482295755, 617263981937329,
    623200027125000, 628937488878501, 634482798850180, 639841988684347, 645020724916796,
    650024340019476, 654857860100408, 659526029690891, 664033333987412, 668384018862029,
    672582108910159, 676631423767125, 680535592893181, 684298069000000, 687922140268896,
    691410941491783, 694767464249315, 697994566226553, 701094979754325, 704071319653940,
    706926090453884, 709661693039214, 712280430787552, 714784515239602, 717176071346898,
    719457142334915, 721629694215680, 723695619980458, 725656743500000]
private def phb_m8_r256_5_p1 : List ℕ :=
  [727514823157053, 729271555233432, 730928577071745, 732487470029965, 733949762245317,
    735316931222414, 736590406259218, 737771570723164, 738861764188679, 739862284446383,
    740774389393295, 741599298812658, 742338196051178, 742992229600910, 743562514592365,
    744050134204900, 744456141000000, 744781558182539, 745027380794814, 745194576847662,
    745284088392754, 745296832539751, 745233702421808, 745095568112614, 744883277497934,
    744597657104412, 744239512888193, 743809630985737, 743308778429044, 742737703827350,
    742097138017203, 741387794682734, 740610370947764, 739765547941334, 738853991338107,
    737876351875000, 736833265845342, 735725355571741, 734553229858778, 733317484426598,
    732018702326375, 730657454338568, 729234299354868, 727749784744622, 726204446706532,
    724598810606342, 722933391301195, 721208693451316, 719425211819613, 717583431559786,
    715683828493473, 713726869376943, 711713012157835, 709642706222380, 707516392633553,
    705334504360551, 703097466500000, 700805696489238, 698459604312043, 696059592697119,
    693606057309653, 691099386936260, 688539963663566, 685928163050725]
private def phb_m8_r256_5_p2 : List ℕ :=
  [683264354296107, 680548900398402, 677782158312379, 674964479099502, 672096208073627,
    669177684941971, 666209243941535, 663191213971178, 660123918719498, 657007676788683,
    653842801814506, 650629602582590, 647368383141095, 644059442909972, 640703076786894,
    637299575250000, 633849224457572, 630352306344751, 626809098717404, 623219875343242,
    619584906040294, 615904456762831, 612178789684815, 608408163280994, 604592832405686,
    600733048369360, 596829059013084, 592881108780909, 588889438790253, 584854286900380,
    580775887779001, 576654472967090, 572490270941958, 568283507178653, 564034404209726,
    559743181683437, 555410056420434, 551035242468960, 546618951158642, 542161391152896,
    537662768500000, 533123286682868, 528543146667585, 523922546950708, 519261683605413,
    514560750326483, 509819938474206, 505039437117187, 500219433074134, 495360110954628,
    490461653198916, 485524240116757, 480548049925345, 475533258786338, 470480040842023,
    465388568250631, 460259011220840, 455091538045479, 449886315134461, 444643507046967,
    439363276522899, 434045784513621, 428691190212018, 423299651081883]
private def phb_m8_r256_5_p3 : List ℕ :=
  [417871322886644, 412406359717470, 406904914020756, 401367136625000, 395793176767112,
    390183182118144, 384537298808471, 378855671452435, 373138443172463, 367385755622679,
    361597749012014, 355774562126840, 349916332353126, 344023195698139, 338095286811698,
    332132739006989, 326135684280960, 320104253334299, 314038575591010, 307938779217597,
    301804991141859, 295637337071318, 289435941511279, 283200927782535, 276932418038719,
    270630533283331, 264295393386419, 257927117100948, 251525822078850, 245091624886770,
    238624641021504, 232124984925156, 225592770000000, 219028108623065, 212431112160451,
    205801890981372, 199140554471943, 192447211048714, 185721968171951, 178964932358681,
    172176209195489, 165355903351095, 158504118588698, 151620957778097, 144706522907601,
    137760915095721, 130784234602659, 123776580841596, 116738052389773, 109668746999389,
    102568761608302, 95438192350549, 88277134566683, 81085682813927, 73863930876165,
    66611971773755, 59329897773176, 52017800396515, 44675770430794, 37303897937137,
    29902272259786, 22470982034974, 15010115199638, 7519759000000]
private def phb_m8_r256_5 : List ℕ :=
  pCat phb_m8_r256_5_p0
    (pCat phb_m8_r256_5_p1
    (pCat phb_m8_r256_5_p2
      phb_m8_r256_5_p3))
private def pvn_m8_r256_5_0_p0 : List ℕ :=
  [2000049693910567, 2000035207361314, 2000014131631382, 1999962250722167, 2000009942212273,
    1999971848075905, 2000028574518989, 2000011128911966, 1999972797767624, 1999976159215289,
    1999962306632988, 2000003960543329, 1999966417934911, 1999938277423108, 1999996064668641,
    2000003029698355, 1999980468100895, 1999954903714638, 1999961307352393, 1999977061750190,
    1999998794020945, 2000012297639082, 1999954408439657, 2000029269675248, 2000038141478660,
    1999981705794389, 2000008622754793, 2000018260361942, 1999963437350043, 1999950805944750,
    2000015830643544, 1999969977079115, 1999989548658150, 2000029207148079, 1999987073611192,
    1999950194903104, 1999951402663890, 1999995730214372, 1999986407048199, 2000009701164157,
    2000044913806730, 2000051913886127, 2000007066151931, 2000048111098336, 2000031769934551,
    2000025685425551, 1999951752211670, 2000032189367665, 2000029774280914, 2000063192294454,
    2000050504709076, 2000054258572203, 2000087733794350, 2000079672565066, 1999993163512391,
    1999892812491700, 1999874912052725, 2000012580224738, 1999604654959687, 2001113915522348,
    2002054220003755, 2002599581537433, 2001456308415877, 2003294460945960]
private def pvn_m8_r256_5_0_p1 : List ℕ :=
  [2013945636040919, 2032738521582251, 2061261716763359, 2099766585013112, 2146642597846740,
    2198325508296390, 2249753851978365, 2295259364388845, 2329628115223297, 2349053447239614,
    2351771354335919, 2338263762060925, 2311014075724990, 2273900216314106, 2231395297889942,
    2187782245049680, 2146557389834088, 2110114835364064, 2079708080631861, 2055616232151570,
    2037415866802615, 2024270148429886, 2015176412076508, 2009145228279339, 2005308243544533,
    2002966294521115, 1998405030215595, 2000824777518843, 2000409968324700, 2000195790331526,
    2000089799526803, 2000039539212583, 2000016706869578, 2000006772163452, 1999997367395149,
    1999999018843494, 1999999649520232, 2000000119963917, 2000000039338094, 2000000012356528,
    2000000003717898, 1999999998928257, 1999999999703887, 1999999999921527, 2000000000019968,
    2000000000004884, 1999999999998852, 2000000000000257, 2000000000000053, 1999999999999991,
    2000000000000001]
private def pvn_m8_r256_5_0 : List ℕ :=
  pCat pvn_m8_r256_5_0_p0
      pvn_m8_r256_5_0_p1
private def pvn_m8_r256_5_1_p0 : List ℕ :=
  [2000026644749838, 2000034951017907, 1999998044306849, 1999974557927753, 2000006187886678,
    2000031119355191, 2000003797686086, 2000030816305160, 2000027730130656, 2000022637785538,
    2000038485650981, 2000000729507221, 2000026375548338, 2000036486829593, 1999999280359891,
    1999966531821861, 1999956655424637, 2000022156232846, 1999998278873151, 2000000398744069,
    2000015027704486, 2000043391202048, 1999943656759753, 1999985617264684, 2000001641388665,
    2000053297140407, 1999980862210871, 1999962823235662, 1999960539737249, 2000017749437268,
    1999905777804422, 2000077729536122, 1999838029428717, 2000200182651711, 1999778288687113,
    2000110880034647, 1999940393297614, 1999902253937560, 2000189476244846, 1999686393904418,
    2000174750417480, 1999979218594827, 1999819729476567, 2000173142216762, 1999880417060144,
    1999961359354897, 2000148355869652, 1999900310682611, 2000033617153765, 2000111993765730,
    1999876980800578, 2000015186521440, 2000074444514264, 1999816562374575, 1999967177987609,
    2000294202526512, 1999860042830750, 1999790642429537, 1999998279434578, 2000591062185501,
    1999343314234233, 2000114193242722, 1999542060280177, 2001157709549646]
private def pvn_m8_r256_5_1_p1 : List ℕ :=
  [1999179015671611, 1999804899249145, 2000006578987440, 2000352171167947, 2000911129927768,
    1998977020276598, 1999404519076094, 2000515934020910, 2000408357516171, 2000878072045099,
    1999674357453285, 1998335960025324, 1999702021401464, 2000909930408838, 2001059124165842,
    2001386847341631, 2000244333151786, 1998032613952358, 1997755932156571, 1999083452690359,
    2000308654100335, 2002085989196738, 2004145871387654, 2003953195004058, 2000749623985683,
    1996251495477854, 1991588009319935, 1987573238565655, 1987267666850473, 1995106051021862,
    2013779198602720, 2043600042760647, 2083944856886926, 2133303437442338, 2187908385067814,
    2241696616287114, 2288306984587356, 2323067031988285, 2343410842152688, 2348326532830656,
    2338097801354771, 2314541497765783, 2281030608161091, 2241839253604296, 2201107176562227,
    2162038612334890, 2126657826286643, 2096002078115040, 2070445785318088, 2049943240062966,
    2034153983037385, 2022513998843034, 2014312849984714, 2008789894587374, 2005228337631782,
    2003021776835077, 2001702633116290, 2000937961308266, 2000506156939929, 2000267734276476,
    2000138727638168, 2000070296371438, 2000034754894053, 2000016723962232]
private def pvn_m8_r256_5_1_p2 : List ℕ :=
  [2000007814659387, 2000003539285041, 2000001551558868, 2000000657832756, 2000000269666750,
    2000000106899753, 2000000041003145, 2000000015232231, 2000000005487473, 2000000001920093,
    2000000000653711, 2000000000216968, 2000000000070339, 2000000000022313, 2000000000006935,
    2000000000002111, 2000000000000628, 2000000000000181, 2000000000000050, 2000000000000011,
    2000000000000001]
private def pvn_m8_r256_5_1 : List ℕ :=
  pCat pvn_m8_r256_5_1_p0
    (pCat pvn_m8_r256_5_1_p1
      pvn_m8_r256_5_1_p2)
private def pvn_m8_r256_5_2_p0 : List ℕ :=
  [1999994104590625, 2000004033613215, 2000004962228172, 1999981968071500, 2000001449305555,
    2000051525625427, 2000013758081526, 2000037519680605, 1999996341997145, 2000027740637624,
    1999967577332275, 2000020253254256, 1999960368777751, 2000044857154268, 1999943487310156,
    2000123549354200, 1999823143194502, 2000166352041064, 1999907709297484, 2000081031334222,
    2000108284660505, 1999786129981635, 2000229384520498, 1999900115672132, 2000018718065611,
    2000189441747964, 1999807406130199, 2000121055434933, 2000124389170672, 1999826633100221,
    2000081540607460, 2000004122209620, 1999809187055077, 2000170075716299, 2000012778427232,
    1999951446887531, 1999911543689991, 2000302638068441, 1999552102022086, 2000464400532196,
    1999521995941060, 2000519197288464, 1999451933895750, 2000560658346666, 1999678488282661,
    1999877743890815, 2000416313534609, 1999511189404346, 2000276438488819, 1999855512585997,
    1999956690366434, 2000254026916014, 1999482034438412, 2000337037794350, 2000233913139789,
    1999367210709230, 2000243374416510, 2000229689748096, 1999728712779457, 2000070833402247,
    1999782807390384, 1999997070949413, 2000527598069420, 1999587204122508]
private def pvn_m8_r256_5_2_p1 : List ℕ :=
  [1999408080770363, 2000573422140906, 2000339831277010, 1999542179393789, 1999881989694993,
    2000113516565713, 2000090203762923, 2000365618033154, 1999879690702868, 1999234122466186,
    2000075534380369, 2000912868654795, 2000049720304237, 1999208465843567, 1999744493461282,
    2000347922612668, 2000332601368088, 2000283686209744, 1999921715654743, 1999180079005227,
    1999373334923481, 2000658259481081, 2001122233166682, 2000028371592865, 1999034963704138,
    1999280476223481, 1999997484792198, 2000458965182740, 2000836858533780, 2000894413384022,
    1999990780337253, 1998654510874497, 1998396664614935, 1999635337228774, 2001127909275370,
    2001706062058991, 2001431449750481, 2000741487751414, 1999551212461134, 1997875736544852,
    1996673650110120, 1997243119898373, 1999849205086063, 2003378906604877, 2006261127269189,
    2007304393405861, 2005664028473469, 2000642592404115, 1992221987543439, 1982048284235961,
    1973771642716260, 1972174119564426, 1981614606870234, 2004737030018864, 2041904341923618,
    2091185177206239, 2148579618974635, 2208442864692866, 2264261869807615, 2309798751033785,
    2340309081550641, 2353398595606096, 2349230073527126, 2330099706988945]
private def pvn_m8_r256_5_2_p2 : List ℕ :=
  [2299645072235739, 2262003118822790, 2221137943001698, 2180413758008491, 2142386776239103,
    2108754758839380, 2080411007546538, 2057567140976832, 2039918085718804, 2026823273800041,
    2017477846520595, 2011052385641063, 2006789378849073, 2004055631704282, 2002358301821745,
    2001336268088241, 2000738481965842, 2000398358009902, 2000209870371020, 2000108029609878,
    2000054341654533, 2000026713297415, 2000012831235363, 2000006020741467, 2000002758904298,
    2000001234185233, 2000000538808849, 2000000229491347, 2000000095337226, 2000000038622150,
    2000000015255604, 2000000005875044, 2000000002205861, 2000000000807519, 2000000000288254,
    2000000000100345, 2000000000034070, 2000000000011280, 2000000000003639, 2000000000001143,
    2000000000000346, 2000000000000100, 2000000000000027, 2000000000000005]
private def pvn_m8_r256_5_2 : List ℕ :=
  pCat pvn_m8_r256_5_2_p0
    (pCat pvn_m8_r256_5_2_p1
      pvn_m8_r256_5_2_p2)
private def pvn_m8_r256_5_3_p0 : List ℕ :=
  [1999983955596571, 2000041451327314, 1999945329656406, 2000049321627785, 1999895017027083,
    2000136993155727, 1999874427892289, 2000099158647175, 2000032377355252, 1999813398460991,
    2000194606909586, 1999911547515999, 1999881817809873, 2000214293618633, 1999897553843394,
    1999952014544232, 2000179692804365, 1999979426960462, 1999814406267035, 2000374526779472,
    1999727904528502, 2000229037841314, 1999651589321240, 2000560275637443, 1999284290804360,
    2000573805935244, 1999824047645626, 1999918286036285, 2000166327931787, 1999690107764912,
    2000392863566905, 1999675420922611, 2000061594881062, 2000388903037907, 1999491909690612,
    2000229966394303, 2000187469805316, 1999676445017656, 2000300720524876, 1999930265409920,
    1999830426832819, 2000310033020052, 1999815759894629, 2000034266626797, 2000371873326576,
    1999645911730002, 1999953726411797, 2000446524628757, 1999683595959209, 1999768204297448,
    2000386711553560, 1999919888224359, 1999800377648360, 2000203509977408, 1999939497794083,
    1999935890584825, 2000218982276356, 1999776665498156, 1999776397988607, 2000468467546186,
    2000100330264318, 1999431919101935, 2000071740100516, 2000547027945732]
private def pvn_m8_r256_5_3_p1 : List ℕ :=
  [1999851935807044, 1999602346064034, 2000104795917596, 2000151400032369, 1999982598296391,
    2000053317293667, 1999819944123588, 1999680727889011, 2000285061634841, 2000493023599613,
    1999641695446687, 1999345535664057, 2000262063696569, 2000645209367998, 1999853348222918,
    1999428823419746, 1999938485502686, 2000296484134982, 2000143260847123, 1999998251127852,
    1999819414756576, 1999567431394046, 1999871728127868, 2000603188243673, 2000530433002557,
    1999529070022285, 1999155190587817, 2000065749077107, 2000865220640475, 2000429312656596,
    1999549499166492, 1999380198331245, 1999810384821445, 2000203431091772, 2000446380165272,
    2000503318883674, 2000040271304674, 1999246954750560, 1999105705513324, 2000053960968653,
    2001076132790015, 2000923872634792, 1999774927887080, 1998920273546888, 1999092576052735,
    1999851282916580, 2000509058495991, 2000888288116880, 2000976905402296, 2000507498482330,
    1999395704344676, 1998312828850051, 1998274565735752, 1999571517206695, 2001378395368991,
    2002508871033784, 2002368095888553, 2001108793951931, 1999160946378497, 1996987154691478,
    1995332159383860, 1995355229691507, 1998066546670230, 2003344114878149]
private def pvn_m8_r256_5_3_p2 : List ℕ :=
  [2009407348860132, 2013308829970498, 2012194037740486, 2004602418908059, 1991248089654148,
    1975152951411516, 1961238110213514, 1955444350574523, 1963417494917718, 1988957183890886,
    2032682903967684, 2091451909310400, 2158830866318146, 2226494827640421, 2286063312030651,
    2330775543120228, 2356563982651909, 2362372183147771, 2349820475357540, 2322461388499895,
    2284884045029057, 2241871152123921, 2197734775534658, 2155887459901091, 2118652071147497,
    2087276098579161, 2062092693989399, 2042761588946222, 2028527691450289, 2018450414746699,
    2011577053722418, 2007052864281926, 2004174705744737, 2002402624315864, 2001345353835781,
    2000733411526762, 2000389460547631, 2000201556969689, 2000101702631991, 2000050051132772,
    2000024030136407, 2000011257442939, 2000005146535421, 2000002296179316, 2000000999801407,
    2000000424836913, 2000000176157490, 2000000071270642, 2000000028132304, 2000000010832699,
    2000000004068699, 2000000001490438, 2000000000532432, 2000000000185462, 2000000000062981,
    2000000000020846, 2000000000006721, 2000000000002107, 2000000000000639, 2000000000000185,
    2000000000000049, 2000000000000010, 2000000000000001]
private def pvn_m8_r256_5_3 : List ℕ :=
  pCat pvn_m8_r256_5_3_p0
    (pCat pvn_m8_r256_5_3_p1
      pvn_m8_r256_5_3_p2)
private def pvn_m8_r256_5_4_p0 : List ℕ :=
  [1999833596053998, 2000106137056426, 2000025817771697, 1999833783075838, 2000102592740438,
    2000154305717507, 1999771483147735, 2000064145125406, 2000012875828049, 2000255164862615,
    1999361922533418, 2000626739874093, 1999574948618353, 2000339976878115, 1999679137605835,
    2000088662050626, 2000401230441373, 1999396963116709, 2000291507788254, 2000169026014849,
    1999653103304769, 2000237719898001, 1999838928295911, 1999971165351690, 2000306565838248,
    1999618392800644, 2000051129166233, 2000420961825101, 1999606284262468, 1999939826194666,
    2000409841441477, 1999795010561979, 1999957689525905, 2000271223380946, 1999799310902158,
    1999978969291299, 2000213926928700, 1999743324959799, 1999994126725760, 2000371256306509,
    1999777604189210, 1999769378100819, 2000358612386415, 1999954310858289, 1999632508240816,
    2000254762643252, 2000235432012848, 1999681875589973, 1999956748448343, 2000243599877600,
    1999911824479866, 1999969462734636, 2000185562652486, 1999858930424123, 1999873200182054,
    2000310234728070, 2000014108849932, 1999606276843069, 2000159273469904, 2000479612463935,
    1999807793976152, 1999634243299169, 2000305927489981, 2000330025477580]
private def pvn_m8_r256_5_4_p1 : List ℕ :=
  [1999738700464575, 1999772294778689, 2000144960704195, 2000077348234811, 1999989681062428,
    2000083097301390, 1999877827960576, 1999759350092558, 2000231277037005, 2000393917370537,
    1999711434895393, 1999459137008021, 2000243690911998, 2000614643233972, 1999874397502486,
    1999419974581375, 1999999123976097, 2000467498187999, 2000133351330664, 1999761604800831,
    1999825343633856, 1999947333591359, 2000047317585452, 2000250931825598, 2000144954894732,
    1999616986934774, 1999539953364513, 2000274311305770, 2000679053746418, 1999961923972875,
    1999208819305083, 1999640882138992, 2000572862539633, 2000599472798081, 1999817829868812,
    1999409402102023, 1999734091178407, 2000162574978834, 2000299775251604, 2000235088483557,
    1999957747874648, 1999521665965903, 1999471725835621, 2000158621699871, 2000863674049766,
    2000559663256370, 1999473668572848, 1998961237529432, 1999680390437151, 2000720050171301,
    2000881979686485, 2000158439680709, 1999454857385325, 1999336364040837, 1999647300767074,
    2000103030511013, 2000585363324384, 2000825214794930, 2000402821598280, 1999385638960429,
    1998618658682218, 1998957588094039, 2000264018674795, 2001451558500758]
private def pvn_m8_r256_5_4_p2 : List ℕ :=
  [2001563561630782, 2000611264827448, 1999336624000506, 1998430030431771, 1998184929713615,
    1998726370020308, 2000144157740787, 2002152704276351, 2003755596193722, 2003597515795000,
    2000961556989369, 1996602862849289, 1992660190283931, 1991633601718869, 1995067931388614,
    2002632408377003, 2011926324363357, 2019026761250700, 2019683637696610, 2010964872988456,
    1992901648247351, 1969432786479314, 1948013572776103, 1937757310264048, 1946675167247670,
    1979046990679007, 2033914540884186, 2105189867288984, 2183217084759126, 2257142040042663,
    2317297941264363, 2356974515775802, 2373255321183170, 2366926662032637, 2341685583708191,
    2302975591760334, 2256774171533876, 2208581253919043, 2162749790894051, 2122190797932157,
    2088399483125681, 2061699537875368, 2041590733152961, 2027102316699060, 2017087821914595,
    2010432359085555, 2006171817050945, 2003540575619543, 2001970779806472, 2001065016881519,
    2000559058451840, 2000285197311666, 2000141449949579, 2000068231866527, 2000032020857279,
    2000014623476166, 2000006500222003, 2000002812754534, 2000001184969823, 2000000486050542,
    2000000194117200, 2000000075483063, 2000000028577151, 2000000010532743]
private def pvn_m8_r256_5_4_p3 : List ℕ :=
  [2000000003778993, 2000000001319690, 2000000000448505, 2000000000148315, 2000000000047710,
    2000000000014920, 2000000000004531, 2000000000001332, 2000000000000375, 2000000000000099,
    2000000000000023, 2000000000000003]
private def pvn_m8_r256_5_4 : List ℕ :=
  pCat pvn_m8_r256_5_4_p0
    (pCat pvn_m8_r256_5_4_p1
    (pCat pvn_m8_r256_5_4_p2
      pvn_m8_r256_5_4_p3))
private def phb_m8_r256_6_p0 : List ℕ :=
  [107984852051329, 152244880471508, 185886890642130, 213980456495177, 238495728721773,
    260446302955955, 280436156936764, 298860012115253, 315992868489967, 332035549969154,
    347140112062582, 361425034904775, 374984815483902, 387896294654188, 400222983579984,
    412018112978100, 423326838218945, 434187869740505, 444634702067858, 454696556130419,
    464399112717024, 473765091084550, 482814710952070, 491566065424972, 500035425013280,
    508237487721137, 516185586479246, 523891862506560, 531367411214679, 538622405801139,
    545666202574004, 552507431211075, 559154072512825, 565613525709098, 571892666989660,
    577997900621600, 583935203772867, 589710165966541, 595328023933817, 600793692506941,
    606111792090139, 611286673162125, 616322438194255, 621222961310904, 625991905970869,
    630632740908732, 635148754541669, 639543068019077, 643818647068574, 647978312771803,
    652024751386244, 655960523314628, 659788071310938, 663509728001181, 667127722787829,
    670644188198717, 674061165734252, 677380611260663, 680604399991773, 683734331097089,
    686772131970006, 689719462186317, 692577917180109, 695349031661357]
private def phb_m8_r256_6_p1 : List ℕ :=
  [698034282797068, 700635093175700, 703152833572609, 705588825532625, 707944343784294,
    710220618498980, 712418837406828, 714540147780470, 716585658296397, 718556440783061,
    720453531863955, 722277934503228, 724030619460752, 725712526662967, 727324566495332,
    728867621021702, 730342545135553, 731750167647564, 733091292313725, 734366698807807,
    735577143641737, 736723361037151, 737806063751164, 738825943859146, 739783673497111,
    740679905566126, 741515274400968, 742290396405114, 743005870653991, 743662279468261,
    744260188958848, 744800149545215, 745282696448376, 745708350159977, 746077616888701,
    746390988985182, 746648945346518, 746851951801415, 747000461476910, 747094915147571,
    747135741568019, 747123357789541, 747058169461537, 746940571118476, 746770946453011,
    746549668575846, 746277100262916, 745953594190400, 745579493158072, 745155130301422,
    744680829293001, 744156904533369, 743583661332027, 742961396078673, 742290396405114,
    741570941338121, 740803301443503, 739987738961678, 739124507934936, 738213854326659,
    737256016132651, 736251223484789, 735199698747147, 734101656604736]
private def phb_m8_r256_6_p2 : List ℕ :=
  [732957304145001, 731766840932173, 730530459074600, 729248343285109, 727920670934502,
    726547612098211, 725129329596175, 723665979025947, 722157708789054, 720604660110598,
    719006967052083, 717364756517436, 715678148252170, 713947254835630, 712172181666232,
    710353026939614, 708489881619572, 706582829401664, 704631946669324, 702637302442322,
    700598958317396, 698516968400827, 696391379232754, 694222229702967, 692009550957900,
    689753366298547, 687453691068944, 685110532534905, 682723889752587, 680293753426512,
    677820105756563, 675302920273498, 672742161662436, 670137785573780, 667489738420937,
    664797957164206, 662062369080114, 659282891515436, 656459431625090, 653591886093003,
    650680140835007, 647724070682718, 644723539047303, 641678397561909, 638588485701476,
    635453630378505, 632273645513288, 629048331576929, 625777475105390, 622460848182624,
    619098207890696, 615689295724626, 612233836969476, 608731540036989, 605182095758862,
    601585176633459, 597940436022484, 594247507293825, 590506002906405, 586715513432509,
    582875606512602, 578985825737190, 575045689449705, 571054689463853]
private def phb_m8_r256_6_p3 : List ℕ :=
  [567012289688133, 562917924649537, 558770997907582, 554570880348896, 550316908351522,
    546008381806915, 541644561986298, 537224669236469, 532747880488521, 528213326560921,
    523620089236223, 518967198088175, 514253627033070, 509478290575927, 504640039718298,
    499737657490116, 494769854063006, 489735261396639, 484632427362963, 479459809285271,
    474215766819891, 468898554097509, 463506311028480, 458037053661552, 452488663467716,
    446858875399889, 441145264553988, 435345231226842, 429455984130130, 423474521475585,
    417397609593340, 411221758679967, 404943195192484, 398557830305320, 392061223723659,
    385448541991815, 378714510240026, 371853356064946, 364858743921218, 357723697990851,
    350440510961698, 343000635441390, 335394553795147, 327611620933583, 319639872856847,
    311465791386422, 303074012187958, 294446958449295, 285564375708638, 276402733174015,
    266934441534876, 257126813516535, 246940655627718, 236328317466332, 225230919222736,
    213574290248361, 201262801135418, 188169577807254, 174120108459183, 158862807588176,
    142011050443024, 122913232201124, 100297429091066, 70876536211016]
private def phb_m8_r256_6 : List ℕ :=
  pCat phb_m8_r256_6_p0
    (pCat phb_m8_r256_6_p1
    (pCat phb_m8_r256_6_p2
      phb_m8_r256_6_p3))
private def pvn_m8_r256_6_0_p0 : List ℕ :=
  [2000166403946002, 2000106137056426, 2000025817771697, 2000166216924162, 2000102592740438,
    1999845694282493, 1999771483147735, 2000064145125406, 1999987124171951, 2000255164862615,
    2000638077466582, 2000626739874093, 2000425051381647, 2000339976878115, 1999679137605835,
    1999911337949374, 2000401230441373, 1999396963116709, 2000291507788254, 2000169026014849,
    2000346896695231, 2000237719898001, 1999838928295911, 1999971165351690, 2000306565838248,
    2000381607199356, 2000051129166233, 1999579038174899, 1999606284262468, 1999939826194666,
    1999590158558523, 2000204989438021, 1999957689525905, 1999728776619054, 2000200689097842,
    2000021030708701, 2000213926928700, 1999743324959799, 1999994126725760, 2000371256306509,
    2000222395810790, 2000230621899181, 2000358612386415, 2000045689141711, 2000367491759184,
    2000254762643252, 2000235432012848, 2000318124410027, 2000043251551657, 2000243599877600,
    2000088175520134, 2000030537265364, 1999814437347514, 2000141069575877, 1999873200182054,
    2000310234728070, 1999985891150068, 1999606276843069, 1999840726530096, 1999520387536065,
    1999807793976152, 1999634243299169, 2000305927489981, 2000330025477580]
private def pvn_m8_r256_6_0_p1 : List ℕ :=
  [2000261299535425, 1999772294778689, 1999855039295805, 2000077348234811, 1999989681062428,
    1999916902698610, 2000122172039424, 1999759350092558, 2000231277037005, 2000393917370537,
    1999711434895393, 2000540862991979, 2000243690911998, 2000614643233972, 1999874397502486,
    1999419974581375, 1999999123976097, 1999532501812001, 1999866648669336, 1999761604800831,
    1999825343633856, 2000052666408641, 2000047317585452, 2000250931825598, 2000144954894732,
    1999616986934774, 1999539953364513, 1999725688694230, 1999320946253582, 1999961923972875,
    1999208819305083, 2000359117861008, 2000572862539633, 2000599472798081, 1999817829868812,
    1999409402102023, 1999734091178407, 1999837425021166, 2000299775251604, 1999764911516443,
    1999957747874648, 1999521665965903, 1999471725835621, 2000158621699871, 2000863674049766,
    2000559663256370, 1999473668572848, 1998961237529432, 1999680390437151, 2000720050171301,
    2000881979686485, 2000158439680709, 2000545142614675, 1999336364040837, 1999647300767074,
    2000103030511013, 2000585363324384, 2000825214794930, 1999597178401720, 2000614361039571,
    2001381341317782, 2001042411905961, 2000264018674795, 2001451558500758]
private def pvn_m8_r256_6_0_p2 : List ℕ :=
  [2001563561630782, 2000611264827448, 2000663375999494, 2001569969568229, 2001815070286385,
    2001273629979692, 2000144157740787, 2002152704276351, 2003755596193722, 2003597515795000,
    2000961556989369, 2003397137150711, 2007339809716069, 2008366398281131, 2004932068611386,
    2002632408377003, 2011926324363357, 2019026761250700, 2019683637696610, 2010964872988456,
    2007098351752649, 2030567213520686, 2051986427223897, 2062242689735952, 2053324832752330,
    2020953009320993, 2033914540884186, 2105189867288984, 2183217084759126, 2257142040042663,
    2317297941264363, 2356974515775802, 2373255321183170, 2366926662032637, 2341685583708191,
    2302975591760334, 2256774171533876, 2208581253919043, 2162749790894051, 2122190797932157,
    2088399483125681, 2061699537875368, 2041590733152961, 2027102316699060, 2017087821914595,
    2010432359085555, 2006171817050945, 2003540575619543, 2001970779806472, 2001065016881519,
    2000559058451840, 1999714802688334, 1999858550050421, 1999931768133473, 1999967979142721,
    1999985376523834, 2000006500222003, 2000002812754534, 2000001184969823, 2000000486050542,
    1999999805882800, 1999999924516937, 1999999971422849, 2000000010532743]
private def pvn_m8_r256_6_0_p3 : List ℕ :=
  [2000000003778993, 2000000001319690, 2000000000448505, 1999999999851685, 2000000000047710,
    1999999999985080, 1999999999995469, 1999999999998668, 2000000000000375, 1999999999999901,
    2000000000000023, 2000000000000003]
private def pvn_m8_r256_6_0 : List ℕ :=
  pCat pvn_m8_r256_6_0_p0
    (pCat pvn_m8_r256_6_0_p1
    (pCat pvn_m8_r256_6_0_p2
      pvn_m8_r256_6_0_p3))
private def pvn_m8_r256_6_1_p0 : List ℕ :=
  [1999956781247331, 2000063409685321, 1999989839455147, 2000116636162477, 2000172253946370,
    2000058289949356, 2000111615169575, 1999559214189127, 2000508274477596, 2000146571522721,
    1999784550271770, 2000339483910774, 2000202097845034, 1999816416828627, 1999865219453745,
    2000199635846571, 1999825955013928, 1999861275628046, 1999698961931704, 1999709334021051,
    2000495364324024, 2000192616285339, 2000530794848240, 2000601534166816, 2000188641124005,
    2000247938777189, 2000566999800760, 2000250599592304, 2000059259452097, 1999719120982100,
    1999624042711531, 2000269777048552, 1999995235161525, 2000253189594832, 2000206269302289,
    2000138703697168, 1999726884650030, 1999967026274539, 2000290543485378, 2000232448153155,
    2000609848704293, 1999828373668240, 2000135450229323, 1999967249109604, 1999926686001501,
    1999855332840818, 1999833136812371, 1999685224619493, 1999768882244677, 1999937348529660,
    2000053849111938, 1999993591824091, 1999947001981704, 2000073115832429, 1999605693548643,
    2000290626364240, 1999827199570946, 2000170228547303, 2000288645811321, 1999642760119836,
    2000591421084004, 2000237421451393, 2000095307828774, 2000186832146634]
private def pvn_m8_r256_6_1_p1 : List ℕ :=
  [2000113767929258, 2000486666297659, 2000226864665977, 2000258138586428, 2000258166529692,
    2000263472574426, 1999875903851809, 2000397917471538, 1999477772438390, 2000227940286484,
    2000147844385494, 2000488721044908, 2000272965283653, 1999405393118105, 1999857406750486,
    1999695687187487, 1999815763781159, 1999535896551358, 1999995599762470, 2000025266535723,
    2000172286530114, 2000121540696266, 1999792532617239, 1999979481545437, 2000103752387744,
    1999986100583433, 2000185750537115, 1999842225222335, 1999863907681261, 1999568755080760,
    2000300040462992, 2000148340382850, 2000504234465913, 2000161800848610, 1999926099800777,
    2000868381077145, 1999952570546197, 2000061683070629, 1999423357485483, 1999703436028553,
    2000078566722532, 1999769179885147, 1999445419615564, 2000021777089152, 2000224971419876,
    2000311691262244, 2000132054702180, 2000255231734181, 1999388724713811, 1999324189359349,
    1998496710852382, 2000416935061808, 2000727430203648, 1999877628535049, 1999448566804006,
    1999830880124775, 2000372137322465, 1999485774202805, 2001338535389824, 1999779521870211,
    1999069047261785, 1999174237295842, 1999058241812377, 2002273623633289]
private def pvn_m8_r256_6_1_p2 : List ℕ :=
  [1999234375381485, 1999959029870712, 2000250103903468, 1998438460730665, 2001830950851134,
    1997816962838454, 2000284660828851, 2003558789876663, 1996294454278489, 2001635614786750,
    2000404118732462, 1998600957988804, 2003641590713717, 1996628424521602, 1997255874167112,
    2006500861057840, 2000293440646952, 1995091275293782, 2001962105933331, 2003448735815702,
    2001042395618820, 2001694405387911, 1998232096588439, 1996783923008155, 2006285917364370,
    2009835343796539, 1995735765807399, 1987023100915809, 2002404088306262, 2019650772922128,
    2011043440797584, 1987464456357907, 1983281883539161, 2005650168429062, 2028207754393709,
    2024407123198368, 1999436697711608, 1980695744329737, 1987760513706148, 2016677060934518,
    2045588123611575, 2054563653679440, 2039722822498996, 2012404018963704, 1991399591568432,
    1993371831159023, 2025449532282636, 2084506311339704, 2160396104790639, 2239300157154172,
    2307581320574212, 2355444470841525, 2378230415522665, 2375798682217902, 2351677804361270,
    2312015639346016, 2263876499563269, 2213549130458565, 2165729473827499, 2123501875327463,
    2088533879313493, 2061233675355724, 2040995283705806, 2026610619950802]
private def pvn_m8_r256_6_1_p3 : List ℕ :=
  [2016717197800111, 2010104448483900, 2005823488150805, 2003166126246006, 2001605505277101,
    2000750189476982, 2000318383056742, 2000120222545015, 2000038913521549, 2000009860146151,
    2000001305268400, 1999999555174022, 1999999551034561, 1999999775016664, 1999999916104795,
    1999999975808192, 1999999995342858, 2000000000126816, 2000000000708431, 2000000000471942,
    2000000000235335, 2000000000102869, 2000000000041342, 2000000000015518, 2000000000005456,
    2000000000001794, 2000000000000549, 2000000000000155, 2000000000000039, 2000000000000007]
private def pvn_m8_r256_6_1 : List ℕ :=
  pCat pvn_m8_r256_6_1_p0
    (pCat pvn_m8_r256_6_1_p1
    (pCat pvn_m8_r256_6_1_p2
      pvn_m8_r256_6_1_p3))
private def pvn_m8_r256_6_2_p0 : List ℕ :=
  [2000038377754321, 1999699693082193, 2000235940262972, 2000034811690255, 1999686668432189,
    2000174918731176, 2000197932426632, 1999896239265967, 1999710296572774, 1999898452233867,
    2000647890275054, 2000089827389894, 1999838140301922, 2000082080640136, 2000031418528705,
    1999975767220044, 2000123845406085, 2000090022877704, 1999602766069547, 2000313812190246,
    2000247408949202, 2000085894737874, 2000117305959491, 1999912566492646, 2000171112488758,
    1999863496293829, 2000339400987576, 1999887433202212, 2000097112608644, 2000130961382142,
    1999580456876028, 1999501701420711, 1999821252571484, 2000061531702353, 2000112571769354,
    2000319789300858, 1999930002491486, 2000372883377248, 2000218540754151, 2000513432332932,
    2000530802696000, 2000220367728473, 2000856465448063, 1999940400262409, 1999858538171013,
    2000037208576211, 1999521395612514, 2000319800936013, 2000175979280818, 2000187798603080,
    2000026119092053, 2000154782040670, 1999513909261423, 2000317969171127, 1999931980984777,
    2000217940613778, 2000254627167911, 1999943005950241, 2000606175242041, 1999859000579397,
    2000234673616707, 2000241050441647, 2000101090647238, 1999783911061626]
private def pvn_m8_r256_6_2_p1 : List ℕ :=
  [1999672963393375, 1999822852221131, 1999938592071138, 1999919446036088, 1999855465784576,
    1999833364987089, 2000118679221742, 1999694082448050, 2000245537084514, 1999853046986063,
    1999809083944348, 1999852620050810, 2000146334324365, 2000300474238047, 1999671951159684,
    2000361584541375, 1999851781166181, 2000593410909118, 2000129497159614, 1999782175220377,
    2000217542049722, 2000350340685391, 2000464437411210, 2000616885632795, 1999915357930602,
    2000281819842595, 1999913398232339, 2000149871516894, 1999800890013108, 2000503637075289,
    1999974445482063, 2000429305770572, 2000296624295957, 1999804087018592, 2000285203532786,
    1999100875337360, 1999898581915689, 1999751049255571, 2000315322110843, 1999811254823465,
    1999255114829683, 2000500636203478, 1999389193706877, 2001185339532167, 1999287964240362,
    1999541210110278, 2001488094074668, 1998601843504896, 2000583147419482, 1999612108982153,
    1999411196543797, 2001464896914345, 1997543056184263, 2002676941254843, 2000161806094765,
    1998390287824365, 2002627231566306, 1998104940082005, 2001233651122634, 2001303911126038,
    1996659272670000, 2001745776589608, 1999271913914945, 1997438686317769]
private def pvn_m8_r256_6_2_p2 : List ℕ :=
  [2003802950126219, 2000118398185738, 1997891834022749, 2001549150282640, 1998370598614468,
    1999412466671969, 2002820324368929, 1997361852072915, 1997861739744932, 2003165212139451,
    1998854441491999, 1997046568268986, 2003773365704106, 2001762200495776, 1996037720446732,
    1999259070882650, 2002359334350836, 1999494248260803, 1999154153074950, 2000524934882756,
    1998878521092530, 2000226528458964, 2002718134779707, 1998186682609194, 1995068462521560,
    2002412827160889, 2006958766253708, 1997675415835120, 1991120331284912, 2001729913032951,
    2011248479744523, 2000805159388622, 1987354174803247, 1994834262506573, 2012094568238503,
    2010909208670778, 1992076644646404, 1984678989252262, 2001102290666366, 2018065864127504,
    2011190038100431, 1989664016290747, 1982287638069177, 1998803339437679, 2018880021377874,
    2018353382794947, 1997508310377503, 1979564630126132, 1984283841511468, 2007493346915873,
    2026895089410498, 2024603533067781, 2002679371061478, 1979696017392402, 1974889663592514,
    1993870399204832, 2025459706803551, 2050092720578151, 2052701857233863, 2031378260205516,
    1997625163669690, 1970030218197314, 1965954282096401, 1995018188250417]
private def pvn_m8_r256_6_2_p3 : List ℕ :=
  [2056242506801942, 2139141545019749, 2227804280413192, 2306037201290420, 2361557739157792,
    2388112683126052, 2385540890650991, 2358458448255783, 2314310942109789, 2261358725149774,
    2207004354396501, 2156738470622933, 2113794575881891, 2079389438772814, 2053286455216708,
    2034414023928214, 2021366535623069, 2012731689565341, 2007265228752269, 2003960862886149,
    2002058133585743, 2001016990753134, 2000476867704297, 2000211755337034, 2000088866795233,
    2000035168668103, 2000013090848214, 2000004568596513, 2000001488559576, 2000000450191853,
    2000000125344610, 2000000031749443, 2000000007193749, 2000000001428260, 2000000000248279,
    2000000000044445, 2000000000013682, 2000000000007029, 2000000000003641, 2000000000001647,
    2000000000000653, 2000000000000228, 2000000000000070, 2000000000000019, 2000000000000003]
private def pvn_m8_r256_6_2 : List ℕ :=
  pCat pvn_m8_r256_6_2_p0
    (pCat pvn_m8_r256_6_2_p1
    (pCat pvn_m8_r256_6_2_p2
      pvn_m8_r256_6_2_p3))
private def pvn_m8_r256_6_3_p0 : List ℕ :=
  [2000148759288328, 2000281863545601, 2000106218185393, 1999625694711308, 1999890609154572,
    1999968646563536, 1999965503093419, 2000304840655016, 2000004958280736, 1999836472523515,
    1999556948531867, 2000036127574398, 2000643878712140, 1999859474353026, 2000029151623035,
    1999783475855785, 1999896788962931, 1999882346803165, 1999863931721325, 2000388705200750,
    2000206893930080, 2000019323284455, 1999855766233991, 2000235760656497, 1999910722197514,
    2000089592439854, 2000381708473046, 1999707828679560, 2000013975108680, 1999884159033885,
    1999912107975174, 2000457280228797, 1999616542899490, 2000336527242967, 2000138225677286,
    2000116382808636, 1999978961128197, 2000254601045458, 1999587627686109, 2000014917568125,
    2000596620517737, 1999887937715206, 2000506531931931, 1999778635249679, 1999775408168958,
    1999865000728971, 1999671380478094, 1999851557539097, 1999860645241986, 1999857915516992,
    2000200108613862, 1999971936844012, 2000065212679135, 1999891623904715, 2000407296450155,
    2000139048564576, 2000504160085137, 2000837408247311, 2000385330836915, 2000540737379328,
    1999702877418941, 2000220103450291, 1999823927263730, 2000171331573420]
private def pvn_m8_r256_6_3_p1 : List ℕ :=
  [1999973843771303, 2000080102610181, 2000436013782558, 1999943738381736, 1999687415748154,
    2000320991628516, 1999668783821663, 2000338105135330, 1999896048883175, 2000149612056342,
    1999939737180548, 2000162761733904, 2000213523402692, 2000339593600212, 2000601390411468,
    1999562128480614, 2000467840833498, 1999779480308981, 2000138950937980, 2000078886298517,
    1999221853524377, 2000313485862028, 1999496816456015, 2000571341929654, 1999451328979209,
    1999794304915130, 2000359725012711, 1999229949656799, 2001031268022654, 1999104031895440,
    1999612323523993, 2001133211733074, 1998216829400789, 2001965676386812, 1999155452843552,
    1999874927228538, 2001387874734896, 1997839413939311, 2001904846288884, 1999585956871520,
    1999702156506399, 2002120045792064, 1997899570102766, 2002048245410404, 2001087224008959,
    1997117469677026, 2002120978011775, 1999758832205463, 1999113062804995, 2002467580742156,
    1998484439055021, 2000266223417734, 2002006882905145, 1997322027180421, 2000952989973890,
    2001633162490460, 1997032970434756, 2000630672052251, 2001493668406858, 1997560602779631,
    2000803235463246, 2000881292016483, 1997839799200582, 2001528464978935]
private def pvn_m8_r256_6_3_p2 : List ℕ :=
  [2001152006633164, 1997731166168860, 2001111011462818, 2001058349960420, 1996860114233665,
    2000732632449426, 2003337413671041, 1997325221021435, 1997654967961817, 2003351591657029,
    2001051928452273, 1998339923263018, 2001520503791515, 2000981869389453, 1997728868964840,
    1999477887244686, 2001292270553619, 1999585029264287, 1999877534433354, 2000768937967180,
    1998452555792471, 1999266160520919, 2003558980208633, 2000691574010122, 1994574281015140,
    1998854910178537, 2005678908820821, 1999935547745335, 1992751126011462, 2000157725510066,
    2008615607604337, 2000393401923519, 1990029720687498, 1997976567332562, 2010476138986534,
    2003874618200652, 1989265949344502, 1993344026812658, 2009748391166856, 2009634168577674,
    1992317777934720, 1986774803706318, 2002815174491402, 2014964386553482, 2003726152922089,
    1986221243361183, 1989336190663781, 2008892283795432, 2016248945680590, 2000370059919229,
    1983237114534376, 1988519452948042, 2009477816390452, 2018954296031459, 2004945866735154,
    1984790315566036, 1982930460953745, 2002055784159351, 2020952059704223, 2018718859885022,
    1997073027764854, 1977878370873577, 1980630304636051, 2003688999715951]
private def pvn_m8_r256_6_3_p3 : List ℕ :=
  [2026565869501289, 2028930505474384, 2007924184454263, 1979784099146608, 1966652366534066,
    1980246182150212, 2014018343559270, 2047794923385679, 2060562625238555, 2043000015208263,
    2002746721502797, 1960440062542251, 1939755560378713, 1957117062414793, 2015698701370550,
    2105340881221452, 2207170852840474, 2300280631330512, 2367809528996426, 2400654603086073,
    2398220090953189, 2366691832915352, 2315984229299609, 2256616710115719, 2197419913570475,
    2144412162674187, 2100706498739503, 2067062926774856, 2042684961782718, 2025975534044128,
    2015110613168812, 2008398895042355, 2004457546606332, 2002257209200673, 2001089690019207,
    2000501120579473, 2000219355180665, 2000091323459319, 2000036133196335, 2000013575973490,
    2000004839591217, 2000001635407229, 2000000523357727, 2000000158443484, 2000000045330053,
    2000000012243020, 2000000003119116, 2000000000749381, 2000000000169930, 2000000000036473,
    2000000000007451, 2000000000001462, 2000000000000274, 2000000000000047, 2000000000000006]
private def pvn_m8_r256_6_3 : List ℕ :=
  pCat pvn_m8_r256_6_3_p0
    (pCat pvn_m8_r256_6_3_p1
    (pCat pvn_m8_r256_6_3_p2
      pvn_m8_r256_6_3_p3))
private def pvn_m8_r256_6_4_p0 : List ℕ :=
  [2000076654877362, 1999999769623042, 1999780668661887, 2000113765646388, 2000393916354312,
    2000010225739003, 2000407673544176, 2000015626307216, 1999789500308389, 2000222370993551,
    1999849741786435, 1999763245382043, 1999618458876333, 1999939977112927, 2000322343152521,
    2000234669781517, 2000264590546409, 1999735763765477, 1999438023797536, 2000420322021250,
    1999560565181363, 2000054237846765, 2000142136307360, 2000167293586357, 2000210111473478,
    2000042716860545, 1999977752542416, 1999492164312511, 2000286029166084, 1999613917432304,
    1999782471241192, 2000556361594585, 2000053710041119, 1999853188276739, 2000230522637263,
    1999800140782015, 2000143989105582, 2000052377894028, 2000241450065225, 2000111659594889,
    1999901250890311, 2000155499320900, 1999703796791166, 2000426698121303, 1999674086226628,
    2000028842677816, 1999926554559104, 1999942766508432, 2000191394809534, 2000310505798329,
    2000150401317800, 2000139294244390, 1999522922108503, 2000365121817898, 1999712764184231,
    2000181515881003, 2000261743506322, 2000016302692598, 2000477564375040, 1999998311500658,
    2000136336951894, 1999612759105643, 2000267210805423, 1999581382961786]
private def pvn_m8_r256_6_4_p1 : List ℕ :=
  [1999468567344258, 2000358861200033, 1999438676779306, 2000662813680466, 1999461113462145,
    1999847119215998, 2000136533762741, 1999514613471729, 2000635104675658, 1999821807880844,
    2000785777357506, 2000910190093834, 1999549569607948, 2001788882174392, 1998762645558303,
    2000814958039528, 2000366736669482, 1998634057753527, 2002256873961908, 1998612551305164,
    2000424015963159, 2000821999530643, 1998178528654704, 2002130643869463, 1999150477334637,
    1999479770613604, 2001392543863658, 1997950340436398, 2001561841017437, 2000263548878640,
    1998286863231821, 2002300108096525, 1999082882996298, 1999728264501956, 2002532837545621,
    1997796280639875, 2000538780691345, 2001667736655446, 1997668880743749, 2001027636458400,
    2000761891402368, 1997951452397553, 2001264767636116, 1999702535034678, 1998653011302199,
    2002371908165322, 1998834541496420, 1998030579335962, 2002518062519280, 1999228306709084,
    1998201679978347, 2002094461000551, 1999553321344725, 1998782132203854, 2001956405339698,
    1999373532476763, 1998553559327734, 2001773586505268, 1999522033539644, 1998991738482626,
    2002785272184557, 1999976127619816, 1997823547390942, 2002302048584946]
private def pvn_m8_r256_6_4_p2 : List ℕ :=
  [2000947807500928, 1997239535651400, 2001260481815943, 2002373139599013, 1997793089961166,
    1999626763813429, 2003111698872441, 1999430456632754, 1997771488752134, 2001464416748185,
    2001128966088142, 1998660249159323, 1999931380015611, 1999999382554085, 1998603345509710,
    2000739355491901, 2001403217796256, 1998320822113628, 1999318142531087, 2002162927928304,
    1999272079717052, 1997806739256581, 2002610737804154, 2001996730482972, 1995073410854290,
    1997376663485338, 2006004553832635, 2002708207458490, 1993663399407677, 1998502644026356,
    2007872776920291, 2001451932838259, 1991521879488563, 1998873663373254, 2008952366042736,
    2000584339356198, 1989926344719140, 1999023647383312, 2011159536326574, 2002521039913515,
    1988630079698888, 1995476279672598, 2010542670084615, 2005857337502254, 1989556904946711,
    1991272334174958, 2008671567265387, 2011260100222302, 1993940984528358, 1986118843961430,
    2001452591056075, 2014792577196449, 2004093775510358, 1986345806881868, 1989771609199886,
    2009173228991214, 2014678096579627, 1997703397899513, 1983318648408294, 1992788535040499,
    2013027495014036, 2015694747956920, 1996738940243636, 1981502078368523]
private def pvn_m8_r256_6_4_p3 : List ℕ :=
  [1990409786723454, 2012327996319965, 2019399753746989, 2002310680056502, 1981371465898717,
    1981693372275138, 2003908448048931, 2023923843259968, 2019743851075994, 1994750939451581,
    1973856364913451, 1978473662290768, 2005894350874399, 2031857850575561, 2032433206735873,
    2004963421616484, 1970549687277662, 1957256996128180, 1978436057259844, 2022685459236199,
    2061636797198302, 2068726241748414, 2035953812198322, 1978840423745515, 1928171210198185,
    1914527429540797, 1954268513748026, 2043355220192673, 2160528685409746, 2276833159778007,
    2366343811134098, 2413648360666473, 2416093626609641, 2381426688012843, 2323011676252245,
    2254960160666322, 2188709255482522, 2131517515053025, 2086550780103924, 2053884074123507,
    2031771637298859, 2017752329719616, 2009400930888109, 2004717456361386, 2002242213794209,
    2001008782366964, 2000429248060886, 2000172572771124, 2000065474628509, 2000023410323801,
    2000007875385139, 2000002487959613, 2000000736469225, 2000000203732491, 2000000052504018,
    2000000012557406, 2000000002774348, 2000000000562926, 2000000000104121, 2000000000017378,
    2000000000002578, 2000000000000330, 2000000000000033, 2000000000000001]
private def pvn_m8_r256_6_4 : List ℕ :=
  pCat pvn_m8_r256_6_4_p0
    (pCat pvn_m8_r256_6_4_p1
    (pCat pvn_m8_r256_6_4_p2
      pvn_m8_r256_6_4_p3))
private def pvn_m8_r256_6_5_p0 : List ℕ :=
  [2000032300438622, 1999812876723512, 2000107080930111, 2000431061066951, 1999870075945020,
    1999795796179705, 2000032756466523, 1999982640200044, 1999779220221202, 2000208916235369,
    1999634074343697, 2000480471333261, 2000408953346882, 1999803352440452, 2000363711047949,
    1999995419346476, 2000125704070921, 1999904565519406, 2000336926585749, 2000362416453266,
    1999584281166800, 1999471171788982, 2000047480594903, 1999511625998037, 2000017684583788,
    2000597734735248, 1999808400354335, 2000181854305059, 1999904549516128, 2000438624030671,
    1999636577854921, 1999733222060418, 1999963786053017, 1999868718867652, 1999841787553636,
    2000238466320438, 1999752752556502, 2000537773711130, 2000052225129943, 2000082728395793,
    2000129088006396, 1999540315320830, 2000183867950643, 1999495367778987, 2000012772056575,
    2000185506189137, 1999975405238706, 2000234903758996, 1999603268949040, 2000545742032727,
    1999424013300981, 2000258591816149, 2000420132962408, 1999543231501438, 2000637061790839,
    1999749285552885, 1999777146620964, 2000784475063902, 1999301147123430, 2001072117551755,
    1999063528134060, 1999961666320917, 2000647173631820, 1998574138986924]
private def pvn_m8_r256_6_5_p1 : List ℕ :=
  [2001600669356214, 1999059155713740, 2000128083130450, 2001620060585336, 1998018185965857,
    2001382037218610, 1999764553542473, 1998844506182296, 2001963670816084, 1998304934506177,
    2000519254530730, 2001248128805341, 1998516548865106, 2001806271784691, 1999728746350387,
    1998872559809744, 2001846654615322, 1998132757782997, 2000021498423320, 2001408739720439,
    1997876827248400, 2001214698945905, 2000482481114850, 1997781863375874, 2001680740162408,
    1999607816939218, 1997980604301501, 2002124583043238, 1999676562512682, 1999415114154944,
    2002615665664263, 1999005698261178, 1999558557576191, 2002240339087013, 1998935098954672,
    2000155212374477, 2001519203178946, 1998264151082485, 2000635423082342, 2001764922749099,
    1997926272055772, 2000416802709133, 2002030683799807, 1997946478614644, 1999908686275945,
    2002103139442678, 1998376235698795, 1999455651495745, 2001502894486672, 1998795070476422,
    2000256852493364, 2001784187131518, 1998408798837035, 1999940327173029, 2002451088814994,
    1998782915743689, 1999106616968563, 2002390556251752, 1999090721149739, 1997955586020876,
    2002225974962636, 2000415754237597, 1997235039254115, 2001130409142794]
private def pvn_m8_r256_6_5_p2 : List ℕ :=
  [2001914374827940, 1997748864524236, 1999360514394050, 2001880803680431, 1998789068743741,
    1998689527408288, 2001839249808818, 2000290095549026, 1998625313220382, 2000507927034976,
    2000081321887766, 1999088773289699, 2001025838012726, 2000392615301150, 1998420901580316,
    2001316583522062, 2002537949218282, 1997970161096638, 1998214419317233, 2003301931268404,
    2000961369015378, 1996465185318743, 2001177270462141, 2004157034172872, 1997214743005182,
    1996516118326477, 2005412750008084, 2003562219707962, 1993168666182550, 1997121225844590,
    2007776404927512, 2001655177030315, 1991320430247918, 1999176893720473, 2008514533678957,
    1999155613741247, 1991289262217549, 2002448596087008, 2009356328816751, 1996563367437125,
    1989824946201429, 2003457292130518, 2010119639172983, 1995944811667178, 1989263372122745,
    2004253097609434, 2012061682002761, 1997156333106523, 1987965730754059, 2002032097687928,
    2012329119749785, 1998978979424640, 1986956583080268, 1999157036728755, 2013699233030070,
    2003943989526211, 1986792502369135, 1992463070504799, 2011186275664396, 2010502718601726,
    1991303600855398, 1986041746732310, 2003858922593108, 2015498363474508]
private def pvn_m8_r256_6_5_p3 : List ℕ :=
  [2001668266981573, 1984398188641039, 1991477699458524, 2012324613553078, 2014652220808830,
    1994327873140556, 1981518262663758, 1995477778587907, 2016412097666024, 2014340405514251,
    1991607492147831, 1979364436576189, 1994889590515773, 2018472801348777, 2019251047899152,
    1994896274904889, 1974838309358049, 1984354515274341, 2013979625515838, 2030046781012348,
    2013022727045366, 1979788216203448, 1965959791436592, 1988341158823815, 2027016206812257,
    2044330747203223, 2020950159769881, 1974588417431753, 1945302759977579, 1961579872336089,
    2016253615974716, 2070899022539356, 2083833588673412, 2040013423848234, 1962069593226616,
    1896831836143617, 1888194488415403, 1953952606823588, 2078901194855926, 2225003213704239,
    2350150045404164, 2424748643604716, 2439341289974273, 2402617217699016, 2333606645928907,
    2252978646207715, 2176909431359730, 2114645765729995, 2069060656906227, 2038736528999631,
    2020245900125216, 2009858799570481, 2004468917320279, 2001882707295493, 2000735452246235,
    2000265549299798, 2000088256797445, 2000026853485939, 2000007426533609, 2000001848867259,
    2000000408790809, 2000000078695700, 2000000012778228, 2000000001650822]
private def pvn_m8_r256_6_5_p4 : List ℕ := [2000000000147010]
private def pvn_m8_r256_6_5 : List ℕ :=
  pCat pvn_m8_r256_6_5_p0
    (pCat pvn_m8_r256_6_5_p1
    (pCat pvn_m8_r256_6_5_p2
    (pCat pvn_m8_r256_6_5_p3
      pvn_m8_r256_6_5_p4)))
private def phb_m8_r256_7_p0 : List ℕ :=
  [107416875718985, 151444106222290, 184909166893178, 212854966830982, 237241294171873,
    259076413262028, 278961125051757, 297288074844970, 314330816201315, 330289116739894,
    345314232192274, 359524019513793, 373012478659457, 385856046317665, 398117899598155,
    409850989235992, 421100233094367, 431904138002964, 442296022313097, 452304953258587,
    461956476553025, 471273191955042, 480275212832484, 488980537125021, 497405349763411,
    505564271443560, 513470564967916, 521136307695319, 528572536677969, 535789371604642,
    542796119571301, 549601364865559, 556213046310651, 562638524218115, 568884638610488,
    574957760069837, 580863834325534, 586608421501009, 592196730783417, 597633651154075,
    602923778714911, 608071441062088, 613080719088873, 617955466542607, 622699327613109,
    627315752790186, 631808013194672, 636179213559410, 640432304012951, 644570090798674,
    648595246044942, 652510316687338, 656317732631498, 660019814234338, 663618779172166,
    667116748756196, 670515753748994, 673817739729370, 677024572047937, 680138040410971,
    683159863126161, 686091691040300, 688935111195847, 691691650230543]
private def phb_m8_r256_7_p1 : List ℕ :=
  [694362777541824, 696949908235649, 699454405877400, 701877585060876, 704220713809833,
    706485015825207, 708671672589947, 710781825342284, 712816576927319, 714776993535924,
    716664106339182, 718478913025874, 720222379249890, 721895439993866, 723499000854837,
    725033939257197, 726501105597872, 727901324328180, 729235394976536, 730504093115798,
    731708171278808, 732848359825361, 733925367763627, 734939883528813, 735892575721648,
    736784093809083, 737615068789435, 738386113824038, 739097824837312, 739750781087044,
    740345545706539, 740882666220177, 741362675033828, 741786089901468, 742153414369233,
    742465138198104, 742721737766286, 742923676452330, 743071404999923, 743165361865260,
    743205973547807, 743193654905253, 743128809453372, 743011829651470, 742843097174062,
    742622983169373, 742351848505216, 742030044002773, 741657910658766, 741235779856467,
    740763973565982, 740242804534193, 739672576464741, 739053584188380, 738386113824038,
    737670442930866, 736906840651558, 736095567847205, 735236877223893, 734331013451289,
    733378213273392, 732378705611637, 731332711660512, 730240444975835]
private def phb_m8_r256_7_p2 : List ℕ :=
  [729102111555813, 727917909915017, 726688031151345, 725412659006078, 724091969917085,
    722726133065240, 721315310414085, 719859656742765, 718359319672248, 716814439684822,
    715225150136857, 713591577264796, 711913840184317, 710192050882620, 708426314203750,
    706616727826859, 704763382237292, 702866360690388, 700925739167820, 698941586326331,
    696913963438672, 694842924326538, 692728515285278, 690570775000128, 688369734453702,
    686125416824432, 683837837375652, 681507003334955, 679132913763466, 676715559414598,
    674254922581858, 671750976935226, 669203687345572, 666613009696565, 663978890683468,
    661301267598153, 658580068099656, 655815209969492, 653006600850922, 650154137971292,
    647257707846492, 644317185966496, 641332436460899, 638303311743223, 635229652132734,
    632111285452336, 628948026601058, 625739677099482, 622486024606345, 619186842404385,
    615841888853363, 612450906807978, 609013622998230, 605529747369553, 601998972379800,
    598420972249920, 594795402164859, 591121897420908, 587400072515369, 583629520174027,
    579809810311462, 575940488918792, 572021076872855, 568051068660306]
private def phb_m8_r256_7_p3 : List ℕ :=
  [564029931009364, 559957101421284, 555831986592729, 551653960719322, 547422363669610,
    543136499017465, 538795631919656, 534398986823787, 529945744990110, 525435041808792,
    520865963892008, 516237545917733, 511548767199231, 506798547950985, 501985745218022,
    497109148431268, 492167474546559, 487159362719154, 482083368458871, 476937957203142,
    471721497236136, 466432251871425, 461068370803022, 455627880514817, 450108673620794,
    444508496987515, 438824938465352, 433055412024997, 427197141059684, 421247139569886,
    415202190894121, 409058823584552, 402813283946195, 396461504659792, 389999068785494,
    383421168290514, 376722556049736, 369897490021373, 362939667983628, 355842150809764,
    348597271726383, 341196528298502, 333630452951983, 325888456588249, 317958638135428,
    309827550517619, 301479910213457, 292898232860911, 284062370532153, 274948916201952,
    265530425673401, 255774383599615, 245641802638381, 235085283018133, 224046254623949,
    212450936928392, 200204203513116, 187179847630925, 173204275370456, 158027224512535,
    141264103866252, 122266735905616, 99769886895689, 70503741376170]
private def phb_m8_r256_7 : List ℕ :=
  pCat phb_m8_r256_7_p0
    (pCat phb_m8_r256_7_p1
    (pCat phb_m8_r256_7_p2
      phb_m8_r256_7_p3))
private def pvn_m8_r256_7_0_p0 : List ℕ :=
  [2000032300438622, 2000187123276488, 1999892919069889, 1999568938933049, 1999870075945020,
    1999795796179705, 2000032756466523, 1999982640200044, 2000220779778798, 2000208916235369,
    2000365925656303, 2000480471333261, 1999591046653118, 2000196647559548, 2000363711047949,
    1999995419346476, 1999874295929079, 1999904565519406, 2000336926585749, 2000362416453266,
    1999584281166800, 1999471171788982, 2000047480594903, 2000488374001963, 1999982315416212,
    1999402265264752, 1999808400354335, 2000181854305059, 1999904549516128, 2000438624030671,
    2000363422145079, 2000266777939582, 1999963786053017, 2000131281132348, 1999841787553636,
    1999761533679562, 1999752752556502, 2000537773711130, 2000052225129943, 2000082728395793,
    1999870911993604, 1999540315320830, 2000183867950643, 1999495367778987, 2000012772056575,
    2000185506189137, 1999975405238706, 2000234903758996, 1999603268949040, 1999454257967273,
    1999424013300981, 2000258591816149, 2000420132962408, 1999543231501438, 2000637061790839,
    1999749285552885, 2000222853379036, 2000784475063902, 1999301147123430, 2001072117551755,
    1999063528134060, 1999961666320917, 2000647173631820, 1998574138986924]
private def pvn_m8_r256_7_0_p1 : List ℕ :=
  [2001600669356214, 2000940844286260, 2000128083130450, 2001620060585336, 1998018185965857,
    2001382037218610, 1999764553542473, 1998844506182296, 2001963670816084, 1998304934506177,
    2000519254530730, 2001248128805341, 1998516548865106, 2001806271784691, 1999728746350387,
    1998872559809744, 1998153345384678, 1998132757782997, 2000021498423320, 2001408739720439,
    1997876827248400, 1998785301054095, 2000482481114850, 1997781863375874, 2001680740162408,
    1999607816939218, 2002019395698499, 2002124583043238, 1999676562512682, 1999415114154944,
    2002615665664263, 2000994301738822, 1999558557576191, 2002240339087013, 1998935098954672,
    2000155212374477, 1998480796821054, 1998264151082485, 2000635423082342, 2001764922749099,
    1997926272055772, 1999583197290867, 2002030683799807, 1997946478614644, 1999908686275945,
    2002103139442678, 2001623764301205, 1999455651495745, 2001502894486672, 1998795070476422,
    1999743147506636, 1998215812868482, 1998408798837035, 1999940327173029, 2002451088814994,
    1998782915743689, 2000893383031437, 2002390556251752, 1999090721149739, 1997955586020876,
    2002225974962636, 1999584245762403, 1997235039254115, 2001130409142794]
private def pvn_m8_r256_7_0_p2 : List ℕ :=
  [2001914374827940, 1997748864524236, 1999360514394050, 2001880803680431, 1998789068743741,
    1998689527408288, 2001839249808818, 2000290095549026, 1998625313220382, 2000507927034976,
    2000081321887766, 1999088773289699, 2001025838012726, 2000392615301150, 1998420901580316,
    2001316583522062, 2002537949218282, 1997970161096638, 1998214419317233, 2003301931268404,
    2000961369015378, 1996465185318743, 1998822729537859, 2004157034172872, 1997214743005182,
    1996516118326477, 2005412750008084, 2003562219707962, 1993168666182550, 1997121225844590,
    2007776404927512, 2001655177030315, 2008679569752082, 1999176893720473, 2008514533678957,
    1999155613741247, 1991289262217549, 2002448596087008, 2009356328816751, 1996563367437125,
    1989824946201429, 2003457292130518, 2010119639172983, 1995944811667178, 1989263372122745,
    2004253097609434, 2012061682002761, 2002843666893477, 1987965730754059, 2002032097687928,
    2012329119749785, 1998978979424640, 2013043416919732, 1999157036728755, 2013699233030070,
    2003943989526211, 1986792502369135, 1992463070504799, 2011186275664396, 2010502718601726,
    1991303600855398, 1986041746732310, 1996141077406892, 2015498363474508]
private def pvn_m8_r256_7_0_p3 : List ℕ :=
  [2001668266981573, 1984398188641039, 1991477699458524, 2012324613553078, 2014652220808830,
    1994327873140556, 1981518262663758, 1995477778587907, 2016412097666024, 2014340405514251,
    1991607492147831, 1979364436576189, 1994889590515773, 2018472801348777, 2019251047899152,
    1994896274904889, 1974838309358049, 1984354515274341, 2013979625515838, 2030046781012348,
    2013022727045366, 1979788216203448, 1965959791436592, 1988341158823815, 2027016206812257,
    2044330747203223, 2020950159769881, 1974588417431753, 1945302759977579, 1961579872336089,
    2016253615974716, 2070899022539356, 2083833588673412, 2040013423848234, 2037930406773384,
    2103168163856383, 2111805511584597, 2046047393176412, 2078901194855926, 2225003213704239,
    2350150045404164, 2424748643604716, 2439341289974273, 2402617217699016, 2333606645928907,
    2252978646207715, 2176909431359730, 2114645765729995, 2069060656906227, 2038736528999631,
    2020245900125216, 2009858799570481, 2004468917320279, 1998117292704507, 2000735452246235,
    2000265549299798, 2000088256797445, 1999973146514061, 2000007426533609, 2000001848867259,
    2000000408790809, 1999999921304300, 2000000012778228, 2000000001650822]
private def pvn_m8_r256_7_0_p4 : List ℕ := [2000000000147010]
private def pvn_m8_r256_7_0 : List ℕ :=
  pCat pvn_m8_r256_7_0_p0
    (pCat pvn_m8_r256_7_0_p1
    (pCat pvn_m8_r256_7_0_p2
    (pCat pvn_m8_r256_7_0_p3
      pvn_m8_r256_7_0_p4)))
private def pvn_m8_r256_7_1_p0 : List ℕ :=
  [1999957989081702, 1999861981086858, 2000275360499373, 2000123345934989, 2000086202494976,
    1999950245251251, 1999639487335916, 2000060014853277, 1999596322901490, 1999732722786603,
    2000194091595781, 1999852324501036, 1999676290249592, 2000113717287700, 2000321573999344,
    2000450263642667, 2000216977121557, 1999909497755647, 2000013170533717, 2000407293712919,
    2000299984065421, 2000165753412633, 1999392478350310, 1999976894160309, 2000569342638916,
    2000524347081595, 1999662399442839, 1999789428258401, 1999757832170928, 2000173007085486,
    2000004621263040, 1999958301289733, 2000360397391762, 1999385825558731, 1999823902208769,
    1999909902862748, 1999801442833162, 2000339300713235, 1999895027169713, 2000335290885408,
    2000570566921889, 2000152003801066, 2000136838153390, 1999475418560792, 2000215561095692,
    1999811608617367, 1999777117871895, 2001045496398147, 1999026095710190, 2000674286533823,
    2000173534483179, 1999207463629022, 2000576772407284, 1998704498067675, 2000164574344693,
    2001287057756655, 1998464977829869, 2001646118126528, 1998927977327249, 1999049910550677,
    2001182970938322, 1998270814652823, 2001057273238714, 1999825901641389]
private def pvn_m8_r256_7_1_p1 : List ℕ :=
  [1998588982743838, 2002374869229079, 1998498387864613, 2000207826914081, 2001096993841410,
    1999734490820801, 2000442148471462, 2000382498252238, 1998652525856850, 1999727191419924,
    2000889506444948, 1999061653817592, 2002533290330660, 1998844794471638, 2001246322974565,
    2001145349909197, 1998672572712521, 2000152494971447, 2001238713031922, 1999937776376751,
    1998860225500111, 2000110207526851, 1998709808298056, 2003293451025850, 2000574734579612,
    1998510682940444, 2000299141102524, 1999599505589621, 1997844014976566, 1999473828697235,
    2000641065942639, 1998815912208933, 2000440338990787, 1997010341870557, 1998575660443479,
    2000808163515532, 2000470718930480, 1998013227772357, 2003164028133923, 2001051976806572,
    1998893937915499, 2000329460111039, 2002699739849360, 2000488333790242, 2001700897300993,
    2000723490736156, 1999886630931729, 1999845089071650, 1998913444000759, 1998625266775965,
    2001783968245618, 2000070538068196, 1997585334914181, 2000722143974660, 2000971490032297,
    1997350337574878, 1999974422944869, 2003350232534270, 1999990815213840, 1999770830787957,
    2003050461457441, 1999605101097142, 1996532340095644, 2000174321192822]
private def pvn_m8_r256_7_1_p2 : List ℕ :=
  [2000436048717930, 1997779207129210, 2000369246959751, 2002116906697995, 1999680243962339,
    2000236663755447, 2001321973004551, 1999297889443053, 1998951591097748, 2001249249847779,
    1998673734114924, 1999970222310660, 2001069689920382, 1999661764744493, 1997481305008727,
    2000838365050669, 2003036452907870, 1996324294263615, 1999640103208476, 2001871487677963,
    2003858397676728, 1990100434335690, 2006737383889870, 2000741861175909, 1996170210920822,
    2000982914737380, 2001893357140543, 2001497930165119, 1996714971539143, 1998844115864320,
    2006442952709307, 2000562518309851, 1992435219855628, 2000536334879057, 2004815876269487,
    1998237521127070, 1996251896597305, 2007366468151410, 1999729824816087, 1987270984123260,
    2002516886273159, 2006921689602292, 2015620291643016, 1985923491946564, 2005294263742744,
    2014236640248736, 1996986746430537, 1994060553040268, 1999150709057137, 2006973308712379,
    2003523661343241, 1993430694732510, 1991816899751485, 2009169341433899, 2002500492091127,
    1995329129464456, 2000698724120261, 2006584775056231, 2000491703916385, 1990000116481088,
    2000154989129868, 2020947614580311, 2016519817444012, 1993178615428283]
private def pvn_m8_r256_7_1_p3 : List ℕ :=
  [1990429920399179, 2010063978601250, 2014820651498283, 1995289357925442, 1984860402292207,
    2000453922276853, 2013942624617399, 2000950477301368, 1982188760960469, 1989086634895353,
    2012126584430029, 2015646723076202, 1993986693637029, 1980365942150832, 1996109392477315,
    2018410955972035, 2014060828685659, 1988198794392920, 1977478460444676, 1998321250371966,
    2023435530463187, 2018089343168922, 1987726623002990, 1970003740736088, 1991466293492367,
    2023057422719844, 2033990973920091, 1998405353623162, 1964173536477129, 1971973221755850,
    2003190468129061, 2043155064141842, 2060006495146064, 1981782026800282, 1909649970541161,
    1983527380133099, 2042153619773152, 2006740496335162, 2009910694956554, 2079831796428025,
    2110673907246071, 2064492396204285, 2014634070948201, 2039185868331780, 2147035408953654,
    2288943812713294, 2404889549222148, 2456171735058915, 2440460649212313, 2370932930984493,
    2283888353209587, 2192840767368782, 2120148276995708, 2070290133554903, 2036534165701113,
    2015860104075388, 2005825228120093, 2001950142715627, 2000625220731622, 2000186325260485,
    2000049539294522, 2000011650851165, 2000002372521983, 2000000387377617]
private def pvn_m8_r256_7_1_p4 : List ℕ := [2000000043156150]
private def pvn_m8_r256_7_1 : List ℕ :=
  pCat pvn_m8_r256_7_1_p0
    (pCat pvn_m8_r256_7_1_p1
    (pCat pvn_m8_r256_7_1_p2
    (pCat pvn_m8_r256_7_1_p3
      pvn_m8_r256_7_1_p4)))
private def pvn_m8_r256_7_2_p0 : List ℕ :=
  [2000134331515239, 1999855300152020, 1999795874916179, 2000152816012711, 1999856742454138,
    2000170212839318, 2000379913089990, 1999970839249707, 1999855772455434, 2000206038000286,
    1999963942384825, 1999662875643038, 1999682489565677, 1999960986383798, 1999866419348801,
    2000127445170364, 1999607125725801, 1999774608003697, 1999801635253611, 2000204087525481,
    2000282336351694, 2000576059569499, 1999930869051215, 1999619413834154, 2000392429143136,
    2000372078162334, 2000700009505415, 1999809744881994, 1999378794773656, 2000324600159184,
    2000062571907126, 2000247029698194, 2000449766870149, 1999822842278980, 2000153228491010,
    1999629046581830, 1999809294078301, 2000360152419741, 1999630295559953, 2000892465796067,
    1999202008711473, 1999813695009364, 2000675827851757, 1998813130886947, 2000284647828485,
    2000213869154250, 1998725534394207, 2001799513118155, 1999240929007783, 2000569858280369,
    2001307109693407, 1998055978077583, 2001319815136067, 2000039791906585, 1998619815552493,
    2001814773910997, 1998282253913495, 2001010794332183, 2000803014338048, 1998904845731100,
    2000820190444418, 1999636957994462, 1998738349315650, 2000339470589858]
private def pvn_m8_r256_7_2_p1 : List ℕ :=
  [2001232951413306, 1998247345727148, 2001823808234693, 1998762570335157, 2000068562898776,
    2000570894678716, 1998478574173199, 2000495722432208, 1999822597878396, 1999708548883198,
    2000006306929762, 2000772351592627, 1997796543667599, 2001659167556794, 2000920315041826,
    1999333531077908, 2000942346416364, 1999637490026292, 1999655778393874, 1999989335702302,
    1999461645174394, 1998721195575754, 2003358397185173, 1999778123333853, 1999038683310853,
    2000353173548800, 2001724141551345, 1999784244930327, 2001446998359471, 1998418168525531,
    1999367982208042, 2000788202381187, 1999574851759088, 1999150720776273, 2003451417638607,
    2000784167614431, 1997568631192212, 1999772253936317, 2000629973100567, 1998588589506759,
    1999815382669545, 2000097640337691, 1999120451293535, 1999209161576440, 1997772992512008,
    1998176579901974, 2001177745944100, 2000111903475691, 1998557797712831, 2001669548491774,
    2001239440032707, 1997729710826118, 2001104967637298, 2004119881331666, 2000026233400418,
    1999906125248846, 2002974251040787, 1999564788310113, 1997535344187562, 2001660441021360,
    2000549229850249, 1998198643232257, 2000181022687045, 2001513866746002]
private def pvn_m8_r256_7_2_p2 : List ℕ :=
  [1997178695760165, 1999278285912982, 2000564839552751, 1999624741364513, 2001580792080197,
    2001467742509562, 2001659872400034, 1998073732661001, 2003139470085251, 1995496847526729,
    2001395827781408, 1996879496165766, 2004004391889268, 1995610769329075, 2001130198517586,
    2006517878690805, 1993968038697943, 1999595067420386, 2004932902267118, 1997866421470461,
    1997552099454472, 2001616613704325, 2001518702062898, 1998743970694754, 1996546028200748,
    2003240220791992, 2001426689305359, 1995791043291644, 2000151803154056, 2003812803585426,
    2001967534273769, 1987574743957483, 2011324920434109, 1998146057980259, 1999269361568441,
    1995936049040591, 2003241845993822, 2005451163465223, 1989732971120962, 2005905862926111,
    2009210504575236, 1989535927767807, 1991005248140205, 2011815035822470, 2005101948047481,
    1996147456192362, 1992082850288722, 2001531041733466, 2005954560312088, 1993317172708777,
    1996179488642768, 2011097808608748, 2009430240067438, 1997116376174747, 1996913648672141,
    2007245743772913, 2006064572373369, 1994803463962270, 1997365719411551, 2007595758685117,
    1999971941760955, 1987716327133440, 1999436549674913, 2016642969205721]
private def pvn_m8_r256_7_2_p3 : List ℕ :=
  [2005055404719991, 1982788658225128, 1989752961722018, 2014251790045157, 2015002894534003,
    1995815794249018, 1995218295012135, 2014378627321009, 2016488536970326, 1995296350485202,
    1986999722614893, 2005441093545820, 2017268569835487, 1999233564952915, 1979880670469846,
    1990165930892794, 2015489498719376, 2012048822016674, 1989218862146063, 1978147836558526,
    2004421422309575, 2022667738653837, 2006318736484369, 1980974283741840, 1978205344174804,
    2009368233108609, 2034944787802590, 2001123346932033, 1967879567796717, 1989432754398002,
    1996288950957355, 2032965338434059, 2046480476597817, 1952194296816868, 1926166555574237,
    2034178223481530, 2073378670532729, 1999873462307700, 1967110233196210, 1995987493376936,
    1991183668289712, 1959474735805251, 1985228998931081, 2062505345145446, 2107684468956091,
    2068195258456152, 2004942222022781, 1996911710806014, 2089249350220010, 2245443510878908,
    2390263145527620, 2470721538986083, 2466153153060126, 2392444588263652, 2289326605169983,
    2190225830619058, 2111156888012429, 2056787391235253, 2025013003888791, 2009448121701567,
    2003058513526412, 2000845002932428, 2000195723563122, 2000036207823459]
private def pvn_m8_r256_7_2_p4 : List ℕ := [2000004660510545]
private def pvn_m8_r256_7_2 : List ℕ :=
  pCat pvn_m8_r256_7_2_p0
    (pCat pvn_m8_r256_7_2_p1
    (pCat pvn_m8_r256_7_2_p2
    (pCat pvn_m8_r256_7_2_p3
      pvn_m8_r256_7_2_p4)))
private def pwalks_m8_r256 : List RkmSegWalk := [
  ⟨uOfHb phb_m8_r256_0, bDec bZ (zPad bZ 1 pvn_m8_r256_0_0),
    bDec bZ (zPad bZ 9 pvn_m8_r256_0_1)⟩,
  ⟨uOfHb phb_m8_r256_1, bDec bZ (zPad bZ 9 pvn_m8_r256_0_1),
    bDec bZ (zPad bZ 17 pvn_m8_r256_1_1)⟩,
  ⟨uOfHb phb_m8_r256_2, bDec bZ (zPad bZ 17 pvn_m8_r256_1_1),
    bDec bZ (zPad bZ 33 pvn_m8_r256_2_1)⟩,
  ⟨uOfHb phb_m8_r256_3, bDec bZ (zPad bZ 33 pvn_m8_r256_2_1),
    bDec bZ (zPad bZ 65 pvn_m8_r256_3_1)⟩,
  ⟨uOfHb phb_m8_r256_4, bDec bZ (zPad bZ 65 pvn_m8_r256_4_0),
    bDec bZ (zPad bZ 129 pvn_m8_r256_4_2)⟩,
  ⟨uOfHb phb_m8_r256_5, bDec bZ (zPad bZ 129 pvn_m8_r256_5_0),
    bDec bZ (zPad bZ 257 pvn_m8_r256_5_4)⟩,
  ⟨uOfHb phb_m8_r256_6, bDec bZ (zPad bZ 257 pvn_m8_r256_6_0),
    bDec bZ (zPad bZ 257 pvn_m8_r256_6_5)⟩,
  ⟨uOfHb phb_m8_r256_7, bDec bZ (zPad bZ 257 pvn_m8_r256_7_0),
    bDec bZ (zPad bZ 257 pvn_m8_r256_7_2)⟩
  ]
private def phb_m16_r256_0 : List ℕ :=
  [250207596231953, 347593345707357, 417968576242700, 473581549338528, 519241991604483,
    557442256259463, 589672965253958, 616907698875138, 639820623633272, 658897581464156,
    674498138361192, 686892590023675, 696285106843620, 702828677861024, 706634901407456,
    707780335149787, 706310384788088, 702241273932360, 695560347282283, 686224731246387,
    674158152383464, 659245437668660, 641323812268427, 620169430183838, 595476338208177,
    566822658597104, 533613666763812, 494979574288350, 449574776359302, 395129724909942,
    327231861670145, 234569621467456]
private def pvn_m16_r256_0_1 : List ℕ :=
  [2008490297595894, 2028601682435934, 2066880642013636, 2125282345863564, 2199292910008868,
    2277881358608970, 2346399162984418, 2391255327423589, 2404261734557068, 2384815793175436,
    2339272087066894, 2278174152698555, 2212769129425751, 2152174103037050, 2101942464692146,
    2064040821055106, 2037751896079348, 2020887894804500, 2010844862416875, 2005279922126768,
    2002407649698050, 2001026532707403, 2000408265094353, 2000150988970103, 2000051713822304,
    2000016315587793, 2000004708232147, 2000001230870774, 2000000287636274, 2000000058906127,
    2000000010242429, 2000000001426366, 2000000000137842]
private def phb_m16_r256_1 : List ℕ :=
  [188953632000000, 264606578588581, 320862235487692, 366775610201214, 405887963192264,
    440031499375786, 470303591924574, 497424726034194, 521898902015594, 544095452236915,
    564294803035340, 582715908219049, 599533611255062, 614890123302299, 628902888230894,
    641670135894556, 653274903971609, 663788014661882, 673270319448993, 681774419503066,
    689346002762917, 696024895649160, 701845898760155, 706839456494441, 711032197104473,
    714447370206574, 717105201966944, 719023183215375, 720216302049262, 720697229702008,
    720476466300008, 719562451435992, 717961643109505, 715678567427441, 712715840440721,
    709074162552802, 704752285014079, 699746947057302, 694052781172566, 687662182795966,
    680565139205719, 672749010567538, 664198253688828, 654894075905584, 644814002315002,
    633931333806860, 622214465326270, 609626022428420, 596121757753509, 581649124816701,
    566145409964321, 549535246859659, 531727248084405, 512609341184553, 492042146047385,
    469849286271937, 445802699232211, 419599372005507, 390822447982955, 358871537218701,
    322825790675803, 281137677214722, 230797665719300, 164064234322694]
private def pvn_m16_r256_1_1_p0 : List ℕ :=
  [2000000000166154, 2000000001535260, 2000000009866895, 2000000050922426, 2000000223808239,
    2000000865017768, 2000003000175483, 2000009468503591, 2000027467967201, 2000073810565275,
    2000184828152624, 2000433378459741, 2000955265541816, 2001985883473873, 2003904298373790,
    2007276061629943, 2012878656200769, 2021687040182417, 2034795117633316, 2053256290346242,
    2077844910924601, 2108768731003458, 2145393111597310, 2186059132704899, 2228077431757176,
    2267950268534326, 2301818753599260, 2326064910133685, 2337941771972270, 2336081194780570,
    2320750658406990, 2293793044412643, 2258267436591506, 2217886395461399, 2176390773911687,
    2137004466007798, 2102072578376369, 2072924817804162, 2049943969133543, 2032775822472256,
    2020600541994835, 2012394185950203, 2007133407039318, 2003924670492779, 2002062444732019,
    2001034268369868, 2000494426552614, 2000225046870530, 2000097400553090, 2000040022034378,
    2000015585482221, 2000005740383534, 2000001994957851, 2000000652368991, 2000000200073692,
    2000000057319920, 2000000015266588, 2000000003757389, 2000000000848012, 2000000000173734,
    2000000000031862, 2000000000005123, 2000000000000696, 2000000000000073]
private def pvn_m16_r256_1_1_p1 : List ℕ := [2000000000000004]
private def pvn_m16_r256_1_1 : List ℕ :=
  pCat pvn_m16_r256_1_1_p0
      pvn_m16_r256_1_1_p1
private def phb_m16_r256_2_p0 : List ℕ :=
  [146087612340399, 205388144787103, 250064004569303, 287034226752999, 318995486833881,
    347338932487047, 372895689559684, 396210313085317, 417663132790157, 437532563296597,
    456029905067092, 473320178490044, 489535292760245, 504782741933065, 519151558039259,
    532716511479763, 545541151959341, 557680059362346, 569180542317542, 580083941917511,
    590426647539995, 600240899038961, 609555427909418, 618395975351915, 626785715020585,
    634745601105690, 642294657303675, 649450218530459, 656228134515886, 662642942394763,
    668708013887494, 674435681505238, 679837347324893, 684923577189621, 689704182651373,
    694188292547054, 698384415762508, 702300496468830, 705943962898330, 709321770551679,
    712440440584478, 715306094004123, 717924482211177, 720301014339415, 722440781782129,
    724348580236660, 726028929552393, 727486091628072, 728724086570956, 729746707301982,
    730557532766891, 731159939892557, 731557114409899, 731752060649319, 731747610401276,
    731546430922893, 731151032161340, 730563773255705, 729786868371180, 728822391912270,
    727672283155452, 726338350335972, 724822274218299, 723125611174999]
private def phb_m16_r256_2_p1 : List ℕ :=
  [721249795794353, 719196143032939, 716965849925451, 714559996860257, 711979548425517,
    709225353827025, 706298146875282, 703198545535540, 699927051030691, 696484046482795,
    692869795074670, 689084437708288, 685127990131607, 681000339499787, 676701240330492,
    672230309805879, 667587022365923, 662770703528624, 657780522862240, 652615486022674,
    647274425755276, 641755991744125, 636058639172938, 630180615839525, 624119947639452,
    617874422203435, 611441570435868, 604818645657485, 598002600001690, 590990057649439,
    583777284409048, 576360153051246, 568734103691853, 560894098368569, 552834568776887,
    544549355902857, 536031640003728, 527273859023246, 518267613061710, 509003551918123,
    499471241935853, 489659007348629, 479553739947149, 469140669034174, 458403081112219,
    447321975263072, 435875635295211, 424039092781958, 411783445035388, 399074977165357,
    385874014870436, 372133399771154, 357796423655245, 342793966953762, 327040431728868,
    310427784128508, 292816507496451, 274021250011352, 253786784736632, 231744848425741,
    207329161514844, 179584963726426, 146648274726706, 103702270117241]
private def phb_m16_r256_2 : List ℕ :=
  pCat phb_m16_r256_2_p0
      phb_m16_r256_2_p1
private def pvn_m16_r256_2_0_p0 : List ℕ :=
  [1999999999833846, 1999999998464740, 2000000009866895, 1999999949077574, 1999999776191761,
    1999999134982232, 1999996999824517, 1999990531496409, 1999972532032799, 1999926189434725,
    1999815171847376, 2000433378459741, 2000955265541816, 2001985883473873, 2003904298373790,
    2007276061629943, 2012878656200769, 2021687040182417, 2034795117633316, 2053256290346242,
    2077844910924601, 2108768731003458, 2145393111597310, 2186059132704899, 2228077431757176,
    2267950268534326, 2301818753599260, 2326064910133685, 2337941771972270, 2336081194780570,
    2320750658406990, 2293793044412643, 2258267436591506, 2217886395461399, 2176390773911687,
    2137004466007798, 2102072578376369, 2072924817804162, 2049943969133543, 2032775822472256,
    2020600541994835, 2012394185950203, 2007133407039318, 2003924670492779, 2002062444732019,
    2001034268369868, 2000494426552614, 2000225046870530, 2000097400553090, 2000040022034378,
    2000015585482221, 2000005740383534, 2000001994957851, 1999999347631009, 1999999799926308,
    1999999942680080, 2000000015266588, 2000000003757389, 2000000000848012, 2000000000173734,
    2000000000031862, 1999999999994877, 2000000000000696, 2000000000000073]
private def pvn_m16_r256_2_0_p1 : List ℕ := [2000000000000004]
private def pvn_m16_r256_2_0 : List ℕ :=
  pCat pvn_m16_r256_2_0_p0
      pvn_m16_r256_2_0_p1
private def pvn_m16_r256_2_1_p0 : List ℕ :=
  [1999952049709634, 2000087939056282, 1999943660699276, 1999961439662012, 2000064793118463,
    2000025594453068, 1999938722490305, 1999965625019512, 2000049955396975, 2000054063715288,
    1999978060160355, 1999932491393432, 1999974289245909, 2000047780021192, 2000068480225634,
    2000017577641699, 1999948117728865, 1999923104140955, 1999960765493395, 2000029760970355,
    2000081933497631, 2000086845032856, 2000044778504475, 1999978067885338, 1999914006406777,
    1999871503819486, 1999857089759870, 1999867256623588, 1999895715094697, 1999937488735962,
    1999997257426078, 2000089788708898, 2000252869662244, 2000551028806845, 2001097644620004,
    2002071363967793, 2003741725146533, 2006494961925678, 2010845336677466, 2017435163020080,
    2027001268993167, 2040299658634848, 2057992538737046, 2080496218596159, 2107812365959421,
    2139381439666232, 2173992589627307, 2209787463048178, 2244386653010347, 2275134880592725,
    2299431339803975, 2315092334232500, 2320677015148691, 2315706049533786, 2300727156445341,
    2277217591283323, 2247347090161157, 2213651814454420, 2178686342763268, 2144719468513133,
    2113520636920230, 2086256883897238, 2063495113233156, 2045286285920901]
private def pvn_m16_r256_2_1_p1 : List ℕ :=
  [2031298157766440, 2020962166055004, 2013606808576685, 2008560906038339, 2005221225808315,
    2003087167750916, 2001769755714542, 2000983613092782, 2000529936718661, 2000276670807898,
    2000139896318409, 2000068459992320, 2000032395010039, 2000014808780423, 2000006533487340,
    2000002779474431, 2000001139262887, 2000000449615039, 2000000170763764, 2000000062394712,
    2000000021929927, 2000000007414630, 2000000002412245, 2000000000755523, 2000000000227978,
    2000000000066342, 2000000000018641, 2000000000005062, 2000000000001328, 2000000000000335,
    2000000000000081, 2000000000000017, 2000000000000002]
private def pvn_m16_r256_2_1 : List ℕ :=
  pCat pvn_m16_r256_2_1_p0
      pvn_m16_r256_2_1_p1
private def pvn_m16_r256_2_2_p0 : List ℕ :=
  [1999969698555583, 1999938791452221, 1999927122519928, 1999951722082428, 2000003360638753,
    2000048356324472, 2000054117091629, 2000017164567512, 1999967901980275, 1999946318314249,
    1999969266079652, 2000016847321078, 2000050122937649, 2000042250971654, 2000001024825506,
    1999958650195021, 1999949115978724, 1999977788134185, 2000023691770383, 2000052274699962,
    2000043472962434, 2000004607254436, 1999961690373518, 1999943731013595, 1999961784358297,
    2000003527285383, 2000044291716246, 2000060319938073, 2000042765648255, 2000002202496762,
    1999959410065484, 1999934795733674, 1999939878826159, 1999971628816151, 2000015951024763,
    2000056039000720, 2000077888535603, 2000074471864937, 2000048086015411, 2000007279949121,
    1999962111459565, 1999921992795438, 1999893808765252, 1999879874358048, 1999878785218497,
    1999887817081553, 1999903638037595, 1999922760879266, 1999943798351083, 1999970034030449,
    2000012140751885, 2000094745066714, 2000269522600699, 2000634673044938, 2001361203406816,
    2002726370461221, 2005149192852694, 2009215974858371, 2015680469712165, 2025423135219206,
    2039356186011377, 2058269660767119, 2082630996982658, 2112371790102343]
private def pvn_m16_r256_2_2_p1 : List ℕ :=
  [2146711633462304, 2184073622977199, 2222136242720157, 2258041257165017, 2288740274979602,
    2311423459038856, 2323945936762019, 2325161560696804, 2315092521246083, 2294901178169750,
    2266676146918374, 2233085351218870, 2196973668881007, 2160986333295656, 2127282633094375,
    2097374930031145, 2072095683440718, 2051669044377617, 2035848864999090, 2024082378263449,
    2015665623958097, 2009868580605167, 2006020620690287, 2003557228721473, 2002035404028946,
    2001127765735102, 2000604995187358, 2000314165046310, 2000157876552181, 2000076751361174,
    2000036082309261, 2000016396559035, 2000007198703088, 2000003051953303, 2000001248795567,
    2000000492893986, 2000000187549470, 2000000068757954, 2000000024272381, 2000000008245431,
    2000000002693674, 2000000000845690, 2000000000254973, 2000000000073763, 2000000000020456,
    2000000000005429, 2000000000001376, 2000000000000330, 2000000000000072, 2000000000000013,
    2000000000000001]
private def pvn_m16_r256_2_2 : List ℕ :=
  pCat pvn_m16_r256_2_2_p0
      pvn_m16_r256_2_2_p1
private def phb_m16_r256_3_p0 : List ℕ :=
  [119276234867712, 168023154686612, 204978495028533, 235756932980712, 262542429119677,
    286459548361057, 308178959746188, 328139337387972, 346646557584288, 363924177769754,
    380141606624127, 395430954976304, 409897678536704, 423627600304781, 436691714219982,
    449149571923728, 461051732798959, 472441576118828, 483356667534149, 493829807153679,
    503889845602291, 513562328015783, 522870008420258, 531833265084672, 540470439244320,
    548798113834829, 556831344762550, 564583854255017, 572068193643990, 579295881303590,
    586277520239655, 593022898893926, 599541078010660, 605840465858411, 611928883666152,
    617813622791352, 623501494866566, 628998875954480, 634311745567063, 639445721263454,
    644406089426307, 649197832722295, 653825654675073, 658294001714952, 662607083016329,
    666768888389485, 670783204456103, 674653629306510, 678383585810112, 681976333728015,
    685434980757693, 688762492623151, 691961702310083, 695035318533402, 697985933514153,
    700816030133835, 703527988526323, 706124092160825, 708606533463394, 710977419019309,
    713238774394168, 715392548607480, 717440618289126, 719384791545888]
private def phb_m16_r256_3_p1 : List ℕ :=
  [721226811562566, 722968359959778, 724611059928350, 726156479158361, 727606132579131,
    728961484924998, 730223953140303, 731394908635843, 732475679407919, 733467552030164,
    734371773527422, 735189553140176, 735922063987306, 736570444634289, 737135800573408,
    737619205621952, 738021703243968, 738344307800631, 738588005733948, 738753756688105,
    738842494572488, 738855128570054, 738792544094483, 738655603699296, 738445147941865,
    738161996205048, 737806947478999, 737380781105493, 736884257486965, 736318118762317,
    735683089451378, 734979877069804, 734209172716081, 733371651632156, 732467973739172,
    731498784149640, 730464713657316, 729366379205985, 728204384338248, 726979319625359,
    725691763079096, 724342280546587, 722931426088943, 721459742344522, 719927760877586,
    718336002513069, 716684977658135, 714975186611157, 713207119858741, 711381258361337,
    709498073827988, 707558028980725, 705561577809081, 703509165815182, 701401230249832,
    699238200340017, 697020497508192, 694748535583727, 692422721006854, 690043453025435,
    687611123884870, 685126119011436, 682588817189332, 679999590731702]
private def phb_m16_r256_3_p2 : List ℕ :=
  [677358805645883, 674666821793117, 671923993042963, 669130667422612, 666287187261325,
    663393889330182, 660451104977328, 657459160258903, 654418376065819, 651329068246542,
    648191547726047, 645006120621079, 641773088351869, 638492747750440, 635165391165622,
    631791306564912, 628370777633286, 624904083869081, 621391500677049, 617833299458688,
    614229747699955, 610581109056437, 606887643436094, 603149607079638, 599367252638647,
    595540829251479, 591670582617078, 587756755066728, 583799585633839, 579799310121823,
    575756161170126, 571670368318480, 567542158069437, 563371753949230, 559159376567033,
    554905243672654, 550609570212729, 546272568385455, 541894447693907, 537475414997993,
    533015674565088, 528515428119375, 523974874889960, 519394211657768, 514773632801287,
    510113330341170, 505413493983749, 500674311163485, 495895967084385, 491078644760425,
    486222525054994, 481327786719409, 476394606430509, 471423158827362, 466413616547118,
    461366150260023, 456280928703615, 451158118716145, 445997885269224, 440800391499725,
    435565798740963, 430294266553181, 424985952753337, 419641013444241]
private def phb_m16_r256_3_p3 : List ℕ :=
  [414259603043037, 408841874309063, 403387978371097, 397898064754008, 392372281404828,
    386810774718270, 381213689561683, 375581169299486, 369913355817081, 364210389544253,
    358472409478091, 352699553205414, 346891956924748, 341049755467829, 335173082320678,
    329262069644238, 323316848294588, 317337547842752, 311324296594105, 305277221607389,
    299196448713350, 293082102533002, 286934306495533, 280753182855857, 274538852711817,
    268291436021061, 262011051617586, 255697817227957, 249351849487225, 242973263954532,
    236562175128421, 230118696461856, 223642940376960, 217135018279471, 210595040572936,
    204023116672633, 197419355019238, 190783863092242, 184116747423117, 177418113608247,
    170688066321619, 163926709327286, 157134145491608, 150310476795265, 143455804345067,
    136570228385545, 129653848310338, 122706762673383, 115729069199906, 108720864797219,
    101682245565335, 94613306807389, 87514143039892, 80384848002797, 73225514669402,
    66036235256075, 58817101231823, 51568203327697, 44289631546033, 36981475169542,
    29643822770255, 22276762218308, 14880380690587, 7454764679232]
private def phb_m16_r256_3 : List ℕ :=
  pCat phb_m16_r256_3_p0
    (pCat phb_m16_r256_3_p1
    (pCat phb_m16_r256_3_p2
      phb_m16_r256_3_p3))
private def pvn_m16_r256_3_0_p0 : List ℕ :=
  [1999969698555583, 2000061208547779, 2000072877480072, 2000048277917572, 2000003360638753,
    2000048356324472, 1999945882908371, 1999982835432488, 2000032098019725, 2000053681685751,
    2000030733920348, 2000016847321078, 2000050122937649, 2000042250971654, 2000001024825506,
    2000041349804979, 2000050884021276, 2000022211865815, 1999976308229617, 1999947725300038,
    2000043472962434, 2000004607254436, 2000038309626482, 2000056268986405, 2000038215641703,
    1999996472714617, 2000044291716246, 1999939680061927, 2000042765648255, 2000002202496762,
    2000040589934516, 2000065204266326, 2000060121173841, 2000028371183849, 2000015951024763,
    1999943960999280, 1999922111464397, 1999925528135063, 1999951913984589, 1999992720050879,
    1999962111459565, 1999921992795438, 1999893808765252, 1999879874358048, 1999878785218497,
    1999887817081553, 2000096361962405, 2000077239120734, 2000056201648917, 2000029965969551,
    1999987859248115, 2000094745066714, 2000269522600699, 2000634673044938, 2001361203406816,
    2002726370461221, 2005149192852694, 2009215974858371, 2015680469712165, 2025423135219206,
    2039356186011377, 2058269660767119, 2082630996982658, 2112371790102343]
private def pvn_m16_r256_3_0_p1 : List ℕ :=
  [2146711633462304, 2184073622977199, 2222136242720157, 2258041257165017, 2288740274979602,
    2311423459038856, 2323945936762019, 2325161560696804, 2315092521246083, 2294901178169750,
    2266676146918374, 2233085351218870, 2196973668881007, 2160986333295656, 2127282633094375,
    2097374930031145, 2072095683440718, 2051669044377617, 2035848864999090, 2024082378263449,
    2015665623958097, 2009868580605167, 2006020620690287, 2003557228721473, 2002035404028946,
    2001127765735102, 2000604995187358, 2000314165046310, 2000157876552181, 2000076751361174,
    1999963917690739, 1999983603440965, 1999992801296912, 2000003051953303, 2000001248795567,
    2000000492893986, 2000000187549470, 2000000068757954, 2000000024272381, 2000000008245431,
    2000000002693674, 2000000000845690, 2000000000254973, 2000000000073763, 1999999999979544,
    2000000000005429, 1999999999998624, 2000000000000330, 2000000000000072, 2000000000000013,
    2000000000000001]
private def pvn_m16_r256_3_0 : List ℕ :=
  pCat pvn_m16_r256_3_0_p0
      pvn_m16_r256_3_0_p1
private def pvn_m16_r256_3_1_p0 : List ℕ :=
  [1999961067061662, 1999977661071734, 2000003736711769, 2000006857957624, 1999995787704814,
    1999930417602091, 1999992652070064, 1999949103395296, 2000008543162439, 1999992065215116,
    2000073345740265, 1999988188189604, 2000010400920762, 2000038995742483, 2000012344071833,
    2000042782476819, 2000101839253815, 2000050865848912, 1999983847089190, 1999997777253790,
    2000023818109523, 1999977959081729, 2000025613110099, 1999968599907536, 1999988691644895,
    2000002350376947, 2000007837683739, 2000066906136710, 2000011825288508, 2000016868121406,
    2000033664242247, 1999987332172486, 2000020861475179, 2000051893866592, 2000022180058062,
    2000042283528019, 2000067302110998, 2000025332533760, 1999998295078080, 2000015531567022,
    2000005188612350, 1999969689871559, 1999973478549860, 2000013837944218, 2000035905158182,
    2000025279150513, 2000016572787604, 2000032345281611, 2000050997570598, 2000039523263720,
    2000001287891762, 1999973341024265, 1999978522697144, 2000001112451418, 2000016620398688,
    2000027302908986, 2000049811131656, 2000081147221963, 2000087887261343, 2000051868743291,
    1999981919969382, 1999937986917953, 1999929610046102, 1999985817601411]
private def pvn_m16_r256_3_1_p1 : List ℕ :=
  [2000015273328209, 2000048528817961, 1999992075762997, 1999951739483083, 1999882546232737,
    1999858493802613, 1999875792055359, 1999893265008390, 1999949069812659, 1999979016951532,
    1999993326667554, 2000017041878774, 2000007820544323, 2000002453640845, 2000012638231968,
    1999997221636348, 1999978041801114, 1999948839426023, 1999859837778660, 1999741761378673,
    1999680048340456, 1999817059354514, 2000504740957470, 2002350147152646, 2006163201015724,
    2012972485025466, 2023963900033684, 2040226683445502, 2062481739923591, 2090887358249870,
    2124839727475340, 2162820971565934, 2202464819204104, 2240843955553655, 2274840023501923,
    2301533044640481, 2318613854282624, 2324742540752447, 2319720312498236, 2304432176725614,
    2280632615911829, 2250658336404237, 2217104617486543, 2182492261749412, 2148981726408383,
    2118195638931104, 2091168752568881, 2068395099624813, 2049925178241273, 2035479735858885,
    2024565093923665, 2016581726459781, 2010916284881124, 2007007499500167, 2004382190933011,
    2002665408943855, 2001573565614369, 2000899682901383, 2000497137316932, 2000265043626737,
    2000136187986717, 2000067419202696, 2000032171363142, 2000014820300599]
private def pvn_m16_r256_3_1_p2 : List ℕ :=
  [2000006608982952, 2000002864895689, 2000001214115791, 2000000506622819, 2000000209805246,
    2000000086869240, 2000000036147776, 2000000015140361, 2000000006367863, 2000000002675047,
    2000000001114957, 2000000000458111, 2000000000184555, 2000000000072606, 2000000000027816,
    2000000000010357, 2000000000003742, 2000000000001308, 2000000000000441, 2000000000000140,
    2000000000000041, 2000000000000010, 2000000000000001]
private def pvn_m16_r256_3_1 : List ℕ :=
  pCat pvn_m16_r256_3_1_p0
    (pCat pvn_m16_r256_3_1_p1
      pvn_m16_r256_3_1_p2)
private def pvn_m16_r256_3_2_p0 : List ℕ :=
  [2000043669676913, 1999947086897951, 2000012583051939, 1999993173055238, 1999981817328305,
    1999990699242812, 1999984885208213, 1999938403747106, 1999991130769292, 2000000518503788,
    2000027717466280, 1999995010415459, 1999957142710505, 2000040389888367, 2000024841883263,
    1999957107872720, 1999974346698674, 1999973529506371, 1999965633138207, 1999982593477904,
    1999960150053626, 1999959792344067, 2000022545409859, 2000040002842141, 2000004944299599,
    2000004673630657, 2000009960190671, 1999980212366265, 1999982294568756, 2000034785371880,
    2000060479337566, 2000044721094690, 2000041537742015, 2000049825738009, 2000031183538369,
    2000011054244718, 2000020497138065, 2000043315273861, 2000021247021212, 1999996218349497,
    1999973668470711, 1999999938193097, 1999983360030338, 1999993999823168, 1999982671114960,
    2000022687607416, 2000036561587589, 2000025495315278, 2000014469075506, 1999993471189771,
    2000018060378709, 2000024071426714, 2000012024310360, 2000012074801649, 2000008569942226,
    2000041302996447, 2000068863945411, 2000051386790623, 2000033886718238, 2000014321970759,
    2000005177604692, 2000020733716686, 2000009628830745, 1999981463859169]
private def pvn_m16_r256_3_2_p1 : List ℕ :=
  [1999979404565780, 1999986923042201, 2000004888222970, 2000033739855727, 2000035001137871,
    2000023378259269, 2000035428203974, 2000045080801769, 2000033677656789, 2000015153851670,
    1999980756383146, 1999943369581997, 1999953538189226, 2000009537978718, 2000063093233483,
    2000096426703419, 2000101815761650, 2000060550253928, 1999997175131348, 1999965337638455,
    1999971667711985, 1999990532595797, 2000017914718349, 2000046528912768, 2000043942829598,
    2000002771110865, 1999956542325502, 1999924251342381, 1999896062416083, 1999877376346538,
    1999888634142260, 1999921855442941, 1999947481324508, 1999959865988681, 1999974101060977,
    1999986933488030, 1999982086122843, 1999970338335098, 1999988294078574, 2000053989154458,
    2000145023507508, 2000211932404954, 2000178919864730, 1999928264911983, 1999332451223100,
    1998371117567000, 1997286382095189, 1996702684931714, 1997675372150345, 2001655485291334,
    2010340131299165, 2025378580994616, 2047965493088318, 2078430481881056, 2115956791983421,
    2158517699196278, 2203051574944846, 2245845030644765, 2283059489193251, 2311306293594900,
    2328153630672092, 2332455789160390, 2324440988950911, 2305561294238844]
private def pvn_m16_r256_3_2_p2 : List ℕ :=
  [2278166381120633, 2245091088494839, 2209243803612249, 2173261261556228, 2139268425375771,
    2108756877891405, 2082573844970950, 2060997788251108, 2043867236799276, 2030728415269414,
    2020973418553376, 2013951153426128, 2009044213761244, 2005713352600434, 2003516055608791,
    2002107238563092, 2001229413570575, 2000697984898094, 2000385493675828, 2000207065551098,
    2000108158838507, 2000054938987457, 2000027141138242, 2000013044799065, 2000006102608333,
    2000002780655660, 2000001235090892, 2000000535328503, 2000000226695647, 2000000093923430,
    2000000038131100, 2000000015193608, 2000000005951400, 2000000002295126, 2000000000872520,
    2000000000327287, 2000000000121194, 2000000000044299, 2000000000015973, 2000000000005674,
    2000000000001978, 2000000000000676, 2000000000000223, 2000000000000069, 2000000000000019,
    2000000000000004]
private def pvn_m16_r256_3_2 : List ℕ :=
  pCat pvn_m16_r256_3_2_p0
    (pCat pvn_m16_r256_3_2_p1
      pvn_m16_r256_3_2_p2)
private def pvn_m16_r256_3_3_p0 : List ℕ :=
  [2000038239131893, 2000029183187870, 2000052549720869, 2000024555630854, 1999977166455381,
    1999999185933510, 2000012556393413, 1999984419432534, 1999992718551901, 2000012514403599,
    1999981494359056, 1999965526657868, 2000014487399633, 2000041892550719, 1999995834994049,
    1999952013870099, 1999959024720439, 1999977194808404, 1999981207175262, 1999998990509888,
    2000004930335211, 1999989414597406, 1999957856323362, 1999996004137977, 2000019959631451,
    2000035577217298, 1999985251574304, 1999991808543562, 2000003691152086, 2000006110116326,
    1999994831781765, 1999971228212236, 1999989248335895, 1999977201209923, 1999949932789694,
    1999950453541437, 1999963268332473, 2000002733435085, 2000018465876168, 2000004636463568,
    2000013841512393, 2000013395302465, 1999996147774108, 1999984847480678, 1999972035850677,
    1999989881546053, 2000031561019894, 2000040090255496, 2000031769331127, 2000031383919595,
    2000027961161844, 2000036847121983, 2000047258796209, 2000030884629894, 2000020491748083,
    2000034284562898, 2000038084470327, 2000027674466401, 2000011021201804, 1999981280710696,
    1999967451146208, 1999989885892079, 2000008129057842, 2000001925035941]
private def pvn_m16_r256_3_3_p1 : List ℕ :=
  [1999998051450617, 2000002167217543, 2000009342535077, 2000028010458881, 2000037658197867,
    2000013590993403, 1999986856973737, 1999991830197385, 2000010125211599, 2000021878068928,
    2000032513844865, 2000035663159633, 2000027717413378, 2000032629828288, 2000053601143810,
    2000055648191148, 2000029917821424, 2000007340205143, 1999999983990183, 1999995438489500,
    1999995263147348, 2000001646673110, 1999997024258612, 1999981562868130, 1999988480672858,
    2000029160752957, 2000068789269008, 2000076813533072, 2000056131346386, 2000015618388728,
    1999963237117947, 1999929147057285, 1999946628211243, 2000004857858524, 2000058308105228,
    2000081066775020, 2000078926339148, 2000057684783505, 2000018762639522, 1999982581281861,
    1999978465990016, 2000006379971346, 2000035991765932, 2000046607668943, 2000043439286504,
    2000031999235960, 2000003535959362, 1999956701641385, 1999912582359187, 1999892793058295,
    1999895394345784, 1999906497865307, 1999925053957611, 1999957805788173, 1999992146099992,
    1999992901784713, 1999936873081369, 1999848033355732, 1999797611312201, 1999873044632360,
    2000135953732887, 2000571292369861, 2001026185070266, 2001172577552506]
private def pvn_m16_r256_3_3_p2 : List ℕ :=
  [2000561293103959, 1998812372633973, 1995910292423694, 1992498383001242, 1990043172027517,
    1990770492394626, 1997337147468171, 2012275364758885, 2037322519133606, 2072808636801335,
    2117289526505188, 2167562165906947, 2219090721573166, 2266748012297157, 2305688150851813,
    2332141555488412, 2343962548322306, 2340838663370964, 2324159408221005, 2296616135389811,
    2261649592638838, 2222873025817446, 2183579852158633, 2146405620099538, 2113167457765793,
    2084863361850221, 2061787257206483, 2043706476725886, 2030053398874013, 2020096573670124,
    2013072594854809, 2008273712220194, 2005095528124364, 2003053876677598, 2001781110909446,
    2001010880431860, 2000558298048062, 2000300040913779, 2000156906609848, 2000079847033665,
    2000039542022900, 2000019058343484, 2000008941305531, 2000004084046858, 2000001816607688,
    2000000787121588, 2000000332342397, 2000000136794749, 2000000054915183, 2000000021511771,
    2000000008227381, 2000000003074013, 2000000001122728, 2000000000401081, 2000000000140228,
    2000000000048006, 2000000000016095, 2000000000005282, 2000000000001694, 2000000000000530,
    2000000000000158, 2000000000000042, 2000000000000009, 2000000000000001]
private def pvn_m16_r256_3_3 : List ℕ :=
  pCat pvn_m16_r256_3_3_p0
    (pCat pvn_m16_r256_3_3_p1
      pvn_m16_r256_3_3_p2)
private def phb_m16_r256_4_p0 : List ℕ :=
  [107359169704316, 151362748095303, 184809830815622, 212740617835481, 237113844462411,
    258937233387319, 278811262800908, 297128367071930, 314161952802809, 330111680294380,
    345128724021281, 359330877624261, 372812090560089, 385648758454188, 397904024476573,
    409630810916348, 420874011506133, 431672112389143, 442058414017557, 452061968009825,
    461708306355985, 471020016673726, 480017201525680, 488717849182744, 497138135880881,
    505292674461531, 513194720602158, 520856345173458, 528288579298355, 535501537229172,
    542504521061953, 549306110472699, 555914240019787, 562336266060681, 568579024943351,
    574648883827488, 580551785248327, 586293286342313, 591878593498143, 597312593070700,
    602599878692813, 607744775635793, 612751362600588, 617623491264247, 622364803858872,
    626978749020615, 631468596113011, 635837448200994, 640088253828259, 644223817730629,
    648246810600956, 652159778006570, 655965148547726, 659665241334806, 663262272852749,
    666758363273167, 670155542267670, 673455754369872, 676660863928290, 679772659687742,
    682792859032817, 685723111923446, 688565004549505, 691320062728600]
private def phb_m16_r256_4_p1 : List ℕ :=
  [693989755068786, 696575495915803, 699078648102507, 701500525516474, 703842395500259,
    706105481097408, 708290963156158, 710399982301650, 712433640786517, 714393004228859,
    716279103245798, 718092934990139, 719835464597010, 721507626546759, 723110325949919,
    724644439759519, 726110817915639, 727510284426690, 728843638391564, 730111654966473,
    731315086279985, 732454662299535, 733531091652402, 734545062403956, 735497242795742,
    736388281945807, 737218810513489, 737989441330718, 738700770001777, 739353375473267,
    739947820575967, 740484652540119, 740964403485577, 741387590888171, 741754718023525,
    742066274389511, 742322736108418, 742524566309862, 742672215495385, 742766121885633,
    742806711750953, 742794399726165, 742729589110268, 742612672151734, 742444030320035,
    742224034564009, 741953045557607, 741631413933543, 741259480505350, 740837576478277,
    740366023649462, 739845134597775, 739275212863702, 738656553119610, 737989441330718,
    737274154907070, 736510962846772, 735700125870775, 734841896549408, 733936519420897,
    732984231102060, 731985260391352, 730939828364430, 729848148462387]
private def phb_m16_r256_4_p2 : List ℕ :=
  [728710426572766, 727526861103491, 726297643049801, 725022956054267, 723702976459973,
    722337873356907, 720927808621602, 719472936950052, 717973405883921, 716429355830028,
    714840920073104, 713208224781771, 711531389007720, 709810524677989, 708045736580299,
    706237122341326, 704384772397807, 702488769960354, 700549190969821, 698566104046068,
    696539570428930, 694469643911186, 692356370763317, 690199789649775, 687999931536530,
    685756819589562, 683470469064006, 681140887183572, 678768073009890, 676352017301338,
    673892702360938, 671390101872814, 668844180726707, 666254894829987, 663622190906552,
    660946006281963, 658226268654119, 655462895848702, 652655795558590, 649804865066341,
    646909990948808, 643971048762856, 640987902711069, 637960405286258, 634888396893470,
    631771705448106, 628610145948633, 625403520022261, 622151615441798, 618854205611779,
    615511049021778, 612121888664636, 608686451417160, 605204447380602, 601675569178034,
    598099491205419, 594475868832942, 590804337552817, 587084512069447, 583315985327409,
    579498327472333, 575631084739236, 571713778262350, 567745902799898]
private def phb_m16_r256_4_p3 : List ℕ :=
  [563726925366582, 559656283765841, 555533385013067, 551357603640077, 547128279870050,
    542844717650989, 538506182534433, 534111899384625, 529661049901654, 525152769940172,
    520586146603040, 515960215086816, 511273955253095, 506526287896438, 501716070675884,
    496842093672696, 491903074531981, 486897653140065, 481824385782770, 476681738721916,
    471468081118257, 466181677218339, 460820677710190, 455383110137902, 449866868247579,
    444269700116202, 438589194889988, 432822767928883, 426967644117758, 421020839061211,
    414979137825801, 408839070828606, 402596886391185, 396248519379308, 389789555225974,
    383215188481347, 376520174839147, 369698775342301, 362744691154665, 355650986877308,
    348409999855540, 341013232222021, 333451221488739, 325713384245746, 317787825814610,
    309661106343409, 301317950521324, 292740883379193, 283909767812969, 274801209372038,
    265387778602942, 255636977626547, 245509840045244, 234958991551363, 223925893494755,
    212336804984032, 200096650704235, 187079291708395, 173111227342496, 157942329832115,
    141188214594707, 122201052315319, 99716288962233, 70465865670822]
private def phb_m16_r256_4 : List ℕ :=
  pCat phb_m16_r256_4_p0
    (pCat phb_m16_r256_4_p1
    (pCat phb_m16_r256_4_p2
      phb_m16_r256_4_p3))
private def pvn_m16_r256_4_0_p0 : List ℕ :=
  [1999961760868107, 2000029183187870, 1999947450279131, 1999975444369146, 1999977166455381,
    1999999185933510, 2000012556393413, 2000015580567466, 1999992718551901, 2000012514403599,
    1999981494359056, 1999965526657868, 2000014487399633, 2000041892550719, 2000004165005951,
    1999952013870099, 2000040975279561, 1999977194808404, 1999981207175262, 2000001009490112,
    1999995069664789, 1999989414597406, 1999957856323362, 2000003995862023, 1999980040368549,
    2000035577217298, 1999985251574304, 2000008191456438, 2000003691152086, 2000006110116326,
    2000005168218235, 1999971228212236, 1999989248335895, 1999977201209923, 2000050067210306,
    2000049546458563, 2000036731667527, 2000002733435085, 2000018465876168, 2000004636463568,
    1999986158487607, 2000013395302465, 1999996147774108, 2000015152519322, 1999972035850677,
    2000010118453947, 2000031561019894, 1999959909744504, 1999968230668873, 1999968616080405,
    2000027961161844, 2000036847121983, 2000047258796209, 2000030884629894, 1999979508251917,
    1999965715437102, 2000038084470327, 2000027674466401, 2000011021201804, 1999981280710696,
    1999967451146208, 2000010114107921, 2000008129057842, 1999998074964059]
private def pvn_m16_r256_4_0_p1 : List ℕ :=
  [1999998051450617, 1999997832782457, 2000009342535077, 2000028010458881, 2000037658197867,
    2000013590993403, 2000013143026263, 1999991830197385, 1999989874788401, 2000021878068928,
    1999967486155135, 2000035663159633, 1999972282586622, 1999967370171712, 1999946398856190,
    2000055648191148, 1999970082178576, 1999992659794857, 1999999983990183, 1999995438489500,
    2000004736852652, 2000001646673110, 2000002975741388, 2000018437131870, 2000011519327142,
    1999970839247043, 1999931210730992, 2000076813533072, 1999943868653614, 2000015618388728,
    2000036762882053, 2000070852942715, 1999946628211243, 2000004857858524, 2000058308105228,
    2000081066775020, 2000078926339148, 2000057684783505, 2000018762639522, 1999982581281861,
    2000021534009984, 1999993620028654, 2000035991765932, 2000046607668943, 2000043439286504,
    2000031999235960, 1999996464040638, 2000043298358615, 2000087417640813, 2000107206941705,
    2000104605654216, 2000093502134693, 2000074946042389, 2000042194211827, 1999992146099992,
    1999992901784713, 2000063126918631, 2000151966644268, 1999797611312201, 1999873044632360,
    1999864046267113, 1999428707630139, 1998973814929734, 1998827422447494]
private def pvn_m16_r256_4_0_p2 : List ℕ :=
  [1999438706896041, 1998812372633973, 1995910292423694, 1992498383001242, 1990043172027517,
    1990770492394626, 2002662852531829, 2012275364758885, 2037322519133606, 2072808636801335,
    2117289526505188, 2167562165906947, 2219090721573166, 2266748012297157, 2305688150851813,
    2332141555488412, 2343962548322306, 2340838663370964, 2324159408221005, 2296616135389811,
    2261649592638838, 2222873025817446, 2183579852158633, 2146405620099538, 2113167457765793,
    2084863361850221, 2061787257206483, 2043706476725886, 2030053398874013, 2020096573670124,
    2013072594854809, 2008273712220194, 2005095528124364, 2003053876677598, 2001781110909446,
    2001010880431860, 2000558298048062, 2000300040913779, 2000156906609848, 2000079847033665,
    2000039542022900, 2000019058343484, 2000008941305531, 2000004084046858, 2000001816607688,
    2000000787121588, 2000000332342397, 1999999863205251, 1999999945084817, 2000000021511771,
    2000000008227381, 2000000003074013, 2000000001122728, 1999999999598919, 1999999999859772,
    1999999999951994, 2000000000016095, 1999999999994718, 2000000000001694, 2000000000000530,
    2000000000000158, 2000000000000042, 2000000000000009, 2000000000000001]
private def pvn_m16_r256_4_0 : List ℕ :=
  pCat pvn_m16_r256_4_0_p0
    (pCat pvn_m16_r256_4_0_p1
      pvn_m16_r256_4_0_p2)
private def pvn_m16_r256_4_1_p0 : List ℕ :=
  [1999956608370332, 1999967038808478, 1999970802403832, 1999995463390827, 2000017730775807,
    1999980962522062, 2000018962507566, 1999982803859819, 1999997886978666, 1999998312968208,
    1999923185562123, 1999999734553406, 1999991358185628, 2000004275415008, 1999952574011847,
    1999975213687387, 2000047963668022, 2000017085318929, 2000022538356763, 1999974676679944,
    1999993126996180, 1999988596174481, 1999992963881129, 2000002288388602, 1999987444075124,
    2000015607895051, 2000003520185280, 2000024363875193, 1999995628221991, 1999973847916700,
    2000018662916765, 1999979683714080, 2000014541582358, 2000003320776919, 1999993372273366,
    1999985794795644, 1999971367959935, 1999973979028997, 2000017810081334, 1999993541118954,
    1999972239721364, 1999980769087122, 1999996574708303, 2000036148655682, 2000010037907252,
    1999997317609602, 2000025387461233, 1999986502635746, 1999954245016681, 1999973360929883,
    2000001888792494, 2000026002296471, 2000005699303851, 2000043127918446, 1999987617921432,
    2000060433914680, 1999992083692782, 2000045280618658, 2000006691915749, 2000002701914998,
    1999959531737495, 2000002085132683, 2000032457365452, 2000038345720278]
private def pvn_m16_r256_4_1_p1 : List ℕ :=
  [2000033022539517, 1999960872827204, 1999927965767964, 2000010978890802, 1999957721018574,
    2000046466559806, 1999993083913620, 2000046842889382, 1999940363670575, 2000045272950518,
    2000034344495752, 1999996826496550, 2000015729950444, 2000020871257289, 1999995234902594,
    1999995228816617, 2000019241786454, 1999979550495157, 2000028466338307, 1999995694712106,
    1999947532671617, 1999974876725577, 2000053196652997, 2000030156962508, 1999964607530468,
    2000043091917092, 2000035328477667, 1999978961486642, 2000002730064280, 2000043493327822,
    2000020537919023, 1999995223305664, 1999963649034607, 2000025200461753, 1999963988921059,
    2000017045365345, 1999946437030809, 2000023109145071, 1999998300809319, 1999947107827602,
    2000051979763995, 1999862252990932, 2000162171997248, 1999895225981627, 2000218306746277,
    1999618484694631, 2000588449475062, 1999025384471476, 2001247957535263, 1998679927553622,
    2001136602109902, 1999395334075003, 1999866974798729, 2000785294065066, 1998884277645523,
    2000703243220221, 2000391490154516, 1999086887990197, 2000737975248644, 2000241413755497,
    1999263006525143, 2000490732280900, 2000238548125974, 1999416609754125]
private def pvn_m16_r256_4_1_p2 : List ℕ :=
  [2000409721972545, 2000446726830338, 1999232897362919, 1999816741657970, 2001015001061081,
    2000102265783961, 1998925308813344, 1999969627843418, 2001380550228255, 2000607663893004,
    1998889276534840, 1998879036556969, 2000501881199018, 2001531691560974, 2000861357631378,
    1999477735466045, 1998744505418983, 1998953535843674, 1999610729520393, 2000359872416957,
    2001184974825939, 2001880271182984, 2001642060195792, 1999349504399809, 1994381864684086,
    1987426237660942, 1980809492912208, 1978184152015889, 1983679997007106, 2000792243473187,
    2031339929958307, 2074783490639228, 2128091992991790, 2186191315909063, 2242872556478554,
    2291927537121704, 2328231696869477, 2348537296328743, 2351833731650808, 2339252191430987,
    2313604786407619, 2278712982207351, 2238695958559213, 2197363486353340, 2157799897559765,
    2122163227198091, 2091675674451539, 2066751219247107, 2047196020376353, 2032425581396031,
    2021659712039876, 2014073636484126, 2008898668922718, 2005477205500272, 2003282676596096,
    2001916113843332, 2001089468869163, 2000603536233806, 2000325847456250, 2000171501204535,
    2000087996763003, 2000043991484944, 2000021398783981, 2000010106969006]
private def pvn_m16_r256_4_1_p3 : List ℕ :=
  [2000004623472996, 2000002043410074, 2000000870843363, 2000000357496461, 2000000141372777,
    2000000053911056, 2000000019860108, 2000000007082089, 2000000002448807, 2000000000821691,
    2000000000267451, 2000000000084311, 2000000000025683, 2000000000007543, 2000000000002131,
    2000000000000578, 2000000000000149, 2000000000000035, 2000000000000007]
private def pvn_m16_r256_4_1 : List ℕ :=
  pCat pvn_m16_r256_4_1_p0
    (pCat pvn_m16_r256_4_1_p1
    (pCat pvn_m16_r256_4_1_p2
      pvn_m16_r256_4_1_p3))
private def pvn_m16_r256_4_2_p0 : List ℕ :=
  [2000002298172033, 1999967201871607, 1999991204536036, 2000015697795109, 1999936248933896,
    1999985495336060, 1999986438136479, 1999950689466220, 1999997890567785, 1999978173729575,
    2000013503778756, 2000008451326156, 1999969536202805, 1999994298886506, 2000004285861555,
    2000036439092213, 2000017532681134, 1999960898443265, 1999982722929200, 1999956544378652,
    2000007430744263, 2000007955908740, 1999975710927154, 1999973082558567, 1999973699450180,
    1999957505559847, 1999992319782043, 2000022192289453, 2000005284832003, 2000016788058174,
    2000006134542283, 1999994132768249, 2000014808556126, 2000001414421978, 1999973447030626,
    2000005253032567, 1999965140053898, 2000023862903588, 1999973312103104, 2000033562541297,
    1999980797555291, 2000045106385768, 1999995670321575, 1999965877931200, 1999988357233782,
    2000023841281143, 2000018991778457, 2000003043550953, 1999976985183250, 2000012276818722,
    1999961800356516, 2000044265875860, 1999931464639725, 2000031976886083, 1999981545417957,
    1999990072193904, 1999964648290348, 1999975074666788, 1999999889094145, 1999991036996325,
    2000044792928303, 2000015739254315, 2000003964337246, 2000003926475165]
private def pvn_m16_r256_4_2_p1 : List ℕ :=
  [1999995044839468, 1999936878924052, 1999995603574470, 2000038397272638, 1999971629126000,
    1999988143674332, 2000001575593914, 2000011643906665, 2000023443957629, 2000072503180803,
    2000040753417109, 1999988771433040, 1999967294010282, 2000008891824581, 1999965169457252,
    2000088803819303, 2000031013965065, 1999988159105087, 2000006826802229, 1999974515838253,
    2000065745635042, 1999799676087852, 2000220360188719, 1999744356979781, 2000350313690188,
    1999468931297272, 2000659049610780, 1999221067303017, 2000989447461054, 1998945265481607,
    2000985358217981, 1999344047558735, 2000183677721710, 2000370083490523, 1999256447547289,
    2000902136158244, 1999383350367890, 2000045755800473, 2000464655787993, 1999229192020962,
    2000625188050638, 1999915624268229, 1999483761668642, 2000755807733009, 1999608365575151,
    1999749121288479, 2000713087807334, 1999498128587356, 1999875471592182, 2000706100247425,
    1999512347657165, 1999749641823642, 2000639990642751, 1999708158767414, 1999662181213593,
    2000532987700081, 1999891946368209, 1999534938961056, 2000352102475547, 2000121348211125,
    1999552814860366, 2000221315786265, 2000393804648320, 1999542132238270]
private def pvn_m16_r256_4_2_p2 : List ℕ :=
  [1999750926433332, 2000578638006824, 2000056613228551, 1999343981943705, 2000109959723468,
    2000731500238543, 1999789823830262, 1999149551247568, 2000150982765401, 2000906046968620,
    1999990871262445, 1999112539326780, 1999880176828871, 2000949687162744, 2000489034212111,
    1999270863008796, 1999257334962966, 2000447996200447, 2001038513145584, 2000199970921882,
    1999127829739557, 1999211044284734, 2000249592016621, 2000955020539559, 2000628150721607,
    1999785754101766, 1999320397035883, 1999528183112331, 2000055279245538, 2000483329285183,
    2000699372851779, 2000738563036803, 2000500241028772, 1999798034137847, 1998719482421218,
    1997873024864139, 1998167842997178, 2000172517048136, 2003461455772164, 2006419942365458,
    2006734729954954, 2002431541748184, 1993037255395667, 1980360808324188, 1968519512639250,
    1963118021286406, 1969797966611617, 1992602565675569, 2032668327195699, 2087648347050151,
    2152033013655862, 2218255023489666, 2278244546487885, 2325003275068240, 2353808605246891,
    2362809079256545, 2352966311087478, 2327469524888878, 2290850498435122, 2248046081501108,
    2203607851784447, 2161174349224340, 2123232938759721, 2091129858571071]
private def pvn_m16_r256_4_2_p3 : List ℕ :=
  [2065249630593105, 2045277614956452, 2030473249857700, 2019905459949442, 2012626634371173,
    2007781652169466, 2004661248383965, 2002714767621356, 2001537785883488, 2000847426102921,
    2000454392186811, 2000237095355956, 2000120383506139, 2000059469050954, 2000028573302224,
    2000013346967548, 2000006057863834, 2000002669968120, 2000001142012764, 2000000473757817,
    2000000190517290, 2000000074236505, 2000000028019698, 2000000010241741, 2000000003624833,
    2000000001242146, 2000000000412106, 2000000000132365, 2000000000041153, 2000000000012380,
    2000000000003601, 2000000000001008, 2000000000000269, 2000000000000067, 2000000000000014,
    2000000000000001]
private def pvn_m16_r256_4_2 : List ℕ :=
  pCat pvn_m16_r256_4_2_p0
    (pCat pvn_m16_r256_4_2_p1
    (pCat pvn_m16_r256_4_2_p2
      pvn_m16_r256_4_2_p3))
private def pvn_m16_r256_4_3_p0 : List ℕ :=
  [1999992520668384, 2000033403136385, 2000026490725651, 1999950541445089, 1999975809193463,
    2000016170069223, 1999990962069461, 1999996113865798, 2000006319918618, 1999962778700722,
    1999998665285672, 1999978615595992, 1999980572598552, 1999992363382959, 1999965752870761,
    1999952747853494, 1999981486306086, 2000004582974479, 1999994095548994, 2000010282384111,
    1999994231633433, 1999968039432923, 1999956775114268, 2000039749980908, 1999983414840277,
    2000056793957949, 1999991261127771, 2000015237867668, 1999970041660433, 1999982040342400,
    1999985357161969, 1999985953144172, 2000001337899365, 2000024728044443, 1999953235271849,
    2000010701097921, 1999925685623429, 2000007575835430, 1999939879846840, 2000024079550085,
    1999994394198827, 1999967573578845, 2000028253683755, 2000008649956017, 2000020228994282,
    1999990292473433, 2000006415155401, 2000001861343566, 2000011895946878, 1999995783633912,
    1999963007587120, 1999970605336177, 2000003224064273, 2000043828269444, 1999985448577624,
    2000007212845696, 2000008675879006, 1999985428728943, 1999984405936580, 2000036351996129,
    1999971347615527, 2000011111910586, 2000016688780962, 2000014734219972]
private def pvn_m16_r256_4_3_p1 : List ℕ :=
  [1999997940187476, 1999909687318295, 2000155337914192, 1999789848347164, 2000258774270977,
    1999650945811707, 2000475477105396, 1999375195939658, 2000692844026925, 1999147151862556,
    2000839880126642, 1999136419604625, 2000789026699472, 1999525764305744, 2000101954830705,
    2000341095756814, 1999314102388020, 2000771000386953, 1999371848084709, 2000279464745729,
    2000238624160140, 1999272741992994, 2000689201235978, 1999613246643682, 1999931975081598,
    2000556031007818, 1999388080738470, 2000420125111088, 2000121898469459, 1999416084467478,
    2000586240522732, 1999840173373074, 1999691155865082, 2000627627498674, 1999631643344323,
    1999836525705250, 2000585133282998, 1999541830080639, 1999892412619953, 2000555900875183,
    1999536380565254, 1999845884419882, 2000534756813752, 1999633039960886, 1999809148970770,
    2000556167555334, 1999756499099053, 1999651684700885, 2000495671050756, 1999998970436113,
    1999585804019870, 2000334820773831, 2000201843667663, 1999596408661686, 2000105970883865,
    2000307427790799, 1999664136679589, 1999884928245074, 2000419709265003, 1999884795752531,
    1999606433426633, 2000301003520703, 2000276264923143, 1999571810374545]
private def pvn_m16_r256_4_3_p2 : List ℕ :=
  [1999907970121807, 2000566936155624, 1999988809158238, 1999399872888908, 2000132340816702,
    2000640766261481, 1999817656711063, 1999375347517883, 2000241977053636, 2000628383093069,
    1999698756921853, 1999272229642764, 2000227778072918, 2000788680082282, 1999899312350844,
    1999168535674283, 1999897797170919, 2000793293211692, 2000319430656970, 1999316923674191,
    1999467823474557, 2000493018805019, 2000719316652243, 1999797463663521, 1999155141482592,
    1999740775588263, 2000681071268556, 2000666422078678, 1999783155543727, 1999248770485059,
    1999713451579106, 2000530010893639, 2000723460947847, 2000167442535929, 1999557093354694,
    1999490123863875, 1999890744296721, 2000293036767721, 2000413715386963, 2000312018197428,
    2000124802384844, 1999861130047262, 1999526340440699, 1999339518034225, 1999663275153152,
    2000609795117405, 2001702536992215, 2002011912338526, 2000801623875314, 1998261068044482,
    1995743882283965, 1995205351345516, 1998041366608858, 2003949180704879, 2010504920855040,
    2013841106169714, 2010271894938843, 1998223785648271, 1979622909836516, 1960064214403314,
    1947564052039797, 1950265681283196, 1973883656312794, 2019770464569184]
private def pvn_m16_r256_4_3_p3 : List ℕ :=
  [2084244633675887, 2159355227986042, 2234771446815695, 2300160201363345, 2347343517991350,
    2371695353484013, 2372544109811916, 2352664008058563, 2317161951066745, 2272149731926117,
    2223545974562240, 2176227351512648, 2133603517587210, 2097571354059494, 2068734987244337,
    2046759779212796, 2030747582889446, 2019558270305657, 2012042362827319, 2007181057360336,
    2004149093994627, 2002323605222647, 2001261644174329, 2000664299358281, 2000339230604727,
    2000168014223840, 2000080704047592, 2000037591013488, 2000016975299400, 2000007429634370,
    2000003150478183, 2000001293785542, 2000000514307728, 2000000197807261, 2000000073568667,
    2000000026444832, 2000000009182189, 2000000003077965, 2000000000995499, 2000000000310463,
    2000000000093296, 2000000000026994, 2000000000007508, 2000000000002003, 2000000000000508,
    2000000000000120, 2000000000000025, 2000000000000003]
private def pvn_m16_r256_4_3 : List ℕ :=
  pCat pvn_m16_r256_4_3_p0
    (pCat pvn_m16_r256_4_3_p1
    (pCat pvn_m16_r256_4_3_p2
      pvn_m16_r256_4_3_p3))
private def pvn_m16_r256_4_4_p0 : List ℕ :=
  [2000004051676614, 1999983400735147, 1999973749095676, 1999980070354281, 2000051171319021,
    2000038308071023, 2000002339217806, 2000005182920292, 1999993426403483, 1999983421374604,
    1999970247610672, 2000011854952535, 1999978304288942, 2000020959020968, 1999959693483093,
    2000048782796673, 1999978634515345, 1999976368689016, 1999989532644920, 2000000164134754,
    1999977147405588, 2000015818385150, 1999954668734182, 2000037337846298, 1999922190775511,
    1999984314002122, 1999960683954730, 1999971327886139, 2000019872620303, 1999982751680436,
    2000029278546822, 1999978684694177, 1999967138784634, 1999987326115879, 1999981070684961,
    1999982469735170, 2000000639696830, 2000039709504335, 2000005553275847, 2000020195211713,
    1999999002487216, 2000006109728465, 1999968401263966, 1999976614854747, 1999990694896849,
    2000017375111686, 2000011865275087, 1999956860611511, 2000088259219908, 1999794731974608,
    2000235558438284, 1999656938229357, 2000415446391012, 1999381383083824, 2000659148257449,
    1999253916088198, 2000804969958197, 1999177098313929, 2000729774707930, 1999470763285004,
    2000216438928431, 2000170184907060, 1999578684997492, 2000652314854281]
private def pvn_m16_r256_4_4_p1 : List ℕ :=
  [1999275824906587, 2000495724746018, 1999900890267234, 1999613265628781, 2000656276084464,
    1999359511003300, 2000344556690996, 2000139973728095, 1999474919563354, 2000624434411122,
    1999598138171504, 1999927843119216, 2000511751617501, 1999392989766917, 2000302260708283,
    2000223464125893, 1999467713860598, 2000460463455781, 1999896249960015, 1999649035201859,
    2000538648610789, 1999703030865985, 1999823269838072, 2000556588238755, 1999576853834277,
    1999825519317171, 2000456015125522, 1999588494630485, 1999964007934657, 2000469016440019,
    1999564880208648, 1999934491799459, 2000487520447030, 1999620507519265, 1999880259435441,
    2000527839127456, 1999719936099927, 1999719549236019, 2000425623447068, 1999819968443004,
    1999642741680874, 2000426106731382, 2000066736957754, 1999607633005388, 2000277639806872,
    2000223219390388, 1999592131889747, 2000056725842295, 2000374033439421, 1999755276029883,
    1999845379492586, 2000362107583184, 1999954814499627, 1999724218122736, 2000279987155893,
    2000161257849920, 1999617312199305, 2000009678375342, 2000370522078432, 1999780884379693,
    1999672328133961, 2000358072206597, 2000215313595195, 1999539708200869]
private def pvn_m16_r256_4_4_p2 : List ℕ :=
  [1999910078564827, 2000508688646035, 1999962517767205, 1999495871599167, 2000199772824592,
    2000551702662143, 1999734655270790, 1999465209133378, 2000341023148372, 2000545122073100,
    1999632858529054, 1999453526643018, 2000366443277828, 2000532698141627, 1999616638076663,
    1999435063902032, 2000376200889648, 2000651380674135, 1999719803718556, 1999296747932436,
    2000164533984691, 2000775057106724, 2000063561881119, 1999286590713199, 1999757918020660,
    2000623375904985, 2000413086373431, 1999505575936540, 1999402701867792, 2000249093087066,
    2000681859554415, 2000039653196900, 1999328415205811, 1999609311690914, 2000444717943059,
    2000639182427979, 1999966511588182, 1999378411577519, 1999617592006745, 2000293229230038,
    2000532302284764, 2000116260713689, 1999620295796084, 1999596546474903, 1999973180269099,
    2000300844022111, 2000329827857001, 2000169014478627, 1999995490988020, 1999836116299046,
    1999691229930307, 1999714283836334, 2000084043091390, 2000666435596653, 2000930694276154,
    2000374033226478, 1999132046317445, 1998138571827929, 1998514557939601, 2000557680956256,
    2003159090107192, 2004268909266510, 2002283518774251, 1997479788674151]
private def pvn_m16_r256_4_4_p3 : List ℕ :=
  [1992430082386354, 1990873025543536, 1995476527950342, 2005718612053104, 2017223937683935,
    2023218188584509, 2017647785605941, 1998566522388522, 1970133194282720, 1942139219323776,
    1927095681144615, 1935996506394652, 1974424551818996, 2040465673214691, 2125100664975140,
    2214764224362705, 2295024452604406, 2354100491711216, 2385200062732811, 2387222747702053,
    2363967697156887, 2322391082570466, 2270589527457549, 2216075221152389, 2164664300608501,
    2120041139517951, 2083871267919501, 2056246883211894, 2036249782822596, 2022472384719621,
    2013410930658391, 2007708880994397, 2004270120825750, 2002280042364500, 2001173776717057,
    2000582646375484, 2000278863541211, 2000128673633531, 2000057226440987, 2000024522552319,
    2000010120518821, 2000004020388935, 2000001536294525, 2000000564269761, 2000000199030565,
    2000000067349690, 2000000021839344, 2000000006777574, 2000000002010067, 2000000000568767,
    2000000000153254, 2000000000039234, 2000000000009513, 2000000000002172, 2000000000000463,
    2000000000000089, 2000000000000014, 2000000000000001]
private def pvn_m16_r256_4_4 : List ℕ :=
  pCat pvn_m16_r256_4_4_p0
    (pCat pvn_m16_r256_4_4_p1
    (pCat pvn_m16_r256_4_4_p2
      pvn_m16_r256_4_4_p3))
private def phb_m16_r256_5_p0 : List ℕ :=
  [107551906830945, 151634482882625, 185141611658026, 213122541573453, 237539524366529,
    259402091847737, 279311800219484, 297661788370431, 314725953737675, 330704315063279,
    345748318218670, 359975968314264, 373481383470097, 386341096461250, 398618363815852,
    410366202832032, 421629587838126, 432447074069802, 442852021762056, 452873534688413,
    462537190675352, 471865617891106, 480878954987539, 489595222529089, 498030625792192,
    506199803852072, 514116036183519, 521791415327523, 529236992210693, 536462899243015,
    543478455220173, 550292255220878, 556912248048065, 563345803265737, 569599769494855,
    575680525325788, 581594023962140, 587345832516834, 592941166725366, 598384921714871,
    603681699364924, 608835832711803, 613851407778764, 618732283157602, 623482107619154,
    628104335990755, 632602243505284, 636978938798467, 641237375707389, 645380364003089,
    649410579172996, 653330571354384, 657142773507463, 660849508906013, 664452998014128,
    667955364809670, 671358642608028, 674664779433750, 677875642982335, 680993025209855,
    684018646584042, 686954160026928, 689801154576003, 692561158788106]
private def phb_m16_r256_5_p1 : List ℕ :=
  [695235643907820, 697826026819995, 700333672804120, 702759898106536, 705105972345001,
    707373120758736, 709562526315902, 711675331689354, 713712641110550, 715675522110646,
    717565007156986, 719382095192519, 721127753085034, 722802916992514, 724408493650395,
    725945361586060, 727414372265449, 728816351176277, 730152098852026, 731422391840509,
    732627983620557, 733769605470082, 734847967288532, 735863758376529, 736817648175283,
    737710286968174, 738542306546732, 739314320843079, 740026926530759, 740680703595731,
    741276215879197, 741814011593819, 742294623814742, 742718570946795, 743086357169113,
    743398472858340, 743655394991527, 743857587529725, 744005501783242, 744099576759442,
    744140239493936, 744127905365919, 744062978398416, 743945851544083, 743776906957229,
    743556516252640, 743285040751766, 742962831716800, 742590230573121, 742167569120575,
    741695169734009, 741173345553451, 740602400664320, 739982630267996, 739314320843079,
    738597750297633, 737833188112686, 737020895477248, 736161125415077, 735254122903409,
    734300124983847, 733299360865600, 732252052021211, 731158412274954]
private def phb_m16_r256_5_p2 : List ℕ :=
  [730018647883994, 728832957612447, 727601532798437, 726324557414221, 725002208119463,
    723634654307712, 722222058146109, 720764574608369, 719262351501029, 717715529482976,
    716124242078218, 714488615681886, 712808769559396, 711084815838725, 709316859495714,
    707504998332305, 705649322947591, 703749916701567, 701806855671424, 699820208600209,
    697790036837698, 695716394273245, 693599327260394, 691438874533014, 689235067112663,
    686987928206913, 684697473098283, 682363709023453, 679986635042368, 677566241896816,
    675102511858046, 672595418562940, 670044926838207, 667450992512060, 664813562212752,
    662132573153327, 659407952901884, 656639619136581, 653827479384581, 650971430744037,
    648071359588181, 645127141250468, 642138639689693, 639105707133853, 636028183701481,
    632905896999042, 629738661692880, 626526279054073, 623268536474428, 619965206951683,
    616616048541839, 613220803776345, 609779199041679, 606290943918653, 602755730478519,
    599173232532697, 595543104832673, 591864982216278, 588138478696209, 584363186486276,
    580538674960410, 576664489539004, 572740150496604, 568765151684394]
private def phb_m16_r256_5_p3 : List ℕ :=
  [564738959160233, 560661009718272, 556530709309346, 552347431342395, 548110514856130,
    543819262548965, 539472938653915, 535070766643656, 530611926749221, 526095553273900,
    521520731681669, 516886495437019, 512191822570136, 507435631938130, 502616779149249,
    497734052112642, 492786166171259, 487771758769678, 482689383601883, 477537504176243,
    472314486725740, 467018592380799, 461647968509459, 456200639114751, 450674494161517,
    445067277683959, 439376574500196, 433599795330086, 427734160076459, 421776678986161,
    415724131354124, 409573041368640, 403319650616047, 396959886664160, 390489327020703,
    383903157608830, 377196124707393, 370362479056426, 363395910511763, 356289471223662,
    349035484781013, 341625438060630, 334049851586923, 326298122950017, 318358336117495,
    310217027109470, 301858893192039, 293266428024006, 284419458350081, 275294547720636,
    265864217439341, 256095911285068, 245950592905573, 235380802944206, 224327897658993,
    212718003774812, 200455875292235, 187415146812669, 173422006204117, 158225876648925,
    141441683496059, 122420434411504, 99895305166119, 70592369895029]
private def phb_m16_r256_5 : List ℕ :=
  pCat phb_m16_r256_5_p0
    (pCat phb_m16_r256_5_p1
    (pCat phb_m16_r256_5_p2
      phb_m16_r256_5_p3))
private def pvn_m16_r256_5_0_p0 : List ℕ :=
  [2000004051676614, 2000016599264853, 2000026250904324, 2000019929645719, 1999948828680979,
    2000038308071023, 1999997660782194, 2000005182920292, 2000006573596517, 1999983421374604,
    1999970247610672, 1999988145047465, 2000021695711058, 1999979040979032, 1999959693483093,
    2000048782796673, 1999978634515345, 1999976368689016, 2000010467355080, 2000000164134754,
    1999977147405588, 2000015818385150, 1999954668734182, 2000037337846298, 2000077809224489,
    2000015685997878, 1999960683954730, 1999971327886139, 1999980127379697, 2000017248319564,
    1999970721453178, 1999978684694177, 2000032861215366, 2000012673884121, 2000018929315039,
    1999982469735170, 1999999360303170, 2000039709504335, 1999994446724153, 2000020195211713,
    1999999002487216, 2000006109728465, 2000031598736034, 2000023385145253, 1999990694896849,
    2000017375111686, 2000011865275087, 1999956860611511, 1999911740780092, 1999794731974608,
    1999764441561716, 1999656938229357, 2000415446391012, 2000618616916176, 2000659148257449,
    1999253916088198, 1999195030041803, 1999177098313929, 1999270225292070, 1999470763285004,
    1999783561071569, 1999829815092940, 1999578684997492, 2000652314854281]
private def pvn_m16_r256_5_0_p1 : List ℕ :=
  [1999275824906587, 1999504275253982, 1999900890267234, 1999613265628781, 2000656276084464,
    1999359511003300, 1999655443309004, 1999860026271905, 1999474919563354, 2000624434411122,
    2000401861828496, 2000072156880784, 2000511751617501, 1999392989766917, 1999697739291717,
    1999776535874107, 2000532286139402, 2000460463455781, 1999896249960015, 1999649035201859,
    2000538648610789, 1999703030865985, 1999823269838072, 2000556588238755, 2000423146165723,
    2000174480682829, 2000456015125522, 1999588494630485, 2000035992065343, 2000469016440019,
    2000435119791352, 2000065508200541, 2000487520447030, 1999620507519265, 1999880259435441,
    2000527839127456, 1999719936099927, 1999719549236019, 2000425623447068, 1999819968443004,
    1999642741680874, 1999573893268618, 1999933263042246, 1999607633005388, 2000277639806872,
    2000223219390388, 2000407868110253, 2000056725842295, 2000374033439421, 1999755276029883,
    1999845379492586, 2000362107583184, 1999954814499627, 1999724218122736, 2000279987155893,
    2000161257849920, 2000382687800695, 1999990321624658, 2000370522078432, 2000219115620307,
    1999672328133961, 1999641927793403, 2000215313595195, 1999539708200869]
private def pvn_m16_r256_5_0_p2 : List ℕ :=
  [1999910078564827, 2000508688646035, 2000037482232795, 2000504128400833, 2000199772824592,
    2000551702662143, 2000265344729210, 1999465209133378, 2000341023148372, 2000545122073100,
    2000367141470946, 2000546473356982, 1999633556722172, 2000532698141627, 2000383361923337,
    2000564936097968, 2000376200889648, 2000651380674135, 2000280196281444, 2000703252067564,
    2000164533984691, 2000775057106724, 2000063561881119, 2000713409286801, 2000242081979340,
    2000623375904985, 2000413086373431, 1999505575936540, 2000597298132208, 2000249093087066,
    2000681859554415, 2000039653196900, 2000671584794189, 2000390688309086, 2000444717943059,
    2000639182427979, 2000033488411818, 2000621588422481, 2000382407993255, 2000293229230038,
    2000532302284764, 1999883739286311, 2000379704203916, 2000403453525097, 1999973180269099,
    2000300844022111, 2000329827857001, 2000169014478627, 2000004509011980, 1999836116299046,
    2000308770069693, 1999714283836334, 2000084043091390, 2000666435596653, 2000930694276154,
    2000374033226478, 2000867953682555, 2001861428172071, 1998514557939601, 1999442319043744,
    1996840909892808, 1995731090733490, 1997716481225749, 1997479788674151]
private def pvn_m16_r256_5_0_p3 : List ℕ :=
  [1992430082386354, 1990873025543536, 1995476527950342, 1994281387946896, 1982776062316065,
    1976781811415491, 1982352214394059, 2001433477611478, 2029866805717280, 2057860780676224,
    2072904318855385, 2064003493605348, 2025575448181004, 2040465673214691, 2125100664975140,
    2214764224362705, 2295024452604406, 2354100491711216, 2385200062732811, 2387222747702053,
    2363967697156887, 2322391082570466, 2270589527457549, 2216075221152389, 2164664300608501,
    2120041139517951, 2083871267919501, 2056246883211894, 2036249782822596, 2022472384719621,
    2013410930658391, 2007708880994397, 2004270120825750, 2002280042364500, 2001173776717057,
    2000582646375484, 2000278863541211, 2000128673633531, 2000057226440987, 2000024522552319,
    2000010120518821, 2000004020388935, 1999998463705475, 1999999435730239, 1999999800969435,
    1999999932650310, 1999999978160656, 1999999993222426, 1999999997989933, 2000000000568767,
    2000000000153254, 2000000000039234, 2000000000009513, 2000000000002172, 2000000000000463,
    2000000000000089, 2000000000000014, 2000000000000001]
private def pvn_m16_r256_5_0 : List ℕ :=
  pCat pvn_m16_r256_5_0_p0
    (pCat pvn_m16_r256_5_0_p1
    (pCat pvn_m16_r256_5_0_p2
      pvn_m16_r256_5_0_p3))
private def pvn_m16_r256_5_1_p0 : List ℕ :=
  [1999975938084538, 2000039967229499, 1999985307626161, 1999968908169580, 2000011078416250,
    2000035956425841, 2000018222307410, 2000030106679627, 1999973124927537, 2000016850929468,
    2000014057709568, 1999984984675114, 1999957384879715, 2000057495401498, 2000031209808360,
    1999974589774820, 1999990270256037, 2000015256705619, 1999975310284127, 1999996853637834,
    2000011524585960, 1999958542549753, 1999990282156546, 2000008337984748, 1999997021130232,
    2000015830004776, 1999950846735752, 1999985512298327, 2000026032743805, 2000024719203035,
    2000005074717258, 1999952196640203, 1999954411940942, 1999968804125127, 2000093199425408,
    1999931975843165, 2000142432290652, 1999854400761052, 2000206526539086, 1999816203630491,
    2000158486512011, 1999888062416170, 1999959073736244, 2000078781734691, 1999844471009728,
    2000227777734765, 1999746507930971, 2000204158147566, 1999847699822088, 2000150235495478,
    2000008947361949, 1999591903507155, 2000805538184018, 1999458039154969, 1999776835647654,
    2000575106017722, 1999777619126586, 2000153629787518, 1999886805861787, 1999475234842127,
    2000658988351671, 1999962177152626, 2000526654424245, 1999900339624109]
private def pvn_m16_r256_5_1_p1 : List ℕ :=
  [1999124080393812, 1999408603171012, 2000196418861361, 2000062102172066, 2000552848683347,
    2000252506286869, 2000298578796365, 2000194055880257, 1999715027452579, 1999198335018105,
    1999338594148920, 1998886542367589, 2000015646698400, 2000031641870512, 1999430577742699,
    1999594272449490, 2000082380827238, 1999344785098305, 1999487143046577, 2000436740047454,
    2000134294436496, 1999611688560117, 1999770141933841, 1998863568228314, 1999917680450031,
    2000295724034489, 2000159803874240, 2000012025483449, 2000570274849172, 1999703983781129,
    1999771029945802, 1999998549262569, 1999949993422579, 2000012226099618, 2000469313865523,
    2000331558021580, 1999640814462922, 1999449828197987, 2000422912982478, 2000018351315249,
    2000336165471230, 2000320686102755, 2000004696746668, 2000047808729591, 2000282652448371,
    1999989763427258, 2000198062937124, 2000443363028502, 2000251699698054, 2000371441060713,
    1999696241160788, 2000387909167779, 2000144981446714, 1999555566521618, 2000539592521716,
    2000302813208317, 1999742743415787, 1999901904704974, 1999363555401659, 2000092031535306,
    1999298963346607, 2000179286684424, 2000202897334318, 2000018998894968]
private def pvn_m16_r256_5_1_p2 : List ℕ :=
  [1999999896523908, 2000578141675497, 1999818872612992, 2000305867596290, 1999706654201892,
    2000308858014882, 1999742405887045, 1999895985455458, 2000213761234369, 2000294229393966,
    2000657834551255, 1999561592141138, 2000575927682292, 1999946070209739, 2000151419574092,
    1999505394368268, 1999465915641175, 2000062262683068, 2000290915400954, 2000447432579722,
    2000007291215722, 2000397835824429, 1999944585243448, 2000042882779557, 2000748984166679,
    1999986865970978, 2000204953249615, 2000259944891430, 2000251456787887, 2000428684582126,
    1999959359335614, 2000384075729418, 2000813648844102, 2000330851474578, 2000580867062173,
    2000155971215649, 2000502767648810, 2000612934796839, 2000631142561973, 2000505838271187,
    2000154263638509, 2000868341092437, 1999754078643640, 2000727757580864, 1999501619194967,
    2001241439075727, 1999895657293183, 2000116574960446, 2001316900296602, 1999772098942472,
    2000252661191414, 2001298917893794, 1999859777730619, 2000358513579238, 2000827938732922,
    2000355965601238, 1999446276007052, 2001348564712973, 1999821480550939, 1999620705866327,
    2001236012821537, 2001538024864420, 1996203749184155, 2002779765236222]
private def pvn_m16_r256_5_1_p3 : List ℕ :=
  [2001365493699258, 1997445829490127, 1999934771624616, 1997729284051086, 2007619599981705,
    2000934097994719, 1992236938329431, 2006048731926109, 2004984675138817, 1992524293587926,
    1998470202159949, 2000343352002635, 1987628367904172, 1993255792331501, 2015126313529896,
    2008792477049385, 1968035787176523, 1941609224492399, 1965390640860466, 2019191750589026,
    2055948930541663, 2051496423234315, 2020569437705213, 1997660598194069, 2010602444457893,
    2066861697081563, 2154642910399468, 2251811788262695, 2335697069976290, 2390018135631444,
    2407874373471436, 2391285872124046, 2348502948207392, 2290522905801765, 2227970019959894,
    2169082031517974, 2118892413708719, 2079441379742957, 2050527840096138, 2030628841940343,
    2017711771543000, 2009777902206544, 2005154018555789, 2002593560161907, 2001246664639087,
    2000573007235695, 2000251446864659, 2000104489653200, 2000040466420568, 2000014285057982,
    2000004471147330, 2000001192829206, 2000000250569872, 2000000031169257, 1999999996296964,
    1999999996114357, 1999999998517902, 1999999999601092, 1999999999917425, 1999999999986981,
    1999999999998593, 1999999999999944, 2000000000000010, 2000000000000001]
private def pvn_m16_r256_5_1 : List ℕ :=
  pCat pvn_m16_r256_5_1_p0
    (pCat pvn_m16_r256_5_1_p1
    (pCat pvn_m16_r256_5_1_p2
      pvn_m16_r256_5_1_p3))
private def pvn_m16_r256_5_2_p0 : List ℕ :=
  [1999971437853105, 1999977026461434, 1999961128340645, 2000031841967343, 2000013458245218,
    2000019617835125, 1999987847078870, 2000003346042963, 1999986300187013, 1999961688714373,
    1999987431146723, 2000041474702993, 2000048911215832, 1999982752555862, 1999971236685386,
    2000061055791930, 2000025995552055, 1999993561521412, 2000014178306143, 1999957849017032,
    2000028320738624, 1999936161085794, 2000113436671499, 1999864264517692, 2000205370844835,
    1999817501636913, 2000134952441497, 1999920785986941, 1999986759903631, 2000144928775091,
    1999779293274008, 2000237986356210, 1999739441872743, 2000110243121328, 2000026135626109,
    1999874637401891, 2000282345371234, 1999579724631213, 2000310647986994, 1999842301871717,
    1999870005517977, 2000425254030181, 1999646961576775, 1999958731395137, 2000538142504623,
    1999160103651785, 2000474219370031, 2000106076437876, 1999637619893968, 2000086000477158,
    2000190969367008, 1999874276475630, 2000203599304419, 1999701211929841, 2000177447078470,
    2000211462380325, 1999794363066322, 1999728390344849, 2000392147709978, 1999796438768171,
    2000119476294376, 1999965822898544, 1999805095242091, 2000047062301955]
private def pvn_m16_r256_5_2_p1 : List ℕ :=
  [2000110988155883, 2000071294629631, 2000210990353247, 1999605893623626, 1999708013330971,
    2000183943162435, 2000729167482190, 1999632246443537, 2000185494612156, 1999675811152978,
    1999337524579162, 2000227586462395, 2000916216871492, 1999904139437126, 2000013139247200,
    2000257887284108, 1999741056132430, 1999581524107528, 1999641249927758, 1999332680291590,
    2000306672381053, 2000420188880891, 2000462845732166, 2000284531969509, 2000546234457018,
    1999967620341598, 1999012513695632, 1999408640341198, 1999848740561698, 1999657481419271,
    1999696797593316, 1999898781731799, 1998891328169259, 1999477719749293, 1999960596044740,
    1999920663640641, 2000148316843559, 1999763831021218, 1999812551247037, 1999823988714516,
    1998882615133972, 2000033971195600, 1999395698208401, 2000407987946528, 2000445585042014,
    1999946277349530, 1999496520272200, 2000079031752835, 1999884281673248, 2000333704619019,
    1999761873215011, 2000650522620056, 1999879956420789, 1999527354072560, 2000200946086194,
    1999905466117646, 2000257508358715, 1999734455722576, 2000725272746479, 1999772719864328,
    2000181904226989, 1999995664939949, 2000060409217789, 2000369434839754]
private def pvn_m16_r256_5_2_p2 : List ℕ :=
  [2000126961801698, 2000620640469459, 2000120733404172, 1999956567634375, 1999975640853725,
    2000312935578664, 2000300266978629, 1999993449791986, 2000516134073643, 1999938992199511,
    1999913715583819, 1999664995760865, 1999483211520397, 2000227720466047, 1999691825922808,
    1999480473534864, 2000349798724653, 2000152627733373, 2000397376441821, 1999893515767443,
    2000035347580833, 2000169885474939, 1999782030022979, 2000280380769553, 1999549599229299,
    2000295870952199, 1999784012943657, 2001350178419280, 1999770498789297, 2000367824937925,
    1999560350739602, 1999848278083008, 2000177626327912, 1999435159632236, 2000387756871211,
    2000004609307293, 1999968283380301, 2000764405699904, 1999181950502992, 2000758993000160,
    2000586824966304, 1999915912464843, 1999900682196823, 2001010847590224, 1999140903957614,
    2000979544264655, 2000190517031417, 2000695250023465, 1999415749157515, 2001862963942912,
    1999468745096483, 1999618267678276, 2003546289587798, 1996840734831728, 2003095200710997,
    2000609450279696, 1997943554808033, 2003101642755363, 1998581357620473, 2000929809704853,
    2000691900732343, 1998232434243599, 2004295923470390, 1998410157931505]
private def pvn_m16_r256_5_2_p3 : List ℕ :=
  [1996516201956237, 2007354966132673, 1999910514425439, 1992899168533138, 2005928965227905,
    2004770576241688, 1992803645596738, 2000209643115013, 2006533329284135, 1997021768910196,
    1997616602173982, 2006053102377137, 1998886328610451, 1991959580961059, 2004095495309755,
    2010134827994076, 1993769454388593, 1986532073668836, 2007865894816094, 2023348600731017,
    2002042901498400, 1971429121472286, 1977624096988816, 2016655567480361, 2038718826205532,
    2012761485931290, 1962844642420035, 1938268397006564, 1961395119751246, 2009887555128816,
    2042378384621437, 2035450515706552, 1999951311600679, 1969975273355054, 1978878748706631,
    2040259821598312, 2143061763900656, 2259486269978902, 2358546632803146, 2417814260935829,
    2429112446021906, 2397752993672311, 2337552913201889, 2264722695826032, 2193056033104365,
    2131490618436398, 2083890527215143, 2050232045024891, 2028261386129654, 2014947866026330,
    2007432818658986, 2003472937519089, 2001522726085756, 2000624808019420, 2000238812008253,
    2000084437227074, 2000027358716524, 2000008027110720, 2000002101416675, 2000000481827392,
    2000000094405625, 2000000015252716, 2000000001917005, 2000000000167161]
private def pvn_m16_r256_5_2_p4 : List ℕ := [2000000000007371]
private def pvn_m16_r256_5_2 : List ℕ :=
  pCat pvn_m16_r256_5_2_p0
    (pCat pvn_m16_r256_5_2_p1
    (pCat pvn_m16_r256_5_2_p2
    (pCat pvn_m16_r256_5_2_p3
      pvn_m16_r256_5_2_p4)))
private def pvn_m16_r256_5_3_p0 : List ℕ :=
  [1999966671226377, 2000010322654646, 1999997812254271, 1999988116523723, 1999981950797933,
    1999968306730522, 1999961333635413, 1999987773405109, 2000006630855270, 1999985981300090,
    2000082857888728, 1999878032684255, 2000140439422697, 1999880867203559, 2000204658354108,
    1999847957331946, 1999960385606632, 2000098907754940, 1999771136865481, 2000271983857648,
    1999835829582276, 2000028045668845, 2000151763864018, 1999693784708590, 2000365666182595,
    1999763270855522, 2000090547828149, 2000143988080983, 1999804937114289, 2000114774114873,
    2000182765359204, 1999452962895328, 2000626311032858, 1999643998881468, 1999856260597014,
    2000474153063836, 1999772440181631, 1999717787329810, 2000575200802621, 1999615064088529,
    1999918444178121, 2000306925181561, 2000032073130168, 1999654249000728, 2000272924637537,
    1999883395235078, 1999980854059783, 2000069162878352, 1999852530596963, 2000109406148654,
    2000259210712905, 1999497884069976, 2000129676158750, 2000057941512302, 2000181910797622,
    1999654015161313, 2000181500317706, 1999953287382687, 2000090518797517, 2000075098676584,
    1999762296077850, 1999904763414931, 2000374740316441, 1999742811495778]
private def pvn_m16_r256_5_3_p1 : List ℕ :=
  [1999854851537776, 2000290348241208, 1999947964814262, 1999499329654479, 2000688543885166,
    2000085153235118, 1999541430957921, 2000089129571365, 2000061319558432, 1999977191987508,
    2000095258119209, 2000273211445072, 1999667372882543, 1999678158066475, 1999950208816859,
    2000460616808293, 2000181628093223, 2000084105895347, 1999605039530908, 1999359430461951,
    2000387621935914, 2000661861836601, 1999414618147326, 2000616043634543, 1999785815952613,
    2000052313891928, 1999497507075702, 1999822895739328, 2000132879982988, 2000190169115864,
    2000076498045115, 2000791207647648, 1999775972270104, 2000210362165052, 1999890695216072,
    1999197968862566, 1999497565650684, 1999357938654283, 2000767634857838, 2000239227058568,
    2000890580402498, 2000010514266695, 1999831321666502, 1999829486033025, 2000072047555231,
    1999958572551404, 1999272229120344, 2000155152594138, 1999568132450258, 1999056957376774,
    1999264546944564, 1999655192346343, 2000049152639548, 1999925435983969, 2000242130319881,
    1999641709644518, 1999421828241640, 1999292399912213, 1999656420224777, 2000113245819609,
    1999708872095733, 2000054967326845, 2000020835838283, 1999415936825716]
private def pvn_m16_r256_5_3_p2 : List ℕ :=
  [2000207396446392, 1999881469943954, 2000117769440216, 2000263741055365, 1999795628804365,
    2000478228575071, 1999499085798408, 2000096918732990, 1999560179169562, 2000868671609907,
    1999598140078988, 2000355160821853, 1999753097033691, 2000280618446973, 1999890137194868,
    1999824194735590, 2000931287220717, 2000044794515262, 2000185406443314, 2000149346208450,
    1999724375622559, 2000831221062063, 1999632577120523, 2000811042424433, 1999828321086909,
    2000365545462491, 2000346323649384, 2000112507633251, 1998903771607550, 2000712988752512,
    1998833830700086, 2000653827191505, 1999554024285813, 1999657878169893, 2000488634303943,
    2000230747466274, 2000809069841708, 1998075968689549, 2002471916372239, 1997478444929694,
    2000700871259855, 2001654283566722, 1997398003821987, 2003606974948648, 1998509646205565,
    1999278479191488, 2002313681834734, 1997358131724659, 2001557155636995, 1999923989461916,
    1998567422745658, 2002031211165734, 1998165740588700, 2001127669039045, 2001521030684403,
    1996926239980635, 2003176339228898, 2000571448483238, 1995624468083870, 2004922094105073,
    2001141510028578, 1994065155439692, 2005015189314403, 2003193244368234]
private def pvn_m16_r256_5_3_p3 : List ℕ :=
  [1993091454803761, 2003064986615934, 2006173617146455, 1994468065501374, 1999334463759893,
    2006801101051415, 1997496603414964, 1996725697935310, 2005450769328360, 2000061606331645,
    1995341374429242, 2004482749818538, 2003673321737458, 1993267744798039, 1999853802437716,
    2010339825822964, 1998762561961136, 1988262551266164, 2003713003785743, 2015042497384018,
    1996692745024715, 1982635016430528, 2002564116684803, 2022252099740730, 2003426964737107,
    1974228698192805, 1984438768347138, 2022659291603636, 2031804195983823, 1995304758687719,
    1961886449512038, 1977713548505622, 2025241836398314, 2046830028446744, 2014894848055059,
    1961484591534714, 1940243336180522, 1970304416429651, 2020445759937149, 2042100314803780,
    2014240493365432, 1960838068480937, 1931737924714128, 1966996706296753, 2071751375311703,
    2215440396013776, 2350785495390026, 2437646877954711, 2458293428358675, 2419056885307370,
    2341681174526184, 2251474729527459, 2168293674176189, 2102838102765233, 2057489421264608,
    2029404208355402, 2013737617244333, 2005842084357161, 2002248213776247, 2000775906422072,
    2000236916438475, 2000062692647858, 2000013906650567, 2000002434011966]
private def pvn_m16_r256_5_3_p4 : List ℕ := [2000000290476289]
private def pvn_m16_r256_5_3 : List ℕ :=
  pCat pvn_m16_r256_5_3_p0
    (pCat pvn_m16_r256_5_3_p1
    (pCat pvn_m16_r256_5_3_p2
    (pCat pvn_m16_r256_5_3_p3
      pvn_m16_r256_5_3_p4)))
private def pvn_m16_r256_5_4_p0 : List ℕ :=
  [1999984252558207, 1999972250988846, 2000004312852495, 1999923096667035, 2000130343934403,
    1999818264931011, 2000152694926793, 1999952130788026, 1999908122301774, 2000209909957835,
    1999761815133779, 2000063472641989, 2000166317036176, 1999580549543186, 2000305541271159,
    1999842229282136, 1999963884845841, 2000138811696526, 2000000683918372, 1999667869502298,
    2000500178662970, 1999597311606169, 2000101042864843, 2000320917986533, 1999729714850751,
    1999896417652561, 2000493376664735, 1999442168834696, 2000046825552335, 2000344723588668,
    1999798954441872, 1999705110441399, 2000479442906193, 1999911844965603, 1999666462425459,
    2000196628673570, 2000317984802163, 1999449043812254, 2000343760262072, 1999977241059130,
    2000043060651092, 1999936267097054, 2000080174936636, 1999956432798294, 2000074990773540,
    1999986744106031, 1999847647534693, 1999946014010039, 2000398355659519, 1999772373715006,
    1999868005561593, 2000102544448703, 2000188697198584, 1999755724836249, 2000050166082498,
    2000113742643769, 1999744555112407, 2000476369962932, 1999904758669524, 1999521476775681,
    2000156860356166, 2000469088619939, 1999574793873801, 1999922493906093]
private def pvn_m16_r256_5_4_p1 : List ℕ :=
  [2000292934337378, 1999968084860888, 1999703632159578, 2000263798385817, 1999928679068999,
    2000124492461282, 1999349736205215, 2000742804207077, 1999753779281192, 1999904757001167,
    2000222034095545, 1999800457395706, 1999807979063772, 2000505495947161, 1999697395198005,
    2000076012253410, 1999980687722790, 1999694265506156, 2000192443975553, 1999657778348554,
    2000985667126159, 1999605672916137, 1999557888865032, 1999780468679278, 2000487576815993,
    2000371898233044, 1999803970990726, 2000072893376228, 1999536105566078, 1999996350024479,
    2000032619340003, 2000257639588481, 2000115044573456, 1999881480702563, 2000269133058006,
    1999512209583869, 1999770850756477, 2000101274388846, 2000178637291243, 2000117543337205,
    2000259886282470, 2000109584976263, 1999613039010683, 2000087782004699, 2000053761109335,
    1999287403355457, 1999831182181989, 2000204892962702, 2000924132234523, 2000631015415363,
    1999643709009697, 2000416417195961, 1998910479893653, 1999793308711277, 1999324417168250,
    2000429836214645, 1999813195739980, 2000741375940029, 1999980142173331, 2000145432962180,
    1999963357563048, 1999915589371038, 2000647512373896, 1999863547388822]
private def pvn_m16_r256_5_4_p2 : List ℕ :=
  [1999926471727024, 1999456639671471, 1998923536282277, 1999729721716052, 1999015157680300,
    2000851972642839, 1999353818482050, 1999935447799601, 1999590143786618, 1999833353990772,
    1999140463281510, 2000045338369438, 1999334185650756, 2000724527384078, 1998793805499694,
    2000183074170889, 1999934962737134, 1999169961344784, 2001093378533430, 1998964225473031,
    2001325961827314, 1998799801939615, 2001026427346532, 1998742530798684, 2000522321265450,
    2001140122765384, 1997924485763049, 2002659063417814, 1997561083192998, 2000606798026966,
    2001899185509731, 1996968924181781, 2002845160121856, 1999246657925255, 1999569808484737,
    2002058027336469, 1997519066530741, 2001817040866921, 2000331028650015, 1999010245733871,
    2002221088099317, 1998541722004282, 2001026335399760, 2000726647166285, 1997785442358603,
    2002217773407114, 1998345335012912, 1998370915233039, 2003493463065845, 1997232459707167,
    2000084343424935, 2003942697482156, 1995210368712655, 2000412102061147, 2004426683369727,
    1994666771986032, 2000981382989020, 2005439796441303, 1994444324833010, 2000096668698410,
    2006179056008292, 1994961806870954, 1998194365475966, 2006134978692077]
private def pvn_m16_r256_5_4_p3 : List ℕ :=
  [1996498548713321, 1996808855159050, 2005852915947990, 1998758582004563, 1995989189395977,
    2004691990597897, 2000361039428109, 1995559474469015, 2004090987305270, 2002277238873525,
    1994127422260756, 2002321630903481, 2006360410855730, 1994243434747952, 1996602272692574,
    2010108604708733, 2001319899933210, 1988915354124348, 2003433113520528, 2013367260304838,
    1994029399808899, 1986558482382476, 2009611064141273, 2015244942219377, 1989043139145934,
    1983890218808898, 2013296686580881, 2020561981820563, 1988223025200534, 1975097527017185,
    2008604107061789, 2031995296885336, 2002244697396578, 1965588885185768, 1982513337601584,
    2029529655937464, 2035031916195433, 1988165396808853, 1954875373506067, 1983596984172520,
    2038737097215939, 2048885789091254, 1998606505383672, 1946139417672412, 1952141282411427,
    2009381411072063, 2051431287288762, 2024642992508307, 1945296119358722, 1888437370823487,
    1925089614547908, 2066555864428966, 2258429333540836, 2420187893946746, 2494074504137498,
    2469857910521987, 2377339694597570, 2261022186848510, 2156814902962432, 2081873121800007,
    2036918997423227, 2014171417039310, 2004503703533803, 2001121047800233]
private def pvn_m16_r256_5_4_p4 : List ℕ := [2000189757459036]
private def pvn_m16_r256_5_4 : List ℕ :=
  pCat pvn_m16_r256_5_4_p0
    (pCat pvn_m16_r256_5_4_p1
    (pCat pvn_m16_r256_5_4_p2
    (pCat pvn_m16_r256_5_4_p3
      pvn_m16_r256_5_4_p4)))
private def pvn_m16_r256_5_5_p0 : List ℕ :=
  [2000126562762127, 1999821841260277, 2000024397580504, 2000174367536423, 1999841141687145,
    1999814403629653, 2000411088435166, 1999641248536937, 2000025491923833, 2000089910926243,
    2000144521631429, 1999533553443644, 2000367338667647, 2000025944656971, 1999752734572917,
    2000047006920139, 2000365317575880, 1999488397929957, 2000131787617049, 2000331884540599,
    1999786603041553, 1999689380116402, 2000459277852379, 1999809764256002, 1999781440793102,
    1999903784915670, 2000589001730949, 1999553625950330, 1999780062167763, 2000444387898397,
    2000012318547271, 1999540669515348, 2000163386398225, 2000186490990911, 2000023774605230,
    1999736621514281, 2000250251729717, 2000064875328568, 1999873723686121, 2000043129620968,
    1999915656363094, 2000070439972803, 1999875490104235, 2000231128634026, 1999764599961670,
    1999896285138364, 2000304180014456, 2000076476702908, 1999504109048178, 2000287957789168,
    2000098212152107, 1999971753863862, 1999695433878423, 2000550728818783, 1999369401914722,
    2000404725711169, 2000191865402155, 1999858096408014, 1999763726669883, 2000086963473210,
    2000331134920916, 1999970167022841, 1999377081197550, 2000348617739869]
private def pvn_m16_r256_5_5_p1 : List ℕ :=
  [2000541028832831, 1999178491715454, 2000599414414200, 1999684012075319, 2000082617426364,
    1999895709487483, 2000056446824703, 2000253584278351, 1999719609946534, 2000206355321462,
    1999841318618211, 2000048914947826, 1999995525345545, 2000140009173487, 1999907080199792,
    1999646669194804, 2000462776436692, 1999951398109186, 1999891166385121, 1999940659468998,
    2000164793326440, 1999952868858688, 1999594697967079, 2000229690240511, 2000385817152101,
    1999838722523571, 1999670441014359, 1999872163318156, 2000256674403597, 2000160919304014,
    2000264420534740, 1999886367736165, 1999064421327248, 2000722026488674, 1999640862770854,
    2000643091704007, 1999585533275758, 2000235861215499, 1999537770002094, 2000004010509717,
    2000079518685187, 2000321758099245, 1999995940234071, 1999927204696638, 2000417069963425,
    1999335137781264, 1999720324291541, 2000421533359722, 2000047885936287, 2000573256165930,
    1999136283495241, 2000665630521031, 1999430649981464, 2000348544930074, 1999538665475410,
    2000004685473029, 1999869779213123, 2000624279403937, 1999985623957050, 2000827150757079,
    1999043722158076, 1999925063268529, 1999661118970756, 1999152708570644]
private def pvn_m16_r256_5_5_p2 : List ℕ :=
  [2001133163879464, 1999372166499869, 2002087472313211, 1998879219408042, 2000915284171542,
    1999209362841124, 1999329564589458, 2000171689830280, 1999327433530712, 2001619455679576,
    1997870619290025, 2001529860584620, 1999317199752823, 1999613304316077, 2002594358226960,
    1997620906832395, 2002475536719488, 1999036974150726, 1998023842502389, 2002104000490465,
    1996966490506098, 2001242638777312, 2000144125109253, 1997944382625905, 2001927772084735,
    1997920671564749, 2000071560457276, 2000405387866686, 1998370907957611, 2001674472112246,
    1998029665373820, 1999499604589425, 2001270515681857, 1997977553394153, 2001744661223280,
    1999290747536578, 1998617398494245, 2002864736855220, 1997322138949121, 2000175234044362,
    2002906737970212, 1996249288826793, 2001978304648569, 2001597690607050, 1995355041139855,
    2003742954811135, 2000783137368398, 1995459532301322, 2004973779370820, 1999705911025538,
    1995349081942855, 2005671518797842, 1999288683011653, 1995385249714396, 2005937969221850,
    1999605152154508, 1995824246730328, 2005778250644269, 1999340322406661, 1994834826325744,
    2004553421508322, 1999959248577955, 1995533357668605, 2004321820578434]
private def pvn_m16_r256_5_5_p3 : List ℕ :=
  [2000434327459780, 1995436091331805, 2003668193594836, 2000777945773114, 1995174455671433,
    2003658259667241, 2002052974860115, 1994484466962476, 2003339528953386, 2004504261302776,
    1992923392130860, 2000063213282492, 2008154021356873, 1994366340303951, 1994081926364169,
    2010118008824291, 2001220086845127, 1987975569375104, 2004963003363533, 2011841317545221,
    1989808975409825, 1991309793018999, 2015146319376624, 2005048196871426, 1982221718542619,
    2000326230612890, 2020849022965610, 1996351205589979, 1978872901985364, 2008748563326189,
    2023843684128554, 1989284478111918, 1974582439422658, 2012923275215953, 2029971226642740,
    1989134531181698, 1966457419735149, 2007557257352977, 2039310511218886, 2002017570277215,
    1958866234790608, 1986435922689708, 2040969666767257, 2030373432373488, 1967630981531901,
    1952297948695673, 2012979910987030, 2060361463811129, 2020695847147897, 1947104931324320,
    1946405537654183, 2027097713617018, 2079080246419950, 2012723876870774, 1879986673856882,
    1831376961195496, 1962876406779599, 2221747971478987, 2457277564509441, 2547446836544686,
    2477813203971595, 2321856821237903, 2168158514614840, 2065657937437813]
private def pvn_m16_r256_5_5_p4 : List ℕ := [2016828536072830]
private def pvn_m16_r256_5_5 : List ℕ :=
  pCat pvn_m16_r256_5_5_p0
    (pCat pvn_m16_r256_5_5_p1
    (pCat pvn_m16_r256_5_5_p2
    (pCat pvn_m16_r256_5_5_p3
      pvn_m16_r256_5_5_p4)))
private def pvn_m16_r256_5_6_p0 : List ℕ :=
  [2000147061823942, 2000100384145963, 2000213480215516, 1999476017596044, 2000167701408105,
    2000077086663159, 2000260581213580, 1999585958699687, 1999992502838570, 2000205946495567,
    2000184323423948, 1999477581766290, 2000105990062562, 2000292577441009, 1999965200924813,
    1999481140260188, 2000485551973635, 1999989715665231, 1999832565719085, 1999760150806392,
    2000326388631247, 2000207356693093, 1999627198378760, 1999757070651037, 2000598546372500,
    1999889725606277, 1999616280966506, 2000078248264382, 2000363155144174, 2000044245341910,
    1999469272985420, 2000199884712194, 2000135448363986, 1999986827718569, 1999690120472588,
    2000069441465944, 2000129672124706, 2000086216300952, 1999659280049849, 2000370962751784,
    1999657290953715, 2000164665134643, 1999825571236326, 2000390916237118, 1999461965515953,
    2000115743731282, 2000532930689763, 1999686050090119, 1999785720092217, 2000310808750519,
    2000027388473623, 1999775241030101, 2000290542583172, 1999529100482290, 2000532504422861,
    1999436904340071, 2000297767312638, 2000421527267330, 1999193952544362, 2000164049803513,
    2000343059733234, 2000172100773375, 1999485177306681, 1999953710697818]
private def pvn_m16_r256_5_6_p1 : List ℕ :=
  [2000367285422178, 1999892971899426, 2000021604459672, 1999835302530376, 2000260238990368,
    1999873907844812, 2000046149527477, 2000214137039686, 1999763199942751, 1999983271206287,
    2000078697587891, 1999968709543499, 1999989371285735, 2000068340365543, 2000185674125057,
    1999767198881880, 1999715612764636, 2000464959316435, 1999814546238793, 2000287398406056,
    1999210945343278, 2000984221561092, 1999487108937624, 2000044323879124, 2000032204340679,
    2000164102339734, 1999876990669717, 1999910682672343, 1999957873403846, 1999921476382935,
    2000443449664613, 1999979354406406, 1999759607699732, 1999754688143790, 1999786846925945,
    2001059859438336, 1999211648493000, 2000508672021907, 1999283439005806, 2000222913576121,
    1999775961386109, 2000638326197598, 1999980666545922, 1999879449467969, 1999447295205067,
    2000586681856689, 1999535386330333, 2000198302191728, 2000267933279182, 1999649511373038,
    2000891774264522, 1998200055279745, 2001307461193118, 1999017638291892, 2001142683394156,
    1999775467528885, 1999726166812145, 2000465772438974, 1998799820188749, 2001525955446346,
    1998592102990576, 2000995401814186, 1999438805099550, 2000220834832767]
private def pvn_m16_r256_5_6_p2 : List ℕ :=
  [2001124944340780, 1997889568990736, 2002255688378049, 1997831483562153, 1999969186210118,
    2001724771272352, 1997829170794554, 2002999928272807, 1998687415282509, 1999645507425571,
    2001382093856820, 1996668298174255, 2001769213697802, 1999801399393565, 1999775765248325,
    2002238515085006, 1998179814341559, 2001106686899770, 1999597737131999, 1999017503877432,
    2001630102150935, 1998198058252416, 2000834101043561, 1999720085180226, 1998288803791426,
    2002585500617279, 1998778458325173, 2000575996863779, 2002025264855413, 1997318411449537,
    2001850614119767, 1999284959713909, 1997308215796258, 2003725709703485, 1997414060282377,
    1998233018867973, 2003607064323731, 1995906827684699, 2000529651508014, 2002999908453451,
    1994676492909889, 2002201848575801, 2001705693077903, 1994236076563112, 2003820281577219,
    2000903049643511, 1994654210140203, 2004670085985794, 1999738376023374, 1995130142095632,
    2005372826407383, 1999349714228532, 1995704959418202, 2005098071804750, 1998632472206901,
    1996291843157916, 2005090569668200, 1998475658024208, 1996844422343926, 2004958237133701,
    1998479351350946, 1997301596178352, 2004502604886069, 1997856549681342]
private def pvn_m16_r256_5_6_p3 : List ℕ :=
  [1997758123136096, 2005670953742728, 1998231893942688, 1997158167052654, 2005772754037122,
    1997659392543230, 1995223802615566, 2006761144529933, 1999344057772493, 1992724234815958,
    2006818894552152, 2002912923089236, 1989775658005908, 2003829992053533, 2008375020316203,
    1989849773244995, 1997831130722258, 2013407920720485, 1994696801178598, 1988700304716502,
    2012597708349335, 2005624996989782, 1983140403615885, 2002295426243654, 2017391160156859,
    1989557562390363, 1985736823762554, 2017798574364635, 2009232015927942, 1977470326695103,
    1997830728646370, 2026043473457709, 1995718761413707, 1973114235562135, 2011835465254210,
    2028950231075291, 1983853099165008, 1971404485767658, 2021538349714051, 2030961628633147,
    1976443041882098, 1967602252391692, 2026142617110102, 2037383754968371, 1975151373315190,
    1958125496219128, 2023735556365843, 2051003968627856, 1983340422639738, 1939931715171288,
    2005069385417909, 2069733262494159, 2014322546957709, 1924160435189509, 1960953849126763,
    2086748835502869, 2093296056071465, 1916319302804772, 1769259513843846, 1889984399483389,
    2240531602666262, 2544339026216597, 2585092140514593, 2394687551904985]
private def pvn_m16_r256_5_6_p4 : List ℕ := [2159158259608095]
private def pvn_m16_r256_5_6 : List ℕ :=
  pCat pvn_m16_r256_5_6_p0
    (pCat pvn_m16_r256_5_6_p1
    (pCat pvn_m16_r256_5_6_p2
    (pCat pvn_m16_r256_5_6_p3
      pvn_m16_r256_5_6_p4)))
private def phb_m16_r256_6_p0 : List ℕ :=
  [107728280025847, 151883146611529, 185445223360687, 213472038896843, 237929062832767,
    259827482499112, 279769840583714, 298149920679397, 315242069384667, 331246633450132,
    346315307101647, 360566288964917, 374093851503253, 386974652996996, 399272053707963,
    411039157876771, 422321013584663, 433156239293618, 443578249945715, 453616197041439,
    463295700352066, 472639425153515, 481667543122805, 490398104376101, 498847340764693,
    507029915370265, 514959129444473, 522647095358732, 530104882161943, 537342638880123,
    544369699590746, 551194673467498, 557825522348469, 564269627882930, 570533849922820,
    576624577518689, 582547773636734, 588309014519326, 593913524455187, 599366206598921,
    604671670376671, 609834255930415, 614858055984036, 619746935456988, 624504549103690,
    629134357417009, 633639641000843, 638023513588736, 642288933861739, 646438716198601,
    650475540474257, 654401961007920, 658220414749587, 661933228782948, 665542627213413,
    669050737501931, 672459596298303, 675771154821621, 678987283830198, 682109778218715,
    685140361276279, 688080688635532, 690932351939809, 693696882252613]
private def phb_m16_r256_6_p1 : List ℕ :=
  [696375753231203, 698970384083965, 701482142329294, 703912346372030, 706262267911962,
    708533134197567, 710726130136945, 712842400276804, 714883050659423, 716849150566589,
    718741734158776, 720561802017091, 722310322594879, 723988233585317, 725596443210786,
    727135831439359, 728607251133283, 730011529133983, 731349467287727, 732621843415778,
    733829412232591, 734972906215293, 736053036427487, 737070493300172, 738025947372367,
    738920049993845, 739753433992203, 740526714306346, 741240488588294, 741895337775119,
    742491826632662, 743030504272590, 743511904644234, 743936547002549, 744304936353467,
    744617563877797, 744874907334778, 745077431446307, 745225588262789, 745319817511514,
    745360546928381, 745348192573762, 745283159133236, 745165840203856, 744996618566623,
    744775866445730, 744503945755154, 744181208333117, 743807996164900, 743384641594465,
    742911467525314, 742388787610994, 741816906435588, 741196119684575, 740526714306346,
    739808968664705, 739043152682598, 738229527977358, 737368347987672, 736459858092512,
    735504295722203, 734501890461830, 733452864147130, 732357430953023]
private def phb_m16_r256_6_p2 : List ℕ :=
  [731215797474912, 730028162802866, 728794718588781, 727515649106608, 726191131305715,
    724821334857435, 723406422194847, 721946548545805, 720441861959233, 718892503324681,
    717298606385124, 715660297742966, 713977696859205, 712250916045695, 710480060450427,
    708665228035726, 706806509549258, 704903988487720, 702957741053059, 700967836101055,
    698934335082091, 696857291973891, 694736753206016, 692572757575853, 690365336155834,
    688114512191586, 685820300990691, 683482709801698, 681101737683007, 678677375361225,
    676209605078530, 673698400428568, 671143726180370, 668545538089711, 665903782697320,
    663218397113279, 660489308786906, 657716435261359, 654899683912157, 652038951668706,
    649134124717901, 646185078188760, 643191675816983, 640153769588239, 637071199358872,
    633943792452642, 630771363231966, 627553712642027, 624290627725980, 620981881109305,
    617627230451240, 614226417861014, 610779169276411, 607285193801987, 603744183004024,
    600155810159029, 596519729452320, 592835575122902, 589102960550495, 585321477280186,
    581490693979726, 577610155324049, 573679380801004, 569697863431747]
private def phb_m16_r256_6_p3 : List ℕ :=
  [565665068398530, 561580431571911, 557443357928548, 553253219849843, 549009355290604,
    544711065805747, 540357614421710, 535948223337751, 531482071440574, 526958291613819,
    522375967821729, 517734131943781, 513031760334245, 508267770077276, 503441014904447,
    498550280737212, 493594280811826, 488571650338428, 483480940639220, 478320612702895,
    473089030083239, 467784451059122, 462405019960475, 456948757549912, 451413550332050,
    445797138641559, 440097103335928, 434310850888881, 428435596644198, 422468345945862,
    416405872807207, 410244695716576, 403981050096929, 397610856837742, 391129686194343,
    384532716195335, 377814684504048, 370969832432369, 363991839488196, 356873746428084,
    349607864252459, 342185665877559, 334597656282505, 326833215670647, 318880408468596,
    310725748617032, 302353908287266, 293747352429645, 284885874706978, 275746000236460,
    266300205259748, 256515880167122, 246353924591053, 235766801346811, 224695770523190,
    213066837701093, 200784600688221, 187722486860747, 173706399054061, 158485349532326,
    141673632164805, 122621190342055, 100059122383749, 70708133549816]
private def phb_m16_r256_6 : List ℕ :=
  pCat phb_m16_r256_6_p0
    (pCat phb_m16_r256_6_p1
    (pCat phb_m16_r256_6_p2
      phb_m16_r256_6_p3))
private def pvn_m16_r256_6_0_p0 : List ℕ :=
  [2000147061823942, 2000100384145963, 2000213480215516, 1999476017596044, 2000167701408105,
    2000077086663159, 2000260581213580, 1999585958699687, 1999992502838570, 2000205946495567,
    1999815676576052, 1999477581766290, 2000105990062562, 2000292577441009, 1999965200924813,
    2000518859739812, 2000485551973635, 1999989715665231, 1999832565719085, 1999760150806392,
    1999673611368753, 2000207356693093, 1999627198378760, 1999757070651037, 2000598546372500,
    2000110274393723, 1999616280966506, 2000078248264382, 2000363155144174, 2000044245341910,
    2000530727014580, 2000199884712194, 1999864551636014, 1999986827718569, 1999690120472588,
    1999930558534056, 2000129672124706, 2000086216300952, 2000340719950151, 2000370962751784,
    1999657290953715, 2000164665134643, 2000174428763674, 2000390916237118, 1999461965515953,
    2000115743731282, 2000532930689763, 1999686050090119, 1999785720092217, 2000310808750519,
    2000027388473623, 1999775241030101, 1999709457416828, 2000470899517710, 2000532504422861,
    1999436904340071, 2000297767312638, 2000421527267330, 1999193952544362, 2000164049803513,
    2000343059733234, 2000172100773375, 1999485177306681, 1999953710697818]
private def pvn_m16_r256_6_0_p1 : List ℕ :=
  [2000367285422178, 1999892971899426, 2000021604459672, 1999835302530376, 1999739761009632,
    1999873907844812, 1999953850472523, 2000214137039686, 1999763199942751, 1999983271206287,
    2000078697587891, 1999968709543499, 1999989371285735, 2000068340365543, 2000185674125057,
    1999767198881880, 2000284387235364, 2000464959316435, 1999814546238793, 2000287398406056,
    1999210945343278, 2000984221561092, 1999487108937624, 2000044323879124, 2000032204340679,
    1999835897660266, 2000123009330283, 1999910682672343, 2000042126596154, 1999921476382935,
    2000443449664613, 1999979354406406, 1999759607699732, 1999754688143790, 1999786846925945,
    2001059859438336, 2000788351507000, 1999491327978093, 1999283439005806, 2000222913576121,
    2000224038613891, 1999361673802402, 2000019333454078, 1999879449467969, 1999447295205067,
    2000586681856689, 2000464613669667, 1999801697808272, 2000267933279182, 1999649511373038,
    2000891774264522, 2001799944720255, 2001307461193118, 1999017638291892, 2001142683394156,
    1999775467528885, 2000273833187855, 2000465772438974, 1998799820188749, 2001525955446346,
    1998592102990576, 1999004598185814, 1999438805099550, 2000220834832767]
private def pvn_m16_r256_6_0_p2 : List ℕ :=
  [2001124944340780, 1997889568990736, 1997744311621951, 1997831483562153, 2000030813789882,
    2001724771272352, 1997829170794554, 1997000071727193, 1998687415282509, 2000354492574429,
    2001382093856820, 1996668298174255, 1998230786302198, 1999801399393565, 1999775765248325,
    2002238515085006, 1998179814341559, 1998893313100230, 1999597737131999, 1999017503877432,
    2001630102150935, 1998198058252416, 1999165898956439, 1999720085180226, 1998288803791426,
    2002585500617279, 1998778458325173, 2000575996863779, 2002025264855413, 1997318411449537,
    2001850614119767, 2000715040286091, 1997308215796258, 2003725709703485, 1997414060282377,
    1998233018867973, 2003607064323731, 2004093172315301, 2000529651508014, 2002999908453451,
    1994676492909889, 2002201848575801, 1998294306922097, 1994236076563112, 2003820281577219,
    2000903049643511, 1994654210140203, 1995329914014206, 1999738376023374, 1995130142095632,
    2005372826407383, 1999349714228532, 2004295040581798, 2005098071804750, 1998632472206901,
    1996291843157916, 2005090569668200, 1998475658024208, 1996844422343926, 2004958237133701,
    1998479351350946, 1997301596178352, 1995497395113931, 1997856549681342]
private def pvn_m16_r256_6_0_p3 : List ℕ :=
  [1997758123136096, 2005670953742728, 1998231893942688, 2002841832947346, 2005772754037122,
    1997659392543230, 1995223802615566, 2006761144529933, 2000655942227507, 1992724234815958,
    2006818894552152, 2002912923089236, 1989775658005908, 1996170007946467, 2008375020316203,
    1989849773244995, 1997831130722258, 2013407920720485, 2005303198821402, 1988700304716502,
    2012597708349335, 2005624996989782, 1983140403615885, 2002295426243654, 2017391160156859,
    1989557562390363, 1985736823762554, 2017798574364635, 1990767984072058, 1977470326695103,
    1997830728646370, 2026043473457709, 2004281238586293, 2026885764437865, 2011835465254210,
    2028950231075291, 2016146900834992, 2028595514232342, 2021538349714051, 2030961628633147,
    2023556958117902, 2032397747608308, 2026142617110102, 2037383754968371, 2024848626684810,
    2041874503780872, 2023735556365843, 2051003968627856, 2016659577360262, 2060068284828712,
    2005069385417909, 2069733262494159, 2014322546957709, 2075839564810491, 2039046150873237,
    2086748835502869, 2093296056071465, 2083680697195228, 2230740486156154, 2110015600516611,
    2240531602666262, 2544339026216597, 2585092140514593, 2394687551904985]
private def pvn_m16_r256_6_0_p4 : List ℕ := [2159158259608095]
private def pvn_m16_r256_6_0 : List ℕ :=
  pCat pvn_m16_r256_6_0_p0
    (pCat pvn_m16_r256_6_0_p1
    (pCat pvn_m16_r256_6_0_p2
    (pCat pvn_m16_r256_6_0_p3
      pvn_m16_r256_6_0_p4)))
private def pvn_m16_r256_6_1_p0 : List ℕ :=
  [2000263531041533, 1999651155556731, 2000341235178311, 2000131277585099, 2000277881181079,
    1999952376934308, 1999681730057045, 1999777359998331, 2000188568355212, 2000421874407439,
    1999745051232819, 1999704425278810, 2000208483629764, 2000295478413372, 1999688952384248,
    1999971921674069, 1999940531310767, 1999626872939058, 2000014142488732, 1999877073941405,
    1999822417367863, 2000335829466166, 2000880903623795, 2000062993446242, 1999774920753125,
    2000441553200773, 2000039224093585, 1999707230944149, 1999726439814072, 1999767153727386,
    1999790693957115, 2000368279132142, 1999780144527099, 2000221241087434, 1999846250914077,
    1999889649277628, 1999993201273633, 2000162454353549, 2000504495846299, 2000120899173856,
    2000071250435585, 2000632677838152, 1999863948137316, 1999279878016433, 2000093005081430,
    2000217325231074, 2000083157384959, 1999991771293325, 1999730479890914, 2000937270786525,
    1999873075819381, 1999548951656467, 2000548549647435, 2000345640439037, 1999724581721869,
    1999730140047535, 2000502206327888, 2000192613114704, 1999580246849339, 2000248903759298,
    2000112138746499, 1999773182807077, 1999636094799358, 2000159009232917]
private def pvn_m16_r256_6_1_p1 : List ℕ :=
  [2000499309566695, 2000027327677995, 2000002372792448, 1999947794469243, 1999969110574435,
    2000213093779473, 1999847495857326, 2000551795968004, 1999046931444565, 2000616730238244,
    1999701842050287, 2000277370642308, 2000096491342501, 1999687024894657, 2000297986672769,
    1999541547626043, 1999862270389580, 2000147714763720, 2000031812066008, 1999588913267890,
    1999943179333131, 2000334825254178, 1999839152160785, 2000064972828226, 1999757693747867,
    1999910319763379, 2000368603748963, 2000046775539390, 2000097613995544, 2000110622445081,
    2000122883900021, 1999990996886174, 2000178883641455, 2000095824599328, 1999510367724658,
    2000210178534557, 2000962623833174, 1998811100405946, 1999708328901588, 2000267922124387,
    2000831010585150, 1999678982818842, 2000373242511957, 1998942498212915, 1999867205181782,
    2001157592401431, 1998895757304522, 2001733253509369, 1999358213902612, 1999765328798735,
    2000630543080665, 1999746463166143, 2000736235666144, 1998494154165653, 1999550233021236,
    2000565229634639, 2000367980507350, 2000266021587683, 1998656516673064, 2000237853244137,
    2000649955549644, 1999390927011451, 2001602371057015, 2000299000830863]
private def pvn_m16_r256_6_1_p2 : List ℕ :=
  [2001526611308342, 2000738529956081, 1998658783804518, 2001358785722683, 2000192943218130,
    2002114842857535, 1999553253391371, 1996206723633142, 2001178761193787, 2001198237602552,
    2001255539540997, 1998586232628684, 1996216534700437, 2001265286573352, 1999208595152638,
    2000172049510892, 1998276485289290, 1996255824213757, 2001472530133701, 1999212546301572,
    1998701379888423, 2000466916521802, 1994432259145529, 2001796934885723, 1999693398822879,
    1998570140246027, 2000453705506161, 1999887190867567, 1996297337253726, 2004429725330576,
    1996904444796338, 1999336671248719, 2001753398312573, 1995952072510906, 2001386003963456,
    1998246033490899, 2000744209492167, 2001643506195201, 1999634797420355, 1994843372960157,
    2008114194275601, 1998439970700065, 1997830864783601, 2000916812154136, 1998705992518689,
    1998580635320720, 2002469278337842, 2001210857057682, 2004897208795825, 2003130088883800,
    1992806932375875, 2003129629036900, 1999998159125598, 1997757118134585, 2000256367255116,
    2002916209480460, 1992111358420697, 1996904336796956, 1997153356454965, 1998211733869250,
    2002422701324742, 2001699935137001, 2001602884003457, 2004931065672395]
private def pvn_m16_r256_6_1_p3 : List ℕ :=
  [1998547173068817, 1994755397859254, 2008001174697156, 2000242598690084, 1996380798981612,
    2003336156102635, 2001268127119702, 1985704301468745, 2003476619261444, 2003348323592226,
    1993972424609440, 2001556561829271, 2012694100342935, 1991076095461282, 1996688392768738,
    2013474932092374, 1992915060895470, 1994638055702480, 2013875344296189, 1999326897121641,
    1980135611573331, 2015090414756428, 1994757457521277, 1986571242071050, 2006814689265506,
    2022226558230281, 1977211928400794, 2012637029680149, 2004901948663429, 1998657582647672,
    1988830934023494, 2011885511490447, 2004337937006363, 1999095422361990, 1984082905242859,
    1993543572645469, 1991442968128678, 2009514418752750, 2004616876560777, 2024967007784887,
    2007851141406496, 2034035253555126, 2007735095735919, 2045254194320196, 2002315338758507,
    2055456456636897, 2001353222864872, 2060124070198149, 2007169316469797, 2053760495238367,
    2022821141033282, 2045557028991846, 2042929059685846, 2014764402376124, 2081659283699344,
    1979873336256573, 2104582642025996, 2039331029605396, 2015514618798942, 2191291378863616,
    2098386783270112, 2055249792648176, 2391327826896262, 2691025382008451]
private def pvn_m16_r256_6_1_p4 : List ℕ := [2526778705364911]
private def pvn_m16_r256_6_1 : List ℕ :=
  pCat pvn_m16_r256_6_1_p0
    (pCat pvn_m16_r256_6_1_p1
    (pCat pvn_m16_r256_6_1_p2
    (pCat pvn_m16_r256_6_1_p3
      pvn_m16_r256_6_1_p4)))
private def pvn_m16_r256_6_2_p0 : List ℕ :=
  [2000509655209119, 1999901768902774, 1999924048573838, 1999969269138575, 1999951022615467,
    2000157417822682, 2000129604739203, 2000385839450183, 2000232481203882, 1999870861573580,
    1999422327595848, 1999875441580974, 2000526305035167, 1999990878195561, 1999835439698915,
    1999975735968718, 2000060470238433, 1999896270468559, 2000067360976135, 2000386288693578,
    1999665659988661, 1999755709649143, 2000233851774532, 2000209252123907, 1999165371309579,
    1999839721175924, 1999863191641967, 2000224495423200, 2000371976104083, 2000073105386720,
    2000242638484379, 2000316407511158, 2000256497853564, 2000269276137205, 1999819782494874,
    1999742348784025, 2000022010931683, 1999576877675563, 1999634393377814, 2000691190914691,
    1999745364939804, 1999869030003628, 1999938187566828, 1999903785866577, 2000341967453506,
    1999584638937466, 1999771008369158, 2000836006864946, 2000647302571945, 1999911401682711,
    1999686116110635, 2000552635261713, 2000051174488447, 1999324100796971, 2000004055491401,
    2000388257848420, 2000061018308039, 1999770006073781, 2000015304029381, 2000710363895888,
    1999585347827500, 2000486732195699, 1999587793893908, 2000810956967530]
private def pvn_m16_r256_6_2_p1 : List ℕ :=
  [1999561328653303, 1999856685947691, 2000504387965016, 1999831163579403, 2000471427841974,
    1999795753271367, 1999774461594067, 1999855094692395, 1999914315278184, 2000304528170289,
    2000186253918916, 1999939587226437, 1999778964547246, 2000407790700385, 2000056290709655,
    1999820213169265, 2000374648844587, 1999876646518940, 1999777125886207, 1999961448930661,
    2000137691305458, 2000201535093179, 2000040953018857, 1999778477074922, 2000026991642583,
    1999909679209000, 2000441377286279, 1999060357663125, 2000420023565604, 1999732368726288,
    1999912784803086, 2000069801421851, 2000356112803782, 1999454660140061, 1999318349285601,
    2001693780987734, 1998514132717529, 2000536334848679, 2000098010328170, 1999806408056844,
    2001398329915779, 1998696448095131, 2000151440056286, 2000381906180289, 2000307122329463,
    2000425106292738, 1999142637961959, 2000110370220906, 1999730131806317, 1999869575012870,
    2001155976493839, 1999435943736674, 2000423104094342, 1998894042059709, 1999778875832854,
    2001763347739638, 1998657292196043, 2000385433382984, 1999667014329430, 2000735986936309,
    2001503683779902, 1998233931563126, 2000803508278873, 1999322603497804]
private def pvn_m16_r256_6_2_p2 : List ℕ :=
  [1999534935205238, 2001395960694895, 1998015552643022, 2001468539259354, 1999777512907392,
    1999191671786752, 1999420811612222, 1998769066158935, 2003696688655299, 2000999309256088,
    1997423095310090, 2001814794170220, 1998789058176181, 2005194727112475, 1999636289656142,
    1997516560263266, 2000109767922303, 2001372689714796, 1999177419343255, 2003434729811900,
    1995329058165650, 1999892983840688, 2003057206412299, 1996013737487167, 2002291634017943,
    1996186398931375, 1998756152614964, 2000376171178006, 2000472836887785, 1996321832421114,
    2001821918805457, 1994576641601518, 2002039069957339, 1999174181939236, 1996077271814950,
    2002825144356509, 1999361615868863, 1995304705839808, 2002936657088326, 2002119754115338,
    1995484679717127, 2001528593241215, 1996224782091925, 2002967134306786, 1999079107831262,
    1997155401511209, 2000545234070936, 2002807452174254, 1995014089757190, 2004167500329912,
    2003842628846590, 1995510375764051, 1998693070888180, 1999775231774537, 1998850052051840,
    2002900616173738, 2003979679829025, 1999650379752188, 2003412835660299, 1994906368045292,
    2001205052879418, 2004546969604515, 1998796425892318, 1995003579974550]
private def pvn_m16_r256_6_2_p3 : List ℕ :=
  [2006118672441494, 1989808777453732, 1992801430970223, 2004778652895945, 1999642913187502,
    1995330564828139, 2010421140623263, 1999825757341927, 1989588801535242, 2012305740321674,
    2001254970908229, 1993505515491606, 2007342333756437, 2004838350596128, 1977725103747343,
    2012352775882434, 1997898738204765, 1990845341887532, 2004525166928118, 2017018727117117,
    1973976081111385, 2017150588951129, 2002918042696147, 1990735111406856, 2003195324184180,
    2014658287955243, 1985660750337611, 1995990748756998, 2001126848407586, 2001766342401822,
    1989773763655696, 2011438739483595, 2002109659803872, 2007218016859696, 1984268960120372,
    2013228812759658, 1992930928362446, 2023264355199115, 1978294867030771, 2013854638470514,
    1962587279807888, 2020813655918943, 1974819627607211, 2032172172071315, 1993638944800634,
    2033551778296619, 2013929244250945, 2024943062199532, 2034870925448852, 2008875614165720,
    2066795474130738, 1983888096889982, 2085918557822727, 1998524761001768, 2049180959683702,
    2076139377018390, 1969867162877176, 2105201234283417, 2041161586000071, 1969196066750203,
    2170204563130918, 2100486232855054, 1946318907823044, 2405902548826158]
private def pvn_m16_r256_6_2_p4 : List ℕ := [2863574417487093]
private def pvn_m16_r256_6_2 : List ℕ :=
  pCat pvn_m16_r256_6_2_p0
    (pCat pvn_m16_r256_6_2_p1
    (pCat pvn_m16_r256_6_2_p2
    (pCat pvn_m16_r256_6_2_p3
      pvn_m16_r256_6_2_p4)))
private def phb_m16_r256_7_p0 : List ℕ :=
  [87516204199415, 123386695398043, 150651825421757, 173420224870193, 193288600197199,
    211078418866025, 227279173968874, 242210767070235, 256096071615506, 269097845119547,
    281339320802477, 292916520758596, 303906029967704, 314370124015322, 324360275454524,
    333919625061017, 343084768954926, 351887079968005, 360353703701147, 368508322224357,
    376371748504610, 383962395338576, 391296649775268, 398389175351984, 405253158485622,
    411900511157421, 418342039026359, 424587581929940, 430646132132254, 436525934490019,
    442234571812782, 447779038013395, 453165801122796, 458400857838648, 463489780961360,
    468437760822128, 473249641610122, 477929953348154, 482482940139243, 486912585203761,
    491222633143214, 495416609798276, 499497840012331, 503469463565205, 507334449503036,
    511095609057940, 514755607323990, 518316973833269, 521782112156454, 525153308636050,
    528432740346466, 531622482363274, 534724514413740, 537740726972041, 540672926854948,
    543522842367294, 546292128040830, 548982369005185, 551595085025331, 554131734236210,
    556593716601894, 558982377123753, 561299008819582, 563544855493388]
private def phb_m16_r256_7_p1 : List ℕ :=
  [565721114313541, 567828938215287, 569869438142001, 571843685138233, 573752712306326,
    575597516637305, 577379060725756, 579098274377516, 580756056118226, 582353274610071,
    583890769983417, 585369355089453, 586789816679445, 588152916515740, 589459392419229,
    590709959257589, 591905309878295, 593046115990048, 594133028996002, 595166680781905,
    596147684462014, 597076635085443, 597954110305409, 598780671013634, 599556861942008,
    600283212233479, 600960235983968, 601588432756995, 602168288072575, 602700273871849,
    603184848958788, 603622459420241, 604013539025488, 604358509606408, 604657781419270,
    604911753489102, 605120813937530, 605285340294914, 605405699797559, 605482249670731,
    605515337398137, 605505300978533, 605452469170028, 605357161722647, 605219689599677,
    605040355188277, 604819452499802, 604557267360274, 604254077591389, 603910153182440,
    603525756453487, 603101142210118, 602636557890081, 602132243702080, 601588432756995,
    601005351191764, 600383218286150, 599722246572609, 599022641939437, 598284603727382,
    597508324819883, 596693991727066, 595841784663649, 594951877620862]
private def phb_m16_r256_7_p2 : List ℕ :=
  [594024438432496, 593059628835163, 592057604522860, 591018515195896, 589942504604239,
    588829710585338, 587680265096432, 586494294241385, 585271918292052, 584013251704161,
    582718403127709, 581387475411845, 580020565604188, 578617764944542, 577179158852939,
    575704826911924, 574194842843006, 572649274477157, 571068183719247, 569451626506274,
    567799652759244, 566112306328533, 564389624932547, 562631640089472, 560838377041903,
    559009854674101, 557146085421627, 555247075173050, 553312823163434, 551343321859268,
    549338556834469, 547298506637066, 545223142646156, 543112428918655, 540966322025369,
    538784770875841, 536567716531412, 534315092005868, 532026822053015, 529702822940454,
    527343002208799, 524947258415470, 522515480862198, 520047549305232, 517543333647212,
    515002693609567, 512425478384203, 509811526263146, 507160664244702, 504472707614562,
    501747459500153, 498984710396401, 496184237660886, 493345804976227, 490469161777315,
    487554042640809, 484600166634086, 481607236620554, 478574938517976, 475502940506110,
    472390892179652, 469238423642026, 466045144535201, 462810643000156]
private def phb_m16_r256_7_p3 : List ℕ :=
  [459534484562124, 456216210934130, 452855338731644, 449451358090426, 446003731178793,
    442511890594550, 438975237635771, 435393140433381, 431764931932093, 428089907704690,
    424367323582858, 420596393085712, 416776284624842, 412906118462040, 408984963392781,
    405011833125017, 400985682318764, 396905402247248, 392769816034891, 388577673421057,
    384327644991029, 380018315806945, 375648178361207, 371215624762710, 366718938051958,
    362156282524040, 357525692918118, 352825062307627, 348052128496024, 343204458687322,
    338279432157346, 333274220598756, 328185765747808, 323010753820327, 317745586184281,
    312386345570841, 306928756967628, 301368142136721, 295699366442374, 289916776340594,
    284014125448755, 277984486542143, 271820146064150, 265512476713831, 259051782280705,
    252427106971909, 245625998779622, 238634212595823, 231435333214295, 224010290130651,
    216336723618594, 208388142312421, 200132781890373, 191532024136651, 182538149974494,
    173091047883606, 163113215115960, 152501826716118, 141115449784521, 128750187127827,
    115092699143001, 99614893420520, 81285940743224, 57441810570265]
private def phb_m16_r256_7 : List ℕ :=
  pCat phb_m16_r256_7_p0
    (pCat phb_m16_r256_7_p1
    (pCat phb_m16_r256_7_p2
      phb_m16_r256_7_p3))
private def pvn_m16_r256_7_0_p0 : List ℕ :=
  [1999490344790881, 2000098231097226, 1999924048573838, 1999969269138575, 1999951022615467,
    2000157417822682, 2000129604739203, 2000385839450183, 2000232481203882, 1999870861573580,
    1999422327595848, 1999875441580974, 2000526305035167, 1999990878195561, 1999835439698915,
    1999975735968718, 2000060470238433, 1999896270468559, 2000067360976135, 2000386288693578,
    2000334340011339, 1999755709649143, 2000233851774532, 2000209252123907, 2000834628690421,
    2000160278824076, 1999863191641967, 2000224495423200, 2000371976104083, 2000073105386720,
    2000242638484379, 2000316407511158, 2000256497853564, 2000269276137205, 1999819782494874,
    1999742348784025, 2000022010931683, 1999576877675563, 1999634393377814, 2000691190914691,
    2000254635060196, 1999869030003628, 1999938187566828, 1999903785866577, 2000341967453506,
    2000415361062534, 1999771008369158, 2000836006864946, 2000647302571945, 1999911401682711,
    2000313883889365, 2000552635261713, 2000051174488447, 1999324100796971, 2000004055491401,
    2000388257848420, 2000061018308039, 1999770006073781, 2000015304029381, 2000710363895888,
    1999585347827500, 2000486732195699, 1999587793893908, 2000810956967530]
private def pvn_m16_r256_7_0_p1 : List ℕ :=
  [1999561328653303, 1999856685947691, 2000504387965016, 1999831163579403, 2000471427841974,
    2000204246728633, 2000225538405933, 1999855094692395, 1999914315278184, 2000304528170289,
    2000186253918916, 1999939587226437, 1999778964547246, 2000407790700385, 2000056290709655,
    1999820213169265, 1999625351155413, 1999876646518940, 1999777125886207, 1999961448930661,
    2000137691305458, 2000201535093179, 2000040953018857, 1999778477074922, 2000026991642583,
    1999909679209000, 1999558622713721, 1999060357663125, 2000420023565604, 1999732368726288,
    1999912784803086, 2000069801421851, 2000356112803782, 1999454660140061, 1999318349285601,
    2001693780987734, 2001485867282471, 2000536334848679, 2000098010328170, 1999806408056844,
    2001398329915779, 2001303551904869, 2000151440056286, 2000381906180289, 2000307122329463,
    2000425106292738, 2000857362038041, 2000110370220906, 1999730131806317, 1999869575012870,
    2001155976493839, 2000564056263326, 2000423104094342, 1998894042059709, 1999778875832854,
    2001763347739638, 2001342707803957, 2000385433382984, 1999667014329430, 2000735986936309,
    2001503683779902, 2001766068436874, 2000803508278873, 1999322603497804]
private def pvn_m16_r256_7_0_p2 : List ℕ :=
  [1999534935205238, 2001395960694895, 1998015552643022, 2001468539259354, 1999777512907392,
    1999191671786752, 1999420811612222, 2001230933841065, 2003696688655299, 2000999309256088,
    1997423095310090, 2001814794170220, 2001210941823819, 2005194727112475, 1999636289656142,
    1997516560263266, 2000109767922303, 2001372689714796, 1999177419343255, 2003434729811900,
    1995329058165650, 1999892983840688, 1996942793587701, 1996013737487167, 2002291634017943,
    1996186398931375, 1998756152614964, 1999623828821994, 2000472836887785, 1996321832421114,
    2001821918805457, 1994576641601518, 2002039069957339, 1999174181939236, 1996077271814950,
    2002825144356509, 1999361615868863, 2004695294160192, 2002936657088326, 2002119754115338,
    1995484679717127, 2001528593241215, 2003775217908075, 2002967134306786, 1999079107831262,
    1997155401511209, 2000545234070936, 2002807452174254, 1995014089757190, 2004167500329912,
    2003842628846590, 1995510375764051, 2001306929111820, 1999775231774537, 1998850052051840,
    2002900616173738, 2003979679829025, 2000349620247812, 2003412835660299, 1994906368045292,
    2001205052879418, 2004546969604515, 1998796425892318, 1995003579974550]
private def pvn_m16_r256_7_0_p3 : List ℕ :=
  [2006118672441494, 1989808777453732, 1992801430970223, 2004778652895945, 1999642913187502,
    1995330564828139, 2010421140623263, 1999825757341927, 2010411198464758, 2012305740321674,
    2001254970908229, 1993505515491606, 2007342333756437, 1995161649403872, 1977725103747343,
    2012352775882434, 1997898738204765, 1990845341887532, 2004525166928118, 2017018727117117,
    1973976081111385, 2017150588951129, 2002918042696147, 1990735111406856, 2003195324184180,
    2014658287955243, 1985660750337611, 1995990748756998, 1998873151592414, 2001766342401822,
    1989773763655696, 2011438739483595, 2002109659803872, 2007218016859696, 1984268960120372,
    2013228812759658, 1992930928362446, 2023264355199115, 2021705132969229, 2013854638470514,
    1962587279807888, 2020813655918943, 1974819627607211, 1967827827928685, 1993638944800634,
    2033551778296619, 2013929244250945, 2024943062199532, 2034870925448852, 2008875614165720,
    2066795474130738, 2016111903110018, 2085918557822727, 2001475238998232, 2049180959683702,
    2076139377018390, 2030132837122824, 2105201234283417, 2041161586000071, 2030803933249797,
    2170204563130918, 2100486232855054, 2053681092176956, 2405902548826158]
private def pvn_m16_r256_7_0_p4 : List ℕ := [2863574417487093]
private def pvn_m16_r256_7_0 : List ℕ :=
  pCat pvn_m16_r256_7_0_p0
    (pCat pvn_m16_r256_7_0_p1
    (pCat pvn_m16_r256_7_0_p2
    (pCat pvn_m16_r256_7_0_p3
      pvn_m16_r256_7_0_p4)))
private def pvn_m16_r256_7_1_p0 : List ℕ :=
  [1999482412634813, 1999944707768456, 1999946415378665, 2000006083122887, 1999863335927814,
    2000047443711421, 1999971686992925, 2000119076688952, 2000234998553395, 2000454462737422,
    2000286983089020, 1999423164714533, 1999636958257859, 2000152867288179, 2000241339959069,
    1999950198072918, 1999957415222407, 2000025811586109, 2000071564200288, 1999577514891625,
    2000300622672075, 2000162511752017, 2000404043393137, 1999964260506912, 1999764632787435,
    2000319511060892, 2000718335845845, 2000239126520606, 2000068305859680, 2000251836974940,
    2000136323631690, 2000222848740220, 2000194814107839, 2000055345571629, 2000445056106030,
    2000529484937543, 1999763924812026, 2000228821829971, 2000210833411336, 1999433178542579,
    1999563066964782, 2000027793499433, 2000064519753329, 2000642874102845, 1999739178368599,
    1999702486142295, 2000481037101805, 1999989316796835, 1999804340610313, 2000287316323055,
    2000806667782603, 2000169456834404, 2000038725418525, 2000730922269824, 2000529537101120,
    2000251860987695, 1999116287138558, 2000679524879660, 1999643678173779, 2000349364547732,
    1999560250157373, 2000162751600237, 2000607637106759, 1999509445193339]
private def pvn_m16_r256_7_1_p1 : List ℕ :=
  [2000345279072377, 2000202221400900, 2000127486008063, 2000003724716653, 1999998400511349,
    2000066565528071, 1999899170114463, 2000255222113320, 2000337341197211, 2000441771171890,
    1999766835414446, 2000002406161377, 2000266441830747, 2000247629344751, 1999816745513835,
    1999984024286469, 2000225311532151, 2000158927215971, 2000056772609268, 1999840769867397,
    1999918309884658, 1999589309981228, 1999859345577826, 1999716546594314, 2000660730899438,
    1999597882983450, 1999989829969667, 2000368223137527, 2000085779734540, 1999541622120726,
    1999341952497776, 2000328872498565, 1999238246775012, 1999364400071835, 2000936598387955,
    2000089240407285, 1999465827686749, 1999168873459842, 1999844570411134, 2001667788702426,
    2001208571669767, 1999953952860975, 2000306865753269, 2000491581550163, 2001107282568364,
    2000822298102277, 2000833676406590, 1999740413291120, 2000787580886923, 2000795679886456,
    2000551964576680, 2000226518388772, 1999162625450076, 2000454071461990, 2001385260133881,
    2000818767521353, 1999150255720760, 1999256170327131, 2000577212713784, 2001464622758807,
    2000503982403629, 2001181366752529, 1998045416504540, 2002464466913708]
private def pvn_m16_r256_7_1_p2 : List ℕ :=
  [2001442947193635, 2000651233400168, 2001201810056779, 2000292172741823, 1999778658466057,
    1999738126764197, 1999547746496994, 2002977372804591, 1996812692660222, 1999246164099325,
    2000043187720477, 2002752437730320, 2002541936713891, 1999251537032466, 1996720889689238,
    2005450991804872, 2000355806937908, 2003721144184023, 1999996903423045, 1997000534782564,
    2003204064740495, 1998127260268942, 2002392662825084, 2000739668082762, 1998675565179969,
    1995222501334540, 2002069657857879, 1994706404236862, 2000195999894160, 1998052306221015,
    1996826293654236, 2003366912617982, 1995821820580613, 1999637403834268, 1998276970782520,
    2000017468078278, 1997270636557962, 2000334174041525, 1996847279304639, 1999094932425959,
    2004453295458555, 2004647220246614, 2000307443716883, 1998751786847656, 1997904955550956,
    2007383560493279, 2000846770879546, 1996819151886002, 2004998457268767, 1997574827847381,
    1997139152702277, 2002324627341347, 2001468519357026, 1999473886865032, 2003437169161709,
    1996258540995217, 2001127176044164, 1998881136809196, 2000248630669590, 2004700001142821,
    2006001809848754, 1992030122883080, 2004976678598957, 2002659895753014]
private def pvn_m16_r256_7_1_p3 : List ℕ :=
  [1994816789533930, 2003609209799104, 2006648558377843, 1987609659437751, 2000767405800008,
    1996022327157217, 1995817910302823, 2001252175365645, 2001405542149716, 1994959966422927,
    2009685147628627, 2019450207818777, 1989627010122358, 2013809719224541, 2007612356295612,
    1989151354386725, 1986197555208186, 2018079481472072, 1973285991141699, 2005590410175488,
    2010393178005734, 1991534569250395, 1996351535976695, 2015787264811857, 1988599318179353,
    1999907525033244, 2007321279160522, 2007579160963032, 1987250286027704, 2005419649760127,
    1992069826112743, 2001285008712160, 1985651370680975, 2019628646353514, 1994023876288584,
    2006996151859834, 1993917698037111, 2002535603715970, 1983044411522878, 2052669820411141,
    2001797023197554, 1995952023924652, 2008462299321691, 1999344521918260, 1956544505992148,
    1984101001680826, 2012916421826978, 1999702213341478, 2048991883714844, 1992040418336191,
    2058754085971293, 2000229454306281, 2073845670192474, 2048834034012488, 2009288247122637,
    2078137557822096, 2022405862283500, 2079982861423427, 2095483956548488, 1993922254411686,
    2114009612068368, 2158899045069789, 2005296518663961, 2205632690739144]
private def pvn_m16_r256_7_1_p4 : List ℕ := [2934444148800212]
private def pvn_m16_r256_7_1 : List ℕ :=
  pCat pvn_m16_r256_7_1_p0
    (pCat pvn_m16_r256_7_1_p1
    (pCat pvn_m16_r256_7_1_p2
    (pCat pvn_m16_r256_7_1_p3
      pvn_m16_r256_7_1_p4)))
private def pwalks_m16_r256 : List RkmSegWalk := [
  ⟨uOfHb phb_m16_r256_0, bDec bZ (zPad bZ 1 pvn_m8_r256_0_0),
    bDec bZ (zPad bZ 33 pvn_m16_r256_0_1)⟩,
  ⟨uOfHb phb_m16_r256_1, bDec bZ (zPad bZ 33 pvn_m16_r256_0_1),
    bDec bZ (zPad bZ 65 pvn_m16_r256_1_1)⟩,
  ⟨uOfHb phb_m16_r256_2, bDec bZ (zPad bZ 65 pvn_m16_r256_2_0),
    bDec bZ (zPad bZ 129 pvn_m16_r256_2_2)⟩,
  ⟨uOfHb phb_m16_r256_3, bDec bZ (zPad bZ 129 pvn_m16_r256_3_0),
    bDec bZ (zPad bZ 257 pvn_m16_r256_3_3)⟩,
  ⟨uOfHb phb_m16_r256_4, bDec bZ (zPad bZ 257 pvn_m16_r256_4_0),
    bDec bZ (zPad bZ 257 pvn_m16_r256_4_4)⟩,
  ⟨uOfHb phb_m16_r256_5, bDec bZ (zPad bZ 257 pvn_m16_r256_5_0),
    bDec bZ (zPad bZ 257 pvn_m16_r256_5_6)⟩,
  ⟨uOfHb phb_m16_r256_6, bDec bZ (zPad bZ 257 pvn_m16_r256_6_0),
    bDec bZ (zPad bZ 257 pvn_m16_r256_6_2)⟩,
  ⟨uOfHb phb_m16_r256_7, bDec bZ (zPad bZ 257 pvn_m16_r256_7_0),
    bDec bZ (zPad bZ 257 pvn_m16_r256_7_1)⟩
  ]
private def phb_m32_r256_0 : List ℕ :=
  [253625920117836, 352342148917568, 423678842394630, 480051597196374, 526335850181062,
    565058004974805, 597729048331942, 625335861545688, 648561821556052, 667899407847483,
    683713098786320, 696276882838420, 705797719761662, 712430688724791, 716288912710297,
    717449995312135, 715959962560820, 711835259712515, 705063058570809, 695599899807332,
    683368467936869, 668252016446361, 650085546680481, 628642154467263, 603611706682315,
    574566561908282, 540903870460272, 501741960911678, 455716844864269, 400527967797141,
    331702487285892, 237774300110471]
private def pvn_m32_r256_0_1 : List ℕ :=
  [2007385747787024, 2025308603943992, 2060196556711896, 2114695212702656, 2185575689653269,
    2263179539509824, 2333674258332834, 2383308996383807, 2402794944554529, 2389938998373333,
    2349626332439300, 2291524353221977, 2226755912206908, 2164919721760664, 2112346293094190,
    2071766579776139, 2043018559371202, 2024202126483369, 2012776582922663, 2006324702329275,
    2002932364069335, 2001271158023144, 2000513997891319, 2000193262168508, 2000067294726926,
    2000021584408566, 2000006332112457, 2000001682855601, 2000000399771691, 2000000083224889,
    2000000014709929, 2000000002082307, 2000000000204549]
private def phb_m32_r256_1 : List ℕ :=
  [188840368000000, 264447966133239, 320669901845541, 366555754820430, 405644662792179,
    439767732401753, 470021679026304, 497126555982774, 521586061470471, 543769306469565,
    563956549221986, 582366612288984, 599174234331600, 614521541263475, 628525906555662,
    641285501180194, 652883313040330, 663390121883126, 672866742716147, 681365745178930,
    688932789823687, 695607679197979, 701425193039732, 706415757498275, 710605984864356,
    714019110817842, 716675349400810, 718592180958569, 719784584604236, 720265223975731,
    720044592905381, 719131125926994, 717531277169013, 715249570025258, 712288618978518,
    708649124012409, 704329837125859, 699327499506215, 693636746861002, 687249979184700,
    680157189757427, 672345746321562, 663800115001524, 654501514398148, 644427483080705,
    633551337943153, 621841492875544, 609260595836332, 595764425988802, 581300468345926,
    565806046846314, 549205840329911, 531408516158537, 512302069057495, 491747202462337,
    469567645696961, 445535472842375, 419347852610152, 390588178266729, 358656419756489,
    322632280024707, 280969155564542, 230659319255496, 163965889711693]
private def pvn_m32_r256_1_1_p0 : List ℕ :=
  [2000000000111156, 2000000001044501, 2000000006825462, 2000000035809573, 2000000159962556,
    2000000628251806, 2000002213791045, 2000007096885632, 2000020908607438, 2000057048625926,
    2000145023718976, 2000345142820797, 2000772027363444, 2001628380428253, 2003247544200022,
    2006138110560035, 2011016693691084, 2018807854492510, 2030586589840967, 2047443046847336,
    2070264419272711, 2099455086898009, 2134647409887860, 2174481449818524, 2216539343564458,
    2257499435339967, 2293525877583051, 2320842535301265, 2336376868204773, 2338323771087381,
    2326487512000836, 2302313023577019, 2268599913946602, 2228976365703717, 2187267799165278,
    2146909525514300, 2110522969726310, 2079716139433635, 2055103558547266, 2036489945104844,
    2023137571578818, 2014040171495601, 2008148202554826, 2004519319445280, 2002393599293984,
    2001209471692810, 2000582440534093, 2000266995696712, 2000116350604351, 2000048125725602,
    2000018861010931, 2000006989543594, 2000002443444706, 2000000803566787, 2000000247787280,
    2000000071360372, 2000000019101171, 2000000004723639, 2000000001070960, 2000000000220369,
    2000000000040583, 2000000000006552, 2000000000000895, 2000000000000095]
private def pvn_m32_r256_1_1_p1 : List ℕ := [2000000000000006]
private def pvn_m32_r256_1_1 : List ℕ :=
  pCat pvn_m32_r256_1_1_p0
      pvn_m32_r256_1_1_p1
private def phb_m32_r256_2_p0 : List ℕ :=
  [148433833083716, 208686753875244, 254080124384516, 291644101923528, 324118671587494,
    352917323394442, 378884531378112, 402573596325999, 424370956199493, 444559497062145,
    463353912939492, 480921874508021, 497397409472671, 512889738282846, 527489322856435,
    541272134434493, 554302743353399, 566636606070505, 578321791008541, 589400303213229,
    599909116489092, 609880988473998, 619345112101327, 628327641984768, 636852123955858,
    644939848736853, 652610145551756, 659880627721606, 666767399528732, 673285231579670,
    679447710349569, 685267366414247, 690755784972150, 695923701557762, 700781085300166,
    705337211648740, 709600726145166, 713579700546843, 717281682386223, 720713738871874,
    723882495891552, 726794172758282, 729454613242234, 731869313349858, 734043446244095,
    735981884642947, 737689220986241, 739169785620381, 740427663217028, 741466707612821,
    742290555232685, 742902637238183, 743306190524240, 743504267671910, 743499745951248,
    743295335456506, 742893586445528, 742296895946043, 741507513683550, 740527547378252,
    739358967452120, 738003611181320, 736463186324019, 734739274248698]
private def phb_m32_r256_2_p1 : List ℕ :=
  [732833332583652, 730746697404145, 728480584969689, 726036093020085, 723414201635134,
    720615773659187, 717641554688012, 714492172611609, 711168136702695, 707669836236410,
    703997538622385, 700151387025530, 696131397446721, 691937455228788, 687569310946858,
    683026575634894, 678308715292182, 673415044604296, 668344719802452, 663096730573023,
    657669890914820, 652062828825353, 646273974678020, 640301548129621, 634143543370880,
    627797712501047, 621261546769934, 614532255385598, 607606741531583, 600481575171954,
    593152962142533, 585616708929230, 577868182414451, 569902263724369, 561713295125462,
    553295018687749, 544640505140907, 535742070979278, 526591181397685, 517178336027467,
    507492933643632, 497523110962811, 487255549253044, 476675240594265, 465765203064078,
    454506130582541, 442875958188115, 430849316452013, 418396838498520, 405484267963967,
    392071293363061, 378109998935427, 363542765714068, 348299364044357, 332292821254119,
    315413368427929, 297519248220785, 278422131992969, 257862693769503, 235466755860756,
    210658944044982, 182469164243723, 149003499913997, 105367766687280]
private def phb_m32_r256_2 : List ℕ :=
  pCat phb_m32_r256_2_p0
      phb_m32_r256_2_p1
private def pvn_m32_r256_2_0_p0 : List ℕ :=
  [2000000000111156, 1999999998955499, 1999999993174538, 2000000035809573, 2000000159962556,
    2000000628251806, 2000002213791045, 2000007096885632, 2000020908607438, 1999942951374074,
    1999854976281024, 1999654857179203, 2000772027363444, 2001628380428253, 2003247544200022,
    2006138110560035, 2011016693691084, 2018807854492510, 2030586589840967, 2047443046847336,
    2070264419272711, 2099455086898009, 2134647409887860, 2174481449818524, 2216539343564458,
    2257499435339967, 2293525877583051, 2320842535301265, 2336376868204773, 2338323771087381,
    2326487512000836, 2302313023577019, 2268599913946602, 2228976365703717, 2187267799165278,
    2146909525514300, 2110522969726310, 2079716139433635, 2055103558547266, 2036489945104844,
    2023137571578818, 2014040171495601, 2008148202554826, 2004519319445280, 2002393599293984,
    2001209471692810, 2000582440534093, 2000266995696712, 2000116350604351, 2000048125725602,
    2000018861010931, 2000006989543594, 2000002443444706, 2000000803566787, 2000000247787280,
    2000000071360372, 2000000019101171, 2000000004723639, 2000000001070960, 1999999999779631,
    1999999999959417, 2000000000006552, 2000000000000895, 2000000000000095]
private def pvn_m32_r256_2_0_p1 : List ℕ := [2000000000000006]
private def pvn_m32_r256_2_0 : List ℕ :=
  pCat pvn_m32_r256_2_0_p0
      pvn_m32_r256_2_0_p1
private def pvn_m32_r256_2_1_p0 : List ℕ :=
  [2000056382929465, 1999865810560676, 2000157997643285, 1999947173371853, 1999902038150724,
    2000094682184037, 2000063425837350, 1999901628920033, 1999935596802126, 2000087338001749,
    2000090789994332, 1999948473325185, 1999878583932970, 1999975374050014, 2000108869648825,
    2000118791139217, 1999997692915592, 1999871636975873, 1999856965893069, 1999961912381171,
    2000102440131385, 2000182534620811, 2000158697308413, 2000051081907360, 1999914416788235,
    1999801300834076, 1999740765620482, 1999736561731177, 1999777834416103, 1999853026416874,
    1999961858566571, 2000125038995879, 2000394217008859, 2000865224127766, 2001696465037511,
    2003132067804031, 2005526433391952, 2009363413643106, 2015260122203378, 2023943431873928,
    2036188105192258, 2052710579444448, 2074022260881119, 2100259562880351, 2131021761942671,
    2165257360967423, 2201240188272129, 2236664874209061, 2268868073583869, 2295151624193676,
    2313154958452330, 2321205639576326, 2318575713408950, 2305589423286407, 2283560405285793,
    2254574647070356, 2221168429924929, 2185969334316916, 2151369159599854, 2119282018484751,
    2091015190003949, 2067252769601481, 2048130049317016, 2033364235478475]
private def pvn_m32_r256_2_1_p1 : List ℕ :=
  [2022405271393612, 2014576907515734, 2009188938974348, 2005612875284873, 2003322442084318,
    2001905943635644, 2001059664900046, 2000571024599320, 2000298254809557, 2000151001675689,
    2000074105370935, 2000035253275946, 2000016256801813, 2000007266999991, 2000003148845410,
    2000001322533552, 2000000538385937, 2000000212408797, 2000000081206268, 2000000030079936,
    2000000010793253, 2000000003750766, 2000000001262038, 2000000000411040, 2000000000129546,
    2000000000039496, 2000000000011643, 2000000000003316, 2000000000000909, 2000000000000239,
    2000000000000059, 2000000000000013, 2000000000000001]
private def pvn_m32_r256_2_1 : List ℕ :=
  pCat pvn_m32_r256_2_1_p0
      pvn_m32_r256_2_1_p1
private def pvn_m32_r256_2_2_p0 : List ℕ :=
  [2000086620081754, 2000141400330439, 2000118904584166, 2000020318073102, 1999919789593402,
    1999900074026860, 1999972759284944, 2000065543023535, 2000091028476528, 2000028838356431,
    1999941430117168, 1999911701597519, 1999965368390200, 2000050650427966, 2000089313560011,
    2000047670229109, 1999963533766808, 1999909853202093, 1999931559956745, 2000010294764338,
    2000082684164071, 2000092313619349, 2000032043872844, 1999946231870602, 1999895853112811,
    1999915391106785, 1999991768539422, 2000076252823426, 2000117279898255, 2000091169183615,
    2000013023933115, 1999924843318866, 1999871124532510, 1999876824107033, 1999938155852041,
    2000028012711432, 2000110457775238, 2000155997271196, 2000151162605413, 2000100066739104,
    2000019479069685, 1999930986021749, 1999853765432398, 1999800144858488, 1999774441300788,
    1999774355592682, 1999793724010666, 1999825631043778, 1999865515909427, 1999914719798501,
    1999985737078630, 2000111101145566, 2000358144688744, 2000851467589053, 2001803354463974,
    2003549234998008, 2006580639861341, 2011562853984250, 2019320491090122, 2030774116618786,
    2046817276515048, 2068136812723556, 2094998410220256, 2127039008015269]
private def pvn_m32_r256_2_2_p1 : List ℕ :=
  [2163120872163274, 2201301767580479, 2238957987439501, 2273063882250440, 2300591019045002,
    2318954313694192, 2326413465341295, 2322343155216494, 2307314371223869, 2282973605427879,
    2251753293174569, 2216482262634611, 2179980090328894, 2144712115053384, 2112557355749241,
    2084708962842042, 2061696060912665, 2043494345787001, 2029683774150040, 2019614139349970,
    2012549473265205, 2007775344772648, 2004665230792359, 2002710796528635, 2001525427330423,
    2000831279029507, 2000438673980353, 2000224153018997, 2000110894848276, 2000053111257783,
    2000024620790130, 2000011045260364, 2000004794161596, 2000002012802074, 2000000817172541,
    2000000320704981, 2000000121622172, 2000000044550237, 2000000015754697, 2000000005376015,
    2000000001769057, 2000000000560997, 2000000000171310, 2000000000050328, 2000000000014210,
    2000000000003848, 2000000000000994, 2000000000000243, 2000000000000054, 2000000000000010,
    2000000000000001]
private def pvn_m32_r256_2_2 : List ℕ :=
  pCat pvn_m32_r256_2_2_p0
      pvn_m32_r256_2_2_p1
private def phb_m32_r256_3_p0 : List ℕ :=
  [119820732377088, 168790182496853, 205914224431313, 236833166339088, 263740938604150,
    287767239795085, 309585800565820, 329637297582090, 348229003470912, 365585496209400,
    381876957830062, 397236102249384, 411768866584430, 425561465617722, 438685217376932,
    451199945357472, 463156439746499, 474598277844093, 485563196788736, 496084146422093,
    506190109072500, 515906746489623, 525256916571978, 534261090615576, 542937693583680,
    551303384113227, 559373286840970, 567161186636582, 574679692128813, 581940374273304,
    588953884478748, 595730055871247, 602277990557468, 608606135189816, 614722346701273,
    620633949734448, 626347787017082, 631870263718667, 637207386647721, 642364799007611,
    647347811313392, 652161428977674, 656810376995756, 661299122095961, 665631892667619,
    669812696734543, 673845338204395, 677733431592827, 681480415394688, 685089564251934,
    688564000048717, 691906702047609, 695120516166920, 698208163486879, 701172248062055,
    704015264108331, 706739602624921, 709347557505103, 711841331183378, 714223039861617,
    716494718352147, 718658324571778, 720715743717229, 722668792149312]
private def phb_m32_r256_3_p1 : List ℕ :=
  [724519221010488, 726268719597993, 727918918512543, 729471392600737, 730927663707569,
    732289203253908, 733557434652463, 734733735574538, 735819440078755, 736815840611971,
    737724189891714, 738545702678666, 739281557447008, 739932897959783, 740500834755860,
    740986446554519, 741390781583232, 741714858833746, 741959669251187, 742126176860530,
    742215319834470, 742228011506393, 742165141331906, 742027575802096, 741816159311490,
    741531714983440, 741175045455500, 740746933627149, 740248143372071, 739679420217038,
    739041491989323, 738335069434401, 737560846805628, 736719502427442, 735811699233534,
    734838085281360, 733799294244258, 732695945882371, 731528646493476, 730297989344795,
    729004555086737, 727648912149528, 726231617123575, 724753215124387, 723214240142825,
    721615215381394, 719956653577272, 718239057312703, 716462919313369, 714628722735310,
    712736941440927, 710788040264584, 708782475268282, 706720693987868, 704603135670203,
    702430231501698, 700202404828608, 697920071369439, 695583639419828, 693193510050208,
    690750077296585, 688253728344711, 685704843707940, 683103797399030]
private def phb_m32_r256_3_p2 : List ℕ :=
  [680450957096146, 677746684303301, 674991334505473, 672185257318603, 669328796634687,
    666422290762170, 663466072561806, 660460469578186, 657405804167091, 654302393618841,
    651150550277786, 647950581658099, 644702790555998, 641407475158547, 638064929149153,
    634675441809888, 631239298120753, 627756778855999, 624228160677604, 620653716226018,
    617033714208272, 613368419483547, 609658093146285, 605902992606941, 602103371670449,
    598259480612488, 594371566253620, 590439872031375, 586464638070353, 582446101250411,
    578384495272998, 574280050725698, 570132995145049, 565943553077685, 561711946139862,
    557438393075421, 553123109812231, 548766309517175, 544368202649714, 539928997014074,
    535448897810112, 530928107682885, 526366826770983, 521765252753638, 517123580896678,
    512442004097332, 507720712927945, 502959895678618, 498159738398818, 493320424937979,
    488442136985137, 483525054107610, 478569353788767, 473575211464908, 468542800561274,
    463472292527219, 458363856870575, 453217661191209, 448033871213829, 442812650820031,
    437554162079619, 432258565281229, 426926018962256, 421556679938122]
private def phb_m32_r256_3_p3 : List ℕ :=
  [416150703330887, 410708242597237, 405229449555855, 399714474414192, 394163465794662,
    388576570760269, 382953934839685, 377295702051790, 371602014929692, 365873014544243,
    360108840527053, 354309631093029, 348475523062442, 342606651882538, 336703151648704,
    330765155125198, 324792793765460, 318786197732007, 312745495915929, 306670815955994,
    300562284257365, 294420026009954, 288244165206404, 282034824659724, 275792126020572,
    269516189794203, 263207135357092, 256865080973228, 250490143810102, 244082439954386,
    237642084427309, 231169191199750, 224663873207040, 218126242363486, 211556409576628,
    204954484761227, 198320576852991, 191654793822057, 184957242686214, 178228029523895,
    171467259486925, 164675036813042, 157851464838190, 150996646008595, 144110681892619,
    137193673192411, 130245719755343, 123266920585253, 116257373853483, 109217176909728,
    102146426292698, 95045217740590, 87913646201383, 80751805842954, 73559790063025,
    66337691498933, 59085602037243, 51803612823194, 44491814269982, 37150296067898,
    29779147193303, 22378455917462, 14948309815224, 7488795773568]
private def phb_m32_r256_3 : List ℕ :=
  pCat phb_m32_r256_3_p0
    (pCat phb_m32_r256_3_p1
    (pCat phb_m32_r256_3_p2
      phb_m32_r256_3_p3))
private def pvn_m32_r256_3_0_p0 : List ℕ :=
  [2000086620081754, 1999858599669561, 1999881095415834, 1999979681926898, 1999919789593402,
    1999900074026860, 1999972759284944, 1999934456976465, 2000091028476528, 1999971161643569,
    2000058569882832, 1999911701597519, 2000034631609800, 1999949349572034, 2000089313560011,
    2000047670229109, 1999963533766808, 2000090146797907, 2000068440043255, 1999989705235662,
    1999917315835929, 2000092313619349, 2000032043872844, 1999946231870602, 2000104146887189,
    2000084608893215, 2000008231460578, 2000076252823426, 2000117279898255, 1999908830816385,
    2000013023933115, 2000075156681134, 2000128875467490, 1999876824107033, 2000061844147959,
    1999971987288568, 2000110457775238, 2000155997271196, 2000151162605413, 2000100066739104,
    2000019479069685, 1999930986021749, 2000146234567602, 1999800144858488, 1999774441300788,
    1999774355592682, 1999793724010666, 1999825631043778, 2000134484090573, 1999914719798501,
    2000014262921370, 1999888898854434, 2000358144688744, 2000851467589053, 2001803354463974,
    2003549234998008, 2006580639861341, 2011562853984250, 2019320491090122, 2030774116618786,
    2046817276515048, 2068136812723556, 2094998410220256, 2127039008015269]
private def pvn_m32_r256_3_0_p1 : List ℕ :=
  [2163120872163274, 2201301767580479, 2238957987439501, 2273063882250440, 2300591019045002,
    2318954313694192, 2326413465341295, 2322343155216494, 2307314371223869, 2282973605427879,
    2251753293174569, 2216482262634611, 2179980090328894, 2144712115053384, 2112557355749241,
    2084708962842042, 2061696060912665, 2043494345787001, 2029683774150040, 2019614139349970,
    2012549473265205, 2007775344772648, 2004665230792359, 2002710796528635, 2001525427330423,
    2000831279029507, 2000438673980353, 2000224153018997, 1999889105151724, 1999946888742217,
    1999975379209870, 1999988954739636, 1999995205838404, 1999997987197926, 2000000817172541,
    2000000320704981, 2000000121622172, 2000000044550237, 2000000015754697, 2000000005376015,
    2000000001769057, 2000000000560997, 2000000000171310, 2000000000050328, 2000000000014210,
    2000000000003848, 1999999999999006, 2000000000000243, 2000000000000054, 2000000000000010,
    2000000000000001]
private def pvn_m32_r256_3_0 : List ℕ :=
  pCat pvn_m32_r256_3_0_p0
      pvn_m32_r256_3_0_p1
private def pvn_m32_r256_3_1_p0 : List ℕ :=
  [2000101709450107, 1999892846029442, 2000031999432389, 2000095077639463, 2000027182337140,
    2000122241354338, 2000081871868340, 1999991379559932, 2000037164482340, 1999957112534226,
    2000011951583588, 1999884769788415, 1999996695780297, 1999876333371407, 2000072065078608,
    1999932709003678, 1999912187256784, 1999926949449327, 2000043949712504, 1999912350292025,
    1999929569637914, 1999746341881335, 2000092644295667, 2000032700645374, 1999985715576009,
    1999880528473518, 2000141179128827, 1999929643378523, 2000020592333038, 2000007017603500,
    1999919101575487, 2000074239072144, 2000001490331521, 1999882344365111, 2000007116197926,
    2000105823365524, 2000046577349981, 1999980927031831, 2000012233241250, 2000063199810662,
    2000034830318714, 2000004382645514, 2000041700893307, 2000033934709605, 1999943580643039,
    1999926074008275, 2000030382190262, 2000106337032564, 2000076556518766, 2000026444573198,
    2000014370953616, 2000010036384442, 2000011629419672, 2000057483730964, 2000116045164208,
    2000104422183316, 2000005216273682, 1999932626353536, 1999944585775056, 2000047822183404,
    2000064572402531, 2000063829957105, 1999949052102165, 2000013750295602]
private def pvn_m32_r256_3_1_p1 : List ℕ :=
  [2000035464079752, 2000199199755632, 2000217064222116, 2000172664616259, 2000102649418258,
    1999940326143428, 1999910622990730, 1999878636188827, 1999854441650867, 1999916394321769,
    1999895112786455, 1999874695231071, 1999911044916170, 1999877504420544, 1999865813103439,
    1999916239942585, 1999890757694149, 1999828574581883, 1999790507067468, 1999687119938993,
    1999607222367225, 1999874996555938, 2000852877876038, 2003124207154167, 2007680020751464,
    2015674425948230, 2028190752312960, 2046222956202328, 2070458119347291, 2100841545863720,
    2136377753440361, 2175246834858429, 2214946471488192, 2252437603741551, 2284513662731549,
    2308360771761594, 2322012623309041, 2324540755143386, 2316074609959899, 2297753343043417,
    2271570551328593, 2240055755066286, 2205859837185626, 2171392316636141, 2138605205209003,
    2108913293191156, 2083191854142111, 2061813445742745, 2044719950870253, 2031532100538737,
    2021681378635523, 2014535083827672, 2009489140258696, 2006019620182571, 2003699652380507,
    2002195373220917, 2001253187178662, 2000685552442787, 2000357991317485, 2000177676509436,
    2000083377321625, 2000036735551254, 2000015037442010, 2000005617360054]
private def pvn_m32_r256_3_1_p2 : List ℕ :=
  [2000001847959242, 2000000488780646, 2000000068229737, 1999999971804190, 1999999967877948,
    1999999980670865, 1999999990862419, 1999999996365938, 1999999998795704, 1999999999702615,
    1999999999978995, 2000000000035405, 2000000000031400, 2000000000018582, 2000000000009268,
    2000000000004162, 2000000000001729, 2000000000000673, 2000000000000245, 2000000000000083,
    2000000000000025, 2000000000000006]
private def pvn_m32_r256_3_1 : List ℕ :=
  pCat pvn_m32_r256_3_1_p0
    (pCat pvn_m32_r256_3_1_p1
      pvn_m32_r256_3_1_p2)
private def pvn_m32_r256_3_2_p0 : List ℕ :=
  [2000022589355523, 1999995098571394, 2000207149013757, 2000010378881809, 2000106365809855,
    1999941316644876, 2000015916671224, 1999925572184815, 2000111889672286, 1999868784580617,
    2000047260718997, 1999977278247992, 2000035821527757, 1999987600155689, 2000047733968412,
    2000137861878865, 2000013125700495, 2000061924196199, 2000102436864352, 1999952199236066,
    2000024643553584, 2000182297526403, 2000042523684364, 1999871952131273, 1999926358638103,
    2000012824038587, 2000019261110181, 2000008042722776, 1999960267355340, 1999886763249469,
    1999899467837449, 2000008335747586, 2000063719760625, 1999999182726899, 1999902682093634,
    1999924259007070, 1999970600050490, 1999981517421588, 1999862711837604, 1999896116296584,
    1999937143167321, 2000055846339697, 1999963268360585, 1999945404270426, 1999961864341935,
    2000003749652351, 2000040133640064, 1999970718840240, 2000015379445710, 2000028868155405,
    1999981825919482, 1999965563836806, 1999926364988249, 1999991654276461, 2000059095553565,
    2000008723529207, 1999995496232080, 1999990773997137, 1999981101498865, 2000038805664483,
    2000055540068513, 2000047692452640, 2000086880412925, 2000048168563684]
private def pvn_m32_r256_3_2_p1 : List ℕ :=
  [1999952053231676, 1999935248701050, 1999961247348476, 2000014589721347, 2000102253556563,
    2000092898935299, 1999983450818066, 1999942639898893, 1999985061870260, 2000033328663919,
    2000096139375953, 2000126735194781, 2000054914787915, 1999978316993850, 2000000196760708,
    2000048959579230, 2000059213815794, 2000064276880174, 2000044657506851, 1999961543050706,
    1999898157206978, 1999940157492313, 2000029040190338, 2000090194932481, 2000146033110972,
    2000200404717872, 2000187331364654, 2000104321509394, 2000037233996874, 2000015515721044,
    1999983751207418, 1999929769222863, 1999908100201167, 1999924874656908, 1999917457847904,
    1999866523500005, 1999831426329614, 1999853202219420, 1999904085049275, 1999958874426899,
    2000040060267570, 2000139329277298, 2000133558040970, 1999833525138860, 1999124790374103,
    1998078134670735, 1997014295556385, 1996594188159358, 1997926508930308, 2002565808494547,
    2012295911129775, 2028736528070450, 2052913513927579, 2084915345297200, 2123690371454697,
    2167012827347036, 2211656578543022, 2253796974318654, 2289586414313074, 2315767241370254,
    2330162431751467, 2331935819360201, 2321598722145958, 2300807662703079]
private def pvn_m32_r256_3_2_p2 : List ℕ :=
  [2272026875716831, 2238129891789000, 2202005699904768, 2166225223692504, 2132810138830581,
    2103124531754524, 2077883453902700, 2057249548647682, 2040977302602271, 2028566077439441,
    2019394053125542, 2012819193941496, 2008245090379095, 2005156668287811, 2003133514658467,
    2001848453688183, 2001057592757458, 2000586386445472, 2000314800091352, 2000163495495476,
    2000082078139662, 2000039793618914, 2000018614062428, 2000008391277626, 2000003640823407,
    2000001517911836, 2000000606828465, 2000000231993311, 2000000084505230, 2000000029179829,
    2000000009482020, 2000000002867960, 2000000000793434, 2000000000194811, 2000000000040034,
    2000000000006003, 2000000000000432, 2000000000000085, 2000000000000201, 2000000000000189,
    2000000000000122, 2000000000000062, 2000000000000024, 2000000000000007, 2000000000000001]
private def pvn_m32_r256_3_2 : List ℕ :=
  pCat pvn_m32_r256_3_2_p0
    (pCat pvn_m32_r256_3_2_p1
      pvn_m32_r256_3_2_p2)
private def pvn_m32_r256_3_3_p0 : List ℕ :=
  [2000198882005057, 1999934690241548, 2000093004862757, 1999902960151488, 1999946408854830,
    2000049759455854, 1999996302962425, 2000012888406862, 2000056090398876, 2000050546967978,
    2000108155594158, 2000135972830020, 2000021686294638, 1999961964384953, 2000053260469200,
    2000078630107736, 1999964274809084, 1999942104735088, 2000026765871072, 2000059877022801,
    1999939434114652, 1999952263931061, 1999993929416737, 2000078807771897, 1999950540297408,
    1999934542240639, 1999964092296284, 2000060747076617, 2000124689851957, 2000055293669357,
    2000043864978032, 1999995111824745, 1999986855126655, 2000052361832224, 2000077235684709,
    2000139352524146, 2000117648815736, 1999984476425741, 1999933815688244, 1999951521487379,
    2000029824749165, 2000108051563010, 2000022159747839, 1999912620684407, 1999929738641488,
    1999967903859849, 1999990844199995, 1999982029715880, 1999922121038546, 1999942361893676,
    2000032464661693, 2000027724803639, 1999972077608994, 1999958113959891, 1999939532455352,
    1999928853936556, 1999943562825476, 1999921747068182, 1999910970180173, 1999971126264467,
    1999995101332888, 1999942691535858, 1999925677444834, 1999957533299071]
private def pvn_m32_r256_3_3_p1 : List ℕ :=
  [1999979825025345, 2000013840211722, 2000044859109704, 2000013337043710, 1999972939506943,
    1999985842072600, 1999987614677928, 1999955760941594, 1999972990331314, 2000030605153247,
    2000034865178521, 1999991449406933, 1999960963780977, 1999943135422397, 1999953550830158,
    2000037830439633, 2000133499517314, 2000119468440935, 2000016562024682, 1999949969847919,
    1999955894541478, 1999989250006161, 2000036129234572, 2000078703056400, 2000056061923713,
    1999972339464123, 1999931327033578, 1999983130078254, 2000051493206288, 2000067182125736,
    2000054183394214, 2000043132402172, 2000018935491216, 1999993586485821, 2000020288195004,
    2000093552882994, 2000129038664727, 2000081609314442, 2000004358528676, 1999957822407091,
    1999936562657476, 1999923997373065, 1999948887350406, 2000032208606592, 2000126221971228,
    2000164840180851, 2000148424271762, 2000127324495145, 2000117908713224, 2000088178717787,
    2000026775722101, 1999975583793582, 1999972107435206, 1999991818350783, 1999976303695523,
    1999903166782710, 1999803165687675, 1999720525922992, 1999692108082443, 1999772690991035,
    2000038859490640, 2000508270031765, 2001017127350075, 2001175575607152]
private def pvn_m32_r256_3_3_p2 : List ℕ :=
  [2000481548783322, 1998569512847035, 1995503399326250, 1992022481835338, 1989667253980901,
    1990713306250291, 1997851273618001, 2013615580026001, 2039677700873917, 2076214356295282,
    2121568994795640, 2172334749309987, 2223848301677196, 2270963829962571, 2308915124474800,
    2334074943504139, 2344465192630111, 2339939141803189, 2322032235529322, 2293547430057217,
    2257989914540375, 2218982877576130, 2179778182373574, 2142932606998199, 2110168527205003,
    2082394281564858, 2059834052486139, 2042211324767862, 2028938740691339, 2019282898364230,
    2012488785118711, 2007861206489020, 2004808503115573, 2002857515074836, 2001649363941181,
    2000924438028704, 2000502984157994, 2000265600497248, 2000136077641656, 2000067626267859,
    2000032591409235, 2000015227791798, 2000006896038598, 2000003025986705, 2000001286186430,
    2000000529372618, 2000000210898646, 2000000081293495, 2000000030304163, 2000000010919177,
    2000000003800876, 2000000001277475, 2000000000414375, 2000000000129683, 2000000000039159,
    2000000000011416, 2000000000003214, 2000000000000874, 2000000000000227, 2000000000000055,
    2000000000000011, 2000000000000001]
private def pvn_m32_r256_3_3 : List ℕ :=
  pCat pvn_m32_r256_3_3_p0
    (pCat pvn_m32_r256_3_3_p1
      pvn_m32_r256_3_3_p2)
private def phb_m32_r256_4_p0 : List ℕ :=
  [107460427898493, 151505509245375, 184984138327370, 212941268891645, 237337483670602,
    259181455811264, 279074229858731, 297408610314974, 314458261651952, 330423032484561,
    345454239871014, 359669788551762, 373163716594096, 386012491677678, 398279316527408,
    410017163347230, 421270968212287, 432079253564858, 442475351265186, 452488340332402,
    462143776837611, 471464269702517, 480469940449931, 489178794316790, 497607022796032,
    505769252511527, 513678751643126, 521347602446435, 528786846448627, 536006607441509,
    543016196294603, 549824200776025, 556438562927805, 562866646045720, 569115292925595,
    575190876732449, 581099345606352, 586846261925085, 592436836987868, 597875961758258,
    603168234201670, 608317983668893, 613329292707792, 618206016628210, 622951801097503,
    627570098004479, 632064179796249, 636437152464470, 640691967333823, 644831431785477,
    648858219031212, 652774877039263, 656583836700475, 660287419312550, 663887843450955,
    667387231286989, 670787614406591, 674090939177406, 677299071706353, 680413802425344,
    683436850338758, 686369866962723, 689214439983164, 691972096656797]
private def phb_m32_r256_4_p1 : List ℕ :=
  [694644306976827, 697232486622966, 699737999713455, 702162161375094, 704506240145760,
    706771460222539, 708959003567412, 711070011881325, 713105588456527, 715066799916178,
    716954677849450, 718770220349636, 720514393462150, 722188132548718, 723792343573548,
    725327904316786, 726795665520153, 728196451969240, 729531063516630, 730800276049639,
    732004842406221, 733145493242297, 734222937853504, 735237864954176, 736190943416125,
    737082822969628, 737914134868842, 738685492523706, 739397492100258, 740050713091147,
    740645718857997, 741183057147183, 741663260580440, 742086847121666, 742454320521162,
    742766170738480, 743022874344974, 743224894907072, 743372683351215, 743466678311369,
    743507306459925, 743494982822777, 743430111079303, 743313083847932, 743144282957931,
    742924079708004, 742652835112279, 742330900134179, 741958615908682, 741536313953421,
    741064316369044, 740542936029235, 739972476760774, 739353233513953, 738685492523706,
    737969531461722, 737205619579819, 736394017844853, 735534979065369, 734628748010237,
    733675561519444, 732675648607240, 731629230557798, 730536521013519]
private def phb_m32_r256_4_p2 : List ℕ :=
  [729397726056135, 728213044280704, 726982666862605, 725706777617615, 724385553055142,
    723019162424653, 721607767755359, 720151523889160, 718650578506876, 717105072147755,
    715515138222236, 713880903017944, 712202485698852, 710479998297566, 708713545700642,
    706903225626831, 705049128598170, 703151337903752, 701209929556056, 699224972239664,
    697196527252169, 695124648437087, 693009382108538, 690850766967444, 688648834008980,
    686403606420976, 684115099472954, 681783320395438, 679408268249172, 676989933783820,
    674528299285711, 672023338414147, 669475016025757, 666883287986323, 664248100969494,
    661569392241718, 658847089432701, 656081110290622, 653271362421295, 650417743010398,
    647520138527808, 644578424413018, 641592464740532, 638562111864035, 635487206038050,
    632367575015671, 629203033620878, 625993383293781, 622738411607020, 619437891751414,
    616091581988749, 612699225069465, 609260547612764, 605775259446478, 602243052903767,
    598663602073494, 595036562000797, 591361567834100, 587638233914402, 583866152802359,
    580044894238173, 576174004028882, 572253002857067, 568281385004420]
private def phb_m32_r256_4_p3 : List ℕ :=
  [564258616982946, 560184136065836, 556057348709195, 551877628854916, 547644316103894,
    543356713747636, 539014086644970, 534615658929050, 530160611528171, 525648079481944,
    521077149032211, 516446854465556, 511756174681405, 507004029456445, 502189275372289,
    497310701369039, 492367023882320, 487356881515637, 482278829193139, 477131331730069,
    471912756749017, 466621366859416, 461255311005072, 455812614869713, 450291170212882,
    444688722987609, 439002860066260, 433230994371021, 427370348169349, 421417934251046,
    415370534650433, 409224676512174, 402976604619349, 396622250003606, 390157193934246,
    383576626429067, 376875298235504, 370047464983659, 363086821896500, 355986427033818,
    348738610513724, 341334866453921, 333765723441642, 326020588084961, 318087554486712,
    309953170118880, 301602145263394, 293016988469186, 284177543639451, 275060394258576,
    265638085002405, 255878087340702, 245741398123834, 235180598361994, 224137094193002,
    212537075175104, 200285376320938, 187255739712776, 173274501055591, 158091296661375,
    141321379406696, 122316308961939, 99810338603062, 70532327122868]
private def phb_m32_r256_4 : List ℕ :=
  pCat phb_m32_r256_4_p0
    (pCat phb_m32_r256_4_p1
    (pCat phb_m32_r256_4_p2
      phb_m32_r256_4_p3))
private def pvn_m32_r256_4_0_p0 : List ℕ :=
  [1999801117994943, 2000065309758452, 1999906995137243, 2000097039848512, 2000053591145170,
    1999950240544146, 2000003697037575, 1999987111593138, 1999943909601124, 1999949453032022,
    2000108155594158, 2000135972830020, 1999978313705362, 2000038035615047, 1999946739530800,
    2000078630107736, 1999964274809084, 2000057895264912, 1999973234128928, 2000059877022801,
    1999939434114652, 2000047736068939, 2000006070583263, 2000078807771897, 2000049459702592,
    1999934542240639, 2000035907703716, 2000060747076617, 1999875310148043, 1999944706330643,
    1999956135021968, 2000004888175255, 1999986855126655, 1999947638167776, 1999922764315291,
    2000139352524146, 1999882351184264, 1999984476425741, 1999933815688244, 1999951521487379,
    1999970175250835, 1999891948436990, 1999977840252161, 1999912620684407, 1999929738641488,
    2000032096140151, 2000009155800005, 2000017970284120, 1999922121038546, 1999942361893676,
    1999967535338307, 2000027724803639, 2000027922391006, 1999958113959891, 1999939532455352,
    1999928853936556, 2000056437174524, 2000078252931818, 2000089029819827, 1999971126264467,
    1999995101332888, 2000057308464142, 2000074322555166, 1999957533299071]
private def pvn_m32_r256_4_0_p1 : List ℕ :=
  [2000020174974655, 1999986159788278, 1999955140890296, 1999986662956290, 2000027060493057,
    2000014157927400, 2000012385322072, 2000044239058406, 2000027009668686, 1999969394846753,
    2000034865178521, 2000008550593067, 1999960963780977, 2000056864577603, 2000046449169842,
    1999962169560367, 1999866500482686, 1999880531559065, 2000016562024682, 1999949969847919,
    2000044105458522, 1999989250006161, 1999963870765428, 1999921296943600, 1999943938076287,
    2000027660535877, 2000068672966422, 1999983130078254, 2000051493206288, 1999932817874264,
    2000054183394214, 1999956867597828, 1999981064508784, 1999993586485821, 2000020288195004,
    2000093552882994, 2000129038664727, 1999918390685558, 2000004358528676, 1999957822407091,
    1999936562657476, 1999923997373065, 2000051112649594, 1999967791393408, 2000126221971228,
    2000164840180851, 2000148424271762, 2000127324495145, 2000117908713224, 2000088178717787,
    1999973224277899, 1999975583793582, 2000027892564794, 1999991818350783, 2000023696304477,
    2000096833217290, 2000196834312325, 2000279474077008, 1999692108082443, 1999772690991035,
    1999961140509360, 1999491729968235, 1998982872649925, 1998824424392848]
private def pvn_m32_r256_4_0_p2 : List ℕ :=
  [1999518451216678, 1998569512847035, 1995503399326250, 1992022481835338, 1989667253980901,
    1990713306250291, 2002148726381999, 2013615580026001, 2039677700873917, 2076214356295282,
    2121568994795640, 2172334749309987, 2223848301677196, 2270963829962571, 2308915124474800,
    2334074943504139, 2344465192630111, 2339939141803189, 2322032235529322, 2293547430057217,
    2257989914540375, 2218982877576130, 2179778182373574, 2142932606998199, 2110168527205003,
    2082394281564858, 2059834052486139, 2042211324767862, 2028938740691339, 2019282898364230,
    2012488785118711, 2007861206489020, 1995191496884427, 2002857515074836, 2001649363941181,
    2000924438028704, 2000502984157994, 2000265600497248, 2000136077641656, 2000067626267859,
    2000032591409235, 2000015227791798, 2000006896038598, 2000003025986705, 2000001286186430,
    2000000529372618, 2000000210898646, 1999999918706505, 1999999969695837, 2000000010919177,
    2000000003800876, 2000000001277475, 2000000000414375, 1999999999870317, 1999999999960841,
    1999999999988584, 2000000000003214, 2000000000000874, 2000000000000227, 2000000000000055,
    2000000000000011, 2000000000000001]
private def pvn_m32_r256_4_0 : List ℕ :=
  pCat pvn_m32_r256_4_0_p0
    (pCat pvn_m32_r256_4_0_p1
      pvn_m32_r256_4_0_p2)
private def pvn_m32_r256_4_1_p0 : List ℕ :=
  [1999876749524068, 1999836095708046, 1999911716323001, 2000003262854554, 1999911742227236,
    2000030549947294, 1999826946491209, 1999979779708712, 1999964799477047, 2000086476824806,
    1999988312744727, 1999987002661654, 2000015464703158, 2000024065933606, 2000056217920976,
    2000082481876802, 1999898161730972, 1999966125375283, 1999922909340886, 1999979711309215,
    1999952844256988, 2000157327196427, 1999967453315732, 2000008752178774, 2000134536557785,
    1999984164923193, 2000025020983540, 1999995751363997, 1999954481919557, 2000096006321877,
    2000041209076268, 2000009708140136, 1999948499587746, 1999975419591636, 2000077697745206,
    2000019745517329, 1999978821239114, 1999947784664919, 2000074630762344, 2000054310542538,
    2000055272949722, 2000002259025993, 2000026078077074, 1999994255670490, 2000006432963370,
    1999963859791564, 1999984107945819, 1999955072480114, 1999937459953152, 1999971662308445,
    1999976312028461, 1999998172384414, 2000026382568285, 1999952142709420, 1999947904014778,
    1999996774912533, 1999989740592034, 1999987746252693, 1999977180880749, 1999944401284870,
    1999884479905663, 1999820556146336, 2000051089407141, 2000016526201565]
private def pvn_m32_r256_4_1_p1 : List ℕ :=
  [1999987598272302, 1999927200738597, 1999934180081671, 1999953590887391, 2000011516192490,
    2000013295393422, 2000053901535096, 1999871641979954, 2000004211735043, 1999943674952162,
    1999975937145194, 1999970609595675, 2000016788417685, 2000024449416191, 1999999366117654,
    1999954986662099, 2000129074275953, 2000011590773066, 2000052223671203, 1999994810960644,
    2000040930487423, 2000026341947950, 2000003015913786, 1999912190969779, 2000000225880334,
    2000020416085448, 1999983858924260, 2000095064975181, 2000016645525157, 1999941879428832,
    1999993358352068, 2000000012838894, 2000004081325315, 2000134374003646, 2000056593808407,
    2000013346553725, 1999850855030167, 1999998211036223, 1999993056800050, 1999888523092266,
    2000119184653156, 1999805433398962, 2000107663518886, 1999851233690072, 2000118964242191,
    1999647644805479, 2000449600649990, 1999239072596010, 2001060707863034, 1998970188095967,
    2000870076425644, 1999489511851713, 1999917681828411, 2000599636150494, 1999031244793400,
    2000620999470168, 2000360799113888, 1999156423004876, 2000595103161228, 2000347857464606,
    1999374898059437, 2000185892348625, 2000104669889696, 1999555878598467]
private def pvn_m32_r256_4_1_p2 : List ℕ :=
  [2000261268109854, 2000251622896654, 1999403055245181, 2000097660209672, 2000965024552174,
    2000292636283275, 1998838612858875, 2000393095359449, 2000345662003812, 2001618591803778,
    1997347856245334, 2001134686710757, 1998130012259906, 2003584252682370, 1999511328845623,
    1999728029631792, 2000013992712442, 1996999640973020, 2000963479321552, 2000385452426666,
    1999973089036305, 2003845861846274, 2001487929615042, 1997806941382260, 1995295711769062,
    1986643291287371, 1978200488811643, 1978396959044786, 1984881162172701, 2000382585000482,
    2032692149831401, 2079330897202494, 2132122374338344, 2188453502241917, 2246132643651876,
    2296565697480737, 2331060347663727, 2348087959323926, 2350277100918600, 2338650002055911,
    2313133617219868, 2276403158919459, 2234342504600801, 2192802775494312, 2154917251086781,
    2121278230083614, 2091673250746268, 2066261800442145, 2045543839079196, 2029781871751723,
    2018645556892167, 2011296843599018, 2006707610509587, 2003946085485205, 2002313837503098,
    2001351664863286, 2000782397525651, 2000445470264121, 2000247819570666, 2000134050926469,
    2000070292094515, 2000035666911964, 2000017490879499, 2000008280424422]
private def pvn_m32_r256_4_1_p3 : List ℕ :=
  [2000003779729232, 2000001661495319, 2000000702599240, 2000000285628159, 2000000111620900,
    2000000041956197, 2000000015187504, 2000000005303614, 2000000001790327, 2000000000585389,
    2000000000185722, 2000000000057242, 2000000000017146, 2000000000004990, 2000000000001407,
    2000000000000384, 2000000000000099, 2000000000000022, 2000000000000003]
private def pvn_m32_r256_4_1 : List ℕ :=
  pCat pvn_m32_r256_4_1_p0
    (pCat pvn_m32_r256_4_1_p1
    (pCat pvn_m32_r256_4_1_p2
      pvn_m32_r256_4_1_p3))
private def pvn_m32_r256_4_2_p0 : List ℕ :=
  [1999931088529561, 2000115189777695, 1999896448495206, 1999935916311912, 1999911527069861,
    1999911674211697, 1999884292632671, 1999955413050447, 1999847151895102, 2000029705521324,
    1999979742374939, 2000013785654097, 1999920295208429, 1999914381939762, 1999983782667197,
    1999856207560774, 1999933258159612, 2000121469741057, 1999958659247377, 1999951476697105,
    2000042420410464, 1999962082935186, 1999996982696704, 1999988091444786, 2000081214172256,
    2000060151380404, 2000072359201435, 1999986744347083, 1999966372055045, 1999933948322175,
    1999964418042756, 1999973810170352, 1999988440184204, 1999965848830233, 1999952083930053,
    2000036573695727, 2000110540878658, 2000068091339518, 2000009034468163, 1999957800832615,
    1999993580981554, 2000072324559244, 2000065711563889, 1999976499694968, 2000036941347938,
    1999959649050928, 2000052279286488, 2000013144764831, 2000031541321053, 1999994854260617,
    1999980836727742, 1999977445037466, 2000053473034090, 1999923486629684, 2000088209777306,
    2000033667169530, 2000041727866566, 1999989988885031, 2000033312344835, 2000060836798318,
    2000033778087116, 1999938216847700, 2000078271300227, 1999929006321412]
private def pvn_m32_r256_4_2_p1 : List ℕ :=
  [1999948453732673, 1999921814365004, 2000004755173975, 2000033545848082, 1999983631775864,
    1999944364068070, 1999948135307874, 1999944180557147, 1999986888329888, 2000122972508909,
    2000008147575773, 1999925936926007, 1999912476323523, 1999923797163967, 1999937073357886,
    2000012635457872, 1999901844363084, 2000002399427763, 1999991546152962, 1999810364397966,
    2000059353070499, 1999853672063991, 2000232852596608, 1999695871800924, 2000307426341808,
    1999589056613388, 2000443498234852, 1999363731226056, 2000758055197421, 1999063697579137,
    2000765380667739, 1999484225561301, 2000110868328196, 2000290750266915, 1999393100583349,
    2000719642469009, 1999539659811460, 2000110912991477, 2000478070392564, 1999426887899510,
    2000473779753850, 1999869427544368, 1999540196611718, 2000657551636584, 1999713295215444,
    1999847745472959, 2000528618741521, 1999581364169187, 1999655229410443, 2000893180037519,
    1999261910059382, 2000355359630839, 1999777203155337, 2001015924326860, 1998189785984186,
    2002092721349735, 1998111048697708, 2001465948323070, 1998704645600065, 2000981256706755,
    1999670258672694, 1999284807851705, 2001540354602111, 1998113053558029]
private def pvn_m32_r256_4_2_p2 : List ℕ :=
  [2000827562586956, 2000429031443330, 1999038093396436, 2000846523973462, 1999097894935723,
    2000737656810829, 2000726474803390, 1997900734607301, 2000849954388524, 2001209245070217,
    1998733041125696, 2000209389401200, 2000074203195663, 1999698913245921, 2001493824015522,
    1999554256717550, 1998032588611664, 2001055044218336, 2001255360033326, 1998921618401297,
    1999745650026430, 2000316147727575, 1999245077564724, 2000671466291632, 2001885502827441,
    1999490185212836, 1998275708259262, 2000247246782519, 2000652508909979, 1999362469821403,
    2000378239161712, 2002081615825398, 2000764187478225, 1998509390009629, 1998480507185978,
    1998937835956573, 1998235830113496, 1999227769839197, 2003767201552282, 2008053538809725,
    2007260275896497, 2001002895721632, 1991559438489139, 1980182371824852, 1968525101084506,
    1961999692073026, 1968472789571264, 1993116006870775, 2035487926388083, 2091171815968429,
    2154624161325586, 2219928676374932, 2280113828506756, 2327561251728361, 2356170260569694,
    2363559128903829, 2351496542422991, 2324475596593781, 2287722447414652, 2245870709925313,
    2202599016009706, 2160791536728537, 2122700645279900, 2089919166390948]
private def pvn_m32_r256_4_2_p3 : List ℕ :=
  [2063270413242618, 2042791328431155, 2027879747866623, 2017553620086302, 2010719813109079,
    2006373514038723, 2003701589768318, 2002105193554471, 2001174029033465, 2000642137956081,
    2000344179409766, 2000180506029075, 2000092456868657, 2000046162541699, 2000022426533024,
    2000010584637248, 2000004846919214, 2000002151184162, 2000000924606981, 2000000384623717,
    2000000154781333, 2000000060238016, 2000000022667856, 2000000008247083, 2000000002900945,
    2000000000986633, 2000000000324485, 2000000000103206, 2000000000031747, 2000000000009443,
    2000000000002712, 2000000000000750, 2000000000000197, 2000000000000047, 2000000000000009,
    2000000000000001]
private def pvn_m32_r256_4_2 : List ℕ :=
  pCat pvn_m32_r256_4_2_p0
    (pCat pvn_m32_r256_4_2_p1
    (pCat pvn_m32_r256_4_2_p2
      pvn_m32_r256_4_2_p3))
private def pvn_m32_r256_4_3_p0 : List ℕ :=
  [1999862471949571, 1999952887591667, 1999930250534910, 2000108144178384, 1999995137649900,
    1999999374118211, 2000039034603432, 1999968485801297, 1999954046792174, 1999979704318426,
    1999896734875064, 1999927700899913, 2000054969191794, 1999847546438783, 1999847825305008,
    1999931751673759, 1999993748592798, 1999911079440444, 1999933027330432, 2000004231544289,
    2000038528664789, 1999995564613447, 1999934370436399, 1999917222062217, 1999929049827971,
    1999927247158704, 1999960274856481, 1999948365860577, 1999985140575536, 1999991645406022,
    2000047954683673, 1999937922197149, 2000018257197551, 1999943618946626, 1999965022309551,
    1999986382206601, 2000055207275576, 2000036359047421, 2000146302571900, 1999977601774335,
    2000018760822453, 1999953727439675, 2000012096541099, 2000043073263811, 1999987262384768,
    1999863853506828, 1999972368331642, 1999902218699908, 2000043216021754, 2000039504855951,
    2000049869580652, 2000037726153536, 1999956348887164, 2000019242228689, 2000066462353501,
    2000031358975328, 1999979876819909, 2000061026761125, 2000017646321194, 2000010944232621,
    1999978128032192, 2000025103127629, 2000067872087713, 2000028975323177]
private def pvn_m32_r256_4_3_p1 : List ℕ :=
  [1999984064864073, 1999945142462717, 2000162903849009, 1999736700373555, 2000281165170494,
    1999677470782157, 2000416476166098, 1999558762118488, 2000568271237770, 1999370414845989,
    2000712176858717, 1999354082199878, 2000658926985303, 1999687511433515, 2000112340558602,
    2000168639555709, 1999358609514863, 2000708261278535, 1999518638868819, 2000141349502590,
    2000223262781268, 1999419922345727, 2000465522508316, 1999647555842742, 1999909577521172,
    2000493728962217, 1999462096718739, 2000397689168218, 1999923719487003, 1999668496874737,
    2000133315039544, 2000304690006966, 1999037388656887, 2001299688877609, 1998526503267169,
    2001138285739522, 1998876195078317, 2001247924582315, 1998208709178264, 2001895509569834,
    1998607114528967, 2000237885328861, 2000772331344872, 1998802567063955, 2001007640992841,
    1999125622418979, 2000720552756516, 1999433672553864, 1999803577695082, 2001183873458400,
    1998363567734006, 2000811795423242, 2000310653133737, 1998933741753020, 2001282700327373,
    1999466483202557, 1999776591878117, 2000761508118676, 1999124029671273, 2000553504264685,
    2000112238145094, 1999253278763373, 2001126101826840, 1999493099804524]
private def pvn_m32_r256_4_3_p2 : List ℕ :=
  [1999133923517941, 2001463278412079, 1999506754606524, 1998908896566495, 2001288372390204,
    2000093187628407, 1999251403070293, 2000499846375373, 1999783784105016, 1999959268530673,
    2000796589439968, 1999089987206209, 1999377853351947, 2001613550293452, 1999964362109870,
    1998226185915161, 2000470794103935, 2001158310287530, 1999277857069846, 1999547758230734,
    2000427751078399, 1999716122376454, 2000119954799017, 2000862813533781, 1999301554662764,
    1998653652100740, 2000887470796199, 2001456507068988, 1999206395356976, 1998825559244308,
    2000669519107990, 2000767199660080, 1999563972320675, 1999931685397392, 2000523764307065,
    1999385928723769, 1998788587161619, 2000421466676337, 2001559889317053, 2000338460437391,
    1999207676656745, 1999935626793997, 2000417238528358, 1999204086843281, 1998610441321076,
    2000559167361009, 2002896802779182, 2002534848240921, 1999794332830159, 1997256473515800,
    1996130137960053, 1996180012000873, 1998130999064773, 2003354714488358, 2010643620027888,
    2015032307532196, 2011097215841238, 1997370182642860, 1977567895694907, 1958473581437980,
    1947395874229131, 1950965999648936, 1974395943562652, 2019913208537105]
private def pvn_m32_r256_4_3_p3 : List ℕ :=
  [2084870665943423, 2161293399743504, 2237811937412268, 2303087941036237, 2348867851076388,
    2371363542040093, 2370925616393216, 2350816370312353, 2315906574948477, 2271670484291828,
    2223462517192396, 2175956320921021, 2132716850876184, 2095966582873843, 2066600422397879,
    2044426478612826, 2028536196937948, 2017685494520669, 2010598035127496, 2006153490358594,
    2003468359236756, 2001900687224440, 2001013849946455, 2000526739860830, 2000266594622664,
    2000131408771351, 2000063044854748, 2000029414161364, 2000013332548492, 2000005864960918,
    2000002501283734, 2000001033191473, 2000000412976950, 2000000159602952, 2000000059594085,
    2000000021484187, 2000000007473395, 2000000002506955, 2000000000810506, 2000000000252404,
    2000000000075664, 2000000000021816, 2000000000006041, 2000000000001602, 2000000000000404,
    2000000000000093, 2000000000000018, 2000000000000002]
private def pvn_m32_r256_4_3 : List ℕ :=
  pCat pvn_m32_r256_4_3_p0
    (pCat pvn_m32_r256_4_3_p1
    (pCat pvn_m32_r256_4_3_p2
      pvn_m32_r256_4_3_p3))
private def pvn_m32_r256_4_4_p0 : List ℕ :=
  [1999894440482513, 1999969999510367, 1999998670017739, 1999929948675014, 1999888624421658,
    1999883981697379, 2000039665209203, 1999958545499130, 1999961824374460, 2000035974350502,
    2000062421835942, 1999988131844302, 1999964410360047, 2000037161497221, 2000089842777883,
    1999991369013022, 1999938053411174, 1999894138701580, 2000017413512621, 1999987297618071,
    2000027807154752, 1999888915140962, 1999934410550644, 1999923327500292, 1999965114311675,
    1999884898882741, 1999980330188623, 1999844340096320, 1999926701481151, 1999970910816492,
    1999999145526343, 1999976691059711, 2000051448149253, 1999927045836736, 2000010881392154,
    1999964320770517, 1999907298998288, 1999973039098085, 1999903859817657, 1999935021671356,
    1999958609787250, 1999976026187836, 1999957362082252, 2000020090270525, 2000012443532446,
    2000012071698568, 1999995059315825, 1999835228677213, 2000028492791690, 1999870688150832,
    2000267969088817, 1999715356369023, 2000483275876104, 1999519045071148, 2000541413072018,
    1999428976421100, 2000661877907759, 1999482737407159, 2000583161807257, 1999486920761854,
    2000114457214933, 2000078391838221, 1999574571053884, 2000495527190581]
private def pvn_m32_r256_4_4_p1 : List ℕ :=
  [1999436952655654, 2000428535208666, 1999944409036559, 1999694550679754, 2000532076101051,
    1999504668383403, 2000273839416405, 2000240783520539, 1999447134129250, 2000693930885991,
    1999527508313770, 2000209697169020, 1999944873475715, 2000237693387912, 1999407328156527,
    2001205747223931, 1998350764466176, 2001902287896093, 1998354348236160, 2001170262784360,
    1999063415192211, 2000866024829419, 1999284708982360, 2000443125303476, 2000235254208077,
    1998818335219832, 2001668550624989, 1998609159831492, 2000704598151463, 2000418460527095,
    1999091008850807, 2000958969777200, 1999286617913582, 2000409707530376, 1999805083722504,
    1999870001893853, 2000852014026459, 1998716077106375, 2000730164828416, 2000236501217423,
    1998694656880383, 2001298032311207, 1999649554169389, 1999319372834668, 2001049423729734,
    1999291165061349, 2000028090576395, 2000434455845087, 1999287472411197, 2000596183470540,
    1999810405205868, 1999379043598411, 2000893334262615, 1999421963672105, 1999544627916107,
    2000962607211220, 1999146795849700, 1999729598597064, 2001192789867472, 1999111976677161,
    1999521406488392, 2001124807046229, 1999404333115803, 1999478025564038]
private def pvn_m32_r256_4_4_p2 : List ℕ :=
  [2000873645702898, 1999695598125266, 1999583099448441, 2000378707792661, 1999564981281554,
    2000068465835809, 2000700845022148, 1999198699286658, 1999737713119866, 2001356306983890,
    1999576209046533, 1998695057885655, 2001058754856483, 2000892086807538, 1998811596014156,
    1999760285314675, 2000964066535855, 1999792756678075, 1999531470159442, 2000273415347751,
    1999822101278552, 1999941692037904, 2000805017357288, 1999795139656242, 1998859540539758,
    2000556221140587, 2001326601287006, 1999257530511846, 1998742381758937, 2000829515868835,
    2001068949476978, 1999227812077557, 1999167987106869, 2000448610716964, 2000245658531221,
    1999633568169142, 2000268012935275, 2000386095041777, 1999272176754826, 1999366878946227,
    2000877140815573, 2000844201569399, 1999129616738567, 1998911623212487, 2000561710933739,
    2001072304743240, 1999832058058060, 1999410906414876, 2000392112452124, 2000462451266925,
    1999101994383972, 1998746739392486, 2000409242366084, 2001808770115847, 2001067323148964,
    1999384814167412, 1998676560601737, 1998868975263806, 1999154170575261, 2000115346028920,
    2002479190339616, 2004553021376683, 2003127830568860, 1997483920646900]
private def pvn_m32_r256_4_4_p3 : List ℕ :=
  [1991336200280608, 1990033267003082, 1996057007834766, 2007195551320152, 2018096980825765,
    2022826136498886, 2016756582546704, 1998210885607676, 1970329947777666, 1941990538426164,
    1925993784436762, 1934457986994185, 1973676075164446, 2041302357233371, 2127176115133071,
    2216897521976282, 2296126288762501, 2353890084535956, 2384225605830252, 2386326724127163,
    2363690213120631, 2322707816020144, 2271049782508777, 2216142098337605, 2164007679953488,
    2118646653144506, 2081974233237517, 2054183486050324, 2034320124581041, 2020865713637309,
    2012195613796829, 2006862761057536, 2003722987405026, 2001949246225349, 2000985830565169,
    2000481897728532, 2000227746622766, 2000104061877323, 2000045956826438, 2000019606214573,
    2000008074142656, 2000003206680545, 2000001226899756, 2000000451696340, 2000000159815639,
    2000000054267956, 2000000017660381, 2000000005499582, 2000000001636150, 2000000000464200,
    2000000000125343, 2000000000032134, 2000000000007796, 2000000000001780, 2000000000000377,
    2000000000000071, 2000000000000010, 2000000000000001]
private def pvn_m32_r256_4_4 : List ℕ :=
  pCat pvn_m32_r256_4_4_p0
    (pCat pvn_m32_r256_4_4_p1
    (pCat pvn_m32_r256_4_4_p2
      pvn_m32_r256_4_4_p3))
private def phb_m32_r256_5_p0 : List ℕ :=
  [107611347761521, 151718287019952, 185243934248201, 213240328440938, 237670805817437,
    259545456128175, 279466168038846, 297826297714976, 314899893969118, 330887086088097,
    345939403643236, 360174916963077, 373687796184107, 386554616378932, 398838669035794,
    410593000754000, 421862610717938, 432686075471679, 443096773687487, 453123825223727,
    462792822043028, 472126404819579, 481144723335313, 489865808114131, 498305873388671,
    506479566324765, 514400173736397, 522079794847767, 529529486693020, 536759387282043,
    543778820560758, 550596386358135, 557220037870189, 563657148733877, 569914571355201,
    575998687849797, 581915454711439, 587670442129838, 593268868723079, 598715632323701,
    604015337354605, 609172319246818, 614190666281829, 619074239183965, 623826688740640,
    628451471688574, 632951865070775, 637330979241026, 641591769668916, 645737047678364,
    649769490235466, 653691648886886, 657505957937465, 661214741944988, 664820222600741,
    668324525056446, 671729683751250, 675037647786319, 678250285889377, 681369391006858,
    684396684557349, 687333820376405, 690182388379735, 692943917968966]
private def phb_m32_r256_5_p1 : List ℕ :=
  [695619881201798, 698211695746153, 700720727636072, 703148293845349, 705495664693423,
    707764066096672, 709954681677050, 712068654738934, 714107090124062, 716071055953584,
    717961585265457, 719779677554722, 721526300223527, 723202389947243, 724808853962432,
    726346571282018, 727816393842520, 729219147587878, 730555633494005, 731826628537891,
    733032886614794, 734175139406783, 735254097205648, 736270449692967, 737224866679931,
    738117998809314, 738950478221821, 739722919188876, 740435918713787, 741090057103056,
    741685898509505, 742223991448775, 742704869290629, 743129050726404, 743497040213879,
    743809328400718, 744066392527581, 744268696811940, 744416692813527, 744510819782336,
    744551504989985, 744539164045241, 744474201194419, 744357009607350, 744187971649548,
    743967459141181, 743695833603392, 743373446492504, 743000639422595, 742577744376887,
    742105083908393, 741582971330206, 741011710895805, 740391597969719, 739722919188876,
    739005952614932, 738240967877851, 737428226310994, 736567981077959, 735660477291372,
    734705952123845, 733704634911261, 732656747248568, 731562503078214]
private def phb_m32_r256_5_p2 : List ℕ :=
  [730422108771355, 729235763201960, 728003657813900, 726725976681107, 725402896560881,
    724034586940390, 722621210076401, 721162921028276, 719659867684244, 718112190780927,
    716520023916131, 714883493554839, 713202719028384, 711477812526712, 709708879083682,
    707896016555287, 706039315590693, 704138859595966, 702194724690340, 700206979654857,
    698175685873200, 696100897264503, 693982660207930, 691821013458757, 689615988055688,
    687367607219119, 685075886240017, 682740832359061, 680362444635675, 677940713806532,
    675475622133083, 672967143237639, 670415241927469, 667819874006375, 665180986073112,
    662498515306024, 659772389233178, 657002525487236, 654188831544253, 651331204445512,
    648429530501445, 645483684976610, 642493531754614, 639458922981784, 636379698688292,
    633255686385326, 630086700636801, 626872542603963, 623612999561116, 620307844380542,
    616956834984524, 613559713762216, 610116206948878, 606626023964816, 603088856711097,
    599504378818866, 595872244848800, 592192089436916, 588463526382585, 584686147674246,
    580859522447835, 576983195872511, 573056687957690, 569079492274821]
private def phb_m32_r256_5_p3 : List ℕ :=
  [565051074586669, 560970871376115, 556838288265681, 552652698318008, 548413440206513,
    544119816244228, 539771090257532, 535366485289936, 530905181119409, 526386311570795,
    521808961602632, 517172164145234, 512474896663972, 507716077418439, 502894561384410,
    498009135801144, 493058515301599, 488041336577304, 482956152522913, 477801425797618,
    472575521731463, 467276700493848, 461903108428916, 456452768447619, 450923569348640,
    445313253919375, 439619405643137, 433839433808761, 427970556782597, 422009783159137,
    415953890453320, 409799400932453, 403542554105704, 397179275290169, 390705139549385,
    384115330145900, 377404590454980, 370567168039205, 363596749266970, 356486382448648,
    349228386930593, 341814244884654, 334234471596199, 326478458795699, 318534283865078,
    310388475383285, 302025722159022, 293428508175830, 284576649029225, 275446695316908,
    266011153155841, 256237448331986, 246086522918797, 235510891330166, 224451877413362,
    212835567065571, 200566661647565, 187518725922130, 173517851696166, 158313323665219,
    141519854358267, 122488092761386, 99950514507117, 70631384323333]
private def phb_m32_r256_5 : List ℕ :=
  pCat phb_m32_r256_5_p0
    (pCat phb_m32_r256_5_p1
    (pCat phb_m32_r256_5_p2
      phb_m32_r256_5_p3))
private def pvn_m32_r256_5_0_p0 : List ℕ :=
  [2000105559517487, 1999969999510367, 2000001329982261, 2000070051324986, 1999888624421658,
    1999883981697379, 2000039665209203, 2000041454500870, 1999961824374460, 2000035974350502,
    2000062421835942, 2000011868155698, 1999964410360047, 1999962838502779, 2000089842777883,
    2000008630986978, 1999938053411174, 2000105861298420, 2000017413512621, 2000012702381929,
    2000027807154752, 1999888915140962, 1999934410550644, 1999923327500292, 2000034885688325,
    2000115101117259, 1999980330188623, 2000155659903680, 2000073298518849, 1999970910816492,
    2000000854473657, 2000023308940289, 2000051448149253, 2000072954163264, 2000010881392154,
    2000035679229483, 2000092701001712, 2000026960901915, 1999903859817657, 2000064978328644,
    1999958609787250, 1999976026187836, 1999957362082252, 1999979909729475, 2000012443532446,
    2000012071698568, 1999995059315825, 1999835228677213, 1999971507208310, 1999870688150832,
    1999732030911183, 2000284643630977, 2000483275876104, 2000480954928852, 2000541413072018,
    2000571023578900, 2000661877907759, 1999482737407159, 1999416838192743, 1999486920761854,
    1999885542785067, 2000078391838221, 2000425428946116, 2000495527190581]
private def pvn_m32_r256_5_0_p1 : List ℕ :=
  [1999436952655654, 1999571464791334, 1999944409036559, 1999694550679754, 2000532076101051,
    1999504668383403, 2000273839416405, 1999759216479461, 1999447134129250, 2000693930885991,
    2000472491686230, 2000209697169020, 1999944873475715, 2000237693387912, 2000592671843473,
    1998794252776069, 2001649235533824, 2001902287896093, 2001645651763840, 2001170262784360,
    1999063415192211, 1999133975170581, 1999284708982360, 2000443125303476, 1999764745791923,
    2001181664780168, 1998331449375011, 1998609159831492, 1999295401848537, 2000418460527095,
    2000908991149193, 2000958969777200, 1999286617913582, 2000409707530376, 1999805083722504,
    1999870001893853, 1999147985973541, 1998716077106375, 1999269835171584, 2000236501217423,
    1998694656880383, 1998701967688793, 2000350445830611, 1999319372834668, 1998950576270266,
    1999291165061349, 2000028090576395, 1999565544154913, 1999287472411197, 2000596183470540,
    1999810405205868, 2000620956401589, 2000893334262615, 1999421963672105, 1999544627916107,
    1999037392788780, 1999146795849700, 1999729598597064, 2001192789867472, 1999111976677161,
    1999521406488392, 1998875192953771, 2000595666884197, 1999478025564038]
private def pvn_m32_r256_5_0_p2 : List ℕ :=
  [1999126354297102, 1999695598125266, 1999583099448441, 1999621292207339, 1999564981281554,
    2000068465835809, 1999299154977852, 1999198699286658, 1999737713119866, 2001356306983890,
    2000423790953467, 2001304942114345, 2001058754856483, 2000892086807538, 2001188403985844,
    2000239714685325, 2000964066535855, 2000207243321925, 2000468529840558, 1999726584652249,
    1999822101278552, 1999941692037904, 2000805017357288, 2000204860343758, 2001140459460242,
    2000556221140587, 2001326601287006, 2000742469488154, 2001257618241063, 2000829515868835,
    2001068949476978, 1999227812077557, 1999167987106869, 1999551389283036, 2000245658531221,
    1999633568169142, 1999731987064725, 2000386095041777, 2000727823245174, 1999366878946227,
    2000877140815573, 1999155798430601, 2000870383261433, 2001088376787513, 2000561710933739,
    2001072304743240, 1999832058058060, 2000589093585124, 1999607887547876, 2000462451266925,
    1999101994383972, 1998746739392486, 1999590757633916, 2001808770115847, 2001067323148964,
    1999384814167412, 1998676560601737, 1998868975263806, 1999154170575261, 1999884653971080,
    1997520809660384, 1995446978623317, 1996872169431140, 1997483920646900]
private def pvn_m32_r256_5_0_p3 : List ℕ :=
  [1991336200280608, 1990033267003082, 1996057007834766, 1992804448679848, 1981903019174235,
    1977173863501114, 1983243417453296, 2001789114392324, 2029670052222334, 2058009461573836,
    2074006215563238, 2065542013005815, 2026323924835554, 2041302357233371, 2127176115133071,
    2216897521976282, 2296126288762501, 2353890084535956, 2384225605830252, 2386326724127163,
    2363690213120631, 2322707816020144, 2271049782508777, 2216142098337605, 2164007679953488,
    2118646653144506, 2081974233237517, 2054183486050324, 2034320124581041, 2020865713637309,
    2012195613796829, 2006862761057536, 2003722987405026, 2001949246225349, 2000985830565169,
    2000481897728532, 2000227746622766, 2000104061877323, 2000045956826438, 2000019606214573,
    2000008074142656, 1999996793319455, 1999998773100244, 1999999548303660, 1999999840184361,
    1999999945732044, 1999999982339619, 1999999994500418, 1999999998363850, 2000000000464200,
    2000000000125343, 2000000000032134, 2000000000007796, 2000000000001780, 2000000000000377,
    2000000000000071, 2000000000000010, 2000000000000001]
private def pvn_m32_r256_5_0 : List ℕ :=
  pCat pvn_m32_r256_5_0_p0
    (pCat pvn_m32_r256_5_0_p1
    (pCat pvn_m32_r256_5_0_p2
      pvn_m32_r256_5_0_p3))
private def pvn_m32_r256_5_1_p0 : List ℕ :=
  [2000015840031179, 2000091598412347, 2000094178672202, 2000028814585789, 1999944781018144,
    1999962268703881, 2000089473577727, 2000091761743703, 1999991894184275, 1999991642065220,
    1999900953614289, 1999913110047128, 2000078488003884, 1999960932403935, 1999875300656490,
    2000043627749603, 1999989266883836, 2000073797033487, 2000033209737238, 1999955051945132,
    2000036717199234, 2000035085204293, 1999943780226550, 2000037577464673, 2000032725580549,
    2000000887491009, 1999905846720222, 2000070737479910, 2000040231801956, 2000056653376036,
    2000093377667607, 1999951637302158, 1999992813848064, 1999984583141095, 1999936012845654,
    1999892158222730, 1999894706560681, 2000112729247456, 2000057835734939, 1999945259199406,
    2000254440451868, 1999820179570388, 2000206172902200, 1999979640441149, 2000001658375723,
    2000009544612558, 1999965819379163, 2000225290332261, 1999955839994218, 1999893251731618,
    2000296228549653, 1999853813749642, 2000338143134399, 1999451910359005, 2000379986258104,
    2000280541048642, 1999362763814157, 2000182225218484, 2000027323967841, 1999964966295898,
    2000407918842855, 1999326847898075, 2000636931171488, 1999537994449972]
private def pvn_m32_r256_5_1_p1 : List ℕ :=
  [1999950684128865, 1999897301745726, 1999405922336642, 2000546206066240, 1999091332938656,
    2001196610997645, 2001002240189853, 2000854200608222, 1999632356609862, 2000968794526141,
    1999045213974341, 1999273799840188, 2000260565924281, 2000438114998760, 1999881411263430,
    2000361497337195, 1999060108581810, 2000446174735149, 2000130516594980, 1999370382216288,
    2000008731923816, 2000391506459383, 1999878641241067, 1999601999780998, 1999415299044328,
    1999540759758434, 2000979071703097, 2000478047630190, 2000545546516755, 2000307884260385,
    1998482708282617, 1999298696067865, 2000159059516405, 2001441945333325, 2002275436672875,
    2001582820135599, 2000342389461372, 1998517800609873, 2001101284977308, 2001143889519311,
    2000151911106669, 1999235210218060, 2000711542940879, 1998640866069998, 1999386262173079,
    1999212904948813, 1999474953056532, 2000452922162769, 2000105518664021, 2000389898624576,
    2000172406698168, 2000618708583450, 1999755120880221, 1999540148791896, 1999397407101192,
    1999882227401541, 1998778825938599, 1999604460991755, 1999498301189502, 1999044741090001,
    1999148010776816, 1999305757032498, 2000654742137262, 1998360147736582]
private def pvn_m32_r256_5_1_p2 : List ℕ :=
  [1998568278721818, 1999397751534814, 2000449813752760, 2000350232131639, 2000737539621789,
    1999883406966271, 1999913979723523, 1999110932202216, 2000397313815089, 1999545727075516,
    1999728043429656, 1999271329387805, 2000041078303395, 1999835840055582, 2000027942664581,
    1999018311593655, 1999493504236913, 1999559060645221, 1999829811205683, 1999698539395497,
    1999849036158192, 1999208992039625, 1999665156501636, 1998467367707554, 2000026042026933,
    1999560982634493, 2000871284793697, 2000297386950856, 2000314551502705, 2002057308635056,
    2000035312880636, 2001461280164327, 2001084400720025, 2000999186800646, 1999655218333381,
    2000047595667776, 2000170745000984, 2000520831787800, 2000041747100859, 1999904630387456,
    2000216849967256, 2001224216107422, 2001247683989174, 2001193936546376, 2001231455739887,
    2001252108127149, 1999959145780649, 2000115330615844, 1999693968585132, 1999140217579155,
    1999999956952202, 2000997058631038, 1999818387862356, 1998734479021611, 2000626278092771,
    2000336440632951, 1999784392590472, 2001560817598486, 1998835124359379, 2000439976116574,
    2003546428984412, 2001823444138941, 1994700247305164, 2001908399823386]
private def pvn_m32_r256_5_1_p3 : List ℕ :=
  [2001341172131403, 1998046485308282, 2000982106524481, 1997505519810946, 2005963478492164,
    1998994099399737, 1991193148532593, 2006060643539777, 2004622447239709, 1991610501497932,
    1998497645021637, 2001025982377041, 1987184436651933, 1991757967596766, 2014191687115178,
    2008776433184006, 1967903375523509, 1940943924664024, 1964881879098157, 2019338848168230,
    2056369277650160, 2051677633449763, 2020708490936418, 1998432912154334, 2012278056464396,
    2068877994236277, 2156055794514592, 2252087770384385, 2335092341215455, 2389294474538107,
    2407700569524148, 2391805647728607, 2349345894973892, 2291095069240389, 2227836292139692,
    2168122715043673, 2117303136483322, 2077572454378105, 2048711436772794, 2029094573378563,
    2016555123814521, 2008982692033659, 2004650135227290, 2002299784051224, 2001088876715835,
    2000493367714735, 2000212345853546, 2000085424526011, 2000031388926707, 2000010235149958,
    2000002841940110, 2000000616653525, 2000000074304743, 1999999985188178, 1999999986276522,
    1999999994360874, 1999999998294516, 1999999999587539, 1999999999919368, 1999999999987633,
    1999999999998657, 1999999999999937, 2000000000000008]
private def pvn_m32_r256_5_1 : List ℕ :=
  pCat pvn_m32_r256_5_1_p0
    (pCat pvn_m32_r256_5_1_p1
    (pCat pvn_m32_r256_5_1_p2
      pvn_m32_r256_5_1_p3))
private def pvn_m32_r256_5_2_p0 : List ℕ :=
  [1999989284483091, 1999984337866460, 1999989487378834, 2000017562173487, 2000003094987895,
    2000032664486436, 2000124345298978, 2000145553287899, 1999949667308167, 2000015408389594,
    2000032552054235, 1999917317863373, 1999937481678048, 2000117371870631, 2000057590554165,
    2000096975047673, 2000010772167323, 1999965464483729, 1999944208189913, 1999960929199291,
    2000086001214859, 1999953963399487, 1999885676044245, 1999991735341989, 1999990331961193,
    1999901715427544, 2000088481050432, 1999848080715188, 2000228947666025, 1999878922012627,
    2000037977410102, 2000103907515198, 1999836142092175, 2000047455765854, 2000180181249447,
    1999825105066867, 2000246013890843, 1999624245681821, 2000293257895547, 1999877178701500,
    1999903907527467, 2000289746322623, 1999776994137008, 2000073836421378, 2000391296062495,
    1999444708645337, 2000748977225689, 1999459366584089, 1999775409718842, 2000574453588741,
    1999299127308363, 2000572601310714, 1999167449146991, 2000819858286339, 1999735359959137,
    2000094759196713, 1999759824363898, 2000482018030277, 1999755054160672, 2000272888614477,
    1999720620082512, 1999956641076966, 2000293960004080, 2000400983614572]
private def pvn_m32_r256_5_2_p1 : List ℕ :=
  [1999074034466546, 2000601161572334, 2000422861367384, 1999196553199455, 2000466305683564,
    2000428235489296, 1999643765157340, 1999799924476832, 2000180198487927, 1999881576380275,
    2000306084335567, 1999796796520116, 1999485989778114, 2000800062104981, 1999801542817497,
    1999892095817572, 2000461104256801, 1999586972339534, 2000091684091722, 1998619274232625,
    1999743813261454, 2000099048764517, 2001434942331138, 2000169557081006, 2000688104834365,
    2000306478966011, 2000503645671063, 1999437572803076, 2000040739334104, 2000326352200486,
    1999207927053042, 2001073022257009, 2000055721460407, 1999159409386744, 1999762807319560,
    2000485685375188, 1999484692773964, 2000432988281845, 2000707491654084, 2000036247752093,
    1998322392591973, 1998519102669383, 2000717157769126, 2001132371017998, 2001787509250378,
    1999183923048233, 1999136022016530, 1999021062895028, 1999755926193543, 2000058992583512,
    2000951580863836, 2001031959953105, 2001132203266194, 1999709373372139, 2001221057225377,
    2000654921213035, 2000702171168346, 2000471530884928, 2001108175315201, 1999746951746399,
    1999350814456465, 1999496957869619, 1999869805183281, 1998696071229807]
private def pvn_m32_r256_5_2_p2 : List ℕ :=
  [1999415607226463, 2000266162735467, 2000713251762906, 1999929918475925, 2000276849817445,
    1999579531555041, 2000855285912762, 1999673488587410, 2000039551128447, 1998926806268569,
    1998721241319034, 1999936590977554, 1999441980783645, 2000716722020521, 1998181304844089,
    1999110014855728, 1998659028951939, 1999294813696978, 1999726876658016, 1999538839332369,
    1999790021443908, 2000753340591555, 1999967614330612, 1999741884228605, 2000030073418525,
    1999741458404146, 1999217212224579, 2000143744148341, 2000175105644356, 1999749901145544,
    1999206575584124, 1999676501185154, 1999437174224496, 1999651794403026, 1999911396694109,
    1999857884441155, 1999927355615517, 1998932712630880, 1998790417870522, 1999686321855979,
    1999761930585343, 1999286542444783, 1999096845037881, 2001417782163621, 1999582499695386,
    2001987574384074, 2000961912997847, 2000721441664918, 2000232194779319, 2002441957485415,
    1999252534832019, 1999479309500995, 2002991726438116, 1995983475308479, 2002926589593794,
    1999930570504744, 1997820484935555, 2005316079378628, 2000305233025037, 2000646985312140,
    2000548955886581, 1998974012889471, 2004600943237749, 1997412508961225]
private def pvn_m32_r256_5_2_p3 : List ℕ :=
  [1995246150557142, 2007128529810878, 2000104863300382, 1992430150962994, 2004748817974958,
    2003383360223287, 1992556956686972, 2001906244381850, 2008131920947023, 1996435849432028,
    1996366080931904, 2006334358390471, 1999861559192928, 1992118999960051, 2004014264131948,
    2010449677744821, 1993418108872535, 1984854566814976, 2006137351759764, 2022834019533407,
    2002231496489404, 1971190255472151, 1976918831215768, 2016122170182548, 2038443026146800,
    2012280952997334, 1962081761806448, 1937659497496101, 1961132904051208, 2009600906852380,
    2041739302482459, 2034837499453187, 2000176543148674, 1971362261250892, 1980798832905984,
    2041616079388263, 2143209136898004, 2258717281206182, 2357759354321568, 2417765725035586,
    2429915289779641, 2398906813766348, 2338352380799190, 2264692519733026, 2192144257386167,
    2129983295121157, 2082194192059771, 2048686284179070, 2027052827621079, 2014114921575638,
    2006918559074434, 2003184965217324, 2001374854410025, 2000554554248433, 2000207782154616,
    2000071712771976, 2000022551140378, 2000006374180793, 2000001592026456, 2000000343466211,
    2000000061906478, 2000000008806999, 2000000000874130, 2000000000037567]
private def pvn_m32_r256_5_2_p4 : List ℕ := [1999999999996669]
private def pvn_m32_r256_5_2 : List ℕ :=
  pCat pvn_m32_r256_5_2_p0
    (pCat pvn_m32_r256_5_2_p1
    (pCat pvn_m32_r256_5_2_p2
    (pCat pvn_m32_r256_5_2_p3
      pvn_m32_r256_5_2_p4)))
private def pvn_m32_r256_5_3_p0 : List ℕ :=
  [1999990078233193, 2000013737495575, 1999977914937949, 2000032940965055, 1999960360562722,
    1999961171045649, 1999986267466137, 2000104291102663, 1999966310313027, 1999878129488276,
    2000013451066140, 2000036808829319, 2000089664248815, 2000025828445917, 2000090315369275,
    1999982089209535, 2000263745578420, 1999863049321736, 2000087221086799, 2000023306519340,
    1999872318444809, 1999932295173610, 2000114847125583, 1999771971145285, 2000490699734610,
    1999804523515138, 2000027225127139, 2000134393147562, 1999870625552706, 2000029570348128,
    2000183685431241, 1999566457917792, 2000537230888876, 1999677822752574, 1999667363162601,
    2000866908653910, 1998842145018811, 2000894243613124, 1999349992217613, 2000203369870628,
    1999961292614604, 2000202704618275, 1999733987462892, 2000220115337913, 1999795802500730,
    2000230673823839, 1999779163655476, 2000137794746245, 2000061499585625, 2000158885946160,
    1999650901583324, 1999964971515313, 2000624665887603, 1999427717961660, 2000009180660581,
    2000259927503758, 1999607597980248, 2000264909954554, 2000407833289003, 1999497626736740,
    1999824367330690, 2001011159891083, 1999680211232059, 1999218919282959]
private def pvn_m32_r256_5_3_p1 : List ℕ :=
  [2000874630234182, 1999372769739223, 2000485538132312, 1999400249824081, 2000187192800263,
    1999966710064995, 2000270541521678, 1999501784730818, 2000402749985314, 2000214991032846,
    1999751522789826, 2000025475768299, 1999731551278941, 2000754882267419, 1999619763025203,
    2000143245033912, 1999717820598645, 2000063476537029, 2000496032033169, 1999858959205780,
    1999430178345893, 2000902767696191, 2000174312029561, 1999002197841900, 2000651184192045,
    1999947981697423, 2000343086711344, 1999553709988549, 2000268717891775, 1999096468345194,
    2000053667194129, 2001022843888350, 2000509693206586, 1999394711363670, 2000362748104376,
    1999372853670224, 1999658281061803, 1998770004364202, 2000235478105819, 2000380378969906,
    2000481683313018, 2000282890007023, 2000781178526349, 2000416013174293, 2000231977132273,
    1999119442345463, 2000144828529557, 2001160697827227, 2001094685455762, 1998770920013213,
    1999033387741455, 1999479203330435, 2000921012260062, 2000400665259710, 2001341315852193,
    1999755479741060, 1998106097689373, 1999446115365328, 1999386741072141, 2001201455454513,
    1999835768170773, 2001344222970512, 1999787415595676, 1999193184955103]
private def pvn_m32_r256_5_3_p2 : List ℕ :=
  [1999215262754306, 1999652884485169, 2000409487235024, 2000067550313776, 1999899022350726,
    2000865582769730, 2000470395427080, 2000681707267658, 2000712708931303, 2000667273859818,
    2001080087577002, 2001468101920347, 2000234148331911, 1999851593924404, 1999250235337023,
    1999368705731119, 2000043240441092, 1999839534053103, 1998963548891580, 1999353306572050,
    2000901046799539, 2000666780223717, 2000171539593597, 2000309571191549, 1999262776931753,
    1999793712916127, 1999188615130120, 2000668584841541, 1998920832122223, 2000343031075613,
    1998540254372942, 1999809281479096, 1998675343982973, 1998305382047540, 1999542075537704,
    1999563237816212, 2000311146652044, 1998498139105543, 2002740090433235, 1997046284609129,
    2000604890307991, 2001283424367819, 1997013118684231, 2003720541926083, 1997588268371532,
    1998424395651623, 2002405100050182, 1996977504638293, 2001394951140462, 1999879262090455,
    1997910662077914, 2002035004619000, 1998064249250750, 1999547496365203, 2000058062280711,
    1996450885464763, 2002376014965065, 1999392002973797, 1995682896506617, 2006106468585081,
    2001398346026247, 1993675244316546, 2006103676823133, 2004969305557216]
private def pvn_m32_r256_5_3_p3 : List ℕ :=
  [1993379075130291, 2002155644504072, 2005224759243258, 1993873135878600, 1999266710815808,
    2006722887222316, 1997302749602706, 1997874019947413, 2007682941022016, 2000548945951661,
    1993957373547414, 2004356327421380, 2005165150826390, 1993465738757140, 1998159672159589,
    2008887818855170, 1998235298745297, 1987842111635449, 2003627625434300, 2015725989387628,
    1997095886341273, 1981959682712575, 2001993048176315, 2023038897785194, 2004799200104954,
    1974652972534979, 1983760176760252, 2021766454405332, 2031086933077383, 1994562649466422,
    1961153701803782, 1977211215239225, 2024825027264010, 2046203171792636, 2014229203192328,
    1961211812947408, 1940219008047074, 1969756070254469, 2019025493933336, 2040622842592827,
    2013984600871837, 1962161597148322, 1933613086434874, 1967965773552336, 2071251707277344,
    2214190129295230, 2350009593097795, 2438020341264688, 2459528082973246, 2420288852516778,
    2342151536833324, 2250949312898173, 2167041757179009, 2101342348316031, 2056156251767509,
    2028430664122311, 2013132452514940, 2005515813336772, 2002094299948747, 2000712286463521,
    2000214011761744, 2000055619956837, 2000012088528061, 2000002066993849]
private def pvn_m32_r256_5_3_p4 : List ℕ := [2000000240125287]
private def pvn_m32_r256_5_3 : List ℕ :=
  pCat pvn_m32_r256_5_3_p0
    (pCat pvn_m32_r256_5_3_p1
    (pCat pvn_m32_r256_5_3_p2
    (pCat pvn_m32_r256_5_3_p3
      pvn_m32_r256_5_3_p4)))
private def pvn_m32_r256_5_4_p0 : List ℕ :=
  [1999952785320975, 2000022720397761, 1999994179498746, 1999993928157863, 2000045500987046,
    1999896993356460, 2000064921213550, 1999944160129990, 2000200485023044, 1999839516332876,
    1999980334729848, 1999943406673513, 2000081169721667, 1999798515971887, 2000409687209390,
    1999780253782834, 1999899216550282, 2000099881869427, 1999966734254684, 1999773757521064,
    2000313224127766, 1999972938408588, 1999469196503045, 2001124307224052, 1998852317360830,
    2000943372330369, 1999747839529485, 1999873484011843, 2000346627319007, 2000239217438168,
    1999513326488698, 2000313823446058, 1999824211172388, 1999930395361673, 2000005602145166,
    2000030893338130, 2000110992518345, 1999886625685195, 2000303399362694, 1999808998787284,
    2000049497379596, 2000179320797078, 1999724701043515, 2000321963073992, 2000012599942753,
    1999526344906180, 2000401762947580, 2000069119073546, 1999993741322887, 1999221033587131,
    2001250741444917, 1999039348851353, 1999938098535130, 2000404704834327, 1999774983267707,
    1999735116900203, 2000532956249390, 1999981764410645, 1999228370741281, 2000620157980568,
    1999881125298050, 2000368935844595, 1999456766083282, 1999968762911204]
private def pvn_m32_r256_5_4_p1 : List ℕ :=
  [2000377423308763, 2000116452045630, 1999857637677824, 1999753117762771, 2000160560906215,
    2000231896012937, 2000028612409002, 1999187760851576, 2000947025868868, 1999382271311931,
    2000243103055483, 2000076389134913, 1999937711207103, 2000044972304020, 2000545186958944,
    1999409831849368, 1999981760368399, 2000220932235032, 2000715508077524, 1998691300643629,
    2000186209382675, 2000451218520581, 1999832443892855, 1999701591523149, 2000354822136074,
    1999817011055287, 2000093649426813, 1999906776005695, 2000345925767373, 1999524465143018,
    2000343865579787, 2000244945601383, 2000149603203034, 1999037714350415, 2000446497758478,
    2000371463689597, 2000263939575433, 1999819911249841, 1999340008683742, 2000709593587442,
    1999578020394712, 2000956505248444, 1999218996014217, 2000802470593842, 1999980461820390,
    1999010736039961, 1999490920322744, 2000575504392707, 2000838657569742, 1999622863806280,
    2000037830688443, 2001074306112444, 1999729480183466, 1999348789044918, 1998915188777270,
    1999227494014035, 2000114082741157, 2000958230166946, 2000774337568562, 1999917358883046,
    1998852342622100, 2000302384824115, 2001325386484377, 2000837792572653]
private def pvn_m32_r256_5_4_p2 : List ℕ :=
  [2000582525607258, 1999699576695563, 1999032942586623, 1999350681410699, 2000114809256577,
    2001108095544655, 2000886059218940, 2000559107053989, 1998349751395038, 1999933830606333,
    1998898395027786, 2000589754171757, 1999800703009145, 2000922230414484, 1999551442425220,
    2000417138632163, 2000247241354734, 1998399237385879, 2000203534380782, 1999349397185382,
    2001621004790686, 1998501941845133, 2000788933805703, 1999165753658187, 2001361975422159,
    2001830655167063, 1999043483803438, 2003775179039928, 1997989586409460, 2001570116760856,
    2002440195716284, 1996329272490691, 2002211453645568, 1997960939656049, 1998652730797700,
    2002393692071058, 1997518206105366, 2002001184384461, 2000430087655319, 1998183793553352,
    2001913576427104, 1998285579887851, 2000281942307099, 2000805174708805, 1998129226956195,
    2002083139906004, 1997964065545682, 1997200788953000, 2001936096879981, 1996522210221359,
    1999743523864181, 2002955797394318, 1994519339545432, 2000968764516061, 2004601005972256,
    1993724839858600, 2000904785422586, 2005898367745719, 1993466818056287, 1999034779488001,
    2006357038312754, 1994722398697870, 1997314775514293, 2006073167906873]
private def pvn_m32_r256_5_4_p3 : List ℕ :=
  [1997025730253748, 1996871187433625, 2004881276796907, 1997020335403122, 1995066642186806,
    2004706363877242, 1999126834088304, 1993608448531378, 2004282089954784, 2003636977565728,
    1994085305576273, 2002474957268441, 2008376696252545, 1995336857903846, 1994990305583826,
    2008450114187396, 2001412585120787, 1989399087150648, 2003600006022670, 2013848651899461,
    1994552577107330, 1986853856486591, 2010519969134233, 2016529330396372, 1988906835091964,
    1982145704902766, 2012011820336634, 2020714302252057, 1988480947922180, 1974421758496858,
    2007715325442191, 2031853920282529, 2002818142406584, 1966386043354391, 1983123737280935,
    2029602192352423, 2034576198557067, 1987676924926612, 1954550072528857, 1982901491976698,
    2037419888388498, 2047827687458568, 1998732325356783, 1946797863413851, 1951631662837280,
    2007242564038617, 2049326818419239, 2024478647378844, 1946960835604944, 1889970314655172,
    1924894724688403, 2064966372269314, 2257079997582451, 2420252027342936, 2495308747849194,
    2471115965751137, 2377684515919502, 2260329366873445, 2155580092146464, 2080680268563975,
    2036086276250132, 2013722683729983, 2004315580575096, 2001061855043083]
private def pvn_m32_r256_5_4_p4 : List ℕ := [2000177472272422]
private def pvn_m32_r256_5_4 : List ℕ :=
  pCat pvn_m32_r256_5_4_p0
    (pCat pvn_m32_r256_5_4_p1
    (pCat pvn_m32_r256_5_4_p2
    (pCat pvn_m32_r256_5_4_p3
      pvn_m32_r256_5_4_p4)))
private def pvn_m32_r256_5_5_p0 : List ℕ :=
  [2000018777085398, 1999840114082040, 2000146328755458, 1999841448304249, 2000128122702435,
    1999848712158030, 2000174528092316, 1999770452796597, 2000148339473574, 2000169899530679,
    1999752998207289, 2000091374284837, 1999616103150715, 2000937927404468, 1998756412519834,
    2000871566263060, 2000098345036462, 1999510265231154, 2000184515148542, 2000290413690430,
    1999344560641347, 2000213722179238, 2000336917897906, 1999595928597863, 2000211085020541,
    2000092081239379, 1999951893676073, 1999824639984949, 1999993724517740, 2000265538764002,
    1999799751674022, 1999698308429513, 2000531863584525, 1999396442704807, 2000620523796638,
    1999545515580677, 2000423170452092, 1999550041087561, 2000352521788674, 2000211040644890,
    1999491444014154, 2000701354939981, 2000055000674547, 1999702316371122, 1999831526700132,
    2000976442080958, 1999085889358450, 1999725115425593, 2000732486889905, 1999744447068633,
    1999832581342489, 2000066194839006, 2000320269848947, 1999618737411138, 2000381719048075,
    1999680058514159, 2000663773108104, 1999252646376126, 2000342823745600, 2000213997891169,
    1999844033358775, 1999833465340194, 2000197952965662, 1999628788481649]
private def pvn_m32_r256_5_5_p1 : List ℕ :=
  [2000964493752577, 1999374943200680, 1999666490306462, 1999938294093402, 2000608201516247,
    1999727446647894, 1999687190470997, 2000084364562929, 2000148589227271, 1999629483152289,
    2000697631194388, 1999417585217284, 1999845749897606, 2000307386659117, 2000459771343048,
    1999121858677946, 2000201694652039, 2000529780535547, 1999869717153214, 1999722073670819,
    1999686462757252, 2001194357815953, 1999042479354230, 2000455673659918, 1999460569298654,
    2000342204147331, 1999851252125480, 2000076244739965, 2000314544628460, 1999370457907883,
    2000249628179033, 2000480643918067, 1999821253613685, 2000023114232018, 1999790335379404,
    2000423878509324, 1999917002396435, 1999794540321183, 1999610951132862, 2000072478658497,
    2000699264885612, 1999889665013530, 1998930818374259, 2000420542651812, 2000621288383473,
    1999624348426124, 1999919669192709, 2000301572027478, 2000195492278732, 1999530569859087,
    1999490683885740, 2001067941818589, 2000038247757080, 2000074601654862, 1999146763625339,
    2000560162713740, 1999203226127452, 2001287453223604, 1999776766282180, 2000074969520638,
    1999887760091265, 2000336000337149, 2000299596552482, 1998706649476460]
private def pvn_m32_r256_5_5_p2 : List ℕ :=
  [1999910193707050, 1998965805450546, 2002662785746862, 1999855220554111, 2000877764717610,
    1998903321381031, 1999204560812712, 1999730182590639, 1999463608875643, 2002131435775502,
    1997798486369865, 2001025873393307, 1998482904394301, 1999322571402632, 2003300619064358,
    1998678199200487, 2003009731072391, 1998298035458859, 1998058155326020, 2003175602216936,
    1997056331659599, 2001883573618127, 2001300033909409, 1998416165825538, 2002401799847913,
    1997467925802746, 1999499984198554, 2000912792614851, 1998757831691614, 2002352009371204,
    1998651086417155, 1999293529792716, 2001561374377008, 1998309097737510, 2001423637492403,
    1999103942621510, 1998234250660281, 2002459063983469, 1997579448347852, 2000391418639223,
    2002843206063777, 1996706349750817, 2003163807460805, 2003051579788900, 1996808899365716,
    2004593129344909, 2000398155280934, 1994921843285036, 2004847511823301, 1998681923407295,
    1994588326516503, 2006710338744061, 1999556686354756, 1994086077033528, 2005594232681105,
    1999618787299724, 1994988635163451, 2005745640940097, 2000046213022772, 1994713609178680,
    2003906539644075, 1999282332912995, 1994762698742316, 2003362088307434]
private def pvn_m32_r256_5_5_p3 : List ℕ :=
  [1999027787624430, 1994641808215145, 2004092585474172, 2000311937862562, 1993858452301658,
    2004281922954523, 2003079736831990, 1992897230935223, 2001758278878540, 2005152649249319,
    1992888683784701, 1998806620657691, 2008476553741293, 1995240429029924, 1993080376029955,
    2008859039843892, 2001100230747620, 1987195291502280, 2003012078330811, 2010319641523813,
    1989258577794050, 1991763851251076, 2016748655041074, 2006284841222371, 1981666175743548,
    1999485442562895, 2021293635906191, 1996627800849580, 1977742202191095, 2007982046852728,
    2025008943521861, 1991096369223154, 1975293981133931, 2012664684978739, 2029723976369986,
    1989175011250852, 1966279098526890, 2006664695739559, 2038108295297758, 2001585486255981,
    1959375896550615, 1986798255825516, 2040814587535611, 2030770425881588, 1968722732726591,
    1952259689000368, 2011003955149004, 2058632555976854, 2021232344059437, 1948331732121327,
    1945386827513408, 2024117667725591, 2077359059370806, 2013786457075870, 1881683320066772,
    1831067925406642, 1960812611311284, 2220255659750541, 2457629848701948, 2548706000591274,
    2478408472091813, 2321308944542625, 2167110453780076, 2064861259047214]
private def pvn_m32_r256_5_5_p4 : List ℕ := [2016504788172636]
private def pvn_m32_r256_5_5 : List ℕ :=
  pCat pvn_m32_r256_5_5_p0
    (pCat pvn_m32_r256_5_5_p1
    (pCat pvn_m32_r256_5_5_p2
    (pCat pvn_m32_r256_5_5_p3
      pvn_m32_r256_5_5_p4)))
private def pvn_m32_r256_5_6_p0 : List ℕ :=
  [2000258411461780, 1999762449439820, 2000132915183622, 1999850128321372, 1999907767659894,
    2000383175434898, 1999318159911813, 2000775192478660, 1999147495874654, 2000706989753933,
    1999977146868554, 1999304011066059, 2000231250008453, 2000661465347079, 1999551023662046,
    1999598824059726, 2000718876198560, 1999832937740842, 1999596522053139, 2000204968191127,
    2000139277397515, 1999700938573614, 2000232848245454, 1999656965572600, 2000888556097609,
    1999183446527006, 2000331172283911, 2000006932102630, 1999889175506515, 2000014938735432,
    1999572618323017, 2000630318308908, 1999650848508528, 2000125607675414, 1999995055617271,
    2000150265799236, 1999595888131244, 2000202792107755, 2000580783064579, 1999014690582812,
    2000297953168910, 2000326729809989, 1999902213010440, 1999125697641746, 2001132695919008,
    1999687426334014, 1999820680270035, 1999806289599527, 2000348045321087, 2000086274633162,
    1999961057178527, 1999521718123624, 2001006810956105, 1999519867806845, 2000186881789569,
    2000216187135554, 1999948502798874, 1999804623971273, 2000155930215706, 1999753985544183,
    2000292268099858, 1999773570187682, 2000222487231132, 1999386068303004]
private def pvn_m32_r256_5_6_p1 : List ℕ :=
  [2000590445438416, 2000299253247916, 1999546888474126, 1999664215935871, 2000598023760084,
    2000401316384403, 1999219172111760, 2000704622529648, 1999145832249422, 2000597098354099,
    1999795266873748, 2000699219554146, 1999400249137905, 1999522682533612, 2000868762007209,
    1999890351469077, 1999595328470325, 1999793897062637, 2000342289933334, 2000299807464172,
    1999151243428541, 2000319707158692, 2000195760558473, 1999899032888350, 1999893683246860,
    1999992160176654, 1999940259692774, 2000042897565297, 2000157933216779, 2000087632040087,
    1999524361927922, 2000101039639741, 2000406099183657, 1999900353144281, 2000099140422624,
    1999887338285145, 1999488135161825, 2000962750996971, 1999570763692500, 1999867907393349,
    1999343946174560, 2001327383263154, 1999393888528453, 1999893474252544, 1999423539922623,
    2001194895048613, 2000126932641224, 1999103951277466, 2000699195112293, 1999584462974230,
    2000527125867123, 1998864212309766, 2001446563271876, 1998925969301990, 2000686475067308,
    1999276475930768, 1999695780363258, 2000923601837845, 1999374494069446, 2001366915111305,
    1998187473113713, 2000839549535161, 1999391403086853, 2000729090320087]
private def pvn_m32_r256_5_6_p2 : List ℕ :=
  [2001173709666458, 1997228555038411, 2002556904575389, 1998633099619488, 2000232116196231,
    2001051084926983, 1997001216693041, 2003176416784904, 1999129420876753, 2000542765608535,
    2001841061463165, 1995821843442682, 2001564910502393, 1999445745359364, 1999417796440232,
    2003426393110566, 1998469307606243, 2000234228711380, 1999211565740038, 1999219028825380,
    2002637847120758, 1998394778522632, 1999922679011570, 1999383524144967, 1997944245095912,
    2002318102589020, 1999151286363516, 2000786365742616, 2002354612633158, 1997628336937018,
    2001488246781185, 1999152649872395, 1998015903235475, 2004784426406177, 1998405179809784,
    1998813178460610, 2003538901221378, 1995729645458895, 2000921507702714, 2003268477418865,
    1994615311764579, 2002762917957046, 2002241148621555, 1994510578728565, 2004593610654505,
    2000725177015120, 1993779436073880, 2005356777548981, 2000070307083683, 1993798680466771,
    2005109510296116, 1999799484921875, 1995346237450525, 2005817159458197, 2000662447882277,
    1997799086512181, 2005876127583306, 1998656343716094, 1996524160734766, 2004546900229206,
    1998034866663192, 1997548794558770, 2005023160479526, 1996878230728703]
private def pvn_m32_r256_5_6_p3 : List ℕ :=
  [1996761566139223, 2006192798251387, 1997701186482306, 1995919770983072, 2006936074552417,
    1998664360871409, 1993527007449351, 2005938555460500, 1999964715251407, 1991290613144723,
    2004784313186179, 2002842890812678, 1989562196410471, 2002863884276824, 2008623229151052,
    1990186951817730, 1996752191181631, 2012448929287109, 1994524067623253, 1988426150046325,
    2012440392964270, 2005532469556176, 1982618626855631, 2002345210084024, 2017913634757700,
    1988137182461381, 1982644289397531, 2016384398909389, 2009883874830113, 1977668123300895,
    1997463887173524, 2026783545231219, 1996950699510965, 1972945471825595, 2010433878188567,
    2028161375827737, 1984482211985250, 1972387703571688, 2021878573402370, 2031325902302263,
    1977486758453326, 1968064525657707, 2025065172794794, 2036336430622281, 1975261602584279,
    1957767425657437, 2022357763872921, 2051180144582882, 1985636784387176, 1940700878043782,
    2002821115855188, 2068219998246160, 2015758284557003, 1925051778531432, 1958462214648182,
    2083857347616784, 2093582061574682, 1918046945055628, 1768759006000745, 1887580850086010,
    2239284371821470, 2545030960215492, 2585789221017184, 2394195279893314]
private def pvn_m32_r256_5_6_p4 : List ℕ := [2158310743696649]
private def pvn_m32_r256_5_6 : List ℕ :=
  pCat pvn_m32_r256_5_6_p0
    (pCat pvn_m32_r256_5_6_p1
    (pCat pvn_m32_r256_5_6_p2
    (pCat pvn_m32_r256_5_6_p3
      pvn_m32_r256_5_6_p4)))
private def phb_m32_r256_6_p0 : List ℕ :=
  [103184884372621, 145477537722688, 177624147766365, 204468943949290, 227894503016244,
    248869365890438, 267970663271064, 285575571090789, 301946865493798, 317276443689356,
    331709602262084, 345359554859536, 358316598042874, 370654157061172, 382432919983410,
    393703751400822, 404509799510455, 414888054056629, 424870520720061, 434485121548759,
    443756395810744, 452706052883295, 461353413711297, 469715767154732, 477808660493275,
    485646138399203, 493240941149387, 500604670280987, 507747928010344, 514680435332501,
    521411132664075, 527948266090413, 534299461662375, 540471789711229, 546471820777495,
    552305674456159, 557979062227783, 563497325159025, 568865467206390, 574088184735964,
    579169892773249, 584114748416531, 588926671780755, 593609364783996, 598166328042917,
    602600876105530, 606916151217620, 611115135792306, 615200663729491, 619175430712663,
    623042003594140, 626802828965780, 630460241000221, 634016468637360, 637473642181883,
    640833799369951, 644098890956504, 647270785868776, 650351275966620, 653342080445778,
    656244849916351, 659061170185359, 661792565769238, 664440503159521]
private def phb_m32_r256_6_p1 : List ℕ :=
  [667006393862581, 669491597232278, 671897423112484, 674225134304860, 676475948875782,
    678651042315032, 680751549557698, 682778566879708, 684733153676461, 686616334133229,
    688429098795196, 690172406044374, 691847183489990, 693454329278397, 694994713328074,
    696469178494804, 697878541671722, 699223594828558, 700505105994044, 701723820185155,
    702880460286575, 703975727883510, 705010304050751, 705984850100655, 706900008292535,
    707756402505756, 708554638878675, 709295306415401, 709978977562228, 710606208755446,
    711177540942133, 711693500075396, 712154597585475, 712561330827962, 712914183510373,
    713213626098168, 713460116201289, 713654098942179, 713796007306205, 713886262475338,
    713925274145894, 713913440831072, 713851150149002, 713738779096945, 713576694312272,
    713365252320773, 713104799772854, 712795673668107, 712438201568722, 712032701802193,
    711579483653703, 711078847548586, 710531085225221, 709936479898671, 709295306415401,
    708607831399333, 707874313389527, 707095002969712, 706270142889903, 705399968180316,
    704484706257751, 703524577024635, 702519792960876, 701470559208655]
private def phb_m32_r256_6_p2 : List ℕ :=
  [700377073650299, 699239526979336, 698058102764822, 696832977509031, 695564320698564,
    694252294848937, 692897055542680, 691498751460977, 690057524408848, 688573509333888,
    687046834338515, 685477620685728, 683865982798309, 682212028251405, 680515857758434,
    678777565150201, 676997237347126, 675174954324468, 673310789070388, 671404807536701,
    669457068582147, 667467623907962, 665436517985559, 663363787976061, 661249463641432,
    659093567246926, 656896113454534, 654657109207099, 652376553602734, 650054437759147,
    647690744667444, 645285449034950, 642838517116546, 640349906533989, 637819566082631,
    635247435524911, 632633445369939, 629977516638461, 627279560612392, 624539478568097,
    621757161492494, 618932489780981, 616065332916151, 613155549126113, 610202985021206,
    607207475207738, 604168841877313, 601086894370172, 597961428710834, 594792227114205,
    591579057460147, 588321672734323, 585019810432979, 581673191929066, 578281521796931,
    574844487092507, 571361756585706, 567832979941349, 564257786844709, 560635786067288,
    556966564468098, 553249685925216, 549484690191896, 545671091670915]
private def phb_m32_r256_6_p3 : List ℕ :=
  [541808378100244, 537896009142364, 533933414868800, 529919994130506, 525855112803773,
    521738101900148, 517568255527628, 513344828688892, 509067034900760, 504734043617145,
    500344977435717, 495898909066040, 491394858034215, 486831787095928, 482208598326147,
    477524128849587, 472777146171232, 467966343060668, 463090331937486, 458147638697542,
    453136695911066, 448055835313296, 442903279496279, 437677132696148, 432375370553315,
    426995828702900, 421536190028725, 415993970385414, 410366502558471, 404650918190258,
    398844127348761, 392942795353640, 386943316397331, 380841783404112, 374633953451959,
    368315207934125, 361880506450813, 355324333184197, 348640634206318, 341822743776943,
    334863297176876, 327754126948586, 320486138519771, 313049159979313, 305431759131695,
    297621018686569, 289602257260083, 281358679336050, 272870930771192, 264116526726178,
    255069104245789, 245697429017107, 235964049714432, 225823434014137, 215219319336478,
    204080831946378, 192316593199540, 179805368620196, 166380403519644, 151801295465999,
    135698605325057, 117449692356013, 95839170282083, 67726047262530]
private def phb_m32_r256_6 : List ℕ :=
  pCat phb_m32_r256_6_p0
    (pCat phb_m32_r256_6_p1
    (pCat phb_m32_r256_6_p2
      phb_m32_r256_6_p3))
private def pvn_m32_r256_6_0_p0 : List ℕ :=
  [1999741588538220, 1999762449439820, 2000132915183622, 1999850128321372, 1999907767659894,
    2000383175434898, 2000681840088187, 2000775192478660, 1999147495874654, 2000706989753933,
    1999977146868554, 1999304011066059, 2000231250008453, 2000661465347079, 1999551023662046,
    2000401175940274, 2000718876198560, 1999832937740842, 1999596522053139, 2000204968191127,
    1999860722602485, 1999700938573614, 2000232848245454, 1999656965572600, 2000888556097609,
    2000816553472994, 2000331172283911, 2000006932102630, 1999889175506515, 2000014938735432,
    2000427381676983, 2000630318308908, 1999650848508528, 2000125607675414, 1999995055617271,
    1999849734200764, 1999595888131244, 2000202792107755, 2000580783064579, 1999014690582812,
    1999702046831090, 2000326729809989, 2000097786989560, 1999125697641746, 2001132695919008,
    2000312573665986, 1999820680270035, 1999806289599527, 2000348045321087, 2000086274633162,
    1999961057178527, 1999521718123624, 2001006810956105, 1999519867806845, 2000186881789569,
    2000216187135554, 1999948502798874, 2000195376028727, 2000155930215706, 2000246014455817,
    1999707731900142, 1999773570187682, 2000222487231132, 1999386068303004]
private def pvn_m32_r256_6_0_p1 : List ℕ :=
  [2000590445438416, 2000299253247916, 1999546888474126, 1999664215935871, 2000598023760084,
    2000401316384403, 1999219172111760, 2000704622529648, 1999145832249422, 2000597098354099,
    1999795266873748, 1999300780445854, 1999400249137905, 1999522682533612, 2000868762007209,
    1999890351469077, 2000404671529675, 1999793897062637, 2000342289933334, 2000299807464172,
    1999151243428541, 2000319707158692, 2000195760558473, 2000100967111650, 1999893683246860,
    2000007839823346, 2000059740307226, 2000042897565297, 2000157933216779, 2000087632040087,
    2000475638072078, 2000101039639741, 2000406099183657, 1999900353144281, 2000099140422624,
    1999887338285145, 2000511864838175, 2000962750996971, 2000429236307500, 1999867907393349,
    1999343946174560, 1998672616736846, 1999393888528453, 2000106525747456, 1999423539922623,
    2001194895048613, 2000126932641224, 1999103951277466, 1999300804887707, 1999584462974230,
    2000527125867123, 2001135787690234, 2001446563271876, 1998925969301990, 2000686475067308,
    1999276475930768, 2000304219636742, 2000923601837845, 1999374494069446, 2001366915111305,
    1998187473113713, 1999160450464839, 1999391403086853, 2000729090320087]
private def pvn_m32_r256_6_0_p2 : List ℕ :=
  [2001173709666458, 1997228555038411, 1997443095424611, 1998633099619488, 2000232116196231,
    2001051084926983, 1997001216693041, 2003176416784904, 1999129420876753, 2000542765608535,
    2001841061463165, 1995821843442682, 1998435089497607, 1999445745359364, 1999417796440232,
    2003426393110566, 1998469307606243, 2000234228711380, 1999211565740038, 1999219028825380,
    2002637847120758, 1998394778522632, 1999922679011570, 1999383524144967, 1997944245095912,
    2002318102589020, 1999151286363516, 2000786365742616, 2002354612633158, 1997628336937018,
    2001488246781185, 1999152649872395, 1998015903235475, 2004784426406177, 1998405179809784,
    1998813178460610, 2003538901221378, 2004270354541105, 2000921507702714, 2003268477418865,
    1994615311764579, 2002762917957046, 2002241148621555, 1994510578728565, 2004593610654505,
    2000725177015120, 1993779436073880, 1994643222451019, 1999929692916317, 1993798680466771,
    2005109510296116, 1999799484921875, 2004653762549475, 2005817159458197, 2000662447882277,
    1997799086512181, 2005876127583306, 1998656343716094, 1996524160734766, 2004546900229206,
    1998034866663192, 1997548794558770, 1994976839520474, 1996878230728703]
private def pvn_m32_r256_6_0_p3 : List ℕ :=
  [1996761566139223, 2006192798251387, 1997701186482306, 2004080229016928, 2006936074552417,
    1998664360871409, 1993527007449351, 2005938555460500, 1999964715251407, 1991290613144723,
    2004784313186179, 2002842890812678, 1989562196410471, 1997136115723176, 2008623229151052,
    1990186951817730, 1996752191181631, 2012448929287109, 1994524067623253, 1988426150046325,
    2012440392964270, 2005532469556176, 1982618626855631, 2002345210084024, 2017913634757700,
    1988137182461381, 1982644289397531, 2016384398909389, 1990116125169887, 1977668123300895,
    2002536112826476, 2026783545231219, 2003049300489035, 2027054528174405, 2010433878188567,
    2028161375827737, 2015517788014750, 2027612296428312, 2021878573402370, 2031325902302263,
    2022513241546674, 2031935474342293, 2025065172794794, 2036336430622281, 2024738397415721,
    2042232574342563, 2022357763872921, 2051180144582882, 2014363215612824, 2059299121956218,
    2002821115855188, 2068219998246160, 2015758284557003, 2074948221468568, 2041537785351818,
    2083857347616784, 2093582061574682, 2081953054944372, 2231240993999255, 2112419149913990,
    2239284371821470, 2545030960215492, 2585789221017184, 2394195279893314]
private def pvn_m32_r256_6_0_p4 : List ℕ := [2158310743696649]
private def pvn_m32_r256_6_0 : List ℕ :=
  pCat pvn_m32_r256_6_0_p0
    (pCat pvn_m32_r256_6_0_p1
    (pCat pvn_m32_r256_6_0_p2
    (pCat pvn_m32_r256_6_0_p3
      pvn_m32_r256_6_0_p4)))
private def pvn_m32_r256_6_1_p0 : List ℕ :=
  [2000040181897549, 1999767004715655, 1999600649384131, 2000239139760374, 1999452130525825,
    2000621319367723, 1999734453756178, 1999173318028217, 2000070355531562, 2001123429461173,
    2000072088065771, 1999883946190787, 2000743516615220, 2000582274552766, 1999696360698165,
    1999548133617248, 2000674472377031, 1999650424276835, 1999776682880391, 2000133577549703,
    2000048551865117, 2000409570083498, 2000390959218573, 2000220003345493, 1999647635239970,
    2000392640216747, 2000056793968958, 1999820308651404, 1999902918968431, 1999396481346653,
    1999980857119379, 1999948626598747, 2001194655966972, 2000452493544924, 2000175352484249,
    1999648630468433, 2000959412266612, 1999828594478302, 1999620930816969, 2000720245937123,
    2001037930009367, 1999168925913552, 2000166151398912, 1999851522113765, 2000479542472445,
    1999676111525331, 1999545040503832, 2000725796824108, 1999887772467388, 1999269818979687,
    1999799893335658, 1999904437877037, 2000266258892462, 1999613073006722, 2000514070816994,
    2000195485774957, 1999826961306367, 2000519066278943, 1999786093023036, 2000143566807904,
    1999515095648549, 2001060951546964, 1999220408622292, 2000187925022150]
private def pvn_m32_r256_6_1_p1 : List ℕ :=
  [2000719624718908, 1999286621576106, 2000270138795299, 2000070659840637, 2000821301068184,
    1999806009972925, 1999837124284416, 1999924814041155, 1999687869312986, 2000684662142243,
    1999650252433862, 1999855837612393, 1999877355809238, 2000044269065628, 2000558159409693,
    1999904049836928, 1999483042417020, 1999984270797267, 2000831529603657, 1999982806432001,
    1999862317350331, 1999501936146528, 1999857317359532, 1999476441486791, 1999552128955957,
    1999932512839555, 2000181392823707, 2000350325164406, 2000082830347285, 1999978829932527,
    2000054285058267, 2000077635736512, 1999656400713679, 2000670343480313, 1999518165391280,
    2000108112048725, 2000427206428336, 1999420287904557, 2000416753719886, 1999717878850347,
    2000188861940167, 1999960797888423, 2001527543896698, 1999290826432641, 1999873688402515,
    2000428686943581, 1998936993132934, 2001815435921598, 1999756674139663, 2001390365717609,
    2000441414784609, 1999256065004633, 1999563371522776, 1998118841334602, 2000162544637108,
    2000729875432233, 1999939327146396, 2000773539117848, 1997264395574321, 2001353835970689,
    1998243067879725, 2000933933236912, 2001040667778286, 1999416853629320]
private def pvn_m32_r256_6_1_p2 : List ℕ :=
  [2002683337600390, 1997540609062648, 1998561819265776, 2004281366761377, 1998991039651094,
    2000926072565572, 1998361688366684, 1998539485982229, 2002084922746025, 1999351413430547,
    2001168415041380, 1998205487714379, 1998054735763919, 2000901258087918, 1997227536236972,
    1999479562599801, 1998311020868729, 1998432943767612, 2003794740700592, 2000070715697195,
    2000534863267904, 1999383039270461, 1995181034047617, 2002252909662700, 1998644781924283,
    1999976705465040, 2000674680676472, 1998940285830125, 1998352347622053, 2004458105071620,
    1996611513678562, 2000772579369696, 2002599911699988, 1994896252887505, 2002131617875216,
    1997592342141221, 2001628261913087, 2002730675173084, 1998625547107875, 1995317533679761,
    2008682498267558, 1996141057304793, 1998367059227374, 2001332641145590, 1999076642505583,
    2000397428299515, 2004140040864028, 2001339318185675, 2003751105051573, 2000773652519432,
    1994547558292696, 2006182611209760, 1999949008680927, 1999723140765557, 2001470323852534,
    2001033402752639, 1990564439261317, 1998443973924276, 1995954445752118, 1999163333913972,
    2002268916249666, 2001629633416869, 2003002226757598, 2006350610896747]
private def pvn_m32_r256_6_1_p3 : List ℕ :=
  [1997819786755066, 1997560681076891, 2009135535168199, 1998598340298952, 1996251010319249,
    2004681445609801, 1997492166190366, 1986290429301674, 2003866566899214, 2002870950002071,
    1991776544236366, 2009021625312223, 2008112569473652, 1989759838305888, 2003304822895681,
    2008919034436039, 1988377834442701, 1999641548646595, 2011770680029920, 1990381935431435,
    1984254557359068, 2020716218557165, 1991669381710272, 1985877584365895, 2009999530496459,
    2012630291894964, 1972301216614531, 2016673002345483, 2000258442813262, 1996713185247142,
    1993071994480716, 2012552193283317, 1998766008475339, 1993497805511077, 1982818158290176,
    1996847981545796, 1994928087667436, 2012363677520451, 2007316909790320, 2024872210307691,
    2007411852562149, 2033882420422971, 2007304476936203, 2045608575077014, 2002809339624367,
    2055000250786038, 2000779203993613, 2059114769650571, 2007305598792586, 2053151460184685,
    2023548740528873, 2045054784738366, 2040181290838601, 2014650220657493, 2077044086583043,
    1981676971497926, 2108737388833304, 2034339070632138, 2023090797906348, 2194882695185647,
    2090849916869784, 2068873211653561, 2415313691342236, 2690357684881644]
private def pvn_m32_r256_6_1_p4 : List ℕ := [2507486993183838]
private def pvn_m32_r256_6_1 : List ℕ :=
  pCat pvn_m32_r256_6_1_p0
    (pCat pvn_m32_r256_6_1_p1
    (pCat pvn_m32_r256_6_1_p2
    (pCat pvn_m32_r256_6_1_p3
      pvn_m32_r256_6_1_p4)))
private def pvn_m32_r256_6_2_p0 : List ℕ :=
  [1999879626311315, 2000604890311615, 1999433612587102, 1999918315828326, 2000109524760895,
    1999848231761117, 1999276196148215, 1999902663805615, 2000848833449873, 2000068415867705,
    1999457703858449, 1998984757426108, 2000368481403969, 2000593840735652, 1999541466807934,
    2000066759852743, 2000490077613200, 2000730530121040, 2000092431787979, 2000252983529535,
    2000319400554863, 1999674013166004, 2000525483758493, 1999803261006909, 2000075243660567,
    1999362703184167, 2000238715619877, 1999974601403232, 2000513096316412, 1999967176236412,
    2000339998611049, 2000094636792865, 2000191311945049, 1999526088054495, 2001287707853913,
    2000041539738884, 1998782519273297, 1999769368731133, 2000011165516269, 2000111272398627,
    1999990039886886, 1999973908543130, 2001351377948091, 2000272283425328, 1999662307100504,
    1999970351877116, 2000363197553579, 2000864540767883, 1999335454146503, 2000763826982342,
    2000146689017280, 2000513062037363, 1999443345176881, 1999948481602860, 2000616403317535,
    1999181911876501, 2000913121245363, 1999884793658051, 1999467902141764, 1999981733734567,
    1999880697376770, 1999855738374812, 1999260493684350, 2000580169982196]
private def pvn_m32_r256_6_2_p1 : List ℕ :=
  [2000026002825485, 1999805170264563, 2000409036204118, 2000074812660950, 2000251238741733,
    1999841783238454, 1999886481396506, 2000063762972283, 2000597712079698, 1999808799262155,
    1999993439261935, 1999751582603505, 1999934832005846, 2000531321679229, 2000488698811030,
    1999943433697280, 1999569909747702, 2000309553721656, 2000451354295327, 2000044923396360,
    1999283128997315, 2000176767155038, 1999930916119471, 2000436543799923, 1999993585202635,
    1999306890012909, 2000725916643759, 1999331081060478, 2000447166717423, 2000063165352283,
    2000500893278732, 1999790776728774, 2000209345630800, 1999809637478113, 1998496375222774,
    2001106668063057, 1998414934398655, 2000617941935608, 2000362646575423, 1999328759277791,
    2000719037384741, 1999609099584495, 2000395005857337, 2000110153890732, 1999041733284090,
    2001484127237740, 1998665306410354, 2001796912980288, 1998447986058301, 2000244094159446,
    2000222304373805, 1999105218769271, 2002057940952970, 1999008814031342, 2000443200589181,
    2001405409666760, 1997060003173217, 2002053465490017, 1998774621458434, 2000746165450354,
    2003873225510789, 1997808303009104, 2000394833481642, 1999632097491146]
private def pvn_m32_r256_6_2_p2 : List ℕ :=
  [1999094518187740, 2000162315505129, 1998825636215883, 2002600715174915, 1999067371844980,
    1997713954458204, 2000186210960159, 1998553014843852, 2002702762598840, 2000475208340131,
    1997329716748414, 2001887673670780, 1997928796585159, 2003558325177124, 2000269798072485,
    1998799712849804, 1999934806831446, 2000698140056828, 1998654363568287, 2003003316355476,
    1997539617870557, 1998837432930842, 2004506516296343, 1995110405362923, 2002171539886298,
    1995763968847146, 1996746434291092, 2000908227965053, 2002794850343793, 1997243511135170,
    2004323188732218, 1995039844560953, 2001353152513401, 2000854683336602, 1995204493643238,
    2002317751142824, 2001783424875184, 1994326319848812, 2000919827279734, 2004614570891598,
    1996927833723424, 2002355698675021, 1995738589654034, 2002209802654104, 2000033518030906,
    1998209482530430, 1999177578475476, 2004131076931617, 1995092203195226, 2003251911167821,
    2003404667037329, 1996034321225707, 1998426826853069, 2000779274129494, 1999238023437382,
    2002956856942302, 2003638839098274, 1999337254969967, 2003906542713106, 1996610524176676,
    2000145235577236, 2007488945340905, 2000493146835305, 1995664878097115]
private def pvn_m32_r256_6_2_p3 : List ℕ :=
  [2005909716259364, 1994953020791719, 1987287443675473, 2004946025108242, 1998810027625865,
    1993239546334849, 2011188716516483, 2002192533580124, 1991134224204498, 2011421609510600,
    2002213393724001, 1995432565079334, 2007081098916098, 2006641507194805, 1977706243535303,
    2009351009150035, 1998815710932425, 1988187850934676, 2003561575297799, 2022122761611192,
    1971743192747263, 2015644364860299, 2007397311887251, 1989573082058766, 1998282424731672,
    2012775230864115, 1987333541004203, 1997301411453925, 2001482895041445, 2003163453768443,
    1987451811388387, 2007372998647359, 1997896391100340, 2005273222923700, 1983198748202141,
    2014441507417675, 1990448502983937, 2023249667767202, 1975610242122301, 2013870983965548,
    1961954801414134, 2020281118673233, 1976205873018584, 2030221289803813, 1995035245682322,
    2028910242349068, 2015737845757305, 2021890815365259, 2037060329987674, 2005451352191710,
    2067913461295543, 1982257266272902, 2083285861950061, 2002110701429556, 2043872432796541,
    2080148132417126, 1965529773146282, 2099647708879705, 2048379896877900, 1963992885146010,
    2164360091406023, 2107398448661963, 1939346944155052, 2390935777786426]
private def pvn_m32_r256_6_2_p4 : List ℕ := [2870243707121267]
private def pvn_m32_r256_6_2 : List ℕ :=
  pCat pvn_m32_r256_6_2_p0
    (pCat pvn_m32_r256_6_2_p1
    (pCat pvn_m32_r256_6_2_p2
    (pCat pvn_m32_r256_6_2_p3
      pvn_m32_r256_6_2_p4)))
private def phb_m32_r256_7_p0 : List ℕ :=
  [107558214866950, 151643376409534, 185152470414385, 213135041441704, 237553456317307,
    259417306061814, 279328182159554, 297679246557212, 314744412756265, 330723711230094,
    345768596732589, 359997081295294, 373503288558376, 386363755785646, 398641743215296,
    410390271254979, 421654316870821, 432472437559799, 442877995513523, 452900096212483,
    462564318983329, 471893293321458, 480907159059889, 489623937819985, 498059835828640,
    506229493019675, 514146189646736, 521822018960053, 529268032534383, 536494363373991,
    543510330821118, 550324530458584, 556944911555531, 563378844108195, 569633177139217,
    575714289613076, 581628135082538, 587380280987043, 592975943367995, 598420017639636,
    603717105951444, 608871541593834, 613887410829715, 618768572477187, 623518675521097,
    628141174991406, 632639346313089, 637016298304199, 641274984975066, 645418216261523,
    649448667807922, 653368889901103, 657181315643974, 660888268446576, 664491968903236,
    667994541116390, 671398018520682, 674704349254915, 677915401124131, 681032966189500,
    684058765019663, 686994450633596, 689841612161990, 692601778251335]
private def phb_m32_r256_7_p1 : List ℕ :=
  [695276420232502, 697866955073444, 700374748133727, 702801115736889, 705147327575153,
    707414608959601, 709604142927778, 711717072219557, 713754501131161, 715717497256357,
    717607093123044, 719424287732761, 721170048010006, 722845310167666, 724450980994359,
    725987939068996, 727457035907455, 728859097045868, 730194923064667, 731465290557211,
    732670953046524, 733812641853410, 734891066918950, 735906917584197, 736860863329622,
    737753554476746, 738585622854155, 739357682429978, 740070329912755, 740724145322460,
    741319692533368, 741857519790292, 742338160199643, 742762132196656, 743129939990034,
    743442073985185, 743699011187133, 743901215584143, 744049138512991, 744143219006792,
    744183884126199, 744171549274772, 744106618499232, 743989484775281, 743820530279644,
    743600126648901, 743328635225695, 743006407292819, 742633784295679, 742211098053581,
    741738670960278, 741216816174166, 740645837798498, 740026031051968, 739357682429978,
    738641069856892, 737876462829543, 737064122552261, 736204302063644, 735297246355294,
    734343192482720, 733342369668571, 732294999398383, 731201295508968]
private def phb_m32_r256_7_p2 : List ℕ :=
  [730061464269590, 728875704456023, 727644207417612, 726367157137404, 725044730285426,
    723677096265160, 722264417253260, 720806848232529, 719304537018175, 717757624277332,
    716166243541842, 714530521214247, 712850576566960, 711126521734533, 709358461698965,
    707546494267933, 705690710045844, 703791192397585, 701848017404804, 699861253814583,
    697830962980296, 695757198794457, 693640007613330, 691479428173053, 689275491497007,
    687028220794122, 684737631347815, 682403730395191, 680026516996138, 677605981891902,
    675142107352694, 672634867013846, 670084225700007, 667490139236798, 664852554249341,
    662171407947000, 659446627893624, 656678131762542, 653865827075495, 651009610924601,
    648109369676425, 645164978657113, 642176301817480, 639143191376855, 636065487444395,
    632943017616454, 629775596548506, 626563025499972, 623305091850191, 620001568583587,
    616652213741969, 613256769841686, 609814963253169, 606326503540197, 602791082755960,
    599208374692746, 595578034081795, 591899695739519, 588172973655976, 584397460021060,
    580572724183444, 576698311536860, 572773742327718, 568798510377516]
private def phb_m32_r256_7_p3 : List ℕ :=
  [564772081712796, 560693893094677, 556563350439151, 552379827118410, 548142662132397,
    543851158138629, 539504579326968, 535102149124545, 530643047714314, 526126409348789,
    521551319438309, 516916811390676, 512221863176137, 507465393588391, 502646258168567,
    497763244754722, 492815068614462, 487800367112447, 482717693857835, 477565512268879,
    472342188482736, 467045983527847, 461675044663591, 456227395777105, 450700926709475,
    445093381362588, 439402344412911, 433625226428436, 427759247148938, 421801416645911,
    415748514025391, 409597063271807, 403343305751062, 396983168792121, 390512229643321,
    383925673945468, 377218247669276, 370384201217578, 363417224076114, 356310367987639,
    349055956090816, 341645474763155, 334069443973083, 326317260688884, 318377008179252,
    310235221674623, 301876597543570, 293283628418134, 284436139859841, 275310694044489,
    265879810664094, 256110931588068, 245965018174645, 235394608283632, 224341054733533,
    212730479916482, 200467632246768, 187426138914331, 173432177592903, 158235156768228,
    141449979204227, 122427614502780, 99901164134130, 70596510214099]
private def phb_m32_r256_7 : List ℕ :=
  pCat phb_m32_r256_7_p0
    (pCat phb_m32_r256_7_p1
    (pCat phb_m32_r256_7_p2
      phb_m32_r256_7_p3))
private def pvn_m32_r256_7_0_p0 : List ℕ :=
  [1999879626311315, 1999395109688385, 1999433612587102, 1999918315828326, 2000109524760895,
    1999848231761117, 1999276196148215, 1999902663805615, 2000848833449873, 2000068415867705,
    1999457703858449, 1998984757426108, 2000368481403969, 2000593840735652, 2000458533192066,
    2000066759852743, 2000490077613200, 1999269469878960, 2000092431787979, 2000252983529535,
    1999680599445137, 1999674013166004, 1999474516241507, 1999803261006909, 2000075243660567,
    2000637296815833, 2000238715619877, 1999974601403232, 2000513096316412, 1999967176236412,
    2000339998611049, 2000094636792865, 2000191311945049, 1999526088054495, 2001287707853913,
    1999958460261116, 1998782519273297, 1999769368731133, 2000011165516269, 2000111272398627,
    2000009960113114, 1999973908543130, 2001351377948091, 2000272283425328, 1999662307100504,
    2000029648122884, 2000363197553579, 1999135459232117, 1999335454146503, 2000763826982342,
    2000146689017280, 2000513062037363, 1999443345176881, 1999948481602860, 2000616403317535,
    2000818088123499, 2000913121245363, 1999884793658051, 2000532097858236, 1999981733734567,
    2000119302623230, 1999855738374812, 1999260493684350, 2000580169982196]
private def pvn_m32_r256_7_0_p1 : List ℕ :=
  [1999973997174515, 1999805170264563, 2000409036204118, 2000074812660950, 2000251238741733,
    1999841783238454, 1999886481396506, 2000063762972283, 2000597712079698, 1999808799262155,
    1999993439261935, 1999751582603505, 1999934832005846, 2000531321679229, 1999511301188970,
    1999943433697280, 2000430090252298, 2000309553721656, 2000451354295327, 1999955076603640,
    2000716871002685, 2000176767155038, 1999930916119471, 2000436543799923, 1999993585202635,
    1999306890012909, 1999274083356241, 1999331081060478, 2000447166717423, 2000063165352283,
    2000500893278732, 2000209223271226, 2000209345630800, 1999809637478113, 1998496375222774,
    2001106668063057, 2001585065601345, 2000617941935608, 2000362646575423, 1999328759277791,
    2000719037384741, 2000390900415505, 2000395005857337, 2000110153890732, 1999041733284090,
    2001484127237740, 2001334693589646, 2001796912980288, 1998447986058301, 2000244094159446,
    2000222304373805, 2000894781230729, 2002057940952970, 1999008814031342, 2000443200589181,
    2001405409666760, 2002939996826783, 2002053465490017, 1998774621458434, 2000746165450354,
    2003873225510789, 1997808303009104, 2000394833481642, 1999632097491146]
private def pvn_m32_r256_7_0_p2 : List ℕ :=
  [1999094518187740, 2000162315505129, 1998825636215883, 2002600715174915, 2000932628155020,
    1997713954458204, 2000186210960159, 2001446985156148, 2002702762598840, 2000475208340131,
    1997329716748414, 2001887673670780, 2002071203414841, 2003558325177124, 2000269798072485,
    1998799712849804, 1999934806831446, 2000698140056828, 1998654363568287, 2003003316355476,
    1997539617870557, 1998837432930842, 1995493483703657, 1995110405362923, 2002171539886298,
    1995763968847146, 1996746434291092, 1999091772034947, 2002794850343793, 1997243511135170,
    2004323188732218, 1995039844560953, 2001353152513401, 2000854683336602, 1995204493643238,
    2002317751142824, 2001783424875184, 2005673680151188, 2000919827279734, 2004614570891598,
    1996927833723424, 2002355698675021, 2004261410345966, 2002209802654104, 2000033518030906,
    1998209482530430, 1999177578475476, 2004131076931617, 1995092203195226, 2003251911167821,
    2003404667037329, 1996034321225707, 2001573173146931, 2000779274129494, 1999238023437382,
    2002956856942302, 2003638839098274, 2000662745030033, 2003906542713106, 1996610524176676,
    2000145235577236, 2007488945340905, 1999506853164695, 1995664878097115]
private def pvn_m32_r256_7_0_p3 : List ℕ :=
  [2005909716259364, 1994953020791719, 1987287443675473, 2004946025108242, 1998810027625865,
    1993239546334849, 2011188716516483, 2002192533580124, 2008865775795502, 2011421609510600,
    2002213393724001, 1995432565079334, 2007081098916098, 1993358492805195, 1977706243535303,
    2009351009150035, 1998815710932425, 1988187850934676, 2003561575297799, 2022122761611192,
    1971743192747263, 2015644364860299, 2007397311887251, 1989573082058766, 1998282424731672,
    2012775230864115, 1987333541004203, 1997301411453925, 1998517104958555, 2003163453768443,
    1987451811388387, 2007372998647359, 1997896391100340, 1994726777076300, 1983198748202141,
    2014441507417675, 1990448502983937, 2023249667767202, 2024389757877699, 2013870983965548,
    1961954801414134, 2020281118673233, 1976205873018584, 1969778710196187, 1995035245682322,
    2028910242349068, 2015737845757305, 2021890815365259, 2037060329987674, 2005451352191710,
    2067913461295543, 2017742733727098, 2083285861950061, 2002110701429556, 2043872432796541,
    2080148132417126, 2034470226853718, 2099647708879705, 2048379896877900, 2036007114853990,
    2164360091406023, 2107398448661963, 2060653055844948, 2390935777786426]
private def pvn_m32_r256_7_0_p4 : List ℕ := [2870243707121267]
private def pvn_m32_r256_7_0 : List ℕ :=
  pCat pvn_m32_r256_7_0_p0
    (pCat pvn_m32_r256_7_0_p1
    (pCat pvn_m32_r256_7_0_p2
    (pCat pvn_m32_r256_7_0_p3
      pvn_m32_r256_7_0_p4)))
private def pvn_m32_r256_7_1_p0 : List ℕ :=
  [2000063298955961, 1999765568597453, 1999416993442846, 1999488734069331, 1999695279135811,
    2000191254751990, 2000207461966655, 1999161120010542, 1999592922268911, 1999943487598086,
    2000921426878737, 2000165833437438, 1999467318147939, 1998954119847883, 2000324356676393,
    1999923047812819, 2000302697540479, 2000857679787025, 2000079770562898, 1999887197424699,
    1999858435509779, 2000178441448464, 1999995497924145, 1999922232824632, 1999887080101350,
    1999055813068230, 1999902564566329, 1999937077764287, 2000413544663265, 1999851720746395,
    2000815399154442, 1999764320271928, 2000001350604398, 2001092177948338, 1999791209732034,
    1999414652172983, 2000559632009212, 2000543065999382, 2000701247808660, 1999297628213863,
    1999481356877093, 2000125367438486, 1999884564690446, 1999196976804763, 1999917786268666,
    2001315482334055, 1999820519376927, 2000401681357346, 2000463031432397, 2000361882748087,
    1999958292599684, 1999029951294729, 1999861191311997, 1999910298475640, 2000768356641913,
    2000048611421816, 1999430908464241, 2000155587322447, 1999932584480867, 2000983370653286,
    2000648910656814, 1999994338830620, 2000903477753959, 2000388030601306]
private def pvn_m32_r256_7_1_p1 : List ℕ :=
  [2000038155256864, 1999770786088316, 2000021350809370, 1999774679349450, 2000168589276011,
    1999686609928788, 2000091061035988, 2000569574427318, 1999890222707595, 2000207489232853,
    1999695235927152, 1999923581116780, 2000725348547376, 1999905881691706, 1999979806056430,
    1999749844759527, 2000303370555018, 2000146844054111, 1999498795053886, 2000010710393678,
    2000311359847716, 1999778050073393, 2000455962466383, 2000211687447883, 2000610812983771,
    1999959265423097, 2000193259962291, 2000773981475156, 2000116643225953, 2000413467541812,
    1998825191016123, 1999477853205416, 2000242161477804, 1998798452498822, 2000387013625138,
    2000765135942262, 2000810637256697, 1999683404187075, 1998440878095557, 2000496657766740,
    2000025894357658, 2001826158905468, 1999988166791344, 2000615232656594, 1999378324485487,
    2000935045843150, 2001637691187894, 1998532989062627, 2000070858489093, 1999705401329420,
    2001368045195732, 2001989561953997, 2000152392762100, 1999468937814138, 2000048212297294,
    1999881608076006, 2003891518044390, 1997750177892105, 1998864063086628, 2003197447208934,
    2000929381963876, 2001616228351893, 2000292563589609, 2001677219006039]
private def pvn_m32_r256_7_1_p2 : List ℕ :=
  [2002429544349843, 1999290697000543, 2001273602675633, 2001200894139090, 1998223133162264,
    1999183584119558, 1998643499065472, 2003132521059043, 2000301219149896, 1998320548769033,
    1998987522006273, 2001709782899089, 2001922370477350, 2001919464584773, 1996173571603063,
    2002059771873196, 2001044302425529, 2001968350083276, 2003496191213416, 1998173655164220,
    2002617639489398, 1997685920158944, 2000104653409272, 2001688893559227, 2004153764885619,
    1992856828822642, 2000997898318011, 1996696342027640, 1997044130513938, 1999806272351367,
    1992610533330624, 2000777974691597, 1999097730883652, 2000961353730202, 1997041850260192,
    2003770917861901, 1998285278783250, 1998648392775112, 1998935104554803, 1997480286580649,
    2001278883403160, 2005673152589174, 2001671031925526, 2003713422790712, 1996510085215269,
    2004117496591079, 2006246177255389, 1997339370541819, 2003112719115037, 2001691319543850,
    1996962318287902, 2000313394029992, 2002172334211036, 1998468875637635, 2003283029521406,
    1998772872365309, 1999233618818438, 2002020260030437, 1997743653202796, 2001099142056267,
    2009327071111022, 1997921410683105, 1995804585649554, 2009610283140264]
private def pvn_m32_r256_7_1_p3 : List ℕ :=
  [1997716129346823, 1996058097333160, 2013507066874136, 1994643671859994, 1997451650426458,
    1999184711088815, 1994089875404690, 1995359265270089, 2002191571630965, 1995078880638111,
    2000277943617894, 2021543326393582, 1995695069662924, 2005987422798057, 2014904890787108,
    2002371274205688, 1973296411447711, 2021222558656165, 1980867637924387, 1987056713017052,
    2012665550811862, 2000632289993909, 1986616198879959, 2015435735124242, 1998337737616133,
    1997403775741043, 1999227579130369, 2011110823900716, 1988734035977059, 2001810239370782,
    1997202095442825, 2001492474103822, 1982813471478717, 2017821593522689, 1989254707674211,
    1998397928359499, 1991418666003991, 2003852394663312, 1968749302857676, 2043900345597403,
    2017627074564125, 1996399576696916, 2006690394044259, 2007697984516703, 1968309785119155,
    1971115566442598, 2010760344566850, 1987986825516800, 2050258877440736, 1990835572705827,
    2053555866000577, 2000824675901272, 2061562108232895, 2063222802810758, 2003528450363067,
    2069669880972874, 2030613673338479, 2067112824269298, 2104653541303509, 2004627254550787,
    2093697867892190, 2168375980722610, 2020762522363488, 2144697823339426]
private def pvn_m32_r256_7_1_p4 : List ℕ := [2946756890801670]
private def pvn_m32_r256_7_1 : List ℕ :=
  pCat pvn_m32_r256_7_1_p0
    (pCat pvn_m32_r256_7_1_p1
    (pCat pvn_m32_r256_7_1_p2
    (pCat pvn_m32_r256_7_1_p3
      pvn_m32_r256_7_1_p4)))
private def pwalks_m32_r256 : List RkmSegWalk := [
  ⟨uOfHb phb_m32_r256_0, bDec bZ (zPad bZ 1 pvn_m8_r256_0_0),
    bDec bZ (zPad bZ 33 pvn_m32_r256_0_1)⟩,
  ⟨uOfHb phb_m32_r256_1, bDec bZ (zPad bZ 33 pvn_m32_r256_0_1),
    bDec bZ (zPad bZ 65 pvn_m32_r256_1_1)⟩,
  ⟨uOfHb phb_m32_r256_2, bDec bZ (zPad bZ 65 pvn_m32_r256_2_0),
    bDec bZ (zPad bZ 129 pvn_m32_r256_2_2)⟩,
  ⟨uOfHb phb_m32_r256_3, bDec bZ (zPad bZ 129 pvn_m32_r256_3_0),
    bDec bZ (zPad bZ 257 pvn_m32_r256_3_3)⟩,
  ⟨uOfHb phb_m32_r256_4, bDec bZ (zPad bZ 257 pvn_m32_r256_4_0),
    bDec bZ (zPad bZ 257 pvn_m32_r256_4_4)⟩,
  ⟨uOfHb phb_m32_r256_5, bDec bZ (zPad bZ 257 pvn_m32_r256_5_0),
    bDec bZ (zPad bZ 257 pvn_m32_r256_5_6)⟩,
  ⟨uOfHb phb_m32_r256_6, bDec bZ (zPad bZ 257 pvn_m32_r256_6_0),
    bDec bZ (zPad bZ 257 pvn_m32_r256_6_2)⟩,
  ⟨uOfHb phb_m32_r256_7, bDec bZ (zPad bZ 257 pvn_m32_r256_7_0),
    bDec bZ (zPad bZ 257 pvn_m32_r256_7_1)⟩
  ]
private abbrev pdP_0 : Prop := rkmAllTrueF [
    bSlideChk 14 257 phb_m8_r256_6 257 pvn_m8_r256_6_4 257 pvn_m8_r256_6_5,
    bSlideChk 4 257 phb_m16_r256_7 257 pvn_m16_r256_7_0 257 pvn_m16_r256_7_1,
    bSlideChk 4 257 phb_m32_r256_7 257 pvn_m32_r256_7_0 257 pvn_m32_r256_7_1
  ] = true
private theorem pdk_0 : pdP_0 := by
  decide +kernel
private abbrev pdP_1 : Prop := rkmAllTrueF [
    bSlideChk 14 257 phb_m8_r256_6 257 pvn_m8_r256_6_3 257 pvn_m8_r256_6_4,
    bSlideChk 16 129 phb_m32_r256_2 65 pvn_m32_r256_2_0 129 pvn_m32_r256_2_1,
    bSlideChk 7 33 phb_m8_r256_2 17 pvn_m8_r256_1_1 33 pvn_m8_r256_2_1,
    rkmCheckRowFromWalks 16 28 256
      [2, 4, 8, 16, 28, 28, 28, 28]
      [16586577, 11809602, 12105415, 12346954, 8876427, 11909414, 2703894, 516844]
      [12, 16, 30, 53, 56, 75, 17, 4]
      rkmMasksPack_m16_r256 pwalks_m16_r256 rkmRowPack_m16_r256,
    bSlideChk 4 17 phb_m8_r256_1 9 pvn_m8_r256_0_1 17 pvn_m8_r256_1_1
  ] = true
private theorem pdk_1 : pdP_1 := by
  decide +kernel
private abbrev pdP_2 : Prop := rkmAllTrueF [
    bSlideChk 15 257 phb_m8_r256_6 257 pvn_m8_r256_6_1 257 pvn_m8_r256_6_2,
    bSlideChk 13 129 phb_m32_r256_2 129 pvn_m32_r256_2_1 129 pvn_m32_r256_2_2,
    bSlideChk 12 33 phb_m16_r256_0 1 pvn_m8_r256_0_0 33 pvn_m16_r256_0_1,
    rkmCheckRowFromWalks 8 56 256
      [1, 2, 4, 8, 16, 32, 56, 56]
      [9159601, 8524861, 9925076, 11078486, 12132789, 15039518, 11638492, 2696078]
      [2, 4, 7, 15, 30, 64, 73, 17]
      rkmMasksPack_m8_r256 pwalks_m8_r256 rkmRowPack_m8_r256
  ] = true
private theorem pdk_2 : pdP_2 := by
  decide +kernel
private abbrev pdP_3 : Prop := rkmAllTrueF [
    bSlideChk 16 257 phb_m8_r256_6 257 pvn_m8_r256_6_0 257 pvn_m8_r256_6_1,
    bSlideChk 13 129 phb_m8_r256_4 129 pvn_m8_r256_4_1 129 pvn_m8_r256_4_2,
    bSlideChk 12 33 phb_m32_r256_0 1 pvn_m8_r256_0_0 33 pvn_m32_r256_0_1,
    rkmCheckRowFromWalks 32 14 256
      [1, 2, 4, 8, 14, 14, 14, 14]
      [16813182, 11802523, 11889838, 12403318, 8884799, 11915996, 2742203, 635206]
      [12, 16, 29, 53, 56, 75, 18, 4]
      rkmMasksPack_m32_r256 pwalks_m32_r256 rkmRowPack_m32_r256,
    bSlideChk 2 9 phb_m8_r256_0 1 pvn_m8_r256_0_0 9 pvn_m8_r256_0_1
  ] = true
private theorem pdk_3 : pdP_3 := by
  decide +kernel
private abbrev pdP_4 : Prop := rkmAllTrueF [
    bSlideChk 14 257 phb_m8_r256_6 257 pvn_m8_r256_6_2 257 pvn_m8_r256_6_3,
    bSlideChk 13 129 phb_m16_r256_2 129 pvn_m16_r256_2_1 129 pvn_m16_r256_2_2,
    bSlideChk 15 65 phb_m8_r256_3 33 pvn_m8_r256_2_1 65 pvn_m8_r256_3_1
  ] = true
private theorem pdk_4 : pdP_4 := by
  decide +kernel
private abbrev pdP_5 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m16_r256_5 257 pvn_m16_r256_5_1 257 pvn_m16_r256_5_2,
    bSlideChk 9 257 phb_m32_r256_6 257 pvn_m32_r256_6_0 257 pvn_m32_r256_6_1
  ] = true
private theorem pdk_5 : pdP_5 := by
  decide +kernel
private abbrev pdP_6 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m16_r256_5 257 pvn_m16_r256_5_2 257 pvn_m16_r256_5_3,
    bSlideChk 9 257 phb_m32_r256_6 257 pvn_m32_r256_6_1 257 pvn_m32_r256_6_2
  ] = true
private theorem pdk_6 : pdP_6 := by
  decide +kernel
private abbrev pdP_7 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m16_r256_5 257 pvn_m16_r256_5_3 257 pvn_m16_r256_5_4,
    bSlideChk 9 257 phb_m8_r256_7 257 pvn_m8_r256_7_0 257 pvn_m8_r256_7_1
  ] = true
private theorem pdk_7 : pdP_7 := by
  decide +kernel
private abbrev pdP_8 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m16_r256_5 257 pvn_m16_r256_5_4 257 pvn_m16_r256_5_5,
    bSlideChk 8 257 phb_m16_r256_6 257 pvn_m16_r256_6_1 257 pvn_m16_r256_6_2
  ] = true
private theorem pdk_8 : pdP_8 := by
  decide +kernel
private abbrev pdP_9 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m32_r256_5 257 pvn_m32_r256_5_2 257 pvn_m32_r256_5_3,
    bSlideChk 8 257 phb_m8_r256_7 257 pvn_m8_r256_7_1 257 pvn_m8_r256_7_2
  ] = true
private theorem pdk_9 : pdP_9 := by
  decide +kernel
private abbrev pdP_10 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m32_r256_5 257 pvn_m32_r256_5_3 257 pvn_m32_r256_5_4,
    bSlideChk 17 129 phb_m8_r256_4 65 pvn_m8_r256_4_0 129 pvn_m8_r256_4_1,
    bSlideChk 16 65 phb_m16_r256_1 33 pvn_m16_r256_0_1 65 pvn_m16_r256_1_1
  ] = true
private theorem pdk_10 : pdP_10 := by
  decide +kernel
private abbrev pdP_11 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m32_r256_5 257 pvn_m32_r256_5_4 257 pvn_m32_r256_5_5,
    bSlideChk 17 129 phb_m16_r256_2 65 pvn_m16_r256_2_0 129 pvn_m16_r256_2_1,
    bSlideChk 16 65 phb_m32_r256_1 33 pvn_m32_r256_0_1 65 pvn_m32_r256_1_1
  ] = true
private theorem pdk_11 : pdP_11 := by
  decide +kernel
private abbrev pdP_12 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m32_r256_5 257 pvn_m32_r256_5_1 257 pvn_m32_r256_5_2,
    bSlideChk 9 257 phb_m16_r256_6 257 pvn_m16_r256_6_0 257 pvn_m16_r256_6_1
  ] = true
private theorem pdk_12 : pdP_12 := by
  decide +kernel
private abbrev pdP_13 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m16_r256_5 257 pvn_m16_r256_5_0 257 pvn_m16_r256_5_1,
    bSlideChk 10 257 phb_m32_r256_5 257 pvn_m32_r256_5_5 257 pvn_m32_r256_5_6
  ] = true
private theorem pdk_13 : pdP_13 := by
  decide +kernel
private abbrev pdP_14 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m32_r256_5 257 pvn_m32_r256_5_0 257 pvn_m32_r256_5_1,
    bSlideChk 10 257 phb_m16_r256_5 257 pvn_m16_r256_5_5 257 pvn_m16_r256_5_6
  ] = true
private theorem pdk_14 : pdP_14 := by
  decide +kernel
private abbrev pdP_15 : Prop := rkmAllTrueF [
    bSlideChk 16 257 phb_m16_r256_4 257 pvn_m16_r256_4_0 257 pvn_m16_r256_4_1,
    bSlideChk 13 257 phb_m8_r256_5 257 pvn_m8_r256_5_3 257 pvn_m8_r256_5_4
  ] = true
private theorem pdk_15 : pdP_15 := by
  decide +kernel
private abbrev pdP_16 : Prop := rkmAllTrueF [
    bSlideChk 16 257 phb_m32_r256_4 257 pvn_m32_r256_4_0 257 pvn_m32_r256_4_1,
    bSlideChk 16 257 phb_m8_r256_5 257 pvn_m8_r256_5_1 257 pvn_m8_r256_5_2
  ] = true
private theorem pdk_16 : pdP_16 := by
  decide +kernel
private abbrev pdP_17 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m16_r256_4 257 pvn_m16_r256_4_3 257 pvn_m16_r256_4_4,
    bSlideChk 20 257 phb_m8_r256_5 129 pvn_m8_r256_5_0 257 pvn_m8_r256_5_1
  ] = true
private theorem pdk_17 : pdP_17 := by
  decide +kernel
private abbrev pdP_18 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m32_r256_4 257 pvn_m32_r256_4_3 257 pvn_m32_r256_4_4,
    bSlideChk 15 257 phb_m32_r256_3 257 pvn_m32_r256_3_2 257 pvn_m32_r256_3_3
  ] = true
private theorem pdk_18 : pdP_18 := by
  decide +kernel
private abbrev pdP_19 : Prop := rkmAllTrueF [
    bSlideChk 14 257 phb_m16_r256_4 257 pvn_m16_r256_4_1 257 pvn_m16_r256_4_2,
    bSlideChk 15 257 phb_m8_r256_5 257 pvn_m8_r256_5_2 257 pvn_m8_r256_5_3
  ] = true
private theorem pdk_19 : pdP_19 := by
  decide +kernel
private abbrev pdP_20 : Prop := rkmAllTrueF [
    bSlideChk 14 257 phb_m32_r256_4 257 pvn_m32_r256_4_1 257 pvn_m32_r256_4_2,
    bSlideChk 15 257 phb_m16_r256_3 257 pvn_m16_r256_3_2 257 pvn_m16_r256_3_3
  ] = true
private theorem pdk_20 : pdP_20 := by
  decide +kernel
private abbrev pdP_21 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m16_r256_4 257 pvn_m16_r256_4_2 257 pvn_m16_r256_4_3,
    bSlideChk 17 257 phb_m32_r256_3 257 pvn_m32_r256_3_1 257 pvn_m32_r256_3_2
  ] = true
private theorem pdk_21 : pdP_21 := by
  decide +kernel
private abbrev pdP_22 : Prop := rkmAllTrueF [
    bSlideChk 13 257 phb_m32_r256_4 257 pvn_m32_r256_4_2 257 pvn_m32_r256_4_3,
    bSlideChk 17 257 phb_m16_r256_3 257 pvn_m16_r256_3_1 257 pvn_m16_r256_3_2
  ] = true
private theorem pdk_22 : pdP_22 := by
  decide +kernel
private abbrev pdP_23 : Prop := rkmAllTrueF [
    bSlideChk 21 257 phb_m16_r256_3 129 pvn_m16_r256_3_0 257 pvn_m16_r256_3_1,
    bSlideChk 21 257 phb_m32_r256_3 129 pvn_m32_r256_3_0 257 pvn_m32_r256_3_1
  ] = true
private theorem pdk_23 : pdP_23 := by
  decide +kernel
private theorem pdim_m8_r256_l1 :
    Nat.add (highdNatMin (Nat.mul 1 8) 256) 1 = 9 :=
  rfl
private theorem pdim_m8_r256_l2 :
    Nat.add (highdNatMin (Nat.mul 2 8) 256) 1 = 17 :=
  rfl
private theorem pdim_m8_r256_l4 :
    Nat.add (highdNatMin (Nat.mul 4 8) 256) 1 = 33 :=
  rfl
private theorem pdim_m8_r256_l8 :
    Nat.add (highdNatMin (Nat.mul 8 8) 256) 1 = 65 :=
  rfl
private theorem pdim_m8_r256_l16 :
    Nat.add (highdNatMin (Nat.mul 16 8) 256) 1 = 129 :=
  rfl
private theorem pdim_m8_r256_l32 :
    Nat.add (highdNatMin (Nat.mul 32 8) 256) 1 = 257 :=
  rfl
private theorem pdim_m8_r256_l56 :
    Nat.add (highdNatMin (Nat.mul 56 8) 256) 1 = 257 :=
  rfl
private theorem pdim_m16_r256_l2 :
    Nat.add (highdNatMin (Nat.mul 2 16) 256) 1 = 33 :=
  rfl
private theorem pdim_m16_r256_l4 :
    Nat.add (highdNatMin (Nat.mul 4 16) 256) 1 = 65 :=
  rfl
private theorem pdim_m16_r256_l8 :
    Nat.add (highdNatMin (Nat.mul 8 16) 256) 1 = 129 :=
  rfl
private theorem pdim_m16_r256_l16 :
    Nat.add (highdNatMin (Nat.mul 16 16) 256) 1 = 257 :=
  rfl
private theorem pdim_m16_r256_l28 :
    Nat.add (highdNatMin (Nat.mul 28 16) 256) 1 = 257 :=
  rfl
private theorem pdim_m32_r256_l1 :
    Nat.add (highdNatMin (Nat.mul 1 32) 256) 1 = 33 :=
  rfl
private theorem pdim_m32_r256_l2 :
    Nat.add (highdNatMin (Nat.mul 2 32) 256) 1 = 65 :=
  rfl
private theorem pdim_m32_r256_l4 :
    Nat.add (highdNatMin (Nat.mul 4 32) 256) 1 = 129 :=
  rfl
private theorem pdim_m32_r256_l8 :
    Nat.add (highdNatMin (Nat.mul 8 32) 256) 1 = 257 :=
  rfl
private theorem pdim_m32_r256_l14 :
    Nat.add (highdNatMin (Nat.mul 14 32) 256) 1 = 257 :=
  rfl
private theorem pwalk_m8_r256_0 :
    bWalkOk 2 9 phb_m8_r256_0 1 pvn_m8_r256_0_0 9 pvn_m8_r256_0_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl (rkmTl (rkmTl
      pdk_3)))))
private theorem pwalk_m8_r256_1 :
    bWalkOk 4 17 phb_m8_r256_1 9 pvn_m8_r256_0_1 17 pvn_m8_r256_1_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl (rkmTl (rkmTl
      pdk_1)))))
private theorem pwalk_m8_r256_2 :
    bWalkOk 7 33 phb_m8_r256_2 17 pvn_m8_r256_1_1 33 pvn_m8_r256_2_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_1)))
private theorem pwalk_m8_r256_3 :
    bWalkOk 15 65 phb_m8_r256_3 33 pvn_m8_r256_2_1 65 pvn_m8_r256_3_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_4)))
private theorem pw_m8_r256_4_0 :
    bWalkOk 17 129 phb_m8_r256_4 65 pvn_m8_r256_4_0 129 pvn_m8_r256_4_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_10))
private theorem pwalk_m8_r256_4 :
    bWalkOk 30 129 phb_m8_r256_4 65 pvn_m8_r256_4_0 129 pvn_m8_r256_4_2 :=
  bChn (rfl : 17 + 13 = 30) pw_m8_r256_4_0
    (rkmHd
      (rkmTl
      pdk_3))
private theorem pw_m8_r256_5_0 :
    bWalkOk 20 257 phb_m8_r256_5 129 pvn_m8_r256_5_0 257 pvn_m8_r256_5_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_17))
private theorem pw_m8_r256_5_1 :
    bWalkOk 36 257 phb_m8_r256_5 129 pvn_m8_r256_5_0 257 pvn_m8_r256_5_2 :=
  bChn (rfl : 20 + 16 = 36) pw_m8_r256_5_0
    (rkmHd
      (rkmTl
      pdk_16))
private theorem pw_m8_r256_5_2 :
    bWalkOk 51 257 phb_m8_r256_5 129 pvn_m8_r256_5_0 257 pvn_m8_r256_5_3 :=
  bChn (rfl : 36 + 15 = 51) pw_m8_r256_5_1
    (rkmHd
      (rkmTl
      pdk_19))
private theorem pwalk_m8_r256_5 :
    bWalkOk 64 257 phb_m8_r256_5 129 pvn_m8_r256_5_0 257 pvn_m8_r256_5_4 :=
  bChn (rfl : 51 + 13 = 64) pw_m8_r256_5_2
    (rkmHd
      (rkmTl
      pdk_15))
private theorem pw_m8_r256_6_0 :
    bWalkOk 16 257 phb_m8_r256_6 257 pvn_m8_r256_6_0 257 pvn_m8_r256_6_1 :=
  bWalk1
    (rkmHd
      pdk_3)
private theorem pw_m8_r256_6_1 :
    bWalkOk 31 257 phb_m8_r256_6 257 pvn_m8_r256_6_0 257 pvn_m8_r256_6_2 :=
  bChn (rfl : 16 + 15 = 31) pw_m8_r256_6_0
    (rkmHd
      pdk_2)
private theorem pw_m8_r256_6_2 :
    bWalkOk 45 257 phb_m8_r256_6 257 pvn_m8_r256_6_0 257 pvn_m8_r256_6_3 :=
  bChn (rfl : 31 + 14 = 45) pw_m8_r256_6_1
    (rkmHd
      pdk_4)
private theorem pw_m8_r256_6_3 :
    bWalkOk 59 257 phb_m8_r256_6 257 pvn_m8_r256_6_0 257 pvn_m8_r256_6_4 :=
  bChn (rfl : 45 + 14 = 59) pw_m8_r256_6_2
    (rkmHd
      pdk_1)
private theorem pwalk_m8_r256_6 :
    bWalkOk 73 257 phb_m8_r256_6 257 pvn_m8_r256_6_0 257 pvn_m8_r256_6_5 :=
  bChn (rfl : 59 + 14 = 73) pw_m8_r256_6_3
    (rkmHd
      pdk_0)
private theorem pw_m8_r256_7_0 :
    bWalkOk 9 257 phb_m8_r256_7 257 pvn_m8_r256_7_0 257 pvn_m8_r256_7_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_7))
private theorem pwalk_m8_r256_7 :
    bWalkOk 17 257 phb_m8_r256_7 257 pvn_m8_r256_7_0 257 pvn_m8_r256_7_2 :=
  bChn (rfl : 9 + 8 = 17) pw_m8_r256_7_0
    (rkmHd
      (rkmTl
      pdk_9))
private theorem pwalks_snd_m8_r256 :
    RkmSegWalksSound 8 256 [1, 2, 4, 8, 16, 32, 56, 56]
      [2, 4, 7, 15, 30, 64, 73, 17] pwalks_m8_r256 := by
  dsimp only [RkmSegWalksSound, pwalks_m8_r256]
  exact ⟨bSeg_mk pdim_m8_r256_l1 pwalk_m8_r256_0,
    ⟨bSeg_mk pdim_m8_r256_l2 pwalk_m8_r256_1,
    ⟨bSeg_mk pdim_m8_r256_l4 pwalk_m8_r256_2,
    ⟨bSeg_mk pdim_m8_r256_l8 pwalk_m8_r256_3,
    ⟨bSeg_mk pdim_m8_r256_l16 pwalk_m8_r256_4,
    ⟨bSeg_mk pdim_m8_r256_l32 pwalk_m8_r256_5,
    ⟨bSeg_mk pdim_m8_r256_l56 pwalk_m8_r256_6,
    ⟨bSeg_mk pdim_m8_r256_l56 pwalk_m8_r256_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 8, r = 256)`. -/
theorem rkmTrajPack_m8_r256 :
    rkmEvalT16Lo12 8 56 256 [1, 2, 4, 8, 16, 32, 56, 56]
      [9159601, 8524861, 9925076, 11078486, 12132789, 15039518, 11638492, 2696078]
      [2, 4, 7, 15, 30, 64, 73, 17]
      rkmMasksPack_m8_r256 = rkmRowPack_m8_r256 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m8_r256
    (rkmHd
      (rkmTl (rkmTl (rkmTl
      pdk_2))))

private theorem pwalk_m16_r256_0 :
    bWalkOk 12 33 phb_m16_r256_0 1 pvn_m8_r256_0_0 33 pvn_m16_r256_0_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_2)))
private theorem pwalk_m16_r256_1 :
    bWalkOk 16 65 phb_m16_r256_1 33 pvn_m16_r256_0_1 65 pvn_m16_r256_1_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_10)))
private theorem pw_m16_r256_2_0 :
    bWalkOk 17 129 phb_m16_r256_2 65 pvn_m16_r256_2_0 129 pvn_m16_r256_2_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_11))
private theorem pwalk_m16_r256_2 :
    bWalkOk 30 129 phb_m16_r256_2 65 pvn_m16_r256_2_0 129 pvn_m16_r256_2_2 :=
  bChn (rfl : 17 + 13 = 30) pw_m16_r256_2_0
    (rkmHd
      (rkmTl
      pdk_4))
private theorem pw_m16_r256_3_0 :
    bWalkOk 21 257 phb_m16_r256_3 129 pvn_m16_r256_3_0 257 pvn_m16_r256_3_1 :=
  bWalk1
    (rkmHd
      pdk_23)
private theorem pw_m16_r256_3_1 :
    bWalkOk 38 257 phb_m16_r256_3 129 pvn_m16_r256_3_0 257 pvn_m16_r256_3_2 :=
  bChn (rfl : 21 + 17 = 38) pw_m16_r256_3_0
    (rkmHd
      (rkmTl
      pdk_22))
private theorem pwalk_m16_r256_3 :
    bWalkOk 53 257 phb_m16_r256_3 129 pvn_m16_r256_3_0 257 pvn_m16_r256_3_3 :=
  bChn (rfl : 38 + 15 = 53) pw_m16_r256_3_1
    (rkmHd
      (rkmTl
      pdk_20))
private theorem pw_m16_r256_4_0 :
    bWalkOk 16 257 phb_m16_r256_4 257 pvn_m16_r256_4_0 257 pvn_m16_r256_4_1 :=
  bWalk1
    (rkmHd
      pdk_15)
private theorem pw_m16_r256_4_1 :
    bWalkOk 30 257 phb_m16_r256_4 257 pvn_m16_r256_4_0 257 pvn_m16_r256_4_2 :=
  bChn (rfl : 16 + 14 = 30) pw_m16_r256_4_0
    (rkmHd
      pdk_19)
private theorem pw_m16_r256_4_2 :
    bWalkOk 43 257 phb_m16_r256_4 257 pvn_m16_r256_4_0 257 pvn_m16_r256_4_3 :=
  bChn (rfl : 30 + 13 = 43) pw_m16_r256_4_1
    (rkmHd
      pdk_21)
private theorem pwalk_m16_r256_4 :
    bWalkOk 56 257 phb_m16_r256_4 257 pvn_m16_r256_4_0 257 pvn_m16_r256_4_4 :=
  bChn (rfl : 43 + 13 = 56) pw_m16_r256_4_2
    (rkmHd
      pdk_17)
private theorem pw_m16_r256_5_0 :
    bWalkOk 13 257 phb_m16_r256_5 257 pvn_m16_r256_5_0 257 pvn_m16_r256_5_1 :=
  bWalk1
    (rkmHd
      pdk_13)
private theorem pw_m16_r256_5_1 :
    bWalkOk 26 257 phb_m16_r256_5 257 pvn_m16_r256_5_0 257 pvn_m16_r256_5_2 :=
  bChn (rfl : 13 + 13 = 26) pw_m16_r256_5_0
    (rkmHd
      pdk_5)
private theorem pw_m16_r256_5_2 :
    bWalkOk 39 257 phb_m16_r256_5 257 pvn_m16_r256_5_0 257 pvn_m16_r256_5_3 :=
  bChn (rfl : 26 + 13 = 39) pw_m16_r256_5_1
    (rkmHd
      pdk_6)
private theorem pw_m16_r256_5_3 :
    bWalkOk 52 257 phb_m16_r256_5 257 pvn_m16_r256_5_0 257 pvn_m16_r256_5_4 :=
  bChn (rfl : 39 + 13 = 52) pw_m16_r256_5_2
    (rkmHd
      pdk_7)
private theorem pw_m16_r256_5_4 :
    bWalkOk 65 257 phb_m16_r256_5 257 pvn_m16_r256_5_0 257 pvn_m16_r256_5_5 :=
  bChn (rfl : 52 + 13 = 65) pw_m16_r256_5_3
    (rkmHd
      pdk_8)
private theorem pwalk_m16_r256_5 :
    bWalkOk 75 257 phb_m16_r256_5 257 pvn_m16_r256_5_0 257 pvn_m16_r256_5_6 :=
  bChn (rfl : 65 + 10 = 75) pw_m16_r256_5_4
    (rkmHd
      (rkmTl
      pdk_14))
private theorem pw_m16_r256_6_0 :
    bWalkOk 9 257 phb_m16_r256_6 257 pvn_m16_r256_6_0 257 pvn_m16_r256_6_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_12))
private theorem pwalk_m16_r256_6 :
    bWalkOk 17 257 phb_m16_r256_6 257 pvn_m16_r256_6_0 257 pvn_m16_r256_6_2 :=
  bChn (rfl : 9 + 8 = 17) pw_m16_r256_6_0
    (rkmHd
      (rkmTl
      pdk_8))
private theorem pwalk_m16_r256_7 :
    bWalkOk 4 257 phb_m16_r256_7 257 pvn_m16_r256_7_0 257 pvn_m16_r256_7_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_0))
private theorem pwalks_snd_m16_r256 :
    RkmSegWalksSound 16 256 [2, 4, 8, 16, 28, 28, 28, 28]
      [12, 16, 30, 53, 56, 75, 17, 4] pwalks_m16_r256 := by
  dsimp only [RkmSegWalksSound, pwalks_m16_r256]
  exact ⟨bSeg_mk pdim_m16_r256_l2 pwalk_m16_r256_0,
    ⟨bSeg_mk pdim_m16_r256_l4 pwalk_m16_r256_1,
    ⟨bSeg_mk pdim_m16_r256_l8 pwalk_m16_r256_2,
    ⟨bSeg_mk pdim_m16_r256_l16 pwalk_m16_r256_3,
    ⟨bSeg_mk pdim_m16_r256_l28 pwalk_m16_r256_4,
    ⟨bSeg_mk pdim_m16_r256_l28 pwalk_m16_r256_5,
    ⟨bSeg_mk pdim_m16_r256_l28 pwalk_m16_r256_6,
    ⟨bSeg_mk pdim_m16_r256_l28 pwalk_m16_r256_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 16, r = 256)`. -/
theorem rkmTrajPack_m16_r256 :
    rkmEvalT16Lo12 16 28 256 [2, 4, 8, 16, 28, 28, 28, 28]
      [16586577, 11809602, 12105415, 12346954, 8876427, 11909414, 2703894, 516844]
      [12, 16, 30, 53, 56, 75, 17, 4]
      rkmMasksPack_m16_r256 = rkmRowPack_m16_r256 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m16_r256
    (rkmHd
      (rkmTl (rkmTl (rkmTl
      pdk_1))))

private theorem pwalk_m32_r256_0 :
    bWalkOk 12 33 phb_m32_r256_0 1 pvn_m8_r256_0_0 33 pvn_m32_r256_0_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_3)))
private theorem pwalk_m32_r256_1 :
    bWalkOk 16 65 phb_m32_r256_1 33 pvn_m32_r256_0_1 65 pvn_m32_r256_1_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_11)))
private theorem pw_m32_r256_2_0 :
    bWalkOk 16 129 phb_m32_r256_2 65 pvn_m32_r256_2_0 129 pvn_m32_r256_2_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_1))
private theorem pwalk_m32_r256_2 :
    bWalkOk 29 129 phb_m32_r256_2 65 pvn_m32_r256_2_0 129 pvn_m32_r256_2_2 :=
  bChn (rfl : 16 + 13 = 29) pw_m32_r256_2_0
    (rkmHd
      (rkmTl
      pdk_2))
private theorem pw_m32_r256_3_0 :
    bWalkOk 21 257 phb_m32_r256_3 129 pvn_m32_r256_3_0 257 pvn_m32_r256_3_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_23))
private theorem pw_m32_r256_3_1 :
    bWalkOk 38 257 phb_m32_r256_3 129 pvn_m32_r256_3_0 257 pvn_m32_r256_3_2 :=
  bChn (rfl : 21 + 17 = 38) pw_m32_r256_3_0
    (rkmHd
      (rkmTl
      pdk_21))
private theorem pwalk_m32_r256_3 :
    bWalkOk 53 257 phb_m32_r256_3 129 pvn_m32_r256_3_0 257 pvn_m32_r256_3_3 :=
  bChn (rfl : 38 + 15 = 53) pw_m32_r256_3_1
    (rkmHd
      (rkmTl
      pdk_18))
private theorem pw_m32_r256_4_0 :
    bWalkOk 16 257 phb_m32_r256_4 257 pvn_m32_r256_4_0 257 pvn_m32_r256_4_1 :=
  bWalk1
    (rkmHd
      pdk_16)
private theorem pw_m32_r256_4_1 :
    bWalkOk 30 257 phb_m32_r256_4 257 pvn_m32_r256_4_0 257 pvn_m32_r256_4_2 :=
  bChn (rfl : 16 + 14 = 30) pw_m32_r256_4_0
    (rkmHd
      pdk_20)
private theorem pw_m32_r256_4_2 :
    bWalkOk 43 257 phb_m32_r256_4 257 pvn_m32_r256_4_0 257 pvn_m32_r256_4_3 :=
  bChn (rfl : 30 + 13 = 43) pw_m32_r256_4_1
    (rkmHd
      pdk_22)
private theorem pwalk_m32_r256_4 :
    bWalkOk 56 257 phb_m32_r256_4 257 pvn_m32_r256_4_0 257 pvn_m32_r256_4_4 :=
  bChn (rfl : 43 + 13 = 56) pw_m32_r256_4_2
    (rkmHd
      pdk_18)
private theorem pw_m32_r256_5_0 :
    bWalkOk 13 257 phb_m32_r256_5 257 pvn_m32_r256_5_0 257 pvn_m32_r256_5_1 :=
  bWalk1
    (rkmHd
      pdk_14)
private theorem pw_m32_r256_5_1 :
    bWalkOk 26 257 phb_m32_r256_5 257 pvn_m32_r256_5_0 257 pvn_m32_r256_5_2 :=
  bChn (rfl : 13 + 13 = 26) pw_m32_r256_5_0
    (rkmHd
      pdk_12)
private theorem pw_m32_r256_5_2 :
    bWalkOk 39 257 phb_m32_r256_5 257 pvn_m32_r256_5_0 257 pvn_m32_r256_5_3 :=
  bChn (rfl : 26 + 13 = 39) pw_m32_r256_5_1
    (rkmHd
      pdk_9)
private theorem pw_m32_r256_5_3 :
    bWalkOk 52 257 phb_m32_r256_5 257 pvn_m32_r256_5_0 257 pvn_m32_r256_5_4 :=
  bChn (rfl : 39 + 13 = 52) pw_m32_r256_5_2
    (rkmHd
      pdk_10)
private theorem pw_m32_r256_5_4 :
    bWalkOk 65 257 phb_m32_r256_5 257 pvn_m32_r256_5_0 257 pvn_m32_r256_5_5 :=
  bChn (rfl : 52 + 13 = 65) pw_m32_r256_5_3
    (rkmHd
      pdk_11)
private theorem pwalk_m32_r256_5 :
    bWalkOk 75 257 phb_m32_r256_5 257 pvn_m32_r256_5_0 257 pvn_m32_r256_5_6 :=
  bChn (rfl : 65 + 10 = 75) pw_m32_r256_5_4
    (rkmHd
      (rkmTl
      pdk_13))
private theorem pw_m32_r256_6_0 :
    bWalkOk 9 257 phb_m32_r256_6 257 pvn_m32_r256_6_0 257 pvn_m32_r256_6_1 :=
  bWalk1
    (rkmHd
      (rkmTl
      pdk_5))
private theorem pwalk_m32_r256_6 :
    bWalkOk 18 257 phb_m32_r256_6 257 pvn_m32_r256_6_0 257 pvn_m32_r256_6_2 :=
  bChn (rfl : 9 + 9 = 18) pw_m32_r256_6_0
    (rkmHd
      (rkmTl
      pdk_6))
private theorem pwalk_m32_r256_7 :
    bWalkOk 4 257 phb_m32_r256_7 257 pvn_m32_r256_7_0 257 pvn_m32_r256_7_1 :=
  bWalk1
    (rkmHd
      (rkmTl (rkmTl
      pdk_0)))
private theorem pwalks_snd_m32_r256 :
    RkmSegWalksSound 32 256 [1, 2, 4, 8, 14, 14, 14, 14]
      [12, 16, 29, 53, 56, 75, 18, 4] pwalks_m32_r256 := by
  dsimp only [RkmSegWalksSound, pwalks_m32_r256]
  exact ⟨bSeg_mk pdim_m32_r256_l1 pwalk_m32_r256_0,
    ⟨bSeg_mk pdim_m32_r256_l2 pwalk_m32_r256_1,
    ⟨bSeg_mk pdim_m32_r256_l4 pwalk_m32_r256_2,
    ⟨bSeg_mk pdim_m32_r256_l8 pwalk_m32_r256_3,
    ⟨bSeg_mk pdim_m32_r256_l14 pwalk_m32_r256_4,
    ⟨bSeg_mk pdim_m32_r256_l14 pwalk_m32_r256_5,
    ⟨bSeg_mk pdim_m32_r256_l14 pwalk_m32_r256_6,
    ⟨bSeg_mk pdim_m32_r256_l14 pwalk_m32_r256_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Multi-segment trajectory soundness for `(m = 32, r = 256)`. -/
theorem rkmTrajPack_m32_r256 :
    rkmEvalT16Lo12 32 14 256 [1, 2, 4, 8, 14, 14, 14, 14]
      [16813182, 11802523, 11889838, 12403318, 8884799, 11915996, 2742203, 635206]
      [12, 16, 29, 53, 56, 75, 18, 4]
      rkmMasksPack_m32_r256 = rkmRowPack_m32_r256 :=
  rkmCheckRowFromWalks_sound pwalks_snd_m32_r256
    (rkmHd
      (rkmTl (rkmTl (rkmTl
      pdk_3))))

/-- Module export witness for `FindAllJohnsonRampKickMuxLowHiT5`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxLowHiT5 : True := trivial

end

end QuantumComputation.Specs.DickeSol
