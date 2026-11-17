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
# High-`m` Coupled Walk & Trajectory Part `3` (`FindAllJohnsonRampKickMuxHi256T3`)

Certifies `(256, 256)` (`71446` coords) and `(256, 512)` `s = 0..1` (`66988` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Zigzag `< 2 ^ 60` orbital vector decoder (`FindAllJohnsonRampKickMuxHi256T3`). -/
def rkmZigHi256T3 : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: rkmZigHi256T3 ws
/-- Prepends `g` `false` entries followed by `true` (`FindAllJohnsonRampKickMuxHi256T3`). -/
def rkmPrependGapHi256T3 : ℕ → List Bool → List Bool
  | 0, acc => true :: acc
  | g + 1, acc => false :: rkmPrependGapHi256T3 g acc
/-- Reconstructs mask bits from gap counts (`FindAllJohnsonRampKickMuxHi256T3`). -/
def rkmGapsToMaskHi256T3 : List ℕ → List Bool
  | [] => []
  | g :: gs => rkmPrependGapHi256T3 g (rkmGapsToMaskHi256T3 gs)
/-- Mask segment `0` for `(m = 256, r = 256)`. -/
def rkmMkHiHiB_m256_r256_s0 : List Bool :=
  rkmGapsToMaskHi256T3
    [1, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 89]
/-- Mask segment `1` for `(m = 256, r = 256)`. -/
def rkmMkHiHiB_m256_r256_s1 : List Bool :=
  rkmGapsToMaskHi256T3
    [4, 0, 0, 1, 0, 3, 2, 14, 0, 0, 0, 0, 2, 0, 0, 11, 6, 0, 0, 0, 0, 4, 9, 0, 4, 0, 0, 0, 0, 7, 13,
     0, 0]
/-- Mask segment `2` for `(m = 256, r = 256)`. -/
def rkmMkHiHiB_m256_r256_s2 : List Bool :=
  rkmGapsToMaskHi256T3
    [1, 1, 7, 3, 0, 1, 1, 0, 2, 1, 0, 2, 1, 1, 4, 4, 2, 1, 1, 3, 1, 3, 0, 1, 1, 1, 1, 0, 0, 1, 3, 1,
     1, 2, 11, 6, 2, 12, 7, 2, 0, 1, 0, 0, 0, 3, 0, 7, 0, 0, 2, 8, 0, 0, 3, 2, 5, 14, 0, 0, 0, 0, 0,
     0, 34, 0, 0, 0, 0, 0]
/-- Mask segment `3` for `(m = 256, r = 256)`. -/
def rkmMkHiHiB_m256_r256_s3 : List Bool :=
  rkmGapsToMaskHi256T3
    [2, 0, 1, 0, 3, 4, 0, 0, 0, 1, 0, 0, 2, 1, 1, 2, 0, 2, 0, 2, 0, 0, 3, 0, 1, 0, 1, 0, 0, 11, 0,
     1, 0, 0, 0, 2, 0, 2, 2, 3, 3, 3, 0, 4, 1, 2, 0, 3, 1, 1, 0, 2, 0, 1, 0, 0, 4, 0, 1, 0, 3, 0, 0,
     4, 1, 2, 9, 3, 2, 3, 2, 2, 2, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 2, 1, 1, 0, 1, 0, 0,
     0, 1, 0, 1, 1, 3, 2, 3, 0, 0, 2, 0, 0, 0, 0, 0]
/-- Mask segment `4` for `(m = 256, r = 256)`. -/
def rkmMkHiHiB_m256_r256_s4 : List Bool :=
  rkmGapsToMaskHi256T3
    [2, 0, 0, 1, 0, 1, 0, 0, 1, 4, 1, 3, 2, 0, 0, 0, 0, 5, 0, 0, 0, 0, 2, 1, 0, 0, 0, 1, 4, 0, 0, 1,
     3, 2, 2, 1, 0, 0, 1, 0, 0, 2, 3, 2, 0, 1, 0, 0, 0, 8, 4, 0, 2, 3, 0, 1, 0, 0, 0, 3, 3, 0, 0, 0,
     1, 1, 1, 9, 0, 1, 0, 2, 1, 1, 0, 1, 0, 3, 1, 2, 0, 0, 8, 0, 0, 0, 7, 0, 4, 0, 7, 4, 5, 6, 0, 1,
     1, 1, 0, 2, 4, 0, 3, 0, 0]
/-- Mask segment `5` for `(m = 256, r = 256)`. -/
def rkmMkHiHiB_m256_r256_s5 : List Bool :=
  rkmGapsToMaskHi256T3
    [1, 1, 2, 0, 0, 0, 0, 1, 5, 2, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 2, 2, 0, 4,
     3, 4, 7, 0, 0, 4, 1, 3, 8, 0, 0, 0, 1, 1, 6, 1, 1, 1, 0, 1, 0, 3, 0, 1, 1, 8, 1, 0, 0, 0, 0, 1,
     1, 3, 1, 0, 4, 0, 1, 0, 0, 0, 1, 0, 0, 11, 8, 5, 1, 4, 1, 0, 0, 0, 0, 1, 0, 6, 1, 1, 0, 1, 0,
     0, 1, 0, 1, 1, 1, 2, 0, 1, 2, 0, 0]
/-- Mask segment `6` for `(m = 256, r = 256)`. -/
def rkmMkHiHiB_m256_r256_s6 : List Bool :=
  rkmGapsToMaskHi256T3
    [4, 0, 0, 0, 0, 1, 0, 0, 2, 0, 4, 0, 4, 0, 0, 0, 0, 0, 3, 5, 14, 1, 0, 7, 4, 3, 0, 6, 1, 9, 5,
     0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 1, 3, 0, 1, 2, 0, 0, 0, 1, 0, 2, 1, 0, 0, 0,
     0, 0, 0, 3, 1, 8, 4, 0, 0, 0, 1, 0, 2, 0, 1, 0, 5, 0, 2, 0, 2, 0, 2, 0, 0, 2, 0, 1, 0, 7, 0, 2,
     3, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]
/-- Prefix-kick masks for `(m = 256, r = 256)`. -/
def rkmMasksHiHiB_m256_r256 : List (List Bool) :=
  [rkmMkHiHiB_m256_r256_s0, rkmMkHiHiB_m256_r256_s1, rkmMkHiHiB_m256_r256_s2,
   rkmMkHiHiB_m256_r256_s3, rkmMkHiHiB_m256_r256_s4, rkmMkHiHiB_m256_r256_s5,
   rkmMkHiHiB_m256_r256_s6, []]
/-- Part `0` of `rkmRowHiHiB_m256_r256`. -/
def rkmRowHiHiB_m256_r256_p0 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 6, 0, 0, 0, 0, 0, 0, 0, 8, 22, 1, 0, 0, 0, 0, 0, 0, 0, 11,
   15, 10, 0, 0, 26, 3, 0, 0, 0, 0, 8, 36, 3, 0, 0, 0, 24, 10, 21, 4, 15, 27, 34, 25, 18, 0, 42, 80,
   4, 0, 0, 73, 9, 1, 0, 0, 9, 6, 2, 28, 26, 27, 0, 0, 0, 18, 6, 58, 0, 61, 95, 9, 11, 0, 120, 53,
   78, 1, 52, 34, 80, 54, 44, 207, 50, 67, 257, 22, 47, 39, 0, 0, 0, 155, 413, 560, 42, 17, 405, 20,
   73, 216, 107, 314, 496, 4, 373, 18, 11, 4528, 477, 1615, 248, 555, 475, 11998]
/-- Part `1` of `rkmRowHiHiB_m256_r256`. -/
def rkmRowHiHiB_m256_r256_p1 : List ℕ :=
  [44, 18, 15, 46, 23, 41, 3, 16, 0, 46, 36, 34, 0, 37, 44, 28, 0, 6, 1, 35, 54, 9, 0, 0, 0, 0, 8,
   0, 0, 19, 25, 256, 53, 287, 0, 0, 7, 53, 56, 119, 67, 56, 109, 155, 6, 39, 448, 286, 23, 698,
   433, 18, 101, 41, 425, 5426, 405, 633, 489, 13951, 1025, 18549, 104881, 503, 141, 11, 51, 169,
   14, 12, 4, 41, 3, 0, 105, 78, 166, 28, 5, 120, 396, 340, 368, 181, 1262, 0, 742, 416, 1483, 3145,
   3099, 573, 397, 1834, 1860, 77927, 30126, 16985, 73097, 0, 16159, 53387, 51867, 17193, 6320,
   358492, 8279, 416957, 123045, 1994015, 12792745, 71882, 11410332, 13417563, 668987, 13549921,
   275924950, 73238791, 34536600, 48760622, 488768546, 108850822, 924643, 951474093, 8027973870,
   2243982755, 2287910408, 985402242541]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 256)`. -/
def rkmRowHiHiB_m256_r256 : List ℕ :=
  rkmRowHiHiB_m256_r256_p0 ++ rkmRowHiHiB_m256_r256_p1
/-- Quantized generator list for `m256_r512_s0_c0`. -/
def rkmHbHiHiB_m256_r512_s0_c0 : List ℤ :=
  altBuildHbFrom 256 512 146276156626 0 256
/-- Input orbital vector for `m256_r512_s0_c0`. -/
def rkmViHiHiB_m256_r512_s0_c0 : List ℤ := [rkmP 1000000000000000]
/-- Output orbital vector for `m256_r512_s0_c0`. -/
def rkmVoHiHiB_m256_r512_s0_c0 : List ℤ := rkmZigHi256T3
  [4,8,4,4,14,38,66,210,746,2468,7906,24110,70264,196080,525576,1356310,3377230,8129720,18952042,
   42851598,94103408,200960278,417801438,846503736,1672989530,3228014938,6085534770,11217588288,
   20231635446,35724444190,61795432702,104770762948,174195815866,284155659084,454977856088,
   715356193734,1104904375798,1677102825546,2502538239572,3672255486182,5300948977442,7529623571248,
   10527265007198,14490991820486,19644131661548,26231692074892,34512793478200,44749809014800,
   57194212075548,72069456489776,89551583395278,109748627794668,132680243027472,158259224680198,
   186276750378980,216393120634940,248135565922310,280904274608044,313987216994960,346583637827698,
   377835328213096,406864046087944,432812813930926,454888358485314,472401728217060,484804163536892,
   491715605988380,492943788198108,488492591117470,478559212710246,463520575105232,443910217136220,
   420387597951238,393702215646624,364655188120030,334060944205024,302711450361046,271344992186006,
   240620996341634,211101779993024,183241513892742,157382136751240,133755505033662,112490730942666,
   93625463166594,77119796312868,62871540175036,50731715211938,40519337699418,32034788265688,
   25071294794416,19424283535842,14898545163114,11313316089732,8505485994934,6331211310886,
   4666246032910,3405302426922,2460732788308,1760787072336,1247656907396,875469929110,608353823336,
   418649801674,285322052132,192583569662,128739466056,85235671008,55892870360,36301489242,
   23352460320,14879478658,9390655110,5870335744,3634914336,2229433230,1354466380,815116024,
   485905262,286924638,167830468,97243972,55814278,31733648,17872582,9971202,5510630,3016794,
   1635980,878814,467618,246456,128654,66518,34050,17246,8640,4280,2086,994,464,204,82,30,8,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0]
/-- Quantized generator list for `m256_r512_s1_c0`. -/
def rkmHbHiHiB_m256_r512_s1_c0 : List ℤ :=
  altBuildHbFrom 512 512 83243932584 0 512
/-- Input orbital vector for `m256_r512_s1_c0`. -/
def rkmViHiHiB_m256_r512_s1_c0 : List ℤ := rkmZigHi256T3
  [4,8,4,4,14,38,66,210,746,2468,7906,24110,70264,196079,525576,1356310,3377229,8129720,18952042,
   42851598,94103407,200960278,417801437,846503735,1672989530,3228014938,6085534770,11217588288,
   20231635446,35724444190,61795432702,104770762948,174195815866,284155659084,454977856088,
   715356193734,1104904375798,1677102825546,2502538239572,3672255486182,5300948977442,7529623571248,
   10527265007198,14490991820486,19644131661548,26231692074892,34512793478200,44749809014800,
   57194212075548,72069456489776,89551583395278,109748627794668,132680243027472,158259224680198,
   186276750378980,216393120634940,248135565922310,280904274608044,313987216994960,346583637827698,
   377835328213096,406864046087944,432812813930926,454888358485314,472401728217060,484804163536892,
   491715605988380,492943788198108,488492591117470,478559212710246,463520575105232,443910217136220,
   420387597951238,393702215646624,364655188120030,334060944205024,302711450361046,271344992186006,
   240620996341634,211101779993024,183241513892742,157382136751240,133755505033662,112490730942666,
   93625463166594,77119796312868,62871540175036,50731715211938,40519337699418,32034788265688,
   25071294794416,19424283535842,14898545163114,11313316089732,8505485994934,6331211310886,
   4666246032910,3405302426922,2460732788308,1760787072336,1247656907396,875469929110,608353823336,
   418649801674,285322052132,192583569662,128739466056,85235671008,55892870360,36301489242,
   23352460320,14879478658,9390655110,5870335744,3634914336,2229433230,1354466380,815116024,
   485905262,286924638,167830468,97243972,55814278,31733648,17872582,9971202,5510630,3016794,
   1635980,878814,467618,246455,128654,66517,34050,17246,8639,4280,2086,994,464,204,82,30,8,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0]
/-- Output orbital vector for `m256_r512_s1_c0`. -/
def rkmVoHiHiB_m256_r512_s1_c0 : List ℤ := rkmZigHi256T3
  [460704,2114258,6673634,16667750,34765736,62129804,96164546,128811896,147051690,136833942,
   90008782,11489416,77719583,145327977,160605985,110468273,10334469,98006610,163522234,151296478,
   63228958,59044629,152682363,166834773,91026869,35362834,143998766,173145958,105431148,22930117,
   139107455,176564697,112877501,16439718,136763884,178775034,117512726,12045285,134884821,
   180354857,121938521,6773746,131605126,181434828,127915288,1699158,125280081,181764801,136520047,
   15198061,114238696,180511592,148020834,35068946,96538823,175929829,161578023,61970441,69914078,
   164999826,174759394,95342908,32162423,143253365,182824839,132440191,17786153,105300862,178047572,
   166754930,77892650,46696803,150122089,186201669,139763753,32265807,89248846,173158826,184779116,
   120172014,6612572,109971939,183921431,187210307,119407615,6740105,109034210,186524330,199034656,
   143030468,38331782,79838465,173334395,213180883,187864041,105926689,7768602,120458394,201170286,
   228821412,197122136,115243226,4223404,109222149,199301917,246768527,242642083,189192805,98196213,
   12439522,122566064,213631248,271822966,289763250,266643160,207356314,121037080,19107858,86781947,
   186322317,271446531,336828919,380040595,401196687,402215181,386083089,356260935,316030777,
   267746415,212184917,147992445,70879545,27714806,162549524,357314276,648794780,1093249246,
   1775727060,2823318974,4423962176,6852995944,10510036024,15969299432,24047498228,35894511158,
   53112905462,77913165024,113312440710,163385565628,233577479754,331085869284,465321837466,
   648454671518,896043755146,1227755948956,1668160277580,2247583672074,3003001795544,3978927568584,
   5228247235460,6812940529210,8804608771568,11284723634330,14344500979200,18084300236928,
   22612451963716,28043426089156,34495272018632,42086289767794,50930928832876,61134957982988,
   72790002993102,85967607754380,100713033501020,117039066743392,134920154113314,154287216652898,
   175023512180314,196961908066244,219883895242608,243520616506090,267556099102720,291632776203120,
   315359259383658,338320191839634,360087878595596,380235265123990,398349729228546,414047071681320,
   426985046264768,436875764651610,443496348182368,446697276042974,446407993290242,442639485352388,
   435483688431008,425109776482358,411757533317798,395728171291148,377373085762584,357081128913932,
   335265042203720,312347701584866,288748804509052,264872566558714,241096904564846,217764470372386,
   195175774121368,173584507356040,153195053217138,134162060939136,116591870677086,100545506156794,
   86042908552048,73068065171498,61574689106718,51492127732692,42731214727386,35189827498466,
   28757964955406,23322215163004,18769534886526,14990310496614,11880710110902,9344369028866,
   7293474074018,5649327663458,4342480067834,3312519539544,2507606102982,1883827192570,
   1404443303590,1039080553300,762915506356,555886551980,401956065424,288438877582,205405371654,
   145161845018,101806530244,70856707826,48940468514,33545688396,22818461254,15403404682,
   10318760054,6859909286,4525731260,2963041106,1925144108,1241258388,794198750,504261812,317710104,
   198626744,123212472,75832376,46302490,28045566,16849574,10039860,5932334,3475554,2018662,1162208,
   663160,374982,210084,116600,64088,34872,18782,10008,5266,2730,1390,688,328,146,58,18,2,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi256T3`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi256T3 : (0 : ℕ) = 0 := rfl
end
public section
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem bZeroMul (z : ℕ) : 0 = Nat.mul 0 z := by rw [Nat.mul_eq]; ring
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs
  | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uConsPair (b bz : ℕ) (ps : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  match Nat.add 1 b, Nat.add 1 bz with
  | 0, _ => ps
  | _, 0 => ps
  | vb + 1, vbz + 1 => match ps with | [] => [(vb, vbz)] | h :: t => (vb, vbz) :: h :: t
private theorem uConsPair_eq (b bz : ℕ) (ps : List (ℕ × ℕ)) :
    uConsPair b bz ps = (b, bz) :: ps := by
  unfold uConsPair; rw [n1a, n1a]; cases ps <;> rfl
private def uToPairs (z : ℕ) : List ℤ → Option (List (ℕ × ℕ))
  | [] => some []
  | x :: xs => match x with
    | Int.ofNat n => match uToPairs z xs with
      | some ps => some (uConsPair n (Nat.mul n z) ps)
      | none => none
    | Int.negSucc _ => none
private def uOfPairs : List (ℕ × ℕ) → List ℤ
  | [] => []
  | (n, _) :: ps => Int.ofNat n :: uOfPairs ps
private def uPairsOk (z : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True
  | (b, bz) :: ps => bz = Nat.mul b z ∧ uPairsOk z ps
private theorem uToPairs_sound (z : ℕ) :
    ∀ (hb : List ℤ) (ps : List (ℕ × ℕ)),
      uToPairs z hb = some ps → hb = uOfPairs ps ∧ uPairsOk z ps
  | [], ps, h => by injection h with h'; subst h'; exact ⟨rfl, trivial⟩
  | Int.negSucc _ :: _, _, h => by dsimp only [uToPairs] at h; cases h
  | Int.ofNat n :: xs, ps, h => by
    dsimp only [uToPairs] at h; revert h; cases hxs : uToPairs z xs with
    | none => intro h; dsimp only at h; cases h
    | some qs =>
      intro h; dsimp only at h; injection h with h'; subst h'
      have hp := uToPairs_sound z xs qs hxs
      rw [uConsPair_eq]
      exact ⟨by rw [uOfPairs, hp.1], ⟨rfl, hp.2⟩⟩
private def bConsZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
  | Int.ofNat v => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t
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
private theorem bZero_eq (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bMul0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZero_eq]; rfl
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
    unfold bEnc1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h
    revert h; cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w =>
      intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem bEnc_sound (z : ℕ) :
    ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us → bDec z us = xs
  | [], us, h => by injection h with h'; subst h'; rfl
  | x :: xs, us, h => by
    dsimp only [bEnc] at h; revert h; cases hx : bEnc1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bEnc z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uConsNat_eq, bDec_cons, bEnc1_sound z x u hx, bEnc_sound z xs ws hxs]
private def zTdiv (x : ℤ) (d : ℕ) : ℤ :=
  match x with | Int.ofNat m => Int.ofNat (m / d) | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTdivNat_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by dsimp only [muxRawIntTdivNat, zTdiv]; rw [bNeg_eq, ndiv, Nat.add_eq]
private theorem bSubNatTdiv_eq (m n d : ℕ) :
    rkmUltraSubNatTdiv m n d = zTdiv ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    dsimp only
    have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTdiv]; rw [bNeg_eq]
private theorem bSubTdiv_eq (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTdiv (a - b) d := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => exact bSubNatTdiv_eq m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
      rw [hm]; rfl
  | negSucc m => cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTdiv]
      rw [bNeg_eq, ndiv, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [bSubNatTdiv_eq, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTdiv t d) (by simp only [Int.negSucc_eq]; omega)
private theorem bMul_eq : ∀ (a b : ℤ), muxRawIntMul a b = a * b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [muxRawIntMul]
    rw [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; push_cast; ring
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [muxRawIntMul]
    rw [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq, Nat.add_eq, Nat.add_eq, Int.ofNat_eq_natCast]
    simp only [Int.negSucc_eq]; push_cast; ring
private theorem bForcedAdd_eq : ∀ (a b : ℤ), rkmForcedIntAdd a b = a + b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bOfNatF_eq, Nat.add_eq]
    simp only [Int.ofNat_eq_natCast]; omega
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bNegSuccF_eq, Nat.add_eq, Nat.add_eq]
    simp only [Int.negSucc_eq]; omega
private theorem bAddCons_eq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bForcedAdd_eq]; cases a + b <;> cases xs <;> rfl
private def bStepVal (v P Q d : ℕ) : ℕ := match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSubNatTdiv_eq]; unfold bStepVal at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv; cases h : Q - P with
  | zero => intro _; dsimp only; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k => intro hv; dsimp only at hv ⊢; rw [bNeg_eq]; omega
private abbrev bCellVal (d b0 bz0 c0 b bz v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) bz) (Nat.add (Nat.mul b c1) bz0) d
private theorem bCell_hb (z d b0 bz0 c0 b bz v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hbz0 : bz0 = Nat.mul b0 z) (hbz : bz = Nat.mul b z)
    (hv : 0 < bCellVal d b0 bz0 c0 b bz v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCellVal d b0 bz0 c0 b bz v c1) rest) = rkmUltraAddCons ((v : ℤ) - (z : ℤ))
      (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bAddCons_eq, bSubTdiv_eq, bMul_eq, bMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) bz : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) bz0 : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    rw [hbz0, hbz]; simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCellVal at hv ⊢; rw [bStepVal_eq z v _ _ d hv, hpq]
private theorem bCell_nil (z d b0 bz0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hbz0 : bz0 = Nat.mul b0 z)
    (hv : 0 < bStepVal v (Nat.mul b0 c0) bz0 d) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bStepVal v (Nat.mul b0 c0) bz0 d) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bAddCons_eq, bTdivNat_eq, bMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - (bz0 : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    rw [hbz0]; simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  rw [bStepVal_eq z v _ _ d hv, hpq]
private def bAllPos : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAllPos xs)
private theorem bAllPos_cons {x : ℕ} {xs : List ℕ} (h : bAllPos (x :: xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private theorem bAllPos_uCons {x : ℕ} {xs : List ℕ} (h : bAllPos (uConsNat x xs) = true) :
    0 < x ∧ bAllPos xs = true := by rw [uConsNat_eq] at h; exact bAllPos_cons h
private def bHeadOr (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTailN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem bHeadOr_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHeadOr z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq]
  | c :: cs => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | x :: xs => by unfold bTailN; rw [bDec_cons]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ) → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _, _ => []
  | rem + 1, b0, bz0, c0, bps, vs, cs => match bps with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) bz0 d)
        (bSlide z d rem 0 0 z [] (bTailN vs) (bTailN cs))
    | (b, bz) :: bR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal d b0 bz0 c0 b bz v (bHeadOr z cT)) (bSlide z d rem b bz c bR vT cT)
      | v :: vT, [] => uConsNat (bCellVal d b0 bz0 c0 b bz v z) (bSlide z d rem b bz z bR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal d b0 bz0 c0 b bz z (bHeadOr z cT)) (bSlide z d rem b bz c bR [] cT)
      | [], [] => uConsNat (bCellVal d b0 bz0 c0 b bz z z) (bSlide z d rem b bz z bR [] [])
private theorem bSlide_sound (z d : ℕ) :
    ∀ (rem b0 bz0 c0 : ℕ) (bps : List (ℕ × ℕ)) (vs cs : List ℕ),
      bz0 = Nat.mul b0 z → uPairsOk z bps →
      bAllPos (bSlide z d rem b0 bz0 c0 bps vs cs) = true →
      bDec z (bSlide z d rem b0 bz0 c0 bps vs cs) =
        rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (uOfPairs bps) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | rem + 1, b0, bz0, c0, bps, vs, cs, hbz0, hbps, h => by
    cases bps with
    | nil =>
      dsimp only [bSlide, uOfPairs, rkmUltraSlideLoopAux] at h ⊢; have hp := bAllPos_uCons h
      have hi := bSlide_sound z d rem 0 0 z [] (bTailN vs) (bTailN cs) (bZeroMul z) trivial hp.2
      rw [bMul0, uOfPairs, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 bz0 c0 (bHeadOr z vs) hbz0 hp.1 hi
      rw [bHeadOr_eq z vs] at hc; exact hc
    | cons bp bR =>
      cases bp with | mk b bz =>
      have hbz := hbps.1; have hbR := hbps.2
      cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSlide, uOfPairs] at h ⊢; rw [bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b bz z bR [] [] hbz hbR hp.2
          rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 bz0 c0 b bz z z hbz0 hbz hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfPairs] at h ⊢; rw [bDec_nil, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b bz c bR [] cT hbz hbR hp.2; rw [bDec_nil] at hi
          have hc := bCell_hb z d b0 bz0 c0 b bz z (bHeadOr z cT) hbz0 hbz hp.1 hi
          rw [bHeadOr_eq z cT, bZero_eq z] at hc; exact hc
      | cons v vT => cases cs with
        | nil =>
          dsimp only [bSlide, uOfPairs] at h ⊢; rw [bDec_cons z v vT, bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b bz z bR vT [] hbz hbR hp.2
          rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 bz0 c0 b bz v z hbz0 hbz hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfPairs] at h ⊢; rw [bDec_cons z v vT, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b bz c bR vT cT hbz hbR hp.2
          have hc := bCell_hb z d b0 bz0 c0 b bz v (bHeadOr z cT) hbz0 hbz hp.1 hi
          rw [bHeadOr_eq z cT] at hc; exact hc
private def bStg (z dg mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns cns : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlide z d nL 0 0 z bps vns cns) fun out => cond (bAllPos out) (some out) none
private theorem bStg_sound (z dg mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns cns out : List ℕ)
    (hbps : uPairsOk z bps) (h : bStg z dg mL cL bps vns cns = some out) :
    bDec z out = rkmUltraHornerStage dg mL cL (uOfPairs bps) (bDec z vns) (bDec z cns) := by
  unfold bStg at h; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq] at h
  revert h
  cases hp : bAllPos (bSlide z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 0 z bps vns cns) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]
    exact bSlide_sound z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 0 z bps vns cns
      (bZeroMul z) hbps hp
private def bBind (z dg mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns cns : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL =>
    match bStg z dg mL cL bps vns cns with | none => none | some out => k nL out
private theorem bBind_sound {z dg mL cL : ℕ} {bps : List (ℕ × ℕ)} {vns cns out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (hbps : uPairsOk z bps) (h : bBind z dg mL cL bps vns cns kB = some out)
    (hk : ∀ (mid : List ℕ), kB (rkmNextLen mL cL) mid = some out →
      bDec z out = kU (rkmNextLen mL cL) (bDec z mid)) :
    bDec z out = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (uOfPairs bps) (bDec z vns) (bDec z cns)) (kU nL)) := by
  unfold bBind at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
  revert h; cases hs : bStg z dg mL cL bps vns cns with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h
    rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound z dg mL cL bps vns cns mid hbps hs]
    exact hk mid h
private def bStep (z mL c : ℕ) (bps : List (ℕ × ℕ)) (vns : List ℕ) : Option (List ℕ) :=
  bBind z 16 mL c bps vns vns fun l1 c1 => bBind z 15 mL l1 bps vns c1 fun l2 c2 =>
  bBind z 14 mL l2 bps vns c2 fun l3 c3 => bBind z 13 mL l3 bps vns c3 fun l4 c4 =>
  bBind z 12 mL l4 bps vns c4 fun l5 c5 => bBind z 11 mL l5 bps vns c5 fun l6 c6 =>
  bBind z 10 mL l6 bps vns c6 fun l7 c7 => bBind z 9 mL l7 bps vns c7 fun l8 c8 =>
  bBind z 8 mL l8 bps vns c8 fun l9 c9 => bBind z 7 mL l9 bps vns c9 fun la ca =>
  bBind z 6 mL la bps vns ca fun lb cb => bBind z 5 mL lb bps vns cb fun lc cc =>
  bBind z 4 mL lc bps vns cc fun ld cd => bBind z 3 mL ld bps vns cd fun le ce =>
  bBind z 2 mL le bps vns ce fun lf cf => bStg z 1 mL lf bps vns cf
private theorem bStep_sound (z mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns out : List ℕ)
    (hbps : uPairsOk z bps) (h : bStep z mL cL bps vns = some out) :
    bDec z out = rkmUltraHornerT16Step mL cL (uOfPairs bps) (bDec z vns) := by
  unfold bStep at h; unfold rkmUltraHornerT16Step
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bBind_sound hbps h fun _ h => ?_
  refine bBind_sound hbps h fun _ h => bStg_sound _ _ _ _ _ _ _ _ hbps h
private def bIter (z : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ) → List ℕ → Option (List ℕ)
  | 0, _, _, _, vns => some vns
  | k + 1, mL, cL, bps, vns => match bStep z mL cL bps vns with
    | none => none
    | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL bps vNext
private theorem bIter_sound (z : ℕ) : ∀ (k mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns out : List ℕ),
    uPairsOk z bps → bIter z k mL cL bps vns = some out →
    bDec z out = muxUltraIterFullT16Rkm k mL cL (uOfPairs bps) (bDec z vns)
  | 0, _, _, _, vns, out, _, h => by injection h with h'; subst h'; rfl
  | k + 1, mL, cL, bps, vns, out, hbps, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL cL bps vns with
    | none => intro h; dsimp only at h; cases h
    | some vNext =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bStep_sound z mL cL bps vns vNext hbps hs]
      exact bIter_sound z k mL (rkmNextLen16 mL cL) bps vNext out hbps h
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  let z := 100000000000000000
  match uToPairs z hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some bps => match bEnc z v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vns => match bIter z k mL cL bps vns with
      | none => muxUltraIterFullT16Rkm k mL cL hb v
      | some out => bDec z out
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; dsimp only; cases hh : uToPairs 100000000000000000 hb with
  | none => rfl
  | some bps => dsimp only; cases hv : bEnc 100000000000000000 v with
    | none => rfl
    | some vns => dsimp only; cases hi : bIter 100000000000000000 k mL cL bps vns with
      | none => rfl
      | some out =>
        dsimp only
        have hp := uToPairs_sound 100000000000000000 hb bps hh
        rw [bIter_sound 100000000000000000 k mL cL bps vns out hp.2 hi,
          ← hp.1, bEnc_sound 100000000000000000 v vns hv]
private def muxFastIterBSlideChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    fN (altIntLen inF) fun len0 => muxIntListEq (fIter steps maxLen len0 hbF inF) outF
private theorem muxFastIterBSlideChk_sound {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : muxFastIterBSlideChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold muxFastIterBSlideChk at h; dsimp only [fL, fN] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq] at h
  rw [rkmb_forceNat_eq, fIter_eq] at h
  have h2 : muxUltraIterFullT16HiChk steps 0 maxLen hb vecIn vecOut = true := by
    unfold muxUltraIterFullT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq]
    exact h
  exact muxUltraIterFullT16HiChk_sound h2
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true :=
  (rkmAllTrueF_cons h).2
private theorem rkmT2 {b0 b1 : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b0 :: b1 :: bs) = true) : rkmAllTrueF bs = true :=
  rkmTl (rkmTl h)
private theorem rkmT4 {b0 b1 b2 b3 : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b0 :: b1 :: b2 :: b3 :: bs) = true) : rkmAllTrueF bs = true :=
  rkmT2 (rkmT2 h)
private theorem rkmT8 {b0 b1 b2 b3 b4 b5 b6 b7 : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs) = true) :
    rkmAllTrueF bs = true := rkmT4 (rkmT4 h)
private theorem pdim_256_l1 :
    Nat.add (highdNatMin (Nat.mul 1 256) 256) 1 = 257 := by
  decide +kernel
private theorem pdim_256_l2 :
    Nat.add (highdNatMin (Nat.mul 2 256) 256) 1 = 257 := by
  decide +kernel
private def phb_256_0 : List ℤ :=
  altBuildHbFrom 256 256 236316500000 0 256
private def pvi_256_0 : List ℤ := [rkmP 1000000000000000]
private def pvo_256_0 : List ℤ := rkmZigHi256T3
  [6674,54152,309640,1439366,5768708,20587090,66769196,199586986,555563656,1451422534,3580989226,
   8385651456,18715022736,39945687444,81781878544,161010989212,305509892476,559769214136,
   992092319394,1703406834052,2837284073502,4590303922874,7221370688668,11058058849620,
   16497661543990,24000465633538,34073018247038,47239876861414,64003572329086,84794186171000,
   109911863342200,139467464500506,173328062645066,211074763567232,251980106085978,295010945057650,
   338860293721184,382008358706682,422809370354970,459597328698222,490801000987948,515056882288856,
   531308653914162,538883002631474,537534311906964,527454312458584,509246754908804,483870973078260,
   452561329142826,416731594999962,377874138404410,337463358622510,296871342880638,257301507283176,
   219743421645366,184949469924894,153431779778896,125476182615410,101168944134636,80431633511068,
   63059690851534,48760866142622,37190574191066,27982179705444,20771161116110,15212905070888,
   10994500794104,7841317058382,5519366226798,3834521025242,2629591484388,1780134447746,
   1189694399914,784992546356,511412433758,328987624844,208985460602,131100806070,81221472340,
   49697541492,30034388668,17928452520,10571246826,6157257808,3542774916,2013776864,1130853312,
   627397888,343902662,186250198,99664130,52695480,27530288,14212176,7249902,3654544,1820404,896064,
   435872,209510,99508,46694,21638,9900,4466,1980,862,362,144,52,14,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def phbv_r256_s0 : List ℤ := rkmZigHi256T3
  [241988096000000,340886039298792,415861179621520,478304596000000,532647116270466,581170262171622,
   625234689701194,665730382630582,703277904000000,738330808015030,771232791673700,802251881947026,
   831602027796468,859457347262000,885961873128136,911236424000000,935383574953224,958491334028368,
   980635914566050,1001883861556354,1022293707260876,1041917277751934,1060800736487478,
   1078985426979984,1096508560000000,1113403779072768,1129701629680506,1145429951532588,
   1160614208820422,1175277770066878,1189442146692042,1203127197525148,1216351305039900,
   1229131527964722,1241483734039820,1253422716000000,1264962293312272,1276115401757772,
   1286894172593984,1297310002747056,1307373617250978,1317095124959558,1326484068400150,
   1335549468508116,1344299864873084,1352743352037894,1360887612315564,1368739945525948,
   1376307296000000,1383596277153920,1390613193896606,1397364063100624,1403854632338530,
   1410090397061824,1416076616378798,1421818327569234,1427320359458128,1432587344756822,
   1437623731467944,1442433793440022,1447021640148532,1451391225771950,1455546357624382,
   1459490704000000,1463227801479008,1466761061739952,1470093777918788,1473229130551328,
   1476170193132160,1478919937320090,1481481237817386,1483856876947684,1486049548955122,
   1488061864045364,1489896352187336,1491555466692900,1493041587590268,1494357024805576,
   1495504021165926,1496484755236074,1497301344000000,1497955845397654,1498450260726474,
   1498786536916370,1498966568686394,1498992200590514,1498865228959498,1498587403745334,
   1498160430274134,1497585970913078,1496865646656540,1496001038636186,1494993689559484,
   1493845105080764,1492556755108710,1491130075053884,1489566467019614,1487867300939434,
   1486033915663960,1484067620000000,1481969693704414,1479741388435194,1477383928661942,
   1474898512537952,1472286312735804,1469548477248382,1466686130157052,1463700372368656,
   1460592282322872,1457362916671376,1454013310930238,1450544480106772,1446957419302142,
   1443253104290802,1439432492077922,1435496521435786,1431446113420152,1427282171867484,
   1423005583873946,1418617220256938,1414117936000000,1409508570681790,1404789948889858,
   1399962880619838,1395028161660748,1389986573966938,1384838886017286,1379585853162170,
   1374228217958716,1368766710494836,1363202048702486,1357534938660604,1351766074888146,
   1345896140627606,1339925808119412,1333855738867546,1327686583896754,1321418984001656,
   1315053569988062,1308590962906836,1302031774280534,1295376606323130,1288626052153086,
   1281780696000000,1274841113405066,1267807871415618,1260681528773898,1253462636100342,
   1246151736071510,1238749363592900,1231256045966806,1223672303055398,1215998647439192,
   1208235584571072,1200383612926026,1192443224146720,1184414903185078,1176299128439994,
   1168096371891290,1159807099230088,1151431769985652,1142970837648890,1134424749792564,
   1125793948188342,1117078868920810,1108279942498506,1099397593962092,1090432242989774,
   1081384304000000,1072254186251592,1063042293941348,1053749026299184,1044374777680942,
   1034919937658882,1025384891109960,1015770018301948,1006075694977468,996302292435994,
   986450177613888,976519713162524,966511257524568,956425165008456,946261785861118,936021466339016,
   925704548777542,915311371658794,904842269677826,894297573807370,883677611361096,872982706055452,
   862213178070104,851369344107048,840451517448400,829460008012904,818395122411224,807257164000000,
   796046432934758,784763226221668,773407837768180,761980558432594,750481676072570,738911475592612,
   727270238990564,715558245403108,703775771150346,691923089779440,680000472107358,668008186262736,
   655946497726910,643815669374084,631615961510706,619347631914056,607010935870046,594606126210282,
   582133453348388,569593165315614,556985507795744,544310724159328,531569055497246,518760740653618,
   505886016258098,492945116757528,479938274447002,466865719500344,453727680000000,440524381966370,
   427256049386606,413922904242856,400525166539992,387063054332828,373536783752836,359946569034376,
   346292622540448,332575154787970,318794374472616,304950488493200,291043701975610,277074218296350,
   263042239105626,248947964350054,234791592294958,220573319546276,206293341072092,191951850223784,
   177549038756822,163085096851192,148560213131488,133974574686640,119328367089336,104621774415084,
   89854979260980,75028162764142,60141504619856,45195183099398,30189375067580,15124256000000]
private def pvm_r256_s0_1 : List ℤ := rkmZigHi256T3
  [3831900947120,13896402463822,35492135636506,73716756806942,132060879423818,210748073695512,
   305768019407876,409043850907266,509762073125544,596482536311388,659403078582790,692153670090656,
   692703360977058,663271410761274,609418876363742,538672185442638,459068050829596,377933926282346,
   301082927190182,232461732417128,174183331654292,126819875994720,89821195533982,61947298981028,
   41640976759586,27305099235068,17479563484388,10931876352612,6683839573166,3997545174016,
   2340166775070,1341588398384,753578359728,414932807490,224056840826,118699508388,61718937824,
   31508339114,15798644790,7782924170,3768149180,1793503580,839431358,386447638,175035702,78018168,
   34229106,14784912,6288600,2634412,1087138,442012,177088,69920,27204,10428,3936,1454,524,182,58,
   14,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0]
private theorem dk_r256_s0_0 :
    muxFastIterBSlideChk 29 257 phbv_r256_s0
      pvi_256_0 pvm_r256_s0_1 = true := by
  decide +kernel
private theorem dk_r256_s0_1 :
    muxFastIterBSlideChk 29 257 phbv_r256_s0
      pvm_r256_s0_1 pvo_256_0 = true := by
  decide +kernel
private def phb_256_1 : List ℤ :=
  altBuildHbFrom 256 256 235962637681 0 256
private def pvi_256_1 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r256_s0 pvo_256_0
private def pvo_256_1 : List ℤ := rkmZigHi256T3
  [4430,33708,179170,767798,2812504,9090192,26441168,70149424,171370202,388184050,819546218,
   1618802994,2999690376,5223792698,8556618722,13182777416,19082312930,25890352194,32787122088,
   38484656184,41376570040,39884717040,32968556944,20673470588,4516639764,12511624447,26480350199,
   33561274589,31332310271,19895814151,2310756227,16006227162,28898819604,31651404068,22932173252,
   5646001338,13829592875,27923588021,30875350487,21242057067,2761598757,16961812936,29546832608,
   29449854250,16513271002,3771385651,22528950135,31381789903,26236949791,9236102935,12088427808,
   28140075466,31591692298,20749443718,384642688,20376584883,32160467753,29581109987,13677263151,
   8547592108,27255524016,34145988282,26106990802,6543834224,16151774189,32261714175,34898843631,
   22874268801,1106363055,21511563606,35807162296,36018561808,21996950504,875864553,23901898379,
   38443584219,39119269345,25645929287,2752305931,21665574000,39366049546,44515893550,35462492152,
   15036707912,10565775053,33829431053,48169769329,49703892093,38093817117,16349802811,10208984570,
   35440807240,53868176660,61799345366,57880254198,43053162340,20044980786,7408839707,35385474713,
   60462900771,80168536587,93157913335,99154106487,98714517411,92900599513,82912964603,69726491063,
   53725001477,34298254773,9328317643,25541249118,77991294720,160633858354,293326363576,
   506386049404,844877753524,1374087414726,2186175329376,3407812876296,5208337067548,7807615529130,
   11482427016276,16569780515822,23465295755742,32614645698028,44496220378108,59593700741390,
   78358181006074,101160832701918,128238760349172,159638460955280,195162888183568,234329211044200,
   276344628678494,320106816708456,364233640934906,407123780346444,447046165571132,482252159889376,
   511100802625000,532184824515066,544444046560376,547253482376930,540475979521506,524473246001420,
   500074035906168,468503368938926,431281159206360,390101868029750,346708342625158,302772724222556,
   259795377566720,219029633391470,181436326992668,147668278904836,118081544632336,92767849236352,
   71601308905510,54292314852012,40442140843112,29593156369744,21271167679460,15018075840600,
   10414506652716,7093189526966,4744586291012,3116613650732,2010331831146,1273278521868,
   791806473576,483417176038,289733176206,170455687054,98429234942,55782309318,31023243860,
   16929843328,9064595426,4761309498,2453226202,1239739770,614400478,298568888,142249542,66436848,
   30412638,13643238,5996882,2582248,1089052,449750,181816,71924,27822,10508,3862,1376,466,146,38,6,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0]
private def phbv_r256_s1 : List ℤ := rkmZigHi256T3
  [241625740985344,340375593670234,415238465585880,477588378666344,531849525988908,580300012922390,
   624298458006764,664733512344222,702224809738656,737225225239754,770077941190766,801050583216858,
   830356779910514,858170388585886,884635226351584,909871930897936,933982923703788,957056081025718,
   979167502081848,1000383632217232,1020762916046762,1040357102037960,1059212284523224,
   1077369745106910,1094866638839840,1111736558869160,1128010004938024,1143714775068392,
   1158876295321376,1173517899227622,1187661065995838,1201325624718476,1214529930343168,
   1227291016054460,1239624725832064,1251545830260024,1263068128111962,1274204535798868,
   1284967166412776,1295367399813982,1305415944976720,1315122895617714,1324497779975260,
   1333549605476692,1342286898924386,1350717742740346,1358849807734030,1366690382794476,
   1374246401854144,1381524468426246,1388530877978656,1395271638374224,1401752488579044,
   1407978915815682,1413956171317394,1419689284821096,1425183077921062,1430442176391576,
   1435471021574784,1440273880919522,1444854857747700,1449217900316776,1453366810239748,
   1457305250317856,1461036751835600,1464564721362848,1467892447104386,1471023104833466,
   1473959763442400,1476705390140204,1479262855324546,1481634937152786,1483824325834680,
   1485833627667344,1487665368831308,1489321998964826,1490805894532236,1492119362000770,
   1493264640839102,1494243906349788,1495059272346816,1495712793688560,1496206468675698,
   1496542241322796,1496722003511730,1496747597034418,1496620815531794,1496343406335448,
   1495917072217922,1495343473057154,1494624227420230,1493760914071214,1492755073407512,
   1491608208828870,1490321788042924,1488897244310836,1487335977636418,1485639355901848,
   1483808715952940,1481845364636680,1479750579793614,1477525611207484,1475171681514368,
   1472689987073432,1470081698801286,1467347962971800,1464489901983130,1461508615093614,
   1458405179128062,1455180649155914,1451836059142644,1448372422575694,1444790733066146,
   1441091964927328,1437277073731380,1433346996844860,1429302653944328,1425144947512840,
   1420874763318210,1416492970873872,1412000423883104,1407397960667374,1402686404579486,
   1397866564402180,1392939234732854,1387905196354952,1382765216596626,1377520049677184,
   1372170437041844,1366717107685276,1361160778464396,1355502154400858,1349741928973640,
   1343880784402140,1337919391920166,1331858412041162,1325698494815024,1319440280076836,
   1313084397687840,1306631467768932,1300082100926964,1293436898474156,1286696452640828,
   1279861346781744,1272932155576282,1265909445222670,1258793773626492,1251585690583672,
   1244285737958166,1236894449854500,1229412352785380,1221839965834530,1214177800814924,
   1206426362422578,1198586148386056,1190657649611838,1182641350325674,1174537728210100,
   1166347254538194,1158070394303744,1149707606347914,1141259343482552,1132726052610214,
   1124108174841064,1115406145606686,1106620394770972,1097751346738126,1088799420557922,
   1079765030028256,1070648583795122,1061450485450070,1052171133625206,1042810922085860,
   1033370239820944,1023849471131094,1014248995714668,1004569188751646,994810420985518,
   984973058803188,975057464312998,965063995420876,954993005904712,944844845486976,934619859905642,
   924318390983484,913940776695758,903487351236340,892958445082362,882354385057370,871675494393076,
   860922092789708,850094496475032,839193018262048,828217967605430,817169650656712,806048370318296,
   794854426296246,783588115151994,772249730352890,760839562321700,749357898485046,737805023320812,
   726181218404574,714486762455036,702721931378534,690886998312620,678982233668734,667007905174020,
   654964277912274,642851614364072,630670174446082,618420215549578,606101992578210,593715757984990,
   581261761808570,568740251708798,556151473001566,543495668693004,530773079512974,517983943947956,
   505128498273266,492206976584686,479219610829470,466166630836778,453048264347520,439864737043654,
   426616272576934,413303092597108,399925416779608,386483462852734,372977446624322,359407582007932,
   345774081048572,332077153947930,318317009089180,304493853061318,290607890683080,276659325026428,
   262648357439618,248575187569866,234440013385608,220243031198386,205984435684334,191664419905306,
   177283175329636,162840891852532,148337757816138,133773960029240,119149683786644,104465112888224,
   89720429657650,74915814960810,60051448223908,45127507451278,30144169242890,15101608811584]
private def pvm_r256_s1_1 : List ℤ := rkmZigHi256T3
  [66502420112,30148526986,34115885641,41777008791,8323680388,42823721978,17633778888,29457049407,
   36279920353,3300742908,37566361990,25065474704,17175459575,38610062199,15546605485,24698620348,
   37650029946,10334032124,27690556609,37555016451,10217876965,27071064012,39083190452,15407864854,
   22163535851,40912827075,25496074689,10896715332,39191099012,37935540174,8569302502,27491476967,
   45329348925,33421690677,160407088,34517083516,49489582534,37003359824,4206862652,31838621715,
   53644748977,51499745601,26792924671,10016388306,44755490762,65286245740,65326310624,45417426122,
   11448951478,28097412475,64932223297,92907407935,108808588011,112121207353,104141315367,
   86832276753,61720702779,28965800841,13408199156,70223326148,149953968372,265781884444,
   437032010320,691085068720,1065819207664,1612580883426,2399621085928,3515853083774,5074690005196,
   7217607471884,10116956168494,13977435489600,19035552046722,25556349160970,33826730320502,
   44144833291716,56805156884558,72079502193128,90194250799022,111305030936806,135470367038790,
   162626400375984,192565131560794,224918793677190,259152855112270,294569736857998,330324609664836,
   365453653941118,398914004400946,429633382998090,456566290800044,478752728810672,495374878366942,
   505807084482686,509654887145488,506779710556016,497307061764006,481617570346134,460321749748006,
   434220800319382,404256941942842,371457536967304,336877572567030,301544907446432,266412101454204,
   232317736466418,199959032039586,169876399862950,142449498252402,117903448242934,96323227090732,
   77673894139524,61824221000978,48571454754626,37665280303240,28829497213872,21780419073862,
   16241480354040,11953952214978,8683996610034,6226515777968,4406384006334,3077692792236,
   2121617710902,1443446153176,969209515948,642258405906,420017870476,271070189856,172639956952,
   108501404814,67290253240,41179337658,24865885718,14815360874,8709434304,5051520058,2890632864,
   1631871984,908833690,499309954,270598460,144654230,76272580,39665842,20344744,10290710,5132844,
   2524282,1223812,584794,275340,127696,58308,26196,11570,5016,2126,878,348,128,40,8,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private theorem dk_r256_s1_0 :
    muxFastIterBSlideChk 35 257 phbv_r256_s1
      pvi_256_1 pvm_r256_s1_1 = true := by
  decide +kernel
private theorem dk_r256_s1_1 :
    muxFastIterBSlideChk 34 257 phbv_r256_s1
      pvm_r256_s1_1 pvo_256_1 = true := by
  decide +kernel
private def phb_256_2 : List ℤ :=
  altBuildHbFrom 512 256 144961426229 0 256
private def pvi_256_2 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r256_s1 pvo_256_1
private def pvo_256_2 : List ℤ := rkmZigHi256T3
  [3225669104,11206934750,17855786843,7681361092,2940901151,11244735699,1585467887,7530029035,
   7533027893,653596928,14145678046,12168001681,10681009362,9040385834,11692171434,21074641903,
   12670212653,9363669270,1370904599,2250747531,5623004302,8808662506,6816195565,12366841324,
   15112747587,80441998,7580049427,6870283247,13034593582,31984401504,39086053639,26314169800,
   35954774151,36033868428,29345070593,12867182238,12442964419,6608855062,34606623988,30128708179,
   9211565492,16880772791,1810018329,20744897894,27127635895,21496145038,6652777438,20914233531,
   25871984400,11961932109,11224036731,18212696894,26885844019,965235247,25699327050,8891079557,
   15032602214,6037842860,38372668485,2091084636,20412480586,5521302301,9563882538,4700474747,
   24163617765,15801172686,14256485936,10057503163,19805149462,2162973112,45628356073,888853093,
   32012785858,16917968135,11716894023,31983990146,5083820756,15028155355,13480314278,1142259491,
   25527692411,9325005084,22489845370,12347748181,10561569449,4709540294,20527765893,17917788193,
   26603538554,19700407130,18379434471,3252967364,40565052878,30924106288,35115293402,69564119984,
   50010739326,5062562241,5422625066,46419598582,20056576348,25486432717,3895859535,27865233654,
   1158622097,29957535899,6175489947,5651980104,28751021645,39118854653,2595361459,7059255978,
   26931940903,32453766721,1697156389,10768324671,62437012001,67229609439,6644849541,30700932152,
   5273328482,14124247267,16563184568,44155997974,25209306414,1847637300,14624267528,25706658570,
   6038819485,40868369031,21919991479,23407926380,23545377034,19454207575,30900395897,16052304744,
   53346019304,19066604606,49003623201,66172734251,17228508697,30804972896,25885503152,7226931165,
   17914571545,5874940589,12890837593,52132603255,82302413697,62470172301,9288732549,21516152748,
   4038492506,27502278463,23083225985,21269176144,58271267394,43838590842,13621253231,62669017993,
   62449267041,21196501185,17368281526,20143741916,5457610861,24136312593,10275944647,27706558626,
   56914406066,51040740120,13638634112,25113681401,32722156449,1332415886,59164434756,108002751906,
   121642570598,94841712434,43172552862,8696016231,41236308105,48562592487,38172813693,24301499465,
   19806152701,30778459333,55509502833,86924967435,116327114661,136423564659,142705153737,
   133577913587,110657290205,80785239215,60148634627,78018404553,173298162105,372555639039,
   636120937803,762574114495,254180335059,1833638797392,7011695578312,17380130980586,35489455426142,
   63999300079336,105146721464574,160103487807772,228363662983644,307334136805222,392282791016014,
   476728170940032,553246451206960,614557316570698,654666466243464,669817022607190,659044642238242,
   624228704408506,569654283882646,501210163683052,425416873725114,348491395727074,275615978511178,
   210506150365628,155292391913638,110663328892650,76179223881088,50655749375814,32533443378290,
   20177145994746,12081097707244,6981148228588,3891749488154,2091939724192,1083654564602,
   540605279796,259527181762,119788207608,53104734230,22585812378,9203291536,3587496286,1335411352,
   473726078,159769676,51085878,15434874,4388974,1168832,289736,66314,13854,2592,414,50,2,0]
private def phbv_r256_s2 : List ℤ := rkmZigHi256T3
  [209926568953854,296011090379734,361472296519988,416161204642974,463905555312092,506674339666290,
   545640662209746,581571078129688,614999564051256,646316009535472,675815579458662,703728229418892,
   730237339386392,755492003680052,779615434415226,802710883831904,824865926852364,846155627342946,
   866644924726854,886390463746258,905442018578136,923843616225550,941634433444374,958849520704536,
   975520392348914,991675512037150,1007340695364910,1022539446333086,1037293240509712,
   1051621764877658,1065543122217588,1079074006246010,1092229852477244,1105024968809034,
   1117472649074192,1129585272204438,1141374389179332,1152850799555218,1164024619064930,
   1174905339533018,1185501882150836,1195822644991906,1205875545512984,1215668058674662,
   1225207251222600,1234499812593076,1243552082841636,1252370077939020,1260959512732360,
   1269325821830532,1277474178639164,1285409512742392,1293136525804020,1300659706139780,
   1307983342094338,1315111534340986,1322048207208480,1328797119127626,1335361872279990,
   1341745921522078,1347952582650504,1353985040066714,1359846353893806,1365539466592548,
   1371067209119034,1376432306662162,1381637383995414,1386684970474126,1391577504706430,
   1396317338923492,1400906743072250,1405347908651796,1409642952312626,1413793919236322,
   1417802786311638,1421671465121686,1425401804755572,1428995594456784,1432454566119588,
   1435780396643778,1438974710157296,1442039080115456,1444975031284862,1447784041619430,
   1450467544035402,1453026928091676,1455463541581330,1457778692039760,1459973648174454,
   1462049641221098,1464007866230282,1465849483288884,1467575618679808,1469187365983588,
   1470685787125058,1472071913368110,1473346746261322,1474511258537092,1475566394966670,
   1476513073173400,1477352184406266,1478084594275716,1478711143453624,1479232648339120,
   1479649901691880,1479963673234394,1480174710224630,1480283738000392,1480291460496628,
   1480198560736796,1480005701299424,1479713524760802,1479322654114796,1478833693170626,
   1478247226929436,1477563821940418,1476784026637190,1475908371655078,1474937370129932,
   1473871517979016,1472711294164508,1471457160940080,1470109564081006,1468668933098184,
   1467135681436460,1465510206657568,1463792890607970,1461984099571906,1460084184409814,
   1458093480682384,1456012308760376,1453840973920352,1451579766426420,1449228961598092,
   1446788819864266,1444259586803386,1441641493169742,1438934754905892,1436139573141106,
   1433256134175762,1430284609451534,1427225155507216,1424077913919988,1420843011231892,
   1417520558861228,1414110652998618,1410613374487334,1407028788687566,1403356945324172,
   1399597878317470,1395751605596558,1391818128894598,1387797433525472,1383689488141140,
   1379494244469010,1375211637028510,1370841582826068,1366383981027550,1361838712607240,
   1357205639972242,1352484606561238,1347675436416324,1342777933726634,1337791882342348,
   1332717045257514,1327553164060076,1322299958347326,1316957125104850,1311524338046930,
   1306001246916178,1300387476739992,1294682627041258,1288886271000518,1282997954566548,
   1277017195512138,1270943482431490,1264776273675464,1258514996220490,1252159044466690,
   1245707778960324,1239160525035276,1232516571367822,1225775168438442,1218935526893830,
   1211996815801712,1204958160790318,1197818642063684,1190577292283050,1183233094303774,
   1175784978756098,1168231821456970,1160572440638888,1152805593980286,1144929975420380,
   1136944211739688,1128846858885334,1120636398018146,1112311231255902,1103869677084368,
   1095309965404458,1086630232180278,1077828513648694,1068902740046316,1059850728804546,
   1050670177157140,1041358654097828,1031913591617456,1022332275140950,1012611833073652,
   1002749225354386,992741230898182,982584433795022,972275208111470,961809701119324,951183814748580,
   940393185030442,929433159258702,918298770553268,906984709456584,895485292129952,883794424640116,
   871905562733694,859811666384174,847505148258296,834977815079040,822220800652798,809224489067438,
   795978426241184,782471217590264,768690409059524,754622348089666,740252020228406,725562855963538,
   710536500869448,695152540180924,679388166247238,663217773694606,646612462120224,629539419129000,
   611961146540348,593834478123766,575109315838452,555726979251652,535618012810208,514699216073028,
   492869531349544,470004200718028,445946209348232,420493294925572,393377343469044,364229884537910,
   332520152337906,297433152896558,257596413620682,210332985149320,148730140734804]
private def pvm_r256_s2_1 : List ℤ := rkmZigHi256T3
  [2948228305,8472942022,8701295871,1645587449,9843087970,2157483933,7126645009,1631920551,
   11719254102,1939123205,5038135907,8266370889,10932068784,4636732074,4988227633,535355376,
   12427480121,7953567420,7235702908,9439268424,25331106679,13711144394,6839785665,3199813783,
   14513722616,485677245,2793440625,6547204279,8398553749,13901956390,681848566,9762028829,
   16096717622,2080899938,20456143467,6319875375,16108890308,941286163,1607917698,6521269521,
   15451948852,4395670547,14041492616,10164771497,22484547347,8559528969,9856960106,21894845118,
   4623892234,16452044909,21631290020,27135201642,31774637554,51944393054,22925253972,53846084498,
   32024356186,21479755974,8994900528,1774151472,870779016,15409047575,20017706653,13632329515,
   21691684229,18690551920,21785523519,2765720709,73976471709,9883729790,46277496067,27485911962,
   53360897929,6436862835,16995000567,55989920819,27402496798,20356044953,669372900,19002244298,
   9802115218,71825135424,20900341218,2580970187,30572962844,34346081197,21930048573,24257170278,
   32197308949,17393228243,29239225976,15593810481,12616188249,24050793352,7980812155,1844302121,
   30934829616,27313103091,64109847279,3013695421,10844235614,32356528011,10637075447,17264877372,
   32050768441,55807183879,9097174351,13229860211,78818507151,72079564289,10080865736,42536758688,
   16974925748,23403914432,48554494428,13254877170,49849928709,42548282847,19084257170,27742615040,
   34360966929,70090180783,26024170981,31809676516,29782328140,5666052859,1108092119,48974735570,
   76620892192,39099909956,22518789887,36655781175,12356921616,71247073744,82696720046,45601418702,
   8310838074,13239963958,55459849052,91532779862,81411452414,21416052656,56509308293,111538050183,
   121643480569,93333046623,51958293657,23851974317,22843576871,46998089839,83842537155,
   118616133229,140671326629,145899849159,135594306989,113298086761,80994746121,35096774221,
   38240906332,169571396818,415647972468,873010221776,1696086332980,3119179109756,5480222931242,
   9242392381390,15007782877674,23515936266164,35619558796654,52230990373580,74236254180654,
   102378855224504,137122339617718,178507796398254,226028339495792,278545381980292,334269781858166,
   390824090447880,445390717376336,494936604179028,536490675202908,567438973243850,585796664240824,
   590417592122612,581110809920548,558647915710642,524662229669022,481457433268640,431756069027256,
   378425055884444,324215312558436,271546377207492,222356419177712,178025735628144,139370190232726,
   106692027834664,79870178222536,58470712155024,41859933209980,29306604439356,20064799079850,
   13433746565500,8795051482608,5630404558636,3524334068726,2156861292824,1290451181428,
   754738869186,431463554940,241065509884,131618083238,70214372936,36593269126,18628159504,
   9260935724,4495439176,2130252326,985221258,444605478,195722400,84025022,35167972,14345456,
   5701070,2206508,831332,304758,108638,37628,12640,4106,1280,376,102,22,2,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0]
private theorem dk_r256_s2_0 :
    muxFastIterBSlideChk 31 257 phbv_r256_s2
      pvi_256_2 pvm_r256_s2_1 = true := by
  decide +kernel
private theorem dk_r256_s2_1 :
    muxFastIterBSlideChk 30 257 phbv_r256_s2
      pvm_r256_s2_1 pvo_256_2 = true := by
  decide +kernel
private def phb_256_3 : List ℤ :=
  altBuildHbFrom 512 256 145164704918 0 256
private def pvi_256_3 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r256_s2 pvo_256_2
private def pvo_256_3 : List ℤ := rkmZigHi256T3
  [778265816,3987356860,747693277,809710174,274108407,3576116173,5467412335,1156841626,4624155962,
   4489862929,1862025477,6861223434,2099048674,1641408742,683489513,3207612518,2575053302,
   2671931682,1460871202,3265060125,5514140709,7779498062,12946903046,1317250453,14974413157,
   3962558828,5658519710,18253147479,4577059102,11423844808,6841304579,12962642927,7445145582,
   12142265148,1018203672,7792484132,3171788816,2410554100,4850625948,2867008020,2391396133,
   1668143264,8052559898,5755504387,1433507375,10846660119,6766838776,3147148853,9272259022,
   14307710467,8871366903,627340426,9014336013,20724819695,8890127687,10300782258,985100779,
   13318917709,2222747001,1744523960,10792442392,13309388251,7557380731,12455014715,404025037,
   12697425527,4183488770,21803622859,18751530258,15348079499,5334225097,24433545351,7182778973,
   35797901024,7074896656,803117946,5396260617,8915815503,12458631173,4339360867,13727712502,
   48326603028,4523990463,8722025983,23783193510,18970180810,4244477605,17462988200,22147545700,
   27427581598,2131464951,33020952115,3671102257,15256536740,24549131251,900799629,58984536274,
   26942492094,48442802947,30872768885,1564510976,20857452252,14948401868,21181931969,22771533255,
   5935922800,15292689616,14414756698,73476364308,31521477702,39609751255,10668535140,63844911950,
   20808238036,5725479694,15162428052,34412677504,54082476892,11352360177,55746501552,15407526457,
   21360966550,82756955167,69165963970,16317443435,42654948594,7351543472,33823249530,50128797486,
   50895100621,48016098982,24000246117,60519120082,1151054182,22414941625,23878237418,37268948005,
   76797476444,30221751701,23539940391,34755214224,40308103893,24829444456,29264773147,20790517024,
   33697926754,48430774199,39198890146,32622132217,9893705205,59937928008,43882289527,27637597352,
   5099802354,41126555511,47515105014,37810416525,3807004529,45580673736,57200106551,43374555174,
   23399708130,66911970275,49835224298,7623315546,38512122853,83582482084,55838535863,723505337,
   28640973174,73779054869,100227185479,157097327912,124799184425,89262420188,53032919955,
   55456752512,74537925279,261883829046,193621525641,134350414256,75182062368,2590828924,
   19206704301,50382496738,30621304698,127281772095,222924973270,182360174615,35926445731,
   153047069926,10869964017,81813720141,110616851747,118336896990,212414410167,13947531297,
   171949293520,200028053425,35361572026,94910883998,16316626714,115383657295,41411595811,
   288882261806,138415461233,137336959423,220157075054,85232303551,125975039455,38100640119,
   62362784266,52774520932,265103886425,88424966004,228923437444,338590980411,217381593365,
   117823061354,139304008350,28706929752,320806949025,60786574085,322908732808,146591492171,
   256592057995,124093805018,126644377042,105594913174,108110973089,351801931583,73146543212,
   302672207120,177718869060,418569544856,138574476739,1487694271741,779952036063,2690130219888,
   4793984250148,423160907489,11873952398517,13693261549143,9985011399588,43147370309278,
   35968140142770,43535546124351,147608504542673,149730701058115,61947389672696,465739557339274,
   884409665361562,1102723096906100,1023503104675264,724034851947156,378296216740734,
   128279853944354]
private def phbv_r256_s3 : List ℤ := rkmZigHi256T3
  [210220947940274,296426185263574,361979187328514,416744785436108,464556087771360,507384846579726,
   546405811404014,582386612367988,615861974889560,647222335269952,676763272293728,704715064024552,
   731261347585476,756551426369612,780708685272056,803836521322898,826022632250298,847342187182282,
   867860216606286,887633444697120,906711715429844,925139117546368,942954882739938,960194110631578,
   976888359756576,993066133689022,1008753284225664,1023973348326938,1038747831675958,
   1053096448862558,1067037328052838,1080587186372818,1093761480981972,1106574539841930,
   1119039675427384,1131169284028968,1142974932824122,1154467436513356,1165656925014746,
   1176552903463178,1187164305560150,1197499541155762,1207566538809378,1217372783963692,
   1226925353274028,1236230945557222,1245295909759454,1254126270287626,1262727750002774,
   1271105791134696,1279265574343666,1287212036126548,1294949884740266,1302483614794498,
   1309817520647430,1316955708722710,1323902108852160,1330660484737014,1337234443610164,
   1343627445172840,1349842809871382,1355883726572706,1361753259691106,1367454355813548,
   1372989849865962,1378362470858762,1383574847246144,1388629511930338,1393528906939130,
   1398275387802206,1402871227649638,1407318621053648,1411619687632900,1415776475436924,
   1419790964126656,1423665067965812,1427400638636464,1430999467891150,1434463290052760,
   1437793784372598,1440992577256112,1444061244365066,1447001312604234,1449814262000060,
   1452501527478160,1455064500546002,1457504530886668,1459822927869102,1462020961979898,
   1464099866181294,1466060837199696,1467905036748766,1469633592690786,1471247600139816,
   1472748122509822,1474136192510828,1475412813095884,1476578958361440,1477635574403600,
   1478583580132486,1479423868046872,1480157304971048,1480784732755760,1481306968944972,
   1481724807410038,1482039018952830,1482250351879190,1482359532544062,1482367265869516,
   1482274235836812,1482081105953608,1481788519697274,1481397100935300,1480907454323622,
   1480320165683732,1479635802359288,1478854913552974,1477978030644224,1477005667488454,
   1475938320698354,1474776469907746,1473520578018518,1472171091431052,1470728440258548,
   1469193038525624,1467565284351510,1465845560118136,1464034232623374,1462131653219674,
   1460138157938280,1458054067599208,1455879687907106,1453615309533122,1451261208182842,
   1448817644650366,1446284864858510,1443663099885150,1440952565975656,1438153464541346,
   1435265982143844,1432290290465232,1429226546263824,1426074891315328,1422835452339236,
   1419508340910094,1416093653353404,1412591470625812,1409001858179154,1405324865808024,
   1401560527480304,1397708861150234,1393769868553404,1389743534983102,1385629829047334,
   1381428702405810,1377140089486140,1372763907178364,1368300054506954,1363748412279282,
   1359108842709508,1354381189016768,1349565274996412,1344660904562992,1339667861263580,
   1334585907759872,1329414785277446,1324154213020380,1318803887549348,1313363482121084,
   1307832645987032,1302211003648772,1296498154067602,1290693669825534,1284797096234636,
   1278807950391468,1272725720173092,1266549863170816,1260279805557522,1253914940884104,
   1247454628800116,1240898193693364,1234244923242636,1227494066877364,1220644834137338,
   1213696392925070,1206647867642666,1199498337204334,1192246832914818,1184892336203144,
   1177433776199978,1169870027145832,1162199905616020,1154422167546870,1146535505046120,
   1138538542968628,1130429835236530,1122207860880790,1113871019778488,1105417628057410,
   1096845913136266,1088154008365236,1079339947227410,1070401657056982,1061336952224746,
   1052143526735300,1042818946173386,1033360638928746,1023765886619668,1014031813624672,
   1004155375619518,994133347002328,983962307072966,973638624813370,963158442092680,952517655094180,
   941711893729510,930736498767992,919586496364502,908256569616060,896741026713546,885033765178216,
   873128231579710,861017376019324,848693600524118,836148700327680,823373796803382,810359260554746,
   797094622840292,783568473097676,769768339807484,755680551265506,741290071964762,726580309157702,
   711532882680394,696127349140100,680340868903036,664147800689134,647519203568692,630422219133962,
   612819296620846,594667209267052,575915788779540,556506272438280,536369107292934,515420976230848,
   493560679848750,470663285277500,446571557505732,421082950587422,393928974566660,364740642298436,
   332986443698248,297850241931614,257957639793838,210627934051154,148938704273464]
private def pvm_r256_s3_1 : List ℤ := rkmZigHi256T3
  [2018929594,5826989830,15073951,1328008885,1964186700,3835148469,304909999,1815850243,4287858778,
   9390268518,7140889960,3163358718,1037395434,273266775,323190606,6483150679,9740108167,7049795606,
   7278288569,14595564417,5454760529,5089639295,8327157513,10040849163,4050944419,4041698436,
   1667477257,12964677,11725110887,15250789179,3077149763,10025983787,5973149851,4905678038,
   5704130199,7572809637,14704013388,1080202816,9602422553,18526104916,7003698604,1385382851,
   12957855982,4488576048,4124963894,25503933832,20849143878,25881238874,10652494504,20852109789,
   2652025319,9732265420,106705017,7176437168,1308316715,10266011963,16608663657,4598277298,
   31200984092,17182383654,20817364385,22617081209,2780658456,2099892485,16746692628,34695096092,
   37572543306,27800726494,20949121552,14343716474,21243525422,33703185588,24531778036,21877943558,
   14342190190,2269904448,9943423224,41762695500,35900575784,2561420247,29907816415,13979461185,
   14335067702,16553729076,46552085078,31392137474,5019996320,10852460999,48117577856,38117391424,
   20230471889,52551280017,4541921640,40032940426,9836702572,53791208,4389064648,8680338541,
   23873113569,9874894503,31838786866,5170914540,22298060537,4443196327,20800639778,7302906352,
   16997383105,11237127077,58899726224,27277148403,15845504859,6026835601,11807091450,11716184728,
   3907929950,11970994261,11837022208,8687633153,40178834967,28328519712,49696950156,14299386821,
   35203426227,31932966192,13224496144,21384090397,17046892387,8924979506,1535763790,1125185944,
   33721192103,27764379193,939042992,1586150651,7188058217,18933764688,21466655634,35476585396,
   62900134226,35490228184,2858722478,40242206472,30015285928,21427942074,29302801156,24537823944,
   18884310464,12832735445,20790355099,7690496581,11051463239,14406285179,13791342806,1090831770,
   19122327307,40131130699,13977608715,33469862613,26046207433,13086357191,71847358563,21554064783,
   58069339303,100293714002,45584233287,67927039440,24287421465,43172766448,51510031312,70002588819,
   17887660600,70965493775,53817852716,63320255868,58213873363,7274507970,99778000011,40229492933,
   47271392680,89961714353,16480454677,20345299635,92712355845,78623195734,12038446652,138681059571,
   367429833,45234876899,142616092857,56313074966,38849882492,149525828969,20009052026,134673202346,
   87289233305,80518175547,102503149528,61806044473,215121436945,57877266366,236626421702,
   21793201523,127846696599,75698953244,143708240914,196632834281,129739082167,92599361214,
   438637000748,99003361207,49322859697,194442068987,460221589130,111393872954,97535469769,
   328199257787,233558921065,441088569064,273200023810,102563761782,487275944573,1150417957767,
   821058933675,181452679719,1315202143586,3275826959142,3415804000720,449585719362,6864723740273,
   17377448628049,23488658682839,13268565546861,26685333891492,107851822386870,232128699974254,
   387434204189446,550653431933996,692965347434244,786885490519924,815398923753892,777313140733778,
   685250905651430,559938410130842,424448274087486,298764368357318,195522845501138,118925020943460,
   66920730005752,34482274814394,16018935908214,6579733388442,2335283414106,696356339502,
   167924700198,30838879170,3845232436,239886332]
private theorem dk_r256_s3_0 :
    muxFastIterBSlideChk 31 257 phbv_r256_s3
      pvi_256_3 pvm_r256_s3_1 = true := by
  decide +kernel
private theorem dk_r256_s3_1 :
    muxFastIterBSlideChk 30 257 phbv_r256_s3
      pvm_r256_s3_1 pvo_256_3 = true := by
  decide +kernel
private def phb_256_4 : List ℤ :=
  altBuildHbFrom 512 256 135863375000 0 256
private def pvi_256_4 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r256_s3 pvo_256_3
private def pvo_256_4 : List ℤ := rkmZigHi256T3
  [1427289397,1006045076,2542618934,1711219412,4446610098,4044280105,606053174,1530914814,
   1734193011,4380993914,6937110722,1546268046,396378672,2191016061,3411986656,287696586,3402640144,
   9623650504,7160027139,5750732650,1910420548,5606326159,4660120369,3203967867,6875790212,
   6694508073,1025703989,3126323216,2583012943,10894108217,19548223283,10571291325,7371044010,
   6230070882,3590284390,7609972782,4676679528,9316969229,11089204937,11670899983,9646474437,
   130118374,1488041669,6062398425,2685830669,6590147488,604629676,4578202328,2011071650,8361613131,
   9518728326,5144526247,6182591235,19356923795,2086728809,2250791219,4813163358,10187119570,
   222993864,7070802364,3712213179,23953977368,16980232550,21484234664,13913690261,4028480424,
   8991673112,7459372737,745512712,6004215454,8649667191,9904106822,20196196841,19089338417,
   6342215349,3559073405,15135577358,7869993124,6414965595,24131972870,24965472644,4369034811,
   27066871942,28889888682,30994502734,15227388103,13235483821,7426697557,8300638192,21165439382,
   17843266809,31325596464,35329352070,5157530749,17677388149,29898343358,34779929084,4126737186,
   26075968178,20310435012,14808917326,26283015851,56847840917,57202548934,25582698546,23518094996,
   37982584398,25235441283,3324454482,7017863367,12468894476,40657174349,58757736942,52194296007,
   46417701479,16079412949,27256549127,85252190974,15792492033,55093675634,53285089126,23677586802,
   68843522781,24904359779,22303968812,56609008474,26549852302,73696012493,78635194334,23335589259,
   7403248092,44913739743,396232718,17152754854,17959738462,20310302957,37414088705,34441368098,
   61842282272,12665738790,15733639844,50062370963,59435920010,9764272473,55387317067,57457717020,
   26530317355,15899318092,37525197673,37195378181,53825249222,1442981974,29430234474,19212621083,
   19063560377,3476408878,2832786118,15410682681,70595007304,20337804351,16485418748,9722242840,
   30296980953,35008082340,57925070560,73626856397,16789245317,58308131923,9919645571,40918481334,
   45628035135,58567308004,81507277716,16309782402,40779427442,6755382976,51861281676,55295354962,
   28182439513,164462119851,203908731139,75657566041,44189881068,91922041026,14477226268,
   45149182707,215037462381,100208115057,211480770053,195436709375,32737068180,131552538400,
   49633937540,192940488811,177001264405,155028204067,17739925726,59649336160,212085314307,
   28616267585,176218363516,147728523232,135371021652,109065612156,184229387263,206623697009,
   126620820432,96124214483,167030128264,72607429831,74962276550,253512188053,199221219157,
   196544637931,44969193787,198409440761,170515831234,61346864330,220808486535,300595024153,
   71936633461,169953546615,197162322014,467057369838,162224871799,230536122461,17270465661,
   2691445797,253214704706,275124937845,321648707290,180677872421,501226811344,255517200525,
   1015124443503,1787037336764,2780370937765,2496714686316,160469253218,2513964916691,1715253699326,
   7138706143222,4492588831235,12319564770647,39939056275780,8991222808460,32758702004607,
   5906799473336,17032896448542,110508222421193,259186014865569,149641024455917,336590265012692,
   947149299558808,1247465647960666,1032848413547974,511429692930142]
private def phb_256_5 : List ℤ :=
  altBuildHbFrom 512 256 139823555555 0 256
private def pvi_256_5 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r256_s4 pvo_256_4
private def pvo_256_5 : List ℤ := rkmZigHi256T3
  [2447349531,442184704,444403782,1224416239,441959944,415763532,3027196437,2147305167,3256477639,
   4657317681,1233053361,1077772482,2467731607,420830663,4306805923,6578591697,4425782667,
   1151557943,1112268624,521446899,2106336678,3149312981,1408405096,6151446414,10527165158,
   6896027444,1240854178,6310096582,837405155,4706069463,3321621911,3565592207,1236968927,
   9500053059,8205399131,6575481737,331076906,9539862906,9038903534,11542713458,11018539218,
   7885648802,8379131354,2999847144,8314722200,1773925811,8172757942,16316155346,12315537964,
   12500054474,1407472931,2859793060,5037969421,9506103972,10059323122,10377010475,8890842027,
   1057648986,6313440410,11147947988,4768762040,1998645785,838677644,3025914565,9482448483,
   1060176871,5515509301,11144230909,7217156465,8999276753,7499263682,4552954390,20705039810,
   17173540764,9673852348,21843546068,10418252364,7045019344,12372179114,874529093,3674925345,
   6220212146,11070143460,35158820860,26484245112,15145141999,3990551324,11564546935,6962953284,
   2600061424,2633677590,7136541313,30394703694,11396378764,53216213062,10893873532,21219011840,
   6117784932,12807936002,8317283266,684542375,35439236825,42013206517,39870769467,19764382264,
   19704175047,32296278890,50054031633,43619809500,72849660258,48543286040,21102479099,1185036237,
   66062813295,10902287759,20373638274,5744226025,64458195357,68857585156,8471130836,18226138633,
   71494871964,39769343673,97465529111,434617777,27088089421,31273958213,38211084717,34895688472,
   104706646819,43312518935,41429791823,53995952459,21642449000,13467122961,83261661782,69646452943,
   13932499236,18268219174,18516471390,65422960225,41813389554,25913954938,5273206584,7373604663,
   20399782974,13770022879,5769892017,8875860997,23771145926,9176047767,2394477519,19722637878,
   10601064271,5265376005,9968999749,32740212096,28446800051,10610075336,10076868750,19633514369,
   25692242597,9659895613,30003434351,29541455580,15366016314,30100317199,19498515241,24158563771,
   37409844927,17674097873,11281381316,40558308179,31690265461,52153877573,44260326151,62340819219,
   85209235267,29920502081,55531086186,81889983890,84214450470,27693060665,120422207057,69339642740,
   256945499818,77764965389,37891093247,176081605533,51798212620,100223215423,298545869723,
   23442770962,187965770142,208147818916,50154872054,246330587873,20791464141,323442778276,
   283790139707,11509284400,24792550845,25442759569,53447895405,16331757694,35549501435,62428900063,
   2088415683,31670595625,58364063354,61478945451,139673982745,134412244717,62301776901,40813650511,
   152357186274,72197644469,138424392120,301974854119,375441211595,139132864201,45452748666,
   76455823146,350948446950,193548616007,520345843967,87011894774,38221378288,281510673280,
   85374564509,721866977544,916937214645,74130811320,1335447657838,3021391819017,2590523059424,
   800080154553,3851185584630,7091139293037,6963924689728,10001081966195,17090765073172,
   17639843022867,10746148358066,6671186964534,4585736759510,12077632640902,61720662973699,
   37294679191126,59688520170571,118638459340337,183514759284024,103309169264014,50157599058979,
   506448564885188,1359138992227544,1351066864725026]
private def phb_256_6 : List ℤ :=
  altBuildHbFrom 512 256 134739666666 0 256
private def pvi_256_6 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r256_s5 pvo_256_5
private def pvo_256_6 : List ℤ := rkmZigHi256T3
  [1827101123,1397297539,1057954621,503771449,1559692328,162350220,578145007,1746703204,941341836,
   431503336,3439650390,4033396488,2565132886,1623581852,1980668304,3563614008,2818671400,
   2016752013,4353308589,4695227067,4023081361,1246529807,5178488127,93396239,923475837,6508102426,
   4108341240,939071565,10680424901,5710138171,6452927927,857688037,2445007661,5355524764,
   5279879760,1778247623,2110069406,2992776200,9939673796,5165926028,4724649042,3604877100,
   5842082098,3434827468,12348171700,12282976648,6881438590,7653144304,8373211324,9613486556,
   11614419500,2728728366,4325944687,10187140189,16500117255,9732335531,6737987695,4604455919,
   3358539897,11465739838,10279054486,4666592514,10274352950,5975194432,3663667228,9532571438,
   10703999306,6923722282,3750477557,9145395900,7868458909,2078058249,2417235295,2209179366,
   12356025739,16135252169,13532828883,4482135542,2982416151,3538855222,17451504630,23776620206,
   15590944260,4943320946,19573981952,9591052211,7070310198,26915231111,21328310236,14487122476,
   18875078112,25792784760,15053651280,20254264472,6256510494,15366299134,119726762,6581275761,
   4323296294,25918217660,20239184486,26132815806,27343457618,21363051306,42635068230,37480946789,
   27288744982,3018136000,24693462918,39258030418,31333946576,23973172364,17022679704,21388379020,
   28244094452,67038298690,69512624324,107523485082,50799555223,49282828047,40090031388,69179190754,
   111417076621,42115119230,48138709851,9184384126,47745512035,41837541953,78088028025,74531939834,
   8266984585,29046358638,20803588259,40872396565,80719636447,75786620724,28085119366,41238644247,
   10969677686,10283197513,8690738159,5425583285,10326080723,16904487838,6654854920,2723243393,
   7137076223,1220000827,5400206805,2296416689,2012340225,3419862697,6452721435,9992906875,
   15542754566,23933745262,18579141960,6292895477,8793082091,20894804330,19901439577,8319623309,
   22559635699,23169913011,12347731575,25299295005,4590174189,36192086733,6987029822,33238550487,
   24966515755,41530623193,36555929745,15735158904,15073949268,19314618976,3961908022,1856303612,
   58350072798,87348523692,19102689031,77174196666,134237117837,119427831867,19304136213,
   119979609388,175851614008,202310142967,85847404727,165027467030,135833881866,21127350033,
   135579528012,36001390681,227608719948,387945537103,338714751763,213568104652,124433893110,
   36979520885,25082684523,16518001208,6082232426,12301836420,41779892491,49535270651,27079400397,
   48559732362,34133488062,19992492741,50716153181,9766523598,29332818219,53884101423,105659566794,
   119683639504,82641123632,63131403492,49691612134,244665519604,240004780706,284562750757,
   43256699459,315265129393,562687385445,177165825144,340298346092,42133205220,135061462369,
   205972338146,282888804683,474813513801,19955624055,52777555900,1756013986358,662652893560,
   798885923475,3237829596835,3992416591519,824249390746,4573351191890,925311052476,9765538004838,
   8950657315208,28063390534362,874888948383,28154552560974,7053451369472,27678514931409,
   43129587132605,7442558318479,96551570847647,162921005565719,170320587168067,220445422523085,
   768945442595692,1814031242414194]
private def phb_256_7 : List ℤ :=
  altBuildHbFrom 512 256 125463166666 0 256
private def pvi_256_7 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r256_s6 pvo_256_6
private def pvo_256_7 : List ℤ := rkmZigHi256T3
  [1103232811,1101291115,1720178967,621211687,300785489,1899142193,1251114105,1341570898,1071832235,
   1276908227,136307423,130325326,663448160,3995786275,5598827381,633314975,857099150,44225848,
   618620127,2283325981,1076780131,339215169,6175323277,9780193827,3324989032,1607262217,558815167,
   807892510,2734336318,1647639862,1815966126,1363513644,7199558618,8252582964,6835042622,
   1579878870,575514888,10604472624,4262211942,58919204,896979698,352930809,1061350971,6316839060,
   12330778788,4076956172,1266132587,1058047907,528949345,10119821268,6852195914,9499021746,
   4867957552,8073512772,10767562208,11950967006,10306906944,8940377334,458930387,13216379801,
   18070963259,4572952841,197061187,922316330,17256251767,6442535573,3371693065,2376742745,
   1300453318,6491426512,5550182874,3793195840,10878783402,10594590272,10793789584,1087161962,
   349736999,306597058,8795909158,5396148593,15422052589,1635928093,15865841311,19647816689,
   6392242283,7145605848,1694419327,22092475326,14877822356,17918904684,3169731494,14721731718,
   12045226826,18127372490,14923958244,13471028686,28930862466,14421424280,16653040928,32214080608,
   9657472616,14018478302,12748583074,2209402612,1754367220,2401676469,25030179326,40781607088,
   47458101106,13237334459,8745255381,40370441289,9261677259,17328269259,29526171993,20922607873,
   35572510691,44651410905,4554761080,38754965745,8858974852,7064506117,134656370473,43820250141,
   80452559029,31608259369,47240429169,43704098051,219134635815,13512768600,8968169713,8089682202,
   13820220253,9962009517,13064652545,4276945416,8302449900,2157040796,13835764309,12343989139,
   11905266311,580622452,12393351900,13555686258,10870939280,847104666,5393237005,2908765076,
   12115096860,14960000254,6496652550,2675376970,2382841838,1333637906,384057065,6132156698,
   294417878,1407921649,9111714038,10380876201,32114889050,14853624378,34023259032,2010030801,
   780419418,5947781021,14819428273,15200186151,21987818951,16556888915,15236601825,21042987403,
   25105727345,5498883863,12832870477,42444850411,33952026609,10039728237,52959019769,41723572339,
   8863946567,20313113426,13011058284,41350810891,147397499741,40365473713,50416796722,44321323976,
   236291948452,64134468485,272447476296,647758886463,44979387804,23904693515,6983504344,
   14487357048,26195881544,7837408686,7303142704,4559015709,13100491195,4202148430,1888884373,
   20683042670,17926182964,25960417797,10873696500,5170616031,22095013776,39928064716,37005552228,
   38475239552,27041737568,71142121682,1060470499,54583901916,40906916703,77100530882,112240296628,
   111411916092,47999324744,39968617270,85745002972,86328995340,558362394826,347191854268,
   260714588969,540781902889,2429548444,254293358195,462167910184,455543046699,262302850892,
   159068918891,1197535315921,182046449101,1291494734968,701607484766,2824241744343,7153438322078,
   536269883293,6755885671068,7326047453511,1635882654824,7362092528994,33222026339335,
   17115981875509,11753618613960,13965810063063,44216269511502,20866368194410,1923217316579,
   61691996029298,179197971269316,94741438852978,95664261553624,1985348625102446]
private def phbv_r512_s0 : List ℤ := rkmZigHi256T3
  [211830501941554,298695768562718,364750676350202,419935586559802,468112955520356,511269632173186,
   550589360515964,586845648022684,620577314229586,652177784808446,681944901639010,710110705906000,
   736860240747746,762343952696884,786686171343386,809991085375378,832347063977556,853829851809412,
   874504977263480,894429598822488,913653942091260,932222433376586,950174604748674,967545824568348,
   984367892998422,1000669531850230,1016476790854472,1031813387182026,1046700991173990,
   1061159468364704,1075207085718340,1088860688355380,1102135851782840,1115047013664210,
   1127607588400970,1139830067195794,1151726105790074,1163306601686928,1174581762364028,
   1185561165732200,1196253813893714,1206668181088578,1216812256581074,1226693583126088,
   1236319291561266,1245696131992852,1254830501977648,1263728472048352,1272395808883012,
   1280837996379790,1289060254864616,1297067558630584,1304864651983324,1312456063945434,
   1319846121754802,1327038963275854,1334038548429120,1340848669732566,1347472962037812,
   1353914911535250,1360177864094174,1366265032997018,1372179506120726,1377924252612770,
   1383502129104652,1388915885501422,1394168170382000,1399261536041750,1404198443205812,
   1408981265438956,1413612293275446,1418093738090216,1422427735730764,1426616349927486,
   1430661575498566,1434565341364254,1438329513384008,1441955897028888,1445446239900610,
   1448802234107646,1452025518507992,1455117680827446,1458080259661514,1460914746368440,
   1463622586860330,1466205183298712,1468663895700498,1471000043459798,1473214906790672,
   1475309728095518,1477285713263462,1479144032902808,1480885823511310,1482512188587746,
   1484024199688100,1485422897429328,1486709292443578,1487884366285458,1488949072294842,
   1489904336417474,1490751057985538,1491490110460150,1492122342137678,1492648576821598,
   1493069614461534,1493386231760986,1493599182755196,1493709199360434,1493716991895994,
   1493623249580034,1493428641000348,1493133814561082,1492739398906358,1492246003321656,
   1491654218113800,1490964614970308,1490177747298828,1489294150547294,1488314342505450,
   1487238823588292,1486068077101954,1484802569492526,1483442750578250,1481989053765480,
   1480441896248812,1478801679195666,1477068787915676,1475243592015100,1473326445536510,
   1471317687083972,1469217639933854,1467026612131428,1464744896573360,1462372771076178,
   1459910498430746,1457358326442782,1454716487959408,1451985200881678,1449164668163008,
   1446255077793430,1443256602769512,1440169401049780,1436993615495450,1433729373796238,
   1430376788380958,1426935956312630,1423406959167742,1419789862899262,1416084717683034,
   1412291557747016,1408410401182914,1404441249739606,1400384088597782,1396238886125088,
   1392005593611124,1387684144981442,1383274456489754,1378776426387414,1374189934569196,
   1369514842194304,1364750991281486,1359898204276980,1354956283594016,1349925011122392,
   1344804147706630,1339593432591004,1334292582829682,1328901292660058,1323419232837160,
   1317846049926934,1312181365555954,1306424775614976,1300575849413490,1294634128782252,
   1288599127120476,1282470328384166,1276247186011680,1269929121782400,1263515524603952,
   1257005749223058,1250399114854700,1243694903723796,1236892359513038,1229990685710072,
   1222989043846464,1215886551620316,1208682280893552,1201375255554118,1193964449232362,
   1186448782859852,1178827122057738,1171098274340456,1163260986119178,1155313939487784,
   1147255748772346,1139084956823126,1130800031025810,1122399359006154,1113881243999396,
   1105243899852504,1096485445623678,1087603899739396,1078597173664508,1069463065035570,
   1060199250201356,1050803276107538,1041272551454356,1031604337046844,1021795735246364,
   1011843678419846,1001744916268628,991496001902034,981093276501154,970532852395398,
   959810594347236,948922098808774,937862670875998,926627298621602,915210624433808,903606912924230,
   891810014890572,879813326726222,867609744555016,855191612230228,842550662165760,829677947755892,
   816563765876794,803197567633200,789567855097944,775662061263582,761466409748674,746965749927074,
   732143362009072,716980725103248,701457239292284,685549890071038,669232839837302,652476926075522,
   635249038797966,617511339733594,599220271154958,580325280656128,560767155601054,540475810508126,
   519367290348280,497339620886306,474266912706150,449990726928592,424306966817156,396945086726018,
   367533274364810,335535950148856,300130728502436,259932689166222,212240604136392,150079051559298]
private def pvm_r512_s0_1 : List ℤ := rkmZigHi256T3
  [23690984838918,71493667045328,152106412741780,263443911054756,393968554008668,525385201779654,
   637671668459460,714385043547452,746374221300800,732968505482522,680787438949448,601053703333240,
   506510155300922,408832035586350,317006202874158,236735212990100,170644734050934,118960593965078,
   80341805395744,52647146417972,33519729217186,20761435166904,12523727458568,7365012608054,
   4226521060192,2368834112786,1297690415256,695358647912,364704388832,187343906844,94310025268,
   46551332850,22541522286,10713174044,4999552106,2291947522,1032549434,457311224,199186960,
   85349876,35989440,14938518,6105528,2457756,974688,380892,146704,55696,20842,7688,2790,992,342,
   112,34,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_r512_s0_2 : List ℤ := rkmZigHi256T3
  [24069132,153611794,691085630,2530739562,8000984124,22554327432,57858479300,136983345948,
   302416350372,627472778292,1231203348310,2296085049774,4086646506332,6965877961220,11405085740998,
   17982139191068,27363204226862,40264345330448,57391882919874,79363904173970,106619328723536,
   139324676599932,177291333422892,219916916305888,266162865162608,314576602373276,363360982091162,
   410487164252160,453840618489404,491384826937966,521324329836416,542248554614182,553240396459276,
   553938297417252,544546750925678,525796699751906,498863175838046,465251930019862,426669223194192,
   384889276781366,341632332527766,298463330145710,256717493170506,217455248674356,181445434061384,
   149173043919106,120866035344864,96534958290988,76019285472302,59035072549774,45219735825296,
   34171052793980,25478772825568,18748331161338,13617010853706,9763470338304,6911866794032,
   4831901707592,3336051906788,2275084512010,1532738667574,1020230339498,671026338506,436156001264,
   280190230306,177917681280,111682382202,69309458138,42528876222,25804692694,15483717802,
   9188626538,5393373090,3131405350,1798540876,1021964018,574534484,319588874,175910208,95816890,
   51650132,27555286,14550152,7604718,3934358,2014932,1021560,512744,254784,125336,61040,29424,
   14036,6624,3086,1412,630,272,112,40,12,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private theorem dk_r512_s0_0 :
    muxFastIterBSlideChk 28 257 phbv_r512_s0
      rkmViHiHiB_m256_r512_s0_c0 pvm_r512_s0_1 = true := by
  decide +kernel
private theorem dk_r512_s0_1 :
    muxFastIterBSlideChk 28 257 phbv_r512_s0
      pvm_r512_s0_1 pvm_r512_s0_2 = true := by
  decide +kernel
private theorem dk_r512_s0_2 :
    muxFastIterBSlideChk 27 257 phbv_r512_s0
      pvm_r512_s0_2 rkmVoHiHiB_m256_r512_s0_c0 = true := by
  decide +kernel
private def phbv_r512_s1 : List ℤ := rkmZigHi256T3
  [170483573932032,240629283622732,294132750140944,338969293482048,378234634887578,413519662479260,
   445771313395114,475607781720080,503459304268032,529639741850150,554386492033174,577884344394564,
   600280534605758,621694669413042,642225510224724,661955751907968,680955477043484,699284708766652,
   716995334238018,734132578738488,750736152513178,766841155084484,782478796981296,797676982060586,
   812460782019840,826852826563066,840873626873526,854541845836486,867874525363502,880887278870768,
   893594455235102,906009279237062,918143972492114,930009858089554,941617451548738,952976540221632,
   964096252889576,974985120997728,985651132725728,996101780895114,1006344105552714,
   1016384731937350,1026229904428552,1035885516986288,1045357140516064,1054650047531584,
   1063769234434950,1072719441690508,1081505172131328,1090130707605926,1098600124145982,
   1106917305813018,1115085957362376,1123109615846040,1130991661261296,1138735326339722,
   1146343705560072,1153819763459226,1161166342307070,1168386169204016,1175481862653568,
   1182455938656744,1189310816370368,1196048823366912,1202672200529758,1209183106614432,
   1215583622503324,1221875755178834,1228061441437426,1234142551365074,1240120891592612,
   1245998208347852,1251776190319874,1257456471349410,1263040632958178,1268530206728804,
   1273926676546026,1279231480709012,1284446013923722,1289571629183634,1294609639546368,
   1299561319813222,1304427908118072,1309210607431518,1313910586985832,1318528983625716,
   1323066903089578,1327525421225686,1331905585147178,1336208414329704,1340434901655140,
   1344586014404596,1348662695203718,1352665862923070,1356596413536178,1360455220937686,
   1364243137723842,1367960995937458,1371609607779286,1375189766287680,1378702245988220,
   1382147803514974,1385527178204854,1388841092666506,1392090253325072,1395275350944042,
   1398397061125416,1401456044789212,1404452948633418,1407388405575330,1410263035175190,
   1413077444043014,1415832226229396,1418527963601074,1421165226201980,1423744572600456,
   1426266550223282,1428731695677132,1431140535058022,1433493584249324,1435791349208832,
   1438034326245380,1440223002285500,1442357855130518,1444439353704532,1446467958293672,
   1448444120776988,1450368284849352,1452240886236710,1454062352903976,1455833105255904,
   1457553556331230,1459224111990334,1460845171096700,1462417125692444,1463940361168108,
   1465415256426978,1466842184044138,1468221510420458,1469553595931714,1470838795073034,
   1472077456598852,1473269923658526,1474416533927808,1475517619736284,1476573508190988,
   1477584521296280,1478550976070148,1479473184657078,1480351454437590,1481186088134576,
   1481977383916546,1482725635497910,1483431132236372,1484094159227560,1484714997396984,
   1485293923589406,1485831210655716,1486327127537412,1486781939348734,1487195907456562,
   1487569289558150,1487902339756740,1488195308635158,1488448443327446,1488661987588590,
   1488836181862420,1488971263347710,1489067466062592,1489125020907262,1489144155725116,
   1489125095362284,1489068061725674,1488973273839552,1488840947900682,1488671297332108,
   1488464532835592,1488220862442760,1487940491564990,1487623623042090,1487270457189792,
   1486881191846092,1486456022416494,1485995141918162,1485498741023036,1484967008099920,
   1484400129255588,1483798288374932,1483161667160180,1482490445169208,1481784799852966,
   1481044906592056,1480270938732486,1479463067620604,1478621462637254,1477746291231168,
   1476837718951612,1475895909480322,1474921024662722,1473913224538466,1472872667371318,
   1471799509678386,1470693906258706,1469556010221250,1468385973012298,1467183944442258,
   1465950072711900,1464684504438052,1463387384678750,1462058856957876,1460699063289262,
   1459308144200328,1457886238755216,1456433484577454,1454950017872162,1453435973447816,
   1451891484737558,1450316683820094,1448711701440170,1447076667028646,1445411708722160,
   1443716953382428,1441992526615144,1440238552788532,1438455155051520,1436642455351576,
   1434800574452204,1432929631950090,1431029746291936,1429101034790970,1427143613643148,
   1425157597943044,1423143101699452,1421100237850692,1419029118279634,1416929853828450,
   1414802554313082,1412647328537460,1410464284307456,1408253528444576,1406015166799426,
   1403749304264908,1401456044789212,1399135491388540,1396787746159640,1394412910292098,
   1392011084080410,1389582366935862,1387126857398186,1384644653147014,1382135851013150,
   1379600546989626,1377038836242584,1374450813121966,1371836571172018,1369196203141632,
   1366529800994486,1363837455919044,1361119258338370,1358375297919772,1355605663584314,
   1352810443516136,1349989725171650,1347143595288562,1344272139894764,1341375444317068,
   1338453593189808,1335506670463294,1332534759412142,1329537942643458,1326516302104892,
   1323469919092580,1320398874258934,1317303247620338,1314183118564694,1311038565858874,
   1307869667656034,1304676501502842,1301459144346560,1298217672542042,1294952161858622,
   1291662687486874,1288349324045306,1285012145586914,1281651225605662,1278266637042858,
   1274858452293426,1271426743212094,1267971581119488,1264493036808122,1260991180548326,
   1257466082094054,1253917810688638,1250346435070428,1246752023478372,1243134643657502,
   1239494362864354,1235831247872284,1232145364976736,1228436780000420,1224705558298412,
   1220951764763188,1217175463829596,1213376719479724,1209555595247748,1205712154224662,
   1201846459062980,1197958571981354,1194048554769128,1190116468790830,1186162374990610,
   1182186333896604,1178188405625246,1174168649885524,1170127125983160,1166063892824762,
   1161979008921888,1157872532395080,1153744520977836,1149595032020514,1145424122494214,
   1141231848994570,1137018267745536,1132783434603072,1128527405058826,1124250234243744,
   1119951976931630,1115632687542674,1111292420146922,1106931228467712,1102549165885042,
   1098146285438934,1093722639832712,1089278281436266,1084813262289264,1080327634104328,
   1075821448270160,1071294755854636,1066747607607860,1062180053965182,1057592145050168,
   1052983930677546,1048355460356102,1043706783291550,1039037948389364,1034349004257570,
   1029639999209512,1024910981266574,1020161998160876,1015393097337936,1010604325959292,
   1005795730905108,1000967358776732,996119255899228,991251468323888,986364041830692,
   981457021930764,976530453868776,971584382625340,966618852919360,961633909210368,956629595700814,
   951605956338354,946563034818084,941500874584774,936419518835054,931319010519584,926199392345208,
   921060706777060,915902996040670,910726302124030,905530666779640,900316131526536,895082737652288,
   889830526214980,884559538045158,879269813747774,873961393704090,868634318073570,863288626795750,
   857924359592080,852541555967756,847140255213532,841720496407490,836282318416822,830825759899574,
   825350859306368,819857654882116,814346184667710,808816486501692,803268598021908,797702556667144,
   792118399678742,786516164102202,780895886788768,775257604396988,769601353394262,763927170058384,
   758235090479050,752525150559360,746797386017300,741051832387218,735288525021268,729507499090854,
   723708789588044,717892431326988,712058458945306,706206906905460,700337809496134,694451200833564,
   688547114862888,682625585359464,676686645930176,670730330014732,664756670886944,658765701655996,
   652757455267700,646731964505744,640689261992912,634629380192312,628552351408572,622458207789042,
   616346981324970,610218703852676,604073407054704,597911122460970,591731881449902,585535715249558,
   579322654938740,573092731448096,566845975561210,560582417915684,554302089004206,548005019175604,
   541691238635908,535360777449372,529013665539512,522649932690124,516269608546292,509872722615380,
   503459304268032,497029382739144,490582987128838,484120146403422,477640889396342,471145244809122,
   464633241212302,458104907046364,451560270622640,444999360124232,438422203606902,431828828999966,
   425219264107172,418593536607586,411951674056444,405293703886020,398619653406470,391929549806676,
   385223420155084,378501291400526,371763190373042,365009143784690,358239178230350,351453320188524,
   344651596022124,337834031979252,331000654193978,324151488687108,317286561366950,310405898030056,
   303509524361986,296597465938036,289669748223982,282726396576798,275767436245392,268792892371302,
   261802789989426,254797154028708,247776009312840,240739380560954,233687292388306,226619769306950,
   219536835726414,212438515954368,205324834197276,198195814561064,191051481051760,183891857576134,
   176716967942350,169526835860584,162321484943660,155100938707668,147865220572582,140614353862870,
   133348361808100,126067267543540,118771094110758,111459864458208,104133601441816,96792327825560,
   89436066282054,82064839393104,74678669650292,67277579455518,59861591121578,52430726872696,
   44985008845084,37524459087486,30049099561704,22558952143148,15054038621354,7534380700516]
private def pvm_r512_s1_1 : List ℤ := rkmZigHi256T3
  [15359,123630,633211,2366334,6713311,14287204,20582719,9609898,45628864,159745461,287624974,
   304914047,104588324,212013584,313109955,16824318,313986442,157658299,269633239,207445320,
   257072076,193723439,286075219,118367950,326599676,29848844,309822779,227176059,146723758,
   349525144,167076510,191156391,377521569,242418055,87839154,368225430,428160834,254256166,
   48141289,343601475,535773973,589681959,516651519,344465369,90000059,259625454,759996514,
   1522849372,2736883838,4702208756,7884554530,12996269590,21112939872,33836929028,53521889200,
   83575011992,128856121148,196194210166,295042146604,438288321892,643239263278,932778862950,
   1336697222776,1893164678704,2650304244552,3667788922742,5018360177432,6789132269934,
   9082516881458,12016577057842,15724603190584,20353700981456,26062196458536,33015699726808,
   41381729502520,51322884870734,62988656889400,76506095561824,91969679337080,109430864100612,
   128887904086490,150276624911640,173462876106250,198237386182154,224313680035052,251329593727358,
   278852738600060,306390034486834,333401165631796,359315532613968,383552002205210,405540518591516,
   424744456465540,440682487594540,452948710892328,461229865762108,465318608789430,465122068868526,
   460665195252502,452088738596048,439642053273944,423671216348576,404603252605322,382927443335716,
   359174856153408,333897253124656,307646522946980,280955654701812,254322103505854,228194187991126,
   202960907949668,178945342332542,156401555015046,135514738858444,116404183185130,99128536054978,
   83692777226790,70056310766018,58141609367682,47842904251032,39034500007168,31578385105594,
   25330907344704,20148380723706,15891573171568,12429094180682,9639758226028,7414038714358,
   5654748953092,4277096605870,3208257813836,2386606973118,1760721860114,1288265440152,934826424006,
   672780887340,480218855640,339964358718,238705064508,166237499382,114826019876,78668438052,
   53458246370,36031919166,24089179066,15974281642,10507257330,6855393828,4436673116,2848179614,
   1813665708,1145557288,717699450,446019828,274980456,168209930,102103320,61490042,36721182,
   21723700,12711774,7343926,4180536,2340412,1286598,693844,367008,190562,97330,49062,24526,12226,
   6112,3082,1560,792,396,194,88,36,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_r512_s1_2 : List ℤ := rkmZigHi256T3
  [21713694,108907013,215286274,179210209,54723803,223952400,55788551,209848557,105471804,199922642,
   114409857,207248225,91329694,225657806,36395905,237729489,48641633,218161544,148554852,142975181,
   226555345,8647762,230903868,146157738,125873913,238808273,61454215,186743750,219440266,8389334,
   209930479,207030501,5851140,211515320,214181848,18867008,192565739,236617129,82405915,138500372,
   251549244,175477902,28227383,213489613,257114683,135906839,70220530,237557794,273917672,
   164599700,29892513,213367431,303460817,265788377,120960949,72166292,244451236,342023824,
   340699574,247246580,90812140,89892281,258438007,388471537,466462515,490497855,466303353,
   402852861,307391159,182307717,20604137,196184400,504769642,964590060,1671457900,2770570246,
   4483183626,7138463778,11223106236,17448300752,26840300526,40865684804,61593033458,91907859430,
   135787019366,198644793408,287765651742,412829072014,586539249774,825363226556,1150373546002,
   1588190139828,2171998368496,2942609835588,3949520684858,5251899449694,6919423350674,
   9032866775308,11684327227316,14976968456536,19024158256496,23947880702882,29876322233826,
   36940560218154,45270320598628,54988826511862,66206824775776,79015945686876,93481626917076,
   109635906325424,127470450277816,146930232234876,167908305182554,190242110417534,213711732396032,
   238040446062984,262897806687932,287905405321876,312645265466618,336670697097774,359519261169490,
   380727344673944,399845717440992,416455346715928,430182692042332,440713698855516,447805757424054,
   451296990917336,451112376144320,447266374781166,439861949501324,429086042978744,415201793484606,
   398537935932444,379475979948154,358435856935088,335860780602806,312202069327246,287904636621086,
   263393773072874,239063727559156,215268458169954,192314775657608,170457954981640,149899753172670,
   130788652577158,113222053876728,97250076542562,82880586210992,70085057457018,58804893754536,
   48957859871064,40444330278130,33153114690002,26966683304074,21765675239482,17432630397502,
   13854934630996,10927008782638,8551802977816,6641678661748,5118773039392,3914944969820,
   2971399348988,2238080097860,1672911620770,1240956474908,913544219730,667413915792,483901163588,
   348190346642,248644128736,176215352592,123941248878,86516131196,59936298082,41209446994,
   28120298748,19044131042,12800347886,8538914706,5653337094,3714756008,2422604572,1568076828,
   1007376756,642336730,406519464,255351368,159186212,98475776,60439956,36793196,22207584,13284198,
   7871472,4617834,2680776,1539280,873858,490354,271934,149046,80750,43262,22934,12028,6242,3200,
   1618,806,390,176,72,26,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_r512_s1_3 : List ℤ := rkmZigHi256T3
  [132522596,179912234,86511076,88253927,180654463,91380613,94807170,185512798,82648338,108835029,
   188455991,71572511,121111510,190059532,64067510,128175103,191943861,63694683,128358688,195098810,
   72474958,120125591,198987253,91109477,101385696,201004594,118667050,69627799,196220493,151745039,
   22949048,177660620,183353270,37920406,137692477,202205199,106786675,71188744,193670340,169312586,
   19296846,144038509,202709661,117550479,49210308,181243736,190796020,73723358,90533847,196715037,
   179002971,51406287,107040326,202080912,179808100,55724750,99628263,201039767,195890115,89252489,
   63223344,185071750,218453094,149687426,11902872,132150023,220423905,217411379,126007405,15833996,
   153177208,236095532,236387502,156031982,23559276,118299489,226579429,271006977,241625263,
   148488887,16752189,121085710,234388808,300900438,309763548,262310320,169750752,48860328,81722703,
   204779005,307350615,381609797,424410159,436772405,422583533,386652671,333429729,265957813,
   184284013,84034953,44898474,220832560,474132376,852325372,1427857552,2309980910,3661502154,
   5722141436,8841600252,13525296728,20496065074,30776900078,45800940166,67555021490,98764178156,
   143126020316,205604150958,292789145604,413335298060,578480252800,802651427180,1104158453922,
   1505965439164,2036529560898,2730682695138,3630521409150,4786258747736,6256978504412,
   8111219435272,10427305018212,13293325699476,16806675903946,21073048509218,26204797081616,
   32318592673984,39532327733616,47961254408120,57713388126292,68884258842092,81551149105936,
   95767016341858,111554352380864,128899282211560,147746241082558,167993589288162,189490522935318,
   212035614071878,235377263472092,259216274257576,283210656619036,306982658002058,330127886134994,
   352226262333518,372854418463936,391599042094182,408070589794740,421916735973732,432834909361760,
   440583293868472,444989734780060,445958092026130,443471713393790,437593853325824,428465026761180,
   416297451109156,401366881862050,384002278434312,364573838131446,343480001686074,321134060534794,
   297950984036910,274335037075032,250668680212082,227303142930616,204550943819716,182680508788662,
   161912918065930,142420702455332,124328515110700,107715431216938,92618576815430,79037760124454,
   66940772904752,56269043098770,46943349491700,38869350297838,31942726020594,26053788522870,
   21091459287480,16946567294460,13514458509018,10696943187696,8403633389574,6552741226174,
   5071419040922,3895726800076,2970310653748,2247871146836,1688491180012,1258883706632,931608314446,
   684295098868,498904191894,361040374464,259334596336,184898041526,130849581798,91913949902,
   64085581488,44351634784,30467008340,20774055802,14059976148,9445401066,6298393650,4168829608,
   2738891978,1786130282,1156188312,742879460,473778434,299906568,188420748,117482082,72689402,
   44624252,27177042,16416640,9833918,5840252,3437942,2005510,1159094,663576,376236,211238,117426,
   64620,35194,18966,10110,5326,2764,1406,702,338,154,64,20,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0]
private theorem dk_r512_s1_0 :
    muxFastIterBSlideChk 23 513 phbv_r512_s1
      rkmViHiHiB_m256_r512_s1_c0 pvm_r512_s1_1 = true := by
  decide +kernel
private theorem dk_r512_s1_1 :
    muxFastIterBSlideChk 22 513 phbv_r512_s1
      pvm_r512_s1_1 pvm_r512_s1_2 = true := by
  decide +kernel
private theorem dk_r512_s1_2 :
    muxFastIterBSlideChk 22 513 phbv_r512_s1
      pvm_r512_s1_2 pvm_r512_s1_3 = true := by
  decide +kernel
private theorem dk_r512_s1_3 :
    muxFastIterBSlideChk 22 513 phbv_r512_s1
      pvm_r512_s1_3 rkmVoHiHiB_m256_r512_s1_c0 = true := by
  decide +kernel
private def pwalks_256 : List RkmSegWalk := [
  ⟨phb_256_0, pvi_256_0, pvo_256_0⟩,
  ⟨phb_256_1, pvi_256_1, pvo_256_1⟩,
  ⟨phb_256_2, pvi_256_2, pvo_256_2⟩,
  ⟨phb_256_3, pvi_256_3, pvo_256_3⟩,
  ⟨phb_256_4, pvi_256_4, pvo_256_4⟩,
  ⟨phb_256_5, pvi_256_5, pvo_256_5⟩,
  ⟨phb_256_6, pvi_256_6, pvo_256_6⟩,
  ⟨phb_256_7, pvi_256_7, pvo_256_7⟩
  ]
private theorem ptail_256 : rkmAllTrueF [
    muxIntListEq phb_256_0 phbv_r256_s0,
    muxIntListEq phb_256_1 phbv_r256_s1,
    muxIntListEq phb_256_2 phbv_r256_s2,
    muxIntListEq phb_256_3 phbv_r256_s3,
    muxFastIterBSlideChk 8 257 phb_256_4
      pvi_256_4 pvo_256_4,
    muxFastIterBSlideChk 9 257 phb_256_5
      pvi_256_5 pvo_256_5,
    muxFastIterBSlideChk 6 257 phb_256_6
      pvi_256_6 pvo_256_6,
    muxFastIterBSlideChk 6 257 phb_256_7
      pvi_256_7 pvo_256_7,
    muxIntListEq rkmHbHiHiB_m256_r512_s0_c0 phbv_r512_s0,
    muxIntListEq rkmHbHiHiB_m256_r512_s1_c0 phbv_r512_s1,
    rkmCheckRowFromWalks 256 32 256 [1, 1, 2, 2, 2, 2, 2, 2]
      [13706357, 16281422, 8842647, 8855047, 1086907, 1258412, 808438, 752779]
      [58, 69, 61, 61, 8, 9, 6, 6] rkmMasksHiHiB_m256_r256 pwalks_256 rkmRowHiHiB_m256_r256
  ] = true := by
  decide +kernel
private theorem pw_r256_s0_1 :
    muxFastIterFullT16 58 257 phbv_r256_s0
      pvi_256_0 = pvo_256_0 :=
  (muxFastIterFullT16_add 29 29 257
    phbv_r256_s0 pvi_256_0).trans
    ((congrArg (muxFastIterFullT16 29 257 phbv_r256_s0)
      (muxFastIterBSlideChk_sound dk_r256_s0_0)).trans
      (muxFastIterBSlideChk_sound dk_r256_s0_1))
private theorem pwalk_256_0 :
    muxFastIterFullT16 58 257
      phb_256_0 pvi_256_0 = pvo_256_0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 58 257 h pvi_256_0)
    (muxIntListEq_eq_true.mp (rkmHd ptail_256))).trans pw_r256_s0_1
private theorem pseg_256_0 :
    muxFastIterFullT16 58 (Nat.add (highdNatMin (Nat.mul 1 256) 256) 1)
      phb_256_0 pvi_256_0 = pvo_256_0 := by
  rw [pdim_256_l1]
  exact pwalk_256_0
private theorem pw_r256_s1_1 :
    muxFastIterFullT16 69 257 phbv_r256_s1
      pvi_256_1 = pvo_256_1 :=
  (muxFastIterFullT16_add 35 34 257
    phbv_r256_s1 pvi_256_1).trans
    ((congrArg (muxFastIterFullT16 34 257 phbv_r256_s1)
      (muxFastIterBSlideChk_sound dk_r256_s1_0)).trans
      (muxFastIterBSlideChk_sound dk_r256_s1_1))
private theorem pwalk_256_1 :
    muxFastIterFullT16 69 257
      phb_256_1 pvi_256_1 = pvo_256_1 :=
  (congrArg (fun h ↦ muxFastIterFullT16 69 257 h pvi_256_1)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl ptail_256)))).trans pw_r256_s1_1
private theorem pseg_256_1 :
    muxFastIterFullT16 69 (Nat.add (highdNatMin (Nat.mul 1 256) 256) 1)
      phb_256_1 pvi_256_1 = pvo_256_1 := by
  rw [pdim_256_l1]
  exact pwalk_256_1
private theorem pw_r256_s2_1 :
    muxFastIterFullT16 61 257 phbv_r256_s2
      pvi_256_2 = pvo_256_2 :=
  (muxFastIterFullT16_add 31 30 257
    phbv_r256_s2 pvi_256_2).trans
    ((congrArg (muxFastIterFullT16 30 257 phbv_r256_s2)
      (muxFastIterBSlideChk_sound dk_r256_s2_0)).trans
      (muxFastIterBSlideChk_sound dk_r256_s2_1))
private theorem pwalk_256_2 :
    muxFastIterFullT16 61 257
      phb_256_2 pvi_256_2 = pvo_256_2 :=
  (congrArg (fun h ↦ muxFastIterFullT16 61 257 h pvi_256_2)
    (muxIntListEq_eq_true.mp (rkmHd (rkmT2 ptail_256)))).trans pw_r256_s2_1
private theorem pseg_256_2 :
    muxFastIterFullT16 61 (Nat.add (highdNatMin (Nat.mul 2 256) 256) 1)
      phb_256_2 pvi_256_2 = pvo_256_2 := by
  rw [pdim_256_l2]
  exact pwalk_256_2
private theorem pw_r256_s3_1 :
    muxFastIterFullT16 61 257 phbv_r256_s3
      pvi_256_3 = pvo_256_3 :=
  (muxFastIterFullT16_add 31 30 257
    phbv_r256_s3 pvi_256_3).trans
    ((congrArg (muxFastIterFullT16 30 257 phbv_r256_s3)
      (muxFastIterBSlideChk_sound dk_r256_s3_0)).trans
      (muxFastIterBSlideChk_sound dk_r256_s3_1))
private theorem pwalk_256_3 :
    muxFastIterFullT16 61 257
      phb_256_3 pvi_256_3 = pvo_256_3 :=
  (congrArg (fun h ↦ muxFastIterFullT16 61 257 h pvi_256_3)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl (rkmT2 ptail_256))))).trans pw_r256_s3_1
private theorem pseg_256_3 :
    muxFastIterFullT16 61 (Nat.add (highdNatMin (Nat.mul 2 256) 256) 1)
      phb_256_3 pvi_256_3 = pvo_256_3 := by
  rw [pdim_256_l2]
  exact pwalk_256_3
private theorem pwalk_256_4 :
    muxFastIterFullT16 8 257
      phb_256_4 pvi_256_4 = pvo_256_4 :=
  muxFastIterBSlideChk_sound (rkmHd (rkmT4 ptail_256))
private theorem pseg_256_4 :
    muxFastIterFullT16 8 (Nat.add (highdNatMin (Nat.mul 2 256) 256) 1)
      phb_256_4 pvi_256_4 = pvo_256_4 := by
  rw [pdim_256_l2]
  exact pwalk_256_4
private theorem pwalk_256_5 :
    muxFastIterFullT16 9 257
      phb_256_5 pvi_256_5 = pvo_256_5 :=
  muxFastIterBSlideChk_sound (rkmHd (rkmTl (rkmT4 ptail_256)))
private theorem pseg_256_5 :
    muxFastIterFullT16 9 (Nat.add (highdNatMin (Nat.mul 2 256) 256) 1)
      phb_256_5 pvi_256_5 = pvo_256_5 := by
  rw [pdim_256_l2]
  exact pwalk_256_5
private theorem pwalk_256_6 :
    muxFastIterFullT16 6 257
      phb_256_6 pvi_256_6 = pvo_256_6 :=
  muxFastIterBSlideChk_sound (rkmHd (rkmT2 (rkmT4 ptail_256)))
private theorem pseg_256_6 :
    muxFastIterFullT16 6 (Nat.add (highdNatMin (Nat.mul 2 256) 256) 1)
      phb_256_6 pvi_256_6 = pvo_256_6 := by
  rw [pdim_256_l2]
  exact pwalk_256_6
private theorem pwalk_256_7 :
    muxFastIterFullT16 6 257
      phb_256_7 pvi_256_7 = pvo_256_7 :=
  muxFastIterBSlideChk_sound (rkmHd (rkmTl (rkmT2 (rkmT4 ptail_256))))
private theorem pseg_256_7 :
    muxFastIterFullT16 6 (Nat.add (highdNatMin (Nat.mul 2 256) 256) 1)
      phb_256_7 pvi_256_7 = pvo_256_7 := by
  rw [pdim_256_l2]
  exact pwalk_256_7
private theorem pwalks_snd_256 :
    RkmSegWalksSound 256 256 [1, 1, 2, 2, 2, 2, 2, 2]
      [58, 69, 61, 61, 8, 9, 6, 6] pwalks_256 := by
  dsimp only [RkmSegWalksSound, pwalks_256]
  exact ⟨pseg_256_0, ⟨pseg_256_1, ⟨pseg_256_2, ⟨pseg_256_3,
    ⟨pseg_256_4, ⟨pseg_256_5, ⟨pseg_256_6, ⟨pseg_256_7, trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 256, r = 256)` (`FindAllJohnsonRampKickMuxHi256T3`). -/
theorem rkmTrajHiHiB_m256_r256 :
    rkmLo12EqHi 256 32 256 [1, 1, 2, 2, 2, 2, 2, 2]
      [13706357, 16281422, 8842647, 8855047, 1086907, 1258412, 808438, 752779]
      [58, 69, 61, 61, 8, 9, 6, 6] rkmMasksHiHiB_m256_r256 rkmRowHiHiB_m256_r256 :=
  rkmCheckRowFromWalks_sound pwalks_snd_256
    (rkmHd (rkmT2 (rkmT8 ptail_256)))
private theorem pw_r512_s0_1 :
    muxFastIterFullT16 56 257 phbv_r512_s0
      rkmViHiHiB_m256_r512_s0_c0 = pvm_r512_s0_2 :=
  (muxFastIterFullT16_add 28 28 257
    phbv_r512_s0 rkmViHiHiB_m256_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 28 257 phbv_r512_s0)
      (muxFastIterBSlideChk_sound dk_r512_s0_0)).trans
      (muxFastIterBSlideChk_sound dk_r512_s0_1))
private theorem pw_r512_s0_2 :
    muxFastIterFullT16 83 257 phbv_r512_s0
      rkmViHiHiB_m256_r512_s0_c0 = rkmVoHiHiB_m256_r512_s0_c0 :=
  (muxFastIterFullT16_add 56 27 257
    phbv_r512_s0 rkmViHiHiB_m256_r512_s0_c0).trans
    ((congrArg (muxFastIterFullT16 27 257 phbv_r512_s0)
      pw_r512_s0_1).trans
      (muxFastIterBSlideChk_sound dk_r512_s0_2))
/-- Certified `T_16` walk segment `m256_r512_s0_c0`. -/
theorem rkmWalkChkHiHiB_m256_r512_s0_c0 :
    muxFastIterFullT16 83 257
      rkmHbHiHiB_m256_r512_s0_c0 rkmViHiHiB_m256_r512_s0_c0 = rkmVoHiHiB_m256_r512_s0_c0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 83 257 h rkmViHiHiB_m256_r512_s0_c0)
    (muxIntListEq_eq_true.mp (rkmHd (rkmT8 ptail_256)))).trans pw_r512_s0_2
private theorem pw_r512_s1_1 :
    muxFastIterFullT16 45 513 phbv_r512_s1
      rkmViHiHiB_m256_r512_s1_c0 = pvm_r512_s1_2 :=
  (muxFastIterFullT16_add 23 22 513
    phbv_r512_s1 rkmViHiHiB_m256_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 22 513 phbv_r512_s1)
      (muxFastIterBSlideChk_sound dk_r512_s1_0)).trans
      (muxFastIterBSlideChk_sound dk_r512_s1_1))
private theorem pw_r512_s1_2 :
    muxFastIterFullT16 67 513 phbv_r512_s1
      rkmViHiHiB_m256_r512_s1_c0 = pvm_r512_s1_3 :=
  (muxFastIterFullT16_add 45 22 513
    phbv_r512_s1 rkmViHiHiB_m256_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 22 513 phbv_r512_s1)
      pw_r512_s1_1).trans
      (muxFastIterBSlideChk_sound dk_r512_s1_2))
private theorem pw_r512_s1_3 :
    muxFastIterFullT16 89 513 phbv_r512_s1
      rkmViHiHiB_m256_r512_s1_c0 = rkmVoHiHiB_m256_r512_s1_c0 :=
  (muxFastIterFullT16_add 67 22 513
    phbv_r512_s1 rkmViHiHiB_m256_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 22 513 phbv_r512_s1)
      pw_r512_s1_2).trans
      (muxFastIterBSlideChk_sound dk_r512_s1_3))
/-- Certified `T_16` walk segment `m256_r512_s1_c0`. -/
theorem rkmWalkChkHiHiB_m256_r512_s1_c0 :
    muxFastIterFullT16 89 513
      rkmHbHiHiB_m256_r512_s1_c0 rkmViHiHiB_m256_r512_s1_c0 = rkmVoHiHiB_m256_r512_s1_c0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 89 513 h rkmViHiHiB_m256_r512_s1_c0)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl (rkmT8 ptail_256))))).trans pw_r512_s1_3
end
end QuantumComputation.Specs.DickeSol
