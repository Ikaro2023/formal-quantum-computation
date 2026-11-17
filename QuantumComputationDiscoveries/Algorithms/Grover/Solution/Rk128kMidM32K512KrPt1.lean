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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kEngine

/-
# `(32, 512)` `degP <= 64` Krotov `RampKick128k` Part 1 (`Rk128kMidM32K512KrPt1`)

Certifies Slice 1 (`r = 512` segments `57..79`, `23` segments, `428,032` F1272 /
`428,868 <= 450,000` Horner coord-ops, `dk = 15`, `lTableMax = 32`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kMidM32K512KrPt1

@[expose] public section

open QuantumComputation.Specs.DickeSol

/-- Segments `57..79` (`23` segments) of `(32, 512)` `r = 512` at `lTableMax = 32`. -/
def mm32k512krS1Segs : List Rkm128kSeg := [
  ⟨16, 561392, 1, 40,
    rkm128kMask56 513 [19980243948895534, 46528398448920934, 68019920392021880,
      19648541246173307, 235, 8813272891392, 1073741824, 4460855993319424, 23493996969391421,
      507]⟩,
  ⟨16, 280812, 1, 24,
    rkm128kMask56 510 [11865013785097445, 16875914114294004, 61259317825494568,
      39476895604295700, 6154, 16777216, 2199291691010, 17777247595397120, 64733373313771513,
      54]⟩,
  ⟨17, 271183, 1, 24,
    rkm128kMask56 509 [38959888528388008, 53192583367778170, 37997593127426702,
      8774666836843081, 111931, 0, 562949953421824, 53726536179646464, 22881183567525839, 18]⟩,
  ⟨17, 272956, 1, 25,
    rkm128kMask56 512 [6145356642661485, 18564408389250372, 41549607589204041,
      5351705457863561, 3690177, 18084767253659648, 140772117577760, 9684507007451136,
      26555286240193655, 247]⟩,
  ⟨17, 272725, 1, 24,
    rkm128kMask56 512 [1384731919413442, 46604602657238001, 13714601617478427,
      12641757745754419, 126428911, 1048576, 8606711808, 55188886644604928,
      60445384164349328, 244]⟩,
  ⟨17, 275614, 1, 25,
    rkm128kMask56 512 [31125735576555679, 38908433695830081, 36315481458327734,
      51833495945727267, 3342338048, 524288, 2199023255552, 52917847524900864,
      46665050496630625, 159]⟩,
  ⟨17, 274972, 1, 24,
    rkm128kMask56 510 [3223178071007788, 47247565921724611, 12822976942256066,
      26425523859409503, 133215126403, 0, 549755813888, 40004631065003008, 41041740852130772,
      62]⟩,
  ⟨18, 266548, 1, 25,
    rkm128kMask56 512 [43467274701507243, 40943947335024034, 38083789887012098,
      19747710242458976, 1755787085015, 4503599895805952, 137472507904, 9077567998918656,
      22864767986642684, 194]⟩,
  ⟨18, 268582, 1, 25,
    rkm128kMask56 513 [29503784355368953, 53345147471353691, 68789533931677826,
      16810888543971011, 57691899957902, 2251799813685248, 549755813888, 2251799847239680,
      5295124969447424, 301]⟩,
  ⟨18, 268761, 1, 25,
    rkm128kMask56 509 [45398561481967701, 27839868547515712, 29025680439897564,
      41868568333169, 2030003447477966, 2216203124736, 70506720010240, 562958677573888,
      16200935944144962, 30]⟩,
  ⟨18, 268109, 1, 25,
    rkm128kMask56 510 [47118863828919648, 9840186769016058, 58286742215717379,
      2688875764609397, 66378124039095493, 0, 0, 4503633987109952, 65458176996217344, 52]⟩,
  ⟨19, 259905, 1, 25,
    rkm128kMask56 513 [31328509904604219, 40110331520696909, 45943009689931880,
      28220962643990727, 46301834876295170, 70368744177675, 36028797018963968,
      175921893998592, 41777767663019137, 352]⟩,
  ⟨19, 261705, 1, 25,
    rkm128kMask56 511 [43271474076588050, 69371396678674495, 8520570030175286,
      31254847124405582, 36116486854342624, 562949953421803, 283678294933504,
      316659348799488, 30776544364363776, 80]⟩,
  ⟨20, 475760, 2, 25,
    rkm128kMask56 513 [19173801243305230, 23572866270579496, 4754008375830316,
      48991287369531915, 45911929204288801, 230962, 8592032256, 18142076076032,
      68720382975148546, 336]⟩,
  ⟨20, 476769, 2, 25,
    rkm128kMask56 512 [5942515372104884, 653497914726339, 61675025454348502,
      8648486265907751, 67527710619992032, 124192122, 67108992, 9007199330246660,
      4316808286867456, 213]⟩,
  ⟨22, 447722, 2, 25,
    rkm128kMask56 513 [8271351924540355, 33302184651268938, 71639499052267649,
      41221826012941298, 11265609060909091, 60408497920, 0, 141836999983112,
      21783774819778560, 480]⟩,
  ⟨22, 449264, 2, 25,
    rkm128kMask56 513 [46976649806703375, 8465962818758061, 26367702376723988,
      61082117064763363, 16625616464779107, 15723869281904, 8796227239936, 35184380477440,
      13702732720374272, 299]⟩,
  ⟨23, 443480, 2, 25,
    rkm128kMask56 513 [17821886970518607, 25669280844579985, 8551566034501490,
      1966638890785770, 9909341155516161, 8233720276467928, 562984850030592, 134217736,
      54396431372648448, 286]⟩,
  ⟨23, 438413, 2, 25,
    rkm128kMask56 508 [66792217098420784, 9471888921567828, 46496169473305922,
      9012813233356153, 6078705985002469, 34300936610501004, 1099511627805, 274953404416,
      61873921672085632, 8]⟩,
  ⟨25, 423827, 2, 25,
    rkm128kMask56 513 [45697512779292264, 58097257015691434, 9939905180110221,
      59853346462622076, 857771799158116, 9333204453165334, 14368, 524288, 36615128801607744,
      501]⟩,
  ⟨25, 419532, 2, 25,
    rkm128kMask56 512 [51644866191686845, 10979771674782708, 2325484227679884,
      32752672807159375, 37095366285234948, 48365660525513434, 3774045, 532480,
      29591225695338500, 200]⟩,
  ⟨26, 411641, 2, 25,
    rkm128kMask56 512 [17710661992792341, 67006635168619195, 6146485357308389,
      45596171898760719, 12923149706863621, 20310199661003488, 1009255440, 4503599627894784,
      25693665013792768, 154]⟩,
  ⟨26, 412327, 2, 25,
    rkm128kMask56 512 [57321532248741570, 54638094448791501, 8704227069436586,
      40937223437983549, 65579063425891711, 1994928858159561, 213666503698, 0,
      12033142227599872, 148]⟩]

/-- Input multiplexing factor entering `mm32k512krS1Segs` (`16`). -/
def mm32k512krS1LIn : ℕ := 16

/-- Input Hilbert dimension entering `mm32k512krS1Segs` (`512`). -/
def mm32k512krS1DCurIn : ℕ := 512

/-- Input accumulated `10^15`-scale error pad entering `mm32k512krS1Segs`. -/
def mm32k512krS1PadIn : ℕ := 494071466

/-- Slice `0` (`64` entries) of `mm32k512krS1VecIn`. -/
def mm32k512krS1VecIn0 : List ℤ :=
  [Int.negSucc 13040, Int.ofNat 96124, Int.ofNat 56367, Int.negSucc 8472, Int.negSucc 130849,
   Int.negSucc 253013, Int.negSucc 255219, Int.ofNat 342555, Int.ofNat 323573,
   Int.negSucc 24141, Int.negSucc 798003, Int.negSucc 453488, Int.ofNat 631577,
   Int.ofNat 1094706, Int.negSucc 167178, Int.negSucc 349963, Int.ofNat 837620,
   Int.negSucc 3292344, Int.negSucc 2820189, Int.negSucc 1399850, Int.ofNat 757113,
   Int.ofNat 3865879, Int.negSucc 32620, Int.ofNat 246645, Int.negSucc 2277808,
   Int.negSucc 1249147, Int.negSucc 1695215, Int.ofNat 4112129, Int.ofNat 245116,
   Int.ofNat 3128410, Int.ofNat 2737149, Int.negSucc 5720123, Int.ofNat 4750767,
   Int.ofNat 4518235, Int.ofNat 81017, Int.negSucc 1254654, Int.negSucc 585707,
   Int.negSucc 3903898, Int.negSucc 3953813, Int.negSucc 4268068, Int.ofNat 10952265,
   Int.ofNat 13661928, Int.ofNat 17110863, Int.ofNat 6218830, Int.ofNat 3209144,
   Int.negSucc 13694962, Int.negSucc 25613167, Int.negSucc 6699735, Int.ofNat 14954067,
   Int.ofNat 7462145, Int.negSucc 35250419, Int.negSucc 21628457, Int.ofNat 31738068,
   Int.ofNat 32249335, Int.ofNat 23394505, Int.negSucc 7356940, Int.negSucc 25774773,
   Int.negSucc 37182444, Int.negSucc 3899332, Int.negSucc 10796236, Int.ofNat 51773788,
   Int.ofNat 15839951, Int.ofNat 166815648, Int.ofNat 99454854]
/-- Slice `1` (`64` entries) of `mm32k512krS1VecIn`. -/
def mm32k512krS1VecIn1 : List ℤ :=
  [Int.negSucc 119984579, Int.negSucc 45772572, Int.negSucc 136318871, Int.negSucc 96379299,
   Int.ofNat 78482324, Int.ofNat 207911153, Int.negSucc 87203185, Int.negSucc 253002684,
   Int.negSucc 139955206, Int.negSucc 92208770, Int.negSucc 180287731, Int.ofNat 760297127,
   Int.ofNat 283362582, Int.ofNat 359908218, Int.ofNat 381002488, Int.negSucc 224042146,
   Int.negSucc 277700563, Int.negSucc 22498626, Int.ofNat 177228985, Int.ofNat 590906196,
   Int.ofNat 144034853, Int.negSucc 451280337, Int.negSucc 1004885605, Int.ofNat 385774838,
   Int.negSucc 484507247, Int.ofNat 348037076, Int.ofNat 1255664658, Int.ofNat 978602241,
   Int.ofNat 445040541, Int.ofNat 741341728, Int.ofNat 870435046, Int.negSucc 489026653,
   Int.ofNat 794104936, Int.negSucc 955574941, Int.ofNat 1139935582, Int.negSucc 1042671360,
   Int.negSucc 1610531492, Int.ofNat 2211283512, Int.ofNat 819559538, Int.ofNat 624148664,
   Int.ofNat 8311971918, Int.ofNat 4233882439, Int.ofNat 6117800621, Int.ofNat 9213618802,
   Int.ofNat 4688071087, Int.ofNat 1168972064, Int.negSucc 141071910, Int.negSucc 6403612772,
   Int.negSucc 1930352154, Int.ofNat 7910598, Int.ofNat 7849908083, Int.negSucc 4134789328,
   Int.negSucc 14494059351, Int.negSucc 5048230386, Int.ofNat 1424699045,
   Int.negSucc 12554489482, Int.negSucc 3666054511, Int.negSucc 1249386274,
   Int.negSucc 17329707386, Int.negSucc 17773875133, Int.negSucc 29122005065,
   Int.ofNat 16692455186, Int.ofNat 13709450009, Int.ofNat 3543993896]
/-- Slice `2` (`64` entries) of `mm32k512krS1VecIn`. -/
def mm32k512krS1VecIn2 : List ℤ :=
  [Int.ofNat 27751764295, Int.negSucc 27715432070, Int.negSucc 7676010669,
   Int.negSucc 1202939903, Int.negSucc 25995544515, Int.negSucc 70476537394,
   Int.negSucc 41425907154, Int.ofNat 28440635283, Int.ofNat 45469574971,
   Int.ofNat 151318461126, Int.ofNat 243436280137, Int.ofNat 255496921946,
   Int.ofNat 50616011201, Int.negSucc 98089823031, Int.negSucc 79392752027,
   Int.ofNat 13770592365, Int.ofNat 6884295470, Int.negSucc 91824455517,
   Int.negSucc 151389691531, Int.ofNat 23302909871, Int.negSucc 86705606573,
   Int.negSucc 84091576590, Int.negSucc 7914297506, Int.negSucc 12673047703,
   Int.negSucc 227509386990, Int.negSucc 123240293491, Int.ofNat 35018665921,
   Int.ofNat 45032603538, Int.ofNat 145772415484, Int.ofNat 209833454211,
   Int.negSucc 157061637609, Int.negSucc 581637661081, Int.negSucc 728693322838,
   Int.negSucc 759238228583, Int.negSucc 287524543944, Int.negSucc 178900296197,
   Int.negSucc 299357965966, Int.negSucc 565954204573, Int.ofNat 371418214041,
   Int.ofNat 761877462517, Int.ofNat 934893050258, Int.ofNat 463427433712,
   Int.ofNat 802394866706, Int.ofNat 588996534753, Int.ofNat 488515675576,
   Int.negSucc 516411701816, Int.negSucc 173924081474, Int.ofNat 112321841337,
   Int.negSucc 222742387343, Int.negSucc 281309559668, Int.ofNat 308381801501,
   Int.negSucc 444026184821, Int.ofNat 738986839746, Int.ofNat 745767514724,
   Int.ofNat 1055883788270, Int.ofNat 1186659568358, Int.ofNat 803764612348,
   Int.ofNat 203949942263, Int.negSucc 204466082603, Int.negSucc 1063196277216,
   Int.negSucc 1216822038670, Int.negSucc 14961615836, Int.negSucc 171561050092,
   Int.ofNat 980836197607]
/-- Slice `3` (`64` entries) of `mm32k512krS1VecIn`. -/
def mm32k512krS1VecIn3 : List ℤ :=
  [Int.ofNat 944016935209, Int.negSucc 1953628851662, Int.negSucc 3695672837603,
   Int.negSucc 697901216377, Int.negSucc 949575463828, Int.negSucc 1309409957027,
   Int.negSucc 1708778011695, Int.negSucc 641786319534, Int.negSucc 295702365383,
   Int.negSucc 380506988972, Int.negSucc 1857260713786, Int.ofNat 1114652881413,
   Int.negSucc 2151419160930, Int.ofNat 214167339141, Int.negSucc 2059452668947,
   Int.ofNat 179547677521, Int.ofNat 532656533747, Int.negSucc 596216440517,
   Int.ofNat 1087977245483, Int.negSucc 577926390402, Int.negSucc 324645373181,
   Int.negSucc 1794679917863, Int.negSucc 2972143302902, Int.ofNat 1494732988528,
   Int.ofNat 1676786178407, Int.ofNat 3499683671608, Int.ofNat 2189356638096,
   Int.ofNat 1355343586252, Int.ofNat 4418582134915, Int.ofNat 3975335003041,
   Int.ofNat 2321474090172, Int.ofNat 15816201424514, Int.ofNat 36876733589981,
   Int.ofNat 64997049389206, Int.ofNat 98886685508922, Int.ofNat 136586871760803,
   Int.ofNat 175665779747180, Int.ofNat 213486102335874, Int.ofNat 247492029221203,
   Int.ofNat 275465017272938, Int.ofNat 295727873797290, Int.ofNat 307278264032509,
   Int.ofNat 309852707596982, Int.ofNat 303871819356171, Int.ofNat 290356662292058,
   Int.ofNat 270692693494960, Int.ofNat 246558610171289, Int.ofNat 219588961706533,
   Int.ofNat 191453395898875, Int.ofNat 163495786963258, Int.ofNat 136877544274146,
   Int.ofNat 112423989328609, Int.ofNat 90612330063622, Int.ofNat 71724412891942,
   Int.ofNat 55781180745139, Int.ofNat 42618191448911, Int.ofNat 32013903427204,
   Int.ofNat 23665174347534, Int.ofNat 17208166999491, Int.ofNat 12308926320104,
   Int.ofNat 8675909043458, Int.ofNat 6030545212817, Int.ofNat 4124264369985,
   Int.ofNat 2768713005145]
/-- Slice `4` (`64` entries) of `mm32k512krS1VecIn`. -/
def mm32k512krS1VecIn4 : List ℤ :=
  [Int.ofNat 1828128361690, Int.ofNat 1193115710482, Int.ofNat 770544505524,
   Int.ofNat 488829242672, Int.ofNat 300737666151, Int.ofNat 177507896037,
   Int.ofNat 100261983550, Int.ofNat 54642376906, Int.ofNat 29265242866, Int.ofNat 15766617115,
   Int.ofNat 8705819219, Int.ofNat 4951329433, Int.ofNat 2873847848, Int.ofNat 1676144019,
   Int.ofNat 969046601, Int.ofNat 550636115, Int.ofNat 306328515, Int.ofNat 166693737,
   Int.ofNat 88780497, Int.ofNat 46333080, Int.ofNat 23725249, Int.ofNat 11935823,
   Int.ofNat 5907528, Int.ofNat 2880629, Int.ofNat 1385884, Int.ofNat 658718, Int.ofNat 309625,
   Int.ofNat 143978, Int.ofNat 66212, Int.ofNat 30079, Int.ofNat 13477, Int.ofNat 5942,
   Int.ofNat 2571, Int.negSucc 1081, Int.ofNat 443, Int.ofNat 174, Int.negSucc 65,
   Int.ofNat 22, Int.ofNat 6, Int.ofNat 2, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
/-- Slice `5` (`64` entries) of `mm32k512krS1VecIn`. -/
def mm32k512krS1VecIn5 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Slice `6` (`64` entries) of `mm32k512krS1VecIn`. -/
def mm32k512krS1VecIn6 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Slice `7` (`64` entries) of `mm32k512krS1VecIn`. -/
def mm32k512krS1VecIn7 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Slice `8` (`1` entries) of `mm32k512krS1VecIn`. -/
def mm32k512krS1VecIn8 : List ℤ :=
  [Int.ofNat 0]
/-- Checkpoint fixed-point vector entering `mm32k512krS1Segs` (`513` entries). -/
def mm32k512krS1VecIn : List ℤ :=
  mm32k512krS1VecIn0 ++ (
    mm32k512krS1VecIn1 ++ (
      mm32k512krS1VecIn2 ++ (
        mm32k512krS1VecIn3 ++ (
          mm32k512krS1VecIn4 ++ (
          mm32k512krS1VecIn5 ++ (
          mm32k512krS1VecIn6 ++ (
          mm32k512krS1VecIn7 ++ (
          mm32k512krS1VecIn8))))))))

/-- Output multiplexing factor exiting `mm32k512krS1Segs` (`26`). -/
def mm32k512krS1LOut : ℕ := 26

/-- Output Hilbert dimension exiting `mm32k512krS1Segs` (`512`). -/
def mm32k512krS1DCurOut : ℕ := 512

/-- Output accumulated `10^15`-scale error pad exiting `mm32k512krS1Segs`. -/
def mm32k512krS1PadOut : ℕ := 697075942

/-- Slice `0` (`64` entries) of `mm32k512krS1Vec`. -/
def mm32k512krS1Vec0 : List ℤ :=
  [Int.ofNat 4581, Int.ofNat 9192, Int.ofNat 33718, Int.ofNat 7698, Int.ofNat 25121,
   Int.negSucc 32679, Int.negSucc 40915, Int.ofNat 178697, Int.ofNat 311960, Int.ofNat 160173,
   Int.ofNat 401818, Int.ofNat 90054, Int.ofNat 113948, Int.negSucc 17818, Int.ofNat 72024,
   Int.negSucc 441952, Int.negSucc 95761, Int.ofNat 515367, Int.ofNat 519658, Int.ofNat 854301,
   Int.ofNat 728851, Int.ofNat 954267, Int.negSucc 99616, Int.negSucc 851493,
   Int.negSucc 1504511, Int.ofNat 250345, Int.negSucc 2173416, Int.ofNat 743590,
   Int.negSucc 1452432, Int.ofNat 74727, Int.negSucc 147418, Int.negSucc 516143,
   Int.ofNat 2674770, Int.negSucc 4171926, Int.negSucc 2888382, Int.negSucc 2861578,
   Int.negSucc 1506848, Int.ofNat 3414772, Int.negSucc 2066370, Int.negSucc 4753179,
   Int.ofNat 8540416, Int.ofNat 9416194, Int.ofNat 9145342, Int.ofNat 1795943,
   Int.ofNat 7471132, Int.negSucc 1617144, Int.ofNat 9438779, Int.negSucc 978894,
   Int.negSucc 18959679, Int.negSucc 16441183, Int.negSucc 33042224, Int.negSucc 11517465,
   Int.negSucc 18923742, Int.negSucc 24344000, Int.negSucc 9214877, Int.negSucc 8775986,
   Int.ofNat 35429486, Int.ofNat 73046940, Int.ofNat 100817231, Int.negSucc 122353602,
   Int.negSucc 88864458, Int.negSucc 25357478, Int.negSucc 21518233, Int.ofNat 112242033]
/-- Slice `1` (`64` entries) of `mm32k512krS1Vec`. -/
def mm32k512krS1Vec1 : List ℤ :=
  [Int.negSucc 208162194, Int.negSucc 14332460, Int.negSucc 67380560, Int.ofNat 35241322,
   Int.negSucc 103912275, Int.negSucc 351789573, Int.negSucc 125328407, Int.ofNat 101240261,
   Int.ofNat 65786198, Int.ofNat 285211578, Int.ofNat 521167221, Int.ofNat 231405410,
   Int.negSucc 42011450, Int.negSucc 328983683, Int.ofNat 173294385, Int.ofNat 10906238,
   Int.ofNat 662009221, Int.ofNat 123208438, Int.ofNat 6599294, Int.negSucc 567414,
   Int.ofNat 127996458, Int.ofNat 949417024, Int.ofNat 243437347, Int.ofNat 751039454,
   Int.ofNat 225812268, Int.ofNat 58207719, Int.ofNat 312769148, Int.ofNat 46700119,
   Int.ofNat 8756780, Int.ofNat 399961213, Int.ofNat 55061927, Int.ofNat 848674804,
   Int.ofNat 15275494, Int.negSucc 613182267, Int.negSucc 1110465789, Int.ofNat 233866654,
   Int.ofNat 287980817, Int.ofNat 370081155, Int.negSucc 273250836, Int.ofNat 495600843,
   Int.ofNat 899564203, Int.negSucc 1255983836, Int.ofNat 1913524486, Int.ofNat 2639899877,
   Int.ofNat 510560502, Int.ofNat 14143961, Int.ofNat 1361226977, Int.negSucc 1364122719,
   Int.negSucc 4551223877, Int.negSucc 1370269663, Int.ofNat 2442173635, Int.ofNat 1337295035,
   Int.negSucc 549909233, Int.negSucc 1193441376, Int.ofNat 2399598846, Int.ofNat 1433366230,
   Int.negSucc 3866679715, Int.negSucc 465766400, Int.ofNat 1344351008, Int.negSucc 3633280181,
   Int.negSucc 932894346, Int.negSucc 1490207774, Int.negSucc 11855798853,
   Int.negSucc 9353921734]
/-- Slice `2` (`64` entries) of `mm32k512krS1Vec`. -/
def mm32k512krS1Vec2 : List ℤ :=
  [Int.negSucc 9054077306, Int.negSucc 1358398702, Int.ofNat 1055714989, Int.ofNat 8476940842,
   Int.ofNat 3597437079, Int.ofNat 4349225478, Int.negSucc 6763591161, Int.negSucc 8070031390,
   Int.negSucc 4107487241, Int.ofNat 4610338181, Int.ofNat 9944186580, Int.ofNat 6826332787,
   Int.negSucc 5405953224, Int.ofNat 13683856252, Int.ofNat 7071080606,
   Int.negSucc 13775362043, Int.negSucc 8560866488, Int.negSucc 20115676735,
   Int.negSucc 763776157, Int.ofNat 8749512550, Int.ofNat 16524188633, Int.ofNat 19417614096,
   Int.ofNat 11678322966, Int.negSucc 13745452867, Int.negSucc 10659953685,
   Int.negSucc 22271977557, Int.negSucc 14741949745, Int.negSucc 39437468148,
   Int.negSucc 24951695919, Int.negSucc 4976889971, Int.negSucc 23785287008,
   Int.negSucc 36244822164, Int.negSucc 11932785242, Int.negSucc 30655369317,
   Int.ofNat 27520343303, Int.ofNat 1908479365, Int.negSucc 18295346192,
   Int.negSucc 31730867466, Int.negSucc 9632601630, Int.ofNat 22150178310,
   Int.ofNat 69841311515, Int.ofNat 81399251844, Int.negSucc 11976012766,
   Int.negSucc 10471653383, Int.negSucc 34661423680, Int.ofNat 5645494935,
   Int.ofNat 30194518075, Int.ofNat 44910931093, Int.negSucc 366699421, Int.ofNat 34698809198,
   Int.negSucc 76392595473, Int.negSucc 8046635484, Int.ofNat 4439167855,
   Int.negSucc 30156823922, Int.negSucc 90369375827, Int.negSucc 32557305246,
   Int.negSucc 35855592600, Int.ofNat 64238784519, Int.negSucc 40895029220,
   Int.ofNat 10516624000, Int.negSucc 52086207056, Int.negSucc 14453542849,
   Int.ofNat 65505426108, Int.ofNat 4138155561]
/-- Slice `3` (`64` entries) of `mm32k512krS1Vec`. -/
def mm32k512krS1Vec3 : List ℤ :=
  [Int.negSucc 16674933846, Int.ofNat 6263818686, Int.ofNat 29089471112,
   Int.negSucc 15769737885, Int.negSucc 26497849111, Int.ofNat 55701971791,
   Int.ofNat 67207454701, Int.ofNat 152313824981, Int.ofNat 120551644651,
   Int.ofNat 85037723101, Int.ofNat 43449162119, Int.negSucc 59133872725,
   Int.negSucc 9387153186, Int.negSucc 75907995850, Int.negSucc 59507270209,
   Int.ofNat 130462848832, Int.negSucc 56885882482, Int.negSucc 34587946763,
   Int.ofNat 59638845541, Int.ofNat 118114016930, Int.ofNat 34296554531,
   Int.negSucc 70039216795, Int.ofNat 239770615300, Int.ofNat 245237240901,
   Int.ofNat 113650567920, Int.ofNat 135390331617, Int.ofNat 175655194417,
   Int.negSucc 223540724552, Int.negSucc 218921463815, Int.negSucc 373156775746,
   Int.ofNat 254566487710, Int.ofNat 423419321687, Int.ofNat 143845878082,
   Int.negSucc 176867521935, Int.ofNat 282013555435, Int.ofNat 294933293495,
   Int.ofNat 83050392725, Int.ofNat 88971849331, Int.ofNat 54543928813,
   Int.negSucc 142657021590, Int.negSucc 200626420210, Int.negSucc 142107202024,
   Int.ofNat 411087421831, Int.ofNat 204706499289, Int.ofNat 632886128743,
   Int.ofNat 478970948467, Int.ofNat 1039809105027, Int.ofNat 799704197134,
   Int.ofNat 734897158818, Int.ofNat 394201264284, Int.negSucc 646511884708,
   Int.negSucc 329862583863, Int.negSucc 221011806375, Int.ofNat 1435671084261,
   Int.ofNat 810085989086, Int.negSucc 883726167607, Int.negSucc 1046804572649,
   Int.ofNat 118833933100, Int.ofNat 1267049550916, Int.ofNat 77993745659,
   Int.negSucc 626320185394, Int.negSucc 958722117728, Int.negSucc 855686435862,
   Int.negSucc 1170866565112]
/-- Slice `4` (`64` entries) of `mm32k512krS1Vec`. -/
def mm32k512krS1Vec4 : List ℤ :=
  [Int.negSucc 2158567806390, Int.negSucc 146097608660, Int.negSucc 578257432039,
   Int.ofNat 5180123544, Int.negSucc 1048508898548, Int.ofNat 663299096366,
   Int.negSucc 238140948207, Int.negSucc 323167660489, Int.negSucc 413898833741,
   Int.negSucc 100590723173, Int.ofNat 387005373916, Int.ofNat 3630125121094,
   Int.ofNat 3068719375866, Int.ofNat 5827569948977, Int.ofNat 4935143135909,
   Int.ofNat 4266040023857, Int.ofNat 4983280161825, Int.ofNat 4764481706382,
   Int.ofNat 593312525414, Int.negSucc 1113018564656, Int.negSucc 1288480613603,
   Int.negSucc 2000756811797, Int.negSucc 995348459731, Int.negSucc 2917230013777,
   Int.negSucc 2567603806285, Int.negSucc 386119710786, Int.ofNat 1415724332952,
   Int.ofNat 1478637241372, Int.negSucc 730128706070, Int.negSucc 3346694889009,
   Int.negSucc 4303004574322, Int.ofNat 704221042301, Int.ofNat 3911565330107,
   Int.negSucc 3050094517800, Int.negSucc 8007065238644, Int.ofNat 120602752531,
   Int.ofNat 623283566389, Int.negSucc 2165825692321, Int.ofNat 1478631203920,
   Int.negSucc 4966908904959, Int.ofNat 2285527699242, Int.negSucc 6971119275006,
   Int.ofNat 1821465788322, Int.negSucc 609988441226, Int.negSucc 3213743262859,
   Int.ofNat 1189893628911, Int.negSucc 3723611128626, Int.negSucc 6507188306922,
   Int.ofNat 1490786421182, Int.negSucc 2085044604942, Int.negSucc 4032130351286,
   Int.negSucc 4990805293858, Int.negSucc 4459772395527, Int.ofNat 309477336734,
   Int.ofNat 631303759624, Int.negSucc 606981272336, Int.negSucc 1097761141709,
   Int.ofNat 3781107388425, Int.negSucc 170036486547, Int.negSucc 6847225004499,
   Int.ofNat 4405253553004, Int.ofNat 1625697862621, Int.ofNat 1429631012075,
   Int.negSucc 3890039044563]
/-- Slice `5` (`64` entries) of `mm32k512krS1Vec`. -/
def mm32k512krS1Vec5 : List ℤ :=
  [Int.negSucc 1228569085228, Int.negSucc 4211502897252, Int.negSucc 6153740539259,
   Int.ofNat 5323942240056, Int.ofNat 413343271850, Int.negSucc 3881121174690,
   Int.negSucc 9772112246885, Int.ofNat 1764819925663, Int.ofNat 3892427922380,
   Int.ofNat 5651498671709, Int.ofNat 1893176273362, Int.ofNat 747671126184,
   Int.negSucc 2356423583472, Int.negSucc 4594236923387, Int.negSucc 8684334325171,
   Int.ofNat 891665066122, Int.negSucc 1051689405602, Int.negSucc 4159123678150,
   Int.negSucc 5602917564820, Int.negSucc 7063118896797, Int.negSucc 5625385539265,
   Int.negSucc 3357286045299, Int.negSucc 1409901570685, Int.ofNat 6155196295435,
   Int.ofNat 2792784980740, Int.ofNat 5366630079578, Int.ofNat 2415952077333,
   Int.ofNat 2315172559332, Int.negSucc 2674863373863, Int.ofNat 5142822269903,
   Int.negSucc 1117662036904, Int.ofNat 2934868168975, Int.ofNat 1761173548530,
   Int.ofNat 873820304958, Int.ofNat 3124829755941, Int.ofNat 7075732187957,
   Int.negSucc 3856221646259, Int.negSucc 5584818139747, Int.negSucc 2196140079856,
   Int.ofNat 6332600730936, Int.ofNat 8925870869816, Int.negSucc 4610474759112,
   Int.negSucc 4501034035920, Int.ofNat 7316051842416, Int.ofNat 4682200806052,
   Int.negSucc 4186077653817, Int.ofNat 2448127997837, Int.ofNat 3182246299816,
   Int.ofNat 1428347969059, Int.ofNat 4347429810282, Int.ofNat 4681323249436,
   Int.negSucc 2279837242105, Int.ofNat 9495704757773, Int.ofNat 7619532834795,
   Int.ofNat 9610616246679, Int.ofNat 43642797717951, Int.ofNat 91516818990749,
   Int.ofNat 147306207352762, Int.ofNat 204123369687239, Int.ofNat 255792626321356,
   Int.ofNat 297528667245986, Int.ofNat 326014235954622, Int.ofNat 339577917880355,
   Int.ofNat 338438441910718]
/-- Slice `6` (`64` entries) of `mm32k512krS1Vec`. -/
def mm32k512krS1Vec6 : List ℤ :=
  [Int.ofNat 324511039270908, Int.ofNat 300693650088540, Int.ofNat 270098312033906,
   Int.ofNat 235630816403537, Int.ofNat 199883039614843, Int.ofNat 165080022693171,
   Int.ofNat 132955669437650, Int.ofNat 104629835062120, Int.ofNat 80597161238092,
   Int.ofNat 60844617141119, Int.ofNat 45031871164491, Int.ofNat 32658285544778,
   Int.ofNat 23179493169796, Int.ofNat 16072530212735, Int.ofNat 10865237523444,
   Int.ofNat 7145919482279, Int.ofNat 4563796954249, Int.ofNat 2826362232396,
   Int.ofNat 1696064342371, Int.ofNat 986290078025, Int.ofNat 556385947715,
   Int.ofNat 305038918506, Int.ofNat 163085529027, Int.ofNat 85310227173,
   Int.ofNat 43884815540, Int.ofNat 22325977304, Int.ofNat 11255535715, Int.ofNat 5649185855,
   Int.ofNat 2855862205, Int.ofNat 1456594646, Int.ofNat 731969729, Int.ofNat 350355471,
   Int.ofNat 156898660, Int.ofNat 66468638, Int.ofNat 27713304, Int.ofNat 11968128,
   Int.ofNat 5501690, Int.ofNat 2648807, Int.ofNat 1286433, Int.ofNat 612147, Int.ofNat 281990,
   Int.ofNat 125863, Int.ofNat 54840, Int.ofNat 23538, Int.ofNat 10011, Int.ofNat 4221,
   Int.ofNat 1753, Int.ofNat 707, Int.ofNat 271, Int.ofNat 95, Int.ofNat 30, Int.ofNat 8,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
/-- Slice `7` (`64` entries) of `mm32k512krS1Vec`. -/
def mm32k512krS1Vec7 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Slice `8` (`1` entries) of `mm32k512krS1Vec`. -/
def mm32k512krS1Vec8 : List ℤ :=
  [Int.ofNat 0]
/-- Checkpoint fixed-point vector exiting `mm32k512krS1Segs` (`513` entries). -/
def mm32k512krS1Vec : List ℤ :=
  mm32k512krS1Vec0 ++ (
    mm32k512krS1Vec1 ++ (
      mm32k512krS1Vec2 ++ (
        mm32k512krS1Vec3 ++ (
          mm32k512krS1Vec4 ++ (
          mm32k512krS1Vec5 ++ (
          mm32k512krS1Vec6 ++ (
          mm32k512krS1Vec7 ++ (
          mm32k512krS1Vec8))))))))

end

public section

open QuantumComputation.Specs.DickeSol

private abbrev s1P : ℕ → ℤ := Int.ofNat
private abbrev s1N : ℕ → ℤ := Int.negSucc
private def s1NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem s1NatEq_eq {x y : ℕ} (h : s1NatEq x y = true) : x = y := by
  unfold s1NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def s1IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat x, Int.ofNat y => s1NatEq x y
  | Int.negSucc x, Int.negSucc y => s1NatEq x y
  | _, _ => false
private theorem s1IntEq_eq {a b : ℤ} (h : s1IntEq a b = true) : a = b := by
  cases a with
  | ofNat x =>
    cases b with
    | ofNat y => exact congrArg Int.ofNat (s1NatEq_eq h)
    | _ => cases h
  | negSucc x =>
    cases b with
    | ofNat _ => cases h
    | negSucc y => exact congrArg Int.negSucc (s1NatEq_eq h)
private def s1IntListEq (xs ys : List ℤ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (s1IntEq x y) (s1IntListEq xr yr) false
  | _, _ => false
private theorem s1IntListEq_eq {xs ys : List ℤ}
    (h : s1IntListEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [s1IntListEq] at h
      cases hxy : s1IntEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (s1IntEq_eq hxy) (ih h)
private def s1SegStateAt (st : ℕ × ℕ × ℕ × List ℤ) (l d p : ℕ) (v : List ℤ) : Bool :=
  match st with
  | (ls, ds, ps, vs) =>
    Bool.and (s1NatEq ls l)
      (Bool.and (s1NatEq ds d) (Bool.and (s1NatEq ps p) (s1IntListEq vs v)))
private theorem s1SegStateAt_eq {st : ℕ × ℕ × ℕ × List ℤ} {l d p : ℕ} {v : List ℤ}
    (h : s1SegStateAt st l d p v = true) : st = (l, d, p, v) := by
  rcases st with ⟨ls, ds, ps, vs⟩; unfold s1SegStateAt at h; dsimp only at h
  simp only [Bool.and_eq_true] at h; rcases h with ⟨hl, ⟨hd, ⟨hp, hv⟩⟩⟩
  rw [s1NatEq_eq hl, s1NatEq_eq hd, s1NatEq_eq hp, s1IntListEq_eq hv]
private theorem s1Step {b rest : List Rkm128kSeg}
    {l0 p0 l1 p1 l2 p2 : ℕ} {v0 v1 v2 : List ℤ}
    (h1 : s1SegStateAt (rkm128kRunSegs 32 32 512 b l0 512 p0 v0) l1 512 p1 v1 = true)
    (h2 : rkm128kRunSegs 32 32 512 rest l1 512 p1 v1 = (l2, 512, p2, v2)) :
    rkm128kRunSegs 32 32 512 (b ++ rest) l0 512 p0 v0 = (l2, 512, p2, v2) := by
  rw [rkm128kRunSegs_append, s1SegStateAt_eq h1]; exact h2
private def s1B0 : List Rkm128kSeg := mm32k512krS1Segs.take 2
private def s1B1 : List Rkm128kSeg := (mm32k512krS1Segs.drop 2).take 3
private def s1B2 : List Rkm128kSeg := (mm32k512krS1Segs.drop 5).take 3
private def s1B3 : List Rkm128kSeg := (mm32k512krS1Segs.drop 8).take 3
private def s1B4 : List Rkm128kSeg := (mm32k512krS1Segs.drop 11).take 2
private def s1B5 : List Rkm128kSeg := (mm32k512krS1Segs.drop 13).take 1
private def s1B6 : List Rkm128kSeg := (mm32k512krS1Segs.drop 14).take 1
private def s1B7 : List Rkm128kSeg := (mm32k512krS1Segs.drop 15).take 1
private def s1B8 : List Rkm128kSeg := (mm32k512krS1Segs.drop 16).take 1
private def s1B9 : List Rkm128kSeg := (mm32k512krS1Segs.drop 17).take 1
private def s1B10 : List Rkm128kSeg := (mm32k512krS1Segs.drop 18).take 1
private def s1B11 : List Rkm128kSeg := (mm32k512krS1Segs.drop 19).take 1
private def s1B12 : List Rkm128kSeg := (mm32k512krS1Segs.drop 20).take 1
private def s1B13 : List Rkm128kSeg := (mm32k512krS1Segs.drop 21).take 1
private def s1B14 : List Rkm128kSeg := mm32k512krS1Segs.drop 22
private def s1V0S0 : List ℤ :=
  [s1P 41464, s1N 24058, s1P 6209, s1N 109622, s1P 5978, s1P 135591, s1N 40881, s1P 446262,
   s1N 128517, s1P 363972, s1P 213000, s1P 697548, s1P 1963701, s1N 524433, s1N 614014,
   s1P 445921, s1P 281464, s1N 106615, s1P 2853253, s1N 685908, s1N 2537023, s1N 2085081,
   s1P 891282, s1P 979370, s1P 6805185, s1N 2612336, s1N 824381, s1P 1396815, s1N 3709574,
   s1P 1002264, s1P 1498975, s1N 3826816, s1N 3526444, s1P 3230871, s1N 2439065, s1P 4429426,
   s1N 2474371, s1N 2309908, s1P 4006441, s1P 1160953, s1P 3623151, s1N 3710835, s1N 127725,
   s1N 8047616, s1N 1898645, s1P 16692972, s1P 36572916, s1N 26292433, s1P 10873359,
   s1P 12172846, s1P 19072078, s1N 23330519, s1N 15867346, s1P 24985435, s1P 8131025,
   s1N 20713938, s1N 10348084, s1P 9361449, s1P 69464038, s1N 57903864, s1P 19242641,
   s1N 22233477, s1N 98431436, s1N 50491960]
private def s1V0S1 : List ℤ :=
  [s1N 37295183, s1P 132479533, s1N 20635728, s1P 41210923, s1P 378761844, s1P 333327341,
   s1P 296856672, s1P 32110157, s1P 62308473, s1N 279296564, s1N 191123635, s1P 106034333,
   s1P 135648133, s1N 204523783, s1P 307439993, s1P 689475108, s1N 411899851, s1P 68582640,
   s1N 37951347, s1P 39740817, s1N 456577965, s1N 112790268, s1N 349293044, s1P 413750028,
   s1P 1526839889, s1N 524441153, s1N 1506452354, s1N 168027803, s1P 378740742, s1N 291612358,
   s1P 44959015, s1P 1246637163, s1P 1624059739, s1P 1778860697, s1P 1874686583, s1N 101008741,
   s1P 1441230461, s1P 2658568411, s1P 2390260247, s1P 911804354, s1P 662821904,
   s1P 2279770096, s1N 3358430442, s1P 2604570513, s1P 1488228160, s1P 1254679010,
   s1N 972630652, s1N 3576404502, s1P 4683971781, s1N 5543876494, s1N 6771196482,
   s1N 12042764953, s1P 4310754348, s1N 17852493918, s1N 28528000089, s1N 4574006591,
   s1N 4643728386, s1N 3704485877, s1P 9761429084, s1P 28537877874, s1N 2435053268,
   s1P 2809093184, s1P 11474186315, s1N 12940206129]
private def s1V0S2 : List ℤ :=
  [s1N 1713821621, s1N 1220101050, s1N 7555488259, s1N 22092586451, s1N 26805119332,
   s1N 49497797223, s1N 7548919352, s1P 33949609799, s1P 61340481862, s1N 2308821757,
   s1P 16794174712, s1P 62377164003, s1P 3041324614, s1P 5856177143, s1N 57284419990,
   s1N 60350720359, s1N 18489699955, s1N 91301943475, s1P 67672549768, s1P 145504864247,
   s1P 63231424192, s1P 244281260472, s1P 208373593570, s1P 76581532515, s1N 264851148957,
   s1N 190459484009, s1N 43620727775, s1P 19919939867, s1P 144031836075, s1P 73518485290,
   s1P 75363965591, s1P 150204276407, s1P 17243236096, s1P 190930498301, s1P 158555537089,
   s1N 251378059440, s1P 120693984317, s1P 138945555645, s1P 192415576255, s1N 60454251702,
   s1N 777272045698, s1N 777946010257, s1N 282681954010, s1P 8639360780, s1N 84858765044,
   s1P 363502406286, s1P 522273951936, s1P 888440096727, s1P 553996235177, s1P 582576001567,
   s1P 487902181787, s1P 157783858536, s1P 28401852780, s1P 713232883360, s1N 1449647926417,
   s1P 459472879156, s1N 91034380428, s1P 523379346586, s1P 976665283756, s1P 968356589067,
   s1P 1722285379740, s1P 906636480117, s1P 387790117575, s1P 2236448610128]
private def s1V0S3 : List ℤ :=
  [s1P 421633239199, s1N 475332707244, s1N 318271141333, s1N 1430472255788, s1P 1780052473756,
   s1P 3210437610260, s1N 279945260515, s1N 674465167194, s1P 628871340426, s1P 672811652874,
   s1P 993669243727, s1P 2070078715404, s1N 1086492017237, s1P 547213956046, s1P 449620065422,
   s1P 2860745140600, s1P 1529060249707, s1P 386995420552, s1P 435827164835, s1N 2697437678386,
   s1N 316916673607, s1P 675816022984, s1P 1558967273819, s1P 1726250353018, s1N 1914982043253,
   s1N 340516308461, s1N 3201271004710, s1P 439248952471, s1P 1006289689825, s1N 1990227195096,
   s1P 2916256720123, s1P 5113808935400, s1P 1302611402920, s1P 2953471061472,
   s1N 2343228615110, s1N 188978205179, s1P 1559098387517, s1P 1961531734115,
   s1N 1671494911971, s1N 1884913195608, s1P 2106418331823, s1P 3564768917456,
   s1P 598463574302, s1P 2365286237436, s1P 59206131175, s1P 10427602270134,
   s1P 29768483709405, s1P 57301190972196, s1P 91462810308779, s1P 130050190449166,
   s1P 170453143868293, s1P 209832829616124, s1P 245414512560008, s1P 274825244925094,
   s1P 296288874771688, s1P 308739115565433, s1P 311898947681502, s1P 306229474559538,
   s1P 292766838476381, s1P 272961923012662, s1P 248524854992623, s1P 221230116015017,
   s1P 192731595243075, s1P 164453963792175]
private def s1V0S4 : List ℤ :=
  [s1P 137543616513262, s1P 112837006539020, s1P 90852347692927, s1P 71825746990673,
   s1P 55776354562962, s1P 42566387827788, s1P 31944869479826, s1P 23587322632566,
   s1P 17139233455278, s1P 12255347665865, s1P 8623850029928, s1P 5974414154760,
   s1P 4077667340911, s1P 2743258416539, s1P 1818486539924, s1P 1185961756056,
   s1P 759005438792, s1P 475337679325, s1P 290652642122, s1P 173376779544, s1P 100992521531,
   s1P 57619415528, s1P 32350525010, s1P 17977746890, s1P 9945568973, s1P 5501853210,
   s1P 3050205170, s1P 1694030299, s1P 940158049, s1P 519505749, s1P 284740877, s1P 154301095,
   s1P 82470642, s1P 43408889, s1P 22484286, s1P 11457847, s1P 5745182, s1P 2835928,
   s1P 1379354, s1P 661764, s1P 313296, s1P 146190, s1P 67020, s1P 30050, s1P 13113, s1P 5543,
   s1P 2263, s1P 891, s1N 338, s1P 122, s1P 42, s1P 13, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V0 : List ℤ :=
  s1V0S0 ++
    (s1V0S1 ++
    (s1V0S2 ++
    (s1V0S3 ++
    (s1V0S4 ++
    (mm32k512krS1VecIn5 ++
    (mm32k512krS1VecIn5 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V1S0 : List ℤ :=
  [s1N 45816, s1P 41348, s1P 43890, s1N 60853, s1N 88875, s1N 13519, s1N 150622, s1N 228350,
   s1N 365368, s1N 607805, s1P 265463, s1P 765869, s1P 1210253, s1P 1480750, s1P 477640,
   s1N 1255732, s1P 948444, s1P 648844, s1N 1627508, s1N 1853509, s1P 264401, s1P 1407809,
   s1P 5224740, s1P 4305654, s1N 4824268, s1N 780794, s1N 1609940, s1P 2042382, s1P 314897,
   s1P 2795434, s1N 3124412, s1N 5621527, s1N 2420635, s1N 1690779, s1P 2146973, s1P 3647745,
   s1P 3517992, s1N 2834537, s1P 4893792, s1N 2463994, s1P 303535, s1P 1602409, s1N 3242032,
   s1N 2441799, s1N 12495696, s1N 15945200, s1P 4895050, s1N 25538744, s1N 28394161,
   s1N 18173013, s1N 5084068, s1N 33725902, s1N 33744237, s1N 9702366, s1N 27603900,
   s1P 43969924, s1P 71991400, s1P 73757271, s1P 8156864, s1N 63500252, s1N 5776229,
   s1P 52154065, s1P 34838099, s1P 52777107]
private def s1V1S1 : List ℤ :=
  [s1N 132257531, s1N 39785043, s1P 144758097, s1P 35151046, s1N 47297934, s1N 37839456,
   s1P 69899025, s1N 155834505, s1P 55336521, s1P 441587974, s1P 275223876, s1N 164997092,
   s1P 245046409, s1P 108358726, s1P 161687797, s1P 241284588, s1P 200295474, s1N 253879061,
   s1N 671669599, s1N 341735593, s1N 983276047, s1N 538060602, s1N 27263544, s1P 331912436,
   s1N 763595285, s1N 301602925, s1N 759100039, s1N 200717897, s1P 1916979454, s1P 620535397,
   s1P 896715325, s1P 972734633, s1P 55579365, s1P 2309046960, s1P 2653201862, s1N 3057106003,
   s1N 2414823219, s1N 2156123581, s1N 2348982575, s1P 3663708752, s1N 1451993869,
   s1N 5863707944, s1N 3401212330, s1P 1459675120, s1P 1202102714, s1N 229903103,
   s1N 1780643222, s1N 53930533, s1N 856267365, s1N 6470731307, s1N 8125028574, s1P 7070310284,
   s1N 6718524671, s1N 7199035847, s1N 8222654922, s1N 20392938478, s1N 18617427201,
   s1N 15394730000, s1P 1738565786, s1P 24113331151, s1P 10530315930, s1N 9417903429,
   s1N 11410141178, s1N 21670805750]
private def s1V1S2 : List ℤ :=
  [s1N 1778949481, s1N 2047212945, s1P 6548669947, s1P 20963554824, s1N 15484671440,
   s1N 38542481866, s1N 24633685619, s1N 11758995540, s1P 39741278064, s1P 5712803948,
   s1P 24399541888, s1N 4608712721, s1P 4393123114, s1P 74920990427, s1P 49514767355,
   s1P 53619250002, s1P 92045790792, s1P 58502733189, s1P 8497036821, s1N 54379510991,
   s1N 12463394528, s1N 37828417330, s1N 8085288936, s1N 125735546788, s1N 162104799512,
   s1P 17609789882, s1P 144919841972, s1N 146011783536, s1N 135787335524, s1P 47491330855,
   s1P 31943077988, s1N 16978201135, s1N 417563671086, s1N 171227864341, s1N 140793667387,
   s1N 110832345144, s1P 51548345365, s1N 5868657413, s1P 67662631040, s1P 93498380331,
   s1N 104090165450, s1N 305412779616, s1N 37556619528, s1N 305746368680, s1P 136711501872,
   s1N 31892804360, s1N 50490751631, s1P 346511574121, s1P 19712414666, s1P 804290966263,
   s1P 775044489825, s1P 268381138964, s1N 756232920261, s1N 83970738399, s1N 566579822921,
   s1N 395981929546, s1N 481602843354, s1N 114533190261, s1P 280341706698, s1N 1652546244308,
   s1N 1070638886143, s1N 395426215563, s1P 661913076115, s1P 151721607519]
private def s1V1S3 : List ℤ :=
  [s1N 1206053209021, s1P 646104102474, s1P 553457473614, s1N 2985755626417, s1N 1496463621327,
   s1N 1104204799965, s1N 1700271301655, s1P 2734292075223, s1N 1212138977569,
   s1N 550626719945, s1P 201028993194, s1P 1166100663184, s1N 517180512682, s1P 2078884710015,
   s1P 160078577522, s1N 916139921344, s1N 1289527121998, s1P 1253101398248, s1N 1376003868017,
   s1P 1591215377883, s1N 3668916298986, s1N 2034821181976, s1P 2278908486335,
   s1N 2347896325404, s1P 2675889812500, s1N 1360364236164, s1N 73971503138, s1N 663667006173,
   s1N 2357833287713, s1N 3212823675159, s1N 1588809877776, s1P 1783517286947,
   s1P 2222204138412, s1P 2293542482422, s1P 3703300914496, s1N 3567765142958,
   s1N 4102172397821, s1N 913341005643, s1P 1640344439654, s1N 347431814198, s1P 394376397183,
   s1N 575743471982, s1N 125298585428, s1P 2417286305562, s1N 453942855665, s1P 87163289673,
   s1P 2815201478841, s1N 1255592452818, s1N 2461210744846, s1P 2823065396398,
   s1N 4021715824504, s1P 1397049194544, s1N 1692877089935, s1N 3504962655521,
   s1N 479598518249, s1N 2547908340396, s1N 860852273039, s1P 2901488974569, s1P 2990950579511,
   s1P 4763139031364, s1P 21941729449354, s1P 48245078636670, s1P 82175293535980,
   s1P 121408698557371]
private def s1V1S4 : List ℤ :=
  [s1P 163086032829186, s1P 204133630120333, s1P 241583981023688, s1P 272858932325816,
   s1P 296004763355758, s1P 309852473992764, s1P 314066855626191, s1P 309082533639053,
   s1P 295964102837893, s1P 276228830871598, s1P 251651375864059, s1P 224066065601011,
   s1P 195192920686043, s1P 166513690243469, s1P 139205909515006, s1P 114123428995456,
   s1P 91806864595785, s1P 72514210684227, s1P 56267809872400, s1P 42912822790891,
   s1P 32178334558672, s1P 23731536663459, s1P 17219349788502, s1P 12297086283117,
   s1P 8646835529917, s1P 5988490033114, s1P 4085205721792, s1P 2744236502530,
   s1P 1814034259286, s1P 1178857623738, s1P 752312156987, s1P 471023537476, s1P 289162165156,
   s1P 174052563739, s1P 102785504658, s1P 59630046733, s1P 34050007885, s1P 19183249489,
   s1P 10690584274, s1P 5907794005, s1P 3243908109, s1P 1772116312, s1P 963572151,
   s1P 521280051, s1N 280281635, s1P 149563472, s1P 79081832, s1P 41371171, s1P 21386822,
   s1P 10914883, s1P 5495865, s1P 2729017, s1P 1336074, s1P 644930, s1P 306925, s1P 143909,
   s1P 66338, s1P 29953, s1P 13188, s1P 5635, s1P 2328, s1P 924, s1P 350, s1P 123]
private def s1V1S5 : List ℤ :=
  [s1P 39, s1P 11, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V1 : List ℤ :=
  s1V1S0 ++
    (s1V1S1 ++
    (s1V1S2 ++
    (s1V1S3 ++
    (s1V1S4 ++
    (s1V1S5 ++
    (mm32k512krS1VecIn5 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V2S0 : List ℤ :=
  [s1N 37695, s1N 39602, s1P 1367, s1N 51856, s1P 108321, s1P 5006, s1P 39357, s1P 219524,
   s1N 9275, s1N 496748, s1N 640026, s1N 193849, s1N 102351, s1N 1235326, s1N 154094,
   s1N 679988, s1N 1302752, s1N 1129045, s1N 1701760, s1P 308569, s1P 505573, s1P 2383931,
   s1P 1423356, s1N 789231, s1N 594178, s1N 1553188, s1N 3703687, s1P 1356009, s1N 4338551,
   s1N 5125731, s1N 3153426, s1P 4168705, s1P 2216409, s1P 3267598, s1P 2454944, s1P 2121248,
   s1P 834536, s1N 5090169, s1P 624919, s1P 8516560, s1P 2832883, s1P 6808237, s1N 6827667,
   s1P 5451944, s1P 5271074, s1P 11046654, s1N 7841155, s1P 17179212, s1P 9204772,
   s1P 37737057, s1P 35592592, s1P 24420505, s1P 25143927, s1N 30278298, s1P 77748152,
   s1P 53975738, s1P 48769838, s1P 21655534, s1P 55566675, s1P 10777005, s1P 67473718,
   s1P 131907186, s1P 99877245, s1P 46204160]
private def s1V2S1 : List ℤ :=
  [s1P 14396922, s1N 99722139, s1N 15952287, s1P 7243378, s1P 97027143, s1N 45550030,
   s1N 220270108, s1P 237462392, s1N 320894235, s1N 166621417, s1N 163391307, s1P 25709801,
   s1N 148554707, s1N 422382547, s1P 257717867, s1P 333254975, s1P 578436065, s1N 412378096,
   s1P 75450215, s1P 383650712, s1N 528844373, s1N 211508683, s1P 343095284, s1P 761946210,
   s1P 506982018, s1N 1276577118, s1N 715741865, s1P 16913187, s1N 630169126, s1P 1048063385,
   s1N 329104730, s1P 108475069, s1P 1079036944, s1P 1450872752, s1P 616724298, s1N 180635779,
   s1P 1321672674, s1P 329429949, s1N 3892333923, s1N 1953600242, s1N 1213691912,
   s1P 4579658110, s1P 3461948964, s1P 3089558186, s1P 572960030, s1P 4396265796,
   s1N 3389205167, s1N 1513542820, s1N 718901595, s1P 10064775935, s1N 972507103,
   s1P 6332085083, s1N 8030395454, s1P 5785512331, s1P 2001420355, s1N 2802379099,
   s1P 9608395750, s1N 8186095354, s1N 5647075394, s1P 408548750, s1P 4228915156,
   s1P 9702399807, s1N 2585051143, s1P 32398475972]
private def s1V2S2 : List ℤ :=
  [s1P 439414674, s1P 33971365726, s1N 4482492828, s1N 14195599345, s1N 20877959980,
   s1N 16849085001, s1N 13349821218, s1P 15798362604, s1N 14087700016, s1N 38733989509,
   s1N 8806311143, s1P 2153130545, s1P 31034996470, s1P 12856322594, s1N 15048067265,
   s1P 5560353989, s1N 55048652011, s1N 13360821656, s1P 6263258880, s1N 45454678622,
   s1N 4633092759, s1N 30245286328, s1N 18400704091, s1N 51749844658, s1N 10928368687,
   s1P 31919275454, s1P 134065757060, s1P 21562881211, s1N 183105016318, s1N 146208763161,
   s1P 12604040761, s1P 122488543098, s1N 167643199922, s1N 214217728493, s1N 234712622626,
   s1N 216631435385, s1P 57992889723, s1N 27002690748, s1P 22744869084, s1N 181120000499,
   s1N 276245534532, s1N 281384016601, s1N 106422446172, s1P 414985537483, s1P 121142690324,
   s1N 346794311820, s1N 74421777919, s1N 31551286241, s1N 107076070603, s1N 320910266545,
   s1N 176267969240, s1N 428460448699, s1P 238667675235, s1N 568790255654, s1N 576630170152,
   s1N 822069377519, s1N 835661502082, s1N 873791951415, s1N 1036438890095, s1N 383135072313,
   s1P 896899141622, s1P 701636655613, s1N 867341614542, s1P 447003720878]
private def s1V2S3 : List ℤ :=
  [s1P 740204042301, s1P 2429581335555, s1P 2831605648480, s1P 1988075444681, s1N 592014157221,
   s1N 785737158246, s1P 1060273277228, s1P 1006418640049, s1N 1047522730542,
   s1N 1236151042892, s1P 318836381804, s1P 1205485549102, s1P 2424507058505, s1P 93346956878,
   s1N 1128397533445, s1P 900868842664, s1N 586517516180, s1P 1290764473548, s1P 2838181098395,
   s1N 521800422952, s1N 2003642846462, s1P 362975604795, s1P 1978430884984, s1P 1051306585742,
   s1P 2356364051247, s1N 344172199039, s1N 3684944365004, s1P 1775073097030,
   s1P 2216034549620, s1N 355010569821, s1P 383118420603, s1P 2070723304544, s1N 906802535454,
   s1N 824042497384, s1N 1228476251319, s1N 1176243298126, s1P 1945606405463,
   s1N 4461832672470, s1N 5332636567703, s1N 2204186290931, s1N 1513584683965,
   s1N 3269675101377, s1N 1948897941531, s1N 1480854002495, s1N 4380411266554,
   s1N 2939007577446, s1P 2248155881557, s1P 1883757720032, s1N 1683822720678,
   s1N 2150934594094, s1P 1755618054779, s1N 2869107778868, s1N 2043864396534,
   s1N 1847318458054, s1P 586678029247, s1N 1043806258422, s1P 647082315415, s1P 717625137303,
   s1P 1390400613509, s1N 1657788438098, s1P 3093056315650, s1P 903869874459,
   s1P 1151507807058, s1N 365710005205]
private def s1V2S4 : List ℤ :=
  [s1N 1343180890914, s1P 3963374674916, s1P 2656642692077, s1P 2925893513443,
   s1P 2353793169078, s1P 1187317879421, s1P 814944158190, s1P 2978944517123,
   s1P 4611217663593, s1P 1072980131504, s1P 16599073122012, s1P 42124394079835,
   s1P 76198013827199, s1P 116328679055177, s1P 159401383336731, s1P 202059823042076,
   s1P 241075775248445, s1P 273673501144804, s1P 297777067845693, s1P 312161216292226,
   s1P 316494589905470, s1P 311274517620581, s1P 297670923982417, s1P 277315292994893,
   s1P 252076675336040, s1P 223858125469151, s1P 194432028864093, s1P 165321321891614,
   s1P 137727563454623, s1P 112504288749521, s1P 90169840795072, s1P 70948672822031,
   s1P 54834281983701, s1P 41642368001772, s1P 31096669763606, s1P 22827520150505,
   s1P 16502784239717, s1P 11727806893424, s1P 8213029843150, s1P 5666287226047,
   s1P 3838651929598, s1P 2564308546780, s1P 1690911306406, s1P 1090506420441,
   s1P 687411603866, s1P 430024247293, s1P 268541607581, s1P 163720738547, s1P 94370892275,
   s1P 50723461961, s1P 25841369610, s1P 13009284313, s1N 6755435022, s1P 3660472709,
   s1P 2023090951, s1P 1109148852, s1P 596596974, s1P 316938850, s1P 168675200, s1P 90851682,
   s1P 49511949, s1P 27061088, s1P 14669095, s1P 7818973]
private def s1V2S5 : List ℤ :=
  [s1P 4079206, s1P 2080120, s1P 1037389, s1P 506675, s1P 242686, s1P 114106, s1P 52677,
   s1P 23866, s1P 10600, s1P 4606, s1P 1952, s1P 800, s1N 312, s1P 114, s1P 36, s1P 10, s1P 1,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V2 : List ℤ :=
  s1V2S0 ++
    (s1V2S1 ++
    (s1V2S2 ++
    (s1V2S3 ++
    (s1V2S4 ++
    (s1V2S5 ++
    (mm32k512krS1VecIn5 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V3S0 : List ℤ :=
  [s1N 24361, s1N 52829, s1N 20952, s1P 93451, s1P 38215, s1P 65878, s1P 95358, s1P 84101,
   s1P 51959, s1P 211655, s1P 92661, s1N 358911, s1N 654953, s1N 426813, s1P 199035,
   s1P 1442820, s1P 569797, s1P 260819, s1P 305693, s1P 1937568, s1N 335660, s1P 3160770,
   s1P 908992, s1P 813946, s1P 117454, s1P 3008021, s1P 2190964, s1N 694728, s1N 2871592,
   s1N 2959938, s1P 437849, s1N 1798394, s1P 7679874, s1N 1330493, s1N 2452071, s1P 7075630,
   s1N 431638, s1N 3047485, s1N 5167019, s1N 2395367, s1N 4128028, s1P 8152846, s1P 4169058,
   s1P 10045773, s1N 14425070, s1N 7399744, s1N 21896230, s1N 17057949, s1N 13151657,
   s1P 39631057, s1P 13825625, s1N 42006494, s1P 20322692, s1N 17621082, s1N 57941478,
   s1N 15470193, s1N 35377944, s1N 28834719, s1P 65303478, s1P 19395893, s1N 48776046,
   s1P 75917740, s1P 44013300, s1N 41911075]
private def s1V3S1 : List ℤ :=
  [s1N 62057131, s1P 25938601, s1P 88069592, s1P 86433694, s1N 25194494, s1P 41435525,
   s1N 51077923, s1N 37123291, s1N 356364425, s1N 320451140, s1N 324262894, s1N 23091769,
   s1P 253601103, s1N 162369406, s1P 25148743, s1P 289787828, s1P 240473545, s1N 445105817,
   s1N 56776834, s1P 187475679, s1P 255260825, s1P 461539400, s1P 449922173, s1P 1056806064,
   s1P 204250492, s1P 585158046, s1N 223820900, s1P 759987234, s1P 1239635452, s1P 1568426962,
   s1N 373248413, s1N 324212674, s1P 1009345092, s1P 788241868, s1P 115127816, s1P 610740644,
   s1N 1284853275, s1P 2616631496, s1N 4033960138, s1N 924684388, s1P 2067688841,
   s1P 1848323548, s1N 3329968872, s1P 3505181596, s1P 10080095674, s1P 10691992037,
   s1P 7520068832, s1N 315888565, s1P 1375163949, s1P 4972608869, s1P 3005895308,
   s1P 769790869, s1N 6366042902, s1P 4692844876, s1P 5239919259, s1N 9530098387,
   s1P 9980539326, s1N 2857410969, s1P 9006329100, s1N 7330169533, s1N 733912090,
   s1N 4300842064, s1N 2401321131, s1N 2992566935]
private def s1V3S2 : List ℤ :=
  [s1N 9211160967, s1N 13860063970, s1P 4822154576, s1P 28481449907, s1P 20131282914,
   s1N 5516399942, s1P 17157100348, s1P 1444878045, s1P 15380059295, s1P 1900112687,
   s1N 22825743065, s1N 7544877763, s1P 31894126239, s1P 23694193793, s1P 7098964023,
   s1P 745581412, s1P 22513003164, s1N 52309987038, s1N 24174191439, s1P 7277953060,
   s1P 16880096703, s1P 48594037870, s1P 35718132988, s1N 41878555332, s1N 13612908017,
   s1N 23085787222, s1P 6705837693, s1N 40900888472, s1P 18874643470, s1P 11680611453,
   s1N 10928720846, s1N 43393423973, s1P 3853734633, s1P 16326556648, s1P 146791259351,
   s1P 68165166028, s1P 219382881097, s1P 256725704223, s1P 132418462875, s1P 100749116480,
   s1N 84605491312, s1N 33209509332, s1P 109735633734, s1N 10445713004, s1P 115271939531,
   s1N 216345071461, s1N 145967418659, s1P 358120146572, s1N 103518528068, s1N 891452075682,
   s1P 44189947910, s1P 405035193731, s1N 17973525424, s1N 327731871278, s1P 113576718165,
   s1N 200049376504, s1N 383020195136, s1P 69346823414, s1P 463234281753, s1P 440105795718,
   s1P 183861603679, s1P 605659521140, s1P 216903071384, s1N 138210673414]
private def s1V3S3 : List ℤ :=
  [s1N 1116518692542, s1N 803553709961, s1N 1745361563982, s1N 1273364923190,
   s1N 1667666922611, s1N 1813028957882, s1N 3334576881389, s1N 2024697801671,
   s1P 971336569833, s1P 2152766527843, s1P 1606240376381, s1N 674100325206, s1P 54110399759,
   s1P 1084059606862, s1P 288009635862, s1N 1391099947035, s1N 2566986589727,
   s1N 1403062146923, s1N 892599765401, s1P 2097772128222, s1P 1615784395623, s1P 461883795350,
   s1N 1309402326270, s1P 1492844145649, s1N 191169345514, s1N 2194382580746, s1P 559856104291,
   s1N 2900245778035, s1P 1719173163497, s1N 2246176000223, s1N 3422740122682,
   s1P 555062251561, s1N 1000773065549, s1P 695780124121, s1P 2517689138948, s1P 1494166190591,
   s1P 925381112560, s1P 1022386006077, s1P 162863821245, s1P 279947883015, s1N 142809722212,
   s1P 1290140203525, s1P 924413665127, s1P 4305393106020, s1P 4378763500809,
   s1P 4239892540031, s1P 2341762156430, s1N 62956965452, s1N 1972225384294, s1N 544863122998,
   s1P 3318521665296, s1N 2361933688850, s1N 1122101709237, s1P 439853242712,
   s1N 4499263749161, s1N 4452309905983, s1N 84640844799, s1P 1691213052636, s1N 426376977959,
   s1N 297114784385, s1N 2446253469866, s1P 103630252261, s1N 2004013858140, s1P 1367595832619]
private def s1V3S4 : List ℤ :=
  [s1P 6123741495872, s1P 865120227943, s1P 1935921037904, s1N 581302919383, s1N 2672931218330,
   s1P 3735872190476, s1P 1548736480962, s1N 2133838198776, s1P 397653971304,
   s1N 4434061184599, s1N 212853603923, s1P 2357120561171, s1P 1025186553386,
   s1P 1946687810525, s1N 1313457553500, s1N 384513474979, s1N 3737998478789,
   s1N 1627568538836, s1P 123775085415, s1N 2795088294233, s1P 3406721521666, s1P 526562095289,
   s1P 4013344023918, s1P 635500707904, s1P 13317402910696, s1P 38365119061398,
   s1P 72955010766003, s1P 114292096496661, s1P 158900520433885, s1P 203116978185159,
   s1P 243421673514218, s1P 276841912440419, s1P 301232709716663, s1P 315373365673281,
   s1P 319024526288021, s1P 312828357063957, s1P 298082602295547, s1P 276555778452895,
   s1P 250242978536537, s1P 221150454943166, s1P 191077146353757, s1P 161596000913264,
   s1P 133868773157862, s1P 108723494407520, s1P 86618606754923, s1P 67729247101662,
   s1P 52022317252079, s1P 39262206221191, s1P 29119727543555, s1P 21242929626215,
   s1P 15250092350869, s1P 10775349029808, s1P 7479067939693, s1P 5142257749110,
   s1P 3414014223266, s1P 2330081999985, s1P 1458795217643, s1P 935905490234, s1P 645286295046,
   s1P 398467619628, s1P 200358794804, s1P 86327098757, s1P 39183652462, s1P 20307378219]
private def s1V3S5 : List ℤ :=
  [s1P 12253159725, s1P 7936054580, s1P 4541476214, s1P 2116220418, s1P 871752083,
   s1P 402539950, s1P 242004976, s1P 162612436, s1P 105011661, s1P 63106708, s1P 35767715,
   s1P 19460531, s1P 10314750, s1P 5389132, s1P 2783291, s1P 1405462, s1P 681638, s1P 313897,
   s1P 137789, s1P 58835, s1P 25131, s1P 10955, s1P 4859, s1P 2154, s1P 933, s1P 384, s1P 146,
   s1P 51, s1P 14, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V3 : List ℤ :=
  s1V3S0 ++
    (s1V3S1 ++
    (s1V3S2 ++
    (s1V3S3 ++
    (s1V3S4 ++
    (s1V3S5 ++
    (mm32k512krS1VecIn5 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V4S0 : List ℤ :=
  [s1N 4086, s1N 60626, s1N 31942, s1N 45437, s1P 36871, s1N 56853, s1N 76353, s1P 82704,
   s1P 36003, s1P 101842, s1P 143750, s1P 305697, s1N 240567, s1N 809332, s1N 311835,
   s1P 1022485, s1N 348293, s1N 610257, s1N 464256, s1N 1032299, s1N 2027409, s1N 1801925,
   s1N 124062, s1N 1186555, s1N 1994789, s1P 1040569, s1P 2493575, s1P 974564, s1P 1311023,
   s1P 1156487, s1P 5951344, s1P 5943381, s1P 3206485, s1P 2025969, s1N 2353608, s1N 8056928,
   s1N 537999, s1P 1873114, s1P 7591012, s1N 4495177, s1N 6261876, s1N 2060080, s1N 2584841,
   s1N 15278220, s1N 700214, s1N 15850829, s1N 21103449, s1N 19888527, s1N 32225564,
   s1N 27111020, s1N 20365459, s1N 39731268, s1N 38656468, s1N 15828284, s1P 21438974,
   s1P 21204680, s1N 2507713, s1P 29904163, s1P 28066140, s1P 34088635, s1N 53695842,
   s1N 40984579, s1P 69149675, s1P 66021449]
private def s1V4S1 : List ℤ :=
  [s1N 57772378, s1P 129402875, s1P 5360013, s1N 77849584, s1N 50965606, s1P 44658308,
   s1P 123823491, s1P 28249892, s1P 178118410, s1P 296536365, s1P 436834868, s1P 173222060,
   s1P 385427249, s1P 78156210, s1P 131664746, s1P 8286650, s1P 17011570, s1P 258061498,
   s1N 253055446, s1N 244718583, s1N 136865642, s1P 314018799, s1P 321993267, s1P 475786643,
   s1N 687453562, s1N 866721956, s1N 469320654, s1N 1442112023, s1N 2517098441, s1N 1841433055,
   s1P 830169548, s1N 1503520847, s1P 514549369, s1N 993150562, s1N 1692832190, s1P 1238534180,
   s1N 1103391813, s1N 254936315, s1P 1095505329, s1P 1950673872, s1P 3824053643,
   s1P 2625176525, s1P 2777340687, s1N 1576772993, s1N 3685920700, s1P 1622789438,
   s1N 876111582, s1N 1834854442, s1P 5939466798, s1P 9208531913, s1P 6355095006,
   s1P 620911327, s1N 2714733815, s1N 1214319344, s1P 7754216943, s1P 18405677637,
   s1P 10212583569, s1P 3563418375, s1N 1525726658, s1N 1719565435, s1N 3455557811,
   s1N 659866359, s1P 783585918, s1P 7955211899]
private def s1V4S2 : List ℤ :=
  [s1P 3863778926, s1N 3164547653, s1P 4394075948, s1N 1066466418, s1P 4089587537,
   s1P 4360289949, s1N 18842453121, s1N 21727289741, s1N 26262298496, s1N 23232856874,
   s1N 28188946252, s1N 32130830435, s1N 14096575620, s1P 7555271503, s1P 8803995808,
   s1N 32447583322, s1N 20230260403, s1N 18115814237, s1N 17376754278, s1N 8199993359,
   s1N 6791009205, s1P 19208588742, s1P 40667250855, s1P 11491177259, s1P 21271468664,
   s1P 33806012921, s1N 28941893557, s1N 2101768671, s1P 79990922164, s1P 63291529982,
   s1P 21145595984, s1P 37147839256, s1P 11364881368, s1N 17050141433, s1N 19028149587,
   s1N 41830631279, s1P 85169028900, s1P 5160915594, s1N 76358902931, s1N 54421780897,
   s1N 104164127864, s1N 50495202935, s1N 181225901571, s1N 178536972143, s1N 254380028742,
   s1N 511474842738, s1N 415346384957, s1N 367181561149, s1N 262147239276, s1N 125344308202,
   s1P 230052289998, s1P 409943724959, s1P 508126454569, s1P 210227684430, s1N 55379402355,
   s1N 233997585099, s1N 380740790944, s1N 173972296571, s1N 311836315672, s1N 309998203684,
   s1P 112205422498, s1P 502833461041, s1P 429167749789, s1P 619170827311]
private def s1V4S3 : List ℤ :=
  [s1P 636388311280, s1P 572246022276, s1P 373969425564, s1P 147979129029, s1P 113168772205,
   s1N 419272412990, s1N 553524517612, s1P 62554361231, s1P 147068131474, s1N 505637068452,
   s1N 1242033975589, s1N 1827348527481, s1N 2152002124648, s1N 2862818327786,
   s1N 3466988275355, s1N 2577058026288, s1N 1115675898146, s1P 635458202852,
   s1P 1886265033681, s1P 531480905359, s1N 1086617632850, s1P 113444608916, s1P 251749916939,
   s1P 2250028161737, s1P 3612185149360, s1P 2103546398224, s1P 3076377570660,
   s1P 1663287886314, s1N 1211121116236, s1N 1587531441831, s1P 86584644012, s1P 1533963303577,
   s1P 1487130861930, s1P 1564435457352, s1N 825857231951, s1P 519008123682, s1P 676771416478,
   s1P 684188033812, s1P 766763651724, s1P 2594189200829, s1P 913224542077, s1P 1723724324703,
   s1N 1489358765163, s1P 311459600295, s1N 937994755209, s1N 3299605620164, s1P 650178174945,
   s1N 170134453303, s1P 2311203989345, s1N 2561646965216, s1P 1616913186958,
   s1N 2336881901623, s1N 5230336446238, s1N 2387601165573, s1N 7193424182681,
   s1N 2449236898866, s1N 2740469378817, s1P 1872254652816, s1P 611539661113,
   s1P 2486649891550, s1N 835636718270, s1N 2933299282296, s1N 2610793040589, s1P 4212518008015]
private def s1V4S4 : List ℤ :=
  [s1P 2191840166261, s1N 966530206869, s1N 1135967980268, s1P 1027775604321, s1P 57376739120,
   s1N 3966615564494, s1N 1169155847183, s1N 2380953659681, s1N 2493941535048,
   s1N 1617107244839, s1N 2464078552396, s1N 1086616862427, s1P 2720807416636,
   s1N 4683156276359, s1P 2213886106977, s1P 2714999471761, s1P 608906099197,
   s1P 1199220485251, s1N 2848044284015, s1P 4457111408175, s1P 556405942640, s1P 581706311777,
   s1N 2269246998106, s1N 1842714705480, s1P 4087279001926, s1N 1025751818082,
   s1P 1150380592481, s1P 3787897982948, s1N 2869211452965, s1N 186281565594,
   s1P 1221485733766, s1P 5096196375088, s1P 4730478979000, s1P 5197011940583,
   s1P 26579915022823, s1P 58635386260821, s1P 98880463531490, s1P 143838483187132,
   s1P 189640677628943, s1P 232477705099559, s1P 269031892234615, s1P 296800142018409,
   s1P 314219757851889, s1P 320831486188726, s1P 317027746733112, s1P 304116348366107,
   s1P 283683014056980, s1P 257990519078013, s1P 228899100368589, s1P 198508706284924,
   s1P 168418745420322, s1P 139856642870898, s1P 113871331798583, s1P 90915491738555,
   s1P 71180417544039, s1P 54752480767805, s1P 41396509138343, s1P 30720665184290,
   s1P 22406262482167, s1P 16111136285541, s1P 11407347991618, s1P 7917587629916,
   s1P 5388584287474, s1P 3623650914859]
private def s1V4S5 : List ℤ :=
  [s1P 2421125912309, s1P 1603924284646, s1P 1028231249278, s1P 642117931640, s1P 369727224733,
   s1P 205041301315, s1P 115030166442, s1P 60417623098, s1P 27417036999, s1N 11088651768,
   s1P 4697730098, s1P 2436823167, s1P 1458230018, s1P 883409472, s1P 518606519, s1P 298367780,
   s1P 171161312, s1P 98336940, s1P 56224705, s1P 31717898, s1P 17552208, s1P 9502483,
   s1P 5026266, s1P 2593880, s1P 1303692, s1P 637151, s1P 302667, s1P 139943, s1P 63185,
   s1P 27984, s1P 12208, s1P 5264, s1P 2239, s1P 932, s1P 374, s1P 141, s1P 47, s1P 13, s1P 3,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V4 : List ℤ :=
  s1V4S0 ++
    (s1V4S1 ++
    (s1V4S2 ++
    (s1V4S3 ++
    (s1V4S4 ++
    (s1V4S5 ++
    (mm32k512krS1VecIn5 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V5S0 : List ℤ :=
  [s1P 22459, s1P 38303, s1P 4317, s1P 68724, s1N 65278, s1P 72096, s1N 52348, s1N 29132,
   s1P 104361, s1P 83350, s1P 14221, s1P 65987, s1N 362266, s1N 886136, s1N 445028, s1P 786013,
   s1P 629370, s1P 25324, s1P 520863, s1P 331745, s1P 344506, s1P 849798, s1N 153482,
   s1N 2831458, s1N 368498, s1N 953194, s1P 921447, s1P 2030511, s1P 2483564, s1P 311023,
   s1N 3906503, s1N 2678091, s1P 2424960, s1N 861524, s1P 3299770, s1N 2242696, s1N 7048891,
   s1N 4939852, s1N 10124014, s1N 11332922, s1N 5638069, s1N 5833107, s1P 3140961, s1N 1050674,
   s1N 6121197, s1N 6731058, s1P 378773, s1N 1822286, s1N 9370715, s1N 524427, s1P 10262803,
   s1P 7583553, s1N 38777158, s1N 16353638, s1P 15464934, s1N 7330651, s1N 44863159,
   s1N 25581189, s1N 100697869, s1N 71711638, s1N 26559321, s1P 92224157, s1P 75071783,
   s1P 46094255]
private def s1V5S1 : List ℤ :=
  [s1N 35590367, s1P 68739776, s1P 90581563, s1P 69682531, s1P 47686052, s1N 139522185,
   s1N 193516452, s1P 81838500, s1P 93325644, s1P 83415917, s1P 119342742, s1P 142948008,
   s1N 138806818, s1N 10416355, s1N 4120353, s1P 268048821, s1N 23206233, s1P 400182769,
   s1P 537395053, s1P 2619586, s1P 491825579, s1P 278826432, s1P 635221368, s1P 556649854,
   s1N 1400716799, s1N 785205410, s1P 1449747657, s1P 1755527833, s1N 747198850, s1N 160771038,
   s1N 635389241, s1N 661338181, s1N 1321471202, s1P 492163122, s1P 1477318661, s1P 2012914006,
   s1P 1961682844, s1N 473923329, s1N 1966407669, s1P 1201092605, s1N 1264611715,
   s1P 2370894620, s1N 613327981, s1P 1744752692, s1P 2314584966, s1N 2838192567,
   s1N 555453145, s1P 5787572390, s1P 271965704, s1P 2929093689, s1N 2602333131,
   s1N 1634852968, s1N 523181468, s1P 1464092381, s1N 6821210774, s1N 1757127668,
   s1N 9112385427, s1N 8613955970, s1N 7979104897, s1N 5350748102, s1N 6123146125,
   s1N 7660456188, s1P 1352812038, s1P 13026394254]
private def s1V5S2 : List ℤ :=
  [s1P 12787623864, s1P 6661852682, s1P 6348468589, s1N 2554122732, s1N 2024315183,
   s1N 6365787225, s1P 10196320673, s1P 180796531, s1P 5180060446, s1N 5292037125,
   s1P 6093386821, s1P 20367833286, s1N 9044344190, s1N 12785066817, s1N 1347131120,
   s1P 129431333, s1N 14195799226, s1P 21927202454, s1P 55112251487, s1P 25909465836,
   s1N 6311444661, s1P 25519090315, s1N 16450159818, s1N 19415612551, s1P 19440092580,
   s1P 56655232053, s1P 25224803092, s1N 40714739583, s1N 26576829515, s1P 2146868195,
   s1N 101075694, s1N 98340924535, s1N 30600486078, s1N 495028521, s1P 23873466230,
   s1N 13396638518, s1N 50958711378, s1N 34365321374, s1P 132534628498, s1P 68887627355,
   s1P 14413941780, s1P 36533012275, s1P 59343394165, s1P 47765401810, s1P 25465330909,
   s1P 74360488814, s1N 35734429717, s1N 19926204320, s1N 129814714580, s1N 45543132338,
   s1N 11499635653, s1N 133294673538, s1N 169168088681, s1N 189132455026, s1N 443461058369,
   s1N 381580830348, s1N 511586323885, s1N 595511759846, s1N 62230157156, s1P 276124325283,
   s1P 391767539673, s1P 258384896189, s1N 194564205230, s1N 274173807145]
private def s1V5S3 : List ℤ :=
  [s1N 92581734618, s1N 391788792066, s1N 220095256733, s1P 372814567619, s1P 431515460025,
   s1N 85904666944, s1N 292439989443, s1N 377999200601, s1P 320726506126, s1P 556771159963,
   s1P 1043337098023, s1P 809734698739, s1P 495797890314, s1P 217765776133, s1P 196848989054,
   s1N 288826433958, s1N 958895545362, s1N 876329829166, s1P 256549582229, s1N 271128325937,
   s1N 1315378917565, s1N 1982948419701, s1N 3760375834698, s1N 4176401099912,
   s1N 2785229961413, s1N 756693463644, s1P 401231796773, s1N 90943212990, s1N 167528067114,
   s1P 204240982615, s1N 1188060368642, s1N 985193844631, s1N 549082742021, s1P 4616108869006,
   s1P 3814036283269, s1P 1592934041975, s1P 957594957863, s1P 2215813883849,
   s1P 2382944572358, s1N 1152717840652, s1N 1871984960709, s1P 446656828819,
   s1N 1569949063066, s1N 323464117836, s1N 2450886428906, s1N 4186671284198,
   s1N 1679972107576, s1N 1866772149649, s1P 1684754415823, s1P 2765819914648,
   s1N 115533923295, s1N 722490008559, s1N 1575504633385, s1P 1138036984771, s1N 1486812903292,
   s1P 597305077279, s1P 692390339270, s1N 855351275174, s1N 2044792509964, s1N 1517756103306,
   s1N 1713484364411, s1N 3133534578048, s1N 4217807332835, s1N 8225195536782]
private def s1V5S4 : List ℤ :=
  [s1N 4015138908787, s1P 2663662353352, s1P 1910764286781, s1P 3220264937949,
   s1P 862833266258, s1P 3028573075379, s1P 1617592069120, s1N 747102439563, s1N 2628464013616,
   s1P 4789273470050, s1P 1125583455226, s1N 686199473150, s1P 1314715805963, s1P 365088182924,
   s1N 585199549801, s1N 5423829236120, s1P 803855866025, s1P 1745795953515, s1N 1617803954110,
   s1N 1413404349649, s1N 5527257287142, s1N 3119902414017, s1P 1945530233876,
   s1P 2103978372819, s1P 709931759089, s1N 613961843316, s1P 2577808442996, s1P 359107022424,
   s1N 1099964896885, s1N 1650367309239, s1N 2668573227999, s1N 2433117734690,
   s1P 3061089380057, s1N 3835724542661, s1P 912235188623, s1N 2929222974376, s1P 577145638697,
   s1P 4479126627349, s1P 3340094455479, s1P 2167571587975, s1P 7071879802753,
   s1P 5292100941393, s1P 7091131200484, s1P 31189186345103, s1P 65951980575435,
   s1P 108446336532088, s1P 154920103954686, s1P 201331994029711, s1P 243690406885456,
   s1P 278777932025914, s1P 304299253264122, s1P 318889864825816, s1P 322368071535915,
   s1P 315547615509808, s1P 299839972046503, s1P 277157338093800, s1P 249712506043735,
   s1P 219640128210282, s1P 188772869204513, s1P 158715088925408, s1P 130682668746464,
   s1P 105481332713509, s1P 83481178604979, s1P 64804004958154]
private def s1V5S5 : List ℤ :=
  [s1P 49412332755135, s1P 37021862877835, s1P 27287504982699, s1P 19746119704700,
   s1P 14050033020656, s1P 9822197057944, s1P 6758627644941, s1P 4606781731861,
   s1P 3098824682997, s1P 2034757474471, s1P 1303548152625, s1P 820147801451, s1P 503708520851,
   s1P 295215874632, s1P 161252801840, s1P 81261170679, s1P 38126445736, s1P 17169509250,
   s1P 7798755870, s1P 3762110049, s1P 1970938302, s1P 1101793461, s1P 635760747,
   s1P 369411138, s1P 213595051, s1N 122378859, s1P 69368547, s1P 38844058, s1P 21446078,
   s1P 11648227, s1P 6210126, s1P 3243562, s1P 1657106, s1P 827221, s1P 403297, s1P 192058,
   s1P 89406, s1N 40735, s1P 18189, s1P 7966, s1P 3420, s1P 1435, s1P 582, s1P 226, s1P 80,
   s1P 26, s1P 6, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V5 : List ℤ :=
  s1V5S0 ++
    (s1V5S1 ++
    (s1V5S2 ++
    (s1V5S3 ++
    (s1V5S4 ++
    (s1V5S5 ++
    (mm32k512krS1VecIn5 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V6S0 : List ℤ :=
  [s1N 3114, s1P 60247, s1P 49058, s1P 101713, s1P 5648, s1P 16134, s1P 57914, s1N 32362,
   s1N 106300, s1P 11205, s1N 69981, s1N 8028, s1P 105808, s1P 336705, s1P 526469, s1P 717635,
   s1P 939856, s1P 345097, s1P 439493, s1N 708903, s1N 1703913, s1N 376661, s1P 340225,
   s1N 840841, s1N 1146265, s1P 724722, s1N 57278, s1P 2099050, s1P 1200211, s1P 4348166,
   s1N 1072097, s1N 3979675, s1N 1000389, s1N 2062399, s1N 1326383, s1P 6223331, s1P 674224,
   s1P 596297, s1P 1539821, s1N 1779291, s1N 25860, s1N 1582701, s1P 3966799, s1P 3423772,
   s1P 16871922, s1N 6713545, s1N 10298963, s1P 7417073, s1P 6442564, s1N 9836531, s1P 7786049,
   s1P 34689712, s1P 44926795, s1N 3446431, s1P 2549471, s1P 28880773, s1P 26482696,
   s1N 12969857, s1N 23036273, s1N 9249900, s1N 5510281, s1N 6824598, s1N 44087427, s1P 4716414]
private def s1V6S1 : List ℤ :=
  [s1P 169885777, s1P 47272899, s1P 68366287, s1P 13267517, s1N 45556761, s1P 136497603,
   s1N 190696559, s1N 91390820, s1N 80241085, s1P 196615866, s1P 43577227, s1N 155331401,
   s1N 214096585, s1N 376167272, s1N 76530595, s1P 363503680, s1P 233740306, s1N 367246802,
   s1P 73273701, s1P 37292495, s1P 73975444, s1P 426281810, s1P 1052107403, s1P 758865184,
   s1P 937063426, s1P 314521456, s1N 953288502, s1N 956356069, s1N 1788175090, s1P 525891122,
   s1P 1479526132, s1P 1031889116, s1N 1983537454, s1N 2035672540, s1N 180710648,
   s1P 308431645, s1N 1549370818, s1N 309323809, s1P 1294716026, s1P 53804044, s1N 4819712851,
   s1N 4344906977, s1P 799290462, s1P 516562116, s1P 544009488, s1P 3499238254, s1N 3963313490,
   s1P 1544389622, s1N 2168592550, s1N 1793194364, s1N 3786948328, s1N 1061998870,
   s1P 2121051626, s1N 22754388, s1N 2700887028, s1N 1944807553, s1P 1978301016, s1P 82820216,
   s1P 3268116646, s1P 6244584074, s1N 5172463136, s1P 776057835, s1P 2921338918,
   s1N 11501102788]
private def s1V6S2 : List ℤ :=
  [s1N 2752416029, s1N 905076234, s1N 11054143997, s1P 4514525039, s1P 16952844639,
   s1P 6118302884, s1N 2539466796, s1N 69920442, s1N 9045559516, s1N 22519895786,
   s1N 580455830, s1P 6793589673, s1P 1178340432, s1P 26250376738, s1P 20248607972,
   s1P 9166179178, s1N 24064858007, s1P 6260970821, s1N 6181253282, s1N 10572388038,
   s1N 34597031184, s1N 25982131422, s1N 4009418666, s1N 24085428235, s1N 15302250476,
   s1N 20247695449, s1N 12643581250, s1N 64383189129, s1N 62003453834, s1N 56982180636,
   s1N 3085398284, s1P 12208021186, s1N 25091253231, s1N 43763840890, s1N 36372181450,
   s1N 16969029113, s1N 40791243064, s1P 54788878742, s1P 127007257381, s1P 39777217088,
   s1N 9599749578, s1N 2783647149, s1P 22551821666, s1N 59475739974, s1N 60465158009,
   s1N 56786966308, s1N 50128880605, s1P 52072171901, s1P 131992551890, s1P 81404148387,
   s1P 75918176272, s1N 85286091483, s1N 1882649691, s1N 145367486778, s1N 57120568863,
   s1N 131977890414, s1N 53295381902, s1N 37948102076, s1N 39967777409, s1P 37073492395,
   s1P 107947431550, s1P 138328207856, s1P 229844031080, s1P 493398546138]
private def s1V6S3 : List ℤ :=
  [s1P 709135220746, s1P 701185753859, s1P 223560592143, s1P 149037831658, s1P 4707333829,
   s1P 281230838602, s1P 426050397068, s1P 44769070136, s1N 345069320708, s1N 538626643445,
   s1N 100511404568, s1P 164058721684, s1P 217202504359, s1P 502545287413, s1P 611660313142,
   s1P 668539279513, s1N 351254717970, s1P 223772933064, s1P 85257765782, s1N 770358372708,
   s1N 799851961907, s1N 1408248755200, s1N 201440911059, s1N 803043393119, s1N 1135876272882,
   s1P 533899399693, s1P 379838532018, s1N 682870085455, s1N 1325676398923, s1N 1718318764776,
   s1N 3412804355289, s1N 2686480966638, s1N 3394305816521, s1N 2722447389578,
   s1N 3345685942742, s1P 1252247438598, s1P 2322315632827, s1P 2890814667235,
   s1P 1812499152347, s1P 1253905877947, s1N 284519009386, s1N 2042075513328, s1N 18330491870,
   s1N 3116703765042, s1N 2590974963219, s1N 3594435380155, s1N 1020498627457,
   s1N 1028412278485, s1P 60489774591, s1P 796263337341, s1N 1315269079486, s1N 684774880736,
   s1P 2585306542246, s1P 4752136273880, s1P 2187999315561, s1P 1883923117345,
   s1P 722840000143, s1N 2292544280279, s1N 1054101039368, s1P 1512482305938,
   s1P 1282207797567, s1N 1227397019524, s1N 6892856548, s1P 2655927521364]
private def s1V6S4 : List ℤ :=
  [s1N 1624401063463, s1N 869452522663, s1N 1715773000417, s1N 1430396605561,
   s1N 2912718383557, s1N 6390557941675, s1N 5617811132026, s1N 4939623008121,
   s1N 3692647710484, s1N 4094932728315, s1N 1583161509043, s1N 5657141039532,
   s1P 1445463525524, s1P 200538500593, s1N 2921827935773, s1N 442478812218, s1N 206984552412,
   s1P 312553156951, s1N 2067953140378, s1N 2298783557920, s1P 2619380458800,
   s1P 1290855556990, s1P 3237666100766, s1P 2237810091099, s1P 5288818784265,
   s1P 2457569471716, s1P 66581233671, s1P 4535039708466, s1P 3448740862777, s1P 212672816418,
   s1P 1390577708042, s1N 1277775675995, s1N 1616687895197, s1P 1076601006852,
   s1N 1727364761963, s1P 2971231000404, s1N 3976097638053, s1N 2365732248880,
   s1P 2068824622044, s1N 1372783554593, s1P 3072683019711, s1P 119795236752, s1P 425161602997,
   s1N 3410881469039, s1N 2027740582106, s1N 3800550228681, s1N 7379716559064,
   s1P 4517444117414, s1P 2360756794551, s1P 6834102780215, s1P 2725296792922,
   s1P 13401159729967, s1P 41786595888701, s1P 80428041180800, s1P 125875905205271,
   s1P 173871081569964, s1P 220080834483064, s1P 260630035605488, s1P 292559022898110,
   s1P 313821406382957, s1P 323612791857046, s1P 322222024992593, s1P 310850737662607,
   s1P 291278214863545]
private def s1V6S5 : List ℤ :=
  [s1P 265616046738675, s1P 236152433503101, s1P 205015011357249, s1P 173983927483283,
   s1P 144472518209020, s1P 117481246810474, s1P 93621088791628, s1P 73186614584868,
   s1P 56176464039472, s1P 42346072219968, s1P 31337830124054, s1P 22776602563633,
   s1P 16280427217303, s1P 11458303901597, s1P 7941159067386, s1P 5416085599351,
   s1P 3633824579298, s1P 2397215119665, s1P 1552054205296, s1P 981190819466, s1P 601751981210,
   s1P 355241545254, s1P 200745007546, s1N 108538623106, s1P 56222473079, s1P 28010868135,
   s1P 13641170457, s1P 6674551598, s1P 3325642422, s1P 1655113986, s1P 798894463,
   s1P 373223680, s1P 176380175, s1P 90117727, s1P 51083083, s1P 30863067, s1P 18708789,
   s1P 10978755, s1P 6203643, s1P 3395154, s1P 1793540, s1P 900849, s1N 424416, s1P 187730,
   s1P 79600, s1P 33565, s1P 14572, s1P 6581, s1P 3037, s1P 1384, s1P 611, s1P 253, s1P 96,
   s1P 31, s1P 9, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V6 : List ℤ :=
  s1V6S0 ++
    (s1V6S1 ++
    (s1V6S2 ++
    (s1V6S3 ++
    (s1V6S4 ++
    (s1V6S5 ++
    (mm32k512krS1VecIn5 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V7S0 : List ℤ :=
  [s1P 27555, s1N 35558, s1N 3737, s1P 60410, s1P 95316, s1P 43224, s1P 26636, s1N 109703,
   s1N 25599, s1P 20019, s1N 28975, s1N 48085, s1P 50374, s1N 270437, s1N 171970, s1N 95002,
   s1N 90152, s1N 690457, s1N 377011, s1P 374724, s1P 874845, s1P 2139417, s1P 1376843,
   s1P 62756, s1P 1572837, s1P 697797, s1N 564761, s1N 1938604, s1N 692529, s1N 642574,
   s1N 4403277, s1P 2700958, s1P 2957632, s1P 209100, s1P 4847594, s1N 996126, s1N 498030,
   s1N 6894064, s1N 3180732, s1P 4837206, s1P 3826604, s1N 4401701, s1N 3376182, s1P 971759,
   s1P 11886324, s1P 11445090, s1P 6294125, s1N 113888, s1N 20366230, s1P 1506850,
   s1P 12211031, s1N 7752988, s1N 19871329, s1N 7354296, s1N 31435611, s1N 1181023,
   s1P 44440440, s1P 8642278, s1P 53796366, s1P 31198741, s1P 12318458, s1P 126948030,
   s1P 113476687, s1P 94627829]
private def s1V7S1 : List ℤ :=
  [s1P 73667880, s1N 71467525, s1N 4468401, s1N 72978459, s1N 65382730, s1P 29717982,
   s1P 174502656, s1P 8083663, s1N 14822618, s1N 51445859, s1P 275069782, s1N 144275809,
   s1P 89345314, s1P 110607651, s1P 251382710, s1N 53734601, s1P 508259546, s1N 63909366,
   s1P 585061837, s1P 200225740, s1P 688257386, s1P 384047122, s1N 194022375, s1P 227088915,
   s1P 42999258, s1P 38441653, s1N 410082247, s1N 55013412, s1P 110621760, s1N 466474542,
   s1P 212702964, s1P 1983567648, s1P 1990580750, s1N 632585140, s1N 2554638579,
   s1N 1069750933, s1N 774557229, s1P 2997878312, s1P 4693152389, s1P 3272403769,
   s1N 228809959, s1P 1847363956, s1P 1839521797, s1N 1346072887, s1N 1058438579,
   s1N 1471235587, s1N 953112827, s1N 2867216527, s1P 3842239751, s1N 2330798534,
   s1N 561349250, s1P 1368032653, s1N 3592025457, s1P 2565959944, s1P 5151228034,
   s1P 5930974864, s1P 686799203, s1N 63111726, s1N 8671391654, s1N 4290246276, s1N 3416203827,
   s1P 7907194513, s1N 25316909, s1N 1973892682]
private def s1V7S2 : List ℤ :=
  [s1P 3985001129, s1N 2211446242, s1N 9458615720, s1P 3216406758, s1N 12419073739,
   s1N 16813967851, s1P 3390877105, s1P 667592362, s1N 13072979916, s1P 3404755870,
   s1P 16924944323, s1P 2383318680, s1P 18291247722, s1N 2939528206, s1P 9221524682,
   s1P 5432110487, s1P 12217510807, s1P 21907427629, s1P 19713671421, s1P 16371230665,
   s1N 25811123087, s1N 14570801885, s1N 720519077, s1N 14979493236, s1N 9659957188,
   s1N 13452784714, s1N 12380752808, s1N 4125161694, s1N 11793719455, s1N 17123323652,
   s1N 19506435954, s1P 57171473522, s1P 22842764480, s1N 21563609470, s1P 32755430611,
   s1P 71827534238, s1P 27806734165, s1P 42290736412, s1P 73587687961, s1P 18316347175,
   s1P 72914188570, s1P 82347564006, s1N 20159341659, s1N 125967840232, s1N 25723864804,
   s1P 20417655613, s1N 69384247736, s1N 41425632470, s1N 19396426192, s1N 56772634914,
   s1P 42275466184, s1N 25898844706, s1N 57020367091, s1N 106562122949, s1N 98999302942,
   s1N 38452205796, s1N 13655365563, s1N 144401273788, s1N 29638293822, s1N 125658748922,
   s1P 18074894975, s1P 104246770863, s1N 57139118116, s1N 132697001762]
private def s1V7S3 : List ℤ :=
  [s1N 137452503412, s1N 113869858244, s1N 22522297833, s1N 88248946105, s1N 163115434469,
   s1P 5615200268, s1P 266569095693, s1P 441700646766, s1P 584478218356, s1P 742919011356,
   s1P 581340754557, s1P 395420960128, s1P 756331639669, s1P 370536788287, s1P 270128147135,
   s1P 403027936348, s1P 195098368894, s1N 196478576678, s1N 731911066959, s1N 506778547313,
   s1N 303970442655, s1N 877750374425, s1P 841666010913, s1P 1145968972021, s1P 388268799403,
   s1N 833317515956, s1N 688477215574, s1P 717395684953, s1P 444500992669, s1N 990624969539,
   s1N 449596089070, s1P 1562700827265, s1P 710987438241, s1P 1053391692763, s1P 2056112601311,
   s1N 1153906153540, s1N 395611873273, s1P 520591211420, s1N 836470246921, s1N 2244922601946,
   s1N 3615285545687, s1N 3704236901852, s1N 4759937948225, s1N 2114555013610,
   s1P 647930661464, s1P 1802416313535, s1P 1292431033061, s1P 2175016063720,
   s1N 1684539140564, s1N 398181466313, s1P 939295205704, s1N 279803078710, s1N 4093378838758,
   s1N 3575655872195, s1P 1891337379363, s1P 161406660713, s1N 2608498113769, s1P 9705458207,
   s1N 1248180892488, s1N 3221608381674, s1P 1522521263660, s1P 3754168179494,
   s1P 4122990762231, s1P 756965819889]
private def s1V7S4 : List ℤ :=
  [s1N 1581705256786, s1P 75964720162, s1P 1973115052528, s1N 2936141066916, s1P 969224449313,
   s1P 1658367687481, s1N 971341784106, s1P 1898930321800, s1N 857187262261, s1P 875212965024,
   s1N 2415395958404, s1N 988416778270, s1N 2465780972649, s1N 6061479493902,
   s1N 2402562111500, s1N 4431130519400, s1N 6302816169942, s1N 5295283199701,
   s1N 3536007244317, s1P 1408294267699, s1N 3868859903102, s1P 3112029183217,
   s1P 1636500508682, s1N 969463721164, s1N 2900952740577, s1P 1965592864309,
   s1N 3596059893084, s1N 525816940548, s1N 1649889338266, s1P 661119997287, s1P 5049583946289,
   s1N 570626831466, s1N 4938638136677, s1N 1752445165250, s1N 2203712901986,
   s1P 4046345323249, s1P 4183909746143, s1P 3103589201354, s1N 2932200266583,
   s1N 3744648777467, s1N 3254852545041, s1P 2501734718093, s1P 865470097789,
   s1N 2432889748587, s1N 1572024599574, s1P 1333714328375, s1P 325789913190, s1P 62491872913,
   s1N 417007810155, s1P 2946331564870, s1P 3570210016512, s1N 2535332147833,
   s1P 7871163415835, s1N 5606654411668, s1P 977477725164, s1P 4113006487112, s1P 657651682483,
   s1P 5667263219552, s1P 7976547780140, s1P 416469209346, s1P 19776990300242,
   s1P 52204934381550, s1P 94244590700306, s1P 141964494847380]
private def s1V7S5 : List ℤ :=
  [s1P 190814515370284, s1P 236341933174527, s1P 274784915928459, s1P 303395635947501,
   s1P 320601960515808, s1P 326027187053465, s1P 320351420932158, s1P 305095136419955,
   s1P 282349235478888, s1P 254436514610657, s1P 223615079581300, s1P 191894119640287,
   s1P 160992085229639, s1P 132157691546269, s1P 106352064815140, s1P 83789227468767,
   s1P 64925172588805, s1P 49155228856426, s1P 36708074069377, s1P 26892226518044,
   s1P 19268951308986, s1P 13695416379702, s1P 9588970349157, s1P 6509428806889,
   s1P 4352573819447, s1P 2936819646158, s1P 1963740000371, s1P 1239921307911,
   s1P 715760539575, s1P 378786638388, s1P 190354243040, s1P 95862075269, s1P 50456520650,
   s1P 27813863808, s1P 15595700680, s1P 8628987437, s1P 4631037185, s1P 2400781181,
   s1P 1206313014, s1P 593476611, s1P 291075421, s1P 144895804, s1P 74109410, s1P 39419912,
   s1P 21867001, s1P 12311839, s1P 6718694, s1P 3435798, s1P 1636568, s1P 740913, s1P 330684,
   s1P 150627, s1P 70913, s1P 34103, s1P 16421, s1P 7796, s1P 3619, s1P 1634, s1P 715, s1P 298,
   s1P 116, s1P 40, s1P 12, s1P 2]
private def s1V7 : List ℤ :=
  s1V7S0 ++
    (s1V7S1 ++
    (s1V7S2 ++
    (s1V7S3 ++
    (s1V7S4 ++
    (s1V7S5 ++
    (mm32k512krS1VecIn5 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V8S0 : List ℤ :=
  [s1N 37711, s1N 1096, s1P 21943, s1P 45785, s1P 48467, s1P 16174, s1P 96113, s1P 94940,
   s1N 31930, s1P 133042, s1P 83222, s1P 86905, s1N 20033, s1P 58198, s1N 170344, s1P 3761,
   s1P 485185, s1N 132756, s1N 122945, s1N 565397, s1N 437533, s1P 1067223, s1P 1041524,
   s1P 430823, s1P 864983, s1P 2386610, s1P 1264245, s1N 1988745, s1N 4036641, s1N 3325349,
   s1P 2920431, s1P 245836, s1P 475617, s1P 2182965, s1N 2729625, s1N 791477, s1P 1199069,
   s1N 2583874, s1P 3776278, s1P 6620097, s1N 1127276, s1N 929829, s1P 11613609, s1P 3936510,
   s1P 2677816, s1P 962333, s1P 82376, s1N 1310349, s1N 17262413, s1N 1506376, s1N 38053033,
   s1N 13039163, s1P 8836360, s1N 10729268, s1N 37124646, s1N 27534074, s1N 11359274,
   s1N 34986895, s1N 45913699, s1P 68078116, s1N 9504029, s1P 19831788, s1P 22669818,
   s1N 5243542]
private def s1V8S1 : List ℤ :=
  [s1N 86036037, s1N 112626964, s1N 112969832, s1N 32601747, s1P 251276883, s1P 74633545,
   s1N 226089807, s1P 39791776, s1P 174411797, s1P 477534414, s1N 324331224, s1P 180699239,
   s1N 84213286, s1N 33071662, s1P 81468523, s1P 274873273, s1N 219667487, s1N 168203240,
   s1P 44376046, s1N 66819578, s1N 59291197, s1P 178950913, s1P 273362203, s1P 70525561,
   s1P 129747536, s1N 692544313, s1N 327795415, s1N 551260906, s1P 368652133, s1N 1447628316,
   s1N 128396804, s1P 609928834, s1N 189012530, s1N 1326019384, s1N 387323100, s1N 1814030150,
   s1N 574417417, s1N 1615760388, s1P 2227194714, s1P 1906670473, s1P 3634145705,
   s1P 4083459787, s1P 2806644039, s1N 1521645138, s1P 2815359962, s1P 4066163132,
   s1P 2127861577, s1P 1916304869, s1P 1325667690, s1P 5588746324, s1P 2120457521,
   s1P 2921800116, s1P 2057215326, s1N 364655948, s1N 3095052463, s1N 457686046,
   s1P 2321667427, s1P 64040816, s1P 4232153091, s1P 3698394126, s1P 6833258596,
   s1P 3382637582, s1P 13649408600, s1P 4219877020]
private def s1V8S2 : List ℤ :=
  [s1P 919027948, s1P 2869615117, s1N 459621792, s1N 20558134596, s1N 14196020065,
   s1P 2484934975, s1N 6120978314, s1N 3137581971, s1N 3191708480, s1P 7703592648,
   s1P 10302900164, s1P 830841012, s1P 8032355731, s1N 4332286760, s1N 2265440038,
   s1N 20434788515, s1P 1941870410, s1P 3519681258, s1N 9487957414, s1N 15223931054,
   s1P 11785288252, s1P 14051325292, s1P 18486221727, s1P 8190359005, s1N 13502645404,
   s1P 15743529447, s1N 37455120835, s1N 7990343030, s1N 16062737175, s1N 13670651878,
   s1P 25931828880, s1P 64596762105, s1P 6105412528, s1P 31147064188, s1P 14877652691,
   s1P 42364284256, s1P 4620769074, s1N 9145059071, s1P 30697442543, s1P 28258362259,
   s1N 35065281194, s1P 89323978288, s1P 61349932055, s1P 75955455846, s1P 7549654516,
   s1P 12084505151, s1N 47941903773, s1N 57018223308, s1N 151851176664, s1N 5103711305,
   s1N 59569548450, s1N 27098290160, s1N 43964013132, s1N 51612203038, s1N 63106672469,
   s1N 91043082706, s1N 17832395727, s1P 45628672852, s1N 20854767814, s1P 41138013993,
   s1N 75467426950, s1N 92975261812, s1P 51214431895, s1P 20986380439]
private def s1V8S3 : List ℤ :=
  [s1P 11740939437, s1N 128626187634, s1N 121198514936, s1N 210232654868, s1P 183515814169,
   s1N 1315308084, s1N 155589006961, s1N 85550370078, s1N 134760360873, s1N 134667217705,
   s1N 123108371519, s1P 257854570393, s1P 13160708248, s1N 606242710123, s1N 290088470619,
   s1N 190987123560, s1P 81742759209, s1P 732952860634, s1P 753445647977, s1P 402860354701,
   s1P 346654435258, s1P 831585264527, s1P 625033123511, s1P 358116574800, s1N 213048741415,
   s1P 533837976621, s1P 1325396485885, s1P 2169337037154, s1P 1509682139820,
   s1P 1053817078389, s1P 265741259676, s1N 282897313171, s1N 218993302843, s1N 162608151676,
   s1N 479724314784, s1P 1009445035765, s1P 23444775574, s1P 919267563132, s1P 1547222822264,
   s1P 1605929848383, s1N 174097025722, s1N 1029212615296, s1N 1546029524918, s1N 150327142768,
   s1N 369830229928, s1P 934745346441, s1P 1178564315218, s1N 703679211153, s1N 1767729796229,
   s1P 2270993620721, s1P 6194720296017, s1P 6147879084870, s1P 1639750778262,
   s1P 274705748167, s1N 1990284396562, s1N 500259794368, s1N 2680268739242, s1N 462549225952,
   s1P 1084093077325, s1P 1738780342875, s1P 1172770789959, s1P 1665371326219,
   s1P 4287393524381, s1N 3687743011324]
private def s1V8S4 : List ℤ :=
  [s1N 153768293253, s1N 2924520619595, s1N 3780069057130, s1P 1548793329813,
   s1P 1278346391154, s1N 61115730746, s1N 3583513661064, s1N 1966344325830, s1N 342443122195,
   s1P 2763640959371, s1N 1938203742408, s1P 1057381742084, s1P 1874311724976,
   s1P 2870388327485, s1N 1043034763273, s1N 229125029831, s1N 1423565674244,
   s1N 3260205406543, s1N 4187728277648, s1N 316961028716, s1N 239277951526, s1P 4360707136438,
   s1N 2587916626335, s1N 3884435147824, s1N 6399281457331, s1N 4189878360680,
   s1N 7820729871132, s1N 1085532119014, s1P 248821575387, s1P 1015810706308,
   s1P 1448626976592, s1P 2521665757724, s1P 426840685732, s1P 1100932944428,
   s1P 3881623933184, s1P 2797980296982, s1N 720581810153, s1P 2852798776833,
   s1P 2028994731233, s1N 242855602709, s1N 4782875561934, s1N 6072421402157,
   s1N 3510650998529, s1P 1525056638258, s1P 7931381029644, s1P 5899213125517,
   s1P 752784040707, s1N 1658358688353, s1P 4428365249914, s1N 634210383572, s1N 1192971902448,
   s1P 5262610430747, s1N 3559690731664, s1P 754071400496, s1P 3369777715533,
   s1N 2170568396913, s1P 768723050087, s1N 402465185972, s1N 4154999026987, s1N 4282890240681,
   s1N 1704869507092, s1N 3929333533218, s1N 1278588446262, s1P 7029855820624]
private def s1V8S5 : List ℤ :=
  [s1P 6268897599020, s1P 690796474443, s1P 7513890359879, s1P 6930954928394,
   s1P 5857727794778, s1P 32043024305303, s1P 70142651558330, s1P 116322225987038,
   s1P 166316514578963, s1P 214942413892372, s1P 258297632351014, s1P 292618026787527,
   s1P 315744879390015, s1P 326842550755179, s1P 325928197262052, s1P 314497494855875,
   s1P 294488913677300, s1P 268002592228016, s1P 237608169993906, s1P 205603917622756,
   s1P 173736086192953, s1P 143549417452732, s1P 116188162010709, s1P 92148220438699,
   s1P 71577488982969, s1P 54524791779890, s1P 40824584397870, s1P 30047429549313,
   s1P 21694693992829, s1P 15359842125542, s1P 10702969173088, s1P 7375136683768,
   s1P 5024847817856, s1P 3359198363243, s1P 2177621398757, s1P 1355052212115,
   s1P 805706346491, s1P 458748902592, s1P 252141750107, s1P 135375600718, s1P 71889690306,
   s1P 38107867533, s1P 20229371461, s1N 10725584784, s1P 5647033776, s1P 2936077296,
   s1P 1502985822, s1P 757996969, s1P 378420783, s1P 188617664, s1P 94812381, s1P 48401167,
   s1P 25072674, s1P 13058507, s1P 6748195, s1P 3420479, s1P 1689937, s1P 813557, s1P 383320,
   s1N 178019, s1P 82075, s1P 37748, s1P 17339, s1P 7933]
private def s1V8S6 : List ℤ :=
  [s1P 3595, s1P 1604, s1P 695, s1P 287, s1P 110, s1P 38, s1P 10, s1P 2, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0]
private def s1V8 : List ℤ :=
  s1V8S0 ++
    (s1V8S1 ++
    (s1V8S2 ++
    (s1V8S3 ++
    (s1V8S4 ++
    (s1V8S5 ++
    (s1V8S6 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V9S0 : List ℤ :=
  [s1P 29886, s1P 23051, s1P 7438, s1P 11124, s1P 40862, s1P 69887, s1P 64555, s1P 103155,
   s1P 58728, s1P 82827, s1P 35959, s1N 76179, s1N 196142, s1N 185380, s1N 341532, s1N 111307,
   s1N 295834, s1N 134045, s1N 206535, s1N 112353, s1N 549640, s1P 324677, s1N 724179,
   s1N 1274890, s1P 1100751, s1P 352950, s1P 1267670, s1P 728386, s1N 712268, s1N 5313248,
   s1N 2531620, s1N 2388815, s1P 115582, s1N 3638395, s1N 3155777, s1N 1333273, s1P 2722255,
   s1P 4626538, s1N 4888136, s1N 2806079, s1N 8126960, s1P 2347318, s1N 5045507, s1P 14438495,
   s1P 11834386, s1P 4527562, s1N 7669564, s1N 4889408, s1N 6766780, s1N 15862930, s1P 9661574,
   s1N 8276110, s1P 11723888, s1N 51179582, s1N 52995479, s1N 21859946, s1N 14589444,
   s1N 18174765, s1N 26799270, s1N 2282631, s1N 23749837, s1N 63476597, s1N 34415019,
   s1N 40460035]
private def s1V9S1 : List ℤ :=
  [s1N 187843954, s1P 211292706, s1P 211920530, s1P 175367420, s1N 163672546, s1P 290972247,
   s1P 24137977, s1P 346091861, s1P 227371595, s1P 265859397, s1P 45232149, s1N 156887974,
   s1P 47549444, s1P 75418672, s1P 351667, s1P 158933137, s1P 466003540, s1P 333121308,
   s1N 276966423, s1P 348462219, s1P 520104664, s1P 395301764, s1P 476954763, s1N 208887848,
   s1P 74019162, s1N 8724902, s1P 378117679, s1N 1543179002, s1N 1388297806, s1N 164382856,
   s1P 623081110, s1N 953780709, s1P 671122505, s1N 23926206, s1N 279981690, s1N 1519469479,
   s1N 681277337, s1P 658279039, s1N 1398392471, s1P 2300415936, s1P 1544907107, s1P 97590315,
   s1N 978895557, s1P 94651508, s1P 2746958641, s1N 3331291174, s1N 1357549334, s1P 3599587256,
   s1P 3330230853, s1P 674340423, s1P 4789238678, s1P 228469637, s1N 3764954895, s1N 46777525,
   s1N 5537689250, s1N 1017810621, s1N 1734960920, s1N 5105383319, s1N 4417578824,
   s1N 1537236103, s1N 3887481056, s1N 4626334515, s1P 9756442543, s1P 4136576902]
private def s1V9S2 : List ℤ :=
  [s1P 5069623093, s1P 7988182879, s1P 2330275194, s1P 2126027753, s1P 12096486703,
   s1N 6644291232, s1N 8925064628, s1N 10466856901, s1N 16230126729, s1N 1692377176,
   s1P 5018968134, s1P 5057484020, s1P 1809089680, s1N 13610539083, s1N 15408109142,
   s1N 13328286477, s1N 26269978486, s1N 10579759782, s1N 6240682791, s1N 20221127924,
   s1N 11561934572, s1N 9518441866, s1N 14127799981, s1N 28078889857, s1P 26507066525,
   s1P 7553886255, s1N 12332320724, s1N 19080646289, s1N 3018573707, s1N 19427761508,
   s1P 5435097797, s1P 28323340570, s1N 26888761441, s1N 68851425115, s1P 25622987867,
   s1P 38294311024, s1P 28547740537, s1P 24874145618, s1N 51616110368, s1P 45706155817,
   s1N 1818066307, s1N 65092053910, s1N 1263153676, s1N 6104225894, s1P 69257233005,
   s1N 19521978405, s1P 16059196281, s1N 4727545833, s1P 2939105648, s1N 45352762632,
   s1N 8741858959, s1N 84505964744, s1N 116640666117, s1N 2475611679, s1P 79179542135,
   s1P 65210538882, s1N 34851945220, s1N 120965532699, s1N 16848117161, s1P 128654897577,
   s1N 30804936848, s1P 229115421, s1P 178129637055, s1N 10904062660]
private def s1V9S3 : List ℤ :=
  [s1N 109898898514, s1N 28104984958, s1N 82946987439, s1N 7498478559, s1N 59992907692,
   s1N 243545132231, s1N 185161973378, s1N 157795903515, s1P 235939019982, s1P 87335389912,
   s1P 48779740619, s1N 233272876271, s1N 149401143969, s1N 323870615161, s1N 145984339758,
   s1P 11910079905, s1N 290783261994, s1N 117052377162, s1P 225947868061, s1N 353224420471,
   s1N 201874489063, s1P 181838456537, s1P 661175016744, s1P 486706280894, s1N 146313796219,
   s1N 695239540565, s1P 530761057230, s1P 577755058532, s1P 335453831790, s1P 1027378656827,
   s1P 1011197071077, s1P 330735868049, s1P 713301655235, s1P 467612794375, s1P 332033195418,
   s1P 1294442347325, s1P 1571027835161, s1P 1984650364624, s1P 1272782904302,
   s1P 316176393545, s1P 82008751378, s1N 1067808175382, s1P 712132080212, s1P 541468782306,
   s1P 797593005090, s1P 1798412655954, s1P 119209313498, s1P 2123423231573, s1P 2040206019466,
   s1P 234673452509, s1N 1948275145966, s1P 2625455325358, s1P 2433106318270, s1P 778066412541,
   s1P 1572317458235, s1P 5075494866718, s1P 945390042359, s1N 2120916822889, s1N 228224634265,
   s1P 6477434571675, s1P 4737462742307, s1P 2475533929369, s1N 653909538855, s1P 1036055720439]
private def s1V9S4 : List ℤ :=
  [s1N 2876550742790, s1P 95952548851, s1P 1875461632395, s1N 515814207029, s1P 81317901495,
   s1N 2740139764205, s1N 3827505272091, s1P 2820474481769, s1N 3176160561354,
   s1N 3321913387784, s1P 1025461063263, s1P 2860777865395, s1P 3190419090714,
   s1N 314474513072, s1N 2014641308877, s1N 20667909508, s1P 2439832129977, s1P 161055972051,
   s1N 1704569957367, s1P 2124979294421, s1P 131612024660, s1N 338373076932, s1P 3706353028817,
   s1P 2695260578814, s1N 2689714548123, s1N 3578678258874, s1N 2847752056104,
   s1P 1804904894897, s1P 704831072522, s1P 3655666104367, s1P 52654884148, s1P 2112328681294,
   s1N 2865710224158, s1N 6375253798762, s1N 7063572807795, s1N 4611872554277, s1N 41098151123,
   s1N 1556040018067, s1P 436758509697, s1P 111109697521, s1P 3130985262326, s1N 1578570528376,
   s1P 397089019320, s1P 3779641378918, s1N 2413755000091, s1P 6639614640097,
   s1N 8294186501591, s1N 5065802876064, s1N 4340932495402, s1N 5099349994060,
   s1P 4418113061412, s1P 2348855274910, s1P 4579098972168, s1N 1423797502791,
   s1N 2822845509268, s1P 3128907393471, s1P 438535999786, s1N 699379942195, s1N 3595761809917,
   s1N 1538532019396, s1N 1678060753131, s1P 5831690521265, s1N 1720872868275,
   s1P 1485151528132]
private def s1V9S5 : List ℤ :=
  [s1P 4906141729453, s1N 354860919181, s1N 5619176544432, s1N 3404573370349,
   s1N 2566191106102, s1N 4665535301962, s1P 2695310674757, s1P 4299838264383,
   s1N 8872651620161, s1P 5719370936100, s1P 2356926341041, s1P 7935860425880,
   s1P 3820336194399, s1P 14026787668312, s1P 45602044527520, s1P 88173498182459,
   s1P 137569033398049, s1P 188690602127776, s1P 236474828596688, s1P 276824941239958,
   s1P 306756797796093, s1P 324481160297607, s1P 329661209973065, s1P 323226257794627,
   s1P 306862779475438, s1P 282746881282796, s1P 253406449240377, s1P 221370995856613,
   s1P 188785713077654, s1P 157302921466042, s1P 128166180241485, s1P 102234853185936,
   s1P 79940714791811, s1P 61309559609541, s1P 46121793672191, s1P 34018073591795,
   s1P 24646623149509, s1P 17544133384006, s1P 12322668116895, s1P 8522688879189,
   s1P 5785773419787, s1P 3854575102284, s1P 2498910051222, s1P 1561309201503,
   s1P 945165162514, s1N 560845714515, s1P 324452030803, s1P 178695241876, s1P 91820414428,
   s1P 44134225152, s1P 20508803507, s1N 9737326512, s1P 4938082753, s1P 2669251062,
   s1P 1482041497, s1P 815750735, s1P 437917758, s1P 229251865, s1P 117657271, s1P 59578581,
   s1P 30064369, s1P 15231701, s1P 7679696, s1P 3759688]
private def s1V9S6 : List ℤ :=
  [s1P 1747763, s1N 768920, s1P 327158, s1P 140223, s1P 62883, s1P 29736, s1P 14485, s1P 7049,
   s1P 3352, s1P 1539, s1P 677, s1N 283, s1P 108, s1P 37, s1P 10, s1P 2, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V9 : List ℤ :=
  s1V9S0 ++
    (s1V9S1 ++
    (s1V9S2 ++
    (s1V9S3 ++
    (s1V9S4 ++
    (s1V9S5 ++
    (s1V9S6 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V10S0 : List ℤ :=
  [s1P 16216, s1P 24653, s1P 20682, s1P 14207, s1P 14064, s1N 34594, s1P 11485, s1P 52549,
   s1P 63073, s1N 92087, s1N 4153, s1P 199767, s1N 22098, s1P 153287, s1N 94911, s1N 17743,
   s1P 423503, s1P 92537, s1N 290586, s1P 760761, s1P 915326, s1P 1038106, s1P 183202,
   s1P 166617, s1N 1074622, s1N 1985170, s1N 838103, s1N 1333956, s1N 432423, s1P 434810,
   s1N 1560520, s1N 3778765, s1N 2005033, s1N 924006, s1N 7934158, s1N 2693672, s1N 4771965,
   s1N 3174580, s1N 8784738, s1N 3989829, s1N 1839154, s1N 938391, s1P 2961996, s1P 5729807,
   s1P 14187472, s1N 23321994, s1N 3122780, s1N 9882039, s1N 5917952, s1P 17457046,
   s1P 4432818, s1N 12169117, s1P 8591986, s1P 7649823, s1P 30935675, s1N 5821278, s1N 8398218,
   s1P 84315450, s1P 137862203, s1P 106430740, s1P 125678373, s1P 39697325, s1P 164673270,
   s1P 212735609]
private def s1V10S1 : List ℤ :=
  [s1N 205558562, s1P 47007401, s1P 122341580, s1P 25815869, s1N 94951301, s1P 230846852,
   s1N 46615045, s1N 78268554, s1N 26353761, s1P 173158731, s1N 49745537, s1P 100156953,
   s1N 160120822, s1P 216779726, s1P 585532042, s1P 169827718, s1P 427804690, s1N 89157922,
   s1N 310917782, s1P 519496000, s1N 198057864, s1P 99938498, s1N 468999692, s1N 12377208,
   s1N 662962763, s1N 1000811988, s1P 561294168, s1P 1282894047, s1N 317634186, s1N 202036439,
   s1N 506432658, s1N 2145775480, s1N 389556063, s1P 752540974, s1N 803929017, s1N 1753556351,
   s1N 398486620, s1P 1438503619, s1P 1119800308, s1P 271286756, s1P 947449066, s1P 894161276,
   s1P 1521981373, s1N 3588472159, s1N 3032082263, s1N 4986352317, s1N 2552920256,
   s1N 110671284, s1P 1900812744, s1P 40260289, s1P 1802178426, s1P 131283091, s1N 460790499,
   s1N 3278824757, s1N 3083073604, s1N 3224644508, s1N 2422282708, s1P 7283110711,
   s1N 1314306406, s1P 2812244737, s1P 7031524618, s1P 5419331009, s1P 3380451899,
   s1P 3090881281]
private def s1V10S2 : List ℤ :=
  [s1P 7117009087, s1P 73967601, s1P 619770480, s1P 10633675867, s1P 4841027810,
   s1N 1179208262, s1P 389393198, s1N 7516599666, s1N 1037073806, s1P 3641541250,
   s1P 9531957775, s1N 387113257, s1N 18684277634, s1P 3145077733, s1N 1501378447,
   s1N 23329221079, s1N 2631443890, s1N 17206173390, s1P 4911281675, s1P 13842232649,
   s1P 7415614622, s1N 16854803136, s1N 384475222, s1N 2748135944, s1N 24383199187,
   s1N 35066199299, s1P 13995070762, s1N 5248875425, s1P 49722851265, s1N 26582914546,
   s1N 49628355361, s1N 27699194849, s1N 32390927931, s1N 16289334298, s1N 44155595687,
   s1N 71458189803, s1N 14382292705, s1N 13116686437, s1P 50924762570, s1P 32182890476,
   s1P 42714101608, s1N 24549571285, s1P 23519178555, s1P 4548585097, s1P 27200288847,
   s1N 49000741349, s1N 38909117830, s1N 5776182698, s1N 1246850983, s1N 8996070244,
   s1P 58889107013, s1N 15776045227, s1N 20211742525, s1P 3901396409, s1N 37854341300,
   s1N 60612800737, s1N 12387782836, s1N 182340716538, s1N 83406290388, s1N 215135868264,
   s1N 25998654690, s1P 65393248316, s1P 71436573810, s1N 87453550847]
private def s1V10S3 : List ℤ :=
  [s1N 95630579345, s1P 76262075042, s1P 5160799760, s1P 93690618876, s1N 7531998293,
   s1P 64990625094, s1P 97000374108, s1P 112860534928, s1P 96117280905, s1P 173095254307,
   s1P 285016828352, s1P 110442347676, s1P 7563638713, s1N 94853415858, s1N 327762039357,
   s1N 352097972014, s1N 307121876884, s1N 34432211585, s1N 54834555031, s1N 13165226383,
   s1N 141899248377, s1P 110732900819, s1N 294513331586, s1N 756682094758, s1P 351459603784,
   s1P 475204956393, s1N 789497287203, s1N 354603034631, s1N 152119315223, s1P 542952355,
   s1P 661418880911, s1N 22375484015, s1N 485734650063, s1N 540840994486, s1N 29568706383,
   s1P 405080559102, s1N 567131552652, s1N 1469729179103, s1N 187085609210, s1N 1227777712728,
   s1N 576690687849, s1N 499634558090, s1N 698320923813, s1N 1515541068118, s1N 554300880013,
   s1P 1696161307132, s1P 2556999450779, s1P 1902544024060, s1N 1877025860784,
   s1N 1147076808567, s1N 1290393137260, s1P 104032432840, s1N 2688409157898,
   s1N 2918848519659, s1N 2102059810994, s1N 774279370165, s1N 476058822230, s1N 2819092032381,
   s1N 2409890153159, s1N 3399384858238, s1N 530596539396, s1P 5039339199723,
   s1P 1943458294377, s1P 4199835965718]
private def s1V10S4 : List ℤ :=
  [s1P 980254674374, s1N 1408583867183, s1N 2773289889899, s1N 1155902024489,
   s1P 4257512856455, s1P 6026327239788, s1P 1607053778993, s1P 1624015947939, s1P 25687664371,
   s1P 2389739089794, s1P 428314988809, s1P 325022841660, s1P 1899287041940, s1P 470552307576,
   s1P 1915998291573, s1P 3394461104330, s1P 6041788710597, s1P 675688052582, s1P 252679882836,
   s1P 1311424699918, s1P 64862581029, s1P 2792721693960, s1N 1947719404334, s1P 304232650521,
   s1P 1725593208792, s1P 994872448974, s1P 166090310641, s1P 3095045845948, s1P 1123953164714,
   s1P 2379749149520, s1P 4630344004908, s1P 228040788418, s1P 809818100389, s1N 1347024066031,
   s1N 2995573408767, s1P 718184336667, s1P 5442356405645, s1P 9027821088820,
   s1N 1109828827086, s1N 1338981992502, s1N 597982336609, s1N 8171244289670,
   s1N 1456492525924, s1N 6553021389603, s1N 4500830124802, s1P 980745587437, s1N 519720475788,
   s1P 1827615875852, s1N 3102990562487, s1N 652654414687, s1N 778260096053, s1P 3492274826506,
   s1P 2056190319316, s1N 4771764752329, s1N 6416749208819, s1N 7034652380028,
   s1P 4584716693516, s1N 2445035159040, s1N 3193481024822, s1P 1645663146857,
   s1N 2820586854207, s1P 1151417430606, s1P 4474340702018, s1N 1721490432321]
private def s1V10S5 : List ℤ :=
  [s1N 6604677542470, s1P 6653782746848, s1P 6944870335165, s1P 944690531981, s1N 897217427122,
   s1N 1500827886546, s1N 2234812614398, s1N 4607089137792, s1N 4052642068667,
   s1N 2584993619080, s1N 6754811827655, s1P 1854355044074, s1N 1671114139333,
   s1P 2456266479599, s1P 5817100647272, s1N 1822674530929, s1N 4630129267112,
   s1P 5551562427374, s1P 438900696487, s1P 7417147472478, s1P 7189281217766,
   s1P 5980316898744, s1P 33669403981220, s1P 73991680000509, s1P 122892803919331,
   s1P 175161492075295, s1P 225409682120067, s1P 268934520204039, s1P 302326007725300,
   s1P 323464748731409, s1P 331659593045807, s1P 327452528143289, s1P 312560409979902,
   s1P 289312339544450, s1P 260336989929591, s1P 227984477678915, s1P 194959917846113,
   s1P 162269542406590, s1P 132921765087632, s1P 105463974502919, s1P 82991884331755,
   s1P 63489556523151, s1P 47295111287720, s1P 35251166766050, s1P 25648328250569,
   s1P 17853462782446, s1P 12451798193407, s1P 8913787079446, s1P 6211366129498,
   s1P 3954076703537, s1P 2247839908599, s1P 1176768407093, s1P 618083129260, s1P 353376195868,
   s1P 215257416421, s1P 127781861610, s1N 69770472723, s1P 34913156152, s1P 16618179743,
   s1P 7990663565, s1P 4082654287, s1P 2226230054, s1P 1254192543, s1P 705726460]
private def s1V10S6 : List ℤ :=
  [s1P 388238334, s1P 207519240, s1P 108674694, s1P 56250584, s1P 28549407, s1P 13894177,
   s1P 6367967, s1P 2749846, s1P 1145728, s1P 479983, s1P 209809, s1P 96820, s1P 46632,
   s1P 22892, s1P 11093, s1P 5144, s1P 2240, s1P 914, s1P 352, s1P 131, s1P 44, s1P 12, s1P 2,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0]
private def s1V10 : List ℤ :=
  s1V10S0 ++
    (s1V10S1 ++
    (s1V10S2 ++
    (s1V10S3 ++
    (s1V10S4 ++
    (s1V10S5 ++
    (s1V10S6 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V11S0 : List ℤ :=
  [s1P 5705, s1P 12351, s1P 27027, s1N 435, s1P 38198, s1N 13033, s1N 18160, s1N 43786,
   s1N 74713, s1N 213977, s1P 70066, s1P 30213, s1N 48928, s1N 77600, s1P 4455, s1P 497026,
   s1N 361835, s1N 21388, s1N 79440, s1P 468925, s1N 6804, s1N 653468, s1N 622576, s1P 198118,
   s1P 379999, s1P 1477945, s1P 827723, s1P 446388, s1P 1217396, s1P 1971222, s1P 5433799,
   s1P 371389, s1P 77520, s1P 690617, s1P 2533025, s1N 1897153, s1P 2843992, s1P 6590045,
   s1P 2844186, s1P 13858777, s1N 9045470, s1N 8822458, s1N 11833333, s1N 6215973, s1P 6911363,
   s1N 17640658, s1N 7370634, s1N 10042995, s1P 11180717, s1N 12223419, s1N 651787,
   s1N 7517267, s1N 8906410, s1P 33569330, s1P 42272051, s1N 8521400, s1N 78845578,
   s1N 101667188, s1N 107207944, s1N 113873223, s1P 13222747, s1P 87638796, s1N 104581934,
   s1N 279144901]
private def s1V11S1 : List ℤ :=
  [s1N 29952145, s1N 23703222, s1P 104619695, s1N 311510508, s1N 35768837, s1P 133525160,
   s1N 185051151, s1N 122681326, s1P 164379715, s1N 111998144, s1N 7139443, s1N 476272621,
   s1P 466817456, s1P 292056842, s1P 187011733, s1N 127132252, s1P 131381552, s1P 20549313,
   s1P 127670589, s1P 239665336, s1N 86888107, s1N 854422811, s1P 92592148, s1P 367374131,
   s1N 1101941337, s1N 83960807, s1P 821705606, s1P 763000258, s1P 571419086, s1P 423457553,
   s1N 90138939, s1N 576785802, s1P 704119284, s1P 1531909778, s1N 2295702524, s1P 224000229,
   s1P 699831431, s1P 2094816189, s1P 347343518, s1P 499766720, s1P 97862955, s1P 2494566267,
   s1P 150572340, s1P 963804928, s1N 21085130, s1P 237288667, s1P 1016522687, s1N 1634463068,
   s1P 403961447, s1P 6161645507, s1P 1572159802, s1P 1201685993, s1N 1099260102,
   s1N 6842054344, s1N 1691543293, s1P 713197847, s1P 1729304926, s1N 1348678348,
   s1N 2850325305, s1N 5185547687, s1N 2828876175, s1N 5164281559, s1P 3534127694,
   s1P 6702789274]
private def s1V11S2 : List ℤ :=
  [s1N 3627860585, s1P 2597180900, s1P 1320545757, s1N 2707377078, s1P 146375086,
   s1P 6776977229, s1N 11297325867, s1N 8880442972, s1N 18063145054, s1N 5983221841,
   s1P 2599032956, s1P 13424509863, s1P 15676886849, s1N 6821278431, s1P 1980708739,
   s1P 8493609565, s1P 8412854467, s1P 8480081765, s1P 26203711246, s1P 31656303424,
   s1P 13240863416, s1P 16025289764, s1P 18967111807, s1N 3554896657, s1N 22188202333,
   s1N 15829515670, s1P 21523007316, s1N 29820301486, s1N 13307479792, s1N 7178672042,
   s1N 37199812381, s1N 13995695312, s1P 16492590474, s1P 62688775816, s1P 13532514792,
   s1P 10268837295, s1P 21877781393, s1P 8664119423, s1N 15076476928, s1N 21592849515,
   s1N 1480324778, s1N 29661606386, s1P 4282276993, s1P 83586910142, s1P 84590553592,
   s1P 15611859947, s1N 36256994159, s1N 58699919998, s1N 95647646416, s1N 57787208822,
   s1P 64962995658, s1P 19571463243, s1P 17764143292, s1N 14493103319, s1P 43862639095,
   s1P 9710994653, s1P 56020910056, s1P 55287236599, s1P 64483165673, s1P 58429422254,
   s1P 35836841919, s1N 61940408246, s1N 30935817715, s1N 54567099776]
private def s1V11S3 : List ℤ :=
  [s1P 73200759131, s1P 93630787965, s1P 171633425144, s1P 184906734045, s1N 100240684780,
   s1N 59551610099, s1N 113063472048, s1N 27911196378, s1P 41146323142, s1P 40493333914,
   s1P 103322214300, s1N 47489715696, s1P 50339042898, s1N 5546023886, s1N 107067286295,
   s1N 70104081849, s1P 66870265471, s1P 309480169132, s1P 244368177136, s1P 479592336589,
   s1P 658939942635, s1P 526330413838, s1P 122877897643, s1N 185717336108, s1N 531769726550,
   s1N 539293164407, s1P 67308753029, s1P 51969013975, s1N 440196762689, s1N 764836768460,
   s1N 92250080853, s1P 578532856654, s1P 129154905118, s1P 648560470784, s1P 469613543871,
   s1N 934479959666, s1N 386885340663, s1N 891571967830, s1P 566840352018, s1P 566576948657,
   s1P 815097590690, s1P 441932208197, s1P 586316014425, s1N 401021947085, s1N 274851661889,
   s1N 582654729488, s1N 1054203563245, s1N 1516499403066, s1N 946615157275, s1N 146412288344,
   s1N 1853904742158, s1N 2354633301546, s1N 2889554772929, s1N 3219420307269,
   s1N 256864080908, s1P 1096322689183, s1N 946286821406, s1P 494546526514, s1N 963375347495,
   s1N 571982681040, s1N 2641398825520, s1N 2330070248363, s1N 3150929762848, s1N 1049893562645]
private def s1V11S4 : List ℤ :=
  [s1P 1034931180051, s1P 2408279322371, s1N 2389603288890, s1N 4037273055031,
   s1N 2984266333943, s1P 2437547461583, s1P 4037520711734, s1P 5299589463599,
   s1P 3056271094263, s1N 2009892053670, s1P 2498479007861, s1N 1289020982936,
   s1N 1259794104216, s1P 4129165083987, s1P 3013817280460, s1P 1869074692124,
   s1N 1510569304499, s1N 2066132364997, s1P 2072888317640, s1P 2012514438296,
   s1N 1687572892472, s1N 1303119443397, s1P 4600365995267, s1P 2019620216643,
   s1P 2805834972317, s1N 3676522441409, s1N 826200237680, s1P 3245680852255, s1N 747552985468,
   s1P 1308200283192, s1N 463578419756, s1P 238124922921, s1N 3270099111751, s1N 4176787468567,
   s1P 4395359845154, s1N 1158596317631, s1N 3083919554132, s1P 5489598919992,
   s1P 3697592106755, s1P 5509563458888, s1N 843742379281, s1N 2913288806770,
   s1P 2876824777820, s1N 1224118005087, s1P 5274321572339, s1P 2355844667775,
   s1P 5669003813387, s1P 124405133801, s1P 2592436662514, s1N 3280906022676,
   s1N 6112846434401, s1N 3828397870797, s1N 7662362978174, s1P 1289137569393,
   s1P 2496338739157, s1N 5248840914639, s1N 6023367244596, s1P 4027597219832,
   s1P 1321182483013, s1P 1773520433475, s1P 2785988457172, s1N 6470934192440,
   s1N 5992301687753, s1N 1834784741810]
private def s1V11S5 : List ℤ :=
  [s1N 1393119055869, s1N 5010592329652, s1N 6535861515360, s1N 5350657312045,
   s1P 450079031758, s1P 1396058798933, s1N 1268713977977, s1N 2860313134612, s1N 360745843330,
   s1P 6922177942721, s1N 1361276754545, s1P 5331412721929, s1P 3066226418566,
   s1P 5247535796046, s1P 2040032992268, s1N 2424373547641, s1N 5959560527349,
   s1N 4434413025207, s1N 5875258606244, s1N 2291742846822, s1P 4474019290871,
   s1N 3031011785480, s1N 3474743797496, s1N 3863984369660, s1P 2663299249135,
   s1P 7160586671815, s1P 3959387746811, s1P 4361440341836, s1P 8975185498310,
   s1P 3262118125967, s1P 18242448056827, s1P 53148350028747, s1P 100218623888791,
   s1P 152424151540631, s1P 205191800407890, s1P 253494833128400, s1P 291827604378344,
   s1P 318623680021773, s1P 332258236120439, s1P 332151633038983, s1P 320787636446075,
   s1P 300167621198721, s1P 272054606392782, s1P 239819869288584, s1P 206421229790241,
   s1P 173282524409420, s1P 141743330994768, s1P 113493945979733, s1P 89175862144197,
   s1P 68739544852215, s1P 51547217071948, s1P 37904063948820, s1P 27447622734406,
   s1P 19696359581603, s1P 14049659169737, s1P 9735887131642, s1P 6399799864917,
   s1P 4014828954236, s1P 2451077890469, s1P 1453767885958, s1P 817314616148, s1P 427124957786,
   s1P 208962191151, s1P 99418373834]
private def s1V11S6 : List ℤ :=
  [s1P 48578200773, s1P 25262494910, s1P 13881635454, s1P 7815540906, s1P 4399820463,
   s1P 2451918085, s1P 1350340832, s1P 735281868, s1P 395822294, s1P 210386557, s1P 110107487,
   s1P 56503450, s1P 28289366, s1P 13757279, s1P 6483036, s1P 2963224, s1P 1320116, s1P 578269,
   s1P 251923, s1P 110348, s1P 48908, s1P 21896, s1P 9822, s1P 4360, s1P 1892, s1P 795,
   s1P 317, s1N 116, s1P 38, s1P 10, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V11 : List ℤ :=
  s1V11S0 ++
    (s1V11S1 ++
    (s1V11S2 ++
    (s1V11S3 ++
    (s1V11S4 ++
    (s1V11S5 ++
    (s1V11S6 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V12S0 : List ℤ :=
  [s1N 4578, s1N 9222, s1N 34098, s1P 6870, s1N 22678, s1N 5570, s1P 70274, s1P 89298,
   s1P 70689, s1P 46961, s1P 185529, s1N 6916, s1P 367672, s1N 389817, s1P 170461, s1P 130227,
   s1P 137192, s1N 203294, s1P 233097, s1P 154008, s1P 645296, s1P 183527, s1N 416143,
   s1P 127715, s1N 862641, s1P 1683018, s1N 718492, s1P 1696126, s1P 664706, s1N 1231795,
   s1N 1647191, s1N 1076402, s1P 2826872, s1N 9040896, s1N 4299359, s1N 6823645, s1N 1565202,
   s1P 3306276, s1P 9343192, s1P 7684418, s1P 7152318, s1P 9785603, s1P 8517355, s1N 5721693,
   s1N 17473368, s1N 80297, s1P 17491113, s1P 2691065, s1P 2057075, s1P 8894797, s1P 3150550,
   s1N 9946931, s1P 10936052, s1P 16666968, s1P 26644786, s1P 3414934, s1N 14777890,
   s1N 91065520, s1N 139526808, s1N 107535223, s1N 97309792, s1N 42911669, s1N 19068782,
   s1P 77902351]
private def s1V12S1 : List ℤ :=
  [s1P 262698113, s1P 141333175, s1P 389907895, s1P 317903198, s1P 27053284, s1P 257234017,
   s1N 155969307, s1P 157513290, s1P 178643736, s1P 20125997, s1P 155413718, s1N 240686916,
   s1N 238208587, s1N 29092332, s1N 308163162, s1N 114051518, s1N 470062791, s1N 295040409,
   s1P 464207204, s1P 5442014, s1P 859826755, s1N 100112206, s1P 573805204, s1P 467362182,
   s1N 366003776, s1N 488687240, s1N 1304595109, s1N 1520100930, s1N 891673983, s1P 66968714,
   s1N 16437531, s1N 272344106, s1N 1954907604, s1N 1217370080, s1P 720790166, s1P 1006501111,
   s1N 609186949, s1N 545849878, s1P 1786311309, s1P 868765311, s1P 1025783111, s1N 404575961,
   s1P 1873936281, s1P 1367637633, s1P 2190699687, s1P 2962157078, s1P 2612178079,
   s1P 1380044113, s1N 86597239, s1P 219499929, s1N 2366653029, s1N 4438140, s1P 2560633666,
   s1N 351136828, s1N 2544431853, s1N 331094028, s1N 2170183605, s1N 8462873883,
   s1N 3777041456, s1N 790971763, s1P 2359558980, s1P 2973703142, s1P 11077287944,
   s1P 4857835408]
private def s1V12S2 : List ℤ :=
  [s1P 2429605931, s1P 1819195081, s1N 656112454, s1N 6584820461, s1P 1164181986,
   s1N 8949507699, s1N 2953920803, s1P 4038355447, s1P 1591017686, s1P 554210148,
   s1P 165718527, s1P 1776691169, s1N 2145190896, s1N 13083203688, s1N 4920320839,
   s1P 26110324481, s1P 8366027352, s1P 13967446478, s1P 6069453364, s1N 11053558714,
   s1P 10032205734, s1P 25885616620, s1N 27420017108, s1P 8837447457, s1N 10851139792,
   s1N 7396928878, s1N 5444866027, s1P 24722421335, s1P 41700932440, s1P 10841131964,
   s1N 22637391143, s1P 19573530874, s1N 770854432, s1N 25056306280, s1P 2621164407,
   s1N 30389748871, s1N 15474750452, s1N 42079486671, s1N 18469343116, s1N 23645849757,
   s1P 12164338060, s1P 6380361127, s1N 71233564870, s1P 18672310512, s1P 20416732505,
   s1P 36100558326, s1N 44184156225, s1N 28245105064, s1N 18465527196, s1P 38156771985,
   s1P 37414992158, s1P 2158108083, s1P 122155764163, s1P 59701297944, s1P 52980557314,
   s1P 53883024694, s1P 72515645523, s1N 21136924179, s1P 70710220202, s1N 56634929204,
   s1P 63178360174, s1P 34798156423, s1P 42684529763, s1N 61855316761]
private def s1V12S3 : List ℤ :=
  [s1P 52769652025, s1P 11687151905, s1N 90506998355, s1P 41778439464, s1P 98344485259,
   s1N 94269684774, s1P 103343364541, s1P 61732385725, s1P 87329635653, s1P 72702217132,
   s1P 109199569069, s1P 202414143930, s1P 125719413272, s1P 56120400438, s1P 65981599050,
   s1P 16050178480, s1N 14244038819, s1N 171089005827, s1N 139201820507, s1N 119972512553,
   s1P 33774662488, s1P 67887893705, s1P 86405135917, s1N 11622407026, s1N 115753596634,
   s1N 130228657505, s1N 412925885013, s1N 663697390457, s1N 1146150252180, s1N 854463026561,
   s1N 531094632722, s1N 152377250184, s1P 8092681363, s1N 226096301897, s1N 148380596279,
   s1N 279247528185, s1N 171589228783, s1N 401969231233, s1N 927029018273, s1N 262427598618,
   s1N 256653249373, s1N 990926258849, s1P 247285109500, s1P 23244356858, s1P 67861747949,
   s1N 1126715555853, s1N 719516457721, s1N 1288573482746, s1N 902053949474, s1N 1339028791771,
   s1N 210860679049, s1N 693245438398, s1N 424133099402, s1N 571035906542, s1N 1817239636137,
   s1N 1107941961024, s1N 492198042649, s1N 1055046941786, s1N 1476743482448,
   s1N 1598084576770, s1N 3008061330529, s1N 2861616502562, s1N 1782223547622,
   s1N 1461788110367]
private def s1V12S4 : List ℤ :=
  [s1P 467419113119, s1P 2737446811694, s1P 2199854877997, s1N 1676836226939,
   s1N 2964098290889, s1N 1896211094350, s1N 5259165408939, s1N 2123402866707,
   s1P 3589808821094, s1N 929977667431, s1N 2351132361981, s1P 4171391693861,
   s1N 2338427236591, s1N 1789193460532, s1N 2599567666065, s1N 914798192539,
   s1N 6540717524976, s1N 3484654475574, s1N 2977340761213, s1P 3182739015, s1P 86182717564,
   s1P 5062126651238, s1P 1544767193351, s1P 1798460114468, s1P 2520887097314,
   s1N 1815238690018, s1P 1620758660092, s1P 3139138629319, s1P 2726304134686,
   s1P 5989719297465, s1P 1180602845098, s1N 1399615017161, s1P 4799406275493,
   s1P 2812816872625, s1P 625068367356, s1P 2259839708818, s1P 5968238894042, s1N 343117727052,
   s1P 949050336159, s1N 1847387797092, s1N 2120634683850, s1P 734011240830, s1N 5165836731485,
   s1N 157675057345, s1P 2387282456079, s1N 4079056397809, s1N 4857884445066,
   s1N 1764497721304, s1P 1355602419309, s1N 1667782341061, s1P 3341369318778,
   s1N 1813763416893, s1N 5130663008744, s1N 2261588524306, s1N 5485767336434,
   s1N 9057751827188, s1N 1127182520225, s1P 3803039124239, s1P 3848206210769,
   s1P 4917408629863, s1N 1363336638843, s1N 287833241923, s1P 4281259996977, s1N 5293029526128]
private def s1V12S5 : List ℤ :=
  [s1N 5073750432546, s1P 5112795521334, s1N 989812185091, s1P 3981684402083,
   s1P 5178138058323, s1N 2460494746135, s1N 1947598568701, s1P 1753460947894,
   s1P 7278646960362, s1P 5940017978041, s1N 3735375694094, s1P 2507753383683,
   s1N 1230048542918, s1P 5828379383926, s1P 1342960304943, s1P 676591446575,
   s1P 1801567964017, s1P 1472980988800, s1N 2304782897427, s1N 3019953008230,
   s1N 6519220775165, s1P 4118679622537, s1N 5572690960506, s1N 4727402156310,
   s1N 9226438374611, s1P 1051374489365, s1N 437835727945, s1N 3376846847585,
   s1P 2667533620335, s1N 1512626101100, s1N 4411326989264, s1P 4073475071601,
   s1N 3273059096427, s1P 9305452733871, s1P 7244375310988, s1P 989923594519,
   s1P 8286958305975, s1P 5702832103524, s1P 12367425336621, s1P 45753703071003,
   s1P 91204847199776, s1P 144460957281959, s1P 199012199881429, s1P 248869700067783,
   s1P 289562031547012, s1P 318496508460296, s1P 333722395122899, s1P 334882758626906,
   s1P 323904963026504, s1P 303234454744121, s1P 275250023055830, s1P 242651187529077,
   s1P 208198347949089, s1P 174308863178259, s1P 142694951118429, s1P 114199165517126,
   s1P 89200590849037, s1P 68051128111223, s1P 50940650676014, s1P 37591259274079,
   s1P 27344353842699, s1P 19510608701288, s1P 13576777178924, s1P 9180326416873]
private def s1V12S6 : List ℤ :=
  [s1P 6019535371943, s1P 3817857050393, s1P 2333222363208, s1P 1368440754717,
   s1P 768716410165, s1P 414419385461, s1P 215911598401, s1P 109994115844, s1P 55601559503,
   s1P 28282624539, s1P 14611127748, s1P 7682717074, s1P 4095596807, s1P 2198634640,
   s1P 1180605568, s1P 630729063, s1P 333893504, s1P 174566608, s1P 89861085, s1P 45410368,
   s1P 22467718, s1N 10862148, s1P 5126909, s1P 2363545, s1P 1066578, s1P 472902, s1P 206849,
   s1N 89679, s1P 38779, s1P 16761, s1P 7175, s1P 2983, s1P 1180, s1P 441, s1P 150, s1P 47,
   s1P 11, s1P 1, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0]
private def s1V12 : List ℤ :=
  s1V12S0 ++
    (s1V12S1 ++
    (s1V12S2 ++
    (s1V12S3 ++
    (s1V12S4 ++
    (s1V12S5 ++
    (s1V12S6 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private def s1V13S0 : List ℤ :=
  [s1P 6339, s1P 14959, s1P 28463, s1N 19343, s1N 9634, s1N 28355, s1N 4976, s1N 98825,
   s1N 224979, s1N 213869, s1P 374205, s1N 165759, s1P 71462, s1P 147800, s1N 373365,
   s1N 206549, s1N 14344, s1P 139671, s1N 221357, s1P 861713, s1P 1157803, s1P 1087025,
   s1P 961738, s1N 749480, s1P 1127248, s1N 1022275, s1N 1406807, s1N 2452116, s1N 3580969,
   s1N 4474645, s1N 1916703, s1N 2854235, s1P 418837, s1N 2270178, s1P 73033, s1P 845020,
   s1P 383632, s1P 126430, s1P 2641210, s1P 6614770, s1P 8675390, s1P 7134734, s1P 8041794,
   s1P 204591, s1N 3569496, s1N 8105996, s1N 29410094, s1N 1034058, s1N 1976511, s1P 8024229,
   s1N 2326098, s1P 3385443, s1P 7761869, s1N 26181559, s1N 2310183, s1N 3510901, s1N 29409501,
   s1P 53589669, s1P 55277924, s1P 47117150, s1N 29308809, s1N 179831096, s1N 210496673,
   s1N 138796727]
private def s1V13S1 : List ℤ :=
  [s1N 124342526, s1P 181400759, s1P 21362164, s1P 237144679, s1P 40937769, s1P 14676706,
   s1P 145661278, s1N 293992141, s1N 170971133, s1P 242777697, s1P 546308285, s1N 209294269,
   s1N 514891164, s1N 368626587, s1N 335963794, s1N 289357805, s1N 80074894, s1N 278208244,
   s1P 333441110, s1P 14437, s1N 171778343, s1P 149289051, s1P 666808274, s1P 74429328,
   s1P 485795903, s1P 22940994, s1N 174209918, s1P 48504706, s1P 442204303, s1N 268229329,
   s1P 937521872, s1P 24098231, s1P 1329739389, s1P 1782397473, s1P 1880099189, s1P 1025980796,
   s1P 795986934, s1P 180544062, s1N 2044146908, s1N 981724211, s1N 464074541, s1N 245756358,
   s1P 1397720919, s1P 258581545, s1P 495053982, s1P 496559582, s1N 1144665027, s1N 1154381099,
   s1N 177143211, s1N 1230329497, s1N 3587430323, s1N 1013968938, s1P 1375096262,
   s1N 3196713628, s1N 6164973179, s1P 1464652475, s1N 849995224, s1P 1633042756,
   s1P 582187416, s1P 4914691291, s1P 5394529351, s1P 997588035, s1P 357344817, s1N 3473178012]
private def s1V13S2 : List ℤ :=
  [s1N 4845647750, s1P 4828663019, s1P 4427345557, s1N 6305614437, s1P 3855369808,
   s1P 6869548120, s1N 670061519, s1P 11877122580, s1N 2644773427, s1P 8556465860,
   s1N 9188807450, s1N 7034107899, s1N 13248204535, s1N 20602986668, s1N 26232813376,
   s1P 7237723919, s1N 1956541917, s1P 5445133460, s1P 15486161454, s1P 9417865861,
   s1P 20687989493, s1P 12056661690, s1N 2744909524, s1P 17118908346, s1P 8632428380,
   s1P 14935817888, s1N 41430034314, s1N 11870238497, s1P 3026036049, s1P 16852555311,
   s1N 24349714685, s1P 67656265, s1P 38264578528, s1P 14502468341, s1P 35177373083,
   s1P 37607508142, s1N 3558950953, s1P 13038831610, s1P 17429581712, s1P 22454899332,
   s1P 7470869134, s1P 25054275710, s1N 53289251733, s1P 29067223729, s1N 6552851398,
   s1N 69606189294, s1N 10268631998, s1P 2553853207, s1P 30123638703, s1P 129475434194,
   s1N 37166712877, s1P 23084605734, s1P 22349017449, s1P 7676965441, s1P 16064377068,
   s1P 30000179127, s1N 9270579366, s1N 18003699558, s1P 30058761884, s1P 11330548109,
   s1P 123383233542, s1P 81921082113, s1P 122053322253, s1P 134120142178]
private def s1V13S3 : List ℤ :=
  [s1P 7527704651, s1P 60587979796, s1N 59826148626, s1N 10020885550, s1P 1162009355,
   s1P 20300945410, s1P 100775426734, s1N 23159049620, s1P 9579784088, s1N 571625958,
   s1P 41571958520, s1P 44127883406, s1P 25527655387, s1N 34164506207, s1N 26186857130,
   s1P 42014332205, s1P 60592042983, s1P 128191262077, s1N 35097512262, s1N 188288128203,
   s1N 64628242649, s1N 125477635062, s1N 187756369011, s1N 60206027416, s1N 203012947809,
   s1N 83515798899, s1N 164793622392, s1N 130887483638, s1N 95408645582, s1N 117309260188,
   s1N 97749104789, s1P 202309676526, s1N 484223050639, s1N 301381314438, s1N 647187867790,
   s1N 513003283394, s1N 807758478234, s1N 1095108403779, s1N 243205907938, s1N 1057404578596,
   s1N 398934486476, s1N 293403159615, s1N 139141645619, s1N 321746408210, s1N 520227731270,
   s1N 365161349833, s1N 464140210880, s1N 698927310447, s1N 552789783481, s1N 756816411812,
   s1N 415407320536, s1N 388029942466, s1N 262805011178, s1P 389247173808, s1P 271718283862,
   s1P 1031766093821, s1P 1489767873890, s1P 944851465089, s1N 926972896235, s1N 437913906066,
   s1N 554584723362, s1N 53619819828, s1P 2015173185595, s1N 1243711828359]
private def s1V13S4 : List ℤ :=
  [s1N 629481302135, s1N 1296485451778, s1N 3241684482944, s1N 3947712835728,
   s1N 4574267506711, s1N 3247141930819, s1N 2221272369241, s1P 2388524788796,
   s1P 4615912717613, s1P 3644633374062, s1P 2899884292156, s1N 623336009631,
   s1N 2117980546801, s1P 407219453019, s1P 3584441565794, s1P 4379506769494, s1N 592214904368,
   s1N 1710320161847, s1P 312987208030, s1N 1583601062051, s1N 1603057961879,
   s1N 1045799297606, s1P 721018110763, s1N 3722159832022, s1N 1435705345420,
   s1N 5708859173976, s1N 4931431921327, s1N 2728034262921, s1N 304645795566,
   s1P 1983390595684, s1N 5160776323261, s1N 4511974404612, s1N 3285254840801,
   s1N 1368958886372, s1P 934831208965, s1P 2493306743379, s1P 3750622405552, s1P 287925564583,
   s1P 5034568107350, s1N 2789087172597, s1P 345597814411, s1N 83590662199, s1N 6222002414845,
   s1N 2025286446954, s1N 498723374642, s1P 5942477504781, s1P 2736351419890,
   s1N 2197450525789, s1N 147274797153, s1N 1919718598633, s1P 2434280247922,
   s1N 3426290620095, s1P 1586294500135, s1N 5595393455535, s1P 1208672320455,
   s1P 2646563316845, s1N 2008956897926, s1P 2397092643453, s1P 3979776621640,
   s1P 4556207856595, s1P 2961072660056, s1N 10759007671169, s1N 6744356020343,
   s1N 3261275955401]
private def s1V13S5 : List ℤ :=
  [s1N 4952109999265, s1P 1165389772878, s1N 362693644464, s1N 6206795971846, s1N 784940613531,
   s1N 4918082395492, s1P 122282520114, s1N 5375771396557, s1N 3819661509557,
   s1P 2522196832745, s1P 4114287876890, s1N 4364731666250, s1N 6033098234370,
   s1P 2241542274108, s1P 631570294218, s1P 7824575067224, s1P 987292212745, s1P 1098946063287,
   s1P 2119320861367, s1P 2345673700963, s1N 1927984554721, s1N 1689199966090,
   s1P 3259265878585, s1P 10095898240933, s1N 5709323921957, s1P 1130978493754,
   s1P 609469373331, s1N 2386298776739, s1P 2961543620811, s1N 6247076282095,
   s1N 5163132319426, s1N 1906423037429, s1N 8267003085976, s1N 2225805767338,
   s1P 2414223864740, s1P 2384747324583, s1N 3160129538882, s1P 681268995635,
   s1N 1975098276068, s1N 2384803439334, s1P 3025885794038, s1P 9103195087532,
   s1N 8550006958685, s1N 714454999594, s1P 7748382840668, s1P 7275463554950,
   s1P 8663191947495, s1P 40947501308198, s1P 86457032886769, s1P 140140033543909,
   s1P 195945243801342, s1P 247678452639757, s1P 290105171853712, s1P 319832315113592,
   s1P 335496100289713, s1P 337252193116898, s1P 326282884118579, s1P 304762588016412,
   s1P 275743403931785, s1P 242488654321354, s1P 207724683102110, s1P 173447658420923,
   s1P 141175229282029, s1P 112114917490424]
private def s1V13S6 : List ℤ :=
  [s1P 87065854310913, s1P 66289176760382, s1P 49563729012118, s1P 36392101104732,
   s1P 26202398504917, s1P 18458155945793, s1P 12689209252872, s1P 8489922437570,
   s1P 5513085730284, s1P 3465616094599, s1P 2104679948425, s1P 1233668607111,
   s1P 698320096777, s1P 382609612539, s1P 203779853696, s1P 106119025464, s1P 54451410670,
   s1P 27723384324, s1P 14108694184, s1P 7221753616, s1P 3713578224, s1P 1914763029,
   s1P 996616522, s1P 523198256, s1P 270378922, s1P 132992966, s1P 61145598, s1N 26654906,
   s1P 11573942, s1P 5272076, s1P 2515839, s1P 1195094, s1P 540922, s1P 231805, s1P 96635,
   s1P 40796, s1P 17859, s1P 8031, s1P 3602, s1P 1567, s1P 645, s1P 247, s1P 86, s1P 24, s1P 4,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V13 : List ℤ :=
  s1V13S0 ++
    (s1V13S1 ++
    (s1V13S2 ++
    (s1V13S3 ++
    (s1V13S4 ++
    (s1V13S5 ++
    (s1V13S6 ++
    (mm32k512krS1VecIn5 ++
    mm32k512krS1VecIn8)))))))
private theorem s1Ok0 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B0 mm32k512krS1LIn 512 mm32k512krS1PadIn mm32k512krS1VecIn)
      16 512 513766658 s1V0 = true := by decide +kernel
private theorem s1Ok1 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B1 16 512 513766658 s1V0)
      17 512 544734317 s1V1 = true := by decide +kernel
private theorem s1Ok2 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B2 17 512 544734317 s1V1)
      18 512 577491318 s1V2 = true := by decide +kernel
private theorem s1Ok3 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B3 18 512 577491318 s1V2)
      18 512 604370796 s1V3 = true := by decide +kernel
private theorem s1Ok4 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B4 18 512 604370796 s1V3)
      19 512 620825027 s1V4 = true := by decide +kernel
private theorem s1Ok5 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B5 19 512 620825027 s1V4)
      20 512 625483576 s1V5 = true := by decide +kernel
private theorem s1Ok6 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B6 20 512 625483576 s1V5)
      20 512 631232623 s1V6 = true := by decide +kernel
private theorem s1Ok7 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B7 20 512 631232623 s1V6)
      22 512 635788244 s1V7 = true := by decide +kernel
private theorem s1Ok8 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B8 22 512 635788244 s1V7)
      22 512 642173015 s1V8 = true := by decide +kernel
private theorem s1Ok9 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B9 22 512 642173015 s1V8)
      23 512 650998325 s1V9 = true := by decide +kernel
private theorem s1Ok10 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B10 23 512 650998325 s1V9)
      23 512 660157859 s1V10 = true := by decide +kernel
private theorem s1Ok11 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B11 23 512 660157859 s1V10)
      25 512 672148282 s1V11 = true := by decide +kernel
private theorem s1Ok12 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B12 25 512 672148282 s1V11)
      25 512 681400194 s1V12 = true := by decide +kernel
private theorem s1Ok13 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B13 25 512 681400194 s1V12)
      26 512 689949671 s1V13 = true := by decide +kernel
private theorem s1Ok14 :
    s1SegStateAt
      (rkm128kRunSegs 32 32 512 s1B14 26 512 689949671 s1V13)
      mm32k512krS1LOut 512 mm32k512krS1PadOut mm32k512krS1Vec = true := by decide +kernel

/-- Segment count of `mm32k512krS1Segs` (`23` segments). -/
theorem mm32k512krS1_len : rkm128kSegListLen mm32k512krS1Segs = 23 := by
  rfl

/-- Exact `rkm128kRunSegs 32 32 512` Markovian step across `mm32k512krS1Segs` (`segs
  57..79`). -/
theorem mm32k512krS1_step :
    rkm128kRunSegs 32 32 512 mm32k512krS1Segs mm32k512krS1LIn mm32k512krS1DCurIn
      mm32k512krS1PadIn mm32k512krS1VecIn =
      (mm32k512krS1LOut, mm32k512krS1DCurOut, mm32k512krS1PadOut,
        mm32k512krS1Vec) := by
  have hSegs : mm32k512krS1Segs =
      s1B0 ++ (s1B1 ++ (s1B2 ++ (s1B3 ++ (s1B4 ++ (s1B5 ++ (s1B6 ++
        (s1B7 ++ (s1B8 ++ (s1B9 ++ (s1B10 ++ (s1B11 ++ (s1B12 ++
          (s1B13 ++ s1B14))))))))))))) := rfl
  rw [hSegs]
  exact s1Step s1Ok0 (s1Step s1Ok1 (s1Step s1Ok2 (s1Step s1Ok3
    (s1Step s1Ok4 (s1Step s1Ok5 (s1Step s1Ok6 (s1Step s1Ok7
      (s1Step s1Ok8 (s1Step s1Ok9 (s1Step s1Ok10 (s1Step s1Ok11
        (s1Step s1Ok12 (s1Step s1Ok13 (s1SegStateAt_eq s1Ok14))))))))))))))

/-- Suffix chaining lemma advancing `rkm128kRunSegs 32 32 512` past `mm32k512krS1Segs`. -/
theorem mm32k512krS1_run_after (rest : List Rkm128kSeg) :
    rkm128kRunSegs 32 32 512 (mm32k512krS1Segs ++ rest) mm32k512krS1LIn
      mm32k512krS1DCurIn mm32k512krS1PadIn mm32k512krS1VecIn =
      rkm128kRunSegs 32 32 512 rest mm32k512krS1LOut mm32k512krS1DCurOut
        mm32k512krS1PadOut mm32k512krS1Vec := by
  rw [rkm128kRunSegs_append]
  dsimp only
  rw [mm32k512krS1_step]

end

end QuantumComputation.Specs.GroverFindAll.Rk128kMidM32K512KrPt1
