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
# `(4, 512)` `RampKick128k` Krotov `L <= 248` Part 1 (`Rk128kLowM4K512L248KrPt1`)

Certifies Slice 1 (`r = 512` segments `47..74`, `28` segments, `423,412` F1272 /
`424,281 <= 450,000` Horner coord-ops, `dk = 13`, `lTableMax = 248`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kLowM4K512L248KrPt1

@[expose] public section

open QuantumComputation.Specs.DickeSol

/-- Segments `47..74` (`28` segments) of `(4, 512)` `r = 512` at `lTableMax = 248`. -/
def lm4k512l248krS1Segs : List Rkm128kSeg := [
  ⟨95, 353612, 1, 24,
    rkm128kMask56 380 [51090471939721169, 6005782909026183, 57631622085376594, 0,
      137438953472, 17904447346704384, 9524325271313]⟩,
  ⟨99, 344541, 1, 24,
    rkm128kMask56 395 [54317361530748212, 16332451370986254, 44456040198359056,
      562949953421338, 2251834173423616, 2250700436275200,
      37027898111711175, 5]⟩,
  ⟨102, 339843, 1, 24,
    rkm128kMask56 409 [63149378947633664, 11592209005708573, 49676014399365076, 934,
      9007199254740992, 36591747509256192, 43836776551278343, 102835]⟩,
  ⟨104, 334185, 1, 24,
    rkm128kMask56 416 [31332017245463126, 23057766536910864, 11557697343998113,
      140737488380556, 68719476736, 134217729, 8218975378865121, 15947338]⟩,
  ⟨106, 330645, 1, 24,
    rkm128kMask56 425 [38098804443931233, 64142740849034645, 51840339511450431, 876751, 0,
      18014398509481984, 42514591018647552, 8257450535]⟩,
  ⟨108, 330077, 1, 24,
    rkm128kMask56 433 [56797832890902368, 29043361633098237, 43252845554496642, 29648940, 0,
      1128101077581824, 69725598594892800, 1804691424445]⟩,
  ⟨111, 320936, 1, 24,
    rkm128kMask56 445 [7597397632320885, 35692540925882097, 17477155324942264, 931465717,
      4398046511104, 549755813888, 5031657266479104, 4522597385355509]⟩,
  ⟨113, 328427, 1, 25,
    rkm128kMask56 453 [25786127655541072, 63686575007729705, 2219708198341708, 31324134278,
      0, 0, 32768, 3144619015422076, 17]⟩,
  ⟨116, 311021, 1, 25,
    rkm128kMask56 465 [16765882419554813, 2342828890353532, 13669942897034430, 879773903641,
      8796093022208, 18049651601063968, 2097152, 66233893411094528, 125721]⟩,
  ⟨120, 611385, 2, 25,
    rkm128kMask56 479 [68017673919506302, 37733850096927345, 33780419018293710,
      1006429499563489, 0, 2048, 281474977103872, 39137941091516416,
      1750514053]⟩,
  ⟨124, 605358, 2, 25,
    rkm128kMask56 495 [60816456438084825, 61991780913118504, 58381819253402552,
      2621264438430876, 15, 36028805608898560, 0, 10182645904310272,
      81231589695177]⟩,
  ⟨128, 313169, 1, 26,
    rkm128kMask56 507 [16390821414923705, 24454116875453930, 68540563171904072,
      212491092015554, 36028797018964356, 9007199254740992, 33554432,
      17176879920316416, 57798846932913660, 6]⟩,
  ⟨130, 293389, 1, 25,
    rkm128kMask56 512 [4511782072930551, 8822031948166326, 20266374079166752,
      46942161330490503, 12762, 0, 262144, 62294480547479552,
      47193715502251957, 248]⟩,
  ⟨132, 290568, 1, 25,
    rkm128kMask56 513 [53801181007906114, 6252346010674697, 10597609301724817,
      20904916558020872, 464327, 1073741824, 0, 69823386410287104,
      57863740050129519, 506]⟩,
  ⟨134, 285332, 1, 25,
    rkm128kMask56 513 [65816975506604947, 32745925284390758, 20550433725611169,
      4729133233428627, 14541324, 0, 36028797018963968, 36033197213483008,
      20387776877245792, 267]⟩,
  ⟨137, 283397, 1, 25,
    rkm128kMask56 511 [47633273224101383, 19178058019237963, 31709032628824452,
      21233837292851489, 336205721, 4503599761588224, 9007199254749184,
      8388608, 15403400570566032, 122]⟩,
  ⟨139, 277289, 1, 25,
    rkm128kMask56 511 [29540454523458625, 23753437236311690, 3008948064079707,
      13460857488796778, 16933062150, 1128098938748928, 16809984, 35651584,
      53046457310512128, 114]⟩,
  ⟨142, 269254, 1, 25,
    rkm128kMask56 513 [19497347791914338, 4551344721339419, 2788562424575587,
      69989472338560876, 216963650334, 0, 4194304, 4294967428,
      50622222355668992, 434]⟩,
  ⟨144, 272725, 1, 25,
    rkm128kMask56 513 [58867035169798666, 71044041683435761, 59116950489214557,
      53477867506557862, 4840951894277, 0, 16777216, 4503600701112832,
      34226897411966977, 376]⟩,
  ⟨146, 273008, 1, 25,
    rkm128kMask56 511 [5239300691736710, 32665470459808165, 6495102734835532,
      13660459189721978, 213414811043032, 0, 17592186060800,
      18014398509481984, 20587221904064512, 113]⟩,
  ⟨148, 270871, 1, 25,
    rkm128kMask56 512 [808769052583106, 55427569612959612, 6845787597399360,
      11247361150690770, 6951219096546611, 0, 36028797018963968,
      281474976718848, 36534572904611840, 164]⟩,
  ⟨151, 264263, 1, 25,
    rkm128kMask56 513 [24311183307916258, 19326814148659342, 47041096302598250,
      70301541370302978, 1558954108786241, 3, 562949961809920,
      70368760989696, 13371163052867584, 278]⟩,
  ⟨154, 254765, 1, 25,
    rkm128kMask56 513 [9869093742698414, 59133797972711336, 36663625638808398,
      59567378663837692, 56406975363049654, 549755813940, 2251799813685248,
      18031994995736576, 175924146356224, 489]⟩,
  ⟨157, 489525, 2, 25,
    rkm128kMask56 513 [26567900355157449, 22288276031390543, 36079054065353550,
      18929467829868303, 41666028719671774, 281474976727616, 9345848836096,
      1127001565954048, 18023212319244288, 362]⟩,
  ⟨161, 484880, 2, 25,
    rkm128kMask56 509 [63387217656914707, 43250664075154525, 71158175626745849,
      37133112526892443, 43446889478712959, 15084066, 549755879426,
      70368744177664, 22520267087546369, 24]⟩,
  ⟨164, 494123, 2, 25,
    rkm128kMask56 512 [36040593460547321, 18049605473847963, 716838614935031,
      5291103975764208, 38614908079704324, 4446941294, 8594129920,
      35185446093312, 5702651484439680, 212]⟩,
  ⟨168, 485101, 2, 25,
    rkm128kMask56 508 [55065421253175627, 36567818340086129, 28926760123321506,
      14487287270206769, 21415739519076270, 3534654411795, 35185445830656,
      274945146880, 1425516842197064, 13]⟩,
  ⟨173, 481840, 2, 25,
    rkm128kMask56 513 [60453490311826272, 1311001173573798, 6291756635408800,
      31990047616569716, 54328056181727790, 1697658905429010, 0,
      45036133721309252, 18018934003337220, 389]⟩]

/-- Input multiplexing factor entering `lm4k512l248krS1Segs` (`94`). -/
def lm4k512l248krS1LIn : ℕ := 94

/-- Input Hilbert dimension entering `lm4k512l248krS1Segs` (`376`). -/
def lm4k512l248krS1DCurIn : ℕ := 376

/-- Input accumulated `10^15` error pad entering `lm4k512l248krS1Segs`. -/
def lm4k512l248krS1PadIn : ℕ := 1597588745

/-- Slice `0` (`64` entries) of `lm4k512l248krS1VecIn`. -/
def lm4k512l248krS1VecIn0 : List ℤ :=
  [Int.ofNat 952785362, Int.negSucc 542923009, Int.ofNat 405548032, Int.negSucc 1762858524,
   Int.ofNat 775721286, Int.ofNat 569661955, Int.ofNat 185084899, Int.ofNat 5346441652,
   Int.ofNat 2293334418, Int.ofNat 2106928857, Int.negSucc 1373314513, Int.negSucc 2252094153,
   Int.ofNat 1050462918, Int.ofNat 1577934383, Int.ofNat 1925889356, Int.ofNat 4222184758,
   Int.negSucc 6230526295, Int.negSucc 15295151410, Int.negSucc 28714223354,
   Int.negSucc 3394792696, Int.negSucc 973613815, Int.ofNat 2678874398, Int.ofNat 36955805983,
   Int.negSucc 3755382814, Int.ofNat 18018934929, Int.ofNat 17841430560, Int.ofNat 30077949278,
   Int.ofNat 82121521144, Int.ofNat 101162650883, Int.ofNat 10121618612, Int.ofNat 27388298565,
   Int.ofNat 43219969532, Int.ofNat 25454883085, Int.ofNat 27611758700, Int.ofNat 28665018842,
   Int.ofNat 2337991926, Int.negSucc 43396267859, Int.ofNat 74414606404, Int.ofNat 77590222184,
   Int.ofNat 275851918100, Int.negSucc 69225759028, Int.negSucc 55827674314,
   Int.ofNat 176190525886, Int.negSucc 43228351759, Int.negSucc 164395338740,
   Int.negSucc 241927571218, Int.negSucc 323365168006, Int.ofNat 121259931828,
   Int.ofNat 114911217582, Int.negSucc 862114991285, Int.negSucc 164770554543,
   Int.ofNat 370374240828, Int.negSucc 561674681518, Int.ofNat 193031960791,
   Int.ofNat 96744519343, Int.negSucc 182311676362, Int.negSucc 1104340859653,
   Int.negSucc 472079315053, Int.negSucc 758406219421, Int.ofNat 1636537239799,
   Int.ofNat 1266310259509, Int.ofNat 188413243033, Int.ofNat 1372904371391,
   Int.ofNat 631670696759]
/-- Slice `1` (`64` entries) of `lm4k512l248krS1VecIn`. -/
def lm4k512l248krS1VecIn1 : List ℤ :=
  [Int.ofNat 407806229249, Int.ofNat 136905691397, Int.ofNat 1249848603768,
   Int.negSucc 385827874116, Int.negSucc 857990186896, Int.negSucc 1824089048784,
   Int.negSucc 1303645303698, Int.ofNat 83187713973, Int.negSucc 864279446316,
   Int.negSucc 349377393713, Int.negSucc 385300970753, Int.ofNat 901459751182,
   Int.negSucc 42181427538, Int.negSucc 828332758959, Int.ofNat 681520194068,
   Int.ofNat 587982748730, Int.ofNat 49551459488, Int.ofNat 1189882485274,
   Int.ofNat 2237237357012, Int.ofNat 2004882398190, Int.ofNat 1841121743353,
   Int.ofNat 672095172667, Int.negSucc 958754072110, Int.negSucc 3186166657464,
   Int.negSucc 2381859816616, Int.negSucc 649935383541, Int.negSucc 1225301668758,
   Int.negSucc 1377852124470, Int.ofNat 3867752078764, Int.negSucc 824855606895,
   Int.negSucc 1326424118444, Int.ofNat 3542616218997, Int.ofNat 2369610085636,
   Int.negSucc 85208113241, Int.negSucc 958591059267, Int.negSucc 5317987856233,
   Int.negSucc 988295095145, Int.ofNat 1959918439088, Int.negSucc 753904064993,
   Int.ofNat 2450306998558, Int.ofNat 380975147964, Int.negSucc 3003190720285,
   Int.ofNat 2058248202629, Int.negSucc 3655414376640, Int.negSucc 402296506562,
   Int.ofNat 1343698732531, Int.ofNat 1317798891478, Int.ofNat 2863429033957,
   Int.negSucc 750162371766, Int.ofNat 1060696141693, Int.ofNat 4260376762485,
   Int.ofNat 1974450388586, Int.ofNat 1654048417744, Int.ofNat 4711780617014,
   Int.ofNat 1671123324461, Int.negSucc 1956149065481, Int.ofNat 2442721584860,
   Int.negSucc 2167688138923, Int.negSucc 268184262670, Int.ofNat 1019815091961,
   Int.negSucc 2733177931666, Int.ofNat 751019581368, Int.ofNat 3117205336567,
   Int.negSucc 1820635564261]
/-- Slice `2` (`64` entries) of `lm4k512l248krS1VecIn`. -/
def lm4k512l248krS1VecIn2 : List ℤ :=
  [Int.ofNat 2525457874560, Int.ofNat 1970954446636, Int.ofNat 7776393091415,
   Int.ofNat 2680546589514, Int.negSucc 3620471914218, Int.ofNat 1652859504957,
   Int.negSucc 659577496598, Int.ofNat 156428687595, Int.ofNat 382083407592,
   Int.negSucc 5907190334178, Int.ofNat 192816761995, Int.negSucc 850363626602,
   Int.negSucc 3455414594625, Int.negSucc 2205112454159, Int.ofNat 2397014258433,
   Int.ofNat 888347228358, Int.negSucc 2021503916885, Int.negSucc 2054358389931,
   Int.negSucc 4859551017536, Int.ofNat 4624956662429, Int.ofNat 1133855994179,
   Int.negSucc 1792250791803, Int.ofNat 4225491269368, Int.ofNat 3968857367523,
   Int.ofNat 252426249633, Int.ofNat 2226615289894, Int.negSucc 2664671103442,
   Int.ofNat 2452333852704, Int.ofNat 1749787579121, Int.ofNat 1788881702717,
   Int.ofNat 2015136388668, Int.negSucc 6442050915027, Int.ofNat 3743885740573,
   Int.ofNat 2850721151965, Int.ofNat 4770152577001, Int.ofNat 4414719990241,
   Int.ofNat 26902614366975, Int.ofNat 61608900506307, Int.ofNat 105440796051587,
   Int.ofNat 154204626044293, Int.ofNat 203287467524248, Int.ofNat 248251140179587,
   Int.ofNat 285341232231255, Int.ofNat 311860247080109, Int.ofNat 326363694427919,
   Int.ofNat 328670227131992, Int.ofNat 319709791448905, Int.ofNat 301257230855628,
   Int.ofNat 275609022982011, Int.ofNat 245258433705609, Int.ofNat 212612910720851,
   Int.ofNat 179781557655894, Int.ofNat 148443999292051, Int.ofNat 119797676617949,
   Int.ofNat 94570291203885, Int.ofNat 73078472820073, Int.ofNat 55312577975678,
   Int.ofNat 41029856393749, Int.ofNat 29842604403944, Int.ofNat 21292910715931,
   Int.ofNat 14910108246829, Int.ofNat 10250502025677, Int.ofNat 6921212164686,
   Int.ofNat 4591183343976]
/-- Slice `3` (`64` entries) of `lm4k512l248krS1VecIn`. -/
def lm4k512l248krS1VecIn3 : List ℤ :=
  [Int.ofNat 2992806657340, Int.ofNat 1917427081568, Int.ofNat 1207495331575,
   Int.ofNat 747454040638, Int.ofNat 454769743393, Int.ofNat 271931279285,
   Int.ofNat 159781616373, Int.ofNat 92242867854, Int.ofNat 52315020248, Int.ofNat 29146016381,
   Int.ofNat 15951247199, Int.ofNat 8576595811, Int.ofNat 4531323473, Int.ofNat 2353170704,
   Int.ofNat 1201626137, Int.ofNat 603639168, Int.ofNat 298475659, Int.ofNat 145348762,
   Int.ofNat 69748728, Int.ofNat 33001015, Int.ofNat 15403091, Int.ofNat 7095329,
   Int.ofNat 3226858, Int.ofNat 1449268, Int.ofNat 642916, Int.ofNat 281729, Int.ofNat 121942,
   Int.ofNat 52121, Int.ofNat 21990, Int.ofNat 9149, Int.ofNat 3743, Int.ofNat 1501,
   Int.ofNat 583, Int.ofNat 216, Int.ofNat 74, Int.ofNat 22, Int.ofNat 4, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
/-- Slice `4` (`64` entries) of `lm4k512l248krS1VecIn`. -/
def lm4k512l248krS1VecIn4 : List ℤ :=
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
/-- Slice `5` (`57` entries) of `lm4k512l248krS1VecIn`. -/
def lm4k512l248krS1VecIn5 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Checkpoint vector entering `lm4k512l248krS1Segs` (`377` entries). -/
def lm4k512l248krS1VecIn : List ℤ :=
  lm4k512l248krS1VecIn0 ++
    (lm4k512l248krS1VecIn1 ++
    (lm4k512l248krS1VecIn2 ++
    (lm4k512l248krS1VecIn3 ++
    (lm4k512l248krS1VecIn4 ++
    lm4k512l248krS1VecIn5))))

/-- Output multiplexing factor exiting `lm4k512l248krS1Segs` (`173`). -/
def lm4k512l248krS1LOut : ℕ := 173

/-- Output Hilbert dimension exiting `lm4k512l248krS1Segs` (`512`). -/
def lm4k512l248krS1DCurOut : ℕ := 512

/-- Output accumulated `10^15` error pad exiting `lm4k512l248krS1Segs`. -/
def lm4k512l248krS1PadOut : ℕ := 2644249481

/-- Slice `0` (`64` entries) of `lm4k512l248krS1Vec`. -/
def lm4k512l248krS1Vec0 : List ℤ :=
  [Int.negSucc 163089157, Int.ofNat 20291044, Int.ofNat 114596265, Int.ofNat 35954677,
   Int.negSucc 71129089, Int.negSucc 368019737, Int.ofNat 259515579, Int.ofNat 476196286,
   Int.negSucc 69824121, Int.negSucc 712413399, Int.negSucc 1816146081, Int.negSucc 282160223,
   Int.negSucc 735178734, Int.ofNat 1564144967, Int.negSucc 632729679, Int.negSucc 1975484045,
   Int.negSucc 587364311, Int.ofNat 361338986, Int.negSucc 1663423298, Int.ofNat 1387412365,
   Int.negSucc 4350988810, Int.negSucc 3152338730, Int.ofNat 205099848, Int.negSucc 1898579824,
   Int.negSucc 4201087550, Int.negSucc 669383932, Int.negSucc 5717272072,
   Int.negSucc 8979118975, Int.negSucc 7685848358, Int.ofNat 6576127583, Int.negSucc 4485457958,
   Int.ofNat 447582673, Int.ofNat 2741359690, Int.ofNat 2531450253, Int.ofNat 10401050562,
   Int.ofNat 1314971138, Int.ofNat 3275740604, Int.negSucc 5371932287, Int.ofNat 2649938848,
   Int.negSucc 19687040810, Int.negSucc 34373785403, Int.negSucc 3740916063,
   Int.ofNat 10872199228, Int.ofNat 27869553590, Int.ofNat 34005289972, Int.negSucc 24037762313,
   Int.negSucc 9155429675, Int.ofNat 1142443962, Int.ofNat 20791958793, Int.ofNat 13265001650,
   Int.ofNat 10742387077, Int.negSucc 3558517870, Int.negSucc 48148541816,
   Int.negSucc 9620350527, Int.negSucc 24672763677, Int.negSucc 40573049891,
   Int.ofNat 1146486685, Int.ofNat 296439146, Int.ofNat 19422606430, Int.negSucc 8911766846,
   Int.negSucc 17613346201, Int.ofNat 14919281729, Int.negSucc 32200739102,
   Int.negSucc 6915941227]
/-- Slice `1` (`64` entries) of `lm4k512l248krS1Vec`. -/
def lm4k512l248krS1Vec1 : List ℤ :=
  [Int.negSucc 68573696518, Int.ofNat 29090147408, Int.negSucc 46660253357,
   Int.ofNat 29098768008, Int.ofNat 84846887999, Int.ofNat 15354217283, Int.negSucc 28766672293,
   Int.ofNat 34835055918, Int.ofNat 109698292528, Int.ofNat 92939921983, Int.ofNat 38173529176,
   Int.negSucc 20544448724, Int.ofNat 22009777905, Int.ofNat 91150479327,
   Int.ofNat 103688917292, Int.ofNat 79685109903, Int.negSucc 31417714792,
   Int.negSucc 222287422370, Int.negSucc 139125607677, Int.negSucc 131103524272,
   Int.ofNat 57120669905, Int.negSucc 37111861742, Int.negSucc 40626104764,
   Int.ofNat 65196727274, Int.ofNat 115909262373, Int.negSucc 155280732767,
   Int.ofNat 25239966560, Int.ofNat 103347211458, Int.negSucc 34944328129,
   Int.negSucc 48125925078, Int.negSucc 27549413582, Int.ofNat 93398191540,
   Int.negSucc 219251379823, Int.negSucc 150201990618, Int.negSucc 175518461765,
   Int.negSucc 132129930261, Int.negSucc 37574547856, Int.ofNat 29615565707,
   Int.ofNat 53203366586, Int.negSucc 98395813150, Int.ofNat 99843733592,
   Int.negSucc 74544082762, Int.negSucc 59229995156, Int.ofNat 90639502143,
   Int.negSucc 137857734731, Int.negSucc 276910250978, Int.negSucc 415563987670,
   Int.negSucc 482321343917, Int.negSucc 682178398807, Int.negSucc 570393818649,
   Int.ofNat 90870457684, Int.ofNat 923236643910, Int.ofNat 1687624706377,
   Int.ofNat 1424718322786, Int.ofNat 1077453101373, Int.negSucc 195997900599,
   Int.negSucc 1470764803258, Int.negSucc 1549222603903, Int.negSucc 1068074578781,
   Int.ofNat 1685716432124, Int.negSucc 92999697467, Int.negSucc 2134610485527,
   Int.negSucc 1085521962958, Int.ofNat 138781013785]
/-- Slice `2` (`64` entries) of `lm4k512l248krS1Vec`. -/
def lm4k512l248krS1Vec2 : List ℤ :=
  [Int.ofNat 602952479053, Int.negSucc 655024307654, Int.ofNat 90948357068,
   Int.ofNat 424492806576, Int.negSucc 1533947701950, Int.negSucc 1939793382037,
   Int.ofNat 595332176895, Int.negSucc 1591302421945, Int.ofNat 252998273577,
   Int.negSucc 1686698459209, Int.negSucc 490640236072, Int.ofNat 887044089011,
   Int.ofNat 2226991062751, Int.ofNat 2132083247586, Int.ofNat 1508193138962,
   Int.negSucc 1207169955903, Int.negSucc 2495469185324, Int.ofNat 753414065793,
   Int.ofNat 1025423774832, Int.ofNat 63842540061, Int.ofNat 1105932281569,
   Int.ofNat 579058916146, Int.ofNat 107666775934, Int.negSucc 281665803402,
   Int.negSucc 2861948654186, Int.ofNat 4731721141168, Int.ofNat 403500538679,
   Int.negSucc 1656265443908, Int.negSucc 942109822930, Int.ofNat 1631265345975,
   Int.negSucc 695944944196, Int.negSucc 337429627179, Int.ofNat 2005404107617,
   Int.ofNat 848306961284, Int.ofNat 635349859994, Int.negSucc 1522235628393,
   Int.ofNat 158075598026, Int.negSucc 982616904534, Int.negSucc 1357821484105,
   Int.negSucc 1036218428202, Int.negSucc 1051204535109, Int.negSucc 686499343952,
   Int.ofNat 333437446751, Int.ofNat 192066834170, Int.ofNat 2205328777079,
   Int.negSucc 211117858578, Int.ofNat 541697225525, Int.ofNat 478576891498,
   Int.ofNat 489675171992, Int.ofNat 3029524542006, Int.ofNat 2136761196491,
   Int.ofNat 394243694306, Int.negSucc 84433438821, Int.negSucc 4728289734,
   Int.ofNat 1499472605582, Int.ofNat 39877029384, Int.ofNat 999864451012,
   Int.negSucc 1243132959008, Int.negSucc 996417420771, Int.negSucc 135687675073,
   Int.ofNat 2183491672947, Int.ofNat 657699813961, Int.negSucc 2028061785025,
   Int.negSucc 2435288125318]
/-- Slice `3` (`64` entries) of `lm4k512l248krS1Vec`. -/
def lm4k512l248krS1Vec3 : List ℤ :=
  [Int.negSucc 2778928946832, Int.negSucc 7296037146094, Int.negSucc 7500190674474,
   Int.negSucc 7020865784212, Int.negSucc 4237717903303, Int.ofNat 2771121624522,
   Int.ofNat 2458978533676, Int.negSucc 981393561096, Int.negSucc 2077578727168,
   Int.negSucc 1006200830915, Int.negSucc 678273940537, Int.negSucc 1150235274745,
   Int.ofNat 1182354770492, Int.ofNat 2165303184245, Int.negSucc 945075408918,
   Int.ofNat 1007073465487, Int.ofNat 2133639451344, Int.negSucc 1409171741444,
   Int.ofNat 179062039766, Int.ofNat 1237564551872, Int.negSucc 22361504274,
   Int.negSucc 749190637561, Int.negSucc 599433084589, Int.ofNat 211335741170,
   Int.ofNat 1549748530959, Int.negSucc 463347912945, Int.negSucc 1764513779367,
   Int.negSucc 3043549778166, Int.negSucc 333753974481, Int.negSucc 2271513816023,
   Int.negSucc 3453460540182, Int.ofNat 290679699401, Int.negSucc 2101334577149,
   Int.negSucc 1214498647242, Int.ofNat 1720406731529, Int.ofNat 1465576835266,
   Int.ofNat 1571232377232, Int.ofNat 2668236909116, Int.ofNat 2044314662328,
   Int.ofNat 1218172695598, Int.ofNat 1431673210247, Int.negSucc 2201237183961,
   Int.negSucc 1682868633070, Int.ofNat 651222792440, Int.negSucc 3041127494049,
   Int.ofNat 3077037303045, Int.ofNat 2580930790672, Int.negSucc 2532874667941,
   Int.negSucc 3555991582513, Int.negSucc 2812158629833, Int.negSucc 391848880558,
   Int.negSucc 3992034862826, Int.negSucc 4431050514799, Int.negSucc 10351258072344,
   Int.negSucc 15616919920035, Int.negSucc 17756819682851, Int.negSucc 7117478796644,
   Int.negSucc 1287287112273, Int.negSucc 2598818653773, Int.ofNat 3702047568687,
   Int.negSucc 589408682484, Int.negSucc 8418936689841, Int.negSucc 739726900295,
   Int.negSucc 5554531995054]
/-- Slice `4` (`64` entries) of `lm4k512l248krS1Vec`. -/
def lm4k512l248krS1Vec4 : List ℤ :=
  [Int.negSucc 2070517230307, Int.negSucc 8226663232870, Int.ofNat 1640837572304,
   Int.ofNat 3822212004637, Int.negSucc 695249216738, Int.ofNat 441058993008,
   Int.ofNat 5042300688009, Int.negSucc 826895379006, Int.negSucc 1864853737439,
   Int.negSucc 4437112494821, Int.negSucc 2595716722976, Int.negSucc 7997994048886,
   Int.negSucc 95410112338, Int.negSucc 6058037225157, Int.ofNat 515709454525,
   Int.negSucc 4554521122166, Int.ofNat 1334957201655, Int.negSucc 3104570913244,
   Int.negSucc 2329765483306, Int.ofNat 327953577933, Int.negSucc 1835398355073,
   Int.negSucc 7457436594432, Int.ofNat 1123519309189, Int.negSucc 7666169970374,
   Int.ofNat 2411982922963, Int.ofNat 1138170153318, Int.ofNat 7667303427531,
   Int.ofNat 6245560194169, Int.ofNat 1019027265882, Int.ofNat 7274594519243,
   Int.ofNat 1095705285499, Int.ofNat 6639955158818, Int.ofNat 3500381477613,
   Int.negSucc 782625214165, Int.negSucc 693330752062, Int.ofNat 2148406347039,
   Int.negSucc 2665017961811, Int.negSucc 3212485660746, Int.negSucc 2467368162010,
   Int.ofNat 5570773038358, Int.ofNat 8732199262783, Int.ofNat 2073071431366,
   Int.ofNat 4302913797651, Int.negSucc 6720010848138, Int.ofNat 5584903269682,
   Int.ofNat 8570163342146, Int.negSucc 10321793681640, Int.negSucc 2336301272006,
   Int.negSucc 6780971122589, Int.ofNat 6819881265974, Int.negSucc 1190647598704,
   Int.negSucc 8172637643962, Int.ofNat 2344586764458, Int.negSucc 1254221539794,
   Int.ofNat 9157057501316, Int.negSucc 1115519992480, Int.negSucc 5641617188978,
   Int.negSucc 1887064812080, Int.negSucc 4422372554023, Int.ofNat 10432879267628,
   Int.ofNat 2844701423490, Int.negSucc 6547735697896, Int.negSucc 3457437107115,
   Int.negSucc 4434497713056]
/-- Slice `5` (`64` entries) of `lm4k512l248krS1Vec`. -/
def lm4k512l248krS1Vec5 : List ℤ :=
  [Int.negSucc 2270181706204, Int.ofNat 6676903074703, Int.ofNat 6592807161038,
   Int.ofNat 4343624303388, Int.negSucc 10036225368407, Int.negSucc 3726865152320,
   Int.ofNat 4804819812658, Int.ofNat 5213551031824, Int.negSucc 2718636622433,
   Int.ofNat 10278723754190, Int.ofNat 7445748364817, Int.ofNat 12419377466219,
   Int.ofNat 49212251984165, Int.ofNat 99286536477055, Int.ofNat 156237396163659,
   Int.ofNat 213066984899877, Int.ofNat 263610152651387, Int.ofNat 302941143150219,
   Int.ofNat 328465098187964, Int.ofNat 339294159357356, Int.ofNat 335813335604509,
   Int.ofNat 320134214220013, Int.ofNat 295290732418816, Int.ofNat 264238202281961,
   Int.ofNat 229845451773753, Int.ofNat 194775009645560, Int.ofNat 161023437140660,
   Int.ofNat 129916667239385, Int.ofNat 102381467585932, Int.ofNat 78955099346695,
   Int.ofNat 59689766141767, Int.ofNat 44264772421642, Int.ofNat 32207202380265,
   Int.ofNat 23007292786988, Int.ofNat 16136695026495, Int.ofNat 11080832799857,
   Int.ofNat 7400368039027, Int.ofNat 4764920468773, Int.ofNat 2934759722573,
   Int.ofNat 1722620748149, Int.ofNat 965417555623, Int.ofNat 521991349576,
   Int.ofNat 277065235119, Int.ofNat 147707275722, Int.ofNat 81073807024, Int.ofNat 46312704952,
   Int.ofNat 27306056351, Int.ofNat 16438001637, Int.ofNat 9991984387, Int.ofNat 5984588007,
   Int.ofNat 3413792397, Int.ofNat 1807969850, Int.ofNat 883666432, Int.ofNat 404733293,
   Int.ofNat 179762105, Int.ofNat 80888945, Int.ofNat 38117791, Int.ofNat 18888140,
   Int.ofNat 9646941, Int.ofNat 4955099, Int.ofNat 2512386, Int.ofNat 1243500, Int.ofNat 598697,
   Int.ofNat 280815]
/-- Slice `6` (`64` entries) of `lm4k512l248krS1Vec`. -/
def lm4k512l248krS1Vec6 : List ℤ :=
  [Int.ofNat 128278, Int.ofNat 56696, Int.ofNat 24019, Int.ofNat 9734, Int.ofNat 3815,
   Int.ofNat 1487, Int.ofNat 589, Int.ofNat 238, Int.ofNat 94, Int.ofNat 32, Int.negSucc 9,
   Int.ofNat 2, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
/-- Slice `7` (`64` entries) of `lm4k512l248krS1Vec`. -/
def lm4k512l248krS1Vec7 : List ℤ :=
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
/-- Slice `8` (`1` entries) of `lm4k512l248krS1Vec`. -/
def lm4k512l248krS1Vec8 : List ℤ :=
  [Int.ofNat 0]
/-- Checkpoint vector exiting `lm4k512l248krS1Segs` (`513` entries). -/
def lm4k512l248krS1Vec : List ℤ :=
  lm4k512l248krS1Vec0 ++
    (lm4k512l248krS1Vec1 ++
    (lm4k512l248krS1Vec2 ++
    (lm4k512l248krS1Vec3 ++
    (lm4k512l248krS1Vec4 ++
    (lm4k512l248krS1Vec5 ++
    (lm4k512l248krS1Vec6 ++
    (lm4k512l248krS1Vec7 ++
    lm4k512l248krS1Vec8)))))))

end

public section

open QuantumComputation.Specs.DickeSol

private abbrev s1P : ℕ → ℤ := Int.ofNat
private abbrev s1N : ℕ → ℤ := Int.negSucc
private theorem s1AndLeft {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl
private theorem s1AndRight {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => rfl
private def s1NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem s1Ble_le : ∀ {a b : ℕ}, Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | _ + 1, 0, h => by cases h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (s1Ble_le h)
private theorem s1NatEq_eq {x y : ℕ} (h : s1NatEq x y = true) : x = y :=
  Nat.le_antisymm (s1Ble_le (s1AndLeft h)) (s1Ble_le (s1AndRight h))
private def s1IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat x, Int.ofNat y => s1NatEq x y
  | Int.negSucc x, Int.negSucc y => s1NatEq x y
  | _, _ => false
private theorem s1IntEq_eq {a b : ℤ} (h : s1IntEq a b = true) : a = b := by
  cases a with
  | ofNat _ =>
    cases b with
    | ofNat _ => exact congrArg Int.ofNat (s1NatEq_eq h)
    | negSucc _ => cases h
  | negSucc _ =>
    cases b with
    | ofNat _ => cases h
    | negSucc _ => exact congrArg Int.negSucc (s1NatEq_eq h)
private def s1IntListEq (xs ys : List ℤ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (s1IntEq x y) (s1IntListEq xr yr) false
  | _, _ => false
private theorem s1IntListEq_eq {xs ys : List ℤ} (h : s1IntListEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x _ ih =>
    cases ys with
    | nil => cases h
    | cons y _ =>
      dsimp only [s1IntListEq] at h
      cases hxy : s1IntEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (s1IntEq_eq hxy) (ih h)
private def s1StateEq (s1 s2 : ℕ × ℕ × ℕ × List ℤ) : Bool :=
  match s1, s2 with
  | (l1, d1, p1, v1), (l2, d2, p2, v2) =>
    Bool.and (s1NatEq l1 l2)
      (Bool.and (s1NatEq d1 d2) (Bool.and (s1NatEq p1 p2) (s1IntListEq v1 v2)))
private theorem s1StateEq_eq {s1 s2 : ℕ × ℕ × ℕ × List ℤ} (h : s1StateEq s1 s2 = true) :
    s1 = s2 := by
  rcases s1 with ⟨_, _, _, _⟩
  rcases s2 with ⟨_, _, _, _⟩
  dsimp only [s1StateEq] at h
  have h1 := s1AndLeft h
  have hr1 := s1AndRight h
  have h2 := s1AndLeft hr1
  have hr2 := s1AndRight hr1
  rw [s1NatEq_eq h1, s1NatEq_eq h2, s1NatEq_eq (s1AndLeft hr2),
    s1IntListEq_eq (s1AndRight hr2)]
private def s1RunAtEq (c : List Rkm128kSeg)
    (lI dI pI : ℕ) (vI : List ℤ) (lO dO pO : ℕ) (vO : List ℤ) : Bool :=
  s1StateEq (rkm128kRunSegs 4 248 512 c lI dI pI vI) (lO, dO, pO, vO)
private theorem s1RunStep {c rest : List Rkm128kSeg}
    {lI dI pI l1 d1 p1 : ℕ} {vI v1 : List ℤ} {stOut : ℕ × ℕ × ℕ × List ℤ}
    (h1 : s1RunAtEq c lI dI pI vI l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 4 248 512 rest l1 d1 p1 v1 = stOut) :
    rkm128kRunSegs 4 248 512 (c ++ rest) lI dI pI vI = stOut := by
  unfold s1RunAtEq at h1
  rw [rkm128kRunSegs_append]
  dsimp only
  rw [s1StateEq_eq h1]
  dsimp only
  exact h2
private theorem s1RunLast {c : List Rkm128kSeg}
    {lI dI pI lO dO pO : ℕ} {vI vO : List ℤ}
    (h : s1RunAtEq c lI dI pI vI lO dO pO vO = true) :
    rkm128kRunSegs 4 248 512 c lI dI pI vI = (lO, dO, pO, vO) := s1StateEq_eq h
private def s1Ch0 : List Rkm128kSeg := [
  ⟨95, 353612, 1, 24,
    rkm128kMask56 380 [51090471939721169, 6005782909026183, 57631622085376594, 0,
      137438953472, 17904447346704384, 9524325271313]⟩,
  ⟨99, 344541, 1, 24,
    rkm128kMask56 395 [54317361530748212, 16332451370986254, 44456040198359056,
      562949953421338, 2251834173423616, 2250700436275200,
      37027898111711175, 5]⟩,
  ⟨102, 339843, 1, 24,
    rkm128kMask56 409 [63149378947633664, 11592209005708573, 49676014399365076, 934,
      9007199254740992, 36591747509256192, 43836776551278343, 102835]⟩,
  ⟨104, 334185, 1, 24,
    rkm128kMask56 416 [31332017245463126, 23057766536910864, 11557697343998113,
      140737488380556, 68719476736, 134217729, 8218975378865121, 15947338]⟩]
private def s1V0S0 : List ℤ :=
  [s1N 170034314, s1P 713603700, s1P 678927635, s1N 1734913520, s1P 457897344, s1N 1236535348,
   s1P 308126239, s1N 780607263, s1P 945407599, s1N 4759722353, s1N 1598107278, s1P 2632038344,
   s1P 1697962040, s1P 370758545, s1P 3841322492, s1N 3413777241, s1P 6146224621,
   s1P 2672262836, s1N 666591426, s1N 8195985842, s1P 1621769081, s1N 10337658425,
   s1N 18828092711, s1N 30173253437, s1N 27159832253, s1N 14044889433, s1P 21126857855,
   s1N 27174527190, s1N 42888609954, s1N 17788296544, s1P 5738954868, s1N 29013826889,
   s1N 50979662291, s1N 41588169430, s1P 55558432723, s1N 39503307962, s1P 65112976813,
   s1P 51828596408, s1P 270081894049, s1P 62968506694, s1N 181689901956, s1P 123825202809,
   s1N 138553880257, s1P 180063586155, s1P 255229797240, s1P 103082428541, s1P 358673498898,
   s1P 102312751342, s1P 38969834030, s1P 447259600810, s1P 65420906840, s1P 137079064892,
   s1P 251024558503, s1P 32280181128, s1N 182633456640, s1N 371726427044, s1N 274523909831,
   s1N 250022274840, s1N 865922230917, s1N 856226998204, s1P 278792902749, s1N 197328663387,
   s1P 1178200387237, s1N 2225559302282]
private def s1V0S1 : List ℤ :=
  [s1P 658650612992, s1N 92322620509, s1P 33915923031, s1N 1040300698231, s1N 964836467587,
   s1P 308816101053, s1N 231358257333, s1P 544282649991, s1P 108471234156, s1P 456225923519,
   s1N 108196670210, s1P 585629869377, s1P 194257428444, s1N 869959886648, s1P 417902591133,
   s1P 744957438829, s1N 812279330874, s1P 1689305859739, s1P 888129578, s1P 1691744414688,
   s1P 2008700585781, s1N 352533295225, s1N 2089563683725, s1P 476027723421, s1P 550076214865,
   s1P 71590564060, s1P 2802154172506, s1N 530923491762, s1P 119297186029, s1P 590823342831,
   s1P 1885253411153, s1P 3786396575750, s1N 359278435364, s1N 3320205672759, s1N 1695855001148,
   s1N 4214442888827, s1P 2386662099822, s1P 5075708737617, s1P 1019247335954,
   s1P 2072755756329, s1P 1333676201991, s1N 4512287457649, s1N 2189354512859,
   s1N 2979079263347, s1N 1494270186648, s1P 56366892378, s1N 1092051545342, s1P 2284685885435,
   s1P 4391257609644, s1N 1123644935131, s1N 520806361648, s1P 1239308090917, s1P 133782893112,
   s1P 2180502089714, s1P 1382061741968, s1P 854092222771, s1N 220138236824, s1P 3202753725812,
   s1P 3986311661235, s1N 2487875706880, s1N 2058178023910, s1P 90513807101, s1N 889535089645,
   s1P 3207766437988]
private def s1V0S2 : List ℤ :=
  [s1P 3450922854531, s1P 1382198613449, s1P 2304840772821, s1P 2115521310578, s1P 652590949085,
   s1N 2315605469192, s1N 2125098676969, s1N 4909796258963, s1N 3438612659190,
   s1N 2242569999659, s1P 5083573369346, s1P 4455400314087, s1P 3309277783283,
   s1N 1920494699331, s1N 2642304747385, s1N 2972221209717, s1N 3867204718749,
   s1P 1740173197687, s1N 1192281816363, s1P 1876687458703, s1N 6786580076086,
   s1P 1528823780268, s1N 483411968377, s1N 3591326148801, s1P 757918824455, s1P 1448527421508,
   s1P 3918385980838, s1P 3279900576676, s1P 1100729756091, s1P 3177680093169, s1N 377973792780,
   s1P 3013168814426, s1N 3192475528877, s1P 8033516342655, s1N 2638546527380,
   s1P 3906515872905, s1N 1094337035539, s1N 3279897572273, s1N 3701595301837, s1P 860363590259,
   s1N 2828638118590, s1N 1524747821595, s1N 4536571902451, s1P 1414902654526, s1P 501887472657,
   s1N 543466195869, s1N 4879255166990, s1P 858441400768, s1N 1529208971497, s1P 3020740205242,
   s1P 1250063951873, s1P 4430461304878, s1P 1031569267827, s1P 4469131904037,
   s1P 3596732016298, s1P 9446016786478, s1P 36106133723067, s1P 74546010146860,
   s1P 121018447754693, s1P 170884191898925, s1P 219362821571394, s1P 262131341862541,
   s1P 295780772968726, s1P 318101325829930]
private def s1V0S3 : List ℤ :=
  [s1P 328179628799870, s1P 326320573466986, s1P 313831974159282, s1P 292725164148216,
   s1P 265387685563450, s1P 234277200487136, s1P 201672080710799, s1P 169497773900344,
   s1P 139232565100943, s1P 111884256936802, s1P 88021832757549, s1P 67843117358261,
   s1P 51260526691892, s1P 37989223369044, s1P 27628617471607, s1P 19727038816604,
   s1P 13834949864951, s1P 9532281533986, s1P 6456181561717, s1P 4298216791174,
   s1P 2813958987578, s1P 1812504334836, s1P 1147829810753, s1N 715018959766, s1P 438748511549,
   s1P 264810572679, s1P 156830189445, s1P 91408371992, s1P 52770917781, s1P 30137912907,
   s1P 16787136349, s1P 8953247882, s1P 4528279727, s1P 2186543870, s1P 1032249573,
   s1P 492465385, s1P 243445330, s1P 124892086, s1P 65255727, s1P 33941937, s1P 17302706,
   s1P 8586350, s1P 4144712, s1P 1950499, s1P 897742, s1P 405350, s1P 179985, s1P 78714,
   s1P 33939, s1P 14426, s1P 6037, s1P 2481, s1P 996, s1P 386, s1P 141, s1P 46, s1P 14, s1P 2,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V0S4 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V0S5 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V0S6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V0 : List ℤ :=
  s1V0S0 ++
    (s1V0S1 ++
    (s1V0S2 ++
    (s1V0S3 ++
    (s1V0S4 ++
    (s1V0S5 ++
    s1V0S6)))))
private def s1Ch1 : List Rkm128kSeg := [
  ⟨106, 330645, 1, 24,
    rkm128kMask56 425 [38098804443931233, 64142740849034645, 51840339511450431, 876751, 0,
      18014398509481984, 42514591018647552, 8257450535]⟩,
  ⟨108, 330077, 1, 24,
    rkm128kMask56 433 [56797832890902368, 29043361633098237, 43252845554496642, 29648940, 0,
      1128101077581824, 69725598594892800, 1804691424445]⟩,
  ⟨111, 320936, 1, 24,
    rkm128kMask56 445 [7597397632320885, 35692540925882097, 17477155324942264, 931465717,
      4398046511104, 549755813888, 5031657266479104, 4522597385355509]⟩,
  ⟨113, 328427, 1, 25,
    rkm128kMask56 453 [25786127655541072, 63686575007729705, 2219708198341708, 31324134278,
      0, 0, 32768, 3144619015422076, 17]⟩]
private def s1V1S0 : List ℤ :=
  [s1N 384094518, s1N 624609482, s1N 1989194222, s1N 134115465, s1N 975742330, s1N 461223282,
   s1N 2090017957, s1N 1830660921, s1P 1259852098, s1N 569518781, s1P 165904811, s1N 739342491,
   s1N 2072335602, s1P 2515838643, s1N 3682233666, s1P 8245392435, s1P 1448459895,
   s1N 6625346105, s1N 5456381982, s1P 3407172584, s1P 3349027495, s1P 4195597672,
   s1P 9034469166, s1N 358801646, s1N 13933520740, s1P 1124355776, s1P 12696987793,
   s1P 14657438840, s1P 7412571783, s1N 3516030149, s1P 16386507851, s1P 2707358369,
   s1N 35325697805, s1N 44676061327, s1N 48430448670, s1N 27002653158, s1N 88693460211,
   s1N 78289779382, s1N 162572903226, s1N 183021249852, s1N 196109290040, s1N 95802065882,
   s1N 116759318378, s1N 90275307860, s1N 356499642340, s1N 173359271559, s1N 31796552967,
   s1N 243004605824, s1P 9822856467, s1N 241567384380, s1N 85881823775, s1N 306738884736,
   s1N 14007619929, s1N 220197589179, s1P 87849807469, s1P 144588724447, s1N 192679871965,
   s1P 169608601147, s1P 113103819772, s1N 229559205252, s1N 339509170595, s1P 373730632325,
   s1P 80116562738, s1P 519075245792]
private def s1V1S1 : List ℤ :=
  [s1P 434417576456, s1P 137112774007, s1N 368098171763, s1N 4952201638, s1N 642241609897,
   s1N 1914182402556, s1N 1789386235993, s1N 1213382796435, s1N 652320765297, s1N 409317530421,
   s1N 917327883460, s1P 184108425885, s1P 1081001240057, s1P 20859447599, s1P 264226909673,
   s1N 1449262595772, s1N 1430955014659, s1N 1248471933373, s1P 1511904871545,
   s1N 1371827125248, s1N 782772000215, s1P 382486876108, s1N 1643305647147, s1P 330621240884,
   s1P 1205718282187, s1P 678684021606, s1P 2046911583408, s1P 722526655594, s1P 1742051666460,
   s1N 1633497654976, s1P 819180570803, s1N 1985229022030, s1N 1446788730428, s1N 1373440598994,
   s1N 829940454748, s1N 1203765411591, s1N 93445172, s1N 1023790980384, s1N 129890671081,
   s1P 2449205022484, s1P 317589678024, s1N 182395023973, s1N 1659316890929, s1P 779481813488,
   s1P 1359871146646, s1P 4140501332742, s1P 5019134715799, s1P 5074182269015,
   s1P 3872928589172, s1P 2819847406991, s1N 1378717724246, s1N 460398355866, s1N 143662017547,
   s1P 1065739403933, s1P 461731516014, s1N 3156228655840, s1N 1454662129372, s1P 1317066011472,
   s1N 1733490659903, s1P 2779739214338, s1N 3444780016618, s1N 3125961088473, s1P 903025824189,
   s1P 1462541780848]
private def s1V1S2 : List ℤ :=
  [s1N 1159809853609, s1N 1340646394974, s1P 5715723363126, s1N 1970126861072, s1N 575816880805,
   s1N 1700058931374, s1P 788960506420, s1N 2191154254176, s1N 540708306538, s1N 4164675903912,
   s1N 1911040358382, s1N 1674029701648, s1P 294111857097, s1P 1551489155536, s1P 1399377141433,
   s1P 5250645020216, s1P 2560082981779, s1P 2794394028143, s1P 178431847300, s1N 1412175875286,
   s1N 2603894618458, s1P 4658652709071, s1P 2930532198567, s1P 10239883564146,
   s1P 2495267843307, s1N 666063335592, s1P 2059317427022, s1P 6242618479175, s1N 189270120143,
   s1N 2189555028141, s1P 2714725604488, s1P 4606828810085, s1P 3476828253691, s1N 400700364712,
   s1N 643744453410, s1N 671909495558, s1N 1188448940909, s1N 6669319423370, s1N 6191719290497,
   s1N 1497417455332, s1P 410848299408, s1P 3851325694170, s1P 106982881213, s1P 1589204531055,
   s1N 979964898695, s1N 2831999889506, s1N 4959318677902, s1N 67874938261, s1P 2133596285521,
   s1N 228103071204, s1N 1358993577300, s1P 2361156003671, s1N 585010253633, s1N 4853180640712,
   s1N 1692706583444, s1N 453290508183, s1P 3349467051736, s1P 613827989381, s1N 3470813484484,
   s1N 6049295716096, s1P 2586716671828, s1P 705848557155, s1P 2095850838673, s1P 2943029420028]
private def s1V1S3 : List ℤ :=
  [s1N 282637390631, s1P 3268741621730, s1P 654665285951, s1N 5372709779563, s1P 891207022026,
   s1N 4529256354218, s1P 592818668176, s1P 2338420922093, s1P 241145846251, s1P 5125301913593,
   s1P 4617342109208, s1P 9064894905470, s1P 36058707026597, s1P 74794696715635,
   s1P 122424427137037, s1P 172758937926011, s1P 221153671265827, s1P 264213079971984,
   s1P 297577708803313, s1P 318877555809983, s1P 328335590067310, s1P 326143323021243,
   s1P 312894791351073, s1P 291082209502602, s1P 263747572247268, s1P 232919161102259,
   s1P 200286329493199, s1P 168021795971322, s1P 138080222384985, s1P 111332955635192,
   s1P 87849184872149, s1P 67666045691085, s1P 50984396251597, s1P 37819278584707,
   s1P 27761559398626, s1P 20133876964582, s1P 14302382482209, s1P 9844841917906,
   s1P 6518436516926, s1P 4148517874196, s1P 2554461844497, s1P 1541175863716, s1P 925365982949,
   s1P 560396532296, s1P 344379768703, s1P 214119094333, s1P 133459573116, s1P 82495262894,
   s1P 50115511518, s1P 29740904807, s1P 17186007958, s1P 9660386680, s1P 5285461666,
   s1P 2819940775, s1P 1471171837, s1P 753057641, s1P 379615759, s1P 189137866, s1P 93424008,
   s1P 45845734, s1P 22371946, s1P 10853660, s1P 5229113, s1P 2497730]
private def s1V1S4 : List ℤ :=
  [s1P 1180736, s1P 551494, s1P 254175, s1P 115477, s1P 51677, s1P 22765, s1P 9863, s1P 4194,
   s1P 1746, s1P 706, s1P 273, s1P 99, s1P 30, s1P 8, s1P 1, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V1S5 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V1S6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V1S7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V1 : List ℤ :=
  s1V1S0 ++
    (s1V1S1 ++
    (s1V1S2 ++
    (s1V1S3 ++
    (s1V1S4 ++
    (s1V1S5 ++
    (s1V1S6 ++
    s1V1S7))))))
private def s1Ch2 : List Rkm128kSeg := [
  ⟨116, 311021, 1, 25,
    rkm128kMask56 465 [16765882419554813, 2342828890353532, 13669942897034430, 879773903641,
      8796093022208, 18049651601063968, 2097152, 66233893411094528, 125721]⟩,
  ⟨120, 611385, 2, 25,
    rkm128kMask56 479 [68017673919506302, 37733850096927345, 33780419018293710,
      1006429499563489, 0, 2048, 281474977103872, 39137941091516416,
      1750514053]⟩]
private def s1V2S0 : List ℤ :=
  [s1P 580322079, s1P 812846127, s1N 651187648, s1N 1037010033, s1N 157573971, s1N 2268971597,
   s1N 368588313, s1N 553369497, s1N 403631348, s1N 2056658710, s1N 841656345, s1P 1409155973,
   s1P 2658812122, s1P 4283094476, s1P 5801498205, s1P 7984957746, s1P 4302481341,
   s1P 5256838499, s1P 2111631420, s1P 216067939, s1N 147392566, s1N 3079004890, s1P 4415424375,
   s1N 8657394024, s1P 1646719120, s1P 4781329214, s1P 1314237850, s1P 918265303,
   s1N 4598434609, s1N 12930676895, s1P 24543661, s1P 4616719599, s1P 4061851463,
   s1P 24726747938, s1P 56379444695, s1P 60435570294, s1P 10389620714, s1P 45634678941,
   s1P 52277960844, s1P 57279657622, s1P 121011061943, s1P 177442376109, s1P 167553085675,
   s1P 142193817115, s1P 107568839755, s1P 48532647072, s1P 7134577622, s1P 95181604269,
   s1P 93695474809, s1N 135118339987, s1N 229330563566, s1N 503991722450, s1N 47499429379,
   s1P 15592947061, s1N 110840860768, s1N 46505604638, s1N 40653971006, s1P 127180294738,
   s1P 321870557266, s1P 428556083382, s1P 348958975074, s1P 419259081826, s1N 137393915578,
   s1N 113539624846]
private def s1V2S1 : List ℤ :=
  [s1N 28476149405, s1N 378419793925, s1N 84832288902, s1N 397147662725, s1P 244154075486,
   s1N 367405591757, s1P 593668740732, s1P 768804925062, s1P 1341324677011, s1P 431865582451,
   s1P 134319900235, s1N 34132216163, s1N 864619440180, s1N 1412874082819, s1N 89715431905,
   s1P 97153815977, s1N 1674801246162, s1N 2899709749490, s1N 1006463378897, s1P 831323259498,
   s1P 887213254020, s1P 623664555347, s1N 19966992310, s1P 825266412728, s1N 1007710511543,
   s1N 2678052309713, s1N 739247426773, s1N 17998814088, s1P 578717015570, s1P 2558785245173,
   s1P 428498448937, s1P 497971988787, s1N 1896857517660, s1N 981947523378, s1N 2650826512709,
   s1N 21859593209, s1P 851387517722, s1P 1259435640941, s1N 968461487406, s1P 894917125398,
   s1P 710054037722, s1P 1735746567241, s1P 426031101394, s1P 1038762948749, s1P 596246415009,
   s1P 311434928129, s1P 1958424450480, s1P 605717787830, s1N 1412091357115, s1P 895328033699,
   s1N 120847381240, s1N 623721275775, s1N 1654503327041, s1N 926971444583, s1P 900965896469,
   s1N 1306096173990, s1N 971260008288, s1N 256580320048, s1N 2942987636094, s1N 82992782008,
   s1N 6258676962385, s1N 6333732786964, s1N 4347370245699, s1N 2390259196304]
private def s1V2S2 : List ℤ :=
  [s1P 2478529415282, s1P 1997068518510, s1P 94955893733, s1N 2067942165587, s1N 925716991209,
   s1P 1125118479068, s1P 3394202566736, s1P 3901809210296, s1P 4257977296957,
   s1P 4368308070925, s1P 2640916024798, s1N 264450530844, s1P 621041888009, s1N 27951750305,
   s1P 466181796480, s1N 790042565912, s1N 2533919331327, s1N 2079638662922, s1N 830082353782,
   s1P 203488766340, s1N 1285580640479, s1N 1133652795677, s1N 3131697886130, s1N 6208659840516,
   s1N 6080334051283, s1N 7773304812006, s1N 3586487934197, s1N 1787049419733,
   s1P 1770310438654, s1N 290687978536, s1N 2280053211764, s1N 5033037054193, s1N 2543036404467,
   s1P 2331685416738, s1N 1003658265141, s1N 1519731217166, s1N 1932166890867,
   s1N 5889936000227, s1N 5296748332946, s1P 1680045405472, s1P 6376879248317,
   s1P 4965790990717, s1P 3812829659170, s1P 551837788998, s1N 2079551430525, s1N 1035514203154,
   s1N 4074041469853, s1N 582366854934, s1N 4806604408003, s1N 5816253600030, s1N 443632903716,
   s1P 1225825314521, s1P 5046844096544, s1P 2511915924001, s1N 2336923749016,
   s1P 1891259311504, s1P 1907743885809, s1P 4138639923571, s1P 1663752030137,
   s1P 4336728432485, s1P 2017937260314, s1P 3521455296045, s1N 249083787450, s1P 2554524605077]
private def s1V2S3 : List ℤ :=
  [s1P 710630008298, s1N 2038262401186, s1P 4744606801537, s1N 3922931191942, s1N 2823180518764,
   s1P 1301606090320, s1N 1019043059944, s1N 1398292558044, s1N 966913345120, s1N 3509263623787,
   s1N 2112210752209, s1P 255996869861, s1N 2551448685624, s1P 2319703383583, s1N 339407937163,
   s1P 1633073407754, s1N 2663218119207, s1P 180869085286, s1N 2722800389757, s1N 545032772152,
   s1N 4300218008736, s1P 6388209173412, s1P 2664709336655, s1P 4908528074803,
   s1P 10171421021326, s1P 6207693512128, s1P 10982114654086, s1P 41473187112675,
   s1P 82836564319835, s1P 131409558578155, s1P 182526592090186, s1P 230960351726469,
   s1P 272125919065978, s1P 303027933916621, s1P 322196383948973, s1P 329169892105331,
   s1P 324341801061862, s1P 309124351835324, s1P 285854959191606, s1P 257254752238641,
   s1P 225819588794423, s1P 193547824379657, s1P 162010187992995, s1P 132487639165867,
   s1P 105976510875269, s1P 83089164081331, s1P 63993945594123, s1P 48479731326243,
   s1P 36113437723047, s1P 26401366959169, s1P 18889008353771, s1P 13190253204449,
   s1P 8975242989708, s1P 5950725927320, s1P 3851045725391, s1P 2440807681047,
   s1P 1521955872160, s1P 938276066245, s1P 574421178573, s1P 350248519696, s1P 212891295445,
   s1P 128848790595, s1P 77445768044, s1P 46074485891]
private def s1V2S4 : List ℤ :=
  [s1P 27042115110, s1P 15615360885, s1P 8854354003, s1P 4924723742, s1P 2685925969,
   s1P 1436920975, s1P 754693666, s1P 389619142, s1P 197988449, s1P 99186981, s1P 49066898,
   s1P 23993371, s1P 11604622, s1P 5559602, s1P 2643846, s1P 1247167, s1P 579742, s1P 262670,
   s1P 114926, s1P 48483, s1P 19902, s1P 8095, s1P 3323, s1P 1388, s1P 585, s1P 240, s1P 92,
   s1P 31, s1P 9, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V2S5 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V2S6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V2S7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V2 : List ℤ :=
  s1V2S0 ++
    (s1V2S1 ++
    (s1V2S2 ++
    (s1V2S3 ++
    (s1V2S4 ++
    (s1V2S5 ++
    (s1V2S6 ++
    s1V2S7))))))
private def s1Ch3 : List Rkm128kSeg := [
  ⟨124, 605358, 2, 25,
    rkm128kMask56 495 [60816456438084825, 61991780913118504, 58381819253402552,
      2621264438430876, 15, 36028805608898560, 0, 10182645904310272,
      81231589695177]⟩,
  ⟨128, 313169, 1, 26,
    rkm128kMask56 507 [16390821414923705, 24454116875453930, 68540563171904072,
      212491092015554, 36028797018964356, 9007199254740992, 33554432,
      17176879920316416, 57798846932913660, 6]⟩]
private def s1V3S0 : List ℤ :=
  [s1P 139742672, s1P 130530092, s1P 788768864, s1N 1536482365, s1N 824223265, s1N 9640228,
   s1N 1307392615, s1N 1592942063, s1N 806721175, s1N 1087865961, s1N 1358228596,
   s1P 1596219291, s1P 374634306, s1N 1921255651, s1P 743390810, s1P 5163169864, s1P 4514727978,
   s1N 2177929955, s1N 791573055, s1N 7062310538, s1N 752428580, s1N 5836223394, s1N 5254945392,
   s1N 8421754522, s1N 6488073576, s1N 2616089655, s1P 7680325472, s1N 3713679750,
   s1P 1035811756, s1P 2062980031, s1N 4807327275, s1N 22295580814, s1P 4466820800,
   s1N 27925794235, s1N 12283889158, s1P 14307143114, s1P 12606031638, s1N 9381898118,
   s1N 26896169522, s1N 20145446419, s1N 43376285252, s1N 14356326890, s1N 34519461284,
   s1N 54632648539, s1N 72041159406, s1N 137300036467, s1N 142113402585, s1N 74236387554,
   s1N 70845280705, s1N 83181252889, s1N 116404852224, s1N 270596762054, s1N 277458741161,
   s1P 47206380128, s1P 208045337775, s1P 145110500736, s1N 43314617079, s1N 349222432450,
   s1P 64950168905, s1P 447280173423, s1N 168438780493, s1P 84423706039, s1P 276958253070,
   s1N 506572809997]
private def s1V3S1 : List ℤ :=
  [s1N 465830501435, s1P 68095288916, s1P 152756330008, s1P 265614295905, s1N 273099228434,
   s1P 64125264171, s1P 108447676938, s1N 547456478280, s1N 180345025251, s1N 520952601476,
   s1N 249365897568, s1N 251729406775, s1P 754688648721, s1P 451075824112, s1N 619721199056,
   s1N 120611232344, s1P 231779586860, s1P 456847124175, s1P 709602696727, s1P 1264198365704,
   s1P 1773826807055, s1P 2752700147406, s1P 2211837663172, s1P 851949537855, s1N 1805270426554,
   s1N 65401263847, s1P 1085613814465, s1N 41252006657, s1N 253633895160, s1P 2077784670330,
   s1N 750256006937, s1P 1002205368405, s1N 1709184080510, s1N 972997563146, s1P 1784250976453,
   s1P 747946977340, s1N 1203875813579, s1N 1407491564037, s1N 1795550368233, s1P 872132434041,
   s1N 915080724260, s1N 1603494267785, s1N 2295139308944, s1N 122913862417, s1P 1622278953459,
   s1P 1865434104385, s1P 585806622280, s1P 639405711647, s1P 1398358124389, s1N 875417981085,
   s1N 852296505688, s1N 634983755, s1P 1326398772541, s1P 1998570837530, s1P 145610361381,
   s1N 1611663750885, s1N 2726980792387, s1N 414996839133, s1P 798170386327, s1N 962297442953,
   s1N 1069935230348, s1N 1372089859832, s1P 894823491846, s1N 610440791479]
private def s1V3S2 : List ℤ :=
  [s1P 822356312591, s1P 1125859441984, s1P 879212153578, s1N 1406477677799, s1N 77992651071,
   s1P 1114936622314, s1N 887623552201, s1P 1836805227559, s1P 400832645392, s1P 3403792475458,
   s1P 7295124119526, s1P 4808622140928, s1N 2845191327536, s1N 4796156544062,
   s1P 2237087122571, s1P 3882954208964, s1N 509737904960, s1P 4300125921951, s1P 1231959551927,
   s1P 649295283797, s1P 2802472540232, s1P 2841190477264, s1N 489797679178, s1P 2535700885072,
   s1P 620993692220, s1N 3172455801045, s1N 1387520606808, s1P 127116047303, s1N 1095963050221,
   s1P 50731695388, s1N 1936537952802, s1N 545148521424, s1N 322632888880, s1N 3208071027052,
   s1N 2570682426898, s1N 2370329537497, s1N 1087465858684, s1N 7531179680787,
   s1N 10586822602911, s1N 3084760817961, s1N 141925160592, s1N 3057639035869,
   s1N 2525984416646, s1P 8443900707132, s1N 2663586916740, s1N 3997033834099,
   s1P 2570806617681, s1P 965718806670, s1N 1525889803925, s1N 3643056951753, s1N 4890543007563,
   s1P 1840756574381, s1N 370177357849, s1N 4096528638565, s1N 3149511413465, s1P 6561817241557,
   s1P 2922278713739, s1P 1219766340250, s1P 3166934321083, s1N 935271925517, s1P 2438459437482,
   s1P 2412068045277, s1P 9617500576135, s1N 1750996793612]
private def s1V3S3 : List ℤ :=
  [s1P 3701999619068, s1N 1817354959317, s1P 1595276293996, s1N 1849140698880,
   s1N 1289380309003, s1P 2675160028255, s1P 1299886453703, s1P 646009372015, s1N 4767389326062,
   s1P 1272151186495, s1P 901841702227, s1N 3777332839502, s1N 1569124397548, s1N 294196100723,
   s1P 3448973613145, s1P 866999328387, s1N 1765128824934, s1N 3618584183615, s1N 375424242341,
   s1P 2997146849271, s1N 988736689534, s1N 3563885654278, s1P 1471091760022, s1N 1699279165368,
   s1N 4503398739944, s1N 1334900500073, s1N 1056631728557, s1P 1771977727330,
   s1N 5992348090543, s1P 4279403921023, s1P 8330717392994, s1N 4246784601650,
   s1N 7623927213177, s1P 2729731179579, s1N 2302826819713, s1N 2758940709061, s1P 630614131454,
   s1P 5674142648258, s1P 3236025969450, s1P 3551132820864, s1P 4761024424314,
   s1P 7118313105021, s1P 34036767859391, s1P 73683522660546, s1P 121660191434765,
   s1P 172927357530449, s1P 222490405144618, s1P 265814187156135, s1P 299290796284239,
   s1P 320693986583137, s1P 329366658360968, s1P 326026972203432, s1P 312329644383474,
   s1P 290422102587585, s1P 262639330936441, s1P 231324564939867, s1P 198689322322541,
   s1P 166660993593436, s1P 136738109571621, s1P 109907708307442, s1P 86657840530755,
   s1P 67072273088257, s1P 50962652801414, s1P 37991872144804]
private def s1V3S4 : List ℤ :=
  [s1P 27762424665904, s1P 19867001134442, s1P 13912682712142, s1P 9532436468117,
   s1P 6392835556887, s1P 4200918300892, s1P 2709399186885, s1P 1718629109604,
   s1P 1074633808053, s1P 663838620464, s1P 405867538427, s1P 245901329413, s1P 147709706724,
   s1P 87948759727, s1P 51863896959, s1P 30254582447, s1P 17434867562, s1P 9912479341,
   s1P 5553986436, s1P 3064319543, s1P 1664010804, s1P 889182995, s1P 467604479, s1N 242080724,
   s1P 123441642, s1P 62040165, s1P 30755076, s1P 15048722, s1P 7271852, s1P 3470774,
   s1P 1635772, s1P 760723, s1P 348750, s1P 157449, s1P 69948, s1P 30567, s1P 13139, s1P 5556,
   s1P 2306, s1P 936, s1P 367, s1P 137, s1P 46, s1P 13, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0]
private def s1V3S5 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V3S6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V3S7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V3S8 : List ℤ :=
  [s1P 0]
private def s1V3 : List ℤ :=
  s1V3S0 ++
    (s1V3S1 ++
    (s1V3S2 ++
    (s1V3S3 ++
    (s1V3S4 ++
    (s1V3S5 ++
    (s1V3S6 ++
    (s1V3S7 ++
    s1V3S8)))))))
private def s1Ch4 : List Rkm128kSeg := [
  ⟨130, 293389, 1, 25,
    rkm128kMask56 512 [4511782072930551, 8822031948166326, 20266374079166752,
      46942161330490503, 12762, 0, 262144, 62294480547479552,
      47193715502251957, 248]⟩,
  ⟨132, 290568, 1, 25,
    rkm128kMask56 513 [53801181007906114, 6252346010674697, 10597609301724817,
      20904916558020872, 464327, 1073741824, 0, 69823386410287104,
      57863740050129519, 506]⟩,
  ⟨134, 285332, 1, 25,
    rkm128kMask56 513 [65816975506604947, 32745925284390758, 20550433725611169,
      4729133233428627, 14541324, 0, 36028797018963968, 36033197213483008,
      20387776877245792, 267]⟩]
private def s1V4S0 : List ℤ :=
  [s1P 133182645, s1P 564140021, s1N 107872913, s1N 1280068348, s1P 1098292474, s1P 635486356,
   s1N 2586206, s1N 1256628526, s1N 1389370367, s1N 407216929, s1P 289202092, s1P 793738868,
   s1P 830802186, s1N 2668082711, s1N 2427535198, s1P 2265625894, s1P 1240130426,
   s1P 7240649250, s1N 1625880933, s1N 1354657803, s1P 4263519856, s1N 4345290053,
   s1P 5624270605, s1P 290228942, s1N 1979181968, s1P 7845054943, s1P 13997291266,
   s1P 14998633414, s1P 6123501550, s1P 5427488430, s1P 17190011826, s1P 10910090388,
   s1P 5432276781, s1N 8583699957, s1N 14466777118, s1P 9483745407, s1N 31039587632,
   s1N 18299769565, s1N 12035734887, s1P 2135095695, s1N 5311132261, s1N 10616933272,
   s1N 8607140094, s1P 14998507178, s1P 61113013979, s1P 30328242380, s1N 28524767801,
   s1N 35472709992, s1P 47798426069, s1P 14892550251, s1N 14436380586, s1N 63671520546,
   s1N 65172681012, s1N 51060382675, s1N 84890813353, s1N 142567695711, s1N 53724945569,
   s1N 292483000079, s1N 450424026954, s1N 319288472825, s1N 77210732298, s1N 114019735641,
   s1P 38756681000, s1N 181616337878]
private def s1V4S1 : List ℤ :=
  [s1P 91383896637, s1P 472523219054, s1P 497234514596, s1P 37842934524, s1N 142045879108,
   s1N 412904696566, s1N 664622813941, s1N 189071268816, s1P 59764784995, s1P 175291105597,
   s1P 459673817559, s1P 154750804264, s1P 297918541458, s1P 658151491060, s1P 339619700931,
   s1P 317444920646, s1N 25934952338, s1N 412359179828, s1N 294681424883, s1P 243396772565,
   s1N 146036063864, s1N 423338063777, s1P 808787239209, s1P 628174410399, s1N 439672567249,
   s1N 830361036653, s1N 421262517423, s1N 1533701566129, s1N 1655125320688, s1N 441561681679,
   s1P 1086149741311, s1P 3741294980719, s1P 2284066072172, s1N 2420591237503, s1N 248846337780,
   s1P 227254363941, s1P 718301732078, s1N 1168903038224, s1P 835994669857, s1P 1868813716106,
   s1P 843995980642, s1P 471145191699, s1N 890082777853, s1P 239089543230, s1N 1519755960903,
   s1N 790953457882, s1N 902384883334, s1P 686998431651, s1N 313505502499, s1P 148454936922,
   s1P 2430655718289, s1P 1390554599357, s1P 2475439118656, s1P 2498476001661,
   s1N 1727070432990, s1N 1381035212487, s1N 315583277880, s1P 1218333863718, s1N 373379160425,
   s1N 554007869382, s1P 1088283986768, s1N 579513440927, s1N 866553721651, s1N 621291760799]
private def s1V4S2 : List ℤ :=
  [s1N 1382688673271, s1N 2509118984165, s1N 2320230369149, s1N 1811445576373, s1N 653767861445,
   s1P 1137074023090, s1P 664224790344, s1P 995640915224, s1P 2169413335628, s1P 1976191987462,
   s1N 326070706055, s1N 1040697034538, s1N 211330114918, s1N 67601420045, s1P 107512988668,
   s1N 1679122905505, s1N 1575783840476, s1P 773658503886, s1P 6808294265862, s1P 4364741326511,
   s1N 1166055274465, s1N 5353869642036, s1N 7117860849092, s1P 1282489021936,
   s1P 2730484452938, s1P 1501672915281, s1P 3498723190342, s1N 672524778768, s1N 1631521550702,
   s1P 718260260313, s1N 1669711293046, s1N 655288899101, s1P 1037148570573, s1P 1949308876524,
   s1P 1992877643002, s1P 1641218833866, s1N 2322678829599, s1P 773587865089, s1P 501040511669,
   s1N 2336848761520, s1N 633486681613, s1P 2265147506353, s1N 1111998066511, s1N 3279377975921,
   s1N 2423242641126, s1N 6282249825358, s1N 10112866371869, s1N 3908951298518,
   s1P 3931830848137, s1P 9331961343319, s1P 4532520687513, s1N 4227142203427, s1N 927429742554,
   s1N 238738227723, s1P 991817245660, s1N 4694358099882, s1N 942528791021, s1N 3116210939736,
   s1N 1326893304959, s1N 1973624592396, s1P 2076063303572, s1P 8301545914534,
   s1P 7645036394473, s1P 673630423628]
private def s1V4S3 : List ℤ :=
  [s1N 2982143240205, s1N 1689687329992, s1P 3228399684921, s1P 1672516426922,
   s1P 4395805009577, s1N 4572425152253, s1N 28790121290, s1N 6666674946995, s1P 1834412982033,
   s1P 2969289189839, s1N 868909482229, s1P 49652217999, s1N 39139356039, s1P 1072028466306,
   s1N 1688687868654, s1N 1681308914175, s1N 904920699452, s1P 231888278984, s1N 1872790845130,
   s1P 3930214452148, s1N 2256079156478, s1N 3106041293076, s1P 3827779536418, s1N 29119003399,
   s1P 4421532086133, s1N 474760742185, s1P 1954826791272, s1N 2041057451995, s1P 761833139339,
   s1N 1929098443227, s1N 4957982112813, s1P 3048739802277, s1N 2126333275648,
   s1N 7713426842809, s1P 7639709933085, s1N 2086099367205, s1P 5879553567193,
   s1P 3629165976847, s1P 4541089612862, s1P 1723489063210, s1N 3186527286244, s1P 280180851553,
   s1N 1407282455205, s1P 1679961875912, s1N 2762805843248, s1N 6462976860739,
   s1N 3474823734583, s1P 4798001773402, s1N 1103893481312, s1P 3249228166868,
   s1N 1887762879840, s1N 4493254661561, s1N 5637691134987, s1P 648567774438, s1P 5384673815583,
   s1P 3566752525740, s1P 11954260523046, s1P 42268093763487, s1P 84825392122908,
   s1P 134952636132230, s1P 187110778725809, s1P 235926551802828, s1P 276971670309895,
   s1P 307202111839865]
private def s1V4S4 : List ℤ :=
  [s1P 325054934173887, s1P 330308342193508, s1P 323837003778770, s1P 307343476338840,
   s1P 283083762759473, s1P 253580796361540, s1P 221336499443707, s1P 188578047767180,
   s1P 157082359045278, s1P 128100013511609, s1P 102376234755044, s1P 80231181791346,
   s1P 61672180910558, s1P 46494656570237, s1P 34370043311973, s1P 24905837517719,
   s1P 17687936367984, s1P 12311952558484, s1P 8401970784021, s1P 5624347980086,
   s1P 3696507042677, s1P 2388092182990, s1P 1518281026959, s1P 951093117286, s1P 587929917495,
   s1P 359126200957, s1P 216846452122, s1P 129404440317, s1P 76374099752, s1P 44670100377,
   s1P 25918582352, s1P 14872863681, s1P 8376044963, s1P 4587793671, s1P 2429360927,
   s1P 1244127786, s1P 621013360, s1P 306315130, s1P 151621068, s1P 76135174, s1P 38849664,
   s1P 20007229, s1P 10288530, s1P 5232095, s1P 2614271, s1P 1279405, s1P 612792, s1P 287429,
   s1P 132173, s1P 59668, s1P 26461, s1P 11533, s1P 4933, s1P 2067, s1P 844, s1P 328, s1P 120,
   s1P 37, s1P 10, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V4S5 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V4S6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V4S7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V4S8 : List ℤ :=
  [s1P 0]
private def s1V4 : List ℤ :=
  s1V4S0 ++
    (s1V4S1 ++
    (s1V4S2 ++
    (s1V4S3 ++
    (s1V4S4 ++
    (s1V4S5 ++
    (s1V4S6 ++
    (s1V4S7 ++
    s1V4S8)))))))
private def s1Ch5 : List Rkm128kSeg := [
  ⟨137, 283397, 1, 25,
    rkm128kMask56 511 [47633273224101383, 19178058019237963, 31709032628824452,
      21233837292851489, 336205721, 4503599761588224, 9007199254749184,
      8388608, 15403400570566032, 122]⟩,
  ⟨139, 277289, 1, 25,
    rkm128kMask56 511 [29540454523458625, 23753437236311690, 3008948064079707,
      13460857488796778, 16933062150, 1128098938748928, 16809984, 35651584,
      53046457310512128, 114]⟩,
  ⟨142, 269254, 1, 25,
    rkm128kMask56 513 [19497347791914338, 4551344721339419, 2788562424575587,
      69989472338560876, 216963650334, 0, 4194304, 4294967428,
      50622222355668992, 434]⟩]
private def s1V5S0 : List ℤ :=
  [s1N 62902837, s1P 166028963, s1P 125539591, s1N 574023396, s1N 1225015579, s1P 527292718,
   s1P 1630107704, s1P 952494095, s1N 397125779, s1P 603820546, s1P 996881592, s1P 819176349,
   s1P 820373263, s1N 2973137688, s1N 4900813880, s1P 5740018924, s1P 4512654459,
   s1P 3162572156, s1P 2594822328, s1P 4762450097, s1P 3752080717, s1P 1150812661,
   s1P 3299279212, s1P 192216604, s1N 1583092058, s1N 668695609, s1N 8103343114,
   s1N 10560123258, s1P 2609291351, s1P 22558986182, s1P 3715973975, s1P 3483415566,
   s1N 2271235040, s1P 8710503269, s1N 17671764176, s1N 3880856975, s1N 14178194232,
   s1N 18198272931, s1N 1789672308, s1N 29148035915, s1N 7751519106, s1N 15892322371,
   s1N 10139581433, s1P 1002092200, s1P 6249516543, s1N 15645569808, s1N 17695489408,
   s1N 11730944484, s1P 11677502203, s1N 11101682965, s1P 18942417215, s1P 107895775781,
   s1P 28446300462, s1P 31886063605, s1N 1266614081, s1N 51210796515, s1N 11457661930,
   s1N 73775375332, s1N 38663521760, s1N 124570042849, s1P 109028491439, s1P 190422210185,
   s1P 341611505046, s1P 396576113883]
private def s1V5S1 : List ℤ :=
  [s1P 387232986207, s1P 72207728511, s1N 7243071263, s1N 171055134582, s1N 165895977066,
   s1N 19191301843, s1N 562879539500, s1N 519671542871, s1N 477951103273, s1N 435821369735,
   s1N 465083886783, s1P 86226346496, s1P 164879103664, s1N 26824673816, s1N 258583113845,
   s1P 96975985197, s1N 252102521979, s1N 747437975168, s1N 435515987403, s1N 233200858918,
   s1N 699269509496, s1P 66559573520, s1P 275915739898, s1P 181802900792, s1P 103931776193,
   s1P 176921861986, s1P 727277628543, s1P 591293963890, s1N 419613975790, s1N 944521858788,
   s1N 808239564708, s1P 30098362276, s1P 499195481245, s1P 336198711033, s1N 1035186925822,
   s1N 1403346526474, s1N 406046035758, s1P 425776652452, s1N 1543028117696, s1N 3362354603617,
   s1N 3076825272104, s1N 3163537440355, s1N 887514266342, s1P 904530460929, s1P 935616525844,
   s1P 862410301818, s1P 285795444870, s1P 723533952025, s1P 266484794660, s1N 67341849059,
   s1P 48312641173, s1N 340951728037, s1N 1165758453610, s1P 1591397561448, s1P 824653031768,
   s1P 777553350288, s1P 911256902850, s1N 3001531062936, s1N 2477319528663, s1N 1811147698091,
   s1P 1851173854884, s1N 913579439837, s1P 1036182356354, s1P 327462492950]
private def s1V5S2 : List ℤ :=
  [s1N 1039403290101, s1N 350291419375, s1P 352904197520, s1N 251414999398, s1P 394117895684,
   s1P 154674927663, s1N 330040018045, s1N 387653886076, s1P 1254658740511, s1N 786623988430,
   s1N 528992644799, s1N 842114521206, s1N 47146446156, s1N 1509293607491, s1P 3581056037199,
   s1P 2614809691516, s1P 1731784523637, s1P 2896196293804, s1P 3872881437641,
   s1N 1346757592999, s1N 3497133823913, s1N 690660722142, s1P 3877107811033, s1P 308818048088,
   s1N 2403219736489, s1N 135917939291, s1P 5190095337860, s1P 1237438650151, s1P 1909070158179,
   s1N 7791786001458, s1N 4458277993034, s1N 2868846603577, s1P 3040002793812, s1N 752419322049,
   s1N 2095567094833, s1N 1641373911599, s1P 1430730849917, s1P 2953594930138,
   s1N 2387855217871, s1N 21395954404, s1N 443382446514, s1N 488219243970, s1P 1316677983401,
   s1P 1064570769084, s1N 712389609384, s1N 1119704091488, s1P 431922188556, s1N 2578452237315,
   s1N 2461385717648, s1N 485932442653, s1N 918149327700, s1P 319142644852, s1P 1151895148266,
   s1P 1134157069592, s1P 1472338436487, s1P 1807849695372, s1P 3640952550239,
   s1P 3437473384673, s1P 9489818060284, s1P 11834313610192, s1P 7689261471212,
   s1P 1597328451644, s1N 29770047991, s1N 898534558238]
private def s1V5S3 : List ℤ :=
  [s1N 238396653288, s1N 1304197168334, s1P 116507151608, s1N 473528573264, s1N 2166728167185,
   s1N 5074071376837, s1N 7113154692699, s1N 8245600912386, s1N 1041288898678,
   s1P 5147827368775, s1N 8729786767592, s1N 2307161353913, s1N 2122288799759,
   s1P 4727299376779, s1P 3873183660771, s1P 305742301052, s1P 4322684232524, s1P 484985581572,
   s1N 1229601969543, s1P 2242411684666, s1N 1799593947641, s1N 889721844115, s1P 682410533129,
   s1P 4745127678139, s1N 762379464762, s1P 2912723445749, s1N 5677026372342, s1N 635694127357,
   s1N 1000961546750, s1N 695215218740, s1N 530560473123, s1P 2541586753392, s1P 2370811993597,
   s1N 3235916573606, s1P 1797574378293, s1N 764030023565, s1N 2045852291083, s1P 8888336254355,
   s1P 3562240325774, s1P 4841268848783, s1P 6713592565315, s1N 718283799557, s1N 785958487416,
   s1P 463942612248, s1N 3620103639892, s1N 2831093399134, s1P 4054318848250, s1P 1846646421150,
   s1N 4589917140554, s1P 7281512505487, s1N 1254830830310, s1N 2168613670311,
   s1N 5647435863147, s1P 4179951302299, s1N 1423339487295, s1N 2981936497084,
   s1P 3411478796543, s1P 989380171168, s1P 356593159699, s1N 1275849186779, s1N 1570938160697,
   s1N 6497708519172, s1N 602362992030, s1P 15187976936]
private def s1V5S4 : List ℤ :=
  [s1N 6415042181915, s1P 3373104189645, s1P 5235834753631, s1P 6168062019144, s1P 795786972072,
   s1P 5197064536991, s1P 2591011741846, s1P 26254073910057, s1P 64319165217399,
   s1P 112379737615765, s1P 164854710992528, s1P 216146540757348, s1P 261386488545735,
   s1P 296881876980724, s1P 320328825177777, s1P 330840291539053, s1P 328829676188027,
   s1P 315776554797992, s1P 293902592802738, s1P 265804781570705, s1P 234105229601744,
   s1P 201169493977177, s1P 168925328042503, s1P 138787394133001, s1P 111668719171896,
   s1P 88047023637836, s1P 68055746306822, s1P 51578104882254, s1P 38331314241431,
   s1P 27935511705758, s1P 19967278016526, s1P 13999840414565, s1P 9631744133716,
   s1P 6505346419037, s1P 4315887042626, s1P 2815404793126, s1P 1805206632530,
   s1P 1144015046812, s1P 706016965671, s1P 442245661484, s1P 261719717466, s1P 155441716518,
   s1P 98380082840, s1P 57822081258, s1P 28941862401, s1P 12240290074, s1P 5425913551,
   s1P 3244113623, s1P 2066849024, s1P 1107757589, s1P 504467212, s1P 226311599, s1P 116811026,
   s1P 68642516, s1P 41080604, s1P 23370562, s1P 12372277, s1P 6089065, s1P 2814854,
   s1P 1249727, s1P 550812, s1P 248661, s1P 117126, s1P 56348]
private def s1V5S5 : List ℤ :=
  [s1P 27362, s1P 13292, s1P 6151, s1P 2570, s1P 958, s1P 333, s1P 113, s1P 39, s1P 13, s1P 2,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0]
private def s1V5S6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V5S7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V5S8 : List ℤ :=
  [s1P 0]
private def s1V5 : List ℤ :=
  s1V5S0 ++
    (s1V5S1 ++
    (s1V5S2 ++
    (s1V5S3 ++
    (s1V5S4 ++
    (s1V5S5 ++
    (s1V5S6 ++
    (s1V5S7 ++
    s1V5S8)))))))
private def s1Ch6 : List Rkm128kSeg := [
  ⟨144, 272725, 1, 25,
    rkm128kMask56 513 [58867035169798666, 71044041683435761, 59116950489214557,
      53477867506557862, 4840951894277, 0, 16777216, 4503600701112832,
      34226897411966977, 376]⟩,
  ⟨146, 273008, 1, 25,
    rkm128kMask56 511 [5239300691736710, 32665470459808165, 6495102734835532,
      13660459189721978, 213414811043032, 0, 17592186060800,
      18014398509481984, 20587221904064512, 113]⟩,
  ⟨148, 270871, 1, 25,
    rkm128kMask56 512 [808769052583106, 55427569612959612, 6845787597399360,
      11247361150690770, 6951219096546611, 0, 36028797018963968,
      281474976718848, 36534572904611840, 164]⟩]
private def s1V6S0 : List ℤ :=
  [s1N 122803266, s1N 232289398, s1N 207995458, s1P 134984390, s1P 147127123, s1P 43778026,
   s1P 924606142, s1P 1950476461, s1P 126139594, s1P 299601034, s1N 612408881, s1P 1024999587,
   s1P 1001560875, s1N 689771320, s1P 573460696, s1P 5585338662, s1P 4368477268, s1N 1797595388,
   s1P 1845065931, s1N 3823719741, s1P 548503212, s1P 1181138492, s1P 5755577170,
   s1P 4787624845, s1P 3879792879, s1N 2451781725, s1N 18958800, s1N 8546658171, s1P 3560880081,
   s1N 424108538, s1P 12555203518, s1N 9125126517, s1N 13393011034, s1N 3548605573,
   s1N 25408036162, s1N 19190148648, s1P 9615444747, s1N 8114841125, s1P 2630386879,
   s1P 12885587922, s1N 3832567155, s1N 953959723, s1N 6787647751, s1N 4438598069,
   s1P 4301851201, s1P 10069956197, s1P 32073995765, s1N 126882376, s1N 55873601396,
   s1N 23596728223, s1P 3190963230, s1N 50280301173, s1P 11918244952, s1N 2337906276,
   s1P 85550844712, s1P 9353420919, s1P 28905315688, s1P 52401872443, s1P 106108456870,
   s1N 6711227716, s1N 83316045412, s1N 46389257695, s1N 33456463259, s1P 48694206745]
private def s1V6S1 : List ℤ :=
  [s1P 66163871660, s1P 105679363040, s1P 176768990378, s1P 236830352517, s1P 293564739096,
   s1P 89026122452, s1N 182534260569, s1N 203767055242, s1N 588308738136, s1N 365493967110,
   s1N 339541742285, s1N 247024110900, s1N 214041709575, s1N 560977422430, s1N 422639963181,
   s1P 180819382976, s1N 308533520006, s1P 657706981109, s1N 241777031158, s1N 84022751562,
   s1P 280855699885, s1P 235802692565, s1P 458420173362, s1N 58058858730, s1N 158385669731,
   s1P 455030789455, s1P 170065367891, s1N 657187072858, s1N 543672344913, s1P 357968218433,
   s1N 113375168608, s1P 617712009922, s1N 1041028433763, s1N 743246555991, s1N 82851441419,
   s1P 39495389419, s1N 478731631716, s1P 436278540999, s1P 919616738119, s1N 955409640263,
   s1P 206456473951, s1N 462815017637, s1N 312604869967, s1P 1894889752274, s1N 8201868951,
   s1P 1278202573409, s1P 305629239433, s1N 1203824705377, s1N 152366485421, s1N 1449724741138,
   s1P 156121681328, s1P 3713935568166, s1P 4017426024273, s1P 1219111868531, s1N 137932114757,
   s1P 82232380223, s1P 34064906258, s1P 3315118461195, s1P 628131921635, s1N 127559945616,
   s1P 307530156529, s1N 2033911845799, s1N 706687672792, s1P 2280008323314]
private def s1V6S2 : List ℤ :=
  [s1P 872686345864, s1P 1675176558299, s1N 1894187484968, s1N 1335634498530, s1P 673559010997,
   s1N 728466072262, s1P 166965628322, s1N 341556419432, s1N 816896855487, s1N 1152209858776,
   s1N 127434781897, s1P 891279621739, s1N 910854024565, s1N 728041370522, s1N 676070260971,
   s1P 1111404155028, s1P 694329687898, s1N 1333433641983, s1P 326248700391, s1N 2341367854375,
   s1P 797046282985, s1P 1207343848881, s1P 276072313379, s1P 3205559582610, s1N 3297240560610,
   s1N 6182724235945, s1P 2742872225140, s1N 1569701346000, s1P 3420745883396,
   s1P 1790877781133, s1P 4328126049085, s1P 8486352944598, s1P 4236225002379,
   s1P 3117016683151, s1P 900370919325, s1P 96378980670, s1N 107533407833, s1P 3094179884934,
   s1P 488817900756, s1N 275902630260, s1P 2613426370633, s1N 510967407356, s1N 32850391551,
   s1N 2691755759443, s1N 113317158966, s1P 34984044908, s1P 2071598633546, s1N 1944727458170,
   s1P 817548370276, s1N 1179713279608, s1P 740129995181, s1P 1230827985529, s1N 1259474352621,
   s1N 223216815155, s1P 1612363648871, s1N 1212839091914, s1N 1206130267707, s1N 417779815575,
   s1N 50476597807, s1N 635073068039, s1P 1801452131931, s1N 826097758443, s1P 2086529411787,
   s1P 2684332388360]
private def s1V6S3 : List ℤ :=
  [s1P 1154715847106, s1P 1560612259675, s1P 560255819546, s1P 1761639262486, s1P 7699266212983,
   s1P 5369640512023, s1P 1937438894712, s1P 5244509120609, s1P 5246232550757,
   s1N 13619819202437, s1P 11340691030156, s1P 2083160572091, s1P 9251590594545,
   s1N 1121213677000, s1P 625918503691, s1N 7894653116963, s1N 1666604899370, s1P 3217484112908,
   s1N 1344509173897, s1P 4190448533221, s1P 136586488621, s1P 382833897993, s1P 773631971255,
   s1P 1267918758555, s1P 148451222857, s1N 3710309909992, s1N 846707527706, s1N 2206034768046,
   s1P 2919571767691, s1P 2685064113965, s1N 3317368632266, s1N 2102029165943,
   s1P 2780354506303, s1P 847085140946, s1N 2170643472857, s1N 1992733220225, s1P 666229818801,
   s1N 16030536322, s1N 4314130528107, s1N 7838247844972, s1N 4724584550809, s1N 4283698840781,
   s1P 3354635668219, s1P 6518922059938, s1N 183338415060, s1N 3181178408542, s1P 3334859776678,
   s1N 559759941243, s1N 3896648160838, s1P 1492869321735, s1N 3503650102622, s1N 1420382833053,
   s1P 3657606042855, s1P 5954918484602, s1P 1904215891904, s1P 1633861127375,
   s1N 11697397636962, s1N 2625312962133, s1P 705942519874, s1P 3958361874555,
   s1P 4281562372819, s1P 2426520267481, s1P 4097702228091, s1P 1735288993420]
private def s1V6S4 : List ℤ :=
  [s1P 3416968999532, s1N 4401714917935, s1P 1549952759911, s1P 3673585108904,
   s1N 1984647692232, s1P 7226552999289, s1N 1931889954681, s1N 6052257116393, s1N 176863470425,
   s1P 1184432103621, s1P 1883467973487, s1P 260660556455, s1P 5858976794053, s1N 880789032927,
   s1P 505481978448, s1P 1913746159328, s1P 3455744770048, s1P 7427501743640, s1P 2697407359654,
   s1P 4589160966038, s1P 3544036266501, s1P 12536455326264, s1P 44424850905176,
   s1P 88861284757067, s1P 140586777110596, s1P 193814730764808, s1P 243069880944984,
   s1P 283903406473012, s1P 313189627947115, s1P 329368816928675, s1P 332370472853781,
   s1P 323362982196813, s1P 304452960600185, s1P 278224406100308, s1P 247372252508393,
   s1P 214420958487588, s1P 181482207554660, s1P 150168957574186, s1P 121604498888550,
   s1P 96443603985664, s1P 74945853439814, s1P 57086436634104, s1P 42639434837276,
   s1P 31239200389588, s1P 22450485661564, s1P 15830490202453, s1P 10959698756217,
   s1P 7454623797235, s1P 4981957597471, s1P 3270569021269, s1P 2110529852993,
   s1P 1341699153479, s1P 842341336839, s1P 522450075041, s1P 319127283414, s1P 190921819958,
   s1P 111301564490, s1P 63079311615, s1P 34795509588, s1P 18752552528, s1P 9920614177,
   s1P 5172887415, s1P 2666658653, s1P 1362815361]
private def s1V6S5 : List ℤ :=
  [s1P 692934903, s1P 352188695, s1P 179767210, s1P 92374450, s1P 47713335, s1P 24641002,
   s1P 12631783, s1P 6384512, s1P 3167151, s1P 1539419, s1P 733902, s1P 344194, s1P 159395,
   s1P 73101, s1P 33239, s1P 14961, s1P 6642, s1P 2889, s1P 1224, s1P 499, s1P 192, s1P 68,
   s1P 21, s1P 4, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0]
private def s1V6S6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V6S7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V6S8 : List ℤ :=
  [s1P 0]
private def s1V6 : List ℤ :=
  s1V6S0 ++
    (s1V6S1 ++
    (s1V6S2 ++
    (s1V6S3 ++
    (s1V6S4 ++
    (s1V6S5 ++
    (s1V6S6 ++
    (s1V6S7 ++
    s1V6S8)))))))
private def s1Ch7 : List Rkm128kSeg := [
  ⟨151, 264263, 1, 25,
    rkm128kMask56 513 [24311183307916258, 19326814148659342, 47041096302598250,
      70301541370302978, 1558954108786241, 3, 562949961809920,
      70368760989696, 13371163052867584, 278]⟩,
  ⟨154, 254765, 1, 25,
    rkm128kMask56 513 [9869093742698414, 59133797972711336, 36663625638808398,
      59567378663837692, 56406975363049654, 549755813940, 2251799813685248,
      18031994995736576, 175924146356224, 489]⟩]
private def s1V7S0 : List ℤ :=
  [s1N 119046290, s1N 210730819, s1P 114531572, s1P 326445277, s1P 241266052, s1P 555972734,
   s1P 1017885652, s1P 249099241, s1P 290057659, s1P 1693402096, s1P 756253959, s1P 595607510,
   s1P 977146428, s1N 315375213, s1N 1136556223, s1N 2542899670, s1N 1082369697, s1N 6115878486,
   s1N 4864372016, s1N 1290576980, s1N 363308446, s1P 2435027462, s1P 2034322104,
   s1N 7884084377, s1N 3125660273, s1P 308710316, s1N 3747080168, s1N 2686773208,
   s1P 6776204083, s1P 6930925746, s1P 4193299204, s1N 1884817166, s1N 5867854985,
   s1N 22306455166, s1N 1479546434, s1P 6268639846, s1P 741584882, s1P 18527263254,
   s1P 24371445903, s1P 5658887331, s1N 968191923, s1N 10046229909, s1N 16084538056,
   s1P 16354956315, s1P 25435427638, s1N 39593102261, s1P 21706580203, s1P 4305798625,
   s1P 1983261485, s1P 27510824373, s1P 62023843425, s1P 3919286891, s1P 67350241697,
   s1P 51608054702, s1P 14331587970, s1N 64910749378, s1P 16814226228, s1N 15750613604,
   s1N 10394122016, s1N 42821412571, s1N 39602866031, s1P 22086848955, s1N 583054588,
   s1N 18535158116]
private def s1V7S1 : List ℤ :=
  [s1N 74463167643, s1N 110833823170, s1N 27872875379, s1N 115070802833, s1N 298276981540,
   s1N 279020407210, s1N 186039591778, s1P 28400358589, s1P 275271144345, s1P 520594590125,
   s1P 536685254165, s1P 166179949218, s1N 363880703181, s1N 283715631371, s1P 194885875578,
   s1P 558047657934, s1P 272291431683, s1N 181754562289, s1N 160810855243, s1N 580191222517,
   s1N 598697187187, s1P 100525466700, s1P 145520015591, s1P 434491121798, s1N 582753390715,
   s1N 144535351227, s1P 640080683343, s1P 169013480025, s1N 728896532518, s1P 184678924927,
   s1N 137837164658, s1N 170395929094, s1P 741041915513, s1P 402826360183, s1P 254399300251,
   s1P 676076655005, s1P 144592010212, s1P 858868754926, s1P 650455328013, s1P 1025522399408,
   s1P 1431796095953, s1P 983564909288, s1N 796384366699, s1N 237811925780, s1P 348641514657,
   s1N 898213513024, s1N 331108917752, s1P 604812874647, s1N 2144504373004, s1N 1742516227316,
   s1P 677525348015, s1P 491200602227, s1P 2328959398691, s1P 199322252357, s1N 450947700314,
   s1N 451237533944, s1P 1706092575788, s1P 1827885900276, s1N 164805538193, s1N 3194308414415,
   s1P 3189549636498, s1P 2910861851731, s1N 1915526290836, s1P 239551993769]
private def s1V7S2 : List ℤ :=
  [s1N 283307374180, s1P 1477717701331, s1P 1272308948644, s1P 543645975804, s1P 726028230710,
   s1N 2571534486432, s1N 1768598380646, s1P 146980447267, s1N 306716955252, s1N 687605618628,
   s1P 136114870967, s1P 227400847886, s1N 1184918549561, s1P 796003957876, s1N 1687879025996,
   s1N 751141788153, s1N 432546817426, s1N 1530735070534, s1N 2036430754621, s1N 1300105389721,
   s1N 464057621026, s1N 1704370929151, s1N 1057571791767, s1N 2367006071570, s1N 1996920629401,
   s1P 58176846828, s1P 5363895608697, s1P 5534786884546, s1P 2255019846491, s1N 1519813633709,
   s1P 1626221803558, s1P 516577348357, s1P 2180943039474, s1P 7630788135140, s1P 4154853756305,
   s1P 1796144145517, s1N 2269132911908, s1N 4943246532945, s1P 1193211360087,
   s1N 2097951865672, s1P 3867123099642, s1P 1872776125135, s1N 94680572189, s1N 2171507730383,
   s1N 1420408129095, s1P 541191236480, s1N 1684482452218, s1N 342629209890, s1N 3074469150383,
   s1N 1596183007911, s1N 163896878029, s1P 2236648858129, s1P 928370124524, s1N 343014753792,
   s1N 946362117434, s1N 523458798349, s1N 605323374383, s1P 650573011873, s1P 149578519565,
   s1N 460087312638, s1N 755749041914, s1N 224060730786, s1N 2091910877810, s1N 2152391531718]
private def s1V7S3 : List ℤ :=
  [s1P 157216389405, s1N 1879460828287, s1N 541177401369, s1P 77517254009, s1N 3095402359391,
   s1N 1141338012005, s1N 2714119898572, s1N 3310794215769, s1N 8667324431962,
   s1N 12625075829494, s1N 12682438132820, s1N 7196007814903, s1N 7611140801797,
   s1N 3106804193291, s1P 6167631033564, s1P 6295685165398, s1P 2830748970858, s1N 139986960781,
   s1N 1409419277419, s1P 1309671248879, s1P 530071388283, s1N 704983174841, s1N 483659990491,
   s1P 1238956005643, s1P 2657902370388, s1P 1910037534255, s1N 3586567207340,
   s1N 3645966504711, s1N 1560355578538, s1P 2681841109433, s1P 2025440511606,
   s1P 4305301292037, s1P 2387208367473, s1N 196234450689, s1N 3643197924138, s1P 1182216664591,
   s1P 1552081329418, s1P 3376776388569, s1P 2323303286432, s1P 6314499368012,
   s1P 7206819578446, s1N 3725642795915, s1N 1480569550212, s1N 6426155173821, s1P 960218845900,
   s1P 2210346356969, s1P 6304482273691, s1P 5418369178816, s1P 103610297818, s1N 1652792670441,
   s1N 2066169018630, s1N 3007338638231, s1P 3014004462515, s1P 5486879051098,
   s1N 1342152004609, s1N 3197407714034, s1P 147024030194, s1P 2506473968224, s1P 999642731512,
   s1P 915490161014, s1N 4634962977846, s1N 13260597508895, s1N 3452131777134,
   s1P 3037498494271]
private def s1V7S4 : List ℤ :=
  [s1N 1509635358443, s1N 2769737257410, s1N 1885638594010, s1N 1274990295035, s1P 86514989136,
   s1P 6547463867017, s1P 2112252336765, s1P 3629665951719, s1P 2273261720452,
   s1P 2035450181876, s1P 678224703698, s1N 4599807210415, s1N 1900301452226, s1P 866290588383,
   s1P 3529647579929, s1N 1022000217477, s1N 436693614673, s1N 749373479004, s1N 625278589828,
   s1P 5640902053680, s1P 2071249413320, s1N 5322439703513, s1P 3056392101828,
   s1N 1247604654166, s1P 1261368816582, s1P 4905456732269, s1N 8508327663417,
   s1P 4699088996393, s1P 3560970334477, s1P 6427579531067, s1P 4133560834577,
   s1P 30768680416467, s1P 71532881865755, s1P 121780007871810, s1P 175706147946260,
   s1P 227483869012273, s1P 272086045469911, s1P 305804109589651, s1P 326508960879210,
   s1P 333680244235574, s1P 328198481063563, s1P 311973396582833, s1P 287528498549251,
   s1P 257608176507961, s1P 224838952879938, s1P 191488874172079, s1P 159347492340184,
   s1P 129698119554218, s1P 103342165565938, s1P 80659387193167, s1P 61696569656267,
   s1P 46264926932310, s1P 34024765782635, s1P 24551456395183, s1P 17388482972005,
   s1P 12090827680983, s1P 8255621079796, s1P 5537516909112, s1P 3651620828386,
   s1P 2369839576025, s1P 1515031747928, s1P 954388220908, s1P 592033231934, s1N 361101452959]
private def s1V7S5 : List ℤ :=
  [s1P 216146448252, s1P 126754239931, s1P 72747830326, s1P 40855200605, s1P 22466706160,
   s1P 12114162506, s1P 6417086688, s1P 3347260085, s1P 1723990536, s1P 879436906,
   s1P 445745405, s1P 225137965, s1P 113550696, s1P 57228875, s1P 28796744, s1P 14434790,
   s1P 7186798, s1P 3543515, s1P 1726150, s1P 829520, s1P 393043, s1P 183647, s1P 84655,
   s1P 38512, s1P 17290, s1P 7649, s1P 3324, s1P 1412, s1P 584, s1P 229, s1P 82, s1P 26, s1P 6,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V7S6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V7S7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V7S8 : List ℤ :=
  [s1P 0]
private def s1V7 : List ℤ :=
  s1V7S0 ++
    (s1V7S1 ++
    (s1V7S2 ++
    (s1V7S3 ++
    (s1V7S4 ++
    (s1V7S5 ++
    (s1V7S6 ++
    (s1V7S7 ++
    s1V7S8)))))))
private def s1Ch8 : List Rkm128kSeg := [
  ⟨157, 489525, 2, 25,
    rkm128kMask56 513 [26567900355157449, 22288276031390543, 36079054065353550,
      18929467829868303, 41666028719671774, 281474976727616, 9345848836096,
      1127001565954048, 18023212319244288, 362]⟩]
private def s1V8S0 : List ℤ :=
  [s1N 2780088, s1N 168815122, s1N 238328636, s1P 27974820, s1P 304091577, s1N 7764642,
   s1P 158936975, s1N 1166680654, s1N 638565082, s1N 304278241, s1N 931177473, s1N 348106098,
   s1N 1725351653, s1N 579793468, s1N 2003810268, s1N 1754232322, s1N 1212310605, s1N 449327167,
   s1P 2158197744, s1P 3679656846, s1P 1523135822, s1N 3215230551, s1N 7810574232,
   s1N 4615764250, s1N 5055938189, s1N 307417507, s1P 1097933299, s1N 4707633396,
   s1N 4729504899, s1N 7375919826, s1P 6166386945, s1P 2922559282, s1P 6610232501,
   s1N 760436241, s1N 18004142907, s1N 6408851438, s1P 6173136614, s1N 5138928447,
   s1N 728435981, s1N 33873717393, s1N 20937070706, s1P 20629983152, s1P 4741434115,
   s1P 35000118073, s1P 35653436388, s1P 38632541138, s1N 24139753345, s1N 10106076197,
   s1P 2438170529, s1P 12321551887, s1N 41995018203, s1P 32036209990, s1P 19092219394,
   s1P 33462369123, s1P 834268007, s1P 2100906183, s1N 3402411950, s1N 48743610482,
   s1N 90655683665, s1N 25081925222, s1P 12283500055, s1P 21418212006, s1P 24427047255,
   s1P 43954167325]
private def s1V8S1 : List ℤ :=
  [s1P 14640829595, s1P 82512171697, s1N 39279709524, s1P 56317386390, s1P 6778870260,
   s1N 26544918826, s1P 94316600388, s1N 9424102101, s1N 44574177044, s1N 92706960997,
   s1N 65599083311, s1N 206603848887, s1N 285826772972, s1N 328113031572, s1N 601959114142,
   s1N 573216731771, s1N 530987901848, s1N 522285778229, s1N 31637295327, s1N 181496463754,
   s1N 113723353758, s1N 230791454304, s1N 141221882105, s1N 655638787158, s1N 843862941947,
   s1N 757842261513, s1N 777875386894, s1P 299745563093, s1P 431650256447, s1P 70184294545,
   s1N 231672653804, s1N 156733762893, s1N 40362166361, s1N 293430222218, s1N 10095619533,
   s1N 191069894647, s1N 250997420583, s1P 585443121792, s1P 215415914017, s1P 388468255257,
   s1P 687846588827, s1N 697194088921, s1N 1600473380054, s1P 1450279315633, s1P 896003492968,
   s1P 556489395686, s1N 610137407190, s1P 977976228796, s1P 1923806082724, s1N 434306659824,
   s1N 692753060511, s1P 1184361046688, s1P 601923514450, s1P 916256770305, s1P 968372294097,
   s1P 1529069002801, s1P 3446155703304, s1P 3176050212246, s1P 2501299179372,
   s1P 1367728383912, s1N 714001672842, s1N 1576380021862, s1N 1417592600932, s1N 2627347539221]
private def s1V8S2 : List ℤ :=
  [s1P 298547025238, s1N 533474917348, s1N 81210809692, s1P 921031839168, s1P 93259847152,
   s1N 2640273506860, s1P 293615494818, s1N 1291387311883, s1N 485205220083, s1P 778710860096,
   s1P 1798331526833, s1P 1313632231408, s1P 417044615369, s1P 1345676750847, s1N 24885522866,
   s1N 1123833461467, s1P 1047388812839, s1N 816167395398, s1N 735648941292, s1N 866322657788,
   s1N 13953509127, s1P 554541574478, s1P 182819071516, s1P 430515060401, s1P 1422103751532,
   s1P 1102253351435, s1P 3237088014390, s1P 3540554575145, s1P 3214302468442,
   s1P 1821834565293, s1N 127321516063, s1N 5724854148294, s1N 2884936493925, s1N 646532736769,
   s1P 273416218042, s1P 4765131859934, s1P 4166498007280, s1P 2194282114667, s1N 2566728510166,
   s1N 435151515981, s1N 1592496577384, s1N 4469386949886, s1N 6275255237277, s1N 5253007323473,
   s1P 718535037605, s1N 1987991116764, s1N 2303356253394, s1N 348912743167, s1N 1042717149569,
   s1N 2172560888304, s1N 288875943694, s1N 990480600606, s1P 322749765733, s1P 850184261149,
   s1N 253474308652, s1N 2059158044266, s1P 1711641798825, s1N 2879849930076, s1N 1809434909658,
   s1N 2342475900003, s1N 948878677120, s1P 854532549962, s1P 58281350749, s1P 439745439810]
private def s1V8S3 : List ℤ :=
  [s1P 864517497125, s1P 457437486648, s1P 559771366464, s1N 628176086565, s1P 139693755741,
   s1P 716926606961, s1P 355934074931, s1N 3110217088201, s1N 2244069666981, s1P 2405676861236,
   s1N 1611188038611, s1N 3586342096778, s1N 1037621892702, s1P 1353815004776, s1N 293862590876,
   s1N 1717629086020, s1N 3807740543203, s1N 4278892636766, s1N 10911724366366,
   s1N 13816901629347, s1N 13878158016344, s1N 6717178265064, s1P 1706450097758,
   s1P 2926894514640, s1N 707921481408, s1N 1718494031387, s1P 1894321634707, s1P 3815903302278,
   s1N 1621941923325, s1N 2618100198631, s1N 1049170856135, s1P 490096817283, s1P 4983795921774,
   s1P 1610889453060, s1N 3478876415487, s1P 4586959238870, s1P 4723639028265, s1N 88874271570,
   s1N 3013983092658, s1N 3046941926690, s1N 890670156070, s1P 1697324258327, s1P 2040144808952,
   s1P 2132928697031, s1N 2109625778035, s1P 786435733221, s1P 1774610832850, s1N 7516682492034,
   s1N 7819407572544, s1P 1719677208492, s1N 1761620530704, s1P 2781454670425,
   s1N 2995249028654, s1N 2870287118441, s1P 7080571562364, s1P 7737504615014, s1P 784505415198,
   s1P 333260867435, s1N 1587710592231, s1P 1729071671525, s1P 2131323466602, s1P 6793705244516,
   s1P 4434947594601, s1N 4538224280497]
private def s1V8S4 : List ℤ :=
  [s1P 2144860707194, s1P 4334100685682, s1P 5192970251149, s1P 1904307721216,
   s1N 4633907715329, s1N 6906900878249, s1N 3088876952013, s1N 1477446445055,
   s1P 1639091983775, s1P 4010489075075, s1P 4672449187435, s1P 174069733142, s1P 927997228081,
   s1N 3161502164881, s1P 5672816261026, s1P 3832314106653, s1P 2474609038912,
   s1P 8970235403482, s1P 8250635540054, s1P 1733614973301, s1P 1325933158718,
   s1P 2130015497495, s1P 584199459868, s1P 868685069958, s1N 3733434036470, s1P 1115783715451,
   s1P 5969168346668, s1N 265744988740, s1N 3965806389505, s1P 1933329668590, s1N 4852364965757,
   s1N 422860507791, s1N 4355872057499, s1P 726055522090, s1P 5070768551716, s1P 5001135714021,
   s1N 2069369375059, s1N 9899210458188, s1P 10012372532581, s1P 3634410049029,
   s1P 32846994942216, s1P 75577978332000, s1P 127193569490183, s1P 181845299929311,
   s1P 233654132272242, s1P 277600408908180, s1P 310083823320178, s1P 329169317530911,
   s1P 334561981502355, s1P 327347705593043, s1P 309619804903206, s1P 283968093634321,
   s1P 253268521025780, s1P 219908973915835, s1P 186597973165331, s1P 154220703793441,
   s1P 125322596809160, s1P 98968543210674, s1P 77025100776077, s1P 58753629307520,
   s1P 43532894181396, s1P 31956911960062, s1P 23167505409807, s1P 16171324686892]
private def s1V8S5 : List ℤ :=
  [s1P 11005019549182, s1P 7590636850070, s1P 5275065894752, s1P 3496236262224,
   s1P 2115792039395, s1P 1169733269403, s1P 619357677333, s1P 339232406941, s1N 202635000338,
   s1P 129676500010, s1P 84113435454, s1P 53091612820, s1P 32110025083, s1P 18603799920,
   s1P 10384907656, s1P 5624510482, s1P 2974571859, s1P 1544278502, s1P 790408200,
   s1P 400227025, s1P 201039577, s1P 100379695, s1P 49878094, s1P 24671978, s1P 12142450,
   s1P 5939187, s1P 2882898, s1P 1386613, s1P 659975, s1P 310522, s1P 144319, s1P 66218,
   s1P 29979, s1P 13382, s1P 5879, s1P 2536, s1P 1066, s1P 433, s1P 165, s1P 55, s1P 17, s1P 4,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V8S6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V8S7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V8S8 : List ℤ :=
  [s1P 0]
private def s1V8 : List ℤ :=
  s1V8S0 ++
    (s1V8S1 ++
    (s1V8S2 ++
    (s1V8S3 ++
    (s1V8S4 ++
    (s1V8S5 ++
    (s1V8S6 ++
    (s1V8S7 ++
    s1V8S8)))))))
private def s1Ch9 : List Rkm128kSeg := [
  ⟨161, 484880, 2, 25,
    rkm128kMask56 509 [63387217656914707, 43250664075154525, 71158175626745849,
      37133112526892443, 43446889478712959, 15084066, 549755879426,
      70368744177664, 22520267087546369, 24]⟩]
private def s1V9S0 : List ℤ :=
  [s1N 37211440, s1N 4953624, s1N 62510517, s1N 465925384, s1N 223588941, s1N 313653936,
   s1P 159596525, s1P 878086843, s1P 636270633, s1N 159983131, s1N 1192394480, s1N 237730807,
   s1N 271775845, s1P 915104697, s1N 469930554, s1P 580147470, s1P 1341719229, s1N 510553683,
   s1P 2331018458, s1P 752867374, s1P 3605836054, s1P 1445356222, s1P 4656992057,
   s1N 1204922372, s1N 5554126317, s1P 3492285883, s1P 1499511967, s1P 7695904894,
   s1N 8061590473, s1N 2309186306, s1N 248590589, s1P 6382149774, s1P 5890898336,
   s1P 16068596109, s1P 7516629630, s1P 12483981635, s1P 7148243014, s1P 24087081851,
   s1P 12942777285, s1N 11778970986, s1N 15250574454, s1N 25791211490, s1N 8173250270,
   s1N 2811855101, s1P 31735754421, s1N 14194344415, s1N 45950676169, s1N 17033016138,
   s1N 30810338826, s1P 43085341199, s1P 20180091593, s1P 14754947471, s1P 8400253527,
   s1N 27824320730, s1P 18027470988, s1P 23554310066, s1P 10964121185, s1P 45820660845,
   s1P 47428404715, s1N 51750381332, s1N 8964780897, s1P 39933020877, s1N 49047880148,
   s1N 101807340628]
private def s1V9S1 : List ℤ :=
  [s1N 8143576768, s1N 56535713491, s1P 46483408704, s1N 12500160842, s1N 20655108583,
   s1P 15378851330, s1P 20116167153, s1N 111162371283, s1N 45847670975, s1P 94294070518,
   s1N 156560979202, s1P 119407418298, s1N 127008640014, s1N 6033691310, s1N 30754672479,
   s1N 27285157600, s1P 11599540194, s1P 11591655819, s1P 273037432302, s1P 164774244160,
   s1P 296322997519, s1P 504088478112, s1P 444908730165, s1P 667542928623, s1P 488380662737,
   s1P 371798811246, s1P 257900407136, s1P 322618278788, s1P 126725544452, s1N 488963885819,
   s1N 429497997941, s1N 797528996713, s1N 916840756911, s1N 744294652171, s1N 778777023075,
   s1N 875008783710, s1N 872981405909, s1N 241737063355, s1P 436414538510, s1P 554062165556,
   s1P 181471588226, s1P 212924576992, s1P 69637577774, s1P 617177079336, s1P 1431927406384,
   s1P 1316541817150, s1P 1879690857977, s1P 936613218638, s1P 651641036995, s1P 217076926791,
   s1P 392280981354, s1P 77647825787, s1P 416541296314, s1N 13830811349, s1N 1922207909551,
   s1P 148901353358, s1N 920808362167, s1P 51761515410, s1N 342249650271, s1P 772891434584,
   s1N 799709529954, s1N 1426009359285, s1N 1603580049808, s1N 545185484525]
private def s1V9S2 : List ℤ :=
  [s1P 1562969424718, s1P 4179419334678, s1P 3218096817056, s1N 2142895690777,
   s1N 1541219409460, s1P 457958299224, s1N 1231626819257, s1N 2755877419556, s1P 70661927248,
   s1N 1310067969138, s1P 517771645238, s1P 991886484285, s1N 72085808506, s1N 867984938502,
   s1P 760090262511, s1P 1369873685636, s1P 752071012809, s1P 1104448264536, s1P 1153541325275,
   s1N 1263028564209, s1N 1118064052159, s1N 123655985298, s1N 1760337929790, s1P 115420409511,
   s1N 389923456997, s1P 989252573624, s1P 2504148565961, s1N 702665246515, s1N 557095218232,
   s1N 563148748344, s1P 464840272354, s1N 1217294690084, s1N 135246929377, s1N 1867175619935,
   s1N 2530445496531, s1N 2487122580124, s1N 4590864809182, s1N 4122441413065,
   s1N 3035754711218, s1P 63543601164, s1P 5165093739105, s1P 5229159041734, s1P 1704437858716,
   s1N 1428304502225, s1N 677483058002, s1P 1898876467655, s1P 4778863345671, s1N 779954803546,
   s1N 1594797670936, s1N 3641826683093, s1P 4269970460954, s1P 2975958943270,
   s1N 4722136709220, s1P 3178445348402, s1P 1469791079128, s1P 1383695859847,
   s1P 1584508846482, s1N 2697716371203, s1N 1021257654025, s1N 685634799556, s1P 733012881200,
   s1N 931517865368, s1N 2973952117, s1N 1163568521086]
private def s1V9S3 : List ℤ :=
  [s1P 305865373269, s1P 174265465851, s1P 2789449466601, s1P 1991474721177, s1P 316399501689,
   s1P 1955266142037, s1P 2818743512371, s1P 2608904418472, s1P 977466961995, s1P 868563442078,
   s1P 1502005541826, s1N 2289697333473, s1N 2254242243889, s1N 1313101080893,
   s1P 1149523283508, s1P 491301095060, s1P 358428853977, s1N 565858482208, s1P 2574983522503,
   s1P 1144540963493, s1N 692399193974, s1P 970599072150, s1P 1494623433094, s1P 1440120341027,
   s1N 3794157742919, s1N 4283149133828, s1N 8530912906580, s1N 12407387868655,
   s1N 13475401650802, s1N 10989210139985, s1N 4243034455373, s1P 4499257614602,
   s1P 6563069898871, s1N 735316021130, s1N 4156009889538, s1N 2000895139995, s1P 3226087394020,
   s1P 1900043670543, s1N 2060539640837, s1P 889867317477, s1N 2354694906108, s1N 2770547609022,
   s1P 3540302286775, s1N 4714972530814, s1P 7662237326049, s1P 1247164955658,
   s1P 1851213248578, s1P 410933698877, s1P 1833183370962, s1P 1469541458162, s1N 3188645296703,
   s1P 290157813569, s1N 5910742846006, s1N 3874675441468, s1P 1656714379006, s1P 8503457066250,
   s1N 20422097277, s1N 113922039903, s1P 3870787269528, s1P 2441802583679, s1P 3441239605223,
   s1P 3158288615978, s1P 4416690557939, s1P 6225644553048]
private def s1V9S4 : List ℤ :=
  [s1N 4152363696581, s1P 1626128715045, s1P 1087162257542, s1P 193797247045, s1N 8326295253858,
   s1N 1860024304657, s1P 506066961442, s1P 416611873101, s1P 914313052670, s1N 7088491233928,
   s1P 4809773005377, s1N 1658428855835, s1N 1995795669030, s1N 3825433346520,
   s1P 9272570908704, s1N 845859290661, s1P 1226875166766, s1N 1149513583476, s1P 2087339125721,
   s1N 2411870916423, s1N 323774763158, s1P 2419999535081, s1N 6137635872816, s1N 5746933398144,
   s1P 7049852198609, s1N 3627224443860, s1P 5440825172661, s1P 5072100861198,
   s1P 9115261466280, s1P 2576552393774, s1P 5305975428865, s1N 6520769277917,
   s1P 4832818974387, s1N 3811199895106, s1N 5280998318544, s1N 3483031304653,
   s1P 6136163981331, s1P 3515174254312, s1N 6528194291338, s1N 2222722292687, s1N 257932762077,
   s1P 80696475031, s1N 2514388499372, s1P 4868908700452, s1P 2121533070084, s1P 6136648837958,
   s1P 12973428079567, s1P 11451100626584, s1P 5191746268835, s1P 36817727826463,
   s1P 82077225602935, s1P 135393653191950, s1P 190499463395512, s1P 242263752687649,
   s1P 284902220848878, s1P 315289759938711, s1P 332281814261275, s1P 335185313634582,
   s1P 325496594449416, s1P 305996376928469, s1P 278948500042029, s1P 247020123746552,
   s1P 213173284693714, s1P 179864172139611]
private def s1V9S5 : List ℤ :=
  [s1P 147866286247676, s1P 119061268097316, s1P 93524998648689, s1P 72411311256139,
   s1P 54913693532733, s1P 40451135387792, s1P 29336653106442, s1P 21024145135861,
   s1P 14735922406565, s1P 10163995432118, s1P 6982428838175, s1P 4694103469472,
   s1P 2963825601775, s1P 1706267243912, s1P 898401328007, s1P 452229053485, s1P 236044561418,
   s1N 136972267590, s1P 87683604199, s1P 58116080508, s1P 37834501085, s1P 23648491927,
   s1P 14136231029, s1P 8112193389, s1P 4495888109, s1P 2420732990, s1P 1272930127,
   s1P 656611241, s1P 333467705, s1P 167240702, s1P 83021694, s1P 40863821, s1N 19963613,
   s1P 9684594, s1P 4664713, s1P 2229738, s1P 1056918, s1P 496376, s1P 230765, s1P 106109,
   s1P 48214, s1P 21631, s1P 9565, s1P 4160, s1P 1773, s1P 731, s1P 290, s1P 107, s1P 35,
   s1P 10, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0]
private def s1V9S6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V9S7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V9S8 : List ℤ :=
  [s1P 0]
private def s1V9 : List ℤ :=
  s1V9S0 ++
    (s1V9S1 ++
    (s1V9S2 ++
    (s1V9S3 ++
    (s1V9S4 ++
    (s1V9S5 ++
    (s1V9S6 ++
    (s1V9S7 ++
    s1V9S8)))))))
private def s1Ch10 : List Rkm128kSeg := [
  ⟨164, 494123, 2, 25,
    rkm128kMask56 512 [36040593460547321, 18049605473847963, 716838614935031,
      5291103975764208, 38614908079704324, 4446941294, 8594129920,
      35185446093312, 5702651484439680, 212]⟩]
private def s1V10S0 : List ℤ :=
  [s1P 13919294, s1N 111289542, s1P 204674889, s1P 99526469, s1P 220115630, s1P 79767215,
   s1P 515029217, s1P 249088347, s1N 646014899, s1N 1023610864, s1N 481659060, s1N 821764752,
   s1P 143960175, s1N 2013338556, s1N 1219707626, s1P 1543190523, s1N 996957620, s1N 1100460865,
   s1N 1088969442, s1P 1179637951, s1P 3179286765, s1N 5968311315, s1N 4033905041,
   s1N 3419017034, s1N 1200130519, s1N 6960098482, s1P 3865203708, s1P 1679820621,
   s1P 9265837315, s1P 4638580270, s1P 573363804, s1N 6231059105, s1N 404404861, s1P 4171856263,
   s1P 3979117490, s1P 13424443446, s1N 6742257411, s1N 3976478792, s1P 16735656574,
   s1N 4942150, s1N 4005115619, s1N 36525375729, s1N 9260137201, s1N 36894174525,
   s1P 20097966931, s1N 12892475312, s1N 9902635635, s1N 42687498778, s1N 562765455,
   s1P 22995319177, s1P 7424369372, s1N 8358201728, s1N 12202294081, s1N 65744037092,
   s1N 13776200038, s1N 28981529870, s1N 10685740212, s1P 29705397734, s1P 91377888705,
   s1P 45650330281, s1P 34124824879, s1P 23634640627, s1P 39803111701, s1N 28951980788]
private def s1V10S1 : List ℤ :=
  [s1P 1230451629, s1N 41728074298, s1N 72000881507, s1N 202955412553, s1N 160865921574,
   s1N 2508476231, s1P 243438490, s1P 94004315549, s1N 6372799494, s1P 66347200659,
   s1P 58040042709, s1P 26977325521, s1N 18323904118, s1P 31943771155, s1N 163206606642,
   s1N 91135095206, s1N 46401548475, s1P 52610414276, s1P 11388060979, s1N 31679300015,
   s1P 35375582447, s1N 144142051226, s1N 62534344209, s1N 152823958568, s1P 39639409529,
   s1P 213920317631, s1P 62656828124, s1P 31876547072, s1P 298028756845, s1P 466026518705,
   s1P 408230527138, s1P 506949796039, s1P 464299133653, s1P 532047699056, s1P 423750360855,
   s1P 391241961684, s1P 672058943751, s1P 431086782776, s1N 187937310110, s1N 605346780894,
   s1N 382613512319, s1N 590034941455, s1N 1004826170831, s1N 1178620943926, s1N 1301445023297,
   s1P 134281523153, s1P 950217161061, s1P 1225272537796, s1P 411610812213, s1P 6899091113,
   s1P 80765368658, s1P 365690280768, s1N 203632006237, s1N 1473243728439, s1N 2034463413662,
   s1N 1038732637188, s1N 725790926161, s1P 679518447598, s1N 1333080363901, s1N 37587674831,
   s1P 889161369916, s1N 404337890963, s1N 653153152302, s1N 1198928840831]
private def s1V10S2 : List ℤ :=
  [s1N 827532083453, s1N 2445371773978, s1N 573262346931, s1P 3007432910866, s1P 678786127002,
   s1N 3070212657728, s1N 2764665598607, s1N 1099566759574, s1N 660339123405, s1N 2131063799934,
   s1N 2201336599292, s1N 870730610193, s1N 560692069729, s1N 1902566382087, s1P 1663216758454,
   s1P 1783764829923, s1P 758616126892, s1N 2058445450182, s1N 459968450088, s1N 606225837646,
   s1N 242766582677, s1P 565107748257, s1P 314300392204, s1P 377614355715, s1N 1765780682832,
   s1N 1627832265825, s1N 260533566495, s1N 1449871149138, s1P 822148031530, s1N 697181349329,
   s1N 1031147730843, s1P 2113298661452, s1N 360396008441, s1N 487850630871, s1P 872070846323,
   s1P 182609703853, s1P 1221026594327, s1N 1541191070541, s1P 1737141282594, s1N 917361032577,
   s1P 143243221767, s1N 649597124373, s1N 1581571838347, s1P 2933045455379, s1P 4503718194648,
   s1P 4065214931890, s1P 6353583681805, s1P 7977303001232, s1P 4401279962470,
   s1P 4590579717237, s1N 90583196627, s1N 1680053334967, s1N 2527926023611, s1N 3010612933450,
   s1N 2934263153516, s1P 510385617042, s1P 213254403717, s1P 783862871059, s1P 1037828401051,
   s1P 82420621103, s1P 1781876838516, s1N 404838844169, s1N 1949327910641, s1N 1439505412155]
private def s1V10S3 : List ℤ :=
  [s1P 2050058874693, s1P 177748942660, s1P 57665213678, s1N 1816162149957, s1P 649479908957,
   s1N 682119931304, s1N 833302417654, s1N 2583648214968, s1N 269336558905, s1N 161619406398,
   s1N 157365700878, s1N 804995465189, s1N 436411745915, s1N 2942798260560, s1P 301383658619,
   s1P 1510612895345, s1P 2567805605458, s1P 4452808204861, s1N 1983838946220,
   s1P 1326580102424, s1N 31779215661, s1P 224337432991, s1P 1634820356871, s1P 1847182267209,
   s1P 884125442883, s1N 187961449577, s1P 809980271692, s1P 581147166776, s1P 721339185478,
   s1P 1501105265334, s1P 1615668950477, s1P 913566530485, s1P 2678789581516, s1N 2295706680293,
   s1N 8081589281947, s1N 9827375877556, s1N 13811300286487, s1N 15635638974974,
   s1N 11856106432757, s1N 1580396407717, s1P 1426908078912, s1N 262359090043,
   s1N 3511351188885, s1N 2076251801364, s1N 1476261100539, s1N 8850646595, s1P 1503787649633,
   s1P 2574159357589, s1N 2657066297794, s1N 2528313010404, s1P 706185775012, s1N 3135730840476,
   s1P 34298467723, s1N 6267860063027, s1N 1848930413551, s1P 1574941384572, s1N 376301933503,
   s1N 8021075860720, s1N 1348352966628, s1N 3720682684120, s1N 4896514900920,
   s1P 1079060410619, s1P 383666570810, s1P 4691884292405]
private def s1V10S4 : List ℤ :=
  [s1N 8003843393823, s1N 1012613089198, s1N 2311992215074, s1P 2364044499181,
   s1P 6275889226200, s1P 3615429227503, s1P 6129326608818, s1N 3077283060575,
   s1P 6562782295977, s1P 7147554653351, s1N 738599325588, s1N 3645305950044, s1N 177655500918,
   s1P 350628041208, s1N 3837895744205, s1N 5490389493327, s1N 7746600883737, s1N 6523689291899,
   s1P 1228968558418, s1P 1605887106122, s1N 2450296022174, s1N 4579352840850,
   s1P 8855455951644, s1P 2947688078292, s1P 2141303762379, s1P 645636598091, s1N 1498555114021,
   s1N 2975228850649, s1N 1095295237875, s1P 1587575857030, s1P 1739554977324, s1P 803264451149,
   s1N 7535212131674, s1N 2492082959624, s1P 4623613026023, s1P 7334624596769, s1P 338167752324,
   s1N 5936978269904, s1N 9830273977383, s1N 4131090657441, s1N 6012897957819, s1N 428229899658,
   s1P 3143429520159, s1P 2109934307829, s1P 4986339566153, s1N 482581153368, s1N 5703884747191,
   s1P 595671550782, s1N 3482400027332, s1N 4094362378071, s1N 8231204918907, s1P 621231918054,
   s1P 9595830373453, s1P 11437757737100, s1P 3353205357213, s1N 6589983935742,
   s1P 8350971958500, s1P 6046481183440, s1P 36971105847360, s1P 82072534989533,
   s1P 135987320641238, s1P 192064695482247, s1P 244187811508269, s1P 286941076669340]
private def s1V10S5 : List ℤ :=
  [s1P 317345432224212, s1P 333955065219588, s1P 336196610843563, s1P 325697044288925,
   s1P 305380220117594, s1P 277753189987042, s1P 245360197970267, s1P 210976692031032,
   s1P 177200517909231, s1P 145241290199462, s1P 116624712830841, s1P 91374707071962,
   s1P 70274036757479, s1P 52907347060774, s1P 38844324532553, s1P 28126374686630,
   s1P 20150152935772, s1P 14132538436971, s1P 9691671002087, s1P 6534911461040,
   s1P 4280760469302, s1P 2642518372186, s1P 1498279541162, s1P 778996775129, s1P 383942914222,
   s1P 192754764545, s1N 106622963928, s1P 66131707467, s1P 43547490432, s1P 28647815095,
   s1P 18267217036, s1P 11175504153, s1P 6547102623, s1P 3696843542, s1P 2035029959,
   s1P 1096153092, s1P 571275452, s1P 283151012, s1N 132449562, s1P 59176922, s1P 26101670,
   s1P 11852568, s1P 5679653, s1P 2846246, s1P 1449018, s1P 730366, s1P 359608, s1P 172347,
   s1P 80520, s1N 36785, s1P 16472, s1P 7241, s1P 3120, s1P 1311, s1P 535, s1P 206, s1P 73,
   s1P 21, s1P 5, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V10S6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V10S7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V10S8 : List ℤ :=
  [s1P 0]
private def s1V10 : List ℤ :=
  s1V10S0 ++
    (s1V10S1 ++
    (s1V10S2 ++
    (s1V10S3 ++
    (s1V10S4 ++
    (s1V10S5 ++
    (s1V10S6 ++
    (s1V10S7 ++
    s1V10S8)))))))
private def s1Ch11 : List Rkm128kSeg := [
  ⟨168, 485101, 2, 25,
    rkm128kMask56 508 [55065421253175627, 36567818340086129, 28926760123321506,
      14487287270206769, 21415739519076270, 3534654411795, 35185445830656,
      274945146880, 1425516842197064, 13]⟩]
private def s1V11S0 : List ℤ :=
  [s1N 103276599, s1P 172049412, s1P 45844650, s1P 64630993, s1P 219592888, s1P 135101959,
   s1P 8346342, s1N 138821816, s1N 1052355974, s1N 69371084, s1P 329372987, s1N 7421093,
   s1N 2207490020, s1N 480405489, s1N 473212413, s1P 2008505626, s1N 39530258, s1P 3541596177,
   s1P 2846775144, s1N 577586942, s1P 305557176, s1P 6305788575, s1P 5531901755, s1P 290379193,
   s1N 449514640, s1N 2252240660, s1N 1399058069, s1P 2723914923, s1P 5151371681, s1P 784473165,
   s1P 10192169360, s1P 383839506, s1N 10464781432, s1N 5121859853, s1N 20287044829,
   s1N 10327199718, s1N 7933531958, s1P 25275684719, s1P 28145386365, s1P 5980618901,
   s1N 8090801109, s1N 7197747165, s1P 3463641969, s1P 6458682553, s1P 13369580383,
   s1N 6969556777, s1P 7410571828, s1P 58778692328, s1P 4932162700, s1P 3897319694,
   s1N 369759668, s1N 15033758129, s1N 9391649492, s1N 51614419694, s1N 1274139797,
   s1N 8838671732, s1N 28051041031, s1N 31090895562, s1P 22908122960, s1N 12709090741,
   s1P 48191067882, s1P 49847975738, s1P 63256417493, s1P 62703198894]
private def s1V11S1 : List ℤ :=
  [s1P 38453548108, s1P 62754304446, s1P 66788594303, s1P 60219875589, s1P 9131302036,
   s1N 35422588458, s1P 1785248035, s1P 132907001830, s1P 35691459435, s1P 131262308215,
   s1P 116493228348, s1P 156105714588, s1P 63408107983, s1N 108666617205, s1N 89631399794,
   s1N 24108670445, s1N 11102159067, s1N 92248251967, s1N 64330721328, s1N 89610676223,
   s1N 1509763444, s1P 100880946078, s1N 87293435428, s1N 25516520462, s1N 156782582438,
   s1N 38237503319, s1N 162708769920, s1N 25745327462, s1P 63855144555, s1P 218617026799,
   s1N 48262779267, s1P 32644242206, s1N 25211086999, s1P 84709335918, s1N 17053608687,
   s1N 324776642718, s1N 189580394955, s1N 379632512800, s1N 484911427067, s1N 532428404886,
   s1N 284194227454, s1P 257221039449, s1P 446525936073, s1P 865268968828, s1P 741495175515,
   s1P 452082559943, s1N 333286355550, s1N 566401216309, s1N 285133575066, s1N 485660670139,
   s1N 1328461802160, s1N 1975003579811, s1N 847014604713, s1P 1008482346138, s1P 943842079262,
   s1N 378771318830, s1N 263623298241, s1P 247281985577, s1N 1270443739632, s1N 1513046124810,
   s1N 756828096875, s1N 1256093117166, s1N 148157969112, s1N 1582752429424]
private def s1V11S2 : List ℤ :=
  [s1P 1944157765786, s1P 186726274718, s1N 219198820988, s1N 1974512472997, s1N 150939843652,
   s1N 921737369265, s1P 2434899260085, s1P 2101660570610, s1P 3374297040758, s1N 1422427945067,
   s1N 1224419032030, s1N 326179782826, s1N 732018541037, s1N 753757481374, s1N 992833153356,
   s1N 2202823263082, s1N 1223940032399, s1N 1129655871507, s1P 428398658344, s1P 3400113653395,
   s1P 2678375725098, s1P 428596674631, s1N 1381681252115, s1N 1449554687405, s1P 1239576224016,
   s1N 928211601382, s1N 1187898046523, s1N 2501518413105, s1N 120637282288, s1N 376910877578,
   s1N 1829788520390, s1P 203308198025, s1N 1471482246526, s1N 789267009074, s1P 1309741560793,
   s1N 1296362694966, s1N 755967738676, s1P 785778650408, s1P 628218638091, s1P 1404909263903,
   s1P 2239070795577, s1P 829264074142, s1P 1413430810528, s1N 517248436838, s1P 683420412204,
   s1N 1148803650187, s1P 464589956655, s1P 1210381344368, s1P 48122930521, s1N 1847361136611,
   s1N 117977606482, s1P 1432306358391, s1N 149505765289, s1N 1061402476831, s1N 3935962663042,
   s1N 4870849682588, s1N 7832690638196, s1N 5649832083856, s1N 6717843431780,
   s1N 3563375351926, s1N 693658447482, s1P 2868894389671, s1P 1349943653436, s1N 1555701883856]
private def s1V11S3 : List ℤ :=
  [s1P 1725806246964, s1P 2331203029046, s1P 572165133067, s1N 1717980489896, s1P 2191459685062,
   s1P 1049131334314, s1P 1273334812247, s1P 1781592204786, s1N 2036760083618,
   s1P 1583332973851, s1P 1347304706043, s1N 193194266624, s1N 1227547424852, s1N 987893237762,
   s1N 92967528322, s1N 919987427214, s1N 2306923999187, s1N 1348880074394, s1P 1299397992655,
   s1N 389513278840, s1P 1516840524442, s1P 2519964110791, s1P 1482920243418, s1N 1505929468838,
   s1N 1548304914264, s1N 2983858113620, s1P 640996888600, s1P 1911636763470, s1P 50540448519,
   s1P 97725872568, s1P 1050628448766, s1P 2656566968100, s1N 418496748522, s1N 607493857431,
   s1N 2073930101386, s1N 1232818842484, s1N 1710924163248, s1N 408293062680, s1P 2072701811105,
   s1N 1639978625151, s1N 1582328381946, s1N 2433795950843, s1N 7321268288869,
   s1N 4979979278943, s1N 8643593099558, s1N 14942142978978, s1N 14731066761453,
   s1N 11163018765558, s1P 4130947344642, s1P 4507158535788, s1N 1805734696902,
   s1N 3430281306604, s1N 7697296302533, s1N 5392564863174, s1N 1947724629551, s1N 342751109888,
   s1N 3053633261167, s1N 3462053601091, s1P 1649253905116, s1P 5642654767201, s1P 954681134886,
   s1P 4428459048367, s1P 574671015885, s1N 3484596876329]
private def s1V11S4 : List ℤ :=
  [s1P 1041572341594, s1P 830617720086, s1N 6666105784688, s1N 5322121315465, s1N 3357310993188,
   s1N 3400971273200, s1P 849782434511, s1N 3938126842816, s1P 2522386837501, s1N 8909014199758,
   s1P 541480091555, s1P 1523194495739, s1N 2981471150457, s1N 2004980001708, s1P 4852741889230,
   s1P 2140992907149, s1P 6441845729080, s1P 7333417573550, s1P 1706539530826, s1P 666171412365,
   s1P 5860427286794, s1P 4079061030590, s1P 5727667990400, s1N 4817878154595,
   s1P 5787997546137, s1P 2497408805862, s1N 3932586613502, s1N 4699030275781,
   s1P 3755354169767, s1P 417292052281, s1N 1425840481697, s1P 5064552398368, s1P 5256041386188,
   s1P 2380820101763, s1P 2544849068760, s1N 5667853864653, s1N 3418607997835,
   s1P 6354583260475, s1N 2849323854019, s1N 2393633484537, s1N 7509905992109, s1N 665520030894,
   s1P 4829124457336, s1P 4044894034344, s1N 1773897849413, s1N 2269272826134,
   s1P 1618468675356, s1P 12781998266615, s1P 3182189048091, s1N 6608656700475,
   s1P 5512390304860, s1N 3212163786745, s1P 5579462567045, s1N 3099136183168,
   s1N 7356891616555, s1P 1890612958199, s1N 8449575833967, s1P 7611584499635,
   s1P 4737013560560, s1N 62121325866, s1N 6483369601292, s1N 9890677217558, s1P 6004708859966,
   s1N 3798185951735]
private def s1V11S5 : List ℤ :=
  [s1P 12133513736948, s1P 10388289683243, s1P 7791374534417, s1P 42249315620034,
   s1P 89966346638892, s1P 145412355803309, s1P 202048745401746, s1P 253667077060957,
   s1P 294907851416007, s1P 322908774275618, s1P 336677394927964, s1P 336274921582882,
   s1P 323422701556187, s1P 300892506493519, s1P 271440455554398, s1P 237943469201895,
   s1P 203191466840757, s1P 169480271595894, s1P 137919267618835, s1P 109805257108758,
   s1P 85278871661676, s1P 65018026630929, s1P 48580763531439, s1P 35504021250875,
   s1P 25607046898762, s1P 18210367739416, s1P 12627962183671, s1P 8533859735821,
   s1P 5644523359254, s1P 3608600785718, s1P 2167815043409, s1P 1196745925383, s1P 607110658482,
   s1P 293017504524, s1P 144383269076, s1P 78464867255, s1P 48069565252, s1P 31416163033,
   s1P 20505518292, s1P 13029857305, s1P 8064191522, s1P 4831167132, s1P 2744952359,
   s1P 1450611592, s1P 710095630, s1P 326983479, s1N 146366979, s1P 66321834, s1P 31256637,
   s1P 15323971, s1P 7705463, s1P 3920867, s1P 1986871, s1P 979981, s1P 460582, s1P 204773,
   s1P 87235, s1P 36728, s1P 15822, s1P 7086, s1P 3258, s1N 1488, s1P 661, s1P 277]
private def s1V11S6 : List ℤ :=
  [s1P 107, s1P 35, s1P 9, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V11S7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V11S8 : List ℤ :=
  [s1P 0]
private def s1V11 : List ℤ :=
  s1V11S0 ++
    (s1V11S1 ++
    (s1V11S2 ++
    (s1V11S3 ++
    (s1V11S4 ++
    (s1V11S5 ++
    (s1V11S6 ++
    (s1V11S7 ++
    s1V11S8)))))))
private def s1Ch12 : List Rkm128kSeg := [
  ⟨173, 481840, 2, 25,
    rkm128kMask56 513 [60453490311826272, 1311001173573798, 6291756635408800,
      31990047616569716, 54328056181727790, 1697658905429010, 0,
      45036133721309252, 18018934003337220, 389]⟩]
private theorem s1Segs_split : lm4k512l248krS1Segs =
    s1Ch0 ++ (s1Ch1 ++ (s1Ch2 ++ (s1Ch3 ++ (s1Ch4 ++ (s1Ch5 ++ (s1Ch6 ++
      (s1Ch7 ++ (s1Ch8 ++ (s1Ch9 ++ (s1Ch10 ++ (s1Ch11 ++ s1Ch12))))))))))) := rfl
private theorem s1B0_ok :
    Bool.and (s1NatEq (rkm128kSegListLen lm4k512l248krS1Segs) 28)
      (s1RunAtEq s1Ch0 lm4k512l248krS1LIn lm4k512l248krS1DCurIn
        lm4k512l248krS1PadIn lm4k512l248krS1VecIn
        104 416 1735575570 s1V0) = true := by decide +kernel
private theorem s1B1_ok :
    s1RunAtEq s1Ch1 104 416 1735575570 s1V0
      113 452 1924327997 s1V1 = true := by decide +kernel
private theorem s1B2_ok :
    s1RunAtEq s1Ch2 113 452 1924327997 s1V1
      120 480 1982489795 s1V2 = true := by decide +kernel
private theorem s1B3_ok :
    s1RunAtEq s1Ch3 120 480 1982489795 s1V2
      128 512 2043864659 s1V3 = true := by decide +kernel
private theorem s1B4_ok :
    s1RunAtEq s1Ch4 128 512 2043864659 s1V3
      134 512 2153158318 s1V4 = true := by decide +kernel
private theorem s1B5_ok :
    s1RunAtEq s1Ch5 134 512 2153158318 s1V4
      142 512 2240076596 s1V5 = true := by decide +kernel
private theorem s1B6_ok :
    s1RunAtEq s1Ch6 142 512 2240076596 s1V5
      148 512 2362051371 s1V6 = true := by decide +kernel
private theorem s1B7_ok :
    s1RunAtEq s1Ch7 148 512 2362051371 s1V6
      154 512 2420864767 s1V7 = true := by decide +kernel
private theorem s1B8_ok :
    s1RunAtEq s1Ch8 154 512 2420864767 s1V7
      157 512 2437461190 s1V8 = true := by decide +kernel
private theorem s1B9_ok :
    s1RunAtEq s1Ch9 157 512 2437461190 s1V8
      161 512 2467013523 s1V9 = true := by decide +kernel
private theorem s1B10_ok :
    s1RunAtEq s1Ch10 161 512 2467013523 s1V9
      164 512 2531704457 s1V10 = true := by decide +kernel
private theorem s1B11_ok :
    s1RunAtEq s1Ch11 164 512 2531704457 s1V10
      168 512 2581137479 s1V11 = true := by decide +kernel
private theorem s1B12_ok :
    s1RunAtEq s1Ch12 168 512 2581137479 s1V11
      lm4k512l248krS1LOut lm4k512l248krS1DCurOut lm4k512l248krS1PadOut
      lm4k512l248krS1Vec = true := by decide +kernel

/-- Segment count of `lm4k512l248krS1Segs` (`28` segments). -/
theorem lm4k512l248krS1_len : rkm128kSegListLen lm4k512l248krS1Segs = 28 :=
  s1NatEq_eq (s1AndLeft s1B0_ok)

/-- Exact `rkm128kRunSegs 4 248 512` step across `lm4k512l248krS1Segs`. -/
theorem lm4k512l248krS1_step :
    rkm128kRunSegs 4 248 512 lm4k512l248krS1Segs lm4k512l248krS1LIn lm4k512l248krS1DCurIn
      lm4k512l248krS1PadIn lm4k512l248krS1VecIn =
      (lm4k512l248krS1LOut, lm4k512l248krS1DCurOut, lm4k512l248krS1PadOut,
        lm4k512l248krS1Vec) := by
  rw [s1Segs_split]
  exact s1RunStep (s1AndRight s1B0_ok) (s1RunStep s1B1_ok (s1RunStep s1B2_ok
    (s1RunStep s1B3_ok (s1RunStep s1B4_ok (s1RunStep s1B5_ok (s1RunStep s1B6_ok
      (s1RunStep s1B7_ok (s1RunStep s1B8_ok (s1RunStep s1B9_ok (s1RunStep s1B10_ok
        (s1RunStep s1B11_ok (s1RunLast s1B12_ok))))))))))))

/-- Suffix chaining lemma advancing `rkm128kRunSegs 4 248 512` past `lm4k512l248krS1Segs`. -/
theorem lm4k512l248krS1_run_after (rest : List Rkm128kSeg) :
    rkm128kRunSegs 4 248 512 (lm4k512l248krS1Segs ++ rest) lm4k512l248krS1LIn
      lm4k512l248krS1DCurIn lm4k512l248krS1PadIn lm4k512l248krS1VecIn =
      rkm128kRunSegs 4 248 512 rest lm4k512l248krS1LOut lm4k512l248krS1DCurOut
        lm4k512l248krS1PadOut lm4k512l248krS1Vec := by
  rw [rkm128kRunSegs_append, lm4k512l248krS1_step]

/-- Prefix chaining lemma extending any certified state ending at `lm4k512l248krS1*In`. -/
theorem lm4k512l248krS1_after {segsPrev : List Rkm128kSeg} {l0 d0 p0 : ℕ} {v0 : List ℤ}
    (hPrev : rkm128kRunSegs 4 248 512 segsPrev l0 d0 p0 v0 =
      (lm4k512l248krS1LIn, lm4k512l248krS1DCurIn, lm4k512l248krS1PadIn, lm4k512l248krS1VecIn)) :
    rkm128kRunSegs 4 248 512 (segsPrev ++ lm4k512l248krS1Segs) l0 d0 p0 v0 =
      (lm4k512l248krS1LOut, lm4k512l248krS1DCurOut, lm4k512l248krS1PadOut,
        lm4k512l248krS1Vec) := by
  rw [rkm128kRunSegs_append, hPrev]
  dsimp only
  exact lm4k512l248krS1_step

end

end QuantumComputation.Specs.GroverFindAll.Rk128kLowM4K512L248KrPt1
