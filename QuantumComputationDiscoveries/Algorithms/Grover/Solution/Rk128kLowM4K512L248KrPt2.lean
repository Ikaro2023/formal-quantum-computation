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
# 128-Segment Krotov `(4, 512)` `L <= 248` Part 2 (`Rk128kLowM4K512L248KrPt2`)

Certifies Slice 2 (`r = 512` segments `75..95`, `21` segments, `441,856` F1272 /
`442,719 <= 450,000` Horner coord-ops, `lTableMax = 248`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kLowM4K512L248KrPt2

@[expose] public section

open QuantumComputation.Specs.DickeSol

/-- Segments `75..95` (`21` segments) of `(4, 512)` `r = 512` at `lTableMax = 248`. -/
def lm4k512l248krS2Segs : List Rkm128kSeg := [
  ⟨177, 467971, 2, 25, rkm128kMask56 512
    [7434184003909292, 59625420459660617, 10632777366998970, 24598555698123695,
     71991116309910581, 6915969775651351, 1125968626319374, 20829148276719620, 8589934720, 133]⟩,
  ⟨183, 463197, 2, 26, rkm128kMask56 513
    [69832958656239620, 20446332567534618, 63052235815009344, 20403110898940392,
     27833182939842263, 7318926154002267, 3082, 9323859677298688, 19140315596197960, 266]⟩,
  ⟨185, 475038, 2, 26, rkm128kMask56 513
    [57257783257322766, 6776884607643074, 9320636818384114, 71744008955209946,
     50427122939652720, 65240277917231635, 1575217, 9007200349454336, 40532465366335492, 392]⟩,
  ⟨190, 443433, 2, 25, rkm128kMask56 511
    [34456701757624756, 22501048188854136, 1517570442953417, 29084280723618842,
     4539304258668562, 43956570415133202, 520094890, 18014673521606912, 9288691411320848, 84]⟩,
  ⟨195, 450313, 2, 26, rkm128kMask56 512
    [11236467344599726, 1320257301991916, 58019880635699012, 50031370665228646,
     67750598199376815, 46638005932956733, 104687281139, 1407516625862912, 2322178238316544,
     253]⟩,
  ⟨199, 441441, 2, 26, rkm128kMask56 505
    [69570202450240047, 14894586243112655, 25261030756769686, 51658375034638593,
     18734994339915545, 12528387402239104, 31044229271200, 9007201427390464, 20829182703435784,
     1]⟩,
  ⟨202, 441519, 2, 26, rkm128kMask56 512
    [37754965737125206, 43939451031292739, 35369797591396472, 55077809332432819,
     33081318645314659, 27591048835936164, 7921671528211380, 563224832376832, 704788027146760,
     244]⟩,
  ⟨207, 433460, 2, 26, rkm128kMask56 513
    [31032159399159469, 12820364245077554, 3303663644720199, 50639383086997954,
     63103703488575332, 7126214845391891, 45621026663182148, 8796093022217, 1275712661111044,
     304]⟩,
  ⟨209, 439306, 2, 26, rkm128kMask56 512
    [68445222648312158, 61639509745257648, 6825908312755023, 3546191776120838, 848484415703998,
     3749136889778292, 6247289304725906, 2831, 2199023387650, 201]⟩,
  ⟨214, 410207, 2, 25, rkm128kMask56 512
    [64473128478156441, 57970528993397465, 53761779525446129, 9011049499820045,
     23061332069434398, 6073843437539600, 61882839344933, 295570, 18031990764732416, 178]⟩,
  ⟨217, 402850, 2, 25, rkm128kMask56 512
    [8324861876700525, 28879843379281795, 42905704989062592, 15018369014296557,
     66606778318088733, 37327771010748147, 43890310221418593, 66551839, 4543182047019264, 160]⟩,
  ⟨218, 275145, 1, 30, rkm128kMask56 513
    [58479300394209174, 40346263685923871, 20652201080752968, 28983508914532376,
     27098593895034425, 65390168728813080, 19598807818912296, 838949952, 1135796048626688, 388]⟩,
  ⟨220, 276964, 1, 31, rkm128kMask56 511
    [58480926785667437, 69134494634100131, 3446166932286369, 46564291401591539,
     54403010323078054, 38062406260347711, 41036855218603333, 8890322274, 9026990598258944, 64]⟩,
  ⟨220, 284330, 1, 31, rkm128kMask56 513
    [55452833930729741, 28760394734969036, 65563850501793958, 68891240695194352,
     26783027169961284, 141584434577793, 41593219345145916, 414749628416, 2256833515356160,
     265]⟩,
  ⟨224, 263531, 1, 29, rkm128kMask56 513
    [57829625682395063, 45529707217668885, 70898851838419198, 10098770070438437,
     42751599282473378, 272952684706122, 59221167294663950, 5007891274342, 564191207358464,
     320]⟩,
  ⟨224, 264920, 1, 30, rkm128kMask56 511
    [11237218724552925, 39556997674417282, 34348330814982203, 633074018065142,
     8899712324042752, 2291807493456266, 4716546455298595, 101310431171602, 18594944948109312,
     80]⟩,
  ⟨224, 270767, 1, 30, rkm128kMask56 513
    [1652351405434416, 66549242432212004, 38093787446832637, 71278220772310823,
     15804724625524257, 325870992296446, 60748909123059793, 2043251100490791, 4503883111989248,
     336]⟩,
  ⟨224, 275669, 1, 30, rkm128kMask56 513
    [5059758012750278, 51024064348642104, 46120457161798453, 24486654892588487,
     43039731049547895, 36706277178474540, 3149061440135872, 28150270359040104,
     4504770005958656, 340]⟩,
  ⟨224, 230701, 1, 27, rkm128kMask56 513
    [2822270405121116, 68768062832952664, 44857209411276771, 3042307088237644,
     14438164396406915, 35967207308277274, 40720549017948982, 56200466402016286,
     10141895254605825, 340]⟩,
  ⟨224, 280617, 1, 31, rkm128kMask56 511
    [36163353512384147, 43778481742913131, 42414915417767007, 18013467336632872,
     11167936016683014, 45603358022755592, 17073492383834691, 20278055780395296,
     2533274790395960, 84]⟩,
  ⟨224, 268642, 1, 30, rkm128kMask56 513
    [34255383640252210, 736223556055992, 38867377158076504, 14009560714444804,
     33369360282424176, 39373529318079099, 18768144348683724, 14234607117731827,
     2252349569499404, 341]⟩]

/-- Input multiplexing factor entering `lm4k512l248krS2Segs` (`173`). -/
def lm4k512l248krS2LIn : ℕ := 173

/-- Input Hilbert dimension entering `lm4k512l248krS2Segs` (`512`). -/
def lm4k512l248krS2DCurIn : ℕ := 512

/-- Input accumulated `10^15`-scale error pad entering `lm4k512l248krS2Segs`. -/
def lm4k512l248krS2PadIn : ℕ := 2644249481

/-- Slice `0` (`64` entries) of `lm4k512l248krS2VecIn`. -/
def lm4k512l248krS2VecIn0 : List ℤ :=
  [Int.negSucc 163089157, Int.ofNat 20291044, Int.ofNat 114596265, Int.ofNat 35954677,
   Int.negSucc 71129089, Int.negSucc 368019737, Int.ofNat 259515579, Int.ofNat 476196286,
   Int.negSucc 69824121, Int.negSucc 712413399, Int.negSucc 1816146081, Int.negSucc 282160223,
   Int.negSucc 735178734, Int.ofNat 1564144967, Int.negSucc 632729679, Int.negSucc 1975484045,
   Int.negSucc 587364311, Int.ofNat 361338986, Int.negSucc 1663423298, Int.ofNat 1387412365,
   Int.negSucc 4350988810, Int.negSucc 3152338730, Int.ofNat 205099848, Int.negSucc 1898579824,
   Int.negSucc 4201087550, Int.negSucc 669383932, Int.negSucc 5717272072,
   Int.negSucc 8979118975, Int.negSucc 7685848358, Int.ofNat 6576127583,
   Int.negSucc 4485457958, Int.ofNat 447582673, Int.ofNat 2741359690, Int.ofNat 2531450253,
   Int.ofNat 10401050562, Int.ofNat 1314971138, Int.ofNat 3275740604, Int.negSucc 5371932287,
   Int.ofNat 2649938848, Int.negSucc 19687040810, Int.negSucc 34373785403,
   Int.negSucc 3740916063, Int.ofNat 10872199228, Int.ofNat 27869553590, Int.ofNat 34005289972,
   Int.negSucc 24037762313, Int.negSucc 9155429675, Int.ofNat 1142443962,
   Int.ofNat 20791958793, Int.ofNat 13265001650, Int.ofNat 10742387077, Int.negSucc 3558517870,
   Int.negSucc 48148541816, Int.negSucc 9620350527, Int.negSucc 24672763677,
   Int.negSucc 40573049891, Int.ofNat 1146486685, Int.ofNat 296439146, Int.ofNat 19422606430,
   Int.negSucc 8911766846, Int.negSucc 17613346201, Int.ofNat 14919281729,
   Int.negSucc 32200739102, Int.negSucc 6915941227]
/-- Slice `1` (`64` entries) of `lm4k512l248krS2VecIn`. -/
def lm4k512l248krS2VecIn1 : List ℤ :=
  [Int.negSucc 68573696518, Int.ofNat 29090147408, Int.negSucc 46660253357,
   Int.ofNat 29098768008, Int.ofNat 84846887999, Int.ofNat 15354217283,
   Int.negSucc 28766672293, Int.ofNat 34835055918, Int.ofNat 109698292528,
   Int.ofNat 92939921983, Int.ofNat 38173529176, Int.negSucc 20544448724,
   Int.ofNat 22009777905, Int.ofNat 91150479327, Int.ofNat 103688917292, Int.ofNat 79685109903,
   Int.negSucc 31417714792, Int.negSucc 222287422370, Int.negSucc 139125607677,
   Int.negSucc 131103524272, Int.ofNat 57120669905, Int.negSucc 37111861742,
   Int.negSucc 40626104764, Int.ofNat 65196727274, Int.ofNat 115909262373,
   Int.negSucc 155280732767, Int.ofNat 25239966560, Int.ofNat 103347211458,
   Int.negSucc 34944328129, Int.negSucc 48125925078, Int.negSucc 27549413582,
   Int.ofNat 93398191540, Int.negSucc 219251379823, Int.negSucc 150201990618,
   Int.negSucc 175518461765, Int.negSucc 132129930261, Int.negSucc 37574547856,
   Int.ofNat 29615565707, Int.ofNat 53203366586, Int.negSucc 98395813150,
   Int.ofNat 99843733592, Int.negSucc 74544082762, Int.negSucc 59229995156,
   Int.ofNat 90639502143, Int.negSucc 137857734731, Int.negSucc 276910250978,
   Int.negSucc 415563987670, Int.negSucc 482321343917, Int.negSucc 682178398807,
   Int.negSucc 570393818649, Int.ofNat 90870457684, Int.ofNat 923236643910,
   Int.ofNat 1687624706377, Int.ofNat 1424718322786, Int.ofNat 1077453101373,
   Int.negSucc 195997900599, Int.negSucc 1470764803258, Int.negSucc 1549222603903,
   Int.negSucc 1068074578781, Int.ofNat 1685716432124, Int.negSucc 92999697467,
   Int.negSucc 2134610485527, Int.negSucc 1085521962958, Int.ofNat 138781013785]
/-- Slice `2` (`64` entries) of `lm4k512l248krS2VecIn`. -/
def lm4k512l248krS2VecIn2 : List ℤ :=
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
/-- Slice `3` (`64` entries) of `lm4k512l248krS2VecIn`. -/
def lm4k512l248krS2VecIn3 : List ℤ :=
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
/-- Slice `4` (`64` entries) of `lm4k512l248krS2VecIn`. -/
def lm4k512l248krS2VecIn4 : List ℤ :=
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
/-- Slice `5` (`64` entries) of `lm4k512l248krS2VecIn`. -/
def lm4k512l248krS2VecIn5 : List ℤ :=
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
   Int.ofNat 277065235119, Int.ofNat 147707275722, Int.ofNat 81073807024,
   Int.ofNat 46312704952, Int.ofNat 27306056351, Int.ofNat 16438001637, Int.ofNat 9991984387,
   Int.ofNat 5984588007, Int.ofNat 3413792397, Int.ofNat 1807969850, Int.ofNat 883666432,
   Int.ofNat 404733293, Int.ofNat 179762105, Int.ofNat 80888945, Int.ofNat 38117791,
   Int.ofNat 18888140, Int.ofNat 9646941, Int.ofNat 4955099, Int.ofNat 2512386,
   Int.ofNat 1243500, Int.ofNat 598697, Int.ofNat 280815]
/-- Slice `6` (`64` entries) of `lm4k512l248krS2VecIn`. -/
def lm4k512l248krS2VecIn6 : List ℤ :=
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
/-- Slice `7` (`64` entries) of `lm4k512l248krS2VecIn`. -/
def lm4k512l248krS2VecIn7 : List ℤ :=
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
/-- Slice `8` (`1` entries) of `lm4k512l248krS2VecIn`. -/
def lm4k512l248krS2VecIn8 : List ℤ :=
  [Int.ofNat 0]
/-- Checkpoint fixed-point vector entering `lm4k512l248krS2Segs` (`513` entries). -/
def lm4k512l248krS2VecIn : List ℤ :=
  lm4k512l248krS2VecIn0 ++
  (lm4k512l248krS2VecIn1 ++
  (lm4k512l248krS2VecIn2 ++
  (lm4k512l248krS2VecIn3 ++
  (lm4k512l248krS2VecIn4 ++
  (lm4k512l248krS2VecIn5 ++
  (lm4k512l248krS2VecIn6 ++
  (lm4k512l248krS2VecIn7 ++
  (lm4k512l248krS2VecIn8))))))))

/-- Output multiplexing factor exiting `lm4k512l248krS2Segs` (`224`). -/
def lm4k512l248krS2LOut : ℕ := 224

/-- Output Hilbert dimension exiting `lm4k512l248krS2Segs` (`512`). -/
def lm4k512l248krS2DCurOut : ℕ := 512

/-- Output accumulated `10^15`-scale error pad exiting `lm4k512l248krS2Segs`. -/
def lm4k512l248krS2PadOut : ℕ := 3397256286

/-- Slice `0` (`64` entries) of `lm4k512l248krS2Vec`. -/
def lm4k512l248krS2Vec0 : List ℤ :=
  [Int.negSucc 2461216, Int.negSucc 6367209, Int.negSucc 12761983, Int.negSucc 16479207,
   Int.ofNat 122325945, Int.ofNat 112415778, Int.ofNat 4370959, Int.ofNat 14473766,
   Int.ofNat 25696855, Int.ofNat 95306017, Int.negSucc 225845408, Int.negSucc 267998225,
   Int.negSucc 251773905, Int.ofNat 22071990, Int.negSucc 47661863, Int.ofNat 80061998,
   Int.ofNat 68088589, Int.ofNat 162823036, Int.negSucc 278156994, Int.ofNat 85726914,
   Int.negSucc 391835389, Int.ofNat 645123218, Int.negSucc 341755394, Int.negSucc 730658837,
   Int.ofNat 378543130, Int.negSucc 306996409, Int.negSucc 639939241, Int.negSucc 1446211158,
   Int.negSucc 3796047163, Int.negSucc 2944228890, Int.negSucc 488947684, Int.ofNat 961011936,
   Int.negSucc 149671768, Int.ofNat 1795416660, Int.ofNat 2446345388, Int.ofNat 2783127609,
   Int.ofNat 1705270112, Int.ofNat 4313012207, Int.ofNat 1131590665, Int.ofNat 1526896421,
   Int.ofNat 502611749, Int.ofNat 5400051246, Int.ofNat 3205069977, Int.ofNat 868139196,
   Int.ofNat 5965941013, Int.ofNat 2611031244, Int.negSucc 899104516, Int.ofNat 2198528228,
   Int.ofNat 1870732210, Int.ofNat 3781249415, Int.ofNat 1252919356, Int.negSucc 1781581109,
   Int.ofNat 9153317556, Int.ofNat 6554910207, Int.negSucc 2115519292, Int.negSucc 12011896454,
   Int.ofNat 2903144174, Int.negSucc 1959313369, Int.ofNat 2529325496, Int.ofNat 2090891651,
   Int.ofNat 3031001298, Int.ofNat 11278973478, Int.ofNat 551173602, Int.ofNat 2104606654]
/-- Slice `1` (`64` entries) of `lm4k512l248krS2Vec`. -/
def lm4k512l248krS2Vec1 : List ℤ :=
  [Int.ofNat 4290318338, Int.negSucc 8611427159, Int.negSucc 7765735243,
   Int.negSucc 10189502779, Int.ofNat 797031862, Int.ofNat 17518419018, Int.ofNat 27067596475,
   Int.ofNat 20883815765, Int.ofNat 260364854, Int.negSucc 3588798590, Int.negSucc 16503079431,
   Int.negSucc 27499858841, Int.negSucc 8057246795, Int.ofNat 22805780942,
   Int.ofNat 13481747574, Int.ofNat 6482358625, Int.negSucc 21697236467, Int.ofNat 7960459717,
   Int.ofNat 9571950602, Int.ofNat 1239301633, Int.ofNat 6765161144, Int.negSucc 10528749621,
   Int.negSucc 13909165877, Int.negSucc 23129339767, Int.ofNat 13753067991,
   Int.ofNat 3966924652, Int.negSucc 24225682828, Int.ofNat 23128771522,
   Int.negSucc 18655250214, Int.ofNat 27588603265, Int.ofNat 19689059489,
   Int.ofNat 26757246043, Int.ofNat 48328346234, Int.ofNat 7708314553, Int.ofNat 15758746553,
   Int.negSucc 16892461901, Int.ofNat 11526797240, Int.ofNat 7892201367, Int.ofNat 27484005922,
   Int.negSucc 29867669629, Int.negSucc 9879824052, Int.ofNat 8329535616, Int.ofNat 2329712653,
   Int.negSucc 8460073943, Int.negSucc 78248951273, Int.negSucc 112254791352,
   Int.negSucc 54448238989, Int.negSucc 41666898862, Int.ofNat 29891283561,
   Int.negSucc 8678735487, Int.negSucc 21352783673, Int.negSucc 14986464470,
   Int.negSucc 12029876011, Int.ofNat 41326658418, Int.ofNat 47008702922, Int.ofNat 7957071252,
   Int.ofNat 54247524987, Int.ofNat 15198344236, Int.ofNat 19835201811,
   Int.negSucc 66494426810, Int.negSucc 4455950408, Int.negSucc 5046058339,
   Int.negSucc 58486800656, Int.negSucc 61666462578]
/-- Slice `2` (`64` entries) of `lm4k512l248krS2Vec`. -/
def lm4k512l248krS2Vec2 : List ℤ :=
  [Int.negSucc 1646687209, Int.negSucc 38228099516, Int.ofNat 20835316100,
   Int.negSucc 25153872413, Int.negSucc 117095820456, Int.ofNat 22630088722,
   Int.ofNat 52162557795, Int.ofNat 65164612555, Int.negSucc 17539325362,
   Int.ofNat 43268520352, Int.ofNat 45735493506, Int.ofNat 43081141121,
   Int.negSucc 45755128946, Int.ofNat 28359605411, Int.ofNat 2291913329,
   Int.negSucc 33153593805, Int.negSucc 57019482907, Int.ofNat 87284025688,
   Int.negSucc 18753909611, Int.ofNat 398463205, Int.negSucc 159558532612,
   Int.ofNat 51942306018, Int.negSucc 98233580896, Int.ofNat 63895721532,
   Int.ofNat 50592595558, Int.ofNat 8718023393, Int.negSucc 38456910304,
   Int.ofNat 107734612252, Int.negSucc 46756472432, Int.negSucc 171234380170,
   Int.negSucc 151218845770, Int.negSucc 172702313623, Int.negSucc 184762426529,
   Int.ofNat 77668781896, Int.ofNat 96378816413, Int.ofNat 82918432907,
   Int.negSucc 23531100182, Int.negSucc 101231925482, Int.negSucc 55919122574,
   Int.negSucc 174460907984, Int.negSucc 86329697488, Int.negSucc 180607546243,
   Int.negSucc 26982974576, Int.ofNat 52141050807, Int.negSucc 61873152462,
   Int.ofNat 45771520510, Int.negSucc 167751001551, Int.negSucc 147293278903,
   Int.negSucc 270128548263, Int.negSucc 320341322461, Int.negSucc 309598142699,
   Int.negSucc 221974278765, Int.ofNat 14558821175, Int.ofNat 225330345881,
   Int.ofNat 193178959994, Int.ofNat 152939837117, Int.negSucc 131683889848,
   Int.ofNat 164627842367, Int.ofNat 86167333882, Int.ofNat 113048225241,
   Int.negSucc 51073887982, Int.ofNat 20922190872, Int.ofNat 275856641298,
   Int.ofNat 353829827246]
/-- Slice `3` (`64` entries) of `lm4k512l248krS2Vec`. -/
def lm4k512l248krS2Vec3 : List ℤ :=
  [Int.ofNat 762134408552, Int.ofNat 565413863227, Int.ofNat 179891711369,
   Int.negSucc 426908657378, Int.negSucc 106619036081, Int.ofNat 102754378399,
   Int.ofNat 354448969976, Int.negSucc 144365140253, Int.negSucc 423655220556,
   Int.ofNat 192112257321, Int.ofNat 254999253431, Int.ofNat 496654077914,
   Int.ofNat 289275062944, Int.negSucc 378290038462, Int.negSucc 496276979231,
   Int.ofNat 495876508086, Int.ofNat 201413360713, Int.negSucc 101930846803,
   Int.negSucc 65327327228, Int.ofNat 446716259019, Int.ofNat 68570435675,
   Int.negSucc 414709720018, Int.negSucc 180364037002, Int.negSucc 426351266128,
   Int.negSucc 621496326082, Int.negSucc 366436968993, Int.negSucc 1039983234808,
   Int.negSucc 1124649377781, Int.negSucc 284370814275, Int.ofNat 196922600060,
   Int.ofNat 869595327718, Int.ofNat 1019190515992, Int.ofNat 221664657835,
   Int.ofNat 248850861078, Int.ofNat 762036972189, Int.ofNat 866770889947,
   Int.negSucc 140900593602, Int.negSucc 41750107593, Int.ofNat 40879137296,
   Int.ofNat 258778205417, Int.negSucc 244942993740, Int.negSucc 522613427242,
   Int.negSucc 957935934336, Int.negSucc 1168471558850, Int.negSucc 2053552248501,
   Int.negSucc 3123226742049, Int.negSucc 3188934933046, Int.negSucc 3195777686602,
   Int.negSucc 4086820502506, Int.negSucc 3130925174333, Int.negSucc 2777306775060,
   Int.negSucc 1704610636367, Int.ofNat 955758708209, Int.ofNat 4022407862422,
   Int.ofNat 6543878701448, Int.ofNat 6065519085233, Int.ofNat 2773472906024,
   Int.ofNat 238009857241, Int.negSucc 114879242580, Int.ofNat 1021972670321,
   Int.ofNat 1314019556004, Int.ofNat 2734088562529, Int.ofNat 243895217459,
   Int.negSucc 933704323124]
/-- Slice `4` (`64` entries) of `lm4k512l248krS2Vec`. -/
def lm4k512l248krS2Vec4 : List ℤ :=
  [Int.negSucc 1186188672824, Int.negSucc 1237414880497, Int.negSucc 109459839743,
   Int.ofNat 178849865872, Int.ofNat 2136930340005, Int.ofNat 1734433770957,
   Int.negSucc 3668992278949, Int.ofNat 1581470921, Int.negSucc 2989166559583,
   Int.ofNat 2172798021735, Int.negSucc 270396366523, Int.ofNat 1743574054609,
   Int.ofNat 360402686070, Int.negSucc 128783214295, Int.ofNat 708260108502,
   Int.ofNat 2873210365782, Int.ofNat 992587989643, Int.negSucc 968560904050,
   Int.ofNat 388286516667, Int.ofNat 1845594085880, Int.negSucc 29189802638,
   Int.ofNat 28659090519, Int.negSucc 1101595268429, Int.negSucc 862491403276,
   Int.negSucc 324003939120, Int.ofNat 5228928807696, Int.negSucc 347787755854,
   Int.ofNat 1746336984680, Int.ofNat 815327489967, Int.ofNat 2018769993063,
   Int.ofNat 1109373104472, Int.ofNat 4761027815791, Int.ofNat 1410368924285,
   Int.ofNat 1278040424724, Int.negSucc 715965348474, Int.ofNat 4392463160814,
   Int.ofNat 3693836979780, Int.ofNat 6625551816198, Int.ofNat 1952436207805,
   Int.ofNat 2437080382380, Int.negSucc 453861781329, Int.ofNat 2592266953309,
   Int.ofNat 5943750931256, Int.ofNat 5276307750421, Int.ofNat 3833446848355,
   Int.ofNat 611636092573, Int.ofNat 3489779270744, Int.ofNat 8761607087029,
   Int.ofNat 3776671274875, Int.ofNat 3209765239788, Int.ofNat 718568235705,
   Int.negSucc 4997981183646, Int.negSucc 997104411928, Int.negSucc 805034690947,
   Int.negSucc 1228908009139, Int.negSucc 2498307012519, Int.negSucc 3901318981052,
   Int.negSucc 759002463655, Int.negSucc 1697866805699, Int.ofNat 2964321410467,
   Int.ofNat 3091547320562, Int.negSucc 1768757688422, Int.ofNat 3037784254375,
   Int.negSucc 574897054484]
/-- Slice `5` (`64` entries) of `lm4k512l248krS2Vec`. -/
def lm4k512l248krS2Vec5 : List ℤ :=
  [Int.ofNat 126669334269, Int.negSucc 152599578697, Int.negSucc 4163775559938,
   Int.negSucc 6342239098264, Int.negSucc 5968605773938, Int.ofNat 4619547310009,
   Int.ofNat 1282263236459, Int.ofNat 3054774510488, Int.negSucc 238119945932,
   Int.ofNat 3445675360177, Int.negSucc 3071634166575, Int.ofNat 4901006707653,
   Int.ofNat 463142394667, Int.ofNat 3430366198512, Int.ofNat 789733459864,
   Int.ofNat 3545294651235, Int.negSucc 3492984233115, Int.negSucc 9200486615925,
   Int.ofNat 792625114390, Int.ofNat 8701119135904, Int.ofNat 13012339687143,
   Int.ofNat 15061750305861, Int.ofNat 13365293449233, Int.ofNat 16355514551051,
   Int.ofNat 4936344531054, Int.negSucc 4758222495593, Int.negSucc 6923683571991,
   Int.negSucc 6186567558872, Int.ofNat 2280148882390, Int.ofNat 3262548242739,
   Int.negSucc 1803538950255, Int.negSucc 5190300944693, Int.ofNat 3181249489927,
   Int.ofNat 1155479574952, Int.negSucc 7141866737470, Int.negSucc 3568511729310,
   Int.negSucc 2718066951105, Int.negSucc 13387826085465, Int.negSucc 2278562414186,
   Int.ofNat 9546964102502, Int.ofNat 6904029024375, Int.ofNat 7573830908729,
   Int.ofNat 10677604179297, Int.ofNat 9887880744546, Int.negSucc 1434049434796,
   Int.ofNat 851070880045, Int.negSucc 10733700930860, Int.ofNat 3474871454520,
   Int.ofNat 1160707320040, Int.negSucc 10194760005250, Int.negSucc 2722856640881,
   Int.negSucc 8658935833851, Int.negSucc 15940671852836, Int.ofNat 7719742711999,
   Int.ofNat 8910346964510, Int.ofNat 21350154980665, Int.ofNat 12868798984544,
   Int.ofNat 3423414957798, Int.ofNat 1930552120230, Int.negSucc 2106622762022,
   Int.negSucc 8157627323401, Int.ofNat 3493325245634, Int.negSucc 1791868907647,
   Int.ofNat 2450480645501]
/-- Slice `6` (`64` entries) of `lm4k512l248krS2Vec`. -/
def lm4k512l248krS2Vec6 : List ℤ :=
  [Int.ofNat 5834798659008, Int.negSucc 2715868865002, Int.negSucc 9244740443880,
   Int.ofNat 5949238145567, Int.ofNat 5284085805257, Int.ofNat 6542279794469,
   Int.ofNat 323251464080, Int.negSucc 4311529771797, Int.negSucc 1647864611785,
   Int.ofNat 5939047139891, Int.negSucc 9654965917771, Int.negSucc 9417703996479,
   Int.ofNat 945016394926, Int.ofNat 10089037636900, Int.negSucc 3769588236716,
   Int.negSucc 525686186776, Int.negSucc 14351341011671, Int.ofNat 2478450487065,
   Int.ofNat 9537984215396, Int.negSucc 6462533140667, Int.negSucc 9390949757229,
   Int.negSucc 8944130702077, Int.ofNat 7073368900618, Int.ofNat 12871367183025,
   Int.ofNat 12328168494648, Int.negSucc 728786762595, Int.negSucc 5731604539892,
   Int.negSucc 3860357599801, Int.ofNat 10819571697585, Int.ofNat 6192880166572,
   Int.ofNat 9019661257348, Int.ofNat 7566185522221, Int.negSucc 2707531241439,
   Int.ofNat 6138265736157, Int.negSucc 785123320875, Int.ofNat 4258722750726,
   Int.negSucc 510056852139, Int.ofNat 575129053818, Int.negSucc 1155473446163,
   Int.ofNat 12263659638386, Int.negSucc 8918556998861, Int.ofNat 1846339825445,
   Int.negSucc 3010739502134, Int.negSucc 7435450524727, Int.negSucc 19151150574128,
   Int.negSucc 5775188965844, Int.ofNat 1615640747035, Int.negSucc 4543873496248,
   Int.negSucc 7424797558367, Int.ofNat 13682183991655, Int.negSucc 5983918681590,
   Int.negSucc 4106330158655, Int.ofNat 7737330180173, Int.ofNat 3579014893774,
   Int.negSucc 1102383690431, Int.negSucc 2501133348651, Int.ofNat 3446537102894,
   Int.ofNat 4345497161307, Int.negSucc 84493819048, Int.negSucc 2043082388302,
   Int.negSucc 1626982355251, Int.negSucc 17919666925964, Int.ofNat 1905408566494,
   Int.negSucc 12397187645547]
/-- Slice `7` (`64` entries) of `lm4k512l248krS2Vec`. -/
def lm4k512l248krS2Vec7 : List ℤ :=
  [Int.negSucc 8051266431263, Int.negSucc 8462113901112, Int.negSucc 44055205480,
   Int.ofNat 6117912365962, Int.negSucc 15178012020849, Int.ofNat 4723196565056,
   Int.ofNat 17093990880810, Int.ofNat 3471112370011, Int.ofNat 7592009117167,
   Int.ofNat 13883817693143, Int.ofNat 73494100714063, Int.ofNat 157731310091362,
   Int.ofNat 246540499772591, Int.ofNat 322056103192553, Int.ofNat 372478337833227,
   Int.ofNat 392924716301986, Int.ofNat 384448637364450, Int.ofNat 352443619821257,
   Int.ofNat 304688766948821, Int.ofNat 249440824981343, Int.ofNat 193974614866422,
   Int.ofNat 143621270461128, Int.ofNat 101444393296741, Int.ofNat 68486274562214,
   Int.ofNat 44287237523891, Int.ofNat 27486114824453, Int.ofNat 16396373127839,
   Int.ofNat 9411983547928, Int.ofNat 5205707158126, Int.ofNat 2777471655319,
   Int.ofNat 1428682903195, Int.ofNat 705973016852, Int.ofNat 333247397912,
   Int.ofNat 149440376219, Int.ofNat 63388011607, Int.ofNat 25345280417, Int.ofNat 9528815480,
   Int.ofNat 3368968517, Int.ofNat 1126974814, Int.negSucc 361812123, Int.ofNat 113722189,
   Int.ofNat 35567800, Int.ofNat 11098341, Int.ofNat 3415287, Int.ofNat 1017939,
   Int.ofNat 288671, Int.ofNat 76700, Int.ofNat 19060, Int.ofNat 4340, Int.ofNat 873,
   Int.ofNat 153, Int.negSucc 21, Int.ofNat 2, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Slice `8` (`1` entries) of `lm4k512l248krS2Vec`. -/
def lm4k512l248krS2Vec8 : List ℤ :=
  [Int.ofNat 0]
/-- Checkpoint fixed-point vector exiting `lm4k512l248krS2Segs` (`513` entries). -/
def lm4k512l248krS2Vec : List ℤ :=
  lm4k512l248krS2Vec0 ++
  (lm4k512l248krS2Vec1 ++
  (lm4k512l248krS2Vec2 ++
  (lm4k512l248krS2Vec3 ++
  (lm4k512l248krS2Vec4 ++
  (lm4k512l248krS2Vec5 ++
  (lm4k512l248krS2Vec6 ++
  (lm4k512l248krS2Vec7 ++
  (lm4k512l248krS2Vec8))))))))

end

public section

open QuantumComputation.Specs.DickeSol

private def s2NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem s2NatEq_eq {x y : ℕ} (h : s2NatEq x y = true) : x = y := by
  unfold s2NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def s2IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat x, Int.ofNat y => s2NatEq x y
  | Int.negSucc x, Int.negSucc y => s2NatEq x y
  | _, _ => false
private theorem s2IntEq_eq {a b : ℤ} (h : s2IntEq a b = true) : a = b := by
  cases a with
  | ofNat _ =>
    cases b with
    | ofNat _ => exact congrArg Int.ofNat (s2NatEq_eq h)
    | negSucc _ => cases h
  | negSucc _ =>
    cases b with
    | ofNat _ => cases h
    | negSucc _ => exact congrArg Int.negSucc (s2NatEq_eq h)
private def s2IntListEq (xs ys : List ℤ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (s2IntEq x y) (s2IntListEq xr yr) false
  | _, _ => false
private theorem s2IntListEq_eq {xs ys : List ℤ} (h : s2IntListEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [s2IntListEq] at h
      cases hxy : s2IntEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (s2IntEq_eq hxy) (ih h)
private def s2StateAt (st : ℕ × ℕ × ℕ × List ℤ) (l d p : ℕ) (v : List ℤ) : Bool :=
  match st with
  | (ls, ds, ps, vs) =>
    Bool.and (s2NatEq ls l)
      (Bool.and (s2NatEq ds d) (Bool.and (s2NatEq ps p) (s2IntListEq vs v)))
private theorem s2StateAt_eq {st : ℕ × ℕ × ℕ × List ℤ} {l d p : ℕ} {v : List ℤ}
    (h : s2StateAt st l d p v = true) : st = (l, d, p, v) := by
  rcases st with ⟨ls, ds, ps, vs⟩
  unfold s2StateAt at h; dsimp only at h; simp only [Bool.and_eq_true] at h
  rcases h with ⟨hl, ⟨hd, ⟨hp, hv⟩⟩⟩
  rw [s2NatEq_eq hl, s2NatEq_eq hd, s2NatEq_eq hp, s2IntListEq_eq hv]
private abbrev s2P : ℕ → ℤ := Int.ofNat
private abbrev s2N : ℕ → ℤ := Int.negSucc
private def s2RunAt (c : List Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (l1 d1 p1 : ℕ) (v1 : List ℤ) : Bool :=
  s2StateAt (rkm128kRunSegs 4 248 512 c l0 d0 p0 v0) l1 d1 p1 v1
private theorem s2RunLast {c : List Rkm128kSeg} {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ}
    (h : s2RunAt c l0 d0 p0 v0 l1 d1 p1 v1 = true) :
    rkm128kRunSegs 4 248 512 c l0 d0 p0 v0 = (l1, d1, p1, v1) := s2StateAt_eq h
private theorem s2RunStep {c rest : List Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 l2 d2 p2 : ℕ} {v0 v1 v2 : List ℤ}
    (h1 : s2RunAt c l0 d0 p0 v0 l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 4 248 512 rest l1 d1 p1 v1 = (l2, d2, p2, v2)) :
    rkm128kRunSegs 4 248 512 (c ++ rest) l0 d0 p0 v0 = (l2, d2, p2, v2) := by
  unfold s2RunAt at h1; rw [rkm128kRunSegs_append]; dsimp only
  rw [s2StateAt_eq h1]; exact h2
private def s2Take (n : ℕ) (xs : List Rkm128kSeg) : List Rkm128kSeg :=
  match n with
  | 0 => []
  | k + 1 =>
    match xs with
    | [] => []
    | x :: xr => x :: s2Take k xr
private def s2Drop (n : ℕ) (xs : List Rkm128kSeg) : List Rkm128kSeg :=
  match n with
  | 0 => xs
  | k + 1 =>
    match xs with
    | [] => []
    | _ :: xr => s2Drop k xr
private theorem s2Take_drop (n : ℕ) (xs : List Rkm128kSeg) :
    s2Take n xs ++ s2Drop n xs = xs := by
  induction n generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xr => exact congrArg (List.cons x) (ih xr)
private theorem s2RunStepTd {xs : List Rkm128kSeg} {n : ℕ}
    {l0 d0 p0 l1 d1 p1 l2 d2 p2 : ℕ} {v0 v1 v2 : List ℤ}
    (h1 : s2RunAt (s2Take n xs) l0 d0 p0 v0 l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 4 248 512 (s2Drop n xs) l1 d1 p1 v1 = (l2, d2, p2, v2)) :
    rkm128kRunSegs 4 248 512 xs l0 d0 p0 v0 = (l2, d2, p2, v2) := by
  rw [← s2Take_drop n xs]; exact s2RunStep h1 h2
private def s2Rem0 : List Rkm128kSeg := lm4k512l248krS2Segs
private def s2Chk0 : List Rkm128kSeg := s2Take 1 s2Rem0
private def s2Rem1 : List Rkm128kSeg := s2Drop 1 s2Rem0
private def s2St0VecS0 : List ℤ :=
  [s2N 128677187, s2N 128170603, s2N 41357099, s2P 64664026, s2P 240016623, s2N 171072654,
   s2N 503385467, s2N 155940928, s2N 736048767, s2N 1306927207, s2P 133306657, s2P 218712297,
   s2P 424598705, s2P 1420485827, s2P 2624463169, s2P 2391606147, s2P 928694106, s2P 105009783,
   s2N 500879105, s2P 1874363772, s2P 2648479128, s2N 3420653965, s2N 1189098141,
   s2P 544838390, s2N 5095365075, s2P 4095123383, s2N 5570147959, s2P 5422741757,
   s2N 6298988829, s2N 3916923028, s2P 1665591200, s2P 11197018319, s2P 3064976366,
   s2N 5058394239, s2N 3118254382, s2N 3362101422, s2P 10210074595, s2N 1708225414,
   s2N 20662590245, s2N 13289397708, s2N 10579559824, s2P 2742954566, s2P 6683096114,
   s2N 13523905858, s2N 7955132896, s2P 24661172554, s2P 48946801309, s2P 6162370816,
   s2P 23511496700, s2N 3665577943, s2P 32588936702, s2P 10130018151, s2P 21280141904,
   s2P 11624194370, s2P 1132265517, s2P 47394042761, s2P 27801797240, s2P 37723166370,
   s2N 30028080167, s2N 9177044725, s2N 47511605998, s2N 51036672863, s2N 15568038885,
   s2N 16714090713]
private def s2St0VecS1 : List ℤ :=
  [s2P 26026709344, s2P 18593165331, s2N 18218826430, s2N 33224636708, s2N 2830523986,
   s2P 24969580827, s2P 24064192086, s2P 75304613615, s2N 38255054494, s2N 14441034620,
   s2N 110186893570, s2N 47273310876, s2N 12066773313, s2N 32065447194, s2P 52784523338,
   s2P 80288359195, s2P 114898223854, s2P 337975822, s2N 45325413029, s2N 59568483400,
   s2P 3577494285, s2P 304398347503, s2P 70161556671, s2N 7683235111, s2P 104943379163,
   s2P 18054355134, s2N 172172137803, s2N 210302481457, s2P 35647465861, s2N 4371721589,
   s2N 11274348867, s2N 84386733784, s2N 111832305192, s2N 1479107967, s2P 52478128122,
   s2P 81226006488, s2P 90495687961, s2P 51791995670, s2N 104798568199, s2P 27125336085,
   s2P 108823002620, s2P 149332324039, s2N 97029311771, s2N 288638238619, s2N 12551284724,
   s2N 36322462102, s2P 19392577246, s2N 54179304468, s2N 339276237076, s2N 505239015166,
   s2N 401746031422, s2N 216721349888, s2N 3492969005, s2P 293463183738, s2P 623330232261,
   s2P 903895204028, s2P 960427196354, s2P 458591531376, s2P 575733844587, s2P 1009531554753,
   s2P 1140222400303, s2P 2189392523999, s2P 3548050027355, s2P 1901412124557]
private def s2St0VecS2 : List ℤ :=
  [s2P 628968681148, s2N 77165767401, s2P 305165033524, s2P 283963062932, s2N 174814290460,
   s2P 673595825578, s2P 996798928599, s2P 872234961880, s2P 959944151368, s2P 903900683103,
   s2N 582817915697, s2N 912114851346, s2N 371388497413, s2P 152063705852, s2P 2475630398664,
   s2P 2216720261112, s2N 2130096426294, s2N 737755550693, s2P 2949339652397,
   s2N 1290660766798, s2N 2848517458223, s2N 2418428100569, s2P 108293010985, s2P 689200775386,
   s2P 2358975849933, s2P 2947197108498, s2P 1362298353564, s2P 1631244116575,
   s2P 2350230142198, s2N 243397049655, s2P 1094643163427, s2N 402159388831, s2N 730502055181,
   s2N 649655335987, s2N 1487372465497, s2P 286810565357, s2P 634015871647, s2P 883041303210,
   s2N 1002926363848, s2P 878264478792, s2P 56371129288, s2N 887847549377, s2N 1456246382481,
   s2P 213168587515, s2P 811102270325, s2P 564580152997, s2P 79058906346, s2P 1444577570803,
   s2P 606495898438, s2P 1954427026843, s2N 1582236444246, s2P 37817857312, s2N 1447273763431,
   s2P 409106172361, s2P 338420798607, s2P 591991927822, s2N 1114623767804, s2N 874714307957,
   s2N 2199725065916, s2N 3012558234001, s2P 1201255118555, s2P 296567069898,
   s2N 2339052887170, s2P 1163663726478]
private def s2St0VecS3 : List ℤ :=
  [s2P 756453696340, s2P 495171541496, s2P 1268418099666, s2N 349550261855, s2P 950026334196,
   s2P 245028851801, s2N 875112158158, s2N 1714086672211, s2N 3628252326045, s2N 3722785546814,
   s2N 7399947199704, s2N 6956038505582, s2N 7656894629814, s2N 4796782045640,
   s2N 160150559087, s2N 622839678588, s2N 840194923877, s2N 1547526111481, s2P 432835114512,
   s2N 1474242797171, s2N 1373715048598, s2N 664091792547, s2P 156997036234, s2P 2186933977374,
   s2P 136927525056, s2P 1296329593881, s2N 2712034240865, s2P 1407983283048,
   s2P 1291405712443, s2N 245746630221, s2N 445668159742, s2N 680015653425, s2N 1024487109183,
   s2P 1446954309952, s2P 1758104904755, s2P 1123741664803, s2P 2593150550389,
   s2P 1503879915024, s2P 113727428143, s2N 4563665477567, s2N 1489027155950,
   s2N 1443792317455, s2P 1158022575423, s2N 2119918756566, s2N 2309240934119,
   s2P 1153782910093, s2N 969056355179, s2N 2744286645311, s2P 4005584791193,
   s2N 1926918175013, s2N 3831308636134, s2N 1593468406234, s2P 2795983045687,
   s2P 5003815896798, s2P 7094107789024, s2P 532526901605, s2N 2883644769059,
   s2P 3868639058301, s2P 615769783017, s2P 1984531850713, s2P 116526344374, s2P 3368039746507,
   s2P 7740111567312, s2P 20502534670573]
private def s2St0VecS4 : List ℤ :=
  [s2P 13025458328598, s2N 8527458272009, s2N 3377711468056, s2P 8830458418114,
   s2P 3678041989991, s2N 2583962268994, s2N 1363981574396, s2P 6040362268903,
   s2P 3808234602402, s2P 4922901587774, s2N 3763908845639, s2N 2835588929510,
   s2P 1618106724917, s2N 3462382723131, s2N 8585149462092, s2P 1685520461451,
   s2N 1666694378761, s2N 691051733201, s2P 4576970979032, s2P 2305216666768,
   s2P 7156250884570, s2N 42551581275, s2P 5800515021248, s2P 2758407726187, s2P 934097417625,
   s2P 3034637158148, s2P 2095785524570, s2P 1361785670053, s2P 2350220223509,
   s2N 1816614645411, s2N 4425064460291, s2N 8154823596006, s2N 943287580061,
   s2P 1218066385629, s2P 6592866116769, s2P 352703945972, s2P 1547232537035,
   s2P 11873304201165, s2P 1901124780809, s2P 10294764532663, s2P 346121065184,
   s2P 2355874728344, s2P 9143405350363, s2N 1735184860223, s2N 1931696592513,
   s2N 11619211937816, s2N 4967774370203, s2N 8346409674218, s2P 2039710176715,
   s2P 2058856751800, s2N 268293359152, s2P 10881179700210, s2N 4119688235086,
   s2P 4926299550843, s2N 219732501452, s2P 1335306728558, s2P 376740883873, s2P 2776750179658,
   s2N 9764723497280, s2P 4379709811399, s2P 1458766882280, s2P 8090389693921,
   s2N 172373372946, s2N 3085941308252]
private def s2St0VecS5 : List ℤ :=
  [s2N 4719081726821, s2N 1266421614138, s2N 1877002237544, s2P 5742138408799,
   s2N 8951432970546, s2N 10438592246888, s2N 10740347723658, s2N 2488266297792,
   s2P 3335113061412, s2P 1576104706912, s2P 3908445816270, s2N 1141672953066,
   s2P 5051407854569, s2N 4174911325251, s2P 3504150684993, s2P 7875346743194,
   s2P 3094873503806, s2P 6623726418999, s2P 11228367965531, s2P 1571700097481,
   s2P 26116331358708, s2P 69908102899181, s2P 124446159091602, s2P 182942176091974,
   s2P 238427604547305, s2P 284968692960115, s2P 318537999084619, s2P 337155194854345,
   s2P 340696077574872, s2P 330654671777856, s2P 309673702337978, s2P 280871881099937,
   s2P 247313649755823, s2P 211774163860755, s2P 176619555009215, s2P 143679360498596,
   s2P 114164456031152, s2P 88706295954116, s2P 67477976531433, s2P 50314940436388,
   s2P 36815475382781, s2P 26439596277380, s2P 18610452249792, s2P 12797853320815,
   s2P 8560356879886, s2P 5545110805971, s2P 3467115518639, s2P 2089939709285,
   s2P 1216392365801, s2P 686796965720, s2P 379137302712, s2P 206787143321, s2N 112784237264,
   s2P 62224077959, s2P 34972742604, s2P 19997630616, s2P 11511510427, s2P 6566714616,
   s2P 3656205999, s2P 1966056467, s2P 1016481552, s2P 506016579, s2P 244139126, s2P 115359215]
private def s2St0VecS6 : List ℤ :=
  [s2P 54045138, s2P 25386153, s2N 12036884, s2P 5765046, s2P 2776424, s2P 1334850, s2P 635868,
   s2P 298152, s2P 136890, s2P 61297, s2N 26710, s2P 11330, s2P 4687, s2P 1892, s2P 741,
   s2P 278, s2P 97, s2P 30, s2P 7, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St0VecS7 : List ℤ :=
  [s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St0VecS8 : List ℤ :=
  [s2P 0]
private def s2St0Vec : List ℤ :=
  s2St0VecS0 ++
  (s2St0VecS1 ++
  (s2St0VecS2 ++
  (s2St0VecS3 ++
  (s2St0VecS4 ++
  (s2St0VecS5 ++
  (s2St0VecS6 ++
  (s2St0VecS7 ++
  (s2St0VecS8))))))))
private def s2Chk1 : List Rkm128kSeg := s2Take 1 s2Rem1
private def s2Rem2 : List Rkm128kSeg := s2Drop 1 s2Rem1
private def s2St1VecS0 : List ℤ :=
  [s2N 55190788, s2N 122322916, s2P 61082667, s2N 159811213, s2N 132445169, s2P 329840702,
   s2P 301750024, s2N 593273273, s2P 197711623, s2P 130732799, s2N 705997028, s2P 1013957152,
   s2P 658685037, s2N 33090024, s2P 655220877, s2P 384454087, s2N 1324069197, s2P 491902100,
   s2P 2859370655, s2P 5517275029, s2P 5958080594, s2P 6064180519, s2P 3471436364,
   s2P 5096696124, s2N 516001651, s2P 510264478, s2P 131030156, s2P 120338833, s2P 2651606412,
   s2P 5950681093, s2P 6592271957, s2N 1411657211, s2N 5486485477, s2N 2350814095,
   s2P 9051723445, s2P 4774580019, s2N 14193929213, s2P 2177150545, s2N 2048316074,
   s2P 8316657199, s2P 10089573819, s2N 6352528542, s2P 28397559536, s2P 27760124994,
   s2P 16569370154, s2N 9764170207, s2P 6010671418, s2P 7331531763, s2N 37488706420,
   s2P 2899138772, s2N 15710365827, s2N 33325223603, s2N 13837957065, s2N 26236824839,
   s2N 13371846603, s2P 3851450662, s2P 43407374360, s2N 17466417582, s2P 4400601176,
   s2N 8230008455, s2N 4060047557, s2P 28775940265, s2P 27781013747, s2P 59917157387]
private def s2St1VecS1 : List ℤ :=
  [s2N 14459328054, s2P 59505570226, s2P 40832693301, s2P 36756037795, s2P 43278667952,
   s2P 54089848458, s2P 29749652694, s2P 13059395806, s2N 18914933157, s2N 9325438382,
   s2P 38447452629, s2N 19889118140, s2N 32405766351, s2N 127642036119, s2N 18301838157,
   s2N 32658337841, s2N 35030078546, s2N 110069984126, s2N 1538442120, s2N 51976040152,
   s2N 122016087935, s2N 91168347979, s2N 203009442761, s2N 162152811131, s2N 87053934304,
   s2N 40949534926, s2N 23142619471, s2P 18388076512, s2P 15381425726, s2P 89884898591,
   s2N 132002621787, s2N 229016293385, s2N 49238899290, s2P 97432400594, s2N 54342167733,
   s2N 113877284531, s2P 31161719462, s2P 71282955808, s2N 22494820408, s2P 19329614311,
   s2N 209422295709, s2N 103593934819, s2P 151989137088, s2N 116802534982, s2N 21862542797,
   s2N 65244379909, s2N 7202010513, s2P 39407480481, s2P 233929897024, s2P 62166904733,
   s2N 77036983166, s2N 151214284000, s2N 94709622913, s2N 122604789054, s2N 512751987804,
   s2N 415901126870, s2N 133549100303, s2P 110134488302, s2P 696457535689, s2P 576170526209,
   s2P 310048734147, s2N 42516404803, s2N 173681012121, s2P 399931493705]
private def s2St1VecS2 : List ℤ :=
  [s2P 1310556916738, s2P 1127786157059, s2P 373823283771, s2P 435687196518, s2P 1134036773710,
   s2P 1641839470946, s2P 2185113856194, s2P 2932565815108, s2P 1840593346618,
   s2N 699620156081, s2N 2296135367313, s2N 1038524046556, s2P 315032668745, s2N 1313838983541,
   s2N 773639525602, s2P 551388343384, s2P 3019200414152, s2P 2833264355190, s2P 1094893736452,
   s2P 2580047691870, s2P 1466914837714, s2N 339802513007, s2P 482169237315, s2N 475504103517,
   s2P 657710911039, s2P 1871401028808, s2P 1500748181714, s2P 1054059073167,
   s2N 1497172637134, s2N 1674564819780, s2N 2544771960891, s2N 697175217886, s2N 167856974010,
   s2P 639319371675, s2P 1855055034658, s2P 2593383556892, s2P 1032901625865,
   s2N 2012299417452, s2N 1612644566717, s2N 2663101678754, s2N 1445162409284,
   s2P 325220259450, s2N 1016955818357, s2N 85842148704, s2N 1084943743665, s2P 404659035193,
   s2N 574908371432, s2N 1244282319080, s2N 42137851745, s2N 905404382789, s2P 62354938043,
   s2P 825801290366, s2P 258445514510, s2N 567083877074, s2N 1947107601202, s2N 1181550658239,
   s2N 2427298584206, s2N 539005497223, s2P 1956036195647, s2P 882916420647, s2P 1676783561250,
   s2P 785629389799, s2P 115509049943, s2P 2125652116568]
private def s2St1VecS3 : List ℤ :=
  [s2P 263668833980, s2N 288915504087, s2N 1624378159460, s2N 1119250838923, s2P 393585968541,
   s2P 2496184006129, s2P 479693027182, s2N 1003618905159, s2N 96059761860, s2N 40628784364,
   s2N 444254633325, s2P 282046347404, s2P 512273035467, s2P 2443975685862, s2N 1234479596631,
   s2N 876006534450, s2N 242766218816, s2P 1609427317184, s2P 3487024772868, s2P 6430006876740,
   s2P 6722190653389, s2P 7453332106947, s2P 5664698059677, s2N 3456561915956,
   s2N 3689076795071, s2N 1587347288995, s2P 999179385072, s2P 2036139430921,
   s2N 1472569915211, s2N 2804242788223, s2N 423693553952, s2N 394895681019, s2N 1939666186244,
   s2P 628287166110, s2P 947321174116, s2P 961026230967, s2N 1139376885442, s2P 58331569819,
   s2N 941348859791, s2P 2359754164872, s2P 2564615361161, s2P 1833411821159,
   s2P 3317405054014, s2P 2625696998029, s2P 4386969150814, s2P 656687865616,
   s2P 1276535078896, s2P 2471334382392, s2P 4418943288185, s2P 531767521662,
   s2N 1867641218246, s2P 3429424396, s2P 839242147787, s2N 2406849383588, s2N 3816914879037,
   s2P 1402522549779, s2P 5142463033816, s2P 3339096047720, s2P 4052752040836,
   s2N 1110032684217, s2N 5368294165600, s2N 5465064778956, s2N 7148217549121,
   s2P 990070311301]
private def s2St1VecS4 : List ℤ :=
  [s2P 5276942172317, s2P 10890545512368, s2P 9081075439516, s2N 6957466845121,
   s2N 9966704646612, s2N 2412424157477, s2P 8935040262960, s2P 14631657078060,
   s2P 6579784850836, s2N 1367469117032, s2P 13322194934131, s2P 2622679460935,
   s2P 712213406681, s2P 1491463242825, s2N 3105046032576, s2N 3241416460379, s2P 880053403683,
   s2N 4628735459792, s2P 4030200828099, s2N 612598329624, s2P 1760434316280,
   s2P 2323106177479, s2P 2372030943236, s2N 5578148078060, s2P 1736235520501,
   s2P 3248919370547, s2N 360236650106, s2N 3820359808216, s2P 1081830143214,
   s2P 8562062758636, s2P 1017067514099, s2P 6982467002034, s2N 4304519004901,
   s2P 4773329292032, s2N 7707920276574, s2N 2343982815418, s2P 8181847397294,
   s2P 2351227929599, s2P 3902069754018, s2P 5577932217611, s2P 1300692818451,
   s2N 1556251554032, s2N 8993831081406, s2N 6865688635000, s2N 1026861563378,
   s2P 9105917887921, s2P 4621982362132, s2N 2683746040153, s2N 2974641300215,
   s2P 12779838773591, s2P 1624700978716, s2N 9847488412870, s2N 3151959404191,
   s2N 4688342329739, s2P 6757409067376, s2N 6794382348518, s2N 6828961617962,
   s2N 1801861588340, s2N 520255138381, s2P 5786626613260, s2N 3533340416074,
   s2P 3303619307557, s2P 6012334036869, s2N 1803954163692]
private def s2St1VecS5 : List ℤ :=
  [s2P 1347900390054, s2N 5125636810705, s2N 1290392322580, s2N 2694118671853,
   s2P 9325904134165, s2P 3574172045268, s2P 101057057267, s2N 4655080033199,
   s2N 4264360786624, s2N 4839885890365, s2P 6034899732003, s2P 7832129234837,
   s2P 2668336468974, s2N 9107456195298, s2N 12331811475383, s2N 1411450536509,
   s2P 491549592843, s2P 2024808096884, s2P 2498150969380, s2N 4071147012644,
   s2N 1915559452880, s2N 4219278359045, s2P 2942418800125, s2P 11098858139910,
   s2P 10226883853716, s2P 232620885994, s2P 9942845157987, s2P 9570297839758,
   s2P 8088876467988, s2P 43974169631084, s2P 94286975760190, s2P 152537340215420,
   s2P 211382849229890, s2P 264000082140849, s2P 305099452339967, s2P 331533496182929,
   s2P 342366840648728, s2P 338498924830172, s2P 322109883711169, s2P 296134980641357,
   s2P 263790744625671, s2P 228212752978197, s2P 192062786735829, s2P 157571889158030,
   s2P 126032077529787, s2P 98682970168294, s2P 75393874247851, s2P 56625933553907,
   s2P 41633969934069, s2P 29915143753070, s2P 21167452444410, s2P 14621303578989,
   s2P 9737022054315, s2P 6317302972234, s2P 4053374795751, s2P 2535819042581,
   s2P 1492758592870, s2P 807349400751, s2P 404134368947, s2P 195609024444, s2P 98064896751,
   s2P 53628793108, s2P 31705579649, s2P 19332193826]
private def s2St1VecS6 : List ℤ :=
  [s2P 11693040986, s2P 6866948911, s2P 3884523853, s2P 2124605745, s2P 1130687085,
   s2P 583288952, s2P 287229910, s2P 133165845, s2P 58247954, s2P 24621192, s2P 10504511,
   s2P 4739213, s2P 2294101, s2P 1149892, s2P 564757, s2P 261838, s2P 113706, s2P 47072,
   s2P 19216, s2P 7989, s2P 3416, s2P 1477, s2N 627, s2P 252, s2P 92, s2P 30, s2P 7, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St1VecS7 : List ℤ :=
  [s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St1VecS8 : List ℤ :=
  [s2P 0]
private def s2St1Vec : List ℤ :=
  s2St1VecS0 ++
  (s2St1VecS1 ++
  (s2St1VecS2 ++
  (s2St1VecS3 ++
  (s2St1VecS4 ++
  (s2St1VecS5 ++
  (s2St1VecS6 ++
  (s2St1VecS7 ++
  (s2St1VecS8))))))))
private def s2Chk2 : List Rkm128kSeg := s2Take 1 s2Rem2
private def s2Rem3 : List Rkm128kSeg := s2Drop 1 s2Rem2
private def s2St2VecS0 : List ℤ :=
  [s2P 33375482, s2P 155586912, s2P 47676360, s2N 61917106, s2P 80764319, s2N 571440447,
   s2P 14223234, s2P 821437892, s2P 552152471, s2P 9392129, s2N 544341597, s2N 301535039,
   s2P 921946804, s2P 771261408, s2N 36741461, s2N 121903242, s2N 12814051, s2P 2083517194,
   s2P 758505324, s2N 1068167772, s2N 2595927874, s2P 598194561, s2P 2365504085,
   s2N 2542843619, s2N 4610857600, s2N 5327824073, s2N 6793462128, s2P 3776824664,
   s2P 3156658157, s2P 4287963221, s2N 2458236227, s2N 4618223300, s2N 9736910733,
   s2N 3879366138, s2N 17808137105, s2N 5534595731, s2P 5686826152, s2P 9747249373,
   s2P 2187539015, s2N 10706696952, s2N 152533009, s2P 1292959110, s2N 21889653487,
   s2N 23566891445, s2P 3493959636, s2P 29541216835, s2N 16090715873, s2P 7212667793,
   s2N 17607789108, s2N 7391606448, s2P 40337717869, s2P 4633977545, s2P 9136158558,
   s2P 19551197906, s2P 30043049710, s2N 10743017379, s2N 22878060721, s2N 15889718965,
   s2N 52404324270, s2N 26543125398, s2N 15198983719, s2N 23329742751, s2N 5915369969,
   s2N 33267918038]
private def s2St2VecS1 : List ℤ :=
  [s2P 1793000478, s2N 28862389295, s2N 10492094917, s2P 19223770781, s2P 46664521750,
   s2P 19251334258, s2N 51395815819, s2N 7014897340, s2P 52402340614, s2P 7560983249,
   s2P 36100431844, s2N 45308048246, s2N 66920915410, s2N 94335786932, s2N 60529074325,
   s2N 7810670542, s2N 70794119914, s2N 24656190365, s2P 19287669999, s2P 8127100329,
   s2N 72414611483, s2P 8255651712, s2P 53801237062, s2N 59165166310, s2N 48528897227,
   s2P 60968336579, s2N 29715805845, s2N 37542803228, s2N 86077447617, s2N 178982093772,
   s2N 146896964850, s2P 15185348994, s2P 213960021788, s2P 292111299632, s2P 113497503004,
   s2N 9032222086, s2N 97068023285, s2N 33292298738, s2N 139408292762, s2N 84109445359,
   s2P 77058554739, s2N 107767773348, s2N 172709656388, s2P 2584993312, s2N 2324889232,
   s2P 82854020747, s2P 4206731392, s2N 73936421825, s2N 5756839083, s2P 209501310167,
   s2P 122492282251, s2P 62195497848, s2P 194646460822, s2P 145436200830, s2P 7695459059,
   s2N 34511263462, s2P 150676169984, s2P 36446287150, s2P 75104265466, s2P 162900776616,
   s2P 113087202242, s2P 38730368864, s2P 212466353636, s2P 296672359499]
private def s2St2VecS2 : List ℤ :=
  [s2P 791038229146, s2P 700718786058, s2P 635001881366, s2P 631017809762, s2P 620055264748,
   s2P 687606101448, s2P 157337582980, s2N 529730303258, s2N 335073851961, s2N 1125375441760,
   s2N 1288330295889, s2N 581662765546, s2P 399542872796, s2N 1220504260707, s2N 2843991276052,
   s2N 3894414899160, s2N 1283641403614, s2P 1743430332084, s2P 843598642814, s2P 948025950325,
   s2P 982926716416, s2N 1124614094889, s2N 1705445609680, s2N 1052439199491, s2N 89525645729,
   s2P 539374185563, s2N 1764524934915, s2N 2064917987156, s2N 2985304536825,
   s2P 1756793798448, s2P 1291322526052, s2P 310421780624, s2P 1711268733482,
   s2P 1666650946483, s2P 1486081878114, s2P 1827763066590, s2P 1293129376706,
   s2N 297357070588, s2N 35504882463, s2N 2166954181722, s2N 1978004846907, s2P 1862707430982,
   s2N 1038838503267, s2N 2326259199697, s2N 2338263702749, s2P 1689168547356,
   s2P 236103438946, s2P 742296675156, s2N 1105138709223, s2N 2181620505836, s2N 412631103554,
   s2P 1145156226077, s2N 1739823351804, s2N 842749986258, s2N 876839132468, s2P 170185218759,
   s2P 732664178825, s2N 1060838244536, s2N 969442249219, s2P 164868002850, s2N 3120454179,
   s2P 1222971702111, s2P 867539701246, s2P 1199811738283]
private def s2St2VecS3 : List ℤ :=
  [s2N 2185179762926, s2N 1639115839225, s2N 2222528280046, s2N 1232957533841, s2N 74393642649,
   s2P 183141307672, s2P 181188571799, s2N 1990978913503, s2N 3026595021411, s2N 971092848953,
   s2N 1234258568521, s2P 736104001514, s2P 597443595636, s2N 1651319551931, s2N 1500574132361,
   s2N 691331714264, s2P 246459125932, s2N 1134405521716, s2N 1969080892203, s2N 1208581505912,
   s2P 1616520415346, s2N 1190716501324, s2P 243743000444, s2N 914385552087, s2N 581902184815,
   s2N 253886517356, s2P 2754807491015, s2P 1772603553333, s2N 2918668323120,
   s2N 10170587512243, s2N 8881072894576, s2N 3809195041518, s2P 2717577173455,
   s2N 559496305394, s2P 1039970528133, s2N 788235827818, s2N 501847450748, s2P 202340692071,
   s2P 130479821728, s2N 1583707215304, s2N 2241545899830, s2P 1400732871833, s2P 334554531019,
   s2N 1303462122852, s2N 481774280106, s2P 1550889987177, s2N 525475236440, s2N 464271118852,
   s2N 393406385259, s2N 1674376115796, s2N 3262143073164, s2N 6004613373858, s2P 745396700169,
   s2P 2399428945004, s2N 2915843335134, s2N 3374024541723, s2N 3343743428718,
   s2N 324129860076, s2N 4078392443543, s2N 2128774414219, s2N 1140279397045, s2N 262148952368,
   s2P 3227696949394, s2N 5914910545843]
private def s2St2VecS4 : List ℤ :=
  [s2N 4116002252931, s2P 2414227386921, s2P 6250203150383, s2P 5330739365815,
   s2N 2762569763138, s2N 2601539537773, s2N 9909399337326, s2N 18840871218473,
   s2N 5157027721498, s2N 9867609388825, s2N 9916252062501, s2N 558214418345,
   s2N 4614519317822, s2P 4103747779392, s2P 2070925940690, s2P 12733094110, s2N 5345864164296,
   s2N 8154363666253, s2P 4443051658755, s2P 9885610856339, s2N 5568010275538,
   s2N 7658248310197, s2N 5385409079887, s2N 7153065651927, s2P 3216644197349,
   s2P 3978775530465, s2N 2181296433541, s2N 368860141031, s2N 6578240433462,
   s2N 2875705266038, s2N 2873377326189, s2P 6491015055489, s2N 691890816375, s2P 259016238212,
   s2P 73920420095, s2P 182835934213, s2N 4155753996765, s2N 1906987752101, s2N 4375501692287,
   s2N 7812721868844, s2N 1511126120114, s2P 649094948181, s2P 888804832175, s2P 4303788661008,
   s2P 6175135178438, s2N 8464845818378, s2N 4365740705767, s2P 14327219005924,
   s2P 6657170377769, s2P 2319087649174, s2P 12384853521199, s2P 1869080363963,
   s2P 1885462335977, s2P 4719275467739, s2P 1887882391421, s2P 1927398609619,
   s2N 12948243322507, s2N 2945095744836, s2P 1320712612849, s2P 4031247081613,
   s2P 4080714311838, s2P 2064117853513, s2N 2703067935156, s2P 3454135476902]
private def s2St2VecS5 : List ℤ :=
  [s2P 3348907233427, s2P 5210458309393, s2N 225987702744, s2N 2566979588083,
   s2N 2256405278216, s2P 4335944441528, s2N 4772387094152, s2N 3958347419239,
   s2P 2376900678231, s2P 4181654075406, s2P 1534796749084, s2N 3845368402514,
   s2P 8237191666970, s2N 8082253162708, s2P 70688701368, s2P 8701650975594, s2P 5864623711249,
   s2P 427818384683, s2P 9922012748916, s2P 4009190073587, s2P 3884048826533, s2N 185815796003,
   s2N 10984977132776, s2N 7437940298090, s2N 6663775953000, s2P 2423585086711,
   s2N 5729922095179, s2P 3148906901928, s2N 905309769788, s2N 3365158258498,
   s2N 1219517275049, s2P 7570368756223, s2P 13396773525948, s2P 8840005761624,
   s2N 2872709752313, s2P 10958520969491, s2P 5449723405412, s2P 19065672508127,
   s2P 61329636053615, s2P 116561116146786, s2P 176977695603109, s2P 234996536187411,
   s2P 284236426665536, s2P 319908226482922, s2P 339987522169950, s2P 344317110541398,
   s2P 334231910590596, s2P 312603539413491, s2P 282735341103260, s2P 247794736948254,
   s2P 210926701549605, s2P 174810504394073, s2P 141240287250495, s2P 111348794625516,
   s2P 85823639588165, s2P 64811226469510, s2P 47954758558577, s2P 34697298807885,
   s2P 24515973914935, s2P 16929801928584, s2P 11441455346557, s2P 7556226360961,
   s2P 4849309426792, s2P 3000610254228]
private def s2St2VecS6 : List ℤ :=
  [s2P 1778875178939, s2P 1008688527612, s2P 549685146865, s2P 291277984215, s2P 152723574488,
   s2P 80743939516, s2P 43622780532, s2P 24137319033, s2P 13567643567, s2P 7649794604,
   s2P 4274990810, s2P 2345868836, s2P 1255074643, s2P 651112265, s2P 326314651, s2P 157785115,
   s2P 73773420, s2P 33568449, s2P 15016749, s2P 6682935, s2P 2986709, s2P 1343460, s2P 605199,
   s2P 271167, s2P 120141, s2P 52207, s2P 21977, s2P 8860, s2P 3409, s2P 1264, s2N 457,
   s2P 165, s2N 54, s2P 14, s2P 4, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St2VecS7 : List ℤ :=
  [s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St2VecS8 : List ℤ :=
  [s2P 0]
private def s2St2Vec : List ℤ :=
  s2St2VecS0 ++
  (s2St2VecS1 ++
  (s2St2VecS2 ++
  (s2St2VecS3 ++
  (s2St2VecS4 ++
  (s2St2VecS5 ++
  (s2St2VecS6 ++
  (s2St2VecS7 ++
  (s2St2VecS8))))))))
private def s2Chk3 : List Rkm128kSeg := s2Take 1 s2Rem3
private def s2Rem4 : List Rkm128kSeg := s2Drop 1 s2Rem3
private def s2St3VecS0 : List ℤ :=
  [s2N 29262340, s2P 36936344, s2N 258006505, s2N 173306685, s2N 149088112, s2N 322122273,
   s2N 328123394, s2P 538314825, s2P 99543602, s2P 223741560, s2P 821591057, s2P 791252258,
   s2P 644454835, s2N 128623780, s2N 629921091, s2P 878018462, s2N 853663384, s2P 259458832,
   s2P 429076520, s2N 1187969934, s2P 1552964586, s2N 4317576121, s2P 3167953778,
   s2P 768597522, s2N 2595478652, s2P 1303778739, s2N 371410818, s2N 4567909190,
   s2N 6815981616, s2N 1770226301, s2N 9471228514, s2N 4939996133, s2P 5740775648,
   s2P 1850397653, s2P 1075381005, s2P 71819988, s2P 373330686, s2N 4087666829,
   s2N 18862962132, s2N 12324917592, s2N 19184542519, s2N 23911148307, s2N 6684746677,
   s2P 19959448579, s2P 28178050533, s2P 3389152492, s2N 1782418055, s2N 12729704636,
   s2N 26673898306, s2P 15289032456, s2P 12482045925, s2N 24272967929, s2P 24927660065,
   s2P 11239689761, s2N 16183201864, s2N 17407933059, s2P 15289703489, s2N 4360538291,
   s2P 24018065504, s2N 16106351758, s2N 20800323699, s2N 28244479986, s2P 1918729585,
   s2N 17599026284]
private def s2St3VecS1 : List ℤ :=
  [s2P 26458248005, s2P 35984635604, s2N 1524575678, s2P 70806642430, s2N 526776322,
   s2P 15180114687, s2P 36858365950, s2P 42591730920, s2N 47419398036, s2N 36088828250,
   s2N 15775174279, s2N 16779497691, s2N 1717907496, s2N 15774033043, s2P 33076176342,
   s2P 28326713541, s2P 85401013048, s2P 21223446043, s2N 74570780606, s2N 31651940813,
   s2N 35437237581, s2N 136204118788, s2N 45966549982, s2P 5238418688, s2P 61494666292,
   s2N 25839855063, s2P 39261223487, s2P 22368689121, s2P 29440290030, s2P 11370431740,
   s2N 19332251441, s2P 49100429131, s2P 2224957028, s2P 4167289365, s2P 97230356726,
   s2P 68543173398, s2P 287776458322, s2P 213878843509, s2P 82038413967, s2P 18349360921,
   s2N 94304151151, s2N 249407802363, s2N 173320244834, s2N 44260406023, s2N 257238401,
   s2N 125626219089, s2N 8673231884, s2P 36418800554, s2P 54227985870, s2N 243382791224,
   s2N 58176469469, s2N 56094355648, s2N 32685999884, s2N 121460569513, s2N 117528605318,
   s2P 110476732846, s2P 6964758283, s2N 27924837885, s2P 71233146633, s2P 201372180727,
   s2P 102828210449, s2P 76627955293, s2P 261944892365, s2P 155057675284]
private def s2St3VecS2 : List ℤ :=
  [s2P 193082274044, s2N 120690135424, s2N 231506272517, s2N 172465757653, s2P 193823055175,
   s2P 513065654762, s2P 252375252942, s2P 520960916522, s2P 118249667107, s2N 674087853359,
   s2N 521203352424, s2P 727501632849, s2P 946926714379, s2P 56770607929, s2N 1083984792833,
   s2N 2107120756582, s2N 1321625853214, s2N 1495752290476, s2N 1434385127431,
   s2N 1611302189840, s2P 36563453963, s2P 478183025894, s2N 1684699621143, s2N 3561286932748,
   s2N 2205997155552, s2N 1976541709465, s2P 614097545629, s2P 2108750751974,
   s2P 2011171958295, s2P 1501246714951, s2P 1566971211687, s2P 646757747456, s2P 514780028709,
   s2P 1425713043068, s2P 2044803328501, s2N 1829829073995, s2N 1740789819723,
   s2N 588741481787, s2N 1907580239287, s2P 563134283181, s2P 1609575762565, s2P 189755470301,
   s2N 85025427222, s2N 3928273155355, s2N 2424513777064, s2P 1281844974298, s2N 30419743210,
   s2N 1447613487099, s2P 657631940235, s2P 1184023468089, s2P 1433239507345,
   s2P 1968935904537, s2P 2645711209754, s2N 504999650632, s2P 315190707900, s2P 281162578759,
   s2N 1626132810343, s2N 197018384989, s2N 497536957142, s2N 916137090212, s2P 796081594373,
   s2N 939630795699, s2N 1062461234632, s2N 34773633775]
private def s2St3VecS3 : List ℤ :=
  [s2P 488415587708, s2P 652084836122, s2P 1039045980090, s2P 1724755018412, s2P 95020837667,
   s2N 332430283725, s2N 1133420542095, s2N 1769291189489, s2N 1123874792447,
   s2P 1231494916533, s2P 1147054932329, s2P 3044145916327, s2P 326603994063, s2P 763797747630,
   s2N 1357590827585, s2P 391911020299, s2P 2770444206097, s2P 2982878807334, s2P 282550210386,
   s2N 774377361028, s2P 604900438978, s2N 1825601814992, s2N 815283449385, s2N 1485997703382,
   s2N 384440264585, s2P 1615378175037, s2P 670423350189, s2N 1740120530050, s2N 2177917469979,
   s2N 1887767597982, s2N 1734141131590, s2N 2363549685714, s2N 5211515833300,
   s2N 154839955593, s2P 4201420326786, s2P 4751957749376, s2N 1274000084536,
   s2N 3968152191266, s2N 8308914261074, s2N 6177748619215, s2N 2080872168108,
   s2N 4047549584730, s2N 1702395664205, s2P 217802999305, s2P 681074307534, s2P 903091596872,
   s2N 2938697337346, s2N 1390431421874, s2P 651396219785, s2N 1718821569370, s2P 833355248970,
   s2N 989501239963, s2N 977132050237, s2N 5006652530947, s2N 2145110858688, s2N 2896821637744,
   s2N 411876397167, s2N 513458433335, s2N 5599988436628, s2N 1636252020827, s2P 276747099267,
   s2P 2622422236257, s2N 519853889226, s2N 4563869272730]
private def s2St3VecS4 : List ℤ :=
  [s2N 3973982460731, s2N 1819324329986, s2N 12239254709589, s2N 3074992262341,
   s2P 1740528333338, s2P 544649446207, s2N 1051050524747, s2N 4290380209655,
   s2N 5087543265098, s2N 2970161627837, s2P 2356258659969, s2P 8330244418881,
   s2P 3068599456440, s2N 1996815559352, s2N 1380838370896, s2N 12968534319853,
   s2N 7127763268857, s2N 4885451290428, s2N 19236284328647, s2N 10313733647271,
   s2P 4611629742143, s2P 5060629750514, s2N 167893924975, s2N 2137737420747,
   s2N 9011905079337, s2P 1634865843698, s2P 4439048813083, s2P 3949179307463,
   s2P 476083661068, s2N 2918195200859, s2N 7050732808620, s2N 8469966142647,
   s2P 1436781958056, s2N 2314405491817, s2N 464204342557, s2N 2318641531834,
   s2P 2363213277233, s2P 5917664236526, s2P 1776785193917, s2P 3789959436867,
   s2P 3817901292595, s2P 775681148828, s2P 8987001878625, s2N 6508085264924,
   s2N 1717870986413, s2N 8244481859242, s2N 10490341276876, s2N 8498692993958,
   s2P 6670633060375, s2P 4474265430511, s2N 1608448561477, s2N 620093467650, s2N 699923685145,
   s2N 1875396382767, s2N 5295477156710, s2N 6876834637630, s2P 7351937038117,
   s2P 6099238463055, s2N 2624346669475, s2P 5863079568150, s2P 7132918087956,
   s2P 10438594013943, s2N 1156866997086, s2N 3093479176953]
private def s2St3VecS5 : List ℤ :=
  [s2N 5052048948102, s2P 6621550704158, s2P 5503221161184, s2N 219871445284,
   s2P 2497404121627, s2P 6963875580072, s2P 7802430679901, s2P 5534868737059,
   s2N 2601748940344, s2P 2428572858008, s2N 7988696589464, s2P 4835171151913,
   s2N 228195727375, s2P 2924302556109, s2N 8184075308390, s2N 459677390246, s2P 161631307468,
   s2N 6298657114939, s2N 2056173467464, s2N 1380258780006, s2N 3868314730352,
   s2N 1069857080567, s2P 4032997601592, s2P 263084785772, s2P 543921977758,
   s2P 10349348792652, s2N 7376318574197, s2P 9983330804906, s2N 2686220866958,
   s2P 741552300610, s2N 4976433942505, s2N 13825491281602, s2N 705739277566,
   s2P 4423877773302, s2N 5144779711244, s2N 6866331211594, s2N 1599918362114,
   s2N 193233129376, s2P 1194888521719, s2P 7635591983609, s2N 12798552116800,
   s2N 8930082901928, s2P 2283205160586, s2P 11055689732076, s2P 6584095096075,
   s2P 17109983198168, s2P 59419943769220, s2P 115027077106992, s2P 176409672808375,
   s2P 235576507773564, s2P 285628804585257, s2P 321913303485368, s2P 342166628947487,
   s2P 346166721299550, s2P 335460529719713, s2P 312929903685787, s2P 282057704511752,
   s2P 246295820715410, s2P 208774805789424, s2P 172144891229892, s2P 138374590758895,
   s2P 108627449990410, s2P 83354978047068, s2P 62531643512293]
private def s2St3VecS6 : List ℤ :=
  [s2P 45863051264277, s2P 32897655592416, s2P 23086245325236, s2P 15843286885968,
   s2P 10613675334388, s2P 6919709745785, s2P 4375055042428, s2P 2674932080025,
   s2P 1579674172649, s2P 902151519056, s2P 500232413540, s2P 271099722779, s2P 144847290291,
   s2P 77006248500, s2P 41051414474, s2P 22035313571, s2N 11904680648, s2P 6444746446,
   s2P 3472621360, s2P 1848984205, s2P 966628923, s2P 493795680, s2P 245768572, s2P 119067601,
   s2P 56206386, s2P 25924675, s2P 11729891, s2P 5230849, s2P 2309095, s2P 1011656, s2P 440408,
   s2P 190547, s2P 81673, s2P 34337, s2P 13925, s2N 5346, s2P 1912, s2P 632, s2P 190, s2P 50,
   s2P 11, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St3VecS7 : List ℤ :=
  [s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St3VecS8 : List ℤ :=
  [s2P 0]
private def s2St3Vec : List ℤ :=
  s2St3VecS0 ++
  (s2St3VecS1 ++
  (s2St3VecS2 ++
  (s2St3VecS3 ++
  (s2St3VecS4 ++
  (s2St3VecS5 ++
  (s2St3VecS6 ++
  (s2St3VecS7 ++
  (s2St3VecS8))))))))
private def s2Chk4 : List Rkm128kSeg := s2Take 1 s2Rem4
private def s2Rem5 : List Rkm128kSeg := s2Drop 1 s2Rem4
private def s2St4VecS0 : List ℤ :=
  [s2N 83616518, s2N 113202399, s2P 4238651, s2P 109550911, s2N 314432761, s2N 214907724,
   s2N 304192994, s2P 598243063, s2N 20791538, s2N 110516653, s2N 180916364, s2N 549226001,
   s2N 609328758, s2N 1084137837, s2N 1622300131, s2P 1246165375, s2P 2741687300,
   s2P 2645354586, s2P 1873692667, s2N 362382005, s2P 2943901894, s2P 2480133861,
   s2P 845282429, s2P 1076359767, s2N 3091814307, s2P 3226001244, s2P 447480148,
   s2P 4214761287, s2P 4513759814, s2N 865488784, s2P 3249243806, s2N 1637396712,
   s2P 2017231905, s2N 492914983, s2N 11431022403, s2N 8242870079, s2P 1537935194,
   s2N 4009385414, s2N 1888577014, s2N 1542105149, s2N 8454052335, s2N 1273403784,
   s2N 11173516440, s2N 8678424039, s2P 2992158746, s2P 40066361393, s2P 8114727583,
   s2P 29985950063, s2P 20224894386, s2N 16474878511, s2N 44971073526, s2N 18611482058,
   s2P 7376134552, s2P 2006784306, s2N 2034686517, s2N 20728700672, s2P 1396884029,
   s2P 2479930658, s2N 1736049611, s2N 40312432076, s2N 46008036727, s2N 11567538793,
   s2P 6252405604, s2P 1068910950]
private def s2St4VecS1 : List ℤ :=
  [s2N 13214943842, s2P 25626145486, s2N 25456122893, s2N 23495333934, s2N 14174437469,
   s2N 46178210988, s2P 15493127051, s2P 3718656289, s2N 46934578798, s2N 8338115513,
   s2P 5873908212, s2N 38404099028, s2N 43968340935, s2N 19019116649, s2N 77070217914,
   s2N 51562634752, s2P 8307105083, s2N 6086124191, s2P 9656359706, s2P 84119366105,
   s2P 41607396961, s2P 52285197646, s2N 7881440083, s2P 29171736916, s2P 53962801926,
   s2P 36978073218, s2N 61250526822, s2N 125643154990, s2N 41743435849, s2N 65725162594,
   s2P 76326060302, s2P 7823067007, s2N 10750967471, s2N 29191408697, s2P 82080012086,
   s2N 951293736, s2P 7090163071, s2P 6304790135, s2P 128683931069, s2P 60444999535,
   s2P 2339982532, s2N 67057604674, s2N 71419197942, s2P 17530382321, s2P 109254292381,
   s2P 366996326501, s2P 217050453610, s2P 73847077591, s2N 75521462217, s2N 31781428382,
   s2P 47226094071, s2N 213566146009, s2N 170208885959, s2N 53236753900, s2N 126931748731,
   s2N 150788702986, s2P 36371435164, s2N 32698425772, s2P 70820066133, s2P 73600480054,
   s2N 185172778153, s2P 49032665420, s2N 156243781244, s2P 38859960634]
private def s2St4VecS2 : List ℤ :=
  [s2P 34821534540, s2P 103572915829, s2P 88438905588, s2P 183355502078, s2P 70350713843,
   s2P 254281296080, s2P 680287850264, s2P 42976027359, s2N 256377921910, s2N 58901021338,
   s2N 235019296934, s2N 354913480849, s2N 481764687229, s2P 171781216984, s2P 1021154569228,
   s2P 586445403723, s2P 747208654649, s2P 1276845842356, s2P 798100098610, s2P 1138961725393,
   s2P 864112506503, s2N 315344234700, s2N 507111897227, s2N 85200490292, s2N 379831353387,
   s2N 2013391830926, s2N 2021504187426, s2N 2209496101411, s2N 976191011060,
   s2N 1629291238217, s2N 736869087708, s2N 2209076661683, s2N 882238108706, s2P 4160694217484,
   s2P 2822661624744, s2P 247164330115, s2P 471128502338, s2P 1686746995654, s2N 1045988469610,
   s2P 73119748324, s2P 2350040926703, s2N 1403300494897, s2N 1117736198497, s2P 1922268134572,
   s2P 2040913170459, s2P 2411978095568, s2P 3566822587440, s2P 520705980601, s2N 731590516738,
   s2P 595347664065, s2P 1126563572598, s2P 1978284121028, s2P 1257019866655, s2P 535747055438,
   s2P 1360932851953, s2N 853308857538, s2N 1252045268948, s2N 847652630868, s2P 121207044696,
   s2P 1788761716225, s2P 1158739100443, s2N 1618165915085, s2P 1900650649582,
   s2P 1569818802711]
private def s2St4VecS3 : List ℤ :=
  [s2N 923834637235, s2P 702944743832, s2P 1344743808869, s2N 320612329055, s2P 546001517749,
   s2P 162446848694, s2N 527473396654, s2N 1078704812896, s2N 441379791123, s2N 708382473867,
   s2N 305118355465, s2P 304519495640, s2P 2669371893456, s2P 637059771997, s2N 387290835463,
   s2P 424652027705, s2P 2491780596528, s2P 2601536093542, s2N 217679370535, s2N 2041066600432,
   s2N 1863172677954, s2N 1077277934471, s2N 1663526755771, s2N 980501788659, s2N 598394935742,
   s2P 1747201074515, s2P 945237221789, s2P 2062492454803, s2N 1395577637009,
   s2N 1574194889362, s2N 1020988631083, s2P 4122472445054, s2N 1003615164549,
   s2N 1253690804291, s2P 1102890116481, s2P 127712851833, s2N 1203306276055,
   s2N 1260387003739, s2P 1663271778753, s2P 4174700640114, s2P 4960568179258,
   s2P 6855442654321, s2P 1110129332231, s2N 3450718153140, s2N 3461119354523,
   s2P 388989915391, s2P 481893817935, s2N 2426767570048, s2N 7368844796101, s2P 4318439781043,
   s2P 5733624338908, s2P 2318822922988, s2P 909192813619, s2P 649563036958, s2P 912265224618,
   s2N 802414548653, s2N 4468875936189, s2N 1009212901804, s2N 1423382429434,
   s2P 2009858254459, s2P 2162623204676, s2P 6638624179637, s2P 3014497543641,
   s2P 2383959841940]
private def s2St4VecS4 : List ℤ :=
  [s2P 2239330420065, s2P 4501791640138, s2P 2798872875091, s2P 1776981668720,
   s2N 1691930336587, s2N 4545708804154, s2N 4115417138907, s2N 1648573869304,
   s2N 2627410044516, s2N 1215231195367, s2N 10828636535890, s2N 8686199106659,
   s2N 442433404010, s2P 1349737783147, s2N 2848797741520, s2N 4707041446497,
   s2N 9644429057073, s2N 9809878209495, s2P 1147563722286, s2P 4750909508881,
   s2N 3522785066696, s2P 664086217770, s2N 2948576309310, s2N 1514582951408,
   s2N 2692698642116, s2N 12682298785631, s2P 17509058098270, s2P 11299034907972,
   s2P 5986318028160, s2N 192192600441, s2P 342148147585, s2N 4119844557752, s2N 2509810977392,
   s2N 10121350517733, s2N 7518158812980, s2N 2285936285956, s2N 4060627628690,
   s2N 1062810725005, s2N 4091490718591, s2P 3852558865355, s2N 423455222021,
   s2P 6119296307193, s2N 6176847525216, s2N 1570912193553, s2N 615702193457,
   s2P 2145877428609, s2P 5717425430794, s2N 1937608450763, s2P 569860514207,
   s2P 4853718608439, s2P 5666356291811, s2P 12437202687359, s2P 6087074644998,
   s2P 9181680381874, s2P 6691709713262, s2P 2302835561198, s2N 8398236917170,
   s2N 1467290091082, s2N 5583592800800, s2P 3074026726800, s2N 2108657869160,
   s2N 5965042285420, s2N 4916110729345, s2P 5230844956749]
private def s2St4VecS5 : List ℤ :=
  [s2P 5489746518623, s2N 1172105744317, s2N 5135154974671, s2P 14087076172552,
   s2N 7107133900461, s2N 4804530364188, s2N 860611218628, s2N 2243716277293,
   s2N 2332987031906, s2N 1200145516990, s2N 3206055285924, s2N 1015864226240,
   s2P 368255166999, s2N 10702527897803, s2P 9084012784771, s2N 2638877787311,
   s2P 2210722089704, s2N 7892174829504, s2N 8874318544661, s2P 9332423781684,
   s2P 3327222147571, s2P 2144667069703, s2N 2699695425277, s2P 4911739325500,
   s2P 324414004154, s2P 2950812921402, s2N 5217112419329, s2N 322155309655, s2N 5184371768427,
   s2P 2997785095705, s2P 3280067950391, s2P 5506996377127, s2P 8886226797255,
   s2P 6530932486797, s2P 8408410598760, s2N 3290918838900, s2N 702966492835,
   s2N 5040963008436, s2P 7293077889831, s2P 2050869207461, s2N 4252744580010,
   s2P 5739405128941, s2P 13920265600021, s2P 2246703832553, s2N 8742799090742,
   s2P 2291561429157, s2P 7971931152782, s2N 6809705263146, s2P 1100493025929,
   s2P 3108657525450, s2N 4104065406494, s2P 12270553925825, s2P 9594286076888,
   s2P 11600278436136, s2P 52148369355735, s2P 107317709680662, s2P 169471491561740,
   s2P 230362179719051, s2P 282710150270237, s2P 321262115630430, s2P 343301279304832,
   s2P 348524608359603, s2P 338500351022022, s2P 316053375440393]
private def s2St4VecS6 : List ℤ :=
  [s2P 284722842941412, s2P 248243027826975, s2P 210040261023678, s2P 172857915039843,
   s2P 138606830249267, s2P 108420809144265, s2P 82801323945464, s2P 61788606354287,
   s2P 45068091130985, s2P 32158770119390, s2P 22411053759253, s2P 15271710597448,
   s2P 10131664499587, s2P 6536896666073, s2P 4109585947608, s2P 2500920480136,
   s2N 1468798260478, s2P 843821302356, s2P 479314036794, s2P 264891788033, s2P 138083078857,
   s2P 66898702960, s2P 30771548126, s2P 14262456458, s2P 7121749786, s2P 3891094409,
   s2P 2226365002, s2P 1267319246, s2P 697891203, s2P 368794500, s2P 187305151, s2N 91837430,
   s2P 43687846, s2P 20255255, s2P 9181498, s2P 4082564, s2P 1790180, s2P 776508, s2P 331056,
   s2P 136615, s2N 53782, s2P 20118, s2P 7220, s2P 2531, s2P 882, s2N 299, s2P 98, s2P 26,
   s2P 5, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0]
private def s2St4VecS7 : List ℤ :=
  [s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St4VecS8 : List ℤ :=
  [s2P 0]
private def s2St4Vec : List ℤ :=
  s2St4VecS0 ++
  (s2St4VecS1 ++
  (s2St4VecS2 ++
  (s2St4VecS3 ++
  (s2St4VecS4 ++
  (s2St4VecS5 ++
  (s2St4VecS6 ++
  (s2St4VecS7 ++
  (s2St4VecS8))))))))
private def s2Chk5 : List Rkm128kSeg := s2Take 1 s2Rem5
private def s2Rem6 : List Rkm128kSeg := s2Drop 1 s2Rem5
private def s2St5VecS0 : List ℤ :=
  [s2P 27848971, s2P 43621765, s2P 253039905, s2N 179084089, s2N 144038176, s2N 321757504,
   s2N 345115117, s2N 503763367, s2N 9802503, s2N 151533981, s2N 51526926, s2P 591937899,
   s2N 440183673, s2P 391653428, s2P 931769560, s2P 1108336290, s2P 717343100, s2P 1978497574,
   s2P 2287899384, s2N 3636986008, s2N 107827291, s2N 3747817753, s2N 159476701, s2P 351475987,
   s2N 5023981482, s2P 194414567, s2P 3892248937, s2P 686270013, s2N 2123711004, s2P 979122467,
   s2P 302324496, s2N 564927267, s2N 7730656570, s2N 3093221400, s2N 5798781095,
   s2N 7620151790, s2N 1224892421, s2N 6429821506, s2N 7987965811, s2N 3902323202,
   s2P 20379254821, s2P 8133284687, s2N 2329777603, s2P 14901539498, s2P 2020135633,
   s2N 10987029125, s2N 7140997883, s2N 23642663246, s2N 3459693981, s2P 10899724119,
   s2P 7432335371, s2P 2150278220, s2N 35649184295, s2N 44252378108, s2N 17584555109,
   s2P 4742147651, s2P 33679935790, s2P 7298195582, s2P 8880950126, s2N 11868055079,
   s2N 23553472123, s2N 34187119294, s2N 35917293577, s2N 2925529476]
private def s2St5VecS1 : List ℤ :=
  [s2N 12271122313, s2P 1224722392, s2P 44392217208, s2P 27808804768, s2P 5458067985,
   s2N 23935923021, s2P 25281393187, s2N 42095432876, s2P 9505723669, s2N 39700273948,
   s2N 12344514611, s2N 8869755940, s2P 58097605960, s2P 17179614436, s2N 16970942535,
   s2N 25123120229, s2N 13362885040, s2P 1213297471, s2P 7355009630, s2P 49669983076,
   s2P 5884418972, s2N 86663888575, s2P 5398787140, s2N 89261686210, s2N 52125235187,
   s2N 10561973944, s2N 81050103757, s2N 7552602228, s2P 49315521444, s2N 11099110085,
   s2P 32595138870, s2N 72703684520, s2P 106402786676, s2N 26886108753, s2N 118333163124,
   s2P 38311448029, s2N 62073509357, s2N 21867886296, s2P 84806271058, s2P 19884221961,
   s2P 71382039755, s2N 23942658414, s2N 29933089661, s2N 44200979161, s2N 9711207426,
   s2N 32461002062, s2P 49938613060, s2P 139933901355, s2P 163760173348, s2P 170675754062,
   s2P 256644606496, s2P 138629270847, s2P 9417418761, s2P 270913026070, s2P 128069902936,
   s2N 178418575476, s2N 158621155445, s2N 64822789250, s2P 37163526169, s2P 30389276633,
   s2P 20028742856, s2N 215965089964, s2P 43755645681, s2P 209110766224]
private def s2St5VecS2 : List ℤ :=
  [s2N 204300298970, s2N 186231904870, s2N 112978717637, s2P 71947358160, s2P 230322929062,
   s2P 126996332478, s2P 180310030053, s2P 100268973156, s2P 50142629033, s2P 386814125163,
   s2P 409595093575, s2P 236126143201, s2P 613717773660, s2P 42329404520, s2P 163237002120,
   s2P 289468555391, s2P 678744414463, s2P 259655317709, s2N 499222275950, s2N 794461231600,
   s2N 465724401480, s2N 382749683371, s2N 275460458213, s2N 581019575449, s2N 911994777842,
   s2N 1426902155982, s2N 1262469672315, s2N 834947617164, s2N 1287207724014, s2N 860948947344,
   s2N 411283167426, s2N 578211625966, s2N 2662625062772, s2N 1906827766040, s2N 3341791451304,
   s2N 534075229820, s2P 148009402579, s2N 3023681104268, s2P 1541625861537, s2N 2348390974883,
   s2P 3406652604680, s2P 295669786632, s2P 1885772869541, s2P 1095033930441,
   s2P 1680969834345, s2P 411712000613, s2P 1055326455918, s2P 1081427643729,
   s2N 1129890609610, s2P 680001174212, s2N 1028744721925, s2N 2168105582861,
   s2N 1327033811256, s2P 1754640357516, s2P 2614301467378, s2P 2685014304290,
   s2N 261363762496, s2P 1049144441146, s2N 2050061457820, s2P 1160751993102, s2N 869328309113,
   s2P 3456963494958, s2P 1993016358550, s2P 346523235380]
private def s2St5VecS3 : List ℤ :=
  [s2N 307070859250, s2N 549143460557, s2P 205830391594, s2N 597177826991, s2N 610677094182,
   s2N 212149870542, s2P 177038286264, s2N 1256055587265, s2P 496469153241, s2P 65479675057,
   s2N 551758152605, s2P 1377771027903, s2P 205983580579, s2P 295461068446, s2P 133310310555,
   s2P 1875472441246, s2P 1235852209535, s2P 1529366414519, s2P 2394797449647,
   s2P 1754357607542, s2P 482698165964, s2P 664038059984, s2N 1826084891570, s2N 1150225697816,
   s2N 1576576025708, s2N 1232922026901, s2N 3277362974217, s2P 234404067329,
   s2P 1062080355299, s2N 1393626685137, s2N 1052921072380, s2P 3399020961292,
   s2P 3809520682147, s2P 1653109679339, s2P 1610499938106, s2P 132095722426, s2P 601222692448,
   s2P 1644192832832, s2N 1950861267508, s2P 1621496241927, s2P 1143424348551,
   s2N 676602013204, s2N 1135010823513, s2N 364598635175, s2P 2011535188697, s2P 974950606315,
   s2P 7396223254496, s2N 524468914396, s2N 5983639354022, s2N 8076469068607, s2N 294502104566,
   s2N 1140028251865, s2N 2548379435686, s2N 3982381493685, s2P 2203163927265,
   s2N 4215590885374, s2N 2993819839837, s2P 977975711788, s2N 1087143736556,
   s2N 1617048614897, s2P 2864421347800, s2P 2746391957930, s2N 1196389206290,
   s2N 3830205525348]
private def s2St5VecS4 : List ℤ :=
  [s2N 1840258806401, s2N 1434509181742, s2N 3914468286127, s2N 2978699043220,
   s2P 1884511494520, s2N 2451702285206, s2N 1448589983161, s2P 4054108737048,
   s2N 2064621732478, s2N 1307046177387, s2N 6378114095323, s2N 9442079787394,
   s2N 2614500995619, s2N 2185126581842, s2P 957788380921, s2P 5970480909105,
   s2P 8802290941103, s2P 8303725819761, s2N 3853531754086, s2N 11356554693169,
   s2N 6847258646400, s2P 5106762572975, s2N 1785346838014, s2N 12385232774365,
   s2N 4610113929930, s2N 1938914170979, s2N 9740109776667, s2N 5130173807769,
   s2N 2508807192397, s2P 9049997210388, s2N 1031980804817, s2P 4453919018704,
   s2N 13345928093391, s2N 241376586460, s2N 1291141540446, s2N 4650308574697,
   s2P 8043077818399, s2P 4757217083710, s2P 8511908987554, s2P 2184227314961,
   s2N 4431355168923, s2N 2752059186698, s2N 7962975732039, s2P 1451439157906,
   s2P 7874438850007, s2P 6671357126958, s2N 5077969669011, s2N 3435542163835,
   s2N 139124991996, s2P 4281148910682, s2N 6731952365373, s2N 1188913934499,
   s2P 2260964045294, s2P 1378364803257, s2N 1270248222153, s2N 1208934543218,
   s2N 1907735286445, s2P 5091145685341, s2N 1995749596160, s2P 10405148401748,
   s2P 3688853303473, s2P 16739438391901, s2P 13944506860254, s2P 6220810317782]
private def s2St5VecS5 : List ℤ :=
  [s2N 640548499183, s2N 7060206976687, s2N 1485850512638, s2N 8937146621336,
   s2P 2217106441265, s2N 8202077389767, s2P 4639612731870, s2P 8093049337791,
   s2P 1332547980588, s2P 7315299363027, s2P 2479212449785, s2N 5385014279023,
   s2N 3167417202429, s2N 2174519568539, s2N 3978563411079, s2N 3729471063510,
   s2N 3341515275336, s2P 6592384246926, s2N 6525757054110, s2N 6857860528889,
   s2N 4698005060806, s2N 6408997871112, s2P 2352974565646, s2P 5306282988411,
   s2N 3450869846773, s2P 5390652175607, s2N 2933395614908, s2P 2387250906430,
   s2P 3357614215470, s2N 2281970413076, s2P 4718242370597, s2P 3283607929069,
   s2P 1577068190841, s2N 1156375277694, s2N 4038768930573, s2N 2349301089204,
   s2P 390434328854, s2N 4265149059890, s2P 525312244092, s2P 10697090242153,
   s2P 15855237568723, s2N 2083649382923, s2P 1913048734599, s2N 15137532849561,
   s2N 3978914590140, s2N 7806177714308, s2P 4356310127465, s2P 118320690380,
   s2P 6880970576110, s2P 7949614512075, s2P 1677382895951, s2N 916871889507,
   s2N 7400234881756, s2N 1692904270388, s2N 6042614957279, s2N 2624268369331,
   s2P 6039068560060, s2P 6995245279941, s2P 2011871517101, s2P 11283280747450,
   s2P 8400071594930, s2P 14113829546458, s2P 56614620070756, s2P 113827058558570]
private def s2St5VecS6 : List ℤ :=
  [s2P 177481441978343, s2P 238893858687582, s2P 290665024320566, s2P 327779114142488,
   s2P 347627381340666, s2P 350265136089210, s2P 337196407936151, s2P 312506023512334,
   s2P 278294496485902, s2P 241864430329737, s2P 201100500001679, s2P 165659448707299,
   s2P 130862329799010, s2P 100590203333517, s2P 77273897267541, s2P 56923614222699,
   s2P 39975781828040, s2P 28362851782908, s2P 20473744126467, s2P 13983179960730,
   s2P 8512409607528, s2P 4618212783045, s2P 2368040933059, s2P 1262489049363,
   s2P 742112342521, s2P 464436704583, s2P 288409967909, s2P 169881761926, s2P 93967661691,
   s2P 49292736669, s2P 24879241700, s2N 12360855324, s2N 6250354714, s2P 3258013043,
   s2P 1694718915, s2P 839918976, s2P 389193604, s2P 172440624, s2P 76958380, s2N 36136147,
   s2P 17882991, s2P 9044216, s2P 4502840, s2P 2136987, s2P 945743, s2P 387717, s2P 148932,
   s2P 54975, s2P 20015, s2P 7260, s2P 2599, s2P 904, s2P 300, s2P 92, s2P 25, s2P 5, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St5VecS7 : List ℤ :=
  [s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St5VecS8 : List ℤ :=
  [s2P 0]
private def s2St5Vec : List ℤ :=
  s2St5VecS0 ++
  (s2St5VecS1 ++
  (s2St5VecS2 ++
  (s2St5VecS3 ++
  (s2St5VecS4 ++
  (s2St5VecS5 ++
  (s2St5VecS6 ++
  (s2St5VecS7 ++
  (s2St5VecS8))))))))
private def s2Chk6 : List Rkm128kSeg := s2Take 1 s2Rem6
private def s2Rem7 : List Rkm128kSeg := s2Drop 1 s2Rem6
private def s2St6VecS0 : List ℤ :=
  [s2P 61666395, s2P 152973760, s2N 211414876, s2P 105907803, s2N 134235079, s2N 165746975,
   s2N 9523986, s2N 75123414, s2P 759420792, s2P 125559945, s2P 516885578, s2N 435325808,
   s2N 64549809, s2N 62600850, s2P 849534701, s2P 2488944021, s2P 2997147810, s2N 927135170,
   s2P 636992062, s2P 2459907851, s2N 132381252, s2P 3082978112, s2N 2706232397,
   s2N 2027456678, s2P 3641971514, s2P 2362267802, s2N 1501815080, s2P 1949155500,
   s2P 4997039990, s2P 355759174, s2N 4132915963, s2P 3754093284, s2P 1774945064,
   s2N 253630064, s2P 3599819815, s2N 3004988499, s2N 545052369, s2N 4640318142,
   s2P 14295828513, s2P 8102785944, s2N 12784100809, s2N 12457462178, s2N 12463110205,
   s2N 4212576949, s2N 9194641586, s2N 6399714469, s2P 3288682446, s2P 29787266,
   s2P 17242630236, s2N 2596003452, s2N 17788609429, s2N 4342274910, s2N 11457615077,
   s2N 21939726979, s2N 19242658587, s2N 16404485213, s2N 18324793911, s2N 10374863018,
   s2N 19316487817, s2N 50204190964, s2N 11920083887, s2N 30570995737, s2N 11266363922,
   s2N 8338040691]
private def s2St6VecS1 : List ℤ :=
  [s2N 60450324711, s2P 23753227477, s2P 3466182129, s2P 10475667065, s2N 12912303882,
   s2N 51178676761, s2N 28915789133, s2P 12564907212, s2N 4261308661, s2P 31440694945,
   s2P 24246003711, s2P 621998822, s2N 11098348829, s2N 3520952403, s2N 56545785675,
   s2N 68016185230, s2N 32998575941, s2N 10283581872, s2N 48926016893, s2N 29234989122,
   s2P 70932119781, s2P 53189837645, s2P 45715918742, s2P 74353130007, s2P 4456794758,
   s2N 17583762853, s2N 3213126598, s2P 90231437724, s2P 68255805995, s2P 35931480733,
   s2P 85660895351, s2P 125962165251, s2N 69439010397, s2P 38754970960, s2N 24399013204,
   s2P 40226133907, s2P 10060002660, s2N 13696327509, s2P 19328342908, s2P 21132820086,
   s2P 14173038303, s2P 8722206877, s2P 14829336654, s2P 46495202120, s2P 115561005960,
   s2P 51537147477, s2P 16032482951, s2P 51397154447, s2P 152745001281, s2P 15631314149,
   s2N 61686656251, s2P 5509053972, s2N 68820056992, s2P 145869173494, s2P 143013370764,
   s2P 192643132420, s2P 62002186294, s2P 155191144642, s2P 157666299434, s2N 5659515235,
   s2N 289511750409, s2N 367168195042, s2N 131049416585, s2N 71928477163]
private def s2St6VecS2 : List ℤ :=
  [s2N 88398709673, s2N 26275519877, s2N 182539756625, s2N 350693304179, s2N 91192569420,
   s2P 104841984687, s2P 46143624968, s2P 150859621137, s2P 9140380587, s2N 249982006477,
   s2P 146408258323, s2P 66990518328, s2N 83374605300, s2P 44763207198, s2P 223241749494,
   s2N 189082585695, s2N 129751482478, s2N 3783557424, s2N 225489479651, s2P 868636173030,
   s2P 44157628454, s2N 256284958215, s2N 254672071394, s2N 912085131500, s2P 7518255816,
   s2P 1022423886696, s2P 925231850716, s2P 2126665621818, s2P 2145354771820,
   s2P 2946217528210, s2P 2183334412176, s2P 1724552433757, s2P 232919669472, s2N 261350693703,
   s2P 677628008306, s2P 1525882315496, s2P 1908539867843, s2P 922930605879, s2P 413335803176,
   s2P 1042523182022, s2P 2221711389775, s2P 1852787907597, s2N 1520323001536,
   s2N 1837276610182, s2P 2166882991882, s2P 547588093394, s2N 3156944577919, s2P 371028579051,
   s2P 1625403893725, s2N 1840266282243, s2P 1173246992994, s2N 1882910695673,
   s2P 1668903064704, s2N 1283770829228, s2P 989517583580, s2P 80800333719, s2P 2330574661952,
   s2P 1973712760063, s2P 7202706586, s2N 1814064271758, s2N 1463560000521, s2N 1670627432947,
   s2N 5635172071, s2P 1193362151955]
private def s2St6VecS3 : List ℤ :=
  [s2P 2509779693211, s2P 2804143758140, s2P 1230900548027, s2P 410923313292, s2N 132417280998,
   s2P 599568794159, s2N 1209781570625, s2N 2021731921134, s2N 1077758079535, s2P 523258168169,
   s2P 510364737509, s2N 602235774987, s2P 1484481240653, s2N 717762239446, s2P 420384362188,
   s2P 306227929615, s2N 1071401925001, s2P 180355823976, s2P 569861794072, s2N 105531943266,
   s2P 691379184134, s2P 389846523123, s2N 82835362882, s2N 1213072514836, s2N 170103553097,
   s2P 668747214293, s2P 2553320643084, s2P 3747282980529, s2N 680050429572, s2P 2592997777799,
   s2N 1982892476046, s2N 628697564725, s2P 397093600180, s2P 3593985126044, s2P 130027595386,
   s2N 1175382679143, s2P 158377380101, s2P 5135020542452, s2N 452012223576, s2N 315670272386,
   s2P 576440396516, s2P 1056247527719, s2N 4627122037427, s2P 113816868107, s2N 2368931604278,
   s2N 794429323854, s2P 1248593101919, s2N 1521568234356, s2P 921652582699, s2N 5801451460946,
   s2P 1232221097828, s2P 7338935011946, s2P 111372350950, s2P 4334198296308,
   s2P 3103243819617, s2N 3141700042324, s2P 2254689248791, s2P 2767206972235,
   s2P 3772655953875, s2N 2644537587670, s2P 1302430042883, s2P 3216383970977,
   s2N 5092598206635, s2N 2991379612652]
private def s2St6VecS4 : List ℤ :=
  [s2N 2922618744812, s2N 5680855528064, s2P 162377142884, s2P 2834177365064, s2P 203951705515,
   s2P 2008169403391, s2N 214888141802, s2P 2149967261412, s2P 2015848001963,
   s2P 2189275947928, s2P 1967922568834, s2N 780416105935, s2N 3603489840579,
   s2N 4201642804783, s2N 1517768869596, s2N 1532104259605, s2N 3291491621794,
   s2P 1215112969222, s2P 8494993657864, s2P 5698315734860, s2P 7841765280699,
   s2P 10710261994554, s2P 15039824918840, s2P 11396621278873, s2P 8542356745556,
   s2P 2263273231301, s2N 5110624814979, s2N 4622076907802, s2P 3777108052089,
   s2P 3694759069136, s2N 7439321902658, s2N 1941862885315, s2P 2765649633973,
   s2P 4750955437707, s2P 12993904539754, s2P 8040882899572, s2N 3259794921526,
   s2N 634322733703, s2N 622322341508, s2N 5254133705989, s2N 2674794389806, s2N 3461558316972,
   s2N 6578719922093, s2P 2725039758113, s2P 3119836031607, s2P 1507434566662,
   s2N 10734424209605, s2N 13111453152247, s2N 6891047554665, s2N 3099191283805,
   s2N 6551913495663, s2N 6980227934792, s2N 1651246787183, s2N 482608079716,
   s2P 4012223073046, s2P 859800202041, s2N 3061969912556, s2N 5741332346080,
   s2P 1491714763361, s2P 4761267126837, s2P 5916154565401, s2P 3617956319832,
   s2P 2292363964513, s2N 3749668973117]
private def s2St6VecS5 : List ℤ :=
  [s2P 3091866362824, s2P 995138983819, s2P 3097806182275, s2N 3923869647567,
   s2P 10661344448975, s2P 14857886435837, s2P 9493614419666, s2P 13102332465534,
   s2P 4319320760387, s2N 3521280749714, s2N 4862971192558, s2N 2821369742933,
   s2N 4078311021518, s2P 9395041866246, s2N 790750080241, s2P 8751248581022,
   s2N 1233520989287, s2P 8654938776186, s2N 1648817034007, s2P 1634759433025,
   s2N 1056627673870, s2P 9323778762580, s2N 2564688303342, s2P 1353281046419,
   s2N 890318608823, s2N 1345832682355, s2N 5409215491267, s2N 8245038378173,
   s2N 3763156665528, s2P 3978432062206, s2N 346422012263, s2N 2409010304430,
   s2N 3411358816373, s2P 2159014453592, s2N 7957542640697, s2N 9916161467634,
   s2N 6162090530235, s2N 2967692810726, s2N 4429067809062, s2N 2121399554478,
   s2N 3558398909080, s2P 3873812915964, s2N 3433734605221, s2N 4060868735887,
   s2N 10045622670599, s2N 646901898366, s2N 7272978960901, s2N 12748985322487,
   s2N 7521794123988, s2N 200117302012, s2P 3043525800047, s2N 4176475818765,
   s2P 12060210933011, s2P 3819329006352, s2P 4682917182480, s2P 434941073293,
   s2P 7624864270694, s2P 8557542731937, s2P 1899282709135, s2N 3323530168963,
   s2N 1581527271923, s2P 5989358994722, s2N 7502189248311, s2P 1656843457061]
private def s2St6VecS6 : List ℤ :=
  [s2P 10116103996234, s2P 9474419800397, s2P 3241071731063, s2P 10726975197609,
   s2P 6329844117219, s2P 21251656520553, s2P 68514549485296, s2P 127920521717115,
   s2P 194163052408322, s2P 255030041617332, s2P 303700069760660, s2P 337917611798451,
   s2P 353162211124084, s2P 349672989939889, s2P 332439297501875, s2P 304329499655673,
   s2P 267729957146037, s2P 227707587571246, s2P 188837575403890, s2P 152584987685827,
   s2P 119353077166906, s2P 90439656112144, s2P 67111969102804, s2P 49216692686621,
   s2P 35517259278137, s2P 24780326856308, s2P 16453509011662, s2P 10302588181984,
   s2N 6110515980699, s2P 3504292994158, s2P 1975674585270, s2P 1107730606363,
   s2P 633829106636, s2P 373737870558, s2P 216267728196, s2P 113792617646, s2P 51785763577,
   s2P 20261460237, s2P 7252642598, s2P 2889248825, s2P 1572608602, s2P 1024262789,
   s2P 634569814, s2P 344446757, s2P 164993637, s2P 73177627, s2N 32264446, s2P 15029170,
   s2P 7449698, s2P 3772979, s2P 1868279, s2P 882413, s2P 394393, s2P 167010, s2P 67351,
   s2P 26031, s2P 9700, s2N 3493, s2P 1217, s2P 405, s2P 125, s2P 32, s2P 6, s2P 0]
private def s2St6VecS7 : List ℤ :=
  [s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St6VecS8 : List ℤ :=
  [s2P 0]
private def s2St6Vec : List ℤ :=
  s2St6VecS0 ++
  (s2St6VecS1 ++
  (s2St6VecS2 ++
  (s2St6VecS3 ++
  (s2St6VecS4 ++
  (s2St6VecS5 ++
  (s2St6VecS6 ++
  (s2St6VecS7 ++
  (s2St6VecS8))))))))
private def s2Chk7 : List Rkm128kSeg := s2Take 1 s2Rem7
private def s2Rem8 : List Rkm128kSeg := s2Drop 1 s2Rem7
private def s2St7VecS0 : List ℤ :=
  [s2P 69838876, s2P 279819127, s2P 55602981, s2P 78164508, s2P 180013231, s2P 308657931,
   s2P 348687638, s2P 515990250, s2P 48484337, s2P 243722884, s2N 232487974, s2P 379539650,
   s2P 716931472, s2P 431101788, s2P 856132622, s2N 315916896, s2P 3388121373, s2P 2473907652,
   s2P 1293757801, s2N 1200969500, s2N 2821111732, s2N 82141782, s2N 1440361022,
   s2N 3449136663, s2N 3581814780, s2N 173755263, s2P 4226441762, s2P 2394399337,
   s2P 3758689796, s2P 5573799760, s2P 3571739806, s2N 247192650, s2N 5532742717,
   s2N 571047526, s2P 1230006341, s2P 6390033554, s2P 6459294052, s2P 655385294,
   s2P 8302096910, s2N 2998458908, s2P 2612786111, s2P 14362500903, s2N 7505765716,
   s2N 9650309473, s2N 3348114691, s2N 7892772462, s2N 9108979532, s2N 11919909897,
   s2N 4380574, s2P 8419908052, s2P 18925486499, s2P 13414751901, s2P 13548989629,
   s2P 9289840406, s2N 15971914224, s2P 4166304984, s2N 21831329414, s2N 29328235763,
   s2N 33444859036, s2N 739198056, s2P 18768283971, s2P 33842570538, s2P 2659402238,
   s2P 1136728264]
private def s2St7VecS1 : List ℤ :=
  [s2N 37888913462, s2P 18882080269, s2P 38187025885, s2P 12997189852, s2N 4424038946,
   s2N 32835657751, s2N 56976470994, s2N 11592920380, s2P 3145055224, s2P 3336973349,
   s2P 11720571901, s2P 8662332118, s2P 32906416029, s2P 49778113102, s2P 1617885054,
   s2N 15277486327, s2N 45303559752, s2P 40592041585, s2P 47116411774, s2N 10701208819,
   s2N 32951870630, s2N 2558538155, s2N 37155659480, s2P 15052877225, s2P 108873817160,
   s2P 34705778237, s2P 100346896565, s2P 57111872379, s2P 73483751356, s2P 64921116206,
   s2P 41212951786, s2P 20332156411, s2P 31968732711, s2P 21119518781, s2P 3020095416,
   s2P 9246114545, s2P 81978637152, s2P 80669513143, s2P 91180526734, s2N 46385544169,
   s2N 33812724804, s2P 31172625419, s2N 1333875972, s2N 79354637600, s2N 109543971274,
   s2N 69087991664, s2P 45736690535, s2P 9850181653, s2P 61331997685, s2N 13132741600,
   s2N 51274793838, s2P 30518218625, s2P 54257699038, s2P 8437559061, s2N 33765159986,
   s2P 85548038193, s2P 138700987447, s2P 130127813860, s2P 53022342915, s2P 139806614433,
   s2N 75634477155, s2N 118339072230, s2N 74982449043, s2P 2734556831]
private def s2St7VecS2 : List ℤ :=
  [s2P 262732537353, s2P 86354894137, s2P 344458288798, s2P 204638312759, s2N 133473167499,
   s2N 219927249881, s2N 168334526419, s2N 171977060194, s2N 184471363298, s2N 371046565170,
   s2N 568683053441, s2N 189778130919, s2N 62593427759, s2P 366801625503, s2P 254199334038,
   s2P 11186695498, s2N 365355479859, s2N 634784465578, s2N 458364519198, s2N 77470906521,
   s2N 114055521849, s2N 184703383685, s2P 111734272747, s2N 185739706869, s2N 79388473430,
   s2N 641686754649, s2N 9546149988, s2N 301397648326, s2N 500506033838, s2N 375029274450,
   s2N 191286845105, s2P 444779759187, s2P 613445827074, s2P 284221103356, s2P 35954413883,
   s2P 285771054516, s2P 1039293796734, s2P 2148295954266, s2P 2704029437032,
   s2P 2909582044845, s2P 3765818615952, s2P 3695051666609, s2P 3066398874709,
   s2P 2218238691349, s2P 778005487827, s2N 1404334383985, s2N 1724979408328,
   s2N 2476644206367, s2N 1314091503059, s2P 719721683156, s2P 1283515192324, s2P 838594686812,
   s2P 885878636881, s2P 565465896521, s2N 585735683212, s2N 470628163203, s2P 392925318746,
   s2P 490372606216, s2N 554385605653, s2N 719433196909, s2P 62643380237, s2N 683051684103,
   s2N 1162270445551, s2P 663978283445]
private def s2St7VecS3 : List ℤ :=
  [s2P 1369650902729, s2P 1184716971507, s2P 2419761454173, s2N 746363220892, s2P 985246487373,
   s2P 1893457164012, s2N 3292885239525, s2N 34982639159, s2P 572615286004, s2P 449546193956,
   s2P 1974136138460, s2P 1402635331846, s2P 2193395687605, s2P 1764984543358,
   s2N 259286009124, s2N 805846256984, s2N 1202383356300, s2P 219858898347, s2N 2601727517736,
   s2N 1645968301268, s2N 1687603225451, s2N 1455477305460, s2N 14178400093, s2P 22860857230,
   s2P 119623215738, s2N 1130143631349, s2N 2091836340499, s2P 418981199934, s2N 58517377172,
   s2N 2541038072765, s2N 1320847643376, s2N 534275409652, s2N 799811928628, s2N 579712969258,
   s2P 3112500866218, s2P 3886659656427, s2P 5728988337818, s2P 2556894130513,
   s2N 1650364184945, s2N 82551181373, s2N 1516253988561, s2N 985412399353, s2P 2118258967719,
   s2P 3374062748895, s2P 878156430849, s2P 1083534598868, s2P 5894714068227,
   s2P 2606945846359, s2P 1771218576980, s2N 3694903715274, s2P 92160489275, s2N 3131470950080,
   s2P 2982057996893, s2N 1690856138546, s2P 1849779110263, s2N 92138472346, s2P 2231930126466,
   s2P 5803912933186, s2P 4939420780667, s2P 4202333460323, s2P 1000739007242,
   s2N 2468734821032, s2N 2414215007492, s2N 1340623483384]
private def s2St7VecS4 : List ℤ :=
  [s2N 1894085850216, s2N 1752838201392, s2P 1664726478534, s2N 787348527255,
   s2N 1847791263823, s2N 3135242165495, s2N 2444202785526, s2N 1242985080395,
   s2N 3315379777336, s2N 5024855222428, s2N 1617659431227, s2N 3858033247219,
   s2N 703622595607, s2N 1588819275610, s2N 990334682472, s2N 1974283311998, s2P 3150430536724,
   s2P 4952374120938, s2P 607760437386, s2P 958472292347, s2P 1864329605944, s2N 1322004025322,
   s2P 5448082981463, s2P 3280272506366, s2P 1870050349803, s2P 5870545037962,
   s2P 2092785817882, s2P 4832112343987, s2P 3288123837383, s2P 4684862161531,
   s2P 15396906744380, s2P 14901531878575, s2P 13742433529604, s2P 9503708801548,
   s2P 2786072918091, s2P 5036053068174, s2P 5225660924893, s2N 975245805075,
   s2P 4571352058925, s2P 5913283017417, s2P 2515618079453, s2N 2553264933500,
   s2P 8272327256020, s2P 7630218983298, s2N 4838857493621, s2P 52569560206, s2N 5942085989929,
   s2P 2776863454142, s2N 6090532001076, s2N 10652129973938, s2N 2223885873750,
   s2P 2279149621300, s2N 4143667216432, s2P 1496645504321, s2N 3143681115469,
   s2N 9424156951276, s2P 1748141955833, s2N 8430812720438, s2N 8279747891801,
   s2N 11285521513810, s2N 4279563141969, s2P 1036963574494, s2P 1525840477031,
   s2P 4370692942876]
private def s2St7VecS5 : List ℤ :=
  [s2P 5723293793831, s2N 7467161713562, s2P 1105993846727, s2P 7544892266552,
   s2P 3778430625727, s2P 8475474495706, s2P 2679930445547, s2P 8346978127959,
   s2P 1806723479231, s2P 2177530655459, s2N 5864122547285, s2N 1977523163439,
   s2N 1005304755093, s2P 12589424997882, s2P 11095392817295, s2P 17101972315131,
   s2P 7401088342098, s2N 1548083150033, s2P 434066013239, s2N 876643533140, s2N 3995584975139,
   s2P 527137119211, s2N 2656659304013, s2P 7816950147168, s2N 1474684652720,
   s2N 2061029612201, s2N 1648169900438, s2N 5439342516465, s2P 502024169646, s2P 656579743924,
   s2P 5047264546242, s2P 8199449167827, s2N 5121151869645, s2N 3074482083272,
   s2P 5665683333372, s2P 320021885132, s2N 6803097504733, s2N 1378186133890, s2P 84552538898,
   s2N 2478776686044, s2P 150909977712, s2N 8526845940400, s2N 1887987263269,
   s2N 6614350056143, s2N 4281961301208, s2N 14610351232972, s2P 2357657890631,
   s2P 600054820483, s2P 5185825970175, s2N 2936610269950, s2N 1013165341586, s2N 882420096025,
   s2P 8897827567950, s2N 5194055406602, s2N 9788806958026, s2N 5646315912884,
   s2N 12806821709960, s2N 2369934210814, s2N 6634198202331, s2P 2579996418720,
   s2P 4675235132548, s2P 8635960513214, s2P 8819379497369, s2P 358353212280]
private def s2St7VecS6 : List ℤ :=
  [s2P 7873524379276, s2N 6585797754714, s2N 98637438895, s2P 205436529591, s2N 1257832276213,
   s2P 4103349754088, s2N 496532956159, s2N 8450326399475, s2N 13504745425183,
   s2P 6688123941428, s2N 6987604039011, s2P 11979991440542, s2P 2600712617688,
   s2P 38301102892583, s2P 92303458146832, s2P 157928572613733, s2P 224256768579327,
   s2P 281822634136577, s2P 324117756018231, s2P 351069711483506, s2P 354723380590343,
   s2P 348525683987832, s2P 315731106714160, s2P 289972763358883, s2P 246466912342703,
   s2P 204377065934724, s2P 170948019376754, s2P 132383016367472, s2P 97319752362785,
   s2P 75216619820447, s2P 59249614510969, s2P 42354056041639, s2P 26063296613689,
   s2P 14177843272897, s2P 7426346812060, s2P 4151780441520, s2P 2568949105774,
   s2P 1677162201770, s2P 1090119186688, s2P 683824224839, s2P 408097497566, s2P 229640938060,
   s2P 120941994298, s2P 59555527404, s2P 27644324689, s2P 12320306457, s2P 5469283523,
   s2P 2536273110, s2P 1242479702, s2P 613275309, s2P 288349885, s2N 126805557, s2P 53670926,
   s2P 23227605, s2P 10816962, s2P 5397540, s2P 2754457, s2P 1380999, s2P 667337, s2P 307093,
   s2P 132727, s2P 53260, s2P 19816, s2P 6923]
private def s2St7VecS7 : List ℤ :=
  [s2P 2326, s2P 768, s2N 251, s2P 77, s2P 19, s2P 3, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St7VecS8 : List ℤ :=
  [s2P 0]
private def s2St7Vec : List ℤ :=
  s2St7VecS0 ++
  (s2St7VecS1 ++
  (s2St7VecS2 ++
  (s2St7VecS3 ++
  (s2St7VecS4 ++
  (s2St7VecS5 ++
  (s2St7VecS6 ++
  (s2St7VecS7 ++
  (s2St7VecS8))))))))
private def s2Chk8 : List Rkm128kSeg := s2Take 1 s2Rem8
private def s2Rem9 : List Rkm128kSeg := s2Drop 1 s2Rem8
private def s2St8VecS0 : List ℤ :=
  [s2N 69149845, s2N 172941655, s2N 175025175, s2N 138675343, s2P 36893568, s2P 243779123,
   s2P 127151336, s2P 379025755, s2N 271086991, s2P 176131576, s2P 939188021, s2N 584597428,
   s2N 995077502, s2P 957034413, s2N 138379709, s2P 1422253288, s2N 68416932, s2N 411192022,
   s2P 763626299, s2P 560316116, s2P 3545503735, s2P 2795979634, s2P 1678658248,
   s2P 1574581321, s2N 831735293, s2N 2015872779, s2P 1937279613, s2P 2727842292,
   s2P 5100814117, s2P 943038233, s2P 713476995, s2N 3187150355, s2N 5117738903,
   s2P 1337434029, s2P 6845620624, s2P 9800901595, s2P 6964221206, s2P 852058238,
   s2P 1752174696, s2P 9197287060, s2P 5083247095, s2N 8873889316, s2P 4754190271,
   s2P 4085938701, s2P 3207928820, s2N 9108418758, s2P 3523488053, s2P 10296392587,
   s2P 12917961870, s2N 10676196572, s2N 5877321744, s2N 7777743143, s2P 12399202915,
   s2P 4897064515, s2P 21733719887, s2N 7809701591, s2P 307945913, s2P 29194980591,
   s2P 2034084118, s2P 5742282939, s2N 23031076346, s2N 5426368910, s2N 4192377101,
   s2P 4714043761]
private def s2St8VecS1 : List ℤ :=
  [s2N 51664694806, s2N 39691095621, s2N 6184048518, s2N 16919300696, s2P 22220017811,
   s2P 13256328231, s2P 33630453671, s2P 1612952016, s2N 4718556183, s2N 44406053019,
   s2N 28982667006, s2N 2841040369, s2P 21053481226, s2P 34700253626, s2P 27106648587,
   s2N 871484554, s2P 7841445087, s2P 90788641156, s2P 48822552345, s2N 46611033484,
   s2N 26997549850, s2N 23208951342, s2N 8299821977, s2P 23805309883, s2P 11337817114,
   s2N 25473312969, s2N 40098511053, s2P 4237806332, s2N 11220196291, s2N 64951899658,
   s2N 7401480977, s2N 1781922071, s2P 20002823128, s2P 54549324392, s2N 57854120907,
   s2N 78640438146, s2N 98815621459, s2N 13577234083, s2N 80834572824, s2N 71940352345,
   s2P 65388722057, s2P 18730901764, s2N 65645240595, s2N 67162083889, s2N 90895198893,
   s2P 63102729195, s2N 12848967505, s2N 52972529596, s2N 6540199433, s2N 83103431054,
   s2N 5903480989, s2P 18417299662, s2N 136714706961, s2N 124437590780, s2N 113850642907,
   s2N 98350398593, s2N 38233299532, s2P 51916532301, s2P 37474756493, s2N 65688208069,
   s2N 81851506835, s2P 23061278094, s2N 58563029200, s2N 70455895844]
private def s2St8VecS2 : List ℤ :=
  [s2N 49214499360, s2P 262118501717, s2P 46561112883, s2P 202663063930, s2P 39740112821,
   s2P 27510983610, s2P 44824945002, s2N 197640493263, s2N 99814747996, s2P 120401875586,
   s2P 313697737359, s2P 267931747987, s2P 209136928278, s2P 227636196450, s2P 234637716725,
   s2P 192193632280, s2P 121633892361, s2N 208777546386, s2N 390586647066, s2N 570042552127,
   s2N 671952594596, s2N 114959942245, s2P 322430152179, s2P 113175241743, s2P 64731444167,
   s2N 71602733466, s2N 332476452114, s2N 459646793747, s2N 414056370737, s2N 230266758808,
   s2N 156904451955, s2N 238738189657, s2N 182908601941, s2N 181434401751, s2P 617947143,
   s2P 146873856203, s2N 56193557225, s2N 1138008602536, s2N 644696828222, s2P 126996053537,
   s2P 48709880956, s2N 351000885450, s2N 160117531067, s2N 338784574058, s2N 66716899667,
   s2P 539938408539, s2P 430224743452, s2P 1241762693966, s2P 2421795015467, s2P 2668851680934,
   s2P 3178587037006, s2P 4230429565179, s2P 4487403613379, s2P 2765060402503,
   s2P 696862566605, s2N 742632637983, s2P 860832884340, s2P 3070180133307, s2P 830605233183,
   s2N 1445970544132, s2P 889034399040, s2P 2167093919689, s2N 225146129651, s2N 405615991808]
private def s2St8VecS3 : List ℤ :=
  [s2N 1977808598151, s2N 1278385360229, s2P 484345568529, s2N 1792415218446, s2P 150891587987,
   s2N 792360177718, s2N 1702827531467, s2P 266500734210, s2N 770551248196, s2N 186681080945,
   s2N 172148364307, s2N 1225758102672, s2N 2726005398563, s2N 638763868615, s2P 133292313260,
   s2P 610379136976, s2P 667469218059, s2N 880878818638, s2N 789363417750, s2N 522427950771,
   s2N 2496024804456, s2P 1160890482504, s2P 2001959958728, s2N 1452832041749,
   s2P 514575763497, s2N 510968224014, s2N 1502017346579, s2P 713574114263, s2N 3745197723997,
   s2N 1046152475430, s2N 1484769466507, s2N 518433317816, s2N 472629114408, s2P 1734293379786,
   s2N 329224676989, s2P 312632096396, s2P 628714286981, s2P 2961354682588, s2P 3073565098454,
   s2P 2729306108802, s2P 1188024471157, s2P 4429897799688, s2P 826682177316,
   s2P 2665417714851, s2P 4007101086553, s2P 5564218415205, s2P 3872484838739,
   s2P 1642308611667, s2N 1506016911665, s2N 919120313473, s2P 908002055142, s2N 901166656837,
   s2P 355589233086, s2N 154656143940, s2P 2731218789978, s2P 4603288840295, s2P 4775582235160,
   s2P 818240001563, s2N 939801392542, s2P 818036771229, s2N 779666802828, s2N 1148326280897,
   s2N 158688386410, s2N 3116452162619]
private def s2St8VecS4 : List ℤ :=
  [s2P 273334053809, s2P 136104790043, s2P 5683668298710, s2P 3659950516598, s2N 4773280290105,
   s2N 4406553427218, s2P 1738565845967, s2P 2123070846702, s2P 2390620377683,
   s2P 342248663637, s2N 498443114216, s2N 1590523877718, s2P 1646391318300, s2N 3670135589435,
   s2N 1481454371175, s2P 2175554807032, s2P 5107580115162, s2P 2439344714639,
   s2N 3455319311784, s2N 3960428264477, s2P 211227258268, s2N 4753545169900,
   s2N 3226845836692, s2N 2904813267523, s2N 1903007681392, s2P 3698426735474,
   s2N 1890471540607, s2N 1040554060435, s2N 3769692511772, s2P 360877507836,
   s2N 1907917538584, s2P 827234483654, s2P 1588287005082, s2P 5182041329257,
   s2P 5949460537051, s2P 4206378686359, s2P 8313364649636, s2P 8170875523588,
   s2P 6053774057051, s2N 7494212995342, s2N 14622419213469, s2N 15589835751672,
   s2N 10885606620069, s2P 6567382322117, s2P 2988563147225, s2P 9457284392279,
   s2P 9001586190919, s2P 7709220423728, s2P 6828236836163, s2P 5113891635360,
   s2N 4215305020836, s2P 4291377772312, s2N 1962177921793, s2N 1876428784847,
   s2N 3988476421319, s2P 1049414164212, s2P 2939840296669, s2N 10248083521139,
   s2N 3408197864467, s2P 2950215034604, s2P 8973316218650, s2P 1232386037886,
   s2P 2695767411720, s2P 673646697557]
private def s2St8VecS5 : List ℤ :=
  [s2P 3535645629551, s2P 421546837993, s2N 10158103795681, s2N 10747431499108,
   s2P 12729964784821, s2P 96722164719, s2P 575034699076, s2P 1868044665825, s2P 478735385382,
   s2N 2714131199755, s2N 2302007070147, s2N 2796340353197, s2N 1118439348331,
   s2P 8773344738815, s2P 2814215347179, s2P 10421090227221, s2P 7670720326448,
   s2N 2627854230266, s2N 2444777943048, s2N 10680634191312, s2N 486298004927,
   s2P 8036033669357, s2P 8735265995930, s2N 13786308877742, s2N 8866795957569,
   s2P 8762221312171, s2P 3813534227581, s2P 4479926694135, s2P 753290849652,
   s2N 1811997105038, s2N 2449370448506, s2P 841026351326, s2N 10311073144071,
   s2N 7177750449722, s2N 4817220175710, s2N 5417263107476, s2N 5878352254773,
   s2N 1984985688335, s2N 4821098765154, s2P 3182350557564, s2N 6217170421328,
   s2N 2146054384879, s2N 912277957454, s2N 4788248091765, s2P 3571657309201,
   s2P 2095650604408, s2P 3194088089639, s2N 344158255819, s2N 5475520728885,
   s2P 6861692840719, s2N 9231968151056, s2N 11668332736947, s2N 7971043092990,
   s2P 2137661079914, s2N 1196849782825, s2P 6786071051302, s2N 1714801330816,
   s2N 3860305571424, s2P 7999953888337, s2P 2232780428226, s2P 2660632837108,
   s2N 743046745273, s2N 9093484789465, s2N 7988535375359]
private def s2St8VecS6 : List ℤ :=
  [s2N 11338318090502, s2P 2859821111109, s2P 11591765477774, s2P 13227273875547,
   s2P 3244892837380, s2P 11165304008591, s2P 8392813887745, s2P 1639137729079,
   s2P 900277946689, s2P 3849598149491, s2N 1993677612877, s2N 9031099228989,
   s2N 1081817574023, s2N 6549324251632, s2N 9981776070560, s2P 4186309645663,
   s2P 1189110917091, s2P 6060779529799, s2N 15784722365783, s2P 14769378484575,
   s2P 17122438760722, s2P 63018594033764, s2P 123294494784256, s2P 195939099582480,
   s2P 259378103650893, s2P 308311799795115, s2P 345256626481099, s2P 361069879842475,
   s2P 352885026812135, s2P 331347829767421, s2P 303071951107798, s2P 266106981643344,
   s2P 221737615670876, s2P 177877368267851, s2P 141024595385625, s2P 111333587160361,
   s2P 85754925158372, s2P 62639017765660, s2P 42663087307353, s2P 27091279457972,
   s2P 16269944337462, s2P 9468634922324, s2P 5487954480038, s2P 3231609584297,
   s2P 1941032120184, s2P 1175226544364, s2P 704345542019, s2P 410412194493, s2P 229932130759,
   s2P 123090929481, s2P 62743433709, s2P 30636713468, s2P 14559523444, s2P 6794474068,
   s2P 3078067382, s2P 1326169531, s2P 539945760, s2P 212494463, s2P 85013970, s2P 36424947,
   s2P 16950536, s2P 8327918, s2P 4157954, s2P 2055709]
private def s2St8VecS7 : List ℤ :=
  [s2P 991689, s2N 462409, s2P 207265, s2P 88993, s2P 36392, s2P 14037, s2P 5057, s2P 1694,
   s2P 526, s2P 150, s2N 36, s2P 6, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St8VecS8 : List ℤ :=
  [s2P 0]
private def s2St8Vec : List ℤ :=
  s2St8VecS0 ++
  (s2St8VecS1 ++
  (s2St8VecS2 ++
  (s2St8VecS3 ++
  (s2St8VecS4 ++
  (s2St8VecS5 ++
  (s2St8VecS6 ++
  (s2St8VecS7 ++
  (s2St8VecS8))))))))
private def s2Chk9 : List Rkm128kSeg := s2Take 1 s2Rem9
private def s2Rem10 : List Rkm128kSeg := s2Drop 1 s2Rem9
private def s2St9VecS0 : List ℤ :=
  [s2P 2569969, s2N 73988986, s2N 121892464, s2P 95974398, s2P 340165124, s2P 88714539,
   s2N 118538289, s2P 85392894, s2P 663209898, s2N 343660163, s2P 1239556938, s2P 1265147076,
   s2P 258878769, s2N 30661967, s2P 274241472, s2P 1400538961, s2N 501261679, s2N 245509035,
   s2N 377384889, s2N 1201996388, s2P 9544871, s2P 1669926785, s2N 1537182957, s2N 197701194,
   s2P 2572727386, s2P 2201415205, s2P 3620472190, s2P 2761925949, s2N 1803074187,
   s2N 778140610, s2P 112970078, s2P 266939334, s2P 3038801522, s2P 4675856845, s2P 4527986360,
   s2P 1659706090, s2N 641301682, s2P 12578869257, s2N 2439414741, s2N 7370417016,
   s2N 9213881522, s2N 3722291532, s2N 7636313489, s2N 5697614476, s2P 13715759604,
   s2N 8488038559, s2P 4290315662, s2P 270245511, s2N 14389200737, s2N 5095957796,
   s2P 14176391497, s2P 13712631566, s2N 9690843382, s2N 22136187290, s2N 5135920608,
   s2P 2065016867, s2P 21152842140, s2P 5735457283, s2P 6825999874, s2N 2668579128,
   s2N 17937097473, s2N 27354775174, s2N 22035691632, s2N 23718376040]
private def s2St9VecS1 : List ℤ :=
  [s2P 18721934743, s2P 17284618511, s2P 400722745, s2N 4894246459, s2P 6002609205,
   s2P 90919474, s2P 21900721173, s2P 29279011448, s2P 32304414976, s2P 23426722465,
   s2P 30791490876, s2P 3208406065, s2N 37827706430, s2P 4980007176, s2P 34393543349,
   s2P 16906402484, s2N 68349180474, s2N 44274029309, s2N 20934034060, s2P 26671227807,
   s2P 7680352086, s2N 22177909849, s2P 25080883812, s2N 24734153732, s2N 58385357063,
   s2N 92231833417, s2N 35656725380, s2N 7632354771, s2N 22803303920, s2N 11741370713,
   s2P 1061576310, s2P 9025661309, s2N 6694281780, s2P 29560724451, s2P 8664829964,
   s2P 45672163257, s2P 126442718833, s2P 40458056927, s2N 16854234210, s2N 11617538072,
   s2N 39805836325, s2N 39440248789, s2N 14035878770, s2N 26549912716, s2N 149629275427,
   s2N 96430869255, s2P 41820510387, s2P 20426758194, s2N 29710488537, s2N 3905267196,
   s2N 96463433690, s2N 53020024378, s2P 12355342120, s2N 39982596065, s2P 102748434166,
   s2N 26644138841, s2P 93549375503, s2P 57073273612, s2N 102586589261, s2N 86447631790,
   s2N 5640052266, s2P 249809629295, s2P 82127790401, s2N 98897692837]
private def s2St9VecS2 : List ℤ :=
  [s2P 39795974053, s2P 41337353286, s2N 54439149624, s2N 20094121220, s2N 61009790010,
   s2N 68335734217, s2N 136826086670, s2N 89694726753, s2N 54907985676, s2P 23641334171,
   s2N 13035978668, s2N 199025523093, s2N 198142658376, s2N 152219781028, s2P 60384879889,
   s2P 252854642579, s2P 78025399239, s2P 83103765433, s2P 28680302888, s2N 155617464319,
   s2P 302747874429, s2P 121020433842, s2P 144949007803, s2P 332676029483, s2P 549323367620,
   s2P 203694039334, s2N 102140385345, s2N 546736497281, s2N 408766823240, s2N 625523665659,
   s2N 194853248276, s2P 150154835128, s2N 60768837151, s2N 78135806325, s2N 190417384266,
   s2P 424625097442, s2P 682485999705, s2N 186963781839, s2N 64534238907, s2P 750010822015,
   s2P 431316158617, s2N 227314678383, s2N 229973616035, s2N 343525573700, s2N 149783743596,
   s2N 838737983120, s2N 304641781006, s2N 41070983721, s2N 619865586928, s2N 162014876445,
   s2N 43655955196, s2N 280350744109, s2N 356630547092, s2N 264803176977, s2N 1037170752137,
   s2N 1399442241910, s2N 1395276726135, s2N 1949870919991, s2N 2196021911071,
   s2N 4450638755193, s2N 5042999850033, s2N 4064814637624, s2N 581675477313,
   s2P 2783760746889]
private def s2St9VecS3 : List ℤ :=
  [s2P 2681040316040, s2P 1145988229176, s2N 440400553162, s2P 811275225648, s2N 429067963150,
   s2N 1833491763045, s2N 1554561129998, s2N 215098878626, s2N 88784043758, s2N 279779398423,
   s2N 1660325220569, s2P 18573102030, s2N 551812972595, s2N 1063642505350, s2N 143385537018,
   s2P 2638137064645, s2P 536549834881, s2N 2442820851066, s2N 2562202934367, s2P 735732944540,
   s2N 1814767857259, s2N 1773254578284, s2N 1640894970632, s2N 103724913716, s2P 173183356538,
   s2P 1774480321687, s2N 1409830049418, s2N 1447730202754, s2N 836375394340, s2N 247939885828,
   s2N 1197109909213, s2P 1124959413331, s2N 914900187047, s2N 1343933748285, s2P 703561499012,
   s2N 30308933910, s2N 84558180030, s2N 2171216697767, s2N 3215613816761, s2N 848418374844,
   s2P 220684851331, s2N 1550068107695, s2N 149071112867, s2N 1077446258652, s2P 707832874158,
   s2P 362051919684, s2N 823331146397, s2N 2622663330242, s2N 3779626678689, s2N 2433471037979,
   s2P 231023875667, s2N 1299660437731, s2P 3440760061213, s2P 3999748243880,
   s2P 7402666253374, s2P 1470638689688, s2P 2199103823448, s2N 2240270923022,
   s2P 1330532003645, s2N 72167134881, s2N 2766844868145, s2N 1665262321332, s2N 2435770973864,
   s2N 719755618656]
private def s2St9VecS4 : List ℤ :=
  [s2P 4519725179875, s2P 4284491307040, s2P 1354359985661, s2P 1832526019132,
   s2P 4870129093580, s2N 1983733625337, s2N 2574377634362, s2N 4358717553219,
   s2N 3020561386718, s2N 1881143009531, s2N 5522279784332, s2N 679444465314, s2N 643732706200,
   s2P 2933395853452, s2N 370892153236, s2N 2888844090803, s2P 4098343751501,
   s2P 3002219598381, s2P 2386667062628, s2P 2952103349591, s2P 3473372388318,
   s2N 3270436380703, s2P 1987913939524, s2P 2648431755735, s2P 2560465812451, s2N 6880117989,
   s2P 2093149912917, s2P 412256776122, s2N 816592462561, s2N 4935812920214, s2N 4506217400693,
   s2N 2528192313155, s2P 2162961518651, s2P 1214529521704, s2N 4682900798033,
   s2P 4126988765189, s2P 3337452863558, s2N 2888914908864, s2N 2240843067688,
   s2N 1287480410058, s2P 660869102830, s2P 4825798216962, s2P 5557245072317,
   s2P 4996063363034, s2P 8755149088641, s2P 14241565919013, s2P 13153053681696,
   s2P 1878822970708, s2N 7757589820718, s2N 15405475662191, s2N 7148324116192,
   s2N 9627852498107, s2N 3477007695159, s2N 4564996875131, s2N 11295700654535,
   s2N 4232929493278, s2P 6028438748177, s2P 9980321614471, s2P 7670346402261,
   s2N 5698135834221, s2P 3180205370267, s2P 3595845528029, s2P 6282753310376,
   s2P 2038495876503]
private def s2St9VecS5 : List ℤ :=
  [s2N 12478588729416, s2N 4255851222094, s2N 4900529386718, s2N 1124240855914,
   s2P 6629249046557, s2P 7519691952842, s2P 6170365023064, s2N 6933639654133,
   s2N 832798363924, s2N 8477911153631, s2N 1008189327768, s2N 5329780643297, s2P 102812632036,
   s2P 968879497024, s2P 4053145235010, s2P 593766707082, s2N 1830097014738, s2N 698177900973,
   s2P 8105193223183, s2P 3222856210383, s2N 4367359372691, s2P 3853175926812,
   s2P 13066584060764, s2P 19418498983023, s2P 2060491943725, s2P 6515672266237,
   s2P 4124497397369, s2P 3432477443556, s2P 6074713311367, s2N 597927046120,
   s2N 10366070496966, s2P 406246081386, s2N 1615159259407, s2P 2647847618513,
   s2P 2311973156474, s2N 140020952172, s2P 7491606874826, s2P 1211049065563,
   s2N 2563308097985, s2P 1037973033955, s2N 8219336054800, s2N 2428274699289,
   s2N 11741332333327, s2P 1804885008448, s2P 6432844814790, s2P 4322526670878,
   s2N 666605916245, s2P 1777281678189, s2N 10703304028673, s2N 4130076055489,
   s2P 4958595384125, s2P 4556764201722, s2P 1307663413274, s2P 554906790082, s2N 967693435972,
   s2P 8977843319583, s2N 3365856900831, s2N 7156034904149, s2N 11501640737944,
   s2P 3677694231347, s2P 2078289105909, s2N 570686874798, s2N 4091606325432,
   s2P 1718125941610]
private def s2St9VecS6 : List ℤ :=
  [s2P 500899197407, s2N 352450664823, s2P 9187217618791, s2P 8518651548517, s2N 4406186326303,
   s2N 14357653551264, s2N 6396501200608, s2N 3240139571429, s2N 6899060455514,
   s2N 14460670793532, s2P 2512965647583, s2P 14601784013382, s2P 6172129992,
   s2P 17962259387244, s2N 1089803628607, s2N 1370409828398, s2P 8295795660766,
   s2P 1539408134729, s2N 9418982483220, s2N 7834200442608, s2N 3030340623805,
   s2N 1463326526740, s2P 743466035315, s2N 2674366944782, s2N 5510109823635,
   s2N 17128052109455, s2P 11427797212927, s2P 18804230084756, s2P 67286639208949,
   s2P 130054636261804, s2P 202164289403109, s2P 269974804393040, s2P 319899916482607,
   s2P 348849510046435, s2P 360258724490644, s2P 355423721706049, s2P 333557975578246,
   s2P 297266889203131, s2P 253713840465615, s2P 210347488451688, s2P 171032013641336,
   s2P 136119007979390, s2P 104877672115191, s2P 77272656235486, s2P 54030851044586,
   s2P 35821575592654, s2P 22640307284794, s2P 13783156101827, s2P 8189816953983,
   s2P 4810891811388, s2P 2818013234912, s2P 1648932061162, s2P 959129551436, s2P 549658231559,
   s2P 307462421499, s2P 166719307305, s2P 87351891170, s2P 44214861780, s2P 21644048987,
   s2P 10251726169, s2P 4696031536, s2P 2077785595, s2P 889846748, s2P 370554790]
private def s2St9VecS7 : List ℤ :=
  [s2P 151380298, s2P 62100677, s2P 26223022, s2P 11268224, s2P 4718863, s2P 1878052,
   s2P 728511, s2P 293733, s2P 128281, s2P 58970, s2P 26887, s2P 11646, s2P 4681, s2P 1723,
   s2P 576, s2P 172, s2P 43, s2P 9, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St9VecS8 : List ℤ :=
  [s2P 0]
private def s2St9Vec : List ℤ :=
  s2St9VecS0 ++
  (s2St9VecS1 ++
  (s2St9VecS2 ++
  (s2St9VecS3 ++
  (s2St9VecS4 ++
  (s2St9VecS5 ++
  (s2St9VecS6 ++
  (s2St9VecS7 ++
  (s2St9VecS8))))))))
private def s2Chk10 : List Rkm128kSeg := s2Take 2 s2Rem10
private def s2Rem11 : List Rkm128kSeg := s2Drop 2 s2Rem10
private def s2St10VecS0 : List ℤ :=
  [s2N 20491785, s2N 23547578, s2P 80496882, s2P 193772846, s2P 16675830, s2P 313802682,
   s2N 8290503, s2P 319689583, s2P 820109654, s2P 380716944, s2P 170521895, s2N 927930535,
   s2N 42317405, s2N 671684408, s2N 945312045, s2N 766669574, s2N 988899062, s2P 1554606158,
   s2P 1935664891, s2N 180247538, s2N 965752325, s2P 1149404998, s2N 230974292, s2N 768296253,
   s2P 2275947978, s2P 1543648732, s2N 1165485181, s2N 1663097336, s2P 1132556543,
   s2P 1142179325, s2N 321962225, s2P 268520438, s2P 2884535495, s2N 1821915409,
   s2P 1477006826, s2P 6705286515, s2P 7222043432, s2N 2146324487, s2P 995412730,
   s2N 5370350535, s2N 1294097313, s2P 1961481371, s2N 4749470196, s2N 14375991460,
   s2N 14207807485, s2N 7292395117, s2N 10182907198, s2P 1345517290, s2P 6842127703,
   s2P 9898629515, s2N 535875295, s2N 16100097616, s2N 19864100653, s2N 1198400518,
   s2P 3756647343, s2P 14017617837, s2P 4909347312, s2P 3887168732, s2P 9439837493,
   s2P 14898595187, s2P 6706404790, s2P 2687092926, s2N 3552677152, s2N 19321002429]
private def s2St10VecS1 : List ℤ :=
  [s2N 13286298839, s2N 6004716239, s2N 16278173731, s2P 7617357753, s2N 21892082681,
   s2N 20324480753, s2N 478345525, s2P 169007489, s2N 27083130703, s2N 14363060735,
   s2P 11124937797, s2P 44378438039, s2P 10910905048, s2N 2654221140, s2P 8996145241,
   s2N 27221151011, s2P 12512882557, s2N 41834473232, s2N 46583814974, s2P 23903984957,
   s2N 53801765558, s2N 43238572295, s2N 48543821592, s2N 37796175553, s2P 8744291116,
   s2N 28331936709, s2N 8306342425, s2P 49885216173, s2P 47185720126, s2N 43134042389,
   s2N 16867298201, s2P 55662880976, s2N 27845895611, s2P 4599004725, s2P 27083858512,
   s2P 438208263, s2P 21622420129, s2N 79954570560, s2N 1659026003, s2N 23669163823,
   s2N 31456472832, s2N 22059601806, s2N 7659436493, s2N 87731624338, s2P 22675529982,
   s2P 21757799592, s2N 121808607278, s2N 9795077986, s2P 134604028738, s2P 82160080948,
   s2P 67693285252, s2P 18513426478, s2P 33836002639, s2P 3649879131, s2N 52239825560,
   s2P 41271513300, s2P 103284332657, s2P 118913080440, s2P 6883085391, s2P 110017176163,
   s2P 35777928341, s2N 46022282647, s2N 82962081586, s2P 88420886416]
private def s2St10VecS2 : List ℤ :=
  [s2N 94359899288, s2N 92053976644, s2N 224990357837, s2P 17387298823, s2P 37941638999,
   s2P 106235783935, s2N 37044858908, s2N 52922586421, s2P 14040986747, s2N 79315871726,
   s2N 7688890244, s2N 22193023385, s2N 40337879502, s2N 158258663186, s2N 59859909128,
   s2N 35107815376, s2N 45788395967, s2P 38049736639, s2P 236467482501, s2P 178113167840,
   s2P 73326533595, s2P 243907383802, s2P 202185699735, s2P 196584992970, s2P 47993123446,
   s2N 4555865388, s2P 189692776425, s2P 305177446088, s2N 151617365971, s2N 485785091861,
   s2N 53847009047, s2N 340213960626, s2N 21582330391, s2N 149558873258, s2P 69027010519,
   s2P 87465433855, s2P 69223247310, s2P 250321406499, s2P 188036595017, s2P 642626636342,
   s2P 1033617303145, s2P 734196210196, s2N 391558097757, s2N 518841467774, s2N 136759206145,
   s2P 326984792379, s2P 365394756044, s2P 137636639586, s2P 185521064076, s2N 396228201952,
   s2P 175927803341, s2P 90013229070, s2P 691545978036, s2N 55855636936, s2P 437048765910,
   s2P 455677863069, s2P 117814059381, s2N 296993233869, s2N 240205843228, s2N 126039199175,
   s2N 692888523111, s2N 464659450698, s2P 10038179214, s2P 1007478748137]
private def s2St10VecS3 : List ℤ :=
  [s2P 1568762350074, s2P 740693981705, s2N 279535147538, s2N 1375863641101, s2N 1668780021515,
   s2N 2146188931292, s2N 488095984708, s2P 1742043023185, s2N 35304215981, s2N 5529328956730,
   s2N 2262016357041, s2P 5601547111339, s2P 3858329019669, s2N 2565193231256,
   s2P 1152116438898, s2P 492359976936, s2P 2373931701310, s2P 1238482545202,
   s2N 1251497181181, s2N 445632664969, s2N 1522523496141, s2P 818998297986, s2P 1315225556554,
   s2N 1053748944455, s2P 514404652160, s2N 1155105146863, s2N 503607322881, s2P 546616741317,
   s2P 1876430361909, s2N 1835895827820, s2P 1001715279224, s2N 2968275199462,
   s2N 485419332950, s2P 1020834982473, s2P 87198387669, s2N 948480029269, s2P 354687040304,
   s2P 1448204131709, s2N 821738636692, s2N 1587546768241, s2N 863017922221, s2N 278975949143,
   s2N 3271763319413, s2P 917889268543, s2N 1471217914575, s2N 1572944847196,
   s2N 1105394459758, s2P 495090183698, s2P 2057237115852, s2N 1405033660368,
   s2N 2597514824399, s2P 941830242919, s2P 1500734197298, s2P 1042392227641, s2N 936856397697,
   s2N 3280398619903, s2P 1177440661578, s2N 230824344054, s2P 1047330854874, s2P 432207291414,
   s2P 1387739073749, s2N 548873502693, s2N 709548848288, s2P 28108827266]
private def s2St10VecS4 : List ℤ :=
  [s2P 5159665005216, s2P 8005956674451, s2P 2432964660689, s2P 5030450006939,
   s2P 3201468409208, s2N 949051308008, s2P 1654980485938, s2P 3030108721324,
   s2P 3363879692182, s2P 1917112206256, s2P 1157653103676, s2N 387536339202, s2N 16116994807,
   s2N 1336290444541, s2P 1063402414788, s2P 3676735811928, s2P 1235910102846,
   s2P 1304539523542, s2P 7949282451972, s2P 5581744703846, s2P 2278394406719,
   s2P 3124705961750, s2P 5121758338245, s2P 4053467992092, s2N 2167310631387,
   s2N 1042541732321, s2N 53897410871, s2N 3138542816713, s2N 1067911556976, s2P 298961339235,
   s2N 2436489930354, s2P 248586340141, s2P 4318154115456, s2P 1483912450571, s2P 36177847818,
   s2N 1555230336991, s2P 2305144047251, s2P 1736237133886, s2N 1908321852418,
   s2N 7213135725501, s2N 3504574946723, s2P 534715517656, s2N 1910654620465, s2N 899433909932,
   s2N 8355208609079, s2N 1750772231487, s2N 4584719033334, s2N 733126564261,
   s2N 2561506468258, s2P 953013504115, s2P 2721930784203, s2P 2492947267987,
   s2P 3706217574850, s2P 3175277270097, s2N 3409553509560, s2P 12472914147333,
   s2P 2389492261840, s2P 4121423272322, s2N 5782348006404, s2N 15690039920457,
   s2N 18220268556702, s2N 5415527906643, s2N 8998060882960, s2N 12444745914603]
private def s2St10VecS5 : List ℤ :=
  [s2N 9807170345289, s2P 3460154898560, s2P 15612649079308, s2P 3394272155715,
   s2N 4063509981727, s2N 2976635013376, s2N 1293784692660, s2N 4249854255300,
   s2N 11338223538760, s2P 86481949361, s2P 7662523197415, s2N 1182300297273,
   s2P 1588938753984, s2P 1300131899255, s2P 8777478918598, s2P 5270751060317,
   s2P 8482934287085, s2P 937573675923, s2N 113098511410, s2N 6377546879798, s2P 2483936731986,
   s2P 856735474323, s2N 6275986447285, s2N 2758092479718, s2N 12523783837457,
   s2N 12543170353929, s2N 7840150849971, s2P 10534102981391, s2P 4626305218785,
   s2P 13912194876990, s2P 4134053939345, s2N 778410131399, s2N 2728516033375,
   s2N 5911320403022, s2N 4031932053451, s2P 1440020720698, s2N 2916005315840,
   s2P 5778845066388, s2P 5105209411446, s2P 1723945257078, s2P 8841833696145,
   s2P 3491459637196, s2N 32992127437, s2N 1450520810093, s2P 8019769036727, s2N 545993892828,
   s2N 1191185996425, s2P 12962703803035, s2N 1820877119547, s2P 5913939134798,
   s2N 1903017868694, s2P 3558375521495, s2P 6690455123161, s2N 8078799863304,
   s2N 943761228584, s2P 1231586476883, s2N 10641120128936, s2N 2405772068797,
   s2N 1287384899349, s2P 3238260386086, s2N 10124469694657, s2P 1155357967606,
   s2P 2644947595900, s2N 4787131168599]
private def s2St10VecS6 : List ℤ :=
  [s2N 2394976095163, s2P 2577396518839, s2P 5641398820171, s2P 6897172041017,
   s2P 4732189291846, s2P 2624979074546, s2P 4515453015188, s2P 2515926085999,
   s2P 8811028906629, s2N 6375584135428, s2N 10366697365650, s2N 13875281118147,
   s2N 6256206738095, s2N 14279504980494, s2P 1138619132793, s2N 2436738151973,
   s2P 15608918455417, s2N 8766224829830, s2P 10477769615972, s2P 13826320661294,
   s2P 1486648763216, s2N 1678561707551, s2P 2638458004191, s2P 8264841469516,
   s2N 9826745587104, s2P 3113067249252, s2P 1594087450307, s2P 3401575572702,
   s2P 8043541048740, s2P 3022213373987, s2P 5374575289318, s2P 4048630614232,
   s2N 7432821830565, s2P 908233022670, s2P 15989045585795, s2P 15624358276438,
   s2P 664013478820, s2P 7571104900315, s2P 13909200810102, s2P 63686119720952,
   s2P 130184851192575, s2P 201389768204261, s2P 268328139654805, s2P 323135756614110,
   s2P 358445751080225, s2P 369934462226483, s2P 358666623775795, s2P 330331126676898,
   s2P 292106470766252, s2P 249842056717890, s2P 207176031296583, s2P 166207346561414,
   s2P 128451108242015, s2P 95246708119413, s2P 67611467995776, s2P 45953806923564,
   s2P 29980201479632, s2P 18856699696824, s2P 11498871528801, s2P 6838826347264,
   s2P 3987407125624, s2P 2286972398767, s2P 1291717434447, s2P 717700386862]
private def s2St10VecS7 : List ℤ :=
  [s2P 391279023348, s2P 208666976124, s2P 108531133994, s2P 54931783856, s2P 26983567024,
   s2P 12899068362, s2P 5925290589, s2P 2674034400, s2P 1185768426, s2P 485726773,
   s2N 175592617, s2P 57987818, s2P 19744807, s2P 7747138, s2P 3394230, s2P 1504900,
   s2P 642042, s2P 263319, s2N 104504, s2P 41405, s2P 16258, s2P 5912, s2P 1904, s2P 556,
   s2P 156, s2P 43, s2P 11, s2P 1, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0]
private def s2St10VecS8 : List ℤ :=
  [s2P 0]
private def s2St10Vec : List ℤ :=
  s2St10VecS0 ++
  (s2St10VecS1 ++
  (s2St10VecS2 ++
  (s2St10VecS3 ++
  (s2St10VecS4 ++
  (s2St10VecS5 ++
  (s2St10VecS6 ++
  (s2St10VecS7 ++
  (s2St10VecS8))))))))
private def s2Chk11 : List Rkm128kSeg := s2Take 2 s2Rem11
private def s2Rem12 : List Rkm128kSeg := s2Drop 2 s2Rem11
private def s2St11VecS0 : List ℤ :=
  [s2N 29798422, s2N 90216954, s2N 147055047, s2P 86472385, s2N 89530182, s2N 38218857,
   s2N 198115701, s2N 196777713, s2N 21370564, s2N 679012030, s2N 595114022, s2N 929424102,
   s2N 186361771, s2P 974454045, s2P 784362644, s2N 1644418329, s2N 2408899285, s2N 1033420194,
   s2N 718478526, s2N 305555016, s2N 485210783, s2N 117377659, s2N 931482362, s2P 77115081,
   s2N 272049732, s2P 925456026, s2N 663223043, s2N 23743918, s2P 848496464, s2P 3678096028,
   s2P 540394614, s2P 1489628771, s2P 1787911443, s2P 4053843537, s2N 684375700,
   s2N 2859018562, s2N 327275488, s2N 5266229394, s2P 299284353, s2N 5092629850, s2P 232036142,
   s2N 1399773922, s2P 6094650072, s2P 1127984119, s2P 5850496951, s2P 2125298990,
   s2P 11839810033, s2N 1956425254, s2N 2203905959, s2P 4943436935, s2P 4168690939,
   s2P 8826448008, s2P 16481881067, s2P 5009515920, s2N 12378072324, s2N 11154837964,
   s2P 11619182054, s2N 3616008432, s2N 11854089879, s2N 10515873321, s2P 6792358228,
   s2P 22432533124, s2N 593816520, s2N 13371045597]
private def s2St11VecS1 : List ℤ :=
  [s2P 1151390851, s2P 4673137623, s2N 7687341614, s2N 21048062669, s2N 15947156833,
   s2N 4012845855, s2N 1305037756, s2N 7243303577, s2P 21899679522, s2P 5752197999,
   s2P 4796383258, s2P 868426231, s2N 10452256940, s2N 19605769786, s2N 510180094,
   s2P 36696227429, s2P 57899114289, s2P 23675252252, s2N 30779371974, s2N 12636224965,
   s2N 57495191783, s2N 375761395, s2P 42370509286, s2P 39174420354, s2P 54237907365,
   s2P 60189470012, s2N 23081079541, s2N 11352279133, s2P 17971227243, s2P 16277066882,
   s2P 1975607881, s2N 34277106739, s2N 67941324929, s2P 33483036039, s2N 77902512996,
   s2N 37169252253, s2N 7676682135, s2P 22557783507, s2P 16299494936, s2N 43982467685,
   s2N 35774091394, s2N 8594352542, s2P 8287178427, s2N 15844516574, s2N 71525717585,
   s2N 74118970611, s2N 99265074540, s2N 42951193693, s2N 2079518559, s2P 67233241648,
   s2P 21622983200, s2P 33384358425, s2P 28974556571, s2N 51372343825, s2P 42968613717,
   s2P 64239196015, s2N 15425021303, s2N 78703145200, s2N 48286947566, s2P 2188272774,
   s2N 86415082135, s2P 20761082967, s2N 90570010110, s2N 128124740203]
private def s2St11VecS2 : List ℤ :=
  [s2N 148824132074, s2N 37301448002, s2N 85978716, s2N 8032324241, s2N 148953671119,
   s2N 134166140619, s2N 1161669805, s2N 14993082510, s2P 27397465618, s2P 163362823982,
   s2N 80121667528, s2P 22547535702, s2P 130435136592, s2P 46452745442, s2P 55558798388,
   s2N 112464721148, s2N 106757333586, s2N 56863430985, s2N 4809668492, s2N 55162187327,
   s2P 62150951341, s2N 144978835249, s2N 85574316480, s2P 22403052378, s2P 8675731908,
   s2P 171360286087, s2P 316140265648, s2P 268645823367, s2N 78255223301, s2N 312007838275,
   s2N 46705541207, s2N 225092963769, s2N 111666336104, s2N 352075618600, s2N 174163615453,
   s2P 138161995286, s2P 59961502720, s2N 44743984816, s2N 252012628190, s2N 340484843792,
   s2N 142534391189, s2P 364570625967, s2P 20591198409, s2N 267567722901, s2P 157367178097,
   s2P 317070808730, s2P 64315384527, s2P 342587993582, s2P 113058237255, s2N 193055240458,
   s2N 886266526553, s2N 1060100211317, s2N 926042151760, s2P 54308519930, s2P 610420080804,
   s2P 255219209661, s2N 178035356078, s2N 351166621830, s2N 199436617936, s2P 20579761401,
   s2N 99700562385, s2N 451198256711, s2N 32731061021, s2P 126497823360]
private def s2St11VecS3 : List ℤ :=
  [s2P 232459470085, s2P 475764168959, s2N 1167775565928, s2N 301303098361, s2N 333211641960,
   s2N 374364755374, s2N 449288453956, s2N 224403606481, s2P 553114374742, s2P 1424709880252,
   s2P 2008559462415, s2P 2574649502630, s2P 1292404302596, s2P 1337972265517,
   s2N 827877237966, s2N 3286634986630, s2N 6104691361919, s2N 4845071765932,
   s2N 3367681127402, s2N 214734809024, s2P 3460696290595, s2P 1913549546574, s2P 687962138232,
   s2N 683610123306, s2P 361069109064, s2P 441961518638, s2P 498607949274, s2N 117149950121,
   s2P 1304523538597, s2P 2214135709584, s2P 3599974253578, s2N 138939087130, s2N 721132287304,
   s2N 317831153303, s2P 644933137039, s2P 1290750322338, s2P 1184268248543, s2N 1292624589701,
   s2P 154933741538, s2N 175958853935, s2N 429720514148, s2N 3053539082198, s2P 396819422117,
   s2N 3303436773900, s2P 833401903954, s2P 2478241794267, s2P 658233577482, s2N 1259494635174,
   s2P 921186209925, s2N 1197724569420, s2P 404803611853, s2P 46378233324, s2N 625094818048,
   s2N 3248549809601, s2N 994601160594, s2N 723988273442, s2N 1955637640330, s2P 1742332592813,
   s2N 122210983343, s2P 406998808006, s2P 1042008416690, s2P 2817813571577, s2N 507214881394,
   s2P 3443193445588]
private def s2St11VecS4 : List ℤ :=
  [s2P 1705366604663, s2N 1340936120049, s2P 3327827859169, s2P 3458797379813,
   s2P 1337464698518, s2N 3980899504486, s2N 318573752063, s2P 3060110557362,
   s2P 3480391012312, s2P 33865015919, s2P 2183925927548, s2P 3993061388038, s2P 6802233455662,
   s2N 12704054868, s2N 5127734356972, s2N 1546034764988, s2N 587063083587, s2P 2206974082395,
   s2N 398158030312, s2N 1587438126553, s2N 875096479313, s2P 2539791371782, s2P 1738906194246,
   s2N 101856929794, s2N 3699809896768, s2P 531642983032, s2N 315029114705, s2N 613802847898,
   s2N 4244689528695, s2N 2638630175755, s2N 1993232780568, s2P 3999816525710,
   s2P 6222840004728, s2N 4171345778451, s2N 4369376190583, s2N 6002775746895,
   s2N 1363701594322, s2P 1160421960040, s2N 1043039940008, s2P 5483035098312,
   s2P 4757943377641, s2P 4466241721761, s2P 342836386994, s2N 1158585287762,
   s2P 2362693246244, s2P 761378159816, s2N 6310737190695, s2N 1300350428078,
   s2P 1412824212191, s2P 1826908704460, s2P 9567259198922, s2P 2761016339711,
   s2P 3029858846754, s2P 2172870383722, s2P 84472025238, s2P 4670009105260, s2N 7245461693188,
   s2N 3390738747799, s2N 3543943682417, s2N 7514663349677, s2N 1901564015131,
   s2P 1906308833224, s2P 9360281206308, s2P 4553180664802]
private def s2St11VecS5 : List ℤ :=
  [s2P 3952897223063, s2N 2174811500063, s2N 1742850914, s2P 14111881363501,
   s2P 16105299996193, s2P 6462340017100, s2N 3722897705640, s2P 4100179819426,
   s2P 7645813218936, s2P 11969217056206, s2P 15256751923711, s2P 14110299072473,
   s2P 6487386531485, s2P 4119836399915, s2P 360025915861, s2N 1402844089221,
   s2N 8394121225200, s2N 5511478545377, s2P 8504919218387, s2P 4277644215430,
   s2P 296997116817, s2P 78872404822, s2N 3633482545166, s2P 5859473753406, s2P 6184999240048,
   s2P 6113792017073, s2P 5193928778025, s2P 8868444409193, s2P 11460984303348,
   s2P 1689663549817, s2N 3562326200698, s2N 2314420324102, s2N 2787184414031,
   s2N 2973678758270, s2N 9525377035234, s2N 16636685749905, s2N 9376365257582,
   s2P 4196110963234, s2P 4799632751365, s2P 2987409066304, s2P 12723132655886,
   s2P 7881029831851, s2N 7476849729668, s2N 738735220357, s2P 3710708350346,
   s2N 5637928840519, s2N 1167627504293, s2N 9347278760706, s2N 7757048333177,
   s2N 443313095979, s2N 5415085534854, s2N 8095084804031, s2N 2502567563484, s2N 130455115961,
   s2P 8387805773829, s2P 3428572764688, s2N 8550453634264, s2P 473680775574,
   s2N 2019403658850, s2N 7032520094948, s2N 7947821766086, s2N 5532413710422,
   s2N 7455053156225, s2P 2507370606332]
private def s2St11VecS6 : List ℤ :=
  [s2N 2621500934786, s2P 4115017643313, s2P 5992971824126, s2N 2551570293475,
   s2N 7989770129790, s2P 495765604786, s2P 2927912035309, s2P 6678024062661,
   s2P 2881085013167, s2N 4565703298811, s2N 930932708051, s2N 9082945551495,
   s2P 17439398717596, s2N 7472420315416, s2P 4669031890399, s2P 20105044146771,
   s2P 2187556231361, s2P 8357267472800, s2P 7470771072909, s2N 949362184891,
   s2N 8378615222576, s2P 11108483563293, s2N 6144318104761, s2N 5882664350851,
   s2P 4747595950427, s2P 8183927531716, s2P 5630615896868, s2P 2649074129913,
   s2N 8061792280403, s2P 3041860395827, s2N 6911976385884, s2N 3183106530828,
   s2N 6376805470983, s2N 7679936655722, s2N 8591057289249, s2P 2951647743834,
   s2N 665672568751, s2P 16098113660541, s2N 5360323265984, s2P 1663986613717,
   s2P 3119790413128, s2P 4181379907856, s2P 12963135590326, s2P 15589746113473,
   s2P 3730187556952, s2P 9512836105112, s2P 6374278747332, s2P 22086531660035,
   s2P 75322533218093, s2P 146268913192085, s2P 223345454822892, s2P 293019571690344,
   s2P 343787933144800, s2P 369636252171265, s2P 370821128717007, s2P 351955709360389,
   s2P 319177851300527, s2P 278145897973453, s2P 233383753450541, s2P 188451031158160,
   s2P 146209195243946, s2P 108841464287300, s2P 77704737822494, s2P 53240748985794]
private def s2St11VecS7 : List ℤ :=
  [s2P 35074871594758, s2P 22282284431316, s2P 13693536413072, s2P 8182164513497,
   s2P 4741849438305, s2P 2726773856541, s2P 1481701889642, s2P 820931097877, s2P 459747628213,
   s2P 226437523748, s2P 92911226152, s2P 35136179275, s2P 15126491421, s2P 7873570108,
   s2P 4219419507, s2P 2066132572, s2P 901391046, s2P 356034409, s2P 131485676, s2P 47315671,
   s2P 17256381, s2P 6479196, s2P 2462027, s2P 919599, s2P 333381, s2P 117825, s2P 42356,
   s2P 15532, s2P 5380, s2P 1665, s2P 469, s2P 129, s2P 36, s2P 9, s2N 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St11VecS8 : List ℤ :=
  [s2P 0]
private def s2St11Vec : List ℤ :=
  s2St11VecS0 ++
  (s2St11VecS1 ++
  (s2St11VecS2 ++
  (s2St11VecS3 ++
  (s2St11VecS4 ++
  (s2St11VecS5 ++
  (s2St11VecS6 ++
  (s2St11VecS7 ++
  (s2St11VecS8))))))))
private def s2Chk12 : List Rkm128kSeg := s2Take 2 s2Rem12
private def s2Rem13 : List Rkm128kSeg := s2Drop 2 s2Rem12
private def s2St12VecS0 : List ℤ :=
  [s2N 27460617, s2N 84309234, s2N 148222860, s2N 97703395, s2N 42770016, s2P 132982864,
   s2P 220238726, s2N 250154127, s2P 155209103, s2P 95737822, s2P 44472758, s2P 183798157,
   s2P 68818532, s2P 343717773, s2P 1448974679, s2P 2214287644, s2P 2034065634, s2N 1044422411,
   s2P 302384346, s2N 376047916, s2N 336955685, s2N 85345275, s2P 1465555069, s2N 395051012,
   s2P 1005903468, s2P 861128666, s2N 858388931, s2P 689146528, s2N 668294352, s2N 3760730104,
   s2N 9153846, s2N 2685336876, s2N 3971042356, s2P 2660795480, s2P 44012440, s2P 1240824449,
   s2P 2615557730, s2N 1017712245, s2N 5082593272, s2N 6141620318, s2P 3656957152,
   s2N 3582253213, s2N 1088436296, s2N 5392182130, s2N 1184376901, s2N 8810994425,
   s2P 5369117168, s2P 7093085421, s2N 5598362715, s2P 7566100142, s2N 4772988851,
   s2N 5333914683, s2N 383261691, s2P 2860388631, s2N 2835559967, s2P 3270070396,
   s2N 197613130, s2N 5903650968, s2N 19941821337, s2N 14557448845, s2N 15939988962,
   s2N 2493756923, s2P 7861084233, s2P 336618558]
private def s2St12VecS1 : List ℤ :=
  [s2N 929641859, s2N 15643171503, s2P 5512176732, s2P 11181529490, s2P 20463654621,
   s2P 12157873269, s2N 2302493113, s2N 549526297, s2N 13251318312, s2N 5960567307,
   s2P 2273207137, s2P 8022413993, s2P 17644358345, s2N 7526171262, s2N 38112739240,
   s2N 23527700223, s2N 32622579090, s2P 3936843536, s2P 6187562888, s2N 8065573530,
   s2N 40662953980, s2N 15569395539, s2N 61596122806, s2N 631990285, s2P 15014477065,
   s2P 71707720425, s2P 17465288957, s2N 4713306717, s2P 2690257088, s2N 36012885437,
   s2N 16678840185, s2P 8628513633, s2P 64932026331, s2P 83330157608, s2P 55663905832,
   s2N 7883120750, s2N 4756519430, s2P 9471317637, s2N 5848652655, s2N 21338688589,
   s2N 39141545610, s2N 16665755290, s2N 11514999091, s2N 8973030502, s2P 60743443135,
   s2P 42406323948, s2P 65728630247, s2P 479835922, s2N 12882727732, s2P 28603646849,
   s2P 19755326543, s2P 34967912537, s2P 3379895110, s2N 43912237125, s2P 23485846311,
   s2P 29579811326, s2P 110047331856, s2P 109523375580, s2P 79303262145, s2N 46839374359,
   s2N 84185443744, s2N 33674836281, s2P 89780035512, s2N 102087246479]
private def s2St12VecS2 : List ℤ :=
  [s2N 25624937484, s2P 18987878899, s2P 24835010262, s2N 33724649654, s2P 33732339997,
   s2P 34106439157, s2N 109094018159, s2N 103536350661, s2N 105940413738, s2N 124154400420,
   s2N 101119293169, s2P 26757465113, s2P 98297888046, s2N 85210346481, s2N 25337703913,
   s2N 138986566223, s2N 105300572963, s2N 159895447361, s2N 71478344163, s2P 75549800344,
   s2P 99729836521, s2P 30612506734, s2N 72588766529, s2N 51256576595, s2N 38588849008,
   s2N 125194069882, s2N 184016889826, s2N 104050338660, s2N 170139074304, s2P 157365370144,
   s2P 246724955418, s2N 30207359380, s2N 107090468626, s2N 225434552853, s2N 34108007593,
   s2N 22373371671, s2P 191107335801, s2P 229789283788, s2P 108401445760, s2N 223158959733,
   s2N 279319629450, s2N 85116452105, s2N 62944461524, s2N 51496609440, s2N 160737212699,
   s2N 457533142343, s2N 471223995731, s2N 279452524024, s2P 64234623363, s2P 152396389225,
   s2P 28276142957, s2P 293365033166, s2P 219857739350, s2P 141206664158, s2P 85980841749,
   s2P 334414215208, s2N 5728044036, s2N 331253063338, s2N 7803738480, s2P 273260972854,
   s2N 295826138438, s2N 470176505934, s2N 854821807920, s2N 863214701258]
private def s2St12VecS3 : List ℤ :=
  [s2N 1449998821284, s2N 614071667869, s2P 126231692460, s2N 151055707655, s2P 566059108454,
   s2P 147214421903, s2N 285325373051, s2P 442751587114, s2P 211447065293, s2P 400528796673,
   s2P 234367357074, s2N 779063899736, s2N 327349992876, s2P 180789049354, s2P 101647718266,
   s2N 881234339815, s2N 289076383870, s2N 211318181086, s2P 825978866666, s2P 1228679938979,
   s2P 1369563502679, s2P 1718501135378, s2P 2291411340046, s2P 2732555012113,
   s2P 1994678423266, s2P 1502709603797, s2P 2429970304814, s2P 4318708751199,
   s2P 4865546009242, s2P 3696418865995, s2P 5105307392135, s2P 2362790069992,
   s2P 1424389206708, s2P 973822173776, s2P 1392117694046, s2P 150323530092, s2P 63062849556,
   s2N 385339188989, s2N 899184877650, s2P 296110188142, s2P 1078322223532, s2P 3421460660188,
   s2P 3137403577662, s2P 1849265074820, s2P 1567202486826, s2N 1905665665408,
   s2P 807788116073, s2N 1079096182302, s2N 744488990616, s2P 1410894026929, s2N 640712647502,
   s2N 913176218908, s2P 1105591277588, s2N 2474930224779, s2P 3859953440029, s2P 258079492061,
   s2P 1075250288596, s2N 995275718695, s2P 189864799594, s2P 2963415824054, s2P 425181324457,
   s2N 887490531069, s2P 542327453198, s2P 2070576626217]
private def s2St12VecS4 : List ℤ :=
  [s2P 2844916534345, s2P 475360963703, s2N 277740707108, s2P 629348965286, s2N 713045276114,
   s2N 1402029757762, s2P 1497995169217, s2P 1816768822941, s2P 3271374242669,
   s2P 5263883413432, s2P 5134300043024, s2P 662981651289, s2N 3855459315816, s2P 7476979804,
   s2P 1191026691280, s2P 525940024436, s2P 1736919171982, s2N 117829937246, s2N 1087288007546,
   s2N 4115457107685, s2N 1864097618371, s2N 5213135201241, s2N 2907114624106,
   s2N 6012918073070, s2N 3053922602905, s2N 183488351318, s2P 901493683273, s2N 4019731691253,
   s2N 2543257631379, s2P 314786250585, s2N 3270487603083, s2N 3836465620596,
   s2N 3731648940551, s2N 3341621729796, s2N 189284411982, s2P 2407657369853,
   s2P 4646521039194, s2N 1563757999635, s2P 985864521328, s2P 1817981475101,
   s2N 2069591597270, s2P 4488256048409, s2N 3235006910958, s2P 4750938389490,
   s2P 4767372145363, s2N 2390145721738, s2P 1178265981647, s2N 3463809262802,
   s2N 7024616241630, s2N 4387331100620, s2P 5647997998476, s2P 2206144862940,
   s2N 3707016814925, s2N 52948197943, s2N 3354416133614, s2N 4694577559782, s2N 174482816874,
   s2N 3239705963334, s2P 4390570321460, s2P 5604758388050, s2P 3918254127647,
   s2P 3206728091318, s2P 1587653756537, s2N 4144783021478]
private def s2St12VecS5 : List ℤ :=
  [s2N 4607799091177, s2N 2670315226317, s2N 5503320488226, s2N 11143398248320,
   s2N 4411670238919, s2N 2778803506322, s2N 6906584918085, s2N 13727182071777,
   s2N 3514976630626, s2N 5262488348154, s2N 3161638804693, s2P 7107925763044,
   s2P 2539231464250, s2P 3626479366953, s2P 11103538196806, s2P 12481044635763,
   s2P 1504407918598, s2P 5592967439142, s2P 7439278994030, s2P 20726905183673,
   s2P 11586238725585, s2P 204401054227, s2P 3423920248743, s2N 7401886974131,
   s2N 10430567815553, s2P 2458082073273, s2N 7673183089268, s2N 939362218163,
   s2N 863105979696, s2P 2864659853634, s2P 3375269736663, s2N 2701403009812,
   s2P 2972070567025, s2N 3923455669266, s2N 6337513949042, s2N 5998180290524,
   s2P 1610723301864, s2P 11503911739352, s2P 10348034298140, s2N 1223622166400,
   s2P 5858671039686, s2P 5361277114757, s2N 7223589895313, s2N 3504571652993,
   s2P 16055399707244, s2P 10718455360967, s2P 16058308493027, s2P 492326631816,
   s2P 2657776489494, s2N 12161636522583, s2P 2076126326971, s2P 9061641062158,
   s2P 4423603788189, s2N 2519802169629, s2N 7664974358741, s2N 4900312930179,
   s2N 6992124060386, s2P 3254374675439, s2N 1774587990012, s2N 216760934100,
   s2N 3715177326125, s2P 8119819303212, s2N 117983614834, s2N 686937564785]
private def s2St12VecS6 : List ℤ :=
  [s2P 4406492139614, s2P 7014319262550, s2N 12424301605067, s2P 6349769506652,
   s2P 5856541608978, s2N 2594243515829, s2N 11880059194570, s2P 7091129007741,
   s2N 15431761972158, s2P 4197572959878, s2N 525128695283, s2N 953202519227,
   s2N 2361530542550, s2P 6393854340873, s2P 11421510258545, s2P 7435076206733,
   s2N 5443193219233, s2P 12905571739347, s2P 2476901902156, s2N 11251417554438,
   s2N 2615132787945, s2N 5308272565652, s2N 10723230410438, s2N 10678894586163,
   s2P 3996756423101, s2N 1655541411169, s2N 8572708015283, s2N 10374907166530,
   s2P 9959369901742, s2P 712122122959, s2N 696959203343, s2P 1723040886494, s2P 4814105878518,
   s2P 1405367483773, s2P 6265325493757, s2N 2330688174383, s2P 8275668829160,
   s2N 4454199921143, s2N 3594852345115, s2P 9346130730665, s2P 14606411820585,
   s2P 2385150542466, s2N 7794986368040, s2N 7361959834354, s2P 16039519089225,
   s2P 7387765483699, s2P 3482223363270, s2P 8060145318278, s2P 10007305402406,
   s2P 2254461478818, s2N 183857996091, s2N 3541939398282, s2P 1369416312401,
   s2N 11621086038008, s2P 9757916942351, s2P 18723880619825, s2P 76171072251058,
   s2P 153320628020617, s2P 234599802788454, s2P 304582380846539, s2P 352704195029200,
   s2P 375050023194816, s2P 372988190166131, s2P 351189738730994]
private def s2St12VecS7 : List ℤ :=
  [s2P 315181509462051, s2P 270660457552356, s2P 222682107480264, s2P 175531022148983,
   s2P 132619887958764, s2P 96060182703321, s2P 66736135361508, s2P 44561969946531,
   s2P 28672819471294, s2P 17801102514493, s2P 10680527172180, s2P 6221697345837,
   s2P 3539103784922, s2P 1967068923567, s2P 1059954458416, s2P 547163540400, s2P 268453092308,
   s2P 125399868402, s2P 56462827907, s2P 24941193609, s2P 11011130530, s2P 4806264036,
   s2N 2132847342, s2P 919075116, s2P 348345179, s2P 113303536, s2P 34561170, s2P 11576325,
   s2P 4497846, s2P 1840943, s2P 722737, s2P 271225, s2N 95420, s2P 29783, s2P 8142, s2P 2095,
   s2P 573, s2P 171, s2P 50, s2P 12, s2P 1, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0]
private def s2St12VecS8 : List ℤ :=
  [s2P 0]
private def s2St12Vec : List ℤ :=
  s2St12VecS0 ++
  (s2St12VecS1 ++
  (s2St12VecS2 ++
  (s2St12VecS3 ++
  (s2St12VecS4 ++
  (s2St12VecS5 ++
  (s2St12VecS6 ++
  (s2St12VecS7 ++
  (s2St12VecS8))))))))
private def s2Chk13 : List Rkm128kSeg := s2Take 3 s2Rem13
private def s2Rem14 : List Rkm128kSeg := s2Drop 3 s2Rem13
private def s2St13VecS0 : List ℤ :=
  [s2N 1851699, s2N 28328414, s2N 60960161, s2P 48745292, s2P 122810612, s2N 54782338,
   s2P 27053041, s2N 132577904, s2N 278013824, s2N 228537632, s2P 192189275, s2P 32311267,
   s2N 3753601, s2P 177453460, s2P 201704089, s2N 74556906, s2N 82666158, s2N 130917588,
   s2P 64626643, s2P 378784167, s2P 1312931501, s2P 1676919110, s2P 2310936421, s2P 2559028900,
   s2P 1128206460, s2N 791246178, s2N 797313512, s2P 1192228556, s2P 3752870027, s2P 787182326,
   s2P 1401115025, s2P 2349424414, s2P 1030519360, s2P 355800858, s2P 1858922417,
   s2P 2925303262, s2N 493651968, s2N 3197367361, s2N 4243381524, s2N 2234909854,
   s2N 942947274, s2N 1195810380, s2P 1075021825, s2N 2101626950, s2N 6936089667,
   s2N 4684700712, s2N 8690970186, s2P 2081626457, s2N 896136846, s2P 3380917062,
   s2N 4589859018, s2P 4176440508, s2P 5473544854, s2P 8951320037, s2P 6137267235,
   s2P 2366657819, s2P 1936729849, s2P 7007063193, s2P 313649398, s2N 10752086071,
   s2N 1528528619, s2N 653288796, s2P 3415021598, s2P 3306588507]
private def s2St13VecS1 : List ℤ :=
  [s2N 2809635521, s2N 2011161200, s2N 9951041860, s2N 26202506369, s2N 15010936201,
   s2N 7637870182, s2N 21668547845, s2N 14014399333, s2N 16353174182, s2P 7394691787,
   s2P 23960063284, s2P 10443812268, s2P 24554067955, s2P 12141798274, s2N 6447185166,
   s2P 61813117, s2P 2797702199, s2P 28715052193, s2P 41130318296, s2P 13426640605,
   s2N 20049317260, s2P 983277595, s2P 10356304157, s2P 7298902226, s2N 17368324712,
   s2N 34389318940, s2P 4498334416, s2P 20479743083, s2P 22733054275, s2N 2182152872,
   s2N 1942655226, s2N 19805746758, s2N 35398675383, s2P 11570045573, s2P 37030849915,
   s2P 101763499834, s2P 32632039718, s2N 9085861301, s2N 86656547213, s2N 49931797757,
   s2P 24099282307, s2P 13588042885, s2N 42756815970, s2N 16510954158, s2N 17941421044,
   s2N 4731555669, s2N 23805299722, s2N 33948645438, s2N 11808280181, s2N 295301979,
   s2P 28808611088, s2N 9218841489, s2N 30175545058, s2N 29137555579, s2N 23087494211,
   s2N 74888013918, s2N 7467263614, s2P 70360042280, s2P 19772127813, s2P 53716521678,
   s2P 16596784400, s2P 54505243183, s2P 2934905602, s2N 72675343054]
private def s2St13VecS2 : List ℤ :=
  [s2N 33406195703, s2N 74751117137, s2P 50131960032, s2P 64490905496, s2P 440379392,
   s2P 1275083062, s2N 55670706453, s2N 4395207921, s2N 86790982455, s2N 148710991770,
   s2N 62902942319, s2N 125150039422, s2P 25018843679, s2P 15073470739, s2N 39564967242,
   s2N 42062302782, s2N 100858080926, s2N 125155561777, s2N 179409153791, s2N 192226318560,
   s2N 106746688826, s2N 12213508695, s2P 41225464410, s2P 83009005793, s2N 71083125063,
   s2N 83619119475, s2N 21092930471, s2N 75218490160, s2N 9776979042, s2N 50221953455,
   s2N 5205808613, s2P 63695124277, s2N 99686518476, s2N 71232229456, s2N 215942247368,
   s2N 212422442700, s2N 156146626706, s2N 9431221413, s2P 14459058727, s2P 226045835394,
   s2N 31576947261, s2N 2650157474, s2P 284017251133, s2P 80447774089, s2N 259906345039,
   s2N 228404854368, s2P 203056751417, s2P 3550095409, s2P 59677385152, s2P 234777414238,
   s2N 37828986364, s2P 350380462852, s2N 98574431229, s2P 67862317170, s2P 466855050084,
   s2P 386387314027, s2P 270080993030, s2N 56858829691, s2N 42388502970, s2P 101404555227,
   s2P 194717859605, s2P 151974000444, s2N 123473778308, s2N 303010618889]
private def s2St13VecS3 : List ℤ :=
  [s2P 369828914805, s2N 246739050625, s2P 50477977648, s2P 489533087896, s2P 527783997735,
   s2P 403181270107, s2N 468193458888, s2P 205389020917, s2P 464882118577, s2N 584551667201,
   s2N 13118876464, s2P 254822507144, s2N 73794546875, s2P 463086760110, s2P 673155926734,
   s2P 165234142861, s2P 180592405989, s2N 1025358857237, s2N 1248026057267, s2N 1390077777436,
   s2P 208366231846, s2P 104633173340, s2N 99252326181, s2N 183952726670, s2P 204018989773,
   s2P 423872539443, s2P 24232078243, s2N 368284855146, s2N 932114313852, s2N 796832838873,
   s2N 895992220037, s2N 1733923806944, s2N 2192668131876, s2N 2521338460198,
   s2N 3237970892553, s2N 3204379138869, s2N 1920326197567, s2N 751041889113,
   s2P 1092235320529, s2P 3529420495941, s2P 2686481121766, s2P 2580379890482,
   s2P 226044566094, s2N 2727391349328, s2N 5777506550977, s2N 5240723148779, s2N 622310270845,
   s2P 2580443955742, s2P 1898663238459, s2N 580134757049, s2N 1626594622654,
   s2P 3259101875623, s2N 921693630777, s2P 185001451590, s2P 1361476063931, s2N 2598912370507,
   s2N 1532794031892, s2P 1418412631702, s2N 2966626004872, s2N 3113400337613,
   s2P 551441968511, s2P 2494733987899, s2N 121126442723, s2N 1075694493232]
private def s2St13VecS4 : List ℤ :=
  [s2P 32068418154, s2P 602020809189, s2N 1632332557773, s2N 941307501724, s2P 4319554532283,
   s2P 1038555820897, s2P 935337256027, s2P 1381273349537, s2N 378681058730, s2P 640934660150,
   s2N 659903530941, s2P 610545102035, s2P 600774465276, s2N 1198143999892, s2N 176618000830,
   s2P 1913501140682, s2P 900431288583, s2P 1516256347132, s2P 1127797691058,
   s2N 3395446255563, s2N 977300224261, s2P 475955709274, s2N 4188003593066, s2N 6877731610978,
   s2N 3267381489094, s2N 3408030505334, s2N 1129426713988, s2P 150766014638,
   s2N 2436861361937, s2N 1206073819925, s2N 2391561399432, s2P 533692279116, s2P 811141531254,
   s2P 744883059207, s2P 1921482313613, s2N 1671195690645, s2N 93882156746, s2N 674277529195,
   s2P 5006780237086, s2N 657403948609, s2P 5550436049217, s2P 5031510432399,
   s2N 5413995100341, s2N 779575790669, s2N 506838266745, s2N 2843870149661, s2N 4987770461042,
   s2N 1769899532713, s2P 7702157607298, s2P 2566509247563, s2P 6359580422244,
   s2N 3289875782157, s2N 5637439416573, s2N 1546997140372, s2N 2003452739455,
   s2N 5392788078160, s2N 6450611388008, s2N 4252275744865, s2N 5592393789603,
   s2N 603633803722, s2N 152390440495, s2N 3875511786297, s2N 1897437825098, s2N 2929192837294]
private def s2St13VecS5 : List ℤ :=
  [s2N 2123560642609, s2P 476596237787, s2N 559975318305, s2N 878086022163, s2N 3413210280160,
   s2N 3532911875019, s2N 6952461320693, s2N 2173440254945, s2P 2969752402519,
   s2P 1308254696392, s2N 686829582323, s2N 8355086988113, s2N 9259379338556,
   s2N 6181725822415, s2N 4271361750711, s2N 5233635292239, s2P 2731734892997,
   s2P 6604480053827, s2N 4157767590177, s2N 14340936856826, s2P 3429399011831,
   s2P 14853778810233, s2N 5072428516759, s2N 6426922320397, s2P 7625169227003,
   s2P 14582625838143, s2N 4777157673080, s2P 5120955480063, s2P 753045726796,
   s2N 4325707378933, s2P 2218158333823, s2P 10143741374052, s2P 332838664993,
   s2P 9947958246014, s2P 11303194573065, s2N 9297231577016, s2N 11598980906972,
   s2N 5348704251995, s2P 316654730066, s2N 115174187219, s2N 10350274794589,
   s2N 3494833805196, s2N 2235827865299, s2N 6669554968587, s2N 9056899360657,
   s2N 143194090698, s2N 3451270476437, s2N 7197132883739, s2N 20838192997728,
   s2N 3594638572374, s2N 1697256496542, s2N 120092107303, s2N 6158156391416,
   s2N 2674048740816, s2P 9059673102151, s2P 10600373567174, s2N 6140469114109,
   s2N 173457473201, s2N 8998287863899, s2P 12773227204698, s2N 6742987981740,
   s2P 18117491897732, s2P 3577235734656, s2P 2875589355912]
private def s2St13VecS6 : List ℤ :=
  [s2N 1445242578983, s2N 5586779003321, s2N 5538109057847, s2N 9642733833023,
   s2P 781617043983, s2P 7730563425549, s2P 2053991562375, s2P 4998095927812,
   s2N 5799901811575, s2N 643924339533, s2N 10882991591408, s2N 5360516792114,
   s2N 6019521374809, s2P 15356947962034, s2P 7929564598578, s2P 3033742637332,
   s2P 3539112006722, s2P 5053840663229, s2N 1748946141346, s2N 6555144430843,
   s2P 4873060715489, s2P 5165916980600, s2P 12904965419261, s2N 11548777510617,
   s2N 6227373249601, s2P 4485526270455, s2P 9194412083860, s2P 9096510602352,
   s2P 9704625786397, s2N 10265571110349, s2N 1631425149242, s2P 2298925413167,
   s2N 14053610367070, s2N 5569988995416, s2N 5142670694461, s2N 1282630741043,
   s2N 5854411806874, s2N 11663300562502, s2N 7472494945345, s2N 700642882930,
   s2P 1379087687433, s2P 7918143642153, s2N 2487472153099, s2N 1830884179889,
   s2P 6735368230711, s2N 7008636017863, s2N 11800434025509, s2P 5653110608335,
   s2P 9465185257244, s2N 11304397389121, s2P 8078812443700, s2N 4539741386596,
   s2P 830442951691, s2P 4957821387053, s2P 5571413909876, s2N 1269388227664,
   s2N 1501486519597, s2N 15367070091419, s2N 10132955923259, s2P 2185287129312,
   s2P 1960191674706, s2P 3095095363982, s2N 13134497071360, s2N 10768785576471]
private def s2St13VecS7 : List ℤ :=
  [s2P 5024410703099, s2N 8487404426144, s2P 20986402616036, s2P 84195258922659,
   s2P 167235362925513, s2P 251586941636458, s2P 321479318876208, s2P 367166574907234,
   s2P 385232927498449, s2P 377318556726742, s2P 348319797072864, s2P 304769253838844,
   s2P 253587519697436, s2P 201103422803627, s2P 152259938009054, s2P 110231133129033,
   s2P 76409301967533, s2P 50796819413612, s2P 32444898420226, s2P 19963993901062,
   s2P 11848506016835, s2P 6808373752631, s2P 3782401404205, s2P 2024158671483,
   s2P 1049175678251, s2P 528726647119, s2P 254978784837, s2P 114335012423, s2P 46865119587,
   s2P 17390581780, s2P 6368656505, s2P 2173573436, s2P 623527106, s2P 169402634, s2P 60831843,
   s2P 29780223, s2P 12892022, s2P 4235153, s2P 1127551, s2P 299368, s2P 84709, s2P 22347,
   s2P 5376, s2N 1381, s2P 426, s2P 141, s2P 40, s2P 8, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2St13VecS8 : List ℤ :=
  [s2P 0]
private def s2St13Vec : List ℤ :=
  s2St13VecS0 ++
  (s2St13VecS1 ++
  (s2St13VecS2 ++
  (s2St13VecS3 ++
  (s2St13VecS4 ++
  (s2St13VecS5 ++
  (s2St13VecS6 ++
  (s2St13VecS7 ++
  (s2St13VecS8))))))))
private def s2Chk14 : List Rkm128kSeg := s2Rem14
private theorem s2Chk0_ok :
    s2RunAt s2Chk0 lm4k512l248krS2LIn lm4k512l248krS2DCurIn
      lm4k512l248krS2PadIn lm4k512l248krS2VecIn
      177 512 2687694192 s2St0Vec = true := by
  decide +kernel
private theorem s2Chk1_ok :
    s2RunAt s2Chk1 177 512
      2687694192 s2St0Vec
      183 512 2704786737 s2St1Vec = true := by
  decide +kernel
private theorem s2Chk2_ok :
    s2RunAt s2Chk2 183 512
      2704786737 s2St1Vec
      185 512 2740629969 s2St2Vec = true := by
  decide +kernel
private theorem s2Chk3_ok :
    s2RunAt s2Chk3 185 512
      2740629969 s2St2Vec
      190 512 2786843677 s2St3Vec = true := by
  decide +kernel
private theorem s2Chk4_ok :
    s2RunAt s2Chk4 190 512
      2786843677 s2St3Vec
      195 512 2808472877 s2St4Vec = true := by
  decide +kernel
private theorem s2Chk5_ok :
    s2RunAt s2Chk5 195 512
      2808472877 s2St4Vec
      199 512 2830112435 s2St5Vec = true := by
  decide +kernel
private theorem s2Chk6_ok :
    s2RunAt s2Chk6 199 512
      2830112435 s2St5Vec
      202 512 2857044629 s2St6Vec = true := by
  decide +kernel
private theorem s2Chk7_ok :
    s2RunAt s2Chk7 202 512
      2857044629 s2St6Vec
      207 512 2877779314 s2St7Vec = true := by
  decide +kernel
private theorem s2Chk8_ok :
    s2RunAt s2Chk8 207 512
      2877779314 s2St7Vec
      209 512 2905556492 s2St8Vec = true := by
  decide +kernel
private theorem s2Chk9_ok :
    s2RunAt s2Chk9 209 512
      2905556492 s2St8Vec
      214 512 2944935542 s2St9Vec = true := by
  decide +kernel
private theorem s2Chk10_ok :
    s2RunAt s2Chk10 214 512
      2944935542 s2St9Vec
      218 512 3043494708 s2St10Vec = true := by
  decide +kernel
private theorem s2Chk11_ok :
    s2RunAt s2Chk11 218 512
      3043494708 s2St10Vec
      220 512 3116255878 s2St11Vec = true := by
  decide +kernel
private theorem s2Chk12_ok :
    s2RunAt s2Chk12 220 512
      3116255878 s2St11Vec
      224 512 3206043719 s2St12Vec = true := by
  decide +kernel
private theorem s2Chk13_ok :
    s2RunAt s2Chk13 224 512
      3206043719 s2St12Vec
      224 512 3345647894 s2St13Vec = true := by
  decide +kernel
private theorem s2Chk14_ok :
    s2RunAt s2Chk14 224 512
      3345647894 s2St13Vec
      lm4k512l248krS2LOut lm4k512l248krS2DCurOut
      lm4k512l248krS2PadOut lm4k512l248krS2Vec = true := by
  decide +kernel
private theorem s2StepProof :
    rkm128kRunSegs 4 248 512 lm4k512l248krS2Segs
      lm4k512l248krS2LIn lm4k512l248krS2DCurIn lm4k512l248krS2PadIn lm4k512l248krS2VecIn =
      (lm4k512l248krS2LOut, lm4k512l248krS2DCurOut, lm4k512l248krS2PadOut, lm4k512l248krS2Vec) :=
  s2RunStepTd s2Chk0_ok (
    s2RunStepTd s2Chk1_ok (
      s2RunStepTd s2Chk2_ok (
        s2RunStepTd s2Chk3_ok (
          s2RunStepTd s2Chk4_ok (
            s2RunStepTd s2Chk5_ok (
              s2RunStepTd s2Chk6_ok (
                s2RunStepTd s2Chk7_ok (
                  s2RunStepTd s2Chk8_ok (
                    s2RunStepTd s2Chk9_ok (
                      s2RunStepTd s2Chk10_ok (
                        s2RunStepTd s2Chk11_ok (
                          s2RunStepTd s2Chk12_ok (
                            s2RunStepTd s2Chk13_ok (
                              s2RunLast s2Chk14_ok))))))))))))))

/-- Segment count of `lm4k512l248krS2Segs` (`21` segments). -/
theorem lm4k512l248krS2_len : rkm128kSegListLen lm4k512l248krS2Segs = 21 := rfl

/-- Exact `rkm128kRunSegs 4 248 512` step across `lm4k512l248krS2Segs` (`segs 75..95`). -/
theorem lm4k512l248krS2_step :
    rkm128kRunSegs 4 248 512 lm4k512l248krS2Segs
      lm4k512l248krS2LIn lm4k512l248krS2DCurIn lm4k512l248krS2PadIn lm4k512l248krS2VecIn =
      (lm4k512l248krS2LOut, lm4k512l248krS2DCurOut, lm4k512l248krS2PadOut, lm4k512l248krS2Vec) :=
  s2StepProof

/-- Suffix chaining lemma advancing `rkm128kRunSegs 4 248 512` past `lm4k512l248krS2Segs`. -/
theorem lm4k512l248krS2_run_after (rest : List Rkm128kSeg) :
    rkm128kRunSegs 4 248 512 (lm4k512l248krS2Segs ++ rest)
      lm4k512l248krS2LIn lm4k512l248krS2DCurIn lm4k512l248krS2PadIn lm4k512l248krS2VecIn =
    rkm128kRunSegs 4 248 512 rest
      lm4k512l248krS2LOut lm4k512l248krS2DCurOut lm4k512l248krS2PadOut lm4k512l248krS2Vec := by
  rw [rkm128kRunSegs_append]; dsimp only; rw [lm4k512l248krS2_step]

/-- Prefix chaining lemma extending any certified state ending at `lm4k512l248krS2*In`. -/
theorem lm4k512l248krS2_after {segsPrev : List Rkm128kSeg} {l0 d0 p0 : ℕ} {v0 : List ℤ}
    (hPrev : rkm128kRunSegs 4 248 512 segsPrev l0 d0 p0 v0 =
      (lm4k512l248krS2LIn, lm4k512l248krS2DCurIn, lm4k512l248krS2PadIn, lm4k512l248krS2VecIn)) :
    rkm128kRunSegs 4 248 512 (segsPrev ++ lm4k512l248krS2Segs) l0 d0 p0 v0 =
      (lm4k512l248krS2LOut, lm4k512l248krS2DCurOut, lm4k512l248krS2PadOut, lm4k512l248krS2Vec) := by
  rw [rkm128kRunSegs_append, hPrev]; dsimp only; exact lm4k512l248krS2_step

end

end QuantumComputation.Specs.GroverFindAll.Rk128kLowM4K512L248KrPt2
