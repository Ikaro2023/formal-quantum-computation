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
# `(32, 512)` `degP <= 64` Krotov `RampKick128k` Part 2 (`Rk128kMidM32K512KrPt2`)

Certifies Slice 2 (`r = 512` segments `80..104`, `25` segments, `438,784` F1272 /
`439,641 <= 450,000` Horner coord-ops, `dk = 13`, `lTableMax = 32`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kMidM32K512KrPt2

@[expose] public section

open QuantumComputation.Specs.DickeSol

/-- Segments `80..104` (`25` segments) of `(32, 512)` `r = 512` at `lTableMax = 32`. -/
def mm32k512krS2Segs : List Rkm128kSeg := [
  ⟨26, 413335, 2, 25,
    rkm128kMask56 513 [55560655663955246, 40081241444281869, 35297078877851723,
      42230831299837342, 189485306314248, 1207300970359360, 66256594010487, 9007199254740992,
      36204998052290824, 384]⟩,
  ⟨26, 410777, 2, 25,
    rkm128kMask56 512 [19644473910895790, 66824897681993325, 1807100063872952,
      27870477628927774, 35457878643980326, 52669103063901158, 8550291901264387, 0,
      679515634270216, 168]⟩,
  ⟨27, 407186, 2, 25,
    rkm128kMask56 509 [47447324817584065, 56591477523579760, 59597600179477189,
      64226997289925796, 58477427480460779, 74792971818733, 36046432708479570, 24,
      3678966443409408, 16]⟩,
  ⟨27, 405763, 2, 25,
    rkm128kMask56 513 [65339491045797077, 18504459574979511, 35263174637757765,
      27118042834205059, 38340564652984608, 60605693157973373, 14073822417721736, 3856,
      36380778178813952, 448]⟩,
  ⟨27, 403977, 2, 25,
    rkm128kMask56 504 [56886033617555921, 56525920141785786, 12979711967543865,
      59880786220810846, 28420457967982392, 2261044815443065, 581697033977875,
      18014398509883476, 36101399146201088]⟩,
  ⟨27, 403904, 2, 25,
    rkm128kMask56 505 [35955843951303376, 43614556012868251, 62110002112159718,
      7931559793054254, 12412962512598268, 56022844603700867, 54006569684190945, 66639955,
      2273790046240768, 1]⟩,
  ⟨27, 273292, 1, 30,
    rkm128kMask56 503 [62438454515463755, 59744542115516372, 68112052753465562,
      19541152641575531, 64612279389396764, 2419221669643008, 37160630758706248, 839914704,
      18613632883490944]⟩,
  ⟨28, 268059, 1, 30,
    rkm128kMask56 503 [21034798374951890, 51728134584909233, 66437142237314514,
      46490481953121610, 45512280159059280, 581805386243693, 56902287750154244, 15637218704,
      18023469614628864]⟩,
  ⟨28, 269400, 1, 30,
    rkm128kMask56 504 [43366838920577080, 44891431434985346, 42906340455010284,
      66630489438980414, 13138823140326414, 88098795510271, 1310901629823500, 490775512066,
      40550555768061952]⟩,
  ⟨28, 268683, 1, 30,
    rkm128kMask56 502 [51814031034777839, 66566665783053157, 56742453790276321,
      36285855852945308, 68276066748808187, 16129686096477971, 45999743917310368,
      6609967137920, 10133103456550912]⟩,
  ⟨28, 269072, 1, 30,
    rkm128kMask56 510 [66327840801635215, 63516214897208826, 12762996032731995,
      57765533861515270, 33205212154028432, 52927964781611966, 54791275937662132,
      123172777639936, 10133374040014848, 32]⟩,
  ⟨28, 269038, 1, 30,
    rkm128kMask56 443 [16233355395328871, 17454783246508919, 34051583498044098,
      5169139038550871, 33858378667557041, 119239375265322, 1832895364753092,
      1838692767457225]⟩,
  ⟨28, 267689, 1, 29,
    rkm128kMask56 511 [35597480215394351, 10994068440823797, 59282414902423199,
      57902812752323505, 48406140336560163, 25405385784404205, 142479636897793,
      27025052529140108, 18579547486158848, 72]⟩,
  ⟨28, 265317, 1, 29,
    rkm128kMask56 511 [30638557651704802, 27037332889624995, 62187368342460729,
      2497595431072834, 19738323425108728, 21730264750195743, 59714991809832863,
      50763363556353373, 40532396646334466, 72]⟩,
  ⟨28, 266328, 1, 29,
    rkm128kMask56 509 [19332245057300129, 71066762500085499, 43516181126609453,
      19591205944874804, 8299556736074793, 27089255948850699, 36101540679123153,
      180391049187336, 4503599627370544, 18]⟩,
  ⟨28, 267153, 1, 29,
    rkm128kMask56 512 [46549178979507471, 13378949233454975, 34383652296495327,
      63261877480435152, 38255193693236047, 19246960145291671, 41503845634922576,
      23683359666471249, 304, 130]⟩,
  ⟨28, 268736, 1, 29,
    rkm128kMask56 512 [37363361491966074, 6810040915711821, 17804526706394024,
      23693733025886081, 31885887751152012, 1240367142903944, 2287543806722978,
      45053867632631971, 9007199254748577, 128]⟩,
  ⟨28, 267106, 1, 29,
    rkm128kMask56 512 [33794945322407088, 12642047178495450, 46838888216075937,
      202373227509887, 54261340389837198, 6884499753609560, 27283967571448517,
      4905393902947121, 137439003008, 132]⟩,
  ⟨28, 267826, 1, 29,
    rkm128kMask56 505 [3670396076873248, 50030168155073840, 46046963437148698,
      6562265028623568, 43963255426898759, 36768138025727762, 27840062750728,
      23362494076584098, 274878305432, 1]⟩,
  ⟨28, 268659, 1, 29,
    rkm128kMask56 512 [61111639966305713, 31996950487466966, 39675313948273507,
      56307971043177213, 10976812885726699, 28400075127717714, 46979403818781524,
      17223059375392963, 141837003317760, 136]⟩,
  ⟨28, 270881, 1, 29,
    rkm128kMask56 506 [29846986036553016, 31062993889563252, 2408344865304335,
      5370358880408288, 11037891639397540, 43445200395111938, 21902547183814020,
      3380182396204642, 16974353, 2]⟩,
  ⟨28, 271569, 1, 29,
    rkm128kMask56 494 [39129929829466866, 58204624103258611, 35018344617637698,
      54833787146037185, 18909432897028116, 45530611842787577, 41235761391978514,
      61628752682096296, 35184617480266]⟩,
  ⟨28, 267151, 1, 29,
    rkm128kMask56 508 [23552036959814703, 69110274601658878, 34686199612431639,
      65095091389821246, 64091579858175417, 19527846295654871, 4811566768391320,
      2279298409967744, 1614807067, 8]⟩,
  ⟨28, 264231, 1, 29,
    rkm128kMask56 508 [55000791680865104, 62565243148090546, 38835804564277342,
      67236807188990227, 59955208254670334, 14078769840896758, 45599126956114064,
      36109476104326344, 6914590219, 8]⟩,
  ⟨28, 267778, 1, 29,
    rkm128kMask56 513 [68325270224106693, 69754084854271488, 48698570995322964,
      26204025046590714, 61632331055368333, 1252920051466970, 54757887958041818,
      580594220344324, 63050433442224048, 479]⟩]

/-- Input multiplexing factor entering `mm32k512krS2Segs` (`26`). -/
def mm32k512krS2LIn : ℕ := 26

/-- Input Hilbert dimension entering `mm32k512krS2Segs` (`512`). -/
def mm32k512krS2DCurIn : ℕ := 512

/-- Input accumulated `10^15`-scale error pad entering `mm32k512krS2Segs`. -/
def mm32k512krS2PadIn : ℕ := 697075942

/-- Slice `0` (`64` entries) of `mm32k512krS2VecIn`. -/
def mm32k512krS2VecIn0 : List ℤ :=
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
/-- Slice `1` (`64` entries) of `mm32k512krS2VecIn`. -/
def mm32k512krS2VecIn1 : List ℤ :=
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
/-- Slice `2` (`64` entries) of `mm32k512krS2VecIn`. -/
def mm32k512krS2VecIn2 : List ℤ :=
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
/-- Slice `3` (`64` entries) of `mm32k512krS2VecIn`. -/
def mm32k512krS2VecIn3 : List ℤ :=
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
/-- Slice `4` (`64` entries) of `mm32k512krS2VecIn`. -/
def mm32k512krS2VecIn4 : List ℤ :=
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
/-- Slice `5` (`64` entries) of `mm32k512krS2VecIn`. -/
def mm32k512krS2VecIn5 : List ℤ :=
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
/-- Slice `6` (`64` entries) of `mm32k512krS2VecIn`. -/
def mm32k512krS2VecIn6 : List ℤ :=
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
/-- Slice `7` (`64` entries) of `mm32k512krS2VecIn`. -/
def mm32k512krS2VecIn7 : List ℤ :=
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
/-- Slice `8` (`1` entries) of `mm32k512krS2VecIn`. -/
def mm32k512krS2VecIn8 : List ℤ :=
  [Int.ofNat 0]
/-- Checkpoint fixed-point vector entering `mm32k512krS2Segs` (`513` entries). -/
def mm32k512krS2VecIn : List ℤ :=
  mm32k512krS2VecIn0 ++ (
    mm32k512krS2VecIn1 ++ (
      mm32k512krS2VecIn2 ++ (
        mm32k512krS2VecIn3 ++ (
          mm32k512krS2VecIn4 ++ (
          mm32k512krS2VecIn5 ++ (
          mm32k512krS2VecIn6 ++ (
          mm32k512krS2VecIn7 ++ (
          mm32k512krS2VecIn8))))))))

/-- Output multiplexing factor exiting `mm32k512krS2Segs` (`28`). -/
def mm32k512krS2LOut : ℕ := 28

/-- Output Hilbert dimension exiting `mm32k512krS2Segs` (`512`). -/
def mm32k512krS2DCurOut : ℕ := 512

/-- Output accumulated `10^15`-scale error pad exiting `mm32k512krS2Segs`. -/
def mm32k512krS2PadOut : ℕ := 944940146

/-- Slice `0` (`64` entries) of `mm32k512krS2Vec`. -/
def mm32k512krS2Vec0 : List ℤ :=
  [Int.negSucc 7054, Int.ofNat 6874, Int.negSucc 732, Int.negSucc 14899, Int.negSucc 26582,
   Int.ofNat 3234, Int.ofNat 14744, Int.ofNat 31465, Int.negSucc 45063, Int.negSucc 109350,
   Int.negSucc 203368, Int.negSucc 148253, Int.negSucc 116480, Int.ofNat 204514,
   Int.negSucc 167590, Int.negSucc 94085, Int.ofNat 7594, Int.negSucc 108603,
   Int.negSucc 544205, Int.ofNat 453495, Int.negSucc 152631, Int.ofNat 428586,
   Int.ofNat 595775, Int.negSucc 681094, Int.negSucc 937608, Int.ofNat 173648,
   Int.ofNat 464569, Int.ofNat 234199, Int.ofNat 802829, Int.ofNat 61494, Int.ofNat 2616606,
   Int.ofNat 354868, Int.ofNat 462887, Int.negSucc 1394104, Int.negSucc 1989790,
   Int.negSucc 767164, Int.negSucc 7125544, Int.negSucc 7464148, Int.negSucc 6510003,
   Int.negSucc 3905263, Int.ofNat 2516628, Int.ofNat 6136856, Int.ofNat 591412,
   Int.negSucc 3566305, Int.ofNat 786424, Int.ofNat 6275395, Int.negSucc 2393940,
   Int.ofNat 10849556, Int.ofNat 8181556, Int.ofNat 524039, Int.negSucc 1945120,
   Int.negSucc 3004051, Int.negSucc 15659961, Int.negSucc 2110657, Int.ofNat 29309552,
   Int.ofNat 4083489, Int.ofNat 17029590, Int.negSucc 14824424, Int.ofNat 33232885,
   Int.ofNat 15808346, Int.ofNat 10654703, Int.ofNat 17008816, Int.ofNat 9161391,
   Int.negSucc 5074562]
/-- Slice `1` (`64` entries) of `mm32k512krS2Vec`. -/
def mm32k512krS2Vec1 : List ℤ :=
  [Int.ofNat 31550900, Int.ofNat 51386397, Int.ofNat 98079434, Int.ofNat 45906276,
   Int.ofNat 3944859, Int.negSucc 39354026, Int.ofNat 52153394, Int.negSucc 15614987,
   Int.negSucc 95711740, Int.negSucc 69104072, Int.negSucc 90796919, Int.negSucc 17236050,
   Int.ofNat 37940046, Int.negSucc 31606197, Int.negSucc 23934328, Int.ofNat 125103689,
   Int.ofNat 51380990, Int.ofNat 77278476, Int.ofNat 25627663, Int.ofNat 45209422,
   Int.negSucc 24027363, Int.negSucc 100572256, Int.ofNat 47364082, Int.negSucc 75529712,
   Int.ofNat 87861134, Int.negSucc 58922032, Int.ofNat 9194520, Int.ofNat 113262867,
   Int.ofNat 144989128, Int.ofNat 30935998, Int.ofNat 69739293, Int.negSucc 28057728,
   Int.ofNat 143042398, Int.ofNat 254224934, Int.ofNat 47604569, Int.ofNat 245934254,
   Int.ofNat 226510611, Int.ofNat 12754487, Int.ofNat 14355886, Int.ofNat 46612101,
   Int.ofNat 177109903, Int.ofNat 75828850, Int.ofNat 200591691, Int.ofNat 469359033,
   Int.ofNat 264520388, Int.ofNat 52201405, Int.ofNat 291986649, Int.negSucc 13828213,
   Int.negSucc 738768076, Int.negSucc 404273246, Int.ofNat 497528849, Int.ofNat 112486587,
   Int.negSucc 7853122, Int.negSucc 93699170, Int.ofNat 53162855, Int.ofNat 1257262404,
   Int.ofNat 27471431, Int.ofNat 242626101, Int.negSucc 555469040, Int.negSucc 162426324,
   Int.negSucc 1154172075, Int.negSucc 1302254632, Int.negSucc 920191980, Int.negSucc 982319568]
/-- Slice `2` (`64` entries) of `mm32k512krS2Vec`. -/
def mm32k512krS2Vec2 : List ℤ :=
  [Int.negSucc 345700941, Int.negSucc 533515109, Int.negSucc 596427436, Int.negSucc 146563294,
   Int.negSucc 1186075275, Int.negSucc 349694971, Int.negSucc 734200570, Int.ofNat 1290205279,
   Int.ofNat 1599808317, Int.ofNat 749980792, Int.ofNat 1673776267, Int.ofNat 958598535,
   Int.ofNat 62773599, Int.ofNat 2540774362, Int.ofNat 2039642492, Int.ofNat 2518754197,
   Int.ofNat 4773758496, Int.ofNat 607280575, Int.negSucc 541737569, Int.negSucc 1704318755,
   Int.ofNat 1659823448, Int.ofNat 1593831761, Int.ofNat 1058452117, Int.ofNat 680308188,
   Int.negSucc 4674840235, Int.negSucc 2583767469, Int.ofNat 5327398179, Int.ofNat 6192105240,
   Int.negSucc 1467175003, Int.negSucc 2342375624, Int.negSucc 4331374306,
   Int.ofNat 2185544253, Int.negSucc 585908519, Int.negSucc 2354621819, Int.negSucc 985504051,
   Int.negSucc 1401754759, Int.ofNat 7276623380, Int.ofNat 608130296, Int.ofNat 2853280404,
   Int.negSucc 2430819325, Int.ofNat 6741322261, Int.ofNat 1744789001, Int.ofNat 1846182471,
   Int.ofNat 3607239530, Int.ofNat 2820178455, Int.negSucc 59098280, Int.ofNat 865324518,
   Int.negSucc 5976829735, Int.ofNat 4277496856, Int.negSucc 4260242907,
   Int.negSucc 4628382786, Int.ofNat 273242852, Int.negSucc 5439420370, Int.negSucc 925711729,
   Int.ofNat 7608303050, Int.ofNat 16747554317, Int.ofNat 11623788015, Int.ofNat 4817398208,
   Int.ofNat 5341612306, Int.ofNat 8763738738, Int.negSucc 289873821, Int.negSucc 3399961677,
   Int.negSucc 1717702512, Int.ofNat 7610176291]
/-- Slice `3` (`64` entries) of `mm32k512krS2Vec`. -/
def mm32k512krS2Vec3 : List ℤ :=
  [Int.ofNat 6498812701, Int.ofNat 6190894859, Int.negSucc 1949445131, Int.ofNat 3717894409,
   Int.ofNat 4283010949, Int.negSucc 19028521282, Int.negSucc 13420495652,
   Int.negSucc 7664496846, Int.negSucc 3683618774, Int.negSucc 9818464303,
   Int.ofNat 4179221115, Int.ofNat 8564763570, Int.negSucc 5999490757, Int.negSucc 27613441528,
   Int.negSucc 12021491278, Int.negSucc 19054097375, Int.negSucc 3507024906,
   Int.ofNat 27626809663, Int.ofNat 32077056093, Int.ofNat 31120256767, Int.ofNat 109845612,
   Int.ofNat 25683437651, Int.ofNat 34874486719, Int.ofNat 69307235692, Int.ofNat 6165628364,
   Int.negSucc 2909338, Int.negSucc 15222953726, Int.negSucc 3389692619, Int.ofNat 40594532285,
   Int.ofNat 46469317510, Int.negSucc 9806872821, Int.negSucc 30863622082,
   Int.negSucc 63341094474, Int.negSucc 18801835671, Int.negSucc 39439194774,
   Int.negSucc 2418739589, Int.ofNat 16259937867, Int.negSucc 1013458232,
   Int.negSucc 1340939624, Int.ofNat 39151954497, Int.negSucc 16964112778,
   Int.negSucc 39304759285, Int.ofNat 1577560156, Int.ofNat 5294068434,
   Int.negSucc 114303380175, Int.negSucc 96866665993, Int.negSucc 71380070502,
   Int.negSucc 114122152125, Int.ofNat 128066076157, Int.ofNat 116725259308,
   Int.negSucc 24346320115, Int.negSucc 83687695493, Int.ofNat 91960565836,
   Int.ofNat 27409371502, Int.negSucc 11792381297, Int.negSucc 7042659334,
   Int.negSucc 98375994414, Int.negSucc 132730204645, Int.negSucc 109545963314,
   Int.ofNat 2081607431, Int.negSucc 48950132529, Int.negSucc 146698194789,
   Int.negSucc 68068814485, Int.negSucc 104022089762]
/-- Slice `4` (`64` entries) of `mm32k512krS2Vec`. -/
def mm32k512krS2Vec4 : List ℤ :=
  [Int.negSucc 122238053614, Int.negSucc 2599665190, Int.negSucc 204946929171,
   Int.negSucc 42313383536, Int.negSucc 45186846054, Int.ofNat 111655999054,
   Int.ofNat 155991993762, Int.negSucc 74791584570, Int.negSucc 77284141839,
   Int.negSucc 208818192759, Int.negSucc 174991076152, Int.negSucc 201327238298,
   Int.negSucc 213732993811, Int.negSucc 290771573656, Int.negSucc 101351784816,
   Int.negSucc 167019105220, Int.negSucc 342584388964, Int.negSucc 69239937158,
   Int.ofNat 24322388599, Int.negSucc 25050780295, Int.ofNat 3884263788,
   Int.negSucc 158409866330, Int.negSucc 36900265086, Int.negSucc 175967410572,
   Int.ofNat 36984883818, Int.ofNat 292027289757, Int.ofNat 108362684262,
   Int.ofNat 444235647952, Int.ofNat 284477206995, Int.ofNat 36699237194, Int.ofNat 2329492390,
   Int.negSucc 103513707594, Int.ofNat 323270704010, Int.negSucc 169822561357,
   Int.negSucc 692810284821, Int.negSucc 369786625795, Int.ofNat 9785846810,
   Int.ofNat 7848061120, Int.negSucc 335224063808, Int.negSucc 439812561061,
   Int.negSucc 232538305933, Int.negSucc 193339867450, Int.negSucc 528282099956,
   Int.negSucc 308222376968, Int.negSucc 180677237933, Int.negSucc 176134448361,
   Int.negSucc 185647368857, Int.negSucc 303328871303, Int.negSucc 179393302604,
   Int.ofNat 259637577709, Int.ofNat 166925136734, Int.negSucc 189677928759,
   Int.negSucc 404517138101, Int.ofNat 103280727441, Int.negSucc 339673220726,
   Int.ofNat 193084606979, Int.ofNat 312171607293, Int.ofNat 512536657003,
   Int.ofNat 634847551661, Int.negSucc 614539945274, Int.negSucc 51101789500,
   Int.ofNat 264495421415, Int.ofNat 238897137080, Int.ofNat 22287174186]
/-- Slice `5` (`64` entries) of `mm32k512krS2Vec`. -/
def mm32k512krS2Vec5 : List ℤ :=
  [Int.ofNat 227295571929, Int.ofNat 250265000057, Int.negSucc 750914889593,
   Int.ofNat 72215649970, Int.ofNat 376711979895, Int.ofNat 519382957814,
   Int.ofNat 559363808020, Int.ofNat 650999418832, Int.negSucc 777578743559,
   Int.negSucc 70017257077, Int.negSucc 131769605696, Int.ofNat 540637271689,
   Int.ofNat 559700889279, Int.ofNat 2943889366480, Int.ofNat 4228714384007,
   Int.ofNat 4866204589841, Int.ofNat 3547809970285, Int.ofNat 340434475413,
   Int.negSucc 901506631688, Int.ofNat 263260435888, Int.ofNat 732069502878,
   Int.negSucc 179127922138, Int.negSucc 1119828537671, Int.negSucc 3504357203224,
   Int.negSucc 2653736506012, Int.negSucc 907407679153, Int.ofNat 1330502481873,
   Int.negSucc 3919437225511, Int.negSucc 10528967801182, Int.negSucc 7724586888461,
   Int.negSucc 1008377611839, Int.negSucc 343560107571, Int.ofNat 1658555478538,
   Int.negSucc 415895264225, Int.negSucc 4286889555618, Int.negSucc 8298824973086,
   Int.negSucc 4649617227741, Int.negSucc 2399848347301, Int.negSucc 50568734691,
   Int.negSucc 2942685091732, Int.ofNat 9436171016514, Int.ofNat 3557147145227,
   Int.negSucc 984957178046, Int.negSucc 1161653035742, Int.ofNat 3096325894988,
   Int.negSucc 28742536221, Int.ofNat 647942433664, Int.negSucc 4114833943674,
   Int.negSucc 2323040995837, Int.ofNat 2733147313181, Int.ofNat 5736697547441,
   Int.ofNat 5244846129814, Int.ofNat 3203154720397, Int.negSucc 109791281136,
   Int.ofNat 4291491267483, Int.ofNat 1775143659417, Int.ofNat 2544244976839,
   Int.negSucc 525454947584, Int.negSucc 1041867060941, Int.negSucc 4003886775853,
   Int.ofNat 448391490114, Int.ofNat 1509411823842, Int.ofNat 3660659289828,
   Int.negSucc 329820800996]
/-- Slice `6` (`64` entries) of `mm32k512krS2Vec`. -/
def mm32k512krS2Vec6 : List ℤ :=
  [Int.ofNat 1649385927477, Int.ofNat 3796768222937, Int.ofNat 4575275753788,
   Int.ofNat 10953905919325, Int.ofNat 11499120704263, Int.ofNat 5762832046873,
   Int.ofNat 719409212050, Int.negSucc 1034099670945, Int.negSucc 7150924802171,
   Int.negSucc 4610211562643, Int.ofNat 2041647482623, Int.ofNat 1138116490920,
   Int.ofNat 1298727695106, Int.ofNat 2302909707616, Int.ofNat 2489122306015,
   Int.negSucc 2548155289181, Int.ofNat 3577591994785, Int.ofNat 2298485548205,
   Int.ofNat 194712889967, Int.negSucc 4532734269477, Int.negSucc 6940910190131,
   Int.negSucc 1016981514352, Int.negSucc 5383995747848, Int.negSucc 247089486878,
   Int.ofNat 4842605604218, Int.ofNat 1017049393409, Int.negSucc 14515056419646,
   Int.ofNat 12060398445924, Int.negSucc 5557520929232, Int.negSucc 6052690121879,
   Int.ofNat 6820164902975, Int.ofNat 5175256533823, Int.negSucc 2000061295308,
   Int.ofNat 2312071910144, Int.ofNat 6339731580548, Int.ofNat 6317591138566,
   Int.negSucc 3622495051147, Int.negSucc 1363860679674, Int.negSucc 6617263236430,
   Int.negSucc 9242073637293, Int.negSucc 7057482160422, Int.negSucc 1883039612279,
   Int.negSucc 4576566641374, Int.ofNat 2549200753989, Int.negSucc 3703266297905,
   Int.negSucc 15569222889449, Int.negSucc 7653170071459, Int.negSucc 3646305801802,
   Int.negSucc 9008595019301, Int.ofNat 5409595277176, Int.ofNat 10666571025028,
   Int.negSucc 4487531249250, Int.ofNat 14170225036537, Int.negSucc 15720324039919,
   Int.negSucc 16107916857452, Int.ofNat 9679837263355, Int.ofNat 8407334583116,
   Int.negSucc 1260994154359, Int.ofNat 5742166374683, Int.ofNat 5459691276749,
   Int.ofNat 10179382564405, Int.ofNat 3785946866626, Int.ofNat 8159760752169,
   Int.negSucc 1304315767998]
/-- Slice `7` (`64` entries) of `mm32k512krS2Vec`. -/
def mm32k512krS2Vec7 : List ℤ :=
  [Int.negSucc 1537688710274, Int.negSucc 1396012460129, Int.ofNat 5509754369523,
   Int.negSucc 4814710275544, Int.ofNat 6332086700614, Int.ofNat 163634028181,
   Int.negSucc 9931482742334, Int.ofNat 1673166686767, Int.negSucc 146189315165,
   Int.negSucc 469656614221, Int.ofNat 4271696077548, Int.negSucc 12616461546363,
   Int.negSucc 591378174749, Int.negSucc 341995115279, Int.ofNat 1665127976162,
   Int.ofNat 15175128938338, Int.ofNat 4551968702863, Int.ofNat 9512604128488,
   Int.negSucc 9930855960976, Int.negSucc 7397488233024, Int.negSucc 10881587036298,
   Int.negSucc 2255630793484, Int.ofNat 12389812851312, Int.ofNat 1565312889104,
   Int.ofNat 1148465002253, Int.negSucc 19075367665483, Int.negSucc 10898461703118,
   Int.negSucc 11558210525028, Int.negSucc 4767271713334, Int.negSucc 12988880942666,
   Int.ofNat 4189034910263, Int.negSucc 3856502438350, Int.negSucc 12571229052697,
   Int.ofNat 11240618220657, Int.negSucc 8532753722940, Int.ofNat 5408590059554,
   Int.ofNat 57264237723125, Int.ofNat 168048602706576, Int.ofNat 287149482585360,
   Int.ofNat 377741595237539, Int.ofNat 432629973761292, Int.ofNat 431878136398699,
   Int.ofNat 388248231668541, Int.ofNat 319562750640445, Int.ofNat 242962833598356,
   Int.ofNat 174512819219227, Int.ofNat 118223009756982, Int.ofNat 72678776150301,
   Int.ofNat 39010885610353, Int.ofNat 18062296366834, Int.ofNat 7349307925032,
   Int.ofNat 2758057473369, Int.ofNat 1019985484263, Int.negSucc 388556695818,
   Int.negSucc 150600384827, Int.negSucc 56729582612, Int.negSucc 20031060382,
   Int.negSucc 6495938681, Int.negSucc 2017278623, Int.negSucc 450880694, Int.negSucc 70300358,
   Int.ofNat 9845247, Int.negSucc 1645675, Int.negSucc 277693]
/-- Slice `8` (`1` entries) of `mm32k512krS2Vec`. -/
def mm32k512krS2Vec8 : List ℤ :=
  [Int.negSucc 33175]
/-- Checkpoint fixed-point vector exiting `mm32k512krS2Segs` (`513` entries). -/
def mm32k512krS2Vec : List ℤ :=
  mm32k512krS2Vec0 ++ (
    mm32k512krS2Vec1 ++ (
      mm32k512krS2Vec2 ++ (
        mm32k512krS2Vec3 ++ (
          mm32k512krS2Vec4 ++ (
          mm32k512krS2Vec5 ++ (
          mm32k512krS2Vec6 ++ (
          mm32k512krS2Vec7 ++ (
          mm32k512krS2Vec8))))))))

end

public section

open QuantumComputation.Specs.DickeSol

private abbrev s2P : ℕ → ℤ := Int.ofNat
private abbrev s2N : ℕ → ℤ := Int.negSucc
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
  | ofNat x =>
    cases b with
    | ofNat y => exact congrArg Int.ofNat (s2NatEq_eq h)
    | _ => cases h
  | negSucc x =>
    cases b with
    | ofNat _ => cases h
    | negSucc y => exact congrArg Int.negSucc (s2NatEq_eq h)
private def s2IntListEq (xs ys : List ℤ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (s2IntEq x y) (s2IntListEq xr yr) false
  | _, _ => false
private theorem s2IntListEq_eq {xs ys : List ℤ}
    (h : s2IntListEq xs ys = true) : xs = ys := by
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
private def s2SegStateAt (st : ℕ × ℕ × ℕ × List ℤ) (l d p : ℕ) (v : List ℤ) : Bool :=
  match st with
  | (ls, ds, ps, vs) =>
    Bool.and (s2NatEq ls l)
      (Bool.and (s2NatEq ds d) (Bool.and (s2NatEq ps p) (s2IntListEq vs v)))
private theorem s2SegStateAt_eq {st : ℕ × ℕ × ℕ × List ℤ} {l d p : ℕ} {v : List ℤ}
    (h : s2SegStateAt st l d p v = true) : st = (l, d, p, v) := by
  rcases st with ⟨ls, ds, ps, vs⟩; unfold s2SegStateAt at h; dsimp only at h
  simp only [Bool.and_eq_true] at h; rcases h with ⟨hl, ⟨hd, ⟨hp, hv⟩⟩⟩
  rw [s2NatEq_eq hl, s2NatEq_eq hd, s2NatEq_eq hp, s2IntListEq_eq hv]
private theorem s2Step {b rest : List Rkm128kSeg}
    {l0 p0 l1 p1 l2 p2 : ℕ} {v0 v1 v2 : List ℤ}
    (h1 : s2SegStateAt (rkm128kRunSegs 32 32 512 b l0 512 p0 v0) l1 512 p1 v1 = true)
    (h2 : rkm128kRunSegs 32 32 512 rest l1 512 p1 v1 = (l2, 512, p2, v2)) :
    rkm128kRunSegs 32 32 512 (b ++ rest) l0 512 p0 v0 = (l2, 512, p2, v2) := by
  rw [rkm128kRunSegs_append, s2SegStateAt_eq h1]; exact h2
private def s2B0 : List Rkm128kSeg := mm32k512krS2Segs.take 1
private def s2B1 : List Rkm128kSeg := (mm32k512krS2Segs.drop 1).take 1
private def s2B2 : List Rkm128kSeg := (mm32k512krS2Segs.drop 2).take 1
private def s2B3 : List Rkm128kSeg := (mm32k512krS2Segs.drop 3).take 1
private def s2B4 : List Rkm128kSeg := (mm32k512krS2Segs.drop 4).take 1
private def s2B5 : List Rkm128kSeg := (mm32k512krS2Segs.drop 5).take 2
private def s2B6 : List Rkm128kSeg := (mm32k512krS2Segs.drop 7).take 2
private def s2B7 : List Rkm128kSeg := (mm32k512krS2Segs.drop 9).take 2
private def s2B8 : List Rkm128kSeg := (mm32k512krS2Segs.drop 11).take 2
private def s2B9 : List Rkm128kSeg := (mm32k512krS2Segs.drop 13).take 3
private def s2B10 : List Rkm128kSeg := (mm32k512krS2Segs.drop 16).take 3
private def s2B11 : List Rkm128kSeg := (mm32k512krS2Segs.drop 19).take 3
private def s2B12 : List Rkm128kSeg := mm32k512krS2Segs.drop 22
private def s2V0S0 : List ℤ :=
  [s2P 5679, s2P 12104, s2N 25146, s2N 10870, s2P 3716, s2N 43633, s2P 90529, s2N 223880,
   s2N 88270, s2N 5421, s2N 188519, s2N 104790, s2N 407044, s2N 279537, s2P 74273, s2P 421914,
   s2P 97101, s2N 111710, s2P 578514, s2P 146555, s2P 644867, s2P 1385182, s2P 1291299,
   s2P 1910266, s2P 875230, s2P 392118, s2P 1529526, s2P 2139578, s2N 1418843, s2P 2026928,
   s2N 1516941, s2P 1460255, s2P 1768407, s2P 1937146, s2N 1689869, s2P 3675478, s2N 5241068,
   s2N 50540, s2N 1126312, s2N 9554754, s2P 3616704, s2P 2139297, s2P 7614965, s2P 4269478,
   s2N 11874881, s2N 5969540, s2N 8715050, s2P 1570329, s2N 15708056, s2N 10962259,
   s2N 19408121, s2N 10482742, s2P 42510112, s2N 32644508, s2P 7763347, s2N 47365109,
   s2P 146140491, s2P 108531815, s2P 78747991, s2N 17798997, s2N 75267611, s2N 92280931,
   s2P 109715997, s2P 93200959]
private def s2V0S1 : List ℤ :=
  [s2P 55852642, s2P 18496615, s2P 135687316, s2P 42675373, s2P 224678606, s2P 209703857,
   s2P 22009080, s2N 186395541, s2N 309882009, s2N 227223770, s2N 34285482, s2P 37323187,
   s2P 399669843, s2P 2031747, s2P 524912804, s2P 326088388, s2P 201952196, s2N 439227407,
   s2N 493027422, s2P 222730686, s2P 312387992, s2N 281285064, s2N 63825023, s2P 680404094,
   s2P 60634158, s2P 84895110, s2P 160036225, s2N 317595510, s2P 125020265, s2N 756250587,
   s2P 543226567, s2P 1481295, s2N 947742839, s2N 117521630, s2N 821438549, s2N 710633329,
   s2N 512833107, s2N 1575537496, s2N 858658443, s2N 800566320, s2P 202498738, s2N 685807311,
   s2P 1365962558, s2P 1385257244, s2P 2052293784, s2P 354729966, s2N 1572274480,
   s2N 318407143, s2N 670948149, s2N 642246082, s2N 744409989, s2P 71780780, s2P 5032217382,
   s2P 4342986665, s2P 6100271154, s2P 1517708566, s2N 1365535526, s2N 1023788827,
   s2N 2493380773, s2P 3096431801, s2P 2736969062, s2P 1955326662, s2P 1105284995,
   s2N 1022095760]
private def s2V0S2 : List ℤ :=
  [s2P 1329413927, s2P 1547871589, s2P 2355211326, s2N 5508336678, s2P 1742886907,
   s2N 486645622, s2N 2146882904, s2N 17783796230, s2N 361087972, s2N 15197160054,
   s2N 7615272811, s2N 9794436825, s2N 11703992219, s2N 2410659992, s2N 907483058,
   s2P 12114480293, s2N 7759757530, s2N 5375961588, s2N 754305701, s2N 1052883803,
   s2P 7330409188, s2P 12081506244, s2P 12806911538, s2P 7721906559, s2P 16496925576,
   s2P 40622305636, s2P 11528637116, s2P 4695297979, s2P 4430996850, s2N 13827464133,
   s2N 11373049408, s2P 16100638297, s2P 1844468508, s2P 16886170384, s2P 48627565686,
   s2P 12550053569, s2P 15733238564, s2P 8984655738, s2P 32355952394, s2N 6743244477,
   s2N 81861661252, s2N 7552352732, s2P 10182146498, s2N 26310503450, s2P 5631613799,
   s2N 43674986532, s2N 81513903717, s2N 51150587758, s2P 6660495933, s2P 82447258715,
   s2N 40259819003, s2N 23573050153, s2P 17109624482, s2P 55618753754, s2P 51072355481,
   s2P 42498298324, s2P 5147590590, s2N 9029754267, s2N 7360081475, s2P 18868869084,
   s2N 10980687732, s2N 11541748715, s2N 102069003531, s2N 71895425410]
private def s2V0S3 : List ℤ :=
  [s2P 16108803287, s2P 22306548183, s2N 5324002952, s2N 44397462332, s2N 22329170478,
   s2N 39661597864, s2N 79850174118, s2N 57115907827, s2P 11086776457, s2P 10501376863,
   s2N 92918770738, s2N 55640423581, s2P 33610830112, s2P 42691922008, s2P 71377558238,
   s2N 2756486800, s2P 89279572395, s2P 158436462857, s2P 269623419557, s2P 190514193196,
   s2P 101874434280, s2P 35410953148, s2N 15632961838, s2N 115624320651, s2P 8038521905,
   s2N 8665931103, s2N 93319783621, s2N 71673083344, s2P 65810890727, s2P 188931655123,
   s2P 76987640011, s2P 293550514370, s2P 347844859734, s2P 410118052182, s2P 471277194195,
   s2P 357959413143, s2N 87139314154, s2N 145229364028, s2N 54877197915, s2P 87234432071,
   s2N 95552259930, s2N 419150213063, s2P 293084829854, s2N 357525670563, s2N 172088530192,
   s2N 285062388983, s2N 302758575684, s2N 285889113867, s2N 122438821702, s2P 261855204228,
   s2P 113657530405, s2N 83075273565, s2N 280343367778, s2P 116605575609, s2P 303130968277,
   s2P 1927521571362, s2P 1306326111549, s2P 1181315348581, s2P 1455805522290,
   s2P 170976832814, s2N 667217694860, s2N 1412785649372, s2P 321884674850, s2P 373368361461]
private def s2V0S4 : List ℤ :=
  [s2P 88142964531, s2P 480948900224, s2P 1018514178035, s2P 1511254799716, s2P 51467147397,
   s2P 157533068179, s2P 527329522533, s2N 1483442865091, s2N 1102536964563, s2N 590453279802,
   s2P 1643939170909, s2P 974078284296, s2P 320835466071, s2P 1277083343287, s2P 682185710587,
   s2N 501880542120, s2N 1348153949193, s2N 1474142450597, s2N 685302960710, s2P 1222837501261,
   s2P 1977191371815, s2P 2372610854537, s2P 3167181839697, s2P 5725157007307,
   s2P 6784471539467, s2P 5208460970851, s2P 2704434102435, s2P 2786761333013,
   s2P 1151424804489, s2N 2484888523546, s2N 5228923718793, s2N 9430391581655,
   s2N 2537973688328, s2P 805124692907, s2P 4726085730513, s2N 452570328540, s2N 6479822050886,
   s2N 105949239076, s2P 1099121847663, s2P 2359093273740, s2N 2728669939360,
   s2N 3808160123814, s2N 4415834552797, s2N 315141947977, s2P 2730942443397,
   s2P 1100718742079, s2N 301710302260, s2N 638141877404, s2P 3565049557186, s2N 3263116988628,
   s2P 854000337821, s2P 1624527302355, s2P 2909651651031, s2P 7514063427336,
   s2N 2100474384712, s2N 1980219394361, s2N 2292876464706, s2N 4343449843235,
   s2N 4693776055599, s2N 1375791710447, s2N 9014152083785, s2N 2859455618343,
   s2P 114711158297, s2P 2259258137781]
private def s2V0S5 : List ℤ :=
  [s2N 2605508932911, s2N 1274729894081, s2N 844455522958, s2P 3125691343288, s2N 180439519077,
   s2P 7391244896195, s2N 416981007900, s2N 3443631439935, s2N 7443234776561, s2N 251846205051,
   s2N 4403628997096, s2N 2110635877177, s2N 4638237295952, s2N 2710639935064,
   s2N 5861031633213, s2N 669857633141, s2N 443147950673, s2N 8298123446465, s2N 2872387494319,
   s2P 248706946023, s2P 5216821088802, s2P 311350030031, s2P 5929400729879, s2P 679235131855,
   s2P 1520665493145, s2N 4719668393244, s2N 5742452872977, s2N 5967829655726,
   s2N 9602806045392, s2N 1815961502485, s2N 729543716151, s2P 1309001306999,
   s2P 6748596198374, s2P 2034387618046, s2P 1177665622709, s2P 1624864360343,
   s2P 3024827842053, s2P 3587210577065, s2P 1810818720780, s2P 5574612976636,
   s2P 10037434078067, s2P 10898910506821, s2N 3887603085513, s2N 7553754911404,
   s2N 5262463503719, s2N 147561962145, s2P 843815475204, s2N 3269856316016, s2N 3512231841934,
   s2N 4177493895679, s2P 4959902938149, s2N 3065983636507, s2N 148020037778,
   s2P 5370572642319, s2N 1824002703466, s2N 1948968092027, s2P 2356129066617,
   s2P 8341523022184, s2N 6624401189166, s2P 2497153610690, s2P 9827065840543,
   s2P 5148749839711, s2P 16971951019813, s2P 56144172861939]
private def s2V0S6 : List ℤ :=
  [s2P 107934105042628, s2P 165972015466159, s2P 223372269508500, s2P 273726810000073,
   s2P 312033552980129, s2P 335403189674063, s2P 343203651990946, s2P 336631864453464,
   s2P 318049976846217, s2P 290415708812573, s2P 256893378828264, s2P 220560849034305,
   s2P 184140461975000, s2P 149773130023854, s2P 118898338407295, s2P 92268596283246,
   s2P 70071876122957, s2P 52101875973194, s2P 37923384275501, s2P 27000475928671,
   s2P 18780898222737, s2P 12743961058954, s2P 8423290290494, s2P 5415803346289,
   s2P 3383830649115, s2P 2053412688690, s2P 1210165044070, s2P 693025034336, s2P 386112277501,
   s2P 209663830370, s2P 111211973559, s2P 57779491842, s2P 29506388198, s2P 14876009569,
   s2P 7435520222, s2P 3691297487, s2P 1815771613, s2P 879653337, s2P 416754637, s2P 192227054,
   s2P 86360527, s2P 38022118, s2P 16576644, s2P 7237495, s2P 3188761, s2P 1419108, s2P 634663,
   s2P 283024, s2P 124981, s2P 54414, s2P 23313, s2P 9820, s2P 4060, s2P 1643, s2P 643,
   s2P 239, s2P 80, s2P 23, s2P 4, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V0 : List ℤ :=
  s2V0S0 ++
    (s2V0S1 ++
    (s2V0S2 ++
    (s2V0S3 ++
    (s2V0S4 ++
    (s2V0S5 ++
    (s2V0S6 ++
    (mm32k512krS2VecIn7 ++
    mm32k512krS2VecIn8)))))))
private def s2V1S0 : List ℤ :=
  [s2N 4236, s2N 18457, s2N 18928, s2P 64328, s2P 92522, s2P 120786, s2N 11724, s2N 161331,
   s2N 126865, s2N 16327, s2P 114620, s2N 89186, s2N 33774, s2P 31417, s2P 19582, s2N 744978,
   s2N 247003, s2N 295607, s2N 285552, s2P 355058, s2P 36226, s2P 176033, s2P 234286,
   s2P 1318380, s2P 1961429, s2P 3227997, s2P 598772, s2P 1454384, s2P 87158, s2P 3152873,
   s2N 2118379, s2N 4672609, s2N 752222, s2P 3312853, s2P 5576878, s2P 4469181, s2P 1424427,
   s2P 5089065, s2N 3733582, s2N 5524552, s2N 4327194, s2N 5520039, s2N 2611965, s2P 2395368,
   s2N 2917884, s2N 21929780, s2N 35518012, s2P 35184668, s2N 51771181, s2N 43942648,
   s2N 26333319, s2N 30419177, s2P 11891775, s2P 10782607, s2P 9835336, s2N 83581412,
   s2N 46167125, s2P 4520831, s2N 21514877, s2P 55300668, s2N 6338666, s2P 97622860,
   s2N 91577917, s2P 195072181]
private def s2V1S1 : List ℤ :=
  [s2P 67383327, s2P 11058300, s2N 7737561, s2P 120795765, s2P 112183629, s2P 124490702,
   s2P 301750190, s2P 157161308, s2P 53995406, s2P 48392378, s2N 100508380, s2N 294802497,
   s2N 235423837, s2N 130413581, s2P 182440539, s2N 299897599, s2N 229828187, s2P 206720078,
   s2N 266276311, s2N 604370530, s2N 993924001, s2N 307925830, s2N 443534537, s2P 112647243,
   s2P 220339878, s2N 525949168, s2N 607958328, s2N 177380999, s2P 544880130, s2P 652401085,
   s2N 476723291, s2N 54524014, s2P 740144350, s2N 344126181, s2P 401117445, s2P 631258037,
   s2P 43586407, s2N 578498481, s2P 552913035, s2P 33244646, s2P 486085984, s2N 250224193,
   s2N 458990300, s2P 2053020722, s2P 103617848, s2P 1553986177, s2P 24341303, s2P 1438782204,
   s2N 2734410186, s2P 1424545309, s2P 87258890, s2N 2359337508, s2N 795472530, s2P 576605305,
   s2P 2063584778, s2P 667438499, s2N 415921533, s2P 3666782585, s2P 48057896, s2N 4187920500,
   s2N 6518728548, s2N 1198322393, s2N 10135717364, s2N 2143981673]
private def s2V1S2 : List ℤ :=
  [s2N 7055626543, s2N 7389124965, s2N 882387423, s2P 9024840184, s2N 4978106277,
   s2N 2975365586, s2P 1446276114, s2P 7123624614, s2P 1871698731, s2N 1211550238,
   s2N 3593293715, s2N 2872445523, s2P 4066090879, s2P 4394690046, s2P 7593808922,
   s2N 3918834132, s2N 6941745612, s2P 2163407072, s2P 17041334329, s2P 15600623467,
   s2N 6054899037, s2N 13182413612, s2N 6738455552, s2N 15480713307, s2P 3041158800,
   s2P 22381096281, s2P 14788512342, s2P 11663664565, s2P 3148663434, s2N 11234054946,
   s2P 11732940437, s2P 12141943562, s2P 6893320520, s2N 34815435040, s2N 32547171409,
   s2N 12935876388, s2P 43024021730, s2P 19298862055, s2N 59586708414, s2P 15708352386,
   s2P 4295698566, s2N 29321193092, s2P 22509695269, s2N 21078822742, s2N 45375966850,
   s2P 21684024072, s2P 30851773787, s2P 40575298970, s2P 44661390009, s2P 57389468831,
   s2P 5398198722, s2N 63242242965, s2N 13463015586, s2P 49363288412, s2P 72167182247,
   s2P 52364075896, s2P 13833058743, s2P 15019002502, s2N 18854040640, s2P 18282545128,
   s2N 20614858975, s2P 7831709961, s2N 53449729610, s2N 73642288106]
private def s2V1S3 : List ℤ :=
  [s2P 7466932545, s2P 18810525062, s2N 18597855971, s2N 60044899981, s2N 58054233217,
   s2P 83431539347, s2N 16387869603, s2N 42805295768, s2P 42827280044, s2N 61496506497,
   s2N 24438679168, s2N 30772530391, s2N 8929251607, s2N 88350570707, s2N 44032585398,
   s2N 41872335524, s2P 26386459211, s2N 24960857008, s2P 144057562668, s2N 17882130136,
   s2N 8529836629, s2P 42543237722, s2N 76860609039, s2P 27466272721, s2P 7737907826,
   s2P 1003894394, s2P 164857140778, s2P 328087305262, s2P 129429242193, s2N 95867238703,
   s2N 183221994111, s2N 90447333694, s2P 212847708324, s2P 263292832268, s2N 170302481460,
   s2N 271567169128, s2N 56580950872, s2N 267323835376, s2N 160859511562, s2N 116126048437,
   s2P 206040060367, s2P 584679786057, s2P 318758360406, s2N 485270959033, s2N 140160632925,
   s2N 446502085692, s2N 264090605481, s2P 215646758516, s2P 47501362712, s2N 488204524187,
   s2P 433015397803, s2N 387360881222, s2N 80492146912, s2N 141303131152, s2N 299506237735,
   s2N 696842634432, s2P 431328755110, s2P 765382899065, s2P 90597552144, s2N 417632109025,
   s2P 101758885431, s2P 308872164504, s2P 177293316313, s2P 812388855917]
private def s2V1S4 : List ℤ :=
  [s2P 1711638901460, s2P 2230823479945, s2P 1370645778177, s2P 721789580068, s2P 352472924437,
   s2P 412878612795, s2P 918742407635, s2P 704620474358, s2P 566122893760, s2P 278387127351,
   s2N 464544026194, s2N 1077588440855, s2N 1739252770898, s2N 1224240598474, s2P 119078340332,
   s2P 562943172147, s2P 854386032035, s2N 421051388740, s2P 308992875861, s2P 139653232188,
   s2N 1000959602689, s2N 702361824568, s2N 3510362975758, s2N 1521919197402, s2N 471886726888,
   s2P 1221150132261, s2P 667348307002, s2P 872070008567, s2N 3018436660770, s2N 1787988270750,
   s2N 1380885119347, s2N 5243705384075, s2N 5256099721516, s2N 3639188032023,
   s2P 4023825647953, s2P 8068708456704, s2P 7923040812052, s2P 1973273332297,
   s2N 6358198416183, s2N 7911305821587, s2N 2276059920, s2P 946711823348, s2P 439491234753,
   s2N 2245513087597, s2N 6225485794377, s2P 3949969740287, s2N 999756164744, s2N 350045724662,
   s2N 2414422690481, s2P 3755519203693, s2N 2600846412607, s2N 1478713471018,
   s2N 5311703036723, s2N 2393410164407, s2P 2368304432845, s2P 674135777663,
   s2P 1758391409699, s2N 41052121397, s2P 3230291540412, s2P 4252572220739, s2P 3331622407300,
   s2P 6284448612054, s2P 2962064703480, s2P 1679023313168]
private def s2V1S5 : List ℤ :=
  [s2P 531560331912, s2P 467842032056, s2P 7995341863112, s2P 3466517014322, s2P 5813491822639,
   s2N 3673509495398, s2N 1095064390623, s2P 880210285113, s2P 2255532974973,
   s2P 6761368032296, s2P 2784236417533, s2N 810099826893, s2N 5204502623542,
   s2N 2294561531012, s2P 2003375409384, s2P 6470364218247, s2P 156419436488, s2P 322571007575,
   s2N 4807353371829, s2N 5001284495144, s2N 5037894528134, s2P 850819155761,
   s2N 3540209287163, s2N 5241402049110, s2N 2672234842752, s2P 7041030931858,
   s2N 2112020340539, s2P 146693363164, s2N 317790691063, s2N 4281268334163, s2P 4134660071261,
   s2P 3353081701514, s2N 554087102814, s2N 1115990699874, s2N 7382837673283,
   s2N 7273502975799, s2N 8663950715438, s2N 2531770439440, s2P 3199520805298,
   s2P 903025602273, s2N 1042764189293, s2N 3063597896659, s2N 7681565079453,
   s2N 3162108980358, s2P 1634525350956, s2N 2584726496396, s2N 8216336111082,
   s2N 16288628855765, s2N 2618430936411, s2N 1306055052844, s2N 2147427323331,
   s2P 2977768490070, s2P 6677332485821, s2P 2193284278650, s2N 2956025536422,
   s2N 7813779683512, s2N 5358455541116, s2P 5889425692676, s2N 184814128020,
   s2N 5123788100535, s2P 2174741094211, s2N 4419398993716, s2P 1540215457202,
   s2N 2563163600895]
private def s2V1S6 : List ℤ :=
  [s2P 3663271039277, s2N 6967377874172, s2N 1397411430307, s2P 7721335821361,
   s2P 9670081200864, s2P 3946084396230, s2P 35911357366841, s2P 83788736975284,
   s2P 141638485635679, s2P 201907559702558, s2P 257177488590490, s2P 301524018479213,
   s2P 331243475324907, s2P 344928045686927, s2P 343118044758948, s2P 327802345024278,
   s2P 301915298984804, s2P 268859892451061, s2P 232058017761429, s2P 194560716023055,
   s2P 158774967994980, s2P 126344247205275, s2P 98175568144613, s2P 74568411395962,
   s2P 55387247496059, s2P 40228834320881, s2P 28556579703812, s2P 19794248573499,
   s2P 13383934441351, s2P 8818268108513, s2P 5656346593520, s2P 3529764712881,
   s2P 2142195400364, s2P 1264407030486, s2P 726121655485, s2P 406044553849, s2P 221361141707,
   s2P 117845395369, s2P 61396634975, s2P 31384300802, s2P 15782014564, s2P 7823824580,
   s2P 3827524696, s2P 1847015959, s2P 877747718, s2P 409938040, s2P 187868301, s2P 84471231,
   s2P 37324932, s2P 16261967, s2P 7016579, s2P 3011095, s2P 1289159, s2P 551237, s2P 235176,
   s2P 99860, s2P 42068, s2P 17524, s2P 7194, s2P 2895, s2P 1134, s2P 426, s2P 150, s2P 46]
private def s2V1S7 : List ℤ :=
  [s2P 11, s2P 2, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V1 : List ℤ :=
  s2V1S0 ++
    (s2V1S1 ++
    (s2V1S2 ++
    (s2V1S3 ++
    (s2V1S4 ++
    (s2V1S5 ++
    (s2V1S6 ++
    (s2V1S7 ++
    mm32k512krS2VecIn8)))))))
private def s2V2S0 : List ℤ :=
  [s2P 1033, s2P 9474, s2N 40267, s2N 12144, s2N 6465, s2P 20511, s2N 139984, s2N 98065,
   s2N 112444, s2P 160857, s2P 94348, s2P 199071, s2P 291888, s2P 198112, s2P 223368,
   s2P 400080, s2P 112033, s2N 56575, s2N 343356, s2P 74889, s2N 1044867, s2P 503614,
   s2P 1217795, s2P 1324889, s2P 896436, s2P 469755, s2P 589942, s2P 383885, s2P 3210770,
   s2N 2929251, s2N 931849, s2P 2193628, s2N 828802, s2N 5404645, s2N 697595, s2N 5124942,
   s2P 2241930, s2P 1124027, s2N 3647509, s2P 9745462, s2P 9499089, s2P 29669783, s2N 26144564,
   s2P 18065192, s2N 16574235, s2N 44196361, s2P 9595348, s2N 7865493, s2P 11474180,
   s2N 26581006, s2N 13551528, s2N 25748981, s2N 59901856, s2N 66055640, s2N 83575919,
   s2N 27922728, s2N 150699786, s2P 58640165, s2N 240908, s2N 25972261, s2N 22874748,
   s2P 13344082, s2P 77518601, s2N 96187982]
private def s2V2S1 : List ℤ :=
  [s2N 90103144, s2N 6077996, s2N 85269101, s2P 18270024, s2P 98464369, s2N 43158565,
   s2P 166539753, s2N 12207621, s2N 46740998, s2N 24804781, s2N 133823878, s2N 394875944,
   s2P 62275828, s2P 178760133, s2P 199966879, s2P 484307850, s2P 12186219, s2P 405819613,
   s2P 148529095, s2N 19917097, s2N 365794032, s2P 111122900, s2N 191231881, s2P 19386776,
   s2P 309420266, s2P 318878501, s2N 163911481, s2N 1133901872, s2N 1106156617, s2P 28447582,
   s2P 632347948, s2P 894091922, s2P 477396162, s2P 159732360, s2P 1124104183, s2N 1010397650,
   s2N 995037421, s2P 1461120328, s2N 1088266889, s2P 668817158, s2P 916223660, s2P 1724814883,
   s2P 117666766, s2P 1321601377, s2P 1568685155, s2P 11454462, s2P 845996629, s2N 1444420856,
   s2P 702086335, s2P 342205594, s2P 1920359709, s2P 2884477371, s2N 102524379, s2P 3090336951,
   s2P 4437363318, s2N 4939682914, s2P 772788713, s2P 2001023794, s2N 1888850510,
   s2N 3804171916, s2P 5210953592, s2P 1249820440, s2N 606033818, s2P 2191433253]
private def s2V2S2 : List ℤ :=
  [s2N 2572299248, s2P 6167328471, s2P 581234562, s2P 6861495203, s2P 2116968039, s2P 71255430,
   s2N 3755453066, s2N 11147518516, s2N 9007674288, s2N 1902171534, s2P 1501846442,
   s2P 2886779230, s2P 2918477221, s2N 4294618932, s2P 3217772363, s2N 570183652,
   s2N 6948106251, s2N 6790429229, s2N 13252508687, s2N 9576068570, s2N 17533975720,
   s2N 215310064, s2P 6442693636, s2P 8736624526, s2P 2824784080, s2P 4934545602,
   s2P 12517973432, s2N 16542521034, s2N 1540006313, s2N 19901698741, s2N 29693241444,
   s2P 10801472158, s2P 600330992, s2P 24868311992, s2P 49864082649, s2P 27149382198,
   s2P 58618295963, s2P 18740170243, s2N 41415455840, s2N 12274841615, s2P 3141557204,
   s2N 18780252338, s2P 26039169010, s2N 16237304426, s2P 23485984353, s2N 8344807250,
   s2N 38963188364, s2N 8135447997, s2P 3305846305, s2P 13036748820, s2P 33219418452,
   s2N 18300158773, s2P 15476872633, s2P 46296826273, s2N 27512927014, s2N 5524885861,
   s2P 81542145101, s2P 78879608241, s2P 8332789190, s2P 16408201251, s2P 41723430982,
   s2P 6456881352, s2N 46229400256, s2P 17899391556]
private def s2V2S3 : List ℤ :=
  [s2P 114422062991, s2P 38246450890, s2P 3015437695, s2N 71043326735, s2N 68171472017,
   s2N 79116781964, s2N 5923449709, s2N 43811016352, s2N 30040009048, s2N 63623766135,
   s2N 13021397215, s2P 23465029436, s2P 106265596413, s2P 64793491578, s2N 30696814910,
   s2N 17590428122, s2P 31733915588, s2P 26238065549, s2P 41665326563, s2N 36205245271,
   s2N 29335486385, s2P 53032681929, s2N 13473883864, s2N 100722684592, s2N 103495086815,
   s2P 47205131597, s2N 57505067362, s2N 85035674850, s2P 119427018369, s2P 44528829774,
   s2N 98487074292, s2N 76592790996, s2P 191165507702, s2P 305234047019, s2P 330460439281,
   s2N 165899770331, s2P 373166514219, s2P 65264022157, s2P 213850960359, s2N 39499801112,
   s2N 434523341054, s2N 525280059138, s2N 444095697583, s2N 54757955411, s2P 59032864735,
   s2P 117318030336, s2P 336269648242, s2P 674868190483, s2N 170650564928, s2P 476623300840,
   s2P 167555444938, s2N 192322088757, s2N 90822282647, s2N 374311199319, s2P 432848305963,
   s2P 289923557247, s2N 133004549705, s2N 516452041964, s2P 130396317482, s2P 501101927498,
   s2N 257409672473, s2N 713378146837, s2N 482472857065, s2N 103142312738]
private def s2V2S4 : List ℤ :=
  [s2P 143383984463, s2P 36696461611, s2P 105972377449, s2N 408833051406, s2P 281017677445,
   s2P 621823575532, s2P 340273641371, s2P 261465831642, s2P 1264865087630, s2P 1629555620510,
   s2P 1341201279453, s2P 1864393455587, s2P 124195206768, s2P 1804068577520, s2P 168649695782,
   s2N 852339659638, s2N 1032520555846, s2N 1700729240613, s2N 84167230450, s2N 152017406025,
   s2N 1934503165417, s2N 1707049203678, s2N 769080639688, s2P 1604665691256, s2N 439661282092,
   s2N 150937979751, s2N 185674493859, s2N 1031910126069, s2P 1334765751040, s2P 886920624315,
   s2P 2999756070113, s2P 3374773753971, s2P 722320369810, s2N 105003567448, s2P 1833777740620,
   s2P 2405763933496, s2P 3323751457673, s2P 4641713649442, s2P 1195602765350,
   s2N 3279160043816, s2N 10374176620318, s2N 6607878407016, s2P 1814041691963,
   s2P 10391712522764, s2P 8458277742847, s2N 1292758064083, s2N 1040081456971,
   s2P 1801014472870, s2P 518485337299, s2N 2150147864500, s2N 3123396741740, s2P 335843307014,
   s2P 1414114889560, s2N 800101123724, s2N 3302086031406, s2N 1307959028113,
   s2P 4177623284964, s2P 913705965087, s2N 1175721069185, s2N 5826227407476, s2N 502805134307,
   s2N 3054491582986, s2N 1226535347157, s2P 1062159493208]
private def s2V2S5 : List ℤ :=
  [s2N 1376675499870, s2P 1682084506311, s2P 738886875097, s2P 2985121002782,
   s2P 6003993723554, s2P 6805352246901, s2N 1318826353057, s2P 1445009387062,
   s2N 1024176538139, s2P 5403717572062, s2P 4821345929733, s2P 6816423136450,
   s2P 2654660420215, s2N 529450577650, s2N 4712098610069, s2P 3431473405364,
   s2P 5197150268049, s2N 6674570621984, s2N 1204244869109, s2P 450186279366,
   s2P 3299718981491, s2N 4933957005640, s2N 8153636585109, s2P 4296429240355,
   s2N 2346216614680, s2N 540256965451, s2N 3355799402893, s2P 452774088561, s2N 2980264655127,
   s2N 5823628930207, s2P 5243117139710, s2N 2407518473024, s2P 2080089379358,
   s2N 969513557659, s2N 2561344891309, s2N 504105098542, s2N 1258437633770, s2N 2015362971538,
   s2P 6023607744695, s2P 2003283799924, s2N 3091873054303, s2N 5572671541244,
   s2N 6900542954868, s2N 8061236451360, s2N 7724310269709, s2N 2207149362465,
   s2P 5511187949266, s2N 5235132082486, s2N 8406993224811, s2N 501441070146, s2P 592744616066,
   s2P 720528730074, s2N 3260702218569, s2N 11516573893522, s2N 1488808578446,
   s2N 13520236101462, s2N 8340265304776, s2N 2368879163003, s2P 9320231428121,
   s2P 2134175595983, s2P 1006450455481, s2N 2556450784283, s2N 1377653893833,
   s2N 5909198198796]
private def s2V2S6 : List ℤ :=
  [s2P 3888118493477, s2P 1001571971521, s2N 8392405917153, s2N 1021494236815,
   s2P 6128413339214, s2N 1072937977248, s2N 7867126856942, s2P 2955881651648,
   s2P 5075474487267, s2P 4515624035081, s2N 4443476373401, s2P 11618984556831,
   s2P 5894451808705, s2P 18714331997017, s2P 61826315711277, s2P 118215088532602,
   s2P 180151052444273, s2P 239573273705733, s2P 289660852237312, s2P 325691973418310,
   s2P 345297118628654, s2P 348304699371937, s2P 336349282085936, s2P 312346664653105,
   s2P 279906215241725, s2P 242755419080536, s2P 204259769446747, s2P 167103710023509,
   s2P 133155580456335, s2P 103492691404663, s2P 78532344526088, s2P 58208190912642,
   s2P 42143789591249, s2P 29795903528946, s2P 20559027057859, s2P 13834564021486,
   s2P 9072704680553, s2P 5794968911654, s2P 3603465675011, s2P 2180998986475,
   s2P 1284926995136, s2P 737107772869, s2P 411986344841, s2P 224564209569, s2P 119522437432,
   s2P 62212274462, s2P 31721925275, s2P 15871882596, s2P 7803644686, s2P 3773761517,
   s2P 1795623584, s2P 840529644, s2P 386900351, s2P 175060728, s2P 77862149, s2P 34063605,
   s2P 14678065, s2P 6241786, s2P 2625386, s2P 1094611, s2P 453126, s2P 186381, s2P 76156,
   s2P 30871]
private def s2V2S7 : List ℤ :=
  [s2P 12384, s2P 4897, s2P 1896, s2P 710, s2P 253, s2P 81, s2P 21, s2P 4, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0]
private def s2V2 : List ℤ :=
  s2V2S0 ++
    (s2V2S1 ++
    (s2V2S2 ++
    (s2V2S3 ++
    (s2V2S4 ++
    (s2V2S5 ++
    (s2V2S6 ++
    (s2V2S7 ++
    mm32k512krS2VecIn8)))))))
private def s2V3S0 : List ℤ :=
  [s2P 10288, s2P 27934, s2P 14998, s2P 12085, s2P 86024, s2P 51870, s2P 34102, s2N 74707,
   s2N 89394, s2N 178038, s2P 73220, s2N 10331, s2N 103976, s2N 241955, s2N 26839, s2N 473315,
   s2N 347246, s2N 724368, s2N 314414, s2N 114618, s2N 441856, s2P 64580, s2P 502563,
   s2P 2081431, s2N 1131209, s2N 1356540, s2P 616375, s2P 2437188, s2P 1558608, s2N 3850873,
   s2N 4512799, s2N 2007681, s2P 2765084, s2N 5802927, s2N 10083478, s2N 14737915,
   s2N 15936285, s2N 17902689, s2P 14380183, s2P 14649291, s2N 32161888, s2N 29414066,
   s2P 1334306, s2P 1091614, s2P 4467746, s2N 5492324, s2N 1450682, s2P 47907801, s2N 25462828,
   s2P 35942856, s2N 85356065, s2N 48711236, s2N 22716002, s2P 46422228, s2N 52315437,
   s2P 17692037, s2P 13113573, s2P 36130443, s2P 10177535, s2P 4880491, s2P 138016749,
   s2P 141513567, s2P 78702801, s2P 135980348]
private def s2V3S1 : List ℤ :=
  [s2P 3642573, s2P 34877572, s2N 26510847, s2N 13940445, s2P 115994829, s2P 111712968,
   s2N 35715139, s2P 119613954, s2N 360998560, s2N 180315244, s2N 98127098, s2N 60979796,
   s2P 59749898, s2N 159517229, s2N 18033902, s2N 259607649, s2P 66613654, s2P 423038672,
   s2N 104293845, s2P 36499215, s2P 89780843, s2N 83400884, s2P 173982951, s2P 435138001,
   s2N 369671432, s2N 152003581, s2N 610254604, s2P 5687254, s2P 572926858, s2N 405092562,
   s2N 1561523932, s2N 1908757589, s2N 545036610, s2N 665135973, s2P 620410755, s2P 237489486,
   s2P 724249020, s2P 1563900947, s2P 1807099198, s2P 146990953, s2N 736796367, s2P 620159848,
   s2P 125121128, s2P 543588038, s2N 953048946, s2N 892064338, s2N 2097731678, s2N 2731501892,
   s2N 2973283793, s2P 141569421, s2P 829107797, s2P 2267231281, s2P 4221582372,
   s2N 2230576393, s2P 2134553126, s2P 6815313994, s2P 5586714792, s2P 1118856942,
   s2N 123167987, s2P 3634945495, s2P 1528059704, s2N 6653145, s2P 3967693837, s2N 1617544116]
private def s2V3S2 : List ℤ :=
  [s2N 137521747, s2P 927181512, s2P 1599170571, s2P 1344954346, s2P 4157200693,
   s2P 1879300807, s2N 941314595, s2N 2673433387, s2P 4090650177, s2P 3947165124,
   s2P 2379402097, s2P 7497273963, s2P 6006690280, s2N 7733835568, s2N 1475791624,
   s2P 11384877415, s2P 2468086610, s2P 9638722949, s2P 2918807009, s2P 9225626815,
   s2P 3197361299, s2N 10215146200, s2N 16670049414, s2N 12340932075, s2N 7153666888,
   s2P 15605078491, s2N 9272146061, s2N 25236023717, s2N 16197327009, s2P 1999158706,
   s2P 15458370992, s2N 5019621715, s2N 23641455691, s2N 28082427949, s2N 39523179410,
   s2N 8188497447, s2P 16468389160, s2P 2591353446, s2P 15885382095, s2N 12986316010,
   s2P 18098445293, s2P 34838199253, s2P 35104292002, s2P 50891018868, s2P 31063596597,
   s2P 53165286734, s2P 9968059190, s2N 30045058, s2N 7414527562, s2N 28914948890,
   s2N 23484755541, s2N 45469948673, s2N 23105531358, s2P 43154567376, s2P 4613125940,
   s2N 5499159305, s2P 5008478895, s2P 72847526339, s2P 31780128279, s2P 49858457711,
   s2P 10493786820, s2P 51443901691, s2P 36245966746, s2P 7943543070]
private def s2V3S3 : List ℤ :=
  [s2P 5071527199, s2N 8478330972, s2N 69731751973, s2N 73488204984, s2N 46178495947,
   s2N 2528535283, s2P 41469882658, s2N 4827302300, s2N 71931747467, s2N 53511293154,
   s2N 71019225129, s2P 32082751747, s2P 79284091061, s2P 32488774577, s2N 25863307586,
   s2P 677962675, s2P 62428165230, s2P 97286143966, s2P 80327217031, s2N 38296352366,
   s2N 135705756783, s2N 11724421001, s2P 30041781076, s2P 18529990533, s2P 186788961905,
   s2N 205852661177, s2P 173440222124, s2N 117535403276, s2P 171790502109, s2P 67550563725,
   s2P 99986291440, s2P 210939996132, s2N 90623393519, s2N 186634385394, s2N 112694370844,
   s2P 138308840053, s2P 9109181378, s2N 69565346377, s2N 354568210823, s2P 164839654205,
   s2P 166138470583, s2P 244318426968, s2P 379044658451, s2P 401263131801, s2P 370435512423,
   s2P 302631605146, s2P 342258865035, s2P 184886185726, s2N 30399472089, s2N 176966638903,
   s2N 463257640928, s2N 490944010368, s2N 341670728379, s2N 41584024937, s2P 137192375666,
   s2P 240640090143, s2P 423051275564, s2P 709181119767, s2P 528162608540, s2P 466349572030,
   s2P 190094695097, s2P 392018945884, s2N 196943434775, s2N 67808283221]
private def s2V3S4 : List ℤ :=
  [s2N 326692263396, s2N 194938291465, s2N 435726807806, s2N 1276959602450, s2N 633627985035,
   s2N 385313142645, s2N 175822780102, s2P 611874286332, s2P 506765720145, s2P 509574321205,
   s2P 603927658727, s2P 667014797354, s2P 318196216792, s2N 423598801572, s2N 663336172226,
   s2P 361460577704, s2P 631795554408, s2P 981155800521, s2P 1554639378814, s2P 293030619256,
   s2P 2755956733875, s2P 2496195295721, s2P 575111128843, s2P 130606292193, s2P 663045611893,
   s2P 105012501369, s2N 388432027186, s2P 1335937574554, s2P 2302771752803, s2P 92700462069,
   s2P 2193210821501, s2P 52351006728, s2N 202442401951, s2P 776382802057, s2P 1110364493232,
   s2P 2237199727242, s2N 570860027010, s2P 410279345961, s2P 2162627205209, s2P 2525235439744,
   s2P 1490662182145, s2P 2209403853310, s2P 1605546869245, s2P 1840073429159,
   s2P 5796255040477, s2P 11054201522136, s2P 5494760082146, s2N 7345853381575,
   s2N 8645804182724, s2N 6033611088104, s2N 3145364588921, s2N 1273062399422,
   s2P 2926690663017, s2P 3439529358140, s2P 4674050378742, s2N 3405950195303,
   s2N 4534389052752, s2P 122323038141, s2N 1583775508275, s2N 696070402973, s2N 2802975156566,
   s2N 1396912498970, s2N 3644131122966, s2N 4001950414292]
private def s2V3S5 : List ℤ :=
  [s2N 567694791047, s2P 1521658712433, s2N 632973138144, s2N 1589648226175, s2P 4477341869575,
   s2N 1356412498730, s2P 478978483347, s2N 932412602987, s2P 1617981841126, s2P 5154831459999,
   s2N 5469577291642, s2P 1981120123435, s2N 4310859453594, s2P 7942592220499,
   s2P 1516749632541, s2P 727679124342, s2N 2514863881924, s2P 11772995379699,
   s2P 6217225555766, s2P 1705693480219, s2P 3116754709318, s2P 3973335659323,
   s2P 5081250000904, s2P 7490283306208, s2N 2682632613013, s2P 2434096333130,
   s2N 1737278782740, s2N 287769367895, s2P 1214083687682, s2N 4284512201734, s2N 689483200546,
   s2N 3051239718265, s2N 781015305187, s2N 310280845902, s2P 4574769448411, s2N 2935497255690,
   s2P 452755887071, s2N 2805934590823, s2P 10595671109, s2N 421584310587, s2N 3018990135040,
   s2N 2396771834897, s2N 6351599019953, s2P 1399489929085, s2P 1818183008418,
   s2P 3817909371288, s2P 9014941392342, s2N 193840456300, s2N 381264607881,
   s2N 12761901051569, s2N 8524718949133, s2N 2278767621853, s2N 1500843409384,
   s2N 8631925488739, s2N 4180831198377, s2N 2014829138266, s2N 711366869206,
   s2N 4812056406633, s2P 1889375002938, s2P 3525353942450, s2N 8896543865138,
   s2N 10096916741104, s2N 9659840648843, s2N 9658790059179]
private def s2V3S6 : List ℤ :=
  [s2N 4027695174616, s2N 10698921921654, s2N 1745523572743, s2N 2359683982353,
   s2P 3039173189543, s2N 7996721930453, s2N 4499662846412, s2N 8955908481072,
   s2P 4742417026638, s2P 1121375338354, s2N 5289308177799, s2N 387144246470, s2N 758435602131,
   s2N 3471718068757, s2N 1373126815103, s2P 5942847716356, s2N 7290790361148,
   s2P 929846972152, s2P 10269207126022, s2P 8388617444873, s2P 12671562749771,
   s2P 53744094033496, s2P 109902609875437, s2P 173166245189977, s2P 234955284937389,
   s2P 287811501936754, s2P 326386956045156, s2P 347840188930760, s2P 351781899386103,
   s2P 339888851908452, s2P 315298147583452, s2P 281905284497363, s2P 243695305707368,
   s2P 204215927977113, s2P 166253975887640, s2P 131718819837116, s2P 101690262599785,
   s2P 76566369491319, s2P 56249027362662, s2P 40322296944830, s2P 28199638957458,
   s2P 19233002909153, s2P 12786718462321, s2P 8282998595249, s2P 5226083923337,
   s2P 3210905710542, s2P 1920953207514, s2P 1119190319385, s2P 635243997974, s2P 351458665044,
   s2P 189691482302, s2P 99974642945, s2P 51510181523, s2P 25976437809, s2P 12836775424,
   s2P 6222516006, s2P 2961103703, s2P 1384032450, s2P 635576221, s2P 286798930, s2P 127183421,
   s2P 55441987, s2P 23769698, s2P 10030951]
private def s2V3S7 : List ℤ :=
  [s2P 4171398, s2P 1711664, s2P 693980, s2P 278346, s2P 110528, s2P 43453, s2P 16898,
   s2P 6482, s2P 2441, s2P 893, s2P 311, s2P 100, s2P 27, s2N 5, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V3 : List ℤ :=
  s2V3S0 ++
    (s2V3S1 ++
    (s2V3S2 ++
    (s2V3S3 ++
    (s2V3S4 ++
    (s2V3S5 ++
    (s2V3S6 ++
    (s2V3S7 ++
    mm32k512krS2VecIn8)))))))
private def s2V4S0 : List ℤ :=
  [s2P 994, s2P 9400, s2P 41671, s2N 18958, s2N 24877, s2N 175, s2N 113482, s2P 5326,
   s2N 128993, s2N 24453, s2N 31418, s2N 306010, s2N 163312, s2N 113869, s2P 13880, s2P 16458,
   s2N 314815, s2P 323517, s2P 582218, s2P 210346, s2P 1253742, s2P 189630, s2N 545659,
   s2N 1358561, s2N 706584, s2P 660386, s2P 2759443, s2P 96595, s2N 809783, s2N 4189300,
   s2N 1321253, s2N 2211154, s2N 5889868, s2P 5114260, s2N 6175095, s2N 7267453, s2N 6010026,
   s2N 8795442, s2P 17254973, s2N 1854985, s2P 46657781, s2P 2873726, s2N 39324539,
   s2N 59768358, s2P 38304819, s2P 261282, s2N 27814302, s2P 7769154, s2N 38384510,
   s2N 34035533, s2N 23625166, s2P 37990931, s2P 41041562, s2P 42069018, s2N 21934246,
   s2P 21789307, s2N 86060306, s2N 49496770, s2N 60707160, s2P 45642390, s2N 2923146,
   s2N 18825202, s2N 17180037, s2N 70482228]
private def s2V4S1 : List ℤ :=
  [s2N 161004582, s2N 164371804, s2N 20215100, s2N 29136140, s2N 256162936, s2N 9445249,
   s2P 173813588, s2P 15320674, s2N 34014220, s2P 8790877, s2P 151461506, s2P 308254701,
   s2P 71955763, s2N 20232247, s2P 97142579, s2P 123856544, s2N 544534710, s2N 282101159,
   s2P 153201050, s2P 81198338, s2N 32193202, s2N 429529152, s2N 70142347, s2N 135719722,
   s2P 367880765, s2P 215405086, s2N 477471379, s2N 538945127, s2N 134766291, s2P 746797536,
   s2P 485923506, s2N 230970108, s2N 810117351, s2N 55120969, s2N 323624618, s2P 1365897881,
   s2P 125733542, s2N 1015605698, s2P 1509952194, s2P 462421368, s2N 1089131191,
   s2N 1188487581, s2N 779069062, s2P 339141883, s2P 3042638553, s2N 677624448, s2N 1662716902,
   s2N 1339308965, s2P 1347809805, s2P 1248201425, s2P 1026229748, s2P 579464911,
   s2N 575119458, s2N 442262285, s2P 545040026, s2N 7821861660, s2N 2795463698, s2N 2348831327,
   s2P 574572408, s2N 1922874611, s2P 790837499, s2N 57229253, s2N 3032126184, s2N 4116005947]
private def s2V4S2 : List ℤ :=
  [s2P 4694159947, s2P 2035293832, s2N 1776508457, s2N 3560068735, s2N 2326237516,
   s2P 431731098, s2P 2160286048, s2P 6917023300, s2P 9804608183, s2P 3984773763,
   s2P 3155535323, s2N 1011529310, s2N 2173300450, s2N 6042486059, s2N 852520203,
   s2N 158868328, s2N 9183165857, s2N 9350308177, s2P 7764039145, s2N 209648892,
   s2N 6061558890, s2P 2785020309, s2N 312191266, s2N 7222142391, s2N 2471452037,
   s2P 751483907, s2N 6193051271, s2N 16615802374, s2N 27909100713, s2N 24055574237,
   s2N 10304080362, s2N 7874378609, s2N 1473100352, s2N 16058770864, s2P 20387212425,
   s2P 8333272053, s2N 29712431352, s2P 2694355858, s2P 12278801326, s2P 8949518561,
   s2P 5021909250, s2P 37984478425, s2P 37478522851, s2P 6268722660, s2P 22748721982,
   s2P 13396001795, s2P 21656772912, s2P 6610437493, s2N 5575604847, s2N 19477785883,
   s2N 15105319439, s2P 56550048757, s2P 52458072040, s2P 25599247812, s2P 32896828495,
   s2P 51661416862, s2P 39266726900, s2N 2487029414, s2N 52263301507, s2N 24923654916,
   s2N 5880822248, s2N 23977858539, s2N 30439392638, s2N 9508806878]
private def s2V4S3 : List ℤ :=
  [s2P 14794028909, s2N 34927949241, s2N 15569610522, s2N 32625003294, s2N 55791220977,
   s2N 22020386707, s2N 19219248017, s2N 59727238045, s2N 62290528449, s2P 27904780124,
   s2N 11396443476, s2N 60881416244, s2N 84600294016, s2N 73698110207, s2N 138192566636,
   s2N 139003517166, s2N 174722557044, s2N 270704276531, s2N 20827981973, s2P 24994635608,
   s2N 6657864178, s2N 90714580233, s2N 122440854548, s2N 17820712796, s2N 6807637393,
   s2P 136811026921, s2N 94392409111, s2P 94476063311, s2P 198430297567, s2P 88298114011,
   s2P 67839660973, s2N 24393629388, s2P 18349310203, s2P 8140027785, s2P 131311283728,
   s2P 109592623600, s2P 162996691177, s2N 132850462484, s2P 318524651305, s2P 137810170576,
   s2P 120169240481, s2N 2236793695, s2N 14827295823, s2P 43262291690, s2N 28562795042,
   s2N 58044949664, s2N 192989933189, s2N 108799614006, s2P 125526351660, s2P 152065304351,
   s2P 36718102653, s2N 413149192328, s2P 193065129775, s2P 451788027889, s2P 250939060096,
   s2N 542359235639, s2N 519636462786, s2N 72538448865, s2N 11781822924, s2N 421045563298,
   s2N 315675535537, s2N 295898322986, s2N 644828364708, s2N 169908343996]
private def s2V4S4 : List ℤ :=
  [s2N 204568843037, s2P 68942100433, s2P 533763338895, s2P 757037804248, s2P 490580669827,
   s2P 387506521483, s2N 141034214219, s2P 154044012069, s2P 351919541612, s2N 304170013790,
   s2P 513212651472, s2P 1378952090038, s2P 840203926559, s2P 396759018271, s2P 913802353202,
   s2P 67574790660, s2P 76664676617, s2N 339561811837, s2N 1167936992906, s2P 1258875399737,
   s2P 791822582493, s2P 1795103761940, s2N 1129729111636, s2P 416872930171, s2P 1231179797525,
   s2P 903705132742, s2N 31706812625, s2N 1290744894167, s2N 1379362032917, s2N 2366700522465,
   s2N 1986956916975, s2P 994460734705, s2P 578766926658, s2P 779162716135, s2P 778952056411,
   s2P 22591631857, s2N 2290070295662, s2N 1909080361119, s2P 554361460101, s2P 805341403026,
   s2N 2520541198950, s2N 98853538453, s2P 257298842587, s2N 2063773621222, s2P 1426082293998,
   s2N 3769887705359, s2P 2492448607712, s2P 5827767371381, s2N 1776223418638,
   s2N 1665898389396, s2P 4855370862558, s2P 5333051370822, s2P 9591968787067,
   s2P 8070914063433, s2P 5165839973285, s2N 2034929508121, s2N 3140989922045,
   s2N 9150606271132, s2N 6334688372548, s2P 2255410567084, s2P 4079534641749,
   s2P 541908297993, s2N 2889045139085, s2P 1527456716416]
private def s2V4S5 : List ℤ :=
  [s2N 5357000872175, s2P 2185839431959, s2N 3839199729657, s2N 4631790269876,
   s2N 7402903708739, s2N 242498783001, s2N 3689711313477, s2N 908167974788, s2N 5328892117529,
   s2P 440217714183, s2N 764351376143, s2N 2571136911566, s2P 421990543279, s2N 4723098549106,
   s2P 582736124963, s2P 9106535687302, s2P 3624670253670, s2P 1377039163913,
   s2N 1422942048897, s2P 2479004599689, s2N 4161301409786, s2N 4710732325129,
   s2P 761928905781, s2P 1767898331225, s2P 6336159422319, s2P 3611784805852,
   s2P 4291161784731, s2P 438542765060, s2P 8196487334291, s2P 4467349226398,
   s2N 4826935203419, s2N 4653956446026, s2N 578267715026, s2N 2258165643784, s2N 564897307709,
   s2P 2814159940264, s2P 1838723797798, s2N 3997456907432, s2N 540296706979,
   s2N 5121609028818, s2N 4693177425997, s2N 1638896212466, s2N 390691224786,
   s2N 1471312966673, s2N 199010299518, s2N 584618969240, s2N 854445386886, s2P 4511459512048,
   s2N 1012642655418, s2N 4853162720686, s2P 6552298751187, s2P 444992465769,
   s2P 8603799275872, s2P 10779252149435, s2N 2042312826490, s2N 4082786747690,
   s2N 956050632497, s2N 9856817399502, s2N 3717000800638, s2N 6824733138549, s2P 649046626461,
   s2N 9132342572836, s2N 4352936663414, s2N 5733133841663]
private def s2V4S6 : List ℤ :=
  [s2P 6271426069852, s2P 262804665434, s2N 2485271937029, s2N 4479213557433,
   s2N 8667731330977, s2N 4904986984158, s2N 11911860608225, s2N 12770530961604,
   s2N 5920739907417, s2P 5160374672966, s2P 7426250626385, s2N 5154024760834,
   s2P 2605932669524, s2N 6992852853296, s2P 4270298721838, s2P 5304258727804,
   s2N 3872863129898, s2N 7400498304875, s2P 2670447950165, s2P 2596982466878,
   s2N 6101519886664, s2P 5466443207002, s2P 3498480791416, s2P 6519268116741,
   s2N 1268673947197, s2P 10533006157611, s2P 7813181452513, s2P 15167638296298,
   s2P 58862016563806, s2P 117696278363106, s2P 183055016233467, s2P 245854532738621,
   s2P 298332140555513, s2P 335097204591717, s2P 353549616399858, s2P 353770170827274,
   s2P 338008950978430, s2P 309933047181703, s2P 273813315247966, s2P 233810929728832,
   s2P 193469633213666, s2P 155448760357909, s2P 121470234855332, s2P 92416359088999,
   s2P 68507152084182, s2P 49498318224126, s2P 34861890730001, s2P 23931546301513,
   s2P 16008635155974, s2P 10432536345110, s2P 6621817402237, s2P 4093061543696,
   s2P 2463672879676, s2P 1444175255519, s2P 824636344439, s2P 458862648279, s2P 248954422009,
   s2P 131787541647, s2P 68123355277, s2P 34416448928, s2P 17008825861, s2P 8229903828,
   s2N 3901779768, s2P 1813676028]
private def s2V4S7 : List ℤ :=
  [s2P 827005499, s2P 370067579, s2P 162562045, s2P 70123090, s2P 29714689, s2P 12375554,
   s2P 5068986, s2P 2043536, s2P 811585, s2P 317794, s2P 122790, s2P 46822, s2P 17610,
   s2P 6526, s2P 2372, s2P 833, s2N 275, s2P 82, s2P 18, s2P 2, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0]
private def s2V4 : List ℤ :=
  s2V4S0 ++
    (s2V4S1 ++
    (s2V4S2 ++
    (s2V4S3 ++
    (s2V4S4 ++
    (s2V4S5 ++
    (s2V4S6 ++
    (s2V4S7 ++
    mm32k512krS2VecIn8)))))))
private def s2V5S0 : List ℤ :=
  [s2N 11238, s2P 14946, s2N 18551, s2N 25243, s2P 32985, s2P 68944, s2N 44093, s2P 96396,
   s2N 32692, s2N 76669, s2N 181589, s2P 12744, s2P 41729, s2P 51784, s2N 174972, s2N 62701,
   s2P 85118, s2P 392759, s2P 496579, s2N 499527, s2P 98704, s2P 685956, s2P 967382,
   s2P 257121, s2P 3253796, s2P 2901440, s2P 3195469, s2N 1942553, s2P 4132715, s2N 5851640,
   s2N 4562818, s2N 6844316, s2N 73099, s2N 20234160, s2P 3697773, s2P 23712252, s2P 4532758,
   s2P 2843125, s2N 65876, s2N 32888253, s2N 14984817, s2N 24602262, s2N 7146852, s2N 28378820,
   s2N 54070716, s2P 12553950, s2N 73234054, s2P 31312658, s2P 17059963, s2N 44722562,
   s2P 7085875, s2P 38022475, s2N 41701755, s2P 27042557, s2P 12568918, s2P 23231583,
   s2P 7153238, s2P 75385608, s2P 79248216, s2P 53763968, s2P 14913793, s2P 61012034,
   s2P 105327271, s2N 61062380]
private def s2V5S1 : List ℤ :=
  [s2P 18758722, s2P 84365486, s2P 33488016, s2P 44130923, s2N 18563174, s2P 42038803,
   s2N 145796685, s2N 64703856, s2P 131214163, s2P 278464443, s2P 36896149, s2N 86852835,
   s2N 117908923, s2N 94863064, s2N 68335267, s2P 308815027, s2P 357615421, s2N 8939599,
   s2P 244938615, s2P 117650223, s2N 65309804, s2P 44065821, s2P 31184431, s2P 363633448,
   s2P 587047229, s2N 106383388, s2N 43653720, s2P 230244660, s2P 241470538, s2P 923599633,
   s2P 570349527, s2P 504430519, s2P 358034941, s2P 1197885018, s2P 915536707, s2P 254532705,
   s2P 448937826, s2P 816846574, s2N 75068591, s2N 728280581, s2N 1380938090, s2N 1670947596,
   s2P 560043172, s2P 1582864071, s2P 2470575453, s2P 908033618, s2N 719659112, s2N 314813555,
   s2N 1296445689, s2N 370168979, s2P 228359704, s2N 3141171010, s2N 2151260711,
   s2P 1960098656, s2N 2901712333, s2P 1409596088, s2P 407508751, s2P 5547157841,
   s2P 159817255, s2P 610769183, s2P 1031547661, s2P 276386526, s2P 376096747, s2P 3469306983]
private def s2V5S2 : List ℤ :=
  [s2P 4567233300, s2P 3436431128, s2P 737749658, s2N 2007218785, s2N 1224029619, s2N 60473667,
   s2P 5107321612, s2N 2504739134, s2P 4677307833, s2P 1336948568, s2P 1091936228,
   s2P 1118862907, s2N 1364989757, s2P 2323725864, s2P 3219441875, s2P 5094795459,
   s2P 14092118062, s2N 6859985427, s2N 5536793242, s2N 3614014102, s2P 1084552580,
   s2N 8042635643, s2N 7402482793, s2N 1927061538, s2P 7285235217, s2P 2312315995,
   s2N 12717195417, s2N 12740777366, s2N 125174665, s2N 7955939896, s2P 3868339368,
   s2P 1544403233, s2N 13147273345, s2N 30731162162, s2N 15969318675, s2P 6792147049,
   s2P 8344778696, s2P 18276449724, s2N 27034633466, s2N 30698838274, s2P 7569517010,
   s2P 804537477, s2P 20273364349, s2P 4668785708, s2P 27822517217, s2N 8262789613,
   s2P 9127890745, s2P 40629648518, s2N 38392136495, s2N 17873477450, s2P 13969830067,
   s2N 2028908282, s2P 11021710649, s2P 20248511433, s2N 1785165434, s2P 31933949572,
   s2N 9868348268, s2N 37519308274, s2P 15107295315, s2N 48863041733, s2P 8197696960,
   s2P 4473450250, s2N 34506433526, s2N 15118390126]
private def s2V5S3 : List ℤ :=
  [s2N 6904145629, s2P 11180408255, s2N 29630716389, s2N 32815423115, s2N 34529101409,
   s2P 29357955845, s2N 61743857480, s2N 84925249341, s2N 249808871, s2N 63311582737,
   s2N 38432414784, s2N 49070684948, s2P 7622082051, s2P 48545133950, s2N 50688598503,
   s2N 39232100504, s2P 118363685657, s2P 18835626634, s2N 12296108757, s2P 70139516124,
   s2P 15788192563, s2P 15183168077, s2N 68567562194, s2P 69114745048, s2N 97914109524,
   s2N 72644388884, s2N 93522193796, s2P 333209014433, s2N 5194660905, s2N 263227659636,
   s2P 164674952038, s2N 69799581035, s2N 74944820385, s2N 39860128006, s2P 72475985737,
   s2N 10681934407, s2P 124140142803, s2N 101155284911, s2N 145218452013, s2P 119404781846,
   s2N 84263964374, s2N 13826030328, s2P 193818203670, s2P 242999140240, s2N 162999411975,
   s2N 67347134662, s2N 61208632929, s2P 155250965963, s2N 374620542509, s2N 320895043755,
   s2N 440966518046, s2N 312834958243, s2P 491877032609, s2P 96372967822, s2P 14215270241,
   s2P 178763555921, s2P 176473888656, s2N 104205337237, s2P 233270248628, s2P 39675807447,
   s2P 300896789089, s2P 10354303657, s2N 98337728994, s2P 296697225128]
private def s2V5S4 : List ℤ :=
  [s2N 87494896056, s2N 237887560859, s2N 229614401997, s2P 230023995208, s2N 127887601118,
   s2P 36933560562, s2P 144631422277, s2N 327208475609, s2P 173593306035, s2P 183002100435,
   s2P 855557708062, s2P 984349540920, s2P 744200609279, s2P 1409887384615, s2P 973387770881,
   s2P 773929850973, s2N 157113163085, s2N 325705413453, s2P 208597369853, s2P 1267683523972,
   s2P 236333359529, s2N 38059823731, s2P 15311473242, s2N 333965145804, s2N 920878636738,
   s2N 1424492858002, s2N 154351959817, s2N 715196908748, s2P 1482928024147, s2P 1077922359841,
   s2P 930241451434, s2P 1145501662716, s2N 431868461243, s2N 1281651967300, s2N 836725504813,
   s2P 960325381220, s2P 1498149927057, s2P 100545696474, s2N 1251543442506, s2P 284441476027,
   s2N 860086436282, s2N 3049395394607, s2N 4068583736840, s2N 883042712939, s2N 2599818486238,
   s2N 5590754607477, s2N 4922723421237, s2P 1188251461584, s2P 1845578935862,
   s2P 1861890205386, s2P 1320618676282, s2P 3263414861224, s2N 1227865313064,
   s2P 1061465250369, s2N 1109965270210, s2P 623008909209, s2P 567496498195, s2P 1918617519982,
   s2P 549343351567, s2P 3720519650971, s2N 5127515967360, s2N 9030546034680,
   s2N 2000732308059, s2P 2434371234279]
private def s2V5S5 : List ℤ :=
  [s2N 4095176991173, s2N 10906033512477, s2N 8792521414214, s2P 3234780301015,
   s2P 1712465755269, s2N 10658046945185, s2N 2763680404194, s2P 1553929700034,
   s2N 3060427578162, s2N 58802988829, s2N 3226230591160, s2N 1622780407351, s2N 1764477652244,
   s2P 1871481618920, s2P 8181396136885, s2N 1161298521519, s2N 3747275332498,
   s2N 3471292203132, s2P 921146919480, s2P 1062882564390, s2P 7038031851338,
   s2P 4820252517804, s2P 4358867885333, s2N 216255660407, s2N 3470890149404,
   s2N 1222569974109, s2P 2912828512262, s2P 1276407448869, s2P 25014790339, s2P 2093908473864,
   s2N 5866554704846, s2N 125031176973, s2N 6861950939441, s2N 2395928760702,
   s2N 3272118061744, s2N 8691861994070, s2N 982045174139, s2N 2699326604690,
   s2P 8899303663940, s2P 2346048280025, s2P 3804543005507, s2N 2322304892094,
   s2N 632190477628, s2N 3156955397713, s2N 3763211086480, s2N 1517074312144,
   s2P 5325067158449, s2P 4076314483426, s2P 1013592936006, s2P 6591350127957,
   s2N 4637062411580, s2P 4849053533649, s2N 2112307352897, s2N 2179338986108,
   s2P 1280662339897, s2N 2627909927663, s2P 8405044495878, s2P 761693080573, s2P 814868279238,
   s2P 3490820527933, s2P 7131273477739, s2P 3312251707821, s2N 7255001106548,
   s2N 4242046288425]
private def s2V5S6 : List ℤ :=
  [s2N 6708426862980, s2N 554375717384, s2N 5458552889880, s2P 2461863290977,
   s2P 5004424654084, s2N 1097380269128, s2P 8849310718085, s2P 2834171653579,
   s2P 18177799280732, s2N 3680371515496, s2P 14372994484619, s2P 10928906383501,
   s2P 4039655701690, s2P 2281222358922, s2N 5269598651941, s2P 7317755606049,
   s2N 3087126464742, s2P 1941446569862, s2N 3262745624075, s2P 10260666228672,
   s2P 2775813105744, s2P 337951323040, s2N 2423261631855, s2N 3943392485549,
   s2N 3261337143471, s2N 3183855812246, s2N 1453483360733, s2N 3987512880431,
   s2P 2854426815612, s2N 3682834637452, s2P 9014455436510, s2P 4299342133013,
   s2N 10993489018482, s2P 8331110224125, s2P 2624723652635, s2P 2048374642589,
   s2P 7066293492122, s2P 7718755000032, s2P 12784383356171, s2P 56612748371290,
   s2P 117874342269402, s2P 186775406776311, s2P 252893991583894, s2P 307383629505927,
   s2P 344276062309154, s2P 360968112292990, s2P 357999450380662, s2P 338320162828502,
   s2P 306308515667798, s2P 266795885731195, s2P 224279675965019, s2P 182428836439093,
   s2P 143852716828210, s2P 110134325514101, s2P 81940602528040, s2P 59296695656154,
   s2P 41744742621959, s2P 28598816970008, s2P 19072029162948, s2P 12374869410909,
   s2P 7813609262466, s2P 4804827687840, s2P 2875220869813, s2P 1672082701182]
private def s2V5S7 : List ℤ :=
  [s2P 946889747812, s2P 524388612773, s2P 283852087748, s2P 148749764117, s2P 74435490046,
   s2P 35266394498, s2P 15874484333, s2N 6906481647, s2P 2982151270, s2P 1308952113,
   s2P 588725552, s2P 268491523, s2P 121851716, s2P 54165220, s2P 23376485, s2P 9768608,
   s2P 3956241, s2P 1556981, s2P 597402, s2P 224125, s2P 82289, s2P 29490, s2P 10250, s2P 3429,
   s2P 1091, s2P 324, s2P 87, s2P 18, s2P 2, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0]
private def s2V5 : List ℤ :=
  s2V5S0 ++
    (s2V5S1 ++
    (s2V5S2 ++
    (s2V5S3 ++
    (s2V5S4 ++
    (s2V5S5 ++
    (s2V5S6 ++
    (s2V5S7 ++
    mm32k512krS2VecIn8)))))))
private def s2V6S0 : List ℤ :=
  [s2N 10192, s2N 23554, s2P 15387, s2P 23024, s2P 22770, s2N 37981, s2P 113578, s2P 23627,
   s2P 29019, s2P 12047, s2N 42894, s2N 167858, s2N 34679, s2P 196800, s2N 149517, s2N 343012,
   s2P 168521, s2N 768582, s2N 1357831, s2N 996960, s2P 574115, s2N 406654, s2P 844079,
   s2N 393617, s2P 214773, s2N 513619, s2N 3533595, s2N 7389803, s2N 947055, s2N 5761002,
   s2N 5474918, s2P 11857815, s2P 6821666, s2P 8787166, s2P 13779708, s2P 3629079, s2P 2158473,
   s2N 18905786, s2N 16416007, s2N 13601221, s2P 25822595, s2P 18554633, s2P 12326735,
   s2P 48710853, s2P 50172011, s2N 12108838, s2N 68853842, s2N 20375506, s2P 16860461,
   s2N 57730231, s2P 5504804, s2P 45771904, s2P 22348418, s2N 33404173, s2P 4740578,
   s2P 52435409, s2P 46279675, s2P 10978570, s2P 6497420, s2N 7767785, s2N 52004814,
   s2P 94902035, s2N 17441435, s2P 45764035]
private def s2V6S1 : List ℤ :=
  [s2N 4525608, s2P 58068707, s2P 115287965, s2P 55249908, s2P 88147108, s2P 132004976,
   s2N 43818056, s2P 60204795, s2N 43904736, s2P 53798461, s2P 135542813, s2N 5732,
   s2N 129938206, s2N 82530933, s2N 273403520, s2N 95696999, s2N 128122410, s2N 29708490,
   s2N 19080788, s2N 501824781, s2N 205224959, s2N 183400982, s2P 220387851, s2P 60951275,
   s2P 118613816, s2N 114015685, s2N 288623176, s2N 508111648, s2N 248613924, s2N 430273572,
   s2P 132455888, s2N 274735870, s2N 21500142, s2P 2460308, s2P 543657525, s2N 926236,
   s2N 397910937, s2P 166811902, s2P 2233292412, s2P 1013747586, s2P 878749639, s2N 875486546,
   s2N 468724189, s2P 1289911740, s2N 1697396685, s2N 1796100055, s2N 1785785583,
   s2N 732851912, s2N 1117336657, s2P 788308873, s2N 1106412643, s2N 1733654460, s2P 267773126,
   s2P 3165737056, s2P 3339963424, s2P 860609053, s2P 2391575517, s2P 507380736,
   s2N 2230949261, s2N 214149614, s2P 2801362853, s2N 1422013184, s2N 1920651494, s2N 832623566]
private def s2V6S2 : List ℤ :=
  [s2P 4607618734, s2N 1378107227, s2P 2499530181, s2P 21417283, s2N 1973208204,
   s2N 2700638700, s2N 2130030807, s2P 3272359181, s2N 3373381701, s2N 231499777,
   s2P 2394879821, s2P 7524745977, s2P 5171338646, s2P 6548222576, s2P 1390519398,
   s2P 5054351317, s2P 2589519532, s2P 9167001631, s2P 209000880, s2N 3243222711,
   s2P 8865943566, s2P 13998875721, s2N 4350393745, s2P 5432689232, s2P 2006590745,
   s2P 1381092495, s2P 16415940947, s2P 4516686137, s2P 7397876889, s2P 6812245155,
   s2P 1994042293, s2P 731033823, s2P 721103138, s2N 1469739128, s2N 10685049084,
   s2N 16213735632, s2N 19474683882, s2N 24451978102, s2N 6901416003, s2P 9086960026,
   s2P 4202046702, s2P 13178993975, s2P 9485423624, s2N 48322454303, s2N 35472494052,
   s2P 324275798, s2N 2056746172, s2N 2722280674, s2P 751586972, s2N 6847890246,
   s2N 57266287213, s2P 13252552194, s2P 5935960223, s2P 27307403437, s2P 755701743,
   s2P 15128888367, s2N 12456812636, s2P 26409739478, s2P 40108487189, s2N 28352234783,
   s2N 2510254987, s2P 10933871141, s2P 21214784224, s2N 25345605626]
private def s2V6S3 : List ℤ :=
  [s2N 28910736383, s2N 49755644223, s2N 14322863920, s2N 8496541826, s2N 8047728425,
   s2N 39403377049, s2P 6651275322, s2P 19580952274, s2P 34426190054, s2P 70332857413,
   s2N 23271780841, s2P 79129812384, s2P 31798886408, s2N 5901919015, s2P 10082806380,
   s2P 16631225636, s2N 6858434214, s2P 32163911783, s2N 13896911814, s2N 170747454581,
   s2N 83081601647, s2N 90358891662, s2N 90057126544, s2N 127906549972, s2N 179592632329,
   s2N 130446087535, s2P 5401480489, s2N 117266618979, s2N 130691678691, s2P 83713464498,
   s2P 203952881373, s2P 296188835160, s2P 22090386323, s2N 71870598137, s2N 108765955479,
   s2N 151247247805, s2P 48329490018, s2N 48849491038, s2P 39196108383, s2P 250921770816,
   s2N 249057871274, s2P 57216865880, s2N 36051616203, s2P 215078275051, s2N 253731693447,
   s2N 163513233951, s2P 241741377650, s2P 308203234908, s2N 215214475693, s2N 82967359187,
   s2N 52675662616, s2N 69616491292, s2P 122611490992, s2N 40660618672, s2N 80879378438,
   s2P 176278984601, s2P 235085978095, s2N 148345985302, s2P 118426669894, s2P 338452683078,
   s2P 340760972835, s2N 291289282075, s2P 491733223097, s2N 160538988190]
private def s2V6S4 : List ℤ :=
  [s2N 141634269024, s2N 239085363065, s2N 180228016634, s2N 43348074361, s2N 381036620260,
   s2P 129107528635, s2N 298361940992, s2P 304686025319, s2N 32394952393, s2N 103798010825,
   s2P 290509503379, s2P 317148414371, s2P 204509274237, s2P 150884399172, s2P 328141310280,
   s2P 78577663466, s2P 200360291750, s2N 201896437637, s2N 410681590066, s2N 590723279507,
   s2N 774307342962, s2P 844143313536, s2P 92926717553, s2N 484594124470, s2N 1376712815666,
   s2N 1481210259061, s2N 1518614569104, s2N 592793726222, s2N 128076551597, s2N 748495152102,
   s2N 775556369144, s2N 230180968407, s2P 2069664756037, s2P 1717293141861, s2P 795246193629,
   s2P 295253002713, s2P 363861338297, s2P 1634640702170, s2P 1335467151924, s2N 355912446253,
   s2N 1157225109935, s2N 3036478257041, s2N 1319452644764, s2P 470541700151, s2N 751151170712,
   s2P 1006561893919, s2N 1085809386052, s2N 848888021382, s2P 864074028474, s2P 1642943244556,
   s2P 1326821146860, s2N 2302074611170, s2N 1481098665719, s2P 2498904468264,
   s2N 665190401953, s2P 7869316090346, s2P 4138774895133, s2P 3486057289362,
   s2P 1261439188044, s2P 3126643286507, s2P 950783951169, s2N 1805207145157,
   s2P 1966514183677, s2P 3376542712406]
private def s2V6S5 : List ℤ :=
  [s2P 604714898183, s2N 6777628215527, s2P 1361121495138, s2P 14473606658149,
   s2N 1031252148260, s2N 5251108601419, s2P 5397540790579, s2N 2351868780870,
   s2P 5220582265688, s2P 799217907365, s2N 3908811586941, s2N 7963805530719,
   s2N 6560045690336, s2P 5536801317889, s2N 884447745057, s2N 2671606584284,
   s2N 1617186961936, s2N 676168242480, s2P 2083513636405, s2N 2193058502038,
   s2N 6049621143493, s2N 5010640514392, s2N 296073156131, s2N 5760635861391,
   s2P 3625454920902, s2N 4448244273089, s2N 4667231883204, s2P 5017950965961,
   s2N 1176870923976, s2N 998648569013, s2P 6318315191604, s2N 1065228002703,
   s2N 1875083088688, s2P 121644370580, s2P 663095192551, s2P 6478217020555, s2P 4918047143398,
   s2P 1479285355161, s2N 685402726129, s2P 4333186878562, s2P 5538718323420,
   s2P 5716343274235, s2N 147503109974, s2N 6910938595289, s2P 1649893308991,
   s2N 2521063638041, s2N 8420021282092, s2N 3141056856656, s2N 6356243649627,
   s2N 4811789339595, s2P 3805962793150, s2P 3253484396462, s2N 626582690508,
   s2N 2910312278165, s2P 2907335191957, s2N 5143475439464, s2N 2902323323108,
   s2N 4569779616064, s2N 1465991319634, s2N 2313704629228, s2P 6472373604308,
   s2P 4658598518134, s2N 2453189723391, s2P 925631990107]
private def s2V6S6 : List ℤ :=
  [s2N 1761457871983, s2N 10689939712820, s2N 3759966187369, s2P 5327021521242,
   s2N 6313490310202, s2P 12061728856888, s2P 8308686766362, s2P 10460134828801,
   s2P 607452326460, s2P 813103425717, s2P 2312480013924, s2N 14721961513395,
   s2N 1541319813911, s2P 5184795629196, s2N 8566262360638, s2P 5701661610063,
   s2P 13119820060774, s2P 7405609246450, s2N 3527644939232, s2N 374021771208,
   s2N 7262423242389, s2P 2456470578766, s2N 3461503641203, s2N 2524438965414,
   s2N 7679427077328, s2P 10289686391899, s2N 2144174229480, s2N 5124394708639,
   s2P 4499045779258, s2N 4149205459619, s2N 6946495965789, s2N 2487482670776,
   s2N 947107332221, s2N 6139757629461, s2P 3231116337501, s2N 8711162952532,
   s2P 4325480628947, s2P 6307597152004, s2P 6629895705255, s2P 8125864065513,
   s2P 5441687090558, s2P 3714031123923, s2P 1403833039500, s2P 5628223504905,
   s2P 2269158336139, s2P 11389012521329, s2P 4697545858371, s2P 26722658814910,
   s2P 81279393828251, s2P 150382794292981, s2P 222573686422646, s2P 286822994065022,
   s2P 334752756845194, s2P 361698931509196, s2P 366827934263556, s2P 352471452313338,
   s2P 323010589870306, s2P 283717914772534, s2P 239759622277730, s2P 195493126900582,
   s2P 154135121431706, s2P 117709952993522, s2P 87181270833501, s2P 62668519179778]
private def s2V6S7 : List ℤ :=
  [s2P 43757493639704, s2P 29674901881247, s2P 19572483644155, s2P 12540636973610,
   s2P 7808820707808, s2P 4734089734989, s2P 2787529712284, s2P 1593402854917,
   s2P 890457161247, s2P 487527711848, s2P 257439631670, s2P 127880279503, s2P 58833956050,
   s2P 25196234993, s2P 10327490733, s2P 4231436462, s2P 1800279957, s2P 802108503,
   s2P 366550451, s2P 167074546, s2P 74508432, s2P 32222006, s2P 13479299, s2P 5455244,
   s2P 2140885, s2P 811626, s2P 302281, s2P 109070, s2P 35977, s2P 10509, s2P 2834, s2P 781,
   s2P 230, s2P 67, s2N 16, s2P 1, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V6 : List ℤ :=
  s2V6S0 ++
    (s2V6S1 ++
    (s2V6S2 ++
    (s2V6S3 ++
    (s2V6S4 ++
    (s2V6S5 ++
    (s2V6S6 ++
    (s2V6S7 ++
    mm32k512krS2VecIn8)))))))
private def s2V7S0 : List ℤ :=
  [s2P 8468, s2N 19643, s2N 21717, s2P 15682, s2P 15050, s2P 58898, s2P 97754, s2P 24444,
   s2P 22566, s2N 24936, s2P 3743, s2P 107900, s2N 394125, s2P 140564, s2N 202475, s2N 103085,
   s2N 140074, s2P 35507, s2P 579255, s2P 466404, s2P 1333974, s2P 1423882, s2P 110936,
   s2N 1279062, s2P 71317, s2N 2503334, s2N 4389527, s2P 3161332, s2N 2905259, s2P 2655422,
   s2P 910943, s2N 16513752, s2P 1855767, s2N 1364897, s2N 4366167, s2N 11496100, s2N 16591601,
   s2N 8678762, s2P 5818092, s2P 14072705, s2P 13473637, s2N 4574167, s2N 26898460,
   s2N 38989377, s2N 38511469, s2N 22893429, s2P 15255298, s2P 56893384, s2P 4786478,
   s2N 15497947, s2P 84593340, s2N 9460925, s2P 35488629, s2P 22978753, s2P 12236396,
   s2N 41754359, s2P 78387108, s2P 14871535, s2P 20911882, s2P 9518228, s2N 50627978,
   s2P 9799822, s2N 74890476, s2N 73641028]
private def s2V7S1 : List ℤ :=
  [s2N 53182050, s2N 37791079, s2N 44933161, s2N 28548083, s2N 72640252, s2N 66846807,
   s2P 166140096, s2P 85517055, s2P 2864225, s2P 165622412, s2P 260103682, s2N 113999563,
   s2N 14214853, s2N 8424245, s2N 108450549, s2N 6568260, s2P 100637460, s2N 141923285,
   s2N 290403299, s2P 130005273, s2P 139273092, s2N 88511322, s2P 29946796, s2N 351743768,
   s2N 8699616, s2N 235230535, s2N 221193680, s2N 279501589, s2N 208861681, s2N 973140950,
   s2N 74901444, s2P 389926199, s2N 867267136, s2N 122495816, s2P 641051739, s2P 807377598,
   s2N 39958763, s2P 1395106368, s2P 1417714376, s2P 231610868, s2P 106812761, s2P 772795455,
   s2N 289533719, s2P 298768998, s2P 1198488413, s2P 425828051, s2P 57288413, s2P 1681657575,
   s2P 1371322465, s2N 549633149, s2N 2313679098, s2N 170335611, s2P 928086929, s2P 316381557,
   s2P 864616608, s2P 1456803448, s2P 3700097410, s2P 3217009635, s2P 307880491, s2P 615175360,
   s2P 1271121600, s2N 1646718707, s2N 4891715243, s2N 1094605664]
private def s2V7S2 : List ℤ :=
  [s2P 662308592, s2N 5323098887, s2P 1256908091, s2P 1184374567, s2P 1925916238,
   s2P 3261459438, s2P 2601954394, s2P 3789253583, s2P 965186846, s2P 195443477, s2N 440203634,
   s2N 5185730358, s2N 2642834584, s2N 2211014828, s2N 4760682758, s2N 6782642090,
   s2N 5234553280, s2N 6567712620, s2P 971081223, s2P 1528314181, s2N 4856840676,
   s2N 1511959148, s2P 6567331769, s2P 2509189011, s2P 4586953738, s2P 11531856179,
   s2P 13020596464, s2P 846074232, s2P 4872272978, s2N 9603120387, s2N 6620121434,
   s2N 15365923381, s2P 9066428328, s2P 9324594351, s2P 3757315741, s2N 716616811,
   s2P 3821413702, s2P 8411301983, s2P 2572115750, s2P 3096442512, s2N 2087962830,
   s2N 4865532873, s2N 13115958142, s2N 12586419311, s2N 948530135, s2N 13372323530,
   s2N 29508250745, s2N 15661349848, s2P 1478494458, s2P 27515305245, s2P 47770204513,
   s2P 44844953076, s2P 26247179957, s2P 11898300691, s2P 17469180624, s2N 26636913828,
   s2N 19221536190, s2N 26640510085, s2N 3651495720, s2N 18203591928, s2N 19668090115,
   s2N 46481530767, s2N 35008474495, s2N 16630362841]
private def s2V7S3 : List ℤ :=
  [s2N 28414442893, s2N 17101545424, s2P 10336586062, s2P 14127348978, s2N 47481105396,
   s2N 40520758531, s2N 13627360853, s2N 31583493879, s2N 2297854826, s2N 18917136281,
   s2N 80914736049, s2N 16049007883, s2P 20509693844, s2P 31681994356, s2P 33399295940,
   s2N 34368139882, s2P 9695996167, s2P 44705290474, s2N 25215304911, s2P 22703026111,
   s2P 57438387756, s2P 62018767371, s2P 44092730222, s2N 21204932905, s2N 88656165565,
   s2N 2742421033, s2N 72960514062, s2N 63433721563, s2N 111363738368, s2N 73289321121,
   s2P 68472769720, s2P 128739417592, s2P 146860144091, s2N 82963650151, s2N 326689367807,
   s2N 202230871341, s2P 20350745570, s2P 171240010969, s2P 166082162205, s2P 91561267628,
   s2P 173331677192, s2N 26967292722, s2N 199384330500, s2N 410813864712, s2N 174704519491,
   s2N 214492377393, s2P 56031108737, s2N 121055601514, s2P 183709438095, s2N 268823043349,
   s2P 97615476832, s2P 226849844091, s2P 66510687180, s2N 219478034368, s2P 88797314686,
   s2P 94899347177, s2P 109990880251, s2P 258302726648, s2P 49152959176, s2N 160639309559,
   s2N 137899761228, s2P 258031031268, s2P 438778072766, s2P 330946596555]
private def s2V7S4 : List ℤ :=
  [s2N 301548436413, s2N 289681991848, s2N 353252703176, s2N 345165080190, s2P 204669897602,
   s2P 228010085410, s2N 32178643427, s2N 184847474770, s2P 39715241934, s2P 202070558307,
   s2N 72239502185, s2N 192299564018, s2N 327858364093, s2P 186803269260, s2P 266411057213,
   s2P 279248935366, s2P 210743294655, s2P 310504768447, s2P 151683132851, s2P 303144827307,
   s2P 410098047279, s2P 514077921809, s2P 667041382907, s2P 511775523730, s2P 31030235355,
   s2P 27210045642, s2P 360056735446, s2P 865076148583, s2P 107378784775, s2N 858975216555,
   s2N 313669507059, s2N 472478758578, s2N 1196242659178, s2N 940806520291, s2N 1568033833287,
   s2N 463187111282, s2N 1832604235491, s2N 1924182167843, s2N 511004730586, s2P 2166023814455,
   s2P 802609501703, s2N 1184607339926, s2P 1154776431660, s2N 273228883579, s2N 1497326000831,
   s2N 137447485208, s2N 341824869731, s2N 931003992922, s2P 1151978624252, s2P 2025644087053,
   s2N 675081612710, s2P 720904588032, s2N 283273718887, s2N 4285835644356, s2N 3358813061114,
   s2N 508588756621, s2N 5313599317742, s2N 2980147023702, s2N 4275060436773,
   s2N 3775031250613, s2N 1183769191811, s2N 2599108164153, s2N 2143565205191,
   s2P 3330664976309]
private def s2V7S5 : List ℤ :=
  [s2P 1017428129241, s2P 1117273203359, s2N 2596024491934, s2N 5350345984896,
   s2N 6031500098733, s2N 3966513944371, s2N 7684103584070, s2N 8711521376695,
   s2N 7475087306914, s2N 11576131713591, s2N 767534891862, s2P 2158950787691,
   s2P 395941743499, s2P 1370979386253, s2P 8521496875282, s2N 1309761591979,
   s2N 1731342333424, s2P 907514415935, s2N 898943037023, s2N 7781471242932, s2P 1593912376868,
   s2P 5579039105374, s2N 3115477623607, s2N 1473499186400, s2N 4611159542763,
   s2N 5567175044654, s2N 2358362254871, s2N 4146189845209, s2N 3520233694293,
   s2N 2046396597886, s2N 5050149324545, s2N 1831844097501, s2N 6708917906528,
   s2P 1149589501762, s2P 2354125554478, s2N 54453690431, s2N 1678378684686, s2P 909821989805,
   s2N 682651098156, s2P 2423867046000, s2P 251587196619, s2N 5358122525379, s2P 3721072736261,
   s2P 1360319100656, s2N 290237119960, s2N 4544226304516, s2N 2632530832583,
   s2N 5471317449307, s2N 6210607433171, s2N 5696342651559, s2N 5171541775325,
   s2N 3839215000532, s2N 1511996584916, s2N 1195267553327, s2P 591114452519,
   s2N 6043932484232, s2N 9316775317681, s2N 5359671472491, s2N 3654487213499,
   s2P 6479656338506, s2P 7313910002835, s2P 2327912965992, s2P 3476893095859,
   s2N 2068446026378]
private def s2V7S6 : List ℤ :=
  [s2N 7454450652402, s2N 9136790808732, s2P 3091732375813, s2P 13631807068801,
   s2N 1734312420251, s2P 9173796418438, s2P 1229113046634, s2P 75306162143, s2P 1726386114991,
   s2N 3185617136965, s2P 2646887325073, s2P 9691751200956, s2P 2188356604495,
   s2N 1245512131938, s2P 8150279181981, s2P 11400715917434, s2P 7164540808957,
   s2P 10542398285466, s2P 149773175512, s2N 10558007277466, s2N 1874843155237,
   s2N 8566016906785, s2P 2246793204943, s2P 7011480781548, s2P 10327530867729,
   s2P 8206331242934, s2P 455491560612, s2N 519913738783, s2P 7665965787659, s2N 7547516792207,
   s2P 1316061048277, s2N 2756190737512, s2N 570923737367, s2P 4731095652419,
   s2N 7966064845628, s2P 5904130873908, s2P 1897009933007, s2P 7397030533741,
   s2N 3907774827443, s2N 3464489965641, s2N 6958371233907, s2P 3104076177629,
   s2N 1382514760312, s2N 3189076798879, s2N 10537003462942, s2P 2938123786787,
   s2P 5849031568802, s2P 2706202306043, s2P 4269567235529, s2P 884299893119,
   s2P 5888110439958, s2P 12422111943922, s2N 5883946407705, s2P 6904587932990,
   s2P 6517566018505, s2P 20080072552930, s2P 73353487720050, s2P 144426241084736,
   s2P 220446817289851, s2P 288737200172803, s2P 339656963028406, s2P 367867221169014,
   s2P 372473738778222, s2P 356200198357953]
private def s2V7S7 : List ℤ :=
  [s2P 324021302016562, s2P 281846757285990, s2P 235362399867519, s2P 189241230955357,
   s2P 146831957633948, s2P 110133345282849, s2P 79956862567627, s2P 56235313413767,
   s2P 38345213132266, s2P 25364684695697, s2P 16279839858266, s2P 10138065880572,
   s2P 6128057314583, s2P 3599581190969, s2P 2056664589649, s2P 1142052059398,
   s2P 614128287174, s2P 318038524950, s2P 157761989381, s2N 74728342371, s2P 33824565057,
   s2P 14704366761, s2P 6195582073, s2P 2559719608, s2P 1048836632, s2P 429495364,
   s2P 176070853, s2P 71976271, s2P 29126685, s2P 11597758, s2P 4487269, s2P 1718529,
   s2P 630132, s2P 205230, s2P 58146, s2P 15370, s2P 4287, s2P 1317, s2N 407, s2P 113, s2P 26,
   s2P 4, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V7 : List ℤ :=
  s2V7S0 ++
    (s2V7S1 ++
    (s2V7S2 ++
    (s2V7S3 ++
    (s2V7S4 ++
    (s2V7S5 ++
    (s2V7S6 ++
    (s2V7S7 ++
    mm32k512krS2VecIn8)))))))
private def s2V8S0 : List ℤ :=
  [s2P 9348, s2P 17515, s2N 22310, s2N 20632, s2N 30431, s2N 69071, s2N 47088, s2N 31837,
   s2P 48748, s2P 24858, s2P 320, s2P 129548, s2P 367658, s2P 177697, s2N 138364, s2N 105504,
   s2N 193628, s2N 173389, s2N 3171, s2N 656173, s2P 854756, s2P 1779562, s2P 1077604,
   s2P 1042120, s2P 1118479, s2P 5743841, s2P 2829633, s2P 491401, s2N 6354168, s2P 868683,
   s2N 4187000, s2N 7563960, s2N 1969724, s2N 9534470, s2N 8510020, s2N 2480878, s2N 2767299,
   s2N 1029781, s2P 2165269, s2P 1334605, s2N 13145548, s2P 4197373, s2P 28473600,
   s2P 19218984, s2P 37299027, s2P 2447936, s2P 1469627, s2N 14889044, s2N 63261098,
   s2N 69066962, s2N 37918311, s2N 48947519, s2N 29316133, s2N 39249520, s2N 59083408,
   s2N 23022924, s2P 59286208, s2P 19015132, s2N 29417226, s2P 30622903, s2P 32358862,
   s2N 44921852, s2N 17613995, s2P 37384956]
private def s2V8S1 : List ℤ :=
  [s2P 5298026, s2P 34164940, s2N 39249660, s2N 157735072, s2N 81000886, s2N 123963751,
   s2N 81400840, s2N 60736990, s2P 53726272, s2P 105922267, s2P 139822644, s2N 139002588,
   s2N 266474231, s2N 61698917, s2N 63124752, s2N 201163825, s2P 126326898, s2P 129169021,
   s2P 212230434, s2P 197135365, s2P 233068877, s2P 174579864, s2N 24730402, s2P 80432154,
   s2P 287007877, s2P 13634459, s2N 221816013, s2P 265763089, s2P 326540770, s2P 246058489,
   s2N 147871292, s2P 147529259, s2P 708121879, s2P 630127123, s2N 86498017, s2P 1199068622,
   s2P 933492471, s2P 808326443, s2P 688214940, s2P 347587187, s2P 510320916, s2P 77377604,
   s2P 146849476, s2N 366338123, s2N 130353190, s2N 365531078, s2N 823810478, s2N 330547531,
   s2P 338181563, s2P 1449841862, s2P 1864068073, s2P 425297974, s2N 1379322690,
   s2N 1050601908, s2P 2278632536, s2P 2555716702, s2P 3455684172, s2N 236858658,
   s2N 1469937277, s2P 1563694, s2P 3442821357, s2N 2912274503, s2N 3209196483, s2P 2097788686]
private def s2V8S2 : List ℤ :=
  [s2N 1421313124, s2N 3025511811, s2N 1461021150, s2P 2588587966, s2N 391613144,
   s2N 1486575246, s2N 1806823625, s2N 845641905, s2P 4594021893, s2P 1795918166,
   s2P 5801131947, s2N 1001237902, s2P 817115971, s2P 149460423, s2P 266303280, s2N 2942905574,
   s2N 4554011231, s2N 1349054296, s2N 1124435695, s2P 39828994, s2P 7771336973,
   s2N 2095080315, s2N 3230033077, s2N 3919056038, s2P 278992238, s2N 4304801256,
   s2N 7396660912, s2N 13795026716, s2N 2640508612, s2P 9951007112, s2N 4233969260,
   s2P 2663105937, s2P 11160550965, s2N 7390646094, s2N 5461749327, s2N 10489760444,
   s2P 140492202, s2P 2328392940, s2P 5572692369, s2N 14970127288, s2N 9011443042,
   s2P 2708678631, s2P 13054553018, s2P 10107011016, s2P 11452424420, s2N 6307499107,
   s2P 2463474818, s2P 5197048925, s2P 11563822102, s2N 5268215894, s2P 3514831095,
   s2N 13751768032, s2P 5874382592, s2P 9461145844, s2N 7370139081, s2N 4705388117,
   s2P 1164407686, s2P 39024223774, s2P 32151364140, s2N 1931287996, s2N 47788252417,
   s2N 7057119716, s2N 28500521549, s2P 48222736256]
private def s2V8S3 : List ℤ :=
  [s2P 29246220180, s2N 13939514752, s2N 40816578374, s2N 3486803914, s2P 25983923085,
   s2P 12197686909, s2N 39014606938, s2N 11890683113, s2P 13891746133, s2N 53662485223,
   s2N 118641693746, s2N 13956208791, s2P 4464575722, s2P 16090752058, s2N 18727412930,
   s2N 16939885679, s2N 8839678105, s2N 45123168390, s2N 35012575563, s2N 55825456909,
   s2P 4257267513, s2N 21162628611, s2N 18951443472, s2N 20559606378, s2P 8724415864,
   s2N 1878075525, s2N 60877253514, s2P 1626771557, s2N 14517974987, s2N 55172620696,
   s2P 17348115399, s2P 4658391411, s2N 95980318853, s2N 29405118209, s2P 5343722657,
   s2P 21561119403, s2P 170733065320, s2P 256009618472, s2P 113840719499, s2P 86212530498,
   s2N 291526268235, s2N 285915908758, s2N 247288589144, s2N 23175199744, s2N 41594542439,
   s2P 171472811740, s2P 24948988376, s2N 96442752190, s2P 386370267375, s2P 224617485284,
   s2N 233709569560, s2P 63153653991, s2P 108828960027, s2N 93719909603, s2P 303422981447,
   s2N 94286115390, s2N 351898411630, s2N 107498486256, s2N 27177657251, s2N 179625011774,
   s2N 119208037716, s2P 37140726665, s2N 139088006844, s2N 177920256135]
private def s2V8S4 : List ℤ :=
  [s2N 238634434815, s2N 2948610186, s2P 125001283179, s2P 286958769479, s2P 243228749846,
   s2N 246549516471, s2N 301174708429, s2N 119657856778, s2P 181460181083, s2P 499919842599,
   s2P 511319202915, s2N 129255368063, s2P 139593822544, s2P 238587973987, s2P 203673848222,
   s2P 81976825372, s2P 37716088095, s2P 26162683729, s2P 15078559261, s2P 259030142127,
   s2P 502742259288, s2P 758777253279, s2P 330694469276, s2P 327290789429, s2P 287767865799,
   s2P 348328303790, s2P 490722948796, s2P 720506371675, s2P 333010944341, s2N 66077570066,
   s2N 353667891600, s2N 15314973047, s2N 52201895507, s2N 729789175478, s2N 1410685257959,
   s2N 1222061551275, s2N 808045551498, s2N 810038735905, s2N 232488654155, s2N 622844817392,
   s2N 1295532496512, s2P 484005482194, s2P 2296041613998, s2P 2453767107521,
   s2P 1583481451162, s2P 356138695059, s2P 1847728060162, s2N 275000500452, s2N 1824946608566,
   s2P 581679429849, s2P 2629297775088, s2P 1068967886984, s2P 1414831597687,
   s2P 1550586405121, s2N 1008954010986, s2P 1663986588237, s2P 3366569704249, s2N 94998561262,
   s2P 1147525428600, s2N 290753450601, s2N 1540526817365, s2P 679056257258, s2N 817093332665,
   s2N 3797812116163]
private def s2V8S5 : List ℤ :=
  [s2N 2766918187935, s2N 551218149528, s2P 5702310591638, s2P 3303945887459,
   s2P 1252075368634, s2N 7875551481211, s2P 1618884795547, s2P 3666044741716,
   s2P 580808449802, s2N 753177711733, s2P 5582607766105, s2N 2220246965249, s2P 6569920209805,
   s2P 1547951070603, s2N 1549430796453, s2N 7018623857428, s2P 2073529252258,
   s2N 4025759914117, s2N 12790783295768, s2N 8861809481016, s2N 8726418551111,
   s2N 5803230008130, s2N 2468441744636, s2P 2266671591859, s2N 1472891498688,
   s2P 2712513800900, s2P 7769606762839, s2P 2130781149639, s2N 1937746055958,
   s2N 2022736840967, s2N 663011055619, s2N 4071258815018, s2P 1457902336981,
   s2P 5858095732576, s2N 602232741158, s2N 4036698705539, s2P 1722567575311, s2N 650766209321,
   s2N 6252962871119, s2N 5363405046285, s2N 3214291187190, s2N 2909729994217,
   s2P 1449575979661, s2P 3760036251025, s2P 2046307206507, s2P 408753335649,
   s2N 2638762422659, s2N 593555429480, s2P 756056257887, s2P 2220983130497, s2N 982083177606,
   s2N 1689596685504, s2N 4763795133610, s2P 1832210375329, s2N 1209434120460,
   s2N 1127446963631, s2P 1411008543321, s2N 4385487510455, s2N 7419160586597,
   s2N 8777797356763, s2N 3439725218720, s2P 1412242381673, s2P 3985740609905,
   s2N 2393017658653]
private def s2V8S6 : List ℤ :=
  [s2N 6284937825145, s2N 7656929414717, s2N 5672244905588, s2N 1160609591487,
   s2N 11712038332342, s2N 9181789795856, s2N 3967077142218, s2N 10623164847994,
   s2N 12491362792102, s2P 2685920148655, s2P 10938600061734, s2P 867956696505,
   s2N 1251818196848, s2P 7910659307108, s2P 2282430561751, s2N 779192028089,
   s2P 3267801701117, s2P 5641635938162, s2N 9584369071810, s2N 6335568750936,
   s2P 12179087629327, s2P 9427139711465, s2N 5216729185380, s2N 4947271179003,
   s2P 12104175095536, s2P 4898941885707, s2N 2263698187276, s2P 700474128547,
   s2N 8981797070600, s2N 6866470812840, s2P 1385882476308, s2P 3236372902653,
   s2P 1185887447109, s2P 10707023104453, s2P 5413544356362, s2P 6674137670069,
   s2P 395109514365, s2N 5837604068732, s2N 1784368080882, s2P 5608670989349,
   s2N 4576107435912, s2N 6754396973088, s2N 6664291211024, s2P 2577647646424,
   s2N 1413864322839, s2N 9103263406472, s2N 6210945012728, s2P 3755484906877,
   s2N 10994523586410, s2P 1696571135150, s2P 469027745836, s2N 4242717409037,
   s2P 2943274094278, s2N 1703046952537, s2N 65941162014, s2P 10691659100854,
   s2P 9255543172883, s2N 4525669673972, s2N 1216816978606, s2P 6948638513449,
   s2P 825906815349, s2P 9727904323984, s2P 2748239681263, s2P 33692152066023]
private def s2V8S7 : List ℤ :=
  [s2P 96982765724995, s2P 175247101445404, s2P 253633386123789, s2P 318896428500952,
   s2P 362096597270822, s2P 379561756073870, s2P 372413208567465, s2P 345214717147264,
   s2P 304327061042659, s2P 256370196228637, s2P 207140540826938, s2P 160914537165755,
   s2P 120516159454916, s2P 87015368439438, s2P 60848229128938, s2P 41016940236071,
   s2P 26818426881268, s2P 17020005768002, s2P 10381921790208, s2P 6143388746085,
   s2P 3587043748586, s2P 2034361559677, s2P 1075238959616, s2P 515720933863, s2P 226584054537,
   s2P 95343250184, s2P 40755057316, s2P 18262785433, s2P 8430141780, s2P 3857618667,
   s2P 1704060136, s2P 720671702, s2P 292693543, s2P 114987120, s2P 43999729, s2P 16467829,
   s2P 6026643, s2P 2145613, s2P 737320, s2P 242445, s2P 75571, s2N 22113, s2P 6026, s2P 1523,
   s2P 354, s2P 74, s2P 11, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V8 : List ℤ :=
  s2V8S0 ++
    (s2V8S1 ++
    (s2V8S2 ++
    (s2V8S3 ++
    (s2V8S4 ++
    (s2V8S5 ++
    (s2V8S6 ++
    (s2V8S7 ++
    mm32k512krS2VecIn8)))))))
private def s2V9S0 : List ℤ :=
  [s2P 1955, s2P 20393, s2P 15036, s2N 3855, s2N 8192, s2N 41986, s2P 32371, s2N 71700,
   s2N 33605, s2P 51845, s2N 7341, s2P 14528, s2N 10837, s2N 128822, s2N 316304, s2N 333744,
   s2N 532819, s2N 372257, s2P 283643, s2N 425497, s2P 709982, s2P 1661465, s2P 404585,
   s2P 766932, s2N 3424689, s2N 524209, s2N 3426097, s2P 243076, s2N 2632192, s2N 2751937,
   s2N 3310421, s2P 2650226, s2P 3872067, s2P 6309282, s2N 679053, s2N 200050, s2N 297525,
   s2P 3551992, s2P 15352779, s2P 7590896, s2P 11811710, s2P 20419157, s2P 3322030,
   s2N 6022646, s2P 20479139, s2P 13058683, s2P 16637082, s2N 8187907, s2N 32321902,
   s2N 1522772, s2P 45247669, s2N 28979079, s2N 14803161, s2P 4065357, s2N 7364241,
   s2P 51217567, s2N 44411361, s2N 87695521, s2N 47465517, s2N 52256274, s2P 18902743,
   s2N 41807950, s2N 7916977, s2P 23606186]
private def s2V9S1 : List ℤ :=
  [s2P 61304414, s2P 93338711, s2P 31274254, s2P 8919061, s2P 72275747, s2P 41043355,
   s2N 52728707, s2P 55999073, s2N 29175922, s2P 79053595, s2P 64000730, s2N 141142163,
   s2N 30461669, s2N 46870535, s2N 18580611, s2N 73464411, s2N 57060649, s2N 306831539,
   s2N 255474917, s2N 77575668, s2N 131013926, s2P 87646637, s2P 259441283, s2N 25796185,
   s2N 25762212, s2N 87303445, s2P 100150976, s2P 271462682, s2P 16721007, s2N 84402442,
   s2P 466636482, s2P 221091723, s2P 119085586, s2P 27807496, s2P 201905507, s2P 132557757,
   s2P 475928655, s2P 268699237, s2P 161432882, s2N 220645500, s2P 527718751, s2P 246918028,
   s2P 726998657, s2P 532392404, s2N 313044248, s2N 511548409, s2P 74021041, s2P 191882578,
   s2P 796399643, s2N 1079400004, s2P 49220440, s2P 1690199752, s2P 389230767, s2N 996247104,
   s2N 9577982, s2N 378489066, s2N 2583092629, s2N 2152921436, s2P 611728079, s2N 543932456,
   s2P 2916229330, s2P 790176997, s2P 954797815, s2N 1605409068]
private def s2V9S2 : List ℤ :=
  [s2N 761152420, s2N 18164880, s2P 698695864, s2P 1170952842, s2P 2281815391, s2P 7318065356,
   s2P 432278081, s2N 1243042926, s2P 2364760556, s2N 3049191664, s2N 269591754,
   s2N 3364160395, s2N 4264878830, s2N 1125570128, s2N 113216340, s2N 1138670932,
   s2P 175313688, s2P 354318636, s2P 1263351659, s2N 4510946201, s2N 766511722, s2N 2670656239,
   s2P 3944581310, s2N 2098368547, s2N 5727673209, s2N 687552916, s2N 479865065, s2N 806410697,
   s2P 1868333960, s2P 7212753619, s2N 5822612933, s2N 6927730488, s2N 3074368487,
   s2P 5055010631, s2N 1626200564, s2P 8195508618, s2P 16917647643, s2P 13432700275,
   s2P 6554585724, s2N 1698628194, s2N 8681909374, s2N 18423347959, s2N 8416596805,
   s2N 5693093030, s2N 7969746193, s2N 9506116600, s2N 6062392252, s2N 7632841126,
   s2P 178688220, s2P 143318450, s2N 12488396962, s2N 22612229221, s2N 12151020769,
   s2N 11442681649, s2N 7620239438, s2N 9415820427, s2N 7721651075, s2N 19269565085,
   s2N 7292826447, s2P 22360399047, s2N 14712732319, s2N 8822789991, s2N 22937392482,
   s2P 5206562991]
private def s2V9S3 : List ℤ :=
  [s2P 11252897753, s2P 6489834683, s2N 40546595142, s2N 55541180424, s2N 64985638393,
   s2N 38483329518, s2N 13745852162, s2N 12331815731, s2P 30971188963, s2P 6329110490,
   s2N 13890536928, s2N 37959964913, s2N 14823243910, s2P 24833177337, s2N 25944297039,
   s2P 41729572482, s2P 1561155035, s2N 69474946039, s2N 37996757545, s2N 12451262222,
   s2N 25564097199, s2P 64658512274, s2N 3017789859, s2N 2682844778, s2N 59395777322,
   s2N 34716688631, s2P 63107850060, s2P 21923857676, s2N 17248617939, s2P 16463388307,
   s2P 49573307784, s2N 7664644377, s2N 151517457879, s2N 41602637408, s2N 108190837977,
   s2P 43264676347, s2N 53517368114, s2P 79436725478, s2P 59038640455, s2N 89695045433,
   s2N 40149188880, s2P 119095185869, s2P 7191038503, s2N 220027959053, s2N 77908458873,
   s2N 145364330271, s2N 192014416076, s2N 152044917081, s2P 91571278427, s2P 140642032705,
   s2P 40316287430, s2N 134499865998, s2N 178100115458, s2N 138899640939, s2N 307385096683,
   s2N 373949856199, s2P 150819031116, s2P 356476679205, s2P 386535477171, s2P 210419172481,
   s2N 72066670382, s2N 151244045817, s2P 110011086782, s2N 100904070351]
private def s2V9S4 : List ℤ :=
  [s2N 158480177115, s2P 87908632314, s2P 97166570345, s2N 67891245855, s2P 179069064475,
   s2N 117127905406, s2N 180732964298, s2N 136166142221, s2N 20120519287, s2N 89739588239,
   s2P 64715305751, s2P 161046504970, s2N 211582593270, s2N 282194556030, s2N 63900483360,
   s2P 95264858176, s2P 651423313109, s2P 262184296339, s2N 111885996195, s2N 301496235454,
   s2P 254386632734, s2P 96729789061, s2P 47272583910, s2P 73465641773, s2P 495004335701,
   s2P 59040257021, s2P 254955098093, s2N 119430325004, s2P 79318065272, s2N 34364832324,
   s2N 49739157912, s2N 27894805282, s2P 164842177036, s2P 477699059910, s2P 839244731286,
   s2P 337046971268, s2P 674121414832, s2P 96744315290, s2N 439562237586, s2N 447934811409,
   s2N 632621945195, s2N 947533262814, s2N 434037004250, s2P 680923014505, s2P 504277155268,
   s2P 647581487385, s2N 349747583019, s2N 634785495988, s2N 378773288862, s2N 411097569330,
   s2N 342625423030, s2N 947619189382, s2N 300742716695, s2P 1822256439694, s2P 3011689058274,
   s2P 2846092649112, s2P 1281540982780, s2P 431111500806, s2P 1080162066247,
   s2P 3334922141339, s2P 1118789123232, s2P 2192869827355, s2P 823846611492, s2N 78119060807]
private def s2V9S5 : List ℤ :=
  [s2N 1672117222543, s2N 3850554907462, s2N 3672538108991, s2N 42513462010, s2P 153654581358,
   s2N 3317833534350, s2N 1511979621926, s2P 1036791907328, s2N 1961229499385,
   s2N 586090483536, s2P 48631681903, s2N 3785285278516, s2N 3887115877180, s2N 1990270976163,
   s2N 1338561023930, s2P 6774698467732, s2P 9313213749760, s2P 4502756552952,
   s2P 2347262815283, s2N 2259270702911, s2P 3226538438201, s2P 827021293067,
   s2N 5899413834049, s2P 5925331003208, s2P 5228465349734, s2N 3606729547651,
   s2N 568271828965, s2N 895609000597, s2P 801206213681, s2P 2395509932705, s2P 4507020514205,
   s2P 11274800286528, s2P 3654793148781, s2P 9573287890132, s2P 11448110457248,
   s2P 5886408265194, s2P 5943046242678, s2P 932782399790, s2P 2076487287417,
   s2P 1200137489354, s2P 4224949169202, s2P 1350716145058, s2P 480110963875,
   s2N 1227638061196, s2P 330193370701, s2P 241649625183, s2N 2105627066316, s2N 3945331291384,
   s2N 553166812091, s2N 1009711117642, s2P 567558363457, s2N 306610839454, s2P 2147626928554,
   s2P 8495069586697, s2P 1792681061795, s2N 5267205461699, s2N 1662588930653,
   s2P 1428657120968, s2P 145083839026, s2N 4072997907950, s2N 1330456610777,
   s2P 3508536655193, s2P 4988484845528, s2P 2803117407820]
private def s2V9S6 : List ℤ :=
  [s2P 1238392289355, s2P 6667865404678, s2P 2056181586594, s2P 5992009368204,
   s2P 1394651360407, s2P 3271951104585, s2P 5566786707272, s2P 8525892401949,
   s2P 8287215662560, s2P 437321098665, s2N 8735730496369, s2N 9151698014676, s2N 570422449213,
   s2P 4959947349325, s2P 2144676014551, s2N 7140568895569, s2N 4277865203187,
   s2P 517817209176, s2P 9145035906128, s2P 11127505760901, s2P 13427031788536,
   s2P 1705685684503, s2P 15108632091718, s2P 4145631355617, s2P 7481473570364,
   s2N 1414267157420, s2N 8466917875487, s2P 2352808712679, s2P 8838742482337,
   s2P 12939935286837, s2P 8952024291740, s2P 4638935285997, s2P 2957381016722,
   s2N 4936429208549, s2N 6713218533955, s2P 3397570385945, s2N 4519358520807,
   s2P 529904701766, s2P 8209887480799, s2N 2263072474932, s2P 3419629785353,
   s2P 9783152795031, s2N 10808534550971, s2P 4583894758610, s2P 10373873036625,
   s2N 5294382303308, s2P 736777710126, s2P 3899865602086, s2P 7266753327902,
   s2N 3656862639550, s2N 6849754655239, s2N 4391303734040, s2P 2114413431492,
   s2P 3959285705682, s2N 2107371672407, s2N 5679790462956, s2N 5644183389158,
   s2N 10058460239194, s2P 10782291576137, s2P 5429975381442, s2P 12920710862335,
   s2N 5252473758082, s2N 3567485040366, s2N 9983397682260]
private def s2V9S7 : List ℤ :=
  [s2N 315869176241, s2P 1410100353015, s2P 5202103450210, s2P 5765863455082,
   s2P 6335100710940, s2N 1894197971346, s2P 10682680944445, s2P 527333751612,
   s2P 9848754774867, s2P 5916806888727, s2P 56609006919983, s2P 134019254627056,
   s2P 221277804622138, s2P 300529941842235, s2P 358324290345795, s2P 387554094615489,
   s2P 387460464749158, s2P 362536003653673, s2P 320207378391194, s2P 268503783001116,
   s2P 214638406844708, s2P 164149858221144, s2P 120430963786269, s2P 84886018688048,
   s2P 57526023519868, s2P 37531013157981, s2P 23624886530931, s2P 14373608534855,
   s2P 8446909995269, s2P 4776748522310, s2P 2584929627977, s2P 1331914449685,
   s2P 651913264167, s2P 303492953859, s2P 135041345855, s2P 57859579768, s2P 24068181540,
   s2P 9786374375, s2P 3903718718, s2P 1527519726, s2P 584662677, s2P 218022660, s2P 78929658,
   s2P 27666587, s2P 9360319, s2P 3040266, s2P 940593, s2P 274876, s2P 75437, s2P 19414,
   s2P 4693, s2P 1065, s2P 219, s2P 38, s2P 3, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0]
private def s2V9 : List ℤ :=
  s2V9S0 ++
    (s2V9S1 ++
    (s2V9S2 ++
    (s2V9S3 ++
    (s2V9S4 ++
    (s2V9S5 ++
    (s2V9S6 ++
    (s2V9S7 ++
    mm32k512krS2VecIn8)))))))
private def s2V10S0 : List ℤ :=
  [s2P 7056, s2N 9793, s2N 19084, s2N 9401, s2P 64826, s2N 20681, s2P 42871, s2N 58825,
   s2P 9650, s2P 43741, s2N 2330, s2N 7469, s2P 25568, s2P 88893, s2N 34123, s2N 232890,
   s2P 310144, s2P 330748, s2P 97842, s2P 687333, s2P 746062, s2P 1491325, s2N 158247,
   s2N 3733273, s2P 1050525, s2N 52448, s2P 84081, s2P 887529, s2N 890600, s2N 302057,
   s2N 6063712, s2N 1066490, s2P 33009, s2P 375610, s2P 1636210, s2N 3584485, s2N 5028093,
   s2P 671321, s2P 4520764, s2P 7182057, s2P 4654947, s2P 3974909, s2P 1062572, s2N 6111352,
   s2P 13005114, s2N 4461061, s2P 7918512, s2P 5010674, s2N 6406209, s2N 10237881, s2P 6109026,
   s2P 24251288, s2N 16461343, s2N 8869915, s2P 29671649, s2N 26909053, s2N 48883189,
   s2N 10681913, s2N 53970924, s2N 82570055, s2N 36126111, s2N 26425799, s2P 52802447,
   s2P 10259074]
private def s2V10S1 : List ℤ :=
  [s2N 888486, s2P 10794110, s2P 46243791, s2N 48347143, s2P 80725372, s2N 72476438,
   s2N 21942107, s2N 136583532, s2N 113828319, s2P 93251360, s2P 23566372, s2N 38792963,
   s2N 105259357, s2N 19371507, s2N 85989150, s2N 37348470, s2N 94016413, s2N 6466959,
   s2N 73402833, s2P 110349177, s2N 36664545, s2P 51711233, s2N 28079267, s2N 60429628,
   s2N 134532193, s2N 178797579, s2N 269012709, s2N 177391144, s2P 75900457, s2P 253810291,
   s2N 36576304, s2P 124608998, s2P 237032623, s2N 325426590, s2P 82671318, s2P 267551645,
   s2P 147386863, s2N 178845664, s2P 53052049, s2N 323351918, s2N 235231470, s2P 522857563,
   s2P 88355802, s2P 11465546, s2P 163704126, s2P 798670537, s2P 230352622, s2P 501344365,
   s2P 372013908, s2N 242916569, s2N 341710216, s2N 2238796932, s2N 717705896, s2N 457387728,
   s2P 783216750, s2P 1129589156, s2N 1206847478, s2N 1124083424, s2N 169982305, s2N 472045627,
   s2N 530785734, s2N 2330358492, s2N 563422685, s2N 422452091]
private def s2V10S2 : List ℤ :=
  [s2N 503870586, s2N 4006975008, s2N 3033422938, s2N 2363059895, s2N 1137214847,
   s2N 1859674915, s2P 628297903, s2N 3221052124, s2P 2213627486, s2P 1615199775,
   s2N 1084812779, s2N 4320071268, s2N 2700218367, s2P 129659521, s2N 3168031085,
   s2P 1466881645, s2P 3106450910, s2P 3635350607, s2N 3261725495, s2N 2229422146,
   s2P 2408010221, s2N 1203707162, s2N 4217356054, s2N 2408636570, s2N 6572887095,
   s2N 4622025685, s2P 2592417924, s2P 5043495759, s2P 1550666193, s2N 4446950448,
   s2N 3280478048, s2N 3735776350, s2P 4062216888, s2P 3181484350, s2N 4266369047,
   s2N 8390067203, s2P 5608115760, s2P 2875759166, s2N 4192709625, s2P 1707573981,
   s2N 1015930744, s2P 1249569502, s2N 653214830, s2N 4187501877, s2N 3934014295,
   s2N 1516319001, s2N 2026538515, s2N 1932006801, s2N 5390078268, s2N 4896570505,
   s2N 4415657843, s2N 5397788851, s2N 11392492075, s2N 12977792332, s2N 16919879758,
   s2N 13719563248, s2N 11287399488, s2N 474739797, s2N 8822592960, s2N 19155538967,
   s2N 10845728586, s2N 34003357657, s2N 20229081436, s2N 14177139169]
private def s2V10S3 : List ℤ :=
  [s2P 2615837297, s2P 6904939218, s2P 31907790769, s2P 5885135125, s2P 23456025623,
   s2P 15288495607, s2P 17960814332, s2P 8238509807, s2P 9532120830, s2N 26857812094,
   s2N 31110924254, s2N 24160426834, s2N 23594442904, s2P 11175455801, s2N 4846677156,
   s2N 32495971307, s2P 8283853349, s2P 13019591378, s2P 60142801761, s2P 57073872132,
   s2N 45262286880, s2P 19115744307, s2P 3393848114, s2N 61412109521, s2P 8391063938,
   s2P 97275259711, s2P 29345881791, s2N 38094724155, s2N 64349670738, s2N 68872396393,
   s2P 17061393094, s2N 30776649295, s2N 136318823981, s2N 29417725683, s2P 44411264891,
   s2N 54657381741, s2P 14738891237, s2N 3579510380, s2P 96273474263, s2N 51553780308,
   s2N 45609459277, s2P 26613589714, s2N 75960067170, s2N 89642129151, s2N 39335059050,
   s2P 27255301403, s2P 63739744417, s2P 20615732471, s2P 40072842941, s2P 2557702719,
   s2N 100622555183, s2P 317841620267, s2P 21174508574, s2N 99967929171, s2N 88248251075,
   s2N 128189426600, s2P 70619390648, s2N 132873520449, s2N 161894322873, s2P 10826624170,
   s2N 96995570514, s2N 171498096725, s2P 87859645758, s2P 3358558920]
private def s2V10S4 : List ℤ :=
  [s2P 1000240081, s2P 302270007841, s2P 345401665918, s2P 408411755497, s2P 463731887844,
   s2P 203756562955, s2N 122427830269, s2N 17640617600, s2N 307320202184, s2N 70176147955,
   s2P 72626623158, s2P 236201634776, s2N 40661625868, s2N 40116458851, s2P 150363703333,
   s2P 138631076877, s2P 151748762162, s2P 213441062108, s2P 210298748693, s2P 243589566813,
   s2P 81878921586, s2N 104291889959, s2N 67086238519, s2N 150102740000, s2P 84309323322,
   s2P 410047056332, s2N 222955150806, s2P 316809609150, s2N 414715700167, s2N 167445850508,
   s2N 240711280337, s2N 682749059489, s2N 115174108265, s2N 20624357659, s2N 143354530527,
   s2P 16184641333, s2P 397366250733, s2N 38664786743, s2N 280800402003, s2N 106715300223,
   s2N 196890041176, s2N 9517970049, s2N 390720405654, s2N 309147447621, s2N 375915820517,
   s2N 136302883707, s2P 552477939951, s2N 312486048702, s2P 116402342928, s2P 613420311971,
   s2P 828514779862, s2P 1058296183718, s2P 971663645492, s2P 410203021608, s2N 221527917887,
   s2P 1318063518179, s2N 863984634070, s2P 795893374871, s2N 246619733544, s2N 902129593059,
   s2P 1140118216661, s2P 2970868349350, s2P 1927565036162, s2P 1437739560613]
private def s2V10S5 : List ℤ :=
  [s2P 2253337119794, s2P 1830137739634, s2N 219134984584, s2N 2975840613256,
   s2N 1451107821706, s2P 219457363483, s2P 3551116373049, s2P 2831835848633,
   s2P 3525227072012, s2P 182921200952, s2N 3918512201986, s2N 6424196228685,
   s2N 1559033327444, s2N 1097633585584, s2N 817045300229, s2P 2753469244341, s2N 515996493348,
   s2P 1476341707576, s2P 8132769007947, s2P 1197504066739, s2N 4735450073502,
   s2N 8189334675992, s2N 666653342435, s2N 4988376144153, s2N 1744379659475, s2P 554075537391,
   s2P 2912244194519, s2P 7245270486935, s2P 3265725927516, s2P 3174895319227,
   s2P 4697042355474, s2P 3768067813883, s2N 1078029823915, s2P 2139084917447, s2P 10486181934,
   s2P 629947214694, s2P 2587612739797, s2P 359383696274, s2P 7257924116583, s2N 1071048509863,
   s2P 1945935876358, s2P 3158491284302, s2N 3315691092058, s2N 7767316866953,
   s2N 555739648987, s2P 3655838936781, s2P 4631431375626, s2N 8939647465256,
   s2N 12411695884226, s2P 5397080690300, s2N 5217865306735, s2N 1852456688025,
   s2P 1414037231455, s2N 2111353584204, s2N 211435001821, s2N 4333431339268, s2P 21847525512,
   s2N 1911307522664, s2N 5069256934441, s2P 515192279458, s2P 162496107729, s2P 655571796123,
   s2P 1975657820882, s2P 7440719319624]
private def s2V10S6 : List ℤ :=
  [s2P 1870980101055, s2N 3411930080382, s2N 3005081825889, s2N 983139685733, s2N 482810627649,
   s2P 850751411417, s2N 6451960681099, s2N 2462460365944, s2N 2878166617783,
   s2P 1343276753844, s2N 628127887608, s2N 5739099001211, s2N 4059326322227,
   s2N 3054535745601, s2P 4836980996356, s2P 3288479208032, s2P 6330741470388,
   s2P 14062484655191, s2P 11841300543686, s2P 8981480125440, s2P 4077915081102,
   s2N 6509164157134, s2N 2661002702021, s2N 2547926228007, s2N 4870981698094,
   s2P 3795676756614, s2P 8906776325991, s2P 2454721248534, s2P 3259676173109,
   s2P 10208836425529, s2P 523100066175, s2P 8666375614615, s2P 11820974708238,
   s2P 12916614339966, s2P 14317753164889, s2P 2108115177672, s2P 6691833999873,
   s2P 9111622158484, s2P 6531483127626, s2N 2146345237796, s2P 4390900444001,
   s2P 20348840619686, s2P 7719115922440, s2P 1913801326662, s2N 33705298803,
   s2P 2970517219301, s2P 2126459082571, s2P 3244653687312, s2N 10592668639138,
   s2N 3333766178110, s2P 1247602761321, s2N 2300194908021, s2N 6505559402101,
   s2N 2887424690135, s2P 12737984460358, s2P 4780015063456, s2P 3037797745808,
   s2N 2842570980781, s2N 3265436774844, s2N 7337652915528, s2N 3765742039058,
   s2N 7959561119578, s2N 3994565488947, s2N 8324320239032]
private def s2V10S7 : List ℤ :=
  [s2N 12538388817802, s2N 7405102923651, s2N 9028271586835, s2N 1832101174625,
   s2P 627054262665, s2N 4461323772674, s2P 2444302021405, s2P 2569783397509,
   s2N 8063415177128, s2N 16201829002634, s2P 5993211077335, s2P 1442721056399,
   s2P 2129165575125, s2P 2689653692058, s2N 1888609201567, s2P 9237528985404,
   s2P 12518729289278, s2P 3097422994697, s2P 10607335117995, s2P 16866323125353,
   s2P 83600752491738, s2P 175014609220960, s2P 269114075158366, s2P 345782163112206,
   s2P 391978172122819, s2P 403380719727984, s2P 383366238931487, s2P 340298951922889,
   s2P 284333295612076, s2P 224827823621044, s2P 168880010456235, s2P 120833269236234,
   s2P 82629921485772, s2P 53820255679558, s2P 34329028314728, s2P 19372475708756,
   s2P 12745985087003, s2P 6568217804696, s2N 2337664603954, s2P 770807093378,
   s2P 379416558662, s2P 231395591066, s2P 126814443948, s2P 59833968506, s2P 25193664799,
   s2P 9803439413, s2P 3604612402, s2P 1267039680, s2P 427879560, s2P 138967102, s2P 43354539,
   s2P 12951799, s2P 3692647, s2P 999707, s2P 253634, s2P 59002, s2N 12323, s2P 2292, s2P 365,
   s2P 44, s2P 3, s2P 0, s2P 0, s2P 0]
private def s2V10 : List ℤ :=
  s2V10S0 ++
    (s2V10S1 ++
    (s2V10S2 ++
    (s2V10S3 ++
    (s2V10S4 ++
    (s2V10S5 ++
    (s2V10S6 ++
    (s2V10S7 ++
    mm32k512krS2VecIn8)))))))
private def s2V11S0 : List ℤ :=
  [s2N 274, s2P 21839, s2P 11926, s2P 1047, s2P 3503, s2N 45342, s2N 63441, s2N 70326,
   s2N 3320, s2N 14620, s2P 20350, s2N 72158, s2P 128920, s2N 278977, s2N 246405, s2N 271165,
   s2N 40525, s2N 163856, s2N 319299, s2P 75324, s2N 458396, s2N 193459, s2N 409499,
   s2P 462733, s2P 776979, s2P 1575029, s2P 249023, s2P 2572752, s2P 2985761, s2P 2928744,
   s2P 2880639, s2P 3454250, s2P 413662, s2P 3252647, s2N 25011, s2N 3727543, s2N 4408186,
   s2N 76690, s2N 5633562, s2N 7433899, s2P 7099997, s2N 2325924, s2N 4506719, s2P 6456698,
   s2P 2931688, s2P 3801850, s2P 4180951, s2N 1775654, s2P 5202762, s2N 83913, s2N 15422864,
   s2N 15318672, s2N 24424866, s2N 16781557, s2N 14965886, s2N 27775938, s2P 12489376,
   s2P 29143341, s2P 21586116, s2P 47651314, s2P 83118054, s2N 34810686, s2N 65412000,
   s2N 86417688]
private def s2V11S1 : List ℤ :=
  [s2P 535271, s2P 49586253, s2P 50341740, s2P 85345050, s2P 52488315, s2N 11523174,
   s2N 46867494, s2N 21634668, s2P 66187406, s2N 55457408, s2N 104228669, s2N 89270413,
   s2N 153988033, s2N 54425173, s2N 37536236, s2P 5140492, s2N 3231618, s2N 97460752,
   s2N 117395712, s2N 20143346, s2N 55245800, s2N 49360347, s2P 40298576, s2P 197929837,
   s2N 107440121, s2N 11620051, s2P 126321438, s2P 12287643, s2P 100110310, s2P 106187748,
   s2P 167375020, s2P 203356859, s2P 232654796, s2P 173158749, s2P 124008696, s2N 210899422,
   s2N 105543489, s2N 84155894, s2P 185564240, s2P 275327947, s2P 75966707, s2P 200596151,
   s2N 474951022, s2N 410412579, s2N 437922705, s2N 834769954, s2P 120876854, s2N 410594513,
   s2P 90977890, s2N 695097470, s2N 1756296, s2N 222053222, s2P 284492336, s2P 41284999,
   s2P 578348468, s2P 1085570724, s2P 75792477, s2P 162344912, s2P 305701989, s2P 1030746040,
   s2P 1390486477, s2P 1879691056, s2P 2357902826, s2P 1649051336]
private def s2V11S2 : List ℤ :=
  [s2P 515431342, s2P 87967250, s2N 1006342237, s2N 840113880, s2N 698939235, s2P 1921064632,
   s2N 788365855, s2N 345465566, s2N 1624212798, s2N 2802298994, s2N 1682088423, s2N 772663976,
   s2P 1784841510, s2P 1239867394, s2P 620213885, s2N 2294512861, s2P 3797149666,
   s2N 615140658, s2N 5098621029, s2N 2536756882, s2N 3960559249, s2P 3007565401,
   s2P 3181002888, s2N 2956888421, s2N 6372927375, s2N 1790912406, s2N 4022995217,
   s2N 185959718, s2P 4246008103, s2P 837954291, s2N 6287321177, s2P 456968527, s2N 3156735119,
   s2P 1081205486, s2N 1396136626, s2N 348756946, s2P 2168830159, s2N 2257308039,
   s2P 888660010, s2N 654784852, s2N 3061571004, s2N 813078459, s2P 14730227, s2P 202580468,
   s2P 9420811645, s2P 1947089602, s2N 8372033577, s2N 6531418653, s2N 6844239182,
   s2N 3064653549, s2N 4915713418, s2N 5698213127, s2N 5942224567, s2N 10080360270,
   s2P 3595465007, s2P 3424013414, s2P 6915120677, s2N 17057698869, s2N 2915385526,
   s2P 1102664603, s2N 4948900306, s2N 4160915783, s2P 9980898539, s2P 3540487100]
private def s2V11S3 : List ℤ :=
  [s2P 10922599573, s2P 12635479554, s2N 1406738909, s2P 9662147031, s2N 30882206104,
   s2N 18080900697, s2N 25473429450, s2N 13274378471, s2N 11964436424, s2P 10531453043,
   s2P 25259522512, s2N 9571474840, s2N 11530398781, s2P 30445512164, s2N 3283256157,
   s2N 50508021225, s2P 7059763125, s2P 6255437378, s2P 5992856783, s2N 27613271218,
   s2P 21502033039, s2N 12558915737, s2P 36356489967, s2P 6785503750, s2N 68443807648,
   s2N 41195639379, s2N 28066865998, s2P 40132617051, s2P 107231608405, s2P 42484459639,
   s2P 2966936302, s2N 32330806220, s2N 39487455661, s2N 15120337454, s2N 48153277154,
   s2N 74592365951, s2P 6786602040, s2P 88199375053, s2P 100632290935, s2P 44920915679,
   s2N 40550620037, s2N 82740427759, s2N 15110698151, s2N 55930853073, s2N 11283817404,
   s2N 19700579483, s2P 105766820484, s2N 19281188913, s2N 31509960054, s2N 87614800165,
   s2N 47647819956, s2N 87456729392, s2N 107714986519, s2N 120437647541, s2P 16499275870,
   s2P 138628579007, s2N 91466470747, s2P 145849714590, s2P 169620584520, s2P 144247934720,
   s2P 25741966532, s2P 118045416088, s2P 244024385731, s2P 134688914345]
private def s2V11S4 : List ℤ :=
  [s2P 77891148717, s2P 2686245850, s2P 165526904599, s2N 54748442086, s2N 230628129278,
   s2N 121932027383, s2N 11821302780, s2N 14081831829, s2P 74841086497, s2N 17684109028,
   s2N 335106430726, s2N 140677045471, s2N 95285931586, s2N 213146326784, s2N 47208316182,
   s2N 87776582381, s2N 176782314360, s2N 437131210817, s2N 333491882230, s2N 558784882131,
   s2N 183603432097, s2N 118513484388, s2N 215117786750, s2N 122834583598, s2N 207811580872,
   s2P 193174017532, s2N 90788565163, s2N 219385329244, s2N 389396594039, s2N 446476588730,
   s2N 100635219257, s2P 152265801836, s2N 130321859036, s2N 181833836835, s2N 201914571992,
   s2N 262641575797, s2P 122072585575, s2N 243609905587, s2N 175178785924, s2N 131297615665,
   s2P 136822157368, s2P 248609661940, s2P 95614120760, s2P 350091870043, s2N 185121924666,
   s2N 234346033647, s2N 52588021676, s2P 101140799403, s2P 281554915228, s2N 719044192485,
   s2N 93516349350, s2P 713499035732, s2N 488630136799, s2P 80475145486, s2N 68749395855,
   s2P 110406267765, s2P 300811946035, s2P 805762980816, s2P 1344840576591, s2P 2099738798606,
   s2P 1675531369996, s2P 1217176926812, s2P 773873303494, s2P 807069018253]
private def s2V11S5 : List ℤ :=
  [s2N 442086186376, s2N 1061668825937, s2N 21937979197, s2P 591838994736, s2N 57494508944,
   s2N 342105528341, s2P 1003980100163, s2P 1651696336936, s2N 990523925322, s2N 5826087666086,
   s2N 4001588455629, s2N 55733132345, s2N 3038205247826, s2N 949425596958, s2N 1723493082191,
   s2N 1097669431561, s2N 865156454678, s2N 1741859792198, s2N 4375000016271,
   s2N 4066965325445, s2P 800281750202, s2N 1188458394519, s2P 3893450257720,
   s2P 8630070260424, s2P 7006345916717, s2N 902453777894, s2N 6422756547392,
   s2P 3602394854884, s2P 2223300638512, s2N 6371991624214, s2P 2118176681072,
   s2P 557843074474, s2N 143831689775, s2P 3460574618170, s2N 1207329426008, s2P 1830674491234,
   s2N 284082986989, s2P 5289537596105, s2P 11104623918657, s2P 5512737041220,
   s2N 5262102088961, s2P 1165381128243, s2P 2463309361726, s2P 854416071469,
   s2P 3672667732973, s2P 1150541114958, s2P 2178084052239, s2P 431591753468, s2N 827749663577,
   s2P 2161593738990, s2P 4057507981080, s2P 3521531558330, s2P 3069402321502,
   s2P 1380762367020, s2P 2868097794587, s2N 6986503120672, s2N 10172171607329,
   s2N 7303886086448, s2N 3562719451837, s2N 4534148075252, s2N 1695698872723,
   s2P 1879920430608, s2P 8830000814155, s2N 3205569638178]
private def s2V11S6 : List ℤ :=
  [s2P 465933257037, s2N 1755725875602, s2P 783741193231, s2N 1015691559515, s2N 3946630034751,
   s2P 1607436983806, s2P 977733009975, s2P 1059752290887, s2N 6492410221043,
   s2N 6299343381791, s2P 1546899892699, s2N 1830528852639, s2N 388180481151, s2N 861954702710,
   s2N 4560044642520, s2N 2115403714354, s2P 1819178555911, s2N 954751333621,
   s2N 4534275837392, s2N 9920924893206, s2N 1854090423335, s2N 4913864341259,
   s2N 7142505371777, s2N 2801285560625, s2N 4441315255012, s2N 1969462903214,
   s2N 6747002200025, s2N 1045326546154, s2N 4488196838651, s2P 2425688097737,
   s2P 11193875550829, s2N 4830285844550, s2N 17696470739724, s2N 3669889957667,
   s2N 8945345895161, s2P 5312524214771, s2P 4591019023113, s2P 2486989103007,
   s2P 1455592956830, s2N 4889625699537, s2N 12956678749755, s2N 1824643031387,
   s2N 19788048291304, s2N 406913214764, s2N 6159288736291, s2P 6820735150390,
   s2P 17943945286498, s2P 13762981374696, s2P 252512686725, s2P 561930551464,
   s2P 6606682071798, s2P 8920576083524, s2P 3358790364651, s2N 1288111643381,
   s2N 13083259459508, s2P 723129644803, s2P 4207634062309, s2N 4574121944753,
   s2P 444941549622, s2P 7725806227652, s2N 1393765669347, s2N 1118047831747, s2N 154681066276,
   s2P 5202347445936]
private def s2V11S7 : List ℤ :=
  [s2N 2779832860721, s2P 6527925797158, s2P 2897035343782, s2P 3591924697429,
   s2N 5590549672816, s2P 4932408111365, s2P 13097558728112, s2N 1735633797023,
   s2N 13685809696345, s2N 9179419782988, s2N 10305722536759, s2N 11410376912745,
   s2P 2795190421507, s2P 6727785209170, s2N 657896617894, s2N 3341000971114,
   s2N 14791637487919, s2P 27986767110, s2N 3243899080229, s2N 7495911806876,
   s2P 2649310071621, s2P 13892534288682, s2P 7484723548798, s2N 4923122342600,
   s2P 13446133842557, s2N 11557604959314, s2P 7283151831228, s2P 11843169270562,
   s2P 29264981783670, s2P 112832007681724, s2P 217417329011007, s2P 319409769681117,
   s2P 385701454963586, s2P 419621613980743, s2P 407734418425152, s2P 365537583436749,
   s2P 304971103353194, s2P 241742845463649, s2P 174031989669916, s2P 119769964954670,
   s2P 82640808670937, s2P 53019038888027, s2P 28996303415923, s2P 13214656959237,
   s2P 5237959675024, s2N 1961240399916, s2P 805218317167, s2P 392067149038, s2P 193756174626,
   s2P 83558848628, s2P 31039425912, s2P 10770677958, s2P 3842697291, s2P 1426736657,
   s2P 516325515, s2P 171187373, s2P 52260835, s2P 12444235, s2P 2226494, s2P 357848,
   s2P 64457, s2P 11823, s2P 1765, s2P 185]
private def s2V11S8 : List ℤ :=
  [s2P 9]
private def s2V11 : List ℤ :=
  s2V11S0 ++
    (s2V11S1 ++
    (s2V11S2 ++
    (s2V11S3 ++
    (s2V11S4 ++
    (s2V11S5 ++
    (s2V11S6 ++
    (s2V11S7 ++
    s2V11S8)))))))
private theorem s2Ok0 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B0 mm32k512krS2LIn 512 mm32k512krS2PadIn mm32k512krS2VecIn)
      26 512 707067605 s2V0 = true := by decide +kernel
private theorem s2Ok1 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B1 26 512 707067605 s2V0)
      26 512 713741778 s2V1 = true := by decide +kernel
private theorem s2Ok2 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B2 26 512 713741778 s2V1)
      27 512 721773601 s2V2 = true := by decide +kernel
private theorem s2Ok3 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B3 27 512 721773601 s2V2)
      27 512 731723837 s2V3 = true := by decide +kernel
private theorem s2Ok4 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B4 27 512 731723837 s2V3)
      27 512 738434062 s2V4 = true := by decide +kernel
private theorem s2Ok5 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B5 27 512 738434062 s2V4)
      27 512 752652115 s2V5 = true := by decide +kernel
private theorem s2Ok6 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B6 27 512 752652115 s2V5)
      28 512 771197176 s2V6 = true := by decide +kernel
private theorem s2Ok7 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B7 28 512 771197176 s2V6)
      28 512 785193336 s2V7 = true := by decide +kernel
private theorem s2Ok8 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B8 28 512 785193336 s2V7)
      28 512 806978984 s2V8 = true := by decide +kernel
private theorem s2Ok9 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B9 28 512 806978984 s2V8)
      28 512 843575132 s2V9 = true := by decide +kernel
private theorem s2Ok10 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B10 28 512 843575132 s2V9)
      28 512 883840984 s2V10 = true := by decide +kernel
private theorem s2Ok11 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B11 28 512 883840984 s2V10)
      28 512 921392386 s2V11 = true := by decide +kernel
private theorem s2Ok12 :
    s2SegStateAt
      (rkm128kRunSegs 32 32 512 s2B12 28 512 921392386 s2V11)
      mm32k512krS2LOut 512 mm32k512krS2PadOut mm32k512krS2Vec = true := by decide +kernel

/-- Segment count of `mm32k512krS2Segs` (`25` segments). -/
theorem mm32k512krS2_len : rkm128kSegListLen mm32k512krS2Segs = 25 := by
  rfl

/-- Exact `rkm128kRunSegs 32 32 512` Markovian step across `mm32k512krS2Segs` (`segs
  80..104`). -/
theorem mm32k512krS2_step :
    rkm128kRunSegs 32 32 512 mm32k512krS2Segs mm32k512krS2LIn mm32k512krS2DCurIn
      mm32k512krS2PadIn mm32k512krS2VecIn =
      (mm32k512krS2LOut, mm32k512krS2DCurOut, mm32k512krS2PadOut,
        mm32k512krS2Vec) := by
  have hSegs : mm32k512krS2Segs =
      s2B0 ++ (s2B1 ++ (s2B2 ++ (s2B3 ++ (s2B4 ++ (s2B5 ++ (s2B6 ++
        (s2B7 ++ (s2B8 ++ (s2B9 ++ (s2B10 ++ (s2B11 ++ s2B12))))))))))) := rfl
  rw [hSegs]
  exact s2Step s2Ok0 (s2Step s2Ok1 (s2Step s2Ok2 (s2Step s2Ok3
    (s2Step s2Ok4 (s2Step s2Ok5 (s2Step s2Ok6 (s2Step s2Ok7
      (s2Step s2Ok8 (s2Step s2Ok9 (s2Step s2Ok10
        (s2Step s2Ok11 (s2SegStateAt_eq s2Ok12))))))))))))

/-- Suffix chaining lemma advancing `rkm128kRunSegs 32 32 512` past `mm32k512krS2Segs`. -/
theorem mm32k512krS2_run_after (rest : List Rkm128kSeg) :
    rkm128kRunSegs 32 32 512 (mm32k512krS2Segs ++ rest) mm32k512krS2LIn
      mm32k512krS2DCurIn mm32k512krS2PadIn mm32k512krS2VecIn =
      rkm128kRunSegs 32 32 512 rest mm32k512krS2LOut mm32k512krS2DCurOut
        mm32k512krS2PadOut mm32k512krS2Vec := by
  rw [rkm128kRunSegs_append]
  dsimp only
  rw [mm32k512krS2_step]

end

end QuantumComputation.Specs.GroverFindAll.Rk128kMidM32K512KrPt2
