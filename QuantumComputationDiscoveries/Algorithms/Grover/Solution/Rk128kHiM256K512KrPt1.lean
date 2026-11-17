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
# `(256, 512)` `RampKick128k` Krotov Part 1 (`Rk128kHiM256K512KrPt1`)

Certifies Slice 1 (`r = 512` segments `59..89`, `31` segments, `441,344` F1272 /
`442,206 <= 450,000` Horner coord-ops, `dk = 13`, `lTableMax = 4`, `degP <= 64`).
-/

namespace QuantumComputation.Specs.GroverFindAll
namespace Rk128kHiM256K512KrPt1

@[expose] public section

open QuantumComputation.Specs.DickeSol

/-- Unmodified segments 59..89 (31 segs) of (256, 512) r = 512 (lTableMax = 4). -/
def hm256k512krS1Segs : List Rkm128kSeg := [
  ⟨2, 295425, 1, 22, rkm128kMask56 512
    [32051930656735026, 62483461468486246, 30371661450334714, 55860607347609484,
     72057594037921967, 72057594037927935, 63050394783186943, 14295735565482941,
     14565476064552992, 223]⟩,
  ⟨2, 303554, 1, 23, rkm128kMask56 513
    [4679236351435786, 53944937470941021, 15796372165132091, 67209090806647986,
     72057594036866973, 72057594037927935, 18014398509481983, 9010576063307519,
     60572897705509336, 419]⟩,
  ⟨2, 305261, 1, 23, rkm128kMask56 513
    [66092128764649529, 68266248811602280, 51414810742291387, 19568709642700736,
     72057594010401632, 72057594037927935, 72057594037927935, 48182611312062399,
     29475655972534264, 460]⟩,
  ⟨2, 304779, 1, 23, rkm128kMask56 512
    [58963291564667841, 53830315196856249, 6283645408508926, 54597304649234318,
     72057593986428291, 68719476735, 0, 49766451870441600, 6107247036696064, 168]⟩,
  ⟨2, 301415, 1, 23, rkm128kMask56 512
    [67988032399155680, 43394376534673278, 7284273733109777, 50596423423410028, 34796837404,
     72055395014672384, 36028797018963967, 5573746844580863, 33252366456135513, 199]⟩,
  ⟨2, 355937, 1, 25, rkm128kMask56 512
    [44877973168182647, 18365447947481661, 32678086075220447, 1267605436505506, 2088103647435,
     0, 0, 10344018681933824, 58587630638263619, 150]⟩,
  ⟨2, 370475, 1, 26, rkm128kMask56 513
    [47030323363949585, 40615572150562227, 40117475412604506, 13190836212404649,
     19908546326640, 71494644084506624, 72057594037927935, 17225272945410015,
     41220882531114660, 489]⟩,
  ⟨2, 369422, 1, 26, rkm128kMask56 513
    [13132033832959470, 62180636998016221, 57874184552840877, 65720094543036125,
     56066636471578187, 36028797018963967, 0, 15455112046247936, 53619547371891600, 422]⟩,
  ⟨2, 386225, 1, 27, rkm128kMask56 511
    [22086593548283265, 39723655475148845, 71497786129810534, 28394649520148512,
     23622022551296341, 3, 24, 22420168878325760, 21627609575015155, 75]⟩,
  ⟨4, 170951, 1, 22, rkm128kMask56 513
    [69323858791298397, 37132707345968819, 13832134970227200, 61595498958427268,
     32788353190336998, 340, 192, 24924186323451904, 57158945845747157, 485]⟩,
  ⟨4, 236107, 1, 27, rkm128kMask56 513
    [485979816201224, 5606236888361314, 18155052555706134, 52776891777083138,
     47108795601643131, 44790, 0, 23012647372851204, 36509364053722794, 287]⟩,
  ⟨4, 249384, 1, 28, rkm128kMask56 513
    [57395085281720061, 62516056815082140, 18013125057844380, 57423544361345906,
     36582554873061368, 72057594035620019, 72057594037927935, 20499502020395007,
     46536690017455220, 298]⟩,
  ⟨4, 298304, 1, 32, rkm128kMask56 511
    [55116473450777664, 26773103974249379, 17779030797973530, 71306045498170241,
     16587884733311395, 16313563937, 201326592, 69357193480110082, 70116339994928482, 89]⟩,
  ⟨4, 297328, 1, 32, rkm128kMask56 513
    [38350258635042634, 33086177483142917, 66245231807626437, 54225821325082598,
     24260632984529210, 72054194635542646, 72057594037927935, 72057594037927935,
     14648183442849281, 343]⟩,
  ⟨4, 311168, 1, 33, rkm128kMask56 508
    [32620426668117922, 25400294372000196, 62708151050820608, 64455969085474391,
     18158686620191346, 1691794333896223, 0, 2251801961168896, 39747579958689792, 12]⟩,
  ⟨4, 304789, 1, 33, rkm128kMask56 512
    [65094908841495761, 68262683879864753, 45503193209785734, 47765869101514904,
     34627910460996354, 3446747460854675, 140737488355335, 1073741824, 17728909348962432, 177]⟩,
  ⟨4, 310208, 1, 33, rkm128kMask56 510
    [50502785206088945, 10701505987085827, 14878458460178992, 4908288744972374,
     59029114743892418, 32068401951296922, 36028797018960171, 72055395014672383,
     12124795755814903, 41]⟩,
  ⟨4, 318044, 1, 34, rkm128kMask56 512
    [35133754037428341, 44981886743474411, 26455271160838713, 12988129216815154,
     65616905904250819, 11360712378751565, 72057594037159599, 71987225293748207,
     29695610042974207, 149]⟩,
  ⟨4, 306941, 1, 33, rkm128kMask56 513
    [35150232413483837, 71464418095167829, 145725937590547, 63343347317763764,
     63286015986953376, 64227923856990583, 216610996, 2048, 22522405847040000, 280]⟩,
  ⟨4, 308942, 1, 33, rkm128kMask56 513
    [70227472593896825, 41797244725662271, 60797826067856508, 56932777532489279,
     21365812525015675, 18820815837712806, 72057533802847488, 72057594037403647,
     21320492468141567, 454]⟩,
  ⟨4, 312921, 1, 33, rkm128kMask56 513
    [4613918815624543, 36892883277580766, 19314287192005863, 4226799713338207,
     43799098059651275, 54460159897354987, 5700808074981, 536870912, 39708038877151232, 491]⟩,
  ⟨4, 339038, 1, 36, rkm128kMask56 511
    [12622264359208053, 3748394266545799, 58638680056591279, 54783771599765415,
     15324780709313179, 62995967673743544, 70921460577594777, 67553951460884479,
     63045996736675839, 83]⟩,
  ⟨4, 303305, 1, 33, rkm128kMask56 512
    [26786129346678528, 11511450374184240, 17542534865065390, 19293187070693273,
     6228155916633552, 34637492399009326, 57471778268282032, 549755813891, 2392812314165248,
     202]⟩,
  ⟨4, 314825, 1, 34, rkm128kMask56 512
    [54130615039296741, 10802808292555163, 3715810183439663, 35017534889640592,
     27020023552483046, 20124026876406277, 54616947817084884, 362, 4538783999459328, 176]⟩,
  ⟨4, 317486, 1, 34, rkm128kMask56 511
    [11948646670050690, 50533396656416804, 6507674385349166, 10656737797552980,
     27215147610425780, 29720636688395660, 40700368876888798, 57130, 36037593246203904, 84]⟩,
  ⟨4, 153026, 1, 20, rkm128kMask56 511
    [57974452093260708, 44008687995402920, 59019844505260654, 11172992939865709,
     51837672052974594, 7933076830540298, 4862078207946392, 140714, 9156732840312832, 68]⟩,
  ⟨4, 192988, 1, 23, rkm128kMask56 513
    [16435077982759357, 24926447920088858, 15964274782053354, 68777761695324692,
     34301357273521147, 70324616304089957, 43267479887020876, 72057594037731257,
     63048194686189567, 346]⟩,
  ⟨4, 170439, 1, 22, rkm128kMask56 512
    [57185750626676698, 27105231061962737, 11935043026107585, 8829296673554221,
     65014579306056708, 61313931545955686, 24190112058725092, 72057594037657586,
     51791395714760447, 214]⟩,
  ⟨4, 177331, 1, 22, rkm128kMask56 512
    [59490334219118897, 16714317865643487, 3604553890320827, 59078062771621896,
     17952549737853460, 71680807691816608, 22069738415747561, 943735426, 18577348462903296,
     137]⟩,
  ⟨4, 185569, 1, 23, rkm128kMask56 513
    [34791329084628044, 45183263466732013, 58845851851465461, 2816108381748177,
     17127343350766028, 23470259476622245, 22429125328063200, 72057589742432762,
     53480245575020543, 311]⟩,
  ⟨4, 201836, 1, 24, rkm128kMask56 513
    [34264476258659840, 1093718371927703, 54579559499362445, 29323948697602637,
     34753183106337120, 36125722174831877, 67127070042842935, 72057523144228782,
     67553994410523647, 511]⟩]

/-- Input multiplicity lIn = 2 entering hm256k512krS1Segs (after seg 58). -/
def hm256k512krS1LIn : ℕ := 2
/-- Input truncated dimension dCurIn = 512 entering hm256k512krS1Segs. -/
def hm256k512krS1DCurIn : ℕ := 512
/-- Input 10 ^ 15-scaled error pad padIn = 571733853 entering hm256k512krS1Segs. -/
def hm256k512krS1PadIn : ℕ := 571733853

/-- Slice 0 (64 entries) of hm256k512krS1VecIn. -/
def hm256k512krS1VecIn0 : List ℤ :=
  [Int.ofNat 7175496, Int.ofNat 10846536, Int.ofNat 3203560, Int.negSucc 33763892,
   Int.negSucc 101034042, Int.negSucc 36084381, Int.negSucc 61192714, Int.negSucc 38242929,
   Int.ofNat 106480546, Int.negSucc 7759191, Int.ofNat 71672427, Int.ofNat 43544362,
   Int.ofNat 68453639, Int.ofNat 43420147, Int.ofNat 8946312, Int.negSucc 70742397,
   Int.ofNat 11189797, Int.negSucc 10466110, Int.ofNat 10466938, Int.ofNat 23590142,
   Int.ofNat 106516095, Int.ofNat 140601675, Int.ofNat 257648858, Int.ofNat 139220312,
   Int.negSucc 210215025, Int.ofNat 112272907, Int.ofNat 35049437, Int.negSucc 11112532,
   Int.negSucc 231737663, Int.negSucc 435356255, Int.negSucc 19915358, Int.ofNat 83410972,
   Int.ofNat 58115044, Int.ofNat 88039033, Int.ofNat 660510425, Int.ofNat 768841882,
   Int.ofNat 352756164, Int.negSucc 541900502, Int.negSucc 854523690, Int.negSucc 1093238701,
   Int.negSucc 562460158, Int.negSucc 53266983, Int.negSucc 208024215, Int.negSucc 2151624180,
   Int.negSucc 3442063558, Int.negSucc 4920103049, Int.negSucc 3182335263,
   Int.negSucc 1894432439, Int.negSucc 4120635930, Int.ofNat 835283539, Int.ofNat 2754165832,
   Int.ofNat 1128505368, Int.negSucc 1749014360, Int.negSucc 1287387073, Int.ofNat 2742587038,
   Int.negSucc 661742267, Int.ofNat 893678752, Int.ofNat 752234303, Int.ofNat 2291773352,
   Int.ofNat 638918527, Int.ofNat 2590369775, Int.ofNat 3337330922, Int.negSucc 666329411,
   Int.ofNat 37084707]
/-- Slice 1 (64 entries) of hm256k512krS1VecIn. -/
def hm256k512krS1VecIn1 : List ℤ :=
  [Int.negSucc 6094126600, Int.negSucc 6456905602, Int.ofNat 2355023907, Int.ofNat 8003760013,
   Int.ofNat 5072620464, Int.negSucc 6530112489, Int.negSucc 1706296787,
   Int.negSucc 2710800098, Int.negSucc 7096108593, Int.negSucc 3970492890,
   Int.ofNat 5848498557, Int.ofNat 933324044, Int.ofNat 4674546808, Int.ofNat 1210419343,
   Int.negSucc 4889288111, Int.negSucc 220976518, Int.ofNat 526443361, Int.negSucc 2522594348,
   Int.ofNat 3861748790, Int.negSucc 232457918, Int.ofNat 1796477656, Int.ofNat 1465373241,
   Int.ofNat 494084743, Int.negSucc 4079740218, Int.negSucc 4092672186, Int.negSucc 1681010512,
   Int.ofNat 2696424981, Int.negSucc 1284639265, Int.negSucc 2200271164,
   Int.negSucc 4918973601, Int.negSucc 15917727095, Int.negSucc 29809378060,
   Int.negSucc 43283823054, Int.negSucc 47865186036, Int.negSucc 40662002875,
   Int.negSucc 32206492565, Int.negSucc 8305263191, Int.ofNat 16215543980,
   Int.ofNat 16620038402, Int.ofNat 9412190286, Int.negSucc 1602734098, Int.negSucc 6054371113,
   Int.negSucc 6114491067, Int.negSucc 4028100486, Int.negSucc 2519571606,
   Int.negSucc 916786066, Int.ofNat 1837053243, Int.negSucc 11318996919,
   Int.negSucc 14983836872, Int.negSucc 14972059452, Int.negSucc 9392985439,
   Int.negSucc 4290822524, Int.ofNat 13781698208, Int.negSucc 5284805732,
   Int.negSucc 9001401185, Int.ofNat 2615958760, Int.negSucc 2507054852, Int.ofNat 4363426619,
   Int.negSucc 3071326163, Int.negSucc 6942584448, Int.negSucc 4394779577,
   Int.negSucc 7258775008, Int.ofNat 15162817287, Int.ofNat 24999427980]
/-- Slice 2 (64 entries) of hm256k512krS1VecIn. -/
def hm256k512krS1VecIn2 : List ℤ :=
  [Int.ofNat 25411976747, Int.ofNat 19999449066, Int.ofNat 11513784830, Int.ofNat 5427671031,
   Int.ofNat 244856997, Int.ofNat 4615496435, Int.negSucc 9267432206, Int.negSucc 6218612635,
   Int.negSucc 18111287241, Int.negSucc 15526183525, Int.ofNat 619532326,
   Int.negSucc 1515351621, Int.ofNat 9790656933, Int.ofNat 7928525762, Int.negSucc 14581712488,
   Int.negSucc 4578556870, Int.negSucc 11867506343, Int.ofNat 14025298300,
   Int.ofNat 19782958373, Int.negSucc 6490247451, Int.negSucc 8265117010,
   Int.negSucc 10395951444, Int.negSucc 12252393981, Int.negSucc 11435975092,
   Int.negSucc 3232455810, Int.negSucc 10218888377, Int.negSucc 26001195587,
   Int.negSucc 5445139611, Int.negSucc 5075085898, Int.negSucc 7981292831, Int.ofNat 11172273,
   Int.negSucc 3370768200, Int.negSucc 21082369381, Int.negSucc 21939476938,
   Int.ofNat 14505336989, Int.negSucc 9111387147, Int.negSucc 2548068531,
   Int.negSucc 1094156249, Int.negSucc 8650196937, Int.ofNat 11448238733,
   Int.negSucc 4910482988, Int.ofNat 840766150, Int.negSucc 10829623577,
   Int.negSucc 12793639023, Int.ofNat 5773903804, Int.ofNat 10038828292, Int.ofNat 10572932069,
   Int.ofNat 15059433391, Int.ofNat 13504654552, Int.negSucc 1196061694, Int.ofNat 3898425321,
   Int.ofNat 4373047237, Int.ofNat 6006614412, Int.ofNat 4377776159, Int.ofNat 7671731172,
   Int.negSucc 5486308615, Int.negSucc 4388264574, Int.ofNat 7263093485,
   Int.negSucc 2534669394, Int.ofNat 11039934710, Int.negSucc 5884617909,
   Int.negSucc 19598743063, Int.negSucc 1876436224, Int.negSucc 8207293627]
/-- Slice 3 (64 entries) of hm256k512krS1VecIn. -/
def hm256k512krS1VecIn3 : List ℤ :=
  [Int.negSucc 5085199505, Int.ofNat 15172281425, Int.ofNat 6925812659, Int.negSucc 1281556952,
   Int.ofNat 2412172021, Int.negSucc 5216940796, Int.negSucc 6880790168,
   Int.negSucc 2828318253, Int.negSucc 4556081733, Int.negSucc 1670277689,
   Int.ofNat 1019496821, Int.ofNat 2360700909, Int.ofNat 13842050426, Int.ofNat 273940537,
   Int.negSucc 2015644510, Int.ofNat 6955589130, Int.ofNat 1717458211, Int.ofNat 12241535572,
   Int.negSucc 3361087930, Int.ofNat 12176676393, Int.ofNat 15074295547, Int.ofNat 10280299596,
   Int.negSucc 10202352239, Int.negSucc 11129391594, Int.ofNat 6741583512,
   Int.negSucc 5402175574, Int.ofNat 9123404042, Int.ofNat 12363385003, Int.ofNat 23010294201,
   Int.negSucc 11863589707, Int.negSucc 8169419106, Int.negSucc 12748376263,
   Int.ofNat 26405066849, Int.negSucc 8217307521, Int.negSucc 7929776623,
   Int.negSucc 6375434744, Int.ofNat 11305479124, Int.ofNat 17496961506,
   Int.negSucc 23836729472, Int.negSucc 3102859326, Int.ofNat 18600067031,
   Int.ofNat 42626562968, Int.ofNat 95649568921, Int.ofNat 145916907892,
   Int.ofNat 276923769009, Int.ofNat 400829354886, Int.ofNat 693988559502,
   Int.ofNat 1091771985424, Int.ofNat 1645382127350, Int.ofNat 2495910606008,
   Int.ofNat 3659385706539, Int.ofNat 5322064245438, Int.ofNat 7560776490714,
   Int.ofNat 10499721861149, Int.ofNat 14385614028872, Int.ofNat 19353039318152,
   Int.ofNat 25565202819609, Int.ofNat 33211890513612, Int.ofNat 42410651208214,
   Int.ofNat 53290480746859, Int.ofNat 65887076147675, Int.ofNat 80127747832175,
   Int.ofNat 95939559279825, Int.ofNat 113106894572205]
/-- Slice 4 (64 entries) of hm256k512krS1VecIn. -/
def hm256k512krS1VecIn4 : List ℤ :=
  [Int.ofNat 131261841238729, Int.ofNat 150038905853487, Int.ofNat 168971390708172,
   Int.ofNat 187434953514079, Int.ofNat 204837876554822, Int.ofNat 220650164242041,
   Int.ofNat 234286246598223, Int.ofNat 245178203543228, Int.ofNat 252923919577413,
   Int.ofNat 257276388367386, Int.ofNat 258083217756521, Int.ofNat 255314249978982,
   Int.ofNat 249102457927263, Int.ofNat 239726213901780, Int.ofNat 227577737641052,
   Int.ofNat 213145180586837, Int.ofNat 196976574106341, Int.ofNat 179627881444471,
   Int.ofNat 161637585618945, Int.ofNat 143527116778977, Int.ofNat 125782637157060,
   Int.ofNat 108811206118893, Int.ofNat 92915879443487, Int.ofNat 78312562601023,
   Int.ofNat 65154967689707, Int.ofNat 53531223604492, Int.ofNat 43444826782853,
   Int.ofNat 34818837125881, Int.ofNat 27533418055147, Int.ofNat 21467073655041,
   Int.ofNat 16510114269622, Int.ofNat 12550066573403, Int.ofNat 9453855507410,
   Int.ofNat 7068123985882, Int.ofNat 5238150259921, Int.ofNat 3830522494474,
   Int.ofNat 2745384915229, Int.ofNat 1914561981789, Int.ofNat 1291120838891,
   Int.ofNat 838330698485, Int.ofNat 522925673711, Int.ofNat 313285806933,
   Int.ofNat 180571135836, Int.ofNat 100490749976, Int.ofNat 54303352751,
   Int.ofNat 28718146985, Int.ofNat 15011686493, Int.ofNat 7843842425, Int.ofNat 4141239053,
   Int.ofNat 2226395117, Int.ofNat 1222037255, Int.ofNat 682863158, Int.ofNat 385863934,
   Int.ofNat 218711769, Int.ofNat 123421751, Int.ofNat 68929266, Int.ofNat 37934820,
   Int.ofNat 20512629, Int.ofNat 10877070, Int.ofNat 5648799, Int.ofNat 2870658,
   Int.ofNat 1426691, Int.ofNat 693121, Int.ofNat 329059]
/-- Slice 5 (64 entries) of hm256k512krS1VecIn. -/
def hm256k512krS1VecIn5 : List ℤ :=
  [Int.ofNat 152612, Int.ofNat 69123, Int.ofNat 30564, Int.ofNat 13181, Int.ofNat 5539,
   Int.ofNat 2260, Int.ofNat 891, Int.ofNat 335, Int.ofNat 117, Int.ofNat 36, Int.ofNat 8,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
/-- Slice 6 (64 entries) of hm256k512krS1VecIn. -/
def hm256k512krS1VecIn6 : List ℤ :=
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
/-- Slice 7 (64 entries) of hm256k512krS1VecIn. -/
def hm256k512krS1VecIn7 : List ℤ :=
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
/-- Slice 8 (1 entries) of hm256k512krS1VecIn. -/
def hm256k512krS1VecIn8 : List ℤ :=
  [Int.ofNat 0]
/-- Input 513-entry fixed-point amplitude vector entering hm256k512krS1Segs. -/
def hm256k512krS1VecIn : List ℤ :=
  hm256k512krS1VecIn0 ++
  (hm256k512krS1VecIn1 ++
  (hm256k512krS1VecIn2 ++
  (hm256k512krS1VecIn3 ++
  (hm256k512krS1VecIn4 ++
  (hm256k512krS1VecIn5 ++
  (hm256k512krS1VecIn6 ++
  (hm256k512krS1VecIn7 ++
  (hm256k512krS1VecIn8))))))))

/-- Output multiplicity lOut = 4 exiting hm256k512krS1Segs (after seg 89). -/
def hm256k512krS1LOut : ℕ := 4
/-- Output truncated dimension dCurOut = 512 exiting hm256k512krS1Segs. -/
def hm256k512krS1DCurOut : ℕ := 512
/-- Output 10 ^ 15-scaled error pad padOut = 856402969 exiting hm256k512krS1Segs. -/
def hm256k512krS1PadOut : ℕ := 856402969

/-- Slice 0 (64 entries) of hm256k512krS1Vec. -/
def hm256k512krS1Vec0 : List ℤ :=
  [Int.ofNat 238127, Int.negSucc 696448, Int.ofNat 339651, Int.ofNat 456061, Int.ofNat 1439903,
   Int.ofNat 640333, Int.ofNat 1832285, Int.ofNat 889631, Int.ofNat 295187, Int.ofNat 1379516,
   Int.ofNat 591443, Int.ofNat 1764612, Int.negSucc 3653289, Int.negSucc 5005824,
   Int.negSucc 164728, Int.ofNat 6184219, Int.ofNat 4550731, Int.ofNat 7288818,
   Int.ofNat 6990467, Int.ofNat 15674716, Int.ofNat 16457958, Int.ofNat 6216878,
   Int.negSucc 6866844, Int.negSucc 667673, Int.negSucc 4252957, Int.negSucc 6798059,
   Int.negSucc 3605705, Int.ofNat 7592417, Int.negSucc 3929234, Int.negSucc 6559367,
   Int.negSucc 2404668, Int.negSucc 8484434, Int.negSucc 10539614, Int.negSucc 28537996,
   Int.negSucc 41293390, Int.negSucc 53508684, Int.negSucc 2980553, Int.ofNat 42027086,
   Int.ofNat 8710376, Int.negSucc 959957, Int.negSucc 44510465, Int.ofNat 19558256,
   Int.negSucc 37390663, Int.negSucc 47275477, Int.negSucc 40981327, Int.ofNat 4321502,
   Int.ofNat 44826762, Int.negSucc 33820615, Int.negSucc 25427149, Int.negSucc 32947149,
   Int.negSucc 56738857, Int.ofNat 21047872, Int.ofNat 21531106, Int.ofNat 35163784,
   Int.ofNat 52501211, Int.negSucc 65287575, Int.ofNat 74988688, Int.ofNat 101968124,
   Int.ofNat 103363675, Int.ofNat 179068668, Int.ofNat 30960700, Int.negSucc 46599210,
   Int.negSucc 6620756, Int.negSucc 64879437]
/-- Slice 1 (64 entries) of hm256k512krS1Vec. -/
def hm256k512krS1Vec1 : List ℤ :=
  [Int.ofNat 57136936, Int.negSucc 20732901, Int.negSucc 22337315, Int.ofNat 9266109,
   Int.ofNat 89502602, Int.ofNat 51963499, Int.negSucc 98292814, Int.negSucc 72893448,
   Int.ofNat 174748577, Int.ofNat 76717837, Int.ofNat 42330094, Int.negSucc 120157465,
   Int.ofNat 119823434, Int.ofNat 556730360, Int.ofNat 377366540, Int.ofNat 245119806,
   Int.negSucc 144040928, Int.negSucc 90682747, Int.negSucc 173284179, Int.negSucc 435149915,
   Int.negSucc 429767479, Int.negSucc 176956882, Int.negSucc 289465270, Int.negSucc 324066172,
   Int.ofNat 220095111, Int.ofNat 386578941, Int.ofNat 54144233, Int.ofNat 495262556,
   Int.ofNat 24978312, Int.ofNat 383078728, Int.ofNat 752441163, Int.ofNat 233158747,
   Int.negSucc 46049563, Int.negSucc 264106913, Int.negSucc 622293557, Int.ofNat 311744915,
   Int.negSucc 4912973, Int.negSucc 204251353, Int.negSucc 945443489, Int.negSucc 242657233,
   Int.ofNat 405898692, Int.negSucc 447887156, Int.negSucc 891453365, Int.ofNat 77069584,
   Int.ofNat 554262145, Int.ofNat 413608165, Int.negSucc 766594286, Int.negSucc 736394666,
   Int.ofNat 601027764, Int.negSucc 627654478, Int.negSucc 50234018, Int.negSucc 457512704,
   Int.ofNat 681883216, Int.ofNat 842666233, Int.ofNat 247196172, Int.ofNat 764859609,
   Int.negSucc 296299710, Int.ofNat 215098464, Int.ofNat 184071133, Int.negSucc 786928292,
   Int.negSucc 1430021457, Int.negSucc 1279089778, Int.negSucc 1029196364,
   Int.negSucc 2245491781]
/-- Slice 2 (64 entries) of hm256k512krS1Vec. -/
def hm256k512krS1Vec2 : List ℤ :=
  [Int.ofNat 1424987883, Int.ofNat 4502277161, Int.negSucc 1087793424, Int.negSucc 317739239,
   Int.ofNat 2606263047, Int.negSucc 1040161653, Int.negSucc 1632865711,
   Int.negSucc 2982693102, Int.negSucc 4731650625, Int.negSucc 2744581853,
   Int.negSucc 6336615256, Int.negSucc 1816979407, Int.ofNat 3409347941, Int.ofNat 5328359157,
   Int.ofNat 5772223847, Int.ofNat 8667068597, Int.ofNat 3032413614, Int.negSucc 752739860,
   Int.negSucc 271352172, Int.ofNat 1846152619, Int.ofNat 6255178646, Int.negSucc 4048302206,
   Int.negSucc 4838719430, Int.negSucc 1960607090, Int.ofNat 5025464402,
   Int.negSucc 5062998722, Int.negSucc 10558137351, Int.ofNat 3369668461, Int.ofNat 6431301783,
   Int.negSucc 5978969445, Int.negSucc 7109502767, Int.negSucc 6883504219,
   Int.negSucc 8251106978, Int.negSucc 4339301216, Int.ofNat 2000775984,
   Int.negSucc 2623145318, Int.negSucc 2397676549, Int.negSucc 496386730, Int.ofNat 226834896,
   Int.negSucc 1543532426, Int.ofNat 1395022926, Int.ofNat 46828523, Int.ofNat 3585784204,
   Int.ofNat 1144093634, Int.negSucc 4054318379, Int.ofNat 660490298, Int.negSucc 2257915575,
   Int.ofNat 9035094265, Int.ofNat 2931541156, Int.ofNat 4922209349, Int.ofNat 9526897234,
   Int.ofNat 5233262783, Int.negSucc 12057334514, Int.negSucc 12030801188, Int.ofNat 217493179,
   Int.ofNat 1536292555, Int.ofNat 10372580692, Int.ofNat 11607649550, Int.negSucc 7624151923,
   Int.negSucc 8642692793, Int.ofNat 5493601927, Int.ofNat 489990040, Int.negSucc 4991127803,
   Int.negSucc 7467333609]
/-- Slice 3 (64 entries) of hm256k512krS1Vec. -/
def hm256k512krS1Vec3 : List ℤ :=
  [Int.negSucc 18222020260, Int.ofNat 703001217, Int.ofNat 5183886452, Int.ofNat 14680033183,
   Int.negSucc 11305559044, Int.negSucc 15904965870, Int.ofNat 19706154261,
   Int.negSucc 3288345886, Int.ofNat 17856451639, Int.negSucc 445487524,
   Int.negSucc 6556107520, Int.negSucc 1017305693, Int.ofNat 36682405293,
   Int.ofNat 18883611104, Int.ofNat 21569489375, Int.ofNat 6387522705, Int.ofNat 1603551045,
   Int.ofNat 1009931965, Int.negSucc 5307340700, Int.negSucc 10578184821, Int.ofNat 5323207294,
   Int.ofNat 4888030362, Int.negSucc 27362390834, Int.negSucc 25588100123,
   Int.negSucc 32507511932, Int.negSucc 13497266025, Int.negSucc 11299911,
   Int.negSucc 1916493891, Int.negSucc 6418154643, Int.ofNat 10974412210,
   Int.negSucc 9371272489, Int.negSucc 8294917269, Int.ofNat 17155255497,
   Int.negSucc 2504775383, Int.negSucc 26593308459, Int.negSucc 17078490696,
   Int.negSucc 12967550273, Int.negSucc 19939092761, Int.negSucc 25553671602,
   Int.negSucc 12567160308, Int.ofNat 26617295145, Int.ofNat 1759567321,
   Int.negSucc 6800606794, Int.negSucc 9013720422, Int.negSucc 4579097681,
   Int.ofNat 12092167116, Int.ofNat 1073778043, Int.negSucc 13430841772, Int.ofNat 9915980793,
   Int.negSucc 9916530186, Int.negSucc 4384508120, Int.ofNat 28428415600,
   Int.ofNat 32144813258, Int.ofNat 5898424023, Int.negSucc 39152377122,
   Int.negSucc 14524181471, Int.negSucc 20664422496, Int.ofNat 12800262716,
   Int.negSucc 15879821150, Int.ofNat 1459828120, Int.ofNat 34061664664, Int.ofNat 25224088272,
   Int.ofNat 1486037095, Int.negSucc 23257808915]
/-- Slice 4 (64 entries) of hm256k512krS1Vec. -/
def hm256k512krS1Vec4 : List ℤ :=
  [Int.negSucc 8339178038, Int.negSucc 16221612008, Int.ofNat 4686373481, Int.ofNat 5852974630,
   Int.negSucc 3461950992, Int.negSucc 10533340480, Int.negSucc 2580047093,
   Int.negSucc 14618249272, Int.negSucc 24824019853, Int.negSucc 28285953844,
   Int.negSucc 35548742993, Int.ofNat 5154923026, Int.negSucc 1776770552, Int.ofNat 5583345004,
   Int.ofNat 3277460317, Int.negSucc 14635599775, Int.ofNat 23762114191, Int.ofNat 11129664502,
   Int.ofNat 6562148434, Int.ofNat 18606704316, Int.ofNat 1258011081, Int.ofNat 4762634085,
   Int.negSucc 12937489495, Int.negSucc 13972827150, Int.negSucc 5545689761,
   Int.ofNat 19298113160, Int.ofNat 13711892089, Int.ofNat 22940322565, Int.ofNat 56553695344,
   Int.ofNat 41420269878, Int.ofNat 12463185271, Int.ofNat 12300956179, Int.ofNat 3730696688,
   Int.negSucc 32515838966, Int.ofNat 8909447876, Int.negSucc 30304849386,
   Int.ofNat 13474057233, Int.negSucc 8675264059, Int.ofNat 6797382659,
   Int.negSucc 19850130503, Int.negSucc 34440798262, Int.negSucc 84841623452,
   Int.negSucc 66813174507, Int.negSucc 72485520575, Int.ofNat 39335692224,
   Int.negSucc 21625853716, Int.negSucc 25150170861, Int.negSucc 10013347122,
   Int.negSucc 8224295622, Int.ofNat 13459113395, Int.negSucc 82030565929,
   Int.ofNat 67157814469, Int.ofNat 70533391550, Int.ofNat 81092672417, Int.ofNat 14451707171,
   Int.ofNat 56999953544, Int.ofNat 207414007191, Int.ofNat 116199739161,
   Int.negSucc 198271837504, Int.negSucc 14144064986, Int.negSucc 172037070459,
   Int.negSucc 160456165851, Int.ofNat 160408939757, Int.negSucc 120145565711]
/-- Slice 5 (64 entries) of hm256k512krS1Vec. -/
def hm256k512krS1Vec5 : List ℤ :=
  [Int.negSucc 75100589859, Int.ofNat 218230414528, Int.ofNat 26172547071,
   Int.ofNat 104966218244, Int.ofNat 225550481721, Int.ofNat 119567567105,
   Int.ofNat 82872248756, Int.ofNat 60716092112, Int.negSucc 4022318272, Int.ofNat 95112505208,
   Int.negSucc 82935916718, Int.negSucc 58800910484, Int.ofNat 155311147260,
   Int.negSucc 87977328307, Int.ofNat 138997497924, Int.negSucc 73040072656,
   Int.negSucc 142488064601, Int.ofNat 110844533437, Int.ofNat 9872535528,
   Int.negSucc 18322044784, Int.negSucc 141948293457, Int.negSucc 50597460308,
   Int.ofNat 100412222019, Int.ofNat 78247944507, Int.negSucc 390737153366,
   Int.negSucc 332030318864, Int.negSucc 118777915766, Int.negSucc 169281765228,
   Int.negSucc 40863673133, Int.ofNat 268785587762, Int.ofNat 40433687526,
   Int.ofNat 100198261168, Int.ofNat 24457477026, Int.ofNat 277949438371,
   Int.ofNat 505690448023, Int.ofNat 169460680651, Int.ofNat 355650859345,
   Int.negSucc 67500617364, Int.negSucc 180387994003, Int.negSucc 99914094032,
   Int.ofNat 260056295237, Int.negSucc 37399771487, Int.negSucc 20443382936,
   Int.negSucc 226267845092, Int.negSucc 171136937745, Int.ofNat 557068544832,
   Int.ofNat 531098454754, Int.negSucc 506721340573, Int.ofNat 594709506153,
   Int.negSucc 197929407698, Int.ofNat 146634042727, Int.negSucc 43313494235,
   Int.ofNat 325141688845, Int.negSucc 382819510246, Int.negSucc 174708408605,
   Int.negSucc 113679375838, Int.ofNat 722180904087, Int.ofNat 280215569037,
   Int.ofNat 61589192953, Int.ofNat 150768095308, Int.ofNat 429680254450,
   Int.ofNat 782673406202, Int.ofNat 71644666124, Int.negSucc 691609355176]
/-- Slice 6 (64 entries) of hm256k512krS1Vec. -/
def hm256k512krS1Vec6 : List ℤ :=
  [Int.negSucc 685353158460, Int.negSucc 75279374258, Int.negSucc 31006664528,
   Int.ofNat 1100146309424, Int.ofNat 613162980021, Int.negSucc 495981926975,
   Int.ofNat 167386815429, Int.negSucc 1094872851217, Int.negSucc 734354732888,
   Int.negSucc 722062537798, Int.negSucc 1830556825335, Int.ofNat 439512280594,
   Int.ofNat 264734846563, Int.negSucc 1429688253107, Int.ofNat 906707760215,
   Int.negSucc 1402989273153, Int.negSucc 2032686652610, Int.negSucc 671552707315,
   Int.ofNat 540955760328, Int.ofNat 196975771113, Int.ofNat 261387170720,
   Int.ofNat 486093718377, Int.negSucc 445747755923, Int.negSucc 1218345192512,
   Int.negSucc 1278426835874, Int.negSucc 1168716614550, Int.negSucc 292301015744,
   Int.ofNat 1265219925768, Int.ofNat 114180522631, Int.negSucc 1433075311728,
   Int.negSucc 678727764745, Int.negSucc 997731269779, Int.negSucc 417179112208,
   Int.negSucc 662072639804, Int.ofNat 3412346670256, Int.ofNat 3421328845632,
   Int.negSucc 2395809835209, Int.negSucc 938171980138, Int.ofNat 895868648425,
   Int.negSucc 818796568811, Int.negSucc 2815112619174, Int.negSucc 5484144878228,
   Int.negSucc 3235163646607, Int.ofNat 1380457517606, Int.negSucc 2740120102736,
   Int.negSucc 3620835682643, Int.negSucc 20057551578677, Int.negSucc 47171494628729,
   Int.negSucc 83948201692274, Int.negSucc 127856656652804, Int.negSucc 175239819059278,
   Int.negSucc 221933681763854, Int.negSucc 263933336498909, Int.negSucc 297887002959883,
   Int.negSucc 321279592580888, Int.negSucc 332471080286628, Int.negSucc 330878024127033,
   Int.negSucc 317262401623570, Int.negSucc 293757595681009, Int.negSucc 263405386186851,
   Int.negSucc 229408127689182, Int.negSucc 194518460799327, Int.negSucc 160772588476776,
   Int.negSucc 129551549453071]
/-- Slice 7 (64 entries) of hm256k512krS1Vec. -/
def hm256k512krS1Vec7 : List ℤ :=
  [Int.negSucc 101684812375042, Int.negSucc 77647738439940, Int.negSucc 57553096883625,
   Int.negSucc 41323577451242, Int.negSucc 28663681425633, Int.negSucc 19147230631013,
   Int.negSucc 12293609772280, Int.negSucc 7575308099540, Int.negSucc 4455528992946,
   Int.negSucc 2528720676476, Int.ofNat 1334376170771, Int.negSucc 722649255337,
   Int.negSucc 364410340186, Int.negSucc 149718779330, Int.negSucc 51002590284,
   Int.ofNat 17214915090, Int.negSucc 7249311850, Int.negSucc 3795465178,
   Int.negSucc 2130581008, Int.negSucc 1193892996, Int.negSucc 657127129,
   Int.negSucc 352985475, Int.negSucc 184004908, Int.negSucc 92750373, Int.negSucc 45148609,
   Int.negSucc 21223179, Int.negSucc 9639545, Int.negSucc 4234033, Int.negSucc 1800213,
   Int.negSucc 741420, Int.negSucc 295754, Int.negSucc 114132, Int.negSucc 42522,
   Int.negSucc 15258, Int.negSucc 5261, Int.negSucc 1738, Int.negSucc 544, Int.negSucc 157,
   Int.negSucc 39, Int.negSucc 7, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
/-- Slice 8 (1 entries) of hm256k512krS1Vec. -/
def hm256k512krS1Vec8 : List ℤ :=
  [Int.ofNat 0]
/-- Checkpoint 513-entry fixed-point amplitude vector exiting hm256k512krS1Segs. -/
def hm256k512krS1Vec : List ℤ :=
  hm256k512krS1Vec0 ++
  (hm256k512krS1Vec1 ++
  (hm256k512krS1Vec2 ++
  (hm256k512krS1Vec3 ++
  (hm256k512krS1Vec4 ++
  (hm256k512krS1Vec5 ++
  (hm256k512krS1Vec6 ++
  (hm256k512krS1Vec7 ++
  (hm256k512krS1Vec8))))))))

end

public section

open QuantumComputation.Specs.DickeSol

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
    | negSucc _ => cases h
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
private def s1StateAt (st : ℕ × ℕ × ℕ × List ℤ) (l d p : ℕ) (v : List ℤ) : Bool :=
  match st with
  | (ls, ds, ps, vs) =>
    Bool.and (s1NatEq ls l)
      (Bool.and (s1NatEq ds d) (Bool.and (s1NatEq ps p) (s1IntListEq vs v)))
private theorem s1StateAt_eq {st : ℕ × ℕ × ℕ × List ℤ} {l d p : ℕ} {v : List ℤ}
    (h : s1StateAt st l d p v = true) : st = (l, d, p, v) := by
  rcases st with ⟨ls, ds, ps, vs⟩
  unfold s1StateAt at h; dsimp only at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨hl, ⟨hd, ⟨hp, hv⟩⟩⟩
  rw [s1NatEq_eq hl, s1NatEq_eq hd, s1NatEq_eq hp, s1IntListEq_eq hv]
private abbrev s1P : ℕ → ℤ := Int.ofNat
private abbrev s1N : ℕ → ℤ := Int.negSucc
private def s1RunAt (c : List Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (l1 d1 p1 : ℕ) (v1 : List ℤ) : Bool :=
  s1StateAt (rkm128kRunSegs 256 4 512 c l0 d0 p0 v0) l1 d1 p1 v1
private theorem s1RunLast {c : List Rkm128kSeg} {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ}
    (h : s1RunAt c l0 d0 p0 v0 l1 d1 p1 v1 = true) :
    rkm128kRunSegs 256 4 512 c l0 d0 p0 v0 = (l1, d1, p1, v1) :=
  s1StateAt_eq h
private theorem s1RunStep {c rest : List Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 l2 d2 p2 : ℕ} {v0 v1 v2 : List ℤ}
    (h1 : s1RunAt c l0 d0 p0 v0 l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 256 4 512 rest l1 d1 p1 v1 = (l2, d2, p2, v2)) :
    rkm128kRunSegs 256 4 512 (c ++ rest) l0 d0 p0 v0 = (l2, d2, p2, v2) := by
  unfold s1RunAt at h1; rw [rkm128kRunSegs_append]; dsimp only
  rw [s1StateAt_eq h1]; exact h2
private def s1Take (n : ℕ) (xs : List Rkm128kSeg) : List Rkm128kSeg :=
  match n with
  | 0 => []
  | k + 1 =>
    match xs with
    | [] => []
    | x :: xr => x :: s1Take k xr
private def s1Drop (n : ℕ) (xs : List Rkm128kSeg) : List Rkm128kSeg :=
  match n with
  | 0 => xs
  | k + 1 =>
    match xs with
    | [] => []
    | _ :: xr => s1Drop k xr
private theorem s1Take_drop (n : ℕ) (xs : List Rkm128kSeg) :
    s1Take n xs ++ s1Drop n xs = xs := by
  induction n generalizing xs with
  | zero => cases xs <;> rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xr => exact congrArg (List.cons x) (ih xr)
private theorem s1RunStepTd {xs : List Rkm128kSeg} {n : ℕ}
    {l0 d0 p0 l1 d1 p1 l2 d2 p2 : ℕ} {v0 v1 v2 : List ℤ}
    (h1 : s1RunAt (s1Take n xs) l0 d0 p0 v0 l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 256 4 512 (s1Drop n xs) l1 d1 p1 v1 = (l2, d2, p2, v2)) :
    rkm128kRunSegs 256 4 512 xs l0 d0 p0 v0 = (l2, d2, p2, v2) := by
  rw [← s1Take_drop n xs]
  exact s1RunStep h1 h2
private def s1Rem0 : List Rkm128kSeg := hm256k512krS1Segs
private def s1Chk0 : List Rkm128kSeg := s1Take 3 s1Rem0
private def s1Rem1 : List Rkm128kSeg := s1Drop 3 s1Rem0
private def s1St0VecS0 : List ℤ :=
  [s1N 4079362, s1P 9195415, s1P 5320510, s1P 4988438, s1N 13969315, s1P 20420393,
   s1P 89053306, s1P 105043462, s1P 18123919, s1N 77210247, s1N 68029606, s1P 34246307,
   s1N 8596821, s1P 39408865, s1N 8506358, s1N 24534802, s1P 42661748, s1P 45704425,
   s1P 212190603, s1P 253945681, s1P 210209583, s1P 31227445, s1N 167283889, s1N 70993460,
   s1P 44179239, s1N 1682800, s1P 116933789, s1P 30992529, s1N 271318766, s1N 46671788,
   s1N 73996174, s1N 287185182, s1P 84634076, s1P 106273730, s1P 219254336, s1P 102442899,
   s1N 61727709, s1P 12140122, s1P 152680886, s1P 73563018, s1P 108152714, s1P 387254788,
   s1P 1069754909, s1P 785104849, s1P 306007070, s1N 177922946, s1P 1132174219, s1P 1730133706,
   s1P 1118920344, s1P 11556099, s1P 483834400, s1P 568184829, s1P 3835073215, s1N 2823730248,
   s1N 5735774213, s1N 2094052424, s1N 3820264788, s1N 3006258452, s1N 3393654962,
   s1N 394795166, s1N 872783730, s1N 653948295, s1N 2990029722, s1P 1423315587]
private def s1St0VecS1 : List ℤ :=
  [s1P 1689285026, s1N 5866240118, s1P 606452569, s1N 948997045, s1P 2262444352,
   s1P 4185299880, s1P 156489154, s1P 6049346540, s1P 5837794194, s1N 5814297707,
   s1N 6601990109, s1N 11540529354, s1P 2075995525, s1N 3797528964, s1N 329601186,
   s1P 3947905764, s1P 6347561, s1N 3452756598, s1N 155011777, s1N 3585688219, s1N 750750038,
   s1P 589712173, s1N 1577957764, s1N 1679934519, s1P 3129194556, s1P 2108872907,
   s1N 652777385, s1N 2894831084, s1N 2637138963, s1N 2055534949, s1N 1948590770,
   s1N 2179918817, s1N 3134046146, s1N 1026590946, s1N 3378063500, s1N 2223901478,
   s1N 1380038430, s1P 2271391467, s1P 1613850411, s1P 4086791924, s1N 1769226472,
   s1P 1918118535, s1P 60749466, s1P 2962355027, s1P 13853582287, s1P 29623607751,
   s1P 46815925244, s1P 53516417845, s1P 44979156848, s1P 19348939907, s1N 17056299550,
   s1N 2078995463, s1N 12803148059, s1N 3314276814, s1P 2136293429, s1P 9346164847,
   s1P 7743762104, s1P 4265191432, s1P 3051786735, s1P 1618172076, s1P 5134678692,
   s1P 10755881627, s1P 19580947056, s1P 15514245502]
private def s1St0VecS2 : List ℤ :=
  [s1P 1733287214, s1P 3608425503, s1P 12188753375, s1P 5524946407, s1N 8544289971,
   s1N 4476566919, s1N 4939606721, s1N 3922885559, s1P 7073884914, s1P 10051429081,
   s1P 3150635108, s1P 5478249575, s1N 18096259370, s1N 20092621520, s1N 22425631481,
   s1P 6550376978, s1N 17480385768, s1N 13022379470, s1N 30669908961, s1N 793416251,
   s1N 14207015265, s1P 29031874679, s1P 9080057571, s1P 2384505279, s1P 19756106362,
   s1P 6279099754, s1N 5838849873, s1N 428898128, s1N 21601166891, s1P 3499202708,
   s1P 16313846405, s1P 10730864811, s1N 9423727387, s1N 12724255470, s1N 11947928258,
   s1N 17865677065, s1N 606259195, s1N 15780767149, s1P 737946744, s1P 2311416092,
   s1N 4078763489, s1N 8694584966, s1N 6435798464, s1N 10463463405, s1P 2789414851,
   s1N 14878228495, s1N 3146292618, s1P 6740425637, s1N 7827257684, s1N 12032641453,
   s1P 6278144898, s1P 8233956488, s1P 1177726887, s1N 6586912694, s1P 8555002965,
   s1P 18160998160, s1N 4101870186, s1P 7131937230, s1P 323102000, s1N 614947362,
   s1P 10657890228, s1P 49060844, s1N 2180492480, s1N 4664996569]
private def s1St0VecS3 : List ℤ :=
  [s1P 9940217510, s1P 15019232824, s1N 8632598836, s1P 4863040174, s1P 5396385683,
   s1P 6474301755, s1N 6055882530, s1P 16461727778, s1P 4526919938, s1P 5533244935,
   s1P 6558634997, s1P 12409297961, s1N 278809011, s1P 3631989664, s1P 6934947060,
   s1P 11692449088, s1N 6579774962, s1P 12561701870, s1N 10231508284, s1P 5245706751,
   s1N 8124202920, s1P 1382627211, s1N 7120314971, s1P 5738840980, s1N 19054517593,
   s1N 7368193181, s1P 18917567014, s1P 17846049847, s1P 7744155594, s1N 3285093637,
   s1N 9811847064, s1P 6097556723, s1N 3944293688, s1P 6791411032, s1P 19417015096,
   s1N 19555177144, s1N 8636010958, s1N 9478485696, s1N 21733877607, s1P 23200786630,
   s1N 8398738369, s1P 4745472851, s1N 23498147829, s1N 3645907817, s1P 6400893883,
   s1P 3636030603, s1P 28411374108, s1N 10237590401, s1P 43792748193, s1N 47922606269,
   s1N 6033229772, s1P 39265113162, s1N 22477120523, s1P 50814666164, s1N 15731874550,
   s1N 36263230362, s1N 30185466101, s1N 33195114081, s1N 85357153846, s1N 156751175691,
   s1N 312622851123, s1N 538483555509, s1N 865994759935, s1N 1403441315192]
private def s1St0VecS4 : List ℤ :=
  [s1N 2209626301959, s1N 3346498530203, s1N 4978394468251, s1N 7279063056150,
   s1N 10374364039771, s1N 14445634861949, s1N 19746690421941, s1N 26489077777154,
   s1N 34816826387167, s1N 44876609262566, s1N 56805254299923, s1N 70640417089361,
   s1N 86289634331779, s1N 103561179586611, s1N 122171911431881, s1N 141727300222066,
   s1N 161719268933677, s1N 181545073689394, s1N 200534870116507, s1N 217998209240843,
   s1N 233282643752473, s1N 245809739549196, s1N 255085105495570, s1N 260722411686436,
   s1N 262494992199482, s1N 260371930699397, s1N 254503013144413, s1N 245177472008274,
   s1N 232801393262849, s1N 217893348422542, s1N 201060724020021, s1N 182942912961647,
   s1N 164152577251477, s1N 145248988811153, s1N 126738515965782, s1N 109070031184677,
   s1N 92608379250961, s1N 77602972992952, s1N 64180236300910, s1N 52368590196005,
   s1N 42137888695422, s1N 33427931712182, s1N 26155259328975, s1N 20206647651031,
   s1N 15435275766065, s1N 11669105445610, s1N 8729517505302, s1N 6451268413792,
   s1N 4695521464467, s1N 3353051936360, s1N 2339936621001, s1N 1590281056340,
   s1N 1049810749626, s1N 672050176491, s1N 416928601338, s1N 250737033897, s1N 146350851699,
   s1N 83082162509, s1N 46012268386, s1N 24958586765, s1N 13324870399, s1N 7040756526,
   s1N 3703489321, s1N 1949640731]
private def s1St0VecS5 : List ℤ :=
  [s1N 1031304362, s1N 549228225, s1N 294366105, s1N 158397883, s1N 85257291, s1N 45711117,
   s1N 24315610, s1N 12788735, s1N 6632124, s1N 3384157, s1N 1696493, s1N 834593, s1N 402600,
   s1N 190329, s1N 88132, s1N 39955, s1N 17721, s1N 7679, s1N 3245, s1N 1330, s1N 524, s1N 194,
   s1N 65, s1N 17, s1N 3, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0]
private def s1St0VecS6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St0VecS7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St0VecS8 : List ℤ :=
  [s1P 0]
private def s1St0Vec : List ℤ :=
  s1St0VecS0 ++
  (s1St0VecS1 ++
  (s1St0VecS2 ++
  (s1St0VecS3 ++
  (s1St0VecS4 ++
  (s1St0VecS5 ++
  (s1St0VecS6 ++
  (s1St0VecS7 ++
  (s1St0VecS8))))))))
private def s1Chk1 : List Rkm128kSeg := s1Take 3 s1Rem1
private def s1Rem2 : List Rkm128kSeg := s1Drop 3 s1Rem1
private def s1St1VecS0 : List ℤ :=
  [s1N 1571620, s1N 8559235, s1N 820742, s1N 854935, s1N 4588382, s1N 13527293, s1N 50252241,
   s1N 50018443, s1N 32928378, s1P 36223127, s1P 12947703, s1N 38058638, s1P 78071509,
   s1N 104071598, s1P 72564165, s1P 68053368, s1P 21268889, s1P 2607790, s1P 17448797,
   s1P 36195063, s1N 17101933, s1N 74184847, s1P 16409030, s1P 22358014, s1N 60833029,
   s1N 197718602, s1N 270682535, s1N 187385659, s1N 327054991, s1N 153776125, s1N 125809884,
   s1P 68961265, s1P 119148187, s1P 84255570, s1P 264641885, s1N 69778499, s1N 32149904,
   s1N 99890597, s1N 146000175, s1N 65675634, s1N 77395365, s1P 120172779, s1N 385908841,
   s1N 48249151, s1P 462877830, s1N 129386916, s1P 152123143, s1P 118104096, s1P 143490265,
   s1N 366879232, s1N 542769901, s1N 1243593016, s1N 1500588949, s1N 2380207516,
   s1N 2580558839, s1N 1200562149, s1N 1453917164, s1P 506219868, s1P 6219823376,
   s1P 1511456273, s1P 1773147632, s1P 3512733973, s1N 382557619, s1P 1365127009]
private def s1St1VecS1 : List ℤ :=
  [s1N 484847377, s1N 1495624995, s1P 4824191123, s1P 3720945832, s1P 4286750066,
   s1P 5082619519, s1N 609767174, s1P 1651309367, s1N 1237403396, s1P 2065035625,
   s1N 6497489580, s1P 3109712243, s1P 7165881394, s1P 7577270460, s1P 7824896638,
   s1P 8420205335, s1N 1443982306, s1N 1587877925, s1N 5362832158, s1N 3721603671,
   s1N 1835704153, s1P 746228435, s1N 3111018038, s1P 2958261344, s1N 749123960,
   s1P 1952609534, s1P 2059027120, s1P 2266750426, s1P 818774720, s1N 1311757553,
   s1P 1598599459, s1P 2388591290, s1P 856267666, s1P 2108883198, s1P 620930765,
   s1N 1441136180, s1N 1719868618, s1P 288349416, s1N 907036893, s1P 577615566, s1N 2548278657,
   s1N 1762693004, s1N 636934813, s1P 4685464192, s1P 4372113381, s1P 5202224788,
   s1P 6759335480, s1P 6837426073, s1P 1916459064, s1P 1944264844, s1N 294919815,
   s1N 1095523769, s1P 466028323, s1P 558381995, s1P 19664263741, s1P 2544141684,
   s1P 3427695331, s1N 38802883, s1P 1456566321, s1N 9323010533, s1N 40045141941,
   s1N 55267817710, s1N 50819438198, s1N 32119729888]
private def s1St1VecS2 : List ℤ :=
  [s1N 10002580555, s1N 11291267221, s1P 1268873198, s1N 6021227217, s1N 13830501805,
   s1N 14583496052, s1N 11287772384, s1P 7975116665, s1N 5094972189, s1N 9306475272,
   s1N 9167599919, s1N 6170209211, s1P 22282766406, s1N 8000670163, s1P 6652863925,
   s1P 11767076312, s1P 17553990746, s1P 1143137104, s1P 15268488610, s1P 341120651,
   s1P 17043797475, s1P 13450049436, s1N 1058971772, s1P 6201091182, s1P 41895287878,
   s1P 19049144159, s1P 6802627861, s1P 5072708978, s1P 12222341617, s1P 12409625911,
   s1P 27347668184, s1P 12503362814, s1P 14193612449, s1P 6110919301, s1N 13325655515,
   s1P 1722267781, s1N 1435293137, s1P 10599358547, s1P 22446569704, s1P 10551575492,
   s1P 5981973811, s1N 6655612503, s1P 3898595823, s1P 6565936081, s1N 6899146349,
   s1P 869762646, s1P 13350873073, s1N 2349475002, s1N 16568677061, s1P 6516163384,
   s1N 4179077910, s1P 22352846021, s1N 4253010484, s1P 1524766884, s1P 11991224709,
   s1P 2296422180, s1N 308325510, s1P 5595400590, s1N 5448292204, s1N 581868361,
   s1P 2778896376, s1P 16887923216, s1P 12932566040, s1P 8771654058]
private def s1St1VecS3 : List ℤ :=
  [s1N 1683513994, s1N 2757927619, s1N 12120345103, s1N 4285518231, s1P 3225594060,
   s1N 11145582942, s1P 6980089617, s1N 4254534933, s1P 9385961606, s1P 2408405177,
   s1P 3878327075, s1P 5799035030, s1N 6745079208, s1P 12264976163, s1P 10520126118,
   s1P 6622293974, s1N 8221917685, s1N 15125591049, s1P 6177786365, s1P 3963553699,
   s1P 4356092642, s1P 16787628923, s1P 1711733439, s1P 1471871154, s1P 4311485485,
   s1N 16369039765, s1P 6943589918, s1N 2058500545, s1N 10651171668, s1N 2745086812,
   s1P 832445645, s1N 5011190194, s1P 5294580471, s1P 3659800726, s1P 997159760,
   s1N 5383163934, s1N 16475385763, s1N 58146717029, s1N 26476387292, s1P 30696208916,
   s1P 28188863839, s1P 887863063, s1N 35777184487, s1N 19318476838, s1P 27888000282,
   s1P 6674035579, s1N 37785207749, s1N 14190114393, s1P 7696109780, s1N 12801374801,
   s1P 11412600775, s1N 10252429429, s1P 4797627764, s1P 27232777883, s1P 1162920593,
   s1P 1219130901, s1P 4261372851, s1N 15253689440, s1P 35301288580, s1P 31406469133,
   s1N 10524831942, s1P 4943069919, s1P 27142826460, s1N 25572260206]
private def s1St1VecS4 : List ℤ :=
  [s1N 17384814077, s1N 6555761883, s1N 2171681115, s1P 1119515651, s1P 17219201309,
   s1N 26019856142, s1N 2396377593, s1P 28812504365, s1P 21776933850, s1P 20410214890,
   s1P 66160141634, s1P 127157632851, s1P 255810412548, s1P 494117014188, s1P 874204907427,
   s1P 1460602771368, s1P 2364953134643, s1P 3729785321061, s1P 5717447353269,
   s1P 8511371244055, s1P 12321517249572, s1P 17389740922790, s1P 23978407884255,
   s1P 32330256851208, s1P 42626888232629, s1P 54980113218724, s1P 69437628722386,
   s1P 85956537452500, s1P 104349136687493, s1P 124257179420890, s1P 145180076633657,
   s1P 166517233154698, s1P 187583847620763, s1P 207617841215514, s1P 225820959604077,
   s1P 241434901913636, s1P 253809429010732, s1P 262434340545755, s1P 266953282494525,
   s1P 267188869300122, s1P 263174995912383, s1P 255163808327484, s1P 243589253873422,
   s1P 229007191445637, s1P 212045129010905, s1P 193379489334199, s1P 173707927019329,
   s1P 153739109996999, s1P 134074543281559, s1P 115313925809856, s1P 97689262890508,
   s1P 81740347736672, s1P 67187317804167, s1P 54663541325261, s1P 43655043462336,
   s1P 34388785945928, s1P 26878050972624, s1P 20599750364181, s1P 15566588389645,
   s1P 11784617905628, s1P 8742722064176, s1P 6317420811598, s1P 4429020718869,
   s1P 3178152780860]
private def s1St1VecS5 : List ℤ :=
  [s1P 2324790932980, s1P 1565721470548, s1P 902418946863, s1P 449095541636, s1P 212425506198,
   s1P 111807077609, s1P 70004612423, s1P 47390066937, s1P 31327776988, s1P 19494949802,
   s1P 11427594204, s1P 6388769727, s1P 3453612933, s1P 1826491573, s1P 953516365,
   s1P 494410728, s1P 255570151, s1P 131916212, s1P 67987062, s1P 34941302, s1P 17871243,
   s1P 9075003, s1P 4564409, s1P 2268934, s1P 1112623, s1P 537388, s1P 255330, s1P 119217,
   s1P 54655, s1P 24580, s1P 10828, s1P 4665, s1P 1956, s1P 793, s1P 306, s1P 111, s1P 34,
   s1P 9, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0]
private def s1St1VecS6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St1VecS7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St1VecS8 : List ℤ :=
  [s1P 0]
private def s1St1Vec : List ℤ :=
  s1St1VecS0 ++
  (s1St1VecS1 ++
  (s1St1VecS2 ++
  (s1St1VecS3 ++
  (s1St1VecS4 ++
  (s1St1VecS5 ++
  (s1St1VecS6 ++
  (s1St1VecS7 ++
  (s1St1VecS8))))))))
private def s1Chk2 : List Rkm128kSeg := s1Take 3 s1Rem2
private def s1Rem3 : List Rkm128kSeg := s1Drop 3 s1Rem2
private def s1St2VecS0 : List ℤ :=
  [s1P 345645, s1P 1213593, s1P 3123584, s1P 6907480, s1P 7109976, s1N 6415971, s1N 2220502,
   s1P 15151286, s1N 643229, s1N 4640659, s1P 10800975, s1P 10458713, s1P 126246396,
   s1N 120108003, s1N 14139518, s1N 1319625, s1N 18457108, s1N 44264698, s1P 6365203,
   s1P 21488532, s1N 40681479, s1N 13650842, s1N 35244835, s1P 50202877, s1P 38174245,
   s1P 105495682, s1N 44832848, s1N 8566083, s1P 11934110, s1N 50414999, s1N 80067332,
   s1N 204865838, s1N 313113998, s1P 49748743, s1P 95322679, s1N 98100071, s1N 329383925,
   s1P 98166721, s1N 397529433, s1P 73032164, s1P 292498121, s1N 109891132, s1P 175170186,
   s1P 113161137, s1P 11392486, s1P 14254443, s1P 463683975, s1N 192675534, s1N 312026936,
   s1P 59974494, s1P 40270402, s1P 99214482, s1N 456946548, s1N 102942713, s1P 79393467,
   s1P 114654708, s1P 5141856, s1P 270699855, s1N 191135274, s1N 153454220, s1N 244400765,
   s1N 876312937, s1N 2607973732, s1N 4259406198]
private def s1St2VecS1 : List ℤ :=
  [s1N 4876997666, s1P 330876393, s1P 5032252062, s1N 361069914, s1N 3471550971,
   s1N 4317088203, s1P 3355586012, s1P 644394599, s1P 1419216468, s1P 2465918335,
   s1N 5661636267, s1N 3155807608, s1N 2908195047, s1N 4372488455, s1P 8939764878,
   s1P 1203824201, s1P 6449187559, s1P 8114647483, s1P 1794678241, s1N 1173251826,
   s1P 7802045930, s1P 3793109346, s1P 655122041, s1P 4222419840, s1N 263782504,
   s1N 5555086817, s1P 3919355509, s1P 3683543338, s1N 794288429, s1N 1683613750,
   s1N 502982543, s1N 1708814038, s1N 1060696798, s1N 1139804041, s1N 2164662200,
   s1N 2051668823, s1N 457041026, s1P 947515572, s1P 108723970, s1N 1940763397, s1N 1782580236,
   s1N 3647344053, s1N 3355753617, s1N 1147306435, s1P 2193439033, s1P 874277023,
   s1P 2337553689, s1P 5108661714, s1P 6549445097, s1P 5583759686, s1P 3581068655,
   s1N 4704908619, s1N 11001554640, s1N 5185847460, s1N 3266520145, s1P 10636313520,
   s1P 8294246057, s1P 1322076873, s1P 20656020490, s1P 10605999512, s1N 13998393970,
   s1N 5251213998, s1P 6102194774, s1N 4340985788]
private def s1St2VecS2 : List ℤ :=
  [s1N 13932832653, s1N 1194761855, s1N 1495725381, s1N 12443238105, s1P 14218599858,
   s1N 11180046249, s1P 5446263605, s1P 4984656014, s1P 14540643448, s1P 1565776593,
   s1N 29886320293, s1N 20374711366, s1N 9022693739, s1P 55141715984, s1P 64854820472,
   s1P 15556013701, s1P 21050560149, s1P 10281921697, s1P 2251729132, s1N 3677040446,
   s1P 876499655, s1P 11001966303, s1P 18858449417, s1N 12817535879, s1N 17182346294,
   s1P 6636299193, s1N 13894238204, s1P 21801231014, s1P 4352587035, s1P 4456975086,
   s1P 14172052759, s1N 8331061843, s1N 1547254756, s1N 19495449773, s1P 19948843783,
   s1N 16530379568, s1N 23786809033, s1N 10557539508, s1P 14349868291, s1N 5463168920,
   s1P 2051909593, s1P 14921394507, s1N 1192369203, s1P 14329525847, s1P 12190581672,
   s1N 18746593321, s1P 8334934719, s1N 738404969, s1N 15094304430, s1P 3319640265,
   s1P 963740351, s1N 12097630623, s1P 14453401652, s1P 2234984440, s1P 845229356,
   s1N 2268080538, s1N 5413702278, s1N 8689653790, s1P 10815294324, s1N 8870993625,
   s1P 9049837246, s1P 12908329668, s1N 10858900165, s1N 220278184]
private def s1St2VecS3 : List ℤ :=
  [s1P 1342061235, s1P 4281903525, s1N 803376463, s1N 5366382167, s1P 4856534497,
   s1N 1461467056, s1N 6728095071, s1P 6470533129, s1N 12893709085, s1N 7314486658,
   s1N 2168943934, s1P 7507698661, s1N 3603576443, s1N 17740605784, s1P 15079571698,
   s1P 16036551750, s1P 15769066084, s1N 249135074, s1P 6892721962, s1N 7762582243,
   s1P 11407760741, s1N 5948592607, s1P 3908855328, s1P 8561034742, s1P 18484365600,
   s1N 8798770976, s1N 12333470175, s1P 8371374242, s1N 2913292930, s1P 5343119887,
   s1P 3484463096, s1N 12063284525, s1N 3905935222, s1N 13404190579, s1P 11913973625,
   s1P 14114641922, s1N 2942506277, s1P 3517367982, s1N 24603399910, s1N 24346810583,
   s1P 9074193024, s1P 9836955028, s1N 20954787053, s1N 25369061986, s1N 30470106144,
   s1P 2631669556, s1N 23122852182, s1N 597924255, s1N 18313355736, s1P 12208321519,
   s1N 34148463894, s1N 9779900563, s1P 36247241778, s1P 44489541927, s1P 52439273129,
   s1N 3681859229, s1P 267525908, s1P 4958805226, s1N 25214923305, s1P 29507952751,
   s1P 11741540669, s1P 11436840096, s1P 11815578428, s1N 5948592628]
private def s1St2VecS4 : List ℤ :=
  [s1N 16545158352, s1P 167990764, s1P 21989728283, s1N 10296289542, s1P 12316038613,
   s1N 8688426706, s1P 6143829712, s1N 18657989575, s1N 19039471179, s1N 25767243322,
   s1P 8745759234, s1P 6222045856, s1N 5233079582, s1P 5522086821, s1P 18143250350,
   s1P 4488576201, s1P 13617576641, s1P 8115581222, s1N 2359654788, s1N 5567837608,
   s1P 501286329, s1P 3003561509, s1P 6694646363, s1N 14316813854, s1P 4390016730,
   s1N 9995159508, s1P 9066642525, s1N 9963208441, s1N 26160667288, s1N 67562002407,
   s1N 159524732268, s1N 410746415307, s1N 790475531806, s1N 1508585095065, s1N 2510963924852,
   s1N 4284130260064, s1N 6703231967471, s1N 10426066526995, s1N 15319872809642,
   s1N 22035148925601, s1N 30716584457857, s1N 41575366711358, s1N 54983836287436,
   s1N 70718832261404, s1N 88851848310645, s1N 109220027465782, s1N 131054613690783,
   s1N 154067549259569, s1N 177313385552115, s1N 199820018288305, s1N 220898340835796,
   s1N 239499060190979, s1N 254662818958886, s1N 265809485001570, s1N 272464464480727,
   s1N 274258283039008, s1N 271221345633106, s1N 263713612509454, s1N 252086449554343,
   s1N 236789725953550, s1N 218759222289024, s1N 198848944177755, s1N 177982209801042,
   s1N 156457925089365]
private def s1St2VecS5 : List ℤ :=
  [s1N 135732170970711, s1N 115667889036474, s1N 97347730366359, s1N 80454568928131,
   s1N 65244603478704, s1N 52441942869605, s1N 41549170910876, s1N 32257450896623,
   s1N 24759500912779, s1N 18836848870933, s1N 13961800394517, s1N 10215425357271,
   s1N 7428252499940, s1N 5470866111482, s1N 3979322280291, s1N 2641757657192,
   s1N 1512495671525, s1N 747413047240, s1N 341451298147, s1P 166271952823, s1P 97240702856,
   s1N 65340362487, s1N 44980567848, s1N 29837979598, s1N 18817399063, s1N 11328887429,
   s1N 6559598871, s1N 3676759838, s1N 2005317871, s1N 1068685924, s1N 558536651,
   s1N 287219794, s1N 145743869, s1N 73147531, s1N 36372442, s1N 17935677, s1N 8772688,
   s1N 4254504, s1N 2044099, s1N 971868, s1N 456690, s1N 211831, s1N 96864, s1N 43612,
   s1N 19305, s1N 8387, s1N 3565, s1N 1474, s1N 590, s1N 222, s1N 77, s1N 22, s1N 5, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St2VecS6 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St2VecS7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St2VecS8 : List ℤ :=
  [s1P 0]
private def s1St2Vec : List ℤ :=
  s1St2VecS0 ++
  (s1St2VecS1 ++
  (s1St2VecS2 ++
  (s1St2VecS3 ++
  (s1St2VecS4 ++
  (s1St2VecS5 ++
  (s1St2VecS6 ++
  (s1St2VecS7 ++
  (s1St2VecS8))))))))
private def s1Chk3 : List Rkm128kSeg := s1Take 3 s1Rem3
private def s1Rem4 : List Rkm128kSeg := s1Drop 3 s1Rem3
private def s1St3VecS0 : List ℤ :=
  [s1P 707634, s1P 769826, s1N 332913, s1P 43726, s1P 2889206, s1P 3277170, s1P 13901064,
   s1P 7805075, s1P 10808156, s1N 5099134, s1N 3274255, s1N 5041816, s1N 17865696, s1N 8604323,
   s1P 19061163, s1P 115183056, s1P 125813695, s1N 29079235, s1N 61299109, s1P 27966285,
   s1P 6208690, s1P 4874966, s1P 14654775, s1P 35582680, s1N 15248739, s1P 80396163,
   s1P 28133553, s1P 20514314, s1P 43419947, s1P 57761210, s1P 85692475, s1P 204145302,
   s1P 54476685, s1P 94316655, s1P 135411141, s1P 218073250, s1P 262181773, s1P 284929571,
   s1P 207711829, s1P 458559321, s1P 35757312, s1N 66020858, s1N 18045697, s1P 50668977,
   s1P 169161643, s1N 336467782, s1P 10650830, s1P 328726265, s1N 268719864, s1N 220357094,
   s1N 72094257, s1N 131999414, s1P 241183644, s1P 61336418, s1N 125895736, s1N 203677530,
   s1P 212946325, s1P 404821639, s1P 119403956, s1N 132686273, s1P 229314716, s1N 7591249,
   s1P 531729149, s1P 226337127]
private def s1St3VecS1 : List ℤ :=
  [s1P 114518204, s1P 59493892, s1P 518008071, s1P 553819636, s1P 622769153, s1N 272360093,
   s1N 1858310221, s1N 2053817726, s1N 2208822891, s1N 1889869275, s1P 90583175,
   s1P 6934079383, s1P 10680594685, s1P 1425865459, s1N 7166998932, s1N 6492436563,
   s1N 5061789246, s1P 650246467, s1N 1335180339, s1N 6073418096, s1N 4297842746,
   s1N 2432989237, s1N 2816014407, s1P 416542343, s1P 10986908846, s1P 2214863742,
   s1N 1669241236, s1N 3051220227, s1P 254753199, s1N 2963835268, s1N 2315801784,
   s1N 3676673960, s1N 1192897863, s1N 447538028, s1P 333583338, s1P 1823080658,
   s1P 1398439716, s1N 2680565645, s1N 870991917, s1P 1432408758, s1N 612699725,
   s1P 1746597656, s1N 824491904, s1N 1027416885, s1P 1603055749, s1P 929021188, s1P 680522237,
   s1P 3231871200, s1P 3852237857, s1P 6133780398, s1P 1894024344, s1N 3643675224,
   s1P 1795624078, s1P 5239237358, s1P 8373332179, s1P 11931686325, s1P 14432556544,
   s1P 8793190807, s1P 11003646237, s1P 12330490995, s1N 5241192881, s1N 10349864326,
   s1N 5355544417, s1N 9024002218]
private def s1St3VecS2 : List ℤ :=
  [s1N 15088488194, s1N 4309402210, s1P 1596619062, s1P 8168395796, s1P 6044020858,
   s1P 15851613014, s1P 7796987468, s1P 8876914274, s1P 15763933430, s1N 3318080523,
   s1N 19050747490, s1N 9303200935, s1N 25538364879, s1N 2309165392, s1P 22665928438,
   s1P 21489857482, s1N 15079667017, s1N 17037531003, s1P 13862613042, s1P 2596472827,
   s1N 23304105084, s1P 5891202188, s1P 2713516365, s1P 4474965770, s1N 2269867265,
   s1P 9024332162, s1P 6396687677, s1P 12771012408, s1P 23488477621, s1P 33916181627,
   s1P 29674973070, s1P 36158407261, s1P 37515164175, s1P 9629880757, s1P 28597525855,
   s1P 33166813826, s1P 31821882216, s1P 29455384046, s1N 2590772910, s1N 8706567703,
   s1N 3363581421, s1P 680648751, s1P 3017549180, s1P 859656125, s1P 4940640988,
   s1N 19847358187, s1N 22414619551, s1N 9376533602, s1N 10562153849, s1N 6836255244,
   s1N 17226137235, s1N 20172537055, s1N 16844704513, s1P 1535648149, s1P 5163724867,
   s1P 7772754036, s1P 4260405591, s1N 17424674885, s1N 4596564823, s1N 3200492851,
   s1N 3927552945, s1P 10592252619, s1P 5253173028, s1N 4505822741]
private def s1St3VecS3 : List ℤ :=
  [s1P 1879547713, s1P 2694134308, s1P 6804771957, s1P 2610854429, s1P 10761664310,
   s1N 1126307069, s1P 2845846579, s1N 4888399209, s1N 3569795945, s1N 3331799809,
   s1N 5033959695, s1P 11522573734, s1N 1664037035, s1P 3360876670, s1N 6740824079,
   s1P 15154279569, s1P 8743642204, s1P 6657255682, s1P 6728703531, s1P 15272184300,
   s1P 21491719498, s1P 2203034792, s1N 9207459945, s1N 1796877216, s1N 7519772928,
   s1N 12691542336, s1P 6600247606, s1P 5607897587, s1P 826960800, s1N 3595367135,
   s1N 20720160932, s1P 23161987673, s1P 21734196519, s1P 8533866064, s1P 19428905942,
   s1N 12221142500, s1N 11896462168, s1P 8953383378, s1N 13491919203, s1N 3073896608,
   s1N 10817129304, s1N 515694882, s1N 10045862805, s1N 17968052659, s1P 9803633253,
   s1N 25539868832, s1N 4540097581, s1N 3206601386, s1P 6857069065, s1N 5760799696,
   s1P 5376179018, s1P 32197469467, s1P 29340864614, s1N 22909581679, s1P 52605661455,
   s1N 4567031877, s1P 3272962630, s1N 665029694, s1P 13812083054, s1P 7372913385,
   s1P 19700629543, s1N 32717478954, s1P 22042194754, s1P 16220912669]
private def s1St3VecS4 : List ℤ :=
  [s1P 32816616167, s1P 20905723925, s1P 18540002481, s1P 28805459123, s1P 40777384492,
   s1P 3322236278, s1N 19024323492, s1P 13375493681, s1P 1247506962, s1N 11805728117,
   s1P 11835130, s1P 9621282240, s1P 12889536505, s1P 10247788920, s1P 8256880243,
   s1P 8957944346, s1N 815961913, s1N 7849311386, s1N 2214720170, s1P 25642932119,
   s1P 25590296074, s1N 5050711470, s1P 2434804031, s1P 10444862269, s1P 16596868663,
   s1N 7572842495, s1N 16115051571, s1P 29340608870, s1P 49405105705, s1N 58818285401,
   s1N 44780454623, s1N 48186945089, s1N 26890456376, s1N 22749960794, s1P 37193244153,
   s1P 1084053995, s1N 4777552693, s1N 43117803253, s1P 35224587126, s1P 20939771993,
   s1N 22178320380, s1P 66956068722, s1N 42996616783, s1N 6918946676, s1P 66943023383,
   s1P 61517523684, s1P 84181104059, s1N 80090095251, s1P 66665497966, s1P 86059024641,
   s1P 517519761642, s1P 1060850118581, s1P 1985000451346, s1P 3884537780190,
   s1P 6436498730241, s1P 10343241329278, s1P 15969062504168, s1P 23450883751079,
   s1P 33303005527698, s1P 45778873983350, s1P 60878223537721, s1P 78877711525257,
   s1P 99221335827300, s1P 121463554182347]
private def s1St3VecS5 : List ℤ :=
  [s1P 145524213003697, s1P 170147752907257, s1P 194262069505135, s1P 216950536713096,
   s1P 237545510600427, s1P 254487807908178, s1P 267174944585696, s1P 275246224663268,
   s1P 278081694277399, s1P 276084481108517, s1P 268553976661305, s1P 257010197627212,
   s1P 241327196552633, s1P 223060911130870, s1P 202412055910726, s1P 180690842461811,
   s1P 159088574236376, s1P 137304141504375, s1P 116426054368456, s1P 97631573667377,
   s1P 80561410200997, s1P 65154353394096, s1P 52027208644459, s1P 41106907477809,
   s1P 31804080302517, s1P 24018876870179, s1P 18004189484180, s1P 13635060882703,
   s1P 10337597264345, s1P 7580809453166, s1P 5189223320820, s1P 3242771062151,
   s1P 1834344960064, s1P 942207561508, s1P 447342487807, s1P 205350859902, s1P 99303579049,
   s1P 55596731613, s1P 36414902195, s1P 25772113456, s1P 18246461308, s1P 12452928748,
   s1P 8108154100, s1P 5041069359, s1P 3006496919, s1P 1729105471, s1P 963697354,
   s1P 522734873, s1P 276966135, s1P 143782429, s1P 73320717, s1P 36804464, s1P 18216246,
   s1P 8901538, s1P 4298556, s1P 2052503, s1P 969315, s1P 452747, s1P 209088, s1P 95428,
   s1P 43011, s1P 19122, s1P 8372, s1P 3600]
private def s1St3VecS6 : List ℤ :=
  [s1P 1513, s1P 619, s1P 240, s1P 88, s1P 28, s1P 7, s1P 1, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St3VecS7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St3VecS8 : List ℤ :=
  [s1P 0]
private def s1St3Vec : List ℤ :=
  s1St3VecS0 ++
  (s1St3VecS1 ++
  (s1St3VecS2 ++
  (s1St3VecS3 ++
  (s1St3VecS4 ++
  (s1St3VecS5 ++
  (s1St3VecS6 ++
  (s1St3VecS7 ++
  (s1St3VecS8))))))))
private def s1Chk4 : List Rkm128kSeg := s1Take 2 s1Rem4
private def s1Rem5 : List Rkm128kSeg := s1Drop 2 s1Rem4
private def s1St4VecS0 : List ℤ :=
  [s1P 155519, s1P 373289, s1P 3348401, s1P 2919944, s1P 849355, s1P 3602697, s1P 2132797,
   s1N 3397161, s1P 8756878, s1N 1427072, s1N 13770934, s1N 9436641, s1P 12554403,
   s1P 18266053, s1N 4681243, s1P 12575261, s1N 21648967, s1P 4001222, s1P 25539188,
   s1P 63601401, s1P 98475646, s1P 110899795, s1P 82982640, s1P 76561300, s1P 71450777,
   s1P 22714819, s1N 12340023, s1P 11782997, s1P 6830016, s1P 38358075, s1N 35362997,
   s1P 28551520, s1P 141863814, s1P 53995103, s1P 203295824, s1P 218013185, s1P 74093259,
   s1P 45874352, s1P 13463895, s1P 168607216, s1P 172667753, s1N 181825847, s1N 78972124,
   s1N 133779715, s1P 12449032, s1N 42999238, s1P 443417938, s1P 522987635, s1P 395251659,
   s1N 13261508, s1N 205701964, s1N 213220499, s1N 346325595, s1P 22621441, s1P 390849879,
   s1P 186520859, s1N 76017946, s1N 148620842, s1N 373164608, s1N 31841447, s1P 85211386,
   s1P 157266867, s1N 313365217, s1P 157885227]
private def s1St4VecS1 : List ℤ :=
  [s1P 311664189, s1P 194921021, s1P 5292771, s1P 504464110, s1P 374062461, s1P 67991056,
   s1P 458899159, s1P 128082862, s1P 364767186, s1N 697085915, s1N 792349305, s1N 825421021,
   s1P 60145092, s1P 113709311, s1P 826285659, s1P 2170928964, s1P 4173505759, s1P 3800589109,
   s1N 2110396444, s1N 6498699311, s1N 7434487589, s1N 2686888448, s1P 3961226086,
   s1P 6663564283, s1P 7401029818, s1P 4562455749, s1N 2876705501, s1N 2595503733,
   s1P 4703902897, s1P 9125961045, s1N 968534718, s1N 1808387666, s1N 7220898128,
   s1N 6296466796, s1P 2829418782, s1P 935600955, s1N 1318055889, s1N 3115764375,
   s1N 3998136202, s1N 1506186007, s1N 2955503455, s1P 1299491332, s1P 256994313,
   s1N 1109731912, s1P 802054903, s1P 1993520011, s1P 3617509015, s1P 432410026, s1P 495675951,
   s1N 698671619, s1N 1895423574, s1N 1150503801, s1N 836592757, s1N 478965321, s1P 1346082027,
   s1P 4199553010, s1P 1365354345, s1P 2698379849, s1P 782395713, s1N 2988621208,
   s1N 2403280166, s1N 4912693926, s1N 10514842041, s1N 7453996783]
private def s1St4VecS2 : List ℤ :=
  [s1N 9651623883, s1N 11632229022, s1N 16223271978, s1N 4812590927, s1P 10975847989,
   s1P 18840434372, s1P 6698348877, s1P 1888852624, s1P 19115867060, s1P 27525319304,
   s1P 13417204804, s1N 12197188575, s1N 9620203161, s1P 27877766843, s1P 13873096407,
   s1N 5132870370, s1P 2615436328, s1P 8181449446, s1N 6998715489, s1P 985313646,
   s1N 9766846886, s1N 4426248102, s1P 6849973386, s1N 19911444819, s1N 22202918931,
   s1P 19240411444, s1P 6010490421, s1N 11970526501, s1N 13266830329, s1N 7694078076,
   s1P 1836237796, s1N 17506246003, s1N 5592137371, s1N 17516791063, s1N 25280138410,
   s1N 16274007225, s1P 8322936916, s1P 31015950631, s1P 10492133626, s1N 28738766643,
   s1P 5546278650, s1P 20185602940, s1P 18038876865, s1N 25164820527, s1P 5374286,
   s1P 9072109187, s1P 5794856032, s1N 7454755741, s1N 15684973053, s1N 30931887034,
   s1N 40883488857, s1N 24834425322, s1N 31333205155, s1N 24964010496, s1N 5775951598,
   s1N 4046769676, s1P 2994848552, s1P 19451133888, s1N 8378040315, s1P 7631502158,
   s1N 4953472549, s1N 4137533755, s1P 11094172992, s1P 8164124674]
private def s1St4VecS3 : List ℤ :=
  [s1P 15143595094, s1N 10924665890, s1N 21087060322, s1N 15195015697, s1N 5733205578,
   s1P 7325209351, s1P 6643736311, s1P 8164530177, s1N 4732753146, s1N 10464766095,
   s1N 9733560835, s1N 3106874154, s1P 3624335239, s1N 8577148823, s1N 2439199451,
   s1P 14907208436, s1N 4655358808, s1N 7580080893, s1P 4093538981, s1P 9644941068,
   s1N 15757113452, s1P 12361734677, s1P 17956267116, s1P 15300002703, s1P 6767041374,
   s1N 9440363054, s1N 9950061409, s1N 2721862141, s1P 10012785141, s1P 2684828414,
   s1N 1345632830, s1N 18758809491, s1P 13433122292, s1P 14034894956, s1N 20113765776,
   s1N 622842357, s1P 17403163428, s1P 12915733625, s1P 10483594898, s1P 25352710347,
   s1P 13317895417, s1N 6120097717, s1N 8225203544, s1N 20224882762, s1P 6868566124,
   s1N 8462103552, s1P 5697930923, s1P 19142532267, s1N 27077500004, s1P 14746061426,
   s1N 23398085772, s1P 1015722121, s1N 28010036809, s1P 12173197478, s1P 44731949269,
   s1P 11677692325, s1N 16629194636, s1N 11081198451, s1P 2440804877, s1P 24347752830,
   s1N 2790044854, s1N 6458753300, s1P 30543433183, s1P 20285710468]
private def s1St4VecS4 : List ℤ :=
  [s1P 5358618298, s1P 15137780483, s1P 36066702447, s1P 2279097532, s1P 4612936472,
   s1N 9450896166, s1N 12403793495, s1P 16514352188, s1N 25806881864, s1P 554019401,
   s1N 25545102362, s1N 26802978365, s1N 3708307547, s1N 29832003530, s1P 12881214644,
   s1N 23908848030, s1P 8481956802, s1P 30089885022, s1P 21465133660, s1N 670580425,
   s1N 6935011215, s1N 54854216607, s1N 51350956650, s1N 976368238, s1N 14489680646,
   s1P 13126332651, s1N 28524803687, s1N 31929618550, s1P 8191518951, s1N 5885105181,
   s1P 32390385764, s1P 5770458196, s1N 8619051444, s1N 21094702492, s1P 43142754722,
   s1P 11927941734, s1P 57506687194, s1P 44310810461, s1P 35557737187, s1N 17859056312,
   s1N 85247712573, s1N 50132875515, s1N 5827514501, s1N 12676301602, s1N 66541093959,
   s1P 23088438137, s1P 51652817177, s1P 32369797467, s1P 92123705168, s1P 18014871400,
   s1P 983257362, s1P 6399294406, s1P 88398392745, s1P 93857613050, s1P 45519302351,
   s1P 3305718876, s1N 78708358073, s1N 38064375855, s1N 245172732753, s1N 180757466731,
   s1N 72525026531, s1N 43547816247, s1N 9371046891, s1N 57882621146]
private def s1St4VecS5 : List ℤ :=
  [s1N 103565584013, s1N 216243992612, s1N 229407538942, s1N 658902478997, s1N 1617667372933,
   s1N 3431383474545, s1N 6306219679756, s1N 10929846681168, s1N 17271284620423,
   s1N 25900457337613, s1N 37667860701454, s1N 52164386918969, s1N 69402349533092,
   s1N 89968735451523, s1N 113117444625489, s1N 137745659881414, s1N 163535493153658,
   s1N 189550732973024, s1N 214051253743491, s1N 235982302221303, s1N 254787853750655,
   s1N 269351978523842, s1N 278534947082918, s1N 282090539200396, s1N 280261070385978,
   s1N 273167030357939, s1N 261133054638896, s1N 245058711415449, s1N 226030729485256,
   s1N 204872561345464, s1N 182305307995221, s1N 159319873210247, s1N 136957759079772,
   s1N 116098326039944, s1N 96746101985514, s1N 79478951937735, s1N 63597311933391,
   s1N 50436771425554, s1N 39264055322572, s1N 30128756430674, s1N 23412296849357,
   s1N 17793882350988, s1N 12892811542789, s1N 9264644592468, s1N 6678047497744,
   s1N 4508122169218, s1N 2637651558687, s1N 1285676427493, s1N 522173726267, s1N 189943547749,
   s1N 78970976616, s1N 48747388969, s1N 37966424832, s1N 29450351479, s1N 21368941586,
   s1N 14600865278, s1N 9539982154, s1N 6021753025, s1N 3689762004, s1N 2198754649,
   s1N 1275340683, s1N 720629957, s1N 397128512, s1N 213746947]
private def s1St4VecS6 : List ℤ :=
  [s1N 112539734, s1N 58056652, s1N 29391613, s1N 14623015, s1N 7159769, s1N 3453012,
   s1N 1642316, s1N 770981, s1N 356991, s1N 163196, s1N 73941, s1N 33150, s1N 14506, s1N 6071,
   s1N 2402, s1N 902, s1N 326, s1N 116, s1N 38, s1N 11, s1N 3, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St4VecS7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St4VecS8 : List ℤ :=
  [s1P 0]
private def s1St4Vec : List ℤ :=
  s1St4VecS0 ++
  (s1St4VecS1 ++
  (s1St4VecS2 ++
  (s1St4VecS3 ++
  (s1St4VecS4 ++
  (s1St4VecS5 ++
  (s1St4VecS6 ++
  (s1St4VecS7 ++
  (s1St4VecS8))))))))
private def s1Chk5 : List Rkm128kSeg := s1Take 2 s1Rem5
private def s1Rem6 : List Rkm128kSeg := s1Drop 2 s1Rem5
private def s1St5VecS0 : List ℤ :=
  [s1P 62297, s1P 1032399, s1N 489904, s1N 99053, s1N 5053818, s1N 2384382, s1N 4881296,
   s1N 4081762, s1P 667072, s1P 11672148, s1P 9850337, s1N 11489560, s1N 3765426, s1N 10742856,
   s1N 26422275, s1P 1714646, s1P 7061312, s1P 12308868, s1P 5638292, s1P 9467464, s1P 9911361,
   s1P 34328766, s1P 30711025, s1P 3954202, s1P 46385881, s1P 51655648, s1P 44161112,
   s1N 3828142, s1N 102459397, s1N 156684669, s1N 98397494, s1N 6571977, s1N 43915617,
   s1N 11084105, s1P 78135716, s1P 158313081, s1P 75399181, s1N 106074020, s1P 53488100,
   s1P 7260391, s1P 136019302, s1P 122294074, s1P 274437115, s1P 241801926, s1P 83229654,
   s1P 34783184, s1P 173267381, s1P 198112361, s1N 75119585, s1P 141732674, s1N 40627801,
   s1P 148291325, s1N 237857812, s1N 55188278, s1N 645212255, s1N 290772624, s1N 81429153,
   s1N 153152143, s1N 151290685, s1N 130795541, s1P 306749090, s1P 632682471, s1P 123080494,
   s1P 106512368]
private def s1St5VecS1 : List ℤ :=
  [s1P 78282163, s1P 204432282, s1P 297702177, s1N 455385348, s1N 370221197, s1P 381950104,
   s1N 235002647, s1P 642399025, s1P 365129158, s1P 429386761, s1P 336793065, s1P 74674914,
   s1P 469196631, s1P 75577917, s1N 103797572, s1N 553967028, s1N 103598084, s1N 47829262,
   s1N 627773102, s1N 729139236, s1N 978394092, s1N 566575177, s1N 1140834931, s1P 486313872,
   s1P 223456717, s1P 731279519, s1P 2727063863, s1P 1198333471, s1N 2820617207,
   s1N 10398790195, s1N 9814532176, s1N 4393698568, s1P 7033923889, s1P 7828781312,
   s1N 3467844306, s1N 5574819806, s1N 2882513631, s1P 2130103637, s1P 6931191112,
   s1P 3482194894, s1N 3109586079, s1P 2351002018, s1N 5059111738, s1N 1532899692,
   s1P 2216926015, s1P 4197097211, s1P 2861558172, s1P 1427460847, s1N 1743063919,
   s1N 3183987966, s1P 239214269, s1P 806834663, s1P 2354251846, s1N 7247572, s1N 2540805353,
   s1N 539735750, s1P 2770379457, s1N 870250303, s1N 727756145, s1N 1990743805, s1P 1375420926,
   s1P 3188584352, s1P 244205196, s1N 1792576321]
private def s1St5VecS2 : List ℤ :=
  [s1P 3612132583, s1P 2875579714, s1P 4506198978, s1N 3878198011, s1N 960745380,
   s1N 471593792, s1P 957412437, s1P 733981773, s1P 4155229211, s1N 2044359880, s1N 6713188967,
   s1N 8043170939, s1N 10632670330, s1N 17928139873, s1N 16022182071, s1N 33162021711,
   s1N 34975246647, s1N 24580954101, s1N 1999705091, s1P 6121929778, s1P 8874896011,
   s1N 4142930925, s1N 22979872583, s1N 12067978373, s1N 5797375479, s1N 12938727534,
   s1N 21920138280, s1N 2889237975, s1P 3239602810, s1P 6750556984, s1P 6489600683,
   s1P 6582232563, s1N 2325030135, s1P 3540003293, s1N 15643467359, s1N 12409866787,
   s1N 23491854259, s1N 5746933909, s1P 15233908665, s1P 17946488934, s1N 1267668019,
   s1P 21651894545, s1P 29698425763, s1P 16734633230, s1P 14957574016, s1N 2049967227,
   s1N 14943310342, s1N 17663958877, s1P 24748374402, s1P 29803443887, s1P 13737187828,
   s1P 10402602870, s1P 10294503465, s1N 3446206676, s1P 5165942901, s1P 626763417,
   s1P 6478519250, s1N 5235102617, s1N 11780023728, s1N 18944862054, s1P 4883052200,
   s1P 9361587480, s1N 16692218869, s1N 9199350213]
private def s1St5VecS3 : List ℤ :=
  [s1N 3074626289, s1P 5399648827, s1N 38933910209, s1N 34548827249, s1P 18751271442,
   s1P 30122284349, s1P 20256956152, s1P 15029321791, s1P 13511603482, s1P 9379721166,
   s1N 4744508222, s1N 10529419046, s1N 7694909423, s1N 7674115473, s1P 15883221415,
   s1P 11248543073, s1N 6213961963, s1P 6443272145, s1P 17815727207, s1P 16582616866,
   s1N 8880890960, s1N 12041093726, s1N 4450132172, s1N 16236865067, s1N 5433084695,
   s1P 7070280138, s1P 17035454956, s1P 7580819752, s1P 13230218975, s1N 1172207629,
   s1N 9558455839, s1N 16911401132, s1N 3495751536, s1N 13936365483, s1P 12554995917,
   s1P 7613229095, s1N 3954019721, s1N 22823300419, s1N 23059142612, s1N 19662487484,
   s1N 9319817695, s1P 6571272870, s1N 12142437836, s1P 4745751647, s1N 14400267349,
   s1N 1062573906, s1N 8749303737, s1P 4150941137, s1P 24238021911, s1P 31523785205,
   s1P 34779024305, s1P 20419520105, s1N 12266269750, s1P 1115966681, s1P 9435406013,
   s1N 10463463762, s1P 9486374612, s1N 4792820484, s1N 116787884, s1N 14625159811,
   s1N 14981590985, s1N 12312225628, s1N 4375091335, s1P 9200161305]
private def s1St5VecS4 : List ℤ :=
  [s1N 7635657988, s1P 34361874794, s1P 27239227458, s1N 22224230181, s1N 12992918027,
   s1P 40138400074, s1P 24037177355, s1P 2121027199, s1P 4536501691, s1N 19368633058,
   s1P 41638604371, s1P 2219207551, s1P 36890880710, s1N 20283659704, s1P 14428794735,
   s1N 22641907601, s1P 15991475893, s1P 884053837, s1N 11083086729, s1N 22979348270,
   s1P 1862564407, s1P 1652150311, s1P 1265704727, s1N 23935104321, s1P 12100101055,
   s1N 14309619737, s1N 46721416443, s1N 38925051669, s1N 30016040029, s1N 2366283169,
   s1N 47386600673, s1P 20460685346, s1P 38827996566, s1P 7571307851, s1P 1703882968,
   s1N 3260781397, s1N 5754773350, s1P 67742843910, s1N 23449248209, s1N 4028517972,
   s1N 62294507985, s1P 87317752730, s1P 19778026044, s1P 3428740631, s1N 31814515890,
   s1N 24690495529, s1P 117659719122, s1N 25256133242, s1P 9877365130, s1P 2963504655,
   s1P 26840602631, s1N 34618665364, s1P 12939668293, s1P 39358796665, s1N 107350382152,
   s1N 75659005354, s1N 82352793336, s1P 69832035258, s1P 219578097484, s1N 148166456897,
   s1N 13127899509, s1P 28320294848, s1N 150472294392, s1P 101090313453]
private def s1St5VecS5 : List ℤ :=
  [s1P 7610789998, s1N 46574438450, s1P 39343834560, s1P 11877997509, s1P 308765620,
   s1N 37591657309, s1P 7604764360, s1P 93800095320, s1N 4579728544, s1N 115028341424,
   s1P 4432057702, s1P 23525494594, s1N 101809732476, s1N 12144551916, s1N 65129081578,
   s1N 308701310740, s1P 159065156059, s1N 176311704786, s1N 288786262360, s1N 236093064322,
   s1N 860154115168, s1N 2743932380540, s1N 5887470865316, s1N 11250837473159,
   s1N 18529321725764, s1N 28602510514114, s1N 42364825470594, s1N 59264196452422,
   s1N 79685166444538, s1N 103086091991867, s1N 128708251110046, s1N 156163376005498,
   s1N 183733374082255, s1N 210100289359794, s1N 234653824753238, s1N 255663391653185,
   s1N 271565626554535, s1N 282036599108871, s1N 286709954022897, s1N 285241481986290,
   s1N 278140975101932, s1N 266045083041942, s1N 249286675205979, s1N 228812129282298,
   s1N 206315273182535, s1N 183120370684246, s1N 159747897648391, s1N 136640603671113,
   s1N 114634129744609, s1N 94563578073151, s1N 76812177230830, s1N 61400919630815,
   s1N 48296383242161, s1N 37475584060063, s1N 28783549835462, s1N 21873844163112,
   s1N 16330594337095, s1N 11833124274268, s1N 8215916071156, s1N 5412459979380,
   s1N 3365146831068, s1N 1973665407998, s1N 1096980616355, s1P 583930781495]
private def s1St5VecS6 : List ℤ :=
  [s1N 303057150965, s1N 157307346435, s1N 84047990687, s1N 47217034603, s1N 27975068905,
   s1N 17223172108, s1N 10782172231, s1N 6737360885, s1N 4151761875, s1N 2506847187,
   s1N 1478885104, s1N 851692167, s1N 478902212, s1N 263095099, s1N 141338726, s1N 74321042,
   s1N 38290830, s1N 19347983, s1N 9597289, s1N 4677735, s1N 2242245, s1N 1057899, s1N 491576,
   s1N 225029, s1N 101458, s1N 45016, s1N 19623, s1N 8387, s1N 3505, s1N 1425, s1N 559,
   s1N 209, s1N 73, s1N 21, s1N 5, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St5VecS7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St5VecS8 : List ℤ :=
  [s1P 0]
private def s1St5Vec : List ℤ :=
  s1St5VecS0 ++
  (s1St5VecS1 ++
  (s1St5VecS2 ++
  (s1St5VecS3 ++
  (s1St5VecS4 ++
  (s1St5VecS5 ++
  (s1St5VecS6 ++
  (s1St5VecS7 ++
  (s1St5VecS8))))))))
private def s1Chk6 : List Rkm128kSeg := s1Take 2 s1Rem6
private def s1Rem7 : List Rkm128kSeg := s1Drop 2 s1Rem6
private def s1St6VecS0 : List ℤ :=
  [s1P 333271, s1P 2076588, s1P 936314, s1P 321499, s1N 1139551, s1N 1358384, s1N 1734256,
   s1N 96780, s1P 3511739, s1P 10407541, s1N 5750234, s1N 17373925, s1N 1963693, s1N 11663949,
   s1N 1283103, s1N 322488, s1P 9629528, s1P 8813426, s1P 9451052, s1N 5729426, s1N 29562961,
   s1N 10989321, s1P 4237833, s1P 5153528, s1N 15693130, s1N 10181702, s1P 10789788,
   s1P 58234514, s1P 22274552, s1P 21173117, s1P 34601694, s1P 16909014, s1P 1032828,
   s1P 113145663, s1P 128585312, s1N 8853217, s1N 84972394, s1N 163172701, s1N 80519870,
   s1P 74975936, s1P 140038016, s1N 9298242, s1N 32537792, s1P 100657647, s1N 92417983,
   s1N 115377307, s1N 214572927, s1N 273842411, s1N 373362375, s1N 344039704, s1N 54368979,
   s1P 56269714, s1P 42050903, s1N 46102707, s1N 85704327, s1N 141062771, s1N 11213515,
   s1N 144198389, s1N 267188052, s1P 95327409, s1P 200059715, s1P 240383139, s1P 63351494,
   s1P 313864754]
private def s1St6VecS1 : List ℤ :=
  [s1N 185615811, s1N 507515968, s1N 9095571, s1N 153083070, s1P 102188168, s1P 602718098,
   s1P 414308116, s1P 775496439, s1P 110842667, s1P 572303632, s1P 446766298, s1N 90244151,
   s1P 651352422, s1P 481929349, s1P 434357088, s1P 282223791, s1P 588793220, s1P 201202999,
   s1P 668643692, s1N 109056458, s1P 550241826, s1P 972949407, s1P 242423768, s1P 1164842913,
   s1P 77081731, s1N 276617566, s1N 588798033, s1N 159537797, s1N 545278990, s1N 65352374,
   s1N 975826567, s1N 909250676, s1N 381829834, s1N 1518014679, s1N 2894879052, s1N 2430662634,
   s1N 2716115423, s1N 8162422929, s1N 11871887342, s1N 11605853626, s1N 6305127781,
   s1P 1939725495, s1P 6932843282, s1P 5409854517, s1P 2135026298, s1N 1582238910,
   s1N 986366145, s1N 1672279032, s1N 5204542036, s1N 2102375108, s1N 820064818,
   s1N 2403614865, s1N 2276063958, s1P 558899703, s1N 926198986, s1N 1256848943,
   s1P 1876157289, s1P 2732673227, s1N 1590153253, s1P 941027337, s1P 1924255474,
   s1P 4863491991, s1P 3803119812, s1P 1058311329]
private def s1St6VecS2 : List ℤ :=
  [s1N 1632688050, s1N 3412967129, s1P 1348846868, s1N 475451381, s1N 1658504156,
   s1N 1270758412, s1P 1484496594, s1N 2953608798, s1N 1159814448, s1N 3786552647,
   s1N 2308921967, s1N 2262952747, s1P 523899316, s1P 2774818225, s1P 8218730772,
   s1P 8221396138, s1N 4317944803, s1N 2387232915, s1P 1908524209, s1P 5268944921,
   s1P 3770320899, s1N 2776986166, s1P 200318230, s1N 4198212759, s1P 6559981125,
   s1P 9711904232, s1P 12959696062, s1P 33790921091, s1N 5245744573, s1N 28909891542,
   s1N 15695131339, s1N 41569907676, s1N 30412303647, s1N 2842896724, s1N 4196234055,
   s1N 454832537, s1N 22620406462, s1N 4733735590, s1P 1733655554, s1P 5450398100,
   s1N 6923715052, s1P 3387418870, s1P 1972759080, s1N 7317552613, s1P 8623552005,
   s1N 3590865215, s1P 2695131465, s1P 19110049296, s1P 11295064345, s1P 11435549889,
   s1P 15183029899, s1P 12955524605, s1P 21091598550, s1P 30277464331, s1P 18155862029,
   s1P 1748201412, s1N 19168518376, s1N 12681337206, s1P 15265745047, s1P 35533756309,
   s1P 11408450475, s1P 929702677, s1N 9757861968, s1P 8408370778]
private def s1St6VecS3 : List ℤ :=
  [s1P 17479581317, s1P 25471898142, s1P 5154210699, s1N 2265565313, s1N 3144498366,
   s1N 1774422741, s1N 10247960370, s1P 22602012559, s1P 33280984737, s1N 4753939077,
   s1N 14961127385, s1N 12290874524, s1N 16919173250, s1N 15571350294, s1P 9058964554,
   s1P 4688782923, s1N 12425135681, s1N 15661979907, s1P 19674133854, s1N 30408845543,
   s1N 13659530907, s1N 706533416, s1P 12800205371, s1P 30989945850, s1P 24042636172,
   s1P 2785206886, s1P 9822026688, s1N 8548889859, s1N 3163885529, s1N 5311260455,
   s1N 6060221544, s1N 14704175968, s1N 1303517637, s1N 12256372004, s1P 8308519703,
   s1P 4762900680, s1P 6935579736, s1P 14830583015, s1P 26134825349, s1P 13961951405,
   s1P 5014100161, s1P 13010903279, s1P 6802159599, s1N 19238381144, s1P 2151868734,
   s1P 2817559363, s1N 17135272575, s1N 25898767242, s1P 5067340022, s1P 7336536190,
   s1N 22525451230, s1N 11613668121, s1N 9832428717, s1P 14450258406, s1P 7061947170,
   s1P 25926309238, s1P 6503532926, s1N 5111232917, s1P 11044124625, s1N 20530275486,
   s1P 6917442677, s1N 26548368212, s1P 1312386462, s1N 18635550404]
private def s1St6VecS4 : List ℤ :=
  [s1N 20717477620, s1P 53344678903, s1P 1991615985, s1N 31651592594, s1P 23695524869,
   s1P 15560409190, s1P 6548895993, s1P 4579513297, s1P 15148405106, s1N 18339331359,
   s1N 13405147279, s1N 31515906371, s1N 34860401796, s1P 12345907226, s1N 1981326512,
   s1P 29812147633, s1N 31093397717, s1P 14242773087, s1N 4823559755, s1P 627610306,
   s1N 101596003, s1N 263603170, s1P 7149324301, s1N 2519321656, s1N 10500249941,
   s1N 21615546198, s1N 54839687602, s1N 36319745725, s1N 9210208583, s1P 39345050827,
   s1N 6216627341, s1N 29043334091, s1N 30773963658, s1N 9491215612, s1P 15795432881,
   s1N 56279313683, s1N 16552713522, s1N 13670079113, s1P 23969149201, s1N 71084117122,
   s1N 88388040544, s1N 58182468842, s1P 14382931240, s1N 18434296129, s1P 31212129746,
   s1P 101567181433, s1N 28359257325, s1P 30820760541, s1N 25422692906, s1P 22756555324,
   s1P 47221859864, s1N 24938338447, s1N 54214515185, s1P 68550065585, s1P 52119085986,
   s1N 24107805688, s1P 48998804395, s1N 63992786405, s1P 153238139776, s1P 156358069960,
   s1P 71902169827, s1N 41846088848, s1N 175106029036, s1P 129756754147]
private def s1St6VecS5 : List ℤ :=
  [s1P 47816712908, s1P 86802075412, s1N 15767027325, s1P 108891697094, s1N 79529356388,
   s1N 152373290590, s1P 35837119639, s1P 12700489170, s1P 65542570676, s1N 98750569029,
   s1N 64856443651, s1N 138285517930, s1P 82024224058, s1N 84800865757, s1N 46190774511,
   s1N 272989735672, s1N 85348265624, s1P 173147449389, s1N 154011026335, s1N 31324252630,
   s1N 157490374020, s1P 13458629849, s1N 154879471274, s1P 73458252986, s1N 234756501061,
   s1P 169760913801, s1N 191233475735, s1N 6288975820, s1N 332133012770, s1N 214144101408,
   s1P 47283677012, s1P 115079732999, s1P 305228403318, s1P 48476664521, s1P 480162470738,
   s1N 429350768426, s1N 542729744347, s1N 2611194224156, s1N 6546305620627,
   s1N 13142044659912, s1N 22822300888367, s1N 36089436629801, s1N 53388517905793,
   s1N 74495226600317, s1N 98889457473423, s1N 126084178406364, s1N 155585816287682,
   s1N 185408139501745, s1N 214236276149777, s1N 239400865123147, s1N 261666511331095,
   s1N 277808491624054, s1N 289032609155877, s1N 292626473439757, s1N 289442736938622,
   s1N 280763969121643, s1N 265993766082446, s1N 247234948799960, s1N 225695891119576,
   s1N 201439095893459, s1N 176386530747549, s1N 152033577950991, s1N 128407454771654,
   s1N 105901142199312]
private def s1St6VecS6 : List ℤ :=
  [s1N 86249309093869, s1N 69102656811046, s1N 54964392762863, s1N 42421868608441,
   s1N 32369072753779, s1N 24706921390241, s1N 18332940268468, s1N 13106632856924,
   s1N 9086455550352, s1N 5977298006456, s1N 3583618458805, s1N 1914479185887,
   s1P 924614740137, s1N 428897299337, s1N 210768353798, s1N 117588663319, s1N 72712763904,
   s1N 46581476606, s1N 29616529990, s1P 18457638748, s1N 11291064230, s1N 6805199980,
   s1N 4048593114, s1N 2376573044, s1N 1374218103, s1N 781230415, s1N 435943002, s1N 238534866,
   s1N 127914098, s1N 67217717, s1N 34620372, s1N 17483613, s1N 8661665, s1N 4211977,
   s1N 2011546, s1N 943977, s1N 435478, s1N 197551, s1N 88127, s1N 38656, s1N 16658, s1N 7047,
   s1N 2917, s1N 1177, s1N 456, s1N 169, s1N 57, s1N 16, s1N 3, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St6VecS7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St6VecS8 : List ℤ :=
  [s1P 0]
private def s1St6Vec : List ℤ :=
  s1St6VecS0 ++
  (s1St6VecS1 ++
  (s1St6VecS2 ++
  (s1St6VecS3 ++
  (s1St6VecS4 ++
  (s1St6VecS5 ++
  (s1St6VecS6 ++
  (s1St6VecS7 ++
  (s1St6VecS8))))))))
private def s1Chk7 : List Rkm128kSeg := s1Take 2 s1Rem7
private def s1Rem8 : List Rkm128kSeg := s1Drop 2 s1Rem7
private def s1St7VecS0 : List ℤ :=
  [s1P 239115, s1P 1455447, s1P 743334, s1P 652913, s1P 1815937, s1N 52870, s1N 175422,
   s1N 3607024, s1N 2472913, s1N 3447284, s1P 2060507, s1P 13568955, s1P 11273300, s1N 2294409,
   s1N 16252385, s1N 3225854, s1N 1507099, s1P 4678794, s1P 3199673, s1N 7973776, s1N 11667253,
   s1N 20364470, s1P 11275020, s1P 11818954, s1N 34084669, s1N 3197922, s1N 35400015,
   s1N 2849244, s1N 32315546, s1N 17507780, s1P 16730866, s1P 16411390, s1N 29883928,
   s1N 22269905, s1P 26487885, s1N 44052060, s1N 30231622, s1N 55864245, s1N 9414239,
   s1P 3771049, s1P 48017984, s1P 16462583, s1P 85362644, s1P 112018679, s1P 161302743,
   s1P 184586623, s1P 144920224, s1N 61181086, s1N 110824285, s1N 153158947, s1P 76051224,
   s1P 74116640, s1P 5078198, s1P 60926307, s1P 53767100, s1P 181929871, s1N 199368248,
   s1N 146525596, s1N 582727730, s1N 214749995, s1N 59394811, s1N 46463962, s1P 188555135,
   s1P 273663891]
private def s1St7VecS1 : List ℤ :=
  [s1N 103562761, s1P 3923403, s1N 218798570, s1N 360214379, s1N 60148449, s1P 396235689,
   s1P 725282823, s1P 737720362, s1P 576390330, s1P 270511738, s1N 11690474, s1N 157873192,
   s1P 100576555, s1P 233398164, s1P 652453394, s1N 201141639, s1N 81413224, s1N 196712120,
   s1N 75411076, s1P 533503069, s1P 392779274, s1P 814119568, s1P 669503397, s1P 83465419,
   s1P 181499789, s1P 376859708, s1P 517374531, s1P 786330547, s1N 674351921, s1N 809785982,
   s1N 738564335, s1P 189233706, s1N 666380465, s1N 1032467161, s1N 597536879, s1N 675115921,
   s1N 745984850, s1N 670340413, s1N 1009162644, s1P 575901079, s1P 1151477612, s1N 626760914,
   s1N 1560802340, s1N 2306010749, s1P 56309596, s1P 3225711213, s1P 3320718232, s1P 483851972,
   s1N 1204222015, s1N 5129382025, s1N 7558815298, s1N 10997105271, s1N 12878671746,
   s1N 9041463728, s1N 3511232929, s1P 1554224686, s1P 2403784613, s1P 4175802729,
   s1N 3981018006, s1N 2586653187, s1P 1563809231, s1P 1110250079, s1N 2695147291,
   s1P 367798379]
private def s1St7VecS2 : List ℤ :=
  [s1P 1760251802, s1P 2695887614, s1N 4833768, s1N 1144038119, s1N 2668390156, s1P 781926299,
   s1P 213598748, s1N 6453981986, s1N 2486669929, s1N 3900674112, s1N 1647867541,
   s1N 530128859, s1P 4860603043, s1P 1025916869, s1P 1941712761, s1N 208121776,
   s1N 1931395005, s1P 364988216, s1N 726034470, s1P 2306421696, s1N 2071384735,
   s1P 7475204211, s1P 998086316, s1P 1224604845, s1P 3783646197, s1P 10109803001,
   s1P 9769770245, s1P 8492526075, s1N 7772953878, s1N 4151946994, s1N 8287277065,
   s1N 2062112627, s1N 8979713367, s1N 23403851652, s1N 22397802068, s1N 6200301887,
   s1N 20015800688, s1N 8642033911, s1P 23094036473, s1N 1796566389, s1N 9672276481,
   s1N 23030988330, s1N 32824354873, s1N 13422429579, s1P 10320428558, s1P 15082935230,
   s1N 24594044865, s1N 20421358759, s1N 17311463941, s1P 9322401675, s1P 5736303113,
   s1P 3267216609, s1P 4158770949, s1N 3100176245, s1P 10721091720, s1N 5825353935,
   s1P 7131097281, s1N 1982560323, s1N 13836151255, s1N 32724778034, s1N 5878669775,
   s1N 20888995220, s1P 569414516, s1P 5924759477]
private def s1St7VecS3 : List ℤ :=
  [s1P 679574422, s1N 12795034382, s1N 23030070734, s1N 24291931089, s1N 31398657781,
   s1N 21163024280, s1P 8441876128, s1P 20954179377, s1P 9778941689, s1N 17702138417,
   s1N 29291105381, s1N 21334800798, s1N 12987392721, s1N 5982306228, s1P 3340536912,
   s1P 11475130942, s1P 22694818136, s1P 25458971927, s1P 2114922374, s1N 21677539265,
   s1N 2787930649, s1P 5372438492, s1N 9144672001, s1P 15622727170, s1P 26432612358,
   s1N 4679105434, s1P 18842611213, s1N 12632152252, s1N 14303118840, s1P 475568542,
   s1P 336785637, s1P 1066426070, s1P 19965396660, s1P 16472429025, s1P 6663848471,
   s1P 25107103231, s1P 21812575379, s1P 17733718316, s1P 11882898580, s1P 804229335,
   s1N 1397048703, s1N 353917847, s1P 4863913533, s1P 19092100933, s1P 1676571711,
   s1N 10841043432, s1P 1302813954, s1N 3400598960, s1N 15602508835, s1N 5819647143,
   s1N 20307433845, s1N 31551328368, s1N 19443063805, s1P 20943891356, s1P 11966178275,
   s1P 4984757687, s1P 8590073621, s1N 50422036589, s1N 11358033594, s1P 7401940840,
   s1P 2778005047, s1N 8130386201, s1P 17240461098, s1P 429433775]
private def s1St7VecS4 : List ℤ :=
  [s1N 10568156137, s1N 8148768970, s1N 6343588821, s1P 14061946464, s1P 10190375237,
   s1N 47804327464, s1N 49813134437, s1P 5463176009, s1P 38411775205, s1N 7381120602,
   s1N 17983540860, s1N 5746571537, s1N 8597085731, s1N 17840384039, s1N 12172448962,
   s1P 16782273744, s1P 1449212945, s1N 13863665254, s1N 1923529024, s1N 5525678013,
   s1N 16197700485, s1N 5658097304, s1P 8998356370, s1N 1303383266, s1N 20082211954,
   s1P 50264436768, s1N 23964630434, s1N 38671377822, s1N 53058973451, s1N 58273633828,
   s1N 43280002031, s1N 27959996704, s1P 32417255284, s1P 36787957720, s1N 22085926810,
   s1N 60810704344, s1N 22223529250, s1P 15259529502, s1P 54163745898, s1N 7263227018,
   s1P 13741883442, s1P 9932406373, s1N 54168844549, s1P 7679980405, s1P 35533995368,
   s1P 28142383653, s1N 44814622184, s1N 28277602131, s1N 56429387513, s1P 48288954576,
   s1P 72848346899, s1N 68461987060, s1N 98559825532, s1P 107525493629, s1P 15122385838,
   s1N 14174539590, s1P 49788871918, s1P 65130111329, s1N 121528825218, s1N 84596335984,
   s1P 16073244073, s1P 19739997106, s1P 120527890151, s1N 23916904414]
private def s1St7VecS5 : List ℤ :=
  [s1N 152450088098, s1P 30861666100, s1P 70747583940, s1P 115696906348, s1P 16137527146,
   s1P 218775354361, s1N 87055971486, s1N 49864681744, s1N 81953259269, s1N 76251092209,
   s1N 111828012385, s1P 192602758996, s1P 60543929407, s1N 184125873939, s1N 176067955627,
   s1P 245239625229, s1P 63012315301, s1P 73657463411, s1P 94062492813, s1N 106744752756,
   s1N 110061444939, s1P 111007155471, s1N 494024377155, s1P 137267241252, s1N 67975305621,
   s1N 42139795812, s1N 168381966450, s1N 302924777310, s1P 71252370735, s1P 273774624577,
   s1N 140108487698, s1N 11629217757, s1N 58177295338, s1P 77916691863, s1P 258921391006,
   s1P 549115758763, s1P 19201636747, s1N 138237066517, s1P 306473284536, s1P 216722146313,
   s1P 40336419507, s1P 375724987640, s1P 173576792903, s1P 695711345793, s1P 162731240757,
   s1N 495907335968, s1P 24924370732, s1P 198640349910, s1P 279778961108, s1P 209418182539,
   s1P 1090106793435, s1P 784763014772, s1P 2421002335779, s1P 7273905822800,
   s1P 15646953014123, s1P 27946508419017, s1P 44473014190210, s1P 65972004910860,
   s1P 91772247351556, s1P 120986696582815, s1P 151779860668999, s1P 183814716939866,
   s1P 214704521534613, s1P 243688474792561]
private def s1St7VecS6 : List ℤ :=
  [s1P 265986810477435, s1P 284732656562713, s1P 294980932275676, s1P 298444605496564,
   s1P 294657259194062, s1P 283416594479227, s1P 267948529444470, s1P 247557757163093,
   s1P 222897345271533, s1P 197233627219278, s1P 171458341035601, s1P 145092663318723,
   s1P 120686910325770, s1P 98573635879748, s1P 80235243114854, s1P 62596374372811,
   s1P 48514357893304, s1P 37615133482886, s1P 28360620378828, s1P 21038876015936,
   s1P 15303977857354, s1P 10338436283810, s1P 6161686086762, s1P 3207255631325,
   s1P 1513446072245, s1P 704908105129, s1P 356635321412, s1N 199979662375, s1P 116963050113,
   s1P 67598610529, s1P 38329073725, s1P 21870242844, s1P 12921370988, s1P 7955548666,
   s1P 5012976488, s1P 3152189507, s1P 1942009909, s1P 1162048328, s1P 673977623,
   s1P 379382078, s1P 207762813, s1P 110959677, s1P 57905787, s1P 29571104, s1P 14792685,
   s1P 7254004, s1P 3488964, s1P 1646619, s1P 762822, s1P 346991, s1P 155008, s1P 68011,
   s1P 29298, s1P 12387, s1P 5131, s1P 2077, s1P 815, s1P 306, s1P 107, s1P 34, s1P 8, s1P 1,
   s1P 0, s1P 0]
private def s1St7VecS7 : List ℤ :=
  [s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St7VecS8 : List ℤ :=
  [s1P 0]
private def s1St7Vec : List ℤ :=
  s1St7VecS0 ++
  (s1St7VecS1 ++
  (s1St7VecS2 ++
  (s1St7VecS3 ++
  (s1St7VecS4 ++
  (s1St7VecS5 ++
  (s1St7VecS6 ++
  (s1St7VecS7 ++
  (s1St7VecS8))))))))
private def s1Chk8 : List Rkm128kSeg := s1Take 2 s1Rem8
private def s1Rem9 : List Rkm128kSeg := s1Drop 2 s1Rem8
private def s1St8VecS0 : List ℤ :=
  [s1N 364428, s1P 526323, s1P 1753625, s1P 484872, s1P 1682103, s1P 63920, s1N 231008,
   s1N 2640256, s1N 227160, s1P 108665, s1P 1311026, s1P 550540, s1P 3872493, s1P 2798078,
   s1P 4252184, s1P 16059795, s1P 6320783, s1P 24515807, s1P 20864128, s1P 29175624,
   s1P 9286941, s1P 7492010, s1N 2897048, s1P 106524, s1N 21224191, s1N 6012057, s1P 32662946,
   s1N 16506077, s1N 23773074, s1P 8553448, s1N 21081863, s1P 10020714, s1P 9182518,
   s1P 2299506, s1P 20598187, s1P 35562303, s1P 55739519, s1P 16459119, s1N 41625675,
   s1P 28149405, s1P 30776753, s1N 35238269, s1P 83703043, s1P 80599733, s1P 95926207,
   s1P 22719484, s1P 53421019, s1P 105783653, s1P 38375587, s1N 9178961, s1P 6625878,
   s1P 80238331, s1P 95434244, s1P 111578130, s1P 153257448, s1P 161043778, s1N 213281891,
   s1N 291112904, s1N 253644267, s1N 207445579, s1P 114101692, s1P 45361291, s1P 18165383,
   s1N 90322815]
private def s1St8VecS1 : List ℤ :=
  [s1P 221000454, s1P 484223581, s1P 155629867, s1P 162448434, s1P 162396569, s1P 399447115,
   s1N 5908243, s1P 115510261, s1N 352684, s1N 338785025, s1N 312773302, s1N 433691883,
   s1P 169727886, s1N 340375072, s1N 130996653, s1P 474805997, s1N 442012734, s1N 370164646,
   s1N 617072660, s1N 700882709, s1P 439970505, s1P 161538684, s1P 363875647, s1N 194904687,
   s1N 452106816, s1P 163266986, s1N 32514236, s1P 493733355, s1P 537435549, s1P 94003372,
   s1P 340291453, s1P 386046294, s1P 498108986, s1P 308324577, s1P 1287335911, s1P 1117488319,
   s1N 65311469, s1N 244213953, s1N 114176919, s1N 783046046, s1N 389371869, s1N 1747722623,
   s1N 1230543261, s1N 731472284, s1N 2067983022, s1N 1414101389, s1P 481395666, s1P 730066427,
   s1N 173123532, s1P 2041279110, s1N 1524566043, s1P 3815317814, s1P 1803711870,
   s1P 1141332668, s1P 32884361, s1P 2532527585, s1N 3010296326, s1N 5761978112,
   s1N 1803132204, s1P 1478869205, s1N 6056605625, s1N 3313458066, s1P 7347412818,
   s1P 9739382134]
private def s1St8VecS2 : List ℤ :=
  [s1N 3449063237, s1N 1600353270, s1N 9732264038, s1N 11235882210, s1N 8198662550,
   s1N 296274996, s1N 2525448564, s1P 2362958407, s1P 5309466317, s1P 2421549725,
   s1N 2403396887, s1P 4279246243, s1N 4172529368, s1P 1384835970, s1P 799106115,
   s1N 4062724920, s1N 110217695, s1P 2571685276, s1N 1097536614, s1N 7489273041,
   s1P 266121689, s1N 563101874, s1P 1399564142, s1N 3525409277, s1N 2494614156,
   s1P 1951141372, s1P 1852089480, s1P 1729947695, s1P 4890376193, s1N 5384544390,
   s1N 6457358673, s1N 5216149458, s1N 86575576, s1P 5689249976, s1N 1197881698,
   s1P 2381461459, s1P 12909401802, s1P 1894628882, s1P 3943036304, s1N 8765124315,
   s1N 14324634435, s1N 15685720746, s1N 12090293511, s1P 8217763567, s1P 12761967025,
   s1P 17407934727, s1P 35149696333, s1P 8819170725, s1P 8475522766, s1N 12488963448,
   s1N 42073751501, s1N 34748034932, s1N 8958912978, s1P 2544611560, s1P 10495089242,
   s1N 3790458576, s1P 3426409241, s1P 15036707421, s1P 20179466278, s1N 2993415587,
   s1N 1291497983, s1P 1057288149, s1N 3891437613, s1P 8129227784]
private def s1St8VecS3 : List ℤ :=
  [s1N 4871642987, s1P 5810519792, s1P 1918090282, s1N 3167744379, s1P 3963086291,
   s1P 6566117437, s1P 6802088283, s1P 3116723246, s1N 11475511864, s1N 15891390653,
   s1N 24882688659, s1N 19532037980, s1P 244537889, s1P 21601238228, s1N 2509877581,
   s1N 22526758050, s1N 19446272038, s1P 12137495838, s1N 16419491055, s1N 37235755058,
   s1N 24605554337, s1P 19301431086, s1N 21053853825, s1P 2619079552, s1P 14291182565,
   s1N 1450156393, s1N 27669800707, s1N 34045024650, s1N 20007851792, s1N 2880798948,
   s1P 20567433887, s1P 14953835275, s1N 3913335589, s1N 3060242874, s1N 18389828399,
   s1P 20974709518, s1P 3429518727, s1P 777623107, s1N 5392107021, s1N 1570247592,
   s1N 7681863476, s1P 5062977821, s1N 3242607489, s1P 4858495654, s1N 9087554929,
   s1P 13822718629, s1P 31268523014, s1P 8261148840, s1P 19925680874, s1P 14548948308,
   s1N 7745547203, s1N 2647687637, s1P 5062228300, s1P 31356952883, s1P 8566938048,
   s1N 19786454109, s1N 20814308184, s1N 8932383975, s1N 15351663404, s1N 23591493665,
   s1N 5917986737, s1P 9275013712, s1P 12167819590, s1P 12465386386]
private def s1St8VecS4 : List ℤ :=
  [s1P 39847772906, s1P 45593756369, s1P 28402416505, s1P 23873660693, s1N 26635595953,
   s1N 8987783607, s1N 1757817444, s1P 7540312583, s1P 20728017616, s1N 9653179640,
   s1P 533680415, s1N 69908691, s1N 28052274405, s1N 18874299396, s1N 34488611094,
   s1N 40349047116, s1N 40051988087, s1N 19373182558, s1N 6197984808, s1P 13958114158,
   s1P 4749042039, s1N 30263031695, s1N 6144012934, s1P 3064926936, s1N 2966272782,
   s1N 35192352643, s1N 13257335401, s1N 7581342932, s1P 43764936413, s1P 13629315478,
   s1P 18506311455, s1P 48373460230, s1P 52382035711, s1N 13107645138, s1N 6287129298,
   s1N 5932681145, s1N 20803321444, s1N 9452892229, s1N 59505260403, s1N 38838711966,
   s1N 24977573476, s1N 13989919235, s1P 24511914347, s1P 35450392018, s1P 84761806594,
   s1P 93934886142, s1N 53375596244, s1N 114365018867, s1N 7746920941, s1N 91197690334,
   s1N 58528223400, s1N 96762905403, s1N 68104411497, s1N 51952102404, s1P 17874302280,
   s1N 38827890596, s1P 90465865560, s1N 79164706903, s1N 17137689777, s1P 89065436260,
   s1N 119927258939, s1N 2913257747, s1N 82285502106, s1N 80453805182]
private def s1St8VecS5 : List ℤ :=
  [s1N 55896137159, s1N 19443229944, s1P 34386538610, s1P 68912570068, s1N 26253874378,
   s1N 177549616745, s1N 344027490922, s1P 64568939368, s1N 179787511709, s1N 36225454288,
   s1N 50140662134, s1N 58181964175, s1P 73979886565, s1N 196421254707, s1N 207971598724,
   s1N 13423722372, s1P 71629447467, s1N 102158587273, s1P 265271559624, s1N 103560210151,
   s1N 83627267998, s1P 160262866442, s1P 181069531387, s1N 322059587062, s1N 30809406772,
   s1P 129209223876, s1P 283406869292, s1N 266931966499, s1N 300061312478, s1N 152150113956,
   s1P 171867939635, s1P 154055727550, s1N 161947827051, s1N 287790590710, s1P 157020648807,
   s1P 329290134340, s1N 333350600874, s1N 338379439457, s1N 185280017817, s1N 50470583154,
   s1P 47803114564, s1P 361291909877, s1N 246186555376, s1P 245897704596, s1N 160724824009,
   s1N 44506106944, s1P 179533509838, s1P 677681626673, s1N 447464218852, s1N 211360185640,
   s1N 103769869226, s1N 653192710783, s1N 703507455562, s1P 309835266483, s1N 71303400641,
   s1N 360898400556, s1P 114848080764, s1P 984346694763, s1P 551878170264, s1P 229055052467,
   s1P 65600223716, s1N 52269480180, s1N 951376712329, s1N 358458613961]
private def s1St8VecS6 : List ℤ :=
  [s1N 325982579651, s1P 1355590229558, s1N 1543321785338, s1N 965525266063, s1N 7112931160036,
   s1N 17122268375611, s1N 32081247425405, s1N 53638019809628, s1N 79471487311758,
   s1N 108905909798302, s1N 142882844660749, s1N 178252872667304, s1N 212040991373171,
   s1N 243258025451328, s1N 270252068040147, s1N 289627038858487, s1N 301441709682937,
   s1N 305121427592009, s1N 301192328507262, s1N 289761132200517, s1N 271682884706503,
   s1N 248924290593891, s1N 222773643943370, s1N 194865368145084, s1N 167115541264828,
   s1N 140360892126932, s1N 115119707263468, s1N 92488451339265, s1N 73325009923017,
   s1N 57497356777983, s1N 44402300556858, s1N 33444854718418, s1N 24430234489844,
   s1N 17054106531979, s1N 11309605607443, s1N 7058963672838, s1N 4090703492154,
   s1N 2218351063414, s1N 1157342819525, s1N 586908807705, s1N 282783358204, s1P 126914736026,
   s1N 54953319888, s1P 25773828534, s1N 14608025518, s1N 9600926003, s1N 6524720124,
   s1N 4303200456, s1N 2715302147, s1N 1645702981, s1N 964389574, s1N 548982963, s1N 304354323,
   s1N 164538165, s1N 86805245, s1N 44719023, s1N 22510714, s1N 11079771, s1N 5335859,
   s1N 2515790, s1P 1161908, s1N 525880, s1N 233327, s1N 101504]
private def s1St8VecS7 : List ℤ :=
  [s1N 43292, s1N 18095, s1N 7405, s1N 2958, s1N 1148, s1N 428, s1N 150, s1N 46, s1N 11, s1N 1,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0]
private def s1St8VecS8 : List ℤ :=
  [s1P 0]
private def s1St8Vec : List ℤ :=
  s1St8VecS0 ++
  (s1St8VecS1 ++
  (s1St8VecS2 ++
  (s1St8VecS3 ++
  (s1St8VecS4 ++
  (s1St8VecS5 ++
  (s1St8VecS6 ++
  (s1St8VecS7 ++
  (s1St8VecS8))))))))
private def s1Chk9 : List Rkm128kSeg := s1Take 2 s1Rem9
private def s1Rem10 : List Rkm128kSeg := s1Drop 2 s1Rem9
private def s1St9VecS0 : List ℤ :=
  [s1N 163442, s1N 1382397, s1N 690616, s1N 297891, s1P 1501740, s1N 21474, s1N 762250,
   s1N 2397705, s1N 378705, s1P 1969174, s1P 2311790, s1P 4729140, s1P 4184770, s1N 6341227,
   s1N 6108786, s1P 10001582, s1P 2934295, s1P 943236, s1P 6321480, s1P 1621862, s1P 27098299,
   s1P 14002416, s1P 19641213, s1P 7225055, s1P 16634824, s1P 16351403, s1P 2961671,
   s1P 7216124, s1N 34444883, s1N 31460308, s1N 23961656, s1N 9098364, s1N 2724291,
   s1N 2839392, s1P 11067071, s1P 10447268, s1N 6731737, s1P 3175449, s1P 37603414,
   s1N 28901770, s1P 8012203, s1N 890307, s1P 80153386, s1P 62049368, s1N 36925672,
   s1N 31221743, s1N 73027285, s1N 56893204, s1N 72000468, s1P 31673835, s1N 14580216,
   s1P 34754333, s1P 96981829, s1P 57338447, s1P 141646061, s1N 57202756, s1P 114761518,
   s1P 87508010, s1P 22656608, s1P 155920905, s1P 153018896, s1P 39462975, s1N 240249534,
   s1N 235422581]
private def s1St9VecS1 : List ℤ :=
  [s1N 378408432, s1N 11220198, s1P 68521437, s1P 262626748, s1P 274342106, s1P 288810175,
   s1P 97892651, s1N 373726941, s1N 75476584, s1P 141639933, s1P 165638968, s1N 266396661,
   s1N 384883500, s1N 230311584, s1P 193210404, s1P 446411274, s1P 117054757, s1N 389032242,
   s1N 548612680, s1N 574867865, s1N 521741775, s1N 212671340, s1N 105515933, s1N 178807376,
   s1N 269749688, s1P 628689834, s1P 345643613, s1N 142956458, s1P 604783157, s1N 405373263,
   s1N 284669038, s1N 599780291, s1N 852319295, s1N 565491736, s1N 321870936, s1P 202412727,
   s1N 325580395, s1P 189903405, s1N 13434337, s1N 796962509, s1N 1277069114, s1N 687162053,
   s1N 900307783, s1N 1291369469, s1N 874828661, s1N 103707118, s1P 483382826, s1P 2722452195,
   s1P 1197203972, s1P 696734656, s1P 2411157914, s1N 629695591, s1N 2391195019, s1N 525137260,
   s1N 4253613016, s1N 1294606456, s1N 4449487621, s1N 1840735205, s1N 2500668297,
   s1P 2873601179, s1P 1579587153, s1P 5859197749, s1P 4798434712, s1P 1578935323]
private def s1St9VecS2 : List ℤ :=
  [s1P 640296244, s1P 4599706676, s1P 5250312912, s1N 4901110571, s1N 8876277672,
   s1N 3070897322, s1N 1453849293, s1P 2352907755, s1P 2307783482, s1P 6966798293,
   s1P 2428966200, s1N 11819259265, s1N 4683513157, s1P 813354318, s1N 2776801776,
   s1P 5028902312, s1P 3867078670, s1N 9258340959, s1P 3206498072, s1P 3198162085,
   s1P 6356297884, s1P 3629276329, s1P 4373070818, s1P 3162838543, s1N 936566716,
   s1P 1430815529, s1P 2199945275, s1N 1394750548, s1P 1670675481, s1P 3557370807,
   s1N 329248803, s1N 6234168537, s1N 1292951741, s1N 3167571270, s1P 1026407319,
   s1N 180655358, s1N 3759035803, s1N 4453427076, s1N 2085165078, s1N 1122735456,
   s1N 11584072801, s1N 12404434694, s1N 1851594316, s1P 7663248858, s1N 205617786,
   s1N 1041243173, s1N 2725899676, s1N 3669410424, s1N 5167865471, s1N 320392086,
   s1N 15025688550, s1N 8438755257, s1N 15290230264, s1N 24412468, s1P 182628815,
   s1N 19474255291, s1N 21591623031, s1N 613669914, s1N 5460121684, s1P 15838955779,
   s1P 20256185138, s1P 8857603663, s1P 21878202607, s1P 42030803116]
private def s1St9VecS3 : List ℤ :=
  [s1P 25141690918, s1P 17734567506, s1P 26738331993, s1P 19016825831, s1N 13132981163,
   s1N 8488006356, s1N 9478839894, s1P 5246306033, s1N 3529900472, s1N 3282481419,
   s1N 2153101210, s1P 7687425676, s1N 6806342581, s1N 7980015052, s1N 8392513973,
   s1P 6198153389, s1P 2671791942, s1P 1619654601, s1P 2722240719, s1P 6877144750,
   s1N 5717934466, s1P 3875102429, s1P 10811348612, s1P 47846299438, s1P 49104348863,
   s1P 18684141239, s1P 1336822529, s1N 16055715215, s1N 8952319627, s1P 10105595680,
   s1P 15787745526, s1P 3151646585, s1N 4627223244, s1N 20302542298, s1N 7925681642,
   s1N 24621841018, s1N 37187447434, s1N 4457262950, s1N 15082048032, s1N 766891716,
   s1N 3110941294, s1P 18907807713, s1P 26606137101, s1P 19868483116, s1N 2881179009,
   s1P 3082902071, s1N 7681533132, s1N 11160433475, s1N 5836588132, s1N 7136689892,
   s1P 1392968137, s1P 4867313369, s1P 17273308794, s1P 1099649427, s1N 14269149645,
   s1N 12201014540, s1N 12830214238, s1N 19175502940, s1N 1643691639, s1P 13039207473,
   s1P 4091540881, s1N 18030480266, s1N 32388004471, s1P 17327965501]
private def s1St9VecS4 : List ℤ :=
  [s1N 10440029482, s1P 875797085, s1N 20493294288, s1N 21876923959, s1P 2555898953,
   s1P 24071241903, s1P 20097363030, s1P 18214515962, s1N 6968132377, s1P 6578037606,
   s1N 10209157541, s1P 6125920532, s1P 13113002176, s1P 8116215881, s1N 26045067816,
   s1N 40717075246, s1N 35170464151, s1N 35721180014, s1N 16484909078, s1N 21481049687,
   s1P 4016269790, s1P 14368050425, s1N 21280421009, s1N 4126207887, s1P 1501482657,
   s1P 20763216320, s1P 5361772861, s1N 1643928584, s1N 9899764196, s1N 48455808814,
   s1N 49361727499, s1N 47524980519, s1N 28583834637, s1N 18731847079, s1P 25075748144,
   s1P 32560988421, s1P 22588555129, s1P 26001735738, s1N 30871313283, s1N 60397390876,
   s1N 25225713449, s1N 33788557411, s1N 45144650786, s1N 96761029786, s1N 108627310303,
   s1P 2455151162, s1N 34291087679, s1N 48369751293, s1N 21336981063, s1P 59760524118,
   s1P 118785710006, s1N 41157742349, s1P 105790910465, s1N 28345337010, s1N 135319220147,
   s1N 43551120936, s1P 43290506825, s1P 20255109972, s1P 9588427781, s1N 108824547379,
   s1N 44083978497, s1P 93005788796, s1N 51606877804, s1P 85156843446]
private def s1St9VecS5 : List ℤ :=
  [s1N 16297000250, s1N 50013844014, s1P 2373074566, s1N 113259155933, s1N 39276740806,
   s1N 85375741963, s1P 227254111211, s1N 247442099394, s1N 202617671804, s1P 226768174475,
   s1N 172234991133, s1N 15292614864, s1P 74087789380, s1N 246640384643, s1P 123336741699,
   s1N 16971568586, s1N 131245840702, s1P 19089153849, s1N 14964943096, s1P 211297563786,
   s1N 115946023793, s1P 93394978655, s1N 155915327164, s1N 28960049135, s1P 347461760453,
   s1N 225845030172, s1P 96161895388, s1P 224235881032, s1N 191925572318, s1N 132200571523,
   s1N 127816061359, s1N 203275650264, s1N 186488037798, s1P 4431409781, s1N 212370726582,
   s1N 141470301512, s1P 334971430304, s1P 536275170176, s1N 395378843791, s1P 353286596622,
   s1P 304205087355, s1P 54700464707, s1P 372149240498, s1P 231561074162, s1P 160593105569,
   s1P 556395503152, s1N 151137412195, s1P 350731858648, s1P 266410325243, s1P 54640506876,
   s1N 115548180353, s1N 281137185363, s1N 477222874521, s1P 286171948571, s1N 416047449115,
   s1N 464832527869, s1P 205722675410, s1N 608150818911, s1P 1273952966758, s1N 213789242018,
   s1N 525942392802, s1N 532040464414, s1N 501753600513, s1P 292192961230]
private def s1St9VecS6 : List ℤ :=
  [s1P 551233014305, s1P 741800749121, s1N 961253655108, s1N 1307899567431, s1P 8233468446,
   s1N 758000529775, s1N 1248547734024, s1N 1321067582939, s1N 740238820026, s1P 450483130018,
   s1P 893329977196, s1N 221282455258, s1N 1327573020406, s1P 1414776846639, s1P 99706816933,
   s1P 1494864092537, s1N 1482584570698, s1N 2709759663107, s1N 12481880525275,
   s1N 27991906607077, s1N 49853038214404, s1N 78057874483184, s1N 111582857499736,
   s1N 148665339684248, s1N 187099217786794, s1N 223966808644925, s1N 256509293295179,
   s1N 282914619860109, s1N 301866017965190, s1N 311695780090904, s1N 312141227926353,
   s1N 303331949184801, s1N 287324319161200, s1N 265140630755397, s1N 238648443688768,
   s1N 209415864116045, s1N 179058882332315, s1N 149724040229570, s1N 122798783041135,
   s1N 98849039796672, s1N 78256452208190, s1N 60841595434452, s1N 46347374823008,
   s1N 34069718629374, s1N 24245025850479, s1N 16551386116121, s1N 10778890381163,
   s1N 6767473636671, s1N 4070148897308, s1N 2268378398853, s1N 1134590103411,
   s1N 504121177973, s1N 202497169868, s1N 77773814208, s1N 31894249891, s1N 15790881631,
   s1N 9526794839, s1N 6324403148, s1N 4229871610, s1N 2744503942, s1N 1710131958,
   s1N 1022707992, s1N 588782651, s1N 328112926]
private def s1St9VecS7 : List ℤ :=
  [s1N 177873219, s1N 93791168, s1N 47786240, s1N 23311501, s1N 10830212, s1N 4806449,
   s1N 2063932, s1N 874699, s1N 372993, s1N 161542, s1N 70741, s1N 30902, s1N 13270, s1N 5535,
   s1N 2230, s1N 859, s1N 313, s1N 105, s1N 31, s1N 6, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St9VecS8 : List ℤ :=
  [s1P 0]
private def s1St9Vec : List ℤ :=
  s1St9VecS0 ++
  (s1St9VecS1 ++
  (s1St9VecS2 ++
  (s1St9VecS3 ++
  (s1St9VecS4 ++
  (s1St9VecS5 ++
  (s1St9VecS6 ++
  (s1St9VecS7 ++
  (s1St9VecS8))))))))
private def s1Chk10 : List Rkm128kSeg := s1Take 3 s1Rem10
private def s1Rem11 : List Rkm128kSeg := s1Drop 3 s1Rem10
private def s1St10VecS0 : List ℤ :=
  [s1P 112705, s1P 883406, s1N 592532, s1P 872659, s1P 1336416, s1P 678743, s1N 3485,
   s1N 2848668, s1P 54926, s1N 576877, s1N 163550, s1N 148422, s1N 1188426, s1N 544387,
   s1N 13604952, s1N 1051, s1N 6482067, s1N 7592072, s1P 14926587, s1P 3177356, s1N 11866036,
   s1P 12301844, s1P 29938, s1N 1007305, s1N 4161447, s1N 8599957, s1P 400503, s1N 4776899,
   s1N 30225064, s1N 24303957, s1P 16416808, s1N 36938593, s1P 25671403, s1N 6334732,
   s1P 28652411, s1N 8590771, s1N 24665116, s1P 12485510, s1N 10681701, s1P 3593975,
   s1P 20530592, s1P 62297883, s1N 20205765, s1N 6956459, s1N 61046456, s1P 16548957,
   s1N 30411565, s1N 39149959, s1N 32414104, s1P 86067299, s1P 29796843, s1N 147033471,
   s1N 11448876, s1N 1757999, s1N 30075106, s1P 909265, s1P 151916760, s1P 50404660,
   s1P 90644452, s1P 162314252, s1P 85977588, s1P 24984069, s1P 11010327, s1P 2156997]
private def s1St10VecS1 : List ℤ :=
  [s1N 56941392, s1N 83490991, s1N 38209107, s1P 51920486, s1P 85099580, s1N 150435122,
   s1N 269008497, s1N 193643539, s1N 376927134, s1N 162785578, s1N 169202981, s1N 144276997,
   s1N 327383314, s1N 650179397, s1N 34189386, s1N 149631038, s1N 218008913, s1P 129256498,
   s1P 194402227, s1P 68819291, s1P 515753250, s1N 323693651, s1N 111553082, s1N 41550164,
   s1N 67079038, s1P 95925001, s1P 418723740, s1N 333747220, s1N 807375310, s1N 881545188,
   s1N 181934931, s1P 555699244, s1P 87958157, s1P 26653053, s1P 449382958, s1N 83140011,
   s1N 340328149, s1N 108792288, s1P 968299867, s1P 341473067, s1P 787215388, s1P 4528033,
   s1N 1023669666, s1P 544110517, s1P 13527792, s1N 395459089, s1P 331574200, s1N 1296624645,
   s1N 24616124, s1N 553976079, s1N 372002180, s1P 823446503, s1P 146994563, s1N 1765393304,
   s1N 3257730589, s1N 2482599114, s1N 1718066972, s1N 2264401654, s1N 1282753145,
   s1N 2823319315, s1N 2918839989, s1N 2787501588, s1N 381567748, s1P 1155161352]
private def s1St10VecS2 : List ℤ :=
  [s1P 3194977450, s1P 3595865301, s1N 4393005309, s1P 3260326375, s1N 421006557,
   s1P 2330826053, s1P 3294289133, s1N 6490914149, s1P 6118428977, s1N 249986588,
   s1N 2372358987, s1P 8435019007, s1P 3916049563, s1N 26614013, s1P 238529510, s1P 436826308,
   s1P 8750629545, s1P 11572721569, s1P 1596476530, s1N 503869097, s1N 2074798104,
   s1P 9394755495, s1P 6171145519, s1N 6030596496, s1N 781929073, s1P 310660824,
   s1P 8962797863, s1N 112525132, s1P 2254069178, s1N 579072450, s1N 3563806171,
   s1N 3483491776, s1P 1759768107, s1N 966394129, s1N 4268286057, s1N 105340015,
   s1N 1865624829, s1N 2006371868, s1P 7621713781, s1P 2595032395, s1P 1112661545,
   s1N 1683700748, s1P 4203551719, s1P 6172696954, s1P 9893481459, s1N 6072919895,
   s1P 1578478239, s1P 14937681102, s1N 1890921269, s1N 9375073775, s1P 3090147017,
   s1N 2711281388, s1N 7098972413, s1N 353131212, s1N 5143504917, s1N 9477950532,
   s1N 3647331119, s1N 970742075, s1P 10546147717, s1P 27096577153, s1P 13476906490,
   s1P 5858142224, s1P 648455191, s1P 14938012788]
private def s1St10VecS3 : List ℤ :=
  [s1P 15771827178, s1P 662388133, s1N 27324106869, s1N 2309170974, s1N 11540253801,
   s1N 14312521870, s1N 10165851831, s1N 6436419229, s1P 2227467742, s1P 17206836295,
   s1P 22437013828, s1N 15561683868, s1N 16921791767, s1N 15675804472, s1N 4854784567,
   s1N 26350580938, s1P 26051197782, s1N 33193511983, s1N 5951148873, s1N 12155404139,
   s1N 6375748096, s1N 10733245504, s1P 749585932, s1P 5300798377, s1P 2447469760,
   s1N 6542792527, s1N 5959348566, s1N 1389413848, s1P 16163105200, s1P 2173899928,
   s1N 1672687195, s1P 13367345007, s1N 1316130733, s1N 25743279925, s1N 6467801779,
   s1P 15238598013, s1P 35157676313, s1P 19239433765, s1N 10808664785, s1N 13204894591,
   s1N 46340501440, s1N 17829575474, s1P 30186005079, s1N 6830231666, s1N 17664145995,
   s1P 10981536526, s1N 15084847763, s1N 22371942319, s1N 37841541911, s1P 10180094557,
   s1N 5828284118, s1N 3584123158, s1N 19379511146, s1P 19187218347, s1P 1149136709,
   s1P 9094639101, s1N 13672147361, s1N 10161217654, s1P 24230450841, s1P 2064787601,
   s1N 23440597017, s1N 33399445234, s1N 1639378189, s1P 3984923778]
private def s1St10VecS4 : List ℤ :=
  [s1N 15639971657, s1P 1204550048, s1N 3099332017, s1N 8170845557, s1P 10621333663,
   s1N 14635508446, s1P 14521873633, s1P 4410028172, s1N 5734816785, s1P 23316442391,
   s1P 7007220820, s1P 21984618916, s1P 7474891053, s1P 9886021477, s1P 5582785714,
   s1N 30587151172, s1N 16015286671, s1N 9312498407, s1P 12877247009, s1P 19319139764,
   s1P 8399858198, s1P 4930792146, s1P 31836175472, s1P 53444692515, s1P 30165375345,
   s1P 6844743172, s1N 21872089531, s1P 9172521314, s1N 12555289873, s1P 9325312408,
   s1N 5345553334, s1N 33278355657, s1N 863898706, s1P 28610815246, s1P 24184940895,
   s1P 56640684877, s1N 13831492070, s1P 52732802591, s1P 32011636487, s1N 39195375379,
   s1P 25209990065, s1N 56202699892, s1N 82977106056, s1P 28706147583, s1N 25200795709,
   s1N 116931214519, s1N 17160404623, s1P 21770627031, s1N 34552887491, s1P 86025797118,
   s1P 122883964739, s1P 24141726048, s1N 544820305, s1N 8109289605, s1N 2949221536,
   s1P 122329091108, s1N 15015885186, s1P 1256578475, s1N 10760165831, s1P 202904771967,
   s1P 107932953349, s1P 21708739085, s1P 258742831316, s1N 40999853836]
private def s1St10VecS5 : List ℤ :=
  [s1N 117443334300, s1P 179683075467, s1N 223953997378, s1P 83985262819, s1P 230169608010,
   s1P 71873419210, s1N 84860717303, s1N 207715315046, s1P 22318436809, s1P 30252103694,
   s1N 163318808914, s1N 243659373513, s1N 2497791825, s1P 124473168578, s1N 54596410701,
   s1P 120130356646, s1N 138566033818, s1N 64097186224, s1P 123988940854, s1P 285173319187,
   s1P 128587152093, s1N 33085748785, s1N 17000150461, s1N 22253312857, s1P 105038791466,
   s1P 154958905256, s1P 181010420075, s1N 249947392741, s1P 184523168001, s1N 454934487520,
   s1N 257600638736, s1P 107830282440, s1N 147203620726, s1P 256256881845, s1P 359137797248,
   s1N 162868040968, s1P 51129258388, s1N 48750203804, s1N 165636452570, s1P 150585880075,
   s1P 487310538697, s1P 321832931595, s1N 168168712530, s1N 550748551470, s1N 214070022131,
   s1P 464553215411, s1N 45109487942, s1N 486948082980, s1P 94943154791, s1N 322034879691,
   s1N 36915217222, s1P 387727646708, s1P 76599214906, s1P 698366274317, s1P 85888150083,
   s1P 377463281321, s1P 485220345697, s1P 788126519405, s1P 436475411062, s1P 570739094287,
   s1N 875984190549, s1P 210898820259, s1N 40413943991, s1P 297499069677]
private def s1St10VecS6 : List ℤ :=
  [s1P 447961297409, s1P 225338036560, s1P 398038613368, s1N 86911257122, s1P 901905779574,
   s1P 1232973477917, s1P 908151441906, s1N 1408747682722, s1P 1805085209641, s1P 784941984710,
   s1P 503264464438, s1N 478830268265, s1P 1642793151101, s1P 1703107783087, s1N 649507190854,
   s1N 1087841865284, s1P 391859820600, s1N 1103218582118, s1P 214026399964, s1P 1288257895596,
   s1N 2191784741723, s1N 1863364378426, s1N 380754237375, s1P 731835652616, s1P 1400491903308,
   s1P 1450789349049, s1P 723286556140, s1P 1248026674953, s1N 469652807722, s1N 2534862949492,
   s1N 1692625222587, s1P 4669745399955, s1P 18741648285203, s1P 41149118424853,
   s1P 71441830976962, s1P 107902514245896, s1P 148359954638672, s1P 190625307409966,
   s1P 231383320422226, s1P 267033754502692, s1P 294945736215096, s1P 313335225123068,
   s1P 321301500241618, s1P 318918388868982, s1P 306886975882417, s1P 286463527191160,
   s1P 259588534848704, s1P 228677352058426, s1P 196227462765577, s1P 164462342027284,
   s1P 134981286170319, s1P 108585146719736, s1P 85472611963679, s1P 65614573389064,
   s1P 48963105178118, s1P 35427725766830, s1P 24795939194750, s1P 16731507952483,
   s1P 10834725323390, s1P 6698433732815, s1P 3935101446722, s1P 2189624174968,
   s1P 1152916568623, s1P 575608367528]
private def s1St10VecS7 : List ℤ :=
  [s1P 274178901824, s1P 126115518742, s1P 57155121897, s1P 26249024923, s1P 12585615775,
   s1P 6412484837, s1P 3456128007, s1P 1928305878, s1P 1086589952, s1P 606892535,
   s1P 332097785, s1P 176862674, s1P 91312686, s1P 45595621, s1P 21992401, s1P 10245770,
   s1P 4616065, s1P 2016503, s1P 857010, s1P 356915, s1P 144087, s1P 59714, s1P 23370,
   s1P 7699, s1P 2214, s1P 680, s1P 256, s1P 100, s1P 35, s1P 9, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St10VecS8 : List ℤ :=
  [s1P 0]
private def s1St10Vec : List ℤ :=
  s1St10VecS0 ++
  (s1St10VecS1 ++
  (s1St10VecS2 ++
  (s1St10VecS3 ++
  (s1St10VecS4 ++
  (s1St10VecS5 ++
  (s1St10VecS6 ++
  (s1St10VecS7 ++
  (s1St10VecS8))))))))
private def s1Chk11 : List Rkm128kSeg := s1Take 3 s1Rem11
private def s1Rem12 : List Rkm128kSeg := s1Drop 3 s1Rem11
private def s1St11VecS0 : List ℤ :=
  [s1P 59368, s1N 474142, s1P 971479, s1P 1001625, s1P 1520492, s1P 886550, s1P 1329949,
   s1N 862613, s1N 1178958, s1N 1728232, s1N 1024427, s1N 1160574, s1P 1893871, s1N 1283215,
   s1N 11071996, s1N 5665027, s1N 6495938, s1N 6344133, s1P 4575706, s1P 14365147,
   s1P 11339158, s1N 9249242, s1P 11307162, s1N 514639, s1P 4034692, s1N 9026963, s1N 8455890,
   s1N 4742411, s1N 4275044, s1N 10573489, s1N 4083108, s1P 7206041, s1P 40687065,
   s1P 51666783, s1P 18807634, s1N 19418582, s1P 26564584, s1N 288663, s1N 3001929,
   s1P 23550490, s1N 29745354, s1P 51553389, s1P 66823897, s1N 11330093, s1P 13494022,
   s1P 38446430, s1N 44268887, s1N 67149035, s1N 31802810, s1N 32418945, s1N 18903037,
   s1N 81438109, s1N 78642800, s1N 69495520, s1N 64800306, s1N 11556412, s1P 50940829,
   s1P 73145170, s1N 16205464, s1N 79378871, s1P 82396606, s1P 153112703, s1N 78991919,
   s1P 65092375]
private def s1St11VecS1 : List ℤ :=
  [s1P 74295, s1P 53850196, s1N 31753342, s1N 102014493, s1N 155268422, s1N 78937493,
   s1P 77180207, s1P 141540384, s1P 296491020, s1P 377864101, s1P 355551677, s1P 393203621,
   s1P 84659586, s1N 104468115, s1N 52933324, s1N 87895938, s1N 456970503, s1N 255005650,
   s1N 167298040, s1N 7425855, s1N 408129067, s1N 522688384, s1P 100301666, s1N 168648087,
   s1N 294041522, s1P 144341002, s1P 26637197, s1P 318352952, s1P 44293721, s1N 387341027,
   s1P 43211697, s1P 18788807, s1P 443243906, s1N 19759115, s1P 1059957454, s1N 203954973,
   s1P 44753558, s1N 221282862, s1N 680489166, s1P 602479204, s1N 56977712, s1N 81105024,
   s1N 31690841, s1N 1262685359, s1N 1070945720, s1P 672011703, s1P 37390563, s1P 738830878,
   s1P 580338511, s1P 686312153, s1N 393107765, s1N 390978278, s1N 439445539, s1P 7641044,
   s1P 797745267, s1P 633216596, s1P 712099855, s1P 1882542748, s1P 2504609018, s1P 1792439509,
   s1P 1856419472, s1P 2293466786, s1P 1014906216, s1N 1616319431]
private def s1St11VecS2 : List ℤ :=
  [s1N 660070650, s1P 634692732, s1P 4517776853, s1P 5090538741, s1P 2477221939,
   s1P 3122441645, s1N 412402359, s1N 2449539330, s1N 7683072725, s1N 6685543636,
   s1N 6679109657, s1N 2590360838, s1N 2240336754, s1N 934660704, s1P 3616867842,
   s1N 3562282752, s1N 2600317854, s1N 1790453181, s1P 3160630982, s1P 3525846286,
   s1P 5267855862, s1P 1038299615, s1P 8062150326, s1P 13480578541, s1P 2116996669,
   s1P 2043108482, s1P 9721865805, s1P 6219889079, s1N 2666492566, s1N 447389236,
   s1N 3181419870, s1N 3943075663, s1P 2500737709, s1N 903597404, s1N 962195118, s1P 862911613,
   s1P 618947140, s1N 6625048033, s1P 1683466192, s1N 3949078730, s1P 2163855036,
   s1P 2614807956, s1P 5280645614, s1P 5300731043, s1P 274981540, s1N 2801997638,
   s1N 6853132199, s1N 3662391365, s1N 8657909910, s1N 6873886384, s1P 1957055000,
   s1P 18637774653, s1P 6510277592, s1N 688730785, s1P 5509589788, s1N 3212376081,
   s1P 5570152161, s1P 5041872172, s1P 4398467426, s1N 306313288, s1P 15818795434,
   s1P 4680476608, s1N 16694495165, s1N 7050494979]
private def s1St11VecS3 : List ℤ :=
  [s1N 8535924403, s1N 4505298231, s1N 17803824036, s1N 8749204940, s1N 2457698089,
   s1N 5030360175, s1N 12792572052, s1N 28288758703, s1N 7162991816, s1N 37413812813,
   s1N 1588024354, s1P 13584992845, s1N 278636872, s1P 7764662453, s1N 1028704611,
   s1P 8789934161, s1N 21212570069, s1N 12795809142, s1N 41314637956, s1N 21471305943,
   s1N 14821534367, s1P 2180973958, s1P 4665943342, s1P 1414122834, s1N 5358903204,
   s1N 6315009511, s1N 154325785, s1P 11280157267, s1N 8900202044, s1N 12639725084,
   s1N 19552488018, s1N 8007055573, s1P 4603686572, s1P 23641016117, s1P 11097901513,
   s1N 29983015335, s1N 11791388360, s1N 14063401496, s1P 20612090847, s1P 15672977996,
   s1N 14319786191, s1P 3710956148, s1P 6877274367, s1N 6686796284, s1N 1684720210,
   s1P 5001532864, s1N 12226423267, s1N 13751522454, s1N 20937189894, s1P 36257901208,
   s1P 40244081013, s1P 25998822798, s1N 415282171, s1N 12959591908, s1P 7670749127,
   s1N 16544592503, s1N 30955784019, s1N 11502782785, s1P 17380699551, s1P 17440222952,
   s1P 11244497586, s1N 26895933887, s1N 7068357180, s1P 9037551986]
private def s1St11VecS4 : List ℤ :=
  [s1P 12094367339, s1P 3221880581, s1P 1274921698, s1P 32933926082, s1P 35328013038,
   s1P 21133737642, s1P 9612863508, s1N 2338750335, s1N 10887198087, s1N 18801969642,
   s1N 6657193183, s1N 12115812591, s1N 18005097767, s1N 10595158002, s1P 7104116817,
   s1N 4164547048, s1N 1680071494, s1N 8119779264, s1P 13974892562, s1P 6886903463,
   s1N 1844277144, s1P 15617947428, s1P 32259752755, s1P 24519723147, s1P 41867885401,
   s1P 30926515507, s1P 15406673312, s1N 44259610277, s1N 7339719182, s1P 3604387376,
   s1N 14912631991, s1P 13683026043, s1P 17698320133, s1N 10013126409, s1N 35185503170,
   s1N 14694057786, s1N 17795520740, s1N 24797620162, s1P 37701391528, s1P 74998274949,
   s1P 11110482361, s1N 21835893447, s1N 26923880583, s1P 63178678934, s1P 48254805501,
   s1N 23907991055, s1P 108150717081, s1P 63320817608, s1N 24279185501, s1N 28747620400,
   s1N 71998729918, s1N 41389269621, s1N 29334470992, s1N 64590793118, s1P 4306727916,
   s1P 108388283383, s1P 89626529033, s1N 147869117494, s1P 86283690525, s1P 195319962668,
   s1N 141828411971, s1N 108124114460, s1P 198405918131, s1N 39605941159]
private def s1St11VecS5 : List ℤ :=
  [s1N 294877096483, s1N 21777467251, s1P 181679707818, s1P 47132730906, s1N 75131029136,
   s1P 31943660179, s1P 17597066847, s1P 9179586258, s1N 67348726375, s1P 217717371118,
   s1P 2507089509, s1P 103665765624, s1N 32801306644, s1P 109881192639, s1N 143779262588,
   s1P 6788422008, s1P 225818439182, s1P 77180706898, s1P 204471527647, s1P 92265175130,
   s1P 338069075423, s1P 194750995859, s1P 133708200860, s1N 252724535967, s1N 238852611197,
   s1N 150233355964, s1P 63216329934, s1N 100097685454, s1N 38797216661, s1N 211750429360,
   s1N 346910696291, s1N 318860566281, s1P 156023533684, s1N 7866387140, s1N 38946966487,
   s1N 37938398133, s1P 270851065954, s1P 146690455298, s1N 176328765025, s1P 113041760524,
   s1N 422202881628, s1P 17546849264, s1N 487154625562, s1P 93021009705, s1P 728183317612,
   s1P 522273890716, s1N 195857405646, s1N 478743366425, s1N 105425035146, s1P 240739412977,
   s1N 130404950906, s1N 51386011577, s1N 379190079738, s1N 492305948597, s1N 282765866997,
   s1P 76479657806, s1N 414076636883, s1N 416143301009, s1N 1035466285067, s1N 13546052386,
   s1N 462878754182, s1N 298451857833, s1N 260443429250, s1P 132723531101]
private def s1St11VecS6 : List ℤ :=
  [s1P 91482724316, s1N 269171929790, s1P 983785461445, s1P 626938855027, s1N 223638136284,
   s1P 360331964679, s1P 1240962577754, s1P 248954514831, s1P 1221657044713, s1P 334873802217,
   s1P 260081631686, s1P 2986427036210, s1P 847572307421, s1P 303948256979, s1P 975923344620,
   s1N 955770247760, s1N 1051051742254, s1P 385621134174, s1P 555580059654, s1P 430527356321,
   s1P 1410320463245, s1P 1648841406964, s1P 670358712661, s1P 417229586218, s1P 693325661729,
   s1P 692536639616, s1P 662612516736, s1P 54196431616, s1N 656396183947, s1N 1006860297013,
   s1N 1756089290124, s1N 528562319460, s1N 2446234238959, s1N 409302752558, s1P 2983144768262,
   s1P 1629388771596, s1N 1873899145842, s1P 2636912416813, s1P 5911478640866,
   s1P 2651757004146, s1P 990557283095, s1P 2019184917719, s1P 14768247400100,
   s1P 37694754004865, s1P 70094602825860, s1P 110257848663753, s1P 155258799306099,
   s1P 201300126315289, s1P 244431046352130, s1P 281135898797726, s1P 308673843460850,
   s1P 325225070518923, s1P 329897240001045, s1P 322754389338833, s1P 304954436019062,
   s1P 278765744504726, s1P 247182166332331, s1P 213230339810702, s1P 179375672667467,
   s1P 147312412127615, s1P 118079408650863, s1P 92267633180678, s1P 70162325634297,
   s1P 51810145703241]
private def s1St11VecS7 : List ℤ :=
  [s1P 37057525620978, s1P 25602641656214, s1P 17027581987821, s1P 10880096993228,
   s1P 6646507574925, s1P 3891175560852, s1P 2173079382732, s1P 1154294715444,
   s1P 591522915526, s1P 294597057022, s1P 139322111320, s1P 60666601353, s1N 24374243906,
   s1P 9621029380, s1P 4171290499, s1P 2110977442, s1P 1178676942, s1P 667677865,
   s1P 367677198, s1P 194723942, s1P 99252310, s1P 48810752, s1P 23197160, s1P 10661290,
   s1P 4741621, s1P 2043266, s1P 854430, s1P 346920, s1P 136540, s1P 51900, s1P 18974,
   s1P 6654, s1P 2237, s1P 718, s1P 219, s1P 60, s1P 13, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1St11VecS8 : List ℤ :=
  [s1P 0]
private def s1St11Vec : List ℤ :=
  s1St11VecS0 ++
  (s1St11VecS1 ++
  (s1St11VecS2 ++
  (s1St11VecS3 ++
  (s1St11VecS4 ++
  (s1St11VecS5 ++
  (s1St11VecS6 ++
  (s1St11VecS7 ++
  (s1St11VecS8))))))))
private def s1Chk12 : List Rkm128kSeg := s1Rem12
private theorem s1Chk0_ok :
    s1RunAt s1Chk0 hm256k512krS1LIn hm256k512krS1DCurIn
      hm256k512krS1PadIn hm256k512krS1VecIn
      2 512 590525035 s1St0Vec = true := by decide +kernel
private theorem s1Chk1_ok :
    s1RunAt s1Chk1 2 512
      590525035 s1St0Vec
      2 512 611850723 s1St1Vec = true := by decide +kernel
private theorem s1Chk2_ok :
    s1RunAt s1Chk2 2 512
      611850723 s1St1Vec
      2 512 640642590 s1St2Vec = true := by decide +kernel
private theorem s1Chk3_ok :
    s1RunAt s1Chk3 2 512
      640642590 s1St2Vec
      4 512 665040278 s1St3Vec = true := by decide +kernel
private theorem s1Chk4_ok :
    s1RunAt s1Chk4 4 512
      665040278 s1St3Vec
      4 512 689629359 s1St4Vec = true := by decide +kernel
private theorem s1Chk5_ok :
    s1RunAt s1Chk5 4 512
      689629359 s1St4Vec
      4 512 709463702 s1St5Vec = true := by decide +kernel
private theorem s1Chk6_ok :
    s1RunAt s1Chk6 4 512
      709463702 s1St5Vec
      4 512 730037231 s1St6Vec = true := by decide +kernel
private theorem s1Chk7_ok :
    s1RunAt s1Chk7 4 512
      730037231 s1St6Vec
      4 512 749238660 s1St7Vec = true := by decide +kernel
private theorem s1Chk8_ok :
    s1RunAt s1Chk8 4 512
      749238660 s1St7Vec
      4 512 770963464 s1St8Vec = true := by decide +kernel
private theorem s1Chk9_ok :
    s1RunAt s1Chk9 4 512
      770963464 s1St8Vec
      4 512 782763497 s1St9Vec = true := by decide +kernel
private theorem s1Chk10_ok :
    s1RunAt s1Chk10 4 512
      782763497 s1St9Vec
      4 512 818880963 s1St10Vec = true := by decide +kernel
private theorem s1Chk11_ok :
    s1RunAt s1Chk11 4 512
      818880963 s1St10Vec
      4 512 841593287 s1St11Vec = true := by decide +kernel
private theorem s1Chk12_ok :
    s1RunAt s1Chk12 4 512
      841593287 s1St11Vec
      hm256k512krS1LOut hm256k512krS1DCurOut
      hm256k512krS1PadOut hm256k512krS1Vec = true := by decide +kernel

/-- Segment count of hm256k512krS1Segs (31 segments). -/
theorem hm256k512krS1_len : rkm128kSegListLen hm256k512krS1Segs = 31 := by
  rfl

/-- Exact rkm128kRunSegs 256 4 512 step across hm256k512krS1Segs (segs 59..89). -/
theorem hm256k512krS1_step :
    rkm128kRunSegs 256 4 512 hm256k512krS1Segs hm256k512krS1LIn
      hm256k512krS1DCurIn hm256k512krS1PadIn hm256k512krS1VecIn =
      (hm256k512krS1LOut, hm256k512krS1DCurOut,
       hm256k512krS1PadOut, hm256k512krS1Vec) := by
  exact s1RunStepTd s1Chk0_ok
    (s1RunStepTd s1Chk1_ok
    (s1RunStepTd s1Chk2_ok
    (s1RunStepTd s1Chk3_ok
    (s1RunStepTd s1Chk4_ok
    (s1RunStepTd s1Chk5_ok
    (s1RunStepTd s1Chk6_ok
    (s1RunStepTd s1Chk7_ok
    (s1RunStepTd s1Chk8_ok
    (s1RunStepTd s1Chk9_ok
    (s1RunStepTd s1Chk10_ok
    (s1RunStepTd s1Chk11_ok
    (s1RunLast s1Chk12_ok))))))))))))

/-- Suffix chaining lemma advancing rkm128kRunSegs 256 4 512 past hm256k512krS1Segs. -/
theorem hm256k512krS1_run_after (rest : List Rkm128kSeg) :
    rkm128kRunSegs 256 4 512 (hm256k512krS1Segs ++ rest) hm256k512krS1LIn
      hm256k512krS1DCurIn hm256k512krS1PadIn hm256k512krS1VecIn =
      rkm128kRunSegs 256 4 512 rest hm256k512krS1LOut hm256k512krS1DCurOut
        hm256k512krS1PadOut hm256k512krS1Vec := by
  rw [rkm128kRunSegs_append]
  dsimp only
  rw [hm256k512krS1_step]

end

end Rk128kHiM256K512KrPt1
end QuantumComputation.Specs.GroverFindAll
