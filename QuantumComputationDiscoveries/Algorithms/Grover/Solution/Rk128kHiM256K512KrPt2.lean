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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM64K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM128K128KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K512KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256K512KrPt0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K512KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM4K512L248KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K512KrPt0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM256K512KrPt1
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K512KrPt0
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kHiM1024F256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM64K256KrCert
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kLowM4K512L248KrPt2
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM16K512KrPt2
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kMidM32K512KrPt2

/-
# `(256, 512)` `RampKick128k` Krotov Part 2 (`Rk128kHiM256K512KrPt2`)

Certifies Slice 2 (`r = 512` segments `90..122`, `33` segments, `434,688` F1272 /
`435,537 <= 450,000` Horner coord-ops, `dk = 12`, `lTableMax = 4`, `degP <= 64`).
-/

namespace QuantumComputation.Specs.GroverFindAll
namespace Rk128kHiM256K512KrPt2

@[expose] public section

open QuantumComputation.Specs.DickeSol

/-- Unmodified segments 90..122 (33 segs) of (256, 512) r = 512 (lTableMax = 4). -/
def hm256k512krS2Segs : List Rkm128kSeg := [
  ⟨4, 189771, 1, 23, rkm128kMask56 510
    [59238898789786582, 30575388340976506, 19048081183393911, 45850188308617758,
     7469117594771691, 40828206914004158, 35665890903081, 1104895296193, 0, 34]⟩,
  ⟨4, 176802, 1, 22, rkm128kMask56 513
    [24189234144825799, 48330759043240977, 65440586696773600, 59815347912224055,
     36323455073152745, 67787766598370126, 43764621449353540, 72042183475617698,
     72057594037927935, 479]⟩,
  ⟨4, 178776, 1, 22, rkm128kMask56 510
    [34142607320429544, 42349004649447681, 2999623178888079, 1706950509318612,
     63208089260947550, 10416850204664000, 2255648398192062, 105734168124496, 0, 34]⟩,
  ⟨4, 175539, 1, 22, rkm128kMask56 513
    [5430758383600641, 12933545652164046, 32910718477792352, 69070528795157693,
     8529066581952706, 34595412020280377, 67551511515768427, 71213099313716734,
     72057594037927935, 507]⟩,
  ⟨4, 173512, 1, 22, rkm128kMask56 512
    [981113602053577, 19729508167352357, 21424057136924197, 33533382817292372,
     36266603098769120, 2118713082947337, 69951070541204241, 4522034442325186, 0, 128]⟩,
  ⟨4, 176306, 1, 22, rkm128kMask56 513
    [44392508999648235, 33830943826937270, 26106821515126955, 745893977234809,
     58434447958506427, 46845402128501369, 67476871060770296, 17240168104328684,
     36028659580010495, 503]⟩,
  ⟨4, 193527, 1, 23, rkm128kMask56 512
    [70554621841034412, 11989338878386287, 37297077031505600, 51938353587797280,
     18201360462269593, 8502092092992, 11296469685765978, 2392597713127982, 36028797018963974,
     128]⟩,
  ⟨4, 195430, 1, 24, rkm128kMask56 513
    [13355325776428193, 6195624949318299, 51205841270296046, 24754520608518023,
     60103639261678090, 42212445711160706, 25009196084228931, 72057589723050660,
     72057585447993343, 511]⟩,
  ⟨4, 175786, 1, 22, rkm128kMask56 513
    [23011957974255628, 69449732516382940, 31438338080046546, 13148062804819058,
     65601262732240960, 15639207805995767, 29201532371857023, 44978546451601356,
     63050326063710201, 367]⟩,
  ⟨4, 211968, 1, 25, rkm128kMask56 513
    [35583773448402407, 71370009194954563, 44947667692849057, 28503738778734355,
     17941177721816463, 19658927315175444, 71669388846430938, 71776083748159103,
     69805794224240437, 367]⟩,
  ⟨4, 170783, 1, 22, rkm128kMask56 512
    [67779323803795522, 28826949635603028, 63032594135716193, 22303058638929615,
     28530400829123103, 40532275173994988, 69518820875396959, 72042990932335311,
     72057594037927915, 223]⟩,
  ⟨4, 184501, 1, 23, rkm128kMask56 513
    [38311478895574974, 68475975807642737, 71214847089090821, 60165483651380097,
     27143101274450665, 3659209178231808, 20270064065072654, 11330470834495495,
     4503599627370760, 288]⟩,
  ⟨4, 188269, 1, 23, rkm128kMask56 513
    [44987090521756145, 19093603572802293, 34321218193039023, 63914249347633229,
     6327170523435388, 9225676209176901, 18991643156565002, 36952936988279608,
     4503599627928578, 256]⟩,
  ⟨4, 165044, 1, 21, rkm128kMask56 510
    [41900027394592002, 39301625862567919, 63595143195526044, 64261541248893417,
     34711115381573674, 16291160094146429, 1781284133195837, 781302173750569, 9015995351769381,
     32]⟩,
  ⟨4, 257266, 1, 29, rkm128kMask56 510
    [61698111571784234, 57926674603571255, 51791998715275723, 18177167217295817,
     28419558965889410, 19674273572011460, 60176518416499714, 37190902297963131, 16777228, 32]⟩,
  ⟨4, 226074, 1, 26, rkm128kMask56 511
    [28822058320387077, 36725056727437808, 2537039644511717, 20640922962076622,
     66572550723715132, 64104895401085347, 5499896867079312, 4504195434425921, 80, 64]⟩,
  ⟨4, 256411, 1, 28, rkm128kMask56 511
    [5492314462479472, 16186391493853098, 69372645932947019, 6130088590803520,
     1268221336983043, 6061791733017024, 45128571778277904, 992626469074515, 4503599665119256,
     64]⟩,
  ⟨4, 256622, 1, 28, rkm128kMask56 502
    [54645025558062821, 37702108937032767, 35769045719425075, 27141565557371293,
     724686485331711, 194212005897747, 4421044621477138, 189598376755286, 9007214488488067]⟩,
  ⟨4, 227769, 1, 26, rkm128kMask56 484
    [4852496966272902, 26907155319438857, 12348427791046783, 43210801993815712,
     26812335936513666, 28341334449530064, 33550640758665632, 2550926347939125, 34435292472]⟩,
  ⟨4, 259172, 1, 28, rkm128kMask56 509
    [39451854037615414, 30435251998460993, 66446574289452034, 4700273939081980,
     23636460500162009, 4601631287477073, 68660216002094224, 54131757080224681, 274878513314,
     16]⟩,
  ⟨4, 249395, 1, 28, rkm128kMask56 484
    [70592824746271442, 57858164997407297, 52964677880583137, 135754857873769, 245645849910514,
     63065413982037446, 2968039943307268, 4299667574698894, 36784570373]⟩,
  ⟨4, 179114, 1, 22, rkm128kMask56 507
    [48832961843379943, 15137772397069060, 498715844978716, 28036412044356707,
     14710032788743376, 34486804724356224, 41900591132445745, 20961171500103537, 6678691218400,
     4]⟩,
  ⟨4, 251205, 1, 28, rkm128kMask56 477
    [69330558917952680, 5480638483782883, 2424244472551743, 46786444891168186,
     56930017007007486, 7848535416388610, 36281781416577842, 11386576146828528, 340296424]⟩,
  ⟨4, 137525, 1, 18, rkm128kMask56 509
    [47068008851165176, 37755425596544868, 28457348009778153, 46615333279415675,
     863379701571717, 709061054300992, 58412058103380742, 6720571556169047, 35188667056740, 16]⟩,
  ⟨4, 318998, 1, 33, rkm128kMask56 482
    [66920544914206228, 17629440714602629, 69244196815509446, 11318827117110636,
     18254335001986555, 646703972624678, 62803860749582980, 30527512707583, 10754235206]⟩,
  ⟨4, 267019, 1, 29, rkm128kMask56 510
    [12473339368323338, 16941006209521161, 37698560069484632, 7619745991742822,
     13414138562559480, 60605291378352448, 60970354443863817, 67163702584454911,
     1746655587121528, 32]⟩,
  ⟨4, 318978, 1, 33, rkm128kMask56 512
    [3456303492168110, 32389555319378411, 53348409140950707, 70784871185904394,
     34298258465824797, 67275820664621057, 71129560790392021, 664726062128268,
     4503603549244689, 128]⟩,
  ⟨4, 317817, 1, 33, rkm128kMask56 503
    [61165813314115414, 23419177447840791, 31526416369854434, 52224492963397649,
     9418163613730127, 50409894857157132, 38227944842657285, 2003634654418464,
     18577350610403970]⟩,
  ⟨4, 252266, 1, 27, rkm128kMask56 487
    [49971017734490225, 61913457912995335, 6850251573133312, 66138468304494160,
     14607631804020696, 65021836319890088, 6933877210259486, 12495883769421907, 276497453165]⟩,
  ⟨4, 279441, 1, 30, rkm128kMask56 506
    [15760122696753714, 43785416444489306, 53628416997691803, 53493857650379982,
     56058773180425426, 8965487363022849, 56650203570341197, 16329313690708857,
     7651324885411904, 3]⟩,
  ⟨4, 306517, 1, 32, rkm128kMask56 507
    [70460345899933751, 53776326796127040, 37189161421976343, 63020172823120173,
     779370272681720, 69893944536748266, 63377972402688063, 9078724137145375, 1109183693838, 4]⟩,
  ⟨4, 241273, 1, 27, rkm128kMask56 508
    [16118810276705750, 55023574373329520, 17321475885453821, 8987682688211952,
     5774400819194374, 54590704487771028, 200723939963067, 10998578403424699,
     67225113047085638, 15]⟩,
  ⟨4, 254526, 1, 28, rkm128kMask56 491
    [18570002492018374, 64354930723600157, 21472605408368577, 58985699327209276,
     12869226035449, 53240359214115080, 68790402485024966, 3464092746588368, 4398656553030]⟩]

/-- Input multiplicity lIn = 4 entering hm256k512krS2Segs (after seg 89). -/
def hm256k512krS2LIn : ℕ := 4
/-- Input truncated dimension dCurIn = 512 entering hm256k512krS2Segs. -/
def hm256k512krS2DCurIn : ℕ := 512
/-- Input 10 ^ 15-scaled error pad padIn = 856402969 entering hm256k512krS2Segs. -/
def hm256k512krS2PadIn : ℕ := 856402969

/-- Slice 0 (64 entries) of hm256k512krS2VecIn. -/
def hm256k512krS2VecIn0 : List ℤ :=
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
/-- Slice 1 (64 entries) of hm256k512krS2VecIn. -/
def hm256k512krS2VecIn1 : List ℤ :=
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
/-- Slice 2 (64 entries) of hm256k512krS2VecIn. -/
def hm256k512krS2VecIn2 : List ℤ :=
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
/-- Slice 3 (64 entries) of hm256k512krS2VecIn. -/
def hm256k512krS2VecIn3 : List ℤ :=
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
/-- Slice 4 (64 entries) of hm256k512krS2VecIn. -/
def hm256k512krS2VecIn4 : List ℤ :=
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
/-- Slice 5 (64 entries) of hm256k512krS2VecIn. -/
def hm256k512krS2VecIn5 : List ℤ :=
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
/-- Slice 6 (64 entries) of hm256k512krS2VecIn. -/
def hm256k512krS2VecIn6 : List ℤ :=
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
/-- Slice 7 (64 entries) of hm256k512krS2VecIn. -/
def hm256k512krS2VecIn7 : List ℤ :=
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
/-- Slice 8 (1 entries) of hm256k512krS2VecIn. -/
def hm256k512krS2VecIn8 : List ℤ :=
  [Int.ofNat 0]
/-- Input 513-entry fixed-point amplitude vector entering hm256k512krS2Segs. -/
def hm256k512krS2VecIn : List ℤ :=
  hm256k512krS2VecIn0 ++
  (hm256k512krS2VecIn1 ++
  (hm256k512krS2VecIn2 ++
  (hm256k512krS2VecIn3 ++
  (hm256k512krS2VecIn4 ++
  (hm256k512krS2VecIn5 ++
  (hm256k512krS2VecIn6 ++
  (hm256k512krS2VecIn7 ++
  (hm256k512krS2VecIn8))))))))

/-- Output multiplicity lOut = 4 exiting hm256k512krS2Segs (after seg 122). -/
def hm256k512krS2LOut : ℕ := 4
/-- Output truncated dimension dCurOut = 512 exiting hm256k512krS2Segs. -/
def hm256k512krS2DCurOut : ℕ := 512
/-- Output 10 ^ 15-scaled error pad padOut = 1167040741 exiting hm256k512krS2Segs. -/
def hm256k512krS2PadOut : ℕ := 1167040741

/-- Slice 0 (64 entries) of hm256k512krS2Vec. -/
def hm256k512krS2Vec0 : List ℤ :=
  [Int.ofNat 12286, Int.ofNat 14087, Int.ofNat 6234, Int.negSucc 25862, Int.negSucc 14216,
   Int.ofNat 14315, Int.ofNat 138596, Int.ofNat 18886, Int.ofNat 176688, Int.ofNat 161868,
   Int.negSucc 78191, Int.negSucc 110530, Int.negSucc 167049, Int.ofNat 31611,
   Int.ofNat 125651, Int.ofNat 52355, Int.ofNat 97722, Int.ofNat 280195, Int.ofNat 332659,
   Int.ofNat 379884, Int.ofNat 444584, Int.ofNat 374391, Int.ofNat 75372, Int.ofNat 444477,
   Int.negSucc 9466, Int.ofNat 337455, Int.ofNat 729096, Int.ofNat 1252873, Int.ofNat 817592,
   Int.ofNat 668331, Int.negSucc 478725, Int.ofNat 1027516, Int.ofNat 989719, Int.ofNat 883824,
   Int.negSucc 1013173, Int.ofNat 333503, Int.negSucc 1447870, Int.negSucc 325017,
   Int.ofNat 112281, Int.ofNat 979985, Int.ofNat 153516, Int.ofNat 899192, Int.ofNat 2046966,
   Int.negSucc 2834701, Int.negSucc 1807697, Int.negSucc 2942304, Int.negSucc 3320689,
   Int.negSucc 1364429, Int.ofNat 371759, Int.negSucc 1294104, Int.negSucc 1850412,
   Int.negSucc 2086115, Int.negSucc 1354973, Int.negSucc 1717077, Int.negSucc 2603910,
   Int.negSucc 2476552, Int.negSucc 3745203, Int.ofNat 4387883, Int.ofNat 986216,
   Int.ofNat 7343462, Int.negSucc 5203117, Int.negSucc 17819589, Int.negSucc 14270488,
   Int.negSucc 5947904]
/-- Slice 1 (64 entries) of hm256k512krS2Vec. -/
def hm256k512krS2Vec1 : List ℤ :=
  [Int.ofNat 2847887, Int.ofNat 9007320, Int.ofNat 7489689, Int.ofNat 16235896,
   Int.ofNat 8021741, Int.ofNat 4204286, Int.ofNat 3196248, Int.negSucc 5062724,
   Int.negSucc 12257743, Int.ofNat 11693158, Int.negSucc 4363601, Int.negSucc 30020666,
   Int.negSucc 1733629, Int.negSucc 21798575, Int.negSucc 21629665, Int.negSucc 11614279,
   Int.negSucc 9561307, Int.ofNat 1067091, Int.ofNat 16569669, Int.ofNat 21162719,
   Int.ofNat 11950074, Int.ofNat 10937128, Int.ofNat 10429442, Int.ofNat 865798,
   Int.negSucc 14014222, Int.negSucc 16663861, Int.negSucc 9760726, Int.ofNat 24012974,
   Int.ofNat 42534918, Int.ofNat 63696678, Int.ofNat 8762455, Int.negSucc 44563725,
   Int.ofNat 6964644, Int.ofNat 31851417, Int.negSucc 36027207, Int.negSucc 31853000,
   Int.ofNat 34940549, Int.ofNat 35429890, Int.ofNat 45648980, Int.ofNat 15490516,
   Int.ofNat 21816059, Int.negSucc 5526467, Int.negSucc 10162184, Int.negSucc 38288140,
   Int.negSucc 76713948, Int.negSucc 18783334, Int.ofNat 40603064, Int.negSucc 48146766,
   Int.negSucc 25601070, Int.negSucc 16561325, Int.ofNat 105238197, Int.ofNat 267339421,
   Int.ofNat 204843577, Int.ofNat 108129155, Int.ofNat 23044272, Int.negSucc 109755494,
   Int.ofNat 11533695, Int.negSucc 150653994, Int.negSucc 42485079, Int.negSucc 134037511,
   Int.ofNat 125352477, Int.negSucc 104118452, Int.ofNat 51988681, Int.negSucc 122526538]
/-- Slice 2 (64 entries) of hm256k512krS2Vec. -/
def hm256k512krS2Vec2 : List ℤ :=
  [Int.ofNat 47779106, Int.ofNat 134002948, Int.ofNat 57828353, Int.ofNat 27986152,
   Int.negSucc 6155143, Int.negSucc 129243088, Int.negSucc 21398392, Int.ofNat 51596487,
   Int.ofNat 181919549, Int.ofNat 142991577, Int.ofNat 109461863, Int.negSucc 97128423,
   Int.ofNat 209542234, Int.ofNat 313746908, Int.ofNat 84728218, Int.negSucc 191555283,
   Int.ofNat 148153292, Int.ofNat 99816889, Int.negSucc 41845003, Int.ofNat 112386258,
   Int.negSucc 99902976, Int.negSucc 118907822, Int.negSucc 465326160, Int.negSucc 311351361,
   Int.ofNat 112496120, Int.ofNat 512392705, Int.ofNat 147974386, Int.negSucc 100133021,
   Int.negSucc 550576589, Int.negSucc 423841172, Int.ofNat 32544949, Int.ofNat 88007300,
   Int.negSucc 177701838, Int.ofNat 313342006, Int.ofNat 22106251, Int.negSucc 395015370,
   Int.ofNat 405637888, Int.ofNat 486686754, Int.ofNat 312323853, Int.negSucc 405076738,
   Int.negSucc 231801564, Int.negSucc 324837628, Int.ofNat 122356817, Int.ofNat 334741691,
   Int.ofNat 786228048, Int.negSucc 195810838, Int.negSucc 45476404, Int.ofNat 444464985,
   Int.ofNat 350695701, Int.ofNat 144104292, Int.negSucc 355476404, Int.ofNat 202276708,
   Int.negSucc 288413370, Int.ofNat 438897724, Int.ofNat 1187438780, Int.ofNat 739705187,
   Int.ofNat 940550941, Int.ofNat 1484770, Int.negSucc 219110297, Int.ofNat 1068959575,
   Int.ofNat 2434787710, Int.ofNat 1859161326, Int.negSucc 325784526, Int.negSucc 631035002]
/-- Slice 3 (64 entries) of hm256k512krS2Vec. -/
def hm256k512krS2Vec3 : List ℤ :=
  [Int.ofNat 471938367, Int.ofNat 164212047, Int.negSucc 319801626, Int.negSucc 591524656,
   Int.ofNat 180067928, Int.negSucc 755844212, Int.ofNat 443032185, Int.negSucc 286458050,
   Int.negSucc 337847919, Int.negSucc 43121193, Int.negSucc 825688936, Int.negSucc 1038174040,
   Int.ofNat 1156031937, Int.ofNat 637725316, Int.ofNat 813263075, Int.ofNat 310114928,
   Int.negSucc 1542672092, Int.negSucc 2621098445, Int.negSucc 1248599314,
   Int.negSucc 1898158326, Int.ofNat 1454781648, Int.ofNat 1176447615, Int.ofNat 1934960257,
   Int.negSucc 470276349, Int.negSucc 815137902, Int.negSucc 1277843696,
   Int.negSucc 1116505705, Int.negSucc 1250918956, Int.negSucc 125086074, Int.ofNat 1474108900,
   Int.ofNat 205085360, Int.negSucc 1542028281, Int.ofNat 265412919, Int.ofNat 3000836513,
   Int.ofNat 2945431730, Int.ofNat 2764692826, Int.ofNat 3185199400, Int.ofNat 2389494323,
   Int.ofNat 125686468, Int.negSucc 2869690128, Int.ofNat 964334464, Int.negSucc 1510687309,
   Int.negSucc 1275969893, Int.ofNat 3049452373, Int.ofNat 2994701815, Int.ofNat 3750061481,
   Int.ofNat 1208936795, Int.negSucc 478647470, Int.ofNat 2960004158, Int.ofNat 3481361355,
   Int.negSucc 3076330260, Int.negSucc 16641388230, Int.negSucc 16259993942,
   Int.negSucc 11995268900, Int.negSucc 13300343019, Int.negSucc 3989681598,
   Int.negSucc 1391666085, Int.ofNat 405798616, Int.negSucc 3275965763, Int.ofNat 10619785120,
   Int.negSucc 1573371817, Int.ofNat 3593777845, Int.negSucc 3162184018,
   Int.negSucc 4816784631]
/-- Slice 4 (64 entries) of hm256k512krS2Vec. -/
def hm256k512krS2Vec4 : List ℤ :=
  [Int.negSucc 7575219449, Int.negSucc 4224881100, Int.ofNat 749431643, Int.ofNat 10011101237,
   Int.negSucc 7192433732, Int.negSucc 10044632862, Int.ofNat 4832671337,
   Int.negSucc 118913827, Int.negSucc 3091346974, Int.negSucc 2043214637,
   Int.negSucc 13165363171, Int.ofNat 14289855136, Int.negSucc 11587962782,
   Int.ofNat 1920250637, Int.ofNat 1167557738, Int.ofNat 13286956213, Int.ofNat 16652339197,
   Int.ofNat 19508816679, Int.ofNat 9976424322, Int.negSucc 1631640989, Int.negSucc 8483737762,
   Int.ofNat 10833901417, Int.ofNat 1372162852, Int.ofNat 6895544797, Int.ofNat 5489411246,
   Int.ofNat 6572479483, Int.ofNat 9560094597, Int.negSucc 2843041484, Int.negSucc 2429721023,
   Int.negSucc 9960659884, Int.negSucc 1672332496, Int.negSucc 8553310194,
   Int.negSucc 5725676598, Int.negSucc 9351455583, Int.negSucc 8189845735,
   Int.negSucc 3286830618, Int.negSucc 5112628676, Int.ofNat 10031818575, Int.ofNat 5547647748,
   Int.negSucc 2993979861, Int.negSucc 6932910594, Int.negSucc 9739722972,
   Int.negSucc 17562162223, Int.negSucc 24216192521, Int.negSucc 1567777542,
   Int.ofNat 16261554935, Int.ofNat 18051592673, Int.negSucc 9231754270,
   Int.negSucc 33577182384, Int.ofNat 6250355537, Int.ofNat 25528065773,
   Int.negSucc 5450080959, Int.negSucc 24912389187, Int.ofNat 9923784902, Int.ofNat 1611532757,
   Int.ofNat 7474478574, Int.ofNat 28508797995, Int.ofNat 9056004152, Int.ofNat 11765632523,
   Int.ofNat 18739903926, Int.ofNat 11875544687, Int.negSucc 32279491691,
   Int.negSucc 20986754535, Int.negSucc 33764091914]
/-- Slice 5 (64 entries) of hm256k512krS2Vec. -/
def hm256k512krS2Vec5 : List ℤ :=
  [Int.negSucc 10352634625, Int.negSucc 7313500883, Int.ofNat 28269313146,
   Int.ofNat 15731781805, Int.ofNat 15552551503, Int.negSucc 8932521498,
   Int.negSucc 16902763431, Int.ofNat 2532088553, Int.ofNat 15906058287, Int.ofNat 6299258261,
   Int.negSucc 31589735088, Int.negSucc 57814602454, Int.negSucc 16345009335,
   Int.negSucc 24210198576, Int.ofNat 27621283019, Int.ofNat 60084900912, Int.ofNat 2546946751,
   Int.ofNat 6416770089, Int.negSucc 82782007481, Int.negSucc 1742243646,
   Int.ofNat 14076968527, Int.negSucc 30055629519, Int.ofNat 49824004093,
   Int.ofNat 88482843351, Int.ofNat 94414564509, Int.ofNat 73045880336, Int.ofNat 52685251613,
   Int.ofNat 66019515135, Int.ofNat 60082329942, Int.negSucc 51802225852,
   Int.negSucc 40555773513, Int.ofNat 47276085471, Int.negSucc 181720216582,
   Int.negSucc 281037689566, Int.negSucc 134381502471, Int.ofNat 153467206573,
   Int.negSucc 7092794485, Int.ofNat 5399797681, Int.ofNat 67892533389,
   Int.negSucc 160754828690, Int.negSucc 31205581732, Int.negSucc 18848357512,
   Int.negSucc 165223754794, Int.negSucc 304160536311, Int.negSucc 38448386734,
   Int.ofNat 41987057448, Int.ofNat 70401903885, Int.ofNat 133763309454, Int.ofNat 79434017298,
   Int.negSucc 124949308775, Int.negSucc 78880695377, Int.negSucc 225720954603,
   Int.negSucc 159902194450, Int.negSucc 130218513153, Int.ofNat 81711493631,
   Int.ofNat 9334355197, Int.negSucc 270414451775, Int.negSucc 214961100918,
   Int.negSucc 12564383075, Int.negSucc 40952324117, Int.negSucc 66087070832,
   Int.negSucc 399390635637, Int.negSucc 423114162721, Int.negSucc 471561819395]
/-- Slice 6 (64 entries) of hm256k512krS2Vec. -/
def hm256k512krS2Vec6 : List ℤ :=
  [Int.negSucc 498273758626, Int.negSucc 69688400685, Int.ofNat 366398715492,
   Int.ofNat 283556148547, Int.negSucc 53151833780, Int.negSucc 146858270901,
   Int.negSucc 238689088740, Int.ofNat 121855878293, Int.ofNat 43983376214,
   Int.negSucc 235467186402, Int.ofNat 343847828108, Int.negSucc 74504754044,
   Int.ofNat 432639110592, Int.ofNat 117010806558, Int.ofNat 204143141299,
   Int.ofNat 267888714605, Int.negSucc 280342293555, Int.negSucc 207878320451,
   Int.negSucc 711978006749, Int.negSucc 970543482987, Int.negSucc 706776237931,
   Int.negSucc 409903420968, Int.negSucc 297329059750, Int.negSucc 33383378196,
   Int.ofNat 12624260702, Int.negSucc 45615594147, Int.ofNat 235459303100,
   Int.ofNat 472711029781, Int.ofNat 327072755120, Int.ofNat 515213758833,
   Int.negSucc 227627472625, Int.ofNat 115788061509, Int.ofNat 716679661025,
   Int.ofNat 238615815613, Int.negSucc 41787323909, Int.negSucc 893711391678,
   Int.ofNat 367010466223, Int.ofNat 130696153713, Int.ofNat 620307288093,
   Int.negSucc 71517096932, Int.negSucc 398888317754, Int.ofNat 132962914173,
   Int.ofNat 941133571542, Int.negSucc 165735934188, Int.ofNat 143068172156,
   Int.ofNat 731321674987, Int.negSucc 432824965834, Int.ofNat 373911550111,
   Int.ofNat 744352711567, Int.ofNat 149543270815, Int.ofNat 972397459096,
   Int.ofNat 148573664129, Int.negSucc 1234680218652, Int.ofNat 211215293290,
   Int.ofNat 221999721273, Int.negSucc 884742391946, Int.negSucc 676720249949,
   Int.negSucc 853477215811, Int.negSucc 299292006510, Int.negSucc 264466460039,
   Int.negSucc 749936841093, Int.negSucc 69853907326, Int.negSucc 581199354782,
   Int.negSucc 185516158246]
/-- Slice 7 (64 entries) of hm256k512krS2Vec. -/
def hm256k512krS2Vec7 : List ℤ :=
  [Int.ofNat 126850353038, Int.negSucc 288541112980, Int.negSucc 1142117405656,
   Int.negSucc 232340089958, Int.negSucc 555009316058, Int.negSucc 1463587732767,
   Int.negSucc 868697643600, Int.negSucc 90435175836, Int.ofNat 1591485450168,
   Int.ofNat 561055088730, Int.negSucc 949762865035, Int.negSucc 1050430508565,
   Int.negSucc 7204711796, Int.ofNat 2588835482653, Int.ofNat 879302237575,
   Int.negSucc 736310854197, Int.ofNat 2127881010198, Int.negSucc 2578574308399,
   Int.negSucc 4712727682047, Int.negSucc 2816672280737, Int.negSucc 2727124904423,
   Int.negSucc 396791615319, Int.negSucc 13625561291, Int.negSucc 3778802721769,
   Int.ofNat 2016143328962, Int.ofNat 4178076516336, Int.negSucc 4276402701359,
   Int.negSucc 812813431245, Int.negSucc 852556142734, Int.ofNat 3425004741214,
   Int.ofNat 2326785876399, Int.negSucc 8805703695407, Int.negSucc 9991493712804,
   Int.negSucc 5753487686845, Int.ofNat 2646854658035, Int.negSucc 3211761605896,
   Int.ofNat 12544573456611, Int.negSucc 1773381071221, Int.negSucc 19533805511815,
   Int.ofNat 9083077576829, Int.ofNat 17162796025608, Int.ofNat 7609335198891,
   Int.negSucc 293963853820, Int.negSucc 5667920784577, Int.ofNat 652586215718,
   Int.negSucc 1571625286792, Int.ofNat 15275569756210, Int.negSucc 9507801784318,
   Int.negSucc 15309488489005, Int.negSucc 1970498297303, Int.negSucc 3009030180233,
   Int.ofNat 368788863478, Int.ofNat 32741666398551, Int.ofNat 12585369720627,
   Int.ofNat 4347415892565, Int.ofNat 6773777167175, Int.ofNat 2808427685891,
   Int.negSucc 25389821819852, Int.negSucc 39972511987773, Int.negSucc 16977494494400,
   Int.negSucc 40151797158458, Int.ofNat 160157491551531, Int.ofNat 557002438653146,
   Int.ofNat 698958528159471]
/-- Slice 8 (1 entries) of hm256k512krS2Vec. -/
def hm256k512krS2Vec8 : List ℤ :=
  [Int.ofNat 410052738964169]
/-- Checkpoint 513-entry fixed-point amplitude vector exiting hm256k512krS2Segs. -/
def hm256k512krS2Vec : List ℤ :=
  hm256k512krS2Vec0 ++
  (hm256k512krS2Vec1 ++
  (hm256k512krS2Vec2 ++
  (hm256k512krS2Vec3 ++
  (hm256k512krS2Vec4 ++
  (hm256k512krS2Vec5 ++
  (hm256k512krS2Vec6 ++
  (hm256k512krS2Vec7 ++
  (hm256k512krS2Vec8))))))))

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
  | ofNat x =>
    cases b with
    | ofNat y => exact congrArg Int.ofNat (s2NatEq_eq h)
    | negSucc _ => cases h
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
private def s2StateAt (st : ℕ × ℕ × ℕ × List ℤ) (l d p : ℕ) (v : List ℤ) : Bool :=
  match st with
  | (ls, ds, ps, vs) =>
    Bool.and (s2NatEq ls l)
      (Bool.and (s2NatEq ds d) (Bool.and (s2NatEq ps p) (s2IntListEq vs v)))
private theorem s2StateAt_eq {st : ℕ × ℕ × ℕ × List ℤ} {l d p : ℕ} {v : List ℤ}
    (h : s2StateAt st l d p v = true) : st = (l, d, p, v) := by
  rcases st with ⟨ls, ds, ps, vs⟩
  unfold s2StateAt at h; dsimp only at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨hl, ⟨hd, ⟨hp, hv⟩⟩⟩
  rw [s2NatEq_eq hl, s2NatEq_eq hd, s2NatEq_eq hp, s2IntListEq_eq hv]
private abbrev s2P : ℕ → ℤ := Int.ofNat
private abbrev s2N : ℕ → ℤ := Int.negSucc
private def s2RunAt (c : List Rkm128kSeg) (l0 d0 p0 : ℕ) (v0 : List ℤ)
    (l1 d1 p1 : ℕ) (v1 : List ℤ) : Bool :=
  s2StateAt (rkm128kRunSegs 256 4 512 c l0 d0 p0 v0) l1 d1 p1 v1
private theorem s2RunLast {c : List Rkm128kSeg} {l0 d0 p0 l1 d1 p1 : ℕ} {v0 v1 : List ℤ}
    (h : s2RunAt c l0 d0 p0 v0 l1 d1 p1 v1 = true) :
    rkm128kRunSegs 256 4 512 c l0 d0 p0 v0 = (l1, d1, p1, v1) :=
  s2StateAt_eq h
private theorem s2RunStep {c rest : List Rkm128kSeg}
    {l0 d0 p0 l1 d1 p1 l2 d2 p2 : ℕ} {v0 v1 v2 : List ℤ}
    (h1 : s2RunAt c l0 d0 p0 v0 l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 256 4 512 rest l1 d1 p1 v1 = (l2, d2, p2, v2)) :
    rkm128kRunSegs 256 4 512 (c ++ rest) l0 d0 p0 v0 = (l2, d2, p2, v2) := by
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
  | zero => cases xs <;> rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xr => exact congrArg (List.cons x) (ih xr)
private theorem s2RunStepTd {xs : List Rkm128kSeg} {n : ℕ}
    {l0 d0 p0 l1 d1 p1 l2 d2 p2 : ℕ} {v0 v1 v2 : List ℤ}
    (h1 : s2RunAt (s2Take n xs) l0 d0 p0 v0 l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 256 4 512 (s2Drop n xs) l1 d1 p1 v1 = (l2, d2, p2, v2)) :
    rkm128kRunSegs 256 4 512 xs l0 d0 p0 v0 = (l2, d2, p2, v2) := by
  rw [← s2Take_drop n xs]
  exact s2RunStep h1 h2
private def s2Rem0 : List Rkm128kSeg := hm256k512krS2Segs
private def s2Chk0 : List Rkm128kSeg := s2Take 3 s2Rem0
private def s2Rem1 : List Rkm128kSeg := s2Drop 3 s2Rem0
private def s2St0VecS0 : List ℤ :=
  [s2N 77974, s2N 585057, s2N 744623, s2N 842961, s2N 798787, s2P 165409, s2P 1184376,
   s2N 327546, s2N 1246460, s2N 1496007, s2N 955539, s2N 113082, s2P 3597135, s2N 275928,
   s2P 6299703, s2N 664642, s2N 1411388, s2N 5553348, s2N 1249790, s2P 94844, s2P 5145063,
   s2P 4944202, s2P 18374941, s2P 13870986, s2N 11283435, s2P 4902590, s2N 3160040, s2N 490428,
   s2N 9495756, s2N 185354, s2N 2800258, s2N 9712049, s2N 1005929, s2N 13304476, s2N 9207567,
   s2P 577957, s2P 24003035, s2P 18562912, s2P 8197427, s2P 3094407, s2P 13392296,
   s2N 41222448, s2P 68714735, s2P 31703067, s2N 51762453, s2P 2145974, s2P 41879717,
   s2P 58338961, s2N 43066298, s2N 5384558, s2N 16071039, s2P 69253772, s2P 2496110,
   s2P 58989511, s2P 67460134, s2N 244968, s2P 88669769, s2P 12714045, s2P 56085763,
   s2P 53856881, s2N 33546194, s2N 81856626, s2N 24388595, s2P 79043828]
private def s2St0VecS1 : List ℤ :=
  [s2N 113439774, s2P 34399288, s2N 120306936, s2N 121983897, s2N 122944718, s2P 218432466,
   s2P 89942676, s2N 77419488, s2N 20109983, s2N 81988507, s2N 221815825, s2P 81365161,
   s2N 127647678, s2N 6066493, s2N 4755287, s2N 46273712, s2N 278037262, s2N 329785317,
   s2N 17019520, s2P 6219303, s2P 34314945, s2P 124069710, s2N 238816237, s2N 514415065,
   s2N 714965430, s2N 426923385, s2N 292984527, s2N 221567062, s2P 204449052, s2N 155814497,
   s2P 70574183, s2P 149337399, s2P 421603096, s2P 544875773, s2N 9095803, s2N 608142149,
   s2N 586212381, s2N 415483787, s2P 344632752, s2N 119558424, s2N 755726851, s2N 607958971,
   s2P 145260692, s2N 169125234, s2P 294259798, s2N 1137293368, s2N 668608495, s2P 192770295,
   s2N 309124260, s2P 617045424, s2P 196652000, s2N 527254729, s2P 719845769, s2P 537242356,
   s2P 363052288, s2N 175566276, s2N 480075838, s2P 191343061, s2N 19818634, s2N 600079744,
   s2N 758756977, s2P 479588341, s2N 559816259, s2N 1672871614]
private def s2St0VecS2 : List ℤ :=
  [s2P 394444625, s2P 1109358742, s2P 1379704883, s2P 1401523626, s2P 3049234332,
   s2P 2750400998, s2P 200737214, s2N 849350831, s2N 741424485, s2P 1576776331, s2N 4222634539,
   s2N 3927438833, s2N 604521734, s2P 3615685929, s2P 5094901617, s2P 2153276997,
   s2N 730197535, s2P 1576765692, s2P 1192302863, s2P 2654579176, s2N 2763353823, s2N 90522494,
   s2P 3595162978, s2P 10905194742, s2P 6654140512, s2N 6899837771, s2N 8924028935,
   s2P 8877381477, s2P 9243561075, s2N 2531413360, s2N 4377240328, s2P 4596761517,
   s2P 93086111, s2N 550608292, s2N 1802638274, s2N 2361057714, s2N 2790652899, s2N 1189630331,
   s2P 6712164449, s2N 3453045539, s2N 199499230, s2N 2778437296, s2N 5049487038,
   s2P 9795567648, s2N 4459558435, s2P 6291712670, s2P 2493829624, s2N 3800185078,
   s2N 5123804314, s2N 2500038361, s2N 2613045478, s2P 4028850190, s2P 7200762725,
   s2P 14178585108, s2P 9339450699, s2N 5508106760, s2N 9507846404, s2P 4311120051,
   s2N 4287449436, s2P 9801204363, s2P 8948346942, s2P 6395012947, s2N 1988407913,
   s2N 1164636552]
private def s2St0VecS3 : List ℤ :=
  [s2N 168230555, s2P 3682783191, s2N 7947943497, s2P 7526992940, s2P 19358238827,
   s2P 1811464995, s2P 8550482752, s2P 6907165882, s2P 23854159521, s2P 11338112072,
   s2P 19977325327, s2N 12525230620, s2P 2947080928, s2P 24369938451, s2P 8008035960,
   s2N 1805532679, s2P 9687656219, s2N 3998216096, s2P 5635606593, s2N 24754872530,
   s2P 22820619346, s2N 838230469, s2N 24094562161, s2P 432359349, s2P 14239635756,
   s2N 8018823015, s2N 7570678758, s2N 13615271972, s2N 411057965, s2P 30178931610,
   s2P 28072842045, s2P 7200852150, s2N 13299007113, s2N 9244713905, s2N 23697023465,
   s2N 14840088366, s2N 7755747727, s2N 18316708476, s2P 6706127002, s2P 5581163228,
   s2N 8672013356, s2P 2719955591, s2N 466068126, s2N 8387846850, s2N 17463061442,
   s2N 11087066709, s2P 27139768936, s2N 29641071045, s2N 4914892377, s2P 26322738687,
   s2N 35289651477, s2N 12734052071, s2P 15031304076, s2P 31648355934, s2N 7836624456,
   s2N 20933741609, s2P 23176099925, s2P 8476932762, s2P 15362481750, s2P 5180584862,
   s2N 1647996434, s2P 32235812004, s2P 1319300599, s2P 10120020905]
private def s2St0VecS4 : List ℤ :=
  [s2P 21064348822, s2P 4443230596, s2P 15463675289, s2N 5124686819, s2P 24189234394,
   s2P 21530553390, s2P 24391406669, s2N 522814528, s2N 5943443435, s2N 18952352112,
   s2N 15097531975, s2P 5484065602, s2P 15103021191, s2P 158049552, s2P 1316837578,
   s2P 22153983975, s2N 11072432517, s2N 13064459333, s2P 25017513399, s2P 32209353930,
   s2N 15867811, s2P 7949369001, s2P 15055484949, s2P 19685133997, s2N 8592307066,
   s2N 13749524805, s2N 2226868920, s2P 9870499604, s2N 33684940444, s2N 6680511104,
   s2P 18269252370, s2N 2080876668, s2P 9580550755, s2P 21526583375, s2P 74126142192,
   s2P 7823882204, s2N 11973560870, s2N 22409209875, s2P 14897162324, s2N 46857560313,
   s2N 2630715049, s2P 45590929925, s2N 11394308065, s2P 17250157897, s2N 5183045058,
   s2N 39271872650, s2N 106079161293, s2P 1015187710, s2N 38642893510, s2N 77775532858,
   s2N 47694704856, s2N 36953688398, s2P 61157208251, s2N 27591880920, s2N 79323920732,
   s2P 80269316927, s2P 36150937521, s2N 136228606540, s2N 41313918366, s2N 259803150528,
   s2N 8222093781, s2P 176225366373, s2P 209381621250, s2P 62768385242]
private def s2St0VecS5 : List ℤ :=
  [s2P 39328511964, s2P 160201839147, s2N 207953352885, s2P 126982534876, s2N 8422615701,
   s2P 158787077150, s2N 17421988448, s2P 98507315006, s2N 211572176506, s2N 117386224889,
   s2N 144967618861, s2P 139374351926, s2P 191681103870, s2P 49272058480, s2P 26073544026,
   s2P 88321809064, s2P 42744290511, s2P 86414213569, s2P 65674343346, s2N 26282710214,
   s2N 40900715602, s2P 56073635663, s2N 224066394463, s2N 50160672870, s2P 146665261486,
   s2P 329502412045, s2N 137014534973, s2P 108113960839, s2N 85703872553, s2P 85303746788,
   s2P 15888809543, s2P 37387334886, s2P 90958523264, s2P 85947645850, s2N 361516653932,
   s2P 272672809061, s2P 181034423394, s2P 290558752449, s2P 120774265255, s2N 360670262614,
   s2P 497722295709, s2P 509142989710, s2P 439127571934, s2P 519264202742, s2P 409373696282,
   s2P 602041630364, s2P 10058403351, s2P 15500522071, s2N 167730823877, s2N 11871647709,
   s2P 398190182774, s2N 462181085049, s2N 358104003058, s2N 243174796659, s2P 45010832722,
   s2P 309046662671, s2N 22069973145, s2P 35741454411, s2P 42185223952, s2P 346003967424,
   s2N 378854683758, s2N 305722116804, s2P 633935156887, s2P 288575128992]
private def s2St0VecS6 : List ℤ :=
  [s2P 536124785602, s2N 716636187385, s2N 701078837668, s2N 520821484845, s2N 519620720327,
   s2N 310288198698, s2N 393889528803, s2N 1484765597002, s2N 669318703353, s2P 764031697717,
   s2P 1204309626800, s2P 1533195272661, s2P 913282743236, s2P 256004052371, s2N 1266632256527,
   s2P 349153146141, s2N 277735144804, s2N 843569256060, s2N 1807916197723, s2P 660650814289,
   s2N 728433623108, s2N 1662885909337, s2N 451461621212, s2N 247543107340, s2P 512765234240,
   s2N 1168859636363, s2N 20686928910, s2P 483591964341, s2P 282520850608, s2N 893336278706,
   s2N 3021546477044, s2N 77866870443, s2N 922835705433, s2P 428848498059, s2N 743474597843,
   s2P 31758695516, s2P 1803522988435, s2P 638750504724, s2P 3862868783466, s2P 3383524978749,
   s2P 2766577341907, s2P 2573881504795, s2N 522109273598, s2N 925661840891, s2P 1858782729820,
   s2P 28961629263, s2N 1372999716630, s2N 2523999730095, s2P 3366276887346, s2P 4152656843132,
   s2P 1317805492071, s2P 4420066508298, s2P 4334085205159, s2P 660525600839,
   s2P 2154167369816, s2P 7244785900854, s2P 30182058574684, s2P 65814577109622,
   s2P 111103597933572, s2P 161900795593188, s2P 213571335189152, s2P 261485944323608,
   s2P 301032401912094, s2P 328739210863142]
private def s2St0VecS7 : List ℤ :=
  [s2P 341383089146405, s2P 340177778307905, s2P 323573465721579, s2P 299256001056437,
   s2P 264548066689728, s2P 228984467064540, s2P 191913459118402, s2P 154849199545576,
   s2P 122994406735719, s2P 94861324967604, s2P 69589841578765, s2P 49515176081567,
   s2P 35001204517132, s2P 24017587030725, s2P 15225393593568, s2P 8685149867654,
   s2P 4525724932749, s2P 2256981408409, s2P 1126711618129, s2P 565883434433, s2P 277047624928,
   s2P 128186878878, s2P 55693110771, s2P 23220956169, s2P 9705779854, s2P 4260112762,
   s2P 2003846919, s2P 993943628, s2P 503320743, s2P 253263904, s2P 124631737, s2P 59511070,
   s2P 27475315, s2P 12246444, s2P 5266771, s2P 2185018, s2P 874341, s2P 337374, s2P 125468,
   s2P 44929, s2P 15468, s2P 5106, s2P 1606, s2P 473, s2P 124, s2P 26, s2P 2, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0]
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
private def s2Chk1 : List Rkm128kSeg := s2Take 3 s2Rem1
private def s2Rem2 : List Rkm128kSeg := s2Drop 3 s2Rem1
private def s2St1VecS0 : List ℤ :=
  [s2P 3124, s2N 18595, s2N 639043, s2N 230683, s2P 610798, s2P 1435917, s2P 559341,
   s2N 515928, s2P 315133, s2P 1352103, s2N 269612, s2N 4168078, s2N 2062209, s2N 3800716,
   s2N 3502853, s2N 543979, s2N 4180613, s2N 836832, s2P 1017183, s2P 3322000, s2P 3843615,
   s2P 7342419, s2P 1320950, s2P 3719645, s2N 995336, s2N 4658237, s2N 11000924, s2N 11353443,
   s2P 17461179, s2P 11999835, s2P 10464168, s2N 1877529, s2P 5055817, s2P 795761, s2N 1476548,
   s2P 16595300, s2N 4714255, s2P 5369163, s2P 24489839, s2P 19999308, s2N 10239402,
   s2N 42603109, s2N 8258945, s2P 28597400, s2P 31060959, s2N 49972561, s2P 40554367,
   s2N 25393707, s2N 86433231, s2N 23595776, s2P 23014799, s2P 47110946, s2P 22041356,
   s2N 34687659, s2N 25264628, s2N 36371776, s2N 90078452, s2P 19171499, s2P 108915278,
   s2P 71210546, s2N 17095306, s2P 5640020, s2P 52403767, s2N 59072482]
private def s2St1VecS1 : List ℤ :=
  [s2N 13390225, s2P 64575491, s2N 2957442, s2P 149676622, s2P 63675217, s2N 245839,
   s2P 620037, s2N 100008939, s2P 79414751, s2P 117450225, s2P 90106304, s2P 205755203,
   s2P 260634410, s2P 145499923, s2P 130308370, s2P 59448872, s2N 82795916, s2N 29338616,
   s2N 4692846, s2N 68949001, s2P 56785715, s2P 211158371, s2N 41768896, s2P 93378889,
   s2N 25450654, s2N 186873390, s2N 294869001, s2N 324369953, s2N 312587750, s2N 333666002,
   s2N 293719655, s2N 112957150, s2P 296123793, s2P 138112367, s2N 622520932, s2N 474061809,
   s2P 393002551, s2P 516289938, s2N 342586718, s2N 104746016, s2P 1155104829, s2P 99565146,
   s2P 328751868, s2P 518019608, s2P 495621221, s2P 1178964420, s2P 456121502, s2P 458462620,
   s2P 308872557, s2N 459181607, s2N 308288028, s2N 608442662, s2P 314762766, s2P 399346133,
   s2N 259493655, s2P 422556094, s2N 221578592, s2N 43612100, s2N 143913515, s2P 455466128,
   s2P 211084409, s2P 418862265, s2N 168581553, s2P 55215105]
private def s2St1VecS2 : List ℤ :=
  [s2N 1682320440, s2N 1084963073, s2N 1062599716, s2N 556180644, s2N 864666131, s2N 591973005,
   s2P 680424540, s2P 876543731, s2P 249081636, s2P 2273181725, s2P 1481003982, s2P 86485915,
   s2P 2076358529, s2P 3102813719, s2P 734436152, s2P 3044000160, s2P 2063802050,
   s2P 3278716154, s2P 500441238, s2P 871387940, s2P 1185219197, s2P 2413473259,
   s2P 3317798831, s2P 6091480355, s2P 7090542060, s2P 357684902, s2N 5117169670,
   s2N 1729487354, s2P 687646054, s2N 952933177, s2N 4441390526, s2N 3457890725,
   s2N 8525348591, s2N 10239189291, s2P 6383969292, s2P 11127564503, s2P 10707519398,
   s2N 1978520210, s2P 7241855176, s2P 2172672701, s2P 4534292467, s2P 7817277710,
   s2P 3736169533, s2P 284247727, s2P 8362304484, s2P 200203952, s2P 1394019564,
   s2P 1293153169, s2P 778853428, s2N 1367977095, s2N 3346048632, s2N 6853278244,
   s2N 561838028, s2N 3530081966, s2N 2267849303, s2N 3673555907, s2P 87682840, s2N 5047355033,
   s2N 12353642902, s2N 11621671146, s2N 10778798153, s2N 7333364381, s2P 4242941393,
   s2P 8321572275]
private def s2St1VecS3 : List ℤ :=
  [s2P 7852788926, s2N 11224880679, s2P 1008374932, s2P 7651757797, s2P 7385979903,
   s2N 107871477, s2N 1161166794, s2N 1529109265, s2N 5025880520, s2N 7625897993,
   s2N 20401794351, s2N 16232440318, s2P 1276130986, s2P 16778354950, s2P 7480172620,
   s2N 10196026348, s2N 36746721587, s2N 15710451488, s2N 4562455353, s2P 14756672409,
   s2P 14123619627, s2N 7490029129, s2N 17035859648, s2P 9824510819, s2N 9795020507,
   s2N 10812470190, s2P 7113623140, s2P 17810643682, s2N 14681445975, s2N 6806224020,
   s2N 15398518540, s2N 13810895832, s2N 1104282161, s2P 72163594, s2N 22935462902,
   s2P 19471937132, s2P 13879378757, s2P 5829021218, s2P 29093999130, s2N 7946435966,
   s2P 11195746051, s2P 6719252527, s2P 4737351961, s2P 28686180511, s2P 36349767264,
   s2P 23662646318, s2P 10562976303, s2N 7064942500, s2P 5525782321, s2N 3660988601,
   s2P 11518585971, s2N 30252774215, s2P 4232199907, s2P 53117903880, s2P 9535766386,
   s2N 728713308, s2P 4873780910, s2P 15124775980, s2P 25458013967, s2N 4780789894,
   s2P 24409470974, s2N 471256209, s2P 22444807117, s2P 2156378667]
private def s2St1VecS4 : List ℤ :=
  [s2N 457612582, s2N 8918631754, s2N 23746372000, s2N 10982706936, s2N 22382381191,
   s2N 3404799051, s2P 10364954644, s2P 9649892178, s2P 15565417244, s2N 1337031814,
   s2P 1225392415, s2N 21392544664, s2P 311782878, s2P 12598943722, s2P 4593399590,
   s2P 16678562442, s2P 15174291457, s2N 21793329692, s2N 9249893978, s2N 3264602436,
   s2N 17846742908, s2P 4603921229, s2N 852605203, s2P 20031690082, s2P 18527880736,
   s2N 7739791127, s2N 36568934585, s2N 14402708771, s2P 22370419361, s2N 11886596975,
   s2N 7188594128, s2P 20571665566, s2P 44809914430, s2N 9824595102, s2P 31274109887,
   s2N 15424413203, s2P 25836199234, s2P 5469809345, s2P 21569503250, s2P 30632243479,
   s2N 43294004336, s2P 28140238412, s2N 10664455128, s2P 30102010194, s2P 12011257449,
   s2P 73464948815, s2N 17234309028, s2N 32487300448, s2N 59589007268, s2P 42528227721,
   s2P 51069003686, s2P 46708456946, s2P 120843207409, s2P 144256491191, s2N 90814627585,
   s2N 109370803488, s2N 42288781926, s2N 64436971878, s2N 53790191440, s2N 16996559237,
   s2N 36256038463, s2P 78685397256, s2N 6289990412, s2P 173406809557]
private def s2St1VecS5 : List ℤ :=
  [s2P 202388710562, s2N 87206416647, s2N 274626530127, s2N 296539133151, s2N 50257928197,
   s2N 34737096344, s2N 87146070805, s2P 39754739515, s2P 4747111331, s2N 100974364384,
   s2N 146204792852, s2P 34388954194, s2N 16933977391, s2N 254390368506, s2N 21265593323,
   s2P 115236245586, s2P 109517478910, s2P 49608919847, s2N 7606582279, s2P 43217927356,
   s2P 36178939966, s2P 130975378350, s2N 166562039339, s2N 246234063521, s2N 157440472214,
   s2P 166463268560, s2P 395335760273, s2N 72749189041, s2P 36029005051, s2N 183031201225,
   s2P 66217294950, s2P 128929439007, s2N 289972226340, s2N 428736135736, s2N 102871541312,
   s2P 23565927962, s2N 125347793515, s2N 242932304876, s2P 85716396892, s2P 27937524522,
   s2P 5591304063, s2N 559177169249, s2N 415731513810, s2N 79686954683, s2N 486593263415,
   s2N 314266581763, s2P 119430344698, s2P 153810463323, s2P 297438318451, s2P 118084987597,
   s2P 161950360521, s2N 200690625991, s2P 601260892890, s2P 13920851388, s2P 968167609008,
   s2P 384727140513, s2N 78572717184, s2N 43662467657, s2N 249901568750, s2P 207214541884,
   s2P 382116754313, s2N 190222290794, s2N 169179739381, s2P 85367032426]
private def s2St1VecS6 : List ℤ :=
  [s2N 597122053942, s2N 288149036688, s2P 318950615079, s2P 343045908067, s2P 689436354155,
   s2P 588265891824, s2N 485243298791, s2N 220954305482, s2P 55430866117, s2P 343342266783,
   s2N 520053262759, s2N 1773440419641, s2N 287754106192, s2N 100013163434, s2N 536772953947,
   s2N 926283296238, s2N 352600837099, s2P 764783874126, s2P 3053956640928, s2P 1101510952701,
   s2P 557534894773, s2P 1680702186544, s2N 375865978026, s2P 282188492584, s2N 758956550856,
   s2P 596168250670, s2P 290501996896, s2P 102830103812, s2N 563502265089, s2N 835740296159,
   s2P 544934877856, s2N 1686013069410, s2N 1350840701849, s2N 10110949036, s2P 1543451009478,
   s2P 1682665452686, s2P 242762455803, s2N 1693244929330, s2P 632840884396, s2N 1359368966185,
   s2N 127822560792, s2N 755373063212, s2P 170513496994, s2N 840462397270, s2N 890412158775,
   s2P 573093229131, s2P 5799872471962, s2P 3202896533899, s2P 2009416666290,
   s2P 2446628251248, s2P 3303963380049, s2P 2326967639994, s2N 1227107524091,
   s2P 691303649553, s2P 1638348938774, s2P 770436281987, s2P 1517978333203, s2P 777432916839,
   s2P 4919849060305, s2P 5049106538533, s2P 3833772174209, s2P 2272540009709,
   s2P 3123697061945, s2P 2600496312037]
private def s2St1VecS7 : List ℤ :=
  [s2P 13204300889746, s2P 42520419829968, s2P 86104366044093, s2P 140078404844246,
   s2P 196622065692997, s2P 251856511197977, s2P 299772870323289, s2P 332892880494470,
   s2P 349310743238372, s2P 349898354872974, s2P 334830216777749, s2P 306703107287653,
   s2P 271028390988952, s2P 232210935638668, s2P 192342005998633, s2P 153439089304003,
   s2P 118196792788510, s2P 88473817418566, s2P 64416155702402, s2P 45238856533827,
   s2P 30253983697911, s2P 19078446926946, s2P 11311876346443, s2P 6328989435086,
   s2P 3366221183873, s2P 1715024222544, s2P 841289172255, s2P 398074640338, s2P 181681445675,
   s2P 80046548207, s2P 34196729254, s2P 14303689713, s2P 5943758657, s2P 2493280966,
   s2P 1067825281, s2P 467603949, s2P 207589076, s2N 92158507, s2P 40365617, s2P 17261754,
   s2P 7156173, s2P 2863307, s2P 1102680, s2P 407972, s2P 144804, s2P 49233, s2P 16001,
   s2P 4952, s2P 1444, s2P 389, s2P 90, s2P 16, s2P 1, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
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
private def s2Chk2 : List Rkm128kSeg := s2Take 3 s2Rem2
private def s2Rem3 : List Rkm128kSeg := s2Drop 3 s2Rem2
private def s2St2VecS0 : List ℤ :=
  [s2P 41032, s2P 74890, s2P 52560, s2N 369344, s2P 231687, s2P 1032261, s2P 1343823,
   s2P 820803, s2N 1240150, s2N 533046, s2P 172938, s2N 3564250, s2N 604079, s2P 1199351,
   s2P 132834, s2P 4176748, s2P 3502602, s2N 507658, s2P 712222, s2N 610886, s2N 2644820,
   s2P 3300431, s2N 2820843, s2P 522267, s2N 5013161, s2N 5049908, s2N 4255958, s2N 4919295,
   s2N 6473950, s2N 5265868, s2N 3624471, s2N 2234150, s2N 20895894, s2N 19912717, s2N 7200653,
   s2P 474817, s2P 3886605, s2N 3331514, s2N 19431181, s2P 14070585, s2P 13993622,
   s2N 11325061, s2P 485973, s2N 8038918, s2N 23078287, s2N 15906675, s2P 20691332,
   s2P 46371326, s2P 109431765, s2P 19546423, s2P 48275821, s2N 21723141, s2N 34299875,
   s2P 14988790, s2P 53184272, s2N 673633, s2N 26659180, s2P 33003943, s2P 16369718,
   s2P 20837134, s2N 26440537, s2N 26702282, s2N 29594526, s2N 71741803]
private def s2St2VecS1 : List ℤ :=
  [s2P 95557923, s2P 125705027, s2P 91955264, s2P 4732258, s2P 78585716, s2P 54761742,
   s2N 47432217, s2N 145934232, s2N 2282796, s2P 59697651, s2P 47288813, s2N 4400279,
   s2N 126965609, s2P 21426821, s2N 62724033, s2N 67102273, s2N 137688367, s2P 160371639,
   s2N 55641311, s2N 19864171, s2N 57919351, s2P 232368016, s2P 293625096, s2P 72524405,
   s2P 158221289, s2P 191123244, s2P 35350458, s2N 55900496, s2N 112671932, s2P 155696348,
   s2P 110256694, s2N 28898563, s2P 315780655, s2P 151989021, s2P 211667550, s2P 131200087,
   s2N 378072788, s2N 289110997, s2N 457889465, s2P 239742551, s2P 500837760, s2P 811853997,
   s2P 1130881637, s2P 285033588, s2P 120006872, s2N 487329448, s2N 426937324, s2N 454324480,
   s2N 22784436, s2P 584048562, s2P 102676923, s2P 616260441, s2P 612230659, s2P 8089770,
   s2P 199956383, s2N 281370615, s2P 92569445, s2N 1208612262, s2P 729929546, s2P 743063304,
   s2N 146687887, s2N 100823332, s2P 239197075, s2N 392321249]
private def s2St2VecS2 : List ℤ :=
  [s2P 421297526, s2P 562953517, s2N 435959497, s2N 260348634, s2P 1302399827, s2P 707739517,
   s2P 1936301981, s2P 99854237, s2N 452620810, s2P 1209849829, s2P 736622401, s2N 1679971879,
   s2N 1710465693, s2N 1985277763, s2P 673897512, s2P 745556634, s2N 251092768, s2P 824401077,
   s2P 562769671, s2N 1989168985, s2N 1442715981, s2N 662453744, s2N 1769680803,
   s2P 1802778074, s2N 808205460, s2N 389239148, s2N 4415863419, s2N 2525844425,
   s2N 5874838640, s2N 8138247461, s2N 5839935964, s2N 3729961488, s2N 310120271,
   s2P 3093273233, s2P 4800098434, s2N 474208342, s2N 5398100878, s2P 969080266,
   s2P 7206350063, s2N 1856064831, s2N 5597837415, s2P 3826187458, s2N 4973383187,
   s2N 3276714563, s2N 14404306861, s2N 11730231285, s2N 6801058012, s2P 1832322819,
   s2P 3292071568, s2P 5843410802, s2N 4221894015, s2N 2628047207, s2P 2227165653,
   s2P 6691012688, s2N 2917437856, s2N 2565569181, s2N 703144049, s2N 4544602703,
   s2N 4183502306, s2P 315865073, s2P 2169828636, s2P 2077658510, s2P 6179359419,
   s2P 799114082]
private def s2St2VecS3 : List ℤ :=
  [s2P 1611344586, s2P 3416874089, s2P 1093093971, s2P 6594464311, s2N 1625909414,
   s2N 14518658848, s2N 12463598553, s2N 2838095224, s2P 5573021679, s2P 11496716332,
   s2P 20889326725, s2P 14468573626, s2P 12401588850, s2N 5625429467, s2N 21473528154,
   s2N 19104955496, s2N 1918316730, s2P 5214770286, s2P 9730866883, s2P 9840374084,
   s2N 2665400496, s2N 2789529740, s2P 28781521084, s2P 7298862214, s2P 19643456320,
   s2P 19854287731, s2P 24678805987, s2P 4341766712, s2P 3341952933, s2N 5800095851,
   s2P 21395947150, s2P 3936895512, s2N 17900341487, s2N 7103412233, s2P 6533131404,
   s2N 4175413019, s2N 5321167699, s2P 8239216738, s2N 5311245635, s2P 2633766644,
   s2N 16715692039, s2N 32782747533, s2N 25472252432, s2N 11593518007, s2P 24986703594,
   s2P 9680897187, s2N 1641885353, s2P 14009597763, s2N 4093887619, s2N 10080575191,
   s2N 13049353487, s2N 10736484515, s2N 8827011817, s2N 8701847413, s2N 36192942451,
   s2N 29642569325, s2N 27397190186, s2N 15035128646, s2P 7053468458, s2P 36666041764,
   s2P 21244447562, s2P 7954375205, s2P 1492854540, s2P 4323088588]
private def s2St2VecS4 : List ℤ :=
  [s2P 20374862217, s2P 25561086266, s2P 32481149466, s2P 29403401660, s2N 12759519085,
   s2P 5434515472, s2P 7458328816, s2N 11992052428, s2N 8544241756, s2P 17849969146,
   s2N 6392650356, s2N 10468594349, s2P 24187025433, s2P 12243172087, s2P 6097004324,
   s2N 11221746581, s2N 3583886245, s2N 25859009196, s2N 6717175062, s2N 2101185059,
   s2P 2632015823, s2P 12672501835, s2P 4389485673, s2N 5433861443, s2P 24616675364,
   s2P 10746865866, s2P 2316027722, s2N 38395516402, s2N 23655982915, s2N 31194572265,
   s2N 28878051809, s2P 8325083055, s2P 17662456929, s2P 30265298368, s2N 24402453103,
   s2P 40975174595, s2P 44122064202, s2N 36881772606, s2N 9539523176, s2P 23318064372,
   s2N 25964633544, s2P 709063556, s2P 19472459455, s2N 19621735399, s2P 23749901857,
   s2P 61780309380, s2P 3525182671, s2P 55264642761, s2N 51309862668, s2N 43602906211,
   s2N 16620803514, s2N 19708636028, s2N 38303051394, s2N 51063123114, s2N 60167904782,
   s2P 2016720914, s2P 29822383503, s2P 58346312636, s2N 22332389000, s2N 162006069555,
   s2N 61079795538, s2P 36544824102, s2P 117270609912, s2N 131426178053]
private def s2St2VecS5 : List ℤ :=
  [s2N 113670068165, s2N 178427751535, s2N 32785986209, s2N 81945686124, s2P 4889244668,
   s2N 95384276296, s2N 14139116507, s2N 48080044930, s2N 315201714092, s2P 226506145439,
   s2P 289258936381, s2P 104556590335, s2P 118049174170, s2P 111668608721, s2P 39317560228,
   s2P 157270679166, s2N 7358868180, s2N 32788961885, s2N 103205714814, s2P 43848653233,
   s2N 156565980811, s2P 127974122701, s2P 67531569038, s2N 30658568568, s2P 131354152540,
   s2P 221390764177, s2P 117303000229, s2N 33201840479, s2N 287543781209, s2N 64037240606,
   s2P 459488250757, s2P 230671105782, s2P 91581795767, s2N 28002462318, s2P 203718265184,
   s2N 176534660911, s2N 374589070959, s2P 76829394320, s2N 374696507342, s2N 240301035655,
   s2P 213502204169, s2N 362810136180, s2N 325236378227, s2N 238878482931, s2N 43781218017,
   s2P 86117612661, s2P 375350251697, s2N 468433242259, s2P 303018794236, s2N 418529685636,
   s2N 32013489970, s2P 315507523586, s2N 22605333396, s2P 272785552214, s2N 128036549273,
   s2N 775147916607, s2P 146237367275, s2N 617272825333, s2N 46763126812, s2N 218524383603,
   s2N 553183275115, s2N 207722601706, s2N 1453620006, s2N 621177765551]
private def s2St2VecS6 : List ℤ :=
  [s2N 361732720220, s2N 27119623768, s2P 249295144391, s2N 332607995278, s2P 281855540431,
   s2P 163537365656, s2P 326447814131, s2P 170545689088, s2N 595889889094, s2N 42168060206,
   s2N 194116744009, s2P 703499402785, s2N 98622704206, s2N 99682251773, s2N 975481717097,
   s2N 1836061886017, s2N 284641053365, s2P 860695905961, s2P 1719301231339, s2P 214894334536,
   s2P 820602129929, s2N 445618197692, s2N 1086193263229, s2N 1258093154699, s2P 614020027794,
   s2N 389481390760, s2N 1367692363975, s2P 1173821701223, s2P 1705443668730, s2P 866693716514,
   s2N 1761948889108, s2P 191121024317, s2P 831761097123, s2P 507639488308, s2N 14018023668,
   s2N 674851882409, s2P 668466121664, s2P 1841733401612, s2P 1184131988147, s2N 762203366107,
   s2N 2113114249446, s2N 1089275408505, s2N 1410659952681, s2P 352177009733, s2P 721623736925,
   s2P 306058253368, s2P 636708008383, s2N 1109025595941, s2P 3912875832688, s2P 2188846774095,
   s2P 1027012701205, s2N 1987470044425, s2P 398212100110, s2N 300063563136, s2P 818395683821,
   s2P 1370184096073, s2P 3499308862657, s2P 4811023161927, s2P 1277553039651,
   s2P 2559846556640, s2P 3095508266324, s2N 665391571668, s2N 1516597446936, s2N 693026024646]
private def s2St2VecS7 : List ℤ :=
  [s2P 1055145883302, s2N 2464551903362, s2N 1278685441891, s2P 4162438758172,
   s2P 8200862777818, s2P 5398498954380, s2N 2573205414957, s2N 7637447437464,
   s2N 2655535276392, s2P 18290911712083, s2P 57907174178558, s2P 112656902313071,
   s2P 175311314235092, s2P 238613967632525, s2P 295055131055606, s2P 336847156807387,
   s2P 358924974189171, s2P 360963591512157, s2P 345792746224141, s2P 317007580659002,
   s2P 278457880935041, s2P 234643381662387, s2P 190223742921945, s2P 148842521867081,
   s2P 112513836700640, s2P 81951020744579, s2P 57214791008791, s2P 38076243828157,
   s2P 24063049619600, s2P 14393997267460, s2P 8239437455643, s2P 4269480048691,
   s2P 2498374504322, s2P 1027535022803, s2P 291756703161, s2P 95320934993, s2N 52100581184,
   s2P 30015903085, s2P 14859242020, s2P 6475898851, s2P 2575096573, s2P 950104556,
   s2P 331389277, s2P 113915482, s2P 40871244, s2P 15744705, s2P 6329088, s2P 2520926,
   s2P 959176, s2P 343169, s2P 115012, s2P 36119, s2P 10626, s2N 2916, s2P 735, s2P 161,
   s2P 28, s2P 3, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
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
private def s2Chk3 : List Rkm128kSeg := s2Take 3 s2Rem3
private def s2Rem4 : List Rkm128kSeg := s2Drop 3 s2Rem3
private def s2St3VecS0 : List ℤ :=
  [s2N 23365, s2N 373, s2P 142252, s2P 56804, s2P 165556, s2P 398985, s2P 8037, s2P 591657,
   s2P 322961, s2P 1793895, s2N 6653, s2P 1946788, s2P 2951183, s2P 308129, s2N 400061,
   s2N 1541933, s2N 2037729, s2P 1595030, s2P 612894, s2P 3360740, s2P 3468351, s2N 2064896,
   s2N 3699627, s2P 2942457, s2P 2272833, s2P 1344952, s2N 1069705, s2P 2619977, s2N 540920,
   s2P 977057, s2N 4918295, s2N 12047518, s2N 968599, s2P 833467, s2P 16209868, s2P 10456145,
   s2P 21862037, s2N 252839, s2N 9826299, s2P 131202, s2P 25681881, s2P 15199523, s2P 10494233,
   s2N 5373252, s2N 577687, s2N 24426608, s2P 18266160, s2N 5877886, s2N 17484390,
   s2N 21393715, s2N 31328063, s2P 8871297, s2N 18995243, s2N 43019184, s2N 48082831,
   s2P 46379591, s2N 58898545, s2P 81048593, s2P 86133227, s2P 25449969, s2P 25809517,
   s2P 8420735, s2N 5175503, s2P 50915874]
private def s2St3VecS1 : List ℤ :=
  [s2P 11102913, s2P 33809884, s2N 9962799, s2N 111826374, s2N 117350734, s2N 77926243,
   s2N 86345357, s2P 117212853, s2P 101312994, s2N 17340582, s2P 53827247, s2N 85620856,
   s2N 48811123, s2N 91550813, s2P 64842357, s2P 143503517, s2P 11745382, s2N 98770375,
   s2N 38244733, s2N 129591130, s2N 125105388, s2P 38109661, s2P 200719575, s2P 111306384,
   s2P 86660143, s2P 150427675, s2P 119085838, s2N 143780801, s2N 317758715, s2N 228463342,
   s2N 89123595, s2N 94789281, s2N 96793072, s2N 132457034, s2N 27555379, s2N 426272565,
   s2P 71972875, s2N 341813547, s2N 160228546, s2P 417907727, s2N 72945447, s2N 6404305,
   s2P 47101045, s2P 210525983, s2P 97472881, s2P 414379901, s2P 61264577, s2P 231578563,
   s2P 407411032, s2N 483725964, s2P 277105501, s2N 75908828, s2N 89680907, s2N 612581319,
   s2N 1170970203, s2N 1314346086, s2N 343850652, s2P 324726336, s2P 1104427137, s2P 3409799,
   s2P 715246308, s2N 76785684, s2P 425105940, s2N 729892950]
private def s2St3VecS2 : List ℤ :=
  [s2N 1349876324, s2P 50375924, s2N 840458759, s2P 782671607, s2N 1268342353, s2N 795984787,
   s2P 153135115, s2N 405002409, s2N 1373139096, s2P 990948223, s2N 11259259, s2N 182457178,
   s2N 1622398967, s2N 269871410, s2N 683404838, s2N 1597726741, s2P 587680989, s2N 670790952,
   s2N 1283763110, s2N 627319284, s2P 516700300, s2P 2660679954, s2P 2008593659,
   s2P 1963536879, s2N 685041641, s2N 553411593, s2P 537328540, s2P 948024487, s2P 462253335,
   s2P 1401280079, s2P 1613758526, s2P 1448637597, s2N 895900499, s2P 2354783824,
   s2P 2653061724, s2P 1010834113, s2N 1348746622, s2N 644459408, s2P 1194251819,
   s2P 605650760, s2N 2203561953, s2N 3270867012, s2N 3653536957, s2N 8332691897,
   s2N 6970847216, s2N 12692030756, s2N 7046439597, s2P 1245264569, s2P 2756553463,
   s2P 4672730805, s2P 2398097923, s2N 1109047069, s2P 2536659425, s2P 960138650,
   s2P 4176537087, s2N 2501272895, s2P 2625906146, s2P 9130468685, s2P 6211449850,
   s2N 9808710172, s2N 14859799025, s2N 8027544672, s2P 294650011, s2P 1582120173]
private def s2St3VecS3 : List ℤ :=
  [s2N 2266966473, s2N 1237209470, s2P 1849751069, s2N 1120556965, s2P 3126845120,
   s2P 4622491143, s2P 90979052, s2P 3686051471, s2N 579315898, s2N 1329788592, s2N 342870843,
   s2N 4422170260, s2N 9111389280, s2N 6575324298, s2N 10989298652, s2N 7165444972,
   s2N 6988073675, s2N 6200009050, s2N 2289944895, s2P 284700758, s2P 16138432428,
   s2P 8476687263, s2N 23231900703, s2N 29119799735, s2N 17783947549, s2P 10703223124,
   s2P 16133818392, s2N 471568163, s2N 1387548851, s2P 17802062222, s2N 17686813511,
   s2N 6588264994, s2N 1342309414, s2N 33428690257, s2N 26324802888, s2N 1914417276,
   s2P 6289916046, s2N 13650601945, s2N 13073810016, s2N 5625645337, s2P 4366713765,
   s2N 5596752780, s2N 9113078597, s2P 8299174646, s2N 16145189127, s2N 14975251623,
   s2P 381859067, s2N 1804186514, s2N 28073230301, s2N 8082869662, s2P 24668626890,
   s2P 24914280447, s2P 10217649190, s2N 10710871470, s2P 3218737590, s2N 18282957280,
   s2P 1103119245, s2P 15080386154, s2N 13325793440, s2N 26161229260, s2N 16488479836,
   s2P 4757765619, s2P 31660693185, s2P 16276873794]
private def s2St3VecS4 : List ℤ :=
  [s2N 11213650882, s2N 21692376424, s2N 19822907368, s2P 5099108519, s2N 26295684078,
   s2N 50583155442, s2N 20743563028, s2P 18023721953, s2N 476621179, s2N 17621445232,
   s2N 5320888359, s2P 22533511400, s2N 23298122159, s2P 11104203501, s2N 16362000938,
   s2P 20289163884, s2P 8169017161, s2P 7602502941, s2P 8132320998, s2P 11374622452,
   s2P 16972018946, s2N 11607154260, s2N 2976886848, s2N 10591252641, s2P 11180670483,
   s2P 24346072428, s2P 8885941403, s2P 2706589964, s2P 9554760552, s2P 713180369,
   s2P 8240681402, s2P 34641975133, s2P 32093004155, s2P 13576052852, s2P 18288006188,
   s2P 9686446988, s2P 16015831218, s2P 14273625002, s2P 15887930940, s2P 57493888386,
   s2P 79514463477, s2P 20783546332, s2N 33890243982, s2P 12086391189, s2N 55909099737,
   s2P 12604923101, s2P 37016327981, s2P 14399718860, s2N 24097128066, s2N 12869071994,
   s2N 42649883337, s2P 5494967105, s2P 30426144364, s2P 21971533359, s2N 19706420211,
   s2N 11227900030, s2N 43308863558, s2P 79134238217, s2P 38487210895, s2N 29754205384,
   s2N 68454755182, s2P 24215338245, s2P 58373446528, s2N 32115212718]
private def s2St3VecS5 : List ℤ :=
  [s2P 82014730245, s2N 136471944270, s2P 35728862360, s2P 310103303657, s2P 126953654465,
   s2N 158207977634, s2P 180879989353, s2N 175833166490, s2N 125810140410, s2N 58195253518,
   s2P 115186592050, s2P 12674100395, s2N 63240818996, s2N 182026758929, s2N 18291142843,
   s2N 69631095992, s2N 124545228407, s2N 205647249781, s2N 260281468132, s2N 115851893549,
   s2P 167683434344, s2N 4493882155, s2N 24476874294, s2N 29543045226, s2N 30787508782,
   s2N 23435827629, s2N 102704295977, s2N 9122534311, s2N 34379159126, s2N 184255128537,
   s2N 130413941387, s2P 49796548308, s2N 258831775766, s2N 474732656210, s2N 238492941731,
   s2N 52674605711, s2P 378237159158, s2N 264367886731, s2N 268969793562, s2N 257913813945,
   s2N 268691446797, s2N 325939989901, s2P 275403662531, s2P 172775631059, s2N 384567153606,
   s2N 203338357339, s2N 14916159384, s2P 406696377962, s2P 102656517722, s2P 57220043643,
   s2P 198131604905, s2N 320859798390, s2P 5452953969, s2N 980748844335, s2N 236954811982,
   s2P 21841803848, s2N 124407257349, s2P 341244442207, s2N 57590556783, s2N 89578965355,
   s2N 777842549750, s2P 67210275467, s2P 211902109917, s2P 322000952299]
private def s2St3VecS6 : List ℤ :=
  [s2N 471338927247, s2N 203582066450, s2P 46461784235, s2N 42145271268, s2P 368158127203,
   s2N 433338817642, s2N 232436567976, s2N 541213614610, s2P 663850709767, s2P 112645634506,
   s2P 281935253391, s2N 470278468781, s2N 373524273467, s2P 17348902178, s2P 110694722967,
   s2N 458040528346, s2N 341830385202, s2N 209430302864, s2N 826593079736, s2P 116803212340,
   s2P 739713255428, s2P 1753187853545, s2P 2394577729304, s2P 1535810528851, s2P 807389034630,
   s2N 763256991560, s2N 761294370130, s2N 662287535481, s2N 44924975903, s2N 1379799642305,
   s2P 1551972110291, s2N 774375696064, s2N 69871685141, s2N 496970420734, s2N 1632852775835,
   s2N 830661039354, s2N 205598843009, s2P 125579478779, s2P 1260373767063, s2P 467464906547,
   s2P 679240466533, s2N 1514463628163, s2N 1090835521889, s2N 392151593018, s2N 296896907027,
   s2N 222756865991, s2P 2428076401865, s2P 3510588148900, s2N 376025063801, s2N 584794066475,
   s2N 1363507453559, s2N 413798314826, s2P 2662240634866, s2N 1411044386735, s2N 662176832223,
   s2P 2146578235970, s2P 1749643355113, s2P 787894567504, s2P 2555387043993, s2N 866790821426,
   s2N 1221033787813, s2N 1082869833766, s2P 1051156276016, s2P 694506929329]
private def s2St3VecS7 : List ℤ :=
  [s2P 1570547457211, s2P 3368133627656, s2P 4162474922535, s2N 1743945585406,
   s2P 7389829480506, s2P 3252648439046, s2N 8354144398772, s2P 9917189343969,
   s2P 1251426127240, s2N 5990788956596, s2N 2014725251195, s2N 2962910858346,
   s2N 2744545751087, s2N 2284267206216, s2N 7074875903372, s2N 12777563209944,
   s2N 8747237415365, s2P 13571738153594, s2P 57500663656033, s2P 120133239788311,
   s2P 192543378175160, s2P 262783675609502, s2P 320436995238536, s2P 358555747270079,
   s2P 374457732984966, s2P 367681028843558, s2P 342113530713756, s2P 302252096886593,
   s2P 255221675160844, s2P 206564976243066, s2P 160062812256256, s2P 119132334937329,
   s2P 84749970409081, s2P 57335414630895, s2P 36831914920853, s2P 22514855930316,
   s2P 13132202377551, s2P 7245132865208, s2P 3693283249005, s2P 1698370616901,
   s2P 699201221795, s2P 262909270701, s2P 95245100205, s2P 35695372271, s2P 14343073400,
   s2P 5988545188, s2P 2454954547, s2P 952402442, s2P 346406435, s2P 118471091, s2P 39403738,
   s2P 12665681, s2N 3687258, s2P 951343, s2P 235843, s2P 62582, s2P 17445, s2P 4601, s2P 1077,
   s2P 215, s2P 32, s2N 1, s2P 0, s2P 0]
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
private def s2Chk4 : List Rkm128kSeg := s2Take 3 s2Rem4
private def s2Rem5 : List Rkm128kSeg := s2Drop 3 s2Rem4
private def s2St4VecS0 : List ℤ :=
  [s2P 9473, s2N 31703, s2P 166275, s2P 297901, s2P 608637, s2P 355345, s2P 332345, s2N 153750,
   s2N 489065, s2P 42497, s2P 940006, s2P 584285, s2P 1051461, s2P 1597081, s2P 2844722,
   s2N 622478, s2P 636458, s2P 1122010, s2P 1790006, s2N 435269, s2N 1924034, s2N 3914585,
   s2N 162061, s2P 1058757, s2P 5526697, s2P 2991599, s2N 2309968, s2N 5095894, s2P 339815,
   s2N 2909777, s2P 2543110, s2P 3375761, s2P 13426496, s2P 8243621, s2P 10716883, s2P 6461596,
   s2N 1408918, s2P 11173218, s2P 138149, s2N 3179400, s2P 372904, s2P 4319134, s2N 17727712,
   s2N 14007223, s2P 4262336, s2P 12012415, s2N 12859876, s2N 27109109, s2P 16103156,
   s2P 55928412, s2P 22682052, s2N 14979849, s2P 16776033, s2P 8391051, s2N 5331356,
   s2P 12127490, s2N 48408028, s2N 61707223, s2N 86041449, s2N 3565428, s2P 1940451,
   s2P 76294419, s2P 28317526, s2P 49369204]
private def s2St4VecS1 : List ℤ :=
  [s2N 6239615, s2N 28592901, s2N 43031558, s2N 37498766, s2N 30851666, s2N 78124143,
   s2N 28425594, s2P 76786934, s2N 14527850, s2P 17899748, s2N 49142273, s2P 70533449,
   s2P 148589710, s2P 90392154, s2P 104741384, s2P 60118674, s2N 72554258, s2P 144573348,
   s2N 5777091, s2N 111447372, s2P 26534545, s2P 82888472, s2P 20585416, s2P 181749244,
   s2P 197140728, s2P 13842155, s2N 97269942, s2N 139490555, s2N 37006289, s2P 18802887,
   s2P 217302955, s2P 12275034, s2P 97775109, s2N 79888109, s2N 239503706, s2P 118421631,
   s2P 120499402, s2P 250053026, s2N 691250480, s2N 12984348, s2P 104798232, s2P 231764937,
   s2N 329438236, s2P 121259674, s2N 97790531, s2P 166652484, s2N 401874121, s2P 38118072,
   s2P 59468348, s2P 201163416, s2P 71129922, s2N 387067795, s2P 156284893, s2N 414267431,
   s2P 212733911, s2P 40305447, s2N 224556851, s2N 106521447, s2N 609442320, s2N 372384139,
   s2N 7332528, s2P 832630577, s2N 118400993, s2N 85408433]
private def s2St4VecS2 : List ℤ :=
  [s2P 598601823, s2P 594351579, s2N 434630204, s2P 1010558723, s2P 1701211066, s2N 702218356,
   s2P 964507840, s2N 1147150100, s2N 1197316220, s2P 134450168, s2N 408609695, s2P 27839744,
   s2N 83668595, s2N 1441530350, s2N 790648294, s2P 916836509, s2P 1004330206, s2P 571591897,
   s2P 215320564, s2P 447943715, s2N 1144942085, s2N 1019746440, s2N 1310335907, s2N 134985258,
   s2P 347098060, s2N 316941173, s2N 829197753, s2N 557383397, s2N 1531478777, s2P 252844083,
   s2N 519774323, s2N 554225390, s2N 1924316785, s2N 2665624919, s2N 2308192445, s2N 318675911,
   s2N 1718490187, s2N 3533299572, s2N 2459685225, s2N 1067385315, s2N 1337363256,
   s2N 111229275, s2N 1906718230, s2N 28339408, s2P 98347016, s2N 729680244, s2P 3130650161,
   s2P 3452644720, s2N 1882248219, s2N 1454477190, s2P 1196883977, s2P 1694531842,
   s2P 752728103, s2P 952337722, s2P 5079644050, s2N 364166357, s2P 1777214057, s2N 6866956941,
   s2N 13876789904, s2N 5580928262, s2N 11228011564, s2N 10198234015, s2P 441070757,
   s2N 9394084455]
private def s2St4VecS3 : List ℤ :=
  [s2P 2273338807, s2N 205878117, s2P 3504581656, s2N 879466598, s2N 1247354193,
   s2P 2306402650, s2P 5228182906, s2N 4856399552, s2P 327277740, s2N 7185075467,
   s2N 5128888009, s2P 10552745122, s2N 5060045828, s2N 8989719624, s2N 2419239451,
   s2N 3135117479, s2N 186714995, s2P 115897051, s2N 1433555614, s2N 6560714550,
   s2N 1699816884, s2N 523311623, s2N 2094299636, s2N 4959755951, s2N 13286203175,
   s2N 9611970644, s2N 4108195385, s2N 8351482892, s2N 22335444801, s2N 8233264355,
   s2N 1876654956, s2N 4175358290, s2N 24850949293, s2P 12136136613, s2P 20692850835,
   s2P 2977095140, s2P 40544622817, s2P 19599040440, s2P 17794153288, s2P 3962363561,
   s2P 3451163591, s2P 20733512210, s2P 20783313527, s2N 710584367, s2N 8570966957,
   s2N 2263680522, s2N 10998930103, s2N 16853617602, s2N 20607063752, s2N 14963989604,
   s2N 8945510628, s2N 2366550703, s2N 3626010119, s2N 6945076924, s2P 7947697580,
   s2P 1095825962, s2P 5354839825, s2P 23365719923, s2P 4361139583, s2P 19197366148,
   s2N 31427870173, s2N 29675602872, s2P 3054006075, s2P 22381103330]
private def s2St4VecS4 : List ℤ :=
  [s2N 29353514980, s2P 7351333198, s2N 31248411962, s2N 23498796395, s2N 26323108014,
   s2N 27204210110, s2N 39353815046, s2N 17349821629, s2N 22586439848, s2N 34643816923,
   s2N 5267813973, s2P 20738313995, s2N 19545677274, s2P 7794587820, s2N 830023751,
   s2P 14404025437, s2N 10518702027, s2N 9226522346, s2P 9902266845, s2P 11358524956,
   s2P 7612699347, s2N 6367777697, s2N 12832718338, s2N 7046332111, s2N 17578780696,
   s2P 20976394791, s2P 8056696369, s2N 14203276741, s2N 20363176017, s2P 3677002027,
   s2P 15671763540, s2N 3627152531, s2N 16523166994, s2N 4686371538, s2N 3475981180,
   s2N 5774461782, s2P 12229056956, s2N 11516739897, s2P 9323673888, s2P 8997405677,
   s2P 34553262051, s2P 42569788532, s2P 3750083320, s2P 26503447526, s2N 44633852848,
   s2P 40746390601, s2P 50261375846, s2P 4035514103, s2P 53302622952, s2P 56469778515,
   s2P 53505132090, s2P 33323133136, s2P 55012405144, s2P 32590067364, s2P 23456743626,
   s2N 7975803452, s2P 4826738566, s2P 59392069826, s2P 78041962843, s2P 7766905837,
   s2P 34743027006, s2N 23433155589, s2N 126863801269, s2N 67104726299]
private def s2St4VecS5 : List ℤ :=
  [s2P 259624234, s2N 63207463196, s2P 37013569445, s2N 191527368231, s2N 78334579477,
   s2P 123243835548, s2P 204647971293, s2P 25561104630, s2P 75260100459, s2N 17551030070,
   s2N 136767764869, s2P 140061570911, s2P 234661195700, s2P 32173339347, s2N 27491794341,
   s2N 13119143059, s2N 2437896456, s2P 186831017854, s2N 125984748452, s2N 84633378690,
   s2N 216611186520, s2N 54472123273, s2P 77574564345, s2N 42431221673, s2N 38876889036,
   s2N 36288170750, s2N 5379968383, s2P 79454576668, s2N 136250735984, s2N 222651046600,
   s2N 61573524815, s2N 176483678802, s2P 412605671018, s2P 212464354908, s2N 103382200514,
   s2P 269307951814, s2P 104826690303, s2N 24064080855, s2N 175584510295, s2N 262599588217,
   s2N 189305791745, s2P 206370091712, s2P 426418736729, s2P 169686961735, s2N 339940323182,
   s2N 352380338807, s2N 378129293703, s2P 79005137872, s2P 92562291681, s2N 207748145183,
   s2N 619778078955, s2N 126108025865, s2N 210994114764, s2P 157689884148, s2P 531271755675,
   s2P 233654816927, s2P 965700891254, s2P 183845649282, s2N 187224508018, s2P 126701039056,
   s2P 132441986980, s2P 403379712428, s2P 75545958160, s2P 379432734857]
private def s2St4VecS6 : List ℤ :=
  [s2P 292753036956, s2N 239441454297, s2P 194617092204, s2N 672698824629, s2N 275671375186,
   s2P 669282630297, s2P 184951707857, s2N 597066817559, s2N 157960460466, s2P 14125700691,
   s2P 109675550006, s2P 370911630500, s2N 671030648164, s2N 77216316095, s2P 289242188867,
   s2P 182153650623, s2N 141696297763, s2P 302770910244, s2P 214878753321, s2P 485194657671,
   s2P 91757596227, s2N 48622435826, s2N 1047744941788, s2N 456906135297, s2N 198007019028,
   s2N 195953510887, s2N 1033099581724, s2P 224365086429, s2P 988570147825, s2N 51616714628,
   s2N 422457805752, s2P 1513381163914, s2P 2410326332537, s2P 2547340295965, s2P 760299003071,
   s2N 448955976580, s2N 1521517911283, s2N 564993327403, s2N 1045372846875, s2N 335138366685,
   s2P 579673632317, s2P 446104095703, s2P 227859564996, s2N 222687983422, s2N 470273335721,
   s2N 1962475029665, s2N 1676615377512, s2N 1373422672976, s2P 141047942257,
   s2P 1488582895623, s2P 2071306315061, s2P 819113445863, s2N 1901578221435,
   s2N 1507873784505, s2P 1556762773259, s2P 3371280592424, s2P 2096099806471,
   s2P 870329602140, s2P 1312378557271, s2P 1040770103415, s2P 921717432174, s2N 301784404575,
   s2N 2359682584728, s2N 1228657844875]
private def s2St4VecS7 : List ℤ :=
  [s2P 174270101738, s2P 1842049178335, s2N 864104768988, s2N 1609038023357, s2P 1724539744296,
   s2P 7696541650462, s2P 6479143040122, s2P 4326623796354, s2P 7034310609068,
   s2P 7896239609571, s2P 4182777910161, s2P 4088589229514, s2P 2058226680736,
   s2P 2147891605804, s2P 4459347890652, s2P 2797072147969, s2N 233459469296,
   s2N 3998467537136, s2N 1179302602096, s2N 2248940699894, s2N 585543245122,
   s2P 15568250638609, s2P 18458824268178, s2P 3671439603201, s2P 4273648024420,
   s2P 16303514856859, s2P 68319719394093, s2P 142196150958186, s2P 224070665670912,
   s2P 299272366004536, s2P 355586397552117, s2P 385625592362792, s2P 387470484403943,
   s2P 364262098474069, s2P 322774419583245, s2P 271076060218112, s2P 216375598434377,
   s2P 164101742773291, s2P 118177546362747, s2P 80364164243394, s2P 52772084961427,
   s2P 30660984118880, s2P 19913932973957, s2P 10060191186873, s2P 3556768274466,
   s2P 1122096838799, s2P 470469540749, s2P 241954369920, s2P 115369200818, s2P 47966340977,
   s2P 17900351895, s2P 6264718265, s2P 2142076435, s2P 646818710, s2P 157448974, s2P 31508595,
   s2P 5966462, s2P 1309953, s2P 343882, s2P 92688, s2P 23264, s2N 4330, s2P 557, s2P 53]
private def s2St4VecS8 : List ℤ :=
  [s2P 2]
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
private def s2Chk5 : List Rkm128kSeg := s2Take 3 s2Rem5
private def s2Rem6 : List Rkm128kSeg := s2Drop 3 s2Rem5
private def s2St5VecS0 : List ℤ :=
  [s2N 16588, s2N 69276, s2N 67838, s2N 122967, s2N 117498, s2N 5702, s2P 111010, s2P 656537,
   s2N 832, s2N 340321, s2N 373162, s2P 921300, s2P 355322, s2N 625688, s2P 663017,
   s2P 1119628, s2P 50000, s2N 625586, s2P 1416768, s2P 2779728, s2P 2545243, s2P 1105042,
   s2N 945147, s2N 450287, s2N 1107077, s2P 2169267, s2N 668843, s2N 5996092, s2N 1810683,
   s2N 833643, s2P 3814990, s2N 3673287, s2N 2022907, s2P 8953632, s2P 916826, s2N 5373211,
   s2P 9869828, s2P 4640370, s2N 12375102, s2N 4523020, s2N 3549279, s2N 11903836, s2P 6221184,
   s2P 10894099, s2N 6463353, s2P 1147504, s2N 7172543, s2N 3885249, s2N 15848200,
   s2N 12119113, s2N 4368828, s2N 22174576, s2N 2329963, s2N 4239333, s2P 12534185,
   s2N 10551105, s2N 40027307, s2N 37142627, s2N 45062504, s2N 57572910, s2N 7721620,
   s2N 14839933, s2N 13223854, s2P 12135471]
private def s2St5VecS1 : List ℤ :=
  [s2N 25030618, s2N 36492901, s2N 33882591, s2N 11729024, s2P 17436010, s2N 28485263,
   s2N 42640648, s2P 91064091, s2P 130025472, s2P 99820662, s2N 3646336, s2N 58630199,
   s2N 9783551, s2P 71831907, s2P 86041322, s2N 42331566, s2P 97925828, s2P 93082270,
   s2N 41820348, s2N 36616168, s2N 76395131, s2N 110262791, s2N 40854701, s2P 28172918,
   s2N 42230355, s2P 94701931, s2P 158139776, s2P 77929701, s2P 117113522, s2P 29500674,
   s2P 45054506, s2N 150797239, s2N 42472611, s2N 7064352, s2P 28430906, s2N 130947498,
   s2N 256426683, s2P 89440969, s2P 264207550, s2P 285450967, s2P 307258368, s2N 237326609,
   s2N 200885310, s2P 63495566, s2P 296222858, s2P 344433130, s2P 202604517, s2P 410358588,
   s2P 435974907, s2P 390958015, s2N 201638307, s2N 262219019, s2N 63177616, s2P 34341008,
   s2P 436900206, s2P 349978747, s2P 110932780, s2P 223911788, s2N 147589362, s2N 148786411,
   s2P 25140362, s2N 6105127, s2N 33095843, s2N 254893906]
private def s2St5VecS2 : List ℤ :=
  [s2N 128221638, s2N 64401192, s2N 111323074, s2P 397427545, s2P 391246807, s2N 401969626,
   s2P 818902609, s2N 335727057, s2N 34592618, s2N 1439397401, s2N 1264057058, s2N 815241724,
   s2P 1366979618, s2P 1463441607, s2P 710895265, s2P 1182299392, s2P 423836655, s2P 677585432,
   s2P 338068357, s2N 82652054, s2N 165799603, s2N 507214156, s2N 466844196, s2N 801205790,
   s2N 506583809, s2N 28063291, s2N 1271065090, s2N 1311782355, s2P 830153554, s2N 461268746,
   s2P 973603362, s2P 547139712, s2P 872779617, s2P 338976297, s2P 1170823836, s2P 879899213,
   s2P 1188570302, s2P 414258827, s2P 243950918, s2P 646397918, s2N 112337183, s2N 423244416,
   s2N 362939484, s2N 559312721, s2N 333203423, s2N 1486469154, s2N 696680097, s2N 1100766753,
   s2N 1882042531, s2N 4488886733, s2N 4064306271, s2N 1656505525, s2P 1712054573,
   s2N 1046234625, s2N 2723625345, s2P 822980096, s2P 4343159504, s2P 1485635837,
   s2P 1766446209, s2N 3344081910, s2P 3430088956, s2P 3964206961, s2N 2359200238,
   s2P 774828536]
private def s2St5VecS3 : List ℤ :=
  [s2P 4158586272, s2P 1572551977, s2N 4231312306, s2N 7727893978, s2P 5147285490,
   s2N 9420032431, s2N 7965888051, s2N 9293118503, s2N 6004777093, s2N 3079942784,
   s2P 5156822883, s2N 2211067888, s2N 3169000565, s2N 10227183295, s2N 13296062271,
   s2N 11170979263, s2P 4998250102, s2P 2888567188, s2P 357419192, s2P 4973669568,
   s2N 6839166821, s2N 430784096, s2N 5415431236, s2P 3110778137, s2N 4081960945,
   s2N 3138014604, s2N 610661506, s2N 1746603775, s2P 1033665919, s2P 412399932,
   s2P 4714379387, s2P 5484906806, s2P 7011593927, s2P 3440691402, s2P 2863561525,
   s2N 4178250131, s2N 7331621154, s2N 2921511231, s2N 3169468979, s2N 5229824301,
   s2P 8482523302, s2P 11603013157, s2P 19447408222, s2P 18449821542, s2P 11703706098,
   s2N 15763251246, s2N 10749933723, s2N 42395628783, s2N 27882827903, s2P 4585642000,
   s2P 15546527674, s2N 16829141661, s2N 35902544572, s2N 9763170790, s2N 2232040614,
   s2N 10956220230, s2P 29719184468, s2P 7180344118, s2N 1220049779, s2N 10906514418,
   s2N 7442843411, s2P 1938490491, s2P 7062034023, s2N 13908780035]
private def s2St5VecS4 : List ℤ :=
  [s2N 16819930823, s2N 3667463044, s2P 950802331, s2N 237799549, s2P 929319531,
   s2P 28513341554, s2P 40361339719, s2N 1917439276, s2N 55777708708, s2N 999235844,
   s2P 34957697024, s2N 12681659117, s2N 14792053910, s2N 4954142289, s2P 18469000730,
   s2P 18894262350, s2N 32194057261, s2N 3227519242, s2P 26667717030, s2P 11226219319,
   s2P 1199785594, s2N 10449508337, s2P 4614795845, s2P 3777788875, s2P 8407795508,
   s2P 34381768957, s2N 3100603906, s2N 24293554165, s2N 3485328035, s2N 18146070665,
   s2N 28856300272, s2P 8441513128, s2N 7965546174, s2N 134712839, s2P 28891110070,
   s2P 18770969472, s2N 8781346977, s2N 423957739, s2P 29168500635, s2P 17304024462,
   s2P 9925852734, s2P 26800079002, s2P 33851032475, s2P 49185423156, s2P 11909423078,
   s2P 14953498953, s2P 7325614206, s2N 30640746637, s2N 901323724, s2P 61342604949,
   s2P 5264768748, s2N 20676676436, s2P 30242381852, s2N 24000583408, s2P 36200620242,
   s2P 8224523686, s2P 27570687559, s2P 11585288763, s2P 7817776298, s2P 35300763092,
   s2P 7926048266, s2P 38767610820, s2P 86844698848, s2N 32470834147]
private def s2St5VecS5 : List ℤ :=
  [s2N 62230916199, s2N 36679977945, s2N 128568593155, s2P 28316915758, s2N 140306946486,
   s2N 64346088837, s2P 31771867562, s2P 46599097738, s2N 140398173985, s2N 43992800831,
   s2N 116091872566, s2P 40204025754, s2N 158995423730, s2N 167979063558, s2N 204134285935,
   s2N 131078539039, s2N 103666613619, s2P 33311767885, s2P 7719409879, s2N 50071970827,
   s2N 29129547487, s2P 183787142781, s2P 203108011125, s2P 67474769094, s2P 117891882912,
   s2P 88314749258, s2P 26467879159, s2P 167443702340, s2P 42171005263, s2N 47583664563,
   s2N 75329510575, s2P 240637475342, s2P 16740370312, s2P 38764719578, s2P 303374407033,
   s2P 140298408879, s2P 361684398130, s2P 253587125095, s2P 149317238076, s2N 160894012300,
   s2N 168794820136, s2P 44093355, s2P 33508951169, s2P 111067885999, s2N 453787849507,
   s2P 57261157431, s2N 74472148435, s2N 395840978238, s2P 275445274141, s2N 193889533268,
   s2P 678448252565, s2P 668943526580, s2P 306666248856, s2P 353666569973, s2P 699452943853,
   s2P 504580473753, s2P 383877289168, s2P 361372804867, s2P 247372561465, s2P 273912576917,
   s2P 638538698401, s2N 496932277967, s2P 350579690263, s2P 417053270085]
private def s2St5VecS6 : List ℤ :=
  [s2P 152069375808, s2N 247106608881, s2N 13731112780, s2P 69084828118, s2N 159252029845,
   s2P 234735918855, s2N 2966422499, s2P 435775241057, s2P 281605834398, s2P 28885757941,
   s2P 117642897276, s2N 64274838952, s2N 645677147812, s2N 36769868526, s2P 419357358758,
   s2N 631221273568, s2N 196954806968, s2N 249605264894, s2P 20529209307, s2N 264856774784,
   s2N 185887218372, s2N 472429130105, s2N 463548200272, s2N 708237865564, s2N 27025176234,
   s2P 383408486855, s2N 353134032538, s2N 1009432991431, s2N 983565846572, s2P 464224321991,
   s2P 713415064675, s2N 3805866739, s2P 598235728968, s2N 421054252663, s2N 153342271699,
   s2N 273701653165, s2P 804978782014, s2N 433615862697, s2N 775126945827, s2P 833994411334,
   s2N 269050496032, s2P 1518473077227, s2P 2786812271519, s2P 2322325030680,
   s2N 1189414527322, s2P 559317298936, s2P 331114994553, s2P 169804536219, s2N 321760761892,
   s2N 119343583981, s2N 665852320375, s2N 763297435670, s2N 1223937774498, s2P 376422013962,
   s2P 1843740564285, s2P 211023879688, s2N 1957864127750, s2N 1893007907488,
   s2N 2377059418080, s2N 1082809791867, s2N 2084849052434, s2N 2463682665495,
   s2N 2348499450990, s2N 1143700097083]
private def s2St5VecS7 : List ℤ :=
  [s2N 1918270828032, s2N 297536932931, s2N 93661354688, s2P 260579533490, s2P 2910302511294,
   s2P 1171594214537, s2P 2687716965770, s2N 3314846159744, s2P 3355895237221,
   s2P 377173740499, s2N 1811126468192, s2P 1117273045739, s2N 1783471459741,
   s2P 1119520315903, s2P 4269099601188, s2P 2567553019109, s2P 9954650370262,
   s2P 8358882953399, s2P 3128693504492, s2P 8694391434779, s2P 4321877041637,
   s2P 3266101667483, s2P 3636621242850, s2P 6203792723026, s2P 6825261107316,
   s2N 2022290684297, s2P 12732056622121, s2P 9632356792579, s2P 7226953607159,
   s2P 19776917648344, s2P 13829026212956, s2P 7383112358623, s2P 22256167447259,
   s2P 13018411026844, s2P 35257159878735, s2P 112486346226098, s2P 209852390150593,
   s2P 301610266716759, s2P 370457826484547, s2P 407407352222407, s2P 406200349402955,
   s2P 374111614566665, s2P 322476402314964, s2P 259255848575500, s2P 194201356176986,
   s2P 136976981615157, s2P 91531393424258, s2P 57267441881016, s2P 32810982121552,
   s2P 16998240612434, s2P 7782956902536, s2P 3506457037235, s2P 1213775859581,
   s2N 309647607014, s2P 81854225544, s2P 31785294131, s2P 13549284716, s2P 4945151041,
   s2P 1502940607, s2P 386749723, s2P 84907115, s2P 15914797, s2P 2268223, s2P 221816]
private def s2St5VecS8 : List ℤ :=
  [s2P 13992]
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
private def s2Chk6 : List Rkm128kSeg := s2Take 3 s2Rem6
private def s2Rem7 : List Rkm128kSeg := s2Drop 3 s2Rem6
private def s2St6VecS0 : List ℤ :=
  [s2N 8352, s2N 10319, s2N 56241, s2N 76985, s2N 192832, s2P 70661, s2N 6541, s2N 476204,
   s2N 838909, s2P 380227, s2P 507556, s2P 193718, s2P 688385, s2P 552390, s2P 788546,
   s2P 463096, s2P 284871, s2P 346293, s2P 1510112, s2P 299005, s2P 709937, s2P 1224447,
   s2P 325937, s2P 1813394, s2P 925511, s2P 284169, s2P 2480122, s2P 3881545, s2P 3030038,
   s2P 744207, s2P 4484199, s2P 211692, s2N 5959537, s2N 730981, s2P 10310630, s2N 5640774,
   s2P 7119470, s2P 1606433, s2N 5193842, s2P 8500059, s2P 8050813, s2P 8872818, s2P 10969887,
   s2P 14274602, s2N 2091237, s2N 868257, s2N 1921134, s2N 3594740, s2N 6067600, s2P 1856633,
   s2P 827461, s2N 12914658, s2N 3420290, s2N 7066180, s2N 7884995, s2N 1116905, s2P 2669199,
   s2N 7923219, s2N 10244040, s2N 24812596, s2P 23210977, s2N 23605709, s2P 6549253,
   s2N 12965118]
private def s2St6VecS1 : List ℤ :=
  [s2N 53463090, s2N 54808366, s2N 40919038, s2N 48471720, s2N 17425571, s2P 14747000,
   s2N 27585063, s2N 45745157, s2P 58750320, s2P 31116431, s2P 57738241, s2P 9708132,
   s2N 42565763, s2P 69570333, s2N 45505092, s2N 52238240, s2P 159253, s2P 1158012,
   s2N 80873244, s2N 83114206, s2P 50772640, s2N 6335003, s2P 83512250, s2P 224564672,
   s2P 90445555, s2P 70010620, s2P 71704537, s2N 35851550, s2N 73597423, s2N 8441226,
   s2P 8316941, s2P 100458568, s2P 12012196, s2P 104952434, s2N 17620307, s2P 67881657,
   s2P 94516192, s2P 120809062, s2N 51721938, s2N 1075570, s2P 25911911, s2P 150262434,
   s2P 72942963, s2N 105179901, s2N 281132312, s2N 272138280, s2P 67043514, s2N 128544594,
   s2N 197860470, s2P 207591664, s2N 296331720, s2N 251830138, s2N 301642066, s2P 399067021,
   s2N 16970669, s2N 128020750, s2P 121876516, s2P 356971303, s2P 193998236, s2P 147576391,
   s2P 3706189, s2N 278210521, s2N 480444591, s2N 44802460]
private def s2St6VecS2 : List ℤ :=
  [s2N 645661188, s2P 57941819, s2N 872243493, s2N 65021544, s2N 136241820, s2P 346036397,
   s2N 614335885, s2N 336507470, s2P 3021105, s2P 108721618, s2P 356249515, s2N 33437455,
   s2N 845374501, s2N 571050459, s2N 318545996, s2N 674760552, s2P 356010335, s2N 1495443542,
   s2N 1575942394, s2P 702267487, s2P 228860554, s2N 616374640, s2N 1084783148, s2N 1570073360,
   s2P 338995445, s2P 1164933600, s2P 73594447, s2N 290495828, s2P 867814894, s2N 626295197,
   s2P 420000996, s2P 16791714, s2P 427195084, s2N 568956217, s2P 633012735, s2N 85074568,
   s2N 1046025290, s2N 379618311, s2P 97367531, s2N 752046983, s2N 1135277885, s2P 314344701,
   s2P 1078948514, s2P 1518009598, s2P 507968018, s2P 857462739, s2P 241191059, s2P 500709817,
   s2P 91821671, s2P 100666984, s2P 2684473, s2N 1232181461, s2N 810250552, s2N 1013594535,
   s2P 428027948, s2N 1159090663, s2P 1986184842, s2P 376547591, s2P 1117971675,
   s2P 1147396969, s2N 204242527, s2P 272005511, s2P 1607139490, s2P 1037165997]
private def s2St6VecS3 : List ℤ :=
  [s2P 2241149490, s2P 4568487378, s2P 3071634189, s2P 9711279893, s2P 6848408796,
   s2P 2156555152, s2N 6426017532, s2P 690586812, s2P 9819682968, s2P 4258925523,
   s2P 5812927087, s2N 6788545896, s2N 757409722, s2P 2193438891, s2P 3229256019,
   s2P 7305571614, s2N 6035452927, s2P 5919778972, s2P 1462228655, s2N 8187513935,
   s2P 2357276066, s2P 7157178142, s2N 5726189314, s2P 2172303200, s2P 9804926493,
   s2N 448189655, s2N 1892925624, s2P 2515391908, s2P 6673273578, s2N 1820440344,
   s2N 4458425611, s2N 9504134280, s2N 8723749855, s2P 4929792732, s2N 7531579540,
   s2N 5713125747, s2P 4488566381, s2N 766430511, s2P 3117925318, s2P 8201753829,
   s2P 11103379929, s2N 6872481317, s2N 10167541237, s2N 2435870551, s2N 5307043183,
   s2N 4482313677, s2N 9011339044, s2N 2465547665, s2P 8297359167, s2P 9197300811,
   s2N 4575974069, s2N 11279873329, s2N 894016437, s2P 7273264465, s2P 16840202008,
   s2N 5562855400, s2N 992749952, s2N 3893245182, s2P 5412207960, s2P 12248395410,
   s2N 881091529, s2P 9813471700, s2P 36064990657, s2P 37239067861]
private def s2St6VecS4 : List ℤ :=
  [s2P 20668702404, s2N 28156974054, s2N 36336950681, s2P 13552934182, s2P 26271541279,
   s2N 14565552485, s2P 1270602698, s2P 28509813914, s2N 9264585213, s2N 3496329219,
   s2P 1464863785, s2N 9274219788, s2N 20526011506, s2N 5460523944, s2N 4295066441,
   s2P 3932586457, s2N 8067070185, s2P 2497624709, s2P 4720604301, s2N 12384030725,
   s2N 18958778862, s2N 38973874557, s2N 44747589905, s2N 57725213324, s2N 49382637102,
   s2N 8343438922, s2N 8041758633, s2N 5932039529, s2P 8490863636, s2P 12991421556,
   s2N 4197669554, s2P 4126547206, s2P 9458457944, s2N 7615562749, s2P 1887153990,
   s2P 6326199797, s2P 2847009897, s2N 5718570209, s2P 27817073544, s2N 2337737196,
   s2N 22790252109, s2P 19158595791, s2P 9121635795, s2N 86289108286, s2P 37030176744,
   s2P 33785853750, s2P 4416847283, s2P 19079157926, s2N 18970155944, s2P 8388955933,
   s2N 16715324339, s2N 11701440791, s2N 4165205374, s2N 42654794731, s2N 3887966695,
   s2P 35579593527, s2P 25006299043, s2N 12070553319, s2P 67447850280, s2P 24669269499,
   s2N 70822882465, s2P 59667848981, s2P 30795036771, s2P 28761727681]
private def s2St6VecS5 : List ℤ :=
  [s2P 1278811652, s2P 42264606361, s2P 61296491085, s2P 6214604715, s2P 55585827256,
   s2N 20454348850, s2P 101958226488, s2N 28138919007, s2N 88138134751, s2N 96131080722,
   s2N 80637594961, s2P 81583839898, s2N 82761881895, s2N 114446950015, s2N 44630968824,
   s2N 144218540171, s2P 4808347351, s2P 197642007150, s2P 26448578842, s2N 133975641854,
   s2P 109576042124, s2N 182762675967, s2N 12172786328, s2P 60567537394, s2N 109097924262,
   s2N 71369949461, s2P 154872377328, s2P 32125507128, s2N 190483871457, s2P 44820099643,
   s2N 157108378320, s2N 156569684749, s2N 165761832449, s2N 209631537421, s2P 136536221559,
   s2P 26402118400, s2N 65071658402, s2N 55247425080, s2P 120848987455, s2N 125315751487,
   s2N 36817883072, s2N 293876408821, s2P 22818994077, s2P 224230833872, s2P 299833298535,
   s2P 474146820289, s2N 158389391016, s2N 628861707097, s2N 315435176786, s2P 117808522277,
   s2N 134925744287, s2N 257059088475, s2N 446628246177, s2N 800539832486, s2N 261707185395,
   s2P 101222604054, s2N 337553042890, s2N 99156403579, s2P 104336954149, s2P 245960979898,
   s2P 352971731299, s2N 10164351998, s2N 190239634668, s2N 311387589734]
private def s2St6VecS6 : List ℤ :=
  [s2P 8260728197, s2P 356845881165, s2N 325830356982, s2P 1069714906688, s2N 601532362012,
   s2N 69380209703, s2P 398264963730, s2P 112802889744, s2P 220781406901, s2P 45244510978,
   s2N 190169199913, s2P 1159796103, s2N 176021377902, s2N 271954114292, s2N 115845274920,
   s2N 464640905370, s2P 1443948021, s2P 419439770463, s2N 251004640588, s2N 1801319668,
   s2N 840060830354, s2N 114185235121, s2N 369317858067, s2N 77931807005, s2P 120652502788,
   s2N 138244067101, s2N 140304855825, s2P 49103561030, s2P 395221469913, s2P 247504364935,
   s2P 126191606225, s2P 660893042538, s2N 297206065555, s2P 131037793503, s2N 898232433008,
   s2N 1212040162079, s2N 874779918992, s2P 431507418020, s2N 175393202978, s2P 299072058934,
   s2P 550083910316, s2P 581350589372, s2P 129696293452, s2N 1265831579180, s2N 293117872385,
   s2N 1269489448880, s2N 2148874367638, s2N 1954228007562, s2N 159489062066, s2N 157318603662,
   s2P 831595005957, s2P 737200264176, s2P 680616459950, s2P 2737334764414, s2N 1241020189960,
   s2P 295968929504, s2N 978225531821, s2N 145826594372, s2N 1072836863528, s2N 1767974716951,
   s2N 1907091714253, s2N 882529651526, s2N 1718683191444, s2P 368262812860]
private def s2St6VecS7 : List ℤ :=
  [s2N 255727403965, s2P 860801520605, s2P 1867394076183, s2N 1217629842611, s2N 1565235752763,
   s2N 3518471435979, s2N 3528740272343, s2N 2472602668652, s2N 850516091188,
   s2N 2885512094954, s2N 1506859663174, s2P 137609879029, s2P 3522700879449, s2P 994608766139,
   s2P 1756969648137, s2P 3165456408587, s2P 3043103779343, s2P 2921692277285,
   s2P 2362263589867, s2P 3975383463452, s2N 5221325179877, s2P 2159119804009,
   s2P 1441759369117, s2P 2244333447038, s2P 11845082536596, s2P 1473778088615,
   s2P 6633902114602, s2P 12580742963444, s2P 692362617801, s2P 10240456172681,
   s2P 9429251196742, s2N 3153241429390, s2P 2372309903997, s2P 10335738417298,
   s2P 8071546154352, s2P 2693223116617, s2P 20943455300205, s2P 22431434678877,
   s2P 16692250775419, s2N 2034205130099, s2N 14670515567991, s2P 13058126236422,
   s2P 92610607029642, s2P 204005573785159, s2P 314174440599538, s2P 396674227975327,
   s2P 434945193306495, s2P 424950172088555, s2P 375570334912656, s2P 302806732658053,
   s2P 225842481038058, s2P 154951175319514, s2P 97287012090846, s2P 56068882546638,
   s2P 29325153466299, s2P 13519007911001, s2P 5349386529127, s2P 1801546007554,
   s2P 522097555959, s2P 140832944399, s2P 27064114363, s2P 3967778022, s2P 812729427,
   s2P 203792269]
private def s2St6VecS8 : List ℤ :=
  [s2P 32865386]
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
private def s2Chk7 : List Rkm128kSeg := s2Take 3 s2Rem7
private def s2Rem8 : List Rkm128kSeg := s2Drop 3 s2Rem7
private def s2St7VecS0 : List ℤ :=
  [s2P 13143, s2N 7948, s2P 19820, s2P 92008, s2P 212159, s2P 34294, s2N 3558, s2P 276616,
   s2P 720531, s2P 720350, s2P 269028, s2P 236541, s2P 304216, s2N 518519, s2N 688945,
   s2N 332636, s2N 727271, s2N 696780, s2N 421839, s2P 1008107, s2P 845504, s2P 1076233,
   s2P 828259, s2N 141324, s2N 81905, s2P 348802, s2P 2313478, s2P 1247041, s2N 60238,
   s2P 2636598, s2P 4091707, s2P 4505060, s2P 6458829, s2P 4086896, s2N 198033, s2N 4163347,
   s2N 2800770, s2N 10002076, s2N 6563710, s2N 2795726, s2N 4625456, s2N 8215315, s2N 898531,
   s2N 1234601, s2P 4331978, s2N 2061044, s2P 4658899, s2P 7625300, s2P 1332341, s2P 20291395,
   s2P 9814480, s2P 2344785, s2N 193795, s2P 8220571, s2P 20193700, s2P 7267723, s2P 2272034,
   s2P 8154735, s2P 2895103, s2P 8072700, s2P 12206300, s2N 7525030, s2N 15564152,
   s2N 19248778]
private def s2St7VecS1 : List ℤ :=
  [s2N 31454441, s2N 39861168, s2N 20224581, s2N 27915126, s2P 22999132, s2P 24252554,
   s2N 11669637, s2N 23203175, s2N 2077686, s2P 21859292, s2P 10556055, s2P 68603461,
   s2P 111757887, s2P 59575459, s2P 14799490, s2P 24036261, s2N 41919056, s2N 42082161,
   s2N 17312853, s2N 49095357, s2N 28793157, s2N 81605185, s2N 77624499, s2N 11001548,
   s2P 72024573, s2P 132954945, s2N 37408985, s2N 19259362, s2N 92309233, s2P 20321405,
   s2N 98034603, s2P 92424799, s2P 53414140, s2N 66364785, s2N 39243560, s2N 116350623,
   s2N 170298062, s2P 51174953, s2P 19466096, s2P 33708370, s2P 33583492, s2P 76243364,
   s2N 31283207, s2N 287325080, s2N 37997094, s2P 81477349, s2P 77416069, s2P 212603279,
   s2P 190636860, s2P 165368340, s2P 130871755, s2N 131318208, s2N 56817515, s2N 302207149,
   s2N 139918074, s2N 340623945, s2N 352222042, s2N 53200440, s2P 3251867, s2P 327836744,
   s2P 561389374, s2P 135943558, s2P 109197724, s2P 489118871]
private def s2St7VecS2 : List ℤ :=
  [s2P 204832953, s2N 272891777, s2N 112150014, s2N 941279801, s2N 252363253, s2N 131040572,
   s2P 350134269, s2N 120464877, s2N 860270214, s2N 230889389, s2P 853197220, s2P 227387966,
   s2N 511949731, s2P 3951235, s2P 29018345, s2N 475236043, s2N 124415999, s2P 379697511,
   s2P 577136251, s2P 912462526, s2P 1261048884, s2P 1478603978, s2P 997656320, s2P 1364438760,
   s2P 592925020, s2N 445547077, s2N 176764101, s2P 321903042, s2P 1495094901, s2P 809308089,
   s2P 486319392, s2P 18496958, s2P 1202668683, s2P 469199645, s2P 993227579, s2N 423049671,
   s2N 106533468, s2N 524529115, s2N 672212254, s2N 71068727, s2N 397351824, s2N 368138153,
   s2P 123166764, s2P 563395364, s2P 610436673, s2N 649056754, s2N 847943234, s2N 1776115823,
   s2N 457604185, s2P 282652482, s2P 1297739789, s2P 67338440, s2N 1339032276, s2N 1111358482,
   s2P 1359286472, s2P 784631664, s2P 524645001, s2P 664119958, s2N 474882289, s2P 1285402890,
   s2N 689606020, s2N 704306675, s2N 218946417, s2N 1280124301]
private def s2St7VecS3 : List ℤ :=
  [s2N 838704607, s2N 2576277878, s2N 1222932848, s2N 1427166389, s2N 402002292, s2P 781162107,
   s2P 191670690, s2N 2198604688, s2N 925168818, s2N 48468906, s2P 1683437546, s2P 12984233,
   s2N 3707635104, s2N 4888715642, s2N 6006435181, s2N 9525260602, s2N 16595515250,
   s2N 12132402821, s2N 4842671508, s2P 1147546228, s2P 1974345302, s2N 1436931734,
   s2N 3851241937, s2N 3836289449, s2N 3265238735, s2N 3998591836, s2P 7323249193,
   s2P 7575197755, s2P 10151503058, s2P 8327113267, s2P 6357242507, s2P 7632375638,
   s2N 1148334955, s2N 532656490, s2N 4133444060, s2P 5659507721, s2P 3778094929,
   s2P 6677402118, s2P 840959903, s2N 1535083765, s2N 7176335475, s2N 3591210834,
   s2N 7248927345, s2P 2277227090, s2P 12021278781, s2P 2136479045, s2N 4045005253,
   s2N 522936771, s2N 9026455188, s2N 2614829799, s2N 421173592, s2N 2914698918,
   s2N 9624346559, s2N 5554142347, s2P 6640974493, s2P 10216113430, s2P 11950397211,
   s2P 15620148856, s2P 8481240369, s2P 12474353451, s2N 2449345037, s2N 5819590598,
   s2N 10391494294, s2N 1771852096]
private def s2St7VecS4 : List ℤ :=
  [s2N 5185820330, s2N 6782152264, s2P 3655803691, s2P 24386708148, s2P 17741119257,
   s2N 5212502407, s2N 24799553656, s2N 16052405201, s2N 5221401833, s2N 35001917947,
   s2N 38862506979, s2N 26046443015, s2N 14479014495, s2P 20757920480, s2P 36163853469,
   s2P 15956408845, s2N 13413489086, s2P 3624090303, s2N 7058746113, s2N 9842802415,
   s2P 2279307433, s2P 5053185955, s2N 7413451078, s2N 4113676029, s2N 13158412463,
   s2P 6893688448, s2P 17523121155, s2P 12924290361, s2N 5086645418, s2N 20463085038,
   s2N 18301094773, s2N 23851161175, s2N 25848492912, s2N 27527499126, s2N 51183018564,
   s2N 48912833523, s2N 9233723441, s2P 17094008037, s2P 26423479936, s2P 40210122112,
   s2N 217041124, s2N 19163395686, s2N 17680402240, s2P 9013249111, s2N 26276894325,
   s2N 58874644979, s2N 27351240928, s2P 48142877398, s2P 43006971145, s2P 18856075155,
   s2P 18240415090, s2P 45938220833, s2P 86519818752, s2P 6917908897, s2P 20998061553,
   s2N 64292843561, s2P 27969232590, s2P 6928860904, s2P 23300551803, s2N 29004418941,
   s2N 46241862137, s2N 15080863528, s2P 5056745021, s2N 2222500847]
private def s2St7VecS5 : List ℤ :=
  [s2P 86578431148, s2N 79006196320, s2N 1003345350, s2P 801872741, s2N 41414644498,
   s2P 18806074964, s2P 46734507852, s2P 13734146057, s2P 106051829350, s2P 10932398211,
   s2P 62378905538, s2P 15491318977, s2P 78427829656, s2P 58352617052, s2P 55380163272,
   s2N 54673927153, s2N 85284554378, s2N 60916729099, s2P 27724452014, s2P 15664983795,
   s2P 141022105155, s2P 27595282942, s2P 284733523462, s2P 222129548148, s2P 16764317418,
   s2P 84276805721, s2N 147781769889, s2P 13956461095, s2N 17570256540, s2N 179495584214,
   s2N 135856626995, s2P 153705596840, s2P 55838177819, s2N 192152389105, s2N 111130332809,
   s2P 239572932543, s2P 49085067462, s2N 167594747147, s2N 90066482461, s2P 45671592750,
   s2P 12811904995, s2P 139709708851, s2P 144311937005, s2N 175119503331, s2P 80232285128,
   s2N 3022036961, s2N 61693715568, s2N 319985020542, s2N 106079382708, s2N 372659485998,
   s2N 597471578636, s2N 150047286665, s2P 279268019960, s2P 262544498959, s2N 211658204270,
   s2N 213992120025, s2P 622855090188, s2P 242679477424, s2P 68397538619, s2N 41318788505,
   s2N 239687081285, s2N 550878942586, s2N 703563052978, s2N 120834466567]
private def s2St7VecS6 : List ℤ :=
  [s2P 64144274682, s2P 82161996044, s2N 911878834885, s2N 917758693330, s2N 202568628087,
   s2P 93342543285, s2P 433569843223, s2P 361633317372, s2N 107615857589, s2P 107539871808,
   s2P 40495837631, s2P 198704603782, s2P 168341715618, s2P 71117197222, s2P 258794031963,
   s2N 65472459856, s2P 186894849163, s2N 501872858779, s2P 242450881794, s2P 339666763449,
   s2N 242776162835, s2N 479589400616, s2P 100211920249, s2P 534330027433, s2N 335335121409,
   s2N 470455801083, s2P 240808679591, s2P 53932360123, s2P 318499618877, s2N 20708448712,
   s2N 763595346123, s2N 471167059967, s2N 9968488765, s2P 117168445981, s2P 213507992576,
   s2P 431602989175, s2N 1649757812, s2N 328598941693, s2P 30422216402, s2P 106627509118,
   s2N 170338303070, s2P 416371571331, s2P 967079203201, s2P 1812264652048, s2P 489311354247,
   s2N 849990075118, s2N 712567038066, s2N 149566409783, s2P 582846145230, s2P 546804065260,
   s2P 904789829763, s2N 851349616882, s2N 798217910887, s2N 1544054811525, s2N 2762936132125,
   s2N 2122786807838, s2N 1415118531164, s2P 1274235454307, s2P 534697614046, s2N 752740915761,
   s2N 571207694752, s2P 2037929626882, s2P 2016991416704, s2P 377253858528]
private def s2St7VecS7 : List ℤ :=
  [s2N 1233867015224, s2P 343366007183, s2P 1873481020169, s2P 1404483572908, s2P 239057483455,
   s2P 834258808654, s2P 1482229188100, s2N 1204582179239, s2P 153317418936, s2P 434015471268,
   s2N 1136583028568, s2P 444613711460, s2P 3813107773520, s2P 5540369470757, s2P 713960888801,
   s2N 2664220805832, s2N 1669681387983, s2N 3982020618125, s2N 2234058240522,
   s2P 799989921941, s2P 105920618469, s2P 9294758338910, s2N 1431453897389, s2P 7456164711336,
   s2P 7403086579636, s2P 1772208205271, s2N 2310462196008, s2P 534876537080,
   s2N 10177362351250, s2N 481108694120, s2P 5979288381416, s2N 1560877355673,
   s2N 5630646802103, s2P 16556024215104, s2P 3017371967789, s2P 3695650401928,
   s2P 5854608101727, s2P 14406996479347, s2N 3682819537889, s2N 6255138229167,
   s2P 17004260248904, s2P 9256736411899, s2P 21203201588896, s2P 29865129862066,
   s2P 5383044444326, s2P 15943341621783, s2P 16553701483602, s2P 111381474538900,
   s2P 242111701892431, s2P 366117598051809, s2P 443777120918118, s2P 458281306743266,
   s2P 416124010508348, s2P 337157794591838, s2P 244948374830010, s2P 161295381932582,
   s2P 92607796888686, s2P 51612764997936, s2P 21478537745338, s2P 6246519458338,
   s2N 1515722296312, s2P 394215430362, s2P 103708424802, s2P 21512632501]
private def s2St7VecS8 : List ℤ :=
  [s2P 2874693131]
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
private def s2Chk8 : List Rkm128kSeg := s2Take 2 s2Rem8
private def s2Rem9 : List Rkm128kSeg := s2Drop 2 s2Rem8
private def s2St8VecS0 : List ℤ :=
  [s2P 16281, s2N 2686, s2N 1451, s2N 38250, s2N 130730, s2N 76518, s2P 76158, s2P 235946,
   s2P 49414, s2P 11327, s2P 384223, s2P 839168, s2P 440463, s2P 182212, s2N 171687,
   s2N 429577, s2N 1092350, s2N 777069, s2N 27796, s2N 443296, s2N 500630, s2N 405894,
   s2P 410189, s2N 740021, s2N 376872, s2N 375290, s2N 424833, s2N 1536951, s2N 2073193,
   s2N 425200, s2P 156154, s2P 15646, s2N 1929927, s2N 2543080, s2N 80852, s2N 411255,
   s2N 5904419, s2P 1833755, s2N 9660706, s2P 2329771, s2P 7495516, s2N 5163601, s2N 8778290,
   s2P 7992596, s2P 1314446, s2P 1658243, s2N 4924302, s2P 8184117, s2P 4400252, s2P 3960360,
   s2N 2304555, s2N 10800621, s2N 7073656, s2N 2132397, s2P 5259724, s2P 1477453, s2N 9356206,
   s2N 27715576, s2N 4368594, s2P 2785299, s2N 15459462, s2N 1497151, s2N 5119539, s2N 1323291]
private def s2St8VecS1 : List ℤ :=
  [s2P 19432453, s2N 8055250, s2P 7608977, s2P 15959423, s2P 13635246, s2P 11237227,
   s2P 20986742, s2N 539275, s2N 3268693, s2N 17966229, s2P 9246222, s2P 34526279,
   s2P 55670586, s2P 71576728, s2P 69214381, s2P 84372749, s2P 50752808, s2P 28146590,
   s2P 33948312, s2P 52673549, s2P 44427387, s2P 104555946, s2P 8591086, s2N 52296684,
   s2N 42476750, s2P 41483870, s2P 93737893, s2N 44102566, s2N 17340454, s2P 52621370,
   s2N 32979076, s2P 125670947, s2P 114200007, s2P 58188148, s2P 29217065, s2P 624816,
   s2N 192030145, s2N 92025643, s2N 38984539, s2N 119287451, s2N 59206611, s2N 80319820,
   s2N 117867659, s2N 59867120, s2P 34430590, s2P 162954923, s2P 42796927, s2P 21476895,
   s2N 98379932, s2P 93122133, s2P 189423493, s2N 68630251, s2N 94801306, s2P 60701148,
   s2N 54585953, s2P 84309839, s2P 70058281, s2P 182012873, s2P 540994, s2N 203598438,
   s2N 167176495, s2N 28361958, s2P 140118424, s2N 220837338]
private def s2St8VecS2 : List ℤ :=
  [s2N 134518518, s2N 550377846, s2N 62418077, s2P 457529891, s2P 612678303, s2P 368349729,
   s2P 298357596, s2N 176223948, s2N 100810425, s2N 59124867, s2N 75818422, s2N 45451429,
   s2N 230667506, s2N 331658593, s2N 571939236, s2N 780523372, s2N 1078258635, s2N 1040016613,
   s2N 518548356, s2N 29970750, s2P 230272856, s2P 165865972, s2P 304597196, s2N 350824106,
   s2N 419813850, s2N 630574465, s2N 251691247, s2N 562836221, s2N 994702792, s2N 235323148,
   s2P 413166866, s2P 180450455, s2P 344704342, s2N 363453828, s2N 999682163, s2P 1738257881,
   s2P 1395598344, s2P 1750665486, s2P 497874334, s2P 503316343, s2P 939025285, s2N 52310752,
   s2P 133601137, s2N 1106650658, s2N 1249204378, s2N 1042687958, s2P 123857477, s2P 250211844,
   s2N 460940458, s2N 181372803, s2N 512774690, s2N 83756938, s2N 582747806, s2N 984452365,
   s2P 398914897, s2N 509585716, s2N 223623613, s2P 1306187594, s2N 15018184, s2N 1256912359,
   s2N 1586140244, s2P 1453634787, s2P 2145991124, s2P 671150492]
private def s2St8VecS3 : List ℤ :=
  [s2N 336903951, s2N 1192229706, s2N 1234418165, s2P 77278495, s2P 693511501, s2P 775620662,
   s2N 335589190, s2N 2635464596, s2P 2274186936, s2P 1371119746, s2P 1333577129,
   s2P 515164456, s2P 251518704, s2P 2752321506, s2N 94687696, s2N 627370049, s2N 4243909243,
   s2N 2536325622, s2N 1601743027, s2P 3007765773, s2P 2188029637, s2P 3402387829,
   s2P 2991174947, s2N 351598038, s2N 2214077072, s2P 2748456089, s2P 3977859771,
   s2P 1983171908, s2P 3315820524, s2N 5028740521, s2N 15365928563, s2N 15951790984,
   s2N 7270424442, s2N 6520200789, s2N 281332075, s2P 5926085073, s2P 7362962039,
   s2P 776808565, s2P 893778079, s2P 1078228965, s2N 2239351816, s2P 2661709582,
   s2P 1866581199, s2P 15157902991, s2P 11410256186, s2P 5123878165, s2N 920917835,
   s2N 7200496462, s2N 650342007, s2N 2748557243, s2N 965904903, s2N 6948262401,
   s2N 6819213610, s2P 2577983272, s2N 10534562192, s2N 1720488411, s2N 8717720265,
   s2N 10297989246, s2P 8593832914, s2N 4904469622, s2P 9227378182, s2N 97173356,
   s2P 10305998262, s2P 14121110343]
private def s2St8VecS4 : List ℤ :=
  [s2P 3263678706, s2P 3208114586, s2N 5522575576, s2N 9286656876, s2N 536416804,
   s2N 9096198892, s2P 15218047739, s2P 16031109612, s2P 11610264877, s2P 5173548852,
   s2P 15550929297, s2N 3774907113, s2N 16157991605, s2P 17397913219, s2N 19060892366,
   s2N 6680206, s2P 21546351502, s2P 1933834749, s2P 15309950724, s2P 11999806817,
   s2P 14859542930, s2N 4193531963, s2N 27745982608, s2N 34243901239, s2N 44385626799,
   s2N 27204678341, s2N 18833963937, s2N 19321936605, s2N 3600149225, s2P 4414736692,
   s2P 6348117803, s2P 4010794760, s2N 3069907269, s2P 18689142586, s2P 16027136875,
   s2N 2198048514, s2N 16416414698, s2P 997059815, s2P 16708408226, s2N 12413617399,
   s2N 13490814158, s2P 3343198478, s2N 7577171903, s2P 16305088787, s2N 9278736462,
   s2P 4942347292, s2N 9374205749, s2N 33438424071, s2N 64219614494, s2N 66851397981,
   s2N 48114213937, s2N 28477112641, s2N 9879475948, s2P 61769376454, s2P 70244073650,
   s2N 3746461999, s2N 48261050412, s2N 59805772475, s2N 42654895547, s2N 60209337570,
   s2N 61762611367, s2N 84131090218, s2N 64736143800, s2N 16727180004]
private def s2St8VecS5 : List ℤ :=
  [s2N 14688090480, s2N 67932284393, s2N 67790446826, s2N 31941967544, s2N 14859905291,
   s2N 40968161702, s2N 44246153099, s2N 54545849889, s2N 81470477376, s2N 15069129811,
   s2P 31278056068, s2P 40299164316, s2P 81028531167, s2P 46682180406, s2N 21760512703,
   s2N 1085875300, s2P 25668019946, s2N 35882030107, s2N 33991544961, s2N 111506103093,
   s2N 15044227722, s2N 37144944203, s2P 34236202630, s2P 103729074799, s2N 130276797714,
   s2N 120991240975, s2N 99123108643, s2N 78320969763, s2P 142522489971, s2P 109507006725,
   s2P 157047309455, s2P 309185989491, s2P 239849003933, s2P 139671760451, s2P 87993643622,
   s2P 152454985826, s2N 355678461010, s2P 52425055247, s2N 122977656401, s2N 48389060774,
   s2N 71590839205, s2N 19616685163, s2P 123476946264, s2P 23144871529, s2N 73218520307,
   s2N 4501424698, s2N 15358262978, s2P 93260656040, s2P 81833201646, s2N 280937935512,
   s2N 4343946589, s2N 96284709548, s2N 231161507832, s2P 205334399820, s2N 33739060044,
   s2N 136152660561, s2N 392557387687, s2N 194405322320, s2N 265358520883, s2N 541566469632,
   s2N 479724828595, s2P 162724450656, s2P 507482847450, s2N 177818676470]
private def s2St8VecS6 : List ℤ :=
  [s2N 310002426521, s2P 343305913544, s2P 377848506420, s2N 400592553336, s2P 519283849949,
   s2N 326870963718, s2P 313367042375, s2N 560100737453, s2N 617859929660, s2N 60442186828,
   s2N 47029011164, s2P 71409952579, s2N 500146892005, s2N 865162593240, s2N 596666925680,
   s2N 299048816828, s2P 280665262131, s2P 335322865892, s2N 319916635638, s2P 84778133084,
   s2N 535065812763, s2P 370851368486, s2P 596585084477, s2N 241447296459, s2N 110431144453,
   s2N 36210076937, s2N 153120331992, s2N 660966819423, s2N 38168656455, s2P 25960877442,
   s2N 222990794430, s2N 98641289378, s2P 378581938209, s2P 191228764732, s2N 248219179376,
   s2P 216203623121, s2P 224213257283, s2N 323607789403, s2N 100392108548, s2P 219088089078,
   s2P 672364406733, s2P 444352425449, s2P 15003326502, s2P 338105623898, s2N 176714341233,
   s2P 475553800098, s2P 92867829397, s2P 584073462627, s2P 419726038969, s2N 560597184027,
   s2P 973069227221, s2P 1035989860074, s2P 1407282821130, s2N 1125210205291,
   s2N 1249235307052, s2N 166667639304, s2P 411740952879, s2P 212899222575, s2N 414844878658,
   s2N 1541995707298, s2P 1695418513207, s2P 2624868603777, s2P 2627423028738,
   s2P 1285979644536]
private def s2St8VecS7 : List ℤ :=
  [s2N 1432549666632, s2N 685459258870, s2N 799321546597, s2N 483204478410, s2P 2419861381712,
   s2P 1617142142074, s2P 1612430948840, s2N 1415805908595, s2N 1112544329734,
   s2P 732719488620, s2P 1013728083372, s2P 1487465719018, s2N 153460873273, s2N 793244490759,
   s2N 4386225444711, s2N 4588315984874, s2N 6192224095794, s2N 4937993111223, s2N 24033367919,
   s2N 221466305807, s2N 2045657574850, s2P 5065915403245, s2P 1124369112453,
   s2P 4051578248266, s2P 3632586633182, s2N 1421113325320, s2N 821867994894,
   s2P 11487762859075, s2P 3645826471531, s2N 7515480944571, s2N 11532748154337,
   s2N 8445073902344, s2N 9706452714266, s2P 2907577613219, s2P 3906355556306,
   s2N 11831622181849, s2N 7915601490381, s2P 6771197427840, s2N 10262196374666,
   s2N 15088359894735, s2P 734615549276, s2P 16320027947735, s2N 445884527325,
   s2P 824688096249, s2N 1153564383698, s2P 960233060542, s2P 21271742385016,
   s2P 39043625243240, s2P 14868130985650, s2P 26554694893203, s2P 21789175789133,
   s2P 68700742389839, s2P 218720246399677, s2P 375529195987651, s2P 470305832404890,
   s2P 487000813258614, s2P 424172747990100, s2P 319058072021271, s2P 208151026091127,
   s2P 120477402872215, s2P 55961493937813, s2N 19123807607940, s2P 4758172524376,
   s2P 895913035967]
private def s2St8VecS8 : List ℤ :=
  [s2P 126168576229]
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
private def s2Chk9 : List Rkm128kSeg := s2Take 2 s2Rem9
private def s2Rem10 : List Rkm128kSeg := s2Drop 2 s2Rem9
private def s2St9VecS0 : List ℤ :=
  [s2P 18172, s2P 4628, s2N 5739, s2P 49521, s2P 147297, s2P 161522, s2P 152486, s2P 149426,
   s2P 240346, s2P 31971, s2N 148494, s2N 105840, s2N 195901, s2N 62841, s2N 355299,
   s2N 490993, s2N 571367, s2N 878588, s2N 52951, s2N 645797, s2N 235386, s2P 576885,
   s2P 773348, s2P 723860, s2P 119852, s2N 270861, s2N 1163497, s2P 1310167, s2P 1908070,
   s2N 217195, s2N 809988, s2N 2225895, s2P 527711, s2N 242511, s2N 1959749, s2N 1686242,
   s2N 2484310, s2N 7135123, s2N 4905924, s2N 304157, s2N 611054, s2N 2923605, s2N 7083848,
   s2N 5163810, s2P 4652694, s2P 5962701, s2N 10017239, s2P 9541846, s2N 4158234, s2N 94586,
   s2N 2678637, s2N 275612, s2N 4419719, s2N 4255861, s2P 704613, s2P 822411, s2N 6393116,
   s2N 3336548, s2N 6156156, s2N 5216335, s2N 10099649, s2P 10374279, s2P 20283483,
   s2P 16147073]
private def s2St9VecS1 : List ℤ :=
  [s2P 5693048, s2N 792804, s2N 16922519, s2N 14122106, s2N 17871900, s2P 4756346, s2P 7857212,
   s2P 2733942, s2P 21076251, s2P 7104711, s2N 1503869, s2N 25361966, s2N 23303513,
   s2P 16993258, s2N 6926183, s2N 3353128, s2N 10629547, s2N 14319047, s2N 19676223,
   s2P 41625008, s2P 3027125, s2P 20674968, s2N 17861043, s2P 21973501, s2P 1881949,
   s2N 17535029, s2N 80309301, s2N 66049782, s2N 45271281, s2P 65986070, s2P 51443082,
   s2N 100449904, s2N 125177579, s2N 178749726, s2P 2894932, s2N 72601282, s2N 77482058,
   s2P 77583653, s2P 39404935, s2P 57663601, s2N 60310055, s2P 43137472, s2P 17020541,
   s2P 70199730, s2P 16779405, s2P 215180141, s2N 101783261, s2N 58127917, s2P 1415831,
   s2P 47908114, s2N 36194550, s2P 22200473, s2N 93458958, s2N 24198318, s2N 271952143,
   s2N 72864127, s2N 119632323, s2N 223633579, s2N 81442681, s2N 124938687, s2P 195596975,
   s2P 44366750, s2P 226809109, s2P 190800598]
private def s2St9VecS2 : List ℤ :=
  [s2N 12833777, s2N 121715500, s2P 110369029, s2P 337154145, s2P 57268040, s2P 168671594,
   s2P 275660569, s2P 102549135, s2P 276537439, s2N 241941607, s2P 44666205, s2P 382507601,
   s2N 175501571, s2N 118530119, s2P 534802261, s2P 456336073, s2P 99884609, s2N 89471940,
   s2N 18465558, s2P 78280299, s2P 546804849, s2P 61515549, s2N 192802556, s2P 75898742,
   s2P 433770652, s2P 6364123, s2P 212433841, s2P 94105762, s2N 156656937, s2N 138287391,
   s2N 229492459, s2N 903469533, s2N 869500024, s2N 666841219, s2N 1813255089, s2N 1707230786,
   s2N 1392680460, s2P 531534339, s2P 556208577, s2P 264178100, s2P 838791266, s2P 654413363,
   s2P 633630804, s2P 369089113, s2N 829445897, s2P 160847707, s2P 327313135, s2P 199560564,
   s2P 124408898, s2N 684869739, s2N 726141076, s2N 206868126, s2P 617542520, s2P 1046834756,
   s2P 2161017188, s2P 819766945, s2P 207359728, s2N 1249310992, s2N 1266059984, s2P 976578323,
   s2P 885251881, s2N 1073225348, s2N 190895726, s2P 342842487]
private def s2St9VecS3 : List ℤ :=
  [s2P 273425209, s2N 307954620, s2N 659437709, s2P 41116507, s2N 2548282400, s2N 883257529,
   s2N 344044954, s2N 202669202, s2P 1049294986, s2N 1159132500, s2N 393184327, s2P 1646914586,
   s2N 577222434, s2N 3378357061, s2N 1496336690, s2N 1161881390, s2N 1836363061,
   s2P 1960773540, s2N 619003499, s2N 2393798133, s2P 2165230360, s2N 1071414161,
   s2P 998032735, s2N 3009710396, s2P 1377317544, s2P 827122890, s2P 958116808, s2P 1554154599,
   s2P 2616336858, s2P 5768213330, s2P 1996083273, s2P 1095708501, s2N 1951135504,
   s2N 2735709115, s2N 7152133608, s2N 868550045, s2N 6234471969, s2N 9265156491,
   s2N 5752894185, s2P 3564825997, s2N 888446503, s2P 2144662497, s2P 2902770659,
   s2P 2908366743, s2N 275961539, s2N 4085029323, s2N 7577515108, s2N 17520166796,
   s2N 19102974155, s2N 7030874506, s2N 3647068462, s2N 10509975130, s2N 11637145646,
   s2N 6584165505, s2P 5613535518, s2P 5849579724, s2N 8002777317, s2N 6257849243,
   s2N 4276981425, s2P 4724180124, s2N 4943404118, s2P 17417971357, s2N 13756779846,
   s2P 7316853402]
private def s2St9VecS4 : List ℤ :=
  [s2N 917448995, s2N 610409971, s2N 8466911059, s2N 8019950808, s2N 12702800351,
   s2N 1519436151, s2N 8458414020, s2N 1852973441, s2P 7604769890, s2P 8765504586,
   s2N 3929991440, s2N 397244545, s2P 4251155554, s2N 1452008047, s2N 13812078971,
   s2P 16776289768, s2N 6946860256, s2P 9274723540, s2P 21534695545, s2P 22415308157,
   s2P 7959910165, s2P 7284165809, s2N 6679883743, s2N 5343387787, s2P 2957289376,
   s2P 10596165719, s2P 678321531, s2N 9638052075, s2P 3072622584, s2P 11262147172,
   s2N 2780279347, s2N 9609540358, s2P 6525277661, s2N 23261509121, s2P 18064153634,
   s2N 20228759932, s2P 12567040858, s2N 14471327221, s2N 16810589326, s2N 33973082822,
   s2N 23919624060, s2N 33690615405, s2N 27095195395, s2N 39468922469, s2N 28927539392,
   s2N 9648447330, s2N 14846488180, s2P 7818620101, s2P 3366211737, s2P 22368925143,
   s2P 1059044081, s2N 22642272839, s2P 18880900974, s2P 9644032232, s2P 17700992586,
   s2N 6440283706, s2P 3628720290, s2N 8180970385, s2N 12646117339, s2N 8729629340,
   s2P 33335499288, s2P 40346092109, s2P 42821208869, s2P 79948348267]
private def s2St9VecS5 : List ℤ :=
  [s2P 103867156095, s2P 50331138201, s2P 15895839983, s2P 24039671157, s2P 53498671407,
   s2P 63955311994, s2P 44603278198, s2N 14432053852, s2P 9716113621, s2P 15729593521,
   s2N 70329321960, s2N 47620085609, s2P 132493651435, s2P 29092628127, s2N 20623120866,
   s2N 5426862499, s2N 60100269011, s2P 241474273, s2N 53395602387, s2N 13349587448,
   s2P 58581440459, s2P 40916404501, s2P 74786149245, s2P 149533124122, s2P 96271043246,
   s2P 97322683203, s2N 111668159163, s2N 4149348857, s2P 130854428122, s2P 81134329035,
   s2P 37551900742, s2N 1570679365, s2N 28656172054, s2P 128533263924, s2N 65308729581,
   s2P 248949470073, s2N 213553725918, s2P 130200882054, s2P 14735404937, s2P 95021192486,
   s2N 53195080473, s2N 36181741729, s2P 63108508845, s2P 24332761146, s2N 247507726835,
   s2N 412368063881, s2N 242811316434, s2P 19957618753, s2P 79328359942, s2N 99577913132,
   s2P 8139480159, s2N 93028927346, s2N 255668215483, s2P 185007027483, s2P 39969968509,
   s2P 64492991520, s2P 3936566287, s2P 255054963986, s2N 138452829686, s2N 56322457657,
   s2N 30257133540, s2N 449827988461, s2N 588459136364, s2N 404361581000]
private def s2St9VecS6 : List ℤ :=
  [s2P 368924518674, s2P 125611923337, s2N 214424056460, s2P 853292724246, s2P 671941105766,
   s2P 383369533504, s2N 239207830052, s2P 15220146287, s2N 47417830674, s2P 162772651003,
   s2P 154575942814, s2N 481597853471, s2P 334906093013, s2N 111885464131, s2N 265538766094,
   s2P 183342775247, s2N 16192916517, s2P 542826948748, s2P 583874073999, s2N 99765598513,
   s2P 250153154576, s2N 603643401953, s2N 437020985288, s2P 121878574019, s2P 638814623716,
   s2N 747415871238, s2N 394663015859, s2N 28722862486, s2P 132180266424, s2N 320037061147,
   s2P 460356602428, s2P 54803420061, s2P 133114738325, s2P 134700246007, s2P 396060882980,
   s2N 372727519738, s2P 531637000740, s2P 205984422495, s2N 501623147689, s2P 228322702573,
   s2N 216115458474, s2P 277492380436, s2P 333503959983, s2P 758029522089, s2N 272411122903,
   s2P 93659654739, s2N 321758232838, s2N 906867147736, s2N 311068788324, s2P 349274417031,
   s2P 517732634439, s2N 697616771579, s2N 455996984861, s2N 323079719411, s2N 709158134888,
   s2P 1016545122953, s2P 777665708321, s2P 2104523118024, s2P 706689500552, s2P 777020998518,
   s2P 932513058414, s2P 302239888107, s2N 963626190470, s2N 162985234878]
private def s2St9VecS7 : List ℤ :=
  [s2P 653781539129, s2N 1872581812484, s2N 2495815274570, s2N 1305359926442,
   s2N 2787555770308, s2P 2155818826188, s2P 1324513101946, s2N 1772068695360,
   s2P 1355766245349, s2P 1016172469575, s2N 1360767196296, s2N 1571050403714,
   s2P 415377203837, s2P 1491084886309, s2P 133615188009, s2P 19876451330, s2N 534781890006,
   s2N 1480326446566, s2P 5318039504154, s2N 757232113218, s2P 1575223783788,
   s2N 3762823561607, s2N 5230436580758, s2N 6589659326384, s2N 3209785245100,
   s2N 2475496646368, s2N 2744044279932, s2P 1081161376090, s2P 6726372362093,
   s2P 5613409334847, s2P 4987604069213, s2N 288085061358, s2N 16340453281392,
   s2P 103446992194, s2P 4628801610727, s2N 10682883132087, s2N 17905981120002,
   s2P 4310556672327, s2N 6703484513321, s2N 13284298459154, s2P 2043748998539,
   s2P 4802450439326, s2N 13183740101601, s2N 3133164101614, s2N 19404775554367,
   s2P 4759547791310, s2P 14014958600112, s2N 9365973549685, s2P 1568947168039,
   s2P 10351899077745, s2P 15972499214200, s2P 28688066422126, s2P 37605692046361,
   s2N 3612585327721, s2P 18001115836326, s2P 80295586796660, s2P 270774744989159,
   s2P 447088391496321, s2P 543081534387650, s2P 468869262956995, s2P 381777304606582,
   s2P 218518012003573, s2P 82053093850926, s2P 15127967766812]
private def s2St9VecS8 : List ℤ :=
  [s2P 1801260035746]
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
  [s2N 19027, s2N 5560, s2P 10657, s2P 3015, s2P 40474, s2N 66398, s2N 144133, s2N 101926,
   s2N 122433, s2P 32883, s2P 261341, s2P 123663, s2P 338170, s2P 208170, s2P 66025, s2N 96972,
   s2N 387777, s2P 340503, s2P 657439, s2P 362033, s2P 1003355, s2P 644660, s2P 125605,
   s2P 593710, s2P 87473, s2P 39298, s2N 795295, s2P 48074, s2P 619816, s2P 998556,
   s2P 1937438, s2P 329183, s2P 197211, s2N 2958678, s2N 1542122, s2N 446573, s2P 799698,
   s2N 2319612, s2N 1818116, s2P 1862180, s2N 1136910, s2N 727628, s2P 1673061, s2P 1952017,
   s2P 947503, s2P 4773132, s2P 5756608, s2P 11665436, s2P 9292483, s2P 10970994, s2P 4490305,
   s2N 2997482, s2N 1110423, s2P 4120993, s2P 2768417, s2P 7111410, s2N 3625336, s2N 3745211,
   s2N 7583576, s2N 3462480, s2N 1243742, s2P 10752279, s2P 11236226, s2P 5005327]
private def s2St10VecS1 : List ℤ :=
  [s2N 2936808, s2N 5021316, s2P 1096209, s2P 5501259, s2N 22589744, s2N 14962334, s2N 8630574,
   s2N 26554220, s2N 9284115, s2N 16845110, s2N 10636745, s2N 7177556, s2N 4376175,
   s2N 5877630, s2N 24266887, s2N 10660770, s2N 15115067, s2N 40439252, s2N 29026330,
   s2N 8249602, s2P 34963206, s2N 6093615, s2P 4510768, s2N 16626478, s2N 1926210,
   s2P 21754168, s2P 14201219, s2P 22803222, s2N 10926760, s2P 54210263, s2P 26541118,
   s2P 58481206, s2P 98195754, s2P 135911664, s2P 64240150, s2P 102927024, s2P 94954271,
   s2P 127775354, s2N 14326262, s2N 71021861, s2N 79118288, s2P 19246719, s2P 33834677,
   s2N 90238592, s2N 64717388, s2P 94373110, s2P 288006357, s2P 129709242, s2N 42357544,
   s2N 31659470, s2P 58196207, s2N 33017278, s2P 10066121, s2P 100510044, s2P 11511157,
   s2N 98666238, s2N 63400186, s2P 139961110, s2N 87533362, s2N 43190241, s2N 108157676,
   s2N 6213268, s2P 16967656, s2P 26220537]
private def s2St10VecS2 : List ℤ :=
  [s2P 4091220, s2N 89499125, s2N 159268617, s2N 209907710, s2N 124925364, s2N 249705694,
   s2P 69450113, s2P 398101119, s2P 165675078, s2P 467441846, s2P 539088183, s2P 281481919,
   s2P 55748562, s2N 248377497, s2N 111971786, s2P 122786356, s2P 67572578, s2P 110003458,
   s2N 146299160, s2N 272162201, s2N 57466169, s2P 301200355, s2P 296245209, s2P 157175595,
   s2N 143614506, s2N 280279359, s2N 182247629, s2P 164469743, s2P 457917201, s2P 494211398,
   s2P 9018557, s2N 78364892, s2N 223289434, s2N 162839514, s2N 511912614, s2N 9331651,
   s2N 548475113, s2N 30572897, s2N 197546741, s2N 557244883, s2N 386299550, s2N 495961027,
   s2N 1005977368, s2N 469810375, s2P 851863500, s2P 249242051, s2P 1604652336, s2P 2010465976,
   s2N 1179387780, s2N 837318622, s2P 564420081, s2P 410987291, s2N 1240552346, s2P 283711073,
   s2P 1185010465, s2P 72672623, s2P 132177771, s2N 256080035, s2P 220122418, s2N 322062159,
   s2P 126453217, s2P 295094394, s2P 479651390, s2P 239810421]
private def s2St10VecS3 : List ℤ :=
  [s2P 583875665, s2N 421304209, s2N 2070863824, s2N 1300519791, s2P 3114525381, s2P 316459130,
   s2N 1366771131, s2N 959452946, s2N 322428860, s2N 707825221, s2N 1112169144, s2P 443970999,
   s2N 126821778, s2P 2084597147, s2P 378334172, s2P 867808826, s2P 3798737903, s2P 2618293436,
   s2P 1909993878, s2P 556804232, s2P 1444093853, s2P 824286369, s2P 275774901, s2P 978682913,
   s2P 1983615889, s2N 814950252, s2N 305745473, s2N 3979041256, s2N 2628922174,
   s2P 1172411090, s2P 189035027, s2N 1284064970, s2N 849294581, s2P 2398520133, s2P 998054587,
   s2N 3830947679, s2P 339465250, s2N 6310496255, s2N 6063021837, s2N 6155873985,
   s2N 5182711762, s2N 1309239407, s2P 1500639989, s2N 3361250093, s2N 6353574751,
   s2P 2678278243, s2P 30021028, s2N 9984790553, s2N 12364629619, s2N 12225246609,
   s2N 2709555891, s2P 713106462, s2N 5103491491, s2N 4558157442, s2N 1844635450,
   s2P 6291004755, s2N 1009659474, s2P 6339198315, s2N 14674487164, s2N 17422203641,
   s2N 2510688654, s2P 5921388292, s2N 8610348854, s2N 11136022347]
private def s2St10VecS4 : List ℤ :=
  [s2N 19326063561, s2N 20432466198, s2P 4081856032, s2P 9232431544, s2P 8541366260,
   s2P 4079491699, s2P 3854360385, s2P 627529857, s2P 4363904598, s2N 5261024992,
   s2P 13465625178, s2N 2576020043, s2N 9630173768, s2P 449046544, s2P 12387962141,
   s2P 10922946937, s2N 6419319207, s2N 6259773265, s2N 13124147974, s2P 291278279,
   s2P 1462496248, s2N 1542049656, s2P 173210592, s2P 6662471657, s2N 1642551968,
   s2P 3238567472, s2P 3038555700, s2P 3008886071, s2P 975489593, s2N 1547844178,
   s2P 1904325265, s2P 22341468903, s2P 18087738012, s2P 21823204556, s2P 24644399402,
   s2P 26350629431, s2P 14343719610, s2N 12825256621, s2N 6288222156, s2P 525532925,
   s2P 16967415753, s2P 3531374448, s2P 13521790242, s2N 11814357136, s2N 16365207635,
   s2P 4615422831, s2P 19816608122, s2P 8835436262, s2P 10077168382, s2P 15464211711,
   s2P 33440387412, s2P 22187477108, s2N 1089275223, s2P 2302728218, s2N 2930683135,
   s2N 39929068413, s2N 53419231663, s2N 21026613704, s2N 19291911026, s2N 21162091271,
   s2N 8201875681, s2P 6852757634, s2N 4229837958, s2N 22419857522]
private def s2St10VecS5 : List ℤ :=
  [s2P 19542650666, s2P 6061954680, s2P 35588730457, s2P 10858811894, s2N 14331550153,
   s2N 15854904314, s2N 9386496612, s2P 44410557127, s2P 31371368253, s2P 23721439069,
   s2N 73808875074, s2N 127679845412, s2N 145092494393, s2N 94164093288, s2N 55370719333,
   s2N 6851920236, s2P 609774961, s2P 12477734420, s2N 26941024788, s2N 33551089755,
   s2P 19788642848, s2P 121724137466, s2P 12507017320, s2N 115641584805, s2N 128641688651,
   s2N 51248909343, s2P 114855831482, s2P 92351895183, s2P 30211186136, s2N 148308737749,
   s2N 65795217178, s2N 11916795432, s2N 87372084566, s2N 100835641393, s2N 3241022546,
   s2N 211841168516, s2N 192557450373, s2N 227071848006, s2N 102105830966, s2N 3729731718,
   s2N 50382101067, s2P 21367076627, s2P 26159380899, s2N 147085575632, s2P 30899199446,
   s2P 2812252439, s2N 86113176475, s2N 10158205553, s2N 173002284952, s2P 114348377853,
   s2P 182121157285, s2P 51685058188, s2P 320079255608, s2P 445266531397, s2P 51343349599,
   s2N 312373183258, s2N 107239240831, s2P 9568914722, s2P 170766593931, s2N 201806638626,
   s2P 180261159970, s2P 72988265995, s2P 276903592143, s2N 18182051298]
private def s2St10VecS6 : List ℤ :=
  [s2N 629665102341, s2N 212122143865, s2N 363342957581, s2N 416750570618, s2N 492077719239,
   s2N 502438962778, s2P 229058087956, s2P 164960905312, s2P 561871112598, s2N 318387546781,
   s2P 482253055710, s2P 101069324999, s2P 156689964887, s2P 702497839222, s2P 516922480206,
   s2N 215883470552, s2N 304251709668, s2P 221256804519, s2N 386153790874, s2N 185087331246,
   s2N 303799657262, s2N 155632280234, s2P 19353563458, s2P 539785691503, s2P 108212537486,
   s2P 235250279238, s2N 346427285886, s2P 182282888851, s2N 760334000469, s2N 849969498479,
   s2N 243503602280, s2N 53703033817, s2N 785862288315, s2P 137454442754, s2P 121798025331,
   s2P 168965062020, s2N 79081131917, s2P 14332905952, s2N 489739507745, s2P 614713722664,
   s2P 119520834241, s2N 144580372452, s2P 390732838337, s2P 544173555043, s2P 566368985827,
   s2P 576092065773, s2N 374636066424, s2N 227698998122, s2P 321470609979, s2P 250486634725,
   s2N 188075212847, s2N 786182990931, s2P 238802909247, s2P 580630710620, s2P 1594440685132,
   s2N 1076124784815, s2P 821215378792, s2P 745028543854, s2P 448930897271, s2P 197262879298,
   s2P 942625796263, s2P 89209801632, s2N 663128982703, s2N 484716080190]
private def s2St10VecS7 : List ℤ :=
  [s2N 345822264825, s2P 576602243696, s2P 1250340081407, s2P 1414327190175, s2P 2760124318808,
   s2P 126712644661, s2P 594668777906, s2P 1143725938822, s2P 2492926301639, s2P 3140003589744,
   s2P 3238713158995, s2P 1897013223680, s2P 1762683973962, s2P 1648601808986,
   s2P 3003606119268, s2P 1187999134886, s2P 2934380432220, s2P 1705360279429,
   s2P 634601090327, s2P 352626269786, s2N 343085534455, s2N 379339653698, s2P 85211251451,
   s2N 73026288542, s2N 3946873916246, s2P 3250075456589, s2P 1767290997279, s2N 3125014314614,
   s2N 2533417428014, s2P 5112509248451, s2P 5208107899218, s2P 6614196176201,
   s2N 10545119470904, s2N 16641974627400, s2N 13915935424738, s2N 10349226084268,
   s2N 2207646746696, s2P 8055046629259, s2P 17038155459537, s2N 4274411153354,
   s2N 4306741011067, s2P 6706718246279, s2P 4685173771092, s2P 17219302953201,
   s2P 7954564956056, s2N 3569115766819, s2N 16678919195275, s2N 12903486110315,
   s2N 3570100927528, s2P 10148745564830, s2P 12592988414109, s2P 13913180451178,
   s2N 1778675193292, s2P 10272436995141, s2P 49510507909905, s2P 22912021971848,
   s2P 22640593714928, s2P 44596914731028, s2P 158277338250164, s2P 395014675060768,
   s2P 552342245141251, s2P 560271259636771, s2P 397567990270662, s2P 177920739833135]
private def s2St10VecS8 : List ℤ :=
  [s2P 44206705838470]
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
private def s2Chk11 : List Rkm128kSeg := s2Rem11
private theorem s2Chk0_ok :
    s2RunAt s2Chk0 hm256k512krS2LIn hm256k512krS2DCurIn
      hm256k512krS2PadIn hm256k512krS2VecIn
      4 512 895001622 s2St0Vec = true := by decide +kernel
private theorem s2Chk1_ok :
    s2RunAt s2Chk1 4 512
      895001622 s2St0Vec
      4 512 920722789 s2St1Vec = true := by decide +kernel
private theorem s2Chk2_ok :
    s2RunAt s2Chk2 4 512
      920722789 s2St1Vec
      4 512 950734085 s2St2Vec = true := by decide +kernel
private theorem s2Chk3_ok :
    s2RunAt s2Chk3 4 512
      950734085 s2St2Vec
      4 512 967296531 s2St3Vec = true := by decide +kernel
private theorem s2Chk4_ok :
    s2RunAt s2Chk4 4 512
      967296531 s2St3Vec
      4 512 988956775 s2St4Vec = true := by decide +kernel
private theorem s2Chk5_ok :
    s2RunAt s2Chk5 4 512
      988956775 s2St4Vec
      4 512 1027027140 s2St5Vec = true := by decide +kernel
private theorem s2Chk6_ok :
    s2RunAt s2Chk6 4 512
      1027027140 s2St5Vec
      4 512 1059713070 s2St6Vec = true := by decide +kernel
private theorem s2Chk7_ok :
    s2RunAt s2Chk7 4 512
      1059713070 s2St6Vec
      4 512 1088402264 s2St7Vec = true := by decide +kernel
private theorem s2Chk8_ok :
    s2RunAt s2Chk8 4 512
      1088402264 s2St7Vec
      4 512 1105736906 s2St8Vec = true := by decide +kernel
private theorem s2Chk9_ok :
    s2RunAt s2Chk9 4 512
      1105736906 s2St8Vec
      4 512 1123835630 s2St9Vec = true := by decide +kernel
private theorem s2Chk10_ok :
    s2RunAt s2Chk10 4 512
      1123835630 s2St9Vec
      4 512 1148274915 s2St10Vec = true := by decide +kernel
private theorem s2Chk11_ok :
    s2RunAt s2Chk11 4 512
      1148274915 s2St10Vec
      hm256k512krS2LOut hm256k512krS2DCurOut
      hm256k512krS2PadOut hm256k512krS2Vec = true := by decide +kernel

/-- Segment count of hm256k512krS2Segs (33 segments). -/
theorem hm256k512krS2_len : rkm128kSegListLen hm256k512krS2Segs = 33 := by
  rfl

/-- Exact rkm128kRunSegs 256 4 512 step across hm256k512krS2Segs (segs 90..122). -/
theorem hm256k512krS2_step :
    rkm128kRunSegs 256 4 512 hm256k512krS2Segs hm256k512krS2LIn
      hm256k512krS2DCurIn hm256k512krS2PadIn hm256k512krS2VecIn =
      (hm256k512krS2LOut, hm256k512krS2DCurOut,
       hm256k512krS2PadOut, hm256k512krS2Vec) := by
  exact s2RunStepTd s2Chk0_ok
    (s2RunStepTd s2Chk1_ok
    (s2RunStepTd s2Chk2_ok
    (s2RunStepTd s2Chk3_ok
    (s2RunStepTd s2Chk4_ok
    (s2RunStepTd s2Chk5_ok
    (s2RunStepTd s2Chk6_ok
    (s2RunStepTd s2Chk7_ok
    (s2RunStepTd s2Chk8_ok
    (s2RunStepTd s2Chk9_ok
    (s2RunStepTd s2Chk10_ok
    (s2RunLast s2Chk11_ok)))))))))))

/-- Suffix chaining lemma advancing rkm128kRunSegs 256 4 512 past hm256k512krS2Segs. -/
theorem hm256k512krS2_run_after (rest : List Rkm128kSeg) :
    rkm128kRunSegs 256 4 512 (hm256k512krS2Segs ++ rest) hm256k512krS2LIn
      hm256k512krS2DCurIn hm256k512krS2PadIn hm256k512krS2VecIn =
      rkm128kRunSegs 256 4 512 rest hm256k512krS2LOut hm256k512krS2DCurOut
        hm256k512krS2PadOut hm256k512krS2Vec := by
  rw [rkm128kRunSegs_append]
  dsimp only
  rw [hm256k512krS2_step]

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_0 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM64K128KrCert.isMidM64K128KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_1 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K128KrCert.isMidM16K128KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_2 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM128K128KrCert.isHiTailM128K128KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_3 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM32K512KrPt1.mm32k512krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_4 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM256K512KrPt0.hm256k512krS0SegsR3)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_5 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K512KrPt1.mm16k512krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_6 : True :=
  (And.intro
    (Eq.refl
      Rk128kLowM4K512L248KrPt1.lm4k512l248krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_7 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K256KrCert.isMidM16K256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_8 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM32K512KrPt0.mm32k512krS0SegsR3)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_9 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM256K512KrPt1.hm256k512krS1Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_10 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K512KrPt0.mm16k512krS0SegsR3)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_11 : True :=
  (And.intro
    (Eq.refl
      Rk128kHiM1024F256KrCert.isHiTailM1024Full256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_12 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM64K256KrCert.isMidM64K256KrotovCertCell)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_13 : True :=
  (And.intro
    (Eq.refl
      Rk128kLowM4K512L248KrPt2.lm4k512l248krS2Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_14 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM16K512KrPt2.mm16k512krS2Segs)
    trivial).right

open QuantumComputation.Specs.GroverFindAll in
private theorem _ord_w2_15 : True :=
  (And.intro
    (Eq.refl
      Rk128kMidM32K512KrPt2.mm32k512krS2Segs)
    trivial).right

end

end Rk128kHiM256K512KrPt2
end QuantumComputation.Specs.GroverFindAll
