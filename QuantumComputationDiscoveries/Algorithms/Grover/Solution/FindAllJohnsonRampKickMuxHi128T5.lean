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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T4

/-
# High-`m` Coupled Walk Part `5` (`FindAllJohnsonRampKickMuxHi128T5`)

Certifies `(m = 128, r = 512)` Part A (`s = 0..3` + `77` steps of `s = 4`).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Zigzag `< 2 ^ 58` orbital vector decoder (`FindAllJohnsonRampKickMuxHi128T5`). -/
def rkmZigHi128T5 : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: rkmZigHi128T5 ws
/-- Unpacks `len` LSB-first bits of `< 2 ^ 50` word `w`
  (`FindAllJohnsonRampKickMuxHi128T5`). -/
def rkmWordBitsHi128T5 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWordBitsHi128T5 j (Nat.div w 2)
/-- Unpacks `< 2 ^ 50` words of lengths `ns` (`FindAllJohnsonRampKickMuxHi128T5`). -/
def rkmUnpackMaskHi128T5 : List ℕ → List ℕ → List Bool
  | [], _ => []
  | _, [] => []
  | n :: ns, w :: ws => rkmWordBitsHi128T5 n w ++ rkmUnpackMaskHi128T5 ns ws
/-- Mask segment `0` for `(m = 128, r = 512)`. -/
def rkmMkHiHiB_m128_r512_s0 : List Bool := rkmUnpackMaskHi128T5 [10] [960]
/-- Mask segment `1` for `(m = 128, r = 512)`. -/
def rkmMkHiHiB_m128_r512_s1 : List Bool :=
  rkmUnpackMaskHi128T5 [50, 33]
    [840053126971517, 8558468097]
/-- Mask segment `2` for `(m = 128, r = 512)`. -/
def rkmMkHiHiB_m128_r512_s2 : List Bool :=
  rkmUnpackMaskHi128T5 [50, 50, 50, 28]
    [244867137120827, 519373206372218, 1007045285805852, 268173311]
/-- Mask segment `3` for `(m = 128, r = 512)`. -/
def rkmMkHiHiB_m128_r512_s3 : List Bool :=
  rkmUnpackMaskHi128T5 [50, 50, 50, 50, 50, 50, 50, 22]
    [618697809116860, 68719841553, 1207959554, 907756799891456, 265959165031324, 4292901918,
     1124800395214848, 3670031]
/-- Quantized generator list `s = 0` for `(128, 512)`. -/
def rkmHbHiHiB_m128_r512_s0 : List ℤ := altBuildHbFrom 128 512 270215224489 0 128
/-- Input orbital vector `s = 0` for `(128, 512)`. -/
def rkmViHiHiB_m128_r512_s0 : List ℤ := [rkmP 1000000000000000]
/-- Output orbital vector `s = 0` for `(128, 512)`. -/
def rkmVoHiHiB_m128_r512_s0 : List ℤ := rkmZigHi128T5
  ([28588, 230236, 1304124, 5998748, 23766194, 83756440, 267969588, 789339198, 2162792748,
    5555759890, 13462669098, 30927474296, 67634635466, 141286932686, 282758011202,
    543502549096, 1005569034056, 1794229819778, 3092678918242, 5157451369840, 8332258478124,
    13056964198766, 19867684146542, 29383755886400, 42277885869656, 59227315623492,
    80846387237094, 107604210585676, 139734774755248, 177150131455114, 219369445932134,
    265477072260400, 314120929667548, 363558300828038, 411750180168178, 456498345816948,
    495612581245286, 527090165172636, 549286919169438, 561059364746398, 561860941449546,
    551781234351800, 531524736889352, 502333551656924, 465865321660314, 424042546427302,
    378891656965266, 332389693549734, 286333520613250, 242241948778206, 201295819117944,
    164315934298226, 131774425047734, 103832182947686, 80393539134486, 61169322615576,
    45740495644180, 33616338195656, 24283227135226, 17242073722710, 12034191384764,
    8256624083080, 5568738622492, 3692216314706, 2406563998044, 1542014352912, 971309513316,
    601449751088, 366104047684, 219058895102, 128840625560, 74483718930, 42321795770,
    23633887252, 12970154392, 6994569382, 3706345174, 1929563736, 986861360, 495779020,
    244625700, 118533324, 56395056, 26341272, 12076894, 5433984, 2399062, 1039044, 441354,
    183816, 75036, 30008, 11746, 4494, 1674, 602, 204, 64, 16, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
   [0])
/-- Quantized generator list `s = 1` for `(128, 512)`. -/
def rkmHbHiHiB_m128_r512_s1 : List ℤ := altBuildHbFrom 256 512 144965901639 0 256
/-- Input orbital vector `s = 1` for `(128, 512)`. -/
def rkmViHiHiB_m128_r512_s1 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m128_r512_s0 rkmVoHiHiB_m128_r512_s0
/-- Output orbital vector `s = 1` for `(128, 512)`. -/
def rkmVoHiHiB_m128_r512_s1 : List ℤ := rkmZigHi128T5
  ([284326, 1503014, 5540646, 16428756, 41506800, 92142070, 183097408, 329544758, 541215388,
    814370070, 1123924410, 1419495774, 1629408170, 1675032724, 1494201124, 1067811796,
    440074046, 277760547, 926558897, 1340067511, 1396882737, 1066448449, 430899499, 329118068,
    984370618, 1328705202, 1248657646, 765739660, 34378286, 706164537, 1210724757, 1311030833,
    973282215, 310064253, 457672966, 1075181514, 1339019228, 1163579118, 607145202, 149905287,
    865777869, 1315424161, 1360300921, 988161299, 312297753, 466905690, 1123931510, 1473573708,
    1420685468, 981506768, 273272362, 522001505, 1207318877, 1619770855, 1666622193,
    1341169951, 717203683, 73738828, 874729944, 1536886900, 1946595132, 2041922910, 1816812974,
    1314462322, 613205480, 191007673, 1001697749, 1735625967, 2331659115, 2754402555,
    2993260535, 3058170291, 2973437391, 2770948101, 2483654297, 2139726611, 1757219891,
    1338523377, 863248817, 277473507, 523710452, 1724729702, 3635418252, 6763135870,
    11923482330, 20406478942, 34220648360, 56443924032, 91717411954, 146925031038,
    232107867122, 361665081034, 555891277452, 842890768856, 1260889274084, 1860930459468,
    2709896126980, 3893723812676, 5520615170310, 7723936731862, 10664418916868, 14531170789484,
    19540961895614, 25935196014140, 33974033078902, 43927221271220, 56061392640414,
    70623855286468, 87823274095482, 107808047358752, 130643621162742, 156290387643812,
    184584129494978, 215221142728898, 247750141217636, 281572785027056, 315954169952064,
    350043888546288, 382907376623174, 413566276799166, 441045587152330, 464424533012152,
    482887512123868, 495771205268324, 502604067729526, 503134928637604, 497348283647026,
    485464985451226] ++
  ([467928295911624, 445376524277660, 418604599435088, 388517790351354, 356081312099486,
    322269693650802, 288019544500348, 254188790940926, 221524645030354, 190641626647806,
    162009993678728, 135954050196376, 112659079174702, 92185137532808, 74485678301638,
    59428918820396, 46820022424000, 36422455243612, 27977263305960, 21219432665904,
    15890898739014, 11750123797346, 8578440695662, 6183556442530, 4400722643236, 3092120935150,
    2144995270714, 1469006310718, 993202858740, 662915560340, 436790152446, 284098991528,
    182404712084, 115600207876, 72314180992, 44649449422, 27209551502, 16365283034, 9714178760,
    5690520568, 3289602752, 1876557964, 1056302666, 586681886, 321502378, 173824670, 92717558,
    48787958, 25324410, 12966326, 6548150, 3261492, 1602062, 776018, 370642, 174530, 81004,
    37050, 16690, 7396, 3216, 1364, 560, 220, 76, 22, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
   [0]))
/-- Quantized generator list `s = 2` for `(128, 512)`. -/
def rkmHbHiHiB_m128_r512_s2 : List ℤ := altBuildHbFrom 384 512 103288654545 0 384
/-- Input orbital vector `s = 2` for `(128, 512)`. -/
def rkmViHiHiB_m128_r512_s2 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m128_r512_s1 rkmVoHiHiB_m128_r512_s1
/-- Output orbital vector `s = 2` for `(128, 512)`. -/
def rkmVoHiHiB_m128_r512_s2 : List ℤ := rkmZigHi128T5
  ([1049306213, 465825879, 268472019, 568254027, 706015194, 875279183, 503612826, 340304708,
    281757201, 193989670, 994584223, 1011067894, 589094207, 172705551, 382866218, 295190488,
    662689744, 947394107, 342641425, 479578608, 1419498649, 2032046990, 310860181, 51707183,
    693698675, 347935532, 84651183, 267357107, 27488962, 335138346, 1274480942, 889941093,
    1081561415, 838838454, 748563593, 625925619, 1162626130, 154965136, 606300228, 1332044868,
    1375265345, 1859345945, 488901446, 196168538, 292197523, 1243639108, 710415752, 1139681935,
    586242757, 284465234, 396519183, 274633895, 662937708, 234680474, 786062819, 739565465,
    56950321, 616429034, 1126375462, 1147613652, 1246542430, 2061382770, 2192377914, 565562796,
    666996731, 349066708, 1459833174, 329007346, 1304406057, 992284439, 143619330, 7135670,
    668495297, 292157005, 426830360, 123338548, 526486479, 206435503, 616115580, 784554350,
    590458114, 872665314, 1095529570, 280035454, 846852969, 574358159, 1086054374, 2149423660,
    1389435764, 117564453, 780554957, 656564119, 865828397, 1576250453, 1782276335, 1005118619,
    124534749, 84655873, 493842801, 230147551, 824502754, 1426329582, 568476816, 1058214515,
    1680596927, 441314667, 1587345024, 2511177746, 1539586512, 344468099, 1505251809,
    1218849559, 116340099, 687776098, 686815782, 237803302, 38116881, 74264324, 291401830,
    246846846, 121588561, 585599949, 926585037, 1144591767, 1366752851, 1597292749, 1610805185,
    1129998985] ++
  ([137442687, 970146936, 1552919134, 1127460770, 283900947, 2099902415, 3464634783,
    3693582753, 2619563875, 657377729, 1420364244, 2852130996, 3206476068, 2513495374,
    1183419986, 213003071, 1184404139, 1479752963, 1127032781, 364896813, 481206232,
    1120997454, 1379186146, 1219274054, 720251158, 27335392, 700945555, 1333383483, 1787477335,
    2032372409, 2078670139, 1961540761, 1722153299, 1389653397, 962663561, 385933857,
    485803488, 1949020690, 4555568384, 9285549612, 17824907480, 32996647748, 59409581246,
    104404037250, 179387550880, 301661069452, 496832353172, 801891434372, 1268976281320,
    1969779001634, 3000430315096, 4486553476908, 6588005849942, 9502642762334, 13468269020528,
    18761821445276, 25694789125756, 34603964708060, 45836860716242, 59731535089850,
    76591142181688, 96654223053900, 120062505263458, 146828703849692, 176807391084506,
    209672319648616, 244903545606658, 281787243011650, 319430222509072, 356789915286148,
    392719076787338, 426022869259708, 455524496931060, 480134393896446, 498917275833802,
    511151278891796, 516373961227326, 514411086798656, 505385717476184, 489707015086906,
    468040071308302, 441259810632680, 410393352006206, 376556029166250, 340886494686610,
    304485984511244, 268365985929672, 233407373196410, 200332720523830, 169692143576120,
    141861808433900, 117053293499716, 95331359460770, 76637390854266, 60815792785568,
    47640898901970, 36842394451082, 28127798875180, 21201110142566, 15777226740024,
    11592190744040, 8409614178986, 6023856172472, 4260619243856, 2975647524976, 2052160388286,
    1397564946648, 939880931544, 624198195918, 409382380048, 265155318276, 169606757848,
    107143075016, 66845044372, 41187362420, 25064174138, 15064057674, 8941980152, 5242423682,
    3035570038, 1736043840, 980608146, 547074278, 301449272, 164058976, 88186832, 46819314,
    24550654] ++
  ([12714996, 6504022, 3285912, 1639580, 807980, 393224, 188988, 89684, 42014, 19418, 8846,
    3966, 1742, 742, 302, 116, 40, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0] ++
   [0])))
/-- Quantized generator list `s = 3` for `(128, 512)`. -/
def rkmHbHiHiB_m128_r512_s3 : List ℤ := altBuildHbFrom 640 512 70422535211 0 512
/-- Input orbital vector `s = 3` for `(128, 512)`. -/
def rkmViHiHiB_m128_r512_s3 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m128_r512_s2 rkmVoHiHiB_m128_r512_s2
/-- Output orbital vector `s = 3` for `(128, 512)`. -/
def rkmVoHiHiB_m128_r512_s3 : List ℤ := rkmZigHi128T5
  ([390501385, 1517904506, 120001097, 1384970046, 29950720, 839838957, 396796489, 155045080,
    836860101, 100788216, 458885134, 67568935, 947257941, 707702769, 653534113, 227260270,
    112686282, 720733430, 2483349715, 79947092, 118384161, 325590104, 195088892, 325322999,
    1167725402, 381496975, 3084974, 527338708, 222806361, 1849874634, 107760285, 683869463,
    187211518, 414149196, 419044545, 474808866, 743064474, 635387104, 313780840, 535487214,
    63188862, 64540548, 870074769, 1105105038, 1709541198, 376294513, 687352009, 1971352345,
    816158640, 1230972694, 795216948, 1007264327, 243137962, 456672013, 872613723, 2518481,
    1951365950, 384796535, 486571629, 475492902, 327017412, 1299673214, 1563329256, 516549916,
    588442313, 1466054577, 1689191528, 4415149075, 4588540192, 7090201541, 10181186622,
    17246442445, 28704457562, 44531822379, 62580707930, 88868994609, 124138715682,
    167015792159, 214286541448, 266974331447, 315763682830, 349793328829, 356478187562,
    330779251667, 264544540338, 156773337043, 16525682648, 125729908404, 239473649185,
    291426167498, 260643086143, 147079697376, 16832382960, 175441589267, 264917283472,
    247428671845, 120738358494, 61214325080, 215751187813, 258818653056, 165394528211,
    20831641947, 192540252828, 250550445563, 153555533262, 42714376960, 210661994217,
    234215600546, 91227514879, 117466207957, 239422112756, 174306118737, 27341779763,
    206963376292, 213864957383, 38945845390, 170921918060, 227961539825, 76457506050,
    146497953744, 232303957763, 89238584418, 143360758744, 231321399425, 77530850490,
    157662439412, 223327558557, 45252710396] ++
  ([183686274286, 206802682865, 9132160309, 218121057430, 165271849943, 87791051295,
    234569983130, 88753292429, 172836365435, 211367878032, 26502444702, 230800697993,
    125527341688, 153236214268, 219672938507, 19677066329, 235038771482, 111188203039,
    174281007011, 205777525694, 71342649592, 243689675713, 40654168354, 224378525112,
    140558139581, 168949703817, 205868846420, 87461286308, 241466113717, 4907835567,
    244258552218, 71726139837, 225071851053, 133961646976, 190684271382, 182613172815,
    152702799873, 214835382652, 114635146548, 233233275201, 77834338871, 245162877106,
    48504546334, 251339559189, 26934062529, 254188314630, 12316161768, 258599319067,
    9547983729, 260615409304, 15234599906, 261899549627, 29861396373, 261514706420,
    53160717126, 258407284087, 86208315189, 247969528702, 126085024106, 228162572873,
    171571339033, 194103705966, 217569599202, 142940207959, 258095032993, 71951916344,
    283380862310, 17698764994, 281220717957, 117986844967, 240955411812, 214215123100,
    155836206359, 282888301295, 32669536978, 302382824010, 112979138644, 249178765983,
    241989365487, 124868002604, 316243511432, 55562125092, 286979175313, 230187745747,
    147428795020, 328876419300, 68538783048, 287085002141, 270432459989, 97485003314,
    347069085638, 164176682598, 224331306033, 343832044335, 51065602051, 306080515440,
    310197671572, 43617227473, 355490725403, 278783864593, 102725707480, 379703039940,
    260826676984, 129555202739, 393564978855, 267789197953, 123744494142, 404227639654,
    309422684326, 73055253641, 397834360929, 378436011791, 32420668927, 347428302944,
    447907484066, 188906394728, 225244032065, 477123905991, 379367877649, 3819205229,
    383870326528, 518029244686, 310131107624, 104992821597, 467975224569, 560298377041,
    329216826965, 94595538532] ++
  ([482028623446, 633066691640, 474596709708, 84264779180, 359297853127, 664752233327,
    709194115815, 479162946863, 62584593185, 395412412746, 748872064160, 896950295394,
    806282982542, 508214033946, 78026879628, 393021241663, 823044341161, 1156117294597,
    1368174431525, 1463440492911, 1464120113125, 1396102015081, 1272615768211, 1076813245987,
    743662018901, 141582017993, 945097229206, 2830768226004, 5937146120130, 10792050478534,
    18014596465572, 28283923979586, 42290405799260, 60670831619180, 83932007572254,
    112370044085790, 145994775562930, 184469759585990, 227077794983328, 272719775311804,
    319951142475992, 367055683367656, 412151582398804, 453320253947456, 488745231476998,
    516846807047780, 536398446332762, 546613186640420, 547191900722250, 538329897492378,
    520683140433462, 495299714364742, 463525502283026, 426894988619720, 387018564084318,
    345476780646054, 303729987121712, 263049073480896, 224470107095960, 188772861294594,
    156480929415554, 127879479426478, 103045802904342, 81887605682592, 64184352720410,
    49627747838452, 37858418987316, 28496926383674, 21168183008012, 15519186381750,
    11230562236002, 8022806932682, 5658306326260, 3940241278222, 2709408621286, 1839834802820,
    1233875639716, 817308843660, 534756097182, 345629719360, 220689603828, 139218356372,
    86772494120, 53439765038, 32521357828, 19557717516, 11623467074, 6827204004, 3963331726,
    2274092220, 1289747472, 723049866, 400696846, 219514922, 118885290, 63653584, 33694744,
    17634334, 9124842, 4668436, 2361598, 1181234, 584198, 285670, 138112, 66006, 31176, 14542,
    6690, 3028, 1344, 578, 236, 88, 28, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ++
  ([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0] ++
   [0]))))
/-- Quantized generator list `s = 4` for `(128, 512)`. -/
def rkmHbHiHiB_m128_r512_s4 : List ℤ := altBuildHbFrom 896 512 56557377049 0 512
/-- Input orbital vector `s = 4` for `(128, 512)`. -/
def rkmViHiHiB_m128_r512_s4 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m128_r512_s3 rkmVoHiHiB_m128_r512_s3
/-- Midpoint orbital vector `s = 4a` (`77` steps) for `(128, 512)`. -/
def rkmMidHiHiB_m128_r512_s4a : List ℤ := rkmZigHi128T5
  ([1015486195, 649158319, 340224426, 1658830299, 2787601530, 6177480063, 12689408882,
    30832858697, 64667686180, 115944824627, 183702609626, 260766303647, 324034860558,
    346401976999, 298083981852, 174308232845, 1436276591, 174034061640, 268576487085,
    231878709158, 73717678193, 120703262321, 235899367354, 193912963771, 16442650602,
    175679893056, 238210467321, 111743515148, 100747559270, 228595323907, 159525719652,
    47367069254, 208159321657, 168729329140, 29319553328, 201033415947, 177153244142,
    18116045072, 177295371117, 137576292290, 65298526926, 210200193891, 136505794454,
    80462549714, 199900470977, 92293469818, 114080813870, 175372131823, 21011245274,
    161544986624, 144440297843, 58000775995, 193922244320, 90515565891, 130324058245,
    187865042730, 4652173121, 186020227731, 139203004912, 82719293498, 178346322329,
    18623075208, 182790872818, 162729032159, 37170141113, 121798253252, 44310211910,
    248734694633, 227202276776, 37902619969, 23243031445, 158179322729, 331566474482,
    247519462259, 15388995056, 37095147162, 150991982798, 272594076723, 122605939936,
    88255203942, 49385844927, 159187160883, 190056962430, 42668243986, 223304751323,
    122599217480, 66005238776, 34252539725, 179680150821, 241123673670, 48445357565,
    108345420649, 4611821443, 161599381944, 43273285765, 225386601383, 249958530500,
    7864396533, 113961436971, 53573812885, 184277563946, 8354284663, 244856687701,
    205499602518, 29797887380, 81468687943, 77123640077, 84821961754, 145236669602,
    249321204875, 52955550830, 134186926462, 52394714567, 87648959739, 15663907595,
    219010609294, 123186166205, 195825956945, 254207131234, 5207298205, 90739952073,
    103052979465, 186070062156, 51046127848, 245893734231, 58137480908, 229326635412,
    163070414993] ++
  ([108662373545, 105863312004, 97418487520, 32346737639, 232535278503, 189540326656,
    157123757920, 295252470365, 91183959264, 34268245430, 86224718076, 98182284243,
    106709094735, 141432221566, 101077708306, 255184074471, 102425370970, 62190835654,
    22256087269, 1483389883, 100161348309, 92650552372, 91563867464, 190656823269, 30317750950,
    156342522684, 119637996155, 49971959388, 109944910581, 75154550274, 81085540896,
    72154287311, 56944667697, 63422628104, 49855864098, 50843853969, 26228355259, 29144987003,
    76502061122, 8416210709, 32582039541, 34445975281, 76932876904, 35597954273, 16143809206,
    75758271683, 60702876264, 42119664320, 71968046197, 22230768432, 45866926649, 14003861764,
    77741802236, 7756559737, 92649887131, 37519266884, 77585914470, 60042682147, 25260976,
    20162138192, 54491383717, 15941124609, 84790133676, 43544246125, 121006301525,
    159901138206, 19258875328, 167007533715, 137149832304, 19201102393, 176999886875,
    160056205524, 78853420846, 151035260135, 19821991311, 82749274982, 4934422797, 82822781803,
    75865487152, 99273791200, 158629886455, 6760062579, 207880821064, 91868375023,
    130128898507, 135545289548, 2214044411, 118184190383, 100006996852, 107393035382,
    94781256621, 65273452099, 71890101186, 2609083519, 77864522145, 62135331430, 65604149206,
    107519839503, 31791135419, 114839661524, 14163475063, 47355608559, 86210909118,
    26831931492, 112736306825, 21506262609, 41710044466, 7606939579, 41397826309, 31413687308,
    40456851836, 53810790841, 110095428599, 36132235448, 101787996608, 93212414029,
    69959116139, 177541519554, 79728768744, 231382455623, 71609344727, 209492201928,
    15425223961, 207863630001, 56258919630, 217331202266, 19267320961, 122257843565] ++
  ([54223530500, 50141467202, 98235232363, 81377748647, 24566651852, 33333171762, 27338566227,
    12301632713, 67439903202, 102408596952, 50684719142, 26926708425, 17776444318, 88235679144,
    53299910541, 213096957421, 89179590279, 89029877912, 64332925457, 354302846321,
    282508164283, 13435105054, 14540764149, 280548628793, 289487986641, 69228660761,
    26607133983, 206595326519, 268585031945, 118002925511, 49986492541, 161378136285,
    207558006699, 103601377271, 31063196865, 108441909651, 246484020075, 267370101165,
    138337778841, 36360046443, 106741782835, 279595789595, 350724177609, 204176848591,
    9184904889, 48465140959, 276138582943, 353895172689, 178203058113, 30880356183,
    144145930651, 351359201483, 311959152971, 34397023307, 72686057594, 199465155177,
    509050848629, 443987699983, 92695513959, 104185133816, 68704107269, 357425189257,
    389533144843, 167571259831, 47503768265, 222834956671, 461279580507, 442359348879,
    166050452403, 78871858146, 51912170960, 197962228503, 408437790899, 406461351469,
    285382113149, 242283467545, 324016103197, 416520929867, 413279407493, 308759947851,
    168205735181, 60081686783, 1391793814, 55330198430, 121208702446, 161619746938,
    152022943164, 142078871496, 198406884556, 315098668740, 416054309294, 424645873398,
    320335822402, 163876763032, 78238002988, 160186384494, 381736123142, 596823513828,
    658799072616, 526617022408, 276525937586, 49664000926, 16065780925, 141067384856,
    458172914356, 777203401218, 944552270558, 895865077188, 665791134016, 348704277968,
    59828336912, 97946469585, 71691788955, 122525307376, 427423517094, 797958505374,
    1226423345774, 1718044887408, 2246006786238, 2718062798846, 2958121579398, 2702040697388,
    1632408512642, 516918090819, 3793422344055, 7847563002649, 11803749313905, 14217081952167] ++
  ([13131777422091, 6253606234701, 8759576379740, 33917098170038, 70494025613000,
    118697802341798, 177475201511284, 244495269792138, 316310869919032, 388679289098738,
    457003204439332, 516831481626702, 564342199801400, 596730864180168, 612449177150756,
    611274590035208, 594223194575738, 563338957697976, 521400959580498, 471592239786268,
    417172667792946, 361193698430180, 306283307727332, 254515194563476, 207360801496590,
    165710255290826, 129941802850828, 100018775718196, 75596491141118, 56126239420054,
    40947884343770, 29366048674688, 20707545066050, 14359951507774, 9793104060466,
    6566649562950, 4327495424038, 2800979809760, 1779014063262, 1107582729238, 675088748472,
    402284706672, 234011391294, 132662791222, 73157600578, 39158347214, 20290362274,
    10142859334, 4868218338, 2227679168, 960852140, 382691846, 134718054, 36977494, 3267232,
    5496815, 5854965, 4167835, 2522279, 1385633, 710037, 344009, 158755, 70067, 29631, 12017,
    4669, 1733, 605, 193, 51, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0] ++
   [0]))))
end

public section
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi128T5`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi128T5 : (0 : ℕ) = 0 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHi128T4) rfl).right
private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: pCat xs ys
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
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
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
  | n :: ns => Int.ofNat n :: uOfNatHb ns
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
private def bEnc1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k =>
    match Nat.sub z (Nat.add k 1) with
    | 0 => none
    | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match bEnc1 z x with
    | none => none
    | some u =>
      match bEnc z xs with
      | none => none
      | some us => some (uConsNat u us)
private theorem bEnc1_sound (z : ℕ) (x : ℤ) (u : ℕ) (h : bEnc1 z x = some u) :
    ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bEnc1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w => intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem bEnc_sound (z : ℕ) : ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us →
    bDec z us = xs
  | [], _, h => by injection h with h'; subst h'; rfl
  | x :: xs, _, h => by
    dsimp only [bEnc] at h; revert h; cases hx : bEnc1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bEnc z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uConsNat_eq, bDec_cons, bEnc1_sound z x u hx, bEnc_sound z xs ws hxs]
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
      | nil => cases cs with
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
      | cons v vT => cases cs with
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
      | nil => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT => cases cs with
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
    | nil => cases cs with
      | nil => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t bz bz [] [] hl]
      | cons c cT => dsimp only [bSlZ]; rw [bSlZ_pfx z d rem l t (Nat.mul b c) bz [] cT hl]
    | cons v vT => cases cs with
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
private def bSlChkZN (k mL : ℕ) (bns : List ℕ) (vi : List ℤ) (out : List ℕ) : Bool :=
  match bEnc bZ vi with
  | none => false
  | some vns => bSlideChk k mL bns vns out
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
private theorem bSlSndZN {k mL : ℕ} {bns : List ℕ} {vi : List ℤ} {out : List ℕ}
    (h : bSlChkZN k mL bns vi out = true) : pWOk k mL bns vi out := by
  unfold bSlChkZN at h; revert h
  cases hv : bEnc bZ vi with
  | none => intro h; dsimp only at h; cases h
  | some vns =>
    intro h; dsimp only at h; rw [← bEnc_sound bZ vi vns hv]; exact bSlSndNN h
private theorem pChnN {k1 k2 mL : ℕ} {bns : List ℕ} {vi : List ℤ} {vm vo : List ℕ}
    (kS : ℕ) (h1 : pWOk k1 mL bns vi vm) (h2 : bSlideChk k2 mL bns vm vo = true)
    (hk : k1 + k2 = kS) : pWOk kS mL bns vi vo := by
  unfold pWOk at h1 ⊢; rw [← hk, muxFastIterFullT16_add, h1]; exact bSlSndNN h2
private theorem bWalkBridge {k mL : ℕ} {bns : List ℕ} {vZ : List ℤ} {vk : List ℕ}
    {hb vi vo : List ℤ} (hw : pWOk k mL bns vZ vk)
    (hh : muxIntListEq hb (uOfNatHb bns) = true)
    (hi : muxIntListEq vi vZ = true)
    (ho : muxIntListEq (bDec bZ vk) vo = true) :
    muxFastIterFullT16 k mL hb vi = vo := by
  rw [muxIntListEq_eq_true.mp hh, muxIntListEq_eq_true.mp hi,
    ← muxIntListEq_eq_true.mp ho]
  exact hw
private def phbn_0_p0 : List ℕ := [138350194938368,194700523161278,237285280263640,
  272636315191982,303296578458610,330576495005208,355258112345896,377853263725541,398719022623416,
  418116477861344,436243546050456,453254606845529,469272908782994,484398757981447,498715121553444,
  512291579575895,525187184953411,537452579360501,549131589294122,560262450578304,570878762044651,
  581010238315977,590683311209562,599921615450358,608746384833319,617176778258154,625230150261029,
  632922277188123,640267547598849,647279123583935,653969078251754,660348513547392,666427661732623,
  672215973206792,677722192841950,682954426606396,687920199933892,692626509042476,697079866202960,
  701286339792109,705251589831047,708980899599260,712479203823876,715751113868798,718800940285807,
  721632713037546,724250199658485,726656921582983]
private def phbn_0_p1 : List ℕ := [728856168838310,730851013273827,732644320474840,
  734238760490116,735636817485276,736840798419763,737852840832443,738674919809916,739308854201904,
  739756312139589,740018815905182,740097746194231,739994345806105,739709722792530,739244853089010,
  738600582649240,737777629098252,736776582915835,735597908157786,734241942718600,732708898135391,
  730998858928873,729111781473329,727047492383333,724805686400692,722385923760485,719787627010111,
  717010077249876,714052409757706,710913608954007,707592502655283,704087755556844,700397861875488,
  696521137072257,692455708563024,688199505310376,683750246173726,679105426875308,674262305417155,
  669217885757651,663968899524945,658511785507409,652842666617102,646957323969292,640851167657446,
  634519203726226,627955996751591,621155627323052]
private def phbn_0_p2 : List ℕ := [614111643583002,606817005804937,599264022777169,
  591444278489237,583348547278751,574966695165225,566287564545655,557298838714147,547986881739794,
  538336548015988,528330954170924,517951203845971,507176052876303,495981498306808,484340268933271,
  472221186886682,459588357942223,446400130751392,432607738802234,418153498080090,402968368461324,
  386968580292123,370050846243859,352085356679721,332905156570448,312289314330382,289934765938728,
  265405828170050,238034920999875,206700340727165,169219466199900,119970690831538]
private def phbn_0 : List ℕ := pCat phbn_0_p0 (pCat phbn_0_p1 phbn_0_p2)
private def pvn_0_0 : List ℕ := [3000000000000000]
private def pvn_0_o_p0 : List ℕ := [2000000000014294,2000000000115118,2000000000652062,
  2000000002999374,2000000011883097,2000000041878220,2000000133984794,2000000394669599,
  2000001081396374,2000002777879945,2000006731334549,2000015463737148,2000033817317733,
  2000070643466343,2000141379005601,2000271751274548,2000502784517028,2000897114909889,
  2001546339459121,2002578725684920,2004166129239062,2006528482099383,2009933842073271,
  2014691877943200,2021138942934828,2029613657811746,2040423193618547,2053802105292838,
  2069867387377624,2088575065727557,2109684722966067,2132738536130200,2157060464833774,
  2181779150414019,2205875090084089,2228249172908474,2247806290622643,2263545082586318,
  2274643459584719,2280529682373199,2280930470724773,2275890617175900,2265762368444676,
  2251166775828462,2232932660830157,2212021273213651,2189445828482633,2166194846774867]
private def pvn_0_o_p1 : List ℕ := [2143166760306625,2121120974389103,2100647909558972,
  2082157967149113,2065887212523867,2051916091473843,2040196769567243,2030584661307788,
  2022870247822090,2016808169097828,2012141613567613,2008621036861355,2006017095692382,
  2004128312041540,2002784369311246,2001846108157353,2001203281999022,2000771007176456,
  2000485654756658,2000300724875544,2000183052023842,2000109529447551,2000064420312780,
  2000037241859465,2000021160897885,2000011816943626,2000006485077196,2000003497284691,
  2000001853172587,2000000964781868,2000000493430680,2000000247889510,2000000122312850,
  2000000059266662,2000000028197528,2000000013170636,2000000006038447,2000000002716992,
  2000000001199531,2000000000519522,2000000000220677,2000000000091908,2000000000037518,
  2000000000015004,2000000000005873,2000000000002247,2000000000000837,2000000000000301]
private def pvn_0_o_p2 : List ℕ := [2000000000000102,2000000000000032,2000000000000008,
  2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_0_o : List ℕ := pCat pvn_0_o_p0 (pCat pvn_0_o_p1 pvn_0_o_p2)
private def phbn_1_p0 : List ℕ := [104966525019913,148010114581285,180741728146908,
  208087026416729,231959938759573,253344991139355,272828753916857,290794516518663,307509275500101,
  323167981660236,337918221993558,351874977848825,365129942041903,377757664033742,389819751783990,
  401367833006499,412445696514265,423090875399184,433335840375301,443208914688097,452734986194407,
  461936069075385,470831752313722,479439561685440,487775254848453,495853064071961,503685897552302,
  511285507652742,518662632488807,525827115855832,532788009423593,539553660308036,546131786504595,
  552529542183004,558753574464882,564810073007175,570704813477973,576443195822154,582030278062287,
  587470806257169,592769241140188,597929781877744,602956387320433,607852795063938,612622538590176,
  617268962720547,621795237580693,626204371248849]
private def phbn_1_p1 : List ℕ := [630499221236800,634682504932875,638756809119747,
  642724598665581,646588224474855,650349930774721,654011861803708,657576067961762,661044511473840,
  664419071613361,667701549526715,670893672695486,673997099069163,677013420897628,679944168289666,
  682790812521083,685554769113626,688237400703812,690840019718900,693363890875601,695810233515626,
  698180223790868,700474996709835,702695648055904,704843236186996,706918783725472,708923279146226,
  710857678270323,712722905670859,714519855997197,716249395223204,717912361824664,719509567890619,
  721041800173013,722509821078687,723914369607413,725256162239431,726535893775641,727754238133386,
  728911849100547,730009361050455,731047389619957,732026532352797,732947369310321,733810463651367,
  734616362183082,735365595884277,736058680402816]
private def phbn_1_p2 : List ℕ := [736696116528450,737278390642393,737805975144853,
  738279328861669,738698897431088,739065113671698,739378397932413,739639158425400,739847791542734,
  740004682157543,740110203910344,740164719481239,740168580848565,740122129534597,740025696838826,
  739879604059316,739684162702617,739439674682659,739146432509045,738804719465118,738414809776151,
  737976968767999,737491453016508,736958510487965,736378380670852,735751294699142,735077475467352,
  734357137737562,733590488238577,732777725757400,731919041223159,731014617783624,730064630874434,
  729069248281112,728028630193983,726942929256041,725812290603822,724636851901331,723416743367036,
  722152087793951,720843000562784,719489589648145,718091955617775,716650191624740,715164383392522,
  713634609192934,712060939816753,710443438536952]
private def phbn_1_p3 : List ℕ := [708782161064402,707077155495899,705328462254325,
  703536114020786,701700135658477,699820544128083,697897348394427,695930549324119,693920139573871,
  691866103469181,689768416873007,687627047044053,685441952484251,683213082774978,680940378401537,
  678623770565359,676263180983366,673858521673890,671409694728477,668916592068878,666379095188460,
  663797074877206,661170390929434,658498891833257,655782414440782,653020783617907,650213811872543,
  647361298959951,644463031463813,641518782351509,638528310501989,635491360204461,632407660625992,
  629276925245952,626098851255054,622873118916558,619599390886990,616277311493508,612906505964782,
  609486579611974,606017116956121,602497680797841,598927811224952,595307024553142,591634812194390,
  587910639447308,584133944203017,580304135559525]
private def phbn_1_p4 : List ℕ := [576420592336869,572482661484499,568489656371474,
  564440854949066,560335497774243,556172785881228,551951878486948,547671890514534,543331889917266,
  538930894783263,534467870198882,529941724846129,525351307306338,520695402038845,515972724999435,
  511181918858665,506321547774880,501390091670562,496385939953505,491307384615969,486152612635266,
  480919697587822,475606590375372,470211108946156,464730926875247,459163560645929,453506355447463,
  447756469272761,441910855061126,435966240584847,429919105721993,423765656688813,417501796720320,
  411123092582847,404624736171890,398001500285189,391247687454962,384357070461386,377322822814064,
  370137437055079,362792628172556,355279218670358,347587000850743,339704570536278,331619124644812,
  323316212528819,314779427484242,305990019841948]
private def phbn_1_p5 : List ℕ := [296926405820347,287563535625696,277872068135795,
  267817274501911,257357553219169,246442373882303,235009355604615,222979988547215,210253138430577,
  196694744125442,182120564723527,166265209134507,148721167791444,128802183211497,105169739391312,
  74367366248370]
private def phbn_1 : List ℕ := pCat phbn_1_p0 (pCat phbn_1_p1 (pCat phbn_1_p2 (pCat phbn_1_p3
  (pCat phbn_1_p4 phbn_1_p5))))
private def pvn_1_0_p0 : List ℕ := [2000000000014294,2000000000115118,2000000000652062,
  2000000002999374,2000000011883097,2000000041878220,1999999866015206,1999999605330401,
  1999998918603626,1999997222120055,2000006731334549,2000015463737148,2000033817317733,
  2000070643466343,2000141379005601,2000271751274548,2000502784517028,2000897114909889,
  2001546339459121,2002578725684920,2004166129239062,2006528482099383,2009933842073271,
  2014691877943200,2021138942934828,2029613657811746,2040423193618547,2053802105292838,
  2069867387377624,2088575065727557,2109684722966067,2132738536130200,2157060464833774,
  2181779150414019,2205875090084089,2228249172908474,2247806290622643,2263545082586318,
  2274643459584719,2280529682373199,2280930470724773,2275890617175900,2265762368444676,
  2251166775828462,2232932660830157,2212021273213651,2189445828482633,2166194846774867]
private def pvn_1_0_p1 : List ℕ := [2143166760306625,2121120974389103,2100647909558972,
  2082157967149113,2065887212523867,2051916091473843,2040196769567243,2030584661307788,
  2022870247822090,2016808169097828,2012141613567613,2008621036861355,2006017095692382,
  2004128312041540,2002784369311246,2001846108157353,2001203281999022,2000771007176456,
  2000485654756658,2000300724875544,2000183052023842,2000109529447551,2000064420312780,
  2000037241859465,2000021160897885,2000011816943626,2000006485077196,2000003497284691,
  2000001853172587,2000000964781868,2000000493430680,2000000247889510,2000000122312850,
  2000000059266662,2000000028197528,2000000013170636,2000000006038447,2000000002716992,
  2000000001199531,2000000000519522,2000000000220677,2000000000091908,2000000000037518,
  2000000000015004,2000000000005873,2000000000002247,2000000000000837,2000000000000301]
private def pvn_1_0_p2 : List ℕ := [2000000000000102,2000000000000032,2000000000000008,
  2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_1_0 : List ℕ := pCat pvn_1_0_p0 (pCat pvn_1_0_p1 pvn_1_0_p2)
private def pvn_1_1_p0 : List ℕ := [2000001150979056,1999998819380950,1999999665245608,
  2000001051971731,2000000374563793,1999999115410962,1999999328556286,2000000522497483,
  2000000945422626,2000000124025890,1999999169340482,1999999186104470,2000000084528052,
  2000000898233835,2000000864372548,2000000061533556,1999999187444106,1999998906483637,
  1999999384796148,2000000281880186,2000001061310963,2000001327946942,2000000990952074,
  2000000226524013,1999999330892649,1999998572804615,1999998110098883,1999997979479261,
  1999998134589240,1999998500662421,1999999024395550,1999999712796880,2000000666831155,
  2000002122659712,2000004516638764,2000008592463862,2000015571820045,2000027414390439,
  2000047198827196,2000079662241505,2000131940258574,2000214550526872,2000342657146477,
  2000537638898985,2000828957601102,2001256282174569,2001871768314082,2002742324370536]
private def pvn_1_1_p1 : List ℕ := [2003951615746393,2005601480862844,2007812363476806,
  2010722323768233,2014484190735920,2019260476760341,2025215803492229,2032506790904491,
  2041269632286790,2051605898440557,2063567452671387,2077141671716559,2092238407322290,
  2108680239821821,2126197528083283,2144429525472129,2162932408283104,2181194478038701,
  2198658105840979,2214747261567869,2228898802126980,2240595170878566,2249395861413377,
  2254964974330349,2257092462065471,2255707192091848,2250880704261710,2242821406335008,
  2231859839305092,2218426446270049,2203023904319465,2186196463325274,2168498847741700,
  2150467122936875,2132593544627747,2115306862183203,2098958911553318,2083817691252396,
  2070066536353032,2057808544998876,2047075101877481,2037837192982045,2030018204989856,
  2023507024289937,2018170459295083,2013864266286596,2010442327204200,2007763777525489]
private def pvn_1_1_p2 : List ℕ := [2005698092473973,2004128298431447,2002952580384116,
  2002084609139250,2001452922206074,2000999670364035,2000678999247371,2000455281979395,
  2000301363318729,2000196923958260,2000127029285822,2000080891821189,2000050850893764,
  2000031556076600,2000019331008797,2000011689859244,2000006978191935,2000004111975414,
  2000002391810018,2000001373300349,2000000778324451,2000000435416872,2000000240431812,
  2000000131042719,2000000070495258,2000000037430374,2000000019615371,2000000010145356,
  2000000005178765,2000000002608926,2000000001297067,2000000000636376,2000000000308104,
  2000000000147196,2000000000069386,2000000000032267,2000000000014799,2000000000006692,
  2000000000002980,2000000000001304,2000000000000558,2000000000000233,2000000000000092,
  2000000000000034,2000000000000010,2000000000000002,2000000000000000,2000000000000000]
private def pvn_1_1_p3 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_1_1_p4 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_1_1_p5 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_1_1 : List ℕ := pCat pvn_1_1_p0 (pCat pvn_1_1_p1 (pCat pvn_1_1_p2 (pCat pvn_1_1_p3
  (pCat pvn_1_1_p4 pvn_1_1_p5))))
private def pvn_1_2_p0 : List ℕ := [2000000171957126,2000000455630832,2000000790747226,
  2000001003712578,2000000917633653,2000000483490250,1999999853597113,1999999326385869,
  1999999179226032,1999999492501771,2000000085207350,2000000612896987,2000000770852334,
  2000000474907166,1999999907371607,1999999403075890,1999999250014557,1999999526478511,
  2000000066755178,2000000565782345,2000000753402873,2000000536965892,2000000038897860,
  1999999519958021,1999999239347526,1999999328365883,1999999737429091,2000000272642679,
  2000000693839630,2000000822281344,2000000610140779,2000000148158393,1999999617600879,
  1999999213971315,1999999075821673,1999999243656179,1999999657948711,2000000189672955,
  2000000687153831,2000001021364262,2000001116474903,2000000960169850,2000000595575880,
  2000000101387022,1999999568218384,1999999077973466,1999998690283858,1999998437138842]
private def pvn_1_2_p1 : List ℕ := [1999998324555355,1999998338937228,1999998455596870,
  1999998647471757,1999998893006389,1999999183196468,1999999528747050,1999999969156522,
  2000000586384136,2000001526730846,2000003035822554,2000005513276927,2000009595863635,
  2000016280769735,2000027103895273,2000044391730519,2000071608927046,2000113826564974,
  2000178337474841,2000275443665050,2000419435581760,2000629772117085,2000932452590063,
  2001361546312319,2001960811490466,2002785293898835,2003902749273877,2005394685830517,
  2007356780672757,2009898393853811,2013140895238121,2017214541048777,2022253696701646,
  2028390304976663,2035745643908569,2044420601117836,2054484897904238,2065965907749435,
  2078837904795405,2093012720106329,2108332849167868,2124568019794445,2141416080982386,
  2158508808490362,2175422855296578,2191695633242180,2206845438263479,2220394676971790]
private def pvn_1_2_p2 : List ℕ := [2231894671284829,2240950260370921,2247242323760985,
  2250546436804423,2250746138784411,2247839721569062,2241939989172606,2233267037847410,
  2222134697034482,2208931789917126,2194099764577982,2178108475618044,2161431945149693,
  2144525806826201,2127807862403146,2111642797866863,2096331664895907,2082106284661744,
  2069128321298390,2057492438392667,2047232716965292,2038331386743387,2030728899868333,
  2024334442605610,2019036114020458,2014710175574192,2011228967129957,2008467271104797,
  2006307070752512,2004640780064693,2003373116676706,2002421845679502,2001717645419928,
  2001203342687480,2000832741660821,2000569236081133,2000384353905502,2000256343384821,
  2000168872779796,2000109884969505,2000070623951079,2000044832647066,2000028109853030,
  2000017407538108,2000010646897653,2000006431432269,2000003836920130,2000002260681531]
private def pvn_1_2_p3 : List ℕ := [2000001315431682,2000000755892072,2000000428947106,
  2000000240375169,2000000133016772,2000000072684650,2000000039218105,2000000020894200,
  2000000010991254,2000000005708703,2000000002927401,2000000001482064,2000000000740751,
  2000000000365492,2000000000178017,2000000000085581,2000000000040605,2000000000019010,
  2000000000008777,2000000000003991,2000000000001786,2000000000000783,2000000000000336,
  2000000000000138,2000000000000053,2000000000000017,2000000000000003,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_1_2_p4 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_1_2_p5 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_1_2 : List ℕ := pCat pvn_1_2_p0 (pCat pvn_1_2_p1 (pCat pvn_1_2_p2 (pCat pvn_1_2_p3
  (pCat pvn_1_2_p4 pvn_1_2_p5))))
private def pvn_1_o_p0 : List ℕ := [2000000000142163,2000000000751507,2000000002770323,
  2000000008214378,2000000020753400,2000000046071035,2000000091548704,2000000164772379,
  2000000270607694,2000000407185035,2000000561962205,2000000709747887,2000000814704085,
  2000000837516362,2000000747100562,2000000533905898,2000000220037023,1999999861119726,
  1999999536720551,1999999329966244,1999999301558631,1999999466775775,1999999784550250,
  2000000164559034,2000000492185309,2000000664352601,2000000624328823,2000000382869830,
  2000000017189143,1999999646917731,1999999394637621,1999999344484583,1999999513358892,
  1999999844967873,2000000228836483,2000000537590757,2000000669509614,2000000581789559,
  2000000303572601,1999999925047356,1999999567111065,1999999342287919,1999999319849539,
  1999999505919350,1999999843851123,2000000233452845,2000000561965755,2000000736786854]
private def pvn_1_o_p1 : List ℕ := [2000000710342734,2000000490753384,2000000136636181,
  1999999738999247,1999999396340561,1999999190114572,1999999166688903,1999999329415024,
  1999999641398158,2000000036869414,2000000437364972,2000000768443450,2000000973297566,
  2000001020961455,2000000908406487,2000000657231161,2000000306602740,1999999904496163,
  1999999499151125,1999999132187016,1999998834170442,1999998622798722,1999998503369732,
  1999998470914854,1999998513281304,1999998614525949,1999998758172851,1999998930136694,
  1999999121390054,1999999330738311,1999999568375591,1999999861263246,2000000261855226,
  2000000862364851,2000001817709126,2000003381567935,2000005961741165,2000010203239471,
  2000017110324180,2000028221962016,2000045858705977,2000073462515519,2000116053933561,
  2000180832540517,2000277945638726,2000421445384428,2000630444637042,2000930465229734]
private def pvn_1_o_p2 : List ℕ := [2001354948063490,2001946861906338,2002760307585155,
  2003861968365931,2005332209458434,2007265585394742,2009770480947807,2012967598007070,
  2016987016539451,2021963610635610,2028030696320207,2035311927643234,2043911637047741,
  2053904023679376,2065321810581371,2078145193821906,2092292064747489,2107610571364449,
  2123875070608818,2140786392513528,2157977084976032,2175021944273144,2191453688311587,
  2206783138399583,2220522793576165,2232212266506076,2241443756061934,2247885602634162,
  2251302033864763,2251567464318802,2248674141823513,2242732492725613,2233964147955812,
  2222688262138830,2209302299717544,2194258895175677,2178040656049743,2161134846825401,
  2144009772250174,2127094395470463,2110762322515177,2095320813323903,2081004996839364,
  2067977025098188,2056329539587351,2046092568766404,2037242839150819,2029714459410198]
private def pvn_1_o_p3 : List ℕ := [2023410011212000,2018211227621806,2013988631652980,
  2010609716332952,2007945449369507,2005875061898673,2004289220347831,2003091778221265,
  2002200361321618,2001546060467575,2001072497635357,2000734503155359,2000496601429370,
  2000331457780170,2000218395076223,2000142049495764,2000091202356042,2000057800103938,
  2000036157090496,2000022324724711,2000013604775751,2000008182641517,2000004857089380,
  2000002845260284,2000001644801376,2000000938278982,2000000528151333,2000000293340943,
  2000000160751189,2000000086912335,2000000046358779,2000000024393979,2000000012662205,
  2000000006483163,2000000003274075,2000000001630746,2000000000801031,2000000000388009,
  2000000000185321,2000000000087265,2000000000040502,2000000000018525,2000000000008345,
  2000000000003698,2000000000001608,2000000000000682,2000000000000280,2000000000000110]
private def pvn_1_o_p4 : List ℕ := [2000000000000038,2000000000000011,2000000000000002,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_1_o_p5 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_1_o : List ℕ := pCat pvn_1_o_p0 (pCat pvn_1_o_p1 (pCat pvn_1_o_p2 (pCat pvn_1_o_p3
  (pCat pvn_1_o_p4 pvn_1_o_p5))))
private def phbn_2_p0 : List ℕ := [91597413128893,129243125129815,157928319022762,181942429919786,
  202951035980877,221810359533201,239030210688595,254943517524134,269782056776553,283714963933821,
  296870208974954,309347433889929,321226055041356,332570605693565,343434388058692,353862046385498,
  363891427116858,373554953811873,382880663238535,391892999513925,400613432027211,409060942751672,
  417252415218805,425202948400935,432926112516628,440434159393626,447738196896339,454848334658392,
  461773806695943,468523075239566,475103919191427,481523509906746,487788476455341,493904962098270,
  499878673385885,505714923024766,511418667455679,516994539920617,522446879665117,527779757815237,
  532997000381726,538102208772783,543098778138294,547989913820049,552778646142240,557467843742977,
  562060225619463,566558372035775]
private def phbn_2_p1 : List ℕ := [570964734422215,575281644378228,579511321876456,
  583655882753166,587717345559721,591697637840703,595598601896440,599422000080954,603169519680453,
  606842777412396,610443323580731,613972645918976,617432173149471,620823278284076,624147281689010,
  627405453934190,630599018445363,633729153975539,636796996910606,639803643422578,642750151482655,
  645637542745144,648466804312253,651238890388896,653954723835786,656615197628404,659221176228750,
  661773496876184,664272970803150,666720384381080,669116500201331,671462058095629,673757776100124,
  676004351366827,678202461025929,680352763002192,682455896788404,684512484178613,686523129963704,
  688488422591641,690408934794574,692285224184821,694117833821593,695907292750223,697654116515503,
  699358807650649,701021856143289,702643739879798]
private def phbn_2_p2 : List ℕ := [704224925069191,705765866647717,707267008665232,
  708728784654328,710151617983172,711535922192916,712882101320497,714190550207600,715461654796507,
  716695792413488,717893332040399,719054634575059,720180053080978,721269933026964,722324612517102,
  723344422511578,724329687038790,725280723399151,726197842360999,727081348348962,727931539625138,
  728748708463430,729533141317330,730285118981468,731004916747184,731692804552419,732349047126139,
  732973904127564,733567630280407,734130475502343,734662685029915,735164499539065,735636155261474,
  736077884096887,736489913721588,736872467693180,737225765551823,737550022918070,737845451587434,
  738112259621826,738350651437969,738560827892922,738742986366815,738897320842908,739024021985069,
  739123277212773,739195270773710,739240183814100]
private def phbn_2_p3 : List ℕ := [739258194446780,739249477817168,739214206167155,
  739152548897022,739064672625440,738950741247612,738810915991644,738645355473185,738454215748404,
  738237650365360,737995810413816,737728844573555,737436899161236,737120118175843,736778643342783,
  736412614156654,736022167922740,735607439797273,735168562826494,734705667984546,734218884210249,
  733708338442774,733174155656256,732616458893380,732035369297958,731431006146539,730803486879069,
  730152927128630,729479440750286,728783139849052,728064134807019,727322534309649,726558445371258,
  725771973359725,724963222020420,724132293499388,723279288365804,722404305633705,721507442783030,
  720588795779970,719648459096649,718686525730154,717703087220913,716698233670446,715672053758501,
  714624634759578,713556062558851,712466421667514]
private def phbn_2_p4 : List ℕ := [711355795237538,710224265075867,709071911658044,
  707898814141294,706705050377057,705490696922973,704255829054351,703000520775093,701724844828108,
  700428872705202,699112674656457,697776319699094,696419875625840,695043409012781,693646985226716,
  692230668432013,690794521596960,689338606499624,687862983733208,686367712710910,684852851670280,
  683318457677080,681764586628641,680191293256711,678598631129799,676986652655005,675355409079338,
  673704950490510,672035325817205,670346582828820,668638768134668,666911927182634,665166104257284,
  663401342477405,661617683792986,659815168981617,657993837644291,656153728200617,654294877883413,
  652417322732675,650521097588913,648606236085818,646672770642281,644720732453712,642750151482655,
  640761056448697,638753474817617,636727432789787]
private def phbn_2_p5 : List ℕ := [634682955287786,632620065943202,630538787082613,
  628439139712700,626321143504486,624184816776654,622030176477928,619857238168471,617666016000282,
  615456522696541,613228769529876,610982766299500,608718521307195,606436041332076,604135331604105,
  601816395776297,599479235895571,597123852372193,594750243947734,592358407661519,589948338815458,
  587520030937227,585073475741711,582608663090622,580125580950242,577624215347172,575104550322018,
  572566567880911,570010247944764,567435568296149,564842504523695,562231029963876,559601115640061,
  556952730198704,554285839842508,551600408260440,548896396554399,546173763162406,543432463778096,
  540672451266341,537893675574791,535096083641111,532279619295675,529444223159483,526589832537016,
  523716381303754,520823799788051,517912014647051]
private def phbn_2_p6 : List ℕ := [514980948736276,512030520972545,509060646189800,
  506071234987434,503062193570649,500033423582367,496984821926168,493916280579682,490827686397840,
  487718920905330,484589860077558,481440374109344,478270327170567,475079577147854,471867975371375,
  468635366325717,465381587343728,462106468282119,458809831177542,455491489881697,452151249673970,
  448788906849898,445404248283665,441997050962640,438567081491801,435114095565682,431637837405266,
  428138039157003,424614420250861,421066686714013,417494530436434,413897628384297,410275641756670,
  406628215080497,402954975238381,399255530423056,395529469011795,391776358353260,387995743458446,
  384187145586434,380350060714584,376483957881591,372588277390419,368662428856551,364705789085190,
  360717699758948,356697464915192,352644348189467]
private def phbn_2_p7 : List ℕ := [348557569798222,344436303230419,340279671613316,
  336086743712746,331856529522410,327587975389875,323279958618968,318931281478784,314540664538304,
  310106739232293,305628039548190,301102992704587,296529908668855,291906968333543,287232210137249,
  282503514874086,277718588384790,272874941759260,267969868601597,263000418810049,257963368199712,
  252855183137505,247671979156005,242409472250367,237062921220414,231627058969206,226096010069425,
  220463191100990,214721189162101,208861612434373,202874904549672,196750111467187,190474585162248,
  184033601910863,177409863102719,170582831256126,163527829610392,156214793743812,148606495640240,
  140655939754943,132302404948473,123465159020637,114032920001106,103844915408601,92653550249420,
  80040643687399,65188153107306,45977259703842]
private def phbn_2 : List ℕ := pCat phbn_2_p0 (pCat phbn_2_p1 (pCat phbn_2_p2 (pCat phbn_2_p3
  (pCat phbn_2_p4 (pCat phbn_2_p5 (pCat phbn_2_p6 phbn_2_p7))))))
private def pvn_2_0_p0 : List ℕ := [1999999999857837,2000000000751507,1999999997229677,
  1999999991785622,1999999979246600,1999999953928965,1999999908451296,2000000164772379,
  2000000270607694,2000000407185035,2000000561962205,2000000709747887,2000000814704085,
  2000000837516362,1999999252899438,1999999466094102,1999999779962977,1999999861119726,
  1999999536720551,2000000670033756,2000000698441369,2000000533224225,1999999784550250,
  2000000164559034,2000000492185309,2000000664352601,1999999375671177,1999999617130170,
  1999999982810857,1999999646917731,1999999394637621,1999999344484583,1999999513358892,
  2000000155032127,1999999771163517,2000000537590757,2000000669509614,2000000581789559,
  2000000303572601,1999999925047356,1999999567111065,1999999342287919,2000000680150461,
  2000000494080650,2000000156148877,1999999766547155,1999999438034245,1999999263213146]
private def pvn_2_0_p1 : List ℕ := [2000000710342734,1999999509246616,1999999863363819,
  1999999738999247,1999999396340561,1999999190114572,1999999166688903,1999999329415024,
  1999999641398158,2000000036869414,2000000437364972,2000000768443450,1999999026702434,
  1999998979038545,1999999091593513,2000000657231161,1999999693397260,2000000095503837,
  2000000500848875,2000000867812984,2000001165829558,2000001377201278,2000001496630268,
  1999998470914854,1999998513281304,1999998614525949,1999998758172851,2000001069863306,
  2000000878609946,2000000669261689,2000000431624409,2000000138736754,1999999738144774,
  1999999137635149,1999998182290874,2000003381567935,2000005961741165,2000010203239471,
  2000017110324180,2000028221962016,2000045858705977,2000073462515519,2000116053933561,
  2000180832540517,2000277945638726,2000421445384428,2000630444637042,2000930465229734]
private def pvn_2_0_p2 : List ℕ := [2001354948063490,2001946861906338,2002760307585155,
  2003861968365931,2005332209458434,2007265585394742,2009770480947807,2012967598007070,
  2016987016539451,2021963610635610,2028030696320207,2035311927643234,2043911637047741,
  2053904023679376,2065321810581371,2078145193821906,2092292064747489,2107610571364449,
  2123875070608818,2140786392513528,2157977084976032,2175021944273144,2191453688311587,
  2206783138399583,2220522793576165,2232212266506076,2241443756061934,2247885602634162,
  2251302033864763,2251567464318802,2248674141823513,2242732492725613,2233964147955812,
  2222688262138830,2209302299717544,2194258895175677,2178040656049743,2161134846825401,
  2144009772250174,2127094395470463,2110762322515177,2095320813323903,2081004996839364,
  2067977025098188,2056329539587351,2046092568766404,2037242839150819,2029714459410198]
private def pvn_2_0_p3 : List ℕ := [2023410011212000,2018211227621806,2013988631652980,
  2010609716332952,2007945449369507,2005875061898673,2004289220347831,2003091778221265,
  2002200361321618,2001546060467575,2001072497635357,2000734503155359,2000496601429370,
  2000331457780170,2000218395076223,2000142049495764,2000091202356042,2000057800103938,
  2000036157090496,2000022324724711,2000013604775751,2000008182641517,2000004857089380,
  2000002845260284,2000001644801376,2000000938278982,2000000528151333,2000000293340943,
  2000000160751189,2000000086912335,2000000046358779,2000000024393979,2000000012662205,
  2000000006483163,2000000003274075,2000000001630746,2000000000801031,2000000000388009,
  2000000000185321,2000000000087265,2000000000040502,2000000000018525,2000000000008345,
  2000000000003698,2000000000001608,2000000000000682,2000000000000280,2000000000000110]
private def pvn_2_0_p4 : List ℕ := [2000000000000038,2000000000000011,2000000000000002,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_0_p5 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_0 : List ℕ := pCat pvn_2_0_p0 (pCat pvn_2_0_p1 (pCat pvn_2_0_p2 (pCat pvn_2_0_p3
  (pCat pvn_2_0_p4 pvn_2_0_p5))))
private def pvn_2_1_p0 : List ℕ := [1999999987227226,2000000036635461,1999999941407148,
  2000000050951226,1999999939550683,2000000190191391,1999999649627345,2000000292829775,
  1999999916122006,2000000038826533,1999999830694577,2000000370894098,1999999697278585,
  1999999713479927,1999999885136546,2000000570877754,2000000047248279,1999999638497318,
  1999999917721602,2000000441326559,2000000624995937,2000001226383952,2000000370666823,
  2000000330685592,2000000775068840,2000000319021217,1999999969395361,1999998995740332,
  1999999433890850,1999999726646636,2000000558208338,2000000070664255,2000000054257903,
  1999999702128558,2000000881199685,2000000147124867,2000000156954968,2000000770042366,
  1999999978725667,2000000059043156,2000000325984314,2000000233765979,1999999475481261,
  2000000245959392,1999999256180878,1999999868910175,1999999350969454,1999999592149153]
private def pvn_2_1_p1 : List ℕ := [1999999275244822,1999999213482057,2000000381469765,
  2000000520987919,2000001288746702,2000000050811456,1999999865412147,2000000028512775,
  1999999561227801,2000000466237685,1999999726851729,2000000835797435,2000000380582600,
  1999999344183331,1999999516896286,2000001221233811,1999998900228937,1999999832537562,
  1999999890305206,1999999962139988,2000000760947629,1999999669382065,1999999332354228,
  1999999143077241,1999998385952549,1999999355228197,2000000458348551,1999999971073997,
  1999999815033149,2000000146829761,1999999556049847,1999999190344536,2000000110421732,
  2000000515933672,1999999255190038,1999998177188547,1999998980203708,2000000689319466,
  2000001547471810,2000001399680560,2000001150935974,2000001066351392,2000000616542013,
  1999999579623284,1999998558455421,1999998351319526,1999999129894129,2000000326425664]
private def pvn_2_1_p2 : List ℕ := [2000001168544904,2000001239755659,2000000638534219,
  1999999769690473,1999999041390473,1999998684068472,1999998737587266,1999999139158720,
  1999999828426554,2000000825090293,2000002277048336,2000004499627337,2000008030474341,
  2000013720583568,2000022877994233,2000037480069936,2000060472526064,2000096176760323,
  2000150829777825,2000233281583440,2000355871996992,2000535501096262,2000794893583858,
  2001164036154915,2001681737742028,2002397225520217,2003371646223236,2004679295723749,
  2006408354864968,2008660872899703,2011551719734127,2015206233307726,2019756327212585,
  2025334902437593,2032068528657429,2040068522299335,2049420741836248,2060174629634907,
  2072332232188070,2085838100071712,2100571077231026,2116339010145039,2132877321484747,
  2149852191122356,2166868774638474,2183484486030250,2199226912098837,2213615457668505]
private def pvn_2_1_p3 : List ℕ := [2226185396580957,2236512676295979,2244237639240161,
  2249085812563330,2250884090716495,2249570980952347,2245200067439123,2237936424231301,
  2228046308523741,2215881027934144,2201856339021545,2186429052123766,2170072662081588,
  2153253789424516,2136411017353901,2119937379586993,2104167338423285,2089368642429012,
  2075739018683483,2063407277940535,2052438122905797,2042839766696841,2034573392965381,
  2027563511399587,2021708363564462,2016889690151964,2012981356098729,2009856520920809,
  2007393218507947,2005478359660088,2004010284009859,2002900063389399,2002071798405624,
  2001462159365890,2001019408860193,2000702113846275,2000477717084780,2000321097165326,
  2000213207605714,2000139851522734,2000090620708416,2000058007028334,2000036679512788,
  2000022911464117,2000014137243557,2000008616982693,2000005188238792,2000003085704405]
private def pvn_2_1_p4 : List ℕ := [2000001812814586,2000001051990772,2000000603009868,
  2000000341416907,2000000190935907,2000000105469218,2000000057543010,2000000031008519,
  2000000016503789,2000000008675458,2000000004504006,2000000002309372,2000000001169408,
  2000000000584794,2000000000288792,2000000000140831,2000000000067807,2000000000032230,
  2000000000015120,2000000000006994,2000000000003189,2000000000001429,2000000000000626,
  2000000000000265,2000000000000108,2000000000000040,2000000000000013,2000000000000003,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_1_p5 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_1_p6 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_1_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_1_p8 : List ℕ := [2000000000000000]
private def pvn_2_1 : List ℕ := pCat pvn_2_1_p0 (pCat pvn_2_1_p1 (pCat pvn_2_1_p2 (pCat pvn_2_1_p3
  (pCat pvn_2_1_p4 (pCat pvn_2_1_p5 (pCat pvn_2_1_p6 (pCat pvn_2_1_p7 pvn_2_1_p8)))))))
private def pvn_2_2_p0 : List ℕ := [1999999846278907,2000000248734345,1999999662398150,
  2000000295664630,1999999891131467,2000000117620110,1999999709446299,2000000135251193,
  2000000099491475,2000000081158963,1999999804417682,1999999973177235,1999999962069483,
  2000000357277947,1999999939331501,1999999380265063,2000000391480615,2000000083886950,
  2000000336005782,1999999800883101,2000000002811796,1999999380313975,2000000063062910,
  2000000109856113,2000000413318911,2000000272733832,1999999242454288,1999999935527268,
  1999999737525539,2000000318362461,2000000325408311,2000000915375312,1999999540627837,
  2000000491291158,2000001418212136,2000000762405558,2000000836201346,1999999916563096,
  2000000066975105,1999999471136419,1999999490784718,2000000302996770,1999999387787755,
  2000000320357132,1999999520249481,2000000161954311,2000000019031887,2000000333705685]
private def pvn_2_2_p1 : List ℕ := [1999999881885543,2000000953170694,1999999758009963,
  2000000245081734,2000000745843227,1999999679279854,2000000912768119,2000000382949847,
  1999998941029613,2000000267588231,2000000703737920,1999999774030125,1999999634289903,
  1999999405931180,1999999190550705,1999999221880586,1999999043030719,1999999765423262,
  2000000996775588,2000000717528514,1999999826026429,2000000033470098,2000000296940494,
  1999999908077283,1999999994175450,2000000400670515,2000000061326624,1999999710593881,
  2000000319720673,2000000819926173,2000000176134643,1999999386862196,1999999500584082,
  1999999891688849,1999999872468597,2000000003029201,2000000639091191,2000000835393366,
  1999999857530245,1999998633478011,1999998571738387,1999999582542049,2000000276508844,
  1999999879620697,1999999102979491,1999999029626422,1999999762182254,2000000487013740]
private def pvn_2_2_p2 : List ℕ := [2000000543607746,2000000045220614,1999999510299817,
  1999999216619601,1999999071654469,1999998970076740,1999999060722272,1999999590139775,
  2000000546551144,2000001529398569,2000001994210259,2000001646671647,2000000652344208,
  1999999520626224,1999998784700280,1999998714598764,1999999226298388,1999999991912575,
  2000000641563358,2000000931327195,2000000808769886,2000000379866010,1999999824893560,
  1999999315577741,1999998965196787,1999998817811261,1999998865820812,1999999080173105,
  1999999441371586,1999999966621747,2000000735067744,2000001917532685,2000003819736511,
  2000006949663805,2000012121598341,2000020611914366,2000034385107217,2000056412424868,
  2000091109158580,2000144919201132,2000227075642231,2000350562444788,2000533292961544,
  2000799504536112,2001181343293343,2001720578738546,2002470344359535,2003496750073450]
private def pvn_2_2_p3 : List ℕ := [2004880159095624,2006715871840659,2009113921078942,
  2012197665562664,2016100883967296,2020963126477623,2026923183966896,2034110685855693,
  2042636032123176,2052579089533002,2063977316008053,2076814192657726,2091009008621320,
  2106409127945552,2122785843185085,2139834770051628,2157181458068294,2174392497548629,
  2190991924518648,2206482208954487,2220368614907031,2232185304141339,2241521273374013,
  2248044111453104,2251519659300476,2251825950293726,2248960275147860,2243038804324663,
  2234288847804592,2223034464837303,2209676685754721,2194670016562441,2178497126307562,
  2161643651892731,2144574903783248,2127715948921955,2111436129887339,2096038606207188,
  2081755029889569,2068745041553970,2057099933354658,2046849592802017,2037971724806446,
  2030402341031660,2024046588301749,2018789136823716,2014503537134291,2011060155796979]
private def pvn_2_2_p4 : List ℕ := [2008332491754653,2006201841419058,2004560410992681,
  2003313065227839,2002377954009795,2001686276706022,2001181436270122,2000817808567426,
  2000559314948583,2000377944317850,2000252329914556,2000166449229514,2000108484893966,
  2000069860740780,2000044450357208,2000027944535680,2000017357982561,2000010653275363,
  2000006460247787,2000003870772064,2000002291545151,2000001340421414,2000000774704109,
  2000000442395895,2000000249612267,2000000139155053,2000000076649364,2000000041715041,
  2000000022431020,2000000011917218,2000000006255573,2000000003244308,2000000001662395,
  2000000000841587,2000000000420924,2000000000207987,2000000000101522,2000000000048949,
  2000000000023307,2000000000010953,2000000000005078,2000000000002319,2000000000001041,
  2000000000000455,2000000000000193,2000000000000078,2000000000000028,2000000000000008]
private def pvn_2_2_p5 : List ℕ := [2000000000000001,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_2_p6 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_2_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_2_p8 : List ℕ := [2000000000000000]
private def pvn_2_2 : List ℕ := pCat pvn_2_2_p0 (pCat pvn_2_2_p1 (pCat pvn_2_2_p2 (pCat pvn_2_2_p3
  (pCat pvn_2_2_p4 (pCat pvn_2_2_p5 (pCat pvn_2_2_p6 (pCat pvn_2_2_p7 pvn_2_2_p8)))))))
private def pvn_2_3_p0 : List ℕ := [1999999459527755,2000000231071767,1999999915495669,
  2000000126375661,1999999909905921,1999999966894601,1999999878830880,2000000030863395,
  2000000376036741,1999999628824249,2000000346065708,1999999692889387,1999999911107092,
  1999999888517858,2000000437803072,2000000208980929,1999999437991723,2000000192387652,
  1999999663985474,2000000449661778,1999999996440951,2000000140543042,1999999690986076,
  1999999910763466,2000000136890101,1999999348710408,2000000677319886,2000000552907815,
  1999999654368826,2000000217442505,1999999354510686,2000000172886488,1999999224131372,
  2000000470256309,2000000584052529,2000000362051381,1999999272987255,1999999835510776,
  1999999740128045,1999999863628595,2000000678498746,1999999608713363,1999999982667400,
  2000000420300488,1999999485323898,2000000640128778,2000001351482085,2000000423647302]
private def pvn_2_3_p1 : List ℕ := [2000000949882683,2000001018430824,1999999781072331,
  1999999995754408,2000000418098748,1999999595732246,1999999523556477,2000000183904282,
  2000000003860344,1999999544267205,1999999581311740,1999999934077665,2000000431307443,
  2000000421569186,1999999716505505,1999999652931655,2000000543260846,2000000773688531,
  2000000111300494,2000000073226361,2000000603547740,2000000350230100,1999999668957150,
  1999999855265383,2000000534734404,2000000578150665,2000000177849995,1999999958790810,
  1999999596121048,1999998894222788,1999998701560692,1999999457576401,2000000193335072,
  2000000064134277,1999999685904204,1999999948790197,2000000508817608,2000000494318509,
  1999999994803399,1999999802013066,2000000060750421,2000000168399416,1999999933580553,
  1999999936689760,2000000496790220,2000000962296602,2000000527348107,1999999428883255]
private def pvn_2_3_p2 : List ℕ := [1999998797898831,1999999322527074,2000000445670329,
  2000001041214939,2000000651640516,1999999840795693,1999999426546481,1999999613556046,
  1999999943861080,1999999927370857,1999999548945063,1999999174449273,1999999107178706,
  1999999328262062,1999999623385459,1999999852661953,2000000040518885,2000000235092256,
  2000000350689805,2000000196811367,1999999675423259,1999998947608601,1999998397060780,
  1999998399966360,1999999071881445,2000000174344470,2000001239592827,2000001822529375,
  2000001721264293,2000001049178430,2000000143663189,1999999385616991,1999999032853822,
  1999999139928606,1999999578917008,2000000127104524,2000000568606561,2000000766851059,
  2000000689609620,2000000392153638,1999999977580778,1999999554869637,1999999208733999,
  1999998986421797,1999998899475788,1999998934961818,1999999070545472,1999999289794933]
private def pvn_2_3_p3 : List ℕ := [1999999596865642,2000000032401830,2000000694785983,
  2000001772940605,2000003599118715,2000006732907270,2000012091281185,2000021144047350,
  2000036199202984,2000060808070300,2000100324644413,2000162656059579,2000259239651953,
  2000406274624317,2000626220476262,2000949547999533,2001416690272504,2002080090538488,
  2003006182915919,2004277074951005,2005991635435170,2008265636943931,2011230572778085,
  2015030775946372,2019818526039779,2025746947285026,2032960680439143,2041584546520214,
  2051710695419567,2063385020534947,2076593886251349,2091252417768055,2107195702018125,
  2124174210523632,2141854559549297,2159826368291680,2177615482679394,2194703243542903,
  2210550855025356,2224627325350181,2236438982522684,2245558278239189,2251649530797289,
  2254489441340538,2253980635071734,2250157087099481,2243181022999437,2233331652730708]
private def pvn_2_3_p4 : List ℕ := [2220986814929460,2206599196702938,2190669190732890,
  2173716622138930,2156253517288302,2138759819190551,2121663526061818,2105326202811035,
  2090034256699172,2075995841430197,2063342810023410,2052136810887302,2042378429720925,
  2034018220450171,2026968524823021,2021115125832939,2016327983095263,2012470526790143,
  2009407212680885,2007009242248354,2005158514938102,2003749997198943,2002692765201524,
  2001910009575368,2001338288999491,2000926294194907,2000633343902847,2000427787803823,
  2000285444373744,2000188158824570,2000122530173832,2000078828236859,2000050100890946,
  2000031458509945,2000019514782994,2000011959847187,2000007241473451,2000004331819799,
  2000002560108126,2000001494833172,2000000862333562,2000000491481630,2000000276751309,
  2000000153965371,2000000084626743,2000000045956111,2000000024656389,2000000013069688]
private def pvn_2_3_p5 : List ℕ := [2000000006844616,2000000003541433,2000000001810303,
  2000000000914239,2000000000456139,2000000000224828,2000000000109469,2000000000052647,
  2000000000025003,2000000000011720,2000000000005422,2000000000002472,2000000000001106,
  2000000000000483,2000000000000205,2000000000000081,2000000000000029,2000000000000009,
  2000000000000001,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_3_p6 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_3_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_3_p8 : List ℕ := [2000000000000000]
private def pvn_2_3 : List ℕ := pCat pvn_2_3_p0 (pCat pvn_2_3_p1 (pCat pvn_2_3_p2 (pCat pvn_2_3_p3
  (pCat pvn_2_3_p4 (pCat pvn_2_3_p5 (pCat pvn_2_3_p6 (pCat pvn_2_3_p7 pvn_2_3_p8)))))))
private def pvn_2_o_p0 : List ℕ := [1999999475346893,1999999767087060,1999999865763990,
  1999999715872986,2000000353007597,1999999562360408,2000000251806413,2000000170152354,
  1999999859121399,2000000096994835,1999999502707888,2000000505533947,1999999705452896,
  1999999913647224,2000000191433109,2000000147595244,2000000331344872,1999999526302946,
  1999999828679287,2000000239789304,1999999290250675,2000001016023495,1999999844569909,
  1999999974146408,1999999653150662,2000000173967766,1999999957674408,1999999866321446,
  2000000013744481,2000000167569173,2000000637240471,1999999555029453,1999999459219292,
  2000000419419227,1999999625718203,1999999687037190,2000000581313065,2000000077482568,
  2000000303150114,2000000666022434,1999999312367327,1999999070327027,2000000244450723,
  2000000098084269,1999999853901238,2000000621819554,2000000355207876,1999999430159032]
private def pvn_2_o_p1 : List ℕ := [1999999706878621,2000000142232617,1999999801740408,
  1999999862683052,2000000331468854,2000000117340237,1999999606968590,1999999630217267,
  1999999971524839,2000000308214517,2000000563187731,2000000573806826,2000000623271215,
  2000001030691385,2000001096188957,2000000282781398,1999999666501634,2000000174533354,
  2000000729916587,2000000164503673,1999999347796971,1999999503857780,2000000071809665,
  2000000003567835,1999999665752351,1999999853921497,2000000213415180,2000000061669274,
  1999999736756760,1999999896782248,2000000308057790,2000000392277175,2000000295229057,
  2000000436332657,2000000547764785,2000000140017727,1999999576573515,1999999712820920,
  2000000543027187,2000001074711830,2000000694717882,1999999941217773,1999999609722521,
  1999999671717940,1999999567085801,1999999211874773,1999999108861832,1999999497440690]
private def pvn_2_o_p2 : List ℕ := [1999999937732625,1999999957672063,1999999753078599,
  1999999884926224,2000000412251377,2000000713164791,2000000284238408,1999999470892742,
  1999999159701536,1999999779342666,2000000793672512,2000001255588873,2000000769793256,
  1999999827765950,1999999247374095,1999999390575220,1999999941829950,2000000343888049,
  2000000343407891,2000000118901651,1999999980941559,2000000037132162,2000000145700915,
  2000000123423423,1999999939205719,1999999707200025,1999999536707481,1999999427704116,
  1999999316623574,1999999201353625,1999999194597407,1999999435000507,1999999931278656,
  2000000485073468,2000000776459567,2000000563730385,1999999858049526,1999998950048792,
  1999998267682608,1999998153208623,1999998690218062,1999999671311135,2000000710182122,
  2000001426065498,2000001603238034,2000001256747687,2000000591709993,1999999893498464]
private def pvn_2_o_p3 : List ℕ := [1999999407797930,1999999260123518,1999999436483609,
  1999999817551593,2000000240603116,2000000560498727,2000000689593073,2000000609637027,
  2000000360125579,2000000013667696,1999999649527222,1999999333308258,1999999106261332,
  1999998983813795,1999998960664930,1999999019229619,1999999138923350,1999999305173301,
  1999999518668219,1999999807033071,2000000242901744,2000000974510345,2000002277784192,
  2000004642774806,2000008912453740,2000016498323874,2000029704790623,2000052202018625,
  2000089693775440,2000150830534726,2000248416176586,2000400945717186,2000634488140660,
  2000984889500817,2001500215157548,2002243276738454,2003294002924971,2004751321381167,
  2006734134510264,2009380910722638,2012847394562878,2017301982354030,2022918430358121,
  2029865767544925,2038295571090844,2048327111526950,2060031252631729,2073414351924846]
private def pvn_2_o_p4 : List ℕ := [2088403695542253,2104836159824308,2122451772803329,
  2140893621505825,2159715111254536,2178394957643074,2196359538393669,2213011434629854,
  2227762248465530,2240067196948223,2249458637916901,2255575639445898,2258186980613663,
  2257205543399328,2252692858738092,2244853507543453,2234020035654151,2220629905316340,
  2205196676003103,2188278014583125,2170443247343305,2152242992255622,2134182992964836,
  2116703686598205,2100166360261915,2084846071788060,2070930904216950,2058526646749858,
  2047665679730385,2038318695427133,2030407896392784,2023820449450985,2018421197225541,
  2014063899437590,2010600555071283,2007888613370012,2005796095372020,2004204807089493,
  2003011928086236,2002130309621928,2001487823762488,2001026080194143,2000698782473324,
  2000469940465772,2000312099097959,2000204691190024,2000132577659138,2000084803378924]
private def pvn_2_o_p5 : List ℕ := [2000053571537508,2000033422522186,2000020593681210,
  2000012532087069,2000007532028837,2000004470990076,2000002621211841,2000001517785019,
  2000000868021920,2000000490304073,2000000273537139,2000000150724636,2000000082029488,
  2000000044093416,2000000023409657,2000000012275327,2000000006357498,2000000003252011,
  2000000001642956,2000000000819790,2000000000403990,2000000000196612,2000000000094494,
  2000000000044842,2000000000021007,2000000000009709,2000000000004423,2000000000001983,
  2000000000000871,2000000000000371,2000000000000151,2000000000000058,2000000000000020,
  2000000000000005,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_o_p6 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_o_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_2_o_p8 : List ℕ := [2000000000000000]
private def pvn_2_o : List ℕ := pCat pvn_2_o_p0 (pCat pvn_2_o_p1 (pCat pvn_2_o_p2 (pCat pvn_2_o_p3
  (pCat pvn_2_o_p4 (pCat pvn_2_o_p5 (pCat pvn_2_o_p6 (pCat pvn_2_o_p7 pvn_2_o_p8)))))))
private def phbn_3_p0 : List ℕ := [80624422850390,113819724026050,139154644465165,160398482164085,
  179014029099166,195752861285738,211062247610166,225234124040797,238471626245276,250922914587693,
  262700032888800,273890179071561,284562817011308,294774364903832,304571399433687,313992912810186,
  323071944084522,331836784663154,340311886542493,348518558298045,356475506518603,364199262704847,
  371704523947893,379004427780764,386110776126542,393034219423936,399784409266862,406370125906243,
  412799385501957,419079530927089,425217309110160,431218937280411,437090160004953,442836298537750,
  448462293712224,453972743382463,459371935238028,464663875673616,469852315279266,474940771423257,
  479932548323743,484830754942900,489638320986075,494358011246106,498992438497752,503544075117809,
  508015263581871,512408225967990]
private def phbn_3_p1 : List ℕ := [516725072579960,520967809788157,525138347173179,
  529238504046800,533270015415476,537234537443717,541133652467784,544968873604268,548741648992956,
  552453365708943,556105353375060,559698887502284,563235192582837,566715444958046,570140775480766,
  573512271990119,576830981614525,580097912917412,583314037898587,586480293862998,589597585167516,
  592666784855342,595688736186809,598664254074501,601594126429934,604479115428390,607319958697937,
  610117370438117,612872042473360,615584645245725,618255828751201,620886223423472,623476440968693,
  626027075154596,628538702556934,631011883266076,633447161556320,635845066520321,638206112670840,
  640530800511841,642819617080858,645073036464360,647291520287768,649475518181621,651625468225313,
  653741797369706,655824921839840,657875247518889]
private def phbn_3_p2 : List ℕ := [659893170314405,661879076507868,663833343088441,
  665756338071824,667648420804989,669509942257585,671341245300691,673142664973617,674914528739351,
  676657156729253,678370861977544,680055950646107,681712722240090,683341469814762,684942480174065,
  686516034061258,688062406342040,689581866180516,691074677208343,692541097687378,693981380666136,
  695395774130338,696784521147828,698147860008112,699486024356765,700799243324926,702087741654117,
  703351739816576,704591454131307,705807096876036,706998876395240,708166997204427,709311660090816,
  710433062210579,711531397182773,712606855180120,713659623016741,714689884232987,715697819177477,
  716683605086447,717647416160536,718589423639092,719509795872102,720408698389847,721286293970351,
  722142742704728,722978202060495,723792826942935]
private def phbn_3_p3 : List ℕ := [724586769754574,725360180452855,726113206606061,
  726845993447571,727558683928488,728251418768710,728924336506503,729577573546624,730211264207038,
  730825540764301,731420533497632,731996370731731,732553178878388,733091082476920,733610204233475,
  734110665059247,734592584107634,735056078810380,735501264912720,735928256507585,736337166068876,
  736728104483847,737101181084628,737456503678910,737794178579818,738114310635012,738417003255013,
  738702358440811,738970476810753,739221457626740,739455398819761,739672397014774,739872547554966,
  740055944525398,740222680776056,740372847944344,740506536477001,740623835651492,740724833596874,
  740809617314146,740878272696114,740930884546768,740967536600201,740988311539072,740993291012625,
  740982555654290,740956185098859,740914257999263]
private def phbn_3_p4 : List ℕ := [740856852042956,740784043967913,740695909578266,
  740592523759563,740473960493690,740340292873442,740191593116763,740027932580660,739849381774806,
  739656010374824,739447887235286,739225080402407,738987657126461,738735683873916,738469226339303,
  738188349456816,737893117411658,737583593651133,737259840895499,736921921148577,736569895708127,
  736203825176001,735823769468066,735429787823924,735021938816400,734600280360846,734164869724222,
  733715763533997,733253017786843,732776687857151,732286828505354,731783493886080,731266737556114,
  730736612482205,730193171048686,729636465064946,729066545772726,728483463853264,727887269434287,
  727278012096842,726655740881986,726020504297329,725372350323429,724711326420054,724037479532302,
  723350856096584,722651502046481,721939462818465]
private def phbn_3_p5 : List ℕ := [721214783357496,720477508122493,719727681091680,
  718965345767816,718190545183298,717403321905158,716603718039931,715791775238429,714967534700383,
  714131037178990,713282322985350,712421431992789,711548403641089,710663276940602,709766090476279,
  708856882411579,707935690492295,707002552050276,706057504007053,705100582877367,704131824772612,
  703151265404171,702158940086676,701154883741161,700139130898139,699111715700581,698072671906807,
  697022032893293,695959831657393,694886100819965,693800872627921,692704178956690,691596051312590,
  690476520835129,689345618299208,688203374117252,687049818341249,685884980664720,684708890424588,
  683521576602984,682323067828959,681113392380118,679892578184175,678660652820421,677417643521117,
  676163577172799,674898480317509,673622379153934]
private def phbn_3_p6 : List ℕ := [672335299538475,671037266986221,669728306671855,
  668408443430462,667077701758265,665736105813271,664383679415840,663020446049156,661646428859628,
  660261650657196,658866133915549,657459900772264,656042973028845,654615372150683,653177119266920,
  651728235170225,650268740316471,648798654824329,647317998474756,645826790710396,644325050634878,
  642812797012018,641290048264916,639756822474959,638213137380711,636659010376704,635094458512118,
  633519498489353,631934146662492,630338419035643,628732331261174,627115898637825,625489136108697,
  623852058259124,622204679314416,620547013137470,618879073226256,617200872711164,615512424352210,
  613813740536110,612104833273202,610385714194219,608656394546918,606916885192541,605167196602128,
  603407338852655,601637321623014,599857154189807]
private def phbn_3_p7 : List ℕ := [598066845422973,596266403781224,594455837307298,
  592635153623010,590804359924113,588963462974947,587112469102875,585251384192503,583380213679677,
  581498962545240,579607635308559,577706236020796,575794768257930,573873235113507,571941639191133,
  569999982596663,568048266930123,566086493277310,564114662201096,562132773732403,560140827360842,
  558138822025014,556126756102451,554104627399180,552072433138916,550030169951842,547977833862991,
  545915420280192,543842923981568,541760339102586,539667659122616,537564876850999,535451984412598,
  533328973232812,531195834022032,529052556759517,526899130676668,524735544239671,522561785131493,
  520377840233188,518183695604504,515979336463746,513764747166871,511539911185784,509304811085790,
  507059428502182,504803744115914,502537737628321]
private def phbn_3_p8 : List ℕ := [500261387734855,497974672097771,495677567317740,
  493370048904325,491052091245275,488723667574571,486384749939186,484035309164483,481675314818187,
  479304735172869,476923537166877,474531686363615,472129146909117,469715881487809,467291851276392,
  464857015895725,462411333360628,459954760027493,457487250539580,455008757769898,452519232761519,
  450018624665218,447506880674262,444983945956234,442449763581689,439904274449510,437347417208737,
  434779128176718,432199341253332,429607987831089,427004996700859,424390293952969,421763802873409,
  419125443834852,416475134182169,413812788112119,411138316546845,408451627000805,405752623440712,
  403041206138062,400317271513758,397580711974323,394831415739170,392069266658312,389294144019891,
  386505922346838,383704471181912,380889654860322]
private def phbn_3_p9 : List ℕ := [378061332269060,375219356592005,372363575039776,
  369493828563230,366609951549401,363711771498570,360799108681046,357871775772113,354929577463440,
  351972310049117,348999760984297,346011708414228,343007920671263,339988155737186,336952160667926,
  333899670977464,330830409977380,327744088068137,324640401977792,321519033943353,318379650829496,
  315221903178761,312045424186697,308849828594676,305634711492262,302399647020053,299144186962819,
  295867859221549,292570166151547,289250582752143,285908554691666,282543496149204,279154787452179,
  275741772485870,272303755847678,268839999715039,265349720391305,261832084488589,258286204700276,
  254711135108473,251105865962874,247469317857041,243800335215611,240097678990889,236360018449265,
  232585921905908,228773846239617,224922124987030]
private def phbn_3_p10 : List ℕ := [221028954775303,217092379802741,213110274014998,
  209080320547048,204999987903285,200866502223797,196676814825455,192427564000435,188115029786010,
  183735080065399,179283105888109,174753943263491,170141777816029,165440027495371,160641196857945,
  155736694048812,150716598148889,145569359430195,140281407318600,134836628868739,129215661454477,
  123394911988240,117345161498428,111029518852605,104400309947984,97394137055973,89923593831496,
  81862373074087,73015910253369,63055505913412,51337979868017,36196909079770]
private def phbn_3 : List ℕ := pCat phbn_3_p0 (pCat phbn_3_p1 (pCat phbn_3_p2 (pCat phbn_3_p3
  (pCat phbn_3_p4 (pCat phbn_3_p5 (pCat phbn_3_p6 (pCat phbn_3_p7 (pCat phbn_3_p8 (pCat phbn_3_p9
  phbn_3_p10)))))))))
private def pvn_3_0_p0 : List ℕ := [2000000524653107,2000000232912940,1999999865763990,
  2000000284127014,1999999646992403,2000000437639592,2000000251806413,2000000170152354,
  1999999859121399,1999999903005165,1999999502707888,1999999494466053,1999999705452896,
  2000000086352776,2000000191433109,1999999852404756,1999999668655128,1999999526302946,
  1999999828679287,1999999760210696,2000000709749325,1999998983976505,1999999844569909,
  2000000025853592,1999999653150662,1999999826032234,1999999957674408,1999999866321446,
  1999999986255519,2000000167569173,2000000637240471,2000000444970547,1999999459219292,
  2000000419419227,2000000374281797,1999999687037190,1999999418686935,1999999922517432,
  2000000303150114,1999999333977566,1999999312367327,2000000929672973,1999999755549277,
  1999999901915731,2000000146098762,2000000621819554,1999999644792124,2000000569840968]
private def pvn_3_0_p1 : List ℕ := [1999999706878621,2000000142232617,1999999801740408,
  2000000137316948,2000000331468854,1999999882659763,2000000393031410,2000000369782733,
  2000000028475161,2000000308214517,1999999436812269,1999999426193174,1999999376728785,
  1999998969308615,1999998903811043,1999999717218602,1999999666501634,1999999825466646,
  2000000729916587,2000000164503673,1999999347796971,2000000496142220,1999999928190335,
  1999999996432165,2000000334247649,1999999853921497,1999999786584820,1999999938330726,
  2000000263243240,2000000103217752,1999999691942210,1999999607722825,1999999704770943,
  1999999563667343,1999999452235215,2000000140017727,2000000423426485,2000000287179080,
  1999999456972813,2000001074711830,1999999305282118,1999999941217773,1999999609722521,
  1999999671717940,1999999567085801,2000000788125227,2000000891138168,1999999497440690]
private def pvn_3_0_p2 : List ℕ := [2000000062267375,2000000042327937,2000000246921401,
  1999999884926224,2000000412251377,2000000713164791,1999999715761592,2000000529107258,
  2000000840298464,1999999779342666,2000000793672512,2000001255588873,1999999230206744,
  2000000172234050,2000000752625905,2000000609424780,2000000058170050,1999999656111951,
  1999999656592109,2000000118901651,1999999980941559,2000000037132162,2000000145700915,
  1999999876576577,1999999939205719,1999999707200025,1999999536707481,2000000572295884,
  1999999316623574,1999999201353625,1999999194597407,1999999435000507,1999999931278656,
  2000000485073468,2000000776459567,2000000563730385,2000000141950474,2000001049951208,
  2000001732317392,1999998153208623,1999998690218062,2000000328688865,1999999289817878,
  1999998573934502,1999998396761966,1999998743252313,2000000591709993,1999999893498464]
private def pvn_3_0_p3 : List ℕ := [2000000592202070,1999999260123518,1999999436483609,
  2000000182448407,1999999759396884,1999999439501273,1999999310406927,1999999390362973,
  1999999639874421,1999999986332304,2000000350472778,2000000666691742,2000000893738668,
  2000001016186205,2000001039335070,2000000980770381,2000000861076650,2000000694826699,
  2000000481331781,2000000192966929,1999999757098256,1999999025489655,1999997722215808,
  1999995357225194,2000008912453740,1999983501676126,1999970295209377,1999947797981375,
  1999910306224560,1999849169465274,1999751583823414,1999599054282814,1999365511859340,
  1999015110499183,2001500215157548,2002243276738454,2003294002924971,2004751321381167,
  2006734134510264,2009380910722638,2012847394562878,2017301982354030,2022918430358121,
  2029865767544925,2038295571090844,2048327111526950,2060031252631729,2073414351924846]
private def pvn_3_0_p4 : List ℕ := [2088403695542253,2104836159824308,2122451772803329,
  2140893621505825,2159715111254536,2178394957643074,2196359538393669,2213011434629854,
  2227762248465530,2240067196948223,2249458637916901,2255575639445898,2258186980613663,
  2257205543399328,2252692858738092,2244853507543453,2234020035654151,2220629905316340,
  2205196676003103,2188278014583125,2170443247343305,2152242992255622,2134182992964836,
  2116703686598205,2100166360261915,2084846071788060,2070930904216950,2058526646749858,
  2047665679730385,2038318695427133,2030407896392784,2023820449450985,2018421197225541,
  2014063899437590,2010600555071283,2007888613370012,2005796095372020,2004204807089493,
  2003011928086236,2002130309621928,2001487823762488,2001026080194143,2000698782473324,
  2000469940465772,2000312099097959,2000204691190024,2000132577659138,2000084803378924]
private def pvn_3_0_p5 : List ℕ := [2000053571537508,2000033422522186,2000020593681210,
  2000012532087069,2000007532028837,2000004470990076,2000002621211841,2000001517785019,
  2000000868021920,2000000490304073,2000000273537139,2000000150724636,2000000082029488,
  2000000044093416,2000000023409657,2000000012275327,2000000006357498,2000000003252011,
  2000000001642956,2000000000819790,2000000000403990,2000000000196612,2000000000094494,
  2000000000044842,2000000000021007,2000000000009709,2000000000004423,2000000000001983,
  2000000000000871,2000000000000371,2000000000000151,2000000000000058,2000000000000020,
  2000000000000005,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_0_p6 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_0_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_0_p8 : List ℕ := [2000000000000000]
private def pvn_3_0 : List ℕ := pCat pvn_3_0_p0 (pCat pvn_3_0_p1 (pCat pvn_3_0_p2 (pCat pvn_3_0_p3
  (pCat pvn_3_0_p4 (pCat pvn_3_0_p5 (pCat pvn_3_0_p6 (pCat pvn_3_0_p7 pvn_3_0_p8)))))))
private def pvn_3_1_p0 : List ℕ := [1999999892387214,2000000711209875,2000000090170289,
  2000000185177842,2000000176376849,2000000306194389,2000000039068196,1999999815810735,
  1999999984802682,1999999961017841,2000000373399822,1999999855363878,2000000620491865,
  1999999701465450,2000000551146019,2000000201671835,1999999380741286,1999999807449004,
  1999999765111738,1999999264191227,1999999726112487,2000000529072843,2000000012769662,
  1999999975713387,1999999431766765,1999999643391621,2000000130201932,1999999756923911,
  1999999620070636,2000000400369065,1999999580112871,1999999995249609,1999999130397231,
  2000000319654746,2000000160303369,1999999797330459,1999998700371675,2000000342283309,
  2000000514862215,1999999425981051,1999999933789482,2000000417717890,2000000457699683,
  2000000262656713,1999999751374570,2000000503782769,2000000119405636,1999999879577374]
private def pvn_3_1_p1 : List ℕ := [2000000045000191,1999999818694935,1999999551583513,
  1999999909059005,1999999851903280,1999999775866766,1999999813358209,2000000191831495,
  1999999571474437,2000000360931634,2000000617742140,1999999556758855,2000000262292848,
  2000000449868374,1999999710018132,1999999967647897,2000000223154983,1999999929455510,
  1999999724958387,2000000392867881,2000000153892422,2000000572989477,1999999761379308,
  2000000919766605,1999999702918103,2000000420337916,1999999349982982,1999999208696654,
  1999999286108397,1999998594924131,1999999519046220,1999999969444946,1999999975111500,
  1999999190774656,2000000198635480,2000000378787997,1999999529096732,2000000297809805,
  2000000312954071,1999999917764100,1999999787539075,2000000008235852,2000000065586535,
  2000000102708952,1999999842522237,2000000993300144,1999999516140557,1999998948013188]
private def pvn_3_1_p2 : List ℕ := [2000000422603397,1999999810453336,1999998980772777,
  1999999978017303,1999999933570263,1999999771890127,2000000679233118,2000000757676185,
  1999999543857573,1999999738748311,1999999474807212,2000000157228096,1999999548279469,
  1999999793118980,2000000736862319,2000000187060453,1999999820433846,1999999782517133,
  2000000113137192,2000000287702842,2000000735994569,1999999345108973,2000000040814741,
  2000000313949635,2000000464872021,2000000760105491,2000000102818806,2000000102812008,
  2000001233401201,1999999119746759,2000000902972829,2000001243593052,1999999864795303,
  2000000211325436,2000000383931590,2000000003022619,1999999348846446,2000000200782066,
  2000001109982350,1999999682998485,1999998776601919,2000000052722918,2000000937605291,
  2000000330467959,1999999577475804,1999999364128556,1999999955701914,1999999792955797]
private def pvn_3_1_p3 : List ℕ := [1999999915039873,1999997684240345,2000000553342477,
  1999997524800942,2000004745136579,1999995222762786,2000007290444473,1999990749126479,
  2000015416365468,1999975632031741,2000047593984432,1999913551626844,2000142498444082,
  1999784894229992,2000277579717465,1999691721635738,2000267272009496,1999855938440402,
  1999957315638491,2000211765710222,1999742518516437,2000119161581585,2000123462542100,
  1999738397691082,2000133924752156,2000147502238828,1999742076826693,2000029490642706,
  2000244743548344,1999841634323406,1999815544931069,2000226205779863,2000140334613333,
  1999745138200843,1999862148389928,2000261955402046,2000194054317739,1999777977328797,
  1999711140337602,2000097093578086,2000362190695427,2000141500216634,1999723461152675,
  1999607152384362,1999917075635181,2000341392222021,2000497599127127,2000257888715334]
private def pvn_3_1_p4 : List ℕ := [1999779426068378,1999326804396939,1999093115752127,
  1999135057496556,1999410103588434,1999848641669926,2000408838948474,2001098803886123,
  2001975092273813,2003132218832146,2004692831362474,2006801552442907,2009621394050992,
  2013330372354668,2018116285788257,2024168471918175,2031666183793731,2040763891687088,
  2051574352939642,2064150742324161,2078469496750634,2094415762543802,2111773387969567,
  2130221234227734,2149337166671141,2168610451888735,2187462480512195,2205274848036184,
  2221422966156811,2235312660581013,2246416741287830,2254308382081945,2258688350227157,
  2259403667910791,2256456102383213,2249999870311076,2240328981229508,2227855608143397,
  2213081648182649,2196566140818891,2178891403683260,2160630627886266,2142319286809064,
  2124432125604718,2107366801314100,2091434526961009,2076857419106912,2063771719820129]
private def pvn_3_1_p5 : List ℕ := [2052235698928662,2042240853155033,2033724994685123,
  2026585934830568,2020694680057287,2015907325554198,2012075115978079,2009052411208012,
  2006702523447832,2004901567447810,2003540583807321,2002526259466882,2001780587843495,
  2001239794542417,2000852814772060,2000579556180120,2000389124629926,2000258136939907,
  2000169197975032,2000109581808678,2000070128449985,2000044348212311,2000027713871615,
  2000017114731010,2000010444961424,2000006299688774,2000003755069442,2000002212147848,
  2000001288005882,2000000741205862,2000000421586313,2000000237011678,2000000131703434,
  2000000072339689,2000000039274984,2000000021077664,2000000011181567,2000000005863577,
  2000000003039541,2000000001557551,2000000000788982,2000000000395078,2000000000195559,
  2000000000095683,2000000000046269,2000000000022110,2000000000010434,2000000000004862]
private def pvn_3_1_p6 : List ℕ := [2000000000002232,2000000000001004,2000000000000444,
  2000000000000188,2000000000000075,2000000000000028,2000000000000008,2000000000000001,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_1_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_1_p8 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_1_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_1_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_1 : List ℕ := pCat pvn_3_1_p0 (pCat pvn_3_1_p1 (pCat pvn_3_1_p2 (pCat pvn_3_1_p3
  (pCat pvn_3_1_p4 (pCat pvn_3_1_p5 (pCat pvn_3_1_p6 (pCat pvn_3_1_p7 (pCat pvn_3_1_p8 (pCat
  pvn_3_1_p9 pvn_3_1_p10)))))))))
private def pvn_3_2_p0 : List ℕ := [1999999505483852,1999999938717925,2000000174145515,
  2000000224741747,2000000505720620,1999999863936729,2000000502137770,1999999711788488,
  2000000480328360,2000000399439492,1999999857287890,2000000289080598,2000000097124344,
  1999999682017021,1999999747407034,2000000570985635,1999999921058826,1999999732551146,
  2000000207080940,2000000468035563,1999999872733981,2000000661852901,1999999613466810,
  2000000619272958,2000000008729211,1999999824254995,1999999080039703,1999999586860538,
  1999999872255651,1999999987682938,2000000282676314,1999999657524966,1999999716437995,
  2000000680180644,1999999445849906,1999999126125897,1999999919533223,2000000499431472,
  2000000154895584,1999999390805781,1999999265342837,2000000360851207,2000000177200936,
  1999999739225496,1999999516879945,1999999975282730,1999999974714420,1999999448161307]
private def pvn_3_2_p1 : List ℕ := [2000000009451018,1999999738582814,1999999403356174,
  2000000445858952,2000000031094650,1999999927566148,2000000108033710,2000000781746933,
  1999999368482187,2000000737862429,2000000134212208,2000000436370456,1999999579938394,
  1999999914412841,2000000398672061,1999999358928619,2000000048287590,1999999752538500,
  1999999785270611,1999999734937353,1999999782611418,2000000061280242,2000000011961160,
  2000000287899956,1999999708954649,2000000268717759,2000000531497064,1999999885632399,
  1999999733829845,2000000689066384,1999999603523901,1999999699481190,2000000254220432,
  2000000177405486,2000000131940666,1999999661706531,2000000213360946,2000001207196088,
  2000000113299855,2000000206235645,2000000537809632,1999999568014520,1999998513997104,
  2000000076697267,1999999376578172,1999998646320647,1999999831733434,1999999770964229]
private def pvn_3_2_p2 : List ℕ := [1999999614521331,1999999301956003,2000000082974077,
  2000000168255760,2000000295902865,1999999752786419,2000000354690867,1999999539336841,
  1999999618590802,2000000560456478,2000000419218695,1999999457118346,2000000504898123,
  1999999623026909,2000000714715497,2000000123817476,1999998888232909,2000000060207468,
  1999999283146918,1999999429304309,2000000232751862,1999999635585187,2000000383338261,
  2000001039346240,1999999876884739,1999998987713806,1999999883540457,2000000233747727,
  2000000116781148,1999999009454360,2000001305919264,1999998436074799,2000001953853262,
  1999996305097419,2000006941378799,1999990617532046,2000013570332519,1999978311156489,
  2000034572667335,1999946876142484,2000080047936287,1999884134841730,2000161254536191,
  1999795046095088,2000237537277164,1999756363166575,2000209053449343,1999876467985982]
private def pvn_3_2_p3 : List ℕ := [2000006280084227,2000114676348429,1999807329490238,
  2000188976623737,1999907749331818,1999947699336736,2000167310594486,1999821629764273,
  2000067432946366,2000095711752295,1999814221709322,2000120042288040,2000054055344421,
  1999820040632306,2000129575726863,2000059690856039,1999812419242463,2000098649729875,
  2000109579299244,1999814853216298,2000017580406543,2000175544273510,1999875157602380,
  1999890423659296,2000182459431022,2000029935725984,1999804996417853,2000041025950778,
  2000186572172218,1999910498543485,1999828544491940,2000117480747734,2000160244040926,
  1999868338405141,1999835625930253,2000126941333872,2000179078152206,1999893918334692,
  1999794597678898,2000059002831838,2000229401920497,2000018553645662,1999769697503607,
  1999876089698717,2000174981559989,2000224141705369,1999953767449405,1999737290358911]
private def pvn_3_2_p4 : List ℕ := [1999862076810203,2000167552039035,2000278288440301,
  2000065478789428,1999771490977457,1999713886411202,1999950163125547,2000246939041192,
  2000328166044767,2000123882773253,1999804814050744,1999619134723017,1999700399809239,
  1999992416749784,2000313428087187,2000482396126834,2000414870651783,2000143920775534,
  1999778687395919,1999441644013542,1999221109807989,1999154371015577,1999237127170716,
  1999445869796692,1999760637514484,2000181251048399,2000735782302225,2001483266674193,
  2002513399811298,2003945154493755,2005924990687178,2008624300784616,2012235187428341,
  2016963592267991,2023019054319533,2030600846336279,2039880816071173,2050983868872040,
  2063967598165834,2078803028078639,2095358703904903,2113390387155183,2132538342023536,
  2152333635500269,2172214054280948,2191549252039326,2209673699237056,2225925051550393]
private def pvn_3_2_p5 : List ℕ := [2239684816740860,2250417793465440,2257706746066721,
  2261279178748475,2261023834871968,2256995575619131,2249408454484034,2238617952549356,
  2225094334358753,2209389813191390,2192102607796969,2173841009562245,2155190287097440,
  2136684701332229,2118786181304407,2101870421832441,2086220406747436,2072026715061031,
  2059393486285801,2048348630208184,2038856763673256,2030833418338175,2024159250190953,
  2018693248460975,2014284243347077,2010780309737298,2008035928261607,2005916976953386,
  2004303778325093,2003092518407857,2002195393276409,2001539835603888,2001067141147668,
  2000730764630707,2000494496455535,2000330673931723,2000218528564666,2000142727481235,
  2000092133399936,2000058783442577,2000037071404097,2000023109269595,2000014240099948,
  2000008674318935,2000005223584256,2000003109764432,2000001830317064,2000001065071791]
private def pvn_3_2_p6 : List ℕ := [2000000612771318,2000000348576228,2000000196060101,
  2000000109039698,2000000059964665,2000000032608628,2000000017535022,2000000009324521,
  2000000004903462,2000000002550014,2000000001311455,2000000000667020,2000000000335507,
  2000000000166890,2000000000082092,2000000000039931,2000000000019197,2000000000009120,
  2000000000004278,2000000000001977,2000000000000898,2000000000000399,2000000000000172,
  2000000000000069,2000000000000024,2000000000000007,2000000000000001,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_2_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_2_p8 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_2_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_2_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_2 : List ℕ := pCat pvn_3_2_p0 (pCat pvn_3_2_p1 (pCat pvn_3_2_p2 (pCat pvn_3_2_p3
  (pCat pvn_3_2_p4 (pCat pvn_3_2_p5 (pCat pvn_3_2_p6 (pCat pvn_3_2_p7 (pCat pvn_3_2_p8 (pCat
  pvn_3_2_p9 pvn_3_2_p10)))))))))
private def pvn_3_3_p0 : List ℕ := [1999999822765429,1999999456031221,2000000163741770,
  1999999389444502,2000000060822775,2000000258003916,1999999826735851,2000000376040927,
  2000000399020472,2000000227274019,1999999709554312,2000000320137498,2000000272066882,
  2000000276711578,1999999454413523,2000001049476999,2000000084565692,2000000094043372,
  1999999840469262,1999999959161138,2000000052668895,2000000064647585,2000000131506331,
  1999999813742288,1999999643114337,2000000573807590,2000000041150824,1999999947523551,
  2000000284145499,2000000001964955,2000000015743937,2000000948233235,2000000403316259,
  1999999691448903,1999999343818830,1999999667787193,2000000180554692,1999999623765393,
  1999999306032916,1999999779860117,2000000233299955,2000001009831773,1999999310426577,
  1999999390604332,1999999549791031,2000000669856751,1999999326671579,2000000324830806]
private def pvn_3_3_p1 : List ℕ := [1999999858565958,1999999264804472,2000000207541473,
  1999999869301818,2000000122557968,1999999420515129,1999999951044762,2000000320597053,
  1999999475116050,1999999831672640,1999999952936206,1999999914621207,1999999296565689,
  1999999775321131,2000000002156302,2000000005479763,1999999773989366,2000000202751383,
  1999999784510187,2000000239926080,2000000532840776,1999999783133184,2000000339355670,
  2000000739953357,1999999566776518,2000000086593620,2000000152635548,2000000205187105,
  1999999744506408,1999999728879055,1999999756637607,2000000126421080,1999999675580187,
  1999999067516088,2000000852190475,1999999901789153,1999999234483198,2000000129566022,
  2000000887746181,1999999631377101,2000000153083208,2000000307487739,2000000063001885,
  1999999634102987,2000000302650328,2000000162491794,2000000324148370,1999998978979857]
private def pvn_3_3_p2 : List ℕ := [2000000048729396,2000000716648627,1999999463275313,
  2000000885844005,2000000713145364,2000000205244439,2000000763847350,1999999628913620,
  1999999735703922,1999999644181868,1999999168821857,1999999292559402,2000000591387325,
  1999997799877525,2000000808004446,1999996860209470,2000004406503378,1999992905709114,
  2000011088476482,1999982908512676,2000025127900941,1999962172460659,2000056299747904,
  1999919855272299,2000108922382094,1999856948286056,2000178465874478,1999794179518084,
  2000215877159722,1999801301748534,2000150601950064,1999929730641089,1999970650610639,
  2000119774685427,1999825477539051,2000164984995078,1999908576126769,1999979353992919,
  2000124454610120,1999833803552846,2000117797603503,1999998625467157,1999884197656479,
  2000158098215745,1999906390742508,1999961039787978,2000143047346856,1999864718300365]
private def pvn_3_3_p3 : List ℕ := [2000014696804098,2000120068649035,1999853018641495,
  2000037354558384,2000109593022646,1999850780374148,2000032822530841,2000122207125437,
  1999858736536335,1999997533058232,2000144863770398,1999888513644122,1999938030793418,
  2000158872084190,1999955501172377,1999868270261893,2000126478653807,2000062166318242,
  1999839971112072,2000019038795125,2000153174174517,1999914279103092,1999880874113212,
  2000131551180551,2000076259165135,1999843520959969,1999964421284087,2000166357151364,
  2000002862867661,1999832055088070,2000020356058170,2000168216441948,1999967897558579,
  1999830124447496,2000031925586503,2000172700439486,1999978035112289,1999820506276546,
  1999996461390824,2000181595598780,2000040998739658,1999825096107042,1999910997701854,
  2000152473570876,2000144923359620,1999899962786508,1999810463533051,2000016961742574]
private def pvn_3_3_p4 : List ℕ := [2000201784141054,2000086624384320,1999840139506664,
  1999815717081668,2000047638754996,2000219449423642,2000102926120412,1999849736107369,
  1999779602654809,1999978037899484,2000207462368549,2000201964678641,1999968585922861,
  1999762498882849,1999800943433731,2000043436213471,2000249813940871,2000224005876281,
  1999991193822051,1999758252943624,1999722890751736,1999912933195257,2000179485577349,
  2000324371093777,2000245925195899,1999997971618315,1999738651301164,1999622802942570,
  1999714126166649,1999963011863820,2000247197651309,2000439515513890,2000463218063963,
  2000312968852287,2000042109633594,1999731414902828,1999457249983570,1999271173539227,
  1999194499982952,1999224801392166,1999348582790280,1999554844428500,1999846335710182,
  2000247494000393,2000809490219581,2001613288398293,2002771404475778,2004428493095961]
private def pvn_3_3_p5 : List ℕ := [2006760322809848,2009970322112074,2014282778433116,
  2019931957203781,2027146839447546,2036131787978366,2047044158968051,2059970576759442,
  2074904175342420,2091725472035046,2110189588205864,2129922215072628,2150426037246153,
  2171098328384096,2191259232995681,2210188998767022,2227171296730890,2241538925953534,
  2252717773286600,2260264957557271,2263897631645221,2263509875031622,2259176354591157,
  2251142796134360,2239804616362693,2225676154048105,2209353689681721,2191475788530143,
  2172684436684576,2153590011858543,2134742430964656,2116609959650911,2099566274746654,
  2083885546377838,2069744634590795,2057231025618869,2046354881937215,2037063534913902,
  2029256873944247,2022802333099442,2017548493080442,2013336653711137,2010010050317439,
  2007420657929629,2005433734535436,2003930394007448,2002808575028631,2001982794424248]
private def pvn_3_3_p6 : List ℕ := [2001383054877735,2000953231745735,2000649204070737,
  2000436931095527,2000290615025575,2000191038145765,2000124119987119,2000079708532629,
  2000050597662726,2000031749652694,2000019694728204,2000012077648997,2000007322416905,
  2000004389183341,2000002601280422,2000001524337567,2000000883245484,2000000506061362,
  2000000286722021,2000000160645709,2000000089010443,2000000048774135,2000000026431845,
  2000000014166629,2000000007509618,2000000003937237,2000000002041729,2000000001047237,
  2000000000531293,2000000000266605,2000000000132322,2000000000064953,2000000000031530,
  2000000000015130,2000000000007174,2000000000003357,2000000000001549,2000000000000700,
  2000000000000308,2000000000000130,2000000000000051,2000000000000019,2000000000000005,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_3_p7 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_3_p8 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_3_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_3_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_3 : List ℕ := pCat pvn_3_3_p0 (pCat pvn_3_3_p1 (pCat pvn_3_3_p2 (pCat pvn_3_3_p3
  (pCat pvn_3_3_p4 (pCat pvn_3_3_p5 (pCat pvn_3_3_p6 (pCat pvn_3_3_p7 (pCat pvn_3_3_p8 (pCat
  pvn_3_3_p9 pvn_3_3_p10)))))))))
private def pvn_3_4_p0 : List ℕ := [2000000378036264,1999999480178407,1999999687729315,
  2000000221425446,1999999619344998,1999999697014728,1999999614540849,2000000294578529,
  1999999603510030,2000000227507347,1999999413389597,2000000695723753,2000000532694108,
  1999999819017577,1999999943196095,2000000320036018,2000000299742520,2000000182010398,
  1999999664562095,2000000269045651,2000000222654154,2000000136240644,2000000506672550,
  2000000462074784,1999999552037791,1999999986686527,2000000359504779,1999999929500407,
  2000000013300145,2000000125649767,1999999762464786,2000000046755490,1999999503944435,
  2000000801338660,1999999975342281,2000000172475471,1999999287117081,2000000188906707,
  2000000384933026,2000000758534446,2000000893120166,1999999028801786,2000000104060634,
  2000000660501024,1999999928750716,1999999480575784,1999999020650264,1999999864028863]
private def pvn_3_4_p1 : List ℕ := [1999999795117520,2000000188959624,2000000331130869,
  2000000064844503,1999999275520181,1999999779628028,2000000143694502,2000000109302328,
  1999999570019942,1999999762094304,2000000254142684,1999999739113805,1999999454758962,
  2000000388422322,1999999566688994,1999999961792644,2000000027529150,1999999562252769,
  1999999880239407,2000000282996380,2000000044367124,1999999192197545,2000000182248987,
  1999999562329525,1999999849941274,1999999700592606,1999999682314413,1999999944373903,
  2000000452575688,1999999125319887,1999999899211878,2000000755166234,2000000310896165,
  1999999278044670,2000000752205964,2000000637581279,1999999607079000,2000000237279826,
  1999999980711072,2000000617952172,1999999990465205,1999999062577222,2000000801591578,
  1999999532178086,1999999559440967,1999999693121336,2000001140974374,1999997371049306]
private def pvn_3_4_p2 : List ℕ := [2000003145170959,1999994561481943,2000008480204907,
  1999987812557422,2000018778381210,1999971561494367,2000041887737351,1999940847841630,
  2000081574528565,1999891963540314,2000138408396903,1999832243593559,2000189783932361,
  1999801496713146,2000185617698967,1999852785475467,2000082416127886,2000001541052656,
  1999916281904172,2000146305442690,1999836993443137,2000125975550589,1999956494692294,
  1999943499547344,2000133428392382,1999848996090188,2000092258090989,2000011461843942,
  1999889552017666,2000144323769567,1999906077506180,1999983094087518,2000116543358772,
  1999863115262566,2000058516182932,2000063543113615,1999863143913931,2000100530577312,
  2000019198023725,1999876758008614,2000118290910434,1999994442157770,1999886777027927,
  2000124503159306,1999990785230659,1999883853605360,2000118986028449,2000006202889069]
private def pvn_3_4_p3 : List ℕ := [1999873124020230,2000102943098752,2000040793170022,
  1999862049137440,2000067127108486,2000089127150911,1999866945858249,2000002749777310,
  2000132648572832,1999912015559744,1999920857949580,2000134970705182,2000002047834343,
  1999861940918476,2000069291603964,2000106551226828,1999881249276830,1999943280563031,
  2000142281504603,2000003236944447,1999855964740148,2000044245560191,2000131632860335,
  1999918977365908,1999888010512793,2000107405014030,2000091874729590,1999875883092566,
  1999925896676819,2000135025211580,2000063002035332,1999860295908674,1999943216852615,
  2000142759211039,2000059245808511,1999858629715999,1999932738346900,2000138245382463,
  2000083941190801,1999871304318360,1999893440592364,2000110215306194,2000132294399216,
  1999920522838868,1999844366958438,2000034997575174,2000170021869288,2000024175328580]
private def pvn_3_4_p4 : List ℕ := [1999836085368074,1999909015167229,2000127195778925,
  2000149772022080,1999941533839374,1999816312026493,1999960114646069,2000164450642146,
  2000137932088621,1999918001253414,1999807369772007,1999955385147628,2000166226319001,
  2000166482136058,1999955660963878,1999795495653606,1999880217719934,2000108368977490,
  2000214350855518,2000078151433144,1999851607011985,1999780321028573,1999939164550796,
  2000164017710182,2000229383769387,2000072115619120,1999842149287196,1999751535783613,
  1999880625787070,2000116502649908,2000260607957031,2000196298104927,1999975041153430,
  1999765208076854,1999719979689508,1999870513939269,2000114701993066,2000294732506058,
  2000300078856232,2000128658222253,1999877345740024,1999679671994305,1999633865521436,
  1999759845074424,2000000123979739,2000254737312602,2000427125726233,2000459210510609]
private def pvn_3_4_p5 : List ℕ := [2000344474998938,2000119943055416,1999845798337873,
  1999583227597709,1999378324427522,1999255319433854,1999218412355342,1999259284791207,
  1999367010056722,1999537899321678,1999784028254531,2000140176377220,2000669406410044,
  2001467514024331,2002666251200418,2004434780051721,2006978437247501,2010533715986736,
  2015358475529219,2021716783270825,2029858445978351,2039994114516836,2052267731985229,
  2066728895387846,2083308266732920,2101799370175368,2121849860904337,2142964627469046,
  2164521947275494,2185802484728330,2206029390580140,2224416346367135,2240219309620318,
  2252787121382401,2261606133006589,2266334601252606,2266823706903979,2263123515524872,
  2255473815320329,2244281319088807,2230086009155514,2213520290195764,2195265017352273,
  2176006381795561,2156397125032908,2137024728601569,2118388226191876,2100884253169469]
private def pvn_3_4_p6 : List ℕ := [2084802009202744,2070326056610084,2057545364033804,
  2046466746290128,2037030826769437,2029128813945062,2022618680184784,2017339697969912,
  2013124670300673,2009809544472397,2007240391793847,2005277954849533,2003800105790065,
  2002702630565018,2001898767701034,2001317901616058,2000903755051803,2000612356689361,
  2000409989203384,2000271257497509,2000177361178444,2000114611441052,2000073200512992,
  2000046210456042,2000028835581698,2000017786930977,2000010846206257,2000006538515341,
  2000003896942904,2000002296312435,2000001337881599,2000000770728116,2000000439033781,
  2000000247299729,2000000137750578,2000000075879038,2000000041335450,2000000022269443,
  2000000011865730,2000000006253018,2000000003259160,2000000001680167,2000000000856716,
  2000000000432078,2000000000215539,2000000000106346,2000000000051889,2000000000025037]
private def pvn_3_4_p7 : List ℕ := [2000000000011942,2000000000005626,2000000000002614,
  2000000000001193,2000000000000534,2000000000000233,2000000000000097,2000000000000036,
  2000000000000011,2000000000000002,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_4_p8 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_4_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_4_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_4 : List ℕ := pCat pvn_3_4_p0 (pCat pvn_3_4_p1 (pCat pvn_3_4_p2 (pCat pvn_3_4_p3
  (pCat pvn_3_4_p4 (pCat pvn_3_4_p5 (pCat pvn_3_4_p6 (pCat pvn_3_4_p7 (pCat pvn_3_4_p8 (pCat
  pvn_3_4_p9 pvn_3_4_p10)))))))))
private def pvn_3_5_p0 : List ℕ := [2000000378246570,2000000527762263,1999999636383865,
  1999999920482486,1999999370018231,2000000495077073,1999999647404793,1999999965155619,
  1999999845963738,1999999410553521,1999999762024455,2000000404603908,1999999781317330,
  1999999667405754,1999999575063738,2000000027273663,2000000460430398,2000000387637184,
  1999999727002134,2000000047452545,2000000447093534,2000000096203922,1999999866117369,
  2000000786222641,1999999640368625,2000000183591811,1999999500832878,2000000580804096,
  2000000321807525,2000000236180586,2000000306945516,1999999881593116,2000000571456297,
  1999999577128741,1999999925574640,2000000691530240,1999999760021402,2000000256881265,
  1999999845748643,1999999541284823,1999999677007751,2000000648153907,2000000641374950,
  1999999909207227,1999999046492173,1999999753398757,2000000588229082,2000000471501153]
private def pvn_3_5_p1 : List ℕ := [2000000070442196,2000000227244441,2000000029661137,
  2000000538220532,2000000050846246,2000000550588128,2000000455900764,1999998892301051,
  1999999313283505,1999999786691087,2000000214158319,1999999546524772,2000000384771174,
  1999999758955627,1999999751767663,2000000057254146,2000000034786400,1999999311813983,
  2000000331840332,1999999956481030,1999999793066480,1999999756928241,1999999838982994,
  1999999835871735,2000000105901167,2000000191909912,1999998958401391,1999999986015556,
  2000000918775283,1999998721813434,2000000459835223,1999999386969876,2000001645385607,
  1999997197222497,2000003499611072,1999992947162913,2000011435013409,1999982646540233,
  2000023926552276,1999964796313520,2000050551288199,1999929212494494,2000093665145736,
  1999879999378382,2000147162831474,1999829565583845,2000184996758878,1999816320562324]
private def pvn_3_5_p2 : List ℕ := [2000162454548065,1999882958026606,2000051226806096,
  2000026322723881,1999903019953259,2000143775307627,1999849713777409,2000109426153328,
  1999969282481085,1999940160295134,2000126650978470,1999859242903005,2000090935084131,
  2000000550838077,1999907433623449,2000136277089116,1999894701938286,2000013615362284,
  2000086331875035,1999867582931019,2000092700138172,2000009840894112,1999895220579845,
  2000124515658083,1999948630978305,1999939748049404,2000124921722174,1999910716056280,
  1999976560064323,2000116012852486,1999895015306142,1999999153801602,2000107090648395,
  1999889907091261,2000006669901455,2000105303705670,1999890975917257,1999998857325460,
  2000111219097875,1999899269460619,1999976020737649,2000120962493661,1999920654605558,
  1999940964200936,2000125357310801,1999961426843851,1999901695441375,2000109554990608]
private def pvn_3_5_p3 : List ℕ := [2000020571215491,1999874926386320,2000062610593815,
  2000086526260798,1999882802394671,1999981460056158,2000128014652039,1999947895393888,
  1999899079449409,2000104553242420,2000051551366542,1999871694824679,2000005834449908,
  2000126346534769,1999942090453360,1999893924477937,2000096281338920,2000074032674641,
  1999878860120255,1999960444394000,2000132341544536,2000006482413180,1999866151374015,
  2000022373521164,2000129804886387,1999954253139437,1999875864544283,2000062415423386,
  2000118215745743,1999926316467873,1999885667580945,2000079712023476,2000113215467774,
  1999918906657467,1999884491761597,2000077625798665,2000120968517350,1999931159369230,
  1999871410414999,2000054468928020,2000137489339484,1999966888227457,1999855155315050,
  2000004819071166,2000148447929282,2000031968851510,1999858437077875,1999927381930078]
private def pvn_3_5_p4 : List ℕ := [2000121853726761,2000114789921442,1999917681239045,
  1999853717316153,2000026564531110,2000159896115465,2000042979590353,1999857310332917,
  1999887916964925,2000088859467591,2000160433963211,1999997174789975,1999835645344586,
  1999906785809209,2000110783580486,2000164910851142,1999994874739324,1999828455600147,
  1999885170729808,2000091133685618,2000183076269118,2000045649575836,1999848929783101,
  1999831959152340,2000015171277840,2000184367837290,2000145556527805,1999942829291268,
  1999800252169067,1999871806536583,2000080819069328,2000209538191600,2000127021530957,
  1999915754007548,1999781561156077,1999851852096854,2000060872943290,2000218894596587,
  2000186472304698,1999992165950793,1999799511810361,1999765762891775,1999917137637257,
  2000136254973907,2000258910106796,2000196458866935,1999993375686424,1999788016329944]
private def pvn_3_5_p5 : List ℕ := [1999715008303497,1999820043005625,2000038656328578,
  2000242834626374,2000318523805990,2000226082355034,2000013950019548,1999786220499838,
  1999648059702103,1999658718978971,1999811883444406,2000046370311636,2000276433054559,
  2000425489098899,2000449877691633,2000346591565005,2000146410842101,1999898529952632,
  1999653797058408,1999451964467016,1999315470168206,1999249651873534,1999247714851497,
  1999298342401387,1999394220279387,1999540460932335,1999762548663821,2000113748569578,
  2000681879837740,2001595032805869,2003025365815463,2005189726247633,2008345652541021,
  2012781437032813,2018799408965763,2026692410052985,2036714489191721,2049047985224984,
  2063770203516324,2080823620209059,2099993791588263,2120898793653322,2142993050567489,
  2165586917659292,2187881551336835,2209016682272684,2228127195817253,2244403179748386]
private def pvn_3_5_p6 : List ℕ := [2257147520545254,2265825308343030,2270100221516827,
  2269854565773661,2265191514866466,2256420070219629,2244025055259857,2228625861174914,
  2210928513966499,2191675879753972,2171600499226396,2151383751345090,2131623948867483,
  2112814741301163,2095334012307480,2079442443951752,2065290169093715,2052929484855838,
  2042331447575391,2033404270118210,2026011730621093,2019990203664191,2015163369789806,
  2011354088224913,2008393288284362,2006126022719621,2004415022974034,2003142206499307,
  2002208623209292,2001533309506301,2001051462772164,2000712273803888,2000476673241541,
  2000315170608976,2000205897432712,2000132912056950,2000084783794659,2000053446841419,
  2000033297882152,2000020503131502,2000012478301666,2000007506616296,2000004463826156,
  2000002624004982,2000001524879586,2000000876069064,2000000497611781,2000000279453373]
private def pvn_3_5_p7 : List ℕ := [2000000155171015,2000000085194159,2000000046251066,
  2000000024829062,2000000013180715,2000000006919427,2000000003592236,2000000001844304,
  2000000000936445,2000000000470239,2000000000233529,2000000000114691,2000000000055699,
  2000000000026745,2000000000012692,2000000000005949,2000000000002748,2000000000001250,
  2000000000000557,2000000000000240,2000000000000099,2000000000000036,2000000000000011,
  2000000000000002,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_5_p8 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_5_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_5_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_5 : List ℕ := pCat pvn_3_5_p0 (pCat pvn_3_5_p1 (pCat pvn_3_5_p2 (pCat pvn_3_5_p3
  (pCat pvn_3_5_p4 (pCat pvn_3_5_p5 (pCat pvn_3_5_p6 (pCat pvn_3_5_p7 (pCat pvn_3_5_p8 (pCat
  pvn_3_5_p9 pvn_3_5_p10)))))))))
private def pvn_3_o_p0 : List ℕ := [1999999804749307,2000000758952253,1999999939999451,
  2000000692485023,2000000014975360,1999999580080521,1999999801601755,2000000077522540,
  1999999581569949,2000000050394108,2000000229442567,1999999966215532,1999999526371029,
  1999999646148615,1999999673232943,2000000113630135,2000000056343141,2000000360366715,
  1999998758325142,2000000039973546,1999999940807919,2000000162795052,2000000097544446,
  1999999837338500,2000000583862701,1999999809251512,2000000001542487,2000000263669354,
  1999999888596819,2000000924937317,1999999946119857,1999999658065268,2000000093605759,
  2000000207074598,1999999790477727,2000000237404433,2000000371532237,2000000317693552,
  2000000156890420,2000000267743607,2000000031594431,2000000032270274,1999999564962615,
  2000000552552519,2000000854770599,1999999811852743,1999999656323995,1999999014323827]
private def pvn_3_o_p1 : List ℕ := [2000000408079320,2000000615486347,2000000397608474,
  1999999496367836,2000000121568981,1999999771663993,1999999563693138,1999999998740759,
  2000000975682975,1999999807601732,1999999756714185,2000000237746451,2000000163508706,
  2000000649836607,2000000781664628,2000000258274958,1999999705778843,1999999266972711,
  2000000844595764,1999997792425462,2000002294270096,1999996454899229,2000005090593311,
  1999991376778777,2000014352228781,1999977734088810,2000031290353965,1999955565502695,
  2000062069357841,1999916492103920,2000107143270724,1999866512834276,2000157881841415,
  1999825103335585,2000178239093781,1999834610374166,2000132272270169,1999921613331478,
  2000008262841324,2000062864954202,1999880263175407,2000145713083749,1999869678456928,
  2000073539848688,2000008416191480,1999912279205366,2000132458641736,1999876285664077]
private def pvn_3_o_p2 : List ℕ := [2000060369179247,2000030607162540,1999892124406093,
  2000129409326528,1999917302735894,1999989584179026,2000096270126414,1999874724777218,
  2000076777766631,2000021357188480,1999894669002891,2000117107800273,1999954386242560,
  1999941266896021,2000119711056378,1999912846940631,1999986329110118,2000103481688146,
  1999893067521308,2000019472922695,2000085460959030,1999886019230087,2000038228753025,
  2000073248976872,1999883848021118,2000044619292209,2000071680379372,1999884339300287,
  2000038765425245,2000078831219706,1999888336220721,2000022626355198,2000091843137143,
  1999896598658567,1999995433919845,2000109060528715,1999917364075028,1999956104474352,
  2000117284991565,1999955623353785,1999913581817282,2000105683939016,2000013251222351,
  1999884599651003,2000062763670844,2000076618107134,1999890163530746,1999990161466835]
private def pvn_3_o_p3 : List ℕ := [2000117519385741,1999944405898480,1999912859496494,
  2000102888762847,2000035671324796,1999878155162143,2000020327084177,2000112189262556,
  1999929720930209,1999915525148091,2000102934423210,2000043730643154,1999879266943141,
  1999997546082216,2000122129276109,1999964136930081,1999887464074473,2000066980823488,
  2000095342135691,1999908693413592,1999923648600063,2000107417691326,2000057317573274,
  1999883383362399,1999961082830564,2000122581438553,2000024252273167,1999874330220405,
  1999986532968735,2000127094157315,2000006158080884,1999870700340466,1999995226008135,
  2000130307704652,2000007617299953,1999869050225186,1999985069301813,2000130757353210,
  2000026580358563,1999870796357956,1999956895842405,2000123984764351,2000063042512053,
  1999885918713563,1999914214330483,2000097051852983,2000108784799601,1999928529896020]
private def pvn_3_o_p4 : List ℕ := [1999870952483503,2000035975958172,2000141690431155,
  2000008849382497,1999859389641021,1999941006577516,2000120477705906,2000107107561550,
  1999922081896820,1999858555849352,2000016334768489,2000151191412005,2000056489569322,
  1999875410617008,1999879005317256,2000062434001302,2000158121755716,2000027781062546,
  1999856510412343,1999884906127126,2000073714397510,2000164438209650,2000034269391524,
  1999856457498929,1999864783770005,2000048742501657,2000173534542819,2000082088341299,
  1999887834346983,1999828083977832,1999974467198974,2000153040257720,2000155098835786,
  1999978191386263,1999822254637298,1999860608067703,2000051362853740,2000189851519970,
  2000130413338492,1999935222398630,1999803217510572,1999866105401023,2000061872247071,
  2000202113819827,2000154711342163,1999963472373179,1999801082819535,1999810781994104]
private def pvn_3_o_p5 : List ℕ := [1999983789665536,2000173714151472,2000223953742033,
  2000094453197364,1999887377983967,1999761438047004,1999810316061175,1999998090397385,
  2000191935163264,2000259014622343,2000155065553812,1999947503589201,1999766012387715,
  1999719850811479,1999835391586517,2000047297769266,2000241014311723,2000316533345820,
  2000237298354854,2000042132389590,1999820351073436,1999667623883336,1999645402942092,
  1999760418526568,1999968707703407,2000197706206373,2000374436032080,2000448475147697,
  2000403141491271,2000254107016973,2000039013439814,1999803489379168,1999588477829419,
  1999421941352701,1999315912784237,1999268279753544,1999267939943437,1999301948992459,
  1999363692115894,1999461593377006,1999628168990549,1999929208991003,2000472548614603,
  2001415384113002,2002968573060065,2005396025239267,2009007298232786,2014141961989793]
private def pvn_3_o_p6 : List ℕ := [2021145202899630,2030335415809590,2041966003786127,
  2056185022042895,2072997387781465,2092234879792995,2113538897491664,2136359887655902,
  2159975571237996,2183527841683828,2206075791199402,2226660126973728,2244372615738499,
  2258423403523890,2268199223166381,2273306593320210,2273595950361125,2269164948746189,
  2260341570216731,2247649857182371,2231762751141513,2213447494309860,2193509282042159,
  2172738390323027,2151864993560856,2131524536740448,2112235053547980,2094386430647297,
  2078240464707777,2063939739713239,2051522901452171,2040943802841296,2032092176360205,
  2024813873919226,2018929209493658,2014248463191837,2010584091504006,2007759593190875,
  2005615281118001,2004011403466341,2002829153163130,2001970120639111,2001354704310643,
  2000919917401410,2000616937819858,2000408654421830,2000267378048591,2000172814859680]
private def pvn_3_o_p7 : List ℕ := [2000110344801914,2000069609178186,2000043386247060,
  2000026719882519,2000016260678914,2000009778858758,2000005811733537,2000003413602002,
  2000001981665863,2000001137046110,2000000644873736,2000000361524933,2000000200348423,
  2000000109757461,2000000059442645,2000000031826792,2000000016847372,2000000008817167,
  2000000004562421,2000000002334218,2000000001180799,2000000000590617,2000000000292099,
  2000000000142835,2000000000069056,2000000000033003,2000000000015588,2000000000007271,
  2000000000003345,2000000000001514,2000000000000672,2000000000000289,2000000000000118,
  2000000000000044,2000000000000014,2000000000000003,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_o_p8 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_o_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_o_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_3_o : List ℕ := pCat pvn_3_o_p0 (pCat pvn_3_o_p1 (pCat pvn_3_o_p2 (pCat pvn_3_o_p3
  (pCat pvn_3_o_p4 (pCat pvn_3_o_p5 (pCat pvn_3_o_p6 (pCat pvn_3_o_p7 (pCat pvn_3_o_p8 (pCat
  pvn_3_o_p9 pvn_3_o_p10)))))))))
private def phbn_4_p0 : List ℕ := [76614018292616,108182302690187,132292045183811,152522484831973,
  170262317810632,186224884076723,200834600849619,214368425807171,227019028878486,238926905428775,
  250198278865481,260915798814583,271145291087388,280940207055474,290344664192855,299395587648211,
  308124257960851,316557454685671,324718317919301,332627008433497,340301221167351,347756590056525,
  355007011069303,362064902799939,368941418779371,375646622016308,382189629677728,388578733931012,
  394821503584387,400924870132185,406895201036744,412738362490078,418459773446589,424064452368219,
  429557057850103,434941924079633,440223091911151,445404336202157,450489189947315,455480965657856,
  460382774361773,465197542541193,469928027274670,474576829812018,479146407775884,483639086156482,
  488057067242488,492402439611550]
private def phbn_4_p1 : List ℕ := [496677186287193,500883192154914,505022250718214,
  509096070265164,513106279507284,517054432745044,520942014607764,524770444410107,528541080162499,
  532255222268568,535914116939020,539518959348166,543070896556466,546571030220009,550020419105662,
  553420081428700,556770997028032,560074109392653,563330327551597,566540527838495,569705555540803,
  572826226442780,575903328270525,578937622046556,581929843360792,584880703564190,587790890890699,
  590661071512778,593491890535204,596283972931564,599037924427416,601754332333807,604433766334521,
  607076779230170,609683907642000,612255672678045,614792580564082,617295123241629,619763778935082,
  622199012689925,624601276883784,626971011712016,629308645649342,631614595888979,633889268760595,
  636133060128326,638346355770000,640529531738673]
private def phbn_4_p2 : List ℕ := [642682954707440,644806982298494,646901963397286,
  648968238452616,651006139763412,653015991752922,654998111230984,656952807645007,658880383320250,
  660781133689961,662655347515882,664503307099624,666325288485364,668121561654300,669892390711265,
  671638034063890,673358744594683,675054769826346,676726352080670,678373728631309,679997131850707,
  681596789351465,683172924122395,684725754659503,686255495092142,687762355304528,689246541052856,
  690708254078180,692147692215269,693565049497591,694960516258611,696334279229541,697686521633713,
  699017423277700,700327160639331,701615906952724,702883832290455,704131103642996,705357884995511,
  706564337402130,707750619057803,708916885367813,710063289015063,711189980025207,712297105829711,
  713384811326930,714453238941269,715502528680507]
private def phbn_4_p3 : List ℕ := [716532818191347,717544242813263,718536935630702,
  719511027523708,720466647217018,721403921327694,722322974411332,723223929006914,724106905680337,
  724972023066670,725819397911195,726649145109251,727461377744944,728256207128753,729033742834064,
  729794092732683,730537363029345,731263658295268,731973081500769,732665734046991,733341715796747,
  734001125104533,734644058845718,735270612444951,735880879903803,736474953827664,737052925451935,
  737614884667511,738160920045607,738691118861919,739205567120164,739704349574998,740187549754345,
  740655249981149,741107531394569,741544473970620,741966156542306,742372656819222,742764051406673,
  743140415824306,743501824524269,743848350908923,744180067348105,744497045195964,744799354807375,
  745087065553951,745360245839658,745618963116040]
private def phbn_4_p4 : List ℕ := [745863283897079,746093273773680,746308997427811,
  746510518646288,746697900334231,746871204528190,747030492408947,747175824314017,747307259749833,
  747424857403645,747528675155129,747618770087709,747695198499612,747758015914650,747807277092744,
  747843036040191,747865346019681,747874259560075,747869828465941,747852103826860,747821136026502,
  747776974751486,747719669000017,747649267090316,747565816668836,747469364718282,747359957565427,
  747237640888737,747102459725800,746954458480575,746793680930455,746620170233145,746433968933377,
  746235118969439,746023661679544,745799637808025,745563087511380,745314050364141,745052565364594,
  744778670940350,744492404953751,744193804707139,743882906947968,743559747873783,743224363137044,
  742876787849822,742517056588346,742145203397426]
private def phbn_4_p5 : List ℕ := [741761261794732,741365264774944,740957244813777,
  740537233871870,740105263398551,739661364335481,739205567120164,738737901689348,738258397482292,
  737767083443923,737263988027869,736749139199377,736222564438116,735684290740858,735134344624056,
  734572752126299,733999538810657,733414729766920,732818349613716,732210422500529,731590972109597,
  730960021657712,730317593897904,729663711121015,728998395157172,728321667377150,727633548693624,
  726934059562316,726223219983042,725501049500638,724767567205793,724022791735765,723266741274999,
  722499433555629,721720885857880,720931115010355,720130137390226,719317968923300,718494625083994,
  717660120895187,716814470927966,715957689301270,715089789681409,714210785281479,713320688860668,
  712419512723436,711507268718594,710583968238259]
private def phbn_4_p6 : List ℕ := [709649622216693,708704241129027,707747834989867,
  706780413351771,705801985303617,704812559468833,703812144003517,702800746594419,701778374456801,
  700745034332163,699700732485839,698645474704463,697579266293288,696502112073379,695414016378660,
  694314983052815,693205015446050,692084116411702,690952288302703,689809532967883,688655851748124,
  687491245472351,686315714453357,685129258483474,683931876830060,682723568230823,681504330888967,
  680274162468152,679033060087280,677781020315082,676518039164519,675244112086982,673959233966293,
  672663399112498,671356601255444,670038833538151,668710088509943,667370358119373,666019633706891,
  664657905997294,663285165091910,661901400460546,660506600933164,659100754691298,657683849259191,
  656255871494657,654816807579646,653366643010520]
private def phbn_4_p7 : List ℕ := [651905362588011,650432950406878,648949389845225,
  647454663553500,645948753443133,644431640674836,642903305646526,641363727980882,639812886512499,
  638250759274662,636677323485686,635092555534851,633496430967878,631888924471965,630270009860350,
  628639660056390,626997847077135,625344542016400,623679715027284,622003335304149,620315371064029,
  618615789527435,616904556898566,615181638344874,613446997975976,611700598821895,609942402810585,
  608172370744743,606390462277847,604596635889430,602790848859530,600973057242299,599143215838742,
  597301278168549,595447196440976,593580921524759,591702402917008,589811588711039,587908425563118,
  585992858658055,584064831673618,582124286743704,580171164420232,578205403633694,576226941652312,
  574235714039744,572231654611280,570214695388454]
private def phbn_4_p8 : List ℕ := [568184766552020,566141796393205,564085711263182,
  562016435520663,559933891477554,557837999342562,555728677162679,553605840762442,551469403680862,
  549319277105921,547155369806524,544977588061784,542785835587512,540580013459784,538360020035447,
  536125750869400,533877098628513,531613953002003,529336200608095,527043724896786,524736406048500,
  522414120868447,520076742676436,517724141191929,515356182414070,512972728496426,510573637616160,
  508158763837326,505727956967970,503281062410695,500817921006315,498338368870219,495842237221026,
  493329352201083,490799534688326,488252600099018,485688358180785,483106612795404,480507161690691,
  477889796260830,475254301294428,472600454709516,469928027274670,467236782315354,464526475404529,
  461796854036485,459047657282784,456278615429096]
private def phbn_4_p9 : List ℕ := [453489449591632,450679871311760,447849582127266,
  444998273118620,442125624428433,439231304752162,436314970797935,433376266713195,430414823475636,
  427430258245691,424422173677575,421390157185602,418333780162194,415252597143637,412146144919283,
  409013941579441,405855485496736,402670254235193,399457703380680,396217265285694,392948347720716,
  389650332423510,386322573536798,382964395923634,379575093348622,376153926511693,372700120919603,
  369212864578507,365691305488922,362134548922010,358541654453451,354911632728049,351243441924611,
  347535983886529,343788099878640,339998565925353,336166087678482,332289294755536,328366734480224,
  324396864946267,320378047313011,316308537226370,312186475240706,308009876095839,303776616677528,
  299484422458524,295130852179285,290713280480951]
private def phbn_4_p10 : List ℕ := [286228878146103,281674589532139,277047106694237,
  272342839584795,267557881577367,262687969386706,257728436230508,252674156786541,247519482118269,
  242258162241086,236883253334786,231387005711023,225760727422722,219994616715336,214077554156134,
  207996841911979,201737872768268,195283704272233,188614502493048,181706803031688,174532510082965,
  167057510289052,159239703095777,151026116084965,142348525130037,133116506912851,123205803139876,
  112437431135591,100536556343706,87040314913658,71045791335652,50220912674478]
private def phbn_4 : List ℕ := pCat phbn_4_p0 (pCat phbn_4_p1 (pCat phbn_4_p2 (pCat phbn_4_p3
  (pCat phbn_4_p4 (pCat phbn_4_p5 (pCat phbn_4_p6 (pCat phbn_4_p7 (pCat phbn_4_p8 (pCat phbn_4_p9
  phbn_4_p10)))))))))
private def pvn_4_0_p0 : List ℕ := [1999999804749307,2000000758952253,2000000060000549,
  1999999307514977,1999999985024640,2000000419919479,1999999801601755,1999999922477460,
  1999999581569949,1999999949605892,1999999770557433,2000000033784468,2000000473628971,
  2000000353851385,1999999673232943,1999999886369865,2000000056343141,1999999639633285,
  1999998758325142,2000000039973546,1999999940807919,1999999837204948,2000000097544446,
  1999999837338500,1999999416137299,2000000190748488,1999999998457513,1999999736330646,
  1999999888596819,2000000924937317,2000000053880143,2000000341934732,1999999906394241,
  1999999792925402,1999999790477727,2000000237404433,1999999628467763,1999999682306448,
  2000000156890420,1999999732256393,2000000031594431,1999999967729726,1999999564962615,
  2000000552552519,1999999145229401,2000000188147257,1999999656323995,1999999014323827]
private def pvn_4_0_p1 : List ℕ := [2000000408079320,1999999384513653,1999999602391526,
  1999999496367836,2000000121568981,1999999771663993,2000000436306862,1999999998740759,
  2000000975682975,1999999807601732,2000000243285815,2000000237746451,2000000163508706,
  2000000649836607,1999999218335372,2000000258274958,1999999705778843,2000000733027289,
  1999999155404236,1999997792425462,1999997705729904,1999996454899229,2000005090593311,
  1999991376778777,2000014352228781,1999977734088810,2000031290353965,1999955565502695,
  2000062069357841,1999916492103920,2000107143270724,1999866512834276,2000157881841415,
  1999825103335585,2000178239093781,1999834610374166,2000132272270169,1999921613331478,
  1999991737158676,2000062864954202,1999880263175407,2000145713083749,1999869678456928,
  2000073539848688,2000008416191480,1999912279205366,2000132458641736,1999876285664077]
private def pvn_4_0_p2 : List ℕ := [2000060369179247,2000030607162540,1999892124406093,
  2000129409326528,1999917302735894,2000010415820974,2000096270126414,1999874724777218,
  2000076777766631,2000021357188480,1999894669002891,2000117107800273,1999954386242560,
  1999941266896021,2000119711056378,1999912846940631,1999986329110118,2000103481688146,
  1999893067521308,2000019472922695,2000085460959030,1999886019230087,2000038228753025,
  2000073248976872,1999883848021118,2000044619292209,2000071680379372,1999884339300287,
  2000038765425245,2000078831219706,1999888336220721,1999977373644802,2000091843137143,
  1999896598658567,2000004566080155,2000109060528715,1999917364075028,1999956104474352,
  2000117284991565,1999955623353785,1999913581817282,2000105683939016,2000013251222351,
  1999884599651003,2000062763670844,2000076618107134,1999890163530746,1999990161466835]
private def pvn_4_0_p3 : List ℕ := [2000117519385741,1999944405898480,1999912859496494,
  2000102888762847,2000035671324796,1999878155162143,2000020327084177,2000112189262556,
  1999929720930209,1999915525148091,2000102934423210,2000043730643154,1999879266943141,
  1999997546082216,2000122129276109,1999964136930081,1999887464074473,1999933019176512,
  1999904657864309,1999908693413592,1999923648600063,1999892582308674,1999942682426726,
  1999883383362399,1999961082830564,1999877418561447,1999975747726833,1999874330220405,
  1999986532968735,1999872905842685,1999993841919116,1999870700340466,1999995226008135,
  1999869692295348,1999992382700047,1999869050225186,1999985069301813,1999869242646790,
  1999973419641437,1999870796357956,1999956895842405,1999876015235649,1999936957487947,
  1999885918713563,1999914214330483,1999902948147017,1999891215200399,1999928529896020]
private def pvn_4_0_p4 : List ℕ := [1999870952483503,1999964024041828,1999858309568845,
  1999991150617503,1999859389641021,1999941006577516,1999879522294094,1999892892438450,
  1999922081896820,1999858555849352,1999983665231511,1999848808587995,1999943510430678,
  1999875410617008,1999879005317256,1999937565998698,1999841878244284,1999972218937454,
  1999856510412343,1999884906127126,1999926285602490,1999835561790350,1999965730608476,
  1999856457498929,1999864783770005,1999951257498343,1999826465457181,1999917911658701,
  1999887834346983,1999828083977832,1999974467198974,1999846959742280,1999844901164214,
  1999978191386263,1999822254637298,1999860608067703,1999948637146260,1999810148480030,
  1999869586661508,1999935222398630,2000196782489428,2000133894598977,2000061872247071,
  2000202113819827,2000154711342163,2000036527626821,2000198917180465,2000189218005896]
private def pvn_4_0_p5 : List ℕ := [2000016210334464,2000173714151472,2000223953742033,
  2000094453197364,2000112622016033,2000238561952996,2000189683938825,2000001909602615,
  2000191935163264,2000259014622343,2000155065553812,2000052496410799,2000233987612285,
  2000280149188521,2000164608413483,2000047297769266,2000241014311723,2000316533345820,
  2000237298354854,2000042132389590,2000179648926564,2000332376116664,2000354597057908,
  2000239581473432,2000031292296593,2000197706206373,2000374436032080,2000448475147697,
  2000403141491271,2000254107016973,2000039013439814,2000196510620832,2000411522170581,
  2000578058647299,2000684087215763,2000731720246456,2000732060056563,2000698051007541,
  2000636307884106,2000538406622994,2000371831009451,2000070791008997,2000472548614603,
  2001415384113002,2002968573060065,2005396025239267,2009007298232786,2014141961989793]
private def pvn_4_0_p6 : List ℕ := [2021145202899630,2030335415809590,2041966003786127,
  2056185022042895,2072997387781465,2092234879792995,2113538897491664,2136359887655902,
  2159975571237996,2183527841683828,2206075791199402,2226660126973728,2244372615738499,
  2258423403523890,2268199223166381,2273306593320210,2273595950361125,2269164948746189,
  2260341570216731,2247649857182371,2231762751141513,2213447494309860,2193509282042159,
  2172738390323027,2151864993560856,2131524536740448,2112235053547980,2094386430647297,
  2078240464707777,2063939739713239,2051522901452171,2040943802841296,2032092176360205,
  2024813873919226,2018929209493658,2014248463191837,2010584091504006,2007759593190875,
  2005615281118001,2004011403466341,2002829153163130,2001970120639111,2001354704310643,
  2000919917401410,2000616937819858,2000408654421830,2000267378048591,2000172814859680]
private def pvn_4_0_p7 : List ℕ := [2000110344801914,2000069609178186,2000043386247060,
  2000026719882519,1999983739321086,1999990221141242,1999994188266463,1999996586397998,
  1999998018334137,1999998862953890,1999999355126264,1999999638475067,1999999799651577,
  1999999890242539,1999999940557355,1999999968173208,1999999983152628,1999999991182833,
  2000000004562421,2000000002334218,2000000001180799,2000000000590617,2000000000292099,
  2000000000142835,2000000000069056,2000000000033003,2000000000015588,2000000000007271,
  2000000000003345,2000000000001514,2000000000000672,2000000000000289,2000000000000118,
  1999999999999956,1999999999999986,1999999999999997,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_0_p8 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_0_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_0_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_0 : List ℕ := pCat pvn_4_0_p0 (pCat pvn_4_0_p1 (pCat pvn_4_0_p2 (pCat pvn_4_0_p3
  (pCat pvn_4_0_p4 (pCat pvn_4_0_p5 (pCat pvn_4_0_p6 (pCat pvn_4_0_p7 (pCat pvn_4_0_p8 (pCat
  pvn_4_0_p9 pvn_4_0_p10)))))))))
private def pvn_4_1_p0 : List ℕ := [1999999516205403,1999999944655186,2000000629446340,
  2000000645909857,1999999575763513,1999999774028898,1999999760886586,2000000146049783,
  2000000181018245,1999999981715387,1999999765842999,2000000086437365,1999999704180084,
  1999999704575422,1999999389470064,2000000584262206,2000000428133347,1999999710068008,
  1999999988995587,2000000642822896,1999999846210454,1999999832834298,1999999515692953,
  1999999617509970,1999999021540671,2000000241757156,2000000062296267,1999999663002033,
  1999999668563630,2000000156296076,1999999872854538,1999999656361053,1999999976095181,
  1999999624925165,1999999762831529,2000000929123300,1999999832264842,2000000677092202,
  1999999919368191,1999999731642569,2000000774360339,1999999228464025,2000000186237404,
  1999999876757838,1999999801989417,1999999614058026,2000000487319406,1999999382545951]
private def pvn_4_1_p1 : List ℕ := [2000000088396580,1999999802885220,2000000204448874,
  2000000143431330,1999999144575547,2000000374453305,1999999308345784,2000000100928327,
  1999999500228322,1999999262798792,2000000990009922,1999996670781535,2000005137604156,
  1999989622865748,2000016908474275,1999974690360131,2000037594709083,1999947809361984,
  2000070679248173,1999907585255451,2000118930241085,1999857146917700,2000162468262402,
  1999825581494695,2000170705679686,1999855227796671,2000101756918831,1999960023778184,
  1999965820239447,2000094225025819,1999862256739480,2000138992534852,1999898546479092,
  2000029708518902,2000047551142348,1999892770461609,2000128922898759,1999899805748462,
  2000021532758386,2000071755593856,1999874794500797,2000112373819642,1999949141568994,
  1999961834365432,2000111768083563,1999891445894893,2000039371022692,2000046614560322]
private def pvn_4_1_p2 : List ℕ := [1999881925042035,2000094897895209,1999983153255827,
  1999914366560739,2000119575406879,1999939849216859,1999951842681632,2000110497745301,
  1999916171082164,1999994019903635,2000095710593986,1999893348898656,2000010885600694,
  2000087024135494,1999899084395322,2000030719356020,2000086783000887,1999893418943942,
  2000035946981441,2000071837523081,1999909297614919,2000003553458982,2000099330291049,
  1999900647910063,1999990911880293,2000108962775936,1999916897832170,1999961059251502,
  2000112712328707,1999950615319806,1999930392164983,2000099832929971,1999989124131800,
  1999912890085351,2000083095788477,2000025334205764,1999883382374805,2000046007725795,
  2000101049933245,1999910605587241,1999961150459201,2000098370396202,1999950916754494,
  1999896151667469,2000081637089636,2000046029197473,1999888297494552,2000009118459056]
private def pvn_4_1_p3 : List ℕ := [2000110043121708,1999938315045489,1999921285907906,
  2000092157461109,2000046424781145,1999881294655631,2000003156277281,2000118811918578,
  1999952359680995,1999887948968664,2000123708867912,1999999433710794,1999970615730594,
  1999928386789215,2000115095888796,1999960857855161,2000015254598188,1999913382895930,
  2000089874521403,1999970052816774,2000057407954386,1999904932832748,2000036466711488,
  1999950721932320,2000085222646053,1999980457174848,2000057500773992,1999943836890149,
  1999991484112595,1999912810459304,1999942077783053,1999910624956931,1999910014742997,
  1999928704526200,1999886749382743,1999954839520671,1999868006837663,1999977300396653,
  1999863339268827,1999980412749352,1999886650549345,1999949662631453,1999938666087399,
  1999900488128897,1999982668965973,1999876224764302,1999987200805472,1999886735508701]
private def pvn_4_1_p4 : List ℕ := [1999956325859835,1999931891141614,1999886022819256,
  1999985836277693,1999859410374102,1999953903049083,1999899843701820,1999894971562644,
  1999955672338861,1999837944558930,1999951567579197,1999886600449536,1999870523164698,
  1999973299680592,1999867543909274,1999952964699065,1999935936298915,1999847525223844,
  1999963132192175,1999862432875142,1999877433245081,1999980144613139,1999859651651139,
  1999920463882506,1999939478306959,1999798456489496,1999995662997432,1999880000065594,
  1999866300765738,1999924050033634,1999907551681566,1999884730053967,1999869438514408,
  1999925785675265,1999914849660939,1999829721376285,1999915813939708,1999980376085536,
  1999770071388760,1999858160356036,2000030742407043,1999827014717154,1999819426175675,
  1999908551913414,1999939743658964,1999845949678629,1999975991727890,1999883245985233]
private def pvn_4_1_p5 : List ℕ := [1999726961406143,1999787845883923,1999987847575065,
  1999901068433174,1999959760269319,2000104318278012,2000182875661475,2000025563131896,
  2000093427400434,2000226781518164,2000152862379952,2000056420151384,2000051240630383,
  2000274893572855,2000176157351961,2000048423095485,2000122385429938,2000246769426646,
  2000179158614670,2000104178054059,2000036074450487,2000217925688507,2000314752192685,
  2000115738947028,2000044139976898,2000167482051475,2000283809053013,2000254372453804,
  2000202947085702,2000027057164426,2000151647013500,2000265948291785,2000383157237714,
  2000302140109119,2000044483089396,2000069102600291,2000248808197690,2000332270269759,
  2000415818948756,2000426371010816,2000236829978953,2000066396842753,2000138804430528,
  2000321099269161,2000397911616705,2000401493930783,2000496244374356,2000709031460170]
private def pvn_4_1_p6 : List ℕ := [2000895072621793,2000903179212813,2000704257330463,
  2000385049683377,2000073857574121,1999887924621472,1999931368990277,2000323898498695,
  2001232122012090,2002887808460895,2005589704417393,2009690737663578,2015573024583174,
  2023612728929545,2034137216337213,2047378147642358,2063425530534976,2082188676091859,
  2103370079352265,2126457305051099,2150736078904211,2175325217694173,2199231170937191,
  2221417251841194,2240880545959349,2256728343129933,2268245921340081,2274948608880007,
  2276613069372637,2273285360710922,2265266099057678,2253075629027094,2237404039149447,
  2219052227917541,2198870042534364,2177698576090049,2156318287742929,2135414454202557,
  2115541744648730,2097132624401808,2080455869740678,2065697896843410,2052866181343999,
  2041961925522823,2032833332493606,2025336926036272,2019298717127439,2014490178109881]
private def pvn_4_1_p7 : List ℕ := [2010734435387467,2007858582487620,2005672049121865,
  2004032889352314,2002837880446141,2001978244540445,2001355607513374,2000909611944947,
  2000604600701246,2000404773965288,2000272090856625,2000177967251740,2000108387030145,
  2000058771146333,2000026757656640,2000008812983893,2000000451049849,1999997557498233,
  1999997220006045,1999997782644851,1999998481653079,1999999046626170,1999999431467562,
  1999999670828558,1999999813472509,1999999897436341,1999999946448472,1999999974208749,
  1999999988967959,1999999996089015,1999999999087573,2000000000109926,2000000000321736,
  2000000000271734,2000000000176419,2000000000100867,2000000000053426,2000000000026915,
  2000000000013099,2000000000006204,2000000000002854,2000000000001264,2000000000000532,
  2000000000000211,2000000000000076,2000000000000024,2000000000000006,2000000000000001]
private def pvn_4_1_p8 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_1_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_1_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_1 : List ℕ := pCat pvn_4_1_p0 (pCat pvn_4_1_p1 (pCat pvn_4_1_p2 (pCat pvn_4_1_p3
  (pCat pvn_4_1_p4 (pCat pvn_4_1_p5 (pCat pvn_4_1_p6 (pCat pvn_4_1_p7 (pCat pvn_4_1_p8 (pCat
  pvn_4_1_p9 pvn_4_1_p10)))))))))
private def pvn_4_2_p0 : List ℕ := [1999999733846375,1999999662520126,1999999412537883,
  2000000374241010,2000000565319851,2000000476269074,2000000089439049,1999999957443641,
  1999999475050060,2000000045213445,1999999882548854,2000000308605394,1999999923815620,
  1999999770865904,2000000133987711,2000000549541924,1999999249763840,1999999470405774,
  1999999725777128,2000000501677983,1999999708739583,1999999962321105,2000000289889887,
  2000000105309568,2000000008897471,2000000407568443,2000000381242538,1999999642858764,
  1999998984999903,2000000197509616,1999999238685253,1999999833492957,2000000250488819,
  1999999033109852,2000000493655277,1999999535253579,2000000117301341,2000000002398112,
  1999999779974738,1999999022615283,2000000401346001,1999999907742909,1999999938457696,
  2000000672504143,1999999815683199,2000000652063078,1999999723283037,2000000085167708]
private def pvn_4_2_p1 : List ℕ := [2000001183786368,1999997306944669,2000004584987300,
  1999991417869036,2000014537849982,1999976767240495,2000034365398276,1999950097541650,
  2000068412930529,1999909896769253,2000114079657734,1999861480346324,2000159005541593,
  1999829384268729,2000166575032031,1999856145246928,2000099287952076,1999961568032245,
  1999968964381821,2000093171184271,1999865569211606,2000136049614182,1999901798084619,
  2000028891374037,2000050493508641,1999889148388115,2000125655193879,1999912043732608,
  2000014549303312,2000068889693389,1999879878217865,2000112025289523,1999952043677526,
  1999956812798046,2000112240887590,1999893294769163,2000034750806979,2000055030078236,
  1999891236400632,2000088886466892,1999986059221425,1999919628410557,2000113877980717,
  1999940757287140,1999957122364699,2000106154342369,1999911725051822,1999996842258557]
private def pvn_4_2_p2 : List ℕ := [2000098391237105,1999896113820119,2000012932507927,
  2000079778952795,1999899950140258,2000027578915171,2000078553711584,1999890366467250,
  2000047801204600,2000054007988885,1999899678624733,2000019092340746,2000075539548692,
  1999903509925582,2000006503308921,2000085806353334,1999904897018443,1999991041281946,
  2000106237538624,1999925375169709,1999958513687024,2000105779848331,1999950738497441,
  1999923698563690,2000100647092104,2000002393530465,1999906090355868,2000074310764160,
  2000051545086348,1999903115988486,2000025247442028,2000084331772573,1999920838308793,
  1999970163830461,2000105358906404,1999965191588138,1999909659264543,2000084930395555,
  2000056183567600,1999884207440360,2000002730914637,2000099927586577,1999956379574376,
  1999923786343512,2000102268688419,2000003009568776,1999923712113303,1999952316104443]
private def pvn_4_2_p3 : List ℕ := [2000182467192532,1999889742872797,1999973271981067,
  2000044111051235,2000093701367397,1999815807966576,2000056996168009,2000022229996612,
  2000026165776348,1999863404388956,2000093381282977,2000000942992988,2000013494966558,
  1999910894067324,2000068903961266,2000006583926398,2000002847030203,1999948676033243,
  2000015009742873,2000040370056381,1999984669556758,1999999485007128,1999945445166584,
  2000067608978338,1999970778832930,2000055679696167,1999926049441821,2000021128354229,
  1999986181968104,2000019937446875,2000045298274801,1999948235226414,2000036818822805,
  1999918805625147,2000034311221850,1999988656239696,2000021211736008,2000057158340680,
  1999972172484558,2000059548042827,1999930262629890,1999988210413525,1999952479854707,
  1999888268570751,1999981847185528,1999866600297967,1999941282064278,1999920566182768]
private def pvn_4_2_p4 : List ℕ := [1999881170680356,1999972396964744,1999866995522119,
  1999942056069061,1999956210184113,1999864166402061,1999985523612958,1999911244618943,
  1999911315547650,1999983284847997,1999882740955815,1999943487261609,1999982987611320,
  1999837500881525,2000019566979553,1999886532248274,1999898623441523,1999975765059418,
  1999873171823971,1999929760208841,1999936433866207,1999873725852774,1999901194055480,
  1999916852309374,1999882458575637,1999905184832008,1999929755372431,1999959244329207,
  1999899625713181,1999832127959801,2000010332654842,1999859810673446,1999858896664042,
  1999975423459853,1999941160991660,1999789942729236,1999957644362703,1999969220142122,
  1999834052734650,1999842053625693,2000023964267256,1999871298866697,1999836736733165,
  1999929170026765,1999914141336303,1999863734777848,1999911447553932,1999965467198885]
private def pvn_4_2_p5 : List ℕ := [1999772957142386,1999885206142966,1999990535250676,
  1999927298223420,1999785166400621,1999836239140759,1999936408718530,1999918071856141,
  1999831564157395,1999983389106800,1999988469589855,1999748349003540,1999758997330432,
  1999858490482602,1999917039896079,1999849954253974,1999892865103280,1999995396453707,
  2000204035020421,2000054673188681,1999988341024300,2000161444283366,2000202171163668,
  2000137831603980,2000028049536464,2000087442973257,2000253709647453,2000208089100802,
  2000099554832350,2000085227394646,2000102008139717,2000210661610093,2000284716931390,
  2000123600307562,1999985125835371,2000130252199258,2000311101499982,2000276800687599,
  2000152625279771,2000090347290536,2000088482789345,2000166229739739,2000316215188327,
  2000375855295372,2000230035224770,2000035139067908,2000033017803232,2000225129145273]
private def pvn_4_2_p6 : List ℕ := [2000392058475925,2000388387476190,2000285557504018,
  2000226663070844,2000243299020169,2000257345606201,2000212989301321,2000155473321289,
  2000182518953193,2000344394292035,2000596225904006,2000830729960212,2000946675954636,
  2000897250151581,2000696460490941,2000397107350256,2000066043208347,1999774295129236,
  1999605248186104,1999674491166081,2000151469883851,2001275943623593,2003362025468701,
  2006791719207499,2011987524899535,2019384115544091,2029365182445135,2042236065430864,
  2058125473050288,2077005093364508,2098562449513383,2122309949987473,2147458770665236,
  2173093148681876,2198126143351608,2221424502712318,2241919419702743,2258614454454588,
  2270749320610328,2277812044382552,2279548948573797,2276040203917908,2267627409334003,
  2254865364929571,2238520270981033,2219462915264768,2198583278463299,2176775781870408]
private def pvn_4_2_p7 : List ℕ := [2154871495996866,2133563513422230,2113410763713008,
  2094846349965945,2078148572766991,2063443829420790,2050753682048012,2040023700372172,
  2031124203126170,2023866714605970,2018042836313125,2013450806021638,2009896395086425,
  2007189604349345,2005154073056766,2003641210853241,2002534348736887,2001741419440904,
  2001185669904084,2000801857420848,2000537419130789,2000353984457580,2000226182026061,
  2000138068596728,2000079189167199,2000041816976645,2000019681203146,2000007667768668,
  2000001852433356,1999999483794857,1999998819079172,1999998869041419,1999999137954725,
  1999999414546645,1999999630775258,1999999779796554,1999999874920623,1999999932296042,
  1999999965215174,1999999983169854,1999999992431575,1999999996910537,1999999998912951,
  1999999999719837,1999999999996521,2000000000062986,2000000000059602,2000000000040915]
private def pvn_4_2_p8 : List ℕ := [2000000000024361,2000000000013304,2000000000006831,
  2000000000003339,2000000000001565,2000000000000703,2000000000000300,2000000000000119,
  2000000000000042,2000000000000013,2000000000000003,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_2_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_2_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_2 : List ℕ := pCat pvn_4_2_p0 (pCat pvn_4_2_p1 (pCat pvn_4_2_p2 (pCat pvn_4_2_p3
  (pCat pvn_4_2_p4 (pCat pvn_4_2_p5 (pCat pvn_4_2_p6 (pCat pvn_4_2_p7 (pCat pvn_4_2_p8 (pCat
  pvn_4_2_p9 pvn_4_2_p10)))))))))
private def pvn_4_3_p0 : List ℕ := [1999999794084386,2000000132939275,1999999595523177,
  1999999487225495,1999999487346400,2000000240798530,2000000067281941,2000000640516580,
  2000000400483826,2000000288455203,1999999939372674,2000000015801371,1999999266358174,
  2000000245705781,2000000158442160,2000000088596908,1999999484534635,1999999926257692,
  2000000638985936,2000000313354902,1999999513578259,1999999712933297,1999999635557668,
  2000000197802074,1999999322463274,1999999999056377,2000000811040781,1999998972197985,
  2000000468633831,1999999950015059,2000000375969891,2000000427478490,2000000432284398,
  1999999414891065,1999999930068158,1999999819486925,1999999018895583,2000000335257340,
  1999999883595252,1999998576481584,2000002031214927,1999995071275155,2000009090075896,
  1999984861378030,2000023788461608,1999963386738438,2000052466160100,1999926564878972]
private def pvn_4_3_p1 : List ℕ := [2000096057192147,1999879372909312,2000144130126161,
  1999838442983607,2000168183415359,1999842613846375,2000126932237752,1999925437393343,
  2000008131565409,2000060094544041,1999886215067820,2000137259634126,1999879489937335,
  2000064841846514,2000012549725704,1999914453716098,2000123677658003,1999890283290083,
  2000046788983527,2000037595842153,1999895687987836,2000119936458135,1999925381702959,
  1999989481068691,2000087438151043,1999887103358689,2000069489724027,2000018899287078,
  1999902573120053,2000106644541354,1999958408560415,1999946226445314,2000107903786668,
  1999919281730182,1999991614713031,2000087649353598,1999901219762470,2000032691399058,
  2000067340383995,1999888344188482,2000054785334787,2000049473517970,1999897285778425,
  2000056593939755,2000048662023753,1999886721229955,2000079558032834,2000028059668085]
private def pvn_4_3_p2 : List ℕ := [1999900067468403,2000058388326516,2000037276207461,
  1999908098973110,2000047815886078,2000048479640705,1999898433866886,2000034952441927,
  2000073635975387,1999902831324418,2000009687644946,2000090959356340,1999915341845931,
  1999973780159157,2000099195592757,1999943752823798,1999944890712002,2000106408358132,
  1999987283959837,1999905309881924,2000074122821692,2000036319490443,1999897932269173,
  2000025806862275,2000079460168243,1999911722071144,1999968827500318,2000092142008753,
  1999976908730687,1999916710986778,2000087628301388,2000020551333241,1999917360563930,
  1999987938882078,2000132033649652,1999872535559947,2000004968845671,2000031964651703,
  2000092741735187,1999837081769018,2000073691850994,2000049997732543,2000008441794238,
  1999856493799031,2000162834467759,1999971057829612,1999937287039399,1999978153717810]
private def pvn_4_3_p3 : List ℕ := [2000154437908473,1999897581934593,1999948635810139,
  2000051127339224,2000064206331595,1999922605273319,1999977893399406,2000090484484249,
  1999970111953035,1999965844039280,1999951408381028,2000111374508309,1999950749716020,
  2000008414966845,1999968163484573,2000064197200259,1999997989342349,1999933094215560,
  2000023944171560,1999965959816391,2000066565871308,1999923773534273,2000002505844361,
  2000009200419952,1999998884020414,2000044647490393,1999923583501767,2000035376782464,
  1999981736764826,2000026231885567,2000026156139746,1999933198974804,2000040158930991,
  1999959169897523,2000032754248265,2000038815711722,1999946573403475,2000034036401970,
  1999952190202710,2000000307533800,2000048961564722,1999966740304667,2000060813483053,
  1999968564441094,1999961433302544,2000028184366004,1999945345394915,2000000292771915]
private def pvn_4_3_p4 : List ℕ := [2000077382601830,1999939147227048,2000102710526886,
  1999982543815632,1999979895319560,2000047716593376,1999895404959801,1999977472500323,
  1999962303917798,1999879175281127,1999949242949052,1999926370874829,1999885303482482,
  1999941922103257,1999918639380702,1999892392095593,1999959298977293,1999888500260441,
  1999962749914023,1999889964902582,1999964142435211,1999929601585514,1999895552365303,
  1999955096001850,1999987258696864,1999841657956376,1999962818253673,1999984606516390,
  1999875197564356,1999869651916094,2000027270625344,1999916713989548,1999823262067746,
  1999996482334563,1999899306487356,1999825639462250,1999895902807619,2000025161315445,
  1999853929518087,1999865058840833,1999987543909589,1999913150133242,1999842514984379,
  1999950265667647,1999918729966413,1999872777764945,1999928880590715,1999929314301895]
private def pvn_4_3_p5 : List ℕ := [1999899488499298,1999810073801702,1999981045782142,
  1999982637261865,1999824914256391,1999796564966646,2000016777544037,1999931076780776,
  1999832695743322,1999901657128408,1999896312255631,1999912156563249,1999848922606269,
  1999892889275736,2000020937275473,1999878997942096,1999738786827797,1999840037804668,
  1999970253266438,1999962690587344,1999850660388271,1999869889089416,1999997387272572,
  1999904394133021,1999718359562407,1999765220520139,1999886698974614,1999894449393710,
  1999893966748843,1999919917351364,1999974445520268,2000112553141417,2000184729940952,
  2000055860754500,1999964817400858,2000113804142209,2000267890569044,2000192576145598,
  2000047628215932,2000053226042112,2000160328278662,2000226874256117,2000216847439656,
  2000145720437520,2000054079675895,2000047641941810,2000181686082030,2000321846397929]
private def pvn_4_3_p6 : List ℕ := [2000281837273428,2000091542700810,1999983826453590,
  2000095356898036,2000296934022430,2000367985467022,2000258600557144,2000114031521948,
  2000079539048191,2000154386998951,2000236331614883,2000262627166476,2000256832233363,
  2000279434188654,2000325421421625,2000351815732917,2000291081778730,2000179277329094,
  2000064351495787,2000063982177687,2000184493201096,2000421991448039,2000680594247923,
  2000876379510918,2000962029059931,2000894608293336,2000708318786296,2000418596580931,
  2000058693247803,1999691488525331,1999365480933213,1999204029150367,1999393575311835,
  2000178264929685,2001923655820349,2005061500374900,2010058565558972,2017421072589907,
  2027595448269042,2040899578854835,2057502905200308,2077340256344549,2100060830903364,
  2125059766720756,2151484907534346,2178256953742859,2204174172080866,2228017592808254]
private def pvn_4_3_p7 : List ℕ := [2248618563780344,2264956628280967,2276268768903552,
  2282095026883998,2282282357458901,2276995930499464,2266706837278669,2252123231749793,
  2234104688426310,2213599486629448,2191586025298619,2168997476360533,2146654094546649,
  2125232009844121,2105258521424821,2087108590781226,2071001016965851,2057010575447183,
  2045099684589401,2035154069897797,2027007938259200,2020459511240108,2015286202322270,
  2011263390894346,2008182025332571,2005858682852247,2004136943928590,2002884130755806,
  2001988121003727,2001356118845975,2000914426484210,2000607482485974,2000395375226549,
  2000250280672061,2000152830239759,2000089207322164,2000049238850776,2000025316399396,
  2000011815235440,2000004725288870,2000001335931603,1999999928298816,1999999487632811,
  1999999460795973,1999999573263860,1999999704729674,1999999812454905,1999999888324448]
private def pvn_4_3_p8 : List ℕ := [1999999937041281,1999999966258439,1999999982803689,
  1999999991689015,1999999996215615,1999999998396637,1999999999383628,1999999999797472,
  1999999999953820,2000000000003482,2000000000013634,2000000000011728,2000000000007704,
  2000000000004443,2000000000002358,2000000000001173,2000000000000553,2000000000000247,
  2000000000000102,2000000000000037,2000000000000011,2000000000000002,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_3_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_3_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_3 : List ℕ := pCat pvn_4_3_p0 (pCat pvn_4_3_p1 (pCat pvn_4_3_p2 (pCat pvn_4_3_p3
  (pCat pvn_4_3_p4 (pCat pvn_4_3_p5 (pCat pvn_4_3_p6 (pCat pvn_4_3_p7 (pCat pvn_4_3_p8 (pCat
  pvn_4_3_p9 pvn_4_3_p10)))))))))
private def pvn_4_4_p0 : List ℕ := [1999999690729811,2000000097325528,1999999932904353,
  2000000254586754,1999999497979809,1999999625317995,1999999491478531,1999999857095428,
  1999999534473636,2000000508707834,2000000153572217,2000000363290138,2000000470269398,
  2000000478222388,2000000096765738,1999999679977159,1999999364764158,2000000464576592,
  2000000155276550,1999999869925743,1999999824907965,1999999023967025,2000001261389432,
  1999999908588052,1999999862553848,2000000213511889,2000000169107812,1999999371637870,
  1999999722609085,1999999925557713,1999999841556052,1999999265714952,2000002793418970,
  1999993654029870,2000010637507056,1999982088634224,2000028889313851,1999956847643189,
  2000063004104248,1999914849749609,2000110655271565,1999863856517970,2000155759762687,
  1999833985674653,2000159886228254,1999865630859073,2000085600691754,1999978663005521]
private def pvn_4_4_p1 : List ℕ := [1999950780606809,2000106851667606,1999864963257699,
  2000121888612987,1999931784952842,1999990037918845,2000082490066367,1999878042765597,
  2000107139169538,1999957114528222,1999956682304792,2000107974297454,1999883299930040,
  2000063935115632,2000023952281767,1999904697131928,2000108445980607,1999946724313364,
  1999964233756095,2000101065550487,1999903840781393,2000022107258228,2000068544406113,
  1999891791093220,2000063484820948,2000031835956766,1999898414431539,2000085114478279,
  2000003843709296,1999911384002721,2000097798236626,1999974746229869,1999933525529371,
  2000092370942179,1999974971297171,1999924339729504,2000112557064327,1999955570513706,
  1999932459135794,2000104749360758,1999966969901106,1999933274090524,2000089326431178,
  1999982247105619,1999924158199075,2000084413864886,2000006095525036,1999910518243921]
private def pvn_4_4_p2 : List ℕ := [2000069471655702,2000031191051767,1999905071867151,
  2000049213872049,2000054754648392,1999901740871193,2000021238664847,2000089179695803,
  1999918521305185,1999970472394466,2000099769805553,1999954921468499,1999934139544766,
  2000088187967260,2000008524706588,1999897285997834,2000060893502984,2000050585964201,
  1999916550123679,1999979315715365,2000121654242907,1999919679621351,1999977193481248,
  2000026097557732,2000078307908967,1999832552902631,2000110471647289,2000012659387094,
  1999984783188534,1999910613610826,2000147538004603,1999928711462774,1999976863815322,
  1999983582800878,2000127823657799,1999870523816925,1999979241543223,2000073001485849,
  2000036068282557,1999861348384471,2000045671410366,2000109728669844,1999908138295750,
  1999958413393487,2000058190591471,2000063036783152,1999847766985690,2000066927511163]
private def pvn_4_4_p3 : List ℕ := [2000042261352539,1999999194249813,1999900813058810,
  2000063545937771,2000080612540459,1999915485437483,2000006147114064,1999993141374352,
  2000084256721253,1999920791305466,1999993804668370,2000062076068362,1999979806100890,
  2000006625616685,1999922909485349,2000073621310447,2000015134838004,1999967304879236,
  2000013978766395,1999965176263646,2000068272231331,1999952683703702,1999971029640116,
  2000034431723143,1999980327104356,2000064976664910,1999961227710964,1999973449975986,
  2000052860797685,1999959836501948,2000036718155720,1999959647689170,1999961546989102,
  2000037430316538,1999986800054075,1999995776636720,2000032989737616,1999900972869605,
  2000075022582876,1999988668820114,1999977480829821,2000072896722689,1999913461806549,
  2000013784845378,2000022486869737,1999965788598896,2000061158246278,1999988295765386]
private def pvn_4_4_p4 : List ℕ := [1999964760692902,2000022338883837,1999976026481804,
  1999970396911135,2000080789187192,1999960372491235,2000041096852459,1999983393988468,
  1999989904202509,1999974792428205,1999984691138027,1999992956245102,2000021834516511,
  1999990282853427,2000072659560429,1999992135895330,2000006474062952,2000043753451896,
  1999962576133836,1999942785092615,1999990796612809,1999971815638929,1999827575532660,
  2000003363199649,1999949933419881,1999840291763125,1999915902520317,2000005134236839,
  1999866935650527,1999865204834242,2000008988570030,1999937052898501,1999832538021805,
  1999976613599857,1999996947821950,1999828263783345,1999969450498683,1999980414359463,
  1999917093477149,1999863647019757,1999965878838702,1999954524984380,1999916412294831,
  1999914726782250,1999960580968691,1999892440638925,1999829050260826,1999995105695576]
private def pvn_4_4_p5 : List ℕ := [1999910024625823,1999799589009497,1999973643273066,
  1999985452446507,1999868177336408,1999843406315263,1999919662908069,2000003822077871,
  1999898598973950,1999815098376399,1999933213348665,1999965372037334,1999876543232102,
  1999875587758946,1999939277162622,1999937107518103,1999841885759680,1999835015799880,
  1999994446273717,2000003904477180,1999795957248924,1999775989334899,1999961554609523,
  1999982755965062,1999873677530608,1999873399915347,1999916226439707,1999895649609381,
  1999857487131814,1999823072685486,1999837493571120,1999955826835806,2000028885585372,
  1999910395457818,1999786512558621,1999857757385206,1999948298413241,1999843836410830,
  1999699940024736,1999756039510656,1999937372239481,2000025832657971,1999992181444810,
  1999956615566752,1999987715842792,2000074718785850,2000165605266481,2000184762441976]
private def pvn_4_4_p6 : List ℕ := [2000095818120316,2000011352940168,2000063148345581,
  2000232192159220,2000297735328550,2000178720528505,1999997490271813,2000001303875221,
  2000169131951428,2000319793479649,2000279177861326,2000114916246253,2000022864315901,
  2000074048163730,2000209533343923,2000279918813571,2000251450746875,2000193679313012,
  2000159514347694,2000173230604777,2000184109805120,2000166367353903,2000163169288170,
  2000200240364673,2000287954652988,2000384623427625,2000404968543226,2000327222286093,
  2000185651411950,2000043861707310,1999994802814520,2000080675798519,2000272478335613,
  2000523600612753,2000764548879005,2000921482882851,2000968306128809,2000900341396162,
  2000707207680915,2000400784220630,2000005219870566,1999539270919761,1999063561841171,
  1998717128427128,1998711032768625,1999351156138206,2001067095199088,2004378397788261]
private def pvn_4_4_p7 : List ℕ := [2009838883303170,2018001801388628,2029357843619603,
  2044234014473288,2062717766077477,2084623856211307,2109465082097547,2136436269714276,
  2164457298084179,2192266788830265,2218520379442608,2241886669293692,2261160958915803,
  2275381818995476,2283909482252037,2286454896047130,2283081269897973,2274188671581194,
  2260468442549127,2242822261363858,2222266816624956,2199849769612961,2176583072237558,
  2153385511363203,2131032708547172,2110124432984173,2091077601528922,2074140946973515,
  2059419073810104,2046896786784977,2036462783362626,2027935585735334,2021091887828514,
  2015693274006593,2011506464766800,2008315180652067,2005925314528766,2004166640424847,
  2002893461089983,2001984872200790,2001344190704848,2000897030952017,2000588084077754,
  2000377205180110,2000235573055814,2000142480287856,2000082960546974,2000046173204245]
private def pvn_4_4_p8 : List ℕ := [2000024331510151,2000011960055128,2000005333461547,
  2000002021333733,2000000513706029,1999999922369919,1999999755863334,1999999760892806,
  1999999818067561,1999999877972270,1999999924664815,1999999956355983,1999999976045164,
  1999999987486848,1999999993771258,1999999997049659,1999999998676201,1999999999442468,
  1999999999783550,1999999999925540,1999999999979695,1999999999997759,2000000000002325,
  2000000000002546,2000000000001775,2000000000001042,2000000000000548,2000000000000266,
  2000000000000119,2000000000000048,2000000000000018,2000000000000004,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_4_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_4_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_4 : List ℕ := pCat pvn_4_4_p0 (pCat pvn_4_4_p1 (pCat pvn_4_4_p2 (pCat pvn_4_4_p3
  (pCat pvn_4_4_p4 (pCat pvn_4_4_p5 (pCat pvn_4_4_p6 (pCat pvn_4_4_p7 (pCat pvn_4_4_p8 (pCat
  pvn_4_4_p9 pvn_4_4_p10)))))))))
private def pvn_4_5_p0 : List ℕ := [1999999643144017,2000000087908113,1999999638763931,
  2000000164388355,1999999991184066,2000000407908782,1999999557002865,1999999876522914,
  1999999753186270,1999999524994375,1999999445438020,1999999893791168,1999999740923845,
  2000000252962293,2000000129908498,1999999717238308,2000001325986337,1999999974879653,
  2000000725894438,1999999860413240,1999999219830876,1999999914528931,2000001016307984,
  1999999339357712,2000000994209294,1999996124995534,2000007940170620,1999985105483398,
  2000024870019465,1999961474118655,2000057573313742,1999919320469491,2000107647461980,
  1999865703845743,2000154958949625,1999834075993661,2000158559462565,1999870736497366,
  2000077230272502,1999990517130597,1999938655868016,2000115240705855,1999865010490926,
  2000108942859684,1999957113543362,1999962131985891,2000103231997737,1999878950515597]
private def pvn_4_5_p1 : List ℕ := [2000081396842814,1999999194404527,1999918815854359,
  2000119894808183,1999907047838181,2000012165712614,2000073507862296,1999887035980022,
  2000077261619858,2000008375091467,1999912963192437,2000103342185980,1999955668416687,
  1999951698616811,2000103180675488,1999922527510789,1999988412751716,2000090243886381,
  1999907659807641,2000011605920249,2000081924943002,1999895115227948,2000036602208266,
  2000059910164600,1999908835524690,2000027294185880,2000070047259691,1999897051024561,
  2000037673839135,2000064705262346,1999896247034041,2000038673979336,2000065535032474,
  1999902335982151,2000020374670849,2000077741621602,1999915503352969,1999992181013468,
  2000089610549809,1999936263942997,1999962870521371,2000091802892958,1999961380101188,
  1999938433367279,2000090432916197,1999992986790483,1999912784309311,2000068165091906]
private def pvn_4_5_p2 : List ℕ := [2000037750003845,1999902767059326,2000037292210376,
  2000065672743746,1999920241143803,1999974736179300,2000111412331440,1999935901367893,
  1999952978048562,2000055163330714,2000060599470263,1999853083876001,2000104165808145,
  1999996040919126,1999991197940371,1999904381546055,2000164384076142,1999916199950041,
  1999971093112351,2000014714084649,2000105619812359,1999846876497442,2000058321048229,
  2000038969190210,1999994763333700,1999910824085011,2000082868989146,2000021559627440,
  1999917112077450,1999999308285275,2000075480439050,2000006812435465,1999868469679735,
  2000115026833162,2000015074546724,1999941933430650,1999926053285888,2000152184696029,
  1999974275830310,1999884046534915,2000073317133660,2000048976158378,1999980336090822,
  1999888171630350,2000129313404956,2000002146058409,1999912656651809,2000018134538022]
private def pvn_4_5_p3 : List ℕ := [2000028463935598,2000032800456372,1999878091971424,
  2000056309379350,2000064721876681,1999946207079244,1999984698405815,1999976192954038,
  2000088833493048,1999955438101231,1999945910578506,2000053147689654,1999984791088660,
  2000022862288178,1999954756979001,2000005279984544,2000084224140350,1999931693227557,
  2000008655679923,1999991672048005,2000017634758666,2000044348138059,1999959040586217,
  1999973979216013,2000063974024563,1999945030763527,2000043634958629,1999963990916292,
  1999976508504886,2000099967968977,1999932439370577,2000016518099285,2000001626405048,
  1999938643583642,2000076517516299,1999981143157565,1999969704564186,2000027297267015,
  1999997352823818,1999996495594406,2000068527379718,1999914883685182,2000030013289335,
  1999980166315937,1999985675079938,2000027653177191,1999997371784909,1999954222222521]
private def pvn_4_5_p4 : List ℕ := [2000011567773214,1999978526040777,2000029627694716,
  1999994148242006,2000005619985433,2000007640533442,1999948469885777,2000023085358759,
  1999998884308275,2000015988109300,1999992916372904,2000047638607146,1999934685045154,
  1999993012896406,2000040076422186,1999951257438875,2000000699586098,2000086219316725,
  1999978177501637,1999949285552629,2000063119821053,1999983043364776,1999911299482787,
  2000001014951192,2000102056333104,1999897509519730,2000021212976608,2000116469668207,
  1999983347684474,1999955084369305,2000078248644711,1999998802149805,1999903663061053,
  1999992087834215,1999974158523784,1999920093309216,1999887187210578,1999958119527631,
  1999964302220300,1999826870413983,1999939247718734,1999996678750053,1999848798682108,
  1999920322015063,1999977009863803,1999879642907361,1999909261217066,1999986195749681]
private def pvn_4_5_p5 : List ℕ := [1999962146096814,1999877893691510,1999882017240335,
  1999997044459054,1999969855100692,1999849944384752,1999919849990386,2000021581300045,
  1999939103163357,1999836498768945,1999872647447820,1999966854942804,1999948319458414,
  1999844826467413,1999881380597263,1999986401179694,1999906252978996,1999823163293507,
  1999954894469462,2000009069289415,1999844236573338,1999803942167838,1999961753545592,
  2000006006500371,1999893501849915,1999833345576705,1999870723383771,1999932237215448,
  1999961511793774,1999912024537900,1999847851565604,1999888103788072,1999948366493247,
  1999880967744615,1999804151611844,1999906698081685,2000034520627573,1999960284550080,
  1999783731960358,1999784143137394,1999907186397543,1999953385230043,1999869703823117,
  1999844284350251,1999910675163208,1999987113264393,1999971282360374,1999870597840673]
private def pvn_4_5_p6 : List ℕ := [1999767053853840,1999731760708759,1999818299451985,
  1999920924368422,1999921715278928,1999839873843321,1999826553741712,1999985167985165,
  2000160034725083,2000162362312614,2000020058383867,1999933045561187,2000047774294123,
  2000239046839206,2000286764399495,2000162941143669,2000017190895906,2000013826328803,
  2000148896915347,2000258883246507,2000247014495591,2000156852218931,2000083074077469,
  2000092173955701,2000154237304049,2000193178404405,2000198431423875,2000200108734701,
  2000210189997618,2000224902743563,2000216052021008,2000161545870661,2000102930414680,
  2000103762740500,2000180054153398,2000304169469600,2000415830118894,2000438879727801,
  2000347089976331,2000189990837504,2000041831080957,1999967443706628,2000014129487923,
  2000181150887531,2000414305198759,2000652300577774,2000852008868741,2000974806447407]
private def pvn_4_5_p7 : List ℕ := [2000990933527833,2000893077304456,2000676677073046,
  2000321047061657,1999814291681854,1999188499535322,1998533390427922,1998018181120722,
  1997934577454245,1998717268692439,2000918343928509,2005164094636504,2012108749921360,
  2022360935321806,2036378048245597,2054366851054753,2076220845629277,2101487725747104,
  2129358603959865,2158696928091612,2188123701214870,2216142955907062,2241274294845893,
  2262175418248815,2277754742733263,2287267467106047,2290374586644643,2287149667600390,
  2278039266258594,2263795894529136,2245397438291235,2223956915685933,2200626046552519,
  2176503645277740,2152563373707212,2129609079034547,2108255580816239,2088927187645575,
  2071867753992507,2057160156431108,2044754534011116,2034502679478282,2026193447429235,
  2019583775535279,2014422185068292,2010464658074263,2007484708388311,2005279686059448]
private def pvn_4_5_p8 : List ℕ := [2003674534035610,2002523356561123,2001708840489768,
  2001139766960376,2000747206816700,2000480186529330,2000301535372096,2000184363032457,
  2000109321288893,2000062587423476,2000034407382030,2000018030148758,2000008905435767,
  2000004065363549,2000001646607068,2000000528289719,2000000067382953,1999999914108307,
  1999999889628712,1999999909304445,1999999937194171,1999999960651164,1999999977047616,
  1999999987360667,1999999993381923,1999999996693865,1999999998423062,1999999999283035,
  1999999999690686,1999999999874512,1999999999952961,1999999999984316,1999999999995809,
  1999999999999496,2000000000000391,2000000000000428,2000000000000285,2000000000000157,
  2000000000000075,2000000000000029,2000000000000007,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_5_p9 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_5_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_5 : List ℕ := pCat pvn_4_5_p0 (pCat pvn_4_5_p1 (pCat pvn_4_5_p2 (pCat pvn_4_5_p3
  (pCat pvn_4_5_p4 (pCat pvn_4_5_p5 (pCat pvn_4_5_p6 (pCat pvn_4_5_p7 (pCat pvn_4_5_p8 (pCat
  pvn_4_5_p9 pvn_4_5_p10)))))))))
private def pvn_4_6_p0 : List ℕ := [1999999563853246,2000000156984710,1999999664935885,
  2000000102372442,1999999567834960,2000000053565503,2000000259313707,2000000190395841,
  1999999771806432,2000000095729141,1999999995770081,1999999339712877,2000000369603531,
  1999998767592934,1999999907051455,1999999960326033,1999999861851334,1999999251034430,
  2000001810226358,1999996073070989,2000008087156265,1999986213502491,2000026911128402,
  1999957328097803,2000063036856341,1999910907654297,2000117968789851,1999855523206407,
  2000162929993368,1999834840090505,2000144390648449,1999900477094102,2000033335248723,
  2000040741960501,1999896401419744,2000133492229919,1999884083298102,2000055121291383,
  2000028904237774,1999900663254517,2000120796730618,1999918777496439,1999997459312232,
  2000084923797642,1999880216927009,2000084119574021,2000002351677906,1999913394051572]
private def pvn_4_6_p1 : List ℕ := [2000111211699566,1999939697275808,1999967450572292,
  2000100792243773,1999908540110088,2000012610553881,2000076147992515,1999897699773239,
  2000044731683263,2000049346231726,1999900584775033,2000059269602562,2000037803096020,
  1999894089050409,2000079311442383,2000015084194058,1999911488528659,2000066378029278,
  2000028629295131,1999901626968954,2000067106155977,2000035191980559,1999896589698236,
  2000064534580807,2000039774818409,1999900071104865,2000050464214511,2000051640446245,
  1999906076323222,2000027581779686,2000071357595371,1999915496711597,1999993873722525,
  2000090208055597,1999939902357624,1999954158987451,2000094110783843,1999975750936289,
  1999926985307711,2000074467469268,2000022735523967,1999903660721890,2000054085768772,
  2000047409253657,1999926653329951,1999979044216055,2000118022872856,1999908050793268]
private def pvn_4_6_p2 : List ℕ := [1999990069276037,2000032663537875,2000064988920151,
  1999838058217717,2000132064092858,1999985039966923,1999977477395100,1999926581602582,
  2000150307296254,1999912344587227,1999978350524677,2000016763241549,2000089987061566,
  1999860861919625,2000045587752487,2000068937145318,1999947912232601,1999939226420876,
  2000076919683830,2000040104587568,1999887681217252,2000049275904371,2000027994583853,
  2000013142864319,1999885987634346,2000104229369472,2000017042034667,1999931445317016,
  1999985797882415,2000079730519698,2000016010878427,1999849341897683,2000114859912162,
  2000037968320131,1999936614411782,1999946183034797,2000083941953523,2000052061145899,
  1999833716028181,2000067114815465,2000071482918852,1999967063474851,1999939288942421,
  2000011487619138,2000107688347935,1999892041048982,1999980587584439,2000073023516842]
private def pvn_4_6_p3 : List ℕ := [1999993013583400,1999978278564896,1999947697847927,
  2000086212564698,2000015304387974,1999900531834570,2000055958879380,2000008163182942,
  2000028600090832,1999948692122169,1999960610715368,2000065473161652,2000004923275935,
  1999928434039341,2000049358920212,1999975147129102,2000034301696423,1999991738022873,
  1999927602794724,2000098770706982,1999964375656388,1999973058755443,2000021757731142,
  1999939705014219,2000085806073996,1999991588602452,1999948571740739,2000028175560946,
  2000018958621598,1999963787728460,2000068608990897,1999925259803387,2000037688131300,
  2000033839884527,1999971098523934,1999998881780495,1999993052590188,1999972316337927,
  2000064800633242,1999985024852243,1999987573282026,2000006561675632,1999983350676750,
  2000029340209768,1999973590611593,2000019729762322,1999961401431781,2000009631674850]
private def pvn_4_6_p4 : List ℕ := [2000012272312220,2000040557561632,1999975534014773,
  1999993963039540,2000016652553982,1999960351594207,2000018955162349,2000034799026402,
  1999951173955186,1999978048258496,2000040556522118,1999931066471189,2000018197486555,
  2000044188698847,2000003849374225,1999918012899075,2000056956015364,2000011673622771,
  1999905816086834,2000058055065546,2000079941917201,1999920579322534,1999975710837998,
  2000093522057696,1999926822875143,1999939700834136,2000080838951034,2000010786561952,
  1999978534369276,2000009385466338,2000047661698076,1999984316233258,1999913752435368,
  2000045835458561,2000012492914159,1999901303000588,2000052191189137,2000071256754533,
  1999954519095382,2000026915722884,2000071293336193,1999992731980627,1999970360953115,
  2000005006249049,1999993753711590,1999923939245051,1999932391251527,1999990521681841]
private def pvn_4_6_p5 : List ℕ := [1999911940393161,1999849841758413,1999959669555689,
  1999993850362208,1999877753206260,1999850998724957,1999946601985182,1999987204242916,
  1999907465694295,1999857519451011,1999961940837515,2000020712045216,1999882118904584,
  1999831860717850,1999985892027366,2000007303255679,1999873211556544,1999906121057576,
  2000010894832302,1999923811696090,1999826521573652,1999918840472355,1999992258563833,
  1999910653106328,1999834713818697,1999879390256107,1999952397579608,1999976755959981,
  1999904585736311,1999832892271511,1999868663134472,1999987570708505,1999966801028750,
  1999852706994490,1999849813556982,1999956395682204,1999950355880419,1999834666575270,
  1999853466624534,1999982035253755,1999999442481509,1999856313162192,1999774352340735,
  1999867549070492,1999971131456669,1999967154862578,1999894586811257,1999858391299761]
private def pvn_4_6_p6 : List ℕ := [1999888161137808,1999914471262338,1999898221174815,
  1999836430007003,1999794786009343,1999867751887367,2000001097252520,2000042124600419,
  1999926575021889,1999773640561940,1999770578526830,1999893698516358,1999935308374337,
  1999820835102753,1999699263769619,1999752255340328,1999961960849511,2000106064450635,
  2000052669139157,1999924549727941,1999909309655415,2000046549380479,2000205970206573,
  2000232153517579,2000128910592965,2000039001539702,2000052696307673,2000136854569373,
  2000208155362511,2000209703130175,2000160411327013,2000127343111335,2000132599883676,
  2000143606814053,2000143812608968,2000147095608849,2000168557521002,2000213809396515,
  2000260758626058,2000259249737667,2000189932135258,2000099925267702,2000056837521218,
  2000097671423240,2000217623576067,2000364739324516,2000455155437942,2000432568077854]
private def pvn_4_6_p7 : List ℕ := [2000309551226769,2000144537639126,2000004516684541,
  1999950210210322,2000016002850028,2000186655504950,2000411182903601,2000641147801685,
  2000842850454921,2000985240999523,2001039729429433,2000986625912316,2000802782696396,
  2000447682589296,1999882347245964,1999112654542905,1998224892530526,1997411355358477,
  1997002170781037,1997491426925029,1999524743416521,2003840203390075,2011184942519663,
  2022223550748932,2037435131471394,2057003472019437,2080728843633718,2107991970533592,
  2137776332415118,2168735651419191,2199296371014508,2227792825893727,2252625544496051,
  2272417187792384,2286136605633569,2293174911447420,2293374005714686,2287013870384193,
  2274762223449397,2257589784269327,2236661088485433,2213218448505009,2188477346761108,
  2163544491039109,2139360946051172,2116667969826632,2095993047409874,2077654741536593]
private def pvn_4_6_p8 : List ℕ := [2061784335620583,2048359788461653,2037245370740697,
  2028230325011274,2021062003539978,2015471794628783,2011194268945254,2007980775417845,
  2005608540033829,2003885883021991,2002653973197719,2001785667244976,2001182237148060,
  2000768936054278,2000490284574622,2000305716189747,2000185917049843,2000109938247710,
  2000063000066831,2000034845974642,2000018507168649,2000009369724440,2000004470035810,
  2000001968619844,2000000766185864,2000000232589963,2000000022913304,1999999958014801,
  1999999950499837,1999999961043629,1999999973939749,1999999984175515,1999999991038010,
  1999999995202577,1999999997555475,1999999998810194,1999999999446266,1999999999753860,
  1999999999895870,1999999999958377,1999999999984492,1999999999994760,1999999999998496,
  1999999999999710,2000000000000030,2000000000000070,2000000000000046,2000000000000019]
private def pvn_4_6_p9 : List ℕ := [2000000000000005,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_6_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_6 : List ℕ := pCat pvn_4_6_p0 (pCat pvn_4_6_p1 (pCat pvn_4_6_p2 (pCat pvn_4_6_p3
  (pCat pvn_4_6_p4 (pCat pvn_4_6_p5 (pCat pvn_4_6_p6 (pCat pvn_4_6_p7 (pCat pvn_4_6_p8 (pCat
  pvn_4_6_p9 pvn_4_6_p10)))))))))
private def pvn_4_7_p0 : List ℕ := [1999999466878070,2000000149646064,1999999673676510,
  2000000045439195,1999999976073193,1999999859536692,1999999626335425,1999999734427787,
  2000000726554444,1999999338527845,2000000679974967,1999999769781604,2000000427071593,
  1999998127693994,2000004970354082,1999989559415285,2000018540307980,1999966392161812,
  2000053650378184,1999918945022307,2000110769898863,1999859957823837,2000161484223125,
  1999832405503393,2000147107143083,1999902573312054,2000027952023277,2000050852693029,
  1999888161577081,2000133393604678,1999896940491149,2000029011087405,2000058019245792,
  1999885405570685,2000109853792657,1999956942035251,1999949784909045,2000113401090028,
  1999894202990622,2000029103681341,2000065182694282,1999887350691756,2000078951525947,
  2000013653457716,1999906344273522,2000098582019339,1999976912239087,1999928730158753]
private def pvn_4_7_p1 : List ℕ := [2000103813559521,1999952439489943,1999950982103552,
  2000097459851071,1999948545514902,1999951989829092,2000106669924967,1999930572465871,
  1999969828629930,2000092261462046,1999945857159401,1999956459134038,2000096035345122,
  1999958464146200,1999938136889011,2000101207455845,1999970387050840,1999925056870480,
  2000095798205339,1999990845531270,1999914771039697,2000077867926270,2000018706751804,
  1999908677886366,2000051659619565,2000049610669013,1999911937648242,2000013544664942,
  2000080801756371,1999925676450564,1999973363684166,2000087692153568,1999976478926535,
  1999914753724878,2000093991711891,2000001124972768,1999935982338503,2000000432306394,
  2000112410178682,1999865203024600,2000049101563799,2000016701644349,2000039086129639,
  1999855381199550,2000150801741019,1999960183753548,1999962953034387,1999975118787689]
private def pvn_4_7_p2 : List ℕ := [2000129284944911,1999883343368643,2000005110543809,
  2000043722525836,2000032475200890,1999892505714216,2000044987985946,2000084806366597,
  1999904374483446,1999982204556455,2000063803355214,2000035722143264,1999863741482924,
  2000097699843885,2000015664745373,1999964276814474,1999946683769947,2000082451395751,
  2000024458773645,1999885332223068,2000057356373586,2000029517950286,2000010904080267,
  1999894530080408,2000075156064183,2000063248565390,1999874186013730,2000028678181835,
  2000053317395877,2000024730949997,1999882360224448,2000036596562696,2000125189219604,
  1999871796419075,1999979390850366,2000066599279277,2000043564083362,1999923598185647,
  1999946202850010,2000141195154782,1999963440843105,1999907823720646,2000056088016019,
  2000031318068948,2000022679544031,1999893797441814,2000047862736152,2000063888201172]
private def pvn_4_7_p3 : List ℕ := [1999926085387636,1999974924529287,2000061762260406,
  1999993400142990,2000006061378768,1999931290312176,2000041456518607,2000074010937682,
  1999886587944843,2000027575310678,2000019975205944,1999998118191367,2000038523521911,
  1999896047196555,2000063390358633,2000035870218654,1999956856066943,2000000307724442,
  2000025640174043,1999960932959928,2000068554506187,1999914324326348,2000003777414518,
  2000060318540756,1999963327588049,1999983674097605,2000012037370813,1999972685023280,
  2000060687717092,1999984194133689,1999952070317144,2000030825778347,1999974242976910,
  2000034204031426,1999973392560455,2000005123122774,1999987535081571,2000032676900970,
  1999995671952215,1999982614512558,1999991664680710,2000015613723287,2000034953775991,
  1999982976019021,2000004724510784,1999993690809887,1999976375318098,2000012999493064]
private def pvn_4_7_p4 : List ℕ := [2000054005858903,1999929907156096,2000030290680965,
  2000010880272681,1999988626576224,2000006072338267,2000029672902344,1999957980550305,
  1999952050757706,2000070016193892,1999994724058491,1999958147390127,2000061263983388,
  2000020521548505,1999900041143344,2000040885972685,2000091151130377,1999900305099158,
  1999999810304017,2000070036350098,1999920778447820,1999961516184940,2000048338928642,
  2000029267664214,1999960592754876,1999971706722883,2000063481249284,1999962555451461,
  1999921492419656,2000085387087545,2000024648197972,1999930260450493,2000049861782062,
  2000031837345133,1999926207895234,1999983944640357,2000040430922196,1999993227890653,
  1999976375319077,2000038265096659,2000045953305015,1999966213455036,1999976012485797,
  2000033854811347,1999967960576288,1999937021574029,2000029999120806,2000031586007317]
private def pvn_4_7_p5 : List ℕ := [1999963009692630,2000008448726917,2000080629518755,
  2000040312078080,1999958991825478,1999976296094943,2000065643876740,2000029023577928,
  1999880315507842,1999903241310502,2000037420763109,1999964373970654,1999824352522474,
  1999924671595400,2000019578901091,1999897303374146,1999826452602044,1999953677054741,
  1999979083227458,1999893196437487,1999898061608430,1999978468372524,1999944059210194,
  1999875309014184,1999895072695325,1999962632037860,1999993535595893,1999938413832811,
  1999872776942544,1999892286666830,1999992227070130,1999991044177982,1999852155241620,
  1999816350395163,1999940471582691,2000003709635454,1999897414494079,1999826971501788,
  1999920684775556,1999976401717109,1999892688444938,1999839249083231,1999919696016080,
  1999999061157796,1999930005589175,1999819962360367,1999836430308547,1999936333093951]
private def pvn_4_7_p6 : List ℕ := [1999990277652374,1999946847544065,1999862145481378,
  1999835139189146,1999880715427061,1999934537175851,1999931130768143,1999869240878686,
  1999852317222013,1999937785903494,2000003669220902,1999925389452619,1999771330296632,
  1999729376837694,1999871614948725,2000029699314657,2000006044503083,1999859098658810,
  1999803786788498,1999902042366673,2000000612405004,1999937298669528,1999752216338488,
  1999655542344949,1999758185194234,1999933523998589,2000000614591126,1999934039876052,
  1999855144038951,1999886514805273,2000023006202699,2000141497070933,2000153122041791,
  2000096688164398,2000059381112575,2000076272560451,2000125312718878,2000164028740928,
  2000168340107194,2000157510573004,2000160942209649,2000168205904730,2000151004861337,
  2000116729458568,2000102128408395,2000131885902364,2000201456412335,2000274569193435]
private def pvn_4_7_p7 : List ℕ := [2000294011866680,2000229056321173,2000117038170299,
  2000036578109241,2000044136984546,2000144666821550,2000297542713485,2000430316497674,
  2000470519543422,2000393400024294,2000238374051773,2000075667253218,1999966931271836,
  1999952159878013,2000045203699990,2000225700018610,2000447703574386,2000668571165007,
  2000865650699983,2001023227345143,2001113223838235,2001092251304283,2000906257017148,
  2000492135882349,1999791910713903,1998797015353900,1997609716367589,1996491605727188,
  1995885781278883,1996417075024160,1998867067380265,2004107709916021,2012988220809513,
  2026196397267034,2044127296379873,2066781349781402,2093700876368032,2123954176039673,
  2156180575130889,2188701419398837,2219682000967760,2247314244029319,2269990452055495,
  2286448755084083,2295878924177222,2297979143152144,2292956254554736,2281469822100598]
private def pvn_4_7_p8 : List ℕ := [2264532066948847,2243384071880566,2219368954077861,
  2193816821052208,2167949598062073,2142809838433639,2119216047774703,2097745472811092,
  2078742321097040,2062345762310514,2048529664483839,2037145996429710,2027965848090127,
  2020714768677477,2015101344046188,2010839115734741,2007662301767600,2005335823761530,
  2003660251015346,2002472517963558,2001643526934278,2001073854906571,2000688676004215,
  2000432737841633,2000265895496602,2000159411116637,2000093024231772,2000052693478113,
  2000028879908527,2000015252226015,2000007718415401,2000003711267742,2000001672028979,
  2000000687377804,2000000242517764,2000000059383000,1999999994799941,1999999979065047,
  1999999980532570,1999999986158415,1999999991360197,1999999995042484,1999999997330371,
  1999999998636397,1999999999335572,1999999999690305,1999999999861828,1999999999941070]
private def pvn_4_7_p9 : List ℕ := [1999999999976058,1999999999990801,1999999999996698,
  1999999999998917,1999999999999688,1999999999999928,1999999999999987,1999999999999999,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_7_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_7 : List ℕ := pCat pvn_4_7_p0 (pCat pvn_4_7_p1 (pCat pvn_4_7_p2 (pCat pvn_4_7_p3
  (pCat pvn_4_7_p4 (pCat pvn_4_7_p5 (pCat pvn_4_7_p6 (pCat pvn_4_7_p7 (pCat pvn_4_7_p8 (pCat
  pvn_4_7_p9 pvn_4_7_p10)))))))))
private def pvn_4_8_p0 : List ℕ := [1999999406749470,2000000012203988,1999999860133541,
  1999999800337727,2000000016559632,1999999547646574,2000000926702823,1999998882409468,
  2000000900023873,1999996915020476,2000007410575142,1999983806630484,2000030442544517,
  1999948658012211,2000080351703626,1999885690499572,2000146447434624,1999833261788847,
  2000165403556314,1999866099889008,2000070354512096,2000012154099798,1999909376814468,
  2000131589334613,1999881787535628,2000051084452232,2000040292194877,1999890215667822,
  2000112993837786,1999952751751966,1999950401607919,2000115558095090,1999899819901680,
  2000015291397082,2000080681804373,1999886396351364,2000056940733716,2000044673666465,
  1999893575597134,2000076288951072,2000020788294089,1999901043245208,2000087206466102,
  2000003580137055,1999913573509261,2000078225911312,2000013043235590,1999902122777131]
private def pvn_4_8_p1 : List ℕ := [2000089409056636,2000005292378379,1999912137418247,
  2000073332802789,2000021680060454,1999910183372733,2000052998778622,2000047857553992,
  1999902627637809,2000033079928281,2000072905746591,1999904883793788,2000004865610874,
  2000090042788322,1999923962483710,1999969451790073,2000096350827387,1999957795685659,
  1999938178117447,2000082266356717,2000007681488692,1999909788050866,2000060569044219,
  2000039644655098,1999928128182106,1999986554865709,2000109414964704,1999909017098031,
  1999992169138254,2000036124408929,2000060372643001,1999839920687498,2000128481072151,
  1999980314530975,1999992443310457,1999917131127529,2000150327976209,1999910545856630,
  1999979655714549,2000027838491533,2000072755527388,1999868949692148,2000051119577421,
  2000060661964933,1999946156260672,1999957564102044,2000056606760932,2000051511253165]
private def pvn_4_8_p2 : List ℕ := [1999874097128042,2000056635471874,2000040984151828,
  1999993642710239,1999891615879453,2000117643502306,2000012260067153,1999897330828463,
  2000038175847457,2000050463332454,2000002741242735,1999885071832437,2000101825342147,
  2000016408066024,1999932470298658,2000003180278151,2000034615140617,2000050632427388,
  1999869966302294,2000050597159735,2000081257914989,1999929658062122,1999969510686071,
  2000019678149652,2000094474393015,1999893248258870,1999964241472196,2000134003957490,
  1999949329924836,1999932543718594,2000024694155972,2000078636161848,1999981939680513,
  1999864064266814,2000126663275690,2000030550508447,1999912038950237,1999979688578727,
  2000066948049821,2000032785740043,1999931310306650,1999949518882240,2000125003680809,
  1999977495408148,1999902112069370,2000066094009182,2000005363771623,2000025363564677]
private def pvn_4_8_p3 : List ℕ := [1999951440867418,1999958672260396,2000129395266307,
  1999914084946076,1999980651678897,2000041114531119,2000016394937165,1999990843349271,
  1999980144706903,1999948301447316,2000114823355265,1999947565311785,1999947148582137,
  2000051873709857,1999997187145706,2000007296078571,2000002747455503,1999935023557128,
  2000056570914947,2000028251716726,1999928153389974,2000040363045567,1999976057874160,
  2000033253779970,1999980015428882,1999986057337404,2000005672605186,2000037659562158,
  1999994144962610,1999969473548655,2000003070915446,2000003301471629,2000023373381513,
  1999979405004820,1999984828711477,1999985777895856,2000020998545390,2000001691316292,
  2000021253082120,1999937935561788,2000043894353854,2000009244992462,1999961407431288,
  2000012508421221,1999995583182166,1999985614093564,2000016867981281,2000038195225589]
private def pvn_4_8_p4 : List ℕ := [1999948326895817,1999978919840844,2000048385069105,
  1999992194237871,1999986889150931,2000049213355131,1999991695946175,1999923836224911,
  2000075407085268,2000039657927443,1999888410215463,2000051257813772,2000050557795501,
  1999914932655777,2000035833264570,2000067634899170,1999960056366844,1999946102993643,
  2000018106684807,2000044481047095,1999948322841497,1999989738372023,2000090911383685,
  1999951526916427,1999930612245593,2000089457037000,2000018194210705,1999936843048034,
  2000038051316596,2000025110061908,1999933622873783,1999977262727072,2000042046568166,
  1999998902763170,1999964567363538,2000024162913489,2000024490539610,1999940271205517,
  1999973557850485,2000050189106640,1999993624130082,1999971242056178,2000045801445153,
  2000021273184015,1999949480796969,1999984796869785,2000023556900218,1999988928976450]
private def pvn_4_8_p5 : List ℕ := [1999967266989672,2000020301206618,2000062625575067,
  2000009050416202,1999934587439067,2000015061896958,2000072319093277,1999946341694859,
  1999876348066473,2000048443652060,2000095894313068,1999940573239401,1999942303648770,
  2000098829761550,2000074574561066,1999946255181377,1999998443070010,2000068853446221,
  1999992113354795,1999919448543987,1999959714802071,1999988209724771,1999936099826541,
  1999911526646272,1999929896338800,1999944032949041,1999923781376425,1999874330380075,
  1999887890117453,1999973386673506,1999997747263267,1999892926979860,1999823362215035,
  1999935595134797,2000033541146546,1999936750496570,1999832932569616,1999909016519126,
  2000024960903809,1999977633516722,1999864448334826,1999889116248813,1999970470322793,
  1999938154486491,1999860229864206,1999877121863951,1999957877109446,1999965342520190]
private def pvn_4_8_p6 : List ℕ := [1999879266045467,1999833064841718,1999891326582320,
  1999968598993938,1999977483647968,1999907992591903,1999831603505662,1999845963896061,
  1999936677500818,1999983026326358,1999926813639677,1999847875274330,1999863016768143,
  1999953958430421,1999964009904439,1999846634933287,1999772367754591,1999872492066050,
  2000032661385324,2000044787628474,1999880545657892,1999737595848171,1999787717162053,
  1999941820986682,1999982739622056,1999875693008696,1999793079136403,1999862252179515,
  2000008005612834,2000050447637117,1999920496632319,1999748858755884,1999707574549596,
  1999803925904669,1999901633801725,1999903802815752,1999841166097308,1999809280755224,
  1999865789292350,1999976578232618,2000057399838812,2000072140079496,2000060366088947,
  2000066004938724,2000087700052106,2000106636755139,2000118703800036,2000131455412074]
private def pvn_4_8_p7 : List ℕ := [2000154002393083,2000184266898421,2000196190421357,
  2000162391252665,2000099532023079,2000065457267249,2000100992324667,2000191218776410,
  2000281615562966,2000313940808839,2000257844732529,2000137581182707,2000029107441809,
  2000009036128594,2000097583991836,2000251129869669,2000397742337844,2000472362769201,
  2000438822172003,2000307448171867,2000135960473531,1999998541067641,1999945075485733,
  1999987159850329,2000112039816673,2000297041346925,2000513922552952,2000735161315416,
  2000942992693574,2001123804188635,2001243756757632,2001228721802003,2000971643478584,
  2000365617057626,1999348208157891,1997952825225966,1996369557610990,1995003433509198,
  1994501228231586,1995723359615412,1999660328056177,2007309578802746,2019529212580062,
  2036882842606611,2059497217677990,2086964167590239,2118315679853098,2152082447448293]
private def pvn_4_8_p8 : List ℕ := [2186424554383305,2219310988351240,2248723117886409,
  2272858250187273,2290308177828049,2300187608572253,2302194217628692,2296595968866674,
  2284156231700166,2266016394090149,2243557218926822,2218257065034491,2191561257748026,
  2164773954073738,2138980894542391,2115007170768411,2093408705314138,2074491127495242,
  2058346846426320,2044900975345418,2033958642932841,2025248816338681,2018461981756249,
  2013280478791759,2009401120868764,2006550296192414,2004492251313504,2003031723514751,
  2002012402052558,2001312768842289,2000840693611861,2000527819520286,2000324389055831,
  2000194823278395,2000114129697073,2000065079231582,2000036037039604,2000019323915005,
  2000009998259636,2000004967233199,2000002352539193,2000001049897365,2000000432337941,
  2000000157051032,2000000044166626,2000000003567451,1999999992466852,1999999991856763]
private def pvn_4_8_p9 : List ℕ := [1999999994023184,1999999996257570,1999999997869753,
  1999999998868081,1999999999431061,1999999999727555,1999999999875236,1999999999945274,
  1999999999977013,1999999999990772,1999999999996469,1999999999998720,1999999999999562,
  1999999999999861,1999999999999962,1999999999999993,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_8_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_8 : List ℕ := pCat pvn_4_8_p0 (pCat pvn_4_8_p1 (pCat pvn_4_8_p2 (pCat pvn_4_8_p3
  (pCat pvn_4_8_p4 (pCat pvn_4_8_p5 (pCat pvn_4_8_p6 (pCat pvn_4_8_p7 (pCat pvn_4_8_p8 (pCat
  pvn_4_8_p9 pvn_4_8_p10)))))))))
private def pvn_4_o_p0 : List ℕ := [1999999492256902,1999999675420840,2000000170112213,
  1999999170584850,2000001393800765,1999996911259968,2000006344704441,1999984583570651,
  2000032333843090,1999942027587686,2000091851304813,1999869616848176,2000162017430279,
  1999826799011500,2000149041990926,1999912845883577,1999999281861704,2000087017030820,
  1999865711756457,2000115939354579,1999963141160903,1999939648368839,2000117949683677,
  1999903043518114,2000008221325301,2000087839946528,1999880894766339,2000055871757574,
  2000050373779635,1999885702338046,2000079762859826,2000023683534627,1999895920339171,
  2000084364664570,2000014659776664,1999899483292026,2000088576622071,2000009058022536,
  1999911352314441,2000068788146145,2000032649263463,1999894899903054,2000068252897227,
  2000040231274857,1999900049764511,2000046146734909,2000057040406935,1999912313934088]
private def pvn_4_o_p1 : List ℕ := [2000010505622637,2000080772493312,1999927779851078,
  1999970999612002,2000096961122160,1999954742217054,1999934837970877,2000093932521365,
  1999997673913439,1999906989886134,2000069601502456,2000041359646749,1999910826838835,
  2000009311537604,2000091395436409,1999918635483920,1999981414929443,2000060899126626,
  2000022155105955,1999875632652683,2000113601138388,1999981048690015,1999988378484277,
  1999920910338635,2000165783237241,1999876240268870,2000007694497528,2000018547573581,
  2000075495991399,1999863702961638,2000061302969968,2000044127601971,1999975307077536,
  1999920406419558,2000095028481215,2000021334121993,1999888347624338,2000061299608740,
  2000033002619388,1999982873730137,1999910159924589,2000120561836835,1999975777321217,
  1999945827289675,1999997694089278,2000080799690972,1999978363357117,1999887306699308]
private def pvn_4_o_p2 : List ℕ := [2000124979265250,1999996067801733,1999943019281514,
  1999973213093557,2000092138781973,1999995822857668,1999877571656149,2000102749801259,
  2000014898943690,1999959265656028,1999961438179961,2000042410980877,2000072618334801,
  1999875339397562,2000026477775415,2000067093463231,1999973802642716,1999956175520130,
  1999992168046202,2000109505304647,1999938406916897,1999902087021527,2000127103565617,
  1999997396350897,1999954630023963,1999948473510267,2000093035031078,2000025523063924,
  1999877053132884,2000029068740454,2000114663317706,1999918464792503,1999945668813227,
  2000052931656002,2000048709243760,1999983826631180,1999883732360748,2000094770163328,
  2000078561878960,1999852373764817,2000045591979632,2000017134122715,2000043112359038,
  1999950908857878,1999946645452632,2000070716110783,2000050538854153,1999872407962764]
private def pvn_4_o_p3 : List ℕ := [2000051212685485,2000031095417827,1999988871956365,
  1999999258305058,1999949919325845,2000046325276186,2000045781933732,1999904671588365,
  2000015158875475,2000078171261342,1999940181001922,2000024985979694,1999945027544709,
  2000037577275137,2000040542770448,1999963922856344,1999971527666151,2000031711314052,
  2000024927932049,1999974578073015,1999986885822370,1999985427506498,2000038251030561,
  1999995791894645,1999983708980229,1999982777012359,2000038466438452,1999982201022863,
  2000008071904603,1999962120864158,2000030351438132,2000021059832160,1999964015976901,
  2000011115384216,1999977066536675,2000007001930882,2000038870901118,1999996121720131,
  1999953675056434,2000018759633442,2000038792957235,1999969978658926,2000000012630488,
  2000010081069096,1999972754308141,1999992029437695,2000042395066838,1999978227876937]
private def pvn_4_o_p4 : List ℕ := [1999939496849237,2000079950569103,2000009629437664,
  1999916496233142,2000068574916152,1999990399448803,1999911500056562,2000080028102762,
  2000039426710423,1999924482369932,1999990089004344,2000041374637491,1999997532788601,
  1999958588609098,2000037932743576,2000049636895600,1999920685056772,1999996619968710,
  2000103940410532,1999954065812488,1999934935550746,2000067772644774,1999998892977794,
  1999940907904808,2000050003498426,2000053696517691,1999952609371689,1999967363273950,
  2000035945050593,1999998695458240,1999961067738927,2000031067665715,2000032802074603,
  1999946240080248,1999984104432290,2000057419830762,1999992918262468,1999976322195720,
  2000043105454559,2000013415965746,1999943631846587,1999989246868695,2000020855022233,
  1999996196530210,1999979301086845,2000015706843654,2000020228425918,1999973094604579]
private def pvn_4_o_p5 : List ℕ := [1999944952285700,2000018066117724,2000050893998304,
  1999953393792985,1999965020441930,2000088770759777,2000039864384372,1999884308772188,
  1999964195327636,2000104746100964,1999992287388019,1999896068184999,2000028129459815,
  2000108665601133,1999990366339519,1999938871078217,2000027111765250,2000025070733601,
  1999950882383818,1999959311125676,2000012283325926,2000016666585881,1999986330716886,
  1999993849183643,2000033719951601,2000051204298476,2000025342359571,1999986536645787,
  2000008888222159,2000044117839572,1999973350044729,1999893451521289,1999955410204860,
  2000044514938956,1999967833537271,1999822848576839,1999858745917858,2000006717552527,
  1999992729617925,1999859725685603,1999855256006679,1999965385669619,1999986696433008,
  1999896702336740,1999865707484027,1999940998537244,1999975006753729,1999919310931857]
private def pvn_4_o_p6 : List ℕ := [1999896220996650,1999948199311364,1999984468401567,
  1999945779045174,1999876757989962,1999866314949417,1999930831110579,1999981819976778,
  1999946629108582,1999860202105202,1999824637911195,1999897911575704,1999995407547555,
  1999975767429520,1999861930708528,1999823052413655,1999910898470943,1999984559821908,
  1999927927034674,1999824320399258,1999844020423514,1999982801488346,2000036343028797,
  1999900267422411,1999745474575685,1999778006150008,1999953652243020,2000052092566908,
  1999965647946365,1999821287405371,1999805233427578,1999916214370084,1999976248115867,
  1999888582521664,1999769360209746,1999778820325560,1999916974773798,2000039435929073,
  2000025956085480,1999901018885748,1999795781104550,1999796769324265,1999857308943425,
  1999878858266227,1999837991948401,1999791739535066,1999793360296253,1999845620026074]
private def pvn_4_o_p7 : List ℕ := [1999915897132409,1999969959156608,2000000695896907,
  2000027665099215,2000060604351223,2000080809873469,2000076011471582,2000071039435748,
  2000099203442278,2000157549334370,2000208027154647,2000212322936699,2000160167911201,
  2000081938381516,2000039119001494,2000080093192247,2000190868061571,2000298411756914,
  2000329399536308,2000263308511204,2000138262968793,2000024832000463,1999991967109537,
  2000070533692428,2000229086457178,2000388601700609,2000472276135279,2000447932538594,
  2000332895567008,2000174352138984,2000029914168456,1999951026765207,1999964154105522,
  2000061262653688,2000213711758547,2000398979252687,2000613211672887,2000859022443704,
  2001123003393119,2001359031399423,2001479060789699,2001351020348694,2000816204256321,
  1999741540954590,1998103288827972,1996076218498675,1994098125343047,1992891459023916]
private def pvn_4_o_p8 : List ℕ := [1993434111288954,1996873196882649,2004379788189870,
  2016958549085019,2035247012806500,2059348901170899,2088737600755642,2122247634896069,
  2158155434959516,2194339644549369,2228501602219666,2258415740813351,2282171099900700,
  2298365432090084,2306224588575378,2305637295017604,2297111597287869,2281669478848988,
  2260700479790249,2235796119893134,2208586333896473,2180596849215090,2153141653863666,
  2127257597281738,2103680400748295,2082855127645413,2064970901425414,2050009387859098,
  2037798245570559,2028063119710027,2020473942171885,2014683024337344,2010353772533025,
  2007179975753887,2004896552030233,2003283324781475,2002163747712019,2001400489904880,
  2000889507031631,2000553791364619,2000337544374236,2000201142353336,2000117005695647,
  2000066331395611,2000036578800289,2000019579173607,2000010145181137,2000005071429667]
private def pvn_4_o_p9 : List ℕ := [2000002434109169,2000001113839584,2000000480426070,
  2000000191345923,2000000067359027,2000000018488747,2000000001633616,1999999997251592,
  1999999997072517,1999999997916082,1999999998738860,1999999999307183,1999999999644981,
  1999999999827995,1999999999920622,1999999999964966,1999999999985184,1999999999993991,
  1999999999997665,1999999999999133,1999999999999697,1999999999999903,1999999999999974,
  1999999999999995,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_o_p10 : List ℕ := [2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000,
  2000000000000000,2000000000000000,2000000000000000,2000000000000000,2000000000000000]
private def pvn_4_o : List ℕ := pCat pvn_4_o_p0 (pCat pvn_4_o_p1 (pCat pvn_4_o_p2 (pCat pvn_4_o_p3
  (pCat pvn_4_o_p4 (pCat pvn_4_o_p5 (pCat pvn_4_o_p6 (pCat pvn_4_o_p7 (pCat pvn_4_o_p8 (pCat
  pvn_4_o_p9 pvn_4_o_p10)))))))))
private abbrev dP_0 : Prop := rkmAllTrueF [
    bSlideChk 49 129 phbn_0 pvn_0_0 pvn_0_o,
    muxIntListEq rkmHbHiHiB_m128_r512_s0 (uOfNatHb phbn_0),
    muxIntListEq rkmHbHiHiB_m128_r512_s1 (uOfNatHb phbn_1),
    muxIntListEq rkmHbHiHiB_m128_r512_s2 (uOfNatHb phbn_2),
    muxIntListEq rkmHbHiHiB_m128_r512_s3 (uOfNatHb phbn_3),
    muxIntListEq rkmHbHiHiB_m128_r512_s4 (uOfNatHb phbn_4)
  ] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := rkmAllTrueF [
    bSlideChk 25 257 phbn_1 pvn_1_0 pvn_1_1,
    muxIntListEq rkmViHiHiB_m128_r512_s0 (bDec bZ pvn_0_0),
    muxIntListEq rkmViHiHiB_m128_r512_s1 (bDec bZ pvn_1_0),
    muxIntListEq rkmViHiHiB_m128_r512_s2 (bDec bZ pvn_2_0),
    muxIntListEq rkmViHiHiB_m128_r512_s3 (bDec bZ pvn_3_0),
    muxIntListEq rkmViHiHiB_m128_r512_s4 (bDec bZ pvn_4_0)
  ] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := rkmAllTrueF [
    bSlideChk 19 257 phbn_1 pvn_1_1 pvn_1_2,
    muxIntListEq (bDec bZ pvn_0_o) rkmVoHiHiB_m128_r512_s0,
    muxIntListEq (bDec bZ pvn_1_o) rkmVoHiHiB_m128_r512_s1,
    muxIntListEq (bDec bZ pvn_2_o) rkmVoHiHiB_m128_r512_s2,
    muxIntListEq (bDec bZ pvn_3_o) rkmVoHiHiB_m128_r512_s3,
    muxIntListEq (bDec bZ pvn_4_o) rkmMidHiHiB_m128_r512_s4a
  ] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := bSlideChk 17 257 phbn_1 pvn_1_2 pvn_1_o = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := bSlideChk 16 385 phbn_2 pvn_2_0 pvn_2_1 = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := bSlideChk 14 385 phbn_2 pvn_2_1 pvn_2_2 = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := bSlideChk 13 385 phbn_2 pvn_2_2 pvn_2_3 = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := bSlideChk 12 385 phbn_2 pvn_2_3 pvn_2_o = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := bSlideChk 14 513 phbn_3 pvn_3_0 pvn_3_1 = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := bSlideChk 13 513 phbn_3 pvn_3_1 pvn_3_2 = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := bSlideChk 12 513 phbn_3 pvn_3_2 pvn_3_3 = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := bSlideChk 11 513 phbn_3 pvn_3_3 pvn_3_4 = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := bSlideChk 11 513 phbn_3 pvn_3_4 pvn_3_5 = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := bSlideChk 10 513 phbn_3 pvn_3_5 pvn_3_o = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := bSlideChk 9 513 phbn_4 pvn_4_0 pvn_4_1 = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := bSlideChk 9 513 phbn_4 pvn_4_1 pvn_4_2 = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := bSlideChk 9 513 phbn_4 pvn_4_2 pvn_4_3 = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := bSlideChk 9 513 phbn_4 pvn_4_3 pvn_4_4 = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := bSlideChk 9 513 phbn_4 pvn_4_4 pvn_4_5 = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := bSlideChk 8 513 phbn_4 pvn_4_5 pvn_4_6 = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := bSlideChk 8 513 phbn_4 pvn_4_6 pvn_4_7 = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := bSlideChk 8 513 phbn_4 pvn_4_7 pvn_4_8 = true
private theorem bk_21 : dP_21 := by decide +kernel
private abbrev dP_22 : Prop := bSlideChk 8 513 phbn_4 pvn_4_8 pvn_4_o = true
private theorem bk_22 : dP_22 := by decide +kernel
/-- Certified `T_16` walk `rkmWalkHiHiB_m128_r512_s0` (`FindAllJohnsonRampKickMuxHi128T5`). -/
theorem rkmWalkHiHiB_m128_r512_s0 :
    muxFastIterFullT16 49 129 rkmHbHiHiB_m128_r512_s0 rkmViHiHiB_m128_r512_s0 =
      rkmVoHiHiB_m128_r512_s0 :=
  bWalkBridge (bSlSndNN (rkmHd bk_0)) (rkmHd (rkmTl bk_0)) (rkmHd (rkmTl bk_1)) (rkmHd (rkmTl
    bk_2))
private theorem pw_w1_1 : pWOk 44 257 phbn_1 (bDec bZ pvn_1_0) pvn_1_2 := pChnN 44
  (bSlSndNN (rkmHd bk_1)) (rkmHd bk_2) rfl
private theorem pw_w1_2 : pWOk 61 257 phbn_1 (bDec bZ pvn_1_0) pvn_1_o := pChnN 61 pw_w1_1 bk_3
  rfl
/-- Certified `T_16` walk `rkmWalkHiHiB_m128_r512_s1` (`FindAllJohnsonRampKickMuxHi128T5`). -/
theorem rkmWalkHiHiB_m128_r512_s1 :
    muxFastIterFullT16 61 257 rkmHbHiHiB_m128_r512_s1 rkmViHiHiB_m128_r512_s1 =
      rkmVoHiHiB_m128_r512_s1 :=
  bWalkBridge pw_w1_2 (rkmHd (rkmTl (rkmTl bk_0))) (rkmHd (rkmTl (rkmTl bk_1))) (rkmHd (rkmTl
    (rkmTl bk_2)))
private theorem pw_w2_1 : pWOk 30 385 phbn_2 (bDec bZ pvn_2_0) pvn_2_2 := pChnN 30 (bSlSndNN bk_4)
  bk_5 rfl
private theorem pw_w2_2 : pWOk 43 385 phbn_2 (bDec bZ pvn_2_0) pvn_2_3 := pChnN 43 pw_w2_1 bk_6
  rfl
private theorem pw_w2_3 : pWOk 55 385 phbn_2 (bDec bZ pvn_2_0) pvn_2_o := pChnN 55 pw_w2_2 bk_7
  rfl
/-- Certified `T_16` walk `rkmWalkHiHiB_m128_r512_s2` (`FindAllJohnsonRampKickMuxHi128T5`). -/
theorem rkmWalkHiHiB_m128_r512_s2 :
    muxFastIterFullT16 55 385 rkmHbHiHiB_m128_r512_s2 rkmViHiHiB_m128_r512_s2 =
      rkmVoHiHiB_m128_r512_s2 :=
  bWalkBridge pw_w2_3 (rkmHd (rkmTl (rkmTl (rkmTl bk_0)))) (rkmHd (rkmTl (rkmTl (rkmTl bk_1))))
    (rkmHd (rkmTl (rkmTl (rkmTl bk_2))))
private theorem pw_w3_1 : pWOk 27 513 phbn_3 (bDec bZ pvn_3_0) pvn_3_2 := pChnN 27 (bSlSndNN bk_8)
  bk_9 rfl
private theorem pw_w3_2 : pWOk 39 513 phbn_3 (bDec bZ pvn_3_0) pvn_3_3 := pChnN 39 pw_w3_1 bk_10
  rfl
private theorem pw_w3_3 : pWOk 50 513 phbn_3 (bDec bZ pvn_3_0) pvn_3_4 := pChnN 50 pw_w3_2 bk_11
  rfl
private theorem pw_w3_4 : pWOk 61 513 phbn_3 (bDec bZ pvn_3_0) pvn_3_5 := pChnN 61 pw_w3_3 bk_12
  rfl
private theorem pw_w3_5 : pWOk 71 513 phbn_3 (bDec bZ pvn_3_0) pvn_3_o := pChnN 71 pw_w3_4 bk_13
  rfl
/-- Certified `T_16` walk `rkmWalkHiHiB_m128_r512_s3` (`FindAllJohnsonRampKickMuxHi128T5`). -/
theorem rkmWalkHiHiB_m128_r512_s3 :
    muxFastIterFullT16 71 513 rkmHbHiHiB_m128_r512_s3 rkmViHiHiB_m128_r512_s3 =
      rkmVoHiHiB_m128_r512_s3 :=
  bWalkBridge pw_w3_5 (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl bk_0))))) (rkmHd (rkmTl (rkmTl (rkmTl
    (rkmTl bk_1))))) (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl bk_2)))))
private theorem pw_w4_1 : pWOk 18 513 phbn_4 (bDec bZ pvn_4_0) pvn_4_2 := pChnN 18
  (bSlSndNN bk_14) bk_15 rfl
private theorem pw_w4_2 : pWOk 27 513 phbn_4 (bDec bZ pvn_4_0) pvn_4_3 := pChnN 27 pw_w4_1 bk_16
  rfl
private theorem pw_w4_3 : pWOk 36 513 phbn_4 (bDec bZ pvn_4_0) pvn_4_4 := pChnN 36 pw_w4_2 bk_17
  rfl
private theorem pw_w4_4 : pWOk 45 513 phbn_4 (bDec bZ pvn_4_0) pvn_4_5 := pChnN 45 pw_w4_3 bk_18
  rfl
private theorem pw_w4_5 : pWOk 53 513 phbn_4 (bDec bZ pvn_4_0) pvn_4_6 := pChnN 53 pw_w4_4 bk_19
  rfl
private theorem pw_w4_6 : pWOk 61 513 phbn_4 (bDec bZ pvn_4_0) pvn_4_7 := pChnN 61 pw_w4_5 bk_20
  rfl
private theorem pw_w4_7 : pWOk 69 513 phbn_4 (bDec bZ pvn_4_0) pvn_4_8 := pChnN 69 pw_w4_6 bk_21
  rfl
private theorem pw_w4_8 : pWOk 77 513 phbn_4 (bDec bZ pvn_4_0) pvn_4_o := pChnN 77 pw_w4_7 bk_22
  rfl
/-- Certified `T_16` walk `rkmWalkHiHiB_m128_r512_s4a` (`FindAllJohnsonRampKickMuxHi128T5`). -/
theorem rkmWalkHiHiB_m128_r512_s4a :
    muxFastIterFullT16 77 513 rkmHbHiHiB_m128_r512_s4 rkmViHiHiB_m128_r512_s4 =
      rkmMidHiHiB_m128_r512_s4a :=
  bWalkBridge pw_w4_8 (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl bk_0)))))) (rkmHd (rkmTl (rkmTl
    (rkmTl (rkmTl (rkmTl bk_1)))))) (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl (rkmTl bk_2))))))
end
end QuantumComputation.Specs.DickeSol
