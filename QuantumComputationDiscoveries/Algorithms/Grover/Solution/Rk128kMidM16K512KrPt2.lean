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
# `(16, 512)` `RampKick128k` Krotov Part 2 (`Rk128kMidM16K512KrPt2`)

Certifies Slice 2 (`r = 512` segments `82..107`, `26` segments, `443,392` F1272 /
`444,258 <= 450,000` Horner coord-ops, `lTableMax = 62`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kMidM16K512KrPt2

@[expose] public section

open QuantumComputation.Specs.DickeSol

/-- Segments `82..107` (`26` segments) of `(16, 512)` `r = 512` at `lTableMax = 62`. -/
def mm16k512krS2Segs : List Rkm128kSeg := [
  ⟨53, 417387, 2, 26,
    rkm128kMask56 511 [29121543839984317, 58232923006432872, 63397065217226128, 47027492665286951,
     3377998431622947, 146340530074826, 774093534036094, 8796093022220, 56647389364094976, 95]⟩,
  ⟨54, 412677, 2, 26,
    rkm128kMask56 513 [3106962615686078, 44203567248828502, 22746677088758222, 30953759522735200,
     37410063124423841, 54111160237897785, 10125817664005391, 2251954432509025, 59745262830092288,
     352]⟩,
  ⟨55, 407946, 2, 26,
    rkm128kMask56 512 [70969016996053143, 28217265368236924, 8789469243894450, 7951713249512028,
     26302718650146936, 41106496343785680, 4517082705690917, 18014948265484288, 15080970206052864,
     221]⟩,
  ⟨56, 405267, 2, 26,
    rkm128kMask56 513 [2640447048237738, 59839352673587976, 38698471796643971, 6752258025037210,
     59571594417426726, 14932873254730324, 71133138518046532, 1266637443336271, 18093563346698272,
     280]⟩,
  ⟨56, 263893, 1, 30,
    rkm128kMask56 510 [2139620705861815, 28747133282651408, 61223046639346967, 39210950815508096,
     54541566428957600, 12129141477377709, 45054451783041717, 562950767250625, 36611538181685376,
     48]⟩,
  ⟨56, 277770, 1, 31,
    rkm128kMask56 513 [47498679116033866, 47169302498312472, 35169312856915596, 57004973401636367,
     1114225682804926, 27372342248266055, 2508160558667376, 8590094741, 36169534775754752, 452]⟩,
  ⟨56, 278027, 1, 31,
    rkm128kMask56 513 [68144276930307934, 64946865724854267, 69803597264493183, 19231483369222638,
     46170736835310584, 9297608034124808, 36071815700811424, 456885600786, 282574488371200, 269]⟩,
  ⟨56, 275408, 1, 31,
    rkm128kMask56 511 [19776501222732170, 55053750886280835, 62021018260273405, 4999839040581893,
     28046274249896126, 47517086080266296, 50207800305293236, 6767285947684, 18648825308643328,
     90]⟩,
  ⟨56, 278633, 1, 31,
    rkm128kMask56 511 [12869628711154576, 37193194868752519, 24705736798236759, 8306823075205231,
     12559770816220106, 5695680547696, 9221879172726789, 54997165867024, 158604552310784, 68]⟩,
  ⟨56, 277231, 1, 31,
    rkm128kMask56 511 [6749518168023102, 1709418416567260, 67839216141611144, 16408166632523047,
     13524828846736811, 13511627944609689, 19604879690375522, 1690241800735939, 4503603922337792,
     124]⟩,
  ⟨56, 278247, 1, 31,
    rkm128kMask56 512 [54068823593803676, 31389836805129519, 65073839561754212, 27260195636526055,
     43351217970582928, 9010500919579796, 123506916501066, 27030463158556226, 0, 160]⟩,
  ⟨56, 277965, 1, 31,
    rkm128kMask56 513 [7308181051000341, 27518303922512386, 64760962685117668, 43557969570298881,
     60925475023318686, 7893067287519481, 23783587440476904, 18633043464950665, 6, 276]⟩,
  ⟨56, 277818, 1, 30,
    rkm128kMask56 513 [2663420150834431, 51060762046641598, 37223880688239559, 17131381383519375,
     27769852011504598, 9078024100248130, 13212959872026, 70440452227339, 2251799813685346, 256]⟩,
  ⟨56, 274468, 1, 30,
    rkm128kMask56 510 [21251491315220350, 44342185023251330, 37649505962314517, 54926307319297080,
     71238464436078447, 11690471965885996, 5075413326560275, 6902200562155533, 5070947627303776,
     53]⟩,
  ⟨56, 277734, 1, 30,
    rkm128kMask56 509 [18849122725944280, 7788390772441001, 7989912864220713, 57381006309058170,
     11180946898229891, 167272973069056, 1549954892303874, 149693772599524, 8796093035016, 16]⟩,
  ⟨56, 274276, 1, 30,
    rkm128kMask56 513 [12654160570435663, 69244583169559574, 37876742873775625, 67812463092182840,
     55409730587825471, 1247286788981727, 27268211281559728, 5840585386035361, 18155135997929993,
     500]⟩,
  ⟨56, 273146, 1, 30,
    rkm128kMask56 512 [24543134330116485, 10114610550112578, 36421604470747006, 1702986602268537,
     25122221839350305, 9580836756345387, 75007848894857, 14083954232955712, 35184372622914,
     160]⟩,
  ⟨56, 274670, 1, 30,
    rkm128kMask56 513 [58018419693408358, 71548842536956742, 56928999694755204, 25759953233002327,
     4945134615822316, 48321628227636121, 5681300622214531, 3624265598790025, 4573968377333036,
     256]⟩,
  ⟨57, 269071, 1, 30,
    rkm128kMask56 513 [41048673658371856, 70307245039038807, 7249542518017783, 41851695841347085,
     55034632512471096, 15008403320758051, 4513418174500996, 36068379524610049, 35729426, 464]⟩,
  ⟨58, 265599, 1, 30,
    rkm128kMask56 509 [54461127383244767, 5182308927727281, 1707270885805570, 28376109183630377,
     16755015314971087, 36171833432119563, 238116410838234, 59224324217114656, 1125900217262094,
     16]⟩,
  ⟨59, 254609, 1, 29,
    rkm128kMask56 513 [3447988266973645, 38811416276458228, 6012160121662849, 22526382593543214,
     54194035079007963, 8552100904646305, 9221640838676742, 442081520717860, 2375815434, 384]⟩,
  ⟨59, 251789, 1, 29,
    rkm128kMask56 513 [4622260197407672, 39935657935190031, 71755992692364224, 70423968728506876,
     32682013758213258, 14024334436158356, 61520753732911173, 37160550454905549, 13222062730,
     416]⟩,
  ⟨60, 249596, 1, 29,
    rkm128kMask56 513 [689690236633251, 10828863365397704, 39098524534044405, 60236220939188866,
     30891923642149150, 2587702499944114, 18129587552067714, 55380481370726480, 81948419232,
     416]⟩,
  ⟨60, 238913, 1, 28,
    rkm128kMask56 485 [16841690056293041, 17876768835257628, 24728961298558193, 38233713525202122,
     70021950480101417, 7350261370097283, 6768155036535954, 21091214341784974, 69056792615]⟩,
  ⟨60, 240912, 1, 28,
    rkm128kMask56 513 [62758804955230573, 44404876800648501, 35008858778148236, 70157378999815076,
     9542790633624591, 768156358042040, 23297842077728905, 3673488767501461, 1519009473281, 328]⟩,
  ⟨61, 238833, 1, 28,
    rkm128kMask56 512 [7404392627946032, 5924418286752215, 48278457116191164, 33161264880046201,
     17853241906252267, 23087996324574723, 8792127050752015, 62327541773650002, 106918119644,
     192]⟩]
/-- Entry `lPrev` (`53`) entering `mm16k512krS2Segs` after `segs 0..81`. -/
def mm16k512krS2LIn : ℕ := 53
/-- Entry `dCur` (`512`) entering `mm16k512krS2Segs` after `segs 0..81`. -/
def mm16k512krS2DCurIn : ℕ := 512
/-- Entry `accPad` entering `mm16k512krS2Segs` after `segs 0..81`. -/
def mm16k512krS2PadIn : ℕ := 766172526
/-- Slice `0` (`64` entries) of `mm16k512krS2VecIn`. -/
def mm16k512krS2VecIn0 : List ℤ :=
  [Int.negSucc 25879693, Int.ofNat 72302561, Int.ofNat 302827352, Int.ofNat 80866118,
   Int.ofNat 25272983, Int.negSucc 20026342, Int.ofNat 174141308, Int.ofNat 198240811,
   Int.negSucc 400504222, Int.ofNat 367412143, Int.ofNat 340777222, Int.negSucc 64467009,
   Int.ofNat 62572563, Int.ofNat 161132744, Int.negSucc 288565870, Int.negSucc 63053385,
   Int.negSucc 588216700, Int.negSucc 665824020, Int.negSucc 529124939, Int.negSucc 1294052884,
   Int.negSucc 446461827, Int.negSucc 166959537, Int.negSucc 539036513, Int.ofNat 888155494,
   Int.ofNat 196128916, Int.ofNat 21303913, Int.ofNat 532844710, Int.ofNat 1663436096,
   Int.negSucc 513484361, Int.negSucc 1192359653, Int.ofNat 392722766, Int.negSucc 1454406145,
   Int.ofNat 1145293294, Int.negSucc 1902417168, Int.negSucc 111285210, Int.negSucc 558878905,
   Int.ofNat 577019539, Int.ofNat 548187097, Int.ofNat 733090200, Int.negSucc 1899567147,
   Int.ofNat 392266505, Int.ofNat 494108643, Int.ofNat 885939801, Int.ofNat 130620156,
   Int.ofNat 846957387, Int.negSucc 1634323621, Int.negSucc 3568743729, Int.negSucc 1394510646,
   Int.ofNat 3343578380, Int.ofNat 550462062, Int.ofNat 2800682767, Int.negSucc 766981676,
   Int.negSucc 544589802, Int.negSucc 2361650112, Int.negSucc 1949426764, Int.negSucc 1507495962,
   Int.negSucc 1507736008, Int.negSucc 286969355, Int.negSucc 1038798983, Int.negSucc 465929300,
   Int.negSucc 1778791841, Int.ofNat 2074143420, Int.ofNat 850838557, Int.ofNat 4156467137]
/-- Slice `1` (`64` entries) of `mm16k512krS2VecIn`. -/
def mm16k512krS2VecIn1 : List ℤ :=
  [Int.ofNat 4373765632, Int.ofNat 4389373292, Int.ofNat 2744515139, Int.ofNat 9279907265,
   Int.ofNat 7290130345, Int.ofNat 6099170927, Int.ofNat 5170679388, Int.ofNat 2785242567,
   Int.ofNat 2887272669, Int.ofNat 316362050, Int.negSucc 6843361280, Int.negSucc 3643478525,
   Int.negSucc 16045256731, Int.negSucc 9849158550, Int.negSucc 6840160012,
   Int.negSucc 3660573105, Int.negSucc 623274924, Int.ofNat 781563984, Int.ofNat 3474971329,
   Int.ofNat 4018062952, Int.ofNat 2473327445, Int.ofNat 2825696973, Int.ofNat 9664907928,
   Int.negSucc 1308051676, Int.negSucc 7673077410, Int.negSucc 15271108266, Int.ofNat 2238829364,
   Int.ofNat 3265085147, Int.negSucc 6584129039, Int.negSucc 1788088998, Int.negSucc 10543498634,
   Int.negSucc 2077407206, Int.negSucc 462340633, Int.negSucc 12314885650, Int.negSucc 7019187178,
   Int.ofNat 21969295619, Int.ofNat 9536745431, Int.negSucc 8213866598, Int.ofNat 2180674412,
   Int.ofNat 21402171779, Int.ofNat 20259663565, Int.ofNat 26580912891, Int.ofNat 17582608859,
   Int.ofNat 765949697, Int.negSucc 7531494008, Int.negSucc 12487013845, Int.negSucc 29722597059,
   Int.negSucc 20872200889, Int.negSucc 22822351388, Int.negSucc 20343994231,
   Int.negSucc 24929982667, Int.ofNat 21247647504, Int.ofNat 8662860999, Int.negSucc 36474107800,
   Int.negSucc 54290483365, Int.ofNat 14502705246, Int.ofNat 8026539910, Int.negSucc 66536404823,
   Int.negSucc 75705891109, Int.ofNat 4873241486, Int.ofNat 7216252393, Int.ofNat 293204369,
   Int.ofNat 55621650752, Int.ofNat 35470741005]
/-- Slice `2` (`64` entries) of `mm16k512krS2VecIn`. -/
def mm16k512krS2VecIn2 : List ℤ :=
  [Int.ofNat 37292563637, Int.ofNat 6342535829, Int.ofNat 5990368225, Int.negSucc 15417563475,
   Int.ofNat 11993549274, Int.negSucc 5383963853, Int.ofNat 46187293777, Int.ofNat 72688367523,
   Int.ofNat 162890830094, Int.negSucc 53217378131, Int.negSucc 54708581831,
   Int.negSucc 28549953243, Int.ofNat 4794090720, Int.ofNat 33351216522, Int.ofNat 65863362166,
   Int.ofNat 95932003394, Int.ofNat 14626926904, Int.negSucc 29565957215, Int.negSucc 6359171931,
   Int.negSucc 61158059979, Int.ofNat 31289806181, Int.negSucc 23080654976,
   Int.negSucc 104467733235, Int.negSucc 62874234254, Int.negSucc 54827172808,
   Int.negSucc 112111161336, Int.negSucc 121944301037, Int.negSucc 61729752268,
   Int.negSucc 20042599123, Int.negSucc 115619239547, Int.negSucc 84812515690,
   Int.negSucc 56102612390, Int.negSucc 143461329353, Int.negSucc 4058905607,
   Int.negSucc 7872244954, Int.negSucc 97165716255, Int.negSucc 16543999177,
   Int.ofNat 19382054205, Int.ofNat 189477263489, Int.ofNat 118831620199, Int.ofNat 4892804488,
   Int.ofNat 44902737353, Int.negSucc 3204553835, Int.ofNat 112030301128, Int.ofNat 93756511734,
   Int.ofNat 27373162890, Int.negSucc 105698353370, Int.ofNat 151943742821,
   Int.ofNat 143198596450, Int.ofNat 6508992110, Int.ofNat 158318735569, Int.ofNat 350998841735,
   Int.ofNat 185971644824, Int.ofNat 19877085072, Int.ofNat 125541688962, Int.negSucc 45266635465,
   Int.negSucc 62497053381, Int.negSucc 13687627655, Int.negSucc 90650392673,
   Int.ofNat 53765305699, Int.ofNat 73119240699, Int.ofNat 12669313268, Int.ofNat 68482214729,
   Int.ofNat 225235014556]
/-- Slice `3` (`64` entries) of `mm16k512krS2VecIn`. -/
def mm16k512krS2VecIn3 : List ℤ :=
  [Int.ofNat 269479829593, Int.ofNat 206973890928, Int.ofNat 423380420318, Int.ofNat 652788862827,
   Int.ofNat 313734913936, Int.negSucc 1446511582, Int.negSucc 318561050062,
   Int.negSucc 276346511223, Int.negSucc 145134043386, Int.ofNat 76069665618,
   Int.ofNat 146519497531, Int.ofNat 100312617706, Int.negSucc 377812479452,
   Int.ofNat 187221698967, Int.ofNat 84954317302, Int.negSucc 181674047744, Int.ofNat 1086642387,
   Int.negSucc 130728473178, Int.ofNat 64603983386, Int.negSucc 56253981412,
   Int.negSucc 75022231832, Int.negSucc 428676604683, Int.negSucc 387711955554,
   Int.negSucc 121230517025, Int.negSucc 354736557982, Int.negSucc 293691326672,
   Int.negSucc 238913622777, Int.negSucc 74729018683, Int.negSucc 12134496667,
   Int.ofNat 827214750210, Int.ofNat 1250932931808, Int.ofNat 1048129860879,
   Int.negSucc 532937490469, Int.negSucc 815915116690, Int.negSucc 254235453753,
   Int.ofNat 524272162145, Int.ofNat 512219126487, Int.negSucc 267091698843,
   Int.ofNat 426331120050, Int.ofNat 271422660316, Int.ofNat 493137787732,
   Int.ofNat 1031428888087, Int.ofNat 695060604356, Int.negSucc 750087244320,
   Int.negSucc 1551295607366, Int.negSucc 937266675485, Int.negSucc 401079949489,
   Int.ofNat 695445302969, Int.ofNat 205891570441, Int.ofNat 734539336106,
   Int.ofNat 1789734504502, Int.ofNat 1467099273931, Int.ofNat 1629438897199,
   Int.negSucc 1868167632, Int.negSucc 763633471331, Int.negSucc 1170096894630,
   Int.negSucc 229578330218, Int.negSucc 712164314848, Int.negSucc 1718088166600,
   Int.negSucc 961190269588, Int.negSucc 955899029316, Int.negSucc 687060256608,
   Int.negSucc 563317313731, Int.ofNat 420482846946]
/-- Slice `4` (`64` entries) of `mm16k512krS2VecIn`. -/
def mm16k512krS2VecIn4 : List ℤ :=
  [Int.negSucc 918140897422, Int.negSucc 337852638481, Int.ofNat 1052756767971,
   Int.negSucc 1435632478630, Int.ofNat 2394151648889, Int.negSucc 561597991948,
   Int.ofNat 15583868837, Int.ofNat 273470782435, Int.ofNat 2949918571337,
   Int.ofNat 2260281735930, Int.ofNat 3788686954898, Int.ofNat 4929914887712,
   Int.ofNat 5956907528206, Int.ofNat 5638811895903, Int.ofNat 7140337634752,
   Int.ofNat 5094501594438, Int.ofNat 1425050566877, Int.negSucc 2194023199414,
   Int.negSucc 3305700865289, Int.negSucc 514813936386, Int.ofNat 1876532230353,
   Int.ofNat 4902148847012, Int.negSucc 1192516254386, Int.negSucc 3428061754753,
   Int.negSucc 1642328096057, Int.ofNat 3278637144433, Int.ofNat 1750927471948,
   Int.negSucc 298386635526, Int.ofNat 3255925494617, Int.ofNat 1374218147441,
   Int.ofNat 822779703833, Int.ofNat 2155286016893, Int.ofNat 443218472259,
   Int.negSucc 3447430930905, Int.negSucc 4628601268842, Int.negSucc 5607127731747,
   Int.ofNat 1932319968013, Int.negSucc 5062507137493, Int.negSucc 7899615180620,
   Int.ofNat 475929498025, Int.ofNat 4145033748648, Int.negSucc 3513302276931,
   Int.ofNat 828541958811, Int.negSucc 541913035454, Int.ofNat 1517518504476,
   Int.ofNat 496591790056, Int.ofNat 2211891413379, Int.negSucc 1356423787830,
   Int.ofNat 1314490778958, Int.ofNat 257438138489, Int.negSucc 983827547911,
   Int.ofNat 3302253225153, Int.negSucc 1563062559160, Int.negSucc 2054720096341,
   Int.ofNat 560771949967, Int.ofNat 308477285868, Int.ofNat 1722161873101,
   Int.negSucc 3148316033340, Int.negSucc 996553767950, Int.negSucc 4333691642175,
   Int.negSucc 3076277110373, Int.negSucc 5044436793862, Int.negSucc 8894729157042,
   Int.negSucc 2023267502786]
/-- Slice `5` (`64` entries) of `mm16k512krS2VecIn`. -/
def mm16k512krS2VecIn5 : List ℤ :=
  [Int.negSucc 2462215482162, Int.negSucc 203249979460, Int.negSucc 4238728406914,
   Int.negSucc 8920625283100, Int.negSucc 2985335652316, Int.negSucc 372294917992,
   Int.negSucc 3644791394047, Int.negSucc 5776689455272, Int.negSucc 1802458491927,
   Int.negSucc 1433964799966, Int.negSucc 701965266328, Int.negSucc 2252818823709,
   Int.ofNat 1556032958576, Int.negSucc 3261792852871, Int.ofNat 2826830253179,
   Int.ofNat 8195250363877, Int.ofNat 2270406058845, Int.ofNat 2201344110751,
   Int.ofNat 913851528279, Int.ofNat 2348343377549, Int.negSucc 5791522246882,
   Int.negSucc 5888362287085, Int.ofNat 1149831025247, Int.ofNat 1331977909508,
   Int.negSucc 7441028864106, Int.negSucc 2890906893059, Int.ofNat 1217102592044,
   Int.negSucc 3593547027501, Int.ofNat 78162368983, Int.negSucc 1501886840263,
   Int.negSucc 6229131183906, Int.ofNat 8103700048598, Int.ofNat 440111648933,
   Int.ofNat 5222674298201, Int.ofNat 6479387984162, Int.negSucc 2336399575011,
   Int.negSucc 2767141645561, Int.ofNat 39649878087, Int.ofNat 9344012674431,
   Int.negSucc 277729520519, Int.negSucc 10901527359506, Int.negSucc 10235788687059,
   Int.negSucc 3607661976826, Int.ofNat 1540920300565, Int.negSucc 5557435635053,
   Int.ofNat 2423013138900, Int.ofNat 1881063870353, Int.negSucc 7313463015712,
   Int.negSucc 2613666042436, Int.ofNat 8982347724771, Int.negSucc 1864730597446,
   Int.negSucc 3244229229463, Int.negSucc 5312937613207, Int.negSucc 6726432485182,
   Int.negSucc 6011355413072, Int.negSucc 3078297341094, Int.ofNat 714625130028,
   Int.ofNat 7535492113259, Int.ofNat 3663939223110, Int.ofNat 2441577729335,
   Int.negSucc 7688432236935, Int.negSucc 10893868406251, Int.ofNat 3436324024320,
   Int.ofNat 2175738572027]
/-- Slice `6` (`64` entries) of `mm16k512krS2VecIn`. -/
def mm16k512krS2VecIn6 : List ℤ :=
  [Int.ofNat 4800297337879, Int.ofNat 8045934483837, Int.ofNat 11840778362435,
   Int.ofNat 17378990691540, Int.ofNat 13203615535948, Int.ofNat 28767599273990,
   Int.ofNat 84487678228397, Int.ofNat 137595110288649, Int.ofNat 198681384840406,
   Int.ofNat 257386627444608, Int.ofNat 297532687891082, Int.ofNat 324144360472089,
   Int.ofNat 343264284705213, Int.ofNat 347241297471419, Int.ofNat 330409208182523,
   Int.ofNat 300078447549052, Int.ofNat 268337189924752, Int.ofNat 238714983869814,
   Int.ofNat 208227858438842, Int.ofNat 172062325243248, Int.ofNat 131781073661224,
   Int.ofNat 92715276109618, Int.ofNat 59646897775396, Int.ofNat 35273274496653,
   Int.ofNat 19473294696625, Int.ofNat 10148372989077, Int.ofNat 4961781696602,
   Int.negSucc 2242891342579, Int.ofNat 945719822434, Int.ofNat 403913599090,
   Int.ofNat 206520586171, Int.ofNat 135797265020, Int.negSucc 100559899316,
   Int.ofNat 73277790132, Int.ofNat 49795872086, Int.ofNat 31208933246, Int.ofNat 18147732395,
   Int.ofNat 9956263227, Int.ofNat 5286083218, Int.ofNat 2790840678, Int.ofNat 1489715355,
   Int.ofNat 802640393, Int.ofNat 430432043, Int.ofNat 226585402, Int.ofNat 116360276,
   Int.ofNat 58388451, Int.ofNat 28792977, Int.ofNat 14030088, Int.ofNat 6771027,
   Int.ofNat 3232183, Int.ofNat 1520731, Int.ofNat 702558, Int.ofNat 317835, Int.ofNat 140632,
   Int.ofNat 60858, Int.ofNat 25774, Int.ofNat 10685, Int.negSucc 4331, Int.ofNat 1710,
   Int.ofNat 653, Int.ofNat 235, Int.ofNat 76, Int.ofNat 21, Int.ofNat 4]
/-- Slice `7` (`64` entries) of `mm16k512krS2VecIn`. -/
def mm16k512krS2VecIn7 : List ℤ :=
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
/-- Slice `8` (`1` entries) of `mm16k512krS2VecIn`. -/
def mm16k512krS2VecIn8 : List ℤ :=
  [Int.ofNat 0]
/-- Checkpoint fixed-point vector entering `mm16k512krS2Segs` (`513` entries). -/
def mm16k512krS2VecIn : List ℤ :=
  mm16k512krS2VecIn0 ++ (
    mm16k512krS2VecIn1 ++ (
      mm16k512krS2VecIn2 ++ (
        mm16k512krS2VecIn3 ++ (
          mm16k512krS2VecIn4 ++ (
          mm16k512krS2VecIn5 ++ (
          mm16k512krS2VecIn6 ++ (
          mm16k512krS2VecIn7 ++ (
          mm16k512krS2VecIn8))))))))
/-- Exit `lPrev` (`61`) leaving `mm16k512krS2Segs` after `segs 82..107`. -/
def mm16k512krS2LOut : ℕ := 61
/-- Exit `dCur` (`512`) leaving `mm16k512krS2Segs` after `segs 82..107`. -/
def mm16k512krS2DCurOut : ℕ := 512
/-- Exit `accPad` leaving `mm16k512krS2Segs` after `segs 82..107`. -/
def mm16k512krS2PadOut : ℕ := 1009878088
/-- Slice `0` (`64` entries) of `mm16k512krS2Vec`. -/
def mm16k512krS2Vec0 : List ℤ :=
  [Int.ofNat 5572407, Int.negSucc 10824390, Int.ofNat 3796045, Int.negSucc 4290604,
   Int.negSucc 10926905, Int.negSucc 8106974, Int.ofNat 1873619, Int.negSucc 13885605,
   Int.ofNat 8053946, Int.ofNat 6981295, Int.negSucc 7798751, Int.negSucc 24831125,
   Int.negSucc 36015694, Int.negSucc 15970565, Int.negSucc 45352494, Int.negSucc 43494230,
   Int.negSucc 21029325, Int.ofNat 65778875, Int.ofNat 60493315, Int.ofNat 27175036,
   Int.ofNat 45581982, Int.ofNat 1366992, Int.negSucc 51817568, Int.ofNat 20207069,
   Int.ofNat 60531194, Int.ofNat 148003017, Int.ofNat 149120009, Int.ofNat 152474919,
   Int.ofNat 116634029, Int.ofNat 34433256, Int.negSucc 2192736, Int.negSucc 51403408,
   Int.ofNat 54649260, Int.ofNat 117378799, Int.negSucc 112497076, Int.ofNat 159045903,
   Int.ofNat 139690626, Int.ofNat 257567678, Int.ofNat 90956220, Int.ofNat 107987002,
   Int.ofNat 77501959, Int.ofNat 179515874, Int.ofNat 477509134, Int.ofNat 403711030,
   Int.ofNat 9371145, Int.ofNat 153503848, Int.ofNat 233310906, Int.negSucc 141433486,
   Int.negSucc 52728783, Int.negSucc 33064471, Int.ofNat 333010408, Int.negSucc 275759610,
   Int.negSucc 186452085, Int.ofNat 297067219, Int.ofNat 76433899, Int.ofNat 241540908,
   Int.negSucc 50787651, Int.negSucc 281341181, Int.negSucc 388678120, Int.negSucc 118302449,
   Int.ofNat 127367326, Int.ofNat 9850908, Int.negSucc 576897008, Int.negSucc 163478794]
/-- Slice `1` (`64` entries) of `mm16k512krS2Vec`. -/
def mm16k512krS2Vec1 : List ℤ :=
  [Int.ofNat 245282684, Int.negSucc 716798977, Int.negSucc 635972523, Int.negSucc 224229025,
   Int.negSucc 150415681, Int.negSucc 706940904, Int.negSucc 31784113, Int.negSucc 310143881,
   Int.ofNat 255747939, Int.ofNat 612925423, Int.negSucc 170492191, Int.negSucc 1095917815,
   Int.negSucc 1994904005, Int.negSucc 1953262313, Int.negSucc 1067456104, Int.negSucc 292393110,
   Int.ofNat 234425485, Int.ofNat 1374989549, Int.ofNat 649669476, Int.ofNat 277425977,
   Int.ofNat 483284910, Int.ofNat 1072710543, Int.negSucc 544573781, Int.negSucc 112096559,
   Int.ofNat 514748609, Int.ofNat 875146432, Int.negSucc 510976541, Int.negSucc 90795353,
   Int.negSucc 1713835094, Int.negSucc 1009747332, Int.negSucc 2271299677, Int.negSucc 3096396482,
   Int.negSucc 3746108107, Int.negSucc 1006038403, Int.ofNat 768002842, Int.ofNat 1786892171,
   Int.ofNat 514474799, Int.negSucc 1052435879, Int.ofNat 1300082791, Int.ofNat 2169765392,
   Int.ofNat 283902118, Int.ofNat 1238449462, Int.ofNat 173637753, Int.negSucc 3547344625,
   Int.ofNat 6155943549, Int.negSucc 2554895111, Int.ofNat 231513541, Int.negSucc 940298192,
   Int.ofNat 2089869097, Int.ofNat 1595685977, Int.negSucc 1458657740, Int.negSucc 1221789985,
   Int.negSucc 1125646903, Int.ofNat 2666696866, Int.ofNat 1351736971, Int.ofNat 2690534108,
   Int.ofNat 1841731024, Int.ofNat 3646520522, Int.ofNat 2727970681, Int.negSucc 1610519413,
   Int.negSucc 5122726497, Int.negSucc 7792179448, Int.ofNat 4444712588, Int.ofNat 7774556687]
/-- Slice `2` (`64` entries) of `mm16k512krS2Vec`. -/
def mm16k512krS2Vec2 : List ℤ :=
  [Int.negSucc 989121324, Int.negSucc 1199426520, Int.negSucc 2423956030, Int.ofNat 2580547291,
   Int.ofNat 8665628314, Int.ofNat 5257667558, Int.ofNat 4197539065, Int.negSucc 7503503619,
   Int.negSucc 3568442718, Int.negSucc 5905445529, Int.negSucc 1613860721, Int.ofNat 748301594,
   Int.ofNat 5763849250, Int.negSucc 89406472, Int.ofNat 3731070443, Int.negSucc 9702357857,
   Int.negSucc 11374125287, Int.negSucc 16374378355, Int.negSucc 8906443760, Int.ofNat 5387730911,
   Int.negSucc 1408992257, Int.negSucc 4079064933, Int.ofNat 1264248459, Int.negSucc 3687828706,
   Int.ofNat 5403592906, Int.negSucc 11247481694, Int.ofNat 4524452589, Int.negSucc 556012353,
   Int.negSucc 9031549059, Int.negSucc 10284327711, Int.ofNat 1365571650, Int.ofNat 16970126437,
   Int.ofNat 10298918197, Int.ofNat 19563574755, Int.ofNat 2349877327, Int.negSucc 2228200028,
   Int.negSucc 9213125032, Int.ofNat 10200146196, Int.negSucc 7515058879, Int.ofNat 25574330846,
   Int.ofNat 13201462780, Int.ofNat 3491024380, Int.ofNat 9969045834, Int.negSucc 3027805668,
   Int.ofNat 6675266243, Int.ofNat 24112209450, Int.ofNat 22575968500, Int.ofNat 16734723565,
   Int.negSucc 4197132627, Int.negSucc 2749089452, Int.ofNat 10552430013, Int.ofNat 9689378838,
   Int.ofNat 1563560974, Int.ofNat 19043696013, Int.negSucc 26482068384, Int.ofNat 18452927421,
   Int.ofNat 8166234880, Int.ofNat 30166106890, Int.ofNat 1100184556, Int.ofNat 1826488414,
   Int.negSucc 5622751216, Int.ofNat 18610750327, Int.ofNat 23419096244, Int.ofNat 12875937133]
/-- Slice `3` (`64` entries) of `mm16k512krS2Vec`. -/
def mm16k512krS2Vec3 : List ℤ :=
  [Int.negSucc 17729101856, Int.negSucc 19887857876, Int.negSucc 1148984092,
   Int.ofNat 14405584027, Int.negSucc 31237014621, Int.negSucc 59751589862,
   Int.negSucc 11207497150, Int.negSucc 29475820535, Int.ofNat 4579694297, Int.ofNat 36347568324,
   Int.negSucc 5046845481, Int.ofNat 18944110613, Int.negSucc 12346036450, Int.ofNat 32982651590,
   Int.ofNat 17432664413, Int.ofNat 29802952762, Int.ofNat 46570596561, Int.ofNat 66456864163,
   Int.ofNat 53200442311, Int.ofNat 12489496792, Int.ofNat 15823209878, Int.ofNat 36605919139,
   Int.negSucc 29761564618, Int.negSucc 53454592103, Int.negSucc 43306051492,
   Int.negSucc 21133548968, Int.negSucc 22853388544, Int.negSucc 52936882208,
   Int.negSucc 42969916851, Int.negSucc 70732546592, Int.negSucc 18561093635,
   Int.negSucc 14665443592, Int.ofNat 28667095649, Int.negSucc 3473869877, Int.ofNat 35275727948,
   Int.negSucc 6806502906, Int.ofNat 97064858882, Int.negSucc 108761475319,
   Int.negSucc 44958020436, Int.negSucc 37491274404, Int.ofNat 118425580648,
   Int.ofNat 204451120554, Int.ofNat 238466629343, Int.ofNat 124823241717,
   Int.negSucc 121251715810, Int.negSucc 144159606015, Int.negSucc 85057528749,
   Int.ofNat 26019615333, Int.ofNat 148291760188, Int.negSucc 50879481538,
   Int.negSucc 32470212713, Int.negSucc 203150458969, Int.ofNat 80902675019,
   Int.negSucc 45616596004, Int.negSucc 60158165786, Int.negSucc 66500183339,
   Int.negSucc 74041939651, Int.negSucc 133574568118, Int.negSucc 48159499044,
   Int.negSucc 38211674863, Int.ofNat 19479656776, Int.ofNat 100315648713,
   Int.negSucc 13668934144, Int.negSucc 21086408937]
/-- Slice `4` (`64` entries) of `mm16k512krS2Vec`. -/
def mm16k512krS2Vec4 : List ℤ :=
  [Int.negSucc 110703179954, Int.ofNat 40851570074, Int.ofNat 114787191040, Int.ofNat 35285470770,
   Int.ofNat 75382616326, Int.ofNat 246323859359, Int.negSucc 113362152632,
   Int.negSucc 122639330880, Int.negSucc 100218721732, Int.negSucc 180873280893,
   Int.ofNat 172455004888, Int.ofNat 131609082903, Int.ofNat 239656686034,
   Int.negSucc 79726352313, Int.ofNat 59814384129, Int.ofNat 60089005911, Int.negSucc 26375655920,
   Int.negSucc 91982614557, Int.negSucc 13405042481, Int.negSucc 4205659941,
   Int.negSucc 251706611259, Int.negSucc 213428952927, Int.negSucc 211218278861,
   Int.negSucc 244166931578, Int.negSucc 65434652119, Int.negSucc 71895844573,
   Int.negSucc 133287731999, Int.negSucc 513557009236, Int.negSucc 438132482275,
   Int.negSucc 755084865657, Int.negSucc 118763162333, Int.negSucc 360023961960,
   Int.negSucc 516781063383, Int.negSucc 131758147631, Int.ofNat 91302633989,
   Int.negSucc 318328450292, Int.negSucc 570074538640, Int.negSucc 387542642992,
   Int.ofNat 22827572208, Int.negSucc 684429044271, Int.negSucc 588292992806,
   Int.negSucc 572842706967, Int.negSucc 311975720599, Int.ofNat 215891424572,
   Int.ofNat 339937865675, Int.ofNat 109530791124, Int.negSucc 212582257031,
   Int.ofNat 815496971644, Int.ofNat 610325968681, Int.negSucc 15403433876,
   Int.negSucc 265675037209, Int.negSucc 150088732686, Int.ofNat 792142880359,
   Int.negSucc 51192428608, Int.ofNat 380620859665, Int.negSucc 324224265882,
   Int.negSucc 508319429847, Int.negSucc 596074604893, Int.ofNat 91001174941,
   Int.ofNat 383215053270, Int.ofNat 276611936326, Int.ofNat 425535658995,
   Int.negSucc 539354680020, Int.negSucc 1900662304339]
/-- Slice `5` (`64` entries) of `mm16k512krS2Vec`. -/
def mm16k512krS2Vec5 : List ℤ :=
  [Int.negSucc 1740409312610, Int.negSucc 607782466438, Int.negSucc 676043372952,
   Int.negSucc 657995102131, Int.ofNat 905842438654, Int.ofNat 631252259071,
   Int.ofNat 3893119738814, Int.ofNat 850033085237, Int.negSucc 1260223809679,
   Int.ofNat 665406787182, Int.ofNat 395161413125, Int.negSucc 2470724391190,
   Int.negSucc 163255330753, Int.negSucc 356933922698, Int.negSucc 891092957939,
   Int.negSucc 2095826964738, Int.negSucc 2978724072113, Int.negSucc 3528043863681,
   Int.negSucc 2726529795869, Int.negSucc 3473321462818, Int.ofNat 1286425530907,
   Int.ofNat 6299123110054, Int.ofNat 2423776393475, Int.ofNat 2479314497769,
   Int.ofNat 375622079259, Int.ofNat 5784624089302, Int.ofNat 5019178093728,
   Int.negSucc 3103169752012, Int.negSucc 3765748864214, Int.negSucc 4227038578950,
   Int.ofNat 8025209146313, Int.ofNat 8204739704100, Int.negSucc 755683665986,
   Int.ofNat 3951429456449, Int.negSucc 6325095065659, Int.negSucc 5533834964246,
   Int.ofNat 186046745772, Int.ofNat 1604866477498, Int.ofNat 3017193470254,
   Int.negSucc 7971228193311, Int.negSucc 6265470443941, Int.negSucc 458104249794,
   Int.negSucc 503759601731, Int.ofNat 2136747522551, Int.ofNat 5231946341205,
   Int.negSucc 847917032464, Int.negSucc 2731594489480, Int.ofNat 3570816207546,
   Int.ofNat 864104608948, Int.negSucc 2246197261797, Int.negSucc 323423421700,
   Int.ofNat 9452685055, Int.negSucc 1214420164964, Int.ofNat 671863324113,
   Int.ofNat 2483114210876, Int.ofNat 2794858673757, Int.ofNat 6193190457171,
   Int.ofNat 2531106612880, Int.ofNat 1802619754329, Int.negSucc 1056245736956,
   Int.negSucc 3720672083929, Int.negSucc 7765361935952, Int.negSucc 5530018196004,
   Int.negSucc 12474100363441]
/-- Slice `6` (`64` entries) of `mm16k512krS2Vec`. -/
def mm16k512krS2Vec6 : List ℤ :=
  [Int.negSucc 5582581562900, Int.ofNat 1839438054031, Int.negSucc 6234149056611,
   Int.ofNat 4602447331047, Int.ofNat 4833682667215, Int.negSucc 5274319884574,
   Int.negSucc 3202483264641, Int.ofNat 3964753854059, Int.ofNat 6177930857360,
   Int.ofNat 365536732352, Int.negSucc 3490248367266, Int.negSucc 921012428297,
   Int.negSucc 6527727780148, Int.negSucc 7455184536119, Int.ofNat 14705794599835,
   Int.negSucc 336529508087, Int.negSucc 4888368132611, Int.negSucc 16176453883800,
   Int.negSucc 6866440410054, Int.ofNat 2990195550406, Int.ofNat 13319293713589,
   Int.ofNat 14731770896960, Int.negSucc 6176281296895, Int.negSucc 10176420527504,
   Int.negSucc 13429748020364, Int.negSucc 9246970225003, Int.negSucc 526400517205,
   Int.ofNat 2091416358342, Int.ofNat 2716114794718, Int.negSucc 2901966574715,
   Int.negSucc 1689178640422, Int.negSucc 5500989656167, Int.negSucc 5307844178908,
   Int.ofNat 136248557135, Int.ofNat 3474086761098, Int.negSucc 7135571292483,
   Int.negSucc 3487571539925, Int.negSucc 5632685399628, Int.negSucc 6201281903244,
   Int.negSucc 8337107446640, Int.ofNat 2478452624374, Int.negSucc 11863871698657,
   Int.ofNat 2372872205641, Int.negSucc 6537602881434, Int.negSucc 7974225998496,
   Int.negSucc 5835975929551, Int.negSucc 4314227610697, Int.ofNat 5114736142034,
   Int.negSucc 4521181205975, Int.ofNat 6754717121056, Int.ofNat 3579785493058,
   Int.ofNat 57772757152, Int.negSucc 2346092168032, Int.ofNat 5755738229721,
   Int.ofNat 627125882946, Int.ofNat 1355002923541, Int.negSucc 5932612928270,
   Int.ofNat 9111731635889, Int.negSucc 7306169805981, Int.negSucc 11947304899557,
   Int.negSucc 12439529288966, Int.negSucc 15793935193924, Int.negSucc 11763800827785,
   Int.negSucc 7194811738890]
/-- Slice `7` (`64` entries) of `mm16k512krS2Vec`. -/
def mm16k512krS2Vec7 : List ℤ :=
  [Int.ofNat 11515005135356, Int.ofNat 7363691761327, Int.ofNat 1120809390315,
   Int.negSucc 2319784441135, Int.ofNat 2508245245271, Int.ofNat 2160264640956,
   Int.ofNat 5632161588871, Int.ofNat 5372729397116, Int.ofNat 7724125880585,
   Int.ofNat 13044040041957, Int.ofNat 5363875881322, Int.ofNat 16516303522504,
   Int.ofNat 15694646807273, Int.ofNat 7672937689229, Int.ofNat 5406928447956,
   Int.ofNat 3462889474361, Int.ofNat 3162124805250, Int.negSucc 2733801811057,
   Int.negSucc 5498898000697, Int.negSucc 3105457490714, Int.ofNat 9039736939889,
   Int.negSucc 1153433983322, Int.negSucc 3816127735821, Int.ofNat 5185965986392,
   Int.ofNat 23450443486724, Int.ofNat 8196259319115, Int.ofNat 4935106079961,
   Int.negSucc 15843486716605, Int.negSucc 5867601458298, Int.ofNat 8635480751979,
   Int.ofNat 1195950035378, Int.negSucc 18554653091589, Int.ofNat 14791295626602,
   Int.ofNat 11920623231771, Int.ofNat 3416424195996, Int.negSucc 1220596845752,
   Int.negSucc 21575860781305, Int.negSucc 5936946179542, Int.ofNat 31333912209077,
   Int.negSucc 28681880533949, Int.ofNat 1076937906100, Int.ofNat 936869132133,
   Int.negSucc 22127639336090, Int.ofNat 14939790966639, Int.ofNat 131302668376759,
   Int.ofNat 283576494831589, Int.ofNat 411378832214639, Int.ofNat 472572332552805,
   Int.ofNat 457978883781608, Int.ofNat 386477087419665, Int.ofNat 289126020744428,
   Int.ofNat 193826091798240, Int.ofNat 117234787160667, Int.ofNat 64259875364534,
   Int.ofNat 31994487599217, Int.ofNat 14465720691102, Int.ofNat 5921880477869,
   Int.ofNat 2169758040735, Int.ofNat 741764944382, Int.ofNat 165782361948, Int.ofNat 26295850874,
   Int.ofNat 4960495731, Int.negSucc 790231378, Int.negSucc 87752083]
/-- Slice `8` (`1` entries) of `mm16k512krS2Vec`. -/
def mm16k512krS2Vec8 : List ℤ :=
  [Int.ofNat 5225308]
/-- Checkpoint fixed-point vector exiting `mm16k512krS2Segs` (`513` entries). -/
def mm16k512krS2Vec : List ℤ :=
  mm16k512krS2Vec0 ++ (
    mm16k512krS2Vec1 ++ (
      mm16k512krS2Vec2 ++ (
        mm16k512krS2Vec3 ++ (
          mm16k512krS2Vec4 ++ (
          mm16k512krS2Vec5 ++ (
          mm16k512krS2Vec6 ++ (
          mm16k512krS2Vec7 ++ (
          mm16k512krS2Vec8))))))))

end

public section

open QuantumComputation.Specs.DickeSol

private abbrev s2P : ℕ → ℤ := Int.ofNat
private abbrev s2N : ℕ → ℤ := Int.negSucc
private theorem s2AndLeft {a b : Bool} (h : Bool.and a b = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl
private theorem s2AndRight {a b : Bool} (h : Bool.and a b = true) : b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => rfl
private def s2NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem s2Ble_le {a b : ℕ} (h : Nat.ble a b = true) : a ≤ b := by
  induction a generalizing b with
  | zero => exact Nat.zero_le _
  | succ a ih =>
    cases b with
    | zero => cases h
    | succ b => exact Nat.succ_le_succ (ih h)
private theorem s2NatEq_eq {x y : ℕ} (h : s2NatEq x y = true) : x = y :=
  Nat.le_antisymm (s2Ble_le (s2AndLeft h)) (s2Ble_le (s2AndRight h))
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
  | cons x _ ih =>
    cases ys with
    | nil => cases h
    | cons y _ =>
      dsimp only [s2IntListEq] at h
      cases hxy : s2IntEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (s2IntEq_eq hxy) (ih h)
private def s2StateEq (st1 st2 : ℕ × ℕ × ℕ × List ℤ) : Bool :=
  match st1, st2 with
  | (l1, d1, p1, v1), (l2, d2, p2, v2) =>
    Bool.and (s2NatEq l1 l2)
      (Bool.and (s2NatEq d1 d2) (Bool.and (s2NatEq p1 p2) (s2IntListEq v1 v2)))
private theorem s2StateEq_eq {st1 st2 : ℕ × ℕ × ℕ × List ℤ} (h : s2StateEq st1 st2 = true) :
    st1 = st2 := by
  rcases st1 with ⟨_, _, _, _⟩
  rcases st2 with ⟨_, _, _, _⟩
  dsimp only [s2StateEq] at h
  have h1 := s2AndLeft h
  have hr1 := s2AndRight h
  have h2 := s2AndLeft hr1
  have hr2 := s2AndRight hr1
  rw [s2NatEq_eq h1, s2NatEq_eq h2, s2NatEq_eq (s2AndLeft hr2), s2IntListEq_eq (s2AndRight hr2)]
private def s2RunAtEq (c : List Rkm128kSeg)
    (lI dI pI : ℕ) (vI : List ℤ) (lO dO pO : ℕ) (vO : List ℤ) : Bool :=
  s2StateEq (rkm128kRunSegs 16 62 512 c lI dI pI vI) (lO, dO, pO, vO)
private theorem s2RunStep {c rest : List Rkm128kSeg}
    {lI dI pI l1 d1 p1 : ℕ} {vI v1 : List ℤ} {stOut : ℕ × ℕ × ℕ × List ℤ}
    (h1 : s2RunAtEq c lI dI pI vI l1 d1 p1 v1 = true)
    (h2 : rkm128kRunSegs 16 62 512 rest l1 d1 p1 v1 = stOut) :
    rkm128kRunSegs 16 62 512 (c ++ rest) lI dI pI vI = stOut := by
  unfold s2RunAtEq at h1
  rw [rkm128kRunSegs_append]
  dsimp only
  rw [s2StateEq_eq h1]
  dsimp only
  exact h2
private theorem s2RunLast {c : List Rkm128kSeg}
    {lI dI pI lO dO pO : ℕ} {vI vO : List ℤ} (h : s2RunAtEq c lI dI pI vI lO dO pO vO = true) :
    rkm128kRunSegs 16 62 512 c lI dI pI vI = (lO, dO, pO, vO) := s2StateEq_eq h
private def s2Ch0 : List Rkm128kSeg := [
  ⟨53, 417387, 2, 26,
    rkm128kMask56 511 [29121543839984317, 58232923006432872, 63397065217226128, 47027492665286951,
     3377998431622947, 146340530074826, 774093534036094, 8796093022220, 56647389364094976, 95]⟩]
private def s2V0S0 : List ℤ :=
  [s2P 4929263, s2N 121860330, s2N 121021353, s2N 181094122, s2N 154082403, s2N 257987599,
   s2N 327906709, s2N 198360853, s2P 359058551, s2P 117307503, s2N 278819851, s2N 337799448,
   s2P 44768636, s2N 114226841, s2P 334531763, s2P 218150591, s2P 304527381, s2P 229999746,
   s2P 652952002, s2P 413453194, s2N 485626797, s2P 668185253, s2P 754530879, s2P 426818446,
   s2P 1045403838, s2P 1612105374, s2P 1831677383, s2P 1495843867, s2P 578789333, s2N 508134733,
   s2N 1067123274, s2N 1003053703, s2N 869292248, s2P 1014153262, s2P 568719675, s2N 915084573,
   s2P 130455230, s2P 77696223, s2P 633322118, s2P 1876035134, s2P 43160678, s2P 487940309,
   s2N 1334301274, s2N 2158387419, s2N 2018516418, s2P 1154733757, s2P 1202417929, s2P 392837943,
   s2N 2068896883, s2N 1962485524, s2P 1131097975, s2N 1605255150, s2N 3093957626, s2P 306653959,
   s2P 698166089, s2P 2946584089, s2P 696916562, s2P 1654231444, s2N 121722649, s2P 159564918,
   s2N 3479149560, s2P 265338971, s2P 1444474110, s2N 2357405787]
private def s2V0S1 : List ℤ :=
  [s2P 387617776, s2P 278657094, s2P 4542805654, s2P 1633731557, s2P 3005718624, s2N 5770079248,
   s2N 479859667, s2N 312334785, s2N 5278596552, s2N 4041964750, s2N 5734848374, s2P 7476505012,
   s2P 7550969764, s2P 3794062421, s2P 7080801253, s2P 2722723972, s2P 8542850187, s2P 2069116867,
   s2N 4980321920, s2N 8012805023, s2P 11354125643, s2P 5756209488, s2P 15680195747,
   s2P 1766983699, s2P 4237582394, s2N 4390979020, s2N 5824432918, s2N 6658009498, s2P 4840824049,
   s2P 12779982419, s2P 5740084993, s2P 11005484036, s2N 9281811714, s2N 10395728740,
   s2N 4455523300, s2N 14990689954, s2P 248689068, s2N 11656423680, s2P 11064623707,
   s2P 8785344814, s2N 16518213996, s2N 1394761607, s2N 516622735, s2N 13225577164,
   s2N 9534604928, s2N 3411714321, s2N 3644330543, s2N 14215211692, s2P 7154265199,
   s2P 29005244425, s2P 36799453547, s2P 6535306761, s2P 13962975191, s2P 8189118482,
   s2P 37418958526, s2P 72125681750, s2P 54647911187, s2P 6554355047, s2N 26443985625,
   s2N 42206763950, s2P 11236738565, s2P 30335953742, s2P 33249594073, s2N 39891689641]
private def s2V0S2 : List ℤ :=
  [s2N 21624149814, s2P 65997905763, s2N 37443725527, s2N 19698979536, s2P 75139526810,
   s2N 680909765, s2P 50259906216, s2P 13193850304, s2P 5529649571, s2P 36144845872,
   s2P 103154165625, s2N 41263642483, s2N 59534206890, s2N 5259548205, s2P 5454946727,
   s2N 89184942659, s2N 108194831593, s2N 35304549469, s2P 28115729515, s2P 26388141209,
   s2N 59395983774, s2N 21772758296, s2N 59387217970, s2P 123007006015, s2P 17562744873,
   s2N 11901583732, s2P 89606451038, s2P 64295019518, s2N 16660045356, s2N 1779217940,
   s2N 36021392616, s2P 826472408, s2P 91229679708, s2N 39518496714, s2N 150858030564,
   s2N 72474149299, s2N 40896757490, s2P 19505804916, s2P 169155368647, s2P 103046447353,
   s2P 28001911730, s2P 80309463357, s2P 33768108380, s2N 94222000806, s2N 176469044769,
   s2P 79919700267, s2P 215466346357, s2P 60852648367, s2P 110593412558, s2P 158282498842,
   s2P 104639419311, s2P 4230584357, s2P 59289462515, s2N 64385565285, s2N 68024720317,
   s2N 33458481247, s2P 39515626687, s2P 12921400688, s2N 77867945492, s2N 243824369945,
   s2N 91301569341, s2N 238843393114, s2N 264334233818, s2N 113647920281]
private def s2V0S3 : List ℤ :=
  [s2N 91322264461, s2N 120393411217, s2N 62220863284, s2P 56774755446, s2N 213274287687,
   s2N 28570350614, s2N 271564114497, s2N 198840133771, s2N 108548048935, s2P 19930113196,
   s2P 130075893814, s2P 501047061553, s2P 764991711877, s2P 502985211029, s2P 66450994932,
   s2N 7269525778, s2P 168737299606, s2P 4006210088, s2N 40681270069, s2P 401804770,
   s2P 231991261318, s2P 237987987342, s2P 6659194953, s2N 34441269187, s2P 204982307973,
   s2P 14343962429, s2N 218598408566, s2N 261306972251, s2P 219770928801, s2P 122949504145,
   s2N 189239222453, s2P 457446082417, s2P 316875517990, s2N 376262185543, s2N 275878011723,
   s2N 1213650627939, s2N 1001390348561, s2N 741793797039, s2P 808229525608, s2P 932943984517,
   s2N 756950227926, s2P 365944924544, s2N 87472125627, s2N 366371038965, s2N 597436313390,
   s2P 259009735377, s2N 452362650943, s2P 523526599054, s2N 441573891352, s2P 1566680777681,
   s2P 806477827776, s2P 702804625237, s2P 614211625391, s2N 784132239464, s2N 484286627764,
   s2P 491577023365, s2N 647587480915, s2N 1740668830323, s2N 2708718741945, s2N 6296730176,
   s2P 2656012180022, s2P 1044690626917, s2P 377579333599, s2N 133982269781]
private def s2V0S4 : List ℤ :=
  [s2N 658016888472, s2N 1160685560307, s2P 539492596977, s2N 857839734572, s2N 1425110137099,
   s2N 1757553813471, s2N 170387419922, s2N 235659464806, s2N 1723804539077, s2N 197479708729,
   s2N 496892536799, s2P 898231121618, s2N 792046760822, s2P 1252199073827, s2N 818738007400,
   s2N 487154835563, s2P 697025632401, s2P 1017213023310, s2N 2019542335488, s2N 1611824233987,
   s2P 3946845321769, s2P 3627451138994, s2P 7508815730297, s2P 11223238510870, s2P 6047430392925,
   s2P 3043661236810, s2P 397988087558, s2P 457233949516, s2P 3042000420442, s2P 904907750851,
   s2P 217347632250, s2P 73551257389, s2N 404119835420, s2N 3985550255367, s2N 5869848209724,
   s2N 40172808175, s2P 3354775302571, s2N 2185501243797, s2P 7580716933041, s2N 790499814716,
   s2P 1431166254516, s2N 1195362989811, s2P 1360942429374, s2P 211933420625, s2N 5023533605213,
   s2N 6415949713984, s2P 1386293384022, s2N 4268296917079, s2P 528270930412, s2P 1774514871612,
   s2P 140575895706, s2P 1527632622035, s2P 98084909484, s2P 3607348516069, s2N 1659141190527,
   s2N 1253676813356, s2N 783194144558, s2P 1220681774633, s2P 3167253559472, s2P 1708279614322,
   s2P 539076067964, s2N 254904674262, s2P 582850873914, s2P 761859713952]
private def s2V0S5 : List ℤ :=
  [s2N 22593949945, s2N 2672242805130, s2N 3181759582948, s2N 319699227072, s2N 4912437573466,
   s2N 9604679813340, s2N 3549780756261, s2N 524249650146, s2N 6378961509576, s2N 2229425338939,
   s2N 4831881065725, s2N 4454346746836, s2N 3406611816946, s2N 2041924259949, s2N 5594321885038,
   s2N 5893145810761, s2N 1590258471191, s2N 1471542543729, s2P 4744525921890, s2P 6138796155939,
   s2N 2704800905597, s2N 694548070869, s2P 5849064605015, s2P 10129717009213, s2P 3266280042194,
   s2P 4554262275915, s2P 2467211698941, s2N 5393765120506, s2P 2723929194753, s2N 998650849311,
   s2N 3281797363892, s2P 4336287713114, s2N 1129669679882, s2P 1134436696227, s2P 4334350929451,
   s2N 1594881732852, s2P 3754948605373, s2N 5152279358123, s2N 4373214980351, s2P 6771316556036,
   s2P 10209723651114, s2P 1241047994322, s2N 7933463668048, s2P 8560045083171, s2N 4598514557109,
   s2N 894743897953, s2P 4152258346137, s2P 2955762710670, s2N 11465074930314, s2N 5271221871779,
   s2N 1986390566687, s2N 1123631593471, s2N 4375985138122, s2N 4959660819823, s2P 850483573953,
   s2N 2793688962585, s2P 4851703083390, s2P 1084370403587, s2N 2969250833474, s2P 18104395034,
   s2N 7699031259497, s2N 11586412282785, s2P 4036844393987, s2N 1023023671557]
private def s2V0S6 : List ℤ :=
  [s2P 11927495747742, s2N 533338522385, s2N 6516948201735, s2P 1856810315985, s2N 2949428660730,
   s2N 10396452181006, s2N 1476710305738, s2P 10058606607850, s2P 12009660188144,
   s2P 6669586388098, s2P 1721746809388, s2P 4777435016837, s2P 13882130411011,
   s2P 58092158471472, s2P 115252155220117, s2P 172658252018454, s2P 227591628277689,
   s2P 279863197996544, s2P 323484061865489, s2P 345944496269118, s2P 348945017520443,
   s2P 331719773819389, s2P 313112316814467, s2P 286369665072086, s2P 256815386523211,
   s2P 223775237066275, s2P 181498048345693, s2P 137103781364936, s2P 98297830625863,
   s2P 66739406182203, s2P 41694675199530, s2P 23269651360989, s2P 11587051658425,
   s2P 5339393947020, s2P 2396547628241, s2P 1067153998119, s2P 463238782264, s2P 201125434471,
   s2P 100798030534, s2P 65685854775, s2P 49465799725, s2P 36581205619, s2P 24977316440,
   s2P 15703680549, s2P 9233786409, s2P 5173950166, s2P 2808956106, s2P 1495314037, s2P 785437144,
   s2P 407658779, s2P 208794589, s2N 105332342, s2P 52293018, s2P 25539986, s2P 12286601,
   s2P 5823555, s2P 2714823, s2P 1247155, s2P 566387, s2P 252122, s2P 107592, s2P 43161,
   s2P 16270, s2P 5902]
private def s2V0S7 : List ℤ :=
  [s2P 2145, s2P 802, s2P 304, s2P 110, s2P 35, s2P 9, s2P 1, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V0S8 : List ℤ :=
  [s2P 0]
private def s2V0 : List ℤ :=
  s2V0S0 ++
  (s2V0S1 ++
  (s2V0S2 ++
  (s2V0S3 ++
  (s2V0S4 ++
  (s2V0S5 ++
  (s2V0S6 ++
  (s2V0S7 ++
  s2V0S8)))))))
private def s2Ch1 : List Rkm128kSeg := [
  ⟨54, 412677, 2, 26,
    rkm128kMask56 513 [3106962615686078, 44203567248828502, 22746677088758222, 30953759522735200,
     37410063124423841, 54111160237897785, 10125817664005391, 2251954432509025, 59745262830092288,
     352]⟩]
private def s2V1S0 : List ℤ :=
  [s2P 48438832, s2P 43673677, s2P 37424372, s2P 118735000, s2P 102682551, s2P 183602396,
   s2P 18687323, s2P 279831046, s2P 433370057, s2P 375267832, s2P 336946590, s2P 67714799,
   s2N 56563103, s2N 180371282, s2P 190473797, s2P 153216206, s2P 360994298, s2P 542376177,
   s2P 24458830, s2P 313097277, s2P 625655901, s2P 702816414, s2P 132627082, s2P 33930089,
   s2N 247516992, s2N 398088612, s2P 141008812, s2N 521602875, s2N 195741771, s2P 1061715943,
   s2P 2085717526, s2P 1190733197, s2P 1751930794, s2P 1849155250, s2P 1115049241, s2N 523227674,
   s2N 1339550957, s2N 126166686, s2N 194290377, s2N 538307493, s2P 931634052, s2N 116294469,
   s2P 170279777, s2P 427869145, s2P 1221075644, s2P 1282606404, s2P 1325723343, s2P 1598827871,
   s2P 4101282939, s2P 1705780370, s2N 192335832, s2N 1825016460, s2N 1283592763, s2N 167299134,
   s2N 495652660, s2P 238112769, s2P 654243143, s2P 4672076726, s2N 124328539, s2N 1952715472,
   s2N 519315947, s2N 1820941386, s2N 4709363399, s2P 1447323609]
private def s2V1S1 : List ℤ :=
  [s2N 283449191, s2P 2054043338, s2N 4090235852, s2N 2607061917, s2P 80845514, s2P 2487473780,
   s2P 857116214, s2P 4397752656, s2N 6941287040, s2N 2068429188, s2P 973806707, s2P 2691115064,
   s2P 6693131046, s2P 4110691888, s2P 5279998888, s2P 11490109216, s2P 6083615687,
   s2P 1595543573, s2P 3399265931, s2P 607596313, s2N 748229670, s2P 7769947048, s2P 7786235594,
   s2P 14348620815, s2P 2202082171, s2N 4863105870, s2P 3951175107, s2P 9834652485,
   s2P 11893275809, s2N 4233812510, s2N 11333364676, s2N 13758408201, s2N 3562509709,
   s2N 1841697730, s2N 10453028182, s2P 11105569703, s2P 15038458455, s2P 7712998185,
   s2P 2299916628, s2P 5712623096, s2N 13442316769, s2N 12038640715, s2P 11025021912,
   s2P 13181863279, s2N 2852561832, s2N 9888944389, s2N 4277290206, s2N 12745270776,
   s2N 372109091, s2P 17199762803, s2N 5466843228, s2P 9292504466, s2P 7116107096,
   s2N 14285436666, s2P 21557340410, s2P 14890922550, s2P 13745647449, s2P 48316557965,
   s2P 17050029533, s2P 8221380234, s2P 44047900647, s2P 72682381584, s2P 52439343317,
   s2P 114170450284]
private def s2V1S2 : List ℤ :=
  [s2P 51092538352, s2P 22959160977, s2P 35184665748, s2N 15933527756, s2N 1909947225,
   s2N 19125943795, s2N 14376507951, s2N 2542954585, s2N 37636595888, s2N 2978743006,
   s2P 81273129172, s2P 36524878040, s2N 29126308903, s2N 63458655555, s2P 78437962955,
   s2P 24346756673, s2N 83237676446, s2N 28235127066, s2P 36958181150, s2N 3199403893,
   s2P 3782075874, s2N 92842252886, s2N 11302308301, s2P 144527161516, s2P 64672502147,
   s2P 1595507706, s2P 40337892218, s2P 15350866906, s2N 32451145049, s2N 73002486308,
   s2N 31235307516, s2N 4307533580, s2N 90118506306, s2P 50597919572, s2P 88922780225,
   s2P 63397729167, s2N 26631858346, s2N 15415210700, s2N 252613429, s2N 31458562627,
   s2P 136504084571, s2P 75146696624, s2N 111786866453, s2N 158835284789, s2P 37218396698,
   s2P 73937411302, s2P 115905715951, s2P 46223000542, s2P 206494945255, s2P 97185058964,
   s2N 101191218626, s2N 64455254134, s2N 42453651434, s2N 42465451895, s2P 61744770716,
   s2N 121591479825, s2P 50498218961, s2P 87562202150, s2P 89126029412, s2P 326310461774,
   s2P 44389398722, s2P 47787567986, s2N 19363295834, s2P 60560950296]
private def s2V1S3 : List ℤ :=
  [s2P 1639353155, s2P 56716451563, s2P 1753061547, s2N 26158070106, s2N 45347694896,
   s2N 189304183887, s2P 175171254452, s2P 185209006446, s2P 173350629952, s2P 288277425357,
   s2P 64236569675, s2P 47325861878, s2N 120752200103, s2N 170453798818, s2N 49559419533,
   s2N 50814046155, s2N 253502522270, s2N 546558139515, s2N 230312330408, s2N 234286648107,
   s2N 355906853643, s2N 419722416540, s2N 379077569675, s2N 494420501306, s2N 527316061836,
   s2N 470929072622, s2N 378115916467, s2N 145577594189, s2N 139442373620, s2N 152521779422,
   s2P 77225628701, s2P 680510942459, s2P 488205700109, s2P 486935910381, s2P 27164403405,
   s2N 220434945284, s2N 345346029189, s2N 857703057579, s2N 1186324935296, s2N 235171199199,
   s2P 516744217772, s2P 983380196864, s2N 157183605757, s2N 1148522511364, s2N 572897767527,
   s2P 746289047720, s2P 1085480382224, s2P 459593874614, s2P 28805491177, s2N 62042854524,
   s2N 321798228922, s2P 446133392435, s2P 233346941245, s2N 493895292641, s2P 108768320718,
   s2P 472340507641, s2P 860058491128, s2P 415217171994, s2P 2516410754585, s2P 870152204551,
   s2P 786054127890, s2P 270716493147, s2P 1056268879963, s2P 1704557430315]
private def s2V1S4 : List ℤ :=
  [s2P 877386303176, s2N 428476987896, s2N 3111927065991, s2N 1282602719764, s2N 357315403664,
   s2P 1953479915403, s2N 384509501639, s2N 406100909887, s2P 790509464547, s2P 448566646834,
   s2N 86815007105, s2P 1238754419599, s2P 382245169872, s2P 1579741709036, s2P 1803106520019,
   s2N 1663274940098, s2N 2690654198336, s2N 2438789897444, s2N 1495863664216, s2N 668752214621,
   s2N 366302506105, s2N 527760858156, s2N 4086929956, s2N 331188041713, s2N 547411480001,
   s2P 663013909596, s2P 638263098323, s2P 4266991072986, s2P 680648760887, s2P 4175095350736,
   s2P 10628892657145, s2P 5945960430520, s2P 5993142215915, s2P 8011941289187, s2P 5229873952139,
   s2N 978914030284, s2N 2552903117227, s2N 1030359326356, s2P 5651966484273, s2N 613639266375,
   s2N 743463804273, s2P 727258293448, s2P 7906378853537, s2P 2532795713228, s2P 195175283829,
   s2P 2159370355008, s2P 791665974425, s2P 1322206185473, s2P 2920458300488, s2P 1268026613412,
   s2N 2275888787297, s2P 653124918354, s2N 2178744810608, s2N 4102636238623, s2P 3236484495602,
   s2N 1906500370611, s2N 1571155507011, s2N 1561602927717, s2N 1017597688638, s2P 2173136896032,
   s2N 2394029342034, s2P 1195765912390, s2P 52954785748, s2P 1423714933434]
private def s2V1S5 : List ℤ :=
  [s2P 2953395925106, s2P 5622949311116, s2P 103582769446, s2P 1717096083739, s2N 3318972421482,
   s2N 2997954285418, s2N 1035530888005, s2N 887272262716, s2P 2310064105782, s2N 295303375255,
   s2N 92576011635, s2N 1533338402483, s2N 7809077037411, s2N 2972693400667, s2P 3967561626242,
   s2P 4264534545952, s2P 4203325717517, s2P 3635158731329, s2P 5256028737387, s2P 5689991137737,
   s2P 3739896021980, s2N 5979595743101, s2N 12059118106586, s2N 2054659535439, s2P 3646205720178,
   s2P 1224326214321, s2N 4117325340633, s2N 5844383122616, s2P 2228902626442, s2N 1360096845601,
   s2N 4822682697009, s2P 8649604274944, s2P 3269329172942, s2P 6249224484921, s2N 170812812062,
   s2N 3158651391974, s2N 6710421094442, s2N 7078534573256, s2P 1728205695234, s2P 7328305176174,
   s2P 3223616231537, s2P 12131926092600, s2P 3525996200972, s2N 4394834763927, s2P 1430486181375,
   s2P 2651656212817, s2P 2005295190215, s2N 4747028075174, s2P 8141629848858, s2N 3707893266517,
   s2N 3294753006528, s2P 4803467179877, s2P 2865507914278, s2N 853243803764, s2N 2059640199714,
   s2N 10788001744027, s2N 3918853331398, s2N 5872953415778, s2N 4966621232697, s2P 1626305640962,
   s2P 6862872131764, s2P 1423192517890, s2P 706982842051, s2P 1848771235452]
private def s2V1S6 : List ℤ :=
  [s2N 7450956652515, s2N 4352738352946, s2N 10703378293330, s2N 9358980341357, s2N 2673758689849,
   s2N 2192108910029, s2N 3814340380656, s2P 3614666524765, s2N 7840772534702, s2N 446087698072,
   s2N 5334892675971, s2N 7742168675050, s2N 6804543796667, s2P 1287047121805, s2N 13277557503076,
   s2P 13234081513750, s2P 2146979890034, s2N 12515896884299, s2P 12342772286733,
   s2P 10260265286802, s2P 44400638599058, s2P 91578589425685, s2P 152317798011499,
   s2P 216922283390929, s2P 276075905318463, s2P 320505554383023, s2P 342776928703953,
   s2P 345377437978729, s2P 337305978981886, s2P 322944283849622, s2P 300156717545256,
   s2P 267155838217817, s2P 226365133161866, s2P 182340983201812, s2P 139121134759343,
   s2P 99810070036861, s2P 66847582377552, s2P 41649341065498, s2P 24172009342514,
   s2P 13132309862662, s2P 6722506556358, s2P 3265518689560, s2N 1519647272901, s2P 690172601619,
   s2P 317598486435, s2N 156412414678, s2P 86178317875, s2P 52179496013, s2P 33130626464,
   s2P 20961519070, s2P 12736316182, s2P 7467114960, s2P 4298517380, s2P 2388617224,
   s2P 1231103462, s2P 577206711, s2P 252357524, s2P 110209620, s2P 51774281, s2N 26490079,
   s2P 14040076, s2P 7325341, s2P 3675623, s2P 1767361]
private def s2V1S7 : List ℤ :=
  [s2P 817126, s2P 364393, s2P 156841, s2P 65111, s2P 26067, s2P 10087, s2P 3786, s2P 1383,
   s2P 489, s2P 164, s2P 48, s2P 12, s2P 1, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V1S8 : List ℤ :=
  [s2P 0]
private def s2V1 : List ℤ :=
  s2V1S0 ++
  (s2V1S1 ++
  (s2V1S2 ++
  (s2V1S3 ++
  (s2V1S4 ++
  (s2V1S5 ++
  (s2V1S6 ++
  (s2V1S7 ++
  s2V1S8)))))))
private def s2Ch2 : List Rkm128kSeg := [
  ⟨55, 407946, 2, 26,
    rkm128kMask56 512 [70969016996053143, 28217265368236924, 8789469243894450, 7951713249512028,
     26302718650146936, 41106496343785680, 4517082705690917, 18014948265484288, 15080970206052864,
     221]⟩]
private def s2V2S0 : List ℤ :=
  [s2N 21985156, s2N 57059596, s2P 14675508, s2P 88649977, s2P 29857559, s2P 130840624,
   s2P 182871117, s2P 2420302, s2P 82038384, s2P 81740710, s2P 334312134, s2P 268848307,
   s2P 456027463, s2P 454819734, s2P 41542702, s2N 148740227, s2P 91418163, s2P 139380174,
   s2N 20801099, s2N 456790455, s2N 427628635, s2N 118567980, s2P 388558982, s2P 187503800,
   s2P 539919161, s2P 669770636, s2P 751097036, s2P 411437462, s2P 85262324, s2N 511568472,
   s2P 336649674, s2P 815140111, s2P 671084628, s2P 289479563, s2P 1130374811, s2N 150186929,
   s2N 1738741168, s2N 2378221675, s2N 1942150147, s2N 1072573543, s2N 834416413, s2N 660184356,
   s2N 88268462, s2N 1227234162, s2P 295264237, s2N 472300526, s2N 786864949, s2N 50777064,
   s2P 183946368, s2P 1732338555, s2P 911000824, s2N 849087065, s2N 342619922, s2N 3022990561,
   s2N 4091307009, s2N 2419036438, s2N 2292474370, s2P 3777181830, s2P 1811915391, s2P 1686327919,
   s2P 2122437839, s2N 964074094, s2N 230878878, s2P 2775367705]
private def s2V2S1 : List ℤ :=
  [s2P 1071233236, s2N 5725703152, s2N 1603137457, s2N 4206110814, s2N 499039949, s2N 2813976953,
   s2P 206900038, s2N 2963212905, s2N 2631070705, s2P 2936647933, s2P 2825165195, s2P 1496487369,
   s2P 3785364468, s2P 5864632639, s2P 5810519374, s2P 304933751, s2N 1378466118, s2P 1753352096,
   s2N 1666450471, s2P 2042557671, s2P 6558869874, s2P 5148694464, s2P 6729220361, s2P 7154377176,
   s2P 9247365308, s2P 7615272434, s2P 7246801842, s2P 345763218, s2N 1323059195, s2N 13194018452,
   s2N 13807958957, s2P 1138472449, s2P 8893691045, s2N 8242769785, s2N 16796237463,
   s2N 2027397505, s2N 4503278722, s2N 6765337939, s2N 4598806841, s2N 13690265212,
   s2N 7770135543, s2N 718512910, s2P 20083663784, s2P 2790364499, s2P 25019800602,
   s2N 1050982135, s2N 14005341123, s2N 1088699959, s2N 23506479262, s2N 14801812091,
   s2N 627888662, s2P 4532416460, s2N 6220620812, s2N 6151851561, s2N 36037882501,
   s2N 16997617481, s2N 3579576257, s2P 25667346074, s2P 38541659816, s2P 7213656303,
   s2N 6829766169, s2N 5439804821, s2P 11310001272, s2N 12599170534]
private def s2V2S2 : List ℤ :=
  [s2N 29393398730, s2N 13914206714, s2P 35180760620, s2P 22653330633, s2P 28843907199,
   s2P 36343340110, s2P 65410376580, s2P 60629801492, s2P 78582957956, s2P 100611616158,
   s2P 43314723497, s2P 48187609337, s2P 81566155908, s2P 65784790846, s2P 84815589459,
   s2P 49771820153, s2P 6136304567, s2P 22337585391, s2P 49287703727, s2P 43027479478,
   s2P 27758108141, s2N 96619011038, s2N 24725620647, s2P 31360806725, s2P 86084135901,
   s2P 60060566879, s2P 53781632484, s2P 51273466887, s2P 36512695265, s2P 31799909085,
   s2N 6693055128, s2N 55415104616, s2N 83143109152, s2N 81318939295, s2N 21170150655,
   s2N 6081295869, s2N 112779179227, s2N 48515643317, s2N 19372514445, s2N 43255805853,
   s2N 80784947742, s2N 67540921473, s2N 15673772909, s2N 138603822341, s2N 96162699968,
   s2N 197168053436, s2N 12076920717, s2P 89544337122, s2P 26596254523, s2N 127608376455,
   s2N 110396823839, s2N 78360247463, s2N 93143649763, s2N 115242138534, s2P 16936000588,
   s2N 108548233465, s2N 127597931933, s2N 144062069196, s2N 124449147432, s2N 88448704196,
   s2N 57508353616, s2N 16460085624, s2P 218651621, s2P 16279118424]
private def s2V2S3 : List ℤ :=
  [s2P 234524990957, s2N 52159488810, s2P 65132929796, s2P 65604769430, s2P 205962690471,
   s2P 132614147955, s2P 105972863311, s2P 34144724674, s2P 81995699073, s2N 32997903345,
   s2P 156146668462, s2N 28438197155, s2N 120656404867, s2N 45340821637, s2N 34663412959,
   s2N 143483732231, s2P 31849379310, s2P 393317226497, s2P 241039350604, s2P 79815020957,
   s2N 32310477536, s2P 153075386079, s2P 30270710202, s2P 112749024056, s2N 227349431084,
   s2N 192775281792, s2P 138953978119, s2P 347482283210, s2P 392069423834, s2N 71079364912,
   s2N 391270171067, s2N 259262487799, s2N 636958466729, s2N 594709386279, s2N 260199065160,
   s2P 337531196096, s2P 552067360848, s2P 550918643081, s2P 298773196430, s2P 244125353029,
   s2P 196509602531, s2P 205615869417, s2P 326369841420, s2P 1023328344833, s2P 954797061920,
   s2P 1244826136826, s2P 1182135359292, s2P 1077305851788, s2P 677979314063, s2N 42320054525,
   s2N 747938253731, s2N 969299492222, s2N 1094915053689, s2P 488482852425, s2N 238955575517,
   s2N 546025118884, s2P 185971770588, s2P 1122554855695, s2N 574970937823, s2N 573927898396,
   s2N 191556423515, s2N 449283755207, s2P 117512882461, s2P 666052273295]
private def s2V2S4 : List ℤ :=
  [s2N 245813076423, s2N 616631595906, s2N 1156914363789, s2N 2421741313479, s2P 93171263266,
   s2P 1139974131218, s2P 2216089096840, s2P 2472516707908, s2P 1863153873260, s2N 609155516064,
   s2N 1328053901747, s2N 1294156108999, s2P 169303431711, s2P 600278296861, s2P 946679716672,
   s2P 626384022074, s2N 76948456304, s2P 1297836217327, s2P 1799503673778, s2N 96997108366,
   s2N 1287408771346, s2P 887131999752, s2N 4029782114601, s2N 964485682475, s2N 971077486562,
   s2P 396469114860, s2N 2864539116726, s2N 4117902742778, s2N 2615705610719, s2N 1893097779736,
   s2P 1037091118715, s2P 2477809709444, s2P 2466144763091, s2N 547113485761, s2N 1751806126475,
   s2N 607345605284, s2P 2680302331178, s2P 3508619199334, s2P 485726429660, s2P 5457705037279,
   s2P 12563075270488, s2P 9553233906779, s2P 2589493988479, s2N 3637912568782, s2P 4561824199542,
   s2N 609161024536, s2P 3094005815215, s2P 2615213297380, s2N 1353900442718, s2P 4957958510190,
   s2P 1231108799456, s2P 3968960375644, s2P 1436261381828, s2P 3097640395829, s2P 267016477030,
   s2P 1825173404325, s2P 3070966926947, s2P 4266542495376, s2P 2416421331082, s2P 441521698097,
   s2N 742394652920, s2P 1492173798476, s2P 886545980187, s2N 2468538260701]
private def s2V2S5 : List ℤ :=
  [s2N 1152983395987, s2P 1307593519335, s2N 831900143719, s2N 983693180052, s2N 2102674481949,
   s2N 731739024825, s2N 306676088898, s2N 1173145432671, s2P 4804162651815, s2N 4716370234300,
   s2P 1731239891921, s2P 1252293789259, s2N 833845548097, s2N 2851778085367, s2N 4818401389059,
   s2N 1203497368950, s2N 2399484848604, s2P 2168891564251, s2N 244783614682, s2N 7551256829125,
   s2N 4614537421503, s2N 1517864814332, s2N 991061710279, s2P 1444294669398, s2P 5839721722068,
   s2P 11953409891818, s2P 13383022225426, s2P 2017950858678, s2N 3008337453595,
   s2N 2723609108852, s2N 2299211731248, s2N 1842485388947, s2N 3777690326970, s2P 3271087874104,
   s2N 3963524748452, s2P 4084805341367, s2N 332155247692, s2N 8049820876789, s2P 1915725419734,
   s2P 4820606071547, s2P 9579814223244, s2P 818250468461, s2N 4170636913604, s2N 2978014349931,
   s2N 13357033573567, s2N 2377513600981, s2N 6410476952375, s2P 451523124640, s2N 9115664353716,
   s2N 4799115219309, s2P 2219699247045, s2P 803475429789, s2P 487637668496, s2P 3274638020750,
   s2N 3564969716897, s2N 2126032520061, s2N 4773727668615, s2P 5941399894923, s2P 218589854284,
   s2N 2648101402844, s2P 3338228667980, s2N 1923995968073, s2N 5850168107301, s2N 5614638984035]
private def s2V2S6 : List ℤ :=
  [s2N 12234781639190, s2P 1909218013128, s2N 4077225922185, s2P 2311207528588, s2N 3795717026901,
   s2P 5205616716578, s2N 3274234949771, s2P 4906014536856, s2N 15263558030688, s2N 5879285156248,
   s2N 1230884013161, s2N 18471145517388, s2P 8848473459462, s2N 5164835520075, s2N 7155336230985,
   s2P 3655660956733, s2N 1671713166739, s2N 8958702741302, s2N 8516256152074, s2N 5538379218986,
   s2N 2738525134318, s2N 743471446775, s2N 2085655322291, s2P 2504353268257, s2N 9287265042566,
   s2P 9501167212142, s2P 3107964029041, s2P 32944672021454, s2P 83487110798438,
   s2P 150766873034428, s2P 220709911679390, s2P 278265981892435, s2P 316985645139370,
   s2P 339340106912503, s2P 347871113004772, s2P 345889813285181, s2P 328992418004025,
   s2P 303909244415072, s2P 265248244641059, s2P 221860466671660, s2P 177239547528763,
   s2P 131463960342988, s2P 92005763939253, s2P 61997700674267, s2P 39342777445978,
   s2P 22759337984330, s2P 11880149967412, s2N 5632191894731, s2P 2446598631060, s2P 986671447521,
   s2P 386257241349, s2P 164241509763, s2P 86170947537, s2P 54638334031, s2P 36923932301,
   s2P 24429707160, s2P 15530098617, s2P 9449339388, s2P 5473731150, s2P 3036038676,
   s2P 1618881072, s2P 815728131, s2N 378284995, s2P 160418374]
private def s2V2S7 : List ℤ :=
  [s2P 64524973, s2P 26771288, s2P 12407195, s2P 6377101, s2P 3381429, s2P 1745700, s2P 857499,
   s2P 399575, s2P 177342, s2N 75352, s2P 30784, s2P 12130, s2P 4614, s2P 1693, s2P 593, s2P 192,
   s2P 56, s2P 12, s2P 1, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V2S8 : List ℤ :=
  [s2P 0]
private def s2V2 : List ℤ :=
  s2V2S0 ++
  (s2V2S1 ++
  (s2V2S2 ++
  (s2V2S3 ++
  (s2V2S4 ++
  (s2V2S5 ++
  (s2V2S6 ++
  (s2V2S7 ++
  s2V2S8)))))))
private def s2Ch3 : List Rkm128kSeg := [
  ⟨56, 405267, 2, 26,
    rkm128kMask56 513 [2640447048237738, 59839352673587976, 38698471796643971, 6752258025037210,
     59571594417426726, 14932873254730324, 71133138518046532, 1266637443336271, 18093563346698272,
     280]⟩,
  ⟨56, 263893, 1, 30,
    rkm128kMask56 510 [2139620705861815, 28747133282651408, 61223046639346967, 39210950815508096,
     54541566428957600, 12129141477377709, 45054451783041717, 562950767250625, 36611538181685376,
     48]⟩]
private def s2V3S0 : List ℤ :=
  [s2P 10726423, s2N 58187019, s2P 28949186, s2N 77038676, s2N 23385346, s2P 46818978,
   s2P 206978273, s2P 51599374, s2P 49573555, s2P 141736380, s2P 19678509, s2N 11530204,
   s2N 44627493, s2P 153549450, s2P 125984450, s2N 158973736, s2N 249210842, s2N 334163397,
   s2N 701883164, s2N 202432497, s2P 225484530, s2P 407099282, s2P 15632063, s2P 106769602,
   s2P 13506313, s2P 70882364, s2P 494648155, s2N 65376976, s2N 307140082, s2N 398695171,
   s2N 353582964, s2P 16113760, s2P 620867566, s2N 433335350, s2N 1822267354, s2N 699697967,
   s2P 1240435852, s2N 426337757, s2N 304280273, s2N 362651490, s2P 1050923141, s2N 314276837,
   s2N 422640223, s2N 352667045, s2N 1235768368, s2N 1336634821, s2N 3724015628, s2N 459847991,
   s2P 196349244, s2P 1592217572, s2N 1055467086, s2N 147875342, s2P 882123635, s2P 1358040151,
   s2N 1415248921, s2N 52390097, s2N 1284501269, s2N 837531203, s2P 1239288304, s2P 386433946,
   s2P 2979430460, s2P 2525532578, s2P 4450110828, s2P 4678030212]
private def s2V3S1 : List ℤ :=
  [s2P 2255455137, s2P 396462430, s2P 3200226617, s2P 1045231964, s2N 5318555092, s2P 154314427,
   s2N 3450386464, s2P 681779476, s2N 153456910, s2N 562771738, s2P 3564738137, s2P 957321129,
   s2P 63260790, s2N 380770566, s2N 4840139533, s2N 1585221608, s2N 1485942187, s2N 2539000591,
   s2P 2226067894, s2N 2699712144, s2P 1719586545, s2P 2458157138, s2P 1149720656, s2N 103628198,
   s2P 4225241838, s2N 3039007536, s2P 5433493922, s2P 2920867931, s2P 7423664256, s2P 218288908,
   s2N 3932970098, s2N 6089336542, s2N 165555388, s2P 1229803717, s2P 9613946541, s2P 14318012115,
   s2P 11281808095, s2P 10505552197, s2N 9815046494, s2N 20346550679, s2N 7696165506,
   s2P 4021473501, s2P 5504157886, s2N 10274680105, s2N 12476633208, s2P 13118034365,
   s2P 4825967140, s2N 11504686149, s2P 6926236882, s2N 5756753559, s2N 3061959625,
   s2P 13607492880, s2N 19438652704, s2P 6532633807, s2P 5498572433, s2P 23056692016,
   s2P 6508418807, s2P 10137129721, s2N 29015914886, s2P 4141905531, s2P 24889654606,
   s2P 13383856356, s2P 7683400169, s2N 14022579584]
private def s2V3S2 : List ℤ :=
  [s2N 16775957893, s2N 5458802471, s2N 37696767793, s2N 18285994675, s2N 9621923152,
   s2N 37236976701, s2N 36599204309, s2N 3379562929, s2P 8377600179, s2P 12256600798,
   s2P 62939307403, s2P 7658938144, s2N 8111176162, s2N 41596856967, s2P 14025561713,
   s2P 36437113978, s2N 5122223307, s2N 48394629445, s2N 48876025099, s2N 37987288441,
   s2P 43780347480, s2P 79321080900, s2P 28327845507, s2N 122307732549, s2N 56337715766,
   s2N 21648907747, s2P 40450535865, s2P 38358968515, s2P 95329971865, s2P 92639728322,
   s2P 86919146491, s2P 51052657542, s2P 85583735293, s2P 24647999030, s2N 20237785321,
   s2N 3285215065, s2P 49778399492, s2P 1734262409, s2P 46081588638, s2P 46714278542,
   s2P 63715378424, s2P 84504097213, s2P 55393534345, s2P 124894034029, s2P 57729338519,
   s2N 20065498651, s2P 1571796301, s2P 1729547923, s2P 135022858770, s2N 55629822794,
   s2P 216107657039, s2P 179600394168, s2P 99654639067, s2P 51087212369, s2N 93808173052,
   s2N 76681786758, s2N 167993095020, s2N 62535801045, s2P 120359793426, s2P 114246966547,
   s2P 87312566285, s2P 117107919380, s2P 132494563199, s2P 37452020343]
private def s2V3S3 : List ℤ :=
  [s2P 12961862742, s2P 60050695079, s2N 199180729040, s2P 8989912538, s2P 43971366129,
   s2P 139271318169, s2P 17902812348, s2P 152911905492, s2P 33419044063, s2N 149145586907,
   s2P 165742356323, s2P 105007334274, s2N 40095728271, s2P 195138469104, s2P 116551859272,
   s2P 90857896131, s2P 181256567906, s2P 67123877922, s2N 59833475516, s2N 72151836761,
   s2N 141992030915, s2P 7550262697, s2P 50610341677, s2P 40107789697, s2P 59321044911,
   s2P 228278556428, s2N 282242951969, s2N 184976542518, s2P 124059933215, s2P 70548126506,
   s2P 286588629088, s2P 310351001596, s2N 955998277, s2N 360347823147, s2P 428044714131,
   s2P 361850715422, s2P 35264058013, s2N 137379756775, s2N 188467426037, s2N 341683325261,
   s2N 108831348878, s2N 278605560515, s2N 634973784947, s2N 148489232752, s2P 702164857226,
   s2P 707672001061, s2P 683054549010, s2P 184594917387, s2P 258636103508, s2N 392298781952,
   s2N 600855298339, s2N 47059383367, s2P 612336187235, s2N 462762023796, s2N 596062828592,
   s2P 624854514957, s2N 975684147483, s2P 1011727149579, s2N 689627161717, s2N 729348187949,
   s2N 1253355229661, s2N 1794558946208, s2N 1650048368818, s2N 235778619791]
private def s2V3S4 : List ℤ :=
  [s2P 454325073247, s2P 301279302579, s2P 472811154226, s2P 271337325117, s2P 213640080541,
   s2P 133770540108, s2P 402025280796, s2P 1338692104279, s2P 993058160309, s2N 605535870633,
   s2N 67403692982, s2N 756271414820, s2N 1863183440414, s2P 880911633518, s2N 2502784530149,
   s2P 117875577319, s2P 575496588845, s2N 888507746142, s2N 413583870309, s2N 995034619396,
   s2N 3713055738900, s2N 1395649230449, s2P 3214383400262, s2P 1235482150182, s2N 861932450188,
   s2N 3079036612491, s2N 93239615317, s2N 266914530605, s2N 1885485769479, s2N 513664685694,
   s2N 1533483507921, s2N 94798864613, s2N 405865101430, s2N 740046581203, s2N 1023857726198,
   s2N 1207952278650, s2N 501756407480, s2P 1587232499618, s2P 702389953233, s2P 3045369213846,
   s2P 4389213209562, s2P 6086199300588, s2P 4581004992676, s2P 8456877831829, s2P 9873502084920,
   s2P 332470734339, s2N 445080882236, s2N 5469266321164, s2N 1839737107538, s2P 6677895216163,
   s2P 250899479815, s2N 4555871429882, s2P 1996377905696, s2N 3189778574911, s2P 1474112037067,
   s2P 799371378214, s2P 4848314111824, s2P 1367422992342, s2N 6437928175818, s2P 311026748978,
   s2N 1794131014793, s2N 1274109231562, s2N 1655368693267, s2N 2618167192897]
private def s2V3S5 : List ℤ :=
  [s2P 4763402637373, s2P 1254357195652, s2P 2470863557464, s2N 2933597134190, s2P 389601064493,
   s2N 1948869238516, s2N 3669573276115, s2N 6144768354688, s2P 2444388290732, s2N 1263743660672,
   s2N 3054671677758, s2P 710942988319, s2P 1085795227405, s2N 2434218946355, s2N 764460334832,
   s2N 427992776493, s2N 1510089185951, s2N 5729735718901, s2N 1757958655753, s2P 1379448164504,
   s2P 1922935939880, s2P 3101816011999, s2P 1502774228913, s2N 587011466436, s2N 6798019123622,
   s2N 1263109669285, s2P 365759904160, s2N 2326488913162, s2P 3768036280681, s2P 5795360333274,
   s2N 5157857885469, s2P 1879127051026, s2P 7727593907078, s2P 6832890437681, s2N 1391685811988,
   s2P 3152468017396, s2N 1815984248170, s2P 9056481771994, s2P 6987708182629, s2P 14773261289645,
   s2P 4069065543807, s2N 311143386806, s2N 6741993755906, s2N 4953245182885, s2N 3241563457935,
   s2N 5222863842070, s2P 8500002098865, s2P 1321352047471, s2P 4708848625911, s2P 1786565691947,
   s2P 1947900210455, s2P 982839436023, s2P 16614152519538, s2N 791916349458, s2P 1839118577405,
   s2N 7427388172515, s2P 3778280914148, s2N 953802266459, s2N 170242309814, s2P 6279005888441,
   s2P 3413819525632, s2P 5424300125097, s2N 3348177594185, s2P 11321344939193]
private def s2V3S6 : List ℤ :=
  [s2N 1947781810426, s2P 11012861888529, s2N 5395620041668, s2N 11376783360182,
   s2P 7567372774726, s2P 6168184228351, s2N 7067097630422, s2N 737968352045, s2N 842439382817,
   s2N 1934589436332, s2P 7097825957209, s2P 7166414120584, s2P 2409072822409, s2P 10967725389325,
   s2P 7138363272948, s2N 6062017009847, s2P 5989895850796, s2P 6352323973082, s2N 2760933050106,
   s2N 6414822120169, s2N 10323534898776, s2N 1472829637460, s2N 7796932775885,
   s2N 10999784436188, s2N 4831740452185, s2N 4872438192415, s2N 3691465213708, s2P 5329561603946,
   s2N 10209081147793, s2P 10268996563967, s2P 3012158628413, s2P 1937924228035,
   s2P 4575330947320, s2P 9122626594509, s2P 7474639850987, s2N 6027146672894, s2P 14436593982697,
   s2P 17349118011533, s2P 20580969601640, s2P 70362277877953, s2P 139026042443618,
   s2P 207548737864119, s2P 261793704243397, s2P 311005514460301, s2P 343919496906089,
   s2P 355209851806043, s2P 355670260118210, s2P 343817473354035, s2P 312007886181479,
   s2P 265412757963354, s2P 217311231340404, s2P 170588425666575, s2P 129835832668891,
   s2P 88501528722100, s2P 56277200782136, s2P 33898108344931, s2P 17475667248401,
   s2N 7653244659144, s2P 3075427257119, s2P 1170404566865, s2P 414252979863, s2P 153109964876,
   s2P 79154158328, s2P 55341636017]
private def s2V3S7 : List ℤ :=
  [s2P 39999858142, s2P 27057599822, s2P 17372662093, s2P 10251197118, s2P 5824874581,
   s2P 3124510066, s2P 1449668388, s2N 565063995, s2P 200452762, s2P 77858685, s2P 37228327,
   s2P 20174011, s2P 10727302, s2P 5640317, s2P 2826243, s2P 1226850, s2P 448862, s2P 149419,
   s2P 53076, s2P 22218, s2P 10196, s2P 4619, s2P 1966, s2P 778, s2P 282, s2P 92, s2P 24, s2P 4,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V3S8 : List ℤ :=
  [s2P 0]
private def s2V3 : List ℤ :=
  s2V3S0 ++
  (s2V3S1 ++
  (s2V3S2 ++
  (s2V3S3 ++
  (s2V3S4 ++
  (s2V3S5 ++
  (s2V3S6 ++
  (s2V3S7 ++
  s2V3S8)))))))
private def s2Ch4 : List Rkm128kSeg := [
  ⟨56, 277770, 1, 31,
    rkm128kMask56 513 [47498679116033866, 47169302498312472, 35169312856915596, 57004973401636367,
     1114225682804926, 27372342248266055, 2508160558667376, 8590094741, 36169534775754752, 452]⟩,
  ⟨56, 278027, 1, 31,
    rkm128kMask56 513 [68144276930307934, 64946865724854267, 69803597264493183, 19231483369222638,
     46170736835310584, 9297608034124808, 36071815700811424, 456885600786, 282574488371200, 269]⟩]
private def s2V4S0 : List ℤ :=
  [s2P 10844943, s2N 56432336, s2N 40931252, s2N 30434735, s2N 53782577, s2P 34529200,
   s2P 184490237, s2N 37054063, s2N 103717027, s2N 2563410, s2N 37003210, s2N 75337924,
   s2N 99227005, s2P 209144327, s2P 129308899, s2P 89503059, s2N 30681436, s2N 40305086,
   s2N 221174642, s2P 130137353, s2P 319789612, s2P 227279882, s2P 417089295, s2P 519789596,
   s2P 465559014, s2P 329454295, s2P 281773778, s2N 203223759, s2P 33880575, s2N 51522803,
   s2N 129321892, s2N 46846278, s2N 229498770, s2N 20614462, s2P 1398237474, s2P 1289978230,
   s2P 365795773, s2N 1328773612, s2N 90560845, s2P 1897296934, s2N 271749308, s2N 1236375024,
   s2N 704726425, s2N 210244884, s2N 476474346, s2P 235507651, s2N 762429051, s2P 959345645,
   s2N 672230034, s2P 162656235, s2P 626572320, s2P 15006800, s2P 1168727506, s2P 3039938223,
   s2P 2613732126, s2P 1554600384, s2N 201155845, s2P 639069923, s2P 728608067, s2N 1770256879,
   s2N 142523555, s2N 659611726, s2N 1058862885, s2N 99462779]
private def s2V4S1 : List ℤ :=
  [s2N 2172132628, s2P 1941177012, s2P 597205187, s2P 896385855, s2P 3189506848, s2P 2333133552,
   s2P 5072746714, s2P 2644879598, s2P 2153828303, s2N 4661018561, s2N 3892791915, s2N 1746039361,
   s2P 2914142275, s2P 5455228588, s2P 270772036, s2P 1714717873, s2P 1415296814, s2N 1935410362,
   s2N 4744835866, s2N 3531030857, s2N 2397036805, s2N 3502990424, s2N 262367714, s2N 4151390050,
   s2N 181889612, s2P 5053550036, s2P 3161467933, s2N 489242510, s2P 2992529793, s2P 388388175,
   s2N 956912731, s2P 1043841993, s2P 2565973596, s2P 21089939, s2P 8668899664, s2P 1252902276,
   s2N 7748384200, s2N 2789734805, s2N 408710429, s2N 4816368008, s2N 3106051106, s2P 66864086,
   s2P 6336159344, s2P 5341969215, s2P 2075054390, s2P 10305592006, s2P 11398832968,
   s2P 15170216082, s2P 24854733976, s2P 14287762152, s2P 7947292997, s2P 27712733513,
   s2P 11978670252, s2P 16334635092, s2N 5557018758, s2N 8850787586, s2N 13672187298,
   s2P 3023143743, s2N 15431786305, s2N 9380694696, s2P 17190282586, s2P 6413570183,
   s2P 13501492323, s2N 26742574767]
private def s2V4S2 : List ℤ :=
  [s2P 11054422728, s2P 20884204983, s2P 14859400926, s2P 936699216, s2P 10331032032,
   s2N 1112404963, s2N 21003789765, s2N 23698002591, s2N 2859582749, s2P 20459463974,
   s2N 15082389812, s2P 20597918535, s2P 24282221579, s2N 27995545931, s2N 2833549495,
   s2P 2973180201, s2P 6114456941, s2P 23507727415, s2P 81954194020, s2P 33396561106,
   s2P 21265286327, s2N 11691039651, s2N 28700134916, s2N 42872514957, s2N 70663611574,
   s2N 51656793185, s2N 71267257907, s2N 47954160072, s2P 53747277791, s2P 95431610694,
   s2P 19047749155, s2P 3565661332, s2P 19829382752, s2N 63379349082, s2P 46307151965,
   s2P 93446269033, s2P 714244355, s2N 68948863809, s2N 91443926846, s2N 46604480299,
   s2N 10941643307, s2N 8314175786, s2P 125772855585, s2P 138142948946, s2P 33816812676,
   s2P 61002120106, s2P 156028959214, s2N 101077573, s2N 71521672512, s2N 58147383692,
   s2P 61202528484, s2N 42537532328, s2N 100719772084, s2N 77369152912, s2N 121487452371,
   s2P 1467057033, s2P 153340361854, s2P 44373653142, s2P 105646195523, s2P 165361632225,
   s2P 81032002900, s2P 29847812006, s2P 231325668040, s2P 13908251289]
private def s2V4S3 : List ℤ :=
  [s2P 165210501992, s2P 7110361734, s2P 120734425316, s2N 179377685137, s2P 120707921324,
   s2P 166171709720, s2N 142265502677, s2P 123412725954, s2N 46891145969, s2N 24259306622,
   s2N 23284972566, s2N 100159675759, s2N 141050644412, s2P 60835352265, s2P 123803067945,
   s2P 85755162961, s2P 20000973172, s2P 161998887880, s2N 22155928397, s2P 25382696023,
   s2P 208641930840, s2P 7941567169, s2N 8746078211, s2N 23150735607, s2P 71908362388,
   s2N 30993412247, s2P 78940268286, s2P 371139891801, s2P 192655581739, s2P 129843506309,
   s2N 168223792649, s2N 192002487369, s2N 56964556123, s2P 380963413597, s2P 401276960981,
   s2P 177449203998, s2P 146345664402, s2P 24506410504, s2N 244568669238, s2N 46983299865,
   s2N 43562320133, s2P 39145357557, s2N 237316765368, s2N 309781145147, s2N 6643781318,
   s2N 191158136067, s2P 226016586454, s2P 471131461427, s2P 425726886779, s2P 402253346396,
   s2P 138174681070, s2N 85083162770, s2N 184238058440, s2P 9248289066, s2P 522556940842,
   s2P 758661129734, s2P 1035532810310, s2P 1208130581186, s2P 1253499095762, s2P 714879469505,
   s2P 161840426087, s2N 280909334763, s2N 111855342665, s2N 313863457364]
private def s2V4S4 : List ℤ :=
  [s2N 731739131640, s2N 209535079224, s2N 37848542656, s2P 121835926002, s2N 185266712039,
   s2P 168804138369, s2P 697903152150, s2N 636654651603, s2N 1428766999906, s2N 2036790030599,
   s2N 2249620841804, s2N 1284450530462, s2N 23143666163, s2P 1267177562236, s2P 2210732472216,
   s2P 664519352294, s2N 447617113206, s2N 89812118057, s2P 948426146187, s2N 665646058805,
   s2N 1915825034158, s2P 1062810325312, s2P 1152805989857, s2N 335651735994, s2P 981777033255,
   s2N 1181199142968, s2N 1635102190460, s2P 1504342390773, s2N 472061359794, s2P 2933877503235,
   s2P 1881008963157, s2P 2820225312157, s2P 2455991272906, s2P 2059789284683, s2P 1000464861088,
   s2P 1442326713240, s2P 1817956868530, s2P 1214379190808, s2N 2388209785355, s2N 1616547955068,
   s2P 1673698300972, s2P 1811402063006, s2N 918159831437, s2P 73590173584, s2P 4088220478722,
   s2N 2868769163371, s2N 2413896793390, s2N 2628998593408, s2P 3074008975658, s2P 5241663578893,
   s2N 2232448178859, s2N 11138574267012, s2N 865380221174, s2P 2517473333948, s2P 7241139634708,
   s2P 6137417291406, s2P 8627088028011, s2P 4624549646409, s2P 641610060295, s2P 2538128656573,
   s2P 2691327681383, s2N 4247938427565, s2N 2657185548708, s2N 3031005267651]
private def s2V4S5 : List ℤ :=
  [s2N 880480908357, s2P 685776289726, s2P 800217109343, s2N 5374700367955, s2N 2826583705293,
   s2N 2721348323948, s2P 1087915778795, s2P 3072775955967, s2N 1372105447881, s2P 2862395490026,
   s2P 759947224053, s2N 720467129864, s2N 1713895136806, s2N 692666881337, s2N 2642478006373,
   s2N 3479275768115, s2N 3984771704123, s2N 2680147992265, s2P 3317933230068, s2P 1238068904240,
   s2P 2101047055595, s2N 376540418027, s2N 2595300070224, s2N 1117138409404, s2N 4290376560355,
   s2N 6028260914365, s2N 2877495285782, s2N 1712802408472, s2P 1169871433683, s2N 6510767275310,
   s2N 7006320420536, s2N 2572633225959, s2P 5884682374287, s2N 6638620543519, s2N 2855339944078,
   s2P 427489186115, s2N 6943412535352, s2N 4879750562529, s2N 1461778285451, s2N 8574469432806,
   s2N 1985895129946, s2N 3930350893171, s2P 2788038082216, s2P 2726640576788, s2P 2521705325683,
   s2N 8472239018478, s2P 12480855972584, s2P 10972844070329, s2P 2257963123700,
   s2P 6515193340257, s2N 466683343996, s2P 19811513712605, s2N 1231604421638, s2N 35599167348,
   s2N 2135944530726, s2N 2917499061021, s2N 788743039128, s2N 3920246379296, s2P 5098125981358,
   s2N 2517863067019, s2P 6713626954944, s2N 5404059879146, s2P 973705052775, s2N 7276252212954]
private def s2V4S6 : List ℤ :=
  [s2P 4572542651609, s2N 11305223355123, s2N 10980746223959, s2P 9375181672349,
   s2P 7776259117616, s2N 1497282856337, s2N 3016726023817, s2P 322586424474, s2P 4516928129400,
   s2N 3013393615320, s2N 6934782975483, s2P 5483128126549, s2N 1931756024384, s2P 6552233339180,
   s2N 8771706206871, s2N 3711073713385, s2P 1693079259376, s2N 405654239266, s2N 5139467366807,
   s2N 7594370688326, s2N 10849195796662, s2P 10895763184842, s2P 4405137109798,
   s2N 10126243375740, s2P 1288610483512, s2N 2781270805511, s2P 1305494497569, s2N 2358699277256,
   s2P 3505153396540, s2N 5520101600339, s2N 14975416016157, s2N 604883005825, s2N 8413681637232,
   s2N 14087670349596, s2N 2406704980301, s2P 2772143701745, s2N 12232864130626,
   s2N 2584389608672, s2N 1715942313442, s2P 6959707044781, s2P 1135677484226, s2P 32302653034,
   s2P 10792467260821, s2N 10207013114275, s2P 2148250115896, s2P 8013946006110,
   s2P 1347719408442, s2P 26746786631386, s2P 86429888056861, s2P 148340548746400,
   s2P 221998436895145, s2P 268449301708723, s2P 323132187741488, s2P 361109727821679,
   s2P 366785866356477, s2P 361677812942844, s2P 339886740479210, s2P 295429321927231,
   s2P 244752977580995, s2P 198685684771191, s2P 153813238570590, s2P 108321534239412,
   s2P 67666720188495, s2P 37548789099783]
private def s2V4S7 : List ℤ :=
  [s2P 18861177742691, s2P 8816139448506, s2P 3949366751804, s2P 1737248097896, s2P 765319280825,
   s2P 345975647167, s2P 164939165853, s2P 84632866129, s2P 47153583870, s2P 27935630391,
   s2P 16609053648, s2P 9325056726, s2P 4777991248, s2P 2223141922, s2P 956105911, s2N 393856678,
   s2P 162891181, s2P 70556465, s2P 32500357, s2P 15628365, s2P 7569917, s2P 3573868, s2P 1610532,
   s2P 687126, s2P 278196, s2P 108256, s2P 40839, s2P 15530, s2P 5884, s2P 2049, s2P 626, s2P 174,
   s2P 47, s2P 13, s2P 2, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V4S8 : List ℤ :=
  [s2P 0]
private def s2V4 : List ℤ :=
  s2V4S0 ++
  (s2V4S1 ++
  (s2V4S2 ++
  (s2V4S3 ++
  (s2V4S4 ++
  (s2V4S5 ++
  (s2V4S6 ++
  (s2V4S7 ++
  s2V4S8)))))))
private def s2Ch5 : List Rkm128kSeg := [
  ⟨56, 275408, 1, 31,
    rkm128kMask56 511 [19776501222732170, 55053750886280835, 62021018260273405, 4999839040581893,
     28046274249896126, 47517086080266296, 50207800305293236, 6767285947684, 18648825308643328,
     90]⟩,
  ⟨56, 278633, 1, 31,
    rkm128kMask56 511 [12869628711154576, 37193194868752519, 24705736798236759, 8306823075205231,
     12559770816220106, 5695680547696, 9221879172726789, 54997165867024, 158604552310784, 68]⟩]
private def s2V5S0 : List ℤ :=
  [s2P 10771166, s2P 54499505, s2N 24781775, s2N 37846054, s2N 101750593, s2N 131258671,
   s2P 14531020, s2P 34783803, s2P 133516828, s2P 13161311, s2N 59800098, s2N 104319073,
   s2N 2395091, s2P 53860014, s2P 167943008, s2P 146012982, s2P 26986795, s2P 17545803,
   s2N 99220049, s2P 47223522, s2P 89820756, s2P 403457775, s2P 208648315, s2P 377807305,
   s2P 225880733, s2N 183392860, s2N 62711011, s2P 141738061, s2N 51151086, s2N 548987748,
   s2N 374899407, s2N 222783129, s2N 387111708, s2N 415565291, s2P 365357484, s2P 194803763,
   s2N 109799452, s2P 64863045, s2P 504552656, s2N 514495812, s2P 1103101744, s2P 2559816326,
   s2P 1698500097, s2P 1132570322, s2P 323585435, s2P 48738200, s2P 379347874, s2P 362168657,
   s2N 199908972, s2N 135857324, s2P 227949345, s2P 1228366835, s2P 4866799, s2P 626839789,
   s2P 34172337, s2P 806292408, s2P 1565234421, s2N 2093023642, s2N 846155880, s2N 1140385733,
   s2N 3092413061, s2N 1434612434, s2N 1451516410, s2N 1872463906]
private def s2V5S1 : List ℤ :=
  [s2P 306724127, s2P 1130878999, s2P 878269798, s2P 2082620808, s2P 487628705, s2P 1627846992,
   s2N 780225994, s2N 1352875108, s2P 1223140511, s2N 1055312034, s2N 91786936, s2P 1463208875,
   s2N 1564569788, s2P 2254169519, s2P 1111963053, s2P 5566898601, s2P 6333338923, s2P 3804578524,
   s2P 3288621339, s2N 2436836224, s2N 4763183658, s2P 1810985286, s2N 5644091579, s2N 1962854107,
   s2N 4538379727, s2N 1677665009, s2P 1586415062, s2P 3942531811, s2N 3932914935, s2N 5135804937,
   s2N 203546319, s2N 1194621588, s2N 3707107826, s2P 5709861247, s2P 1513061858, s2N 618950039,
   s2P 5342805580, s2N 3612563836, s2N 1657493277, s2N 5871921743, s2N 1185725888, s2N 2926203290,
   s2N 12255099594, s2N 5499977953, s2N 3598443211, s2P 5427694269, s2P 9245453269,
   s2P 6762799314, s2P 8971193221, s2N 1793376458, s2N 8336552589, s2N 13276220218,
   s2N 11953357128, s2N 4388955562, s2P 2823837226, s2P 5901947583, s2P 2891961634,
   s2N 1737832107, s2N 30489241621, s2N 20191445584, s2P 8669340323, s2P 5206129667,
   s2N 20477724843, s2N 40890781973]
private def s2V5S2 : List ℤ :=
  [s2N 11765750460, s2N 26752196058, s2N 33334010573, s2N 11056164758, s2P 12569026075,
   s2P 18323021028, s2P 9470046905, s2P 15282915573, s2N 19554649851, s2N 18349952454,
   s2N 13108669269, s2N 15023105853, s2N 2531426112, s2N 988163060, s2P 6354543400,
   s2N 10084071114, s2P 8487320333, s2N 6597874352, s2P 4263266217, s2P 26435254648,
   s2P 22316594051, s2P 17492374711, s2P 19195452128, s2P 10808046775, s2N 47795442769,
   s2N 58919725834, s2N 22874565119, s2N 6356895658, s2N 45564333618, s2N 22372306055,
   s2N 12084420812, s2P 64879424523, s2P 102392567615, s2P 72621392595, s2P 1092743878,
   s2P 83262488142, s2P 59196120719, s2N 12083139642, s2N 11160207583, s2N 49576623615,
   s2P 70282478611, s2P 100917125321, s2P 50672244495, s2N 16733700706, s2P 23405947735,
   s2P 95537590676, s2P 90869746276, s2P 91624127146, s2N 30249396055, s2N 138757636141,
   s2N 29585807473, s2N 53523333040, s2P 86488549760, s2N 76136743797, s2P 41848451707,
   s2P 79201937379, s2P 99504343487, s2P 152053735447, s2P 4537119059, s2P 111189277328,
   s2P 181336493485, s2P 269547263643, s2P 199606383386, s2P 138122945938]
private def s2V5S3 : List ℤ :=
  [s2P 112773044592, s2N 28869751610, s2N 84513638097, s2N 24748641484, s2P 145077807106,
   s2P 28093485558, s2N 77590366892, s2N 193956785648, s2P 39450384556, s2P 32588174033,
   s2N 86919563265, s2N 85960298606, s2N 74917797853, s2N 7187134531, s2N 129867362957,
   s2N 89906374163, s2N 63447815420, s2N 184064252795, s2P 28435511189, s2N 49451116253,
   s2N 186544416912, s2P 97170119806, s2P 30375402792, s2P 89329410701, s2P 98554449000,
   s2N 96341552261, s2N 197949967978, s2N 52148021163, s2N 64434646660, s2P 883059583,
   s2N 126416951671, s2P 70341644923, s2P 175728056218, s2P 53178680088, s2N 68496234031,
   s2N 49875785600, s2P 21392120988, s2P 193184397035, s2P 182547261303, s2P 494795393974,
   s2P 249589840466, s2P 30839466851, s2P 20681503631, s2P 164256504797, s2P 31168399569,
   s2P 195599758931, s2P 285159227478, s2P 313590879766, s2P 184037950822, s2N 134091455617,
   s2N 56398916329, s2N 37226362103, s2N 242504699405, s2N 73069475248, s2P 180218929376,
   s2P 341175846781, s2P 30451575535, s2N 192445723585, s2N 118600315603, s2N 383013951213,
   s2N 369374427699, s2N 662799421947, s2N 374022286296, s2N 259417956252]
private def s2V5S4 : List ℤ :=
  [s2P 162451396753, s2P 99032777799, s2N 350163150694, s2N 466765890431, s2P 696755579358,
   s2P 1180824306295, s2P 879256364642, s2P 1086504468127, s2N 769435793373, s2N 975143963199,
   s2N 576603131532, s2P 114565934879, s2N 997689695295, s2P 301535866143, s2N 210794559184,
   s2P 220343840037, s2P 1997942554003, s2P 869025781160, s2P 1147644220909, s2P 38500619963,
   s2N 22442872793, s2P 140222438469, s2P 2669414909996, s2P 4045241681523, s2P 2087957696751,
   s2N 193976889500, s2N 945534787712, s2P 491452445328, s2P 342874444721, s2N 488739040431,
   s2P 753864454409, s2P 516079285098, s2P 1277353385483, s2P 371657222438, s2N 929526806401,
   s2N 690196566247, s2N 1437407758868, s2N 2701121073059, s2P 794434821037, s2P 1461841545524,
   s2N 809672353749, s2N 1030876990700, s2P 1426209809186, s2P 780442775771, s2N 4839121998178,
   s2N 2955355089942, s2N 3462216656978, s2N 4013358181729, s2N 2685138276891, s2N 6378374694588,
   s2N 1809625513826, s2P 587531757808, s2P 2850906778200, s2P 3122238535568, s2P 5989436811779,
   s2P 5165265464992, s2P 8458402255611, s2P 2931267616765, s2N 1098392439282, s2N 1705382285924,
   s2P 3635982970334, s2N 5403203504532, s2N 2381736346751, s2N 10218944538699]
private def s2V5S5 : List ℤ :=
  [s2P 945920587350, s2P 5155360118362, s2P 1116028553871, s2P 3779083189065, s2P 4388636007900,
   s2P 3207015072720, s2P 1463101779192, s2P 1823253614309, s2P 2421103167549, s2N 812812032519,
   s2P 2327371927974, s2P 2642203931912, s2N 2099794717020, s2N 2705173475171, s2N 1971874701792,
   s2N 2388756397265, s2P 3291459060611, s2P 4827403304407, s2P 1505043516017, s2P 635774612455,
   s2P 1373020579662, s2P 2427078828533, s2N 1534640055753, s2N 2482392358005, s2P 904518436560,
   s2P 3491320100542, s2P 1067624900949, s2P 4891074717229, s2N 751945733605, s2N 447513805886,
   s2P 156251015541, s2P 2120362597031, s2P 3104121241752, s2N 501728288190, s2N 8518592241269,
   s2N 12746346511833, s2N 3159358158685, s2P 4136706710310, s2N 3965987872562, s2N 9971115157399,
   s2P 8117830966728, s2P 666126237237, s2N 9603390191564, s2P 6384284115184, s2P 2799429186747,
   s2N 4497281073807, s2P 7690722265131, s2N 721030823056, s2P 5070899416312, s2P 9645351139210,
   s2P 9990478964123, s2N 182121477365, s2N 5960737802382, s2P 16497830548889, s2N 3454842063480,
   s2N 5180477771602, s2P 2106191193817, s2N 2009320701107, s2P 6669135263076, s2P 5356084921370,
   s2N 9705345006525, s2N 3061868785660, s2P 2475741672901, s2P 576307509020]
private def s2V5S6 : List ℤ :=
  [s2N 6818359557296, s2P 3949924620456, s2N 2488509880751, s2P 3465741035616, s2P 9115141841319,
   s2N 3557335787125, s2N 1999584447975, s2P 9094488734354, s2P 11016139356279,
   s2P 10680938242744, s2N 6984040251066, s2N 1044729326821, s2P 5924941634425, s2N 5531309948423,
   s2P 950817992602, s2P 2440408926659, s2P 5640507382902, s2N 3948452268863, s2P 5352737149235,
   s2P 3728375085722, s2N 5801714529110, s2P 1410674046423, s2P 9811567944631, s2P 3005237245116,
   s2N 4116064297071, s2P 10751664591180, s2P 8260999733410, s2P 774857597391, s2P 15776349609030,
   s2P 3989256427259, s2N 4986155764985, s2N 2670213948168, s2N 1562308903425, s2N 4002524610143,
   s2P 7289499627258, s2P 9432609749571, s2P 8437605485582, s2P 1741436365326, s2N 780145370124,
   s2N 15461711152918, s2P 6022397504445, s2P 2329847841041, s2N 6955158477654, s2P 7887336367094,
   s2P 3522248861429, s2P 4024873501889, s2P 6009420412868, s2P 4466603421989, s2P 14665497713125,
   s2N 1766238256752, s2P 1961611015904, s2P 9034162190266, s2N 4820825799093, s2P 634932825297,
   s2P 306254044747, s2P 17564590467778, s2P 62141246001458, s2P 126119520584948,
   s2P 193451833305240, s2P 258691968624800, s2P 318853871468787, s2P 362707394373072,
   s2P 379618207904678, s2P 370280350096895]
private def s2V5S7 : List ℤ :=
  [s2P 342983951553718, s2P 304323027819460, s2P 257004926787098, s2P 203765282929050,
   s2P 149906360780773, s2P 101752854798306, s2P 63723743623785, s2P 36963728558461,
   s2P 19986491467649, s2P 10153284064076, s2P 4892173978438, s2P 2259939468948,
   s2N 1015211522386, s2P 452261862003, s2P 204228494626, s2P 95578276263, s2P 47130783946,
   s2P 24220995489, s2P 12399345589, s2P 6018484334, s2P 2700727333, s2P 1126438733,
   s2P 451015753, s2P 181934053, s2P 76951806, s2P 34353216, s2P 15807076, s2P 7273391,
   s2P 3274999, s2P 1425616, s2P 597814, s2P 239479, s2P 94013, s2P 35191, s2P 11679, s2P 3365,
   s2P 901, s2P 249, s2N 72, s2P 19, s2P 3, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0]
private def s2V5S8 : List ℤ :=
  [s2P 0]
private def s2V5 : List ℤ :=
  s2V5S0 ++
  (s2V5S1 ++
  (s2V5S2 ++
  (s2V5S3 ++
  (s2V5S4 ++
  (s2V5S5 ++
  (s2V5S6 ++
  (s2V5S7 ++
  s2V5S8)))))))
private def s2Ch6 : List Rkm128kSeg := [
  ⟨56, 277231, 1, 31,
    rkm128kMask56 511 [6749518168023102, 1709418416567260, 67839216141611144, 16408166632523047,
     13524828846736811, 13511627944609689, 19604879690375522, 1690241800735939, 4503603922337792,
     124]⟩,
  ⟨56, 278247, 1, 31,
    rkm128kMask56 512 [54068823593803676, 31389836805129519, 65073839561754212, 27260195636526055,
     43351217970582928, 9010500919579796, 123506916501066, 27030463158556226, 0, 160]⟩]
private def s2V6S0 : List ℤ :=
  [s2P 7809689, s2N 39157007, s2P 49508187, s2N 26823166, s2P 95977498, s2P 54928557,
   s2P 109834115, s2P 21313628, s2P 68895680, s2P 84366073, s2P 10424616, s2N 124392916,
   s2N 69837260, s2N 8355431, s2N 1978926, s2N 43086665, s2N 205528873, s2N 82304567,
   s2N 40472359, s2P 54108128, s2P 87794247, s2P 125097789, s2N 68837899, s2P 145561602,
   s2P 54439119, s2P 300278118, s2P 87311023, s2N 166681856, s2N 340875979, s2N 578256356,
   s2N 162183145, s2P 568235124, s2P 657064616, s2P 143080141, s2P 117744279, s2N 477281263,
   s2P 347037803, s2N 327654738, s2P 437448043, s2P 516588866, s2P 324346044, s2P 1065222430,
   s2N 77764998, s2N 444338931, s2N 370867276, s2N 46750163, s2P 469867687, s2N 87651983,
   s2N 1266907084, s2N 2057946688, s2N 1423911568, s2N 511038057, s2N 2473387102, s2P 736365609,
   s2P 837730738, s2P 991518933, s2P 1368208811, s2P 518470018, s2N 798494395, s2P 133254515,
   s2P 593670107, s2N 586678394, s2N 1171152814, s2N 1687352967]
private def s2V6S1 : List ℤ :=
  [s2N 1278315851, s2N 1510585352, s2N 254557059, s2P 423812962, s2P 2786756972, s2P 3713286447,
   s2P 2641371565, s2P 1458632769, s2P 248012107, s2N 924906394, s2N 1233085299, s2N 1773063349,
   s2N 133244406, s2N 466815335, s2N 172886229, s2P 530777624, s2P 647402255, s2N 1480046799,
   s2P 1111044769, s2P 634210716, s2P 1941808396, s2N 2157457815, s2N 6858909252, s2N 1482139126,
   s2N 2131909336, s2P 3628073502, s2N 7605031390, s2N 3351401613, s2N 1610214969, s2P 4080685066,
   s2P 3964519415, s2P 2430422480, s2P 2151391082, s2P 4710418596, s2N 2144342993, s2P 2977825736,
   s2P 11525794200, s2P 2569576416, s2N 1187838993, s2N 296234831, s2N 1620363595, s2N 1796086326,
   s2P 2757278920, s2P 1364698413, s2P 3593930915, s2N 3315835193, s2N 1767744850, s2N 1654972484,
   s2N 3262265856, s2P 4525337253, s2N 1523559135, s2N 6058897402, s2N 447069741, s2P 6943606208,
   s2P 5086128731, s2N 13858514053, s2N 4423106053, s2P 11583868402, s2N 10692173148,
   s2P 5239723232, s2P 19199268490, s2P 1348753025, s2N 1657139387, s2N 1277493424]
private def s2V6S2 : List ℤ :=
  [s2P 21398775564, s2P 5390366009, s2P 12644997579, s2P 25979525913, s2P 26438362411,
   s2P 20867189586, s2N 10174642922, s2N 4634069981, s2P 11694299488, s2P 6518240814,
   s2P 11540927316, s2P 7382643004, s2N 11619263511, s2N 42911505569, s2N 44101108718,
   s2N 17649293614, s2N 3110735952, s2N 4993123351, s2N 2921084360, s2N 9115891378,
   s2P 1956162096, s2P 7152794506, s2P 27306185262, s2P 5966299472, s2N 18585685306,
   s2N 29341128679, s2P 218832151, s2P 13568981291, s2N 19631691001, s2N 5601476191,
   s2P 6713394071, s2N 6959632417, s2N 52520114493, s2N 45972364592, s2N 26271566310,
   s2N 6518806691, s2P 36344281364, s2P 47421219728, s2P 45224415049, s2P 64845552192,
   s2P 39531974062, s2P 57723221492, s2P 67432502905, s2P 395739762, s2N 52688292176,
   s2N 281874953, s2P 67607049261, s2P 77143426660, s2P 133010230847, s2P 124460673675,
   s2N 5387513457, s2N 65155788126, s2N 70615807128, s2N 54875152937, s2N 69060646164,
   s2N 14927356597, s2P 66988683794, s2P 103891166356, s2N 119082214964, s2N 133897219448,
   s2N 206834863, s2P 52758910306, s2N 29667623206, s2N 52127081794]
private def s2V6S3 : List ℤ :=
  [s2N 25590930108, s2N 23410410359, s2N 85573987876, s2P 76462845460, s2P 215949790262,
   s2P 95377120512, s2N 3304205537, s2N 161025094084, s2N 146761235131, s2N 170088899603,
   s2N 281610182957, s2N 237035309509, s2N 163873709487, s2N 36822935590, s2N 103679223458,
   s2N 23325328749, s2N 70166981908, s2N 41695475105, s2N 106084897626, s2N 77153015750,
   s2P 260992502066, s2P 38104469153, s2N 152685195598, s2N 63403960019, s2P 92963102801,
   s2N 41877311358, s2N 45874519117, s2P 80215314379, s2N 53722130763, s2N 69168108034,
   s2P 89063563733, s2N 40722695859, s2P 231873033098, s2N 133968446389, s2N 121628554022,
   s2N 146457076171, s2N 47936823735, s2N 58646520165, s2N 104622403830, s2N 23215723991,
   s2P 30957525964, s2N 44454879106, s2N 148271579564, s2N 184817977437, s2N 92545746978,
   s2N 75624665836, s2N 14923440074, s2P 538393397437, s2P 14279699721, s2N 467771544787,
   s2N 79704801, s2P 247447618921, s2P 163410414010, s2N 130275930749, s2P 31866443653,
   s2P 124177617516, s2P 121607956128, s2P 8969954644, s2P 86778598094, s2N 245311843370,
   s2P 16524099567, s2N 322976638044, s2N 250019164171, s2N 41976815201]
private def s2V6S4 : List ℤ :=
  [s2N 69700177274, s2P 209252645639, s2P 79816298887, s2N 31376369748, s2N 180537886636,
   s2P 9418700887, s2P 514979833311, s2P 943739626524, s2P 827713114706, s2P 554129617500,
   s2N 708354611355, s2N 46560332395, s2P 673093891271, s2P 477070776632, s2N 971144438285,
   s2N 1986499846284, s2N 833875328250, s2N 520450733312, s2N 745375099430, s2N 884074402752,
   s2N 358693938509, s2N 302827709797, s2N 848182627557, s2N 1631360819163, s2N 2257486361885,
   s2N 1556776134644, s2N 1162973020187, s2P 794255504562, s2P 198321638091, s2P 1422683994858,
   s2P 1632685444581, s2P 1921000307948, s2N 2442703999974, s2N 3550124962157, s2N 2738992777495,
   s2N 1510512934267, s2N 1308667910538, s2P 305336783491, s2P 2029390978366, s2P 1384693935162,
   s2N 229937908430, s2N 801739970583, s2N 629650110031, s2N 1340047779122, s2N 1353236332960,
   s2N 2027261286263, s2P 614212195316, s2P 4261128087770, s2P 1328671213772, s2N 638148485954,
   s2P 3509098584466, s2P 2126086070027, s2P 1505414673836, s2N 1312658175841, s2N 1336861074807,
   s2N 3431731604917, s2N 2121764270545, s2P 1932701197516, s2N 1967292675420, s2N 6771958501435,
   s2N 2482653015418, s2N 4470200788484, s2N 8702436090798, s2N 7089184944859]
private def s2V6S5 : List ℤ :=
  [s2N 2516441293444, s2N 7606296806191, s2P 2247096153753, s2P 84482862930, s2P 4634238078779,
   s2P 3671500295356, s2P 4226226056210, s2P 3083719502689, s2N 1769150933229, s2N 6025483049261,
   s2N 2955837383743, s2N 3325757999268, s2N 2103678561241, s2P 1355991829804, s2P 4029933742020,
   s2P 4494741056320, s2P 4530597923349, s2P 83327989174, s2N 3002697001035, s2N 4118775442220,
   s2P 499542514934, s2P 1745674473652, s2N 2733593976399, s2N 1614579441821, s2N 5515041489621,
   s2P 1953172121750, s2P 2489182551318, s2N 568824691240, s2N 2906201477989, s2N 561866360729,
   s2P 3055454352544, s2P 765932677328, s2N 1188374951807, s2P 1422986715029, s2P 2573495182409,
   s2P 1648547041208, s2P 2151817346696, s2P 4195490589249, s2P 149254958217, s2N 414165237932,
   s2P 3364358872814, s2P 6946844660682, s2P 15737194049165, s2P 18534496199328,
   s2P 3013883011144, s2N 6855282108613, s2N 6480094635793, s2N 8334257865514, s2N 1002901763934,
   s2N 1634028616921, s2N 619165156285, s2N 5534435064675, s2N 1783675970255, s2N 2345133373781,
   s2P 6146370173825, s2P 7944536104463, s2P 10477994127911, s2P 6683167774405,
   s2P 12038022905536, s2P 3071832033366, s2P 4364585743588, s2P 294727058545, s2P 427785181001,
   s2N 4657757065522]
private def s2V6S6 : List ℤ :=
  [s2N 14062418365815, s2N 3451069065035, s2N 832449074363, s2P 4356659191049, s2N 12967904020399,
   s2P 8011276041557, s2P 2474528800450, s2N 3013432278095, s2P 1335447401128, s2P 1468622472743,
   s2N 2754013278720, s2P 3658637668137, s2N 3238220331918, s2N 725865518324, s2P 809855898486,
   s2P 12440482494691, s2P 7949107829180, s2N 6326190226067, s2N 2371302512209,
   s2N 12141690161287, s2N 7001203695933, s2N 7771160125045, s2N 6579578586741, s2N 1342476335373,
   s2P 5320094749963, s2N 1426647053402, s2N 1941216767424, s2P 2486568450450, s2P 3710997896438,
   s2N 1248219385421, s2P 2881999733809, s2P 7184345853034, s2N 6929079975713, s2P 1971239300934,
   s2P 2843104345755, s2P 18973177082769, s2P 1523961037148, s2P 2762297795200, s2P 4526834295358,
   s2N 11246023337620, s2N 9351851620873, s2N 4200096826412, s2P 7864386760062,
   s2P 12221613750509, s2N 1288598014538, s2P 2315135601186, s2P 2355997770684, s2N 3573816849520,
   s2N 4725905942900, s2N 4852067439609, s2N 1662110225547, s2N 5883453968759, s2P 3883942442949,
   s2P 10959762621875, s2P 5543334667951, s2P 4139611748403, s2P 12690329782477,
   s2P 1110657673099, s2P 986771507723, s2P 10278788148853, s2P 6851722772329, s2P 3135507973973,
   s2P 1984421249982, s2P 18730323431547]
private def s2V6S7 : List ℤ :=
  [s2P 61593194010274, s2P 126422676997285, s2P 204767125181161, s2P 281187823903141,
   s2P 339477393377459, s2P 374816076682913, s2P 383499239831047, s2P 372648852208647,
   s2P 340061975167473, s2P 291990820898238, s2P 235696028100924, s2P 176383103809402,
   s2P 122425660885344, s2P 79976441551223, s2P 49315117418324, s2P 28220352095498,
   s2P 14698141221036, s2P 6936924733675, s2P 3019810915623, s2P 1262312969776, s2P 534362557692,
   s2P 238602772458, s2P 112879240525, s2P 55170162281, s2P 27020559562, s2P 12966392951,
   s2P 6014974329, s2P 2680748926, s2P 1147244618, s2P 475883443, s2P 190250913, s2P 78198775,
   s2P 31509610, s2P 11013509, s2P 3362545, s2P 1095430, s2P 456809, s2P 214367, s2P 95210,
   s2P 38009, s2P 13652, s2P 4443, s2P 1312, s2P 348, s2P 81, s2P 14, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0]
private def s2V6S8 : List ℤ :=
  [s2P 0]
private def s2V6 : List ℤ :=
  s2V6S0 ++
  (s2V6S1 ++
  (s2V6S2 ++
  (s2V6S3 ++
  (s2V6S4 ++
  (s2V6S5 ++
  (s2V6S6 ++
  (s2V6S7 ++
  s2V6S8)))))))
private def s2Ch7 : List Rkm128kSeg := [
  ⟨56, 277965, 1, 31,
    rkm128kMask56 513 [7308181051000341, 27518303922512386, 64760962685117668, 43557969570298881,
     60925475023318686, 7893067287519481, 23783587440476904, 18633043464950665, 6, 276]⟩,
  ⟨56, 277818, 1, 30,
    rkm128kMask56 513 [2663420150834431, 51060762046641598, 37223880688239559, 17131381383519375,
     27769852011504598, 9078024100248130, 13212959872026, 70440452227339, 2251799813685346, 256]⟩]
private def s2V7S0 : List ℤ :=
  [s2P 7799661, s2P 39447959, s2P 46956249, s2P 41925035, s2P 39313903, s2P 64934401,
   s2P 17653340, s2N 55802681, s2P 32634959, s2P 172040031, s2P 16372703, s2N 101179225,
   s2P 84373518, s2P 55323573, s2P 30410161, s2N 2049113, s2P 132206344, s2P 105972713,
   s2P 65358095, s2P 14604267, s2P 27602683, s2N 258004972, s2N 48837455, s2N 90839178,
   s2N 59485887, s2P 29966641, s2P 73320776, s2N 73105308, s2N 295324847, s2N 391004064,
   s2N 147541646, s2P 148105953, s2P 300104057, s2P 140105911, s2P 701122526, s2P 829210360,
   s2P 348587551, s2P 37204534, s2P 187294005, s2P 694928927, s2P 122289076, s2N 342506505,
   s2N 791355782, s2N 543366353, s2N 378306250, s2N 546261512, s2P 69723625, s2P 356182339,
   s2P 456259344, s2N 982033347, s2N 651813922, s2N 906773936, s2P 106829035, s2P 1399288654,
   s2P 639465189, s2P 1349258892, s2P 1786423864, s2P 782870134, s2P 1300465462, s2P 1629912881,
   s2P 1378178448, s2P 559025609, s2P 396523684, s2N 1479947061]
private def s2V7S1 : List ℤ :=
  [s2N 561761113, s2P 708571865, s2N 900738218, s2N 591577834, s2N 1347944191, s2N 1378954049,
   s2N 1646592238, s2N 1247952306, s2N 963198785, s2P 968420483, s2P 1220966599, s2P 978545820,
   s2N 867710814, s2P 343060270, s2P 1543717315, s2P 4477220885, s2P 1859955384, s2P 3035626431,
   s2P 400613841, s2N 1571104462, s2P 932440290, s2P 1574116103, s2N 3171429320, s2N 1759344297,
   s2N 4667986447, s2P 1501685756, s2P 6310367549, s2N 3472453019, s2N 2867984933, s2N 3773728780,
   s2N 2044356719, s2N 2994707069, s2P 1362037251, s2P 4240657865, s2P 5743526572, s2P 9738610002,
   s2P 2006936875, s2N 3592619994, s2P 1769413496, s2P 1270593635, s2N 1007346820, s2P 4573178783,
   s2N 5888865442, s2N 595101596, s2P 4480457309, s2N 1581324267, s2N 1945154003, s2N 4918478032,
   s2N 2493462498, s2N 7669263102, s2P 3988788733, s2P 3872390302, s2P 1062397397, s2N 7610549652,
   s2N 8096267591, s2N 9222202128, s2P 3528344328, s2P 4450666920, s2N 19731662871,
   s2N 8602487606, s2P 11545350085, s2P 6353940298, s2P 1692559244, s2P 4727991164]
private def s2V7S2 : List ℤ :=
  [s2N 12337148896, s2P 4714362285, s2P 8120460832, s2N 8920106251, s2P 2351174011,
   s2N 1202606527, s2N 3716519533, s2P 1555895135, s2N 20371852554, s2P 3524989013,
   s2P 12512266602, s2P 22155225265, s2P 4635207705, s2P 19697057926, s2P 12190980489,
   s2P 5855456998, s2P 38651960045, s2P 17870124547, s2N 13985446591, s2N 6374871182,
   s2N 21026917580, s2N 34327843036, s2N 15846385938, s2N 6392495756, s2N 4956604515,
   s2P 29220815853, s2P 39372735577, s2P 1836511982, s2P 14634698820, s2P 19441201206,
   s2P 22794493249, s2P 22605234560, s2P 25605002878, s2N 3588304417, s2N 27989640160,
   s2N 18266353148, s2P 8665050241, s2N 677316933, s2N 44322776686, s2N 31382595199,
   s2N 9153457077, s2P 35234485694, s2N 11876275634, s2N 49536945725, s2P 31301803318,
   s2P 2844958948, s2P 53685971282, s2N 18884342841, s2P 2504735178, s2P 8984728395,
   s2P 2028993516, s2N 32271101566, s2N 104276383069, s2P 60050147022, s2P 40158807160,
   s2P 128670879670, s2P 100830172227, s2P 18516254484, s2P 29949903761, s2N 60239675354,
   s2N 52299796325, s2P 102229555373, s2P 171397009166, s2P 70667833048]
private def s2V7S3 : List ℤ :=
  [s2P 15610040873, s2P 137611934323, s2N 164399274643, s2N 1709298383, s2N 54074158336,
   s2P 42496462450, s2N 64127398777, s2N 26479291476, s2N 23893695158, s2N 67995950047,
   s2N 51670390307, s2N 17690273800, s2N 1350293683, s2P 14743142565, s2P 222775644061,
   s2N 7848518213, s2N 164186104750, s2N 85902789270, s2P 225065277308, s2P 72129388553,
   s2N 139738696779, s2N 5002213783, s2N 40371832236, s2N 331316774203, s2P 341311151925,
   s2P 190971851104, s2N 73550512973, s2P 60012533307, s2P 13659684513, s2N 93866277193,
   s2N 13155076202, s2P 229519718095, s2P 102431377113, s2N 65505401720, s2N 82214586522,
   s2N 1392692633, s2P 36391779141, s2N 51216275870, s2N 18663223307, s2N 94355171817,
   s2P 18745638299, s2P 32497562789, s2P 130236798130, s2P 85757559800, s2P 169843364686,
   s2P 233500381235, s2P 28357806182, s2N 111577705085, s2P 176045229183, s2P 175824002665,
   s2P 188352582204, s2N 411231119573, s2N 406127188222, s2P 229954862995, s2N 256085075556,
   s2P 368473287592, s2N 133003804682, s2N 94264852516, s2N 13087980818, s2N 8014031904,
   s2N 77216865666, s2P 184347972909, s2N 65848650257, s2N 284099300555]
private def s2V7S4 : List ℤ :=
  [s2N 259659224600, s2P 53837379046, s2P 128918312982, s2N 220572050414, s2N 325884785809,
   s2N 190170157076, s2P 512924646760, s2P 193995854989, s2P 241382520717, s2N 101027983100,
   s2N 265205652818, s2N 185437416768, s2N 149965573061, s2P 661418326024, s2P 972926050211,
   s2P 890252895567, s2P 573928843747, s2P 485259715771, s2N 649501541903, s2N 1515289161116,
   s2N 977889133102, s2P 443141129558, s2P 320391174504, s2P 645558250040, s2P 319190103854,
   s2N 540887578849, s2N 92094523125, s2P 242793280355, s2P 1422264781136, s2P 1241060660511,
   s2N 1215361840681, s2N 307559421050, s2N 641013512790, s2P 1719862458218, s2P 1649378210935,
   s2N 3160176110795, s2N 2103935660749, s2P 1542675182947, s2P 970988430758, s2N 220272236107,
   s2P 625443020740, s2P 1044512366534, s2P 3868080486821, s2P 1806135652191, s2N 2073129615497,
   s2N 2217035860351, s2P 1076963826652, s2P 1343449398608, s2P 1678246477262, s2P 1676599622440,
   s2N 1903527730858, s2N 5487600054033, s2N 1253346503916, s2P 3437588455075, s2P 2181878088438,
   s2P 4387423415878, s2N 3204101040717, s2N 3399930554485, s2N 319121873098, s2N 698266460318,
   s2N 5313118600765, s2N 4251858170641, s2P 4321430684281, s2N 2735296480164]
private def s2V7S5 : List ℤ :=
  [s2N 2000219426743, s2N 4989566478592, s2N 2206517706624, s2P 3342988542257, s2N 2917237264806,
   s2N 1692781222850, s2N 121576159689, s2P 3733372194660, s2P 1103827283429, s2N 459536621888,
   s2N 6114371193626, s2N 6738083766791, s2N 4904614001818, s2P 1544442780888, s2N 64998873545,
   s2N 9592971147224, s2N 2039291277292, s2P 2054906318106, s2N 5896258181457, s2N 1795916599508,
   s2P 335137483033, s2N 7177933358614, s2N 4142745029246, s2N 892125687291, s2N 4876303831943,
   s2N 1023180217326, s2N 327443132285, s2N 3309944358449, s2P 950584751519, s2P 845184188823,
   s2N 738365888149, s2N 1382912087108, s2P 1512358295162, s2P 5687739643478, s2P 591783096092,
   s2N 4232345183564, s2P 2314054452214, s2N 1137916162972, s2N 2096050756514, s2P 920082893323,
   s2P 2131868044655, s2P 4894948955398, s2N 2384029492604, s2P 4602318620, s2N 1450423205759,
   s2N 2572507987811, s2P 1782564756454, s2P 3613902905425, s2P 9125550564794, s2P 4178478510333,
   s2N 8188954644322, s2N 12721604176126, s2N 16149772471159, s2N 14026952432986,
   s2N 4678406098411, s2N 4622514219794, s2P 3211803143164, s2N 576759718311, s2P 10794069872972,
   s2N 8257098707006, s2N 9123595800776, s2P 4488277879162, s2P 9559732378474, s2N 3841845091311]
private def s2V7S6 : List ℤ :=
  [s2P 4832398388752, s2N 15466937180939, s2N 8998255612222, s2N 2408090107193, s2P 9471848800060,
   s2P 5106811437839, s2N 1597614122239, s2N 6429362139024, s2N 2916703305536, s2P 3736249144108,
   s2P 7653504714733, s2N 915635392441, s2P 1136464164056, s2P 5405948962997, s2N 1731898200889,
   s2P 4329721149007, s2P 8382131442554, s2P 3213441811437, s2P 2877986628487, s2N 815158356933,
   s2P 3123870420890, s2P 6966293787029, s2P 6669317525755, s2P 805836038732, s2N 1313479766646,
   s2P 541734343709, s2P 2895518758770, s2N 2165874951046, s2N 11175155366836, s2P 12969350533203,
   s2N 5290598174968, s2N 6737708818682, s2P 11470786766285, s2N 7391275856828, s2N 3531776217953,
   s2N 7200275456570, s2N 9992838918902, s2N 402646655683, s2P 3296768179452, s2P 7635775337006,
   s2P 6656782035200, s2P 4821167703413, s2N 1369177534454, s2N 9463792429382, s2N 1425678668091,
   s2N 10200972384505, s2N 10333773912622, s2N 6969326652687, s2N 10558212364449,
   s2P 3284101074919, s2N 4653676308635, s2P 8468098258863, s2P 1060806660742, s2N 7971064739309,
   s2N 3237711360106, s2N 3098774353940, s2P 2289669101803, s2P 10890133509284, s2N 5248246648072,
   s2P 2836623579743, s2N 8072826391481, s2P 6396320638345, s2P 9269090776019, s2P 3063703534424]
private def s2V7S7 : List ℤ :=
  [s2P 1069173824663, s2P 2328917863924, s2P 2941445796918, s2P 8431478993631, s2P 2694381163918,
   s2P 9035775631448, s2P 4781522174037, s2P 31455455359160, s2P 96700757187881,
   s2P 178068160761590, s2P 260155994590555, s2P 328466614813200, s2P 374268770447114,
   s2P 394418467898203, s2P 387618681801576, s2P 354852940296829, s2P 302167011167094,
   s2P 239768463458067, s2P 177887075279328, s2P 123628422678719, s2P 80421197385840,
   s2P 48851441160990, s2P 27658803227042, s2P 14602414302219, s2P 7216289637591,
   s2P 3364493558237, s2P 1498066211921, s2P 647274002583, s2P 276200978819, s2P 118134144701,
   s2P 51011811223, s2P 22185158295, s2P 9625027627, s2P 4118815459, s2P 1723988316,
   s2P 702796630, s2P 278295384, s2P 106614289, s2P 39310817, s2P 13920717, s2P 4763644,
   s2P 1601558, s2P 540530, s2P 185557, s2P 64398, s2P 22096, s2P 7301, s2P 2271, s2P 651,
   s2P 168, s2P 36, s2N 4, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0,
   s2P 0, s2P 0]
private def s2V7S8 : List ℤ :=
  [s2P 0]
private def s2V7 : List ℤ :=
  s2V7S0 ++
  (s2V7S1 ++
  (s2V7S2 ++
  (s2V7S3 ++
  (s2V7S4 ++
  (s2V7S5 ++
  (s2V7S6 ++
  (s2V7S7 ++
  s2V7S8)))))))
private def s2Ch8 : List Rkm128kSeg := [
  ⟨56, 274468, 1, 30,
    rkm128kMask56 510 [21251491315220350, 44342185023251330, 37649505962314517, 54926307319297080,
     71238464436078447, 11690471965885996, 5075413326560275, 6902200562155533, 5070947627303776,
     53]⟩,
  ⟨56, 277734, 1, 30,
    rkm128kMask56 509 [18849122725944280, 7788390772441001, 7989912864220713, 57381006309058170,
     11180946898229891, 167272973069056, 1549954892303874, 149693772599524, 8796093035016, 16]⟩]
private def s2V8S0 : List ℤ :=
  [s2P 1473342, s2N 6353262, s2N 11971979, s2P 33424275, s2P 54247936, s2P 19411277, s2P 76744444,
   s2P 46767567, s2P 78550702, s2N 127500454, s2P 86785224, s2P 14268840, s2P 157668062,
   s2N 21003240, s2N 17100342, s2N 75235616, s2P 64350664, s2N 76231547, s2N 34611231,
   s2N 118114784, s2N 24029256, s2N 132748246, s2N 71386636, s2P 80888061, s2P 237189355,
   s2N 78876969, s2P 43827813, s2P 58481489, s2P 46793066, s2N 107211482, s2P 104829245,
   s2P 140694369, s2N 113786865, s2N 15044913, s2P 469526493, s2P 369311918, s2P 45573660,
   s2P 213348290, s2N 67157016, s2N 327105285, s2N 641406054, s2N 591078443, s2N 683220067,
   s2P 116410316, s2N 210529355, s2N 280815421, s2N 1210279491, s2N 48170874, s2P 464586555,
   s2P 1453883432, s2P 980511333, s2P 494412728, s2P 469626312, s2P 388776626, s2N 238695692,
   s2N 376278679, s2P 413619463, s2P 717688064, s2N 137601620, s2P 900675665, s2P 68903011,
   s2N 259940233, s2P 4694336, s2N 391441679]
private def s2V8S1 : List ℤ :=
  [s2N 1272381185, s2N 2582993558, s2N 927696719, s2N 32027928, s2P 2430312143, s2P 377486325,
   s2P 1824252987, s2N 305682983, s2N 1450358108, s2P 646473969, s2P 981662606, s2P 343834064,
   s2P 5577114, s2P 170891077, s2P 1894594738, s2P 46986257, s2P 3439950459, s2N 490786148,
   s2N 1050186845, s2P 2889878277, s2P 1706911638, s2N 2081367700, s2N 969623319, s2N 1439053759,
   s2N 1070164277, s2N 5629814806, s2N 1450754146, s2N 2034619194, s2N 3129002766, s2N 3956651545,
   s2N 6263223474, s2N 4725390032, s2N 2283540091, s2N 1005775302, s2P 2809231848, s2N 4217987355,
   s2N 7524535172, s2N 4905811893, s2P 2349536212, s2P 3039450506, s2P 8973782988, s2P 2153863946,
   s2P 1781995228, s2P 1577922086, s2P 6047342098, s2N 3746032244, s2N 374928247, s2N 1538043529,
   s2P 346951547, s2N 2156459921, s2N 7841602911, s2N 4175269011, s2N 2100562518, s2N 1818128762,
   s2N 8103610060, s2N 4108276428, s2P 10586646146, s2P 1606048499, s2P 811335455, s2P 5728013192,
   s2P 2301831197, s2P 14729233433, s2P 7362875885, s2P 16949229427]
private def s2V8S2 : List ℤ :=
  [s2N 10244202447, s2N 1787965342, s2N 3114137904, s2P 1593985911, s2N 8575898907,
   s2N 7010482565, s2N 12238464513, s2N 17717911835, s2N 5073903432, s2P 1128506403,
   s2P 2753745890, s2P 11779857153, s2P 23828741340, s2N 6580924445, s2N 21967196409,
   s2P 15096041296, s2P 13626645336, s2N 10431446319, s2N 14810305504, s2N 7298845214,
   s2P 4044261840, s2N 4897150390, s2N 9008586140, s2N 5991208121, s2N 11895434628,
   s2N 4477502215, s2P 16802492421, s2P 28567069540, s2P 7095974135, s2N 22802634478,
   s2N 46353316325, s2N 11390909567, s2N 18442238096, s2N 1267056013, s2P 36024551975,
   s2P 14571361145, s2P 16636709760, s2N 23610920577, s2P 694377810, s2N 3582122800,
   s2N 7570662175, s2N 47230550424, s2N 48025337235, s2N 74288092445, s2N 65517812712,
   s2N 21897269643, s2N 18314783909, s2P 27083678109, s2P 29116303897, s2N 37801639338,
   s2N 9603738910, s2P 19945104924, s2P 20616241341, s2P 19101623191, s2P 18787363214,
   s2P 16380390994, s2P 34739747597, s2P 68587405777, s2N 290045309, s2N 8384191507,
   s2N 46472914392, s2N 71224861741, s2N 51198490113, s2N 21819211725]
private def s2V8S3 : List ℤ :=
  [s2P 12931160287, s2P 103378931545, s2P 131974647627, s2P 239970123567, s2P 83472512153,
   s2N 13652572329, s2P 13041772445, s2N 71834278873, s2N 18221917910, s2P 17238097510,
   s2N 57195879984, s2P 106796640765, s2P 176780666863, s2P 51466280113, s2P 4466581201,
   s2P 39040653936, s2P 32686510687, s2P 29730814638, s2P 154472206268, s2P 22771816367,
   s2P 73878152605, s2N 103242238446, s2N 203306577628, s2N 308166649056, s2N 259503396495,
   s2N 162083883462, s2P 8694901849, s2N 40993990375, s2N 59380449849, s2N 176921237685,
   s2P 11111353900, s2P 237107199884, s2P 239543833413, s2P 96916525707, s2N 89228004536,
   s2N 17651012781, s2N 105714422117, s2N 159729340501, s2N 156845240401, s2P 33101700260,
   s2P 10228175134, s2N 144543697893, s2P 22839471316, s2P 117762678895, s2N 1094474431,
   s2P 129694384031, s2N 84489623186, s2P 59199338388, s2P 123277242776, s2P 122145088049,
   s2P 102986444650, s2N 189272321639, s2N 23280757548, s2N 350630016049, s2N 283276827212,
   s2N 372211293459, s2N 355414621428, s2N 193880117611, s2N 28252917372, s2N 34618675265,
   s2N 196198371026, s2P 179280461865, s2P 169268838143, s2P 528557832087]
private def s2V8S4 : List ℤ :=
  [s2P 16324644122, s2P 154661615857, s2P 86884087201, s2P 221666929596, s2N 5681463448,
   s2N 48642370728, s2P 171570066189, s2P 268407904439, s2N 208246962887, s2N 240109664813,
   s2P 187223955769, s2P 375908005740, s2P 351769378032, s2N 555010266385, s2N 103986348771,
   s2N 266755427750, s2N 388928047254, s2P 1332793055, s2P 84641061799, s2P 397147316935,
   s2P 842456445883, s2P 865744408347, s2P 1094760255165, s2P 479447871388, s2P 86599567074,
   s2N 66011816967, s2N 240900099815, s2N 697776734070, s2N 1304689194481, s2N 1281668155865,
   s2N 1223536044517, s2N 440977288767, s2N 587505887427, s2N 177431928794, s2P 1425388884222,
   s2N 156066251024, s2P 890461378752, s2N 65281688604, s2P 395609155518, s2P 1514807158902,
   s2P 4302889272222, s2P 2664106864792, s2P 1037072811603, s2P 556389791508, s2N 963358821399,
   s2N 783408105437, s2N 1419409177181, s2N 490875381324, s2N 259165384685, s2P 495274540318,
   s2N 1281552183510, s2N 4644556731522, s2N 4194939681850, s2N 1905003551015, s2N 2084175204176,
   s2P 1899452340612, s2P 97346028404, s2N 577760480117, s2P 1164506417080, s2P 4924598237923,
   s2P 3024218762738, s2P 3162546664373, s2N 1970639345943, s2N 3481645955898]
private def s2V8S5 : List ℤ :=
  [s2N 6522843789543, s2N 5101926230218, s2N 981806386650, s2P 26536435185, s2N 1001573818579,
   s2N 3955590941236, s2N 1857247687627, s2P 3405945322912, s2P 2320470656543, s2N 10159940417507,
   s2N 1145788002351, s2P 144281582071, s2N 4292537836025, s2N 648171986102, s2N 2172898467692,
   s2N 3685951493689, s2P 8318972278082, s2P 2053902557660, s2N 5630532913417, s2N 3595851341737,
   s2N 3002180475407, s2N 5405055275625, s2N 2596296614204, s2N 812847545407, s2N 2649137108803,
   s2N 75013108971, s2P 1247176367086, s2P 181753652993, s2N 4356747991630, s2N 4018600321187,
   s2N 1322100681086, s2P 2514332159638, s2P 4477013022562, s2P 1899331078181, s2N 4119136285928,
   s2P 6105629534810, s2P 5798821897331, s2N 323734531141, s2P 595883025472, s2N 1503453528013,
   s2N 2339266967330, s2P 2183175034083, s2P 3432156681277, s2N 1628644529003, s2N 206985683724,
   s2N 2673113622000, s2P 1023344020514, s2P 7484682236318, s2P 6386044742769, s2N 676377008301,
   s2P 170795945759, s2N 847364234654, s2N 4490673925259, s2N 7503366886992, s2N 7883851015013,
   s2N 7350034545541, s2N 157468689435, s2P 6530263329163, s2P 19064709429533, s2P 6992780700895,
   s2N 14832798060620, s2N 11913225521641, s2N 9405329316088, s2N 2112253874719]
private def s2V8S6 : List ℤ :=
  [s2N 6413697628751, s2P 8394947860365, s2N 5402381814243, s2P 1448133384874, s2N 8805862223184,
   s2P 2236378208293, s2P 4841871891626, s2P 7316241464442, s2P 6543500460696, s2N 4858504803986,
   s2P 9240005476355, s2N 10581735786247, s2N 6706654867647, s2N 977729188518, s2N 6048723922543,
   s2N 4536641495700, s2P 918994442922, s2P 1843921695133, s2N 106136279885, s2P 7952928714768,
   s2P 2110965626154, s2P 3614135735823, s2N 3736182697716, s2P 3440725033503, s2P 13218365571543,
   s2N 1263438925248, s2P 2412043604477, s2P 8628840109345, s2P 5814931305646, s2N 867860393630,
   s2P 5954901863505, s2P 9241564361151, s2P 14428871830010, s2P 7449928170396, s2N 276355213304,
   s2N 1323772216554, s2N 6894140277747, s2P 3146044887442, s2P 2452783547557, s2P 2578119559856,
   s2P 6710916736935, s2P 6483741770755, s2N 4330545548006, s2P 5427513436931, s2P 10555463579460,
   s2P 5420767934254, s2P 17293504246233, s2P 4280834096300, s2P 4062026531760, s2P 7533173132023,
   s2N 4736423877967, s2N 468769514759, s2P 6350137262199, s2N 3041633633679, s2N 11412588647112,
   s2P 1835740336908, s2N 4980344201432, s2P 1785578072645, s2N 11121365748756, s2N 4700246795223,
   s2N 7108774911524, s2N 3668993045614, s2N 7388792682569, s2P 580710932933]
private def s2V8S7 : List ℤ :=
  [s2N 4970000813639, s2N 5499574032460, s2N 5072921252335, s2N 8243195549282, s2N 5334296561586,
   s2P 10292551384206, s2P 3076591732955, s2P 5514011375567, s2N 7504496067595, s2P 2246695182719,
   s2P 10764555511467, s2P 4313431402120, s2P 10885252713777, s2P 5812323824590,
   s2P 34689665033161, s2P 105456951253163, s2P 191386095809377, s2P 276964452815432,
   s2P 348629557864108, s2P 394754316147395, s2P 407839114084755, s2P 387415984352749,
   s2P 340276931176326, s2P 277585222032446, s2P 210988325365525, s2P 149712054101117,
   s2P 99275890719927, s2P 61566247928907, s2P 35743585937682, s2P 19461338402129,
   s2P 9965272254885, s2P 4818785637506, s2P 2212872265166, s2P 971986856492, s2P 411854824206,
   s2P 169886527052, s2P 68789849915, s2P 27505998147, s2P 10884288104, s2P 4263843986,
   s2P 1630011111, s2P 631493132, s2P 226613641, s2N 67914611, s2P 17764367, s2P 4970631,
   s2P 1713197, s2P 639523, s2P 233961, s2P 73368, s2P 18392, s2P 4140, s2P 928, s2P 197, s2P 36,
   s2P 4, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V8S8 : List ℤ :=
  [s2P 0]
private def s2V8 : List ℤ :=
  s2V8S0 ++
  (s2V8S1 ++
  (s2V8S2 ++
  (s2V8S3 ++
  (s2V8S4 ++
  (s2V8S5 ++
  (s2V8S6 ++
  (s2V8S7 ++
  s2V8S8)))))))
private def s2Ch9 : List Rkm128kSeg := [
  ⟨56, 274276, 1, 30,
    rkm128kMask56 513 [12654160570435663, 69244583169559574, 37876742873775625, 67812463092182840,
     55409730587825471, 1247286788981727, 27268211281559728, 5840585386035361, 18155135997929993,
     500]⟩,
  ⟨56, 273146, 1, 30,
    rkm128kMask56 512 [24543134330116485, 10114610550112578, 36421604470747006, 1702986602268537,
     25122221839350305, 9580836756345387, 75007848894857, 14083954232955712, 35184372622914,
     160]⟩]
private def s2V9S0 : List ℤ :=
  [s2N 848856, s2N 10820780, s2N 9777731, s2N 4278011, s2P 24404086, s2P 43261987, s2P 86831978,
   s2P 158222076, s2P 12116796, s2P 84568920, s2P 13061326, s2N 79491192, s2P 23002311,
   s2P 129835304, s2N 83518289, s2P 5133061, s2P 70519194, s2P 66601440, s2N 48957748,
   s2N 52410218, s2N 3892500, s2N 37893285, s2N 97823015, s2N 75762523, s2N 106847739,
   s2N 185624124, s2P 54120430, s2P 184299519, s2P 145897043, s2P 3002309, s2N 16778533,
   s2N 120744025, s2N 255158997, s2N 340245032, s2P 49890954, s2P 119933384, s2N 270639326,
   s2P 176419123, s2P 12181245, s2N 14234527, s2N 319124507, s2N 581579533, s2N 398187178,
   s2N 59446424, s2N 355205000, s2P 699213218, s2P 806642117, s2N 157161434, s2N 933669653,
   s2N 658773245, s2N 646439324, s2P 6249450, s2P 998675403, s2P 81522061, s2N 1087174766,
   s2P 343427071, s2N 211111153, s2P 951778584, s2P 1264788521, s2P 22917905, s2P 1135418774,
   s2P 773305165, s2P 273615204, s2P 165558604]
private def s2V9S1 : List ℤ :=
  [s2P 558687444, s2N 231706434, s2P 698521484, s2P 261476658, s2P 763967238, s2N 382120427,
   s2P 866101598, s2P 2104381298, s2P 442302980, s2N 335396299, s2N 2503374883, s2N 2641953737,
   s2N 2535045649, s2N 1492621486, s2N 393590563, s2N 227334352, s2P 715628306, s2N 1291479366,
   s2N 36756741, s2P 811284502, s2P 1799636956, s2P 3165443368, s2N 907269424, s2N 1214534577,
   s2N 721877833, s2P 2197271162, s2P 2560471615, s2P 2130805766, s2P 648873752, s2P 5660220858,
   s2P 2891582631, s2P 290703423, s2P 489324216, s2P 2915499867, s2P 1672609874, s2P 1906412283,
   s2N 1529435006, s2N 3653060401, s2N 3629527041, s2P 6366346131, s2P 5938070729, s2P 2978678992,
   s2N 3842458014, s2N 3877364684, s2N 7147823997, s2N 3482940702, s2P 5750999763, s2P 7528738954,
   s2N 1679791873, s2N 8794733753, s2P 3801325009, s2P 5155859056, s2N 5143392359,
   s2P 13918198540, s2P 1021880867, s2P 1674238014, s2P 775043655, s2N 7723802136, s2N 3549157739,
   s2N 150590402, s2N 4835551184, s2P 5931061722, s2P 3305339651, s2N 1447933354]
private def s2V9S2 : List ℤ :=
  [s2P 11292650843, s2P 1128064505, s2P 91484277, s2P 1310192198, s2P 1418987214, s2N 9071038147,
   s2P 3089965391, s2P 6535959190, s2N 9287491371, s2N 20117597155, s2N 10596849364,
   s2P 17953485209, s2P 12392097952, s2P 7032353813, s2N 3473206533, s2N 8611514977,
   s2N 7631866633, s2P 6951160054, s2P 5691567966, s2P 27053749023, s2P 18681049927,
   s2P 13235355728, s2N 16801460324, s2N 7183936674, s2N 10233801822, s2N 19323805855,
   s2N 407293179, s2N 8315666281, s2P 386954961, s2P 15419552886, s2P 15535027760, s2P 4610804790,
   s2N 22445527257, s2N 19688702749, s2N 31128080568, s2N 21589978526, s2N 10580834206,
   s2P 7584593230, s2N 10417154433, s2N 10244308690, s2N 6207100334, s2N 15293573828,
   s2N 17254534299, s2P 37418350412, s2P 36529156077, s2P 30539292584, s2P 249663245,
   s2P 7541830925, s2N 10142883190, s2N 16246883135, s2N 22668944174, s2N 23472598953,
   s2N 68810394872, s2N 11120167882, s2N 58131910308, s2P 45559615006, s2P 71425340387,
   s2P 57216127756, s2P 6856105750, s2N 15024299600, s2P 11460114996, s2P 19819152990,
   s2P 58930674656, s2P 96258667073]
private def s2V9S3 : List ℤ :=
  [s2P 46530322381, s2N 18115578198, s2N 80633714482, s2N 24789514395, s2P 28075479539,
   s2P 101608779804, s2P 30780285032, s2P 80017444834, s2P 97199161958, s2P 197332584890,
   s2P 122309058722, s2N 56117855330, s2N 58855394969, s2N 178980019423, s2P 51280167800,
   s2P 23514357762, s2N 70550756264, s2N 27335562538, s2P 38061360473, s2P 83059240224,
   s2N 78717078496, s2N 58089564230, s2N 42206860364, s2N 90286547082, s2P 29656996604,
   s2N 72897016578, s2N 41878544054, s2N 40487085481, s2N 91789663863, s2P 40069441592,
   s2P 106471934088, s2P 88963388797, s2P 93708762136, s2P 87504410098, s2P 185377346041,
   s2P 345876674978, s2P 296675536225, s2P 162291800722, s2P 219147395048, s2P 331934372739,
   s2P 149763033773, s2N 101077228032, s2N 133506891695, s2N 118811126164, s2N 22498774427,
   s2P 136227710, s2N 70750877017, s2N 102543463676, s2N 3585668127, s2P 143399643335,
   s2N 57405335423, s2N 99152395751, s2P 110925234399, s2N 106180254989, s2P 135865403036,
   s2P 17685443829, s2N 206649358690, s2P 316061882856, s2N 115294697075, s2N 157891810073,
   s2P 127621919158, s2P 200911841174, s2N 322017513434, s2N 222444666059]
private def s2V9S4 : List ℤ :=
  [s2N 121286141923, s2N 428913174048, s2N 358577560363, s2N 203096353109, s2P 147014086316,
   s2P 130390128639, s2P 272956718983, s2P 141119215480, s2P 192666711241, s2P 50660588633,
   s2N 298725495363, s2N 463391976019, s2N 342824725864, s2P 182929303104, s2N 112769203823,
   s2N 47182895400, s2N 128526648769, s2N 496066225101, s2N 316392410484, s2P 173073936922,
   s2P 326095510637, s2P 453017968289, s2P 294755153010, s2P 801788892454, s2P 337319110959,
   s2N 16843794779, s2N 375918788255, s2P 143226830473, s2P 232325243220, s2N 546820075639,
   s2P 152300958270, s2N 125427361213, s2N 974946641299, s2N 393237903298, s2N 1621723511621,
   s2N 1574195829914, s2P 762169083441, s2P 175950105174, s2N 472954044485, s2N 58402263010,
   s2P 750756247036, s2P 652814523315, s2N 697487903426, s2N 1047008186934, s2N 1810503833145,
   s2N 1589049834421, s2P 482560632022, s2P 667899116151, s2N 881498123202, s2N 2988723755846,
   s2N 2409179331831, s2N 2932440336334, s2N 3845906486466, s2P 1149430463020, s2N 1999183375020,
   s2N 1903352241185, s2N 1571226894472, s2P 3104232742603, s2P 3085954729296, s2P 3731660986871,
   s2P 2560811826147, s2N 1766146564957, s2N 1576543331105, s2N 3121800077042]
private def s2V9S5 : List ℤ :=
  [s2N 782449850778, s2P 188957219813, s2N 265188250710, s2N 626129713479, s2P 5072862311224,
   s2P 316892788750, s2N 1203575907234, s2N 3808922134136, s2N 7613727561995, s2N 353701571763,
   s2P 6186246160575, s2P 6423242612703, s2P 7041686554294, s2N 526759944429, s2N 8035654401569,
   s2N 2507461740308, s2N 3458325895795, s2N 3531689808935, s2N 3340988141866, s2N 524429628371,
   s2N 1175188216478, s2N 1348938368559, s2N 2953809866498, s2P 2400947459844, s2P 7164330324717,
   s2N 799410169075, s2N 135033352005, s2N 782304374868, s2N 427436366997, s2N 3096937190192,
   s2P 1128666390130, s2N 2386517105275, s2N 5502173052345, s2N 6666374211721, s2N 640910004435,
   s2P 1791554232598, s2P 779966811953, s2P 3176342551582, s2N 3843851817317, s2N 4343710915569,
   s2N 6722353590469, s2N 1733365426868, s2P 1269519853413, s2P 1355232159637, s2N 3276855110026,
   s2P 3296988152131, s2N 1811356640671, s2N 5341865961911, s2N 757378369073, s2P 3252095131258,
   s2N 6300776960957, s2N 8810179760264, s2N 1298670475428, s2N 4721152217722, s2P 1046208681031,
   s2P 1686584434741, s2P 3049561933914, s2P 2320574197495, s2N 3065067715456, s2N 5694145885275,
   s2P 5435071193648, s2P 2674763426662, s2P 1731870967617, s2N 7812762645999]
private def s2V9S6 : List ℤ :=
  [s2N 9841590018621, s2N 13442978517079, s2N 19756141808832, s2N 11636991749177,
   s2P 2898255414914, s2N 11887305992131, s2N 15731786551543, s2N 6883279311555,
   s2P 3937531965743, s2N 10614669894816, s2N 5101746506192, s2P 2030477372035, s2N 3761876115454,
   s2P 1296504009479, s2N 2383116281116, s2P 6344514930492, s2N 2704807290267, s2P 2955684599004,
   s2P 2804375169704, s2P 633394432740, s2P 15458130254323, s2P 947865915543, s2N 2750036304870,
   s2N 846874164518, s2N 5075147097734, s2P 4135091336223, s2N 5831680220052, s2P 5914778744511,
   s2P 1136483896056, s2P 4665544864280, s2P 2366205446166, s2N 4081896224940, s2P 3658920194258,
   s2P 1120460579280, s2P 4427658821776, s2P 7048575191064, s2P 72700054248, s2N 598826065278,
   s2P 6915513839434, s2P 8386618589581, s2P 17242062240929, s2P 6611649711375, s2P 3361172471694,
   s2P 1053475565131, s2P 7866932808905, s2P 11543598591992, s2N 2210479384702, s2N 6605215834188,
   s2N 8928147719095, s2N 7737476414433, s2P 847240425916, s2P 3639851757228, s2N 6393994979035,
   s2N 13928453057247, s2N 10461403478752, s2N 9354217352253, s2P 724671695870, s2P 4001885692508,
   s2N 2121898922576, s2N 8889381670301, s2P 2011518793616, s2P 4247952400838, s2P 5653023566247,
   s2P 8855829243751]
private def s2V9S7 : List ℤ :=
  [s2N 7414249792667, s2P 4706516927732, s2N 110954046704, s2N 314444465306, s2P 46340364099,
   s2N 9538488719447, s2N 3215738597862, s2N 6457165103088, s2N 14345172568627, s2P 9097766835720,
   s2N 1026154081374, s2N 1411381561684, s2P 2374016648194, s2N 1769209658730, s2P 7859523044434,
   s2N 9076868797614, s2N 9187272973446, s2N 4344629023740, s2N 11629096541036,
   s2P 13626650741377, s2P 12445218910421, s2P 73278381627487, s2P 160555240643920,
   s2P 257287807544623, s2P 343257597944620, s2P 400694807817457, s2P 419487273908184,
   s2P 399558458212751, s2P 349463935144157, s2P 282406784939664, s2P 211765253609210,
   s2P 147799937519683, s2P 96243593798321, s2P 58594918692900, s2P 33423270207882,
   s2P 17903485515541, s2P 9029855829157, s2P 4301769249900, s2P 1942990353245, s2P 835611155414,
   s2P 344029409328, s2P 136196646150, s2P 52139360232, s2P 19467040937, s2P 7089935921,
   s2N 2461929562, s2P 807240960, s2P 234326346, s2P 57030687, s2P 12371142, s2P 2991629,
   s2P 941421, s2P 327939, s2P 109524, s2P 29888, s2P 6301, s2P 1114, s2P 195, s2P 32, s2P 2,
   s2P 0, s2P 0, s2P 0, s2P 0]
private def s2V9S8 : List ℤ :=
  [s2P 0]
private def s2V9 : List ℤ :=
  s2V9S0 ++
  (s2V9S1 ++
  (s2V9S2 ++
  (s2V9S3 ++
  (s2V9S4 ++
  (s2V9S5 ++
  (s2V9S6 ++
  (s2V9S7 ++
  s2V9S8)))))))
private def s2Ch10 : List Rkm128kSeg := [
  ⟨56, 274670, 1, 30,
    rkm128kMask56 513 [58018419693408358, 71548842536956742, 56928999694755204, 25759953233002327,
     4945134615822316, 48321628227636121, 5681300622214531, 3624265598790025, 4573968377333036,
     256]⟩,
  ⟨57, 269071, 1, 30,
    rkm128kMask56 513 [41048673658371856, 70307245039038807, 7249542518017783, 41851695841347085,
     55034632512471096, 15008403320758051, 4513418174500996, 36068379524610049, 35729426, 464]⟩]
private def s2V10S0 : List ℤ :=
  [s2P 919537, s2P 384251, s2P 15507614, s2N 8841892, s2N 8625939, s2N 16406379, s2N 47847144,
   s2N 7763888, s2N 87871050, s2N 91019167, s2N 70785535, s2N 55624126, s2N 77530923,
   s2N 170748565, s2N 115925207, s2N 38526215, s2P 2726366, s2P 30807840, s2N 18286363,
   s2N 8517889, s2P 77726436, s2N 46334137, s2N 35222817, s2N 13538259, s2N 3981965,
   s2P 115058329, s2N 33360295, s2N 4932200, s2N 49208288, s2N 183380915, s2N 114282180,
   s2N 268125601, s2N 40603159, s2P 33247268, s2N 242139180, s2P 16876862, s2N 43593376,
   s2N 558750180, s2N 95904072, s2P 17306603, s2P 259248396, s2P 186749064, s2N 303983729,
   s2N 51874979, s2N 192195715, s2N 877109273, s2N 615418513, s2N 349107358, s2N 120942916,
   s2N 560510474, s2N 177782336, s2N 680056079, s2N 46400528, s2N 413862296, s2P 503769083,
   s2P 1310790035, s2P 1125300263, s2P 864850893, s2P 1272850341, s2P 856117219, s2P 71999294,
   s2P 6106775, s2N 651980447, s2P 362716100]
private def s2V10S1 : List ℤ :=
  [s2P 297214134, s2P 271571516, s2P 158718030, s2P 1394806, s2P 883149804, s2P 1588041201,
   s2P 962771024, s2P 473847498, s2P 533629585, s2P 7540844, s2P 87228137, s2N 42116996,
   s2N 1034698507, s2P 1855358400, s2N 437495722, s2N 1894064471, s2N 1150379778, s2P 1438839950,
   s2P 529375707, s2P 414682986, s2N 3336098727, s2P 285050563, s2P 2054086592, s2P 5004922308,
   s2P 1582495487, s2P 1270544423, s2P 369897547, s2P 581769807, s2P 3810388390, s2P 1237052021,
   s2N 2249257595, s2N 374244850, s2N 143370305, s2P 1685883191, s2P 355766060, s2N 451660075,
   s2N 1085371378, s2N 884090030, s2N 3778334394, s2N 4222964205, s2N 2344622868, s2N 1518948958,
   s2P 1371175466, s2N 1686917171, s2P 487045730, s2N 5022063469, s2N 7174947069, s2N 3102544399,
   s2N 34917445, s2N 5737272994, s2N 1398005589, s2N 3339703306, s2P 7454337379, s2P 9689640017,
   s2P 14534810892, s2P 12705402377, s2P 5998707473, s2P 6460515009, s2P 2457696297,
   s2N 1932470531, s2P 1988378391, s2P 333837580, s2N 5647147322, s2N 6270848123]
private def s2V10S2 : List ℤ :=
  [s2N 2333360972, s2N 3516120876, s2N 2764231041, s2N 2122510971, s2N 3738790107, s2N 3990211228,
   s2N 10833882459, s2N 11431390136, s2N 13794426933, s2P 6936599131, s2P 9382042602,
   s2P 3752377456, s2P 12388625103, s2P 3043591083, s2N 15500552876, s2N 13638530463,
   s2N 16488047029, s2N 2518164211, s2N 6747706765, s2N 3434303006, s2N 1121686668,
   s2N 3469348863, s2P 8440604721, s2N 3442836526, s2N 1563054263, s2N 4651446404,
   s2N 12461441369, s2N 8978809937, s2N 26739468308, s2N 14059888743, s2N 23506653420,
   s2N 15228656310, s2N 1537591084, s2P 18047499831, s2P 20506427397, s2P 9466273234,
   s2N 273925695, s2N 9835217680, s2P 4611784845, s2N 18521611128, s2N 5071247354,
   s2N 27614545679, s2N 29790967094, s2N 8461579870, s2P 1511907180, s2P 30924615961,
   s2P 23629773895, s2P 32900983815, s2P 18298722370, s2P 9819546400, s2P 6093154466,
   s2P 38786625518, s2P 18442107138, s2P 43811536468, s2P 26849126578, s2N 33044656899,
   s2N 9902888652, s2P 25633705918, s2P 20226747674, s2P 40257709521, s2P 15898171826,
   s2P 48879304813, s2P 14163536297, s2P 4535358840]
private def s2V10S3 : List ℤ :=
  [s2P 67077832772, s2P 49091252715, s2N 8360590813, s2N 67263523017, s2N 70217193739,
   s2N 68400040559, s2N 19149924662, s2N 58793394830, s2N 151969047642, s2N 154840259196,
   s2N 143323341111, s2N 179868989165, s2N 175787853726, s2N 27298281816, s2P 59270775667,
   s2P 73091281824, s2P 80470568898, s2N 4878740657, s2P 16478974539, s2N 15397578780,
   s2P 15056181785, s2P 29564607016, s2P 14923032607, s2P 62364894642, s2P 16816105020,
   s2N 42337817140, s2P 19047508290, s2N 101144586313, s2N 46967692022, s2N 168918066508,
   s2N 2040065395, s2P 31854605155, s2N 3866256315, s2P 9366681269, s2P 66718184838,
   s2N 47771157184, s2N 35804103, s2P 31665112490, s2N 30454978263, s2N 45666275816,
   s2N 104448152292, s2P 50778617359, s2P 153790023442, s2P 94811276227, s2N 13848077020,
   s2N 55623561007, s2N 177878374022, s2N 26300015626, s2N 212493597853, s2N 269513456455,
   s2N 229420260722, s2N 293809561975, s2N 460133968379, s2N 463766182695, s2N 315995465556,
   s2N 39907049081, s2P 65096621039, s2P 161305545131, s2P 62860766006, s2P 27784641409,
   s2P 29038661019, s2P 6504893405, s2P 77373284936, s2N 187036035176]
private def s2V10S4 : List ℤ :=
  [s2N 84262406002, s2N 24330065515, s2P 92313340483, s2N 236029747147, s2N 331650978289,
   s2N 86861177082, s2N 326142123620, s2N 319494956413, s2N 147694569457, s2N 105411943784,
   s2N 62813592378, s2N 382438923461, s2N 63788647156, s2P 650129068862, s2P 9572703556,
   s2P 54956816145, s2N 102150015210, s2P 226127474868, s2P 27166952520, s2P 78527262181,
   s2P 329149985076, s2P 147019223428, s2N 62996552952, s2P 340482677196, s2N 36066796150,
   s2P 2369868686, s2N 23353607869, s2N 419123985784, s2N 600140854872, s2N 139915993700,
   s2N 52916389843, s2N 177022205700, s2P 1071982279304, s2P 944478415346, s2P 437127703777,
   s2N 388681548749, s2N 318788054919, s2P 1111746942231, s2P 827975381989, s2N 1163624081508,
   s2P 439792786281, s2P 1148823001653, s2N 274930043885, s2N 1238184944589, s2N 668642526501,
   s2N 1837908192804, s2N 1749371482163, s2N 2532497517823, s2N 1135518225212, s2P 75987046614,
   s2P 1821850837568, s2P 1359254476451, s2N 1158112462782, s2N 1032883733387, s2P 1516908107105,
   s2P 815867102474, s2P 1448234419811, s2N 1100845087503, s2N 143981301898, s2P 127679964118,
   s2N 2071613272526, s2P 4153600715192, s2P 1662194025304, s2P 2482991485763]
private def s2V10S5 : List ℤ :=
  [s2N 292097714931, s2P 974515766307, s2N 3758734569622, s2N 6707488550184, s2N 3198088338061,
   s2P 1282269559067, s2N 1479099194784, s2P 8270055760167, s2P 5653000267338, s2P 3566018063445,
   s2N 1583043812516, s2N 1249085625361, s2N 4931244773777, s2P 564442350650, s2P 1150839276204,
   s2N 5050472791882, s2N 1258381167678, s2P 3274076147270, s2N 2179369663409, s2N 1095464925216,
   s2N 1850060444075, s2N 11402978880149, s2N 1775505411442, s2N 1168039771795, s2N 2885452645891,
   s2N 4174268109329, s2N 1310940989789, s2N 4043979448958, s2P 1308149416054, s2N 4010225039890,
   s2N 1738269483561, s2P 814698121863, s2N 662408171873, s2P 2014289797644, s2P 3540599372485,
   s2P 1739066848042, s2P 3538418938586, s2P 4182754901585, s2P 169842767953, s2N 2521997233100,
   s2N 1285787137847, s2N 6656351308911, s2N 3792529218991, s2P 1946755883508, s2P 5346473782618,
   s2P 4287188865913, s2P 5403749512864, s2P 805732423712, s2N 4861831807770, s2P 4751942290240,
   s2N 3070379019825, s2N 449990309610, s2P 4770473373240, s2N 5645529671868, s2N 2871536509415,
   s2P 1569514617347, s2P 8665799283218, s2P 315296623758, s2N 2703854093562, s2P 6970738074965,
   s2P 2504095683130, s2N 131358553251, s2P 712403711088, s2P 7728665400310]
private def s2V10S6 : List ℤ :=
  [s2P 7972007666375, s2N 8015702994825, s2P 1527900819640, s2P 442606635647, s2P 1533606666753,
   s2N 9214367067378, s2P 3995520746524, s2P 22011548951161, s2P 11441219273482,
   s2N 19316556900953, s2N 8371282337484, s2P 752054908112, s2N 6997706397038, s2N 3432631930841,
   s2P 2648850284812, s2N 9045355696940, s2N 10522440258289, s2N 4839959639741, s2N 1787404184161,
   s2N 2353706480288, s2N 1920370883994, s2P 2265183713775, s2N 132975996524, s2N 7253419202245,
   s2N 9533694858702, s2N 4999938026563, s2P 5674896417607, s2P 7851310173152, s2N 4992540378747,
   s2N 1226317612546, s2N 1622562022585, s2N 1780203099575, s2P 1809231144234, s2N 3924494704607,
   s2P 3315500785298, s2N 3034091397648, s2N 2625942188731, s2N 401739722902, s2N 7920753214300,
   s2N 5289446620863, s2N 3416511881495, s2P 4115574573667, s2P 5492559562554, s2P 2983358045772,
   s2N 7905383478098, s2P 540954764966, s2P 14334375844344, s2P 10875248994380, s2P 7416407842639,
   s2P 1040192129546, s2P 806037696090, s2P 12967238819295, s2P 13376794262688, s2P 1493297742825,
   s2P 5368196880805, s2N 17162278905777, s2N 1710002773941, s2P 10139567151827,
   s2N 10071054198798, s2N 5176575315851, s2N 3543328026831, s2N 5953139666613, s2P 756123281889,
   s2N 4436927628531]
private def s2V10S7 : List ℤ :=
  [s2N 8678734109604, s2P 7852551148555, s2P 2353736925981, s2P 1670318203617, s2P 2502840831097,
   s2P 310290505900, s2P 8814923525187, s2N 17229619818536, s2N 56757106558, s2N 5575972447273,
   s2N 2184417368292, s2N 3514417145009, s2P 8374048296215, s2N 4519742320010, s2N 14458857117978,
   s2P 6269651281216, s2P 2169369086224, s2P 7098960624008, s2P 12683892069053,
   s2N 11066588789825, s2P 11804994457290, s2P 2174939244245, s2P 136574805805, s2P 6996419126442,
   s2N 5217971814246, s2P 14812194319844, s2P 8546098657611, s2P 75149990462714,
   s2P 174061820345749, s2P 281512174814903, s2P 370964333652776, s2P 422334797401483,
   s2P 427683515539918, s2P 391735522055378, s2P 327974052907803, s2P 252776675458138,
   s2P 180251164734425, s2P 119376174390565, s2P 73652792339234, s2P 42445001596856,
   s2P 22903797849307, s2P 11596197303009, s2P 5525818766022, s2P 2483882841248,
   s2P 1045318524527, s2P 437753001486, s2P 160181843107, s2P 46431307966, s2P 11305944641,
   s2P 2824279152, s2P 853414270, s2P 299573278, s2P 91764908, s2P 21824087, s2P 4534206,
   s2P 1060984, s2P 297362, s2P 83248, s2P 20659, s2P 4398, s2N 792, s2P 114, s2N 9, s2P 0]
private def s2V10S8 : List ℤ :=
  [s2P 0]
private def s2V10 : List ℤ :=
  s2V10S0 ++
  (s2V10S1 ++
  (s2V10S2 ++
  (s2V10S3 ++
  (s2V10S4 ++
  (s2V10S5 ++
  (s2V10S6 ++
  (s2V10S7 ++
  s2V10S8)))))))
private def s2Ch11 : List Rkm128kSeg := [
  ⟨58, 265599, 1, 30,
    rkm128kMask56 509 [54461127383244767, 5182308927727281, 1707270885805570, 28376109183630377,
     16755015314971087, 36171833432119563, 238116410838234, 59224324217114656, 1125900217262094,
     16]⟩,
  ⟨59, 254609, 1, 29,
    rkm128kMask56 513 [3447988266973645, 38811416276458228, 6012160121662849, 22526382593543214,
     54194035079007963, 8552100904646305, 9221640838676742, 442081520717860, 2375815434, 384]⟩]
private def s2V11S0 : List ℤ :=
  [s2P 5597434, s2P 10291947, s2P 1794000, s2P 14847502, s2N 1450751, s2N 9011914, s2N 20986151,
   s2N 42582753, s2N 8957683, s2P 16012505, s2P 7738073, s2N 16900262, s2N 107367728,
   s2N 141082450, s2N 133989468, s2N 151284775, s2N 69850927, s2N 22663590, s2N 63006406,
   s2N 32433484, s2N 35959599, s2P 17223548, s2N 11840432, s2N 66062761, s2P 95363345,
   s2P 39415802, s2N 17501894, s2P 70095742, s2N 20170454, s2P 31958608, s2P 184390486,
   s2P 63124727, s2P 55661256, s2N 29634144, s2N 82602497, s2N 215995567, s2P 126307229,
   s2N 199398455, s2N 355878468, s2N 98672406, s2N 79609384, s2N 378837938, s2P 81965797,
   s2P 225307642, s2P 103577926, s2P 861082568, s2P 54073205, s2P 220408088, s2N 380948577,
   s2N 204958172, s2N 95380133, s2P 311209880, s2N 198482529, s2N 480437431, s2N 357034597,
   s2N 38993628, s2N 939595550, s2N 1199334268, s2N 1612066016, s2N 1086784660, s2N 890013999,
   s2N 898418124, s2N 480405094, s2P 504478409]
private def s2V11S1 : List ℤ :=
  [s2P 337085675, s2P 550477489, s2P 172445206, s2P 1643976, s2P 536929227, s2P 832246889,
   s2P 385954899, s2N 293327999, s2N 813494728, s2N 848210268, s2N 222057176, s2N 1440792502,
   s2P 1187078466, s2N 13180575, s2N 1236636702, s2N 550104155, s2P 894846074, s2P 2444990804,
   s2P 399043157, s2N 2665175608, s2P 686052819, s2N 2721491474, s2N 169492448, s2N 1834281567,
   s2N 1701118066, s2N 1439003266, s2P 3621070477, s2P 2070368955, s2N 1590140439, s2N 833093869,
   s2P 3026701544, s2P 3059504590, s2N 768814222, s2N 1693234517, s2P 1465874694, s2N 742511032,
   s2P 1876846775, s2P 1844044863, s2N 2167417403, s2P 919315257, s2N 5164209170, s2N 194078338,
   s2N 691267672, s2N 1471412979, s2N 1040791387, s2P 951193951, s2N 1203558039, s2N 48135230,
   s2N 562380659, s2N 6198679434, s2N 5149645695, s2N 2324169277, s2N 597771064, s2P 940202430,
   s2P 3521252400, s2P 8009867105, s2P 1764413430, s2P 4199644985, s2P 8626833644, s2P 5654042715,
   s2P 2661212775, s2P 4468424173, s2P 10515732298, s2N 4941052518]
private def s2V11S2 : List ℤ :=
  [s2N 11809433382, s2N 6635782022, s2P 8983467535, s2P 11498707922, s2P 5230245470,
   s2N 1419598930, s2N 1391893900, s2P 794429463, s2N 4185980606, s2N 5554736810, s2N 1614010725,
   s2N 7673823572, s2N 6640743889, s2N 2815151892, s2N 12216479212, s2N 5330305420, s2N 966833252,
   s2N 920558533, s2N 12194210888, s2P 11242101312, s2N 2283115908, s2P 8815909985,
   s2P 27487142629, s2P 13105482416, s2N 704209882, s2N 9576190583, s2N 6464143761,
   s2N 6617986715, s2P 3264804954, s2P 2239322895, s2P 2834298438, s2N 3457586392,
   s2P 19194732055, s2P 21399774008, s2P 3915338170, s2N 2601703226, s2P 16205624389,
   s2P 2440398122, s2P 25268650289, s2P 10068271586, s2N 11052929762, s2P 19214606249,
   s2P 17572043127, s2P 30332276885, s2P 12977955144, s2P 18715078849, s2P 12623336854,
   s2N 6290292970, s2P 10787738850, s2P 2565789676, s2P 14044592894, s2N 8835524541,
   s2N 23864769522, s2N 21570453100, s2N 38065347519, s2N 14059751634, s2P 1638380501,
   s2N 21842706400, s2N 54991249700, s2N 23304076673, s2N 25047642809, s2N 15790814334,
   s2N 34767789822, s2N 9620942149]
private def s2V11S3 : List ℤ :=
  [s2N 66774017184, s2N 41518545303, s2N 357678521, s2N 4606306507, s2N 24204321330,
   s2N 53661329602, s2N 83051188547, s2N 33368619916, s2P 16692459604, s2P 41365139956,
   s2P 42793234432, s2N 58772278158, s2N 83385816269, s2P 6107146018, s2P 6937001588,
   s2N 20414748592, s2N 19263966627, s2N 33842124634, s2P 12449506638, s2N 27872266271,
   s2P 69303380069, s2P 93592582903, s2P 115012992542, s2P 232465382264, s2P 202746580700,
   s2P 196599089911, s2P 23164414503, s2N 769985838, s2N 34970091125, s2N 15507594773,
   s2P 82850203084, s2P 45142080994, s2N 53008544463, s2P 34846426547, s2P 101733414054,
   s2P 3564583649, s2P 1464292440, s2P 13393538485, s2N 88219127013, s2N 41033338556,
   s2P 105101026601, s2N 101657146800, s2P 52957904238, s2P 74050832831, s2P 60548364754,
   s2N 78752724975, s2N 24026180223, s2P 101067414552, s2P 147258317096, s2N 91365460167,
   s2P 42724133999, s2N 116538349173, s2N 65617643235, s2N 816712274, s2N 6973019041,
   s2N 58248132211, s2N 16018741025, s2N 47170340559, s2N 90486473518, s2N 148562758121,
   s2N 8850678724, s2N 93008882163, s2N 87880449508, s2N 287768263910]
private def s2V11S4 : List ℤ :=
  [s2N 505548077159, s2N 489219134973, s2N 374896119810, s2N 259806133203, s2P 50414096429,
   s2P 168791847170, s2P 210789446764, s2P 262098576176, s2P 145963637365, s2P 321008408279,
   s2P 354185670678, s2P 175282719796, s2N 31398625050, s2N 156403480172, s2N 251335846934,
   s2N 142590275108, s2N 280334564003, s2N 426298792364, s2N 412297792732, s2N 108464222406,
   s2P 273312502736, s2P 169898883599, s2N 301062346176, s2N 236408468630, s2P 396006652472,
   s2N 125620687489, s2P 205812664965, s2N 263619577657, s2N 187372290692, s2N 222221063036,
   s2N 245325043104, s2N 419849544974, s2P 169185489922, s2P 77309989374, s2N 425683120813,
   s2P 689456227939, s2P 131118442806, s2P 120510285315, s2N 306533340737, s2N 20558569784,
   s2P 27972852520, s2P 614126049451, s2P 1464008163092, s2P 970374245501, s2P 934370057536,
   s2P 1195917978408, s2P 1148637872125, s2N 265659192579, s2P 223662838120, s2P 847187394959,
   s2P 859561387162, s2P 416659468927, s2N 674228397734, s2N 515635494471, s2P 2341412021626,
   s2P 2230615442175, s2P 2642898796607, s2P 3456391425623, s2P 1783713946159, s2P 449847631062,
   s2N 1128164508442, s2P 2119071942182, s2P 966248281061, s2P 598145223987]
private def s2V11S5 : List ℤ :=
  [s2N 1175346899365, s2N 1622687267964, s2P 1357619190189, s2P 2122810552900, s2P 2399760335178,
   s2P 4197140346748, s2P 5169010171681, s2N 575038989681, s2N 2701148298495, s2N 3006112234507,
   s2N 3882970080922, s2N 1365251331978, s2N 947101645382, s2N 1009646906550, s2N 5972481172793,
   s2N 7920920963148, s2N 253538937317, s2N 446620369394, s2N 2668276843443, s2P 6545481198441,
   s2P 9042770153774, s2N 1486453158761, s2P 4559893381503, s2P 4167333653784, s2N 792203445139,
   s2N 3408300609093, s2P 4269301485078, s2N 6046265340778, s2N 4122010357747, s2N 3549552274320,
   s2P 3564997766258, s2N 960987411214, s2P 304558107669, s2P 254276391783, s2P 3205701687345,
   s2P 1812892657333, s2P 711518093083, s2N 684907137969, s2P 79827660583, s2N 822921740046,
   s2N 421214280341, s2P 2530026747696, s2N 3526335200980, s2P 732275359067, s2N 3436940872451,
   s2P 4198671665430, s2P 1921236897803, s2P 1849119782057, s2N 8883278502382, s2N 5539060785818,
   s2P 4453534926208, s2P 514022531694, s2P 7903679856649, s2P 3552598295933, s2P 4757365284524,
   s2P 6805099270809, s2N 1328989677171, s2P 456797586065, s2N 733386283423, s2N 5222049776519,
   s2N 2736498823463, s2N 6853563429499, s2P 669128243463, s2P 763522957994]
private def s2V11S6 : List ℤ :=
  [s2N 3267032936257, s2N 9790857255534, s2N 935733713650, s2N 4057480700791, s2N 15845022891541,
   s2N 62213316100, s2P 15195534687881, s2N 7191538419498, s2N 4711256964044, s2P 13626179295273,
   s2N 12246706377510, s2N 5871935663861, s2N 10840929848996, s2P 3985055298211,
   s2P 5886502325135, s2P 6417373482041, s2P 15428199090246, s2N 3188798074561, s2N 6912808174763,
   s2N 896623723072, s2P 2596218622183, s2N 9592319234582, s2P 2621224984235, s2N 4920258047666,
   s2N 1095452962090, s2N 4213377790265, s2N 3686844094819, s2N 7457057536334, s2N 102934554958,
   s2N 3557866848296, s2N 5744271013781, s2N 12266209301794, s2N 7331848148740, s2N 649836734420,
   s2N 380023693276, s2N 1286792732103, s2P 3193400347700, s2P 2561431475527, s2P 7536561284212,
   s2N 5593231234711, s2P 6407124455298, s2P 4205563090576, s2N 1900718533759, s2N 1686278538330,
   s2N 4269122535007, s2N 410789330746, s2P 2268348041929, s2N 14522866533350, s2P 4666358741259,
   s2P 5571335361332, s2N 11286393973638, s2N 1452691562790, s2P 4016982043993,
   s2P 13755949446772, s2P 11349933950528, s2P 1603955342525, s2P 4926834873172,
   s2P 2591592760045, s2P 16066919347178, s2P 11646768826677, s2P 10761953015969,
   s2P 6144358655578, s2N 6282452658938, s2P 4084863429461]
private def s2V11S7 : List ℤ :=
  [s2P 5434919530643, s2N 1383930989554, s2P 11625326272513, s2P 1427054109361, s2P 1888277439042,
   s2P 9870040436280, s2P 13527474945483, s2P 2109064786182, s2P 3235062654299,
   s2P 12000504943210, s2P 560327873351, s2P 936038675865, s2N 7327025011157, s2N 4392158707228,
   s2N 5237949895346, s2N 17364922382337, s2N 166137716143, s2P 18667005872213, s2P 6216090246206,
   s2P 1987374353499, s2P 458771896320, s2N 4399262299893, s2P 12013434751861, s2N 3373988865156,
   s2N 7746538426636, s2N 17903688788742, s2N 1160965168628, s2P 9603896328318, s2P 3833587388636,
   s2P 7556985294990, s2N 10808335638038, s2P 11346922147605, s2P 37719735949048,
   s2P 134923351770178, s2P 254116844873226, s2P 360948727197571, s2P 427535633246644,
   s2P 441374774115900, s2P 406666545292304, s2P 339209801889627, s2P 258536266685102,
   s2P 181253667155309, s2P 117408297877041, s2P 70544373483530, s2P 39431596601427,
   s2P 20537269449743, s2P 9990689372800, s2P 4563949450637, s2P 1936343271291, s2P 803612933578,
   s2P 270791149133, s2P 69270990334, s2P 15582816715, s2P 4021524046, s2P 1232577297,
   s2P 372370287, s2P 100517311, s2P 24015247, s2P 5149702, s2P 1022152, s2P 167331, s2P 20847,
   s2P 2147, s2N 202]
private def s2V11S8 : List ℤ :=
  [s2N 12]
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
private def s2Ch12 : List Rkm128kSeg := [
  ⟨59, 251789, 1, 29,
    rkm128kMask56 513 [4622260197407672, 39935657935190031, 71755992692364224, 70423968728506876,
     32682013758213258, 14024334436158356, 61520753732911173, 37160550454905549, 13222062730,
     416]⟩,
  ⟨60, 249596, 1, 29,
    rkm128kMask56 513 [689690236633251, 10828863365397704, 39098524534044405, 60236220939188866,
     30891923642149150, 2587702499944114, 18129587552067714, 55380481370726480, 81948419232,
     416]⟩]
private def s2V12S0 : List ℤ :=
  [s2P 2080839, s2N 9491098, s2P 7963676, s2N 249909, s2N 10336986, s2P 11690478, s2P 698558,
   s2P 6898632, s2P 4831311, s2P 44174385, s2P 11832930, s2P 53504783, s2N 51739025, s2N 8390627,
   s2P 10549345, s2P 28156752, s2P 23389636, s2P 74642344, s2P 170422242, s2P 83952175,
   s2N 142517488, s2N 153415240, s2P 19986454, s2P 10832504, s2N 11989299, s2P 70340234,
   s2P 1977721, s2P 105665092, s2P 23884074, s2P 70340026, s2N 83422857, s2N 144039916,
   s2N 137548621, s2P 51977214, s2P 289193966, s2P 120279250, s2P 137032332, s2N 227414058,
   s2N 39125456, s2P 233814854, s2P 498306999, s2N 83589485, s2P 199196848, s2P 175359644,
   s2P 14181685, s2P 149916677, s2P 332831096, s2N 365500459, s2P 186729493, s2P 268356305,
   s2P 100474512, s2P 324140341, s2P 469666854, s2P 264638480, s2P 223777482, s2P 605737724,
   s2P 223822768, s2P 236559593, s2P 221252139, s2P 43379878, s2P 228637198, s2P 557451393,
   s2N 46658769, s2N 173363518]
private def s2V12S1 : List ℤ :=
  [s2N 738233684, s2N 740524087, s2P 533514530, s2P 1469678015, s2P 1850986976, s2P 224104488,
   s2N 1259534003, s2N 1716137413, s2N 782833800, s2P 141118402, s2P 178261526, s2N 369386159,
   s2P 865317893, s2N 686022315, s2N 223708810, s2N 332186109, s2N 654756592, s2N 851274954,
   s2N 1397027288, s2P 673477806, s2P 2545902571, s2P 1851116089, s2N 1781751656, s2N 1083407426,
   s2P 2294370795, s2N 589108723, s2N 2053541572, s2P 1258601769, s2N 1254631728, s2P 929515263,
   s2P 2926839243, s2N 1418090312, s2N 1722956773, s2N 5041281804, s2N 4235325779, s2P 230516816,
   s2P 2230912449, s2N 1727300461, s2N 144331707, s2P 2032378442, s2P 2973633633, s2N 1051048450,
   s2P 1342563110, s2P 1880528527, s2N 131361882, s2N 715147337, s2P 210188439, s2P 1976392043,
   s2N 2425631464, s2N 2534738525, s2P 692941764, s2P 1919832914, s2P 2513541121, s2P 4375141716,
   s2P 385454018, s2N 863466025, s2P 1084603118, s2P 2543462739, s2P 191506148, s2N 1890911077,
   s2P 502998936, s2N 7931283359, s2N 4708433223, s2N 5668241892]
private def s2V12S2 : List ℤ :=
  [s2P 14656482, s2N 463547541, s2N 7313594902, s2N 261791258, s2N 14788426549, s2P 8599839286,
   s2N 4336537855, s2N 16855026486, s2N 2992383195, s2P 11851360098, s2P 5100508297,
   s2P 7416346420, s2P 1604618914, s2P 8951734933, s2P 1659355286, s2P 727260628, s2N 6020904421,
   s2P 3885943698, s2N 2959512149, s2P 1533959582, s2P 14853245420, s2P 8024446193,
   s2P 1867016096, s2P 18814595177, s2N 2686746635, s2N 3722899482, s2P 12237322948,
   s2P 7062215118, s2P 32303727066, s2P 12493765081, s2N 4145358528, s2P 2591067048,
   s2N 4937457816, s2P 5556446828, s2N 11751240976, s2N 4447957425, s2P 731510716,
   s2P 11547977400, s2N 4747893429, s2N 6295561469, s2P 22106415109, s2N 4943097115,
   s2N 12711370744, s2N 5695319113, s2N 10631092098, s2N 1143113986, s2P 3069693684,
   s2P 29059673036, s2N 12559782976, s2P 3542531605, s2N 703888560, s2P 14080696445,
   s2P 14073093838, s2P 29161974398, s2P 4753377908, s2P 47740620062, s2P 3699870285,
   s2P 4415350546, s2P 16565990491, s2N 15160499755, s2N 6312756534, s2N 7897743197,
   s2P 8772606507, s2N 20126842838]
private def s2V12S3 : List ℤ :=
  [s2N 38325127697, s2N 27883679107, s2N 12213286759, s2N 14208245207, s2P 14907708929,
   s2P 75645233802, s2P 24707544170, s2P 41204041, s2P 20475421555, s2P 12070151182,
   s2P 2650794878, s2P 110958735650, s2P 17888773342, s2P 4187116334, s2P 5361332465,
   s2N 3736189141, s2P 43189323632, s2P 51389120196, s2P 69103118812, s2P 75821213508,
   s2P 61513823036, s2P 41800949876, s2N 42854489894, s2N 39356161644, s2N 15916317858,
   s2N 16615544989, s2N 28848959259, s2N 94655026773, s2N 35518787327, s2N 25004750356,
   s2P 21935860430, s2P 504752667, s2P 73059640503, s2P 54790880022, s2P 84884149081,
   s2P 271810022272, s2P 196923108785, s2N 190509789432, s2N 100894726538, s2N 81167867364,
   s2N 195188714872, s2P 55549404755, s2N 41291088829, s2N 81458851762, s2P 20814218242,
   s2P 23513196596, s2P 42801752200, s2P 108315708887, s2P 55473906019, s2P 42936866989,
   s2N 16838945562, s2N 4458549084, s2N 34299381270, s2P 37174526350, s2P 101657168489,
   s2P 50516462903, s2P 48138900646, s2P 20974649880, s2N 46847982430, s2P 113480479604,
   s2N 46736885024, s2P 40115554186, s2N 160786816046, s2N 74871274411]
private def s2V12S4 : List ℤ :=
  [s2P 44274166289, s2N 102970153391, s2N 29860340815, s2N 26936185152, s2N 45024450752,
   s2N 171939513443, s2N 96160819755, s2N 19006985616, s2N 4734891174, s2P 138290891508,
   s2P 121987192972, s2N 281388767874, s2N 495339437104, s2N 482696731247, s2P 366758437561,
   s2P 195752734143, s2P 109004152425, s2N 469812199358, s2N 274482542619, s2P 138390241531,
   s2P 98151404904, s2N 752111344917, s2N 509881292523, s2N 158164888199, s2N 580173337461,
   s2N 294974186944, s2N 88673728694, s2P 68637777516, s2N 73515354086, s2N 313007893358,
   s2N 330955047835, s2P 521001438968, s2P 441824413025, s2N 86643809020, s2N 76810178717,
   s2P 352742932417, s2N 299479213004, s2P 23971464208, s2N 358286965800, s2P 309907238635,
   s2P 277021018379, s2P 80472459713, s2P 40089021140, s2P 656315718807, s2P 488877878117,
   s2N 1168906750, s2P 492966910644, s2N 73291106596, s2N 778821452688, s2N 73102245066,
   s2N 423083860393, s2N 902099016648, s2N 10094353922, s2N 556963791294, s2N 589659900515,
   s2P 781152808171, s2P 1911703023488, s2P 1844229297292, s2P 1158266430132, s2N 258275316323,
   s2N 430440961560, s2N 1572650892546, s2P 245817081420, s2P 1307025080426]
private def s2V12S5 : List ℤ :=
  [s2P 1671055773581, s2P 2060070602837, s2P 3352059037352, s2P 3409896366654, s2N 980913769819,
   s2N 1169202058638, s2P 1209110940827, s2P 3095352215560, s2P 1838820022353, s2P 3982927349435,
   s2P 2520047310406, s2P 1585899080638, s2P 1326051138248, s2N 1789533940885, s2P 6418080791519,
   s2P 2655317336586, s2P 3682966789019, s2P 396511400160, s2P 2353887288655, s2N 3245050242783,
   s2N 8148173296232, s2N 7480845764534, s2P 2172270619100, s2N 653414265435, s2N 3852820675445,
   s2N 2898107648345, s2N 7507146151272, s2N 5848611699716, s2N 4000440611757, s2N 1518224644239,
   s2P 5486673025240, s2P 1915233911196, s2N 1536314153165, s2N 4179193283164, s2N 4596941797181,
   s2P 3034787392500, s2N 1450929699595, s2P 345844765237, s2P 6568660347976, s2P 992228413379,
   s2N 3600695360815, s2P 2697861458795, s2N 2426681893580, s2N 2366364644934, s2N 5448706384689,
   s2P 3018976958389, s2P 950395006197, s2P 2602035637942, s2P 1597464838494, s2P 44859386421,
   s2P 3242229647227, s2P 3220891800475, s2P 3880610618703, s2P 3424280907451, s2N 2814371428187,
   s2N 472783112948, s2N 8378516999665, s2N 3286011725715, s2N 3334710168542, s2P 827993343263,
   s2N 4069829226215, s2N 10327193496952, s2N 6406854766635, s2P 138083616346]
private def s2V12S6 : List ℤ :=
  [s2N 266358524744, s2P 7005300225586, s2P 4488876285128, s2N 6373558422739, s2N 3018835448709,
   s2N 612541446567, s2N 2856112033302, s2N 1637351510675, s2P 11042118902626, s2P 12141624198574,
   s2P 17183120738810, s2P 19320015377426, s2P 1291113566203, s2P 5107810172870,
   s2N 8641109331255, s2N 6922745571934, s2P 14710843295059, s2P 8099237699991, s2N 5795014793645,
   s2P 3015105906236, s2P 6925773512591, s2N 3599126661132, s2P 8670229354623, s2N 1585133884442,
   s2N 855172144318, s2N 3603059290020, s2N 696785365755, s2P 3330216383304, s2P 3097320039051,
   s2N 2567127962664, s2P 6309780185267, s2P 4432034319656, s2P 1988715481064, s2P 5052413613038,
   s2P 1787150239570, s2P 2035316080717, s2N 4155065512657, s2N 10989098405527,
   s2N 12521825959046, s2N 6160618981187, s2P 1552710218010, s2P 5685804046076, s2N 1427627350606,
   s2N 3048922125672, s2P 7293699945459, s2P 3912548902222, s2N 1536892538558, s2N 13737470070981,
   s2N 2576495203556, s2P 3456828238573, s2P 12547915149289, s2N 567608778159, s2N 2280243923737,
   s2P 2438727647997, s2N 1662429762568, s2N 5754264709444, s2N 10218669364780,
   s2N 10157707655548, s2N 6260238877168, s2N 3386046646314, s2P 19307583240555,
   s2N 2303888816163, s2N 486270491160, s2N 5946836913379]
private def s2V12S7 : List ℤ :=
  [s2P 12864042074437, s2P 7462501110442, s2P 10946050780483, s2P 2096725579615,
   s2P 1870097070038, s2P 12549255526762, s2P 13834749951922, s2N 827183205019, s2P 5980252094589,
   s2N 10568294954390, s2N 1234174829901, s2N 1517561580991, s2N 4559636021677, s2P 2826683579012,
   s2P 8571163469194, s2N 523616898605, s2N 2851666490530, s2P 7323875450814, s2N 20372806822653,
   s2N 10669848257768, s2N 3924862635347, s2N 12703870903696, s2N 5087327763272,
   s2P 8848471974273, s2P 3704486091277, s2N 12397233092241, s2N 9858595609474,
   s2P 13008242447200, s2N 846576924888, s2P 8205905439449, s2P 3279728547652, s2P 18770002509520,
   s2P 6933362591267, s2N 12912598471753, s2P 16495222052892, s2N 10504482913831,
   s2P 13417412608143, s2P 45418371380379, s2P 158932960781695, s2P 290549052082738,
   s2P 397764370206268, s2P 451281695323378, s2P 443798088405056, s2P 387543828495945,
   s2P 304872596324190, s2P 218187074509248, s2P 142915753631829, s2P 86122801491874,
   s2P 47875183967906, s2P 24599955798292, s2P 11733256209704, s2P 5201153825481,
   s2P 2123836782838, s2P 785702692670, s2P 259491767973, s2P 76120489847, s2P 19970971388,
   s2P 4766349757, s2P 1055783352, s2P 219400762, s2P 42930811, s2N 6652619, s2P 755261,
   s2N 57708]
private def s2V12S8 : List ℤ :=
  [s2N 1870]
private def s2V12 : List ℤ :=
  s2V12S0 ++
  (s2V12S1 ++
  (s2V12S2 ++
  (s2V12S3 ++
  (s2V12S4 ++
  (s2V12S5 ++
  (s2V12S6 ++
  (s2V12S7 ++
  s2V12S8)))))))
private def s2Ch13 : List Rkm128kSeg := [
  ⟨60, 238913, 1, 28,
    rkm128kMask56 485 [16841690056293041, 17876768835257628, 24728961298558193, 38233713525202122,
     70021950480101417, 7350261370097283, 6768155036535954, 21091214341784974, 69056792615]⟩,
  ⟨60, 240912, 1, 28,
    rkm128kMask56 513 [62758804955230573, 44404876800648501, 35008858778148236, 70157378999815076,
     9542790633624591, 768156358042040, 23297842077728905, 3673488767501461, 1519009473281, 328]⟩,
  ⟨61, 238833, 1, 28,
    rkm128kMask56 512 [7404392627946032, 5924418286752215, 48278457116191164, 33161264880046201,
     17853241906252267, 23087996324574723, 8792127050752015, 62327541773650002, 106918119644,
     192]⟩]
private theorem s2Segs_split : mm16k512krS2Segs =
    s2Ch0 ++ (s2Ch1 ++ (s2Ch2 ++ (s2Ch3 ++ (s2Ch4 ++
      (s2Ch5 ++ (s2Ch6 ++ (s2Ch7 ++ (s2Ch8 ++ (s2Ch9 ++
        (s2Ch10 ++ (s2Ch11 ++ (s2Ch12 ++ s2Ch13)))))))))))) := rfl
private theorem s2B0_ok :
    s2RunAtEq s2Ch0 mm16k512krS2LIn mm16k512krS2DCurIn mm16k512krS2PadIn
      mm16k512krS2VecIn 53 512 771317415 s2V0
      = true := by decide +kernel
private theorem s2B1_ok :
    s2RunAtEq s2Ch1 53 512 771317415 s2V0
      54 512 776441027 s2V1 = true := by decide +kernel
private theorem s2B2_ok :
    s2RunAtEq s2Ch2 54 512 776441027 s2V1
      55 512 781649164 s2V2 = true := by decide +kernel
private theorem s2B3_ok :
    s2RunAtEq s2Ch3 55 512 781649164 s2V2
      56 512 795668650 s2V3 = true := by decide +kernel
private theorem s2B4_ok :
    s2RunAtEq s2Ch4 56 512 795668650 s2V3
      56 512 816152270 s2V4 = true := by decide +kernel
private theorem s2B5_ok :
    s2RunAtEq s2Ch5 56 512 816152270 s2V4
      56 512 834550403 s2V5 = true := by decide +kernel
private theorem s2B6_ok :
    s2RunAtEq s2Ch6 56 512 834550403 s2V5
      56 512 850516101 s2V6 = true := by decide +kernel
private theorem s2B7_ok :
    s2RunAtEq s2Ch7 56 512 850516101 s2V6
      56 512 875882396 s2V7 = true := by decide +kernel
private theorem s2B8_ok :
    s2RunAtEq s2Ch8 56 512 875882396 s2V7
      56 512 910162753 s2V8 = true := by decide +kernel
private theorem s2B9_ok :
    s2RunAtEq s2Ch9 56 512 910162753 s2V8
      56 512 932194965 s2V9 = true := by decide +kernel
private theorem s2B10_ok :
    s2RunAtEq s2Ch10 56 512 932194965 s2V9
      57 512 950027748 s2V10 = true := by decide +kernel
private theorem s2B11_ok :
    s2RunAtEq s2Ch11 57 512 950027748 s2V10
      59 512 966586947 s2V11 = true := by decide +kernel
private theorem s2B12_ok :
    s2RunAtEq s2Ch12 59 512 966586947 s2V11
      60 512 980238081 s2V12 = true := by decide +kernel
private theorem s2B13_ok :
    s2RunAtEq s2Ch13 60 512 980238081 s2V12
      mm16k512krS2LOut mm16k512krS2DCurOut mm16k512krS2PadOut mm16k512krS2Vec
      = true := by decide +kernel

/-- Segment count of `mm16k512krS2Segs` (`26` segments). -/
theorem mm16k512krS2_len : rkm128kSegListLen mm16k512krS2Segs = 26 := rfl

/-- Exact `rkm128kRunSegs 16 62 512` step across `mm16k512krS2Segs` (`segs 82..107`). -/
theorem mm16k512krS2_step :
    rkm128kRunSegs 16 62 512 mm16k512krS2Segs
      mm16k512krS2LIn mm16k512krS2DCurIn mm16k512krS2PadIn mm16k512krS2VecIn =
      (mm16k512krS2LOut, mm16k512krS2DCurOut, mm16k512krS2PadOut, mm16k512krS2Vec) := by
  rw [s2Segs_split]
  exact s2RunStep s2B0_ok (s2RunStep s2B1_ok (s2RunStep s2B2_ok (s2RunStep s2B3_ok
    (s2RunStep s2B4_ok (s2RunStep s2B5_ok (s2RunStep s2B6_ok (s2RunStep s2B7_ok
    (s2RunStep s2B8_ok (s2RunStep s2B9_ok (s2RunStep s2B10_ok (s2RunStep s2B11_ok
    (s2RunStep s2B12_ok (s2RunLast s2B13_ok)))))))))))))

/-- Suffix chaining lemma advancing `rkm128kRunSegs 16 62 512` past `mm16k512krS2Segs`. -/
theorem mm16k512krS2_run_after (rest : List Rkm128kSeg) :
    rkm128kRunSegs 16 62 512 (mm16k512krS2Segs ++ rest)
      mm16k512krS2LIn mm16k512krS2DCurIn mm16k512krS2PadIn mm16k512krS2VecIn =
    rkm128kRunSegs 16 62 512 rest
      mm16k512krS2LOut mm16k512krS2DCurOut mm16k512krS2PadOut mm16k512krS2Vec := by
  rw [rkm128kRunSegs_append]; dsimp only; rw [mm16k512krS2_step]

/-- Prefix chaining lemma extending any certified state ending at `mm16k512krS2*In`. -/
theorem mm16k512krS2_after {segsPrev : List Rkm128kSeg} {l0 d0 p0 : ℕ} {v0 : List ℤ}
    (hPrev : rkm128kRunSegs 16 62 512 segsPrev l0 d0 p0 v0 =
      (mm16k512krS2LIn, mm16k512krS2DCurIn, mm16k512krS2PadIn, mm16k512krS2VecIn)) :
    rkm128kRunSegs 16 62 512 (segsPrev ++ mm16k512krS2Segs) l0 d0 p0 v0 =
      (mm16k512krS2LOut, mm16k512krS2DCurOut, mm16k512krS2PadOut, mm16k512krS2Vec) := by
  rw [rkm128kRunSegs_append, hPrev]; dsimp only; exact mm16k512krS2_step

end

end QuantumComputation.Specs.GroverFindAll.Rk128kMidM16K512KrPt2
