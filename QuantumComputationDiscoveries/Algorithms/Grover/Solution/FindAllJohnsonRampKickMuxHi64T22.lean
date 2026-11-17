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
 High-`m` Checkpointed Walk Part `22` (`FindAllJohnsonRampKickMuxHi64T22`, `145358` coords).
-/
namespace QuantumComputation.Specs.DickeSol
@[expose] public section
/-- Concatenates two `List ℕ` word sublists (`Hi64T22`). -/
def rkmCatNHi64T22 : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: rkmCatNHi64T22 xs ys
/-- Appends `tz` spine-strict trailing zeros (`Hi64T22`). -/
def rkmZTailHi64T22 : ℕ → List ℤ
  | 0 => []
  | c + 1 => highdStrictConsInt (Int.ofNat 0) (rkmZTailHi64T22 c)
/-- Unpacks `< 2^51` ZigZag fixnums + `tz` trailing zeros (`Hi64T22`). -/
def rkmDec15Hi64T22 (tz : ℕ) : List ℕ → List ℤ
  | [] => rkmZTailHi64T22 tz
  | u :: us =>
    let q := Nat.div u 2
    let z := match Nat.mod u 2 with | 0 => primOfNatForced q | _ => primNegSuccForced q
    highdStrictConsInt z (rkmDec15Hi64T22 tz us)
/-- Gap-encoded spine-strict sign-flip helper (`Hi64T22`). -/
def rkmFlipGapsHi64T22 : List ℕ → List ℤ → List ℤ
  | [], vs => vs
  | _, [] => []
  | 0 :: gs, v :: vs => highdStrictConsInt (muxRawIntNeg v) (rkmFlipGapsHi64T22 gs vs)
  | (g + 1) :: gs, v :: vs => highdStrictConsInt v (rkmFlipGapsHi64T22 (g :: gs) vs)
/-- Quantized generator list for `p49_r512_m2_4_s2_c0`. -/
def rkmHbHi64_c64_r512_m2_4_s2_c0 : List ℤ := altBuildHbFrom 128 512 272829607142 0 128
/-- Input orbital vector for `p49_r512_m2_4_s2_c0`. -/
def rkmViHi64_c64_r512_m2_4_s2_c0 : List ℤ := rkmDec15Hi64T22 0 [116219000,550903694,3533219803,
  14673299039,54001510321,173809705666,499954221340,1305809942894,3126084568746,6909878999394,
  14185147895668,27169590102676,48731452319932,82094195725866,130215131422986,194866321396392,
  275590694507564,368844332356486,467694866225990,562366437062958,641693273584214,695228417900144,
  715473695869094,699582236155238,650006605898142,573891700439420,481415358828582,383599153541666,
  290226283915862,208387633911046,141903957535870,91568471407360,55935771412682,32307208419032,
  17617540582786,9054697191390,4377072291560,1985138290956,842137519178,332932623900,122102174730,
  41302746062,12790657318,3590664036,901346312,198317316,37046362,5541720,575112]
/-- Output orbital vector for `p49_r512_m2_4_s2_c0`. -/
def rkmVoHi64_c64_r512_m2_4_s2_c0 : List ℤ := rkmDec15Hi64T22 21 [2116352277,6247725977,12487618551,
  19268726315,23830287509,23390417239,16688762829,5019062259,7938857398,17534348828,20155287478,
  14843804948,3740149432,8820419809,18088078409,20731292111,15964037825,5604249111,6813294650,
  17395110510,23152239260,22750683058,16606811342,6448630488,5386289105,16635379373,25590832765,
  31314151137,33622735417,32928582873,30007011001,25752550981,20958524711,16132728019,11314086731,
  5762404117,2762904796,19659431144,56949274536,139911371416,318790495336,687942323778,
  1414720072390,2779281204936,5223696020662,9403963003860,16232167625882,26889509384828,
  42786834037190,65450853296940,96324155006258,136486163392184,186327838360686,245238824502282,
  311383137454862,381639649787668,451761662988932,516767402354738,571519475379406,611400727370470,
  632961947841186,634414479976904,615870294282392,579286066516406,528131408349856,466857365002668,
  400275531954048,332963908532140,268794813145044,210641730866282,160278056423742,118442747999864,
  85023459984298,59299191275496,40189728909918,26473248321388,16950706378612,10551456930396,
  6386014594084,3758219715128,2150821107272,1197083549356,647983445224,341143265348,174682789946,
  86996843744,42139465132,19851392974,9094642568,4051732930,1755155496,739196480,302631322,
  120422472,46565036,17493566,6383482,2261922,778042,259702,84078,26380,8014,2352,660,172,40,6]
/-- Quantized generator list for `p49_r512_m2_4_s3_c0`. -/
def rkmHbHi64_c64_r512_m2_4_s3_c0 : List ℤ := altBuildHbFrom 288 512 132582514705 0 288
/-- Input orbital vector for `p49_r512_m2_4_s3_c0`. -/
def rkmViHi64_c64_r512_m2_4_s3_c0 : List ℤ := rkmFlipGapsHi64T22
  [1,9,0,1,2,6,0,0,0,0,0,0,0,0,0,0,0,1,0,0,50,0,0,0,0,0]
  rkmVoHi64_c64_r512_m2_4_s2_c0
/-- Output orbital vector for `p49_r512_m2_4_s3_c0`. -/
def rkmVoHi64_c64_r512_m2_4_s3_c0 : List ℤ := rkmDec15Hi64T22 71 [45255485802,37483827832,
  7702858779,35307839857,13072347545,24479764672,25068042804,8655749559,26116167481,1720718803,
  29678821724,26517230132,3933803243,14410925183,7622201432,30629344904,17480381174,16100279625,
  27650866931,6323975543,17636551698,11456451956,13199374359,18910917285,2547598510,22753016374,
  13973852700,14733347249,26518285707,6545457927,18799435434,18624008266,5630634459,24158848389,
  14762781991,8975701040,15319947522,3469264167,22711492033,17595635135,7942431808,25738732586,
  14863238902,13187076655,27164861785,13029988109,11543891948,19990020090,5953329452,11790147935,
  10523862711,10568638274,27998944328,20196785482,7665319641,29305159621,24736809267,999690942,
  23714931394,22945414718,1272110196,18656493169,17681333205,502861872,14562054588,7585865610,
  17356137937,40638539441,43231943931,23312113117,1645315308,10397130568,2772611439,23714149347,
  32195565521,19349535785,6020326402,25015396344,23223556894,2110488918,21522986685,28651519399,
  13124150163,14170345098,34494097168,34797722612,15605067992,10296552471,26402678661,23329490715,
  5115604983,13944261084,19771803490,8003284164,14129047831,33188925657,37403611293,22827410101,
  4452327096,31238619028,44388727494,38128709000,16706557316,8846092333,26751939115,29483973247,
  16163156445,7494095994,31555597794,46201118414,46148596760,32606392432,11827868666,8161045915,
  20435975961,20826054547,8765959309,12502270130,36917426888,57870799880,70629906992,73440036376,
  66931942324,52753379682,32488362766,7177162046,22661903121,56245796247,90484335535,117057289231,
  120602526061,80956479499,18421055548,176148499464,356190036710,475054446950,401413925394,
  22819961073,933133029495,2363836262021,4148594202533,5818700218451,6525748604931,5017732452369,
  307529741986,11260234388892,29634080069718,56925248299772,94037420814900,141024929263362,
  196925396422148,259721347826720,326449196803332,393448117165544,456716262278534,512322934722910,
  556816389624330,587569289501738,603016263503616,602757445053528,587524072254836,559022938846464,
  519692164475218,472409289295206,420193607228626,365938956396886,312202965837910,261066550607498,
  214065647895722,172187605952944,135918284101724,105323006167838,80144610155190,59904148449432,
  43993375776092,31752143842840,22527523271374,15714463274192,10779886153308,7273300582914,
  4827439574930,3152287457678,2025369110780,1280522924814,796709862106,487817036348,293941948230,
  174304242994,101714010302,58405827178,32999152864,18343523696,10031199424,5395920468,2854762296,
  1485295640,759870642,382203486,188982650,91847162,43870304,20591208,9496092,4302342,1914734,
  836952,359266,151420,62642,25426,10118,3944,1498,550,192,62,16,2]
/-- Quantized generator list for `p49_r512_m2_4_s4_c0`. -/
def rkmHbHi64_c64_r512_m2_4_s4_c0 : List ℤ := altBuildHbFrom 512 512 83248563025 0 512
/-- Input orbital vector for `p49_r512_m2_4_s4_c0`. -/
def rkmViHi64_c64_r512_m2_4_s4_c0 : List ℤ := rkmFlipGapsHi64T22
  [0,2,0,0,0,5,1,0,0,0,0,1,0,0,0,0,0,4,0,1,0,2,0,0,3,1,0,3,0,0,1,0,0,0,0,5,0,0,0,3,4,0,0,1,0,0,4,3,
  2,3,0,0,0,1,0,0,1,0,0,0,0,0,4,0,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,43,0,6,0,0,0,6,0,6,0,0]
  rkmVoHi64_c64_r512_m2_4_s3_c0
/-- Part `0` of `rkmWHi64T22o2`. -/
def rkmWHi64T22o2_p0 : List ℕ := [11379200310,9128701477,12597121879,4434218194,16141699815,
  8525837101,50719094621,84723252276,161594139917,256573836836,403535758817,496291933548,
  560141291125,471597210544,264981763537,49538980591,312397898082,430650377813,323070771986,
  12248695161,265572191503,395255697494,243823250953,124343407253,349956679750,299834710233,
  18296967742,289997616616,309556737413,72868090596,279176826882,358582832103,87832181690,
  243268482176,304319775147,20263746792,307549410484,289362137295,52157248057,331387720202,
  243927868111,95315618073,345762333882,142865002107,234552663651,283424715680,20214910220,
  311334141399,218045158840,180538638134,361497797955,53322830306,308360891562,253220816459,
  130555968749,315643233928,67686678069,286004149451,198604587310,160015760412,306112163749,
  6973234468,344893635532,174221312459,260768173047,293463573912,73098663304,350487405311,
  86468210564,287123405178,221930805033,201959573311,276803455136,78758100484,325681036909,
  4505805180,273884217816,183868444923,276392943287,262514520816,156307280124,361880231277,
  64742378415,337909717454,87116038423,307786574261,189733990116,248839429048,255080380645,
  186477072967,292491823710,119125611208,336717357863,84695057577,313714236050,38205378075,
  353807110675,114552227226,343693516580,196405262533,308597172569,260620175664,246669652702,
  319079108375,206443806865,323307103332,142508157026,335097107785,93780728685,365167106346,
  96775793592,351790927563,62876049133,373908527992,50682618026,369375161831,7100923940,
  408717950350,26746065967,410581956049,70991642736,441387546638,50947718461,398156025921,
  77303677664,381992242412,100929733711,418218260487,34245499960,369084174058,51057680779,
  415127364289,17880649889,400980109216,47311086982,401766842949,64849281797,426507158324,
  110332560716,419787842009,130281971517,435249365472,186089858246,413949455549,237324046445,
  375107947776,290246647940,314514161275,337329533359,234101566350,360587113720,171891653297,
  405243809607,87086660074,445217021088,16516574972,473814914885,150117738605,452544036964,
  273582348928,396521797575,384696556135,296379630812,449564104664,199925593701,519891537377,
  51398658738,549292048910,151358801874,460391954319,285409682941,358507884026,408350229882,
  216363078981,511531675471,4041763046,522103915242,207877942818,466366729011,427623318201,
  293695701758,559448059472,84129434419,642474439513,221696230093,540310859168,461531212932,
  334283482679,621640617327,31120217228,633683053758,299235829704,457060530159,523716092011,
  188834887192,652851361258,198373378974,547292911163,532009301517,253288756662,732513744854,
  221099322956,594759726023,578310514185,266412847384,769772994274,217805334580,643939135211,
  638298357631,226463222742,784792266998,297804137328,585507339077,715968017267,71432995794,
  784646170432,538887756428,365665898827,828702577891,279741837649,635130688776,812387245164,
  10297847826,833137005867,697644987951,285999018038,960789070912,511532548792,556686371215,
  1006218885765,312197453599,743062887850,981038737304,145620854098,849026679721,937433832349,
  26502340091,937016598384,951751149208,30484231849,1054171923915,1093605587675,66087530797,
  1056986476408,1173109747122,130769729384,1092735654227,1316420208475,292382456805,1050451039058,
  1478018613230,587252794930,848649768631,1588185251283,993699079137,460760860414]
/-- Part `1` of `rkmWHi64T22o2`. -/
def rkmWHi64T22o2_p1 : List ℕ := [1608200724734,1527083850188,247938651498,1278642032197,
  1896008013521,1104486964415,554538809200,1879274119550,1882174667716,515217099564,1290582445625,
  2289778172149,1788936845113,96031103563,1719981801128,2534788530202,1846496414402,30291458724,
  1912921296525,2915216545505,2396529179421,553969939249,1733772242764,3332180923354,3401485824680,
  1804740752316,822767097805,3362681097041,4702128605413,4186826581939,1860860793147,1557560172404,
  4909446388564,6944226828174,6699786984106,3837280383198,1153339015481,6962619527593,
  11733371879885,13561316818621,11100275982963,4093067431103,6343247988738,17786394339390,
  26949885057936,30421902513684,25552648762088,11292633947884,11225900927515,38534398908635,
  65183133722209,84569014528393,90079019202861,76309759726907,40104611218409,18802237194928,
  97649049623164,191017556587544,291611764734888,391278709037204,482081677471010,557251628034110,
  611886129713556,643324158993828,651186712845876,637126689216536,604369132530978,557140842042140,
  500086673162126,437752438675032,374187358516318,312689435927682,255690916594060,204761988215462,
  160700523388620,123673275501972,93377485635016,69198849137896,50349932340394,35980734153604,
  25259178906194,17423554163028,11811358002360,7870024905350,5154974102486,3319767117846,
  2102198972178,1309117326668,801817577674,483080396868,286329387014,166982995332,95828949456,
  54125089262,30091078410,16469258292,8874974486,4709511588,2461263572,1266981630,642491388,
  320997980,158025354,76663846,36655760,17275418,8025940,3676114,1660158,739286,324646,140588,60036,
  25270,10470,4260,1698,656,238,76,20,2]
/-- Output orbital vector for `p49_r512_m2_4_s4_c0`. -/
def rkmVoHi64_c64_r512_m2_4_s4_c0 : List ℤ :=
  rkmDec15Hi64T22 135 (rkmCatNHi64T22 rkmWHi64T22o2_p0 rkmWHi64T22o2_p1)
/-- Quantized generator list for `p49_r512_m2_4_s5_c0`. -/
def rkmHbHi64_c64_r512_m2_4_s5_c0 : List ℤ := altBuildHbFrom 896 512 56358198412 0 512
/-- Input orbital vector for `p49_r512_m2_4_s5_c0`. -/
def rkmViHi64_c64_r512_m2_4_s5_c0 : List ℤ := rkmFlipGapsHi64T22
  [0,1,3,9,6,1,2,0,0,1,0,5,1,6,0,6,2,3,0,1,5,2,0,2,0,2,2,0,2,0,2,2,0,1,2,0,1,2,0,2,0,3,1,0,2,1,0,2,
  3,3,1,1,1,1,6,1,6,0,2,0,0,2,6,0,2,0,0,4,7,0,7,2,1,27,0,0,0,12,0,0,0,6,0,0,0,0,4,0,0,0,4,0,0,0,0,5,
  0,0,0,0,0,6,0,0,0,0,0,0,39,0,0,0,0,8,0,0,0]
  rkmVoHi64_c64_r512_m2_4_s4_c0
/-- Part `0` of `rkmWHi64T22o3`. -/
def rkmWHi64T22o3_p0 : List ℕ := [104913943285,16974001376,37635344400,292347523984,71540035032,
  484507517139,279535682994,80480548084,81634788438,26978154946,84054713150,378850701240,
  125984519521,31755562667,36201582017,65480956673,89095581685,100116130595,93417688681,56740172141,
  129973656691,28736277043,61756656861,426243168973,126086562078,45136668107,34378404347,
  195688133249,314023513048,431343980547,164065318523,268134907011,258514669769,591229183321,
  577165820773,88919822887,685865179689,124608735025,180017201065,206257558017,24830102760,
  271694938014,181308229148,171052571992,341876836082,46611462591,154319739005,76212128981,
  86400648939,16764354493,114209979129,59636729752,412077639152,128567204711,116480444902,
  51169352315,115317404711,247780303285,114392685335,61203598578,310072057928,65221199883,
  105516608959,152301157196,187159723691,205139896292,156545549442,59363180353,28887330910,
  495077834739,185921961879,123111722030,261168016000,548362119762,123396949196,304712780637,
  242056574953,307781773895,16040910427,150751838700,117567907678,120763187952,424732722697,
  72753682826,295466728326,61647358783,94119101972,6858805742,179218721115,143349682297,
  321295904992,187765332661,255084225132,74076228945,166644819285,312888121415,394503702254,
  257215375333,446384527510,415975571905,422354663290,242310334079,320995753660,144948510075,
  148093695597,331220668441,78727069628,183443498797,73832063198,175593986216,225136741000,
  216197638446,223533053827,222794201744,106287505079,26018867754,164905931913,34729624178,
  65616549187,250365210290,323229974499,75096632040,155744563830,383299192967,112636855101,
  102382708434,74771851800,450243636392,80709889042,3928675231,38948244495,103849970725,
  195250959186,664295129043,604006775946,185983323727,515585750324,907785667639,636969827928,
  711028117115,1060284019746,2283921453671,2173406433074,2275595599931,2459045727034,2360750691351,
  1605344540538,1227638201263,953222292008,400010934660,2015959789171,1908991117130,2404935405591,
  1786856727164,1030369184139,345255802784,34694936654,738240688793,1527359182998,1310121935245,
  1781016642372,1474496260859,828394064986,1629466060580,1425899605999,1671848330970,1608548759747,
  1079306176284,160407061596,1612604630923,1880227125010,1765248996367,1233876735364,406691528300,
  1691494700657,1899042570516,1938784294425,649034975540,1093357785292,2271937760535,1649266266638,
  909192685707,366428264207,1575055746336,2337005733059,516616040248,394272150410,969100841223,
  1061787086774,1251560807427,386606684294,1097634906420,1115348079211,1247463264402,404926743355,
  1196969847587,1327713959716,593119993823,249007032035,200039347446,992788602005,645677058630,
  272643530485,331286998819,689011417564,1232476042759,775226494694,1084133334002,1900689210615,
  629305736532,476579833346,1250435168967,1413909497394,640960911751,1433708938377,1701836049418,
  919425674881,500976816661,1940323074704,1804495851161,245971518729,2214532853108,1790521607555,
  153094020500,1893500832636,1875219000991,697167154248,1321708530012,2463406441211,1322962568008,
  1582942745368,2836293684117,1295791898858,1652501510914,2901111551099,1452074889916,1669729797704,
  3769618676587,666522356998,2448648663812,2800639824699,279446728506,2007303319912,2642420565171,
  426274314418,2170426894916,3210434894829,635514369969,2571262593760,2199495022929,680085472995,
  2446107417086,2434924278293,980490182205,3605012546854,2130811230693]
/-- Part `1` of `rkmWHi64T22o3`. -/
def rkmWHi64T22o3_p1 : List ℕ := [3055164201129,3765648524590,58455893228,4071986737311,
  2266310028664,1320206201424,4638593771461,615881782188,3481451333776,3276397372995,2153744775125,
  3247195366842,112733926032,1117908587627,2081330831298,803888443563,1976396051951,2944766918832,
  607066472956,4092162494677,1225451751954,3542479118212,3082760361165,2033016318271,3665810700304,
  508442194765,3377991255067,2875763731120,2176729790216,4688104921543,1147790077281,4424058529784,
  811970145725,3863304059807,1544629840968,1531537644016,2651098807383,475803449602,3026931881390,
  2033352550643,2655938252775,2936267906484,1722410159152,2994928696727,177502697169,2767246312916,
  1102914631671,1813257739597,2341313527962,519673807706,3481265303843,661186760732,4277753407498,
  1450200767599,4342812518387,2131249467452,3899946762326,2629791442725,2925446388569,3169743202344,
  1569667059944,4262688309531,956172185861,4837722682642,479218159990,5121348229081,172569361023,
  5171465183298,140946554232,4815468440765,172002767713,4139320874826,173457841922,3186617528557,
  29088719587,1857990087794,1093100264817,1792829275123,1114981287904,828020065056,2226158152491,
  1347136576385,1656037097420,151717856122,2854312799107,650085093967,2718942583228,292755365304,
  2887239470479,657154474656,4713461963066,418144093120,5165947887045,721943610007,6900520178832,
  3183341593922,6938313095241,5747968150623,5786388628384,7987109162108,3594726632281,9264594152007,
  1405205299804,10756601331208,2377132859668,10367219083613,5712074128893,9833747877896,
  10901787488156,5461773265587,13892487195717,686235776481,13920849207688,6968717257690,
  11250802467171,12652119644977,5528363856310,16058237991612,2531572985736,15810335225863,
  12085336510781,8971789725608,17659318281062,1667235865268,16616052555073,11639146880759,
  9858477824048,18319195192798,1741245743066,18193947319463,15059736969329,7603036551276,
  21037729460380,8185406219168,14986103916485,19807261455477,284267663885,20070832548480,
  16960614691032,5957334381449,21873562575237,12129264468975,12723421875882,25169019644612,
  11226462479740,14702480846567,25656637234677,10473273002965,15152949293998,25151287298114,
  9197638047406,17555871679563,29528743610141,14956910424013,13548747848284,30843012428910,
  21657907709566,6443347175961,29916414914057,28961654575375,3392619303243,27569782699054,
  40350691559526,24695614091838,9049433971327,37499250561467,40444811543297,14329076721115,
  25551890597838,54745242214830,54546101356022,23008293139438,23912539294787,61022389752799,
  67106593711283,35683642498165,21751758179488,80942329650320,115552785037012,108320839056398,
  58091373076528,19620116141239,98097122500139,148335544746729,147988456123891,87464981219859,
  28279935622630,182118812935238,349922772031606,506639629604304,631547860472102,711572730391608,
  742318542650606,727125858963466,674854795603118,597197458984184,506196897032676,412401112196724,
  323811372547894,245567383485772,180181960540380,128094635125096,88335448581788,59147515512402,
  38483066971054,24344480819446,14980801935428,8970703105710,5228552634774,2966649895852,
  1638748914866,881296606878,461395709866,235139607424,116633419872,56298717958,26441008600,
  12080435248,5368226878,2319749196,974613142,398039222,157996016,60942596,22839248,8315028,2940380,
  1009798,336730,108992,34222,10408,3054,852,220,48,6]
/-- Output orbital vector for `p49_r512_m2_4_s5_c0`. -/
def rkmVoHi64_c64_r512_m2_4_s5_c0 : List ℤ :=
  rkmDec15Hi64T22 20 (rkmCatNHi64T22 rkmWHi64T22o3_p0 rkmWHi64T22o3_p1)
end

public section
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private abbrev bZ : ℕ := 1000000000000000
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
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | Int.negSucc _ :: _ => none
  | Int.ofNat n :: xs =>
    match uToNatHb xs with
    | some ns => some (uConsNat n ns)
    | none => none
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfNatHb ns
private theorem uToNatHb_sound : ∀ (hb : List ℤ) (ns : List ℕ), uToNatHb hb = some ns →
    hb = uOfNatHb ns
  | [], _, h => by injection h with h'; subst h'; rfl
  | Int.negSucc _ :: _, _, h => by dsimp only [uToNatHb] at h; cases h
  | Int.ofNat n :: xs, _, h => by
    dsimp only [uToNatHb] at h; revert h; cases hxs : uToNatHb xs with
    | none => intro h; dsimp only at h; cases h
    | some ms =>
      intro h; dsimp only at h; injection h with h'; subst h'
      rw [uConsNat_eq, uOfNatHb, uToNatHb_sound xs ms hxs]
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
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  match uToNatHb hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some bns =>
    match bEnc bZ v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vns =>
      fH4 (toH4 (mkHbZ bZ bns)) fun h4 =>
        fQ4 (toQ4 vns) fun vs0 =>
          match bIter bZ k mL cL h4 vs0 with
          | none => muxUltraIterFullT16Rkm k mL cL hb v
          | some out => bDec bZ (q4L out)
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; cases hh : uToNatHb hb with
  | none => rfl
  | some bns =>
    dsimp only; cases hv : bEnc bZ v with
    | none => rfl
    | some vns =>
      dsimp only; rw [fH4_eq, fQ4_eq]
      cases hi : bIter bZ k mL cL (toH4 (mkHbZ bZ bns)) (toQ4 vns) with
      | none => rfl
      | some out =>
        dsimp only; rw [bIter_sound bns bZ k mL cL (toQ4 vns) out hi,
          q4L_toQ4, ← uToNatHb_sound hb bns hh, bEnc_sound bZ v vns hv]
private def bSlideChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    fN (altIntLen inF) fun len0 => muxIntListEq (fIter steps maxLen len0 hbF inF) outF
private theorem bSlideChk_sound {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : bSlideChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold bSlideChk at h; dsimp only [fL, fN] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, fIter_eq] at h
  have h2 : muxUltraIterFullT16HiChk steps 0 maxLen hb vecIn vecOut = true := by
    unfold muxUltraIterFullT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq]; exact h
  exact muxUltraIterFullT16HiChk_sound h2
private theorem bCh (c : ℕ) {a b m : ℕ} {hb vi vm vo : List ℤ}
    (h1 : muxFastIterFullT16 a m hb vi = vm) (h2 : bSlideChk b m hb vm vo = true)
    (hc : a + b = c) : muxFastIterFullT16 c m hb vi = vo :=
  Eq.mp (congrArg (fun k => muxFastIterFullT16 k m hb vi = vo) hc)
    ((muxFastIterFullT16_add a b m hb vi).trans
      ((congrArg (muxFastIterFullT16 b m hb) h1).trans (bSlideChk_sound h2)))
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def pzeros : ℕ → List ℤ
  | 0 => []
  | k + 1 => Int.ofNat 0 :: pzeros k
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
      | 0 => primOfNatForced (Nat.div w 2)
      | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCatZ (z : ℕ) : List (List ℕ) → List ℤ
  | [] => pzeros z
  | ws :: wss => pzig ws ++ pzigCatZ z wss
private def phbv_g0 : List ℤ := pzigCatZ 0
 [
 [279377517713408,393168574012718,479162119139172,550548244697434,612462058752310,667549768398204,
 717390601574228,763018128934172,805153406941488,844323665405842,880928567309678,915279859266414,
 947626423254028,978170812470494,1007080566585468,1034496192153198,1060536937678618,
 1085305066446020,1108889079508370,1131366188391176,1152804240907558,1173263241292170,
 1192796564645090,1211451937756958,1229272239099526,1246296157204068,1262558736959652,
 1278091836336816,1292924510878378,1307083339457152,1320592701909030,1333475016950962,
 1345750947104572,1357439576037302,1368558562709786,1379124275912130,1389151912131808,
 1398655599184318,1407648487626154,1416142831636202,1424150060780222,1431680843850618,
 1438745145790452,1445352278559142,1451510946671032,1457229288032690,1462514910616248,
 1467374925431494,1471815976196222,1475844266050582,1479465581615332,1482685314654446,
 1485508481568694,1487939740917486,1489983409140732,1491643474630288,1492923610281024,
 1493827184634260,1494357271711150,1494516659619758,1494307858007458,1493733104418914,
 1492794369609848,1491493361857172],
 [1489831530297260,1487810067315696,1485429910003724,1482691740688722,1479595986538236,
 1476142818229204,1472332147666018,1468163624722750,1463636632976160,1458750284386786,
 1453503412875504,1447894566731950,1441921999779282,1435583661206468,1428877183964328,
 1421799871604838,1414348683424128,1406520217747826,1398310693172478,1389715927547910,
 1380731314452028,1371351796870594,1361571837748990,1351385387029460,1340785844724090,
 1329766019498854,1318318082154770,1306433513285384,1294103044261228,1281316590536726,
 1268063176086320,1254330847546230,1240106576355390,1225376146839464,1210124027747260,
 1194333224204924,1177985106367662,1161059210178206,1143533004526772,1125381617668720,
 1106577513881894,1087090108879942,1066885309219718,1045924956532380,1024166151405764,
 1001560423463524,978052702589260,953580029741568,928069921904182,901438270410982,873586598587876,
 844398422198362,813734325043046,781425146840276,747262314284490,710983696237218,672252151997888,
 630621543286662,585479877660194,535947358034814,480675906439288,417400410086854,341713392140694,
 242262859245042]]
private def phbv_g1 : List ℤ := pzigCatZ 0
 [
 [203646742586880,287218652037738,350812431986400,403977856249062,450424776503612,492061137240344,
 530023439407366,565054172097698,597670447264622,628249768966510,657077872800314,684377328076594,
 710325593295578,735066923715104,758720512595318,781386228231140,803148762153668,824080695788814,
 844244811791898,863695865942450,882481966103120,900645659896728,918224803044802,935253260194588,
 951761476171666,967776945833118,983324603724152,998427149687872,1013105322866120,
 1027378133768934,1041263062013774,1054776225757280,1067932527630744,1080745781051758,
 1093228820051300,1105393595177918,1117251257582564,1128812233021488,1140086287220228,
 1151082583803432,1161809735801318,1172275851584798,1182488575950660,1192455126970160,
 1202182329124618,1211676643176664,1220944193162970,1229990790841474,1238821957881392,
 1247442946046410,1255858755589276,1264074152048374,1272093681613300,1279921685206196,
 1287562311408038,1295019528344004,1302297134628904,1309398769462234,1316327921952518,
 1323087939741854,1329682036994024,1336113301802790,1342384703071180,1348499096907318],
 [1354459232577794,1360267758055546,1365927225195538,1371440094568410,1376808739979370,
 1382035452697042,1387122445414770,1392071855964772,1396885750803768,1401566128287028,
 1406114921746328,1410534002385978,1414825182009880,1418990215591482,1423030803697534,
 1426948594775644,1430745187314846,1434422131887646,1437980933081358,1441423051325920,
 1444749904624844,1447962870195462,1451063286024116,1454052452341590,1456931633023656,
 1459702056921234,1462364919124408,1464921382164166,1467372577155510,1469719604885324,
 1471963536848112,1474105416232578,1476146258861756,1478087054089248,1479928765653970,
 1481672332495594,1483318669532816,1484868668406380,1486323198188654,1487683106061526,
 1488949217964176,1490122339212238,1491203255089786,1492192731415420,1493091515083754,
 1493900334583422,1494619900492742,1495250905954024,1495794027127562,1496249923626142,
 1496619238930998,1496902600789980,1497100621598722,1497213898765522,1497243015060598,
 1497188538950390,1497051024917468,1496831013766646,1496529032917826,1496145596686068,
 1495681206549358,1495136351404548,1494511507811836,1493807140228246],
 [1493023701230416,1492161631727102,1491221361161668,1490203307704932,1489107878438594,
 1487935469529578,1486686466395484,1485361243861430,1483960166308478,1482483587813856,
 1480931852283178,1479305293574802,1477604235616532,1475828992514772,1473979868656288,
 1472057158802696,1470061148177780,1467992112547732,1465850318294414,1463636022481700,
 1461349472914956,1458990908193734,1456560557757674,1454058641925682,1451485371928368,
 1448840949933778,1446125569066362,1443339413419228,1440482658059580,1437555469027346,
 1434558003326916,1431490408911930,1428352824663034,1425145380358514,1421868196637686,
 1418521384956946,1415105047538322,1411619277310398,1408064157841426,1404439763264456,
 1400746158194292,1396983397636048,1393151526885074,1389250581418006,1385280586774660,
 1381241558430484,1377133501659254,1372956411385660,1368710272027442,1364395057326668,
 1360010730169744,1355557242395708,1351034534592330,1346442535879510,1341781163679414,
 1337050323472772,1332249908540722,1327379799691506,1322439864971324,1317429959358572,
 1312349924440636,1307199588072402,1301978764015486,1296687251557244],
 [1291324835108442,1285891283778458,1280386350926788,1274809773689502,1269161272479282,
 1263440550457480,1257647292976578,1251781166991298,1245841820436480,1239828881569668,
 1233741958276268,1227580637334880,1221344483640292,1215033039381386,1208645823171012,
 1202182329124618,1195642025884200,1189024355583812,1182328732752616,1175554543151026,
 1168701142535234,1161767855344890,1154753973308320,1147658753959146,1140481419057588,
 1133221152909188,1125877100572950,1118448365950166,1110934009744412,1103333047282178,
 1095644446182688,1087867123864216,1079999944873004,1072041718019444,1063991193304526,
 1055847058617888,1047607936186662,1039272378752130,1030838865448610,1022305797356106,
 1013671492695004,1004934181627358,996092000625102,987142986360718,978085069070372,
 968916065333246,959633670203572,950235448623538,940718826035646,931081078101970,921319319424886,
 911430491148794,901411347304854,891258439740134,880968101448492,870536428091902,859959257467226,
 849232146633248,838350346364832,827308772543582,816101974025148,804724096439512,793168841278658,
 781429419501464],
 [769498498732398,757368142941206,745029743255004,732473938258870,719690521768604,706668335585910,
 693395144139960,679857487135898,666040505309680,651927733044094,637500849812044,622739380005958,
 607620327432530,592117726223374,576202083566348,559839680626368,542991684927736,525613008111968,
 507650813740326,489042534535186,469713186398346,449571648201610,428505374826382,406372653043332,
 382990841960576,358117717248826,331420222356488,302418361981278,270374726143518,234046858359352,
 191010133959870,134999993109124]]
private def pvm_c1_1 : List ℤ := pzigCatZ 143
 [
 [1875148412,13690460771,9593029690,13935347891,5578714961,7861121264,2721227739,449277681,
 7839056628,2680663030,1618363525,4809324992,6433038884,12005530715,7951417127,23550596641,
 22933846916,44900272403,26511500764,78538800259,748528006,16517823715,31592452835,45273535810,
 8820181655,20094834955,38814769508,4753474093,26212197513,32764918508,18253755946,32912519735,
 1371291098,36313534984,13026861523,47905080963,4429893471,25786122850,11259532561,35932962329,
 7796918678,55136345422,35562574688,16910320469,24731221035,19027286620,50540453758,27610382302,
 19869316385,33661999495,3967723502,56249277556,75058596142,47099608476,421620053,27730458471,
 16138531205,25229686874,66848953570,86644346046,72027370520,34159174824,15021959625,57034613875],
 [83962984495,94721421931,90837062273,81874754255,72515099641,64649759621,52200176701,2388920067,
 157397409134,571720445698,1502198215908,3367439943986,6787280223158,12612960226946,
 21914927809290,35926441301242,55933597277602,83100903505712,118255023222880,161662903717588,
 212835610281050,270400748309540,332089355497182,394856264101460,455124928032422,509132453263024,
 553331172386420,584782546897658,601478577009354,602544924732196,588301709770928,560177906397088,
 520498551464064,472186321847040,418429532179518,362364789863016,306811444523488,254082393509056,
 205882189909008,163288830583314,126803286812258,96444392797170,71866541427378,52481266424994,
 37568603458984,26368988721170,18151195434246,12256138640438,8119666144494,5279213625094,
 3369491230446,2111694657658,1299685889774,785560849952,466164028488,271433253762,154937330972,
 86593464876,47315518162,25233619502,13110589842,6623684924,3247445568,1541793310],
 [707197098,312549340,132658024,53842002,20771696,7548228,2545176,774180,199110,34578,2659,6353,
 3915,1769,653,191,39,3]]
private def pvm_c1_2 : List ℤ := pzigCatZ 104
 [
 [5596586574,3974151134,29531829790,22490582139,43918113252,46931345969,6215226886,16985270112,
 30734130547,18356626398,21172623022,34421588915,7377583371,26149659990,13701780271,23241912357,
 16953257666,7297721988,29776921533,7207676903,30493177326,7132244276,27217006049,6158780653,
 23076167450,3628612064,20418206125,3908415592,34693702458,15058983358,26063995689,23651739047,
 9724794320,17704532724,10488358281,20838356827,4471842908,23434388422,586400059,41601904197,
 45990261247,14417814697,6773557038,8963668723,35882322189,30895730781,4024425652,26913823670,
 13404691676,17250715771,26133997047,1179242345,27368058020,26677884182,426952081,23155472923,
 15959960963,14882411804,36304099658,24417776528,11006033917,39623448389,38798273349,11177554769],
 [17947065754,23582756268,4022959098,20469057765,27583065835,9458136983,22805506404,46611625348,
 44834422234,19072089452,13374105641,32973529975,28767973901,2972399867,30153932936,52672488514,
 54179688316,36416273500,9485155640,13930609393,23081009085,13467933807,10856900198,40129050726,
 64483302234,77177472568,74885036944,57931825132,30578622800,739274831,30419667197,54809599177,
 70969035369,75815839465,67213579987,45821458801,16858056515,7178829638,2842919850,65074932915,
 235549103705,530045671749,916409848259,1258784163645,1257762427051,390844898507,2130179451948,
 7365237303012,16598674608818,31230277730072,52607624338606,81815539036830,119450948138182,
 165420877088520,218804017978914,277809817164940,339854081985490,401750197132574,459994762053798,
 511109860907544,551994163760738,580233361481886,594327430748600,593806571455892],
 [579226313558184,552051242040760,514452263191686,469051839851336,418654362490780,365995480735376,
 313536420227448,263319074587600,216887004596334,175268111595958,139007883732370,108238305987714,
 82766696716788,62170292982108,45885485132836,33284299972436,23734314500774,16641165145354,
 11474974000446,7783321371430,5193962376598,3410489705754,2203776091940,1401463555506,
 877142642532,540282660116,327491198846,195320979826,114601563304,66134413388,37527263626,
 20932608296,11474198722,6178790992,3267555916,1696430354,864366424,432080788,211833530,101822846,
 47970488,22143038,10011200,4431666,1920068,813880,337372,136692,54102,20904,7876,2890,1026,352,
 110,30,8]]
private def phbv_g2 : List ℤ := pzigCatZ 0
 [
 [170493057075200,240642668618684,294149111265454,338988148637800,378255674176648,413542664496824,
 445796109409696,475634237387226,503487309175200,529669203043294,554417329763478,577916489192130,
 600313925190666,621729251158490,642261233997514,661992573174800,680993355169400,699323606455476,
 717035217079800,734173414838928,750777912186860,766883810598402,782522322338530,797721352816362,
 812505975124000,826898820224228,840920400441242,854589379698430,867922800855304,880936278196554,
 893644161397154,906059675973290,918195044220252,930061589857186,941669828988374,953029549510200,
 964149880711794,975039354512874,985705959537426,996157189023770,1006400083410340,
 1016441268304488,1026286988433086,1035943138083950,1045415288472472,1054708712405636,
 1063828406563474,1072779111674014,1081565330820800,1090191346090524,1098661233741596,
 1106978878051588,1115147983981918,1123172088781318,1131054572635090,1138798668454630,
 1146407470890824,1153883944645452,1161230932146500,1168451160646080,1175547248793346,
 1182521712729268,1189376971745238,1196115353543200],
 [1202739099131182,1209250367384792,1215651239302170,1221943721977350,1228129752314536,
 1234211200503724,1240189873276238,1246067516957030,1251845820329108,1257526417324088,
 1263110889551662,1268600768679646,1273997538675324,1279302637917866,1284517461190814,
 1289643361562906,1294681652164800,1299633607868706,1304500466877368,1309283432228306,
 1313983673218828,1318602326756872,1323140498642354,1327599264783386,1331979672351352,
 1336282740878610,1340509463302262,1344660806957228,1348737714521586,1352741104917010,
 1356671874166866,1360530896214408,1364319023703310,1368037088722666,1371685903518408,
 1375266261173000,1378778936255106,1382224685440886,1385604248108370,1388918346906406,
 1392167688299424,1395352963089346,1398474846915744,1401534000735406,1404531071282288,
 1407466691508896,1410341481009932,1413156046429158,1415910981850208,1418606869172188,
 1421244278470738,1423823768345272,1426345886253022,1428811168830506,1431220142203006,
 1433573322282592,1435871215055200,1438114316857270,1440303114642424,1442438086238560,
 1444519700595866,1446548418026068,1448524690433356,1450448961537284],
 [1452321667088032,1454143235074320,1455914085924290,1457634632699650,1459305281283358,
 1460926430561084,1462498472596750,1464021792802336,1465496770102206,1466923777092168,
 1468303180193472,1469635339801940,1470920610432420,1472159340858744,1473351874249360,
 1474498548298800,1475599695355138,1476655642543604,1477666711886464,1478633220419348,
 1479555480304100,1480433798938340,1481268479061796,1482059818859570,1482808112062402,
 1483513648044098,1484176711916140,1484797584619666,1485376543014838,1485913859967724,
 1486409804434780,1486864641544994,1487278632679784,1487652035550740,1487985104275236,
 1488278089450038,1488531238222934,1488744794362472,1488918998325852,1489054087325046,
 1489150295391200,1489207853437358,1489226989319584,1489207927896520,1489150891087416,
 1489056097928720,1488923764629224,1488754104623844,1488547328626060,1488303644679070,
 1488023258205678,1487706372056978,1487353186559840,1486963899563268,1486538706483634,
 1486077800348842,1485581371841432,1485049609340690,1484482698963740,1483880824605704,
 1483244167978920,1482572908651246,1481867224083506,1481127289666058],
 [1480353278754552,1479545362704866,1478703710907266,1477828490819800,1476919868000940,
 1475978006141530,1475003067095994,1473995210912890,1472954595864784,1471881378477490,
 1470775713558658,1469637754225772,1468467651933538,1467265556500698,1466031616136266,
 1464765977465224,1463468785553680,1462140183933494,1460780314626402,1459389318167640,
 1457967333629086,1456514498641920,1455030949418842,1453516820775824,1451972246153432,
 1450397357637720,1448792285980704,1447157160620444,1445492109700708,1443797260090266,
 1442072737401800,1440318666010452,1438535169072000,1436722368540696,1434880385186760,
 1433009338613530,1431109347274300,1429180528488820,1427222998459512,1425236872287350,
 1423222263987470,1421179286504476,1419108051727462,1417008670504760,1414881252658428,
 1412725906998442,1410542741336674,1408331862500574,1406093376346630,1403827387773586,
 1401534000735406,1399213318254028,1396865442431878,1394490474464168,1392088514650976,
 1389659662409118,1387204016283804,1384721673960104,1382212732274204,1379677287224476,
 1377115433982360,1374527266903040,1371912879535970,1369272364635200],
 [1366605814169522,1363913319332476,1361194970552150,1358450857500844,1355681069104568,
 1352885693552366,1350064818305514,1347218530106546,1344346914988136,1341450058281846,
 1338528044626712,1335580957977720,1332608881614114,1329611898147596,1326590089530374,
 1323543537063108,1320472321402696,1317376522569970,1314256219957250,1311111492335788,
 1307942417863092,1304749074090138,1301531537968470,1298289885857190,1295024193529846,
 1291734536181196,1288420988433896,1285083624345062,1281722517412748,1278337740582316,
 1274929366252720,1271497466282684,1268042111996800,1264563374191522,1261061323141086,
 1257536028603330,1253987559825434,1250415985549572,1246821374018490,1243203792980988,
 1239563309697340,1235899990944620,1232213903021958,1228505111755726,1224773682504632,
 1221019680164770,1217243169174560,1213444213519662,1209622876737774,1205779221923410,
 1201913311732562,1198025208387346,1194114973680542,1190182668980090,1186228355233534,
 1182252092972372,1178253942316388,1174233962977884,1170192214265888,1166128755090278,
 1162043643965872,1157936939016444,1153808697978700,1149658978206194],
 [1145487836673188,1141295329978470,1137081514349116,1132846445644200,1128590179358452,
 1124312770625884,1120014274223348,1115694744574062,1111354235751082,1106992801480726,
 1102610495145972,1098207369789784,1093783478118420,1089338872504686,1084873604991142,
 1080387727293288,1075881290802680,1071354346590038,1066806945408292,1062239137695594,
 1057650973578300,1053042502873904,1048413775093950,1043764839446890,1039095744840918,
 1034406539886762,1029697272900454,1024967991906050,1020218744638322,1015449578545430,
 1010660540791538,1005851678259412,1001023037552996,996174664999932,991306606654068,
 986418908297934,981511615445186,976584773343012,971638426974526,966672621061122,961687400064800,
 956682808190472,951658889388238,946615687355626,941553245539820,936471607139854,931370815108778,
 926250912155810,921111940748448,915953943114568,910776961244498,905581036893064,900366211581610,
 895132526600000,889880023008604,884608741640240,879318723102116,874010007777744,868682635828818,
 863336647197096,857972081606240,852588978563644,847187377362242,841767317082296],
 [836328836593158,830871974555022,825396769420652,819903259437084,814391482647330,808861476892034,
 803313279811136,797746928845506,792162461238556,786559914037848,780939324096674,775300728075622,
 769644162444120,763969663481982,758277267280910,752567009746000,746838926597226,741093053370914,
 735329425421182,729548077921390,723749045865556,717932364069764,712098067173560,706246189641328,
 700376765763652,694489829658668,688585415273406,682663556385100,676724286602502,670767639367182,
 664793647954802,658802345476388,652793764879586,646767938949904,640724900311946,634664681430620,
 628587314612354,622492832006286,616381265605446,610252647247920,604107008618016,597944381247404,
 591764796516260,585568285654376,579354879742282,573124609712350,566877506349874,560613600294162,
 554332922039594,548035501936692,541721370193162,535390556874932,529043091907182,522679005075364,
 516298326026212,509901084268730,503487309175200,497057029982138,490610275791290,484147075570574,
 477667458155036,471171452247800,464659086420996,458130389116684],
 [451585388647776,445024113198938,438446590827494,431852849464312,425242916914692,418616820859232,
 411974588854706,405316248334910,398641826611522,391951350874936,385244848195104,378522345522356,
 371783869688226,365029447406254,358259105272804,351472869767850,344670767255768,337852823986120,
 331019066094432,324169519602958,317304210421444,310423164347880,303526407069252,296613964162282,
 289685861094158,282742123223268,275782775799922,268807843967062,261817352760972,254811327111984,
 247789791845172,240752771681046,233700291236226,226632375024130,219549047455648,212450332839800,
 205336255384396,198206839196702,191062108284082,183902086554638,176726797817854,169536265785228,
 162330514070898,155109566192260,147873445570592,140622175531658,133355779306320,126074280031132,
 118777700748946,111466064409486,104139393869956,96797711895598,89441041160286,82069404247084,
 74682823648824,67281321768654,59864920920606,52433643330146,44987511134716,37526546384282,
 30050771041876,22560206984116,15054876001756,7534799800192]]
private def pvm_c2_1 : List ℤ := pzigCatZ 244
 [
 [59491826901,15420319357,732369732,2493312255,15211130503,10272434928,34914946878,17820763010,
 8524433536,6151090893,4289793298,7810980157,27604118301,37814505831,8414738543,5367899888,
 9487821852,5205905414,32665571006,15738918718,2252747215,10536342097,46492073725,17678951595,
 20835065172,17351421194,6215786285,16581728159,6525087046,1204729737,12711647881,19664003786,
 4777897295,14627386558,16005400879,11104255992,9490734617,1789384297,2882732079,36679726835,
 27047920507,2580990804,22485021887,14614364748,1889140937,3886585274,19003687240,21924381418,
 15817537513,14590158804,23938060450,18532428048,17816905504,32722487712,8787114763,9949687698,
 563938442,111604263,3449486165,4374999787,44329929304,5885870102,39441711753,10190776185],
 [8829501658,11507697303,1838530,30058549992,15508614874,789847384,1227845744,12176855344,
 18731032024,14888687292,21821864275,33323260829,8766791719,5829441559,32402753684,12800568395,
 8203504347,854789991,8819455002,7124078393,10570976283,18799893633,72464003,11014756651,
 7410017329,30357675511,42833691457,11962205881,19683197095,3782357070,11459768965,11061401723,
 25308285416,15644951926,12733095968,46143404184,50991156544,18586338090,14752604187,25007352817,
 12450429395,9092740762,12727510184,3448991708,9319844779,6820543719,479125688,5819804676,
 12825785975,41528007569,31662966985,44529028439,21261666911,36144170971,7949455232,22476319470,
 19778818676,47779589676,65305877917,71747187786,190060742215,289346746078,579139633167,
 759632328300],
 [993187355031,929779435106,662359636561,37299900778,653215583042,971003593741,462719152346,
 446803306542,1072725140261,287221973414,683419094630,984167051813,297422345925,1215578084016,
 61465384299,1445247996767,19914501691,1409514821512,97664930414,1641694997645,754856639275,
 1548355609548,1805366190688,824429277489,3645225082777,3626102403865,329164065483,4091011520294,
 6883674461002,6521791609750,3249773160248,1369320033705,5162178044001,5838821144387,
 1211312568341,10700811920606,31559627409074,62487591760250,103901369251654,155195897399440,
 214886125605514,280241697914936,348129043126342,414375885162462,475343748200064,527063724765750,
 566618377395182,592012229302308,601920792678700,596747524768532,577513150183210,545962702370578,
 504935881757470,457154726341170,405269364044192,352200935058422,300292707667140,251119882493886,
 206068251536962,166176596825022,131716527294208,102503003011634,78349252641722,58967082790766],
 [43743651451336,31901602394662,22802959025190,16004245931954,11107083036294,7667011251116,
 5247761455748,3514588467080,2263172302436,1380917845176,792755102124,429695895596,223953413846,
 116373306240,63102337228,36615120026,22289728416,13560937536,7877239380,4235740116,2066461036,
 900079222,344296924,114061832,33581308,11000448,6134338,4871888,3743648,2529434,1515468,824008,
 415832,198768,91612,41290,18350,8050,3468,1456,586,222,78,24,4]]
private def pvm_c2_2 : List ℤ := pzigCatZ 257
 [
 [26802099597,32526038267,34437633059,31704466125,690541407,2305648827,5466400835,18559706753,
 11718455953,6412036569,20922331754,20973902186,18902679930,6403219112,2605836423,28579809998,
 14022619872,14834173873,12269067049,21044024751,28161001319,10346300013,19926006235,11024206424,
 28334697083,19941978282,38183403002,36677928628,3356236074,26173080131,20624154465,1713636203,
 27934306867,16985764424,1196223005,4642496721,3501707712,3918296142,24797928355,5608382332,
 5131102004,4120749836,3400905671,13274706934,17782800723,2110878672,31505970912,9440153829,
 7760457875,12362401491,13788406405,11556510569,28834239495,16166871947,3111916497,11115450935,
 87981426,29759346834,1189487790,22079700751,13049008076,29411418168,6462944964,12926228485],
 [45043433332,24571613898,27637354288,3433326735,6496410885,3774237418,7107501666,1680559191,
 22695409660,13712782066,6406225778,4240247615,29053760743,8205019915,5100379421,25161089296,
 7763321510,22893868677,2476002048,15846177578,30050124174,30701417028,4253947035,9396284739,
 2693362859,9739778379,5296655651,1482970293,16726471727,3080212659,20116157210,7336390704,
 15323659829,18138854203,11333417562,4054668543,3997492884,14382196395,9302027053,6164850358,
 71833351835,46838681112,156168077767,208735848270,332979182935,437799198712,630052251427,
 707689907094,758280592825,727174570608,363828594951,32984245890,420477529732,659222521687,
 599161091462,185668351195,331224188855,635139196132,507010234747,26676079319,572169464406,
 613822933801,62888896932,599809655022],
 [620604283605,110768290609,660576898982,497731996383,458006629553,716545465022,9133337010,
 749715531703,369487557366,654003516106,599022384929,485881307605,746780729190,336515435896,
 888842058631,350864957721,895193651322,353123581838,976793590421,593586038911,911876456790,
 891128342210,624044106623,1274795981301,74303220800,1219448869158,591476039302,1109588748851,
 1383184684385,151429590554,1593220494912,1239746833632,818684160771,2261375340859,1576851408783,
 699593179850,2791755366460,2704600115064,347021897476,2683710931993,4658203924751,4208114876847,
 1330306814999,2548612518422,5911207924958,7457364080692,6263041683428,2518108023830,
 2758731752591,8272694959365,12137333772523,11976953342745,5612481194983,8894935376642,
 33330544207176,68717720312018,114884038821806,170704610778828,234192570505878,302282381404160,
 371078700630198,436545819230980,494908447785472,542742734354774],
 [577280962078974,596881616664114,601164377769928,590756324671870,567053430757714,532159179999526,
 488759359153364,439773192260360,387958885307418,335710866034600,285045423260864,237603843120284,
 194584078586278,156671107062680,124066122216498,96618519554964,73979173861352,55700490404912,
 41273621024808,30141139862322,21721905098636,15454594735138,10842486369818,7480115017364,
 5055429773102,3334384328310,2139931274614,1334506504040,809221703164,478487044684,277206004628,
 158293647298,89618194620,50506707460,28357115976,15816275410,8714690022,4711749720,2484004908,
 1270823666,629324238,301738498,140598914,64186580,29084652,13304464,6248488,3044010,1536280,
 794128,413986,214670,109656,54868,26818,12794,5960,2700,1188,508,206,78,24,6]]
private def pvm_c2_3 : List ℤ := pzigCatZ 239
 [
 [2992803495,17428799737,7504801655,19417251973,22510381555,37616751287,28125005435,18890993853,
 16828862693,3596434292,2917109527,10712209865,7042598627,12638704111,39295649373,15534138202,
 2827841300,27213784482,3875475412,789670607,15406165078,20158464942,709350918,30454315538,
 3641483890,13414653690,16209592739,29962016643,13714663613,14525822380,30944864991,30439251845,
 23076544619,7889292519,4940015238,29921786542,44912861792,1375136449,7556957444,9921707700,
 26919958947,13127385815,3904623149,10572215797,3854178461,7999897872,3915799840,5167867951,
 11869647371,19107286343,22826120706,436263678,1378452841,18929047025,17431868258,1614991209,
 13455038165,19191428228,24579756456,17334970291,8233190591,13348226996,1297851169,10906019901],
 [46760548681,17865075553,1488960332,10327569457,8907572493,13713770805,10047675376,16318121924,
 7224416843,1192600890,1820653509,2230050337,22325936646,25503074458,15855665538,25172823410,
 23969729986,2572339598,1450447616,17169928081,3213695486,33648312390,20671947234,35793634998,
 79959026239,105562569312,181902557407,266695482582,353205649465,469902420148,604010567971,
 638233201500,643546467049,585017031186,341789578357,57095645726,289078315220,491680925917,
 575180924194,393056445379,4864285135,369029546854,557391206899,407211003730,3323993233,
 409221290597,537846004226,263813659957,233742164501,524202298824,380955658889,108838044981,
 533509298546,421448746275,157778200209,519691354342,378922258287,248119240937,584823742402,
 230449198519,507916881125,492402103968,114989317984,622635058285],
 [244883549356,530163259328,457512550799,274871050573,667521671718,40141375110,630713054983,
 147574209652,670871680612,360621170495,574113325065,431495468572,536762605270,479432129129,
 535881171307,595503620546,537842595556,582989973115,647001417009,424415481778,732407629444,
 399532680955,916517836959,171280538990,957977375814,212400180570,897672264723,656269539815,
 689068400218,1029839455900,208143538085,1168962591611,572653515679,761157346706,1139640711142,
 24281925039,1270771692311,925162215263,575187847904,1437951655328,725536205526,901884980523,
 1827754390731,956723971995,972591513898,2083467387794,1358592606062,612122769207,2371743086379,
 2561171568635,827475326619,1727933603714,3358596876436,3034342895086,907924442948,2062494222201,
 4522055978267,5205157823797,3624702288165,329944055399,3551643706258,6831333122234,8408975510118,
 7426605634256],
 [3640249684708,2379100961413,9421396560331,15838961350177,19536358214131,18021563736879,
 8775291732845,10261961467196,40400339952954,82085355002840,134747155914564,196625001027252,
 264795258668116,335503910083802,404637919301974,468126289803698,522241948563022,563898665103716,
 590963032399098,602472136661504,598646236754910,580707820736820,550618892695104,510835376164180,
 464096064843026,413212493241236,360844866281426,309297135394508,260383270969806,215390444453948,
 175121504886694,139974556620108,110023371551200,85084955775948,64779161874390,48589426640380,
 35926821179290,26191133254098,18819631320724,13317352256046,9268779057034,6335654979452,
 4247429695202,2789771880350,1794236283984,1130004432608,697359424952,422210871060,251180365294,
 147089737758,84923489742,48401968590,27250097966,15153707434,8317763438,4501047902,2397880774,
 1255932964,646096716,326316876,161862688,78954168,37959834,18048474],
 [8522090,4014838,1895612,900102,430546,207374,100344,48590,23450,11232,5316,2474,1126,496,208,82,
 28,6]]
private def pvm_c2_4 : List ℤ := pzigCatZ 222
 [
 [9238074364,5267064383,3486164025,5797371979,13850909685,585776007,6718451375,9698590283,
 31321374851,321269852,45285830271,27946133027,16934970715,16533729749,22362784605,4758852986,
 17344794485,15922423668,527909201,20941882825,31543638907,8148684093,15878823285,7959476150,
 11859355988,7756869673,11323447046,14566909184,11766676376,8298241291,2069769841,44532722088,
 25711588048,349259742,12172050544,3913095747,17175756265,7158926645,20869597546,21893871273,
 14177947593,38647471833,24988570647,22652484861,8270064929,10280947116,20749671208,26677244452,
 17660875384,5539927850,7298187348,20646694714,34033008261,29132547699,13432872180,1798064852,
 3699872657,7798939873,1080921157,5974593152,20179430271,9627815073,14471484948,7692881760],
 [3275603533,18923596929,10404969459,16999957056,14509312196,12039653469,18777721965,41765469896,
 44094228881,111528018724,151480544771,217137857266,331593668937,411899606810,525934983727,
 560688399674,626977602467,543282282844,434077572253,216467156282,66274733166,332766412997,
 484644317852,481837446065,305413391178,4922434259,326539552409,511314772646,367740740847,
 123744216778,299167572846,479858596595,357494455756,10227475403,347808664191,503123865470,
 187543738717,234366902279,465046213048,296700020847,116871970125,460721220136,353129716553,
 119763289427,459445744730,337941594865,169393639181,473700888518,250643032705,275701517863,
 523692592192,93192482411,399834935663,396225151260,192092481538,555097666161,182630013816,
 411243782020,419502684373,210802851413,543182408510,11871113573,587958870053,262912945834],
 [439660529054,423555503093,259339076971,509317371272,149682000522,604873536655,37197387329,
 630356360124,122527278351,605395592649,182989410072,538743482578,249536490613,634104810621,
 197865301026,635323377446,242497795845,657902005167,236397335550,699170537736,90083703493,
 685437631495,41800765741,763818605560,279966528238,744051839439,505598365079,607972477504,
 706307661760,323360905505,825482911809,50584994855,864256217692,535653939818,656540667119,
 967640181159,107821107420,1003389802670,458579078964,729531193317,996802806603,17192144985,
 1036334727628,863877770842,408822802509,1249959769527,594059113251,780786871102,1266750215966,
 343514445490,1008189931253,1435178420311,456656626245,1091032892046,1725895611282,732318477342,
 1051701765585,2037070848007,1384158347181,386896662540,1971556710170,2222787347430,852486700008,
 1331127366583],
 [2879858647451,2711978976827,871790377147,1599925596906,3408882399114,3655590433370,
 2119241554286,681876372379,3635646531289,5485634151873,5405948881923,3305555711991,273578849462,
 4414814985142,8001831801778,9863780282146,9038092224308,5097553576250,1654930660985,
 10194461167729,18867685879037,25468948313551,27359512673645,21751416255607,6151405359863,
 21187305496018,60956615302426,112658942116030,174591171500640,243917103093002,316863998867238,
 389080491111452,456118211868940,513925618780270,559239932569320,589825601659086,604573981028962,
 603501179299386,587663421796300,558989071069552,520031235342704,473670446688764,422818768132138,
 370175920212354,318065525623992,268351145998774,222413304919718,181165557080462,145094651260162,
 114317987689000,88655074043826,67708250104514,50944856394378,37771683645804,27594291910864,
 19857737536750,14069481693340,9808188085160,6723166617310,4528725461410,2996431847206,
 1946972690304,1242357736766,778703517482],
 [479661206776,290537248706,173173779192,101646227080,58792065946,33527271386,18857598368,
 10462932682,5726471554,3091075012,1645145488,863077818,446227272,227351992,114170060,56534782,
 27626942,13338304,6371828,3017120,1418848,663970,309742,144232,67092,31170,14444,6664,3054,1380,
 608,258,102,36,10]]
private def pvm_c2_5 : List ℤ := pzigCatZ 205
 [
 [6655496400,10566908576,5669897879,9738548776,12841052657,17886095656,15981212285,13145326413,
 3975679577,14812569304,25311982907,309047039,2049274133,6747694515,18022708897,10122335971,
 26233512579,37059871321,7792683509,19549297265,29857034547,17514486005,18731245063,2832203283,
 5595456988,721925156,13793834000,25481597313,26955187835,21210210717,17132585198,27176469051,
 23045786755,9342166556,12789253496,7838207912,2055102512,5195439782,4663231781,760827610,
 3590751856,31265165948,28857843698,11340353198,17585757036,9523267389,8550113727,22223427614,
 1502235583,8684195875,9315947392,3919533795,27776045997,43960415253,36636432197,10152710978,
 32844679733,27315415756,77332363803,163458395804,175386270923,303807361758,369896234553,
 465828833828],
 [533794511605,567470784474,573456662145,440030347228,250536774213,40993823242,194751180358,
 418832983393,465864270900,378959529193,161175706466,144215093626,399368466985,438225027482,
 281177429573,20065496627,325037361526,446370863785,278087398644,49511586434,356340684705,
 438054901148,163981094301,212443017905,433946473492,291375208611,68447387215,378835798698,
 385621930377,12107128763,353370359730,406754376709,19898982106,337343278684,369531822731,
 16271839583,411139328420,365959059063,67654776453,372476741746,271847898035,212315249755,
 484833289914,75865783345,368431023189,401234874668,86447458828,431375408215,201892296300,
 355065726736,373230061417,148265593001,510541107072,107288813723,439578040159,357366514634,
 275844263116,445292842501,91101100971,483141673926,66481458441,513152799405,215133262988,
 451298028990],
 [379357182053,336856543617,474610708794,242294140696,458883706651,130037919667,498748003660,
 87796330772,551644740533,45771687749,606020928702,9179656764,617483449861,5833691018,
 581465717376,6280904313,571396900641,48315541179,590911670910,150417471346,612376977907,
 271732134217,597467712584,376932254202,546837485101,489429433087,422413063144,579543449116,
 272081161511,733655064789,63342031211,699989958796,331204345938,634065025357,637866633633,
 393875487888,852578150856,25386730252,805204520577,416287403049,590568699990,792944352862,
 91792946205,895501326325,519710607085,602455049126,986199602734,74738047282,945935684095,
 739436383685,407287526680,1045186433244,420521587600,727657363183,1112541234687,290521293467,
 884874696528,1127359812614,107393243336,1106378734435,1181764058153,1219102033,1232023149410,
 1295550204218],
 [124566370454,1238386439311,1609548893939,618949058721,989689223340,1902816789646,1296201542204,
 430416731595,1949647503157,2096848983103,755248720551,1160102858256,2413546690952,2209528948084,
 594843830684,1576093394557,3079335385945,3003532411975,1293699968977,1224831896086,3343732499498,
 4097072466332,3126366871246,715151232154,2356990838495,5039151504521,6315794991635,5554243282935,
 2742504728411,1508284900096,6159840593480,9991931174002,11802765036612,10596886707340,
 5825043546298,2349062830773,12870032604729,23798360446383,32505188721847,35981853260407,
 31198922972089,15494700400077,13016297276578,55065607718310,109978280209560,175631451755794,
 248645963470682,324758853979638,399287294496908,467603588557636,525570520849828,569906575929006,
 598452845496226,610311175872376,605833168026018,586465668550878,554488924963086,512702879740966,
 464117081150358,411683988404162,358094566007638,305638623674864,256124162926260,210848138115840],
 [170611321335500,135769318714718,106309733297420,81943395539648,62197143664990,46497530470906,
 34238531805320,24830587656386,17731893511582,12465079365574,8623204645120,5868738327418,
 3928407852514,2585923391800,1673862580198,1065506142948,667111061070,410923705018,249110101998,
 148680689256,87402533998,50625301936,28902611722,16268950488,9030932266,4944511646,2670372876,
 1422648794,747670200,387632452,198268640,100061326,49837020,24505202,11901206,5712436,2711954,
 1274564,593598,274232,125794,57338,25982,11704,5238,2322,1010,428,174,64,20,4]]
private def pvm_c2_6 : List ℤ := pzigCatZ 189
 [
 [10543617567,21447002510,9639517509,13161623530,2765120006,12204500260,19165014085,4046663438,
 16580199080,5511089074,11137584929,15644740267,7587819512,86074391,15833096491,2235057174,
 3543128388,19843102093,4192085964,9339746931,10390572314,12588756031,11480762575,24710835989,
 18704748671,5123727495,30874469603,22643102825,9106980509,17952939851,46297964671,24216131491,
 11460154288,9913182706,3856324856,13724933603,12965881133,8498801530,15060751255,21068209369,
 8474969103,12855431179,41288385969,37497968486,62165575389,105147985566,148422547529,
 248058006568,333366726461,402030989728,506050228849,566737955740,517458668369,480688803762,
 312918546559,140969735792,144128875902,338990879675,431222500320,401246876563,249112845974,
 56673718660,288364138721,401174400818],
 [365676508343,97186458524,183560126058,438227325795,326174487696,111537692985,230199559559,
 399063106220,299525402257,1533642466,354624267376,361103750745,155003971474,203834254508,
 411520763487,237499723796,155727826564,399767013887,286983555750,68618550400,370709228689,
 262710629042,124347316516,402351550831,279236120964,112036826934,399090315487,225896146512,
 209768428424,378505348147,74537971374,319130981632,357071512635,45954574755,402404276934,
 269144564157,198411241297,403206583694,42950458289,347090354771,273030032394,225189450182,
 422668467315,341978841,429733079780,268621033693,316057646307,373199383122,63554231868,
 423332649365,115064784268,404614808868,255716444097,363253416739,349813344498,213578132780,
 460668806773,40550141635,509097000274,91609822047,443266885633,226422674030,408651487648,
 269575758823],
 [346902109349,343313197662,342734825188,379732056743,287010922015,455376314822,252255779588,
 472513209107,174769700347,503701350254,157547258944,489049357935,162535104891,474869835676,
 189787052006,497934240495,280661379659,484016568954,360276098916,440877544055,387708047919,
 430571941776,456908660268,357063156951,508215345455,259031840178,582662697740,85303168339,
 619112791247,129952075595,588738486640,333714872630,511532680725,529810335093,358604888854,
 686062728168,115248482109,751902826303,208380341547,653687046298,526470666028,374639290025,
 731300919723,40171365875,715136723656,437702529336,532585389979,828662665889,16723639308,
 839938188120,477234909108,569725767407,857752882829,1890461563,877207951174,679833651210,
 332669332705,939921609153,418647100857,635285316726,978184971050,160815037940,889247141247,
 919312237141],
 [147210558648,1098728711564,855564037438,317494553601,1172840316571,844300116287,323645871136,
 1187749637040,901272720926,313146246009,1341497854211,1175906567563,119807372732,1407526138978,
 1507028074834,285369863408,1241112152545,1822761816169,999621311413,611930659120,1843442694010,
 1802891108824,458605626988,1331102725453,2360667276585,1882518338359,134566853019,1808417688896,
 2751553966264,2124200722208,255388324460,1894305217167,3262534283319,3162120478951,1549516395605,
 956884477004,3315040927736,4491317144834,3904027243512,1655891722748,1543194586301,4668883044817,
 6707539334161,6898798449247,4895858126939,878817141589,4396165668500,9674328198686,
 13436674603126,14241342704488,11073922516372,3628856393670,7505453316439,20762527451969,
 33637230394501,42890344531053,44937840994361,36381541614699,14575516728391,21897058356418,
 72930527270860,136824585135712,210423221565500,289429956163736],
 [368855353023184,443544438331414,508718761172720,560458128416356,596052287470942,614177468272168,
 614889646218116,599461919594564,570115795622318,529701567030912,481375243582120,428306096605362,
 373435964073614,319301656686466,267924649925578,220766231223912,178740562744750,142273107134126,
 111388619045214,85812286146312,65069656923858,48574933485948,35701823137894,25835303413504,
 18405662405278,12907844909402,8909670513598,6052278959900,4045585214816,2660870323254,
 1722044714388,1096648482350,687292825406,423974045420,257484045630,153985293988,90706530238,
 52643335340,30109693984,16975906062,9436666292,5173047892,2796968396,1491769020,784946484,
 407521066,208775392,105555678,52677204,25952900,12626322,6067752,2881380,1352648,628052,288580,
 131292,59172,26426,11692,5118,2210,936,386],
 [150,54,16,2]]
private def pvm_c2_7 : List ℤ := pzigCatZ 174
 [
 [27721850639,7491743416,4313792661,11610854076,3769468314,9109542999,4622187474,11870279474,
 13824387930,3518065056,8190373333,22852298573,26877931810,6620241814,3229454386,3327974683,
 2452136417,6095340230,12543278299,2133871719,2249236561,3808965661,517190618,380933994,
 9276998753,19379565151,1680854872,20147225320,14318090123,3536011417,16416646867,30721513444,
 75104101067,87643503200,203241046951,241625399734,328184749969,411755959762,549302044447,
 515133072420,538954632085,386066546012,230893765765,5210866929,228658880418,397383089587,
 422992805724,308073923655,72081942536,186328815172,394079936479,371736584820,196337351923,
 131683047809,307177557340,379777830219,201202344550,139507573922,362287947115,335149635652,
 79062236945,249021311441,384897630168,227271208177],
 [125691524133,374649877158,244274389191,23054618079,351495807108,352403212821,41058020378,
 309503393520,303674047019,7565011948,335199680484,317285958409,7240391523,359656383486,
 328547957829,84204904111,329129676706,242926622327,185258006953,319961773268,137813794695,
 299826979493,355811859212,50772739774,353566339167,271222032720,185434905644,374746193231,
 70302903666,331214540256,241592913185,179885639061,348792549696,34687200599,369256152821,
 253128880690,242686976248,405050687923,40752841745,403489550456,166331013157,318882724021,
 293760383740,197565910398,372121803299,76944213905,408628166132,70206690917,410609824645,
 214435373276,331770736766,350716239355,211587700051,437717627240,105069947148,442288991905,
 1460069214,444439868780,51142493845,415304482283,110184791650,379035571142,228935204919,
 418246393021],
 [275991804366,394854067014,329536063743,361342366833,346895497150,294365629418,387846484403,
 297425033773,363132661944,293686294194,340835317767,298407626071,352053666792,355880470576,
 327819701165,378730496525,344886705880,449709333610,298724007131,472834161739,265346307968,
 526644623876,158877931067,525501564787,64103107132,548190506350,95534238842,503604521995,
 224161028559,460276315516,357194380586,407881056325,528262780097,257011959248,639287887922,
 44459093853,652626748811,172156311941,596783830860,412493962926,406159408307,569425877405,
 158973102202,664730430202,177468953054,603907175531,520715374961,347277724320,739502281122,
 44536871462,744815492801,461249118755,497518239616,745949798768,65961562193,785503084845,
 424974966687,510764020094,779038624002,36868343098,773128992199,631342890311,301254384324,
 865879443176],
 [321372552184,699487844749,925982657813,36421863095,908152608180,769538144388,275845819145,
 986001293987,548938012003,522937872160,1040080263640,445433443994,640542571493,1090423385743,
 410487769325,751365465746,1221541132458,476724045180,785416571511,1311502518823,553613490571,
 773754174962,1403776990110,735989373794,640987335433,1530286751427,1170867035825,169161790128,
 1441935909746,1635366528692,542110572256,1059677889081,1962913748627,1441969301939,177183035550,
 1748563363552,2155632976536,1102580234358,728787624769,2186006606975,2381554189921,1178807726563,
 781210685254,2443614878412,2885131927634,1791260621012,364429512649,2547256585411,3684943229307,
 3195607655065,1235007081123,1425467881886,3757964766064,4863005190122,4242085708624,
 1929215222008,1504014977077,5069628517943,7610983005177,8130572902099,6098545238365,
 1641301088481,4434499573046,10763785491450],
 [15648989858156,17363839864866,14521587741962,6472256356400,6351987192267,22251347531923,
 38318013935903,50759284106129,55427508862479,48452005892621,26858368340595,10922674778520,
 64729633933858,132575747216724,210805562408992,294486575793440,377978447325978,455587220948348,
 522196807044998,573781097872154,607732826597602,622987161914614,619955717253726,600311804702774,
 566678809478786,522273706809336,470551547421954,414887601827110,358323386933374,303391579422976,
 252023447313308,205532025569222,164656242732514,129646687657392,100373000199668,76435381725958,
 57267231437334,42221045778344,30634348807004,21875901483590,15374593643706,10634419860046,
 7239105829286,4849624621690,3197290499956,2074515561408,1324753396754,832672614058,515211065084,
 313856232532,188271330372,111231116182,64735535054,37121139664,20977284900,11684531922,
 6416345824,3474190110,1855145698,977068404,507637780,260208622,131608626,65690102],
 [32361672,15737908,7556620,3583140,1678264,776660,355222,160616,71808,31750,13878,5990,2548,1064,
 430,162,54,12,2]]
private def pvm_c2_8 : List ℤ := pzigCatZ 160
 [
 [24775477663,13244497707,3378337013,12156333341,4689944441,3459303079,19963537478,8333825869,
 7759173220,3180425212,18331728945,3268502218,12562340220,22001911370,11109922166,11270219227,
 11202524323,2583922122,364657701,17462554110,23767886583,54739260268,75719305017,130242869896,
 211721116853,319820651432,417562312261,473517137684,534355539607,522719264730,401664967553,
 204007337222,27791347724,287557307969,411812506852,385583058163,221958693650,15858458938,
 282383564577,408616545702,288319182485,20817254744,230635798170,398784044327,251702741344,
 23777554200,304983357747,348647541492,157743255493,209055981341,331241023822,285702515961,
 72829683291,306719462648,310538346285,36968843253,337873859426,339643920801,30772861952,
 273998315522,312888937373,19438436154,304588765276,294102296079],
 [73927740901,316158586916,295503255985,102713117057,363518745072,223565522419,184613642407,
 347813877234,65396313969,274648613779,266124536490,62977676638,368207192199,183672548522,
 260136857898,336941346049,22170675746,347319682746,221497910605,161848196857,340818267656,
 15771321959,322148111699,198499535466,258471380684,303012738607,71925886461,377808992450,
 124089704855,320983610775,289636866376,157637178896,397434639509,35753825779,318586002256,
 171894794483,302917309763,263196446012,233826950412,330122966901,124254939311,401406115038,
 19159071196,394791715837,140678690656,372769939980,257712027867,296658161979,335472066654,
 204076146246,373156873179,124952136845,378980811968,49036790904,400928147181,2301462095,
 413986681064,55854578691,438306066187,105794232442,441008896836,158922173489,424937115429,
 199320375486],
 [379286839848,250179993301,358536012319,268934323982,350576839478,265755390075,360479914281,
 250555854016,399319194886,192519709627,387896230109,192405377230,406434535078,208432582135,
 473337368983,155720667194,478512492170,129001137633,497487270107,70055541058,489427405606,
 19762049937,515754617065,109198641083,469710150224,212687518434,424122494735,330261041721,
 353350798382,453674445966,225643370973,515803708301,113225078484,583750730470,62967163548,
 560025177469,207414309285,521003876184,391996235950,374725564613,516398897241,190900846028,
 623215405758,110869537002,557656495855,368407399703,389487047342,556004526602,151256038463,
 669101423055,175220441857,616856589830,497323370006,381827431047,705048491241,22350564992,
 737926030268,410818598944,477802960809,680158375303,59341197980,714209551402,404539575440,
 455196054833],
 [727323136371,34213159425,737287831242,561453116392,375757883683,867867084479,246185046183,
 716572040484,786962894204,133990663415,891917012329,553078618579,456256439290,921360512638,
 301953864676,685907564911,932414742289,167082395733,771408162782,850617943018,41244404731,
 949785154209,859946535865,189094437000,1102218979480,889277341696,261291259687,1172146409005,
 910586034281,267924836038,1213617658808,1026713347604,116145146143,1173153124599,1190436367185,
 124210767877,1127967862282,1477089393318,561712158578,915304344777,1738471499325,1188202042153,
 343678539238,1662892448034,1736380031108,494252582834,1155488285219,2035643881073,1533379562571,
 26192281930,1638361903726,2268159476970,1478996262706,305140282155,2040935861097,2677344537105,
 1782882525035,193567405212,2186678410916,3123649171938,2494790050202,572825199496,1775575037041,
 3514828362923],
 [3870139296461,2606945571363,105960334045,2762277344688,4926163416624,5483565482764,
 4028892662806,814758085850,3305311073395,7113708697121,9350513058057,9032638280851,5721396623395,
 288565149898,7896666257442,15293702449004,20265327864644,20677965166636,15049597884464,
 3062746688086,14116311097813,33797854488877,52027985032905,64107498019593,65288400247919,
 51537425649797,20239539798017,29284564163990,95547075269786,174996105214728,262434507618806,
 351672733916048,436293278629770,510395413354190,569209472184178,609508877895080,629792008421318,
 630244522157296,612520652615572,579398319053772,534368962234744,481220607967930,423663520658704,
 365033811930454,308093848987820,254931973697820,206950470816368,164921711487546,129088560984734,
 99285914251972,75064236671406,55801588621496,40796339969264,29337641370190,20754246420700,
 14444433565178,9890781749380,6663733731134,4417551281708,2881678300928,1849854785422,
 1168673419430,726699320568,444808010292],
 [268042627934,159041952172,92931711024,53484960900,30324095248,16939701086,9325192518,5059581984,
 2706102534,1426959582,741957302,380456696,192418898,95998016,47250306,22947300,10997708,5202108,
 2429008,1119752,509720,229156,101754,44626,19326,8256,3472,1430,570,218,74,22,6]]
private def pvm_c2_9 : List ℤ := pzigCatZ 147
 [
 [4801280173,21280925781,5859236047,21808312613,2945846155,3949934620,22459454849,10450191567,
 246077777,1931630331,9221989305,19835312252,30005053435,81108620954,119284189811,194446510604,
 319674041715,410007208358,502910566179,564085235674,464145573605,312673609438,64708913087,
 195657586355,385346173838,426726554485,250509533724,51536356064,295401105875,381564777252,
 241697672871,43071215655,315751467782,347264580685,149810734780,162291936736,374756010989,
 247007333520,89104455890,328762411963,301689865966,31574696129,283746038763,298466500374,
 1509120865,313734202275,312968171118,35227255899,300050710441,315093995556,19688496298,
 302771770245,240120683806,106690968414,363602985975,142444398540,214607931182,345088227867,
 70136792826,275873101058,314581329049,74614773335,309860783372,185701078629],
 [243782901513,270130476226,8433985432,339623542833,182991609906,220323264546,356428229711,
 31756035591,344920808738,183221419185,205201925975,309886665170,26389824322,338452353651,
 104659065246,256648395760,256330373613,189234605509,305287218170,13667676660,339051745777,
 164661467748,295086991768,300222556653,181604637735,346116900954,15534278516,350756405715,
 107650322136,304383044796,189532214945,217076031755,292075931774,174621919144,330912985023,
 76375626963,380618838450,15640375123,368202043539,155015140266,365011871568,233151761355,
 291603686441,315276978878,242125046272,327012974675,168450583553,319695505524,64787701646,
 394614521719,82718377515,365341932728,13654506802,406633851779,14367017258,419857396536,
 53133984545,409333769781,123487845764,428644986660,144651313103,407464426051,172017165516,
 399908158296],
 [166528596875,383138913097,152264050798,370335071784,141807981685,380982676393,119941748522,
 393467835024,113093557931,436366164505,80499783496,467239277538,39688511195,481948064967,
 8967534273,466645261636,38232849770,459632442021,84158458597,440094819434,133515525066,
 430781746289,224571963353,388133644784,336012530248,280459808041,382627586413,212620245558,
 457671955034,116080552471,534231104689,43662675523,527609270238,177337874946,496766702443,
 321928575617,397442858172,417154858862,291996809249,526065509109,94592101622,533653765054,
 85685540532,508510688991,291731357159,400697301548,483258750870,189686318761,579887931015,
 53672936205,603207839580,359122022032,441414717337,563599145961,199293138518,676963255220,
 131763844032,599328362949,401285662239,426495085034,651653450150,55524237341,680077630099,
 348125405061],
 [465477607560,633963177076,76327648117,702574559609,383943308023,471670285560,710151968918,
 14699258325,736269392439,459529615025,470262625182,806271716188,80417749978,761796574459,
 621356915953,318502222280,861105183484,335185566320,600697833745,812480776255,55813238763,
 772024450072,699881536222,201657133493,900192630771,571748111721,444385788618,997701027330,
 428584650394,652011264673,1030882112783,268953723639,794433930404,981690732088,76363054408,
 962601355641,1045518284435,78514974637,979032074642,1092901647022,147375559420,967523366203,
 1195285296747,289131474307,946416587256,1369194197418,544290531350,827227755115,1514272114739,
 864706002245,596758557864,1625216369850,1336359150016,56551230161,1450710108945,1760428757229,
 745633294325,849107953402,1868744801680,1569341598278,123458116456,1499456525449,2182521631407,
 1414756904493],
 [351465493340,1986558784694,2424131557726,1350912736396,610518170823,2312788995353,2778497344685,
 1733230591651,296191826570,2296970240658,3277767089410,2717632417140,786340277494,1727090914969,
 3740238402851,4328705447739,3117165633693,443629794001,2765022551326,5334462473010,6247815315248,
 4970143554600,1618231571132,3033333548713,7694800412207,10839517946261,11093115967335,
 7666721208547,718141927917,8489738910790,17722105525218,24201430814062,25248785327052,
 18994074949652,4994592821262,15380756662619,38902050426409,60804798161895,75460936467401,
 77287290588063,61723268951717,26083697556957,29885504553170,103855677918134,191185276785950,
 285541949577630,379745982132822,466678873895324,540110305144802,595331337420928,629528837799588,
 641884750455910,633426081965632,606682565816294,565226602780276,513173890185456,454714664987602,
 393727909599028,333508602326658,276615789420850,224830792950270,179202597938740,140151963808426,
 107606168450248],
 [81140718816994,60110825161558,43762200814770,31316636434792,22032221306614,15240936912570,
 10367824569918,6936361851374,4564422734964,2954546798022,1881432551310,1178754820088,
 726679502002,440857411198,263235245064,154717251566,89524761420,51005885480,28617674104,
 15814301602,8608585586,4616823164,2439756358,1270579348,652180184,329989590,164609246,80962254,
 39267866,18783204,8861984,4124520,1893858,858030,383608,169252,73692,31652,13404,5592,2292,914,
 348,122,36,8]]
private def phbv_g3 : List ℤ := pzigCatZ 0
 [
 [152688411993894,215602632151712,263652302133424,303970689977518,339325406867618,371138108365768,
 400254639562630,427226965085088,452439067736416,476170948679386,498634306552978,519993858473242,
 540380792424062,559901634668212,578644309415892,596682406885188,614078267832790,630885262748874,
 647149508841320,662911185652888,678205558428900,693063784924330,707513559200624,721579630976936,
 735284228756156,748647407677722,761687337859564,774420545231240,786862114098924,799025858629860,
 810924468900026,822569635975402,833972159596832,845142041341070,856088565585950,866820370178762,
 877345508366762,887671503277046,897805396014588,907753788270444,917522880188326,927118504120052,
 936546154803474,945811016416524,954917986894436,963871699841756,972676544324198,981336682786326,
 989856067307932,998238454383968,1006487418389046,1014606363867112,1022598536769516,
 1030467034749608,1038214816609160,1045844710980674,1053359424319966,1060761548275000,
 1068053566489610,1075237860894304,1082316717530774,1089292331951774,1096166814233702,
 1102942193635386],
 [1109620422933234,1116203382459846,1122692883870618,1129090673660428,1135398436450474,
 1141617798063364,1147750328403014,1153797544154256,1159760911315866,1165641847579408,
 1171441724565266,1177161869926224,1182803569328094,1188368068316100,1193856574074978,
 1199270257090146,1204610252716650,1209877662662108,1215073556389364,1220198972444104,
 1225254919712322,1230242378612104,1235162302223910,1240015617363192,1244803225598924,
 1249526004221334,1254184807161940,1258780465868710,1263313790139032,1267785568912934,
 1272196571028886,1276547545944296,1280839224422722,1285072319189668,1289247525558692,
 1293365522029468,1297426970859332,1301432518609730,1305382796668918,1309278421752142,
 1313119996380520,1316908109339684,1320643336119252,1324326239334076,1327957369128216,
 1331537263562478,1335066448986322,1338545440394946,1341974741772202,1345354846420088,
 1348686237275416,1351969387214274,1355204759344854,1358392807289186,1361533975454292,
 1364628699293226,1367677405556490,1370680512534214,1373638430289558,1376551560883690,
 1379420298592710,1382245030116898,1385026134782580,1387763984736960],
 [1390458945136182,1393111374326938,1395721624021880,1398290039469080,1400816959615804,
 1403302717266808,1405747639237402,1408152046501480,1410516254334702,1412840572453056,
 1415125305146936,1417370751410956,1419577205069626,1421744954899078,1423874284744964,
 1425965473636712,1428018795898226,1430034521255196,1432012914939152,1433954237788334,
 1435858746345560,1437726692953130,1439558325844944,1441353889235872,1443113623408508,
 1444837764797400,1446526546070820,1448180196210194,1449798940587234,1451383001038890,
 1452932595940166,1454447940274886,1455929245704476,1457376720634832,1458790570281328,
 1460170996732036,1461518199009208,1462832373129082,1464113712160066,1465362406279340,
 1466578642827954,1467762606364430,1468914478716960,1470034439034196,1471122663834720,
 1472179327055210,1473204600097338,1474198651873450,1475161648851078,1476093755096272,
 1476995132315850,1477865939898544,1478706334955102,1479516472357378,1480296504776414,
 1481046582719590,1481766854566804,1482457466605776,1483118563066446,1483750286154536,
 1484352776084258,1484926171110224,1485470607558568,1485986219857290],
 [1486473140565866,1486931500404126,1487361428280418,1487763051319100,1488136494887344,
 1488481882621302,1488799336451616,1489088976628330,1489350921745186,1489585288763324,
 1489792193034424,1489971748323272,1490124066829790,1490249259210526,1490347434599622,
 1490418700629284,1490463163449742,1490480927748736,1490472096770518,1490436772334406,
 1490375054852866,1490287043349174,1490172835474626,1490032527525334,1489866214458614,
 1489673989908956,1489455946203606,1489212174377766,1488942764189392,1488647804133646,
 1488327381456972,1487981582170802,1487610491064940,1487214191720572,1486792766522962,
 1486346296673800,1485874862203236,1485378541981600,1484857413730782,1484311554035338,
 1483741038353278,1483145941026544,1482526335291222,1481882293287442,1481213886069014,
 1480521183612766,1479804254827626,1479063167563418,1478297988619404,1477508783752550,
 1476695617685546,1475858554114558,1474997655716730,1474112984157448,1473204600097338,
 1472272563199038,1471316932133712,1470337764587346,1469335117266782,1468309045905546,
 1467259605269422,1466186849161806,1465090830428838,1463971600964294],
 [1462829211714264,1461663712681608,1460475152930186,1459263580588866,1458029042855326,
 1456771585999622,1455491255367552,1454188095383800,1452862149554862,1451513460471762,
 1450142069812552,1448748018344604,1447331345926674,1445892091510780,1444430293143830,
 1442945987969076,1441439212227322,1439910001257942,1438358389499676,1436784410491200,
 1435188096871502,1433569480380030,1431928591856622,1430265461241222,1428580117573378,
 1426872588991518,1425142902732006,1423391085127970,1421617161607916,1419821156694100,
 1418003094000688,1416162996231672,1414300885178562,1412416781717844,1410510705808186,
 1408582676487428,1406632711869302,1404660829139930,1402667044554064,1400651373431058,
 1398613830150616,1396554428148258,1394473179910520,1392370096969914,1390245189899578,
 1388098468307686,1385929940831558,1383739615131492,1381527497884302,1379293594776566,
 1377037910497572,1374760448731962,1372461212152054,1370140202409858,1367797420128760,
 1365432864894882,1363046535248106,1360638428672734,1358208541587832,1355756869337176,
 1353283406178862,1350788145274520,1348271078678154,1345732197324586],
 [1343171491017492,1340588948417040,1337984557027094,1335358303181982,1332710172032840,
 1330040147533472,1327348212425782,1324634348224684,1321898535202562,1319140752373192,
 1316360977475180,1313559186954830,1310735355948504,1307889458264394,1305021466363728,
 1302131351341382,1299219082905880,1296284629358762,1293327957573316,1290349032972632,
 1287347819506980,1284324279630476,1281278374277022,1278210062835494,1275119303124168,
 1272006051364330,1268870262153074,1265711888435254,1262530881474560,1259327190823676,
 1256100764293520,1252851547921516,1249579485938866,1246284520736794,1242966592831722,
 1239625640829354,1236261601387614,1232874409178410,1229463996848174,1226030294977148,
 1222573232037362,1219092734349254,1215588726036890,1212061128981746,1208509862774958,
 1204934844668038,1201335989521952,1197713209754538,1194066415286160,1190395513483576,
 1186700409101910,1182981004224688,1179237198201840,1175468887585600,1171675966064222,
 1167858324393412,1164015850325404,1160148428535574,1156255940546472,1152338264649224,
 1148395275822118,1144426845646324,1140432842218584,1136413130060772],
 [1132367570026156,1128296019202272,1124198330810202,1120074354100146,1115923934243100,
 1111746912218486,1107543124697516,1103312403922148,1099054577579384,1094769468670728,
 1090456895376572,1086116670915252,1081748603396560,1077352495669416,1072928145163424,
 1068475343724036,1063993877440984,1059483526469666,1054944064845126,1050375260288270,
 1045776874003886,1041148660470104,1036490367218806,1031801734606536,1027082495575404,
 1022332375403458,1017551091443938,1012738352852840,1007893860304126,1003017305691890,
 998108371818784,993166732069900,988192050071272,983183979332140,978142162870018,973066232817522,
 967955810009940,962810503552306,957629910364796,952413614705080,947161187666194,941872186648418,
 936546154803474,931182620449290,925781096453388,920341079582856,914862049818640,909343469631794,
 903784783219036,898185415694834,892544772236958,886862237182196,881137173068658,875368919620776,
 869556792672754,863700083025896,857798055234768,851849946316738,845854964378904,839812287155914,
 833721060451468,827580396475730,821389372069990,815147026809154],
 [808852360971646,802504333365252,796101858996244,789643806567794,783128995792184,776556194499626,
 769924115524600,763231413348492,756476680474818,749658443510640,742775158924550,735825208448076,
 728806894083232,721718432674296,714557949996432,707323474307686,700012929303658,692624126405910,
 685154756305568,677602379672426,669964416926746,662238136955722,654420644638584,646508867023058,
 638499537970884,630389181060100,622174090496288,613850309742104,605413607523048,596859450805072,
 588182974263898,579378945673314,570441726525842,561365227058444,552142854680720,542767454583672,
 533231241030414,523525717478552,513641583233580,503568623750822,493295580945034,482809998868256,
 472098038788310,461144255912802,449931327568600,438439719284472,426647270513774,414528675026382,
 402054821277814,389191943695326,375900514115932,362133769011170,347835714661172,332938364624940,
 317357814325954,300988492034770,283694430029302,265295418562536,245543816250570,224082918392244,
 200364991649766,173467568465806,141591177432548,100088098445152]]
private def pvm_c3_1 : List ℤ := pzigCatZ 121
 [
 [127145202,8968071739,27263224055,49960845598,161419815231,376779419986,535884607343,
 547399389596,491562820891,286786766750,53969133366,171852784017,192050611078,60382167599,
 113640005343,354028302382,470418342011,28456982370,353243496796,40621273808,236217828629,
 107807737585,117141592825,390395459707,47876927939,79049620286,36065749376,219299490791,
 12582120415,55054060217,382440683048,84415948919,50044693629,391974565072,424223600904,
 158976749500,89700674960,248264888234,116367495213,220342450823,106584172883,353769251687,
 469076637901,3582639361,432878246976,139093988061,353453491035,134040657327,973253719,
 374821833423,111038193216,120106667880,298810207571,67842920015,439670735348,113689861638,
 287167281387,121854433925,140614694577,205769369731,371849123685,237931506246,234279606185,
 103517191237],
 [76707000189,247304466932,8430672202,88994410813,272034814640,147246676795,241212455827,
 466404831673,194811812116,256494059554,258518673836,160137284038,4684835215,144449739492,
 6391270957,219754666628,100743477391,84916782024,239074708581,4142085220,190087524175,
 67598176613,111204794281,197972451717,70262137213,256503826273,252989141369,110978136323,
 374428445071,188978471793,95104510253,402577464709,7534624759,369545633801,50963476921,
 400165296439,152827943559,224343037221,89042772911,402043073093,349783049089,83107438531,
 35866429174,388981677625,28103608251,505557028151,279887918807,5395266691,532270667647,
 94642613708,52363954376,393606898156,247588305702,202560864566,460761676474,124838786644,
 241287124647,156118405561,148161020947,80736878072,155840351989,488147441935,390344078915,
 104849030477],
 [191414778299,260796338329,83831926042,399024159996,162349853227,330100460887,159052389527,
 126866146978,508272682119,824139306919,246089371770,449382517652,9315345383,68139105829,
 386716385624,378375260780,70883867455,152760729693,77553341798,207664165258,143224852462,
 439773933609,19741750965,79052118451,624277294688,345143013891,433739530833,127100266131,
 684296822314,99215854532,274783018039,351467024829,231429174078,163044553326,283360819965,
 263633280065,56228210526,94522259380,65590355307,347863975392,650937405647,87768908087,
 187619994192,16115312952,19165390454,44383725792,300083939100,142238295797,596776534481,
 270496203859,66633292791,184989483909,424906751179,366328783543,592587119991,310807652801,
 2424901469,338619153253,269584581341,411295914905,152049872679,98355700864,565152509403,
 7434574069],
 [861198647036,513444568810,31822498403,385298160827,829811667312,590569543232,859337626682,
 584513501414,282646745751,85146895791,410119241534,424398233730,16530512146,375794203947,
 153072146645,290787614756,91653072928,466097152369,381179462111,472664486294,1162840940560,
 922547308390,79270251010,366519607539,40259927236,658142823668,602483640330,169181690169,
 687995247529,436180419589,432431935618,458595463516,36691863649,1089718113181,894407380139,
 137765859802,480042160018,791709504762,700892007379,1049777282993,154065977266,433537784252,
 696017165168,449848210610,1034101438219,1144064894087,605911320362,1315548537032,116177832714,
 696805085425,523043580023,181553271947,318286981392,127161297828,820673102106,18799745660,
 724708689357,718556091271,313098749690,392534986695,1272125764298,46866531491,707575329749,
 297997451494],
 [2316849744208,1847686818552,1141554082342,973136473575,646253203523,107966020047,197127330610,
 397358874115,875140162144,1910858135402,68641998881,1807414569217,1194203957053,1188043378462,
 289341291247,2216818908073,1748204969605,1044101546589,1226501572683,2084743526595,896586679853,
 1615582846480,321565031764,319424911232,16307427969,1756181827632,3126611699496,65263929063,
 490550153574,1993345320822,2111113180128,2644275255538,446714149068,289956083729,2781626757648,
 4722965832856,621235504590,1500936903208,964785471022,158137690295,10274047955920,273964905653,
 3284939899386,4524858553663,7403760029752,7180768559274,2056657122710,10195646085840,
 2760466098449,8691175320757,14866904895894,21153259683260,3820107968762,281637311529,
 5170911159404,2347298016676,6915725395358,29076577814528,41672011275562,21554057172960,
 11224734305181,17191885637035,16192860206014,64374913897570],
 [93019775791878,86598284566626,54770135166642,20609276671074,5813016737052,22506790045904,
 72372900857410,149597834516038,244422191658136,345863843177566,443473191500350,528416849794134,
 594124389444118,636623905673928,654536940372010,648871571825282,622453930364906,579473832048784,
 524622527944616,462800911095020,398347236623418,334977565724376,275514552977548,221798422747106,
 174922725247988,135250638130188,102551075348100,76297216455516,55745683581156,39995059767622,
 28169897324946,19500127637788,13282767904832,8893580694326,5840664367764,3765092683846,
 2394666521998,1510433542350,942628304150,574002823092,333129866232,178988802832,85974301322,
 35024330208,10704967582,1223523482,1287475563,1246389015,664545137,215104339,6550574,75191774,
 73121224,50340388,28694826,14168592,6143268,2336410,770946,217366,53282,14400,7194,5328],
 [3746,2292,1240,604,266,104,34,6]]
private def pvm_c3_2 : List ℤ := pzigCatZ 117
 [
 [792138904,5210619370,65226413947,150095473564,361399586641,563726117498,578303939511,
 445036612862,225817949809,94932670047,249337112616,121319639721,17135308433,254173875846,
 379061557999,305715555910,100743715850,333862098073,97316078553,280008163724,157441135478,
 168348698083,44497847126,150453358601,285365835399,312669213407,103694738686,81749979579,
 104299010622,296101678147,108439661125,277570815766,73217277050,142807683269,47176748908,
 438257171766,227707115492,171438650808,348896321882,133757429602,79286820829,21162789213,
 39818135178,569312939761,493696628069,41711055266,336082074506,249849814185,97126437451,
 9226679234,355392963859,259426818765,209746119454,30688073831,408165014611,46636543542,
 234007254458,253422661836,272774082955,194490955086,233436543943,278469633245,238964033165,
 14045734262],
 [59706880309,388851584055,129914848502,37045927603,67275468770,114926856637,280777592200,
 183664611094,260058213943,309755197269,309437976305,178385539592,92159008344,353442625622,
 3499736295,200044165048,16014162821,178048195854,95426532590,13773490606,42399248888,
 148824484343,62774010463,48806793717,228049449527,1226607423,108406746021,307075931475,
 67994038050,423286236487,75098202439,360192158839,100721808403,306406155063,171077864849,
 238111322907,108359829731,254835811221,298903952661,298899271773,147136846554,468996122917,
 296806909423,156446928633,439735078191,231171614428,318134584203,234261777939,247783082599,
 244250191311,237325636781,464310094705,182897228157,176562871856,4151219795,213799886660,
 358995935398,430536884892,293753297936,77191206549,250115080445,38033313696,114787393506,
 160045128021],
 [492290681687,107077459609,242614070363,441408509249,361273714383,148150962038,427940340756,
 378380826261,229907336307,363608846168,12172189305,746233894105,566480895377,73917800886,
 91590052108,183734319249,143460673664,198708298980,586277383796,215468793177,125576580570,
 160455172189,451719968352,100264347138,247478417269,482663513783,384604662296,379004794044,
 171031411855,558674329365,80530679343,492750453086,180744112312,241941200753,262677876097,
 431468921320,304765521567,123506064032,148025831881,418872498401,175498798316,234164626408,
 8857694374,306687073889,171472890691,142376672222,167637040407,138411875213,232654984856,
 416010843516,132984650967,285149751363,190012068879,356316490955,17805761294,207096449543,
 496853435415,409096415535,585819941785,42195388467,82754607683,735134673975,120175410989,
 78680339351],
 [39129838367,996607125529,89165843177,701553680866,292897779430,212693028550,63495080159,
 104832382743,594878125436,1025003183684,703477194866,105052808684,94181330267,304542044372,
 579712214630,166145933458,323537393811,145397130111,329123330076,246677115056,388259164801,
 712665218949,126679057485,794950834268,1153865955362,477412722584,109618723421,245081588159,
 595966999020,748703893974,291385668504,376393346423,894239993299,332394692018,499485395418,
 288888093658,301528229439,1445107410481,546006501027,770901248768,380942334244,92419836963,
 467187067825,916356848395,108827299331,1317756274878,781277460858,1020178866969,919685293215,
 127955395753,1071436446288,316987822712,51439492591,361508574807,156457655117,1021358557715,
 1003335188888,326724129772,287732803440,89749968226,521197760831,1264877257301,691011569372,
 641821138764],
 [209104419932,995536638117,358440151479,1185823706408,2470065807672,1552729945728,240262668587,
 262102558458,82499255590,687184619737,1276165403967,1146516809548,2452689190136,97101613559,
 1423211813733,293843653351,624963745296,118369986198,2116329277465,502304468677,909954093097,
 2143319360395,1995085224963,1974911820277,1106825875072,519418983314,1491144919125,699965706258,
 1653580619498,1798359263522,1127277168034,329278229678,123773247388,4185789284168,2583356233342,
 2408403346851,4688835604074,3159614972991,7891634776040,408361748742,2271298271006,1719079882127,
 373246407478,11093603713178,57095739408,1159714178379,6036641044362,3228024972255,1512982032870,
 17284677950680,5940133269006,11214533366421,1300940098147,13086558520060,10598763855222,
 7578738390762,10651959453312,4092072163878,8579883737101,2294714694229,25874476063836,
 45222638309076,30989335737834,3742384497923],
 [23052106823297,5622189150977,37820262494234,77920810254882,91165348199152,73829152304536,
 39871165151248,10163060204826,2295036281766,25489645917188,80272834658428,160761972683520,
 257374660652356,359346439799454,456260015933480,539475171041062,602552363815048,641847903849470,
 656328911544280,647281669909770,617905406179408,572509466636922,515950771138862,453112377230982,
 388323699289098,325144075884518,266286370264520,213502426343930,167685542621086,129100280133638,
 97506302907100,72272763184338,52575467487152,37553957921652,26362215514924,18194365038480,
 12337304995410,8212162645858,5369913609262,3459617991888,2203112131322,1386247785642,
 855830426270,511293186056,290222231562,153296924234,73549656212,30981639574,10729466652,
 2492990002,109562475,525680349,334028011,110249239,13285092,53082362,50670954,35255276,20541028,
 10494896,4794016,1975102,737824,252368],
 [81546,27106,10660,5262,2938,1638,858,414,182,70,20,4]]
private def pvm_c3_3 : List ℤ := pzigCatZ 103
 [
 [125166354283,384992068820,635128085013,602206523274,217076592789,201087230453,228710657778,
 1038273226,313846352771,389589825000,101590398609,165906141293,202034152240,49865430599,
 170611837965,18783128301,341313641642,117241859579,168188845413,86262236339,402979626050,
 11534516067,139061823815,3730051899,122692421215,24720408960,25882089522,30866370446,
 113125398038,203516184048,45370448722,450469339273,260793718537,28279527554,123408382892,
 339670517027,166081598507,6580009968,47083435650,159342730275,30045845085,191792876750,
 173250811715,195803355325,254823152332,609831636630,196405100301,161603391018,319918569600,
 525738484074,55495767440,4011071387,119659594018,532963251981,365533947493,188807000265,
 338170664948,141157397503,291508847371,6018692493,74079316053,36720148219,307192330763,
 101086514082],
 [273831401111,192246977303,221001250315,286902929644,141896727310,27442198123,34781060014,
 9189053936,10532732764,241979961971,260918444923,25740861019,54877601333,198402618815,
 99754495309,499142471089,271777478162,16718014500,314413651442,110052470462,96391194931,
 305296349675,127612410151,160410360943,45240862544,27720159877,201767184488,13240546163,
 116484635646,245844941124,93158816927,454844670470,178382365299,97602958734,215545289544,
 258246927845,40413826069,27954825918,116566223997,53342319195,216390885149,31336738149,
 96403043725,200798544079,210414615387,313918464085,231039137655,50886609274,273529420569,
 359242833369,293999163867,20741341761,146831609341,283157049231,167736854805,330535422337,
 115691020117,317307747591,372114727181,89447074741,10658864287,129377935613,318246010349,
 425668797353],
 [135557703534,345403097233,513406216063,760537589679,452154702854,86902877383,10611243217,
 215100507814,709450198838,112123532372,241234846637,37104358726,543263645542,116865332830,
 414448407905,155180039677,155734074893,72234653445,559711449941,318930361895,394997412697,
 373208313232,88019926704,236111123593,89352635324,67880538003,92200030924,524362371177,
 953008240401,127591629188,393044692438,176964923807,416827949501,152972611436,488421172934,
 287120961774,63980706964,192521794697,16554643456,150176336848,290072313840,76374032192,
 506776284051,26468745590,403107103816,343449950289,19940247254,264142060409,354110113202,
 90811998044,97841900185,57676807124,89498304751,22523987403,270858475093,27804468865,
 184631009104,119872896735,193689193722,58946356122,710096056225,283300408845,518946070042,
 199623695992],
 [263044402255,38772332121,241171691136,81654152866,195858148681,269463709771,36565130393,
 53174013115,217469216415,656485507603,570358633177,329287056991,188409662054,87184002740,
 700539678389,831489367361,696185015923,402273422960,242507765176,329936695417,334015277423,
 301759719383,576063459520,541881297680,116424453741,348699804786,576847587592,738128315012,
 828443140918,272759538275,336754021737,478353258906,1068866018524,142124369470,171704665288,
 1098525167589,617596111007,281911625480,1142685205812,571530188985,37039003446,164157373477,
 1000650720204,907598200394,562459595052,164697141811,429249734101,649405016757,1713635824886,
 978248113728,1033707466011,970508162165,247129311083,430342288364,368499113326,48266183740,
 1299108917387,503195969489,239237718994,367493192770,336997861412,131619376927,309429583053,
 421739637059],
 [455250048399,778501683054,385759198968,897638642472,1004323030221,1769197630735,914196845802,
 1192222746400,534770858342,1535941477253,577295762479,1886247132410,607158553915,432441933247,
 395093809920,6466327667,792032313891,2064785064687,1387743632916,949308230996,5256366241536,
 4845416394523,5063746537422,2969044885873,990882353144,811248468124,2161072979023,3986728693068,
 1356084922655,41450339366,280494937545,532336618273,4114158490402,2955177309189,2366302831789,
 2527798795228,4306847059289,1185402281399,2234518159754,7014195755829,1806593935979,
 7587568636074,2630900836291,5963424128675,5250377436526,3234326023302,3244569950911,
 3837919481384,4808077735314,5513620479487,1903457020721,11084270013872,6215797285882,
 7946000154999,4761898764401,8479545335838,8755980760708,84928962991,1587347536561,1835798378754,
 490795709182,123863834273,7571563085766,13561872348412],
 [4232442477118,11849184955557,11857717659825,9188835380708,28443765019532,22210843294274,
 5006798667701,24916849928959,15759991981881,15910609724356,42708718036434,42303245339464,
 15678145222744,15887633839499,28491562902727,12235844156301,24350192008978,61968383501574,
 82498174197404,77775230301082,51880110915290,17706302738990,8909310666521,14425593906543,
 9150855452670,63221271978388,143375331819510,241139576474538,345937533354180,446952035441004,
 534697036451374,602064889828240,644803932200370,661567683170584,653629552067236,624300368258140,
 578176779863342,520410778010826,456107814620040,389861694604114,325428976889580,265571034580676,
 212063999971068,165821519758862,127060439293516,95470926391208,70383732956364,50930179935006,
 36179153043696,25234288981398,17287839598522,11642184516474,7714272739098,5032997207362,
 3232329108460,2039738109678,1260254732516,758550507554,442160223674,248046092470,133093972262,
 67897625656,32739815860,14836285144],
 [6285572396,2483344392,921532934,332905326,128793524,60847494,35692042,22983348,14586970,8726674,
 4869340,2537926,1241850,573972,252306,106346,43430,17406,6942,2792,1140,466,184,66,20,4]]
private def pvm_c3_4 : List ℤ := pzigCatZ 101
 [
 [193036360631,503928507578,680591914803,454867389196,33778133742,294136558069,86018900038,
 228297263088,405055875943,205616023492,152753786102,226680874767,70589200942,103691489922,
 55473579955,281728923101,227462581236,142502061278,9088016510,357060717477,139190191092,
 264732602034,35049021221,10251991950,103346951667,75066981415,4747254263,5256122762,2322080956,
 44773122912,356853624146,32716932098,296515152265,406230768067,107851042492,9597885256,
 203287420983,250383452127,2738774486,42653103900,234630027911,24826344532,156381567230,
 24288547575,511576265411,380343866274,314759062308,144789185496,93336720623,292951922288,
 550777693000,41652444008,334866088982,81387887830,81084657755,622400524795,289687373833,
 201913752480,77383219741,98020694865,260932339305,152614507186,247245677629,64771168491],
 [126181965203,28735216624,327419629023,314919966185,62629696218,114149723958,109651865640,
 14663997909,50807118216,133430303260,99795155185,309444099463,6892645426,325273378111,
 239742156712,346296920605,242368732269,221904786471,28016002263,116512778400,345528159684,
 54127597748,25836092407,280357309833,97308129529,206588446077,66006044029,195085516432,
 208401056721,370687205814,110624286817,123583279588,362273739372,93276142305,138123630504,
 224764642406,74476732413,3290376263,106212850623,33610841192,50613879001,167905630531,
 78156760131,77973705189,134372562675,11186626805,358995710599,301364158967,130356731539,
 8777032163,260086442181,424101390607,117690620979,222391612607,75207474411,218170120307,
 309318461933,118461456395,193317123301,386622073943,280011584107,292109346689,232243348648,
 324096965823],
 [240063351163,465971550641,412666819748,479577385495,693865280723,406078840475,107602778614,
 242471181871,177626127633,351563436530,661071094664,114043245968,314513598845,322693655858,
 335287146530,240955016052,342071350977,8570078672,221111718713,17076940346,375237961353,
 748896024847,52105881447,25948799271,86220098080,26670481679,301763284287,423819530096,
 185818369802,728296887947,776684468549,27397010696,233950984696,269525509783,287074673407,
 54637984195,380639790800,362215704492,106816737442,16500195066,255666744035,177539734490,
 634016894016,412664132067,16426777175,113438377567,242044222268,32419453895,337431651319,
 51754697522,53547565534,156358500768,29322093229,876776986,178247695008,271417143133,
 158897312209,114222482792,269313003457,25841918534,535574673260,118245844585,693806793927,
 191512676051],
 [306352203144,89739957288,138641194171,48291589697,248264268272,88539545862,72536519955,
 287590298087,16922618387,25636572710,108371191199,395076886465,890862513311,295426090763,
 35939779987,322949894274,368643704717,1146107499869,506528896399,114922296119,272760866156,
 13117357932,772738872467,124349911797,399067838006,141758735896,319219192884,62110766385,
 368044726896,962636813542,1077444762854,465157177561,86633191304,52294644428,796697905544,
 703442407404,701550572210,1443045181273,415261322265,58029296330,653423604312,27041989400,
 322100439005,254275914925,825372423314,435306960444,1386553185596,321801709262,1391980028465,
 47834703363,1312204759494,997953217190,438654491265,578536042715,898131907221,289048463892,
 791688644092,197423364849,754464370793,729330997121,197280391485,424993021620,3849770668,
 628013588232],
 [590893377705,294386684141,409833629817,531099521915,1763583816506,592986351714,895688610259,
 1482791879015,143827406837,2388828124110,634440734169,1155865806419,583685080044,239565836946,
 289070109518,1273925772045,2247862232362,2151904020089,2808794910754,7054104818921,4442672811216,
 179816925098,940209356896,3008560069164,2295836749405,3016915437566,1349947738865,772594676781,
 1612034965094,642174798359,2961601817022,1981204795327,2234999703841,4978629560150,1245742148661,
 1862765182585,3349257552516,4079725543497,2717018080419,4960135649368,4527178937455,
 7842026963449,4681411357230,2876296684972,6289036049927,208313239900,4422616345446,2962996824587,
 225674707095,8173873200324,747893225608,8224797908387,1721698545732,12117256185402,3188927387426,
 7748054052775,2194239855665,7331456762478,5742528585092,814911046600,1818497613144,2161974602620,
 2752185517865,2543965077989],
 [8524866912194,16312178797158,6097778120964,12554018468269,15052617448519,5637024318890,
 27844347954330,26022219903272,203101802094,23727491769213,21158216803307,7255382043904,
 37635396341626,45188073421918,24530691513444,7923155762247,28099696789593,21343359087473,
 9675875962678,48805152581972,76931410930992,81940297517716,63244419692462,30411774366916,
 1629223744581,18030842189163,8186963188459,32287799999066,101578913302736,192921041109966,
 296431009376818,401110264514326,496625920888910,574591932558282,629319677792738,658112004015872,
 661129201233622,640881720824478,601512638472150,548055862110112,485770834488028,419587023098084,
 353693705604360,291314516594306,234663549202052,185028028355012,142912500539014,108206341801794,
 80360702793238,58562900429544,41888653628776,29414375397608,20285202835512,13748223559050,
 9165007923496,6013535777742,3883412877316,2465054207286,1533838009602,931782278810,549906165282,
 313612104980,171919401130,90133230076],
 [44978977404,21271754362,9499137166,3998487600,1592066530,609843566,235112832,98941732,48828186,
 27774406,16735114,9956606,5655794,3034306,1536180,736190,335588,146404,61590,25214,10154,4068,
 1632,654,254,92,30,8]]
private def pvm_c3_5 : List ℤ := pzigCatZ 88
 [
 [775786492099,439655632084,285207774628,169280425723,410698280079,324639559580,220072550982,
 334180837211,35180548174,114366769356,100347736704,306486080053,69340044688,90041028494,
 32366030178,95072151983,159655230185,270757028324,181291554470,243998179903,185079994097,
 5061189933,241399402776,6618859733,22808193430,142911443985,52389474891,20010214929,162436627922,
 170720270370,135423933235,517540431,36240623732,213956089870,339483788929,170739482563,
 156529672667,460867032802,306352462350,266855278701,92384444480,14803383063,46818265610,
 426084900105,42930741489,235435574622,259559034059,316500953435,311172905119,398323230808,
 54674996117,156733540667,246692760055,108459115146,45657782193,165092885337,136369342356,
 202341767892,95925122132,174350539543,121898079226,536949879024,582807499374,78808537600],
 [306278360136,243911091573,80319304488,388519712295,142800561709,87582903696,72593812037,
 286505399059,72095659271,144650349201,128827440934,1024588431,251573152491,112690742843,
 298834064513,88905988236,415682615925,40139004711,85658081988,69247098003,364550780588,
 24960320602,212681524771,78940769190,224642060529,45456286172,149061019304,211321348591,
 309551717783,238169663021,313174844535,73688114295,14080037392,286965893090,129365094542,
 102770266105,35103673680,118640332523,107538268853,220295281463,11270078271,33245573595,
 52965023781,85565333120,53784867816,102512569321,437289911914,13525535799,269301730992,
 198901714549,347856171558,16424356461,172408898668,254834034757,92139690593,70322307810,
 33551447804,43975066337,156639371915,245694142059,118077314659,170415680342,478695029099,
 222484473759],
 [117898147391,139583161946,595354937895,468964694135,105379213912,107315473936,268546435285,
 683381097309,87990726184,78133851410,646773988393,250607168253,190180298029,48908595765,
 143058458571,446419238241,23643536896,169897491968,262103809421,657404274039,545605248463,
 385398636125,43865234801,75535240944,299979600673,168083499053,714929872944,118470181598,
 89431863080,289037657229,562160884516,650945045372,389916101577,134154612971,36617745516,
 15738342602,286941086311,627575159543,459059207233,196256348639,350406033032,314855006314,
 317860732701,260794022113,24114521054,69754441330,135352639709,709696367013,478134539743,
 170392372614,8948040796,301261793031,219514195072,124669629504,20131833359,179411363194,
 266622482928,82774362951,96508930437,466475241398,12169012045,132299025097,160770932231,
 226220224492],
 [77772276806,533787815229,1104642085,277261472348,358214523312,66459179996,504977988623,
 86503515201,134964378088,120054703159,331471323362,319713633327,100405152782,2322496266,
 57009662066,618120114369,127310783878,377057614861,696788622580,26612209160,262853071641,
 734805975885,775522842970,263348838076,309700234504,335585223389,912358769211,445115009205,
 762557910652,344888099031,493902839669,425045394009,540285819459,199459772702,615090332849,
 418184279111,554239220123,291013231149,329968391168,326030089328,1138894129959,843077609521,
 937128653370,842560208402,205854360116,668160085388,572262871591,71032346418,774706693528,
 1368921506990,640374892430,942101362397,228452577018,210567552724,845054382468,280297871944,
 1850626702307,258490644997,264895042344,985874270036,1292576631036,1442044298061,1160244616280,
 1686823962051],
 [3509351092316,2098545661709,3129951414632,3683323246723,3508505668368,1889495383147,
 1031520903015,3746939914590,2912318941333,1527373420866,3114445738703,223961650777,3938269344162,
 2508004413527,134340389883,643482181321,35657506136,1344499813796,2213030058367,1855997384576,
 846862095238,2704676319323,1482539001378,591257492219,176884514205,3220616766018,3617667525257,
 1985397289765,4942367650392,1687792447209,1849587354391,4875586824344,1944590486567,
 4485736642883,2963130649702,801908893805,3344700972491,5649956723782,2926838219478,6136221432025,
 1130304476360,7035113974414,2520158597561,4383399235769,4384136274984,2249502692270,
 4127531810499,1040459194088,4277915186274,2781599874667,2748662015625,5772928603844,
 2976739695972,7924122842311,5455378441123,5684309605984,3760197481474,7442465094823,
 7372565655653,2773813711286,5356024950350,1048221866117,3277116162983,626928312604],
 [1654328138244,353149300679,1996097027190,6341757807250,2918131328064,6195018260957,
 6457039576669,6348336729382,16047777669430,7361092332146,11084479671407,15788885422047,
 1493752302246,21976932788756,21521471996670,940732891153,21740193372261,18316297527225,
 7068704539548,30207919991940,29152343652326,4540563805980,22084448887029,27918630744279,
 7671571671913,23587514512064,43319879130080,38147165900232,12045326339400,17775213152045,
 32500637937997,22576727464779,8140502002040,45751990802038,73887104007848,81072689580840,
 64885618325380,32062978661986,4519021212177,30249085365093,32870526024853,5201702542495,
 53811985214136,139506554382150,242942278409818,352887453908750,457858068574282,547827272719968,
 615390682995620,656338726675730,669687610973602,657270226480246,623025752213938,572155357010538,
 510306381790978,442900475472878,374656890985456,309312433496428,249515410138554,196861985145232,
 152036777824834,115013340851478,85270139948466,61987336917174],
 [44205494755718,30942068038896,21270263796390,14367399629544,9539171361606,6225172890266,
 3990724814970,2510172169840,1546519780712,931260567938,546776544552,312255873762,173047858116,
 92871440624,48186710530,24142966722,11675280688,5452593804,2464539416,1083089486,466580156,
 199522434,86112552,38158236,17554820,8380932,4104154,2027296,994528,479092,225110,102836,45638,
 19690,8272,3382,1344,518,188,62,14]]
private def pvm_c3_6 : List ℤ := pzigCatZ 86
 [
 [805798787061,345161477018,342884738450,59966175459,473068530939,197473265862,330759969842,
 276183559471,53108498093,76168455748,197268350672,273767051955,30961666173,79456668708,
 74194624738,17704443963,240361908881,128935058570,302028716856,94130827469,215247001201,
 155094057051,203791801898,56315873104,78164154874,99054260929,76635378995,89840309195,
 54333260312,251691900842,39308287787,28850927383,86674744017,309418307280,147893372213,
 156029138157,373837643491,144585331262,533592290532,91266598639,17839765738,55616949467,
 206346650114,271081783959,331770236505,205597988802,18489638733,153070609729,579687968139,
 141373828302,129464732466,18786628714,305943871941,49491165283,68895215710,175660589555,
 53777236223,122625592754,262334486260,54687410377,147341526883,156064843224,696474436814,
 223826840974],
 [486785977742,89720961129,150780045218,180150034027,325452921571,67287566817,93079606318,
 217470932715,109272014951,235360222247,38073317895,153568988686,152812250429,22339064229,
 404700883231,82883183400,248497890617,296986931585,63556177912,194483127487,164230130466,
 320356981476,146618859929,75755745720,130375076623,180932115255,144545801422,69086579936,
 210078956983,192552064229,352684108477,225178337261,216919090551,72922319198,291354594004,
 17514865580,54527853666,50869049713,10999248759,210426547977,142558532937,32104204975,
 89287811905,51486154201,206177227284,267534833577,293268571864,9674220028,409264597746,
 157464779833,209413730368,12205030438,269127965868,14387625340,184482423593,71290777469,
 31230648994,42506391826,9589668051,114111635023,412857177801,197621527788,136610081785,
 241846791199],
 [451775260557,169462511516,34431307141,596030377643,390331983557,7967699323,279350658142,
 508101011233,539541040359,244357106816,240163740797,381286418529,355491998165,233377627993,
 72509056150,317157765631,385090996013,30280294556,191136293794,251942730777,511806236661,
 610221661687,481693926151,13188630409,84561123148,622472004487,207809773956,268038356796,
 500358774364,189057393027,259996973561,786906039940,337664482694,120847673545,139996717139,
 26916110172,111856140636,295493162273,488171355815,622034361449,294111253115,400147659382,
 212393996076,222860742009,214967867671,78244851403,230847712246,135540918123,744100323205,
 427410969625,157405660892,241217722481,127829923005,155804049056,55080354040,35464475357,
 240045944576,305619935796,281250034339,176764338706,254448533518,155056430194,210116201329,
 160288002637],
 [406099061858,148823219727,349906415913,127206182641,163438067776,542254105212,36331914463,
 412371182399,77646640604,299693008027,327568686632,68482528305,4683785351,184520991951,
 442094308718,483160753141,102471126732,638272664647,120705367672,249078091482,592018949302,
 874801992885,124104286467,183500391116,451255473512,453468361036,126385245655,1270180190843,
 19399318848,298562999208,216187017449,156368487885,875256665001,51002004765,237448314617,
 324018802215,449751529799,642723576413,530444422453,642317620862,272371285362,1314794852809,
 683933252433,776026822518,227987952828,1001325539816,241853128416,273533587139,198506064231,
 557002975388,1840120571038,93543224010,130980775265,222460255071,12098040308,1627562935960,
 454719614655,1064421083009,549979080179,621479729587,2451117937726,1067091893865,2042564851602,
 3123416003691],
 [3233320289908,2266944558085,4108979489620,2775880851739,1024004859020,1848914126318,
 3821351829757,3295325700888,1273101309147,1392470417198,156311244381,4340371946031,2765783961350,
 547061370286,369774427715,349526196365,1769714482011,2126522006630,1173674578907,1047560668275,
 2901260001332,1617130308573,323178573311,919395280636,2617447200893,2885812644244,1905862761200,
 5312845628649,1314010361712,3274036621678,3841880745977,1544697074720,4204081959156,
 4206602280185,1475339711023,2954031405978,4083878370253,1547757273757,7192997503096,44466904864,
 5898032918857,3798972505680,5455705643088,4106912049759,2098976617849,4905011072942,71821585085,
 3684941680043,3024056108324,3173109469514,4378624554055,1368777713537,7110392992502,
 1823715241270,8597559869489,4125087014167,6253878068850,2685757783292,7766368666427,
 6465594411721,2789109950608,4170981631526,1382908304927,2309534585765],
 [996750922940,630239888886,1249355152065,2462510694514,7374280400036,3086526148598,7027455703879,
 7267331028453,6346108876696,16761217571514,8137174394784,10978438337735,16637048531031,
 295566291488,21600445891202,22568444305912,707236641406,21184285052587,19735209049635,
 4710204332308,29063360711674,30456778066568,7348854113296,20174958924229,28746464227827,
 10956093348053,20074314693852,42068267854494,40089613970196,15932053460388,14512743078571,
 32140461617535,25808955643747,2521823231026,40146427105150,70676803563174,81556302268098,
 68794484393492,37731783806920,470278603120,28378274758881,35894440787005,13846865815461,
 39938474205086,121727486530280,223168234501878,333227996151520,440267595604428,533839385260344,
 605968217479288,651839880099866,669926503571846,661638988645226,630644952805846,582025216633742,
 521438270376756,454415561754046,385846665330822,319663230423922,258704240402228,204733026661304,
 158567377834638,120276680783192,89399794769220],
 [65147147112622,46566478032950,32666613532128,22502766018522,15229929891476,10130697648782,
 6623038481238,4253387660000,2680477526190,1654998348134,999124557690,588438297334,337316411852,
 187788804176,101330507256,52910609920,26703882118,13019956752,6135089824,2798839068,1240936034,
 538396358,231030256,99477098,43669784,19787316,9283326,4475714,2186222,1065806,512408,241044,
 110476,49248,21356,9016,3704,1482,572,210,68,16,2]]
private def pvm_c3_7 : List ℤ := pzigCatZ 74
 [
 [637457348861,494867015447,388487379257,22738925266,624497903824,86767995776,167786877409,
 340864787403,62642080244,279312795584,53372761233,109210539985,27661555887,26539936247,
 249130200302,39666650747,135819306191,186171237687,159025054676,193111406016,107774572863,
 150470064949,203240934429,267249641858,58662439424,176547655650,169646447103,35866244419,
 73402836321,214389809339,314918492252,9464367609,134484525170,119558588525,289935378147,
 137692197464,54081008758,272311212788,387158320411,46981892951,227333473078,406353523214,
 39149623527,369754412315,73367079015,26537091412,2353630514,241297660781,125306390876,
 344654611120,331845414356,398907218725,16398805578,119725976139,355094288032,107693102661,
 333628746113,68994228791,24635515579,249795327223,101367812365,70978005823,87734895830,
 169626155576],
 [521292216193,81968245093,71511881901,191008566290,51486313854,185141148003,91024935416,
 156651881579,68345304557,308066003342,87071036680,595968097256,551175925432,18223904634,
 59749042444,89476999776,111783822885,138916412588,118290193573,289976208867,71912944077,
 142446167453,7162379257,137877907011,9714484256,69975425605,79788558381,41282256021,17753408785,
 411824076811,183877421373,408823465489,329129163164,233758290911,249756368942,7637212737,
 18766421268,208014502785,34324703138,144894573396,38167580950,116433286664,157959111197,
 264447956029,384401591329,100669384491,327157752221,107058986866,146943577971,203978676540,
 200345621260,94139220645,88966809595,106579854765,100384537440,178211831731,125553164125,
 45869182935,300877548821,225440753374,122962723244,67258341515,36599354407,47414623295],
 [592846005982,217466145934,364241435221,109899431522,469744032524,89068711171,279878674805,
 57847253337,402265447346,55922314789,131815617033,544495147099,307442031524,141976372728,
 492592727551,31063854951,228565667569,54892600925,225187686225,450517379877,64896782729,
 142021586363,37018332865,167309106213,556029466093,163295577247,242934471036,137112181681,
 781053674675,610543305607,278906828062,83008749118,368045188611,183689837061,79163821158,
 127758615671,284932570987,707205025545,579079843953,14283170233,191906071057,125757983001,
 306149970517,80961183707,187172135890,561692828648,70859170382,535153344087,460869274040,
 712943863496,253485970924,140854582571,274833370131,160105641769,296373739675,379659300167,
 125058270134,705905700595,139932328138,54021695552,348514753178,349862113971,18392825800,
 408672270147],
 [347969704268,874187365889,242827501667,160703736669,185801729124,395384020421,53057990416,
 137458992157,323367995844,282909439846,169831889547,228068492385,483903223926,185949520032,
 43104361284,444705786102,901228042891,99375280160,298086185350,103212955757,4126985457,
 35583949382,45576540794,276146997966,179995892159,392653692387,248745220397,493282016896,
 351386632256,293915766414,1107888276233,333555766307,948344375498,328224236295,197578387354,
 386200405651,663445926695,114539304812,504807990626,728180228120,808620436725,482124079297,
 1615543034888,1666563264293,1737612727760,2921447865963,2499663120934,2632618630995,
 2929393576588,2911661229547,1004207014534,1702824316163,607102910919,2480812693952,2891467601043,
 2164820168616,3621818450959,98452638388,2598159074912,2612171854019,2283680947144,1807415858477,
 603850472859,2845451305658],
 [825394287681,1165015878706,1106359598345,170570301331,3265431937620,710153520287,187620870730,
 243401683600,1033984951983,1071440395764,1699187457623,475156294322,3160638360844,3391663258377,
 1089887479507,3572886704356,810388839669,760808822840,1184038677472,3258231186607,2135924513282,
 3155789623164,3794391870591,1142624905172,3628958894782,4734987650531,1237180280255,
 5000985888456,2035312147135,2646690212041,3253014941482,1645004581335,3087920278059,
 4377653711938,822948021020,5369686010005,1795272523238,4088220978574,4256712560389,1680739466833,
 6059265181418,349190339653,6619582085275,1033709555310,4833535038944,1656987756905,1511213280151,
 3618945564612,368685858507,4880465386249,930622186772,3956941369444,3137343369917,4358656398203,
 4628676213874,5743969006956,3867562912023,5151056348539,4683286368232,6812014273038,
 2613654244521,6300120116273,1266980105286,5817605993986],
 [854366622712,3069365569867,4396577353,2447675539406,43381107453,1272658278873,1209263244240,
 497691674316,5210462431851,6459893231703,1438240117806,7577244314436,978438402674,10517463960071,
 9333878349967,5877813886326,15828178577448,6097964363682,12213319513887,15538462860207,
 2035262168896,20447463771464,17526734679986,4496695529635,21249511427415,13678580778589,
 11036632237476,27474291866276,18668877612854,7075766736833,25108667002887,18303409294579,
 7633697540344,30282233371338,30514541958082,8106682593416,19185517527779,30364281515431,
 16882640813817,12183221238990,37571990294118,43096722160134,25459690873978,4754123691337,
 30072018990555,35989604994549,18078884106519,16682104512576,53935932243486,78576548494202,
 80800236256388,59419364647036,21819499728388,18776858995455,47392253536895,51301483877401,
 22915290860701,38940708080010,129308783484478,238560240511320,354510596689026,464666157527330,
 558167557421838,627139266822362],
 [667326523328014,678064056883812,661734848889832,622924586833994,567469591104950,501557678655334,
 430992819998388,360684649357010,294376506813074,234585474662764,182701168240888,139180617148312,
 103782493041234,75798688111194,54257601935162,38086822409948,26231934869774,17733815177892,
 11770211219190,7669408647402,4904486012788,3076150644892,1890672329638,1137477760040,
 669050148736,384256674260,215234865922,117454496186,62389826370,32238619588,16200466196,
 7917911112,3766085992,1745477376,789935404,350167386,152695724,65857188,28268888,12151850,
 5257430,2295138,1010440,447098,197806,87010,37846,16208,6806,2790,1108,422,150,44,8]]
private def pvm_c3_8 : List ℤ := pzigCatZ 73
 [
 [599525679955,497509431659,435339974357,124697514629,591005237970,212839072974,68304732385,
 363436695641,77663451149,279136104002,41021706990,101681090959,37967350289,103759472789,
 226986532114,61421878472,63698647559,246683289991,16801785946,238951518848,6605154808,
 74772102245,319560430247,149967870008,56348333006,245684753092,69069496651,70385149683,
 15926050276,331008412137,196070075032,35361753172,151227754540,77795424846,327610901885,
 243681747,70736351021,400206038358,163447933637,221985152525,35307666767,388486587620,
 305818202380,231093097095,217344165621,77628239625,111343826430,208328781985,112496957183,
 99831998408,596425320150,144154580169,21290199489,288405312459,215983827356,207767059398,
 221637250015,228140334871,10324569304,175004386553,156943751247,137775389407,138577358959,
 387530354920],
 [259823717977,221298396947,236028861275,21670834836,219771340634,143754115847,43495571190,
 10764283849,267737696825,188768301944,12466808599,224474490482,688062042190,369689407548,
 87613298064,193654227962,96200020323,67485058324,115047285294,219938306805,132889425417,
 201149277913,25692114551,135679924999,46890838591,32878862875,57931210471,138071349887,
 148427614918,274095015591,54252266715,648833648843,114161764264,192244705529,92427442392,
 45167651786,154210755586,103777779843,157351139911,76711111340,15176082142,167790862710,
 46717181054,20658493021,411932963999,118544251029,428423012179,39579298935,167476022925,
 73075050739,239994660356,104813295530,28396119876,201115656499,51918725584,2529833119,
 199905756163,74414065298,325776634959,126342111697,164276043018,41189286470,108431883658,
 310109968617],
 [111008752122,628191580918,68682543252,320585908857,263571088586,330214065718,11912167632,
 407659425409,169406778754,103721179316,324209851694,479133063511,335275271667,398323319534,
 190628583545,124353300067,233264695907,157860706959,30993081052,389588938643,262585251193,
 211249030967,156445619133,105417286594,268138963061,561200816005,148379287469,272921236610,
 69832405537,895086378129,478857401309,175972989452,8681455507,337475068675,92802797351,
 51806188909,41411865932,233797739307,799985661327,408399358761,275904444569,70886054353,
 226753616569,240624753441,284306404019,183247101602,744280666524,216814392679,336287853385,
 362073177278,625732240662,378200423656,72284725341,182044055125,28070594739,654731442363,
 199696646732,495075451033,245542448397,332308130025,430608713512,109400044805,254481042468,
 641873819823],
 [383943588408,273611064645,400750415819,601634537925,146002630542,239218435039,31402364351,
 231953630515,96231782775,309157716466,361867121486,352305148869,25831627913,439480858778,
 235002889515,828234296188,173145702595,531537556993,84373849166,97744642616,22038785709,
 54787840706,135498437251,205533912864,208166219326,1054278735,594788837957,48069755015,
 11864800091,920419801562,121059518108,1313434798553,317914345078,60562759610,165728890932,
 259602332640,523267335133,462982389197,385623638433,863484625442,857310501280,1921895058849,
 1965792521622,1932713027445,2696480888018,3044458251337,2310025388306,2929777663489,
 2416934367322,1255462960067,70509309828,244883299904,3370806714831,2911359217190,2364831877363,
 1890782155258,520118021163,3782787769497,2761701249186,1713457851541,1007073480552,895793612454,
 2765946943673,1653110947670],
 [71612700448,1128751521174,883555315468,2426458950617,1874786873528,1354842636226,27761805373,
 1158168761626,1339532248709,900674669704,65056409660,2882416554395,3067051755658,1351371924458,
 3918483224643,1287578652720,1163838189012,777775460299,3107261778332,1254216047837,2890441176399,
 4352678749768,331884888582,3569334691165,4037667421554,1270685410044,5459801482745,1645904064886,
 3309890032836,3544526700439,210584186462,2745174873392,4005760363519,1062039474027,5184904934930,
 1745581687633,4508903223215,3893444727302,2055234326780,5385593383929,671296298622,6101867505884,
 2322494975501,5625733086383,2403668295428,3078830604820,2564734663577,366247193254,3995657734738,
 1955781489599,4519302977413,2460890987156,3224002568710,4623568326219,3649584326927,
 5739831721942,4854403630170,4863911467373,4317904121019,5519443120078,6098108299464,
 3221827690211,5563023496683,1817817288846],
 [5070114910832,216323011190,2442440952011,695521000130,1994726713000,710514679083,810027675025,
 2234327898816,634984643372,5988378006345,6895027383027,1917262869928,8177745309214,828367121452,
 11246768910805,9852361989177,5961084213028,16247997734088,6379695320316,12358867019781,
 16073485939807,1498909435482,20426557239824,18158625001004,3758657130639,21224171551321,
 14591875630221,9946152303346,27313522315490,19753335716268,5672396397103,24762298811767,
 19525866288895,5752002947622,29328688685758,31386890987956,10221194900918,17466067244921,
 30468934587079,18946517398327,9428858204074,35914077906878,43641012276954,27932129404220,
 1819600725823,28467713790075,36852112062035,21321503272423,12291809978282,50172178721412,
 76964219413886,81995639832790,62980290003324,26384447999752,15032457751293,46215155517723,
 53906489269049,29724097484169,28336966973076,115996482474324,224032249440534,340360465298836,
 452317299147968,548681287027250],
 [621118421604018,664909713517334,678991136401068,665456634385592,628728657106528,574598292217848,
 509302335431562,438756927243466,368016133218936,300973872016470,240284870723024,187451801114988,
 143015189586848,106787952791860,78090838486144,55961397503500,39322718731674,27107667179856,
 18340476586768,12181388623020,7942261948688,5081886128438,3189235241282,1961393297886,
 1180888227188,695210688416,399733273542,224219491348,122568821330,65241352692,33793885606,
 17029069902,8348494216,3984005406,1852741932,841219068,373955888,163391154,70514618,30232320,
 12953170,5574242,2416696,1055846,463702,203804,89166,38634,16500,6918,2832,1124,430,152,44,8]]
private def pvm_c3_9 : List ℤ := pzigCatZ 60
 [
 [158479287071,417980582695,123412596833,388429575013,588984989619,488711121875,306612795627,
 20192156181,522667992226,263957225758,54652336772,139031457887,219946744221,18907232978,
 82625254235,290155368228,44904893461,32134948565,179074506059,117868077607,333438756798,
 5703800263,136547273378,167444236773,337907206495,279560322518,36977032809,230139676584,
 136613563483,61565504539,109300471073,126571896297,98293737470,24648930598,185427084002,
 40249150076,126593464834,263008351605,136076372103,253356884147,475740313408,86529714642,
 5175991974,295520369055,188702811581,338304834332,231795439186,222450326327,277294284123,
 225420797,17350824596,418017419486,230697458321,9007715581,335482147270,86445356714,21412255547,
 407432976853,319640309819,225725631998,62315808362,167796119772,64924955917,71675036867],
 [308582476590,40925561806,266446438741,179087847898,152511876154,93752224237,95677362612,
 405076322919,261165605445,6272773702,94256724536,113574178007,9479473578,244880471793,
 64814761140,411158050969,175437036466,287016666259,245446409420,59422064188,29720638257,
 221734873423,336985448567,9147299710,120355239760,303614833718,192467933074,470477687896,
 128762466316,266178497900,152952802084,381667694288,94941975443,124723860769,101950566336,
 174803994623,7695010451,168797724013,185881140713,62944476885,136539610977,125298864914,
 13654464231,54899906856,108277852081,410409083055,83841001065,392097904869,146529825471,
 205240571666,12264600615,151578250675,14537554125,222399369563,225059503100,113141563627,
 150578633556,119265339642,158057334326,113693739931,164751606881,6667769400,776175648213,
 147802477409],
 [295712099092,197619848659,132518696679,223113895827,283338282534,433374109704,336973568647,
 321833912001,117828169966,164315911252,123594661819,476703914289,31841152622,229248403546,
 89749978365,290618304985,28498780886,288572750160,223344508514,83493212712,9662583702,
 98025100536,47765379013,440478605588,50779847995,327448437447,261395258672,289156819664,
 154085686659,527209525563,127756310724,284145320426,57645041470,376450883417,501608618613,
 17553297176,422716829732,686125507037,74333582685,536258597093,148585149574,299726666401,
 165940312458,483175783411,72272766095,349906310235,394629590524,1001497973667,571121157333,
 9727977380,372976633704,183939651085,248814428585,329914081049,52224260548,83805501127,
 471445224631,428171269313,641649054295,312264369965,88818193731,428285844038,790913224141,
 144882765833],
 [232078619278,61725239607,442389164050,109166791124,6469829574,902509345974,13616843963,
 232186248923,67011880249,30582021526,500085001341,260870227473,222337308667,404582094729,
 611615169250,265406499025,74251560224,153022673657,370210346053,421317713304,209525061923,
 1224943907137,903174362954,1883832904953,2215879943680,2485606084127,2711565580506,3413538746743,
 2639013761148,1168499019389,958202304030,733585886551,107588566742,1853343612862,2420773896289,
 2531941579370,2668950500823,965485624002,850000703826,1138794727019,2522477023398,3464470255955,
 1271638419036,992022450072,1588216647753,2400963152700,2479451335433,342644135950,1606356320796,
 1830165822917,1521101446710,780441640853,676790762693,1122817459300,1106299860843,723928687392,
 819585332395,851819176085,2276161371586,653503595401,131047226161,313657793868,2063474382405,
 1683187128064],
 [1109786472094,1504021365783,772926795026,2069863331847,987994684137,3980497143180,2102012336097,
 3242842919421,2981745117588,948250150761,2133230832073,2213108239462,1786216117967,1683740536385,
 2623466089414,1904204288985,900712900073,4463099731450,2424267558189,4132348319151,5155256704336,
 2231567004266,3829579582903,2265870949496,2363218338434,3496478684367,1329266232508,
 3550412725076,3405057435937,1473902502905,3515718932992,1782576463295,2304505293355,
 4702978389918,793938248654,5530469939909,1547912189728,5553834448366,2435730505175,2931627044569,
 4346882994452,1282864095250,4562636121975,791392402816,4509059358058,1993282885773,3723468317627,
 2270930709114,1668701009550,2979583094719,176541454556,3368623765732,2388773298267,4793077277633,
 3060063168238,5724086950614,2713382565045,5566542977413,2468435334116,4796962879980,
 3218934896783,5307720984669,3110764381260,6348169303406],
 [1144105030071,5459963226053,105464489365,3826772994772,80240673819,3425333623385,668383929503,
 1847149528194,69211273428,544773161431,2407488909064,2530898093866,2285663140477,3687588695565,
 2522857642098,6725044575570,417608036102,7882624191659,4160057160087,8247404929482,
 11244511574912,1482218946743,13397027754939,7464202046357,9181239329096,13699826655156,
 1627407658497,18074624711083,14169129980029,6532933710300,19290178824570,8440249395856,
 13569296051377,20872850081121,4215296529729,18669504898236,23010635144102,3921321457574,
 18825998265217,21795008337223,1599510241971,22398773246972,27439410132136,8741600041458,
 16886515124519,26833713053807,12353905301563,14814597890614,32954954760992,27897003964180,
 3373423536612,22683514924173,31642900567431,16959613239913,12218056447206,37780538690468,
 44220148076208,27533526346594,3203100216633,31404554532013,41811257170057,27795408667837,
 6040468492796,46433937256352],
 [77360648315166,86426176070312,69300067013766,30959582607384,16144910415997,55941974245605,
 73182170787597,57185973646831,4059622367169,82903186854910,194418861478240,317464664568334,
 437914800175288,542959495826706,622889429443802,672051842877580,688986212347648,675893506737720,
 637674122763932,580788962578994,512166756988034,438315562381572,364718213906368,295520324710736,
 233468665532146,180031736784890,135629535503618,99908543719284,72013478471718,50824123766752,
 35140711208298,23813502123354,15820943709950,10305979678634,6582138813452,4120607864128,
 2527539159098,1518261554396,892562911590,513201047136,288407635620,158317853364,84844894676,
 44372347572,22639683072,11268203012,5471530520,2592866916,1199881798,542745208,240286506,
 104303054,44488318,18693800,7760678,3192542,1304946,531130,215520,87190,35126,14058,5568,2164],
 [818,294,98,26,4]]
private def pvm_c3_10 : List ℤ := pzigCatZ 48
 [
 [148803314040,104558745335,245557626719,257736170297,7194664342,196188445953,278549382237,
 133326173993,531755985887,417317109997,661623525775,369979281543,69673682348,26155875652,
 418774778476,211180746540,9136221369,264002527732,417828302407,30894077293,52096321215,
 8710032346,227669314666,24864389802,34709344888,314659521889,47149071257,50335080065,
 354238366564,40551504447,169820513206,225631602231,73847983001,21565403873,85990372653,
 212533889196,71528180928,24728264503,79395936389,113793439886,276902216269,8604432280,
 144470848151,137053306979,491748545750,263595000494,127656203297,144910592131,443338377711,
 112325438680,356977552664,71482407768,107808712759,292811746883,55067542685,344820572088,
 150234563054,269485289595,73331728472,199023241839,109555444478,134354020756,176433490371,
 469535495237],
 [458093874428,102905664686,430195668222,175679132053,45754543448,173584416283,107655987847,
 66784038876,276424929907,7351465973,60323158552,264979995794,63795791383,33513009570,
 194669163229,170059596090,115949183966,191062161628,93445157478,163486708395,46480964785,
 207569412065,19484120931,124205989983,240691203557,252719576182,5545991413,190668880453,
 179675049149,262191364955,29085618319,166660915635,237456145528,137500522822,107540396719,
 169445064753,212366181843,312931695775,244224622718,227836740849,127892312812,228465083656,
 138523012838,354845522910,268409418744,398785311750,31147057916,196482994056,160879146756,
 48897620909,245991622482,253978659591,78326143095,101783436820,526146349925,140653849879,
 263829629574,28311502079,105516701344,50283324773,109685621127,291050574031,351360914759,
 42722583045],
 [35113677918,181094732313,291043097157,98268645720,88944831128,82995631849,560975714121,
 5662686199,546447935116,242308305696,44081460821,348295820199,294277759288,150914856218,
 421075568239,499824714521,14285017288,150329641659,38720089089,299754846993,323258573140,
 491705707291,643402638130,162940049419,121102940625,365300194999,392704818014,127229505399,
 154496989406,722208202707,98966919524,128561382952,39937226042,353654885513,98686237525,
 499976409882,377080677838,343335573311,163362689717,452414496438,30837651902,387912001644,
 92059734577,101422068417,293336355981,494972754896,175809483122,321766709889,165718993473,
 90812286355,359547288688,64133155378,927021291127,330238145154,59732470292,368744936205,
 141962796343,516535807165,245390716925,84105345886,409206528006,572258730991,46791589393,
 643895722275],
 [230836865045,77036031268,21946541663,1610815112307,1531017781412,2009328234875,2836523283220,
 3112480584759,2402851090202,2539492647689,1515506919214,1612110384665,38381768948,238495389356,
 1601956741997,1803439894604,2472548002181,1487802026698,1446982355219,989175990872,411176222994,
 1699394617775,3106660055338,2173128610611,1623221911608,718836344708,2135796654217,1872584377926,
 2056639094873,1206812134922,70415318418,2513302740161,2479760959252,1199593961001,11643138818,
 1335697427824,2160671029019,1065983840286,240643073597,875589351885,851464733560,1643823173245,
 438689862064,647144147150,960301931001,382920120456,1381784947245,546352055712,1956293777686,
 1456113641439,500020602922,287702906282,1581295449569,1960998177490,20148477808,1477924760569,
 1584821052678,1136976883627,304272778541,2453679691382,2341225197377,608513393101,2885643232984,
 2247317207339],
 [243208661053,2783267347574,3173229974407,485855639929,4282783952196,1892257060985,2204056822725,
 1624933820938,1477129227879,612168922492,3004497262610,3522369391587,1623304566177,4659921082018,
 1508287772499,3104630502923,4312821677218,142830738670,4833933206451,2553636862108,2889299272534,
 3952893312425,486747057153,2410377725816,2432728331769,283666811591,3097208009874,3115617309533,
 3601993735991,3698680555076,920774872062,4330158008253,1322275561160,2943550963466,4123789781417,
 1732352656855,5448560972248,447187181756,4881639101467,1762459556540,4719731602894,1768081512585,
 1789432047687,3415196009270,293420596236,3778138947433,1120569837598,3591721234888,2029150178971,
 2705518210357,2708479776964,1429021453094,3146011460463,505460201590,4657488027690,921438628605,
 4905336163665,2109885931632,6342908195156,1361085897925,6226259464367,917459632554,5742309221844,
 624995614645],
 [5087287774109,504113166334,4331078485210,1023616589377,4849923780955,26941522384,4349929739504,
 1022833572412,2807536888729,986519559495,1153112846342,648280933647,1378407199779,1624730063632,
 2300576773884,1725056689513,2890586632515,2324210504880,4935917751274,1492699402939,
 7675033459115,2494050615157,7402398210866,6276973910866,5377709179993,9686327443029,
 1533741054062,12734138849780,6620971822298,9587156224835,13080273844017,2219277123852,
 16095019142762,9326870158332,9774697593195,15944871521541,363452292931,17435097801642,
 14344099239984,7055248005147,21482683379535,11692471084859,10960870059062,20112648868078,
 4988844146990,17623631272153,22533835044985,3799560011039,19327162992004,23137536286114,
 3840698550592,19241384925847,23344219815571,4187539428451,20666135440848,28677677915006,
 12653710160796,13580323727903,27763350689753,17952490303067,8318201312150,30790553800030,
 32432497142856,11826610048652],
 [16541383651573,33017957426245,26136952116165,363315368792,30554160635072,46414767043100,
 38336852803190,10117900033342,23585525828423,45130762469101,42573882045139,15005465642539,
 27411429915952,68044189535542,90605652419102,85324575035898,52348380001544,1584284263066,
 50501040645617,85737423041771,89128917056307,52416338926217,24395733990262,133593928840374,
 261912415538252,393530217597152,513118696578304,608306553443586,671190519877792,698799675749984,
 692653978985902,657703234298002,600980650534700,530270465772540,453003122133590,375488894372788,
 302509311841018,237220483954142,181287157661720,135156798986452,98391565047890,69994792202204,
 48690934352370,33138917866908,22075654595450,14397676358518,9194615737606,5749605056318,
 3520088775600,2109518305424,1237072811706,709634484172,398048464510,218239845158,116916398896,
 61182512238,31266968280,15602099462,7601408684,3616122744,1680005336,762500938,338257456,
 146766144],
 [62338492,25948342,10598568,4254128,1680744,654702,251840,95788,36052,13418,4930,1780,624,208,60,
 14,2]]
private def pvm_c3_11 : List ℤ := pzigCatZ 38
 [
 [117725914094,56350538458,129788422530,148266783332,327815721245,102933220981,79040980507,
 240026401309,23610355474,130781785503,338943917185,203892095706,326738719685,219366744351,
 199890629565,715224396137,449942965493,526473469697,156034257149,295736021057,203713182966,
 54190958300,359244166410,186804673566,43813766638,152575706968,229267867989,125967313579,
 152430243971,94141907290,71258606326,291666121294,22842530385,261557443889,22280889238,
 144443880595,179660320319,344424801946,28647755502,40268672042,179561041614,223767952113,
 131492894163,27468427728,47343373216,53300665113,142922613364,213944867803,277285217872,
 117255426552,50921920216,360563856257,60177122119,614503869165,433176783824,448713329656,
 95181252996,33958823209,331374674423,34851942163,78556229219,388034009260,26627257794,
 202613894883],
 [305359262065,224608373060,124638293822,10278652620,31034462227,204373216521,125768998838,
 134810680500,136011523166,63177342891,387312755269,62948761441,34180645639,88350950824,
 231787595526,111160550359,286978521086,119737053446,47374477874,63817788899,125296698193,
 277619327005,3391524021,32679740109,353317908704,191555282839,181595977357,210573925300,
 167581560667,146089504698,48451056286,89762635558,222486786208,48550538998,59292016602,
 242613912097,23943408907,134976673815,293655391697,260190231506,89231079362,159626414189,
 58709249156,463391011721,218320378329,68113349584,176777550587,132043801228,162833409466,
 106502510327,230485647713,66159481908,141501055943,202004317323,246933250219,22419293837,
 145780780336,156475657793,287577109620,236135098890,392493668424,141994498244,161406190192,
 206855854408],
 [413865528188,179738788345,487171026968,155555999603,349370881440,761988599635,45078122525,
 206443465319,506818828854,175695937641,215118994951,167950919499,752547989648,431286101669,
 556048947617,155213166045,19242578221,108360094008,95350942965,226952626991,263092062155,
 24609680617,165534277443,103211344134,448298246161,266133846188,184764975236,292171071694,
 22803253856,257442697307,29205530802,267070508544,163335104559,702853297697,409660363269,
 617404021404,343511570971,266558606199,80874043614,225495150805,528049578870,316506777417,
 54124435111,109293038559,255045666600,319742235745,616179455852,1064357300639,205259344766,
 837465810895,2201675108848,2771088206199,2645812869944,2934619181805,2826993026714,1540105518247,
 944854963836,343604361051,228112237465,1390076020030,1649355912201,1978394058776,2044632939453,
 1608897940482],
 [610407291403,29315896020,919961930422,2261982379341,2127246507050,1322506334067,1094914997968,
 286717401677,1956621704611,2360550115046,2439251942505,1071140433512,388858610278,2323432438431,
 2381207573160,1451361499109,40881224540,512500625048,2006653905571,1607270542228,1566441389143,
 617969236691,1659482032834,1911946797937,977420820310,360629602752,1588605493333,783159229334,
 760332264531,60744771410,47944198628,1625637583273,770405205004,373684944651,766280646295,
 551684131392,1594865184489,462219178088,1012024760996,1231904218177,1469013513246,91599226472,
 1176096737511,2421476276934,514074483975,1687117231569,1536698644178,1125634922343,335489521149,
 1570835380190,2436286810509,272592960848,2568961866676,2371571053085,101890920026,1607004286566,
 3226677341345,890639125076,2896825311772,3477485504689,603559933491,2373277932950,2701453673253,
 60429421354],
 [2819752571844,2645174062163,540163762647,2953721817790,1773886776657,409445618797,2409242477128,
 2698967178237,361000371489,4679732066080,2606539524045,4165350353893,4675170470172,1799063113286,
 4387588101483,1178536891916,2071684432428,3322167202255,692813401910,3539812985416,2406619009471,
 1613015742343,2739383868214,1208844604235,1817549951835,3287747468944,364955177623,4459287659763,
 2309893974606,3877376999602,3811482543705,2179807683283,4344959601656,21028308952,3633813119701,
 2417323609558,2474822055716,4350936229983,1535662366615,4698094554716,190861688660,4274157130811,
 567196489584,2145393410770,2539338738921,1297271515599,2683647848300,896289580439,3821079104665,
 1359984010798,3096335794258,2682226403671,2850303069819,3034457532500,1761089799784,
 3333217195315,218628876074,5313734656946,127263725084,5226360570553,762699128084,6213668112698,
 182079028015,6008012016019],
 [200225746985,5416581553084,426013786170,4557744202957,252117241679,4004385509764,337768829524,
 2927110244637,706416049408,3560618305638,96937369336,2681189064101,47688475270,2197401272550,
 3498915334,1088821510685,1169322322552,864889646294,3052436640737,2820636249519,3048725463230,
 4620256484880,2099758940585,6115012021713,398808232226,7109827669766,1738726582426,8181209195665,
 5934492837771,6673244769292,10266943176012,1840023894029,11773470473023,3825809885471,
 10746230794760,9665945724416,6819649506253,15143494995293,2323890270651,14636237445668,
 12106916965790,7017005979601,16838260602573,3640501841139,15439984973278,15098153160024,
 4802006165849,18935611582023,8898976633927,13564947024680,21170568024200,4398792082714,
 17310332069057,18865138252675,1324837912972,20028141231916,15826770674840,7229153485017,
 24541966247781,17632413228495,6680610573354,23907285407462,16977432912686,7171058934109],
 [25050822766983,19394371987963,5042875215298,26524567690454,26162930432788,4156623983878,
 21048738196855,28593153371003,12021490709863,16195320245842,34830861460450,29922312320322,
 4551790630874,23901538390191,36015263266377,23120781467663,7560564803842,37855654168080,
 49723610193228,35536425121698,1992499588060,33748511812161,52957016830313,44428510320703,
 9544995971499,38527157373366,80559193521474,99079017631210,85059781596626,41161071512640,
 19203992358705,76166864863935,109302793044061,103175130255909,51017484138759,44157502464644,
 170908198972766,312442433455324,450405262454598,568393985670478,654492675185318,702500824521654,
 711896020755492,686831628635276,634592223917202,563923584205960,483560996595054,401148204762774,
 322610670456944,251947011515562,191341952198036,141481369673848,101956436186214,71668116676284,
 49174562947152,32953880232418,21578235174396,13810390317236,8640969768440,5285961375708,
 3161455777478,1848474828186,1056422630206,590031088468],
 [321980417902,171633624986,89350757464,45418351998,22538816308,10918081614,5162375118,2382541782,
 1073370770,472108764,202777612,85079980,34886104,13987186,5487114,2107750,793450,292968,106186,
 37804,13216,4530,1514,486,144,36,4]]
private def pvm_c3_12 : List ℤ := pzigCatZ 28
 [
 [23178970842,183406252554,76242912237,68620062445,240366490428,295408339664,204701167553,
 179550124888,42313941380,452881739483,118899167086,164773759887,18755921525,274938168071,
 45244416748,144577503355,230089392655,56568444490,162755319387,70243438140,185712565841,
 286511770981,435205806461,393320088415,458413210995,567837950283,333600694869,151241289057,
 312013016747,139076777082,240683189236,74129974531,400480663346,279178095500,8388590770,
 204059354713,91023071472,408042892917,108463686742,4875257114,262066316842,102132450367,
 309111248490,207859811911,161287843761,95890688046,440742790015,177740812438,151986883222,
 164842417698,77163567029,110841993172,92707897901,92960185685,58239900336,87381149206,
 35875610089,387739770555,26214735048,297709507614,185380628394,296985791846,73064804941,
 389075533451],
 [366188134033,288113105169,462091004824,203521342224,101803511790,118956960265,178682830369,
 53846870495,313328168258,37862968551,49551948804,159858396467,214840887421,240846109116,
 12474757671,171226199614,170440428903,322744763397,249818794194,22454930564,107977621050,
 146665492140,16450419801,124390445159,209418198447,53279951154,15951189457,306747954775,
 118317863632,17746636516,164243994674,523965699378,148350900761,70297223395,53388174888,
 141584124789,139643567573,99451127836,63768084667,46179810793,180684524080,271629445545,
 69445107062,61350762471,62764126024,146107627255,215318041060,171022373404,403951834084,
 357024903705,415497184704,532529405043,137087032528,428776344749,385073106916,11549320284,
 129127198596,364591388551,15828233598,252775633049,46961387899,344715903509,39428444092,
 201723970512],
 [230126962371,125185256692,94468337413,6327886214,29746245275,161759126029,575700881839,
 343002424878,200445049881,316268156249,43142619451,497997603408,481579603598,233539269797,
 147575220723,506096991322,416726776328,448551888786,45242418125,129820347848,183390065572,
 14641866413,211014694416,863149458703,304115088052,257349415831,373507435506,29434670777,
 470646195246,1407707936845,1428072578892,1451847428587,1602213387796,2711459487587,2623871113270,
 2434001057765,2400017331464,2218057503401,185624013216,759572372254,1384995840281,1379381804792,
 1839023071183,1788198347124,1447873920027,1472946797904,180330502123,799205184355,1281428843712,
 1763635431241,1965614928114,1804602898701,46992042973,549826610192,1241409650101,2075602972710,
 2354709635633,734912812156,469200701714,1234966139165,2286151792076,2228403440843,768775131624,
 737597973358],
 [2106177752017,2288362396868,1450576322013,634482297551,1462484863612,1481285757649,
 1220651440958,710113206347,732343815721,1834391178854,1222840608813,763185115536,380700017012,
 1624149990561,1709089679348,125864472328,659516443645,650145084448,774405395447,596313458646,
 13106179596,561886620715,1138840083872,963585751575,31417440035,1054905016754,1626851065017,
 380812415928,371431298346,1492116995357,1169082970278,531843632095,1159494689547,2150349120486,
 1132973556549,1506266608903,1571196613664,1638045317893,496441439867,1738043591378,2177976996733,
 34008569011,1800411836136,2079779214003,607781026424,1060396516114,3164899856115,1251453345236,
 1973977919746,3620675121795,335774287416,1906566716138,3180456633269,440330074800,1791621080230,
 3428942253769,540873112888,3112427199702,2383290029281,99913276465,2622516650982,1851366939021,
 314515379336,2514318824586],
 [3100366594405,1096744170853,3360106922526,1874555414955,1518069694507,3678918178002,
 1842109999819,3631157521971,4339108476686,1430565836448,5185120003687,965755796510,3496481445322,
 2970741000919,1428692062253,2119183094396,1687084677829,708153293523,2984927817592,1575464489617,
 2833406155419,3156194622126,1273027517594,3240728335083,1392114503366,2374345522158,
 3744394128143,726068969973,5193074334530,773333409935,4856868753179,2165041836922,3190734800856,
 3215442224831,1029163171675,3547432449956,1025314900979,2997586832933,2821615504400,
 2129691441410,3785773464909,1136586154377,3603851164862,198047772413,2883489482267,1192830690730,
 1243573922908,2512980306583,255697733552,3675428005920,1153195378585,3988489064833,1872868832250,
 3598722847262,2589107057055,2825154580075,3230539997456,1688101995306,4267804390639,
 1236384362705,4406130587614,95526406685,5801929101439,456190215683],
 [5428571997402,28325153607,5946351053199,1048484075193,4444041345136,466283017374,3812116209057,
 47131902219,3526350385618,393519466568,1975635920889,1093794622772,2528505225380,787821634223,
 1881193686021,1279469045588,1844672140248,1323291513117,1467535634731,1632496721420,
 1035541498176,2428051819951,811020772123,4328681320222,2868398624748,4323123774521,4488989468121,
 4227649891728,7264773799338,1686442380313,8175612730199,724342348573,8606890300548,3434082705854,
 8779606914613,7645729267371,6466554670890,11437930420114,1642400293367,13209092042959,
 5006869383905,11084397736988,10480361697742,6575223770227,14633200397841,820196500489,
 15512008210168,10470790992542,9711536393213,17063485759149,1138872862259,16325607000534,
 11352637065900,9556304912581,18276092172583,2682841433767,17366463176518,15955257371046,
 5605496468777,20569087154391,10242107206809,13193577477328,21826816448358,5492212319844],
 [16660561701731,18963981707367,1294027909472,21277595644762,18446672740064,4840602001519,
 24336625832387,19860636558087,3991748595744,23160704925530,18590114268076,5308370330119,
 25557407781165,22748838301427,1159195278630,25180405802992,28332692624910,7738203028818,
 19453127951753,30744435615801,16522945481271,12761859759406,35131952476682,33741049714230,
 8934021583342,22423364942479,38851247703477,28583519458543,3081691931410,37396011630476,
 53658869571462,41277610745840,5595778265766,35134670837909,59325263025939,52838258888409,
 15716972443583,37879650275382,85907592500988,107659572057682,92010814899876,41648047528314,
 27833945297097,93097139782965,130299876704299,121894195842459,61015693330003,47438501722964,
 188827523502746,342843359100484,488264969180722,607126398049244,687464488840382,724350510864240,
 719381994913038,679111180332920,612989011037902,531343527578544,443754145944640,357996505560468,
 279568317069506,211693848683494,155650397875828,111255602623986],
 [77382980817152,52416625221200,34599902958490,22268214629166,13978760387662,8561372197084,
 5116632142506,2984195912852,1698543138008,943429643380,511309308806,270360129696,139450926284,
 70153856860,34416412848,16462688714,7677187732,3490000818,1546463166,667925562,281184664,
 115385066,46157414,18002308,6846880,2540042,919376,324768,111992,37700,12378,3956,1220,356,92,18,
 2]]
private abbrev dP_0 : Prop := bSlideChk 13 513 phbv_g3 pvm_c3_10 pvm_c3_11 = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := bSlideChk 13 513 phbv_g3 pvm_c3_11 pvm_c3_12 = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := bSlideChk 13 513 phbv_g3 pvm_c3_12 rkmVoHi64_c64_r512_m2_4_s5_c0 =
  true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := bSlideChk 13 513 phbv_g3 pvm_c3_8 pvm_c3_9 = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := bSlideChk 13 513 phbv_g3 pvm_c3_9 pvm_c3_10 = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := bSlideChk 23 289 phbv_g1 rkmViHi64_c64_r512_m2_4_s3_c0 pvm_c1_1 =
  true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := bSlideChk 23 289 phbv_g1 pvm_c1_1 pvm_c1_2 = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := bSlideChk 22 289 phbv_g1 pvm_c1_2 rkmVoHi64_c64_r512_m2_4_s3_c0 =
  true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := rkmAllTrueF [ bSlideChk 12 513 phbv_g2 rkmViHi64_c64_r512_m2_4_s4_c0
  pvm_c2_1, muxIntListEq rkmHbHi64_c64_r512_m2_4_s2_c0 phbv_g0] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := rkmAllTrueF [ bSlideChk 12 513 phbv_g2 pvm_c2_1 pvm_c2_2,
  muxIntListEq rkmHbHi64_c64_r512_m2_4_s3_c0 phbv_g1] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := rkmAllTrueF [ bSlideChk 12 513 phbv_g2 pvm_c2_2 pvm_c2_3,
  muxIntListEq rkmHbHi64_c64_r512_m2_4_s4_c0 phbv_g2] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := rkmAllTrueF [ bSlideChk 12 513 phbv_g2 pvm_c2_3 pvm_c2_4,
  muxIntListEq rkmHbHi64_c64_r512_m2_4_s5_c0 phbv_g3] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := bSlideChk 12 513 phbv_g2 pvm_c2_4 pvm_c2_5 = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := bSlideChk 12 513 phbv_g2 pvm_c2_5 pvm_c2_6 = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := bSlideChk 12 513 phbv_g2 pvm_c2_6 pvm_c2_7 = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := bSlideChk 12 513 phbv_g2 pvm_c2_7 pvm_c2_8 = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := bSlideChk 12 513 phbv_g2 pvm_c2_8 pvm_c2_9 = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := bSlideChk 12 513 phbv_g3 pvm_c3_2 pvm_c3_3 = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := bSlideChk 12 513 phbv_g3 pvm_c3_4 pvm_c3_5 = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := bSlideChk 12 513 phbv_g3 pvm_c3_6 pvm_c3_7 = true
private theorem bk_19 : dP_19 := by decide +kernel
private abbrev dP_20 : Prop := rkmAllTrueF [ bSlideChk 11 513 phbv_g2 pvm_c2_9
  rkmVoHi64_c64_r512_m2_4_s4_c0, bSlideChk 1 513 phbv_g3 pvm_c3_5 pvm_c3_6] = true
private theorem bk_20 : dP_20 := by decide +kernel
private abbrev dP_21 : Prop := rkmAllTrueF [ bSlideChk 11 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0
  pvm_c3_1, bSlideChk 1 513 phbv_g3 pvm_c3_7 pvm_c3_8] = true
private theorem bk_21 : dP_21 := by decide +kernel
private abbrev dP_22 : Prop := rkmAllTrueF [ bSlideChk 28 129 phbv_g0 rkmViHi64_c64_r512_m2_4_s2_c0
  rkmVoHi64_c64_r512_m2_4_s2_c0, bSlideChk 3 513 phbv_g3 pvm_c3_1 pvm_c3_2, bSlideChk 2 513 phbv_g3
  pvm_c3_3 pvm_c3_4] = true
private theorem bk_22 : dP_22 := by decide +kernel
private theorem pacc_c1_s1 : muxFastIterFullT16 46 289 phbv_g1 rkmViHi64_c64_r512_m2_4_s3_c0 =
    pvm_c1_2 := bCh 46 (bSlideChk_sound bk_5) bk_6 rfl
private theorem pacc_c1_s2 : muxFastIterFullT16 68 289 phbv_g1 rkmViHi64_c64_r512_m2_4_s3_c0 =
    rkmVoHi64_c64_r512_m2_4_s3_c0 := bCh 68 pacc_c1_s1 bk_7 rfl
private theorem pacc_c2_s1 : muxFastIterFullT16 24 513 phbv_g2 rkmViHi64_c64_r512_m2_4_s4_c0 =
    pvm_c2_2 := bCh 24 (bSlideChk_sound (rkmHd bk_8)) (rkmHd bk_9) rfl
private theorem pacc_c2_s2 : muxFastIterFullT16 36 513 phbv_g2 rkmViHi64_c64_r512_m2_4_s4_c0 =
    pvm_c2_3 := bCh 36 pacc_c2_s1 (rkmHd bk_10) rfl
private theorem pacc_c2_s3 : muxFastIterFullT16 48 513 phbv_g2 rkmViHi64_c64_r512_m2_4_s4_c0 =
    pvm_c2_4 := bCh 48 pacc_c2_s2 (rkmHd bk_11) rfl
private theorem pacc_c2_s4 : muxFastIterFullT16 60 513 phbv_g2 rkmViHi64_c64_r512_m2_4_s4_c0 =
    pvm_c2_5 := bCh 60 pacc_c2_s3 bk_12 rfl
private theorem pacc_c2_s5 : muxFastIterFullT16 72 513 phbv_g2 rkmViHi64_c64_r512_m2_4_s4_c0 =
    pvm_c2_6 := bCh 72 pacc_c2_s4 bk_13 rfl
private theorem pacc_c2_s6 : muxFastIterFullT16 84 513 phbv_g2 rkmViHi64_c64_r512_m2_4_s4_c0 =
    pvm_c2_7 := bCh 84 pacc_c2_s5 bk_14 rfl
private theorem pacc_c2_s7 : muxFastIterFullT16 96 513 phbv_g2 rkmViHi64_c64_r512_m2_4_s4_c0 =
    pvm_c2_8 := bCh 96 pacc_c2_s6 bk_15 rfl
private theorem pacc_c2_s8 : muxFastIterFullT16 108 513 phbv_g2 rkmViHi64_c64_r512_m2_4_s4_c0 =
    pvm_c2_9 := bCh 108 pacc_c2_s7 bk_16 rfl
private theorem pacc_c2_s9 : muxFastIterFullT16 119 513 phbv_g2 rkmViHi64_c64_r512_m2_4_s4_c0 =
    rkmVoHi64_c64_r512_m2_4_s4_c0 := bCh 119 pacc_c2_s8 (rkmHd bk_20) rfl
private theorem pacc_c3_s1 : muxFastIterFullT16 14 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    pvm_c3_2 := bCh 14 (bSlideChk_sound (rkmHd bk_21)) (rkmHd (rkmTl bk_22)) rfl
private theorem pacc_c3_s2 : muxFastIterFullT16 26 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    pvm_c3_3 := bCh 26 pacc_c3_s1 bk_17 rfl
private theorem pacc_c3_s3 : muxFastIterFullT16 28 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    pvm_c3_4 := bCh 28 pacc_c3_s2 (rkmHd (rkmTl (rkmTl bk_22))) rfl
private theorem pacc_c3_s4 : muxFastIterFullT16 40 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    pvm_c3_5 := bCh 40 pacc_c3_s3 bk_18 rfl
private theorem pacc_c3_s5 : muxFastIterFullT16 41 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    pvm_c3_6 := bCh 41 pacc_c3_s4 (rkmHd (rkmTl bk_20)) rfl
private theorem pacc_c3_s6 : muxFastIterFullT16 53 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    pvm_c3_7 := bCh 53 pacc_c3_s5 bk_19 rfl
private theorem pacc_c3_s7 : muxFastIterFullT16 54 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    pvm_c3_8 := bCh 54 pacc_c3_s6 (rkmHd (rkmTl bk_21)) rfl
private theorem pacc_c3_s8 : muxFastIterFullT16 67 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    pvm_c3_9 := bCh 67 pacc_c3_s7 bk_3 rfl
private theorem pacc_c3_s9 : muxFastIterFullT16 80 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    pvm_c3_10 := bCh 80 pacc_c3_s8 bk_4 rfl
private theorem pacc_c3_s10 : muxFastIterFullT16 93 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    pvm_c3_11 := bCh 93 pacc_c3_s9 bk_0 rfl
private theorem pacc_c3_s11 : muxFastIterFullT16 106 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    pvm_c3_12 := bCh 106 pacc_c3_s10 bk_1 rfl
private theorem pacc_c3_s12 : muxFastIterFullT16 119 513 phbv_g3 rkmViHi64_c64_r512_m2_4_s5_c0 =
    rkmVoHi64_c64_r512_m2_4_s5_c0 := bCh 119 pacc_c3_s11 bk_2 rfl
/-- Certified `T_16` walk chunk `p49_r512_m2_4_s2_c0`. -/
theorem rkmWalkChkHi64_c64_r512_m2_4_s2_c0 :
    muxFastIterFullT16 28 129 rkmHbHi64_c64_r512_m2_4_s2_c0
      rkmViHi64_c64_r512_m2_4_s2_c0 = rkmVoHi64_c64_r512_m2_4_s2_c0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 28 129 h rkmViHi64_c64_r512_m2_4_s2_c0)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl bk_8)))).trans (bSlideChk_sound (rkmHd bk_22))
/-- Certified `T_16` walk chunk `p49_r512_m2_4_s3_c0`. -/
theorem rkmWalkChkHi64_c64_r512_m2_4_s3_c0 :
    muxFastIterFullT16 68 289 rkmHbHi64_c64_r512_m2_4_s3_c0
      rkmViHi64_c64_r512_m2_4_s3_c0 = rkmVoHi64_c64_r512_m2_4_s3_c0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 68 289 h rkmViHi64_c64_r512_m2_4_s3_c0)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl bk_9)))).trans pacc_c1_s2
/-- Certified `T_16` walk chunk `p49_r512_m2_4_s4_c0`. -/
theorem rkmWalkChkHi64_c64_r512_m2_4_s4_c0 :
    muxFastIterFullT16 119 513 rkmHbHi64_c64_r512_m2_4_s4_c0
      rkmViHi64_c64_r512_m2_4_s4_c0 = rkmVoHi64_c64_r512_m2_4_s4_c0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 119 513 h rkmViHi64_c64_r512_m2_4_s4_c0)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl bk_10)))).trans pacc_c2_s9
/-- Certified `T_16` walk chunk `p49_r512_m2_4_s5_c0`. -/
theorem rkmWalkChkHi64_c64_r512_m2_4_s5_c0 :
    muxFastIterFullT16 119 513 rkmHbHi64_c64_r512_m2_4_s5_c0
      rkmViHi64_c64_r512_m2_4_s5_c0 = rkmVoHi64_c64_r512_m2_4_s5_c0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 119 513 h rkmViHi64_c64_r512_m2_4_s5_c0)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl bk_11)))).trans pacc_c3_s12

/-- Lane witness (`FindAllJohnsonRampKickMuxHi64T22`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi64T22 :
    rkmHbHi64_c64_r512_m2_4_s2_c0 = rkmHbHi64_c64_r512_m2_4_s2_c0 := rfl

end
end QuantumComputation.Specs.DickeSol
