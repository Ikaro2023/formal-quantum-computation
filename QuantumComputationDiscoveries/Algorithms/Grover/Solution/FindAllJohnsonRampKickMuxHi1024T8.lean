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
# High-`m` Checkpointed Walk Part `8` (`FindAllJohnsonRampKickMuxHi1024T8`)

Certifies `1` `T_16` checkpoint walk(s) (`44631` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Quantized generator list for `m1024_r512_s1_c2`. -/
def rkmHbHi_m1024_r512_s1_c2 : List ℤ := altBuildHbFrom 1024 512 51956169884 0 512
/-- Part 0 of `rkmViHi_m1024_r512_s1_c2`. -/
def rkmViHi_m1024_r512_s1_c2_p0 : List ℤ := let p := rkmP; let n := rkmN; [
  n 4024,p 213815,n 1533698,p 6683191,n 21578860,p 55612640,n 118396888,p 211252850,n 315780078,
  p 388216688,n 371466169,p 229217455,p 12774680,n 252134173,p 352386091,n 234763219,n 41394489,
  p 288646276,n 316262771,p 90630293,p 210258082,n 327154960,p 148932668,p 166514713,n 320534371,
  p 158891794,p 160931169,n 312385744,p 134815507,p 184867356,n 299839431,p 81843712,p 225412147,
  n 271757838,p 3296065,p 265419003,n 215551515,n 92405742,p 283729435,n 123955686,n 187193228,
  p 259148093,n 2289935,n 253423296,p 178683904,p 127134035,n 262143851,p 50232620,p 222726921,
  n 188618414,n 107354759,p 267589318,n 86869271,n 160860923,p 94775991,p 252079942,n 493750625,
  p 457671220,n 461650885,p 906442198,n 1764286469,p 2702104545,n 3667575824,p 5087377949,
  n 7378929639,p 10475665306,n 14045282300,p 18050826424,n 22782123325,p 28263782573,n 33882364836,
  p 38762953056,n 42320002268,p 44178620884,n 43670806190,p 39822903619,n 32054711839,
  p 20745193135,n 7011291411,n 7803061799,p 22110918026,n 33734523571,p 40160294868,n 39578039747,
  p 31750480930,n 17977135622,p 618570515,p 17066606472,n 31046624133,p 37450638149,n 34183477494,
  p 21976247757,n 4099302621,n 14684728583,p 29127004784,n 34631663312,p 28942862342,n 13639844490,
  n 6000470869,p 23053101723,n 31578388961,p 28529206729,n 14770813219,n 4719900733,p 22153644679,
  n 30104233596,p 25147730134,n 9582899968,n 9746340086,p 24454020706,n 27962891720,p 18391435712,
  n 9773623,n 18189634453,p 26976992267,n 21957916957,p 5897894595,p 12898355938,n 24761488057,
  p 23340704379,n 9092298431,n 10279129431,p 23682583843,n 23246898176,p 9295460945,p 9878790682,
  n 23034876562,p 22405966254,n 8145061476,n 11319465680,p 23809561278,n 21061051355,p 4633202843,
  p 14747272455,n 24362340031,p 17941243410,p 372511887,n 18609410887,p 24428852019,n 13389279561,
  n 7265067269,p 22983875212,n 22339288729,p 5664292674,p 15086774218,n 25015315899,p 16843766613,
  p 3837641679,n 22055938762,p 23951261571,n 7524658883,n 14943639725,p 26001816501,n 16890911414,
  n 5393564679,p 23571094933,n 23394073367,p 4646580834,p 18189585709,n 26687936633,p 13386675478,
  p 11208591061,n 26700462180,p 19990435299,p 3436528668,n 24068596324,p 24598208176,n 4281881092,
  n 20022336633,p 27418589229,n 10941230931,n 15429934148,p 28372089140,n 16147269522,
  n 10478201504,p 27788075587,n 20295709554,n 5495964912,p 26577859035,n 23611849531,n 1240795480,
  p 25267972341,n 25800705764,p 2013681356,p 23701243112,n 26972072080,p 4697600926,p 22050459370,
  n 27834631141,p 6847906836,p 21019770647,n 28567691098,p 7932461625,p 20707016465,n 28723974022,
  p 8018894808,p 20607180741,n 28451316684,p 7675129912,p 20878527360,n 28293622430,p 6683592001,
  p 22020139068,n 27901761660,p 4512405281,p 23587361957,n 26662970448,p 1576677261,p 24979082419,
  n 24899237098,n 1713865007,p 26524450595,n 22730840872,n 5890932175,p 28146946261,n 19314422291,
  n 10901231870,p 28796227501,n 14518076873,n 15765212456,p 28205870817,n 8981161101,n 20345801978,
  p 26604155302,n 2395497088,n 24652065129,p 23090900200,p 5370022296,n 27353366400,p 17154729519,
  p 12981561597,n 27596910751,p 9662086033,p 19632643687,n 25555250893,p 811491945,p 24996223003,
  n 20415164336,n 9115295355,p 27303815352,n 11833933992,n 17982198581,p 25373838572,n 1444393622,
  n 24154983028,p 19645013609,p 9545548430,n 26790081823,p 9967531312,p 19643266800,n 23950015637,
  n 2578034248,p 25548703511,n 15392877282,n 14533706347,p 25496316484,n 3259750698]
/-- Part 1 of `rkmViHi_m1024_r512_s1_c2`. -/
def rkmViHi_m1024_r512_s1_c2_p1 : List ℤ := let p := rkmP; let n := rkmN; [
  n 23339342374,p 19274436394,p 10484362806,n 26387379876,p 6860361515,p 21893167059,n 21008144331,
  n 8203484374,p 26174597224,n 8672319546,n 20638104010,p 21896940681,p 7005724800,n 26535269230,
  p 9219815552,p 21209153918,n 21965068630,n 8235980939,p 26815723821,n 7557970631,n 22380441379,
  p 20728530538,p 10459072250,n 27063748556,p 4853530174,p 24799254544,n 18675651991,n 14917198912,
  p 26896316190,p 582375895,n 27306613821,p 13982152734,p 20040886194,n 24770487569,n 7309514272,
  p 29044093030,n 7393844980,n 25912010666,p 20317594076,p 16366708472,n 28407911029,n 2854967945,
  p 29964813421,n 11436552407,n 24885740682,p 23367811027,p 14506523701,n 30515654455,n 1145673550,
  p 31602126059,n 12491344463,n 26630669402,p 23889503130,p 16748663493,n 31163041043,n 3904676917,
  p 33295461013,n 9603297038,n 30181191368,p 21585138201,p 22512884750,n 30328939599,n 11575027879,
  p 34819392205,n 1003298091,n 34780550189,p 13503194917,p 30567166725,n 24359337238,n 22969048097,
  p 32371663968,p 13008182250,n 36851833859,n 1788154870,p 37664053312,n 9592965038,n 35139492717,
  p 20103297669,p 29892475919,n 28861266376,n 22619269400,p 35254992227,p 13973560869,
  n 39045037893,n 4560385579,p 40366683056,n 5002981627,n 39593681715,p 14071403896,p 37130882403,
  n 22074833647,n 33279372933,p 28687323012,p 28273537486,n 33907739878,n 22432686341,
  p 37942326218,p 16239626489,n 40965226941,n 10211659244,p 42984429762,p 4656202258,n 43961931001,
  p 425494391,p 44056922328,n 5142460352,n 43680092362,p 9421330363,p 43234142503,n 12977259353,
  n 42819535353,p 15618885103,p 42296163397,n 17497942872,n 41664312783,p 18915306435,
  p 41249709828,n 19886334789,n 41373574712,p 20088036484,p 41938861924,n 19329154692,
  n 42591781135,p 17847480032,p 43284312887,n 15889277142,n 44320769585,p 13189289044,
  p 45698478841,n 9302326479,n 46836294164,p 4337953361,p 47292834779,p 1257314376,n 47217473463,
  n 7589455160,p 46515810537,p 15054177852,n 44284355623,n 23170271493,p 39923173908,p 30956132906,
  n 33751724510,n 38253787586,p 25566336009,p 44799284999,n 14535192130,n 48888106028,p 1341103105,
  p 49329544537,p 12601310030,n 46180345467,n 27098716211,p 38072083201,p 40372860646,
  n 24200514451,n 49077927885,p 6746878404,p 52376092710,p 13523275642,n 47979168057,n 34057452474,
  p 33668837680,p 48783752084,n 12903625795,n 56289451640,n 14191541739,p 50044863994,
  p 39226234007,n 31263037573,n 56776684859,p 1489147149,p 59887910518,p 34734351762,n 36088220295,
  n 45753925058,p 33144639835,p 115465698489,p 130909670829,p 135649520380,p 259378584791,
  p 566389395100,p 1022857221554,p 1617467185993,p 2481521761429,p 3860435806239,p 5982447847046,
  p 8996657483867,p 13056765618806,p 18439812863807,p 25544205830367,p 34754222109740,
  p 46308291120868,p 60290631838381,p 76713477291345,p 95554141894056,p 116670327717564,
  p 139661507227585,p 163810925038169,p 188166783737383,p 211693151287897,p 233374997344519,
  p 252233233624020,p 267309452675854,p 277710307689441,p 282736647584724,p 282033636189555,
  p 275669161176040,p 264098085803535,p 248047531949234,p 228397310313008,p 206107008457447,
  p 182187324327450,p 157676031528439,p 133583163073506,p 110803622057228,p 90027456013626,
  p 71685504221427,p 55950250371823,p 42784657186051,p 32013480823551,p 23389972192073,
  p 16642048837106,p 11496271632338,p 7687251505848,p 4961892393410,p 3084391132505,
  p 1843142237277,p 1057587759193,p 582463953216,p 308058972374,p 156712609225,p 76903078233,
  p 36563881262,p 16939950034,p 7696827104,p 3449626310,p 1530288457,p 671587450,p 290194534,
  p 122467537,p 49988058,p 19539746,p 7246917,p 2528660,p 823515,p 248333,p 68747,p 17299,p 3907,
  p 777,p 130,p 15,p 0,p 0,p 0]
/-- Input orbital vector for `m1024_r512_s1_c2`. -/
def rkmViHi_m1024_r512_s1_c2 : List ℤ :=
  rkmViHi_m1024_r512_s1_c2_p0 ++ (rkmViHi_m1024_r512_s1_c2_p1)
/-- Part 0 of `rkmVoHi_m1024_r512_s1_c2`. -/
def rkmVoHi_m1024_r512_s1_c2_p0 : List ℤ := let p := rkmP; let n := rkmN; [
  n 1035798888,p 4153333166,n 11171826257,p 23028247254,n 37960473989,p 50293281597,n 51792601316,
  p 36324589890,n 5818544239,n 27338802950,p 45040457784,n 35501301898,p 2806055214,p 30972533111,
  n 42499753533,p 21018727964,p 15443101867,n 39863699142,p 29802640249,p 4703248098,n 34469142671,
  p 33483339730,n 1478710849,n 30239435210,p 33540209223,n 5183993857,n 28070128293,p 32499462761,
  n 5482558018,n 26137279824,p 31485264837,n 4257030875,n 26358716387,p 28793264912,n 2105666827,
  n 26527161732,p 26801819810,p 1793630413,n 27267613350,p 22966311763,p 5364923466,n 27728352448,
  p 19461132283,p 10317388617,n 27637484022,p 14142149926,p 14247305190,n 26647879931,p 9129670714,
  p 18737701977,n 24676166009,p 2527864677,p 21661131467,n 21111677841,n 3263612580,p 24008719449,
  n 16837269621,n 9940533885,p 24608032655,n 10651841259,n 15155619925,p 23413635377,n 4542855631,
  n 19896973739,p 20883184608,p 2889243916,n 22918950357,p 15887576787,p 9489406270,n 23809335697,
  p 10284979082,p 15690831529,n 23208622829,p 2949576413,p 20728724429,n 19672396904,n 4488417831,
  p 23359190944,n 14821356571,n 11510479519,p 24493512932,n 8128547154,n 18120217810,p 22640352464,
  n 209987498,n 22390234268,p 18555194831,p 7360043503,n 24890661139,p 12771111135,p 14964420420,
  n 24877879136,p 4874658979,p 20932973895,n 21742683674,n 3293638980,p 24573870578,n 16734549204,
  n 11351466478,p 26170818411,n 9496556903,n 18781944604,p 24485926112,n 811266550,n 23793924171,
  p 20040738985,p 7667516708,n 26471005868,p 13650919745,p 15845723517,n 26470291971,p 5109289908,
  p 22465995319,n 22962502372,n 4076061349,p 26196049906,n 17014871183,n 12621401920,p 27341920936,
  n 9183956554,n 20281374255,p 25343833341,p 294037180,n 25542717102,p 19919799360,p 9601442047,
  n 27514658355,p 12420317316,p 17660243171,n 26628298712,p 3422518174,p 24096017602,n 22439783582,
  n 6470707744,p 27441771076,n 15129724365,n 15324886411,p 27163942965,n 6290494715,n 22162198287,
  p 23915079274,p 3330126769,n 26651128967,p 17557584038,p 12931027596,n 27559055474,p 8625628750,
  p 20582571648,n 24666339866,n 1050643631,p 25389034961,n 18966082112,n 10503052553,p 27255677825,
  n 10740921895,n 18920768506,p 25344890359,n 764688773,n 24524164598,p 19731709596,p 8952751495,
  n 26535082559,p 11815731674,p 17237742783,n 25261149958,p 2369098444,p 23458641918,n 20423530045,
  n 7720211965,p 26190288876,n 12376157737,n 16418381352,p 24842593072,n 2890548895,n 22420965699,
  p 20222214020,p 6757230657,n 25440761657,p 12760032775,p 15697215508,n 24663460157,p 3070674609,
  p 22137019155,n 19791606787,n 6868702417,p 24794715477,n 12119396260,n 15362097493,p 23837851798,
  n 2866542180,n 21683500138,p 19316305453,p 7114944692,n 24625299396,p 11362167074,p 15939742934,
  n 23180879735,p 1615714087,p 21731782899,n 18004806610,n 7997834362,p 24024891827,n 10158981562,
  n 16439415939,p 22532088567,n 340538958,n 22296189280,p 16857605468,p 9724431415,n 23936163755,
  p 8094007667,p 17734783695,n 21273465921,n 1765485740,p 22596650508,n 15144135669,n 11416284249,
  p 23741976741,n 6084435183,n 19385208881,p 20333403700,p 4500293121,n 23585727673,p 12802068648,
  p 14083206366,n 23146450078,p 3049206234,p 20937633027,n 18598187487,n 7335317869,p 24211903801,
  n 10395493087,n 16853565485,p 22775044622,p 406054151,n 23153684891,p 16396705029,p 11240214474,
  n 24597023931,p 6736098117,p 19751573756,n 21300879716,n 4290850125,p 24718599277,n 13732347634,
  n 15070901513,p 24846818856,n 2703816263,n 23122325578,p 19354345863,p 9297463244,n 26123076017,
  p 9556467811,p 19318509237,n 23669217045,n 2278352556,p 25627024826]
/-- Part 1 of `rkmVoHi_m1024_r512_s1_c2`. -/
def rkmVoHi_m1024_r512_s1_c2_p1 : List ℤ := let p := rkmP; let n := rkmN; [
  n 16302317932,n 14236712865,p 26825134151,n 4801811381,n 23735942213,p 21772107135,p 8420868162,
  n 27899975092,p 11442398058,p 19858991632,n 25756695897,n 1518605520,p 27133373271,n 17962740049,
  n 14670316320,p 28738363208,n 5537736422,n 25243514497,p 23418208192,p 9029122972,n 29951473300,
  p 11964687174,p 21691110839,n 27329970333,n 2517316052,p 29349471035,n 18243551620,n 16830881158,
  p 30393528723,n 4272642589,n 27869040593,p 23748513502,p 11722023504,n 32089277252,p 10367890697,
  p 25107896910,n 27792195517,n 5971426180,p 32114474321,n 16306919048,n 21112089184,p 31164699521,
  n 162470992,n 31502683162,p 21774598927,p 17031216878,n 33586272248,p 5605459739,p 29996107428,
  n 25943680391,n 12528474298,p 34559638736,n 10897295852,n 27401206052,p 29628455352,p 7611973927,
  n 35145538140,p 15940050100,p 24900056954,n 32700069802,n 3411213404,p 35162225243,n 19812191000,
  n 22173599556,p 34528811888,n 624744122,n 34268938920,p 23343146582,p 19105933504,n 36186187814,
  p 4463196494,p 33663062672,n 26394270349,n 16861654564,p 37416645714,n 7121842820,n 32920867371,
  p 28264183895,p 14794429923,n 37832201967,p 9486379905,p 31947172245,n 30032571090,n 13057943673,
  p 38601183286,n 11193058209,n 31859298000,p 31146378785,p 12580382925,n 38990784296,
  p 11609165694,p 31762716968,n 31328459378,n 12351530976,p 39095300393,n 11779022624,
  n 32105945085,p 31549198583,p 13133807828,n 39698347543,p 10687517465,p 33392550589,
  n 30628122732,n 15094052090,p 39573306480,n 8520004504,n 34498080245,p 29083021266,p 17370105889,
  n 39525187978,p 5735122137,p 36450120556,n 26882569324,n 21126676766,p 39029744972,n 1143630207,
  n 38322320073,p 22956480372,p 25206252013,n 37302488627,n 4081650288,p 39782094120,n 18279565201,
  n 29854568646,p 34956244321,p 10806981667,n 40999750558,p 11442768547,p 34815927538,
  n 30248985762,n 18455405908,p 40220829868,n 3179019416,n 38698604584,p 23883274352,p 26345987503,
  n 37952939045,n 6772931514,p 41710374799,n 14615554905,n 34367661448,p 32159020230,p 18058934788,
  n 41423600180,p 2884643643,p 40247996068,n 23155822501,n 29132956802,p 37831893231,p 10946830215,
  n 43527644562,p 9907713181,p 39087032629,n 28609189474,n 25701642164,p 41025799344,p 6491328809,
  n 44568607030,p 14300439533,p 38633100429,n 32278962720,n 24585204236,p 43813474946,p 5350912045,
  n 46712159390,p 15258953866,p 40548038142,n 33325514656,n 26612046687,p 45543659740,p 7547142027,
  n 49767686148,p 13227184272,p 45309054873,n 32165093233,n 32965341349,p 46190231266,
  p 14802880519,n 53140362111,p 6251397668,p 52011936137,n 26930099122,n 43005011428,p 44163954277,
  p 27404615716,n 55541884216,n 7346909384,p 59610086863,n 14491242738,n 55966713132,p 35257238763,
  p 45168888342,n 52320533919,n 28528241529,p 63651979114,p 7892456699,n 68090408024,p 14534453650,
  p 65396565714,n 36371838415,n 56076201346,p 55334809406,p 41102806789,n 69614478228,
  n 21755335177,p 78191469918,n 346030377,n 80816401705,p 23227381691,p 77635601053,n 44905648075,
  n 68893206980,p 63998234638,p 55167053202,n 79905990037,n 37796080205,p 92180850392,
  p 18492825723,n 100052629511,p 1772588300,p 103302503916,n 22705892502,n 103097820866,
  p 43100798466,p 100353155700,n 61346341918,n 94396017445,p 78204028357,p 85889647020,
  n 95304381999,n 77120556296,p 115578199606,p 75962208435,n 143375775793,n 128275113755,
  p 90708789876,p 213972201154,p 349462560270,p 487748300346,n 398712149840,n 3386562608750,
  n 7077277253197,n 5863598274754,p 9884873023070,p 51458622186615,p 126281729402043,
  p 230118359653246,p 342566476902307,p 431918578416165,p 468748995368123,p 440224189263795,
  p 356422526218690,p 245308888170720,p 139450801881140,p 61836219019226,p 18537913247133]
/-- Output orbital vector for `m1024_r512_s1_c2`. -/
def rkmVoHi_m1024_r512_s1_c2 : List ℤ :=
  rkmVoHi_m1024_r512_s1_c2_p0 ++ (rkmVoHi_m1024_r512_s1_c2_p1)
end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs
  | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs => match x with
    | Int.ofNat n => match uToNatHb xs with | some ns => some (uConsNat n ns) | none => none
    | Int.negSucc _ => none
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfNatHb ns
private theorem uToNatHb_sound :
    ∀ (hb : List ℤ) (ns : List ℕ), uToNatHb hb = some ns → hb = uOfNatHb ns
  | [], ns, h => by injection h with h'; subst h'; rfl
  | Int.negSucc _ :: _, _, h => by dsimp only [uToNatHb] at h; cases h
  | Int.ofNat n :: xs, ns, h => by
    dsimp only [uToNatHb] at h; revert h; cases hxs : uToNatHb xs with
    | none => intro h; dsimp only at h; cases h
    | some ms =>
      intro h; dsimp only at h; injection h with h'; subst h'
      rw [uConsNat_eq, uOfNatHb, uToNatHb_sound xs ms hxs]
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
private abbrev bCellVal (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCellVal z d b0 c0 b v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCellVal z d b0 c0 b v c1) rest) = rkmUltraAddCons ((v : ℤ) - (z : ℤ))
      (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uConsNat_eq, bDec_cons, ht, bAddCons_eq, bSubTdiv_eq, bMul_eq, bMul_eq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCellVal at hv ⊢; rw [bStepVal_eq z v _ _ d hv, hpq]
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
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs => match bns with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSlide z d rem 0 z [] (bTailN vs) (bTailN cs))
    | b :: bR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal z d b0 c0 b v (bHeadOr z cT)) (bSlide z d rem b c bR vT cT)
      | v :: vT, [] => uConsNat (bCellVal z d b0 c0 b v z) (bSlide z d rem b z bR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal z d b0 c0 b z (bHeadOr z cT)) (bSlide z d rem b c bR [] cT)
      | [], [] => uConsNat (bCellVal z d b0 c0 b z z) (bSlide z d rem b z bR [] [])
private theorem bSlide_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSlide z d rem b0 c0 bns vs cs) = true → bDec z (bSlide z d rem b0 c0 bns vs cs) =
      rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSlide, uOfNatHb, rkmUltraSlideLoopAux] at h ⊢; have hp := bAllPos_uCons h
      have hi := bSlide_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp.2
      rw [bMul0, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi; rw [bHeadOr_eq z vs] at hc; exact hc
    | cons b bR =>
      cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b z bR [] [] hp.2
          rw [bZero_eq z, bDec_nil] at hi; have hc := bCell_hb z d b0 c0 b z z hp.1 hi
          rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_nil, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b c bR [] cT hp.2; rw [bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b z (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT, bZero_eq z] at hc; exact hc
      | cons v vT => cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_cons z v vT, bDec_nil]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b z bR vT [] hp.2; rw [bZero_eq z, bDec_nil] at hi
          have hc := bCell_hb z d b0 c0 b v z hp.1 hi; rw [bZero_eq z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_cons z v vT, bDec_cons z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAllPos_uCons h
          have hi := bSlide_sound z d rem b c bR vT cT hp.2
          have hc := bCell_hb z d b0 c0 b v (bHeadOr z cT) hp.1 hi
          rw [bHeadOr_eq z cT] at hc; exact hc
private def bStg (z dg mL cL : ℕ) (bns vns cns : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlide z d nL 0 z bns vns cns) fun out => cond (bAllPos out) (some out) none
private theorem bStg_sound (z dg mL cL : ℕ) (bns vns cns out : List ℕ)
    (h : bStg z dg mL cL bns vns cns = some out) :
    bDec z out = rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z vns) (bDec z cns) := by
  unfold bStg at h; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq] at h
  revert h
  cases hp : bAllPos (bSlide z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns vns cns) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]
    exact bSlide_sound z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns vns cns hp
private def bBind (z dg mL cL : ℕ) (bns vns cns : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL =>
    match bStg z dg mL cL bns vns cns with | none => none | some out => k nL out
private theorem bBind_sound {z dg mL cL : ℕ} {bns vns cns out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBind z dg mL cL bns vns cns kB = some out)
    (hk : ∀ (mid : List ℕ), kB (rkmNextLen mL cL) mid = some out →
      bDec z out = kU (rkmNextLen mL cL) (bDec z mid)) :
    bDec z out = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z vns) (bDec z cns)) (kU nL)) := by
  unfold bBind at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
  revert h; cases hs : bStg z dg mL cL bns vns cns with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound z dg mL cL bns vns cns mid hs]
    exact hk mid h
private def bStep (z mL c : ℕ) (bns vns : List ℕ) : Option (List ℕ) :=
  bBind z 16 mL c bns vns vns fun l1 c1 => bBind z 15 mL l1 bns vns c1 fun l2 c2 =>
  bBind z 14 mL l2 bns vns c2 fun l3 c3 => bBind z 13 mL l3 bns vns c3 fun l4 c4 =>
  bBind z 12 mL l4 bns vns c4 fun l5 c5 => bBind z 11 mL l5 bns vns c5 fun l6 c6 =>
  bBind z 10 mL l6 bns vns c6 fun l7 c7 => bBind z 9 mL l7 bns vns c7 fun l8 c8 =>
  bBind z 8 mL l8 bns vns c8 fun l9 c9 => bBind z 7 mL l9 bns vns c9 fun la ca =>
  bBind z 6 mL la bns vns ca fun lb cb => bBind z 5 mL lb bns vns cb fun lc cc =>
  bBind z 4 mL lc bns vns cc fun ld cd => bBind z 3 mL ld bns vns cd fun le ce =>
  bBind z 2 mL le bns vns ce fun lf cf => bStg z 1 mL lf bns vns cf
private theorem bStep_sound (z mL cL : ℕ) (bns vns out : List ℕ)
    (h : bStep z mL cL bns vns = some out) :
    bDec z out = rkmUltraHornerT16Step mL cL (uOfNatHb bns) (bDec z vns) := by
  unfold bStep at h; unfold rkmUltraHornerT16Step
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  exact bStg_sound _ _ _ _ _ _ _ _ h
private def bIter (z : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, vns => some vns
  | k + 1, mL, cL, bns, vns => match bStep z mL cL bns vns with
    | none => none
    | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL bns vNext
private theorem bIter_sound (z : ℕ) : ∀ (k mL cL : ℕ) (bns vns out : List ℕ),
    bIter z k mL cL bns vns = some out →
    bDec z out = muxUltraIterFullT16Rkm k mL cL (uOfNatHb bns) (bDec z vns)
  | 0, _, _, _, vns, out, h => by injection h with h'; subst h'; rfl
  | k + 1, mL, cL, bns, vns, out, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL cL bns vns with
    | none => intro h; dsimp only at h; cases h
    | some vNext =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bStep_sound z mL cL bns vns vNext hs]
      exact bIter_sound z k mL (rkmNextLen16 mL cL) bns vNext out h
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  let z := 100000000000000000
  match uToNatHb hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some bns => match bEnc z v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vns => match bIter z k mL cL bns vns with
      | none => muxUltraIterFullT16Rkm k mL cL hb v
      | some out => bDec z out
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; dsimp only; cases hh : uToNatHb hb with
  | none => rfl
  | some bns => dsimp only; cases hv : bEnc 100000000000000000 v with
    | none => rfl
    | some vns => dsimp only; cases hi : bIter 100000000000000000 k mL cL bns vns with
      | none => rfl
      | some out =>
        dsimp only; rw [bIter_sound 100000000000000000 k mL cL bns vns out hi,
          ← uToNatHb_sound hb bns hh, bEnc_sound 100000000000000000 v vns hv]
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
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def phbv_w0_p0 : List ℤ := pzig
  [150481141962574,212500709419118,259877262180416,299639371440446,334513819156584,
   365901185313012,394634715507950,421258113470862,446149588146194,469584910686652,
   491772566677252,512874761637600,533020673948634,552315190519336,570844876246314,
   588682178410406,605888465106450,622516270306518,638610985081270,654212153438034,
   669354480273052,684068626001646,698381840619542,712318475185266,725900398522924,
   739147339784264,752077172396616,764706151218970,777049112008282,789119640275710,
   800930215091634,812492332242612,823816610256420,834912882124434,845790275014130,
   856457279842028,866921812242432,877191266199654,887272561396292,897172185156026,
   906896229717738,916450425461818,925840170614194,935070557874726,944146398351138,
   953072243125004,961852402730502,970490964788108,978991810002842,987358626709110,
   995594924120602,1003704044423778,1011689173836170,1019553352736030,1027299484957104,
   1034930346331316,1042448592552576,1049856766426674,1057157304564994,1064352543573412,
   1071444725782274,1078436004558496,1085328449236496,1092124049700972,1098824720651180,
   1105432305573412,1111948580445814,1118375257197270,1124713986940116,1130966362994522,
   1137133923720784,1143218155174252,1149220493596344,1155142327753868,1160985001137828,
   1166749814031930,1172438025460124,1178050855021742,1183589484622098,1189055060105732,
   1194448692798974,1199771460967870,1205024411197148,1210208559695366,1215324893531048,
   1220374371804238,1225357926757530,1230276464830412,1235130867660380,1239921993034118,
   1244650675791744,1249317728686946,1253923943205598,1258470090345308,1262956921358146,
   1267385168458676,1271755545499228,1276068748614306,1280325456835772,1284526332680482,
   1288672022711824,1292763158076594,1296800355018494,1300784215369542,1304715327020468,
   1308594264371276,1312421588762910,1316197848891036,1319923581202818,1323599310277546,
   1327225549191898,1330802799870624,1334331553423298,1337812290467894,1341245481441722,
   1344631586900390,1347971057805330,1351264335800400,1354511853478096,1357714034635836,
   1360871294522758,1363984040077458,1367052670157094,1370077575758204,1373059140229626,
   1375997739477852,1378893742165134,1381747509900684]
private def phbv_w0_p1 : List ℤ := pzig
  [1384559397425208,1387329752789112,1390058917524598,1392747226811928,1395395009640088,
   1398002588962076,1400570281845052,1403098399615518,1405587247999762,1408037127259742,
   1410448332324578,1412821152917832,1415155873680748,1417452774291586,1419712129581218,
   1421934209645112,1424119279951860,1426267601448346,1428379430661718,1430455019798256,
   1432494616839238,1434498465633960,1436466805989952,1438399873760548,1440297900929844,
   1442161115695202,1443989742547324,1445784002348024,1447544112405756,1449270286548980,
   1450962735197442,1452621665431430,1454247281059096,1455839782681872,1457399367758078,
   1458926230664764,1460420562757842,1461882552430578,1463312385170478,1464710243614628,
   1466076307603550,1467410754233596,1468713757907936,1469985490386206,1471226120832814,
   1472435815863974,1473614739593520,1474763053677496,1475880917357584,1476968487503422,
   1478025918653798,1479053363056794,1480050970708902,1481018889393124,1481957264716102,
   1482866240144306,1483745957039302,1484596554692116,1485418170356744,1486210939282808,
   1486974994747392,1487710468086092,1488417488723258,1489096184201524,1489746680210558,
   1490369100615132,1490963567482474,1491530201108942,1492069120046048,1492580441125830,
   1493064279485592,1493520748592040,1493949960264820,1494352024699470,1494727050489806,
   1495075144649756,1495396412634654,1495690958362006,1495958884231734,1496200291145934,
   1496415278528126,1496603944342034,1496766385109892,1496902695930300,1497012970495616,
   1497097301108934,1497155778700604,1497188492844360,1497195531773026,1497176982393806,
   1497132930303214,1497063459801586,1496968653907230,1496848594370204,1496703361685736,
   1496533035107274,1496337692659200,1496117411149194,1495872266180274,1495602332162486,
   1495307682324284,1494988388723592,1494644522258544,1494276152677922,1493883348591290,
   1493466177478838,1493024705700906,1492558998507260,1492069120046048,1491555133372496,
   1491017100457318,1490455082194856,1489869138410960,1489259327870590,1488625708285156,
   1487968336319620,1487287267599310,1486582556716512,1485854257236794,1485102421705086,
   1484327101651522,1483528347597032,1482706209058698,1481860734554868,1480991971610040,
   1480099966759514,1479184765553794,1478246412562780]
private def phbv_w0_p2 : List ℤ := pzig
  [1477284951379724,1476300424624950,1475292873949358,1474262340037698,1473208862611614,
   1472132480432476,1471033231303974,1469911152074510,1468766278639338,1467598645942520,
   1466408287978624,1465195237794226,1463959527489178,1462701188217662,1461420250189020,
   1460116742668356,1458790693976924,1457442131492298,1456071081648294,1454677569934700,
   1453261620896760,1451823258134430,1450362504301422,1448879381104006,1447373909299582,
   1445846108695030,1444295998144818,1442723595548870,1441128917850210,1439511981032354,
   1437872800116466,1436211389158272,1434527761244714,1432821928490372,1431093902033616,
   1429343692032522,1427571307660508,1425776757101722,1423960047546154,1422121185184496,
   1420260175202704,1418377021776300,1416471728064388,1414544296203384,1412594727300448,
   1410623021426630,1408629177609714,1406613193826748,1404575066996268,1402514792970210,
   1400432366525484,1398327781355230,1396201030059738,1394052104137020,1391880993973036,
   1389687688831558,1387472176843678,1385234444996930,1382974479124050,1380692263891336,
   1378387782786602,1376061018106744,1373711950944880,1371340561177052,1368946827448524,
   1366530727159594,1364092236450974,1361631330188700,1359147981948540,1356642163999936,
   1354113847289420,1351563001423520,1348989594651124,1346393593845310,1343774964484606,
   1341133670633662,1338469674923356,1335782938530254,1333073421155478,1330341081002900,
   1327585874756692,1324807757558178,1322006682982000,1319182603011536,1316335468013600,
   1313465226712352,1310571826162424,1307655211721238,1304715327020468,1301752113936648,
   1298765512560874,1295755461167594,1292721896182442,1289664752149078,1286583961695026,
   1283479455496462,1280351162241906,1277199008594814,1274022919154992,1270822816418824,
   1267598620738266,1264350250278556,1261077620974588,1257780646485938,1254459238150448,
   1251113304936352,1247742753392882,1244347487599284,1240927409112214,1237482416911420,
   1234012407343694,1230517274064968,1226996907980544,1223451197183348,1219880026890156,
   1216283279375688,1212660833904518,1209012566660696,1205338350674990,1201638055749676,
   1197911548380732,1194158691677402,1190379345278944,1186573365268510,1182740604084004,
   1178880910425810,1174994129161248,1171080101225624]
private def phbv_w0_p3 : List ℤ := pzig
  [1167138663519730,1163169648803648,1159172885586674,1155148198013230,1151095405744554,
   1147014323835990,1142904762609704,1138766527522582,1134599419029110,1130403232439026,
   1126177757769456,1121922779591314,1117638076869682,1113323422797890,1108978584624984,
   1104603323476264,1100197394166578,1095760545005966,1091292517597334,1086793046625704,
   1082261859638650,1077698676817458,1073103210738530,1068475166124518,1063814239584670,
   1059120119343790,1054392484959224,1049631007025202,1044835346863872,1040005156202264,
   1035140076834420,1030239740267842,1025303767353376,1020331767897570,1015323340256492,
   1010278070909918,1005195534014734,1000075290936278,994916889756322,989719864756234,
   984483735873766,979208008131876,973892171037718,968535697949978,963138045412416,
   957698652451460,952216939835408,946692309292698,941124142686404,935511801141990,
   929854624125004,924151928465216,918403007323304,912607129095958,906763536254850,
   900871444114516,894930039523798,888938479474970,882895889624120,876801362715830,
   870653956904446,864452693963554,858196557374448,851884490283442,845515393316882,
   839088122241584,832601485457108,826054241304898,819445095177692,812772696410790,
   806035634934746,799232437666756,792361564615364,785421404670212,778410271045158,
   771326396339250,764167927175698,756932918373954,749619326604246,742225003467318,
   734747687934486,727184998074232,719534421981388,711793307812924,703958852820482,
   696028091253414,687997880986904,679864888707096,671625573458296,663276168325434,
   654812659986924,646230765827360,637525908244558,628693185718940,619727340132376,
   610622719724698,601373236954664,591972320381758,582412859498372,572687141207688,
   562786776347352,552702614283738,542424643121168,531941872449586,521242194745204,
   510312220473496,499137080527114,487700187725008,475982946502082,463964396333494,
   451620769414442,438924935964630,425845700162480,412346894397224,398386196390666,
   383913557927070,368869076939796,353180051118112,336756791858654,319486494447608,
   301223932430418,281776698846422,260880491629466,238154750772610,213015328949748,
   184478793403010,150627451036432,106510097573240]
private def phbv_w0 : List ℤ := phbv_w0_p0 ++ (phbv_w0_p1 ++ (phbv_w0_p2 ++ phbv_w0_p3))
private def pvm_w0_1_p0 : List ℤ := pzig
  [975893,6869204,29066859,89150792,213083875,409481638,636972403,787162596,720469513,364995856,
   176792086,620705881,661884998,229537769,380462351,678836348,391094745,248506421,652060592,
   420210561,230726813,639106532,369557335,296377231,628875016,251160419,409565731,586214930,
   68411483,524792561,472927926,159946240,585018117,267514198,385929588,533575421,13836053,
   534926874,340840633,304506009,529741258,32394385,503617539,343278690,280183304,484372695,
   28998387,556614780,400322001,119982249,102052706,671122274,1471430863,1769933220,2124405369,
   3504956902,6051360567,9110214690,12496521547,17070525798,23719899183,32226940704,41666419927,
   51636135010,62335037097,73280587540,82600913271,88030812340,88201812939,82481762962,
   70015338779,49967552464,23092252941,7457560979,37214419608,61886125455,77583436114,
   80591139105,68514644736,42403928205,7453046154,28655845718,57989123293,73601274828,
   70635287155,48478482240,12622443991,26322033031,56486091448,68774345585,59197365900,
   30081598491,9436962437,45274645806,63702589793,57618235912,29660814181,9219260941,43899408030,
   60215933271,50637829228,18750740777,21075455845,50318591804,55576856775,34791729114,
   2187311658,37810749537,54340864908,42776066625,8796408466,29322834724,50875984467,44454154644,
   13875652965,24119694563,48396290502,44652878919,14405035230,24475414454,48142242663,
   42036265772,10173940905,27675871949,48127556300,38096488425,3265755112,34144685804]
private def pvm_w0_1_p1 : List ℤ := pzig
  [49013922863,30767317096,8379526676,41642444519,46324950748,19161787565,21530570137,
   47623318492,40055092497,3217115574,36508368318,49549607129,25844654398,17098991896,
   47378534899,42354673580,5264966657,36488007087,50775337232,25453493057,20473741243,
   50582245454,40413974427,2150501969,43118720194,49616147321,15953878920,31305221624,
   53510364333,31277321954,17804818154,52339491185,42420771796,3823435704,46898661815,
   49875228420,9855164873,39194876181,54584252958,21800283351,31045230687,56568168250,
   31045555453,22773334435,55950739228,38224767217,14423679021,54138527918,44182345423,
   7134479831,52438168612,48495316165,1824551077,50630622294,50826696525,2150913096,48477633304,
   52266952055,5343157192,47104561240,53588529749,6833483490,47184284476,53950680671,6162324138,
   47756003976,52982549005,4396361096,48462578666,51719774941,1756122300,50308855806,50100847145,
   2914013419,53018169178,46692410325,9373893707,55028156582,41539792511,16287968073,56348706482,
   35497775299,24030097963,57451696170,27515075061,33089299725,56673358804,16703422015,
   41644172495,52702315908,4486365203,48395025575,46297294656,8514867062,53677261681,36924991056,
   22848185626,55872929191,23204532704,36471725284,52637344761,6690768756,46668628460,
   44441217675,10632420613,52992535038,31513333891,28346668837,53640498386,13034043427,
   43391233451,45874343612,8191461626,51561299125,30815168094,28064977060,51839030071,
   10475020114,44355009736,42845118703,13618986015,52506291660,23533916077,35563516435,
   48238063400,1493914652,49003377293,32684892420]
private def pvm_w0_1_p2 : List ℤ := pzig
  [26470591854,51092570249,8037780636,46094330008,38610458449,20883097971,52115213372,
   12925513675,43494234593,40936552284,17085265652,52065418019,15983158726,42582386494,
   42725932215,16848230587,53346759788,15050813647,44515359769,41454956878,19958920832,
   53341879231,11449456506,47142493652,39099740971,25423452251,54219793042,4478753911,
   52455356027,33149417666,34800391428,52100611157,6833872893,56151673014,23273195561,
   44586995761,47241138538,20942422836,58902992121,8321414554,55609346428,35741970353,
   38571435523,54787820690,12211332926,61315581929,17176198032,54271389870,43031208971,
   35594792405,59994925192,9482123342,64926895073,18715460512,57317326236,43659099911,
   39097388493,61006640776,13980041384,68062691673,13456046350,64045343114,38704998615,
   50000726015,58093759104,28442153620,69239502021,2807041453,71178406228,23172058239,
   64230109777,46082396428,49715062684,63327543409,29639436087,73410623828,6410374020,
   75952159363,17423116566,71469637486,39444240837,61033759717,57671630082,45960235950,
   70831894861,27652552761,78482893970,7589524092,80896308411,12670750576,78735778278,
   31617837577,72714807097,48067957680,63452825548,61430613883,51596265937,71729113242,
   38026724128,79301589861,23864526221,84401048716,10152504144,87054260773,2542439984,
   87321649110,14201998905,85669017047,24967820860,82973418726,34668739311,80044387889,
   42814501076,77144111798,49114372425,74105383215,53890436440,70974630816,57769129245,
   68369029501,60931422916,66985591962,62910192563,66846302181,63309486146,67392622262,
   62466772029,68431456605]
private def pvm_w0_1_p3 : List ℤ := pzig
  [60966042754,70534065738,58594289175,74101855579,54437920028,78474073118,48175670127,
   82695879125,40420606732,86805132860,31279716947,91173009049,19696966984,94780272002,
   5230233553,95857714513,10924615561,94050623228,28046626060,89489214619,46729159115,
   80333272910,65795708272,64877341527,82044782023,44302704442,94243193686,19164698105,
   101370251711,11372747387,98962563410,43615519842,85126806213,72664447837,61324006058,
   96755829708,25564003651,108534764767,18106533263,102161087650,60752089424,78930066633,
   98799997541,33835967928,116064057146,20960101408,109282593585,78185415999,70738975728,
   118639748664,6038546275,121899446647,54798003915,116142991986,177701145224,95759504632,
   86579178994,357580604418,885706128510,1543382087380,2410965902752,3874736720228,6403649823684,
   10316714111738,15851622835994,23447355913670,33878236735964,48057192095112,66715316064764,
   90283726402730,119031554422204,153198785211292,192873951470380,237670655213424,
   286494401048624,337608304002036,388918203061746,438223434111180,483282617228194,
   521784375466850,551429872411066,570221732269290,576843172594752,570910194857932,
   552968581409824,524286648379632,486603688751236,441960075394758,392616151020708,
   340976859852442,289443324850158,240188589468672,194929703936348,154785869083884,
   120269435019322,91392022837028,67825201661218,49052469754758,34476361262524,23477590545570,
   15443524665946,9785980491856,5959653202292,3482004482216,1949578338076,1045652992780,
   537502168700,265202472566,125938053208,57788273548,25751225740,11203544134,4780236196,
   2004310710,824556628,331034466,128613566,47876240,16897986,5596992,1722124,487106,125208,
   28844,5846,1004,134,8]
private def pvm_w0_1_p4 : List ℤ := pzig
  [0]
private def pvm_w0_1 : List ℤ :=
  pvm_w0_1_p0 ++ (pvm_w0_1_p1 ++ (pvm_w0_1_p2 ++ (pvm_w0_1_p3 ++ pvm_w0_1_p4)))
private def pvm_w0_2_p0 : List ℤ := pzig
  [8959625,44979858,142452793,328931894,579644767,778563224,748758197,382868148,202107516,
   653178515,615586506,75129791,530015409,641925080,129461457,511104723,611760204,50636531,
   561915845,529686434,117901256,618813605,367149476,332115938,609007949,112768512,521393050,
   471213117,196132509,594168552,190962709,464508279,476557746,167418816,569551563,169645016,
   461894152,425900745,222483969,549766200,94462313,456010717,264349660,433513170,694411479,
   299140382,120972311,873338302,2124155717,3083718006,3983424027,5942174068,9518306519,
   14166823332,19419470643,25908778336,34565761183,45152311578,56325703371,67023360976,
   76891161015,85054334978,89272281173,87044006046,77254999115,60216310282,36607258949,
   7559248760,23938148758,52649660083,72900850108,80696019043,74178466732,53335261419,
   20809349036,16917930260,50483551639,70991347404,73082499223,55930246048,23268276193,
   16415617871,50978774086,68648821501,63216943378,36680030081,1887180513,39360249716,
   62164211277,60929128022,35373234789,4162035087,40962104094,59642757289,52586913916,
   22725715765,17173814323,48901977548,56962869783,37139884918,506922138,36921514023,54009164908,
   43339347611,10164679444,28368450870,51212081787,45200600172,13646972071,25088243905,
   48646160750,43699080603,13197212392,25156043392,48314408825,41469886020,8348221091,
   29967253899,48642799738,35723496779,222765171,35913567952,47977996661,27836791504,11675538824,
   43528354443,44976338724,14588795927]
private def pvm_w0_2_p1 : List ℤ := pzig
  [26081680277,48088617342,35786861749,2311877435,39193446874,47766716501,20710911630,
   22498219298,49021835135,38090167102,2148394102,40785077461,48082978760,18105734525,
   26486644383,50867453702,34835913561,9803154701,47052431638,45953791219,7004061848,37820321228,
   51573363765,22657895892,25522387930,52938622785,35687238454,12650000042,50736284987,
   44918866640,263802690,45343638229,50736401750,11541326513,38125566207,54408963248,22028396361,
   30872238211,56304652256,30154297851,24084078195,56178853860,36190639671,17387310743,
   54862158130,41210231603,11379213395,53770747924,45155175557,7187513199,52989430636,
   47316353697,4576308701,51870767208,48264689801,2666773771,51034763896,49042366669,1974880873,
   51471875478,49132687861,3386610847,52537728568,47649188613,6176936135,53316328234,45276477395,
   9548522279,54480627862,42538189977,14371372979,56337699476,38200323847,20991897301,
   57388941990,31678420089,27983334651,56912345816,24029706753,34868020371,55609928686,
   15103557993,42343844609,52630683076,3775813357,49195494787,46265361000,8912825990,53428926065,
   37013472086,21320880974,55102338899,25565919074,33633411172,53802672917,10904617314,
   44790161232,47324691161,6107082867,51741970568,35629231515,22557126249,53504982382,
   20371197683,37304466457,49900164716,1602303297,48745546157,38938918666,18917526132,
   52901048105,21112118008,36458600010,48315666395,9866977,48252416396,35826106841,22111012195,
   52099642694,15296910663,41231032173,44349592826,9839586006,50863956353,25791019816,
   32531834344,48410231715,1033904146]
private def pvm_w0_2_p2 : List ℤ := pzig
  [47972851776,33798344867,25584581535,51090147116,7976212435,45911744585,37774299704,
   21254276596,51373439331,12009553854,43721626252,40193630569,18538128149,52414612172,
   13869239863,44513783687,41045897260,20039094382,53143331507,11678723440,46227221166,
   39285658591,23169561059,53455627144,7864247795,49829896553,36517563098,30026074786,
   53723782027,646856653,54420265448,29141380667,38760706421,50538926812,11657410814,57620402763,
   18996800714,48755634402,44750842679,26692566423,58908418474,2537970849,58124611481,
   31442675618,42964417974,53041127677,17422382869,62481107708,12333448639,57956722609,
   39579915868,40820313954,58585469257,14988161811,65739767306,14118331913,60075640439,
   40798974826,43164690170,60194459505,18512793769,69100308972,9329191379,66372228527,
   35702492030,52911671762,56627529935,31293164515,69323129576,5145001212,72430910599,
   21576192430,65990641798,45268729473,51246391557,63196074858,30356080800,73740517121,
   6045820503,76390658126,18775293281,71533624389,41419913510,60176232780,59791456099,
   43713719121,72625746686,23795345672,79520597293,2241115893,80742950188,19089581151,
   76916409331,38536389808,68765580220,54923752765,57051691211,67730345858,42677707752,
   77000501431,26780588091,83028105704,10615731674,86042921747,4772801350,86158566958,
   18854790645,83615848617,31595418122,79043635698,43086323143,73387109311,53168511534,
   67473263846,61459187801,61622911383,67786851706,55763052714,72528244055,49969232103,
   76361193742,44801925386,79624243591,40953409851,82058110946,38585332322,83332917069,
   37265151815]
private def pvm_w0_2_p3 : List ℤ := pzig
  [83707637940,36713553038,83832634653,37371980087,83833579408,39861863572,83012939515,
   44016314159,80780103766,49046508200,77431992645,54760368173,73342854198,61779258626,
   67754429983,70073390641,59473782272,78306121340,48552681499,85493921665,35688086484,
   91891486460,20212237197,96840960169,1144993326,97872416114,20171853892,93719475993,
   41821415795,84752825788,63795970780,69257940927,84301070151,45423257010,98560014840,
   15775047413,104714372627,17820900001,101186450990,54469647570,82767968663,86394416559,
   50795792610,107785173086,8689181521,115088676095,42322665187,97787143462,87078539268,
   60420830727,119633076297,1955184142,123534423878,62112872820,94265806865,115227798987,
   35694829410,149497689538,76582406824,49602457549,18565621818,329275555940,718155435254,
   1120858181614,1797557884492,3188593763930,5620704497068,9273420663856,14462350419590,
   21880799807922,32492600835674,47195692519288,66629120068114,91280379718722,121658901253356,
   158214432634922,200980762221432,249245117538354,301523015491852,355809390915644,
   409838341634416,461157561818842,507092732767608,544835522138728,571780395483862,
   585990785572578,586542559548998,573583043219596,548149604054032,511922192407010,
   467048781525290,416048532921248,361699160567342,306827687711910,254016051622566,
   205316328144580,162081261834866,124957367703996,94010742777010,68910413678864,49097534326500,
   33903934176722,22620905216760,14538713860996,8976692620726,5312486584596,3008360465522,
   1628356589576,842189909998,416417999214,197126713026,89568317872,39200338452,16594790682,
   6822854882,2731873470,1065357478,403261062,147136154,51248610,16846304,5161418,1454292,371232,
   84316,16628,2730,340]
private def pvm_w0_2_p4 : List ℤ := pzig
  [20]
private def pvm_w0_2 : List ℤ :=
  pvm_w0_2_p0 ++ (pvm_w0_2_p1 ++ (pvm_w0_2_p2 ++ (pvm_w0_2_p3 ++ pvm_w0_2_p4)))
private def pvm_w0_3_p0 : List ℤ := pzig
  [46774953,178863470,425011477,705007528,809818299,536303660,70318082,618078159,637291644,
   66116663,566584165,602373264,20108982,614646065,485298932,225702108,651924499,254926232,
   463744910,570610573,77590957,613655698,310240817,414945341,554377042,85243852,595097289,
   247981122,450905498,484931863,190718657,576029152,103533995,512215341,342143332,356739106,
   533213071,48306155,436701482,55394354,815380123,930512902,681221351,1194944442,2806899149,
   4725442436,6543593497,9191217504,13791305745,20222547836,27646365315,36062032820,46258454173,
   58116016916,69906426197,79646423956,86275217633,88843756654,85346792341,73589643408,
   53242746811,26309270656,4227392020,35068970155,61714637082,78361979679,80182773482,
   65923174689,38208278728,2263477453,34646738567,63423513050,75340695773,66053441836,
   38031109877,524764585,38467806650,64179845229,68479341758,48734573553,11609408554,28919381892,
   57571389409,63724752246,44859596715,7824747878,32385415540,58056479611,57363253130,
   30827202555,8998431957,43781165538,57453990331,43160518878,7328758597,31980691727,53966176796,
   46955075539,15164669112,24010987308,49514519259,47377834654,18331501153,21352379525,
   48176371750,45763244297,15717459328,23304857326,47465663141,42114784570,10371701533,
   28152507179,48573861010,36875677075,459951976,36044860958,47836904745,27095667474,12030967784,
   42976623553,44169511824,13974286405,26738869563,48362890360,34535119951,4779126261,
   40481163470,46183596959]
private def pvm_w0_3_p1 : List ℤ := pzig
  [17559903546,24503244628,48580300935,35673181896,5304054998,42716109189,46654950504,
   13560249095,30374479129,50224706812,30072350783,14459314489,47925676790,42633321845,
   1801761408,41232988706,50012571425,16533967620,31076109122,52459433569,29375674782,
   18936567132,51552879501,39945837384,6902550710,48445844749,47390589174,3909025507,43300138207,
   51762762014,13764700875,36737924223,54357438538,22656364759,30309864841,55972775022,
   29667703019,24824443147,56252615468,34596516795,19769979495,55379993836,38489002875,
   15131161569,54646073344,41751418361,11996298105,54548593678,43570518771,10635223055,
   54293881010,43903082241,10085323379,53877368762,43821061263,10307903453,54349799534,
   43300252333,12341170477,55552275626,41209672179,15975253791,56259885868,37686435897,
   20061672871,56577477360,33630603771,24902426167,57196284190,28333433573,31237084015,
   57042059006,20763597871,37929953397,54818131148,11788224251,43756585687,51054059892,
   2134582231,49195872519,45786845460,9083621224,53804188251,37434177360,21440246148,55442574233,
   25957363694,32792632106,53558462805,12843841792,42538830466,48646869719,2002557035,
   50438350162,39356930615,18361668999,53953711894,25093803543,33291059227,51413315016,
   8086990633,44623197087,43546513678,10213303996,51684808847,29916923482,28766754924,
   51796078023,10515281446,43478827514,42990796889,10848335359,50725541882,27116786471,
   30438307739,49721354308,5948807827,45664368673,38815478570,18107398176,51519716437,
   18127980324,38464121796,44845664949,6912246387,49522587482,27525878731,30731164125]
private def pvm_w0_3_p2 : List ℤ := pzig
  [48822541868,2111966047,47821799527,33838986164,25724864494,50614053417,7260782300,45719157164,
   36927703885,21787096499,51206321770,10985541065,44823797881,39438161254,20838945086,
   52731997199,11151044932,46242490306,39058069635,22793407447,52859313246,8891425977,
   47982749061,37644361802,26487404912,53810100313,4100374840,52322908776,33634455205,
   34006948031,52764475414,4896646706,55778006921,25977452830,42064189094,49484865535,
   15923907517,59037281852,15019869771,52248007561,42188432192,31265094942,58436480767,
   1853540379,59813160758,28370069127,46309508359,51984140756,21532052498,63538593403,8471668848,
   60664431508,36831616591,44345521413,57469211888,18407554126,66333278625,11550662448,
   62037137336,39472501557,45853021855,60093744128,21172838018,69881779589,7359662966,
   67521171896,34812628553,53915440575,56825534354,31774077262,70233760129,4925102167,
   73406356078,22471241495,66308227179,46636000632,50333359812,64681939751,27965995699,
   74860171862,2325996966,76561466591,23340991440,70153510658,46152713421,56757347047,
   63967812826,38038121794,75568828319,16023974447,80617255436,7087256347,79430299169,
   29178486134,72704706276,48508603835,61326643087,63958497750,46330798770,75101028443,
   28943854953,82037933428,10561857046,85095048941,7445222912,84583321768,24043115813,
   80795416287,38742809780,74205461584,51515821937,65628300859,62452756586,56093094258,
   71461689117,46455615917,78309183450,37087135892,82977113981,27980255073,85932448324,
   19206860748,87928519283,11232126149,89462965890,4674662250,90491872757,255695464]
private def pvm_w0_3_p3 : List ℤ := pzig
  [90795607238,3924063465,90591703375,6718120116,90559180106,8419658001,91121150883,8401011582,
   91924226824,6484216447,92359934409,3211091282,92476955004,1042393658,92814445065,6815476681,
   93210185824,14785246798,92525016329,24534413583,90013685248,35103670612,86018196209,
   46578603633,80394191096,59523532198,71536350473,72836376063,58470136694,84446291536,
   42079708649,93883281629,22423730536,100721048322,1741319262,101828316801,28835578547,
   94904310652,55469124802,80580358061,80801044151,57137275578,101630689544,23339453485,
   111171029847,15587363761,107959923412,56749214542,89055823485,95294107275,50459091926,
   118253558126,957799269,123277455301,57491953249,98695434538,107140329242,48455809645,
   136453638633,22943626805,128930779556,98746447872,66318044841,110607366317,79773219240,
   342298252092,514485113476,744607283396,1426771205684,2877461978710,5219525348862,
   8651784633432,13767433325458,21522661854728,32901567156292,48680480454336,69523829703740,
   96192094445428,129483179788132,169838536846700,216931977948384,269574815556490,
   325932242206680,383762272493832,440461244005028,493006136870386,538063672269672,
   572403624547170,593467041483648,599793634165694,591128175600946,568264040431004,
   532817880310988,487071939917786,433865863703656,376426982000632,318068330222322,
   261800319196092,209986014933318,164159242071756,125040608775708,92697350677394,66753096564902,
   46571253940330,31381679255834,20359387614828,12678539706508,7558376028436,4304170947156,
   2337454808650,1209354303970,595922177282,279809452800,125359328766,53706573682,22065540012,
   8720004818,3321970178,1220285864,431014624,145435214,46409562,13821136,3779660,930672,201176,
   36790,5328]
private def pvm_w0_3_p4 : List ℤ := pzig
  [512]
private def pvm_w0_3 : List ℤ :=
  pvm_w0_3_p0 ++ (pvm_w0_3_p1 ++ (pvm_w0_3_p2 ++ (pvm_w0_3_p3 ++ pvm_w0_3_p4)))
private def pvm_w0_4_p0 : List ℤ := pzig
  [163462345,465875554,774224701,770558606,270889221,435051115,711137890,239155985,493631969,
   635124156,5124876,631483847,426343730,346126836,637513017,40755086,605980214,378635767,
   393406443,579585098,93251098,617521617,205269014,512265612,436707179,309238267,564610392,
   64417592,585103217,181222110,492362404,349991917,393174283,578397220,9932432,273200677,
   451575503,1377548488,1662578409,1935731940,3450030941,6271273078,9509879587,13195487094,
   18630624303,26574760888,36217385757,46537251840,57597877221,69445706674,80388871549,
   87577099134,89028235741,83977025236,71505456647,50511126358,21791773047,10773547911,
   41774743220,66247535395,79755108014,78189973325,59723386434,27395009465,11092795667,
   46309109678,69601705209,74251673864,57385954999,22816258006,18603421978,53007304895,
   69056562238,61380817035,31949133046,9417108774,46944545571,65082617254,56227859849,
   24446035482,16805162252,50266470197,61229545730,43978052397,6022403008,34179541944,
   56653431597,50608121520,19543618445,20916740435,50185607560,52486947917,25964018034,
   14740612922,46311577165,50809872564,26183832735,13105855423,44331045738,48891579947,
   23442993172,16641515950,45883570761,45413428690,15819973339,23477751747,47119239210,
   39750713629,5807528374,32360436882,48426358381,30621167014,8757882476,41683178529,44796423630,
   16038392501,24210194811,47210189732,35796373969,2515091101,39458956722,46660992729,
   18145167036,24292920634,48019496691,34806933698,5421570536,41881978619]
private def pvm_w0_4_p1 : List ℤ := pzig
  [45812322320,13107321867,30786533987,50142305112,28564070223,16541276623,48144110950,
   40251300689,904597627,41764788108,48211826937,13856860736,33016029602,52089211805,26140823290,
   22722349746,51954054531,35997531372,11432006664,49194196255,43963352086,535478932,45317776611,
   49695161102,8748265375,40566768861,52867630188,16656524805,34885022489,54451774342,
   23794879601,29316902639,55606880808,29629130475,24955413201,56163636056,33521104005,
   21468100983,55728478548,36196101921,18297973261,55193032180,38478253293,16209490765,
   55433100660,39752424405,15934789523,55809545956,39407056781,16713629497,55718359282,
   38260325363,17947162775,55969033468,36804609105,20501617583,56915063020,33997190163,
   24711228397,57347250424,29382239889,29387088929,56722724020,23933837175,34138162415,
   55812670770,17641368727,39782590635,54182103192,9353642825,45720822621,50289081628,516440670,
   50289431173,44206996798,10619973282,53426571119,36675974932,21216857738,55344122289,
   26714921618,32426605748,54308511699,13788357034,42190922484,49164956303,387070587,49057285098,
   40805925293,14791346723,53156401340,29107116351,29437954159,53020004816,13313708721,
   42056110849,46665749930,4545040706,49757391083,34952823716,21763671448,52053712739,
   19110960078,37308333666,47992641633,669275791,48453718704,35782291407,21308628575,51337571910,
   17176913361,38091673991,45446363146,4263698074,48687524689,31435062908,26123941332,
   50375866147,9673146152,43511826472,40163697263,15152900359,50451933472,20163068289,
   36199603931,45385873920,4875522844,49093919001]
private def pvm_w0_4_p2 : List ℤ := pzig
  [28572135358,30278196388,49006099377,1980576330,47780223866,33205996649,25991784127,
   50079267824,6673528389,45901391129,36524274456,22858770570,51637999985,9452247422,46418778718,
   38250863641,23317057673,52634780212,8623999683,47503424557,37514704174,25035526226,
   53060731637,6543287420,50061498120,36185150263,29860699067,53927294152,521241169,54108439651,
   31039363194,36920201934,52014942127,7977082983,57116507146,23748501777,45057135385,
   48821204664,19638120806,60117059521,11689294076,54686264814,40162722757,34280585435,
   58187911416,4553764698,61263614141,26693878976,48905808022,51651604211,24455536785,
   64422709666,6038023057,62284927001,35462011724,46066175116,57345950587,19662277693,
   67223638800,11078612785,63393552723,39769468586,47002328256,60846032937,21539560971,
   70593524800,8058107241,67672266913,36453646536,53108824894,58886081751,29836816745,
   71915209014,1951873430,73847860937,26123012898,64828213412,50382626241,46627140469,
   67771900756,22200600540,76458109441,4890345804,75867375308,31090776451,66555719651,
   53383090488,49992034662,69641692419,28303742213,78757013280,3997647222,80541336555,
   20351694740,75498349040,42436819863,64575810889,60520412662,48998136682,73614508419,
   30196684801,81459964660,9766324160,84314289205,10655113516,82665755884,29623373079,
   77043806125,46152976804,68026145524,59839894803,56377617881,70727500168,43121551740,
   78990938873,29379798039,84687922440,16034085014,87795674521,3480549801,88493141282,8269901833,
   87371886171,19202005638,85276562912,29001695409,82850660449,37200986252]
private def pvm_w0_4_p3 : List ℤ := pzig
  [80243633102,43638570901,77344722661,48685606580,74323673800,52872297541,71812921429,
   56279132720,70415641740,58468209543,70111156015,59131586180,70411185278,58609387427,
   71178377699,57436157960,72950637758,55434464141,76132291449,51767726340,80172755084,
   46075025439,84169103429,38893589286,88088663116,30422713229,92370957635,19694623964,
   96260475616,6038299145,98018086021,9597628453,97051693350,26352520402,93616778049,44866156667,
   86171573650,64607978814,72535400899,82551841251,53285184300,97024215006,29194284511,
   107448162229,1145888057,109565463594,35419014976,99996006465,68388789649,79759375788,
   98431092696,46254922489,118966333503,702710084,121524904740,47827441710,106331760065,
   96740211409,65428935014,129080608120,7412854017,137808162575,61776234369,110229576694,
   120947358986,49701107673,150726277499,20809129099,188563156376,253647396466,244553740438,
   514444254292,1353958072850,2821046666664,5009160511170,8420557008878,13978011409378,
   22686487304472,35387149360760,52877711333376,76157474324224,106364014511466,144322610748566,
   190070938185004,242728053990680,300683981598734,361783750030270,423297912674256,
   481828885802674,533470462801962,574338994293692,601259144337812,612258861347384,
   606702473983910,585162090348606,549239441473098,501444400200574,445063823858578,
   383893820599906,321800851056564,262219577253770,207760631466624,160047361701664,
   119783329581506,86959580412792,61090454298120,41406550664554,26988788253412,16861575841460,
   10066991900756,5728569828774,3100325493522,1593266485372,776695184000,359029755068,
   157418283466,65529018726,25935037204,9773932150,3510276766,1200323952,389259504,118768124,
   33660592,8700148,1998912,393178,62090]
private def pvm_w0_4_p4 : List ℤ := pzig
  [6764]
private def pvm_w0_4 : List ℤ :=
  pvm_w0_4_p0 ++ (pvm_w0_4_p1 ++ (pvm_w0_4_p2 ++ (pvm_w0_4_p3 ++ pvm_w0_4_p4)))
private def pvm_w0_5_p0 : List ℤ := pzig
  [403927939,795740756,748900651,82413110,629274236,574308397,205497301,693914634,211645901,
   564985079,503686390,307963804,641465489,15763463,639429150,249032099,531115721,450269936,
   355322278,572367199,148648851,614891582,59361037,584910575,241713292,506580176,404773169,
   351000077,445596372,326780670,739520629,274829302,62963363,1016028688,2392688179,3287110546,
   4464754015,7362878324,12002815967,17432412752,23851033349,32587596920,43845727519,56023666674,
   67617017585,78190890984,86677106559,90167910882,85700992893,72446379424,51207254161,
   23011215836,9993504388,42709714599,68055454550,80244308243,76504820544,56574593891,
   23043786492,16972627658,52447580439,72751670478,71973874981,50126375444,12782475983,
   29022434549,60760544632,70199029089,53648672166,17606544149,24411345035,56498192164,
   65346257493,46187597504,6892922067,34590652835,59237000360,56167786905,27009858148,
   14835908520,49148002927,58104351010,36592692325,3748505833,40969237390,55287828767,
   39362531602,1811304759,36603799899,53518802714,38445768491,461617236,36968640796,51035970373,
   33596362468,4434367216,39507722557,49152111218,26479687271,13825097491,44471352924,
   44601426921,14478452480,25118014974,47221264615,36496478656,143146692,37043168949,47193425562,
   22608384219,18645408641,45833378448,38850471057,2959423838,35283458320,47125194883,
   22848080472,19653105106,47219337379,37522776600,2090288354,40034493363,46037976518,
   15252547411,28028801699,49115805240,30211764889,14155691503]
private def pvm_w0_5_p1 : List ℤ := pzig
  [47383038986,41015972839,128796905,41301799068,47545242275,13465897748,32309681900,50893675811,
   25693484594,22448647592,51617091537,35312751738,12685341980,49613942037,42270342950,
   2895347164,45626399819,47602742650,6462075759,41202390353,51645465368,14240177347,36933900131,
   53878887634,20306769199,32364798835,54658515002,25572216891,27817313465,55247553516,
   30091970425,24457937393,55909754088,33010149913,22397108973,55917597410,34485864737,
   20775386347,55534016708,35546809637,19794266547,55812638682,36033898633,20443409015,
   56530188658,34973622621,22417106157,56671658218,32678366551,24716013015,56533872064,
   30017413781,27735147025,56847308484,26354283075,32216583049,56739946420,20767542609,
   37247838553,55122894144,13989858581,41806774747,52522278526,6692789959,46442544393,
   49168825818,2016480240,51148784485,43680157270,12254199160,54234855225,35582260726,
   22440053932,54972605027,25971014436,32014860386,53924736315,14755322158,41360254698,
   50152334239,1190246302,48964882296,42192904547,13269354183,52794762676,30852427871,
   26670621103,52878740918,17196190659,38769261829,48957068326,858842431,48266171129,39359844004,
   16741730362,52215309081,24605788894,32265382030,49805467929,7116847488,44115492404,
   41568076875,12036244093,50954624452,26715026697,30761630187,49646427574,6467335659,
   44378585387,39373247412,14756882910,50113455931,22406332590,33679368422,47194560479,397150908,
   47169617162,33997477773,23171437699,50169756884,12049925975,41422514837,40911906162,
   12686941974,49758396339,21879921896,34993713668,46093839311]
private def pvm_w0_5_p2 : List ℤ := pzig
  [4049247249,49231224494,28698160069,30434811749,48716842352,1559908963,47599979037,32769440324,
   26230782934,50137090173,6157345196,46819038042,36227093331,24549280699,52070869918,7554560439,
   47750464175,36932546928,25209446780,52513833825,6900608024,48717159902,36752479701,
   27158766397,53740561962,4320356023,52114316645,34713627818,32669300740,53751428429,2111374321,
   55261332126,29471185185,38937413307,52024989902,10105222960,58667367839,22247434040,
   47595854692,48396723169,22316188997,60790161808,9705013107,56083026989,39405754484,
   35810522740,58732060653,5653380131,62732713478,26347887901,50637582789,52034888152,
   25754164738,65192381007,5649596806,62925513046,36072363179,46094212507,58619471836,
   18816521658,68506782273,12723494136,63928516034,41798030107,46183540731,62601856316,
   19137317372,71349229103,11772842594,66820029206,40722088733,50323759093,62613348346,
   25180445502,73923652241,4097791228,73165800884,32712810843,60937400255,56387442102,
   39604750904,71948509741,12724329855,77636734802,15663102281,73160497053,41722422360,
   59550277088,62371614875,38879503513,75602336990,13904588454,80550913137,12339607852,
   77364062662,36955498181,66953115045,57560698170,50740263166,72558910323,30462995113,
   81235717364,8036301038,83654029847,14582683106,80401200712,35584696459,72310370967,
   53548482062,60287616900,67641731671,45298057715,77659722572,28437154488,83848131149,
   10932770559,86602417744,6027030437,86246375211,21578699182,83048770958,35367964331,
   77434753221,47449332296,70146373712,57947358763,62117023633,66775147490]
private def pvm_w0_5_p3 : List ℤ := pzig
  [54097322674,73697033195,46371534449,78689014018,38887492388,82190424091,31712503221,
   84886385792,25316131266,87175127153,20298210129,88923954702,16831852188,89872683317,
   14544565219,90230344150,13108167876,90629063485,12828717987,91361868700,14348786644,
   91929251277,17751393891,91686555344,22413293990,90741319345,28026626197,89571428668,
   35216287856,87740826561,44457543897,83943999266,54922198808,77655982321,65538280055,
   69394283104,76527539384,58673962895,87998271075,43789771356,97920936256,24686576261,
   104215757769,2892966972,106841087924,21898741626,104321090029,49788815327,92999317420,
   76761751468,72753937979,99730747429,44595080490,117429812730,6446420497,122938954653,
   37279960655,112257226628,79744613664,86028874675,118186401967,38739138724,137572207480,
   19297515654,134533385129,83174497109,99079217810,134122753398,36564734673,160790770349,
   50608828869,140940214772,152564437986,18886414884,71839101628,561341448292,1464856559712,
   2786254377096,4967077737212,8893388994122,15537348386310,25739553858714,40401579259910,
   60767596883350,88313387215932,124213375402570,168828144173550,221581971020118,281127290834026,
   345422322142288,411576126778498,475724925510752,533298888871554,579722406622684,
   611220247184144,625348773146172,621138088732978,599012065805984,560691712835434,
   509111938439552,448218560017788,382529830002464,316511314354346,253961375662646,
   197613346251000,149040341010950,108804044753040,76714875228978,52088033261240,33943945174748,
   21156286999896,12569343891186,7096722327922,3797753467258,1922059257332,918392796758,
   413777911732,175644913010,70218155246,26430149216,9361840604,3115690010,970570114,280846442,
   74482828,17711968,3644436,608978]
private def pvm_w0_5_p4 : List ℤ := pzig
  [71182]
private def pvm_w0_5 : List ℤ :=
  pvm_w0_5_p0 ++ (pvm_w0_5_p1 ++ (pvm_w0_5_p2 ++ (pvm_w0_5_p3 ++ pvm_w0_5_p4)))
private def pvm_w0_6_p0 : List ℤ := pzig
  [723970277,823806030,64016587,696239119,411003480,485361820,588536339,263127941,662989194,
   55006900,667829171,127856342,624562372,280687777,548599733,402136556,451475330,492572011,
   342759587,555287558,225786526,584177829,125682945,625813444,47103977,488163009,105030175,
   948654660,891266339,720784626,1875517689,4055956488,6130140065,8647272570,13319418925,
   20407269842,28745479453,38189017240,49757885359,63024761956,75402588653,84517839802,
   89312853985,88179292398,78242345845,58000575772,29406250189,3560388453,36670929680,
   64597533987,80369370218,78399672529,58183523562,24345711563,15555163995,51859099402,
   73587015751,72469767468,48049144499,8502460568,33107368390,62962897791,69851319954,
   49744795679,9832352676,33230698190,61296301807,62945985012,37493745481,4589735319,44438904294,
   62582857677,49702196928,12595728919,29682913783,56013186312,53140510895,22088080340,
   20904356604,51749913275,52596371834,23321248151,18531478231,48659184260,49720558003,
   20878181032,20760882800,49138960861,45792350438,12987239667,27490057577,49252626210,
   38479916317,2311111516,35405485440,48884596047,28164563504,12455591338,43841581079,
   43497757860,12039000643,27768372907,47350558838,32238797301,7097109643,41489724524,
   44348208131,12978549092,28363865390,47524019289,29757949006,11158222430,43566582551,
   41794349190,6386934177,34790855361,47938116980,21626650513,22647476609,48200769272,
   33890945521,8569223317,44235231408,43141389973,5298154358,37794856588,48786236897,17357126378]
private def pvm_w0_6_p1 : List ℤ := pzig
  [29456898776,50661301161,27619550974,19658547302,49984887735,36457987704,9806107952,
   48054395517,43302272996,1096937222,44918099879,47723043954,6718651429,40512178429,50638021842,
   14088980577,35940782717,53021547500,20299578115,32214348831,54538471308,24723985267,
   28931609187,54850617030,28112393551,25672748521,54917229880,31134564459,23315150005,
   55502872062,33082838933,22502150837,55929899652,33469279219,22449575911,55758757016,
   33171890827,22706133579,55882134358,32602034725,24177017031,56618227000,30768849271,
   27135339491,56871415040,27349610191,30486114435,56273369598,23304837795,33966699065,
   55649564074,18619454751,38439973385,54695037308,12193270373,43504163847,52046680662,
   4278576173,47747137817,47731469664,3972208416,51164158261,42482656928,12864750284,54204905655,
   35451530240,22918144948,55555859265,25737561778,32728839398,53923281497,14402613210,
   40966060502,49851330299,2286125040,47902836706,43339243355,11163362027,52805073342,
   33066660059,25031947495,53533768968,19459358587,36883258189,49712642480,4413673659,
   45870132193,42064550594,11606983074,51571506809,29803990590,27797200584,51681884491,
   13059083080,40946507004,44985281695,5293760837,48750543082,32872008539,23023237367,
   50791332232,16049353067,38703977591,45395854760,4580936884,48638575519,31580419660,
   24803423854,49658653983,12187053564,40367538958,42022747401,9488240293,49177843500,
   26166108821,30649800225,48126234882,3340911637,45692101453,35324971208,20723477216,
   49619082479,14068209886,39757821548,41859297107,10969511253,49829569020,22961001577]
private def pvm_w0_6_p2 : List ℤ := pzig
  [34793771471,46467162576,4056220462,49241358007,28429189568,30437813254,48485066475,1497645716,
   47750345110,32893473477,26851060233,50778614374,5335165823,48099366981,35676142256,
   26214405184,52179688129,6067374650,48575324568,36236376961,26411480263,52966525152,5901923369,
   50230409405,36494561034,29216478652,54449315625,2447828622,53583840108,33664735947,
   34343703489,53818348940,3326036718,56293044825,29201443530,40432747698,52798318403,
   11444274899,60154471430,21539224493,49179172679,48463094650,23347003566,61408335175,
   9637731876,56783943654,40301365177,36099093225,60165719536,5237078962,64008635167,27412322386,
   51052022554,53332362831,24874347369,66081479452,7788430295,62765182377,38921224354,
   44487728952,61241177689,15792013773,69838913342,16654079799,63108046827,45720898142,
   42838961180,65402451973,13562955615,71979514212,18613107053,64565445497,47368201496,
   45008223804,67418722719,17266180749,75424701876,13534290711,70420631797,42123766504,
   53753450478,63992024375,28607174693,76029054514,739566041,76846144105,29746952776,66788216396,
   54369545617,47694679763,71605002872,22485756466,79769672263,5347797726,78505787268,
   32279280475,68585891503,55235604924,51612902748,71972936351,29708639859,81277350180,
   5244352136,82957584223,19384548598,77648999556,41970006421,66508594463,60710936210,
   50918305096,74416580871,32296879543,82620540498,12045551380,85529352937,8441559346,
   83796548646,27818109995,78219563127,44944074522,69522997898,59104982533,58343988583,
   70132045524,45380485662,78289753823,31513665029,83968519358]
private def pvm_w0_6_p3 : List ℤ := pzig
  [17717763630,87407221839,4764694793,88683001208,7033210543,87975219719,17768102390,85817248508,
   27567145601,83008463765,36257392414,80193259640,43444672749,77528758115,48959792136,
   74857779390,53146280757,72253008321,56551698742,70273349016,59299456795,69518649989,
   60944594224,69984106136,61110079805,71146849187,60081699758,72815064590,58385650993,
   75525352039,55802329964,79688312318,51395353017,84671064013,44772513834,89488332144,
   36517406937,94158805857,26725552800,99092433040,14220619427,103192740955,1529318487,
   104513850966,19241810980,102708243207,38277920689,97818133106,59447955622,87456175843,
   81189563835,69757988480,99888546904,46140980629,114635616003,16241989418,123385049810,
   20931709614,120040520541,59879886239,103716612972,96789758120,73765763459,128349428907,
   26337632088,141851330522,28788967938,136047699815,89083956845,101114180760,138082178582,
   40832676761,164745259729,43037591683,142956606464,112466376624,86600617063,121591011597,
   193927066158,737683554622,1451792944440,2764210100998,5526751993148,10625536363242,
   18851133366532,31213976312176,49237558601214,74735669574286,109182395061172,153216606101452,
   206574620564046,268197573230782,336120682903150,407156047187458,476794329103730,
   539672230071964,590485126720486,624884804345664,640005775307218,634626525668840,
   609191447476232,565823083603768,508224952669750,441293924622414,370411183124906,
   300605702600716,235878966805258,178881905997706,130945345284324,92327005151010,62517679209734,
   40513051620334,25031236681914,14691047278242,8161770312266,4278451502358,2110140677582,
   976660620020,423229694264,171341896840,64660390678,22685616228,7371836048,2205492828,
   601318984,146790152,31096144,5384480]
private def pvm_w0_6_p4 : List ℤ := pzig
  [658166]
private def pvm_w0_6 : List ℤ :=
  pvm_w0_6_p0 ++ (pvm_w0_6_p1 ++ (pvm_w0_6_p2 ++ (pvm_w0_6_p3 ++ pvm_w0_6_p4)))
private def pvm_w0_7_p0 : List ℤ := pzig
  [954013797,316945236,681037406,383955019,591209049,424132448,537043452,452306325,496217769,
   473445046,461590786,489866569,430208935,502973096,400308936,512637645,373520693,525282120,
   335121762,507766017,360267733,624157758,104442592,174299917,945463601,1782394114,1955332499,
   3190827902,6337836015,10251740190,14662749955,21322883864,31106697701,42575671630,54523272293,
   67221365160,79751628017,88606283238,90449277963,84148268652,69061007565,44161139252,
   10900768503,24962620361,56047279544,76332232951,80947696982,66422270469,34167342120,
   7398197054,46099697605,70909401048,74142351895,53088658064,13265892485,31037586785,
   62704388640,69859768299,49927221624,9989187969,34254422353,63181729398,62922024083,
   33729356414,10204569150,48329091481,62683362734,45597613913,4934106220,37833237046,
   59212066997,47874829706,10794887267,31454437737,55470491506,47128309849,10689965224,
   31807796272,53856433277,42070919560,4560729433,34997912165,51883568672,35061928847,4994403927,
   41502382608,49234036957,22993426894,18516390282,46428391681,41688026968,7590973755,
   32034100321,48461381738,29001228157,12128303793,43805709016,42145154383,8764526910,
   31005514056,47130154169,26949346718,14607892414,45051560297,39584237694,2146785101,
   36959731485,46020858582,17829064173,24864260289,47527352080,31179476533,11540708063,
   45191195746,40731424087,1346056314,39320294772,46297203639,13592328786,30906505742,
   49081648229,24728643564,21818982446,49803106683,33608360260,13020529730,48221010151,
   40054926376]
private def pvm_w0_7_p1 : List ℤ := pzig
  [4213862560,44802575295,45111674940,4362519445,40996782637,49168867872,11587602317,37386990063,
   51616940814,17264693585,33424504961,52679417292,22308441459,29335733611,53570585962,
   26783440107,26270233153,54525485626,29797957839,24335245395,54776414088,31487513845,
   22665543121,54575124596,32864743051,21478467933,54968638962,33751896395,21762534125,
   55731741348,33198708229,23210056029,55901219332,31548973357,24869441747,55831139044,
   29665359755,27173917715,56282500754,26937104665,30884421609,56471043632,22485405111,
   35184921555,55413573426,17000489745,39164508881,53667093614,11117586029,43430251649,
   51547776244,3945916479,48158050351,47805075042,4819718622,51914653927,41870611168,13885545836,
   54009286067,34670267012,22785430302,55055392235,26132225524,32149149514,54407463685,
   15231322148,41064148676,50507835983,2681003414,47698838684,43572358137,9951296477,51891892894,
   34426364279,22646725035,53657439298,22344965051,35053478297,51274857070,7337742525,
   44802382833,43921885126,8385281966,50368156947,32867143342,23363821896,51860016419,
   18526483688,37114290166,48097799423,918788670,47174067164,37758511605,17301796921,50820254692,
   22434732029,32948078937,47961305594,4305267309,44722120441,38615156496,15515027246,
   50398623153,22201846780,33707174720,47019400057,1328875652,45620092614,35042215453,
   19483724583,49379849918,16816778837,37326536191,44039321044,5865976188,48442933215,
   28423412396,28395028458,48240361439,5535164818,44116085172,36440044411,18543918119,
   49537704194,15876147503,39015601933,42874418852,10232427984]
private def pvm_w0_7_p2 : List ℤ := pzig
  [50172736503,23314570074,34811623736,46449362331,3985048357,49076611414,28601416377,
   30298656081,48919542712,1639920337,48543025611,33220290502,27877482454,51440041487,4405945310,
   49038997640,35211063697,27129288619,52366742598,5598849967,49298718689,36530526712,
   27293713740,54042458853,5311618344,51759914654,36486508467,30648692259,54998262248,1644863015,
   54353998485,33761903822,34853919054,54698562153,3196120939,57500199922,30041226819,
   41375830683,54036045452,11666515734,61203060731,22144088596,49421706004,49582163273,
   22421189403,62421293372,11634598707,57014428629,42776783150,35109168748,62191889485,
   3050857977,64630803186,30244500757,49642325569,55860984676,21408952552,67241303483,
   12628521130,61727084884,43869967853,40968061911,64763067892,10221446784,70554886639,
   23158046658,60212074210,51576811345,36386946161,68928557978,4550339956,71807675347,
   28411552930,60004517072,55760246521,36271209207,72270922854,5509242678,75139234155,
   26370627858,64302723362,53640205901,42190763731,71760276458,13031260632,78044865867,
   18087936006,71920937476,46186481971,54805489109,67199944388,29681472706,78504292755,484513291,
   79111391426,28581141375,69567073785,53687961146,51638697076,71899621343,27900917711,
   81486298722,1315036392,82005232881,25140682668,74154814440,48774354507,59460356935,
   67426349722,39890636162,79661480775,17515570555,84884750720,5716663859,83336094811,
   28072808266,75931779428,48058302451,63975748625,64459947008,48836674040,76454509585,
   31721785681,83740646088,13632264980,86580951003,4533148080,85661251992]
private def pvm_w0_7_p3 : List ℤ := pzig
  [21871769441,81796164955,37519207478,75649385566,50857518877,67662157761,61724519924,
   58230689938,70401496023,47942959457,77322041186,37596279146,82722607963,27908603627,
   86567945202,19176182106,88848604507,11263489249,89934328192,4010482090,90530361581,2352967268,
   91187419492,7301483575,91901039033,10575705484,92355522972,12504103013,92596095717,
   13541168108,93218325646,13523252005,94657544741,11741382912,96499578210,7909035331,
   97977858883,2578331384,99078450078,3897109044,100345500805,12269198937,101365838892,
   23280611454,100616720879,36186952191,97411157830,49965498168,92223122739,65164243911,
   84123177416,81959116398,70815224923,97883271621,52259472520,110985634192,29538991247,
   121330083489,995008650,125752595414,33001219456,119803364157,67658389863,103950660954,
   101807530758,75563160515,131325816069,31994590564,146075381326,19141484452,145469373465,
   78032465497,118535230754,130147137682,67175312515,165592476933,7613090979,164694957936,
   78969678120,149009028291,179124501325,70490146648,366016671502,641629874974,1366791488834,
   3341976770524,7305323336640,13983905438094,24559364814268,40894152025986,65122144528848,
   98954369818454,143291500585646,198223589196414,262975213795412,335502504088094,
   412039662888204,487163645990984,554573703649620,608211140981764,643180984204870,
   656261364812084,646160390947574,613713133383790,561960837275714,495874895379450,
   421602961750760,345410669133862,272689760825738,207347137505830,151659518094514,
   106467576271840,71514447566684,45790320047090,27834482914778,15996067521898,8655532236442,
   4392614084248,2082850535708,919332434090,376253857226,142172259576,49341774572,15619377774,
   4463968526,1133069980,248207764,44354488]
private def pvm_w0_7_p4 : List ℤ := pzig
  [5605318]
private def pvm_w0_7 : List ℤ :=
  pvm_w0_7_p0 ++ (pvm_w0_7_p1 ++ (pvm_w0_7_p2 ++ (pvm_w0_7_p3 ++ pvm_w0_7_p4)))
private def pvm_w0_8_p0 : List ℤ := pzig
  [931213865,427606497,581310636,555177316,396016641,628148743,241811502,664017530,105277029,
   671956809,15591147,659337968,119987730,628923661,216068813,604831438,257658630,481958649,
   487951409,781449122,160532949,618690032,2384321009,3808170388,5296557521,9028017534,
   15121940123,22202107848,30928945089,42893145448,56946443957,70250016426,81512616599,
   89664144706,91100733509,81957599826,61878034153,33051910798,1985364802,38485566003,
   67851533506,81488127515,75521188914,50824206535,11930755956,31419520334,64961296243,
   76437162826,61922085603,26297820030,18886642970,57132808543,72034223482,56333134515,
   17050077580,28460812992,60670586195,64951903404,38077249013,7551164465,48433232868,
   63320336863,45204887064,3948696913,38970839761,60144731618,46833913179,6406289782,36768780448,
   56894744749,42697591260,3141524373,37948968551,54922271020,36296201875,5938544889,43334844930,
   50974725459,24524644626,17829027686,47619925369,44267638802,9520505219,31975010501,
   49769510118,30899724849,10181581891,43062477716,43818765017,11856671328,29242233230,
   48047376503,29343934434,12491080178,44159013253,40554553998,4894636853,34447409825,
   46278429374,20723763503,22178149453,47198792590,32864095243,9225318701,43498040738,
   40987711949,3935531126,36498106090,46167201135,16267431984,28276519334,48720629389,
   26329734452,19636182506,48319014567,34109372362,10386165946,45792137399,40565619326,
   1262641496,42645950917,45637893092,6506075607,39120289441,48699848082,13056372045,34756032209,
   50395763334]
private def pvm_w0_8_p1 : List ℤ := pzig
  [19199960359,30270248393,51885912014,24526020473,26770038587,52981070500,28245155941,
   23944223745,53088390462,30959907129,21123192793,52967278568,33510477187,19014038137,
   53497255716,35287214727,18384370039,54058271616,35647752781,18513875363,54056261912,
   35395144405,18822912509,54322812178,35053023043,20177822861,55294343378,33668159603,
   22972425629,55929870408,30821767225,26168585981,55802960052,27451019623,29457422939,
   55764500344,23622563259,33746196769,55650377794,18227838111,38805357327,54157347510,
   11377846879,43325886769,51249367374,4151868763,47306391335,47689012466,3750120754,51343646031,
   42736618456,13046833898,54381358285,35352297126,22687454056,55129292135,26286311510,
   31464522772,54001257059,16279087494,39741030192,51113773207,4586018420,47225888278,
   45073361977,8570704161,52010870870,35620506855,21278288939,53331217370,24092813185,
   32719622369,51703867238,10681483189,42899492031,46246456650,4817211680,50004539267,
   35908564174,20382182970,52042389779,22037200770,33703066648,49235402837,6233009522,
   44222956114,41680989395,11168479949,50536089698,28445579181,28143647957,50060471046,
   10887178183,41107130037,42607946084,7800829764,48467752017,29620401800,25814057014,
   49433670161,11520903234,40893635640,42007525197,9614630671,48849439432,26483151727,
   28909698397,47624282890,6382370401,42862756987,37922862498,15346604686,49339488403,
   20097102606,35254573078,45162271281,3407404175,47438772102,29898713283,26233969409,
   48234319652,7691084049,42978785109,37844898544,17030549312,50055005739,17100757884,
   38932256244]
private def pvm_w0_8_p2 : List ℤ := pzig
  [43502483695,9927129699,50228420642,23608261545,34460046635,46680474490,3359223250,49268647723,
   29443649624,30430223150,49920901971,1659582986,49553459832,33469390065,28642279301,
   51871813432,4147015655,49438798403,35570721770,27193490138,53205733125,6093186076,50250030340,
   37561236781,27921885295,55286968760,5290198603,52699510727,37037775388,30798234702,
   55754262815,2486415646,54770044182,35364624081,34476499467,56441729804,1920040046,58600255837,
   31851404500,41216715446,55631141975,10096037727,61724352070,24681840181,48265808661,
   52147408172,19550331584,63890801043,15568558712,56500203582,46561415169,32333224991,
   64411257792,1464406297,64140720587,35250467520,46006758690,59713135283,15146856593,
   68391566302,20079846355,59229482721,50481295568,34841942052,68446088015,1557473623,
   69754341302,32389784871,54390558913,58973309312,26264611394,72242543321,7971363842,
   69529572250,40628508125,51792716323,64755135450,23125511124,75571005791,10354647376,
   71287603486,41918580163,53215020445,65603272490,25225394004,77281738401,7230282842,
   75258840780,38291288303,60348574475,62783706782,35494395118,77042402309,5066706949,
   79346200968,25995203245,69951994539,53031423300,50796467620,72361840577,24985515477,
   81743195980,3795738891,80537102641,31840861868,69595526496,55878285471,50919877085,
   73399250214,27189642334,82858964621,1275975899,83758399086,24155060451,76605312801,
   46887793612,62747385244,65251645583,44085233539,78121936150,22711738868,84902554917,567152507,
   85534611076,20787515687,80510302607,40219443730,70819936142]
private def pvm_w0_8_p3 : List ℤ := pzig
  [56926088355,57770672371,70306229664,42697655724,79927723109,26689292267,85629953380,
   10479085158,87660440093,5438597950,86673857382,20584574275,83507287259,34386072794,
   78848658168,46320347123,73059057529,56199366052,66318026842,64293953093,58958606107,
   71097119834,51624024016,76894413241,45011378223,81583963676,39426661226,84991646705,
   34681909017,87350878134,30556913152,89309795145,27330899185,91323992968,25649495112,
   93162622589,25777591185,94302341354,27270346560,94793703167,29727570093,95250876168,
   33632693924,95716718395,39771617639,95164354364,47892223702,92787920305,57016697433,
   88988248068,67227063592,83824669009,79386553651,75603583730,92633731006,63058918153,
   104851667973,47040435062,115812226840,27282237501,125332449381,1688167628,129696276972,
   28355488668,126392628271,59960661449,115782578864,93757932660,93504062917,125132942763,
   57742841478,146823213990,12919453213,158148213503,43872689111,147061375802,100671793006,
   113698479669,151020912933,54919994736,180667679190,19931708930,193227782641,145549487639,
   80559649422,163106546132,119325136930,494088995058,1968595473668,5075673214960,10543037148816,
   19854166608440,35261027328780,59158405731400,93452800314830,139374402500026,197439618410454,
   267034956304800,345668461240074,428548182758012,509022580700240,579726713301692,
   633817758400480,665869746211898,672467151570152,652704146476296,608548034419382,
   544755428793128,468110280824280,386131672527420,305717878110526,232188263821162,
   168910265606914,117405256513994,77703322452764,48764348509894,28885153206668,16071805348500,
   8358802799078,4043393365614,1809703436014,745164791730,280410692218,95632492424,29222734884,
   7864896548,1811746812,338038632]
private def pvm_w0_8_p4 : List ℤ := pzig
  [44385614]
private def pvm_w0_8 : List ℤ :=
  pvm_w0_8_p0 ++ (pvm_w0_8_p1 ++ (pvm_w0_8_p2 ++ (pvm_w0_8_p3 ++ pvm_w0_8_p4)))
private def pvm_w0_9_p0 : List ℤ := pzig
  [675841253,840969451,222138081,590235426,593059180,220782613,695068799,128010971,623553302,
   397926222,453981191,562286319,221434940,678036950,94693619,463021529,556901243,1325618362,
   1098768413,2199320862,5183147167,8308993006,12336730999,19709427098,29953444901,41313108294,
   54421095387,69426362246,82717646717,90319731512,90710811713,81912899616,60914636171,
   28540079094,9166117924,45081227619,72364588232,82936886451,70866289010,38306293563,4943707091,
   46392203190,73149313575,74197727778,47062079315,2118619560,42382959032,69014191791,
   66606655036,34562336477,13533238547,54264268730,67548619781,47615508702,4493983795,
   40678860011,64043391646,51822000919,10707220764,35182358174,59641215979,49325492530,
   10181227175,34958150487,58038875500,43903190781,2009898700,39857137320,54856492963,
   33896634760,9320264386,46039114863,50576191190,19356524519,24985667555,50394300344,
   39267902159,246919520,38561878862,48788707987,22231201398,21324636654,48048909437,37123604086,
   2370210576,39347116141,45257455236,15497801927,26813878721,47692409172,29457671719,
   13232948387,44718300720,38761055341,673699262,37770163746,44640872915,13783225276,29304373524,
   47580555593,24431404180,20319271984,47227143849,32586883734,10615247184,44531687469,
   39305442550,1053141600,41127458231,44446598266,7069694157,37168248407,47387639006,14034570365,
   32225362305,48970094024,20630131261,27222424195,50325276908,26254361297,23196656001,
   51073666428,30241861959,19620500391,50780406504,33441218671,15989424487,50455099248]
private def pvm_w0_9_p1 : List ℤ := pzig
  [36523767809,13235824361,50781634418,38685327357,11879447991,50956801930,39586998805,
   11004706953,50723171440,40243011843,10371512577,51116441702,40848511701,11007746497,
   52241418234,40354374203,12939515421,53019455376,38771647577,15114589749,53510215514,
   37064340699,17724188471,54609801910,34839562067,21699909111,55762207982,31049318845,
   26461221413,55852003194,26182528583,30994358739,55305893904,20996492895,35837431177,
   54626788290,14663736145,41414849805,52679735352,6625686849,46470705257,48708498968,2007547908,
   50218373005,43535523894,10717386016,53302061099,37199667908,20269849084,55332012155,
   28541774290,30153521160,54739331869,17837318336,38688464350,51426370325,6434803964,
   45627171058,46128591813,5737904923,51198301792,38056566823,18865186843,53882258808,
   26554434311,31143130151,52370263958,13059498273,40959906115,47316908188,1229237416,
   48335113899,38882685754,16371660290,52310163491,26187248074,30881367820,50853959843,
   10313289680,42005525920,43983417535,6271411863,48796111518,32897628513,22541640911,
   50875963680,17534813061,37180657661,46409527294,1097345504,46888623965,35002172764,
   19462892706,49669782955,18953553760,34892660282,45759348993,14898770,45932754662,34656426115,
   20108149941,49596488622,16622403373,37057547857,43768898172,4540778460,46818682831,
   30004560958,24668625384,48225350861,10479115846,40964664576,40106955625,12515877633,
   49150558522,22208703319,33418945181,45638000488,1167582746,46328306453,31506748366,
   24254190592,48779539579,9670996372,42618399430,39209371595,16232333681,50582507974]
private def pvm_w0_9_p2 : List ℤ := pzig
  [17861767453,38710956469,43914543998,9191012854,50162223761,24597135444,33916002992,
   47669210857,2430333785,50016776896,30566336177,30741992783,50940194746,1856809987,50115050407,
   34046611284,28461328986,52493951297,5128322154,49678340408,37086432371,26734865975,
   54710673276,7253378847,51119578383,39032963284,27734446146,56394611395,6518559408,52759099114,
   38792146565,29453850057,57188661452,5021636845,55055385039,38290781080,33190147274,
   58616585767,694277674,58971147116,34882665439,39276848675,57787706872,6177771646,61818478283,
   29412236264,45718774806,56020211263,14720380427,65291422258,21377758647,54467460395,
   51442808010,26984309946,66451849091,8843888878,62084016004,42504193721,39758786425,
   64424015530,5947949688,68624178463,29892601232,54178552650,58068629249,25184945605,
   71254772210,10604639119,66275017323,44000557700,44667576752,66778324385,12009511227,
   73637855522,23701700837,63279473401,54111144012,38432004566,72468087567,4944293873,
   75034689280,29741077933,61680280889,58313728682,35623679752,75117010355,2484680129,
   77165126814,31063102487,64509211075,58701353088,39964440612,75638816251,8338247379,
   79343065824,24624220699,69753840499,53341824370,49018754852,73339642657,20880868185,
   81886081100,10108598929,78254950097,39381522894,63617628244,63015690947,40633943111,
   78193510852,12855125646,83436501023,15926877398,78634798410,42255577557,64908577651,
   63416658226,44339583650,77634457815,19608609995,84078281972,6419260771,82745565823,
   31102954642,74302882446,52352044159,59940249273,68800602234,41243514816]
private def pvm_w0_9_p3 : List ℤ := pzig
  [79796615805,20046483809,85243519216,1777354311,85393859793,22574398444,80708876482,
   41142821607,71838459655,56826246804,59671147194,69411433271,45328731241,78894229920,
   30008333160,85282711927,14708609681,88590426010,16529974,89013011603,13864115646,87092431754,
   26842912523,83641366543,38668914746,79409959296,48939014149,74770629005,57416768040,
   69757986582,64324804079,64472934973,70214823526,59415831096,75452636747,55293484781,
   79884032224,52438690890,83165593959,50581138781,85424858642,49416306054,87305938985,
   49312063811,89134077172,51039944970,90330182045,54710078773,90168839610,59595568228,
   88872159689,65453603757,86989346706,73158388876,83750894609,83031274631,77601813100,
   93708612862,68473363153,104289975221,57006169480,115549248536,41645385617,126562555951,
   20699501220,134046393402,4204077186,137251407947,32522315607,135714378048,65902692500,
   124244222297,100066593341,101627289278,131021659712,68821658221,158197296905,20409362448,
   169771912716,35360599156,164927551079,97649547469,135055717608,156730460676,75328976291,
   200659068451,33681447643,134810758050,2875918631,239338287281,4392215109,1136261712114,
   3524428698198,8078722908650,16740871617944,32126050933480,56812177082984,92983967197004,
   142393429508154,205974711836946,282864016826714,369464684513792,459400757711262,
   544497373821696,616191751860812,666779200363684,690410908329804,684029424017692,
   648162892759464,587135916173884,508325529091384,420594083411836,332499036733744,
   250923164004360,180428923279422,123250534619150,79659073560910,48476830434206,27626400662798,
   14657635617276,7195062570482,3245353469858,1334556428988,495554466890,164066377084,
   47551561980,11713690918,2319693938]
private def pvm_w0_9_p4 : List ℤ := pzig
  [320940196]
private def pvm_w0_9 : List ℤ :=
  pvm_w0_9_p0 ++ (pvm_w0_9_p1 ++ (pvm_w0_9_p2 ++ (pvm_w0_9_p3 ++ pvm_w0_9_p4)))
private def pvm_w0_10_p0 : List ℤ := pzig
  [365142417,740917781,782761529,260400299,473683090,692107750,121189880,584896461,551731659,
   217689066,642269230,288848784,730106395,102678223,585981561,2336165064,3150458759,5141229844,
   10153018037,16419337894,24117125929,35812556116,50491601173,65023739080,78753107507,
   90012029002,93270549113,84576145678,64239881123,33112011842,6390710538,45745352207,
   73564149878,82364000203,68986753062,34267714337,12623641689,54639280996,76034133453,
   69295516296,35795275209,12997784915,56080520588,72911589833,55988593116,13706729709,
   34719482587,65853874744,62381497513,25355998922,24307327114,59068607559,60452366548,
   27550792031,21501156407,57164865234,56756365687,21028460388,26571117826,56198670071,
   49489995882,10325657019,35631784361,56501567270,37660493407,6769107875,45114426446,
   50995914149,20541558160,24734496996,51493125947,39125281614,2801223636,41574590455,
   47716077400,17327235891,26065932073,48944935670,32813328859,9957194089,44388135782,
   41957880235,5137088518,35277098914,46229542919,18835066176,24514032782,47383710887,
   29557144312,14070744290,45338799587,36851842256,3643346098,40729573177,42204229960,6446678663,
   35539075209,46069660624,14774547753,30293737653,47725527078,21476920031,24320326627,
   47902967500,27671963697,18359653209,47990313240,32942230775,13582509597,47687027602,
   36535960361,9427880925,46440400034,39368908549,5248491445,45297874654,42217887811,1991403301,
   44971594548,44245092963,140326001,44584519932,45176574513,1318847682,43954100134,46121877265,
   2537703688,44191220270]
private def pvm_w0_10_p1 : List ℤ := pzig
  [47164548125,2439360474,45260605326,47236845715,1172235382,46095662970,46566837789,242052317,
   47012987386,46088856935,2265929139,48884266382,45163060795,5783683203,50950491494,42859151291,
   10032723683,52311101576,39879547959,14285231833,53672417826,36693136809,19399623133,
   55304974340,32193302931,25617790889,55918462776,26032668791,31667528155,55092616108,
   19274352621,37255135235,53657591648,11862965651,43153941697,51144514230,2835390413,
   48649103287,46286032594,7143329602,52308102091,39490820570,16803665628,54339254643,
   31569317924,26461709920,55055510981,21746102542,36209619974,53099278835,9734369596,
   44349654258,47741541195,2913263787,49852477518,39983498397,15355806597,53147672584,
   29953233941,27876543411,53472397128,16908495187,39169094991,49276012384,2009624277,
   47087082903,40997161214,12712213606,51315306569,29774612796,26788651968,51789083411,
   15350137784,39371170590,46958981669,1575824391,47812217280,36530987503,18176295217,
   50663354456,22397552257,32567655505,48287231820,5661743947,43940048405,40046426864,
   12846233234,49866998485,25537286762,29897343612,48173712339,7297473428,42154176726,
   39594449749,11666634959,48533797638,25259995883,29626391033,47626262296,5822882147,
   43311510351,37751256800,15306988780,48727516651,20635359666,33230009662,45047309063,30813909,
   45214415762,33066779863,21509533271,48865896656,13375919047,39555782257,41418041356,
   10264659200,48538644221,24029354404,31433440508,46271941653,1223572314,45716822608,
   33421647179,22865128909,49727690684,11166378495,42553434687,40220759898]
private def pvm_w0_10_p2 : List ℤ := pzig
  [15436671610,50757988017,18941998372,37980918524,44813697487,7750301485,50510251398,
   26339746663,33539633423,49183200370,1432292702,50799817401,31793562958,30508003546,
   51814138717,3022044318,50080418160,35654417951,27256170397,53802699194,7279930671,49996411989,
   39472557352,25758826948,56364161419,9226577454,51216859650,41146090727,25997501865,
   57544148550,9606193911,52075655611,42081840650,26749461842,59273114947,9047017606,54842565084,
   42205677241,30414379661,60752618764,5248340865,58084387437,39565440534,35120097470,
   60642661099,256114402,61323326824,36102781403,41435835209,60546153494,7600139068,65671175929,
   29179900722,49922247126,57205033587,18346162655,67783181140,19244554735,57784766955,
   51464442560,30350069548,68828167181,6322952292,66443359138,41598613741,45196119165,
   65553550054,11213534588,71712496015,26097060380,58639129986,56763387579,30046887085,
   72912706978,6464438951,70682224471,41583246114,50951419748,66721220517,18827537503,
   76066596458,17859038087,67786370921,50577650452,44176796746,72099896463,10842400485,
   78018153582,24795173065,67491376605,55240847844,43145211776,74504240917,10251886479,
   79190525438,24546567257,68936698843,54650650856,46192659120,74750726977,15485366919,
   81687850598,17611057261,74816269587,47555240398,55867958768,69759275849,28412361129,
   81212977832,2935151689,80759127383,33379222214,69042170822,58719558839,48202967099,
   75909968318,21412834664,83335610265,7663046524,80809205512,35397899017,69346165531,
   58671280264,50815902920,75221974237,27571391359,83842527548,2130686926]
private def pvm_w0_10_p3 : List ℤ := pzig
  [84388067989,23064450452,77605196882,45832310303,64833948757,64412668764,47677825320,
   77618224689,27745860667,84942421114,6528921900,86559020681,14607715404,83169441136,
   34406045385,75730016301,51770984316,65177529768,65923881699,52293962317,76562313300,
   37766187204,83876589451,22343894481,88348936176,6900837660,90440463519,7726314294,90404596214,
   21028683305,88394542909,32971014854,84761070562,43791504039,80201847943,53590018988,
   75516456194,62126464079,71149706451,69105782818,67044990690,74666445033,63081016895,
   79419825254,59633402176,83829098881,57468427139,87655449308,56948075578,90352739679,
   57651660007,92017263490,59209030328,93364750939,62232513775,94429601976,67593838566,
   94079734275,74914796479,91614156148,83168503612,87686691081,92763352831,82163350596,
   104656684700,72948699767,117440701589,59203921648,129108243752,42106770771,140287887187,
   20157535464,149806775534,8711030568,152894856993,41414905403,149113882872,77488413130,
   136743535079,117371816663,108752338222,151610672540,69301909011,180549551601,12580287694,
   192320497910,56908540850,174928659515,122462518395,125014131068,132417680214,197076851655,
   444511886537,213454960817,582588576046,2301020004644,6340539126278,15148638091026,
   31581082283436,58468478109442,98612698693558,154477625484752,227025437691840,314261727930716,
   410607560351144,507554834557238,595091758786238,663212422160334,703358407403262,
   709947994017868,681791523324178,622712823168368,540815159085418,446543492897896,
   350350719666060,260841218708214,183816098388150,122142404143362,76146630115228,44272290644040,
   23841967105494,11801594658476,5322205390950,2163574371588,782001936208,246474691746,
   65701606774,13997120046]
private def pvm_w0_10_p4 : List ℤ := pzig
  [2069764854]
private def pvm_w0_10 : List ℤ :=
  pvm_w0_10_p0 ++ (pvm_w0_10_p1 ++ (pvm_w0_10_p2 ++ (pvm_w0_10_p3 ++ pvm_w0_10_p4)))
private def pvm_w0_11_p0 : List ℤ := pzig
  [146740875,413576069,710334627,786024811,437226805,217399730,674771204,539011934,222112787,
   515685247,787996823,1105210808,1004661307,3502742796,6636489175,10174104752,17641725575,
   28372079382,40453846707,55649180724,72719823603,86109744676,92916220237,90990231056,
   75303170753,44713162124,5262456717,35588557999,69325719624,84136546971,72353862884,
   37486332341,9476036933,53809231302,77775167689,69029140336,30986786125,19306882341,
   60484432870,73390275769,49574304126,381108617,47470573873,68828518014,53009379769,7789337916,
   41977036716,66022446803,49328852322,3272047457,43324414407,62201874080,41102447999,7164501835,
   49941904850,57471246335,25516377586,22813035528,54333232839,47184337380,5821014669,
   39549303323,54437861818,27992819389,18601918343,49934940892,42820494653,2609133460,
   39622522254,49798533981,19388432792,26176687662,49336696261,31917264048,11297753584,
   44977317901,40924020922,1858128141,38830041455,45502509448,12579897927,30707603379,
   46839815430,22130848825,22109321741,47073265210,29824538283,14739919751,45915453308,
   34973591165,7796334459,43179478188,39093734081,916841231,40553778208,42775136011,4543839870,
   38430490212,44986047015,8699617646,35774710106,46244951427,12773418290,33210907158,
   47837355583,16186881794,31849963542,49147245999,18099913154,30894461578,49525174589,
   19514385484,29779625300,50080589067,20919398608,29629285020,51163729085,21191391518,
   30616889204,51629222393,20311336326,31590510466,51584245365,19382583406,32803928442,
   52053067445,17959592730,35235549066]
private def pvm_w0_11_p1 : List ℤ := pzig
  [52402126947,15058180294,38145010286,51654886025,11429140262,40665825790,50555891489,
   7712066972,43624910982,49493842875,2885274310,47262122374,47236447653,3287012013,50262001604,
   43498514563,9597717347,52394265710,39269696019,16066380727,54496418814,34150840283,
   23570914843,55845456452,27063322061,31287150999,55185150398,18699166695,38006595851,
   53013458128,9934344555,44207784481,49738437006,14763257,49962915491,44142577656,11119570866,
   53684725017,35897206406,21865882960,54768775477,26230912326,31659433750,53926678575,
   15225506064,40929437288,50507156719,2262902082,48453022420,43334834863,11372936041,
   52538404174,33227314909,23962285229,53377966272,21287703089,35440055797,51101716094,
   7157430039,45181694359,44402770332,8480206434,50975811319,33302895608,23171435244,51956530571,
   19603065448,35651450426,48733527791,4025801986,45555540642,40699885233,12974830423,
   50875147114,27401013257,28757685639,49818596762,10930005449,40693455511,43078994080,
   6442503380,48133705195,31386431634,23724139048,49860777673,14721472530,38437494872,
   43986331223,4609299057,47071008034,31317103665,22774616013,48540192442,14347425843,
   37654654213,42961186982,5434874856,47219314429,29668480268,25294350082,48207565085,
   10237034220,40367131188,39820392655,10836202539,47676890608,24286246809,29992188029,
   46413354304,3564522487,44225878303,35354850492,19212500790,49078602709,15553864950,
   37961836846,42390802667,7816243917,47949433182,26244527759,29639068401,47484102752,3440050349,
   45686267777,35214314114,21858400270,50481786195,12549895090]
private def pvm_w0_11_p2 : List ℤ := pzig
  [42051368104,41282614625,13895353993,50936344206,20949140381,37047575833,46538886918,
   5921834410,51290899917,28431041600,33067824170,50687685403,71661806,50981122198,33605670185,
   29089361527,52965479850,5655180071,49777321495,38522322400,25290779940,55688275685,
   10328918028,49969773060,42380615387,23646599371,57729130732,12656057043,50081808301,
   44406042484,22360381696,59009945893,14643238878,50702113498,46633931321,22619911777,
   61376583390,14599481657,53277614819,47001623470,25308920258,62575411889,12306232232,
   55596785426,45996410133,28523854423,63787043336,9103878475,59470335079,44206835664,
   34581867022,64774892875,2370644406,63901962834,38998441187,41918923579,63263149636,6035629968,
   67380380309,32229833552,50150589492,60860401177,17080100283,71097996838,21591018449,
   59985592117,54194657122,31005692812,71172215443,7232593612,67772048702,43718646653,
   45183618387,68275006232,9909703604,74340112109,28298223724,60561943118,59245406779,
   30871950883,75011944930,6841689843,71867930501,42980735422,50962203010,68735495173,
   17729279617,78180280412,19706523501,69490603953,52632689612,45082467274,73795919661,
   10759948271,78920090300,25819474201,67407325775,56936288954,42163221282,76432259643,
   8694544161,80838217784,26231840571,69833125795,56027917254,46027359420,75513062827,
   14202749925,81718525720,19769562649,74177787181,50083248014,54731892106,71997126137,
   26967656163,82519269104,4548242701,80695924471,35074783034,67511877674,60408271735,
   45481091395,77413482430,18053820076,84333827699,11018076392,80875684006,38233487499]
private def pvm_w0_11_p3 : List ℤ := pzig
  [68085339311,60732656350,48053787266,76504602095,23502025615,84441714648,2680345773,
   84298701241,27855021378,76605936542,49928940459,62554211663,67472458560,43833407398,
   79673592085,22400728433,86203618852,188454596,87096550491,21180929212,82709966516,40568408471,
   73749737265,57307729106,61262756876,71036956199,46499424071,81507627780,30645842208,
   88530438515,14562288789,92104690708,1285054617,92595555941,16633558326,90731365220,
   31139965249,87323492243,44296958824,82899743108,55686056973,77610126279,65331055830,
   71554409740,73709840477,65202096777,81282718090,59353980132,88012562017,54561119363,
   93533637046,50700490828,97881806509,47428078593,101768685998,45065924636,105758387781,
   44549834801,109407213398,46221423652,111938974697,49389425693,113646726588,53840499516,
   115327256365,60784348379,116201427948,70841639102,114529681379,82666285965,110445014708,
   95860821676,104487300659,112005728479,94042202698,129821733130,77269531391,146165200169,
   55857915282,162001236372,27216956903,174769653321,10691355605,177902504402,52525069664,
   173225161381,102369138617,150161845942,149827999548,109022146509,185364100847,62789549084,
   224765113218,6741472375,358856568231,435649009105,284244706105,7083906221,1198204891950,
   5372215124928,15297114046880,34096149667812,65363657694414,112996220988194,179870529548420,
   265856242976878,366549478786726,473481692257316,575391315178190,659879107394584,
   715342143229044,733316588505716,710761382058014,651192841864468,563870313430358,
   461298468230422,356185141386502,259010317715328,176737662732570,112582815181666,
   66508978706148,36148840228134,17906386701614,7991771103074,3166888456596,1091800635556,
   317305934322,73393976144]
private def pvm_w0_11_p4 : List ℤ := pzig
  [11724267196]
private def pvm_w0_11 : List ℤ :=
  pvm_w0_11_p0 ++ (pvm_w0_11_p1 ++ (pvm_w0_11_p2 ++ (pvm_w0_11_p3 ++ pvm_w0_11_p4)))
private def pvm_w0_12_p0 : List ℤ := pzig
  [43765549,158135801,370601243,626145097,790331701,612777195,255416779,657170508,118228584,
   1747149598,3048249565,4872827704,10645312693,17781809050,27534898655,42637897820,59299843333,
   75320337874,89794681581,95689556312,87454399129,65374765552,29555393835,15576572559,
   56594555328,80602126493,80404071822,52605367385,4071946888,45340418300,75047793235,
   73245286498,38539393549,15166431125,60430268412,73595003209,48923323112,1306173902,
   51052960553,70853735074,47982919197,2668586323,50048519986,66102799481,40162817188,
   12190723574,55446064663,59795512914,23648987599,27468091441,58848785388,48065384639,
   2034991808,44687274102,56580066957,25913352666,23138860124,53830840923,42677394222,2282108992,
   44951636761,50248678480,14700357913,31604745635,51212159346,28588657837,17889964949,
   49128514134,37762293469,6239955525,43874278190,42688736915,4628888646,37096741416,46092204489,
   13779909746,31243582714,47605369119,20145429654,25370839184,47084333395,25608022760,
   19373355556,46693490091,30410983030,14992771774,46370208433,33322651880,11525907946,
   45078228047,35556640338,7942793524,44187896283,38016293130,5562042626,44255376847,39412428126,
   4515676888,43939268889,39947707566,3429558882,43662448513,40917638880,2912455982,44549419271,
   41509283850,3904335360,45598819957,40947400172,5291100796,46220048199,40382749548,6729894950,
   47587445369,39873499124,9453889892,49520017589,38124390300,13141762354,50745034157,
   35537160672,16679071758,51784835545,32982825612,20810993116,53301919065,29438586866,
   26111252008]
private def pvm_w0_12_p1 : List ℤ := pzig
  [54069745479,24331518204,31325422162,53557834467,18786990342,36126209944,52741448513,
   12768639820,41465658038,51196108823,5184882656,46682237238,47645940737,3293666919,50461955246,
   42635819105,11576156533,53293899794,36836744765,20328298637,55448726418,29191122171,
   29656401083,55469127556,19473583275,37954779523,52905567660,9072526493,44735071491,
   48701968812,1857320010,50585390883,42385178272,13907769942,54430349335,32989271422,
   25774990358,54849250207,21557794108,35907927826,52369575781,9223114380,44506717946,
   47305423517,4420350881,51124848820,38540580999,18683987381,53852560780,26362297077,
   31330777663,52269685348,12581415137,41526763929,47218754964,2299218750,49211593559,
   38165894298,17989220110,52660644177,24782709844,32142676226,50496279537,9061809276,
   42674108254,43604262927,7164338369,49354886776,32576078879,23347524703,51181016586,
   17166362373,37454539991,46417937292,745867678,46497199761,35721476222,18023290610,49659134639,
   21038094266,33167212356,46949189875,3157314630,44599713814,37305844937,16047035727,
   49265860308,21423230729,32557872859,45932960396,2614392849,43713144299,35865452340,
   16556164168,48520011845,19824846610,33942634432,45060350241,714251103,45474644818,32640620405,
   21248790105,48030654708,14193750515,37448476217,41800902304,6848179432,47113219339,
   27449046186,27642070326,47555519147,6232251990,43247924628,36959188037,16934676311,
   48908214330,17916451105,36150578677,43794391016,5150151456,47901499649,28721320528,
   28306657506,48883254079,5363944004,45580700376,36802410281,20412429369]
private def pvm_w0_12_p2 : List ℤ := pzig
  [50925771896,14648697047,40978039475,43075623536,11545697796,51567258831,23760048320,
   36136963600,48704158077,3788854057,51861961914,30826318601,31701872035,52106701758,2875131063,
   50457163467,36627275028,26434094698,54746418189,9639725720,49281249704,42272646371,
   22455395691,57502215546,14429010493,48780168859,45887015990,19600924890,58766150285,
   18103046930,47628681670,48984551729,16840681891,60551960076,21352540959,48115808301,
   51838167402,16496845508,62628899857,22043347516,49454860606,52685855063,17241760521,
   63755590296,21950587335,51042952565,53591784742,19193102660,66090771081,20209788886,
   54931964460,53001955733,24105394419,67551481842,15538652501,58770224715,50266033672,
   29683791084,68257088883,9844253486,63538884300,46635986273,37777616391,68657762064,532947289,
   68887777039,39057239052,47376338450,65675052615,10960624535,72252565626,29116540691,
   56971489533,60800656768,24605575780,74852305209,15186739166,67421404328,50895511243,
   40895701683,72529822062,2918017156,74333591695,35997047498,56138860804,65464203797,
   23102278623,77973381062,15957882709,70670005757,51052028524,45795198934,73608754255,
   9804883983,78493024044,28476243235,65007606715,60110094538,36741336934,78122484697,428190589,
   78933280202,35801898771,62885106991,64306999132,33858963882,79512780763,1827343522,
   78880471132,36912131143,63137269619,64711912756,35823123942,80358428059,2344721165,
   81542483046,31201709425,68687015231,59175987546,44595406842,77299916107,13714670883,
   83202173600,18795475465,76572815799,47989428754,58973537746,69891343963]
private def pvm_w0_12_p3 : List ℤ := pzig
  [33396448939,81971096380,3680528604,83303978015,26111145154,74447259580,52267188113,
   57118984049,71888651218,33787172558,83183163441,7266621371,85560239248,19617592097,
   79524662673,44287879342,66405674638,64613946125,48002268717,79076704974,26248426598,
   86889413999,2985814409,88033630696,20128162275,83160637375,41626234606,73352743624,
   60246816747,59817996049,75029502886,43651194872,85467570463,25771662245,91598706828,
   7030775114,93908607687,11658176750,93045611272,29352976343,89522294693,45323760166,
   83643785798,59313717107,75733043417,71528754262,66415350536,82274869797,56588230857,
   91560142798,46988601684,99130697083,37790111989,104986300328,28795955408,109748542759,
   20138694199,114237902378,12578377092,118633875671,6786743137,122463866026,2522558494,
   125718046405,797165546,129380159892,2678696261,134059468465,1843050926,138833051440,
   1746169788,142935488079,7098549365,147415292122,15084849640,152488970455,27643856031,
   155655779606,43762794712,156162564319,62395868569,155145777874,86293738542,148684507907,
   113908045587,134177824402,141565941390,113544857901,172244303741,78840109916,195794162176,
   36197382867,214361135875,15392484087,238440709368,119283398812,203231398605,301888342117,
   272933915325,554029606423,869858002939,325344625960,5479121037640,17675079936140,
   41042935838144,80810008312992,141810607496700,225933799423070,330185247939686,446346443358352,
   561904223740786,661734737074382,730669261729826,757011812297576,736003767160466,
   671493567031832,574784631152318,461245304660428,346324633348952,242445989727682,
   157386195154126,94043263075800,51238709143898,25155151879584,10958880198204,4148104856188,
   1320783524352,333722826434]
private def pvm_w0_12_p4 : List ℤ := pzig
  [58018913188]
private def pvm_w0_12 : List ℤ :=
  pvm_w0_12_p0 ++ (pvm_w0_12_p1 ++ (pvm_w0_12_p2 ++ (pvm_w0_12_p3 ++ pvm_w0_12_p4)))
private def pvm_w0_13_p0 : List ℤ := pzig
  [9856867,41138733,133368597,251848843,599781793,409355843,1536532267,1306986596,4101083455,
   8528127534,14178637493,25763787630,39893451875,56775315796,76434160993,90824133258,
   95960328791,88244811344,61492886155,19720809754,26554698514,66837180663,85678348170,
   72203350759,31655336856,21235439568,66130295271,79963289050,54115648743,2513095222,
   49583202668,75459758775,58223544036,6974103195,46467106977,70710249232,51616852583,566151319,
   52087535132,67081273469,36285820276,17883150508,58838756617,57789046646,14197700821,
   39191775251,61392254312,36989293133,14365299885,54060949530,51121042417,7026610576,
   41927900960,55182697345,23280747140,26537247086,53764172005,35705970408,12966442608,
   49840068683,42377838026,1717402558,42993163317,46014609810,8503909547,36644385585,48421203640,
   15474141053,31320076181,48253385974,20529636727,25576797651,47746766920,25229846581,
   21493424997,47819308824,27853872821,18877760193,46814428308,29468738399,16069733437,
   46170635908,31433840845,14608224013,46630240092,32116970769,14573798071,46474161676,
   31937696485,14316030921,46473926888,32265505721,14916038205,47606227220,31729411605,
   16977838651,48313326100,30044342505,18937634619,48637278456,28624568033,21224322733,
   49795424424,26636644313,24897896585,50644660722,23151626115,28683220713,50452586334,
   19424224351,32180956269,50415598066,15417588065,36595695081,50086426392,9851587155,
   41223646571,48150334878,3508472947,44883900269,45392468444,2766417428,48437457577,42225584134,
   10053992584,51944306555,37280134132,18259781498]
private def pvm_w0_13_p1 : List ℤ := pzig
  [53854369311,30642245422,25907424978,54254136741,23467311796,33271877840,53905566073,
   15064656850,40875439270,51629278363,4890272364,47230208810,46705361845,5606614875,51545853698,
   40256823805,15892599725,54598094780,32232691669,26664643143,55678283186,21656667635,
   36829282895,53376226372,9549140679,44760454009,48315530564,2738275902,50745224313,41133842800,
   15582233402,54642338449,30873234026,28451152882,54739303129,17863909100,39209708420,
   50794736721,3997463010,47195429942,43890121823,10254519675,52617332742,33639072967,
   24744895597,53995880336,19786544639,37319062461,50212025350,4316255777,46199168125,
   42351504700,11133074726,51470234255,31023133284,26273823108,52333851179,15922854886,
   39335544224,47249908007,1219936301,47701957894,36957995913,17648490421,50878270076,
   23197386453,32300506253,48945360378,6407741511,43919701499,40766779690,11943113696,
   49729992145,26780962962,28382147528,48585401123,9731803700,40714474970,41450358827,8494540743,
   48118056284,28525837001,26374517153,48573508478,10487255447,40361056973,40838417076,
   9166832672,47401297981,26798654470,26874319474,47144963855,8731524696,40774010812,39327074951,
   11690888441,48101018770,23720650911,30587427881,46024682906,3328480669,43305671809,
   35173553806,17296242468,47973617459,17950301050,35156523748,43788864771,3695216277,
   46809944822,29865824693,25623957673,48153959810,8720305817,41844859825,38629488830,
   14201617208,48967315465,20819706972,34570970904,45720539049,2628357389,48165439388,
   31069302355,26943538143,49975111416,7612057729,44817844965]
private def pvm_w0_13_p2 : List ℤ := pzig
  [38776430228,17964025740,51531196841,17856738326,39686315234,45702108197,8701296565,
   52425919730,26995882649,34768188733,50803206180,762791058,51617536473,34061232450,28857926008,
   53821609749,7369637012,49456690736,40914494735,22716822807,56834156266,14716413875,
   47979945615,46464919656,18044972264,58637848393,20152844438,45800623182,50277601995,
   13204257337,59465039732,25561262813,43698014533,54362227500,9367447324,61241918075,
   29505482124,43265345064,57101789339,7574838999,62218831774,31636332621,42669616871,
   58874905248,5994616298,63448973389,33652051724,43523682536,61081339415,6648838819,65871202468,
   33294708747,46182996115,61423529132,9251134044,67369123547,31482630954,48947455470,
   61384643689,12737719855,69880981708,28483004791,54065038061,60380390578,19481441984,
   72049942639,22030973086,59616446544,56534368399,27304741643,72693608938,14226324079,
   65393554833,51570378964,37157054332,72956402613,2950479280,71882234508,42413740145,
   48907273381,69253014198,11179609096,75613633291,29992759374,59903867192,62651381245,
   26957565569,77660004000,13668558389,71139362731,50620344738,45260061314,73965081391,
   7315627359,77786864870,32515455473,61510286595,63995731902,29719835830,79442482927,9330759020,
   75476559772,46005013669,53554109597,71709011342,19279601642,80844499607,19199594054,
   71872669010,53233333367,47341047563,75621516114,12991459498,82049703015,23736171084,
   71755529930,55397325027,47380450607,76043461688,14143702358,82241695371,21402868248,
   73474472374,52734361877,51932987479,74546514178,21839585106,83579406395]
private def pvm_w0_13_p3 : List ℤ := pzig
  [11496519138,78969623258,42673778623,62133642839,67061751448,36272045756,81415120761,
   5640969209,84189388510,25241516907,75567443733,52300430880,57243952220,72410093425,
   32032598729,83653103804,3367320538,85347758311,25228363736,77907993266,50626432635,
   62618036427,70457618294,41387755864,83293548701,16515660365,88629134412,9550587541,
   86705263139,34475073434,78264820766,56305002819,64349253691,73691757326,46198242892,
   85974195325,25227629967,93073498062,2986637700,95248060409,18999451400,92857208580,
   39490731605,86291266203,57751769696,76096223578,73544177033,63127503621,86855552142,
   48488371426,97580624895,33183389189,105482412930,17751982468,110524994567,2291532471,
   113217688876,13060591657,114453600479,27716228018,114851071604,40925945067,114379233415,
   52553283582,112938924614,63205952963,111242778497,73212518098,110501626718,81850203461,
   111025168993,88402774884,112121271786,93551021573,114054580969,98095066498,118470681756,
   100777568303,125543322625,100189771012,133674660688,97507298767,143726813547,92558329274,
   157400481710,81780970703,171616710997,65770230952,185526193174,45150201495,201054296259,
   14230046334,210564700920,21275532788,219740279957,72720466033,217471678586,156491568716,
   127231185957,143920869671,343323767,361908640043,1341176916983,1863216109629,6155593454,
   7035543838314,23707589500730,56556589121872,112441039048000,195373498864202,303887004982314,
   430000865555898,559560208663448,673905541773250,753465989608678,783066144904416,
   756903944222974,680546864945642,568891195045962,441352882690836,316626218470166,
   208796566795890,125484148041140,67937803166910,32625926221616,13600971998542,4762301848190,
   1320340335360]
private def pvm_w0_13_p4 : List ℤ := pzig
  [251155015886]
private def pvm_w0_13 : List ℤ :=
  pvm_w0_13_p0 ++ (pvm_w0_13_p1 ++ (pvm_w0_13_p2 ++ (pvm_w0_13_p3 ++ pvm_w0_13_p4)))
private def pvm_w0_14_p0 : List ℤ := pzig
  [4285367,9137130,105637057,189091018,987340633,1754641390,5402822125,9394536468,19770654931,
   31955514680,50485109279,70982844546,87970847747,98539628726,91632515721,65325573958,
   23128494425,28601706475,70408968056,85573767309,68112734820,20123752045,37602412197,
   75143074496,75018036133,35480797388,24776970784,69223642395,71061922492,30634949753,
   28840743563,69557341458,62215812201,12753872382,43442344554,68599367181,44343306310,
   13020397622,59165303033,58689725156,14036670329,40312780447,62666814566,34061276825,
   22190430785,58231069168,45089054165,4573925187,49624043048,52045297615,8878550036,41385347662,
   53500321127,18212250810,31936548982,52946724049,26000220090,24918593670,52102753107,
   29895255602,19542270870,49380994785,32721708658,14531161038,47981013875,34937789990,
   12349609106,46931143553,34936436988,10776633514,45314983609,35364579270,9680425434,
   45460289721,35373086346,10778026770,45632359425,33876305046,11892293814,45426343573,
   32993866106,13411502018,46613980329,31547872334,16682097804,47461382529,28649151952,
   19787348068,47634685117,26080117076,23063779434,48639158397,22831953188,27733011138,
   48973415467,17964885960,32100405702,48061398607,13092215348,36099039902,47302401193,
   7672406040,40931108824,45599615513,633877578,45163558914,42022868009,6538204019,48148705502,
   37910093449,13681882437,51054792256,32817370429,21912645289,52908628612,25571750467,
   29987822095,52524334746,17390114131,36938921109,50946565700,8733003493,43723846515,
   47979188234,1495295162,49610661751,42238789692,12360082852]
private def pvm_w0_14_p1 : List ℤ := pzig
  [53031033403,34538578498,22459131034,54592840405,25721902374,32415093624,54417271229,
   14798879358,41825394962,50959727513,2260545044,48772294850,44440256603,10094473715,
   53201033628,36039941929,22318082167,55514209344,25100102781,34337347293,54215443658,
   11608180237,44083061589,48800351740,2434493472,50636428845,40593993876,16249751440,
   54489475273,29565250654,29915538536,54502433515,15339335458,41511970496,49515995869,170178681,
   49221817652,40700621051,15206393415,53291703584,28891461859,29614209557,53215672640,
   13759037013,41888840035,47545412070,3111790176,49562203413,37042022186,19071073536,
   52296683921,23461673930,33254985476,50335619177,7120106024,44660120082,42575954693,
   10745877465,50708034626,29366929835,26945055173,50373202972,13224183207,39584154453,
   44577727876,4320114832,48039165659,33297727454,22110594036,50342170809,16853755886,
   36951903750,45127345851,1767604781,46033652376,33868209909,19564450941,48947914744,
   18210079739,35072062739,45071228412,876688512,45705047405,33531637540,20239973410,48449265733,
   16353527060,35720640632,43203915253,2938197847,45410321120,31297195201,22123874887,
   48006124454,13419385647,38253603355,41552558786,7718074024,47027971705,26787344596,
   27102546318,46628549847,7322772546,41314714742,37819945629,13846356691,48309890692,
   21162112395,33416122111,45339510796,1038539390,46136222199,31969455324,23169544512,
   48588584627,11780598282,40298022050,40928550635,11263118295,49527669346,23920296335,
   33217486187,47633317406,78413030,48006050397,33488353406,24715785198,50896128417]
private def pvm_w0_14_p2 : List ℤ := pzig
  [10951320590,43476015298,41681495523,14628632667,52548921348,21892366617,38173881117,
   48629226174,5236182488,52747628571,30758430108,32078804498,52828718273,3915973278,50470321670,
   38612845463,24504002891,55953467284,13358346621,47817570139,45928713482,17681056728,
   58376936197,21023335198,44897331734,50995391703,11245932569,58793656790,27888970853,
   40741714245,55406284148,4463563058,59259432959,34514971120,37611726266,59508384427,475678212,
   59786325606,38996596997,35035986347,61796727530,4625795637,59292093037,42963831922,
   32331300036,64350707373,8290941628,60088401874,46329313695,31788407559,66651305492,9436740121,
   61188406429,47499267030,31959338148,67670490501,9897286258,62204538880,48550068435,
   33131051799,69536417938,8718735851,65112058665,47923772150,36935279852,70221574799,4774136510,
   67625617358,45126373139,41100803495,69958790664,29399287,70755109159,41563551676,47398509934,
   69427673605,7933857527,74410068120,34406035761,55047796429,65750360738,17820523498,
   76117938047,25240024614,62453393726,60583993701,29300990389,77428336184,12931153443,
   70936912423,51403766456,43400285134,74801427881,3211882105,76582443556,37880264059,
   56621473625,68301728370,20902385892,79881185485,20483379464,69897763444,56322413807,
   41488110595,77339040696,2457633540,78498365515,37032203718,60019045680,67184488439,
   26964633253,80958528224,12334051317,75570486307,48507495298,52835122760,73412783069,
   18399544905,81892602510,19821671365,72678840917,53556619998,48340064116,75963838175,
   14405679049,82925867188,22034980497,73640031289]
private def pvm_w0_14_p3 : List ℤ := pzig
  [53889947834,50478710734,75433491697,18246290659,83237447856,16939197695,76548558755,
   48874843458,57128308072,72368264169,28675262977,84018922366,3993110379,82589628289,
   35814589282,68960742990,62259633613,45736116987,79913028654,16623879710,86816403141,
   14260103528,82571577646,43026040695,68230156377,66479204580,46007022298,82380632909,
   18864824897,89517872020,9968473219,87647490017,37467822954,77378984378,61174238953,
   60040328237,79380507934,37518470358,91122588427,12038871783,96036522998,14133050675,
   94196704603,39019920208,86040315268,61173676491,72392455775,79713888642,54488715764,
   94152057739,33847757729,104151057454,11951186968,109446816475,10105227334,110031574690,
   31705996343,106410462043,52435614336,99566695672,71695224583,90495520543,88710391270,
   79704676694,103061689443,67315226153,115127036006,53775489688,125669446127,40222543729,
   134872497126,27692740336,142258460401,16130519937,147964799990,5040510344,153355567407,
   4820359210,159308680532,11932214075,164946951949,16508169598,170048126798,19640909827,
   176624761587,19629455532,184754260270,14523612309,191909427155,6350413042,199740609058,
   6173746282,208885434011,26906596341,214130269962,52205380564,219488315947,93341652115,
   204155932462,133774817040,143894524725,54266973811,272692803520,27893860874,1108514331991,
   2457388649419,2745098200623,281195715454,11427751699006,38670326388160,91047743996378,
   174826309739890,290103144237674,428756493845548,573863034360096,701606761214654,
   786848761049256,811163530261592,769472306117958,671652042790336,538605373580054,
   395251399912036,263610608553952,158121884115052,84033297965164,38723358485986,14966047794390,
   4571205718204]
private def pvm_w0_14_p4 : List ℤ := pzig
  [955603789010]
private def pvm_w0_14 : List ℤ :=
  pvm_w0_14_p0 ++ (pvm_w0_14_p1 ++ (pvm_w0_14_p2 ++ (pvm_w0_14_p3 ++ pvm_w0_14_p4)))
private def pvm_w0_15_p0 : List ℤ := pzig
  [26378757,147388858,585464735,1789214012,4754691677,10545770138,21324838287,36804188536,
   58540550335,79401286118,97278708545,97986201120,79506498165,38055786700,16924527290,
   64263194103,87604814794,70836007369,19657229976,39613870168,78801837141,72680003060,
   22693982563,38857328455,75680154052,63069744875,6678148586,52378651280,72670677893,
   41300770876,20829690878,66489655021,58796303336,5993351373,49729504775,65351827458,
   26847849727,33862148983,63743685456,38860488473,17819323017,58508571468,47333340819,
   6519634355,52943080362,49848927261,2310590264,46212994348,51811735447,8472434626,42457329254,
   51350800879,11129119170,38223514540,50231940423,13660619220,36397847256,49857343747,
   13053646938,35816550824,47726016155,12149623880,35174104296,46977616601,10519538534,
   36934011722,45529418897,6786526340,38147823088,43217614845,3714950094,39879648124,41864186759,
   804778509,42770628222,38804681359,6370577277,44308009640,35233340505,11270527083,46254648048,
   31726469515,17615479221,48106672328,26123755003,24147046275,48045963920,20052011775,
   29782541479,47788484880,13614574691,36197809269,46480940110,5233684835,41874442531,
   42753890394,3334866444,45875956511,38238572542,11861245000,49562739711,32299677346,
   21501516776,51538035467,23862492106,30467579624,50824588163,14642848416,38113429776,
   48758941585,4621827832,45398581864,44468239015,7028712551,50742027578,37016712915,18474908307,
   53122099734,27977959577,28949562399,53595012070,17409853379,39137063899,51274112750,
   4595292311,47408907949,45092861754,8658027590]
private def pvm_w0_15_p1 : List ℤ := pzig
  [52421323499,36460421200,21211759422,54970739717,25715428058,33533907128,54311798111,
   12160446236,44060498062,49128508881,2502379569,50983268794,40604485907,16602061253,
   54779787204,29528773091,30322699627,55005715832,15294415497,42298223715,50146135992,608383628,
   50255141139,41056914378,15906696440,54217362863,29102565068,30307265500,54182600709,
   14009618706,42757221676,48680623359,3021926323,50696674226,38163394603,19188999901,
   53556652334,24595531207,33465192181,51837777750,8409376471,45136835819,44537812042,9446092516,
   51731456321,31768679980,25884399836,52079639063,15981026732,38971160656,47130553857,
   1313228795,48230724032,36859715065,19200077539,51792738240,21344750209,34702411133,
   48164405756,3297864713,45075209783,38620772582,14512180460,49916693979,24541476108,
   30869142512,48490912729,6509320884,43357016808,39613307149,12750949929,48939395458,
   24818027587,29429635005,47241896652,7041414791,41766538761,39073610920,12053150224,
   48338462523,24428917270,29946441740,46762580509,5188262094,42505395416,36962099507,
   14425031643,47591828342,21475190563,31429801257,45180927610,2246529879,43781632655,
   34708023050,18345339254,48210490799,16999522904,35576680172,42987164513,3823368413,
   45657941794,29884620713,23694726875,47553192256,11112677167,39882172057,40302607576,
   11010296572,48518493043,23846195234,31468342450,46449494467,1988406374,45005899674,
   34554141449,20166605571,49448130534,15415398835,38967578077,43618078860,8335873898,
   50065416365,27013049138,31353674212,49245023299,3289179910,47058559922,36652503661]
private def pvm_w0_15_p2 : List ℤ := pzig
  [21291909647,52110134842,15519297235,41832187393,45337524918,10619127472,53469039907,
   26458866912,35721577524,51396205539,427614019,51957370408,35580145651,27554093277,55039633712,
   10479983351,48481045037,44278120680,18702178284,57874829377,20561210146,44685539792,
   51068877749,10555521687,58549176616,28970444057,39267268695,55812095166,1705002558,
   57604587497,37331929092,33272479190,60321742207,6536849950,56865804262,44257065073,
   28262798159,63208104820,13137076497,54903812187,49402321888,22682048864,64826848177,
   19829408556,52651347136,54626856235,17852999493,66995616710,25075792671,51645742263,
   58289470320,14796608148,68014942241,28533845788,50141715474,60775621589,11751614851,
   68937167414,31897303469,49721320747,63569600582,10659595700,70864007959,33036666624,
   50943829784,64516361111,11432101143,71773607402,32715966693,52083581471,65005480016,
   12803302020,73567696081,31597810096,55394906700,65005754551,17184857007,75513970998,
   27341458273,59534097007,62505701340,22796961866,76203787077,21936008280,63948903758,
   59470464667,30122562389,77378729106,13821124557,70013632337,53405211304,40080920154,
   75951191617,2580828392,74553425618,44426144221,49994823023,72589241660,10150372060,
   78790235243,32747251142,61598365284,65979644581,26500022071,80099878642,16066938881,
   71477717405,53964981520,43000741058,76849151897,2896196019,78895418928,37825341605,
   60084108039,68474590342,25831762590,81450017107,14764890564,73972601084,51472549525,
   48448708145,75520991794,11515581282,81605181467,27850532102,68870021618,60600803507,
   40762202393]
private def pvm_w0_15_p3 : List ℤ := pzig
  [79675529998,3919712898,81408638405,33530282070,66037630766,63813897923,37318540233,
   81078490484,1444761576,82394440875,34409088664,68064070238,63565945377,41272745687,
   81046026850,7241477582,84292553601,27890822136,73357795470,58215141241,50603347081,
   79023797564,20053774376,87462176299,13418887200,82793008338,44910293015,66280027395,
   70171274570,40762027528,86097234155,10034951089,91000506788,21817907061,84678907441,
   51014932480,68304410748,74490657479,44155478585,90104354068,15221681916,96677703993,
   15268420604,93938608034,44310735853,82443331565,69473243628,63497325366,89043531537,
   39029502739,101972428270,11351205432,107715869355,17209792534,106133756284,44689471405,
   97540923839,69688026134,82831754562,91268106347,63451588729,108665737192,41051773086,
   121146677523,16980442057,128253914382,7944037839,130237737841,33088519912,128070181002,
   57468163801,122764209263,79844780416,114688153824,99614177361,103928963425,117287414312,
   91410829742,133468389861,78868880311,147622632466,67121441692,159091369855,55564360793,
   169075215578,44673304248,179155892007,36776198235,188274592724,32092776462,195713487953,
   29016143511,204377147432,30394949164,213606028071,38289279383,220263440310,50331478422,
   226453607767,72261435415,216194587148,73124501504,220421723625,16469093781,465185912162,
   363253162138,637031682937,2212366795033,3934334405257,4154679691861,2469413436256,
   25710011378932,77116519075372,165497056053522,292434337983258,448480914137100,611415966864268,
   749517224637192,830998525077414,835849056452820,763552015324730,632683140601686,
   473433467334500,317240616389132,187786183916890,96167235336174,41220650214390,13932956316410]
private def pvm_w0_15_p4 : List ℤ := pzig
  [3215218325602]
private def pvm_w0_15 : List ℤ :=
  pvm_w0_15_p0 ++ (pvm_w0_15_p1 ++ (pvm_w0_15_p2 ++ (pvm_w0_15_p3 ++ pvm_w0_15_p4)))
private def pvm_w0_16_p0 : List ℤ := pzig
  [194164283,966600898,3294229293,8828554108,19662018031,37230364196,60765732615,84967956104,
   101023793959,96658065482,66974038835,12611789004,44754242718,84789977281,81100745228,
   36109451263,29094306973,77505609188,75118531945,25690069428,41075971378,78758742627,
   57446009088,4412030638,62062337277,71428525348,22464534881,42660668613,70814558696,
   40595447925,24451273123,67123365774,49027741839,10838514757,59518758574,54369362907,
   1339274809,54594921806,54622469165,4169489796,48768174828,54887572725,7289589946,46755626000,
   52781767419,7039788834,43988703468,50884842393,6458484598,44425784980,48448270087,2515818100,
   44280042428,44775877295,634269725,45380899832,41955879447,6411223641,46951447076,36599944751,
   11992143815,47199547398,32028867843,17962032665,48581995342,25603959453,25203552723,
   47593567270,18058762493,30782164637,46170230340,10700876575,37209311179,43681199328,
   1103655701,42349332521,38370844014,7978634722,45559117477,32691516446,17234277610,48387853505,
   24720326320,27166923272,48142947061,14794778294,35070252132,45711757475,4832152684,
   42218998068,41701347049,6815323521,47900889134,34131942891,18590574571,50077276816,
   24742317437,28933377393,50200574490,14033389241,38954752779,47437091844,973932861,46743734003,
   40593167532,12150278504,51041090297,31562260548,24498607168,52949656525,20180793722,
   36542578986,51045506747,6087461426,45932841318,44645545043,8247370785,51707690144,35520447749,
   22135857763,54590329514,23385429559,35564282585,52996864394,8282729121,46001873095,
   46431441554,7198839964]
private def pvm_w0_16_p1 : List ℤ := pzig
  [52437478559,36636118538,22179026468,55403919409,23513529418,36373544154,53382152741,
   7311534264,47168504828,45883053519,9222336215,53312800912,34765334893,24791941329,55331082236,
   20364812449,38993707567,51988303360,3044164855,49261688167,42746561862,14299468850,
   54022911995,29672874540,29790960916,53916244333,13786918458,42981260720,48275225995,
   4420228753,51585326634,36584373099,22018147381,53752675270,21120038789,36481436505,
   50285642712,3808574473,47313587343,41415706278,14610499756,52841780211,26874089008,
   31403309470,51170805883,9055886264,43507954120,43259141517,9115839405,50335907136,30517645745,
   26459154229,51190601198,13296658653,40738024715,44598181480,6033649838,48751606259,
   31668963960,23730045362,49825047383,15091060290,38014729520,44526904339,3748043003,
   47450483950,32453308361,22644218767,49403974112,14942954801,37570774249,43304141756,
   4248585862,46238133965,31093152218,22461516868,48254370005,14066376980,37786251778,
   42449330929,6038527851,46793576128,28810873221,24974893581,47195667428,10516825831,
   39054168623,39834914492,9164183992,46867091393,25806378940,27977897578,46650508731,6263751302,
   42108412210,37082707215,14810435163,47769186296,20372137693,32616294097,44479575618,190567971,
   44628106645,33108917712,20773123234,48637583705,14406223526,38545614642,42298707441,
   8115734263,48163511668,26715350263,28802729815,47722366226,5832121783,43862600807,37843804546,
   16964824830,50646239981,19237293084,37491116770,46164457829,4920803123,49891882836,
   30564364167,28247335225,50882814496,8066583389]
private def pvm_w0_16_p2 : List ℤ := pzig
  [45526403811,40852094072,16880404534,53555366067,20936481456,39568947230,49096305387,
   5562170735,53422712172,31787614125,31436172109,54010210792,6380729005,49930613879,41686423256,
   21169366332,57217220045,18606082956,45182855562,50273269515,11058396157,58462662620,
   29019282031,38936240307,55949586120,626455434,56746273759,38582856148,30680752936,60276389271,
   10371399086,54127988312,47475915655,22697151823,63424496160,19772686901,50655793955,
   53916950260,14689462664,64091415791,28422724856,45439411994,59375926219,6027259899,
   64266724712,36818662385,40736391231,64233343598,1067077975,64104343835,43021503348,
   36291980276,66959213855,7417370066,62483342266,48477129329,31322373327,69528659780,
   13538211297,61691366823,53437074366,28153413514,71861916481,17320543036,61209162810,
   56190286627,25738937927,72738839050,20347802725,60333115981,58763949268,23886648834,
   74443989539,22308900818,61365526070,60349196497,24671884125,75691654450,21567362193,
   62606949685,59909093468,26104946552,76151426987,20222401512,64488663396,59439804751,
   29376888095,77509625364,16398072897,68220506193,56547827400,35113361618,77123448651,
   10101898230,71262473438,51876500567,41264024941,76240190322,2547552371,75399432771,
   45577499066,50035229920,73910509107,8704026887,78754149042,35255629781,58982865275,
   68137551600,21119562726,80114850119,23040665462,68019860442,60247633043,35932199701,
   79785132640,6415562833,76436683121,46756521896,51655649874,73896453885,12768041151,
   80743237544,29385967807,65972268833,63574928638,34007602708,81147688411,6506863848]
private def pvm_w0_16_p3 : List ℤ := pzig
  [78085055034,45190262447,55696672603,72624404140,19930509032,82569830737,20383512998,
   73209243462,55812239231,47232625103,78521912082,10881720510,83904355357,27700615462,
   71327857334,60361031953,43953143627,80625010568,7769699004,84855346835,29846218470,
   72715357762,61693321425,46942909505,82096428500,12578057302,87809125341,24132648726,
   78356489286,56912476501,55835048775,80498707578,24291243938,91402336267,11138665468,
   88301738506,45132001969,72055624839,72963765558,45376771962,91071448023,12252761459,
   97371104060,22766590155,91350188207,55277230862,73985910524,81592821583,47528642303,
   99089520968,15166187570,106305364785,19423777142,102859075952,52596150763,89304564139,
   81237729628,67016627810,103099602805,38107752599,116853193266,5268186266,121900448181,
   28589729120,118140451178,60850175181,105934768813,89614973840,86302404912,113711931949,
   61032515547,132290420936,32319258838,144497717085,1995932717,149781600308,28886746201,
   148586788235,59520721102,142359427506,88508140635,132373639875,114269265588,118870003640,
   136574621281,102239233311,156540501954,84531126578,174241216759,67733361363,188405084294,
   51273769734,200090865183,35142761573,212029253086,22832094778,222674299313,14612292955,
   230915106312,8343162246,238897456265,4139854073,243160637700,24166206727,308019059921,
   19377279236,551684077526,548661595870,87058263531,1513766676591,4403093054755,7583429834219,
   4643208612421,16617893396120,70982450291120,170437755604894,317427280775096,498016659834166,
   679738567689762,819290868074250,878766171560492,841644815222176,719393954135112,
   545908713115452,363711169462520,208712210084720,99893351918948,37584327857230]
private def pvm_w0_16_p4 : List ℤ := pzig
  [9624419295722]
private def pvm_w0_16 : List ℤ :=
  pvm_w0_16_p0 ++ (pvm_w0_16_p1 ++ (pvm_w0_16_p2 ++ (pvm_w0_16_p3 ++ pvm_w0_16_p4)))
private def pvm_w0_17_p0 : List ℤ := pzig
  [799492363,3538550652,10614738733,24747121646,47110323965,74547580302,97804232841,103177935840,
   79480700607,26615747628,37280971904,83406587219,83174733074,36055525121,35044412103,
   80021435568,71611960773,10617435252,56701837596,78753303787,40193255928,31791650588,
   74880206269,53962454960,11450864460,67043261929,60912191460,129695216,58234704971,62560205304,
   7909459393,53729179689,61134077550,10162534255,48929788829,59779974746,10284791175,
   48559488629,55952217150,7352625455,47303179973,53167954030,3175256901,49280867539,47956879232,
   3147442212,49352623771,43118159926,9457936668,51458533301,36259679346,17810092660,50797423113,
   28467232076,24564019872,50605610037,19910656768,32952292208,47749841433,9177348312,
   38617683426,43192757565,640242689,44191042196,37246166445,12502637625,47267434248,27861631987,
   22660117829,47413187880,18297350551,32367780799,46022901970,6051572035,40816213861,
   40146550862,6536057780,45583336053,32479735064,18471468504,48713910397,22098518414,
   30738355742,47567503533,8911337298,39897242042,42563110709,4136459367,46680761762,35069165869,
   18200449989,50526912416,23321151289,31299954973,49174985518,9685675435,41281121717,
   44441531818,4686636250,49073287025,35786146372,20170015720,52444507171,22777123058,
   33635520786,50576585197,8231296800,44167176586,45007478377,7600027745,51820196700,34625626021,
   23892276749,54051370816,20192079393,37420133885,50945801568,4395676725,47738955167,
   43655652208,12585806814,54268771767,31225067522,29145262700,54650028475,15154262408,
   42144127172,49454694475]
private def pvm_w0_17_p1 : List ℤ := pzig
  [1866905479,51247195956,39807220293,19425064721,55689496500,25147312167,35536243019,
   53420166328,7435980977,47106954377,45351254218,10409236092,53839307151,32947246222,
   27672669876,55191709891,16134920370,42326992324,49506839225,2847643583,51328866328,
   38000099669,20716645897,54452925464,22762964011,36461189577,51745536170,4292581495,
   48337271701,42099898388,15086579556,53493685935,27003422938,31743811436,51837628333,
   9335557236,44402882102,44309917395,9733553207,51939794536,30606887603,28027495257,52012627186,
   12425964641,41806083785,44732184984,6603591646,49599081079,32115094298,24559297850,
   51205168227,14967269634,39672369114,45272093249,4886847587,48583855534,32224307699,
   23382797133,49810710564,15116669103,37899839909,44264329682,3902228662,47316127079,
   32122099126,22963953044,49353279841,14301302308,38184013094,42886047195,5430919563,
   46581652176,29946149287,23631498099,47871265462,12622762421,38490836715,41595126366,
   7462879766,47139631699,27551013240,26445595592,46961993167,8687157284,40132341646,38658373269,
   11058650307,46989685462,24092433575,29285855105,46024971236,4573784133,42858389803,
   36019785690,16452882442,47955992735,18779202198,33950231722,43772513671,1567813473,
   45071785994,31809239787,21966106747,48326710880,13226828089,39146983571,41771850992,
   9083134368,48453441891,25993773248,29589012864,47537595835,5052964766,44067978834,37378628557,
   17183667317,50421275644,19253287715,37189154711,46304586010,4329231116,49771113063,
   31267890400,27563982768,51153946755,9157707814,44824735902,41657164623]
private def pvm_w0_17_p2 : List ℤ := pzig
  [15164274083,53187707476,22949542747,37569488729,50163293528,2408174482,52465600387,
   34676643624,28327079862,54902174145,10443121450,47786010066,44551293217,16466449665,
   56840831198,23779146999,40868866921,53068106564,4171761930,56744000507,35385651892,
   32638428024,58354551089,7802557862,53226685294,45053655679,22080416875,60975575524,
   20376860459,47596252839,53865834310,10975071756,62252558725,31667696936,41253681064,
   60129355337,480271035,60779976316,41090943201,32971907817,64017160158,10666457545,57447125905,
   50113652576,24126539474,67207086287,20902530294,53957952600,57216281723,16143522297,
   68296721104,29374073979,48949200313,62280388092,7553049122,67880684265,37755310106,
   43551020612,67148399781,219038654,67783652370,44522579497,39293076761,70289924082,6206194775,
   66453733059,49437712306,34539631190,72211191959,12157671540,65023312518,54300615217,
   30857244427,74596318202,16266666885,64830918875,57211161710,29015735376,75543105011,
   18481149276,64034325080,58872171545,27305005445,76435170328,20270476155,64543118515,
   60369803110,27964387696,77829841619,19273878986,66280277286,59430976741,30252387959,
   77752569814,16839648299,67780948497,57878083704,33408223482,78320206495,12883385054,
   71257841760,54740091639,39538920251,77770819142,5606021565,74400152639,48731643364,
   46142827682,75535351649,2707406775,77527174222,41550298443,54520020811,72470783586,
   14292072362,80573131165,30255268560,63781873944,65352635961,27686544447,80599306710,
   16544706301,71892662023,55771766732,42285228186,78810228483,698703747,79509168648]
private def pvm_w0_17_p3 : List ℤ := pzig
  [40941312863,58177400067,71192531860,21112320848,82177023823,21458351268,71455682718,
   58312948975,42315212421,80188332324,2554188548,81984702399,37764069576,63744055650,
   68917791175,30291614467,83813686892,10227393473,79442440967,48447673786,57258306876,
   75964818185,22524027549,87097722300,17106598755,79894895099,53365424092,56259058874,
   79085170427,21270091331,89510939170,18057882711,83004125159,54267477576,61089915564,
   80874874475,27933613723,93450832820,10580035333,90207375333,47953852668,72050891454,
   78169436057,42172046017,96597960106,5321484642,100615673861,33046168476,89860461636,
   67592534569,66116739435,93766000070,32870225272,108277410179,5367371070,109389243534,
   43812050713,97040164453,78068594588,72799698248,104568780503,39612893509,120761551138,
   1307198118,125153833867,38071748788,117353337740,74891484787,98171249199,106274444130,
   69642031866,130052966793,34705606251,144570260822,3504531107,148750754323,42370026302,
   142560958582,79886325061,127314300293,114107311118,105089520734,142867275987,77543828939,
   164649455938,45640668932,179673317987,10933499617,189109902782,23827938263,193010164183,
   56856674696,190933467604,88797081945,185051520845,119259794298,178329019292,145273272391,
   169578922593,167718357776,158465563850,190006516229,146956338137,217993321592,138980674430,
   284681353283,235299774093,283056926336,582016312732,573969899470,200074999284,1967047963483,
   7078831097069,11624117118253,4710583048261,30626994402978,112623648345480,252292068058750,
   442180251983986,649307088293018,821439689773290,907364968152082,880049287882758,
   748869136902386,554731518603914,351748768340442,185165804532226,76336043444596]
private def pvm_w0_17_p4 : List ℤ := pzig
  [21347121109380]
private def pvm_w0_17 : List ℤ :=
  pvm_w0_17_p0 ++ (pvm_w0_17_p1 ++ (pvm_w0_17_p2 ++ (pvm_w0_17_p3 ++ pvm_w0_17_p4)))
private theorem dk_w0_0 : muxFastIterBSlideChk 5 513 phbv_w0
    rkmViHi_m1024_r512_s1_c2 pvm_w0_1 = true := by
  decide +kernel
private theorem dk_w0_1 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_1 pvm_w0_2 = true := by
  decide +kernel
private theorem dk_w0_2 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_2 pvm_w0_3 = true := by
  decide +kernel
private theorem dk_w0_3 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_3 pvm_w0_4 = true := by
  decide +kernel
private theorem dk_w0_4 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_4 pvm_w0_5 = true := by
  decide +kernel
private theorem dk_w0_5 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_5 pvm_w0_6 = true := by
  decide +kernel
private theorem dk_w0_6 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_6 pvm_w0_7 = true := by
  decide +kernel
private theorem dk_w0_7 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_7 pvm_w0_8 = true := by
  decide +kernel
private theorem dk_w0_8 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_8 pvm_w0_9 = true := by
  decide +kernel
private theorem dk_w0_9 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_9 pvm_w0_10 = true := by
  decide +kernel
private theorem dk_w0_10 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_10 pvm_w0_11 = true := by
  decide +kernel
private theorem dk_w0_11 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_11 pvm_w0_12 = true := by
  decide +kernel
private theorem dk_w0_12 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_12 pvm_w0_13 = true := by
  decide +kernel
private theorem dk_w0_13 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_13 pvm_w0_14 = true := by
  decide +kernel
private theorem dk_w0_14 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_14 pvm_w0_15 = true := by
  decide +kernel
private theorem dk_w0_15 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_15 pvm_w0_16 = true := by
  decide +kernel
private theorem dk_w0_16 : muxFastIterBSlideChk 4 513 phbv_w0
    pvm_w0_16 pvm_w0_17 = true := by
  decide +kernel
private theorem dk_w0_17 : muxFastIterBSlideChk 3 513 phbv_w0
    pvm_w0_17 rkmVoHi_m1024_r512_s1_c2 = true := by
  decide +kernel
private theorem dkhb_w0 : muxIntListEq rkmHbHi_m1024_r512_s1_c2 phbv_w0 = true := by
  decide +kernel
private theorem pw_w0_1 : muxFastIterFullT16 10 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_2 :=
  (muxFastIterFullT16_add 5 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) (muxFastIterBSlideChk_sound dk_w0_0)).trans
      (muxFastIterBSlideChk_sound dk_w0_1))
private theorem pw_w0_2 : muxFastIterFullT16 15 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_3 :=
  (muxFastIterFullT16_add 10 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_1).trans
      (muxFastIterBSlideChk_sound dk_w0_2))
private theorem pw_w0_3 : muxFastIterFullT16 20 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_4 :=
  (muxFastIterFullT16_add 15 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_2).trans
      (muxFastIterBSlideChk_sound dk_w0_3))
private theorem pw_w0_4 : muxFastIterFullT16 25 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_5 :=
  (muxFastIterFullT16_add 20 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_3).trans
      (muxFastIterBSlideChk_sound dk_w0_4))
private theorem pw_w0_5 : muxFastIterFullT16 30 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_6 :=
  (muxFastIterFullT16_add 25 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_4).trans
      (muxFastIterBSlideChk_sound dk_w0_5))
private theorem pw_w0_6 : muxFastIterFullT16 35 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_7 :=
  (muxFastIterFullT16_add 30 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_5).trans
      (muxFastIterBSlideChk_sound dk_w0_6))
private theorem pw_w0_7 : muxFastIterFullT16 40 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_8 :=
  (muxFastIterFullT16_add 35 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_6).trans
      (muxFastIterBSlideChk_sound dk_w0_7))
private theorem pw_w0_8 : muxFastIterFullT16 45 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_9 :=
  (muxFastIterFullT16_add 40 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_7).trans
      (muxFastIterBSlideChk_sound dk_w0_8))
private theorem pw_w0_9 : muxFastIterFullT16 50 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_10 :=
  (muxFastIterFullT16_add 45 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_8).trans
      (muxFastIterBSlideChk_sound dk_w0_9))
private theorem pw_w0_10 : muxFastIterFullT16 55 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_11 :=
  (muxFastIterFullT16_add 50 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_9).trans
      (muxFastIterBSlideChk_sound dk_w0_10))
private theorem pw_w0_11 : muxFastIterFullT16 60 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_12 :=
  (muxFastIterFullT16_add 55 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_10).trans
      (muxFastIterBSlideChk_sound dk_w0_11))
private theorem pw_w0_12 : muxFastIterFullT16 65 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_13 :=
  (muxFastIterFullT16_add 60 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_11).trans
      (muxFastIterBSlideChk_sound dk_w0_12))
private theorem pw_w0_13 : muxFastIterFullT16 70 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_14 :=
  (muxFastIterFullT16_add 65 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_12).trans
      (muxFastIterBSlideChk_sound dk_w0_13))
private theorem pw_w0_14 : muxFastIterFullT16 75 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_15 :=
  (muxFastIterFullT16_add 70 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_13).trans
      (muxFastIterBSlideChk_sound dk_w0_14))
private theorem pw_w0_15 : muxFastIterFullT16 80 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_16 :=
  (muxFastIterFullT16_add 75 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_14).trans
      (muxFastIterBSlideChk_sound dk_w0_15))
private theorem pw_w0_16 : muxFastIterFullT16 84 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = pvm_w0_17 :=
  (muxFastIterFullT16_add 80 4 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 4 513 phbv_w0) pw_w0_15).trans
      (muxFastIterBSlideChk_sound dk_w0_16))
private theorem pw_w0_17 : muxFastIterFullT16 87 513
    phbv_w0 rkmViHi_m1024_r512_s1_c2 = rkmVoHi_m1024_r512_s1_c2 :=
  (muxFastIterFullT16_add 84 3 513 phbv_w0 rkmViHi_m1024_r512_s1_c2).trans
    ((congrArg (muxFastIterFullT16 3 513 phbv_w0) pw_w0_16).trans
      (muxFastIterBSlideChk_sound dk_w0_17))
/-- Certified `T_16` walk chunk `m1024_r512_s1_c2`. -/
theorem rkmWalkChkHi_m1024_r512_s1_c2 : muxFastIterFullT16 87 513
    rkmHbHi_m1024_r512_s1_c2 rkmViHi_m1024_r512_s1_c2 = rkmVoHi_m1024_r512_s1_c2 :=
  (congrArg (fun h ↦ muxFastIterFullT16 87 513 h rkmViHi_m1024_r512_s1_c2)
    (muxIntListEq_eq_true.mp dkhb_w0)).trans pw_w0_17
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi1024T8`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi1024T8 :
    rkmWalkChkHi_m1024_r512_s1_c2 = rkmWalkChkHi_m1024_r512_s1_c2 :=
  rfl
end
end QuantumComputation.Specs.DickeSol
