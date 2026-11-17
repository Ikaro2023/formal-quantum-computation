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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T6

/-
# High-`m` Checkpointed Walk Part `7` (`FindAllJohnsonRampKickMuxHi1024T7`)

Certifies `1` `T_16` checkpoint walk(s) (`44118` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Quantized generator list for `m1024_r512_s1_c1`. -/
def rkmHbHi_m1024_r512_s1_c1 : List ℤ := altBuildHbFrom 1024 512 51956169884 0 512
/-- Part 0 of `rkmViHi_m1024_r512_s1_c1`. -/
def rkmViHi_m1024_r512_s1_c1_p0 : List ℤ := let p := rkmP; let n := rkmN; [
  p 0,p 0,n 2,n 6,n 8,n 7,n 11,n 16,p 3,n 2,n 11,n 7,p 2,n 4,n 2,p 3,p 1,n 4,n 0,n 4,n 5,n 27,n 10,
  p 2,p 10,p 9,p 16,p 2,n 4,n 14,n 15,n 4,n 8,p 2,p 14,n 0,n 4,n 28,n 31,n 15,n 3,p 17,p 13,p 15,
  p 2,n 5,n 55,n 14,n 14,p 77,n 126,p 218,n 509,p 865,n 1469,p 2208,n 2597,p 1571,p 3600,n 18587,
  p 54103,n 129210,p 275020,n 538551,p 985140,n 1694502,p 2746107,n 4185969,p 5963277,n 7832613,
  p 9218526,n 9055257,p 5638612,p 3445591,n 21220965,p 50936539,n 95307222,p 155357908,n 228998430,
  p 309660792,n 385547027,p 440176015,n 454841316,p 413184335,n 307314434,p 143898311,p 52248791,
  n 239763725,p 369275559,n 398299635,p 308649544,n 119620738,n 110600844,p 300027849,n 372621001,
  p 292614988,n 87500737,n 155219926,p 322388859,n 329321471,p 167864335,p 80456330,n 280793396,
  p 318001993,n 167384780,n 82268521,p 275814921,n 287868116,p 108858786,p 140650440,n 286682774,
  p 224186342,p 1550773,n 221193126,p 265931380,n 100663667,n 141757407,p 262567772,n 161027485,
  n 75696416,p 241437886,n 189613119,n 32347091,p 220052673,n 198125139,n 12042818,p 206711500,
  n 194389763,n 12382305,p 203347645,n 181249855,n 30981861,p 207543377,n 157227545,n 65567593,
  p 213156805,n 118009180,n 112216880,p 210238535,n 59044145,n 162454370,p 185740567,p 20041412,
  n 200572605,p 127120556,p 109383076,n 204046927,p 30520102,p 183965404,n 151084504,n 87852103,
  p 206306954,n 37335614,n 184840501,p 144120383,p 104532092,n 201749364,p 2301719,p 201140323,
  n 102796305,n 152321542,p 175627792,p 71268885,n 204775764,p 10537003,p 210510606,n 110910999,
  n 139044035,p 110534696,p 189370126,n 325323582,p 166049023,n 136543976,p 538907883,n 1072443751,
  p 1400577129,n 1823514704,p 2876599971,n 4523011051,p 6370923858,n 8561364524,p 11721660468,
  n 16001784206,p 20898711236,n 26177956438,p 32141550351,n 38637278104,p 44589181561,
  n 48947942551,p 51305803709,n 51065566293,p 46940596970,n 38094963566,p 25095220218,n 9144960144,
  n 8606205441,p 26153437808,n 40136911633,p 47412578394,n 46510239479,p 37176672818,n 20132008953,
  n 1594813624,p 22508847958,n 37097146326,p 41794616399,n 34963175658,p 17573235334,p 5242640908,
  n 25488648149,p 36280396814,n 34120293073,p 19221997333,p 3396282672,n 24220121496,p 33971389297,
  n 28722131925,p 10792534936,p 12318594780,n 29506842664,p 31323167337,n 16679338573,n 6449082353,
  p 26092011023,n 31499793526,p 18451185744,p 6056202417,n 26815457683,p 30997189343,n 15958360330,
  n 9798136462,p 29997792294,n 30032469552,p 9062675972,p 18319488326,n 33202875960,p 24704195269,
  p 2568231570,n 28865114725,p 33198815522,n 11724533097,n 19073905770,p 35502673865,n 23517903993,
  n 8747522515,p 34231643957,n 30486066121,p 558816719,p 30301928135,n 35090284177,p 7825413306,
  p 27377860442,n 37056885971,p 11918762830,p 24626706768,n 38147329013,p 14172533844]
/-- Part 1 of `rkmViHi_m1024_r512_s1_c1`. -/
def rkmViHi_m1024_r512_s1_c1_p1 : List ℤ := let p := rkmP; let n := rkmN; [
  p 24675076802,n 38488883780,p 12900779458,p 25828855908,n 38058183278,p 9862523851,p 29605667648,
  n 36469710071,p 2935532416,p 33497173051,n 32426252872,n 5860756453,p 37771055937,n 24769279817,
  n 17604621460,p 38312766103,n 12777882898,n 28630311749,p 34412149992,p 3750564761,n 36589977577,
  p 21949763514,p 20845053230,n 36322809204,p 3041904810,p 34399049187,n 24160143289,n 19013966408,
  p 35396860446,n 2061219514,n 34490391331,p 20805323299,p 23194798565,n 32457628893,n 6211777824,
  p 35673469530,n 10829304506,n 30934238439,p 24157585440,p 20197415947,n 32597996563,n 6938538419,
  p 35775385964,n 5846677734,n 33656135825,p 17235379208,p 27978862053,n 26512443804,n 20891558779,
  p 32399702499,p 12598558864,n 35711359514,n 3900724491,p 37731787150,n 3305490839,n 37526846709,
  p 10028209518,p 36445050218,n 16145323434,n 35868252495,p 19947622842,p 33872143675,
  n 24174960669,n 33466210201,p 26615813191,p 33482424637,n 27341434195,n 32086877112,
  p 31313118379,p 38671924534,n 22896051575,n 28612482926,p 39871322214,p 59241836116,p 3736763107,
  n 3734283953,p 77025060029,p 130566641139,p 105338793707,p 114008549700,p 232816992527,
  p 371388748637,p 446729048372,p 544536296914,p 783394257542,p 1127577145826,p 1475053663476,
  p 1862927850732,p 2438736432938,p 3253498433567,p 4226782266468,p 5336047106474,p 6714870523891,
  p 8505378577972,p 10708316974307,p 13265600525478,p 16236493201397,p 19791653442882,
  p 24039976391575,p 28952028357046,p 34485054274400,p 40713784949720,p 47774989989733,
  p 55710240113965,p 64427792917060,p 73824920143509,p 83891573669986,p 94655333666605,
  p 106048120548562,p 117870938347871,p 129894596399997,p 141962168416585,p 153970040849997,
  p 165763706946997,p 177083548594360,p 187625774022255,p 197146578531887,p 205497027012564,
  p 212564118854087,p 218196940742690,p 222203623858404,p 224421709426346,p 224789200915021,
  p 223349891302652,p 220196072087675,p 215408757707425,p 209049245312432,p 201202046163169,
  p 192023171714306,p 181747840923934,p 170650214118845,p 158986877120859,p 146964353586417,
  p 134747565985482,p 122493974677750,p 110382120285057,p 98611908260690,p 87376804132173,
  p 76827257837445,p 67048349896007,p 58063382986410,p 49858614329111,p 42413330083840,
  p 35719233135280,p 29781618741964,p 24605650105709,p 20178030337803,p 16454776523001,
  p 13360916691984,p 10801341692916,p 8677249982332,p 6901358502529,p 5406963224436,
  p 4149349246418,p 3101138660732,p 2244786721909,p 1565416120091,p 1046051765493,p 665866733430,
  p 400900914138,p 226152483494,p 117934861069,p 55725136950,p 23161965384,p 8208174184,
  p 2700709587,p 1572577437,p 1994575440,p 2602959694,p 2894320222,p 2803581525,p 2441804346,
  p 1954035719,p 1456519093,p 1019768335,p 673799695,p 420911727,p 248358471,p 137837769,
  p 71297951,p 33740579,p 14021815,p 4553415,p 549603,n 792441,n 990555,n 794547,n 531551,n 316993,
  n 172636,n 86498,n 39732,n 16450,n 5868,n 1563,n 81,p 279,p 263,p 171,p 89,p 39,p 13,p 2,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0]
/-- Input orbital vector for `m1024_r512_s1_c1`. -/
def rkmViHi_m1024_r512_s1_c1 : List ℤ :=
  rkmViHi_m1024_r512_s1_c1_p0 ++ (rkmViHi_m1024_r512_s1_c1_p1)
/-- Part 0 of `rkmVoHi_m1024_r512_s1_c1`. -/
def rkmVoHi_m1024_r512_s1_c1_p0 : List ℤ := let p := rkmP; let n := rkmN; [
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
/-- Part 1 of `rkmVoHi_m1024_r512_s1_c1`. -/
def rkmVoHi_m1024_r512_s1_c1_p1 : List ℤ := let p := rkmP; let n := rkmN; [
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
/-- Output orbital vector for `m1024_r512_s1_c1`. -/
def rkmVoHi_m1024_r512_s1_c1 : List ℤ :=
  rkmVoHi_m1024_r512_s1_c1_p0 ++ (rkmVoHi_m1024_r512_s1_c1_p1)
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
  [0,0,5,13,17,15,3,33,29,3,2,25,15,3,11,11,8,3,4,21,4,10,7,47,31,25,3,22,22,34,16,21,7,33,27,13,
   11,28,18,10,39,35,101,40,131,268,501,1060,1657,2448,3001,1276,6204,27847,79906,191573,411842,
   817559,1517236,2649183,4359590,6748393,9764676,13033497,15608330,15664911,10193122,5196330,
   36175027,89092526,169656567,280816714,420025969,576436778,729043967,847105534,894136567,
   836111458,653108119,351683100,26614704,405985593,690401098,790849969,659551128,318757779,
   130865697,533291488,730977941,632837258,266533575,215865739,593700662,679551283,421025862,
   55371302,495368351,650141898,424186325,52947289,489353508,606395257,324100144,170982520,
   538514541,517679438,121980905,356105843,554011024,318084799,164778543,504073750,420304247,
   15148685,428299576,458741371,80755296,362449242,463004259,128129144,322183518,452358517,
   135559986,311046716,434827839,109021662,325837824,409057277]
private def pvm_w0_1_p1 : List ℤ := pzig
  [51030246,358395500,366505447,36973097,394758618,294155557,149817953,413596136,179373303,
   272124025,386907196,18678585,372572361,287080458,169913068,404581129,103477508,336703402,
   321397909,134290407,405018838,109342383,342049019,306190248,171263586,399157661,37444174,
   385576088,239159679,255493153,334612814,148847122,482366657,196680794,168719668,122691460,
   854192261,1228724186,1229339295,1767023852,3321238165,5299591620,7239876307,9882143400,
   14251418925,20237859764,27099960351,35027903334,44953538003,56768817142,68979376405,
   80367604730,90623108439,98722087658,102069082423,98286267658,86812210887,67854749058,
   41273301071,8196165956,27193119158,59133980419,82819399490,94278384733,89630920658,
   67415927859,31472363132,10247187408,48952339863,75892562950,82862910745,66204185718,
   30601609413,12826876719,51242398384,72505088597,67904686362,37845988219,5830444329,
   45688717892,66497479601,59423243644,25840664611,19652739159,54824501552,62719948467,
   39991581764,2977668680,45119961975,62808541960,44792355619,1386600766,42498247830,61998665199,
   44384081334,1932165978,48013281497,62907420166,36571939739,14176879603,56747484246,
   61161474719,21439480646,34883507980,65979610747,48726470288,5153174252,56895844805,
   65623845770,21509174167,40791254413,70165239454,42419005313,21187319645,68760021802,
   57453536147,5367071195,63800245366,65194864087,7832449226,57944360846,70860804945,15655084706,
   55387808054,72264635705,18480869584,53938452778,73253859899]
private def pvm_w0_1_p2 : List ℤ := pzig
  [17168583524,57741418088,71504749603,9479574382,62266205844,67324057091,1806643377,69876653772,
   58435271765,19682868967,74217032348,42932339139,38877890467,74984203492,19746413365,
   59380006409,64198310090,10144064548,71498446933,42211946898,42172394268,70905813237,
   5725122822,65752388854,49103355419,33813684825,70762759648,8707507841,65074472959,45846142028,
   37854189664,67072801789,1336346117,68305704698,32717067801,51589519589,57109080592,
   23969617306,68670019241,6023596170,66629318548,32626896871,53162382103,53340459444,
   33360364740,66300184675,11753376545,70354654510,9980266261,67482330727,30230376976,
   60830591414,46211163981,50870816739,57972841182,38290590322,67619111929,26516123089,
   73966445756,15786031538,76977528455,4673348603,80230048468,3445567273,82010440787,9447255676,
   82340899246,15443875019,85481998181,16307305308,86175862370,17238340569,88971089523,
   15343769454,93926500730,5951018705,90127085009,8273490106,109529238840,29883790942,
   70573220237,14061789798,156020013728,133127388886,38764157018,118024546116,336427271856,
   453782815410,462077927174,615957189136,1014779300106,1464172915728,1844758271198,
   2356413885844,3238356925002,4443130194800,5796938477052,7372798731024,9476953796196,
   12285673505242,15710758633028,19690076025784,24442781086038,30306478180376,37413815618658,
   45684344220334,55121779050308,65971177529166,78515715302736,92806351088152,108688108692680,
   126060599525828,145004446756404,165609484417202,187738374364904,211023615108092,
   235082356928384,259670491890402,284597943291588,309528641532906,333914235326940,
   357137287933460,378700303889148,398264649486716,415526072511534,430088002757172,
   441479279396642,449300368562830]
private def pvm_w0_1_p3 : List ℤ := pzig
  [453354848189672,453650423501538,450287308670202,443351085147770,432906755190650,
   419087183467352,402185556864476,382665929171292,361080948798356,337959759947948,
   313743936342772,288803403659236,263501871734844,238250357820894,213504401259584,
   189705581744452,167205960548722,146221528350126,126838313230906,109061576161306,
   92876217067102,78285905276018,65315612786352,53984226319034,44268104557688,36077237376260,
   29255676684176,23604505331978,18915935409060,15004670796764,11726641311892,8982175117544,
   6706899285748,4856877970710,3394403051652,2278556315418,1461745820454,891129583062,
   512732137616,276055072050,137651619976,62996199414,26689440564,11449988622,6465803610,
   5602101808,5798180454,5814160372,5356847718,4534912536,3560838538,2615807648,1808836998,
   1181781356,730520744,426850776,234851048,120667874,56956758,23845168,8063010,1393462,890809,
   1305669,1073251,718693,425481,229193,113419,51463,21099,7523,2073,211,246,248,154,72,26,4,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_1_p4 : List ℤ := pzig
  [0]
private def pvm_w0_1 : List ℤ :=
  pvm_w0_1_p0 ++ (pvm_w0_1_p1 ++ (pvm_w0_1_p2 ++ (pvm_w0_1_p3 ++ pvm_w0_1_p4)))
private def pvm_w0_2_p0 : List ℤ := pzig
  [0,0,5,13,17,25,1,5,27,41,7,0,21,17,1,19,5,13,10,6,3,27,4,20,1,11,37,39,15,23,16,32,16,28,9,1,
   35,1,99,112,241,488,793,1296,1605,712,3346,16069,47656,118255,262444,536519,1025314,1842353,
   3119698,4971895,7416910,10239263,12777084,13639411,10390036,713058,24771757,67882596,
   136132683,233801130,360819757,509892600,664120469,796385650,871883069,854770874,718772313,
   459735630,106131265,277845003,601392100,770107327,718853534,443971593,20082162,411735028,
   688366919,690458882,403272095,59663553,492047550,684820087,533656128,107064409,372259949,
   638203592,533093181,112686760,370410926,612370611,453429490,4637500,451427275,573995230,
   282654207,210530165,536076676,444053613,6150700,427723010,504004307,159910734,312402350,
   505545243,251026016,222367842,484123239,293618348,168573656,461007853,301503946,151397736,
   445010049,282854790,167155752,435708695,239675086,210319330,425695019,169649738,272620564,
   401882961]
private def pvm_w0_2_p1 : List ℤ := pzig
  [69654346,340354822,347269811,58877569,391599314,245273561,202937107,396215438,88594119,
   331545509,322714740,107768352,395837871,155460424,294813430,343245095,81823709,394752244,
   155009667,302136175,321046034,135911684,415279259,117622294,295585484,162338059,392774433,
   641764886,383168425,307766114,994254659,2066871600,2873402721,3668007768,5408724839,
   8442582704,12193595819,16403696768,21893342707,29499042230,38854458885,49011014522,
   59804823037,71522549042,83288116309,92904826066,98511199621,99299086186,94241282457,
   81480476706,60072641131,31587781682,848986364,34076133963,64249027846,85819423091,93328083276,
   84463807467,60532861924,25033072757,16121430587,53648491098,77264659237,80452610020,
   62566555817,27798946740,15103438410,52927101677,72238166720,66226583389,37493699708,
   4113727988,44034009313,66168899228,60140434475,28410922102,14660801232,50419385435,
   62996424526,45214711587,4433661134,38338209380,60285273205,50188664838,13160188573,
   31877363399,59467645110,51772756173,12478973942,34294906684,60118628969,48810421932,
   5572258161,42905331019,63164358526,39975679799,10951897683,54775372608,60907086407,
   22860622972,33730959164,65945837391,47777832014,7269720310,57278105469,63362055980,
   18395981073,43324124799,69846875850,37359636745,26940303195,68774852582,51810825355,
   11675515671,66306529162,60668835011,1291397409,62017956260,65122889457,6621890584,59628716418,
   68292781151,8494702164,59900230278,67500230221,6701420784,61491715758,66249202231]
private def pvm_w0_2_p2 : List ℤ := pzig
  [31624518,66684114208,60360714469,11724140281,70438944056,51086826763,26448321259,74262383792,
   35205005075,44843433937,70967505172,13022797623,60485631317,60708806054,14653502130,
   71448581403,37342087426,43266505760,67953850409,5179108682,64836347558,48639194639,
   33092209269,68908582742,10966299243,61187828775,48912454450,32296428812,67773133351,
   5447657988,63821314386,39900445583,41854450469,62141479294,10918807052,67798154203,
   20466799144,57708939772,46383234997,36997020855,62936099244,11846335414,68071737585,
   13488129942,62763526180,36398290277,50588460857,54190716864,34655200156,65019755207,
   16224423493,69886163026,2964544171,70838730487,20066460810,68004818888,34384495375,
   61630356265,47266630194,54462122872,57870019647,47734214271,65029828212,40102582872,
   71190428591,33476184077,76686915986,29639625260,79408000179,25920436451,82455830852,
   24540486386,85445111913,26908164757,85463125846,28879011362,87577825757,36210796351,
   86033140994,44658300046,82458140567,53275984317,81207978444,73328528592,59827482929,
   68047400963,74485548332,124852750922,11708970462,35813554123,108731122860,253789982694,
   232208451084,197869334726,372629328846,687633634168,923232234738,1101309626224,1479720676620,
   2172846835526,3022622509938,3917422232140,5041865440284,6673381240506,8858472996926,
   11466950029188,14526249964206,18326420111074,23151854380862,29044914806280,35934732218438,
   43925688395146,53329477376880,64404461514134,77164731643170,91500986878948,107425366791112,
   125105044404128,144645966871900,165906862534388,188564428712706,212327142544978,
   237027542296714,262492578172708,288361297645110,314067172031260,339001115518312,
   362673975631078]
private def pvm_w0_2_p3 : List ℤ := pzig
  [384717732733492,404753137739114,422288977369614,436770200163284,447731614326928,
   454913991586368,458248119564142,457743089594274,453395825931792,445204061662860,
   433262228464946,417847682778404,399419588754354,378529555817372,355711072027388,
   331422264967980,306067271323742,280060958844204,253875451884370,228027804010892,
   203014117059340,179231488913672,156933507785516,136240229124700,117189934291958,
   99799076251024,84098338386366,70131443181220,57925556704312,47455322089090,38621885570134,
   31257226401628,25150490645774,20083916142464,15864357612652,12341095034564,9407823061912,
   6992771057808,5043733875246,3514329430102,2355299638770,1511739753452,924961293976,
   536731625536,293742973980,150888171462,72783606904,33660276118,16116080268,9311212994,
   7092137516,6355814856,5794231460,5031672078,4093909476,3120995830,2237925530,1514919538,
   970405638,588623552,337653936,182442204,92099834,42753532,17648470,5935794,1090264,536197,
   828971,675735,444451,257491,135459,65375,28893,11537,4005,1085,125,100,90,50,16,2,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_2_p4 : List ℤ := pzig
  [0]
private def pvm_w0_2 : List ℤ :=
  pvm_w0_2_p0 ++ (pvm_w0_2_p1 ++ (pvm_w0_2_p2 ++ (pvm_w0_2_p3 ++ pvm_w0_2_p4)))
private def pvm_w0_3_p0 : List ℤ := pzig
  [0,0,5,13,7,27,19,5,8,21,41,17,0,25,1,19,5,15,13,17,12,22,17,21,3,1,30,1,25,13,49,21,39,42,71,
   218,321,574,755,572,1036,6799,22200,58871,137848,295931,591848,1110849,1963636,3268417,
   5102870,7408753,9827884,11463867,10576722,4271073,11710641,42908060,95542143,175181500,
   284583421,420892028,572800411,718746890,827552141,862819722,791661003,596759308,288723683,
   86202133,448581932,702079003,762643938,593077273,229521936,215241726,581229133,719810818,
   561351501,160335866,311393148,632623383,639213332,317822701,169561543,558204060,624181575,
   322152628,171158308,550588769,570880894,214410427,281345503,573612498,453297989,5571462,
   438111838,540699221,221926984,266339100,530027293,352394180,117040844,477133897,415556938,
   11896900,420008757,436407410,47644971,378282645,433981660,67228751,358793369,418306390,
   52752445,360575239,391230306,8334031,377441591,348362456,62696596,398502939,281496390,
   154891980,407821115,182109424,256641596,384978707]
private def pvm_w0_3_p1 : List ℤ := pzig
  [46860872,346332526,308866655,114735509,391443848,166700843,272958323,355426824,30927624,
   375049041,212601768,241535306,368507845,7698645,359438586,178436669,301344077,423420554,
   58105147,179682105,200251849,856064078,1145161859,1149423440,1652383743,3061769660,4912691369,
   6761034182,9116529043,12925556526,18357623199,24801559938,32084157211,40898666880,51622035171,
   63332564224,74589592273,84652748224,93055295199,98247366966,97770521371,90007611242,
   74930545575,53013847464,24714331791,8086060897,40988754512,68520869377,86295359620,
   91209723713,80896674992,55172317963,18268180258,21746969222,56080980897,77219434224,
   79347496185,60226844884,24247469343,17772612227,53051773130,71169832851,66013105224,
   37939965167,3783501653,43070439888,64540333891,60292191516,31886627537,10003369179,
   47529721770,62770608165,48130134444,11019034351,30780395327,57356104140,54610453543,
   22334399254,22490324826,54383862669,55336598234,24858874097,20529331617,54748718184,
   55686260953,21029139832,27400340506,58213175209,51498140608,10612630269,38841308913,
   62723681570,42253329173,9019522807,54068808932,60286866713,22286709688,33696236574,
   65475358769,46305066000,10167102964,58864225429,60654622562,13361422241,46159711859,
   68390546268,32030540419,32951496797,69362966472,44886231937,19464942653,67437887150,
   54618537879,9783415019,65853314264,59182562065,4111589961,63441610394,61609863339,1323553957,
   64153402576,61871390881,4477350425,65788047354,58332252109,10214481191,68519678626,
   53206331403]
private def pvm_w0_3_p2 : List ℤ := pzig
  [21095214923,71968348264,41901481763,34695451757,71621511086,26898482329,49519898441,
   68001075890,5041279643,63395695675,54477341662,20065310722,69775919921,33108457908,
   45726045742,66124718239,1121951482,64253755928,45540734433,32293069951,67552416412,
   12050864361,60166121375,49135493942,29452454012,66069607063,10632110760,59805227044,
   45150843729,35307003875,63869972098,1697096760,63808417007,31167063892,48158272114,
   55127532551,22986412399,65615625148,5625533881,62593905989,32425913226,49422418704,
   52934135529,30113202241,64374772530,7629278634,66920938993,15360383852,62792612094,
   35676344003,53713359619,51171463254,40430899934,62210626077,24705043393,69853945290,
   9280465854,73693215029,4897022866,73656535100,18578937983,71902124931,30895382868,69838551164,
   40271369657,66489569281,48012159190,62752274486,55173159919,61027184951,59689684654,
   59962618186,62363534209,59207805499,65162370060,61794778860,64952515451,65310339885,
   62846572392,69477858838,60433465265,77639533641,52395107506,83754654014,43871133093,
   92185092611,30485920400,100101527560,10226854761,99310971529,2931705155,112627780376,
   49338052588,72156041265,24516567925,133857945384,165460800864,64362884520,69506610476,
   270808150158,473886278214,537774805530,622056917696,950314414030,1485467974010,2033372701368,
   2597990820996,3431884290316,4719657522736,6389592478846,8330091831456,10674185984880,
   13735156832792,17703334371032,22546410943650,28240524236976,34990913242166,43136670297596,
   52880456344476,64205984487058,77071806431818,91604252300962,108033498578608,126459181747610,
   146736447244390,168603695163324,191874405031716,216456409538206]
private def pvm_w0_3_p3 : List ℤ := pzig
  [242185081590560,268673737154288,295350828091712,321635869627754,347063528825264,
   371241163931160,393712546213268,413892093325596,431148988381126,444965786659750,
   455030918724598,461199153362488,463380418098160,461473246713622,455404404292458,
   445234158621588,431231211852496,413852423533664,393642675947088,371128819532204,
   346776371610768,321022046506162,294337966909436,267266051481356,240389565039612,
   214256319922872,189299661495920,165801084392014,143909157151128,123695866799826,
   105214274662564,88527375261894,73699344395534,60762185063832,49681414854866,40340857985410,
   32553866968862,26094791583320,20736808267248,16282355324388,12578239495354,9514928117394,
   7015091286126,5018498276338,3469249867818,2308520305714,1473087792694,897993696990,
   520988694954,286738995326,149580418348,74463561414,36351172462,18625868046,11094355334,
   8042316024,6607904626,5573662752,4560108124,3543362042,2601819638,1806061342,1186987576,
   739377944,436430576,243641482,128061600,62825498,28289852,11285462,3630202,593860,364799,
   505135,392707,248381,138637,70251,32627,13845,5285,1749,449,51,24,16,4,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_3_p4 : List ℤ := pzig
  [0]
private def pvm_w0_3 : List ℤ :=
  pvm_w0_3_p0 ++ (pvm_w0_3_p1 ++ (pvm_w0_3_p2 ++ (pvm_w0_3_p3 ++ pvm_w0_3_p4)))
private def pvm_w0_4_p0 : List ℤ := pzig
  [0,0,5,13,3,17,23,29,7,10,1,45,9,25,1,17,11,11,7,5,33,25,18,4,4,9,43,14,9,62,99,194,339,326,2,
   1899,7502,22295,56908,131227,280042,558615,1047594,1849307,3067722,4755489,6808846,8792403,
   9682688,7552219,743403,19741494,55207223,113382398,199433687,315052180,455487067,606762576,
   744322981,834606778,840805935,733017854,501158173,166786138,211698772,545937489,739128092,
   719007637,472110220,64050697,368698879,661179098,686408007,419605974,33559498,468971497,
   673560904,535574059,117078892,361351560,631168521,530445958,112360177,369896829,610301560,
   448330265,12044351,457028900,572831387,273576614,222367638,542060731,438869090,7103080,
   439105889,504533688,149208301,325552571,510625396,244696757,233934721,491350404,291890195,
   176159193,468050992,304106883,153352337,450344984,290013707,162208371,439122482,252809849,
   197559875,428916378,191642029,252225905,409408158,104293735,315300507,366912024,8958922,
   370107113,287177124,140437984,393567913,160932898,269945492,359071935]
private def pvm_w0_4_p1 : List ℤ := pzig
  [8074489,363603362,247792999,190081029,372751768,52456653,347791225,292171678,134093866,
   322358351,29050819,489864936,503207971,201614940,264462035,985137060,1890875825,2509913448,
   3193538427,4759286486,7449835249,10774076290,14506545251,19320804480,26017678239,34464475880,
   43859762017,53874618700,64775312567,76205023454,86508763343,93726113036,96735965221,
   94819881340,86615106491,70617906128,46922076333,17740418522,13863573724,44775364743,
   71014405620,87424619407,89644787252,76461907791,49912977750,14069139259,24969987257,
   58639779816,77936214739,77401163176,57246523067,22462817350,18352845278,53582946273,
   71402509116,65259547591,37446369798,2320463958,40642062891,63715397406,61687827837,
   34399038980,6649075650,43681728309,61129124758,51414479235,17890924972,24508391130,
   54570760853,56492675304,29477580941,12416110875,47841124696,57657502225,34888532460,
   8636498074,47186165785,57452396044,33326624331,11242242575,49853525116,57567312407,
   27406722476,21690137088,56485501761,53245518636,13748194171,36158117129,61922137040,
   43255274429,8095918449,54073176336,59686512355,20355697988,35100977012,64709949723,
   43644362844,13558503088,60622178103,57891117942,7184197191,49890494801,65799925058,
   25363447689,38519219477,69212351570,37726009329,27966279475,68350066462,46565272243,
   18754360285,67723683212,52344306509,14358911775,67136658708,53725568809,12615540751,
   66669713206,53921069689,14686286433,68792267632,50311749485,21495116807,69791252956,
   43268029373,30035091165,71036587520,33019851515]
private def pvm_w0_4_p2 : List ℤ := pzig
  [42689862255,69418049472,16455532273,54646775717,62192816202,2884574162,65030655343,
   49052065256,26863894992,69131970471,25868586366,48573700548,62179466651,2499879377,
   64432482000,42857510183,34812147643,65737533270,9754969235,58329363957,48351627544,
   27205319110,65853221673,12790362334,57821001742,46362458285,29961954187,63334226650,
   6133135501,60544675171,38419454846,40920577196,58608424511,11320981981,63702499348,
   19880205053,54956030719,45250930878,35835019084,60373208421,10695546963,64488227244,
   15605476089,59202538301,38403010616,46556299182,54749901517,28485709257,64264118586,
   7649245638,67880993917,12676361924,66043158084,30407710457,59017745559,45501824524,
   48483449202,58141761241,36898629953,67362790882,25134386328,72837989149,12822543739,
   76238391124,1000029532,78756750031,8604576318,79597916760,16561462633,79132896277,23925737864,
   79567867078,29097686801,80619170109,31514628980,80996940192,33245553891,82890138923,
   32947709268,86393533146,28979470773,88837553541,24124330640,92716690798,16159248663,
   96918144759,3703425868,97765686558,9050615558,99448513353,27690534919,94975387766,46755577984,
   86077400007,65634638235,74464406948,90966419878,41977681463,89716399635,38255529848,
   137548275592,59431422680,38556283477,45971080886,233156524886,303140701920,262756038430,
   344178235532,652423708856,1027872360924,1329454710526,1688884685336,2353633689072,
   3374058060638,4607524297324,6020536246102,7838499993490,10337647276322,13592587393140,
   17534745257582,22223618673770,27947691914948,35025647644210,43584226727536,53598727748834,
   65120395572650,78380647620524,93638675826586]
private def pvm_w0_4_p3 : List ℤ := pzig
  [110966017022436,130223219376794,151232984714974,173922103029220,198260729445044,
   224076064775618,250955579244032,278341045816418,305701987061620,332605698312946,
   358629574138990,383232656969282,405737338180964,425451365361978,441822004934006,
   454493421048532,463239819449404,467861402219560,468152517813582,463973906009700,
   455364116726014,442593959677048,426119580548316,406471504697988,384160088022068,
   359654511620168,333429929428470,306027490280494,278068763847564,250204775291958,
   223027390888866,196993971176884,172403782281754,149430295124674,128181979121910,
   108753697006454,91243376380598,75732607204064,62249714352666,50739979198380,41059962663288,
   32998416297660,26313724639358,20772622654136,16177524448416,12376930821072,9260757547130,
   6746979179710,4766817141802,3253722255664,2138302741116,1348635772414,813874502784,
   468787825356,257447528084,135179168466,68703214522,34902496196,18836962742,11573214846,
   8222674834,6387729906,5058938860,3909514472,2891245494,2032494700,1356068430,858678740,
   515962438,293878224,158227614,80096784,37741636,16239190,6120224,1795312,191688,258015,287873,
   206267,122915,65045,31289,13781,5527,1981,615,155,27,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_4_p4 : List ℤ := pzig
  [0]
private def pvm_w0_4 : List ℤ :=
  pvm_w0_4_p0 ++ (pvm_w0_4_p1 ++ (pvm_w0_4_p2 ++ (pvm_w0_4_p3 ++ pvm_w0_4_p4)))
private def pvm_w0_5_p0 : List ℤ := pzig
  [0,0,5,13,3,9,9,25,31,31,26,7,9,31,17,13,11,11,17,17,16,11,37,5,45,58,67,138,157,225,1582,5853,
   17090,43731,102188,221465,449114,855773,1532778,2574685,4028454,5792779,7442976,7973049,
   5469724,3215318,22655091,58685124,117622353,204637138,321227959,462112616,612366903,746159578,
   828702949,822693926,699313303,451793096,107176375,269737993,585798874,744190461,679815888,
   393403933,32183413,447586372,687480779,641504144,315045443,154881633,548700618,666596435,
   437890834,24763906,469618075,639630088,427499969,44235827,482391940,602186479,319477486,
   177401690,542872873,513939296,108932967,371066905,559309464,307848543,184235855,518093498,
   417776581,32154717,446160880,463914385,70743522,378500342,473336101,127354532,331791356,
   465186053,145438530,310986246,449136355,131639898,314437932,426874903,89937564,336428572,
   394160145,22645922,367658150,342920879,67104751,394769286,263876667,171993037,400202578,
   150396363,277104493,364175452,4432465,357253449,268862878,159295154,383418707,116188442,
   294284122,305522413]
private def pvm_w0_5_p1 : List ℤ := pzig
  [107746763,410292702,218117877,169821297,155752018,351416260,818199913,854332254,816782475,
   1382113128,2666200679,4159371604,5610754719,7594711764,10898949875,15596558570,21176183457,
   27543520886,35343012607,45012212686,55918940569,66859707276,77110572201,86330869910,
   93435186919,96298853560,92989768055,82861386084,66096746377,42858335034,13885666731,
   18099642679,48466833836,72463238297,86465053636,87684032373,74217277280,46786538757,
   10209026200,27760011840,59107007187,77069139306,76670654683,56498816724,21108124399,
   19341063437,52944035274,70063011979,65317318724,39133183977,510307777,39297120146,62493404977,
   61636628500,37321897279,1525894063,39745953272,60636907743,54081355594,23002810175,
   17887756751,49737002924,57667448869,36946341248,3159478030,41755336957,57487365896,
   41688180925,3158844282,37248718284,56964766337,43345509790,2944244735,39786224889,57738923780,
   39478809731,3803885699,45399260170,58217689647,31934278510,17154762304,54966596835,
   54397616128,15527186281,34820123691,61153528054,43037068275,8249742217,54394164894,
   58920612637,17629002874,37646730060,63993454695,39712700222,17737193486,61936414777,
   54561598580,625044967,54033149563,62647921792,17271109145,44098377579,67455345856,29832918161,
   35884876553,68682259266,37639632557,28467248815,68197672312,43404161211,24047850869,
   68877903168,45287493865,23827332379,68614027210,43943294913,25438057319,69168076148,
   40852030949,31400997613,70172758286,32777460351,39821484865,68400249826,21904018577,
   49111614963,65292711718,6686110043]
private def pvm_w0_5_p2 : List ℤ := pzig
  [59777472147,56168240660,12877583450,65953294647,41020020364,32839675042,67387381471,
   19236101130,52812802876,58315974375,9096508219,64087038764,37832619513,36685218607,
   64072985390,7304383489,59139428107,46107314540,28230089390,63693099369,13156889986,
   55340403738,47717925119,26967315545,63503584846,9513553963,57242794047,41635967978,
   33585691050,60352750299,1647409485,61828687444,29071140219,47410154773,51567873176,
   22343305034,62260664393,6348202118,60474371036,32273936495,47671429529,51397219426,
   27049617858,62201553809,3020400425,64590005920,20095987359,58980625667,39594210070,
   46580607862,54629825887,29900176383,64932359188,11908879604,69878466399,5659535672,
   69375088758,22486947193,64922331089,38000738192,58504813882,50778121571,50705505045,
   60324684624,41376440234,67893962659,31723936851,74287650392,23496409402,78694984489,
   16515839909,81205357566,9938423662,83662766513,5035561235,86295436872,2935303520,87704672899,
   2142396361,88990799148,2680063364,91406549229,6739272897,92616968500,12903657456,92652705709,
   20264640971,93165052658,31725070224,90413183361,44701560507,84606978056,58173621808,
   76939012829,74940574391,61476814324,87811447970,43381654159,100093423111,18318694114,
   106930590088,13589308472,100249469121,38105937247,99907672700,89825669604,41456525359,
   62715267945,83943883518,196490356808,146187589466,87200517446,218718424418,487959171228,
   694781010990,823023217540,1090658707688,1658039433398,2442258218124,3305721453828,
   4331013893968,5787735227474,7855450539632,10502932635056,13682782372640,17560135729714,
   22465692664642,28648591557584]
private def pvm_w0_5_p3 : List ℤ := pzig
  [36160232901766,45006283261482,55350630059878,67503372624724,81710524982344,98002771742322,
   116269261569678,136442386422474,158558805245084,182623640083426,208435299796166,
   235562472405374,263486137282732,291744592129996,319933926751622,347583519720928,
   374056640212132,398592328997618,420458779805286,439085197239558,454071745753514,
   465098775026720,471844734867806,474001950275938,471382115571876,464022740304606,
   452208026954344,436390586652316,417076222009146,394752787041074,369899341962616,
   343046163623284,314821027117908,285933425426460,257097009013414,228933261858338,
   201908613824218,176332147142026,152403162095966,130272427074084,110080666953782,
   91957963050980,75992790614960,62194679541040,50474015755862,40650151811966,32483760574852,
   25719324545844,20122166040952,15499881194466,11706148950906,8631497798612,6188539300924,
   4298475796976,2882849420846,1861309590462,1153896754126,685416997698,389700633726,
   212371940552,111688435070,57704286900,30359997066,17144695012,10836131284,7616279130,
   5671217828,4252558060,3109583726,2182839748,1461485446,931065640,563800144,324151288,
   176588612,90807848,43780354,19546878,7889628,2723792,671016,14433,166295,146945,94843,52307,
   25829,11619,4775,1785,601,179,43,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0]
private def pvm_w0_5_p4 : List ℤ := pzig
  [0]
private def pvm_w0_5 : List ℤ :=
  pvm_w0_5_p0 ++ (pvm_w0_5_p1 ++ (pvm_w0_5_p2 ++ (pvm_w0_5_p3 ++ pvm_w0_5_p4)))
private def pvm_w0_6_p0 : List ℤ := pzig
  [0,0,5,13,3,9,5,15,0,53,27,9,12,3,19,23,13,17,2,13,53,32,47,36,124,899,3226,9871,26250,63683,
   143328,301381,594332,1100053,1905678,3069729,4536128,5977995,6553374,4578345,2827999,19999292,
   52662245,107276900,189508047,301715290,439721287,589661430,726318321,814693978,816294625,
   700376048,458195335,115694348,261839568,579187011,736904492,668481693,376055738,53057270,
   463973627,688525912,619759221,273366260,200551528,574477551,653303728,385045719,93173299,
   514505324,629367201,361131166,130029820,531999139,577622806,231005913,271561409,573803668,
   453697747,2471147,449694280,540593587,201812152,294239518,539767919,328959282,158454746,
   499737999,394449560,62053016,453611553,419034986,7479458,418781509,418605722,9403321,
   401320731,401611274,6215400,400000905,369803526,49708492,408594537,320136362,116210824,
   416811981,247222480,198515270,410863289,146540918,284486804,374738245,18408920,355589690,
   294358381,125810209,384806140,159001879,268757915,358094614,362794,334134039,191786308,
   266511278,476034453,225821118,33886692,231050464]
private def pvm_w0_6_p1 : List ℤ := pzig
  [939165689,1540106184,1839388839,2369888516,3769339571,6020415836,8646384409,11611879756,
   15625665921,21355360124,28649098427,36885613830,45906885341,56064865920,67201633295,
   78030568808,86857384785,92576226376,94471154119,91278874750,81270112673,63634050864,
   39400957597,10786635484,19751384440,49175519275,73089040980,86531108013,86173218476,
   71599252105,44777096566,9490810539,28118493695,59648614426,76946126303,75467770016,
   55592127375,21868332402,17643498024,51969504703,70045707096,65584985211,40188751772,
   2350686177,35665916321,60840293372,63207771073,40898735908,2689468857,35532331463,58179421204,
   56074688251,29574226588,10468476828,45584068239,58300242884,42196652579,5565816746,
   33408319908,55316958859,48173931158,14462971359,27749648719,54104823526,49147915785,
   15802065078,26896957304,54194521183,48806846958,12371139903,32750925011,56936830664,
   43950674289,2085179470,41644401772,58219492003,34953918636,13797374156,53690439707,
   55060408962,16317312707,34574434505,60629232284,41835686591,9533495173,54912758428,
   57677418965,14307741474,40798063060,63348917623,34826660780,22802421640,62754724661,
   50146442350,6175898626,57764162349,58957020066,8408510469,49794968525,64254577376,20654908235,
   42970460875,67387263632,28232895357,37820591591,67710208614,32881919217,33826025423,
   68256584518,35301096621,33798334583,68918104320,33334444991,36269110811,68051234554,
   29206184185,40509747727,67750007902,21880687171,48233214567,65024177844,9830049815,
   55613094031,58689316480,4157728532,62616113645,49064753946,22070335872]
private def pvm_w0_6_p2 : List ℤ := pzig
  [66980445941,32115582674,40333054458,63889518643,10711065496,55541824112,53708939149,
   15268802649,64932208360,31946197251,41038886055,60814802744,2747932027,58759330393,
   43579307988,29621666952,63188085575,11274153862,55200765442,46012332261,25538929057,
   61857394556,12397484535,54979199873,44353260350,29904797000,60521980511,3745669060,
   57859340688,35265724571,39398113557,56172941936,11747159722,62144850397,17668978042,
   53420789174,42518835841,33803623727,58407401292,8732195736,63137534465,16695313632,
   56846166904,38801038201,41871494395,55232605356,21879622702,64435751565,371343687,65698429940,
   20380317165,59743267433,39065846018,48709170924,54374684087,34900411889,64941327766,
   19543146186,70463470107,3174220533,72154491460,13029171173,71367078503,27367598188,
   68282755026,39289342131,62875254921,49677874452,56462574784,58872234361,50696366515,
   65937722540,45551503734,70798911153,40404992481,74958477740,36364777142,78791479595,
   34733319203,81012396110,34550215826,82000463737,35228083199,83239469652,38576609080,
   83366702557,44479356543,81042854952,50959305016,78011451855,59569171967,72976177498,
   70519226614,63371425381,80308979337,51612231224,90492838748,35675419117,99613808829,
   13710516606,102526633244,9202369192,102701806307,37711971643,92361690918,64596250918,
   73226178203,87191254551,47671928440,109469185018,44933570,95941633609,14321446419,
   126991239636,123680140010,12396267098,13300839634,192482718018,373979487482,425487297696,
   473576649302,732793900350,1219078872532,1771889491154,2340766134914,3117849217092,
   4339686253100,6053015616268]
private def pvm_w0_6_p3 : List ℤ := pzig
  [8170654299354,10728251305148,13987723662472,18258625691754,23685655251272,30276331529116,
   38115927104042,47482452500204,58716590056184,72010032965360,87360834041192,104726037963574,
   124167109368252,145806742934944,169644478453286,195434832532762,222749785630986,
   251141423325990,280224219576560,309599580355174,338719237418250,366843641399924,
   393149236013798,416892506896206,437494435822058,454496569705878,467462648597298,
   475941593890756,479540728387018,478054042355254,471543120910426,460311045991572,
   444796277624908,425469265305350,402799828479106,377299115335864,349581436714138,
   320380800425236,290495230880018,260684977484214,231580003204144,203641853778256,
   177188092208136,152451469508598,129632487414062,108916589747530,90453384534848,74317550907798,
   60478169571000,48794821136342,39042853190422,30956464760728,24272729194048,18762768159148,
   14244271824802,10577631262882,7652778843292,5374546363194,3652051956472,2394221889004,
   1510676556400,915679899036,532676225812,297640818996,160464334212,84436443938,44388408958,
   24195333578,14236068850,9196460752,6385435422,4571242594,3252915894,2249261404,1493660144,
   947388200,572434858,328923236,179380262,92560938,44957764,20371040,8470766,3125208,937876,
   154692,64629,89139,63823,36635,18417,8355,3465,1319,457,139,33,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_6_p4 : List ℤ := pzig
  [0]
private def pvm_w0_6 : List ℤ :=
  pvm_w0_6_p0 ++ (pvm_w0_6_p1 ++ (pvm_w0_6_p2 ++ (pvm_w0_6_p3 ++ pvm_w0_6_p4)))
private def pvm_w0_7_p0 : List ℤ := pzig
  [0,0,5,13,3,9,0,25,12,5,27,43,27,3,12,11,13,7,51,35,308,1265,4054,11699,30350,72753,162310,
   338587,661260,1207051,2047376,3190225,4458690,5283539,4397706,539602,13291247,39169514,
   84655369,156182460,257863433,388250194,536774717,681201804,787964247,817221974,733455123,
   520212468,194720947,184413297,523479680,717610317,688834346,425650481,5163748,419683218,
   673019149,633945964,304899997,169752023,558070642,653851633,394946766,84122982,510784699,
   627292434,354390145,141732681,539652472,569696179,205867816,299085712,580621387,427915750,
   46740918,478227105,525713630,149409789,343356485,541315598,275935085,223424565,517747132,
   344522647,138082389,484794254,372135793,91208567,458268824,371929201,80043921,443462926,
   350821473,99888911,438479936,310176511,145375363,436332752,247788061,209653959,426179592,
   160587385,282638561,394685904,48169893,349103401,328069644,83970372,389746639,219176404,
   215659004,374339709,56753896,341352910,323570951,70634673,304687002,29560449,464762377,
   638086724,439881201,418655004,1034651025,2093470412,3090573257,4023425192,5552692487,
   8263006778]
private def pvm_w0_7_p1 : List ℤ := pzig
  [12040467889,16453736598,21604129191,28192386616,36631281291,46422564702,56666212705,
   66908048594,76997494527,86103125574,92378945415,93907912472,89685370425,79386911674,
   62604285125,39142596528,10317897331,20537643799,49187996150,71791163077,84971393100,
   85556193279,71664519072,44615937807,9372805694,27104147746,57664371037,75669994872,
   75923092059,57025683666,23397395971,15656249367,49321859426,68307211311,66656045714,
   43783119091,6429097212,32428467342,58751740287,63318481454,44661018953,9235101866,29803977902,
   56341122051,58432976198,35032975351,3167531293,39167961826,56986150125,47933611714,
   15284712001,25217970281,52446717672,51917978643,24118766768,16281002558,48037082193,
   53429925060,28104421837,14221605043,48281647264,53157182085,25827962352,17352168142,
   50369670423,52136711284,19904931725,26367388321,55526110618,47183900975,6708669664,
   38642625700,57953111393,36803162988,11568995650,52707489155,55261802588,16315861365,
   35125904085,60355620032,39913661373,11851193855,55628601780,55770610375,10373189976,
   44119318686,62515813593,29303268830,28499157192,63159945441,44524309434,13337601370,
   60575515867,54335634908,664120378,55100495843,59947626720,10379897471,49408334633,64038444162,
   18030582733,45917150141,65725535066,21690930883,43263622627,65845651148,23567961177,
   42758723877,66533108144,22012740775,45642672867,65480957550,16656649321,49245493127,
   62925284200,9511259889,54636801065,59382343288,1835138278,60940157787,51185261350,15975811438,
   64406849777,39440179444,30894786988,65647763045,23026327298,47140487414]
private def pvm_w0_7_p2 : List ℤ := pzig
  [60351095273,874151658,58797917558,46739902717,22216136661,63887953908,25809096415,45145968339,
   58321927876,3379981366,59867460867,38581337230,32323850904,60871030507,9040864096,55258113450,
   44927667917,26605117383,61077438932,11616848247,53134593127,44237535968,26376736864,
   60288602227,8183849228,55971885202,38805034031,34497066811,56943648030,3732893442,59033681965,
   27010997378,46222153274,49911696411,22909208437,60483856302,4971294005,58007809921,
   31398869058,44688170510,51386902109,24180747329,61863566954,331240992,62159465493,23364531234,
   53745388708,43793141791,39173604691,58417417202,20873744622,65909327621,714788957,66612018332,
   19532000847,62021490967,37811488950,53544006640,52396507955,41888128545,62893434502,
   27792482966,70107687079,12842320135,74663478342,1212397789,76326789745,13866947882,
   75148544112,25663533167,72474776413,36468514176,69747604570,45198145209,66934937751,
   51686483526,63595154086,57146352183,60771656165,61906800678,59775192564,64797000727,
   60000497037,65803434900,60661246762,66296121053,63065962405,65686879568,67798532798,
   62285947299,72997079531,57065725008,78699626592,50481667435,86227860791,39924526446,
   92974839342,25983094191,97556224087,10205053598,101375722828,10293927080,100174048069,
   33028783721,92679289234,55245561180,80434781767,79101117763,57102617554,95563105350,
   28695446791,106167213099,7056755931,105203208552,47645973132,83685950725,73619477657,
   66235733038,121589787592,18033648190,63836570341,30790212066,200039872088,252555807592,
   206063052406,269435796704,549797364940,924370799558]
private def pvm_w0_7_p3 : List ℤ := pzig
  [1255662537278,1629813242216,2283895204168,3340916501076,4729237837130,6389408786728,
   8478254523250,11301204955394,15076828337696,19847424493936,25640856323584,32662609726204,
   41271872895808,51775387902100,64289431258394,78819409247490,95437421698644,114330931830834,
   135658461450092,159370751995720,185184151365794,212715251856580,241614770872802,
   271555587467262,302097736563808,332583427205742,362179513531624,390035720364504,
   415421601295230,437739646145038,456438199028966,470938804601462,480669499588140,
   485191794095186,484324532331614,478172803680990,467050178467310,451363438847456,
   431546129612170,408075762158870,381538241254746,352668433849488,322318222817484,
   291358732202968,260568188750532,230562230763586,201792026942028,174593471634864,
   149245849760992,126002335531578,105079347434470,86618679954592,70650000147634,57077303283384,
   45697455707626,36242617496704,28429351242838,21997923798188,16732761782274,12464075573770,
   9057064829660,6397128122164,4377797119078,2894637544720,1845031218924,1131718954138,
   667461111466,378743591312,207487389762,110681074618,58467350232,31433232786,17779461964,
   10825516428,7066175066,4807259414,3296341968,2220685440,1447210372,904768268,540241112,
   307270120,166084998,85065940,41103602,18602070,7786112,2942048,949828,219176,3207,45725,37511,
   22327,11313,5123,2113,793,269,77,17,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_7_p4 : List ℤ := pzig
  [0]
private def pvm_w0_7 : List ℤ :=
  pvm_w0_7_p0 ++ (pvm_w0_7_p1 ++ (pvm_w0_7_p2 ++ (pvm_w0_7_p3 ++ pvm_w0_7_p4)))
private def pvm_w0_8_p0 : List ℤ := pzig
  [0,0,5,13,3,11,10,21,13,0,8,7,27,47,13,53,272,1087,3546,10245,26904,65669,148874,314823,620696,
   1137017,1918786,2932529,3908550,4093145,1893478,5537012,22634791,55429202,110860337,195054318,
   310402067,451758556,602811277,734440160,807286079,780218098,624537513,340694578,28993276,
   399840653,662807262,720735985,532592954,146466215,299951373,622983716,671509211,407717428,
   54747204,488344803,661108912,468121953,8226432,453492372,634175289,413080978,74424054,
   507338551,587505102,253273801,259594723,574439226,451639273,17716347,466506954,534220799,
   163732964,337533070,544447357,277962760,228147206,522203269,337972472,154052262,493565121,
   359464490,117542140,471435519,353680398,115421978,459033475,325929770,142690374,452903157,
   276715476,193193196,444840699,204011424,258567784,423276101,106199042,326721790,375294609,
   14007947,380076962,288432061,148446265,401214168,164564947,264430291,347171700,27024696,
   398917493,320822016,62862414,185542137,222862773,798987782,1050757765,1057927756,1435829563,
   2594094722,4286204737,6081905654,8136273205,11186699208,15748494799,21606117870,28305991147,
   35930550538,44984912819,55467209978]
private def pvm_w0_8_p1 : List ℤ := pzig
  [66393846879,76437825584,84732876989,90657568096,92975863363,89789671286,79665867661,
   62584744886,39620353327,12170977806,17822492630,46956942629,70469079164,83875996349,
   84552001502,71889382663,46919538248,12856552399,24087081051,55628746928,74231233893,
   75548267118,59038878557,27872113906,10733788380,46085560447,67242706182,67544986427,
   47113066536,12281641447,26236347701,55581661786,64646453543,49347271574,15550953221,
   23299255607,52065183794,59450133489,41898079354,6026058603,32432421343,55377011276,
   51905460173,23996053166,14978466564,46485768157,54673786402,34301317519,4671297947,
   41010940012,54389370597,37464943480,362179830,38245639135,54400365144,38157229983,1903677469,
   41214768058,54705746269,33657867002,8808718362,46108819039,53987958556,25848376097,
   20755629585,53824339178,49494032367,10307691784,36341715474,57636939227,37780168962,
   10359643150,52056476321,55025652632,15621576683,36225628261,60213957180,37465479069,
   14990047323,56521474402,53166046567,5783498296,47354345410,61167338941,23304417950,
   34403542992,63104615761,37869432718,20853642620,62311492181,48448748974,9714954592,
   59360336871,54574538314,384848654,55102344713,58827166884,6902571973,52517759617,61602752306,
   10177187465,51367811211,61820960314,10889271469,50816845785,61590262644,9562903097,
   52995015245,60546055076,4084766983,56523932219,56507641628,3751284936,59660704411,51025864526,
   13629698798,63660064849,42356185008,26963541282,65134627323,28650187816,40105251482,
   62252532193,12215656148,52346437988,55026300065,8479143099,61586325600]
private def pvm_w0_8_p2 : List ℤ := pzig
  [39367106397,30467266125,62179985288,17380645335,48768225159,54027427682,9247700062,
   60883142487,33764746416,36850932620,58714049493,4015702098,55381935588,41680988125,
   27651395903,60114210132,10681560689,53387842709,43435751822,26258092620,58852007683,
   9582009318,53108245756,40992760033,30079231709,58146539458,1509257477,57092451463,31766248192,
   39851373794,52682938649,12645638097,59816615416,16716863219,52619331385,41280656650,
   33818630998,56476260999,8284043629,60506728942,18336092943,53856676173,40992834280,
   38502843992,56321799703,17317233019,63056091518,6277680451,61612556893,28731932358,
   53211847784,47110580847,39249483847,59850056734,21333615570,66860630741,1589236881,
   68764770274,17587767339,66022782561,34458796678,58937197712,48577995195,48421272039,
   60228114124,36226446008,69297426157,23928009693,75209344910,11915522568,78078587621,24890824,
   79182222424,11322954009,79653209451,20782084348,79356248032,28206369047,77994682511,
   34561579106,76594213670,40032858453,76397666141,43519635686,77002655520,44814358287,
   77610132819,45100837732,79154598762,44262279371,82509577803,40718421614,86269286942,
   34741748621,89592883627,27494649320,93735607366,17403980077,97624465419,3569848288,
   98632293502,11759157860,97619867107,29249281987,93645751186,49694224762,82875414353,
   68658962479,67106744482,86027182844,45335996983,100320535073,15135172344,104223506328,
   16457115292,100670987089,52114403387,81970284394,82468646852,50277553217,101124630397,
   12476922144,113046507406,47551866350,74289777321,53225129123,95935572656,175216684244]
private def pvm_w0_8_p3 : List ℤ := pzig
  [109229977244,61282577722,198327997192,462944906188,681525100916,841163553190,1139510488272,
   1751040939506,2647876969274,3719628186544,5019379215414,6805023220502,9334183648726,
   12693502998462,16880730431360,22022276245546,28444672411156,36514668496420,46448063461224,
   58309516696316,72181624587306,88282134147988,106880468166124,128101632910988,151825649118004,
   177771976462576,205653178617010,235219138442312,266145344602010,297889441535404,
   329670581446706,360599084127038,389840498760474,416678991445806,440455097408344,
   460475018869128,476008646321364,486403986265630,491237975063360,490393572982698,
   484017680164448,472409231343676,455931244966074,435005887931658,410175528701584,
   382159357673140,351841586911030,320180593501318,288083934103178,256313079891646,
   225456924596168,195967881406884,168220762544784,142550948556506,119250738033426,
   98532666291272,80487338988490,65063042900802,52079597436060,41270717399172,32337501995140,
   24994477843232,18996650336616,14145839292868,10282195018060,7269792253304,4983931943096,
   3304221044138,2113818237820,1302827367976,773062189890,441908931718,244092795660,131208703778,
   69568254246,37174664434,20567852340,12044191576,7490039542,4858989608,3198568768,2084175678,
   1321444728,806928500,471768540,263118802,139597514,70240852,33380340,14886904,6164410,2324138,
   765490,196260,19246,19913,19305,11797,5945,2641,1057,379,121,31,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0]
private def pvm_w0_8_p4 : List ℤ := pzig
  [0]
private def pvm_w0_8 : List ℤ :=
  pvm_w0_8_p0 ++ (pvm_w0_8_p1 ++ (pvm_w0_8_p2 ++ (pvm_w0_8_p3 ++ pvm_w0_8_p4)))
private def pvm_w0_9_p0 : List ℤ := pzig
  [0,0,5,13,3,21,8,1,15,19,4,29,168,615,2072,6481,17880,45779,108342,238135,485288,912643,
   1567616,2406477,3136972,2948635,120522,8436894,27542783,63704242,124254449,215266766,
   338119867,485205288,636174019,756991312,804338875,736903138,532450561,205735564,181215238,
   525637889,712312450,658934983,362081330,80469468,491799599,685167336,556329187,152351650,
   330012772,633076969,579584334,188680093,313754943,617187232,521427817,81189166,410256972,
   609900073,369957988,139136222,537552711,517695228,91485255,402329927,560360286,249275533,
   268705135,546808994,340358925,166672337,514304446,382476289,104717311,484278708,391452673,
   81448663,465505758,376782713,92220335,458104118,341681345,131514691,456304516,284949195,
   192691021,450091884,203672791,266398841,426502790,96363415,339190421,372381458,32114404,
   390615309,273872570,174836054,409368067,148156828,273650758,314639997,97320759,475140594,
   398835705,70685432,78807645,661239354,1431117205,1943263824,2369799889,3381404460,5378444781,
   8107670360,11199828633,14898340102,19949344455,26757245432,34941268457,43883310930,
   53444798525,63754114144,74288249829,83538202396,89776287921,91890941474,89198471461,
   80729167502]
private def pvm_w0_9_p1 : List ℤ := pzig
  [65377080123,43082369916,15622399843,13963101975,42405225034,66332828717,81845592924,
   85101424911,74153331424,50297319355,17642394276,18145140288,50428350649,71980490796,
   76738540781,62627918980,33044347931,4324135845,39886811940,64058709973,69227878424,
   52758269921,19438428642,19483505788,50738431429,63865697946,54212113599,24553508112,
   14515212178,47396674457,60196027034,47631774747,15371855324,22881070846,50795769467,
   55542522112,33991054907,4041233919,39615939394,54761779557,42088174914,8077325239,30199432661,
   52652970278,46236112337,13521010104,27035310354,51718110901,46137666590,13510134349,
   27427555811,52387500446,45178407399,8942783220,33630261022,54515704753,39700764734,1273128890,
   41771367143,54842194258,30501860497,15929574495,52037085320,51112274295,13081009756,
   34641680656,57374191389,38126813040,10016617622,51744764025,54391322894,14298277127,
   37688885383,60044958744,34603440987,18692638795,57504073380,49920338791,575082810,50367661574,
   59060173225,16878096236,40109216266,62402883287,30443153604,28497179538,62960195615,
   41234676738,18661771188,62122579427,47980175796,11061170892,59623049261,52083506986,
   4798125642,57620900439,55193492350,1633036048,57432113287,55887615154,1870208746,57409720173,
   54635671948,3669238056,58442514109,52892649402,8486616946,61277933475,48357620936,16624434048,
   63075711429,40834746922,25655973928,63942063223,31408510078,36682414690,63420907253,
   17454847462,48348399452,57671123639,251606108,56861876556,47259381979,18172620863,62187220556,
   31151959819,37944578071,60131621930]
private def pvm_w0_9_p2 : List ℤ := pzig
  [8155154833,53134188935,48080061652,16614498894,60390970271,27706194996,40736150878,
   56553706551,1418640537,57006109050,37280467345,31035176395,57867739638,7797449087,52946489139,
   42136468424,26620084896,58638576247,9158934066,52526444222,40527788971,27879147565,
   57037453178,5385653875,54556860151,35906708788,35402438034,54774321185,6430335105,57755740096,
   23734679577,45570103875,47293846930,22649427934,59070434039,4807845044,57300920594,
   30686019761,43483657599,50190031424,21486079618,60372122755,3784033676,60173031752,
   27727205479,50271902071,46973949374,32849288688,59616872663,11134371601,64884493256,
   11381904317,62731795037,31864743836,53768237128,48669885313,39450006657,61135071148,
   22005424516,68919796673,3744775689,71678655496,13816090795,69472108087,30132859280,
   63307735292,44894767847,54839192219,57347144500,45290121410,66701192835,34921108499,
   73125295176,23840611214,77724054443,12980317991,81247760644,3575186150,83416480277,4197902900,
   84057277700,11083960755,84191940875,17075677728,84951065912,21104620937,86029646265,
   22879349206,86691929504,23409258747,87643708139,22824073178,89850130240,19772979061,
   92352678577,14084338666,93965576992,7026229599,95511966343,1965457695,96988798392,14312844070,
   95943736533,28515411861,91892121402,43360679184,85640253013,60252472119,74335810354,
   76932782836,56973681495,90057693771,35883530638,100485670768,8696799349,103809802373,
   22589081393,96442694304,52392687086,80825454583,81942781465,50573047234,100055349536,
   13056873383,105970658963,30073393267,95044448558,74842898824]
private def pvm_w0_9_p3 : List ℤ := pzig
  [56005736247,91313131931,29377434366,134378418868,84768820730,16556944363,23883967208,
   214733441888,383377745090,442648207228,534239878748,855983177646,1428241735020,2124307212432,
   2914766241678,3992682605836,5623096498730,7929488632684,10898467024212,14588188817078,
   19268790936992,25322025788820,33031188690212,42514858212560,53867452619362,67318379672856,
   83208351290692,101801135300310,123132245360580,147041413136966,173324881958014,
   201819788581366,232320758333656,264416432574036,297417190219250,330449064328178,
   362625907749252,393148739732510,421268719805894,446189428923328,467039031976526,
   482971215137282,493333126946108,497780785714452,496270885099628,488959852976354,
   476105952529404,458050410055226,435276028467940,408474957052914,378551147014486,
   346534054983398,313443374077030,280173614566936,247447595485728,215840378777934,
   185835180032472,157863722752174,132304555282896,109445104056468,89435503834004,72264149875420,
   57770057816714,45687295185882,35703264006578,27510445487012,20838364112110,15463167057830,
   11200733948010,7892779502030,5394232349330,3566391784842,2276379586766,1400785382446,
   830580130434,474922813386,262655961074,141414623508,74996464760,39890804200,21762208524,
   12410636108,7438015412,4628693424,2924951110,1835446536,1124565676,665355234,377564664,
   204596650,105519102,51624616,23859924,10354328,4177820,1540262,500864,131124,18020,7689,8729,
   5341,2613,1113,421,137,35,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_9_p4 : List ℤ := pzig
  [0]
private def pvm_w0_9 : List ℤ :=
  pvm_w0_9_p0 ++ (pvm_w0_9_p1 ++ (pvm_w0_9_p2 ++ (pvm_w0_9_p3 ++ pvm_w0_9_p4)))
private def pvm_w0_10_p0 : List ℤ := pzig
  [0,0,5,13,3,23,11,5,50,217,778,2719,8286,23191,59484,140311,304748,606711,1095004,1751125,
   2345758,2175695,344357,8191604,26185763,61048370,120585925,211498436,335612865,485061872,
   638022307,757693432,797512883,714323402,487893761,140500876,253685612,579816285,718330470,
   597498907,240660572,220323754,585290615,674310588,427114053,43556807,489787670,655894909,
   433291648,53898694,503999481,621110900,318438395,202571161,574388718,522577875,79859104,
   419128150,583699397,278879044,249926846,563451701,394266480,113378056,513893281,448714034,
   23418786,466542609,465194816,21303211,435809265,458908876,26652019,424922845,436470348,
   1547814,430174249,397725240,58103024,443056803,338338324,136957094,451263409,252891714,
   228717174,439477095,138058730,319441392,393365287,89504,383717860,292202819,162646373,
   425444156,183944601,236330075,272215240,172518906,613000757,621397872,408688329,591878270,
   1438963317,2585072016,3613114383,4741054452,6690046519,9893753162,14112191347,18977839912,
   24710811419,31968872818,40973932463,51076347660,61323379809,71177781200,80309139917,
   87735058542,91608886135,90116019950,82398936399,68435011708,48381227979,22719945008,
   6714018710,36263912931,61435406388,78342428111]
private def pvm_w0_10_p1 : List ℤ := pzig
  [84202975420,77158335435,56826063658,25682515191,10447933099,43913638080,67581134081,
   76244471734,67235101263,41518525360,4939921161,32461878945,59800433044,69231060075,
   58054159256,29159586999,9060278859,44026961216,63039522553,58911057846,33380594361,3864845485,
   39016700130,58579298527,54092942884,26611288835,12162153779,44740010868,56483211337,
   42403020894,8916724505,28755782375,52460447754,49639111629,21059871388,18307929372,
   47415960357,50891418542,26900079725,12037685337,44690597624,51869715775,28309104508,
   12417719164,45558989329,50879497786,25082981921,16464318749,48341314516,49712622423,
   18290979630,25955856920,53100858715,44314164048,5343232913,37545840851,55044839406,
   34142081291,11836080215,50288842390,52211037585,15192832036,33426208112,57194478863,
   38029310850,10366864902,51745255491,53411953292,12411869445,39381995755,59703294378,
   31383740443,22710197269,58436272900,46122416277,5123912539,53069819018,56080116103,
   10049925902,45307869236,60830113877,22478735572,35905115936,62503184029,32874468410,
   27376798982,63193804435,40059428252,21252717690,62472252201,44027444158,16441583794,
   61110021867,46788837912,13571187142,61205670281,47808681360,14199737582,61771246595,
   45974467304,16790222348,61937901771,42954895246,20988896532,63231659201,38108570076,
   28387209430,63994273465,29497895358,36939706398,62197316467,18772379208,45401161656,
   58804404347,5459378368,54437409260,51346989163,11478587983,60293368440,38097409971,
   28437922819,60999886832,21023924865,44354329637,56113500620,997655244,56758052967,41716115748]
private def pvm_w0_10_p2 : List ℤ := pzig
  [24916290714,59672469587,19617748634,44851143312,52446366107,7244708799,57842706982,
   32863160503,35223611399,56285770380,2891555417,53665072519,38574505086,28082394426,
   57064403359,8224087742,52306889186,40275217135,27882644433,56548947504,5927849107,52597670591,
   36889768154,31365704038,55222535203,912799645,56265897460,29022497481,40997724025,50195299548,
   14797882394,57840003771,14747336658,51206134240,40175041947,32921341073,55977759670,
   7726863264,59580417669,18886688050,51382982800,41819157693,34042870727,57181997088,
   11369743554,62822147379,12718659252,58537552650,34846699911,45896079257,52390361684,
   27611842740,63487078909,6653807547,67141426602,14500745859,63461720983,34086926596,
   53719469712,50770685935,39905412373,63353281248,23909057500,70947240543,6949216447,
   73502659530,10237418605,71973704127,26757541608,67673947642,41392891331,61383307383,
   53287042818,53272629994,62631594447,43758519767,70258074360,34026245848,76498035051,
   25259303689,80931534996,17584147324,83500377719,10466266729,85214162180,4125325356,
   87058400895,381997754,88757050862,2741727841,89666468851,3815549484,90372790812,3834673135,
   91850442335,1661761276,93491376898,3120434420,94062335627,9382323439,93973600336,17012160636,
   93766154311,27366383055,91685094760,39890199654,86358183615,52689685281,78738048196,
   66312973256,67831453113,80603062257,51236491404,91909893130,30585019153,99303369537,
   6645388278,102433373822,22104297638,96158464849,50714594319,80620378000,76234552278,
   56486120619,97371333853,20409528598,104045534172,18315039276]
private def pvm_w0_10_p3 : List ℤ := pzig
  [98232622181,59488359451,73110719070,92013592744,30707458727,103846783101,13286766465,
   107681685240,84829200748,35375703155,56220196565,83392263072,230167873314,249809545752,
   230241203244,372613656830,736511976774,1197793988946,1670095489090,2284410941294,
   3293705808856,4843730544302,6917313981860,9519463212694,12860600194488,17309794539174,
   23185442701988,30643272808100,39786389699010,50847047865244,64210378726704,80243010733066,
   99111441107698,120773320760932,145120596210078,172088524569586,201594328571360,
   233362276800116,266813187829926,301126749595848,335412162794758,368828210998636,
   400562766416230,429731095266006,455331681380236,476339777918992,491889477681140,
   501418096002918,504684302257992,501678836230854,492525531307824,477459512935078,
   456889483452496,431474929046566,402136018107542,369965707013872,336083132399130,
   301502397349274,267072360295410,233492228773968,201363392524776,171226735244882,
   143556684840704,118718024681044,96915586020582,78168826991798,62326950305286,49118669541598,
   38216386481026,29292664332624,22055032482966,16256810351902,11690682343854,8175250658410,
   5543210163642,3635573886114,2302148742468,1405839214672,827690939160,470332375166,
   258780826998,138751282738,73293479530,38757258068,20908043558,11687739200,6800401180,
   4079075616,2476161154,1491843954,878228764,499717726,272893614,142341562,70652034,33250958,
   14773124,6158116,2385182,844076,263920,67008,9578,2891,3439,2011,925,361,117,27,3,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_10_p4 : List ℤ := pzig
  [0]
private def pvm_w0_10 : List ℤ :=
  pvm_w0_10_p0 ++ (pvm_w0_10_p1 ++ (pvm_w0_10_p2 ++ (pvm_w0_10_p3 ++ pvm_w0_10_p4)))
private def pvm_w0_11_p0 : List ℤ := pzig
  [0,0,5,13,1,41,128,659,2328,7569,22186,58987,142656,313405,620036,1083467,1593484,1690805,
   187830,5371944,19298929,48078582,99903055,182773556,300746581,448618868,606615089,738054224,
   793674719,725159704,506703919,157786938,244817934,578417833,714532758,578247189,200662478,
   269116380,614372715,653789932,349382773,147637631,558979684,634287723,314813070,205803862,
   586343411,561886418,140686287,379073279,611550834,374620315,152749857,552118148,495809623,
   26808808,459048058,540866149,144527386,375973680,545946633,207221022,321524790,534817747,
   226165462,299930806,518541515,209938672,308180260,498440903,163197160,339207796,469172277,
   88329304,382493684,421455035,11620621,423782166,345242079,129207859,444617990,232405649,
   251944359,428837634,90011055,345480851,338801326,106423192,447845079,284702180,129149454,
   194533039,282579563,861396986,1069027079,1066272690,1504316579,2751542368,4515599887,
   6379094514,8540883297,11752353906,16509631629,22581627228,29503055761,37316322842,46466544007,
   56916873970,67663934879,77304751346,84840338461,89588856660,90421423721,85617718008,
   73843930175,55168251442,30962027579,3122933684,26050783148,53194338529,73794308340,
   83544092011,80075728484,63520785353,36024262530,1578074681,33605480779,61666934374]
private def pvm_w0_11_p1 : List ℤ := pzig
  [75479346717,71390015634,50295862181,17024857794,20541470548,52403822283,68790557086,
   64023186489,39440236662,3042910823,33524781441,58434794658,62852215629,44328189836,9198472485,
   28845044905,54556788246,57869633089,37690459166,2047715281,34378557901,55388868078,
   50744665881,22303728880,16166326084,46068836403,53168326012,33941311389,2598390583,
   38053892554,53219605405,39168315752,3499600923,33722478719,51693884242,40314647307,5537032264,
   33066338120,52283894275,39396836820,1697524133,37128191461,52402838408,34379989509,5860103093,
   42934399270,52232759531,26226881462,18427506142,50815061667,47792031010,11173419921,
   33506157151,54833821328,37012986613,8381389397,48645409066,52921013589,16781305390,
   32578532202,57085447473,37628227394,11233823294,52003728389,52149048984,10045522201,
   41204057379,59083198600,27839582597,26827942059,59160022564,41863786009,11121477161,
   55375261740,52227615143,2886119938,49792719888,58214610563,14162850826,42692484688,
   60882514841,23680097962,35619643282,62554289125,30891769626,30691647080,63298536993,
   34792910040,27388919990,62724427887,36852892992,25186361646,62673714193,37710433062,
   25798702728,63401760681,35699381340,28918416554,63108274123,31428097074,32866726502,
   62539496197,25919187662,38812245904,61842854633,17169696306,46388753082,58242870917,
   5483129910,52796389486,51787870445,7351580443,58273320538,42600992393,22540416807,61431957644,
   28021354791,38072787223,58479482762,9574382615,50244217281,49781044892,10799766348,
   58458137533,34195554494,32570799170,58353449127,10912112344]
private def pvm_w0_11_p2 : List ℤ := pzig
  [49567708264,47127152215,14659660345,57641573070,26786454285,38969993963,54013599388,
   2140204202,55214608511,34610319428,31653025390,55116043059,4825970592,51931103346,38361036721,
   28050716359,56048177250,5899882839,52420272183,36856871182,30277582868,54365014395,1590899226,
   53684782110,32268320199,36354646031,52489332044,8654672068,57152743933,21012007454,
   46101823538,44756910239,23350600465,57116997306,4666249841,55938118041,31117286282,
   42306844790,50464708449,19811092491,59448387982,6553007815,57280386271,31564537260,
   45227783758,50844902763,25910947203,61623167986,2627097976,63036472507,21156234736,
   55899909014,42192775971,42075609439,57865673958,23767778554,66621582555,3094205905,
   68227779442,17955669863,63594300091,37422050112,54159185788,53516020287,41232080881,
   65086424054,25799907664,72010654059,8869597521,74998915592,8192751187,74853989527,23930585164,
   71918364128,37533726405,66344646055,49155466546,58819352122,59270464013,50651865755,
   67799387416,42890845002,74220787579,35604352423,78586112300,28470046488,81868834231,
   21919797851,84882929780,17001541344,87340685363,14016578781,88700749390,12228738516,
   89501153283,11395938477,90693808072,12495645300,91923688709,16071072785,92045871780,
   21199542740,91177608529,27396951083,90070757036,35742631080,87684887755,46379661011,
   82341433318,57542296734,74464294485,68797086201,64315379038,80850644274,49733791881,
   91431680269,30505418960,97919113348,8768400327,100747728367,16368269473,97452530876,
   43969387700,84485439497,68654123423,63981019270,89580344410,34687548765]
private def pvm_w0_11_p3 : List ℤ := pzig
  [102694179779,3019864139,100773173388,40360958266,86524464685,77119385033,53394287584,
   99996700910,9175966563,104461002627,39065532807,88949140436,89648283348,32946931757,
   89414042321,16230430612,152677687274,159694434556,84362215812,122129494388,358120423114,
   675661518112,952760773978,1272523423836,1869270319652,2896368167814,4330971059998,
   6137785542254,8476351118844,11691815702376,16111650987554,21906866600340,29181442146876,
   38167216399828,49278757897126,62955410202088,79463142016986,98861329309298,121139892962218,
   146341298456396,174508673723990,205499434696608,238848709895922,273811338570992,
   309529443892980,345159447959042,379853952205850,412652972330412,442432110351638,
   467999457741084,488293966030060,502550396890460,510332516483436,511451470932290,
   505872784984558,493704490044998,475272326719156,451206082138280,422448707324086,
   390157779831910,355544387127518,319730398575862,283682363895440,248224204639244,
   214084417902616,181924506596454,152321541965444,125715330447798,102354370244416,
   82273743545208,65318439889630,51202363965638,39579443285872,30103325000788,22462348685226,
   16389251273990,11654037833780,8051102191364,5389126020244,3487460360752,2178374742802,
   1312233104844,762416518112,427897644500,232829134376,123651739160,64783541258,33975348710,
   18124429672,9953928558,5640172656,3267240582,1904010364,1097535706,617156214,335152366,
   174566704,86778742,41007532,18348462,7736882,3054254,1117330,372170,108968,25640,3220,1109,
   1129,589,237,73,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_11_p4 : List ℤ := pzig
  [0]
private def pvm_w0_11 : List ℤ :=
  pvm_w0_11_p0 ++ (pvm_w0_11_p1 ++ (pvm_w0_11_p2 ++ (pvm_w0_11_p3 ++ pvm_w0_11_p4)))
private def pvm_w0_12_p0 : List ℤ := pzig
  [0,0,2,59,272,1233,4556,14861,42896,110801,254726,515581,890106,1196297,788514,1931032,
   10181385,29450400,67648107,134023826,236080481,374238696,535276315,687396434,781292055,
   761333292,587650611,263377052,145911754,516630745,705429544,614494657,255985118,224706034,
   596892827,657404934,355023251,152875159,567743226,624545787,273675444,260247096,609512303,
   518340668,44633631,458958005,600459906,261538169,287300745,590483926,387420517,149617879,
   547541670,446984015,61974907,506154618,464701217,23042087,481046460,455850497,26510519,
   474295300,426207501,65736807,480133012,374646319,133861911,487408852,296619459,221791771,
   481053370,188070923,315929565,444539822,50700241,395261155,360866666,109002914,442649055,
   237380860,242210698,387039857,610394,456274450,455479385,88799642,29535562,469515242,
   1266278549,1825829380,2181479075,2993730482,4797534413,7442612110,10488198257,14020015796,
   18756628015,25260010908,33295328445,42185887818,51616039947,61684925508,72062777033,
   81407464360,87892575403,90170612922,87527011297,79226216314,64318483613,42565219814,
   15471355845,13873996165,41883351152,65094951625,79949849738,82937212281,71991026978,
   48107171791,15500619238,19716188962,50835122503,71198028488,75275948077,60886029948,
   31095141709,6214575005,40987865146,63847708777]
private def pvm_w0_12_p1 : List ℤ := pzig
  [68100487738,51618032985,18701768612,19997850180,51042985011,63645282322,53634689729,
   24512037040,13527067104,46181795229,60008853704,48772468107,17231119642,20831780368,
   49041063115,55296159596,36534302375,694058114,35474381576,53897149839,45039483104,13568376875,
   24249376977,49138401170,48161752557,21198259136,17798992014,47000963517,49133930202,
   22657186593,16850083933,46207694102,48155126635,21048733530,19507404680,48539718319,
   46841055968,14629302629,27297382959,51311452552,41541643787,4115130924,36628850648,
   53123401425,32882892456,11158024704,47889589887,50362866520,16364832339,29649253149,
   54362643560,39323856513,5448479393,47130995318,53343867759,17965870688,31988997896,
   57014723089,37030894458,12447555752,52449668677,50669144664,7302200913,43073822437,
   58126122424,24006156963,30871997631,59531555744,37231433361,17197577819,57192994814,
   47585380231,4486063329,53434415958,54484705545,5659464426,48530327690,58034858597,14002577380,
   43069928736,60270266509,20746068760,39149547574,61969548361,24540122142,37128452588,
   62195826083,25849954970,35861581728,61862793495,26055978898,36346157800,62179783089,
   23969728430,39435398768,61547003231,18905618364,43284173180,59337353505,12476813444,
   47654716850,56661879807,3985187402,53400436046,51689589055,7664261959,58019524724,42891745515,
   20176495461,60000330126,31643438053,32973769287,59714075038,16770550563,46005567519,
   54102806366,2098528522,55141761151,41877900910,21271712858,58501473293,24762850972,
   39443218834,55096844549,2015602552,53466417340,41262100231,22768760815]
private def pvm_w0_12_p2 : List ℤ := pzig
  [57270458994,18985135117,43200484733,49953778322,7973821996,55799374577,30198913538,
   35476799332,53605488043,148761494,52907569752,34752944879,29974354121,54188656462,4490524309,
   51847366689,36447904278,30077510686,54303870663,2020418562,52723016840,32798649423,
   33525262561,52329977868,4003647634,55288169361,26199488502,41841967672,48337778673,
   16759832529,56908882708,12590014621,50622132371,38535216926,32033413602,55030745367,
   6264543847,58843007108,20627621989,49879767587,43123350462,30765778938,57236729717,5890438511,
   60955093358,19780576127,54223951843,41819519108,38652696398,57106851057,17075045273,
   64107480306,6991164343,62690559881,29980347602,53711564552,48942693253,38635618207,
   62046814684,19354052922,68700036171,1894283244,69226777166,22733970359,64337626949,
   41113628394,54791734028,55808580427,41474503807,66556499514,25667830306,73644182443,
   9019911733,77299876572,6989625311,77517773279,21647723542,74503765502,34982642193,69142923489,
   47060724178,62734513900,57442344765,56133905835,65561137052,49367895088,71567966673,
   42333616119,76365923370,35658945278,80578472353,30372970305,83887445056,26744454716,
   85857836389,24148549961,87023052086,22387873798,88300784789,22333406947,89511724166,
   24587671768,89649898965,28432243021,88655352816,33216764604,87321504765,39724010347,
   85174915596,48512751118,80601926663,58280195435,73429015364,67991016780,64398476045,
   78332532553,52231473678,88521276388,35501298575,95677286683,15749319112,99145024322,
   6260547082,98731464515,31543915839,90774318520,56824516854,74329870157]
private def pvm_w0_12_p3 : List ℤ := pzig
  [78336369839,51253134884,95681745818,19388648065,102839179811,17631307833,95975260154,
   53153491542,76797152395,85880709023,40015147712,102468455636,4295490316,101811433061,
   52430516359,77601266376,92839703350,27614381149,101747653173,14988679003,115793421744,
   117930008810,15165970776,2807631673,160785303666,392021895048,548312801098,684078502680,
   1017856818318,1698197538640,2688887660130,3923740758388,5526777168768,7819965139032,
   11121011796124,15593554356694,21332726701236,28571109187450,37747256531648,49349655537216,
   63710537435640,80967788044406,101206072435868,124582791511028,151269098734620,181246786842330,
   214157353576948,249339648553558,285997453836176,323319811515672,360447656568562,
   396352301453218,429785879290474,459395951779440,483944580482652,502484305937688,
   514392228099652,519290452127798,516967225300286,507390141122670,490804310312052,
   467825678646706,439437947931634,406872216303454,371428451617506,334327477407934,
   296648457622120,259344021951448,223280523697962,189249754616544,157932132201718,
   129831054631972,105217984250536,84120302203124,66359471634286,51622935115262,39541997438988,
   29751955268178,21923833095160,15770613851618,11038751279860,7496584752532,4927251327624,
   3128290614946,1916088091026,1131680712534,644903231950,355348239018,190142934604,99525190106,
   51505941378,26709863762,14064070190,7581111904,4180027774,2334661430,1301827168,714182450,
   380852238,195665050,96223364,45075192,20028866,8405342,3313888,1218434,413014,126516,33614,
   6940,608,367,269,109,27,1,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_12_p4 : List ℤ := pzig
  [0]
private def pvm_w0_12 : List ℤ :=
  pvm_w0_12_p0 ++ (pvm_w0_12_p1 ++ (pvm_w0_12_p2 ++ (pvm_w0_12_p3 ++ pvm_w0_12_p4)))
private def pvm_w0_13_p0 : List ℤ := pzig
  [0,37,292,1481,5994,20603,60798,155151,338364,605465,770238,146239,3026687,12387064,34227921,
   77607584,152809845,267194880,418336283,586242466,728934409,787197724,702808069,448459512,
   58162505,361025267,654007326,682260139,404744860,71002054,513267415,676497490,449727631,
   49411427,516793036,642847181,329299914,215544064,599871611,530449786,51288215,464587015,
   597597084,231318305,328266751,596096724,331646399,229766365,572484440,373965079,178504059,
   550504770,375708315,171690467,537196160,345764405,202383939,528803258,286133199,261404087,
   514662050,195666587,336293995,480107434,74685881,409581015,409684670,70600744,459255019,
   293684162,221033760,455612333,123531118,363850022,406085079,32681769,372220322,145910955,
   410010899,672623030,461120503,305207454,793864279,1857476048,2944666957,3874184524,5224268547,
   7724776476,11465777703,15997787554,21176409947,27553702718,35717131111,45434100726,
   55742362077,65801927098,75245447531,83494411682,89047196477,89878091042,84572310337,
   72822627134,54897034139,31225341942,3041812189,26692897205,53549146280,73087838305,
   82057727852,78516558389,61817624152,33499906553,1690261437,36347838182,62678395731,
   74762308592,69583675151,47508091554,13082015647,24816189409,55135023056,68685108407,
   61488141948,35729387845,1014772829,37273733974,60506174813,61791884148]
private def pvm_w0_13_p1 : List ℤ := pzig
  [40332074055,4373935456,32294230512,55787054655,56910440684,34639189399,2325306663,37954253362,
   55990263127,48232147584,18603035395,19072491275,47349066114,52560389915,31427589494,
   5920715448,39963034439,52347884138,36523904925,1259398842,34417939964,51051174061,38814978322,
   3795619653,33840602207,51197786094,37360229105,776327478,36128935886,50745585311,33643083276,
   5304251132,41578575015,50846545070,25969158607,16688132151,48083396900,46739078231,
   13333280634,29728741012,52680419311,38399877012,4183727236,44462967439,52192438180,
   21060389075,25921089091,53718263010,41250974185,2907483061,45740762890,53562159835,
   18853328518,31558497404,56944299711,36322345422,13850083152,53006399689,49042697520,
   4301470615,44923008363,56819671732,19934460007,34708272855,59443227258,32311010905,
   23133935467,58435645790,42288689785,11887383885,56158317440,49677262669,2864750931,
   53181280060,53938253569,4182394588,49395637576,56449581321,10019237934,46393421142,
   58549926409,13531299830,45296596942,59380810925,14203998470,44986686762,58793807605,
   13483981564,45420601828,58258833401,11175808536,47951150230,57087348589,5857141974,
   51471791796,53656467315,1340067263,54454147518,48863457403,9573245479,57772065910,42483665415,
   20214876647,60330592946,32327394623,31962797539,59415054630,19264446371,42446821531,
   55329187898,4329838815,51911765735,47249377284,13503005956,57990971677,32780196012,
   31405280190,57130420167,13892784158,45832947084,49624319459,7599053587,55632416336,
   34147533413,30358188245,56147283926,10590791173,47835480751]
private def pvm_w0_13_p2 : List ℤ := pzig
  [44853102156,15257168562,55592928395,24064072162,39075537156,51056435873,4726242555,
   54155091192,30910069279,33470728501,52377515326,820741999,51671544379,34027002470,30453548106,
   53352466987,1931656574,52472065844,33001227737,32919771551,52016194318,2458259238,53386115839,
   28365296354,37746364278,49948414021,10856616295,56405121328,18857568635,46747355561,
   43078967888,24475015370,55816131339,3974291344,54577481630,31267018243,40435434441,
   51086409898,17231474532,59469925261,9675259978,55359986816,34721498921,40386446693,
   53233475940,18081290200,62160231503,7167089174,60414720150,31100021537,48842943457,
   50280223454,29858546498,62410155055,6808402957,66359818632,16798784603,62070357937,
   37991261752,50455274142,54739019693,33284052895,65961659946,12925338502,71254021185,
   8127326392,70612850372,27824075789,64400463317,44918183984,53507015326,58877997549,
   39400273499,69456046282,23788817092,76353599887,8022925523,79349156782,7260083673,78742571419,
   21870991202,75516177988,35460057233,70840780327,47310705562,65357074442,56868979791,
   59089030467,64363388680,52159334894,70587980079,45362853667,75967205442,39692575958,
   80151326983,35375803661,82814707026,31892038860,84510694833,29121076767,86119067266,
   27868492576,87580744299,28758778035,88040426920,31250207900,87349491621,34649067777,
   86271713000,39490577054,84741361233,46542836555,81387937538,55024310966,75600018863,
   63694847451,68103312530,72879657116,58459362719,82769683271,44916249862,91212028036,
   27733233097,96470356653,8402589758,98852762064,13843408302,96488660581]
private def pvm_w0_13_p3 : List ℤ := pzig
  [38625276973,86243993658,61890297558,69036025647,82019829131,44963592864,97426000532,
   12418926189,101611142357,23171511013,93430032962,57823916932,72425761437,88355747805,
   35087080984,102591431390,8430568348,100635337875,56073667193,74182435848,92853398874,
   27555971509,106293452969,24609848571,101971463028,96533046882,21366961495,62887759475,
   66698220850,246003001630,322708078800,343731240112,519220632776,981311824680,1669684228076,
   2495396854620,3566403855708,5188765549338,7655607150002,11101626406602,15605530767654,
   21407498820418,28971451585366,38815278061840,51304402308262,66631481366816,84973703748534,
   106611864813494,131844164138892,160760396452502,193091635077026,228262847895896,
   265563043814296,304241650991406,343440186907656,382054885867448,418704529511452,
   451879873294960,480185540688708,502512794142132,518058312302254,526244170252128,
   526666683950044,519152443990978,503886561727452,481504381096078,453059735742130,
   419871366453820,383328036632552,344745757566434,305319296051194,266141952082690,
   228231777676682,192515775375028,159766656564570,130525247087184,105052359511730,
   83336347089968,65153018700078,50152130753354,37939281479424,28131869250162,20383814490242,
   14386774672718,9860886355824,6546131039834,4199789805110,2599932508016,1551729913902,
   892913269454,496006341300,266762181228,139630201384,71699801316,36507107432,18652552524,
   9658687246,5089271850,2717746346,1455458434,771358712,399482550,200104168,96192372,44114352,
   19207950,7904928,3059916,1107238,371268,113778,31090,7188,1208,38,63,23,1,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_13_p4 : List ℤ := pzig
  [0]
private def pvm_w0_13 : List ℤ :=
  pvm_w0_13_p0 ++ (pvm_w0_13_p1 ++ (pvm_w0_13_p2 ++ (pvm_w0_13_p3 ++ pvm_w0_13_p4)))
private def pvm_w0_14_p0 : List ℤ := pzig
  [110,933,4868,19271,61420,159273,325150,446561,6035,2571876,10730509,30931156,72987547,
   148569806,266448361,424198702,598655961,740812940,782851603,662407100,360134405,66342439,
   477839026,698196623,602342504,206459849,302552775,642569260,598137739,176426788,361472994,
   649738145,473100986,52492874,535054697,593533362,171453587,389511161,613995206,301636493,
   275987631,596627022,360866051,212721205,574915884,370806385,198797355,560283612,343456687,
   226743927,550140374,282394261,286095861,533301806,187203159,362646341,493822430,58902029,
   436790739,415290004,94294860,483019927,285953760,254010130,476193077,111662576,379948462,
   379289227,115015213,483687274,279168105,191620103,253028894,273417484,855769673,986830074,
   906996349,1350388178,2647773905,4399113240,6173099827,8286676314,11584719489,16501390606,
   22681555619,29662782688,37615977127,47031114888,57714140797,68456963970,77812242293,
   84850959220,88851242225,88496318082,81982718221,68204482164,47643266695,22011435488,
   6538090024,35345404639,60590364928,77563765887,82328452864,73355034139,51773554654,
   20757305497,14642640047,47382112930,69545153699,75060967842,62206531313,34105064964,
   2404084256,38100676863,62906650708,68693100067,52918587386,20522164951,17723920307,
   49213102062,63444671011,55081935214,26366925325,12269761077,45474008902,59661473647,
   49259652594,18849937399]
private def pvm_w0_14_p1 : List ℤ := pzig
  [18992587759,48342053050,55971444211,37704281758,1772002861,34391420869,53092958504,
   45457923737,15445175032,22182840992,48358521127,48848855744,22641639415,16049900817,
   45352813052,48696773515,24390052918,13772225744,44056072627,48427511498,23331818705,
   16577557023,46313370764,46684075097,17337487634,22999849432,48634177619,42847137076,
   8566800483,32212216323,51665100010,35458272005,5752180557,43078385418,50124735233,21744779978,
   22421095112,51116832753,42905138772,2502988029,40605441551,53388961346,25386202969,
   22235147195,52934095618,42940123149,621201115,44448939988,53646894723,19542970650,31199829372,
   56839703899,35573385658,15298168622,53598787097,47343716464,1174362665,46693944707,
   55193045358,15696190945,38239429785,58835157114,27191555337,28735100743,59034033828,
   36503352089,19109323465,57931619824,43923847591,11229362127,56507754836,48643717913,
   5470486043,54315556938,51232784317,837381601,52191155582,53248052405,2140936046,51652711636,
   54324066431,2321188414,52079139616,53527980729,665152352,52555922550,51940051705,2072556075,
   54196605200,49888244031,7255476465,56917134444,45563715325,14718269567,58662979246,
   38955195199,22710964953,59424380478,31042993957,31777078387,59431917356,20251529889,
   41900897863,56121552394,6255558927,50193500047,48646171738,8687174606,55745454585,37929493504,
   24515300438,58133537007,22357014224,40193741016,53920688751,2492206656,51309326656,
   42450627411,17891952225,56163931054,25207074565,37259991881,53180257070,1891024621,
   51647523769,39087853452,23096863604,55117728189]
private def pvm_w0_14_p2 : List ℤ := pzig
  [16411373090,43140493744,46874797119,10535661851,54429033862,26325687491,36996093027,
   50644839982,3724331558,52611482669,30369225392,32660123704,51356426895,8648668,51787815770,
   32137458813,32687728301,51899615324,2063579502,52967068083,28832966016,35981440140,
   49729277919,7436111773,54518203650,23147480069,42589015027,46514919172,18271776804,
   56348077183,11049053594,50651124042,37337873911,31716279347,54066484904,4958714920,
   57620238195,22849640708,47764487188,45376488581,27260484909,58101559188,892083176,59017958569,
   25775536336,48641083250,47608089823,29485954129,60856462638,5270025636,63706044945,
   19905814516,56360341964,42230496101,40692435963,58657726468,19598180146,67212071969,
   3734685196,67163460226,26412972235,59053467835,46136867794,44508067810,61230667967,
   25805002183,70572172144,5293904118,73605032035,15096127734,70469571080,34028046905,
   62082859295,50577771108,49941651828,63954295583,35625267747,73460772654,20295985526,
   78787724721,4593801761,80321484128,11000718869,79026404223,25759400066,75862050268,
   38787520141,71273779441,49586131492,65334296850,58426158445,58391089197,65956257906,
   51368524822,72406487175,45205590167,77408313500,40088656044,80748967225,35599993515,
   83014421464,31713161856,85046846309,29194956407,86870951950,28668996646,87779073771,
   29735888767,87597080510,31723701980,87039817447,34979675343,86324608394,40349402392,
   84388458627,47510828745,80379499658,55289615318,74789474453,63629371181,67749358410,
   73170362226,57753397695,82788864433,43988641838,90400935406,27628719323,95775033991]
private def pvm_w0_14_p3 : List ℤ := pzig
  [8786099930,98583897432,13636695054,95811791129,37644389931,85925438280,60158802800,
   69986916139,80826410255,46237743862,96227895198,14555467941,100835034073,19727671407,
   94661057616,54855896894,74756391035,85538266437,39449076536,101523120138,2748977450,
   102471613633,50742788863,78707262664,88541736648,36150809793,107972164737,18866847175,
   101797068522,80308643128,47751529703,89310793279,32633407980,177138819168,193391250064,
   143096013982,234430146468,568988938548,1051128827622,1580348163532,2271436184344,
   3422206312496,5285214621772,7946894141478,11469268141394,16114796333362,22377010136330,
   30782078057238,41696238370878,55349803910944,72018604634896,92117229563348,116062863194658,
   144027075459046,175809241616196,210923960942000,248768150730168,288668243436036,
   329758583521790,370835268200562,410365598399676,446688731903470,478273284224148,
   503864729143392,522474493547722,533307297141198,535760776499968,529542083504508,
   514823569732722,492312757496616,463170879784990,428819421897978,390738788685192,
   350346444353268,308970256881450,267867033246370,228220144178006,191083735873104,
   157290919677568,127373201153872,101533381169616,79684601519250,61536538317392,46693741967296,
   34735055860076,25259429973336,17900795961000,12324801438724,8221198257770,5300554975970,
   3297353402026,1976891629428,1141928629942,635986983870,342234339196,178637466886,91009995152,
   45645972808,22769005906,11405618260,5771905922,2949759912,1511924860,768701130,383045782,
   185067740,85942830,38099484,16034526,6375076,2382546,832156,269568,80100,21446,5014,960,132,
   12,0,0,0,0,0,0,0,0,0]
private def pvm_w0_14_p4 : List ℤ := pzig
  [0]
private def pvm_w0_14 : List ℤ :=
  pvm_w0_14_p0 ++ (pvm_w0_14_p1 ++ (pvm_w0_14_p2 ++ (pvm_w0_14_p3 ++ pvm_w0_14_p4)))
private def pvm_w0_15_p0 : List ℤ := pzig
  [1634,10153,40244,113513,211260,88393,1210469,6288262,20721945,54145182,119628015,229369412,
   385532611,568095338,726388849,784635384,669464701,355713076,91192042,510437559,704047622,
   547171519,91397378,420658512,674303197,487706332,33424946,529870849,630186000,243513727,
   335422773,634790940,394916267,186022787,596275182,459612733,103347577,562155576,471665919,
   82689409,547386462,448253549,113702229,548671324,392854513,185243887,552273398,301799981,
   283474115,538174498,171427011,388363317,484127864,5329897,472063361,372290402,178639170,
   500311451,195799170,350153720,450174897,14577011,437778534,263109819,297354927,543261134,
   215148677,146111135,103990567,883030340,1541145661,1812230582,2272232995,3673493320,
   6065873441,8924375974,12110077723,16308551680,22296116387,30025502434,38779265369,48111384448,
   58150510447,68749254730,78659028813,85931371048,89027910449,87158789954,79595656725,
   65319489068,43931286309,16852215690,12717514622,40965977203,64247997456,78905643041,
   81369493578,69576748315,44696831866,11334172015,23919379921,54010064224,72238274993,
   73392285166,55937258809,23825228536,14146518402,47321845487,66404521478,65624398461,
   44409647610,8732255121,29568897729,56827704994,63246341929,46758919906,13431884677,
   24616447247,52803674164,59306558329,40801449202,5134301457,31887513185,53989500956,
   51642152741,25859336780,11907582934,43875705597]
private def pvm_w0_15_p1 : List ℤ := pzig
  [53952287922,36629260015,845578044,34649393914,51491004619,41051382118,8623204705,28680056479,
   50051664886,42667155867,10346405854,27827907056,49120185329,40998628530,8289016035,
   29645544721,49616916280,38389030435,2170924818,35803759540,50278670131,31462318174,8195884206,
   42467140749,48421039530,21343342395,21146947957,49551190020,42907662451,5160693064,
   36557369080,51803327931,29331795222,14808874840,48570564643,46499770748,8930968415,
   36339102411,54009590982,29443037633,18486358069,51998785556,44507849975,1552310064,
   43212661498,53662544267,20131230440,30837654338,56675793141,34845935516,16665139170,
   54158317431,45648744232,1942070532,48338981743,53311082910,11383113355,41402113749,
   57699286918,21967856039,33842377127,58949865608,30409688813,25939640195,58758404644,
   37427295893,19243667533,58466814170,42285457509,14683911337,57640587218,44798517195,
   11379206225,56342945672,46365604195,9180303845,56053457760,47257626647,9386069183,56836503682,
   46226980095,11779781031,57344882156,43598809487,15052562635,57966163564,40381132195,
   19899782341,59389489504,35305525251,26991073561,59857897290,27436460755,34544963167,
   58276819594,18097995939,41838080901,55425353774,7050775263,49506525283,49907668994,6785943580,
   55405866973,39904523736,21329575938,57302327137,26704727432,34817516080,55511340643,
   10592666722,47135263192,48318055217,8873052687,54964234630,33929267507,28037963453,
   55200340534,14777557913,43609152729,48065842284,7453261974,53830668709,32097755320,
   30488052444,53806974077,8144307210,47424850204,41668733191]
private def pvm_w0_15_p2 : List ℤ := pzig
  [17599914825,53958579576,20091744221,40376439019,47733728544,8567962822,53473367869,
   26407420504,35995429862,49451704289,3822870251,51710758044,29331620073,33372262989,
   50568198590,2501913668,52572268023,28909468166,35595284524,49714388761,6448507455,53346605616,
   24582569209,39440888515,47482649154,13195920834,55583913579,16895518392,47152290254,
   41949000691,25293225595,55248759290,3480105729,53801756749,31373470240,38649301136,
   51444141823,14091617367,59198706196,13763781357,53364021689,38635050834,35797249766,
   55452638517,10704879011,61234556322,16538746017,55374761317,40647754318,39424876140,
   57467544811,16535193017,64607038102,9267460991,61588366207,33824362784,49574494886,
   53516959739,30840691477,65794396264,8197228776,69483427017,15472346788,64812643508,
   37502991151,53133086091,55630759672,36420526558,68169589109,16751129361,74218002922,
   4035948961,73803056099,24393207030,67801575190,42946170027,57573324001,58445935240,
   44461935522,69955470429,29476823303,77160941564,13364787102,80482087605,3065529876,
   80760082558,18780590167,78709510543,32801393802,74635592492,44701743921,68714449427,
   54749442850,61508222960,63420504269,54030709329,70769568396,47154379038,76432131671,
   41033928675,80312326882,35356150842,83034710819,30193437311,85407410906,26287327282,
   87518033223,24243856949,88800114568,23770908554,89098202321,24245403103,89083911234,
   25874024928,89171981675,29497193713,88615700498,35149990196,86491893413,41866399133,
   83018884350,49313518226,78634390543,58226105449,72323607006,68400498862,62713108007,
   78074221755]
private def pvm_w0_15_p3 : List ℤ := pzig
  [50168612582,86360328668,35332395771,93553758729,17017427588,97982539980,5034318690,
   96806637123,28263481759,89868835242,51407847456,76916731615,74041829265,55227770264,
   91462936480,26068641861,99879967143,6930387433,98822646228,43304869570,83286117231,
   76210611027,52936123638,97709286260,13283910165,105812802883,35259079961,89655235904,
   77123352678,54216230307,105923095293,506590658,108265763986,59333557986,73847316521,
   94645472571,35822483182,147772725334,109242463996,18872716304,81554023638,348474611736,
   681485347740,988480164422,1415823429412,2253157549816,3690324335536,5751998229712,
   8497274052882,12233667884036,17483995705042,24753945840080,34381947542760,46635161641940,
   61908405737302,80758849152910,103700396719000,130950044190744,162358881033256,197546051034984,
   236038618099868,277235660630426,320226203950128,363661213476152,405837525325924,
   444955581411208,479367712015632,507671686374864,528668059619510,541322421688588,
   544847932407032,538890605185422,523689998319592,500093649013590,469406985581720,
   433167120155764,392957434114436,350323069577664,306762912176460,263727105140406,
   222564906450580,184421142673012,150125901360666,120131846806602,94527737235290,73118309727458,
   55534313582166,41333272075100,30066842062148,21311461972528,14673794739546,9786681754054,
   6307076410272,3920008137874,2346679135176,1352374170362,750567369944,401815191142,
   208149419406,104865795512,51747499350,25229576076,12259913018,5975213836,2924880202,
   1431615720,694422454,330186714,152271338,67486810,28529796,11432816,4319042,1529832,505014,
   154216,43128,10886,2436,472,72,8,0,0,0,0,0,0]
private def pvm_w0_15_p4 : List ℤ := pzig
  [0]
private def pvm_w0_15 : List ℤ :=
  pvm_w0_15_p0 ++ (pvm_w0_15_p1 ++ (pvm_w0_15_p2 ++ (pvm_w0_15_p3 ++ pvm_w0_15_p4)))
private def pvm_w0_16_p0 : List ℤ := pzig
  [11714,47841,81190,194520,2029421,8945780,28555973,73690624,160364251,299768888,483953551,
   670927790,782009695,725521222,449163157,1024999,459637942,699326667,562113374,92252127,
   438635915,676392642,434901547,129633675,592451444,576651533,80434842,481990884,613917315,
   186770360,410716674,611051533,214160918,391391788,593788439,181590954,416049884,562962085,
   99055710,467399214,506213147,26026997,520991554,407098155,180652653,546200420,254264945,
   339660909,510633968,51218489,464472655,391034430,173701242,506305283,180787844,379044962,
   447583577,50164311,433355382,162943281,444671177,655847652,335310919,163493436,750079527,
   1859715016,2833062153,3633762764,5061048039,7820644172,11758244235,16337563848,21661764963,
   28529485440,37380342057,47584742030,58037271737,68112269296,77518650743,85254505272,
   89276915495,87544387462,79141964089,64159925966,42928494121,16177040924,13832194170,
   42876091043,65997910484,79185662053,79948339776,67151168531,41582662942,7205446391,
   28756338791,57871222448,73253147245,71130551612,51336111905,17906088596,20576803404,
   52708586281,68340936828,62593527621,37365506854,448335505,36393971987,60338033908,62046124029,
   40355280354,3682231869,33448101381,56525632416,56474128803,32969126696,4625074488,39939196793,
   56627616838,46801242083,15372715106,22549578014,49031224761,51335544342,27870795891,
   9985456305,42447117530,51784964323,32863554728]
private def pvm_w0_16_p1 : List ℤ := pzig
  [3662233830,37588774743,50288143992,34489952723,1394196497,36760483696,50113443431,32757232570,
   4741721860,38990867521,48726412408,27891561063,10779706843,42976468854,47372271177,
   20054052358,21211422232,48195926725,42102445294,7039525629,32938729739,50270465452,
   32401343681,9020250057,44751519210,48148653099,15744201984,28710969344,51816058627,
   36070560630,6939188394,45111701453,49250880934,15134951923,31653976019,54067627202,
   33300060427,14562752967,50861885936,46040144793,3758103848,41971849424,53669024371,
   20716174192,30406853376,56440374445,34196578424,17842496170,54626122859,44034478156,
   4910094958,49819729799,51267328214,7103766351,44164280087,56078401214,16740007281,38342575877,
   58183756890,24189843181,32185283037,58678017680,30435721133,26719063963,59099514594,
   35073548957,23228133059,59293391622,37367734911,21212000823,58716130966,38258700501,
   19960945247,58440492994,38562561601,20498270243,59141988048,37184227039,23315364425,
   59525890450,33660067325,27048395765,59123521650,29168416769,31479545485,58888857810,
   23356743879,37622230699,57876231450,14819690239,44304710221,54288861454,4484143781,
   49787168999,48643012828,6595334306,54494067321,40940855692,19354637250,57553147665,
   29290981870,32692977334,56223616259,14311276640,43753040838,50354696277,2062454431,
   52030290736,40191705855,19935622389,56088358462,24066721475,37087594599,52442421824,
   3628759661,49054212281,41149356824,17393086228,54327382241,23420270212,37161809398,
   50756331211,440392083,50889149416,35709442187,25126617429,53061896412,12467256731]
private def pvm_w0_16_p2 : List ℤ := pzig
  [44069779779,43275232206,14301909586,53357483663,21570273368,39257619092,47336334237,
   8348037127,52425457764,25515865843,35697460539,48410601524,4855243234,51870564401,27539723186,
   35510995292,49331619789,6256701909,53136856366,24952145389,38401295549,47375277188,
   10834710422,54012091059,20136113860,43420095606,44733761391,19535932375,55828697344,
   10096420327,50733115371,36886646428,31475759304,53677934235,3738757625,56476487286,
   25029230869,45104892773,47689695612,22806532394,59120178339,4908777392,57189280826,
   31762737793,42888440279,52145049668,19732763162,62189251271,7303181776,60335673570,
   32987757225,47367757629,52875480182,26007977768,63992304917,214809667,65096647486,25656553407,
   56573959315,47665222928,40099834912,62915532553,18215696239,69891601890,6089480695,
   68449491527,29769020644,59521176864,50097220309,44680416089,65030736956,25756790920,
   73479082911,4621810171,75366587168,16868756985,71417575753,36917547330,62742331756,
   53956944991,50446376363,66943644108,35488412926,75582338789,18818442837,80248150192,
   1567602738,81588186787,15014487976,80091343208,29935498669,76002918719,42832396596,
   69651787422,53921374805,61796629477,63493607700,53504925432,71461331179,45580149815,
   77493478846,38162204620,81615653597,31045329961,84494333118,24396981456,86910830515,
   18936071229,89006944894,15235861078,90351933901,13076993051,90839228914,11886986446,
   91112220903,11760096311,91727203468,13475005686,92237682735,17313046941,91774778862,
   22562418000,90333049897,28732309425,88475029338,36453820634,85721547999,46172566709]
private def pvm_w0_16_p3 : List ℤ := pzig
  [80626923360,56805920690,72772249325,67161120225,62802502712,77488511082,50069798957,
   87493426829,33075697228,94692574768,12573585495,97380376199,9688755817,95712564290,
   34007502454,87682899641,59089679435,70658955988,80202405378,46334233305,95257248809,
   15765934072,102240528954,21063552416,94985855753,56996221635,73552314580,86561503572,
   39545564269,105630485523,7456932605,102492689912,53822677024,79589977833,94523496163,
   32877135250,112766732490,26018234144,100155800369,79634684455,63002577810,130706730286,
   38838405412,60414989681,17107880762,247144575628,454956725056,590426908676,851175964036,
   1500769274814,2637490960864,4226355759938,6357843224408,9408850609394,13914057442124,
   20319350642024,28921503673888,40052177053620,54258600038256,72235065901788,94547904843532,
   121421339418978,152763059669970,188330008635166,227789859377444,270570533263498,
   315640176783988,361449997780694,406121206179312,447737375560730,484536793565308,
   514931904045628,537463696895178,550850880147666,554183261803176,547155413236252,
   530182281530448,504319333705800,471043299246630,432023420712086,388981898190960,
   343649795863352,297751747956816,252948134965210,210715427018960,172204898205824,
   138143770647482,108821859891548,84162944708522,63844051758836,47415630207548,34389567417360,
   24285957803740,16648698549166,11047124656102,7077375247680,4368996841592,2595238752414,
   1482423513132,814439872362,430926948276,220175242010,109102141876,52752014804,25073849604,
   11805621300,5538000060,2592978840,1207890016,555598656,249860732,108739852,45371480,18005098,
   6748692,2374208,779070,236816,66146,16808,3836,772,128,14,0,0,0,0]
private def pvm_w0_16_p4 : List ℤ := pzig
  [0]
private def pvm_w0_16 : List ℤ :=
  pvm_w0_16_p0 ++ (pvm_w0_16_p1 ++ (pvm_w0_16_p2 ++ (pvm_w0_16_p3 ++ pvm_w0_16_p4)))
private def pvm_w0_17_p0 : List ℤ := pzig
  [22236,21783,381565,2785340,11738793,36970594,94227759,201207280,365406905,565544550,737334595,
   781896590,610273591,213781436,283372312,647079487,655728300,266549117,299036783,658234044,
   533680285,2674921,535629462,618379761,165124088,432925870,628612861,229272368,388333486,
   615899985,218949004,399312902,591623963,150093824,448913730,545752189,31205746,511847670,
   459642707,126342861,555269486,317004505,299194061,542288334,115629835,447722263,441676470,
   122281818,521839231,245621506,342019546,469656213,29758603,495366662,318546149,235282021,
   376305950,146451890,716952793,725483962,452108441,732295348,1864991225,3301286732,4568796481,
   6129152430,8938531453,13325384630,18785106833,24962953980,32346468023,41581880872,52333428983,
   63286723930,73223235597,81528119304,87392999001,89025156016,84284191495,72120878848,
   53049507449,28373912902,274306394,30192159973,56936322524,75298241311,81344163924,73573286523,
   52695729712,21451249799,14784213177,48020480064,69760139127,74186836312,60064790107,
   30672602934,6911735200,42593973385,65377590192,67392481423,47676159566,12855745955,
   25468729685,54515612418,63958753131,49592502482,16187354697,23128493075,52215399084,
   59247108479,41646860122,6780905649,30734864381,54299439350,52588368897,25963655234,
   12654718532,44217218905,53400662500,35955653561,501978674,35133148542,52068437327,40559858596,
   6614031841,30595937361,49933807212,40655994101]
private def pvm_w0_17_p1 : List ℤ := pzig
  [8192855328,28983174352,49157939377,39659684054,5507525969,32232729733,49467900630,35124308527,
   1531422375,37092531258,48737847127,28407884612,11317901606,44002923205,46684052608,
   16781044157,24987233023,49194618396,38758510985,812945030,38140500908,50084762321,25354052208,
   18838325872,49524371709,42872265946,3466395405,38705645495,51384080506,24609617723,
   21607008997,51662888444,41190457603,2712130539,45148941614,51107270281,15125340164,
   33423459202,54588707325,30727910828,18971674592,53454531743,43056854240,4610181634,
   49041872543,51101682492,8326240729,41893521435,55310663684,19957394763,33303564985,
   57334971516,29922686935,25226813893,57933779656,37242046987,18303852969,56869372744,
   42210277487,11972629659,54931164854,46141933281,6691605439,53668420934,49061781487,3645509431,
   53102558078,50151771485,2469478023,52412455256,50074327385,2168763705,52306661406,49839014287,
   3476789975,53650788860,48522089201,7192301759,55297978956,45242571047,12156559251,56363670082,
   40962685379,17810140641,57698266008,35643370855,25245672109,58747797322,27663990349,
   33810360519,57473438884,17370630333,41563672665,53885647310,6008735107,48614851639,
   48274619312,7258413192,54581207285,38702400684,22044251754,56642396703,24942357046,
   35453020252,53857925449,8957566336,46437981980,46630793583,9161070919,54033778028,33200738509,
   28077678815,54558363118,14008573365,43216949075,46832706486,7244295690,52197170789,
   32061343124,28502514548,53191323307,10080993980,45903089640,42680237127,15348924365,
   53058185320,22118554187,37163156809]
private def pvm_w0_17_p2 : List ℤ := pzig
  [48084917044,3794168524,50980838017,30843622958,30640691376,51218410653,2848086292,49169414870,
   34575995243,26563879611,51522931422,6533535039,47587554685,36704732444,25216266646,
   52651801591,6431434402,49135099020,35527326735,28197053769,52011965130,2308781149,50821359321,
   31937236592,33021025556,51273413117,4824971389,54741730846,24844224963,41875286739,
   47273500822,16923001282,56419297455,12819859002,50284843198,39286377157,31014456317,
   55810219734,3894399526,58650167001,24295179748,47590910786,47050873817,25624387153,
   59586537456,2065271595,59665224543,29470001288,47749731118,51118308043,26574417873,
   63131482190,346927278,63794797663,26185554000,53598017736,48608445187,34825190321,63521889064,
   10865622908,68970271281,14543146112,64599996102,37953281423,51549448727,56617237394,
   32096958694,68666754703,9132039447,73138552184,14430141597,69943802187,36133066302,
   59824883380,54226874259,44258667705,67647112748,25225669298,75830816891,4823024165,
   78559656542,15167950781,75964992779,33551977148,68652114550,49677497221,57738921879,
   63147960650,44626811560,73565378543,30559720983,80571282992,16284986534,84156929113,
   2117624005,84887750126,11648314697,83698096571,24426193058,81348439828,35520029819,
   78079902021,44651908456,73879907760,52193066985,69078815001,58707968476,64508169388,
   64275172645,60912587661,68460791730,58322528986,71055681691,56305723005,72569880618,
   54868646942,73652603371,54710945423,74157515742,56315870846,73314581253,59200507299,
   70896902662,62649211404,67496441029,66871191141,63239874948,72484132670]
private def pvm_w0_17_p3 : List ℤ := pzig
  [57090949575,78958004121,48260904148,84889569374,37333236239,89886099077,24718244138,
   94280648738,9368691151,96785942117,9038545213,95152804630,28647004394,89080727445,48322236055,
   78683478814,68213510118,61768736575,85589501209,37782043410,96495300868,9557881911,
   100263119003,22245920653,94406663078,55713461950,74825539273,83244367887,44353857250,
   101367100700,4723070469,105596610717,41366881249,87797195892,80360423296,53232048745,
   108231848187,360516360,109790427402,55672140464,82879671189,101230058517,30685344968,
   126238535304,53376524684,73890353515,51752430171,137331383502,316852088814,385435180220,
   496015087082,912385263206,1749784854974,2954472562562,4555524335010,6870435836018,
   10414957494598,15646346768786,22867123381230,32399365995618,44796355914870,60809731663324,
   81116520051256,106076369926868,135731523889120,169971073808282,208601918238824,
   251192445471434,296824285760126,344002887610564,390829711723946,435300562561222,
   475511282686614,509686409394638,536140997633266,553345682363656,560148262308460,
   556039423700410,541291076415662,516883558339458,484282075334872,445200867116264,
   401457890521242,354923275371348,307489570000372,260991468875734,217061311913440,
   176969126779264,141517022844078,111030657005120,85441684602812,64418044260670,47491241655880,
   34147413061350,23875254986068,16183228499060,10604237017188,6700912707198,4075692598870,
   2383017219022,1338677589332,722764236816,375588742226,188378631766,91588467210,43421563230,
   20213910030,9302792278,4252257076,1931918024,869002780,384024322,165108998,68377914,27026864,
   10112922,3556252,1167170,354974,99246,25270,5792,1172,200,24,0,0,0]
private def pvm_w0_17_p4 : List ℤ := pzig
  [0]
private def pvm_w0_17 : List ℤ :=
  pvm_w0_17_p0 ++ (pvm_w0_17_p1 ++ (pvm_w0_17_p2 ++ (pvm_w0_17_p3 ++ pvm_w0_17_p4)))
private theorem dk_w0_0 : muxFastIterBSlideChk 5 513 phbv_w0
    rkmViHi_m1024_r512_s1_c1 pvm_w0_1 = true := by
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
private theorem dk_w0_16 : muxFastIterBSlideChk 3 513 phbv_w0
    pvm_w0_16 pvm_w0_17 = true := by
  decide +kernel
private theorem dk_w0_17 : muxFastIterBSlideChk 3 513 phbv_w0
    pvm_w0_17 rkmVoHi_m1024_r512_s1_c1 = true := by
  decide +kernel
private theorem dkhb_w0 : muxIntListEq rkmHbHi_m1024_r512_s1_c1 phbv_w0 = true := by
  decide +kernel
private theorem pw_w0_1 : muxFastIterFullT16 10 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_2 :=
  (muxFastIterFullT16_add 5 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) (muxFastIterBSlideChk_sound dk_w0_0)).trans
      (muxFastIterBSlideChk_sound dk_w0_1))
private theorem pw_w0_2 : muxFastIterFullT16 15 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_3 :=
  (muxFastIterFullT16_add 10 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_1).trans
      (muxFastIterBSlideChk_sound dk_w0_2))
private theorem pw_w0_3 : muxFastIterFullT16 20 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_4 :=
  (muxFastIterFullT16_add 15 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_2).trans
      (muxFastIterBSlideChk_sound dk_w0_3))
private theorem pw_w0_4 : muxFastIterFullT16 25 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_5 :=
  (muxFastIterFullT16_add 20 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_3).trans
      (muxFastIterBSlideChk_sound dk_w0_4))
private theorem pw_w0_5 : muxFastIterFullT16 30 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_6 :=
  (muxFastIterFullT16_add 25 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_4).trans
      (muxFastIterBSlideChk_sound dk_w0_5))
private theorem pw_w0_6 : muxFastIterFullT16 35 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_7 :=
  (muxFastIterFullT16_add 30 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_5).trans
      (muxFastIterBSlideChk_sound dk_w0_6))
private theorem pw_w0_7 : muxFastIterFullT16 40 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_8 :=
  (muxFastIterFullT16_add 35 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_6).trans
      (muxFastIterBSlideChk_sound dk_w0_7))
private theorem pw_w0_8 : muxFastIterFullT16 45 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_9 :=
  (muxFastIterFullT16_add 40 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_7).trans
      (muxFastIterBSlideChk_sound dk_w0_8))
private theorem pw_w0_9 : muxFastIterFullT16 50 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_10 :=
  (muxFastIterFullT16_add 45 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_8).trans
      (muxFastIterBSlideChk_sound dk_w0_9))
private theorem pw_w0_10 : muxFastIterFullT16 55 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_11 :=
  (muxFastIterFullT16_add 50 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_9).trans
      (muxFastIterBSlideChk_sound dk_w0_10))
private theorem pw_w0_11 : muxFastIterFullT16 60 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_12 :=
  (muxFastIterFullT16_add 55 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_10).trans
      (muxFastIterBSlideChk_sound dk_w0_11))
private theorem pw_w0_12 : muxFastIterFullT16 65 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_13 :=
  (muxFastIterFullT16_add 60 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_11).trans
      (muxFastIterBSlideChk_sound dk_w0_12))
private theorem pw_w0_13 : muxFastIterFullT16 70 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_14 :=
  (muxFastIterFullT16_add 65 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_12).trans
      (muxFastIterBSlideChk_sound dk_w0_13))
private theorem pw_w0_14 : muxFastIterFullT16 75 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_15 :=
  (muxFastIterFullT16_add 70 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_13).trans
      (muxFastIterBSlideChk_sound dk_w0_14))
private theorem pw_w0_15 : muxFastIterFullT16 80 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_16 :=
  (muxFastIterFullT16_add 75 5 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_14).trans
      (muxFastIterBSlideChk_sound dk_w0_15))
private theorem pw_w0_16 : muxFastIterFullT16 83 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = pvm_w0_17 :=
  (muxFastIterFullT16_add 80 3 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 3 513 phbv_w0) pw_w0_15).trans
      (muxFastIterBSlideChk_sound dk_w0_16))
private theorem pw_w0_17 : muxFastIterFullT16 86 513
    phbv_w0 rkmViHi_m1024_r512_s1_c1 = rkmVoHi_m1024_r512_s1_c1 :=
  (muxFastIterFullT16_add 83 3 513 phbv_w0 rkmViHi_m1024_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 3 513 phbv_w0) pw_w0_16).trans
      (muxFastIterBSlideChk_sound dk_w0_17))
/-- Certified `T_16` walk chunk `m1024_r512_s1_c1`. -/
theorem rkmWalkChkHi_m1024_r512_s1_c1 : muxFastIterFullT16 86 513
    rkmHbHi_m1024_r512_s1_c1 rkmViHi_m1024_r512_s1_c1 = rkmVoHi_m1024_r512_s1_c1 :=
  (congrArg (fun h ↦ muxFastIterFullT16 86 513 h rkmViHi_m1024_r512_s1_c1)
    (muxIntListEq_eq_true.mp dkhb_w0)).trans pw_w0_17
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi1024T7`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi1024T7 :
    rkmWalkChkHi_m1024_r512_s1_c1 = rkmWalkChkHi_m1024_r512_s1_c1 :=
  rfl
private theorem laneRoot_Hi1024T7 : rkmHbHi_m1024_r512_s1_c1 = rkmHbHi_m1024_r512_s1_c1 :=
  (And.intro (Eq.refl rkmHbHi_m1024_r512_s1_c0) rfl).right
end
end QuantumComputation.Specs.DickeSol
