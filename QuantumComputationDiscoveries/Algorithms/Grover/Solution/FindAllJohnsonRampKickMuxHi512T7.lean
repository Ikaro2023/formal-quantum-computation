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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T6

/-
# High-`m` Checkpointed Walk Part `7` (`FindAllJohnsonRampKickMuxHi512T7`)

Certifies `2` `T_16` checkpoint walk(s) (`37449` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Zigzag `< 2 ^ 60` `ℕ → ℤ` list decoder (`FindAllJohnsonRampKickMuxHi512T7`). -/
def rkmZigHi512T7 : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: rkmZigHi512T7 ws
/-- Gap-encoded sign-flip helper (`FindAllJohnsonRampKickMuxHi512T7`). -/
def rkmFlipGapsHi512T7 : List ℕ → List ℤ → List ℤ
  | [], vs => vs
  | _, [] => []
  | 0 :: gs, v :: vs => muxRawIntNeg v :: rkmFlipGapsHi512T7 gs vs
  | (g + 1) :: gs, v :: vs => v :: rkmFlipGapsHi512T7 (g :: gs) vs
/-- Quantized generator list for `m512_r512_s2_c1`. -/
def rkmHbHi_m512_r512_s2_c1 : List ℤ := altBuildHbFrom 1024 512 51800528925 0 512
/-- Input orbital vector for `m512_r512_s2_c1`. -/
def rkmViHi_m512_r512_s2_c1 : List ℤ := rkmZigHi512T7
  [3307292913,1103447101,1207360306,946570383,3544198449,88376542,2101981352,1275574441,1911458612,
   457972270,2612097615,2421385274,965494623,1997625919,247483169,4010316054,789811606,2814772037,
   3390709671,3427157620,1248472208,1745302199,1399426372,346134727,1313702109,720651974,738590871,
   813998688,1350836098,3489026439,2770813052,712198390,668008310,3682498221,2421895283,4199603690,
   1275620976,2869362782,4569031307,2617628585,1830162206,2013166556,883514523,1564260573,
   2008323360,1994556212,996414545,3258800653,131407883,700360856,3015014812,853828551,3796118549,
   2999059844,4782019428,4750716781,3033621611,553286424,1934855258,310599202,1169636776,1657876816,
   1374694019,4971219967,2800408562,1412419804,525142869,634455966,1597165203,1169617665,2947163658,
   195294352,258063039,1457304346,1469388003,2346204737,2489821863,1588457804,390823060,1777369062,
   3363810082,699839568,895269690,1676115125,1710154125,4145090053,4324766501,608722424,2007161346,
   5422969830,814348392,841582480,2716350125,823511292,2569632112,223647591,2967090110,1273921663,
   967293068,2181955513,1410300507,4605273927,2019533019,5070461535,4765132419,3544534181,
   4920277383,1405812322,2522975345,6443552552,372953712,7054089310,9081920432,11730706006,
   16157485796,3935912178,14158658506,664226874,17823662510,3225442935,24785280302,15698707145,
   21536615174,17514182699,15953163518,5806950299,16542205796,12919576402,14424820960,24004566834,
   4841097620,16396699680,14904531341,1299319496,9524532273,6492145737,13149886576,11905161037,
   10023979644,1763741171,3481119199,7390216020,11950930733,10031296274,3028384296,1717681214,
   13943617804,9371131331,4136359278,365064312,10249206897,11625926846,4150291731,2334482139,
   5632192656,14602820425,1963984142,284604705,12090842825,9947676284,7387282651,11135284847,
   16042963776,3671949597,2710242485,13518349990,10626532829,972998260,14402407720,15929368079,
   6722556687,5285195866,15691529643,2163028386,11850565260,15811244259,4256823101,9451128302,
   9297619655,427788562,12016536412,4288150405,959905978,8658932826,6084571029,2802018947,
   3923289504,7080956369,3161096187,206639047,14555635151,7048554619,4099856082,11446957687,
   7373294407,12652344484,1670575445,8877642063,18850324518,16541515940,10514852565,1710107995,
   7369988258,14347187363,10914918489,13408802536,1673294328,12462055861,8618835644,12675061508,
   11449408227,5969380547,12844020558,616850977,12057871217,8236517898,10006855232,9668592527,
   4046637317,16617933730,3344979042,10824563851,3808999108,12257428536,7620137939,10795081385,
   9122185352,7733394444,8229815243,2596561529,12801926876,1720250198,11776692185,181775188,
   10367252440,218108821,5955881913,9132607672,12026320664,5724067483,8798936881,7001296222,
   10850947186,4560340849,8560480207,3161623270,955396778,10971331843,5935162637,11061008060,
   9731244948,9453643819,9946686947,9409139160,12316749240,6078445249,13910426617,2960311990,
   14894086570,386139104,12938659725,1533507473,13900825958,7067400272,12236148239,12544702351,
   6594530042,13529589756,1165908576,5904165811,4501561284,15424263504,7203606206,9404076447,
   8618371783,6160064478,10369903464,1087982307,9790848333,1724682463,10901886248,6033724512,
   10548839371,11912780523,7349534170,22852133368,12196615278,15822705205,27520680671,7041375207,
   20483892008,22364415832,2098712015,24671889497,20371461393,4520685494,19382867786,7995409594,
   13009066233,18312100361,2157386811,18074952420,19966191060,1158843608,16912380253,15126754877,
   2701421118,17705161880,14973298650,3591751077,19853223935,17690930353,631050199,14116194638,
   14188000524,788277446,13567634701,14581248379,151511975,16396361356,20284923138,8397313292,
   10804522119,23499249405,18901099023,1119931772,21944053022,28766869772,17091561238,7112328367,
   30999653331,40273005087,28528313831,2358582125,24611385804,40468784582,38432701990,18645035022,
   10211034991,35122093145,46849336027,42886276085,25181564059,657986882,25565453770,41180355876,
   44278355204,35792048988,17800345504,6203969497,30597244257,50419875087,64056446265,71690446955,
   72953502471,67901767739,58452355057,46451647647,30976331001,8698334117,24899477672,77553768986,
   164224763456,309301580226,547827634800,929631403484,1526442736140,2438230041448,3797389785584,
   5773271712692,8577993200736,12470166375618,17752982153932,24766871096328,33878448329342,
   45464799216002,59890348781944,77476077038670,98464577362322,122984939272350,151019401834902,
   182373286609706,216651972527458,253250372593214,291358827172140,329985956417816,367996972750160,
   404165899341164,437239904958182,466011930614660,489395074754590,506491146621484,516647100181678,
   519495280857628,514974929682196,503333151216596,485104719140018,461072339640862,432211629150372,
   399626781755094,364483073681360,327941461062574,291099487201304,254941970436294,220304242126154,
   187849596069896,158061028350704,131245712989184,107549523444852,86978527600810,69424596943760,
   54692717687502,42527998709602,32640689192650,24727853472714,18490801701766,13647930751196,
   9943176153900,7150680873220,5076481328660,3558014309622,2462136582174,1682204831376,
   1134639147498,755301917802,495954291704,320987983304,204562889876,128213358684,78926335278,
   47650912928,28174207724,16291098236,9200045044,5068087922,2720508382,1421744786,722882470,
   357454314,171902526,80444748,36682966,16341314,7141132,3080260,1322404,570648,249892,111780,
   51124,23784,11150,5206,2386,1064,456,180,64,16,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Output orbital vector for `m512_r512_s2_c1`. -/
def rkmVoHi_m512_r512_s2_c1 : List ℤ := rkmZigHi512T7
  [406600317,1820562170,1780420307,941021615,372793888,1118338768,1176013022,3303552743,3567062509,
   3799619495,735425490,315444738,2782268483,3761275312,1731643837,2453619841,2479101544,501783712,
   350633279,3493178371,3363955491,1035233345,2556418810,619914080,251159767,1563654035,1088590619,
   2069966583,2825802496,3044078722,1526370164,984701911,1046721649,2236015253,389874418,450716482,
   2421031895,1188814134,2144559024,134585981,37832076,2544293330,2157286281,3498426577,491955164,
   737021024,3221694488,779304206,4167619201,222187010,913830839,1543567452,1807286220,3239193420,
   2074261,8880500617,645211893,2611575126,5828996160,1851134079,2314456633,1223629922,157174719,
   2697912506,2866879249,552313681,3712791995,2320677828,2996164330,1834483819,6339410702,
   10612945545,12773672946,15275487955,14020300006,15963812803,18421834572,16467836575,12653457316,
   11058825805,6505751788,2481146530,5289181139,11187741752,14919196789,9037032182,7882426505,
   1323226362,5338696260,4668533107,9050926626,7958187297,4718724374,3367811715,3558238935,
   7815794280,10141337455,8949476432,660536593,6558815613,10368883508,10413453391,2890354090,
   5411011144,7311732613,10108750242,6519744863,4911246721,9055917892,8870670553,3358015602,
   3679648188,7624111285,7486959750,1716222339,266021007,9287836668,9180907223,743476989,1887951714,
   12551518709,6533368408,4403432564,6587343431,11802923192,1578540564,5784207723,8419610292,
   7536002115,6804144415,8961389592,7144554969,1662776497,9062319056,10838074325,443350099,
   11466715432,9108819901,1113108340,10165522064,11594701473,781082206,12702867578,8392876541,
   2392440750,13842000556,10941526639,5792773111,10381060820,6635607099,4037642099,8013120834,
   11334574617,11345597229,5304889632,8394436977,12025882765,6529867978,998462957,5183007301,
   12411012234,8512663680,4799011269,7879413898,10317076614,4737572170,14624258594,19178211856,
   8331748190,11439614000,8630662094,6551914987,3894144843,3072360186,3472724523,3283824288,
   20391384850,13353704024,10974606168,23867143090,11645914062,7631633413,6164740166,16950941002,
   2345448105,2261237369,11853329682,4204290407,14684928171,7001198450,9814861138,14245841667,
   6617995689,16324451760,3160415168,8933981239,7674379974,9051563506,8830870251,1593650629,
   15251866586,1160572070,10196856447,5764700870,6982999604,9119515741,3215968623,10652263972,
   2634745893,16352856805,1261936637,5170432070,11388720139,8503885559,11432245648,8056027160,
   7886154813,1881737443,9319818024,1580137941,8006168047,6678004644,7142622092,11353907905,
   11212461403,5602713292,3831519498,11783549993,8181939465,5404433172,462710301,8763187831,
   2965328408,11008323166,812658687,7585252799,3647884746,9004885610,2192793061,4842050949,
   6832941336,3985028684,13816011027,16082435501,3870574701,3237168347,11490407781,5141930073,
   10914008120,9582735722,4582154253,2622350803,9817463254,5151346702,8925893585,6216470831,
   6772832312,4754964244,8411562063,6350454187,8902736120,8208619558,7649238839,7976644145,
   7780370166,8987024430,8294723303,13638470473,4808278340,18476432102,5358888984,11777953209,
   5010670157,10501430434,7099467682,6500387325,5222128709,7865810972,9128405908,4755007079,
   10416208147,2657777002,12439964586,2086353060,10607717557,5019269519,8243137342,8035354042,
   3059198475,5076079179,6712715770,13307034612,2578623238,9002198315,3209742391,8675142804,
   5166485816,9624379091,12908234615,1702395340,14164620692,6054524244,11574820735,12374254213,
   5342051020,14617172466,1024687506,15281945947,9365846627,13035225964,22380939304,3606029462,
   22088309985,22066155237,4540949002,24434822836,13959636914,11704197959,20476727843,2517171515,
   20562771326,22174904536,1839194712,14923865167,9113164385,8612989608,14423902020,2155341468,
   11937086923,10635758891,4967186986,17008517204,10761569450,7392039841,16426754255,5963663115,
   11779429800,17452141510,5608018398,11696050685,17722915107,6959746381,8971963632,12785630698,
   504632214,14267148731,16043700159,3258908977,12177974664,16692029592,6283693186,9668580531,
   15784536659,5447466455,11834665366,19772450362,10783458534,8523430207,23774243439,23054437235,
   5278523299,17533509352,28300084530,18720774256,4177637835,24609241789,29519493731,15547747581,
   9798330600,31618697412,36100394324,19955344942,7477634319,31396865257,40467653685,31016411005,
   7357217375,19664735446,37187382860,37329627508,21254158270,3168269799,26544536169,41073197345,
   41805316929,28381531207,5992455339,17102204238,33995640382,41259896276,37966777922,24740150404,
   4358476754,18288982471,38416837819,53565955861,63319338721,67587762305,66298287109,60672328597,
   53647170317,48378570967,46630314443,48534521099,52126406563,49732248977,20363413771,80563786160,
   333556604306,870664158990,1895071245330,3702075057824,6696075960862,11398201807426,
   18440629048486,28544166205634,42475356407578,60980692901438,84699923080806,114066236789004,
   149205520217808,189848531265538,235269634834654,284264581945162,335177234797154,385979917016690,
   434404186654780,478110205637822,514876142295774,542785778700302,560392683554184,566842159207342,
   561937111037230,546140797192208,520517576606622,486620989496690,446345022859894,401757863914352,
   354937478635912,307825612439610,262112387153210,219158555632170,179957360473020,145133314246984,
   114971519391548,89468780591456,68396956452510,51369664186266,37905196079860,27480772798710,
   19575522168568,13701479243278,9423302417198,6368291029020,4228747636470,2758846448958,
   1768036172798,1112701614582,687411177010,416658797008,247627828684,144199127676,82211081700,
   45850671142,24994626188,13306918910,6913513036,3502639316,1729352702,831603674,389304418,
   177355960,78611080,33897232,14220716,5805982,2308044,894038,337798,124646,44974,15878,5482,1840,
   592,176,44,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Quantized generator list for `m512_r512_s3_c0`. -/
def rkmHbHi_m512_r512_s3_c0 : List ℤ := altBuildHbFrom 1024 512 51812710743 0 512
/-- Input orbital vector for `m512_r512_s3_c0`. -/
def rkmViHi_m512_r512_s3_c0 : List ℤ := rkmFlipGapsHi512T7
  [1,3,0,3,1,3,0,0,3,5,3,0,3,0,3,0,0,0,0,0,1,0,3,4,0,0,0,0,3,0,0,1,1,0,1,1,1,1,1,1,0,0,1,1,1,1,3,1,
   1,1,1,1,0,1,2,1,1,2,2,1,0,1,0,1,0,1,1,2,1,0,2,1,1,0,1,0,1,1,0,1,7,0,1,6,2,0,1,1,0,2,0,0,2,0,2,4,
   4,0,1,3,0,1,2,0,0,0,1,1,2,1,2,0,4,0,2,1,0,2,0,0,0,0,0,2,0,5,1,0,2,0,2,0,1,0,2,0,1,0,1,4,2,1,0,0,
   0,0,2,7,3,0,2,2,2,0,1,0,0,1,0,0,0,0,0,0,1,0,0,0,0,1,0,1,0,4,1,0,0,0,0,0,2,0,0,1,3,3,0,0,0,0,6,0,
   9,44,0,0,0,0,0,0,0,0,12,0,0,0,0,0,0]
  rkmVoHi_m512_r512_s2_c1
/-- Output orbital vector for `m512_r512_s3_c0`. -/
def rkmVoHi_m512_r512_s3_c0 : List ℤ := rkmZigHi512T7
  [985425646,695952168,881645983,371671182,382340072,147770668,1221412685,1720631188,822056176,
   584974329,1786983027,763339414,919115631,952564533,2429161237,1048504660,2560511771,1283189561,
   619482697,2690950780,2049623217,825708123,498113690,282008801,1271962680,2480356013,1459326002,
   4554298655,3985615293,5754422793,3204785157,333816924,506906403,1801166662,832833059,2848116208,
   896755975,3018515968,3403360585,750227764,2097577283,3741584960,1502392777,1364269359,2450930980,
   5775088351,3688204197,325728727,1424041257,545106377,150187677,3918432395,1132927672,1474058648,
   5770410353,684124827,1970491712,3711064521,1360594109,465373176,3541399945,1011730436,2024016120,
   1203598331,12080406,702115482,4592174352,3871949346,1855063673,4984774477,753990912,366417178,
   2251442421,1848700985,127544809,1895144013,2912100184,2216838853,6860911928,4453125970,
   3467921186,3504586431,4847441415,3380302817,1066436283,737612844,459724381,1651067269,3258202484,
   4743300694,626404266,5428343381,2069439617,4732604843,937689993,7943397760,419874521,3014829666,
   1954557217,4604728161,1538926310,2332457034,9255689190,4408651934,1121885988,698610606,
   13709596059,11602779023,2863317397,6840560737,492153927,8040917528,10348967210,8623482078,
   11081666248,5726406832,9560124262,703084241,4107804387,10733283467,20605248439,15709443159,
   10860826389,10422076195,17671683253,2656110297,11490837368,3353088891,6306173288,13515992938,
   3739512698,16509266874,7072550520,3411648872,14530010267,15364940907,9492524723,2319269799,
   59435955,404993095,11116757698,11051575148,4036279218,1295944015,1995188925,12751919813,
   1142626753,6171538377,742972877,3967138590,10275392990,2504283169,8089909410,6910618061,
   4112544004,6430890901,4932237796,1363805785,6100425365,4056681713,3904892642,15739085447,
   3296397547,8505650729,15924009323,2857427035,7921342176,5710145617,104685283,3673851474,
   1022856698,2782876078,3469636362,12814702530,2836254248,7110658506,10414410876,9443744354,
   3086042769,912326409,7800576042,13096538030,10491424190,11066155256,9596620904,8700979920,
   1795864850,2787841476,7986418706,322286762,3001793992,3415493311,2827424541,8545247711,
   9453381997,11943617671,10424406337,9908189747,2558997695,19778602495,13031821835,11650976658,
   3713894055,6032737650,15004424830,12462146732,15184859114,8078637882,1509041510,398457243,
   4573417293,6852929113,7856951533,9046385739,7079344645,4034903270,10503462202,9529559508,
   12787789472,13620116604,1781259898,7021023844,471416152,9813811692,4019679544,470086186,
   11488769000,12540327758,13655027372,15178667960,4385868974,12487599558,7632456454,18174918014,
   18287214066,12478392202,18120677634,3407353790,9395576198,774197444,8568089003,17343432983,
   6081216011,11697767469,2522525741,3814170345,2182812085,9226974169,410232651,1293039914,
   4478042460,15949334560,27981516928,2562025834,13815683330,4620997485,10770299343,11123013423,
   6692180477,9207277278,9597401328,1375869701,9684655761,9173627829,1009598975,35407286,
   12296982884,8646863006,2149470030,10884953774,7215612723,2307001953,1065127645,4054847,
   3455065103,3135951227,7667169963,3145450042,3378819552,98993404,1704844562,7860427947,226100822,
   6177430656,4286604906,8102525724,3283239412,2113093555,12661849470,4564829763,4443051725,
   29946207721,10473365031,8707034759,5654051367,7095981378,6050100142,2716946451,8313585330,
   10576935628,660589900,3735425557,4407137477,9638219459,2066071101,11770079781,6248053680,
   6525228384,10012073558,6402611951,4098095903,27931865031,1722865231,19341021659,5336868612,
   6173022605,9650691295,5298345269,22163469016,8917790174,17014324357,5532570385,5439968478,
   13179003850,10081121667,4717336065,23205955677,1161204987,22681420237,5804937293,9744537975,
   15089595850,18257987814,11791667561,11031423285,6993325351,29657799720,18255684816,4715522770,
   9750230531,42831113019,11865184592,10208557678,11917054938,7008414912,6159118001,6104217187,
   6987051741,9993810596,29363791755,20306079862,4560239642,2654567763,1341218834,10487206362,
   9867380938,11807941115,10609373474,3052351342,1108047795,1524767304,4881352456,24356767155,
   18514023037,20976375814,6764245277,89439025466,27371937327,8290356717,13970599187,45228067294,
   5835401865,6192777191,10975293269,14430210092,43417006306,39884537687,27709434180,17851023020,
   51346408369,28504595580,4227405957,37449049645,30095656452,4291991716,15304225857,8632513700,
   8567749625,2503190489,9989777028,3271396624,10958250054,15146635095,40182045631,6438228932,
   33006872020,6349369450,4426289258,12662392367,60627879155,17858281651,81431184356,58903943462,
   42918426805,40028110779,43521593150,46138708334,14273041155,48454210097,3111542910,15947110835,
   62567718310,77415398265,167808496126,258229498289,443674540530,609363525959,1013940458258,
   1342942516697,1729874045078,2199892492023,2423038469450,2379049442883,2021693560748,
   1229131210541,8131306060,1098709159516,1926496311383,2027423727948,1140060524155,292511164791,
   1608054057448,2078590908231,1161561102580,506205416328,1870896547663,1719734464252,110064031335,
   1648892596507,1827553312022,253462917743,2098313912873,1094554394504,663737952581,3431162218393,
   261930851148,2459845933176,3517254327368,14157787818724,31936764308258,52108720050786,
   83362291844362,130333764901578,185119076231746,244900708229440,314741066129340,391368384797956,
   462789206112260,523143400977020,574300981414884,614084301773494,633959946562592,629436328555976,
   605440615416146,569349841801742,523322281669558,466083432952320,399637922042246,331192198338702,
   268627810875202,215575377521478,170927100474424,131897609873360,96945797039204,66443584635590,
   41607374777244,23211010664614,11009530114914,3896767134130,391105765010,914695998239,
   1098917943431,850193021627,529749572549,279915737601,125771758743,46040190275,11417904879,
   525430438,3030290472,2516176936,1519141238,774395518,349388678,142191676,52578444,17677720,
   5381466,1469176,353350,72290,11560,1030,141,91,17,0,0,0,0,0,0,0]
end
public section
private abbrev bZ : ℕ := 2000000000000000
private theorem hbZ0 : Nat.ble bZ 0 = false := rfl
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by
  rw [Nat.add_eq]
  exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem hzMul0 (z : ℕ) : Nat.mul 0 z = 0 := by
  rw [Nat.mul_eq]
  omega
private def uC (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x, xs with
  | 0, _ => xs
  | v + 1, [] => [v]
  | v + 1, h :: t => v :: h :: t
private theorem uC_eq (x : ℕ) (l : List ℕ) : uC x l = x :: l := by
  unfold uC
  rw [n1a]
  cases l <;> rfl
private def uOh : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOh ns
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
  | Int.ofNat v => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t
private theorem bCZ_eq (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem bOfF (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  unfold primOfNatForced
  rw [n1a]
private theorem bNsF (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  unfold primNegSuccForced
  rw [n1a]
private theorem bSubF (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat
  rw [bOfF, Nat.sub_eq]
  cases h : z - u with
  | zero =>
    dsimp only
    rw [Nat.sub_eq, Int.ofNat_eq_natCast]
    omega
  | succ k =>
    dsimp only
    rw [Int.negSucc_eq]
    omega
private def bDc (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bCZ (rkmForcedSubNatNat u z) (bDc z us)
private theorem bDc0 (z : ℕ) : bDc z [] = [] := rfl
private theorem bDcS (z u : ℕ) (us : List ℕ) :
    bDc z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDc z us := by
  rw [bDc, bCZ_eq, bSubF]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]
  omega
private theorem bM0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZ0]
  rfl
private def bNL : List ℕ → ℕ
  | [] => 0
  | _ :: us => Nat.add (bNL us) 1
private theorem bNL_eq (z : ℕ) : ∀ (us : List ℕ), bNL us = altIntLen (bDc z us)
  | [] => rfl
  | _ :: us => by
    dsimp only [bNL]
    rw [bDcS]
    dsimp only [altIntLen]
    rw [bNL_eq z us]
private def zTd (x : ℤ) (d : ℕ) : ℤ := match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.ofNat_eq_natCast]
    omega
  | k + 1 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.negSucc_eq]
    omega
private theorem bTdN : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTd x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => by
    dsimp only [muxRawIntTdivNat, zTd]
    rw [bNeg, ndiv, Nat.add_eq]
private theorem bSTdN (m n d : ℕ) : rkmUltraSubNatTdiv m n d = zTd ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, ndiv, Nat.add_eq]
  cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by
      rw [Int.ofNat_eq_natCast]
      omega
    rw [hm]
    rfl
  | succ k =>
    dsimp only
    have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by
      rw [Int.negSucc_eq]
      omega
    rw [hm]
    dsimp only [zTd]
    rw [bNeg]
private theorem bSTd (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTd (a - b) d := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact bSTdN m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]
        omega
      dsimp only [rkmUltraSubTdiv]
      rw [hm]
      dsimp only [zTd]
      rw [ndiv, Nat.add_eq, Nat.add_eq]
  | negSucc m =>
    cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
        omega
      dsimp only [rkmUltraSubTdiv]
      rw [hm]
      dsimp only [zTd]
      rw [bNeg, ndiv, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]
      rw [bSTdN, Nat.add_eq, Nat.add_eq]
      refine congrArg (fun t => zTd t d) ?_
      simp only [Int.negSucc_eq]
      omega
private theorem bMul (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a with
  | ofNat _ =>
    cases b with
    | ofNat _ =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
      push_cast
      ring
    | negSucc _ =>
      dsimp only [muxRawIntMul]
      simp only [bNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
  | negSucc _ =>
    cases b with
    | ofNat _ =>
      dsimp only [muxRawIntMul]
      simp only [bNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
    | negSucc _ =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
private theorem bFAdd (a b : ℤ) : rkmForcedIntAdd a b = a + b := by
  cases a with
  | ofNat _ =>
    cases b with
    | ofNat _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bOfF, Nat.add_eq, Int.ofNat_eq_natCast]
      omega
    | negSucc _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bSubF, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
  | negSucc _ =>
    cases b with
    | ofNat _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bSubF, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
    | negSucc _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bNsF, Nat.add_eq, Int.negSucc_eq]
      omega
private theorem bAC (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons
  rw [bFAdd]
  cases a + b <;> cases xs <;> rfl
private def bSV (v P Q d : ℕ) : ℕ := match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bSV_eq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  unfold bSV at hv ⊢
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢
  revert hv
  cases h : Q - P with
  | zero =>
    intro _
    have hm : (P : ℤ) - (Q : ℤ) = Int.ofNat (P - Q) := by
      rw [Int.ofNat_eq_natCast]
      omega
    rw [hm]
    dsimp only [zTd]
    rw [Int.ofNat_eq_natCast]
    push_cast
    ring
  | succ k =>
    intro hv
    have hm : (P : ℤ) - (Q : ℤ) = Int.negSucc k := by
      rw [Int.negSucc_eq]
      omega
    rw [hm]
    dsimp only [zTd] at hv ⊢
    omega
private theorem bSV_same (z P d : ℕ) : bSV z P P d = z := by
  unfold bSV
  simp only [Nat.sub_eq, Nat.add_eq, ndiv, Nat.sub_self, Nat.zero_div, Nat.add_zero]
private theorem bSV_comm (z A B d : ℕ) : bSV z (Nat.add A B) (Nat.add B A) d = z := by
  have hc : Nat.add B A = Nat.add A B := by
    simp only [Nat.add_eq]
    omega
  rw [hc]
  exact bSV_same z (Nat.add A B) d
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bSV v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bChb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bDc z rest = tailZ) :
    bDc z (uC (bCV z d b0 c0 b v c1) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ)) (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0)
        ((c0 : ℤ) - (z : ℤ))) (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uC_eq, bDcS, ht, bAC, bSTd, bMul, bMul]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
  unfold bCV at hv ⊢
  rw [bSV_eq z v _ _ d hv, hpq]
private theorem bC0 (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDc z rest = tailZ) :
    bDc z (uC (bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uC_eq, bDcS, ht, bAC, bTdN, bMul]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [bSV_eq z v _ _ d hv, hpq]
private def bAP : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAP xs)
private theorem apC {x : ℕ} {xs : List ℕ} (h : bAP (uC x xs) = true) :
    0 < x ∧ bAP xs = true := by
  rw [uC_eq] at h
  cases x with
  | zero => exact Bool.noConfusion h
  | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHO (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem hoEq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHO z cs : ℤ) - (z : ℤ)) = (match bDc z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by
    unfold bHO
    rw [bDc0, bZ0]
  | _ :: _ => by
    unfold bHO
    rw [bDcS]
private theorem tnEq (z : ℕ) : ∀ (xs : List ℕ),
    bDc z (bTN xs) = (match bDc z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | _ :: _ => by
    unfold bTN
    rw [bDcS]
private def rPad (z : ℕ) : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | k + 1, [] => uC z (rPad z k [])
  | k + 1, x :: xs => uC x (rPad z k xs)
private theorem rPad_uC (z r x : ℕ) (xs : List ℕ) :
    rPad z (r + 1) (uC x xs) = uC x (rPad z r xs) := by
  rw [uC_eq]
  rfl
private theorem rPad_hd (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ), bHO z (rPad z k xs) = bHO z xs
  | 0, _ => rfl
  | _ + 1, [] => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
  | _ + 1, _ :: _ => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
private theorem rPad_tl (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ),
    bTN (rPad z k xs) = rPad z (k - 1) (bTN xs)
  | 0, _ => rfl
  | _ + 1, [] => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
  | _ + 1, _ :: _ => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
private theorem rPad_bNL (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ),
    Nat.ble (bNL xs) k = true → bNL (rPad z k xs) = k
  | 0, [], _ => rfl
  | 0, _ :: xs, h => by
    dsimp only [bNL] at h
    rw [Nat.add_eq] at h
    have h1 : bNL xs + 1 ≤ 0 := Nat.le_of_ble_eq_true h
    omega
  | k + 1, [], _ => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bNL]
    rw [rPad_bNL z k [] rfl, Nat.add_eq]
  | k + 1, _ :: xs, h => by
    have hk : Nat.ble (bNL xs) k = true := by
      have h1 := Nat.le_of_ble_eq_true h
      dsimp only [bNL] at h1
      rw [Nat.add_eq] at h1
      exact Nat.ble_eq_true_of_le (by omega)
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bNL]
    rw [rPad_bNL z k xs hk, Nat.add_eq]
private theorem bAP_rPad {z : ℕ} (hz : Nat.ble z 0 = false) :
    ∀ (k : ℕ) (xs : List ℕ), bAP xs = true → bAP (rPad z k xs) = true
  | 0, _, h => h
  | k + 1, [], _ => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bAP]
    rw [hz]
    dsimp only [cond]
    exact bAP_rPad hz k [] rfl
  | k + 1, x :: xs, h => by
    dsimp only [bAP] at h
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bAP]
    revert h
    cases Nat.ble x 0 with
    | true =>
      intro h
      dsimp only [cond] at h
      cases h
    | false =>
      intro h
      dsimp only [cond] at h ⊢
      exact bAP_rPad hz k xs h
private def bEqN (a b : ℕ) : Bool :=
  cond (Nat.ble a b) (Nat.ble b a) false
private theorem bEqN_self (a : ℕ) : bEqN a a = true := by
  have hle : Nat.ble a a = true := Nat.ble_eq_true_of_le (by omega)
  unfold bEqN
  rw [hle]
  rfl
private theorem bEqN_eq (a b : ℕ) (h : bEqN a b = true) : a = b := by
  unfold bEqN at h
  revert h
  cases hab : Nat.ble a b with
  | false =>
    intro h
    dsimp only [cond] at h
    cases h
  | true =>
    cases hba : Nat.ble b a with
    | false =>
      intro h
      dsimp only [cond] at h
      cases h
    | true =>
      intro _
      have h1 := Nat.le_of_ble_eq_true hab
      have h2 := Nat.le_of_ble_eq_true hba
      omega
private def bCT (z x : ℕ) (xs : List ℕ) : List ℕ :=
  match xs with
  | h :: t => x :: h :: t
  | [] => cond (bEqN x z) [] [x]
private def bTrim (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => bCT z x (bTrim z xs)
private theorem bTrim_rPad (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ), bTrim z (rPad z k xs) = bTrim z xs
  | 0, _ => rfl
  | k + 1, [] => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bTrim]
    rw [bTrim_rPad z k []]
    dsimp only [bTrim, bCT]
    rw [bEqN_self z]
    rfl
  | k + 1, x :: xs => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bTrim]
    rw [bTrim_rPad z k xs]
private theorem rPad_bTrim_len (z : ℕ) : ∀ (xs : List ℕ), rPad z (bNL xs) (bTrim z xs) = xs
  | [] => rfl
  | x :: t => by
    have hal : bNL (x :: t) = bNL t + 1 := rfl
    rw [hal]
    dsimp only [bTrim]
    have ih := rPad_bTrim_len z t
    revert ih
    cases bTrim z t with
    | cons _ _ =>
      intro ih
      dsimp only [bCT, rPad]
      rw [uC_eq, ih]
    | nil =>
      intro ih
      dsimp only [bCT]
      cases he : bEqN x z with
      | true =>
        dsimp only [cond, rPad]
        rw [uC_eq, bEqN_eq x z he, ih]
      | false =>
        dsimp only [cond, rPad]
        rw [uC_eq, ih]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, [], vs, cs =>
    uC (bSV (bHO z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d) (bSl z d rem 0 z [] (bTN vs) (bTN cs))
  | rem + 1, b0, c0, b :: bR, vs, cs =>
    uC (bCV z d b0 c0 b (bHO z vs) (bHO z (bTN cs)))
      (bSl z d rem b (bHO z cs) bR (bTN vs) (bTN cs))
private theorem bSl_len (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bNL (bSl z d rem b0 c0 bns vs cs) = rem
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, [], vs, cs => by
    dsimp only [bSl]
    rw [uC_eq]
    dsimp only [bNL]
    rw [bSl_len z d rem 0 z [] (bTN vs) (bTN cs), Nat.add_eq]
  | rem + 1, b0, c0, b :: bR, vs, cs => by
    dsimp only [bSl]
    rw [uC_eq]
    dsimp only [bNL]
    rw [bSl_len z d rem b (bHO z cs) bR (bTN vs) (bTN cs), Nat.add_eq]
private theorem bSl_rPad (z d : ℕ) : ∀ (rem b0 c0 kv kc : ℕ) (bns vs cs : List ℕ),
    bSl z d rem b0 c0 bns (rPad z kv vs) (rPad z kc cs) = bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, kv, kc, [], vs, cs => by
    dsimp only [bSl]
    rw [rPad_hd z kv vs, rPad_tl z kv vs, rPad_tl z kc cs]
    rw [bSl_rPad z d rem 0 z (kv - 1) (kc - 1) [] (bTN vs) (bTN cs)]
  | rem + 1, b0, c0, kv, kc, b :: bR, vs, cs => by
    dsimp only [bSl]
    rw [rPad_hd z kv vs, rPad_tl z kc cs, rPad_hd z (kc - 1) (bTN cs), rPad_hd z kc cs,
      rPad_tl z kv vs]
    rw [bSl_rPad z d rem b (bHO z cs) (kv - 1) (kc - 1) bR (bTN vs) (bTN cs)]
private theorem bSl_zero (z d : ℕ) : ∀ (rem b0 : ℕ) (bns : List ℕ),
    bSl z d rem b0 z bns [] [] = rPad z rem []
  | 0, _, _ => rfl
  | rem + 1, b0, [] => by
    dsimp only [bSl, bHO, bTN, rPad]
    rw [bSV_same z (Nat.mul b0 z) d, bSl_zero z d rem 0 []]
  | rem + 1, b0, b :: bR => by
    dsimp only [bSl, bCV, bHO, bTN, rPad]
    rw [bSV_comm z (Nat.mul b0 z) (Nat.mul b z) d, bSl_zero z d rem b bR]
private theorem bSl_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAP (bSl z d rem b0 c0 bns vs cs) = true → bDc z (bSl z d rem b0 c0 bns vs cs) =
      rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOh bns) (bDc z vs) (bDc z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, [], vs, cs, h => by
    dsimp only [bSl, uOh, rkmUltraSlideLoopAux] at h ⊢
    have hp := apC h
    have hi := bSl_sound z d rem 0 z [] (bTN vs) (bTN cs) hp.2
    rw [bM0, uOh, tnEq z vs, tnEq z cs] at hi
    have hc := bC0 z d b0 c0 (bHO z vs) hp.1 hi
    rw [hoEq z vs] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, [], [], h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDc0]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b z bR [] [] hp.2
    rw [bZ0 z, bDc0] at hi
    have hc := bChb z d b0 c0 b z z hp.1 hi
    rw [bZ0 z] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, [], c :: cT, h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDc0, bDcS z c cT]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b c bR [] cT hp.2
    rw [bDc0] at hi
    have hc := bChb z d b0 c0 b z (bHO z cT) hp.1 hi
    rw [hoEq z cT, bZ0 z] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, v :: vT, [], h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDcS z v vT, bDc0]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b z bR vT [] hp.2
    rw [bZ0 z, bDc0] at hi
    have hc := bChb z d b0 c0 b v z hp.1 hi
    rw [bZ0 z] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, v :: vT, c :: cT, h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDcS z v vT, bDcS z c cT]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b c bR vT cT hp.2
    have hc := bChb z d b0 c0 b v (bHO z cT) hp.1 hi
    rw [hoEq z cT] at hc
    exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uC b (uC (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs => match hbz with
    | [] => match vs, cs with
      | [], [] => uC (bSV z p0 q0 d) []
      | _, _ => uC (bSV (bHO z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTN vs) (bTN cs))
    | [_] => []
    | b :: bz :: bR => match vs, cs with
      | [], [] => uC (bSV z (Nat.add p0 bz) (Nat.add bz q0) d) []
      | v :: vT, c :: cT => uC (bSV v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] => uC (bSV v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT => uC (bSV z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
private theorem bSlZ_rPad (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    rPad z rem (bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs) =
      bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, _, _, bns, vs, cs => by
    cases bns with
    | nil =>
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, bSl_zero z d rem 0 []]
        | cons _ cT =>
          have hrec := bSlZ_rPad z d rem 0 z [] [] cT
          dsimp only [mkHbZ] at hrec
          rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, hrec]
      | cons _ vT =>
        cases cs with
        | nil =>
          have hrec := bSlZ_rPad z d rem 0 z [] vT []
          dsimp only [mkHbZ] at hrec
          rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, hrec]
        | cons _ cT =>
          have hrec := bSlZ_rPad z d rem 0 z [] vT cT
          dsimp only [mkHbZ] at hrec
          rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, hrec]
    | cons b bR =>
      dsimp only [mkHbZ]
      rw [uC_eq, uC_eq]
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSl_zero z d rem b bR]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSlZ_rPad z d rem b c bR [] cT]
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSlZ_rPad z d rem b z bR vT []]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSlZ_rPad z d rem b c bR vT cT]
private def uCN4 (x1 x2 x3 x4 : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x1 with
  | 0 => xs
  | v1 + 1 => match Nat.add 1 x2 with
    | 0 => xs
    | v2 + 1 => match Nat.add 1 x3 with
      | 0 => xs
      | v3 + 1 => match Nat.add 1 x4 with
        | 0 => xs
        | v4 + 1 => match xs with
          | [] => [v1, v2, v3, v4]
          | h :: t => v1 :: v2 :: v3 :: v4 :: h :: t
private theorem uCN4e (x1 x2 x3 x4 : ℕ) (xs : List ℕ) :
    uCN4 x1 x2 x3 x4 xs = uC x1 (uC x2 (uC x3 (uC x4 xs))) := by
  unfold uCN4
  rw [n1a x1, n1a x2, n1a x3, n1a x4, uC_eq, uC_eq, uC_eq, uC_eq]
  cases xs <;> rfl
private def bAP4 : List ℕ → Bool
  | a :: b :: c :: d :: xs => cond (Nat.ble a 0) false (cond (Nat.ble b 0) false
      (cond (Nat.ble c 0) false (cond (Nat.ble d 0) false (bAP4 xs))))
  | xs => bAP xs
private theorem bAP4e : ∀ (xs : List ℕ), bAP4 xs = bAP xs
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: xs => by
    dsimp only [bAP4, bAP]
    rw [bAP4e xs]
private def bChkP (out : List ℕ) : Option (List ℕ) := match out with
  | [] => some []
  | x :: xs => cond (bAP4 (x :: xs)) (some (x :: xs)) none
private theorem bChkPe (out : List ℕ) : bChkP out = cond (bAP out) (some out) none := by
  cases out with
  | nil => rfl
  | cons _ _ =>
    dsimp only [bChkP]
    rw [bAP4e]
private theorem cond_some_eq {α : Type} {b : Bool} {x y : α}
    (h : cond b (some x) none = some y) : b = true ∧ x = y := by
  cases b with
  | false => cases h
  | true =>
    dsimp only [cond] at h
    injection h with h'
    exact ⟨rfl, h'⟩
private inductive HbZ4 : Type
  | tail : List ℕ → HbZ4
  | c4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → HbZ4 → HbZ4
private abbrev hbz4C (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) : List ℕ :=
  b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: t
private def hbz4L : HbZ4 → List ℕ
  | HbZ4.tail l => l
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L r)
private def fH4 {α : Type} (h : HbZ4) (k : HbZ4 → α) : α := match h with
  | HbZ4.tail l => fL l fun lF => k (HbZ4.tail lF)
  | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r => k (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r)
private theorem fH4e {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ =>
    dsimp only [fH4, fL]
    rw [rkmb_forceList_eq]
  | c4 _ _ _ _ _ _ _ _ _ => rfl
private def toH4 : List ℕ → HbZ4
  | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs => match toH4 bs with
    | HbZ4.tail l => HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.tail l)
    | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t =>
      HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t)
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
    have ih := hbz4L_toH4 bs
    dsimp only [toH4]
    revert ih
    cases toH4 bs with
    | tail _ =>
      intro ih
      dsimp only [hbz4L, hbz4C] at ih ⊢
      rw [ih]
    | c4 _ _ _ _ _ _ _ _ _ =>
      intro ih
      dsimp only [hbz4L, hbz4C] at ih ⊢
      rw [ih]
private def bSlZ4 (z d : ℕ) : HbZ4 → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | HbZ4.tail l, rem, p0, q0, vs, cs => bSlZ z d rem p0 q0 l vs cs
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR, rem, p0, q0, vs, cs => match rem with
    | 0 => []
    | r3 + 1 => match r3 with
      | 0 => bSlZ z d 1 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
      | r2 + 1 => match r2 with
        | 0 => bSlZ z d 2 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
        | r1 + 1 => match r1 with
          | 0 => bSlZ z d 3 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
          | r0 + 1 => match vs, cs with
            | [], [] => uC (bSV z (Nat.add p0 z1) (Nat.add z1 q0) d) []
            | v1 :: v2 :: v3 :: v4 :: vR, c1 :: c2 :: c3 :: c4 :: c5 :: cR =>
              uCN4 (bSV v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                (bSV v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                (bSV v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                (bSV v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 c5) z3) d)
                (bSlZ4 z d bR r0 (Nat.mul b4 c4) z4 vR (c5 :: cR))
            | [], c1 :: c2 :: c3 :: c4 :: c5 :: cR =>
              uCN4 (bSV z (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                (bSV z (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                (bSV z (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                (bSV z (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 c5) z3) d)
                (bSlZ4 z d bR r0 (Nat.mul b4 c4) z4 [] (c5 :: cR))
            | _, _ =>
              bSlZ z d ((((r0 + 1) + 1) + 1) + 1) p0 q0
                (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
private theorem bSlZ4_eq (z d : ℕ) : ∀ (hbz : HbZ4) (rem p0 q0 : ℕ) (vs cs : List ℕ),
    bSlZ4 z d hbz rem p0 q0 vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs
  | HbZ4.tail _, _, _, _, _, _ => rfl
  | HbZ4.c4 _ _ _ _ _ _ b4 z4 bR, rem, _, _, vs, cs => by
    match rem with
    | 0 => rfl
    | r3 + 1 => match r3 with
      | 0 => rfl
      | r2 + 1 => match r2 with
        | 0 => rfl
        | r1 + 1 => match r1 with
          | 0 => rfl
          | r0 + 1 => match vs with
            | [] => match cs with
              | [] => rfl
              | [_] => rfl
              | [_, _] => rfl
              | [_, _, _] => rfl
              | [_, _, _, _] => rfl
              | _ :: _ :: _ :: c4 :: c5 :: cR =>
                dsimp only [bSlZ4, hbz4L, hbz4C, bSlZ, bHO]
                rw [uCN4e]
                exact congrArg (fun r => uC _ (uC _ (uC _ (uC _ r))))
                  (bSlZ4_eq z d bR r0 (Nat.mul b4 c4) z4 [] (c5 :: cR))
            | [_] => rfl
            | [_, _] => rfl
            | [_, _, _] => rfl
            | _ :: _ :: _ :: _ :: vR => match cs with
              | [] => rfl
              | [_] => rfl
              | [_, _] => rfl
              | [_, _, _] => rfl
              | [_, _, _, _] => rfl
              | _ :: _ :: _ :: c4 :: c5 :: cR =>
                dsimp only [bSlZ4, hbz4L, hbz4C, bSlZ, bHO]
                rw [uCN4e]
                exact congrArg (fun r => uC _ (uC _ (uC _ (uC _ r))))
                  (bSlZ4_eq z d bR r0 (Nat.mul b4 c4) z4 vR (c5 :: cR))
private def bDg (z dg mL cL : ℕ) (h4 : HbZ4) (vT cT : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlZ4 z d h4 nL 0 0 vT cT) fun raw => bChkP raw
private theorem bDg_rPad {z dg mL cL : ℕ} {b vT cT outT : List ℕ}
    (h : bDg z dg mL cL (toH4 (mkHbZ z b)) vT cT = some outT) :
    bAP outT = true ∧
      rPad z (rkmNextLen mL cL) outT =
        bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b vT cT := by
  unfold bDg at h
  dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq, bChkPe, bSlZ4_eq, hbz4L_toH4] at h
  rcases cond_some_eq h with ⟨hp, rfl⟩
  have hsl := bSlZ_rPad z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b vT cT
  rw [hzMul0 z] at hsl
  exact ⟨hp, hsl⟩
private theorem bDg_sound {z : ℕ} (hz : Nat.ble z 0 = false) (dg mL vL cL : ℕ)
    (b vT cT outT : List ℕ) (h : bDg z dg mL cL (toH4 (mkHbZ z b)) vT cT = some outT) :
    bDc z (rPad z (rkmNextLen mL cL) outT) =
      rkmUltraHornerStage dg mL cL (uOh b) (bDc z (rPad z vL vT)) (bDc z (rPad z cL cT)) := by
  rcases bDg_rPad h with ⟨hp, hsl⟩
  have hpos : bAP (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b
      (rPad z vL vT) (rPad z cL cT)) = true := by
    rw [bSl_rPad, ← hsl]
    exact bAP_rPad hz _ _ hp
  unfold rkmUltraHornerStage
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bM0 z, hsl,
    ← bSl_rPad z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z vL cL b vT cT]
  exact bSl_sound z _ _ 0 z b (rPad z vL vT) (rPad z cL cT) hpos
private def bDg1 (z mL cL : ℕ) (h4 : HbZ4) (vT cT : List ℕ) : Option (List ℕ) :=
  match bDg z 1 mL cL h4 vT cT with
  | none => none
  | some raw => fL (bTrim z raw) fun outT => some outT
private theorem bDg1_sound {z : ℕ} (hz : Nat.ble z 0 = false) (mL vL cL : ℕ)
    (b vT cT outT : List ℕ) (h : bDg1 z mL cL (toH4 (mkHbZ z b)) vT cT = some outT) :
    bDc z (rPad z (rkmNextLen mL cL) outT) =
      rkmUltraHornerStage 1 mL cL (uOh b) (bDc z (rPad z vL vT)) (bDc z (rPad z cL cT)) := by
  unfold bDg1 at h
  revert h
  cases hd : bDg z 1 mL cL (toH4 (mkHbZ z b)) vT cT with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some raw =>
    intro h
    dsimp only [fL] at h
    rw [rkmb_forceList_eq] at h
    injection h with h'
    subst h'
    rcases bDg_rPad hd with ⟨_, hsl⟩
    have hpad := rPad_bTrim_len z (bSl z (Nat.mul 1 wdScale) (rkmNextLen mL cL) 0 z b vT cT)
    rw [bSl_len] at hpad
    rw [← bTrim_rPad z (rkmNextLen mL cL) raw, hsl, hpad, ← hsl]
    exact bDg_sound hz 1 mL vL cL b vT cT raw hd
private def bBdD (z g m c : ℕ) (h4 : HbZ4) (vT xT : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen m c) fun n => match bDg z g m c h4 vT xT with | none => none | some o => k n o
private theorem bBdD_sound {z : ℕ} (hz : Nat.ble z 0 = false) {endL g m vL c : ℕ}
    {b vT xT outT : List ℕ} {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBdD z g m c (toH4 (mkHbZ z b)) vT xT kB = some outT)
    (hk : ∀ m0, kB (rkmNextLen m c) m0 = some outT →
      bDc z (rPad z endL outT) = kU (rkmNextLen m c) (bDc z (rPad z (rkmNextLen m c) m0))) :
    bDc z (rPad z endL outT) =
      (HighDForce.withForcedNat (rkmNextLen m c) fun nL => HighDForce.withForcedList
        (rkmUltraHornerStage g m c (uOh b) (bDc z (rPad z vL vT)) (bDc z (rPad z c xT))) (kU nL)) :=
  by
  unfold bBdD at h
  dsimp only [fN] at h
  rw [rkmb_forceNat_eq] at h
  revert h
  cases hs : bDg z g m c (toH4 (mkHbZ z b)) vT xT with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some mid =>
    intro h
    rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bDg_sound hz g m vL c b vT xT mid hs]
    exact hk mid h
private def bSpD (z m c : ℕ) (h4 : HbZ4) (vT : List ℕ) : Option (List ℕ) :=
  bBdD z 16 m c h4 vT vT fun l x => bBdD z 15 m l h4 vT x fun l x =>
  bBdD z 14 m l h4 vT x fun l x => bBdD z 13 m l h4 vT x fun l x =>
  bBdD z 12 m l h4 vT x fun l x => bBdD z 11 m l h4 vT x fun l x =>
  bBdD z 10 m l h4 vT x fun l x => bBdD z 9 m l h4 vT x fun l x =>
  bBdD z 8 m l h4 vT x fun l x => bBdD z 7 m l h4 vT x fun l x =>
  bBdD z 6 m l h4 vT x fun l x => bBdD z 5 m l h4 vT x fun l x =>
  bBdD z 4 m l h4 vT x fun l x => bBdD z 3 m l h4 vT x fun l x =>
  bBdD z 2 m l h4 vT x fun l x => bDg1 z m l h4 vT x
private theorem bSpD_sound {z : ℕ} (hz : Nat.ble z 0 = false) (mL cL : ℕ) (b vT outT : List ℕ)
    (h : bSpD z mL cL (toH4 (mkHbZ z b)) vT = some outT) :
    bDc z (rPad z (rkmNextLen16 mL cL) outT) =
      rkmUltraHornerT16Step mL cL (uOh b) (bDc z (rPad z cL vT)) := by
  unfold bSpD at h
  unfold rkmUltraHornerT16Step
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  unfold rkmNextLen16
  exact bDg1_sound hz mL cL _ b vT _ outT h
private def bItD (z : ℕ) : ℕ → ℕ → ℕ → HbZ4 → List ℕ → Option (ℕ × List ℕ)
  | 0, _, c, _, vT => some (c, vT)
  | k + 1, m, c, h4, vT => match bSpD z m c h4 vT with
    | none => none
    | some vN => fN (rkmNextLen16 m c) fun nL => bItD z k m nL h4 vN
private theorem bItD_sound {z : ℕ} (hz : Nat.ble z 0 = false) :
    ∀ (k m c : ℕ) (b vT : List ℕ) (endL : ℕ) (outT : List ℕ),
      bItD z k m c (toH4 (mkHbZ z b)) vT = some (endL, outT) →
        bDc z (rPad z endL outT) = muxUltraIterFullT16Rkm k m c (uOh b) (bDc z (rPad z c vT))
  | 0, _, _, _, _, _, _, h => by
    injection h with h'
    injection h' with hc hv
    subst hc
    subst hv
    rfl
  | k + 1, m, c, b, vT, endL, outT, h => by
    unfold bItD at h
    revert h
    cases hs : bSpD z m c (toH4 (mkHbZ z b)) vT with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some vN =>
      intro h
      dsimp only [fN] at h
      rw [rkmb_forceNat_eq] at h
      unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bSpD_sound hz m c b vT vN hs]
      exact bItD_sound hz k m _ b vN endL outT h
private theorem u2f {s m : ℕ} {b u v : List ℤ}
    (h : muxUltraIterFullT16Rkm s m (altIntLen u) b u = v) : muxFastIterFullT16 s m b u = v := by
  have hc : muxUltraIterFullT16HiChk s 0 m b u v = true := by
    unfold muxUltraIterFullT16HiChk
    dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, h]
    exact muxIntListEq_eq_true.mpr rfl
  exact muxUltraIterFullT16HiChk_sound hc
private def pWOk (k m : ℕ) (bns : List ℕ) (l0 : ℕ) (uT : List ℕ) (l1 : ℕ) (vT : List ℕ) : Prop :=
  muxFastIterFullT16 k m (uOh bns) (bDc bZ (rPad bZ l0 uT)) = bDc bZ (rPad bZ l1 vT)
private def bSlChk (s m : ℕ) (bns : List ℕ) (l0 : ℕ) (uT : List ℕ) (l1 : ℕ) (vT : List ℕ) :
    Bool :=
  fL bns fun bF => fL uT fun uF => fL vT fun vF =>
    cond (Nat.ble (bNL uF) l0)
      (fH4 (toH4 (mkHbZ bZ bF)) fun h4 =>
        match bItD bZ s m l0 h4 uF with
        | none => false
        | some (endL, outT) => cond (muxNatListEq [endL] [l1]) (muxNatListEq outT vF) false)
      false
private theorem bSlSnd {s m : ℕ} {bns : List ℕ} {l0 : ℕ} {uT : List ℕ} {l1 : ℕ} {vT : List ℕ}
    (h : bSlChk s m bns l0 uT l1 vT = true) : pWOk s m bns l0 uT l1 vT := by
  unfold bSlChk at h
  unfold pWOk
  dsimp only [fL] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq] at h
  revert h
  cases hle : Nat.ble (bNL uT) l0 with
  | false =>
    intro h
    dsimp only [cond] at h
    exact Bool.noConfusion h
  | true =>
    intro h
    dsimp only [cond] at h
    rw [fH4e] at h
    revert h
    cases hi : bItD bZ s m l0 (toH4 (mkHbZ bZ bns)) uT with
    | none =>
      intro h
      dsimp only at h
      exact Bool.noConfusion h
    | some p =>
      cases p with
      | mk endL outT =>
        intro h
        dsimp only at h
        revert h
        cases he : muxNatListEq [endL] [l1] with
        | false =>
          intro h
          dsimp only [cond] at h
          exact Bool.noConfusion h
        | true =>
          intro h
          dsimp only [cond] at h
          have hl1 : endL = l1 := (List.cons.inj (muxNatListEq_eq_true.mp he)).1
          have hot : outT = vT := muxNatListEq_eq_true.mp h
          have hit := bItD_sound hbZ0 s m l0 bns uT endL outT hi
          rw [hl1, hot] at hit
          have hln : altIntLen (bDc bZ (rPad bZ l0 uT)) = l0 := by
            rw [← bNL_eq bZ]
            exact rPad_bNL bZ l0 uT hle
          refine u2f ?_
          rw [hln]
          exact hit.symm
private theorem bCh (k1 k2 mL : ℕ) {bns : List ℕ} {l0 : ℕ} {v0 : List ℕ}
    {l1 : ℕ} {v1 : List ℕ} {l2 : ℕ} {v2 : List ℕ}
    (h1 : pWOk k1 mL bns l0 v0 l1 v1) (h2 : bSlChk k2 mL bns l1 v1 l2 v2 = true) :
    pWOk (k1 + k2) mL bns l0 v0 l2 v2 :=
  (muxFastIterFullT16_add k1 k2 mL (uOh bns) (bDc bZ (rPad bZ l0 v0))).trans
    ((congrArg (muxFastIterFullT16 k2 mL (uOh bns)) h1).trans (bSlSnd h2))
private theorem bLift {n m : ℕ} {hb1 hb2 vi1 vi2 vo1 vo2 : List ℤ}
    (hw : muxFastIterFullT16 n m hb1 vi1 = vo1)
    (hhb : muxIntListEq hb1 hb2 = true) (hvi : muxIntListEq vi1 vi2 = true)
    (hvo : muxIntListEq vo1 vo2 = true) : muxFastIterFullT16 n m hb2 vi2 = vo2 := by
  rw [← muxIntListEq_eq_true.mp hhb, ← muxIntListEq_eq_true.mp hvi,
    ← muxIntListEq_eq_true.mp hvo]
  exact hw
private theorem bH {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) : b = true :=
  (rkmAllTrueF_cons h).1
private theorem bT {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: pCat xs ys
private def phbn_w0_p0 : List ℕ := [75015178796886,105932068986458,129549384284695,
  149370882823192,166755871378897,182402542140961,196726269864765,209998092050067,222406546683888,
  234089106289745,245149701388316,255669191786329,265711973189560,275330331951820,284567420863633,
  293459355053143,302036726650011,310325723954358,318348974514307,326126191104105,333674674190525,
  341009708057749,348144876888317,355092319738230,361862938264194,368466567491559,374912117362988,
  381207690961284,387360683943777,393377868717528,399265466126451,405029206845317,410674384233476,
  416205900058661,421628304233846,426945829499511,432162421816689,437281767102751,442307314834626,
  447242298957375,452089756465421,456852543965936,461533352486367,466134720748747,470659047100812,
  475108600266692,479485529057115,483791871159837,488029561114813,492200437564817,496306249860560,
  500348664089311,504329268587487,508249578990304,512111042865244,515915043970600,519662906175600,
  523355897074500,526995231323411,530582073725477,534117542087288,537602709866967,541038608632252,
  544426230345022]
private def phbn_w0_p1 : List ℕ := [547766529487049,551060425040289,554308802333734,
  557512514767682,560672385425249,563789208580029,566863751107997,569896753811001,572888932658531,
  575840979953884,578753565430266,581627337281953,584462923135139,587260930962764,590021949947214,
  592746551294502,595435289003237,598088700591405,600707307783783,603291617162563,605842120783566,
  608359296760264,610843609817633,613295511817741,615715442258811,618103828749382,620461087459084,
  622787623547407,625083831571795,627350095876242,629586790961553,631794281838287,633972924363398,
  636123065561457,638245043931337,640339189739141,642405825298134,644445265236373,646457816752698,
  648443779861682,650403447628147,652337106391749,654245035982179,656127509925428,657984795641582,
  659817154634566,661624842674228,663408109971153,665167201344543,666902356383506,668613809602073,
  670301790588224,671966524147220,673608230439490,675227125113342,676823419432718,678397320400219,
  679949030875629,681478749690115,682986671756306,684472988174438,685937886334719,687381550016091,
  688804159481536]
private def phbn_w0_p2 : List ℕ := [690205891570075,691586919785597,692947414382652,
  694287542449333,695607467987372,696907351989546,698187352514528,699447624759260,700688321128968,
  701909591304894,703111582309851,704294438571668,705458301984630,706603311968961,707729605528453,
  708837317306288,709926579639140,710997522609603,712050274097023,713084959826780,714101703418086,
  715100626430349,716081848408148,717045486924884,717991657625141,718920474265801,719832048755971,
  720726491195749,721603909913875,722464411504305,723308100861742,724135081216165,724945454166383,
  725739319712649,726516776288369,727277920790926,728022848611663,728751653665035,729464428416970,
  730161263912455,730842249802384,731507474369677,732157024554696,732790985979996,733409442974402,
  734012478596465,734600174657290,735172611742768,735729869235227,736272025334524,736799157078583,
  737311340363408,737808649962578,738291159546243,738758941699632,739212067941097,739650608739685,
  740074633532279,740484210740297,740879407785971,741260291108221,741626926178126,741979377514011,
  742317708696155]
private def phbn_w0_p3 : List ℕ := [742641982381136,742952260315814,743248603350966,
  743531071454594,743799723724884,744054618402863,744295812884729,744523363733884,744737326692667,
  744937756693794,745124707871520,745298233572523,745458386366518,745605218056609,745738779689381,
  745859121564750,745966293245560,746060343566939,746141320645435,746209271887906,746264244000199,
  746306282995608,746335434203111,746351742275413,746355251196766,746346004290605,746324044226979,
  746289413029788,746242152083842,746182302141725,746109903330483,746024995158132,745927616520000,
  745817805704882,745695600401049,745561037702071,745414154112494,745254985553349,745083567367512,
  744899934324905,744704120627544,744496159914451,744276085266403,744043929210550,743799723724884,
  743543500242573,743275289656154,742995122321591,742703028062200,742399036172442,742083175421583,
  741755474057228,741415959808727,741064659890453,740701601004959,740326809346009,739940310601486,
  739542129956185,739132292094479,738710821202872,738277740972431,737833074601101,737376844795912,
  736909073775056]
private def phbn_w0_p4 : List ℕ := [736429783269863,735938994526659,735436728308509,
  734923004896850,734397844093007,733861265219610,733313287121880,732753928168826,732183206254312,
  731601138798028,731007742746341,730403034573041,729787030279975,729159745397572,728521194985254,
  727871393631739,727210355455236,726538094103523,725854622753917,725159954113133,724454100417028,
  723737073430233,723008884445672,722269544283967,721519063292731,720757451345734,719984717841970,
  719200871704591,718405921379731,717599874835209,716782739559107,715954522558235,715115230356462,
  714264868992934,713403444020152,712530960501940,711647423011266,710752835627944,709847201936204,
  708930525022116,708002807470892,707064051364039,706114258276376,705153429272912,704181564905568,
  703198665209763,702204729700846,701199757370370,700183746682219,699156695568574,698118601425711,
  697069461109650,696009270931618,694938026653355,693855723482241,692762356066242,691657918488682,
  690542404262820,689415806326242,688278117035064,687129328157926,685969430869792,684798415745537,
  683616272753329]
private def phbn_w0_p5 : List ℕ := [682422991247781,681218559962893,680002967004759,
  678776199844042,677538245308205,676289089573504,675028718156721,673757115906643,672474266995273,
  671180154908767,669874762438095,668558071669409,667230063974115,665890719998651,664540019653934,
  663177942104506,661804465757330,660419568250259,659023226440149,657615416390610,656196113359389,
  654765291785368,653322925275166,651868986589337,650403447628147,648926279416921,647437452090940,
  645936934879881,644424696091783,642900703096516,641364922308755,639817319170421,638257858132586,
  636686502636821,635103215095965,633507956874295,631900688267088,630281368479534,628649955604995,
  627006406602580,625350677274009,623682722239748,622002494914384,620309947481211,618605030866006,
  616887694709954,615157887341701,613415555748498,611660645546400,609893100949484,608112864738062,
  606319878225824,604514081225895,602695412015755,600863807300962,599019202177665,597161530093819,
  595290722809080,593406710353312,591509420983650,589598781140068,587674715399375,585737146427589,
  583785994930614]
private def phbn_w0_p6 : List ℕ := [581821179603136,579842617075690,577850221859786,
  575843906291031,573823580470158,571789152201852,569740526931297,567677607678323,565600294969057,
  563508486764953,561402078389089,559280962449594,557145028760078,554994164256918,552828252913255,
  550647175649528,548450810240401,546239031217878,544011709770442,541768713637995,539509907002406,
  537235150373435,534944300469787,532637210095058,530313728008294,527973698788877,525616962695441,
  523243355518491,520852708426374,518444847804252,516019595085671,513576766576315,511116173269498,
  508637620652931,506140908506235,503625830688671,501092174916515,498539722529428,495968248245185,
  493377519902024,490767298187868,488137336355573,485487379923342,482817166359323,480126424749391,
  477414875446993,474682229703858,471928189280299,469152446033708,466354681483727,463534566352488,
  460691760078134,457825910299714,454936652311378,452023608483594,449086387648941,446124584449786,
  443137778644929,440125534372019,437087399362242,434022904103476,430931560947712,427812863158150,
  424666283890911]
private def phbn_w0_p7 : List ℕ := [421491275105824,418287266400139,415053663758427,
  411789848211181,408495174393843,405168968997104,401810529098258,398419120362301,394993975100118,
  391534290169670,388039224704370,384507897650973,380939385097092,377332717365963,373686875853220,
  370000789577131,366273331409943,362503313953579,358689485017814,354830522653089,350925029683210,
  346971527674984,342968450272311,338914135810934,334806819116684,330644622374151,326425544933736,
  322147451902279,317808061335069,313404929813864,308935436155258,304396762944434,299785875528751,
  295099498030722,290334085846733,285485793981130,280550440418108,275523463546768,270399872415188,
  265174188279889,259840375513750,254391759404486,248820927669527,243119611562794,237278541154366,
  231287267576709,225133942527082,218805041750598,212285014061887,205555829827778,198596391299915,
  191381749333154,183882042616099,176061028887646,167873998182614,159264717104144,150160789946617,
  140466301418804,130049496361951,118720664779236,106188607949408,91963082489117,75088114190598,
  53095516879568]
private def phbn_w0 : List ℕ := pCat phbn_w0_p0 (pCat phbn_w0_p1 (pCat phbn_w0_p2 (pCat phbn_w0_p3
  (pCat phbn_w0_p4 (pCat phbn_w0_p5 (pCat phbn_w0_p6 phbn_w0_p7))))))
private def phbv_w0 : List ℤ := uOh phbn_w0
private def pvn_w0_0_p0 : List ℕ := [1999998346353543,1999999448276449,2000000603680153,
  1999999526714808,1999998227900775,2000000044188271,2000001050990676,1999999362212779,
  2000000955729306,2000000228986135,1999998693951192,2000001210692637,1999999517252688,
  1999999001187040,1999999876258415,2000002005158027,2000000394905803,1999998592613981,
  1999998304645164,2000001713578810,2000000624236104,1999999127348900,2000000699713186,
  1999999826932636,1999999343148945,2000000360325987,1999999630704564,2000000406999344,
  2000000675418049,1999998255486780,2000001385406526,2000000356099195,2000000334004155,
  1999998158750889,1999998789052358,2000002099801845,2000000637810488,2000001434681391,
  1999997715484346,1999998691185707,2000000915081103,2000001006583278,1999999558242738,
  1999999217869713,2000001004161680,2000000997278106,1999999501792727,1999998370599673,
  1999999934296058,2000000350180428,2000001507507406,1999999573085724,1999998101940725,
  2000001499529922,2000002391009714,1999997624641609,1999998483189194,2000000276643212,
  2000000967427629,2000000155299601,2000000584818388,2000000828938408,1999999312652990,
  1999997514390016]
private def pvn_w0_0_p1 : List ℕ := [2000001400204281,2000000706209902,1999999737428565,
  2000000317227983,1999999201417398,1999999415191167,2000001473581829,2000000097647176,
  1999999870968480,2000000728652173,1999999265305998,1999998826897631,1999998755089068,
  2000000794228902,2000000195411530,2000000888684531,2000001681905041,2000000349919784,
  2000000447634845,1999999161942437,1999999144922937,1999997927454973,1999997837616749,
  2000000304361212,2000001003580673,2000002711484915,2000000407174196,2000000420791240,
  1999998641824937,2000000411755646,2000001284816056,1999999888176204,2000001483545055,
  1999999363039168,2000000483646534,1999998909022243,1999999294849746,1999997697363036,
  1999998990233490,1999997464769232,1999997617433790,1999998227732909,1999997539861308,
  2000000702906161,1999998738512327,2000003221776276,2000000186476856,2000003527044655,
  2000004540960216,2000005865353003,2000008078742898,2000001967956089,2000007079329253,
  2000000332113437,2000008911831255,1999998387278532,2000012392640151,1999992150646427,
  2000010768307587,1999991242908650,2000007976581759,1999997096524850,2000008271102898,
  2000006459788201]
private def pvn_w0_0_p2 : List ℕ := [2000007212410480,2000012002283417,2000002420548810,
  2000008198349840,1999992547734329,2000000649659748,1999995237733863,1999996753927131,
  2000006574943288,1999994047419481,2000005011989822,1999999118129414,1999998259440400,
  2000003695108010,1999994024534633,2000005015648137,2000001514192148,2000000858840607,
  2000006971808902,1999995314434334,2000002068179639,2000000182532156,1999994875396551,
  2000005812963423,1999997924854134,1999998832758930,2000002816096328,1999992698589787,
  2000000981992071,1999999857697647,1999993954578587,2000004973838142,1999996306358674,
  1999994432357576,2000008021481888,1999998164025201,1999998644878757,2000006759174995,
  1999994686733585,2000000486499130,2000007201203860,1999992035315960,1999996638721656,
  2000002642597933,1999992154235178,2000001081514193,2000005925282630,1999992094377870,
  1999997871588449,2000004725564151,1999995351190172,2000000213894281,2000006008268206,
  1999997855924797,2000000479952989,2000004329466413,1999996957714485,1999998598990526,
  2000001961644752,1999996459521815,1999998419451906,1999999896680476,1999992722182424,
  1999996475722690]
private def pvn_w0_0_p3 : List ℕ := [2000002049928041,1999994276521156,1999996313352796,
  2000006326172242,1999999164712277,1999995561178968,2000009425162259,2000008270757970,
  1999994742573717,1999999144946002,2000003684994129,1999992826406318,1999994542540755,
  2000006704401268,2000000836647164,1999993768972069,2000004309417822,2000006337530754,
  1999994275295886,1999997015309726,2000006422010279,1999999691574511,1999993971064391,
  2000004118258949,2000005003427616,1999995165703736,1999997976681341,2000008308966865,
  2000001672489521,1999994587718074,2000001904499554,2000006128714268,1999996189931030,
  1999994602459307,2000004561092676,2000003866697222,1999995885092378,1999998701719235,
  2000006400963438,2000000860125099,1999994111653907,2000000090887594,2000005183626220,
  1999999890945589,1999997022059043,2000004566303836,2000006013160332,1999997137966258,
  1999995600531559,2000003500648111,2000005425473593,1999997719829575,1999995719759896,
  2000001580811635,2000000477698389,1999994514334078,1999997032418681,2000005530504030,
  2000004865622474,1999995273178090,1999995026656526,2000004704569580,2000006158374620,
  1999996960777375]
private def pvn_w0_0_p4 : List ℕ := [1999993044786691,2000001480155995,2000007447043285,
  2000000193069552,1999993530670137,1999999233246263,2000006950412979,2000003533700136,
  1999993881925880,1999993727648824,2000003297265021,2000006764794878,2000000582954288,
  1999997047917094,2000002250780642,2000007712131752,2000003601803103,1999995297961776,
  1999995690814108,2000003080032239,2000005184951732,1999999456008846,1999995104575833,
  1999999137658768,2000005450943124,2000003016862256,1999994725580314,1999994043609738,
  2000003674767085,2000011426066684,2000006098307639,1999992088647397,1999986239659664,
  1999996479312396,2000010241946004,2000011182207916,1999998950643992,1999987664055251,
  1999989814269303,2000002260342747,2000009691433893,2000003997704797,1999993495466883,
  1999990843949819,1999998921306594,2000009037476210,2000009983095530,2000000579421804,
  1999991543809873,1999992436622561,2000001350710559,2000008852580940,2000007486649325,
  1999998204124461,1999990073388032,1999991154534823,1999999684474900,2000007058097319,
  2000007094000262,2000000394138723,1999993216182649,1999992709375810,1999999924244012,
  2000008198180678]
private def pvn_w0_0_p5 : List ℕ := [2000010142461569,2000004198656646,1999994597738940,
  1999988250375297,1999990549450488,2000000559965886,2000010972026511,2000014383434886,
  2000008545780619,1999996443835816,1999984500173334,1999979863497456,1999985735843084,
  1999998820708937,2000012305692902,2000020234392291,2000019216350995,2000009322517511,
  1999994894482504,1999982438953427,1999976575331986,1999978556861957,1999987409217970,
  2000000328993441,2000012782726885,2000020590177938,2000022139177602,2000017896024494,
  2000008900172752,1999996898015251,1999984701377871,1999974790062456,1999967971776867,
  1999964154776522,1999963523248764,1999966049116130,1999970773822471,1999976774176176,
  1999984511834499,1999995650832941,2000012449738836,2000038776884493,2000082112381728,
  2000154650790113,2000273913817400,2000464815701742,2000763221368070,2001219115020724,
  2001898694892792,2002886635856346,2004288996600368,2006235083187809,2008876491076966,
  2012383435548164,2016939224164671,2022732399608001,2029945174390972,2038738038519335,
  2049232288681161,2061492469636175,2075509700917451,2091186643304853,2108325986263729,
  2126625186296607]
private def pvn_w0_0_p6 : List ℕ := [2145679413586070,2164992978208908,2183998486375080,
  2202082949670582,2218619952479091,2233005965307330,2244697537377295,2253245573310742,
  2258323550090839,2259747640428814,2257487464841098,2251666575608298,2242552359570009,
  2230536169820431,2216105814575186,2199813390877547,2182241536840680,2163970730531287,
  2145549743600652,2127470985218147,2110152121063077,2093924798034948,2079030514175352,
  2065622856494592,2053774761722426,2043489263800405,2034712298471880,2027346358843751,
  2021263999354801,2016320344596325,2012363926736357,2009245400850883,2006823965375598,
  2004971588076950,2003575340436610,2002538240664330,2001779007154811,2001231068291087,
  2000841102415688,2000567319573749,2000377650958901,2000247977145852,2000160493991652,
  2000102281444938,2000064106679342,2000039463167639,2000023825456464,2000014087103862,
  2000008145549118,2000004600022522,2000002534043961,2000001360254191,2000000710872393,
  2000000361441235,2000000178727157,2000000085951263,2000000040222374,2000000018341483,
  2000000008170657,2000000003570566,2000000001540130,2000000000661202,2000000000285324,
  2000000000124946]
private def pvn_w0_0_p7 : List ℕ := [2000000000055890,2000000000025562,2000000000011892,
  2000000000005575,2000000000002603,2000000000001193,2000000000000532,2000000000000228,
  2000000000000090,2000000000000032,2000000000000008,2000000000000001]
private def pvn_w0_0 : List ℕ := pCat pvn_w0_0_p0 (pCat pvn_w0_0_p1 (pCat pvn_w0_0_p2 (pCat
  pvn_w0_0_p3 (pCat pvn_w0_0_p4 (pCat pvn_w0_0_p5 (pCat pvn_w0_0_p6 pvn_w0_0_p7))))))
private def pvn_w0_1_p0 : List ℕ := [1999998616330508,1999998799517777,2000000134407129,
  2000000699043271,1999998943789692,1999998232945107,2000000733840353,1999999894012040,
  1999999573239618,2000001721712227,1999999277590212,1999999688752224,2000000425367372,
  2000000639656583,1999998585624012,1999999222773129,2000000516746429,2000002401498928,
  1999999662204065,1999997749919714,2000000392593062,2000000545243325,1999999655171512,
  2000000723160827,2000000010440224,1999999540474102,2000000844994448,1999998238781629,
  2000000990652716,2000000301747679,1999999869498028,1999999505780336,1999999221216305,
  2000002543052133,1999999507527424,1999999496406176,1999998309130089,1999999355758613,
  2000001976455370,2000001711413067,1999999461763465,1999998111820230,1999999893414308,
  2000000823027994,2000000269980803,1999998681382222,2000000491710504,2000000925249943,
  2000000638843852,2000000077888399,1999998237673715,1999998649567538,2000002811655040,
  2000000067446147,1999997941653535,1999999966701355,2000002110674287,2000000626531742,
  1999999027122763,1999998569080061,2000000817147546,1999998725725993,2000000003181289,
  2000002400650423]
private def pvn_w0_1_p1 : List ℕ := [2000000319763631,1999998849613718,1999999776014923,
  1999999046384193,2000000342930242,2000001396619610,1999999244570269,1999999618923311,
  1999999776437245,2000000506850428,1999999581123215,2000000546375329,2000001427292133,
  1999999378739041,1999999614959250,1999998905245606,1999999301229278,1999999625810470,
  1999999988678258,2000001724195209,2000000274802804,2000001487482596,2000000222995375,
  2000000864024737,1999998593181978,1999997648358050,1999998438236352,1999998145713275,
  2000002325124909,2000001101340179,2000001447134633,1999999548143380,2000000278382622,
  1999999506946161,2000001030777460,2000000484140633,2000000140613281,2000001653170688,
  1999998937082123,2000001346738337,1999997524021672,2000000568875511,1999997702276491,
  1999998146053973,1999998856761140,1999995571060966,2000000350133241,1999994787302193,
  2000004304594057,1999995058237881,2000006358837489,1999992748791925,2000013325549263,
  1999995028370260,2000015007651132,1999998708711399,2000008670207937,2000001764196666,
  2000004579029692,2000007109170078,2000000832388772,2000008915072467,1999996997572721,
  2000005523774571]
private def pvn_w0_1_p2 : List ℕ := [1999996465011692,2000001356707147,2000004848400243,
  1999998161892021,2000013338402030,2000004583605848,2000010405088134,2000010644037176,
  1999997738094445,2000003607502451,1999994063214617,1999998523521753,2000001928711008,
  1999994504679681,2000005001723469,1999999015650292,1999998943877899,2000004243538681,
  1999993564391685,2000001888710298,2000002771506892,1999997719789733,2000007840703535,
  2000000216963137,1999998847257609,2000004326619576,1999994123776579,2000001469304591,
  2000004347291685,1999994190301031,2000004309950308,2000000736590562,1999990895142860,
  2000004005733037,1999999941400147,1999992969513158,2000003948489158,1999996539652030,
  1999994117322951,2000008032725946,1999999342420140,1999994952296011,2000006814753527,
  1999999676226303,1999997186727025,2000007222186392,1999997116177523,1999991325627483,
  2000002498646063,1999999360979762,1999995427099463,2000002731981696,1999998722077681,
  1999994864383594,2000001661960062,1999999746850561,1999997466464724,2000003686127357,
  2000001451180196,1999998730177892,2000004095163510,1999999914556344,1999995317520365,
  2000003681793482]
private def pvn_w0_1_p3 : List ℕ := [2000001981720641,1999992245809064,1999998950559494,
  2000002795537071,1999991001973700,1999993588757842,2000005471772576,1999997629096453,
  1999990976726102,2000003423057713,2000006123568934,1999997862461982,2000004195374409,
  2000009507249906,1999996480613280,1999992920664486,2000003486656936,2000000904959145,
  1999991838776609,2000000671465128,2000006878358657,1999997991700659,1999995847913592,
  2000005828246233,2000001975471893,1999993552120596,2000000130514487,2000006836782143,
  1999998113904255,1999994154478456,2000004417431188,2000005212671526,1999996460277058,
  1999998334193720,2000006923122515,2000002454438929,1999994323131151,1999999826014497,
  2000004894915174,1999998652711838,1999995148227032,2000002848865131,2000005756329982,
  1999997753826846,1999996604065403,2000003298896504,2000002519729098,1999995728592313,
  1999997796282784,2000006611911597,2000004877038752,1999996634507739,1999998010532951,
  2000004349741910,2000002880867884,1999997177627476,1999999559558036,2000004942929567,
  1999999627708116,1999991859412290,1999996270217751,2000005603404661,2000004185887736,
  1999994844700391]
private def pvn_w0_1_p4 : List ℕ := [1999995077436049,2000005046237105,2000006353020151,
  1999997021264314,1999993547694815,2000001269272307,2000006789112932,2000000339063876,
  1999993291611300,1999998563011313,2000006981941668,2000004597771061,1999995772288586,
  1999994000558994,2000001190419865,2000005093317609,1999999691217326,1999995914644051,
  2000001548991068,2000007936783745,2000005428951709,1999997671131544,1999995804151220,
  2000002109172399,2000005617978632,2000000044809786,1999994638420748,1999998305255918,
  2000005690104427,2000005492988925,1999996301926864,1999990420305815,1999998022013703,
  2000010772722314,2000012002464025,1999999428553273,1999987455758524,1999989678772382,
  2000003492430029,2000012451382731,2000006021814537,1999992751783069,1999988249400975,
  1999996215152145,2000006477888131,2000007319632032,1999998087479112,1999990244319524,
  1999993605634387,2000004270811959,2000010449892914,2000006216844471,1999996335291527,
  1999990950475431,1999995774235484,2000005560982671,2000009648619344,2000004068694878,
  1999994705667589,1999990063504409,1999993957530869,2000002715501537,2000007920375605,
  2000004602896732]
private def pvn_w0_1_p5 : List ℕ := [1999996593994903,1999991887109885,1999994667516740,
  2000002821388087,2000010018425450,2000009900227676,2000001649749121,1999991633599856,
  1999987677758612,1999992547156105,2000003078905990,2000012739456773,2000014859981311,
  2000007051166192,1999993748453425,1999982904520468,1999980269989537,1999987046953748,
  2000000319991311,2000013876879066,2000020865700631,2000018088049460,2000007511192791,
  1999993823153310,1999981986276375,1999976351246718,1999979166109636,1999988949976733,
  2000001557268789,2000012996079500,2000020532254879,2000022228364526,2000017462635503,
  2000007850976509,1999996262309971,1999984879827991,1999974953951607,1999967737253506,
  1999964241906748,1999964200443529,1999966416997511,1999970216890837,1999975787163687,
  1999983368317651,1999993393349702,2000008006184058,2000032171386000,2000073776761570,
  2000144446024581,2000262149583575,2000454361165873,2000760441832901,2001233980456567,
  2001946315180307,2002990536739351,2004484008731801,2006568600798342,2009409260306548,
  2013190943753406,2018112426616673,2024375640392764,2032170963265066,2041660059204494,
  2052957388182417]
private def pvn_w0_1_p6 : List ℕ := [2066110874136832,2081082946457982,2097734614006690,
  2115815612998690,2134962551074097,2154705622737571,2174483999059734,2193669975450194,
  2211601274539321,2227619345279630,2241110058784203,2251542833161142,2258504832653149,
  2261727663201884,2261104435092440,2256695477140641,2248721912377708,2237547790965972,
  2223652966525055,2207599784840880,2189996789887122,2171462369879846,2152590941362607,
  2133923979901981,2115927766469248,2098978970178791,2083358213293143,2069250842774096,
  2056753525880093,2045885069256356,2036599918401295,2028802956099224,2022364382327680,
  2017133625165107,2012951451883363,2009659745713704,2007108752321417,2005161908927583,
  2003698584341226,2002615156647169,2001824856833229,2001256753583846,2000854186452064,
  2000572893895164,2000379033586201,2000247249763972,2000158900456794,2000100514921478,
  2000062511637274,2000038174280390,2000022860536399,2000013406936042,2000007690243832,
  2000004309170382,2000002356217915,2000001256008065,2000000652207418,2000000329721354,
  2000000162234517,2000000077695214,2000000036235228,2000000016477051,2000000007321075,
  2000000003189321]
private def pvn_w0_1_p7 : List ℕ := [2000000001369001,2000000000582860,2000000000248091,
  2000000000106418,2000000000046291,2000000000020471,2000000000009177,2000000000004140,
  2000000000001862,2000000000000825,2000000000000354,2000000000000144,2000000000000052,
  2000000000000017,2000000000000003]
private def pvn_w0_1 : List ℕ := pCat pvn_w0_1_p0 (pCat pvn_w0_1_p1 (pCat pvn_w0_1_p2 (pCat
  pvn_w0_1_p3 (pCat pvn_w0_1_p4 (pCat pvn_w0_1_p5 (pCat pvn_w0_1_p6 pvn_w0_1_p7))))))
private def pvn_w0_2_p0 : List ℕ := [1999999021194035,1999998592822077,1999999154162988,
  2000000607156228,2000000749624370,1999998186115212,1999998999552168,2000000703497393,
  1999998650892147,2000000606645565,2000000866635882,2000000209733084,1999999050322295,
  2000000681403109,2000000536534235,2000000162962379,1999998239784132,1999998782756890,
  2000002310159363,2000001359220144,1999998736716019,1999999572951749,1999999952700807,
  1999999151306507,2000001466259819,1999998997911176,2000000786360511,2000000498907437,
  1999999191790909,2000000068292206,1999998920637499,2000001967818945,1999999393747167,
  1999999003761216,1999999958345100,2000000503932571,2000001462202861,2000000319048005,
  1999998472510816,1999997916588370,2000000629986297,2000001869929370,2000001332753090,
  1999998570416521,1999999157856262,2000000644421146,2000000059287134,1999999435876821,
  2000000079850422,1999998707754924,2000001781554435,2000002032785532,1999998462254490,
  1999997768837607,2000001183424226,2000001086761630,1999999877700567,1999997731911999,
  2000000701062876,2000001897448428,1999999500183848,2000000098619679,2000000841666777,
  1999998216705198]
private def pvn_w0_2_p1 : List ℕ := [1999998798558106,2000000740769353,2000000278427091,
  2000001626607145,2000000165163111,1999999103100388,1999998914870858,2000000359398815,
  2000000952518215,1999999148973780,2000000478807998,1999999962732008,1999999379217737,
  1999999855429320,1999999946015515,2000001539282417,1999999742002493,2000000863528601,
  1999999242319568,1999999351009374,1999998819376732,1999999148603832,2000001134940074,
  1999999264389008,2000001772368015,2000000386585256,2000001740660034,2000000712651516,
  1999999940302859,1999997243771504,1999997671042721,1999999194438074,1999999610867282,
  2000002778424985,1999999259945101,2000001948959077,1999998691644922,2000001027655827,
  2000000164317128,1999999252103874,2000002966258037,1999997664172898,2000004439897879,
  1999995394370614,2000005634504990,1999992536248787,2000007145870566,1999989534313884,
  2000008498859195,1999988023489590,2000003696720419,1999994636064347,2000000227300049,
  2000000038182817,1999996389799513,2000003668237750,1999995918274380,2000008930874613,
  2000000931472589,2000007710899715,2000004839641668,2000001217867337,2000009884908283,
  1999998354640200]
private def pvn_w0_2_p2 : List ℕ := [2000009657356761,2000004943501760,2000000220270577,
  2000008059576384,1999995878583237,2000002682356579,2000000902083550,1999997534931483,
  2000007595540904,2000002180353091,2000011421019237,2000012555810296,2000002371925864,
  2000007950266838,1999998317591292,1999996997560991,2000003198243999,1999993488499735,
  2000000980255294,2000003218422367,1999996106106105,2000004639987278,1999998297973190,
  1999995270034029,2000004981196864,1999996760436513,2000001020061139,2000009172744838,
  1999996334360137,2000001215449381,2000005582359044,1999992676218316,2000001435439550,
  2000005993713338,1999994540016820,2000002245481385,2000002242276117,1999991595184866,
  2000002652417046,2000003443093501,1999991133352032,1999999631379098,2000002127864268,
  1999993595606043,2000002383255324,2000004212404407,1999993939361941,2000000879254149,
  2000006488954406,1999998959796356,2000000483035195,2000001271107565,1999994451619608,
  1999998124854942,2000001648590072,1999996478146777,1999999100085611,2000001268733850,
  1999995161336819,1999998448789580,2000002921613963,1999996008688669,1999998676207805,
  2000007609615641]
private def pvn_w0_2_p3 : List ℕ := [1999999735913431,1999994905914365,2000005685201413,
  2000003372406419,1999992778125909,2000000981373944,2000006355253600,1999993446812545,
  1999992060854243,2000003397517980,1999998163220494,1999991252353126,1999999796955825,
  2000001817556933,1999992100599822,1999999155363276,2000010452176783,2000003878494047,
  1999996491651257,2000004754239674,2000004054465682,1999992980250927,1999995742186912,
  2000004481035157,1999999297010719,1999994034298059,2000003665118063,2000006006092570,
  1999995933587580,1999995948328049,2000005333785397,2000002914715015,1999994115870533,
  1999999263693011,2000005847309858,1999999497437743,1999995245176251,2000002777863725,
  2000006467279298,1999998560029862,1999997014125614,2000004338474983,2000003062870297,
  1999995564641067,1999997048213982,2000004436574704,2000002491883807,1999996081830464,
  2000000079088328,2000005669169086,2000000389421877,1999994098728865,1999998658761649,
  2000005801380402,2000002471807794,1999996992583305,2000001162135387,2000005098627747,
  1999999926727419,1999995934619085,2000001988674699,2000007808005665,2000000814482318,
  1999991557057038]
private def pvn_w0_2_p4 : List ℕ := [1999995958831112,2000005107875344,2000002928623433,
  1999994355905067,1999995005346854,2000004531190273,2000006447073236,1999997421589876,
  1999993826628178,2000001408965747,2000006454009156,2000000623986919,1999993571458877,
  1999997165371287,2000005911521692,2000005435835301,1999997331152796,1999995234654019,
  2000001021082246,2000004051513706,1999999197094154,1999994513075537,1999999004497675,
  2000007096592760,2000006640586386,1999999211391098,1999996696991836,2000002039837327,
  2000006122568565,2000001625142751,1999994248083433,1999995736211075,2000005264313860,
  2000008727841390,1999999853451833,1999989703005439,1999991827953231,2000005192609556,
  2000014358379256,2000007560192740,1999992517249555,1999987112241086,1999996607442184,
  2000008842350722,2000010006869273,1999999471509379,1999989760770502,1999992050629762,
  2000002556323087,2000007912439109,2000002272754293,1999992873635753,1999990412308275,
  1999997979777071,2000007954782572,2000009647004027,2000001492323822,1999992832750207,
  1999992614090749,2000000334209445,2000008152480079,2000008451950480,2000000552175424,
  1999991979531557]
private def pvn_w0_2_p5 : List ℕ := [1999991042987772,1999997938859657,2000005444138061,
  2000006882273520,2000001357806388,1999993763680842,1999991264754994,1999997019897187,
  2000006423494896,2000011404768931,2000007965350564,1999998576509309,1999989590743330,
  1999987512144108,1999994669129869,2000006516984518,2000014770666336,2000013973381828,
  2000004566894148,1999991420427830,1999981387587977,1999980307928817,1999989195725170,
  2000003231324568,2000015396217446,2000020606169336,2000016945943230,2000005727990666,
  1999991583827265,1999980609027118,1999976840908141,1999980716237376,1999990385499310,
  2000002918102125,2000014424250111,2000021139200831,2000021435476628,2000016142652120,
  2000006936585030,1999995434876332,1999983700572920,1999974081202157,1999967862929899,
  1999964815283865,1999964351665910,1999966342967069,1999970512534259,1999976016110651,
  1999982459379899,1999991097411230,2000004858456303,2000028206916556,2000068530086585,
  2000138696016015,2000259256253453,2000460287909476,2000784326274753,2001290757416754,
  2002060159295573,2003197215476595,2004832386845830,2007122791756040,2010251262897461,
  2014421636535879]
private def pvn_w0_2_p6 : List ℕ := [2019849387160094,2026748306214645,2035314155849243,
  2045705505612985,2058022097791655,2072282555494321,2088404575538767,2106190622009686,
  2125321025217590,2145355642456607,2165745201706095,2185853185770153,2204987812615863,
  2222441758132371,2237535895548658,2249663058976959,2258328227738194,2263181865223250,
  2264043338421877,2260911900992021,2253964027013092,2243537673923461,2230105647845667,
  2214241151055499,2196578843467530,2177774698655403,2158467819941649,2139247138371452,
  2120625338368634,2103021393013771,2086751942295250,2072030740074861,2058974755284623,
  2047615255920015,2037912195100626,2029770310206733,2023055477610237,2017610057821846,
  2013266254882554,2009856890025005,2007223388909704,2005221121164968,2003722453452178,
  2002617973646890,2001816344429075,2001243194590022,2000839392073519,2000558982040387,
  2000367018530829,2000237465705931,2000151291661943,2000094826177103,2000058408130953,
  2000035313301800,2000020930996926,2000012147738398,2000006895129658,2000003823443058,
  2000002069210462,2000001092006856,2000000561592574,2000000281309272,2000000137218691,
  2000000065185295]
private def pvn_w0_2_p7 : List ℕ := [2000000030173250,2000000013624310,2000000006012466,
  2000000002600789,2000000001107321,2000000000466574,2000000000195819,2000000000082410,
  2000000000034966,2000000000014997,2000000000006493,2000000000002824,2000000000001220,
  2000000000000517,2000000000000212,2000000000000081,2000000000000026,2000000000000006,
  2000000000000001]
private def pvn_w0_2 : List ℕ := pCat pvn_w0_2_p0 (pCat pvn_w0_2_p1 (pCat pvn_w0_2_p2 (pCat
  pvn_w0_2_p3 (pCat pvn_w0_2_p4 (pCat pvn_w0_2_p5 (pCat pvn_w0_2_p6 pvn_w0_2_p7))))))
private def pvn_w0_3_p0 : List ℕ := [1999999411708086,1999998862938079,1999998609455963,
  1999999259223661,2000001329700598,2000000258241032,1999997882478558,2000000241251549,
  1999999377670259,1999999208818028,1999999676711499,2000001357032525,2000000026784738,
  1999999738790550,1999999651689967,2000000503207440,2000001632646321,1999999010293255,
  1999997455893902,2000000380635209,2000002011050020,1999999626014991,2000001130982917,
  1999998597335745,1999999622945678,2000000586463787,1999999040484215,2000000929069180,
  1999999372292403,2000001456440154,1999999729693858,1999998631551011,2000000343587679,
  2000000580472016,2000000369670302,1999999438360215,1999999226783667,1999999393457410,
  2000001598243472,2000001415780928,2000000055568381,1999997735455109,1999998336727438,
  2000001193165027,2000001971272608,1999999384101263,2000000324265797,1999999351480063,
  1999999655338208,2000001120241797,1999999904115121,1999997301502561,2000000593246050,
  2000001996255969,2000001362561454,1999998368799051,1999998290201238,2000001704914631,
  2000001001114764,1999998073334355,1999999763773435,2000000729498409,1999999100172493,
  2000001192928758]
private def pvn_w0_3_p1 : List ℕ := [2000000833942133,2000000236546041,1999999425361453,
  1999998770849000,1999999251997239,1999999691269509,2000002135849449,2000000656548035,
  1999999060931565,2000000000265212,1999999430598280,2000000544704990,1999999179651076,
  2000001054178592,1999999872208120,1999999594289443,1999999702716578,1999999264269245,
  2000001226924660,1999999277840719,2000001867726613,1999999995463654,1999999959954108,
  1999998934002586,1999999358273653,1999999146984493,1999999742697445,2000000758619961,
  1999998751762023,2000002718163969,2000000229552204,2000003066684199,1999999310989137,
  1999998173305690,1999998595699760,1999996147959829,2000003234124746,1999996301529582,
  2000005807033249,1999994644013890,2000007488372346,1999991830807602,2000009178786219,
  1999990772356698,2000009503917763,1999993769112759,2000004341524601,2000000500562658,
  1999998038613677,2000002775557137,1999995663411637,2000004920002932,1999993636542975,
  2000001567542267,1999995429352485,1999996822492558,2000002141866747,1999993606122457,
  2000004039717015,1999994131434797,1999999568914312,2000005292976310,1999997209699080,
  2000009892278367]
private def pvn_w0_3_p2 : List ℕ := [2000002724857943,2000002863349086,2000008030241587,
  1999999647566012,2000008627284767,2000004722651134,2000003017487861,2000008762163927,
  1999998048662326,2000003562463061,2000002914809520,1999994288488357,2000003837587731,
  2000000796995348,2000004100389269,2000014819043839,2000005418832559,2000007834970228,
  2000008326430449,1999996872184550,2000003083042037,1999999426812888,1999993195630630,
  2000005157593132,1999999497087491,1999996129571813,2000007125588953,1999996518866467,
  1999994160726717,2000006066035241,1999997280312378,1999998575006341,2000009507921787,
  1999998829661782,1999998525165366,2000006137246099,1999995330087777,1999998125700309,
  2000008367694989,1999997235689182,1999995850902096,2000004899792161,1999997327387414,
  1999996571648138,2000004296507019,1999996190322438,1999993376423239,2000002538437963,
  1999999869854213,1999996685108754,2000001346949276,1999998626244654,1999998556837195,
  2000005552295490,2000002118471359,1999997931571189,2000002041581373,1999998248979844,
  1999994525512125,2000002268333187,2000000851118027,1999993248184806,2000000522744373,
  2000003858428902]
private def pvn_w0_3_p3 : List ℕ := [1999992588543208,1999995570372668,2000006566661188,
  1999999458835129,1999994081970208,2000006104929577,2000005101369896,1999993778916782,
  1999999290043981,2000007969749530,1999997927067486,1999994958766689,2000003188793514,
  1999999360514119,1999990843634261,1999999215412836,2000003874032729,1999992232830345,
  1999991125833045,2000002474131072,2000002518113936,1999996308520420,2000004198038859,
  2000009526781606,1999999450881117,1999995826337676,2000003397740629,2000001759104555,
  1999992442910267,1999997139417376,2000006297003290,2000000609279670,1999994690786748,
  2000001428604693,2000005565144424,1999997795556338,1999995489106705,2000003817054376,
  2000003547433064,1999995716176175,1999997419695228,2000004709287026,2000002704163686,
  1999996468228229,2000000632567483,2000006443731079,2000000849242869,1999995472501952,
  2000000292236554,2000004293271952,1999998883128518,1999995258951424,2000002328146513,
  2000006465173674,1999999322402673,1999994985092378,2000000347114500,2000003793493234,
  1999999106843658,1999996955448385,2000003730374383,2000006336953776,1999998074327855,
  1999994222196578]
private def pvn_w0_3_p4 : List ℕ := [2000002625962830,2000009037897193,2000002342412355,
  1999993261239044,1999996626333269,2000005053840813,2000002297016284,1999993592509333,
  1999994726788708,2000003700999846,2000005791218120,1999998029315654,1999993966531683,
  2000000966810871,2000006758045527,2000001267782955,1999994042916355,1999996526898858,
  2000004103751413,2000005052866275,1999998589163035,1999995926606578,2000001529972479,
  2000004959988056,1999999436398529,1999993610786013,1999996728242540,2000004681164220,
  2000006594357110,2000000405447366,1999996507022916,2000001831752087,2000007785686412,
  2000003863337601,1999994708322516,1999993215920708,2000002353091146,2000010548018241,
  2000005719965157,1999992280724102,1999987375407562,1999998037434683,2000011650110326,
  2000012519837582,2000000220975595,1999988947113712,1999991301045993,2000003654414415,
  2000010591524375,2000004410454680,1999993648893966,1999990820312996,1999998107007718,
  2000006497817455,2000005981661491,1999996782314469,1999989670443323,1999993095277375,
  2000003208818764,2000009400274896,2000006064516401,1999997087223411,1999991645500236,
  1999995528937030]
private def pvn_w0_3_p5 : List ℕ := [2000004772899968,2000009611348337,2000005331102727,
  1999996531958309,1999991243010763,1999993699124858,2000001457404140,2000007193677994,
  2000005143470628,1999997231006969,1999991171227599,1999992565442249,2000000457764926,
  2000009062920611,2000011786884259,2000005732960035,1999994830233151,1999987332615828,
  1999988820465424,1999998178608375,2000009506097565,2000015945392856,2000012985176984,
  2000001473822423,1999987925619928,1999980112087382,1999981884154816,1999991999930102,
  2000005866939806,2000017294411989,2000020802994518,2000014787835593,2000002471548884,
  1999989270482664,1999979812265471,1999977073760915,1999982071819484,1999992983887056,
  2000005591329351,2000015725526971,2000021088523313,2000020873880875,2000015075452400,
  2000004953016003,1999993148282301,1999982264983643,1999973582561392,1999967500815726,
  1999964469716202,1999964685365958,1999967355893251,1999971215549721,1999975792107512,
  1999981708817212,1999990124238086,2000003061297239,2000025151135683,2000065474640229,
  2000138799388244,2000267395041927,2000484593721092,2000839400373877,2001400645847914,
  2002260381210128]
private def pvn_w0_3_p6 : List ℕ := [2003537186138828,2005379091613157,2007964278640638,
  2011497785151522,2016203894634123,2022314683786598,2030054673204844,2039621110815000,
  2051160443088058,2064743310978963,2080341295947854,2097808194175650,2116867888406529,
  2137110833757182,2158001327991169,2178897014180006,2199080228023358,2217798773040335,
  2234312488345978,2247941660049516,2258113298471824,2264401162501948,2266555465704924,
  2264519013973479,2258428205455545,2248599334053439,2235502280757220,2219724644564792,
  2201929822620853,2182812785509380,2163057369548137,2143298643241998,2124093136364384,
  2105898528577728,2089063092665465,2073824113964893,2060313831750022,2048571132425569,
  2038557130730579,2030172797888148,2023276914882460,2017702873774035,2013273228537055,
  2009811359669834,2007150072326943,2005137308937476,2003639380019863,2002542208176020,
  2001751079728142,2001189351270811,2000796496098266,2000525811546574,2000342044425627,
  2000219126592715,2000138147658264,2000085631507262,2000052133451168,2000031139274625,
  2000018226865065,2000010443236880,2000005850717815,2000003201860079,2000001710139887,
  2000000890784829]
private def pvn_w0_3_p7 : List ℕ := [2000000452242570,2000000223695222,2000000107785653,
  2000000050599701,2000000023155436,2000000010340396,2000000004513938,2000000001931226,
  2000000000812691,2000000000337937,2000000000139605,2000000000057611,2000000000023860,
  2000000000009940,2000000000004159,2000000000001739,2000000000000721,2000000000000290,
  2000000000000110,2000000000000037,2000000000000010,2000000000000001]
private def pvn_w0_3 : List ℕ := pCat pvn_w0_3_p0 (pCat pvn_w0_3_p1 (pCat pvn_w0_3_p2 (pCat
  pvn_w0_3_p3 (pCat pvn_w0_3_p4 (pCat pvn_w0_3_p5 (pCat pvn_w0_3_p6 pvn_w0_3_p7))))))
private def pvn_w0_4_p0 : List ℕ := [1999999689034558,1999999279270708,1999998926918400,
  1999998201154874,1999999669380488,2000001932198974,1999999064610140,1999999225665710,
  1999999590098013,1999999916080837,1999998483701565,1999999722996416,2000000572873280,
  2000000501553706,2000000451892194,1999998996340945,1999999591226937,2000001934692475,
  2000001391490391,1999997152499415,1999999690654902,1999999542174492,2000000532456021,
  2000001909810442,1999999055699470,2000000563786190,1999998943431581,2000000251858570,
  2000000013152024,1999998933587002,2000000788758321,2000000962121948,2000000033321876,
  1999999078387575,1999999886382537,1999999917559570,2000000985830436,2000000174118526,
  1999999192134118,1999998708497780,1999999936924322,2000001594183696,2000002511283810,
  1999998347631374,1999998051406918,1999999705796930,2000000248032141,2000000619479690,
  2000001700767125,1999998587828499,1999999394911804,2000001221328931,2000000914392290,
  1999998961465790,1999997505052860,2000000137323660,2000003070330235,2000000233172839,
  1999997733405524,2000001012506665,2000000324364239,1999999760699843,2000000088951835,
  1999999569502940]
private def pvn_w0_4_p1 : List ℕ := [1999999626644956,1999999248436543,2000000863234733,
  2000000517628735,2000000637338657,2000001291329368,1999998192678094,1999998887476966,
  1999999039536818,2000001544004517,2000000484037067,1999999993688189,2000000629915736,
  1999999038835578,2000000552896246,1999998627218442,2000001321821454,1999999849797308,
  2000000029036727,1999999763019164,1999999717090366,1999999523915549,1999999495338077,
  2000001702503672,1999999218189745,2000002524330669,1999998542017793,2000000065091128,
  1999999284343617,1999998504888999,2000001804764721,1999995905372076,2000004078162448,
  1999995249682623,2000008258357130,1999995131403949,2000009022736218,1999989938479535,
  2000007293082539,1999989698128440,2000005676700022,1999996049086203,2000000757166756,
  2000003370170452,1999996143809473,2000004761912738,1999995653322468,2000004676949761,
  1999996310409813,2000002214770376,2000002438146315,1999996902973320,2000005340140480,
  1999994798673633,2000003726624688,2000000260649255,1999996174233138,2000004384234069,
  1999991765678094,1999999959547931,2000000389594094,1999994054341480,2000003117862621,
  1999994596640806]
private def pvn_w0_4_p2 : List ℕ := [1999998109054853,2000001662526605,1999996696859156,
  2000007203580942,2000002437011729,2000002190300612,2000008776823549,1999999132047806,
  2000005817309926,2000008300547345,2000000659857972,2000008957282564,2000003959927530,
  2000000562454485,2000008027951547,1999997015446264,1999996791685177,2000003501577315,
  1999997142792886,2000007395627159,2000012189219840,2000002857689110,2000011745283797,
  2000009063194525,1999996364634023,2000005060770181,2000001276819541,1999991861830078,
  2000004313368625,2000002535912036,1999994655944300,2000004879223082,2000000321471529,
  1999992427436118,2000003495444635,2000001195466391,1999995520593588,2000007445662387,
  2000004844574585,1999994629993216,2000002502898077,2000003256443513,1999996444584407,
  2000003145266714,2000003230114169,1999995011086531,2000000184298365,2000003559764414,
  1999997479208701,1999998767517974,1999999271589169,1999995018700519,1999999887614993,
  2000002213908808,1999995259664622,1999997769580532,2000002589384887,1999997727770307,
  2000000612287520,2000007663392897,1999999067631297,1999994796749022,2000004145156543,
  2000001195352842]
private def pvn_w0_4_p3 : List ℕ := [1999991297932162,2000000570533321,2000005677165237,
  1999994252232916,1999993769706113,2000005047299392,1999998504088945,1999991910337831,
  2000002592342799,2000006179126054,1999995867561533,1999998116519876,2000006612260114,
  1999999468899601,1999995881698308,2000005190795637,2000004288913679,1999992524611148,
  1999995699715995,2000005061061013,1999998061822606,1999991690573111,1999998437934513,
  1999999854208768,1999991849028220,1999995453050018,2000006997390495,2000004025900431,
  1999997531016765,2000003670153591,2000007419643652,1999998027599536,1999993158833879,
  2000001508441338,2000003250067505,1999995476852848,1999997128819328,2000004736373007,
  2000002275282328,1999995465334341,1999999138100207,2000005405204618,2000000203060807,
  1999995103294576,2000000799023776,2000004305485656,1999998594176134,1999996133088944,
  2000003048731035,2000005917501150,1999998911473671,1999997048819733,2000003696267130,
  2000003910094083,1999996494783016,1999995476209436,2000002987918261,2000005204097469,
  1999998523735848,1999997023753652,2000003077444473,2000002705178369,1999995686198952,
  1999996087523930]
private def pvn_w0_4_p4 : List ℕ := [2000004957600923,2000007264440201,1999997954126913,
  1999993089280462,2000001835678881,2000008896023788,2000002751958131,1999995118785582,
  1999998418826085,2000005477732921,2000002729464236,1999993780638430,1999993989754595,
  2000002926269396,2000005131131317,1999997856907962,1999994200309405,2000000251926456,
  2000006283003051,2000002517896801,1999995012784627,1999996069143408,2000003219839387,
  2000004176060645,1999998339511340,1999996258611915,2000001623295734,2000005960373714,
  2000001513961416,1999993875301941,1999994656185997,2000002786076733,2000005843325583,
  2000000173418251,1999995821337105,2000000518807674,2000008391827791,2000007584779880,
  1999997170178357,1999990788643557,1999998158202874,2000010052370938,2000010516207037,
  1999998119118398,1999987308961241,1999991029523315,2000005452695779,2000013784550348,
  2000006592619832,1999993455780978,1999989907459918,1999998524655486,2000008114098682,
  2000007707553356,1999998229010495,1999991104240273,1999994768918694,2000004198172232,
  2000007588122046,2000001053829272,1999992034456079,1999990105088183,1999997459235788,
  2000006869544286]
private def pvn_w0_4_p5 : List ℕ := [2000008666620567,2000001290764934,1999993184391738,
  1999992895377575,2000000193953074,2000007758211275,2000008573975150,2000001713577397,
  1999993409133480,1999991592775073,1999997686321321,2000005206760150,2000006960663747,
  2000001615068811,1999993760111901,1999990089837258,1999994545892463,2000004427601283,
  2000011818580622,2000010612512719,2000001715840566,1999991427548066,1999986576094351,
  1999990749726803,2000001989442101,2000013144472927,2000016628740185,2000010090395270,
  1999997381174097,1999985164343747,1999979497008271,1999983549427478,1999995694110330,
  2000009783673967,2000018930030549,2000019523902067,2000011974648254,1999999350014295,
  1999986389271916,1999978240801251,1999977971049420,1999984961357891,1999996096116222,
  2000007926653419,2000017382064781,2000021789958449,2000019846041461,2000012529470141,
  2000002232170006,1999991065407549,1999980474623683,1999971902180395,1999966644369475,
  1999964888577562,1999965659809942,1999967977508385,1999971560516252,1999976323358058,
  1999982034419696,1999989300007994,2000001053417584,2000023373468453,2000066228851210,
  2000145674713761]
private def pvn_w0_4_p6 : List ℕ := [2000287676537043,2000532297959337,2000937551983881,
  2001583566862212,2002577495928992,2004057956938818,2006196959534376,2009198176149614,
  2013291498079305,2018723617233824,2025743585945939,2034582632268008,2045429193362686,
  2058401725809830,2073522216998342,2090692938591409,2109678990284341,2130099706652129,
  2151432021734668,2173027608459300,2194143451652208,2213983583516632,2231748606981300,
  2246689042430993,2258157931660071,2265657574940670,2268875361598835,2267704816607436,
  2262249987952923,2252813431224294,2239869724501534,2224027562547576,2205984244678194,
  2186476918673951,2166235144376332,2145938961815310,2126185633923134,2107466818073436,
  2090156493864545,2074508847794574,2060664587958976,2048663760478161,2038462950952335,
  2029954725730612,2022987311379493,2017382843606844,2012953004704425,2009511418876310,
  2006882676284717,2004908228072366,2003449610599659,2002389541092870,2001631424664590,
  2001097766487016,2000727918533054,2000475517999793,2000305897032807,2000193663306436,
  2000120573814096,2000073756875069,2000044285572735,2000026071938768,2000015033855570,
  2000008482018023]
private def pvn_w0_4_p7 : List ℕ := [2000004677691972,2000002519288003,2000001324025857,
  2000000678584822,2000000338988919,2000000165008484,2000000078258433,2000000036170047,
  2000000016300758,2000000007170656,2000000003083988,2000000001299852,2000000000538616,
  2000000000220290,2000000000089334,2000000000036084,2000000000014568,2000000000005889,
  2000000000002379,2000000000000954,2000000000000376,2000000000000140,2000000000000048,
  2000000000000013,2000000000000002]
private def pvn_w0_4 : List ℕ := pCat pvn_w0_4_p0 (pCat pvn_w0_4_p1 (pCat pvn_w0_4_p2 (pCat
  pvn_w0_4_p3 (pCat pvn_w0_4_p4 (pCat pvn_w0_4_p5 (pCat pvn_w0_4_p6 pvn_w0_4_p7))))))
private def pvn_w0_5_p0 : List ℕ := [1999999862201629,1999999529498387,1999999557130693,
  1999998694032110,1999997552117331,2000000938660693,2000000754140962,1999999896911433,
  1999998896571765,2000000195328618,1999999644694283,1999998719644321,1999999393337869,
  1999999570646069,2000000584213580,2000001039209711,1999999965284035,1999997492084209,
  2000001888671895,2000001655661501,1999999564023624,2000000109218104,1999997496223328,
  2000000306199691,2000000241182901,2000000833112213,2000000930954310,1999999158207103,
  2000000135056854,2000000250717282,1999999498039309,1999998890833381,2000000584046783,
  2000000576859711,2000000625446116,1999999768129440,1999999337199216,1999999492047251,
  2000000814896515,2000000329590987,2000000999229879,1999998388811486,1999997892103590,
  2000000893767315,2000002682750718,2000000006407017,2000000176909898,1999998657516576,
  1999998195216547,2000000577353464,2000001423381410,2000000331847916,1999998976655773,
  1999999313109950,2000001779983389,2000002116692952,1999996931106051,1999998120959805,
  2000001466482985,2000000778788294,2000000184174546,1999999554121937,2000000383011099,
  1999999803557289]
private def pvn_w0_5_p1 : List ℕ := [1999999976238345,2000001023740607,1999998780579546,
  2000000284897957,1999999135089712,1999999730671401,1999999906955837,2000001188500042,
  2000002149451353,1999998661738486,1999999654657744,1999998092472420,2000000767864410,
  1999999833037359,2000000473350665,2000000845015926,1999999971652037,1999999815069828,
  1999998969054667,2000001363554959,1999998337303798,2000001926962271,1999999182408496,
  1999999901267981,2000000587914415,1999997261173559,2000003008521123,1999995874314008,
  2000006587501314,1999994363080257,2000007346434669,1999991544070771,2000008331725276,
  1999990751077131,2000007931896913,1999992238251947,2000002650320281,1999999606132762,
  1999999144171011,2000007107773092,1999996152039089,2000004923843830,1999995065178371,
  2000001182256442,1999996924558128,1999998274571303,2000003816402071,1999994741730051,
  2000005400548146,1999997633642870,2000000228760498,2000003098444890,1999994334358370,
  2000006061666965,1999998254574686,1999999295269273,2000005221600661,1999994464674629,
  2000003598145692,2000001287006980,1999997563346678,2000003545700366,1999994391072774,
  1999999231345585]
private def pvn_w0_5_p2 : List ℕ := [2000000145549547,1999994234207252,2000003081474478,
  1999996223550073,1999994746260570,2000002593388217,1999994569476215,2000001093751088,
  2000006141508166,1999998670613040,2000006608381465,2000004143634339,1999999344712439,
  2000009879483604,2000003791928921,2000001580778099,2000010544878094,2000002171510804,
  2000003840830778,2000008990732085,1999994525461790,1999997318366968,2000004903990001,
  1999995393815595,2000004226951712,2000013378957867,2000003096507585,2000008717878866,
  2000012884604166,1999999117029686,2000001683868231,2000004920069522,1999993879722315,
  1999999793817564,2000006241561455,1999995913413110,1999999236863689,2000005144235110,
  1999994540554470,1999995587844933,2000004584044593,1999999908914064,2000000300488043,
  2000005886652445,1999999268467692,1999997468512062,2000004252644169,2000001473509361,
  1999998814593256,2000002127157284,1999998716655285,1999998416596336,2000004502037159,
  1999999906125482,1999994266021294,2000000888984806,2000000218760621,1999994644246722,
  2000000658992748,2000002593236192,1999992032100607,1999996898503803,2000007213226077,
  2000000334877764]
private def pvn_w0_5_p3 : List ℕ := [1999995351925394,2000006713555153,2000004349972973,
  1999992422367897,1999998395115817,2000005839837730,1999996363176312,1999993748245650,
  2000004597840777,2000000761923320,1999991606168842,1999998397061459,2000003882396221,
  1999996100092513,1999996549596181,2000006397912951,2000001402380862,1999993558343849,
  2000002007238804,2000007982949790,1999998810200709,1999995077058900,2000003327777646,
  2000001608106074,1999993689161351,1999998542132132,2000003510160792,1999994999368264,
  1999989455128073,1999998085852520,2000002318627444,1999995554071201,1999997944302424,
  2000007926475612,2000006029034667,1999997560899733,1999999099406479,2000004344201016,
  1999999095219504,1999993721253050,2000000237922114,2000004471253752,1999998287359973,
  1999995921879479,2000002391160142,2000004272645621,1999997564862220,1999996643096077,
  2000003623359415,2000002972554515,1999995828816954,1999997099463521,2000004150323364,
  2000003499191912,1999997217297738,1999998769044495,2000005895725563,2000003792536325,
  1999995853428005,1999996945354997,2000003460513678,2000002466116711,1999996905241843,
  1999998835712785]
private def pvn_w0_5_p4 : List ℕ := [2000005727897610,2000003349961643,1999993847099542,
  1999994516543754,2000005002802701,2000007384351634,1999998313814891,1999993501269207,
  2000000804948797,2000007589746628,2000002506142691,1999995657805868,1999999774181051,
  2000006782036814,2000003556261970,1999994931163981,1999994295290394,2000001847002416,
  2000004701193712,1999998036154673,1999993633570676,1999999426174697,2000005718956436,
  2000002715542436,1999996233451918,1999996571976739,2000002515993931,2000003969820765,
  1999998141103930,1999994992775734,2000000903170899,2000006953115489,2000003398191104,
  1999995338170905,1999994205409204,2000001011239895,2000005403722852,2000000512145707,
  1999993953175201,1999997432510733,2000007928929009,2000010775938029,2000001117650200,
  1999990998743948,1999993514238423,2000006257312562,2000013454707434,2000005092513863,
  1999990596235621,1999987411488086,1999998720195530,2000010660441573,2000010190276067,
  1999999201420874,1999990939944709,1999994711636236,2000005094517556,2000008868216990,
  2000001835645513,1999993167395912,1999992919331617,2000000730857640,2000007488388192,
  2000005253955193]
private def pvn_w0_5_p5 : List ℕ := [1999995803077756,1999989352727682,1999993106283378,
  2000002831065348,2000008326587512,2000004802551137,1999996583703938,1999992001934943,
  1999995829608859,2000004601400831,2000009502993617,2000005609754813,1999997072340304,
  1999992040472971,1999994516827577,2000001779957696,2000007231590094,2000005517971886,
  1999997471868489,1999990224360843,1999990618778954,1999998707286186,2000008335726490,
  2000012570501223,2000008171569305,1999997557389535,1999987952062750,1999986551914253,
  1999994674119317,2000006876749781,2000015549435383,2000015652563810,2000006688568433,
  1999992950841502,1999981868717279,1999979655161250,1999987235071630,2000000375292302,
  2000013004980122,2000019923401384,2000018162180153,2000008298400736,1999994725780521,
  1999983269155532,1999977920025056,1999979760866835,1999987836520139,1999999681724010,
  2000011467597986,2000019336146195,2000021341182682,2000017795344947,2000009976028583,
  1999999317097394,1999987747026259,1999977604585413,1999970481221376,1999966513129286,
  1999965131521191,1999966022331925,1999968927116356,1999973011040270,1999977263598028,
  1999981717945393]
private def pvn_w0_5_p6 : List ℕ := [1999988132097129,2000000039181347,2000023626583771,
  2000070314011794,2000160235474920,2000325682242171,2000614935718518,2001097442165761,
  2001869969540861,2003061977612419,2004838628119463,2007400936940120,2010982718060413,
  2015843029734471,2022252420185789,2030472422179297,2040729583832102,2053186371080033,
  2067911352311368,2084851218753667,2103808015652015,2124425742276019,2146190088409472,
  2168443331471111,2190414228103195,2211261012079522,2230124427695593,2246186601103341,
  2258730325605023,2267192532399310,2271206016636260,2270625020702240,2265532496671460,
  2256229052257442,2243205354526770,2227101166092248,2208655346409832,2188651974526893,
  2167867958778978,2147026900019930,2126762677914608,2107594610545714,2089914511256625,
  2073984780244218,2059945857031652,2047830848017908,2037584869003343,2029086605266696,
  2022169813240879,2016642948182391,2012305712657305,2008961950692043,2006428843986819,
  2004542735433811,2003162108440444,2002168325504322,2001464723610133,2000974614128882,
  2000638661467662,2000412027097544,2000261569900240,2000163297561348,2000100176026506,
  2000060332775451]
private def pvn_w0_5_p7 : List ℕ := [2000035639214425,2000020627765693,2000011686660889,
  2000006474765515,2000003504799830,2000001852071666,2000000954786238,2000000479914461,
  2000000235100260,2000000112221288,2000000052194799,2000000023660541,2000000010460012,
  2000000004514412,2000000001905077,2000000000787802,2000000000320152,2000000000128302,
  2000000000050898,2000000000020059,2000000000007874,2000000000003079,2000000000001194,
  2000000000000456,2000000000000167,2000000000000056,2000000000000014,2000000000000002]
private def pvn_w0_5 : List ℕ := pCat pvn_w0_5_p0 (pCat pvn_w0_5_p1 (pCat pvn_w0_5_p2 (pCat
  pvn_w0_5_p3 (pCat pvn_w0_5_p4 (pCat pvn_w0_5_p5 (pCat pvn_w0_5_p6 pvn_w0_5_p7))))))
private def pvn_w0_6_p0 : List ℕ := [1999999986020355,1999999642314883,1999999684117868,
  2000000170176642,1999997368255975,1999998633136859,2000000082688858,2000001154073705,
  1999999652917235,1999999299168507,2000000279109079,1999999597894442,1999999360839041,
  1999999013182843,1999999353521186,1999998727168544,2000002398579370,2000000521460325,
  1999997602341040,2000000624337457,1999999845319050,2000002017562068,2000000673317411,
  1999998965086133,1999999305967593,1999998612723906,2000000248190003,2000001017713342,
  2000000541299574,1999999431843132,2000000675530151,2000000225793897,1999999552198344,
  1999999112787634,1999999800084434,1999999994841736,2000001347176895,1999999830880766,
  1999999982399394,1999999465114519,1999999164439171,2000000429400498,2000002613415817,
  1999999046808638,1999997847885489,1999999529453883,2000000108308389,2000001378857062,
  2000001776011213,2000000026102542,1999998337597042,1999998763057813,1999999603540356,
  2000002436060551,1999999876022122,1999997181361012,2000001109322930,2000002402249596,
  2000000514299744,1999998220246249,1999998739541930,2000000697878251,1999999348466528,
  2000001301807895]
private def pvn_w0_6_p1 : List ℕ := [1999999699017813,1999999861392496,2000000132729984,
  2000000040623835,2000000824059747,1999998881796044,2000001424153866,1999998724225199,
  1999999320907504,1999998953164088,2000000850748225,2000001996636476,2000000205644148,
  2000000130634621,1999998429590813,2000000634617496,1999997701323579,2000001586877430,
  2000000229856387,1999999625686858,2000002174767236,1999996584393518,2000004101453710,
  1999994342792421,2000006637951449,1999992872997160,2000008306271983,1999991606185989,
  2000008305769796,1999990930255013,2000006215758745,1999996103496556,2000001714470631,
  2000003248456200,1999995445885240,2000005547095897,1999994632729013,2000004214441099,
  1999997350581252,1999999351027218,1999999303373740,1999996329247584,2000005927341503,
  1999996621307437,2000005320470127,2000001514805733,1999996461020446,2000003881383322,
  1999993437220575,2000001874070839,2000000045576488,1999995055181443,2000006147906635,
  1999996774636091,2000000270573139,2000003363589648,1999995018731837,2000003702976426,
  1999999965971314,1999999105571345,2000004259638679,1999995675947504,2000002223261305,
  2000003061685032]
private def pvn_w0_6_p2 : List ℕ := [1999996415395678,2000004805084111,1999998198549090,
  1999995011925997,2000003381442089,1999995377381153,1999998069310094,2000002704630217,
  1999993013722714,1999998786967274,1999999572646856,1999993032127035,2000004398512242,
  2000003201387297,1999997390632642,2000007594489511,2000002593909707,1999999610729565,
  2000010851177788,2000002438714659,1999999511401789,2000012480387833,2000005084353167,
  2000001132154259,2000009758946976,1999998774042732,1999993746469658,2000004290309007,
  1999998877616012,1999998596738871,2000011581135323,2000007269048495,2000004412615878,
  2000013516387770,2000005715535935,1999997445373566,2000004949799758,2000001519669650,
  1999995000344091,2000003075028896,2000003573181813,1999997104433864,2000000639354096,
  1999999839807770,1999994483254698,2000000466915835,2000003970622285,1999999720436633,
  2000001616817343,2000002400257613,1999997688850506,2000002573475551,2000005101706923,
  1999997110168031,1999997549191560,2000005413286437,1999999526752221,1999997254643066,
  2000004355931426,2000000031959679,1999991618348057,2000001347471491,2000005655283495,
  1999993272663044]
private def pvn_w0_6_p3 : List ℕ := [1999994051455087,2000004315019347,1999998625341429,
  1999992436485981,2000004368059756,2000007177493397,1999996126086732,1999998566000433,
  2000006157461341,1999998699305061,1999993197546287,2000002786059430,2000003404551108,
  1999993931575200,1999997540002287,2000003637340223,1999996088449891,1999992248262329,
  2000002885162649,2000005031567513,1999994746030618,1999996619114490,2000005517131779,
  2000001998071935,1999996695071075,2000002731140007,2000005383883368,1999996131927431,
  1999994981116512,2000004491901014,2000002861882622,1999993373535495,1999994658542347,
  2000000585804954,1999996024516441,1999990556397999,1999998296850935,2000005590636488,
  2000000960972408,1999998960722706,2000005116169251,2000005238800294,1999997208258041,
  1999995780506878,2000002559268831,2000002133031237,1999995435380046,1999997626100054,
  2000004190726123,2000001662648147,1999995958559873,1999999028616377,2000004981904300,
  2000001453803775,1999994986411816,1999998713342474,2000004683615083,2000000712066789,
  1999995574528779,2000000112134215,2000006272641068,2000002924969587,1999996576759801,
  1999999302890636]
private def pvn_w0_6_p4 : List ℕ := [2000004716357093,2000000401337939,1999994239627784,
  1999999289857350,2000007606677010,2000004401845410,1999994225968780,1999993781747928,
  2000003788296187,2000007007775303,1999998523480370,1999994131302146,2000000977500435,
  2000006235164829,2000001345164385,1999995696661739,1999999758478403,2000007263016659,
  2000005169249205,1999996350156709,1999995066886940,2000002024750008,2000004325499368,
  1999998182356121,1999993815583703,1999998224337135,2000004550674499,2000002906332259,
  1999996553678791,1999996715782374,2000003065351290,2000004367597584,1999998019850674,
  1999994070498101,1999999112264643,2000006432460282,2000005402466035,1999997128444597,
  1999993880401943,2000000439603548,2000006029414606,2000001257254134,1999992843237400,
  1999993675406120,2000004571472810,2000012389063232,2000006368770476,1999993223042050,
  1999989980175856,2000001321397198,2000012932976881,2000010414324396,1999996816390932,
  1999987709537076,1999992939688442,2000005800836258,2000011046094702,2000003372024515,
  1999993412479550,1999993255973436,2000001829070986,2000008184621100,2000005018130489,
  1999996112878461]
private def pvn_w0_6_p5 : List ℕ := [1999991831027568,1999997399520630,2000006278417341,
  2000007761433234,1999999955946961,1999991356934906,1999990613638711,1999998052610365,
  2000006242483555,2000007118110649,1999999970087984,1999992661606402,1999993171484885,
  2000000856662505,2000007953080838,2000008041884252,2000001374977756,1999993921159719,
  1999992453189755,1999998469509902,2000006101298240,2000007684833151,2000001499456235,
  1999992908376118,1999988981653823,1999993152573420,2000003085106863,2000011762733243,
  2000012269712009,2000003728995362,1999992333345664,1999986072112892,1999988960391670,
  1999999349858295,2000011301380430,2000017475096868,2000013487752680,2000001283449524,
  1999987826055930,1999980151626233,1999981648831939,1999991479489738,2000005306579146,
  2000016722489628,2000020303438384,2000014770598618,2000003193962120,1999990424946047,
  1999980858570168,1999977670758273,1999982059854550,1999992314955832,2000004461469257,
  2000014557893841,2000020288427002,2000020703808759,2000015673570659,2000006255919270,
  1999994851824581,1999984050779641,1999975321588522,1999969099069239,1999965678483460,
  1999965294282012]
private def pvn_w0_6_p6 : List ℕ := [1999967417346778,1999970729566581,1999974131190411,
  1999977505945567,1999981532404022,1999987627049443,1999999301719819,2000024674261957,
  2000079110597091,2000188085914277,2000391445746512,2000749525852410,2001349977637767,
  2002313696875914,2003799114688740,2006004551895418,2009167452509388,2013558290108532,
  2019467323367262,2027184004312483,2036970266281154,2049029401921956,2063472524255736,
  2080285611216392,2099301569476872,2120182385878171,2142415536993095,2165326895100425,
  2188110396597344,2209873128759986,2229692903408108,2246683524810026,2260061211587786,
  2269204828013696,2273703221270484,2273384799007087,2268326808716219,2258844028126046,
  2245458591630656,2228854517203842,2209822071897434,2189198096224158,2167808466883035,
  2146417963100706,2125691214247648,2106166611932341,2088243448773100,2072181266141403,
  2058109457224091,2046044543208402,2035912222981062,2027571321949072,2020837129819879,
  2015502238943186,2011353728668233,2008186232972677,2005810970682211,2004061171965012,
  2002794520695620,2001893295429176,2001262876679464,2000829225604872,2000535846807224,
  2000340637550002]
private def pvn_w0_6_p7 : List ℕ := [2000212908791914,2000130752342706,2000078834189061,
  2000046623524020,2000027021790654,2000015333024831,2000008510210783,2000004616008495,
  2000002444857367,2000001263539185,2000000636807879,2000000312827878,2000000149740129,
  2000000069830079,2000000031728349,2000000014050644,2000000006068378,2000000002558781,
  2000000001054967,2000000000426169,2000000000169113,2000000000066121,2000000000025550,
  2000000000009783,2000000000003714,2000000000001397,2000000000000516,2000000000000182,
  2000000000000058,2000000000000014,2000000000000002]
private def pvn_w0_6 : List ℕ := pCat pvn_w0_6_p0 (pCat pvn_w0_6_p1 (pCat pvn_w0_6_p2 (pCat
  pvn_w0_6_p3 (pCat pvn_w0_6_p4 (pCat pvn_w0_6_p5 (pCat pvn_w0_6_p6 pvn_w0_6_p7))))))
private def pvn_w0_7_p0 : List ℕ := [2000000064416393,1999999873480388,1999999210431672,
  2000001019172749,1999999028432771,1999998086721695,1999998067674489,2000000050307202,
  2000000955794198,1999999634313604,1999999797875410,1999999843869274,2000000288142306,
  1999998865908326,2000000522227786,1999998552490998,1999997369852691,2000002157248812,
  2000000367329540,2000000177715720,1999999134109876,1999998706375133,2000001139095003,
  2000001024785348,2000001031382981,2000000098810121,1999999128936874,1999998220112359,
  2000000146910228,2000000614302695,2000000211724522,1999999814947757,2000000839569383,
  2000000006868451,2000000562323839,1999999101274559,1999999113785003,1999999942448754,
  2000000607183755,1999999817042893,2000001503800718,1999999770499319,1999997700772161,
  2000000273578698,2000001743033684,2000000782560515,1999999670883772,1999998964726037,
  1999998068823774,2000000332075912,2000000920652237,2000001736226030,2000001692729294,
  1999997316213784,1999998161610135,2000001622130822,2000001202166888,1999999029690535,
  1999997505662345,2000001808667035,2000001187344427,2000000697795596,1999999906500610,
  1999998558764822]
private def pvn_w0_7_p1 : List ℕ := [1999999989195358,1999999017328342,2000001644622351,
  1999999037905166,2000000365300429,2000000209483621,1999999918991912,2000000225928138,
  1999999544253187,2000001649677617,1999999227928238,2000000096254713,1999997121523724,
  2000000904087075,2000001082363825,1999999301045990,2000003906871740,1999995832521501,
  2000004664990987,1999992726846432,2000006821709814,1999991999521560,2000008870202942,
  1999991964372078,2000008269281242,1999993047901680,2000004455265626,1999998283580751,
  1999998021836700,2000004831646131,1999994525577883,2000006102357245,1999995299704642,
  2000001527538066,1999998852786251,1999998633126157,2000003651617891,1999996557334977,
  2000004891978266,1999996239129558,2000001077877709,2000003735028200,1999994569755568,
  2000004028664703,1999995471382409,1999998147261424,2000003431199849,1999995590172695,
  2000006735473091,2000001045979895,1999997446226216,2000005006914203,1999995153430612,
  1999999690276440,2000000864239645,1999995180028216,2000003559662456,1999998662602817,
  1999999171620101,2000004040033960,1999994999900742,2000001613839531,2000003353527302,
  1999995864134386]
private def pvn_w0_7_p2 : List ℕ := [2000004264834619,2000000083555643,1999995980478542,
  2000005613491235,1999999294602512,1999999078671612,2000005060434844,1999995220313701,
  1999998565237545,2000002946341902,1999993637648000,2000000726065978,2000002479602772,
  1999991617377830,1999999157978327,1999999702527224,1999992124368070,2000004027299833,
  2000003923221613,1999994402945251,2000005951311653,2000006991144330,1999997486972452,
  2000006557188092,2000006744549006,1999998384051315,2000008714340409,2000010690908839,
  2000000845513283,2000006148270915,2000005059832833,1999993519225133,1999999258491781,
  2000003842813288,1999996735077836,2000003794038625,2000012292331826,2000006093012611,
  2000006641316095,2000010556382402,2000002655024272,2000000089793744,2000003319522895,
  1999999136788605,1999999072154880,2000004950078995,2000000424072617,1999997157029535,
  1999999971903903,1999997568964391,1999996573281304,2000005109439751,2000002254291358,
  1999995555544275,2000002205902382,2000006002166520,1999997567215425,1999999687104439,
  2000006093820916,1999997373697128,1999995627581309,2000007098258540,2000004368750014,
  1999992277083507]
private def pvn_w0_7_p3 : List ℕ := [1999998864206006,2000006255853687,1999996029130084,
  1999994455152131,2000004305779492,2000000156421022,1999990694299883,1999998372192338,
  2000004937327552,1999996770266435,1999997654478823,2000006891878677,2000002538879440,
  1999994700702878,2000000788333016,2000004729690834,1999995667862102,1999995723859148,
  2000005264262762,2000001092770437,1999991687621055,1999996662117416,2000003953841454,
  1999998122494793,1999994464247510,2000002287987087,2000002691958570,1999995265770742,
  1999998998388368,2000007246385583,2000002697452056,1999994695232775,1999999510223763,
  2000005590516010,1999999259089111,1999995205654047,2000001466851075,2000001790770288,
  1999993127524106,1999991405730152,1999998404232503,1999999493683794,1999995043282011,
  1999999371228820,2000007260463162,2000004052660256,1999997525913200,2000000211593321,
  2000004264287728,1999999633493297,1999994707621548,1999999558835329,2000004382216131,
  1999999045398107,1999995072730414,2000001159146322,2000005124105811,1999999534614565,
  1999995586646469,2000000761208460,2000004660898990,1999998917287436,1999994594629406,
  2000000790674295]
private def pvn_w0_7_p4 : List ℕ := [2000005756479175,2000000661701967,1999996732165596,
  2000002190860318,2000006502929719,1999999976691094,1999992586003410,1999997976474417,
  2000007942974802,2000005423726406,1999995171715093,1999994571498702,2000003092835966,
  2000005558004815,1999998574895710,1999994861903518,2000001055544209,2000006016959389,
  2000000621629483,1999994695116325,1999999214311618,2000006869037766,2000005547537871,
  1999998102231405,1999996358360314,2000002210830005,2000004937038942,1999998955893408,
  1999993770217237,1999997779312194,2000003818584635,2000002099922897,1999996376713002,
  1999996615048993,2000002967600536,2000005510856052,1999999277725284,1999993105410699,
  1999996976643941,2000005632060865,2000006204441669,1999998326210803,1999994113582599,
  1999999742868715,2000006802673748,2000003997050178,1999993445655520,1999989670674445,
  1999999739533461,2000011734245976,2000010294889131,1999997390173218,1999989258325870,
  1999995871778987,2000009402792031,2000013609765999,2000003204725376,1999990597474373,
  1999990346425645,2000001156373772,2000009177968150,2000005868106627,1999996599689576,
  1999992786518278]
private def pvn_w0_7_p5 : List ℕ := [1999998794755761,2000007115465305,2000007257672408,
  1999998870714416,1999992174782493,1999994931341509,2000003592513972,2000008452044918,
  2000004192138897,1999994815250352,1999989757748838,1999994293645792,2000003450260113,
  2000007433678165,2000002663089498,1999994862377279,1999992051016226,1999996943263453,
  2000005177312155,2000009134142857,2000004854080357,1999996429321206,1999992145651980,
  1999995857491284,2000003598750929,2000008180085058,2000005403119218,1999996914093125,
  1999989254485826,1999989208840813,1999997736500932,2000008501530260,2000013350285059,
  2000008921209928,1999998299165845,1999988324085036,1999985660735716,1999992751896612,
  2000005504648987,2000015705838713,2000016978249047,2000008742637705,1999995463529130,
  1999983697000168,1999979331937910,1999984871933662,1999997609117056,2000011031982726,
  2000018943580557,2000018522941582,2000010451625611,1999997878106827,1999985596949220,
  1999978486400767,1999979075556294,1999986417232816,1999997419893525,2000008772449183,
  2000017570726622,2000021386226230,2000019091677133,2000011649943402,2000001410690882,
  1999990542500087]
private def pvn_w0_7_p6 : List ℕ := [1999980445041839,1999972302391427,1999967251788851,
  1999965641939372,1999966638366881,1999968989982185,1999971952652651,1999975209633100,
  1999978344696621,1999981279529948,1999985895147214,1999997866686403,2000028423316761,
  2000097162541598,2000236986456603,2000500731272499,2000968146163918,2001752438666183,
  2003006267312457,2004926391285395,2007754778784662,2011773558519524,2017292295045747,
  2024627516502391,2034075131394161,2045876703837722,2060181590722791,2077008823898195,
  2096214223052435,2117468415719597,2140250220341466,2163858080640011,2187440528511171,
  2210044819294486,2230680543051110,2248392395147520,2262334277972078,2271836336379485,
  2276457526030048,2276018334335654,2270610673273859,2260584428017946,2246512631378846,
  2229139620715576,2209318437656640,2187944674583094,2165893715065845,2143967025845339,
  2122851293963737,2103092244123261,2085083221618369,2069067195975086,2055149753891069,
  2043319942257568,2033475549416894,2025449595999762,2019035376817872,2014008195748672,
  2010142776893044,2007226062618892,2005065641735972,2003494381056179,2002371997007866,
  2001584348264348]
private def pvn_w0_7_p7 : List ℕ := [2001041194703992,2000673079271989,2000427866841145,
  2000267335475976,2000164077964206,2000098850398284,2000058410230725,2000033822210388,
  2000019174535690,2000010633250858,2000005762995559,2000003050136700,2000001575291712,
  2000000793408592,2000000389492627,2000000186292858,2000000086792212,2000000039384202,
  2000000017409259,2000000007499392,2000000003150380,2000000001291974,2000000000518012,
  2000000000203449,2000000000078451,2000000000029772,2000000000011146,2000000000004122,
  2000000000001503,2000000000000534,2000000000000181,2000000000000056,2000000000000013,
  2000000000000002]
private def pvn_w0_7 : List ℕ := pCat pvn_w0_7_p0 (pCat pvn_w0_7_p1 (pCat pvn_w0_7_p2 (pCat
  pvn_w0_7_p3 (pCat pvn_w0_7_p4 (pCat pvn_w0_7_p5 (pCat pvn_w0_7_p6 pvn_w0_7_p7))))))
private def pvn_w0_8_p0 : List ℕ := [2000000058028808,2000000202587432,1999998846775596,
  2000000787473899,2000000185918940,1999999127118358,1999997787605458,1999998231625722,
  2000000406051170,2000000263778474,2000000106114006,1999999280829460,2000000833402519,
  1999999175798178,1999999503712050,2000001611499245,1999997129493550,1999998643665751,
  2000000188889191,2000000579762375,2000001243404879,1999998969185694,1999998974867134,
  1999999739530094,2000000828700838,2000000867929120,2000001520671588,1999999771147039,
  1999998618874211,1999998857380620,2000000527240858,1999999690624701,2000000457344814,
  1999999917086030,2000000444201289,2000000724068083,2000000435075268,1999998626432934,
  1999999963275354,1999999790147637,1999998972731743,2000001465996983,2000001481711209,
  1999998970901864,1999998368852751,2000000272038546,2000000479572550,2000001660226964,
  2000000418191736,1999998513312974,1999999399804832,1999998186275488,2000000050223999,
  2000003365836969,2000001089527865,1999998675434058,1999997327178172,2000001834353082,
  2000001143943921,1999998587713391,1999999169482128,1999999085653307,2000002013100039,
  2000000108165616]
private def pvn_w0_8_p1 : List ℕ := [2000001524721671,1999998920996067,1999998996419460,
  2000000144364315,1999999620857644,2000000619838411,1999999011049264,2000001441919789,
  1999999007893971,2000000751017196,1999999154311748,2000000259348298,2000003319654306,
  1999995774199865,2000003788828592,1999993015414906,2000006635926161,1999992756132307,
  2000009433247650,1999992383669417,2000008398250848,1999992217631839,2000004764242961,
  1999996467643991,1999999564818193,2000003855887976,1999994671999087,2000006511426668,
  1999994830494440,2000003116479274,1999998735911139,1999998703797813,2000002831011555,
  1999996832934691,2000004775867275,1999996005984164,2000001080771579,2000000363294251,
  1999995377836284,2000006408553037,1999996410034284,2000000618321135,2000002886624656,
  1999995643983597,2000005782926747,1999997758125889,1999997958205519,2000003406480511,
  1999992906847999,2000001267902637,2000001887155094,1999997797217490,2000005956296072,
  1999999071025781,2000000148393411,2000002952688775,1999994821154690,2000001529384225,
  1999999424325884,1999995061145398,2000005071324656,1999998851303951,1999997151931757,
  2000004529135840]
private def pvn_w0_8_p2 : List ℕ := [1999996247206909,1999999875930213,2000005122619542,
  1999995979456919,2000001463896350,2000002617219267,1999995255670354,2000004522191440,
  2000002943221503,1999995593498676,2000004642659302,1999999700063864,1999993295038138,
  2000004083905939,1999999206353766,1999994202234246,2000004291880334,1999996337609499,
  1999990401350071,2000003240336369,1999999250221427,1999993729444822,2000005061241088,
  2000002096954453,1999997280966437,2000007984217079,2000004629351453,1999997406607978,
  2000006936114388,2000006771284638,2000001111496424,2000010221764107,2000009703085292,
  1999999022651447,2000002416498419,2000003330147331,1999994419948181,1999998234550311,
  2000004547699540,2000002162018105,2000006083842350,2000011656928660,2000006519476772,
  2000006178435714,2000007310143167,2000000757711003,1999998580587291,2000004028727760,
  2000000698575512,2000000019479280,2000004451207590,1999998599862473,1999992676102742,
  2000001453864210,2000004156510110,1999995412148574,1999999755289924,2000005830521654,
  1999998260689909,1999997635864988,2000007862472965,2000002500913697,1999992204439905,
  2000002037984179]
private def pvn_w0_8_p3 : List ℕ := [2000008204371547,1999997352434121,1999996110908904,
  2000005590720960,2000000774714254,1999992748784468,2000001582489061,2000005075043662,
  1999994537816448,1999994421407482,2000002461421812,1999998400941121,1999993016786586,
  2000002062099305,2000006257030064,1999997333746290,1999998071082815,2000005982544055,
  2000000956984799,1999993308411700,2000000103768887,2000006307409315,1999997773537722,
  1999993530142978,2000001070549211,2000000794753368,1999994044187549,1999997656447698,
  2000004199767395,1999998872291899,1999993134066882,2000001031278558,2000006995765880,
  1999999650331198,1999996351552920,2000003088128435,2000003756334873,1999996965320072,
  1999997598137937,2000004429631005,2000001895152435,1999993583388129,1999994884432416,
  1999999351017534,1999995098137945,1999991842043046,1999998884407583,2000005372932414,
  2000001802488910,1999998162607809,2000003171494269,2000005513786825,1999998369112074,
  1999995289582359,2000001512555674,2000003601272830,1999997396187942,1999995334311569,
  2000001886376052,2000004670374251,1999998291793093,1999995838998051,2000002529457826,
  2000004631477449]
private def pvn_w0_8_p4 : List ℕ := [1999997651138498,1999994987097048,2000001410318281,
  2000004763373611,1999998992667784,1999995826615174,2000003233154569,2000008414074227,
  2000000477432367,1999992181249724,1999997453461093,2000006935986842,2000005279918653,
  1999996401049522,1999995354089710,2000002986430038,2000005105775327,1999997980724007,
  1999994976585547,2000001606065388,2000005870817486,2000000404932550,1999994613941394,
  1999998244882860,2000005863840509,2000005680344542,1999998642708065,1999996953540881,
  2000003010656613,2000005461334321,1999999477906334,1999994491962380,1999997748854934,
  2000003285215086,2000002021820887,1999995967392519,1999995562420429,2000002805280164,
  2000006559981649,2000000227446061,1999993111579945,1999995882283517,2000004393399460,
  2000006443004561,1999999324366900,1999993662277191,1999998609042015,2000007636431328,
  2000006614378221,1999995011924560,1999988101671634,1999995799143104,2000009180564057,
  2000012148247346,2000001250663839,1999989940817591,1999992515679399,2000006078100224,
  2000013884967626,2000006831714230,1999994127602381,1999990325598288,1999998150651376,
  2000007261111679]
private def pvn_w0_8_p5 : List ℕ := [2000007012492710,1999998450745579,1999992764891730,
  1999997226582730,2000005966105847,2000008001347369,2000001082889576,1999993366723260,
  1999993365387830,2000001102071586,2000008263436950,2000006679800421,1999997502868950,
  1999990422945104,1999992617599747,2000000990002761,2000006636330566,2000004377434625,
  1999996911241982,1999991786758021,1999994530003301,2000002969943442,2000008870554054,
  2000006531729272,1999998661983646,1999992900467111,1999994228026858,2000001276270913,
  2000007883072820,2000007761154947,1999999962887334,1999990618006715,1999987792874753,
  1999994118160494,2000004920737148,2000012578720955,2000011816944221,2000002722304400,
  1999991068736165,1999985018657738,1999989140047593,2000000821883399,2000012637362174,
  2000017703186460,2000013186309282,2000001097333083,1999987491665612,1999979673264752,
  1999981820079420,1999992431931881,2000005957905552,2000016415995684,2000019712912155,
  2000014520295019,2000002881504446,1999989771737591,1999980602430900,1999978381827565,
  1999983051373458,1999992694399410,2000004466757406,2000014860428445,2000020628506100,
  2000020331376599]
private def pvn_w0_8_p6 : List ℕ := [2000014764963623,2000005761245111,1999995018290914,
  1999984148959614,1999974992044624,1999969004561751,1999966396197801,1999966335492408,
  1999967969981315,1999970823758158,1999974240371329,1999977106714246,1999978735421195,
  1999980270397283,1999985793796998,2000003728974941,2000049972082800,2000153218196405,
  2000361583113673,2000749599479906,2001425525254785,2002538853980348,2004286524712356,
  2006915085540285,2010716296584145,2016014901852087,2023148217277729,2032437475000232,
  2044151528842788,2058465322363391,2075417816840249,2094875492203192,2116507396916981,
  2139776523083720,2163950788036552,2188135216909544,2211324604297984,2232472883803894,
  2250572368075775,2264734022970659,2274259628560989,2278697876480448,2277878551440970,
  2271921477976163,2261219727300961,2246399564096525,2228262406214655,2207716086788616,
  2185703465641451,2163135853525055,2140837126701889,2119502344195781,2099672577209967,
  2081725766074098,2065881841750497,2052219162614561,2040698613800339,2031191561691776,
  2023508225167361,2017423779706228,2012700441011024,2009104676604906,2006419428288441,
  2004451742071200]
private def pvn_w0_8_p7 : List ℕ := [2003036507667469,2002037150003910,2001344136030314,
  2000872097516701,2000556251844588,2000348651810070,2000214634972861,2000129693732954,
  2000076864336271,2000044643945695,2000025389652593,2000014126226720,2000007682392236,
  2000004080482943,2000002115158885,2000001069295560,2000000526896128,2000000252942856,
  2000000118261471,2000000053840003,2000000023867154,2000000010304158,2000000004334413,
  2000000001777751,2000000000711705,2000000000278509,2000000000106724,2000000000040127,
  2000000000014835,2000000000005400,2000000000001930,2000000000000674,2000000000000225,
  2000000000000069,2000000000000017,2000000000000002]
private def pvn_w0_8 : List ℕ := pCat pvn_w0_8_p0 (pCat pvn_w0_8_p1 (pCat pvn_w0_8_p2 (pCat
  pvn_w0_8_p3 (pCat pvn_w0_8_p4 (pCat pvn_w0_8_p5 (pCat pvn_w0_8_p6 pvn_w0_8_p7))))))
private def pvn_w0_9_p0 : List ℕ := [1999999968484342,2000000592877149,1999998790610512,
  2000000123379235,2000000526058920,2000000269933637,1999999004884948,1999997448373655,
  1999998883780903,1999999689905768,2000000822873488,1999999147799577,2000000198488471,
  2000000892010603,1999997857068959,2000001393594818,2000000560603956,1999998237639064,
  1999998687192316,1999998585988359,2000000755389345,2000001064461946,2000000131175789,
  1999998813463530,1999999581057538,1999999511660928,2000000656102479,2000001429218224,
  2000001532572254,1999998941011839,1999999273988890,1999999207870808,1999999892721713,
  2000000009472314,2000000234445213,1999999396002811,2000001088075450,2000001039553603,
  1999999178585914,2000000265230594,1999999910225809,1999998443580175,1999999390543244,
  2000002027039567,2000000623241996,1999999643293508,1999999125644625,1999998541188305,
  2000001305451882,2000001122588995,2000000146118262,2000001123646298,1999998152122312,
  1999997929152906,1999998840348526,2000003217703670,2000002351444485,1999997843296686,
  1999999398282656,1999999662947973,2000002076319265,1999998813923246,1999999355638399,
  1999999128982991]
private def pvn_w0_9_p1 : List ℕ := [1999999536746950,2000001896861940,2000000407738451,
  2000000987552269,1999998227028330,2000000739620771,1999999049467516,1999999888801456,
  2000000822681614,1999997537006813,2000005065815599,1999993819474399,2000005916934386,
  1999993066226732,2000009183736401,1999992114095162,2000008122160673,1999991323056846,
  2000005218806115,1999995359540309,2000001658613887,2000002958753980,1999996130554106,
  2000006741373413,1999993567165457,2000003648152872,1999997488054306,1999999300370494,
  2000002473611422,1999996759275219,2000004369092582,1999996418552748,2000002492888581,
  1999999486487410,1999996762402486,2000005287277384,1999995365969406,2000003239192866,
  2000001584253118,1999994526712126,2000004273943093,1999996352223152,2000000660222752,
  2000003642045872,1999994548310294,2000004283273600,2000000140430505,1999997365169879,
  2000005539133940,1999996990596178,1999999148317668,2000000461367270,1999994447782366,
  2000002938796646,2000000154612496,1999998833245640,2000006403244032,1999997875844697,
  1999999823618263,2000004327271105,1999994143186129,1999999661430993,2000002071378483,
  1999994976636824]
private def pvn_w0_9_p2 : List ℕ := [2000003355609321,2000001238542097,1999994948459729,
  2000003842666707,1999999623974427,1999996938092843,2000005999213149,1999998096951437,
  1999996350607122,2000005893762449,1999997848657562,1999998267640273,2000007583295150,
  1999997574942280,1999997045127346,2000005426713497,1999995193287659,1999996000457010,
  2000006810921595,1999996755547744,1999993472797711,2000002448348085,1999995275780331,
  1999993765618764,2000003713863690,1999997809988355,1999995459273175,2000006411535361,
  2000002917713836,1999998375718334,2000006689116840,2000003824147231,1999998027867113,
  2000007578726726,2000009608069033,2000003407653988,2000007056709740,2000007653082375,
  1999998917572432,1999999532720028,2000000273929411,1999996532641795,2000000435550148,
  2000006826001605,2000004219934408,2000007575715509,2000011849064321,2000005664770980,
  2000002738694691,2000005723311240,2000000236304739,1999997264868859,2000006907849116,
  2000004884427666,1999994410333942,1999998485822123,2000003745582354,1999995880345572,
  1999996328780454,2000006273160702,2000000052497862,1999993327558118,2000004626082612,
  2000008296485478]
private def pvn_w0_9_p3 : List ℕ := [1999996076418184,1999996197061164,2000006821375294,
  2000001624294114,1999995152063736,2000003991328305,2000005313655340,1999995074911189,
  1999996699838343,2000005428991554,2000000248578582,1999993991523377,2000001304672229,
  2000002016573947,1999992562129784,1999995007741641,2000004055008442,2000000529497962,
  1999995037816002,2000002882178471,2000007074676367,1999997180086146,1999994930169964,
  2000003810572153,2000003251058344,1999995977655914,1999998394378555,2000003270172626,
  1999997167730526,1999992702351688,2000000898487584,2000004075064543,1999995348973154,
  1999993858985465,2000002383690678,2000003717092153,1999997492170982,1999998844318433,
  2000005180378937,2000001792979227,1999995507988617,2000000074111785,2000005411853966,
  2000000469069838,1999995805116042,1999999303870885,2000000473676178,1999993293827789,
  1999990414851520,1999998099244734,2000002272540795,1999997869322759,1999998353811842,
  2000005320274884,2000005418101660,1999998170569427,1999996844632080,2000002973434690,
  2000003296726995,1999996117650759,1999995661826433,2000002967090030,2000003484371641,
  1999996827720782]
private def pvn_w0_9_p4 : List ℕ := [1999996667927547,2000003524280126,2000004360559824,
  1999997183179340,1999995275821069,2000002440020798,2000004590861567,1999996901702117,
  1999994478190644,2000003571000756,2000009143429435,2000001618766653,1999993096747489,
  1999996912430180,2000005895593342,2000004827898557,1999996666277074,1999996419175505,
  2000003619403746,2000004494245129,1999997588903687,1999995178989857,2000001462843968,
  2000005953644305,2000000893604176,1999994420492496,1999997505701386,2000005124259109,
  2000004940772659,1999998591554562,1999997618789245,2000003371772583,2000005893645946,
  2000000541574460,1999995125684288,1999997773958240,2000003648185866,2000002221650816,
  1999995241608053,1999994549469755,2000002232113212,2000006919270803,2000001555185539,
  1999993746524954,1999994699529922,2000003277885009,2000006955394380,1999999927562744,
  1999992832894495,1999997274494096,2000007701795976,2000009003525047,1999998000540779,
  1999987990369524,1999991876953423,2000005780427476,2000012935717804,2000004541056861,
  1999991574770225,1999990584991563,2000002416628122,2000012467064129,2000009507934655,
  1999997893191688]
private def pvn_w0_9_p5 : List ℕ := [1999991132536201,1999996177902192,2000005670731093,
  2000007382355683,1999999780037222,1999993250527422,1999995983440565,2000004308474285,
  2000008335572880,2000003409720999,1999994813818424,1999992190235307,1999998867522666,
  2000007443645930,2000008126829691,2000000173997153,1999992080208442,1999991638376312,
  1999998515288507,2000005563151171,2000005704587072,1999998737975137,1999992021663285,
  1999992918463909,2000000715372022,2000007722064969,2000007621073088,2000001025500213,
  1999994012706522,1999992908923846,1999999092353839,2000007150345643,2000009262702492,
  2000002781412057,1999992882798131,1999987555816870,1999990971294137,2000001011259992,
  2000010952129403,2000013598734880,2000006467710663,1999994341406736,1999985833563212,
  1999986706879798,1999996268565339,2000008821660012,2000017216816664,2000016323888252,
  2000006003191848,1999991780121671,1999981492048993,1999980236561272,1999988005852005,
  2000000881647003,2000013243037452,2000019679552289,2000017222516253,2000007128256647,
  1999994142471158,1999983515745364,1999978618330616,1999980608612035,1999988782515027,
  2000000514935964]
private def pvn_w0_9_p6 : List ℕ := [2000011796277390,2000019051790475,2000020741598136,
  2000017191479735,2000009453930813,1999998920147358,1999987620757892,1999977857353499,
  1999971070556952,1999967352908674,1999966189841868,1999967239588899,1999970087378589,
  1999973631465169,1999976340879746,1999977319003574,1999977134858857,1999978309945204,
  1999986764560095,2000015369723696,2000089355771185,2000252695331610,2000575308156062,
  2001161480408271,2002158937212631,2003766334654651,2006236260992098,2009871542885797,
  2015013580073344,2022021709973456,2031242845250619,2042971976855759,2057406628574153,
  2074600737010745,2094424519723687,2116536620818742,2140373879678324,2165162801530865,
  2189954844264675,2213684580797581,2235246045850481,2253579256615365,2267757054361401,
  2277062344659143,2281047135061517,2279566975638504,2272787248633694,2261161113363455,
  2245382468922828,2226320407819564,2204943596927279,2182243462664898,2159164096899604,
  2136544912175189,2115079790851687,2095294177081841,2077539472653889,2062002364592545,
  2048725478597291,2037635142376589,2028572090980844,2021321550968230,2015640088439816,
  2011277650214388]
private def pvn_w0_9_p7 : List ℕ := [2007994167252771,2005570814428207,2003816505980856,
  2002570479376874,2001701927729710,2001107625871637,2000708393611358,2000445083246616,
  2000274596930206,2000166260423322,2000098724639534,2000057447811825,2000032732217692,
  2000018245761379,2000009941783409,2000005290849634,2000002747958112,2000001391915403,
  2000000687170497,2000000330474801,2000000154759013,2000000070549518,2000000031303510,
  2000000013519722,2000000005684876,2000000002328410,2000000000929629,2000000000362185,
  2000000000137882,2000000000051377,2000000000018767,2000000000006726,2000000000002363,
  2000000000000809,2000000000000266,2000000000000080,2000000000000020,2000000000000003]
private def pvn_w0_9 : List ℕ := pCat pvn_w0_9_p0 (pCat pvn_w0_9_p1 (pCat pvn_w0_9_p2 (pCat
  pvn_w0_9_p3 (pCat pvn_w0_9_p4 (pCat pvn_w0_9_p5 (pCat pvn_w0_9_p6 pvn_w0_9_p7))))))
private def pvn_w0_10_p0 : List ℕ := [1999999796699841,2000000910281085,1999999109789846,
  1999999529489192,2000000186396944,2000000559169384,2000000588006511,1999998348223628,
  1999998216468745,1999998100190252,2000000367712745,2000000157722369,1999998608865758,
  2000001880637656,1999999134178081,1999998773190079,2000001239550772,2000000250891856,
  1999999824683360,1999998253410814,1999998318022254,1999999482383327,2000001278209405,
  2000000309957040,1999999874420116,1999999218172982,1999999455704690,1999998965016708,
  2000001412901248,2000001522039361,2000000763185082,1999999507649044,1999999476639175,
  1999998881992373,2000000194937209,2000000225358241,1999998789484052,2000000594407067,
  2000001072279512,1999999932707009,2000000018916038,2000001272146665,1999998921356859,
  1999998250786711,2000000245977582,2000000368510512,2000001610847244,2000000389652103,
  1999997916190399,2000000111093505,1999999543084580,2000000771783726,2000000903643110,
  2000001619596710,1999999998962869,1999995559749691,1999999677394053,2000001305787563,
  2000002914498080,1999999074432960,1999998842771683,2000000611814961,1999999921412640,
  2000001348956253]
private def pvn_w0_10_p1 : List ℕ := [1999998566560375,1999999723843159,1999998143604002,
  2000001160338914,2000001498082165,1999999082758090,2000003169705351,1999994693527227,
  2000006386836473,1999992362256022,2000007010150003,1999992018093598,2000009210917286,
  1999991766081712,2000006326728658,1999994470587097,2000003252875894,2000001240573265,
  1999997355409430,2000005593870876,1999992540401605,2000004518516091,1999996058786747,
  2000000661613181,2000002669348130,1999997665733446,2000004525463313,1999996020906351,
  2000002359362187,1999998316094142,1999998220880532,2000003907897140,1999994929331272,
  2000004474738216,1999999669731703,1999996720592193,2000005184441754,1999994793273304,
  2000001445177045,2000002705505572,1999996344133693,2000005054375121,1999996740127568,
  1999997544376639,2000004527958946,1999995564664723,2000001679007801,2000001839824094,
  1999996187944357,2000003743479875,1999999141888830,1999999866989496,2000004643918334,
  1999995409546388,1999999628261505,2000000943975857,1999993724240645,2000003266684204,
  2000002201716282,1999996706328284,2000005901461596,2000000789270282,1999997107896138,
  2000004209805146]
private def pvn_w0_10_p2 : List ℕ := [1999996231998942,1999996597927792,2000004480694796,
  1999996427722515,1999999168611751,2000004531159528,1999994580962837,1999999778324950,
  2000005733357716,1999995445590049,2000000556554170,2000005082761032,1999994202649263,
  2000000390541103,2000006351433789,1999995803561729,2000001196220375,2000006921000278,
  1999994529236680,1999997103613444,2000005190530410,1999996682196450,1999997981178950,
  2000004006560417,1999994332712691,1999994327201385,2000002652444816,1999995802781511,
  1999993987058617,2000003264933989,1999999500768521,1999997408496349,2000006205506117,
  2000004256331840,1999997600494365,2000003939706949,2000005158538307,2000002368786085,
  2000007312129297,2000009589105928,2000004165874095,2000005719807000,2000004315331047,
  1999996724042506,1999998052927578,2000001536180093,1999998263637738,2000001641912144,
  2000010195692425,2000006676852012,2000005487303084,2000011933571545,2000005822957031,
  1999996184183293,2000003082370083,2000008475470501,1999998827275947,1999998869381315,
  2000005926664841,1999997897854796,1999992657535914,2000003500599225,2000004907430569,
  1999992877079166]
private def pvn_w0_10_p3 : List ℕ := [1999996691002155,2000008162225880,2000001580207584,
  1999995533009380,2000003837189987,2000004525781753,1999995584564874,1999999203174685,
  2000007625933293,2000000580286035,1999994901571776,2000002882350435,2000003491499802,
  1999995440242129,1999998392015688,2000005326131986,1999998682627053,1999991823571597,
  1999999369031681,2000002585216035,1999994305639930,1999995748057220,2000005716122824,
  2000004028013580,1999996056922593,1999999059131278,2000004659909012,1999999209931029,
  1999995996915976,2000003339002322,2000003571311046,1999994323046047,1999994393769298,
  2000002801356646,2000001915759749,1999994108225003,1999995909030267,2000002702216586,
  1999999768644849,1999995618406084,2000001482664204,2000005504161583,1999999593670656,
  1999996207373600,2000001823942373,2000004502442805,1999998903603469,1999997578974525,
  2000003416470668,2000001992514342,1999993091994486,1999991958782249,1999998064712649,
  1999998381415826,1999994254796109,1999997429034963,2000005457004060,2000004791367861,
  1999997708922873,1999998688824598,2000004908731627,2000002575673351,1999995537053207,
  1999996891764584]
private def pvn_w0_10_p4 : List ℕ := [2000003386416156,2000002377482122,1999995794218968,
  1999996824772906,2000004451368060,2000004104309779,1999996175380580,1999996011677927,
  2000003890185083,2000004493512215,1999995852638348,1999993180764763,2000002404139170,
  2000009238216051,2000002679444492,1999994111023395,1999997494664921,2000005250715217,
  2000003549733841,1999996749806337,1999997388935645,2000003932905486,2000004564202954,
  1999997622496460,1999994791895926,2000001328888501,2000006219982293,2000001043176530,
  1999994696141221,1999997490365240,2000004121568671,2000004017677021,1999998470400762,
  1999997461960410,2000003356357885,2000006653517306,2000001289311619,1999995498900842,
  1999998395128804,2000004337571402,2000002583242908,1999995187810454,1999993545882692,
  2000000851197670,2000007082310346,2000003027262122,1999994212589632,1999993812872893,
  2000002671025510,2000007308586233,2000000512343753,1999992359027026,1999995317076686,
  2000006517612982,2000011190469652,2000001803014731,1999988955845007,1999988966922381,
  2000002270474501,2000012217411418,2000006979818457,1999994147901020,1999989761636078,
  1999998741414242]
private def pvn_w0_10_p5 : List ℕ := [2000010281385663,2000011087452268,2000000919597356,
  1999992538067416,1999995443417807,2000004306494804,2000007211951010,2000001077670734,
  1999994031456538,1999994682120554,2000002483593493,2000008504258602,2000005380784725,
  1999996303980079,1999991786622872,1999997018168442,2000005889714900,2000008726070755,
  2000002804009199,1999994151974657,1999991138542446,1999996520126809,2000004485981816,
  2000006392815349,2000000252316107,1999992866425634,1999991978149920,1999998370545511,
  2000006088987332,2000008346014796,2000003141846593,1999995165709734,1999992107731670,
  1999997276266772,2000005917332683,2000009886225181,2000005391729267,1999995738284896,
  1999988112878280,1999988472781382,1999997360738350,2000008766754676,2000014150042265,
  2000009360387128,1999997911181082,1999987695379105,1999985240253134,1999992226126209,
  2000004899165300,2000015809348706,2000018050197162,2000009977672471,1999996261182840,
  1999984301567371,1999979766173157,1999984491794497,1999996321391312,2000009832367723,
  2000018593691430,2000018664813754,2000010627079135,1999998415865100,1999986727731915,
  1999979463401327]
private def pvn_w0_10_p6 : List ℕ := [1999979097341535,1999985809234396,1999997003772330,
  2000008551102119,2000016997820191,2000020629948138,2000018983388961,2000012370075202,
  2000002179238377,1999990855508764,1999980791581090,1999973217022069,1999968340330639,
  1999966206118847,1999966850856445,1999969663835701,1999973176414841,1999975810714516,
  1999976684842778,1999975732739450,1999973936796718,1999975133875511,1999989818293114,
  2000040281893080,2000166778302153,2000435332079495,2000947535622665,2001851037528912,
  2003348037980431,2005699100903713,2009220314524243,2014272083102817,2021237678203789,
  2030490346450719,2042349961540403,2057033118394502,2074602760108904,2094924265632769,
  2117634817417327,2142132290972581,2167588617398577,2192989958508345,2217202093327390,
  2239055102818911,2257438071147887,2271392889350151,2280196341777092,2283421079603671,
  2280968555518615,2273070398596104,2260258788303311,2243310494748345,2223172511429947,
  2200878931957176,2177468739317956,2153912806219805,2131056193576605,2109579277816085,
  2089978680236510,2072566657123492,2057485759695774,2044734390295728,2034198478226255,
  2025684832093133]
private def pvn_w0_10_p7 : List ℕ := [2018952598039930,2013740386399355,2009787761084284,
  2006850739621639,2004711651208599,2003184145514510,2002114373818235,2001379423224479,
  2000884018086399,2000556350807291,2000343705588505,2000208329398504,2000123813914342,
  2000072099563838,2000041105540850,2000022925335571,2000012497313094,2000006653459455,
  2000003456756518,2000001751319658,2000000864676351,2000000415801837,2000000194652209,
  2000000088677980,2000000039305540,2000000016948616,2000000007110358,2000000002902991,
  2000000001154022,2000000000447019,2000000000168899,2000000000062323,2000000000022487,
  2000000000007939,2000000000002741,2000000000000920,2000000000000296,2000000000000088,
  2000000000000022,2000000000000003]
private def pvn_w0_10 : List ℕ := pCat pvn_w0_10_p0 (pCat pvn_w0_10_p1 (pCat pvn_w0_10_p2 (pCat
  pvn_w0_10_p3 (pCat pvn_w0_10_p4 (pCat pvn_w0_10_p5 (pCat pvn_w0_10_p6 pvn_w0_10_p7))))))
private def pvi_w0 : List ℤ := bDc bZ (rPad bZ 513 pvn_w0_0)
private def pvo_w0 : List ℤ := bDc bZ (rPad bZ 513 pvn_w0_10)
private def phbn_w1_p0 : List ℕ := [75032819953730,105956980801289,129579850132325,
  149406010049628,166795086995372,182445437351052,196772533554829,210047476845759,222458849548935,
  234144156516988,245207352711711,255729316955457,265774460097802,275395080788624,284634341966595,
  293528367252976,302107755971713,310398702581573,318423839951948,326202885492898,333753143739708,
  341089902570933,348226749363673,355175826028649,361948036786282,368553218974804,375000284632213,
  381297338746892,387451778715396,393470378537435,399359360519867,405124456685133,410770961637410,
  416303778297171,421727457647381,427046233423926,432264052515801,437384601707187,442411331286219,
  447347475958477,452196073432587,456959980987505,461641890283521,466244340639692,470769730967769,
  475220330525413,479598288628683,483905643444535,488144329967863,492316187273833,496422965124546,
  500466329999080,504447870607379,508369102941088,512231474908110,516036370592153,519785114173776,
  523478973545333,527119163648584,530706849560596,534243149350831,537729136729855,541165843507997,
  544554261880416]
private def phbn_w1_p1 : List ℕ := [547895346553345,551190016724856,554439157932141,
  557643623776191,560804237533685,563921793665004,566997059226468,570030775194137,573023657705875,
  575976399227785,578889669650575,581764117320953,584600370012712,587399035841768,590160704129062,
  592885946214937,595575316228286,598229351813499,600848574818050,603433491943259,605984595360666,
  608502363296177,610987260584057,613439739192639,615860238723500,618249186885741,620606999946859,
  622934083161627,625230831180273,627497628437180,629734849521221,631942859528795,634122014400542,
  636272661242642,638395138633572,640489776917102,642556898482295,644596818031200,646609842834898,
  648596272978518,650556401595799,652490515093738,654398893367830,656281810008392,658139532498399,
  659972322403271,661780435553008,663564122217034,665323627272125,667059190363734,668771046061041,
  670459424006019,672124549056794,673766641425571,675385916811371,676982586527818,678556857626195,
  680108933013992,681639011569132,683147288250083,684633954202022,686099196859226,687543200043854,
  688966144061281]
private def phbn_w1_p2 : List ℕ := [690368205792114,691749558781045,693110373322662,
  694450816544353,695771052486417,697071242179492,698351543719420,699612112339641,700853100481223,
  702074657860607,703276931535180,704460065966738,705624203082934,706769482336779,707896040764283,
  709004013040294,710093531532605,711164726354403,712217725415106,713252654469661,714269637166352,
  715268795093172,716250247822815,717214112956331,718160506165498,719089541233952,720001330097117,
  720895982880983,721773607939766,722634311892488,723478199658520,724305374492119,725115938015986,
  725909990253890,726687629662385,727448953161644,728194056165441,728923032610316,729635974983942,
  730332974352719,731014120388623,731679501395333,732329204333661,732963314846293,733581917281889,
  734185094718531,734772928986564,735345500690828,735902889232323,736445172829293,736972428537781,
  737484732271639,737982158822028,738464781876424,738932674037128,739385906839308,739824550768584,
  740248675278169,740658348805570,741053638788876,741434611682630,741801332973309,742153867194410,
  742492277941164]
private def phbn_w1_p3 : List ℕ := [742816627884885,743126978786950,743423391512452,
  743705926043490,743974641492152,744229596113159,744470847316208,744698451678003,744912464953991,
  745112942089806,745299937232435,745473503741101,745633694197881,745780560418061,745914153460233,
  746034523636140,746141720520281,746235792959271,746316789080970,746384756303388,746439741343353,
  746481790224981,746510948287911,746527260195346,746530769941885,746521520861150,746499555633223,
  746464916291888,746417644231688,746357780214790,746285364377676,746200436237655,746103034699200,
  745993198060111,745870964017522,745736369673726,745589451541853,745430245551384,745258787053504,
  745075110826312,744879251079870,744671241461107,744451115058581,744218904407092,743974641492152,
  743718357754321,743450084093400,743169850872493,742877687921929,742573624543057,742257689511911,
  741929911082737,741590316991407,741238934458693,740875790193429,740500910395538,740114320758944,
  739716046474364,739306112231978,738884542223975,738451360146995,738006589204440,737550252108677,
  737082371083125]
private def phbn_w1_p4 : List ℕ := [736602967864224,736112063703296,735609679368290,
  735095835145410,734570550840641,734033845781154,733485738816604,732926248320318,732355392190370,
  731773187850545,731179652251196,730574801869987,729958652712528,729331220312900,728692519734067,
  728042565568177,727381371936760,726708952490804,726025320410724,725330488406223,724624468716035,
  723907273107559,723178912876375,722439398845649,721688741365425,720926950311800,720154035085974,
  719370004613199,718574867341596,717768631240857,716951303800825,716122892029958,715283402453659,
  714432841112494,713571213560271,712698524862002,711814779591733,710919981830238,710014135162587,
  709097242675578,708169306955030,707230330082940,706280313634498,705319258674961,704347165756382,
  703364034914189,702369865663615,701364656995976,700348407374796,699321114731769,698282776462559,
  697233389422446,696172949921789,695101453721334,694018896027331,692925271486490,691820574180741,
  690704797621818,689577934745648,688439977906548,687290918871222,686130748812559,684959458303218,
  683777037309007]
private def phbn_w1_p5 : List ℕ := [682583475182036,681378760653656,680162881827164,
  678935826170275,677697580507356,676448131011411,675187463195816,673915561905796,672632411309631,
  671337994889594,670032295432607,668715295020608,667386975020626,666047316074545,664696298088559,
  663333900222309,661960100877680,660574877687267,659178207502483,657770066381309,656350429575674,
  654919271518448,653476565810043,652022285204607,650556401595799,649078886002130,647589708551857,
  646088838467421,644576244049408,643051892660015,641515750706018,639967783621212,638407955848309,
  636836230820281,635252570941128,633656937566043,632049290980965,630429590381490,628797793851125,
  627153858338857,625497739636012,623829392352384,622148769891606,620455824425725,618750506868979,
  617032766850709,615302552687410,613559811353867,611804488453344,610036528186800,608255873321091,
  606462465156104,604656243490814,602837146588180,601005111138881,599160072223799,597301963275240,
  595430716036810,593546260521921,591648524970834,589737435806225,587812917587166,585874892961490,
  583923282616450]
private def phbn_w1_p6 : List ℕ := [581958005227614,579978977405912,577986113642747,
  575979326253113,573958525316600,571923618616212,569874511574897,567811107189678,565733305963289,
  563641005833188,561534102097836,559412487340108,557276051347700,555124681030402,552958260334067,
  550776670151133,548579788227517,546367489065721,544139643823932,541896120210951,539636782376706,
  537361490798154,535070102160305,532762469232138,530438440737132,528097861218120,525740570896171,
  523366405523170,520975196227764,518566769354284,516140946294283,513697543310246,511236371351040,
  508757235858632,506259936565556,503744267282599,501210015676112,498656963034336,496084884022064,
  493493546422940,490882710868606,488252130553893,485601550937157,482930709424807,480239335039009,
  477527148067445,474793859693939,472039171608669,469262775596560,466464353102361,463643574770765,
  460800099959827,457933576225733,455043638776864,452129909894883,449191998320379,446229498600391,
  443241990394894,440229037739034,437190188257638,434124972328170,431032902187944,427913470980989,
  424766151739531]
private def phbn_w1_p7 : List ℕ := [421590396294516,418385634109055,415151271028026,
  411886687936358,408591239317727,405264251704482,401905022008612,398512815722420,395086864976257,
  391626366439210,388130479046947,384598321539029,381028969785793,377421453882439,373774754985057,
  370087801860056,366359467114617,362588563071429,358773837245787,354913967377255,351007555961068,
  347053124216352,343049105418652,338993837512939,334885554909933,330722379352623,326502309720919,
  322223210619607,317882799567332,313478632571239,309008087831507,304468347270752,299856375522679,
  295168895939421,290402363083788,285552931055906,280616416856494,275588257801910,270463461766520,
  265236548718421,259901481611105,254451584162613,248879442347241,243176785474369,237334341434086,
  231341658901621,225186886787892,218856497657544,212334936668067,205604169946302,198643094782379,
  191426756163919,183925285757107,176102432777825,167913476746544,159302171042122,150196102933797,
  140499334574151,130080079819853,118748584060394,106213580093950,91984709247701,75105772499499,
  53108003237075]
private def phbn_w1 : List ℕ := pCat phbn_w1_p0 (pCat phbn_w1_p1 (pCat phbn_w1_p2 (pCat phbn_w1_p3
  (pCat phbn_w1_p4 (pCat phbn_w1_p5 (pCat phbn_w1_p6 phbn_w1_p7))))))
private def phbv_w1 : List ℤ := uOh phbn_w1
private def pvn_w1_0_p0 : List ℕ := [1999999796699841,1999999089718915,1999999109789846,
  1999999529489192,2000000186396944,1999999440830616,1999999411993489,1999998348223628,
  1999998216468745,1999998100190252,1999999632287255,2000000157722369,2000001391134242,
  2000001880637656,1999999134178081,1999998773190079,1999998760449228,1999999749108144,
  2000000175316640,1999998253410814,1999998318022254,1999999482383327,1999998721790595,
  2000000309957040,1999999874420116,1999999218172982,1999999455704690,1999998965016708,
  1999998587098752,2000001522039361,2000000763185082,1999999507649044,2000000523360825,
  2000001118007627,2000000194937209,2000000225358241,1999998789484052,1999999405592933,
  1999998927720488,1999999932707009,2000000018916038,2000001272146665,2000001078643141,
  2000001749213289,1999999754022418,1999999631489488,1999998389152756,1999999610347897,
  1999997916190399,1999999888906495,2000000456915420,2000000771783726,2000000903643110,
  2000001619596710,2000000001037131,1999995559749691,1999999677394053,2000001305787563,
  2000002914498080,2000000925567040,2000001157228317,1999999388185039,2000000078587360,
  1999998651043747]
private def pvn_w1_0_p1 : List ℕ := [1999998566560375,1999999723843159,1999998143604002,
  1999998839661086,1999998501917835,2000000917241910,2000003169705351,2000005306472773,
  2000006386836473,2000007637743978,1999992989849997,1999992018093598,1999990789082714,
  1999991766081712,1999993673271342,1999994470587097,1999996747124106,2000001240573265,
  2000002644590570,2000005593870876,2000007459598395,2000004518516091,2000003941213253,
  1999999338386819,1999997330651870,1999997665733446,1999995474536687,1999996020906351,
  1999997640637813,1999998316094142,2000001779119468,2000003907897140,2000005070668728,
  2000004474738216,1999999669731703,1999996720592193,1999994815558246,1999994793273304,
  1999998554822955,2000002705505572,2000003655866307,2000005054375121,2000003259872432,
  1999997544376639,1999995472041054,1999995564664723,1999998320992199,1999998160175906,
  1999996187944357,1999996256520125,1999999141888830,1999999866989496,1999995356081666,
  1999995409546388,2000000371738495,2000000943975857,2000006275759355,2000003266684204,
  2000002201716282,2000003293671716,2000005901461596,2000000789270282,2000002892103862,
  2000004209805146]
private def pvn_w1_0_p2 : List ℕ := [2000003768001058,2000003402072208,2000004480694796,
  2000003572277485,2000000831388249,2000004531159528,2000005419037163,2000000221675050,
  2000005733357716,2000004554409951,2000000556554170,1999994917238968,1999994202649263,
  2000000390541103,1999993648566211,1999995803561729,1999998803779625,1999993078999722,
  1999994529236680,1999997103613444,1999994809469590,1999996682196450,2000002018821050,
  2000004006560417,2000005667287309,2000005672798615,2000002652444816,2000004197218489,
  2000006012941383,2000003264933989,2000000499231479,1999997408496349,1999993794493883,
  1999995743668160,1999997600494365,1999996060293051,2000005158538307,2000002368786085,
  2000007312129297,2000009589105928,2000004165874095,2000005719807000,2000004315331047,
  2000003275957494,2000001947072422,2000001536180093,2000001736362262,2000001641912144,
  2000010195692425,2000006676852012,2000005487303084,2000011933571545,2000005822957031,
  2000003815816707,2000003082370083,2000008475470501,2000001172724053,2000001130618685,
  2000005926664841,2000002102145204,1999992657535914,1999996499400775,1999995092569431,
  1999992877079166]
private def pvn_w1_0_p3 : List ℕ := [1999996691002155,1999991837774120,1999998419792416,
  2000004466990620,2000003837189987,2000004525781753,2000004415435126,2000000796825315,
  2000007625933293,2000000580286035,2000005098428224,2000002882350435,2000003491499802,
  1999995440242129,1999998392015688,1999994673868014,1999998682627053,1999991823571597,
  1999999369031681,2000002585216035,2000005694360070,2000004251942780,2000005716122824,
  1999995971986420,1999996056922593,1999999059131278,2000004659909012,2000000790068971,
  2000004003084024,2000003339002322,1999996428688954,1999994323046047,1999994393769298,
  1999997198643354,1999998084240251,2000005891774997,2000004090969733,2000002702216586,
  2000000231355151,1999995618406084,1999998517335796,2000005504161583,1999999593670656,
  2000003792626400,2000001823942373,1999995497557195,1999998903603469,1999997578974525,
  1999996583529332,1999998007485658,1999993091994486,1999991958782249,1999998064712649,
  1999998381415826,2000005745203891,2000002570965037,2000005457004060,2000004791367861,
  2000002291077127,1999998688824598,1999995091268373,1999997424326649,1999995537053207,
  1999996891764584]
private def pvn_w1_0_p4 : List ℕ := [1999996613583844,1999997622517878,2000004205781032,
  2000003175227094,1999995548631940,1999995895690221,1999996175380580,1999996011677927,
  1999996109814917,1999995506487785,1999995852638348,1999993180764763,2000002404139170,
  2000009238216051,2000002679444492,2000005888976605,1999997494664921,1999994749284783,
  1999996450266159,1999996749806337,1999997388935645,1999996067094514,1999995435797046,
  1999997622496460,1999994791895926,1999998671111499,1999993780017707,2000001043176530,
  2000005303858779,2000002509634760,2000004121568671,2000004017677021,2000001529599238,
  2000002538039590,2000003356357885,1999993346482694,1999998710688381,1999995498900842,
  2000001604871196,2000004337571402,2000002583242908,1999995187810454,1999993545882692,
  1999999148802330,2000007082310346,2000003027262122,2000005787410368,1999993812872893,
  1999997328974490,1999992691413767,1999999487656247,2000007640972974,2000004682923314,
  2000006517612982,2000011190469652,1999998196985269,1999988955845007,1999988966922381,
  2000002270474501,2000012217411418,2000006979818457,1999994147901020,1999989761636078,
  2000001258585758]
private def pvn_w1_0_p5 : List ℕ := [2000010281385663,2000011087452268,2000000919597356,
  2000007461932584,2000004556582193,2000004306494804,2000007211951010,1999998922329266,
  1999994031456538,1999994682120554,1999997516406507,2000008504258602,2000005380784725,
  2000003696019921,2000008213377128,1999997018168442,1999994110285100,1999991273929245,
  1999997195990801,1999994151974657,2000008861457554,2000003479873191,1999995514018184,
  1999993607184651,1999999747683893,2000007133574366,2000008021850080,1999998370545511,
  1999993911012668,1999991653985204,1999996858153407,2000004834290266,2000007892268330,
  1999997276266772,1999994082667317,1999990113774819,2000005391729267,2000004261715104,
  2000011887121720,1999988472781382,1999997360738350,2000008766754676,2000014150042265,
  1999990639612872,1999997911181082,2000012304620895,2000014759746866,2000007773873791,
  1999995100834700,1999984190651294,1999981949802838,2000009977672471,1999996261182840,
  2000015698432629,2000020233826843,2000015508205503,1999996321391312,1999990167632277,
  2000018593691430,2000018664813754,2000010627079135,2000001584134900,1999986727731915,
  1999979463401327]
private def pvn_w1_0_p6 : List ℕ := [1999979097341535,2000014190765604,2000002996227670,
  1999991448897881,1999983002179809,1999979370051862,2000018983388961,2000012370075202,
  2000002179238377,1999990855508764,1999980791581090,1999973217022069,2000031659669361,
  2000033793881153,1999966850856445,1999969663835701,1999973176414841,1999975810714516,
  1999976684842778,1999975732739450,1999973936796718,1999975133875511,1999989818293114,
  1999959718106920,2000166778302153,2000435332079495,2000947535622665,2001851037528912,
  2003348037980431,2005699100903713,2009220314524243,2014272083102817,2021237678203789,
  2030490346450719,2042349961540403,2057033118394502,2074602760108904,2094924265632769,
  2117634817417327,2142132290972581,2167588617398577,2192989958508345,2217202093327390,
  2239055102818911,2257438071147887,2271392889350151,2280196341777092,2283421079603671,
  2280968555518615,2273070398596104,2260258788303311,2243310494748345,2223172511429947,
  2200878931957176,2177468739317956,2153912806219805,2131056193576605,2109579277816085,
  2089978680236510,2072566657123492,2057485759695774,2044734390295728,2034198478226255,
  2025684832093133]
private def pvn_w1_0_p7 : List ℕ := [2018952598039930,2013740386399355,2009787761084284,
  2006850739621639,1995288348791401,1996815854485490,1997885626181765,1998620576775521,
  1999115981913601,1999443649192709,1999656294411495,1999791670601496,1999876186085658,
  2000072099563838,2000041105540850,2000022925335571,2000012497313094,2000006653459455,
  2000003456756518,2000001751319658,2000000864676351,2000000415801837,2000000194652209,
  2000000088677980,2000000039305540,1999999983051384,1999999992889642,1999999997097009,
  1999999998845978,1999999999552981,1999999999831101,1999999999937677,2000000000022487,
  2000000000007939,2000000000002741,2000000000000920,2000000000000296,2000000000000088,
  2000000000000022,2000000000000003]
private def pvn_w1_0 : List ℕ := pCat pvn_w1_0_p0 (pCat pvn_w1_0_p1 (pCat pvn_w1_0_p2 (pCat
  pvn_w1_0_p3 (pCat pvn_w1_0_p4 (pCat pvn_w1_0_p5 (pCat pvn_w1_0_p6 pvn_w1_0_p7))))))
private def pvn_w1_1_p0 : List ℕ := [2000000018055855,1999999440728227,1999999187487497,
  1999998991584542,1999999991586069,1999999696865327,2000000024344971,1999999327242799,
  1999999176695808,1999997978032072,1999998186850804,1999998938950519,1999998651736846,
  2000001146263142,2000001733612310,2000000879283557,1999999831596063,1999998298329265,
  1999999133045800,2000000660702070,1999998842838945,1999999157411736,1999998757797187,
  1999998341156433,1999999283469205,2000000096982648,1999999021420967,2000000518229478,
  1999999643349826,1999997877275603,1999999041573027,2000000887620586,1999999864693900,
  2000000391698768,1999999829602995,2000001011096388,2000000611736570,2000000796400681,
  1999999567046874,1999999798813602,1999998625643490,1999999689666815,1999998848112941,
  2000000430053361,2000000112203852,2000002292417895,2000000924136907,2000000383929922,
  2000000178452371,1999999390576391,1999998660225428,1999997851199305,2000000934582099,
  1999998028345540,2000000199351249,2000002094534679,2000002883631431,1999998667400060,
  1999997895572753,1999998046792401,2000000099662151,2000002117210408,2000000796805696,
  2000001987210448]
private def pvn_w1_1_p1 : List ℕ := [2000000698161165,2000000220548574,1999999122971560,
  1999999598459168,1999998394968164,2000001321629896,1999994996815061,2000000762350321,
  1999998765201331,1999996875687097,2000002857988336,2000008251211740,2000008079845483,
  2000004267243619,1999997060530798,1999993720378884,1999993360943973,1999990565413966,
  1999992942028640,1999993319847434,1999994864930520,1999998994870330,2000000722152000,
  2000004333721641,2000007358827933,2000005498978100,2000004347447141,2000002083810420,
  1999999242676678,1999998363654190,1999996214438749,1999996118730706,1999996309126689,
  1999996456311923,1999999229931041,2000003227208837,2000004413920334,2000005254609372,
  2000003729118297,1999997959226998,1999996060061765,1999995018609721,1999995916535464,
  1999998620520071,2000002774426946,2000005935556626,2000004546587135,2000000306341873,
  1999996574343509,1999996923538946,2000000625553155,1999994622054052,1999996338922853,
  1999997340506255,1999999288300981,1999998294043901,1999998062415420,1999993004919203,
  1999996907537897,2000001839566536,2000001537214182,2000001617718788,2000003693162015,
  2000004804474692]
private def pvn_w1_1_p2 : List ℕ := [2000002453227227,2000002671363192,2000005204922357,
  1999999742909032,2000004596239396,2000005823430327,2000002165690221,2000003396224511,
  2000002581511213,2000006390862656,2000000341475666,2000000524877666,2000009224865816,
  2000005087272227,2000001027033792,2000002105235185,1999997851577465,1999995127766280,
  1999998068081287,1999997241312301,1999995045411501,1999996662981913,1999995838369498,
  1999994784499382,1999994982770254,1999993627052226,1999995733487175,2000001626242198,
  2000003690149955,2000002593186866,2000005964957672,2000000760173261,2000007619005699,
  2000006455685920,2000002426799158,2000003975217010,1999996962888839,1999995798310142,
  1999996316073317,1999995054501357,1999996682246996,1999999474270034,2000005509530949,
  2000003934024541,2000007590001030,2000007804093577,2000001922489607,2000008852862545,
  2000004131021524,2000000890955838,1999999245055690,2000004866517756,2000002151553092,
  2000002124103162,2000008847658532,2000011484844547,2000003510832687,2000006888850369,
  2000010721680106,2000001407300062,2000004469823053,2000004594288293,2000004754753002,
  2000005944737993]
private def pvn_w1_1_p3 : List ℕ := [2000000742992514,1999995560312627,2000000910371882,
  1999993240101823,1999996737626295,1999989976246123,1999994060975389,1999996416910988,
  2000003494672497,1999999331769332,2000005849679164,2000002338017917,2000005510070676,
  2000000615662877,2000004837252791,2000006039225303,2000004985059710,1999998781687658,
  2000002997107124,1999998465794959,1999996570561408,1999994184425038,1999996011599259,
  1999994146850050,1999999692050576,2000008634442512,2000004865672268,2000001533625616,
  1999998964188039,1999999820920495,1999996002094750,2000001503619359,2000004401253471,
  2000003280875509,2000003225912826,2000000401591090,1999993114190212,1999996887769659,
  1999993035628392,1999996949242511,2000006997067976,2000002915921471,2000001657877793,
  2000001100950511,1999996632377051,1999999199962462,2000002981707963,2000000547386363,
  2000005585098394,1999998868972540,1999999435224732,1999997929122929,1999999258553298,
  1999999917523698,1999995215703770,1999993558953026,1999992098084957,1999996791737905,
  1999997840023341,1999999640292846,2000004424358281,2000005182325979,2000005431220129,
  2000004166751386]
private def pvn_w1_1_p4 : List ℕ := [1999997497032933,1999998800505042,1999999941349819,
  1999994387158814,1999993460875982,1999995940315045,2000002193327740,2000001510589255,
  1999998990121642,2000002594474577,1999992506268485,1999997327378842,1999999807804323,
  1999995047254411,1999993728337652,1999992670075236,1999994720850401,2000001697750654,
  2000004502420638,2000008549391630,2000000614533485,2000001017109550,1999996774224598,
  1999996563696407,1999999271875591,1999994539581129,1999995562248364,1999998828363563,
  1999996986102806,1999992200740771,1999998493024910,1999992982888679,2000001777878249,
  2000002701887306,2000002218625044,2000002702638770,2000004333188089,2000003653324006,
  2000004796111598,1999999812123854,1999999029165353,1999989944883627,2000002460330838,
  2000002264646360,2000004945323909,1999998264501510,1999992715223933,1999997982520464,
  2000000323904934,2000002339309001,2000009909159838,2000000305053308,1999994409699647,
  1999996329038205,1999997669737130,1999996933801845,1999999834095208,2000010108731431,
  2000013977466240,2000007707651839,1999989810275088,1999988651735081,1999995130726237,
  2000012428147771]
private def pvn_w1_1_p5 : List ℕ := [2000008175503688,1999993211628452,1999995117032017,
  1999998334438679,2000002131742186,2000008762945178,2000004241388537,2000005224323718,
  2000005194599735,2000005024913765,2000013209852043,2000000521248461,1999996509112499,
  1999993873191169,2000000591429013,1999995155337492,2000006976136159,2000007892351164,
  2000004665943233,2000004946977876,1999999687627678,1999990267211390,1999991186758348,
  1999997164083893,2000006286333624,2000003133969381,1999995569214496,1999992825472528,
  2000000614967037,2000002524037493,2000011228071263,1999999849517017,1999998759936713,
  1999985157366569,2000001788139559,1999999822223661,2000009597032068,1999999787140994,
  1999991653463890,1999986960649463,2000009389120302,2000011524731921,1999991915596527,
  1999993834799728,2000006536571564,2000011966532005,1999994268383836,2000004597675565,
  1999989351945709,2000014635889716,2000020581219973,2000005624710088,1999995442033590,
  1999988937266927,1999995106121703,1999983509113418,1999997700611267,2000024600537292,
  2000018081528483,2000006111413526,1999991992355545,2000010662874781,2000004939540024,
  2000017450001668]
private def pvn_w1_1_p6 : List ℕ := [2000027069330176,1999994171524918,1999988787064949,
  1999973341342917,1999995827822056,2000012474622470,2000001139992633,1999973038454642,
  1999991668755785,1999993997307042,1999994029579428,2000039902618544,1999998101164224,
  1999957975244472,1999984851266034,2000018527411148,2000022084449757,1999995431730428,
  1999997823624106,1999950007645566,2000009757997595,1999953135035067,1999963611677137,
  2000005139310709,1999983957739975,1999941241122891,1999930443906876,1999965702293131,
  2000064989210504,2000282960237387,2000720445239076,2001530082978145,2002923560912307,
  2005176779028717,2008628686635003,2013670233275195,2020720532565541,2030189211038690,
  2042426932347536,2057668955487685,2075978427628813,2097197093059414,2120911589893914,
  2146443166069555,2172866649173129,2199060562951557,2223785223984253,2245780929267964,
  2263875088150523,2277085706198865,2284708854135752,2286379524923655,2282098578498060,
  2272223062155084,2257422342296429,2238607102600498,2216841342687032,2193248843317994,
  2168923677504016,2144859753531928,2121870570357030,2100674745822266,2081376548189849,
  2065381152890768]
private def pvn_w1_1_p7 : List ℕ := [2049290060935693,2041323201509046,2026394859623166,
  2021737945992851,2019032477922295,2011234692079938,2003226796943451,1998897809340834,
  1997712856260461,1997975752498861,1998489000101709,1999074838485602,1999365397036046,
  1999569714959952,1999790524634733,1999947558945094,2000014004572177,2000026218477709,
  2000020191821101,2000012328782177,2000006797122018,2000003544293053,2000001793278699,
  2000000859913121,2000000424572149,2000000200309273,2000000074086051,2000000016665532,
  1999999999158692,1999999996904438,1999999998056116,1999999999064070,1999999999617237,
  1999999999878110,1999999999974851,1999999999999653,2000000000002501,2000000000001447,
  2000000000000581,2000000000000195,2000000000000056,2000000000000012,2000000000000001]
private def pvn_w1_1 : List ℕ := pCat pvn_w1_1_p0 (pCat pvn_w1_1_p1 (pCat pvn_w1_1_p2 (pCat
  pvn_w1_1_p3 (pCat pvn_w1_1_p4 (pCat pvn_w1_1_p5 (pCat pvn_w1_1_p6 pvn_w1_1_p7))))))
private def pvn_w1_2_p0 : List ℕ := [2000000138975492,1999999729381589,1999999608732334,
  1999998804238279,1999999565536473,1999999478059770,2000000092338741,1999999682191111,
  1999999962963652,1999999560619522,1999998051223419,1999998911944939,1999998131779532,
  1999998010927521,1999999723700238,2000000760792276,2000001588548610,2000001643484481,
  1999998698335611,1999999141066144,1999999817088323,1999999554060846,1999999534334743,
  1999999803363726,1999997932780750,1999998917453390,1999999414457417,1999998644824384,
  1999999476342349,2000001266584322,1999999027220276,1999998775817368,1999998539926918,
  2000000039829104,1999999795733569,2000000295239194,1999999478203937,2000000833859172,
  2000000159811611,2000001444377463,2000000015549850,2000000670192436,1999999023792099,
  1999999650277617,1999999263294376,1999998526765304,1999999824656660,2000000329122965,
  2000002168594407,1999999603548334,2000002322244505,2000000517415242,1999999150275199,
  1999998540505397,2000000444435664,1999998385817906,1999997484334166,2000000049054161,
  2000001365845025,2000003282620006,2000000076705021,1999998533240859,1999997903589188,
  1999999766029043]
private def pvn_w1_2_p1 : List ℕ := [1999998841372613,2000003050105637,1999998964227153,
  2000003911605281,2000000341756104,1999998224304209,2000001757276066,1999999930483910,
  1999997249050386,1999999955589400,2000000100884569,1999997598721805,1999996391398663,
  1999996171816000,2000003923098659,2000007932855543,2000007078512801,2000005407146773,
  1999999938042308,1999996203560843,1999994703477956,1999991588880133,1999992059995486,
  1999993097405907,1999992890752952,1999995998311298,1999998915547415,2000002753077642,
  2000005585541358,2000005812288851,2000005267859853,2000004204327486,2000001022529464,
  1999999318899431,1999999103599151,1999995745426902,1999995757687827,1999995845723957,
  1999996593157224,1999999984082269,2000003901020067,2000005793567469,2000004362911961,
  2000001592765765,1999999374964142,1999994760169060,1999995999060666,1999993467656780,
  2000001138493132,2000005769084976,2000004654484571,1999999997797704,2000001437739272,
  1999999132984755,1999998571680761,1999998023204097,1999994469538704,1999996137181540,
  2000000393561614,1999999882525533,1999996077238812,1999993729396215,1999998925608754,
  1999995798252389]
private def pvn_w1_2_p2 : List ℕ := [1999998645585666,2000003385139041,1999999851826674,
  2000003915611235,2000003617048026,2000004485696200,2000001993883514,2000000187273731,
  2000006985711509,2000003811536947,1999999477127554,2000005935367793,2000006467186996,
  2000000747445657,2000001756766508,2000003667454272,2000002784106326,2000006024803819,
  2000006688950030,2000002683990628,2000000939563132,1999999321635453,1999997711516608,
  1999997351439962,1999998036328638,1999993475551915,1999999729183184,1999995494647193,
  1999994363440316,1999995020374333,1999990360760235,1999997763127295,2000000512664782,
  2000000210509638,2000003098442033,2000002148196152,2000004252926302,2000004936141038,
  2000008237363750,2000004744377370,2000000903995474,2000003892062763,1999994524225027,
  1999996836105393,1999995196609951,1999994975052699,1999997218383166,2000004653285681,
  2000004306095160,2000002697779200,2000006362921468,2000010391418523,2000004030836191,
  2000001304117679,2000008752882218,1999999134506575,1999998184988509,2000004490497001,
  2000004582133838,2000004367426773,2000008979309172,2000004514990406,2000012759983800,
  2000004070691009]
private def pvn_w1_2_p3 : List ℕ := [2000004983090169,2000003202611296,2000007864774394,
  2000004541168805,2000007075607076,1999998466979998,2000002925136372,1999999500796326,
  1999998504057556,1999992095187974,1999992727238912,1999993113779915,1999996974076431,
  1999995048935341,2000003318500158,2000003707314050,2000001758253212,2000001074764232,
  2000005081791314,2000005349190206,2000002405612827,2000006721232006,2000002743613520,
  2000001222267170,2000000867072506,2000001425700044,1999992728730317,1999991083915165,
  1999996700928414,2000000090219146,2000002050152726,2000007698113390,2000001179188667,
  2000000914410049,1999999614901964,1999994726466640,2000002471450112,2000003343371477,
  2000001762940980,2000006121732614,2000002514984668,1999994073053898,1999995964726195,
  1999991519384396,1999999750613784,2000001925391617,2000003235917572,2000003022028908,
  1999999121065637,1999999140773514,1999997915737645,2000002015306735,2000003077086112,
  2000002925193468,2000000513549209,1999997845160884,2000001026396918,2000001894436298,
  1999997641295592,1999997232691198,1999993894098106,1999992829444402,1999996219596698,
  1999994035675121]
private def pvn_w1_2_p4 : List ℕ := [1999997755649910,2000003871212441,2000005908041808,
  2000005217043474,1999998814465137,2000006670911644,2000000630382730,1999995773578565,
  1999997367695900,1999993080033865,1999994980579078,2000002011588203,2000000997384239,
  2000001233329369,1999995710035909,1999999794691516,1999997505019156,1999999172306512,
  1999997555768642,1999990563607166,1999992497885029,1999994138036465,1999999683803408,
  2000005107950761,2000007173760423,1999998091156928,2000004939473844,1999998434170524,
  1999997329380262,1999997384733984,1999996086451474,1999996859622228,1999999455960230,
  1999994313942239,1999995472796931,1999991703472042,2000000419829993,1999995454314872,
  2000003444108489,2000001209161531,2000000315236348,2000005317559554,2000006300601976,
  2000005794812849,2000000157760904,1999990806558921,1999999410940447,2000002241839019,
  2000001599239488,2000003409782244,1999997945027584,1999992498770589,1999995208294369,
  2000005262175599,2000004643473443,2000003723243490,1999998154916728,2000002552965593,
  1999995832657849,1999991434969059,1999994410080234,2000002625109102,2000018939664015,
  2000014227790072]
private def pvn_w1_2_p5 : List ℕ := [1999992191025984,1999990526051908,1999996512427416,
  2000004584962541,2000008217898082,1999996674351556,1999999267679441,1999993300566729,
  2000000948925773,2000003874120016,2000007708139443,1999997573538053,2000005821663749,
  2000011327347063,2000007120685977,2000006704853725,2000003467338419,1999994571402728,
  1999996139245143,1999997572402186,2000000797033016,2000002984934740,2000009035126523,
  2000008617277655,2000004990972711,1999988016429073,1999994526489912,1999993748913225,
  2000008182304475,1999997161519130,2000001947627690,1999989346796492,1999997620775311,
  2000003705736700,2000010337449133,2000002400971380,1999998842558171,1999991106899862,
  1999988828401459,2000011182060288,2000009301082926,1999995561526859,1999980086010375,
  2000011383415327,2000000048235736,2000000777646334,1999997249990270,1999993342520785,
  2000010687284779,2000007863157623,1999999555599279,1999987388493554,2000001429114384,
  2000019808450145,2000005700208300,2000011048309263,2000004847481006,1999999932647978,
  1999974288141534,1999984173155303,2000014730922684,2000005042928498,2000020598352412,
  2000003850276890]
private def pvn_w1_2_p6 : List ℕ := [1999998297296583,1999999123465477,2000012708731392,
  2000022068594042,2000029278396491,1999994051535528,1999967734561497,2000008110170206,
  1999993060744173,1999996885250097,2000011602042370,1999972941701215,1999968937012574,
  2000001328983074,2000047226785721,1999980970017485,2000001697081055,1999957220275735,
  2000003932606692,2000033335147035,1999991746835436,1999995711569041,2000008780940625,
  1999976768144573,1999954668286064,1999975427940477,1999999726974116,1999993160715395,
  1999963776367206,1999934930591679,1999921096722191,1999932893168277,1999995563147923,
  2000166017377247,2000546043753934,2001293718071249,2002633494252757,2004862880934796,
  2008351665853946,2013529027793511,2020855223041528,2030777482535943,2043673012308572,
  2059784617245185,2079156522459435,2101579722081527,2126557147769308,2153298003934429,
  2180747131770087,2207649860444713,2232646950775561,2254389450896533,2271659619391778,
  2283484634653182,2289222045043822,2288632341371083,2281831612246851,2269472801514556,
  2252035162211127,2231571545876590,2206894052401935,2184236581522796,2155658981985408,
  2135483404557588]
private def pvn_w1_2_p7 : List ℕ := [2109819613817551,2088637562770438,2073854823968029,
  2056384780664126,2040610446013227,2032106850803569,2026720278908893,2019607160080983,
  2011036700824373,2004102343657720,2000013073581942,1998390309561520,1998256948064606,
  1998618900384515,1998989622211170,1999308646687016,1999591136494826,1999808934615410,
  1999940506715688,1999999556312751,2000016323762469,2000015579075180,2000010601017048,
  2000006194715019,2000003306123602,2000001677244339,2000000827213799,2000000389422517,
  2000000165872358,2000000059615508,2000000016166678,2000000002025894,1999999998928001,
  1999999998943689,1999999999427867,1999999999763482,1999999999922135,1999999999980517,
  1999999999997186,2000000000000444,2000000000000540,2000000000000260,2000000000000091,
  2000000000000024,2000000000000004]
private def pvn_w1_2 : List ℕ := pCat pvn_w1_2_p0 (pCat pvn_w1_2_p1 (pCat pvn_w1_2_p2 (pCat
  pvn_w1_2_p3 (pCat pvn_w1_2_p4 (pCat pvn_w1_2_p5 (pCat pvn_w1_2_p6 pvn_w1_2_p7))))))
private def pvn_w1_3_p0 : List ℕ := [2000000198706859,1999999841047904,2000000092290048,
  1999999065170479,1999999381501701,1999999127147125,1999999785686293,1999999816242114,
  1999999507379355,2000000677147886,1999999397573739,1999998866528541,1999999255010534,
  1999998290029514,1999997773112361,1999998779076894,1999998604331325,2000001202045043,
  2000002086245190,2000000586118372,1999999380983709,2000000003392475,1999998887784290,
  1999999819781337,2000000369127181,1999999103457322,1999998333279378,1999999971620051,
  1999998137411304,1999998587415588,1999999343481137,2000000883419768,1999999617364983,
  1999999435268092,1999998143463121,1999999816641282,1999999111171044,2000000395348961,
  1999999223990297,2000000305339930,2000000077345347,2000000458582828,2000001445032314,
  2000000029274722,2000000802024377,1999999109333688,2000001017413221,1999997858399263,
  1999998825962670,1999999811260110,2000000364124824,1999999544568443,2000001602285341,
  2000002576091706,1999999508418719,2000000276045970,1999999741399418,2000000549336058,
  1999998212155218,1999997857598583,1999997061048715,2000003117846071,2000000069476892,
  2000003401660701]
private def pvn_w1_3_p1 : List ℕ := [1999999133526205,1999997727589011,2000000536264698,
  1999998046202514,1999998579140389,2000003058579164,2000001500446041,1999999477323700,
  2000002006226331,2000000641413466,2000000406754513,1999998404773370,1999998595772810,
  2000002269955553,1999999854807899,1999995748290970,1999995406916097,1999996536775829,
  2000002138173712,2000006965370768,2000006607469950,2000006292609993,2000002922524957,
  1999998779503716,1999995959840833,1999993778385051,1999992654113482,1999992377288929,
  1999991777393339,1999993155803335,1999997574698960,1999999240698712,2000003330563653,
  2000005954445864,2000005254184947,2000004706076767,2000003603356766,2000001511918853,
  1999999937500933,1999997850890015,1999997699202956,1999993106665681,1999996442423210,
  1999996317400479,2000001756661965,2000004442836482,2000004645387677,2000003183214368,
  2000004534728666,1999998125420015,1999992238660001,1999994902319632,1999998102627836,
  2000001666501108,2000004300869207,2000001702198650,2000001690233313,2000000944904022,
  2000003286311586,1999996674651634,1999993086656924,2000000176759964,1999997196836913,
  1999999075721600]
private def pvn_w1_3_p2 : List ℕ := [1999998635729524,1999996020672565,1999996157573372,
  1999994617592174,1999999037138045,1999999293021287,1999996499938638,2000003571151642,
  2000006116886529,1999999832608367,2000001551385275,2000006310357583,2000002420261135,
  2000001057942149,2000004121732409,2000003738878071,2000004568204536,2000004464452274,
  2000002802445897,1999999649656845,2000004762353621,2000002154334108,2000007276347911,
  2000006618041901,2000001055235268,2000004493896960,1999999554894813,1999998628810903,
  1999999110342752,1999994628480589,1999998109047793,1999998494766030,1999997356943754,
  1999993412985855,1999992417436310,1999994925275176,1999992494858749,2000002038206753,
  1999998329030610,1999999529341474,2000002558519138,2000004165205246,2000003970692614,
  2000007647520780,2000006416069308,2000002936978272,2000002297680827,2000001463036792,
  1999996341320412,1999989460072377,1999999989074667,1999998716469958,1999995371086897,
  2000003475035200,2000007741566721,2000000839301252,2000009645636253,2000004482467836,
  2000008866587818,2000001685964936,2000001438857744,2000000203302899,2000005089634965,
  1999999259412543]
private def pvn_w1_3_p3 : List ℕ := [2000006030809288,2000004855545604,2000010272058201,
  2000007896814614,2000006055181258,2000003000733737,2000007397548111,2000006250301941,
  2000007438504823,2000001814651972,2000004545364559,2000005100183138,2000000734896622,
  1999997537012475,1999996275038561,1999995235896346,1999988777547973,1999994935476462,
  1999998157595480,1999999384480000,1999999616624923,2000003364157984,2000001448815555,
  2000001513512293,2000005880943631,2000006868261091,1999999990116653,2000005426180132,
  2000005827067695,2000001768208598,2000002237458230,1999993080712087,1999992231734552,
  1999996371487287,1999996089399917,2000001423579905,2000008209273366,1999999801912457,
  2000002867722383,1999998524313115,1999997780563084,1999999397780256,2000000353813959,
  2000005972177399,2000005316726729,2000003444008690,1999996942748733,1999994118849558,
  1999994380341261,1999996617429035,2000001371900537,2000002741389793,2000002050705534,
  2000001073604752,1999996404999930,1999999106775968,2000003779324748,2000001356911514,
  2000002207611487,2000000059611477,1999999086698521,2000003562159787,2000000045076763,
  2000000989021994]
private def pvn_w1_3_p4 : List ℕ := [1999994633113595,1999998374000090,1999995838470233,
  1999988090006033,1999995115369182,2000000360231121,1999998740971491,2000004635997698,
  2000002378480541,2000005180789983,2000002930803063,2000004481377142,1999998875280492,
  1999992688993253,1999995943007648,1999995863193598,2000000672542769,2000000801948742,
  1999999119096303,1999995725817196,2000002685461793,1999996683896082,2000002215677818,
  1999997147993277,1999989278122472,1999991121285534,1999996073161274,1999997471240963,
  2000004537056659,2000001008625914,2000005915240455,1999999783018177,2000003756784521,
  1999995291600541,1999996909070838,1999999721717897,1999996728855899,1999998137243707,
  1999996174443205,1999991932564943,1999996125880833,1999994745827262,2000000416728931,
  2000000328614975,1999995001232687,2000002853348549,2000008853657968,2000007178246001,
  2000001161781457,2000000600436198,1999993581092541,1999998860609668,2000002493410578,
  2000006861015091,1999999035202552,1999991708587089,1999997659736180,1999999381343186,
  2000001470307869,2000003608329492,1999999887648172,2000007759362487,2000003870382689,
  1999985062187352]
private def pvn_w1_3_p5 : List ℕ := [1999988985306316,1999997542776600,2000018052009073,
  2000011630310708,2000002265333497,1999992439138791,1999998314633908,1999998773546035,
  2000005822979936,2000005527710613,1999993661149608,1999994760133760,2000003288579864,
  1999999866308241,2000001421455984,2000001453421490,2000003111484143,2000005381250952,
  2000012143061526,2000007526762410,2000007968824508,1999995552806329,2000003320122396,
  1999991893852910,1999999016650461,1999995439807625,2000013834601030,2000009460663418,
  2000005255949342,1999994818048478,1999993156241641,1999994828323144,2000003596749432,
  2000005037923752,1999991687958115,1999997605564363,1999991524069651,2000003281573197,
  2000004624299982,2000019616529933,1999986147416422,1999985143680371,2000008112270607,
  2000004446914272,2000003373098880,1999990976848802,1999995137185253,2000002912563198,
  2000003542551200,1999999603021049,1999983710948183,2000008787796305,2000010929806862,
  2000002918062853,1999990054680395,1999996863723425,2000011408816276,1999990880340410,
  2000020134533749,2000018954745364,2000006133541092,1999989729123922,1999984015200698,
  1999985383132575]
private def pvn_w1_3_p6 : List ℕ := [2000005416607245,2000012885175896,2000006953099310,
  2000019397613682,1999978744307012,1999995697852852,2000039855698418,2000014934888552,
  2000013983994951,1999996417562257,1999997302350997,1999962731156364,2000041441056638,
  1999994803321429,1999977524694490,1999975927115932,1999977660326801,2000032262512338,
  2000022426330659,1999970184850671,1999981081125801,2000006550207107,1999996915911258,
  1999997136610466,2000017683854647,2000014494553482,1999982583594584,1999962085574971,
  1999972521590786,1999993554489669,1999999265035290,1999984263293731,1999958614755817,
  1999932509731883,1999911402736160,1999904117862244,1999937217924940,2000070300541826,
  2000410754492846,2001128186409078,2002467614877390,2004757963953539,2008410451359909,
  2013901712480906,2021738853243194,2032406862981938,2046301781688988,2063656469298620,
  2084467169169422,2108437885865008,2134938497887672,2163040588788239,2191470153499216,
  2218955963131790,2243651457176032,2264981867249911,2279872981821594,2291045842717910,
  2291592900349858,2291269797852422,2277767824762369,2264602380616567,2244713070030403,
  2218831774755285]
private def pvn_w1_3_p7 : List ℕ := [2196198679219309,2170505234704225,2142115837958533,
  2119158553267660,2099492314811306,2078441873063397,2058822934335643,2045379266572820,
  2036787469858928,2028862652789947,2019999733407217,2011351673096663,2004651723918975,
  2000672062366981,1998965504313022,1998562328857169,1998699804753743,1999006985285248,
  1999338331641837,1999622540122683,1999823400355396,1999939392390043,1999992564076234,
  2000009936422051,2000011592229868,2000008492716554,2000005166033091,2000002835048532,
  2000001456090808,2000000706022032,2000000318871939,2000000130547944,2000000046644274,
  2000000013595420,2000000002607210,1999999999828713,1999999999520689,1999999999707651,
  1999999999873850,1999999999956759,1999999999988222,1999999999997720,1999999999999886,
  2000000000000150,2000000000000088,2000000000000030,2000000000000006]
private def pvn_w1_3 : List ℕ := pCat pvn_w1_3_p0 (pCat pvn_w1_3_p1 (pCat pvn_w1_3_p2 (pCat
  pvn_w1_3_p3 (pCat pvn_w1_3_p4 (pCat pvn_w1_3_p5 (pCat pvn_w1_3_p6 pvn_w1_3_p7))))))
private def pvn_w1_4_p0 : List ℕ := [2000000250206562,1999999797501018,2000000385940707,
  1999999527033729,1999999571408176,1999999137037187,1999999154004015,2000000061469978,
  1999999109778033,1999999868512602,2000000598415469,1999999653306387,1999999295680320,
  1999999903285344,1999998351334602,1999998753075338,1999998175094658,1999997580778242,
  1999998803800253,2000001612189653,2000001006208087,2000000806904864,2000000542632137,
  1999999492211213,1999998637785986,2000000947883434,1999999503755433,1999999326924588,
  1999999214482487,1999999971996306,1999998075663770,1999998659011423,1999998327755743,
  2000000730359245,1999999742967945,2000000077417390,1999998665934823,1999998989445796,
  1999999630347172,1999998935660993,2000000466930462,1999998845922586,2000000591197551,
  1999999056021486,2000001593792052,2000000597940672,2000000117344134,2000000571195681,
  2000001208689663,1999999546797114,1999997951892108,2000000524753284,1999998573810907,
  1999999099439630,1999999561622217,2000002340062805,2000000389494455,2000002244098556,
  1999997860512792,2000002791070222,2000000336297547,1999998495900009,1999998900009905,
  1999996226685448]
private def pvn_w1_4_p1 : List ℕ := [1999999220595116,2000003105124861,2000000550133310,
  2000000101750607,2000002322035302,1999997936849814,1999997738427867,1999999435710602,
  2000000223317808,2000001425669645,1999999793942191,2000000761503033,2000003410169489,
  2000000325446715,1999998261214194,1999999557769458,2000000350795889,2000002484562041,
  1999999984138533,1999995577650574,1999994614107492,1999996420914104,2000000066623697,
  2000004364569009,2000006787479743,2000006425723317,2000005543540925,2000000638957973,
  1999998346861872,1999996871414166,1999993523294792,1999992239930489,1999992164992513,
  1999991560382626,1999994229350124,1999996388904219,2000002162284156,2000001637577660,
  2000006405060996,2000004775005112,2000004397218129,2000003286402126,2000002381569149,
  1999999832252911,1999999474795620,1999995298380380,1999992455748171,1999997183854039,
  1999998914566460,1999998740848455,2000004251695359,2000005846573505,2000006508507556,
  2000000584354551,1999996637987452,1999994200927076,1999993449443667,2000003121902057,
  1999999889502647,1999999072579877,2000004208338637,2000003430432153,2000002874790473,
  1999998691630163]
private def pvn_w1_4_p2 : List ℕ := [1999997196946838,1999998046217951,1999995876221601,
  1999999537200795,2000001388183980,1999994920197941,1999995104591962,2000000084382027,
  1999995463726509,1999992939453739,1999999980394025,2000001084827904,2000000382208098,
  2000000911864244,2000004525728140,2000001210328985,2000005187260413,2000001599938890,
  2000000816041483,2000005674193079,2000002083136626,2000006227703566,2000004724905301,
  1999999509930117,2000003084673956,2000001792427520,2000004683027790,2000006170226046,
  2000004715801301,2000004612575345,2000002292489774,2000005291740219,1999995952036460,
  1999998810612525,1999998063564255,1999997394255853,1999999476275383,1999998490011762,
  1999992444917876,1999992672343266,1999994806930631,1999994339221888,1999997080549205,
  1999997964059908,2000000797517872,1999996751460194,2000004763795986,2000007419836732,
  2000001964683791,2000004294373940,2000013580592699,1999998573430515,2000001942571822,
  1999997149586514,1999997317821719,1999993125748104,1999997253172829,1999996812520845,
  2000003912964113,1999998595208651,2000005328116167,2000006849142066,2000008254137448,
  2000004781499944]
private def pvn_w1_4_p3 : List ℕ := [2000004734706731,2000001669488568,2000004232197710,
  1999999683463791,2000001065039514,2000002421018988,2000006836202383,2000009891343215,
  2000005498568607,2000004926996310,2000005851588209,2000009602483176,2000003580281631,
  2000005305365440,2000007089160501,2000005250989614,2000002416124655,2000004997802510,
  2000002135855534,1999996271811724,1999992811668610,1999995335251594,1999990852971256,
  1999994868878403,2000002072399998,1999996291274815,1999999746476543,2000002346340426,
  2000002205850282,2000005196465490,2000003936237078,1999999444725469,2000009366485247,
  2000004506247115,2000004704367395,2000003358712393,1999995544716018,1999993660512121,
  1999992364969851,1999997702567517,2000000394832887,2000003060347585,2000003453769443,
  2000002145397045,2000000319697670,1999996763732363,1999997313042833,2000001674068139,
  2000004201190172,2000007205144035,2000003828262367,1999997814593509,1999997201921546,
  1999993077216235,1999995076973035,2000002433282306,2000000846709549,2000003264098344,
  1999997050439780,1999999421938581,1999999751097860,2000001638234268,2000004187864592,
  1999997826712267]
private def pvn_w1_4_p4 : List ℕ := [1999999542376128,2000006291958589,1999997918597186,
  2000001164152541,2000001360248069,2000001363456512,1999995874920844,1999993041238428,
  1999993721681334,1999991477739154,1999998657803392,1999999048505399,2000000268062206,
  2000001321698848,2000007387705203,2000003166632971,2000007332245771,1999996848400056,
  1999994286938191,1999997405288831,1999996687141302,1999998427441125,2000002620931852,
  1999994231576014,1999999662683249,1999998383117978,2000005467847090,1999997914847402,
  1999996910155235,1999991443310385,1999990149351147,1999996634761373,1999996411162585,
  1999998859362533,2000005402337853,2000002146747488,2000004184714672,1999999836161709,
  1999997267577014,2000000108186063,1999996741073602,1999999976887897,1999998956193381,
  1999993735733467,1999990201694960,2000000015511906,1999996676834698,1999995836464437,
  1999995016285854,1999998855751424,2000004083040367,2000005655668460,2000009741661703,
  2000002332704517,1999992606052122,1999999091428924,2000002063739542,2000004234630653,
  2000004715818268,1999990800487578,2000000276222677,1999998395318490,1999998753239843,
  1999993607444177]
private def pvn_w1_4_p5 : List ℕ := [2000005435162211,2000011680984836,2000007893339864,
  1999988507517199,1999983677681671,1999997636203447,2000006311481470,2000010631738785,
  2000010698718130,1999995113199977,1999994928798732,2000002609714390,2000005755075118,
  1999999346043748,2000001192999910,1999994226099363,2000002913453106,1999995828578563,
  2000005766896703,1999994364966830,2000003259006657,2000001523542220,2000012889750272,
  2000007117317453,2000007055546911,2000006712977476,2000003148736466,1999994086874399,
  1999990998690628,2000001250497093,2000001877567380,2000017689960448,2000003403763569,
  2000000519744048,1999988758048034,2000005048155461,1999996312552258,2000000577188598,
  2000009338343003,1999981627003773,1999989312582567,2000007714094532,2000013649100427,
  2000002884175797,1999988075670009,1999999237716034,1999998365835752,2000011843133203,
  1999994917940443,1999989325929922,2000003164608732,2000005456543502,2000003338329162,
  1999976981767887,2000008292640395,2000007247884133,1999998387358874,2000002657026265,
  2000003900244854,1999991515324817,1999994456916174,2000007181263235,2000010569764213,
  2000030954113164]
private def pvn_w1_4_p6 : List ℕ := [1999997281729534,1999991141826108,1999998725533352,
  1999966555745486,2000012215735068,2000018697116375,2000015980780770,1999968055311683,
  2000024108347110,1999989004292428,2000020304518094,2000045530125805,1999996280908327,
  1999990894970855,1999989691824464,2000004228030407,2000029399077642,1999987371816788,
  1999950261395695,1999990365660759,2000023223328178,2000003495531928,1999989709133008,
  1999997564063637,1999992869820720,1999982797969061,1999996365038540,2000020670060477,
  2000020879654763,1999994661254764,1999971284335573,1999971122854987,1999986748814220,
  1999998573965729,1999995627374912,1999979803357804,1999957276516998,1999930836485101,
  1999901007403997,1999875370506100,1999882209321873,1999986090007055,2000304695334821,
  2001027559365817,2002430469757451,2004890375500111,2008863863621866,2014910491427609,
  2023525732992757,2035384699614193,2050529846472927,2069927213409867,2091925541752696,
  2118994993058181,2145354546090936,2177525445663145,2203636713569550,2234178602892950,
  2256550766811448,2275503803855864,2291027594053444,2294956138994985,2294852273185442,
  2289299084902952]
private def pvn_w1_4_p7 : List ℕ := [2273155314150501,2253739599575030,2233186525986143,
  2206958770061053,2177814831794018,2152176619682084,2129159843026954,2105045804590990,
  2081512657272617,2062816293621064,2049788652442607,2039742592931484,2030005558365485,
  2020115629485543,2011324581794376,2004903696465963,2001110309391693,1999341926310685,
  1998783362802602,1998819601609150,1999090824285312,1999405036212068,1999667114337679,
  1999844622953669,1999944443013573,1999990285304632,2000006046782896,2000008425735321,
  2000006481743336,2000004046767524,2000002247053726,2000001147750847,2000000544016763,
  2000000237913524,2000000094555398,2000000033305869,2000000009917956,2000000002199839,
  2000000000155048,1999999999824056,1999999999871657,1999999999942132,1999999999979719,
  1999999999994286,1999999999998774,1999999999999854,2000000000000024,2000000000000020,
  2000000000000004]
private def pvn_w1_4 : List ℕ := pCat pvn_w1_4_p0 (pCat pvn_w1_4_p1 (pCat pvn_w1_4_p2 (pCat
  pvn_w1_4_p3 (pCat pvn_w1_4_p4 (pCat pvn_w1_4_p5 (pCat pvn_w1_4_p6 pvn_w1_4_p7))))))
private def pvn_w1_5_p0 : List ℕ := [2000000325216873,1999999704276604,2000000417274154,
  1999999921458151,1999999810495501,1999999750891886,1999998745988054,1999999729390127,
  1999999688355872,1999999003853703,1999999703489783,2000000699961324,1999999399909003,
  2000000151337318,1999999773726454,1999999146944147,1999999018244034,1999999401648792,
  1999997232767134,1999997458979292,1999999233394996,2000000567425831,2000000211072995,
  2000002165042527,2000000186975909,1999999467882769,1999999378877490,2000000798409251,
  1999999086984261,1999999958028755,1999999170240085,2000000469572647,1999998642819490,
  1999998382233269,1999998392056917,1999998914142630,2000000844450672,1999999143184774,
  2000000430332163,1999998247311568,1999999923275864,1999998584974882,1999999752278460,
  1999999940896106,1999999143385457,1999999265189243,2000000270052124,2000001474460309,
  1999998759117460,2000001374516191,2000001119627312,2000001022998588,1999998390440738,
  2000001559531609,1999997782770423,2000000501761508,1999997323485742,1999999117901565,
  2000002609485437,1999999911708525,2000000552258269,2000001242670572,1999999857200826,
  2000001905110766]
private def pvn_w1_5_p1 : List ℕ := [2000002246809041,1999996184045908,1999997553812133,
  1999999612622329,1999998670015050,2000000743712207,2000001711743696,2000001675212728,
  2000000713659524,1999997374736024,1999998551892368,2000001067069990,1999998800606648,
  1999999376305585,2000000906139425,2000002082483005,2000002571413448,1999999990819361,
  1999997980476918,1999999594518665,2000002320923842,2000001944485114,2000000780315881,
  1999996293384930,1999994657318989,1999995893401660,1999997370968705,2000001767417735,
  2000006382782427,2000005856931588,2000006384706333,2000002781251590,2000002671396045,
  1999996904620325,1999997310624172,1999993885599836,1999991785896301,1999991285987886,
  1999992606426462,1999993465532405,1999997837743949,2000001150246647,2000002229770062,
  2000005655865176,2000005274334473,2000001760063507,2000005689445426,2000003577221961,
  2000000179863211,1999996607653962,1999995440872099,1999997148835852,1999992758089977,
  1999998518584538,2000000281156141,2000002507526528,2000010128046883,2000004680078727,
  1999997952765368,1999996085983961,1999996441769906,1999998621602524,1999996715860480,
  1999998306713892]
private def pvn_w1_5_p2 : List ℕ := [2000003461425824,2000002468131143,2000002302125021,
  2000004847882277,1999999096056306,1999993782832386,2000000645886061,2000000078254793,
  1999996897910383,1999996435106300,2000001809884184,1999995745723761,1999995319310327,
  1999996517237652,1999994172916622,2000000478167340,1999998007757223,1999998769016124,
  2000003841879807,2000000605587277,2000004276180948,2000003157421724,2000000488224837,
  2000002752021010,2000002578860545,2000006694435248,2000002655908174,2000005976230963,
  1999999530625481,2000001197860288,2000004946043522,2000003220706654,2000003438813489,
  2000006698416888,2000005028532350,2000004002041135,2000004652476671,1999998318951124,
  1999998178300620,1999997773317499,2000002239714886,1999997592169489,1999996954124071,
  1999996593114208,1999993466988731,1999988377286495,2000002959136677,1999991798285425,
  1999994674266641,1999999274267014,2000002302790459,1999997394656673,2000004482427535,
  2000003583589551,2000009713874240,2000004564345929,2000005537414243,2000003671405364,
  2000000101943262,1999994085628491,1999997163362380,1999995601144533,1999998195901302,
  1999996860480517]
private def pvn_w1_5_p3 : List ℕ := [1999999636427667,2000004609057261,2000005429329981,
  2000007348976072,2000004386531321,2000006259306285,2000004499640265,2000004376069099,
  1999997872832866,1999999129047621,2000005251408041,2000006847192574,2000003501483569,
  2000006778558686,2000007635662557,2000006254067526,2000004254527615,2000008692918894,
  2000006697951916,2000001712661035,2000008996756641,2000005409206952,2000003362796718,
  2000005601981234,1999999973671614,1999992859944184,1999995923990074,1999990298630319,
  1999997811650515,1999997299190694,1999993536651489,2000000580378436,2000001080204232,
  2000002654859527,2000001862983439,2000002713029631,2000002789018917,2000004430457960,
  2000007727867108,2000007272721267,2000003865280825,1999998241582040,1999993659245737,
  1999994750267113,1999995131479149,1999997861620853,2000002979871038,2000002606394272,
  2000003723660955,2000000958754733,1999994054706701,1999999759791000,1999998809255915,
  2000005015903062,2000005876994542,2000005375518434,2000001917551287,1999994149262301,
  1999994956991757,1999997435133457,1999997132337588,2000006114404381,1999997582297623,
  1999996941078345]
private def pvn_w1_5_p4 : List ℕ := [2000001218595448,2000001802934546,1999999870211366,
  1999998789034411,2000004270769480,1999999637426149,2000001010017353,2000000601097625,
  2000002838428154,2000000585855509,2000004955204980,1999994661492563,1999994848518780,
  1999993512930468,1999992632202073,1999997044305995,1999997682309421,1999994077392105,
  2000005931536792,2000003110376809,2000008589998701,2000002517624331,2000001221347537,
  1999994407304931,1999996355705209,2000000956097181,1999997615732237,1999997774924326,
  1999997008383893,1999995837599342,2000005021694906,2000002060368434,1999999180867375,
  1999997201217547,1999991515897906,1999994117696755,1999991856131454,1999995363805468,
  1999999840175465,2000003757662950,2000000578011955,2000006153932546,1999999472711589,
  1999996055943725,2000000715787239,2000001948313893,1999999667273930,1999993314203638,
  1999994926747738,1999998157040789,1999993992060201,1999997570141260,1999996191569180,
  1999988963481062,2000002304203450,2000002010810499,2000012163530400,2000004112191006,
  1999997553646813,1999994821945544,2000004995643107,2000004097081594,1999999794691568,
  1999997873906293]
private def pvn_w1_5_p5 : List ℕ := [2000001410400935,2000002853080808,1999991596552316,
  1999987779816477,2000007112195362,2000011799376563,2000008549656345,1999997638785712,
  1999988213423363,1999984825160148,2000006463074879,2000006525712161,2000010870058095,
  1999995046159528,2000003553963372,1999997324020806,2000006346814147,2000000372209061,
  2000001577172370,1999996522361168,1999999168152018,2000002596802443,1999998978624209,
  1999996563260659,1999996670974597,2000008425260790,1999998955214230,2000011962215789,
  2000005915156879,2000014299330281,2000002095336332,2000001443770720,1999988646206988,
  1999990547477452,2000015570512992,2000002753632184,2000007365300411,2000007770447997,
  1999990883511072,1999994610821096,2000003869523347,2000014770876614,1999988006908397,
  1999987833886117,1999993424886931,2000005016049991,2000014860777066,1999992926733299,
  1999997172107161,1999992327135344,2000016987932959,1999997139032024,1999984782548808,
  2000005455824101,2000009529213983,1999993191677891,1999993390111705,2000002380971223,
  1999990327267629,2000009043529160,1999999684202893,2000003680393919,2000012382955431,
  1999969801642843]
private def pvn_w1_5_p6 : List ℕ := [2000008099443143,2000001653412831,2000020257187297,
  2000003788698206,2000040266756938,1999967861814804,1999977066044310,2000013095511696,
  1999990567565593,2000018407051695,2000008461790293,1999979745602367,1999997674441097,
  2000011437085558,2000030249815493,2000033376452387,1999986591622759,1999976093083049,
  2000024977096568,2000030404210573,1999983092429223,1999968111583566,1999990935311764,
  2000000504590229,1999997255180726,2000003459831395,2000005546189843,1999989235115904,
  1999976390165057,1999990007191442,2000016112533017,2000023895181210,2000005829874078,
  1999982079600982,1999973523030785,1999981909853965,1999994308851256,1999998783128518,
  1999992217305009,1999978373368625,1999956887304694,1999930263640576,1999882391816778,
  1999853243683973,1999797756374241,1999960038921548,2000111179469347,2001208468866846,
  2002173147629296,2005946814685364,2008903742961561,2018006767554099,2025068420304103,
  2041413573664273,2056205066380417,2078576473260531,2104310649159628,2130210744912989,
  2162652531873588,2192775947676961,2220975044306592,2250287520688866,2272082898950805,
  2286899560835779]
private def pvn_w1_5_p7 : List ℕ := [2298432347467025,2301177775456803,2293536223770693,
  2281512116677811,2265588193509723,2242110193308611,2213897189520752,2186853820158664,
  2161505559578239,2135158850808110,2108286376402306,2084568950150523,2066453723886306,
  2052948896398133,2041389794352734,2030175094113194,2019627284020585,2010936306117508,
  2004853238383482,2001267748742102,1999539309554029,1998954501001107,1998962636962819,
  1999209047423492,1999493265179200,1999722406693136,1999872175990847,1999954093874651,
  1999991126999643,2000003911499363,2000006066985499,2000004757100433,2000002981015086,
  2000001642866602,2000000823408937,2000000379335012,2000000160430168,2000000061709607,
  2000000021200010,2000000006280683,2000000001474116,2000000000192138,1999999999953274,
  1999999999952319,1999999999977497,1999999999992076,1999999999997763,1999999999999506,
  1999999999999925,1999999999999995]
private def pvn_w1_5 : List ℕ := pCat pvn_w1_5_p0 (pCat pvn_w1_5_p1 (pCat pvn_w1_5_p2 (pCat
  pvn_w1_5_p3 (pCat pvn_w1_5_p4 (pCat pvn_w1_5_p5 (pCat pvn_w1_5_p6 pvn_w1_5_p7))))))
private def pvn_w1_6_p0 : List ℕ := [2000000421671734,1999999670139658,2000000244229679,
  2000000209159537,1999999779452300,2000000392366068,1999999336655847,1999999040120864,
  1999999767314221,1999999795807118,1999998550186409,2000000011665100,1999999975730959,
  1999999817383272,1999999950467614,2000000489383416,1999999010599502,1999999575669455,
  1999999952217153,1999999104447958,1999996720896736,1999998525319088,1999998187094814,
  1999999413781087,2000000436390362,2000002246111544,1999999859692401,2000000310606857,
  1999999472530265,2000000623588297,1999999563500909,1999999246612991,2000000271776373,
  1999999413210626,2000000749489100,1999997764921626,1999999017010181,1999997844931629,
  1999999902729347,1999999803779816,1999999647134029,1999999998177209,1999999082291529,
  1999999151962996,1999998550464594,2000001162034627,1999998277390049,1999999279711984,
  1999999290226063,2000001790062388,1999997577420496,2000001737891384,2000000030882542,
  2000001131691852,2000001406647636,1999998624664714,2000001355000681,2000000733117496,
  1999997475023174,1999998643986612,1999999900971037,1999998571412552,2000002213269429,
  2000000847141731]
private def pvn_w1_6_p1 : List ℕ := [1999997969436046,2000001846448987,2000002898482848,
  2000000834389822,1999999881072275,1999998142841541,1999998328586950,1999998654732482,
  1999997554950486,2000001512701920,2000002982866648,2000000342018889,1999999392108761,
  1999999346958914,1999999718699308,1999999489577127,1999998697314173,1999998174246545,
  2000001818879987,2000002730252644,2000001624616020,1999999882598164,1999998012469230,
  1999999609703976,2000003241385211,2000001424425264,2000002114781807,1999997440379024,
  1999996735083034,1999992893631691,1999996915919255,1999999755787586,2000002713056948,
  2000005545418246,2000006810396663,2000004499764380,2000003423854775,2000002019205255,
  1999998138628260,1999996480543604,1999994996522914,1999989860262051,1999992756098454,
  1999992313864235,1999992753445666,1999998296260639,2000000837540117,2000004413449340,
  2000000687627893,2000004867797103,2000007308671367,2000002308474351,2000004324793317,
  2000000435281595,1999996376593355,1999998051538434,1999995112118988,1999993043808893,
  1999995203383287,2000001581835569,2000008324039268,2000005721138208,2000000690828413,
  2000001230813768]
private def pvn_w1_6_p2 : List ℕ := [1999999399218694,1999993732674336,1999998908075321,
  1999997830615022,1999996908652419,1999999956303797,2000008046633111,2000002658933235,
  1999997905253863,2000002678526014,1999997846855628,1999998696349579,1999998716372937,
  1999996364750211,2000002125056389,1999997662863739,1999995839295421,1999997387623643,
  1999994176643934,1999997770727764,1999995736823464,1999999763507564,1999996787761784,
  2000002679148771,2000002986101961,2000001509306747,2000003252876747,2000001073442002,
  2000000127849642,2000005311307652,2000006367048527,2000001951173955,2000004638958113,
  2000001177666827,2000002713335506,2000001726866428,2000004634104160,2000002545863875,
  2000005092517388,2000006227227841,2000009835812052,1999996202521307,2000005410800845,
  1999998668361773,1999996798547580,2000001370366321,2000004540978701,1999992398763143,
  1999996852110705,1999994889248344,1999995953470412,1999992092045500,1999994348172426,
  1999996676466499,1999998587711141,1999994827354448,2000000699116830,2000001852651008,
  2000003466749002,2000005733956101,2000006706600701,2000008934958016,2000003034646843,
  2000001038650869]
private def pvn_w1_6_p3 : List ℕ := [1999997368622000,1999998691665736,1999995660217768,
  1999995893267268,1999995556353515,1999998632314344,2000003290897456,2000004990714159,
  2000001853916554,2000006998427445,2000009366490271,2000005572497531,1999999855417499,
  2000000462820110,2000004298231043,1999998674886240,2000004983766013,2000007592809997,
  2000003188440861,2000005556616551,2000009886783375,2000002734609703,2000008943130171,
  2000005578927638,2000004009714059,2000008061926042,2000003841118442,2000008605501016,
  2000006962465644,2000000363496469,1999995878316942,1999995837236922,1999995705230587,
  1999993788713810,1999994526323584,1999995837178573,1999997327654037,2000000646446814,
  2000001221765873,2000001793027868,2000001196540502,2000000114236535,2000005717647317,
  2000008369839168,2000006586749369,2000007815877792,1999997912266858,1999998483739242,
  1999994173314579,1999993368301241,1999997262464706,2000000632999337,2000004753794323,
  2000002643505002,1999998515906783,2000000557286342,1999992863881736,2000000881343999,
  2000004092759412,2000004605198131,2000008162123473,2000001879615116,1999995776613129,
  1999992885724536]
private def pvn_w1_6_p4 : List ℕ := [2000001637854254,1999998801979801,1999998520611328,
  1999998293544706,2000002471473765,1999996631747432,2000002071385436,1999999392718596,
  2000000215565895,2000003233193218,2000000173390166,1999997884992024,2000004397183587,
  1999998576958604,2000007761831566,2000000612484316,1999998165676308,1999994204648169,
  1999996036772365,1999994848400230,1999992502171316,1999995903612945,1999995647407373,
  1999999463892110,2000008756016148,2000004893800023,2000004575452006,1999999814867257,
  1999995292694500,2000001538023630,1999998775153874,1999998305236296,1999994743702042,
  1999996456709264,1999999079443962,2000004515019449,1999999376545391,2000001980584681,
  1999998610882980,1999991404308929,1999993624400527,1999993003054718,1999993569005790,
  1999997594756528,2000003135035140,2000006104787608,1999998381028819,1999997268603155,
  2000005710995258,1999996535641018,2000004584179141,1999995951421089,1999996127984974,
  1999995033519388,1999998507301398,1999997049621419,1999996311931829,1999989281626925,
  1999990747053346,2000003063035210,2000009041730952,2000005005503986,1999998926279537,
  1999996708980848]
private def pvn_w1_6_p5 : List ℕ := [2000008241516976,2000000409883619,1999995534988040,
  2000002009750342,2000010821642189,1999995851106912,1999996703736562,1999984498895086,
  2000000944983123,2000006215828180,2000018534484273,1999998936527522,1999990974734406,
  1999987689403201,1999998762551516,2000004675395820,2000004624489404,2000003559199104,
  1999998226436965,2000003039283989,2000000974387475,2000008768566997,1999992122194122,
  2000004058477512,1999998818647912,2000003569838270,1999995146374331,1999998943752154,
  2000000323182489,1999994265580591,2000009617366447,1999997795974108,2000007788689321,
  2000022696653264,2000003354452293,1999999269213310,1999992984253989,1999998818135071,
  1999993046610307,2000013181910463,2000015703977354,1999993608976532,1999997127698150,
  1999994272970705,2000017508345930,2000000236548691,1999995469052226,1999983545531839,
  1999993785985847,2000016338358628,2000000966810323,1999986552448678,2000002829569458,
  2000014826414942,1999988194823306,2000000456496818,1999999511000461,1999996634854704,
  2000014953823564,1999979490290109,2000014354355026,1999985931345567,1999998932441357,
  1999991276627044]
private def pvn_w1_6_p6 : List ℕ := [2000031257541168,1999983544850045,1999997491990857,
  2000011169520197,1999965495528634,2000012414115109,2000031963092576,2000009568823740,
  2000011892275525,1999986846695093,1999979710516110,2000004056935593,2000007956163663,
  2000010593459068,2000000362427828,1999971577064615,1999994482413967,2000045844759541,
  2000030190658108,1999982591088325,1999991430448340,2000026340280157,2000021389353934,
  1999995063708367,1999986932766442,1999988272039941,1999985731261148,1999992040294426,
  2000008295228296,2000010937756009,1999991573702379,1999974633858314,1999983132094562,
  2000008318900174,2000022428180918,2000013947124414,1999991360551619,1999981744857000,
  1999974058351502,2000003603348035,1999968375983431,2000054772025331,1999880108071821,
  2000178858226227,1999615922304945,2000471747440334,1999050267252422,2000908077328119,
  1998397969728644,2001247770457192,1998961894659348,2001681259764581,2003102470109088,
  2005214500683559,2012811610423232,2018967024668547,2031002275558516,2048008906335300,
  2065616772887983,2090658801675383,2119617523418209,2148105545073757,2180585309420816,
  2213980552925029]
private def pvn_w1_6_p7 : List ℕ := [2241773845527588,2266239183969630,2287863765468899,
  2300350164491226,2302750171119433,2299657761104205,2290794540929460,2272887460366460,
  2247907631425124,2221287668273993,2195020499613047,2167433108202564,2138175788711230,
  2110212721523268,2086942639317112,2069049193656530,2054631330326583,2041583523325798,
  2029303737723958,2018514246535440,2010129150629335,2004463376997464,2001176629973827,
  1999607635018539,1999091851562850,1999115471430595,1999343506726177,1999591782024506,
  1999782883053137,1999902737381390,1999965952516861,1999993628781901,2000002886768496,
  2000004343197581,2000003343313514,2000002053026472,2000001103009074,2000000535594425,
  2000000237765761,2000000096592235,2000000035686328,2000000011823871,2000000003418412,
  2000000000810608,2000000000128289,1999999999994709,1999999999985435,1999999999992757,
  1999999999997480,1999999999999306,1999999999999846,1999999999999974,1999999999999998]
private def pvn_w1_6 : List ℕ := pCat pvn_w1_6_p0 (pCat pvn_w1_6_p1 (pCat pvn_w1_6_p2 (pCat
  pvn_w1_6_p3 (pCat pvn_w1_6_p4 (pCat pvn_w1_6_p5 (pCat pvn_w1_6_p6 pvn_w1_6_p7))))))
private def pvn_w1_7_p0 : List ℕ := [2000000490959859,1999999728257981,2000000029564513,
  2000000384425735,1999999695937450,2000000398987222,2000000129170925,1999999236599318,
  1999999083391244,2000000349065099,1999999002200822,1999999120644677,1999999678399571,
  2000000052117732,1999999318990861,2000000544333551,2000000154161393,1999999507585674,
  1999999012449746,2000001103230618,1999998897292720,1999998319793430,1999997673446721,
  1999998514244907,1999997303433330,2000000243337221,2000000703277733,2000001442297096,
  2000000134970910,1999999759901015,2000000900382695,1999999259282772,2000000595831714,
  1999998451157735,2000000743561979,1999999766732501,2000000207520615,1999998922106591,
  1999997934830796,1999998933191945,1999998845775968,2000000046130311,1999999036784746,
  2000001229829246,1999998180997042,1999999368133825,1999998834832322,2000001596140382,
  1999996818087424,2000000301538371,1999999825706314,1999999083250843,2000000688494861,
  1999998643827055,2000000822201551,2000002095381963,1999999393589379,1999999919607473,
  2000002533887709,1999999265300884,1999999598575951,1999999806062526,1999996667646162,
  1999999634301064]
private def pvn_w1_7_p1 : List ℕ := [2000002058116335,1999999392761934,1999999184906933,
  2000000421160425,2000001553684369,2000002995225123,2000000197583559,1999999753239807,
  2000000235556984,1999997263046046,1999996903021775,1999999491606999,2000001665225561,
  2000001379654195,2000000925024937,1999999027207843,2000000289690743,2000000578231625,
  1999998391620549,1999997843896659,1999999317695061,2000000284518091,2000004335576947,
  2000000403741700,2000000165470251,1999997597911375,2000001057361210,2000000993236198,
  2000002693036255,2000002814045148,1999999513555231,1999995629968702,1999995122441435,
  1999995188125457,1999996949689710,2000001779374032,2000004547541403,2000004136377548,
  2000007452526595,2000003690220248,2000002430190693,2000002833468237,1999997133049496,
  1999996266498833,1999992563348607,1999993326107406,1999990559494436,1999989722129512,
  1999998542668285,1999998119143377,1999999044567083,2000003619033778,2000002497443413,
  2000004905363050,2000006628267475,2000003838940973,2000001698651073,2000000027098381,
  1999999930491961,1999997000008616,1999991097521338,1999991395895951,2000002357109043,
  2000002271357451]
private def pvn_w1_7_p2 : List ℕ := [2000004420436999,2000005569603223,2000003664183778,
  1999997069972219,1999998791746314,2000001274160626,1999991841312585,1999996335414967,
  2000002055829841,2000001233621733,2000004971747230,2000000391429395,2000001279680680,
  2000002553742553,1999996290467871,1999999458529582,1999997515293658,2000001220092561,
  1999997504151188,1999999546319983,1999996232325147,1999994930473993,1999997836011168,
  1999995776564265,1999995487807081,1999998672419578,1999999081325968,1999999504809126,
  2000005821239257,2000000518249694,2000000834602487,2000000569601402,2000004102111660,
  2000003010878272,2000005885819421,2000002606405405,2000005248001958,1999997489056488,
  2000008439519264,1999999491696600,2000000301619853,2000006261903150,2000007776928034,
  2000001395334126,2000010414605859,2000002239269771,1999998483551323,1999999113474088,
  2000003506125213,2000000754833893,1999998843568101,1999996012111067,1999999509842272,
  1999994365243945,1999992383059715,1999995285781017,1999994792717025,1999996295460618,
  1999994217411065,1999998649266292,1999998424208281,2000000856471004,2000001654006520,
  2000006926081248]
private def pvn_w1_7_p3 : List ℕ := [2000008193879851,2000006744505555,2000003874729032,
  2000001795319117,1999998905317285,2000000112150789,1999995304716208,1999992880767652,
  1999997324985192,2000000608699253,2000001239223391,1999997916739202,2000007776881777,
  2000009115473778,2000004159509798,2000005411957042,2000005403926335,1999996265955011,
  2000004083152507,2000002586167783,2000001552332620,2000007228132197,2000002972488584,
  2000007141892424,2000006736715969,2000005499135392,2000007366676242,2000006485223434,
  2000003753129753,2000004822118291,2000009371206133,2000008970949973,2000004384401591,
  2000001726338327,1999998355810135,1999996770127544,1999995707201292,1999993390470896,
  1999994787484719,1999995163147114,1999995742352507,2000003225677839,1999998569822988,
  2000001558015815,1999999117893408,2000000638602044,2000006583770471,2000007550435316,
  2000008025169063,2000005955983293,2000000877213758,2000000140801996,1999990299717880,
  1999996158840170,1999997786052436,1999998954901845,2000005827646319,2000001720997769,
  1999999495271707,1999996187592132,1999998472369843,1999995826987199,2000005498721872,
  2000008777251733]
private def pvn_w1_7_p4 : List ℕ := [2000006379231996,1999995798807535,2000000258775104,
  1999997279832854,1999997357861652,1999999782522220,1999998458890406,1999998028831574,
  2000003388293417,1999994510957367,2000003086449125,1999998909121701,2000002039396147,
  2000001297881740,1999999712611863,1999998626734702,2000001169850030,2000006374817080,
  2000002892756974,1999999738211820,2000000751020182,1999993953984651,1999996985718556,
  1999995645968583,1999990576976557,1999994987447142,1999994401344273,2000003205234048,
  2000006779645350,2000006047426066,2000000294691060,2000000643622587,1999998165033184,
  2000002813833068,1999998656766652,1999993505021558,1999998036483400,1999996799957241,
  1999998906855939,2000003472897054,2000002569961822,2000000001388602,1999996075915072,
  1999995127554039,1999995055632443,1999984388436650,2000000670112394,1999998877384559,
  2000002619407378,2000000613980192,2000000207670977,1999999396000951,2000003411521977,
  2000001393074325,1999999644652944,1999997348483790,1999993954921920,1999998000595965,
  2000002622250473,1999994364010816,1999990504775501,1999985928401390,2000000871319386,
  2000007591238429]
private def pvn_w1_7_p5 : List ℕ := [2000002849258648,1999994145412686,2000010935381255,
  1999999060622559,2000001780124910,1999993693212075,2000006961270679,2000004324657087,
  2000007686365945,1999992679432396,1999986070704676,1999993129866153,2000008391351972,
  2000015183612679,2000002861603626,1999995841520228,1999987424929988,1999999401268598,
  1999995929564766,2000010803067748,1999996619844434,2000001765696327,2000001839038173,
  2000005967113381,2000001565754091,1999995980280795,2000007540618278,1999995046047691,
  2000003639464581,2000002192503343,1999989199042528,2000006374688679,1999997737818300,
  1999995903058795,1999997883860930,2000016953099281,2000011960493333,2000005463141204,
  2000012600853439,1999987151609629,1999994807787790,1999995242162880,2000018668235417,
  2000006749373648,1999995639963261,1999996623709776,1999999338876827,2000016153514675,
  2000006696666985,1999983086818933,1999984494285949,2000016849224875,1999995939172561,
  1999990076420738,2000009860049488,1999990434309359,2000019996681656,1999980041043263,
  2000008266009720,1999994961469459,2000009475188009,1999984271994225,2000019489597389,
  1999993485475206]
private def pvn_w1_7_p6 : List ℕ := [1999972361677999,2000022934829349,1999991962676352,
  1999997531968087,2000024687986863,1999986696558903,1999982223907086,1999996187697354,
  2000003261985996,2000027631091277,2000021011977311,1999996326269029,1999992154479500,
  1999985393870799,1999996140255342,2000027300215073,2000008606612711,1999962869738249,
  1999982796266071,2000035410657374,2000030623465323,1999993857781777,1999994256817891,
  2000017591393448,2000020135061541,2000007777977142,2000000268348399,1999991994149139,
  1999980935210644,1999984061688970,2000003396083498,2000014951802945,2000000175394700,
  1999980324598496,1999972321979403,2000003272821255,2000000974367027,2000050845900493,
  1999942831228120,2000099252442703,1999783418126954,2000313970723414,1999478495187748,
  2000751885363250,1998973438867273,2001249316027719,1998610290321564,2001207023802996,
  1999091797651760,1999973555193190,2000384092316297,1998551076707412,2000806979439939,
  1999801964797995,2000572629900035,2004551871727213,2006453609556246,2013277433214481,
  2024162822641067,2035559701787340,2053591450941855,2077452985297027,2102327887129647,
  2131855197029541]
private def pvn_w1_7_p7 : List ℕ := [2166287624313914,2198813228532162,2228754205795719,
  2258397262180455,2282956174503990,2297573898813316,2304484668959229,2305873952779459,
  2298909156771012,2281840727029381,2258313864579822,2232900355168621,2206333091291422,
  2177245630069839,2146433923823266,2117396996032487,2093219252761893,2074173310312980,
  2058400918308049,2044138079233516,2031008424680469,2019699544090740,2010975696961377,
  2005049188027959,2001555338139269,1999837732724083,1999227577676809,1999195101595698,
  1999389259965419,1999616128382523,1999793857068555,1999906153768362,1999965839346062,
  1999992370519249,2000001603282858,2000003393331953,2000002739435117,2000001703459730,
  2000000914496269,2000000440491458,2000000193182288,2000000077418384,2000000028255196,
  2000000009298040,2000000002704709,2000000000667348,2000000000125052,2000000000009617,
  1999999999994808,1999999999996674,1999999999998773,1999999999999653,1999999999999923,
  1999999999999988,1999999999999999]
private def pvn_w1_7 : List ℕ := pCat pvn_w1_7_p0 (pCat pvn_w1_7_p1 (pCat pvn_w1_7_p2 (pCat
  pvn_w1_7_p3 (pCat pvn_w1_7_p4 (pCat pvn_w1_7_p5 (pCat pvn_w1_7_p6 pvn_w1_7_p7))))))
private def pvn_w1_8_p0 : List ℕ := [2000000537439028,1999999873160808,1999999792439949,
  2000000476734678,1999999772197294,2000000062635989,2000000454789122,2000000181704214,
  1999998728345554,1999999957664166,1999999827379328,1999999272412247,1999998882515475,
  2000000083161827,1999999338534937,1999999677229957,2000000001560666,2000001058809700,
  1999998637932758,1999999904472276,2000000229133258,2000000442043893,1999998128855217,
  1999999271400901,1999997553136978,1999997657244253,1999998156574330,1999999651096972,
  2000001675405166,1999999738918815,2000001259819477,1999999325163531,2000001173452477,
  1999999647333459,1999999659138388,1999999608490826,1999999600485638,2000000945816386,
  1999999605907655,1999999692873065,1999997500072797,1999999845986899,1999997721168242,
  1999999985145421,1999999108775506,2000001851171916,1999997140353505,1999999717630612,
  2000000641340166,1999998287315932,1999999985068242,1999998664009665,1999999293903816,
  2000000824591427,1999998820337319,1999998303626776,2000002227485227,2000000154480255,
  1999999256218828,2000002001509743,2000000084760870,2000000343321279,2000002142248409,
  1999998651967679]
private def pvn_w1_8_p1 : List ℕ := [1999997157720627,1999999591160961,2000000040329705,
  2000000781487560,1999998981936966,1999998573275947,2000001875331457,2000001783567042,
  2000000840430117,2000001492677318,2000001625376169,1999998436319154,1999997471327551,
  1999997266102064,1999999387780881,2000001769217348,2000000971678595,1999999269435347,
  2000001531841087,1999999418017523,2000001628434781,1999997516771946,1999998065294356,
  1999997942704320,2000002097186189,2000002698647287,2000000826234018,1999999805084181,
  1999999353887061,1999998698994527,2000001115893919,2000003717420383,2000002661115562,
  2000000085989390,1999999324475772,1999993621958643,1999994842768775,1999997303217587,
  1999997156728814,2000003851952542,2000003899576883,2000005600292315,2000004798247436,
  2000004363284495,2000005053119502,1999997797880428,1999998516231558,1999998213449964,
  1999990526894177,1999990834502586,1999992133474242,1999992698268219,1999996802064659,
  1999998463513380,1999999622227889,2000001539750400,2000004542216580,2000005970991716,
  2000006008636942,1999999714678456,2000004896903348,2000003927367167,1999996633507264,
  1999991542034783]
private def pvn_w1_8_p2 : List ℕ := [1999994161361504,1999996442351312,1999996108672186,
  2000007078398503,2000005953133666,1999999314444250,2000004632050505,2000001118295173,
  1999998558333100,1999996400617321,1999992624911095,2000000961946444,1999999438990800,
  2000002625782107,2000001091145887,2000004316706035,2000001047463114,1999998980495308,
  1999999887123336,1999997452526413,1999999315285551,2000001090702715,1999998345553707,
  1999996390161921,1999999703384433,1999993947808898,1999997353833785,1999996216742513,
  1999996006024274,1999995152751667,2000001894376132,2000000308022812,2000004390840736,
  1999996984403950,2000005233029146,1999997787632452,2000003603434798,2000006810426009,
  2000003205219375,1999999473909462,2000009476498053,2000000060195373,2000000649470650,
  2000003432944688,2000002956985007,2000001250453748,2000007838236683,2000007912589411,
  2000006069269393,1999999420370805,2000000919955401,2000004206362355,1999999585365323,
  2000000617933759,1999999389086834,2000000595414052,1999995269338725,1999995090358427,
  1999994396294475,1999995497921602,1999993829777893,1999994625600284,1999996429293346,
  1999997436321541]
private def pvn_w1_8_p3 : List ℕ := [1999996118683570,2000000133895846,2000002217056195,
  2000006132089370,2000009161676223,2000004877810422,2000004295451530,2000002606607509,
  2000004485946150,1999996023143686,1999992627882760,1999998520545336,1999999317394803,
  1999992326821320,2000002420232209,2000001880784702,2000002429290222,2000010690265720,
  2000004763967235,2000005506726643,2000002792946141,2000000373702264,2000002534188610,
  2000002216955858,2000002321336552,2000004696963434,2000005644856964,2000004418456000,
  2000005987160079,2000009106875722,2000006006257427,2000003394693316,2000004950619737,
  2000006877493824,2000009494290733,2000008392208757,2000003835512169,2000005275778543,
  1999997050998723,1999999372061934,1999996027331290,1999993002291401,1999994394315947,
  1999994064897799,1999997996456745,2000001323228983,1999998284413423,2000000558540596,
  1999996145477146,2000004222727253,2000005113709151,2000005057353259,2000011490846524,
  2000005304590916,2000002669049414,1999997204882493,1999995541758143,1999991629873539,
  1999999993815998,2000000718662041,2000003062651857,2000001000673436,2000003152433497,
  1999992875036387]
private def pvn_w1_8_p4 : List ℕ := [1999993850850507,2000003039694354,2000006137155895,
  2000004436901563,2000006619790825,1999995798798235,2000002992165976,1999996191996464,
  1999997956854787,1999999135034318,1999999048703220,1999999367642428,1999998829096033,
  1999999389123805,1999998619068668,2000001632903038,2000004171711957,1999996401490040,
  1999999682145548,2000001196968896,2000000749500860,2000007167662194,2000001170178428,
  2000001351110152,1999998633668596,1999998219001465,1999996109248329,1999995502743384,
  1999988953683476,1999993176153819,1999997600852023,2000002950734026,2000008094397549,
  2000000843016919,2000000353569448,2000003407108173,2000000658099626,1999999785835321,
  1999998341986891,1999995299701022,1999997048330545,1999993313666911,2000007683490909,
  1999997660577324,2000001753059153,2000002646261210,1999998115163709,1999991164151181,
  1999991304875728,1999992104052883,1999997866449446,2000001150258798,1999999349286901,
  1999999869533696,2000000992260445,1999999290690300,2000006333626706,1999999972027787,
  1999998199551418,1999993074387538,1999999868617306,2000002093376132,2000003603522523,
  1999979193458758]
private def pvn_w1_8_p5 : List ℕ := [1999994014369574,1999996346823349,2000003329448033,
  1999994905579926,2000004916435104,2000003939664924,2000004041642481,1999998959455088,
  1999995148078768,2000002123405886,2000008626389810,2000011758866608,1999992069483617,
  1999989174402253,1999986213122434,2000010930275018,2000006200191225,2000011145315447,
  1999996613452480,1999991142767064,1999995016950168,1999999364421202,2000005952756926,
  1999992770482855,2000005899474932,2000003983382644,1999997656812870,2000010124710896,
  1999993799315286,2000002828598741,2000004180819847,2000001631902055,1999993209835672,
  2000001939985359,2000007105013206,1999984910009565,2000002843685241,1999996635270784,
  2000009862182687,2000008966314095,2000018227747768,2000008511096000,1999986943509022,
  1999994266568205,2000001785605417,2000012064074540,2000008295855951,1999995935254252,
  1999984886898006,2000019451840701,2000018755897924,1999978397026895,2000007883973482,
  1999983544315449,2000015908657122,1999983897800777,2000003376809092,1999995444574623,
  2000015837050203,1999986027110865,2000000820511143,2000015863559873,1999971990734618,
  2000015518003681]
private def pvn_w1_8_p6 : List ℕ := [2000013663065796,1999978655789494,2000007663054185,
  1999995814243214,1999984195037747,2000010706518169,2000010379451367,2000004918674086,
  1999994894421756,1999976621703512,1999994074426412,2000017221622436,2000016795427105,
  2000020422318573,2000005952336889,1999971854881659,1999987733840049,2000032897409452,
  2000016291417612,1999967012482303,1999975474590469,2000019457180395,2000025416921132,
  2000002673668790,1999998578819555,2000010797733990,2000015238083858,2000014177880638,
  2000012167262611,2000002673629199,1999980828742306,1999982247565997,1999986262375260,
  2000032099250362,1999973599801955,2000052221106030,1999857288919382,2000183568172537,
  1999685006319027,2000513158970844,1999298509237424,2000954610346871,1998802032082435,
  2001294350615356,1998739278194080,2000928079202114,1999635883107691,1999650621877149,
  2000927827773837,1998860639248951,2000694157720885,1999991094390328,1998916472747489,
  2000792526585873,1999110071698729,1999133899204277,2001274039072044,2000868972473747,
  2003595842946964,2009987834474420,2016044288057699,2026773542326048,2044230168678760,
  2063722795146489]
private def pvn_w1_8_p7 : List ℕ := [2087256250117046,2118118270599690,2151353503436118,
  2183488120724438,2216949377896372,2250021101913965,2276312213477316,2294064212889698,
  2305779045035575,2310735540589841,2305373556263738,2289660431206099,2267906275094861,
  2243559865604138,2216516876077291,2185990743740814,2153838641105568,2123903229629199,
  2098887614390036,2078715964162437,2061633790842629,2046215046938484,2032288265392092,
  2020513334569567,2011523364124264,2005427345240645,2001815649561156,2000016824585047,
  1999351849381602,1999280734295846,1999445585468349,1999649948689823,1999811592321414,
  1999913763908777,1999968038366932,1999992241492603,2000000797758228,2000002610604789,
  2000002178359114,2000001358121501,2000000723094932,2000000343360830,2000000147911945,
  2000000058122042,2000000020805039,2000000006735078,2000000001942637,2000000000484718,
  2000000000097666,2000000000012436,1999999999999054,1999999999998724,1999999999999487,
  1999999999999856,1999999999999970,1999999999999996]
private def pvn_w1_8 : List ℕ := pCat pvn_w1_8_p0 (pCat pvn_w1_8_p1 (pCat pvn_w1_8_p2 (pCat
  pvn_w1_8_p3 (pCat pvn_w1_8_p4 (pCat pvn_w1_8_p5 (pCat pvn_w1_8_p6 pvn_w1_8_p7))))))
private def pvn_w1_9_p0 : List ℕ := [2000000542319979,2000000093530440,1999999607713591,
  2000000407625944,2000000015397026,1999999845031423,2000000031590417,2000000996961110,
  1999999392508985,1999999355064957,1999999768934859,2000000153653030,1999998804487161,
  1999999523374782,1999999486780973,1999999872235525,1999998573333728,2000000935629161,
  2000000194617530,1999999772063726,1999998755926873,2000001132509708,1999999710797561,
  1999999732866082,1999999350819741,1999998380935551,1999998379423652,1999996262522140,
  1999999488536556,1999999056219584,2000001294032274,2000000112221177,2000000274623192,
  2000000742151233,2000000065821272,2000000683258044,1999998908413263,2000000156120633,
  1999998965537355,2000001831325832,1999999046696353,2000000249296255,1999997826650731,
  2000000258270355,1999996872546823,1999999138725430,2000001584795369,1999998331974186,
  1999999662092513,1999999560578810,1999999144043423,2000000249308917,1999999233444495,
  1999997603438249,2000001113991599,2000000033269927,1999997314228566,2000000544877148,
  2000000392197701,1999999026984673,2000001403541663,2000000495994023,1999999079187177,
  2000002077678260]
private def pvn_w1_9_p1 : List ℕ := [2000001692274467,2000000088084070,1999998558082483,
  1999997555521887,2000000437651805,2000000742143962,1999998682141018,1999998520667833,
  2000000991659587,2000000316265290,2000000814803272,2000001890204502,2000002111637900,
  2000001216562315,1999999568921021,1999995492467203,1999999409316985,1999998612467918,
  2000001592617401,1999999623616489,2000000453359641,2000000373637497,2000001531997010,
  2000000928262962,1999997822749977,1999996761246239,1999999467932259,2000001016421054,
  2000001561907612,2000001835953329,2000001027364539,1999997047255405,2000000029932818,
  2000000950606519,2000001018901200,2000005555794924,2000000733193820,1999999625900368,
  1999996648422692,1999994270145171,1999995686114958,1999995619159112,2000002166911041,
  2000002748574795,2000001740756492,2000007953654929,2000005648536602,2000002022856562,
  2000003619508700,2000001127998394,1999997979289392,1999994746285476,1999991942752485,
  1999990240417530,1999993117441224,1999993060056552,1999998337307546,1999995798644990,
  1999998528184148,2000005262784778,2000005651770933,2000002087552058,2000002117541930,
  2000009245320788]
private def pvn_w1_9_p2 : List ℕ := [2000003097412015,1999998250129544,2000000503487032,
  1999990388452819,1999991430280310,1999999269330173,1999999785252705,2000004968911951,
  2000000313880200,2000005325297465,2000003695830045,2000001519804431,1999995690177922,
  1999995560329329,1999998241796295,1999996949708651,2000000310967336,2000002463695368,
  2000002183781682,2000002245832658,2000003453728012,1999996225832395,2000000643264514,
  1999999207720572,1999999613603309,1999998750929884,2000001233011502,1999994729028498,
  1999999859714573,1999994375090127,2000000245763049,1999991132231803,1999996580726794,
  1999998730506610,1999998842150116,2000000056162328,2000006232331417,1999994900074488,
  2000001216266061,2000005108668987,2000001639464241,2000001378551398,2000007056632914,
  2000002847994216,2000002921273387,2000002880473223,2000003114295232,2000001107863373,
  1999998478867934,2000007376737624,2000007822490512,2000006322484827,2000002088550998,
  2000004248918381,2000002402671750,2000001201138838,2000000540045532,2000002142468503,
  2000000884996196,1999998448750136,1999995884285955,1999997316391526,1999994494413608,
  1999993507044963]
private def pvn_w1_9_p3 : List ℕ := [1999995590714031,1999994024541263,1999997101177362,
  1999994873810301,1999996581858838,1999997161211062,2000003806169323,2000007790493913,
  2000004917714453,2000002077064169,2000011965172605,2000003622977188,1999996894507011,
  2000002152253178,1999994580135409,1999997005591876,1999997050052768,1999995195648370,
  1999998845442708,2000001214851679,2000004623248866,2000007715249351,2000006422744322,
  2000003922409930,2000003425423777,2000002777801451,2000000140807908,2000002186980246,
  2000004723018284,2000002624829704,2000003118525237,2000006540515822,2000006586064416,
  2000009637022196,2000001872866876,2000005495328075,2000005569394978,2000006376600449,
  2000010330069383,2000007589043687,2000005539619704,2000004584236920,1999999435399805,
  2000001493756039,1999994076846142,1999995011270447,1999992699605933,1999993688816760,
  2000001977698933,1999996739662192,1999998826019050,1999998205161112,1999999757299897,
  1999998771768928,2000007106968148,2000006125992235,2000009509510893,2000007009962779,
  2000004880073770,1999994545642431,1999995457679048,1999997033105414,1999995454222872,
  1999999415491157]
private def pvn_w1_9_p4 : List ℕ := [2000009222488796,1999998063296019,2000000136154438,
  1999991740989655,1999997481018091,2000003660058069,2000004173207679,2000004902200319,
  2000003408429072,2000001524518817,1999998745986689,1999998233999601,1999999513372121,
  1999996320173364,2000001833946201,1999999290671322,1999994728823916,2000002012685686,
  1999999316083225,2000002885403995,2000000108232352,1999998296154548,1999998083353651,
  2000002705552847,2000001968156488,2000005355007620,2000001987244437,1999999254773784,
  2000002251517169,1999998153885189,1999997426155376,1999992838406142,1999987274273833,
  1999994280078949,2000001591351786,2000001362653145,2000004599945699,1999998895765372,
  2000007306303654,1999996982338849,2000004527481972,2000001542935331,1999994262456688,
  1999994739926387,1999999334398061,1999997225489225,1999999497530461,2000002800726517,
  2000003250756681,2000001694863242,1999996074186563,1999989024492922,1999994446872720,
  1999992240799847,1999999796694808,1999998582743036,2000000191892317,1999995849292634,
  2000004812766796,1999999009723897,2000011593862688,1999991148272898,1999994418975604,
  2000000751685231]
private def pvn_w1_9_p5 : List ℕ := [2000009561591377,1999993807763366,1999989794381509,
  1999992768144417,1999994368527615,1999996928176106,1999995229883179,2000002943490804,
  2000002426846409,2000010053748584,1999993591135999,1999998162518639,1999994875210260,
  2000016424071093,2000009011503707,1999997588261801,1999989183464623,1999987312794023,
  2000003052975638,2000005746644401,2000014333704478,1999996615044952,1999990987732821,
  2000004357808227,1999990526431489,2000003716480810,1999998447873288,1999999104122256,
  2000003507531763,2000006051306195,2000000326667120,1999993785730204,2000015752212708,
  1999992939930551,2000001094338866,2000000203468432,2000004591243441,1999997245754286,
  1999993805936085,2000000667761566,1999991070117471,2000003404441534,2000016682196401,
  2000018584903618,2000002653889005,1999997656571286,1999986912016535,2000001135738515,
  2000033414701632,1999975922611429,2000005739546746,1999994119358719,2000024366132681,
  1999995482528334,2000001994358520,1999989958620803,2000009131942289,1999995644615005,
  1999979593672346,2000023497595549,1999987137104399,1999993157437311,2000024509981598,
  1999982238235409]
private def pvn_w1_9_p6 : List ℕ := [1999994037357632,2000013788864969,1999992704492713,
  2000003771286570,2000005755447609,1999990265458592,1999992696089995,1999992910535609,
  2000005343918150,2000020451027929,1999999288274341,1999982064246662,1999990704128416,
  1999991768105969,2000006430008215,2000037742669059,2000019397602105,1999970583381862,
  1999981990058371,2000029352489026,2000021932469091,1999978193021512,1999974378753902,
  2000004667772389,2000015846104985,2000007336943735,2000001818437296,2000009482968727,
  2000003287051542,2000025087722207,1999999401392015,2000053380241528,1999919563078755,
  2000099345727529,1999783335233390,2000331180186669,1999529298812266,2000683474497619,
  1999062835668788,2001102505217134,1998740563116867,2001245489085118,1999028328175242,
  2000512523953763,2000117360135753,1999251651057356,2001055505130119,1999062134779041,
  2000311135822505,2000493921873499,1998957887205124,2000902266753494,1999864397766748,
  1999182018366534,2000908041143051,1999403007741814,1998913653150802,2000530736241158,
  1999343290858929,1999406236316402,2002935071189264,2005520586408469,2010112849228718,
  2021069630077117]
private def pvn_w1_9_p7 : List ℕ := [2034908058619055,2051343367300760,2075251957627019,
  2105190946617925,2136337241919328,2169552798189263,2206058970157468,2240886409552274,
  2268911769324735,2290472226198764,2306602888056779,2314359307527582,2310533580581371,
  2296550410652587,2276685007793325,2253176208995958,2225456229758745,2193548684222404,
  2160263473358860,2129588138135343,2103794179700863,2082528773789836,2064194908330882,
  2047697823537395,2033053214286075,2020896876236397,2011739710103996,2005580787896880,
  2001946838340028,2000136480852158,1999457760929424,1999367032421638,1999508593446237,
  1999690537434057,1999834313037754,1999924498841525,1999971980728284,1999992989344274,
  2000000390887516,2000001992983526,2000001681820973,2000001038818025,2000000543804371,
  2000000252733323,2000000106226174,2000000040649694,2000000014162047,2000000004467893,
  2000000001261601,2000000000311801,2000000000064338,2000000000009702,2000000000000404,
  1999999999999619,1999999999999825,1999999999999952,1999999999999992]
private def pvn_w1_9 : List ℕ := pCat pvn_w1_9_p0 (pCat pvn_w1_9_p1 (pCat pvn_w1_9_p2 (pCat
  pvn_w1_9_p3 (pCat pvn_w1_9_p4 (pCat pvn_w1_9_p5 (pCat pvn_w1_9_p6 pvn_w1_9_p7))))))
private def pvn_w1_10_p0 : List ℕ := [2000000492712823,2000000347976084,1999999559177008,
  2000000185835591,2000000191170036,2000000073885334,1999999389293657,2000000860315594,
  2000000411028088,1999999707512835,1999999106508486,2000000381669707,1999999540442184,
  1999999523717733,1999998785419381,2000000524252330,1999998719744114,1999999358405219,
  1999999690258651,2000001345475390,1999998975188391,1999999587145938,2000000249056845,
  1999999858995599,2000000635981340,1999998759821993,2000000729663001,1999997722850672,
  1999998007192353,1999997122788603,1999998397607421,2000000166908462,1999999746546798,
  2000000900583331,1999999583583470,2000001424058104,1999999551622012,2000001509257984,
  1999998298319707,2000000375113882,1999998951211358,2000001870792480,1999999248803611,
  1999999317865320,2000001225465490,1999997112455824,1999998155897901,1999999837135636,
  1999999287979371,1999999727446811,1999999924906161,1999998040783802,2000000566463836,
  2000000737029324,1999997114794823,1999999657937586,2000000985245856,1999998144467739,
  1999999319702945,2000000232686588,1999998229300027,2000000505865218,2000001012008060,
  1999999398200834]
private def pvn_w1_10_p1 : List ℕ := [2000000006040203,2000000351057741,2000002296087176,
  2000001935974673,1999999072468163,1999997507612761,2000000376995456,2000000183208589,
  1999998874278789,1999999075649507,1999999936227595,1999999052427993,2000001456050092,
  1999998891580573,2000003430455964,2000002226562985,2000001733960593,1999998247706784,
  1999997576279292,1999998309848591,1999999466781858,2000000368806422,1999999770137809,
  1999999174466365,2000001629101242,2000002371650347,2000000313202133,1999997285828309,
  1999998965280191,1999997633697578,1999999531155003,2000003971698880,1999999790062739,
  2000001507414833,1999999022721391,1999997697635919,2000000769463155,2000001166228517,
  2000004627844595,2000002204325967,2000000560942994,2000000349305303,1999993145201970,
  1999994198610488,1999998568341301,1999996579719631,1999999753923036,2000004020458764,
  2000005174483605,2000004311741039,2000005540833124,2000002863203416,2000004780062131,
  1999999648457879,1999997946097806,1999994633358266,1999989697375780,1999992145278420,
  1999994569586805,1999994788961902,1999991164158373,1999998671944851,2000005745418684,
  1999998323455554]
private def pvn_w1_10_p2 : List ℕ := [2000003153086644,2000006757996469,2000001869756349,
  2000008254633437,2000003536275260,2000001705824436,1999992734994866,1999992317529546,
  1999995253737638,1999998840365100,1999999970282022,1999999797503452,2000005558378849,
  2000005525787574,2000002018139609,1999999352027992,1999999002405537,1999993624040093,
  1999999428686623,1999996914230811,1999999628513561,2000001983569295,2000005137696495,
  1999998747858415,2000004044954705,1999996544690969,2000002056272002,1999996784554549,
  2000002466118898,1999999318097107,1999996949787317,1999997971659143,2000001952446321,
  1999992130457276,1999998351801226,1999995747174635,1999992037995338,1999998571286482,
  2000003960671088,1999997144927191,1999999947657358,2000001836925737,2000000511428349,
  2000001391438039,2000001734818181,2000006407351265,2000001418127124,2000003555329253,
  2000005207205438,2000004721872177,1999998456978615,1999999543836795,2000003900288021,
  2000006548269015,2000005245712095,2000005533077628,2000004798310452,2000004350489960,
  2000000897932425,2000001393920738,2000003993209353,2000000161143381,2000001500896996,
  1999998292253344]
private def pvn_w1_10_p3 : List ℕ := [1999998586287729,1999995727376144,1999995273309001,
  1999994028191164,1999994787796831,1999995045905126,1999998720501152,1999990110698752,
  1999993484089082,2000005825488329,1999998143052972,2000003016368825,2000007502212415,
  2000006231073366,2000007592429557,2000004039318941,2000000754520755,1999999800771378,
  1999997713291353,1999996573535443,1999996071524233,1999995476807130,1999996460327677,
  2000002017451635,2000005251731101,2000004764779754,2000006393894736,2000006810058302,
  2000000890629949,2000003510511922,2000000235708076,2000004906905846,2000002009839772,
  2000000235043093,2000005744384500,2000006270163879,2000006827513686,2000007589333980,
  2000002192934487,2000006243799779,2000003816228227,2000009087459007,2000009143607033,
  2000006239196101,2000009060338817,2000001703676895,2000004697788099,2000000387098722,
  1999995715955498,1999991328283508,1999996959391994,1999994151116265,1999998738737129,
  1999998092914827,1999998908593957,1999995386512915,1999999794883674,2000000646519957,
  2000002239021230,2000007974667280,2000013990758464,2000001281012917,2000006907841665,
  1999997689501257]
private def pvn_w1_10_p4 : List ℕ := [1999994614850328,1999994438493288,1999996653909761,
  2000004603638639,2000004798700664,1999999312065149,1999995157672119,1999995413186085,
  1999999495200512,2000000017703643,2000006148491442,2000004323431503,2000001074735015,
  2000005442476887,1999996392193638,1999998846499023,1999999467436177,1999999997972576,
  1999998272467448,1999998432024386,1999996166415018,2000001572725021,2000001689409776,
  2000000049496702,2000000852422281,1999996069786026,2000000113050411,2000003088715328,
  2000002143302453,2000004051262862,2000001641619706,1999998943453222,2000006330924735,
  1999997717585118,1999997778474137,1999985026896139,1999994763317484,1999995646482620,
  1999997172974316,2000003547990689,2000003025050071,1999998641526774,2000004156792665,
  2000005288467814,2000000330294950,1999998132287221,1999997796431261,1999995180890270,
  1999998966964449,1999994114960109,2000003124026840,2000003262614192,2000005006036779,
  1999996798694024,1999997950952048,1999986034067484,1999999138567384,1999990329489170,
  2000002668434306,1999996913488697,1999995174654352,1999997350827365,2000011081734508,
  2000004458895087]
private def pvn_w1_10_p5 : List ℕ := [1999991492837821,1999997233714807,2000002719984239,
  2000006589501925,1999994959439166,1999997641331967,1999988397022161,1999999419397506,
  1999988659289881,1999997097531353,1999995127731012,2000007544797925,2000009128993907,
  1999994104166219,1999994484288357,1999996503337324,2000014828899860,2000009127842408,
  2000002357761385,1999995124884734,1999978584443490,2000005932592296,2000005104278839,
  2000005958527469,2000003504207456,1999996920440999,1999996947891406,1999996506474129,
  2000004996905298,1999985318104122,2000010153039931,2000002280119821,1999998672716118,
  2000000670609417,2000005243603181,2000004933690469,1999994096029442,2000005304686737,
  2000001526175671,1999999445976102,2000000762383652,2000002440676228,1999987821616422,
  1999990742988481,2000010488187907,1999996617877361,2000044719512733,1999986314031336,
  1999995854821641,1999993014700406,2000022614033647,1999997082299067,1999996903611404,
  1999994512353365,2000007215105046,2000021708503153,1999980057731156,2000013854717090,
  2000008925511510,1999974326795815,2000014252297790,1999997886297021,1999981275475177,
  2000015047828226]
private def pvn_w1_10_p6 : List ℕ := [2000002145995858,1999992347887071,2000004316256850,
  1999995716125187,1999998748404755,2000004994888514,2000001635698312,2000005479125027,
  1999992426682452,1999979908977184,2000003219114466,2000016503436010,2000003174684725,
  2000002213144629,1999993668803816,1999969686060422,1999991070859174,2000040715592178,
  2000029451971731,1999978540786597,1999979985944610,2000021760796575,2000023069354167,
  1999992863479422,1999975772894951,2000001555771455,1999992026444582,2000031283859155,
  1999961292300867,2000083904248063,1999870885250855,2000221837270265,1999695318237020,
  2000506970229129,1999328528741651,2000864937022539,1998900053753988,2001211519234725,
  1998810475278558,2001010846780374,1999385434394729,2000004065653030,2000549354579758,
  1999036751844308,2001013711863974,1999429969737922,1999853744417604,2000804027028724,
  1998960704545884,2000580780551290,2000253102708164,1999064551726168,2000859867232126,
  1999944967984332,1999175553701746,2000913776656011,1999873268541128,1998950843043563,
  2000547277197252,1999668131023709,1998284418890803,2000130965425574,2001229922966588,
  2001758627163684]
private def pvn_w1_10_p7 : List ℕ := [2007078893909362,2015968382154129,2026054360025393,
  2041681145922181,2065166882450789,2092559538115873,2122450354114720,2157370533064670,
  2195684192398978,2231394603056130,2261571700488510,2287150490707442,2307042150886747,
  2316979973281296,2314718164277988,2302720307708073,2284674920900871,2261661140834779,
  2233041716476160,2199818961021123,2165596099169351,2134313905437601,2107787688760739,
  2085463550237212,2065948804936680,2048472898519602,2033221792317795,2020803687388622,
  2011605505332307,2005504765057457,2001948383567065,2000195552882505,1999542652000880,
  1999450541028284,1999574903489186,1999735125213725,1999860042131199,1999937114120628,
  1999976979904862,1999994291047560,2000000262715219,2000001515145236,2000001258088468,
  2000000759570619,2000000387197759,2000000174694339,2000000071095838,2000000026289222,
  2000000008838860,2000000002690733,2000000000734588,2000000000176675,2000000000036145,
  2000000000005780,2000000000000515,1999999999999929,1999999999999954,1999999999999991]
private def pvn_w1_10 : List ℕ := pCat pvn_w1_10_p0 (pCat pvn_w1_10_p1 (pCat pvn_w1_10_p2 (pCat
  pvn_w1_10_p3 (pCat pvn_w1_10_p4 (pCat pvn_w1_10_p5 (pCat pvn_w1_10_p6 pvn_w1_10_p7))))))
private def pvi_w1 : List ℤ := bDc bZ (rPad bZ 513 pvn_w1_0)
private def pvo_w1 : List ℤ := bDc bZ (rPad bZ 513 pvn_w1_10)
private abbrev dP_0 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w1 513 pvn_w1_5 513 pvn_w1_6
  ] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w1 513 pvn_w1_4 513 pvn_w1_5
  ] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w1 513 pvn_w1_3 513 pvn_w1_4
  ] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w1 513 pvn_w1_2 513 pvn_w1_3
  ] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w1 513 pvn_w1_1 513 pvn_w1_2
  ] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w1 513 pvn_w1_0 513 pvn_w1_1
  ] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w0 513 pvn_w0_6 513 pvn_w0_7
  ] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w0 513 pvn_w0_5 513 pvn_w0_6
  ] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w0 513 pvn_w0_4 513 pvn_w0_5
  ] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w0 513 pvn_w0_3 513 pvn_w0_4
  ] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w0 513 pvn_w0_2 513 pvn_w0_3
  ] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w0 513 pvn_w0_1 513 pvn_w0_2
  ] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := rkmAllTrueF [
    bSlChk 4 513 phbn_w0 513 pvn_w0_0 513 pvn_w0_1
  ] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := rkmAllTrueF [
    bSlChk 3 513 phbn_w1 513 pvn_w1_9 513 pvn_w1_10
  ] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := rkmAllTrueF [
    bSlChk 3 513 phbn_w1 513 pvn_w1_8 513 pvn_w1_9
  ] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := rkmAllTrueF [
    bSlChk 3 513 phbn_w1 513 pvn_w1_7 513 pvn_w1_8
  ] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := rkmAllTrueF [
    bSlChk 3 513 phbn_w1 513 pvn_w1_6 513 pvn_w1_7
  ] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := rkmAllTrueF [
    bSlChk 3 513 phbn_w0 513 pvn_w0_9 513 pvn_w0_10,
    muxIntListEq pvo_w1 rkmVoHi_m512_r512_s3_c0
  ] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := rkmAllTrueF [
    bSlChk 3 513 phbn_w0 513 pvn_w0_8 513 pvn_w0_9,
    muxIntListEq pvo_w0 rkmVoHi_m512_r512_s2_c1,
    muxIntListEq pvi_w1 rkmViHi_m512_r512_s3_c0
  ] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := rkmAllTrueF [
    bSlChk 3 513 phbn_w0 513 pvn_w0_7 513 pvn_w0_8,
    muxIntListEq phbv_w0 rkmHbHi_m512_r512_s2_c1,
    muxIntListEq pvi_w0 rkmViHi_m512_r512_s2_c1,
    muxIntListEq phbv_w1 rkmHbHi_m512_r512_s3_c0
  ] = true
private theorem bk_19 : dP_19 := by decide +kernel
private theorem pw_w0_1 : pWOk 8 513 phbn_w0 513 pvn_w0_0 513 pvn_w0_2 :=
  bCh 4 4 513 (bSlSnd (bH bk_12))
    (bH bk_11)
private theorem pw_w0_2 : pWOk 12 513 phbn_w0 513 pvn_w0_0 513 pvn_w0_3 :=
  bCh 8 4 513 pw_w0_1
    (bH bk_10)
private theorem pw_w0_3 : pWOk 16 513 phbn_w0 513 pvn_w0_0 513 pvn_w0_4 :=
  bCh 12 4 513 pw_w0_2
    (bH bk_9)
private theorem pw_w0_4 : pWOk 20 513 phbn_w0 513 pvn_w0_0 513 pvn_w0_5 :=
  bCh 16 4 513 pw_w0_3
    (bH bk_8)
private theorem pw_w0_5 : pWOk 24 513 phbn_w0 513 pvn_w0_0 513 pvn_w0_6 :=
  bCh 20 4 513 pw_w0_4
    (bH bk_7)
private theorem pw_w0_6 : pWOk 28 513 phbn_w0 513 pvn_w0_0 513 pvn_w0_7 :=
  bCh 24 4 513 pw_w0_5
    (bH bk_6)
private theorem pw_w0_7 : pWOk 31 513 phbn_w0 513 pvn_w0_0 513 pvn_w0_8 :=
  bCh 28 3 513 pw_w0_6
    (bH bk_19)
private theorem pw_w0_8 : pWOk 34 513 phbn_w0 513 pvn_w0_0 513 pvn_w0_9 :=
  bCh 31 3 513 pw_w0_7
    (bH bk_18)
private theorem pw_w0_9 : pWOk 37 513 phbn_w0 513 pvn_w0_0 513 pvn_w0_10 :=
  bCh 34 3 513 pw_w0_8
    (bH bk_17)
private theorem pwalk_w0 : muxFastIterFullT16 37 513 phbv_w0 pvi_w0 = pvo_w0 :=
  pw_w0_9
/-- Certified `T_16` walk chunk `m512_r512_s2_c1`. -/
theorem rkmWalkChkHi_m512_r512_s2_c1 : muxFastIterFullT16 37 513
    rkmHbHi_m512_r512_s2_c1 rkmViHi_m512_r512_s2_c1 = rkmVoHi_m512_r512_s2_c1 :=
  bLift pwalk_w0 (bH (bT bk_19))
    (bH (bT (bT bk_19)))
    (bH (bT bk_18))
private theorem pw_w1_1 : pWOk 8 513 phbn_w1 513 pvn_w1_0 513 pvn_w1_2 :=
  bCh 4 4 513 (bSlSnd (bH bk_5))
    (bH bk_4)
private theorem pw_w1_2 : pWOk 12 513 phbn_w1 513 pvn_w1_0 513 pvn_w1_3 :=
  bCh 8 4 513 pw_w1_1
    (bH bk_3)
private theorem pw_w1_3 : pWOk 16 513 phbn_w1 513 pvn_w1_0 513 pvn_w1_4 :=
  bCh 12 4 513 pw_w1_2
    (bH bk_2)
private theorem pw_w1_4 : pWOk 20 513 phbn_w1 513 pvn_w1_0 513 pvn_w1_5 :=
  bCh 16 4 513 pw_w1_3
    (bH bk_1)
private theorem pw_w1_5 : pWOk 24 513 phbn_w1 513 pvn_w1_0 513 pvn_w1_6 :=
  bCh 20 4 513 pw_w1_4
    (bH bk_0)
private theorem pw_w1_6 : pWOk 27 513 phbn_w1 513 pvn_w1_0 513 pvn_w1_7 :=
  bCh 24 3 513 pw_w1_5
    (bH bk_16)
private theorem pw_w1_7 : pWOk 30 513 phbn_w1 513 pvn_w1_0 513 pvn_w1_8 :=
  bCh 27 3 513 pw_w1_6
    (bH bk_15)
private theorem pw_w1_8 : pWOk 33 513 phbn_w1 513 pvn_w1_0 513 pvn_w1_9 :=
  bCh 30 3 513 pw_w1_7
    (bH bk_14)
private theorem pw_w1_9 : pWOk 36 513 phbn_w1 513 pvn_w1_0 513 pvn_w1_10 :=
  bCh 33 3 513 pw_w1_8
    (bH bk_13)
private theorem pwalk_w1 : muxFastIterFullT16 36 513 phbv_w1 pvi_w1 = pvo_w1 :=
  pw_w1_9
/-- Certified `T_16` walk chunk `m512_r512_s3_c0`. -/
theorem rkmWalkChkHi_m512_r512_s3_c0 : muxFastIterFullT16 36 513
    rkmHbHi_m512_r512_s3_c0 rkmViHi_m512_r512_s3_c0 = rkmVoHi_m512_r512_s3_c0 :=
  bLift pwalk_w1 (bH (bT (bT (bT bk_19))))
    (bH (bT (bT bk_18)))
    (bH (bT bk_17))
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi512T7`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi512T7 :
    rkmWalkChkHi_m512_r512_s2_c1 = rkmWalkChkHi_m512_r512_s2_c1 :=
  rfl
private theorem laneRoot_Hi512T7 : rkmZigHi512T7 = rkmZigHi512T7 :=
  (And.intro (Eq.refl rkmZigHi512T6) rfl).right
end
end QuantumComputation.Specs.DickeSol
