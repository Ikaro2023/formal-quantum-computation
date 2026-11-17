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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T5

/-
# High-`m` Checkpointed Walk Part `6` (`FindAllJohnsonRampKickMuxHi512T6`)

Certifies `2` `T_16` checkpoint walk(s) (`49248` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Zigzag `< 2 ^ 60` `ℕ → ℤ` list decoder (`FindAllJohnsonRampKickMuxHi512T6`). -/
def rkmZigHi512T6 : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: rkmZigHi512T6 ws
/-- Gap-encoded sign-flip helper (`FindAllJohnsonRampKickMuxHi512T6`). -/
def rkmFlipGapsHi512T6 : List ℕ → List ℤ → List ℤ
  | [], vs => vs
  | _, [] => []
  | 0 :: gs, v :: vs => muxRawIntNeg v :: rkmFlipGapsHi512T6 gs vs
  | (g + 1) :: gs, v :: vs => v :: rkmFlipGapsHi512T6 (g :: gs) vs
/-- Quantized generator list for `m512_r512_s1_c1`. -/
def rkmHbHi_m512_r512_s1_c1 : List ℤ := altBuildHbFrom 512 512 83534166666 0 512
/-- Input orbital vector for `m512_r512_s1_c1`. -/
def rkmViHi_m512_r512_s1_c1 : List ℤ := rkmZigHi512T6
  [7866,53906,289598,1130514,4124978,12253086,34954246,85819068,202433052,425954792,855000350,
   1567827846,2718514006,4366072830,6571447646,9195772022,11928778444,14256922640,15467254732,
   14908200272,12140436412,7233107750,967805174,5290569549,9841622027,11219652465,8863359231,
   3445433829,3136861622,8334862344,10015125706,7398796938,1544109082,4920663067,8971179467,
   8645014441,4044869415,2545712398,7725825726,8776219576,5121858384,1279083981,6885275101,
   8546376855,5337647957,890876310,6515968414,8216671336,5003057322,1151343681,6507394431,
   7804690149,4267228607,1856346886,6700114962,7242599244,3194740056,2818109137,6909793705,
   6463550349,1846766613,3874239450,6957054540,5414733324,330844526,4864639789,6724357007,
   4080686073,1230375986,5618718634,6149374436,2532559880,2711352343,6021029477,5206650619,
   886117891,3957540720,6022979698,3960692152,744321239,4855579035,5601870745,2530055285,2210108802,
   5362545902,4818298548,1023201708,3397854741,5451011103,3784704955,414816266,4262616648,
   5173425584,2597555372,1676118389,4765332853,4623405883,1395386293,2710224410,4948768716,
   3880300596,271655768,3465634857,4876897659,3071554257,713599968,3974961122,4613186424,2269398658,
   1501948475,4264135873,4264727997,1548286703,2109883970,4384935238,3880856548,961459726,
   2523175773,4404912529,3544800675,519993971,2780461252,4353386458,3286292724,260738866,2890367153,
   4291185835,3141422217,164805387,2869281640,4210622028,3122039534,262018582,2719280071,4134649457,
   3218520439,528499155,2418210924,4011765322,3414640598,983453022,1949468225,3813398701,3647408149,
   1584027363,1270790200,3443716546,3845211314,2302082048,377849471,2839256789,3876945599,
   3020223067,720671513,1902706512,3606964790,3606369132,1928639446,623297551,2873958187,3822314051,
   3070037129,966306747,1563357510,3425876576,3834166114,2632204738,331616826,2127739939,3763745053,
   3929838799,2555751495,164708831,2341810544,4036809290,4304463972,3039104352,661986056,2030864209,
   4140163729,4965436079,4227301781,2134897937,702208126,3465468152,5361529426,5842349258,
   4751299222,2349445380,777097165,3881423667,6236037237,7292565395,6795878685,4827045293,
   1763313987,1824482686,5296115304,8056542620,9649592346,9823132240,8552098818,6013531166,
   2528937634,1500684009,5653461989,9539337883,12845289631,15362162619,16985267907,17695901275,
   17538203213,16596679707,14968758743,12729195277,9893006875,6384138095,2005798463,3599893130,
   11010835080,21101672518,35138594488,54902541244,82857045124,122371866848,178006096242,
   255855451468,363976307742,512901898544,716258602366,991479349840,1360606099902,1851172765162,
   2497154367506,3339952567194,4429367792850,5824492818726,7594453015678,9818908362098,
   12588217667376,16003151171088,20174032829740,25219202314978,31262705676958,38431148381142,
   46849676186200,56637093594452,67900189008898,80727405633478,95182068687240,111295445908064,
   129059977188214,148423058795676,169281802439190,191479200251240,214802105610192,238981384218450,
   263694503105880,288570712282050,313198838979824,337137562495508,359927876520902,381107288168832,
   400225163580712,416858522448594,430627517162136,441209811755794,448353104097810,451885112746692,
   451720475537386,447864173425816,440411288403368,429543112885068,415519833700338,398670202112650,
   379378760090278,358071312624982,335199408860532,311224616781060,286603346977922,261772905038780,
   237139338067050,213067500116950,189873606173218,167820386463374,147114802903332,127908156386266,
   110298304722862,94333631430564,80018357680772,67318773074544,56169972425794,46482720360272,
   38150117261490,31053802722016,25069500393798,20071775874386,15937942743478,12551107722570,
   9802391839104,7592399198846,5832028355636,4442734101008,3356351247876,2514588498934,
   1868291710858,1376563612626,1005812898070,728790895662,523659745830,373122941566,263637715946,
   184719363504,128340230206,88420705644,60405886422,40919368090,27484559796,18303705000,
   12085174666,7910361922,5132479750,3300623878,2103519382,1328364472,831081210,515061646,316154770,
   192178000,115668496,68926368,40660664,23743876,13724474,7852270,4446798,2492636,1383064,759644,
   413020,222298,118434,62454,32588,16810,8564,4304,2124,1020,472,210,84,28,6,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0]
/-- Output orbital vector for `m512_r512_s1_c1`. -/
def rkmVoHi_m512_r512_s1_c1 : List ℤ := rkmZigHi512T6
  [67608,296773,870360,1946975,3475448,4960735,5579814,4239953,1596028,3309376,2207605,9549600,
   14043010,27774574,70909198,134244140,258016426,485035992,844602452,1417282170,2281540022,
   3484329238,5079167524,7056236116,9286409226,11552357584,13516189646,14716381656,14696336716,
   13113897344,9838621434,5117026258,363504489,5589840181,9404512653,10792786105,9276840385,
   5174323265,403398924,5769503616,9143646206,9318393552,6167856362,772039308,4866111655,8523568057,
   8690493345,5259773757,366563806,5782210922,8574376190,7455764878,2926153962,2916333931,
   7308039497,8113503445,4924134557,665438698,5836468898,7963564996,5953008486,859733214,4606375125,
   7523148441,6347540831,1749928201,3733182718,7060794064,6389551386,2143265172,3230826429,
   6668322763,6225401889,2195301265,3037462132,6392762658,5930139324,1984126766,3063017971,
   6196507279,5562142563,1592781541,3259261162,6043484910,5110375860,1083939984,3536936665,
   5908322727,4601357165,484051863,3853635412,5734341374,4036013786,140025151,4163193455,5525726497,
   3421365371,776087982,4418839342,5251125664,2794104352,1374093725,4619953203,4925984021,
   2153135773,1915865630,4730356746,4559810046,1549979246,2384714845,4777235223,4165499933,
   983301175,2759102222,4747277362,3781076502,494709560,3053434433,4675522999,3411127571,84238805,
   3248804144,4568270908,3102145348,225658001,3376294151,4453759055,2849094275,432917582,3417821168,
   4344965498,2693652814,528831627,3404117175,4254398739,2621397741,506997330,3309331018,4186687352,
   2663017834,362299385,3150234941,4132077351,2791380015,84895460,2884486288,4071425496,3017719172,
   328936298,2509915451,3966131759,3288592473,877102879,1970868664,3760745924,3576519060,1542777290,
   1262197943,3390939915,3780803579,2272087979,350978686,2776570856,3817229926,2985743800,716962694,
   1871662095,3543790055,3532205703,1872170027,644983438,2852211228,3745891354,2939625380,820910256,
   1652374835,3395851681,3666341491,2360877891,42765743,2307164294,3710064868,3595951608,2020650496,
   383282315,2673648725,3964001297,3754723257,2114640891,355003886,2757492096,4234449380,4262150970,
   2814223604,356318058,2314297891,4333140199,5049158657,4222883113,2080710399,772591002,3537313372,
   5442110884,5952150126,4907038520,2548475784,562860391,3701323097,6149639201,7353779135,
   7034652221,5235434435,2293174299,1252204374,4777030440,7687897528,9514174640,9972898530,
   8997954064,6726616968,3450257456,450083307,4564230015,8503716539,11944210119,14655820787,
   16513067717,17483057531,17601614255,16948498945,15623485081,13717984085,11280485817,8280909489,
   4577346127,120853128,6305723312,14747548608,26598337154,43525803084,67890235928,102982244144,
   153336438802,225130178886,326676026092,469021469284,666671291938,938440617178,1308433525666,
   1807130611926,2472560478010,3351518939066,4500780089588,5988217558600,7893730011902,
   10309847344306,13341881676198,17107477043768,21735405375184,27363461418388,34135332724520,
   42196363654076,51688190661188,62742296083088,75472608825186,89967372760736,106280602996654,
   124423546070976,144356639919722,165982522824994,189140661349024,213604151225386,239079187690600,
   265207598642784,291572685209654,317708426687866,343111893847712,367258493101956,389619450988230,
   409680759838650,426962656998550,441038616621714,451552807607764,458235020775972,460912192116508,
   459515838231808,454084960202100,444764244868766,431797677857252,415517959520808,396332362334938,
   374705866844938,351142548028280,326166246238662,300301545445084,274056001750838,247904427896198,
   222275858836200,197543615802984,174018668648374,151946285545766,131505770457130,112812934169366,
   95924831974574,80846233341718,67537265005480,55921684142114,45895285747638,37334019735314,
   30101479928292,24055520561954,19053848427242,14958523952484,11639377572022,8976405753584,
   6861252976212,5197912246930,3902789065026,2904274442268,2141964334334,1565648303198,
   1134171878900,814257063982,579345468064,408509990430,285464675302,197688836952,135670937730,
   92269880844,62186047980,41531165546,27484485032,18022393452,11709055826,7536724292,4805682036,
   3035241414,1898654688,1176136586,721390272,438050494,263306022,156647670,92227724,53731220,
   30972734,17663938,9966094,5562552,3071324,1677542,906388,484446,256128,133944,69274,35420,17892,
   8918,4378,2110,992,448,188,72,20,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
/-- Quantized generator list for `m512_r512_s2_c0`. -/
def rkmHbHi_m512_r512_s2_c0 : List ℤ := altBuildHbFrom 1024 512 51800528925 0 512
/-- Input orbital vector for `m512_r512_s2_c0`. -/
def rkmViHi_m512_r512_s2_c0 : List ℤ := rkmFlipGapsHi512T6
  [5,2,0,1,0,0,0,0,2,0,0,0,0,9,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,6,1,0,0,0,0,0,1,0,0,0,4,
   3,0,0,1,0,0,2,0,4,2,4,7,0,1,0,2,5,0,0,0,0,0,2,0,1,0,6,0,0,0,0,7,4,3,0,0,0,0,0,0,7,2,0,1,0,0,0,0,
   1,0,0,0,0,0,0,8,0,0,1,0,0,2,3,0,5,0,0,0,0,1,0,0,0,0,94,0,0,0,0,0,0,8,0,1,0,0,1]
  rkmVoHi_m512_r512_s1_c1
/-- Output orbital vector for `m512_r512_s2_c0`. -/
def rkmVoHi_m512_r512_s2_c0 : List ℤ := rkmZigHi512T6
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
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true :=
  (rkmAllTrueF_cons h).2
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def phbv_w0_p0 : List ℤ := pzig
  [171077973331968,241468249503688,295158258500214,340151126663952,379553368621432,
   414961419204382,447325517093920,477266011739190,505214639995968,531486356966650,
   556319387916318,579899166700420,602373442334834,623862238580672,644464661182770,
   664263693328032,683329661943544,701722799438314,719495173880036,736692168229788,
   753353631184418,769514784642544,785206947950104,800458122252242,815293466660160,
   829735689777446,843805374300612,857521248183998,870900412756626,883958535871638,
   896710016433916,909168125332872,921345126795236,933252383388814,944900447295842,
   956299139992368,967457622087682,978384454772244,989087654076882,999574738947222,
   1009852773975562,1019928407499950,1029807905671252,1039497182999018,1049001829811992,
   1058327137006756,1067478118405618,1076459531000782,1085275893324672,1093931502154678,
   1102430447733770,1110776627665436,1118973759621834,1127025392987052,1134934919542908,
   1142705583292054,1150340489502300,1157842613046530,1165214806104340,1172459805284318,
   1179580238219508,1186578629683086,1193457407266390,1200218906657088,1206865376551512,
   1213398983231794,1219821814835426,1226135885342248,1232343138301464,1238445450319196,
   1244444634325178,1250342442635542,1256140569827056,1261840655436926,1267444286500920,
   1272952999941602,1278368284817350,1283691584442030,1288924298384316,1294067784354964,
   1299123359989632,1304092304534278,1308975860439590,1313775234870390,1318491601135532,
   1323126100043382,1327679841187562,1332153904167338,1336549339746660,1340867170955628,
   1345108394137852,1349273979946912,1353364874294970,1357381999256274,1361326253928208,
   1365198515252290,1368999638797390,1372730459507274,1376391792414480,1379984433322320,
   1383509159456800,1386966730090034,1390357887136662,1393683355724744,1396943844742406,
   1400140047361524,1403272641539612,1406342290501022,1409349643198484,1412295334755992,
   1415179986893918,1418004208337252,1420768595207772,1423473731400926,1426120188948134,
   1428708528365210,1431239298987568,1433713039292784,1436130277211138,1438491530424654,
   1440797306655168,1443048103941924,1445244410909148,1447386707024040,1449475462845630,
   1451511140264852,1453494192736260,1455425065501688]
private def phbv_w0_p1 : List ℤ := pzig
  [1457304195806264,1459132013107018,1460908939274470,1462635388787438,1464311768921346,
   1465938479930344,1467515915223418,1469044461534794,1470524499088822,1471956401759590,
   1473340537225440,1474677267118616,1475966947170212,1477209927350612,1478406552005580,
   1479557159988192,1480662084786716,1481721654648664,1482736192701076,1483706017067242,
   1484631440979956,1485512772891432,1486350316580020,1487144371253812,1487895231651268,
   1488603188138950,1489268526806486,1489891529558848,1490472474206030,1491011634550232,
   1491509280470628,1491965678005790,1492381089433870,1492755773350596,1493089984745150,
   1493383975074032,1493637992332926,1493852281126682,1494027082737450,1494162635191010,
   1494259173321408,1494316928833888,1494336130366228,1494317003548500,1494259771061300,
   1494164652692530,1494031865392740,1493861623329080,1493654137937936,1493409617976246,
   1493128269571564,1492810296270910,1492455899088426,1492065276551882,1491638624748070,
   1491176137367120,1490678005745760,1490144418909546,1489575563614126,1488971624385518,
   1488332783559462,1487659221319870,1486951115736382,1486208642801080,1485431976464344,
   1484621288669934,1483776749389246,1482898526654832,1481986786593152,1481041693456630,
   1480063409654966,1479052095785808,1478007910664710,1476931011354480,1475821553193878,
   1474679689825692,1473505573224228,1472299353722214,1471061180037134,1469791199296998,
   1468489557065598,1467156397367214,1465791862710820,1464396094113792,1462969231125124,
   1461511411848176,1460022772962954,1458503449747950,1456953576101528,1455373284562892,
   1453762706332640,1452121971292892,1450451208027046,1448750543839124,1447020104772756,
   1445260015629776,1443470399988480,1441651380221512,1439803077513422,1437925611877876,
   1436019102174548,1434083666125684,1432119420332362,1430126480290440,1428104960406206,
   1426054974011750,1423976633380024,1421870049739658,1419735333289470,1417572593212746,
   1415381937691222,1413163473918848,1410917308115278,1408643545539134,1406342290501022,
   1404013646376316,1401657715617732,1399274599767654,1396864399470264,1394427214483448,
   1391963143690502,1389472285111624,1386954735915222,1384410592429012,1381839950150940,
   1379242903759900,1376619547126288,1373969973322368]
private def phbv_w0_p2 : List ℤ := pzig
  [1371294274632454,1368592542562944,1365864867852164,1363111340480056,1360332049677706,
   1357527083936718,1354696531018420,1351840477962938,1348959011098102,1346052216048218,
   1343120177742706,1340162980424572,1337180707658772,1334173442340422,1331141266702894,
   1328084262325762,1325002510142640,1321896090448888,1318765082909202,1315609566565078,
   1312429619842156,1309225320557474,1305996745926576,1302743972570530,1299467076522842,
   1296166133236246,1292841217589406,1289492403893510,1286119765898764,1282723376800786,
   1279303309246910,1275859635342390,1272392426656512,1268901754228614,1265387688574028,
   1261850299689908,1258289657061002,1254705829665324,1251098885979740,1247468893985480,
   1243815921173568,1240140034550174,1236441300641882,1232719785500894,1228975554710154,
   1225208673388388,1221419206195094,1217607217335446,1213772770565124,1209915929195102,
   1206036756096330,1202135313704390,1198211664024054,1194265868633804,1190297988690274,
   1186308084932634,1182296217686920,1178262446870292,1174206831995252,1170129432173780,
   1166030306121444,1161909512161426,1157767108228512,1153603151873016,1149417700264668,
   1145210810196432,1140982538088282,1136732939990928,1132462071589490,1128169988207130,
   1123856744808626,1119522396003904,1115166996051532,1110790598862152,1106393258001878,
   1101975026695656,1097535957830562,1093076103959080,1088595517302316,1084094249753188,
   1079572352879568,1075029877927384,1070466875823682,1065883397179658,1061279492293636,
   1056655211154024,1052010603442224,1047345718535510,1042660605509864,1037955313142790,
   1033229889916076,1028484384018534,1023718843348708,1018933315517532,1014127847850980,
   1009302487392666,1004457280906412,999592274878800,994707515521680,989803048774648,
   984878920307502,979935175522666,974971859557574,969989017287050,964986693325632,
   959964932029886,954923777500694,949863273585496,944783463880536,939684391733048,
   934566100243446,929428632267470,924272030418312,919096337068722,913901594353088,
   908687844169480,903455128181694,898203487821250,892932964289382,887643598558996,
   882335431376612,877008503264288,871662854521502,866298525227042,860915555240848,
   855513984205856,850093851549806,844655196487028]
private def phbv_w0_p3 : List ℤ := pzig
  [839198058020230,833722474942236,828228485837730,822716129084970,817185442857474,
   811636465125712,806069233658758,800483786025928,794880159598410,789258391550864,
   783618518863016,777960578321226,772284606520044,766590639863742,760878714567848,
   755148866660640,749401131984636,743635546198076,737852144776370,732050963013550,
   726232036023686,720395398742310,714541085927804,708669132162790,702779571855498,
   696872439241112,690947768383124,685005593174648,679045947339742,673068864434702,
   667074377849352,661062520808314,655033326372266,648986827439196,642923056745630,
   636842046867862,630743830223150,624628439070928,618495905513984,612346261499634,
   606179538820886,599995769117590,593794983877572,587577214437768,581342491985340,
   575090847558778,568822312048994,562536916200408,556234690612022,549915665738480,
   543579871891122,537227339239026,530858097810036,524472177491794,518069608032736,
   511650419043114,505214639995968,498762300228124,492293428941164,485808055202390,
   479306207945772,472787915972908,466253207953948,459702112428534,453134657806710,
   446550872369836,439950784271492,433334421538370,426701812071162,420052983645434,
   413387963912496,406706780400264,400009460514114,393296031537726,386566520633918,
   379820954845482,373059361096000,366281766190666,359488196817082,352678679546072,
   345853240832458,339011907015860,332154704321468,325281658860810,318392796632522,
   311488143523098,304567725307654,297631567650654,290679696106660,283712136121058,
   276728913030782,269730052065036,262715578345994,255685516889522,248639892605860,
   241578730300322,234502054673988,227409890324376,220302261746118,213179193331632,
   206040709371782,198886834056538,191717591475626,184533005619170,177333100378342,
   170117899545984,162887426817250,155641705790214,148380759966512,141104612751928,
   133813287457024,126506807297730,119185195395950,111848474780146,104496668385936,
   97129799056664,89747889543994,82350962508464,74939040520072,67512146058830,60070301515320,
   52613529191256,45141851300032,37655289967260,30153867231318,22637605043882,15106525270460,
   7560649690916]
private def phbv_w0 : List ℤ := phbv_w0_p0 ++ (phbv_w0_p1 ++ (phbv_w0_p2 ++ phbv_w0_p3))
private def pvm_w0_1_p0 : List ℤ := pzig
  [5524,28285,116800,290551,901616,1152095,4166942,136537,15960586,21380830,65779468,133912904,
   274129690,539060890,972767938,1688741108,2761242528,4259305418,6226367822,8560863048,
   11048711202,13324422344,14847681548,15064927172,13528718640,10051250222,4938301234,977698507,
   6467545881,10134205371,10876671263,8366161713,3258548339,2848137188,7830378384,9836234640,
   8045415966,3074900130,3100574005,7874627687,9158862611,6342620519,650806103,5282636980,
   8615259052,7718479286,3017267922,3151447969,7631342909,8082132037,4275814101,1750560202,
   6751313606,7991965678,4791719446,1029652043,6169880957,7720465589,4815626837,834429366,
   5896372882,7392921622,4487825602,1035782897,5840862759,7027527459,3914563895,1527296826,
   5919855372,6578451558,3148161766,2182526951,6044149039,6028786317,2217494105,2916254644,
   6105884024,5353448198,1194527068,3650142699,6057692401,4531533699,123961611,4286245016,
   5854465286,3606127606,937601599,4788209539,5468601953,2598116851,1909676316,5108207854,
   4936607682,1561288192,2766784213,5228045371,4268368637,562806919,3454021472,5176761732,
   3526160262,370877185,3964568375,4958459127,2760827111,1175830196,4306946514,4640640788,
   2012312454,1851755669,4485622019,4252538665,1343220199,2375614592,4554904110,3853044266,
   760727404,2758088879,4525345803,3483728497,312722545,3014278242,4459191158,3173703518,
   12957597,3149738157,4363801271,2962148119]
private def pvm_w0_1_p1 : List ℤ := pzig
  [186792330,3192315068,4281626214,2849276808,222600897,3128990345,4204850225,2862541591,
   99668212,2975673984,4141894958,2976650192,173376494,2693500581,4055701307,3194844587,
   609936665,2276926340,3913186038,3455623616,1188776676,1671758859,3637999639,3713820925,
   1889912405,873667396,3165074424,3851720554,2630203722,135151832,2402801329,3760820311,
   3306563503,1286612545,1318513570,3286142236,3726122110,2465129144,94444222,2312926039,
   3687358387,3436765007,1692162317,779368568,2927513752,3861081008,3200676794,1218542828,
   1282901267,3305562295,4058361401,3254256687,1194398571,1364116398,3490082230,4411742394,
   3788928008,1823094150,831520015,3304875641,4796489307,4818384711,3335586661,769003613,
   2141698862,4567673146,5829100026,5568089046,3823452574,1006436314,2211184885,5070690345,
   6912741845,7320720091,6189802527,3724289273,379697081,3236742830,6490265262,8837765558,
   9910864886,9551058008,7806561042,4903724222,1197370234,2895649311,6964689623,10656425403,
   13701896417,15926805029,17252734025,17687556243,17300940321,16189746331,14444735917,
   12123843833,9225898569,5656382971,1184266131,4606758854,12375770580,23103426966,38205535392,
   59687907422,90345546616,134015055938,195897127604,282966055910,404475662036,572565011664,
   802967941488,1115831918908,1536645216308,2097255949994,2836949749268,3803540482064,
   5054417759692,6657479155276,8691853157960,11248297824328,14429147729458,18347679627868,
   23126771514846,28896739000274,35792251709122,43948267619800,53494976884650,64551814038606]
private def pvm_w0_1_p2 : List ℤ := pzig
  [77220671691856,91578525838406,107669761589712,125498565377748,145021817180032,166142962572442,
   188707359848066,212499577722836,237243064036470,262602515994748,288189158336550,
   313568979936554,338273799615998,361814841953288,383698320211234,403442361783678,
   420594484548636,434748750387530,445561693445580,452766151864724,456182224817770,
   455724727415382,451406713507710,443338864882966,431724787225512,416852490928004,
   399082551982036,378833629607584,356566150074694,332765041016612,307922413381278,
   282521040986220,257019387879380,231838792700600,207353250374944,183882048738700,
   161685334763892,140962514580328,121853244428738,104440654329684,88756367536814,74786837948016,
   62480522324576,51755429534534,42506638601238,34613443945508,27945862725620,22370318952000,
   17754396228622,13970620768262,10899295259800,8430450187958,6465011698574,4915304678350,
   3705017899944,2768756938246,2051302353460,1506677569694,1097114947314,791991446092,
   566788372152,402114019740,282814259062,197184675908,136288857438,93380751396,63424454176,
   42701977356,28498134976,18851335780,12359441342,8030701308,5170896204,3299049564,2085304258,
   1305718856,809782676,497351542,302463514,182111820,108543704,64036018,37390068,21605680,
   12354788,6991056,3914572,2168996,1189234,645238,346438,184060,96754,50318,25876,13146,6586,
   3250,1570,738,332,140,50,12,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_1_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_1_p4 : List ℤ := pzig
  [0]
private def pvm_w0_1 : List ℤ :=
  pvm_w0_1_p0 ++ (pvm_w0_1_p1 ++ (pvm_w0_1_p2 ++ (pvm_w0_1_p3 ++ pvm_w0_1_p4)))
private theorem dk_w0_0 : muxFastIterBSlideChk 6 513 phbv_w0
    rkmViHi_m512_r512_s1_c1 pvm_w0_1 = true := by
  decide +kernel
private theorem dk_w0_1 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_1 rkmVoHi_m512_r512_s1_c1 = true := by
  decide +kernel
private def phbv_w1_p0 : List ℤ := pzig
  [150030357593772,211864137972916,259098768569390,298741765646384,333511742757794,
   364805084281922,393452539729530,419996184100134,444813093367776,468178212579490,
   490299402776632,511338383572658,531423946379120,550660663903640,569134841727266,
   586918710106286,604073453300022,620651447908716,636697949028614,652252382208210,
   667349348381050,682019416115498,696289753776634,710184639476460,723725876528388,
   736933134983118,749824234725976,762415381922568,774721367887554,786755737435056,
   798530932252902,810058413690634,821348768466952,832411800117322,843256608467692,
   853891658999022,864324843633378,874563534205502,884614629669252,894484597914750,
   904179512930842,913705087931872,923066704972734,932269441497494,941318094201624,
   950217200533384,958971058114230,967583742319674,976059122229626,984400875129634,
   992612499721120,1000697328178622,1008658537174974,1016499157980608,1024222085730488,
   1031830087941200,1039325812351200,1046711794149000,1053990462646822,1061164147450954,
   1068235084174576,1075205419733934,1082077217264504,1088852460690044,1095533058974098,
   1102120850080578,1108617604667468,1115025029535364,1121344770850498,1127578417160058,
   1133727502215994,1139793507622002,1145777865317062,1151681959907768,1157507130860532,
   1163254674563906,1168925846270278,1174521861925528,1180043899894428,1185493102589004,
   1190870578006474,1196177401182810,1201414615567566,1206583234325126,1211684241567132,
   1216718593520528,1221687219635266,1226591023635482,1231430884517622,1236207657498764,
   1240922174918168,1245575247094814,1250167663143590,1254700191752484,1259173581923106,
   1263588563676574,1267945848726796,1272246131122914,1276490087862674,1280678379478282,
   1284811650596268,1288890530472746,1292915633505396,1296887559723364,1300806895256294,
   1304674212783498,1308490071964358,1312255019850856,1315969591283164,1319634309269132,
   1323249685348456,1326816219942306,1330334402689086,1333804712767012,1337227619204146,
   1340603581176448,1343933048294440,1347216460878980,1350454250226684,1353646838865436,
   1356794640800438,1359898061751258,1362957499380230,1365973343512612,1368945976348876,
   1371875772669438,1374763100032182,1377608318963072]
private def phbv_w1_p1 : List ℤ := pzig
  [1380411783140150,1383173839571194,1385894828765304,1388575084898666,1391214935974744,
   1393814703979092,1396374705029056,1398895249518520,1401376642257936,1403819182609788,
   1406223164619702,1408588877143336,1410916603969260,1413206623937922,1415459211056906,
   1417674634612576,1419853159278280,1421995045219206,1424100548194046,1426169919653560,
   1428203406836172,1430201252860698,1432163696816296,1434090973849768,1435983315250282,
   1437840948531602,1439664097511942,1441452982391498,1443207819827750,1444928823008610,
   1446616201723484,1448270162432330,1449890908332766,1451478639425298,1453033552576738,
   1454555841581852,1456045697223326,1457503307330070,1458928856833940,1460322527824910,
   1461684499604768,1463014948739354,1464314049109392,1465581971959992,1466818885948804,
   1468024957192930,1469200349314580,1470345223485536,1471459738470454,1472544050669048,
   1473598314157166,1474622680726816,1475617299925156,1476582319092486,1477517883399264,
   1478424135882194,1479301217479370,1480149267064558,1480968421480594,1481758815571942,
   1482520582216442,1483253852356252,1483958755028022,1484635417392310,1485283964762272,
   1485904520631628,1486497206701932,1487062142909188,1487599447449768,1488109236805726,
   1488591625769458,1489046727467768,1489474653385334,1489875513387588,1490249415743040,
   1490596467145046,1490916772733036,1491210436113218,1491477559378762,1491718243129500,
   1491932586491120,1492120687133878,1492282641290870,1492418543775812,1492528488000398,
   1492612565991216,1492670868406222,1492703484550826,1492710502393532,1492692008581210,
   1492648088453958,1492578826059576,1492484304167684,1492364604283450,1492219806660966,
   1492049990316264,1491855233040000,1491635611409764,1491391200802098,1491122075404142,
   1490828308224988,1490509971106698,1490167134735024,1489799868649810,1489408241255088,
   1488992319828902,1488552170532806,1488087858421100,1487599447449768,1487087000485146,
   1486550579312308,1485990244643182,1485406056124400,1484798072344884,1484166350843166,
   1483510948114456,1482831919617454,1482129319780906,1481403202009918,1480653618692018,
   1479880621202972,1479084259912370,1478264584188958,1477421642405744,1476555481944862,
   1475666149202202,1474753689591824,1473818147550112]
private def phbv_w1_p2 : List ℤ := pzig
  [1472859566539726,1471877989053318,1470873456617018,1469846009793700,1468795688186014,
   1467722530439220,1466626574243760,1465507856337652,1464366412508624,1463202277596056,
   1462015485492682,1460806069146082,1459574060559950,1458319490795144,1457042389970508,
   1455742787263478,1454420710910472,1453076188207046,1451709245507834,1450319908226266,
   1448908200834056,1447474146860466,1446017768891344,1444539088567934,1443038126585462,
   1441514902691468,1439969435683940,1438401743409182,1436811842759462,1435199749670418,
   1433565479118214,1431909045116470,1430230460712924,1428529737985868,1426806888040304,
   1425061921003880,1423294846022532,1421505671255888,1419694403872408,1417861050044232,
   1416005614941784,1414128102728078,1412228516552752,1410306858545824,1408363129811136,
   1406397330419526,1404409459401692,1402399514740740,1400367493364438,1398313391137148,
   1396237202851422,1394138922219300,1392018541863236,1389876053306710,1387711446964482,
   1385524712132484,1383315836977364,1381084808525640,1378831612652484,1376556234070128,
   1374258656315852,1371938861739584,1369596831491074,1367232545506658,1364845982495562,
   1362437119925786,1360005934009518,1357552399688084,1355076490616410,1352578179147008,
   1350057436313442,1347514231813286,1344948533990546,1342360309817534,1339749524876190,
   1337116143338818,1334460127948230,1331781439997302,1329080039307868,1326355884209012,
   1323608931514660,1320839136500518,1318046452880298,1315230832781220,1312392226718778,
   1309530583570736,1306645850550332,1303737973178674,1300806895256294,1297852558833842,
   1294874904181880,1291873869759762,1288849392183566,1285801406193032,1282729844617510,
   1279634638340842,1276515716265172,1273373005273642,1270206430191930,1267015913748590,
   1263801376534176,1260562736959068,1257299911209990,1254012813205160,1250701354548018,
   1247365444479496,1244004989828768,1240619894962422,1237210061732012,1233775389419908,
   1230315774683402,1226831111496996,1223321291092800,1219786201898968,1216225729476124,
   1212639756451648,1209028162451790,1205390824031510,1201727614601924,1198038404355330,
   1194323060187638,1190581445618160,1186813420706624,1183018841967300,1179197562280136,
   1175349430798750,1171474292855178,1167571989861228]
private def phbv_w1_p3 : List ℤ := pzig
  [1163642359206272,1159685234151380,1155700443719572,1151687812582062,1147647160940316,
   1143578304403704,1139481053862594,1135355215356646,1131200589938114,1127016973529906,
   1122804156778178,1118561924899188,1114290057520156,1109988328513836,1105656505826510,
   1101294351299056,1096901620480802,1092478062435756,1088023419540884,1083537427275990,
   1079019814004812,1074470300746870,1069888600939574,1065274420190116,1060627456016588,
   1055947397577754,1051233925390882,1046486711036982,1041705416852748,1036889695608504,
   1032039190171342,1027153533152630,1022232346538996,1017275241305862,1012281817012470,
   1007251661377342,1002184349833030,997079445058856,991936496490370,986755039804048,
   981534596375736,976274672711146,970974759846684,965634332718646,960252849498782,
   954829750893986,949364459407716,943856378560598,938304892067416,932709362967454,
   927069132704976,921383520156268,915651820599428,909873304622756,904047216967188,
   898172775297882,892249168899572,886275557289858,880251068744038,874174798724484,
   868045808206952,861863121895424,855625726316300,849332567781822,842982550211648,
   836574532800278,830107327516854,823579696422362,816990348787686,810337937994208,
   803621058196516,796838240724602,789987950200236,783068580339340,776078449408740,
   769015795301946,761878770194184,754665434731926,747373751706440,740001579154262,
   732546662819886,725006627907158,717378970035628,709661045306178,701850059366420,
   693943055349968,685936900544622,677828271621868,669613638233368,661289244748302,
   652851089867472,644294903804558,635616122670138,626809859627728,617870872310516,
   608793525888868,599571751057502,590198996061444,580668171693466,570971587962260,
   561100880836216,551046927093536,540799744830376,530348376559778,519680751027500,
   508783518808972,497641855339054,486239223125588,474557082308732,462574535153418,
   450267885054164,437610083501196,424570028123774,411111659655556,397192782599830,
   382763498666308,367764085232198,352122057775292,335747996365228,318529434208288,
   300321579893234,280932602837608,260098992723902,237441329558472,212377215898816,
   183926164978234,150176228381196,106191033759136]
private def phbv_w1 : List ℤ := phbv_w1_p0 ++ (phbv_w1_p1 ++ (phbv_w1_p2 ++ phbv_w1_p3))
private def pvm_w1_1_p0 : List ℤ := pzig
  [379968,1205111,2098368,1627487,81031,2476607,6498822,4696374,3798126,2696503,1686102,10917385,
   18711932,4885749,145303615,392244696,438419967,75392470,1002812197,2815149076,2578777423,
   699300004,2098611340,2702648615,5996090421,4370156021,543254129,4237462652,6211034090,
   11184498706,11523765882,12963396442,15482699746,17113024756,7584101598,9448512468,845318721,
   3734350682,10871624096,8678799622,6687168928,8590309370,9104895026,5255218656,959553203,
   6360094145,8165198521,7572018637,1040234425,253158888,10393215628,7712836124,3604856160,
   10423988340,7495104649,10861510365,5156406691,2699253609,481011812,3270397782,72220661,
   7209268785,4256356719,4539034741,1251008262,8521907278,6612310262,5295424457,5881302847,
   4363110781,233987391,2427265556,3452633305,6934635571,6279299777,681502727,249673040,
   8478351380,5143758226,1666086247,1150163895,3786066345,4836064061,2204513637,2234946101,
   6101924219,9525717339,1875752279,2934998841,2962528476,678102774,931163003,6423614976,
   7450780812,2781828086,3692406298,1204139418,5102188153,3631056379,4967435789,2217124095,
   2596302366,1908042211,1327104672,2664324588,6143849912,6881200606,1966408220,1988947715,
   1957452315,1672550495,2808736467,4148897580,689523606,8684203970,3586198204,1481380883,
   3975757045,2754502793,956755652,681947056,1162079720,839743520,6919147820,3630737860,
   1146152896,453613055,2597043591]
private def pvm_w1_1_p1 : List ℤ := pzig
  [996439927,6346682304,2266148948,805468752,4898491359,3710652907,2391865688,1042239373,
   1425652489,3563388751,1478092807,610620436,1359217643,2316180836,5901993774,4437931638,
   48997084,4486953969,73881307,989547028,2018013098,345804951,2094894521,1472125260,3931960020,
   1174604672,279107956,1774612796,4866996478,3463331268,2671003344,1000332257,2016641190,
   2396215348,2804268068,3812428248,2135048390,2493479703,3419612703,3048151709,1227061789,
   2624586159,3234058254,3816402226,2980208612,2322124792,1367621437,2586811055,4328242,
   730393096,4106686915,3930506213,5671887921,282907508,1765101364,1110881743,533453341,
   1421284835,1740330183,3136564111,4131581340,4500815782,3699221876,1666568756,3325072859,
   922096533,262239984,4535973104,1219445021,380397978,76628386,4453430015,4419185713,1647352857,
   5568096759,853221295,2746495084,6057431558,9281529316,6258344903,822033052,2267882195,
   1213767975,840084124,6340190694,7186413914,3823649455,4412793165,507508823,9610606071,
   13283242365,12055679322,2218293236,483422746,1137141429,5032283405,19013753923,2925869838,
   15866488058,6089403325,4110310913,9751887225,6145998464,6641659395,27882813200,23168008317,
   38635481026,60413586475,12689401203,13703809888,44896053929,1150435422,45215528072,8663761833,
   35374013881,20286127328,60140826350,18614242596,60515089457,106308716575,93331720211,
   38138021273,35098701760,115161788310,205106457168,316318024424,464002666172,665933162916]
private def pvm_w1_1_p2 : List ℤ := pzig
  [943215209340,1321759631956,1833840909608,2519587796984,3428400365294,4620281952330,
   6167031974812,8153206677032,10676723099360,13848955454024,17794156594760,22648035932598,
   28555340854348,35666319671158,44131989215238,54098191452646,65698503678138,79046164741538,
   94225287959714,111281738954898,130214153285584,150965646346858,173416819184888,
   197380679721816,222600069745176,248748106919612,275432017334126,302200554129010,
   328554983145374,353963381539194,377877755723432,399753258645028,419068593075322,
   435346547274720,448173538788680,457217051356396,462239940958410,463110754271054,
   459809434484780,452428069000198,441166640316276,426324051742440,408284988404336,
   387503417941758,364483715493778,339760502017832,313878309302018,287372131945702,
   260749804836618,234476967719184,208965163293848,184563381006092,161553124783572,
   140146867456066,120489572097516,102662821115086,86691002569512,72548960191612,60170515181468,
   49457307546940,40287473947508,32523768308008,26020831009338,20631414228032,16211463189944,
   12624047024612,9742158654476,7450600591750,5646717910204,4241259268280,3156387903646,
   2328930646456,1700853551256,1234016662876,883568857768,629694814162,444416602244,308566705334,
   214345519600,148443116564,99626749950,65771532198,44694080102,31322302304,21049904158,
   12327684316,5775468088,1817977682,83703661,773151121,849435963,657238211,401486635,190705387,
   61389569,1761781,17419936,19137104,14817460,9398640,5059662,2343766,919500,274796,28282,40615,
   42855,27729,13561,4801,695,660,800,572,324,160,68,22,4,0,0,0,0,0,0,0,0,0]
private def pvm_w1_1_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_1_p4 : List ℤ := pzig
  [0]
private def pvm_w1_1 : List ℤ :=
  pvm_w1_1_p0 ++ (pvm_w1_1_p1 ++ (pvm_w1_1_p2 ++ (pvm_w1_1_p3 ++ pvm_w1_1_p4)))
private def pvm_w1_2_p0 : List ℤ := pzig
  [1164190,2192287,1879304,1175141,2894298,3527931,885741,2421531,8613562,7506984,36063785,
   149587192,350947727,580524476,799944297,1230696730,2052398045,2223254870,298734935,2079358219,
   1225464576,1362669012,1818698731,494746407,1003521594,3399166226,1046013091,3545374545,
   5496596145,2365720297,5755160279,5646074498,3608887916,6008740342,11294538184,10486436482,
   14145864620,18746882306,14125427460,5720315118,3715666322,5124039606,7939011356,4651074924,
   8556899412,6871809984,10008119474,13275133664,819892366,5425595498,3573686683,12202413977,
   4943508733,2569096119,3416741299,2007830882,12018802528,8812819324,6501835038,504997148,
   6779627583,9072750173,2288257423,2028144745,791444208,4372187892,3173653365,8002884503,
   8304586397,20008088,4361362350,8578901014,644481110,6017320459,1819226945,1790901747,
   475663359,2203772554,3607887581,7278433133,8427959209,5546356,1221466369,5092622164,
   6747207074,403800592,898064539,2298545391,2817075261,945845028,2099706627,10158795813,
   5627281951,2847312953,5211189215,810696495,3255984595,759650970,3117897100,3271541744,
   6257875830,6481792980,4096378600,1252554991,2299225753,6662785497,1881335432,3824671069,
   2619528483,1735686935,485707925,5449917282,5815781992,4896426326,1714654876,2757079934,
   2310435735,3164998729,3635598559,800097708,6644722036,6937114828,655657397,1817963700,
   1228368319,1706769889,47145228,3374146281]
private def pvm_w1_2_p1 : List ℤ := pzig
  [740899468,1646542600,5443467556,6868103852,363880550,2672739377,1895227715,2737554150,
   6047468934,473113122,940611389,1545559627,929075214,1018220481,2579984717,44825522,247775863,
   3633741409,3885578315,2562597295,3605925440,5652030956,3994676564,2122602073,144653742,
   1371865140,1175792458,749479075,1950108077,130032656,3175168242,14574353,123882086,22212472,
   3396066270,2331062420,3785142162,4195311962,453927207,121092784,2606594026,3820934098,
   2778010778,4824892866,188935721,132766743,1796824829,5087513849,2651532501,1425421279,
   4040808970,3738235858,2161309552,2021887443,1094927336,3976154486,1920323723,1202293751,
   4487608553,2888501353,4540236345,202081237,719315700,172441435,538135567,3414324161,
   6208058147,2598943542,5140830868,530386274,5682809330,3796485037,2876374746,2471474059,
   942908512,4728329230,964939967,747063555,1059849300,1314515150,6749258539,7849416273,
   4864403517,6085435680,6245795123,10350630256,7774858786,4909780383,5488205979,4892564568,
   100677527,8777398343,18965004530,3435702701,8408036860,14726579587,17233024582,45259706971,
   28099025424,15399853415,17443029582,8290001866,39707288937,17894537140,1937655762,26030363537,
   26168877864,9128995120,39025002499,1799934451,26846170504,7077938829,8652694665,27808220052,
   13795411994,39502651311,44684592017,2510050254,26108279324,4441902259,38939563665,26064608917,
   23789210636,60184746226,49230165662,1227564501,58228929763,92332894619]
private def pvm_w1_2_p2 : List ℤ := pzig
  [92426291273,63145929011,14711202251,45500521890,116432970758,203195689138,315701529146,
   467694612554,676671112678,964567345208,1358922101398,1894274141908,2613649235790,
   3570050256508,4827879242282,6464204508768,8569755012334,11249492738250,14622591818592,
   18821643956782,23990913089288,30283478392424,37857137601794,46868997414786,57468756542298,
   69790786143540,83945224276656,100008417389480,118013155386588,137939249399932,159705082212588,
   183160806983170,208083867868486,234177458320882,261072417636592,288332897806782,
   315465918967124,341934684331352,367175260226996,390615964217138,411698568105438,
   429900236685986,444755007303178,455873582893392,462960267882194,465826020478938,
   464396817969390,458716818190960,448946128734320,435353338922584,418303299485962,
   398240924029124,375672011627094,351142237978432,325215517763478,298452927143994,
   271393227516432,244535968262986,218327623504810,193151724847266,169321857122402,
   147080350654142,126596192830476,107973987600516,91250679127280,76418144732806,63410703357120,
   52141334552700,42482305005260,34297458621930,27439020037928,21749694453918,17083869961610,
   13297813961724,10254218121524,7835723423380,5934480470432,4452013669742,3308571371918,
   2437852262150,1780285499362,1286714896022,920889722958,654286084866,461536536298,321778382596,
   220957378534,150190000900,102223450680,70016410356,47679669448,31463686334,19538410484,
   11071627574,5476743576,2129691342,384433464,340446107,503109735,418719761,270661515,142866633,
   58797883,13716091,5342626,10274358,9125622,6306386,3733584,1949754,899574,357682,112758,19068,
   7797,10205,6457,2881,803,76,302,268,170,90,38,10,2,0]
private def pvm_w1_2_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_2_p4 : List ℤ := pzig
  [0]
private def pvm_w1_2 : List ℤ :=
  pvm_w1_2_p0 ++ (pvm_w1_2_p1 ++ (pvm_w1_2_p2 ++ (pvm_w1_2_p3 ++ pvm_w1_2_p4)))
private def pvm_w1_3_p0 : List ℤ := pzig
  [2253212,2562129,1856860,2697329,2652110,1196024,7996955,40058922,141061947,332518816,
   627298153,995648884,1370461601,1707541332,1592202841,419606294,1366305270,1537956307,
   835582471,2389078178,586832119,797241459,1146371479,2264965268,366847263,282509422,4647790663,
   4305275478,963569522,399367616,2672195990,3770071335,5915333289,3362529503,3398537269,
   2075179777,4266065980,4084749560,5382421814,5594486422,15107595190,18827520638,12178699048,
   14772868902,3555664318,6696213634,9907618922,1394089586,5353492078,9014935932,7079257616,
   6847746674,15107979848,9492441454,1473059338,1126665345,2228993879,8310383899,7348866571,
   4300038129,3609074925,7300255182,10851382238,9366986020,3123455252,1125655736,5573470825,
   8687988389,2894108129,252922951,3716203754,3943251772,8021347891,9168585813,6213266825,
   2725407666,2401032052,5164706668,2395744206,5755706761,2339225357,1391569496,299624984,
   916253534,1325446661,7838906577,6522525127,4538901373,4739742295,6715210692,5044948774,
   116147646,158223919,414810617,2291601396,245070897,2535636561,6716052787,2242043255,
   8033674623,2912101999,4997351641,4268020831,228584531,3183855033,832175352,4682331244,
   8385125700,5292396428,3824488810,1464866457,1090391361,32492207,1442340021,5206972785,
   2937713749,4150006225,1671883910,3626567368,671836108,7691719698,5995120572,2334340516,
   2292477269,5617587821,1104469953,1397691042,3249831108]
private def pvm_w1_3_p1 : List ℤ := pzig
  [5067606278,1560416946,2400466414,754362884,1192882820,1913318701,5052164641,2564887383,
   3272214422,7243711552,4827223378,2278542565,462815531,1531862714,2953579084,791331538,
   2521531512,1266703510,924087214,899886587,2476982811,48485270,3243491798,1469322821,
   4260559769,6832224273,1305552907,2533824022,2910950938,1001309300,119137950,4004614364,
   1491995032,690121819,934804575,1045563854,1579895037,1942531370,1559502140,2214774239,
   694449654,22444725,3739544324,3666864788,3286438254,818993132,476140734,2340765668,816517842,
   5460678080,1517527322,4635940144,4024754580,180863048,5815316689,4813593935,69140133,
   1175818208,71958496,1900319638,1196914792,1003726513,7357720094,3269152483,3321975482,
   1370481549,5036251315,3871213229,4704071199,2934183718,1096684628,2146584619,4642372425,
   808601013,6204107883,4136892418,239942815,8056990602,3030271779,2905121205,7760973406,
   1468880513,2183024223,2663743605,16748293032,17734344625,18534910560,13852275915,12282874374,
   37182294669,27773331446,19559737181,2053974082,21604083368,19533774411,17361642402,6202256703,
   13832247177,21059886730,15172136933,3035968157,38467320242,8738528565,27395148239,12579271604,
   2696188611,21138184381,17501080276,20161164930,25002152835,20967114947,17631139198,9732215468,
   18449414235,5201197833,16905607476,3437499667,31243687885,11109741273,32841338568,36424268990,
   5591294143,37210065689,22762905725,11260076526,18253804728,10824412819,42517622559]
private def pvm_w1_3_p2 : List ℤ := pzig
  [41382863473,4511270531,40292049342,61106912454,45001617360,1996475490,46212356561,80219370081,
   90515177481,77276957979,45765340275,1333975015,53763648694,121550385404,208287796674,
   324137643362,483102182940,703449574186,1008595256140,1428321077818,2000210981620,
   2771203942184,3799175791190,5154452081384,6921130881860,9198067715080,12099351224258,
   15754079940300,20305240132396,25907487720652,32723660840966,40919898746236,50659317302396,
   62094287627700,75357477652818,90551941872722,107740676023042,126936180534582,148090684843960,
   171087757981908,195736055543236,221765920518798,248829460476686,276504568927816,
   304303141162102,331683484774266,358066606059704,382855824600350,405458723056420,
   425310596521864,441897533991488,454779062676914,463606445683496,468140466572680,
   468258426240772,463965948223382,455386384646792,442769449589802,426459745359656,
   406904818235270,384609746711158,360137914590568,334073493548310,307000992074584,
   279493644234976,252078783573032,225235019875480,199379112329014,174848263597076,
   151909862454874,130756286057976,111501658035932,94198879091962,78844149997508,65379348636224,
   53709602172998,43714504139258,35250184987760,28159762091568,22286251152592,17475424455444,
   13576341340314,10448044417194,7965324234416,6017225438038,4504154328440,3339433247178,
   2451742405778,1783422447460,1286329018764,919741454910,650896883382,455294005632,315069193160,
   216489026346,148285347746,101278640896,68559429730,45448462622,29039462994,17560007554,
   9828354106,4926880120,2070088768,587030772,57763085,251151487,241588729,167894619,94450693,
   42543461,12921487,713144,5128212,5239870,3902510,2458830,1371166,686738,308396,121914,40340,
   9528,250,1331,879,285,32]
private def pvm_w1_3_p3 : List ℤ := pzig
  [126,114,74,36,12,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_3_p4 : List ℤ := pzig
  [0]
private def pvm_w1_3 : List ℤ :=
  pvm_w1_3_p0 ++ (pvm_w1_3_p1 ++ (pvm_w1_3_p2 ++ (pvm_w1_3_p3 ++ pvm_w1_3_p4)))
private def pvm_w1_4_p0 : List ℤ := pzig
  [3421498,2517273,1363774,3431926,25703069,89717894,243877595,532523114,931121699,1342971632,
   1591706615,1401582238,546800673,741328431,1288107356,87319140,2118694377,1881602738,226553164,
   43275199,2448814351,2552716408,1116806945,2533130036,3255068849,1074022339,4163748330,
   975108263,1625761613,377292554,1284107453,1305203927,4430563614,1567513912,1008604178,
   1511550097,3130243565,3101895951,9799889785,1637267128,1023146944,1425689941,4158484524,
   643645244,7905792624,16905342350,16336342194,9638349402,13717620760,11159247946,5009178946,
   5409299762,8874828382,4372359578,997045844,9447831276,9398053370,11593011014,10808352502,
   7945144032,2379444978,708637304,1294943499,9574982713,9917548683,3538753459,2529538779,
   7396211394,8365371440,9498132824,5692234364,1675739184,5836210613,10538788175,798447199,
   4373947018,1820343738,381615992,4625845347,10671689147,5944716321,1995639274,761764644,
   5460664352,212036232,4482847803,547694154,799944279,994979354,1490119346,2813162642,
   6607189081,6472813013,10189859643,1666689323,3076188362,298958435,2486623604,430744297,
   2018844254,2325990408,1564037494,2156516999,653645427,3590162559,5525161137,5620547253,
   3336751741,5047885363,2927418365,5701384147,5330616413,3195834258,3287831202,7529995178,
   5492750644,478224930,3334082360,2633073320,214303671,2585449199,4972078895,1257914225,
   3730737349,3247163369,768806919,3773233146,7448985870]
private def pvm_w1_4_p1 : List ℤ := pzig
  [6345364158,2822511482,753721941,4346405199,1204032157,8418260,3113428238,1386402898,
   1524218950,3297349864,6662158660,1803442262,5348439581,5573360909,281182031,2075430500,
   4936289008,1053765364,1495725626,1743064632,776872526,442801838,682387672,4696768824,
   2807049658,570693292,3075193677,743650579,2691537690,4514348668,2021461517,6270825243,
   1298055123,3787034691,931822193,42856007,556119362,1757514478,2355160446,3424754164,812685497,
   1468547978,2351564077,1735653314,1502186524,90686214,700829243,1211619243,834362143,
   2074294654,4208928386,1997802112,1661168284,374578878,6633600840,5070946415,3297852848,
   3713030676,4293474524,8697884602,405424185,1097545001,3324245557,917739741,2500591369,
   1224260022,3452383833,5806750696,4001328259,2906857180,3708287850,2903136544,4527198318,
   9779319549,2963865514,9889230337,8095542650,16449756809,25912060620,26835586809,12024463120,
   19332347055,20198475976,18013084179,2464489964,21019311070,26615747371,19498034922,1997202718,
   15170621457,16591084268,10982734761,3177719240,18949198062,16127050013,3661754010,8928219510,
   28949978799,801716759,21228962010,18118871277,7237510765,29283814532,1001206317,24397312291,
   6230128406,9841505476,12233847161,7234701112,28456563968,3443150271,30142251955,3166824773,
   20476876794,266394941,17246409421,1473392558,13578061386,8142024087,23330900409,39639352,
   26719930986,11756979886,27329924347,36574671701,2481041597,32582261296,28519561764]
private def pvm_w1_4_p2 : List ℤ := pzig
  [4976271255,26618577241,14422123687,13168692948,22336895922,329988534,34274123621,51342273677,
   35427041081,4141031976,42963285440,59169181862,45309506928,9114144868,33719138645,68197239453,
   85383133173,83217958797,64227376757,32268116673,10134876650,63312328986,131030589674,
   220617117292,343079588896,513486703290,751705584690,1083482667598,1541807008496,2168478321940,
   3015792085940,4148240233058,5644105797106,7596806856406,10115814214026,13326946883644,
   17371809477302,22406172151052,28597013295114,36118199204118,45144389830104,55843784936478,
   68368577353534,82845708000802,99363996996356,117965786388756,138630970548066,161274760216572,
   185728595185614,211750336882170,239003180369964,267080929169624,295491376515456,
   323689124474128,351077210714992,377031645276894,400930461933098,422164840251514,
   440179251159642,454487249238750,464691127716670,470511243518286,471786370132812,
   468486210861900,460718046115578,448709962092320,432806646352854,413456257570458,
   391180239666186,366555660090830,340194622150390,312711516428606,284702139754274,
   256729183079188,229299779721946,202850189270644,177743386008072,154264650007540,
   132616126561970,112922132646884,95239970608038,79566019579796,65841927752724,53967623151684,
   43815173611780,35236692564200,28070193810744,22148753320594,17309970218320,13400500607166,
   10276836282206,7806956995584,5873647246334,4376377463628,3230035500238,2362270603292,
   1711878639340,1228531019718,872453870320,613034319904,426655763136,294714507430,202404068424,
   138172827160,93423139460,62116166458,40210167438,25043321268,14804369688,8170345596,
   4110164628,1803653960,616258000,86026052,97160505,122345747,92115701,54121399,25356237,
   8292269,138901,2692714,2949508,2278660,1482696,857020,449344,215260]
private def pvm_w1_4_p3 : List ℤ := pzig
  [94108,37220,13080,3966,998,228,96,86,72,44,18,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_4_p4 : List ℤ := pzig
  [0]
private def pvm_w1_4 : List ℤ :=
  pvm_w1_4_p0 ++ (pvm_w1_4_p1 ++ (pvm_w1_4_p2 ++ (pvm_w1_4_p3 ++ pvm_w1_4_p4)))
private def pvm_w1_5_p0 : List ℤ := pzig
  [3749392,4040126,29105209,110794202,306481497,659660334,1127329407,1508240694,1505833753,
   902389706,169406420,943447457,403946662,1350287594,2375889677,1186713868,99252514,1402153758,
   3505701353,2450456970,481547333,606479590,683129852,3545937599,1460787026,3096513330,
   1488144605,2691586669,2290181780,887985125,455685830,1930784738,1715727687,459424568,
   4970300015,2704024858,2983039688,2438938453,5680613890,1583970064,3030127739,3928677701,
   4380647073,6606547353,1102559482,2160631240,4521278289,3124574449,4955435184,9564600848,
   7035435110,15924468990,15632977144,10581896852,9234516578,10557288736,8928981678,5188106826,
   4882992126,4119480532,1510752106,11649259382,9999920730,9923553108,9639035816,9016436366,
   6673482634,1237817162,2044856673,8964835457,10053118381,3887326333,2618516691,410060292,
   9704836948,13927992416,4407005188,1848797086,4677523343,9043294445,693587376,1863848216,
   4293733030,224486084,3406426107,11650723189,3891010109,1742379413,282088400,3474441430,
   1159367443,1587160820,3053276989,2914186315,1395232434,5795603482,1902616302,1592555481,
   7446991277,7663035817,4548193693,590644743,2472423005,395470517,2257116146,701775855,
   3694406108,964766480,857553986,3093847594,2707398371,3911596459,3554863013,5160963821,
   1531890627,4538770215,6299397679,8239670403,4507892565,1888465652,3176712552,2488705016,
   3951790546,4621201774,5774361816,1021693284,930696344,597281657]
private def pvm_w1_5_p1 : List ℤ := pzig
  [632113743,3136876397,4765342855,5715536019,2392052861,1932758348,6129542064,6946240792,
   5447701212,2527106337,1325011235,1212356176,143776614,1384985689,2652689531,3219035316,
   6406569622,7097143814,484611124,2902714893,3100374885,851276641,254080801,202040710,
   3855705850,1334462546,3669533870,1153958985,2682250959,4451480266,5412258238,2871018296,
   2983197607,741149822,550256981,3904816474,2350868250,312711853,1152097715,2952257887,
   2994890267,2297603727,2083530495,2742170831,2678059304,240763736,5454424522,2159131749,
   3331680968,1419993757,1699041485,7024485638,2221025809,715668763,1638210433,779813086,
   1034846241,3369815400,2458965585,7260637422,795118102,3388519834,279087613,5178064913,
   8813989208,1580919071,14293563384,7270013149,16952463812,17274176019,18883226052,26474673807,
   23002214554,15761868555,5605012612,5226611287,152214530,13252176438,18397144519,27322974072,
   4193518821,21749382875,20668830548,13879592379,3794506791,14965909952,15865182717,2835379070,
   1916892886,17083090587,11329415052,703424140,17667443549,16686812662,8186669302,19293490253,
   10714991004,12350706516,22751868447,470247244,28035132652,4756103933,15658478625,14531006126,
   5057441768,23663736539,6869414719,13297324350,4345577501,8746140841,16352635502,12519933560,
   21513305175,20863067155,15547986784,24373672368,2369641103,12039480785,6230438004,10076608072,
   10576602641,16391383453,7071549402,21473162876,277789089,28326246529,20537500487,14932307272]
private def pvm_w1_5_p2 : List ℤ := pzig
  [31192342276,6529608516,28996858987,33880328425,4752873015,24133217326,23082133422,2165304073,
   21433766999,14225180039,10939435112,27668126352,17614326602,14111808033,44803192099,
   52603924857,31481701067,6782852518,41849052000,56967214436,46453761154,15922720606,
   22614092487,56837121539,78329434733,83832466833,74146571553,51936050501,19598749781,
   22306481240,75844242042,146273864256,242065686740,375829492124,564088917034,829836418788,
   1201278537998,1717475377608,2423912980558,3383323852668,4665160669472,6363305442348,
   8577906295978,11437936987270,15079135801516,19662129508874,25356835011964,32343009434982,
   40809466220746,50934499007698,62891410478604,76826891967502,92851686270426,111035328113098,
   131381278464798,153826296678986,178228648788120,204354105821370,231884290700434,
   260411069907262,289440049867886,318411471555288,346708747724724,373678138059246,
   398661229967200,421014856754884,440136807630342,455500143386278,466673083274288,
   473335475236346,475300437921442,472522298887604,465092747567534,453239540661154,
   437318210268128,417789653124198,395197120277358,370146209897418,343277724040740,
   315236673303108,286648916140888,258103025619200,230130134467810,203186768726820,
   177647866368210,153805771447790,131868812775786,111962286549704,94136642219632,78379811327638,
   64627700210526,52772844556960,42675058097864,34174195064516,27101073100218,21284341275050,
   16555183142208,12752346191858,9727253014390,7347197273598,5495787924776,4071832820988,
   2988310250656,2171938711048,1562721284162,1112761462530,784323350756,547684181560,
   379352629740,260865445668,178016667104,120247609464,80012119424,52087037878,32902333322,
   19982364626,11547376288,6269383532,3141064872,1408261340,527906730,130804542,16791999,
   50932807,43129045,26206729,12265821,3796237]
private def pvm_w1_5_p3 : List ℤ := pzig
  [248764,1608820,1671424,1276430,832028,486144,260106,128754,59248,25398,10162,3822,1386,506,
   196,76,28,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_5_p4 : List ℤ := pzig
  [0]
private def pvm_w1_5 : List ℤ :=
  pvm_w1_5_p0 ++ (pvm_w1_5_p1 ++ (pvm_w1_5_p2 ++ (pvm_w1_5_p3 ++ pvm_w1_5_p4)))
private def pvm_w1_6_p0 : List ℤ := pzig
  [9415499,77803102,264518039,643232678,1160754261,1552494174,1427757349,627469414,396648072,
   678439715,411249339,2035235408,2314324651,1012552690,629704735,2429164606,3216694179,
   618381826,1808957984,1410967897,1160292616,1151944933,1401557593,1904916412,2813014270,
   3887557819,1279382309,3100254552,1392426689,2181140402,2274455601,281970244,1027095504,
   4076781199,4748346686,1639844172,3094412063,1051409235,1316032926,3158193423,269580271,
   3255586450,748759334,3225813602,3191026344,515254903,9815829695,3408002459,1865269746,
   2815294241,4360757253,1579541767,1334851861,1118262063,2158192362,12569666656,9549504242,
   13165496100,13348622576,9772441292,11105917148,11296696630,9464803952,3630661224,2590700766,
   5313836374,4756750946,8068598676,10017707416,9212040406,8120263972,14283043434,9082847792,
   970246221,2062999864,6112232381,8083896071,9569452041,4819976039,2155830573,9919878870,
   11753808178,6488725610,5470244782,5532669911,5104137733,2656562447,2914481642,4976958588,
   1927714806,5271928035,4871320617,5864119863,5172620579,2279901767,2462896668,2224179874,
   992289991,1588755969,5998491075,1439277912,5941041800,2593454250,2042398934,3575740381,
   6384210377,2991973145,6264242677,3214559901,1833303023,767940955,4622189,6017307,1475718084,
   2802519298,2487995850,3086380874,2609657577,3463026325,3383972931,188943244,1919227511,
   6263081461,8538425245,5983771861,4224803943,2338856643,1328529317]
private def pvm_w1_6_p1 : List ℤ := pzig
  [2390224772,3286343396,6054430596,3412631428,2181658514,4090515972,896902742,1291928742,
   1133548453,3853185725,8617900887,5641895929,810276756,5681043080,5481106588,1448661664,
   2415531768,1762327634,4253824858,2250466979,5376775251,651973369,690400062,6948289588,
   4724841294,3250491956,945653677,1818312484,2771339469,4793048631,957371196,3743624188,
   3516130048,397051235,1567009577,840363311,5921892276,1277517278,5182928848,2507589047,
   1091858512,469243124,769820810,6365116842,3166599239,3306824938,654621831,2484638441,
   3714997791,226116772,8072983105,1744173686,33587064,2824579502,3265666796,6137406687,
   8594426596,7727151007,13537792348,12868265357,15539697900,18986687819,22142268544,23189900641,
   16727987608,12924073527,9345509564,7948750024,8718029055,12618914054,13714095309,12652743486,
   4757367725,3160781363,29058333644,16962265317,3760379684,19198680704,22034947007,7111525966,
   9281698348,15757095065,6358102910,3955683609,7909582151,17742277014,1528920373,5122880977,
   15415035348,10356049745,12897352531,18604777730,2446352095,18454727089,13635904662,5454035600,
   23273916141,1798146480,15219550252,16848825437,11798481995,21534133368,6838976074,18323022225,
   938349330,13623521600,8099164417,8848821019,16004810394,11849842830,10988100909,3510028323,
   13203741486,4414498393,26330150407,6940474963,23524391612,14326715544,15111928535,15647186223,
   5830998506,8471831638,6776192007,5071943291,15222248122,18368223962,6452636903,23952205727]
private def pvm_w1_6_p2 : List ℤ := pzig
  [6680211987,22176220360,21454271724,10058597367,32282973641,17060139287,17050978158,
   29816762052,7667757818,23474627635,30485883503,8840624979,16358499632,19605147542,344291868,
   19498705677,18890529207,2787220058,26596601480,31322564792,10527126836,23461909675,
   49526885085,51809645261,28991054123,7457503796,39730366466,54941857772,46901090354,
   21552640880,14137569309,46348682725,71491676241,80740012027,79167135515,63252274135,
   39549649529,6146558463,37143193706,92578714766,170046694422,275914405138,427835557764,
   644243606234,950008571528,1382473174744,1982227856140,2807139428874,3927730941988,
   5426820658772,7410873253778,10000455562458,13335266909004,17577946410578,22902156724860,
   29496468542910,37559726652214,47285588365464,58860995771014,72454551194706,88197015287150,
   106174919457466,126417063306562,148875029143244,173417706049688,199825005982260,
   227776969954856,256857185019534,286562727414778,316310140539972,345451796871438,
   373303373689222,399167659740200,422359339417652,442238852761992,458243788153364,
   469910979740234,476898223950880,479005156382486,476182163813340,468528300312960,
   456286882719230,439836189724466,419668689173468,396363667836046,370561432683004,
   342937489017638,314172606119534,284923172548528,255798665038690,227345480198626,
   200032726424044,174240832874430,150257402939558,128280575886174,108425516513404,
   90731309122486,75169737269252,61657596870000,50070835622790,40257221150496,32046282292472,
   25257794967664,19710109332512,15227854333628,11647571671718,8820627505614,6614140992050,
   4911173966168,3610840773900,2628175319000,1893312436472,1349854413436,952746101566,
   666165737108,461788864050,317494901430,216377539742,145877971268,96938204240,63174996318,
   40134592530,24689123342,14599834794,8231982960,4381794352,2171765564,980302700]
private def pvm_w1_6_p3 : List ℤ := pzig
  [385942742,118326356,15009590,14429005,15880249,9970333,4371133,931457,627000,1048046,945088,
   684014,434618,251198,134406,67248,31672,14118,5994,2440,956,360,128,40,8,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_6_p4 : List ℤ := pzig
  [0]
private def pvm_w1_6 : List ℤ :=
  pvm_w1_6_p0 ++ (pvm_w1_6_p1 ++ (pvm_w1_6_p2 ++ (pvm_w1_6_p3 ++ pvm_w1_6_p4)))
private def pvm_w1_7_p0 : List ℤ := pzig
  [107386081,426821354,978894353,1517459198,1523858349,734474692,297389914,412993069,877994345,
   2397740570,2403687721,1172108234,1031231473,2255026468,1652483313,1565223963,3007087672,
   855127509,694733497,209973696,122500587,969285307,2584729290,858891086,5466990163,2722067250,
   1138200780,230401648,777472832,4310474251,2948279538,298466136,1943290263,1902243450,
   2313908816,3953466547,1778598155,3541890338,625349903,592056374,571932734,1016624036,
   3479070139,723079011,1713118852,3436363773,1588670843,7358170678,5281008296,353641036,
   5990076411,110571180,2642536199,4711424825,187343228,2028168721,3957541975,4070123157,
   2462548507,214901272,3569936900,10767843110,10745788476,9627791414,10570985158,14038362704,
   11983102188,8964335706,12421094656,816579180,3619171398,6564555052,6560846790,2810567294,
   8386110846,10827681224,9099306030,14771634324,7260547912,6775964342,4272365710,1709259265,
   7822159161,9636054633,10323082311,2777487709,3661277450,9572746958,11453467684,5696090104,
   1986521373,5843463347,357695966,391810370,2767606242,4425395620,1479615543,2159652799,
   4641904739,9651476075,2498534529,147810041,2394142550,1134899446,4149351779,4631900023,
   945249481,2127564180,4542844780,1915845590,2358813258,2172892181,3449358957,5006344001,
   4665494327,4153602695,2244351721,1662973861,1427361197,2516494059,1586007136,4254963126,
   4952039176,595945469,2439790337,182637843,789799055,1235967292]
private def pvm_w1_7_p1 : List ℤ := pzig
  [3623508261,5212215289,5659822947,5590674217,7126313409,5559064545,1815949695,1074978585,
   2711522752,2987388558,5249673244,1797789610,1975346088,5998818920,3482224790,3778309654,
   6419930181,8230825233,5770025555,758586318,301110026,852883662,2755783756,2483988320,
   6988410340,3941424644,1800263099,5662960053,880698804,2162403983,4162835234,929134556,
   6668047374,5949086318,1630324737,280859183,7082843877,3892971176,1101860674,2032118730,
   241873587,114706104,4091057619,7100354578,2116008106,118818081,6292533314,6758550593,
   9702422730,10464597395,16595768180,13633154319,18191526400,17675264473,22189794016,
   20796443201,11381535790,13601572657,1863132787,7873344830,12044200933,14015325658,12800982451,
   8166952516,3248481838,8188211905,14478541378,13400656647,9761950530,9190629198,24516539999,
   15682965968,1859685398,18977050527,21452173528,2396836958,10919833423,12598026616,6287211191,
   4163547671,12154733622,4593428859,7014511022,14617730930,11852564115,2000337844,16871745744,
   11228168381,4606489725,14469529272,13702782731,14863254327,19817029566,6107401408,15371891659,
   10546438494,13556353106,17143029767,6105523875,18951013122,2591276293,18603640155,7386661572,
   13155555750,14128801377,13800061727,8573439724,2275520658,12604936167,2417958716,15329745108,
   3881626105,16143597095,3879186622,15014045444,4799329793,13461703013,10809776062,24895742772,
   497333692,24403078703,13064468893,10306505460,8400969548,7463432027,5377289723,8992055938,
   5603956520]
private def pvm_w1_7_p2 : List ℤ := pzig
  [14415047307,17774723915,6673280180,27021303680,13902659092,16386493291,23684389685,1764818018,
   27068960204,19835256742,11832803631,31035482833,16751927645,13796377184,27020904012,
   10575689670,16742973887,26641511263,12024710343,10945393824,17705405860,4242377010,
   17761824411,23852600045,10207352081,17671043910,34484554432,30644241634,3437166048,
   29972900543,51279603759,50735568365,26140419219,7475605216,38174179536,53000325808,
   46662278060,25056638476,7375001553,39240691211,63536151041,78290283445,79310320141,
   70124439319,52322712425,24903798997,9457866204,55074479028,118095897070,204412662666,
   328986772982,509276815936,766852314808,1135879160440,1657355674778,2382657357758,
   3381687908798,4738050344360,6552119004732,8948366385560,12070138903990,16078992684412,
   21159053804990,27509297469972,35335584650780,44848925645406,56254088042554,69733134055218,
   85436090505080,103468106451980,123869352128902,146601512211200,171539753553198,
   198460548660516,227033391080848,256824624758724,287305026699884,317857951698182,
   347797472175984,376396520870274,402914997579124,426627716015880,446858318895144,
   463014572757460,474615901984954,481314136358710,482912086104894,479375924134756,
   470835034033252,457571645016424,440006187837270,418677993651206,394217936684926,
   367315418812592,338686262222874,309044124196228,279073382432048,249403227758694,
   220586783117352,193088377232020,167277761950416,143428251714368,121718046390446,
   102236156159652,84993261504200,69935316557928,56957078090830,45914431447782,36636074009702,
   28935076575500,22619678650104,17502036406876,13404215867162,10161802683914,7626065134082,
   5665362539898,4165906346614,3031648270618,2183181256966,1555871264032,1097667799988,
   767019424306,531117252412,364469538348,247692850114,166408035268,110197490332,71647020574]
private def pvm_w1_7_p3 : List ℤ := pzig
  [45522925184,28121962518,16799122114,9647929758,5292599678,2751527020,1341409538,603554928,
   243828090,83494016,20436536,324534,3380597,2281351,673083,311106,669422,661928,510970,342698,
   208226,117076,61670,30684,14506,6550,2832,1170,462,172,56,16,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_7_p4 : List ℤ := pzig
  [0]
private def pvm_w1_7 : List ℤ :=
  pvm_w1_7_p0 ++ (pvm_w1_7_p1 ++ (pvm_w1_7_p2 ++ (pvm_w1_7_p3 ++ pvm_w1_7_p4)))
private def pvm_w1_8_p0 : List ℤ := pzig
  [460561741,1193144446,1676900619,1247630858,127079627,298935257,897698317,2572986736,
   2677880973,1320599108,742852857,1231318432,132422225,2561035815,2571107862,602241930,
   1600940333,624199739,1362198614,15747620,1551164979,3756486408,3257636287,2156436295,
   4182352624,941542803,1492806660,2585366757,2035049947,3007877450,1825627976,2648721633,
   155273589,2963760982,3845501453,421161605,2280456470,2128904484,2013454117,1351192113,
   1327913076,1307317555,1890368291,4873308768,283809877,1233823967,1344683653,3231417200,
   10993588,7902651109,1096422827,4364215794,3234963758,3086630116,1801432992,419648482,
   3776697425,2172463801,1280459891,2024239881,1708810489,2757537047,1448691781,9963829139,
   986151789,1672276728,2935242678,6892671952,10430949858,8335462630,7702962234,17959788800,
   11652408568,10040392646,8564332112,5662595446,5427034368,6524483414,2393681192,4305698826,
   6714543208,8662061184,10951895680,10045094180,11437748930,9941667544,9398808980,2176191780,
   3587718509,6295333379,13395754161,10227492113,1390851604,4858778014,11399442128,7409833390,
   607213886,303111641,1575396531,1381906193,2119070638,2559762278,4896515652,402957618,
   3106350561,8221762981,6408789511,1375371745,1665547008,65296486,1728407099,4197209529,
   2904657145,1980620393,2018189572,2888164934,3104735904,2492765112,418565173,1012667593,
   6532631641,3982045401,1978697591,2520354715,4444042583,4906893543,1749897329,1826910172]
private def pvm_w1_8_p1 : List ℤ := pzig
  [5402365736,587135380,262683870,80314806,822911266,1277414292,2104783751,1553787686,4434433945,
   3916646569,5897758297,6251734271,7091943955,5839212471,2907115161,24642480,4998959422,
   300652719,72837641,2659129046,9484157128,4704370606,6314082716,4934362869,5629701775,
   2191020653,4290220105,88788314,7558782623,3829558592,3520736806,6694087580,2853790212,
   1821155296,1752549271,1335293940,5098277581,4408788833,9908200916,4425859437,18028084936,
   10590278907,12881193132,19476014783,19217238658,16760827687,19268729262,16888075705,
   11240160004,5704597719,2555595235,13662630606,11417429649,15259187956,9528378233,4367351470,
   6451767314,9587289023,13621011438,9221667751,6825857464,11067916640,14665469369,12203944990,
   8529752695,13142579339,19637174446,15642245885,8639637377,21355884628,12838886479,4306026087,
   14793567878,9701368977,1801801642,10259363628,7012910691,4849367440,1008450600,13636307403,
   8012855750,6118978570,11561228003,11235482088,11206900450,17625232969,156322931,15760436006,
   9518616749,2344221837,21897671878,1622975329,14023049953,16755849692,14319854166,14833775515,
   2614997433,13191091720,10521795833,15635966127,13818991886,12995280830,12471980829,4028709627,
   16079486516,1550743450,14297015217,1862867088,11737976226,5297195397,9597124465,7675482406,
   5598015286,15983925141,13402538371,10715027576,11107642348,11208243583,11751815167,
   11267788080,13939637838,10852356571,19930051207,3738106320,23046126434,10859098136,8836443135,
   6629940301]
private def pvm_w1_8_p2 : List ℤ := pzig
  [5205842206,497636238,13331690303,8936823371,12162346466,18356857422,3835984927,25947165673,
   17115077797,13812067422,27343935342,8083034460,20361759521,20624216995,4996931536,28479579542,
   19208782058,8713776139,28367941655,17098715553,9031597468,23490243216,13198194398,11209756187,
   22799284931,14211459853,6558878960,18010258448,8384142468,11898560837,27433359291,21990123275,
   1975258662,27318056388,39188521608,26567523086,3582368897,34411588681,52781537587,47989242613,
   23363926219,8580520682,37425314842,51294729830,45954972622,26395698308,3001605029,34074465579,
   58270153781,73986837071,79301984863,73142640967,59304435799,38433518357,8824473973,
   29263272272,80350549318,153732765444,258843541800,411249487348,635199004550,959617490552,
   1423142102830,2079758522640,2996177553700,4254514608458,5959479943722,8237323158174,
   11234062663996,15119962709954,20088618665516,26349026705946,34121443894232,43633018444190,
   55104274514518,68733614161160,84685983032690,103077858292456,123956700652968,147284752716296,
   172928916286602,200649858317982,230092891620510,260789233259068,292166297755746,
   323560707475424,354236390525802,383413067923720,410301340452818,434136987847278,
   454214372140274,469921793947908,480775011445186,486441817147616,486756435960328,
   481727102965018,471536781909526,456533245515588,437207901691674,414167948020692,
   388106154905112,359768609692716,329919910058256,299308459144450,268636410318258,
   238536592623426,209555532303216,182141277977308,156636571067454,133278706134444,
   112205901475210,93468006253690,77039053752960,62830451977380,50704777328644,40490080108444,
   31993784170462,25014822931776,19353119438610,14816435045300,11225219923472,8416079437644,
   6244083121010,4583841592276,3329294677270,2392399269332,1701136428686,1197306309766]
private def pvm_w1_8_p3 : List ℤ := pzig
  [834446206858,576004259960,393747109958,266325303198,177945606440,117151906762,75751795370,
   47928069142,29551543318,17681946936,10222151458,5683391126,3023372662,1529471868,730075998,
   325325734,133212576,48897414,15443684,3941244,836740,388264,490378,546670,487202,370070,
   250378,154938,89156,48226,24708,12056,5622,2512,1070,432,164,58,14,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_8_p4 : List ℤ := pzig
  [0]
private def pvm_w1_8 : List ℤ :=
  pvm_w1_8_p0 ++ (pvm_w1_8_p1 ++ (pvm_w1_8_p2 ++ (pvm_w1_8_p3 ++ pvm_w1_8_p4)))
private def pvm_w1_9_p0 : List ℤ := pzig
  [1161111737,1807815208,1135472415,17338402,427704339,2314099940,3069822311,1581426686,99264729,
   35360842,623962370,2354798065,1713887890,1373917924,1602618517,1161163897,723338434,
   2688130342,3263318545,836669624,2196594102,4589847097,2708528552,1366149468,671164605,
   439565405,1919010805,211857205,3053561414,2292993912,5252289787,291449232,2074010302,
   551054407,1263438803,1623939622,1875830894,1526862349,4077691965,3627250706,144964985,
   471630031,1144849084,784501864,475031393,4479410573,1217653822,4796440522,2408432151,
   2365153163,2025960344,4337230936,918151853,3996851479,2060522113,3104234463,1841062966,
   542653190,7170189834,886089996,314642987,1867452418,2521476325,3787719537,1556171191,
   3491009538,5244673197,2529907921,2925053347,7963495669,4653944693,2579399654,2149202328,
   4350807862,5575710402,6720386814,12386809732,12978933920,12975526968,9744322630,9946274230,
   8775780380,6541752308,5979346992,2309692036,2937064264,8470422086,3938279896,8234062870,
   11438407242,9495587954,11927443532,12482429770,8699480154,6049073780,4758329071,10784765255,
   12884813505,6073751559,875358102,5955743628,7200444182,5745661414,2162022924,802933132,
   2532527183,1188988793,1958910260,6108463640,5209623200,1012229803,3870082551,7360549347,
   3204406585,1974187927,236831302,437315584,3291753523,3744867143,3068972831,1199377523,
   2064121483,2894252966,4060057996,3468796688,1809565766,4476056935,1534591675]
private def pvm_w1_9_p1 : List ℤ := pzig
  [3146878331,452461768,5087470313,7193052721,4255613951,1625866865,533198988,746596600,
   2976898474,762094183,2082413120,412836707,2167046058,323937657,2693521494,4278166781,
   1215118491,372762597,9653661831,5589548177,11404075379,617006553,2232135219,1108239004,
   2848122543,2636105977,1683314814,9516649224,8189427772,390194218,7909123854,11785227655,
   14710028328,19778283249,9162237332,20760158705,17185718732,17605431857,19876892544,8566679619,
   12241004148,2057096736,6013860977,7737146844,19756417905,13900108912,2346423427,5057088746,
   10236986382,10729552545,11644822276,8085928641,2064414946,9674692822,12977951511,10532338956,
   5603417091,6783709531,18019121284,12485590065,2197474410,15315583432,16319287351,10016075794,
   10675169928,20835514583,10811097266,13591686886,11903992797,8359748594,5635700970,9785048161,
   4700118782,3239874237,9072512045,7499467016,4340870687,7866803737,12456013842,3092397279,
   13297108385,13870347682,7000231438,13383897943,9108329314,11626025690,17696770747,5105870703,
   15916678222,5785103493,8538635981,17753540240,4490690124,19598716761,2259279800,17350831142,
   6492472821,8384541221,15409508102,7459585814,11427613907,5735248470,20631690942,1850917221,
   15379918507,3264504616,8444534158,9417865163,7611178053,11329701620,7394522628,8960873715,
   1651151897,12690146162,1108140948,14550558153,1194956811,17137106440,4498845916,17480920475,
   10137110579,10849037464,6023403626,15370613985,13583055517,10593101216,17278275092,3522600845]
private def pvm_w1_9_p2 : List ℤ := pzig
  [18604075375,6155788283,9910582232,7323713046,3999139175,1982171568,13761421780,9877001486,
   13753362791,21911708627,3036874211,22087262646,18217340070,10831613415,28168817223,
   13948422583,16407212488,24217954404,3125478272,20859452383,20010071491,6398013326,26541782958,
   20526619342,4921512851,24245310703,17202314795,4916038154,20089057448,14630324300,6491181655,
   20395126939,15486257077,2296066004,17825297700,14653155130,4968936091,24672469965,30529764355,
   15010313279,13343279360,35315412128,39054351946,21259714844,10778490935,39451110413,
   52096975759,44963558355,19902464169,11952410838,37272864532,49572566870,45455579360,
   25674976112,1934459091,30230227563,55142537083,71528013763,77183353913,74472437881,
   64084381895,45684134567,21080099057,10666585684,55084690102,118146564222,208667185224,
   343117722128,543519481242,837425608212,1264408222784,1878409118426,2746466802386,
   3953428975578,5607906492298,7841640498608,10808845154974,14689922383888,19691068323810,
   26037007667252,33964615374182,43717472372256,55533556199940,69627329173370,86173765116012,
   105293171377236,127031488204682,151339727216134,178059957238692,206917156752620,
   237513004264698,269324842373082,301715800534110,333954957131814,365242315021418,
   394738216214366,421600077763838,445024453944630,464287704417208,478781308695112,
   488042555005232,491780328113060,489891799199438,482466263479838,469777026690774,
   452264777702472,430513998056648,405221957434616,377161357209272,347140673925862,
   315966726227288,284411635320782,253184299790472,222906769491968,194097168500636,
   167160756393456,142388989555628,119964725410946,99971441663474,82405243537470,67189197812592,
   54189390899650,43231442863928,34115887946656,26631253888124,20564503727788,15709140625904,
   11871410447062]
private def pvm_w1_9_p3 : List ℤ := pzig
  [8874815731414,6562931055110,4800512423946,3473097234144,2485516374122,1759827705666,
   1233096518254,855269638976,587221620312,398959097624,267956406888,177625023368,115949339524,
   74328276988,46645453218,28562861180,17008553604,9815885808,5471233968,2934706000,1508915832,
   740410064,344976192,151755706,62679918,24255878,8905070,3284464,1397716,781752,537012,386710,
   267840,174086,106024,60792,33002,17038,8402,3964,1790,772,314,118,36,8,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_9_p4 : List ℤ := pzig
  [0]
private def pvm_w1_9 : List ℤ :=
  pvm_w1_9_p0 ++ (pvm_w1_9_p1 ++ (pvm_w1_9_p2 ++ (pvm_w1_9_p3 ++ pvm_w1_9_p4)))
private def pvm_w1_10_p0 : List ℤ := pzig
  [1939701603,1497549988,287302355,1161614372,3050905181,2428509572,130005670,1140838483,
   913560758,1510770671,1081975542,1430726094,1782407379,607173721,173375347,3270192016,
   1330935601,3680824607,4423674754,1626294299,1227893273,2437759618,303413959,1179534501,
   810421121,826519346,717830197,3781127622,907469925,4493266529,136330844,3811969918,212347176,
   1054252999,2051906957,3451448732,1935375621,2806505177,2810090590,1542145606,105173742,
   1962314901,524167683,2133346460,3026259323,580014547,4094000816,1839857282,3136857923,
   4039587233,4291282872,166377635,293069380,3791122081,1405688112,3606520322,304656173,
   2425303758,1383530287,3381529045,5919246621,2519324810,902600040,626774683,5563661348,
   4806131174,2289710183,97767663,67943397,3541082579,242105396,299715764,51568824,3855293347,
   6204486251,6128138777,3868451945,272993802,364709264,572339907,5134677868,4533204916,
   10457152658,13275899384,8929262514,11364929378,13692611420,8289854798,9128122180,5714129642,
   5065422040,3758636944,4119380790,4669763408,6626129782,7609755820,8524651604,8933179888,
   14016104046,15083002426,12374282058,4551236810,5382114621,9767958099,11193426465,4437361375,
   1726432041,3363105392,6615929036,6002460082,4082441886,2054475501,2576216157,299155021,
   4746678064,4994986462,4785898716,1458623344,6038136785,3070219601,4659162425,115980490,
   1867788335,1095603979,1080573525,3373749305,2958344989,5224645611]
private def pvm_w1_10_p1 : List ℤ := pzig
  [1944852601,1062589382,7182663810,814266120,764133064,1799472751,1854464386,1442911675,
   889213027,3469817703,8922133849,335596473,8276904613,1129709822,575042767,1680360162,
   968208037,420725202,2597568258,1111072858,1654688370,4224359527,9284170482,11105117037,
   16560491882,23000945047,7942397968,25049147791,12896583790,17015122817,11470305314,
   18061093201,646080766,4804566628,3980444219,16952815350,9244428609,17328528890,1871038867,
   740961631,7520720710,17210507997,6291849768,8931532031,4442364843,6619956092,9158100987,
   17096656978,2830807406,4922584695,10498257058,16501851345,1516327584,10331655016,12010013185,
   15845974976,4224394054,15579420819,17129523522,114872078,11761438107,17439731838,5272036697,
   13210101287,15667298540,1912166337,10041084911,9936801966,350072348,316495969,8401123210,
   6596475737,1063923251,10188868560,6812951595,197328276,16375493946,5071171555,6759958987,
   15370498246,3184049729,17568471923,8887635128,6387165602,16748678617,1568778456,13368185736,
   12613138441,9279412113,16869598280,3348435560,12241232591,9642354778,11886117690,15997850795,
   10285433215,15472211606,4846312944,11871861889,4474907368,12043791708,8975286423,10085149475,
   12639357360,9695757338,11415805345,4793646243,14703812936,8111364958,5012687615,4963202722,
   13099040144,2979865869,13026523863,2070681110,10233216670,5678946875,11860737301,7333042694,
   17181515404,2727052207,16379701761,400212893,17612601296,4615553884,13366020713,7299836947,
   12868909828]
private def pvm_w1_10_p2 : List ℤ := pzig
  [7669956444,13273450339,18425066241,1357133126,14037095788,2785000116,9650762659,5564447877,
   5949083716,655529358,12177728195,7633413453,13713968076,25547249474,6494590380,20581506865,
   22005567871,3309776204,25304416586,14811035060,14221390645,26668827869,10160834357,
   16592110502,21299359360,292381123,21158179225,19377534859,4200454330,24917740140,20587309566,
   1424017643,19250761247,17256183259,2303173240,17993109948,14680295300,2313793601,18184271491,
   18161174433,1136401249,16337491192,19287083290,5006266784,18371901593,33409635105,27473140067,
   4358326933,23234652056,40722809386,36608270666,12628133024,18270463589,43191050583,
   51987784959,40114367991,13892166807,15312993404,38732589728,49154023714,42808014380,
   23466197220,2344979307,29970347767,54000541593,69394270559,75808959855,74747170559,
   65888310201,49922789643,28835855247,1165485431,37960406788,93838073212,175095649258,
   297722600888,483721627968,761240622060,1170372520032,1766932268642,2622135967816,
   3825727991096,5492499270568,7764496736084,10809533888398,14822268503572,20025470075692,
   26664753940568,34998538583616,45288628225796,57789119679138,72728573186870,90288072904988,
   110581208320554,133635785658252,159374118502740,187594644971610,217961307193082,
   250002281093958,283115158722728,316578587681224,349574142440496,381219365053064,
   410607541731128,436849568390552,459116938940736,476685536322846,488976441161676,
   495588039476650,496316364308122,491164222905500,480340045103838,464245625913442,
   443451946111446,418664942128142,390685549453230,360368146981974,328579664831160,
   296160631436658,263890108404404,232457271352818,202441769862712,174303159655064,
   148378129998046,124883926029208,103926905302498,85515537031414,69576834585258]
private def pvm_w1_10_p3 : List ℤ := pzig
  [55974576040078,44527405489134,35025312558882,27243769125466,20955451072570,15939709300544,
   11989870894378,8918330033160,6559431972232,4770362044804,3430483209536,2439678555870,
   1716205048158,1194407123984,822467846074,560260263926,377319068496,250958054762,164575679170,
   106193897148,67258708294,41702855794,25244442596,14878599236,8515027014,4719417562,2526555470,
   1303059510,645732878,306696638,139342606,60540204,25252588,10252972,4186948,1820772,894560,
   501204,304400,188418,114274,66702,37246,19878,10152,4966,2328,1042,444,176,58,12,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_10_p4 : List ℤ := pzig
  [0]
private def pvm_w1_10 : List ℤ :=
  pvm_w1_10_p0 ++ (pvm_w1_10_p1 ++ (pvm_w1_10_p2 ++ (pvm_w1_10_p3 ++ pvm_w1_10_p4)))
private def pvm_w1_11_p0 : List ℤ := pzig
  [2464592329,912081570,1348459973,3064956126,1288759529,1801689257,1748035280,572705429,
   331570486,1034302336,2045282393,287193112,175248398,1559488482,939578774,5327763781,
   2739370766,2812388036,2836309957,176149668,812758212,36522937,2115441371,2202167202,187680949,
   213513423,1379369004,1197413335,3749170543,2905108522,2316962092,1480148326,3951839963,
   2590875035,4027400292,27970000,1679568905,1113545280,870331256,944985920,3311210023,
   1434934157,3432570728,17951156,460945719,1505822499,4884941678,3139093721,3367436451,
   368366868,2598988174,3994324594,4181006701,1045802027,591135770,2488301578,2223817867,
   675628067,850375100,2822715223,161360346,6619659356,1138128878,3492312519,1152249738,
   3116674625,4145578813,1366848331,1458256754,2533562512,2660353726,3227731024,1978702072,
   1937757795,252259439,3039981425,916447378,3443899884,1981919091,3572815755,3761419951,
   8247156045,1637061091,1744033705,3447391965,2127800741,1735241652,4185921112,6748730954,
   8034254680,10634849056,10896450270,12467853678,11146578588,9535949060,9659966350,5865309498,
   5170707112,2665146058,5675787664,5661549170,4803435372,5555939984,4922391684,10979698944,
   15447899470,17876971006,12870753220,5159740096,2186838187,7850040793,6835279325,10629509695,
   1752764705,2050623834,6225515150,6068436456,1900877158,160899977,3895049445,1092294150,
   3603617888,7544618244,2506648676,2833662606,3686784485,1867200383,2776544847]
private def pvm_w1_11_p1 : List ℤ := pzig
  [2583304669,1866897939,2087569957,4894328288,7653014923,2151094337,7657642575,1955323821,
   2423524980,1869812586,1515047380,803305459,4855975382,4585351515,9659667486,12665259559,
   14980352288,24759219253,12896125758,21156732017,12869770666,15377842603,10246585024,
   9550737161,4160068882,6378306550,9443454627,13024351572,14581617215,12061122008,2373153834,
   662698739,4563754194,20932795753,6034194334,7064219979,7404393785,3350994220,17623980333,
   3493844196,4295332365,5657397143,12730558462,7795260463,10807898984,12861910244,9869839099,
   13076052092,1905601717,12056101477,11305116576,15241248085,11074740073,16064662916,8532120553,
   3549433232,20637049424,13045729245,4481809459,11078917978,12560632701,760569456,14730674004,
   7307489765,997304729,9415070774,2592916863,3711102398,3841453810,7923897223,6120633146,
   6520959266,13040860741,1301953376,11400344590,9783594869,890724401,17275045654,5786943063,
   11444201275,14290556228,3688011648,14500397369,8852291572,15580337354,9408601749,2095395801,
   16030725674,4920350479,15878829635,8589742520,8215770378,14921409585,4392686579,13224836224,
   5221635025,15723722871,8469020688,15403086352,6012636589,6177067041,10075926490,643519864,
   14174423403,1009558382,15611845728,473975703,12478134967,2792832890,11302335616,3582342021,
   7656683359,6155181084,7232271390,8042787863,3506994199,14671131138,14314215218,6219835997,
   5572504413,10996687964,10362903532,11930304451,15487252899,6909194680,16439046078,617853437,
   14957043403]
private def pvm_w1_11_p2 : List ℤ := pzig
  [633487741,14855166842,5411522008,11664391115,8026168519,11723630852,13358579430,4924199053,
   15169387067,5496233431,6810174484,871818780,9416276791,3202379949,10435608568,9298491098,
   11486327417,24151665823,6608130037,21206384760,26750310244,2729189418,22746093277,17801086179,
   9087813542,24428315600,11414822534,15494147125,24612882009,6003117553,16426883654,18404311634,
   1265207413,21730733181,19642112713,2542893090,21231941790,20161843604,1632891430,16396170017,
   15767296233,992222024,15895927962,15977053298,869291792,16748860035,19935353569,5684828471,
   13339315650,22657133644,14047532834,9047580481,30474053459,34933749055,19774126755,7492017924,
   33202614294,42439373028,29915318662,2972720010,26585507377,47170474469,49618718805,
   33384985061,6778873053,20692365262,41238604590,48087501574,39354087834,19591457590,5608405337,
   32048417415,54578760993,68862957573,74808294745,73956813447,66199080899,51887984769,
   32766154855,8051579087,27002746148,78518141894,154906605842,271466134336,451689421884,
   726459967676,1137686836178,1744469389106,2625675499590,3880971921228,5635511373992,
   8045498929260,11298932490924,15613082119874,21232963368842,28428369168184,37484239732694,
   48685353271988,62299908607424,78561851935036,97648509058502,119654618689572,144568464210548,
   172253268104618,202432687229940,234680627945196,268419743592188,302932444596892,
   337383478305512,370850827519624,402363792408008,430948651386184,455679793240328,
   475730765337118,490419693317162,499246394208310,501920222616410,498376791848598,
   488780774299308,473513515917406,453147295704564,428409957579720,400143292800872,
   369257492237982,336684009152714,303330185600720,270039488953680,237560223477604]
private def pvm_w1_11_p3 : List ℤ := pzig
  [206523717643822,177431543506098,150650924757868,126417671986496,104845929089326,
   85943434161152,69630294298774,55759021934244,44133970123326,34529043106888,26703196717114,
   20413540054718,15425879831710,11522543823756,8507446447282,6208613604890,4478641318730,
   3193698239862,2251654958114,1569781761984,1082288172554,737850614576,497211387028,
   330916029726,217256092390,140476483590,89283768694,55660076824,33957509636,20228360144,
   11739585392,6623464672,3625580002,1921766628,984670998,486956364,232187078,106728858,47379450,
   20423368,8651950,3681980,1625260,768290,393774,215130,121184,68270,37698,20182,10420,5178,
   2472,1132,490,194,66,16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_11_p4 : List ℤ := pzig
  [0]
private def pvm_w1_11 : List ℤ :=
  pvm_w1_11_p0 ++ (pvm_w1_11_p1 ++ (pvm_w1_11_p2 ++ (pvm_w1_11_p3 ++ pvm_w1_11_p4)))
private def pvm_w1_12_p0 : List ℤ := pzig
  [2881737759,1036494526,2467091023,523710818,2869771076,1324079081,965470615,952776170,
   1456547835,974397820,925608464,846043433,1557174762,3809032505,430898210,4953859218,
   2170488467,2383236413,114726188,2655510566,1738703499,3879728,1434098584,589640181,1674391889,
   2287734216,2145792795,69534565,1868994480,1141023008,289443254,4695836799,1298177937,
   5331181498,981408988,1570783635,1690560733,329600013,2626996240,2964904551,379101392,
   262226678,4244949078,2128651995,3806367659,2856497756,460300841,262291730,2767800635,
   2712214160,2992885518,222451917,4396071383,2352928435,3716125946,2168724730,2434451949,
   383541442,2076973706,3975392561,1710346170,3541560454,2583033579,3512115155,22318569,
   1137421746,1607656988,1026926766,3935339434,820095237,1932021091,1983284721,4225034367,
   1577231999,1602322888,1432280867,5404851414,4091152080,235624198,219654597,1277709089,
   2104677295,2120442064,2822379788,388705228,3967025349,4063816071,3070721165,4296722479,
   2949723293,5324245955,2549889361,1537743655,1004969498,3148986998,4383182436,9254984840,
   8774759800,10679838064,11435058542,12020282538,11404761010,8161662492,7191768552,2772696832,
   7589551726,4724922864,6215623986,3318053046,121921216,5931840600,10464249314,17117015986,
   15310701088,15861399950,8415512182,4008502164,6257075327,7023073579,9325224579,5781669897,
   2107499198,3348398536,8271749478,1923668339,2937786036,5853160723,1454354240]
private def pvm_w1_12_p1 : List ℤ := pzig
  [5866091634,2746699040,5439886758,757069700,5278081664,7769978625,6467070204,17787242155,
   15868061180,17092596891,20346782134,21845599365,9348079664,15948468717,5529090208,7230513935,
   2127506224,5623161538,10361847567,14591994494,11668541451,12000050034,361580664,6426983375,
   6426801532,16301784969,5871542288,7418826607,6816450993,5354299138,14429086499,10297595876,
   2502151322,7437597483,6109502844,10398024349,9087338250,10021676756,8498129703,10143454544,
   8226418381,9790006927,11436793222,15139419109,6409461739,6062241440,19752350073,183840444,
   4079982906,18782701413,10342002736,11517291758,11284436079,14123558332,10791919110,
   10604884659,10533626872,4250263994,18015142457,1370079403,197124953,9201942839,8695627780,
   8620615746,2681904147,4207397636,2846081875,7271207051,9878929552,1444317492,12030178893,
   9314543898,10599613568,11450714443,2787417754,14881253894,8546233853,5302208009,16292744878,
   2429817457,16019561613,8924583926,9354331554,12744363375,1120410796,16338797166,5569984095,
   10631053081,12103955546,5400785060,13742874419,3321527712,18219334252,2260622637,9193497247,
   11122927310,7540354408,13922956651,5355398317,13143870170,239806352,14189898383,934620521,
   7603454094,7488366991,7073120591,11896896552,12171369212,9481971005,8640605709,7070024232,
   6190076808,8135193183,2190839199,9796758586,1507132554,9945497619,128248137,13994643118,
   1458810868,14331756131,4281123233,14190096094,8895359836,9128046343,2502980133,17473927190,
   15376523652]
private def pvm_w1_12_p2 : List ℤ := pzig
  [7241737551,15209435141,3253135902,13421878624,518300835,12635869025,2854418167,13487688814,
   8131113084,9705888911,10210494729,5537421650,13674449982,2701909858,9188702859,2853417217,
   7069488626,764875444,13753099257,13931330093,6479409058,21485013914,7039503602,20422098159,
   27338452977,4413532127,23341045296,23177787568,2956593255,21431746323,12056405869,12570915676,
   23813284432,7738530802,16532433371,21024091507,3197970951,16481507700,17274330896,2477195571,
   21451887855,19315729379,253894170,18066725036,18878448388,2585882296,14231599449,14567839965,
   258314624,15217836584,17305305240,3739711808,14901255171,21708610233,10420052333,9530308362,
   23611926324,21196745718,1287693874,23867623775,37187407713,30595578667,7672599529,20818336848,
   40278010194,39725630922,19992548890,8828863125,35278828485,49352093497,44962061335,
   24593256675,2502034400,27401212804,43655708138,46306073932,34592102930,13349501938,
   11519704051,36168410887,56821359595,69689208931,74170384077,72341514113,65126014611,
   52140837275,34010505467,10810348605,21413579506,70365104990,146026921080,263463223378,
   447426552728,733852611332,1170739417936,1823084437710,2779518818512,4155783499990,
   6096377237966,8778273405532,12414876800184,17255133205494,23577428005988,31681671692752,
   41879451164676,54478306950446,69759122794380,87950525396382,109203623974824,133566634311570,
   160959094449794,191149493295362,223741752066858,258172849686704,293720764876958,
   329522620126760,364604824969314,397925807840354,428428116381962,455094403319098,
   477002827407582,493379143395424,503642526044756,507440720373290,504670153248342,
   495479076581756,480254767950680,459597200930582]
private def pvm_w1_12_p3 : List ℤ := pzig
  [434281454866546,405211078643966,373365620366772,339746858059432,305328556304598,
   271013415326442,237599116146094,205754092080640,176003184354638,148723147756140,
   124147451024082,102378906370448,83407827422098,67133137846606,53384214680800,41941931290952,
   32557961420136,24971727560026,18924503016372,14170301164744,10483427888054,7662905804664,
   5534279630270,3949471000832,2785339931568,1941480908034,1337618741126,910838243774,
   612805425804,407103477536,266787950194,172242019960,109378627610,68197298652,41669272184,
   24902353870,14528512348,8259971530,4568639218,2454625726,1279359880,646154110,316014508,
   149647924,68685330,30643136,13367708,5762526,2494906,1107478,513706,251034,128254,67234,35414,
   18442,9384,4632,2210,1006,432,170,58,16,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_12_p4 : List ℤ := pzig
  [0]
private def pvm_w1_12 : List ℤ :=
  pvm_w1_12_p0 ++ (pvm_w1_12_p1 ++ (pvm_w1_12_p2 ++ (pvm_w1_12_p3 ++ pvm_w1_12_p4)))
private def pvm_w1_13_p0 : List ℤ := pzig
  [3339114629,759836158,632169805,2992795613,655046048,2629899556,973496665,161542374,631210886,
   2331585381,1699659042,882472431,933261585,4314788544,1569470967,3176511835,703928969,
   4162859064,342239640,2300156737,605005319,2171835118,2458746147,920953472,1432526418,
   1396884725,631072622,16188067,101604998,380438144,3545172677,833985892,5062478738,568486397,
   1575966001,4921608601,2598671446,1907787354,1122795096,1039865587,2437747613,4484110402,
   2217416909,2236947359,838437745,3174078686,1610887760,1774977733,1098613113,890634150,
   1524589774,1595053945,3485668261,92773996,6955993730,434391021,4143005043,927642310,272230143,
   2437245287,2574266114,1800324036,389198139,3453336501,1212385872,2924006886,487909259,
   636602353,268136950,4136535815,881058688,264751215,194937136,4365707692,2460255080,1309601455,
   354187320,1935325695,3676764163,3006989515,1270891305,1137601422,1908807756,5766781210,
   1562419570,1024730239,2022730665,441133853,3080946524,1276205340,1329935674,2066088759,
   2211055399,1707839599,3994762937,3663571985,5573482325,2177083741,5493924265,1048965985,
   913477059,1464826550,6074986752,4367383138,9026264862,8842709768,12925906478,11385333220,
   13130368186,6576722424,6629724394,5831108580,8672438610,8492409202,1132141316,4049679992,
   2291341949,7209760324,5183592442,15710249854,16709495798,14173814968,17876271614,3579681694,
   4060209852,12504894615,932432870,21276346365]
private def pvm_w1_13_p1 : List ℤ := pzig
  [16845972244,14887688827,23395297370,17151606199,13977960230,12026776509,7414855236,795834525,
   1564087888,9091655270,3195301821,16855900668,14776886527,5357286812,3842305449,6295354325,
   12051589656,11618234499,7512718676,7005961153,8813516221,4634900652,13044829711,7953186878,
   2904669005,7295102515,10684221846,8189876799,7435176538,7570462722,8853428499,7478932260,
   7613255625,3625234401,7825430164,19221878163,2555271109,6015087008,11882740143,10793533134,
   39102172,17533305991,11669146836,1450416288,6539972111,17796605804,3882317803,10008510133,
   15011862594,7252645541,13428323073,10220387734,7897863949,14160315371,4856245656,9658542017,
   13216159805,6456982038,1063218601,3857513073,9352820304,2598226652,2992974506,12937715284,
   528955393,5000325405,3634138266,12245971939,13928143343,13193334912,6910258086,11861848097,
   7089954084,11787172498,12343229597,3317447445,14003849568,6261804749,10700909281,14414095792,
   6682137774,13740731981,4257298436,15536553240,6451713371,6093330675,13774120160,1218702404,
   15215586339,3666440964,12530925522,7967625281,7302227275,14421895362,5919643548,12898990405,
   1323765165,13222271558,3062326251,8899987861,9533973108,14439237450,5725126547,5878816051,
   8781691728,4109758708,9961508073,1580192821,11407983990,2489807331,15898672969,4144282591,
   10368588622,1940906790,6761140955,4345877142,8562284726,4693651897,10061950367,5356617942,
   12396553610,5043357389,13133982041,3539841710,15552152836,1470316534,14359964107,2759828867]
private def pvm_w1_13_p2 : List ℤ := pzig
  [13364640220,4385278116,12753596013,7638423739,14488764930,18438397320,537334969,8972170477,
   3409852566,12516862666,1716495054,12750389101,6215825645,10520481222,10173036018,4570498835,
   10657010549,398744200,10978064438,3538973960,8178203967,2625277411,12101188138,12233857070,
   7616960413,24183319185,12546605965,15557135044,24426583312,2916044238,24106820339,25947521653,
   250056501,22235876282,15879601070,7963505265,19817576233,6929526335,15918655588,22217550814,
   4286051226,16686902521,18017603995,423136239,17086035760,16194286464,3109817549,20708099309,
   18767489707,893265645,15545143210,16716563022,2293954614,13368758701,14225810509,82873416,
   15453671836,18635693618,6429387542,12726853343,23075257493,14964758815,5429712954,22990905298,
   25791443792,10509989212,15290662799,35540128513,37158448855,19536113167,8033202994,
   32835321028,42723408534,32040175672,6336467790,22148226465,42669842517,48479773901,
   37185376245,13185632343,13684365278,34626168754,45048010848,42708074104,27767790174,
   4682591340,20079326189,42340392665,60073684327,71044059545,73908160451,70208291619,
   62335847609,50515579417,33585831231,10632189489,21109769522,69519952324,147838285296,
   274363988818,475982200846,793752994282,1286353037556,2032467083248,3136016526162,
   4733366503588,6997986384344,10141456846074,14413553954172,20101657663268,27525503815234,
   37024550758342,48939775837090,63592486554872,81259567268320,102143696835178,126340621674040,
   153808694493648,184344723871640,217567348284896,252909027092470,289619847732664,
   326786605590750,363367550077118,398239738866244,430255047023350,458301769765896,
   481368674320418]
private def pvm_w1_13_p3 : List ℤ := pzig
  [498606558694090,509380929764634,513310288557854,510287185865694,500481591537492,
   484327090114090,462490780669172,435828835823896,405331575329832,372063481966486,
   337103763767648,301491923508100,266181301741118,232002529185204,199638269640806,
   169610024421264,142276734833912,117843643581356,96378884714480,77834948999444,62072479910118,
   48884444024032,38019237468676,29201611416050,22150519219852,16593260088764,12275681212556,
   8968634644958,6471239225676,4611678422354,3246263959760,2257375146314,1550728941534,
   1052306384272,705176535878,466407905114,304217557532,195464682142,123545852160,76700329160,
   46694432770,27829799128,16211627648,9216089494,5105699834,2752981370,1443183840,734925848,
   363364370,174421072,81341868,36922272,16371428,7134684,3084818,1340080,593204,270678,127844,
   62170,30750,15250,7484,3592,1670,744,312,118,38,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w1_13_p4 : List ℤ := pzig
  [0]
private def pvm_w1_13 : List ℤ :=
  pvm_w1_13_p0 ++ (pvm_w1_13_p1 ++ (pvm_w1_13_p2 ++ (pvm_w1_13_p3 ++ pvm_w1_13_p4)))
private theorem dk_w1_0 : muxFastIterBSlideChk 6 513 phbv_w1
    rkmViHi_m512_r512_s2_c0 pvm_w1_1 = true := by
  decide +kernel
private theorem dk_w1_1 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_1 pvm_w1_2 = true := by
  decide +kernel
private theorem dk_w1_2 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_2 pvm_w1_3 = true := by
  decide +kernel
private theorem dk_w1_3 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_3 pvm_w1_4 = true := by
  decide +kernel
private theorem dk_w1_4 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_4 pvm_w1_5 = true := by
  decide +kernel
private theorem dk_w1_5 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_5 pvm_w1_6 = true := by
  decide +kernel
private theorem dk_w1_6 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_6 pvm_w1_7 = true := by
  decide +kernel
private theorem dk_w1_7 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_7 pvm_w1_8 = true := by
  decide +kernel
private theorem dk_w1_8 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_8 pvm_w1_9 = true := by
  decide +kernel
private theorem dk_w1_9 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_9 pvm_w1_10 = true := by
  decide +kernel
private theorem dk_w1_10 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_10 pvm_w1_11 = true := by
  decide +kernel
private theorem dk_w1_11 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_11 pvm_w1_12 = true := by
  decide +kernel
private theorem dk_w1_12 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_12 pvm_w1_13 = true := by
  decide +kernel
private theorem dk_w1_13 : muxFastIterBSlideChk 6 513 phbv_w1
    pvm_w1_13 rkmVoHi_m512_r512_s2_c0 = true := by
  decide +kernel
private theorem ptail_ok : rkmAllTrueF [
    muxIntListEq rkmHbHi_m512_r512_s1_c1 phbv_w0,
    muxIntListEq rkmHbHi_m512_r512_s2_c0 phbv_w1
  ] = true := by
  decide +kernel
private theorem pw_w0_1 : muxFastIterFullT16 12 513
    phbv_w0 rkmViHi_m512_r512_s1_c1 = rkmVoHi_m512_r512_s1_c1 :=
  (muxFastIterFullT16_add 6 6 513 phbv_w0 rkmViHi_m512_r512_s1_c1).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) (muxFastIterBSlideChk_sound dk_w0_0)).trans
      (muxFastIterBSlideChk_sound dk_w0_1))
/-- Certified `T_16` walk chunk `m512_r512_s1_c1`. -/
theorem rkmWalkChkHi_m512_r512_s1_c1 : muxFastIterFullT16 12 513
    rkmHbHi_m512_r512_s1_c1 rkmViHi_m512_r512_s1_c1 = rkmVoHi_m512_r512_s1_c1 :=
  (congrArg (fun h ↦ muxFastIterFullT16 12 513 h rkmViHi_m512_r512_s1_c1)
    (muxIntListEq_eq_true.mp (rkmHd ptail_ok))).trans pw_w0_1
private theorem pw_w1_1 : muxFastIterFullT16 12 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_2 :=
  (muxFastIterFullT16_add 6 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) (muxFastIterBSlideChk_sound dk_w1_0)).trans
      (muxFastIterBSlideChk_sound dk_w1_1))
private theorem pw_w1_2 : muxFastIterFullT16 18 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_3 :=
  (muxFastIterFullT16_add 12 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_1).trans
      (muxFastIterBSlideChk_sound dk_w1_2))
private theorem pw_w1_3 : muxFastIterFullT16 24 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_4 :=
  (muxFastIterFullT16_add 18 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_2).trans
      (muxFastIterBSlideChk_sound dk_w1_3))
private theorem pw_w1_4 : muxFastIterFullT16 30 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_5 :=
  (muxFastIterFullT16_add 24 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_3).trans
      (muxFastIterBSlideChk_sound dk_w1_4))
private theorem pw_w1_5 : muxFastIterFullT16 36 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_6 :=
  (muxFastIterFullT16_add 30 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_4).trans
      (muxFastIterBSlideChk_sound dk_w1_5))
private theorem pw_w1_6 : muxFastIterFullT16 42 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_7 :=
  (muxFastIterFullT16_add 36 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_5).trans
      (muxFastIterBSlideChk_sound dk_w1_6))
private theorem pw_w1_7 : muxFastIterFullT16 48 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_8 :=
  (muxFastIterFullT16_add 42 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_6).trans
      (muxFastIterBSlideChk_sound dk_w1_7))
private theorem pw_w1_8 : muxFastIterFullT16 54 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_9 :=
  (muxFastIterFullT16_add 48 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_7).trans
      (muxFastIterBSlideChk_sound dk_w1_8))
private theorem pw_w1_9 : muxFastIterFullT16 60 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_10 :=
  (muxFastIterFullT16_add 54 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_8).trans
      (muxFastIterBSlideChk_sound dk_w1_9))
private theorem pw_w1_10 : muxFastIterFullT16 66 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_11 :=
  (muxFastIterFullT16_add 60 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_9).trans
      (muxFastIterBSlideChk_sound dk_w1_10))
private theorem pw_w1_11 : muxFastIterFullT16 72 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_12 :=
  (muxFastIterFullT16_add 66 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_10).trans
      (muxFastIterBSlideChk_sound dk_w1_11))
private theorem pw_w1_12 : muxFastIterFullT16 78 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = pvm_w1_13 :=
  (muxFastIterFullT16_add 72 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_11).trans
      (muxFastIterBSlideChk_sound dk_w1_12))
private theorem pw_w1_13 : muxFastIterFullT16 84 513
    phbv_w1 rkmViHi_m512_r512_s2_c0 = rkmVoHi_m512_r512_s2_c0 :=
  (muxFastIterFullT16_add 78 6 513 phbv_w1 rkmViHi_m512_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w1) pw_w1_12).trans
      (muxFastIterBSlideChk_sound dk_w1_13))
/-- Certified `T_16` walk chunk `m512_r512_s2_c0`. -/
theorem rkmWalkChkHi_m512_r512_s2_c0 : muxFastIterFullT16 84 513
    rkmHbHi_m512_r512_s2_c0 rkmViHi_m512_r512_s2_c0 = rkmVoHi_m512_r512_s2_c0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 84 513 h rkmViHi_m512_r512_s2_c0)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl ptail_ok)))).trans pw_w1_13
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi512T6`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi512T6 :
    rkmWalkChkHi_m512_r512_s1_c1 = rkmWalkChkHi_m512_r512_s1_c1 :=
  rfl
private theorem laneRoot_Hi512T6 : rkmZigHi512T6 = rkmZigHi512T6 :=
  (And.intro (Eq.refl rkmZigHi512T5) rfl).right

end
end QuantumComputation.Specs.DickeSol
