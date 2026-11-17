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
# High-`m` Checkpointed Walk Part `8` (`FindAllJohnsonRampKickMuxHi512T8`)

Certifies `1` `T_16` checkpoint walk(s) (`43605` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Zigzag `< 2 ^ 60` `ℕ → ℤ` list decoder (`FindAllJohnsonRampKickMuxHi512T8`). -/
def rkmZigHi512T8 : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: rkmZigHi512T8 ws
/-- Quantized generator list for `m512_r512_s3_c1`. -/
def rkmHbHi_m512_r512_s3_c1 : List ℤ := altBuildHbFrom 1024 512 51812710743 0 512
/-- Input orbital vector for `m512_r512_s3_c1`. -/
def rkmViHi_m512_r512_s3_c1 : List ℤ := rkmZigHi512T8
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
/-- Output orbital vector for `m512_r512_s3_c1`. -/
def rkmVoHi_m512_r512_s3_c1 : List ℤ := rkmZigHi512T8
  [3365158519,1188540413,3678369584,3344795848,1246929103,5218158271,756221289,2811707417,
   1071936902,2849437839,2103596312,215078057,492549897,900844627,2402954849,1208248096,1430342012,
   1087075237,1539189811,540748040,861922007,906517485,2365259794,3208799187,410580122,1963488968,
   648215654,2549099021,738144552,1479016723,1107899564,3277580112,5801029713,1013988674,952051060,
   1431292022,679207145,1364454319,4272409297,6695536522,5020610030,3939404825,2063494954,
   2615135327,8385833212,8354050957,2984327426,3808913959,50145858,1105160529,9935605176,
   10059770805,7189210472,509481907,1644095599,1356831509,2082179860,1784802361,1416525598,
   832118008,917855157,1278350492,2475220045,122925252,406123185,2790644840,5004462557,3283574378,
   1771545135,1097112022,5835773226,2515728879,3672568225,988307078,2707261356,2879890065,
   2716904930,1007275518,772752480,5639056977,151010868,3177886740,3522761446,5658610659,942116736,
   6225087380,7534299023,2018292190,1032931584,6074071939,1195566629,4562947886,4221736507,
   3046234259,4219373190,851139119,755750479,1074187760,819628179,636985112,7867513455,1035329179,
   112839846,6690919716,3913621267,3601518649,4607491240,704539438,5734974897,6798201040,2421756128,
   323449210,3195155006,8070562321,1098385203,4361598776,130847577,7387250217,4799164141,6089019191,
   7535962726,15730145169,4214708688,5131299460,2432429899,6027471147,1620367460,1993515150,
   296238095,5279233357,4193949832,5137731635,5738307850,3314263819,2122776480,1860710234,
   3646090539,2685239900,3729896026,6534362631,2546752254,12481181488,9120808121,5413524021,
   1189545113,692929191,1651638812,564418741,229483191,1071646036,5601952515,1732834148,9476832879,
   4827544834,531323537,5815821929,8192295378,2109251421,1233980445,6399079593,1587761346,120634203,
   3406722681,113730461,6066372122,10857930429,3171406219,3200662787,10698389982,4843885065,
   2805879843,3854511123,4369202816,2282403879,4056382952,4099173902,444042571,4196502932,
   2542719026,1970701108,215869389,10943953917,5132041969,12603388029,12662893570,4839994153,
   15026758906,2730249103,2522875983,2368003390,8141241774,17863846571,10153128844,3499007329,
   2257413516,640910986,3086051406,4902179258,4335427681,2798298265,10754785893,7235071138,
   5426294491,7744459162,6087608897,14955899754,3744471067,1355454012,8552030517,344885177,
   2273699321,27218167,4398763043,4442716607,3871683959,960355447,14268899634,1421082465,
   15545319752,6999071528,75570624,5371836132,9817568827,3851380824,17660742909,10677590365,
   8661211559,79264115,1804924694,4561823991,9891545142,14061402627,28455336734,4115908319,
   16615067930,8697870286,13819690758,11617977204,5423421917,660746014,23441494383,13842239329,
   25430289739,15316458047,10636181983,8873876739,9995498930,3566074517,25386658972,13328701907,
   21682606458,19157190759,19438024880,34457422641,24739959904,20620272093,14275980272,4454504915,
   9345698478,5605754235,2128428447,3186992666,14721812709,27033013860,17671577041,14721442246,
   15054828807,1101936164,4528529298,20238480773,13554247532,6546432461,11138277880,2228962172,
   2413830833,603250758,310484388,79509909,5877155556,14317713678,16804330045,2816660928,4517320743,
   11052086027,1253276316,13332561023,6093041725,18414144773,11405299564,4590514889,20084794039,
   25731159188,19034497151,10685968992,11831340746,23805096141,26958918706,7519711073,9529523149,
   41360339074,41279073931,45612415006,12709380881,26413560570,31028602129,77723617384,94676103495,
   157224619602,198042450117,272899952946,309099571223,404123678166,476737595811,599895477530,
   736184195681,866799033008,1060047269531,1174208304544,1337876042491,1406942843958,1496366572521,
   1532924366632,1516072331467,1472908299248,1273084335419,1018706578928,718944718071,330643376436,
   94378847690,467467138945,805984950472,1078938576177,1221424662430,1241443312469,1069759507880,
   734651490019,331640770836,167127017424,623332249115,979795156534,1171537255687,1184151205212,
   958077018733,545986039298,30552406208,558569708375,946571897772,1123751025609,1115918025534,
   769943623005,298503910728,338970917530,814019835161,1142739134790,1097420318653,746554204414,
   182128954971,447881677569,914613026352,1118719348215,942354817612,472672552097,189223630127,
   767937871670,1050268851463,1021009565934,580451041671,101844984735,783588685300,1119494098409,
   971516220578,448557549351,256528681361,864811991034,1095785735919,848877284572,227522256991,
   519627184197,1047475352422,1063729976259,570426676372,218258139752,895255416479,1170316007554,
   813072158171,53903074831,802247197080,1126694598071,884022758114,123243178871,697978048685,
   1160614648600,940221367243,164373839766,723993062084,1208454189599,928093208452,62057531477,
   870179060693,1232925285834,777391406207,190601077467,988538531436,1165891923387,570812522636,
   457434038164,1183720172837,1072915561796,168113917491,873384345029,1277364627616,707220905863,
   430303005043,1162616281214,1060559646119,132023070760,936152500836,1282764854541,567466219458,
   668611032446,1332377740905,826611400238,348230069424,1230457366763,1033988888932,21589887878,
   1116425237881,1242869838032,194522788347,1096363533263,1319775009352,274605188039,1013540991783,
   1351763764458,350932379815,1007636790509,1360050853234,365731018071,1041962710251,1398983930762,
   284481768219,1152530956289,1412203606728,107734975801,1367928264101,1311963427680,227783502666,
   1505094588085,1092967900520,572293760162,1619850033675,796696376636,1033612886336,1649792443695,
   273530535560,1519976658528,1420456501373,474651044843,1816687524362,815805568103,1248264386427,
   1715875827282,65028220708,1831523589641,1156613527554,1169985358958,1908858039165,37801542085,
   1968855632366,1131470655275,1419512689023,1922307169766,451976760874,2177257731423,650595314306,
   1950853445960,1590423624487,1357459099735,2215210472626,567408881876,2489846650527,264050213632,
   2499643266290,890987118541,2070374274763,1529268549394,1285589879956,2628617097225,688771831457,
   4731242633760,2212069110778,6363962338813,8164441815857,128392740930,11618814549820,
   20280262708850,16363068738844,16260851851491,74367898486257,110499184256669,55379102542173,
   125963001948096,401956529577632,691239625087800,903471295837562,975104324686258,891757953326816,
   693244532149190,454134368320314,246196614073144,107081443871850,35256953155688,7612300913484]
end
public section
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem n0m (z : ℕ) : (0 : ℕ) = Nat.mul 0 z := by rw [Nat.mul_eq]; omega
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uCN (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uCN_eq (x : ℕ) (xs : List ℕ) : uCN x xs = x :: xs := by
  unfold uCN; rw [n1a]; cases xs <;> rfl
private def uToHb : List ℤ → Option (List ℕ)
  | [] => some [] | Int.negSucc _ :: _ => none
  | Int.ofNat n :: xs => match uToHb xs with | some ns => some (uCN n ns) | none => none
private def uOfHb : List ℕ → List ℤ
  | [] => [] | n :: ns => Int.ofNat n :: uOfHb ns
private theorem uToHb_s : ∀ (hb : List ℤ) (ns : List ℕ), uToHb hb = some ns → hb = uOfHb ns
  | [], _, h => by injection h with h'; subst h'; rfl
  | Int.negSucc _ :: _, _, h => by dsimp only [uToHb] at h; cases h
  | Int.ofNat n :: xs, _, h => by
    dsimp only [uToHb] at h; revert h; cases hxs : uToHb xs with
    | none => intro h; dsimp only at h; cases h
    | some ms =>
      intro h; dsimp only at h; injection h with h'; subst h'; rw [uCN_eq, uOfHb, uToHb_s xs ms hxs]
private def uCP (b bz : ℕ) (xs : List (ℕ × ℕ)) : List (ℕ × ℕ) := match Nat.add 1 b with
  | 0 => xs | b' + 1 => match Nat.add 1 bz with
    | 0 => xs | bz' + 1 => match xs with | [] => [(b', bz')] | h :: t => (b', bz') :: h :: t
private theorem uCP_eq (b bz : ℕ) (xs : List (ℕ × ℕ)) : uCP b bz xs = (b, bz) :: xs := by
  unfold uCP; rw [n1a b, n1a bz]; cases xs <;> rfl
private def mkP (z : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => [] | b :: bs => uCP b (Nat.mul b z) (mkP z bs)
private def hbP : List (ℕ × ℕ) → List ℤ
  | [] => [] | p :: ps => Int.ofNat p.1 :: hbP ps
private theorem mkP_hb (z : ℕ) : ∀ (bs : List ℕ), hbP (mkP z bs) = uOfHb bs
  | [] => rfl | b :: bs => by rw [mkP, uCP_eq b (Nat.mul b z), hbP, uOfHb, mkP_hb z bs]
private def pOk (z : ℕ) : List (ℕ × ℕ) → Prop
  | [] => True | p :: ps => p.2 = Nat.mul p.1 z ∧ pOk z ps
private theorem mkP_ok (z : ℕ) : ∀ (bs : List ℕ), pOk z (mkP z bs)
  | [] => trivial | b :: bs => by rw [mkP, uCP_eq b (Nat.mul b z)]; exact ⟨rfl, mkP_ok z bs⟩
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
  | Int.ofNat v => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t
private theorem bCZ_eq (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by cases x <;> cases xs <;> rfl
private theorem bOfF_eq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  simp [primOfNatForced, Nat.one_add]
private theorem bNsF_eq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  simp [primNegSuccForced, Nat.one_add]
private theorem bSub_eq (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat; rw [bOfF_eq, Nat.sub_eq]; cases h : z - u with
  | zero => dsimp only; rw [Nat.sub_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => [] | u :: us => bCZ (rkmForcedSubNatNat u z) (bDec z us)
private theorem bDec_nil (z : ℕ) : bDec z [] = [] := rfl
private theorem bDec_cons (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by rw [bDec, bCZ_eq, bSub_eq]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bM0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZ0]; rfl
private def bEnc1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k => match Nat.sub z (Nat.add k 1) with | 0 => none | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs => match bEnc1 z x with
    | none => none | some u => match bEnc z xs with | none => none | some us => some (uCN u us)
private theorem bEnc1_s (z : ℕ) (x : ℤ) (u : ℕ) (h : bEnc1 z x = some u) :
    ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bEnc1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w => intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem bEnc_s (z : ℕ) : ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us → bDec z us = xs
  | [], _, h => by injection h with h'; subst h'; rfl
  | x :: xs, _, h => by
    dsimp only [bEnc] at h; revert h; cases hx : bEnc1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u => dsimp only; cases hxs : bEnc z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uCN_eq, bDec_cons, bEnc1_s z x u hx, bEnc_s z xs ws hxs]
private def zTd (x : ℤ) (d : ℕ) : ℤ := match x with
  | Int.ofNat m => Int.ofNat (m / d) | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTdN_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTd x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => by dsimp only [muxRawIntTdivNat, zTd]; rw [bNeg_eq, ndiv, Nat.add_eq]
private theorem bSubNTd_eq (m n d : ℕ) : rkmUltraSubNatTdiv m n d = zTd ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    dsimp only; have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTd]; rw [bNeg_eq]
private theorem bSubTd_eq (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTd (a - b) d := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => exact bSubNTd_eq m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
      rw [hm]; rfl
  | negSucc m => cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTd]
      rw [bNeg_eq, ndiv, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [bSubNTd_eq, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTd t d) (by simp only [Int.negSucc_eq]; omega)
private theorem bMul_eq : ∀ (a b : ℤ), muxRawIntMul a b = a * b
  | Int.ofNat _, Int.ofNat _ => by
    dsimp only [muxRawIntMul]; simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | Int.ofNat _, Int.negSucc _ => by
    dsimp only [muxRawIntMul]
    rw [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; push_cast; ring
  | Int.negSucc _, Int.ofNat _ => by
    dsimp only [muxRawIntMul]
    rw [bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | Int.negSucc _, Int.negSucc _ => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq, Nat.add_eq, Nat.add_eq, Int.ofNat_eq_natCast]
    simp only [Int.negSucc_eq]; push_cast; ring
private theorem bFAdd_eq : ∀ (a b : ℤ), rkmForcedIntAdd a b = a + b
  | Int.ofNat _, Int.ofNat _ => by
    dsimp only [rkmForcedIntAdd]; rw [bOfF_eq]; simp only [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | Int.ofNat _, Int.negSucc _ => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
  | Int.negSucc _, Int.ofNat _ => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega
  | Int.negSucc _, Int.negSucc _ => by
    dsimp only [rkmForcedIntAdd]; rw [bNsF_eq, Nat.add_eq, Nat.add_eq, Int.negSucc_eq]; omega
private theorem bAC_eq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bFAdd_eq]; cases a + b <;> cases xs <;> rfl
private def bSV (v P Q d : ℕ) : ℕ := fN P fun p => fN Q fun q => match Nat.sub q p with
  | 0 => Nat.add v (Nat.div (Nat.sub p q) d) | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bSV_eq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSubNTd_eq]; unfold bSV at hv ⊢; dsimp only [fN] at hv ⊢
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq] at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv; cases h : Q - P with
  | zero => intro _; dsimp only; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k => intro hv; dsimp only at hv ⊢; rw [bNeg_eq]; omega
private abbrev bCV2 (d b0 bz0 c0 b bz v c1 : ℕ) : ℕ :=
  bSV v (Nat.add (Nat.mul b0 c0) bz) (Nat.add (Nat.mul b c1) bz0) d
private theorem bC_hb2 (z d b0 bz0 c0 b bz v c1 : ℕ) {rest : List ℕ} {tZ : List ℤ}
    (h0 : bz0 = Nat.mul b0 z) (hb : bz = Nat.mul b z)
    (hv : 0 < bCV2 d b0 bz0 c0 b bz v c1) (ht : bDec z rest = tZ) :
    bDec z (uCN (bCV2 d b0 bz0 c0 b bz v c1) rest) = rkmUltraAddCons ((v : ℤ) - (z : ℤ))
      (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tZ := by
  subst h0; subst hb; rw [uCN_eq, bDec_cons, ht, bAC_eq, bSubTd_eq, bMul_eq, bMul_eq]
  refine congrArg (· :: tZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCV2 at hv ⊢; rw [bSV_eq z v _ _ d hv, hpq]
private theorem bC_nil2 (z d b0 bz0 c0 v : ℕ) {rest : List ℕ} {tZ : List ℤ}
    (h0 : bz0 = Nat.mul b0 z) (hv : 0 < bSV v (Nat.mul b0 c0) bz0 d) (ht : bDec z rest = tZ) :
    bDec z (uCN (bSV v (Nat.mul b0 c0) bz0 d) rest) = rkmUltraAddCons ((v : ℤ) - (z : ℤ))
      (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tZ := by
  subst h0; rw [uCN_eq, bDec_cons, ht, bAC_eq, bTdN_eq, bMul_eq]; refine congrArg (· :: tZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  rw [bSV_eq z v _ _ d hv, hpq]
private def bPos : List ℕ → Bool
  | [] => true | x :: xs => cond (Nat.ble x 0) false (bPos xs)
private theorem bPos_uCN {x : ℕ} {xs : List ℕ} (h : bPos (uCN x xs) = true) :
    0 < x ∧ bPos xs = true := by
  rw [uCN_eq] at h
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHd (z : ℕ) : List ℕ → ℕ
  | [] => z | x :: _ => x
private def bTl : List ℕ → List ℕ
  | [] => [] | _ :: xs => xs
private theorem bHd_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHd z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHd; rw [bDec_nil, bZ0] | _ :: _ => by unfold bHd; rw [bDec_cons]
private theorem bTl_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTl xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl | _ :: _ => by unfold bTl; rw [bDec_cons]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ) → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _, _ => []
  | rem + 1, b0, bz0, c0, bps, vs, cs => match bps with
    | [] => uCN (bSV (bHd z vs) (Nat.mul b0 c0) bz0 d) (bSl z d rem 0 0 z [] (bTl vs) (bTl cs))
    | (b, bz) :: bR => match vs, cs with
      | v :: vT, c :: cT => uCN (bCV2 d b0 bz0 c0 b bz v (bHd z cT)) (bSl z d rem b bz c bR vT cT)
      | v :: vT, [] => uCN (bCV2 d b0 bz0 c0 b bz v z) (bSl z d rem b bz z bR vT [])
      | [], c :: cT => uCN (bCV2 d b0 bz0 c0 b bz z (bHd z cT)) (bSl z d rem b bz c bR [] cT)
      | [], [] => uCN (bCV2 d b0 bz0 c0 b bz z z) (bSl z d rem b bz z bR [] [])
private theorem bSl_s (z d : ℕ) :
    ∀ (rem b0 bz0 c0 : ℕ) (bps : List (ℕ × ℕ)) (vs cs : List ℕ),
    bz0 = Nat.mul b0 z → pOk z bps → bPos (bSl z d rem b0 bz0 c0 bps vs cs) = true →
    bDec z (bSl z d rem b0 bz0 c0 bps vs cs) = rkmUltraSlideLoopAux d rem
      (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) (hbP bps) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | rem + 1, b0, bz0, c0, [], vs, cs, h0, _, h => by
    dsimp only [bSl, hbP, rkmUltraSlideLoopAux] at h ⊢; have hp := bPos_uCN h
    have hi := bSl_s z d rem 0 0 z [] (bTl vs) (bTl cs) (n0m z) trivial hp.2
    rw [bM0, hbP, bTl_eq z vs, bTl_eq z cs] at hi
    have hc := bC_nil2 z d b0 bz0 c0 (bHd z vs) h0 hp.1 hi; rw [bHd_eq z vs] at hc; exact hc
  | rem + 1, b0, bz0, c0, (b, bz) :: bR, vs, cs, h0, hk, h => by
    cases vs with
    | nil => cases cs with
      | nil =>
        dsimp only [bSl, hbP] at h ⊢; rw [bDec_nil]; dsimp only [rkmUltraSlideLoopAux]
        have hp := bPos_uCN h; have hi := bSl_s z d rem b bz z bR [] [] hk.1 hk.2 hp.2
        rw [bZ0 z, bDec_nil] at hi
        have hc := bC_hb2 z d b0 bz0 c0 b bz z z h0 hk.1 hp.1 hi; rw [bZ0 z] at hc; exact hc
      | cons c cT =>
        dsimp only [bSl, hbP] at h ⊢; rw [bDec_nil, bDec_cons z c cT]
        dsimp only [rkmUltraSlideLoopAux]; have hp := bPos_uCN h
        have hi := bSl_s z d rem b bz c bR [] cT hk.1 hk.2 hp.2; rw [bDec_nil] at hi
        have hc := bC_hb2 z d b0 bz0 c0 b bz z (bHd z cT) h0 hk.1 hp.1 hi
        rw [bHd_eq z cT, bZ0 z] at hc; exact hc
    | cons v vT => cases cs with
      | nil =>
        dsimp only [bSl, hbP] at h ⊢; rw [bDec_cons z v vT, bDec_nil]
        dsimp only [rkmUltraSlideLoopAux]; have hp := bPos_uCN h
        have hi := bSl_s z d rem b bz z bR vT [] hk.1 hk.2 hp.2; rw [bZ0 z, bDec_nil] at hi
        have hc := bC_hb2 z d b0 bz0 c0 b bz v z h0 hk.1 hp.1 hi; rw [bZ0 z] at hc; exact hc
      | cons c cT =>
        dsimp only [bSl, hbP] at h ⊢; rw [bDec_cons z v vT, bDec_cons z c cT]
        dsimp only [rkmUltraSlideLoopAux]; have hp := bPos_uCN h
        have hi := bSl_s z d rem b bz c bR vT cT hk.1 hk.2 hp.2
        have hc := bC_hb2 z d b0 bz0 c0 b bz v (bHd z cT) h0 hk.1 hp.1 hi
        rw [bHd_eq z cT] at hc; exact hc
private def bStg (z dg mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns cns : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSl z d nL 0 0 z bps vns cns) fun out => cond (bPos out) (some out) none
private theorem bStg_s (z dg mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns cns out : List ℕ)
    (hk : pOk z bps) (h : bStg z dg mL cL bps vns cns = some out) :
    bDec z out = rkmUltraHornerStage dg mL cL (hbP bps) (bDec z vns) (bDec z cns) := by
  unfold bStg at h; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq] at h; revert h
  cases hp : bPos (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 0 z bps vns cns) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bM0 z]
    exact bSl_s z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 0 z bps vns cns (n0m z) hk hp
private def bBnd (z dg mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns cns : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL =>
    match bStg z dg mL cL bps vns cns with | none => none | some out => k nL out
private theorem bBnd_s {z dg mL cL : ℕ} {bps : List (ℕ × ℕ)} {vns cns out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ} (hpok : pOk z bps)
    (h : bBnd z dg mL cL bps vns cns kB = some out)
    (hk : ∀ (mid : List ℕ), kB (rkmNextLen mL cL) mid = some out →
      bDec z out = kU (rkmNextLen mL cL) (bDec z mid)) :
    bDec z out = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (hbP bps) (bDec z vns) (bDec z cns)) (kU nL)) := by
  unfold bBnd at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; revert h
  cases hs : bStg z dg mL cL bps vns cns with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_s z dg mL cL bps vns cns mid hpok hs]
    exact hk mid h
private def bStep (z mL c : ℕ) (bps : List (ℕ × ℕ)) (vns : List ℕ) : Option (List ℕ) :=
  bBnd z 16 mL c bps vns vns fun l1 c1 => bBnd z 15 mL l1 bps vns c1 fun l2 c2 =>
  bBnd z 14 mL l2 bps vns c2 fun l3 c3 => bBnd z 13 mL l3 bps vns c3 fun l4 c4 =>
  bBnd z 12 mL l4 bps vns c4 fun l5 c5 => bBnd z 11 mL l5 bps vns c5 fun l6 c6 =>
  bBnd z 10 mL l6 bps vns c6 fun l7 c7 => bBnd z 9 mL l7 bps vns c7 fun l8 c8 =>
  bBnd z 8 mL l8 bps vns c8 fun l9 c9 => bBnd z 7 mL l9 bps vns c9 fun la ca =>
  bBnd z 6 mL la bps vns ca fun lb cb => bBnd z 5 mL lb bps vns cb fun lc cc =>
  bBnd z 4 mL lc bps vns cc fun ld cd => bBnd z 3 mL ld bps vns cd fun le ce =>
  bBnd z 2 mL le bps vns ce fun lf cf => bStg z 1 mL lf bps vns cf
private theorem bStep_s (z mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns out : List ℕ)
    (hk : pOk z bps) (h : bStep z mL cL bps vns = some out) :
    bDec z out = rkmUltraHornerT16Step mL cL (hbP bps) (bDec z vns) := by
  unfold bStep at h; unfold rkmUltraHornerT16Step
  refine bBnd_s hk h fun _ h => bBnd_s hk h fun _ h => bBnd_s hk h fun _ h => ?_
  refine bBnd_s hk h fun _ h => bBnd_s hk h fun _ h => bBnd_s hk h fun _ h => ?_
  refine bBnd_s hk h fun _ h => bBnd_s hk h fun _ h => bBnd_s hk h fun _ h => ?_
  refine bBnd_s hk h fun _ h => bBnd_s hk h fun _ h => bBnd_s hk h fun _ h => ?_
  refine bBnd_s hk h fun _ h => bBnd_s hk h fun _ h => bBnd_s hk h fun _ h => ?_
  exact bStg_s _ _ _ _ _ _ _ _ hk h
private def bIter (z : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ) → List ℕ → Option (List ℕ)
  | 0, _, _, _, vns => some vns
  | k + 1, mL, cL, bps, vns => match bStep z mL cL bps vns with
    | none => none | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL bps vNext
private theorem bIter_s (z : ℕ) : ∀ (k mL cL : ℕ) (bps : List (ℕ × ℕ)) (vns out : List ℕ),
    pOk z bps → bIter z k mL cL bps vns = some out →
    bDec z out = muxUltraIterFullT16Rkm k mL cL (hbP bps) (bDec z vns)
  | 0, _, _, _, _, _, _, h => by injection h with h'; subst h'; rfl
  | k + 1, mL, cL, bps, vns, out, hk, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL cL bps vns with
    | none => intro h; dsimp only at h; cases h
    | some vNext =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bStep_s z mL cL bps vns vNext hk hs]
      exact bIter_s z k mL (rkmNextLen16 mL cL) bps vNext out hk h
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  let z := 100000000000000000
  match uToHb hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some bns => match bEnc z v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vns => fL (mkP z bns) fun bps => match bIter z k mL cL bps vns with
      | none => muxUltraIterFullT16Rkm k mL cL hb v | some out => bDec z out
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; dsimp only [fL]; cases hh : uToHb hb with
  | none => rfl
  | some bns => dsimp only; cases hv : bEnc 100000000000000000 v with
    | none => rfl
    | some vns =>
      dsimp only; rw [rkmb_forceList_eq]
      cases hi : bIter 100000000000000000 k mL cL (mkP 100000000000000000 bns) vns with
      | none => rfl
      | some out =>
        dsimp only; rw [bIter_s 100000000000000000 k mL cL (mkP 100000000000000000 bns)
          vns out (mkP_ok 100000000000000000 bns) hi, mkP_hb, ← uToHb_s hb bns hh,
          bEnc_s 100000000000000000 v vns hv]
private def bWalkChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    fN (altIntLen inF) fun len0 => muxIntListEq (fIter steps maxLen len0 hbF inF) outF
private theorem bWalkChk_sound {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : bWalkChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold bWalkChk at h; dsimp only [fL, fN] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, fIter_eq] at h
  have h2 : muxUltraIterFullT16HiChk steps 0 maxLen hb vecIn vecOut = true := by
    unfold muxUltraIterFullT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq]; exact h
  exact muxUltraIterFullT16HiChk_sound h2
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2) | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCat : List (List ℕ) → List ℤ
  | [] => [] | ws :: wss => pzig ws ++ pzigCat wss
private def phbv_g0 : List ℤ := pzigCat
  [
   [150065639907460,211913961602578,259159700264650,298812020099256,333590173990744,
    364890874702104,393545067109658,420094953691518,444917699097870,468288313033976,
    490414705423422,511458633910914,531548920195604,550790161577248,569268683933190,
    587056734505952,604215511943426,620797405163146,636847679903896,652405770985796,
    667506287479416,682179805141866,696453498727346,710351652057298,723896073572564,
    737106437949608,750000569264426,762594677493784,774903557430792,786940757074870,
    798718721039734,810248913370266,821541923274820,832607556594342,843454915294762,
    854092466847852,864528105031602,874769203414374,884822662572438,894694951916954,
    904392146865174,913919961975010,923283780567042,932488681279384,941539461935538,
    950440661050826,959196577257366,967811286889070,976288659935726,984632374547666,
    992845930249092,1000932659998160,1008895741214758,1016738205882176,1024462949816220,
    1032072741184306,1039570228347552,1046957947090666,1054238327297168,1061413699121192,
    1068486298701662,1075458273459710,1082331687015994,1089108523760832,1095790693106690,
    1102380033449712,1108878315864282,1115287247552382,1121608475067370,1127843587330008,
    1133994118452936,1140061550388274,1146047315411750,1151952798455570,1157779339301150,
    1163528234641906,1169200740025424,1174798071683536,1180321408258124,1185771892429874,
    1191150632456572,1196458703626998,1201697149636100,1206866983886518,1211969190721332,
    1217004726592354,1221974521168114,1226879478385278,1231720477447000,1236498373771482,
    1241213999893718,1245868166323254,1250461662360546,1254995256874360,1259469699042442,
    1263885719057590,1268244028801084,1272545322485284,1276790277267144,1280979553834204,
    1285113796964590,1289193636062400,1293219685669796,1297192545957036,1301112803191598,
    1304981030187476,1308797786735660,1312563620016784,1316279064996798,1319944644806542,
    1323560871106016,1327128244434068,1330647254544250,1334118380727468,1337542092122082,
    1340918848012038,1344249098113588,1347533282851142,1350771833622742,1353965173055636,
    1357113715252390,1360217866027984,1363278023138264,1366294576500166,1369267908404044,
    1372198393718452,1375086400087708,1377932288122562],
   [1380736411584228,1383499117562090,1386220746645324,1388901633088706,1391542104972834,
    1394142484358984,1396703087438840,1399224224679282,1401706200962446,1404149315721214,
    1406553863070360,1408920131933476,1411248406165868,1413538964673558,1415792081528566,
    1418008026080588,1420187063065210,1422329452708806,1424435450830212,1426505308939322,
    1428539274332704,1430537590186344,1432500495645630,1434428225912662,1436321012330996,
    1438179082467904,1440002660194234,1441791965761966,1443547215879532,1445268623784976,
    1446956399317040,1448610748984238,1450231876031972,1451819980507780,1453375259324770,
    1454897906323288,1456388112330882,1457846065220632,1459271949967884,1460665948705438,
    1462028240777246,1463359002790666,1464658408667322,1465926629692586,1467163834563778,
    1468370189437062,1469545857973128,1470691001381656,1471805778464646,1472890345658586,
    1473944857075562,1474969464543278,1475964317644056,1476929563752848,1477865348074256,
    1478771813678616,1479649101537168,1480497350556338,1481316697611140,1482107277577752,
    1482869223365260,1483602665946618,1484307734388820,1484984555882328,1485633255769770,
    1486253957573900,1486846783024904,1487411852086980,1487949282984304,1488459192226318,
    1488941694632416,1489396903356006,1489824929907982,1490225884179612,1490599874464870,
    1490947007482202,1491267388395762,1491561120836122,1491828306920466,1492069047272280,
    1492283441040562,1492471585918542,1492633578161940,1492769512606776,1492879482686706,
    1492963580449962,1493021896575822,1493054520390692,1493061539883770,1493043041722300,
    1492999111266446,1492929832583776,1492835288463376,1492715560429580,1492570728755352,
    1492400872475310,1492206069398400,1491986396120222,1491741928035044,1491472739347452,
    1491178903083706,1490860491102768,1490517574107008,1490150221652624,1489758502159740,
    1489342482922214,1488902230117162,1488437808814184,1487949282984304,1487436715508642,
    1486900168186800,1486339701744986,1485755375843858,1485147249086114,1484515379023822,
    1483859822165474,1483180633982814,1482477868917386,1481751580386858,1481001820791076,
    1480228641517888,1479432092948728,1478612224463956,1477769084447950,1476902720293990,
    1476013178408880,1475100504217354,1474164742166250],
   [1473205935728448,1472224127406592,1471219358736580,1470191670290820,1469141101681282,
    1468067691562308,1466971477633208,1465852496640636,1464710784380740,1463546375701090,
    1462359304502392,1461149603739974,1459917305425056,1458662440625800,1457385039468134,
    1456085131136354,1454762743873520,1453417904981608,1452050640821448,1450660976812446,
    1449248937432070,1447814546215118,1446357825752750,1444878797691298,1443377482730850,
    1441853900623600,1440308070171948,1438740009226398,1437149734683192,1435537262481714,
    1433902607601650,1432245784059916,1430566804907318,1428865682224988,1427142427120542,
    1425397049724004,1423629559183466,1421839963660476,1420028270325174,1418194485351156,
    1416338613910060,1414460660165880,1412560627268996,1410638517349922,1408694331512764,
    1406728069828378,1404739731327230,1402729313991952,1400696814749592,1398642229463538,
    1396565552925118,1394466778844892,1392345899843578,1390202907442668,1388037792054662,
    1385850542972980,1383641148361482,1381409595243636,1379155869491296,1376879955813096,
    1374581837742444,1372261497625118,1369918916606436,1367554074618014,1365166950364072,
    1362757521307312,1360325763654328,1357871652340550,1355395161014712,1352896262022822,
    1350374926391632,1347831123811592,1345264822619262,1342675989779188,1340064590865214,
    1337430590041216,1334773950041252,1332094632149090,1329392596177118,1326667800444618,
    1323920201755360,1321149755374534,1318356415004966,1315540132762618,1312700859151348,
    1309838543036896,1306953131620086,1304044570409214,1301112803191598,1298157772004260,
    1295179417103714,1292177676934842,1289152488098816,1286103785320030,1283031501412036,
    1279935567242424,1276815911696618,1273672461640562,1270505141882256,1267313875132086,
    1264098581961930,1260859180762980,1257595587702250,1254307716677714,1250995479272024,
    1247658784704768,1244297539783212,1240911648851450,1237501013737958,1234065533701418,
    1230605105374820,1227119622707734,1223608976906688,1220073056373600,1216511746642182,
    1212924930312208,1209312486981628,1205674293176360,1202010222277762,1198320144447598,
    1194603926550480,1190861432073620,1187092521043842,1183297049941668,1179474871612450,
    1175625835174332,1171749785922980,1167846565232900],
   [1163916010455228,1159957954811824,1155972227285494,1151958652506226,1147917050633200,
    1143847237232424,1139749023149794,1135622214379356,1131466611926578,1127282011666376,
    1123068204195672,1118824974680216,1114552102695400,1110249362060804,1105916520668134,
    1101553340302266,1097159576455034,1092734978131442,1088279287647864,1083792240421902,
    1079273564753412,1074722981596308,1070140204320610,1065524938464276,1060876881474264,
    1056195722436240,1051481141792342,1046732811046340,1041950392455528,1037133538708568,
    1032281892588566,1027395086620492,1022472742702080,1017514471717264,1012519873131112,
    1007488534565198,1002420031352224,997313926068672,992169768044128,986987092845880,
    981765421737212,976504261107786,971203101874314,965861418849614,960478670078018,
    955054296134890,949587719387878,944078343217338,938525551193120,932928706204722,
    927287149541530,921600199919654,915867152451466,910087277553728,904259819789766,
    898383996640758,892458997200782,886483980789788,880458075478068,874380376515276,
    868249944656340,862065804375888,855826941961978,849532303479062,843180792589032,
    836771268218110,830302542056052,823773375872716,817182478635454,810528503408964,
    803810044017224,797025631444840,790173729952514,783252732878420,776260958093894,
    769196643078058,762057939571586,754842907764878,747549509970114,740175603720112,
    732718934229234,725177126142858,717547674491574,709827934754510,702015111922136,
    694106248432704,686098210837304,677987675025878,669771109819866,661444758705246,
    653004619441838,644446421239214,635765599134664,626957265142478,618016175663014,
    608936694541504,599712751045358,590337791878842,580804726167576,571105862111812,
    561232833712988,551176515603820,540926923533040,530473097436842,519802963222210,
    508903168325226,497758884694482,486353570948738,474668682868172,462683317803242,
    450373773575784,437712995315088,424669873336134,411208339892604,397286189564758,
    382853512327838,367850571514214,352204865555650,335826953493088,318604342084244,
    300392205867594,280998669148302,260160159639706,237497168120788,212427160187900,
    183969418495402,150211544998998,106216006474150]]
private def pvm_c0_1 : List ℤ := pzigCat
  [
   [587148456,1352537802,333629253,171081271,357500211,1495437196,835750885,609340305,70683234,
    2375081478,577900003,198251737,1610798703,1802808360,1848719327,898382917,1509335173,
    1169196848,2742177267,2784774445,1258100390,849249503,1706103032,3201586715,1390526902,
    528493005,289039177,637675498,525281871,1706044242,3536429651,2713924503,7413683807,
    1446415123,4576666441,1762043720,2149292893,1709684194,271730451,1338644546,4075351952,
    3812934699,154094461,1801115262,2064198237,281653163,3267544982,878785489,997883999,
    1603854631,6002190931,151465399,1645440140,5098886687,1750635683,3063923732,2865251801,
    1696524791,417849672,3004572569,387283439,312842487,1461278793,2644320651,1571716403,
    630082601,2595414834,1221617369,3590262985,290678894,7450400532,115433764,3006967910,
    3548294793,1079878618,513317687,1596168067,1918849577,523193847,245818661,2520627713,
    2560498055,2156852546,4466640380,6621801424,2751796764,1068642401,5540534015,958616431,
    1793822912,7275450755,948535886,840849237,795911152,7241951670,14441318,486243953,5091482505,
    4922808097,601624310,995013655,6186431828,4157701038,6027327089,306259016,1043898077,
    2930523571,4389820340,12594874560,2791102494,2958040930,4836975103,6370187115,8851383743,
    12471132151,3014558015,661932373,4112561952,7076990358,9916310954,9921629796,4498136056,
    17261340240,8114880956,17120609277,1194836571,11624572981,15086477605],
   [18849397401,14039321695,11065791659,7514990781,916598618,652760362,2669817674,2573784796,
    13194398924,18440383294,14224390936,6776908429,1472516465,11009909949,10066106521,10733200803,
    1512747811,6118098731,16526031836,2904605306,10575372968,35395117,1501810524,6942635765,
    7905113363,7279586669,3180020738,6282651251,10825860520,6647602540,4929652555,2337427784,
    5842163048,7162209479,2846400270,3295930344,9096882831,656876992,810726188,1147506967,
    14834905665,9275767543,7144706951,7241868563,5896225293,2330755676,317165841,4210930745,
    253989733,7351114526,2091106606,409899916,6602451232,11772791442,13799496202,184869333,
    3866068224,1558529946,3607369148,5557175266,12241660010,11669501834,12114479482,5096216404,
    9369679236,4835602564,1962731456,13785510300,6136787073,3032586988,9985759510,12795924709,
    11880873165,3642495313,6682352873,10153467853,13907142447,12784732885,9346740919,7626560233,
    5980935263,1715442178,8051399716,12121111040,14203759904,15500348664,1361746276,9643878522,
    751080520,3368101557,7654280909,12545871409,5782931785,5513691339,2182077819,15490400794,
    8170712350,12168258942,5515730990,7037466190,10986295824,215849695,7542413200,2631123217,
    8060928446,11352003246,14285989604,9046283178,14371457116,1877848604,11898313314,15443740928,
    16650925674,11276429874,18219082330,15776580078,13357528670,3847363810,5511213136,20486918129,
    2750378149,8456239633,12546410437,242720625,3894768353,7347685719,9490969383,6034302239],
   [4968050468,8775582216,16666165508,17934014438,19135330592,5021681828,16659307007,4394205131,
    8245341493,6303476876,8792608820,903081825,8058741691,4082066063,8518203609,1051077209,
    5567168088,6714905650,12937553762,1026703182,376895991,2300031532,1046710995,870919046,
    966562695,13411194277,4333639992,7263270125,9915937670,3298104379,134439379,6306183019,
    3374300937,10513930958,3515641284,5878009461,8585701632,10994268616,6121313116,4670377618,
    4741939265,24461461215,11382256841,13698775439,64079065,8465258861,2231799334,225524696,
    17349576748,6263773913,15883120786,7373113039,3793650234,10636269781,11927221251,6386464113,
    5632614470,5570327976,7027395618,9854634522,22628720639,14269481671,6495509451,6971637138,
    30584942005,7785094119,5046985293,19348403166,403514945,7685368129,719420497,2189331757,
    16166798656,6420392471,1795641737,3943710181,6263392049,12455580553,42281233823,7852143882,
    2916559334,11502861300,4471115506,26505593951,6628366219,14498495004,39570536312,5504219261,
    7990271946,31603116533,10704466911,16579937270,1124664842,3058046152,4225146992,11706407924,
    18312332689,7205484623,4487730902,2315328809,6721054821,3995509928,18618262582,27800082647,
    49737558210,40277632529,30267432068,11697647017,8209779822,7259616062,20067019750,40154654363,
    42654554013,32487184636,19859987824,43783031642,25426969875,11233139413,64703877746,
    28944845437,7820006923,34364250636,31473027511,14107243938,33260624186,15845396979,
    11423363952,14240574802],
   [12695772471,5559943135,9907538349,2904401655,8475955620,6351927509,3300351306,6216616024,
    24794199309,2852297147,37248069448,4401641442,24056507347,5563672487,18639991859,19453275103,
    44848221710,58046441372,53056613365,74451398601,11768273685,108411936380,50469831331,
    81724395520,190383666895,341099927884,443916534963,694067345564,1009320976911,1327263383258,
    1731736546869,2082518304896,2282121261985,2302897394878,2002486265789,1339175693652,
    294887084161,668199476725,1616677924900,2001138482855,1557497474440,515983690103,785030486185,
    1793951157066,1865428787059,776045185628,688541765652,1788408313011,1632732747772,
    179871747657,1403237490947,1818412149376,634462495201,1244607237899,1884509688174,
    623808563331,1416146813823,1887289648198,123704565045,1811177240369,1523129994260,
    629484923272,2716960911471,722204921931,274494791672,3219342223151,2070772749033,
    5162796853068,12277759602202,23956939655398,49347835253510,86410547047428,130271892097424,
    185188753038808,255147319324044,333004805311634,408588526196848,479399593569214,
    545618274473058,600648566110910,634269220616514,642895958658120,631254124492194,
    604548071011434,563271247612822,506648918283676,438338821157778,366672496250464,
    299808305029400,241546132489984,191328124784560,147091989060688,107786268462350,
    73908536196628,46573462792828,26393666933724,12974887970100,5075560545632,1087598614266,
    504745714837,859237997069,713790590915,456581286625,244406020611,111148336993,41746824921,
    11407720111,718613015,1786112800,1633059054,992151666,496289138,217004168,84913392,30021994,
    9615360,2783598,723688,166986,33506,5626,728,60,2,0,0,0,0],
   [0]]
private def pvm_c0_2 : List ℤ := pzigCat
  [
   [44414462,1443058910,367383102,578137352,1334369353,664540922,520470120,837724892,2120070501,
    612037476,6047209,2744859630,1377474687,51799359,628053011,1384525392,1041792299,2925857087,
    2182525804,1970817161,170289008,4025009447,492233975,872565174,1235518023,716733100,
    2148554391,1876309166,2360953257,1768746556,2659108379,3653651282,860039579,785868156,
    3581785107,5205898945,2723060703,6099801189,814973,318881707,3803727161,874532886,3967289476,
    936388889,319129936,2364852804,2334842833,316416321,849436306,2131245965,2404177522,
    4473983782,4620213467,3574871327,1633305182,3398326903,2549075321,1118717085,1256907909,
    1320189515,482299226,1713598145,951348855,2149909143,327358029,1208796429,2602066858,
    7663149459,459775633,636289980,1394843038,1867562403,3828170391,627265719,3022247234,
    3183744756,1619543100,27804045,2258995432,495771569,1264721029,1864437457,285031604,636751922,
    3925713209,500127956,7016401359,39268377,9463515688,2087298744,4069905970,36086292,1791915635,
    1164773466,3276690907,1601667033,3973150893,4500675495,5823860348,1557605478,2654277204,
    3593762576,2479801999,10299741111,1923203690,535897045,238359320,4882510620,1170928612,
    442818904,7048191819,2882160517,3546948312,4530855500,7619903224,4751959364,5971554604,
    1417138685,13502941565,1835689162,17703314441,9047975579,5616456724,2086336322,2063739443,
    5391617776,16586959174,11416933732],
   [9843468996,4576336396,2760930556,5874819441,6034167437,16971705953,11416578195,22957639729,
    11976791457,5240791403,350777406,16053247189,4749644508,450411411,17191490542,14653739710,
    12091496224,3920231668,2962695752,7892011751,7042536441,17915275747,3575481697,1075022471,
    1784442249,10778773800,11773305490,1542907783,6034157642,2236344734,16301772189,2602791417,
    3247465963,1194091867,968587726,7830620932,380566884,1979829823,3732272770,5923451352,
    3941781551,4354498887,1740211610,3156096002,2590256685,2265293987,1885878613,13819862089,
    9830354359,8906164697,43139312,6601231987,6923370213,180567169,5169314270,2918081541,
    1125541819,527056160,7064940836,11275647590,4307289146,15110364052,561331949,807414465,
    9017181440,3311545417,9297238308,18311358066,3931823620,7058705134,14615139346,8074187410,
    1083622126,4813982516,9233806006,8622978572,323895939,3476716039,5659142787,490238330,
    11646359103,5295474177,10968194523,14457159707,8717241373,13034432239,11953805829,4664941615,
    1963074565,14799268286,6230653764,11629233470,15028626516,7077348800,10325642634,2839244035,
    3594366488,11407620757,12093532631,10448382963,791445689,728206998,12223316860,2812932366,
    10168456920,11185046100,9408269146,3800836560,6389713364,2794726799,4891627412,5903185420,
    20967188638,1467323170,12168162012,10963600752,3072160710,17904160790,12030962252,8570900728,
    18950195860,19811942798,18261007536,10281834574,7714432958,1331345885,10434488763,7084861075],
   [11299676663,4247138916,10130134127,9593350947,4873310711,9410829077,9803228163,4001112764,
    10981347590,22821177134,24552471992,3795111154,2880158421,9030376883,3088872947,4844285254,
    2523250516,869255814,4165840108,15728932217,258706955,12584475407,7577259594,5860260880,
    7219931178,4310559956,115395538,6234668552,3411206490,2313994029,1147804506,10182002143,
    7306110877,6610749590,6715703518,12420598245,3285115526,5469542385,4618847714,2469048689,
    4913132958,9504267673,12808299238,1791878904,26554183798,4308318075,4302704167,11250240539,
    12352417101,11760524999,11471386763,7672558815,2854903605,8938542232,6766092123,15510479294,
    4513186832,8503900208,11480830691,7591710954,23580388391,10903326621,8969585488,16472826342,
    5669665634,19819512879,4625264452,2598968109,5127448737,19664325945,24890566709,5215152548,
    5909416529,14252023640,17604322085,1367169473,16546826932,11361100933,4499212842,851815165,
    16909560550,11522296083,1128334647,44688202679,16044337267,17829947732,1039247618,2646033066,
    22079086463,15649346735,5570883762,36390230338,13088620114,11095885023,339613842,10420852341,
    52408614,23888062037,52253707424,39697726249,36022123634,19850822883,552585145,2482687123,
    1580238837,10833454705,5474722892,12085245088,24361126807,39827574144,5774691287,20787910421,
    14057648992,1130166133,58354124232,18437280673,79469332475,32040080506,11615563114,
    16482204301,36319637722,638785460,447329957,32739693760,1108030827,7239935891,6903611746,
    1033081200],
   [8469934200,4917255516,6921922064,21879889750,976564633,12183049361,8792068806,10462971883,
    22309098169,21722420424,15280365100,25824720849,16582227549,24905962240,23309662769,
    38758593554,14763320121,73226443664,223046647787,226814434668,278393246733,569194597674,
    824058325267,1001046428484,1367915561917,1754833816152,2028862518749,2201169700516,
    2190441004879,1929019021840,1283218692623,465488566988,513637912596,1403667961169,
    1834843097142,1688529878489,953781302508,204374618656,1348050289867,1866239610532,
    1397336011357,348328543498,1066897028118,1808669217917,1342617276300,20751330746,
    1359838075525,1726776170120,705327462861,1019012102599,1776970687484,967951685799,
    813523285261,1864820962354,958419885319,1024724332257,1892788871578,605660123011,
    1508368325081,1740120190612,227084662532,1995653994271,1048745611004,1532656296194,
    1754553736033,675959208629,1636218933944,1449006354363,4198163634677,1786289001005,6507725763,
    147282433512,7740120371828,26640483134598,52552233755868,86582248473426,136476524855746,
    203289534494710,278651957523226,356126987135972,435561371701476,514323077335874,
    582048499646314,627979463629012,649507021482584,650360577758622,633003526130112,
    596313679185556,540300742821528,470421763394930,396095798687170,325617244571040,
    262777777415172,207443924394262,158291433541996,114903728683752,78061109281568,48827924366730,
    27580159662334,13639423427170,5517563685812,1434508954632,219626106035,637060127459,
    556885345983,357887269027,189733552625,84987387255,31458962235,8615839879,773407189,
    1033003718,959930860,563750460,268510328,110738592,40549486,13317582,3933604,1042694,246500,
    51414,9306,1426,176,14,0,0],
   [0]]
private def pvm_c0_3 : List ℤ := pzigCat
  [
   [446164489,1147391536,306520308,1637626242,545482867,84690331,1173910135,2180139338,509997267,
    769677932,2469691771,708080758,843763262,1421954470,326186146,2743905009,3292857846,
    1340780463,145347022,1870452381,669893411,2170137760,2677953579,410168039,3923170733,
    1748759728,2691979375,2015378398,2883362329,1325895658,394900377,1132324429,598466172,
    2609736117,2798048594,1454872110,794505501,938167156,2649928879,7320295923,2578589815,
    563327111,5622854329,2114212067,855444260,1568091219,1123264378,3105396754,1794252981,
    891966766,3630882342,4819008835,2001591269,3436650934,2192196004,988561389,628764198,
    1719347185,762149721,2688496661,499652631,4820569227,1735187044,4274223837,903978172,
    864704192,3242758703,2745668405,283878434,1527375362,809657671,4584100071,2320057055,
    286817631,2377779214,1611517311,3881795271,1504147197,712959893,3647753578,1857489355,
    3920840210,3485109298,2599443891,4293795024,2849514371,3268887731,3939208306,42436013,
    1268102481,5410627957,5691692129,2821430046,429934306,6122557478,3746652730,87548833,
    195548904,5946364276,4996400461,2847419339,184357762,7965175279,534793503,3486213774,
    5677648038,2367057514,2791303609,351815293,4674845473,4685845521,1967164748,231009869,
    11787085554,8117079329,734348355,1274579030,9467611533,1949511562,9286418072,5074913980,
    1475186914,11625300384,1701419186,8764050727,13863387153,1775245177,8462580369],
   [1577366417,8663858561,4076813714,4160237918,13364258802,5289884516,21323578284,9671325,
    5826786188,4539639354,2435298663,15496328679,15523656285,19470611837,5936476111,11680161535,
    9364738823,11540999511,9008452233,6062742270,10278092660,6496342268,17404349168,15665313516,
    3977900483,6218879814,7904589523,15645556919,9096081903,2148383455,5117442645,2957220708,
    10869937720,8632934590,2064035264,2853419666,3112763585,10699022021,6173840113,1577655402,
    3580434118,6673831023,4781004114,4038340566,3542944748,743407879,1095200368,465206289,
    1492050773,1985895681,7143231080,2773067102,10038986615,5482922693,10231044617,1752039671,
    10931101841,12774078109,3555702476,6060690793,2093613897,4569463618,9202152029,1248724545,
    8379829014,2645272630,7143998796,15570517742,4997217544,1613992353,483328756,9347961004,
    2030729924,7819454732,5883050104,16105557514,12078474862,1079759612,7669914302,8960131050,
    6488581874,12057847912,394194759,4339078162,2019461861,2683662781,1117061388,13875368773,
    3217428169,11034697415,7642137733,18152530769,14015753209,10336527725,3258464975,4808320343,
    11220058326,7351750802,11593694554,11474117494,11784869974,7902408792,9567472820,10154881001,
    7395353275,14339957371,799882697,8085851603,2980692896,8806141854,1805264801,15564466012,
    14539515292,2705193326,6737089092,513915801,1141009800,8516801440,11385709160,8434788388,
    3523491926,15998468092,5572668324,12588358672,6318612574,11042935826,18309802966,14914670046],
   [17591899166,25559207852,11502963602,431318679,1245606160,8189804423,3383409141,5276170573,
    6837788271,3301710697,5194218561,17205562071,8736163499,17353393217,18227519412,15969759200,
    22304186950,11620769544,604605852,899501509,4681227487,885152914,5619777272,2694952040,
    4188063960,10164300151,10187151839,3866506921,2614762204,4280622187,15836978042,4894845943,
    4105662732,6043906648,15327677490,11121847803,3873840882,14420272629,8871065354,4999147211,
    1644773032,1917416651,7438803591,2580806966,4160546814,704072029,11793695185,3650562836,
    1970134675,23647585328,3726569548,10359529410,5300270469,4674197646,22501146161,10029469499,
    4749267737,18112964487,1900464003,2831005409,9106734830,5573484169,12420783292,22216115210,
    10720569319,10968730307,24555107711,16223676416,2317685690,2084416863,4076505354,10685456713,
    23114044712,11423217591,16088731021,25985437453,8649252892,16893317355,4469622601,3483959264,
    12223952729,15990917236,8413709733,10924135025,6006014026,23792229022,6780524480,14645182569,
    20670196209,37599288071,20004093478,4733159805,23569157076,69977679027,29334487116,
    19017920815,15388045558,22992132148,6171206694,2531621529,6348072411,4689443905,16694776733,
    30967796850,17342518297,6258012054,23884371930,34432171529,17192268168,5684298701,12358703859,
    14592891450,38027534439,34040528262,44204032262,65583054423,7379543767,48387186892,7961848642,
    12833045264,9323989067,32171332551,644071826,3905883788,2842637263,7192637092,9566843314,
    20691827212],
   [12768609474,5140601059,11498296520,9058072390,17409637191,12561402102,18474464472,2226621908,
    7393859265,58277916424,59115869767,47482546772,109216608645,202310865572,310618559259,
    442993421200,609630220227,817369075804,1163933606113,1514015581612,1710544810669,
    1957598594372,2213325186887,2101879429208,1716369768335,1215911061410,445769188887,
    500342970967,1269478768920,1729493621785,1697925320810,1116318946675,103703075344,
    981441010868,1632167860775,1679754862790,887515817083,381584692689,1419116815956,
    1660438539111,949919036600,361423204514,1519736624637,1585170124726,414315379197,946447431631,
    1704045333082,1007046893975,610554931831,1719830942790,1189304336353,478520623701,
    1705233038794,1249738147259,667780239953,1838848086330,924169163361,1103247706111,
    1848453268956,260973993557,1726799740369,1408382765052,843107459390,1998353019779,
    155363440756,1904512424790,1030078914921,1383420255543,1846038639300,1047992434688,
    2462259614949,1938969137487,365271038511,3261788749091,5597225259585,80362729771,
    11688338927324,27409831696650,53836632044954,98690178829328,159916660058062,230639799983268,
    309044780891518,395762113961722,484506936143714,562275608024328,618991783018058,
    652796966675350,665443344180720,656248340351666,622868765609448,566629009254994,
    494956751479296,418199071912694,344531541499948,277552695705332,217501973727146,
    163865493021116,116980832299926,77972954212356,47803347055944,26471724857500,12867331843114,
    5165500148772,1401757695410,84892163967,458448514497,403817557999,253279481935,129546094169,
    55539508499,19501122297,4974527131,338539937,599084598,499735220,269381164,117549944,44122146,
    14571978,4269086,1109910,254790,51122,8820,1268,144,8],
   [0]]
private def pvm_c0_4 : List ℤ := pzigCat
  [
   [823605611,894913448,289037111,1679884980,228058440,1605021424,2079438427,743575642,806996027,
    1963427940,312115282,1156732543,60869659,2556868053,4077915660,435145071,316350057,235114062,
    717578927,3163926730,2780094807,622878214,2923319717,3279617004,2144703733,599973324,
    2835112561,1852872147,719576576,2540745691,997784140,1449609023,769143547,1893326156,
    1326376201,2451366347,1233407884,51134554,1681470703,4282761264,2603874496,4199041273,
    2750194071,1177530801,5313460639,3504545143,695812695,6112071931,779488861,2377900102,
    1569426309,1771436575,4938105394,1103256216,606907379,3563170651,1981617464,2115054073,
    4225190820,753987501,82560348,1525999338,2146551601,1636569815,147351531,2737330909,
    3160523091,2246117745,1768553756,537864335,2770939727,2693438707,1493240163,3786591562,
    1955696631,1593832195,4492655135,1975995755,4993080438,4328106623,1208804681,329289628,
    5559595167,1214518442,852323080,1557953321,3760439888,1145597448,4976981928,2057485753,
    2662049003,706331148,4035214062,1731380011,1401237846,3791306057,10093992391,3024420682,
    1096861698,109441869,4159910716,2804336830,2697321216,612638220,1983348256,3765323242,
    10069690937,107626531,8030603285,3886256370,4131462046,2917752789,9309718388,182661444,
    8542177675,4038847673,3343864716,5354905527,4661467980,5426382542,2432112648,11979877961,
    3259452542,3188553043,303793582,4026048227,13002923028,6011533982],
   [13652141186,8342520883,1255114637,3191553727,8813201877,9035576453,1240457449,11740591467,
    937346591,2676702160,10720934584,10649428132,5668226648,11404449896,12661738088,6226341974,
    762466378,8852437441,22611868447,2460460593,11644959053,17570000521,9786607065,11299463237,
    15112554141,1257783575,5716672960,5787764704,11786487750,18373158438,10162970940,134056156,
    458091468,8010021435,10585218145,13491714159,211362216,3054695537,1790903086,11229319564,
    11847530748,211005433,3987933573,3765258137,2208620943,3253420829,7713731303,5593456500,
    2450196117,831152002,6238628290,1320683264,4957887910,8192477961,3440139171,12343900028,
    1416748095,1510523347,3275964934,6910597299,6279287305,1602220969,14477107781,9893749109,
    3489486621,164301027,9429851557,1800307476,2203229121,6523709569,2369729633,2969407914,
    13028749954,9796498844,1396211495,11201333556,2742558154,1743900302,2041271664,650479024,
    16337043314,5098007628,13980607714,4131178456,7191728460,7519083898,12623132728,6292503928,
    7413809974,1472553524,9549023908,2389838245,3890966407,2401719255,1488421611,10499413009,
    3820569961,18190134817,10166967239,18229902295,9893502457,7567278565,9549848,9258382780,
    1532624971,13149520180,18673521768,7350716628,14887545638,2751889512,9956744975,6395521937,
    7555179215,4712161041,8836605643,4188919842,2633469755,11761272280,14869602020,7323858386,
    4366637124,1141303476,3360930536,9242369426,3448385454,3767955632,16256762182,5056885576],
   [7857952702,11788259226,8499206976,5888488450,13034981230,9165951580,31340714698,13606594362,
    23271895722,7073297266,4503473456,2908006350,8216777951,5337615239,1462388611,840011370,
    3287948143,19875460873,17247411043,14599500313,3190649886,12803100484,21439231138,7525873650,
    18775161888,9068271881,539904910,388945420,11682843550,5929860383,15334195638,14951158257,
    5882456845,7673418117,2157474614,2968331264,6971231289,4221946546,6299070952,11135618178,
    1574358126,8672300546,15284581751,7309709854,4687469815,6676897118,10812407541,46919358,
    5058844195,8317973456,4767454274,18432455619,3004026268,4833553521,4320708900,7253953116,
    15347040216,13952972820,11085564895,13307898304,14982923775,10767446175,16638234271,
    5929786737,3915045906,30560612487,9933663332,6112337082,26301170590,1596725711,5977820267,
    19726472009,8426254104,7428415030,25100837273,11543811568,4191614832,8979578106,3447795124,
    13113367091,12751471177,6265716645,3553241953,33664446605,18701976644,18751222005,29600104146,
    44861515119,23704367228,29614783533,35023602550,33646988646,26738713469,23514270375,
    11903427685,3434502282,7245787805,12224416096,37034320565,8291972147,2085425160,22369341959,
    46783819402,602594177,7217822901,21282453892,30858156921,10884886722,423230822,15608987883,
    43110285890,23222606429,25225371761,55475813640,14733323065,49709215907,13765536544,
    20286634898,9808650606,7198223505,27127975371,3223489986,26878620336,19916998564,5999806982,
    13217865275,9579758843,5304275574],
   [23669984787,2293656320,7326569096,28158670090,41278007721,100498249444,102351047429,
    152782254252,236705964079,384750810746,552325325657,741322962154,937333798327,1253937463956,
    1553880650043,1829548144908,2012020491947,2038122212906,1932497744273,1650913109046,
    1054487403521,200735861306,553636771920,1180733205109,1692252091844,1693835091863,
    1085576435874,220977479153,730424246039,1511334538664,1680477536877,1123238939348,98733956927,
    1001813725023,1613387380708,1394765329989,348537978534,901021717384,1544515280495,
    1288709296924,110962231871,1188791129933,1620070380754,772346616055,676350902077,
    1563711572442,1216012064399,267311179045,1615103083272,1332803927857,168650920693,
    1575525714406,1371802436405,286036969889,1731325592282,1197046287403,772312264053,
    1794402435754,685011779827,1374230502889,1665982387442,296756831418,1883436305301,
    820372730682,1462817719554,1612875725879,755171022977,1923642458392,91728850001,2038234644575,
    751819559830,2109264093698,849993926807,1605972978163,990659348168,10070389150,4955731754931,
    6549023192309,2999531593437,1524389069326,9527307286554,30888376321010,70454292230708,
    124517643718162,190274682141184,270043845700254,363136345928148,459431916965434,
    544983733780684,611333482846122,656558028065032,679325548076514,675809649620490,
    643333866712020,585283749860458,511142658149150,431834598612060,355067996317646,
    284129580739470,219714967876580,162259171005844,112907822422964,73039108560832,43310792471136,
    23130799517038,10813624534102,4162681705296,1078471776220,65063988909,322574988291,
    268593211281,158611115533,75872995743,30102367745,9581745087,2075705855,17058510,321304094,
    216603112,101231750,38538892,12521594,3526342,862174,181598,32378,4728,526],
   [34]]
private def pvm_c0_5 : List ℤ := pzigCat
  [
   [1141354011,825513870,815843419,1385799406,626802677,2758184724,434749595,626912232,905205697,
    1199742297,2254394270,1244021833,3086972262,1741842415,2411432163,1431016994,843777763,
    3567505228,2765011363,1687903456,1848267255,3652062706,1168093389,828877963,257212347,
    1825081965,2703433392,1125904553,1027225269,509185081,2681661239,655401193,558163266,
    2439805475,1690325565,2579468784,925380119,2367118929,1872173850,323963979,4336987999,
    572717212,4795878104,959901557,1716438290,650311712,4019864581,3499492041,991330724,
    6476203405,4179810607,3143167969,1988986442,5626474829,26365088,794277014,1468127370,
    3280574536,1187360715,2204603789,840770542,801613189,416467238,1055263910,2054428068,
    304642919,1605725787,2015652810,1694695083,689435823,5175238363,2317006165,2491842570,
    2546466763,641990156,4799439437,3960245091,5908706926,1165414089,3547573307,547094070,
    5036597537,1222366638,796560699,431228500,2338978125,2141037723,2039263005,1097512144,
    3768477645,2746984299,7505172872,180925759,1971899954,3049427886,5040274199,54890683,
    5198577454,1722311504,892418838,8219398827,2915512434,8705870723,367305159,3205310702,
    1938857215,6323397324,2272071021,3286304482,8171667102,1698048024,8313573411,3566803998,
    6403146109,5057372839,3279152985,11968232310,3417587201,4701408674,403886735,1112470834,
    14637075315,4742917992,36762705,5563776568,810030881,1741950377,1667814308],
   [1792872316,14079635949,10125218,3997333624,5619646284,9615686152,6207611596,3660259398,
    2510378239,4090108639,2494671143,3365152955,17443844235,2955096897,6077085923,767079813,
    10550292296,2412081954,1372012304,19264891386,16895096994,5702704810,3316095776,2404012311,
    10979946249,10887430231,4083803363,15996196787,14481932435,14960128067,9310102783,13905454811,
    4603588367,7334810498,9449831726,10111669604,16855323520,11470764706,1509495343,1008073315,
    8225351445,5913470021,15391800607,8232711567,9089855898,3174456804,8311259546,5673858588,
    488041437,3243245086,8782509517,3203401475,3809543874,9514318531,6392355995,10704174230,
    1108746054,2748282846,136245533,1107070455,4194244859,8191869640,2341662094,4174651079,
    4912274370,2210110954,5510567081,4533299069,11618726195,2943198211,11617682701,10048507573,
    6086421082,6586357475,2383095791,13734234523,1431139470,1266209230,3430880578,4250302074,
    10834130464,5236874044,8406312148,1888234449,2572821458,750061072,9179034164,10372937814,
    9385195738,22405707,16091811832,4570086952,10365623088,6745183334,9399315452,10141154022,
    2649172218,6709603868,3221959173,439422100,3168567090,10852015853,300582363,5408549333,
    20892372475,12396582427,15356674689,9373159913,9907367211,2788803804,4926029017,5459237450,
    16306807346,13546148126,15190733444,9134923080,1803477361,2684099781,3473283087,9382457949,
    4565206285,13174539447,238451287,11729398212,8587673880,2766075552,15065939268,2825611717],
   [10865637114,3361919981,9852882698,6788430066,3032215320,11474411330,8565739798,11183604740,
    8531178856,1070433492,9432984780,11643626602,22488431008,17074223558,21893364854,16587570580,
    18477048068,6572965735,4560031192,11255944411,8828781914,1909727824,873948918,25833709963,
    6414198323,26902112581,5868617217,9977857744,12625552582,17277906130,6970553178,7608499154,
    5606990145,4585233604,4578927954,18021128754,12210495397,3948127528,11013559445,1981432396,
    6249444381,322384839,7762791579,285194379,14264969436,887495856,14371111516,7919891431,
    1461115055,9657090660,1767289897,1999677625,15801862577,14857093060,8713227569,3483955986,
    5440475876,13001017079,827350655,17116740485,22383186192,6394595639,11855708660,13161661146,
    15718642096,10499775163,9249138035,642674530,14003035797,3292031624,35137585551,15311216509,
    20757884140,10635878478,3855461164,5068217415,9498998890,15495722165,21252305342,44088551339,
    26088875040,19481955209,37862616200,26543704083,12375671612,5946305744,25560054183,2448467168,
    25279940331,12222126985,9233283332,19354781566,41476991789,13130907999,11334617414,3784849426,
    46318099448,25126968805,16463878079,10411352712,33539910555,23056904642,2740033045,
    32352763057,3799763838,36002137159,5779639188,29646534050,25737916715,30461937030,22429587620,
    50727366831,8747248656,33186221396,21227413267,14153386719,13423725250,22493532764,4440391218,
    27987454685,18517795981,16728134512,10581916720,14458698544,36947778567,4727902008,
    21351999803,84646561724],
   [104973114275,175410940706,222559550831,310560123688,479451240739,659556962222,889992629305,
    1113817149698,1351166999001,1648217068700,1870697743567,2022280781918,1964215193605,
    1757174164176,1375079130333,807237293742,59736902411,696095747779,1355783975372,1621323132233,
    1501931812756,1061117994281,275302024328,734823908928,1465051829293,1568358001884,
    1195895950397,369618984518,740317142024,1489960428921,1472261642702,781745328409,333825012521,
    1316280078530,1518889602309,785451924456,433961019642,1380047556651,1399746065196,
    462882531023,903694498909,1595562140040,970786119813,390944833965,1472749685904,1312921267221,
    8866827967,1423361545824,1491528981723,38128759744,1402759848962,1452149810741,20496427860,
    1571476765990,1365403030311,395666997601,1752719079580,956311639947,987020123371,
    1743381153688,246059727049,1672634514347,1263803875896,906541908152,1821520665951,52599998068,
    1841550868348,912682088477,1497556310839,1527383998508,970563271276,1971845768751,
    585500124021,2069343088032,222454603112,1857395786107,641403857180,2531000645964,904542609307,
    4747533037393,4517730136657,4092880488689,5831448749261,2174388677797,15940991448108,
    49463662691554,96052535693862,158490951643272,241075708457894,339779944599770,441602146010940,
    533621168162674,609082102839160,664439671102852,694351143784108,692600343704748,
    657628597215956,595669940476972,518066750899200,435733727918596,355575081083262,
    280643244732422,212351807424878,152227252666854,102102309019580,63281392269814,35753487844736,
    18085050348824,7942501673356,2826862564116,637149785354,90506493645,215318689485,158499149163,
    84609688445,36456239859,12812328007,3460670407,526518341,113609428,136253548,69766630,
    26484884,8190866,2115526,455472,79932,10830],
   [972]]
private def pvm_c0_6 : List ℤ := pzigCat
  [
   [1459917959,895596030,1302014565,1558294808,1452943447,1474003400,1005320948,307435404,
    2444290948,2746619939,1262847862,946785725,1160490703,3990871666,1484612147,1933003678,
    4192577401,1517421036,1174053179,2660051458,1500834,2027047489,1917334232,672441751,
    2113038416,423588506,2357493433,77386606,194354660,520572367,1038071700,418407262,3418432433,
    788293273,1427003322,2926915493,2668148893,1523076860,377258712,4291732063,2622442562,
    1679587992,3010583657,2552587643,1954331870,3523236831,3413092134,2284845926,2571441882,
    4512038533,1386044298,516863200,5331304121,3569019415,3120966463,3155403909,901997749,
    4346532981,2817318165,588120056,2046206238,1676475310,1118921815,2266294016,2452856853,
    897756455,651948488,195944329,3857325802,2781988629,233814060,3616610696,1946325505,
    1145551358,2585853575,7768047043,4439246190,541639957,1848154617,3792982609,1821352081,
    919535337,1536947328,500159935,1443318023,958930835,5908794035,3412679054,572957784,
    5812079227,2003980844,442826258,5159958607,1545996496,6294153475,1844541394,3510555589,
    7799563430,4035957140,6768574807,3874649682,2260721007,3228171108,3402500810,863618956,
    2351135813,2509407144,12147733781,1062322028,511345934,2046189876,9441301925,9730985244,
    816113938,4165691608,678484417,12050191506,7522835107,4391776495,2068772535,3253889095,
    3785409159,4905008080,2153759308,9353814338,4716952027,9377440311,2868313066],
   [443281083,2671361313,100761943,5274323062,2183713004,1727257820,9592694233,214727153,
    7033939015,2723554879,12246367100,6496689118,2447137358,8438946760,420451301,1088198705,
    4629477106,8715649175,15685770587,7694892877,2497781516,8367797231,564399709,1181249354,
    6184215782,10482159672,18253581832,14370613912,2725238048,48865066,862938804,5920796071,
    13264107471,3967196087,14339334911,15842225727,15523705055,14598512331,6157770927,10304429989,
    6033407100,17021530006,7129785332,13393973460,9227331080,5010361620,332611184,13894058027,
    13569615169,180225207,11139062221,3257601762,11334748904,5823843830,2714688289,5374620616,
    2351490420,5344175285,1711739313,6173834991,9031904593,8436231714,2099000124,702818568,
    112545815,3412619661,9568125726,8549176853,4423393312,2443754034,5097197940,1799522203,
    888770608,142506319,3019077845,16844597859,6141947597,5361861631,323212823,6754227543,
    5377945051,8234393997,1379448975,9232893187,5682990492,2071739043,7974768302,13018501860,
    3830581400,2100102774,2413509303,7393397524,4904668276,3120046520,11754548072,2976622320,
    10006029308,11802237284,873847197,15517470256,9038443740,8280773982,5639558188,11912435358,
    324318107,909882249,5267812936,2395263375,284525521,1800993879,13248594305,15778830705,
    11282792353,16425906063,6861528659,12273560187,7385983783,200105811,8616674506,9768362166,
    26287828932,792351907,11823184546,4093416604,1433375936,5946906965,15256062247,4811059183],
   [5347222245,1466627435,9214142908,5362976366,10387262802,1944282222,7174975982,2539523102,
    8970337096,1789002389,10243233902,225075796,22436116968,2010315288,9475010206,99637076,
    13286365952,296690592,22853235410,9533636380,23949658434,32377801096,9078305358,7314225940,
    1772652609,4979270032,346454085,13525432396,4746137915,2846237883,30927631833,9431036381,
    19661728871,410548385,10798775536,18016000412,7744466508,2200839405,9201411938,2263026777,
    17845393758,2759629030,2605337483,5097504116,9231562293,7535968334,11497780447,982972917,
    16187859929,6769595724,18019910402,11583688697,13763361054,6188230743,17553045974,10119150027,
    6812923564,3479920337,8648734247,2109714427,9278134542,6898772152,19364535891,9884864430,
    11163608431,7358848759,2850144802,6018492849,26964098632,11380242380,4372286626,23739641027,
    39445580558,28354591635,16538122340,54736197431,7175545118,15947273561,14255667778,2205355184,
    13725344199,33337608554,10057966635,7825026669,6093551147,646116965,11889990829,18174040316,
    602889891,17005191749,42019793746,19156394089,20945815337,8105138473,28333332651,39491347070,
    12063116159,40000828177,5708802934,23284732433,24116260484,27588662404,20745894871,
    15448561498,19656736349,21132693137,40570979122,20167764411,33887142527,18458116722,
    27508294337,34929997371,23221829628,25375684874,7069101955,9194192015,1362686316,30076030710,
    28282422599,4861370496,36118603367,85594536258,83817487485,145418801404,256808139529,
    318689538410,413431300555,598332038810],
   [814638311855,1032233209456,1288707709073,1511912402566,1711432977709,1912394750232,
    1955489791685,1859213082190,1549757689125,1058935247918,481371947455,209411447561,
    884130625786,1408320765117,1635656923646,1408520574651,866574994940,69569691355,734055908425,
    1364658136726,1590607285613,1237263780298,313888015105,633119445143,1292209994122,
    1477357696509,1027375150496,39746619552,1075873954113,1454944500732,1120785309637,
    160979020108,981626311776,1500776716837,1023754589930,96188340284,1173064043877,1460866996402,
    674068967969,664296449599,1517208682636,1132198225191,205835939203,1335116841970,
    1387692117923,192086121496,1272582939166,1524369323763,283295330706,1275685156114,
    1499026787913,219937354754,1330583328764,1513749105901,91530412419,1616915298094,
    1189726998845,625036099613,1739475471898,627779349235,1284244297079,1584511379878,
    341772505862,1807182768987,692017027008,1413689502820,1499181619585,737449994207,
    1869434741100,48007606115,1912854753719,745238131450,1751896994144,1275682417381,
    1532492036105,1537543031442,1120181617560,1903276796305,833413735739,2623920801198,
    1773242871034,1872554281941,2417091770419,1720900155889,5509979935911,10984124481873,
    8574254309697,6466906737312,33118830141248,73871259869728,136329623546958,223410711980474,
    326940328596090,433247200368280,531832970608904,616274516107126,679351620919506,
    711613488859634,706302395934768,664815155147658,596674986721530,514399223636340,
    428170895419104,344001578051030,265119386324812,194027573809152,133293107540662,
    84966134248392,49666174879624,26258543521040,12309455747348,4933845044428,1547190095016,
    256970265060,100435634949,126949615787,78221753373,36079376835,13334689773,3888058267,
    785092629,28644403,64542076,37402948,13652840,3778666,816024,133110],
   [14382]]
private def pvm_c0_7 : List ℤ := pzigCat
  [
   [1831977371,1109007832,1792362753,1408750866,546459583,861734733,1986310616,1673273695,
    3067153632,982682718,1491698173,3077631988,3719103711,1569859884,2246627973,3480566054,
    222696992,280604214,252325429,3490521133,1924516932,456077486,115654636,881844204,1607861593,
    13097006,2265862770,719235926,914481927,707888282,960865261,2161161435,2147120766,1610256886,
    2040215463,2471926819,3239738382,2307224277,3506934041,230634602,2095362468,6077456175,
    1662126860,150731845,1115809884,2003729447,1395999760,1595511275,5242994007,1876446662,
    3661734246,735781565,1237925858,456856796,803952212,465675132,3682428315,3144128169,
    4096365437,130847980,4062440525,5433326049,922865047,3398953057,1694333732,421176640,34534796,
    4082145476,2846785639,2842940243,3909563628,3683682437,3615074718,85098817,2398939837,
    1391348938,4774519490,72231730,3327924023,2247082797,2885496293,3249220516,2435998965,
    2749032417,260729238,5671739981,1778376861,7166439214,6517785073,1343796202,3779130051,
    1164429028,1729629859,3973367407,5166551416,6975062503,1931740274,1788224910,3662580599,
    7043551879,1566653474,4885070029,9363105148,2089098287,1345535130,3198932377,6709926130,
    8274265221,7364718638,4212759240,3847282556,10494910765,2752442896,12648070,6803766513,
    2602928415,4669110598,6257343319,1849151134,2926289610,4364239188,8105227924,2503537769,
    1371065674,1196401222,6765239775,11214747083,5125759170],
   [2915498838,6264674670,2192746803,1889848431,4201343574,6127919835,5681061775,4262453622,
    2191119749,1239697454,9946073322,2579303507,5035934023,5298899965,4147141195,6514189209,
    11356313088,5992345444,941414595,4787241866,10976092842,4806727278,3807808697,4661456117,
    8005841809,7711520885,7072170279,671145474,11399933103,6407207313,8526353630,7492048566,
    14580878516,11723023662,11665294866,9222271054,5822836375,2976036284,1377558327,12062998979,
    8696514943,9758685179,17977202693,13201202079,23221240895,6115434455,2109215644,750723299,
    5944380252,19190312808,13022546164,4741238834,7916559876,880075535,17860692007,6505201519,
    7238199107,3801087981,9314589144,3277134561,8753773352,1085232771,10323736458,167697794,
    8021224791,7648166891,1614981772,2461374037,1065318122,2510250533,7473770466,2410149949,
    2008873751,122583505,6211309482,3828026905,3926204318,849400399,11372339560,674038565,
    7558308261,4184782625,11656130053,3090147743,4311732975,5302674947,5783600751,7888672905,
    369488491,10973726601,9561582661,7104672534,884791015,13390598666,3872445966,1461348932,
    3093399998,6508820806,694858393,2746494160,12540191338,3134147874,5393773848,11060462288,
    6081346256,5471640538,14136776440,5369229230,13322247292,8043653486,5120007078,725043550,
    6412835564,3224119219,13898548344,9931542581,3007108547,9138007613,17241794143,8304233719,
    12882218581,13602473253,16206184495,10259861923,9615807614,4391350460,11906950264,9551498246],
   [16902983116,6346051648,9782370702,8143742967,764274168,19112164731,499481645,10444555763,
    8459689604,1001553944,10103933960,3098812285,16277548264,3492721548,1283946413,8939757778,
    4054347541,14861704864,9493080074,9008351550,387656326,17577157384,3337911745,9808648854,
    1679810433,25034526850,18823300044,26433468016,22656785368,6703799682,2903590116,1483542150,
    17212293310,4445764,11375812788,2675252091,22630767833,14767798279,29081060151,4541107362,
    1622123160,14154326192,1776274074,902627202,14238065406,7110503763,27986698508,9033336637,
    6090486010,1379693009,12991736974,4962327105,15063216799,2190743879,3584277955,3012184100,
    6433260253,17368548040,8074122747,1304327394,22733572742,9654762563,5309954326,14373829953,
    11482686268,15011337333,29002779918,39532106993,39531610526,23970755821,463364592,26146494183,
    8516042902,22657081924,8358258177,17210252426,12542530631,25081025850,14578081000,15573677427,
    23590931693,140785951,14407464639,23040377909,22495897630,20226685259,17799664826,24471915744,
    35342380341,16542132236,8494819819,8455252935,13243121666,34310553319,29519748696,30166523102,
    25834668601,181692843,28458644477,3107867465,32184715998,31924281203,13515191069,3265951479,
    41354684709,25444880484,35102126124,25745210681,4450688259,21171602662,21467450621,3098296076,
    5141794715,34457847462,77318761821,32624241656,98784526257,166808076260,233605753483,
    310842457808,423179157963,595344554710,752066537855,947131370706,1227156175099,1471039171202,
    1627473683145,1795264933412],
   [1895917151465,1845159761892,1651457557501,1277982415482,718413674349,82149006268,528824632974,
    1098631911051,1470971210614,1544923767367,1277276920982,621470601917,160434508295,
    901530187058,1396065237145,1467669909812,1108228630919,317538222894,630339549274,
    1320021456125,1473853800898,951340770731,96708905886,804595734262,1405642344309,1319028336628,
    413186301483,661663601869,1321569027104,1255888801399,491347133028,693246645162,1433371932583,
    1152840460088,134000503713,988678392709,1464218595594,830655728189,493604482967,1433259127270,
    1211420813739,25731258665,1244187014646,1408176568123,340407967472,1108787531736,
    1564027025399,434283374972,1106474781338,1532427970269,407453667416,1169170337814,
    1520330440405,219135506652,1440298667844,1393529612947,331678552979,1614981369604,
    964430414485,915254797965,1689816367950,196361196929,1568383855561,1234341358278,912509786894,
    1719234219073,67904645350,1741126967778,954644682253,1391056449739,1552795243424,790453720716,
    1915355523669,183100146403,2038828479814,349491167373,1997954976339,786721119562,
    1858672803322,1286149817559,2068540674043,1376892533170,2491670872974,360921094741,
    1145599272229,1097154169284,409862475965,7704105243957,13464476781963,11159802316127,
    669988935703,19563271784822,58474858036544,124963396434596,217646036743836,325649000244586,
    437245320590776,543850486581282,636407978151442,702465764829592,730086191625202,
    714907699127504,662874988036222,586379114233602,497959355222270,406594281535046,
    317874091099768,235903115741328,164428385406740,106473863844784,63362486873984,34249546696256,
    16562974137624,6995350427128,2458181310086,626735338212,39815796774,75777256979,59708955863,
    29421407637,11079448755,3259567163,696097445,69000769,22001614,14668312,4699234,999964],
   [133516]]
private def pvm_c0_8 : List ℤ := pzigCat
  [
   [2290859043,1296603856,1643430331,116569825,1521034972,2405905605,1813053686,398485849,
    1955287423,4435477158,2280409405,3406574468,1096184087,1836034094,1208417105,2065022515,
    1439916274,1084755845,2734501428,1665724496,1969614169,576954719,814185897,476387413,
    1477152826,1179458244,1788797083,684311445,1927420180,390068667,748328974,1547850028,
    967300538,4532271181,884969940,2469852510,142586570,4642282711,5059233036,1621645309,
    2078146093,1532885827,1334773354,1325100719,3737294661,967610098,274077355,3451546995,
    2902557724,1973572630,2739526035,2219461413,2663188809,1646223952,18732923,1202791276,
    327880146,222684461,5150985402,1534467009,2358325755,1254533861,3684245495,238907425,
    2769916619,7572396039,1654942674,6472616667,2303503467,1784618334,230473540,928732730,
    1743206758,1591913023,3290107405,3818056312,182530159,368054713,1490819027,1599637193,
    4996000156,4609479278,6453352595,5227515156,6142484591,1214510881,2399682860,1388226029,
    380658224,9385440117,3499392102,1571210635,2055207759,341265664,2404055838,8901692867,
    6193647330,5023016133,1249584956,5469540059,3321768142,4484479053,8386681948,7634490373,
    4243674229,4009227393,3725612750,4229982191,1050634752,6727302206,73608701,10075941029,
    6234040168,4363529494,1739380691,5596340862,718819583,791395138,3209783539,3036302973,
    1628405643,3090922250,10274914765,166386553,4071765588,193981264,3171046694,3086580958],
   [7913894846,5636543358,10469998733,7174110983,3472554120,5759286921,2659638602,4507594058,
    1981634594,3194116641,5489560138,4873874861,7239185129,1336389260,121415198,585264490,
    7188088940,6420918376,8926056095,8223837447,3536808693,3925366610,3271109791,518478795,
    8522733166,869406128,10578995802,10427804130,2309602943,2727300145,8095723125,481346344,
    4883605767,13409145399,6034160053,3509540409,9862677855,10499014352,9203106452,13360613072,
    12252443366,6671766654,8585887204,6155934252,6116655701,4431975795,1574349806,7848198267,
    22714140159,11147526839,14424961891,23873419337,1703229893,9829918951,6981326648,5009740754,
    15486696590,14765106530,10565185182,1953317322,4285056921,15701809345,2899742851,4338973353,
    1148712281,6078859921,5910593156,8300155430,8249193756,5723655263,4513142106,5381154589,
    4339863967,3705433117,2015057199,7318751298,5265631999,759112175,3923553400,17563071,
    718971954,4292284497,2355104814,5234432172,2812791204,12122462740,10484124575,2103178751,
    3162747407,7307968635,6833840621,4356742871,4751368923,3986577963,2753815069,15415297075,
    9327621247,1663800500,130456171,425465653,12888080832,244041154,4518857638,2367447446,
    3806095288,122483085,11654135636,2998659197,14777060414,1760651750,6902118566,10983131516,
    1398047262,14416096370,12737886782,7532580088,8639404422,1069632740,8683981116,95102958,
    10982476012,2149853946,1519269107,14551407907,1727737332,14209596515,5879532773,27264812097],
   [8688729807,17131374835,641689727,4811362629,10944918168,4703422402,17578496638,13392616002,
    4965015536,15894915650,12791619385,5613955811,9848540753,1861189701,8291036029,9433163262,
    9197826197,15692503720,4738754752,8675928720,3149841163,2805816260,10766720350,336144832,
    9896331268,6517839804,16280456624,1020561868,7670579120,3370086782,9030957603,24884148888,
    14278910064,32327408710,16074715714,13723807778,9715120044,1157169431,20687793392,1560865487,
    31446563948,11928798575,10171108695,23287165673,18322291731,8023275323,1503671486,9529152848,
    9562446651,8766518834,7517432564,16538788790,5616210215,1709123970,23845298240,12773079297,
    18854002520,12004630183,3879964112,29058638061,30729789888,34984417615,30401823116,
    27008552805,16424121268,12004353214,771091202,3946398062,13168072279,23811280878,21960621535,
    330150047,7518861654,8029213162,3432558640,14271932705,20147719925,1067127617,28725794322,
    29285826717,6673031470,24723267960,12537705627,40346132822,10312669403,16746086603,
    17317966844,37214193147,4640063077,11250946525,15085078717,38660147930,17276259903,9402605767,
    26977914292,15484705305,2164288152,16014891847,26232902157,46772521150,11010434730,
    21768770045,9189861768,15030450689,26105972893,47845164188,24588659595,8770932063,66906375173,
    79596636484,116034752981,157471114846,213081411805,330316466424,460678797579,571915770002,
    722684654969,954576493828,1182840940549,1365344135288,1610906037655,1756478099530,
    1839857011741,1781707950648,1651573694277,1391277165182,896887351075,296648249844],
   [299248596064,873489835823,1310395805252,1477587865449,1394565925638,1011731363497,
    334881865946,448008514654,1095550554119,1442465868978,1370851868529,876407015276,136245587419,
    703057627399,1324968372822,1415657400387,957786939398,54655870539,829827062023,1319291837316,
    1244950455107,577323542314,387860312642,1220561315251,1397013530356,687978889963,348857976783,
    1147572192568,1313369787285,699599218778,485649921640,1337633687513,1238076362740,
    273927255641,838405037419,1438560143814,938920188631,365310908069,1365411934360,1245837819639,
    103703217520,1143686583622,1429285055749,443831438542,984277144614,1542052995669,587644833440,
    977023187272,1532091415711,547417726766,981577603214,1547620792333,421468466092,1217031574954,
    1502256169249,11610964358,1517882484934,1171870858925,544390505671,1640958569708,681785991549,
    1248012923317,1524289826300,291060743420,1716165978911,758617188148,1343349959494,
    1472826267933,534619669531,1854240169114,280611159995,1789539062577,1005722840132,
    1434794132006,1576310929607,996424800217,1904247936550,511999972036,2085022722593,59984288203,
    2232268011704,266693769811,2484639015567,96586190946,2270204278048,33333577554,1377345388541,
    1726246243882,3496463158536,1506742548035,9217672511123,13126809134949,12778777766885,
    8238764856799,8895941482636,51561439939106,125238896190756,224154265968156,338124763424890,
    458168068897148,574155913556524,671032592508670,731827277998796,745955128958352,
    714593763146836,648536238653258,561558129491378,465189092242204,367597579728706,
    275016779441426,192887521855730,125518530426264,75013448191046,40736608864900,19846643915074,
    8514664056976,3112171425354,898339397902,154272288398,25258250511,36887618625,19536102057,
    7256154483,2032938339,409343955,43625231,5283420,3515034],
   [718578]]
private def pvm_c0_9 : List ℤ := pzigCat
  [
   [2731189475,894095810,197072757,2364572105,2220240462,896341181,1727118487,3737997568,
    4214893677,2293554452,1133069385,1624813994,880280094,511110761,3307186268,724969361,
    338409789,221711488,2474053179,138958778,2200531114,1145880834,322785002,242115098,1528157471,
    2217653667,2077151072,696788154,267120019,1597512669,2323873228,1845886545,153997111,
    1036620844,5696980606,5261325085,670901001,2224261216,117222736,1955905365,275878197,
    3012899396,699216937,3451815321,2196348974,243558851,3720912221,1245888646,1165474729,
    1656749363,3134166639,270993586,3092876908,1110319441,826189042,3755056379,2651049959,
    2470738642,1331463591,1570924257,2754660346,2193501777,6817062046,403965339,3005564683,
    1526451680,1607454219,3229520165,1508599319,1285125697,6520859415,1637614901,4014951695,
    4294153261,1043655188,2431237492,1582223043,3989732654,8299250873,4986082426,3363930432,
    5090839525,1976744798,4185265723,4354690878,1510424917,5058469262,1573967388,2617695133,
    6476316827,9061708522,7058649773,3453253664,3901739455,39914702,7856963569,5743529158,
    5568247057,2519439150,2894632029,914442007,1331994213,2966806070,4065650049,5663962239,
    25994481,7643193002,4965687653,3847303367,6418125284,9523418123,5522536367,1089155540,
    4037811196,943068551,1577210434,5087171963,3374010902,202967466,2741781689,8142618696,
    3341589648,2845712981,69496380,283602479,864386376,997208053,11059209031],
   [4278892644,177355510,6375705131,2852580673,10678085042,4469099556,3738864430,5855145498,
    6002427683,5993932031,235453049,749429363,5019163055,6126104250,2840112732,163057740,
    285672990,55553890,1957953469,12764188979,2353902800,11250610560,412727447,4012187294,
    4077398335,4617950115,2889958465,2450946963,790982785,1674969495,6838455289,15595663984,
    8499329638,2714016864,5735555256,143664094,2098664257,929389207,5607700471,4927338177,
    9442671591,13032316809,8570640331,5788656466,6076528618,3226517283,26073569264,7486491092,
    7858141714,4750899760,5690874482,1395723274,419610803,5442688185,5551481795,19160838559,
    12928979975,19653791965,14274434131,12740474823,3108380681,3504159719,12268773996,14121038914,
    20851157112,2524561120,4132738809,2381368242,7503809367,5999041799,10876893431,2463298145,
    5461964810,921337769,7051545802,7428037838,245048206,1208069653,9822935979,6409398136,
    6768966033,757951977,1164088384,3422152063,3555996814,4251487558,3598348045,6481011779,
    3874564990,2478527546,5983548498,5838415790,435653340,3576112417,6345066908,13034233501,
    7371723437,2505175633,835680070,10505985837,1672622488,17067116859,4991418051,8415629003,
    6831950911,7186579638,1482127895,6078525316,6331642542,2322723039,7820632402,628228577,
    6463314726,24015809,11643131656,3166617158,8173031652,1409778429,16552484890,276979889,
    19655423174,6398593662,14324772952,3668782479,9476597716,7233212970,13027378924,862075577],
   [673147701,3834020626,9461314755,5019884244,20050987699,11254975525,17632691753,13319357449,
    20062428025,5681657466,11868910611,10207438442,7306622128,15813976146,16984767298,7769794024,
    3800376250,11161011455,2314102486,8955230593,6796251777,7548321675,3998933878,12311911162,
    7728236657,18060133576,5005184209,6035843690,5160986666,103395938,10614060974,743982143,
    28467073070,5387581581,16106897870,13470119199,3758695652,12500184998,13962473346,26340306208,
    21968687006,20135364044,2389876289,14408688176,8495928332,20255832002,19771267770,1329967830,
    946824961,43136200633,10779727096,21644861617,3439021634,26083747073,35100190732,30580756407,
    36700779148,12365012183,7824259790,10874794772,883010539,24542548208,9995458551,8006010890,
    19277182417,11099806044,707621585,19811543311,2176376370,7143228366,4131526904,4153021605,
    16957209916,7200373659,15819537762,4564716625,38403631367,43181370716,1873693900,13866972649,
    14400722388,33335385277,15304544160,2319819614,27536765989,18321811488,10735811819,
    16683609092,26515336886,19965529121,27854409808,6938415624,35544398693,941189695,24014507929,
    599679000,14266583116,26286396253,2553163221,56338051302,45612744815,24391132560,58159291149,
    65665757616,112513957337,209974719148,249658572925,307171488962,453968327153,615060477182,
    761154886521,930854243048,1152223298971,1344813529396,1589893924189,1711978253096,
    1773545413435,1777231763588,1650748454019,1355523223098,956474798421,478664991838,
    127651787920,735033150985,1173340609618,1423077592301,1395225658526,1177942097999],
   [634345115630,59792894504,730583959581,1267138312926,1465001268833,1199693185250,597548969017,
    149147507327,881594358030,1332131960437,1318103361430,814312733193,32377687865,893798938240,
    1343826612471,1189900448008,537961396103,376262193825,1100112101718,1312065507563,
    878672450280,109767105424,1036349262025,1359460891846,862846630417,130192857359,996314453562,
    1331553864775,827963709806,343099756256,1263394717515,1263357268076,379682773013,740057645811,
    1405230368350,992603247329,254369793713,1327575917632,1248855999409,190656533576,
    1053539515114,1431587766501,529257357942,891475767496,1512638296231,684895327294,836554406854,
    1525766602623,670119118620,839178294310,1511130156655,616438281874,1015944116378,
    1553652607217,284685098478,1313076093234,1375898946311,219403609011,1533650771406,
    991175646831,796289166131,1667850720450,289725162227,1502827248141,1243376650236,724340949054,
    1718783005895,267319645528,1624906099930,1132600956201,1067729407747,1747146027028,
    382649232934,1911710495339,397758970104,1823517743332,1064902015827,1568724136123,
    1537226791036,1189725039584,1906243764679,852625813169,2181192697544,676608755364,
    2297482966271,683836824345,2004857712426,189256563516,2215627635387,540284136192,
    4587917600186,2896233553500,3257263254281,8239141307011,12045329649825,17001375605129,
    16726608586157,3569808293114,54973257723118,137574396327884,244906227207140,369747814165690,
    502250392336232,625384479166142,717353311608424,761168813657180,752583634924098,
    699769460104598,616727036398574,516947017626166,411174886845542,308203845865570,
    215689809200808,139539365115390,82641141394946,44358202075144,21328589634538,9040609708902,
    3290498511794,975145079292,202208731532,7109561152,17764400751,10200484309,3557173661,
    876767135,145915545,11878381],
   [768932]]
private def pvm_c0_10 : List ℤ := pzigCat
  [
   [2820561781,598014567,1729013880,2597299693,798022925,3191014268,4631854573,3189477110,
    1066277709,6634924,780897,1804309115,2359488284,467958309,321997113,2518216684,362553056,
    673612402,1490330566,669741561,2139935771,722303909,1286898720,369625285,2630469348,933356624,
    42477188,3796300313,1586197584,176886139,1294007336,3287541573,4190047788,515298887,
    4317866735,1165562104,3708344988,1017698690,2120278393,457999529,3224528128,1714778219,
    3272958127,3826596688,419027609,976207585,286445586,286269446,299139310,3643908179,1605113546,
    288002920,2743477893,976372089,2821452363,2467215061,6135037646,2748427449,699213328,
    1455845589,3731856655,2435803202,930757419,3523707227,448976997,4300286254,923682845,
    2364712794,2080602722,1421509595,1521325503,2878479886,6984677099,3113919588,4661827325,
    4514126199,920049968,11951239161,1169356642,519108757,3032275340,3895320045,36085223,
    805605077,5587166390,7513050257,8717978876,6612949067,1541692577,1509744769,9143215614,
    4480405963,4930408616,2579054731,1117325263,173937403,2255621242,1786096697,66713203,
    3033672259,2497762095,2521755045,2228911110,396122350,11021704951,6802639920,3257812744,
    5988301313,4275759139,4091292082,5772962327,428938445,2043258342,876676954,2666874508,
    8033688363,6077554821,2653745578,1831688683,2325529427,5074775066,3277540211,1690823150,
    5560901223,569614452,6971923262,3246292506,5444132039],
   [3809708684,8082742998,6453524679,2642166295,1977384940,1332757211,5594386839,322157026,
    7078097825,3064146837,8564415924,5672591294,5206678374,422506478,2418808904,1408567243,
    11445189763,4926544138,637456009,5045948427,3410063320,7242714686,1582948366,523288045,
    11798677113,611897772,2446074739,1640552418,11272823120,1197393053,6338850647,3212506496,
    571664039,3988705185,6662967963,5026607479,934070142,3788122166,10206522988,975358865,
    17786458112,6470932891,892651633,8885017904,591614927,11514175525,6031356827,10048125537,
    6970247561,13020551845,3458945546,4249616356,10549525374,9553295466,13370375252,3685035750,
    10469958356,3226702556,5139134722,950576132,5537800293,4273849933,20161634393,14049456661,
    12395899959,19880128625,16284492139,10804275705,7840170654,15617952160,5583650704,15491860340,
    4422322690,7868455334,7627626139,6552174879,1884844219,11615805117,4333607725,3855754200,
    5188569130,4016345318,6638065980,3814377841,1439234629,1557702870,636569725,10103117219,
    4225314090,4260199209,5662614960,1859005862,1702424555,11750111403,10697333466,3632138559,
    1486235914,8178434360,1199564820,9106071844,4125375503,6657758697,50783967,10784085445,
    3414741144,5813625199,1739666905,11724509477,4961831777,15853129387,1457589165,9203266617,
    9597559440,8333868217,11601862884,509364277,6123155932,3597297159,7702119756,1993850494,
    5541661428,7071946336,3132001588,9035516594,7445097165,20308484366,7944712612,14000064772],
   [3334659880,9273334240,783771382,22313468846,2629305361,8598640730,5517326146,318631105,
    4654342026,4067361169,1306750577,17649863141,10706041439,19798967473,14363166639,8577258659,
    14648813391,2140356830,4619527613,28834469640,7015113826,7519174574,15642897632,4366555695,
    6366686588,19278673867,6307925666,20514964985,11100474442,2178384499,2000271040,8662128162,
    403439249,10438916918,2174408455,2413917354,2086460327,20241174090,10094340198,6834512088,
    11787844278,13303832721,11418101610,16137779133,40615756016,1218917004,40576554672,2026706823,
    32448339032,31314339239,48124375554,16589677458,12174862700,16527772678,20049550253,
    5486877892,25586811135,1253985463,20349931809,1580613023,1047998016,1744328951,14890715130,
    7478785667,1544182976,13207791730,23132007254,11679190485,7657553236,13441063138,19259194107,
    20921221528,27499641555,8754227033,33523118156,38462538575,9033071310,20888992628,4174530979,
    23018168746,29399679961,2996586179,24330535012,13003431643,18154549520,9527475575,16222216365,
    29265614648,26424773479,11953989007,8622870072,7743356349,1380457123,29215379726,36707151639,
    90553313440,63318630153,61371221870,132808930341,197941711164,297863153807,355306648090,
    479996371569,617512311900,768953165011,987802566656,1182592244331,1323088329050,1531716107373,
    1710725895406,1761918110089,1728376553304,1597109753221,1341542726600,975315244125,
    505770118446,56825729504,609196630229,1033193927626,1387734443311,1441161248076,1212171686239,
    763262851732,204522462103,448767807281,1052040219340,1381711324797,1348147588632],
   [936633518775,263813512880,480151809090,1119504501545,1314840301022,1146371514875,583075224938,
    243315134796,997984378695,1334410839584,1121551551771,422334950262,473539076650,1119742870461,
    1252001923250,815854007907,32042854205,910638978276,1316742854145,1001905047032,94835750219,
    894186515953,1296989847186,945111117159,53243202102,915766924342,1327717250199,890258987092,
    244485390834,1218802257865,1254263184660,446077404073,672840041051,1376139333852,
    1021421662703,194993034333,1278741035884,1257476309987,236087981850,988687023132,
    1404004200351,609377681390,827318583848,1481353572733,749901383652,719800319816,1491630634903,
    779858787096,706242883820,1480813643659,749191572972,809047983382,1555251439171,540764218490,
    1118860197502,1469906028891,116816007304,1369991732346,1243156522211,410715732665,
    1586514247698,798572005225,1101285784679,1578432583204,110472095462,1618562415381,
    950253764714,1070520630108,1632029428251,184646531431,1782023367030,743508253721,
    1474953670367,1481713693776,910063171710,1844433352743,138915115983,2000487172206,
    538658029581,1904008899387,1106188522160,1661263563992,1579691546341,1447630451235,
    1872491846576,1282392732722,1956880544295,1055133807261,1981171440840,583503923750,
    2781587910809,1151759297405,3652838516334,4383699982558,743316229032,2391077527413,
    5855099205275,14625907471315,25286413755371,23078393266951,6769293664152,69694911554508,
    164198541306568,286843944146808,429626007054772,574225929746636,694162101405570,
    766013441106626,779906836777592,740878759539412,662442125560702,559529487475170,
    445456606768846,332020009099820,229600349815172,145902491025950,84392547334472,43998016365600,
    20441537907606,8335564679174,2913362565982,835110754040,176261433306,16330989400,6272934487,
    3869635149,1146673145,210426645],
   [20644123]]
private def pvm_c0_11 : List ℤ := pzigCat
  [
   [2213028837,2591742491,1573144396,961060094,5043580791,4037823576,2080434061,632617865,
    852654366,1195379871,1905257182,1025105955,1712380641,1558411802,296822973,731239389,
    1195262814,812432288,370110946,849870024,3070438606,1151883129,245168407,1773258337,785713320,
    2766631281,2949952278,1008288438,3258572896,3478491103,1024006683,2828768930,2085195409,
    2061415717,2496818596,2122153176,1329932661,3793188823,246732116,5204880240,2428279367,
    598702291,3179155858,388396407,509450647,2027463575,2184368702,55796180,2194226579,1783234736,
    1798565968,3614442281,3033164412,3931074385,528087930,3166376178,3848357915,1513487767,
    2667301557,1725086573,1156274448,3898064428,3820931441,1345772321,1497493908,26820116,
    5222878941,3654805584,5907161997,1226546214,4068014704,4171391691,8077585660,4038143165,
    2357963204,84931947,263080596,5174393323,3733074282,4838658323,3098454924,14849625969,
    1111580444,2911712445,103469064,5308837407,6274434732,6450482695,390366607,3778469746,
    1986464552,2635313773,478513233,3321905273,325694788,2501341086,2138136158,1920306134,
    3725276061,5053815866,5185161815,940614392,5874485542,2107336615,9899330091,5370961372,
    1900174860,8025423597,432305105,1053346391,319932458,499069408,3068005309,252578686,
    2616716020,11084501455,1230162646,1773102682,2524153260,59791882,2868190867,3179291275,
    1426156721,4045260561,5403574283,8504933094,904318128,8138438743],
   [2035498161,6974887722,3145736363,2162886205,6472386584,325296357,3461860988,2371762626,
    2440181089,421976466,2468203645,6594945460,6784693323,9695923955,475593170,1030702105,
    4419613741,11538541734,4514306534,4753078624,1866488165,2001513905,4407924890,6737116707,
    7698602919,4362693426,200070424,4051440536,8037958296,3346152863,7271897959,8779327875,
    8108120432,4510172181,9338838254,5455255317,974241542,8528132122,4095469067,7713927311,
    3495206652,11290188651,4739320021,917865810,12724160640,1139902714,2979582574,4670994316,
    9534959770,1641612531,4303036270,1602396267,5934079659,6565063559,15106340903,6979317725,
    9593932519,539048642,8610132582,3595581472,11969194790,10822318912,4711853560,10072531304,
    3300529096,14682917782,4837757685,6079061349,5633853875,8248611927,12126812605,27479140787,
    19650539331,10342337649,7554816961,435123287,14609307692,9320791174,10382157464,7798043752,
    6259027394,7038484581,1679236900,14704755295,6536114991,1341785933,7309637176,3475857043,
    10078825324,1885902123,685530689,10262882446,9663020803,5246669683,51919542,1832909381,
    8467884956,8472876873,4297606244,3766307559,431349684,6521189249,6706275308,2991613217,
    14141484094,1827439321,10087070886,10968241091,3107687236,7879526705,591629839,3101512543,
    1332323066,7995448849,11689520915,4337367229,15325250951,48794120,13142124353,10094558758,
    4149217051,4443470296,1363265528,7709774446,9760743079,12936646096,1143272978,8391574318],
   [6769143240,7764004911,9466364690,8055062782,14457641856,3355257914,11040112284,7458640006,
    5792770688,15971334516,419983780,15550102936,3741893321,12588170042,2244237970,721551247,
    11614790702,24212106375,1027471317,21017557443,2122888697,32362770199,8794678743,7919220149,
    4502668155,14924618768,4079905126,17841068278,9103333782,12107331686,3106181893,1720207951,
    8294832551,10033973579,10676956678,21019287805,19467045650,13678611507,30530711924,
    21858701669,20663479452,20585459521,25889377590,16724045041,39032742670,3974786740,8250067601,
    22310751610,26250317241,10579572838,6233301304,36411689604,14404999686,8232524140,8561533486,
    5469607978,31190418184,15335459156,21926513754,9513202606,4061979772,10899330609,2432220031,
    10738813241,37486690501,22897127126,9082317219,12298231695,20856477088,28334763163,
    30223363594,15593234798,26172604649,37410208898,1172532502,2518484079,6586055120,20578059621,
    22721837094,10969000725,29437118921,21168686128,8768356977,22957207318,7213607406,21399051635,
    3196609879,38957712880,53976163245,73414835026,88772753621,116485485132,143296159301,
    197021279370,312687068869,423356713996,542017089455,639853526606,805209872213,1025798536950,
    1187937644625,1388175245214,1534386708471,1653182145568,1725194657451,1693713363536,
    1586110472443,1270571748036,902186355671,497232199996,24908663484,569606904531,999066314730,
    1312214421501,1410198593294,1249839152737,875928829912,321635731187,322338554813,878019931534,
    1224446065039,1357494364702,1153425654565,548869290136,166156039864,838467108697,
    1232566587486,1287487394843],
   [903410858896,223185445845,531225137873,1107622953274,1283031763401,979338693208,221198820063,
    651618258035,1159145775798,1216531718235,693911435764,140608477018,909335386975,1241730207616,
    980326595751,173956711736,774257895956,1283405594577,1051483873852,203673831551,757442092543,
    1256812646448,996294121089,149876228512,846838022148,1350937272139,893100243890,204210480438,
    1159766111525,1261949262092,459458747847,629137248587,1348066746070,1039390105149,
    179510366667,1236139623176,1252828286151,260652612820,941298398684,1382921195477,644655906034,
    754641461902,1465892371891,795003844094,639012360798,1431664805425,874962966594,583141471158,
    1442607891499,862848309828,633788961760,1512305668671,751206433218,892105251138,1528746164089,
    403836471500,1159805564366,1391083781313,6450214069,1443997968318,1140884542141,620752480233,
    1644348417020,539403315465,1333276786097,1403142896666,397363727282,1674584435371,
    696151399260,1350391346590,1490919792339,563103670295,1837312507724,369599966353,
    1727119225071,1177559567858,1258793541046,1714251936907,550541650681,2049220426208,
    99450215843,2065768362217,729487315978,1946219155524,1241928667969,1792248090601,
    1551978917246,1565867045630,1754479287633,1268169668917,2102301620640,1176930683074,
    2790144767419,2345536808771,2099293904502,3713415849672,1942007546772,1613255446042,
    1051789139486,7433749512311,23691694035339,34297818328127,22841420958377,20161681119826,
    98671681479814,214708143063776,363486693678546,525780081359594,670280351514676,
    767145868277402,801069598244520,773931128433534,698437439003780,590751540727482,
    467029742099030,342694114662858,231305836536564,142257602714188,78965569841768,39163689029498,
    17148107339404,6523336493478,2104120032710,551391002656,106838151252,10801444326,1459253419,
    863918543],
   [158125921]]
private def pvm_c0_12 : List ℤ := pzigCat
  [
   [1051296691,3196863161,2122657435,4903196110,4436421965,258005875,1315785178,1782845685,
    863714620,1024349761,1043319573,2133231080,231791795,1597722537,475831318,77723034,308636117,
    1112202217,2261010754,1151778405,976381904,141153851,4162665664,1241048375,1791362294,
    1411273911,339191772,1694560015,3107152221,3415346760,3436437694,1783496643,412964903,
    1782503542,126353621,1503134771,3630424259,3956555418,3602852804,4656416165,815237941,
    491722894,1418222458,1067421201,469579021,2768564450,1995258914,4439397443,4006518640,
    1489596651,1462666499,2533945316,3043576053,1804053000,1797087734,992019573,2533578961,
    1723091746,1632157543,1720129866,632003060,1427338655,8551393727,4243266654,343280385,
    3494591007,5977939178,7366747155,4956934388,2120946121,527821133,2446525665,1328017778,
    7363713953,6574263976,5085026375,6879054802,4750516855,5444630052,769085328,852334690,
    7560675069,6484411408,784012748,4517342277,2149507937,2436090049,8278742911,1876982681,
    486391244,2641993913,1085155159,4743715501,3591889806,2327471439,4859143456,309435208,
    4892318937,1713071673,3635037952,4508813181,1256880232,9819725142,5931995843,4180939037,
    5631604064,2519339626,2327315387,302579116,4598065743,6460548170,4262504067,4818254527,
    1440217478,1242161107,3984018811,1086751763,2860430786,395191121,751940108,8037923205,
    2786958407,3519352914,403903215,3810186001,5572270730,3958555664,12968928341],
   [3339003031,4055090810,3227651235,1199776436,3965230531,1979904290,2705878289,879562155,
    1835578594,2472424757,1695274309,12805353746,3415524481,2430230397,4013916500,754391030,
    2348982994,1797502285,2112531393,456803045,12142345769,5177418103,8348890242,763372735,
    5637643292,1065489550,10131803398,6781800369,6668006092,4863146725,9604122355,295660211,
    2069159498,4850960220,12220925264,11596744303,3043682267,55917710,420767422,6675016637,
    4900990406,1887479430,1059565048,1772772073,8655860512,582754894,12228299289,3820615151,
    5962524367,2109358964,342711356,1508492178,7920669172,1527623352,6087060164,8037789956,
    1529833653,9261551002,4526988483,2085041601,13686111545,11487376959,6052991643,11310032331,
    1052344772,5569731864,9407398300,5114963822,4308240798,10840388610,18205135170,1100455262,
    2645308662,3447397972,5045401306,11522959451,3720368425,21759405769,20282402041,21254681641,
    11473636071,12358883141,7964676616,7271591974,2595061062,19530287770,5827422724,2791272052,
    4530469638,17104787031,1629355231,7501905041,4992583268,5031431659,3062806264,920560902,
    14210619650,8234693289,4797272352,10377006817,5675567370,7478116437,5046256102,2128833037,
    1357924830,494465559,2434344357,3631435547,5821620937,10557049674,4385141679,14920491074,
    2231827883,7532568736,8915742877,62622561,3275832009,5067613880,11200910023,5824192852,
    8525562915,14113811279,2264422337,16048806369,1948066979,7405854697,1169408344,2355853296],
   [3930224856,1033541673,7615284803,15533565070,1056389265,11838229228,5139918115,2863733240,
    8030877402,2212895797,23695770938,8608637349,20939583092,588907267,15480804800,3106546624,
    15489132484,8313737106,5779298531,19244742938,4127957956,8232060968,2873075343,108947037,
    5869804615,8546690861,11397780559,30283207133,1015868101,35104689455,16635270728,22636071875,
    27356595632,9564793817,39521636970,11413570831,21651542380,17357477435,11691316066,7087456009,
    23727208079,23759364700,24993049265,17881034680,5549006906,2482882618,6726004299,238013392,
    8736686878,3981226273,24062436800,12112637626,10960875830,9668879443,10175047419,2997962884,
    18699338302,25743023928,2111223471,28649338758,4643762903,4325271712,51935220404,9403787033,
    29953176712,26714373656,13622033381,28766711494,32395804949,21174966237,20031398034,
    26510199313,1126564415,5472578439,6342447481,25573151960,27634405945,18987273384,19741054138,
    3292298334,7304040265,33734413282,55974858277,100581071916,124089619431,116831524490,
    179191042161,254556856908,331487949005,456579052718,594226650129,735826528124,870656867255,
    1033261881544,1229227798853,1432402728772,1563086103335,1641772286460,1674775944417,
    1641493935574,1500536288041,1210534645674,858549249345,391203677812,107069956198,547145874487,
    979835926808,1275007725067,1406277014108,1244633154459,864763893450,401223761935,224527075663,
    789863189758,1170923712249,1319595001976,1171502866893,716353507686,100530655591,583249359985,
    1139687599300,1320977659219,1063284070694,527631219869,148571786835,836186061178,
    1227165967399,1160679407236],
   [691954677601,75578205125,803537612336,1250855179855,1116464506650,497888622845,339719305719,
    985267872858,1196347214807,878298964900,76225421549,767506315451,1209803604854,1070464810831,
    268128256940,680470358920,1239709312045,1052513556708,276882825869,671297214133,1226991377560,
    1035602309265,187327313342,836550456706,1338300823941,889107287010,214437580092,1120404913493,
    1233535330780,485706067689,640772788243,1322948151572,1020860999955,163105026763,
    1232128862172,1221301913755,268690447304,902062695496,1372725416553,652900519374,698147566736,
    1445309399517,827454919336,568132183818,1391731451973,921332055674,451829775744,1398880938679,
    968701796152,488053867186,1444113087187,919649071814,665654374828,1523101851309,671897695454,
    931595602340,1465222104765,344544619542,1199054579430,1378076194701,136802220991,
    1537948528418,1024451006891,822401744563,1638125136998,304408883665,1441414127511,
    1274416020492,585858431538,1738954233803,468618318768,1550728234352,1337271547805,
    830433929973,1834922630622,83026407027,1851830878289,947238932802,1460382744938,1615694799263,
    829564723723,2044995120922,191836632656,2128889587059,488523752610,2088290526500,
    1019861531877,1928005909463,1395928581038,1657770631948,1762297190267,1448278145269,
    2223772246592,1693477663948,2435772328433,2668697301381,967836527654,2073267952422,
    950597426570,3210474003292,6461387441178,519604516668,17392865104905,35863460630691,
    38744418357391,14052352973017,47859278973490,155852929886138,309186395748902,487345640165756,
    653532970837666,771491542321798,821018437032904,801240844612502,724217479003138,
    607745346767302,471720456161848,336105441602210,217826842812078,127175450961564,
    66217364222030,30401721470224,12135589717826,4130732131554,1164054542394,258199165812,
    40609795818,3259741564],
   [158503407]]
private def pvm_c0_13 : List ℤ := pzigCat
  [
   [172914965,1039921549,6438781229,3436552624,848206656,3051523709,703110256,646297741,804984267,
    1272259766,1228769805,1737405373,1366750866,492903658,48273210,1844823693,1995029108,
    1669646709,533638948,1854756535,3000059586,2030586079,450319318,314707520,1166424036,
    2777957906,629702935,518800756,3030281598,1849909205,4545336875,855617536,1334930070,
    2162661724,902611255,1389191575,5584674062,1030874733,4179555909,1027448487,2895218022,
    1451712954,333068811,4155147167,4389789440,1768627931,3268236219,4023195900,1453464725,
    1422078954,1207208492,400286243,972772339,3184482714,2764385585,345748963,385933951,
    3153979036,3032682255,3051462962,750364958,9150834823,9060848902,2923717495,2456913802,
    2712165361,1986683135,4796919311,5684704116,7970508997,6437115410,5641522661,3836709612,
    3116225817,2714304498,2364995679,617772632,6545019699,2015610622,1798603722,4870769785,
    283275391,7472918104,22314629,2792075211,3233500346,2743142645,2829934176,1612566233,
    3859548830,4201810835,5848745555,2973894141,2633220641,4107026749,981690556,2034216895,
    9530597083,4631671446,3058631206,4541635169,2365150140,5689047608,9862950243,246729083,
    50831779,4380131750,2226980592,5603038311,1141618396,4841159516,279182440,4020168805,
    4123214196,595759899,494705709,880798795,1820666485,422050650,869804283,5715319079,5133585675,
    8049791996,1417537076,9831722793,5689667112,2550611981,5762356761],
   [4266661731,3984497908,4875319230,818571547,5782956167,2649888604,8022733711,28728987,
    4209827884,7868257545,465038783,4096068336,2729447739,2821480825,3830564525,1883798522,
    7777074162,7279557387,7341110102,797379153,3164180596,6194160195,10648995492,2691419248,
    6825315075,1945328281,5189199609,10115750837,7069002926,5006692583,5091689110,3521767706,
    3539510158,4155167254,8878780696,9687947919,9886201997,944714827,6473335276,2993805762,
    2415640385,8307239848,5203118607,5843452333,1257685930,576632181,273743919,4842505157,
    970652928,11618216626,2727538633,5898448656,7587402087,4773383961,4212708535,5098474039,
    1784966890,3494949347,6025164528,4220443704,1928947754,4463787562,9443388406,4348515882,
    5664975012,5653765089,208228698,11321349809,13567519193,17240417247,7255956784,3433507281,
    1226160183,2506639834,11821930910,6380269912,12075888032,10598804734,633256131,13677531354,
    4785000750,4486010535,8394228882,20130294025,13357958781,25184952021,16675098635,17919545809,
    1500253009,8108882503,11552405372,1609734592,24157738396,2933257882,3985079044,8293985057,
    899805340,4940290495,7553102161,2486319101,1203820721,8192475442,1550516705,11711973158,
    10726478481,7613326730,7422469523,1462343028,5388381297,5816892460,2420741647,4837843766,
    8622374767,1495919016,3635891595,9633416983,15040948718,591037211,7439122668,2648996622,
    291454635,1338001623,3688322455,4344543776,6872873077,8974703676,14310139005,1344220751],
   [6106146889,16079903255,3862384939,19806221727,17493466192,14472175375,8310740324,9376303657,
    3323497998,4103500314,6017461314,7353987082,8716554947,13699446726,4564340537,5521284578,
    10645027288,7144211346,4193047438,3357702588,22614816868,4884959565,27844365554,19548173845,
    33235506460,11951202923,29937405924,15111935279,25281115960,16515177311,16870380440,
    13708508361,12106193095,9324531287,35791045689,10468090254,41125114637,3634555010,6982179978,
    2380627238,14913047736,12206400800,11051099266,5662072781,14036179852,11845571483,10168381861,
    3206514167,1311142636,4834547164,897456181,12112430154,11634701957,6175320624,10729092375,
    310404670,48552202686,12998217055,13261945688,6091054516,37829980553,34940766054,4986204354,
    6139676412,31317281206,18828260775,26087323356,23567743948,8289689077,40051718918,10659652488,
    39514186958,1375478205,3936483739,11224447901,37081058726,94802060123,101201132964,
    140990814461,168622545126,223631357663,279720678766,379896536669,531984476918,652766519023,
    799720822458,944020464071,1128862756930,1268528243905,1430586073330,1595865192577,
    1658686085122,1645247982037,1550092226080,1381308469195,1129876773388,747039828739,
    281469294816,196709279492,632165905311,1009800431032,1258047924779,1341072117834,
    1212858541093,888815775480,371947990521,235833901999,730183904806,1120278480877,1296841433602,
    1185182884301,793313491850,179504271231,412355066721,973815503348,1284946383903,1173689369094,
    758288723585,72399752146,623346714874,1076574011769,1182423975230,948164838167,337973328422,
    439418830056,1034064103301,1204265229900,924471524061],
   [243655593384,579394750324,1115040092473,1146658307030,663369206085,116876090685,826752208246,
    1205759707909,955673019630,209495238107,693460895339,1195968779474,1068713632257,327179473626,
    643220906804,1185543069971,1041271811734,325630906193,642846295375,1215792025006,
    1056646832233,165003043828,852144952218,1321987671951,844134797440,229685363594,1106206571047,
    1205370850122,469777295785,645190916535,1334996770080,972673850407,184586905081,1203335113006,
    1216389948651,241674973298,879093591702,1343208021327,673764742274,681046528934,1414431809013,
    844648165478,501433112898,1362435712995,950698491744,340343245596,1343091645911,1051733473906,
    332675586302,1393794189959,1033316752322,444400773668,1464822423843,907323086856,686176928456,
    1473183183343,655662490322,919056248574,1478644053011,326258987156,1286603657538,
    1367329277585,265579155517,1589768918324,919757630453,939560896335,1606499966518,187929655629,
    1500036132647,1240936984240,733521450684,1792691873603,295609008502,1649187046696,
    1243394692173,972235127875,1832553030404,66848506954,1905505622209,854655252358,1560345168592,
    1595522170955,967575196755,2045136302094,293861873988,2155745823855,437835316434,
    2133280314130,997933662463,1921968291947,1469152849520,1644809569458,1937620435353,
    1550764187993,2305591956840,1870600420118,2059785454445,2183012239343,679293260968,
    300151111030,1243745098545,3015424031876,9902399110784,7196686295022,9913379012945,
    32311115621421,45854841986605,37294461850695,9354634314508,111053886798760,270919284984308,
    465523190277354,651263411206758,785520157160438,844022035705002,823913255007180,
    737486485153306,605718400023130,454119632610676,308188938028576,187491685771424,
    101175577080308,47854030522090,19549615691328,6762827861444,1923911129648,429181744024,
    68694046558],
   [6364367352]]
private def pvm_c0_14 : List ℤ := pzigCat
  [
   [457664245,2529442872,6303149129,2871483617,2949004204,634685099,1276198563,452434188,
    1363507159,965230935,1690831868,866372575,757322851,2157756877,2718520268,1309144221,
    1066465602,2098017875,2492779564,1462050949,1060490559,694730528,451645987,959362848,
    528663645,1830850493,1814185410,2826948394,2085624453,1583632146,3330301912,743016106,
    80925130,5489436581,371826034,3099021188,876083373,2809140747,3607259566,1674823812,
    2986365798,4725557841,3246562799,5812483632,2380174179,200973023,1363655892,35020616,
    2086546771,1929558940,3261009035,1335011738,460819198,2177302278,2294579167,632983926,
    5964948160,8602025383,7694860032,4270799051,1300681991,629721444,5506662256,5715208079,
    5808894912,9469223367,6028573652,1182381069,3425976124,3046031157,585444760,4111265115,
    843567700,2733939209,585816415,1677275794,2950487323,1900178647,5108936496,851946920,
    8087552407,4461432650,1806391711,1228803913,4846996469,932862994,1826581678,148380188,
    1948075144,2414571104,2129493443,2564895037,6161919490,1587318471,562013256,3146301092,
    5441459703,10547688865,6782917366,4879814879,6450190641,16099280,3436570027,2171233185,
    3241006027,2115160292,4488588842,1729935822,9027865579,542209761,4327581832,1245524117,
    1191864115,261006224,1575896392,312740614,1287705330,918956427,923929793,8768497442,
    8576553507,1375999825,7303944488,292981201,7831181459,1010537457,1054382821,1605763536],
   [6795471045,3337350786,6336655324,8337624839,2621385557,1366192773,5914442887,4707112872,
    5014357370,5185770059,1511296642,7210360595,7442116766,8589297373,2182025971,1715729771,
    5910530000,4057063705,5896463557,3170994590,568839193,9406688069,11517494500,2321998503,
    1527479586,68073448,646425765,1028626492,9209067508,845208005,736114848,1121557281,9511487959,
    3465902539,1759586395,2673702076,8659215253,846262688,15851177868,4535912784,833892461,
    588773073,7148371219,489204372,7849676293,10781097742,3081461962,3218534747,1271873098,
    2395016003,3529710596,5286253275,2908854179,2866651603,316145536,4967997332,7829996698,
    3007191583,3469216496,5889151175,1699786751,9776158135,320170648,3835179551,6571365368,
    5906687573,3417857840,8975266968,5269147636,487388136,9965317728,13125209226,8219527157,
    7217459689,7228379187,19076523325,5935428106,15621395979,1211290835,498548141,7481120492,
    1632391062,16789817816,389894920,15611627654,704436839,16173811456,3256621524,8013517370,
    3342673011,11979502633,19444107735,20992646909,11946999433,22484847757,8121292351,9545562005,
    19257146158,1621452590,15919916994,1849927306,6255072428,2640445007,546518780,12637262457,
    1422450663,3624319301,1552331068,7031961224,5703623325,13739541456,6192475071,2850024371,
    2445470636,4949219425,1358090928,1194541105,9367368596,10038198795,3846282120,10648879815,
    2831014467,7475602842,7546133335,19848679410,9318037309,15042559932,14471461393],
   [8459730256,93006232,3415853523,1380078292,2926368855,5677541290,16796848867,3689676933,
    17673878401,7177519449,4105286218,9030568893,1565462177,9588812863,15111174592,20679136193,
    30914332718,20180066033,24348427854,23079592211,23588220100,10954351411,22360747422,
    12886900987,14663009588,9660661140,2287259456,25134502944,15772400247,30614987276,8890023653,
    17864961096,13947456984,7520635305,17759361034,7920361812,3048868188,9277887683,6584600122,
    19591669925,18426892579,13423213533,25137050191,10243317763,5174554085,13502420088,4170272823,
    17104840630,16055305828,3205632211,22449451230,27050375113,3653622734,10134780662,38102362453,
    33631728290,1942788208,12375997571,20049730244,34170669769,6461214746,24822538358,3529695719,
    41662955180,23428616275,1762089588,6039488373,24596260408,20695382283,59217356222,80348118073,
    154343786144,172202644877,214072926756,240222241737,371830148126,430887240259,602456323114,
    719128322451,897608649592,1043321740699,1174096465374,1342264565551,1478989930086,
    1598036905305,1622635883560,1613060741523,1488253696324,1249391874233,953289444692,
    592618069187,175964228816,328599006020,744453907811,1076497860880,1262038356285,1282542192820,
    1151905547713,810721796758,313103243693,241810266711,763351958112,1134800914675,1270998268450,
    1137446401419,788460650454,260853032405,359782385777,923058376970,1203734855289,1181079718378,
    866430254189,259612861048,425639699358,993910006285,1196515372984,1023563890539,563171060146,
    147487486286,757745888129,1140890066004,1136555577695,608147752334,152770454756,825527899887,
    1157502712400,1032253984347,413796074552],
   [394628792564,993831166231,1129029309586,778143718625,31250326208,767340597018,1192884604377,
    1002040091312,234049095287,655012771987,1170564160792,1057860465435,312128475092,595683472300,
    1172558662695,1027542103906,323362066603,637909392203,1253585857478,1019851219045,
    111229728800,885462025658,1297257751087,774263040140,251415355426,1112166681125,1174700341988,
    436277428051,684028542977,1330826491836,927487819947,235115839111,1188604886236,1176811508569,
    238886909922,893226779808,1315378142433,658702770980,644273341306,1413050876993,840871141202,
    456707465726,1311305179145,995013749766,257823255404,1282194326369,1111411858346,178673131270,
    1335784729503,1129725188516,244681845972,1380049767357,1075397627510,404295098896,
    1439274234831,914111959404,615853640600,1472341298499,726030660380,938671055952,1532906006159,
    300812909658,1345202535876,1345040639665,308581530803,1598006243628,900358032671,960300151885,
    1624466381348,187913862365,1561769902115,1267153691932,817146816660,1814414790993,
    253383389164,1664031538936,1266766427471,993522731939,1867299092746,52335945494,1927191742807,
    921852649808,1568974821188,1671841709367,934938998825,2085220601938,174730959322,
    2172640361243,609990613578,2093200022860,1208449750457,1792343966659,1753319474272,
    1503184476380,2212314141555,1428740274919,2377143405606,1543584699938,1883472553785,
    1070223483537,1156330556782,1320409804897,3808728185399,2010526452982,11747461885406,
    11940294339006,2985999699863,26639096804241,48546197396327,54352584378251,19897533221881,
    80873674394506,253017654930828,466919285369178,670342289405918,814517964889450,
    872113249269520,839608665628006,731937037396864,576754709161580,407947768131826,
    256522082880428,141783877723890,67962974206288,27771123371714,9442398465156,2572321451550,
    524600810434],
   [68264101014]]
private def pvm_c0_15 : List ℤ := pzigCat
  [
   [1826381151,4206932184,1047730161,6232775877,1507321739,1402918792,708863307,554411439,
    998650124,2174346005,186381607,1226848611,2944899800,2577819285,151127822,2240476197,
    2042294320,107897147,1527790393,1300219562,19633683,286688249,19833219,1263085539,633836831,
    2959022668,1529586937,2704926175,2520424054,258262387,1379474030,1134913503,203149430,
    4062839906,4614669482,4811643787,945822479,24039655,275573000,1819571774,6471105629,
    2767509280,5522273848,246873910,3350009275,2362703640,2721438003,1259338920,219108843,
    456297640,366988236,1654726537,5928033890,10338949547,6396474432,1506564377,931269289,
    798584455,6351321760,8515463635,8902330018,4191928433,3639366136,3463274463,240323915,
    1321584015,4885532384,817233499,506042789,1766698515,1702395127,2649002188,1086892392,
    723308155,355217002,2485024134,9253141829,3703686424,688907176,3590746653,3476785145,
    1804153070,2607589698,2149044863,1441873067,1152636854,1906171536,5441099273,1125546774,
    1963819547,4565031233,271280754,7338759888,6021425793,3724686254,4008176922,8088633375,
    2723628076,5844593460,1806139590,3292341619,731415637,2718001841,659534467,5012594455,
    4131939613,2737680416,4957733951,8958929809,1662777819,4616066072,2297147654,4373626295,
    2612256580,5982160239,3501478204,872971310,6051799249,1714173528,7114552550,7050934759,
    87763797,3670037108,3877182486,1732201901,6570808707,7492061780,3170638278],
   [6746987685,2605380932,2552861958,9745941561,3719638330,8142539989,5302810888,2098842611,
    5146949120,3630896457,6556707291,4568354503,2711589104,2285426440,1817704437,6245053331,
    12874909832,8305298651,4621827701,1638504924,2032642583,4463565869,4013012232,2650955345,
    1568759569,331103937,7815705621,3010925130,1476433910,2131230712,2016836621,334241577,
    2731274980,3370704207,5907654048,13312163006,8485452171,608596783,3957710043,3544499046,
    6496546991,12308417123,3108057276,1281843985,6367555702,6993273970,7324862620,1502248887,
    6362962283,5081870995,4777974054,3066392375,6163566636,3731011475,3405511162,884548111,
    5969195932,7653250617,1624480383,6001162155,984715894,3652091136,859369088,4734289448,
    5283856100,468887551,10558776317,2181068775,6769258406,19478206129,8540338802,4217894505,
    4015386466,503961985,3738535968,742132417,22766447762,136491094,9256600178,8981187847,
    706619191,11110322453,8260949863,7874492657,9678477845,2479097863,3439629433,10327995616,
    1144645049,15843033460,1067978737,14060521426,289946252,20300779366,9619315986,3414641030,
    8174387911,3411416803,17338092333,17820573545,21976719321,23979480499,1618513299,8610455799,
    11892341138,4325796850,6053547064,16447748064,2836074679,1614031566,7344196537,1018181916,
    13651587611,4451021984,2440716632,4496462615,15064550392,12456800205,15724673738,16421354217,
    7302440946,7235585063,5804385586,4363810220,6006601623,5020655816,10711034265,620632893],
   [9257198075,10940598294,3223702894,2557423479,11056419634,6741810469,11045598102,13024014993,
    16034714476,24612817607,34882729852,25231769123,12914028068,28797715939,8636319458,
    23519617767,6310815212,11924721745,4057412633,307090672,19353081573,25945675246,17355448153,
    18563485376,10847516899,2192140476,15376382910,10858747875,13006508082,1329331043,4623375546,
    8150911976,17866772720,3451847555,7006186254,20793959404,1775612295,12133552440,6193165284,
    13526971534,2389040886,12846500524,12805876902,13947425235,20700680790,18867930289,
    16780625121,4465290829,49103791785,13464149856,15938082711,25427865901,38553973314,
    10216705519,10935796890,29094401338,22087836329,29982655068,30755848079,3821727742,
    12953787335,31159250060,37935325203,81304536956,133706625479,151649255008,210083596045,
    286014925066,308707464339,408316182986,526270933897,680509552356,830329098907,977716055254,
    1118437656001,1287943567798,1391543575549,1510951568198,1582524588933,1621222160060,
    1517655182977,1385585630018,1085905382195,808903900460,375616020463,30868800547,453140247082,
    841684745569,1146187810684,1306401057181,1227845159034,1030761503053,682845656896,
    220149706915,323338301375,819173962868,1145788900635,1269085642034,1095147227573,743760946322,
    210053249715,370163425151,857479401640,1173513925649,1196735088348,884557542409,317982682950,
    322904701152,859918467713,1173529748064,1122430586621,680349847660,20772772095,590214771875,
    1031300395146,1131339093309,829384882904,204243010857,539668512869,1044803550374,
    1160302665355,755450692012,20933605197,641119116297,1105879185756,1069141332273,502048196324,
    266508541022],
   [904588221759,1133738754666,847921913041,78137832822,759433760866,1194613438543,971353216582,
    227499014961,651318849491,1151250004572,1016679040847,304036310618,614160476600,1156086341795,
    1027206586074,279927007805,701890313629,1254704944080,982538138549,3479885582,914735395386,
    1250000266523,723043642710,315738161284,1110820417637,1156666588410,374637151649,746242725415,
    1315317802572,872105437955,299688510359,1176140051246,1139447127971,210094398218,893446674128,
    1311407804583,629078414490,640307921996,1377217043179,860973257100,434105652964,1274502434831,
    1002705281958,153898012654,1240234493727,1160070928506,53621494770,1245620599125,
    1223931121734,63309968298,1279662846531,1193149676816,128895084278,1339229845781,
    1127102448742,291199166622,1401896617783,1022342976308,522945768444,1540606298267,
    799573890708,943183122508,1557220142071,339085142812,1317389696354,1377583673501,227081652417,
    1603152228614,992973101229,907937874173,1701378611064,276816567229,1588219978475,
    1341006114056,760883772044,1830978133599,392299830252,1620827444426,1414322606889,
    879523684837,1939995962988,148497790475,1909313559163,1148740994744,1445547417724,
    1841817083957,683063591297,2157720156690,190360892579,2141318822143,1013673448672,
    1912590618814,1628072231771,1471160440189,2166860492392,1111424274296,2490696045609,
    910173602437,2411176657998,628484433540,1867242958015,554694557474,1997644230970,
    2908992746349,6137883234473,1060808911888,12493627992696,14919638097432,3119217665904,
    20654161511971,50894885608091,69987943131941,42107536385649,67660165979570,261610908633246,
    499012070935652,717058533757292,861157725644870,902166443896672,838981252757338,
    694891324144020,510136742895748,328848319907476,183833869989754,87693565261252,34905952285688,
    11199043746186,2721000960548],
   [431143486658]]
private def pvm_c0_16 : List ℤ := pzigCat
  [
   [3152402163,2332409808,3902917204,2252356461,5156525741,1914739021,680240010,1836830463,
    1253924784,1115602263,1743519690,3733875819,670779706,685656175,1550834048,171785665,
    2823945637,485329604,463763700,786853983,113282911,545065532,1095093931,1605821832,905709028,
    4197743937,1687764454,808699952,122468856,1217304105,577536703,1325577923,4409193756,
    1544251479,3915510413,3894982562,1231107326,5430446364,1115243065,3679260397,645351306,
    5185614816,5733048949,2010971581,851003304,1322749812,3753642142,3091532171,6365795486,
    8718231411,6065566490,1730592367,1496372085,1761505403,8871407396,9889309011,6968920730,
    3759674457,227165488,1449912317,1925238946,1583425415,1620451838,1406635319,644440664,
    3681676850,317070651,795521395,2259375391,393125396,581692645,7000059734,5720447241,226669186,
    1974848052,3322412329,743025545,4062789748,2589166574,4108066947,1013293679,429874530,
    2600483264,6332365163,1622392669,1417547320,225477904,5071003287,5708798286,1870388615,
    4874859789,8210243002,3428593497,4980044267,671215888,637840621,5918581879,2778119574,
    4233799316,119786997,1396900913,3596346055,3400756612,4758016232,2019778409,1500045178,
    1540558740,2104740280,10888528705,1140556044,2083684100,3960729045,4075804993,5302495179,
    8720322607,6554353722,163568722,5901841345,2789790970,958095972,358339249,5700096403,
    484471013,6940352472,1708634295,11422976483,12881983168,4078814363],
   [2652663950,2768477081,3001854744,659316619,301778240,1293456202,1735806088,1729049347,
    3142613328,7189554453,1377871908,10507831901,5409380416,8806131598,6541352573,6679937581,
    4854535584,4701621009,5540834311,3821924048,3275752147,3907505078,800814043,1582469241,
    486997881,2998260917,2334751685,2428020573,669156136,6058017230,12324265887,3212556312,
    2433207885,4744902291,2759483694,1476290566,5255759798,11022926639,927406589,8109585722,
    5514966902,1379106025,2938298632,577201202,4875982940,8115086693,1613702034,10183086553,
    5460313959,5760091957,9378761392,4406177748,8762215738,348338135,4534897561,256508511,
    1082970215,1101355588,1055275299,1618829321,3880475736,1144635128,9834846668,17114598301,
    10762454690,6995674901,7811226755,1125066035,12109611842,5344444499,12140531820,8427089259,
    6689667886,4237637667,4690212777,7239070637,1316367963,4293742902,6561503091,112355882,
    5592846873,12983841426,784944176,19207045750,808879887,9233118432,6429960595,566576636,
    9795746681,8831161721,10768923325,4920560913,9682147915,146614327,12221701796,3279690685,
    9083610680,1817492985,13763279064,16327184902,4996935398,16268321488,2180777265,6307902612,
    8632019851,13198119623,27670979963,18644180497,10122487573,25315604741,13483266956,
    11822792893,20675033906,727588509,13819630928,2208958912,4239389551,1034650714,12101614817,
    4649557538,8784219225,5371463138,1337357068,5663759772,1891409156,10329507893,11836944262,
    16048498305],
   [13901540406,12070059307,26069703024,29900955765,23104546328,30511079181,16219539844,
    11845935157,12359907856,10442747107,13503680344,5801794456,9166404861,11142343968,19566405935,
    26955823990,15089546651,12399693486,2539417891,16385746681,3218908820,20540814777,6039896792,
    9921632963,12506654591,6902245303,3166462456,4845752687,688756636,8928697954,14004924243,
    13467170950,4669911288,2077579849,1347437159,5140631004,14157597688,10979017659,23636883968,
    702865370,860114049,32267208362,18154513029,24064763434,9620748046,10854644611,40968977452,
    13846272941,2863536910,42274435402,33031013653,25427338034,32433607775,2151595734,42267243629,
    19083663448,84797628549,106741814230,159310975367,212510294114,248415550475,337580439968,
    389543609077,495234893174,629246299763,758502048628,929421982405,1105425865518,1218207143435,
    1330717228342,1468805633847,1538348102792,1564814573207,1546656197968,1419149613739,
    1237836901936,924530447031,558663523342,169357948685,230342160079,643473629738,961241203411,
    1199568163470,1267654273677,1190872141104,910499875349,522294017428,3458990769,414474426643,
    889401585502,1163855302205,1262448299548,1042653927869,637862625880,125676533535,437027195727,
    880695065066,1157138949119,1144339033018,866065477995,336291958588,289403827644,829571788535,
    1158764375482,1093595462613,747639844606,164579127241,490009146641,983554813500,1131024226271,
    885304039484,370763198311,274753500521,875722493314,1156542552717,956145900948,363817900897,
    366367089617,955186546246,1117154457161,818562384020,162468121789,560126777693,1044713148504,
    1088489835009,547525900140,212894782154,856296542191],
   [1176193970938,846927093871,45578845930,783867157744,1171629599007,918582025410,192036633851,
    664670244819,1143189906774,985787077207,249600493090,646934353228,1184529329729,992393611752,
    190025654821,778910913517,1266316856200,876773380755,81363296331,960854011496,1202624010309,
    645310863516,361350434612,1161801975787,1105478655716,293393788999,807936160945,1314507710128,
    775863237515,346937732905,1179298688172,1097719622141,168643813004,898076612804,1310566264801,
    592130004104,645750387920,1354800270795,848173746070,389407624322,1254138939403,1016976405580,
    89200884980,1164218361025,1221278415416,63835457727,1173875101715,1267521162458,129539858153,
    1167284511853,1287130816780,110150110347,1175540930905,1286289293970,40123757583,
    1260151307261,1242983243068,105762004822,1402888251147,1175589946448,428331266664,
    1569512938949,894327513398,827389222626,1578045742125,508935371842,1216527549744,
    1494171265615,32945892225,1599794125198,1176842025839,766516888607,1787798876794,473238234887,
    1504688179527,1491884203242,514051765060,1858649738329,706931962802,1488836703092,
    1652210975813,579946088699,2008846462728,550338572349,1783273417943,1510881247434,
    1105715943198,2057313920855,159324383737,2176613200112,804360636147,1936675864385,
    1605412414762,1458241145372,2145537297655,820970399075,2530658611796,320654229342,
    2570712799659,115710270960,2193382307734,858395212815,1661489939127,2602463559394,
    2579360193436,4655653036843,7715092492823,573677881414,12375768863708,17015892205212,
    9225063493540,16016701623217,57538907612663,88279262780251,56428131994877,78055608832532,
    306365074002340,570709897849582,795831037735488,921535339346186,920053363987766,
    801155105390572,607456088619226,397478395167508,221242276867350,102575244404240,
    38327432342704,10869929595074],
   [2022497519638]]
private theorem pchk_c0_s0 : rkmAllTrueF [
    muxIntListEq rkmHbHi_m512_r512_s3_c1 phbv_g0,
    bWalkChk 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1 pvm_c0_1
  ] = true := by decide +kernel
private theorem pchk_c0_s1 : bWalkChk 5 513 phbv_g0
    pvm_c0_1 pvm_c0_2 = true := by decide +kernel
private theorem pchk_c0_s2 : bWalkChk 5 513 phbv_g0
    pvm_c0_2 pvm_c0_3 = true := by decide +kernel
private theorem pchk_c0_s3 : bWalkChk 5 513 phbv_g0
    pvm_c0_3 pvm_c0_4 = true := by decide +kernel
private theorem pchk_c0_s4 : bWalkChk 5 513 phbv_g0
    pvm_c0_4 pvm_c0_5 = true := by decide +kernel
private theorem pchk_c0_s5 : bWalkChk 5 513 phbv_g0
    pvm_c0_5 pvm_c0_6 = true := by decide +kernel
private theorem pchk_c0_s6 : bWalkChk 5 513 phbv_g0
    pvm_c0_6 pvm_c0_7 = true := by decide +kernel
private theorem pchk_c0_s7 : bWalkChk 5 513 phbv_g0
    pvm_c0_7 pvm_c0_8 = true := by decide +kernel
private theorem pchk_c0_s8 : bWalkChk 5 513 phbv_g0
    pvm_c0_8 pvm_c0_9 = true := by decide +kernel
private theorem pchk_c0_s9 : bWalkChk 5 513 phbv_g0
    pvm_c0_9 pvm_c0_10 = true := by decide +kernel
private theorem pchk_c0_s10 : bWalkChk 5 513 phbv_g0
    pvm_c0_10 pvm_c0_11 = true := by decide +kernel
private theorem pchk_c0_s11 : bWalkChk 5 513 phbv_g0
    pvm_c0_11 pvm_c0_12 = true := by decide +kernel
private theorem pchk_c0_s12 : bWalkChk 5 513 phbv_g0
    pvm_c0_12 pvm_c0_13 = true := by decide +kernel
private theorem pchk_c0_s13 : bWalkChk 5 513 phbv_g0
    pvm_c0_13 pvm_c0_14 = true := by decide +kernel
private theorem pchk_c0_s14 : bWalkChk 5 513 phbv_g0
    pvm_c0_14 pvm_c0_15 = true := by decide +kernel
private theorem pchk_c0_s15 : bWalkChk 5 513 phbv_g0
    pvm_c0_15 pvm_c0_16 = true := by decide +kernel
private theorem pchk_c0_s16 : bWalkChk 5 513 phbv_g0
    pvm_c0_16 rkmVoHi_m512_r512_s3_c1 = true := by decide +kernel
private theorem pacc_c0_s1 : muxFastIterFullT16 10 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_2 :=
  (muxFastIterFullT16_add 5 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      (bWalkChk_sound (rkmHd (rkmTl pchk_c0_s0)))).trans (bWalkChk_sound pchk_c0_s1))
private theorem pacc_c0_s2 : muxFastIterFullT16 15 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_3 :=
  (muxFastIterFullT16_add 10 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s1).trans (bWalkChk_sound pchk_c0_s2))
private theorem pacc_c0_s3 : muxFastIterFullT16 20 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_4 :=
  (muxFastIterFullT16_add 15 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s2).trans (bWalkChk_sound pchk_c0_s3))
private theorem pacc_c0_s4 : muxFastIterFullT16 25 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_5 :=
  (muxFastIterFullT16_add 20 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s3).trans (bWalkChk_sound pchk_c0_s4))
private theorem pacc_c0_s5 : muxFastIterFullT16 30 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_6 :=
  (muxFastIterFullT16_add 25 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s4).trans (bWalkChk_sound pchk_c0_s5))
private theorem pacc_c0_s6 : muxFastIterFullT16 35 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_7 :=
  (muxFastIterFullT16_add 30 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s5).trans (bWalkChk_sound pchk_c0_s6))
private theorem pacc_c0_s7 : muxFastIterFullT16 40 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_8 :=
  (muxFastIterFullT16_add 35 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s6).trans (bWalkChk_sound pchk_c0_s7))
private theorem pacc_c0_s8 : muxFastIterFullT16 45 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_9 :=
  (muxFastIterFullT16_add 40 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s7).trans (bWalkChk_sound pchk_c0_s8))
private theorem pacc_c0_s9 : muxFastIterFullT16 50 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_10 :=
  (muxFastIterFullT16_add 45 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s8).trans (bWalkChk_sound pchk_c0_s9))
private theorem pacc_c0_s10 : muxFastIterFullT16 55 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_11 :=
  (muxFastIterFullT16_add 50 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s9).trans (bWalkChk_sound pchk_c0_s10))
private theorem pacc_c0_s11 : muxFastIterFullT16 60 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_12 :=
  (muxFastIterFullT16_add 55 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s10).trans (bWalkChk_sound pchk_c0_s11))
private theorem pacc_c0_s12 : muxFastIterFullT16 65 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_13 :=
  (muxFastIterFullT16_add 60 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s11).trans (bWalkChk_sound pchk_c0_s12))
private theorem pacc_c0_s13 : muxFastIterFullT16 70 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_14 :=
  (muxFastIterFullT16_add 65 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s12).trans (bWalkChk_sound pchk_c0_s13))
private theorem pacc_c0_s14 : muxFastIterFullT16 75 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_15 :=
  (muxFastIterFullT16_add 70 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s13).trans (bWalkChk_sound pchk_c0_s14))
private theorem pacc_c0_s15 : muxFastIterFullT16 80 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = pvm_c0_16 :=
  (muxFastIterFullT16_add 75 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s14).trans (bWalkChk_sound pchk_c0_s15))
private theorem pacc_c0_s16 : muxFastIterFullT16 85 513
    phbv_g0 rkmViHi_m512_r512_s3_c1 = rkmVoHi_m512_r512_s3_c1 :=
  (muxFastIterFullT16_add 80 5 513 phbv_g0 rkmViHi_m512_r512_s3_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s15).trans (bWalkChk_sound pchk_c0_s16))
/-- Certified `T_16` walk chunk `m512_r512_s3_c1`. -/
theorem rkmWalkChkHi_m512_r512_s3_c1 : muxFastIterFullT16 85 513
    rkmHbHi_m512_r512_s3_c1 rkmViHi_m512_r512_s3_c1 = rkmVoHi_m512_r512_s3_c1 :=
  (congrArg (fun h ↦ muxFastIterFullT16 85 513 h rkmViHi_m512_r512_s3_c1)
    (muxIntListEq_eq_true.mp (rkmHd pchk_c0_s0))).trans pacc_c0_s16
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi512T8`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi512T8 :
    rkmWalkChkHi_m512_r512_s3_c1 = rkmWalkChkHi_m512_r512_s3_c1 :=
  rfl
end
end QuantumComputation.Specs.DickeSol
