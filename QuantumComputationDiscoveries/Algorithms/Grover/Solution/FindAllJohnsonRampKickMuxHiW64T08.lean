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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiWin
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHiW64T07

/-
# Caustic `r = 1024` Halo-16 Walk `w64_m32` Part `1` (`FindAllJohnsonRampKickMuxHiW64T08`)

Certifies part `1` of the `w64_m32` `r = 1024` halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Generator list for `w64_m32_s5`. -/
def rkmHbWin_w64_m32_s5 : List ℤ := altBuildHbFrom 1856 1024 19586394833 0 1024
/-- Entry `rkmXsWin_w64_m32_s5_in`. -/
def rkmXsWin_w64_m32_s5_in : List ℤ := [rkmP 114159959, rkmP 319756100, rkmP 324515303,
  rkmN 34816223, rkmN 739157368, rkmN 1851303338, rkmN 3178444393, rkmN 4255823599,
  rkmN 4359686184, rkmN 2637891878, rkmP 2067818531, rkmP 10261789180, rkmP 21906069919,
  rkmP 35600198639, rkmP 47720057017, rkmP 52467014466, rkmP 41665954739, rkmP 5257209183,
  rkmN 66891071952, rkmN 182378004391, rkmN 342403543598, rkmN 536723490686, rkmN 737463784338,
  rkmN 893573986155, rkmN 924415066532, rkmN 715554447928, rkmN 116902720829, rkmP 1056708097765,
  rkmP 3020492661981, rkmP 6010378123012, rkmP 10269858792390, rkmP 16033252214729,
  rkmP 23505756910362, rkmP 32843172792710, rkmP 44132211392243, rkmP 57372955615746,
  rkmP 72466205645943, rkmP 89207552453656, rkmP 107287088126361, rkmP 126298116279651,
  rkmP 145752934039909, rkmP 165104631489612, rkmP 183774409552133, rkmP 201181759478545,
  rkmP 216775245895628, rkmP 230061513393983, rkmP 240631106723963, rkmP 248178436698034,
  rkmP 252514795158712, rkmP 253574425411054, rkmP 251413138576975, rkmP 246199080825052,
  rkmP 238199078545011, rkmP 227759607149845, rkmP 215284972039133, rkmP 201214628680190,
  rkmP 186000864319320, rkmP 170088012640847, rkmP 153894327764465, rkmP 137798094397916,
  rkmP 122127172666880, rkmP 107152190293495, rkmP 93084398282557, rkmP 80076344820954,
  rkmP 68224900321584, rkmP 57576934435340, rkmP 48136704823045, rkmP 39872824406474,
  rkmP 32726470188376, rkmP 26618822052332, rkmP 21458110351558, rkmP 17145462583472,
  rkmP 13579956060072, rkmP 10663030601667, rkmP 8301073950979, rkmP 6407435570575,
  rkmP 4904170203971, rkmP 3722368292899, rkmP 2801951735192, rkmP 2091712083369,
  rkmP 1548761625859, rkmP 1137459047291, rkmP 828539106662, rkmP 598592350183, rkmP 428893269969,
  rkmP 304818514802, rkmP 214706234566, rkmP 149829928023, rkmP 103653467443, rkmP 70955673389,
  rkmP 47915889902, rkmP 31918870667, rkmP 20945631193, rkmP 13405325472, rkmP 8246128257,
  rkmP 4823446007, rkmP 2634503815, rkmP 1244132548, rkmP 387325936]
/-- Exit `rkmXsWin_w64_m32_s5_out`. -/
def rkmXsWin_w64_m32_s5_out : List ℤ := [rkmN 336398198, rkmN 258541105, rkmP 269566093,
  rkmP 787694739, rkmP 782570131, rkmN 64361244, rkmN 1243244011, rkmN 1971101123, rkmN 1296777760,
  rkmP 863938293, rkmP 3404279165, rkmP 4151387376, rkmP 1741416546, rkmN 3132540039,
  rkmN 7604336044, rkmN 8098871718, rkmN 2655885274, rkmP 7218063894, rkmP 15866047399,
  rkmP 16304883380, rkmP 4720689239, rkmN 15138211526, rkmN 32542323318, rkmN 34143041621,
  rkmN 12342597260, rkmP 27242743259, rkmP 64900487204, rkmP 74786745415, rkmP 38947896217,
  rkmN 37507170255, rkmN 121679555855, rkmN 163899174449, rkmN 121711337720, rkmP 12709183933,
  rkmP 195159971945, rkmP 337659013150, rkmP 342766180928, rkmP 154461156639, rkmN 197442224369,
  rkmN 585130552391, rkmN 816856480939, rkmN 713172616005, rkmN 200310726996, rkmP 621368012222,
  rkmP 1469961307616, rkmP 1955089891578, rkmP 1719905035758, rkmP 605041126134,
  rkmN 1225279678070, rkmN 3257283231040, rkmN 4730974761119, rkmN 4861650611709,
  rkmN 3122449563454, rkmP 500020490949, rkmP 5367769916621, rkmP 10235971215240,
  rkmP 13495208323621, rkmP 13566188323162, rkmP 9355921482980, rkmP 657124250562,
  rkmN 11618108989901, rkmN 25441843979321, rkmN 37927588046214, rkmN 45792973201623,
  rkmN 45936196789690, rkmN 36005521593707, rkmN 14847407655488, rkmP 17250472594252,
  rkmP 58562231502972, rkmP 106158897109371, rkmP 156322041541025, rkmP 205051450201258,
  rkmP 248576540352628, rkmP 283790704452007, rkmP 308550238351560, rkmP 321813695108136,
  rkmP 323622495242333, rkmP 314952883447179, rkmP 297479895633348, rkmP 273302374132856,
  rkmP 244671089038995, rkmP 213754816230150, rkmP 182464327639556, rkmP 152342625572790,
  rkmP 124518685830080, rkmP 99712966644374, rkmP 78282619697063, rkmP 60288068877307,
  rkmP 45569692919609, rkmP 33822002386880, rkmP 24659343890196, rkmP 17667661071211,
  rkmP 12443336865462, rkmP 8617414562626, rkmP 5869654450391, rkmP 3932977155699,
  rkmP 2592913003907, rkmP 1682047740524, rkmP 1073795625582, rkmP 674484220109, rkmP 416889266624,
  rkmP 253393511939, rkmP 151432247676, rkmP 88805390167, rkmP 51098783789, rkmP 28699107185,
  rkmP 15700979890, rkmP 8171259783, rkmP 3968883052, rkmP 1614189455, rkmP 486828407]
/-- Generator list for `w64_m32_s6a`. -/
def rkmHbWin_w64_m32_s6a : List ℤ := altBuildHbFrom 1856 1024 19587930735 0 1024
/-- Entry `rkmXsWin_w64_m32_s6a_in`. -/
def rkmXsWin_w64_m32_s6a_in : List ℤ := [rkmN 336398198, rkmN 258541105, rkmP 269566093,
  rkmP 787694739, rkmP 782570131, rkmN 64361244, rkmN 1243244011, rkmN 1971101123, rkmN 1296777760,
  rkmP 863938293, rkmP 3404279165, rkmP 4151387376, rkmP 1741416546, rkmN 3132540039,
  rkmN 7604336044, rkmN 8098871718, rkmN 2655885274, rkmP 7218063894, rkmP 15866047399,
  rkmP 16304883380, rkmP 4720689239, rkmN 15138211526, rkmN 32542323318, rkmN 34143041621,
  rkmN 12342597260, rkmP 27242743259, rkmP 64900487204, rkmP 74786745415, rkmP 38947896217,
  rkmN 37507170255, rkmN 121679555855, rkmN 163899174449, rkmN 121711337720, rkmP 12709183933,
  rkmP 195159971945, rkmP 337659013150, rkmN 342766180927, rkmP 154461156639, rkmN 197442224369,
  rkmP 585130552392, rkmP 816856480940, rkmP 713172616006, rkmN 200310726996, rkmP 621368012222,
  rkmP 1469961307616, rkmP 1955089891578, rkmP 1719905035758, rkmP 605041126134,
  rkmP 1225279678071, rkmP 3257283231041, rkmP 4730974761120, rkmP 4861650611710,
  rkmP 3122449563455, rkmP 500020490949, rkmP 5367769916621, rkmP 10235971215240,
  rkmP 13495208323621, rkmP 13566188323162, rkmP 9355921482980, rkmP 657124250562,
  rkmP 11618108989902, rkmP 25441843979322, rkmP 37927588046215, rkmP 45792973201624,
  rkmP 45936196789691, rkmP 36005521593708, rkmP 14847407655489, rkmP 17250472594252,
  rkmP 58562231502972, rkmP 106158897109371, rkmP 156322041541025, rkmP 205051450201258,
  rkmP 248576540352628, rkmP 283790704452007, rkmP 308550238351560, rkmP 321813695108136,
  rkmP 323622495242333, rkmP 314952883447179, rkmP 297479895633348, rkmP 273302374132856,
  rkmP 244671089038995, rkmP 213754816230150, rkmP 182464327639556, rkmP 152342625572790,
  rkmP 124518685830080, rkmP 99712966644374, rkmP 78282619697063, rkmP 60288068877307,
  rkmP 45569692919609, rkmP 33822002386880, rkmP 24659343890196, rkmP 17667661071211,
  rkmP 12443336865462, rkmP 8617414562626, rkmP 5869654450391, rkmP 3932977155699,
  rkmP 2592913003907, rkmP 1682047740524, rkmP 1073795625582, rkmP 674484220109, rkmP 416889266624,
  rkmP 253393511939, rkmP 151432247676, rkmP 88805390167, rkmP 51098783789, rkmP 28699107185,
  rkmP 15700979890, rkmP 8171259783, rkmP 3968883052, rkmP 1614189455, rkmP 486828407]
/-- Exit `rkmXsWin_w64_m32_s6a_out`. -/
def rkmXsWin_w64_m32_s6a_out : List ℤ := [rkmP 231789013, rkmN 704419225, rkmP 1547235858,
  rkmN 2773992677, rkmP 4269144493, rkmN 6375698409, rkmP 8999521918, rkmN 12200456328,
  rkmP 16190194080, rkmN 21069063685, rkmP 26908445064, rkmN 33903336083, rkmP 42074591973,
  rkmN 51421054809, rkmP 62120975073, rkmN 73907766078, rkmP 86652486355, rkmN 100028698921,
  rkmP 113496814839, rkmN 126552120301, rkmP 138426347223, rkmN 148073086981, rkmP 154761254101,
  rkmN 157352028705, rkmP 154936565276, rkmN 146905465893, rkmP 132639571498, rkmN 112013949814,
  rkmP 85629098114, rkmN 54131488610, rkmP 18951743614, rkmP 18055694801, rkmN 54848118592,
  rkmP 89382735684, rkmN 119620623050, rkmP 144298411968, rkmN 162808328251, rkmP 175398923244,
  rkmN 183613079336, rkmP 189638377772, rkmN 196465924081, rkmP 207337891651, rkmN 225082667767,
  rkmP 251543316231, rkmN 287531263015, rkmP 331924246765, rkmN 382003771185, rkmP 433999999668,
  rkmN 482976078987, rkmP 524250215911, rkmN 553984692014, rkmP 569407914756, rkmN 569448075874,
  rkmP 554786337849, rkmN 526808379583, rkmP 487352417084, rkmN 437854982596, rkmP 378841090792,
  rkmN 310003549490, rkmP 231265145165, rkmN 143153294021, rkmP 48604739524, rkmP 46160548650,
  rkmN 132026512844, rkmP 197614380193, rkmN 231225387828, rkmP 223828071190, rkmN 171790841679,
  rkmP 77899386182, rkmP 47729407666, rkmN 189555982355, rkmP 329718224728, rkmN 450991661561,
  rkmP 539335724019, rkmN 585207596998, rkmP 582744961964, rkmN 527717131271, rkmP 417104786304,
  rkmN 249329309813, rkmP 27631031800, rkmP 234428334993, rkmN 507847234855, rkmP 747282717453,
  rkmN 896326188883, rkmP 900088093116, rkmN 724191588239, rkmP 372839453805, rkmP 100500552276,
  rkmN 596607664314, rkmP 990494077414, rkmN 1166431937540, rkmP 1056163363931, rkmN 667377087329,
  rkmP 91814216689, rkmP 515243174628, rkmN 979416697096, rkmP 1162665910608, rkmN 1009776532457,
  rkmP 569727020760, rkmP 17783588694, rkmN 568050035460, rkmP 913063373595, rkmN 956692116165,
  rkmP 704498623046, rkmN 257700320934, rkmN 225949937205, rkmP 589272914391, rkmN 727762877436,
  rkmP 620271361017, rkmN 328607221867, rkmN 30609303346, rkmP 331032299406, rkmN 481220696453,
  rkmP 452276859943, rkmN 281195921336, rkmP 49443442184, rkmP 152585413061, rkmN 261756942999,
  rkmP 263425120356, rkmN 188512168529, rkmP 89449079992, rkmN 8206303057, rkmN 45007018749,
  rkmP 88469829895, rkmN 143501430424, rkmP 203680720381, rkmN 225072022757, rkmP 150657027717,
  rkmP 39890977885, rkmN 288843685372, rkmP 465816241958, rkmN 432963459572, rkmP 141460107059,
  rkmP 303025923549, rkmN 664994184305, rkmP 701450916484, rkmN 323251037037, rkmN 310231044239,
  rkmP 844805466097, rkmN 928564589742, rkmP 445668353846, rkmP 368190802991, rkmN 1029771178839,
  rkmP 1095719193439, rkmN 464522523402, rkmN 514395799551, rkmP 1225635737578, rkmN 1176823023860,
  rkmP 345867849473, rkmP 760361276053, rkmN 1409392891251, rkmP 1131431141801, rkmN 67345402237,
  rkmN 1084921954389, rkmP 1524038719569, rkmN 907798548718, rkmN 371610135304, rkmP 1424178453312,
  rkmN 1479414228315, rkmP 458966701623, rkmP 925582328575, rkmN 1658360108007, rkmP 1166914796955,
  rkmP 218649665612, rkmN 1469261150451, rkmP 1615180599600, rkmN 506428978930, rkmN 1025276165465,
  rkmP 1775913421424, rkmN 1117233410493, rkmN 462162915803, rkmP 1697320323649,
  rkmN 1553612750717, rkmP 106067435414, rkmP 1462819366300, rkmN 1814752494943, rkmP 605654507361,
  rkmP 1157971518083, rkmN 1935399652132, rkmP 1001724352742, rkmP 852308339840,
  rkmN 1963111478555, rkmP 1287176030227, rkmP 593550122922, rkmN 1942680544708,
  rkmP 1470311372566, rkmP 408366263188, rkmN 1907397281631, rkmP 1564976807183, rkmP 306611676381,
  rkmN 1877213521150, rkmP 1585646322388, rkmP 285914180756, rkmN 1860849309997,
  rkmP 1546458687036, rkmP 337266650347, rkmN 1862496558417, rkmP 1460326835803, rkmP 453298115489,
  rkmN 1887297507817, rkmP 1333816689164, rkmP 638437001267, rkmN 1940793237658,
  rkmP 1153948467856, rkmP 913768880540, rkmN 2012220608782, rkmP 872101010777, rkmP 1301902638212,
  rkmN 2042196338174, rkmP 406024592052, rkmP 1779815837808, rkmN 1896755118389, rkmN 310074331154,
  rkmP 2212352915162, rkmN 1395282345006, rkmN 1219834845495, rkmP 2329747408891,
  rkmN 438829475539, rkmN 2044260274466, rkmP 1840942052629, rkmP 798843152874, rkmN 2329733587200,
  rkmP 704438275365, rkmP 1799766109952, rkmN 1757453009093, rkmN 638605682409, rkmP 1983457375853,
  rkmN 554590630323, rkmN 1438845521473, rkmP 1279048203181, rkmP 496245763234, rkmN 1322786615464,
  rkmP 376955518683, rkmP 784899003223, rkmN 821077545871, rkmP 29230575151, rkmP 692632069575,
  rkmN 761076294861, rkmN 66483546482, rkmP 1129309342250, rkmN 836631797034, rkmN 998675952578,
  rkmP 1748398843715, rkmP 384129513480, rkmN 2436774093119, rkmP 589630926618, rkmP 2755168749605,
  rkmN 1746244743070, rkmN 2654220790446, rkmP 2911989435799, rkmP 2166264711770,
  rkmN 3952803244908, rkmN 1376059107481, rkmP 4791367048685, rkmP 390748002497,
  rkmN 5407443310026, rkmP 683444124472, rkmP 5827551810656, rkmN 1754751712259,
  rkmN 6109485965236, rkmP 2750173024299, rkmP 6326104743161, rkmN 3613311736902,
  rkmN 6551014489639, rkmP 4298989333625, rkmP 6847764734484, rkmN 4767641232968,
  rkmN 7262523038275, rkmP 4979919096074, rkmP 7820628675480, rkmN 4891959385741,
  rkmN 8524048285768, rkmP 4449164491032, rkmP 9347030208828, rkmN 3580861535504,
  rkmN 10223153152636, rkmP 2200213808054, rkmP 11022013009308, rkmN 221650544033,
  rkmN 11520823042176, rkmN 2392237457989, rkmP 11390413231712, rkmP 5551512283054,
  rkmN 10223918413615, rkmN 8946516246158, rkmP 7633725601991, rkmP 11981152122884,
  rkmN 3416674984767, rkmN 13783183447458, rkmN 2236780882412, rkmP 13327579806142,
  rkmP 8530997865494, rkmN 9712108265807, rkmN 13905379063901, rkmP 2655534941005,
  rkmP 16095187362424, rkmP 6761427037344, rkmN 12770010196588, rkmN 15436607722310,
  rkmP 3074759562973, rkmP 18576623707268, rkmP 10373185642572, rkmN 11967828511518,
  rkmN 20684350551157, rkmN 4132610840543, rkmP 19023578249739, rkmP 21582578641786,
  rkmN 972830021330, rkmN 25060926671019, rkmN 24196807188787, rkmP 3005750918152,
  rkmP 30760591606563, rkmP 31000989589322, rkmP 381944384231, rkmN 35629590968298,
  rkmN 44356977777082, rkmN 13740708861312, rkmP 36706164984121, rkmP 69719149075591,
  rkmP 57388853167667, rkmP 1552686386483, rkmN 65843351239505, rkmN 101083576165161,
  rkmN 72914924246250, rkmP 21750792187397, rkmP 157902727800378, rkmP 295685163030505,
  rkmP 398032384576194, rkmP 443739721721887, rkmP 431418288587110, rkmP 375133507649225,
  rkmP 295886779511795, rkmP 213482889560130, rkmP 141596074046321, rkmP 86562257854234,
  rkmP 48815184045895, rkmP 25375415814779, rkmP 12131518683226, rkmP 5312881723418,
  rkmP 2118237046284, rkmP 761730049100, rkmP 243557841286, rkmP 67489825906, rkmP 15332039538,
  rkmP 2382494434]

end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β :=
  HighDForce.withForcedList xs k
private abbrev bz0 : ℕ := 10000000000000000
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uCN (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 => xs
  | v + 1 =>
    match xs with
    | [] => [v]
    | h :: t => v :: h :: t
private theorem uCN_eq (x : ℕ) (xs : List ℕ) : uCN x xs = x :: xs := by
  unfold uCN; rw [n1a]; cases xs <;> rfl
private def uHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uHb ns
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ :=
  match x with
  | Int.ofNat v =>
    match xs with
    | [] => [Int.ofNat v]
    | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v =>
    match xs with
    | [] => [Int.negSucc v]
    | h :: t => Int.negSucc v :: h :: t
private theorem czEq (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem onEq (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  simp [primOfNatForced, Nat.one_add]
private theorem nsEq (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  simp [primNegSuccForced, Nat.one_add]
private theorem sbEq (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat; rw [onEq, Nat.sub_eq]; cases h : z - u with
  | zero => dsimp only; rw [Nat.sub_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private def bD (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bCZ (rkmForcedSubNatNat u z) (bD z us)
private theorem d0 (z : ℕ) : bD z [] = [] := rfl
private theorem dc (z u : ℕ) (us : List ℕ) :
    bD z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bD z us := by rw [bD, czEq, sbEq]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bM0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZ0]; rfl
private def bE1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k =>
    match Nat.sub z (Nat.add k 1) with
    | 0 => none
    | w + 1 => some (Nat.add w 1)
private def bE (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match bE1 z x with
    | none => none
    | some u =>
      match bE z xs with
      | none => none
      | some us => some (uCN u us)
private theorem e1S (z : ℕ) (x : ℤ) (u : ℕ) (h : bE1 z x = some u) :
    ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bE1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bE1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w =>
      intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem eS (z : ℕ) : ∀ (xs : List ℤ) (us : List ℕ), bE z xs = some us →
    bD z us = xs
  | [], us, h => by injection h with h'; subst h'; rfl
  | x :: xs, us, h => by
    dsimp only [bE] at h; revert h; cases hx : bE1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bE z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uCN_eq, dc, e1S z x u hx, eS z xs ws hxs]
private def zTdiv (x : ℤ) (d : ℕ) : ℤ :=
  match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem ngEq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem tdEq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by dsimp only [muxRawIntTdivNat, zTdiv]; rw [ngEq, ndiv, Nat.add_eq]
private theorem sntEq (m n d : ℕ) :
    rkmUltraSubNatTdiv m n d = zTdiv ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    dsimp only; have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTdiv]; rw [ngEq]
private theorem stEq (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTdiv (a - b) d := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => exact sntEq m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
      rw [hm]; rfl
  | negSucc m => cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTdiv]; rw [ngEq, ndiv, Nat.add_eq]
      rw [Nat.add_eq]; exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [sntEq, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTdiv t d) (by simp only [Int.negSucc_eq]; omega)
private theorem mlEq : ∀ (a b : ℤ), muxRawIntMul a b = a * b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [ngEq, Nat.mul_eq, Nat.add_eq]
    rw [Int.ofNat_eq_natCast, Int.negSucc_eq]; push_cast; ring
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [ngEq, Nat.mul_eq, Nat.add_eq]
    rw [Int.negSucc_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq, Nat.add_eq, Nat.add_eq, Int.ofNat_eq_natCast]
    simp only [Int.negSucc_eq]; push_cast; ring
private theorem faEq : ∀ (a b : ℤ), rkmForcedIntAdd a b = a + b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [onEq, Nat.add_eq]
    simp only [Int.ofNat_eq_natCast]; omega
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [sbEq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [sbEq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [nsEq, Nat.add_eq, Nat.add_eq]
    simp only [Int.negSucc_eq]; omega
private theorem acEq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [faEq]; cases a + b <;> cases xs <;> rfl
private def bSV (v P Q d : ℕ) : ℕ :=
  match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem svEq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← sntEq]; unfold bSV at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv; cases h : Q - P with
  | zero => intro _; dsimp only; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k => intro hv; dsimp only at hv ⊢; rw [ngEq]; omega
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bSV v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bD z rest = tailZ) :
    bD z (uCN (bCV z d b0 c0 b v c1) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uCN_eq, dc, ht, acEq, stEq, mlEq, mlEq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCV at hv ⊢; rw [svEq z v _ _ d hv, hpq]
private theorem bCell_nil (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bD z rest = tailZ) :
    bD z (uCN (bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uCN_eq, dc, ht, acEq, tdEq, mlEq]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  rw [svEq z v _ _ d hv, hpq]
private def bAP : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAP xs)
private theorem apC {x : ℕ} {xs : List ℕ} (h : bAP (uCN x xs) = true) :
    0 < x ∧ bAP xs = true := by
  rw [uCN_eq] at h
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
    ((bHO z cs : ℤ) - (z : ℤ)) = (match bD z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHO; rw [d0, bZ0]
  | c :: cs => by unfold bHO; rw [dc]
private theorem tnEq (z : ℕ) : ∀ (xs : List ℕ),
    bD z (bTN xs) = (match bD z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | x :: xs => by unfold bTN; rw [dc]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs =>
    match bns with
    | [] => uCN (bSV (bHO z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSl z d rem 0 z [] (bTN vs) (bTN cs))
    | b :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uCN (bCV z d b0 c0 b v (bHO z cT)) (bSl z d rem b c bR vT cT)
      | v :: vT, [] => uCN (bCV z d b0 c0 b v z) (bSl z d rem b z bR vT [])
      | [], c :: cT => uCN (bCV z d b0 c0 b z (bHO z cT)) (bSl z d rem b c bR [] cT)
      | [], [] => uCN (bCV z d b0 c0 b z z) (bSl z d rem b z bR [] [])
private theorem bSl_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAP (bSl z d rem b0 c0 bns vs cs) = true →
      bD z (bSl z d rem b0 c0 bns vs cs) =
        rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
          (uHb bns) (bD z vs) (bD z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSl, uHb, rkmUltraSlideLoopAux] at h ⊢; have hp := apC h
      have hi := bSl_sound z d rem 0 z [] (bTN vs) (bTN cs) hp.2
      rw [bM0, uHb, tnEq z vs, tnEq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHO z vs) hp.1 hi; rw [hoEq z vs] at hc; exact hc
    | cons b bR =>
      cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSl, uHb] at h ⊢; rw [d0, rkmUltraSlideLoopAux]
          have hp := apC h; have hi := bSl_sound z d rem b z bR [] [] hp.2
          rw [bZ0 z, d0] at hi; have hc := bCell_hb z d b0 c0 b z z hp.1 hi
          rw [bZ0 z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uHb] at h ⊢; rw [d0, dc z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := apC h
          have hi := bSl_sound z d rem b c bR [] cT hp.2; rw [d0] at hi
          have hc := bCell_hb z d b0 c0 b z (bHO z cT) hp.1 hi
          rw [hoEq z cT, bZ0 z] at hc; exact hc
      | cons v vT => cases cs with
        | nil =>
          dsimp only [bSl, uHb] at h ⊢; rw [dc z v vT, d0]
          dsimp only [rkmUltraSlideLoopAux]; have hp := apC h
          have hi := bSl_sound z d rem b z bR vT [] hp.2; rw [bZ0 z, d0] at hi
          have hc := bCell_hb z d b0 c0 b v z hp.1 hi; rw [bZ0 z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uHb] at h ⊢; rw [dc z v vT, dc z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := apC h
          have hi := bSl_sound z d rem b c bR vT cT hp.2
          have hc := bCell_hb z d b0 c0 b v (bHO z cT) hp.1 hi; rw [hoEq z cT] at hc
          exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uCN b (uCN (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs =>
    match hbz with
    | [] =>
      uCN (bSV (bHO z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTN vs) (bTN cs))
    | [_] => []
    | b :: bz :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uCN (bSV v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] =>
        uCN (bSV v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT =>
        uCN (bSV z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
      | [], [] =>
        uCN (bSV z (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR [] [])
private theorem bSlZ_eq (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs = bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTN vs) (bTN cs)
      have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
      dsimp only [mkHbZ] at hrec; rw [hz0] at hrec; dsimp only [mkHbZ, bSlZ, bSl]; rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ]; rw [uCN_eq, uCN_eq]; cases vs with
      | nil => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR vT cT]
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
    uCN4 x1 x2 x3 x4 xs = uCN x1 (uCN x2 (uCN x3 (uCN x4 xs))) := by
  unfold uCN4; rw [n1a x1, n1a x2, n1a x3, n1a x4]
  rw [uCN_eq, uCN_eq, uCN_eq, uCN_eq]; cases xs <;> rfl
private def bAP4 : List ℕ → Bool
  | a :: b :: c :: d :: xs =>
    cond (Nat.ble a 0) false (cond (Nat.ble b 0) false
      (cond (Nat.ble c 0) false (cond (Nat.ble d 0) false (bAP4 xs))))
  | xs => bAP xs
private theorem bAP4e : ∀ (xs : List ℕ), bAP4 xs = bAP xs
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: xs => by dsimp only [bAP4, bAP]; rw [bAP4e xs]
private def bChkP (out : List ℕ) : Option (List ℕ) :=
  match out with
  | [] => some []
  | x :: xs => cond (bAP4 (x :: xs)) (some (x :: xs)) none
private theorem bChkPe (out : List ℕ) : bChkP out = cond (bAP out) (some out) none := by
  cases out with | nil => rfl | cons _ _ => dsimp only [bChkP]; rw [bAP4e]
private inductive HbZ4 : Type
  | tail : List ℕ → HbZ4
  | c4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → HbZ4 → HbZ4
private abbrev hbz4C (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) : List ℕ :=
  b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: t
private def hbz4L : HbZ4 → List ℕ
  | HbZ4.tail l => l
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L r)
private def fH4 {α : Type} (h : HbZ4) (k : HbZ4 → α) : α :=
  match h with
  | HbZ4.tail l => fL l fun lF => k (HbZ4.tail lF)
  | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r => k (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r)
private theorem fH4e {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ => dsimp only [fH4, fL]; rw [rkmb_forceList_eq]
  | c4 _ _ _ _ _ _ _ _ _ => rfl
private def toH4 : List ℕ → HbZ4
  | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs =>
    match toH4 bs with
    | HbZ4.tail l => HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.tail l)
    | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t =>
      HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t)
  | bs => HbZ4.tail bs
private theorem hbz4L_toH4 : ∀ (xs : List ℕ), hbz4L (toH4 xs) = xs
  | [] => rfl | [_] => rfl | [_, _] => rfl | [_, _, _] => rfl
  | [_, _, _, _] => rfl | [_, _, _, _, _] => rfl
  | [_, _, _, _, _, _] => rfl | [_, _, _, _, _, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: bs => by
    have ih := hbz4L_toH4 bs; dsimp only [toH4]
    cases h : toH4 bs with
    | tail _ => rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
    | c4 _ _ _ _ _ _ _ _ _ => rw [h] at ih; dsimp only [hbz4L, hbz4C] at ih ⊢; rw [ih]
private def bSlZ4Step (z d b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (bR : HbZ4)
    (ih : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _ => []
  | 1, p0, q0, vs, cs => bSlZ z d 1 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
  | 2, p0, q0, vs, cs => bSlZ z d 2 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
  | 3, p0, q0, vs, cs => bSlZ z d 3 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
  | rem + 4, p0, q0, v1 :: v2 :: v3 :: v4 :: vR, c1 :: c2 :: c3 :: c4 :: c5 :: cR =>
    uCN4 (bSV v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
      (bSV v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
      (bSV v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
      (bSV v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 c5) z3) d)
      (ih rem (Nat.mul b4 c4) z4 vR (c5 :: cR))
  | rem + 4, p0, q0, vs, cs =>
    bSlZ z d (rem + 4) p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
private def bSlZ4 (z d : ℕ) : HbZ4 → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | HbZ4.tail l => fun rem p0 q0 vs cs => bSlZ z d rem p0 q0 l vs cs
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR =>
    bSlZ4Step z d b1 z1 b2 z2 b3 z3 b4 z4 bR (bSlZ4 z d bR)
private theorem bSlZ4_eq (z d : ℕ) : ∀ (hbz : HbZ4) (rem p0 q0 : ℕ) (vs cs : List ℕ),
    bSlZ4 z d hbz rem p0 q0 vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs
  | HbZ4.tail _, _, _, _, _, _ => by dsimp only [bSlZ4, hbz4L]
  | HbZ4.c4 _ _ _ _ _ _ b4 z4 bR, rem, _, _, vs, cs => by
    dsimp only [bSlZ4, hbz4L, hbz4C]; match rem with
    | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl
    | rem1 + 4 => match vs with
      | [] => rfl | [_] => rfl | [_, _] => rfl | [_, _, _] => rfl
      | _ :: _ :: _ :: _ :: vR => match cs with
        | [] => rfl | [_] => rfl | [_, _] => rfl | [_, _, _] => rfl | [_, _, _, _] => rfl
        | _ :: _ :: _ :: c4 :: c5 :: cR =>
          dsimp only [bSlZ4Step]; have hr : rem1 + 4 = (((rem1 + 1) + 1) + 1) + 1 := by omega
          rw [hr]; dsimp only [bSlZ, bHO]; rw [uCN4e]
          exact congrArg (fun r => uCN _ (uCN _ (uCN _ (uCN _ r))))
            (bSlZ4_eq z d bR rem1 (Nat.mul b4 c4) z4 vR (c5 :: cR))
private def bDg (z dg mL cL : ℕ) (h4 : HbZ4) (v c : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    bChkP (bSlZ4 z d h4 nL 0 0 v c)
private theorem bDg_sound (z dg mL cL : ℕ) (b v c out : List ℕ)
    (h : bDg z dg mL cL (toH4 (mkHbZ z b)) v c = some out) :
    bD z out = rkmUltraHornerStage dg mL cL (uHb b) (bD z v) (bD z c) := by
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c
  have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
  rw [hz0] at hsl; unfold bDg at h; dsimp only [fN] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, bChkPe, bSlZ4_eq, hbz4L_toH4, hsl] at h; revert h
  cases hp : bAP (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; dsimp only [cond] at h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bM0 z]; exact bSl_sound z _ _ 0 z b v c hp
private def bBdD (z g m c : ℕ) (h4 : HbZ4) (v x : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen m c) fun n => match bDg z g m c h4 v x with | none => none | some o => k n o
private theorem bBdD_sound {z g m c : ℕ} {b v x out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBdD z g m c (toH4 (mkHbZ z b)) v x kB = some out)
    (hk : ∀ m0, kB (rkmNextLen m c) m0 = some out → bD z out = kU (rkmNextLen m c) (bD z m0)) :
    bD z out = (HighDForce.withForcedNat (rkmNextLen m c) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage g m c (uHb b) (bD z v) (bD z x)) (kU nL)) := by
  unfold bBdD at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; revert h
  cases hs : bDg z g m c (toH4 (mkHbZ z b)) v x with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bDg_sound z g m c b v x mid hs]
    exact hk mid h
private def bSp (z m c : ℕ) (hbz v : List ℕ) : Option (List ℕ) :=
  fH4 (toH4 hbz) fun h4 =>
    bBdD z 16 m c h4 v v fun l x => bBdD z 15 m l h4 v x fun l x =>
    bBdD z 14 m l h4 v x fun l x => bBdD z 13 m l h4 v x fun l x =>
    bBdD z 12 m l h4 v x fun l x => bBdD z 11 m l h4 v x fun l x =>
    bBdD z 10 m l h4 v x fun l x => bBdD z 9 m l h4 v x fun l x =>
    bBdD z 8 m l h4 v x fun l x => bBdD z 7 m l h4 v x fun l x =>
    bBdD z 6 m l h4 v x fun l x => bBdD z 5 m l h4 v x fun l x =>
    bBdD z 4 m l h4 v x fun l x => bBdD z 3 m l h4 v x fun l x =>
    bBdD z 2 m l h4 v x fun l x => bDg z 1 m l h4 v x
private theorem bSp_sound (z mL cL : ℕ) (b v out : List ℕ)
    (h : bSp z mL cL (mkHbZ z b) v = some out) :
    bD z out = rkmUltraHornerT16Step mL cL (uHb b) (bD z v) := by
  unfold bSp at h; rw [fH4e] at h; unfold rkmUltraHornerT16Step
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  refine bBdD_sound h fun _ h => bBdD_sound h fun _ h => bBdD_sound h fun _ h => ?_
  exact bDg_sound z 1 mL _ b v _ out h
private def bIt (z : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, v => some v
  | k + 1, m, c, hbz, v =>
    match bSp z m c hbz v with
    | none => none
    | some vN => fN (rkmNextLen16 m c) fun nL => bIt z k m nL hbz vN
private theorem bIt_sound (z : ℕ) : ∀ (k m c : ℕ) (b v out : List ℕ),
    bIt z k m c (mkHbZ z b) v = some out →
      bD z out = muxUltraIterFullT16Rkm k m c (uHb b) (bD z v)
  | 0, _, _, _, _, _, h => by injection h with h'; subst h'; rfl
  | k + 1, m, c, b, v, out, h => by
    unfold bIt at h; revert h; cases hs : bSp z m c (mkHbZ z b) v with
    | none => intro h; dsimp only at h; cases h
    | some vN =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bSp_sound z m c b v vN hs]
      exact bIt_sound z k m _ b vN out h
private def drN : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | _, [] => []
  | k + 1, _ :: xs => drN k xs
private theorem dnEq : ∀ (s : ℕ) (b : List ℕ),
    uHb (drN s b) = rkmDropInts s (uHb b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: bs => dnEq k bs
private def dr2 : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | k + 1, _ :: _ :: xs => dr2 k xs
  | _, _ => []
private theorem d2Eq (z : ℕ) : ∀ (s : ℕ) (b : List ℕ),
    dr2 s (mkHbZ z b) = mkHbZ z (drN s b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: bs => by
    dsimp only [mkHbZ, drN]; rw [uCN_eq, uCN_eq]
    dsimp only [dr2]; exact d2Eq z k bs
private theorem dr_hbS (m r hPt k rem w : ℕ) :
    rkmDropInts (k + 1) (altBuildHbFromAux m r hPt (rem + 1) w) =
      rkmDropInts k (altBuildHbFromAux m r hPt rem (w + 1)) := by
  dsimp only [altBuildHbFromAux]; rw [strictConsInt_eq, Nat.add_eq]; rfl
private theorem dr_hbA (m r hPt : ℕ) : ∀ (k rem w : ℕ),
    rkmDropInts k (altBuildHbFromAux m r hPt rem w) = altBuildHbFromAux m r hPt (rem - k) (w + k)
  | 0, _, _ => rfl
  | _ + 1, 0, _ => by rw [Nat.zero_sub]; rfl
  | k + 1, rem + 1, w => by
    rw [dr_hbS, dr_hbA m r hPt k rem (w + 1), Nat.succ_sub_succ_eq_sub,
      show w + 1 + k = w + (k + 1) by omega]
private theorem drHb (m r hPt w0 d : ℕ) :
    altBuildHbFrom m r hPt w0 (d - w0) = rkmDropInts w0 (altBuildHbFrom m r hPt 0 d) := by
  unfold altBuildHbFrom; rw [dr_hbA, Nat.zero_add]
private theorem dr_add : ∀ (a b : ℕ) (xs : List ℤ),
    rkmDropInts (a + b) xs = rkmDropInts b (rkmDropInts a xs)
  | 0, b, _ => by rw [Nat.zero_add b]; rfl
  | _ + 1, b, [] => by rw [Nat.succ_add]; cases b <;> rfl
  | a + 1, b, _ :: xs => by rw [Nat.succ_add]; exact dr_add a b xs
private def bAZ (z u : ℕ) : ℕ := Nat.add (Nat.sub u z) (Nat.sub z u)
private theorem azEq (z u : ℕ) : bAZ z u = rkmIntAbsNat ((u : ℤ) - (z : ℤ)) := by
  unfold bAZ; simp only [Nat.add_eq, Nat.sub_eq]; cases h : z - u with
  | zero =>
    have hm : (u : ℤ) - (z : ℤ) = Int.ofNat (u - z) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; dsimp only [rkmIntAbsNat]; omega
  | succ k =>
    have hm : (u : ℤ) - (z : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [rkmIntAbsNat]; rw [Nat.add_eq]; omega
private def bPZ (z : ℕ) : ℕ → List ℕ → List ℕ
  | 0, us => us
  | k + 1, us => uCN z (bPZ z k us)
private theorem pzEq (z : ℕ) : ∀ (k : ℕ) (us : List ℕ),
    bD z (bPZ z k us) = rkmPrependZeros k (bD z us)
  | 0, _ => rfl
  | k + 1, us => by
    dsimp only [bPZ, rkmPrependZeros]
    rw [uCN_eq, dc, bZ0 z, rkmw_strictConsInt_eq, pzEq z k us]
private def bNL : List ℕ → ℕ
  | [] => 0
  | _ :: us => Nat.add (bNL us) 1
private theorem nlEq (z : ℕ) : ∀ (us : List ℕ), bNL us = altIntLen (bD z us)
  | [] => by rw [d0, rkmw_altIntLen_eq]; rfl
  | u :: us => by
    dsimp only [bNL]; rw [Nat.add_eq, nlEq z us, dc]
    rw [rkmw_altIntLen_eq, rkmw_altIntLen_eq]; simp only [List.length_cons]
private def bTL (z thr : ℕ) : ℕ → List ℕ → ℕ → ℕ × List ℕ × ℕ
  | _, [], acc => (0, [], acc)
  | off, u :: us, acc =>
    fN (bAZ z u) fun ax =>
      match Nat.ble ax thr with
      | true =>
        fN (Nat.add off 1) fun off1 =>
          fN (Nat.add acc ax) fun acc1 => bTL z thr off1 us acc1
      | false => (off, u :: us, acc)
private theorem tlEq (z thr : ℕ) : ∀ (us : List ℕ) (off acc : ℕ),
    ((bTL z thr off us acc).1, bD z (bTL z thr off us acc).2.1,
      (bTL z thr off us acc).2.2) = rkmTrimLeft thr off (bD z us) acc
  | [], _, _ => by rw [d0]; rfl
  | u :: us, off, acc => by
    rw [dc]; dsimp only [bTL, rkmTrimLeft, fN]; simp only [rkmb_forceNat_eq]
    rw [azEq z u]; cases Nat.ble (rkmIntAbsNat ((u : ℤ) - (z : ℤ))) thr with
    | false => dsimp only; rw [dc]
    | true =>
      dsimp only
      exact tlEq z thr us (Nat.add off 1) (Nat.add acc (rkmIntAbsNat ((u : ℤ) - (z : ℤ))))
private def bTR (z thr : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | u :: us =>
    match bTR z thr us with
    | ([], dTail) =>
      fN (bAZ z u) fun ax =>
        match Nat.ble ax thr with
        | true => fN (Nat.add ax dTail) fun dSum => ([], dSum)
        | false => (uCN u [], dTail)
    | (v :: vs, dTail) => (uCN u (v :: vs), dTail)
private theorem trEq (z thr : ℕ) : ∀ (us : List ℕ),
    (bD z (bTR z thr us).1, (bTR z thr us).2) = rkmTrimRight thr (bD z us)
  | [] => by rw [d0]; rfl
  | u :: us => by
    rw [dc z u us]; dsimp only [bTR, rkmTrimRight]; rw [← trEq z thr us]
    rcases bTR z thr us with ⟨ws, dTail⟩; cases ws with
    | nil =>
      dsimp only; rw [d0]; dsimp only [fN]; simp only [rkmb_forceNat_eq]; rw [azEq z u]
      cases Nat.ble (rkmIntAbsNat ((u : ℤ) - (z : ℤ))) thr with
      | true => rfl
      | false => dsimp only; rw [uCN_eq, dc, d0, rkmw_strictConsInt_eq]
    | cons v vs =>
      dsimp only; rw [dc z v vs]; dsimp only
      rw [uCN_eq, dc, dc z v vs, rkmw_strictConsInt_eq]
private def bTW (z thr off : ℕ) (us : List ℕ) (dropAcc : ℕ) : ℕ × List ℕ × ℕ :=
  match bTL z thr off us dropAcc with
  | (off1, us1, d1) =>
    match bTR z thr us1 with
    | ([], d2) => fN (Nat.add d1 d2) fun dOut => (0, [], dOut)
    | (v :: vs, d2) => fN (Nat.add d1 d2) fun dOut => (off1, v :: vs, dOut)
private theorem twEq (z thr off : ℕ) (us : List ℕ) (dropAcc : ℕ) :
    ((bTW z thr off us dropAcc).1, bD z (bTW z thr off us dropAcc).2.1,
      (bTW z thr off us dropAcc).2.2) = rkmTrimWin thr off (bD z us) dropAcc := by
  dsimp only [bTW, rkmTrimWin]; rw [← tlEq z thr us off dropAcc]
  rcases bTL z thr off us dropAcc with ⟨off1, us1, d1⟩; dsimp only; rw [← trEq z thr us1]
  rcases bTR z thr us1 with ⟨ws, d2⟩; cases ws with
  | nil => dsimp only [fN]; simp only [rkmb_forceNat_eq]; rfl
  | cons v vs => dsimp only [fN]; simp only [rkmb_forceNat_eq]; rw [dc z v vs]
private def bWS (z w0 thr d : ℕ) (hbz : List ℕ)
    (off : ℕ) (us : List ℕ) (dropAcc : ℕ) : Option (ℕ × List ℕ × ℕ) :=
  fN (Nat.sub off 16) fun sLo =>
    match Nat.ble w0 sLo with
    | false => none
    | true =>
      fN (Nat.sub sLo w0) fun kD => fN (Nat.sub off sLo) fun padL =>
        fN (Nat.sub (Nat.add d 1) sLo) fun remMax => fL (dr2 kD hbz) fun hbzSl =>
          fL (bPZ z padL us) fun vns => fN (bNL vns) fun curLen =>
            match bIt z 1 remMax curLen hbzSl vns with
            | none => none
            | some out => some (bTW z thr sLo out dropAcc)
private theorem wsS (z w0 thr d : ℕ) {hb : List ℤ} {b : List ℕ}
    (hhb : uHb b = rkmDropInts w0 hb)
    (off : ℕ) (us : List ℕ) (dropAcc o1 : ℕ) (u1 : List ℕ) (d1 : ℕ)
    (h : bWS z w0 thr d (mkHbZ z b) off us dropAcc = some (o1, u1, d1)) :
    (o1, bD z u1, d1) = muxWinStepT16 thr d hb off (bD z us) dropAcc := by
  unfold bWS at h; unfold muxWinStepT16; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq] at h
  cases hb0 : Nat.ble w0 (Nat.sub off 16) with
  | false => rw [hb0] at h; cases h
  | true =>
    rw [hb0] at h; simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at h ⊢
    set sLo := Nat.sub off 16; set kD := Nat.sub sLo w0
    set padL := Nat.sub off sLo; set remMax := Nat.sub (Nat.add d 1) sLo
    set vns := bPZ z padL us
    rw [d2Eq] at h; revert h
    cases hi : bIt z 1 remMax (bNL vns) (mkHbZ z (drN kD b)) vns with
    | none => intro h; cases h
    | some out =>
      intro h; injection h with h'
      have ho : o1 = (bTW z thr sLo out dropAcc).1 := (congrArg Prod.fst h').symm
      have hu : u1 = (bTW z thr sLo out dropAcc).2.1 := (congrArg (fun p => p.2.1) h').symm
      have hd : d1 = (bTW z thr sLo out dropAcc).2.2 := (congrArg (fun p => p.2.2) h').symm
      have hkd : uHb (drN kD b) = rkmDropInts sLo hb := by
        rw [dnEq kD b, hhb, ← dr_add w0 kD hb]
        have hw : w0 + kD = sLo := by
          have hle := rkmw_nat_ble_eq_true.mp hb0; dsimp only [kD]; rw [Nat.sub_eq]; omega
        rw [hw]
      rw [ho, hu, hd, twEq z thr sLo out dropAcc]
      rw [bIt_sound z 1 remMax (bNL vns) (drN kD b) vns out hi, hkd]
      dsimp only [vns]; rw [nlEq z (bPZ z padL us), pzEq z padL us]
private def bWI (z w0 : ℕ) : ℕ → ℕ → ℕ → List ℕ → ℕ → List ℕ → ℕ →
    Option (ℕ × List ℕ × ℕ)
  | 0, _, _, _, off, us, dropAcc => some (off, us, dropAcc)
  | k + 1, thr, d, hbz, off, us, dropAcc =>
    match bWS z w0 thr d hbz off us dropAcc with
    | none => none
    | some (off1, us1, drop1) => bWI z w0 k thr d hbz off1 us1 drop1
private theorem wiS (z w0 : ℕ) {hb : List ℤ} {b : List ℕ}
    (hhb : uHb b = rkmDropInts w0 hb) :
    ∀ (k thr d off : ℕ) (us : List ℕ) (dropAcc oR : ℕ) (uR : List ℕ) (dR : ℕ),
      bWI z w0 k thr d (mkHbZ z b) off us dropAcc = some (oR, uR, dR) →
        (oR, bD z uR, dR) = muxWinIterT16 k thr d hb off (bD z us) dropAcc
  | 0, _, _, off, us, dropAcc, oR, uR, dR, h => by
    dsimp only [bWI, muxWinIterT16] at h ⊢; injection h with h'
    rcases Prod.mk.inj h' with ⟨rfl, h2⟩; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩; rfl
  | k + 1, thr, d, off, us, dropAcc, oR, uR, dR, h => by
    dsimp only [bWI, muxWinIterT16] at h ⊢; revert h
    cases hs : bWS z w0 thr d (mkHbZ z b) off us dropAcc with
    | none => intro h; cases h
    | some res1 =>
      rcases res1 with ⟨o1, u1, d1⟩; intro h
      rw [← wsS z w0 thr d hhb off us dropAcc o1 u1 d1 hs]
      exact wiS z w0 hhb k thr d o1 u1 d1 oR uR dR h
private def bNE (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem neT {a b : ℕ} (h : bNE a b = true) : a = b := by
  unfold bNE at h; simp only [Bool.and_eq_true, rkmw_nat_ble_eq_true] at h
  exact Nat.le_antisymm h.1 h.2
private def bWinChk (w0 steps thr d : ℕ) (b : List ℕ)
    (offIn : ℕ) (xsIn : List ℤ) (offOut : ℕ) (xsOut : List ℤ) (dropExp : ℕ) : Bool :=
  fL b fun bF => fL (mkHbZ bz0 bF) fun hbz => fL xsIn fun inF => fL xsOut fun outF =>
    match bE bz0 inF with
    | none => false
    | some uIn =>
      match bWI bz0 w0 steps thr d hbz offIn uIn 0 with
      | none => false
      | some (oR, uR, dR) =>
        Bool.and (bNE oR offOut)
          (Bool.and (muxIntListEq (bD bz0 uR) outF) (bNE dR dropExp))
private theorem bWinChk_sound {w0 steps thr d : ℕ} {hb : List ℤ} {b : List ℕ}
    (hhb : uHb b = rkmDropInts w0 hb)
    {offIn : ℕ} {xsIn : List ℤ} {offOut : ℕ} {xsOut : List ℤ} {dropExp : ℕ}
    (h : bWinChk w0 steps thr d b offIn xsIn offOut xsOut dropExp = true) :
    RkmWinIterSound steps d hb offIn xsIn offOut xsOut dropExp := by
  unfold bWinChk at h; dsimp only [fL] at h; simp only [rkmb_forceList_eq] at h
  revert h; cases he : bE bz0 xsIn with
  | none => intro h; cases h
  | some uIn =>
    intro h
    change (match bWI bz0 w0 steps thr d (mkHbZ bz0 b) offIn uIn 0 with
      | none => false
      | some (oR, uR, dR) =>
        Bool.and (bNE oR offOut)
          (Bool.and (muxIntListEq (bD bz0 uR) xsOut) (bNE dR dropExp))) = true at h
    revert h
    cases hi : bWI bz0 w0 steps thr d (mkHbZ bz0 b) offIn uIn 0 with
    | none => intro h; cases h
    | some res =>
      rcases res with ⟨oR, uR, dR⟩; intro h
      change Bool.and (bNE oR offOut)
        (Bool.and (muxIntListEq (bD bz0 uR) xsOut) (bNE dR dropExp)) = true at h
      simp only [Bool.and_eq_true, muxIntListEq_eq_true] at h
      obtain ⟨ho, hx, hd⟩ := h; have ho' := neT ho; have hd' := neT hd
      rw [← ho', ← hx, ← hd']
      have hit := wiS bz0 w0 hhb steps thr d offIn uIn 0 oR uR dR hi
      rw [eS bz0 xsIn uIn he] at hit
      have h2 : muxWinIterT16HiChk steps thr 0 d hb offIn xsIn oR (bD bz0 uR) dR = true := by
        unfold muxWinIterT16HiChk; simp only [rkmb_forceList_eq]; rw [← hit]
        simp only [Bool.and_eq_true, rkmw_nat_beq_eq_true, muxIntListEq_eq_true]
        exact ⟨trivial, trivial, trivial⟩
      exact muxWinIterT16HiChk_sound h2
private theorem rkmChS (kT dT : ℕ) {w0 k1 k2 d o0 o1 o2 d1 d2 : ℕ}
    {hb x0 x1 x2 : List ℤ} {b : List ℕ} (h1 : RkmWinIterSound k1 d hb o0 x0 o1 x1 d1)
    (hhb : uHb b = rkmDropInts w0 hb)
    (h2 : bWinChk w0 k2 100000000 d b o1 x1 o2 x2 d2 = true)
    (hk : k1 + k2 = kT) (hd : d1 + d2 = dT) :
    RkmWinIterSound kT d hb o0 x0 o2 x2 dT :=
  rkmChainWinIterT16 hk hd (muxIntListEq_eq_true.mpr rfl) rfl
    (muxIntListEq_eq_true.mpr rfl) h1 (bWinChk_sound hhb h2)
private theorem rkmSegWalk_mk {nSub d offIn offOut dropSeg : ℕ}
    {hb xsIn xsOut : List ℤ} (hhb : hb.length = d)
    (hble : Nat.ble (Nat.add offIn (altIntLen xsIn)) (Nat.add d 1) = true)
    (hiter : RkmWinIterSound nSub d hb offIn xsIn offOut xsOut dropSeg) :
    RkmWinSegWalkSound nSub ⟨d, hb, offIn, xsIn, offOut, xsOut, dropSeg⟩ := by
  simp only [rkmw_nat_ble_eq_true, rkmw_altIntLen_eq, Nat.add_eq] at hble
  obtain ⟨hout, hbd⟩ := hiter hhb hble; exact ⟨hhb, hble, hout, hbd⟩
private def bAllT : List Bool → Bool
  | [] => true
  | false :: _ => false
  | true :: bs => bAllT bs
private theorem bAllT_hd {b : Bool} {bs : List Bool} (h : bAllT (b :: bs) = true) :
    b = true := by
  cases b with
  | false => exact Bool.noConfusion h
  | true => rfl
private theorem bAllT_tl {b : Bool} {bs : List Bool} (h : bAllT (b :: bs) = true) :
    bAllT bs = true := by
  cases b with
  | false => exact Bool.noConfusion h
  | true => exact h
private theorem bTl4 {a b c d : Bool} {bs : List Bool}
    (h : bAllT (a :: b :: c :: d :: bs) = true) : bAllT bs = true :=
  bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl h)))
private def uNatCatN : List (List ℕ) → List ℕ
  | [] => []
  | ns :: nss => ns ++ uNatCatN nss
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
      | 0 => primOfNatForced (Nat.div w 2)
      | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCat : List (List ℕ) → List ℤ
  | [] => []
  | ws :: wss => pzig ws ++ pzigCat wss
private def rkmPhb_w64_m32_s5 : List ℕ := uNatCatN
  [
   [717401334415663,716974358826651,716544599659927,716112058332471,715676736232235,
    715238634718104,714797755119860,714354098738148,713907666844434,713458460680963,
    713006481460720,712551730367380,712094208555265,711633917149292,711170857244924,
    710705029908117,710236436175267,709765077053150,709290953518866,708814066519776,
    708334416973444,707852005767568,707366833759913,706878901778248,706388210620268,
    705894761053529,705398553815365,704899589612817,704397869122552,703893392990782,
    703386161833181,702876176234798,702363436749971,701847943902239,701329698184243,
    700808700057641,700284949953005,699758448269724,699229195375904,698697191608261,
    698162437272022,697624932640810,697084677956538,696541673429294,695995919237226,
    695447415526427,694896162410811,694342159971992,693785408259160,693225907288952,
    692663657045323,692098657479411,691530908509406,690960410020405,690387161864281,
    689811163859529,689232415791129,688650917410392,688066668434811,687479668547904,
    686889917399059,686297414603375,685702159741497,685104152359448,684503391968467,
    683899878044831,683293610029682,682684587328852,682072809312677,681458275315816,
    680840984637065,680220936539164,679598130248604,678972564955430,678344239813042,
    677713153937990,677079306409768,676442696270602,675803322525238,675161184140725,
    674516280046189,673868609132616,673218170252618,672564962220202,671908983810538,
    671250233759713,670588710764495,669924413482079,669257340529840,668587490485077,
    667914861884753,667239453225230,666561262962007,665880289509441,665196531240478,
    664509986486367,663820653536377,663128530637510,662433615994205,661735907768039,
    661035404077427,660332102997312,659626002558851,658917100749103,658205395510703,
    657490884741533,656773566294396,656053437976672,655330497549979,654604742729825,
    653876171185255,653144780538490,652410568364565,651673532190960,650933669497222,
    650190977714586,649445454225586,648697096363665,647945901412773,647191866606962,
    646434989129977,645675266114837,644912694643410,644147271745984,643378994400828,
    642607859533750,641833864017645,641057004672037,640277278262615,639494681500761,
    638709211043071,637920863490867,637129635389704,636335523228871,635538523440875,
    634738632400929,633935846426426,633130161776402,632321574650999,631510081190912],
   [630695677476829,629878359528867,629058123305992,628234964705438,627408879562108,
    626579863647972,625747912671455,624913022276811,624075188043494,623234405485513,
    622390670050778,621543977120442,620694322008220,619841699959710,618986106151697,
    618127535691445,617265983615981,616401444891364,615533914411947,614663386999622,
    613789857403058,612913320296920,612033770281084,611151201879831,610265609541033,
    609376987635327,608485330455267,607590632214473,606692887046762,605792089005257,
    604888232061498,603981310104521,603071316939932,602158246288964,601242091787516,
    600322846985180,599400505344245,598475060238692,597546504953168,596614832681941,
    595680036527845,594742109501196,593801044518700,592856834402337,591909471878224,
    590958949575467,590005260024984,589048395658311,588088348806392,587125111698341,
    586158676460185,585189035113589,584216179574554,583240101652091,582260793046879,
    581278245349893,580292450041007,579303398487578,578311081943002,577315491545239,
    576316618315324,575314453155836,574308986849352,573300210056867,572288113316184,
    571272687040283,570253921515647,569231806900571,568206333223430,567177490380919,
    566145268136262,565109656117384,564070643815051,563028220580974,561982375625882,
    560933098017549,559880376678795,558824200385440,557764557764226,556701437290690,
    555634827287011,554564715919796,553491091197843,552413940969845,551333252922058,
    550249014575921,549161213285626,548069836235649,546974870438218,545876302730747,
    544774119773204,543668308045436,542558853844437,541445743281559,540328962279669,
    539208496570247,538084331690425,536956452979963,535824845578168,534689494420742,
    533550384236569,532407499544437,531260824649681,530110343640769,528956040385805,
    527797898528964,526635901486844,525470032444748,524300274352883,523126609922470,
    521949021621779,520767491672072,519582002043459,518392534450660,517199070348677,
    516001590928366,514800077111912,513594509548201,512384868608091,511171134379569,
    509953286662803,508731304965082,507505168495632,506274856160321,505040346556236,
    503801617966130,502558648352749,501311415353014,500059896272072,498804068077203,
    497543907391579,496279390487879,495010493281742,493737191325064,492459459799133,
    491177273507590,489890606869225,488599433910581,487303728258387,486003463131788],
   [484698611334393,483389145246106,482075036814759,480756257547529,479432778502126,
    478104570277763,476771603005881,475433846340638,474091269449139,472743841001415,
    471391529160127,470034301569998,468672125346958,467304967066994,465932792754694,
    464555567871480,463173257303510,461785825349244,460393235706668,458995451460151,
    457592435066931,456184148343218,454770552449897,453351607877814,451927274432641,
    450497511219296,449062276625900,447621528307261,446175223167874,444723317344393,
    443265766187590,441802524243758,440333545235543,438858782042187,437378186679162,
    435891710277157,434399303060419,432900914324390,431396492412650,429885984693098,
    428369337533382,426846496275518,425317405209673,423782007547093,422240245392119,
    420692059713265,419137390313330,417576175798474,416008353546251,414433859672526,
    412852628997244,411264595008997,409669689828338,408067844169787,406458987302474,
    404843047009351,403219949544924,401589619591423,399951980213349,398306952810318,
    396654457068133,394994410907984,393326730433715,391651329877039,389968121540621,
    388277015738922,386577920736693,384870742685011,383155385554723,381431751067184,
    379699738622147,377959245222655,376210165396788,374452391116109,372685811710618,
    370910313780049,369125781101312,367332094531861,365529131908787,363716767943381,
    361894874110940,360063318535528,358221965869426,356370677166956,354509309752365,
    352637717081413,350755748596308,348863249573585,346960060964500,345046019227502,
    343120956152280,341184698674868,339237068683257,337277882812887,335306952231400,
    333324082411927,331329072894179,329321717032517,327301801730123,325269107158333,
    323223406460103,321164465436498,319092042214999,317005886898335,314905741192408,
    312791338011785,310662401061077,308518644390378,306359771922779,304185476951777,
    301995441606209,299789336280112,297566819024647,295327534898974,293071115276630,
    290797177103632,288505322104133,286195135929032,283866187242456,281518026740474,
    279150186095810,276762176821614,274353489046585,271923590192832,269471923546880,
    266997906713086,264500929937392,261980354287927,259435509677187,256865692708644,
    254270164328341,251648147259458,248998823194817,246321329718854,243614756926474,
    240878143701519,238110473612025,235310670372914,232477592819083,229610029322772],
   [226706691578216,223766207663733,220787114275844,217767848011414,214706735551208,
    211601982570821,208451661171369,205253695581116,202005845828166,198705689020949,
    195350597793716,191937715374060,188463926602120,184925824068014,181319668323357,
    177641340848093,173886288092327,170049454431923,166125201229537,162107208311199,
    157988352951503,153760559755203,149414612395204,144939914648452,140324182971264,
    135553045000879,130609506211139,125473227601428,120119525523793,114517950653104,
    108630207037182,102406992908535,95782990012395,88668472556053,80934244623273,72381987847174,
    62677810015780,51170580129421,36179035075236]]
private def rkmPhb_w64_m32_s6a : List ℕ := uNatCatN
  [
   [661787798966643,661087240344788,660383884114067,659677728305484,658968770905939,
    658257009857906,657542443059104,656825068362164,656104883574296,655381886456944,
    654656074725434,653927446048630,653195998048566,652461728300088,651724634330480,
    650984713619092,650241963596958,649496381646408,648747965100673,647996711243492,
    647242617308700,646485680479821,645725897889649,644963266619824,644197783700399,
    643429446109409,642658250772418,641884194562077,641107274297661,640327486744606,
    639544828614034,638759296562280,637970887190400,637179597043679,636385422611127,
    635588360324975,634788406560150,633985557633756,633179809804537,632371159272336,
    631559602177545,630745134600546,629927752561143,629107452017985,628284228867985,
    627458078945719,626628998022825,625796981807391,624962025943332,624124126009753,
    623283277520311,622439475922561,621592716597292,620742994857853,619890305949468,
    619034645048545,618176007261962,617314387626359,616449781107400,615582182599037,
    614711586922756,613837988826814,612961382985460,612081763998144,611199126388719,
    610313464604623,609424773016049,608533045915104,607638277514956,606740461948960,
    605839593269775,604935665448465,604028672373589,603118607850266,602205465599239,
    601289239255906,600369922369353,599447508401357,598521990725380,597593362625540,
    596661617295575,595726747837775,594788747261910,593847608484129,592903324325849,
    591955887512619,591005290672964,590051526337218,589094586936323,588134464800622,
    587171152158619,586204641135725,585234923752978,584261991925744,583285837462394,
    582306452062956,581323827317744,580337954705964,579348825594298,578356431235454,
    577360762766700,576361811208363,575359567462311,574354022310397,573345166412885,
    572332990306836,571317484404476,570298638991529,569276444225517,568250890134033,
    567221966612980,566189663424780,565153970196542,564114876418211,563072371440661,
    562026444473776,560977084584472,559924280694701,558868021579404,557808295864427,
    556745092024409,555678398380608,554608203098706,553534494186561,552457259491911,
    551376486700048,550292163331431,549204276739263,548112814107013,547017762445891,
    545919108592278,544816839205097,543710940763136,542601399562312,541488201712888,
    540371333136629,539250779563895,538126526530683,536998559375605,535866863236802],
   [534731423048795,533592223539271,532449249225802,531302484412494,530151913186567,
    528997519414859,527839286740263,526677198578078,525511238112287,524341388291760,
    523167631826362,521989951182989,520808328581509,519622745990617,518433185123601,
    517239627434007,516042054111216,514840446075919,513634783975483,512425048179226,
    511211218773574,509993275557113,508771198035523,507544965416400,506314556603959,
    505079950193606,503841124466394,502598057383339,501350726579609,500099109358572,
    498843182685700,497582923182334,496318307119291,495049310410322,493775908605406,
    492498076883883,491215790047421,489929022512802,488637748304534,487341941047275,
    486041573958073,484736619838403,483427051066002,482112839586505,480793956904852,
    479470374076485,478142061698310,476808989899429,475471128331616,474128446159562,
    472780912050839,471428494165611,470071160146066,468708877105554,467341611617440,
    465969329703651,464591996822897,463209577858584,461822037106373,460429338261402,
    459031444405147,457628317991900,456219920834878,454806214091919,453387158250773,
    451962713113959,450532837783188,449097490643317,447656629345836,446210210791858,
    444758191114598,443300525661328,441837168974776,440368074773958,438893195934422,
    437412484467877,435925891501181,434433367254675,432934861019828,431430321136166,
    429919694967464,428402928877163,426879968202991,425350757230750,423815239167231,
    422273356112234,420725049029646,419170257717543,417608920777273,416040975581479,
    414466358241015,412885003570716,411296845053959,409701814805972,408099843535844,
    406490860507157,404874793497200,403251568754698,401621110955973,399983343159493,
    398338186758712,396685561433133,395025385097510,393357573849110,391682041912918,
    389998701584724,388307463171954,386608234932168,384900923009082,383185431366012,
    381461661716608,379729513452733,377988883569354,376239666586281,374481754466605,
    372715036531646,370939399372248,369154726756205,367360899531631,365557795526035,
    363745289440884,361923252741396,360091553541295,358250056482247,356398622607680,
    354537109230651,352665369795430,350783253732418,348890606306017,346987268455011,
    345073076625024,343147862592556,341211453280069,339263670561587,337304331058171,
    335333245922655,333350220612917,331355054652949,329347541380905,327327467683258],
   [325294613714107,323248752598617,321189650119488,319117064385235,317030745478990,
    314930435086401,312815866101090,310686762206003,308542837428811,306383795669386,
    304209330197175,302019123116089,299812844794318,297590153256208,295350693533086,
    293094096969582,290819980481676,288527945762290,286217578429830,283888447114599,
    281540102477433,279172076154332,276783879620140,274375002963573,271944913564978,
    269493054667224,267018843828998,264521671248428,262000897943538,259455853774279,
    256885835288967,254290103375688,251667880696671,249018348880570,246340645444192,
    243633860411091,240897032589740,238129145468473,235329122677809,232495822963161,
    229628034601756,226724469186805,223783754689044,220804427690247,217784924664680,
    214723572161895,211618575716778,208468007279268,205269790914853,202021686475986,
    198721270881101,195365916558420,191952766511517,188478705336250,184940325355538,
    181333886827762,177655270909905,173899923694996,170062789162454,166138228232770,
    162119920236369,158000741889301,153772617163075,149426329007881,144951280369744,
    140335186741744,135563674634086,130619748187956,125483066807819,120128944910110,
    114526930781961,108638725468147,102415023335092,95790501005980,88675425652092,80940591226068,
    72387663809537,62682725007772,51174592761507,36181872118644]]
private theorem rkmStatOk_hiw64t08 : bAllT [
  muxIntListEq (uHb rkmPhb_w64_m32_s5) (altBuildHbFrom 1856 1024 19586394833 565 459),
  muxIntListEq (uHb rkmPhb_w64_m32_s6a) (altBuildHbFrom 1856 1024 19587930735 664 360),
  Nat.ble (Nat.add 581 (altIntLen rkmXsWin_w64_m32_s5_in)) (Nat.add 1024 1)
  ] = true := by decide +kernel
private theorem rkmHhb_w64_m32_s5 :
    uHb rkmPhb_w64_m32_s5 = rkmDropInts 565 rkmHbWin_w64_m32_s5 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd rkmStatOk_hiw64t08)).trans
    (drHb 1856 1024 19586394833 565 1024)
private theorem rkmHhb_w64_m32_s6a :
    uHb rkmPhb_w64_m32_s6a = rkmDropInts 664 rkmHbWin_w64_m32_s6a :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl rkmStatOk_hiw64t08))).trans
    (drHb 1856 1024 19587930735 664 1024)
private def rkmC_w64_m32_s5_1 : List ℤ := pzigCat
  [
   [324167301,461227125,482356067,31480171,976237970,2295042626,3427259676,3800023568,2584074848,
    1198649157,7449522187,15661510219,24257464635,29475751233,26711836031,11046788783,
    22237859496,74575294380,141986443070,212676805606,265533468872,268929274600,183712362502,
    31544042659,411751708101,972773880677,1695218982703,2507007029751,3267218968517,
    3750693247843,3639453131005,2523230948963,91853683800,4762440614700,12074869963034,
    22603807211296,36863298339496,55255173281526,78018658192976,105188221970410,136562505180102,
    171688975047514,209866706614974,250168537356658,291481721530266,332561681006454,
    372100214185980,408797642804094,441434594932758,468939508329298,490445408688410,
    505331878067704,513250451806596,514131205598984,508174407033848,495824018609928,
    477729745439530,454701622388816,427658439178618,397575007648094,365433367607196,
    332177989209200,298680244659666,265709549518904,233914993897570,203816776276062,
    175803894107898,150138986953950,126970336523708,106345020283118,88226280322616,
    72510587053970,59044476848072,47641191117218,38094433190920,30189585593226,23714623838108,
    18466200555218,14255377200624,10910932592980,8280467331926,6231367606112,4650463839896,
    3441833049830,2526413508206,1839249946946,1327847553170,950741666476,675048789410,
    475160168588,331525772134,229195592200,156599811120,105881138422,70556488756,46079724954,
    29539227154,18445431312,10999572954,6291658344,3140826218,1304165704,399849806]]
private def rkmC_w64_m32_s5_2 : List ℤ := pzigCat
  [
   [331959645,1179368307,1995869185,2287402525,1975452817,150374409,3058709526,6928926944,
    10692070520,12513365258,9897017030,1039596438,15037257047,36731574281,59991657077,
    76922202347,76226602243,46263280895,22729749040,134936604912,282393012380,441472018834,
    570042156888,607746340186,481813103954,116827771232,547238913463,1534254487609,2807365138345,
    4243560856373,5611825077399,6560335177783,6612979378857,5181220082363,1591113803521,
    4874581572088,14920916954176,29177165575042,48131284328408,72065992964592,101008018905582,
    134693484474598,172553257421304,213724763677828,257085496040790,301309630402026,
    344942019389424,386482811539492,424475418368564,457593181942380,484713452683342,
    504976973884510,517828098802416,523032228997234,520672297662992,511126368234044,
    495026671217394,473209130880270,446654319102288,416425577177194,383611296714516,
    349270735939896,314389400342146,279845092393150,246384477173944,214609213132066,
    184974016736308,157791042292480,133241505140752,111392325456124,92213935709726,
    75600924494846,61391454920340,49385102657112,39358780352862,31081399359792,24323121926108,
    18864268327508,14501503338204,11050298575204,8347488903184,6251688283698,4642259707364,
    3417829099736,2495391528078,1806633479770,1296891610888,923195908576,651471441950,
    455548273308,315641251424,216580036390,146827816166,98504474142,65132503242,42269072894,
    26937237316,16643839218,9743458188,5352119968,2644361020,895598074,210493638]]
private def rkmC_w64_m32_s5_3 : List ℤ := pzigCat
  [
   [573821686,973412060,1362654572,984606176,173659391,2152884255,4667641343,6497243947,
    6461480921,3670380139,2727824258,12363571332,22930881800,30996094598,31135233688,18370379554,
    10625283455,55335692369,108705776325,156452077521,178160805293,149593050439,48383840723,
    137194879788,400694464210,708062277038,993190956612,1158724177052,1084097515626,642958697030,
    270395101235,1708586230465,3634693331049,5887068885071,8153825431967,9957504063045,
    10659908081283,9488138007107,5580732955349,1946981161370,13922265525920,31029809393218,
    53729104822770,82182353215462,116205579514218,155244600035590,198382599539748,
    244379486331222,291739025168764,338797656006468,383829460426252,425154503823254,
    461242408535540,490804435750202,512863484807566,526799319574098,532368430689292,
    529695003185026,519240118277466,501751142903122,478197950555166,449701252906202,
    417461061148248,382688211170728,346543752165030,310091232003204,274260339586548,
    239823556519996,207387092816618,177390483447182,150116428666440,125707015268312,
    104184830992420,85474496515332,69426378638178,55838875732268,44476789041862,35088956714570,
    27422466427200,21232015857558,16288116959696,12381988016094,9328302529380,6965121609968,
    5154832102238,3781898321448,2750376965960,1982783223834,1417097280534,1003870595740,
    704753585204,490298376580,337969951908,230433064100,155540833072,103809349312,68211811964,
    44107833542,27962891116,17096569406,9911929318,5396046862,2603698506,847114802]]
private def rkmC_w64_m32_s5_4 : List ℤ := pzigCat
  [
   [473002317,558204999,418499101,309164826,1707909526,3159302146,4169308148,3716842906,
    937869888,3970234007,10180915379,15664807667,17353566191,12003184343,1745332512,23491037728,
    48775549782,69120544750,73664870160,51010084836,6231905849,96600737909,206417726925,
    307688948727,359988314553,317004869427,138506101281,196288879104,671680813004,1223138540858,
    1732114871404,2030148294106,1917661412746,1197012607932,283457998513,2577715460197,
    5589779991911,9030535687685,12392853302225,14948441390627,15776972391299,13824540492501,
    7987861243465,2780857152092,19360399357046,42352159542086,71988726611102,108069714566244,
    149936326022412,196486635359812,246230453050584,297380984898512,347973846785022,
    395998491244050,439534844945300,476878413307158,506644272362624,527842976763218,
    539923101637882,542779090058004,536726504513734,522451691762656,500940517830488,
    473394266724778,441142433884912,405558092670996,367980227637582,329651740336956,
    291671193072460,254961141079514,220252181710650,188081615910316,158802945894724,
    132603184253912,109527548702012,89506192955122,72380462802366,57929631448934,45894688494566,
    35997509699144,27956872697136,21501639499340,16378517199740,12358063809680,9237131133574,
    6840444231738,5019255345528,3649204059908,2628953735210,1876925947192,1327818122074,
    930615984508,646221969326,444570830626,302772768176,203966820938,135877874502,89402745888,
    57853784678,36622759320,22544827648,13587615304,7552294566,3638406322,1481795764,425167132]]
private def rkmC_w64_m32_s5_5 : List ℤ := pzigCat
  [
   [274121862,722767054,598943786,55057287,1068947071,2431280659,2929271855,1970080683,508124170,
    4527951576,8854723794,11096650106,9320494052,1925530046,10796500015,25951772073,37802135931,
    39477635955,24522244607,10159656574,60377836044,114135217318,151850609406,149426512830,
    86088365286,47169341659,239075238611,452230021703,622905086731,670456112605,513936867401,
    96208409637,589084052622,1473149375242,2399693781718,3127787527090,3355638769486,
    2768672749972,1104169298552,1772861449509,5793077785927,10621599082791,15623827870607,
    19867979191209,22170506137133,21184708582383,15524556492407,3910246815317,14680561089058,
    40873533250192,74791768117602,115993548972700,163464187137960,215663732994920,
    270627280315058,326103984232626,379721938648194,429162824756626,472325373568514,
    507465094802972,533298868248098,549065768333042,554543512733286,550022953761362,
    536247238522544,514324846095348,485625851543062,451673290792070,414039366390546,
    374252338708448,333719772315964,293673468264718,255133896176328,218894181561172,
    185520348353798,155367269338968,128602293143776,105234977068804,85150609416772,
    68142644246144,53943148847548,42249091029238,32743932197354,25115530590202,19068675787198,
    14332545664852,10665793018938,7859194877068,5734994886298,4144643487488,2966491569408,
    2102919520374,1476606213228,1026936399216,707188242056,482077901136,325274753228,
    217174069534,143294847564,93197077572,59563659292,37300084266,22779376174,13377070692,
    7267967948,3325857124,985169498]]
private def rkmC_w64_m32_s5_6 : List ℤ := pzigCat
  [
   [359511189,711464529,570684269,259840000,1347060612,2262030442,2441276008,1032046594,
    1812533005,5155331703,7548136947,7172915647,2526827777,6215587892,16468733500,24239292952,
    24412974482,12392104914,12116836545,44160782533,73345936369,84874574535,64190311515,
    4021814435,90622433186,197946037944,280744093934,293540689908,196175828258,29662197375,
    365049646277,743686399991,1054139381041,1156870456989,916094340463,241718658345,866354232228,
    2281985902494,3738667593470,4844917054514,5133041499912,4142453633292,1526129586228,
    2837088761499,8741632550715,15586893373977,22360019509611,27679295878439,29899032875687,
    27267355937705,18119456758691,1082392032959,24736546295802,59603504062230,103072688946716,
    153974703555744,210481938303946,270241953440806,330561980534310,388624778157630,
    441711391470214,487406308584406,523764525244000,549429555754464,563692661158028,
    566494560922732,558373591103170,540374278233032,513927549745486,480716273292008,
    442541445662064,401198913649784,358376128020606,315573345239970,274050318517156,
    234799755473358,198543657537214,165746938050234,136645037461128,111280454928016,
    89542512091722,71207392292296,55975796767050,43505367390580,33437325266414,25417793603200,
    19113189492540,14219594175966,10467801961392,7625650824488,5497840104490,3923342261080,
    2771501723082,1938051667718,1341384777036,918822364326,622874314484,417876647058,
    277322377904,181838042956,117556974292,74723597314,46527060824,28217024176,16496164592,
    9114488044,4577981934,1920224018,526013340]]
private def rkmC_w64_m32_s5_7 : List ℤ := pzigCat
  [
   [370952358,660995258,329601852,693047937,1731312677,2353846971,1956332409,126963920,
    3225415888,5799639572,6342889538,3548010736,2952056873,11177990751,17491242589,17465604653,
    8035640561,10918745836,34205572636,51980914444,52520872804,27286813474,24176002981,
    90712155111,148427222137,166651863385,118488592025,6877807340,192907756946,390698092662,
    524581008018,511045443230,286507879910,162659442083,774590324837,1403386646655,1836158409741,
    1835634286863,1204418391961,140617060780,2102454181130,4366563237380,6409431990398,
    7561399142326,7121158653654,4509529674332,562313547907,7943184322897,16941472294831,
    26298775550951,34253727271193,38695919317971,37392617589499,28259481291773,9638403507317,
    19457974304704,59170600111242,108712016609714,166389936396440,229733177315520,
    295702128284274,360956070694172,422144463337456,476187623686762,520515927121446,
    553245512329014,573278461884896,580324374704470,574849269818304,557966129008602,
    531286035273448,496749223834776,456453925178978,412498909838426,366852055812268,
    321251854018494,277143526847900,235647994014740,197559829165300,163368559729964,
    133296311141714,107344698830074,85345038693564,67007478815286,51965843227274,39815901759124,
    30145806338654,22558563015960,16687290229512,12204410566048,8825947561476,6312021139962,
    4464597890118,3123510477404,2161624413104,1479797679132,1002031012812,671023400058,
    444245800132,290592381184,187624148720,119372665434,74632494236,45653351442,27147969578,
    15548298350,8465632302,4270866210,2032010628,578425466]]
private def rkmC_w64_m32_s5_8 : List ℤ := pzigCat
  [
   [588797899,490637405,55371758,1029695610,2108073922,2278336722,889833894,1759679551,
    4623520011,6109701923,4545601483,788710416,8373717572,14437718080,14769479882,6604384842,
    9677578519,28669235673,40559956055,35469818847,8478921257,36446697088,84224852616,
    111205003968,93995976360,21070863686,97443353999,225669617093,307763219647,285079746045,
    120714942579,176418455418,537478592060,838631670536,929365493132,680513209068,40653016346,
    916392717765,1972427838859,2788693536549,2976132301181,2202757426995,316324392701,
    2549561033076,5920288052778,9002300112582,10792944480144,10269860867834,6631889334088,
    453349491739,10647435125917,22831758046785,35122857034215,45023651245819,49697245325627,
    46325940532551,32500956084075,6582579873843,32024388377900,82721640501620,143716832676164,
    212170247962124,284464750800728,356558960524958,424374613431218,484169674985764,
    532852828741674,568209403740002,589019565784714,595070964161032,587074434498590,
    566507727946316,535411170910372,496164096752706,451268187305548,403155825279116,
    354038930703382,305803547749082,259949733724178,217574137663668,179386548222848,
    145750884396352,116742426077680,92211843788590,71848290716614,55237970086902,41914038460632,
    31396790179950,23222119347404,16962706282222,12238794405840,8723760219634,6144078381956,
    4275894905352,2940712049182,1998917911754,1342887051560,891416277226,584561249464,
    378483235536,241795631204,152018902612,94135362038,57170818144,33851772884,19512595712,
    10815343634,5559269308,2506504788,911024324,214056312]]
private def rkmC_w64_m32_s5_9 : List ℤ := pzigCat
  [
   [552628288,425128976,377110413,1636730605,2495589753,1929402389,425141734,3750652476,
    6114820496,5384654446,648074008,6786586347,13317556981,14197485917,6163844885,9649329930,
    26708976372,35087577232,25754461888,3715626637,44881274899,78664094973,82584213123,
    41343271547,41960958020,140898261504,209178561232,197644477042,77579658930,136873545255,
    380079832027,546499812417,524015949547,243055933679,277383254864,905873986184,1414329916262,
    1537550164118,1065053567382,57892033081,1656608652699,3314337112813,4440209325193,
    4415541208833,2789624342697,524850630144,5112383147174,10027650349382,13908097044666,
    15224971966916,12631503017684,5342202291212,6541083774573,21833643653903,38258701804425,
    52647308407361,61322316107997,60608583311091,47385391725139,19586910221897,23432637315702,
    80726153975632,149800642325436,226867465492716,307255203463990,385915549924470,
    457949589532862,519083585965482,566037294095546,596750750502868,610457919649966,
    607619377851326,589741432200888,559116973089808,518533472621390,470981676419104,
    419397175325222,366453904753564,314422615948368,265091940419152,219745908026658,
    179189385756146,143804530494608,113627266070528,88431033274224,67809239295382,51246856281508,
    38182266543262,28053342682232,20329769429912,14534427945112,10253318798420,7138460546058,
    4905366751680,3327660232996,2228337856516,1473008581348,961114349668,618710105960,
    392775432408,245841538566,151372006416,91735401592,54441215076,31488749944,17669615620,
    9407610520,4535981480,1949697232,479607016]]
private def rkmC_w64_m32_s5_10 : List ℤ := pzigCat
  [
   [658098961,1105627101,593305077,1010402724,2523989686,2755032490,722876882,2829099263,
    6257862741,6710089103,2175496575,6118562054,13623802978,14633625228,5832395516,11075155587,
    27876393089,33139359639,18206210109,15533809786,53856211266,74249597914,56611728522,
    4737851391,90363385301,158765416393,161896333013,70639917455,101396119424,290635365526,
    399513597950,335869306252,63172359600,360944980637,779822729067,981393996963,779555641629,
    110720198539,896507313888,1913753274860,2489373690884,2199634730436,831388391480,
    1465621434149,4124178565827,6243724951011,6817461466299,5052378315879,699973508281,
    5708357602782,12812166474500,18607208840282,20850019209892,17609604912976,7845385511522,
    8132264828187,28434570974467,49676750722699,67375679009327,76599818547681,72752360657839,
    52345286202977,13618828370443,43099747138958,115355126775870,198838326275780,287917278070062,
    376324250043344,457890114336412,527210303447680,580159977959236,614204339794014,
    628488083244776,623724905458030,601931675871966,566063097991904,519611873377952,
    466223961445672,409372113873154,352112549386520,296930273828654,245674148126858,
    199562192629340,159242789208374,124889179522378,96309693397828,73058638186072,54536638329504,
    40073792068928,28994807294094,20662450096410,14505997803252,10035028576788,6841626052998,
    4597693190512,3045642837456,1988844104328,1280237411690,812060937984,507590619058,
    312354019322,189172807014,112565004796,65564379270,37330977860,20450590768,10711920838,
    5126901970,2146135638,491913814]]
private theorem rkmWC_w64_m32_s5_0 : bWinChk 565 26 100000000 1024 rkmPhb_w64_m32_s5
    581 rkmXsWin_w64_m32_s5_in 612 rkmC_w64_m32_s5_1 4921142051 = true := by decide +kernel
private theorem rkmWC_w64_m32_s5_1 : bWinChk 565 26 100000000 1024 rkmPhb_w64_m32_s5
    612 rkmC_w64_m32_s5_1 645 rkmC_w64_m32_s5_2 4949349438 = true := by decide +kernel
private theorem rkmWC_w64_m32_s5_2 : bWinChk 565 25 100000000 1024 rkmPhb_w64_m32_s5
    645 rkmC_w64_m32_s5_2 673 rkmC_w64_m32_s5_3 5121646384 = true := by decide +kernel
private theorem rkmWC_w64_m32_s5_3 : bWinChk 565 25 100000000 1024 rkmPhb_w64_m32_s5
    673 rkmC_w64_m32_s5_3 700 rkmC_w64_m32_s5_4 4845898023 = true := by decide +kernel
private theorem rkmWC_w64_m32_s5_4 : bWinChk 565 25 100000000 1024 rkmPhb_w64_m32_s5
    700 rkmC_w64_m32_s5_4 725 rkmC_w64_m32_s5_5 4590776323 = true := by decide +kernel
private theorem rkmWC_w64_m32_s5_5 : bWinChk 565 24 100000000 1024 rkmPhb_w64_m32_s5
    725 rkmC_w64_m32_s5_5 748 rkmC_w64_m32_s5_6 4109862230 = true := by decide +kernel
private theorem rkmWC_w64_m32_s5_6 : bWinChk 565 24 100000000 1024 rkmPhb_w64_m32_s5
    748 rkmC_w64_m32_s5_6 770 rkmC_w64_m32_s5_7 3358459018 = true := by decide +kernel
private theorem rkmWC_w64_m32_s5_7 : bWinChk 565 24 100000000 1024 rkmPhb_w64_m32_s5
    770 rkmC_w64_m32_s5_7 791 rkmC_w64_m32_s5_8 4221848669 = true := by decide +kernel
private theorem rkmWC_w64_m32_s5_8 : bWinChk 565 24 100000000 1024 rkmPhb_w64_m32_s5
    791 rkmC_w64_m32_s5_8 811 rkmC_w64_m32_s5_9 3953680830 = true := by decide +kernel
private theorem rkmWC_w64_m32_s5_9 : bWinChk 565 24 100000000 1024 rkmPhb_w64_m32_s5
    811 rkmC_w64_m32_s5_9 829 rkmC_w64_m32_s5_10 3927933695 = true := by decide +kernel
private theorem rkmWC_w64_m32_s5_10 : bWinChk 565 24 100000000 1024 rkmPhb_w64_m32_s5
    829 rkmC_w64_m32_s5_10 844 rkmXsWin_w64_m32_s5_out 3941483998 = true := by decide +kernel
private theorem rkmWinIter_w64_m32_s5 :
    RkmWinIterSound 271 1024 rkmHbWin_w64_m32_s5 581 rkmXsWin_w64_m32_s5_in
      844 rkmXsWin_w64_m32_s5_out 47942080659 :=
  rkmChS 271 47942080659 (rkmChS 247 44000596661 (rkmChS 223 40072662966 (rkmChS 199
    36118982136 (rkmChS 175 31897133467 (rkmChS 151 28538674449 (rkmChS 127 24428812219 (rkmChS
    102 19838035896 (rkmChS 77 14992137873 (rkmChS 52 9870491489 (bWinChk_sound
    rkmHhb_w64_m32_s5 rkmWC_w64_m32_s5_0) rkmHhb_w64_m32_s5 rkmWC_w64_m32_s5_1 rfl rfl)
    rkmHhb_w64_m32_s5 rkmWC_w64_m32_s5_2 rfl rfl) rkmHhb_w64_m32_s5 rkmWC_w64_m32_s5_3 rfl rfl)
    rkmHhb_w64_m32_s5 rkmWC_w64_m32_s5_4 rfl rfl) rkmHhb_w64_m32_s5 rkmWC_w64_m32_s5_5 rfl rfl)
    rkmHhb_w64_m32_s5 rkmWC_w64_m32_s5_6 rfl rfl) rkmHhb_w64_m32_s5 rkmWC_w64_m32_s5_7 rfl rfl)
    rkmHhb_w64_m32_s5 rkmWC_w64_m32_s5_8 rfl rfl) rkmHhb_w64_m32_s5 rkmWC_w64_m32_s5_9 rfl rfl)
    rkmHhb_w64_m32_s5 rkmWC_w64_m32_s5_10 rfl rfl
/-- Certified `w64_m32` seg `5` (`271` steps). -/
theorem rkmWinSegWalkSnd_w64_m32_s5 :
    RkmWinSegWalkSound 271 ⟨1024, rkmHbWin_w64_m32_s5, 581, rkmXsWin_w64_m32_s5_in,
      844, rkmXsWin_w64_m32_s5_out, 47942080659⟩ :=
  @rkmSegWalk_mk 271 1024 581 844 47942080659
    rkmHbWin_w64_m32_s5 rkmXsWin_w64_m32_s5_in rkmXsWin_w64_m32_s5_out
    (rkmw_buildHbFrom_length 1856 1024 19586394833 1024 0)
    (bAllT_hd (bAllT_tl (bAllT_tl rkmStatOk_hiw64t08)))
    rkmWinIter_w64_m32_s5
private def rkmC_w64_m32_s6a_1 : List ℤ := pzigCat
  [
   [397177143,1433761818,3460194563,7257455838,14506372267,28242734558,52665676853,92293613150,
    151546144205,233191927088,331752022165,429132219932,500357815111,511667678574,433266516121,
    282704254104,110741344621,8789812933,752309077,102832107642,161906402639,68282346618,
    214493650992,490093225389,468385244978,187253107777,92791870903,29500096804,523109082054,
    1101917511389,1397660348116,1439820355361,1109455039100,833663578833,908538302252,
    1187041563881,1892981356806,2460189982813,2527183205814,1385023723073,2320003894199,
    4417201135130,2153718557879,215418091116,1875385511866,4644066540093,2741788768432,
    1010624597144,672816661722,3644775833379,999349496405,5065663864750,2453333556175,
    94209896802,3644680636194,7481097686525,1392072432001,14691780627216,3403107765814,
    13073860542109,3009123105253,10991671307806,8422353090648,5180281864474,6994779490674,
    488171234039,11105314551737,651131785523,28727850599820,43312993442514,22338014677810,
    13769361567855,26327172710613,1270128984182,50711204859170,88665965894080,93703371379004,
    67900553861074,30754779350782,5818317044990,10158008584578,50300624337586,123255228317280,
    219734078412108,327508354460304,434046411042596,528334768359156,602006345281690,
    649902233181506,670144996637314,663809142205338,634292284841104,586524631639136,
    526149330866066,458793408541500,389502875133568,322381276485108,260424259625110,
    205522704155296,158584033786192,119725828954024,88493503059770,64071465142766,45462267186216,
    31626418529098,21578165929764,14443614132472,9487497014956,6116672772050,3871266617062,
    2405210428936,1466985328844,878243440854,516056748342,297308089510,167727506914,92468399634,
    49384409312,25442373412,12302123008,5411090618,1990293400,374004164]]
private def rkmC_w64_m32_s6a_2 : List ℤ := pzigCat
  [
   [751927146,2531041127,5576175844,10445965457,18149960500,30183861121,48491039644,75298419675,
    112732207134,162122070185,222978641410,291794798255,361056610438,419077271963,451347589464,
    443861694805,388199572462,287047674561,157621866380,29846538893,62811306081,98517365976,
    81849100487,48138366280,49424606063,123943221116,265033113149,413791642670,492155025055,
    466221901652,396443182533,421154570960,658815955909,1088878797870,1517972587689,
    1694538982242,1511803436993,1131216865092,882101134067,980438961126,1311704997387,
    1494080819604,1168872610083,265692229242,942503728266,1974618007165,2307034181790,
    1525518349069,378563175849,2698815166920,4187516430127,3793380461818,1529905957203,
    1221737738609,2650343997232,2063553996229,511393669704,237766163798,207994948086,
    307526539737,884771839973,2095823009222,1669404588985,576720006979,3105329593036,
    3358125937239,257008455323,5143304747490,4358414490793,3127892245613,6530046380966,
    771357332877,4700238023925,4155232756764,378035992166,5898035840887,4060194614214,
    6048246381784,7318765891475,5555140470433,8978967300812,5521948118820,8456518389879,
    5683921336659,5783072288102,4750581516312,2267160344291,1928958827519,512935297613,
    3661483736249,1288302091567,8820787589190,9627361551910,6292052207145,18133666952419,
    5003353309213,20788450212622,26755976722354,2499416308818,25679581321575,25155577481649,
    6489069110518,39749095500496,43891501202068,15522506190872,20699564607525,34678099031195,
    14032700084965,29520295443926,70958452697270,88664238557846,75684931785624,41103466505134,
    3867662299686,15819754874455,3373021459797,46834110189534,131446096352988,240277415319178,
    359392105608782,474182271396860,571875061500512,643203266760086,683178189419918,
    691054191612948,669672967977270,624428315340390,562097559598022,489747874717010,
    413866646115428,339783085190842,271391105772812,211126556077802,160127499709786,
    118501521717656,85629777391564,60454837331614,41722696209844,28160491876344,18595059279206],
   [12016633300828,7601398670078,4707691188170,2854889648884,1695298181006,985530537280,
    560846610046,311927263096,169331154334,89565515022,45792236724,22314724444,10138988442,
    4025460434,1097741070]]
private def rkmC_w64_m32_s6a_3 : List ℤ := pzigCat
  [
   [878584919,2812902138,5866058741,10461144762,17400007147,27667719064,42284002201,62354654970,
    89195562011,124135387658,167767604499,219061705236,275015614859,330749628672,379329372625,
    411764328446,418609075103,392688421738,331249891705,238101014758,125328875403,11431053354,
    83150059840,141971500371,160493898734,149510992457,134064756282,144271343629,201739097940,
    306941143959,435901479204,551267277153,625373097338,663268080909,708750322590,822233618569,
    1036441180902,1315918643015,1553985135450,1623912427365,1463163135106,1133962345521,
    802630373086,629250745915,634043225942,648704929149,419733592080,182815869806,1000568075961,
    1611639104972,1561602628963,657428368842,873782847712,2459851700827,3429788696998,
    3291945248909,1950172128018,180929807418,2234867136397,3230481388088,2637039438563,
    818696118952,1087634324756,1936973402349,1443537543626,364331465205,258523836243,
    121867290636,98267981968,378648274394,1322636001271,1477592068284,10396044436,2170529747503,
    2752990797938,634132790781,2537479262245,3614524661266,1135992121547,2835814864739,
    4317320147234,1243237204823,3756794366635,4957830665994,16952084997,5482281978159,
    4062516627786,2837791278386,5872140563941,1002845128782,4795456118752,4006089454283,
    1673559981307,5263704340934,2150480989631,5053918527737,5505162952784,4187075045878,
    7636403660619,3291401153387,8317545337904,2576542609590,7819454873001,2092357842811,
    6522418062346,1840369238058,4497868200699,1368789945233,1871750277646,305956885497,
    314091140804,3633777804270,319122335939,7607097487491,3117624678177,10011255326348,
    10159352621208,7332274489265,18019554665401,3443307961087,19115302623506,18419505941410,
    7528603229035,27073720221265,14701662952305,17204321353444,33007089728884,14601896911862,
    19384975768185,34322486219331,14622605395217,22711073295216,45568233044698,35223340187628,
    337066628592,32032236605505,37478270019503,10302927575793,34896482599250,73946346700890],
   [87270374919002,69285382154432,29674339462896,11957377530281,34175110060535,20887352296539,
    34510162142442,128426827008234,249082951763216,380023268039960,503957212416924,
    606027419398708,675979083685426,709067834235816,705825628210440,670995421624476,
    612023799709742,537484258480470,455714148456304,373839539744574,297235070923718,
    229379918227258,172014071161502,125474086045338,89101403940500,61639438730300,41565277030600,
    27334385310512,17537480185284,10981131827644,6712031764572,4005425832388,2333743780550,
    1327487942266,736905889526,398865666710,210218061412,107612332672,53184997890,24991538022,
    10777259098,3935680704,964022484]]
private def rkmC_w64_m32_s6a_4 : List ℤ := pzigCat
  [
   [658484573,2070139302,4348456757,7941971148,13364181849,20977381940,31350001551,45610429628,
    64837920973,89481923320,120181559035,157605020720,200893919461,248362270416,296663757337,
    341293374052,376360340803,394958560620,390476035409,358560639254,298442021273,213507984354,
    111962524721,6686117058,87353578168,157152114917,195545637266,204741714105,197240218354,
    192464867025,211337249068,268637913695,365615719736,488849120655,615024196646,722844391093,
    804653990166,873029189199,955621861946,1077507907629,1238413806274,1399454979903,
    1491272528072,1445257240553,1235374656818,904859808907,553545362768,284400658977,
    136681972832,51225387513,94265481385,386382001634,772878159011,1034847343862,883265955929,
    146160105478,1064999935162,2329848714647,3083375956764,2893349518205,1698731494264,
    127338901102,1920388525035,2996598406562,2931475108161,1744947517958,70407506534,
    1716043161325,2438024131212,1935872766179,581497379710,773442179094,1358623909517,
    1027625304506,315006931903,91241275795,6983623182,108842701164,274111237544,1026005088611,
    1296273023998,363101664649,1372443053965,2397080299348,1411418506505,1153363305471,
    3100789506312,2368521143799,757992320147,3491315790798,3038959795485,486679614457,
    3799027776246,3453468926199,558812828963,4302430570690,3583760980741,1304948856529,
    5068612683070,2982194939185,2946123230943,5450980271410,1031681961321,4778356499419,
    4303065621788,1754857054374,5263809370241,1819788938916,3814077062734,4393469967385,
    874790207505,5292762366396,2397683966569,4694872342705,5148929154962,3257813219914,
    6960190874505,1710115149467,7725253497078,545328409840,7498703752847,109768685368,
    6453383286834,412705212697,4868915840183,588667643290,3017580536828,818554127509,
    1008315221663,1399214056514,1088942611641,2898987702475,2758232765844,5779731246770,
    2797079198537,9583350426979,62751799589,12607093393086,6136038120536,12414517877211],
   [14157857506809,6540929606790,20543665772264,5819021679604,19274528435667,20265317906079,
    6122897135592,26805701933582,14885499796784,16539941038797,30594686219591,10242956280257,
    22969420239746,33698745159140,10464073003086,23883821250455,36126985575837,14156803042507,
    23595116391374,45898786861040,34964558172182,810934215015,34946663657381,42553647594505,
    16383776027097,30184294341196,72507256394396,88824081622504,70994391515086,27464729705362,
    21181011038709,50695372128865,41658596398241,14885888451738,115774416581498,247636279955242,
    391067244861602,525508520753590,633504572385254,703505298926810,730931060958464,
    717679520586704,670549288908586,599163941375550,513925007985316,424368501647188,
    338110709393294,260395599991342,194135402258450,140279121415100,98339068478524,
    66935369992478,44265967989076,28457837784028,17792467802020,10822178402000,6405223677808,
    3689222736674,2067697081716,1127420142520,597764942024,307816034462,153610993544,73644498858,
    33706861472,14378132424,5348032226,1513499632,203646718]]
private def rkmC_w64_m32_s6a_5 : List ℤ := pzigCat
  [
   [576994529,1807238392,3878176167,7206613248,11969894571,18291915568,27015959963,39034766482,
    54449098089,74221624596,99026726759,129244676558,164585121317,204288056268,246938825983,
    289832068788,328917751607,359588527152,376910671657,375554250670,351339640865,302947118844,
    231908009353,143137454386,45253018935,50812868169,133291763220,193517504125,227702849654,
    238538506215,235824437834,235177941645,253496919194,303533223163,389360558580,504129300617,
    632450436430,756196118357,861289886830,944705820759,1016018370758,1090919775299,
    1180117083916,1276581237479,1350665301362,1356550375169,1252301496542,1023674607385,
    699471120410,347185708575,45613566368,154748158250,258916186053,321139313224,401709396621,
    506676262758,551271068793,384228366954,122606541212,958838648305,1908081860550,2590153844073,
    2617825546882,1803641469045,301948673652,1405105161420,2691300995387,3055804769882,
    2348019424469,839422966234,885399662530,2163313183207,2516028192012,1845976018459,
    488436818004,919405082222,1729368226425,1617255381004,769390004825,233329344891,803121152638,
    748545211865,368358357116,131500366383,207050527878,292439006555,43294977293,795568286708,
    1332823711695,902423748640,534669770720,1971610528793,2046231817680,321982270131,
    2016689123333,2929900766532,1328839754461,1672975009163,3450378867048,2185225116655,
    1233919060513,3723891892584,2788124160169,927501417141,3937433684776,3147312156059,
    921619123615,4264048430330,3240007062137,1398745615633,4751782632512,2850012873571,
    2492882162503,5107003693672,1616329851291,3957117683167,4679356273748,478938002832,
    4975964350621,3058522598358,2690679332878,4818743898735,726545733898,4225557032594,
    3663559437967,1842254799921,5129044498800,1249304254015,4952977029355,4053916466078,
    3566528955986,5984909714255,1644725779115,6886642317570,184782585061,6880904216653,
    1503101413242,6182410495612,2154051452971,4982640102013],
   [2220082909884,3432524055460,1937543975315,1670381406981,1571679488112,184990090569,
    1335078856633,2094227644494,1445689864276,4082438558931,2270779513649,6015411448210,
    4311921699526,7273142009801,7810014408385,6724847538480,12184353560186,3258383785775,
    15837933643745,3459334302897,16497393402500,12404287185928,11807744904457,20621123244861,
    560390467640,22984844729994,14759209446022,14495711660621,26345398308791,4448608744571,
    24493890680614,24697933609160,5022235031731,30679249054899,23000865860439,10331469642092,
    34366376619400,24252644004506,10404186686357,36525547386203,29454954776369,5577082988002,
    39666931612710,45273452255022,17632629530940,23073557802009,47459568529989,37110881641983,
    4476201136758,55292395612846,88216488235546,85590091013096,47552970189278,8570654915141,
    55937507977161,68561255722797,30079432018833,61770071430844,195548597441260,350300882416134,
    501571653765458,627260477938152,711856938072794,748384658398604,738130992928276,
    688762542314786,611650559433478,519182895080012,422616505014438,330738673268858,
    249347115945388,181382710913530,127471793508808,86636855698350,56992576093738,36311096774450,
    22417335338658,13415536237266,7783905709096,4379182572712,2388874645096,1262998427068,
    646831797738,320275839378,152892236996,69843963828,30295317896,12036581902,4125613150,
    869537832]]
private def rkmC_w64_m32_s6a_6 : List ℤ := pzigCat
  [
   [698102476,2082238973,4183618036,7387108679,11991772756,18114141627,26228444284,37105806811,
    51044283960,68440152379,90306522356,116639879325,147408728210,182232646759,220198548494,
    259315890309,296909307706,329832266217,353893311584,364485731193,358047926904,331758700281,
    284052326824,216463278315,133302516444,41605096985,50238341191,132689320546,197489976645,
    240288707268,261537611009,266901578166,267221951231,276117101676,306741841009,367654484386,
    459702555669,576452006522,704528247311,827927973064,933685016843,1016918571572,1081290199403,
    1135651728194,1187135627363,1233543839620,1259049596187,1235655769700,1132962256523,
    934000581256,648172068105,315408994372,3625939180,250299328237,391264577950,431524651929,
    405945881364,351118657043,270514912772,118656534037,178982089787,670637327424,1311460495191,
    1928875676568,2256569881829,2040095938392,1175939409115,187515326447,1653584886952,
    2707506371923,2928605230666,2184986585905,715395834184,951167722636,2205446291905,
    2603653254738,2040530825475,781869335716,650182474310,1688525597621,1949267833762,
    1390764416169,331103733824,701124849770,1231782505731,1092363537326,499302064925,
    111028381297,396342899820,343309452905,224391071924,296510554335,502383986646,481796758973,
    58406443203,928836757730,1441616715567,940682665408,506354411894,1919321456469,2058985315994,
    514761093917,1713769823237,2820608519056,1675423129167,1028699552417,3106358815946,
    2650469407447,180306219725,3044212817888,3333998250541,589668885964,2843980894110,
    3774007885287,1152572226386,2702497288628,4077730544895,1444007703376,2778475810282,
    4323901145701,1383507599270,3182201706860,4472866645367,830862059832,3898580179084,
    4294124151455,325445790909,4653528392422,3454483088467,1929984923823,4934136669314,
    1844382313531,3462901444401,4357732345604,195723165388,4413138086265,2999028625026,
    2266199247386,4673842498983,903231224618],
   [4350785339786,3786121693193,2431480827689,5515525637014,235236134875,5847641527465,
    2800842868840,5035068115096,4685989670809,3574921477623,5645336473988,1974203416712,
    5694396723993,600934303969,4990423648582,372241639403,3736890310529,954164513842,
    2133815382182,1273427365211,360836726517,1501529205820,1439772311007,1800503047567,
    3185737132488,2334114343698,4843793149233,3329754589055,6324630169128,5092686520030,
    7301896533783,7846497832893,7112750265778,11415409156672,4929328974783,14960007115659,
    206974388128,17021695995186,6845265683096,15869488686475,14948102192749,10001872465534,
    21500359173456,977283219758,22634966074537,14813984728819,14736696918042,25534901728422,
    2096582421154,25400580234339,21200712021889,10227401130138,30566460313640,14933424478864,
    19140115781095,33130073685203,11117308489297,23886143667044,35583688993172,11710869160716,
    25021966692305,39968497251527,18618726873425,21675680258186,47825464066740,38416769025984,
    334047583421,40399038653821,52476874130171,25460412694489,27350842479646,77102779073224,
    96123522845956,72548207049972,15942635231228,47265666753409,84964183459043,71573742106675,
    3452271387770,133186796742878,296551072065518,465266940680104,611652146216608,
    714880079253344,764348373829748,759959555129206,709997964616432,627738107674870,
    527915019310788,423886661917650,325894797461154,240439354885012,170521633310972,
    116408105021168,76572010856456,48572147281768,29729529309336,17565077770954,10019980663154,
    5519193565124,2934965903916,1506192614916,745111992860,354785611612,162044311516,70485900948,
    28865350996,10761118036,3147543640,563836444]]
private def rkmC_w64_m32_s6a_7 : List ℤ := pzigCat
  [
   [217693239,909582728,2602066745,4926592764,8250076473,12960163876,19173155069,27174746788,
    37625312701,50977683352,67439274115,87652298344,111964645579,139957841612,171737265873,
    206433792280,242445693861,277683968122,309763234945,335256282528,350368442101,351976784062,
    337010138049,303242177720,250829668517,181675871134,99994876809,11768300634,75069774696,
    152721137501,214915712882,257652530153,280997853464,290081667775,293582667808,302521295595,
    328393981530,379962463741,460584701000,566478920795,688602747418,813665891475,927698085824,
    1020733210317,1089407814008,1136304376937,1167175287006,1186044981105,1190366247688,
    1167717817577,1097963805046,961738769721,750000953762,473417464267,164392905134,128372589974,
    353612906295,475489063636,486186794171,404731973784,263184713795,84706666910,132855183472,
    414430612047,783458157320,1222350746605,1641434848462,1880259759407,1757362616606,
    1156025594665,112083704842,1145972121660,2241386558205,2776049469464,2496145799991,
    1423330988014,119393539526,1610758222063,2528107708218,2555806794653,1711994953872,
    338519846181,1039996482601,1923043047598,2024503371813,1371505484714,279331388051,
    784836798385,1397558132154,1357570073945,768361434976,23737469536,619159878215,784051551382,
    566726117917,227294039638,19932774839,8515683465,34454111218,253674838761,625343700826,
    815755914233,457560004810,450359082122,1368005516905,1518376199292,529000801403,
    1101220926685,2197019214930,1760000305159,130621907841,2167718693674,2707336458069,
    1116131190494,1532205145808,3137915540859,2251699239382,587875167204,3099829950921,
    3083962769852,383107785687,2781779080979,3604629910086,1206614816971,2390194269501,
    3909182538346,1809815077387,2095759131211,4119902549562,2168352431569,2026779102877,
    4325408064444,2244200470897,2272745978307,4528005653902,1950812756113,2852144741217,
    4599717257086,1184785817817,3640122262877],
   [4304465303376,51908168370,4335819992281,3446719925324,1540159191390,4597533810077,
    2054390982886,2940230943600,4273282444397,315194549366,4059062615504,3337411201017,
    1755970109547,4748822875244,1414001116123,4145362287555,4130820471146,2001794294388,
    5546067433367,767767166944,5465443094520,3272761419329,4215280751411,4932418353048,
    2372889941450,5547715494597,513936363001,5219045132660,942446011995,4203667890837,
    1785719680012,2784786825060,1993538729473,1190460337701,1676813085700,433904805165,
    1015551556505,2016539623536,202246795008,3543157566021,596158320246,5050482415118,
    1239565847593,6624050602205,1569125990876,8368906412680,1339872602695,10313503107239,
    196193677020,12259577251200,2229552759238,13668019660965,6089953879727,13701129038878,
    11073208739988,11449448575325,16267815467259,6255986790268,20174305926218,1935600580772,
    20807179327749,12096526827139,16079721060318,21494435157558,4966133730127,25661233158171,
    10597961415831,20135481558466,24593795382758,3931672376731,28567088168233,17395346828047,
    16308468034862,31535877981990,9580121486312,24707368143101,32585930930501,4790470912179,
    29533010714228,34639594138434,4590747571174,32040373622013,40482277747139,11712701556893,
    30580391898034,51213299591388,32456676713490,12750559855519,51328852246031,54017160739089,
    14952212214347,45137308426270,92025756671930,97839614768596,56129186880440,14814150541395,
    80360794586519,104282698770935,62756574746349,47729431331194,210465443788472,395164013036962,
    567734282961096,699488812132018,773156260900362,784706783258734,741517805150470,
    658314112896786,552529668108866,440394927760882,334456029233060,242623739370056,
    168441848962666,112075787816612,71545424009552,43851972482074,25819608428786,14607677861390,
    7941401542622,4147581308826,2080028493792,1000404193564,460716035138,202547687754,
    84374497496,32819044670,11534930670,3334112316,555079624]]
private def rkmC_w64_m32_s6a_8 : List ℤ := pzigCat
  [
   [494395976,1497699443,3204666996,5914590671,9575076552,14358389737,20853001390,28982958629,
    39393448296,52548691411,68594911172,87907144063,110979092202,137505572275,167090650610,
    199466270173,233019987916,266136570257,296679243986,321898286503,338471180974,343537796751,
    334466512760,308888269477,266194971424,207352925257,134620681492,52767073497,32153571841,
    113430190026,184781189607,240736911578,278939918989,300724892210,310453806555,316085941610,
    327909672071,355575807642,406389908849,483463142026,584746307163,702012697760,823718449015,
    937309232814,1031812015393,1100844758618,1143624569663,1163568081766,1164745676393,
    1148225187162,1109939901549,1038601856738,919945728067,743532303574,509998962985,
    235908271704,45586493870,290785695933,457376273760,518084165389,468022842976,324178897085,
    116881856932,125544412116,388377249945,672228464208,978534686503,1285664827884,1529397756975,
    1603749700570,1391127391857,818386350752,83311523960,1144462796547,2078542330254,
    2566223883517,2376674513344,1480955658749,99810183622,1346804568820,2380426248221,
    2643975130752,2046607066773,806735886914,627161785068,1748195983175,2183603272926,
    1828719016131,872579730152,289644149164,1216140720299,1588325677598,1324386897085,
    598017165284,246116765376,849075244369,998813014956,718185137031,230912627422,182945338238,
    358016584873,328578703318,262227907649,287743833660,356445636521,268313800652,127141840806,
    713078908741,1084418481268,815255655567,145526887095,1281680649284,1762944737647,
    1052200016616,568749324062,2033753548573,2190417977382,717293889653,1468418263073,
    2752696650082,2028208742111,336721194825,2611859272766,2963299642261,956421462560,
    1938328040712,3390722981833,2099148984880,1009257482316,3387751558161,2949591149266,
    66240376830,3128919415263,3510097381978,739247253483,2798026218101,3860579544840,
    1333538895687,2547535238431,4096730449342],
   [1680839494215,2487788548533,4279863482466,1743191687375,2680708057601,4401822186440,
    1465826883065,3117135768515,4369776256504,806888128283,3685866906781,4039641192364,
    196408961158,4182156913519,3310036814636,1388818724354,4400354182839,2201822434902,
    2575778708810,4243648863991,790014930242,3658503061718,3644752444697,983539804747,
    4530607875012,2269172738873,3193177719981,4582981847346,414148046808,5127960227983,
    2591104657682,3935063409738,4781245622443,1652368557931,5631714192502,861328188511,
    5168085158545,2882887213226,3792546600094,4002618954837,2046781485489,4136603505230,
    416375232340,3434396989665,775896508454,2156488707798,1394043717117,571275745757,
    1457894713402,1107703167019,1085827383589,2743641641208,437814648824,4275666791855,
    327842795854,5709815246498,1071787474695,7109567526965,1660578680174,8576372194446,
    1928269120571,10203955502777,1638938966396,11996882198080,492029736213,13772275172031,
    1797449775351,15100041656642,5352798119880,15336481156381,9984130998191,13753336383302,
    15092128757878,9715766851763,19623137747871,2899011810158,22047302442622,6363645876372,
    20471308279873,16527409068747,13250276334930,24414778272066,324451682425,25745260869665,
    15295383858775,17176686610986,27263891229038,781770839062,27903311340991,21535867563689,
    12584550881560,32704040748896,14094505501212,22154879962775,34695035959289,8867132954731,
    28092756349242,37160392279956,8008424302584,31525927642033,43357736424929,14908273836655,
    30265119717410,53759665251552,34643312133532,14141393725105,56220895776987,58683247251445,
    14969860084421,50980256546328,99949949141784,100900701416240,48602785467030,33194373833169,
    102889976736675,119430640316901,58904409473575,77270019561706,264408525411746,
    464338270619454,637997697969538,756083450983600,804786587813054,786044546114036,
    713636553146562,607357415775738,487402026726828,370357226743868,267280958840406,
    183611323202512,120259267926210,75183348279608,44898339699314,25622327086466,13974224259024,
    7281986019334,3623423250464,1719849047968,777316422644,333561265408],
   [135015605648,51140412962,17580312422,5085082222,782568648]]
private def rkmC_w64_m32_s6a_9 : List ℤ := pzigCat
  [
   [225240726,907997931,2518408414,4684352377,7781260534,12038460983,17442030460,24337107775,
    33244546194,44261883081,57736417170,74282214229,93688282010,116408351209,142393943782,
    170994668001,201532411134,233215444159,264122023886,292127878479,315201547326,330308085505,
    334898238792,326546622285,303430369996,264546954827,210624794082,143616679581,66786066996,
    14625695018,94871578163,168419342400,229760435217,275740256258,305970459345,322855638196,
    331619399001,340516060750,358266321149,392806448554,449989199525,531264616826,633223913693,
    747955218750,864963859221,972082061234,1059210963987,1120225993164,1152921618941,
    1159045160698,1142476653323,1105618917576,1046796586925,959953985004,836753325853,
    669263659106,456857146475,210711364056,44961935350,275640922723,443514562752,517606037959,
    483433965168,346837106175,130790431670,132017434754,410800895707,684264804308,940797586473,
    1167814575636,1337813606413,1399965828096,1284026219849,924020422712,297920697881,
    534157593807,1413330154472,2106602830429,2371913281086,2048988278123,1141677198340,
    147538226070,1457197484847,2376993388858,2594433129103,2018656414174,828833328931,
    578923401607,1732095812762,2253910347949,2000514971592,1106563843971,75385035433,
    1114384777444,1662277127361,1574637785032,947657491635,65475276700,719908509136,
    1128379571605,1055773200366,603337372919,16581665728,439497682684,608842411959,507513599654,
    284767525749,103099489010,20002019389,40551771987,196251741930,459771352697,663815319850,
    552034743161,3869062858,777526967784,1299092320661,1083024228226,65735416855,1221723479847,
    1907459575838,1373198440111,211219430807,1859277325396,2373882990075,1229630560776,
    921209682680,2583754461749,2463267675512,492478826307,1978505431725,3089040468070,
    1883581521751,845656934243,3037005092898,2913337753789,449608296150,2470129061356,
    3469531941533,1629306945056],
   [1634077906318,3613731830087,2555802864852,749652833646,3493196015993,3211881831520,
    31559315491,3270169510213,3647856477860,622152099735,3082142108537,3930452170002,
    973526612075,3025367437051,4102974536432,1051781579553,3144677507791,4161318318630,
    830873929535,3423443756405,4054136592988,310243359615,3778038336631,3711360456304,
    458094827650,4082948884607,3095508203948,1370758576144,4229670777729,2224203834900,
    2331944743222,4165611571535,1103748933588,3313579067668,3810032970507,374981650777,
    4250281557798,2859763649095,2337860594153,4705084890132,817654186307,4410224292137,
    3711708618248,2304835858526,5219165052539,599264738348,4979842428840,3188452050551,
    3348716663293,4697489453102,1078412048428,4885962407799,1045022690240,3969944704602,
    2457737450199,2423571477299,2916001899274,765298390938,2460589039575,593658631708,
    1312499436146,1417409071771,241906398562,1642496809426,1938433680845,1334022714185,
    3584505478156,627795419156,5075157178929,320521642120,6388268774128,1366121625669,
    7571837159829,2381918282934,8726179077654,3242663560817,9976760654983,3795364150646,
    11431795376352,3835705839511,13123312014453,3112979579346,14944532454598,1376587285499,
    16610323788865,1543327930329,17662885153166,5648326217246,17518476309521,10697132961047,
    15532306341888,16125165073390,11092158170929,20925519041367,3829448011786,23546496858112,
    5942003389160,22039984767217,16628629334639,14777027253092,25052373315210,1724448680361,
    27057480046121,14309864809385,19275571170950,27373958539358,1655579539277,29772166271063,
    20048011617517,15965686575882,33709054963326,10924318106062,26198268537111,34656285972691,
    3915463787979,33140184051016,36552227725596,1240877469080,38492396815921,43362892316027,
    6532669907185,40557504566058,56480895512506,25275700406632,30556969783845,67773116421975,
    54877196404829,5178236956732,76719806968346,114224304190308,90348380662564,12350761716826,
    80915519225389,137756085936403,117121639790859,5428948521361,179583368302814,397435043301298,
    600361827948684,748599510237172],
   [820173287030122,813214049769050,741968067706502,629470011469322,500025131084166,
    373699471322598,263654700131920,176019209680826,111376809688816,66861698935588,
    38099901180522,20608780737886,10577354270356,5146691415540,2370537027592,1031193455196,
    422023685744,161634211548,57099137568,18043050618,4631721676,603686892]]
private def rkmC_w64_m32_s6a_10 : List ℤ := pzigCat
  [
   [605801248,1757715953,3588830280,6354543449,9928823772,14504164867,20646897604,28115148211,
    37503891566,49153262467,63160880044,79878628473,99660157678,122244061427,147546752770,
    175434664305,204719463396,234614329371,263584449286,289555968467,310411475420,323991188797,
    327560720472,319039477373,297036104172,260372071845,209687824200,146532063217,73676636132,
    4607093298,83013247761,156723576688,220833829843,271490435486,307659948017,330296792790,
    343137818315,352470769628,366079753161,391371044672,435021886421,500608162848,587536564209,
    691450075974,804064277897,914721030678,1012338099167,1088279182096,1136455069481,
    1154982582928,1145886422411,1112208825624,1056433848967,979011683020,876657606845,
    743854216798,576237563817,374602626834,147948733153,83508935405,290752885478,441379166583,
    507118636424,471146734461,334052583466,114618768085,156728591723,445013713238,719203223577,
    956715182720,1141578227243,1256267107816,1273573168151,1155277317570,860625337479,
    367220672274,300426263274,1050871497291,1726076549660,2132788720927,2100065264398,
    1549458410269,549523110614,674692282042,1790522198535,2456559512850,2441076286155,
    1716183356644,487466784431,863748449091,1906481816498,2311511475927,1968789624640,
    1024658705301,175081978833,1214864948330,1759965668405,1669614217974,1034272850715,
    125472989978,714735241770,1201771301393,1206453490252,789164374405,159926410972,416309828280,
    732260054253,718960296854,458741148629,123774055378,128051980356,237313575861,256460758314,
    280546524685,344468481936,369512223325,216483078636,177798953068,679584574443,974171288840,
    754270018523,21789909457,995176234506,1549438053395,1199990357056,9282553354,1411941318133,
    2071901751386,1414833762007,287053011493,1973691655206,2453591686969,1258170162224,
    920639017908,2601563335095,2524875481502,613908376837,1851319828259,3075190632900,
    2065296001259],
   [541688679321,2842123987836,3048864837361,900650414024,2023936501584,3439907651537,
    2149231047090,914775582388,3317512514803,3046999795278,225967426721,2860354778441,
    3584998233772,1231216736311,2260627623609,3843902230998,2026079297039,1676807272877,
    3937473693826,2597360152365,1220350280329,3969507936124,2957338371741,960851825727,
    4010756063600,3116516306661,932522729307,4085340705970,3071413650935,1135169761961,
    4171111226866,2811664624299,1531777937649,4215268176304,2339485274989,2055678807351,
    4164953395696,1679200165869,2642709965499,3992269909708,848960332763,3267179470881,
    3664498181156,199311491154,3916294946107,3042324929558,1579840467382,4433322634211,
    1809121974436,3272354838802,4319392486289,329089339021,4741531295708,2843157133709,
    3056238920021,4828967886936,192832050210,4970711210311,2594181632944,3478469515248,
    4322143034833,1140488489625,4598309238908,1116825530921,3614676747779,2590701209474,
    1930887560946,2973113965993,197098749237,2335654879676,1062713977899,999731195603,
    1558196081120,623867822815,1236847106077,2166092973986,221891059678,3373149714451,
    1272587772506,4125509081492,3018503619533,4420168893973,4827842286562,4336241171278,
    6579374412015,4001905160021,8221224776140,3572814958458,9755095195429,3221946483645,
    11206266970580,3134613459486,12584364736519,3499571631871,13843829284916,4488034869320,
    14855665543549,6219348486591,15400180385130,8721660181882,15182344139531,11898516829379,
    13860062161984,15500345865116,11075283895593,19080706638459,6504678087366,21921268950198,
    11188520480,22966724324357,8199736236327,20904610346826,16985679039782,14564621710835,
    24243999754009,3681794707194,27030216922498,10242961593696,22506484707575,23458973897155,
    9478799284890,30343334983702,9761200807360,25167420758763,27984648025905,5903309926286,
    33980595529946,20745310070766,18842196904683,38075800005617,13598244433141,28300817544696,
    41507226246698,10111752351696,35163065866785,48552074449323,14449981016525,37760613510960,
    60768257042060,31372948447986],
   [29398737492669,73043211944173,61437126191899,4158931691504,83138798559664,122483381741662,
    91056375489092,416931121699,104012450463079,158901944392453,120522268819341,20224903491152,
    235137921987596,472220665077026,676155440928890,806303997179024,846081281024224,
    802491990556020,698631434995742,563646324583652,424097239640826,298865269457616,
    197820768995560,123207871341414,72276829119074,39946032895320,20792136517246,10182100400280,
    4682844190290,2017256138572,810728462902,302052017434,103148481378,31463725356,8045489486,
    1199345820]]
private def rkmC_w64_m32_s6a_11 : List ℤ := pzigCat
  [
   [458657305,1414898452,3148901749,5693896080,8786696559,13133090938,18610825955,25386329596,
    33895850675,44296598400,56740023581,71785084202,89497895429,109670709462,132711198561,
    158078831900,185281614249,213573363678,241757662239,268296296036,291566692669,309316175514,
    319359077949,319881520782,308597184075,284466140704,247000114311,196306238846,134153893729,
    63464040580,12406175336,88610778287,160531115964,223964010397,275543534900,313506101393,
    338912497580,354533151591,365319607128,378236440577,400086460044,437203554687,493818343618,
    570806359773,665202417522,771176132945,879432615206,979504867317,1062071303880,1119379476445,
    1147106743442,1144803401621,1114733710894,1059840449019,983283711830,885752845571,
    765459765770,619892452729,447543198258,251219908499,41188432804,163630213394,338271500781,
    454762770640,489033392375,427702559088,272487220015,40529251218,238354767870,527840621819,
    794123326096,1009627755965,1154610266574,1214408472107,1173604572458,1012616591409,
    711868105296,263572942787,311712633561,949327359604,1535383724701,1923294676584,
    1970701006701,1590042575602,795773974081,270467088131,1357783842416,2167657202607,
    2444504799838,2068156070531,1111256532196,164607294818,1382946819729,2171888880378,
    2290191069391,1713639946652,646088088455,551581313311,1489050325084,1881799059701,
    1643005909328,903121917551,49518878797,879334131224,1323602949589,1276841607108,812869719089,
    142250512520,476207104584,834298579215,846355270190,569231326313,161120649328,198477225978,
    392216414933,408420950490,322028257783,226451096800,159917963367,80098233224,87080557604,
    356089217911,617213685774,668402566171,349637260926,297772798976,972937408247,1241428887348,
    809941936133,218870814751,1308859492146,1759206185029,1158069315504,271306341194,
    1705588002407,2190193129924,1283292443285,560721090839,2188037480618,2466563591181],
   [1087286262772,1127524917836,2694737847609,2468137316556,493414071743,1923624715967,
    3066989954476,2039414706191,514105933931,2778283960816,3051899935289,1043597554762,
    1814767394530,3364860684349,2355952137174,518967080486,3057422412123,3222035132926,
    795508324015,2337003761403,3621563622066,1924226646977,1432022015363,3650593684156,
    2782299056187,527165162141,3451695024468,3373124063285,256019777932,3165163471992,
    3747111942273,852222808436,2902058092642,3964296472771,1233970012126,2733887913380,
    4071345187675,1395168667654,2692849183738,4091298120763,1344134162362,2775069444306,
    4027571443811,1101901862384,2953209930922,3877527935997,699210260372,3196489416120,
    3643137363323,158287945538,3492852454178,3318151763541,539621562557,3842214142098,
    2837419011531,1466680162331,4186175721714,2022209775827,2673329571497,4285056651850,
    620844071901,3990257412375,3669494238080,1440705282854,4829365793819,1880805867422,
    3663999095054,4311026109957,938338741359,4868152089072,1992441961335,3571949554335,
    3925119736010,1218764259912,4293541560325,1126454726716,3253552811934,2613209690411,
    1454046755989,2870849250250,315287040953,2021916962451,1425710107022,518998591630,
    1566777644461,1078123927972,754471447644,2288816300721,761120894194,2816973178582,
    2624654900001,2571118985021,4491257956032,1624412049420,6101172350289,147890981665,
    7310727779500,1655310960981,8090057714667,3598925659056,8501514394536,5538870186209,
    8671170406041,7375754869844,8761282862820,9040883048151,8945724541635,10474124728930,
    9387132713634,11601907155455,10215029981119,12322190273740,11506327421086,12499784225901,
    13270459822803,11969400248760,15439052764250,10540361131799,17851962807535,8000817111168,
    20225585933338,4138677572747,22093834361657,1184740060537,22749201048340,7868322676980,
    21256904792529,15325817912227,16647454797816,22262005372998,8341308131019,26657214948551,
    3269458809759,26129364749288,16294490344490,18726849998719,27117772619601,4135494488780,
    30802040132650,14806564704214],
   [22729314782077,30986102181715,2077826571850,34279587650574,24013517050244,17365606364531,
    39940568936921,15527180250799,29341433857084,43940661137700,9921792640732,38710165524347,
    51156732345311,11619858331711,44662342417492,64466491504506,25592267511646,42553442337435,
    82840950549413,56755520139103,24502219302280,106694141535276,130002724419740,69787583660428,
    45918657909457,150976491254553,176358269307031,84591196015427,114156831987730,
    369421611283602,613863855012080,789477212623346,865156732789362,840795517523970,
    739946887139692,596996302442808,444993874916394,307954986976620,198471688319682,
    119320589428506,66954979539730,35052323592930,17096498955462,7749682233566,3252462575082,
    1256901044152,443392386342,140817067502,39104549192,8639584558,1018758386]]
private theorem rkmWC_w64_m32_s6a_0 : bWinChk 664 25 100000000 1024 rkmPhb_w64_m32_s6a
    844 rkmXsWin_w64_m32_s6a_in 848 rkmC_w64_m32_s6a_1 3203477616 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6a_1 : bWinChk 664 21 100000000 1024 rkmPhb_w64_m32_s6a
    848 rkmC_w64_m32_s6a_1 827 rkmC_w64_m32_s6a_2 2400146233 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6a_2 : bWinChk 664 18 100000000 1024 rkmPhb_w64_m32_s6a
    827 rkmC_w64_m32_s6a_2 808 rkmC_w64_m32_s6a_3 2428092486 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6a_3 : bWinChk 664 16 100000000 1024 rkmPhb_w64_m32_s6a
    808 rkmC_w64_m32_s6a_3 790 rkmC_w64_m32_s6a_4 1633195577 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6a_4 : bWinChk 664 14 100000000 1024 rkmPhb_w64_m32_s6a
    790 rkmC_w64_m32_s6a_4 774 rkmC_w64_m32_s6a_5 1599913096 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6a_5 : bWinChk 664 13 100000000 1024 rkmPhb_w64_m32_s6a
    774 rkmC_w64_m32_s6a_5 759 rkmC_w64_m32_s6a_6 1417610728 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6a_6 : bWinChk 664 12 100000000 1024 rkmPhb_w64_m32_s6a
    759 rkmC_w64_m32_s6a_6 744 rkmC_w64_m32_s6a_7 1201524823 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6a_7 : bWinChk 664 11 100000000 1024 rkmPhb_w64_m32_s6a
    744 rkmC_w64_m32_s6a_7 731 rkmC_w64_m32_s6a_8 1197515390 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6a_8 : bWinChk 664 11 100000000 1024 rkmPhb_w64_m32_s6a
    731 rkmC_w64_m32_s6a_8 717 rkmC_w64_m32_s6a_9 1149346981 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6a_9 : bWinChk 664 10 100000000 1024 rkmPhb_w64_m32_s6a
    717 rkmC_w64_m32_s6a_9 705 rkmC_w64_m32_s6a_10 1059221572 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6a_10 : bWinChk 664 10 100000000 1024 rkmPhb_w64_m32_s6a
    705 rkmC_w64_m32_s6a_10 692 rkmC_w64_m32_s6a_11 1004353874 = true := by decide +kernel
private theorem rkmWC_w64_m32_s6a_11 : bWinChk 664 10 100000000 1024 rkmPhb_w64_m32_s6a
    692 rkmC_w64_m32_s6a_11 679 rkmXsWin_w64_m32_s6a_out 1025414720 = true := by decide +kernel
/-- Certified `w64_m32_s6a` partial walk (`171` substeps). -/
theorem rkmWinIterSnd_w64_m32_s6a :
    RkmWinIterSound 171 1024 rkmHbWin_w64_m32_s6a 844 rkmXsWin_w64_m32_s6a_in
      679 rkmXsWin_w64_m32_s6a_out 19319813096 :=
  rkmChS 171 19319813096 (rkmChS 161 18294398376 (rkmChS 151 17290044502 (rkmChS 141
    16230822930 (rkmChS 130 15081475949 (rkmChS 119 13883960559 (rkmChS 107 12682435736 (rkmChS
    94 11264825008 (rkmChS 80 9664911912 (rkmChS 64 8031716335 (rkmChS 46 5603623849
    (bWinChk_sound rkmHhb_w64_m32_s6a rkmWC_w64_m32_s6a_0) rkmHhb_w64_m32_s6a
    rkmWC_w64_m32_s6a_1 rfl rfl) rkmHhb_w64_m32_s6a rkmWC_w64_m32_s6a_2 rfl rfl)
    rkmHhb_w64_m32_s6a rkmWC_w64_m32_s6a_3 rfl rfl) rkmHhb_w64_m32_s6a rkmWC_w64_m32_s6a_4 rfl
    rfl) rkmHhb_w64_m32_s6a rkmWC_w64_m32_s6a_5 rfl rfl) rkmHhb_w64_m32_s6a rkmWC_w64_m32_s6a_6
    rfl rfl) rkmHhb_w64_m32_s6a rkmWC_w64_m32_s6a_7 rfl rfl) rkmHhb_w64_m32_s6a
    rkmWC_w64_m32_s6a_8 rfl rfl) rkmHhb_w64_m32_s6a rkmWC_w64_m32_s6a_9 rfl rfl)
    rkmHhb_w64_m32_s6a rkmWC_w64_m32_s6a_10 rfl rfl) rkmHhb_w64_m32_s6a rkmWC_w64_m32_s6a_11
    rfl rfl
/-- Cumulative `w64_m32` part `1` lane witness. -/
theorem rkmHiLane_w64_m32_wint1 :
    @rkmWinIterSnd_w64_m32_s6a = @rkmWinIterSnd_w64_m32_s6a :=
  (And.intro (Eq.refl rkmHiLane_w64_m32_wint0) rfl).right
/-- Module lane witness for `FindAllJohnsonRampKickMuxHiW64T08`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T08 :
    @rkmHiLane_w64_m32_wint1 = @rkmHiLane_w64_m32_wint1 :=
  (And.intro (Eq.refl laneWitness_FindAllJohnsonRampKickMuxHiW64T07) rfl).right

end
end QuantumComputation.Specs.DickeSol
