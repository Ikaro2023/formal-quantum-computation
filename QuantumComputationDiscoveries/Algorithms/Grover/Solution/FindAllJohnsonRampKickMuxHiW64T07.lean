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

/-
# Caustic `r = 1024` Halo-16 Walk `w64_m32` Part `0` (`FindAllJohnsonRampKickMuxHiW64T07`)

Certifies part `0` of the `w64_m32` `r = 1024` halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Generator list for `w64_m32_s0`. -/
def rkmHbWin_w64_m32_s0 : List ℤ := altBuildHbFrom 64 1024 362194750000 0 64
/-- Entry `rkmXsWin_w64_m32_s0_in`. -/
def rkmXsWin_w64_m32_s0_in : List ℤ := [rkmP 1000000000000000]
/-- Exit `rkmXsWin_w64_m32_s0_out`. -/
def rkmXsWin_w64_m32_s0_out : List ℤ := [rkmP 81209410344368, rkmP 185840573349654,
  rkmP 298202131968439, rkmP 387374582265804, rkmP 432037280260790, rkmP 427205550635861,
  rkmP 382192439582429, rkmP 313697611198732, rkmP 238636648062879, rkmP 169555669177906,
  rkmP 113204817013744, rkmP 71368286099918, rkmP 42654151908000, rkmP 24247574165225,
  rkmP 13147204983628, rkmP 6815303630181, rkmP 3384507792764, rkmP 1613056739959,
  rkmP 738877747745, rkmP 325715718979, rkmP 138318753221, rkmP 56663032513, rkmP 22375873200,
  rkmP 8474576466, rkmP 3112896322, rkmP 978344558, rkmP 244793141]
/-- Generator list for `w64_m32_s1`. -/
def rkmHbWin_w64_m32_s1 : List ℤ := altBuildHbFrom 128 1024 186509809523 0 128
/-- Entry `rkmXsWin_w64_m32_s1_in`. -/
def rkmXsWin_w64_m32_s1_in : List ℤ := [rkmP 81209410344368, rkmP 185840573349654,
  rkmP 298202131968439, rkmP 387374582265804, rkmP 432037280260790, rkmP 427205550635861,
  rkmP 382192439582429, rkmP 313697611198732, rkmP 238636648062879, rkmP 169555669177906,
  rkmP 113204817013744, rkmP 71368286099918, rkmP 42654151908000, rkmP 24247574165225,
  rkmP 13147204983628, rkmP 6815303630181, rkmP 3384507792764, rkmP 1613056739959,
  rkmP 738877747745, rkmP 325715718979, rkmP 138318753221, rkmP 56663032513, rkmP 22375873200,
  rkmP 8474576466, rkmP 3112896322, rkmP 978344558, rkmP 244793141]
/-- Exit `rkmXsWin_w64_m32_s1_out`. -/
def rkmXsWin_w64_m32_s1_out : List ℤ := [rkmP 1367777821, rkmP 7488328020, rkmP 29306582546,
  rkmP 93706472659, rkmP 257753080502, rkmP 630625812641, rkmP 1400785919046, rkmP 2864212800970,
  rkmP 5447497556101, rkmP 9712425182371, rkmP 16333528241954, rkmP 26038524822985,
  rkmP 39511061512566, rkmP 57263869516082, rkmP 79501003659425, rkmP 105994723110236,
  rkmP 136007471649421, rkmP 168282009730709, rkmP 201113098222348, rkmP 232499036386470,
  rkmP 260351765699541, rkmP 282735180038362, rkmP 298091885222306, rkmP 305420042002962,
  rkmP 304375531365976, rkmP 295284461294340, rkmP 279070366894147, rkmP 257114470927876,
  rkmP 231074470994906, rkmP 202694555184694, rkmP 173631989719288, rkmP 145321489928284,
  rkmP 118889187580716, rkmP 95115571581861, rkmP 74444045548292, rkmP 57021292736333,
  rkmP 42758401699739, rkmP 31399424869671, rkmP 22587404907892, rkmP 15921204825933,
  rkmP 10999175415791, rkmP 7449525633280, rkmP 4947339979698, rkmP 3222392086341,
  rkmP 2058954340271, rkmP 1290710993738, rkmP 794026823049, rkmP 479362862153, rkmP 284084568748,
  rkmP 165320669922, rkmP 94402278922, rkmP 52957196328, rkmP 29062924421, rkmP 15639935494,
  rkmP 8203335742, rkmP 4146825133, rkmP 1927488630, rkmP 802087285, rkmP 267322251]
/-- Generator list for `w64_m32_s2`. -/
def rkmHbWin_w64_m32_s2 : List ℤ := altBuildHbFrom 256 1024 97199393939 0 256
/-- Entry `rkmXsWin_w64_m32_s2_in`. -/
def rkmXsWin_w64_m32_s2_in : List ℤ := [rkmP 1367777821, rkmP 7488328020, rkmP 29306582546,
  rkmP 93706472659, rkmP 257753080502, rkmP 630625812641, rkmP 1400785919046, rkmP 2864212800970,
  rkmP 5447497556101, rkmP 9712425182371, rkmP 16333528241954, rkmP 26038524822985,
  rkmP 39511061512566, rkmP 57263869516082, rkmP 79501003659425, rkmP 105994723110236,
  rkmP 136007471649421, rkmP 168282009730709, rkmP 201113098222348, rkmP 232499036386470,
  rkmP 260351765699541, rkmP 282735180038362, rkmP 298091885222306, rkmP 305420042002962,
  rkmP 304375531365976, rkmP 295284461294340, rkmP 279070366894147, rkmP 257114470927876,
  rkmP 231074470994906, rkmP 202694555184694, rkmP 173631989719288, rkmP 145321489928284,
  rkmP 118889187580716, rkmP 95115571581861, rkmP 74444045548292, rkmP 57021292736333,
  rkmP 42758401699739, rkmP 31399424869671, rkmP 22587404907892, rkmP 15921204825933,
  rkmP 10999175415791, rkmP 7449525633280, rkmP 4947339979698, rkmP 3222392086341,
  rkmP 2058954340271, rkmP 1290710993738, rkmP 794026823049, rkmP 479362862153, rkmP 284084568748,
  rkmP 165320669922, rkmP 94402278922, rkmP 52957196328, rkmP 29062924421, rkmP 15639935494,
  rkmP 8203335742, rkmP 4146825133, rkmP 1927488630, rkmP 802087285, rkmP 267322251]
/-- Exit `rkmXsWin_w64_m32_s2_out`. -/
def rkmXsWin_w64_m32_s2_out : List ℤ := [rkmP 234884283, rkmP 483439818, rkmP 837351352,
  rkmP 1529733299, rkmP 2518198138, rkmP 4218087123, rkmP 6964979061, rkmP 11301173066,
  rkmP 18246622958, rkmP 28861901823, rkmP 45284831394, rkmP 70065391875, rkmP 107114560437,
  rkmP 161793510088, rkmP 241379489902, rkmP 355966982971, rkmP 518692054381, rkmP 746940387746,
  rkmP 1062998313804, rkmP 1495208389398, rkmP 2078889929541, rkmP 2857242408625,
  rkmP 3882201847390, rkmP 5214812053712, rkmP 6925769215625, rkmP 9094593996070,
  rkmP 11809011985664, rkmP 15162953704023, rkmP 19253575130214, rkmP 24178184294168,
  rkmP 30028835753588, rkmP 36887346997789, rkmP 44818889356492, rkmP 53865073382762,
  rkmP 64037708694721, rkmP 75311860480159, rkmP 87620961350998, rkmP 100852320136906,
  rkmP 114845191019343, rkmP 129391240268988, rkmP 144236773862394, rkmP 159089342874117,
  rkmP 173625433561200, rkmP 187502070860911, rkmP 200369574788713, rkmP 211886106291615,
  rkmP 221732786876006, rkmP 229628040877992, rkmP 235341285171567, rkmP 238703902763259,
  rkmP 239617649727784, rkmP 238059171665828, rkmP 234081246869870, rkmP 227809657893138,
  rkmP 219436568937788, rkmP 209211138690800, rkmP 197426750228782, rkmP 184407803911321,
  rkmP 170494638792800, rkmP 156029064932562, rkmP 141341305889757, rkmP 126737710711100,
  rkmP 112491708611157, rkmP 98836317230554, rkmP 85960221405847, rkmP 74006005335669,
  rkmP 63070551511139, rkmP 53208378214218, rkmP 44435278885662, rkmP 36734320808293,
  rkmP 30061678969768, rkmP 24352936980479, rkmP 19529458762042, rkmP 15503352238240,
  rkmP 12183142690853, rkmP 9477372651009, rkmP 7298109819099, rkmP 5563305894357,
  rkmP 4197975287998, rkmP 3135766213793, rkmP 2318594537971, rkmP 1697038728589,
  rkmP 1229569876672, rkmP 881771875381, rkmP 625992503363, rkmP 439821356964, rkmP 305910642243,
  rkmP 210613934254, rkmP 143479324939, rkmP 96778581491, rkmP 64489722721, rkmP 42519169837,
  rkmP 27641196922, rkmP 17678820825, rkmP 11118012119, rkmP 6720844275, rkmP 3925878175,
  rkmP 2069147222, rkmP 943678454, rkmP 326433419]
/-- Generator list for `w64_m32_s3`. -/
def rkmHbWin_w64_m32_s3 : List ℤ := altBuildHbFrom 512 1024 51677427350 0 512
/-- Entry `rkmXsWin_w64_m32_s3_in`. -/
def rkmXsWin_w64_m32_s3_in : List ℤ := [rkmP 234884283, rkmP 483439818, rkmP 837351352,
  rkmP 1529733299, rkmP 2518198138, rkmP 4218087123, rkmP 6964979061, rkmP 11301173066,
  rkmP 18246622958, rkmP 28861901823, rkmP 45284831394, rkmP 70065391875, rkmP 107114560437,
  rkmP 161793510088, rkmP 241379489902, rkmP 355966982971, rkmP 518692054381, rkmP 746940387746,
  rkmP 1062998313804, rkmP 1495208389398, rkmP 2078889929541, rkmP 2857242408625,
  rkmP 3882201847390, rkmP 5214812053712, rkmP 6925769215625, rkmP 9094593996070,
  rkmP 11809011985664, rkmP 15162953704023, rkmP 19253575130214, rkmP 24178184294168,
  rkmP 30028835753588, rkmP 36887346997789, rkmP 44818889356492, rkmP 53865073382762,
  rkmP 64037708694721, rkmP 75311860480159, rkmP 87620961350998, rkmP 100852320136906,
  rkmP 114845191019343, rkmP 129391240268988, rkmP 144236773862394, rkmP 159089342874117,
  rkmP 173625433561200, rkmP 187502070860911, rkmP 200369574788713, rkmP 211886106291615,
  rkmP 221732786876006, rkmP 229628040877992, rkmP 235341285171567, rkmP 238703902763259,
  rkmP 239617649727784, rkmP 238059171665828, rkmP 234081246869870, rkmP 227809657893138,
  rkmP 219436568937788, rkmP 209211138690800, rkmP 197426750228782, rkmP 184407803911321,
  rkmP 170494638792800, rkmP 156029064932562, rkmP 141341305889757, rkmP 126737710711100,
  rkmP 112491708611157, rkmP 98836317230554, rkmP 85960221405847, rkmP 74006005335669,
  rkmP 63070551511139, rkmP 53208378214218, rkmP 44435278885662, rkmP 36734320808293,
  rkmP 30061678969768, rkmP 24352936980479, rkmP 19529458762042, rkmP 15503352238240,
  rkmP 12183142690853, rkmP 9477372651009, rkmP 7298109819099, rkmP 5563305894357,
  rkmP 4197975287998, rkmP 3135766213793, rkmP 2318594537971, rkmP 1697038728589,
  rkmP 1229569876672, rkmP 881771875381, rkmP 625992503363, rkmP 439821356964, rkmP 305910642243,
  rkmP 210613934254, rkmP 143479324939, rkmP 96778581491, rkmP 64489722721, rkmP 42519169837,
  rkmP 27641196922, rkmP 17678820825, rkmP 11118012119, rkmP 6720844275, rkmP 3925878175,
  rkmP 2069147222, rkmP 943678454, rkmP 326433419]
/-- Exit `rkmXsWin_w64_m32_s3_out`. -/
def rkmXsWin_w64_m32_s3_out : List ℤ := [rkmP 117809487, rkmP 374752579, rkmP 637090105,
  rkmP 1088532796, rkmP 1816756524, rkmP 2906395303, rkmP 4713731232, rkmP 7433953135,
  rkmP 11723317032, rkmP 18186400004, rkmP 27870271226, rkmP 42337309549, rkmP 63539350611,
  rkmP 94447936000, rkmP 138742242025, rkmP 201690824637, rkmP 290158554334, rkmP 413025879188,
  rkmP 581918968596, rkmP 811332196568, rkmP 1119793547519, rkmP 1529931934680, rkmP 2069352499506,
  rkmP 2771177618781, rkmP 3674277085642, rkmP 4824016258079, rkmP 6271769721066,
  rkmP 8075158770094, rkmP 10297181240670, rkmP 13005164831259, rkmP 16269460383633,
  rkmP 20160924854365, rkmP 24748832795435, rkmP 30097329213903, rkmP 36262097767260,
  rkmP 43286489061146, rkmP 51197217607419, rkmP 60000795227003, rkmP 69679252680924,
  rkmP 80187332159710, rkmP 91449744752529, rkmP 103359890299795, rkmP 115779752992678,
  rkmP 128541002599477, rkmP 141447779444384, rkmP 154281053473613, rkmP 166804095295819,
  rkmP 178769943073449, rkmP 189928890175082, rkmP 200037399084869, rkmP 208866885727559,
  rkmP 216212002078209, rkmP 221899268829311, rkmP 225793191165982, rkmP 227802128087821,
  rkmP 227881726789348, rkmP 226036155437403, rkmP 222318329639545, rkmP 216826807019102,
  rkmP 209701939703206, rkmP 201119784010213, rkmP 191284924063030, rkmP 180422523651385,
  rkmP 168769885307681, rkmP 156568076963975, rkmP 144054014132939, rkmP 131452951972352,
  rkmP 118972858224181, rkmP 106798824239550, rkmP 95089920459810, rkmP 83977138037122,
  rkmP 73561973939879, rkmP 63917577240088, rkmP 55089526157385, rkmP 47098474493351,
  rkmP 39943131639921, rkmP 33603156016607, rkmP 28043270092333, rkmP 23216352950791,
  rkmP 19067057363201, rkmP 15534693634630, rkmP 12556129632112, rkmP 10068206592902,
  rkmP 8009340970795, rkmP 6321047453870, rkmP 4949310304622, rkmP 3844663174701,
  rkmP 2963124980236, rkmP 2265805658379, rkmP 1718925040415, rkmP 1293909018468,
  rkmP 966305854381, rkmP 715981354991, rkmP 526353113221, rkmP 383914499737, rkmP 277827032182,
  rkmP 199398954381, rkmP 141876624051, rkmP 100132659247, rkmP 69909951590, rkmP 48331653157,
  rkmP 33034038207, rkmP 22196845024, rkmP 14681844132, rkmP 9442370801, rkmP 5895786298,
  rkmP 3477042320, rkmP 1861811506, rkmP 896901285, rkmP 316292498]
/-- Generator list for `w64_m32_s4`. -/
def rkmHbWin_w64_m32_s4 : List ℤ := altBuildHbFrom 1024 1024 29638027559 0 1024
/-- Entry `rkmXsWin_w64_m32_s4_in`. -/
def rkmXsWin_w64_m32_s4_in : List ℤ := [rkmP 117809487, rkmP 374752579, rkmP 637090105,
  rkmP 1088532796, rkmP 1816756524, rkmP 2906395303, rkmP 4713731232, rkmP 7433953135,
  rkmP 11723317032, rkmP 18186400004, rkmP 27870271226, rkmP 42337309549, rkmP 63539350611,
  rkmP 94447936000, rkmP 138742242025, rkmP 201690824637, rkmP 290158554334, rkmP 413025879188,
  rkmP 581918968596, rkmP 811332196568, rkmP 1119793547519, rkmP 1529931934680, rkmP 2069352499506,
  rkmP 2771177618781, rkmP 3674277085642, rkmP 4824016258079, rkmP 6271769721066,
  rkmP 8075158770094, rkmP 10297181240670, rkmP 13005164831259, rkmP 16269460383633,
  rkmP 20160924854365, rkmP 24748832795435, rkmP 30097329213903, rkmP 36262097767260,
  rkmP 43286489061146, rkmP 51197217607419, rkmP 60000795227003, rkmP 69679252680924,
  rkmP 80187332159710, rkmP 91449744752529, rkmP 103359890299795, rkmP 115779752992678,
  rkmP 128541002599477, rkmP 141447779444384, rkmP 154281053473613, rkmP 166804095295819,
  rkmP 178769943073449, rkmP 189928890175082, rkmP 200037399084869, rkmP 208866885727559,
  rkmP 216212002078209, rkmP 221899268829311, rkmP 225793191165982, rkmP 227802128087821,
  rkmP 227881726789348, rkmP 226036155437403, rkmP 222318329639545, rkmP 216826807019102,
  rkmP 209701939703206, rkmP 201119784010213, rkmP 191284924063030, rkmP 180422523651385,
  rkmP 168769885307681, rkmP 156568076963975, rkmP 144054014132939, rkmP 131452951972352,
  rkmP 118972858224181, rkmP 106798824239550, rkmP 95089920459810, rkmP 83977138037122,
  rkmP 73561973939879, rkmP 63917577240088, rkmP 55089526157385, rkmP 47098474493351,
  rkmP 39943131639921, rkmP 33603156016607, rkmP 28043270092333, rkmP 23216352950791,
  rkmP 19067057363201, rkmP 15534693634630, rkmP 12556129632112, rkmP 10068206592902,
  rkmP 8009340970795, rkmP 6321047453870, rkmP 4949310304622, rkmP 3844663174701,
  rkmP 2963124980236, rkmP 2265805658379, rkmP 1718925040415, rkmP 1293909018468,
  rkmP 966305854381, rkmP 715981354991, rkmP 526353113221, rkmP 383914499737, rkmP 277827032182,
  rkmP 199398954381, rkmP 141876624051, rkmP 100132659247, rkmP 69909951590, rkmP 48331653157,
  rkmP 33034038207, rkmP 22196845024, rkmP 14681844132, rkmP 9442370801, rkmP 5895786298,
  rkmP 3477042320, rkmP 1861811506, rkmP 896901285, rkmP 316292498]
/-- Exit `rkmXsWin_w64_m32_s4_out`. -/
def rkmXsWin_w64_m32_s4_out : List ℤ := [rkmP 114159959, rkmP 319756100, rkmP 324515303,
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
private def rkmPhb_w64_m32_s0 : List ℕ := uNatCatN
  [
   [185443712000000,260072981217880,315830499094905,361559627942844,400712471978769,
    435071734916125,465703017995189,493304462762018,518363327210848,541235796542733,
    562191592616117,581440698167050,599150258224391,615455745431980,630468604999895,
    644281648261906,656972955467587,668608761621930,679245630411672,688932118284465,
    697710065908618,705615612265699,712679998774679,718930211948442,724389500000000,
    729077789586553,733012022253124,736206425297100,738672728177142,740420332865247,
    741456444433847,741786166499584,741412564780344,740336700863481,738557637253048,
    736072413797172,732875994634484,728961183781795,724318506350140,718936051046681,
    712799268000000,705890713908607,698189733882335,689672065877015,680309348958575,
    670068510249276,658910996519020,646791803781818,633658240051780,619448329574889,
    604088726399545,587491942647830,569552597565224,550142230659882,529101945567598,
    506231660782038,481273829665073,453887685965745,423606232097201,389759249745426,
    351322186296018,306578547484269,252199926217782,179648596000000]]
private def rkmPhb_w64_m32_s1 : List ℕ := uNatCatN
  [
   [135047527497241,190145630283000,231847822848568,266519842181853,296638560420917,
    323479637036552,347803940869816,370109156212374,390742279670500,409956876971205,
    427945040788775,444856510420027,460810749245211,475904914944225,490219312215783,
    503821237628470,516767761357451,529107784869829,540883592690422,552132042663466,
    562885492754765,573172532452178,583018566950621,592446288848304,601476062784197,
    610126241910414,618413430423356,626352702991670,633957789431209,641241231126323,
    648214514304085,654888184208997,661271943412427,667374736860763,673204825773661,
    678769852115712,684076895056769,689132520590005,693942825278623,698513474941719,
    702849738959179,706956520768417,710838385037677,714499581927633,717944068792392,
    721175529620234,724197392471921,727012845138452,729624849209767,732036152720034,
    734249301513081,736266649452552,738090367585084,739722452350649,741164732921922,
    742418877743825,743486400334937,744368664404171,745066888328664,745582149032247,
    745915385297841,746067400541681,746038865072287,745830317852404,745442167777792,
    744874694482550,744128048676629,743202252017255,742097196512010,740812643447383,
    739348221832501,737703426343506,735877614749569,733870004796764,731679670520799,
    729305537954018,726746380185788,724000811728466,721067282133377,717944068792392,
    714629268850760,711120790145405,707416341069778,703513419251239,699409298909368,
    695101016743137,690585356170933,685858829719268,680917659322777,675757754258675,
    670374686391914,664763662351075,658919492187487,652836553988423,646508753816081,
    639929480222986,633091552445784,625987161195735,618607800735915,610944190649457,
    602986185343161,594722668873714,586141432098828,577229028400592,567970603244893,
    558349691547252,548347975095870,537944989970789,527117770751018,515840413959695,
    504083537118849,491813601137424,478992051233066,465574213094072,451507853073112,
    436731268026296,421170701753432,404736772334037,387319402980745,368780408936342,
    348942258849334,327570274558052,304342864490955,278798167229015,250229167538379,
    217449002615448,178150358592354,126395869130130]]
private def rkmPhb_w64_m32_s2 : List ℕ := uNatCatN
  [
   [99532179393536,140415954849464,171552276783817,197604431530352,220383416331142,
    240820320810141,259469590260030,276693333860690,292743662373992,307804560698220,
    322015240210358,335484098920949,348297532915691,360525746781188,372226725726489,
    383449034343913,394233840024056,404616408630320,414627231646651,424292890154488,
    433636727130301,442679377665359,451439192209441,459932578123339,468174278047103,
    476177598827665,483954601347665,491516259132034,498872591798073,506032778068223,
    513005252051898,519797785732897,526417560007976,532871226164397,539164959326684,
    545304505121199,551295220583738,557142110156885,562849857480297,568422853560955,
    573865221815856,579180840402263,584373362186916,589446232652990,594402705999804,
    599245859653810,603978607378744,608603711147099,613123791913289,617541339410428,
    621858721076934,626078190205748,630201893397468,634231877388797,638170095319212,
    642018412491360,645778611674336,649452397993405,653041403444923,656547191070950,
    659971258824381,663315043152117,666579922320992,669767219508588,672878205678889,
    675914102260725,678876083645196,681765279516731,684582777031028,687329622851901,
    690006825057930,692615354928847,695156148620675,697630108737869,700038105809954,
    702380979679542,704659540808013,706874571504604,709026827084209,711117036958715,
    713145905666346,715114113843117,717022319140161,718871157090427,720661241927956,
    722393167362698,724067507313622,725684816602655,727245631611799,728750470905605,
    730199835821026,731594211026515,732934065052133,734219850792248,735452005982362,
    736630953651450,737757102551116,738830847562776,739852570084010,740822638395119,
    741741408006883,742609221990430,743426411290069,744193295019892,744910180744877,
    745577364747191,746195132278345,746763757797801,747283505198586,747754628020452,
    748177369651065,748551963515668,748878633255658,749157592896462,749389047005073,
    749573190837589,749710210477069,749800282961995,749843576405588,749840250106255,
    749790454649353,749694332000498,749552015590587,749363630392704,749129292991049,
    748849111642025,748523186327592,748151608800973,747734462624801,747271823201766,
    746763757797801,746210325557838,745611577514156,744967556587311,744278297579627,
    743543827161221,742764163848517,741939317975165,741069291655299,740154078739029],
   [739193664760046,738188026875211,737137133795974,736040945711446,734899414202936,
    733712482149739,732480083625944,731202143788000,729878578752764,728509295465725,
    727094191559068,725633155199231,724126064923552,722572789465600,720973187568729,
    719327107787372,717634388275554,715894856562047,714108329311579,712274612071427,
    710393499002707,708464772595595,706488203367679,704463549544568,702390556721815,
    700268957507165,698098471142027,695878803101019,693609644668322,691290672489508,
    688921548097372,686501917410212,684031410200866,681509639534668,678936201174376,
    676310672949924,673632614090694,670901564517832,668117044093884,665278551826841,
    662385565025398,659437538401987,656433903119819,653374065779850,650257407343215,
    647083281984272,643851015868948,640559905852581,637209218090923,633798186557316,
    630326011458427,626791857540140,623194852274363,619534083916582,615808599422931,
    612017402214364,608159449774194,604233651063774,600238863739409,596173891151681,
    592037479106240,587828312362643,583545010845087,579186125535691,574750134017384,
    570235435629349,565640346193192,560963092262598,556201804842911,551354512519823,
    546419133927914,541393469479935,536275192266315,531061838020885,525750794033063,
    520339286868128,514824368735163,509202902316072,503471543837803,497626724132476,
    491664627385010,485581167213284,479371959659591,473032292591063,466557090907200,
    459940876829516,453177724395226,446261207085173,439184337274539,431939495887850,
    424518350246687,416911757590940,409109651092924,401100904313271,392873168889846,
    384412678693851,375704011566757,366729796824854,357470352618854,347903231401252,
    338002643301037,327738714716380,317076520576872,305974799543022,294384214984514,
    282244948363005,269483281919093,256006597277749,241695787032595,226393226130864,
    209882640303977,191852990082828,171827416006679,149004102996304,121821516997846,
    86253495689361]]
private def rkmPhb_w64_m32_s3 : List ℕ := uNatCatN
  [
   [460436539697286,465026973019580,469540547518115,473979526525504,478346053745924,
    482642162024662,486869781304325,491030745858239,495126800879863,499159608497085,
    503130753271715,507041747237130,510894034520737,514688995592389,518427951175200,
    522112165851047,525742851389466,529321169825501,532848236309325,536325121748037,
    539752855257902,543132426443448,546464787518164,549750855280087,552991512954267,
    556187611912935,559339973283188,562449389451064,565516625470094,568542420381643,
    571527488453735,574472520344436,577378184195366,580245126660394,583073973874192,
    585865332364879,588619789914674,591337916372148,594020264419357,596667370296899,
    599279754489699,601857922376076,604402364842507,606913558866245,609391968067872,
    611838043235624,614252222823279,616634933423183,618986590215957,621307597398250,
    623598348589856,625859227221396,628090606903687,630292851779862,632466316861195,
    634611348347569,636728283933430,638817453100019,640879177394637,642913770697645,
    644921539477836,646902783036814,648857793742945,650786857255412,652690252738905,
    654568253069391,656421125031446,658249129507542,660052521659703,661831551103898,
    663586462077528,665317493600331,667024879629023,668708849205981,670369626602224,
    672007431454983,673622478900086,675214979699415,676785140363641,678333163270461,
    679859246778526,681363585337267,682846369592777,684307786489942,685748019370961,
    687167248070429,688565649007117,689943395272589,691300656716795,692637600030750,
    693954388826443,695251183714060,696528142376653,697785419642348,699023167554186,
    700241535437698,701440669966303,702620715224607,703781812769687,704924101690442,
    706047718665081,707152798016813,708239471767820,709307869691560,710358119363479,
    711390346210178,712404673557093,713401222674752,714380112823641,715341461297754,
    716285383466850,717211992817474,718121400992786,719013717831236,719889051404126,
    720747508052095,721589192420570,722414207494209,723222654630375,724014633591675,
    724790242577593,725549578255240,726292735789266,727019808870942,727730889746455,
    728426069244428,729105436802705,729769080494403,730417087053276,731049541898400,
    731666529158199,732268131693836,732854431121997,733425507837064,733981441032717,
    734522308722974,735048187762683,735559153867484,736055281633260,736536644555087],
   [737003315045699,737455364453487,737892863080034,738315880197207,738724484063824,
    739118741941891,739498720112440,739864483890961,740216097642453,740553624796101,
    740877127859581,741186668433014,741482307222571,741764104053739,742032117884263,
    742286406816760,742527028111031,742754038196058,742967492681708,743167446370153,
    743353953267002,743527066592157,743686838790401,743833321541732,743966565771425,
    744086621659862,744193538652100,744287365467215,744368150107408,744435939866876,
    744490781340472,744532720432141,744561802363140,744578071680058,744581572262621,
    744572347331308,744550439454762,744515890557019,744468741924538,744409034213057,
    744336807454260,744252101062277,744154953840000,744045403985235,743923489096687,
    743789246179775,743642711652294,743483921349911,743312910531511,743129713884384,
    742934365529271,742726899025250,742507347374483,742275743026821,742032117884263,
    741776503305275,741508930108982,741229428579206,740938028468391,740634759001380,
    740319648879071,739992726281939,739654018873438,739303553803265,738941357710518,
    738567456726711,738181876478682,737784642091375,737375778190501,736955308905087,
    736523257869898,736079648227753,735624502631716,735157843247181,734679691753834,
    734190069347511,733688996741932,733176494170337,732652581386996,732117277668617,
    731570601815639,731012572153415,730443206533287,729862522333547,729270536460290,
    728667265348157,728052724960968,727426930792243,726789897865616,726141640735137,
    725482173485463,724811509731939,724129662620567,723436644827865,722732468560611,
    722017145555478,721290687078554,720553103924746,719804406417075,719044604405848,
    718273707267723,717491723904645,716698662742677,715894531730702,715079338339009,
    714253089557755,713415791895306,712567451376455,711708073540510,710837663439259,
    709956225634802,709063764197261,708160282702344,707245784228791,706320271355667,
    705383746159533,704436210211469,703477664573948,702508109797583,701527545917708,
    700535972450823,699533388390878,698519792205408,697495181831505,696459554671638,
    695412907589294,694355236904468,693286538388973,692206807261576,691116038182965,
    690014225250522,688901361992921,687777441364534,686642455739641,685496396906444,
    684339256060878,683171023800219,681991690116472,680801244389550,679599675380226],
   [678386971222860,677163119417888,675928106824080,674681919650541,673424543448473,
    672155963102670,670876162822747,669585126134107,668282835868614,666969274154993,
    665644422408920,664308261322825,662960770855368,661601930220602,660231717876807,
    658850111514979,657457088046971,656052623593278,654636693470446,653209272178101,
    651770333385585,650319849918184,648857793742945,647384135954047,645898846757744,
    644401895456838,642893250434680,641372879138688,639840748063348,638296822732707,
    636741067682319,635173446440633,633593921509811,632002454345949,630399005338678,
    628783533790137,627155997893276,625516354709488,623864560145529,622200568929708,
    620524334587319,618835809415291,617134944456024,615421689470377,613695992909791,
    611957801887501,610207062148800,608443718040340,606667712478412,604878986916172,
    603077481309776,601263134083384,599435882092972,597595660588928,595742403177366,
    593876041780113,591996506593311,590103726044592,588197626748739,586278133461803,
    584345169033582,582398654358417,580438508324215,578464647759634,576476987379342,
    574475439727278,572459915117816,570430321574739,568386564767935,566328547947705,
    564256171876569,562169334758473,560067932165253,557951856960251,555820999218930,
    553675246146357,551514481991405,549338587957501,547147442109771,544940919278389,
    542718890957952,540481225202672,538227786517184,535958435742739,533673029938545,
    531371422258003,529053461819575,526718993571994,524367858153513,521999891744870,
    519614925915636,517212787463561,514793298246543,512356275006808,509901529186838,
    507428866736591,504938087911502,502428987060719,499901352404998,497354965803637,
    494789602509784,492205030913399,489601012271118,486977300422182,484333641489556,
    481669773565285,478985426379059,476280320948890,473554169212706,470806673639572,
    468037526819167,465246411027987,462432997770678,459596947294711,456737908076507,
    453855516276921,450949395163841,448019154499436,445064389889388,442084682091182,
    439079596278272,436048681256640,432991468629939,429907471909033,426796185561358,
    423657083995056,420489620472347,417293225946018,414067307812291,410811248572609,
    407524404396097,404206103573531,400855644852671,397472295643624,394055290081656,
    390603826933355,387117067330416,383594132313378,380034100165487,376436003514372],
   [372798826176334,369121499714779,365402899680522,361641841497284,357837075950610,
    353987284232495,350091072487069,346146965794568,342153401521265,338108721951772,
    334011166106776,329858860633407,325649809636520,321381883296429,317052805091360,
    312660137409741,308201265297291,303673378034647,299073448180880,294398207643478,
    289644120242411,284807350119484,279883725197257,274868694705292,269757279552434,
    264544014015185,259222876809815,253787209086186,248229616176677,242541848985502,
    236714659612305,230737624020804,224598922065203,218285061630387,211780528487662,
    205067335850451,198124436108227,190926939406342,183445055397435,175642627948467,
    167475053345434,158886231827558,149803939734287,140132489712671,129740439714030,
    118438530578627,105936255605582,91744536452402,74909670740068,52969337825242]]
private def rkmPhb_w64_m32_s4 : List ℕ := uNatCatN
  [
   [697618147490540,698446293849763,699266294157656,700078192095405,700882030859789,
    701677853170956,702465701280035,703245616976599,704017641595963,704781816026344,
    705538180715862,706286775679411,707027640505380,707760814362248,708486336005039,
    709204243781653,709914575639071,710617369129433,711312661416000,712000489279000,
    712680889121357,713353896974312,714019548502928,714677879011500,715328923448853,
    715972716413542,716609292158952,717238684598302,717860927309556,718476053540240,
    719084096212170,719685087926092,720279060966236,720866047304784,721446078606264,
    722019186231850,722585401243596,723144754408588,723697276203022,724242996816208,
    724781946154501,725314153845167,725839649240175,726358461419923,726870619196903,
    727376151119294,727875085474498,728367450292614,728853273349849,729332582171872,
    729805404037110,730271765979988,730731694794115,731185217035411,731632359025185,
    732073146853163,732507606380462,732935763242511,733357642851934,733773270401371,
    734182670866266,734585869007599,734982889374579,735373756307290,735758493939296,
    736137126200202,736509676818173,736876169322416,737236627045619,737591073126353,
    737939530511431,738282021958240,738618570037022,738949197133131,739273925449251,
    739592777007574,739905773651954,740212937050015,740514288695243,740809849909027,
    741099641842685,741383685479447,741662001636416,741934610966492,742201533960278,
    742462790947942,742718402101063,742968387434446,743212766807909,743451559928042,
    743684786349942,743912465478925,744134616572206,744351258740561,744562410949960,
    744768092023179,744968320641389,745163115345718,745352494538793,745536476486266,
    745715079318303,745888321031067,746056219488175,746218792422125,746376057435721,
    746528032003460,746674733472913,746816179066076,746952385880711,747083370891663,
    747209150952160,747329742795097,747445163034296,747555428165759,747660554568897,
    747760558507738,747855456132131,747945263478924,748029996473125,748109670929057,
    748184302551490,748253906936754,748318499573851,748378095845538,748432711029402,
    748482360298922,748527058724515,748566821274566,748601662816450,748631598117535,
    748656641846178,748676808572698,748692112770352,748702568816282,748708190992459,
    748708993486617,748704990393167,748696195714102,748682623359899,748664287150396],
   [748641200815666,748613377996880,748580832247159,748543577032408,748501625732153,
    748454991640354,748403687966218,748347727834998,748287124288776,748221890287253,
    748152038708509,748077582349769,747998533928154,747914906081418,747826711368688,
    747733962271183,747636671192933,747534850461483,747428512328592,747317668970925,
    747202332490731,747082514916520,746958228203727,746829484235371,746696294822704,
    746558671705853,746416626554456,746270170968287,746119316477882,745964074545144,
    745804456563953,745640473860767,745472137695208,745299459260651,745122449684804,
    744941120030274,744755481295136,744565544413493,744371320256024,744172819630534,
    743970053282493,743763031895569,743551766092156,743336266433896,743116543422197,
    742892607498741,742664469045988,742432138387681,742195625789331,741954941458711,
    741710095546338,741461098145948,741207959294972,740950688975000,740689297112243,
    740423793577994,740154188189074,739880490708285,739602710844847,739320858254841,
    739034942541637,738744973256325,738450959898139,738152911914875,737850838703304,
    737544749609588,737234653929679,736920560909725,736602479746469,736280419587637,
    735954389532332,735624398631416,735290455887894,734952570257288,734610750648015,
    734265005921749,733915344893796,733561776333448,733204308964344,732842951464827,
    732477712468291,732108600563528,731735624295078,731358792163561,730978112626021,
    730593594096253,730205244945138,729813073500970,729417088049774,729017296835633,
    728613708061000,728206329887016,727795170433817,727380237780845,726961539967152,
    726539084991697,726112880813654,725682935352701,725249256489311,724811852065052,
    724370729882862,723925897707343,723477363265039,723025134244712,722569218297624,
    722109623037809,721646356042339,721179424851600,720708836969553,720234599863998,
    719756720966837,719275207674328,718790067347345,718301307311631,717808934858047,
    717312957242822,716813381687799,716310215380678,715803465475262,715293139091691,
    714779243316683,714261785203766,713740771773517,713216210013784,712688106879923,
    712156469295017,711621304150108,711082618304413,710540418585549,709994711789747,
    709445504682074,708892803996640,708336616436818,707776948675449,707213807355055,
    706647199088041,706077130456905,705503608014436,704926638283918,704346227759332],
   [703762382905547,703175110158522,702584415925498,701990306585190,701392788487978,
    700791867956095,700187551283818,699579844737650,698968754556506,698354286951894,
    697736448108098,697115244182358,696490681305042,695862765579829,695231503083882,
    694596899868019,693958961956886,693317695349128,692673106017557,692025199909319,
    691373982946060,690719461024094,690061640014559,689400525763586,688736124092453,
    688068440797750,687397481651532,686723252401478,686045758771045,685365006459620,
    684681001142677,683993748471924,683303254075453,682609523557892,681912562500549,
    681212376461560,680508970976034,679802351556194,679092523691523,678379492848906,
    677663264472765,676943843985204,676221236786144,675495448253459,674766483743115,
    674034348589302,673299048104567,672560587579950,671818972285111,671074207468462,
    670326298357300,669575250157927,668821068055786,668063757215580,667303322781405,
    666539769876863,665773103605199,665003329049409,664230451272374,663454475316970,
    662675406206195,661893248943282,661108008511821,660319689875869,659528297980075,
    658733837749786,657936314091166,657135731891305,656332096018335,655525411321540,
    654715682631465,653902914760025,653087112500618,652268280628226,651446423899529,
    650621547053005,649793654809040,648962751870029,648128842920482,647291932627127,
    646452025639010,645609126587598,644763240086880,643914370733466,643062523106684,
    642207701768685,641349911264532,640489156122303,639625440853184,638758769951568,
    637889147895142,637016579144993,636141068145689,635262619325380,634381237095886,
    633496925852790,632609689975526,631719533827473,630826461756040,629930478092758,
    629031587153366,628129793237897,627225100630768,626317513600865,625407036401625,
    624493673271127,623577428432169,622658306092357,621736310444186,620811445665122,
    619883715917684,618953125349525,618019678093514,617083378267813,616144229975959,
    615202237306942,614257404335284,613309735121114,612359233710250,611405904134269,
    610449750410591,609490776542546,608528986519458,607564384316712,606596973895830,
    605626759204548,604653744176885,603677932733214,602699328780340,601717936211567,
    600733758906768,599746800732459,598757065541866,597764557174996,596769279458704,
    595771236206766,594770431219940,593766868286040,592760551180000,591751483663939],
   [590739669487233,589725112386575,588707816086040,587687784297155,586665020718959,
    585639529038069,584611312928741,583580376052937,582546722060384,581510354588638,
    580471277263145,579429493697302,578385007492522,577337822238287,576287941512216,
    575235368880118,574180107896057,573122162102407,572061535029913,570998230197747,
    569932251113568,568863601273578,567792284162580,566718303254031,565641662010105,
    564562363881744,563480412308713,562395810719660,561308562532164,560218671152795,
    559126139977167,558030972389990,556933171765124,555832741465632,554729684843835,
    553624005241360,552515705989196,551404790407742,550291261806865,549175123485940,
    548056378733913,546935030829343,545811083040452,544684538625183,543555400831238,
    542423672896137,541289358047260,540152459501898,539012980467303,537870924140732,
    536726293709497,535579092351013,534429323232842,533276989512742,532122094338714,
    530964640849045,529804632172356,528642071427648,527476961724346,526309306162342,
    525139107832045,523966369814420,522791095181037,521613286994108,520432948306538,
    519250082161965,518064691594800,516876779630275,515686349284484,514493403564422,
    513297945468031,512099977984239,510899504093004,509696526765352,508491048963421,
    507283073640500,506072603741068,504859642200840,503644191946799,502426255897241,
    501205836961814,499982938041555,498757562028933,497529711807880,496299390253841,
    495066600233801,493831344606330,492593626221619,491353447921517,490110812539569,
    488865722901054,487618181823019,486368192114319,485115756575652,483860877999596,
    482603559170644,481343802865240,480081611851817,478816988890828,477549936734785,
    476280458128293,475008555808085,473734232503056,472457490934296,471178333815128,
    469896763851139,468612783740215,467326396172574,466037603830800,464746409389876,
    463452815517216,462156824872701,460858440108707,459557663870142,458254498794475,
    456948947511771,455641012644718,454330696808665,453018002611650,451702932654432,
    450385489530520,449065675826208,447743494120605,446418946985662,445092036986206,
    443762766679970,442431138617622,441097155342795,439760819392119,438422133295247,
    437081099574888,435737720746832,434391999319985,433043937796392,431693538671271,
    430340804433038,428985737563335,427628340537064,426268615822408,424906565880863],
   [423542193167265,422175500129819,420806489210122,419435162843198,418061523457518,
    416685573475031,415307315311189,413926751374977,412543884068935,411158715789188,
    409771248925472,408381485861158,406989428973280,405595080632560,404198443203437,
    402799519044087,401398310506451,399994819936264,398589049673073,397181002050270,
    395770679395110,394358084028741,392943218266225,391526084416564,390106684782727,
    388685021661669,387261097344360,385834914115805,384406474255072,382975780035312,
    381542833723786,380107637581885,378670193865157,377230504823328,375788572700324,
    374344399734299,372897988157651,371449340197052,369998458073464,368545344002167,
    367090000192776,365632428849270,364172632170008,362710612347755,361246371569701,
    359779912017485,358311235867218,356840345289499,355367242449445,353891929506702,
    352414408615477,350934681924551,349452751577304,347968619711736,346482288460485,
    344993759950851,343503036304816,342010119639061,340515012064992,339017715688756,
    337518232611263,336016564928206,334512714730081,333006684102207,331498475124744,
    329988089872715,328475530416026,326960798819482,325443897142811,323924827440678,
    322403591762711,320880192153513,319354630652685,317826909294846,316297030109648,
    314764995121796,313230806351070,311694465812338,310155975515581,308615337465903,
    307072553663557,305527626103958,303980556777706,302431347670599,300880000763652,
    299326518033118,297770901450502,296213152982581,294653274591420,293091268234390,
    291527135864186,289960879428843,288392500871754,286822002131689,285249385142806,
    283674651834676,282097804132294,280518843956097,278937773221983,277354593841324,
    275769307720985,274181916763342,272592422866293,271000827923280,269407133823301,
    267811342450929,266213455686326,264613475405261,263011403479123,261407241774942,
    259800992155397,258192656478839,256582236599303,254969734366524,253355151625951,
    251738490218767,250119751981899,248498938748036,246876052345643,245251094598978,
    243624067328104,241994972348908,240363811473110,238730586508285,237095299257871,
    235457951521188,233818545093451,232177081765785,230533563325238,228887991554798,
    227240368233405,225590695135966,223938974033370,222285206692500,220629394876249,
    218971540343534,217311644849309,215649710144578,213985737976411,212319730087957],
   [210651688218456,208981614103255,207309509473819,205635376057746,203959215578782,
    202281029756831,200600820307969,198918588944461,197234337374768,195548067303565,
    193859780431752,192169478456467,190477163071099,188782835965301,187086498825005,
    185388153332429,183687801166095,181985444000841,180281083507831,178574721354568,
    176866359204909,175155998719075,173443641553666,171729289361667,170012943792469,
    168294606491875,166574279102112,164851963261849,163127660606201,161401372766748,
    159673101371540,157942848045117,156210614408512,154476402079271,152740212671458,
    151002047795671,149261909059052,147519798065296,145775716414668,144029665704011,
    142281647526756,140531663472936,138779715129198,137025804078810,135269931901675,
    133512100174344,131752310470024,129990564358589,128226863406592,126461209177278,
    124693603230589,122924047123183,121152542408436,119379090636461,117603693354112,
    115826352104998,114047068429494,112265843864750,110482679944701,108697578200081,
    106910540158429,105121567344100,103330661278280,101537823478991,99743055461103,
    97946358736344,96147734813311,94347185197480,92544711391215,90740314893779,88933997201342,
    87125759806995,85315604200755,83503531869579,81689544297371,79873642964993,78055829350274,
    76236104928021,74414471170028,72590929545084,70765481518985,68938128554541,67108872111589,
    65277713646998,63444654614684,61609696465612,59772840647812,57934088606385,56093441783513,
    54250901618466,52406469547617,50560147004444,48711935419544,46861836220640,45009850832590,
    43155980677396,41300227174216,39442591739366,37583075786337,35721680725796,33858407965602,
    31993258910809,30126234963679,28257337523686,26386567987530,24513927749141,22639418199690,
    20763040727599,18884796718544,17004687555469,15122714618592,13238879285414,11353182930727,
    9465626926621,7576212642495,5684941445065,3791814698368,1896833763776]]
private theorem rkmStatOk_hiw64t07 : bAllT [
  muxIntListEq (uHb rkmPhb_w64_m32_s0) (altBuildHbFrom 64 1024 362194750000 0 64),
  muxIntListEq (uHb rkmPhb_w64_m32_s1) (altBuildHbFrom 128 1024 186509809523 0 128),
  muxIntListEq (uHb rkmPhb_w64_m32_s2) (altBuildHbFrom 256 1024 97199393939 0 256),
  muxIntListEq (uHb rkmPhb_w64_m32_s3) (altBuildHbFrom 512 1024 51677427350 42 470),
  muxIntListEq (uHb rkmPhb_w64_m32_s4) (altBuildHbFrom 1024 1024 29638027559 206 818),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_m32_s0_in)) (Nat.add 64 1),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_m32_s1_in)) (Nat.add 128 1),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_m32_s2_in)) (Nat.add 256 1),
  Nat.ble (Nat.add 58 (altIntLen rkmXsWin_w64_m32_s3_in)) (Nat.add 512 1),
  Nat.ble (Nat.add 222 (altIntLen rkmXsWin_w64_m32_s4_in)) (Nat.add 1024 1)
  ] = true := by decide +kernel
private theorem rkmHhb_w64_m32_s0 :
    uHb rkmPhb_w64_m32_s0 = rkmDropInts 0 rkmHbWin_w64_m32_s0 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd rkmStatOk_hiw64t07)).trans
    (drHb 64 1024 362194750000 0 64)
private theorem rkmHhb_w64_m32_s1 :
    uHb rkmPhb_w64_m32_s1 = rkmDropInts 0 rkmHbWin_w64_m32_s1 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl rkmStatOk_hiw64t07))).trans
    (drHb 128 1024 186509809523 0 128)
private theorem rkmHhb_w64_m32_s2 :
    uHb rkmPhb_w64_m32_s2 = rkmDropInts 0 rkmHbWin_w64_m32_s2 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl rkmStatOk_hiw64t07)))).trans
    (drHb 256 1024 97199393939 0 256)
private theorem rkmHhb_w64_m32_s3 :
    uHb rkmPhb_w64_m32_s3 = rkmDropInts 42 rkmHbWin_w64_m32_s3 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl rkmStatOk_hiw64t07))))).trans
    (drHb 512 1024 51677427350 42 512)
private theorem rkmHhb_w64_m32_s4 :
    uHb rkmPhb_w64_m32_s4 = rkmDropInts 206 rkmHbWin_w64_m32_s4 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl rkmStatOk_hiw64t07)))))).trans
    (drHb 1024 1024 29638027559 206 1024)
private theorem rkmWC_w64_m32_s0_0 : bWinChk 0 12 100000000 64 rkmPhb_w64_m32_s0
    0 rkmXsWin_w64_m32_s0_in 0 rkmXsWin_w64_m32_s0_out 699772370 = true := by decide +kernel
private theorem rkmWinIter_w64_m32_s0 :
    RkmWinIterSound 12 64 rkmHbWin_w64_m32_s0 0 rkmXsWin_w64_m32_s0_in
      0 rkmXsWin_w64_m32_s0_out 699772370 :=
  bWinChk_sound rkmHhb_w64_m32_s0 rkmWC_w64_m32_s0_0
/-- Certified `w64_m32` seg `0` (`12` steps). -/
theorem rkmWinSegWalkSnd_w64_m32_s0 :
    RkmWinSegWalkSound 12 ⟨64, rkmHbWin_w64_m32_s0, 0, rkmXsWin_w64_m32_s0_in,
      0, rkmXsWin_w64_m32_s0_out, 699772370⟩ :=
  @rkmSegWalk_mk 12 64 0 0 699772370
    rkmHbWin_w64_m32_s0 rkmXsWin_w64_m32_s0_in rkmXsWin_w64_m32_s0_out
    (rkmw_buildHbFrom_length 64 1024 362194750000 64 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl rkmStatOk_hiw64t07))))))
    rkmWinIter_w64_m32_s0
private theorem rkmWC_w64_m32_s1_0 : bWinChk 0 21 100000000 128 rkmPhb_w64_m32_s1
    0 rkmXsWin_w64_m32_s1_in 0 rkmXsWin_w64_m32_s1_out 1334447977 = true := by decide +kernel
private theorem rkmWinIter_w64_m32_s1 :
    RkmWinIterSound 21 128 rkmHbWin_w64_m32_s1 0 rkmXsWin_w64_m32_s1_in
      0 rkmXsWin_w64_m32_s1_out 1334447977 :=
  bWinChk_sound rkmHhb_w64_m32_s1 rkmWC_w64_m32_s1_0
/-- Certified `w64_m32` seg `1` (`21` steps). -/
theorem rkmWinSegWalkSnd_w64_m32_s1 :
    RkmWinSegWalkSound 21 ⟨128, rkmHbWin_w64_m32_s1, 0, rkmXsWin_w64_m32_s1_in,
      0, rkmXsWin_w64_m32_s1_out, 1334447977⟩ :=
  @rkmSegWalk_mk 21 128 0 0 1334447977
    rkmHbWin_w64_m32_s1 rkmXsWin_w64_m32_s1_in rkmXsWin_w64_m32_s1_out
    (rkmw_buildHbFrom_length 128 1024 186509809523 128 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl
      rkmStatOk_hiw64t07)))))))
    rkmWinIter_w64_m32_s1
private def rkmC_w64_m32_s2_1 : List ℤ := pzigCat
  [
   [464585316,1036880010,2003337672,3904094884,7439524756,13863229592,25156464334,44660027454,
    77593431120,131892567698,220156903910,360224963206,578434423152,911822197278,1411137635152,
    2145094127860,3204449613662,4704978455750,6792003810672,9643070848112,13467974013702,
    18508932174588,25035453399764,33336590793568,43709895611310,56443972250802,71799745218850,
    89986939789570,111138598080344,135287164839966,162340396587362,192063429221462,
    224066878101546,257803733986370,292577723675104,327561124917518,361825641113918,
    394381707565902,424225276304042,450390447393754,472000901243706,488319653281986,
    498790343153294,503068529124648,501041016761998,492828940570474,478778388706094,
    459436297042024,435515910675344,407854616663458,377365534621008,344990196536716,
    311651813809776,278214977305148,245452947516858,214022734433554,184451636630626,
    157130810307876,132318660807718,110150408598498,90652161188480,73759948644878,59338068079672,
    47199527911662,37123926326400,28873419845736,22207155637998,16890780216530,12705452282026,
    9452148853942,6954739385712,5061431885356,3643295267340,2594103760104,1827005831756,
    1272790466932,877243170570,597984715836,403374440282,269077417824,177538931114,115880493936,
    74623283534,47581608368,29771963716,18354859836,10988321098,6248797240,3174890780,1407151488,
    486802536]]
private theorem rkmWC_w64_m32_s2_0 : bWinChk 0 37 100000000 256 rkmPhb_w64_m32_s2
    0 rkmXsWin_w64_m32_s2_in 23 rkmC_w64_m32_s2_1 4921760581 = true := by decide +kernel
private theorem rkmWC_w64_m32_s2_1 : bWinChk 0 29 100000000 256 rkmPhb_w64_m32_s2
    23 rkmC_w64_m32_s2_1 58 rkmXsWin_w64_m32_s2_out 5336752323 = true := by decide +kernel
private theorem rkmWinIter_w64_m32_s2 :
    RkmWinIterSound 66 256 rkmHbWin_w64_m32_s2 0 rkmXsWin_w64_m32_s2_in
      58 rkmXsWin_w64_m32_s2_out 10258512904 :=
  rkmChS 66 10258512904 (bWinChk_sound rkmHhb_w64_m32_s2 rkmWC_w64_m32_s2_0) rkmHhb_w64_m32_s2
    rkmWC_w64_m32_s2_1 rfl rfl
/-- Certified `w64_m32` seg `2` (`66` steps). -/
theorem rkmWinSegWalkSnd_w64_m32_s2 :
    RkmWinSegWalkSound 66 ⟨256, rkmHbWin_w64_m32_s2, 0, rkmXsWin_w64_m32_s2_in,
      58, rkmXsWin_w64_m32_s2_out, 10258512904⟩ :=
  @rkmSegWalk_mk 66 256 0 58 10258512904
    rkmHbWin_w64_m32_s2 rkmXsWin_w64_m32_s2_in rkmXsWin_w64_m32_s2_out
    (rkmw_buildHbFrom_length 256 1024 97199393939 256 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl
      rkmStatOk_hiw64t07))))))))
    rkmWinIter_w64_m32_s2
private def rkmC_w64_m32_s3_1 : List ℤ := pzigCat
  [
   [568342980,898146862,1587538014,2670654756,4269042018,7085578962,11152124316,17479519210,
    27142421082,41633338460,63422657192,95395839088,142311911534,209984100418,306708097812,
    443732006970,635337354958,901024025222,1265070655786,1758791492474,2421462761038,
    3301178462064,4457101641676,5959400633306,7891564448864,10350074034620,13444520033656,
    17297998135866,22044458769360,27827619845456,34796470795014,43101135834498,52887415314798,
    64288652546886,77419215098384,92364664085280,109173451447734,127848045250888,148335949612046,
    170524024454650,194232040632486,219211014847750,245143275693286,271645586811384,
    298277256392942,324549384741508,349939950577280,373909852803538,395921409627412,
    415458967585686,432047751262008,445274376487492,454803078274246,460390060075526,
    461894253586086,459282261961200,452630899273896,442122339721438,428036422190552,
    410738318577968,390662212250270,368294556893572,344153450709218,318769958635358,
    292668765693470,266350599385956,240278342867412,214863828091172,190460371182542,
    167356600434956,145774535114530,125871065496642,107740315569986,91420485057082,
    76899701060724,64124609475488,53008838305382,43440579213480,35291723753718,28423668055980,
    22694554690568,17963962620230,14096701097212,10966787770646,8458181725450,6467293241408,
    4902491761504,3684254814050,2745092296628,2027616392566,1484905972530,1078077795362,
    775948374708,553801637866,391698868538,274760361756,190904616348,131399597948,89564537014,
    60216382590,40066420952,26064583728,16622601696,10220598574,5848160990,3115826756,1228431564,
    348913358]]
private def rkmC_w64_m32_s3_2 : List ℤ := pzigCat
  [
   [502510958,953740872,1598558730,2689950632,4134991646,6621619280,10288326182,15862030322,
    24322879742,36688551744,55113325118,81777590054,120362686654,175610063058,253675555576,
    363365274740,515482852820,724812393954,1009882728496,1394207775040,1907723164344,
    2586732190530,3476270580748,4629898255238,6111396386182,7995609756590,10368069456788,
    13326246587400,16977676587640,21439934035138,26838386341296,33302985685610,40965585473698,
    49953892487136,60387318395712,72369887972398,85983363669878,101280639296270,118277170490676,
    136945604229914,157208562538504,178934423687126,201934434084398,225960761919744,
    250709475142642,275823334399910,300899806600260,325500364971666,349161931054510,
    371412204539948,391783451723122,409830465770692,425145422915836,437373915747350,
    446228496978498,451499542448642,453064090485268,450890026174596,445037594846242,
    435656269451604,422978834525482,407311395975112,389021492304658,368523930670084,
    346264633566978,322705888557940,298309513490904,273523083094186,248767188448606,
    224423858564368,200829390911760,178267575952676,156967375249592,137101752311884,
    118789233654702,102098032383504,87049605980688,73625904346586,61775025549626,51418264752240,
    42457048007888,34778450053168,28262256910408,22784570411124,18222841420652,14459005050360,
    11381604719786,8888522530538,6886603325740,5293478598748,4036812178574,3054120519192,
    2292665419240,1707433376714,1261717202496,924963402504,672668927058,485436317576,
    347395714568,246756445992,173704056458,121175791850,83725235918,57041050156,38473073254,
    25368117454,16413705936,10226564504,5983999510,3088933116,1377639972,476127256]]
private def rkmC_w64_m32_s3_3 : List ℤ := pzigCat
  [
   [418473580,760035762,1334671198,2297847226,3627829792,5832239030,8925305820,13705949230,
    20997698374,31658645304,47591631162,70544516984,103726608918,151237988706,218420582498,
    312807764096,443707848424,623937796428,869438347546,1200828011882,1644002066592,
    2230535421156,2999969409210,3999296061518,5285024449764,6923442830244,8990923107062,
    11574978843612,14772926027862,18692523663956,23449370343954,29165269580786,35965652986220,
    43974655522366,53311894611462,64085739290924,76388128793770,90287654013036,105822263687578,
    122993996533820,141761057731896,162034248200192,183671746558834,206477637166592,
    230201506425024,254540145088428,279142883328442,303617976043478,327542528542202,
    350473680323976,371962309340850,391567230085362,408870365954290,423491540562020,
    435102034368344,443437781775152,448308167281710,449604189038190,447302270994780,
    441464408915226,432236535195400,419841177381380,404569497207440,386769630910992,
    366833605498770,345183513813216,322255977024848,298489101727546,274307927059740,
    250113120347792,226271087700212,203105324519136,180891978243660,159855597850124,
    140169283698452,121955106522754,105286707455574,90194422991982,76669378013880,64670564597804,
    54129995624844,44959352813098,37056143596156,30308150654676,24599464293002,19813363536578,
    15836631474364,12561720940214,9888129624412,7724580754398,5988460805568,4607347976622,
    3517940801688,2665754786592,2004924235666,1496401606620,1108515579094,814910999600,
    594486466990,430485041098,309180648448,220407531676,155689328584,108964499886,75512986652,
    51588780888,34858742068,22986813254,14819698434,9165111560,5242080292,2770620896,1078434234,
    301761246]]
private def rkmC_w64_m32_s3_4 : List ℤ := pzigCat
  [
   [469396030,970434014,1569540056,2662088740,4152838282,6621233136,10367222210,16079591732,
    24711511378,37320463916,56215412378,83667363444,123431664616,180443163822,261078301614,
    374364004576,531498216956,747748242850,1042146147684,1438987371738,1968793220206,
    2668635379728,3584509807324,4770894043414,6292570934040,8224929159580,10654205345088,
    13678118234214,17403991018040,21948949471494,27436876700842,33995877631606,41754822094106,
    50837826920930,61360001212890,73419892315910,87093740097052,102428084235884,119432392734508,
    138073590792528,158269195314492,179884189871470,202727375344278,226551144822944,
    251053893360418,275883387735398,300644980176320,324909849108280,348227676060142,
    370140060342256,390194779736480,407962268577002,423049684554934,435116607730476,
    443887066785870,449160108182700,450818018096584,448829609749026,443252372147678,
    434228644037210,421980316240176,406799856412450,389038152389068,369092174283984,
    347389112111134,324372533429998,300487201393230,276165285190146,251814755160324,
    227807895128780,204474496858438,182095281202454,160899188665910,141062563086586,
    122709451879286,105915579659334,90711490023570,77088836464052,65006028939330,54394263097800,
    45164563349100,37212646562428,30425547328506,24685705362470,19875359682070,15880231998152,
    12591256418464,9907523757686,7736478044254,5995259643354,4610764726760,3519025286178,
    2665595709930,2003831932934,1495028164378,1107038374528,813443203520,593243077466,
    429202635496,308120995338,219386180542,154817434430,108312022916,74872010352,51161549922,
    34343657360,22538812812,14399805178,8755042926,5028661338,2729960784,1065454734,293613470]]
private theorem rkmWC_w64_m32_s3_0 : bWinChk 42 25 100000000 512 rkmPhb_w64_m32_s3
    58 rkmXsWin_w64_m32_s3_in 88 rkmC_w64_m32_s3_1 4657463065 = true := by decide +kernel
private theorem rkmWC_w64_m32_s3_1 : bWinChk 42 23 100000000 512 rkmPhb_w64_m32_s3
    88 rkmC_w64_m32_s3_1 119 rkmC_w64_m32_s3_2 4386293031 = true := by decide +kernel
private theorem rkmWC_w64_m32_s3_2 : bWinChk 42 23 100000000 512 rkmPhb_w64_m32_s3
    119 rkmC_w64_m32_s3_2 152 rkmC_w64_m32_s3_3 4706641409 = true := by decide +kernel
private theorem rkmWC_w64_m32_s3_3 : bWinChk 42 23 100000000 512 rkmPhb_w64_m32_s3
    152 rkmC_w64_m32_s3_3 187 rkmC_w64_m32_s3_4 4288982415 = true := by decide +kernel
private theorem rkmWC_w64_m32_s3_4 : bWinChk 42 23 100000000 512 rkmPhb_w64_m32_s3
    187 rkmC_w64_m32_s3_4 222 rkmXsWin_w64_m32_s3_out 4499311017 = true := by decide +kernel
private theorem rkmWinIter_w64_m32_s3 :
    RkmWinIterSound 117 512 rkmHbWin_w64_m32_s3 58 rkmXsWin_w64_m32_s3_in
      222 rkmXsWin_w64_m32_s3_out 22538690937 :=
  rkmChS 117 22538690937 (rkmChS 94 18039379920 (rkmChS 71 13750397505 (rkmChS 48 9043756096
    (bWinChk_sound rkmHhb_w64_m32_s3 rkmWC_w64_m32_s3_0) rkmHhb_w64_m32_s3 rkmWC_w64_m32_s3_1
    rfl rfl) rkmHhb_w64_m32_s3 rkmWC_w64_m32_s3_2 rfl rfl) rkmHhb_w64_m32_s3 rkmWC_w64_m32_s3_3
    rfl rfl) rkmHhb_w64_m32_s3 rkmWC_w64_m32_s3_4 rfl rfl
/-- Certified `w64_m32` seg `3` (`117` steps). -/
theorem rkmWinSegWalkSnd_w64_m32_s3 :
    RkmWinSegWalkSound 117 ⟨512, rkmHbWin_w64_m32_s3, 58, rkmXsWin_w64_m32_s3_in,
      222, rkmXsWin_w64_m32_s3_out, 22538690937⟩ :=
  @rkmSegWalk_mk 117 512 58 222 22538690937
    rkmHbWin_w64_m32_s3 rkmXsWin_w64_m32_s3_in rkmXsWin_w64_m32_s3_out
    (rkmw_buildHbFrom_length 512 1024 51677427350 512 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl
      rkmStatOk_hiw64t07)))))))))
    rkmWinIter_w64_m32_s3
private def rkmC_w64_m32_s4_1 : List ℤ := pzigCat
  [
   [271177658,718613178,1327067408,2200238464,3871688134,6240428172,10227987236,16363249512,
    25850588146,40502560692,62540038050,95467007056,144080164594,214655371368,316282484038,
    460610719936,663363059750,944918918380,1331140406060,1855186500992,2557744468628,
    3489375926604,4710650071682,6293489827414,8322583963598,10894234870140,14117838113012,
    18113725002560,23011714130766,28948933818054,36065691482278,44500914169066,54386578119220,
    65840499551532,78959646497620,93811682131864,110427718021804,128794552416914,148847486810700,
    170465886050804,193468311057228,217612549496738,242596131539884,268060340024206,
    293597984164248,318762572081680,343080639244754,366067231735696,387240852401232,
    406141059355674,422344742492760,435481805938378,445250148696072,451425887078244,
    453873036828736,452547806432376,447499819789370,438869638468920,426881845221854,
    411835847599370,394094139923722,374066743205220,352196825622348,328944525808112,
    304771097880690,280125131084742,255428551081192,231067452196160,207382457259330,
    184663151481614,163145789932770,143010885628358,124386041881510,107347806700048,
    91927356767260,78115364047608,65868487445894,55116169774072,45766677911830,37713579110930,
    30841200503572,25030088929088,20160284759226,16115540502836,12785519375026,10067353715324,
    7867887165678,6102993267828,4698742549456,3590727432136,2723615920238,2050797031042,
    1532614975940,1136926559922,837108714292,611719551076,443702797268,319123941152,227734744402,
    161026397174,112812794734,78247879618,53450389448,36059486622,23721969560,15278843662,
    9491727390,5492819900,2966261758,1183660082,339730442]]
private def rkmC_w64_m32_s4_2 : List ℤ := pzigCat
  [
   [330175514,657209034,1393632456,2279884866,3975735586,6765148906,11134695156,18195013640,
    29220807632,46233294586,72196121152,111027979024,168589578544,252601869804,373696738722,
    546418470398,788890563478,1125459551046,1586763853372,2211200832666,3046862730508,
    4151183761362,5593930494938,7456231841104,9832256875916,12828716859704,16564047449844,
    21167313832422,26774763480288,33527334248372,41565742080634,51024913881530,62027177575952,
    74675533927030,89045694383018,105177685300004,123069014489056,142667187921626,
    163864793538542,186494717325906,210328884893468,235079618999154,260401877732768,
    285901295832324,311142453232460,335660932422160,358977680065964,380613852266992,
    400108231606930,417032529757208,431008188781942,441719972023988,448927553053480,
    452475420743740,452297003475628,448417852444714,440952868923388,430101160390524,
    416137748242930,399401263408916,380281945363312,359205385513636,336618174636432,
    312972674134984,288712136378170,264258912795816,240001869631822,216289417191314,
    193421954691444,171648609321718,151165505833286,132116216419900,114594605133060,
    98648289594796,84283984565630,71472947581094,60157881119934,50258386085926,41677462496946,
    34307127019984,28032628849328,22738134711718,18309079647220,14635546686050,11614355119842,
    9150137851428,7156991504644,5557703057944,4284961000022,3280214796488,2493129705612,
    1881525736288,1409682594920,1048750965372,774662015634,568021289550,413480412756,
    298499040316,213889038326,151896915240,106905286732,74502591194,51144069300,34698442766,
    22964381560,14882195270,9290141120,5388914240,2907821734,1156470900,330478838]]
private def rkmC_w64_m32_s4_3 : List ℤ := pzigCat
  [
   [507530456,898886172,1791903448,3348649172,6097701220,10403897242,17241492384,28530451824,
    46042092292,73362315632,114925498228,177112751828,269019260816,402415148216,593952774776,
    864460608006,1241777741682,1760664836000,2464822090552,3408313542702,4656113424186,
    6285890808548,8387882447928,11065699220138,14435466912078,18624836747938,23770697248462,
    30015872686814,37504997038448,46378796235916,56768354300754,68786907069048,82522935160802,
    98031712002456,115326897367498,134374349142794,155084653647566,177309815616296,
    200840219273896,225404449400894,250673089656182,276263469590084,301749244279798,
    326670721269826,350549174601076,372902190943878,393259191159244,411179294728848,
    426265972871914,438182764971538,446665451784324,451531427492272,452686873216974,
    450128397688256,443943580977010,434305312431972,421464336505358,405739177604992,
    387502410483852,367167597270262,345172777169054,321966416739822,297992707442082,
    273677918849536,249420142307716,225578620493334,202468122879312,180353376317204,
    159447067960378,139910442706906,121853917888190,105341874278286,90395849261560,
    77000919332180,65111620994628,54657295556466,45549310022168,37685031815284,30954541751832,
    25244055575214,20440239376346,16433099328118,13118089204412,10398035047770,8184079538414,
    6396555141808,4964516277476,3826441398920,2928893092672,2226270412894,1680634732000,
    1259865622682,937931570470,693321901784,508869669954,370889878470,268125907954,192344802666,
    136734596520,96371021190,67300742154,46307759638,31430977670,20743004280,13337933076,
    8222714038,4699189560,2493233520,978018380,276254396]]
private def rkmC_w64_m32_s4_4 : List ℤ := pzigCat
  [
   [320240640,733360656,1453974320,3087020706,5738258592,10485225350,18322144304,31330453108,
    52341273852,85289507836,136577323012,214163746346,329865539846,499322568030,743454725898,
    1089936561648,1573577492204,2239170601220,3141501478534,4347735497430,5938097818738,
    8006024470648,10659705227284,14019932079778,18220336825978,23403452912044,29718247406268,
    37315299028652,46340464369392,56928611382674,69195196932610,83228692817832,99081547651708,
    116762197797634,136227525710830,157376921561942,180047935891074,204014070859380,
    228986194675776,254615338924760,280500407820218,306197212362948,331230732558694,
    355110527718822,377345514445968,397462192635326,415020997541938,429632468432632,
    440972051318702,448791253146006,452927575287170,453309008545292,449956636357980,
    442982169627298,432581773251536,419028355023802,402658881218308,383861826783680,
    363061706597104,340703888075672,317239941228524,293112457560168,268743654400940,
    244523392496932,220801022122412,197879156925638,176009358429764,155391660071688,
    136173739116858,118454267728982,102286207870384,87681603586304,74617841898184,63042521642692,
    52880830263968,44040428928942,36417315636706,29900895767808,24377508792084,19735236598726,
    15865495849960,12666024567168,10041981526776,7906635852578,6182787379554,4801645737392,
    3703742543840,2837567505266,2159189193796,1631988977398,1224980209794,913273266498,
    676152325718,497086157372,362950523824,262943657570,189133390250,134810897104,95210454836,
    66568295794,45856298712,31211245422,20694846416,13385251834,8282832642,4729773258,2491268330,
    966120124,269412934]]
private def rkmC_w64_m32_s4_5 : List ℤ := pzigCat
  [
   [740909060,2027859182,4533102536,9253752146,17919808526,32561836310,57252284006,97259427452,
    160525299926,258352409888,405978672490,624626752248,941786674524,1393843666992,2026786005968,
    2898106886430,4078670200418,5652855314626,7720638523702,10396648769164,13810158424704,
    18103292473312,23427884454940,29942389570420,37805179951760,47169201106020,58173742062564,
    70935912547676,85542046735730,102037582224360,120419747636322,140628901709704,
    162543258491742,185975137727650,210669130968530,236305024084924,262501765059438,
    288826972127466,314807693495628,339944234190416,363726992855248,385652912522674,
    405244650193142,422066987820766,435743456127220,445970594623640,452528369709778,
    455288949279806,454219298880738,449381995463192,440930864370600,429103148090462,
    414209686821160,396620743425022,376752458417320,355050316215938,331973572104762,
    307980387252366,283513086601534,258987239944872,234780558436374,211225992598548,
    188606391363402,167151418228814,147038100899046,128391251867266,111287682707526,
    95759996313536,81802080804388,69375639792434,58415461755720,48836650152194,40539393761066,
    33414756018366,27349354871154,22228742274546,17941635006490,14381328202974,11448384603212,
    9051400079594,7107543404782,5543492161928,4294358211844,3304374609946,2525555659588,
    1917303825580,1445897270338,1082971217472,805750920456,595360367206,436820892894,
    318271429800,230066414690,165090479674,117379423652,82671615446,57595183352,39487199378,
    26673120216,17497674764,11145360096,6759944904,3772751170,1935205998,733127910,200224364]]
private def rkmC_w64_m32_s4_6 : List ℤ := pzigCat
  [
   [254523049,605964471,521988935,164792778,2132745940,6802752076,16012933240,33428660702,
    63942545580,115448710486,199215146904,331059225654,533343560610,835428559690,1276530728866,
    1906686740476,2789163684578,4002101189502,5638984795520,7810423530950,10643127172164,
    14279847952240,18876646722018,24599099916480,31618032852002,40102100143998,50211067600392,
    62086007710416,75839959380074,91548174458426,109237624170482,128879088267442,150378707121788,
    173573514219088,198228646896606,224037706980508,250627654779360,277565529438914,
    304370567501442,330527648278848,355504055688640,378768166446066,399807901366762,
    418150773634850,433380786323004,445154666909226,453214491971526,457396489535450,
    457637038004334,453972636472490,446537427317216,435555470537830,421330178295600,
    404231509364664,384679908786952,363130841639896,340057246248730,315933879293048,
    291222271620564,266357513001578,241737671103830,217715332967790,194591512519590,
    172613227647612,151971605830584,132804351501792,115198306001992,99193736466214,
    84790980320144,71954995731528,60623155175776,50711029592924,42118115743754,34734319796940,
    28443808533138,23130020245532,18678365317006,14979349923834,11930562311216,9437278422018,
    7414385984214,5785693270020,4484379315350,3452479409918,2640129453744,2005561108082,
    1513301556432,1134233829978,844374813540,624258328664,458413962108,334283426872,241876305090,
    173766793912,123566215090,87084225614,60783255008,41736471890,28248190586,18616409010,
    11991129166,7372333882,4152685222,2128874830,797112204,214102826]]
private def rkmC_w64_m32_s4_7 : List ℤ := pzigCat
  [
   [366568737,812783205,1567816045,2399882481,3398995903,3883277831,2852574101,1566321314,
    12702323828,35852998946,79345165688,155792948682,283109853990,486917804928,801683636784,
    1273348112782,1961415110278,2940454180032,4302933396398,6159080522158,8638393479078,
    11888622122698,16073370708572,21369819043200,27962041470408,36035477037558,45768112895252,
    57320461568156,70825737387850,86377486274172,104019406315592,123734688287946,145437769710896,
    168968254965356,194087289261514,220478754012518,247752450741894,275453418150226,
    303073545771092,330066990666400,355868701912560,379914302716678,401660946101452,
    420608449417310,436317999260480,448429827928842,456675828630580,460889638145262,
    461011984779536,457089995408806,449274559797220,437810769273078,423026489379966,
    405317831482606,385131478559262,362948346869668,339264601828084,314575078699992,
    289357665884120,264059770236264,239087327808670,214796484651044,191488263224818,
    169406298352776,148735605664708,129605855040698,112094213944912,96230660483132,
    82005000575812,69372038238122,58259762330122,48575142962138,40210487324398,33049762273726,
    26972342216082,21858000626060,17589703222890,14056717840956,11155999328632,8793106157960,
    6883375006746,5351929241058,4132938224986,3170221744886,2415320688184,1827825342498,
    1374123130402,1025914786744,760832205444,560371827960,409842210990,297560780172,214308123956,
    153136047480,108497978618,75926566882,52696528888,35952732872,24031910582,15754134266,
    9867991410,5902692662,3110258826,1387284854,462979620]]
private def rkmC_w64_m32_s4_8 : List ℤ := pzigCat
  [
   [206602510,205111864,140441645,999267515,2261701365,4531025347,7437211449,10951186787,
    14187874977,14997141325,9830755693,7877721812,48867251486,129202365518,272851986528,
    513152475332,896052163722,1482329525814,2349974725220,3596923436650,5341514329320,
    7724256103766,10906257515684,15067493185676,20403169856362,27116272709314,35411382849024,
    45483622867570,57507642734456,71625531893014,87933614693484,106470153996172,127204238401856,
    150026464574568,174743564273534,201075207710296,228656556131916,257044268316414,
    285727381040096,314143144875640,341694391238962,367772432995106,391778870935436,
    413149111580928,431375288156944,446025645403838,456761655349250,463351242376916,
    465675563908382,463732649855518,457633947732686,447597474730480,433936608496502,
    417043695335798,397373747373096,375424210346692,351716287049274,326775728121612,
    301114628471830,275216909666640,249525572383812,224432006665888,200270579882030,
    177314000765926,155773133647212,135798424746548,117483327592514,100870866469938,
    85958350433628,72705663967688,61042415095218,50874586979428,42091914572788,34573943976750,
    28194939548814,22829159235080,18353548346178,14651665892174,11614787313096,9143173790402,
    7147928388660,5549615893484,4279178578724,3277136014466,2492694849546,1883195862076,
    1413072554912,1053025430098,779500693262,572840319704,418009522208,302858571974,217620467782,
    155117797706,109651480316,76598599510,53046699756,36057412718,24002383960,15650442078,
    9720399074,5722271250,2946400860,1277593018,414132634]]
private def rkmC_w64_m32_s4_9 : List ℤ := pzigCat
  [
   [372247368,617357598,711352694,874995902,328381690,952094257,3707201133,8492873065,
    15575938187,24960820477,35487956261,44370722115,45905904439,29377341875,21911609138,
    134142508078,345205578580,707468578818,1292183113128,2190849991730,3519005086812,
    5416844875506,8049603440628,11606518957170,16296599782422,22342902610678,29974521261138,
    39415389859530,50872467509176,64520532977040,80488203221442,98843771224516,119580107226636,
    142605095311486,167732972761492,194681192595300,223071507587716,252436365357776,
    282231209435178,311850752907772,340649700982274,367967913132304,393154771558334,
    415596611578302,434741638035782,450122230427662,461373993860640,468249539449804,
    470626553655114,468510723440848,462031370219034,451433715204432,437064384768514,
    419353618204544,398796933649330,375931857842534,351317464972766,325513555501656,
    299061219640838,272467103479184,246190089506570,220631250172422,196128257180504,
    172951405801672,151304745143558,131328059346832,113101820725168,96653794422222,
    81965993001548,68982815013852,57619537964636,47768646098848,39308572143838,32109154905490,
    26036815411526,20959852314468,16751502145012,13292270382656,10472665390742,8192790258192,
    6364218270124,4909398817796,3760780294460,2860958045262,2161522753798,1621622448310,
    1208322097786,894041696778,656761097944,479095908546,346876882256,249182581254,177724087218,
    125455948104,87769127276,60698869948,41290076166,27665758120,18077588902,11257119860,
    6752123062,3538011402,1542374424,494665926]]
private def rkmC_w64_m32_s4_10 : List ℤ := pzigCat
  [
   [429150342,1234272492,1974972274,2776609468,3090511938,2405863444,267986153,6401403341,
    17097345793,33582261991,56352504485,83359910059,110020404433,125432396379,110476147287,
    34897579847,147068608672,500466453124,1113298511160,2100589784676,3606171972950,
    5804613448738,8899279380890,13119707748962,18715301021790,25945554618742,35068460445016,
    46325932898166,59926245633944,76027852678020,94720458786952,116009659684312,139803976576838,
    165904696963870,194002282450598,223678506331636,254413183580084,285600236801390,
    316566744398260,346598117426490,374966812306626,400961891338388,423919686900706,
    443252608957772,458472697164264,469213352555524,475242107562136,476467851095128,
    472941751015646,464850167731424,452502341252046,436313601000264,416782701595342,
    394469856434286,369971283078048,343894929504510,316838807769230,289370613353674,
    262011190481368,235222832474438,209399057893958,184861289543568,161857214432140,
    140562422526120,121085789247330,103475659074322,87727440971370,73793559718712,61590843956556,
    51010277890822,41924973623670,34196887521428,27683785043726,22244274184560,17741147324094,
    14045814457078,11039083686960,8613070427124,6671954286436,5131316459142,3918232093136,
    2970845588050,2236432875818,1671713383152,1240792424196,914310196140,668934571304,
    485857017746,350097559968,250432221694,177579648248,124787052286,86872143786,59671558928,
    40343209558,26760288822,17170372462,10512715676,6239674456,3224025342,1374623248,428283974]]
private def rkmC_w64_m32_s4_11 : List ℤ := pzigCat
  [
   [1162899638,2507319838,4638413084,6951157716,8656869686,8654612886,4613905550,6148678705,
    26432816855,59524220207,106429638907,165378780175,228535150781,278455330249,284460106577,
    197003378053,57391636458,580114713566,1506446927822,3007204096622,5290089334180,
    8598008400804,13203026581074,19397864173702,27483167079172,37750138942252,50462913172304,
    65836313767812,84014707423492,105052158777064,128894338839820,155366059726842,
    184164673686618,214859092601848,246899056357110,279629680468142,312314198280806,
    344163135914084,374366702758776,402130433004048,426711201644066,447449397552062,
    463799270219410,475351608443072,481849397156422,483196593336570,479456708205290,
    470845269980034,457714459289844,440532115611006,419856482645802,396309394464686,
    370547044684926,343233594568288,315015821142570,286501034637324,258240222604656,
    230714917099354,204328169176502,179402097113490,156176776687642,134814159561044,
    115405131138222,97976630996908,82501838471160,68910250838624,57097458176882,46934527989980,
    38277558084866,30974147090892,24870665599724,19817045747712,15670178545586,12297663750258,
    9578815798602,7405511187726,5682855881090,4329094569650,3273580840510,2457358206636,
    1831309854208,1354662221660,994743436460,725150030134,524618954198,376575129874,268357704312,
    189443527056,132494645492,91747283560,62604062014,42062757706,27792528132,17804310474,
    10889461300,6399362994,3230107676,1332219438,400045574]]
private def rkmC_w64_m32_s4_12 : List ℤ := pzigCat
  [
   [212934693,795997137,1185425125,1247323551,665137113,1056970232,4219424344,8772374114,
    14494826442,19933422334,22795671326,19239845532,3762432058,29827465735,87463184027,
    173268969293,285646962231,413905394375,532539872731,594367603571,525102963245,215138314909,
    485420196754,1770715216216,3880715306236,7098387222292,11742325051280,18155678336000,
    26688632081806,37677010134696,51418977621648,68147383440976,88004658349104,111018824773892,
    137083962602256,165947583396476,197206564506886,230311124532020,264579728664556,
    299222872246970,333373793532872,366127548002690,396581386731588,423877557093152,
    447244244786554,466031381623554,479739326608282,488040708803638,490790598253900,
    488027077303378,479964219386016,466973633150758,449560859140804,428336553813988,
    403984262538608,377227168140180,348797393359362,319405955808764,289718246690444,
    260335111987288,231777051036434,204476227690380,178772871343214,154915834881438,
    133067246032186,113311283968252,95662848430358,80079465095740,66473314402604,54721436476920,
    44677306126306,36180228392384,29063160583966,23159499467932,18309107124760,14360865713132,
    11176213617296,8630697453428,6613741892452,5029381932790,3795594510230,2842756200772,
    2113020420748,1558809220026,1141416734860,829278431512,597975663754,427829683174,
    303412628378,213366459878,148730208232,102485524082,69701857490,46748938672,30731495752,
    19517240962,12112853204,7029380378,3599196142,1586457824,495323388]]
private def rkmC_w64_m32_s4_13 : List ℤ := pzigCat
  [
   [230302011,887334439,1865664701,3042008619,3632496709,3320147529,895582919,4591788758,
    13460292770,25588636564,39099153370,49739538134,51025881248,33611365308,14554527007,
    104776473959,246053637593,439619738565,671944949159,907511298265,1079661868409,1080865315061,
    755119550707,108220282348,1777758859224,4576254268320,8873683054784,15072131370376,
    23584235884320,34807145386146,49091837500146,66709286668928,87819034633726,112440508888774,
    140429840646172,171467346503084,205054777168354,240523915246008,277059565542466,
    313730854849560,349533300888136,383437048113828,414437770311194,441606685467434,
    464137263100554,481384069992750,492891294552402,498411093259316,497908753765900,
    491555371021084,479711831120936,462901244302042,441776060255562,417080876624822,
    389613811805990,360188208467624,329598668724770,298591534384862,267840084023824,
    237928092523788,209339481036290,182452638746100,157542802764036,134787523551898,
    114275774442630,96019338502972,79966835668590,66016394913804,54028568485848,43839561762382,
    35271109508688,28139443792574,22263453870542,17469748688910,13596319623292,10496096004690,
    8037723770504,6106190081818,4601937068922,3441021505350,2552908505346,1879018795098,
    1372209637206,994375448608,714769024600,509536412198,360292999948,252542368608,175262916580,
    120272528992,81730663290,54585564186,35729769430,22947176896,14187508630,8199732892,
    4356968250,2029775596,642429438]]
private theorem rkmWC_w64_m32_s4_0 : bWinChk 206 18 100000000 1024 rkmPhb_w64_m32_s4
    222 rkmXsWin_w64_m32_s4_in 249 rkmC_w64_m32_s4_1 3696846915 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_1 : bWinChk 206 17 100000000 1024 rkmPhb_w64_m32_s4
    249 rkmC_w64_m32_s4_1 275 rkmC_w64_m32_s4_2 3428955469 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_2 : bWinChk 206 17 100000000 1024 rkmPhb_w64_m32_s4
    275 rkmC_w64_m32_s4_2 302 rkmC_w64_m32_s4_3 3554551885 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_3 : bWinChk 206 18 100000000 1024 rkmPhb_w64_m32_s4
    302 rkmC_w64_m32_s4_3 330 rkmC_w64_m32_s4_4 3385299138 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_4 : bWinChk 206 18 100000000 1024 rkmPhb_w64_m32_s4
    330 rkmC_w64_m32_s4_4 360 rkmC_w64_m32_s4_5 3486827407 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_5 : bWinChk 206 18 100000000 1024 rkmPhb_w64_m32_s4
    360 rkmC_w64_m32_s4_5 386 rkmC_w64_m32_s4_6 3941212052 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_6 : bWinChk 206 18 100000000 1024 rkmPhb_w64_m32_s4
    386 rkmC_w64_m32_s4_6 412 rkmC_w64_m32_s4_7 3325996821 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_7 : bWinChk 206 18 100000000 1024 rkmPhb_w64_m32_s4
    412 rkmC_w64_m32_s4_7 437 rkmC_w64_m32_s4_8 3506367989 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_8 : bWinChk 206 18 100000000 1024 rkmPhb_w64_m32_s4
    437 rkmC_w64_m32_s4_8 462 rkmC_w64_m32_s4_9 3727939775 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_9 : bWinChk 206 19 100000000 1024 rkmPhb_w64_m32_s4
    462 rkmC_w64_m32_s4_9 489 rkmC_w64_m32_s4_10 3489733564 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_10 : bWinChk 206 19 100000000 1024 rkmPhb_w64_m32_s4
    489 rkmC_w64_m32_s4_10 516 rkmC_w64_m32_s4_11 3720059972 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_11 : bWinChk 206 19 100000000 1024 rkmPhb_w64_m32_s4
    516 rkmC_w64_m32_s4_11 537 rkmC_w64_m32_s4_12 3442262878 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_12 : bWinChk 206 19 100000000 1024 rkmPhb_w64_m32_s4
    537 rkmC_w64_m32_s4_12 561 rkmC_w64_m32_s4_13 3451920333 = true := by decide +kernel
private theorem rkmWC_w64_m32_s4_13 : bWinChk 206 18 100000000 1024 rkmPhb_w64_m32_s4
    561 rkmC_w64_m32_s4_13 581 rkmXsWin_w64_m32_s4_out 3450480008 = true := by decide +kernel
private theorem rkmWinIter_w64_m32_s4 :
    RkmWinIterSound 254 1024 rkmHbWin_w64_m32_s4 222 rkmXsWin_w64_m32_s4_in
      581 rkmXsWin_w64_m32_s4_out 49608454206 :=
  rkmChS 254 49608454206 (rkmChS 236 46157974198 (rkmChS 217 42706053865 (rkmChS 198
    39263790987 (rkmChS 179 35543731015 (rkmChS 160 32053997451 (rkmChS 142 28326057676 (rkmChS
    124 24819689687 (rkmChS 106 21493692866 (rkmChS 88 17552480814 (rkmChS 70 14065653407
    (rkmChS 52 10680354269 (rkmChS 35 7125802384 (bWinChk_sound rkmHhb_w64_m32_s4
    rkmWC_w64_m32_s4_0) rkmHhb_w64_m32_s4 rkmWC_w64_m32_s4_1 rfl rfl) rkmHhb_w64_m32_s4
    rkmWC_w64_m32_s4_2 rfl rfl) rkmHhb_w64_m32_s4 rkmWC_w64_m32_s4_3 rfl rfl) rkmHhb_w64_m32_s4
    rkmWC_w64_m32_s4_4 rfl rfl) rkmHhb_w64_m32_s4 rkmWC_w64_m32_s4_5 rfl rfl) rkmHhb_w64_m32_s4
    rkmWC_w64_m32_s4_6 rfl rfl) rkmHhb_w64_m32_s4 rkmWC_w64_m32_s4_7 rfl rfl) rkmHhb_w64_m32_s4
    rkmWC_w64_m32_s4_8 rfl rfl) rkmHhb_w64_m32_s4 rkmWC_w64_m32_s4_9 rfl rfl) rkmHhb_w64_m32_s4
    rkmWC_w64_m32_s4_10 rfl rfl) rkmHhb_w64_m32_s4 rkmWC_w64_m32_s4_11 rfl rfl)
    rkmHhb_w64_m32_s4 rkmWC_w64_m32_s4_12 rfl rfl) rkmHhb_w64_m32_s4 rkmWC_w64_m32_s4_13 rfl
    rfl
/-- Certified `w64_m32` seg `4` (`254` steps). -/
theorem rkmWinSegWalkSnd_w64_m32_s4 :
    RkmWinSegWalkSound 254 ⟨1024, rkmHbWin_w64_m32_s4, 222, rkmXsWin_w64_m32_s4_in,
      581, rkmXsWin_w64_m32_s4_out, 49608454206⟩ :=
  @rkmSegWalk_mk 254 1024 222 581 49608454206
    rkmHbWin_w64_m32_s4 rkmXsWin_w64_m32_s4_in rkmXsWin_w64_m32_s4_out
    (rkmw_buildHbFrom_length 1024 1024 29638027559 1024 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl
      (bAllT_tl rkmStatOk_hiw64t07))))))))))
    rkmWinIter_w64_m32_s4
/-- Cumulative `w64_m32` part `0` lane witness. -/
theorem rkmHiLane_w64_m32_wint0 :
    @rkmWinSegWalkSnd_w64_m32_s4 = @rkmWinSegWalkSnd_w64_m32_s4 :=
  rfl
/-- Module lane witness for `FindAllJohnsonRampKickMuxHiW64T07`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T07 :
    @rkmHiLane_w64_m32_wint0 = @rkmHiLane_w64_m32_wint0 :=
  rfl

end
end QuantumComputation.Specs.DickeSol
