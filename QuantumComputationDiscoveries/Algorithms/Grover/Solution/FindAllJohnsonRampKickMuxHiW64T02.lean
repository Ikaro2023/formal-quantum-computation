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
# Caustic `r = 1024` Halo-16 Walk `w_hi64_m4_r1024` (`FindAllJohnsonRampKickMuxHiW64T02`)

Certifies part `0` of `w_hi64_m4_r1024` (`r = 1024`, halo-16).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Generator list for `w64_m4_s0`. -/
def rkmHbWin_w64_m4_s0 : List ℤ :=
  altBuildHbFrom 16 1024 1346287500000 0 16
/-- Entry `rkmXsWin_w64_m4_s0_in`. -/
def rkmXsWin_w64_m4_s0_in : List ℤ := [rkmP 1000000000000000]
/-- Exit `rkmXsWin_w64_m4_s0_out`. -/
def rkmXsWin_w64_m4_s0_out : List ℤ := let p := rkmP; [p 787596412876264, p 548409404252983,
  p 261311252010012, p 98166948708766, p 30760384648719, p 8278715281850, p 1946391336900,
  p 403739400788, p 74297391189, p 12128968917, p 1744854522, p 218482610]
/-- Generator list for `w64_m4_s1`. -/
def rkmHbWin_w64_m4_s1 : List ℤ :=
  altBuildHbFrom 32 1024 632130833333 0 32
/-- Entry `rkmXsWin_w64_m4_s1_in`. -/
def rkmXsWin_w64_m4_s1_in : List ℤ := let p := rkmP; [p 787596412876264, p 548409404252983,
  p 261311252010012, p 98166948708766, p 30760384648719, p 8278715281850, p 1946391336900,
  p 403739400788, p 74297391189, p 12128968917, p 1744854522, p 218482610]
/-- Exit `rkmXsWin_w64_m4_s1_out`. -/
def rkmXsWin_w64_m4_s1_out : List ℤ := let p := rkmP; [p 111833774110366, p 243612364356824,
  p 368372296314384, p 446228854405964, p 459012287222218, p 413828529719788, p 333511035860435,
  p 243494665786208, p 162588569507634, p 99990711964656, p 56936850541437, p 30139661216051,
  p 14877186238256, p 6863360631829, p 2964155346142, p 1199788288764, p 455408402268,
  p 162142694870, p 54111005205, p 16885375174, p 4953023785, p 1248025827, p 251783744]
/-- Generator list for `w64_m4_s2`. -/
def rkmHbWin_w64_m4_s2 : List ℤ :=
  altBuildHbFrom 64 1024 343696000000 0 64
/-- Entry `rkmXsWin_w64_m4_s2_in`. -/
def rkmXsWin_w64_m4_s2_in : List ℤ := let p := rkmP; [p 111833774110366, p 243612364356824,
  p 368372296314384, p 446228854405964, p 459012287222218, p 413828529719788, p 333511035860435,
  p 243494665786208, p 162588569507634, p 99990711964656, p 56936850541437, p 30139661216051,
  p 14877186238256, p 6863360631829, p 2964155346142, p 1199788288764, p 455408402268,
  p 162142694870, p 54111005205, p 16885375174, p 4953023785, p 1248025827, p 251783744]
/-- Exit `rkmXsWin_w64_m4_s2_out`. -/
def rkmXsWin_w64_m4_s2_out : List ℤ := let p := rkmP; [p 4708056691, p 26839580480, p 106229099920,
  p 339639851102, p 929586356475, p 2248866791696, p 4907561789755, p 9794934307726,
  p 18062759528568, p 31013058992459, p 49876499215653, p 75497537691318, p 107985666476570,
  p 146424963290219, p 188743209943223, p 231817196089743, p 271832353581005, p 304846070086134,
  p 327435239014363, p 337280765388254, p 333550684775007, p 316997188420546, p 289758516322440,
  p 254928760012224, p 216010320093023, p 176373833536993, p 138833154906499, p 105393517425451,
  p 77184040593715, p 54542635032479, p 37197541918259, p 24485627295557, p 15557756942356,
  p 9541640924476, p 5648208178711, p 3226650696617, p 1778615969565, p 945717230754,
  p 484983936976, p 239716082639, p 114138267371, p 52346755891, p 23021996924, p 9734567238,
  p 3832122354, p 1353191900, p 380496287]
/-- Generator list for `w64_m4_s3`. -/
def rkmHbWin_w64_m4_s3 : List ℤ :=
  altBuildHbFrom 128 1024 181682400000 0 128
/-- Entry `rkmXsWin_w64_m4_s3_in`. -/
def rkmXsWin_w64_m4_s3_in : List ℤ := let p := rkmP; [p 4708056691, p 26839580480, p 106229099920,
  p 339639851102, p 929586356475, p 2248866791696, p 4907561789755, p 9794934307726,
  p 18062759528568, p 31013058992459, p 49876499215653, p 75497537691318, p 107985666476570,
  p 146424963290219, p 188743209943223, p 231817196089743, p 271832353581005, p 304846070086134,
  p 327435239014363, p 337280765388254, p 333550684775007, p 316997188420546, p 289758516322440,
  p 254928760012224, p 216010320093023, p 176373833536993, p 138833154906499, p 105393517425451,
  p 77184040593715, p 54542635032479, p 37197541918259, p 24485627295557, p 15557756942356,
  p 9541640924476, p 5648208178711, p 3226650696617, p 1778615969565, p 945717230754,
  p 484983936976, p 239716082639, p 114138267371, p 52346755891, p 23021996924, p 9734567238,
  p 3832122354, p 1353191900, p 380496287]
/-- Exit `rkmXsWin_w64_m4_s3_out`. -/
def rkmXsWin_w64_m4_s3_out : List ℤ := let p := rkmP; [p 344109653, p 734271060, p 1791782470,
  p 4012920876, p 8693135314, p 18281884437, p 37117463049, p 73279248796, p 140227287103,
  p 260494307291, p 469876357074, p 823820511079, p 1404447375819, p 2329109703075,
    p 3759255063963,
  p 5907488088046, p 9042124253440, p 13485174549321, p 19602199723062, p 27781003412906,
  p 38398040933544, p 51773239086268, p 68114817928528, p 87462016179287, p 109630517340622,
  p 134172573795271, p 160360292256066, p 187199720394658, p 213480437748874, p 237858926538311,
  p 258969581771336, p 275550045254961, p 286566236451382, p 291318738472999, p 289516102481306,
  p 281304414807571, p 267247831923194, p 248265799800807, p 225534169175768, p 200366326550272,
  p 174090637067390, p 147938726506454, p 122958787424181, p 99958505135839, p 79482480135825,
  p 61818796733564, p 47029488335061, p 34996184292363, p 25472327372866, p 18134625745530,
  p 12627867778060, p 8600562407762, p 5729002481739, p 3732230563948, p 2377868458765,
  p 1481474616065, p 902572397867, p 537582449857, p 313035388124, p 178200773258, p 99094128534,
  p 53854389979, p 28490553424, p 14680015536, p 7304629578, p 3432704364, p 1512685253,
  p 514630035, p 129089024]
/-- Generator list for `w64_m4_s4`. -/
def rkmHbWin_w64_m4_s4 : List ℤ :=
  altBuildHbFrom 256 1024 95881890909 0 256
/-- Entry `rkmXsWin_w64_m4_s4_in`. -/
def rkmXsWin_w64_m4_s4_in : List ℤ := let p := rkmP; [p 344109653, p 734271060, p 1791782470,
  p 4012920876, p 8693135314, p 18281884437, p 37117463049, p 73279248796, p 140227287103,
  p 260494307291, p 469876357074, p 823820511079, p 1404447375819, p 2329109703075,
    p 3759255063963,
  p 5907488088046, p 9042124253440, p 13485174549321, p 19602199723062, p 27781003412906,
  p 38398040933544, p 51773239086268, p 68114817928528, p 87462016179287, p 109630517340622,
  p 134172573795271, p 160360292256066, p 187199720394658, p 213480437748874, p 237858926538311,
  p 258969581771336, p 275550045254961, p 286566236451382, p 291318738472999, p 289516102481306,
  p 281304414807571, p 267247831923194, p 248265799800807, p 225534169175768, p 200366326550272,
  p 174090637067390, p 147938726506454, p 122958787424181, p 99958505135839, p 79482480135825,
  p 61818796733564, p 47029488335061, p 34996184292363, p 25472327372866, p 18134625745530,
  p 12627867778060, p 8600562407762, p 5729002481739, p 3732230563948, p 2377868458765,
  p 1481474616065, p 902572397867, p 537582449857, p 313035388124, p 178200773258, p 99094128534,
  p 53854389979, p 28490553424, p 14680015536, p 7304629578, p 3432704364, p 1512685253,
  p 514630035, p 129089024]
/-- Exit `rkmXsWin_w64_m4_s4_out`. -/
def rkmXsWin_w64_m4_s4_out : List ℤ := let p := rkmP; [p 214213934, p 523752638, p 1157464366,
  p 2424612786, p 4872169866, p 9345460890, p 17712187045, p 32686555754, p 58914172005,
  p 103794906402, p 178593377279, p 300777141307, p 495482457137, p 798964518012, p 1261577150931,
  p 1951128447329, p 2956881577326, p 4391997372474, p 6396099948309, p 9134915228647,
  p 12798176282079, p 17593870555849, p 23737856018166, p 31440784894129, p 40889309975533,
  p 52225641156965, p 65524254662559, p 80769661519793, p 97836953823945, p 116477643181669,
  p 136314250803856, p 156844575348408, p 177457847717009, p 197461953754737, p 216121075619550,
  p 232700043049865, p 246512637644041, p 256969191271978, p 263618116980948, p 266178830181929,
  p 264560589155138, p 258867492864846, p 249388545035811, p 236573357232940, p 220997790196002,
  p 203321399747595, p 184242723108086, p 164455011970061, p 144606886943374, p 125271088446721,
  p 106921538837000, p 89921559393020, p 74520688154387, p 60860170140844, p 48984792039732,
  p 38858490842095, p 30383196168197, p 23416773083050, p 17790582879976, p 13324341715367,
  p 9838057019557, p 7161528783194, p 5139814226788, p 3637120781369, p 2537770411041,
  p 1745934782644, p 1184466996304, p 792325364110, p 522678727824, p 340006158267, p 218065764797,
  p 137914810047, p 85902635229, p 52720855187, p 31792141035, p 18792242741, p 10857141515,
  p 6026925042, p 3187265552, p 1599970713, p 590221224, p 155412531]
/-- Generator list for `w64_m4_s5`. -/
def rkmHbWin_w64_m4_s5 : List ℤ :=
  altBuildHbFrom 512 1024 51685843478 0 512
/-- Entry `rkmXsWin_w64_m4_s5_in`. -/
def rkmXsWin_w64_m4_s5_in : List ℤ := let p := rkmP; [p 214213934, p 523752638, p 1157464366,
  p 2424612786, p 4872169866, p 9345460890, p 17712187045, p 32686555754, p 58914172005,
  p 103794906402, p 178593377279, p 300777141307, p 495482457137, p 798964518012, p 1261577150931,
  p 1951128447329, p 2956881577326, p 4391997372474, p 6396099948309, p 9134915228647,
  p 12798176282079, p 17593870555849, p 23737856018166, p 31440784894129, p 40889309975533,
  p 52225641156965, p 65524254662559, p 80769661519793, p 97836953823945, p 116477643181669,
  p 136314250803856, p 156844575348408, p 177457847717009, p 197461953754737, p 216121075619550,
  p 232700043049865, p 246512637644041, p 256969191271978, p 263618116980948, p 266178830181929,
  p 264560589155138, p 258867492864846, p 249388545035811, p 236573357232940, p 220997790196002,
  p 203321399747595, p 184242723108086, p 164455011970061, p 144606886943374, p 125271088446721,
  p 106921538837000, p 89921559393020, p 74520688154387, p 60860170140844, p 48984792039732,
  p 38858490842095, p 30383196168197, p 23416773083050, p 17790582879976, p 13324341715367,
  p 9838057019557, p 7161528783194, p 5139814226788, p 3637120781369, p 2537770411041,
  p 1745934782644, p 1184466996304, p 792325364110, p 522678727824, p 340006158267, p 218065764797,
  p 137914810047, p 85902635229, p 52720855187, p 31792141035, p 18792242741, p 10857141515,
  p 6026925042, p 3187265552, p 1599970713, p 590221224, p 155412531]
/-- Exit `rkmXsWin_w64_m4_s5_out`. -/
def rkmXsWin_w64_m4_s5_out : List ℤ := let p := rkmP; let n := rkmN; [n 372317977, n 711476003,
  n 1027204549, n 966013159, n 177492375, p 1667850260, p 4844141779, p 9236110970, p 13974084075,
  p 17113061864, p 15105168156, p 3240902690, n 24325087341, n 73120637249, n 145990483280,
  n 239852914101, n 340243360276, n 416115944840, n 412746561310, n 245233849303, p 206718075829,
  p 1102837145161, p 2641560849011, p 5056134052122, p 8604930715462, p 13556325977151,
  p 20169354174143, p 28669814186956, p 39225294897937, p 51919923438629, p 66732867809599,
  p 83522214476921, p 102017018844097, p 121819223032560, p 142415631563439, p 163199975427293,
  p 183504280152211, p 202635599543777, p 219917015308515, p 234727922955865, p 246540908733889,
  p 254952692551703, p 259705093956944, p 260697045055530, p 257984556958457, p 251770796734067,
  p 242387663127213, p 230269933740538, p 215925264501265, p 199902721310635, p 182761213879906,
  p 165041834704763, p 147243631910372, p 129805618255148, p 113094744610708, p 97399082077830,
  p 82927722294840, p 69813734965154, p 58121643086036, p 47857323535385, p 38978636582849,
  p 31406778152451, p 25037326242148, p 19749878707587, p 15417028292743, p 11910626036368,
  p 9107639133477, p 6893790768814, p 5165504677652, p 3831906749048, p 2814459975243,
  p 2046825697585, p 1474020697735, p 1051183997555, p 742401464549, p 519281025083,
    p 359618203320,
  p 246690405395, p 167494424921, p 112515772445, p 74817038322, p 49151071894, p 31853436572,
  p 20376020741, p 12681020040, p 7731439524, p 4516055565, p 2416387470, p 1161850459,
    p 405306913,
  p 101219113]
/-- Generator list for `w64_m4_s6`. -/
def rkmHbWin_w64_m4_s6 : List ℤ :=
  altBuildHbFrom 1024 1024 29643724279 0 1024
/-- Entry `rkmXsWin_w64_m4_s6_in`. -/
def rkmXsWin_w64_m4_s6_in : List ℤ := let p := rkmP; let n := rkmN; [n 372317977, n 711476003,
  n 1027204549, n 966013159, n 177492375, p 1667850260, p 4844141779, p 9236110970, p 13974084075,
  p 17113061864, p 15105168156, p 3240902690, n 24325087341, n 73120637249, n 145990483280,
  n 239852914101, n 340243360276, n 416115944840, n 412746561310, n 245233849303, p 206718075829,
  p 1102837145161, p 2641560849011, p 5056134052122, p 8604930715462, p 13556325977151,
  p 20169354174143, p 28669814186956, p 39225294897937, p 51919923438629, p 66732867809599,
  p 83522214476921, p 102017018844097, p 121819223032560, p 142415631563439, p 163199975427293,
  p 183504280152211, p 202635599543777, p 219917015308515, p 234727922955865, p 246540908733889,
  p 254952692551703, p 259705093956944, p 260697045055530, p 257984556958457, p 251770796734067,
  p 242387663127213, p 230269933740538, p 215925264501265, p 199902721310635, p 182761213879906,
  p 165041834704763, p 147243631910372, p 129805618255148, p 113094744610708, p 97399082077830,
  p 82927722294840, p 69813734965154, p 58121643086036, p 47857323535385, p 38978636582849,
  p 31406778152451, p 25037326242148, p 19749878707587, p 15417028292743, p 11910626036368,
  p 9107639133477, p 6893790768814, p 5165504677652, p 3831906749048, p 2814459975243,
  p 2046825697585, p 1474020697735, p 1051183997555, p 742401464549, p 519281025083,
    p 359618203320,
  p 246690405395, p 167494424921, p 112515772445, p 74817038322, p 49151071894, p 31853436572,
  p 20376020741, p 12681020040, p 7731439524, p 4516055565, p 2416387470, p 1161850459,
    p 405306913,
  p 101219113]
/-- Exit `rkmXsWin_w64_m4_s6_out`. -/
def rkmXsWin_w64_m4_s6_out : List ℤ := let p := rkmP; let n := rkmN; [n 118843095, n 283042565,
  n 443324957, n 280137153, p 179865343, p 760355549, p 1267635337, p 1401513124, p 724387823,
  n 582026915, n 2234464829, n 3518069358, n 3509849776, n 1824854957, p 1505984839, p 5631546931,
  p 8902733743, p 9442027591, p 5952851569, n 1881536888, n 12190940423, n 21574059281,
  n 25741420962, n 20552171088, n 4399284996, p 20346663604, p 47307130333, p 66575615332,
  p 67363407615, p 42129951081, n 9808834657, n 79712848529, n 148729525194, n 191900843915,
  n 183936488900, n 107854609388, p 36411415140, p 226888577259, p 419012042088, p 551954909805,
  p 562165025317, p 401082559612, p 53530821385, n 447731166583, n 1016097850732, n 1518645403726,
  n 1795991290401, n 1694919312326, n 1107315223609, n 7768523346, p 1517717062457,
    p 3260614357612,
  p 4901969080616, p 6048823779041, p 6292343172365, p 5280678436560, p 2795671272265,
  n 1180106820553, n 6415637005833, n 12415154573730, n 18437436943382, n 23550435053252,
  n 26716999412998, n 26901499718323, n 23183809324289, n 14866758726447, n 1564529168332,
  p 16740300783069, p 39676809737975, p 66503995975873, p 96165427697565, p 127373506994967,
  p 158711243578060, p 188742997806155, p 216121000536186, p 239677898102442, p 258498228894576,
  p 271964082182288, p 279773350834728, p 281931633361858, p 278722643424598, p 270661482504257,
  p 258436872242614, p 242849605153953, p 224752215912432, p 204993292483367, p 184372193956162,
  p 163603928811891, p 143295658573874, p 123934192621584, p 105883643010496, p 89390818672972,
  p 74596036190000, p 61548717591809, p 50224587773909, p 40542538889339, p 32381511470151,
  p 25595597275112, p 20026234879876, p 15512184933164, p 11897653130335, p 9037138934704,
  p 6799037354205, p 5067104639407, p 3741351068784, p 2737257522708, p 1984426119304,
  p 1425690993714, p 1015235008124, p 716533203694, p 501149008511, p 347390178483, p 238670101783,
  p 162407145527, p 109390875391, p 72894806495, p 48081648414, p 31170144389, p 19825069753,
  p 12365631815, p 7406190681, p 4133133267, p 2110023486, p 939752870, p 285465947]
/-- Generator list for `w64_m4_s7a`. -/
def rkmHbWin_w64_m4_p7a : List ℤ :=
  altBuildHbFrom 1792 1024 20052279735 0 1024
/-- Entry `rkmXsWin_w64_m4_s7a_in`. -/
def rkmXsWin_w64_m4_s7a_in : List ℤ := let p := rkmP; let n := rkmN; [n 118843095, n 283042565,
  n 443324957, n 280137153, p 179865343, p 760355549, p 1267635337, p 1401513124, p 724387823,
  n 582026915, n 2234464829, n 3518069358, n 3509849776, n 1824854957, p 1505984839, p 5631546931,
  p 8902733743, p 9442027591, p 5952851569, n 1881536888, n 12190940423, n 21574059281,
  n 25741420962, n 20552171088, n 4399284996, p 20346663604, p 47307130333, p 66575615332,
  p 67363407615, p 42129951081, n 9808834657, n 79712848529, n 148729525194, n 191900843915,
  n 183936488900, n 107854609388, p 36411415140, p 226888577259, p 419012042088, p 551954909805,
  p 562165025317, p 401082559612, p 53530821385, n 447731166583, n 1016097850732, n 1518645403726,
  n 1795991290401, n 1694919312326, n 1107315223609, n 7768523346, p 1517717062457,
    p 3260614357612,
  p 4901969080616, p 6048823779041, p 6292343172365, p 5280678436560, p 2795671272265,
  n 1180106820553, n 6415637005833, n 12415154573730, n 18437436943382, n 23550435053252,
  n 26716999412998, n 26901499718323, n 23183809324289, n 14866758726447, n 1564529168332,
  p 16740300783069, p 39676809737975, p 66503995975873, p 96165427697565, p 127373506994967,
  p 158711243578060, p 188742997806155, p 216121000536186, p 239677898102442, p 258498228894576,
  p 271964082182288, p 279773350834728, p 281931633361858, p 278722643424598, p 270661482504257,
  p 258436872242614, p 242849605153953, p 224752215912432, p 204993292483367, p 184372193956162,
  p 163603928811891, p 143295658573874, p 123934192621584, p 105883643010496, p 89390818672972,
  p 74596036190000, p 61548717591809, p 50224587773909, p 40542538889339, p 32381511470151,
  p 25595597275112, p 20026234879876, p 15512184933164, p 11897653130335, p 9037138934704,
  p 6799037354205, p 5067104639407, p 3741351068784, p 2737257522708, p 1984426119304,
  p 1425690993714, p 1015235008124, p 716533203694, p 501149008511, p 347390178483, p 238670101783,
  p 162407145527, p 109390875391, p 72894806495, p 48081648414, p 31170144389, p 19825069753,
  p 12365631815, p 7406190681, p 4133133267, p 2110023486, p 939752870, p 285465947]
/-- Exit `rkmXsWin_w64_m4_s7a_out`. -/
def rkmXsWin_w64_m4_s7a_out : List ℤ := let p := rkmP; let n := rkmN; [n 167277570, n 230254592,
  n 102566885, p 279215920, p 743907752, p 983542884, p 679475897, n 200226670, n 1229311860,
  n 1999013307, n 1843530831, n 429918551, p 1766972834, p 3820399996, p 4623289980, p 3173609155,
  n 552110654, n 5299395643, n 8974446595, n 9090262147, n 4604328256, p 3869033205, p 13415473367,
  p 19423454864, p 17788771005, p 6762221569, n 11436621438, n 30351345123, n 41211885417,
  n 36413935690, n 12868367025, p 24523845861, p 63422412564, p 87061283769, p 80031748485,
  p 35695522807, n 38746854586, n 121461182404, n 180664355470, n 184686212478, n 115028814311,
  p 23543115801, p 197874429284, p 351763340268, p 420950603585, p 354190113669, p 135184677103,
  n 202657017631, n 575381622286, n 864346805924, n 946788707867, n 735556856801, n 214764183560,
  p 537819458326, p 1352388089244, p 1996942652220, p 2230631241831, p 1870228438651,
  p 854343051472, n 713414403898, n 2556984941768, n 4261522678754, n 5349110226749,
  n 5381939690599, n 4073022501386, n 1381068620412, p 2433860749611, p 6810829368424,
  p 10949535226861, p 13927627502847, p 14857133362357, p 13051913378718, p 8179737815164,
  p 370097447408, n 9742774426537, n 21050718647667, n 32074035052227, n 41122970322897,
  n 46494193855174, n 46674915680423, n 40528211572297, n 27433036091394, n 7364171841129,
  p 19096119652644, p 50813405206250, p 86212765960647, p 123429346490444, p 160479635577382,
  p 195432140824465, p 226559100042048, p 252457041605670, p 272126308113443, p 285006631607613,
  p 290972593326701, p 290293072607933, p 283565006483523, p 271630919975411, p 255490524094225,
  p 236214212380101, p 214866530336554, p 192443653470183, p 169826636739040, p 147752352035129,
  p 126799935192527, p 107389898699896, p 89794717138646, p 74156032065697, p 60506318525990,
  p 48792027135173, p 38897065779074, p 30663388252895, p 23909011215479, p 18443366784728,
  p 14078226748193, p 10635642566229, p 7953665329704, p 5888895068844, p 4317484618004,
  p 3134775401777, p 2254435602458, p 1606011402505, p 1133277245996, p 792267824316,
  p 548713394443, p 376410049127, p 255766827956, p 172116715309, p 114595210106, p 75429914056,
  p 49059601107, p 31485850180, p 19735493245, p 12128761249, p 7245364887, p 4048856915,
  p 2056589676, p 917041049, p 284541302]

end

public section

private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: pCat xs ys
private abbrev fN {α} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uCN (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 => xs
  | v + 1 =>
    match xs with
    | [] => [v]
    | h :: t => v :: h :: t
private theorem uCNe (x : ℕ) (xs : List ℕ) : uCN x xs = x :: xs := by
  unfold uCN; rw [n1a]; cases xs <;> rfl
private def uON : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uON ns
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
private theorem bCZe (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by cases x <;> cases xs <;> rfl
private theorem bONF (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  simp [primOfNatForced, Nat.one_add]
private theorem bNSF (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  simp [primNegSuccForced, Nat.one_add]
private theorem bSE (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat; rw [bONF, Nat.sub_eq]; cases h : z - u with
  | zero => dsimp only; rw [Nat.sub_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bCZ (rkmForcedSubNatNat u z) (bDec z us)
private theorem bDN (z : ℕ) : bDec z [] = [] := rfl
private theorem bDC (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by rw [bDec, bCZe, bSE]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bMul0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZ0]; rfl
private def bE1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k =>
    match Nat.sub z (Nat.add k 1) with
    | 0 => none
    | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs =>
    match bE1 z x with
    | none => none
    | some u =>
      match bEnc z xs with
      | none => none
      | some us => some (uCN u us)
private theorem bE1S (z : ℕ) (x : ℤ) (u : ℕ) (h : bE1 z x = some u) : ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bE1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bE1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w => intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem bES (z : ℕ) : ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us → bDec z us = xs
  | [], us, h => by injection h with h'; subst h'; rfl
  | x :: xs, us, h => by
    dsimp only [bEnc] at h; revert h; cases hx : bE1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bEnc z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uCNe, bDC, bE1S z x u hx, bES z xs ws hxs]
private def zTd (x : ℤ) (d : ℕ) : ℤ :=
  match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNg : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTD : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTd x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by dsimp only [muxRawIntTdivNat, zTd]; rw [bNg, ndiv, Nat.add_eq]
private theorem bSND (m n d : ℕ) : rkmUltraSubNatTdiv m n d = zTd ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    dsimp only; have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTd]; rw [bNg]
private theorem bSTD (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTd (a - b) d := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => exact bSND m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
      rw [hm]; rfl
  | negSucc m => cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTd]
      rw [bNg, ndiv, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [bSND, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTd t d) (by simp only [Int.negSucc_eq]; omega)
private theorem bME : ∀ (a b : ℤ), muxRawIntMul a b = a * b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [bNg, Nat.mul_eq, Nat.add_eq]
    rw [Int.ofNat_eq_natCast, Int.negSucc_eq]; push_cast; ring
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [bNg, Nat.mul_eq, Nat.add_eq]
    rw [Int.negSucc_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq, Nat.add_eq, Nat.add_eq, Int.ofNat_eq_natCast]
    simp only [Int.negSucc_eq]; push_cast; ring
private theorem bFA : ∀ (a b : ℤ), rkmForcedIntAdd a b = a + b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bONF, Nat.add_eq]; simp only [Int.ofNat_eq_natCast]; omega
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bSE, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bSE, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bNSF, Nat.add_eq, Nat.add_eq]; simp [Int.negSucc_eq]; omega
private theorem bAC (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bFA]; cases a + b <;> cases xs <;> rfl
private def bSV0 (v P Q d : ℕ) : ℕ :=
  match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bSV0E (z v P Q d : ℕ) (hv : 0 < bSV0 v P Q d) :
    ((bSV0 v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSND]; unfold bSV0 at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv; cases h : Q - P with
  | zero => intro _; dsimp only; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k => intro hv; dsimp only at hv ⊢; rw [bNg]; omega
private def bSVP (v d p1 q1 : ℕ) : ℕ :=
  match p1 with
  | 0 => 0
  | p + 1 =>
    match q1 with
    | 0 => 0
    | q + 1 => bSV0 v p q d
private theorem bSVP_eq (v P Q d : ℕ) :
    bSVP v d (Nat.add 1 P) (Nat.add 1 Q) = bSV0 v P Q d := by
  unfold bSVP; rw [n1a P, n1a Q]
private theorem bSVE (z v P Q d : ℕ)
    (hv : 0 < bSVP v d (Nat.add 1 P) (Nat.add 1 Q)) :
    ((bSVP v d (Nat.add 1 P) (Nat.add 1 Q) : ℤ) - (z : ℤ)) =
      ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  rw [bSVP_eq] at hv ⊢; exact bSV0E z v P Q d hv
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bSVP v d (Nat.add 1 (Nat.add (Nat.mul b0 c0) (Nat.mul b z)))
    (Nat.add 1 (Nat.add (Nat.mul b c1) (Nat.mul b0 z)))
private theorem bCH (z d b0 c0 b v c1 : ℕ) {r : List ℕ} {tZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bDec z r = tZ) :
    bDec z (uCN (bCV z d b0 c0 b v c1) r) = rkmUltraAddCons ((v : ℤ) - (z : ℤ))
      (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tZ := by
  rw [uCNe, bDC, ht, bAC, bSTD, bME, bME]; refine congrArg (· :: tZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCV at hv ⊢; rw [bSVE z v _ _ d hv, hpq]
private theorem bCN (z d b0 c0 v : ℕ) {r : List ℕ} {tZ : List ℤ}
    (hv : 0 < bSVP v d (Nat.add 1 (Nat.mul b0 c0)) (Nat.add 1 (Nat.mul b0 z)))
    (ht : bDec z r = tZ) :
    bDec z (uCN (bSVP v d (Nat.add 1 (Nat.mul b0 c0)) (Nat.add 1 (Nat.mul b0 z))) r) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tZ := by
  rw [uCNe, bDC, ht, bAC, bTD, bME]; refine congrArg (· :: tZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  rw [bSVE z v _ _ d hv, hpq]
private def bAP : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAP xs)
private theorem bAP_cons {x : ℕ} {xs : List ℕ} (h : bAP (x :: xs) = true) :
    0 < x ∧ bAP xs = true := by
  cases x with
  | zero => exact Bool.noConfusion h
  | succ k => exact ⟨Nat.succ_pos k, h⟩
private theorem bAPu {x : ℕ} {xs : List ℕ} (h : bAP (uCN x xs) = true) :
    0 < x ∧ bAP xs = true := by rw [uCNe] at h; exact bAP_cons h
private def bHO (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
private theorem bHOe (z : ℕ) : ∀ (cs : List ℕ),
    ((bHO z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHO; rw [bDN, bZ0]
  | c :: cs => by unfold bHO; rw [bDC]
private theorem bTNe (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | x :: xs => by unfold bTN; rw [bDC]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs =>
    match bns with
    | [] => uCN (bSVP (bHO z vs) d (Nat.add 1 (Nat.mul b0 c0)) (Nat.add 1 (Nat.mul b0 z)))
        (bSl z d rem 0 z [] (bTN vs) (bTN cs))
    | b :: bR =>
      match vs, cs with
      | v :: vT, c :: cT => uCN (bCV z d b0 c0 b v (bHO z cT)) (bSl z d rem b c bR vT cT)
      | v :: vT, [] => uCN (bCV z d b0 c0 b v z) (bSl z d rem b z bR vT [])
      | [], c :: cT => uCN (bCV z d b0 c0 b z (bHO z cT)) (bSl z d rem b c bR [] cT)
      | [], [] => uCN (bCV z d b0 c0 b z z) (bSl z d rem b z bR [] [])
private theorem bSlS (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAP (bSl z d rem b0 c0 bns vs cs) = true → bDec z (bSl z d rem b0 c0 bns vs cs) =
      rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uON bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSl, uON, rkmUltraSlideLoopAux] at h ⊢; have hp := bAPu h
      have hi := bSlS z d rem 0 z [] (bTN vs) (bTN cs) hp.2; rw [bMul0, uON, bTNe, bTNe] at hi
      have hc := bCN z d b0 c0 (bHO z vs) hp.1 hi; rw [bHOe z vs] at hc; exact hc
    | cons b bR => cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSl, uON] at h ⊢; rw [bDN]; dsimp only [rkmUltraSlideLoopAux]
          have hp := bAPu h; have hi := bSlS z d rem b z bR [] [] hp.2; rw [bZ0 z, bDN] at hi
          have hc := bCH z d b0 c0 b z z hp.1 hi; rw [bZ0 z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uON] at h ⊢; rw [bDN, bDC z c cT]; dsimp only [rkmUltraSlideLoopAux]
          have hp := bAPu h; have hi := bSlS z d rem b c bR [] cT hp.2; rw [bDN] at hi
          have hc := bCH z d b0 c0 b z (bHO z cT) hp.1 hi; rw [bHOe z cT, bZ0 z] at hc; exact hc
      | cons v vT => cases cs with
        | nil =>
          dsimp only [bSl, uON] at h ⊢; rw [bDC z v vT, bDN]; dsimp only [rkmUltraSlideLoopAux]
          have hp := bAPu h; have hi := bSlS z d rem b z bR vT [] hp.2; rw [bZ0 z, bDN] at hi
          have hc := bCH z d b0 c0 b v z hp.1 hi; rw [bZ0 z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uON] at h ⊢; rw [bDC z v vT, bDC z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAPu h
          have hi := bSlS z d rem b c bR vT cT hp.2
          have hc := bCH z d b0 c0 b v (bHO z cT) hp.1 hi; rw [bHOe z cT] at hc; exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uCN b (uCN (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _, _ => []
  | rem + 1, b0, bz0, c0, hbz, vs, cs =>
    match hbz with
    | [] =>
      uCN (bSVP (bHO z vs) d (Nat.add 1 (Nat.mul b0 c0)) (Nat.add 1 bz0))
        (bSlZ z d rem 0 0 z [] (bTN vs) (bTN cs))
    | [_] => []
    | b :: bz :: bR =>
      match vs, cs with
      | v :: vT, c :: cT =>
        uCN (bSVP v d (Nat.add 1 (Nat.add (Nat.mul b0 c0) bz))
          (Nat.add 1 (Nat.add (Nat.mul b (bHO z cT)) bz0)))
          (bSlZ z d rem b bz c bR vT cT)
      | v :: vT, [] =>
        uCN (bSVP v d (Nat.add 1 (Nat.add (Nat.mul b0 c0) bz)) (Nat.add 1 (Nat.add bz bz0)))
          (bSlZ z d rem b bz z bR vT [])
      | [], c :: cT =>
        uCN (bSVP z d (Nat.add 1 (Nat.add (Nat.mul b0 c0) bz))
          (Nat.add 1 (Nat.add (Nat.mul b (bHO z cT)) bz0)))
          (bSlZ z d rem b bz c bR [] cT)
      | [], [] =>
        uCN (bSVP z d (Nat.add 1 (Nat.add (Nat.mul b0 c0) bz)) (Nat.add 1 (Nat.add bz bz0)))
          (bSlZ z d rem b bz z bR [] [])
private theorem bSlZ_eq (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bSlZ z d rem b0 (Nat.mul b0 z) c0 (mkHbZ z bns) vs cs =
      bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTN vs) (bTN cs)
      have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
      dsimp only [mkHbZ] at hrec; rw [hz0] at hrec; dsimp only [mkHbZ, bSlZ, bSl]; rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ]; rw [uCNe, uCNe]; cases vs with
      | nil => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR vT cT]
private def bStg (z dg mL cL : ℕ) (hbz v c : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlZ z d nL 0 0 z hbz v c) fun out => cond (bAP out) (some out) none
private theorem bSS (z dg mL cL : ℕ) (b v c out : List ℕ)
    (h : bStg z dg mL cL (mkHbZ z b) v c = some out) :
    bDec z out = rkmUltraHornerStage dg mL cL (uON b) (bDec z v) (bDec z c) := by
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c
  have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
  rw [hz0] at hsl; unfold bStg at h; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq, hsl] at h; revert h
  cases hp : bAP (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]; exact bSlS z _ _ 0 z b v c hp
private def bBd (z g mL c : ℕ) (hbz v x : List ℕ) (k : ℕ → List ℕ → Option (List ℕ)) :
    Option (List ℕ) :=
  fN (rkmNextLen mL c) fun n =>
    match bStg z g mL c hbz v x with
    | none => none
    | some o => k n o
private theorem bBS {z g mL c : ℕ} {b v x out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBd z g mL c (mkHbZ z b) v x kB = some out)
    (hk : ∀ m0, kB (rkmNextLen mL c) m0 = some out →
      bDec z out = kU (rkmNextLen mL c) (bDec z m0)) :
    bDec z out = (HighDForce.withForcedNat (rkmNextLen mL c) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage g mL c (uON b) (bDec z v) (bDec z x)) (kU nL)) := by
  unfold bBd at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; revert h
  cases hs : bStg z g mL c (mkHbZ z b) v x with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bSS z g mL c b v x mid hs]
    exact hk mid h
private def bSp (z m c : ℕ) (hbz v : List ℕ) : Option (List ℕ) :=
  bBd z 16 m c hbz v v fun l x => bBd z 15 m l hbz v x fun l x =>
  bBd z 14 m l hbz v x fun l x => bBd z 13 m l hbz v x fun l x =>
  bBd z 12 m l hbz v x fun l x => bBd z 11 m l hbz v x fun l x =>
  bBd z 10 m l hbz v x fun l x => bBd z 9 m l hbz v x fun l x =>
  bBd z 8 m l hbz v x fun l x => bBd z 7 m l hbz v x fun l x =>
  bBd z 6 m l hbz v x fun l x => bBd z 5 m l hbz v x fun l x =>
  bBd z 4 m l hbz v x fun l x => bBd z 3 m l hbz v x fun l x =>
  bBd z 2 m l hbz v x fun l x => bStg z 1 m l hbz v x
private theorem bSpS (z mL cL : ℕ) (b v out : List ℕ)
    (h : bSp z mL cL (mkHbZ z b) v = some out) :
    bDec z out = rkmUltraHornerT16Step mL cL (uON b) (bDec z v) := by
  unfold bSp at h; unfold rkmUltraHornerT16Step
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  exact bSS z 1 mL _ b v _ out h
private def bIt (z : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, v => some v
  | k + 1, m, c, hbz, v =>
    match bSp z m c hbz v with
    | none => none
    | some vN => fN (rkmNextLen16 m c) fun nL => bIt z k m nL hbz vN
private theorem bItS (z : ℕ) : ∀ (k m c : ℕ) (b v out : List ℕ),
    bIt z k m c (mkHbZ z b) v = some out →
      bDec z out = muxUltraIterFullT16Rkm k m c (uON b) (bDec z v)
  | 0, _, _, _, _, _, h => by injection h with h'; subst h'; rfl
  | k + 1, m, c, b, v, out, h => by
    unfold bIt at h; revert h; cases hs : bSp z m c (mkHbZ z b) v with
    | none => intro h; dsimp only at h; cases h
    | some vN =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bSpS z m c b v vN hs]
      exact bItS z k m _ b vN out h
private def bDropN : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | _, [] => []
  | k + 1, _ :: xs => bDropN k xs
private theorem bDropN_uON : ∀ (s : ℕ) (b : List ℕ),
    uON (bDropN s b) = rkmDropInts s (uON b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, _ :: bs => bDropN_uON k bs
private def bDrop2 : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | k + 1, _ :: _ :: xs => bDrop2 k xs
  | _, _ => []
private theorem bDrop2_mkHbZ (z : ℕ) : ∀ (s : ℕ) (b : List ℕ),
    bDrop2 s (mkHbZ z b) = mkHbZ z (bDropN s b)
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: bs => by
    dsimp only [mkHbZ, bDropN]; rw [uCNe, uCNe]; dsimp only [bDrop2]; exact bDrop2_mkHbZ z k bs
private def bAbsZ (z u : ℕ) : ℕ := Nat.add (Nat.sub u z) (Nat.sub z u)
private theorem bAbsZ_eq (z u : ℕ) : bAbsZ z u = rkmIntAbsNat ((u : ℤ) - (z : ℤ)) := by
  unfold bAbsZ; simp only [Nat.add_eq, Nat.sub_eq]; cases h : z - u with
  | zero =>
    have hm : (u : ℤ) - (z : ℤ) = Int.ofNat (u - z) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; dsimp only [rkmIntAbsNat]; omega
  | succ k =>
    have hm : (u : ℤ) - (z : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [rkmIntAbsNat]; rw [Nat.add_eq]; omega
private def bPrepZ (z : ℕ) : ℕ → List ℕ → List ℕ
  | 0, us => us
  | k + 1, us => uCN z (bPrepZ z k us)
private theorem bPrepZ_eq (z : ℕ) : ∀ (k : ℕ) (us : List ℕ),
    bDec z (bPrepZ z k us) = rkmPrependZeros k (bDec z us)
  | 0, _ => rfl
  | k + 1, us => by
    dsimp only [bPrepZ, rkmPrependZeros]
    rw [uCNe, bDC, bZ0 z, rkmw_strictConsInt_eq, bPrepZ_eq z k us]
private def bNatLen : List ℕ → ℕ
  | [] => 0
  | _ :: us => Nat.add (bNatLen us) 1
private theorem bNatLen_eq (z : ℕ) : ∀ (us : List ℕ), bNatLen us = altIntLen (bDec z us)
  | [] => by rw [bDN, rkmw_altIntLen_eq]; rfl
  | u :: us => by
    dsimp only [bNatLen]; rw [Nat.add_eq, bNatLen_eq z us, bDC]
    rw [rkmw_altIntLen_eq, rkmw_altIntLen_eq]; simp only [List.length_cons]
private def bTrimL (z thr : ℕ) : ℕ → List ℕ → ℕ → ℕ × List ℕ × ℕ
  | _, [], acc => (0, [], acc)
  | off, u :: us, acc =>
    fN (bAbsZ z u) fun ax =>
      match Nat.ble ax thr with
      | true =>
        fN (Nat.add off 1) fun off1 =>
          fN (Nat.add acc ax) fun acc1 => bTrimL z thr off1 us acc1
      | false => (off, u :: us, acc)
private theorem bTrimL_eq (z thr : ℕ) : ∀ (us : List ℕ) (off acc : ℕ),
    ((bTrimL z thr off us acc).1, bDec z (bTrimL z thr off us acc).2.1,
      (bTrimL z thr off us acc).2.2) = rkmTrimLeft thr off (bDec z us) acc
  | [], _, _ => by rw [bDN]; rfl
  | u :: us, off, acc => by
    rw [bDC]; dsimp only [bTrimL, rkmTrimLeft, fN]; simp only [rkmb_forceNat_eq]; rw [bAbsZ_eq z u]
    cases Nat.ble (rkmIntAbsNat ((u : ℤ) - (z : ℤ))) thr with
    | false => dsimp only; rw [bDC]
    | true =>
      dsimp only
      exact bTrimL_eq z thr us (Nat.add off 1) (Nat.add acc (rkmIntAbsNat ((u : ℤ) - (z : ℤ))))
private def bTrimR (z thr : ℕ) : List ℕ → List ℕ × ℕ
  | [] => ([], 0)
  | u :: us =>
    match bTrimR z thr us with
    | ([], dTail) =>
      fN (bAbsZ z u) fun ax =>
        match Nat.ble ax thr with
        | true => fN (Nat.add ax dTail) fun dSum => ([], dSum)
        | false => (uCN u [], dTail)
    | (v :: vs, dTail) => (uCN u (v :: vs), dTail)
private theorem bTrimR_eq (z thr : ℕ) : ∀ (us : List ℕ),
    (bDec z (bTrimR z thr us).1, (bTrimR z thr us).2) = rkmTrimRight thr (bDec z us)
  | [] => by rw [bDN]; rfl
  | u :: us => by
    rw [bDC z u us]; dsimp only [bTrimR, rkmTrimRight]; rw [← bTrimR_eq z thr us]
    rcases bTrimR z thr us with ⟨ws, dTail⟩; cases ws with
    | nil =>
      dsimp only; rw [bDN]; dsimp only [fN]; simp only [rkmb_forceNat_eq]; rw [bAbsZ_eq z u]
      cases Nat.ble (rkmIntAbsNat ((u : ℤ) - (z : ℤ))) thr with
      | true => rfl
      | false => dsimp only; rw [uCNe, bDC, bDN, rkmw_strictConsInt_eq]
    | cons v vs =>
      dsimp only; rw [bDC z v vs]; dsimp only; rw [uCNe, bDC, bDC z v vs, rkmw_strictConsInt_eq]
private def bTrimW (z thr off : ℕ) (us : List ℕ) (dropAcc : ℕ) : ℕ × List ℕ × ℕ :=
  match bTrimL z thr off us dropAcc with
  | (off1, us1, d1) =>
    match bTrimR z thr us1 with
    | ([], d2) => fN (Nat.add d1 d2) fun dOut => (0, [], dOut)
    | (v :: vs, d2) => fN (Nat.add d1 d2) fun dOut => (off1, v :: vs, dOut)
private theorem bTrimW_eq (z thr off : ℕ) (us : List ℕ) (dropAcc : ℕ) :
    ((bTrimW z thr off us dropAcc).1, bDec z (bTrimW z thr off us dropAcc).2.1,
      (bTrimW z thr off us dropAcc).2.2) = rkmTrimWin thr off (bDec z us) dropAcc := by
  dsimp only [bTrimW, rkmTrimWin]; rw [← bTrimL_eq z thr us off dropAcc]
  rcases bTrimL z thr off us dropAcc with ⟨off1, us1, d1⟩; dsimp only; rw [← bTrimR_eq z thr us1]
  rcases bTrimR z thr us1 with ⟨ws, d2⟩; cases ws with
  | nil => dsimp only [fN]; simp only [rkmb_forceNat_eq]; rfl
  | cons v vs => dsimp only [fN]; simp only [rkmb_forceNat_eq]; rw [bDC z v vs]
private def bWinStepN (z thr d : ℕ) (hbz : List ℕ)
    (off : ℕ) (us : List ℕ) (dropAcc : ℕ) : Option (ℕ × List ℕ × ℕ) :=
  fN (Nat.sub off 16) fun sLo => fN (Nat.sub off sLo) fun padL =>
    fN (Nat.sub (Nat.add d 1) sLo) fun remMax => fL (bDrop2 sLo hbz) fun hbzSl =>
      fL (bPrepZ z padL us) fun vns => fN (bNatLen vns) fun curLen =>
        match bIt z 1 remMax curLen hbzSl vns with
        | none => none
        | some out => some (bTrimW z thr sLo out dropAcc)
private theorem bWinStepN_sound (z thr d : ℕ) (b : List ℕ)
    (off : ℕ) (us : List ℕ) (dropAcc o1 : ℕ) (u1 : List ℕ) (d1 : ℕ)
    (h : bWinStepN z thr d (mkHbZ z b) off us dropAcc = some (o1, u1, d1)) :
    (o1, bDec z u1, d1) = muxWinStepT16 thr d (uON b) off (bDec z us) dropAcc := by
  unfold bWinStepN at h; unfold muxWinStepT16; dsimp only [fN, fL] at h
  simp only [rkmb_forceNat_eq, rkmb_forceList_eq] at h ⊢
  set sLo := Nat.sub off 16; set padL := Nat.sub off sLo
  set remMax := Nat.sub (Nat.add d 1) sLo; set vns := bPrepZ z padL us
  rw [bDrop2_mkHbZ] at h; revert h
  cases hi : bIt z 1 remMax (bNatLen vns) (mkHbZ z (bDropN sLo b)) vns with
  | none => intro h; dsimp only at h; cases h
  | some out =>
    intro h; dsimp only at h; injection h with h'
    have ho : o1 = (bTrimW z thr sLo out dropAcc).1 := (congrArg Prod.fst h').symm
    have hu : u1 = (bTrimW z thr sLo out dropAcc).2.1 := (congrArg (fun p => p.2.1) h').symm
    have hd : d1 = (bTrimW z thr sLo out dropAcc).2.2 := (congrArg (fun p => p.2.2) h').symm
    rw [ho, hu, hd, bTrimW_eq z thr sLo out dropAcc]
    rw [bItS z 1 remMax (bNatLen vns) (bDropN sLo b) vns out hi]
    dsimp only [vns]; rw [bNatLen_eq z (bPrepZ z padL us), bDropN_uON sLo b, bPrepZ_eq z padL us]
private def bWinIterN (z : ℕ) :
    ℕ → ℕ → ℕ → List ℕ → ℕ → List ℕ → ℕ → Option (ℕ × List ℕ × ℕ)
  | 0, _, _, _, off, us, dropAcc => some (off, us, dropAcc)
  | k + 1, thr, d, hbz, off, us, dropAcc =>
    match bWinStepN z thr d hbz off us dropAcc with
    | none => none
    | some (off1, us1, drop1) => bWinIterN z k thr d hbz off1 us1 drop1
private theorem bWinIterN_sound (z : ℕ) :
    ∀ (k thr d : ℕ) (b : List ℕ) (off : ℕ) (us : List ℕ) (dropAcc oR : ℕ) (uR : List ℕ) (dR : ℕ),
      bWinIterN z k thr d (mkHbZ z b) off us dropAcc = some (oR, uR, dR) →
        (oR, bDec z uR, dR) = muxWinIterT16 k thr d (uON b) off (bDec z us) dropAcc
  | 0, _, _, _, off, us, dropAcc, oR, uR, dR, h => by
    dsimp only [bWinIterN, muxWinIterT16] at h ⊢; injection h with h'
    rcases Prod.mk.inj h' with ⟨rfl, h2⟩; rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩; rfl
  | k + 1, thr, d, b, off, us, dropAcc, oR, uR, dR, h => by
    dsimp only [bWinIterN, muxWinIterT16] at h ⊢; revert h
    cases hs : bWinStepN z thr d (mkHbZ z b) off us dropAcc with
    | none => intro h; dsimp only at h; cases h
    | some res1 =>
      rcases res1 with ⟨o1, u1, d1⟩; intro h; dsimp only at h
      rw [← bWinStepN_sound z thr d b off us dropAcc o1 u1 d1 hs]; dsimp only
      exact bWinIterN_sound z k thr d b o1 u1 d1 oR uR dR h
private def bNatEq (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem bNatEq_true {a b : ℕ} (h : bNatEq a b = true) : a = b := by
  unfold bNatEq at h; simp only [Bool.and_eq_true, rkmw_nat_ble_eq_true] at h
  exact Nat.le_antisymm h.1 h.2
private def bWinChk (steps thr d : ℕ) (b : List ℕ)
    (offIn : ℕ) (xsIn : List ℤ) (offOut : ℕ) (xsOut : List ℤ) (dropExp : ℕ) : Bool :=
  let z := 2000000000000000
  fL b fun bF => fL (mkHbZ z bF) fun hbz => fL xsIn fun inF => fL xsOut fun outF =>
    match bEnc z inF with
    | none => false
    | some uIn =>
      match bWinIterN z steps thr d hbz offIn uIn 0 with
      | none => false
      | some (oR, uR, dR) =>
        Bool.and (bNatEq oR offOut) (Bool.and (muxIntListEq (bDec z uR) outF) (bNatEq dR dropExp))
private theorem bWinChk_sound {steps thr d : ℕ} {b : List ℕ}
    {offIn : ℕ} {xsIn : List ℤ} {offOut : ℕ} {xsOut : List ℤ} {dropExp : ℕ}
    (h : bWinChk steps thr d b offIn xsIn offOut xsOut dropExp = true) :
    RkmWinIterSound steps d (uON b) offIn xsIn offOut xsOut dropExp := by
  unfold bWinChk at h; dsimp only [fL] at h; simp only [rkmb_forceList_eq] at h
  set z := 2000000000000000; revert h
  cases he : bEnc z xsIn with
  | none => intro h; dsimp only at h; cases h
  | some uIn =>
    dsimp only; cases hi : bWinIterN z steps thr d (mkHbZ z b) offIn uIn 0 with
    | none => intro h; dsimp only at h; cases h
    | some res =>
      rcases res with ⟨oR, uR, dR⟩; intro h; dsimp only at h
      simp only [Bool.and_eq_true, muxIntListEq_eq_true] at h
      obtain ⟨ho, hx, hd⟩ := h; have ho' := bNatEq_true ho; have hd' := bNatEq_true hd
      subst ho'; subst hx; subst hd'
      have hit := bWinIterN_sound z steps thr d b offIn uIn 0 oR uR dR hi
      rw [bES z xsIn uIn he] at hit
      have h2 : muxWinIterT16HiChk steps thr 0 d (uON b) offIn xsIn oR (bDec z uR) dR = true := by
        unfold muxWinIterT16HiChk; simp only [rkmb_forceList_eq]; rw [← hit]
        simp only [Bool.and_eq_true, rkmw_nat_beq_eq_true, muxIntListEq_eq_true]
        exact ⟨trivial, trivial, trivial⟩
      exact muxWinIterT16HiChk_sound h2
private theorem rkmChS (kT dT : ℕ) {k1 k2 d o0 o1 o2 d1 d2 : ℕ}
    {b : List ℕ} {x0 x1 x2 : List ℤ} (h1 : RkmWinIterSound k1 d (uON b) o0 x0 o1 x1 d1)
    (h2 : bWinChk k2 100000000 d b o1 x1 o2 x2 d2 = true) (hk : k1 + k2 = kT) (hd : d1 + d2 = dT) :
    RkmWinIterSound kT d (uON b) o0 x0 o2 x2 dT :=
  rkmChainWinIterT16 hk hd (muxIntListEq_eq_true.mpr rfl) rfl
    (muxIntListEq_eq_true.mpr rfl) h1 (bWinChk_sound h2)
private theorem rkmSubHb {s d o0 o1 dr : ℕ} {h1 h2 x0 x1 : List ℤ}
    (heq : muxIntListEq h1 h2 = true) (h : RkmWinIterSound s d h2 o0 x0 o1 x1 dr) :
    RkmWinIterSound s d h1 o0 x0 o1 x1 dr := by
  rw [muxIntListEq_eq_true.mp heq]; exact h
private theorem rkmSegWalk_mk {nSub d offIn offOut dropSeg : ℕ}
    {hb xsIn xsOut : List ℤ} (hhb : hb.length = d)
    (hble : Nat.ble (Nat.add offIn (altIntLen xsIn)) (Nat.add d 1) = true)
    (hiter : RkmWinIterSound nSub d hb offIn xsIn offOut xsOut dropSeg) :
    RkmWinSegWalkSound nSub ⟨d, hb, offIn, xsIn, offOut, xsOut, dropSeg⟩ := by
  simp only [rkmw_nat_ble_eq_true, rkmw_altIntLen_eq, Nat.add_eq] at hble
  obtain ⟨hout, hbd⟩ := hiter hhb hble; exact ⟨hhb, hble, hout, hbd⟩
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true :=
  (rkmAllTrueF_cons h).2
private theorem rkmTl4 {a b c d : Bool} {bs : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: bs) = true) : rkmAllTrueF bs = true :=
  rkmTl (rkmTl (rkmTl (rkmTl h)))
private def rkmZZ (u : ℕ) : ℤ :=
  match Nat.ble (Nat.mod u 2) 0 with
  | true => Int.ofNat (Nat.div u 2)
  | false => Int.negSucc (Nat.div u 2)
private def rkmMapZZ : List ℕ → List ℤ
  | [] => []
  | u :: us => rkmZZ u :: rkmMapZZ us
private def hbN_w64_m4_s0 : List ℕ := [344649600000000,471700409591597,557850597066049,
  620415089480536,666106267793848,698275603630152,718771284142833,728609003927953,728250700978365,
  717711409468252,696560357601512,663816674044413,617674592252271,554840343762598,468693708041763,
  342115998381850]
private def hbN_w64_m4_s1 : List ℕ := [228855807409596,318398220338613,383427866142335,
  435089733491235,477750415829432,513666885819010,544184982905867,570180610044170,592257677943157,
  610849058935564,626272916047984,638766252197418,648505853220387,655621770279877,660206109562125,
  662318681694232,661990394842988,659224876258548,653998539836080,646259105079862,635922361610417,
  622866709293193,606924611210222,587869440082051,565395005602471,539082716446697,508346394854683,
  472333302315426,429729960859434,378329115532082,313852799603058,225365059145803]
private def hbN_w64_m4_s2 : List ℕ := [175972352000000,246790002761388,299699758809100,
  343093316193688,380246466215248,412850862702269,441917682332156,468109409740077,491888416684835,
  513592696549442,533478195406723,551744171325571,568549232562565,584021932625997,598268024768564,
  611375580074046,623418690918043,634460209416097,644553810318814,653745570099781,662075192455242,
  669576970602892,676280550336144,682211539857582,687392000000000,691840839685666,695574135186415,
  698605387154044,700945725976346,702604073428601,703587266591069,703900148418057,703545628048846,
  702524712851235,700836513210982,698478220163139,695445055048130,691730189410719,687324632282820,
  682217080729469,676393728000000,669838021692840,662530361846556,654447725577652,645563200459604,
  635845402780231,625257748378741,613757531804632,601294752264732,587810599357309,573235473205004,
  557486354289477,540463244077329,522044243073316,502078570392865,480376363500971,456693229707407,
  430705807071148,401970949459868,369852669318105,333378742075075,290920341766835,239319056505780,
  170473216000000]
private def hbN_w64_m4_s3_p0 : List ℕ := [131552109631740,185224115276725,225846935330810,
  259621543226385,288960702537048,315107055002821,338801775993953,360529668303300,380628747268401,
  399346015607015,416868594083329,433342346311112,448883643615237,463587128955811,477531028515310,
  490780897033851,503392327546562,515412955810133,526883971904438,537841279686850,548316399606086,
  558337181171952,567928372019956,577112077398693,585908134851790,594334422499075,602407114772658,
  610140896165467,617549141126290,624644066432432,631436861014420,637937797175543,644156326356756,
  650101161983545,655780351451475,661201338929146,666371020357164,671295791781943,675981591970117,
  680433940093115,684657969144137,688658455645555,692439846118888,696006280718446,699361614370645,
  702509435711570,705453084073924,708195664739521,710740062643845,713088954694049,715244820840212,
  717209954021225,718986469090805,720576310815321,721981261023208,723202944975240,724242837015790,
  725102265557067,725782417441109,726284341717865,726608952871857,726757033524601,726729236635109,
  726526087216220,726147983580298,725595198123709,724867877655598,723966043272639,722889589777567,
  721638284635464,720211766457766,718609542999846,716830988653656,714875341412246,712741699277940,
  710429016080450,707936096665113,705261591404686,702403989980558,699361614370645,696132610971544,
  692714941771367,689106374476922,685304471484162,681306577563693,677109806113226,672711023805520,
  668106833432916,663293554717232,658267202815336,653023464205033,647557669581123,641864763325711,
  635939269037319,629775250506756,623366267409796,616705324841864,609784815641040,602596454223299,
  595131200375618,587379171101886,579329538171326,570970408449320,562288683355044,553269892832391,
  543897997960557,534155154655671,524021428662798,513474448971998,502488982562784,491036407460100,
  479084052660892,466594361291301,453523815339114,439821533113809,425427408526069,410269594397991,
  394261022269896,377294464457813,359235312822909]
private def hbN_w64_m4_s3_p1 : List ℕ := [339910631034934,319091815077034,296465597091142,
  271582069958215,243752518029184,211820797918455,173539315667620,123124381030565]
private def hbN_w64_m4_s3 : List ℕ :=
  pCat hbN_w64_m4_s3_p0 hbN_w64_m4_s3_p1
private def hbN_w64_m4_s4_p0 : List ℕ := [98183056290816,138512666788937,169226947012646,
  194925974116861,217396197923584,237556087469838,255952572740610,272942854655325,288775626704623,
  303632379937276,317650438769831,330936731916557,343576484395101,355638949194000,367181325553527,
  378251519790316,388890141285706,399131977886927,409007107776765,418541751739604,427758936346214,
  436679016986581,445320095376698,453698356481448,461828343109667,469723181738735,477394769770339,
  484853931987205,492110552194303,499173684699774,506051649291695,512752112607403,519282158209165,
  525648347228423,531856771088098,537913097534638,543822610991136,549590248066747,555220628916066,
  560718085027544,566086683926736,571330251203869,576452390212382,581456499733156,586345789856002,
  591123296293957,595791893315731,600354305456270,604813118143885,609170787364249,613429648465998,
  617591924199495,621659732068932,625635091068229,629519927862755,633316082471648,637025313499204,
  640649302958327,644189660724242,647647928652536,651025584391886,654324044918672,657544669817811,
  660688764331686,663757582196820,666752328286012,669674161071910,672524194926473,675303502269395,
  678013115577335,680654029264728,683227201445956,685733555587784,688173982060185,690549339592966,
  692860456644976,695108132692077,697293139439588,699416221964377,701478099791414,703479467909161,
  705420997727853,707303337984397,709127115597323,710892936474946,712601386279691,714253031151261,
  715848418391170,717388077110954,718872518846207,720302238138436,721677713086592,722999405869974,
  724267763244130,725483217011214,726646184466195,727757068820194,728816259602152,729824133039941,
  730781052421953,731687368440146,732543419515443,733349532106322,734106021001397,734813189596711,
  735471330158433,736080724071593,736641642075451,737154344486061,737619081406533,738036092925499,
  738405609304208,738727851152677,739003029595296,739231346426223,739412994254932,739548156642193,
  739637008226792,739679714843237,739676433630702]
private def hbN_w64_m4_s4_p1 : List ℕ := [739627313133413,739532493392694,739392106030833,
  739206274326947,738975113284981,738698729693961,738377222180627,738010681254519,737599189345609,
  737142820834531,736641642075451,736095711411614,735505079183575,734869787730116,734189871381828,
  733465356447325,732696261192046,731882595809574,731024362385385,730121554852949,729174158942043,
  728182152119159,727145503519851,726064173872854,724938115415773,723767271802154,722551577999690,
  721290960179306,719985335594866,718634612453179,717238689773989,715797457239597,714310795033726,
  712778573669214,711200653804097,709576886045601,707907110741513,706191157758392,704428846246009,
  702619984387379,700764369133690,698861785923387,696912008384609,694914798020129,692869903873865,
  690777062177965,688635995979423,686446414745041,684208013943533,681920474603426,679583462845315,
  677196629386952,674759609019468,672272020052960,669733463729477,667143523601317,664501764872351,
  661807733699929,659060956454688,656260938935387,653407165535614,650499098358980,647536176279075,
  644517813940167,641443400694241,638312299469591,635123845565723,631877345368851,628572074981723,
  625207278760897,621782167753955,618295918028350,614747668882796,611136520931152,607461534047720,
  603721725161725,599916065887423,596043479974805,592102840564236,588092967226454,584012622767263,
  579860509773836,575635266876804,571335464699203,566959601459784,562506098194112,557973293552231,
  553359438126257,548662688255086,543881099246229,539012617946427,534055074583052,529006173786960,
  523863484694228,518624430008631,513286273888365,507846108498766,502300839046961,496647167083547,
  490881571819439,485000289161563,478999288117248,472874244151767,466620509003527,460233076363200,
  453706542701630,447035062380338,440212295989337,433231350618564,426084710466389,418764155800870,
  411260667788740,403564316054565,395664124973885,387547913562195,379202102285654,370611478027577,
  361758905557659,352624969807042,343187527496703]
private def hbN_w64_m4_s4_p2 : List ℕ := [333421138328109,323296333625423,312778661715077,
  301827420540283,290393942211108,278419219008109,265830532389754,252536519389968,238419687060681,
  223324546900353,207037756160785,189252491401660,169498356821722,146984405658446,120170269893728,
  85084360396294]
private def hbN_w64_m4_s4 : List ℕ :=
  pCat hbN_w64_m4_s4_p0 (pCat hbN_w64_m4_s4_p1 hbN_w64_m4_s4_p2)
private def rkmC_w64_m4_s4_1 : List ℤ := rkmMapZZ [659813022,1442450180,2935945964,5810547538,
  11110218632,21138052046,38985217988,70641433254,125529220264,218296012564,372309149542,
  621958616720,1018555148402,1635425861110,2574652786530,3975415304136,6020235353732,8943700623806,
  13035819250340,18643946860790,26168275936114,36049884083290,48750889092348,64723621586994,
  84371831486944,108003416092060,135779404076268,167662407915742,203371772676712,242351840451724,
  283757949240442,326468675237364,369122696459284,410183949280094,448030834094650,481060290088342,
  507801826092002,527025590108174,537836991974650,539745884357546,532702384047050,517098686044070,
  493731768090254,463737890219398,428501221248572,389549789190642,348448139767642,306696959079186,
  265649105922782,226446359364406,189981248997108,156882010305604,127520951480502,102038546472870,
  80379929176104,62339072368520,47602140257216,35790869865480,26498578370578,19319724211966,
  13871948969334,9809384286788,6831992098006,4686731731724,3166875985868,2108014822180,
  1382079072444,892759545162,568002919198,356043144962,219813125282,133596548596,79829011588,
  46912252034,27080024790,15066911992,8096253104,4006472694,1764719182,607740892]
private def hbN_w64_m4_s5_p0 : List ℕ := [74849096529183,105697537275383,129262564258846,
  149040178353163,166386676854326,181998706166435,196290721412572,209533160020304,221914142556913,
  233570837184201,244606944322527,255103144756451,265123691620802,274720755508339,283937393670076,
  292809641275908,301368022725068,309638668337246,317644155563577,325404153534579,332935924414099,
  340254718647186,347374090341243,354306151676618,361061780173943,367650789083996,374082068622989,
  380363703933641,386503074299430,392506937133430,398381499506715,404132479406446,409765158472568,
  415284427620390,420694826689458,426000579049041,431205621923885,436313633070805,441328054329649,
  446252112485583,451088837809176,455841080583126,460511525876991,465102706792120,469617016366348,
  474056718300892,478423956649050,482720764587175,486949072372184,491110714576130,495207436676692,
  499240901072451,503212692583275,507124323488792,510977238151596,514772817266362,518512381771296,
  522197196454223,525828473282027,529407374478999,532935015376924,536412467057308,539840758804018,
  543220880382746,546553784162058,549840387089301,553081572533364,556278192005133,559431066765431,
  562540989329345,565608724875002,568635012564125,571620566781063,574566078296363,577472215360456,
  580339624732527,583168932649217,585960745737424,588715651875094,591434221003602,594117005895013,
  596764542877257,599377352520023,601955940283938,604500797135422,607012400129410,609491212961986,
  611937686494803,614352259253044,616735357898531,619087397679499,621408782858425,623699907119207,
  625961153954911,628192897037202,630395500568513,632569319617937,634714700441739,636831980789361,
  638921490195703,640983550260433,643018474915030,645026570678198,647008136900286,648963465997273,
  650892843674865,652796549143217,654674855322736,656528029041446,658356331224305,660160017074894,
  661939336249834,663694533026302,665425846462962,667133510554632,668817754380992,670478802249583,
  672116873833408,673732184303331,675324944455559]
private def hbN_w64_m4_s5_p1 : List ℕ := [676895360834394,678443635850492,679969967894810,
  681474551448445,682957577188541,684419232090426,685859699526161,687279159359627,688677788038327,
  690055758682014,691413241168300,692750402215348,694067405461791,695364411543972,696641578170625,
  697899060195088,699137009685166,700355575990708,701554905809021,702735143248176,703896429888302,
  705038904840953,706162704806596,707267964130315,708354814855793,709423386777623,710473807492029,
  711506202446037,712520694985170,713517406399702,714496455969546,715457961007796,716402036903001,
  717328797160187,718238353440696,719130815600868,720006291729604,720864888184863,721706709629113,
  722531859063784,723340437862745,724132545804853,724908281105583,725667740447789,726411019011619,
  727138210503604,727849407184952,728544699899081,729224178098398,729887929870365,730536041962862,
  731168599808874,731785687550527,732387388062481,732973782974711,733544952694692,734100976429003,
  734641932204368,735167896888149,735678946208318,736175154772907,736656596088960,737123342581007,
  737575465609056,738013035486139,738436121495406,738844791906792,739239113993256,739619154046625,
  739984977393025,740336648407939,740674230530882,740997786279709,741307377264574,741603064201533,
  741884906925818,742152964404774,742407294750483,742647955232068,742875002287703,743088491536312,
  743288477788992,743475015060145,743648156578342,743807954796908,743954461404255,744087727333955,
  744207802774559,744314737179179,744408579274825,744489377071513,744557177871146,744612028276163,
  744653974197985,744683060865236,744699332831756,744702833984420,744693607550745,744671696106307,
  744637141581969,744589985270915,744530267835502,744458029313936,744373309126765,744276146083200,
  744166578387268,744044643643798,743910378864235,743763820472305,743605004309511,743433965640479,
  743250739158152,743055358988825,742847858697041,742628271290338,742396629223851,742152964404774,
  741897308196682,741629691423717,741350144374635]
private def hbN_w64_m4_s5_p2 : List ℕ := [741058696806724,740755377949587,740440216508796,
  740113240669416,739774478099405,739423955952883,739061700873286,738687738996383,738302095953186,
  737904796872731,737495866384740,737075328622168,736643207223631,736199525335716,735744305615177,
  735277570231016,734799340866452,734309638720771,733808484511069,733295898473878,732771900366688,
  732236509469344,731689744585348,731131624043037,730562165696661,729981386927342,729389304643929,
  728785935283737,728171294813188,727545398728325,726908262055229,726259899350319,725600324700547,
  724929551723474,724247593567244,723554462910440,722850171961826,722134732459989,721408155672850,
  720670452397075,719921632957366,719161707205634,718390684520063,717608573804049,716815383485028,
  716011121513176,715195795360000,714369412016793,713531977992984,712683499314345,711823981521087,
  710953429665820,710071848311389,709179241528577,708275612893675,707360965485923,706435301884808,
  705498624167229,704550933904520,703592232159329,702622519482358,701641795908947,700650060955516,
  699647313615853,698633552357242,697608775116441,696572979295493,695526161757376,694468318821486,
  693399446258945,692319539287746,691228592567702,690126600195238,689013555697972,687889452029130,
  686754281561748,685608036082691,684450706786462,683282284268803,682102758520092,680912118918511,
  679710354223003,678497452565994,677273401445887,676038187719309,674791797593122,673534216616172,
  672265429670793,670985420964029,669694174018598,668391671663570,667077896024757,665752828514811,
  664416449823017,663068739904769,661709677970738,660339242475694,658957411107000,657564160772748,
  656159467589546,654743306869918,653315653109338,651876479972860,650425760281345,648963465997273,
  647489568210116,646004037121276,644506842028556,642997951310158,641477332408197,639944951811705,
  638400775039112,636844766620197,635276890077469,633697107906984,632105381558560,630501671415379,
  628885936772948,627258135817412,625618225603170]
private def hbN_w64_m4_s5_p3 : List ℕ := [623966162029797,622301899818228,620625392486189,
  618936592322841,617235450362609,615521916358172,613795938752576,612057464650440,610306439788224,
  608542808503515,606766513703309,604977496831225,603175697833642,601361055124690,599533505550063,
  597692984349604,595839425118614,593972759767831,592092918482032,590199829677190,588293419956139,
  586373614062673,584440334834028,582493503151661,580533037890269,578558855864965,576570871776527,
  574568998154652,572553145299107,570523221218696,568479131567946,566420779581398,564348066005415,
  562260889027360,560159144202065,558042724375423,555911519604994,553765417077476,551604301022892,
  549428052625320,547236549930028,545029667746807,542807277549323,540569247370302,538315441692311,
  536045721333938,533759943331112,531457960813318,529139622874446,526804774437978,524453256116213,
  522084904063211,519699549821111,517297020159454,514877136907130,512439716776516,509984571179388,
  507511506034101,505020321563559,502510812083419,499982765779946,497435964476913,494870183390864,
  492285190874040,489680748144197,487056609000484,484412519524523,481748217765702,479063433409696,
  476357887429084,473631291714877,470883348687689,468113750887131,465322180537956,462508309091311,
  459671796739337,456812291901205,453929430678515,451022836277802,448092118397681,445136872577975,
  442156679507890,439151104290067,436119695657005,433061985136077,429977486158915,426865693110626,
  423726080313755,420558100941481,417361185853916,414134742350771,410878152832924,407590773364647,
  404271932127322,400920927754503,397537027536989,394119465485318,390667440235590,387180112782884,
  383656604024590,380095992093846,376497309460737,372859539776067,369181614429239,365462408787941,
  361700738082975,357895352896441,354044934205554,350148087927442,346203338902138,342209124241426,
  338163785959944,334065562791586,329912581078394,325702844600171,321434223190371,317104439956469,
  312711056889907,308251458610532,303722833941235]
private def hbN_w64_m4_s5_p4 : List ℕ := [299122154948039,294446153006193,289691291359771,
  284853733525873,279929306747601,274913459513381,269801211921170,264587097357328,259265093557506,
  253828540587113,248270042574241,242581349079665,236753210696926,230775201692096,224635499994363,
  218320611291300,211815018827585,205100732887332,198156702432224,190958033554079,183474931053913,
  175671232910341,167502328145245,158912107861507,149828336636307,140155311533161,129761569096885,
  118457819345205,105953508265645,91759477864963,74921870445233,52977964352337]
private def hbN_w64_m4_s5 : List ℕ :=
  pCat hbN_w64_m4_s5_p0 (pCat hbN_w64_m4_s5_p1 (pCat hbN_w64_m4_s5_p2 (pCat hbN_w64_m4_s5_p3
    hbN_w64_m4_s5_p4)))
private def rkmC_w64_m4_s5_1 : List ℤ := rkmMapZZ [325300990,1173328474,3214212654,7814158392,
  17589758964,36665197204,73184851696,139621676112,256283134476,454562140684,780095840368,
  1299947415502,2106405174596,3324720612060,5118339966590,7693729702134,11303805447568,
  16246857469454,22861834690304,31517114901964,42594091147428,56463127297994,73454285893952,
  93823307523102,117715303046212,145130315998254,175892133579370,209627479577598,245755198068088,
  283491247859296,321871063474594,359785699414644,396035242843088,429391699400324,458669253394216,
  482795505853524,500876495490036,512253021457890,516538700688220,513641539655418,503764472705488,
  487385498550948,465222320257830,438180510426840,407295711841750,373669500290704,338408350732162,
  302567810785990,267105593358248,232846880664032,200461717905580,170455584610890,143170227434896,
  118795038794366,97384049978678,78878622602594,63132383760352,49934518057632,39033917728006,
  30158449568252,23032050695478,17387882494080,12977045068986,9575536782360,6985988910770,
  5039605987120,3595019496076,2535967215744,1769321264160,1220744214118,833020149684,562171224744,
  375098166780,247609441804,161419688002,104033043468,66070622662,41314003088,25364268872,
  15245397468,8760906618,4656361982,2305475660,873462038,243420292]
private def rkmC_w64_m4_s5_2 : List ℤ := rkmMapZZ [336419697,1244809903,2738879801,4977302539,
  7744362665,9671588927,7652174575,5307643604,41684319932,123560515202,286275448164,583776253830,
  1095893638932,1933579166298,3246745630998,5229225678096,8122345931218,12215778884360,
  17841975568234,25367299106364,35174759896646,47642096106974,63113286870362,81865310945456,
  104074850805408,129783100584452,158867706817104,191020944334860,225738929669230,262325269308094,
  299907262059604,337470053044234,373900602481058,408044504868896,438767833777868,465020821589820,
  485898518672454,500692104793706,508928665117228,510394490226682,505142275110152,493480521843814,
  475948464026660,453277172636694,426341349059302,396107467452898,363578777316076,329745635490256,
  295540291148104,261800225408720,229242758069404,198448053588656,169853982452238,143757752439672,
  120326249719388,99611444810542,81567981646066,66074675935532,52953467890940,41989164216150,
  32945909126904,25581065806680,19657554817202,14950737512728,11255270059206,8387595310180,
  6187653640332,4519316209592,3267955897614,2339915005698,1658927101402,1164536372428,809576105042,
  557155352504,379814276046,256246541556,171107004872,113052695642,73677831296,47510832822,
  30011262142,18618984210,11168517060,6256912682,3267981156,1268517496,355420250]
private def rkmC_w64_m4_s5_3 : List ℤ := rkmMapZZ [628335122,1643481710,2719916826,3854452130,
  3712359664,1315901344,5732763963,20018571101,43849120713,77942814907,118523110573,154437189977,
  161011714593,93661376371,120386539086,590598138694,1472015107932,2972613114806,5357751257158,
  8950808825464,14126633809870,21299767375310,30903288523304,43361296950034,59055589525640,
  78286282122004,101233785378246,127921304764468,158185026032084,191654568443372,227745850108246,
  265671047250670,304463121068274,343017659865182,380146076866026,414638287105420,445330870208962,
  471172278624568,491283868872596,505008064955894,511942736742284,511958422009172,505196921671700,
  492054869627620,473150167123642,449278752326756,421363157869488,390397803019150,357396226505128,
  323340843020306,289142242492880,255606012873520,223410431856594,193094629355940,165054964054784,
  139551467194898,116718541111278,96581705524668,79076507253346,64068053914908,51371509588194,
  40769019091848,32026284040930,24905170899480,19173965649456,14615501016214,11031187496238,
  8244763507180,6102524788090,4473396583184,3247883358116,2335542709874,1663643706196,
    1173830135080,
  820439345086,568110343294,389564659440,264621862222,177862206170,118269541770,77717908006,
  50299351618,32042288708,19959822740,11931571208,7009114190,3742476038,1720197510,592180930]
private def hbN_w64_m4_s6_p0 : List ℕ := [60710347323392,85773551447292,104948028362960,
  121064969955436,135222180491974,147983253063859,159683321957539,170540961528635,180708143204784,
  190295624714895,199387100747404,208047657009157,216329102996510,224273486358260,231915493913305,
  239284142380088,246403999979431,253296088878076,259978564865996,266467238028301,272775977660946,
  278917031425392,284901279960700,290738442231449,296437242790000,302005549251262,307450486221825,
  312778530435493,317995590753421,323107075873830,328117951984884,333032792129665,337855818695673,
  342590940165225,347241783047486,351811719743172,356303892958318,360721237176051,365066497608809,
  369342246983590,373550900455886,377694728901424,381775870796529,385796342866280,389758049653337,
  393662792138384,397512275524733,401308116284199,405051848548256,408744929917451,412388746752588,
  415984619003170,419533804621701,423037503606500,426496861710613,429912973849960,433286887240050,
  436619604287277,439912085257889,443165250745227,446379983953575,449557132815058,452697511954280,
  455801904513904,458871063853043,461905715129149,464906556773028,467874261865706,470809479425020,
  473712835609085,476584934843113,479426360875484,482237677768438,485019430828273,487772147479515,
  490496338087138,493192496730571,495861101932904,498502617348435,501117492411433,503706162948768,
  506269051758838,508806569159047,511319113503886,513807071675549,516270819548827,518710722431929,
  521127135484731,523520404115855,525890864359883,528238843235899,530564659088489,532868621912236,
  535151033660679,537412188540638,539652373292741,541871867458952,544070943637813,546249867728096,
  548408899161500,550548291124988,552668290773339,554769139432407,556851072793618,558914321100133,
  560959109325128,562985657342589,564994180091009,566984887730336,568957985792527,570913675326000,
  572852153034314,574773611409328,576678238859129,578566219830967,580437734929438,582292961030132,
  584132071388973,585955235747429,587762620433801]
private def hbN_w64_m4_s6_p1 : List ℕ := [589554388460752,591330699619258,593091710569141,
  594837574926319,596568443346944,598284463608535,599985780688264,601672536838488,603344871659677,
  605002922170815,606646822877406,608276705837169,609892700723526,611494934886966,613083533414382,
  614658619186448,616220312933131,617768733287401,619303996837208,620826218175809,622335509950493,
  623831982909772,625315745949101,626786906155176,628245568848867,629691837626841,631125814401916,
  632547599442197,633957291409043,635354987393902,636740782954052,638114772147301,639477047565667,
  640827700368086,642166820312179,643494495785103,644810813833537,646115860192813,647409719315227,
  648692474397575,649964207407906,651224999111557,652474929096467,653714075797801,654942516521912,
  656160327469664,657367583759123,658564359447652,659750727553424,660926760076367,662092528018571,
  663248101404154,664393549298632,665528939827777,666654340196012,667769816704325,668875434767743,
  669971258932366,671057352891972,672133779504224,673200600806463,674257878031131,675305671620801,
  676344041242862,677373045803837,678392743463368,679403191647859,680404447063807,681396565710811,
  682379602894278,683353613237839,684318650695471,685274768563342,686222019491384,687160455494607,
  688090127964148,689011087678077,689923384811963,690827068949192,691722189091071,692608793666700,
  693486930542628,694356647032298,695217989905287,696071005396349,696915739214256,697752236550457,
  698580542087544,699400700007550,700212754000057,701016747270147,701812722546179,702600722087403,
  703380787691424,704152960701503,704917282013715,705673792083955,706422530934808,707163538162274,
  707896852942358,708622514037535,709340559803075,710051028193253,710753956767426,711449382696000,
  712137342766271,712817873388161,713491010599835,714156790073213,714815247119375,715466416693863,
  716110333401883,716747031503404,717376544918162,717998907230577,718614151694565,719222311238268,
  719823418468701,720417505676297,721004604839385]
private def hbN_w64_m4_s6_p2 : List ℕ := [721584747628578,722157965411078,722724289254911,
  723283749933075,723836377927625,724382203433673,724921256363322,725453566349534,725979162749918,
  726498074650463,727010330869198,727515959959789,728014990215077,728507449670547,728993366107745,
  729472767057632,729945679803876,730412131386101,730872148603063,731325758015788,731772985950644,
  732213858502373,732648401537060,733076640695063,733498601393890,733914308831025,734323787986710,
  734727063626686,735124160304880,735515102366055,735899913948413,736278618986158,736651241212017,
  737017804159719,737378331166437,737732845375189,738081369737199,738423927014228,738760539780856,
  739091230426741,739416021158832,739734934003557,740047990808965,740355213246849,740656622814823,
  740952240838376,741242088472889,741526186705628,741804556357696,742077218085963,742344192384970,
  742605499588793,742861159872888,743111193255908,743355619601487,743594458620003,743827729870312,
  744055452761460,744277646554363,744494330363470,744705523158398,744911243765540,745111510869656,
  745306343015440,745495758609057,745679775919667,745858413080922,746031688092446,746199618821285,
  746362223003350,746519518244826,746671522023570,746818251690486,746959724470882,747095957465805,
  747226967653362,747352771890023,747473386911896,747588829335998,747699115661503,747804262270968,
  747904285431548,747999201296197,748089025904844,748173775185558,748253464955704,748328110923067,
  748397728686978,748462333739414,748521941466090,748576567147528,748626225960126,748670932977195,
  748710703169999,748745551408770,748775492463714,748800541006007,748820711608770,748836018748041,
  748846476803726,748852100060541,748852902708946,748848898846062,748840102476574,748826527513631,
  748808187779728,748785097007577,748757268840973,748724716835638,748687454460070,748645495096362,
  748598852041033,748547538505828,748491567618520,748430952423702,748365705883563,748295840878659,
  748221370208676,748142306593177,748058662672348]
private def hbN_w64_m4_s6_p3 : List ℕ := [747970451007728,747877684082936,747780374304385,
  747678534001990,747572175429866,747461310767016,747345952118018,747226111513692,747101800911772,
  746973032197561,746839817184581,746702167615215,746560095161345,746413611424974,746262727938854,
  746107456167091,745947807505757,745783793283485,745615424762061,745442713137014,745265669538187,
  745084305030316,744898630613590,744708657224213,744514395734953,744315856955694,744113051633969,
  743905990455501,743694684044725,743479142965314,743259377720695,743035398754554,742807216451351,
  742574841136809,742338283078414,742097552485902,741852659511740,741603614251604,741350426744854,
  741093106975000,740831664870160,740566110303523,740296453093800,740022703005666,739744869750211,
  739462962985368,739176992316356,738886967296100,738592897425659,738294792154644,737992660881636,
  737686512954589,737376357671244,737062204279527,736744061977948,736421939915990,736095847194506,
  735765792866097,735431785935500,735093835359957,734751950049598,734406138867800,734056410631563,
  733702774111865,733345238034022,732983811078044,732618501878985,732249319027289,731876271069137,
  731499366506783,731118613798896,730734021360890,730345597565255,729953350741883,729557289178394,
  729157421120454,728753754772095,728346298296025,727935059813941,727520047406838,727101269115312,
  726678732939862,726252446841190,725822418740495,725388656519769,724951168022083,724509961051877,
  724065043375245,723616422720215,723164106777029,722708103198418,722248419599880,721785063559943,
  721318042620443,720847364286783,720373036028199,719895065278019,719413459433926,718928225858208,
  718439371878015,717946904785609,717450831838615,716951160260263,716447897239636,715941049931911,
  715430625458596,714916630907772,714399073334325,713877959760177,713353297174521,712825092534050,
  712293352763179,711758084754273,711219295367868,710676991432892,710131179746884,709581867076210,
  709029060156276,708472765691742,707912990356733]
private def hbN_w64_m4_s6_p4 : List ℕ := [707349740795046,706783023620358,706212845416431,
  705639212737316,705062132107549,704481610022359,703897652947859,703310267321244,702719459550987,
  702125236017028,701527603070968,700926567036257,700322134208380,699714310855045,699103103216366,
  698488517505045,697870559906556,697249236579319,696624553654884,695996517238101,695365133407303,
  694730408214468,694092347685403,693450957819904,692806244591932,692158213949777,691506871816222,
  690852224088713,690194276639520,689533035315894,688868505940234,688200694310244,687529606199088,
  686855247355550,686177623504186,685496740345481,684812603555998,684125218788531,683434591672255,
  682740727812875,682043632792771,681343312171149,680639771484179,679933016245146,679223051944588,
  678509884050439,677793518008170,677073959240925,676351213149664,675625285113294,674896180488812,
  674163904611431,673428462794721,672689860330738,671948102490155,671203194522394,670455141655754,
  669703949097540,668949622034191,668192165631405,667431585034262,666667885367353,665901071734900,
  665131149220880,664358122889145,663581997783541,662802778928031,662020471326810,661235079964425,
  660446609805889,659655065796800,658860452863451,658062775912950,657262039833327,656458249493649,
  655651409744132,654841525416250,654028601322842,653212642258228,652393652998308,651571638300675,
  650746602904720,649918551531734,649087488885017,648253419649979,647416348494246,646576280067756,
  645733219002867,644887169914456,644038137400014,643186126039752,642331140396696,641473185016783,
  640612264428961,639748383145284,638881545661008,638011756454682,637139019988248,636263340707131,
  635384723040331,634503171400516,633618690184113,632731283771399,631840956526591,630947712797935,
  630051556917792,629152493202732,628250525953615,627345659455682,626437897978637,625527245776737,
  624613707088874,623697286138658,622777987134505,621855814269715,620930771722556,620002863656349,
  619072094219542,618138467545800,617201987754076]
private def hbN_w64_m4_s6_p5 : List ℕ := [616262658948697,615320485219437,614375470641601,
  613427619276101,612476935169529,611523422354241,610567084848425,609607926656185,608645951767607,
  607681164158843,606713567792177,605743166616102,604769964565393,603793965561178,602815173511013,
  601833592308949,600849225835606,599862077958242,598872152530824,597879453394097,596883984375653,
  595885749289999,594884751938625,593880996110072,592874485580000,591865224111252,590853215453923,
  589838463345425,588820971510549,587800743661535,586777783498134,585752094707671,584723680965108,
  583692545933111,582658693262108,581622126590354,580582849543993,579540865737117,578496178771829,
  577448792238303,576398709714844,575345934767948,574290470952361,573232321811139,572171490875704,
  571107981665906,570041797690077,568972942445092,567901419416422,566827232078194,565750383893246,
  564670878313184,563588718778434,562503908718302,561416451551026,560326350683829,559233609512979,
  558138231423835,557040219790906,555939577977902,554836309337788,553730417212833,552621904934667,
  551510775824328,550397033192316,549280680338644,548161720552887,547040157114235,545915993291541,
  544789232343370,543659877518051,542527932053725,541393399178392,540256282109964,539116584056306,
  537974308215292,536829457774845,535682035912992,534532045797904,533379490587945,532224373431722,
  531066697468123,529906465826373,528743681626072,527578347977240,526410467980369,525240044726459,
  524067081297069,522891580764357,521713546191127,520532980630868,519349887127803,518164268716929,
  516976128424057,515785469265861,514592294249915,513396606374736,512198408629827,510997703995719,
  509794495444009,508588785937404,507380578429761,506169875866126,504956681182776,503740997307258,
  502522827158429,501302173646496,500079039673053,498853428131125,497625341905201,496394783871274,
  495161756896884,493926263841149,492688307554808,491447890880255,490205016651582,488959687694609,
  487711906826926,486461676857926,485209000588848]
private def hbN_w64_m4_s6_p6 : List ℕ := [483953880812804,482696320314824,481436321871885,
  480173888252951,478909022219008,477641726523096,476372003910347,475099857118021,473825288875536,
  472548301904506,471268898918776,469987082624453,468702855719940,467416220895974,466127180835653,
  464835738214475,463541895700368,462245655953722,460947021627423,459645995366889,458342579810095,
  457036777587611,455728591322630,454418023631004,453105077121272,451789754394691,450472058045270,
  449151990659802,447829554817888,446504753091976,445177588047385,443848062242340,442516178227999,
  441181938548485,439845345740914,438506402335426,437165110855214,435821473816553,434475493728829,
  433127173094571,431776514409475,430423520162435,429068192835571,427710534904259,426350548837157,
  424988237096236,423623602136801,422256646407529,420887372350488,419515782401167,418141878988505,
  416765664534917,415387141456319,414006312162158,412623179055438,411237744532743,409850010984267,
  408459980793842,407067656338957,405673039990792,404276134114237,402876941067923,401475463204244,
  400071702869384,398665662403341,397257344139955,395846750406929,394433883525856,393018745812243,
  391601339575538,390181667119150,388759730740477,387335532730928,385909075375949,384480360955044,
  383049391741803,381616170003922,380180698003226,378742977995697,377303012231493,375860802954973,
  374416352404719,372969662813560,371520736408594,370069575411211,368616182037117,367160558496352,
  365702706993318,364242629726796,362780328889973,361315806670460,359849065250315,358380106806066,
  356908933508731,355435547523842,353959951011461,352482146126209,351002135017279,349519919828464,
  348035502698174,346548885759458,345060071140025,343569060962262,342075857343261,340580462394831,
  339082878223525,337583106930657,336081150612322,334577011359419,333070691257666,331562192387624,
  330051516824715,328538666639242,327023643896407,325506450656335,323987088974085,322465560899679,
  320941868478113,319416013749381,317887998748492]
private def hbN_w64_m4_s6_p7 : List ℕ := [316357825505488,314825496045464,313291012388587,
  311754376550114,310215590540411,308674656364967,307131576024421,305586351514572,304038984826400,
  302489477946086,300937832855027,299384051529854,297828135942451,296270088059975,294709909844866,
  293147603254872,291583170243063,290016612757849,288447932742998,286877132137649,285304212876335,
  283729176888996,282152026100998,280572762433147,278991387801708,277407904118422,275822313290521,
  274234617220745,272644817807357,271052916944163,269458916520525,267862818421377,266264624527243,
  264664336714253,263061956854156,261457486814339,259850928457841,258242283643369,256631554225315,
  255018742053768,253403848974535,251786876829150,250167827454893,248546702684807,246923504347707,
  245298234268203,243670894266707,242041486159455,240410011758516,238776472871811,237140871303126,
  235503208852126,233863487314372,232221708481331,230577874140398,228931986074901,227284046064123,
  225634055883311,223982017303696,222327932092500,220671802012954,219013628824315,217353414281872,
  215691160136968,214026868137007,212360540025473,210692177541942,209021782422092,207349356397723,
  205674901196764,203998418543293,202319910157544,200639377755923,198956823051024,197272247751637,
  195585653562764,193897042185632,192206415317705,190513774652698,188819121880589,187122458687633,
  185423786756372,183723107765652,182020423390630,180315735302792,178609045169964,176900354656320,
  175189665422402,173476979125127,171762297417799,170045621950124,168326954368223,166606296314640,
  164883649428355,163159015344801,161432395695869,159703792109925,157973206211817,156240639622894,
  154506093961010,152769570840540,151031071872392,149290598664016,147548152819416,145803735939165,
  144057349620411,142308995456893,140558675038951,138806389953533,137052141784214,135295932111201,
  133537762511347,131777634558161,130015549821819,128251509869177,126485516263777,124717570565864,
  122947674332393,121175829117041,119402036470216]
private def hbN_w64_m4_s6_p8 : List ℕ := [117626297939072,115848615067513,114068989396210,
  112287422462610,110503915800942,108718470942233,106931089414317,105141772741842,103350522446286,
  101557340045963,99762227056033,97965184988517,96166215352300,94365319653148,92562499393714,
  90757756073548,88951091189109,87142506233774,85332002697848,83519582068572,81705245830135,
  79888995463685,78070832447336,76250758256176,74428774362282,72604882234727,70779083339587,
  68951379139956,67121771095948,65290260664716,63456849300451,61621538454400,59784329574871,
  57945224107241,56104223493970,54261329174607,52416542585798,50569865161297,48721298331978,
  46870843525836,45018502168004,43164275680758,41308165483527,39450172992902,37590299622642,
  35728546783688,33864915884169,31999408329408,30132025521937,28262768861500,26391639745064,
  24518639566829,22643769718231,20767031587960,18888426561959,17007956023436,15125621352877,
  13241423928045,11355365123997,9467446313087,7577668864978,5686034146648,3792543522396,
  1897198353856]
private def hbN_w64_m4_s6 : List ℕ :=
  pCat hbN_w64_m4_s6_p0 (pCat hbN_w64_m4_s6_p1 (pCat hbN_w64_m4_s6_p2 (pCat hbN_w64_m4_s6_p3
    (pCat hbN_w64_m4_s6_p4 (pCat hbN_w64_m4_s6_p5 (pCat hbN_w64_m4_s6_p6 (pCat hbN_w64_m4_s6_p7
    hbN_w64_m4_s6_p8)))))))
private def rkmC_w64_m4_s6_1 : List ℤ := rkmMapZZ [312085414,685053476,1227433544,1196025538,
  757089842,509008583,2849899727,5934532125,9161223781,11068581315,9363991747,1690955129,
  14532039130,39856636866,72541731904,106281895736,128642078076,121038005648,59204407642,
  83891103399,331050274711,692814072841,1154756697369,1662567837943,2106791102297,2306891290595,
  2001020622043,839344270191,1613815619812,5865489325986,12471923849340,22002711902458,
  34996566268052,51911692753892,73072926080594,98623832102042,128485616010582,162331222286730,
  199575199432156,239383567517772,280704959940436,322318095329376,362896877940368,401083178581744,
  435565123153596,465153409235566,488847631831094,505891746009800,515809130459440,518421348749086,
  513844880124426,502470564770020,484927621036002,462035307151780,434748105721980,404097384444354,
  371135633750934,336884857882492,302293995297976,268204915091572,235329796734166,204239438588302,
  175359017320450,148974680605942,125244373010820,104214182854848,85837682692158,69994839929390,
  56512601358814,45181797366082,35774077664210,28054863241028,21793195588932,16770766903594,
  12786027984336,9658631718288,7229874269144,5362901599632,3942534569806,2872399379450,
  2074360156398,1484796031132,1053448804242,740824385074,516369757340,356681210828,244115276896,
  165534710654,110890977252,73481717640,48049071168,30881081908,19437903348,11712380586,6822790348,
  3623747694,1689309058,603736552]
private def rkmC_w64_m4_s6_2 : List ℤ := rkmMapZZ [380357029,113139783,539225500,1623522442,
  3167484350,4307230756,4681668782,3112258400,1119502513,8327444449,18110367561,28052319199,
  34883667221,33038139677,16943371225,18969797906,77365647984,154883924848,240085579416,
  310540916950,332730457112,263267914602,54529704512,336616499253,935639656243,1733692884283,
  2669109594899,3608422361887,4331284531263,4519089530537,3753983164633,1527495385447,
    2739047235304,
  9660015118556,19843057650688,33836564271688,52075058329306,74826081779152,102143219232740,
  133833522492626,169439320119636,208241459779486,249281285704772,291402742567684,333312084399664,
  373646916092314,411054296903294,444266808683762,472173955788060,493881965527780,508756809481792,
  516451512326162,516911448472114,510363720669654,497288967205950,478379880795018,454492380505930,
  426589457166738,395687809946002,362804519221194,328911946591648,294900100287304,261548673274840,
  229509425953382,199297110912286,171289610077210,145734475787506,122761847855850,102399541263362,
  84591478456794,69216136320704,56103753650248,45054077730102,35849421633112,28267202120492,
  22089299241422,17108741194918,13135244207446,9997006097260,7543243087276,5643390411952,
  4186336151980,3079546490170,2246361614016,1625162889888,1166074210014,829737648806,585565802124,
  409601165574,284172394460,195340834856,133044594884,89718527232,59649506458,39195189242,
  25163550998,15825166452,9596272378,5421236222,2851728318,1112673266,313087818]
private def rkmC_w64_m4_s6_3 : List ℤ := rkmMapZZ [853166439,1591736831,2079432513,1818666241,
  629972745,1902522716,5571378628,9804498952,13088946226,13264306766,8589304286,3035363143,
  21834653519,45956962815,70568477789,86999988029,84578207423,51038417881,23546893834,143129229408,
  301044897864,475216625632,626271973940,696350744426,614362735170,304054654596,301953290009,
  1242377562691,2506325747229,4009065831813,5572088093613,6907044740127,7609168900005,
    7163311309567,
  4961550044627,337307232063,7390635417828,18863129367446,34620641769724,55044726494198,
  80304027854850,110315132364210,144717676537078,182871015280122,223872523372036,266595508668154,
  309747378244708,351938690835056,391762547689790,427874255657910,459066117306016,484333295499668,
  502922367853048,514364594214094,518487583901266,515409234166756,505514988570548,489419416500340,
  467920044656786,441942531321296,412486355527564,380571718405508,347191115008034,313270201611108,
  279635112380460,246992205714288,215915370529200,186842681024372,160081107880470,135815105397814,
  114122140095960,94988265952606,78326609506532,63995216330090,51812846253150,41575177172982,
  33066182672696,26069643034566,20376681694446,15791261376280,12134880687732,9247340257864,
  6988860320246,5238825505764,3895099428856,2872887166938,2101886493134,1525703631148,
    1098654175776,
  784825684822,556249501782,390905479354,272552804554,188304539484,128937162652,87450970104,
  58522385304,38723090206,25009352982,15771219238,9529092372,5326496004,2749568012,1050298702,
  289339980]
private def rkmC_w64_m4_s6_4 : List ℤ := rkmMapZZ [203923124,763430068,1028320166,1113332500,
  489077772,889759981,2750976753,4805665007,5879635679,5438066587,2324106855,3930763266,
    12790956440,
  22748762840,30312825348,31757014776,22452383716,994719703,39166680967,88558130525,139316560763,
  176509853849,180135958407,129089846061,6111717503,196241705634,467429246616,774171183498,
  1055674601860,1225228595654,1176836455214,797868372492,9933324309,1306569001835,3084322859427,
  5240571970207,7554469249733,9671453305379,11101873606391,11232066851231,9354101480415,
  4709353531521,3454811184704,15819343401874,32927449319538,55120190447338,82485149334994,
  114820277523916,151618991820952,192079557238044,235135645267010,279510352940194,323784955100318,
  366480106900528,406141464297390,441421630279660,471155301257516,494417921995850,510568453326728,
  519271155189910,520496985567872,514507501648068,501820657827128,483166668039076,459434185434358,
  431613801279448,400742516638020,367850922748798,333919409508778,299841051999360,266395841804842,
  234234190884288,203869098444640,175677964261606,149908981292092,126694524815378,106066550480054,
  87974116191942,72302095164820,58887596982324,47536905457620,38038596908842,30175449151470,
  23733883967182,18510164528324,14316146105842,10981279996258,8354688785488,6305217806244,
  4720437572248,3506121617508,2583656969980,1889043585162,1370447974688,986448449446,704571891312,
  499320936602,350969907396,244855829230,169181757010,115852482832,78554779344,52423637288,
  34482044764,22120846658,13900301822,8380502426,4660241166,2372844072,887564210,238761138]
private def rkmC_w64_m4_s6_5 : List ℤ := rkmMapZZ [365028305,461535493,368857329,319872860,
  1295997840,2345497976,3107592734,2827395812,1349019300,1824063305,6165579759,10674583937,
  13698805233,12916129029,6798056361,5774703828,23721066120,43799802162,60276764230,65139656166,
  50554244362,10176638908,57104530241,145083071617,238267301341,311232452059,331841362333,
  265560204539,84369745007,223944953760,645723973598,1132556675376,1597882277640,1918060313586,
  1943563704466,1517388262404,502391147734,1185688205653,3543119631013,6444880337947,9618641546999,
  12631754865169,14893203945799,15676033906561,14157153164113,9474667869045,798423953429,
  12595003407806,31245490874066,55443795646272,85180491882438,120116052827982,159578252820886,
  202583097275606,247883132156984,294035616573870,339485756923826,382659190123466,422053360997178,
  456323651466416,484354595954710,505314548428300,518688457370438,524288618769812,522245077284098,
  512976935337250,497148410402914,475616216202204,449369334808154,419469864575208,386995747491582,
  352989985804768,318420141712944,284144904375638,250894200360772,219257731046068,189682188996010,
  162477719213262,137828153429410,115807250400200,96395979987000,79501363034038,64975092920464,
  52630010023270,42256429297686,33633973223776,26542355288200,20769430923034,16116777981020,
  12403559213974,9468318036858,7169355991102,5385449443610,4013386229076,2967436517448,
  2177160801662,1584850090228,1144916722556,820765512164,583839204246,412011198812,288309188616,
  200083792402,137644355968,93560025630,63024990712,41755494028,27124500552,17296759958,
    10576074824,
  6197699156,3218647096,1421626932,471653474]
private def rkmC_w64_m4_s6_6 : List ℤ := rkmMapZZ [682228833,1370438305,1716232151,1418987863,
  283319607,1800119516,4334326566,6594253702,7258420070,5311840014,115941954,8144534581,
    17597123249,
  25818939275,28730395647,22470504359,4633579971,25066924018,62086944296,98008855540,120279538622,
  114517978090,68481904406,24513423231,159626019765,318080859685,465515786341,554565841953,
  531746053951,348238743645,26468690480,589811822838,1293387174130,2034974724256,2660048633190,
  2972089823150,2755785383376,1810927538148,7515659565,2743518480851,6299317165729,10401882425935,
  14585601897627,18195256843279,20410809229211,20295861655183,16866064963919,9170584772459,
  3617439539592,22114983536690,46653539405416,77222370619050,113439785772380,154551601407484,
  199462197085212,246791405393266,294955081316498,342261809019778,387015352468640,427616248212368,
  462654386830970,490983125564960,511774576418910,524548862264668,529179488396164,525877094047490,
  515152033853948,497764506417102,474662412693456,446916909966068,415658600080920,382017056176592,
  347069593054002,311800535189520,277070089403426,243596629569690,211947545832376,182540747572438,
  155653119036100,131433620929562,109922509971994,91069365904788,74753638996482,60804156544542,
  49015897902182,39165291207968,31022949702832,24363014773252,18971381557670,14649607971306,
  11219078247910,8522067545064,6421078043976,4799542214370,3559170715478,2618660698984,
  1911710220822,1384787167740,995368149866,709933351390,502200242064,352539377992,245338735094,
  169171280424,115640569070,78159483884,52114694296,34288410986,21895523952,13678550988,8171640630,
  4460896322,2186606506,775111472]
private def rkmC_w64_m4_s6_7 : List ℤ := rkmMapZZ [205860728,584525612,931788670,846848186,
    21417341,
  1307880281,2782229049,3943071243,3854587917,2148070711,1555112060,6623318646,11558966800,
  14598871904,13103118272,5891061974,7502158851,25101401495,42278341395,52856155423,49612700095,
  26711127991,17304278286,78019373486,143157368546,193878047824,207168074808,160712935784,
  40991783696,151279553353,393821654905,640956249107,826392753761,871389530815,700035951675,
  258377676199,465238336130,1421165429314,2487687009264,3469555287816,4112207391302,4131099954902,
  3252515333742,1267611197032,1912246385655,6203154593359,11308800955795,16700567978419,
  21622423383495,25124659562515,26125217308071,23492801363677,16147952480657,3167167216053,
  16117002220528,42031773324128,74506380231902,113046098632396,156741018152612,204310704528618,
  254177922983684,304568183468154,353621627401708,399510264793446,440550246357704,475298083602222,
  502626060014336,521773094609896,532364917822020,534409931593254,528270081116136,514611161504112,
  494341861663094,468542105745556,438391862027280,405102489857304,369854916282146,333749429237652,
  297766974331246,262742502706622,229351978083054,198108499575660,169369220609104,143347856862722,
  120132545108876,99706923548438,81971300259962,66763687824460,53880381020386,43091705468222,
  34157689234028,26839460836198,20907391905364,16147883873004,12367221424786,9392981884312,
  7075713921296,5286914262526,3918520538642,2881241053840,2101765588644,1521039153062,
    1092275887330,
  778027865124,549826210836,385442898308,267865208142,184580079060,125994381196,84944093472,
  56676607148,37114104662,23800163974,14883717720,8829610222,4883071894,2463409018,875335648,
  218488186]
private def rkmC_w64_m4_s6_8 : List ℤ := rkmMapZZ [335816749,498051819,342769295,351965694,
  1397244360,2262908698,2518706920,1569439938,420070789,3514886343,6657644693,8323059367,
    7444355917,
  3005493207,5129801562,15189831354,24169658894,27875842338,22410421130,5765791076,21550832923,
  53898928119,82289637163,94697410259,79049048843,28395099371,56299361372,162831188670,
    266059617152,
  332133865310,323827226388,210846660000,19297047241,351212239747,734932154173,1086584369455,
  1297640324603,1252231646261,853626769183,52279734171,1126134412464,2561070933108,4031157483328,
  5225864102916,5777825614408,5314166918488,3520522945498,214056294650,4589731265165,
    10623562833049,
  17338321282691,23906043734839,29257352097793,32152058151543,31280822070987,25383252070813,
  13374314956989,5536706366754,31748378790826,65199628802152,105341667290136,151153294198652,
  201194843593766,253700083506404,306692682312708,358117467574304,405975617522400,448449838143370,
  484010221457090,511494956663874,530157678689778,539684916172904,540181953066844,532131968663610,
  516336156650956,493839705950098,465850752216650,433661299131446,398571665850198,361826820644196,
  324565307087582,287781125848768,252301522260460,218776753440484,187681765852140,159326964633478,
  133875914172700,111365885917708,91732754862168,74833965272070,60471108660882,48410872366598,
  38401631586114,30187362128262,23519782861858,18164576871052,13907513659406,10557533618218,
  7947009160708,5932165614126,4391690362932,3224710853618,2348581583884,1696891575860,
    1216001870444,
  864389105700,609617061202,426289754648,295522328074,203165202254,138167619120,93014288872,
  61808925532,40394719298,25950169572,16175158046,9566687264,5337934040,2707843344,945720206,
  229381830]
private def rkmC_w64_m4_s6_9 : List ℤ := rkmMapZZ [233350640,362680396,230446240,305844565,
  900592011,1601445027,1628217059,757600987,843672582,3065267242,4942214526,5281101244,3621077794,
  767379625,6941812021,12962120377,16372281487,14368901171,5360543341,10058868238,28873424434,
  44680478274,50254177382,38860886892,7125940248,41806551147,97721220183,143751711825,159025379125,
  125330401841,32948140169,112550125328,285803897682,443452213772,529159033480,486792962704,
  276081832926,110559212933,634347154873,1204324253915,1683962040219,1909215872243,1720244518497,
  1000665876735,282086280390,2042751305698,4059979397992,5981496419554,7354093268166,7682180562130,
  6507012692794,3496441205746,1463482808353,8194579742247,16179260969239,24552070987865,
  32135990610181,37522527235061,39187701661135,35635966032795,25552428983665,7947724839959,
  17720070936558,51462522534284,92725710705970,140404621745896,192909658363430,248273862292290,
  304290664123022,358670040991258,409193965158588,453861378311834,491008522301708,519396036869730,
  538258964747470,547320239319958,546766881433042,537198400123408,519553559713296,495021924317842,
  464952177703636,430761561334858,393854459870672,355553898148298,317048903405090,279357238833038,
  243306545081674,209528204474726,178462904187126,150377683904788,125387170051570,103479133280304,
  84541770945112,68390154325190,54789179020930,43475921160712,34176299424472,26618476179356,
  20544092612714,15714276200208,11913882063864,8953875443142,6671551251242,4928531429510,
  3610279924550,2622649714568,1889261119398,1349729369894,956364212912,671932609114,468054755868,
  323344753626,221174133756,149846524210,100493444470,66449443236,43265255280,27648560078,
  17089093440,10068358238,5629646816,2827867816,959686506,224408290]
private def rkmC_w64_m4_s6_10 : List ℤ := rkmMapZZ [600032040,1205587822,1123974916,517756528,
  791324173,2434269765,3531233287,3427280537,1597015201,2076508546,6357793806,9768857422,
  10281824666,6136271322,2639688533,14179287155,24941244113,29652537065,23826688567,5615540343,
  23338439582,55463494744,79714117254,83367085080,56018833288,4790485303,90304120411,179762096757,
  242623048719,245885241713,164431046109,8878275324,253046984462,517219543362,725450016266,
  790643947416,636913142650,224765961298,426349132291,1223546136073,2001665930923,2543831336133,
  2617859816137,2029213565519,677592732669,1392572854120,3959558267398,6620876689002,8825279191134,
  9939836626752,9347899544238,6565478009538,1356444884406,6166725273155,15479218863275,
  25629258367293,35278251070895,42796544234201,46407624117803,44362065052847,35122869975799,
  17541606385005,8999717181944,44493238894674,88270022998276,139028366735166,194920638897074,
  253688055058474,312830748145108,369791856060982,422138611435654,467725745740426,504824481404538,
  532210360043722,549207517772870,555686403358348,552024076758642,539032517891322,517865570824436,
  489913958770806,456699980859196,419777835300606,380646531579146,340681561186746,301084331097166,
  262850803283982,226759678183438,193373605668266,163053698986416,135982383993626,112191996524800,
  91594011061350,74009884856124,59199491289266,46884628400104,36770525797804,28562734649652,
  21978302508982,16754918846974,12656138845262,9473996958638,7028627724746,5168549837496,
  3767787214854,2722806161736,1950709315958,1385717763026,975908311548,681317064632,471574562826,
  323469498384,219712573156,147633378188,98284712142,64400378726,41414233658,26193347238,
  16030737520,9231235664,4919320868,2312430034,740302256]
private def hbN_w64_m4_s7a_p0 : List ℕ := [54326625688279,76770497993776,93952067358139,
  108403121287610,121105145409063,132561907160710,143072902087549,152833419577692,161979212754325,
  170609198568271,178798108504692,186604045832368,194073252239511,201243248822281,208144981819019,
  214804333440353,221243213391383,227480365147557,233531973148798,239412127903567,245133187658361,
  250706063440299,256140446435377,261444991355642,266627465784187,271694872912625,276653553247983,
  281509269534651,286267278159514,290932389581772,295509019782641,300001234314998,304412786214525,
  308747148787245,313007544095773,317196967814930,321318211007193,325373879272373,329366409648753,
  333298085580442,337171050214933,340987318253221,344748786540707,348457243558795,352114377953655,
  355721786218993,359280979633312,362793390538290,366260378033268,369683233150949,373063183570990,
  376401397920992,379698989708237,382957020920252,386176505327687,389358411519109,392503665693843,
  395613154236080,398687726090842,401728194960169,404735341335895,407709914383650,410652633691213,
  413564190892969,416445251181062,419296454712758,422118417922626,424911734747289,427676977769779,
  430414699289858,433125432326093,435809691554932,438467974191562,441100760816916,443708516154792,
  446291689802738,448850716920006,451386018875642,453898003859493,456387067458699,458853593202025,
  461297953074218,463720508002359,466121608316084,468501594183346,470860796023317,473199534897862,
  475518122882939,477816863421174,480096051656762,482355974753769,484596912198830,486819136089177,
  489022911406848,491208496279886,493376142231276,495526094416321,497658591849101,499773867618630,
  501872149095272,503953658127960,506018611232707,508067219772870,510099690131622,512116223877022,
  514117017920081,516102264666183,518072152160191,520026864225568,521966580597814,523891477052486,
  525801725528090,527697494244071,529578947814160,531446247355287,533299550592270,535139011958488,
  536964782692720,538777010932326,540575841802940]
private def hbN_w64_m4_s7a_p1 : List ℕ := [542361417504829,544133877396087,545893358072771,
  547639993446152,549373914817186,551095250948324,552804128132799,554500670261468,556184998887340,
  557857233287870,559517490525123,561165885503892,562802531027856,564427537853854,566041014744366,
  567643068518254,569233804099843,570813324566416,572381731194167,573939123502689,575485599298043,
  577021254714471,578546184254806,580060480829613,581564235795129,583057538990042,584540478771137,
  586013142047876,587475614315931,588927979689719,590370320933969,591802719494366,593225255527287,
  594638007928686,596041054362135,597434471286061,598818333980216,600192716571384,601557692058373,
  602913332336311,604259708220253,605596889468152,606924944803192,608243941935511,609553947583338,
  610855027493556,612147246461727,613430668351563,614705356113905,615971371805183,617228776605409,
  618477630835690,619717993975298,620949924678298,622173480789747,623388719361492,624595696667556,
  625794468219152,626985088779311,628167612377150,629342092321795,630508581215948,631667130969140,
  632817792810648,633960617302105,635095654349814,636222953216756,637342562534322,638454530313765,
  639558903957381,640655730269433,641745055466814,642826925189473,643901384510594,644968477946543,
  646028249466591,647080742502415,648125999957386,649164064215646,650194977150988,651218780135531,
  652235514048213,653245219283089,654247935757450,655243702919772,656232559757478,657214544804550,
  658189696148966,659158051439984,660119647895266,661074522307858,662022711053019,662964250094907,
  663899174993129,664827520909152,665749322612581,666664614487312,667573430537555,668475804393739,
  669371769318291,670261358211304,671144603616092,672021537724624,672892192382866,673756599096000,
  674614789033554,675466793034426,676312641611804,677152364958002,677985992949192,678813555150051,
  679635080818314,680450598909246,681260138080023,682063726694032,682861392825090,683653164261587,
  684439068510544,685219132801599,685993384090926]
private def hbN_w64_m4_s7a_p2 : List ℕ := [686761849065066,687524554144705,688281525488366,
  689032788996051,689778370312798,690518294832192,691252587699797,691981273816535,692704377842006,
  693421924197740,694133937070403,694840440414934,695541457957636,696237013199209,696927129417730,
  697611829671585,698291136802341,698965073437577,699633661993667,700296924678505,700954883494195,
  701607560239691,702254976513386,702897153715669,703534113051432,704165875532533,704792461980223,
  705413893027529,706030189121601,706641370526017,707247457323050,707848469415900,708444426530890,
  709035348219622,709621253861104,710202162663834,710778093667864,711349065746814,711915097609868,
  712476207803731,713032414714558,713583736569846,714130191440309,714671797241707,715208571736663,
  715740532536438,716267697102685,716790082749176,717307706643503,717820585808744,718328737125117,
  718832177331599,719330923027524,719824990674152,720314396596226,720799156983489,721279287892191,
  721754805246570,722225724840307,722692062337962,723153833276391,723611053066139,724063736992811,
  724511900218428,724955557782758,725394724604628,725829415483222,726259645099353,726685428016721,
  727106778683153,727523711431822,727936240482448,728344379942490,728748143808309,729147545966324,
  729542600194144,729933320161692,730319719432305,730701811463827,731079609609677,731453127119907,
  731822377142249,732187372723142,732548126808745,732904652245935,733256961783299,733605068072103,
  733948983667249,734288721028227,734624292520043,734955710414140,735282986889309,735606134032580,
  735925163840110,736240088218048,736550918983401,736857667864879,737160346503729,737458966454567,
  737753539186185,738044076082359,738330588442640,738613087483139,738891584337292,739166090056631,
  739436615611527,739703171891938,739965769708137,740224419791435,740479132794898,740729919294044,
  740976789787541,741219754697895,741458824372120,741694009082412,741925319026804,742152764329820,
  742376355043114,742596101146106,742812012546609]
private def hbN_w64_m4_s7a_p3 : List ℕ := [743024099081442,743232370517047,743436836550086,
  743637506808035,743834390849778,744027498166177,744216838180652,744402420249742,744584253663662,
  744762347646858,744936711358548,745107353893259,745274284281358,745437511489575,745597044421522,
  745752891918201,745905062758511,746053565659744,746198409278077,746339602209059,746477152988089,
  746611070090892,746741361933986,746868036875140,746991103213839,747110569191725,747226442993052,
  747338732745116,747447446518696,747552592328482,747654178133495,747752211837511,747846701289469,
  747937654283884,748025078561246,748108981808422,748189371659046,748266255693912,748339641441354,
  748409536377626,748475947927278,748538883463527,748598350308617,748654355734188,748706906961625,
  748756011162416,748801675458496,748843906922595,748882712578572,748918099401755,748950074319272,
  748978644210374,749003815906763,749025596192911,749043991806371,749059009438094,749070655732733,
  749078937288949,749083860659711,749085432352591,749083658830058,749078546509770,749070101764855,
  749058330924196,749043240272709,749024836051620,749003124458735,748978111648710,748949803733313,
  748918206781693,748883326820630,748845169834798,748803741767013,748759048518483,748711095949055,
  748659889877458,748605436081542,748547740298516,748486808225178,748422645518155,748355257794121,
  748284650630027,748210829563325,748133800092183,748053567675705,747970137734144,747883515649110,
  747793706763786,747700716383125,747604549774059,747505212165695,747402708749518,747297044679580,
  747188225072696,747076255008636,746961139530308,746842883643943,746721492319284,746596970489756,
  746469323052653,746338554869307,746204670765262,746067675530447,745927573919340,745784370651136,
  745638070409911,745488677844782,745336197570062,745180634165425,745021992176052,744860276112787,
  744695490452287,744527639637167,744356728076148,744182760144199,744005740182679,743825672499474,
  743642561369135,743456411033014,743267225699396]
private def hbN_w64_m4_s7a_p4 : List ℕ := [743075009543626,742879766708244,742681501303107,
  742480217405513,742275919060327,742068610280099,741858295045181,741644977303848,741428660972409,
  741209349935319,740987048045291,740761759123408,740533486959221,740302235310864,740068007905150,
  739830808437673,739590640572911,739347507944320,739101414154427,738852362774931,738600357346789,
  738345401380305,738087498355223,737826651720811,737562864895943,737296141269185,737026484198875,
  736753897013201,736478383010280,736199945458230,735918587595251,735634312629687,735347123740104,
  735057024075358,734764016754657,734468104867629,734169291474385,733867579605583,733562972262482,
  733255472417006,732945083011797,732631806960270,732315647146668,731996606426109,731674687624642,
  731349893539289,731022226938093,730691690560164,730358287115721,730022019286129,729682889723948,
  729340901052960,728996055868212,728648356736047,728297806194138,727944406751521,727588160888618,
  727229071057273,726867139680770,726502369153863,726134761842795,725764320085323,725391046190731,
  725014942439854,724636011085088,724254254350410,723869674431385,723482273495181,723092053680575,
  722699017097962,722303165829361,721904501928417,721503027420405,721098744302230,720691654542427,
  720281760081155,719869062830196,719453564672947,719035267464410,718614173031187,718190283171462,
  717763599654996,717334124223104,716901858588641,716466804435987,716028963421020,715588337171100,
  715144927285042,714698735333089,714249762856890,713798011369463,713343482355170,712886177269681,
  712426097539942,711963244564135,711497619711641,711029224322999,710558059709866,710084127154972,
  709607427912070,709127963205895,708645734232108,708160742157250,707672988118682,707182473224535,
  706689198553649,706193165155514,705694374050211,705192826228344,704688522650979,704181464249572,
  703671651925905,703159086552007,702643768970088,702125699992456,701604880401446,701081310949333,
  700554992358256,700025925320130,699494110496558]
private def hbN_w64_m4_s7a_p5 : List ℕ := [698959548518749,698422239987419,697882185472704,
  697339385514061,696793840620172,696245551268845,695694517906907,695140740950107,694584220783003,
  694024957758856,693462952199515,692898204395309,692330714604923,691760483055286,691187509941444,
  690611795426440,690033339641187,689452142684337,688868204622151,688281525488366,687692105284055,
  687099943977491,686505041504002,685907397765830,685307012631979,684703885938067,684098017486175,
  683489407044686,682878054348131,682263959097024,681647120957699,681027539562145,680405214507829,
  679780145357528,679152331639150,678521772845555,677888468434374,677252417827817,676613620412492,
  675972075539205,675327782522771,674680740641808,674030949138542,673378407218594,672723114050777,
  672065068766879,671404270461449,670740718191575,670074410976663,669405347798210,668733527599570,
  668058949285721,667381611723031,666701513739006,666018654122054,665333031621228,664644644945977,
  663953492765881,663259573710397,662562886368585,661863429288843,661161200978627,660456199904177,
  659748424490227,659037873119722,658324544133523,657608435830109,656889546465276,656167874251831,
  655443417359277,654716173913500,653986141996446,653253319645796,652517704854632,651779295571101,
  651038089698076,650294085092806,649547279566563,648797670884285,648045256764213,647290034877521,
  646532002847941,645771158251383,645007498615546,644241021419528,643471724093426,642699604017932,
  641924658523920,641146884892032,640366280352248,639582842083462,638796567213041,638007452816381,
  637215495916459,636420693483371,635623042433869,634822539630891,634019181883077,633212965944286,
  632403888513098,631591946232314,630777135688447,629959453411200,629138895872942,628315459488176,
  627489140612990,626659935544514,625827840520353,624992851718020,624154965254363,623314177184970,
  622470483503581,621623880141477,620774362966870,619921927784270,619066570333862,618208286290850,
  617347071264810,616482920799020,615615830369785]
private def hbN_w64_m4_s7a_p6 : List ℕ := [614745795385752,613872811187210,612996873045380,
  612117976161699,611236115667083,610351286621184,609463484011636,608572702753286,607678937687413,
  606782183580932,605882435125593,604979686937157,604073933554564,603165169439086,602253388973470,
  601338586461057,600420756124895,599499892106840,598575988466628,597649039180947,596719038142484,
  595785979158961,594849855952152,593910662156882,592968391320016,592023036899422,591074592262923,
  590123050687227,589168405356844,588210649362977,587249775702401,586285777276316,585318646889190,
  584348377247571,583374960958883,582398390530206,581418658367025,580435756771964,579449677943497,
  578460413974635,577467956851587,576472298452405,575473430545595,574471344788714,573466032726930,
  572457485791568,571445695298621,570430652447238,569412348318185,568390773872274,567365919948769,
  566337777263761,565306336408507,564271587847749,563233521917993,562192128825763,561147398645813,
  560099321319318,559047886652020,557993084312347,556934903829488,555873334591443,554808365843026,
  553739986683831,552668186066167,551592952792940,550514275515511,549432142731493,548346542782523,
  547257463851977,546164893962650,545068820974381,543969232581643,542866116311071,541759459518952,
  540649249388659,539535472928037,538418116966732,537297168153469,536172612953274,535044437644639,
  533912628316630,532777170865933,531638050993840,530495254203172,529348765795144,528198570866151,
  527044654304498,525887000787058,524725594775857,523560420514587,522391462025044,521218703103494,
  520042127316952,518861717999385,517677458247837,516489330918460,515297318622462,514101403721967,
  512901568325781,511697794285066,510490063188909,509278356359806,508062654849029,506842939431894,
  505619190602927,504391388570905,503159513253797,501923544273576,500683460950920,499439242299784,
  498190867021841,496938313500802,495681559796588,494420583639374,493155362423484,491885873201141,
  490612092676063,489333997196907,488051562750550]
private def hbN_w64_m4_s7a_p7 : List ℕ := [486764764955203,485473579053358,484177979904556,
  482877941977978,481573439344846,480264445670632,478950934207073,477632877783978,476310248800823,
  474983019218136,473651160548647,472314643848217,470973439706524,469627518237500,468276849069520,
  466921401335326,465561143661674,464196044158710,462826070409056,461451189456587,460071367794911,
  458686571355526,457296765495641,455901914985664,454501983996335,453096936085487,451686734184438,
  450271340583987,448850716920006,447424824158611,445993622580904,444557071767258,443115130581140,
  441667757152453,440214908860371,438756542315661,437292613342465,435823076959518,434347887360797,
  432866997895559,431380361047757,429887928414816,428389650685720,426885477618413,425375358016469,
  423859239705002,422337069505798,420808793211621,419274355559679,417733700204196,416186769688069,
  414633505413564,413073847612015,411507735312480,409935106309317,408355897128622,406770042993499,
  405177477788091,403578134020333,401971942783364,400358833715540,398738734958987,397111573116630,
  395477273207622,393835758621104,392186951068229,390530770532346,388867135217285,387195961493633,
  385517163842914,383830654799572,382136344890648,380434142573045,378723954168246,377005683794384,
  375279233295501,373544502167882,371801387483291,370049783808964,368289583124188,366520674733274,
  364742945174756,362956278126586,361160554307133,359355651371734,357541443804577,355717802805629,
  353884596172349,352041688175877,350188939431393,348326206762293,346453343057831,344570197123831,
  342676613526059,340772432425803,338857489407186,336931615295700,334994635967412,333046372148238,
  331086639202663,329115246911214,327131999235937,325136694073099,323129122992237,321109070960631,
  319076316052195,317030629139692,314971773569091,312899504814797,310813570114339,308713708081033,
  306599648292949,304471110856402,302327805942009,300169433291179,297995681690693,295806228412829,
  293600738618227,291378864718413,289140245694621]
private def hbN_w64_m4_s7a_p8 : List ℕ := [286884506369176,284611256625358,282320090571214,
  280010585642329,277682301638012,275334779684776,272967541120285,270580086290195,268171893249429,
  265742416358454,263291084763999,260817300752381,258320437962133,255799839440973,253254815530230,
  250684641557618,248088555316734,245465754308667,242815392717722,240136578089251,237428367672939,
  234689764389461,231919712371979,229117092026442,226280714545649,223409315801435,220501549526607,
  217555979683049,214571071894068,211545183796850,208476554143929,205363290449569,202203354936410,
  198994548487585,195734492247132,192420606433374,189050085831419,185619871305676,182126616512928,
  178566648789340,174935922914693,171229966101675,167443812085146,163571921549954,159608085269044,
  155545305126766,151375646525401,147090053285455,142678112690199,138127753211274,133424849727646,
  128552699092793,123491309876607,118216418860044,112698093654932,106898686340767,100769726714550,
  94246994678557,87242268099132,79628509240106,71210701993145,61660496081362,50337533014494,
  35588271769886]
private def hbN_w64_m4_p7a : List ℕ :=
  pCat hbN_w64_m4_s7a_p0 (pCat hbN_w64_m4_s7a_p1 (pCat hbN_w64_m4_s7a_p2 (pCat hbN_w64_m4_s7a_p3
    (pCat hbN_w64_m4_s7a_p4 (pCat hbN_w64_m4_s7a_p5 (pCat hbN_w64_m4_s7a_p6 (pCat
    hbN_w64_m4_s7a_p7 hbN_w64_m4_s7a_p8)))))))
private def rkmC_w64_m4_s7a_1 : List ℤ := rkmMapZZ [313003988,352343114,75622949,1003240289,
  1819217919,2113161069,1348586681,721111394,3151566952,4997560660,5230015306,2672461644,
    2216161951,
  8050955859,12400100825,12605587881,6661854357,4857134124,18879789000,30167446530,32188926990,
  20617729308,4882016527,38855020099,69761173183,83187048729,67180782891,16853779113,60483001452,
  144230060678,203977595508,208063720506,133813747004,20058421417,226198823611,430232599429,
  559240670951,541306907991,329978167269,73717114156,606891682416,1144803890848,1521139033836,
  1564531045858,1146593954838,229926484732,1094612787775,2597338776061,3931309874071,4687164239843,
  4478163089941,3037757551147,311327613833,3477563006740,7806902244334,11893037627084,
  14786153876070,15514026013810,13257147855748,7525906958184,1688836313235,13819119905711,
  27695470279411,41608334879225,53448287857043,60909897636999,61737917060119,53981241712529,
  36223338312659,7761895200477,31284910715368,79956872675168,136515918712390,198584289705522,
  263340712322208,327750725902652,388805432279976,443742493150580,490233851490820,526521794529946,
  551496383804148,564715832402676,566372902805920,557217235556730,538446573166846,511580394537416,
  478329440530402,440469770342996,399733844035770,357722577877558,315840723280716,275256004706072,
  236882197795730,201380858310410,169177313322744,140487407654104,115352880450588,93676098019894,
  75256092986752,59822519085788,47063914673394,36651636437896,28259351425038,21575530455918,
  16314059696770,12218847506398,9066013682054,6664657999568,4854781593788,3504359807290,
  2507130393958,1777671121372,1249190975024,870085645748,600549067216,410715431044,278374780690,
  186592747886,123712623586,80905838096,51960918524,32760254864,20098993004,11773887226,6633850266,
  3293959966,1372642710,424940014]
private def rkmC_w64_m4_s7a_2 : List ℤ := rkmMapZZ [248464284,948700854,1297176882,1311107412,
  300350052,1496003463,3193027131,4008383053,3045247389,16253315,4271814632,7937741774,9182294732,
  6465829836,858120099,10574193717,19036999475,21805650337,15173482585,1440893214,23734953454,
  43978162886,52309358706,40436389764,6108768728,44103769931,94703741153,124782036559,114182919405,
  52656549911,53185349832,177986368102,279775393144,311484488590,236894143706,46363484288,
  231758856551,528442182553,746548234085,784616358375,568571930299,83684332621,603606967160,
  1343109480222,1923320501370,2116021669406,1736720411480,709658498448,884072127091,2786869496403,
  4585383415529,5775214084309,5862087485231,4480796577155,1509912909815,2843854516852,
    8014195578974,
  13113422993066,17038750995580,18638628938052,16915067786572,11230750392236,1485014265822,
  11771813198869,27308456587109,43278185717589,57377782242929,67075859416495,69887522564015,
  63658953744503,46821912289361,18589477759687,20929191869588,70711166758942,128893723236976,
  192931684344136,259814793249654,326318869203986,389264381102654,445754205634258,493368468060124,
  530305859366012,555458998805754,568428065737068,569478051447310,559449693795248,539640055438074,
  511666598904544,477326645830928,438468464734758,396877928991092,354189266599218,311822274149278,
  270944047079694,232454639904684,196993144444534,164956513257988,136531102847532,111728552612806,
  90423731808870,72392528883842,57345323647806,44955669292046,34885165010074,26800568510504,
  20387651863484,15359744825460,11461836870052,8472996575294,6205652847400,4503471174454,
  3238510140734,2308147341464,1630281951650,1141289780502,791961328356,544450421720,370746993504,
  250109244268,166781519594,109939410596,71432132618,45588039714,28574660370,17405263104,
  10099679480,5555464910,2795933306,975288526,236911226]
private def rkmC_w64_m4_s7a_3 : List ℤ := rkmMapZZ [232641036,242244664,83445171,752455311,
  924641111,314070261,745902834,2127652868,2991276136,2392979256,438733916,2665145121,5702858717,
  7024246523,5024101901,333728530,7495540062,13738349794,15481620620,9872821204,2560570887,
  18518350311,31695690213,34683883717,22242474761,5108335744,40329584402,70534806400,80322878806,
  57965631158,2332319380,74737517595,148241416151,186425519305,161539924635,62154675281,
    97613444096,
  276081143984,411310454740,437201747768,308414515702,20801528212,375476675801,776151630593,
  1044112098771,1046286327261,696117697765,4667031270,943554807436,1902116349208,2593354954878,
  2727555061952,2093147499510,635124361018,1490369347387,3907612501079,6063444207437,7322945609017,
  7104439374317,5027083407127,1041877456813,4485232277916,10764214079300,16653669676358,
  20816285492646,21934027394572,18950611908874,11303422140442,897281475277,16775191404499,
  34698662363143,52403262102789,67209569128707,76309827825459,77087333439069,67422742835995,
  45951579343881,12239030550953,33146638753630,88667919208350,151949789347348,219992184778288,
  289431958679406,356825855554092,418923199881606,472900573510710,516540571029764,548343842656284,
  567568797785500,574208702202148,568913152506462,552868829179320,527658699066724,495111212668448,
  457155971112804,415696152217488,372504497107062,329145591379386,286928366084866,246882741844756,
  209759381608534,176047659514892,146004368915974,119691640463830,97017203853880,77774069551768,
  61677254118892,48397180611464,37584568113388,28891795553850,21988582073090,16570921576342,
  12367653589982,9142936658100,6695775375204,4858046371694,3492651464728,2488255208854,
  1756627272490,1229105902308,852211068372,585374563312,398337876512,268417492210,178744835550,
  117814895722,76605746070,48964384816,30800849354,18850054920,10973880370,6017966350,2979511410,
  1013223976,239249642]
private def rkmC_w64_m4_s7a_4 : List ℤ := rkmMapZZ [279576794,652706808,816545244,557062946,
  269293437,1361737099,2104689013,1746507691,32704208,2343889980,4702385022,5453587574,3179663952,
  1433515751,6991303251,11289634859,10943145265,4798049711,6001149238,17720006170,24831028466,
  22125103040,7294658062,16543188111,40740535085,54479177377,47274533239,15229111277,35036696008,
  87258103186,118894440872,108887244364,47867181298,55153008085,170432745267,254117472035,
  262091857497,165956633293,29537884948,279951834858,506634729734,616265497386,530983454330,
  220798462484,273399795103,834195762675,1287945321859,1447660564093,1170179393231,413549252233,
  724108641768,2000385394684,3064505651424,3534077966552,3096884057226,1613352249334,803693376975,
  3762350174909,6629294580131,8634554001435,9029538423661,7268438507257,3174530803645,
    2944849505692,
  10268278488432,17531642141412,23195352337224,25690713602178,23703093148130,16446476112702,
  3881555618728,13162881574931,32991522286057,53170261037281,70767596592073,82677764768957,
  85978678961635,78280956696651,58018143147229,24644182259793,21283632186532,78142436776408,
  143393767384348,213818779270368,285809853838308,355683992152404,419978856956416,475707654216968,
  520549235138856,552962118474034,572221147961746,578384800645828,572202305671188,554981090723884,
  528431225461890,494501380029638,455226004535264,412591215724138,368427283887456,324331741785476,
  281623839948302,241324304839200,204160567794692,170589271344548,140829313992040,114904038993690,
  92684380931556,73930529224980,58330194307862,45532115245194,35171146724190,26889554874076,
  20351336656532,15250458751130,11316733426898,8317186225072,6054874209058,4366602339442,
  3120142012852,2208993696404,1549548057958,1077097272404,741698055688,505842586054,341706207578,
  228493318130,151082430748,98713543794,63707566360,40174894860,24796458702,14891074846,8413082232,
  4357601424,2002439238,642863520]
private theorem rkmWC_w64_m4_s3_0 : bWinChk 25 100000000 128
    hbN_w64_m4_s3 0 rkmXsWin_w64_m4_s3_in
    18 rkmXsWin_w64_m4_s3_out 3514053480 = true := by decide +kernel
private theorem rkmWC_w64_m4_s4_0 : bWinChk 28 100000000 256
    hbN_w64_m4_s4 18 rkmXsWin_w64_m4_s4_in
    50 rkmC_w64_m4_s4_1 4832636334 = true := by decide +kernel
private theorem rkmWC_w64_m4_s4_1 : bWinChk 27 100000000 256
    hbN_w64_m4_s4 50 rkmC_w64_m4_s4_1
    89 rkmXsWin_w64_m4_s4_out 5377054265 = true := by decide +kernel
private theorem rkmWC_w64_m4_s5_0 : bWinChk 29 100000000 512
    hbN_w64_m4_s5 89 rkmXsWin_w64_m4_s5_in
    131 rkmC_w64_m4_s5_1 4901060879 = true := by decide +kernel
private theorem rkmWC_w64_m4_s5_1 : bWinChk 29 100000000 512
    hbN_w64_m4_s5 131 rkmC_w64_m4_s5_1
    173 rkmC_w64_m4_s5_2 6316995664 = true := by decide +kernel
private theorem rkmWC_w64_m4_s5_2 : bWinChk 29 100000000 512
    hbN_w64_m4_s5 173 rkmC_w64_m4_s5_2
    214 rkmC_w64_m4_s5_3 5710023474 = true := by decide +kernel
private theorem rkmWC_w64_m4_s5_3 : bWinChk 28 100000000 512
    hbN_w64_m4_s5 214 rkmC_w64_m4_s5_3
    252 rkmXsWin_w64_m4_s5_out 5515929921 = true := by decide +kernel
private theorem rkmWC_w64_m4_s6_0 : bWinChk 25 100000000 1024
    hbN_w64_m4_s6 252 rkmXsWin_w64_m4_s6_in
    283 rkmC_w64_m4_s6_1 4725396239 = true := by decide +kernel
private theorem rkmWC_w64_m4_s6_1 : bWinChk 24 100000000 1024
    hbN_w64_m4_s6 283 rkmC_w64_m4_s6_1
    316 rkmC_w64_m4_s6_2 4658137484 = true := by decide +kernel
private theorem rkmWC_w64_m4_s6_2 : bWinChk 24 100000000 1024
    hbN_w64_m4_s6 316 rkmC_w64_m4_s6_2
    349 rkmC_w64_m4_s6_3 4966749441 = true := by decide +kernel
private theorem rkmWC_w64_m4_s6_3 : bWinChk 23 100000000 1024
    hbN_w64_m4_s6 349 rkmC_w64_m4_s6_3
    377 rkmC_w64_m4_s6_4 4313979527 = true := by decide +kernel
private theorem rkmWC_w64_m4_s6_4 : bWinChk 22 100000000 1024
    hbN_w64_m4_s6 377 rkmC_w64_m4_s6_4
    405 rkmC_w64_m4_s6_5 4137858487 = true := by decide +kernel
private theorem rkmWC_w64_m4_s6_5 : bWinChk 22 100000000 1024
    hbN_w64_m4_s6 405 rkmC_w64_m4_s6_5
    435 rkmC_w64_m4_s6_6 4667956826 = true := by decide +kernel
private theorem rkmWC_w64_m4_s6_6 : bWinChk 21 100000000 1024
    hbN_w64_m4_s6 435 rkmC_w64_m4_s6_6
    459 rkmC_w64_m4_s6_7 4009257904 = true := by decide +kernel
private theorem rkmWC_w64_m4_s6_7 : bWinChk 21 100000000 1024
    hbN_w64_m4_s6 459 rkmC_w64_m4_s6_7
    484 rkmC_w64_m4_s6_8 4114536959 = true := by decide +kernel
private theorem rkmWC_w64_m4_s6_8 : bWinChk 21 100000000 1024
    hbN_w64_m4_s6 484 rkmC_w64_m4_s6_8
    507 rkmC_w64_m4_s6_9 3782142298 = true := by decide +kernel
private theorem rkmWC_w64_m4_s6_9 : bWinChk 20 100000000 1024
    hbN_w64_m4_s6 507 rkmC_w64_m4_s6_9
    532 rkmC_w64_m4_s6_10 3708805051 = true := by decide +kernel
private theorem rkmWC_w64_m4_s6_10 : bWinChk 20 100000000 1024
    hbN_w64_m4_s6 532 rkmC_w64_m4_s6_10
    552 rkmXsWin_w64_m4_s6_out 3536323483 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7a_0 : bWinChk 17 100000000 1024
    hbN_w64_m4_p7a 552 rkmXsWin_w64_m4_s7a_in
    572 rkmC_w64_m4_s7a_1 3168919766 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7a_1 : bWinChk 16 100000000 1024
    hbN_w64_m4_p7a 572 rkmC_w64_m4_s7a_1
    591 rkmC_w64_m4_s7a_2 2764685304 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7a_2 : bWinChk 16 100000000 1024
    hbN_w64_m4_p7a 591 rkmC_w64_m4_s7a_2
    606 rkmC_w64_m4_s7a_3 3125947693 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7a_3 : bWinChk 16 100000000 1024
    hbN_w64_m4_p7a 606 rkmC_w64_m4_s7a_3
    624 rkmC_w64_m4_s7a_4 2895100648 = true := by decide +kernel
private theorem rkmWC_w64_m4_s7a_4 : bWinChk 16 100000000 1024
    hbN_w64_m4_p7a 624 rkmC_w64_m4_s7a_4
    641 rkmXsWin_w64_m4_s7a_out 3016241703 = true := by decide +kernel
private theorem heqPack_w64_m4_t0 : rkmAllTrueF [
  muxIntListEq rkmHbWin_w64_m4_s0 (uON hbN_w64_m4_s0),
  muxIntListEq rkmHbWin_w64_m4_s1 (uON hbN_w64_m4_s1),
  muxIntListEq rkmHbWin_w64_m4_s2 (uON hbN_w64_m4_s2),
  muxIntListEq rkmHbWin_w64_m4_s3 (uON hbN_w64_m4_s3),
  muxIntListEq rkmHbWin_w64_m4_s4 (uON hbN_w64_m4_s4),
  muxIntListEq rkmHbWin_w64_m4_s5 (uON hbN_w64_m4_s5),
  muxIntListEq rkmHbWin_w64_m4_s6 (uON hbN_w64_m4_s6),
  muxIntListEq rkmHbWin_w64_m4_p7a (uON hbN_w64_m4_p7a),
  bWinChk 2 100000000 16
    hbN_w64_m4_s0 0 rkmXsWin_w64_m4_s0_in
    0 rkmXsWin_w64_m4_s0_out 54221171,
  bWinChk 6 100000000 32
    hbN_w64_m4_s1 0 rkmXsWin_w64_m4_s1_in
    0 rkmXsWin_w64_m4_s1_out 311624573,
  bWinChk 15 100000000 64
    hbN_w64_m4_s2 0 rkmXsWin_w64_m4_s2_in
    0 rkmXsWin_w64_m4_s2_out 893769763
  ] = true := by decide +kernel
private theorem itB_w64_m4_s0 :
    RkmWinIterSound 2 16 (uON hbN_w64_m4_s0) 0 rkmXsWin_w64_m4_s0_in
      0 rkmXsWin_w64_m4_s0_out 54221171 :=
  bWinChk_sound (rkmHd (rkmTl4 (rkmTl4 heqPack_w64_m4_t0)))
private theorem rkmWinIter_w64_m4_s0 :
    RkmWinIterSound 2 16 rkmHbWin_w64_m4_s0 0 rkmXsWin_w64_m4_s0_in
      0 rkmXsWin_w64_m4_s0_out 54221171 :=
  @rkmSubHb 2 16 0 0 54221171 rkmHbWin_w64_m4_s0 (uON hbN_w64_m4_s0)
    rkmXsWin_w64_m4_s0_in rkmXsWin_w64_m4_s0_out
    (rkmHd heqPack_w64_m4_t0) itB_w64_m4_s0
/-- Certified `w64_m4` seg `0` (`2` steps). -/
theorem rkmWinSegWalkSnd_w64_m4_s0 :
    RkmWinSegWalkSound 2 ⟨16, rkmHbWin_w64_m4_s0, 0, rkmXsWin_w64_m4_s0_in,
      0, rkmXsWin_w64_m4_s0_out, 54221171⟩ :=
  @rkmSegWalk_mk 2 16 0 0 54221171
    rkmHbWin_w64_m4_s0 rkmXsWin_w64_m4_s0_in rkmXsWin_w64_m4_s0_out
    (rkmw_buildHbFrom_length 16 1024 1346287500000 16 0)
    rfl
    rkmWinIter_w64_m4_s0
private theorem itB_w64_m4_s1 :
    RkmWinIterSound 6 32 (uON hbN_w64_m4_s1) 0 rkmXsWin_w64_m4_s1_in
      0 rkmXsWin_w64_m4_s1_out 311624573 :=
  bWinChk_sound (rkmHd (rkmTl (rkmTl4 (rkmTl4 heqPack_w64_m4_t0))))
private theorem rkmWinIter_w64_m4_s1 :
    RkmWinIterSound 6 32 rkmHbWin_w64_m4_s1 0 rkmXsWin_w64_m4_s1_in
      0 rkmXsWin_w64_m4_s1_out 311624573 :=
  @rkmSubHb 6 32 0 0 311624573 rkmHbWin_w64_m4_s1 (uON hbN_w64_m4_s1)
    rkmXsWin_w64_m4_s1_in rkmXsWin_w64_m4_s1_out
    (rkmHd (rkmTl heqPack_w64_m4_t0)) itB_w64_m4_s1
/-- Certified `w64_m4` seg `1` (`6` steps). -/
theorem rkmWinSegWalkSnd_w64_m4_s1 :
    RkmWinSegWalkSound 6 ⟨32, rkmHbWin_w64_m4_s1, 0, rkmXsWin_w64_m4_s1_in,
      0, rkmXsWin_w64_m4_s1_out, 311624573⟩ :=
  @rkmSegWalk_mk 6 32 0 0 311624573
    rkmHbWin_w64_m4_s1 rkmXsWin_w64_m4_s1_in rkmXsWin_w64_m4_s1_out
    (rkmw_buildHbFrom_length 32 1024 632130833333 32 0)
    rfl
    rkmWinIter_w64_m4_s1
private theorem itB_w64_m4_s2 :
    RkmWinIterSound 15 64 (uON hbN_w64_m4_s2) 0 rkmXsWin_w64_m4_s2_in
      0 rkmXsWin_w64_m4_s2_out 893769763 :=
  bWinChk_sound (rkmHd (rkmTl (rkmTl (rkmTl4 (rkmTl4 heqPack_w64_m4_t0)))))
private theorem rkmWinIter_w64_m4_s2 :
    RkmWinIterSound 15 64 rkmHbWin_w64_m4_s2 0 rkmXsWin_w64_m4_s2_in
      0 rkmXsWin_w64_m4_s2_out 893769763 :=
  @rkmSubHb 15 64 0 0 893769763 rkmHbWin_w64_m4_s2 (uON hbN_w64_m4_s2)
    rkmXsWin_w64_m4_s2_in rkmXsWin_w64_m4_s2_out
    (rkmHd (rkmTl (rkmTl heqPack_w64_m4_t0))) itB_w64_m4_s2
/-- Certified `w64_m4` seg `2` (`15` steps). -/
theorem rkmWinSegWalkSnd_w64_m4_s2 :
    RkmWinSegWalkSound 15 ⟨64, rkmHbWin_w64_m4_s2, 0, rkmXsWin_w64_m4_s2_in,
      0, rkmXsWin_w64_m4_s2_out, 893769763⟩ :=
  @rkmSegWalk_mk 15 64 0 0 893769763
    rkmHbWin_w64_m4_s2 rkmXsWin_w64_m4_s2_in rkmXsWin_w64_m4_s2_out
    (rkmw_buildHbFrom_length 64 1024 343696000000 64 0)
    rfl
    rkmWinIter_w64_m4_s2
private theorem itB_w64_m4_s3 :
    RkmWinIterSound 25 128 (uON hbN_w64_m4_s3) 0 rkmXsWin_w64_m4_s3_in
      18 rkmXsWin_w64_m4_s3_out 3514053480 :=
  bWinChk_sound rkmWC_w64_m4_s3_0
private theorem rkmWinIter_w64_m4_s3 :
    RkmWinIterSound 25 128 rkmHbWin_w64_m4_s3 0 rkmXsWin_w64_m4_s3_in
      18 rkmXsWin_w64_m4_s3_out 3514053480 :=
  @rkmSubHb 25 128 0 18 3514053480 rkmHbWin_w64_m4_s3 (uON hbN_w64_m4_s3)
    rkmXsWin_w64_m4_s3_in rkmXsWin_w64_m4_s3_out
    (rkmHd (rkmTl (rkmTl (rkmTl heqPack_w64_m4_t0)))) itB_w64_m4_s3
/-- Certified `w64_m4` seg `3` (`25` steps). -/
theorem rkmWinSegWalkSnd_w64_m4_s3 :
    RkmWinSegWalkSound 25 ⟨128, rkmHbWin_w64_m4_s3, 0, rkmXsWin_w64_m4_s3_in,
      18, rkmXsWin_w64_m4_s3_out, 3514053480⟩ :=
  @rkmSegWalk_mk 25 128 0 18 3514053480
    rkmHbWin_w64_m4_s3 rkmXsWin_w64_m4_s3_in rkmXsWin_w64_m4_s3_out
    (rkmw_buildHbFrom_length 128 1024 181682400000 128 0)
    rfl
    rkmWinIter_w64_m4_s3
private theorem itB_w64_m4_s4 :
    RkmWinIterSound 55 256 (uON hbN_w64_m4_s4) 18 rkmXsWin_w64_m4_s4_in
      89 rkmXsWin_w64_m4_s4_out 10209690599 :=
  rkmChS 55 10209690599 (bWinChk_sound rkmWC_w64_m4_s4_0) rkmWC_w64_m4_s4_1 rfl rfl
private theorem rkmWinIter_w64_m4_s4 :
    RkmWinIterSound 55 256 rkmHbWin_w64_m4_s4 18 rkmXsWin_w64_m4_s4_in
      89 rkmXsWin_w64_m4_s4_out 10209690599 :=
  @rkmSubHb 55 256 18 89 10209690599 rkmHbWin_w64_m4_s4 (uON hbN_w64_m4_s4)
    rkmXsWin_w64_m4_s4_in rkmXsWin_w64_m4_s4_out
    (rkmHd (rkmTl4 heqPack_w64_m4_t0)) itB_w64_m4_s4
/-- Certified `w64_m4` seg `4` (`55` steps). -/
theorem rkmWinSegWalkSnd_w64_m4_s4 :
    RkmWinSegWalkSound 55 ⟨256, rkmHbWin_w64_m4_s4, 18, rkmXsWin_w64_m4_s4_in,
      89, rkmXsWin_w64_m4_s4_out, 10209690599⟩ :=
  @rkmSegWalk_mk 55 256 18 89 10209690599
    rkmHbWin_w64_m4_s4 rkmXsWin_w64_m4_s4_in rkmXsWin_w64_m4_s4_out
    (rkmw_buildHbFrom_length 256 1024 95881890909 256 0)
    rfl
    rkmWinIter_w64_m4_s4
private theorem itB_w64_m4_s5 :
    RkmWinIterSound 115 512 (uON hbN_w64_m4_s5) 89 rkmXsWin_w64_m4_s5_in
      252 rkmXsWin_w64_m4_s5_out 22444009938 :=
  rkmChS 115 22444009938 (rkmChS 87 16928080017 (rkmChS 58 11218056543 (bWinChk_sound
    rkmWC_w64_m4_s5_0) rkmWC_w64_m4_s5_1 rfl rfl) rkmWC_w64_m4_s5_2 rfl rfl) rkmWC_w64_m4_s5_3
    rfl rfl
private theorem rkmWinIter_w64_m4_s5 :
    RkmWinIterSound 115 512 rkmHbWin_w64_m4_s5 89 rkmXsWin_w64_m4_s5_in
      252 rkmXsWin_w64_m4_s5_out 22444009938 :=
  @rkmSubHb 115 512 89 252 22444009938 rkmHbWin_w64_m4_s5 (uON hbN_w64_m4_s5)
    rkmXsWin_w64_m4_s5_in rkmXsWin_w64_m4_s5_out
    (rkmHd (rkmTl (rkmTl4 heqPack_w64_m4_t0))) itB_w64_m4_s5
/-- Certified `w64_m4` seg `5` (`115` steps). -/
theorem rkmWinSegWalkSnd_w64_m4_s5 :
    RkmWinSegWalkSound 115 ⟨512, rkmHbWin_w64_m4_s5, 89, rkmXsWin_w64_m4_s5_in,
      252, rkmXsWin_w64_m4_s5_out, 22444009938⟩ :=
  @rkmSegWalk_mk 115 512 89 252 22444009938
    rkmHbWin_w64_m4_s5 rkmXsWin_w64_m4_s5_in rkmXsWin_w64_m4_s5_out
    (rkmw_buildHbFrom_length 512 1024 51685843478 512 0)
    rfl
    rkmWinIter_w64_m4_s5
private theorem itB_w64_m4_s6 :
    RkmWinIterSound 243 1024 (uON hbN_w64_m4_s6) 252 rkmXsWin_w64_m4_s6_in
      552 rkmXsWin_w64_m4_s6_out 46621143699 :=
  rkmChS 243 46621143699 (rkmChS 223 43084820216 (rkmChS 203 39376015165 (rkmChS 182 35593872867
    (rkmChS 161 31479335908 (rkmChS 140 27470078004 (rkmChS 118 22802121178 (rkmChS 96
    18664262691 (rkmChS 73 14350283164 (rkmChS 49 9383533723 (bWinChk_sound rkmWC_w64_m4_s6_0)
    rkmWC_w64_m4_s6_1 rfl rfl) rkmWC_w64_m4_s6_2 rfl rfl) rkmWC_w64_m4_s6_3 rfl rfl)
    rkmWC_w64_m4_s6_4 rfl rfl) rkmWC_w64_m4_s6_5 rfl rfl) rkmWC_w64_m4_s6_6 rfl rfl)
    rkmWC_w64_m4_s6_7 rfl rfl) rkmWC_w64_m4_s6_8 rfl rfl) rkmWC_w64_m4_s6_9 rfl rfl)
    rkmWC_w64_m4_s6_10 rfl rfl
private theorem rkmWinIter_w64_m4_s6 :
    RkmWinIterSound 243 1024 rkmHbWin_w64_m4_s6 252 rkmXsWin_w64_m4_s6_in
      552 rkmXsWin_w64_m4_s6_out 46621143699 :=
  @rkmSubHb 243 1024 252 552 46621143699 rkmHbWin_w64_m4_s6 (uON hbN_w64_m4_s6)
    rkmXsWin_w64_m4_s6_in rkmXsWin_w64_m4_s6_out
    (rkmHd (rkmTl (rkmTl (rkmTl4 heqPack_w64_m4_t0)))) itB_w64_m4_s6
/-- Certified `w64_m4` seg `6` (`243` steps). -/
theorem rkmWinSegWalkSnd_w64_m4_s6 :
    RkmWinSegWalkSound 243 ⟨1024, rkmHbWin_w64_m4_s6, 252, rkmXsWin_w64_m4_s6_in,
      552, rkmXsWin_w64_m4_s6_out, 46621143699⟩ :=
  @rkmSegWalk_mk 243 1024 252 552 46621143699
    rkmHbWin_w64_m4_s6 rkmXsWin_w64_m4_s6_in rkmXsWin_w64_m4_s6_out
    (rkmw_buildHbFrom_length 1024 1024 29643724279 1024 0)
    rfl
    rkmWinIter_w64_m4_s6
private theorem itB_w64_m4_p7a :
    RkmWinIterSound 81 1024 (uON hbN_w64_m4_p7a) 552 rkmXsWin_w64_m4_s7a_in
      641 rkmXsWin_w64_m4_s7a_out 14970895114 :=
  rkmChS 81 14970895114 (rkmChS 65 11954653411 (rkmChS 49 9059552763 (rkmChS 33 5933605070
    (bWinChk_sound rkmWC_w64_m4_s7a_0) rkmWC_w64_m4_s7a_1 rfl rfl) rkmWC_w64_m4_s7a_2 rfl rfl)
    rkmWC_w64_m4_s7a_3 rfl rfl) rkmWC_w64_m4_s7a_4 rfl rfl
/-- Certified `w64_m4_s7a` partial walk (`81` substeps). -/
theorem rkmWinIterSnd_w64_m4_p7a :
    RkmWinIterSound 81 1024 rkmHbWin_w64_m4_p7a 552 rkmXsWin_w64_m4_s7a_in
      641 rkmXsWin_w64_m4_s7a_out 14970895114 :=
  @rkmSubHb 81 1024 552 641 14970895114 rkmHbWin_w64_m4_p7a (uON hbN_w64_m4_p7a)
    rkmXsWin_w64_m4_s7a_in rkmXsWin_w64_m4_s7a_out
    (rkmHd (rkmTl (rkmTl (rkmTl (rkmTl4 heqPack_w64_m4_t0))))) itB_w64_m4_p7a
/-- Cumulative `FindAllJohnsonRampKickMuxHiW64T02` lane witness. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T02 :
    @rkmWinIterSnd_w64_m4_p7a = @rkmWinIterSnd_w64_m4_p7a := rfl

end
end QuantumComputation.Specs.DickeSol
