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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi128T8

/-
# Caustic `r = 1024` Halo-16 Walk `w128` (`RkMuxHiW256WinT1`)

Certifies all eight segments (`s0..s7`) and anchor hit of the `w128` `r = 1024` halo-16 walk.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Generator list for `w128_s0`. -/
def rkmHbWin_w128_s0 : List ℤ := altBuildHbFrom 256 1024 96830113207 0 256
/-- Entry `rkmXsWin_w128_s0_in`. -/
def rkmXsWin_w128_s0_in : List ℤ := [rkmP 1000000000000000]
/-- Exit `rkmXsWin_w128_s0_out`. -/
def rkmXsWin_w128_s0_out : List ℤ := let p := rkmP; [p 110381099, p 360821057, p 664735553,
  p 1200472618, p 2003909938, p 3306870501, p 5568532148, p 9112939383, p 14720441411,
  p 23411223402, p 36704737697, p 56921715207, p 87064037719, p 131606064386, p 196470015209,
  p 289590069843, p 421740271507, p 606773265483, p 862765636707, p 1212417087128, p 1683985763109,
  p 2312287616667, p 3138915477542, p 4213248107999, p 5592369097994, p 7341117808369,
  p 9531647762146, p 12241828413148, p 15553991794806, p 19552027989877, p 24318363026227,
  p 29930096889376, p 36454086905406, p 43942505182864, p 52427112559166, p 61914391057809,
  p 72380732631553, p 83768139657840, p 95981827106190, p 108888170466291, p 122315378372966,
  p 136055500889184, p 149868531104905, p 163489087152548, p 176633884847649, p 189011849543735,
  p 200334399243416, p 210326674104588, p 218738942019166, p 225356468283294, p 230009232920522,
  p 232578662130779, p 233002880712079, p 231279215112788, p 227463513883078, p 221667826919503,
  p 214054390279607, p 204828649376556, p 194230007026498, p 182521497200969, p 169979658924194,
  p 156883358846186, p 143504575163835, p 130099201039675, p 116899836565463, p 104110437914147,
  p 91901928123245, p 80410886072611, p 69738579827676, p 59952534877135, p 51088913844006,
  p 43155524457835, p 36136448159815, p 29995657772218, p 24682097141508, p 20133632437025,
  p 16280996136090, p 13051724257552, p 10372437688138, p 8172045120008, p 6382871139800,
  p 4942447981694, p 3794128352579, p 2887519818550, p 2178628800131, p 1629625573542,
  p 1208519516624, p 888476202911, p 647647493971, p 468032674881, p 335285180964, p 238160902745,
  p 167653993980, p 117003793878, p 80856410537, p 55372247115, p 37601815382, p 25224872769,
  p 16730990298, p 10818089077, p 6820152849, p 4124866677, p 2316023525, p 1207443861, p 467067487,
  p 130298572]
/-- Generator list for `w128_s1`. -/
def rkmHbWin_w128_s1 : List ℤ := altBuildHbFrom 512 1024 51720290598 0 512
/-- Entry `rkmXsWin_w128_s1_in`. -/
def rkmXsWin_w128_s1_in : List ℤ := let p := rkmP; [p 110381099, p 360821057, p 664735553,
  p 1200472618, p 2003909938, p 3306870501, p 5568532148, p 9112939383, p 14720441411,
  p 23411223402, p 36704737697, p 56921715207, p 87064037719, p 131606064386, p 196470015209,
  p 289590069843, p 421740271507, p 606773265483, p 862765636707, p 1212417087128, p 1683985763109,
  p 2312287616667, p 3138915477542, p 4213248107999, p 5592369097994, p 7341117808369,
  p 9531647762146, p 12241828413148, p 15553991794806, p 19552027989877, p 24318363026227,
  p 29930096889376, p 36454086905406, p 43942505182864, p 52427112559166, p 61914391057809,
  p 72380732631553, p 83768139657840, p 95981827106190, p 108888170466291, p 122315378372966,
  p 136055500889184, p 149868531104905, p 163489087152548, p 176633884847649, p 189011849543735,
  p 200334399243416, p 210326674104588, p 218738942019166, p 225356468283294, p 230009232920522,
  p 232578662130779, p 233002880712079, p 231279215112788, p 227463513883078, p 221667826919503,
  p 214054390279607, p 204828649376556, p 194230007026498, p 182521497200969, p 169979658924194,
  p 156883358846186, p 143504575163835, p 130099201039675, p 116899836565463, p 104110437914147,
  p 91901928123245, p 80410886072611, p 69738579827676, p 59952534877135, p 51088913844006,
  p 43155524457835, p 36136448159815, p 29995657772218, p 24682097141508, p 20133632437025,
  p 16280996136090, p 13051724257552, p 10372437688138, p 8172045120008, p 6382871139800,
  p 4942447981694, p 3794128352579, p 2887519818550, p 2178628800131, p 1629625573542,
  p 1208519516624, p 888476202911, p 647647493971, p 468032674881, p 335285180964, p 238160902745,
  p 167653993980, p 117003793878, p 80856410537, p 55372247115, p 37601815382, p 25224872769,
  p 16730990298, p 10818089077, p 6820152849, p 4124866677, p 2316023525, p 1207443861, p 467067487,
  p 130298572]
/-- Exit `rkmXsWin_w128_s1_out`. -/
def rkmXsWin_w128_s1_out : List ℤ := let p := rkmP; [p 104796403, p 295389998, p 508019380,
  p 753762834, p 1210532064, p 1775078817, p 2700292786, p 3992008389, p 5867801816, p 8592499674,
  p 12402088138, p 17924874415, p 25573294813, p 36264707048, p 51066291399, p 71382089164,
  p 99195409122, p 136756942296, p 187332505297, p 254747765875, p 344017326039, p 461438111315,
  p 614569702721, p 812937945089, p 1067757047119, p 1392824617657, p 1804371976664,
  p 2321391879432, p 2966125868515, p 3763794439614, p 4743298473217, p 5936692349332,
  p 7379471500655, p 9110252311606, p 11170069805114, p 13602243391592, p 16451001002081,
  p 19760952140738, p 23575427950193, p 27934991844916, p 32876025208308, p 38428408980476,
  p 44614103306166, p 51444624487565, p 58919398627755, p 67023944406130, p 75727996654625,
  p 84984700340963, p 94729252032886, p 104879097943080, p 115333971857738, p 125976813732204,
  p 136675682716751, p 147285638029021, p 157652242048498, p 167614643163436, p 177009788134101,
  p 185676818574974, p 193461357001730, p 200220520103120, p 205826762262511, p 210172234141947,
  p 213172035682456, p 214766926909785, p 214925572807327, p 213645111986430, p 210951714114025,
  p 206899306954253, p 201568035405504, p 195061580508475, p 187503701075911, p 179034427513872,
  p 169805743539634, p 159976947311650, p 149710537813615, p 139167308779858, p 128502774789414,
  p 117863276348548, p 107382812516225, p 97181173857802, p 87361438596385, p 78009599308351,
  p 69193792088555, p 60964338665831, p 53354978439195, p 46383451051274, p 40053486112113,
  p 34356284567184, p 29272537646000, p 24774409801866, p 20827246385237, p 17391937388310,
  p 14426084702974, p 11885906019569, p 9727475656361, p 7907717055699, p 6385369561868,
  p 5121574782620, p 4080334396609, p 3229085195004, p 2538218147220, p 1981776914827,
  p 1536965317904, p 1183921789679, p 905948147974, p 688546138123, p 519774704336, p 389731847062,
  p 290255740756, p 214729212344, p 157722398517, p 114960642752, p 83231462841, p 59646305089,
  p 42354882652, p 29755476536, p 20546047018, p 13983416883, p 9263156723, p 5978992903,
  p 3655700206, p 2030063344, p 1015667206, p 369820541]
/-- Generator list for `w128_s2`. -/
def rkmHbWin_w128_s2 : List ℤ := altBuildHbFrom 1024 1024 29547445255 0 1024
/-- Entry `rkmXsWin_w128_s2_in`. -/
def rkmXsWin_w128_s2_in : List ℤ := let p := rkmP; [p 104796403, p 295389998, p 508019380,
  p 753762834, p 1210532064, p 1775078817, p 2700292786, p 3992008389, p 5867801816, p 8592499674,
  p 12402088138, p 17924874415, p 25573294813, p 36264707048, p 51066291399, p 71382089164,
  p 99195409122, p 136756942296, p 187332505297, p 254747765875, p 344017326039, p 461438111315,
  p 614569702721, p 812937945089, p 1067757047119, p 1392824617657, p 1804371976664,
  p 2321391879432, p 2966125868515, p 3763794439614, p 4743298473217, p 5936692349332,
  p 7379471500655, p 9110252311606, p 11170069805114, p 13602243391592, p 16451001002081,
  p 19760952140738, p 23575427950193, p 27934991844916, p 32876025208308, p 38428408980476,
  p 44614103306166, p 51444624487565, p 58919398627755, p 67023944406130, p 75727996654625,
  p 84984700340963, p 94729252032886, p 104879097943080, p 115333971857738, p 125976813732204,
  p 136675682716751, p 147285638029021, p 157652242048498, p 167614643163436, p 177009788134101,
  p 185676818574974, p 193461357001730, p 200220520103120, p 205826762262511, p 210172234141947,
  p 213172035682456, p 214766926909785, p 214925572807327, p 213645111986430, p 210951714114025,
  p 206899306954253, p 201568035405504, p 195061580508475, p 187503701075911, p 179034427513872,
  p 169805743539634, p 159976947311650, p 149710537813615, p 139167308779858, p 128502774789414,
  p 117863276348548, p 107382812516225, p 97181173857802, p 87361438596385, p 78009599308351,
  p 69193792088555, p 60964338665831, p 53354978439195, p 46383451051274, p 40053486112113,
  p 34356284567184, p 29272537646000, p 24774409801866, p 20827246385237, p 17391937388310,
  p 14426084702974, p 11885906019569, p 9727475656361, p 7907717055699, p 6385369561868,
  p 5121574782620, p 4080334396609, p 3229085195004, p 2538218147220, p 1981776914827,
  p 1536965317904, p 1183921789679, p 905948147974, p 688546138123, p 519774704336, p 389731847062,
  p 290255740756, p 214729212344, p 157722398517, p 114960642752, p 83231462841, p 59646305089,
  p 42354882652, p 29755476536, p 20546047018, p 13983416883, p 9263156723, p 5978992903,
  p 3655700206, p 2030063344, p 1015667206, p 369820541]
/-- Exit `rkmXsWin_w128_s2_out`. -/
def rkmXsWin_w128_s2_out : List ℤ := let p := rkmP; [p 182117304, p 349240900, p 590124324,
  p 1040238265, p 1673923117, p 2792067769, p 4441708441, p 6980619342, p 10874327206,
  p 16585003117, p 25162088491, p 37582804292, p 55579860436, p 81375150594, p 117780918055,
  p 168855793028, p 239453297713, p 336155638321, p 467204708840, p 642887163850, p 876133009993,
  p 1182536257144, p 1581178346466, p 2094560153605, p 2749310462065, p 3576054868070,
  p 4609745684698, p 5889692854767, p 7459188011976, p 9365215973779, p 11657770492753,
  p 14388511147332, p 17609952825328, p 21373494701713, p 25727730348899, p 30716405661581,
  p 36375733990530, p 42732458197486, p 49800756469601, p 57580411265515, p 66054499935206,
  p 75187190182800, p 84923144993126, p 95185962291495, p 105878670439249, p 116884290105508,
  p 128067332770162, p 139276339410349, p 150346877481951, p 161105401436032, p 171373966498567,
  p 180974724109692, p 189735495391635, p 197494629046885, p 204106205566342, p 209444595295150,
  p 213408072163208, p 215922808104770, p 216944325144736, p 216459172869761, p 214485294393359,
  p 211070581447157, p 206291678727622, p 200250591870660, p 193071502240079, p 184896521855953,
  p 175881034305879, p 166189004643064, p 155988138187420, p 145445195590149, p 134721953902167,
  p 123971046701652, p 113333265841780, p 102934521728917, p 92884280795347, p 83274743101859,
  p 74179558709773, p 65654757370193, p 57739037599600, p 50455000764663, p 43810862220690,
  p 37801627508401, p 32411609305751, p 27616041275817, p 23383140494392, p 19675856243748,
  p 16453635164428, p 13674073123026, p 11294081810432, p 9270952857856, p 7563733944243,
  p 6133242444598, p 4943081050605, p 3959781898037, p 3152837315475, p 2495297083209,
  p 1962990932017, p 1534935963873, p 1193046783700, p 921758333245, p 707904901372, p 540403139189,
  p 410004125680, p 309265289097, p 231733925597, p 172511937894, p 127593394785, p 93612094530,
  p 68186566994, p 49204995002, p 35162232541, p 24809021560, p 17204874831, p 11733603319,
  p 7786438022, p 4908848279, p 2998604097, p 1620822729, p 737400669, p 247929742]
/-- Generator list for `w128_s3`. -/
def rkmHbWin_w128_s3 : List ℤ := altBuildHbFrom 1536 1024 22125714285 0 1024
/-- Entry `rkmXsWin_w128_s3_in`. -/
def rkmXsWin_w128_s3_in : List ℤ := let p := rkmP; [p 182117304, p 349240900, p 590124324,
  p 1040238265, p 1673923117, p 2792067769, p 4441708441, p 6980619342, p 10874327206,
  p 16585003117, p 25162088491, p 37582804292, p 55579860436, p 81375150594, p 117780918055,
  p 168855793028, p 239453297713, p 336155638321, p 467204708840, p 642887163850, p 876133009993,
  p 1182536257144, p 1581178346466, p 2094560153605, p 2749310462065, p 3576054868070,
  p 4609745684698, p 5889692854767, p 7459188011976, p 9365215973779, p 11657770492753,
  p 14388511147332, p 17609952825328, p 21373494701713, p 25727730348899, p 30716405661581,
  p 36375733990530, p 42732458197486, p 49800756469601, p 57580411265515, p 66054499935206,
  p 75187190182800, p 84923144993126, p 95185962291495, p 105878670439249, p 116884290105508,
  p 128067332770162, p 139276339410349, p 150346877481951, p 161105401436032, p 171373966498567,
  p 180974724109692, p 189735495391635, p 197494629046885, p 204106205566342, p 209444595295150,
  p 213408072163208, p 215922808104770, p 216944325144736, p 216459172869761, p 214485294393359,
  p 211070581447157, p 206291678727622, p 200250591870660, p 193071502240079, p 184896521855953,
  p 175881034305879, p 166189004643064, p 155988138187420, p 145445195590149, p 134721953902167,
  p 123971046701652, p 113333265841780, p 102934521728917, p 92884280795347, p 83274743101859,
  p 74179558709773, p 65654757370193, p 57739037599600, p 50455000764663, p 43810862220690,
  p 37801627508401, p 32411609305751, p 27616041275817, p 23383140494392, p 19675856243748,
  p 16453635164428, p 13674073123026, p 11294081810432, p 9270952857856, p 7563733944243,
  p 6133242444598, p 4943081050605, p 3959781898037, p 3152837315475, p 2495297083209,
  p 1962990932017, p 1534935963873, p 1193046783700, p 921758333245, p 707904901372, p 540403139189,
  p 410004125680, p 309265289097, p 231733925597, p 172511937894, p 127593394785, p 93612094530,
  p 68186566994, p 49204995002, p 35162232541, p 24809021560, p 17204874831, p 11733603319,
  p 7786438022, p 4908848279, p 2998604097, p 1620822729, p 737400669, p 247929742]
/-- Exit `rkmXsWin_w128_s3_out`. -/
def rkmXsWin_w128_s3_out : List ℤ := let p := rkmP; let n := rkmN; [n 109923774, p 3132009,
  p 313106352, p 698503999, p 1183592275, p 1729744781, p 1923268689, p 1544379131, n 112643209,
  n 3792689667, n 10236711335, n 20233124994, n 33846738635, n 49942486151, n 65559189607,
  n 74403564721, n 65189719175, n 20645854197, p 85345998793, p 289424055782, p 640426347270,
  p 1201424251625, p 2050697059033, p 3281595532931, p 5001991716805, p 7331827744440,
  p 10399168697848, p 14335344277281, p 19267982013833, p 25312961164670, p 32566605441726,
  p 41095930758977, p 50930503837339, p 62054961215581, p 74402851760634, p 87853111968103,
  p 102229310152960, p 117301770643245, p 132792713097669, p 148385190252467, p 163733600555991,
  p 178477173592293, p 192254645044080, p 204719176964800, p 215553035945262, p 224481508697354,
  p 231283956065264, p 235802519943741, p 237948221933592, p 237702661920590, p 235116810414764,
  p 230307205110909, p 223447984206302, p 214761908128967, p 204509372901340, p 192976334603210,
  p 180462001686283, p 167267599631212, p 153685554041260, p 139990032506274, p 126429975881026,
  p 113223302030247, p 100553071876640, p 88566362608576, p 77373803272870, p 67051261356755,
  p 57642466424750, p 49162612481313, p 41602083146284, p 34931196432426, p 29104625747409,
  p 24065073192479, p 19747638562991, p 16083334492340, p 13001538916632, p 10432615606658,
  p 8309989766841, p 6571059629444, p 5158449688713, p 4020374018970, p 3111062305556,
  p 2390243271725, p 1823358504458, p 1381177280037, p 1038829707564, p 775745981948,
  p 575226747684, p 423508113959, p 309463348558, p 224431313268, p 161525633723, p 115306134653,
  p 81456146444, p 57021762944, p 39446460124, p 26811164491, p 17918482482, p 11730810364,
  p 7379107751, p 4374326972, p 2414262212, p 1167994799, p 377688508]
/-- Kick mask `w128` seg `4`. -/
def rkmMkHi_w128_s4 : List Bool := List.replicate 984 false ++ [
  true, false, false, false, false, false, false, false, true, false, true, true, true, false, true,
  true, true, true, true, false, false, false, true, true, true, false, false, false, true, true,
  true, true, false, false, false, false, false, false, false, false, true]
/-- Kick mask `w128` seg `5`. -/
def rkmMkHi_w128_s5 : List Bool := List.replicate 974 false ++ [
  true, false, false, false, true, false, false, true, false, true, false, true, false, false,
  false, true, false, true, false, false, false, false, true, false, true, true, false, false,
  false, true, false, true, true, false, true, false, true, false, true, false, true, true, false,
  true, true, true, true]
/-- Kick mask `w128` seg `6`. -/
def rkmMkHi_w128_s6 : List Bool := List.replicate 971 false ++ [
  true, false, false, false, true, true, false, true, false, true, false, false, false, true, false,
  false, false, false, false, true, false, false, false, false, false, true, false, true, false,
  false, true, false, true, false, false, false, false, false, true, false, false, false, true,
  true, true, true, true, true, true, true, true, true]
/-- Kick-mask schedule for `w128` `r = 1024`. -/
def rkmMasksHi_w128_r1024 : List (List Bool) := [
  [], [], [], [], rkmMkHi_w128_s4, rkmMkHi_w128_s5, rkmMkHi_w128_s6, []]
/-- Certified `rowLo12` vector for `w128` `r = 1024`. -/
def rkmRowHi_w128_r1024 : List ℕ := List.replicate 948 0 ++ [
  96, 530, 324, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 184126, 0, 522993, 101240, 862813, 4592770, 119237, 67401, 546842, 11497220, 791489,
  146047, 917230, 148686124, 832653, 2474307, 45009129, 44862, 4097622, 2464432, 139173112, 30685,
  2039845, 850334, 231227834, 835884883, 30851601, 346583563, 154749208, 198686790, 6547415240,
  292539032, 306422914, 10659475441, 179332914, 13446, 839934161, 2219019, 13331075299, 8703057554,
  4430759475, 952009972681]

end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ :=
  Nat.casesOn (Nat.add 1 x) xs fun v => List.casesOn xs [v] fun h t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uOfNatHb : List ℕ → List ℤ | [] => [] | n :: ns => Int.ofNat n :: uOfNatHb ns
private def bSpineN : List ℕ → List ℕ
  | [] => [] | x :: xs => List.casesOn (bSpineN xs) [x] fun h t => x :: h :: t
private theorem bSpineN_eq : ∀ (xs : List ℕ), bSpineN xs = xs
  | [] => rfl | x :: xs => by dsimp only [bSpineN]; rw [bSpineN_eq xs]; cases xs <;> rfl
private def bDropN : ℕ → List ℕ → List ℕ
  | 0, xs => xs | _ + 1, [] => [] | k + 1, _ :: xs => bDropN k xs
private theorem bDropN_eq : ∀ (k : ℕ) (bns : List ℕ),
    uOfNatHb (bDropN k bns) = rkmDropInts k (uOfNatHb bns)
  | 0, [] => rfl | 0, _ :: _ => rfl | _ + 1, [] => rfl | k + 1, _ :: xs => bDropN_eq k xs
private def bConsZ (x : ℤ) (xs : List ℤ) : List ℤ :=
  Int.casesOn x (fun v => List.casesOn xs [Int.ofNat v] fun h t => Int.ofNat v :: h :: t)
    fun v => List.casesOn xs [Int.negSucc v] fun h t => Int.negSucc v :: h :: t
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
  | [] => [] | u :: us => bConsZ (rkmForcedSubNatNat u z) (bDec z us)
private theorem bDec_nil (z : ℕ) : bDec z [] = [] := rfl
private theorem bDec_cons (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by rw [bDec, bConsZ_eq, bSub_eq]
private theorem bZero_eq (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bMul0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZero_eq]; rfl
private def bEnc1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k => match Nat.sub z (Nat.add k 1) with | 0 => none | w + 1 => some (Nat.add w 1)
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
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
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
    have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    dsimp only; rw [hm]; dsimp only [zTdiv]; rw [bNeg_eq]
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
    dsimp only [rkmForcedIntAdd]; rw [bOfNatF_eq, Nat.add_eq]; simp [Int.ofNat_eq_natCast]
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bNegSuccF_eq, Nat.add_eq, Nat.add_eq, Int.negSucc_eq]; omega
private theorem bAddCons_eq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bForcedAdd_eq]; cases a + b <;> cases xs <;> rfl
private theorem bCastAdd (a b : ℕ) : ((a + b : ℕ) : ℤ) = (a : ℤ) + (b : ℤ) := by push_cast; ring
private theorem bPosAdd_eq (v z q : ℕ) :
    ((v + q : ℕ) : ℤ) - (z : ℤ) = ((v : ℤ) - (z : ℤ)) + Int.ofNat q := by
  rw [Int.ofNat_eq_natCast, bCastAdd]; ring
private theorem bPosSub_eq (v z q : ℕ) (hv : 0 < v - q) :
    ((v - q : ℕ) : ℤ) - (z : ℤ) = ((v : ℤ) - (z : ℤ)) + -(q : ℤ) := by
  have hq : v = (v - q) + q := by omega
  have hqz : (v : ℤ) = (((v - q) + q : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hq
  rw [hqz, bCastAdd (v - q) q]; ring
private theorem bCasesAdd1 (x a : ℕ) (f : ℕ → ℕ) :
    Nat.casesOn (motive := fun _ => ℕ) (Nat.add 1 x) a f = f x := by rw [n1a x]
private theorem bCasesSub (p q a : ℕ) (f : ℕ → ℕ) :
    Nat.casesOn (motive := fun _ => ℕ) (Nat.sub q p) a f =
      (match q - p with | 0 => a | k + 1 => f k) := by rw [Nat.sub_eq]; cases q - p <;> rfl
private def bStepVal (v P Q d : ℕ) : ℕ :=
  Nat.casesOn (motive := fun _ => ℕ) (Nat.add 1 P) 0 fun pF =>
    Nat.casesOn (motive := fun _ => ℕ) (Nat.add 1 Q) 0 fun qF =>
      Nat.casesOn (motive := fun _ => ℕ) (Nat.sub qF pF) (Nat.add v (Nat.div (Nat.sub pF qF) d))
        fun k => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  unfold bStepVal at hv ⊢; rw [bCasesAdd1, bCasesAdd1, bCasesSub] at hv ⊢
  revert hv; cases h : Q - P with
  | zero =>
    intro _; dsimp only; simp only [Nat.sub_eq, Nat.add_eq, ndiv]
    have hm : (P : ℤ) - (Q : ℤ) = Int.ofNat (P - Q) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; dsimp only [zTdiv]; exact bPosAdd_eq v z ((P - Q) / d)
  | succ k =>
    intro hv; dsimp only at hv ⊢; simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢
    have hm : (P : ℤ) - (Q : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTdiv]; exact bPosSub_eq v z ((k + 1) / d) hv
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
  | [] => true | x :: xs => cond (Nat.ble x 0) false (bAllPos xs)
private theorem bAllPos_cons {x : ℕ} {xs : List ℕ} (h : bAllPos (x :: xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private theorem bAllPos_uCons {x : ℕ} {xs : List ℕ} (h : bAllPos (uConsNat x xs) = true) :
    0 < x ∧ bAllPos xs = true := by rw [uConsNat_eq] at h; exact bAllPos_cons h
private def bHeadOr (z : ℕ) (cs : List ℕ) : ℕ := List.casesOn cs z fun x _ => x
private def bTailN (xs : List ℕ) : List ℕ := List.casesOn xs [] fun _ t => t
private theorem bHeadOr_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHeadOr z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; dsimp only; rw [bDec_nil, bZero_eq]
  | c :: cs => by unfold bHeadOr; dsimp only; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl | x :: xs => by unfold bTailN; dsimp only; rw [bDec_cons]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs => List.casesOn bns
    (uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
      (bSlide z d rem 0 z [] (bTailN vs) (bTailN cs)))
    fun b bR => List.casesOn vs
      (List.casesOn cs
        (uConsNat (bCellVal z d b0 c0 b z z) (bSlide z d rem b z bR [] []))
        fun c cT => uConsNat (bCellVal z d b0 c0 b z (bHeadOr z cT)) (bSlide z d rem b c bR [] cT))
      fun v vT => List.casesOn cs
        (uConsNat (bCellVal z d b0 c0 b v z) (bSlide z d rem b z bR vT []))
        fun c cT => uConsNat (bCellVal z d b0 c0 b v (bHeadOr z cT)) (bSlide z d rem b c bR vT cT)
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
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq] at h; revert h
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
    | none => none | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL bns vNext
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
private def fIterN (k mL cL : ℕ) (bns : List ℕ) (v : List ℤ) : List ℤ :=
  let z := 100000000000000000
  match bEnc z v with
  | none => muxUltraIterFullT16Rkm k mL cL (uOfNatHb bns) v
  | some vns => match bIter z k mL cL bns vns with
    | none => muxUltraIterFullT16Rkm k mL cL (uOfNatHb bns) v | some out => bDec z out
private theorem fIterN_eq (k mL cL : ℕ) (bns : List ℕ) (v : List ℤ) :
    fIterN k mL cL bns v = muxUltraIterFullT16Rkm k mL cL (uOfNatHb bns) v := by
  unfold fIterN; dsimp only; cases hv : bEnc 100000000000000000 v with
  | none => rfl
  | some vns => dsimp only; cases hi : bIter 100000000000000000 k mL cL bns vns with
    | none => rfl
    | some out =>
      dsimp only; rw [bIter_sound 100000000000000000 k mL cL bns vns out hi,
        bEnc_sound 100000000000000000 v vns hv]
private def bWinStepN (thr d : ℕ) (bns : List ℕ) (off : ℕ) (xs : List ℤ)
    (dropAcc : ℕ) : ℕ × List ℤ × ℕ :=
  fN (Nat.sub off 16) fun sLo => fN (Nat.sub off sLo) fun padL =>
    fN (Nat.sub (Nat.add d 1) sLo) fun remMax => fL (bDropN sLo bns) fun bnsSl =>
      fL (rkmPrependZeros padL xs) fun vecSl => fN (altIntLen vecSl) fun curLen =>
        fL (fIterN 1 remMax curLen bnsSl vecSl) fun rawSl => rkmTrimWin thr sLo rawSl dropAcc
private theorem bWinStepN_eq (thr d : ℕ) (bns : List ℕ) (off : ℕ) (xs : List ℤ) (dropAcc : ℕ) :
    bWinStepN thr d bns off xs dropAcc =
      muxWinStepT16 thr d (uOfNatHb bns) off xs dropAcc := by
  unfold bWinStepN muxWinStepT16; dsimp only [fN, fL]
  simp only [rkmb_forceNat_eq, rkmb_forceList_eq, fIterN_eq, bDropN_eq]
private def bWinIterN : ℕ → ℕ → ℕ → List ℕ → ℕ → List ℤ → ℕ → ℕ × List ℤ × ℕ
  | 0, _, _, _, off, xs, dropAcc => (off, xs, dropAcc)
  | k + 1, thr, d, bns, off, xs, dropAcc =>
    match bWinStepN thr d bns off xs dropAcc with
    | (o1, x1, d1) => bWinIterN k thr d bns o1 x1 d1
private theorem bWinIterN_eq :
    ∀ (k thr d : ℕ) (bns : List ℕ) (off : ℕ) (xs : List ℤ) (dropAcc : ℕ),
      bWinIterN k thr d bns off xs dropAcc =
        muxWinIterT16 k thr d (uOfNatHb bns) off xs dropAcc
  | 0, _, _, _, _, _, _ => rfl
  | k + 1, thr, d, bns, off, xs, dropAcc => by
    unfold bWinIterN muxWinIterT16; rw [bWinStepN_eq]
    rcases muxWinStepT16 thr d (uOfNatHb bns) off xs dropAcc with ⟨o1, x1, d1⟩
    exact bWinIterN_eq k thr d bns o1 x1 d1
private def bNatEq (a b : ℕ) : Bool := Bool.and (Nat.ble a b) (Nat.ble b a)
private theorem bNatEq_eq_true {a b : ℕ} (h : bNatEq a b = true) : a = b := by
  unfold bNatEq at h; rw [Bool.and_eq_true, rkmw_nat_ble_eq_true, rkmw_nat_ble_eq_true] at h
  omega
private def wSlChk (steps thr d : ℕ) (bns : List ℕ) (offIn : ℕ) (xsIn : List ℤ)
    (offOut : ℕ) (xsOut : List ℤ) (dropExp : ℕ) : Bool :=
  fL (bSpineN bns) fun bnsF => fL xsIn fun inF => fL xsOut fun outF =>
    match bWinIterN steps thr d bnsF offIn inF 0 with
    | (oRes, xRes, dRes) =>
      Bool.and (bNatEq oRes offOut) (Bool.and (muxIntListEq xRes outF) (bNatEq dRes dropExp))
private theorem wSlChk_sound {steps thr d offIn offOut dropExp : ℕ}
    {bns : List ℕ} {xsIn xsOut : List ℤ}
    (h : wSlChk steps thr d bns offIn xsIn offOut xsOut dropExp = true) :
    RkmWinIterSound steps d (uOfNatHb bns) offIn xsIn offOut xsOut dropExp := by
  unfold wSlChk at h; dsimp only [fL] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, bSpineN_eq, bWinIterN_eq] at h
  rcases hres : muxWinIterT16 steps thr d (uOfNatHb bns) offIn xsIn 0 with ⟨oRes, xRes, dRes⟩
  rw [hres] at h; simp only [Bool.and_eq_true] at h; rcases h with ⟨ho, hx, hd⟩
  have ho' := bNatEq_eq_true ho; have hd' := bNatEq_eq_true hd; subst ho'; subst hd'
  have h2 : muxWinIterT16HiChk steps thr 0 d (uOfNatHb bns) offIn xsIn
      oRes xsOut dRes = true := by
    unfold muxWinIterT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, hres]
    simp only [Bool.and_eq_true, rkmw_nat_beq_eq_true]; exact ⟨trivial, hx, trivial⟩
  exact muxWinIterT16HiChk_sound h2
private theorem rkmSubstHbN {k d o0 o2 dT : ℕ} {bns : List ℕ} {hbW x0 x2 : List ℤ}
    (hhb : muxIntListEq (uOfNatHb bns) hbW = true)
    (h : RkmWinIterSound k d (uOfNatHb bns) o0 x0 o2 x2 dT) :
    RkmWinIterSound k d hbW o0 x0 o2 x2 dT := by rw [← muxIntListEq_eq_true.mp hhb]; exact h
private theorem rkmChS (kT dT : ℕ) {k1 k2 d o0 o1 o2 d1 d2 : ℕ}
    {bns : List ℕ} {x0 x1 x2 : List ℤ}
    (h1 : RkmWinIterSound k1 d (uOfNatHb bns) o0 x0 o1 x1 d1)
    (h2 : wSlChk k2 100000000 d bns o1 x1 o2 x2 d2 = true)
    (hk : k1 + k2 = kT) (hd : d1 + d2 = dT) :
    RkmWinIterSound kT d (uOfNatHb bns) o0 x0 o2 x2 dT :=
  rkmChainWinIterT16 hk hd (muxIntListEq_eq_true.mpr rfl) rfl
    (muxIntListEq_eq_true.mpr rfl) h1 (wSlChk_sound h2)
private def rkmCatN : List (List ℕ) → List ℕ | [] => [] | ws :: wss => ws ++ rkmCatN wss
private def pzig : List ℕ → List ℤ
  | [] => [] | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2) | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCat : List (List ℕ) → List ℤ | [] => [] | ws :: wss => pzig ws ++ pzigCat wss
private theorem rkmWP0 {a : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: s) = true) : a = true := (rkmAllTrueF_cons h).1
private theorem rkmSegWalk_mk {nSub d offIn offOut dropSeg : ℕ}
    {hb xsIn xsOut : List ℤ} (hhb : hb.length = d)
    (hble : Nat.ble (Nat.add offIn (altIntLen xsIn)) (Nat.add d 1) = true)
    (hiter : RkmWinIterSound nSub d hb offIn xsIn offOut xsOut dropSeg) :
    RkmWinSegWalkSound nSub ⟨d, hb, offIn, xsIn, offOut, xsOut, dropSeg⟩ := by
  simp only [rkmw_nat_ble_eq_true, rkmw_altIntLen_eq, Nat.add_eq] at hble
  obtain ⟨hout, hbd⟩ := hiter hhb hble; exact ⟨hhb, hble, hout, hbd⟩
private theorem rkmWP1 {a b : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: s) = true) : b = true := rkmWP0 (rkmAllTrueF_cons h).2
private theorem rkmWP2 {a b c : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: s) = true) : c = true := rkmWP1 (rkmAllTrueF_cons h).2
private theorem rkmWP3 {a b c d : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: s) = true) : d = true := rkmWP2 (rkmAllTrueF_cons h).2
private theorem rkmWP4 {a b c d e : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: e :: s) = true) : e = true :=
  rkmWP3 (rkmAllTrueF_cons h).2
private theorem rkmWT5 {a b c d e : Bool} {s : List Bool}
    (h : rkmAllTrueF (a :: b :: c :: d :: e :: s) = true) : rkmAllTrueF s = true :=
  (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons (rkmAllTrueF_cons
    (rkmAllTrueF_cons h).2).2).2).2).2
private def rkmHbN_w128_s0 : List ℕ := rkmCatN
  [
   [99154035923968,139882485405983,170900513971522,196853691158783,219546133854314,
    239905394278757,258483811271705,275642118284884,291631468258896,306635147095097,
    320791837277469,334209524989947,346974278081513,359156034416934,370812558907378,
    381992231638167,392736063596411,403079186663154,413051976478849,422680913137872,
    431989250931866,440997546555094,449724080740154,458185198512859,466395586502902,
    474368501001732,482115957070186,489648886542488,496977270969328,504110254201270,
    511056238304791,517822965736305,524417590110845,530846737446049,537116559405859,
    543232779787804,549200735275187,555025411297673,560711473700797,566263296809189,
    571684988374128,576980411818949,582153206132393,587206803707524,592144446380283,
    596969199885336,601683966916426,606291498952737,610794406991132,615195171305709,
    619496150340495,623699588827703,627807625212549,631822298455755,635745554276416,
    639579250890506,643325164294008,646984993134064,650560363206732,654052831615753,
    657463890622984,660794971217970,664047446431218,667222634413284,670321801299496,
    673346163878222,676296892078805,679175111293767,681981904548477,684718314530253,
    687385345487777,689983965010684,692515105698349,694979666726043,697378515315968,
    699712488119999,701982392520404,704189007854267,706333086566880,708415355298945,
    710436515911997,712397246456174,714298202084055,716140015914067,717923299846649,
    719648645336121,721316624121017,722927788915378,724482674063381,725981796159441,
    727425654635827,728814732319638,730149495960889,731430396733310,732657870709353,
    733832339310820,734954209736380,736023875367215,737041716151895,738008098971546,
    738923377986291,739787894963857,740601979591229,741365949770117,742080111896996,
    742744761128394,743360181632094,743926646824828,744444419597039,744913752525230,
    745334888072384,745708058776914,746033487430558,746311387245615,746541962011884,
    746725406243646,746861905316992,746951635597796,746994764560585,746991450898555,
    746941844624960,746846087166059,746704311445816,746516641962516,746283194857433,
    746004077975681,745679390919367,745309225093124],
   [744893663742115,744432781982558,743926646824828,743375317189155,742778843913936,
    742137269756660,741450629387432,740718949375044,739942248165571,739120536053404,
    738253815144644,737342079312767,736385314146423,735383496889261,734336596371601,
    733244572933805,732107378341133,730924955689895,729697239304645,728424154626180,
    727105618090046,725741536995264,724331809362937,722876323784381,721374959258397,
    719827585017261,718234060340992,716594234359397,714907945841385,713175022970984,
    711395283109450,709568532542826,707694566214254,705773167440274,703804107610326,
    701787145868570,699722028777094,697608489959523,695446249723927,693235014663884,
    690974477236454,688664315315697,686304191720318,683893753713845,681432632475683,
    678920442541214,676356781208977,673741227912817,671073343556696,668352669809696,
    665578728358505,662751020114486,659869024372147,656932197915582,653939974069131,
    650891761688197,647786944085771,644624877889839,641404891826361,638126285422072,
    634788327620748,631390255306026,627931271723156,624410544791325,620827205297357,
    617180344960646,613469014358137,609692220696995,605848925421271,601938041637403,
    597958431341696,593908902431052,589788205476067,585595030233169,581328001869753,
    576985676873055,572566538609986,568068992500972,563491360766163,558831876696936,
    554088678399334,549259801948865,544343173887645,539336602985118,534237771172128,
    529044223544763,523753357318674,518362409595995,512868443785083,507268334487164,
    501558750632876,495736136614351,489796691113584,483736343273471,477550725791873,
    471235144438295,464784543393600,458193465690524,451456007880247,444565767859296,
    437515784550296,430298467824226,422905516660246,415327823033496,407555358362265,
    399577038478844,391380561935096,382952214902613,374276633814857,365336513982960,
    356112248333078,346581474600612,336718500895639,326493567112362,315871880867985,
    304812337583437,293265788068529,281172641048000,268459458831561,255033974920670,
    240777534422783,225533111135518,209085252461269,191124100634621,171174607883200,
    148438005390181,121358691694650,85925800703467]]
private def rkmC_w128_s0_1 : List ℤ := pzigCat
  [
   [126494772090,569699073324,1809772716182,4682460301338,10465705568988,20869791544480,
    37895158223526,63544648178958,99420891826760,146283647131078,203670042169712,269681042888534,
    341007442946118,413215738306218,481253941649400,540086060100560,585337422248806,
    613832767811090,623940455353166,615676577767962,590577449591836,551385548535890,
    501622382377324,445129589155664,385647782531136,326484863275676,270300207314210,
    219007245382118,173777157796952,135120719360742,103014868324860,77048432319990,
    56563531909072,40777771174232,28881416450716,20105157944808,13761667897064,9265268263998,
    6137918477388,4002409640034,2569681259448,1624894641896,1012340304002,621604499878,
    376104342866,224523915462,132120171934,76517953792,43681063102,24461400452,13246789730,
    6970723038,3292571960,1329385586,405942356]]
private def rkmC_w128_s0_2 : List ℤ := pzigCat
  [
   [404165486,1136766552,2502103320,5329467754,10742105256,21176748472,40445370678,74918304736,
    134736133606,236053324970,402857824898,670608618590,1089660829928,1730040120980,
    2685895524282,4080536598144,6070304244144,8848412617904,12645288624536,17726830774724,
    24389129965616,32948907191140,43727277901268,57031210531466,73130316081258,92229678478040,
    114441730479094,139760678793040,168039165681386,198971594374598,232087847465192,
    266754691833158,302191618435978,337497805383570,371689012678732,403744055789554,
    432657098296152,457489973764512,477424474195850,491807109836404,500184032016820,
    502325283352882,498232603680376,488135255391646,472471495089798,451857718114750,
    427051178001626,398904644046260,368320383178498,336205322003418,303429552380840,
    270792460463358,238995100216332,208622990092646,180136522113384,153868920203722,
    130032575662904,108729070688590,89964508800828,73666008295594,59699229043370,47886472472884,
    38021741851852,29885498073884,23255735465002,17917131755772,13668175319848,10324721026834,
    7723358284546,5721605799424,4197924879376,3050722289868,2195930499402,1565833761282,
    1106031616410,773918826962,536549156246,368443109462,250761468506,169023074938,112848847386,
    74596972430,48650665514,31368454140,19780256918,12221989860,7291666950,4066243218,2121124656,
    826310220,233122886]]
private def rkmHbN_w128_s1 : List ℕ := rkmCatN
  [
   [74898981287494,105767981627361,129348714019842,149139509322014,166497568762793,
    182120003040962,196421543501956,209672807812069,222062041915499,233726505392661,
    244769967777248,255273163625225,265300388894282,274903848947367,284126629731908,
    293004790434197,301568875797097,309845033555401,317855856207462,325621025992703,
    333157816579706,340481488577502,347605605126911,354542286480701,361302417409057,
    367895817703004,374331383503826,380617205342757,386760667421354,392768531656310,
    398647009255533,404401822017057,410038255100888,415561202681988,420975207625575,
    426284496115671,431493008001069,436604423489702,441622186715306,446549526613604,
    451389475474755,456144885481085,460818443491677,465412684296115,469930002527127,
    474372663394621,478742812380844,483042484017203,487273609847074,491438025665200,
    495537478112571,499573630695708,503548069290716,507462307185113,511317789704119,
    515115898462602,518857955279136,522545225784490,526178922753288,529760209184411,
    533290201152981,536769970454347,540200547058365,543582921390377,546918046453676,
    550206839806726,553450185407157,556648935333362,559803911393512,562915906630881,
    565985686733564,569013991355916,572001535358402,574949009971947,577857083892352,
    580726404309848,583557597878446,586351271629341,589108013832284,591828394808499,
    594512967698457,597162269187537,599776820192372,602357126510463,604903679435444,
    607416956340196,609897421229841,612345525266520,614761707267679,617146394179497,
    619500001526961,621822933841978,624115585070824,626378338962152,628611569436668,
    630815640939537,632990908776494,635137719434574,637256410888319,639347312892254,
    641410747260386,643447028133418,645456462234341,647439349113012,649395981380297,
    651326644932317,653231619165311,655111177181581,656965585986983,658795106680376,
    660599994635424,662380499675139,664136866239501,665869333546499,667578135746904,
    669263502073067,670925656982028,672564820293193,674181207320832,675775029001640,
    677346492017578,678895798914201,680423148214687,681928734529750,683412748663615,
    684875377716224,686316805181848,687737211044244],
   [689136771868512,690515660889785,691874048098891,693212100325108,694529981316129,
    695827851815357,697105869636632,698364189736501,699602964284114,700822342728859,
    702022471865814,703203495899090,704365556503180,705508792882348,706633341828169,
    707739337775265,708826912855321,709896196949436,710947317738872,711980400754262,
    712995569423334,713992945117200,714972647195270,715934793048823,716879498143310,
    717806876059407,718717038532875,719610095493268,720486155101526,721345323786493,
    722187706280391,723013405653298,723822523346646,724615159205791,725391411511665,
    726151377011560,726895150949059,727622827093144,728334497766514,729030253873129,
    729710184925017,730374379068345,731022923108809,731655902536333,732273401549121,
    732875503077065,733462288804546,734033839192629,734590233500680,735131549807425,
    735657865031457,736169254951220,736665794224467,737147556407235,737614613972321,
    738067038327293,738504899832046,738928267815903,739337210594300,739731795485032,
    740112088824106,740478155981187,740830061374663,741167868486328,741491639875706,
    741801437194009,742097321197761,742379351762070,742647587893584,742902087743114,
    743142908617951,743370106993882,743583738526902,743783858064635,743970519657486,
    744143776569497,744303681288955,744450285538720,744583640286308,744703795753721,
    744810801427029,744904706065717,744985557711801,745053403698705,745108290659931,
    745150264537498,745179370590170,745195653401486,745199156887567,745189924304740,
    745167998256959,745133420703030,745086232963658,745026475728301,744954189061849,
    744869412411123,744772184611200,744662543891567,744540527882117,744406173618961,
    744259517550101,744100595540927,743929442879569,743746094282090,743550583897530,
    743342945312802,743123211557442,742891415108217,742647587893584,742391761298023,
    742123966166218,741844232807112,741552590997825,741249069987441,740933698500664,
    740606504741343,740267516395875,739916760636480,739554264124347,739180053012668,
    738794152949535,738396589080732,737987386052396,737566568013567,737134158618615,
    736690181029552,736234657918233,735767611468436],
   [735289063377830,734799034859831,734297546645340,733784618984379,733260271647604,
    732724523927709,732177394640730,731618902127218,731049064253322,730467898411748,
    729875421522615,729271650034193,728656599923545,728030286697041,727392725390777,
    726743930570875,726083916333672,725412696305808,724730283644189,724036691035845,
    723331930697682,722616014376106,721888953346550,721150758412875,720401439906664,
    719641007686394,718869471136500,718086839166312,717293120208881,716488322219683,
    715672452675203,714845518571396,714007526422028,713158482256886,712298391619875,
    711427259566972,710545090664062,709651888984642,708747658107386,707832401113587,
    706906120584451,705968818598261,705020496727397,704061156035218,703090797072790,
    702109419875478,701117023959380,700113608317613,699099171416440,698073711191242,
    697037225042334,695989709830600,694931161872984,693861576937791,692780950239824,
    691689276435341,690586549616828,689472763307593,688347910456162,687211983430491,
    686064974011970,684906873389233,683737672151756,682557360283243,681365927154799,
    680163361517875,678949651496987,677724784582206,676488747621400,675241526812237,
    673983107693934,672713475138747,671432613343196,670140505819017,668837135383836,
    667522484151552,666196533522430,664859264172883,663510656044949,662150688335441,
    660779339484771,659396587165429,658002408270121,656596778899534,655179674349740,
    653751069099214,652310936795459,650859250241222,649395981380297,647921101282888,
    646434580130537,644936387200584,643426490850157,641904858499673,640371456615827,
    638826250694071,637269205240541,635700283753438,634119448703822,632526661515817,
    630921882546202,629305071063357,627676185225557,626035182058581,624382017432612,
    622716646038407,621039021362713,619349095662894,617646819940740,615932143915442,
    614205015995684,612465383250833,610713191381184,608948384687226,607170906037903,
    605380696837809,603577696993299,601761844877459,599933077293891,598091329439277,
    596236534864661,594368625435403,592487531289749,590593180795965,588685500507965,
    586764415119389,584829847416046,582881718226662],
   [580919946371867,578944448611333,576955139588990,574951931776237,572934735413060,
    570903458446952,568858006469561,566798282650939,564724187671296,562635619650144,
    560532474072703,558414643713450,556282018556672,554134485713882,551971929337943,
    549794230533748,547601267265286,545392914258909,543169042902627,540929521141212,
    538674213366913,536402980305559,534115678897795,531812162175222,529492279131157,
    527155874585727,524802789045003,522432858553847,520045914542125,517641783663926,
    515220287629394,512781243028750,510324461148080,507849747776391,505356903003441,
    502845721007804,500315989834577,497767491162125,495200000057180,492613284717599,
    490007106201992,487381218145427,484735366460293,482069289021397,479382715334258,
    476675366185490,473946953274090,471197178822340,468425735164940,465632304314856,
    462816557504265,459978154698836,457116744083422,454231961517095,451323429955268,
    448390758836432,445433543430848,442451364148266,439443785801476,436410356822225,
    433350608425658,430264053719128,427150186750760,424008481492753,420838390753840,
    417639345014820,414410751180384,411151991239799,407862420828172,404541367679139,
    401188129958811,397801974469660,394382134711712,390927808786983,387438157131378,
    383912300056391,380349315080764,376748234029748,373108039876782,369427663299070,
    365705978914766,361941801165057,358133879799342,354280894915746,350381451502281,
    346434073415828,342437196726551,338389162344090,334288207828505,330132458273100,
    325919916127253,321648449804726,317315780895509,312919469766183,308456899293520,
    303925256426842,299321511214142,294642392852225,289884362228019,285043580301720,
    280115871535407,275096681384056,269981026626663,264763437006249,259437886244799,
    253997709969069,248435507378014,242743022533733,236910999865303,230929006690346,
    224785213058983,218466115665217,211956187412257,205237426594592,198288768143997,
    191085301561220,183597211789637,175788312706923,167613963603035,159018018185894,
    149928192889862,140248720995213,129848051430175,118536768056173,106024123214886,
    91820632903411,74971803705256,53013272633533]]
private def rkmC_w128_s1_1 : List ℤ := pzigCat
  [
   [217068530,367888852,867903274,1427646628,2392136570,3876650666,6005032918,9493886226,
    14531057616,22223160056,33688101222,50468668404,75167616950,110510719300,161070545602,
    232479987942,332322202260,470945938772,660964842458,919385755412,1267108846806,1730431842012,
    2342152897220,3141417457848,4176313235928,5502899100636,7187333811848,9305469473616,
    11943029782954,15195850358778,19168231495760,23972309507840,29725262341098,36546698645974,
    44554797880284,53861874893198,64569302808822,76761512565948,90500462349642,105818567206676,
    122713478775324,141142117037852,161015659765780,182197116129056,204498088781706,
    227679782216226,251454785097920,275490911700992,299418649932470,322838827238628,
    345334071046080,366480258491230,385859882802532,403076157617168,417765476589976,
    429611389994368,438355125999316,443805169828044,445844590111760,444434482209852,
    439616079649792,431507878859070,420301419696058,406253923875626,389677886339314,
    370930516773344,350400262273822,328494323290952,305625251650180,282198120495910,
    258600025457178,235189406326006,212288856467040,190178723613930,169093297897652,
    149219600509294,130696588874742,113617788765662,98033757057940,83956770211404,71365877033960,
    60212057647720,50423993451802,41913719103514,34581178344148,28320126407528,23020902709278,
    18574741589668,14876646396922,11826504110258,9332344361012,7309819728006,5683334737384,
    4386297777818,3360257070984,2555399021306,1928856400960,1445188108066,1074897997288,
    793476127576,581502344038,422888506542,305362689290,218884166650,155591395176,109742110426,
    76532777502,52909221068,36102998390,24248572822,16021807400,10138000502,6197189700,
    3404810904,1615722020,579363840]]
private def rkmC_w128_s1_2 : List ℤ := pzigCat
  [
   [254454356,563957610,945372414,1599218830,2347914634,3672441614,5601562254,8397991984,
    12667064302,18759088912,27689490916,40395540642,58435420530,83984193046,119529347280,
    169071856898,237185783796,330196354050,456071236510,624993587224,849886218940,1146806996190,
    1535560723638,2040625270810,2691098734076,3522090514834,4575006035798,5897847444458,
    7546441970794,9583517015700,12079963325570,15113875686232,18769602220826,23137951750332,
    28313054041380,34391646457478,41469956760758,49640171268138,58988154324644,69587984035174,
    81498652841494,94759211953000,109384177531858,125359790981686,142639221788824,
    161140504066560,180743238964978,201287944095120,222576413792474,244372227287858,
    266405230913074,288375146733516,309958222026904,330814658322872,350596763003798,
    368959421636652,385568780353842,400113365967062,412313329145184,421929090136918,
    428770021254148,432699686106118,433641433105782,431579940832920,426561899046590,
    418694820897520,408142222327908,395119107173694,379883652060826,362729454722024,
    343976172148044,323959067720584,303020346402304,281498483841626,259720450817408,
    237993429931524,216598166934642,195784748028840,175767743080528,156725193982912,
    138796906813858,122085391754790,106657995298016,92548563637794,79761989079786,68276789971220,
    58050070872274,49021614684530,41117498010012,34255064802004,28345184025900,23296627637416,
    19018111991918,15420541872000,12419406017940,9934858027212,7893948318348,6230042820396,
    4883656831980,3802553874972,2940672909514,2258979083134,1723582812850,1306260316210,
    983414255264,735242189814,546125152194,402757401938,295035678344,214614793308,154885734734,
    111053879154,78809456850,55505149610,38593856984,26407874488,17794894026,11485596552,
    7181130998,4033966848,1954430648,712729512]]
private def rkmC_w128_s1_3 : List ℤ := pzigCat
  [
   [372102858,708886818,1045965162,1803016894,2723963248,4150459032,6297474438,9218082272,
    13614953312,19716674562,28504932432,40925438440,58286188824,82654969998,116046976740,
    161970794942,224420517232,308657917748,421627338532,571651939142,769909079214,1029512419952,
    1367027200792,1802662075290,2360375907326,3069397427694,3963517796032,5082792732348,
    6473170158432,8186909969942,10283429651754,12828022004666,15892831329068,19555195225480,
    23897276508414,29004841974178,34964496113156,41862785799548,49782302848276,58799589721882,
    68981350958914,80380319331230,93032575134190,106952365451402,122129678193030,138526057100764,
    156071883406974,174664947296302,194167981509722,214409901327330,235185605155402,
    256258893113376,277366107439992,298220064553018,318517423310856,337944333742944,
    356185439451324,372931746441976,387888906626330,400786804442544,411386309368998,
    419488093665784,424937813143820,427631259123498,427518137463802,424602537853016,
    418944250673232,410655335727294,399897297850298,386875696681398,371832980194132,
    355042382324428,336798065262522,317408241624364,297185404563154,276438793132362,
    255466761468042,234549732271602,213945024114634,193881886035368,174558665964872,
    156140462029048,138758897917986,122511887640158,107465395781626,93655634303024,
    81091110029588,69757178676140,59618414649150,50622970232674,42706365078708,35794305100062,
    29806779323114,24659999950140,20269906567286,16553558537302,13430914828998,10826889697070,
    8671139014192,6899746783324,5454634204992,4284220598002,3343325611012,2592082101072,
    1996737723108,1528078306654,1161866441172,877800792106,658765702036,491242219842,
    363736143770,267568592168,195526159154,141834890202,102239322862,72909303018,51512514322,
    35834168544,24450755736,16364902624,10463301276,6457608504,3576199638,1707091104,614095584]]
private def rkmC_w128_s1_4 : List ℤ := pzigCat
  [
   [458583674,848126618,1345342064,2255088762,3218845590,4903229176,7117155658,10495658156,
    15312538374,22041332108,31729502310,45197218530,64108441938,90139512768,125844540782,
    174526538104,240376273550,328873386594,446815056710,602998671932,808156366426,1075897094060,
    1422542727294,1868152059558,2436889878036,3157104690042,4062855419718,5193126140414,
    6593297028516,8315016108966,10415862362256,12960441742528,16018790774766,19666816064978,
    23984795348502,29056010157514,34965530278620,41797315352256,49632736612314,58546455215936,
    68603917716418,79857728880338,92343331963246,106076564002514,121048795089112,137224543157190,
    154538210215052,172891961187190,192155046534960,212162399559448,232716796842220,
    253589766014806,274525305822476,295244715710592,315451514772708,334839207481418,
    353097553927892,369921728962324,385020253928832,398123032047524,408990290128990,
    417418718985062,423248936764456,426369552821662,426721115915164,424298374488458,
    419149394254990,411375150445738,401125111907506,388593363250482,374012218085668,
    357644630016738,339777361274546,320711479449598,300755121085382,280214531239214,
    259386697295420,238553157754852,217973183384378,197880283773338,178477553298984,
    159936165994122,142394291508218,125956565293736,110696178637466,96655575260826,
    83850209333294,72271081426854,61888125158338,52654393986454,44508574911850,37379746697830,
    31189684407192,25856333487308,21296476585842,17427190088180,14168753942776,11444911905860,
    9184845623974,7323433091234,5801379132034,4566088184212,3570486929260,2773943213926,
    2141119438408,1641841269364,1250913002034,946762855228,712017434350,531963456892,
    394814026160,291138402404,213084090424,154914083724,111644449114,79753388284,56392145776,
    39252097140,26934303566,17939101266,11594060476,7122786470,4015524852,2075151384,788994236,
    215797804]]
private def rkmHbN_w128_s2 : List ℕ := rkmCatN
  [
   [60513167882240,85494969925597,104607170593322,120671766421420,134782996149332,
    147502622390087,159164690956843,169987066303680,180121226274480,189677568871217,
    198739516952687,207371944835686,215626493745956,223545074766909,231162262059092,
    238506978098360,245603711311097,252473415586735,259134187747566,265601786529567,
    271890036182991,278011144590463,283975957052120,289794160966590,295474452550000,
    301024673864254,306451926376133,311762665783837,316962781757295,322057665427968,
    327052266854478,331951144227246,336758506220000,341478248620805,346113986160389,
    350669080286340,355146663497588,359549660746433,363880808329215,368142670617042,
    372337654921293,376468024742179,380535911610528,384543325701353,388492165371605,
    392384225752612,396221206509405,400004718863703,403736291964320,407417378677701,
    411049360861927,414633554179476,418171212497182,421663531915922,425111654467485,
    428516671511642,431879626862682,435201519671309,438483307084951,441725906706978,
    444930198873141,448097028761590,451227208351130,454321518240880,457380709343137,
    460405504460136,463396599754267,466354666120475,469280350468673,472174276923292,
    475037047946449,477869245390583,480671431485934,483444149767713,486187925947439,
    488903268732487,491590670597578,494250608511621,496883544623023,499489926906350,
    502070189772960,504624754648057,507154030516386,509658414438635,512138292040452,
    514594037975836,517026016366522,519434581218871,521820076819664,524182838112083,
    526523191053097,528841452953350,531137932800602,533412931567686,535666742505874,
    537899651424500,540111936957609,542303870818380,544475718041977,546627737217500,
    548760180709593,550873294870307,552967320241702,555042491749707,557099038889683,
    559137185904122,561157151952889,563159151276381,565143393351976,567110083044089,
    569059420748158,570991602528874,572906820252906,574805261716418,576687110767598,
    578552547424460,580401747988126,582234885151808,584052128105674,585853642637811,
    587639591231440,589410133158555,591165424570167,592905618583269,594630865364702,
    596341312212022,598037103631533,599718381413576],
   [601385284705215,603037950080415,604676511607822,606301100916251,607911847257958,
    609508877569817,611092316532452,612662286627438,614218908192628,615762299475683,
    617292576685894,618809854044332,620314243832422,621805856438980,623284800405782,
    624751182471720,626205107615595,627646679097606,629075998499571,630493165763936,
    631898279231623,633291435678737,634672730352199,636042257004329,637400107926418,
    638746373981330,640081144635164,641404507988008,642716550803823,644017358539484,
    645307015372999,646585604230948,647853206815160,649109903628657,650355774000885,
    651590896112262,652815347018062,654029202671656,655232537947136,656425426661338,
    657607941595280,658780154515044,659942136192113,661093956423178,662235684049437,
    663367386975399,664489132187216,665600985770538,666703012927933,667795277995862,
    668877844461237,669950774977564,671014131380698,672067974704202,673112365194341,
    674147362324713,675173024810520,676189410622507,677196577000567,678194580467019,
    679183476839583,680163321244043,681134168126618,682096071266049,683049083785406,
    683993258163620,684928646246763,685855299259060,686773267813661,687682601923170,
    688583351009934,689475563916109,690359288913504,691234573713203,692101465474981,
    692960010816514,693810255822392,694652246052929,695486026552798,696311641859470,
    697129136011478,697938552556508,698739934559315,699533324609483,700318764829010,
    701096296879746,701865961970676,702627800865049,703381853887365,704128160930220,
    704866761461011,705597694528506,706320998769283,707036712414040,707744873293780,
    708445518845873,709138686120000,709824411783976,710502732129470,711173683077598,
    711837300184422,712493618646338,713142673305356,713784498654288,714419128841830,
    715046597677554,715666938636800,716280184865479,716886369184790,717485524095840,
    718077681784190,718662874124307,719241132683941,719812488728418,720376973224858,
    720934616846315,721485449975838,722029502710472,722566804865170,723097385976647,
    723621275307164,724138501848243,724649094324315,725153081196308,725650490665170,
    726141350675331,726625688918107,727103532835040],
   [727574909621186,728039846228347,728498369368241,728950505515625,729396280911365,
    729835721565449,730268853259952,730695701551957,731116291776418,731530649048980,
    731938798268754,732340764121044,732736571080030,733126243411405,733509805174974,
    733887280227206,734258692223747,734624064621891,734983420683015,735336783474971,
    735684175874442,736025620569260,736361140060687,736690756665660,737014492519006,
    737332369575611,737644409612566,737950634231276,738251064859534,738545722753566,
    738834629000044,739117804518069,739395270061120,739667046218976,739933153419615,
    740193611931070,740448441863271,740697663169851,740941295649930,741179358949869,
    741411872565001,741638855841332,741860327977222,742076308025039,742286814892787,
    742491867345716,742691484007900,742885683363800,743074483759801,743257903405728,
    743435960376338,743608672612792,743776057924108,743938133988593,744094918355248,
    744246428445165,744392681552895,744533694847799,744669485375383,744800070058612,
    744925465699206,745045688978919,745160756460797,745270684590427,745375489697155,
    745475187995307,745569795585370,745659328455180,745743802481073,745823233429040,
    745897636955851,745967028610171,746031423833663,746090837962068,746145286226282,
    746194783753409,746239345567806,746278986592112,746313721648261,746343565458490,
    746368532646322,746388637737548,746403895161189,746414319250446,746419924243643,
    746420724285149,746416733426299,746407965626293,746394434753093,746376154584300,
    746353138808023,746325401023744,746292954743158,746255813391018,746213990305956,
    746167498741303,746116351865895,746060562764869,746000144440449,745935109812725,
    745865471720419,745791242921645,745712436094654,745629063838578,745541138674160,
    745448673044471,745351679315632,745250169777510,745144156644421,745033652055813,
    744918668076948,744799216699574,744675309842586,744546959352685,744414177005024,
    744276974503849,744135363483132,743989355507197,743838962071337,743684194602424,
    743525064459517,743361582934456,743193761252450,743021610572665,742845141988797,
    742664366529645,742479295159670,742289938779557],
   [742096308226762,741898414276058,741696267640072,741489878969821,741279258855234,
    741064417825675,740845366350453,740622114839341,740394673643066,740163053053816,
    739927263305732,739687314575386,739443216982273,739194980589281,738942615403162,
    738686131375000,738425538400669,738160846321291,737892064923686,737619203940817,
    737342273052231,737061281884495,736776240011630,736487156955535,736194042186412,
    735896905123180,735595755133893,735290601536146,734981453597482,734668320535790,
    734351211519705,734030135668994,733705102054950,733376119700775,733043197581957,
    732706344626649,732365569716038,732020881684718,731672289321049,731319801367525,
    730963426521122,730603173433658,730239050712141,729871066919117,729499230573007,
    729123550148453,728744034076650,728360690745679,727973528500839,727582555644967,
    727187780438767,726789211101123,726386855809420,725980722699856,725570819867750,
    725157155367851,724739737214640,724318573382631,723893671806670,723465040382231,
    723032686965705,722596619374689,722156845388277,721713372747339,721266209154802,
    720815362275932,720360839738607,719902649133586,719440798014788,718975293899552,
    718506144268904,718033356567820,717556938205488,717076896555562,716593238956420,
    716105972711413,715615105089120,715120643323593,714622594614602,714120966127881,
    713615764995368,713106998315442,712594673153162,712078796540499,711559375476571,
    711036416927872,710509927828497,709979915080374,709446385553481,708909346086074,
    708368803484899,707824764525419,707277235952023,706726224478242,706171736786960,
    705613779530624,705052359331454,704487482781647,703919156443581,703347386850020,
    702772180504310,702193543880584,701611483423953,701026005550707,700437116648502,
    699844823076560,699249131165852,698650047219288,698047577511908,697441728291063,
    696832505776599,696219916161042,695603965609775,694984660261216,694362006227000,
    693736009592152,693106676415260,692474012728649,691838024538552,691198717825281,
    690556098543392,689910172621856,689260945964222,688608424448780,687952613928727,
    687293520232325,686631149163061,685965506499809],
   [685296597996983,684624429384695,683949006368909,683270334631594,682588419830879,
    681903267601196,681214883553439,680523273275105,679828442330444,679130396260605,
    678429140583780,677724680795345,677017022368006,676306170751938,675592131374926,
    674874909642501,674154510938080,673430940623101,672704204037161,671974306498147,
    671241253302369,670505049724696,669765701018683,669023212416701,668277589130070,
    667528836349183,666776959243631,666021962962335,665263852633667,664502633365573,
    663738310245697,662970888341503,662200372700396,661426768349842,660650080297485,
    659870313531269,659087473019550,658301563711217,657512590535803,656720558403603,
    655925472205787,655127336814508,654326157083021,653521937845788,652714683918590,
    651904400098637,651091091164675,650274761877095,649455416978036,648633061191496,
    647807699223433,646979335761870,646147975477002,645313623021292,644476283029577,
    643635960119171,642792658889960,641946383924504,641097139788139,640244931029069,
    639389762178467,638531637750573,637670562242786,636806540135760,635939575893500,
    635069673963456,634196838776614,633321074747590,632442386274720,631560777740152,
    630676253509937,629788817934117,628898475346814,628005230066321,627109086395186,
    626210048620302,625308121012990,624403307829088,623495613309036,622585041677958,
    621671597145747,620755283907149,619836106141845,618914068014535,617989173675015,
    617061427258262,616130832884513,615197394659344,614261116673752,613322003004228,
    612380057712841,611435284847313,610487688441094,609537272513442,608584041069497,
    607627998100355,606669147583146,605707493481106,604743039743649,603775790306446,
    602805749091492,601832920007179,600857306948371,599878913796473,598897744419501,
    597913802672152,596927092395877,595937617418946,594945381556519,593950388610714,
    592952642370674,591952146612638,590948905100000,589942921583383,588934199800702,
    587922743477230,586908556325662,585891642046179,584872004326517,583849646842024,
    582824573255727,581796787218396,580766292368603,579733092332787,578697190725313,
    577658591148536,576617297192859,575573312436797],
   [574526640447032,573477284778478,572425248974333,571370536566148,570313151073874,
    569253096005930,568190374859253,567124991119360,566056948260402,564986249745223,
    563912899025414,562836899541369,561758254722343,560676967986501,559593042740981,
    558506482381939,557417290294612,556325469853365,555231024421746,554133957352541,
    553034271987824,551931971659009,550827059686905,549719539381764,548609414043335,
    547496686960911,546381361413385,545263440669295,544142927986877,543019826614114,
    541894139788785,540765870738512,539635022680812,538501598823145,537365602362959,
    536227036487740,535085904375058,533942209192617,532795954098299,531647142240211,
    530495776756731,529341860776556,528185397418744,527026389792765,525864840998538,
    524700754126484,523534132257566,522364978463332,521193295805963,520019087338315,
    518842356103961,517663105137236,516481337463278,515297056098073,514110264048496,
    512920964312353,511729159878423,510534853726499,509338048827431,508138748143165,
    506936954626786,505732671222556,504525900865957,503316646483728,502104910993910,
    500890697305878,499674008320388,498454846929610,497233216017172,496009118458195,
    494782557119332,493553534858807,492322054526455,491088118963754,489851731003869,
    488612893471684,487371609183842,486127880948782,484881711566775,483633103829958,
    482382060522373,481128584420005,479872678290811,478614344894763,477353586983878,
    476090407302255,474824808586111,473556793563814,472286364955920,471013525475201,
    469738277826689,468460624707701,467180568807877,465898112809214,464613259386096,
    463326011205332,462036370926183,460744341200400,459449924672253,458153123978567,
    456853941748750,455552380604827,454248443161472,452942132026042,451633449798601,
    450322399071961,449008982431705,447693202456222,446375061716737,445054562777343,
    443731708195027,442406500519704,441078942294248,439749036054517,438416784329389,
    437082189640784,435745254503702,434405981426245,433064372909649,431720431448315,
    430374159529831,429025559635011,427674634237911,426321385805869,424965816799524,
    423607929672850,422247726873180,420885210841235],
   [419520384011154,418153248810514,416783807660367,415412062975258,414038017163259,
    412661672625990,411283031758650,409902096950039,408518870582590,407133355032390,
    405745552669209,404355465856522,402963096951542,401568448305237,400171522262362,
    398772321161480,397370847334990,395967103109150,394561090804105,393152812733907,
    391742271206543,390329468523960,388914406982085,387497088870855,386077516474237,
    384655692070253,383231617931006,381805296322699,380376729505663,378945919734379,
    377512869257501,376077580317877,374640055152579,373200295992917,371758305064468,
    370314084587098,368867636774981,367418963836627,365968067974897,364514951387035,
    363059616264681,361602064793897,360142299155189,358680321523530,357216134068378,
    355749738953699,354281138337991,352810334374303,351337329210255,349862124988063,
    348384723844555,346905127911196,345423339314107,343939360174086,342453192606630,
    340964838721950,339474300625000,337981580415490,336486680187908,334989602031543,
    333490348030502,331988920263728,330485320805027,328979551723079,327471615081462,
    325961512938673,324449247348142,322934820358258,321418234012382,319899490348868,
    318378591401085,316855539197433,315330335761360,313802983111384,312273483261111,
    310741838219253,309208049989645,307672120571265,306134051958251,304593846139922,
    303051505100792,301507030820590,299960425274277,298411690432065,296860828259436,
    295307840717153,293752729761286,292195497343223,290636145409692,289074675902773,
    287511090759921,285945391913979,284377581293195,282807660821241,281235632417230,
    279661497995730,278085259466782,276506918735917,274926477704173,273343938268109,
    271759302319826,270172571746977,268583748432786,266992834256068,265399831091239,
    263804740808333,262207565273022,260608306346627,259006965886136,257403545744220,
    255798047769248,254190473805300,252580825692187,250969105265463,249355314356442,
    247739454792211,246121528395647,244501536985433,242879482376069,241255366377891,
    239629190797084,238000957435697,236370668091657,234738324558785,233103928626808,
    231467482081377,229828986704079,228188444272453],
   [226545856560001,224901225336206,223254552366545,221605839412500,219955088231576,
    218302300577316,216647478199308,214990622843207,213331736250741,211670820159733,
    210007876304106,208342906413904,206675912215301,205006895430615,203335857778322,
    201662800973070,199987726725692,198310636743217,196631532728887,194950416382166,
    193267289398754,191582153470605,189895010285931,188205861529221,186514708881254,
    184821554019107,183126398616172,181429244342168,179730092863151,178028945841530,
    176325804936074,174620671801931,172913548090637,171204435450127,169493335524750,
    167780249955278,166065180378921,164348128429337,162629095736646,160908083927439,
    159185094624793,157460129448281,155733190013984,154004277934501,152273394818965,
    150540542273051,148805721898989,147068935295573,145330184058178,143589469778764,
    141846794045895,140102158444743,138355564557105,136607013961410,134856508232735,
    133104048942811,131349637660036,129593275949486,127834965372928,126074707488827,
    124312503852359,122548356015424,120782265526651,119014233931413,117244262771840,
    115472353586820,113698507912023,111922727279899,110145013219695,108365367257468,
    106583790916086,104800285715248,103014853171489,101227494798192,99438212105597,
    97647006600812,95853879787823,94058833167505,92261868237630,90462986492879,88662189424850,
    86859478522069,85054855270001,83248321151058,81439877644608,79629526226987,77817268371508,
    76003105548470,74187039225169,72369070865905,70549201931994,68727433881777,66903768170626,
    65078206250961,63250749572250,61421399581027,59590157720896,57757025432540,55922004153734,
    54085095319349,52246300361369,50405620708889,48563057788136,46718613022467,44872287832387,
    43024083635552,41174001846781,39322043878063,37468211138568,35612505034652,33754926969872,
    31895478344986,30034160557971,28170975004024,26305923075576,24439006162298,22570225651108,
    20699582926185,18827079368969,16952716358178,15076495269813,13198417477163,11318484350818,
    9436697258676,7553057565951,5667566635180,3780225826233,1891036496320]]
private def rkmC_w128_s2_1 : List ℤ := pzigCat
  [
   [364532664,597231074,1066266968,1639832270,2582021260,3952748426,5826388316,8694229660,
    12633790816,18443590578,26633521384,38232978156,54449906710,76883154360,107882359378,
    150427160182,208261583524,286421232414,390987379428,530131381408,713838879922,954457140238,
    1267585993312,1671645644766,2189599791884,2848371680608,3679907957800,4722027007350,
    6017762462046,7617139213594,9576081751130,11957085161268,14829322809444,18267092570126,
    22350236192574,27161836004008,32787313754124,39312168464758,46819516120968,55387208256888,
    65084613344120,75969171107248,88082844498298,101447907161202,116064005301678,131903879444282,
    148910872513704,166996984924614,186040148332052,205885078552612,226342541758992,
    247191753311480,268183260783790,289042797064844,309477211210802,329180680810202,
    347841719665688,365152397330932,380815387278290,394553088159706,406116001434898,
    415289306377330,421900772337158,425824936709954,426988116328196,425370161934294,
    421004761979606,413978938582684,404429805153546,392539727183686,378531794877240,
    362661231653216,345209098138552,326473356931304,306760591139996,286378084255666,
    265625648060106,244789412312730,224134833009504,203902139323192,184302587527276,
    165516155718222,147689687982838,130936730242262,115339310516828,100948115333790,
    87786109730632,75851201472296,65119042165218,55547504221892,47079477629730,39647265273476,
    33174881809872,27581606584582,22785016794114,18702269784438,15253202261568,12360770701406,
    9952942849762,7963151309004,6330385688788,5000457176446,3924680148520,3060791867480,
    2371890496742,1826234499268,1397330706212,1062278648568,802557433118,602404631934,
    449131699488,332691795964,244576465628,178619348866,129321593546,92790358548,65918400838,
    46106568498,31888751748,21503262120,14195013204,9011450112,5299575704,2891979590,1158108914,
    332528350]]
private def rkmC_w128_s2_2 : List ℤ := pzigCat
  [
   [251493506,613139158,945762494,1625034496,2513046608,3764225672,5789484478,8459340324,
    12534505352,18158213894,26220025352,37718141014,53718811918,76047100490,106957916794,
    149120722042,206781290098,284488349824,388689453838,527300402770,710202201250,950170170036,
    1262110736778,1664964196340,2181223032404,2837677241664,3666384416860,4704551135476,
    5995282938022,7587681398708,9537596904412,11906891769902,14763742607806,18181997905378,
    22239994617966,27020161061208,32606333252230,39082898166254,46531607561906,55028682983242,
    64642731047300,75429757347830,87430842235354,100667995562172,115140433888258,130821609976126,
    147655983441486,165557720625318,184407594722746,204053583766476,224311345993836,
    244965023244852,265771246750250,286462205782362,306751912216522,326341591427782,
    344926950427286,362206548784706,377888648721440,391700840628886,403396828597790,
    412764191095810,419630847590726,423869727501112,425403956398796,424207648219876,
    420307694928614,413782380702594,404758578518960,393408458528866,379942709779574,
    364605539256442,347666320290252,329412174401752,310140318472030,290149170524112,
    269732276672120,249170048349700,228724861654568,208635883867410,189114725539142,
    170343889982324,152473608908134,135623065795248,119879708343992,105301399561414,
    91918332862766,79735525680856,68736345278362,58885489200414,50132694861846,42415659895606,
    35663853453944,29800781130912,24747241575126,20423627909450,16751040568568,13654101071430,
    11061005891846,8905038808574,7125138301290,5665803002590,4477828461338,3517112062596,
    2745623606316,2130309531250,1642704550296,1259044035006,958920805846,725958555580,
    546178528318,408245093548,303165610308,223392197882,163522202484,118701012472,85442792582,
    60912414762,42740815936,29610954988,19960943812,13140097280,8300766238,4852349438,2629409710,
    1046714772,298976686]]
private def rkmC_w128_s2_3 : List ℤ := pzigCat
  [
   [376997994,615770648,1237985804,1949420340,3000640760,4644336100,6863563782,10186857364,
    14829748472,21774980674,31515760604,45151171684,64549654318,91290531368,128325546072,
    178950320900,247824835174,340673691128,464620637246,629485030510,846524061980,1130326802106,
    1498469980792,1972245804270,2577662496778,3344756357004,4309828529384,5514093531418,
    7005541432842,8838356113218,11073013954106,13776562380470,17021477123980,20885797865120,
    25451192134266,30801951870328,37022953575552,44197308783630,52403512905206,61712246894374,
    72183452914388,83862250399342,96775961334370,110929621874020,126303170926210,142848582723868,
    160486609261996,179106408396914,198563519878514,218680923294858,239250467320030,
    260034785522496,280772195986248,301180644165812,320964580798014,339821302950758,
    357448734249490,373553865241830,387859756836448,400114805974238,410099041167162,
    417631239574282,422574597806246,424840099923630,424390127861790,421238338184800,
    415450224294576,407140301952248,396468118017950,383634055368628,368871939361710,
    352443180211416,334628197432166,315719058190110,296011908285084,275798545805342,
    255360894494816,234963730492840,214850429570008,195238475734946,176316187420948,
    158242021160742,141142545936902,125113924977254,110222183758494,96505405238512,
    83976743505644,72626236245452,62425339083762,53329034276696,45279985030334,38211563277302,
    32050156156870,26719004854598,22139260134572,18233283189588,14925562381424,12143948006514,
    9821272249934,7894804731098,6308088162894,5009944125030,3955033475506,3103733780290,
    2421012400664,1877355794738,1446992624052,1108583917228,844256163914,638906502448,
    480675556858,359221843202,266757918060,196719087156,143886035822,104500755418,75043213130,
    53420890582,37477938454,25817556452,17454968856,11260396448,7000354334,3893815596,1862582736,
    670349626]]
private def rkmC_w128_s2_4 : List ℤ := pzigCat
  [
   [496255644,975001402,1593548028,2573665090,3788007260,5838458316,8735564690,12938484256,
    19175472580,27961144466,40731315222,58606042786,83695769434,118628279584,166731988262,
    232700094688,321957167628,442336680916,603081700276,815940874384,1095721758506,1460091269676,
    1931296525552,2535471878444,3304244407460,4274544508316,5489073639518,6997504195372,
    8855437459966,11125841888046,13877821946004,17186572416196,21132666535874,25800083544160,
    31275901747122,37646771778346,44997461943898,53407635951804,62948315631434,73679142964480,
    85643285805866,98865084587950,113345390845224,129058451430266,145949319376942,
    163930532760168,182881941963850,202648839498912,223043547861710,243846994869236,
    264811192928274,285664504256278,306115730041622,325861989071190,344595186395306,
    362010031511328,377812855764402,391728805638142,403511226360578,412947641086666,
    419866837050162,424144003133744,425703885058624,424524166642616,420634517565162,
    414116602492876,405100610303204,393760933470822,380311313224096,364996952376396,
    348088567702260,329873449354356,310648075683258,290710398867240,270351609821788,
    249850768618294,229467670842862,209439152348270,189974869748404,171254443261190,
    153426944066834,136609279181280,120888213036746,106320832183254,92937022736162,
    80742463938818,69720687024818,59837707391390,51044098952884,43279194060272,36473939064006,
    30553293398886,25439868063678,21054861349752,17321220069296,14164383196354,11513579750392,
    9303231372844,7472387217134,5966353818592,4735630092436,3736518909346,2930916153262,
    2285316011080,1771567896502,1365139536912,1045747143160,796363874610,602664795664,
    453394298086,338805616370,251573812278,185513133454,135718384068,98598550566,70830240004,
    50402287118,35290092072,24200934734,16218759382,10334495904,6313068682,3442834214,1613277046,
    569905928]]
private def rkmC_w128_s2_5 : List ℤ := pzigCat
  [
   [324063404,695806310,1115398830,1920501518,2869946842,4505252010,6858985834,10467316282,
    15902464624,23533000396,34717039440,50546615638,73214835006,105165834036,149652696774,
    211392652996,295772901494,410574373198,565087755256,771446077116,1044843941406,1403584821650,
    1870759813746,2473448821000,3244596398048,4222829021406,5453177125576,6987994716686,
    8885980621806,11213586549832,14043645940594,17455596042182,21534390120392,26368422152956,
    32048900964574,38666276843002,46308659408788,55057892821534,64985938785142,76151755602448,
    88596115518644,102338876113858,117373968351730,133666491325356,151149913196430,
    169723119768176,189250319545728,209559554060162,230444823075994,251668000131272,
    272962367115394,294038448444940,314589036876974,334297730749908,352846006320684,
    369922114761978,385230042852712,398497233745944,409483935642066,417989282014030,
    423858261725670,426986065621170,427320794280712,424865760922728,419677937131798,
    411866979589758,401590626772892,389049603130822,374481579804406,358152878436556,
    340351712025884,321378849712772,301540049465502,281138034898662,260464688661692,
    239795607511396,219383565102424,199455251527260,180207588165846,161805785091290,
    144383137055810,128040313541758,112847689173448,98846417703950,86051484090930,74454828691572,
    64027987027332,54726513514410,46492354902686,39257981652802,32949126623996,27487356001162,
    22793204699164,18787240571366,15392741083316,12536309480838,10149093361826,8167771613732,
    6534202225514,5196555836884,4108366772428,3228939964532,2522945095778,1959644755796,
    1513259931690,1161581406800,886344288486,672282476326,506757322396,379659820354,282637234778,
    208901369470,153475193448,111672366144,80556171006,57543810804,40372314208,27885008324,
    18722743726,12296719354,7723824494,4449554958,2338249704,894524854,244902982]]
private def rkmC_w128_s2_6 : List ℤ := pzigCat
  [
   [526804852,932325734,1672578126,2794095990,4400443822,6939488036,10484806134,16014969348,
    24201379898,36281452680,53851980146,78806773512,114435847062,164432607294,234259748454,
    330674931004,462435631478,641127158576,880769633218,1199531623140,1619291935384,
    2167076159026,2875532884620,3783161821276,4935813776522,6386087585998,8194693682866,
    10429855624614,13167224825968,16489820397526,20486219345894,25250240864474,30878039924186,
    37466242516048,45108938460628,53893733230094,63898748961014,75187354599106,87804698548582,
    101772857488042,117086647304044,133710327649716,151573449176934,170569453396716,
    190553563524996,211343194412980,232719389975326,254428958296404,276189549911402,
    297694217783178,318619197557722,338631372220364,357397227493024,374592220225888,
    389909893824022,403071077078948,413832674714476,421994537576364,427406622608828,
    429972613549012,429653243198706,426467317403956,420489779785262,411850334462394,
    400727407476180,387342991976098,371955427910474,354850265912272,336333065209378,
    316719281088066,296326356824354,275465512915824,254433987486754,233509242224362,
    212942920214608,192957819658808,173744306845264,155459245381462,138226087274514,
    122134681458942,107243961221040,93583571292566,81157390855156,69946563649626,59913089209394,
    51003811869190,43153650818884,36288717748702,30330234277776,25196113680812,20804440450574,
    17074614117598,13928904615180,11294735630454,9103860759392,7294201968610,5809575443014,
    4599578921160,3620127824184,2832339292988,2203006701164,1703302246490,1309025690254,
    1000100512376,759532990846,573335930940,430209818398,320567998064,237454400656,174575544012,
    127191208920,91965055618,65693369368,46401507094,32188334318,21897589150,14577962100,
    9217191246,5539137046,2936779548,1323958642,448307668]]
private def rkmHbN_w128_s3 : List ℕ := rkmCatN
  [
   [55497431237487,78421347457009,95967913065637,110723865660008,123692044011212,135387200511112,
    146115376013348,156076137306967,165408217446393,174212709476220,182565992502861,
    190527453597776,198144358385179,205455060594652,212491194678323,219279219682607,
    225841534664160,232197302631844,238363071057305,244353247188766,250180467667062,
    255855889836938,261389424130456,266789921474265,272065325928100,277222800131487,
    282268829257703,287209307813681,292049612625617,296794664607582,301448981352083,
    306016722157386,310501726780848,314907548955490,319237485510211,323494601779081,
    327681753862278,331801608203116,335856658866675,339849242841775,343781553636074,
    347655653391593,351473483713023,355236875372287,358947557028824,362607163085049,
    366217240779675,369779256607464,373294602142050,376764599328386,380190505302758,
    383573516790963,386914774128972,390215364945001,393476327537225,396698653977385,
    399883292967033,403031152470105,406143102142917,409219975580328,412262572394818,
    415271660143440,418247976116069,421192228996954,424105100410413,426987246360397,
    429839298572709,432661865747829,435455534731516,438220871609701,440958422733587,
    443668715680319,446352260154122,449009548832354,451641058160549,454247249100163,
    456828567832424,459385446421398,461918303439137,464427544555518,466913563095195,
    469376740563883,471817447146005,474236042175601,476632874582235,479008283313500,
    481362597735611,483696138013472,486009215471471,488302132936209,490575185062239,
    492828658641850,495062832899835,497277979774128,499474364183131,501652244280497,
    503811871698077,505953491777710,508077343792464,510183661157921,512272671634035,
    514344597518100,516399655829268,518438058485096,520460012470524,522465719999683,
    524455378670899,526429181615246,528387317638971,530329971360093,532257323339474,
    534169550206630,536066824780537,537949316185676,539817189963541,541670608179836,
    543509729527548,545334709426104,547145700116780,548942850754544,550726307496491,
    552496213587024,554252709439921,555995932717443,557726018406592,559443098892657,
    561147304030163,562838761211331],
   [564517595432162,566183929356236,567837883376330,569479575673942,571109122276810,
    572726637114506,574332232072181,575926017042545,577508099976142,579078586929995,
    580637582114678,582185187939892,583721505058582,585246632409672,586760667259451,
    588263705241682,589755840396469,591237165207929,592707770640721,594167746175468,
    595617179843118,597056158258271,598484766651534,599903088900905,601311207562255,
    602709203898917,604097157910421,605475148360405,606843252803737,608201547612860,
    609550108003405,610889008059081,612218320755877,613538117985599,614848470578757,
    616149448326830,617441120003928,618723553387871,619996815280706,621260971528673,
    622516087041648,623762225812076,624999450933403,626227824618036,627447408214838,
    628658262226168,629860446324500,631054019368603,632239039419324,633415563754976,
    634583648886337,635743350571276,636894723829026,638037822954102,639172701529876,
    640299412441833,641418007890496,642528539404050,643631057850658,644725613450492,
    645812255787472,646891033820735,647961995895838,649025189755690,650080662551249,
    651128460851952,652168630655929,653201217399965,654226265969248,655243820706895,
    656253925423265,657256623405061,658251957424235,659239969746693,660220702140814,
    661194195885774,662160491779699,663119630147634,664071650849346,665016593286955,
    665954496412409,666885398734791,667809338327483,668726352835168,669636479480696,
    670539755071800,671436216007675,672325898285423,673208837506365,674085068882221,
    674954627241171,675817547033784,676673862338840,677523606869021,678366813976500,
    679203516658414,680033747562229,680857538990997,681674922908519,682485930944394,
    683290594398983,684088944248264,684881011148607,685666825441446,686446417157867,
    687219816023112,687987051460990,688748152598209,689503148268628,690252067017429,
    690994937105208,691731786511993,692462642941189,693187533823448,693906486320468,
    694619527328727,695326683483140,696027981160665,696723446483825,697413105324186,
    698096983305756,698775105808337,699447497970808,700114184694357,700775190645651,
    701430540259952,702080257744184,702724367079934],
   [703362892026418,703995856123379,704623282693949,705245194847453,705861615482171,
    706472567288046,707078072749357,707678154147335,708272833562744,708862132878417,
    709446073781744,710024677767127,710597966138387,711165960011141,711728680315125,
    712286147796497,712838383020086,713385406371617,713927238059892,714463898118938,
    714995406410126,715521782624245,716043046283552,716559216743787,717070313196157,
    717576354669283,718077360031125,718573347990869,719064337100791,719550345758089,
    720031392206685,720507494538999,720978670697703,721444938477438,721906315526509,
    722362819348559,722814467304207,723261276612670,723703264353359,724140447467447,
    724572842759415,725000466898582,725423336420597,725841467728926,726254877096303,
    726663580666171,727067594454090,727466934349135,727861616115268,728251655392691,
    728637067699178,729017868431390,729394072866172,729765696161826,730132753359372,
    730495259383786,730853229045224,731206677040225,731555617952901,731900066256106,
    732240036312592,732575542376147,732906598592716,733233219001511,733555417536096,
    733873208025471,734186604195125,734495619668089,734800267965964,735100562509939,
    735396516621797,735688143524904,735975456345184,736258468112084,736537191759524,
    736811640126835,737081825959680,737347761910971,737609460541768,737866934322163,
    738120195632162,738369256762545,738614129915720,738854827206565,739091360663260,
    739323742228104,739551983758323,739776097026873,739996093723223,740211985454134,
    740423783744426,740631500037736,740835145697266,741034732006518,741230270170026,
    741421771314071,741609246487394,741792706661896,741972162733327,742147625521973,
    742319105773326,742486614158752,742650161276146,742809757650586,742965413734966,
    743117139910632,743264946488011,743408843707218,743548841738675,743684950683705,
    743817180575131,743945541377857,744070042989455,744190695240727,744307507896279,
    744420490655075,744529653150987,744635004953341,744736555567453,744834314435164,
    744928290935359,745018494384489,745104934037079,745187619086239,745266558664158,
    745341761842600,745413237633391,745480994988900],
   [745545042802514,745605389909109,745662045085512,745715017050964,745764314467568,
    745809945940739,745851920019645,745890245197647,745924929912726,745955982547913,
    745983411431710,746007224838504,746027430988982,746044038050534,746057054137657,
    746066487312352,746072345584513,746074636912320,746073369202616,746068550311290,
    746060188043649,746048290154787,746032864349951,746013918284902,745991459566270,
    745965495751908,745936034351242,745903082825608,745866648588601,745826739006404,
    745783361398125,745736523036120,745686231146324,745632492908564,745575315456881,
    745514705879843,745450671220848,745383218478440,745312354606599,745238086515051,
    745160421069555,745079365092196,744994925361677,744907108613599,744815921540743,
    744721370793351,744623462979397,744522204664862,744417602373998,744309662589596,
    744198391753247,744083796265602,743965882486625,743844656735848,743720125292620,
    743592294396352,743461170246765,743326759004125,743189066789487,743048099684925,
    742903863733767,742756364940822,742605609272612,742451602657589,742294350986361,
    742133860111909,741970135849802,741803183978413,741633010239127,741459620336549,
    741283019938712,741103214677278,740920210147737,740734011909610,740544625486640,
    740352056366985,740156310003412,739957391813483,739755307179742,739550061449895,
    739341659936999,739130107919632,738915410642074,738697573314484,738476601113067,
    738252499180245,738025272624828,737794926522176,737561465914365,737324895810344,
    737085221186100,736842446984809,736596578116994,736347619460679,736095575861535,
    735840452133034,735582253056591,735320983381711,735056647826132,734789251075963,
    734518797785825,734245292578986,733968740047496,733689144752320,733406511223471,
    733120843960133,732832147430793,732540426073364,732245684295311,731947926473767,
    731647156955657,731343380057814,731036600067096,730726821240496,730414047805260,
    730098283958994,729779533869773,729457801676248,729133091487750,728805407384395,
    728474753417187,728141133608114,727804551950247,727465012407838,727122518916416,
    726777075382875,726428685685569,726077353674402],
   [725723083170914,725365877968367,725005741831831,724642678498268,724276691676608,
    723907785047836,723535962265063,723161226953608,722783582711069,722403033107396,
    722019581684966,721633231958649,721243987415878,720851851516715,720456827693916,
    720058919352997,719658129872290,719254462603009,718847920869306,718438507968328,
    718026227170273,717611081718444,717193074829302,716772209692514,716348489471004,
    715921917301003,715492496292090,715060229527241,714625120062869,714187170928866,
    713746385128644,713302765639173,712856315411014,712407037368361,711954934409067,
    711500009404682,711042265200480,710581704615490,710118330442519,709652145448184,
    709183152372932,708711353931062,708236752810749,707759351674061,707279153156978,
    706796159869410,706310374395205,705821799292172,705330437092084,704836290300692,
    704339361397732,703839652836935,703337167046027,702831906426735,702323873354789,
    701813070179924,701299499225876,700783162790378,700264063145161,699742202535941,
    699217583182416,698690207278256,698160076991088,697627194462488,697091561807963,
    696553181116939,696012054452737,695468183852559,694921571327464,694372218862347,
    693820128415912,693265301920646,692707741282793,692147448382323,691584425072898,
    691018673181843,690450194510107,689878990832230,689305063896300,688728415423914,
    688149047110137,687566960623457,686982157605739,686394639672176,685804408411240,
    685211465384633,684615812127227,684017450147017,683416380925055,682812605915399,
    682206126545043,681596944213864,680985060294546,680370476132521,679753193045896,
    679133212325384,678510535234227,677885163008124,677257096855154,676626337955692,
    675992887462334,675356746499805,674717916164882,674076397526299,673432191624661,
    672785299472346,672135722053418,671483460323523,670828515209795,670170887610748,
    669510578396179,668847588407058,668181918455419,667513569324251,666842541767381,
    666168836509362,665492454245353,664813395640998,664131661332301,663447251925502,
    662760167996949,662070410092964,661377978729712,660682874393062,659985097538449,
    659284648590733,658581527944052,657875735961677],
   [657167272975859,656456139287678,655742335166885,655025860851745,654306716548874,
    653584902433071,652860418647157,652133265301797,651403442475328,650670950213583,
    649935788529710,649197957403986,648457456783632,647714286582621,646968446681485,
    646219936927121,645468757132582,644714907076883,643958386504783,643199195126584,
    642437332617908,641672798619481,640905592736914,640135714540470,639363163564840,
    638587939308906,637810041235505,637029468771185,636246221305960,635460298193062,
    634671698748682,633880422251717,633086467943503,632289835027551,631490522669271,
    630688529995702,629883856095226,629076500017287,628266460772098,627453737330346,
    626638328622896,625820233540482,624999450933403,624175979611202,623349818342352,
    622520965853928,621689420831278,620855181917686,620018247714035,619178616778454,
    618336287625973,617491258728159,616643528512756,615793095363314,614939957618812,
    614084113573281,613225561475411,612364299528157,611500325888342,610633638666248,
    609764235925200,608892115681149,608017275902243,607139714508392,606259429370828,
    605376418311655,604490679103395,603602209468523,602711007078998,601817069555780,
    600920394468349,600020979334210,599118821618387,598213918732914,597306268036316,
    596395866833085,595482712373136,594566801851269,593648132406612,592726701122057,
    591802505023690,590875541080206,589945806202320,589013297242163,588078010992673,
    587139944186972,586199093497732,585255455536538,584309026853229,583359803935235,
    582407783206904,581452961028813,580495333697068,579534897442599,578571648430431,
    577605582758956,576636696459180,575664985493969,574690445757271,573713073073333,
    572732863195902,571749811807411,570763914518150,569775166865428,568783564312716,
    567789102248773,566791775986764,565791580763358,564788511737809,563782563991024,
    562773732524613,561762012259922,560747398037051,559729884613853,558709466664915,
    557686138780520,556659895465594,555630731138631,554598640130598,553563616683825,
    552525654950871,551484748993368,550440892780848,549394080189548,548344305001192,
    547291560901748,546235841480169,545177140227104],
   [544115450533588,543050765689711,541983078883255,540912383198311,539838671613868,
    538761937002379,537682172128292,536599369646563,535513522101131,534424621923376,
    533332661430533,532237632824089,531139528188138,530038339487715,528934058567090,
    527826677148028,526716186828022,525602579078488,524485845242921,523365976535019,
    522242964036769,521116798696495,519987471326866,518854972602862,517719293059707,
    516580423090752,515438352945319,514293072726499,513144572388910,511992841736403,
    510837870419721,509679647934119,508518163616921,507353406645036,506185366032421,
    505014030627481,503839389110434,502661429990594,501480141603625,500295512108710,
    499107529485676,497916181532056,496721455860076,495523339893592,494321820864946,
    493116885811767,491908521573687,490696714788999,489481451891230,488262719105640,
    487040502445650,485814787709179,484585560474902,483352806098432,482116509708396,
    480876656202444,479633230243144,478386216253801,477135598414165,475881360656049,
    474623486658833,473361959844878,472096763374812,470827880142724,469555292771224,
    468278983606400,466998934712644,465715127867356,464427544555518,463136165964132,
    461840972976529,460541946166529,459239065792459,457932311791024,456621663771014,
    455307101006866,453988602432053,452666146632304,451339711838655,450009275920315,
    448674816377353,447336310333185,445993734526877,444647065305228,443296278614660,
    441941349992878,440582254560313,439218967011334,437851461605217,436479712156874,
    435103692027319,433723374113880,432338730840131,430949734145545,429556355474862,
    428158565767145,426756335444533,425349634400670,423938431988802,422522697009523,
    421102397698171,419677501711849,418247976116069,416813787370988,415374901317244,
    413931283161363,412482897460714,411029708108020,409571678315386,408108770597829,
    406640946756309,405168167860214,403690394229305,402207585415077,400719700181539,
    399226696485358,397728531455375,396225161371444,394716541642581,393202626784385,
    391683370395711,390158725134556,388628642693136,387093073772108,385551968053912,
    384005274175187,382452939698232,380894911081462],
   [379331133648823,377761551558112,376186107768163,374604744004850,373017400725842,
    371424017084068,369824530889826,368218878571483,366606995134680,364988814120010,
    363364267559056,361733285928746,360095798103920,358451731308049,356801011061989,
    355143561130694,353479303467787,351808158157873,350130043356483,348444875227544,
    346752567878231,345053033291075,343346181253185,341631919282436,339910152550456,
    338180783802239,336443713272225,334698838596621,332946054721784,331185253808439,
    329416325131493,327639154975204,325853626523443,324059619744749,322257011271898,
    320445674275635,318625478332252,316796289284612,314957969096242,313110375698058,
    311253362827267,309386779857953,307510471622814,305624278225491,303728034842862,
    301821571516655,299904712933650,297977278193716,296039080564844,294089927224272,
    292129618984734,290157950004783,288174707482018,286179671328006,284172613823515,
    282153299252604,280121483513959,278076913707732,276019327695964,273948453634509,
    271864009474168,269765702428537,267653228405796,265526271401448,263384502848640,
    261227580922436,259055149793974,256866838830022,254662261733012,252441015616016,
    250202680006588,247946815772673,245672963962999,243380644553514,241069355090394,
    238738569219015,236387735086973,234016273607738,231623576569797,229209004574169,
    226771884780885,224311508442387,221827128198712,219317955105764,216783155363815,
    214221846708441,211633094420406,209015906904164,206369230776658,203691945398507,
    200982856768283,198240690686899,195464085082649,192651581367528,189801614671184,
    186912502769261,183982433486416,181009450309276,177991435888502,174926093038946,
    171810922758300,168643198672076,165419937168637,162137862301721,158793364295146,
    155382450164769,151900684547546,148343118255358,144704201291707,140977675993007,
    137156444447982,133232402201092,129196227133406,125037107813821,120742388663727,
    116297098519148,111683312051659,106879265388213,101858099385335,96586018974635,
    91019498306598,85100847183651,78750785194009,71855109442627,64238444046580,55605402069833,
    45379705151221,32072732085860]]
private def rkmC_w128_s3_1 : List ℤ := pzigCat
  [
   [271388458,808465962,1618471632,2794406688,4851055576,8014293262,12940182064,20715484254,
    32352352716,50122186766,76748578408,115872465614,172750230386,254033764154,369078820102,
    529629552680,751427237460,1054352339256,1462812618876,2007873420880,2726591352116,
    3664257288096,4874307381106,6418934928762,8370050792716,10808600438150,13824390513606,
    17515798866110,21987438938082,27348774769624,33710946440496,41183563330218,49870826560550,
    59866310987986,71249024091488,84076708382012,98381560479648,114164694215782,131391200074106,
    149986878301218,169834920929400,190774389854248,212601029538656,235067608039144,
    257888480040440,280744897683914,303291277292848,325164578788948,345992864490552,
    365407174044982,383051691779058,398594605378132,411739106556840,422232484756770,
    429874330131608,434523146484690,436099685986276,434590347127710,430046180415046,
    422580302873892,412364340754210,399620931622642,384616689033432,367652470504052,
    349053992677860,329162282338492,308322308627500,286874974512258,265147890937942,
    243447828517302,222054831374690,201217048835626,181148064841396,162024097532850,
    143984508543018,127132107347816,111534609162728,97228163250146,84219706685622,72491455404100,
    62004338962232,52702345375646,44516716064162,37368864982084,31174760501430,25847111816134,
    21298459789844,17443092818072,14198608919232,11487522382068,9237978571584,7384045161228,
    5866871804784,4633402861254,3637462968182,2838741954246,2202055281346,1698170564916,
    1301734848160,991858261940,751203488178,565380512384,422941539026,314150519924,231793224090,
    169807193402,123357800500,88838040608,63127021242,44338423928,30612362866,20699719816,
    13654853098,8546783584,5098211362,2703925782,1228904852,421690320]]
private def rkmC_w128_s3_2 : List ℤ := pzigCat
  [
   [308254494,668204900,1208643650,2317478140,3960227766,7102304372,12239047516,20423527790,
    33400493060,53380103402,84077842598,129899468996,197491874256,295759200814,436382115720,
    634957047156,911175667912,1290717036932,1805274483698,2493887206632,3404085791782,
    4592623235916,6126518942826,8082290247418,10547476324460,13619362201064,17403922625450,
    22014507315786,27569344346426,34188147247508,41988346685002,51080294753176,61562477020930,
    73514873538576,86993942386496,102026565105288,118603838676324,136677316389216,
    156153783413576,176893791721130,198710195656516,221368587196946,244591112001206,
    268059616397924,291423696797164,314308665977332,336325116034020,357080817568080,
    376191582979460,393294057868800,408056662345168,420190752460030,429460016689220,
    435687657744362,438762804234444,438642516775472,435353460419530,428989705274204,
    419708467686970,407724100328372,393300031378320,376739358324350,358374865936846,
    338557688217378,317647673672856,296002056797402,273966503015630,251867297896682,
    230003266122984,208641770939182,188013633558352,168311468467710,149689249296104,
    132261688450826,116107225042250,101269824396312,87762814505214,75572509413088,64662522698818,
    54978217010852,46450555473064,39000009654644,32540796516436,26982867681706,22236135835460,
    18211914021944,14824581500154,11993917918714,9644662180162,7708654650406,6124306827998,
    4836363989646,3796500043362,2962325944108,2297785622384,1771673087372,1357799199236,
    1034433652274,783294802460,589446366192,440856478622,327387326968,241624277326,176937890160,
    128376569566,92427110508,65758713898,46277020858,31996061272,21694448694,14380976266,
    9044531008,5397906728,2840614126,1270987804,427489306]]
private def rkmC_w128_s3_3 : List ℤ := pzigCat
  [
   [292977342,917358728,2385381978,4848752416,9343268292,16966478624,29658265220,50452789920,
    83107376800,133932820224,210780197030,325002521240,491659349866,730335655134,1066944471978,
    1534256661160,2172940653178,3033376914958,4175912652514,5672460979762,7606433203432,
    10073000746816,13178935910014,17040501099864,21782659218914,27535123911210,34429301851594,
    42593550290748,52146799660982,63194146309802,75818516725524,90074877794386,105983649016662,
    123524096276356,142629511240782,163183298312054,185016483369512,207907896796174,
    231585236488008,255730062422686,279983600324720,303955416425372,327234173240082,
    349398449020000,370031014103848,388730791994326,405126522511720,418889741756544,
    429744357121672,437477332547574,441944573569000,443075490414842,440874570380032,
    435420035609034,426860110196810,415406563413374,401326050153592,384930915908178,
    366567328116014,346604312955608,325421288652102,303397020658410,280900239248608,
    258278705154544,235852874460848,213909218746696,192695865848732,172420407337546,
    153248462913322,135304371320148,118673494770234,103403939535534,89511446518526,
    76982809741526,65780613068584,55848051441160,47112385892174,39490865176150,32893242148804,
    27225513589920,22393416748096,18304309376234,14869151465966,12004267677596,9631755876230,
    7681091507420,6088143000424,4796214813262,3755796683562,2923168279414,2261500563180,
    1739118730170,1329332094176,1009946232134,762527131676,572116723576,426543058618,
    315699497176,232190575812,169421582752,122512598496,87893868742,62287616202,43628423650,
    29997433596,20187510988,13209756922,8162194156,4703033204,2504164510,943496760,249816658]]
private def rkmC_w128_s3_4 : List ℤ := pzigCat
  [
   [267262441,399190243,542377273,277634273,520949750,2675121808,7271291586,15847705268,
    31382099206,58050794302,101871596146,172046635050,280741961502,445168934016,688362708098,
    1039978742274,1539008970520,2233550338338,3183549374622,4461359006864,6152507980734,
    8356411533480,11185795358532,14765945539968,19232660346114,24728572684002,31400321381730,
    39392283221468,48840525885978,59866513876852,72568363117504,87014433433774,103234148537146,
    121211478799292,140879205018040,162113870566974,184733406930250,208496776051828,
    233106127308808,258212449712090,283421838302716,308306592323154,332417221802612,
    355295092331690,376488715303302,395567749161992,412138376814366,425856399811818,
    436439271734730,443676164626110,447434130738862,447661969769058,444391551242758,
    437733835956488,427874650336214,415065982601180,399615712482188,381876077050586,
    362230809491458,341082076338226,318837854468402,295899064678090,272650010452756,
    249447860664238,226615207185170,204435744183868,183148855081456,162949294279052,
    143986725935730,126366988069784,110155362984438,95380011545142,82036398841252,70092647385744,
    59493640190368,50167101915412,42027498122112,34980821259274,28928521804812,23770351954426,
    19407605846908,15745558060350,12693896537246,10169602990954,8096599192134,6406110141340,
    5037324115248,3936653083086,3057476737626,2360327433144,1810834070264,1380701124902,
    1046291753232,787806997926,589423014484,438187961332,323352939484,237093484980,172452744608,
    124350826074,88913219518,62775113350,43691640336,30039597820,20015041946,13035990262,
    8054774586,4491137998,2221776928,786437026]]
private def rkmC_w128_s3_5 : List ℤ := pzigCat
  [
   [216381499,538052125,1253973113,1996566125,2634265957,3347280385,3023290539,767711651,
    5682378118,19798443832,47049178270,96013224928,178828056126,313066731968,523104857024,
    840737242336,1308713319644,1981117859788,2925485744418,4224636043450,5977001115706,
    8297191234492,11315962469636,15177835015816,20039095348502,26062895713092,33414793834198,
    42255430170558,52732465514668,64972365680350,79070771436818,95082838061740,113015660530442,
    132819036642488,154380641956326,177521879876360,201996218672504,227491972490596,
    253637080375780,280006588851158,306135472411758,331530815467670,355688423201248,
    378109884045838,398319456144278,415881659991378,430416885749870,441614312444496,
    449244379779258,453164637936848,453324514903584,449765823304828,442618511389824,
    432094407482530,418477726930044,402112003411234,383388003065874,362727575846306,
    340569404089058,317355079900890,293514885783432,269456416878056,245555223508456,
    222145873301986,199518186834360,177912762453710,157520068904394,138481888368278,
    120892950725468,104804802276956,90231188800988,77151822888190,65519548375296,55265113724466,
    46302457235398,38534515368738,31857171116440,26163095883866,21346163199668,17302542128496,
    13934038643164,11149155346902,8863629339530,7001716066036,5495990407422,4286649218206,
    3322488642316,2558944347374,1958378998114,1489403311286,1125517374164,845025005848,
    630459434598,467069432256,343690772366,251087558026,181931381246,130798011534,93187864226,
    65553950564,45623296376,31063081094,20614234380,13247346232,8000779304,4465233944,2254943334,
    797577728]]
private def rkmC_w128_s3_6 : List ℤ := pzigCat
  [
   [461242521,1334865189,2739770031,5135006081,8010638071,11467966961,14373154999,14411862697,
    7795351919,12349290580,56628268876,140758808408,288397408248,531546312532,914289838710,
    1494490860762,2345435155738,3558610198620,5244625026184,7533340721124,10574379596246,
    14533602464674,19590901018362,25934547480578,33753652314932,43230481573924,54530190565128,
    67789398521534,83106131169774,100527246673086,120039360054318,141560196791544,
    164931905187686,189918914497278,216208373258314,243413862218162,271085021771474,
    298718256757472,325772961989960,351689638280196,375908925217622,397892763528912,
    417144675265150,433227778206542,445782463045810,454538414847640,459324189795476,
    460072797879558,456821101269384,449707005199604,438960999127626,424894898118248,
    407887810420792,388370479205148,366807411754836,343680884683562,319473686325152,
    294654132895282,269663467259646,244904397692722,220732783093086,197453107490620,
    175313919701318,154508387280742,135175788605730,117403729632042,101234047698272,
    86667815068130,73671372684312,62182982024006,52119525458768,43381443790540,35859540756606,
    29438972569786,24003528286186,19439535202936,15637722724172,12495284753552,9918313257208,
    7820852011414,6126331417046,4767679971614,3686167546114,2831488980542,2160888094196,
    1638349611114,1233945260822,923366949248,686162671158,506463661788,371357763190,270182871472,
    195017667508,139637212682,98954314690,69236736422,47918812368,32375799078,21371414940,
    13721042484,8277751804,4584922938,2264773426,775466716]]
private def rkmC_w128_s3_7 : List ℤ := pzigCat
  [
   [317104850,621509108,938596300,874720334,11793882,1976353621,5687519813,11718299675,
    20162854249,30956436651,42325414293,50180751781,47490669355,21036041397,49096864122,
    193079858114,453929684408,890096184846,1578839987574,2619156840944,4132650804948,
    6265527821136,9187622701362,13089777284540,18180226831042,24677737108726,32802160676902,
    42764954184284,54755589648110,68927933821840,85387323216600,104175586491598,125260367441690,
    148525193342518,173763201328144,200675504406644,228873955932860,257888124609774,
    287178668229828,316153697858376,344188701369562,370651049684238,394923025022720,
    416426782260586,434647626870720,449154293135866,459615287686382,465811735238832,
    467643515012792,465130880013548,458410943427466,447727627323448,433419926148378,
    415904746115522,395657809607222,373194156210626,349048550335842,323754933544922,
    297829971734888,271758087261820,245978056503462,220875222048794,196774868872746,
    173939279838666,152567965608924,132800204536364,114718265325882,98354464124792,
    83697390700170,70698578202554,59281245716248,49346624915594,40780670982238,33460422024692,
    27259284266434,22050519028954,17712082453250,14128345880138,11191670031470,8804526940352,
    6879298032464,5338371417862,4114558604604,3149891639242,2395091203284,1808723288324,
    1356847070208,1010821433270,747796926222,549513055640,400801004476,290009556808,208245138404,
    148262416350,104314854114,72656792036,49819822020,33472999344,22025481416,13956616000,
    8298935688,4581701984,2249465132,751992612]]
private def rkmHbWin_w128_s4 : List ℤ := altBuildHbFrom 2048 1024 18396226415 0 1024
private def rkmXsWin_w128_s4_in : List ℤ := pzigCat
  [
   [219847549,6264018,626212704,1397007998,2367184550,3459489562,3846537378,3088758262,225286419,
    7585379335,20473422671,40466249989,67693477271,99884972303,131118379215,148807129443,
    130379438351,41291708395,170691997586,578848111564,1280852694540,2402848503250,4101394118066,
    6563191065862,10003983433610,14663655488880,20798337395696,28670688554562,38535964027666,
    50625922329340,65133210883452,82191861517954,101861007674678,124109922431162,148805703521268,
    175706223936206,204458620305920,234603541286490,265585426195338,296770380504934,
    327467201111982,356954347184586,384509290088160,409438353929600,431106071890524,
    448963017394708,462567912130528,471605039887482,475896443867184,475405323841180,
    470233620829528,460614410221818,446895968412604,429523816257934,409018745802680,
    385952669206420,360924003372566,334535199262424,307371108082520,279980065012548,
    252859951762052,226446604060494,201106143753280,177132725217152,154747606545740,
    134102522713510,115284932849500,98325224962626,83204166292568,69862392864852,58209251494818,
    48130146384958,39495277125982,32166668984680,26003077833264,20865231213316,16619979533682,
    13142119258888,10316899377426,8040748037940,6222124611112,4780486543450,3646717008916,
    2762354560074,2077659415128,1551491963896,1150453495368,847016227918,618926697116,
    448862626536,323051267446,230612269306,162912292888,114043525888,78892920248,53622328982,
    35836964964,23461620728,14758215502,8748653944,4828524424,2335989598,755377016]]
private def rkmXsWin_w128_s4_out : List ℤ := pzigCat
  [
   [423472422,996809350,109113907,1937775277,595665257,3155012320,2298017298,3757488337,
    4587380369,4214066292,8666219654,3167395587,14203375347,1326601657,20794060398,11473144344,
    25504173719,29228496103,23690087964,54923347328,8436811269,85737882209,30392667447,
    112208116644,103649979842,112116362829,215181046719,46864433208,345667821104,129004776920,
    436975035531,453005984297,370871113228,903054791146,26570333904,1320159891631,916806393627,
    1330876398178,2280255056576,349773655099,3625825953993,2177416789451,3702965745644,
    6103068200202,600157501825,9510768104245,7097575287847,7940733813108,17517731679678,
    4192909417756,21979733341861,27363435977923,5375982107932,46000530567738,40622371352620,
    23820007297083,87164179034255,66746738258917,48352569352948,160528539441280,139747981862904,
    47010371849403,277208918374801,351117554044395,146504901876059,281519632131914,
    736021722782084,1012362184684096,1020827692873310,814345367147462,524092082515012,
    269396390268270,105754070000694,27719048364096]]
private def rkmHbN_w128_s4 : List ℕ := rkmCatN
  [
   [53281163044002,75295752469315,92150486357394,106328151706783,118791201654234,130033616781356,
    140349063679952,149929024075928,158906599513398,167378771424575,175418806422041,
    183083666829731,190418684707058,197460641764073,204239873342275,210781749823460,
    217107746879980,223236236025786,229183079959504,234962088583885,240585373605708,
    246063628002439,251406348949231,256622017593746,261718245473137,266701894843376,
    271579178389144,276355742477103,281036737156905,285626875401835,290130483545295,
    294551544462324,298893734733040,303160456783049,307354866807041,311479899133113,
    315538287567475,319532584165063,323465175795860,327338298815542,331154052099216,
    334914408656279,338621226010900,342276255504903,345881150656828,349437474691728,
    352946707340200,356410250991563,359829436274715,363205527130476,366539725430983,
    369833175194664,373086966439293,376302138710437,379479684318146,382620551310868,
    385725646212249,388795836543525,391831953151739,394834792361752,397805117968094,
    400743663081025,403651131839641,406528201003561,409375521433574,412193719470576,
    414983398221218,417745138757887,420479501239885,423187025962076,425868234336640,
    428523629813096,431153698741279,433758911181543,436339721666084,438896569914949,
    441429881509985,443940068529729,446427530147948,448892653198375,451335812707929,
    453757372400555,456157685173636,458537093548797,460895930098745,463234517851708,
    465553170674884,467852193638220,470131883359746,472392528333596,474634409241765,
    476857799250578,479062964292785,481250163336123,483419648639126,485571665994928,
    487706454963736,489824249094610,491925276137147,494009758243632,496077912162168,
    498129949421282,500166076506451,502186495028998,504191401887729,506180989423719,
    508155445568582,510114953986555,512059694210732,513989841773707,515905568332934,
    517807041791051,519694426411408,521567882929042,523427568657318,525273637590420,
    527106240501926,528925525039609,530731635816665,532524714499529,534304899892418,
    536072328018774,537827132199721,539569443129684,541299388949295,543017095315693,
    544722685470341,546416280304469],
   [548097998422230,549767956201684,551426267853686,553073045478775,554708399122144,
    556332436826763,557945264684748,559546986887023,561137705771365,562717521868881,
    564286533948989,565844839062961,567392532586069,568929708258417,570456458224481,
    571972873071419,573479041866205,574975052191611,576460990181104,577936940552674,
    579402986641657,580859210432571,582305692590003,583742512488598,585169748242158,
    586587476731901,587995773633905,589394713445755,590784369512443,592164814051523,
    593536118177565,594898351925918,596251584275821,597595883172866,598931315550854,
    600257947353045,601575843552835,602885068173885,604185684309692,605477754142657,
    606761338962638,608036499185016,609303294368292,610561783231223,611812023669518,
    613054072772101,614287986836961,615513821386601,616731631183093,617941470242757,
    619143391850474,620337448573639,621523692275779,622702174129826,623872944631071,
    625036053609805,626191550243651,627339483069601,628479899995767,629612848312849,
    630738374705337,631856525262445,632967345488792,634070880314836,635167174107058,
    636256270677924,637338213295610,638413044693509,639480807079520,640541542145131,
    641595291074293,642642094552105,643681992773294,644715025450516,645741231822476,
    646760650661860,647773320283105,648779278549996,649778562883099,650771210267036,
    651757257257603,652736739988736,653709694179335,654676155139937,655636157779256,
    656589736610578,657536925758037,658477758962743,659412269588802,660340490629200,
    661262454711576,662178194103867,663087740719855,663991126124585,664888381539688,
    665779537848589,666664625601620,667543675021026,668416716005870,669283778136855,
    670144890681034,671000082596447,671849382536650,672692818855177,673530419609896,
    674362212567297,675188225206694,676008484724346,676823018037500,677631851788361,
    678435012347988,679232525820113,680024418044896,680810714602604,681591440817229,
    682366621760031,683136282253031,683900446872421,684659139951932,685412385586128,
    686160207633646,686902629720377,687639675242592,688371367370013,689097729048825,
    689818783004642,690534551745414,691245057564291],
   [691950322542430,692650368551758,693345217257686,694034890121775,694719408404360,
    695398793167125,696073065275637,696742245401837,697406354026489,698065411441583,
    698719437752709,699368452881377,700012476567314,700651528370707,701285627674423,
    701914793686182,702539045440704,703158401801810,703772881464500,704382502956986,
    704987284642706,705587244722290,706182401235509,706772772063179,707358374929049,
    707939227401647,708515346896102,709086750675940,709653455854845,710215479398399,
    710772838125788,711325548711492,711873627686933,712417091442117,712955956227230,
    713490238154229,714019953198393,714545117199862,715065745865142,715581854768596,
    716093459353910,716600574935533,717103216700101,717601399707834,718095138893919,
    718584449069865,719069344924844,719549841027009,720025951824791,720497691648183,
    720965074709997,721428115107112,721886826821692,722341223722400,722791319565581,
    723237127996442,723678662550197,724115936653215,724548963624138,724977756674988,
    725402328912258,725822693337985,726238862850816,726650850247043,727058668221643,
    727462329369287,727861846185344,728257231066868,728648496313572,729035654128787,
    729418716620410,729797695801836,730172603592881,730543451820688,730910252220622,
    731273016437155,731631756024739,731986482448660,732337207085888,732683941225917,
    733026696071582,733365482739881,733700312262769,734031195587959,734358143579695,
    734681167019527,735000276607072,735315482960760,735626796618580,735934228038805,
    736237787600718,736537485605318,736833332276026,737125337759375,737413512125694,
    737697865369784,737978407411582,738255148096818,738528097197665,738797264413377,
    739062659370922,739324291625603,739582170661679,739836305892964,740086706663434,
    740333382247816,740576341852170,740815594614469,741051149605168,741283015827764,
    741511202219351,741735717651171,741956570929148,742173770794432,742387325923914,
    742597244930757,742803536364903,743006208713583,743205270401817,743400729792910,
    743592595188937,743780874831228,743965576900843,744146709519043,744324280747751,
    744498298590016,744668770990457,744835705835719],
   [744999110954909,745158994120032,745315363046422,745468225393168,745617588763531,
    745763460705362,745905848711506,746044760220212,746180202615527,746312183227694,
    746440709333537,746565788156850,746687426868772,746805632588164,746920412381980,
    747031773265632,747139722203348,747244266108533,747345411844117,747443166222906,
    747537536007923,747628527912749,747716148601854,747800404690933,747881302747228,
    747958849289853,748033050790110,748103913671808,748171444311568,748235649039132,
    748296534137667,748354105844061,748408370349223,748459333798368,748507002291310,
    748551381882745,748592478582530,748630298355962,748664847124050,748696130763787,
    748724155108414,748748925947686,748770449028130,748788730053304,748803774684047,
    748815588538731,748824177193508,748829546182555,748831700998310,748830647091715,
    748826389872445,748818934709146,748808286929656,748794451821235,748777434630787,
    748757240565077,748733874790949,748707342435542,748677648586496,748644798292164,
    748608796561816,748569648365841,748527358635946,748481932265356,748433374109007,
    748381688983733,748326881668465,748268956904407,748207919395227,748143773807236,
    748076524769567,748006176874348,747932734676882,747856202695815,747776585413302,
    747693887275180,747608112691125,747519266034820,747427351644108,747332373821155,
    747234336832600,747133244909709,747029102248525,746921913010015,746811681320217,
    746698411270381,746582106917111,746462772282505,746340411354288,746215028085950,
    746086626396877,745955210172481,745820783264325,745683349490255,745542912634518,
    745399476447886,745253044647776,745103620918367,744951208910713,744795812242860,
    744637434499956,744476079234360,744311749965747,744144450181219,743974183335403,
    743800952850556,743624762116661,743445614491527,743263513300883,743078461838475,
    742890463366152,742699521113961,742505638280231,742308818031662,742109063503406,
    741906377799153,741700763991209,741492225120574,741280764197020,741066384199164,
    740849088074545,740628878739689,740405759080185,740179731950746,739950800175280,
    739718966546951,739484233828242,739246604751015],
   [739006082016570,738762668295699,738516366228747,738267178425658,738015107466031,
    737760155899169,737502326244125,737241620989750,736978042594735,736711593487658,
    736442276067020,736170092701285,735895045728922,735617137458432,735336370168391,
    735052746107475,734766267494494,734476936518421,734184755338417,733889726083855,
    733591850854346,733291131719762,732987570720250,732681169866257,732371931138541,
    732059856488190,731744947836630,731427207075643,731106636067369,730783236644319,
    730457010609378,730127959735813,729796085767271,729461390417780,729123875371753,
    728783542283980,728440392779624,728094428454219,727745650873654,727394061574171,
    727039662062351,726682453815096,726322438279619,725959616873427,725593990984297,
    725225561970262,724854331159582,724480299850725,724103469312338,723723840783221,
    723341415472292,722956194558565,722568179191106,722177370489004,721783769541333,
    721387377407110,720988195115258,720586223664560,720181464023613,719773917130788,
    719363583894173,718950465191526,718534561870226,718115874747211,717694404608927,
    717270152211269,716843118279519,716413303508282,715980708561426,715545334072012,
    715107180642227,714666248843313,714222539215492,713776052267896,713326788478487,
    712874748293976,712419932129748,711962340369773,711501973366522,711038831440882,
    710572914882063,710104223947508,709632758862797,709158519821553,708681506985342,
    708201720483569,707719160413382,707233826839558,706745719794401,706254839277630,
    705761185256265,705264757664513,704765556403650,704263581341904,703758832314326,
    703251309122672,702741011535272,702227939286900,701712092078645,701193469577769,
    700672071417576,700147897197271,699620946481810,699091218801765,698558713653168,
    698023430497361,697485368760844,696944527835120,696400907076528,695854505806092,
    695305323309343,694753358836163,694198611600605,693641080780722,693080765518394,
    692517664919138,691951778051936,691383103949041,690811641605791,690237389980414,
    689660347993836,689080514529476,688497888433050,687912468512360,687324253537089,
    686733242238584,686139433309647,685542825404305],
   [684943417137597,684341207085344,683736193783914,683128375729996,682517751380356,
    681904319151601,681288077419927,680669024520878,680047158749085,679422478358016,
    678794981559709,678164666524512,677531531380811,676895574214758,676256793069991,
    675615185947356,674970750804617,674323485556171,673673388072744,673020456181100,
    672364687663733,671706080258560,671044631658603,670380339511677,669713201420063,
    669043214940182,668370377582259,667694686809988,667016140040188,666334734642455,
    665650467938807,664963337203326,664273339661795,663580472491324,662884732819980,
    662186117726402,661484624239414,660780249337637,660072989949083,659362842950758,
    658649805168245,657933873375290,657215044293382,656493314591314,655768680884759,
    655041139735818,654310687652574,653577321088637,652841036442680,652101830057968,
    651359698221883,650614637165437,649866643062785,649115712030719,648361840128169,
    647605023355681,646845257654904,646082538908048,645316862937359,644548225504561,
    643776622310309,643002048993624,642224501131318,641443974237416,640660463762569,
    639873965093451,639084473552153,638291984395567,637496492814759,636697993934330,
    635896482811774,635091954436820,634284403730766,633473825545802,632660214664321,
    631843565798227,631023873588218,630201132603073,629375337338917,628546482218480,
    627714561590342,626879569728165,626041500829918,625200349017085,624356108333859,
    623508772746329,622658336141651,621804792327202,620948135029729,620088357894477,
    619225454484304,618359418278785,617490242673299,616617920978103,615742446417388,
    614863812128322,613982011160077,613097036472841,612208880936809,611317537331165,
    610422998343042,609525256566465,608624304501278,607720134552052,606812739026977,
    605902110136733,604988239993343,604071120609007,603150743894915,602227101660040,
    601300185609915,600369987345383,599436498361329,598499710045388,597559613676635,
    596616200424248,595669461346149,594719387387626,593765969379921,592809198038807,
    591849063963126,590885557633312,589918669409881,588948389531901,587974708115429,
    586997615151923,586017100506622,585033153916908],
   [584045764990620,583054923204357,582060617901738,581062838291633,580061573446365,
    579056812299875,578048543645858,577036756135857,576021438277333,575002578431686,
    573980164812254,572954185482258,571924628352725,570891481180358,569854731565378,
    568814366949310,567770374612748,566722741673053,565671455082027,564616501623530,
    563557867911060,562495540385275,561429505311476,560359748777039,559286256688794,
    558209014770352,557128008559383,556043223404838,554954644464114,553862256700161,
    552766044878540,551665993564407,550562087119449,549454309698749,548342645247594,
    547227077498209,546107589966429,544984165948304,543856788516628,542725440517398,
    541590104566198,540450763044511,539307398095945,538159991622382,537008525280053,
    535852980475510,534693338361535,533529579832936,532361685522273,531189635795474,
    530013410747366,528832990197099,527648353683477,526459480460176,525266349490864,
    524068939444201,522867228688737,521661195287686,520450816993585,519236071242825,
    518016935150065,516793385502511,515565398754059,514332951019306,513096018067422,
    511854575315868,510608597823974,509358060286361,508102937026203,506843201988326,
    505578828732147,504309790424430,503036059831871,501757609313504,500474410812908,
    499186435850227,497893655513994,496596040452741,495293560866399,493986186497484,
    492673886622049,491356630040413,490034385067642,488707119523785,487374800723855,
    486037395467548,484694870028683,483347190144371,481994321003884,480636227237230,
    479272872903419,477904221478402,476530235842688,475150878268614,473766110407264,
    472375893275020,470980187239737,469578952006528,468172146603144,466759729364933,
    465341657919366,463917889170121,462488379280693,461053083657528,459611956932660,
    458164952945825,456712024726048,455253124472666,453788203535783,452317212396122,
    450840100644263,449356816959232,447867309086426,446371523814845,444869406953606,
    443360903307702,441845956652994,440324509710390,438796504119184,437261880409521,
    435720577973963,434172535038095,432617688630160,431055974549665,429487327334917,
    427911680229457,426328965147325,424739112637127],
   [423142051844837,421537710475293,419926014752313,418306889377393,416680257486902,
    415046040607725,413404158611271,411754529665783,410097070186860,408431694786131,
    406758316217962,405076845324136,403387190976396,401689260016743,399982957195397,
    398268185106297,396544844120023,394812832314010,393072045399928,391322376648077,
    389563716808644,387795954029680,386018973771600,384232658718050,382436888682936,
    380631540513415,378816487988632,376991601713978,375156749010611,373311793799993,
    371456596483159,369591013814417,367714898769176,365828100405547,363930463719364,
    362021829492249,360102034132285,358170909506875,356228282767301,354273976164482,
    352307806855374,350329586699444,348339122044566,346336213501676,344320655707449,
    342292237074222,340250739526293,338195938221700,336127601258486,334045489364367,
    331949355568663,329838944855221,327713993794972,325574230156650,323419372494050,
    321249129708094,319063200581784,316861273285966,314643024853646,312408120620357,
    310156213627884,307886943988352,305599938205414,303294808448963,300971151779392,
    298628549317079,296266565352266,293884746390038,291482620124523,289059694335781,
    286615455702164,284149368520074,281660873322149,279149385383853,276614293107255,
    274054956269419,271470704121294,268860833321195,266224605684956,263561245732460,
    260869938007589,258149824145455,255399999657188,252619510398301,249807348681727,
    246962448990832,244083683240914,241169855529679,238219696307679,235231855888415,
    232204897204322,229137287698696,226027390224175,222873452794824,219673597010264,
    216425804935278,213127904175309,209777550835081,206372209981399,202909133148294,
    199385332318175,195797549679828,192142222294026,188415440577790,184612899231988,
    180729838859957,176760976023411,172700418807122,168541564044817,164276971089712,
    159898205235310,155395641360917,150758214708219,145973100274322,141025294118259,
    135897057203053,130567162225920,125009850768203,119193351704841,113077711678621,
    106611501606132,99726593251070,92329412327984,84285237941894,75387295918106,65287499995831,
    53307122100276,37693863435260]]
private def rkmC_w128_s4_1 : List ℤ := pzigCat
  [
   [366886815,539740381,710690781,505816389,401147980,1831317170,4138609520,7182401576,
    10053493044,11755583756,10267574834,2531070600,15088124917,46062791757,93670446463,
    157779973955,233120238485,306241244309,350178027045,320177596559,148295562649,262499873276,
    1042942653082,2360236783198,4420136581378,7465175521416,11769365625766,17629647535896,
    25353796887058,35242698139864,47572168311270,62570979153856,80398280222398,101123568075922,
    124707784221286,150989451180388,179677295045054,210349853567884,242462140222950,
    275361066890790,308308196406918,340508239065954,371141652481834,399402095869536,
    424531302214966,445853184550988,462804542533562,474958605357240,482041794703858,
    483942435027024,480711165728558,472552564498518,459810474386310,442947639319974,
    422520063507228,399148919604902,373493625214982,346222794901450,317988965524188,
    289407028053612,261036120277052,233365945663020,206808047355984,181692540314402,
    158266926020802,136699765851648,117087240823748,99461468169226,83798895800114,70031683386690,
    58057659731834,47748866508282,38961507710942,31543569488802,25340431956840,20200968482966,
    15981266903474,12547528021480,9777470467140,7562236733108,5805530251312,4423848686318,
    3346325348586,2512720169674,1872798699552,1385657694182,1017714040810,741801515570,
    536389799568,384943910948,273817017436,192946763498,134723593876,92906664732,63080639142,
    42163006334,27578574450,17401704312,10486039692,6030714384,2939364420,1157578844,330269948]]
private def rkmC_w128_s4_2 : List ℤ := pzigCat
  [
   [334848631,800183009,1321819565,2014884029,2141468691,1380222791,752354750,4831026366,
    11136762292,18942430614,26411471404,30810879964,26836672600,7915461736,33508104155,
    104988970315,211361619209,350381437473,508583734647,654652832039,731932205795,651598163395,
    285532152693,539658331700,2045456139888,4500892181546,8217907052524,13542644991786,
    20838397733710,30466545844404,42762783851016,58009057591312,76405988427058,98047043070342,
    122895057046486,150765083732998,181316437095722,214052930959896,248332461008514,
    283389267116058,318362349926534,352332557720096,384364916866896,413552675360062,
    439060434987878,460164267394444,476285211856440,487013752675488,492125768388556,
    491587646917682,485549938583786,474334263212644,458409993662836,438365580640318,
    414876617325842,388672274261482,360501074337010,331100020467074,301168277193886,
    271343819336852,242186922163976,214169869891382,187670697705494,162972656910410,
    140269091963658,119669492613524,101209790461020,84863402563502,70553400023126,58163732545410,
    47550815819358,38554278249808,31004770833000,24731703580744,19569657092846,15361872829468,
    11963430739864,9243715823076,7086798593748,5391011308374,4069378461280,3048107490794,
    2265794918892,1671210866016,1223043679224,888264546110,639943768842,457101958372,
    323787489578,227322550484,157855173670,108283668084,73369687554,48947537346,31914729456,
    20140312464,12406191120,7048956056,3476318058,1452880568,427577152]]
private def rkmC_w128_s4_3 : List ℤ := pzigCat
  [
   [522645012,498991606,226293218,676333635,2222611523,3905510855,5550548845,6182945631,
    4468596617,759827262,10582748898,25514619618,44076233176,62514628976,73672321268,66500984598,
    26623544722,61189620949,211039627439,429561762157,708568226619,1017335520799,1291184939879,
    1421092426475,1244920101925,539943757941,980202497084,3662548548146,7905112952340,
    14141175501536,22814761337004,34350708470312,49120418277644,67405867424152,89363493342074,
    114994859035184,144123037815962,176379332055386,211204165502430,247859441477778,
    285454526761622,322984675568212,359378201061364,393549681788954,424455136117274,
    451146316422336,472818230189266,488847967633188,498822419865372,502553624856396,
    500078527754952,491648685674012,477707758560700,458859055877512,435828405616138,
    409423327533164,380491462324366,349880778985430,318404769264270,286813885125870,
    255772358415236,225842940638620,197479699348598,171025782016076,146716627597904,
    124689205942814,104993258856746,87604301021928,72437657820904,59364050350488,48221846709806,
    38829686119802,30997059274728,24532848062946,19252341277378,14981518446364,11560804693652,
    8847462685206,6715457953850,5055410256758,3774683751152,2795737131532,2053976948276,
    1496623108936,1081516123894,775132164272,550821857388,387835153764,270429983320,186728427580,
    127502843890,85995004844,56856322220,36926050172,23522761910,14281503376,7979172242,
    4020586510,1742247854,511635232]]
private def rkmC_w128_s4_4 : List ℤ := pzigCat
  [
   [247942906,813567658,1421200526,1735095334,1523631528,399432454,1958009675,5783238667,
    10320463591,14282327761,15599757283,10813360649,3115461362,28084145106,64016667806,
    106376365100,144437689588,160956629636,131794406206,28404666672,177422013443,504758593925,
    953676850023,1491080278959,2035326634167,2441825887395,2490765867119,1878924719531,
    218863712745,2951364644602,8150458563996,15925458791828,26812287500702,41291661670280,
    59741639703842,82389825513090,109272391953888,140203637054240,174759253349314,
    212276576471000,251872815147662,292481363906988,332902640921754,371866509143846,
    408101687362872,440407317137800,467717872635770,489160850949524,504100635442774,
    512166102985744,513260315395394,507553788706776,495462776807446,477612732398996,
    454793680491896,427910869149468,397932139945584,365837854805540,332576377665584,
    299026294208626,265967436164066,234060812893014,203837633235844,175697446345266,
    149912769132562,126638512228784,105926412241140,87742394112710,71983826288494,58496397181058,
    47090880795296,37558067709056,29680595382590,23242489219712,18037079360614,13872640016664,
    10575462880174,7991280475636,5985871000990,4444779641874,3271986438890,2387960337662,
    1727718875824,1239047510202,880671589738,620322693906,432938895766,299220645114,204582365980,
    138129958520,92079074098,60320921030,38896977918,24425794396,14402887368,7700933898,
    3664756412,1484455868,408528106]]
private def rkmC_w128_s4_5 : List ℤ := pzigCat
  [
   [298537051,356488535,4604386,970346644,2501637416,4232746628,5034794904,3948493584,109085904,
    7287090209,17687882869,28691222885,35990665275,33674189209,14841410339,26395305350,
    91335264194,174095423564,258653290108,315643464530,303269816040,171717407154,129532647931,
    638126786207,1360017228521,2248547364601,3182277594739,3944394491179,4208271791725,
    3532620405009,1369224594115,2914854182362,10000242317464,20564346156580,35220637445934,
    54454129502978,78558282342568,107579831577056,141279667400704,179114941363718,
    220244056525448,263556341995260,307726016884034,351285661751172,392711429159406,
    430514865574488,463332830613602,490008724709138,509655829729610,521701930085316,
    525910507137198,522378939930262,511514700219704,493993085052246,470703025794870,
    442683666052372,411057969354920,376969487627260,341525006497066,305747026597134,
    270537625974712,236653624577514,204694389589488,175100749799278,148161765899478,
    124028477429460,102733131177472,84210581335942,68320118978700,54867052739952,43622346966480,
    34339188987844,26766886284086,20662104724988,15796690588422,11962316791310,8973245719380,
    6667840357374,4908488238380,3579948457126,2586985511836,1852103329814,1313436367102,
    922481268230,641651462670,441999870414,301408178116,203234779790,135222868630,88519347624,
    56796863182,35540073376,21526060034,12468155534,6765107994,3310856100,1347276644,358666988]]
private def rkmC_w128_s4_6 : List ℤ := pzigCat
  [
   [227201675,973309845,1823902977,2028061021,1280657863,906709824,4700013952,9104416562,
    12252216514,11708410576,5114730336,9414657119,31226457165,55727475851,74786745479,
    76450674159,46544775083,26839459088,147481493258,304713787798,468212030820,584410940158,
    577683535488,359905604882,152829607215,1016421938827,2227411929573,3688833896669,
    5178925213259,6327412331585,6605501093467,5334530953725,1716263636209,5114162330460,
    16016173766522,31759086436564,52931874199410,79857505526854,112523697161218,150538577859556,
    193116902377732,239101295406492,287018657934860,335166261141178,381719584983536,
    424852554660754,462858732744744,494261950153714,517907134053656,533024278227872,
    539260964706482,536682779692576,525744534340846,507236902898116,482214469274738,
    451913027180192,417664449582936,380815779953088,342657368302970,304364086531326,
    266952613791488,231255509402888,197910543719694,167362953413182,139878412131976,
    115564255128564,94395816243124,76244617963880,60905971572020,48124577376924,37617234908718,
    29091878011558,22262386102740,16859163325178,12636042860936,9374213243378,6883922293534,
    5004111050556,3601078808466,2565303511584,1809269911486,1263137603048,872910378690,
    597015016074,403731848498,269777817618,177992352320,115626037632,73663274444,45918520956,
    27950376080,16485159836,9253426448,4803841024,2211226984,834797196,206056330]]
private def rkmC_w128_s4_7 : List ℤ := pzigCat
  [
   [263334331,188334742,918657034,1284042352,828815808,562388053,2651124325,4823993463,
    5851618823,4152060603,1152185386,9686606528,19728795172,27504661122,27221897574,13149975336,
    17764814207,63633202383,115010277415,153309167469,152761490071,86141501643,66546613154,
    306678029224,604860490386,892252438076,1059404845314,965760970990,462352871002,571913631989,
    2183414016875,4292121189657,6642982537419,8770301019959,9984902552759,9391167669579,
    5937205587287,1502008081366,14014828490642,32527502699200,57679293009424,89711948070490,
    128390318536158,172963822177604,222179686593038,274345133853752,327435416773016,
    379235267969126,427500105089524,470121317873110,505276286453176,531550757846292,
    548022745916788,554302274390234,550527757734382,537321028846778,515709250492012,
    487025356259716,452797065037676,414635062745566,374130740861660,332768490937650,
    291859193088972,252495519870172,215530734890636,181574558380214,151007011406650,
    124003439371358,100566780148374,80564363749740,63764043392508,49868373373376,38544364466388,
    29447314007450,22239848341156,16606376713292,12260815680372,8951795651108,6463432321024,
    4615564433522,3260073943312,2277449059386,1573621092822,1075329541612,726383673588,
    484797320690,319455598782,207669067040,132777137016,83587181326,51565031016,30985247556,
    18092961466,10103403702,5185025794,2312594502,825897444]]
private def rkmC_w128_s4_8 : List ℤ := pzigCat
  [
   [604353391,931035149,811706347,168891460,1587342764,2957084114,3371206846,1917896942,
    1696310937,6991025751,11967485337,13748441663,9006463309,4277561954,24721660222,46945918580,
    60987307992,54137965296,15231647956,59263735523,158959791241,256004085953,306648951715,
    257656683705,62527128959,297903421978,792702374208,1324388599508,1723830883844,1764330769918,
    1198285259534,183356778127,2474054399871,5571605153235,9106611500267,12396608193147,
    14441823636159,13971521434051,9542506508109,315220627564,16925132791992,41280304189254,
    73877566435234,114592012488932,162613493509936,216456666063400,274044609027152,
    332858956565424,390139177539442,443107947672684,489196943783652,526246025928492,
    552659790852030,567503221252004,570534071868610,562173164634502,543422293174656,
    515741134937472,480901122347472,440834894975326,397491640468558,352713401629670,
    308138582455702,265137028264732,224774748780390,187809242038544,154705483049776,
    125669173699734,100691588635018,79597019524730,62091140589146,47805103742126,36333586017068,
    27264395021488,20202417327928,14783792318556,10685387110388,7629032001006,5381033672766,
    3749564171126,2581413051610,1755561964940,1179246024842,782154059356,511916196524,
    330447209220,210281068280,131549766488,80944360738,48710384406,28511040060,16140929002,
    8553370164,4228187072,1620279948,368287784]]
private def rkmC_w128_s4_9 : List ℤ := pzigCat
  [
   [264335224,170618733,1122960741,2273253677,2511834643,1266229793,1297184934,4868500136,
    7897633462,7869101886,2699183026,7730029037,20451585383,30077625153,28792816663,10131846843,
    27494639786,75990816486,116727176710,123840257514,71904393622,51759152295,234721192553,
    429732571861,556140308237,514334209565,216150663311,376986682384,1213408637106,2121548751332,
    2806227609754,2882797643546,1950627445368,298414622457,3949589165135,8742689273857,
    13979676100591,18491892220311,20686417935601,18677601053641,10491696375721,5676308067030,
    31193026583306,66743300553150,112152708444988,166308014655332,227191310788692,
    292023241650718,357502499601478,420105021357490,476407199021862,523391895325328,
    558699689466654,580800727102346,589074286123492,583792516204626,566024121660014,
    537474015206880,500285264568336,456830133441388,409509185971150,360582270358648,
    312037331342492,265506171014742,222224296557128,183029815363170,148393286733978,
    118468769094600,93156236317486,72169010435222,55095948084662,41458043447020,30754174662528,
    22494499228460,16225513174386,11543264911240,8100670638862,5608054887432,3830015617950,
    2580541996522,1714958359964,1124061592678,726295637924,462527357904,289975169830,
    178949527286,108414089420,64212206330,37193594400,20732470884,11033862736,5327352532,
    2226187192,504481342]]
private def rkmC_w128_s4_10 : List ℤ := pzigCat
  [
   [305838213,306123773,242282948,1230878152,1697926220,815451486,1211164071,3755445453,
    6057189965,5622694645,799114701,7535512274,16136389310,19851244984,12785174884,7044280683,
    35854574777,61642379129,66622721301,34934363633,38154800288,137427340050,224514559000,
    245960186680,149787173084,87841761935,435478990567,793039348275,998522639087,867187970829,
    254090508655,868163673086,2340712239212,3785898720534,4634247744492,4224181605550,
    1968387280440,2439529269721,8817085560153,16337150678567,23469247673129,28051664999079,
    27502827275639,19148208098935,620071317393,29740270013860,72543680054124,127140478332448,
    191576464153838,262725467016494,336584749592168,408684446932374,474554081305900,
    530174965298650,572362309783572,599029077848126,609309627492996,603540487146652,
    583117387965408,550261168557734,507730698316868,458527889728988,405623448204040,
    351734997286038,299167553705286,249723169422084,204672728034376,164780700981278,
    130366451145852,101388148452936,77536554258650,58323399213138,43162440214182,31433493119150,
    22531615327890,15899274452532,11046342890564,7557033944082,5091106610896,3377479509922,
    2206495769782,1419146658336,898488722060,559622463874,342838843820,206227492336,121710669650,
    70150532262,39405724300,21235821108,10848619624,4930185678,1883187538,385403070]]
private def rkmC_w128_s4_11 : List ℤ := pzigCat
  [
   [288450862,510533766,209960930,739312043,1553492271,1441890585,212530254,2670640220,
    4559551580,4276298508,204489032,6899858577,13876369097,14865403903,5481226427,13535362356,
    34956326626,45247115014,31281578636,12986748793,76793080477,131099072039,136017350851,
    59233715369,102082023778,303807355178,454744948542,441037542486,172956070898,356466813313,
    1027504390331,1586631322093,1698913042991,1054722381937,485461652706,2755621051394,
    5209190729774,6951968606250,6907805255280,4103786449360,1976771589457,11057274644107,
    21837119417789,31952602657581,38166535103911,36784417931833,24231802803401,2307916430434,
    44319461448018,101557528899536,171909438071110,251543787513704,335325735502262,
    417422519111320,491998743787974,553885941844146,599130621554908,625346289682194,
    631842297078380,619533451474296,590674269531214,548475177457780,496672091965708,
    439108004675644,379379542147318,320575598798194,265122604129130,214727719778334,
    170406778539750,132570336785572,101145513006504,75708837532952,55614214619878,40104206535034,
    28396379055158,19747081230726,13488944915560,9052068796604,5968235152874,3866265655546,
    2460599326300,1538325014144,944618515480,569275314506,336646566906,194972922284,110384342608,
    60866010900,32327909052,16443662378,7627735496,3079105392,892122428]]
private def rkmC_w128_s4_12 : List ℤ := pzigCat
  [
   [329516029,574859137,420643251,143252752,1251768492,1933825188,949895128,1610043265,
    4387712505,4693617727,1008376895,5960548782,12125984360,12226332298,1859141996,16477850621,
    33105387299,33929056429,9143685399,37576650974,84319613116,97724612724,48458483112,
    65086305285,202575177393,285356627467,227759352717,13638347150,391752959814,753157994012,
    872548697946,544822392372,295063214273,1470739194491,2541546118299,2895689857423,
    1963254111551,506677282002,4195820050076,8106152962658,10671828983296,10121194173048,
    5030296162948,5061576536101,19151072811953,34552535503255,47070698284583,51579804005835,
    42911605584569,16876580771025,28808717770228,93888851858486,175377858213074,267849520216712,
    364150323631064,456389346444188,537013078935888,599772431780758,640426587701876,
    657097094351908,650254438458290,622393593666476,577490350385990,520356607616996,
    456007309725280,389121863472884,323658313780812,262634101287852,208065331928838,
    161030564953320,121818706855426,90120125808276,65224272200460,46198258201590,32033330858672,
    21749056182382,14461800026912,9419136206350,6009373044832,3755607489030,2299029984280,
    1378218598146,808776939144,464346147156,260489065332,142430779142,75576715442,38881806148,
    18879010946,8316436054,3145033542,823069652]]
private def rkmC_w128_s4_13 : List ℤ := pzigCat
  [
   [230597349,244485713,509306286,919031244,516889656,870503357,2170880917,2073365335,380141174,
    3901355420,5781753652,2817082900,4694244753,12133919459,12416585765,1336556057,17630718662,
    32076232712,26639037542,5165005539,51658418285,81883085263,62017988109,20428266654,
    134484831908,208877345812,164373096408,31450544623,318072938381,539033226445,502067326215,
    91494665311,619927966350,1327901191104,1577461339892,966143598084,596209550321,2697126729253,
    4424027966811,4626332789231,2398069253381,2380066565864,8660380778048,14229096056758,
    16190988813972,11875134440608,72010026549,18748420334529,40551634538623,59445628118061,
    67957535262921,58701869358621,26071290970125,32334833394870,114900454298726,216002270636674,
    326829675808416,436809382454868,535308001327222,613247391537630,664325606689932,
    685658406447510,677797846063544,644217054941474,590440504990400,523028422731062,
    448613263925368,373128755999722,301309471101132,236467305717220,180508505898506,
    134121393507714,97056932191218,68437465602692,47040858551882,31528895207364,20610846425860,
    13143496381850,8177117876122,4963203451658,2938598845280,1696826079474,955184758328,
    523782879010,279360991294,144520671780,72144705340,34414107730,15344565270,6295700850,
    1982312238,286941266]]
private def rkmC_w128_s4_14 : List ℤ := pzigCat
  [
   [384323520,80350447,1081070463,1657115793,494414435,1887482534,3411038032,1707549920,
    2854752161,6859549607,5621725111,2372108868,12253569206,15193407164,3717159004,18145091549,
    34231723395,25191198085,14067224806,62071983962,78108497044,29592484674,74130974197,
    168843982445,165504578767,13791577171,235479820174,424057645528,362639693892,32068096089,
    622413052987,1052173523485,909002294945,1264675524,1418498950364,2603407564506,2618553969008,
    850644634608,2463802523079,6022058807425,7774536113753,5779096691133,703343837332,
    10355438922608,19677667203098,23836877201208,18353285138780,1106604442458,26065222181921,
    56837850580697,81283132365339,88025517161123,67099841573205,12690330887471,75045586946342,
    189577412105568,319109682996602,448861531188716,563889022752970,651744133533618,
    704389859573092,719048059879980,697959748991712,647292091128130,575568645260620,
    492022928929002,405201385532498,322010687809962,247260795323550,183647465711128,
    132046051800030,91974628357098,62092484611588,40644780928604,25803854525458,15890490686264,
    9492525642156,5500155895600,3090435677442,1683242624816,887764920486,452914536404,
    222920804786,105509071912,47526102576,20094758374,7526630986,2270629694,283282016]]
private def rkmC_w128_s4_15 : List ℤ := pzigCat
  [
   [279192476,566077240,215375351,1126661019,839954861,854174022,2466722144,1762385106,
    1559866845,5024548571,4164430589,2192174318,9178508466,8867021590,2566483443,17390721277,
    19693114761,436809877,30061929008,43016430120,14737657984,45715542437,89440222057,
    60227895455,49684145138,167728408640,176122888190,8794680530,258833079913,415509392185,
    252232764723,241446709340,775819098458,882356271308,245834640598,954014896349,1971668211551,
    1857886371061,134820609961,2624563614560,4783575379874,4403369923332,509062649478,
    5839014993989,11441178771939,12185505523139,5252272543929,8723730293492,24761724442228,
    34709867391536,30357886857880,7388365395506,31490232459455,75704314586917,108900111993731,
    113427013036379,75736209538363,9150193596526,135600224837808,288363093335568,446163496565560,
    586673774539744,691348324076484,748844287496244,756347688634526,718829922457732,
    646802201618570,553413608348198,451697151554580,352533052361656,263564954372242,
    189015893580862,130156243053578,86118105694300,54775296619724,33499407007944,19699930626494,
    11137495854046,6050822768396,3157026341486,1580034751068,757345668644,346873286050,
    151060099424,61937219208,23432835804,7782552332,1965471500]]
private def rkmC_w128_s4_16 : List ℤ := pzigCat
  [
   [361926413,1046444067,592296841,1302041166,2651434044,1093506310,2850486709,4715446161,
    582625301,6619820466,8546639024,241602257,13411004625,15308592949,2206821756,26077161160,
    28152926254,6019860431,50844895461,54214038831,9672139330,95617329114,108084729280,
    5824931891,173079924607,221665316853,33997270979,292861981796,455561762632,187837268620,
    430982774951,901892048153,644287987889,434085736932,1624116001242,1770428482834,211653770414,
    2370049119819,4009860801303,2717717858377,1752748009612,6968051047048,8778315605300,
    4036477424838,6505423870097,17268337624865,20157997218133,9398381977263,13705268998452,
    39180300453356,51690243155674,37817506784282,5987424160685,68858079115395,127060080472311,
    151496741143019,118230726938657,17693178390399,141107251258318,332834752151054,
    523342996364600,679393109409742,777091289563988,806551672385372,772005260094926,
    688234452749494,575171472080894,452604157469090,336372805508154,236593999666050,
    157705491667470,99695070283168,59784248624672,34000740095720,18326225613338,9350540906302,
    4508376013664,2049073707330,874657743866,348899577346,128788853798,43148790884,12532565180,
    2717645000]]
private def rkmC_w128_s4_17 : List ℤ := pzigCat
  [
   [646365608,287165801,1393618539,332768787,2257171466,2537959426,1403359501,5797173255,
    3585543481,4987592896,9889862262,1817731998,13534142933,15462662533,5866912638,29568261224,
    20221953338,24558669357,55323547187,19051366427,64152752686,95712427070,4603086048,
    140432912001,160181647669,35810709554,282807238062,265995799964,122798851697,545506545859,
    457289370435,277893370822,1027190572178,842686446456,498944296195,1901873677971,
    1689236771383,664655059526,3423991503652,3600356808156,239158780443,5749604855133,
    7747846568221,2462798306593,8055859805276,15653479114274,11535335539778,5776510925077,
    26371722094645,33418198978579,14786024992925,25625766359520,65600323545280,74994434072960,
    34054622559180,51048032931563,145460748339561,198573119664643,166511488684857,32746270679283,
    183374598301644,433676995988930,659475525048902,812121168452066,867122424058354,
    827485416574824,717284481927318,570121524065722,417858394982932,283305340667764,
    177931284238006,103514473364388,55705852789362,27653238717218,12607845213980,5245253487144,
    1972581992584,660889788076,192688827038,46559253926,7988765352,258304302]]
private def rkmC_w128_s4_18 : List ℤ := pzigCat
  [
   [243425226,629643519,727445963,787714526,1453440754,168844977,2528110223,1047994111,
    3295019672,3839671034,2781734329,8150218329,1449725085,11843985900,10561696850,10282651141,
    23105339265,1461853211,32982339236,26195692814,30140746479,62496473001,3492633963,
    91064205028,78360827592,73117386547,177756928863,38333008501,234420957242,259380988886,
    124821339603,499284766759,263999761805,504818253188,865572188556,65974645508,1230079046951,
    1305801912613,533249455528,2491380556048,1782174632778,1839064690011,4633202835397,
    2327498325045,4310468352578,8375206423352,3302926351166,8563806119785,15291975898709,
    6164634669981,14981277430374,28573504791092,15537099689560,21486672632903,53042598230711,
    43673554904283,15082160201422,87843737942356,113584528658344,50096481143618,87245032624927,
    223115574272473,261465314893205,141673595021615,124563045856216,457696357963872,
    750652511824066,918770612152342,931651437542774,814453472484186,625137495732204,
    424706245045040,255838821400236,136186647324182,63493621829712,25504810145602,8572759065068,
    2277619782870,413070816558]]
private def rkmHbWin_w128_s5 : List ℤ := altBuildHbFrom 2048 1024 18305500000 0 1024
private def rkmXsWin_w128_s5_in : List ℤ := pzigCat
  [
   [423472422,996809350,109113907,1937775277,595665257,3155012320,2298017298,3757488337,
    4587380369,4214066292,8666219654,3167395587,14203375347,1326601657,20794060398,11473144344,
    25504173719,29228496103,23690087964,54923347328,8436811269,85737882209,30392667447,
    112208116644,103649979842,112116362829,215181046719,46864433208,345667821104,129004776920,
    436975035531,453005984297,370871113228,903054791145,26570333904,1320159891631,916806393627,
    1330876398178,2280255056576,349773655099,3625825953993,2177416789452,3702965745644,
    6103068200201,600157501826,9510768104246,7097575287847,7940733813107,17517731679677,
    4192909417755,21979733341862,27363435977924,5375982107932,46000530567738,40622371352620,
    23820007297084,87164179034256,66746738258918,48352569352948,160528539441280,139747981862904,
    47010371849404,277208918374802,351117554044396,146504901876060,281519632131914,
    736021722782084,1012362184684096,1020827692873310,814345367147462,524092082515012,
    269396390268270,105754070000694,27719048364095]]
private def rkmXsWin_w128_s5_out : List ℤ := pzigCat
  [
   [485768467,67595949,1236879328,13630511,2573817031,1637260908,1316011270,3116563246,
    15028770845,22124047282,31141304741,68559755588,134350584325,200854537118,275466299197,
    386429501536,485992388163,460690665296,290553257959,66848712986,186412992044,474884659003,
    586854943924,285701786241,149151130753,171936934440,99441190722,4797508303,388017031163,
    173543240182,1060302160158,2998619944579,5313994883066,6718405302703,4594665214542,
    978597574688,4466200906661,963035103106,6274942453882,9385789217585,6277459849712,
    2188549634593,1158660036859,8921066761618,18099754880087,17212421692250,1110330910805,
    25850287620347,30908032470106,3582517105003,26005518796059,38574645590888,47706070750329,
    31581202985346,41310226384964,89045333916263,55452787765880,2555282797630,103422236151655,
    112928827446820,15407497301642,91839289602535,134035323341550,108670162903558,79525674702865,
    96210050995558,303801552310562,132802858454214,53130495540307,392223335146916,
    1056338513101098,1359128409235814,819787588709030]]
private def rkmHbN_w128_s5 : List ℕ := rkmCatN
  [
   [53018391277610,74924409263804,91696019061813,105803763074010,118205347815707,129392317657616,
    139656890888150,149189604884622,158122904761634,166553293658870,174553676853008,
    182180735741485,189479578815298,196486806384648,203232604183352,209742217471689,
    216037016008398,222135280702894,228052796022227,233803303761539,239398855895158,
    244850092664977,250166464408029,255356410444697,260427504773593,265386575807451,
    270239805591264,274992812644973,279650721619242,284218222243939,288699619515875,
    293098876667369,297419652146397,301665331598502,305839055652670,309943744165491,
    313982117460605,317956715006737,321869911902317,325723933473772,329520868244988,
    333262679494886,336951215586706,340588219225014,344175335773533,347714120747814,
    351206046580724,354652508745286,358054831308010,361414271976220,364732026694664,
    368009233839706,371246978053378,374446293754420,377608168359011,380733545240023,
    383823326450308,386878375232668,389899518336580,392887548159591,395843224729355,
    398767277540583,401660407259700,404523287308686,407356565338418,410160864600808,
    412936785228108,415684905426975,418405782594121,421099954359786,423767939564651,
    426410239175327,429027337143071,431619701209996,434187783666638,436732022064434,
    439252839886350,441750647178635,444225841146414,446678806715635,449109917063662,
    451519534120626,453908009043495,456275682664645,458622885916605,460949940234493,
    463257157937577,465544842591264,467813289350724,470062785287297,472293609698711,
    474506034404092,476700324024664,478876736250987,481035522097509,483176926145163,
    485301186772694,487408536377344,489499201585498,491573403453830,493631357661487,
    495673274693780,497699360017843,499709814250692,501704833320069,503684608618462,
    505649327150645,507599171675062,509534320839384,511454949310515,513361227899332,
    515253323680409,517131400106983,518995617121382,520846131261128,522683095760943,
    524506660650818,526316972850356,528114176259554,529898411846173,531669817729881,
    533428529263276,535174679109971,536908397319833,538629811401532,540339046392489,
    542036224926368,543721467298186],
   [545394891527167,547056613417417,548706746616526,550345402672177,551972691086842,
    553588719370646,555193593092480,556787415929420,558370289714534,559942314483130,
    561503588517516,563054208390326,564594269006462,566123863643720,567643083992138,
    569152020192119,570650760871374,572139393180737,573618002828880,575086674115984,
    576545489966392,577994531960289,579433880364442,580863614162037,582283811081634,
    583694547625289,585095899095860,586487939623528,587870742191560,589244378661348,
    590608919796740,591964435287686,593310993773232,594648662863878,595977509163320,
    597297598289598,598608994895676,599911762689460,601205964453285,602491662062880,
    603768916505835,605037787899574,606298335508868,607550617762885,608794692271804,
    610030615842999,611258444496808,612478233481908,613690037290298,614893909671898,
    616089903648799,617278071529147,618458464920686,619631134743974,620796131245271,
    621953504009115,623103301970594,624245573427326,625380366051149,626507726899536,
    627627702426739,628740338494670,629845680383527,630943772802180,632034659898305,
    633118385268294,634194991966932,635264522516861,636327018917817,637382522655676,
    638431074711279,639472715569073,640507485225552,641535423197520,642556568530163,
    643570959804947,644578635147352,645579632234427,646573988302186,647561740152850,
    648542924161930,649517576285158,650485732065274,651447426638672,652402694741902,
    653351570718040,654294088522923,655230281731260,656160183542610,657083826787246,
    658001243931893,658912467085351,659817528004007,660716458097235,661609288432687,
    662496049741479,663376772423273,664251486551264,665120221877061,665983007835479,
    666839873549234,667690847833548,668535959200666,669375235864286,670208705743903,
    671036396469066,671858335383569,672674549549542,673485065751484,674289910500204,
    675089110036706,675882690335983,676670677110757,677453095815138,678229971648225,
    679001329557633,679767194242964,680527590159207,681282541520084,682032072301328,
    682776206243910,683514966857205,684248377422097,684976460994040,685699240406053,
    686416738271672,687128976987843,687835978737769],
   [688537765493710,689234359019722,689925780874369,690612052413367,691293194792200,
    691969228968679,692640175705468,693306055572557,693966888949703,694622696028820,
    695273496816342,695919311135531,696560158628759,697196058759748,697827030815773,
    698453093909826,699074266982749,699690568805333,700302017980376,700908632944715,
    701510431971222,702107433170766,702699654494147,703287113734000,703869828526662,
    704447816354017,705021094545307,705589680278917,706153590584130,706712842342856,
    707267452291335,707817437021809,708362812984173,708903596487599,709439803702131,
    709971450660265,710498553258494,711021127258836,711539188290337,712052751850550,
    712561833306997,713066447898597,713566610737091,714062336808424,714553640974125,
    715040537972658,715523042420748,716001168814703,716474931531697,716944344831049,
    717409422855479,717870179632339,718326629074840,718778784983245,719226661046058,
    719670270841188,720109627837097,720544745393939,720975636764669,721402315096152,
    721824793430242,722243084704853,722657201755016,723067157313918,723472964013924,
    723874634387592,724272180868666,724665615793061,725054951399830,725440199832119,
    725821373138112,726198483271957,726571542094683,726940561375103,727305552790707,
    727666527928540,728023498286068,728376475272031,728725470207294,729070494325671,
    729411558774748,729748674616695,730081852829061,730411104305567,730736439856875,
    731057870211365,731375406015884,731689057836495,731998836159215,732304751390741,
    732606813859164,732905033814684,733199421430300,733489986802504,733776739951963,
    734059690824183,734338849290180,734614225147125,734885828118998,735153667857217,
    735417753941273,735678095879344,735934703108913,736187584997369,736436750842604,
    736682209873605,736923971251030,737162044067784,737396437349589,737627160055539,
    737854221078651,738077629246416,738297393321332,738513522001434,738726023920825,
    738934907650188,739140181697298,739341854507529,739539934464351,739734429889822,
    739925349045074,740112700130791,740296491287688,740476730596971,740653426080805,
    740826585702768,740996217368301,741162328925150],
   [741324928163812,741484022817962,741639620564883,741791729025892,741940355766752,
    742085508298089,742227194075795,742365420501436,742500194922641,742631524633502,
    742759416874956,742883878835170,743004917649917,743122540402949,743236754126367,
    743347565800985,743454982356684,743559010672773,743659657578338,743756929852584,
    743850834225180,743941377376596,744028565938437,744112406493768,744192905577444,
    744270069676428,744343905230108,744414418630610,744481616223107,744545504306125,
    744606089131843,744663376906392,744717373790145,744768085898013,744815519299727,
    744859680020120,744900574039412,744938207293480,744972585674131,745003715029374,
    745031601163682,745056249838256,745077666771283,745095857638190,745110828071900,
    745122583663076,745131129960370,745136472470664,745138616659310,745137567950366,
    745133331726829,745125913330866,745115318064040,745101551187536,745084617922380,
    745064523449659,745041272910737,745014871407463,744985324002390,744952635718971,
    744916811541772,744877856416668,744835775251047,744790572913998,744742254236515,
    744690824011677,744636286994845,744578647903841,744517911419136,744454082184026,
    744387164804815,744317163850985,744244083855372,744167929314336,744088704687928,
    744006414400059,743921062838658,743832654355836,743741193268045,743646683856231,
    743549130365993,743448537007729,743344907956786,743238247353613,743128559303896,
    743015847878711,742900117114653,742781371013985,742659613544766,742534848640988,
    742407080202706,742276312096170,742142548153950,742005792175061,741866047925088,
    741723319136305,741577609507796,741428922705568,741277262362671,741122632079307,
    740965035422943,740804475928417,740640957098047,740474482401738,740305055277079,
    740132679129447,739957357332109,739779093226313,739597890121387,739413751294831,
    739226679992409,739036679428237,738843752784871,738647903213393,738449133833494,
    738247447733558,738042847970736,737835337571033,737624919529376,737411596809693,
    737195372344985,736976249037397,736754229758284,736529317348282,736301514617371,
    736070824344940,735837249279848,735600792140485],
   [735361455614826,735119242360495,734874155004812,734626196144851,734375368347489,
    734121674149456,733865116057381,733605696547841,733343418067402,733078283032663,
    732810293830298,732539452817089,732265762319972,731989224636064,731709842032702,
    731427616747474,731142550988246,730854646933196,730563906730835,730270332500036,
    729973926330056,729674690280555,729372626381623,729067736633789,728760023008043,
    728449487445850,728136131859162,727819958130428,727500968112607,727179163629172,
    726854546474116,726527118411960,726196881177752,725863836477068,725527985986012,
    725189331351214,724847874189823,724503616089501,724156558608418,723806703275238,
    723454051589110,723098605019655,722740365006949,722379332961505,722015510264258,
    721648898266543,721279498290070,720907311626902,720532339539430,720154583260343,
    719774043992600,719390722909398,719004621154136,718615739840385,718224080051847,
    717829642842318,717432429235643,717032440225682,716629676776255,716224139821104,
    715815830263838,715404748977889,714990896806454,714574274562443,714154883028423,
    713732722956562,713307795068564,712880100055610,712449638578292,712016411266550,
    711580418719601,711141661505869,710700140162913,710255855197354,709808807084795,
    709358996269746,708906423165542,708451088154259,707992991586632,707532133781963,
    707068515028037,706602135581027,706132995665401,705661095473826,705186435167072,
    704709014873906,704228834690996,703745894682800,703260194881463,702771735286705,
    702280515865708,701786536553004,701289797250358,700790297826644,700288038117729,
    699783017926346,699275237021968,698764695140678,698251391985036,697735327223947,
    697216500492525,696694911391948,696170559489321,695643444317529,695113565375090,
    694580922126003,694045513999597,693507340390373,692966400657849,692422694126393,
    691876220085063,691326977787438,690774966451448,690220185259201,689662633356807,
    689102309854196,688539213824941,687973344306068,687404700297869,686833280763710,
    686259084629839,685682110785182,685102358081147,684519825331417,683934511311741,
    683346414759726,682755534374615,682161868817078],
   [681565416708984,680966176633174,680364147133239,679759326713279,679151713837672,
    678541306930834,677928104376969,677312104519830,676693305662458,676071706066935,
    675447303954116,674820097503375,674190084852325,673557264096559,672921633289362,
    672283190441441,671641933520632,670997860451615,670350969115619,669701257350127,
    669048722948568,668393363660015,667735177188868,667074161194542,666410313291144,
    665743631047145,665074111985050,664401753581061,663726553264737,663048508418647,
    662367616378015,661683874430369,660997279815171,660307829723455,659615521297450,
    658920351630204,658222317765195,657521416695942,656817645365610,656111000666606,
    655401479440168,654689078475955,653973794511623,653255624232395,652534564270635,
    651810611205397,651083761561987,650354011811506,649621358370386,648885797599928,
    648147325805822,647405939237670,646661634088493,645914406494237,645164252533266,
    644411168225852,643655149533657,642896192359202,642134292545335,641369445874682,
    640601648069103,639830894789125,639057181633374,638280504138002,637500857776093,
    636718237957073,635932640026106,635144059263475,634352490883961,633557930036211,
    632760371802095,631959811196051,631156243164424,630349662584791,629540064265280,
    628727442943871,627911793287695,627093109892318,626271387281006,625446619903998,
    624618802137743,623787928284145,622953992569789,622116989145148,621276912083790,
    620433755381561,619587512955764,618738178644318,617885746204908,617030209314118,
    616171561566553,615309796473947,614444907464250,613576887880713,612705730980942,
    611831429935953,610953977829196,610073367655580,609189592320461,608302644638637,
    607412517333304,606519203035012,605622694280594,604722983512082,603820063075600,
    602913925220243,602004562096935,601091965757271,600176128152332,599257041131490,
    598334696441183,597409085723677,596480200515803,595548032247670,594612572241362,
    593673811709610,592731741754437,591786353365785,590837637420117,589885584678992,
    588930185787616,587971431273373,587009311544319,586043816887661,585074937468201,
    584102663326756,583126984378550,582147890411576],
   [581165371084926,580179415927098,579190014334267,578197155568521,577200828756077,
    576201022885452,575197726805606,574190929224054,573180618704932,572166783667042,
    571149412381850,570128492971447,569104013406480,568075961504035,567044324925483,
    566009091174289,564970247593773,563927781364832,562881679503619,561831928859174,
    560778516111013,559721427766666,558660650159172,557596169444520,556527971599045,
    555456042416766,554380367506680,553300932289992,552217721997299,551130721665713,
    550039916135926,548945290049217,547846827844398,546744513754695,545638331804574,
    544528265806488,543414299357571,542296415836252,541174598398806,540048829975831,
    538919093268648,537785370745629,536647644638446,535505896938240,534360109391707,
    533210263497100,532056340500149,530898321389888,529736186894391,528569917476418,
    527399493328964,526224894370708,525046100241362,523863090296921,522675843604799,
    521484338938857,520288554774329,519088469282614,517884060325970,516675305452068,
    515462181888433,514244666536749,513022735967040,511796366411699,510565533759397,
    509330213548832,508090380962337,506846010819333,505597077569626,504343555286542,
    503085417659898,501822637988792,500555189174232,499283043711568,498006173682750,
    496724550748379,495438146139572,494146930649617,492850874625413,491549947958699,
    490244120077053,488933359934665,487617636002863,486296916260402,484971168183490,
    483640358735561,482304454356764,480963420953187,479617223885782,478265827958995,
    476909197409089,475547295892144,474180086471735,472807531606265,471429593135945,
    470046232269417,468657409569994,467263084941516,465863217613799,464457766127672,
    463046688319581,461629941305745,460207481465851,458779264426273,457345245042789,
    455905377382789,454459614706947,453007909450346,451550213203019,450086476689911,
    448616649750207,447140681316039,445658519390514,444170111025058,442675402296043,
    441174338280677,439666863032104,438152919553722,436632449772646,435105394512317,
    433571693464199,432031285158535,430484106934133,428930094907124,427369183938658,
    425801307601504,424226398145490,422644386461740],
   [421055202045667,419458772958654,417855025788367,416243885607659,414625275931976,
    412999118675215,411365334103963,409723840790040,408074555561267,406417393450391,
    404752267642054,403079089417751,401397768098649,399708210986187,398010323300336,
    396304008115423,394589166293379,392865696414300,391133494704185,389392454959702,
    387642468469838,385883423934272,384115207378307,382337702064169,380550788398496,
    378754343835809,376948242777752,375132356467859,373306552881636,371470696611655,
    369624648747424,367768266749712,365901404319021,364023911257875,362135633326560,
    360236412091929,358326084768867,356404484053971,354471437950979,352526769587431,
    350570297022029,348601833042110,346621184950599,344628154341779,342622536865135,
    340604121976511,338572692675709,336528025229642,334469888880046,332398045534678,
    330312249440868,328212246840149,326097775602631,323968564839636,321824334492995,
    319664794899270,317489646327004,315298578484921,313091269998832,310867387854768,
    308626586805641,306368508738468,304092781998911,301799020669560,299486823798024,
    297155774570510,294805439426089,292435367106393,290045087634863,287634111219088,
    285201927069018,282748002123033,280271779672951,277772677877977,275250088156455,
    272703373442898,270131866296251,267534866843567,264911640541251,262261415733698,
    259583380986449,256876682167897,254140419249925,251373642793692,248575350081836,
    245744480852633,242879912584864,239980455274177,237044845632284,234071740629062,
    231059710284269,228007229599455,224912669501335,221774286644408,218590211892181,
    215358437261479,212076801071549,208742970986726,205354424575585,201908426927029,
    198402004759755,194831916329406,191194616268441,187486214275143,183702426283230,
    179838516368410,175889227149227,171848695768173,167710351624437,163466790766976,
    159109620087538,154629261934547,150014706118810,145253190887714,140329786296653,
    135226840793940,129923231765495,124393327827899,118605514544759,112520035600627,
    106085715549780,99234762150401,91874062606221,83869560438074,75015501239083,64965515438492,
    53044222309144,37507965033064]]
private def rkmC_w128_s5_1 : List ℤ := pzigCat
  [
   [727355361,27334268,1714337832,46533781,3284397235,726134743,4908450040,2089673206,6770621401,
    4073799461,9108398294,7961772600,11472866871,14363074385,14101825310,24581347640,12141279187,
    46520210735,23880572032,27879226542,86686314532,264355117291,279107269288,357352735985,
    694981292720,699349913361,3196042215,516396961698,255300259749,105652302828,350252154719,
    157450676406,24650818697,443112286058,434278386952,2484837467095,1573657988156,4706388345506,
    10423134471649,4715568799652,1307743510546,2887113148311,460884701801,4487236390032,
    4119030284141,7314971993174,15329828855145,3640826536220,30381191645518,26415812540589,
    8320955122985,5129753961100,35548649213587,28206786556354,35652606041442,44981617573389,
    94691947740098,48445832865554,52155989572995,159082707365298,126799517333298,50858456955001,
    176195649924178,323265653103262,138244133915484,83805499048818,438062287791168,
    931104794237556,1165734341572854,973433730500658,614138304703774,173782484581170]]
private def rkmHbWin_w128_s6 : List ℤ := altBuildHbFrom 2048 1024 17895526315 0 1024
private def rkmXsWin_w128_s6_in : List ℤ := pzigCat
  [
   [485768467,67595949,1236879328,13630511,2573817031,1637260908,1316011270,3116563246,
    15028770845,22124047282,31141304741,68559755588,134350584325,200854537118,275466299197,
    386429501536,485992388163,460690665296,290553257959,66848712986,186412992044,474884659003,
    586854943923,285701786241,149151130753,171936934440,99441190721,4797508303,388017031163,
    173543240181,1060302160158,2998619944580,5313994883066,6718405302704,4594665214542,
    978597574688,4466200906661,963035103105,6274942453882,9385789217586,6277459849712,
    2188549634593,1158660036859,8921066761618,18099754880088,17212421692250,1110330910806,
    25850287620348,30908032470106,3582517105003,26005518796059,38574645590887,47706070750329,
    31581202985345,41310226384963,89045333916263,55452787765879,2555282797630,103422236151656,
    112928827446820,15407497301641,91839289602535,134035323341549,108670162903557,79525674702865,
    96210050995557,303801552310561,132802858454213,53130495540308,392223335146916,
    1056338513101098,1359128409235814,819787588709030]]
private def rkmXsWin_w128_s6_out : List ℤ := pzigCat
  [
   [273827159,1296638460,3431083763,6438423214,11348476549,19510377124,33242433343,55783285650,
    89133401895,133958433836,189840676365,256562940818,327350667853,382758660316,396603936553,
    354381284666,253535761835,98998139312,80547080112,209191134195,197946149658,38943018341,
    156738992891,248787490110,185514733683,39454777336,40104058458,38357148592,140367234995,
    19268829132,196469919474,33044460795,362898452879,312980689828,255348812691,738212770890,
    499563613469,89114984428,504560449715,957616248315,840053763902,661327116365,274061776218,
    543005112064,2070525260099,1156094591511,2566993095897,10859238066788,5645923968040,
    6545424504176,2959846653913,10756737679039,14626660633910,13036766800318,11901863545139,
    1925460131846,14669983373736,3041029010505,12812257023868,4581591295585,31693500361466,
    44073147848144,8227001567568,11003004448903,42468126871799,7426046290502,28779935953291,
    114073076596631,124762177319261,24836069768694,60470649955316,154862070671116,82478956090455,
    108717265113329,2794605413561,142718533897095,175824346217999,314857116826463,
    300351217849679,863216010507272,1712211950525534]]
private def rkmHbN_w128_s6 : List ℕ := rkmCatN
  [
   [51830980649938,73246387021181,89642376449779,103434160570155,115557996908564,126494421108449,
    136529106878259,145848324281621,154581552165527,162823132365804,170644337357789,
    178100579090863,185235955797125,192086248078816,198680965623946,205044788294833,
    211198607248770,217160293972224,222945279420125,228566997623587,234037230638480,
    239366380405686,244563685610576,249637396564803,254594917638175,259442924312910,
    264187460179670,268834017924885,273387607426505,277852813382258,282233844373376,
    286534574870822,290758581387233,294909173742547,298989422227587,303002181305245,
    306950110374242,310835692028845,314661248174299,318428954298173,322140852149345,
    325798861036746,329404787927297,332960336495601,336467115255482,339926644884848,
    343340364839664,346709639339654,350035762797268,353319964751960,356563414363860,
    359767224514023,362932455552618,366060118731334,369151179351978,372206559659450,
    375227141504046,378213768795207,381167249766359,384088359068356,386977839707117,
    389836404839442,392664739439490,395463501847144,398233325208363,400974818816580,
    403688569363367,406375142105745,409035081956858,411668914506069,414277146974000,
    416860269107509,419418754019186,421953058975495,424463626137382,426950883256793,
    429415244332286,431857110226628,434276869249060,436674897704649,439051560413003,
    441407211198394,443742193353207,446056840076466,448351474889069,450626412027207,
    452881956815385,455118406020294,457336048186752,459535163956790,461716026372927,
    463878901166574,466024047032444,468151715889807,470262153131340,472355597860292,
    474432283116630,476492436092781,478536278339557,480564025962805,482575889811277,
    484572075656211,486552784363059,488518212055777,490468550274069,492403986123961,
    494324702422027,496230877833617,498122687005372,500000300692323,501863885879829,
    503713605900629,505549620547230,507372086179856,509181155830186,510976979301064,
    512759703262379,514529471343295,516286424220993,518030699706094,519762432824907,
    521481755898648,523188798619768,524883688125512,526566549068837,528237503686804,
    529896671866547,531544171208932],
   [533180117090000,534804622720284,536417799202102,538019755584891,539610598918683,
    541190434305785,542759364950746,544317492208669,545864915631948,547401733015479,
    548928040440422,550443932316548,551949501423251,553444838949259,554930034531101,
    556405176290376,557870350869872,559325643468575,560771137875609,562206916503151,
    563633060418352,565049649374311,566456761840127,567854475030059,569242864931844,
    570622006334183,571991972853435,573352836959546,574704670001236,576047542230476,
    577381522826270,578706679917779,580023080606795,581330790989599,582629876178216,
    583920400321095,585202426623215,586476017365669,587741233924706,588998136790274,
    590246785584071,591487239077120,592719555206886,593943791093946,595160003058229,
    596368246634839,597568576589472,598761046933447,599945710938344,601122621150293,
    602291829403889,603453386835776,604607343897880,605753750370331,606892655374065,
    608024107383113,609148154236604,610264843150472,611374220728888,612476332975416,
    613571225303909,614658942549145,615739528977219,616813028295692,617879483663500,
    618938937700640,619991432497635,621037009624779,622075710141176,623107574603575,
    624132643075001,625150955133203,626162549878908,627167465943890,628165741498873,
    629157414261246,630142521502621,631121100056224,632093186324125,633058816284315,
    634018025497631,634970849114532,635917321881738,636857478148720,637791351874061,
    638718976631683,639640385616941,640555611652597,641464687194669,642367644338153,
    643264514822645,644155330037828,645040121028869,645918918501689,646791752828144,
    647658654051088,648519651889348,649374775742592,650224054696107,651067517525480,
    651905192701187,652737108393101,653563292474900,654383772528402,655198575847811,
    656007729443880,656811260048005,657609194116228,658401557833175,659188377115916,
    659969677617754,660745484731943,661515823595336,662280719091968,663040195856574,
    663794278278037,664542990502782,665286356438099,666024399755414,666757143893496,
    667484612061608,668206827242602,668923812195962,669635589460786,670342181358719,
    671043609996841,671739897270491,672431064866053],
   [673117134263690,673798126740029,674474063370801,675144965033436,675810852409616,
    676471745987777,677127666065577,677778632752318,678424665971325,679065785462293,
    679702010783585,680333361314499,680959856257492,681581514640374,682198355318455,
    682810396976671,683417658131661,684020157133820,684617912169316,685210941262070,
    685799262275711,686382892915492,686961850730186,687536153113938,688105817308100,
    688670860403027,689231299339851,689787150912228,690338431768050,690885158411135,
    691427347202895,691965014363970,692498175975838,693026847982408,693551046191577,
    694070786276775,694586083778471,695096954105677,695603412537405,696105474224123,
    696603154189178,697096467330197,697585428420473,698070052110324,698550352928438,
    699026345283191,699498043463952,699965461642363,700428613873607,700887514097647,
    701342176140459,701792613715239,702238840423591,702680869756707,703118715096519,
    703552389716842,703981906784498,704407279360422,704828520400755,705245642757921,
    705658659181685,706067582320202,706472424721048,706873198832234,707269917003208,
    707662591485846,708051234435424,708435857911579,708816473879255,709193094209639,
    709565730681081,709934394980000,710299098701785,710659853351672,711016670345619,
    711369561011165,711718536588276,712063608230181,712404787004200,712742083892552,
    713075509793159,713405075520441,713730791806093,714052669299854,714370718570273,
    714684950105451,714995374313789,715302001524709,715604841989381,715903905881431,
    716199203297642,716490744258646,716778538709606,717062596520894,717342927488747,
    717619541335934,717892447712394,718161656195882,718427176292595,718689017437797,
    718947188996435,719201700263740,719452560465830,719699778760302,719943364236810,
    720183325917645,720419672758302,720652413648041,720881557410441,721107112803945,
    721329088522402,721547493195600,721762335389790,721973623608205,722181366291576,
    722385571818635,722586248506617,722783404611750,722977048329746,723167187796282,
    723353831087470,723536986220332,723716661153259,723892863786472,724065601962468,
    724234883466472,724400716026871,724563107315654],
   [724722064948839,724877596486897,725029709435169,725178411244282,725323709310556,
    725465610976406,725604123530742,725739254209362,725871010195338,725999398619399,
    726124426560314,726246101045263,726364429050203,726479417500239,726591073269979,
    726699403183891,726804414016656,726906112493512,727004505290598,727099599035291,
    727191400306542,727279915635204,727365151504357,727447114349633,727525810559529,
    727601246475726,727673428393393,727742362561498,727808055183105,727870512415679,
    727929740371371,727985745117320,728038532675930,728088109025160,728134480098804,
    728177651786760,728217629935315,728254420347404,728288028782880,728318460958778,
    728345722549575,728369819187442,728390756462500,728408539923068,728423175075913,
    728434667386489,728443022279178,728448245137530,728450341304492,728449316082646,
    728445174734429,728437922482364,728427564509280,728414105958530,728397551934209,
    728377907501369,728355177686225,728329367476365,728300481820959,728268525630955,
    728233503779283,728195421101051,728154282393736,728110092417382,728062855894784,
    728012577511677,727959261916917,727902913722668,727843537504574,727781137801940,
    727715719117905,727647285919613,727575842638380,727501393669867,727423943374236,
    727343496076319,727260056065771,727173627597234,727084214890486,726991822130599,
    726896453468083,726798113019041,726696804865309,726592533054604,726485301600662,
    726375114483380,726261975648950,726145889010000,726026858445718,725904887801990,
    725779980891526,725652141493986,725521373356104,725387680191813,725251065682361,
    725111533476436,724969087190274,724823730407779,724675466680634,724524299528410,
    724370232438676,724213268867104,724053412237573,723890665942275,723725033341809,
    723556517765288,723385122510426,723210850843643,723033706000150,722853691184044,
    722670809568394,722485064295334,722296458476141,722104995191327,721910677490713,
    721713508393514,721513490888413,721310627933644,721104922457059,720896377356206,
    720684995498397,720470779720780,720253732830402,720033857604281,719811156789463,
    719585633103090,719357289232457,719126127835071],
   [718892151538708,718655362941471,718415764611838,718173359088718,717928148881501,
    717680136470101,717429324305012,717175714807341,716919310368864,716660113352055,
    716398126090135,716133350887106,715865790017786,715595445727848,715322320233849,
    715046415723261,714767734354505,714486278256975,714202049531063,713915050248188,
    713625282450814,713332748152476,713037449337794,712739387962495,712438565953426,
    712134985208570,711828647597058,711519554959180,711207709106396,710893111821339,
    710575764857826,710255669940857,709932828766621,709607243002498,709278914287052,
    708947844230035,708614034412378,708277486386186,707938201674730,707596181772441,
    707251428144890,706903942228785,706553725431950,706200779133307,705845104682865,
    705486703401692,705125576581898,704761725486609,704395151349943,704025855376981,
    703653838743741,703279102597143,702901648054981,702521476205884,702138588109284,
    701752984795375,701364667265075,700973636489981,700579893412331,700183438944951,
    699784273971216,699382399344994,698977815890598,698570524402733,698160525646440,
    697747820357039,697332409240071,696914292971238,696493472196338,696069947531202,
    695643719561626,695214788843304,694783155901757,694348821232257,693911785299757,
    693472048538812,693029611353499,692584474117338,692136637173207,691686100833259,
    691232865378832,690776931060363,690318298097291,689856966677970,689392936959568,
    688926209067969,688456783097675,687984659111702,687509837141474,687032317186716,
    686552099215348,686069183163366,685583568934735,685095256401267,684604245402504,
    684110535745598,683614127205184,683115019523255,682613212409035,682108705538843,
    681601498555963,681091591070509,680578982659278,680063672865619,679545661199279,
    679024947136263,678501530118680,677975409554592,677446584817862,676915055247989,
    676380820149953,675843878794052,675304230415729,674761874215411,674216809358331,
    673669034974355,673118550157802,672565353967266,672009445425429,671450823518875,
    670889487197896,670325435376306,669758666931235,669189180702935,668616975494575,
    668042050072031,667464403163684,666884033460195],
   [666300939614300,665715120240578,665126573915239,664535299175885,663941294521287,
    663344558411146,662745089265856,662142885466261,661537945353411,660930267228307,
    660319849351654,659706689943596,659090787183462,658472139209493,657850744118575,
    657226599965965,656599704765013,655970056486879,655337653060245,654702492371025,
    654064572262066,653423890532854,652780444939203,652134233192947,651485252961627,
    650833501868173,650178977490574,649521677361559,648861598968253,648198739751845,
    647533097107241,646864668382717,646193450879561,645519441851718,644842638505420,
    644163037998818,643480637441607,642795433894639,642107424369540,641416605828315,
    640722975182948,640026529294997,639327264975179,638625178982961,637920268026123,
    637212528760341,636501957788737,635788551661447,635072306875163,634353219872676,
    633631287042417,632906504717982,632178869177653,631448376643917,630715023282967,
    629978805204208,629239718459743,628497759043861,627752922892515,627005205882786,
    626254603832346,625501112498909,624744727579677,623985444710774,623223259466670,
    622458167359604,621690163838989,620919244290811,620145404037023,619368638334924,
    618588942376531,617806311287939,617020740128677,616232223891044,615440757499446,
    614646335809713,613848953608412,613048605612147,612245286466844,611438990747032,
    610629712955109,609817447520595,609002188799376,608183931072933,607362668547563,
    606538395353582,605711105544524,604880793096314,604047451906440,603211075793109,
    602371658494381,601529193667303,600683674887014,599835095645850,598983449352422,
    598128729330688,597270928819006,596410040969168,595546058845426,594678975423497,
    593808783589551,592935476139187,592059045776383,591179485112441,590296786664902,
    589410942856453,588521946013808,587629788366574,586734462046099,585835959084298,
    584934271412457,584029390860023,583121309153371,582210017914542,581295508659973,
    580377772799196,579456801633515,578532586354664,577605118043437,576674387668300,
    575740386083971,574803104029984,573862532129218,572918660886410,571971480686633,
    571020981793753,570067154348854,569109988368637],
   [568149473743795,567185600237345,566218357482947,565247734983181,564273722107792,
    563296308091913,562315482034247,561331232895215,560343549495075,559352420512003,
    558357834480139,557359779787595,556358244674430,555353217230580,554344685393756,
    553332636947296,552317059517982,551297940573812,550275267421726,549249027205296,
    548219206902367,547185793322648,546148773105267,545108132716266,544063858446056,
    543015936406817,541964352529849,540909092562868,539850142067248,538787486415215,
    537721110786969,536651000167768,535577139344934,534499512904812,533418105229655,
    532332900494459,531243882663719,530151035488123,529054342501182,527953787015784,
    526849352120675,525741020676869,524628775313981,523512598426481,522392472169870,
    521268378456772,520140298952939,519008215073178,517872107977184,516731958565274,
    515587747474046,514439455071923,513287061454613,512130546440456,510969889565677,
    509805070079522,508636066939298,507462858805282,506285424035533,505103740680568,
    503917786477931,502727538846620,501532974881399,500334071346969,499130804672001,
    497923150943033,496711085898220,495494584920933,494273623033205,493048174889021,
    491818214767445,490583716565576,489344653791334,488100999556072,486852726566994,
    485599807119399,484342213088718,483079915922357,481812886631332,480541095781693,
    479264513485724,477983109392924,476696852680742,475405712045089,474109655690582,
    472808651320547,471502666126748,470191666778847,468875619413578,467554489623636,
    466228242446253,464896842351477,463560253230118,462218438381367,460871360500071,
    459518981663650,458161263318651,456798166266913,455429650651351,454055675941322,
    452676200917575,451291183656763,449900581515502,448504351113967,447102448318995,
    445694828226691,444281445144516,442862252572823,441437203185845,440006248812102,
    438569340414191,437126428067969,435677460941077,434222387270787,432761154341157,
    431293708459456,429819994931825,428339958038169,426853541006217,425360685984739,
    423861334015879,422355425006574,420842897699001,419323689640047,417797737149727,
    416264975288527,414725337823620,413178757193909],
   [411625164473840,410064489335948,408496660012058,406921603253105,405339244287499,
    403749506777970,402152312776829,400547582679579,398935235176782,397315187204129,
    395687353890596,394051648504635,392407982398276,390756264949052,389096403499649,
    387428303295159,385751867417829,384066996719177,382373589749346,380671542683554,
    378960749245502,377241100627575,375512485407674,373774789462509,372027895877156,
    370271684850689,368506033597676,366730816245311,364945903725943,363151163664759,
    361346460262334,359531654171774,357706602370134,355871158023792,354025170347417,
    352168484456164,350300941210684,348422377054537,346532623843524,344631508666456,
    342718853656829,340794475794833,338858186699076,336909792407374,334949093145890,
    332975883085856,330989950087054,328991075427169,326979033516046,324953591593805,
    322914509411701,320861538894494,318794423783008,316712899255442,314616691525867,
    312505517418206,310379083913848,308237087670864,306079214512626,303905138883413,
    301714523268361,299507017574858,297282258472212,295039868686096,292779456243933,
    290500613666972,288202917104407,285885925404340,283549179115903,281192199416177,
    278814486954867,276415520608911,273994756138274,271551624733187,269085531441911,
    266595853466808,264081938314967,261543101787937,258978625793111,256387755957037,
    253769699018310,251123619974625,248448638955077,245743827784651,243008206203045,
    240240737694371,237440324877623,234605804400028,231735941266158,228829422524664,
    225884850221431,222900733512185,219875479808694,216807384809776,213694621240499,
    210535226088884,207327086087619,204067921136502,200755265296991,197386444909612,
    193958553283272,190468421276380,186912582924160,183287235052883,179588189543082,
    175810816537185,171949976399115,167999937577109,163954276626861,159805755417717,
    155546168815175,151166153670684,146654946381478,142000071009741,137186931984927,
    132198273083077,127013444756454,121607389667290,115949201422515,110000014097170,
    103709798381180,97012280321503,89816432494910,81991200778293,73335438882135,63510534598731,
    51856233164458,36667929052542]]
private def rkmHbWin_w128_s7 : List ℤ := altBuildHbFrom 2048 1024 17495461538 0 1024
private def rkmXsWin_w128_s7_in : List ℤ := pzigCat
  [
   [273827159,1296638460,3431083763,6438423214,11348476549,19510377124,33242433343,55783285650,
    89133401895,133958433836,189840676365,256562940818,327350667853,382758660316,396603936553,
    354381284666,253535761835,98998139312,80547080112,209191134195,197946149658,38943018341,
    156738992891,248787490110,185514733683,39454777336,40104058458,38357148591,140367234995,
    19268829132,196469919474,33044460796,362898452880,312980689828,255348812692,738212770890,
    499563613470,89114984428,504560449715,957616248315,840053763901,661327116365,274061776218,
    543005112064,2070525260099,1156094591511,2566993095898,10859238066788,5645923968040,
    6545424504176,2959846653913,10756737679039,14626660633909,13036766800318,11901863545140,
    1925460131846,14669983373736,3041029010506,12812257023868,4581591295586,31693500361466,
    44073147848144,8227001567568,11003004448903,42468126871799,7426046290501,28779935953291,
    114073076596631,124762177319261,24836069768693,60470649955315,154862070671115,82478956090456,
    108717265113330,2794605413562,142718533897096,175824346218000,314857116826464,
    300351217849680,863216010507272,1712211950525534]]
private def rkmXsWin_w128_s7_out : List ℤ := pzigCat
  [
   [810938049,2380617486,5145726773,9258554658,15645662253,25185137970,39755596627,61168581274,
    91578828321,131732758392,181164006115,236722641272,292963589319,340523829290,366894825099,
    356883722090,298572654787,191167038548,53138968585,81734975955,172891769524,184407349641,
    98788829056,59973771852,212307415503,261100830970,172012298521,17218910074,83505476104,
    70554554559,5508272893,41896865302,18635593184,125405793015,150030649000,22389264603,
    150666686749,185464419228,88126448773,33300642810,48166950912,194685531225,35597918493,
    40828741372,136674472604,169512378896,315687866209,1178974545114,266181527087,1767139582372,
    957141990713,2178529423332,4606923339527,1011390219256,840012728338,1799750771618,
    7102283516837,2100088376282,1085099134235,2236217370597,24708157124956,2145770705086,
    3466759682353,13738541971053,744393915623,4369290580396,3460475887877,23915104036260,
    671121847632,3177237095090,2165045710479,30733128101678,58144120729666,11429616870988,
    37554282925007,25200420108070,28512033511540,162152973055355,34528317988555,35330652524763,
    206810244359907,27103821069999,552698076654,58284008371524,3300048167126,231241324736154,
    186901131646360,133448673574868,1951740740826780]]
private def rkmHbN_w128_s7 : List ℕ := rkmCatN
  [
   [50672269285409,71608921937792,87638369598409,101121830457349,112974631465713,123666565616427,
    133476920217983,142587801159669,151125792714430,159183127652125,166829485110938,
    174119038274272,181094899532899,187792049593131,194239338436940,200460894194136,
    206477140988185,212305550778199,217961209551241,223457251012938,228805193824531,
    234015207385531,239096323845190,244056609074701,248903301914927,253642928613847,
    258281397654178,262824078930189,267275870321128,271641254031169,275924344556293,
    280128929751438,284258506174244,288316309651723,292305341836580,296228393378550,
    300088064223967,303886781467275,307626815106194,311310291994015,314939208235151,
    318515440231275,322040754553526,325516816789879,328945199494910,332327389350898,
    335664793633940,338958746065847,342210512121732,345421293853990,348592234285503,
    351724421418231,354818891897604,357876634368201,360898592551950,363885668076436,
    366838723077686,369758582599059,372646036805460,375501843029977,378326727668205,
    381121387933913,383886493488269,386622687953590,389330590321493,392010796264306,
    394663879357774,397290392222272,399890867589098,402465819297762,405015743229678,
    407541118183132,410042406694008,412520055806317,414974497796243,417406150853091,
    419815419720243,422202696298949,424568360217573,426912779368667,429236310416086,
    431539299274158,433822081560767,436084983026085,438328319958511,440552399569308,
    442757520357274,444943972454712,447112037955852,449261991228814,451394099212094,
    453508621696523,455605811593545,457685915190632,459749172394566,461795816963304,
    463826076727072,465840173799279,467838324777842,469820740937436,471787628413169,
    473739188376146,475675617201354,477597106628287,479503843914668,481396011983660,
    483273789564868,485137351329475,486986868019797,488822506573536,490644430242999,
    492452798709528,494247768193375,496029491559242,497798118417698,499553795222657,
    501296665365120,503026869263336,504744544449568,506449825653602,508142844883155,
    509823731501327,511492612301220,513149611577852,514794851197492,516428450664521,
    518050527185927,519661195733541],
   [521260569104107,522848757977272,524425870971596,525992014698654,527547293815312,
    529091811074257,530625667372839,532148961800310,533661791683513,535164252631084,
    536656438576230,538138441818141,539610353062073,541072261458177,542524254639106,
    543966418756451,545398838516050,546821597212217,548234776760921,549638457731968,
    551032719380207,552417639675810,553793295333653,555159761841828,556517113489322,
    557865423392890,559204763523157,560535204729961,561856816766979,563169668315661,
    564473827008473,565769359451509,567056331246464,568334807011997,569604850404518,
    570866524138397,572119890005634,573365008894989,574601940810611,575830744890160,
    577051479422456,578264201864664,579468968859022,580665836249144,581854859095895,
    583036091692859,584209587581416,585375399565426,586533579725557,587684179433238,
    588827249364272,589962839512114,591090999200807,592211777097621,593325221225361,
    594431378974396,595530297114382,596622021805716,597706598610704,598784072504474,
    599854487885626,600917888586632,601974317883993,603023818508162,604066432653230,
    605102201986403,606131167657244,607153370306720,608168850076036,609177646615269,
    610179799091814,611175346198636,612164326162342,613146776751073,614122735282222,
    615092238629985,616055323232746,617012025100303,617962379820937,618906422568329,
    619844188108334,620775710805603,621701024630072,622620163163310,623533159604737,
    624440046777709,625340857135482,626235622767046,627124375402844,628007146420372,
    628883966849667,629754867378681,630619878358545,631479029808733,632332351422121,
    633179872569937,634021622306627,634857629374612,635687922208962,636512528941967,
    637331477407632,638144795146073,638952509407839,639754647158138,640551235080998,
    641342299583331,642127866798937,642907962592417,643682612563027,644451842048444,
    645215676128477,645974139628700,646727257124016,647475052942164,648217551167155,
    648954775642645,649686749975251,650413497537802,651135041472536,651851404694235,
    652562609893304,653268679538804,653969635881413,654665500956356,655356296586267,
    656042044384007,656722765755434,657398481902118],
   [658069213824023,658734982322124,659395808000991,660051711271329,660702712352466,
    661348831274810,661990087882253,662626501834540,663258092609600,663884879505837,
    664506881644373,665124117971273,665736607259710,666344368112117,666947418962284,
    667545778077433,668139463560254,668728493350908,669312885229000,669892656815516,
    670467825574733,671038408816096,671604423696061,672165887219919,672722816243581,
    673275227475338,673823137477593,674366562668570,674905519323987,675440023578711,
    675970091428385,676495738731026,677016981208604,677533834448589,678046313905488,
    678554434902337,679058212632194,679557662159590,680052798421967,680543636231098,
    681030190274471,681512475116669,681990505200720,682464294849427,682933858266678,
    683399209538743,683860362635544,684317331411908,684770129608805,685218770854564,
    685663268666073,686103636449960,686539887503759,686972035017057,687400092072627,
    687824071647540,688243986614265,688659849741753,689071673696503,689479471043615,
    689883254247826,690283035674536,690678827590811,691070642166378,691458491474609,
    691842387493481,692222342106532,692598367103798,692970474182742,693338674949161,
    693702980918095,694063403514707,694419954075162,694772643847491,695121483992442,
    695466485584321,695807659611816,696145016978822,696478568505241,696808324927777,
    697134296900726,697456494996742,697774929707608,698089611444984,698400550541149,
    698707757249741,699011241746471,699311014129844,699607084421858,699899462568701,
    700188158441438,700473181836682,700754542477270,701032250012911,701306314020846,
    701576744006483,701843549404032,702106739577133,702366323819464,702622311355361,
    702874711340410,703123532862043,703368784940123,703610476527523,703848616510692,
    704083213710224,704314276881408,704541814714779,704765835836659,704986348809694,
    705203362133375,705416884244566,705626923518015,705833488266860,706036586743135,
    706236227138261,706432417583535,706625166150614,706814480851990,707000369641460,
    707182840414592,707361901009182,707537559205708,707709822727775,707878699242559,
    708044196361238,708206321639430,708365082577611],
   [708520486621539,708672541162665,708821253538545,708966631033242,709108680877728,
    709247410250274,709382826276842,709514936031469,709643746536646,709769264763690,
    709891497633122,710010452015021,710126134729397,710238552546538,710347712187366,
    710453620323785,710556283579024,710655708527975,710751901697526,710844869566897,
    710934618567963,711021155085574,711104485457879,711184615976637,711261552887528,
    711335302390458,711405870639866,711473263745020,711537487770312,711598548735551,
    711656452616250,711711205343911,711762812806307,711811280847754,711856615269392,
    711898821829450,711937906243515,711973874184794,712006731284377,712036483131492,
    712063135273756,712086693217433,712107162427672,712124548328758,712138856304349,
    712150091697716,712158259811977,712163365910328,712165415216273,712164412913850,
    712160364147853,712153274024052,712143147609410,712129989932297,712113805982706,
    712094600712453,712072379035391,712047145827609,712018905927633,711987664136625,
    711953425218577,711916193900506,711875974872639,711832772788607,711786592265623,
    711737437884670,711685314190677,711630225692698,711572176864089,711511172142674,
    711447215930923,711380312596113,711310466470498,711237681851469,711161963001715,
    711083314149383,711001739488231,710917243177787,710829829343492,710739502076859,
    710646265435611,710550123443833,710451080092109,710349139337667,710244305104514,
    710136581283573,710025971732819,709912480277408,709796110709808,709676866789929,
    709554752245244,709429770770917,709301926029922,709171221653164,709037661239597,
    708901248356337,708761986538779,708619879290707,708474930084404,708327142360757,
    708176519529371,708023064968663,707866782025970,707707674017648,707545744229171,
    707380995915224,707213432299802,707043056576300,706869871907605,706693881426184,
    706515088234171,706333495403455,706149105975761,705961922962730,705771949346006,
    705579188077306,705383642078501,705185314241690,704984207429272,704780324474019,
    704573668179142,704364241318363,704152046635977,703937086846918,703719364636822,
    703498882662088,703275643549933,703049649898456],
   [702820904276687,702589409224645,702355167253390,702118180845073,701878452452983,
    701635984501596,701390779386622,701142839475046,700892167105170,700638764586657,
    700382634200565,700123778199391,699862198807097,699597898219152,699330878602562,
    699061142095897,698788690809323,698513526824632,698235652195261,697955068946320,
    697671779074613,697385784548661,697097087308717,696805689266787,696511592306640,
    696214798283832,695915309025706,695613126331413,695308251971915,695000687689994,
    694690435200258,694377496189146,694061872314928,693743565207706,693422576469415,
    693098907673820,692772560366508,692443536064887,692111836258174,691777462407391,
    691440415945347,691100698276629,690758310777589,690413254796324,690065531652660,
    689715142638135,689362089015971,689006372021056,688647992859919,688286952710702,
    687923252723130,687556894018485,687187877689571,686816204800682,686441876387563,
    686064893457379,685685256988670,685302967931316,684918027206487,684530435706605,
    684140194295295,683747303807337,683351765048616,682953578796070,682552745797639,
    682149266772202,681743142409530,681334373370217,680922960285625,680508903757817,
    680092204359494,679672862633927,679250879094887,678826254226577,678398988483553,
    677969082290657,677536536042932,677101350105547,676663524813716,676223060472612,
    675779957357286,675334215712574,674885835753011,674434817662739,673981161595413,
    673524867674103,673065935991198,672604366608305,672140159556145,671673314834452,
    671203832411859,670731712225797,670256954182374,669779558156270,669299523990615,
    668816851496870,668331540454709,667843590611894,667353001684147,666859773355025,
    666363905275787,665865397065261,665364248309708,664860458562682,664354027344893,
    663844954144058,663333238414760,662818879578293,662301877022517,661782230101698,
    661259938136354,660735000413094,660207416184456,659677184668739,659144305049838,
    658608776477072,658070598065009,657529768893286,656986288006434,656440154413692,
    655891367088822,655339924969916,654785826959210,654229071922880,653669658690852,
    653107586056594,652542852776909,651975457571735],
   [651405399123923,650832676079026,650257287045082,649679230592387,649098505253273,
    648515109521874,647929041853897,647340300666385,646748884337473,646154791206145,
    645558019571989,644958567694939,644356433795024,643751616052107,643144112605620,
    642533921554296,641921040955897,641305468826938,640687203142408,640066241835481,
    639442582797230,638816223876334,638187162878777,637555397567547,636920925662328,
    636283744839190,635643852730269,635001246923449,634355924962034,633707884344416,
    633057122523739,632403636907560,631747424857499,631088483688889,630426810670419,
    629762403023773,629095257923257,628425372495432,627752743818730,627077368923072,
    626399244789476,625718368349662,625034736485647,624348346029338,623659193762119,
    622967276414427,622272590665325,621575133142072,620874900419677,620171889020458,
    619466095413581,618757516014609,618046147185024,617331985231762,616615026406723,
    615895266906287,615172702870817,614447330384151,613719145473095,612988144106901,
    612254322196739,611517675595163,610778200095566,610035891431627,609290745276755,
    608542757243512,607791922883043,607038237684484,606281697074367,605522296416019,
    604760031008939,603994896088184,603226886823728,602455998319822,601682225614337,
    600905563678107,600126007414246,599343551657472,598558191173404,597769920657862,
    596978734736145,596184627962305,595387594818403,594587629713764,593784726984205,
    592978880891262,592170085621406,591358335285234,590543623916659,589725945472084,
    588905293829561,588081662787935,587255046065978,586425437301508,585592830050490,
    584757217786130,583918593897944,583076951690821,582232284384067,581384585110429,
    580533846915111,579680062754771,578823225496494,577963327916760,577100362700385,
    576234322439451,575365199632212,574492986681989,573617675896036,572739259484399,
    571857729558746,570973078131181,570085297113040,569194378313659,568300313439130,
    567403094091029,566502711765125,565599157850065,564692423626039,563782500263415,
    562869378821362,561953050246435,561033505371145,560110734912501,559184729470523,
    558255479526734,557322975442618,556387207458062],
   [555448165689756,554505840129571,553560220642912,552611296967035,551659058709331,
    550703495345589,549744596218214,548782350534425,547816747364408,546847775639447,
    545875424150007,544899681543790,543920536323756,542937976846096,541951991318181,
    540962567796461,539969694184327,538973358229936,537973547523990,536970249497475,
    535963451419351,534953140394206,533939303359857,532921927084905,531900998166248,
    530876503026535,529848427911580,528816758887716,527781481839104,526742582464979,
    525700046276848,524653858595632,523604004548740,522550469067099,521493236882107,
    520432292522535,519367620311360,518299204362536,517227028577690,516151076642760,
    515071332024553,513987777967235,512900397488745,511809173377136,510714088186833,
    509615124234812,508512263596700,507405488102786,506294779333949,505180118617493,
    504061487022894,502938865357451,501812234161844,500681573705586,499546863982380,
    498408084705369,497265215302279,496118234910452,494967122371761,493811856227421,
    492652414712662,491488775751295,490320916950144,489148815593348,487972448636528,
    486791792700823,485606824066774,484417518668070,483223852085143,482025799538602,
    480823335882516,479616435597531,478405072783813,477189221153824,475968854024916,
    474743944311742,473514464518473,472280386730825,471041682607881,469798323373703,
    468550279808732,467297522240968,466040020536919,464777744092315,463510661822577,
    462238742153043,460961953008923,459680261804997,458393635435035,457102040260923,
    455805442101509,454503806221131,453197097317842,451885279511301,450568316330333,
    449246170700139,447918804929149,446586180695502,445248259033140,443905000317505,
    442556364250827,441202309846978,439842795415894,438477778547529,437107216095343,
    435731064159294,434349278068324,432961812362313,431568620773490,430169656207274,
    428764870722524,427354215511179,425937640877265,424515096215241,423086529987660,
    421651889702121,420211121887482,418764172069299,417310984744478,415851503355088,
    414385670261310,412913426713494,411434712823272,409949467533707,408457628588415,
    406959132499643,405453914515238,403941908584468],
   [402423047322651,400897261974532,399364482376355,397824636916581,396277652495180,
    394723454481447,393161966670258,391593111236720,390016808689115,388432977820083,
    386841535655941,385242397404077,383635476398293,382020684042043,380397929749418,
    378767120883812,377128162694124,375480958248393,373825408364732,372161411539421,
    370488863872029,368807658987398,367117687954334,365418839200839,363710998425689,
    361994048506177,360267869401810,358532338053740,356787328279699,355032710664187,
    353268352443655,351494117386387,349709865666800,347915453733822,346110734173014,
    344295555562070,342469762319294,340633194544644,338785687852881,336927073198344,
    335057176690839,333175819402067,331282817162011,329377980344624,327461113642127,
    325532015827173,323590479502060,321636290834137,319669229276445,317689067272587,
    315695569944714,313688494763453,311667591198448,309632600348142,307583254547247,
    305519276950252,303440381089144,301346270403377,299236637739922,297111164821044,
    294969521677218,292811366042353,290636342708223,288444082834686,286234203211937,
    284006305470648,281759975235439,279494781216618,277210274234606,274905986170843,
    272581428838299,270236092763916,267869445874460,265480932076229,263069969717974,
    260635949925054,258178234791414,255696155414252,253189009754333,250656060302660,
    248096531531639,245509607105924,242894426824630,240250083262625,237575618073893,
    234870017914453,232132209935882,229361056792827,226555351098892,223713809254512,
    220835064557638,217917659492678,214960037074623,211960531102927,208917355152436,
    205828590095435,202692169907916,199505865462626,196267265948500,192973757477256,
    189622498338553,186210390238779,182734044696795,179189743561006,175573392339763,
    171880464678621,168105935841023,164244202407339,160288984533052,156233205900081,
    152068844804420,147786747416088,143376390758843,138825577801632,134120039266278,
    129242904701627,124173986192449,118888786572168,113357090377893,107540900554760,
    101391306226674,94843515032909,87808534520605,80158240356903,71695982993208,62090720092348,
    50696957265453,35848196422093]]
private def rkmWalksHi_w128_r1024 : List RkmWinSegWalk := [
  ⟨256, rkmHbWin_w128_s0, 0, rkmXsWin_w128_s0_in, 41, rkmXsWin_w128_s0_out, 11457717232⟩,
  ⟨512, rkmHbWin_w128_s1, 41, rkmXsWin_w128_s1_in, 196, rkmXsWin_w128_s1_out, 21163984096⟩,
  ⟨1024, rkmHbWin_w128_s2, 196, rkmXsWin_w128_s2_in, 403, rkmXsWin_w128_s2_out, 26697115372⟩,
  ⟨1024, rkmHbWin_w128_s3, 403, rkmXsWin_w128_s3_in, 652, rkmXsWin_w128_s3_out, 33707447139⟩,
  ⟨1024, rkmHbWin_w128_s4, 652, rkmXsWin_w128_s4_in, 951, rkmXsWin_w128_s4_out, 62802242290⟩,
  ⟨1024, rkmHbWin_w128_s5, 951, rkmXsWin_w128_s5_in, 952, rkmXsWin_w128_s5_out, 2237620033⟩,
  ⟨1024, rkmHbWin_w128_s6, 952, rkmXsWin_w128_s6_in, 944, rkmXsWin_w128_s6_out, 1013531685⟩,
  ⟨1024, rkmHbWin_w128_s7, 944, rkmXsWin_w128_s7_in, 936, rkmXsWin_w128_s7_out, 667241486⟩
  ]
private abbrev rkmBP_00 : Prop := rkmAllTrueF [
  wSlChk 44 100000000 256 rkmHbN_w128_s0
  0 rkmXsWin_w128_s0_in 0 rkmC_w128_s0_1 2465902853,
  wSlChk 33 100000000 256 rkmHbN_w128_s0
  0 rkmC_w128_s0_1 12 rkmC_w128_s0_2 3389087035] = true
private theorem rkmBK_00 : rkmBP_00 := by decide +kernel
private abbrev rkmBP_01 : Prop := rkmAllTrueF [
  wSlChk 29 100000000 256 rkmHbN_w128_s0
  12 rkmC_w128_s0_2 41 rkmXsWin_w128_s0_out 5602727344,
  wSlChk 24 100000000 512 rkmHbN_w128_s1
  41 rkmXsWin_w128_s1_in 66 rkmC_w128_s1_1 3561780607] = true
private theorem rkmBK_01 : rkmBP_01 := by decide +kernel
private abbrev rkmBP_02 : Prop := rkmAllTrueF [
  wSlChk 24 100000000 512 rkmHbN_w128_s1
  66 rkmC_w128_s1_1 96 rkmC_w128_s1_2 4360364131,
  wSlChk 23 100000000 512 rkmHbN_w128_s1
  96 rkmC_w128_s1_2 128 rkmC_w128_s1_3 4504769772] = true
private theorem rkmBK_02 : rkmBP_02 := by decide +kernel
private abbrev rkmBP_03 : Prop := rkmAllTrueF [
  wSlChk 23 100000000 512 rkmHbN_w128_s1
  128 rkmC_w128_s1_3 162 rkmC_w128_s1_4 4208168154,
  wSlChk 23 100000000 512 rkmHbN_w128_s1
  162 rkmC_w128_s1_4 196 rkmXsWin_w128_s1_out 4528901432] = true
private theorem rkmBK_03 : rkmBP_03 := by decide +kernel
private abbrev rkmBP_04 : Prop := rkmAllTrueF [
  wSlChk 20 100000000 1024 rkmHbN_w128_s2
  196 rkmXsWin_w128_s2_in 225 rkmC_w128_s2_1 3832473292,
  wSlChk 19 100000000 1024 rkmHbN_w128_s2
  225 rkmC_w128_s2_1 253 rkmC_w128_s2_2 3747115020] = true
private theorem rkmBK_04 : rkmBP_04 := by decide +kernel
private abbrev rkmBP_05 : Prop := rkmAllTrueF [
  wSlChk 19 100000000 1024 rkmHbN_w128_s2
  253 rkmC_w128_s2_2 282 rkmC_w128_s2_3 4165309388,
  wSlChk 20 100000000 1024 rkmHbN_w128_s2
  282 rkmC_w128_s2_3 313 rkmC_w128_s2_4 4058981550] = true
private theorem rkmBK_05 : rkmBP_05 := by decide +kernel
private abbrev rkmBP_06 : Prop := rkmAllTrueF [
  wSlChk 20 100000000 1024 rkmHbN_w128_s2
  313 rkmC_w128_s2_4 343 rkmC_w128_s2_5 3706060689,
  wSlChk 19 100000000 1024 rkmHbN_w128_s2
  343 rkmC_w128_s2_5 373 rkmC_w128_s2_6 3441534351] = true
private theorem rkmBK_06 : rkmBP_06 := by decide +kernel
private abbrev rkmBP_07 : Prop := rkmAllTrueF [
  wSlChk 20 100000000 1024 rkmHbN_w128_s2
  373 rkmC_w128_s2_6 403 rkmXsWin_w128_s2_out 3745641082,
  wSlChk 21 100000000 1024 rkmHbN_w128_s3
  403 rkmXsWin_w128_s3_in 436 rkmC_w128_s3_1 3932452758] = true
private theorem rkmBK_07 : rkmBP_07 := by decide +kernel
private abbrev rkmBP_08 : Prop := rkmAllTrueF [
  wSlChk 21 100000000 1024 rkmHbN_w128_s3
  436 rkmC_w128_s3_1 468 rkmC_w128_s3_2 4121190499,
  wSlChk 22 100000000 1024 rkmHbN_w128_s3
  468 rkmC_w128_s3_2 503 rkmC_w128_s3_3 4134616583] = true
private theorem rkmBK_08 : rkmBP_08 := by decide +kernel
private abbrev rkmBP_09 : Prop := rkmAllTrueF [
  wSlChk 22 100000000 1024 rkmHbN_w128_s3
  503 rkmC_w128_s3_3 534 rkmC_w128_s3_4 4398931813,
  wSlChk 22 100000000 1024 rkmHbN_w128_s3
  534 rkmC_w128_s3_4 565 rkmC_w128_s3_5 3932022834] = true
private theorem rkmBK_09 : rkmBP_09 := by decide +kernel
private abbrev rkmBP_10 : Prop := rkmAllTrueF [
  wSlChk 22 100000000 1024 rkmHbN_w128_s3
  565 rkmC_w128_s3_5 597 rkmC_w128_s3_6 4430168697,
  wSlChk 22 100000000 1024 rkmHbN_w128_s3
  597 rkmC_w128_s3_6 624 rkmC_w128_s3_7 4313533016] = true
private theorem rkmBK_10 : rkmBP_10 := by decide +kernel
private abbrev rkmBP_11 : Prop := rkmAllTrueF [
  wSlChk 23 100000000 1024 rkmHbN_w128_s3
  624 rkmC_w128_s3_7 652 rkmXsWin_w128_s3_out 4444530939,
  wSlChk 21 100000000 1024 rkmHbN_w128_s4
  652 rkmXsWin_w128_s4_in 678 rkmC_w128_s4_1 3942102053] = true
private theorem rkmBK_11 : rkmBP_11 := by decide +kernel
private abbrev rkmBP_12 : Prop := rkmAllTrueF [
  wSlChk 21 100000000 1024 rkmHbN_w128_s4
  678 rkmC_w128_s4_1 704 rkmC_w128_s4_2 3821819603,
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  704 rkmC_w128_s4_2 729 rkmC_w128_s4_3 4682982432] = true
private theorem rkmBK_12 : rkmBP_12 := by decide +kernel
private abbrev rkmBP_13 : Prop := rkmAllTrueF [
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  729 rkmC_w128_s4_3 753 rkmC_w128_s4_4 4146133906,
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  753 rkmC_w128_s4_4 776 rkmC_w128_s4_5 4411485698] = true
private theorem rkmBK_13 : rkmBP_13 := by decide +kernel
private abbrev rkmBP_14 : Prop := rkmAllTrueF [
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  776 rkmC_w128_s4_5 798 rkmC_w128_s4_6 2565910500,
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  798 rkmC_w128_s4_6 816 rkmC_w128_s4_7 3558950462] = true
private theorem rkmBK_14 : rkmBP_14 := by decide +kernel
private abbrev rkmBP_15 : Prop := rkmAllTrueF [
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  816 rkmC_w128_s4_7 835 rkmC_w128_s4_8 3752048231,
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  835 rkmC_w128_s4_8 853 rkmC_w128_s4_9 3608331541] = true
private theorem rkmBK_15 : rkmBP_15 := by decide +kernel
private abbrev rkmBP_16 : Prop := rkmAllTrueF [
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  853 rkmC_w128_s4_9 868 rkmC_w128_s4_10 3612352005,
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  868 rkmC_w128_s4_10 882 rkmC_w128_s4_11 3179705254] = true
private theorem rkmBK_16 : rkmBP_16 := by decide +kernel
private abbrev rkmBP_17 : Prop := rkmAllTrueF [
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  882 rkmC_w128_s4_11 895 rkmC_w128_s4_12 3149861222,
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  895 rkmC_w128_s4_12 906 rkmC_w128_s4_13 3288855842] = true
private theorem rkmBK_17 : rkmBP_17 := by decide +kernel
private abbrev rkmBP_18 : Prop := rkmAllTrueF [
  wSlChk 22 100000000 1024 rkmHbN_w128_s4
  906 rkmC_w128_s4_13 918 rkmC_w128_s4_14 2688557078,
  wSlChk 23 100000000 1024 rkmHbN_w128_s4
  918 rkmC_w128_s4_14 926 rkmC_w128_s4_15 3000432115] = true
private theorem rkmBK_18 : rkmBP_18 := by decide +kernel
private abbrev rkmBP_19 : Prop := rkmAllTrueF [
  wSlChk 23 100000000 1024 rkmHbN_w128_s4
  926 rkmC_w128_s4_15 936 rkmC_w128_s4_16 2964383756,
  wSlChk 24 100000000 1024 rkmHbN_w128_s4
  936 rkmC_w128_s4_16 943 rkmC_w128_s4_17 2877470908] = true
private theorem rkmBK_19 : rkmBP_19 := by decide +kernel
private abbrev rkmBP_20 : Prop := rkmAllTrueF [
  wSlChk 24 100000000 1024 rkmHbN_w128_s4
  943 rkmC_w128_s4_17 946 rkmC_w128_s4_18 1928431161,
  wSlChk 24 100000000 1024 rkmHbN_w128_s4
  946 rkmC_w128_s4_18 951 rkmXsWin_w128_s4_out 1622428523] = true
private theorem rkmBK_20 : rkmBP_20 := by decide +kernel
private abbrev rkmBP_21 : Prop := rkmAllTrueF [
  Nat.ble (Nat.add 652 (altIntLen rkmXsWin_w128_s4_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 951 (altIntLen rkmXsWin_w128_s5_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 952 (altIntLen rkmXsWin_w128_s6_in)) (Nat.add 1024 1),
  Nat.ble (Nat.add 944 (altIntLen rkmXsWin_w128_s7_in)) (Nat.add 1024 1),
  rkmCheckRowFromWinWalks 128 64 1024 [2, 4, 8, 12, 16, 16, 16, 16]
    [10263992, 6051274, 4048000, 3872000, 7800000, 622387, 340015, 227441]
    [106, 117, 137, 175, 424, 34, 19, 13]
    rkmMasksHi_w128_r1024 rkmWalksHi_w128_r1024
    rkmRowHi_w128_r1024,
  muxIntListEq (uOfNatHb rkmHbN_w128_s4) rkmHbWin_w128_s4,
  muxIntListEq (uOfNatHb rkmHbN_w128_s5) rkmHbWin_w128_s5,
  muxIntListEq (uOfNatHb rkmHbN_w128_s6) rkmHbWin_w128_s6,
  muxIntListEq (uOfNatHb rkmHbN_w128_s7) rkmHbWin_w128_s7,
  muxIntListEq (uOfNatHb rkmHbN_w128_s0) rkmHbWin_w128_s0,
  muxIntListEq (uOfNatHb rkmHbN_w128_s1) rkmHbWin_w128_s1,
  muxIntListEq (uOfNatHb rkmHbN_w128_s2) rkmHbWin_w128_s2,
  muxIntListEq (uOfNatHb rkmHbN_w128_s3) rkmHbWin_w128_s3,
  wSlChk 17 100000000 1024 rkmHbN_w128_s5
  951 rkmXsWin_w128_s5_in 953 rkmC_w128_s5_1 1061238659,
  wSlChk 17 100000000 1024 rkmHbN_w128_s5
  953 rkmC_w128_s5_1 952 rkmXsWin_w128_s5_out 1176381374,
  wSlChk 19 100000000 1024 rkmHbN_w128_s6
  952 rkmXsWin_w128_s6_in 944 rkmXsWin_w128_s6_out 1013531685,
  wSlChk 13 100000000 1024 rkmHbN_w128_s7
  944 rkmXsWin_w128_s7_in 936 rkmXsWin_w128_s7_out 667241486
  ] = true
private theorem rkmWinSt_w128_term : rkmBP_21 := by decide +kernel
private theorem rkmWinIterF_w128_s0 :
    RkmWinIterSound 106 256 (uOfNatHb rkmHbN_w128_s0) 0 rkmXsWin_w128_s0_in
      41 rkmXsWin_w128_s0_out 11457717232 :=
  rkmChS 106 11457717232 (rkmChS 77 5854989888 (wSlChk_sound (rkmWP0 rkmBK_00)) (rkmWP1
    rkmBK_00) rfl rfl) (rkmWP0 rkmBK_01) rfl rfl
private theorem rkmWinIter_w128_s0 :
    RkmWinIterSound 106 256 rkmHbWin_w128_s0 0 rkmXsWin_w128_s0_in
      41 rkmXsWin_w128_s0_out 11457717232 :=
  rkmSubstHbN (rkmWP4 (rkmWT5 rkmWinSt_w128_term)) rkmWinIterF_w128_s0
/-- Certified `w128` seg `0` (`106` steps). -/
theorem rkmWinSegWalkSnd_w128_s0 :
    RkmWinSegWalkSound 106 ⟨256, rkmHbWin_w128_s0, 0, rkmXsWin_w128_s0_in,
      41, rkmXsWin_w128_s0_out, 11457717232⟩ :=
  @rkmSegWalk_mk 106 256 0 41 11457717232
    rkmHbWin_w128_s0 rkmXsWin_w128_s0_in rkmXsWin_w128_s0_out
    (rkmw_buildHbFrom_length 256 1024 96830113207 256 0) rfl rkmWinIter_w128_s0
private theorem rkmWinIterF_w128_s1 :
    RkmWinIterSound 117 512 (uOfNatHb rkmHbN_w128_s1) 41 rkmXsWin_w128_s1_in
      196 rkmXsWin_w128_s1_out 21163984096 :=
  rkmChS 117 21163984096 (rkmChS 94 16635082664 (rkmChS 71 12426914510 (rkmChS 48 7922144738
    (wSlChk_sound (rkmWP1 rkmBK_01)) (rkmWP0 rkmBK_02) rfl rfl) (rkmWP1 rkmBK_02) rfl rfl)
    (rkmWP0 rkmBK_03) rfl rfl) (rkmWP1 rkmBK_03) rfl rfl
private theorem rkmWinIter_w128_s1 :
    RkmWinIterSound 117 512 rkmHbWin_w128_s1 41 rkmXsWin_w128_s1_in
      196 rkmXsWin_w128_s1_out 21163984096 :=
  rkmSubstHbN (rkmWP0 (rkmWT5 (rkmWT5 rkmWinSt_w128_term))) rkmWinIterF_w128_s1
/-- Certified `w128` seg `1` (`117` steps). -/
theorem rkmWinSegWalkSnd_w128_s1 :
    RkmWinSegWalkSound 117 ⟨512, rkmHbWin_w128_s1, 41, rkmXsWin_w128_s1_in,
      196, rkmXsWin_w128_s1_out, 21163984096⟩ :=
  @rkmSegWalk_mk 117 512 41 196 21163984096
    rkmHbWin_w128_s1 rkmXsWin_w128_s1_in rkmXsWin_w128_s1_out
    (rkmw_buildHbFrom_length 512 1024 51720290598 512 0) rfl rkmWinIter_w128_s1
private theorem rkmWinIterF_w128_s2 :
    RkmWinIterSound 137 1024 (uOfNatHb rkmHbN_w128_s2) 196 rkmXsWin_w128_s2_in
      403 rkmXsWin_w128_s2_out 26697115372 :=
  rkmChS 137 26697115372 (rkmChS 117 22951474290 (rkmChS 98 19509939939 (rkmChS 78 15803879250
    (rkmChS 58 11744897700 (rkmChS 39 7579588312 (wSlChk_sound (rkmWP0 rkmBK_04)) (rkmWP1
    rkmBK_04) rfl rfl) (rkmWP0 rkmBK_05) rfl rfl) (rkmWP1 rkmBK_05) rfl rfl) (rkmWP0 rkmBK_06)
    rfl rfl) (rkmWP1 rkmBK_06) rfl rfl) (rkmWP0 rkmBK_07) rfl rfl
private theorem rkmWinIter_w128_s2 :
    RkmWinIterSound 137 1024 rkmHbWin_w128_s2 196 rkmXsWin_w128_s2_in
      403 rkmXsWin_w128_s2_out 26697115372 :=
  rkmSubstHbN (rkmWP1 (rkmWT5 (rkmWT5 rkmWinSt_w128_term))) rkmWinIterF_w128_s2
/-- Certified `w128` seg `2` (`137` steps). -/
theorem rkmWinSegWalkSnd_w128_s2 :
    RkmWinSegWalkSound 137 ⟨1024, rkmHbWin_w128_s2, 196, rkmXsWin_w128_s2_in,
      403, rkmXsWin_w128_s2_out, 26697115372⟩ :=
  @rkmSegWalk_mk 137 1024 196 403 26697115372
    rkmHbWin_w128_s2 rkmXsWin_w128_s2_in rkmXsWin_w128_s2_out
    (rkmw_buildHbFrom_length 1024 1024 29547445255 1024 0) rfl rkmWinIter_w128_s2
private theorem rkmWinIterF_w128_s3 :
    RkmWinIterSound 175 1024 (uOfNatHb rkmHbN_w128_s3) 403 rkmXsWin_w128_s3_in
      652 rkmXsWin_w128_s3_out 33707447139 :=
  rkmChS 175 33707447139 (rkmChS 152 29262916200 (rkmChS 130 24949383184 (rkmChS 108 20519214487
    (rkmChS 86 16587191653 (rkmChS 64 12188259840 (rkmChS 42 8053643257 (wSlChk_sound (rkmWP1
    rkmBK_07)) (rkmWP0 rkmBK_08) rfl rfl) (rkmWP1 rkmBK_08) rfl rfl) (rkmWP0 rkmBK_09) rfl rfl)
    (rkmWP1 rkmBK_09) rfl rfl) (rkmWP0 rkmBK_10) rfl rfl) (rkmWP1 rkmBK_10) rfl rfl) (rkmWP0
    rkmBK_11) rfl rfl
private theorem rkmWinIter_w128_s3 :
    RkmWinIterSound 175 1024 rkmHbWin_w128_s3 403 rkmXsWin_w128_s3_in
      652 rkmXsWin_w128_s3_out 33707447139 :=
  rkmSubstHbN (rkmWP2 (rkmWT5 (rkmWT5 rkmWinSt_w128_term))) rkmWinIterF_w128_s3
/-- Certified `w128` seg `3` (`175` steps). -/
theorem rkmWinSegWalkSnd_w128_s3 :
    RkmWinSegWalkSound 175 ⟨1024, rkmHbWin_w128_s3, 403, rkmXsWin_w128_s3_in,
      652, rkmXsWin_w128_s3_out, 33707447139⟩ :=
  @rkmSegWalk_mk 175 1024 403 652 33707447139
    rkmHbWin_w128_s3 rkmXsWin_w128_s3_in rkmXsWin_w128_s3_out
    (rkmw_buildHbFrom_length 1536 1024 22125714285 1024 0) rfl rkmWinIter_w128_s3
/-- Cumulative `FindAllJohnsonRampKickMuxHiW256WinT0` lane witness. -/
theorem rkmHiLane_w256_wint0 : @rkmWinSegWalkSnd_w128_s3 = @rkmWinSegWalkSnd_w128_s3 :=
  (And.intro (Eq.refl rkmHiLane_m128_s8) rfl).right
private theorem rkmWinIterF_w128_s4 :
    RkmWinIterSound 424 1024 (uOfNatHb rkmHbN_w128_s4) 652 rkmXsWin_w128_s4_in
      951 rkmXsWin_w128_s4_out 62802242290 :=
  rkmChS 424 62802242290 (rkmChS 400 61179813767 (rkmChS 376 59251382606 (rkmChS 352 56373911698
    (rkmChS 329 53409527942 (rkmChS 306 50409095827 (rkmChS 284 47720538749 (rkmChS 262
    44431682907 (rkmChS 240 41281821685 (rkmChS 218 38102116431 (rkmChS 196 34489764426 (rkmChS
    174 30881432885 (rkmChS 152 27129384654 (rkmChS 130 23570434192 (rkmChS 108 21004523692
    (rkmChS 86 16593037994 (rkmChS 64 12446904088 (rkmChS 42 7763921656 (wSlChk_sound (rkmWP1
    rkmBK_11)) (rkmWP0 rkmBK_12) rfl rfl) (rkmWP1 rkmBK_12) rfl rfl) (rkmWP0 rkmBK_13) rfl rfl)
    (rkmWP1 rkmBK_13) rfl rfl) (rkmWP0 rkmBK_14) rfl rfl) (rkmWP1 rkmBK_14) rfl rfl) (rkmWP0
    rkmBK_15) rfl rfl) (rkmWP1 rkmBK_15) rfl rfl) (rkmWP0 rkmBK_16) rfl rfl) (rkmWP1 rkmBK_16)
    rfl rfl) (rkmWP0 rkmBK_17) rfl rfl) (rkmWP1 rkmBK_17) rfl rfl) (rkmWP0 rkmBK_18) rfl rfl)
    (rkmWP1 rkmBK_18) rfl rfl) (rkmWP0 rkmBK_19) rfl rfl) (rkmWP1 rkmBK_19) rfl rfl) (rkmWP0
    rkmBK_20) rfl rfl) (rkmWP1 rkmBK_20) rfl rfl
private theorem rkmWinIter_w128_s4 :
    RkmWinIterSound 424 1024 rkmHbWin_w128_s4 652 rkmXsWin_w128_s4_in
      951 rkmXsWin_w128_s4_out 62802242290 :=
  rkmSubstHbN (rkmWP0 (rkmWT5 rkmWinSt_w128_term)) rkmWinIterF_w128_s4
private theorem rkmWinIterF_w128_s5 :
    RkmWinIterSound 34 1024 (uOfNatHb rkmHbN_w128_s5) 951 rkmXsWin_w128_s5_in
      952 rkmXsWin_w128_s5_out 2237620033 :=
  rkmChS 34 2237620033 (wSlChk_sound (rkmWP3 (rkmWT5 (rkmWT5 rkmWinSt_w128_term)))) (rkmWP4
    (rkmWT5 (rkmWT5 rkmWinSt_w128_term))) rfl rfl
private theorem rkmWinIter_w128_s5 :
    RkmWinIterSound 34 1024 rkmHbWin_w128_s5 951 rkmXsWin_w128_s5_in
      952 rkmXsWin_w128_s5_out 2237620033 :=
  rkmSubstHbN (rkmWP1 (rkmWT5 rkmWinSt_w128_term)) rkmWinIterF_w128_s5
private theorem rkmWinIterF_w128_s6 :
    RkmWinIterSound 19 1024 (uOfNatHb rkmHbN_w128_s6) 952 rkmXsWin_w128_s6_in
      944 rkmXsWin_w128_s6_out 1013531685 :=
  wSlChk_sound (rkmWP0 (rkmWT5 (rkmWT5 (rkmWT5 rkmWinSt_w128_term))))
private theorem rkmWinIter_w128_s6 :
    RkmWinIterSound 19 1024 rkmHbWin_w128_s6 952 rkmXsWin_w128_s6_in
      944 rkmXsWin_w128_s6_out 1013531685 :=
  rkmSubstHbN (rkmWP2 (rkmWT5 rkmWinSt_w128_term)) rkmWinIterF_w128_s6
private theorem rkmWinIterF_w128_s7 :
    RkmWinIterSound 13 1024 (uOfNatHb rkmHbN_w128_s7) 944 rkmXsWin_w128_s7_in
      936 rkmXsWin_w128_s7_out 667241486 :=
  wSlChk_sound (rkmWP1 (rkmWT5 (rkmWT5 (rkmWT5 rkmWinSt_w128_term))))
private theorem rkmWinIter_w128_s7 :
    RkmWinIterSound 13 1024 rkmHbWin_w128_s7 944 rkmXsWin_w128_s7_in
      936 rkmXsWin_w128_s7_out 667241486 :=
  rkmSubstHbN (rkmWP3 (rkmWT5 rkmWinSt_w128_term)) rkmWinIterF_w128_s7
private theorem rkmWinSegWalkSnd_w128_s4 :
    RkmWinSegWalkSound 424 ⟨1024, rkmHbWin_w128_s4, 652, rkmXsWin_w128_s4_in,
      951, rkmXsWin_w128_s4_out, 62802242290⟩ :=
  @rkmSegWalk_mk 424 1024 652 951 62802242290
    rkmHbWin_w128_s4 rkmXsWin_w128_s4_in rkmXsWin_w128_s4_out
    (rkmw_buildHbFrom_length 2048 1024 18396226415 1024 0)
    (rkmWP0 rkmWinSt_w128_term) rkmWinIter_w128_s4
private theorem rkmWinSegWalkSnd_w128_s5 :
    RkmWinSegWalkSound 34 ⟨1024, rkmHbWin_w128_s5, 951, rkmXsWin_w128_s5_in,
      952, rkmXsWin_w128_s5_out, 2237620033⟩ :=
  @rkmSegWalk_mk 34 1024 951 952 2237620033
    rkmHbWin_w128_s5 rkmXsWin_w128_s5_in rkmXsWin_w128_s5_out
    (rkmw_buildHbFrom_length 2048 1024 18305500000 1024 0)
    (rkmWP1 rkmWinSt_w128_term) rkmWinIter_w128_s5
private theorem rkmWinSegWalkSnd_w128_s6 :
    RkmWinSegWalkSound 19 ⟨1024, rkmHbWin_w128_s6, 952, rkmXsWin_w128_s6_in,
      944, rkmXsWin_w128_s6_out, 1013531685⟩ :=
  @rkmSegWalk_mk 19 1024 952 944 1013531685
    rkmHbWin_w128_s6 rkmXsWin_w128_s6_in rkmXsWin_w128_s6_out
    (rkmw_buildHbFrom_length 2048 1024 17895526315 1024 0)
    (rkmWP2 rkmWinSt_w128_term) rkmWinIter_w128_s6
private theorem rkmWinSegWalkSnd_w128_s7 :
    RkmWinSegWalkSound 13 ⟨1024, rkmHbWin_w128_s7, 944, rkmXsWin_w128_s7_in,
      936, rkmXsWin_w128_s7_out, 667241486⟩ :=
  @rkmSegWalk_mk 13 1024 944 936 667241486
    rkmHbWin_w128_s7 rkmXsWin_w128_s7_in rkmXsWin_w128_s7_out
    (rkmw_buildHbFrom_length 2048 1024 17495461538 1024 0)
    (rkmWP3 rkmWinSt_w128_term) rkmWinIter_w128_s7
private theorem rkmWalksSndHi_w128_r1024 :
    RkmWinSegWalksSound [106, 117, 137, 175, 424, 34, 19, 13] rkmWalksHi_w128_r1024 :=
  ⟨rkmWinSegWalkSnd_w128_s0,
  ⟨rkmWinSegWalkSnd_w128_s1,
  ⟨rkmWinSegWalkSnd_w128_s2,
  ⟨rkmWinSegWalkSnd_w128_s3,
  ⟨rkmWinSegWalkSnd_w128_s4,
  ⟨rkmWinSegWalkSnd_w128_s5,
  ⟨rkmWinSegWalkSnd_w128_s6,
  ⟨rkmWinSegWalkSnd_w128_s7,
    trivial⟩⟩⟩⟩⟩⟩⟩⟩
/-- Caustic `w128` `r = 1024` hit certificate (`m = 128`). -/
theorem rkmTrajHitHi_w128_m128 :
    RkmAnchorHitSound 128 ⟨1024, [2, 4, 8, 12, 16, 16, 16, 16],
      [10263992, 6051274, 4048000, 3872000, 7800000, 622387, 340015, 227441],
      [106, 117, 137, 175, 424, 34, 19, 13], rkmMasksHi_w128_r1024, rkmRowHi_w128_r1024⟩ :=
  @rkmCheckRowFromWinWalks_sound 128 64 1024 [2, 4, 8, 12, 16, 16, 16, 16]
    [10263992, 6051274, 4048000, 3872000, 7800000, 622387, 340015, 227441]
    [106, 117, 137, 175, 424, 34, 19, 13] rkmMasksHi_w128_r1024
    rkmWalksHi_w128_r1024 rkmRowHi_w128_r1024
    rkmWalksSndHi_w128_r1024 (rkmWP4 rkmWinSt_w128_term)
/-- Cumulative `RkMuxHiW256WinT1` lane witness. -/
theorem rkmHiLane_w256_wint1 : @rkmTrajHitHi_w128_m128 = @rkmTrajHitHi_w128_m128 :=
  (And.intro (Eq.refl rkmHiLane_w256_wint0) rfl).right

end
end QuantumComputation.Specs.DickeSol
