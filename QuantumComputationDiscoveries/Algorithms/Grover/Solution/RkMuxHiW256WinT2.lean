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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi256T8

/-
# Caustic `r = 1024` Halo-16 Walk `w256` (`RkMuxHiW256WinT2`)

Certifies `RkMuxHiW256WinT2` of the `w256` `r = 1024` halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Generator list for `w256_s0`. -/
def rkmHbWin_w256_s0 : List ℤ := altBuildHbFrom 256 1024 96830113207 0 256
/-- Entry `rkmXsWin_w256_s0_in`. -/
def rkmXsWin_w256_s0_in : List ℤ := [rkmP 1000000000000000]
/-- Exit `rkmXsWin_w256_s0_out`. -/
def rkmXsWin_w256_s0_out : List ℤ := let p := rkmP; [p 110381099, p 360821057, p 664735553,
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
/-- Generator list for `w256_s1`. -/
def rkmHbWin_w256_s1 : List ℤ := altBuildHbFrom 512 1024 51720290598 0 512
/-- Entry `rkmXsWin_w256_s1_in`. -/
def rkmXsWin_w256_s1_in : List ℤ := let p := rkmP; [p 110381099, p 360821057, p 664735553,
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
/-- Exit `rkmXsWin_w256_s1_out`. -/
def rkmXsWin_w256_s1_out : List ℤ := let p := rkmP; [p 104796403, p 295389998, p 508019380,
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
/-- Generator list for `w256_s2`. -/
def rkmHbWin_w256_s2 : List ℤ := altBuildHbFrom 1024 1024 29547445255 0 1024
/-- Entry `rkmXsWin_w256_s2_in`. -/
def rkmXsWin_w256_s2_in : List ℤ := let p := rkmP; [p 104796403, p 295389998, p 508019380,
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
/-- Exit `rkmXsWin_w256_s2_out`. -/
def rkmXsWin_w256_s2_out : List ℤ := let p := rkmP; [p 182117304, p 349240900, p 590124324,
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
/-- Generator list for `w256_s3`. -/
def rkmHbWin_w256_s3 : List ℤ := altBuildHbFrom 1536 1024 22125714285 0 1024
/-- Entry `rkmXsWin_w256_s3_in`. -/
def rkmXsWin_w256_s3_in : List ℤ := let p := rkmP; [p 182117304, p 349240900, p 590124324,
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
/-- Exit `rkmXsWin_w256_s3_out`. -/
def rkmXsWin_w256_s3_out : List ℤ := let p := rkmP; let n := rkmN; [n 109923774, p 3132009,
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
private def rkmHbN_w256_s0 : List ℕ := rkmCatN
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
private def rkmC_w256_s0_1 : List ℤ := pzigCat
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
private def rkmC_w256_s0_2 : List ℤ := pzigCat
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
private def rkmHbN_w256_s1 : List ℕ := rkmCatN
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
private def rkmC_w256_s1_1 : List ℤ := pzigCat
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
private def rkmC_w256_s1_2 : List ℤ := pzigCat
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
private def rkmC_w256_s1_3 : List ℤ := pzigCat
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
private def rkmC_w256_s1_4 : List ℤ := pzigCat
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
private def rkmHbN_w256_s2 : List ℕ := rkmCatN
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
private def rkmC_w256_s2_1 : List ℤ := pzigCat
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
private def rkmC_w256_s2_2 : List ℤ := pzigCat
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
private def rkmC_w256_s2_3 : List ℤ := pzigCat
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
private def rkmC_w256_s2_4 : List ℤ := pzigCat
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
private def rkmC_w256_s2_5 : List ℤ := pzigCat
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
private def rkmC_w256_s2_6 : List ℤ := pzigCat
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
private def rkmHbN_w256_s3 : List ℕ := rkmCatN
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
private def rkmC_w256_s3_1 : List ℤ := pzigCat
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
private def rkmC_w256_s3_2 : List ℤ := pzigCat
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
private def rkmC_w256_s3_3 : List ℤ := pzigCat
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
private def rkmC_w256_s3_4 : List ℤ := pzigCat
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
private def rkmC_w256_s3_5 : List ℤ := pzigCat
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
private def rkmC_w256_s3_6 : List ℤ := pzigCat
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
private def rkmC_w256_s3_7 : List ℤ := pzigCat
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
private theorem rkmWC_w256_s0_0 : wSlChk 44 100000000 256 rkmHbN_w256_s0
    0 rkmXsWin_w256_s0_in 0 rkmC_w256_s0_1 2465902853 = true := by decide +kernel
private theorem rkmWC_w256_s0_1 : wSlChk 33 100000000 256 rkmHbN_w256_s0
    0 rkmC_w256_s0_1 12 rkmC_w256_s0_2 3389087035 = true := by decide +kernel
private theorem rkmWC_w256_s0_2 : wSlChk 29 100000000 256 rkmHbN_w256_s0
    12 rkmC_w256_s0_2 41 rkmXsWin_w256_s0_out 5602727344 = true := by decide +kernel
private theorem rkmWC_w256_s1_0 : wSlChk 24 100000000 512 rkmHbN_w256_s1
    41 rkmXsWin_w256_s1_in 66 rkmC_w256_s1_1 3561780607 = true := by decide +kernel
private theorem rkmWC_w256_s1_1 : wSlChk 24 100000000 512 rkmHbN_w256_s1
    66 rkmC_w256_s1_1 96 rkmC_w256_s1_2 4360364131 = true := by decide +kernel
private theorem rkmWC_w256_s1_2 : wSlChk 23 100000000 512 rkmHbN_w256_s1
    96 rkmC_w256_s1_2 128 rkmC_w256_s1_3 4504769772 = true := by decide +kernel
private theorem rkmWC_w256_s1_3 : wSlChk 23 100000000 512 rkmHbN_w256_s1
    128 rkmC_w256_s1_3 162 rkmC_w256_s1_4 4208168154 = true := by decide +kernel
private theorem rkmWC_w256_s1_4 : wSlChk 23 100000000 512 rkmHbN_w256_s1
    162 rkmC_w256_s1_4 196 rkmXsWin_w256_s1_out 4528901432 = true := by decide +kernel
private theorem rkmWC_w256_s2_0 : wSlChk 20 100000000 1024 rkmHbN_w256_s2
    196 rkmXsWin_w256_s2_in 225 rkmC_w256_s2_1 3832473292 = true := by decide +kernel
private theorem rkmWC_w256_s2_1 : wSlChk 19 100000000 1024 rkmHbN_w256_s2
    225 rkmC_w256_s2_1 253 rkmC_w256_s2_2 3747115020 = true := by decide +kernel
private theorem rkmWC_w256_s2_2 : wSlChk 19 100000000 1024 rkmHbN_w256_s2
    253 rkmC_w256_s2_2 282 rkmC_w256_s2_3 4165309388 = true := by decide +kernel
private theorem rkmWC_w256_s2_3 : wSlChk 20 100000000 1024 rkmHbN_w256_s2
    282 rkmC_w256_s2_3 313 rkmC_w256_s2_4 4058981550 = true := by decide +kernel
private theorem rkmWC_w256_s2_4 : wSlChk 20 100000000 1024 rkmHbN_w256_s2
    313 rkmC_w256_s2_4 343 rkmC_w256_s2_5 3706060689 = true := by decide +kernel
private theorem rkmWC_w256_s2_5 : wSlChk 19 100000000 1024 rkmHbN_w256_s2
    343 rkmC_w256_s2_5 373 rkmC_w256_s2_6 3441534351 = true := by decide +kernel
private theorem rkmWC_w256_s2_6 : wSlChk 20 100000000 1024 rkmHbN_w256_s2
    373 rkmC_w256_s2_6 403 rkmXsWin_w256_s2_out 3745641082 = true := by decide +kernel
private theorem rkmWC_w256_s3_0 : wSlChk 21 100000000 1024 rkmHbN_w256_s3
    403 rkmXsWin_w256_s3_in 436 rkmC_w256_s3_1 3932452758 = true := by decide +kernel
private theorem rkmWC_w256_s3_1 : wSlChk 21 100000000 1024 rkmHbN_w256_s3
    436 rkmC_w256_s3_1 468 rkmC_w256_s3_2 4121190499 = true := by decide +kernel
private theorem rkmWC_w256_s3_2 : wSlChk 22 100000000 1024 rkmHbN_w256_s3
    468 rkmC_w256_s3_2 503 rkmC_w256_s3_3 4134616583 = true := by decide +kernel
private theorem rkmWC_w256_s3_3 : wSlChk 22 100000000 1024 rkmHbN_w256_s3
    503 rkmC_w256_s3_3 534 rkmC_w256_s3_4 4398931813 = true := by decide +kernel
private theorem rkmWC_w256_s3_4 : wSlChk 22 100000000 1024 rkmHbN_w256_s3
    534 rkmC_w256_s3_4 565 rkmC_w256_s3_5 3932022834 = true := by decide +kernel
private theorem rkmWC_w256_s3_5 : wSlChk 22 100000000 1024 rkmHbN_w256_s3
    565 rkmC_w256_s3_5 597 rkmC_w256_s3_6 4430168697 = true := by decide +kernel
private theorem rkmWC_w256_s3_6 : wSlChk 22 100000000 1024 rkmHbN_w256_s3
    597 rkmC_w256_s3_6 624 rkmC_w256_s3_7 4313533016 = true := by decide +kernel
private theorem rkmWC_w256_s3_7 : wSlChk 23 100000000 1024 rkmHbN_w256_s3
    624 rkmC_w256_s3_7 652 rkmXsWin_w256_s3_out 4444530939 = true := by decide +kernel
private theorem rkmHbEq_w256_t2 : rkmAllTrueF [
  muxIntListEq (uOfNatHb rkmHbN_w256_s0) rkmHbWin_w256_s0,
  muxIntListEq (uOfNatHb rkmHbN_w256_s1) rkmHbWin_w256_s1,
  muxIntListEq (uOfNatHb rkmHbN_w256_s2) rkmHbWin_w256_s2,
  muxIntListEq (uOfNatHb rkmHbN_w256_s3) rkmHbWin_w256_s3
  ] = true := by decide +kernel
private theorem rkmWinIterF_w256_s0 :
    RkmWinIterSound 106 256 (uOfNatHb rkmHbN_w256_s0) 0 rkmXsWin_w256_s0_in
      41 rkmXsWin_w256_s0_out 11457717232 :=
  rkmChS 106 11457717232 (rkmChS 77 5854989888 (wSlChk_sound rkmWC_w256_s0_0) rkmWC_w256_s0_1
    rfl rfl) rkmWC_w256_s0_2 rfl rfl
private theorem rkmWinIter_w256_s0 :
    RkmWinIterSound 106 256 rkmHbWin_w256_s0 0 rkmXsWin_w256_s0_in
      41 rkmXsWin_w256_s0_out 11457717232 :=
  rkmSubstHbN (rkmWP0 rkmHbEq_w256_t2) rkmWinIterF_w256_s0
/-- Certified `w256` seg `0` (`106` steps). -/
theorem rkmWinSegWalkSnd_w256_s0 :
    RkmWinSegWalkSound 106 ⟨256, rkmHbWin_w256_s0, 0, rkmXsWin_w256_s0_in,
      41, rkmXsWin_w256_s0_out, 11457717232⟩ :=
  @rkmSegWalk_mk 106 256 0 41 11457717232
    rkmHbWin_w256_s0 rkmXsWin_w256_s0_in rkmXsWin_w256_s0_out
    (rkmw_buildHbFrom_length 256 1024 96830113207 256 0) rfl rkmWinIter_w256_s0
private theorem rkmWinIterF_w256_s1 :
    RkmWinIterSound 117 512 (uOfNatHb rkmHbN_w256_s1) 41 rkmXsWin_w256_s1_in
      196 rkmXsWin_w256_s1_out 21163984096 :=
  rkmChS 117 21163984096 (rkmChS 94 16635082664 (rkmChS 71 12426914510 (rkmChS 48 7922144738
    (wSlChk_sound rkmWC_w256_s1_0) rkmWC_w256_s1_1 rfl rfl) rkmWC_w256_s1_2 rfl rfl)
    rkmWC_w256_s1_3 rfl rfl) rkmWC_w256_s1_4 rfl rfl
private theorem rkmWinIter_w256_s1 :
    RkmWinIterSound 117 512 rkmHbWin_w256_s1 41 rkmXsWin_w256_s1_in
      196 rkmXsWin_w256_s1_out 21163984096 :=
  rkmSubstHbN (rkmWP1 rkmHbEq_w256_t2) rkmWinIterF_w256_s1
/-- Certified `w256` seg `1` (`117` steps). -/
theorem rkmWinSegWalkSnd_w256_s1 :
    RkmWinSegWalkSound 117 ⟨512, rkmHbWin_w256_s1, 41, rkmXsWin_w256_s1_in,
      196, rkmXsWin_w256_s1_out, 21163984096⟩ :=
  @rkmSegWalk_mk 117 512 41 196 21163984096
    rkmHbWin_w256_s1 rkmXsWin_w256_s1_in rkmXsWin_w256_s1_out
    (rkmw_buildHbFrom_length 512 1024 51720290598 512 0) rfl rkmWinIter_w256_s1
private theorem rkmWinIterF_w256_s2 :
    RkmWinIterSound 137 1024 (uOfNatHb rkmHbN_w256_s2) 196 rkmXsWin_w256_s2_in
      403 rkmXsWin_w256_s2_out 26697115372 :=
  rkmChS 137 26697115372 (rkmChS 117 22951474290 (rkmChS 98 19509939939 (rkmChS 78 15803879250
    (rkmChS 58 11744897700 (rkmChS 39 7579588312 (wSlChk_sound rkmWC_w256_s2_0) rkmWC_w256_s2_1
    rfl rfl) rkmWC_w256_s2_2 rfl rfl) rkmWC_w256_s2_3 rfl rfl) rkmWC_w256_s2_4 rfl rfl)
    rkmWC_w256_s2_5 rfl rfl) rkmWC_w256_s2_6 rfl rfl
private theorem rkmWinIter_w256_s2 :
    RkmWinIterSound 137 1024 rkmHbWin_w256_s2 196 rkmXsWin_w256_s2_in
      403 rkmXsWin_w256_s2_out 26697115372 :=
  rkmSubstHbN (rkmWP2 rkmHbEq_w256_t2) rkmWinIterF_w256_s2
/-- Certified `w256` seg `2` (`137` steps). -/
theorem rkmWinSegWalkSnd_w256_s2 :
    RkmWinSegWalkSound 137 ⟨1024, rkmHbWin_w256_s2, 196, rkmXsWin_w256_s2_in,
      403, rkmXsWin_w256_s2_out, 26697115372⟩ :=
  @rkmSegWalk_mk 137 1024 196 403 26697115372
    rkmHbWin_w256_s2 rkmXsWin_w256_s2_in rkmXsWin_w256_s2_out
    (rkmw_buildHbFrom_length 1024 1024 29547445255 1024 0) rfl rkmWinIter_w256_s2
private theorem rkmWinIterF_w256_s3 :
    RkmWinIterSound 175 1024 (uOfNatHb rkmHbN_w256_s3) 403 rkmXsWin_w256_s3_in
      652 rkmXsWin_w256_s3_out 33707447139 :=
  rkmChS 175 33707447139 (rkmChS 152 29262916200 (rkmChS 130 24949383184 (rkmChS 108 20519214487
    (rkmChS 86 16587191653 (rkmChS 64 12188259840 (rkmChS 42 8053643257 (wSlChk_sound
    rkmWC_w256_s3_0) rkmWC_w256_s3_1 rfl rfl) rkmWC_w256_s3_2 rfl rfl) rkmWC_w256_s3_3 rfl rfl)
    rkmWC_w256_s3_4 rfl rfl) rkmWC_w256_s3_5 rfl rfl) rkmWC_w256_s3_6 rfl rfl) rkmWC_w256_s3_7
    rfl rfl
private theorem rkmWinIter_w256_s3 :
    RkmWinIterSound 175 1024 rkmHbWin_w256_s3 403 rkmXsWin_w256_s3_in
      652 rkmXsWin_w256_s3_out 33707447139 :=
  rkmSubstHbN (rkmWP3 rkmHbEq_w256_t2) rkmWinIterF_w256_s3
/-- Certified `w256` seg `3` (`175` steps). -/
theorem rkmWinSegWalkSnd_w256_s3 :
    RkmWinSegWalkSound 175 ⟨1024, rkmHbWin_w256_s3, 403, rkmXsWin_w256_s3_in,
      652, rkmXsWin_w256_s3_out, 33707447139⟩ :=
  @rkmSegWalk_mk 175 1024 403 652 33707447139
    rkmHbWin_w256_s3 rkmXsWin_w256_s3_in rkmXsWin_w256_s3_out
    (rkmw_buildHbFrom_length 1536 1024 22125714285 1024 0) rfl rkmWinIter_w256_s3
/-- Cumulative `RkMuxHiW256WinT2` lane witness. -/
theorem rkmHiLane_w256_wint2 : @rkmWinSegWalkSnd_w256_s3 = @rkmWinSegWalkSnd_w256_s3 :=
  (And.intro (Eq.refl rkmHiLane_m256_s8) rfl).right

end
end QuantumComputation.Specs.DickeSol
