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
# Caustic `r = 1024` Halo-16 Walk `w_hi64_m2_r1024` (`FindAllJohnsonRampKickMuxHiW64T00`)

Certifies part `0` of `w_hi64_m2_r1024` (`r = 1024`, halo-16).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Generator list for `w64_m2_s0`. -/
def rkmHbWin_w64_m2_s0 : List ℤ :=
  altBuildHbFrom 16 1024 969474000000 0 16
/-- Entry `rkmXsWin_w64_m2_s0_in`. -/
def rkmXsWin_w64_m2_s0_in : List ℤ := [rkmP 1000000000000000]
/-- Exit `rkmXsWin_w64_m2_s0_out`. -/
def rkmXsWin_w64_m2_s0_out : List ℤ := let p := rkmP; [p 756674982941953, p 570084140728088,
  p 293913476175642, p 119468361389775, p 40504613768324, p 11795051945242, p 3000462806734,
  p 673439184152, p 134046579598, p 23725063625, p 3661333339, p 477037442]
/-- Generator list for `w64_m2_s1`. -/
def rkmHbWin_w64_m2_s1 : List ℤ :=
  altBuildHbFrom 32 1024 655057833333 0 32
/-- Entry `rkmXsWin_w64_m2_s1_in`. -/
def rkmXsWin_w64_m2_s1_in : List ℤ := let p := rkmP; [p 756674982941953, p 570084140728088,
  p 293913476175642, p 119468361389775, p 40504613768324, p 11795051945242, p 3000462806734,
  p 673439184152, p 134046579598, p 23725063625, p 3661333339, p 477037442]
/-- Exit `rkmXsWin_w64_m2_s1_out`. -/
def rkmXsWin_w64_m2_s1_out : List ℤ := let p := rkmP; [p 88194745355047, p 203209539530873,
  p 324970099841867, p 416255792107912, p 452694239002429, p 431428285782502, p 367479115071236,
  p 283511212671334, p 200009369640873, p 129932576379579, p 78138488784020, p 43675263431516,
  p 22758960776612, p 11081789822880, p 5050300467743, p 2156577452096, p 863367652178,
  p 324136983311, p 114021517684, p 37539166740, p 11470690177, p 3221727217, p 774858973,
  p 150623390]
/-- Generator list for `w64_m2_s2`. -/
def rkmHbWin_w64_m2_s2 : List ℤ :=
  altBuildHbFrom 64 1024 360818923076 0 64
/-- Entry `rkmXsWin_w64_m2_s2_in`. -/
def rkmXsWin_w64_m2_s2_in : List ℤ := let p := rkmP; [p 88194745355047, p 203209539530873,
  p 324970099841867, p 416255792107912, p 452694239002429, p 431428285782502, p 367479115071236,
  p 283511212671334, p 200009369640873, p 129932576379579, p 78138488784020, p 43675263431516,
  p 22758960776612, p 11081789822880, p 5050300467743, p 2156577452096, p 863367652178,
  p 324136983311, p 114021517684, p 37539166740, p 11470690177, p 3221727217, p 774858973,
  p 150623390]
/-- Exit `rkmXsWin_w64_m2_s2_out`. -/
def rkmXsWin_w64_m2_s2_out : List ℤ := let p := rkmP; [p 9421887074, p 52080711917, p 199427998454,
  p 616735071797, p 1631529104764, p 3813788865725, p 8037787074652, p 15487501058067,
  p 27559947542161, p 45641629081233, p 70767850640486, p 103226895053935, p 142212482935478,
  p 185645759851147, p 230261531292908, p 271989472537043, p 306574221599350, p 330300442498932,
  p 340650569115500, p 336733208853979, p 319386976730136, p 290948920008040, p 254766918929644,
  p 214587969755237, p 173968016489310, p 135819129599832, p 102157417276046, p 74054820514803,
  p 51753138385431, p 34875290571671, p 22665453384097, p 14207684735896, p 8590352086323,
  p 5009774275306, p 2817784315938, p 1528364171526, p 799248256521, p 402808878750, p 195663353289,
  p 91478102780, p 41171525408, p 17791686098, p 7344923962, p 2817518819, p 979278461, p 278851433]
/-- Generator list for `w64_m2_s3`. -/
def rkmHbWin_w64_m2_s3 : List ℤ :=
  altBuildHbFrom 128 1024 181682400000 0 128
/-- Entry `rkmXsWin_w64_m2_s3_in`. -/
def rkmXsWin_w64_m2_s3_in : List ℤ := let p := rkmP; [p 9421887074, p 52080711917, p 199427998454,
  p 616735071797, p 1631529104764, p 3813788865725, p 8037787074652, p 15487501058067,
  p 27559947542161, p 45641629081233, p 70767850640486, p 103226895053935, p 142212482935478,
  p 185645759851147, p 230261531292908, p 271989472537043, p 306574221599350, p 330300442498932,
  p 340650569115500, p 336733208853979, p 319386976730136, p 290948920008040, p 254766918929644,
  p 214587969755237, p 173968016489310, p 135819129599832, p 102157417276046, p 74054820514803,
  p 51753138385431, p 34875290571671, p 22665453384097, p 14207684735896, p 8590352086323,
  p 5009774275306, p 2817784315938, p 1528364171526, p 799248256521, p 402808878750, p 195663353289,
  p 91478102780, p 41171525408, p 17791686098, p 7344923962, p 2817518819, p 979278461, p 278851433]
/-- Exit `rkmXsWin_w64_m2_s3_out`. -/
def rkmXsWin_w64_m2_s3_out : List ℤ := let p := rkmP; [p 347196033, p 826871172, p 1966445815,
  p 4490216783, p 9763722931, p 20656357878, p 42090318093, p 83236573214, p 159353879069,
  p 296001641502, p 533809144186, p 934743989851, p 1590644536791, p 2631738523727, p 4235562985760,
  p 6633766370186, p 10115213626458, p 15022006332080, p 21735430510723, p 30651075310727,
  p 42139664156195, p 56497774076486, p 73889639664971, p 94287938164860, p 117422461695604,
  p 142745799547898, p 169426429798652, p 196375273905380, p 222309165740283, p 245846620013653,
  p 265627990300129, p 280445200727444, p 289363446692320, p 291819390915186, p 287678948384649,
  p 277249294164166, p 261241682878296, p 240692069693163, p 216851538856265, p 191062411761037,
  p 164637064764640, p 138753439642752, p 114378717042759, p 92225219234009, p 72739881556954,
  p 56121185836147, p 42356534319714, p 31272380677479, p 22586592903287, p 15958479919467,
  p 11030137058902, p 7457778137893, p 4932632963113, p 3191277158866, p 2019594686559,
  p 1250114025413, p 756806184672, p 448145692767, p 259447463965, p 146899556331, p 81261485390,
  p 43895542756, p 23167099919, p 11830271997, p 5866385950, p 2690787217, p 1094604954,
  p 347398710]
/-- Generator list for `w64_m2_s4`. -/
def rkmHbWin_w64_m2_s4 : List ℤ :=
  altBuildHbFrom 256 1024 95881890909 0 256
/-- Entry `rkmXsWin_w64_m2_s4_in`. -/
def rkmXsWin_w64_m2_s4_in : List ℤ := let p := rkmP; [p 347196033, p 826871172, p 1966445815,
  p 4490216783, p 9763722931, p 20656357878, p 42090318093, p 83236573214, p 159353879069,
  p 296001641502, p 533809144186, p 934743989851, p 1590644536791, p 2631738523727, p 4235562985760,
  p 6633766370186, p 10115213626458, p 15022006332080, p 21735430510723, p 30651075310727,
  p 42139664156195, p 56497774076486, p 73889639664971, p 94287938164860, p 117422461695604,
  p 142745799547898, p 169426429798652, p 196375273905380, p 222309165740283, p 245846620013653,
  p 265627990300129, p 280445200727444, p 289363446692320, p 291819390915186, p 287678948384649,
  p 277249294164166, p 261241682878296, p 240692069693163, p 216851538856265, p 191062411761037,
  p 164637064764640, p 138753439642752, p 114378717042759, p 92225219234009, p 72739881556954,
  p 56121185836147, p 42356534319714, p 31272380677479, p 22586592903287, p 15958479919467,
  p 11030137058902, p 7457778137893, p 4932632963113, p 3191277158866, p 2019594686559,
  p 1250114025413, p 756806184672, p 448145692767, p 259447463965, p 146899556331, p 81261485390,
  p 43895542756, p 23167099919, p 11830271997, p 5866385950, p 2690787217, p 1094604954,
  p 347398710]
/-- Exit `rkmXsWin_w64_m2_s4_out`. -/
def rkmXsWin_w64_m2_s4_out : List ℤ := let p := rkmP; [p 191176485, p 542834926, p 1088933744,
  p 2283538443, p 4463094050, p 8621341503, p 16335476341, p 30004205833, p 54055399808,
  p 95027522724, p 163515540244, p 275154054864, p 453206836709, p 730901230731, p 1154422562924,
  p 1786624020776, p 2709985759576, p 4029962706626, p 5877019310646, p 8407366860128,
  p 11800989394825, p 16256996315971, p 21985159807271, p 29193281399061, p 38071230210210,
  p 48770771247978, p 61384437205361, p 75923406339991, p 92297575523008, p 110300951845868,
  p 129602948260693, p 149750212197796, p 170178353091163, p 190234953360608, p 209212665279375,
  p 226389708865824, p 241076170213123, p 252659666669143, p 260648295688849, p 264705245365725,
  p 264671906664059, p 260578353204230, p 252638361169226, p 241231899008537, p 226875033856450,
  p 210181947267481, p 191822709109273, p 172479527677718, p 152807334389946, p 133399431584650,
  p 114762428892257, p 97300143491544, p 81306431008767, p 66967445438415, p 54369663449670,
  p 43514146450674, p 34332924061383, p 26706703546020, p 20482545408126, p 15488872650187,
  p 11549194216330, p 8491770751492, p 6157098527889, p 4402607057245, p 3104558363787,
  p 2159129477643, p 1480958368072, p 1001866877801, p 668520479468, p 439921047377, p 285562156712,
  p 182752471047, p 115325630348, p 71740355797, p 43909887197, p 26467180413, p 15577479976,
  p 8939078520, p 4917442791, p 2513612845, p 1184875044, p 419565309, p 108086081]
/-- Generator list for `w64_m2_s5`. -/
def rkmHbWin_w64_m2_s5 : List ℤ :=
  altBuildHbFrom 512 1024 51685843478 0 512
/-- Entry `rkmXsWin_w64_m2_s5_in`. -/
def rkmXsWin_w64_m2_s5_in : List ℤ := let p := rkmP; [p 191176485, p 542834926, p 1088933744,
  p 2283538443, p 4463094050, p 8621341503, p 16335476341, p 30004205833, p 54055399808,
  p 95027522724, p 163515540244, p 275154054864, p 453206836709, p 730901230731, p 1154422562924,
  p 1786624020776, p 2709985759576, p 4029962706626, p 5877019310646, p 8407366860128,
  p 11800989394825, p 16256996315971, p 21985159807271, p 29193281399061, p 38071230210210,
  p 48770771247978, p 61384437205361, p 75923406339991, p 92297575523008, p 110300951845868,
  p 129602948260693, p 149750212197796, p 170178353091163, p 190234953360608, p 209212665279375,
  p 226389708865824, p 241076170213123, p 252659666669143, p 260648295688849, p 264705245365725,
  p 264671906664059, p 260578353204230, p 252638361169226, p 241231899008537, p 226875033856450,
  p 210181947267481, p 191822709109273, p 172479527677718, p 152807334389946, p 133399431584650,
  p 114762428892257, p 97300143491544, p 81306431008767, p 66967445438415, p 54369663449670,
  p 43514146450674, p 34332924061383, p 26706703546020, p 20482545408126, p 15488872650187,
  p 11549194216330, p 8491770751492, p 6157098527889, p 4402607057245, p 3104558363787,
  p 2159129477643, p 1480958368072, p 1001866877801, p 668520479468, p 439921047377, p 285562156712,
  p 182752471047, p 115325630348, p 71740355797, p 43909887197, p 26467180413, p 15577479976,
  p 8939078520, p 4917442791, p 2513612845, p 1184875044, p 419565309, p 108086081]
/-- Exit `rkmXsWin_w64_m2_s5_out`. -/
def rkmXsWin_w64_m2_s5_out : List ℤ := let p := rkmP; let n := rkmN; [n 330640175, n 619761320,
  n 793976535, n 513476018, p 334323463, p 2103313052, p 4844835913, p 8315375451, p 11686643339,
  p 12949752764, p 9159986010, n 3969566424, n 31065873477, n 76203919174, n 140680762623,
  n 219735797614, n 298271753108, n 345451492301, n 308736430654, n 108233610612, p 368804506333,
  p 1270749877920, p 2782171126755, p 5120121274559, p 8525661997129, p 13251496142707,
  p 19543754905378, p 27621407752047, p 37652860642746, p 49732475756921, p 63860363311924,
  p 79925535032799, p 97697191200121, p 116823770048160, p 136841685880780, p 157193660587965,
  p 177255293651474, p 196368211203315, p 213877338792376, p 229168803239148, p 241706335967427,
  p 251061615674956, p 256938087628927, p 259185035620157, p 257801319369961, p 252930533927413,
  p 244845784425185, p 233928408258166, p 220641234884808, p 205498779506282, p 189038036805137,
  p 171789952770360, p 154255367268773, p 136885239123336, p 120066455017109, p 104113212291239,
  p 89263714734914, p 75681771051386, p 63462105968460, p 52637929819241, p 43191449449029,
  p 35063987320336, p 28166713506471, p 22390798208390, p 17615717208863, p 13717399272928,
  p 10573604665883, p 8068419838732, p 6095439699692, p 4559386540277, p 3376933126054,
  p 2476778563154, p 1798875431822, p 1294009859133, p 921915574072, p 650501562946, p 454656900576,
  p 314710247293, p 215676169158, p 146412132548, p 98289756188, p 65311156522, p 42883983616,
  p 27702779166, p 17642187970, p 10966399060, p 6638431106, p 3804672041, p 1983653402,
  p 929957580, p 320219917]
/-- Generator list for `w64_m2_s6`. -/
def rkmHbWin_w64_m2_s6 : List ℤ :=
  altBuildHbFrom 1024 1024 29643724279 0 1024
/-- Entry `rkmXsWin_w64_m2_s6_in`. -/
def rkmXsWin_w64_m2_s6_in : List ℤ := let p := rkmP; let n := rkmN; [n 330640175, n 619761320,
  n 793976535, n 513476018, p 334323463, p 2103313052, p 4844835913, p 8315375451, p 11686643339,
  p 12949752764, p 9159986010, n 3969566424, n 31065873477, n 76203919174, n 140680762623,
  n 219735797614, n 298271753108, n 345451492301, n 308736430654, n 108233610612, p 368804506333,
  p 1270749877920, p 2782171126755, p 5120121274559, p 8525661997129, p 13251496142707,
  p 19543754905378, p 27621407752047, p 37652860642746, p 49732475756921, p 63860363311924,
  p 79925535032799, p 97697191200121, p 116823770048160, p 136841685880780, p 157193660587965,
  p 177255293651474, p 196368211203315, p 213877338792376, p 229168803239148, p 241706335967427,
  p 251061615674956, p 256938087628927, p 259185035620157, p 257801319369961, p 252930533927413,
  p 244845784425185, p 233928408258166, p 220641234884808, p 205498779506282, p 189038036805137,
  p 171789952770360, p 154255367268773, p 136885239123336, p 120066455017109, p 104113212291239,
  p 89263714734914, p 75681771051386, p 63462105968460, p 52637929819241, p 43191449449029,
  p 35063987320336, p 28166713506471, p 22390798208390, p 17615717208863, p 13717399272928,
  p 10573604665883, p 8068419838732, p 6095439699692, p 4559386540277, p 3376933126054,
  p 2476778563154, p 1798875431822, p 1294009859133, p 921915574072, p 650501562946, p 454656900576,
  p 314710247293, p 215676169158, p 146412132548, p 98289756188, p 65311156522, p 42883983616,
  p 27702779166, p 17642187970, p 10966399060, p 6638431106, p 3804672041, p 1983653402,
  p 929957580, p 320219917]
/-- Exit `rkmXsWin_w64_m2_s6_out`. -/
def rkmXsWin_w64_m2_s6_out : List ℤ := let p := rkmP; let n := rkmN; [p 214739447, p 543203834,
  p 726720134, p 498093171, n 267812904, n 1351462001, n 2228455853, n 2578638769, n 1746397482,
  p 351234776, p 3162676333, p 5882030364, p 7035822208, p 5355746807, p 518147851, n 6734006634,
  n 14414620111, n 19066693837, n 17612602770, n 8089613858, p 9090385918, p 29985692470,
  p 47775562223, p 54222961289, p 41981373085, p 8147071175, n 43269973628, n 100499775049,
  n 145012986305, n 155710560951, n 115696524081, n 18337903333, p 126130738900, p 288409497946,
  p 423205169471, p 477256434084, p 402759239115, p 173147835985, n 202813212874, n 672129560494,
  n 1137903800497, n 1471253952977, n 1534510514122, n 1211749063314, n 443681231882,
  p 742850516587, p 2216574122819, p 3740741159926, p 4993866093257, p 5611403642705,
  p 5244133636572, p 3626028407568, p 641146623471, n 3622014174775, n 8838553847254,
  n 14443894024533, n 19664943195580, n 23581384080274, n 25212209105914, n 23617860547893,
  n 18004728575935, n 7819346271477, p 7178567015452, p 26873421057155, p 50786888237822,
  p 78106015389756, p 107742520865174, p 138418005842479, p 168762588700667, p 197418199522947,
  p 223136166409083, p 244859806864473, p 261785452455920, p 273399248988893, p 279488561784016,
  p 280128904244807, p 275651945369566, p 266598845906830, p 253664066715305, p 237636696204383,
  p 219344132746114, p 199600641133114, p 179165987432326, p 158714044063014, p 138812358209854,
  p 119911763925794, p 102345417285593, p 86335036653660, p 72001894869861, p 59382000895018,
  p 48442692770136, p 39098765908855, p 31228411622723, p 24687406328956, p 19320569851368,
  p 14971100142391, p 11488129279539, p 8731144928284, p 6573281851730, p 4902624849137,
  p 3623002358645, p 2653172206955, p 1925454382756, p 1384864904727, p 987331418309,
  p 697715225205, p 488642991650, p 339213397843, p 233419844033, p 159097060524, p 107331367823,
  p 71616620214, p 47281871482, p 30666633074, p 19507675075, p 12169761716, p 7293427099,
  p 4075191749, p 2084303851, p 930525094, p 283332302]
/-- Generator list for `w64_m2_s7a`. -/
def rkmHbWin_w64_m2_p7a : List ℤ :=
  altBuildHbFrom 1792 1024 20052279735 0 1024
/-- Entry `rkmXsWin_w64_m2_s7a_in`. -/
def rkmXsWin_w64_m2_s7a_in : List ℤ := let p := rkmP; let n := rkmN; [p 214739447, p 543203834,
  p 726720134, p 498093171, n 267812904, n 1351462001, n 2228455853, n 2578638769, n 1746397482,
  p 351234776, p 3162676333, p 5882030364, p 7035822208, p 5355746807, p 518147851, n 6734006634,
  n 14414620111, n 19066693837, n 17612602770, n 8089613858, p 9090385918, p 29985692470,
  p 47775562223, p 54222961289, p 41981373085, p 8147071175, n 43269973628, n 100499775049,
  n 145012986305, n 155710560951, n 115696524081, n 18337903333, p 126130738900, p 288409497946,
  p 423205169471, p 477256434084, p 402759239115, p 173147835985, n 202813212874, n 672129560494,
  n 1137903800497, n 1471253952977, n 1534510514122, n 1211749063314, n 443681231882,
  p 742850516587, p 2216574122819, p 3740741159926, p 4993866093257, p 5611403642705,
  p 5244133636572, p 3626028407568, p 641146623471, n 3622014174775, n 8838553847254,
  n 14443894024533, n 19664943195580, n 23581384080274, n 25212209105914, n 23617860547893,
  n 18004728575935, n 7819346271477, p 7178567015452, p 26873421057155, p 50786888237822,
  p 78106015389756, p 107742520865174, p 138418005842479, p 168762588700667, p 197418199522947,
  p 223136166409083, p 244859806864473, p 261785452455920, p 273399248988893, p 279488561784016,
  p 280128904244807, p 275651945369566, p 266598845906830, p 253664066715305, p 237636696204383,
  p 219344132746114, p 199600641133114, p 179165987432326, p 158714044063014, p 138812358209854,
  p 119911763925794, p 102345417285593, p 86335036653660, p 72001894869861, p 59382000895018,
  p 48442692770136, p 39098765908855, p 31228411622723, p 24687406328956, p 19320569851368,
  p 14971100142391, p 11488129279539, p 8731144928284, p 6573281851730, p 4902624849137,
  p 3623002358645, p 2653172206955, p 1925454382756, p 1384864904727, p 987331418309,
  p 697715225205, p 488642991650, p 339213397843, p 233419844033, p 159097060524, p 107331367823,
  p 71616620214, p 47281871482, p 30666633074, p 19507675075, p 12169761716, p 7293427099,
  p 4075191749, p 2084303851, p 930525094, p 283332302]
/-- Exit `rkmXsWin_w64_m2_s7a_out`. -/
def rkmXsWin_w64_m2_s7a_out : List ℤ := let p := rkmP; let n := rkmN; [p 111499607, p 349943685,
  p 446220306, p 164697531, n 477636990, n 1069199019, n 1359003491, n 947324027, p 292282733,
  p 1833368790, p 2904467790, p 2793779825, p 1013002696, n 2082654423, n 5238495484, n 6865510218,
  n 5332876982, n 526937488, p 6351859736, p 12584889689, p 14655544822, p 10178914754, n 915026850,
  n 15586480429, n 27984082013, n 31433070256, n 21414736805, p 2217539914, p 33038163346,
  p 59645894612, p 68895586333, p 50885134285, p 4457214327, n 59787409146, n 120822088513,
  n 152272401642, n 131806279739, n 51108632240, p 77173910748, p 218224202993, p 321921246075,
  p 337712047921, p 232461484331, p 6898979137, n 295152072111, n 591364001303, n 777924055621,
  n 758675253734, n 478413625343, p 49745829000, p 731333239088, p 1399120815262, p 1845777851543,
  p 1874241047511, p 1355478889362, p 280587032017, n 1210340878416, n 2831456551807,
  n 4191885902237, n 4870177049026, n 4509266286458, n 2912697103711, n 121486455233,
  p 3548231796876, p 7519542161873, p 11023152739725, p 13214178468006, p 13317823490084,
  p 10781102949432, p 5404327977421, n 2571892802089, n 12441112457825, n 23072953035072,
  n 33019887008768, n 40674467694812, n 44454362508700, n 42991251708043, n 35297582726283,
  n 20888704037558, p 151487592521, p 27169563965978, p 59002517185465, p 94088522781852,
  p 130612432290150, p 166668093416274, p 200418134172804, p 230234860795219, p 254810705918980,
  p 273229489131109, p 284996633188129, p 290031930593842, p 288628524446600, p 281388515967802,
  p 269143778086491, p 252871519348331, p 233612047024271, p 212396331217167, p 190186846715149,
  p 167833379505271, p 146045859365285, p 125381791335733, p 106245487280193, p 88898441527360,
  p 73475992095132, p 60008140079896, p 48441709025477, p 38663008309871, p 30517653494226,
  p 23827907827807, p 18407572705664, p 14072557318227, p 10648596582843, p 7976890895193,
  p 5916587439855, p 4345806018997, p 3161359936088, p 2278026432176, p 1626113756076,
  p 1149878370719, p 805636422099, p 559234521789, p 384499902316, p 261851324546, p 176605865342,
  p 117855195730, p 77773928838, p 50739354196, p 32688179287, p 20578884909, p 12711407747,
  p 7635794645, p 4289808346, p 2189437127, p 980371577, p 305111559]

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
private def rkmPhb_w64_m2_s0 : List ℕ := uNatCatN
  [
   [248185344000000,339675799477009,401713341125139,446766607027885,479669244394806,
    502834678739673,517593806614923,524678039032561,524420021786059,516830581122401,
    501599514312781,478020486896397,444793149790946,399545630059628,337510646061914,
    246360874193101]]
private def rkmPhb_w64_m2_s1 : List ℕ := uNatCatN
  [
   [237156268041795,329946329705804,397334561123015,450870172909381,495078132191515,
    532297270654183,563922240519609,590860713208187,613738502902457,633004181950799,
    648987452958840,661933914794909,672026765210060,679400772243681,684151382717243,
    686340576552831,686000382937605,683134560679871,677718668221153,669698528884018,
    658986878029855,645457705161357,628937396898666,609191106329046,585901537810526,
    558634917966130,526783808725766,489464543272441,445316004591356,392050881936150,
    325236049330902,233538912466313]]
private def rkmPhb_w64_m2_s2 : List ℕ := uNatCatN
  [
   [184739288614912,259085072338017,314630790639508,360186213582876,399190332279806,
    433419078695214,463934006294313,491430604674353,516394280939496,539179867291643,
    560056061028297,579232047248594,596874336067080,613117885523476,628073717493945,
    641834290760679,654477388978917,666068995554471,676665459312203,686315152254052,
    695059756113064,702935272593879,709972824442333,716199295660794,721637846152000,
    726308326880085,730227615036201,733409883874163,735866818297304,737607784563448,
    738639960375960,738968429964969,738596247402975,737524470244806,735752164555670,
    733276381428079,730092104129800,726192164012188,721567122177432,716205112578731,
    710091640613568,703209329240284,695537602028034,687052289094043,677725137235610,
    667523199205078,656408068220002,644334911245784,631251236451431,617095303502987,
    601794045059561,585260305573223,567389104587028,548052469577008,527092107760030,
    504308697656026,479445670939222,452163555787647,421997128543675,388278716773377,
    349987659710791,305413983337633,251241923793061,178966185845696]]
private def rkmPhb_w64_m2_s3 : List ℕ := uNatCatN
  [
   [131552109631740,185224115276725,225846935330810,259621543226385,288960702537048,
    315107055002821,338801775993953,360529668303300,380628747268401,399346015607015,
    416868594083329,433342346311112,448883643615237,463587128955811,477531028515310,
    490780897033851,503392327546562,515412955810133,526883971904438,537841279686850,
    548316399606086,558337181171952,567928372019956,577112077398693,585908134851790,
    594334422499075,602407114772658,610140896165467,617549141126290,624644066432432,
    631436861014420,637937797175543,644156326356756,650101161983545,655780351451475,
    661201338929146,666371020357164,671295791781943,675981591970117,680433940093115,
    684657969144137,688658455645555,692439846118888,696006280718446,699361614370645,
    702509435711570,705453084073924,708195664739521,710740062643845,713088954694049,
    715244820840212,717209954021225,718986469090805,720576310815321,721981261023208,
    723202944975240,724242837015790,725102265557067,725782417441109,726284341717865,
    726608952871857,726757033524601,726729236635109,726526087216220,726147983580298,
    725595198123709,724867877655598,723966043272639,722889589777567,721638284635464,
    720211766457766,718609542999846,716830988653656,714875341412246,712741699277940,
    710429016080450,707936096665113,705261591404686,702403989980558,699361614370645,
    696132610971544,692714941771367,689106374476922,685304471484162,681306577563693,
    677109806113226,672711023805520,668106833432916,663293554717232,658267202815336,
    653023464205033,647557669581123,641864763325711,635939269037319,629775250506756,
    623366267409796,616705324841864,609784815641040,602596454223299,595131200375618,
    587379171101886,579329538171326,570970408449320,562288683355044,553269892832391,
    543897997960557,534155154655671,524021428662798,513474448971998,502488982562784,
    491036407460100,479084052660892,466594361291301,453523815339114,439821533113809,
    425427408526069,410269594397991,394261022269896,377294464457813,359235312822909,
    339910631034934,319091815077034,296465597091142,271582069958215,243752518029184,
    211820797918455,173539315667620,123124381030565]]
private def rkmPhb_w64_m2_s4 : List ℕ := uNatCatN
  [
   [138512666788937,169226947012646,194925974116861,217396197923584,237556087469838,
    255952572740610,272942854655325,288775626704623,303632379937276,317650438769831,
    330936731916557,343576484395101,355638949194000,367181325553527,378251519790316,
    388890141285706,399131977886927,409007107776765,418541751739604,427758936346214,
    436679016986581,445320095376698,453698356481448,461828343109667,469723181738735,
    477394769770339,484853931987205,492110552194303,499173684699774,506051649291695,
    512752112607403,519282158209165,525648347228423,531856771088098,537913097534638,
    543822610991136,549590248066747,555220628916066,560718085027544,566086683926736,
    571330251203869,576452390212382,581456499733156,586345789856002,591123296293957,
    595791893315731,600354305456270,604813118143885,609170787364249,613429648465998,
    617591924199495,621659732068932,625635091068229,629519927862755,633316082471648,
    637025313499204,640649302958327,644189660724242,647647928652536,651025584391886,
    654324044918672,657544669817811,660688764331686,663757582196820,666752328286012,
    669674161071910,672524194926473,675303502269395,678013115577335,680654029264728,
    683227201445956,685733555587784,688173982060185,690549339592966,692860456644976,
    695108132692077,697293139439588,699416221964377,701478099791414,703479467909161,
    705420997727853,707303337984397,709127115597323,710892936474946,712601386279691,
    714253031151261,715848418391170,717388077110954,718872518846207,720302238138436,
    721677713086592,722999405869974,724267763244130,725483217011214,726646184466195,
    727757068820194,728816259602152,729824133039941,730781052421953,731687368440146,
    732543419515443,733349532106322,734106021001397,734813189596711,735471330158433,
    736080724071593,736641642075451,737154344486061,737619081406533,738036092925499,
    738405609304208,738727851152677,739003029595296,739231346426223,739412994254932,
    739548156642193,739637008226792,739679714843237,739676433630702,739627313133413,
    739532493392694,739392106030833,739206274326947,738975113284981,738698729693961,
    738377222180627,738010681254519,737599189345609,737142820834531,736641642075451,
    736095711411614,735505079183575,734869787730116,734189871381828,733465356447325,
    732696261192046,731882595809574,731024362385385,730121554852949,729174158942043,
    728182152119159,727145503519851,726064173872854,724938115415773,723767271802154,
    722551577999690,721290960179306,719985335594866,718634612453179,717238689773989,
    715797457239597,714310795033726,712778573669214,711200653804097,709576886045601,
    707907110741513,706191157758392,704428846246009,702619984387379,700764369133690],
   [698861785923387,696912008384609,694914798020129,692869903873865,690777062177965,
    688635995979423,686446414745041,684208013943533,681920474603426,679583462845315,
    677196629386952,674759609019468,672272020052960,669733463729477,667143523601317,
    664501764872351,661807733699929,659060956454688,656260938935387,653407165535614,
    650499098358980,647536176279075,644517813940167,641443400694241,638312299469591,
    635123845565723,631877345368851,628572074981723,625207278760897,621782167753955,
    618295918028350,614747668882796,611136520931152,607461534047720,603721725161725,
    599916065887423,596043479974805,592102840564236,588092967226454,584012622767263,
    579860509773836,575635266876804,571335464699203,566959601459784,562506098194112,
    557973293552231,553359438126257,548662688255086,543881099246229,539012617946427,
    534055074583052,529006173786960,523863484694228,518624430008631,513286273888365,
    507846108498766,502300839046961,496647167083547,490881571819439,485000289161563,
    478999288117248,472874244151767,466620509003527,460233076363200,453706542701630,
    447035062380338,440212295989337,433231350618564,426084710466389,418764155800870,
    411260667788740,403564316054565,395664124973885,387547913562195,379202102285654,
    370611478027577,361758905557659,352624969807042,343187527496703,333421138328109,
    323296333625423,312778661715077,301827420540283,290393942211108,278419219008109,
    265830532389754,252536519389968,238419687060681,223324546900353,207037756160785,
    189252491401660,169498356821722,146984405658446,120170269893728,85084360396294]]
private def rkmPhb_w64_m2_s5 : List ℕ := uNatCatN
  [
   [568635012564125,571620566781063,574566078296363,577472215360456,580339624732527,
    583168932649217,585960745737424,588715651875094,591434221003602,594117005895013,
    596764542877257,599377352520023,601955940283938,604500797135422,607012400129410,
    609491212961986,611937686494803,614352259253044,616735357898531,619087397679499,
    621408782858425,623699907119207,625961153954911,628192897037202,630395500568513,
    632569319617937,634714700441739,636831980789361,638921490195703,640983550260433,
    643018474915030,645026570678198,647008136900286,648963465997273,650892843674865,
    652796549143217,654674855322736,656528029041446,658356331224305,660160017074894,
    661939336249834,663694533026302,665425846462962,667133510554632,668817754380992,
    670478802249583,672116873833408,673732184303331,675324944455559,676895360834394,
    678443635850492,679969967894810,681474551448445,682957577188541,684419232090426,
    685859699526161,687279159359627,688677788038327,690055758682014,691413241168300,
    692750402215348,694067405461791,695364411543972,696641578170625,697899060195088,
    699137009685166,700355575990708,701554905809021,702735143248176,703896429888302,
    705038904840953,706162704806596,707267964130315,708354814855793,709423386777623,
    710473807492029,711506202446037,712520694985170,713517406399702,714496455969546,
    715457961007796,716402036903001,717328797160187,718238353440696,719130815600868,
    720006291729604,720864888184863,721706709629113,722531859063784,723340437862745,
    724132545804853,724908281105583,725667740447789,726411019011619,727138210503604,
    727849407184952,728544699899081,729224178098398,729887929870365,730536041962862,
    731168599808874,731785687550527,732387388062481,732973782974711,733544952694692,
    734100976429003,734641932204368,735167896888149,735678946208318,736175154772907,
    736656596088960,737123342581007,737575465609056,738013035486139,738436121495406,
    738844791906792,739239113993256,739619154046625,739984977393025,740336648407939,
    740674230530882,740997786279709,741307377264574,741603064201533,741884906925818,
    742152964404774,742407294750483,742647955232068,742875002287703,743088491536312,
    743288477788992,743475015060145,743648156578342,743807954796908,743954461404255,
    744087727333955,744207802774559,744314737179179,744408579274825,744489377071513,
    744557177871146,744612028276163,744653974197985,744683060865236,744699332831756,
    744702833984420,744693607550745,744671696106307,744637141581969,744589985270915,
    744530267835502,744458029313936,744373309126765,744276146083200,744166578387268,
    744044643643798,743910378864235,743763820472305,743605004309511,743433965640479],
   [743250739158152,743055358988825,742847858697041,742628271290338,742396629223851,
    742152964404774,741897308196682,741629691423717,741350144374635,741058696806724,
    740755377949587,740440216508796,740113240669416,739774478099405,739423955952883,
    739061700873286,738687738996383,738302095953186,737904796872731,737495866384740,
    737075328622168,736643207223631,736199525335716,735744305615177,735277570231016,
    734799340866452,734309638720771,733808484511069,733295898473878,732771900366688,
    732236509469344,731689744585348,731131624043037,730562165696661,729981386927342,
    729389304643929,728785935283737,728171294813188,727545398728325,726908262055229,
    726259899350319,725600324700547,724929551723474,724247593567244,723554462910440,
    722850171961826,722134732459989,721408155672850,720670452397075,719921632957366,
    719161707205634,718390684520063,717608573804049,716815383485028,716011121513176,
    715195795360000,714369412016793,713531977992984,712683499314345,711823981521087,
    710953429665820,710071848311389,709179241528577,708275612893675,707360965485923,
    706435301884808,705498624167229,704550933904520,703592232159329,702622519482358,
    701641795908947,700650060955516,699647313615853,698633552357242,697608775116441,
    696572979295493,695526161757376,694468318821486,693399446258945,692319539287746,
    691228592567702,690126600195238,689013555697972,687889452029130,686754281561748,
    685608036082691,684450706786462,683282284268803,682102758520092,680912118918511,
    679710354223003,678497452565994,677273401445887,676038187719309,674791797593122,
    673534216616172,672265429670793,670985420964029,669694174018598,668391671663570,
    667077896024757,665752828514811,664416449823017,663068739904769,661709677970738,
    660339242475694,658957411107000,657564160772748,656159467589546,654743306869918,
    653315653109338,651876479972860,650425760281345,648963465997273,647489568210116,
    646004037121276,644506842028556,642997951310158,641477332408197,639944951811705,
    638400775039112,636844766620197,635276890077469,633697107906984,632105381558560,
    630501671415379,628885936772948,627258135817412,625618225603170,623966162029797,
    622301899818228,620625392486189,618936592322841,617235450362609,615521916358172,
    613795938752576,612057464650440,610306439788224,608542808503515,606766513703309,
    604977496831225,603175697833642,601361055124690,599533505550063,597692984349604,
    595839425118614,593972759767831,592092918482032,590199829677190,588293419956139,
    586373614062673,584440334834028,582493503151661,580533037890269,578558855864965,
    576570871776527,574568998154652,572553145299107,570523221218696,568479131567946],
   [566420779581398,564348066005415,562260889027360,560159144202065,558042724375423,
    555911519604994,553765417077476,551604301022892,549428052625320,547236549930028,
    545029667746807,542807277549323,540569247370302,538315441692311,536045721333938,
    533759943331112,531457960813318,529139622874446,526804774437978,524453256116213,
    522084904063211,519699549821111,517297020159454,514877136907130,512439716776516,
    509984571179388,507511506034101,505020321563559,502510812083419,499982765779946,
    497435964476913,494870183390864,492285190874040,489680748144197,487056609000484,
    484412519524523,481748217765702,479063433409696,476357887429084,473631291714877,
    470883348687689,468113750887131,465322180537956,462508309091311,459671796739337,
    456812291901205,453929430678515,451022836277802,448092118397681,445136872577975,
    442156679507890,439151104290067,436119695657005,433061985136077,429977486158915,
    426865693110626,423726080313755,420558100941481,417361185853916,414134742350771,
    410878152832924,407590773364647,404271932127322,400920927754503,397537027536989,
    394119465485318,390667440235590,387180112782884,383656604024590,380095992093846,
    376497309460737,372859539776067,369181614429239,365462408787941,361700738082975,
    357895352896441,354044934205554,350148087927442,346203338902138,342209124241426,
    338163785959944,334065562791586,329912581078394,325702844600171,321434223190371,
    317104439956469,312711056889907,308251458610532,303722833941235,299122154948039,
    294446153006193,289691291359771,284853733525873,279929306747601,274913459513381,
    269801211921170,264587097357328,259265093557506,253828540587113,248270042574241,
    242581349079665,236753210696926,230775201692096,224635499994363,218320611291300,
    211815018827585,205100732887332,198156702432224,190958033554079,183474931053913,
    175671232910341,167502328145245,158912107861507,149828336636307,140155311533161,
    129761569096885,118457819345205,105953508265645,91759477864963,74921870445233,52977964352337]]
private def rkmPhb_w64_m2_s6 : List ℕ := uNatCatN
  [
   [717998907230577,718614151694565,719222311238268,719823418468701,720417505676297,
    721004604839385,721584747628578,722157965411078,722724289254911,723283749933075,
    723836377927625,724382203433673,724921256363322,725453566349534,725979162749918,
    726498074650463,727010330869198,727515959959789,728014990215077,728507449670547,
    728993366107745,729472767057632,729945679803876,730412131386101,730872148603063,
    731325758015788,731772985950644,732213858502373,732648401537060,733076640695063,
    733498601393890,733914308831025,734323787986710,734727063626686,735124160304880,
    735515102366055,735899913948413,736278618986158,736651241212017,737017804159719,
    737378331166437,737732845375189,738081369737199,738423927014228,738760539780856,
    739091230426741,739416021158832,739734934003557,740047990808965,740355213246849,
    740656622814823,740952240838376,741242088472889,741526186705628,741804556357696,
    742077218085963,742344192384970,742605499588793,742861159872888,743111193255908,
    743355619601487,743594458620003,743827729870312,744055452761460,744277646554363,
    744494330363470,744705523158398,744911243765540,745111510869656,745306343015440,
    745495758609057,745679775919667,745858413080922,746031688092446,746199618821285,
    746362223003350,746519518244826,746671522023570,746818251690486,746959724470882,
    747095957465805,747226967653362,747352771890023,747473386911896,747588829335998,
    747699115661503,747804262270968,747904285431548,747999201296197,748089025904844,
    748173775185558,748253464955704,748328110923067,748397728686978,748462333739414,
    748521941466090,748576567147528,748626225960126,748670932977195,748710703169999,
    748745551408770,748775492463714,748800541006007,748820711608770,748836018748041,
    748846476803726,748852100060541,748852902708946,748848898846062,748840102476574,
    748826527513631,748808187779728,748785097007577,748757268840973,748724716835638,
    748687454460070,748645495096362,748598852041033,748547538505828,748491567618520,
    748430952423702,748365705883563,748295840878659,748221370208676,748142306593177,
    748058662672348,747970451007728,747877684082936,747780374304385,747678534001990,
    747572175429866,747461310767016,747345952118018,747226111513692,747101800911772,
    746973032197561,746839817184581,746702167615215,746560095161345,746413611424974,
    746262727938854,746107456167091,745947807505757,745783793283485,745615424762061,
    745442713137014,745265669538187,745084305030316,744898630613590,744708657224213,
    744514395734953,744315856955694,744113051633969,743905990455501,743694684044725,
    743479142965314,743259377720695,743035398754554,742807216451351,742574841136809],
   [742338283078414,742097552485902,741852659511740,741603614251604,741350426744854,
    741093106975000,740831664870160,740566110303523,740296453093800,740022703005666,
    739744869750211,739462962985368,739176992316356,738886967296100,738592897425659,
    738294792154644,737992660881636,737686512954589,737376357671244,737062204279527,
    736744061977948,736421939915990,736095847194506,735765792866097,735431785935500,
    735093835359957,734751950049598,734406138867800,734056410631563,733702774111865,
    733345238034022,732983811078044,732618501878985,732249319027289,731876271069137,
    731499366506783,731118613798896,730734021360890,730345597565255,729953350741883,
    729557289178394,729157421120454,728753754772095,728346298296025,727935059813941,
    727520047406838,727101269115312,726678732939862,726252446841190,725822418740495,
    725388656519769,724951168022083,724509961051877,724065043375245,723616422720215,
    723164106777029,722708103198418,722248419599880,721785063559943,721318042620443,
    720847364286783,720373036028199,719895065278019,719413459433926,718928225858208,
    718439371878015,717946904785609,717450831838615,716951160260263,716447897239636,
    715941049931911,715430625458596,714916630907772,714399073334325,713877959760177,
    713353297174521,712825092534050,712293352763179,711758084754273,711219295367868,
    710676991432892,710131179746884,709581867076210,709029060156276,708472765691742,
    707912990356733,707349740795046,706783023620358,706212845416431,705639212737316,
    705062132107549,704481610022359,703897652947859,703310267321244,702719459550987,
    702125236017028,701527603070968,700926567036257,700322134208380,699714310855045,
    699103103216366,698488517505045,697870559906556,697249236579319,696624553654884,
    695996517238101,695365133407303,694730408214468,694092347685403,693450957819904,
    692806244591932,692158213949777,691506871816222,690852224088713,690194276639520,
    689533035315894,688868505940234,688200694310244,687529606199088,686855247355550,
    686177623504186,685496740345481,684812603555998,684125218788531,683434591672255,
    682740727812875,682043632792771,681343312171149,680639771484179,679933016245146,
    679223051944588,678509884050439,677793518008170,677073959240925,676351213149664,
    675625285113294,674896180488812,674163904611431,673428462794721,672689860330738,
    671948102490155,671203194522394,670455141655754,669703949097540,668949622034191,
    668192165631405,667431585034262,666667885367353,665901071734900,665131149220880,
    664358122889145,663581997783541,662802778928031,662020471326810,661235079964425,
    660446609805889,659655065796800,658860452863451,658062775912950,657262039833327],
   [656458249493649,655651409744132,654841525416250,654028601322842,653212642258228,
    652393652998308,651571638300675,650746602904720,649918551531734,649087488885017,
    648253419649979,647416348494246,646576280067756,645733219002867,644887169914456,
    644038137400014,643186126039752,642331140396696,641473185016783,640612264428961,
    639748383145284,638881545661008,638011756454682,637139019988248,636263340707131,
    635384723040331,634503171400516,633618690184113,632731283771399,631840956526591,
    630947712797935,630051556917792,629152493202732,628250525953615,627345659455682,
    626437897978637,625527245776737,624613707088874,623697286138658,622777987134505,
    621855814269715,620930771722556,620002863656349,619072094219542,618138467545800,
    617201987754076,616262658948697,615320485219437,614375470641601,613427619276101,
    612476935169529,611523422354241,610567084848425,609607926656185,608645951767607,
    607681164158843,606713567792177,605743166616102,604769964565393,603793965561178,
    602815173511013,601833592308949,600849225835606,599862077958242,598872152530824,
    597879453394097,596883984375653,595885749289999,594884751938625,593880996110072,
    592874485580000,591865224111252,590853215453923,589838463345425,588820971510549,
    587800743661535,586777783498134,585752094707671,584723680965108,583692545933111,
    582658693262108,581622126590354,580582849543993,579540865737117,578496178771829,
    577448792238303,576398709714844,575345934767948,574290470952361,573232321811139,
    572171490875704,571107981665906,570041797690077,568972942445092,567901419416422,
    566827232078194,565750383893246,564670878313184,563588718778434,562503908718302,
    561416451551026,560326350683829,559233609512979,558138231423835,557040219790906,
    555939577977902,554836309337788,553730417212833,552621904934667,551510775824328,
    550397033192316,549280680338644,548161720552887,547040157114235,545915993291541,
    544789232343370,543659877518051,542527932053725,541393399178392,540256282109964,
    539116584056306,537974308215292,536829457774845,535682035912992,534532045797904,
    533379490587945,532224373431722,531066697468123,529906465826373,528743681626072,
    527578347977240,526410467980369,525240044726459,524067081297069,522891580764357,
    521713546191127,520532980630868,519349887127803,518164268716929,516976128424057,
    515785469265861,514592294249915,513396606374736,512198408629827,510997703995719,
    509794495444009,508588785937404,507380578429761,506169875866126,504956681182776,
    503740997307258,502522827158429,501302173646496,500079039673053,498853428131125,
    497625341905201,496394783871274,495161756896884,493926263841149,492688307554808],
   [491447890880255,490205016651582,488959687694609,487711906826926,486461676857926,
    485209000588848,483953880812804,482696320314824,481436321871885,480173888252951,
    478909022219008,477641726523096,476372003910347,475099857118021,473825288875536,
    472548301904506,471268898918776,469987082624453,468702855719940,467416220895974,
    466127180835653,464835738214475,463541895700368,462245655953722,460947021627423,
    459645995366889,458342579810095,457036777587611,455728591322630,454418023631004,
    453105077121272,451789754394691,450472058045270,449151990659802,447829554817888,
    446504753091976,445177588047385,443848062242340,442516178227999,441181938548485,
    439845345740914,438506402335426,437165110855214,435821473816553,434475493728829,
    433127173094571,431776514409475,430423520162435,429068192835571,427710534904259,
    426350548837157,424988237096236,423623602136801,422256646407529,420887372350488,
    419515782401167,418141878988505,416765664534917,415387141456319,414006312162158,
    412623179055438,411237744532743,409850010984267,408459980793842,407067656338957,
    405673039990792,404276134114237,402876941067923,401475463204244,400071702869384,
    398665662403341,397257344139955,395846750406929,394433883525856,393018745812243,
    391601339575538,390181667119150,388759730740477,387335532730928,385909075375949,
    384480360955044,383049391741803,381616170003922,380180698003226,378742977995697,
    377303012231493,375860802954973,374416352404719,372969662813560,371520736408594,
    370069575411211,368616182037117,367160558496352,365702706993318,364242629726796,
    362780328889973,361315806670460,359849065250315,358380106806066,356908933508731,
    355435547523842,353959951011461,352482146126209,351002135017279,349519919828464,
    348035502698174,346548885759458,345060071140025,343569060962262,342075857343261,
    340580462394831,339082878223525,337583106930657,336081150612322,334577011359419,
    333070691257666,331562192387624,330051516824715,328538666639242,327023643896407,
    325506450656335,323987088974085,322465560899679,320941868478113,319416013749381,
    317887998748492,316357825505488,314825496045464,313291012388587,311754376550114,
    310215590540411,308674656364967,307131576024421,305586351514572,304038984826400,
    302489477946086,300937832855027,299384051529854,297828135942451,296270088059975,
    294709909844866,293147603254872,291583170243063,290016612757849,288447932742998,
    286877132137649,285304212876335,283729176888996,282152026100998,280572762433147,
    278991387801708,277407904118422,275822313290521,274234617220745,272644817807357,
    271052916944163,269458916520525,267862818421377,266264624527243,264664336714253],
   [263061956854156,261457486814339,259850928457841,258242283643369,256631554225315,
    255018742053768,253403848974535,251786876829150,250167827454893,248546702684807,
    246923504347707,245298234268203,243670894266707,242041486159455,240410011758516,
    238776472871811,237140871303126,235503208852126,233863487314372,232221708481331,
    230577874140398,228931986074901,227284046064123,225634055883311,223982017303696,
    222327932092500,220671802012954,219013628824315,217353414281872,215691160136968,
    214026868137007,212360540025473,210692177541942,209021782422092,207349356397723,
    205674901196764,203998418543293,202319910157544,200639377755923,198956823051024,
    197272247751637,195585653562764,193897042185632,192206415317705,190513774652698,
    188819121880589,187122458687633,185423786756372,183723107765652,182020423390630,
    180315735302792,178609045169964,176900354656320,175189665422402,173476979125127,
    171762297417799,170045621950124,168326954368223,166606296314640,164883649428355,
    163159015344801,161432395695869,159703792109925,157973206211817,156240639622894,
    154506093961010,152769570840540,151031071872392,149290598664016,147548152819416,
    145803735939165,144057349620411,142308995456893,140558675038951,138806389953533,
    137052141784214,135295932111201,133537762511347,131777634558161,130015549821819,
    128251509869177,126485516263777,124717570565864,122947674332393,121175829117041,
    119402036470216,117626297939072,115848615067513,114068989396210,112287422462610,
    110503915800942,108718470942233,106931089414317,105141772741842,103350522446286,
    101557340045963,99762227056033,97965184988517,96166215352300,94365319653148,92562499393714,
    90757756073548,88951091189109,87142506233774,85332002697848,83519582068572,81705245830135,
    79888995463685,78070832447336,76250758256176,74428774362282,72604882234727,70779083339587,
    68951379139956,67121771095948,65290260664716,63456849300451,61621538454400,59784329574871,
    57945224107241,56104223493970,54261329174607,52416542585798,50569865161297,48721298331978,
    46870843525836,45018502168004,43164275680758,41308165483527,39450172992902,37590299622642,
    35728546783688,33864915884169,31999408329408,30132025521937,28262768861500,26391639745064,
    24518639566829,22643769718231,20767031587960,18888426561959,17007956023436,15125621352877,
    13241423928045,11355365123997,9467446313087,7577668864978,5686034146648,3792543522396,
    1897198353856]]
private def rkmPhb_w64_m2_p7a : List ℕ := uNatCatN
  [
   [726502369153863,726134761842795,725764320085323,725391046190731,725014942439854,
    724636011085088,724254254350410,723869674431385,723482273495181,723092053680575,
    722699017097962,722303165829361,721904501928417,721503027420405,721098744302230,
    720691654542427,720281760081155,719869062830196,719453564672947,719035267464410,
    718614173031187,718190283171462,717763599654996,717334124223104,716901858588641,
    716466804435987,716028963421020,715588337171100,715144927285042,714698735333089,
    714249762856890,713798011369463,713343482355170,712886177269681,712426097539942,
    711963244564135,711497619711641,711029224322999,710558059709866,710084127154972,
    709607427912070,709127963205895,708645734232108,708160742157250,707672988118682,
    707182473224535,706689198553649,706193165155514,705694374050211,705192826228344,
    704688522650979,704181464249572,703671651925905,703159086552007,702643768970088,
    702125699992456,701604880401446,701081310949333,700554992358256,700025925320130,
    699494110496558,698959548518749,698422239987419,697882185472704,697339385514061,
    696793840620172,696245551268845,695694517906907,695140740950107,694584220783003,
    694024957758856,693462952199515,692898204395309,692330714604923,691760483055286,
    691187509941444,690611795426440,690033339641187,689452142684337,688868204622151,
    688281525488366,687692105284055,687099943977491,686505041504002,685907397765830,
    685307012631979,684703885938067,684098017486175,683489407044686,682878054348131,
    682263959097024,681647120957699,681027539562145,680405214507829,679780145357528,
    679152331639150,678521772845555,677888468434374,677252417827817,676613620412492,
    675972075539205,675327782522771,674680740641808,674030949138542,673378407218594,
    672723114050777,672065068766879,671404270461449,670740718191575,670074410976663,
    669405347798210,668733527599570,668058949285721,667381611723031,666701513739006,
    666018654122054,665333031621228,664644644945977,663953492765881,663259573710397,
    662562886368585,661863429288843,661161200978627,660456199904177,659748424490227,
    659037873119722,658324544133523,657608435830109,656889546465276,656167874251831,
    655443417359277,654716173913500,653986141996446,653253319645796,652517704854632,
    651779295571101,651038089698076,650294085092806,649547279566563,648797670884285,
    648045256764213,647290034877521,646532002847941,645771158251383,645007498615546,
    644241021419528,643471724093426,642699604017932,641924658523920,641146884892032,
    640366280352248,639582842083462,638796567213041,638007452816381,637215495916459,
    636420693483371,635623042433869,634822539630891,634019181883077,633212965944286],
   [632403888513098,631591946232314,630777135688447,629959453411200,629138895872942,
    628315459488176,627489140612990,626659935544514,625827840520353,624992851718020,
    624154965254363,623314177184970,622470483503581,621623880141477,620774362966870,
    619921927784270,619066570333862,618208286290850,617347071264810,616482920799020,
    615615830369785,614745795385752,613872811187210,612996873045380,612117976161699,
    611236115667083,610351286621184,609463484011636,608572702753286,607678937687413,
    606782183580932,605882435125593,604979686937157,604073933554564,603165169439086,
    602253388973470,601338586461057,600420756124895,599499892106840,598575988466628,
    597649039180947,596719038142484,595785979158961,594849855952152,593910662156882,
    592968391320016,592023036899422,591074592262923,590123050687227,589168405356844,
    588210649362977,587249775702401,586285777276316,585318646889190,584348377247571,
    583374960958883,582398390530206,581418658367025,580435756771964,579449677943497,
    578460413974635,577467956851587,576472298452405,575473430545595,574471344788714,
    573466032726930,572457485791568,571445695298621,570430652447238,569412348318185,
    568390773872274,567365919948769,566337777263761,565306336408507,564271587847749,
    563233521917993,562192128825763,561147398645813,560099321319318,559047886652020,
    557993084312347,556934903829488,555873334591443,554808365843026,553739986683831,
    552668186066167,551592952792940,550514275515511,549432142731493,548346542782523,
    547257463851977,546164893962650,545068820974381,543969232581643,542866116311071,
    541759459518952,540649249388659,539535472928037,538418116966732,537297168153469,
    536172612953274,535044437644639,533912628316630,532777170865933,531638050993840,
    530495254203172,529348765795144,528198570866151,527044654304498,525887000787058,
    524725594775857,523560420514587,522391462025044,521218703103494,520042127316952,
    518861717999385,517677458247837,516489330918460,515297318622462,514101403721967,
    512901568325781,511697794285066,510490063188909,509278356359806,508062654849029,
    506842939431894,505619190602927,504391388570905,503159513253797,501923544273576,
    500683460950920,499439242299784,498190867021841,496938313500802,495681559796588,
    494420583639374,493155362423484,491885873201141,490612092676063,489333997196907,
    488051562750550,486764764955203,485473579053358,484177979904556,482877941977978,
    481573439344846,480264445670632,478950934207073,477632877783978,476310248800823,
    474983019218136,473651160548647,472314643848217,470973439706524,469627518237500,
    468276849069520,466921401335326,465561143661674,464196044158710,462826070409056],
   [461451189456587,460071367794911,458686571355526,457296765495641,455901914985664,
    454501983996335,453096936085487,451686734184438,450271340583987,448850716920006,
    447424824158611,445993622580904,444557071767258,443115130581140,441667757152453,
    440214908860371,438756542315661,437292613342465,435823076959518,434347887360797,
    432866997895559,431380361047757,429887928414816,428389650685720,426885477618413,
    425375358016469,423859239705002,422337069505798,420808793211621,419274355559679,
    417733700204196,416186769688069,414633505413564,413073847612015,411507735312480,
    409935106309317,408355897128622,406770042993499,405177477788091,403578134020333,
    401971942783364,400358833715540,398738734958987,397111573116630,395477273207622,
    393835758621104,392186951068229,390530770532346,388867135217285,387195961493633,
    385517163842914,383830654799572,382136344890648,380434142573045,378723954168246,
    377005683794384,375279233295501,373544502167882,371801387483291,370049783808964,
    368289583124188,366520674733274,364742945174756,362956278126586,361160554307133,
    359355651371734,357541443804577,355717802805629,353884596172349,352041688175877,
    350188939431393,348326206762293,346453343057831,344570197123831,342676613526059,
    340772432425803,338857489407186,336931615295700,334994635967412,333046372148238,
    331086639202663,329115246911214,327131999235937,325136694073099,323129122992237,
    321109070960631,319076316052195,317030629139692,314971773569091,312899504814797,
    310813570114339,308713708081033,306599648292949,304471110856402,302327805942009,
    300169433291179,297995681690693,295806228412829,293600738618227,291378864718413,
    289140245694621,286884506369176,284611256625358,282320090571214,280010585642329,
    277682301638012,275334779684776,272967541120285,270580086290195,268171893249429,
    265742416358454,263291084763999,260817300752381,258320437962133,255799839440973,
    253254815530230,250684641557618,248088555316734,245465754308667,242815392717722,
    240136578089251,237428367672939,234689764389461,231919712371979,229117092026442,
    226280714545649,223409315801435,220501549526607,217555979683049,214571071894068,
    211545183796850,208476554143929,205363290449569,202203354936410,198994548487585,
    195734492247132,192420606433374,189050085831419,185619871305676,182126616512928,
    178566648789340,174935922914693,171229966101675,167443812085146,163571921549954,
    159608085269044,155545305126766,151375646525401,147090053285455,142678112690199,
    138127753211274,133424849727646,128552699092793,123491309876607,118216418860044,
    112698093654932,106898686340767,100769726714550,94246994678557,87242268099132],
   [79628509240106,71210701993145,61660496081362,50337533014494,35588271769886]]
private theorem rkmStatOk_t00 : bAllT [
  muxIntListEq (uHb rkmPhb_w64_m2_s0) (altBuildHbFrom 16 1024 969474000000 0 16),
  muxIntListEq (uHb rkmPhb_w64_m2_s1) (altBuildHbFrom 32 1024 655057833333 0 32),
  muxIntListEq (uHb rkmPhb_w64_m2_s2) (altBuildHbFrom 64 1024 360818923076 0 64),
  muxIntListEq (uHb rkmPhb_w64_m2_s3) (altBuildHbFrom 128 1024 181682400000 0 128),
  muxIntListEq (uHb rkmPhb_w64_m2_s4) (altBuildHbFrom 256 1024 95881890909 1 255),
  muxIntListEq (uHb rkmPhb_w64_m2_s5) (altBuildHbFrom 512 1024 51685843478 71 441),
  muxIntListEq (uHb rkmPhb_w64_m2_s6) (altBuildHbFrom 1024 1024 29643724279 234 790),
  muxIntListEq (uHb rkmPhb_w64_m2_p7a) (altBuildHbFrom 1792 1024 20052279735 539 485),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_m2_s0_in)) (Nat.add 16 1),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_m2_s1_in)) (Nat.add 32 1),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_m2_s2_in)) (Nat.add 64 1),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_m2_s3_in)) (Nat.add 128 1),
  Nat.ble (Nat.add 17 (altIntLen rkmXsWin_w64_m2_s4_in)) (Nat.add 256 1),
  Nat.ble (Nat.add 87 (altIntLen rkmXsWin_w64_m2_s5_in)) (Nat.add 512 1),
  Nat.ble (Nat.add 250 (altIntLen rkmXsWin_w64_m2_s6_in)) (Nat.add 1024 1)
  ] = true := by decide +kernel
private theorem rkmSmOk_t00 : bAllT [
  bWinChk 0 3 100000000 16 rkmPhb_w64_m2_s0
    0 rkmXsWin_w64_m2_s0_in 0 rkmXsWin_w64_m2_s0_out 154322574,
  bWinChk 0 6 100000000 32 rkmPhb_w64_m2_s1
    0 rkmXsWin_w64_m2_s1_in 0 rkmXsWin_w64_m2_s1_out 447062660,
  bWinChk 0 13 100000000 64 rkmPhb_w64_m2_s2
    0 rkmXsWin_w64_m2_s2_in 0 rkmXsWin_w64_m2_s2_out 676656641,
  bWinChk 0 25 100000000 128 rkmPhb_w64_m2_s3
    0 rkmXsWin_w64_m2_s3_in 17 rkmXsWin_w64_m2_s3_out 2962659292
  ] = true := by decide +kernel
private theorem rkmHhb_w64_m2_s0 :
    uHb rkmPhb_w64_m2_s0 = rkmDropInts 0 rkmHbWin_w64_m2_s0 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd rkmStatOk_t00)).trans
    (drHb 16 1024 969474000000 0 16)
private theorem rkmHhb_w64_m2_s1 :
    uHb rkmPhb_w64_m2_s1 = rkmDropInts 0 rkmHbWin_w64_m2_s1 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl rkmStatOk_t00))).trans
    (drHb 32 1024 655057833333 0 32)
private theorem rkmHhb_w64_m2_s2 :
    uHb rkmPhb_w64_m2_s2 = rkmDropInts 0 rkmHbWin_w64_m2_s2 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl rkmStatOk_t00)))).trans
    (drHb 64 1024 360818923076 0 64)
private theorem rkmHhb_w64_m2_s3 :
    uHb rkmPhb_w64_m2_s3 = rkmDropInts 0 rkmHbWin_w64_m2_s3 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl rkmStatOk_t00))))).trans
    (drHb 128 1024 181682400000 0 128)
private theorem rkmHhb_w64_m2_s4 :
    uHb rkmPhb_w64_m2_s4 = rkmDropInts 1 rkmHbWin_w64_m2_s4 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bTl4 rkmStatOk_t00))).trans
    (drHb 256 1024 95881890909 1 256)
private theorem rkmHhb_w64_m2_s5 :
    uHb rkmPhb_w64_m2_s5 = rkmDropInts 71 rkmHbWin_w64_m2_s5 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bTl4 rkmStatOk_t00)))).trans
    (drHb 512 1024 51685843478 71 512)
private theorem rkmHhb_w64_m2_s6 :
    uHb rkmPhb_w64_m2_s6 = rkmDropInts 234 rkmHbWin_w64_m2_s6 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl (bTl4 rkmStatOk_t00))))).trans
    (drHb 1024 1024 29643724279 234 1024)
private theorem rkmHhb_w64_m2_p7a :
    uHb rkmPhb_w64_m2_p7a = rkmDropInts 539 rkmHbWin_w64_m2_p7a :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bTl4 rkmStatOk_t00)))))).trans
    (drHb 1792 1024 20052279735 539 1024)
private theorem rkmWinIter_w64_m2_s0 :
    RkmWinIterSound 3 16 rkmHbWin_w64_m2_s0 0 rkmXsWin_w64_m2_s0_in
      0 rkmXsWin_w64_m2_s0_out 154322574 :=
  bWinChk_sound rkmHhb_w64_m2_s0
    (bAllT_hd rkmSmOk_t00)
/-- Certified `w64_m2` seg `0` (`3` steps). -/
theorem rkmWinSegWalkSnd_w64_m2_s0 :
    RkmWinSegWalkSound 3 ⟨16, rkmHbWin_w64_m2_s0, 0, rkmXsWin_w64_m2_s0_in,
      0, rkmXsWin_w64_m2_s0_out, 154322574⟩ :=
  @rkmSegWalk_mk 3 16 0 0 154322574
    rkmHbWin_w64_m2_s0 rkmXsWin_w64_m2_s0_in rkmXsWin_w64_m2_s0_out
    (rkmw_buildHbFrom_length 16 1024 969474000000 16 0)
    (bAllT_hd (bTl4 (bTl4 rkmStatOk_t00)))
    rkmWinIter_w64_m2_s0
private theorem rkmWinIter_w64_m2_s1 :
    RkmWinIterSound 6 32 rkmHbWin_w64_m2_s1 0 rkmXsWin_w64_m2_s1_in
      0 rkmXsWin_w64_m2_s1_out 447062660 :=
  bWinChk_sound rkmHhb_w64_m2_s1
    (bAllT_hd (bAllT_tl rkmSmOk_t00))
/-- Certified `w64_m2` seg `1` (`6` steps). -/
theorem rkmWinSegWalkSnd_w64_m2_s1 :
    RkmWinSegWalkSound 6 ⟨32, rkmHbWin_w64_m2_s1, 0, rkmXsWin_w64_m2_s1_in,
      0, rkmXsWin_w64_m2_s1_out, 447062660⟩ :=
  @rkmSegWalk_mk 6 32 0 0 447062660
    rkmHbWin_w64_m2_s1 rkmXsWin_w64_m2_s1_in rkmXsWin_w64_m2_s1_out
    (rkmw_buildHbFrom_length 32 1024 655057833333 32 0)
    (bAllT_hd (bAllT_tl (bTl4 (bTl4 rkmStatOk_t00))))
    rkmWinIter_w64_m2_s1
private theorem rkmWinIter_w64_m2_s2 :
    RkmWinIterSound 13 64 rkmHbWin_w64_m2_s2 0 rkmXsWin_w64_m2_s2_in
      0 rkmXsWin_w64_m2_s2_out 676656641 :=
  bWinChk_sound rkmHhb_w64_m2_s2
    (bAllT_hd (bAllT_tl (bAllT_tl rkmSmOk_t00)))
/-- Certified `w64_m2` seg `2` (`13` steps). -/
theorem rkmWinSegWalkSnd_w64_m2_s2 :
    RkmWinSegWalkSound 13 ⟨64, rkmHbWin_w64_m2_s2, 0, rkmXsWin_w64_m2_s2_in,
      0, rkmXsWin_w64_m2_s2_out, 676656641⟩ :=
  @rkmSegWalk_mk 13 64 0 0 676656641
    rkmHbWin_w64_m2_s2 rkmXsWin_w64_m2_s2_in rkmXsWin_w64_m2_s2_out
    (rkmw_buildHbFrom_length 64 1024 360818923076 64 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bTl4 (bTl4 rkmStatOk_t00)))))
    rkmWinIter_w64_m2_s2
private theorem rkmWinIter_w64_m2_s3 :
    RkmWinIterSound 25 128 rkmHbWin_w64_m2_s3 0 rkmXsWin_w64_m2_s3_in
      17 rkmXsWin_w64_m2_s3_out 2962659292 :=
  bWinChk_sound rkmHhb_w64_m2_s3
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl rkmSmOk_t00))))
/-- Certified `w64_m2` seg `3` (`25` steps). -/
theorem rkmWinSegWalkSnd_w64_m2_s3 :
    RkmWinSegWalkSound 25 ⟨128, rkmHbWin_w64_m2_s3, 0, rkmXsWin_w64_m2_s3_in,
      17, rkmXsWin_w64_m2_s3_out, 2962659292⟩ :=
  @rkmSegWalk_mk 25 128 0 17 2962659292
    rkmHbWin_w64_m2_s3 rkmXsWin_w64_m2_s3_in rkmXsWin_w64_m2_s3_out
    (rkmw_buildHbFrom_length 128 1024 181682400000 128 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bTl4 (bTl4 rkmStatOk_t00))))))
    rkmWinIter_w64_m2_s3
private def rkmC_w64_m2_s4_1 : List ℤ := pzigCat
  [
   [247013632,875095966,1738110030,3522327350,7067451122,13407495996,25259749360,46179763538,
    83227932878,146852753938,253640014328,429415408030,712460517826,1159040210416,1848592493708,
    2891252604880,4435090051656,6673614644066,9852019623880,14270887709796,20286670111800,
    28304616633796,38766176740354,52126110775952,68820502647844,89227565196738,113618998438452,
    142110724266922,174613853550520,210793178979318,250040700701462,291466613104538,
    333917341952818,376016813021390,416235557228504,452980358828884,484698107417030,
    509985420932328,527691782850112,537007115320760,537522672816932,529260892555172,
    512669216404328,488580931763390,458146661574738,422743303962856,383873810483356,
    343063049585010,301763344832660,261275771145696,222691387399916,186857769303678,
    154366218674066,125561619237462,100566809032122,79318108438612,61608305695192,47128133047554,
    35507886870464,26350998669536,19262871028200,13871410966724,9840563853674,6877703719452,
    4735981187660,3213346565648,2148140179700,1415116372592,918698194030,587641616974,
    370425259216,229924732648,140680697638,84701824990,50078034706,29072935226,16331327534,
    8960487692,4549759196,2051575576,716741056]]
private theorem rkmWC_w64_m2_s4_0 : bWinChk 1 29 100000000 256 rkmPhb_w64_m2_s4
    17 rkmXsWin_w64_m2_s4_in 49 rkmC_w64_m2_s4_1 4648446538 = true := by decide +kernel
private theorem rkmWC_w64_m2_s4_1 : bWinChk 1 26 100000000 256 rkmPhb_w64_m2_s4
    49 rkmC_w64_m2_s4_1 87 rkmXsWin_w64_m2_s4_out 4562036805 = true := by decide +kernel
private theorem rkmWinIter_w64_m2_s4 :
    RkmWinIterSound 55 256 rkmHbWin_w64_m2_s4 17 rkmXsWin_w64_m2_s4_in
      87 rkmXsWin_w64_m2_s4_out 9210483343 :=
  rkmChS 55 9210483343 (bWinChk_sound rkmHhb_w64_m2_s4 rkmWC_w64_m2_s4_0) rkmHhb_w64_m2_s4
    rkmWC_w64_m2_s4_1 rfl rfl
/-- Certified `w64_m2` seg `4` (`55` steps). -/
theorem rkmWinSegWalkSnd_w64_m2_s4 :
    RkmWinSegWalkSound 55 ⟨256, rkmHbWin_w64_m2_s4, 17, rkmXsWin_w64_m2_s4_in,
      87, rkmXsWin_w64_m2_s4_out, 9210483343⟩ :=
  @rkmSegWalk_mk 55 256 17 87 9210483343
    rkmHbWin_w64_m2_s4 rkmXsWin_w64_m2_s4_in rkmXsWin_w64_m2_s4_out
    (rkmw_buildHbFrom_length 256 1024 95881890909 256 0)
    (bAllT_hd (bTl4 (bTl4 (bTl4 rkmStatOk_t00))))
    rkmWinIter_w64_m2_s4
private def rkmC_w64_m2_s5_1 : List ℤ := pzigCat
  [
   [332590038,1026081364,2599429502,5731488696,12421188082,25322832332,49694602864,93935760542,
    171533320032,304109711712,523559261692,877214929806,1432001615580,2280524235416,3547194579018,
    5392992126418,8021144274260,11679018844834,16658211402282,23289717558284,31933035434228,
    42960928299298,56735942080532,73582816482972,93755411389550,117401263307108,144528141746086,
    174972799373510,208379650588030,244189214659316,281641447104504,319795625347140,
    357564643507902,393766198849518,427183371344772,456633787500056,481040218006916,
    499495757034758,511321119637616,516104578588982,513725819181674,504358738990664,
    488454198523892,466706603819452,440003805789262,409370068477720,375902599614028,
    340709550744056,304854049131182,269305001585102,234902245362742,202331280958880,
    172113073818160,144603872223710,120005124071682,98380980112170,79680118438376,63760496618416,
    50413739886920,39389112284070,30413247979432,23208083774236,17504109488234,13049267170712,
    9616413215714,7005525813084,5045419542404,3592591047442,2529126712548,1760650582464,
    1211912080376,824919248978,555172283544,369304667788,242980068910,157873095844,101395965894,
    64169374152,39920764284,24444055432,14468228262,8367553966,4440675540,2072383522,740859428]]
private def rkmC_w64_m2_s5_2 : List ℤ := pzigCat
  [
   [219158995,448630853,986773793,1357759277,1410860685,134613783,4906980922,17648763610,
    46268270702,104010510754,212867051752,406837643580,736401039676,1274660425024,2122001784786,
    3413515215326,5323145279252,8067680747998,11908542288140,17147905701224,24122969825072,
    33191509824260,44714591938274,59031430499084,76430704577758,97119317028160,121189479287662,
    148589510950912,179099278957062,212315423248760,247647105277164,284325856915466,
    321428959837332,357916535633580,392680651370972,424601123388208,452607968170496,
    475741016681798,493205007292032,504415529810796,509029595616442,506963029727230,
    498388968546552,483721643650428,463585584724290,438773112081340,410196182807352,
    378832087506864,345672592335224,311675798288724,277725142687674,244598583592836,
    212945509044490,183276767022302,155961040584956,131231670253898,109198709673664,
    89865616694764,73148729541038,58897199006068,46913059281488,36968986174138,28824617574232,
    22238351801394,16977954893330,12827672293408,9591988448472,7099188748378,5200806986328,
    3771610694878,2707689852436,1924267526684,1354017309664,943215021220,650557732372,
    444192368684,300126347066,200832902266,132845644284,86957129658,56111979696,35593384606,
    22213821016,13371973668,7844748394,4200771790,1967771172,703000536]]
private def rkmC_w64_m2_s5_3 : List ℤ := pzigCat
  [
   [259069930,402306110,392668698,242428903,1836649833,4946254979,10349187505,17659101015,
    26054158693,31553013479,25413810269,8562254988,98980280240,290959063604,653513088404,
    1285365628884,2322153934100,3942600870148,6372030654900,9884712659472,14799170285486,
    21470890526286,30277545775162,41597797960838,55785884434022,73139571280300,93868224135986,
    118058711462890,145646230614552,176391980783732,209868640965242,245460915378276,
    282376662350664,319674975619198,356304962387860,391156173518088,423116289502088,
    451130892647638,474262627535568,491743105978248,503015157722732,507760625844190,
    505913744407294,497657879864414,483407787613796,463778969354130,439545412510510,
    411593318376182,380870068458872,348335325386084,314916582667880,281469971956812,
    248751605865838,217396400681598,187907796808614,160655013020194,135877783088422,
    113698474823782,94136117820414,77125221974814,62533932999102,50182537404316,39860897977822,
    31342337393146,24397383507080,18802476979700,14347627204122,10841131125576,8111740321858,
    6010910358370,4411297004344,3206503229672,2308709765940,1646457445616,1163198193836,
    813912713784,564207159664,387425251042,263415144490,177420695664,118097460988,77774342320,
    50480999226,32210054680,20190491642,12163238698,7087149346,3735863160,1709790666,595191584]]
private def rkmC_w64_m2_s5_4 : List ℤ := pzigCat
  [
   [241935176,866311282,1998594160,3486760446,4624184500,4757949700,1853789430,6300231641,
    22709743307,50021327619,88907352555,136050128897,179070099473,192486483303,129867671981,
    83823382180,560716790198,1459312438760,2990209136688,5421124499876,9075464190364,
    14326651515812,21585296958658,31277570930516,43818635554228,59578117063656,78843948084118,
    101784073538870,128410933668884,158553824310632,191839292711708,227686931136200,
    265318227491216,303782099851102,341995210019562,378793252966116,412993081199338,
    443456592655022,469155340482258,489228074422282,503027474296464,510154288907928,
    510473023303040,504112710959342,491449691269450,473077027821026,449763345935768,
    422402799870758,391963751863770,359435964950862,325783487003926,291903844899106,
    258595266379050,226535021140922,196265456575160,168191189313112,142582937337468,
    119588013816652,99246097688330,81506188428204,66246747655448,53293880990764,42439355469716,
    33456428489240,26112239268694,20179111712650,15441325160474,11701041994530,8781241558784,
    6526768647116,4805007306078,3503912982800,2531127424578,1811326431768,1284085824896,
    901872905234,627511160274,432418547364,295288707758,199494249416,133437565710,88304921468,
    57526199408,36934139664,23148199364,14205380788,8361691940,4542938784,2258028808,827485182,
    218539336]]
private theorem rkmWC_w64_m2_s5_0 : bWinChk 71 24 100000000 512 rkmPhb_w64_m2_s5
    87 rkmXsWin_w64_m2_s5_in 121 rkmC_w64_m2_s5_1 4658887267 = true := by decide +kernel
private theorem rkmWC_w64_m2_s5_1 : bWinChk 71 24 100000000 512 rkmPhb_w64_m2_s5
    121 rkmC_w64_m2_s5_1 155 rkmC_w64_m2_s5_2 4635097887 = true := by decide +kernel
private theorem rkmWC_w64_m2_s5_2 : bWinChk 71 23 100000000 512 rkmPhb_w64_m2_s5
    155 rkmC_w64_m2_s5_2 188 rkmC_w64_m2_s5_3 3945038216 = true := by decide +kernel
private theorem rkmWC_w64_m2_s5_3 : bWinChk 71 22 100000000 512 rkmPhb_w64_m2_s5
    188 rkmC_w64_m2_s5_3 220 rkmC_w64_m2_s5_4 4204119860 = true := by decide +kernel
private theorem rkmWC_w64_m2_s5_4 : bWinChk 71 22 100000000 512 rkmPhb_w64_m2_s5
    220 rkmC_w64_m2_s5_4 250 rkmXsWin_w64_m2_s5_out 4706483998 = true := by decide +kernel
private theorem rkmWinIter_w64_m2_s5 :
    RkmWinIterSound 115 512 rkmHbWin_w64_m2_s5 87 rkmXsWin_w64_m2_s5_in
      250 rkmXsWin_w64_m2_s5_out 22149627228 :=
  rkmChS 115 22149627228 (rkmChS 93 17443143230 (rkmChS 71 13239023370 (rkmChS 48 9293985154
    (bWinChk_sound rkmHhb_w64_m2_s5 rkmWC_w64_m2_s5_0) rkmHhb_w64_m2_s5 rkmWC_w64_m2_s5_1 rfl
    rfl) rkmHhb_w64_m2_s5 rkmWC_w64_m2_s5_2 rfl rfl) rkmHhb_w64_m2_s5 rkmWC_w64_m2_s5_3 rfl
    rfl) rkmHhb_w64_m2_s5 rkmWC_w64_m2_s5_4 rfl rfl
/-- Certified `w64_m2` seg `5` (`115` steps). -/
theorem rkmWinSegWalkSnd_w64_m2_s5 :
    RkmWinSegWalkSound 115 ⟨512, rkmHbWin_w64_m2_s5, 87, rkmXsWin_w64_m2_s5_in,
      250, rkmXsWin_w64_m2_s5_out, 22149627228⟩ :=
  @rkmSegWalk_mk 115 512 87 250 22149627228
    rkmHbWin_w64_m2_s5 rkmXsWin_w64_m2_s5_in rkmXsWin_w64_m2_s5_out
    (rkmw_buildHbFrom_length 512 1024 51685843478 512 0)
    (bAllT_hd (bAllT_tl (bTl4 (bTl4 (bTl4 rkmStatOk_t00)))))
    rkmWinIter_w64_m2_s5
private def rkmC_w64_m2_s6_1 : List ℤ := pzigCat
  [
   [431556720,672034302,381639048,322851619,1982105095,4370676603,6856331803,8551827383,
    7769169237,2451591787,9094247642,28138353702,53643319234,81427980984,102719471236,
    102875714760,63132918010,39123528945,225002151493,507372681093,881638978957,1312653755545,
    1721393601887,1971229511569,1854474526979,1085314996993,702608847562,3950848058736,
    9158959421090,16859792616784,27582459915838,41810971626104,59936187454210,82208281734904,
    108694557574174,139244917644310,173472135620178,210747605688444,250216030471940,
    290827770647234,331388270535790,370619474961418,407229750948438,439987423845946,
    467788884002612,489720622521846,505106428286208,513538720908974,514892627342132,
    509319915986376,497228942977066,479248324560900,456181387115682,428954114061330,
    398560214322634,366009823382692,332280349163784,298277661986310,264804994853652,
    232541397541052,202031173685972,173679919497742,147761337247058,124426808046330,
    103721352011076,85601098253624,69951991634184,56608445302116,45370138101130,36017430376892,
    28323695149872,22066186118382,17032610692174,13027096870634,9873485239336,7416000350414,
    5520690425958,4073462423328,2979297215394,2160052086544,1552304470300,1106035469532,
    781176765042,546980946476,379580685544,260904477568,177766948384,119778232186,79898337946,
    52533416424,33939679666,21570603752,13206238400,7879142544,4282455242,2032235130,733511420]]
private def rkmC_w64_m2_s6_2 : List ℤ := pzigCat
  [
   [244782721,318505033,317698179,103199018,830540438,1925540624,2987142730,3406877440,2513325106,
    343356597,5456495125,12743216909,20667061333,26829995025,27250865701,17180208057,7891052750,
    51201389968,111185951490,180740237926,244164602654,275897554890,241950559502,102039808450,
    182807685197,641424903455,1278440260599,2058389573305,2889386946517,3606248350151,
    3959517097493,3607694000411,2120223198853,1009774699112,6343072242254,14458871903446,
    25913279784986,41188770227092,60644932333366,84470398016664,112643083447586,144903524841630,
    180743117748240,219411719138504,259942886925882,301197375720380,341920088498492,
    380807708088820,416580509128858,448053415132574,474201216477608,494210840144186,
    507521280315306,513844431117514,513168901467744,505747751244300,492069545354880,
    472820157192762,448834467683012,421045188950558,390431113969990,357968116003130,
    324587728741030,291140820503240,258372680098184,226905938674012,197232451466738,
    169714076416742,144588005502422,121979618704232,101916322343618,84344873298926,69149321995562,
    56167046462806,45205576591956,36054857376540,28499773112116,22329018001842,17341427548058,
    13351672364540,10191723626594,7713680391420,5789079764282,4308360321054,3180035476502,
    2327788891404,1690109291752,1217046375360,869183124618,615782819088,432507736944,301361486954,
    208033941618,142275764244,96365899582,64402131360,42619970592,27603770252,17544760808,
    10738920994,6172847628,3134355290,1376264416,469166390]]
private def rkmC_w64_m2_s6_3 : List ℤ := pzigCat
  [
   [270392179,731834161,1328803993,1558604321,1372247413,245686201,1926389890,4730956782,
    7878210206,9785912948,9198434920,4404085392,5844895679,21311339411,40383367795,58313564767,
    68473428745,61768810345,28639670009,38123721816,141008663550,272453116936,412770512318,
    527052711442,565675456064,468069959624,169436461824,385375469391,1226961972201,2341113617299,
    3648514574091,4986248900903,6092169849767,6599777322769,6039565809281,3855338034309,
    569084579980,7870512409568,18657635394940,33457719089642,52661124077414,76471537588152,
    104864892946310,137563167793836,174025251978052,213457972807880,254846296342036,
    297000787853244,338620086907706,378360772842382,414913088322592,447072924014694,
    473806030931304,494301262629064,508005982593276,514646252107018,514227657242534,
    507019886378470,493527149074094,474446545015926,450621012266690,422986532839768,
    392521531588078,360199092941388,326944705365140,293603495744442,260914343476466,
    229495022601272,199834159977068,172291552632122,147105527312888,124403325322008,
    104216837973462,86498108121176,71136920734078,57977409094214,46832479981208,37498254611996,
    29764193509906,23422980493218,18276794960074,14141747356982,10851662643162,8258533931308,
    6234000970414,4667894993348,3467268780720,2555159424442,1867994889324,1354942233380,
    975013527792,696067506598,493092728006,346404611278,241455737910,166747881336,114068282600,
    77224811748,51531855608,33962984696,21836558456,13706505958,8248112796,4596979556,2368764748,
    904408912,249182494]]
private def rkmC_w64_m2_s6_4 : List ℤ := pzigCat
  [
   [256710556,595106200,747530276,517653544,372196977,1572166417,3056647125,4118835021,4230030255,
    2648639577,1196375802,6918266006,14021342302,20369445642,23251156100,19430649532,5727154660,
    19077673465,53861209425,92957378131,126568296699,140639285705,118428518101,44612070769,
    91143331290,287347417074,525887372438,767581314044,950629136470,993986365832,804056493584,
    289664340648,619505921377,1949500750721,3656878595003,5605871920419,7548458490013,
    9115123212839,9815268939673,9052306603835,6153397813037,411228381945,8861644817110,
    22274049353264,40294359229294,63194211281554,91003290323134,123478371936472,160093572687092,
    200049664509422,242306203561652,285632074350654,328670544028492,370015535923568,
    408289656143160,442221810043296,470715084317388,492901944164368,508183547889558,
    516249121571090,517078651218300,510926185507996,498289488320952,479868028072198,
    456512693341042,429173627030446,398846376675138,366523490676272,333151420413410,
    299595645608136,266615775949438,234848142130322,204798993687652,176843860155044,
    151234233007522,128109297315618,107509899702796,89396027673496,73663034022894,60158833767120,
    48699226088310,39081069990140,31094485568316,24531073458504,19191638777742,14890597528284,
    11459187504120,8747363397620,6623917280768,4976110940244,3709004855862,2742843510224,
    2012750059950,1465666341564,1058931149980,759344059664,540202336560,381293571622,266921147652,
    185256623516,127514328832,86717926792,58321530078,38628609676,25150436706,16061805034,
    9805338542,5735526982,2998738848,1347963306,458733104]]
private def rkmC_w64_m2_s6_5 : List ℤ := pzigCat
  [
   [216614353,263109481,59819584,668341176,1276920472,1956012838,2073742814,1417466908,399974741,
    3290635649,6507076475,9245738893,9865148435,7181772167,87061965,11524403560,25971603224,
    39990683838,48036397028,44148808312,22678318704,19529259607,80709448877,152801309915,
    219478275515,257941205467,241010004277,142731743263,54689090536,352715812274,728173556544,
    1127366968460,1464514325340,1625196280816,1478304647814,893819747478,231527342167,
    1944393096779,4204744700853,6856476567253,9607975646047,12021946472249,13521063977223,
    13411191806819,10918964655005,5246920604741,4362994667254,18559758614322,37814573436724,
    62362080226812,92154510427588,126837223927184,165745879391128,207928419477296,252189623715160,
    297154013770442,341344561630262,383266583043258,421493878232924,454748016331544,
    481965663784018,502349780551376,515401353579660,520930714941104,519049772093700,
    510145467055822,494841361275084,473947274269264,448404090005596,419228093779584,
    387455616147188,354096021882246,320090198865610,286279421687412,253384759722168,
    221993818558078,192558334410780,165397546122102,140708432607160,118579449339222,
    99006976249274,81913315964592,67164114972426,54584626567978,43975611695068,35124607040740,
    27817507649070,21846439875456,17015175026832,13144346119194,10072112839794,7656210841404,
    5773790429970,4320032196738,3207309954126,2362719083078,1727250647856,1253097332118,
    902098921250,644446168604,456791706654,321138287792,224043694342,154731150962,105912623430,
    71805760170,47962956034,31614598728,20324725712,12754478564,7618754684,4162126626,2062406662,
    749292450]]
private def rkmC_w64_m2_s6_6 : List ℤ := pzigCat
  [
   [229330623,652735543,967047885,1016263319,582317031,630536090,2224000048,3923363696,4994591628,
    4490579172,2064436830,2807660373,9329767039,16045732811,20557681333,19706981153,11306596041,
    6296048448,31522380632,59859827402,83585528990,92154045324,74852506098,23567019444,
    63916868177,179751321619,304534456175,406546224249,445284024989,377908586223,168269115491,
    200357756958,714386371560,1319041445204,1914090311570,2356758112760,2472295897188,
    2077422959386,1009349176514,836964997687,3469478126221,6763356662421,10433318575871,
    14020068275549,16895014181611,18284296338697,17314429360845,13073985884213,4689194465067,
    8595041644528,27336811263374,51827260109678,82041138104724,117607860570932,157810931140674,
    201614990276256,247717150508882,294620695197968,340723708169900,384413435448348,
    424161977953380,458611797377568,486648283229152,507452823646186,520532457405476,
    525729554155532,523207593633246,513420503354740,497066264487004,475030523707568,
    448326842462450,418035635021412,385246157396994,351007566696198,316286773416604,
    281938361131382,248684164308088,217102996054552,187630743483336,160565003230104,
    136078446159976,114234501893870,95005018023604,78289797227158,63934893859564,51749235942360,
    41520423324522,33026460212244,26047063217684,20370441440834,15798828708998,12153083421748,
    9272939270252,7018704318218,5270433495590,3926576540958,2902629256526,2129099332678,
    1549622545888,1119355197476,802157673978,570421325654,402503243560,281599733588,195380908018,
    134412317014,91422954600,61639302778,40838390170,26530021598,16896339402,10275469162,
    5934234774,3009109152,1288871512,413937890]]
private def rkmC_w64_m2_s6_7 : List ℤ := pzigCat
  [
   [485088499,1274183855,2260255705,2671140595,2204464901,512863655,2619734028,6148707496,
    9373089042,10393885032,7760131940,769590682,10393723649,23623992093,35103122483,39780324225,
    32287929283,9453109983,28863176832,77457953738,125143742170,156538956784,153058364126,
    98933981132,14232569809,181508931711,380115578535,568828933407,690578155759,680481792675,
    479329945711,48892175281,610034603870,1443417520684,2335277139288,3107933796816,3537090804678,
    3376256935102,2395171164916,426214869410,2586529728155,6541549157805,11145428302485,
    15895357279743,20083613856453,22828969421205,23129767618575,19940150386901,12259933538333,
    770422367612,19777901844070,45078885728750,76624169519332,113971205702282,156289890678806,
    202398543059490,250829501092926,299918188700894,347904160464780,393041517837090,
    433703279426822,468474073404272,496225490257446,516166945238482,527871374373938,
    531276494018448,526661356935364,514605654863498,495933012145988,471646900816898,
    442863063198712,410743238213908,376435523433192,341023724024312,305486582087778,
    270671036438734,237274310185300,205838478888216,176754184145740,150270091443074,
    126508704352802,105485983820158,87130316735454,71304243838260,57822753062658,46470746806352,
    37018483427888,29232865417100,22886807631354,17767099269954,13677422412518,10442313569118,
    7907533549190,5939659868630,4425882551718,3271913511490,2399632638158,1746287560606,
    1260849471036,903185940248,642023104580,452719824162,316602215536,219685705650,150879942560,
    102685392388,69098219198,45772985552,29866574916,19005516118,11539468314,6741590838,
    3450823326,1473998034,464941004]]
private def rkmC_w64_m2_s6_8 : List ℤ := pzigCat
  [
   [228765538,786927104,1302608052,1254452892,469796202,947960609,3240947991,5122949417,
    5834518197,4542897931,526407313,5823010418,13114662422,18755736054,19684196594,13732586630,
    799082785,22366834001,46414710729,65645460203,70589212621,52733508069,7774109077,62259424056,
    145753764854,222132288784,263717960480,241681685460,133638721102,67650862961,345809116531,
    656242670549,927819922627,1069382492441,986495248973,602038139413,119705361774,1149424976100,
    2376999364588,3606690465506,4566479852826,4937586627084,4397271726792,2675876244630,
    380078880441,4748494461009,10182945221809,16184297670955,22001181926803,26658894871177,
    29021889039021,27880953342101,22058895031253,10525679027435,7491874537384,32416977915132,
    64254324208642,102558600867612,146438697043602,194601050853740,245427143620030,
    297075832949816,347603161356486,395088311380700,437751740944534,474061050609382,
    502812036276008,523182749799968,534758642849482,537527360263140,531848297383462,
    518402548517836,498125584278236,472134320759868,441650608434406,407928432241890,
    372190299254876,335573619534138,299089902592654,263599024697272,229793789742512,
    198198186219264,169174117386568,142934854678810,119564657618150,99040524102426,81254139445824,
    66035192241456,53170534140104,42422441675010,33543803183546,26289141439584,20424080482516,
    15731262629014,12013986561592,9098097168898,6832995516590,5089611162342,3760228840546,
    2755835571106,2003466221672,1444861096264,1033888996928,733732082066,516560842228,
    360711986638,249712644300,171388635598,116428212884,78100523548,51719862220,33704325002,
    21255972242,13108387852,7660025360,4025786016,1858866546,614275700]]
private def rkmC_w64_m2_s6_9 : List ℤ := pzigCat
  [
   [235554127,777092253,840163891,302139943,761899516,2312938074,3287403424,3325564682,1770902332,
    1536732587,5791620599,9834079433,11741145579,9364812259,2181778203,9620796734,23274927678,
    34032727594,36618844362,26123151332,496818296,37334451819,79524087681,112475430695,
    120617617419,90138120059,13892170999,102624742330,238778690194,359815512782,420785890578,
    377388357062,197727126690,123631676743,554092877629,1019001594091,1405566401031,1577638113157,
    1402217655991,780855007047,315385907476,1816451842720,3537329557922,5178352614522,
    6350684140172,6623327588764,5589984593530,2948028983642,1420824327069,7381580235843,
    14498134423359,22019577341007,28904183187027,33882511624971,35556690128143,32525443363069,
    23521066954225,7546255974705,16008806879584,47279434353214,85879205445160,130901509303750,
    180964824033190,234300476529252,288872681076476,342518134920660,393091720972334,
    438607317472902,477358122555512,508010417602992,529665238871858,541882745232572,
    544674791360930,538466658079892,524035561438548,502433106602724,474900235305866,
    442779654621912,407435816423624,370184125146128,332232774134810,294642514722720,
    258299588302214,223903531530526,191968174358852,162832846287546,136679089384692,
    113554831669572,93399054227852,76066568974692,61353378097732,49017336347418,38796616709020,
    30425219181146,23644715816112,18211404779678,13903345912740,10522432053300,7895251652052,
    5873830839168,4333360991888,3170227833940,2300085566452,1655274104688,1181335837106,
    836262854626,587208265236,408722053750,282011207530,192848737888,130482435608,87245725314,
    57718196934,37368354112,23656694756,14526752218,8366140112,4414311124,2071732618,679243640]]
private def rkmC_w64_m2_s6_10 : List ℤ := pzigCat
  [
   [469884919,1364257425,2195561029,2346745627,1327430133,823316888,3853992162,6596858380,
    7309329988,5179272614,571611331,8748772969,16927963063,21799244583,19567318239,8061616289,
    12014291822,36552861728,57640262510,65185632796,50885265906,10320449374,52411359513,
    123715742109,181794914687,200296232121,156020024339,38037672135,144912941414,359917112504,
    550628265322,647555607418,582485770094,309578506178,174104798391,813818543307,1492127411279,
    2038571050937,2256026921249,1960234881813,1027267567357,557720034694,2665784635150,
    5007744781802,7147019298534,8545382600720,8637346853894,6926013053338,3089895254552,
    2918127155715,10795883221993,19851656725213,29014479114833,36894078275781,41888452038593,
    42329587579455,36650583209189,23554009418001,2164556693251,27854505027358,66235292711898,
    112092811714842,163972380364922,219948188441432,277761870996530,334987212344866,
    389204610862882,438165963394680,479938983807706,513018278869388,536394616017672,
    549583900133070,552615429682476,545983618898178,530575166886870,507576606711348,
    478374352570290,444454958622152,407313955848790,368376482254560,328935788228742,
    290110343040816,252817239222872,217763606500982,185451890717214,156194048746548,
    130135482818296,107282152172234,87529646379350,70691108617594,56524852528870,44756625974502,
    35098310152400,27264345424122,20982170063522,15999399442808,12089567115540,9053689842166,
    6720434749920,4944829558684,3607151183896,2608858317316,1870627475292,1330032371800,
    937705983870,655356186948,454091180768,311888667520,212146227926,142701835746,95074078214,
    62370976206,40131166018,25312943836,15391420858,8788153338,4644621070,2171311458,694157472]]
private theorem rkmWC_w64_m2_s6_0 : bWinChk 234 26 100000000 1024 rkmPhb_w64_m2_s6
    250 rkmXsWin_w64_m2_s6_in 284 rkmC_w64_m2_s6_1 4937739579 = true := by decide +kernel
private theorem rkmWC_w64_m2_s6_1 : bWinChk 234 24 100000000 1024 rkmPhb_w64_m2_s6
    284 rkmC_w64_m2_s6_1 314 rkmC_w64_m2_s6_2 4622889566 = true := by decide +kernel
private theorem rkmWC_w64_m2_s6_2 : bWinChk 234 23 100000000 1024 rkmPhb_w64_m2_s6
    314 rkmC_w64_m2_s6_2 346 rkmC_w64_m2_s6_3 4563482390 = true := by decide +kernel
private theorem rkmWC_w64_m2_s6_3 : bWinChk 234 22 100000000 1024 rkmPhb_w64_m2_s6
    346 rkmC_w64_m2_s6_3 374 rkmC_w64_m2_s6_4 4027732044 = true := by decide +kernel
private theorem rkmWC_w64_m2_s6_4 : bWinChk 234 22 100000000 1024 rkmPhb_w64_m2_s6
    374 rkmC_w64_m2_s6_4 402 rkmC_w64_m2_s6_5 4260703524 = true := by decide +kernel
private theorem rkmWC_w64_m2_s6_5 : bWinChk 234 22 100000000 1024 rkmPhb_w64_m2_s6
    402 rkmC_w64_m2_s6_5 431 rkmC_w64_m2_s6_6 4051281964 = true := by decide +kernel
private theorem rkmWC_w64_m2_s6_6 : bWinChk 234 21 100000000 1024 rkmPhb_w64_m2_s6
    431 rkmC_w64_m2_s6_6 460 rkmC_w64_m2_s6_7 4614354227 = true := by decide +kernel
private theorem rkmWC_w64_m2_s6_7 : bWinChk 234 21 100000000 1024 rkmPhb_w64_m2_s6
    460 rkmC_w64_m2_s6_7 484 rkmC_w64_m2_s6_8 4166388411 = true := by decide +kernel
private theorem rkmWC_w64_m2_s6_8 : bWinChk 234 21 100000000 1024 rkmPhb_w64_m2_s6
    484 rkmC_w64_m2_s6_8 508 rkmC_w64_m2_s6_9 4208380202 = true := by decide +kernel
private theorem rkmWC_w64_m2_s6_9 : bWinChk 234 21 100000000 1024 rkmPhb_w64_m2_s6
    508 rkmC_w64_m2_s6_9 534 rkmC_w64_m2_s6_10 4401456102 = true := by decide +kernel
private theorem rkmWC_w64_m2_s6_10 : bWinChk 234 20 100000000 1024 rkmPhb_w64_m2_s6
    534 rkmC_w64_m2_s6_10 555 rkmXsWin_w64_m2_s6_out 3656108351 = true := by decide +kernel
private theorem rkmWinIter_w64_m2_s6 :
    RkmWinIterSound 243 1024 rkmHbWin_w64_m2_s6 250 rkmXsWin_w64_m2_s6_in
      555 rkmXsWin_w64_m2_s6_out 47510516360 :=
  rkmChS 243 47510516360 (rkmChS 223 43854408009 (rkmChS 202 39452951907 (rkmChS 181
    35244571705 (rkmChS 160 31078183294 (rkmChS 139 26463829067 (rkmChS 117 22412547103 (rkmChS
    95 18151843579 (rkmChS 73 14124111535 (rkmChS 50 9560629145 (bWinChk_sound rkmHhb_w64_m2_s6
    rkmWC_w64_m2_s6_0) rkmHhb_w64_m2_s6 rkmWC_w64_m2_s6_1 rfl rfl) rkmHhb_w64_m2_s6
    rkmWC_w64_m2_s6_2 rfl rfl) rkmHhb_w64_m2_s6 rkmWC_w64_m2_s6_3 rfl rfl) rkmHhb_w64_m2_s6
    rkmWC_w64_m2_s6_4 rfl rfl) rkmHhb_w64_m2_s6 rkmWC_w64_m2_s6_5 rfl rfl) rkmHhb_w64_m2_s6
    rkmWC_w64_m2_s6_6 rfl rfl) rkmHhb_w64_m2_s6 rkmWC_w64_m2_s6_7 rfl rfl) rkmHhb_w64_m2_s6
    rkmWC_w64_m2_s6_8 rfl rfl) rkmHhb_w64_m2_s6 rkmWC_w64_m2_s6_9 rfl rfl) rkmHhb_w64_m2_s6
    rkmWC_w64_m2_s6_10 rfl rfl
/-- Certified `w64_m2` seg `6` (`243` steps). -/
theorem rkmWinSegWalkSnd_w64_m2_s6 :
    RkmWinSegWalkSound 243 ⟨1024, rkmHbWin_w64_m2_s6, 250, rkmXsWin_w64_m2_s6_in,
      555, rkmXsWin_w64_m2_s6_out, 47510516360⟩ :=
  @rkmSegWalk_mk 243 1024 250 555 47510516360
    rkmHbWin_w64_m2_s6 rkmXsWin_w64_m2_s6_in rkmXsWin_w64_m2_s6_out
    (rkmw_buildHbFrom_length 1024 1024 29643724279 1024 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bTl4 (bTl4 (bTl4 rkmStatOk_t00))))))
    rkmWinIter_w64_m2_s6
private def rkmC_w64_m2_s7a_1 : List ℤ := pzigCat
  [
   [493763361,985513817,1056636573,353342771,1104821310,2912093176,3978290122,3482786684,
    975726672,3464200723,8091999659,10689584541,9515857263,3156300127,7367006192,18880369794,
    26553146690,25467520220,12296382734,11834412665,40747406113,64399278999,70341385335,
    49178994731,691951042,70564572238,140652454006,183358016582,172167229824,90947170490,
    56781174037,242297280849,413011583079,504016940345,454649211915,229696938187,159836180008,
    647283607820,1113396954210,1405373945324,1372589759420,910257172040,1958457532,1250353977911,
    2619007577459,3775079209695,4342426091595,3976443059095,2453857761003,243524193978,
    3873252909754,7917980260166,11623736326182,14094213324078,14427638812892,11880029310116,
    6030819142206,3078915649739,14859122757853,28153068241237,41297095504327,52256245135905,
    58819516009983,58832459690071,50437296021599,32292850957571,3743597959277,35079841169704,
    83238656444340,139046435241742,200201167728030,263971051502212,327414095477990,
    387606240841360,441856079409874,487884457415970,523958193562530,548968799401224,
    562454328134760,564569521623498,556014789484282,537933309638854,511789885302856,
    479243844989596,442029469737066,401847397256338,360276887396624,318712423045044,
    278321819814066,240026022881984,204499975139720,172185811538718,143318975813142,
    117959945939026,96028725451974,77340484118754,61638036984744,48619756925514,37965046973216,
    29352022550332,22472207853338,17040347240662,12799552625488,9524599429746,7022677879944,
    5130884618198,3715172495672,2666243938578,1896461447784,1337084470508,934444263862,
    647135555514,444269228656,302032475544,203223212616,135262037682,88783478670,57368423308,
    36461806278,22464172834,13461307348,7642655692,3936759982,1806010668,602206970]]
private def rkmC_w64_m2_s7a_2 : List ℤ := pzigCat
  [
   [287856158,805217178,943455628,433065692,812299277,2445560151,3461839871,2830157295,598107207,
    3145171502,6981524892,8740182570,6854943076,868914252,8269354463,17039180977,21110180935,
    16968349509,3110798485,17755733708,38615708936,50161625012,43765739950,15660647310,
    30435117623,81208030469,117155309273,118243114811,71163316777,22686196440,142753908128,
    252103055136,305167650566,262110361460,104896877680,148971240089,442765703453,687541618627,
    782154390269,643464184131,238515211391,391516860274,1122059691602,1759705834594,2079479978648,
    1882068858148,1056164503872,368195474133,2189109428101,4040928510195,5446802125089,
    5905454737277,5005792127673,2544386836389,1380943400690,6322264930854,11495467864418,
    15864769993742,18288623785218,17711607384410,13368940489572,4973447586468,7147728707155,
    21995279077749,37931283841559,52804034159661,64154775798667,69476202100947,66493293180823,
    53428866269671,29219681418049,6340816990816,52550134679840,107840067624414,169903471298754,
    235891275166346,302652040443696,366987098034256,425895937425640,476786774487860,
    517635539446978,547086002563602,564484450973022,569857136880718,563838401952542,
    547561326478768,522528302199114,490472415568602,453223991482598,412591716110054,
    370265509855688,327742996638986,286283713018670,246885432123978,210282211365868,
    176959819775244,147181857247300,121023663561592,98410968265884,79155796675848,62992415252760,
    49608444141142,38669646732632,29840966744908,22801348413742,17253760717028,12931345716850,
    9600838239294,7061872390552,5146825829648,3717303190694,2660629763288,1887370908048,
    1327066056724,924749043084,638484139032,436922902490,295914814134,198358587468,131549153010,
    86003935968,55384253350,35139107620,21652034334,12965542646,7297299802,3685817066,1638219290,
    526420062]]
private def rkmC_w64_m2_s7a_3 : List ℤ := pzigCat
  [
   [227623691,727555675,988741819,834523947,261721756,1691865908,2779812304,2662034242,889742250,
    2168885179,5539016745,7373482143,5683392345,674829729,6839303848,14112093226,16742615232,
    12022232816,199919221,17304108849,32504819769,37913376709,27384302141,267533041,36922926288,
    71275023200,86270395778,68328563064,14327727264,65693316687,147012410037,196055763383,
    181959518603,88934354781,72828726676,263174990694,418870336232,469292981342,361035373226,
    81884002322,324324793609,755394154407,1070398301861,1125219906581,818672463373,136372313145,
    821686089798,1841997208392,2630936967752,2880682508334,2352793533754,961366515186,
    1165808354037,3669361656023,5996138558321,7491006189457,7533155407465,5689309841905,
    1852708724109,3661623318492,10096913218258,16319171495704,20966655664926,22665784660178,
    20280127094102,13151316685124,1292576276686,14503620088055,32665187475747,50951116389925,
    66666415578797,76949503214401,79096398349221,70878207546363,50810896352031,18342680004329,
    26059238576416,80933070101412,143948707569342,212116251333744,282050853675766,350260623091240,
    413424382872730,468636754366132,513594923463080,546716528146534,567188452696158,
    574946198940852,570597780412040,555306259814154,530646751196736,498453446001522,
    460673239255390,419233638365584,375935569618652,332374431121844,289888036696760,
    249532916739388,212082691016912,178044667701304,147689469694682,121089229974112,
    98157126933816,78688865161092,62400521836184,48960252048808,38016304511026,29218146013284,
    22231596749404,16749149406838,12496714296372,9234943626824,6760245589308,4902886847122,
    3523182095466,2508646197666,1770149239154,1237695401366,857435641448,588498448316,
    400190930904,269245549896,179335940580,118152945884,76668490458,48970018036,30753039400,
    18751154128,10943229304,6072952152,3025823938,1018604590,236318788]]
private theorem rkmWC_w64_m2_s7a_0 : bWinChk 539 21 100000000 1024 rkmPhb_w64_m2_p7a
    555 rkmXsWin_w64_m2_s7a_in 579 rkmC_w64_m2_s7a_1 4083148817 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7a_1 : bWinChk 539 21 100000000 1024 rkmPhb_w64_m2_p7a
    579 rkmC_w64_m2_s7a_1 602 rkmC_w64_m2_s7a_2 3715041053 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7a_2 : bWinChk 539 20 100000000 1024 rkmPhb_w64_m2_p7a
    602 rkmC_w64_m2_s7a_2 623 rkmC_w64_m2_s7a_3 3523098384 = true := by decide +kernel
private theorem rkmWC_w64_m2_s7a_3 : bWinChk 539 19 100000000 1024 rkmPhb_w64_m2_p7a
    623 rkmC_w64_m2_s7a_3 643 rkmXsWin_w64_m2_s7a_out 3934552268 = true := by decide +kernel
/-- Certified `w64_m2_s7a` partial walk (`81` substeps). -/
theorem rkmWinIterSnd_w64_m2_p7a :
    RkmWinIterSound 81 1024 rkmHbWin_w64_m2_p7a 555 rkmXsWin_w64_m2_s7a_in
      643 rkmXsWin_w64_m2_s7a_out 15255840522 :=
  rkmChS 81 15255840522 (rkmChS 62 11321288254 (rkmChS 42 7798189870 (bWinChk_sound
    rkmHhb_w64_m2_p7a rkmWC_w64_m2_s7a_0) rkmHhb_w64_m2_p7a rkmWC_w64_m2_s7a_1 rfl rfl)
    rkmHhb_w64_m2_p7a rkmWC_w64_m2_s7a_2 rfl rfl) rkmHhb_w64_m2_p7a rkmWC_w64_m2_s7a_3 rfl rfl
/-- Cumulative `FindAllJohnsonRampKickMuxHiW64T00` lane witness. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T00 :
    @rkmWinIterSnd_w64_m2_p7a = @rkmWinIterSnd_w64_m2_p7a := rfl

end
end QuantumComputation.Specs.DickeSol
