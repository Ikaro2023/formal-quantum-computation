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
# Caustic `r = 1024` Halo-16 Walk `w64_m16` Part `0` (`FindAllJohnsonRampKickMuxHiW64T04`)

Certifies part `0` of the `w64_m16` `r = 1024` halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Generator list for `w64_m16_s0`. -/
def rkmHbWin_w64_m16_s0 : List ℤ := altBuildHbFrom 64 1024 361115083333 0 64
/-- Entry `rkmXsWin_w64_m16_s0_in`. -/
def rkmXsWin_w64_m16_s0_in : List ℤ := [rkmP 1000000000000000]
/-- Exit `rkmXsWin_w64_m16_s0_out`. -/
def rkmXsWin_w64_m16_s0_out : List ℤ := [rkmP 82449610864028, rkmP 188084270564178,
  rkmP 300851702160193, rkmP 389585466669760, rkmP 433134580282446, rkmP 426941764802837,
  rkmP 380753645175864, rkmP 311532619178295, rkmP 236243515882359, rkmP 167326846142323,
  rkmP 111365040644977, rkmP 69987425802437, rkmP 41697205122603, rkmP 23628976349164,
  rkmP 12771477237913, rkmP 6599697732115, rkmP 3267125476459, rkmP 1552212768349,
  rkmP 708770187834, rkmP 311459992188, rkmP 131848462384, rkmP 53841537230, rkmP 21193626539,
  rkmP 8000833495, rkmP 2928574380, rkmP 917191050, rkmP 228720664]
/-- Generator list for `w64_m16_s1`. -/
def rkmHbWin_w64_m16_s1 : List ℤ := altBuildHbFrom 128 1024 186696904761 0 128
/-- Entry `rkmXsWin_w64_m16_s1_in`. -/
def rkmXsWin_w64_m16_s1_in : List ℤ := [rkmP 82449610864028, rkmP 188084270564178,
  rkmP 300851702160193, rkmP 389585466669760, rkmP 433134580282446, rkmP 426941764802837,
  rkmP 380753645175864, rkmP 311532619178295, rkmP 236243515882359, rkmP 167326846142323,
  rkmP 111365040644977, rkmP 69987425802437, rkmP 41697205122603, rkmP 23628976349164,
  rkmP 12771477237913, rkmP 6599697732115, rkmP 3267125476459, rkmP 1552212768349,
  rkmP 708770187834, rkmP 311459992188, rkmP 131848462384, rkmP 53841537230, rkmP 21193626539,
  rkmP 8000833495, rkmP 2928574380, rkmP 917191050, rkmP 228720664]
/-- Exit `rkmXsWin_w64_m16_s1_out`. -/
def rkmXsWin_w64_m16_s1_out : List ℤ := [rkmP 1396351305, rkmP 7646591317, rkmP 29906037377,
  rkmP 95521986778, rkmP 262489652791, rkmP 641595839033, rkmP 1423751003804, rkmP 2908391505966,
  rkmP 5526162130401, rkmP 9843312390064, rkmP 16537830127741, rkmP 26339284389309,
  rkmP 39929778471492, rkmP 57816444132672, rkmP 80193341013117, rkmP 106818622466652,
  rkmP 136938198551725, rkmP 169278196186158, rkmP 202119132834635, rkmP 233450132478908,
  rkmP 261181108315583, rkmP 283381664757775, rkmP 298507333095541, rkmP 305574918154080,
  rkmP 304261992060687, rkmP 294916337790030, rkmP 278480423854463, rkmP 256349604905209,
  rkmP 230189697134740, rkmP 201746681813319, rkmP 172674030686398, rkmP 144398498060820,
  rkmP 118035702141409, rkmP 94354739984785, rkmP 73788006990178, rkmP 56472838142594,
  rkmP 42312892374571, rkmP 31047420746247, rkmP 22316423474229, rkmP 15717824501699,
  rkmP 10850242973748, rkmP 7342927697831, rkmP 4872800460386, rkmP 3171452944715,
  rkmP 2024853435481, rkmP 1268374115789, rkmP 779741304438, rkmP 470424212711, rkmP 278569721585,
  rkmP 161967134799, rkmP 92422152944, rkmP 51825465559, rkmP 28431710970, rkmP 15279367096,
  rkmP 7989902343, rkmP 4021359772, rkmP 1861458549, rkmP 772222283, rkmP 257001481]
/-- Generator list for `w64_m16_s2`. -/
def rkmHbWin_w64_m16_s2 : List ℤ := altBuildHbFrom 256 1024 97199393939 0 256
/-- Entry `rkmXsWin_w64_m16_s2_in`. -/
def rkmXsWin_w64_m16_s2_in : List ℤ := [rkmP 1396351305, rkmP 7646591317, rkmP 29906037377,
  rkmP 95521986778, rkmP 262489652791, rkmP 641595839033, rkmP 1423751003804, rkmP 2908391505966,
  rkmP 5526162130401, rkmP 9843312390064, rkmP 16537830127741, rkmP 26339284389309,
  rkmP 39929778471492, rkmP 57816444132672, rkmP 80193341013117, rkmP 106818622466652,
  rkmP 136938198551725, rkmP 169278196186158, rkmP 202119132834635, rkmP 233450132478908,
  rkmP 261181108315583, rkmP 283381664757775, rkmP 298507333095541, rkmP 305574918154080,
  rkmP 304261992060687, rkmP 294916337790030, rkmP 278480423854463, rkmP 256349604905209,
  rkmP 230189697134740, rkmP 201746681813319, rkmP 172674030686398, rkmP 144398498060820,
  rkmP 118035702141409, rkmP 94354739984785, rkmP 73788006990178, rkmP 56472838142594,
  rkmP 42312892374571, rkmP 31047420746247, rkmP 22316423474229, rkmP 15717824501699,
  rkmP 10850242973748, rkmP 7342927697831, rkmP 4872800460386, rkmP 3171452944715,
  rkmP 2024853435481, rkmP 1268374115789, rkmP 779741304438, rkmP 470424212711, rkmP 278569721585,
  rkmP 161967134799, rkmP 92422152944, rkmP 51825465559, rkmP 28431710970, rkmP 15279367096,
  rkmP 7989902343, rkmP 4021359772, rkmP 1861458549, rkmP 772222283, rkmP 257001481]
/-- Exit `rkmXsWin_w64_m16_s2_out`. -/
def rkmXsWin_w64_m16_s2_out : List ℤ := [rkmP 235319579, rkmP 519769118, rkmP 880812455,
  rkmP 1557269429, rkmP 2568973982, rkmP 4350550376, rkmP 7194457137, rkmP 11636041596,
  rkmP 18715960903, rkmP 29604398293, rkmP 46419439454, rkmP 71812656275, rkmP 109663508674,
  rkmP 165567650577, rkmP 246807703480, rkmP 363742856166, rkmP 529603527722, rkmP 762095111758,
  rkmP 1083852029942, rkmP 1523492713588, rkmP 2116821599529, rkmP 2907367766011,
  rkmP 3947605502119, rkmP 5299145126235, rkmP 7033078355997, rkmP 9229459571765,
  rkmP 11976310726934, rkmP 15367746913365, rkmP 19501081314996, rkmP 24473356425919,
  rkmP 30376152442439, rkmP 37290549191719, rkmP 45280498747701, rkmP 54386123719788,
  rkmP 64617452262933, rkmP 75947358392716, rkmP 88306882081863, rkmP 101580879140340,
  rkmP 115606033973181, rkmP 130171540768211, rkmP 145021649150480, rkmP 159862142337016,
  rkmP 174368355866151, rkmP 188196777041324, rkmP 200998109517698, rkmP 212431347784130,
  rkmP 222179548169795, rkmP 229963573131072, rkmP 235556081061905, rkmP 238792008059203,
  rkmP 239576970290360, rkmP 237891752444670, rkmP 233792830482762, rkmP 227409568551226,
  rkmP 218937269543828, rkmP 208627462325924, rkmP 196775362265016, rkmP 183706287607831,
  rkmP 169760738964072, rkmP 155280146080722, rkmP 140593554467089, rkmP 126005580359370,
  rkmP 111787687909709, rkmP 98170658065879, rkmP 85340702651127, rkmP 73438022476749,
  rkmP 62557296379014, rkmP 52750966178227, rkmP 44033075952472, rkmP 36385302520047,
  rkmP 29762696790473, rkmP 24099992466915, rkmP 19318059834018, rkmP 15328839237340,
  rkmP 12040825788339, rkmP 9362662028251, rkmP 7206689311222, rkmP 5491276093987,
  rkmP 4141898860808, rkmP 3092620390738, rkmP 2285769912218, rkmP 1672338001218,
  rkmP 1211192069261, rkmP 868261874285, rkmP 616168357071, rkmP 432747123067, rkmP 300858926088,
  rkmP 207042559105, rkmP 140989096653, rkmP 95065950402, rkmP 63328319924, rkmP 41732769494,
  rkmP 27106723449, rkmP 17313182395, rkmP 10867334264, rkmP 6555617663, rkmP 3821375418,
  rkmP 2010864212, rkmP 916127320, rkmP 316729513]
/-- Generator list for `w64_m16_s3`. -/
def rkmHbWin_w64_m16_s3 : List ℤ := altBuildHbFrom 512 1024 51677427350 0 512
/-- Entry `rkmXsWin_w64_m16_s3_in`. -/
def rkmXsWin_w64_m16_s3_in : List ℤ := [rkmP 235319579, rkmP 519769118, rkmP 880812455,
  rkmP 1557269429, rkmP 2568973982, rkmP 4350550376, rkmP 7194457137, rkmP 11636041596,
  rkmP 18715960903, rkmP 29604398293, rkmP 46419439454, rkmP 71812656275, rkmP 109663508674,
  rkmP 165567650577, rkmP 246807703480, rkmP 363742856166, rkmP 529603527722, rkmP 762095111758,
  rkmP 1083852029942, rkmP 1523492713588, rkmP 2116821599529, rkmP 2907367766011,
  rkmP 3947605502119, rkmP 5299145126235, rkmP 7033078355997, rkmP 9229459571765,
  rkmP 11976310726934, rkmP 15367746913365, rkmP 19501081314996, rkmP 24473356425919,
  rkmP 30376152442439, rkmP 37290549191719, rkmP 45280498747701, rkmP 54386123719788,
  rkmP 64617452262933, rkmP 75947358392716, rkmP 88306882081863, rkmP 101580879140340,
  rkmP 115606033973181, rkmP 130171540768211, rkmP 145021649150480, rkmP 159862142337016,
  rkmP 174368355866151, rkmP 188196777041324, rkmP 200998109517698, rkmP 212431347784130,
  rkmP 222179548169795, rkmP 229963573131072, rkmP 235556081061905, rkmP 238792008059203,
  rkmP 239576970290360, rkmP 237891752444670, rkmP 233792830482762, rkmP 227409568551226,
  rkmP 218937269543828, rkmP 208627462325924, rkmP 196775362265016, rkmP 183706287607831,
  rkmP 169760738964072, rkmP 155280146080722, rkmP 140593554467089, rkmP 126005580359370,
  rkmP 111787687909709, rkmP 98170658065879, rkmP 85340702651127, rkmP 73438022476749,
  rkmP 62557296379014, rkmP 52750966178227, rkmP 44033075952472, rkmP 36385302520047,
  rkmP 29762696790473, rkmP 24099992466915, rkmP 19318059834018, rkmP 15328839237340,
  rkmP 12040825788339, rkmP 9362662028251, rkmP 7206689311222, rkmP 5491276093987,
  rkmP 4141898860808, rkmP 3092620390738, rkmP 2285769912218, rkmP 1672338001218,
  rkmP 1211192069261, rkmP 868261874285, rkmP 616168357071, rkmP 432747123067, rkmP 300858926088,
  rkmP 207042559105, rkmP 140989096653, rkmP 95065950402, rkmP 63328319924, rkmP 41732769494,
  rkmP 27106723449, rkmP 17313182395, rkmP 10867334264, rkmP 6555617663, rkmP 3821375418,
  rkmP 2010864212, rkmP 916127320, rkmP 316729513]
/-- Exit `rkmXsWin_w64_m16_s3_out`. -/
def rkmXsWin_w64_m16_s3_out : List ℤ := [rkmP 167471570, rkmP 398761704, rkmP 668078071,
  rkmP 1132690329, rkmP 1872049499, rkmP 3003506106, rkmP 4896330265, rkmP 7729811679,
  rkmP 12157657717, rkmP 18827668228, rkmP 28821635294, rkmP 43717811533, rkmP 65518036753,
  rkmP 97280810745, rkmP 142777569773, rkmP 207352917658, rkmP 297988383307, rkmP 423744791245,
  rkmP 596451018322, rkmP 830813940799, rkmP 1145604985158, rkmP 1563763890355, rkmP 2113238717962,
  rkmP 2827491888833, rkmP 3745744463345, rkmP 4913732132657, rkmP 6383200034043,
  rkmP 8212074228739, rkmP 10463572154621, rkmP 13205159121563, rkmP 16507214634492,
  rkmP 20440465683802, rkmP 25073840733542, rkmP 30470927355472, rkmP 36686644921927,
  rkmP 43763358203996, rkmP 51726557024779, rkmP 60581292931836, rkmP 70307965630124,
  rkmP 80859569402976, rkmP 92159006336723, rkmP 104097860048620, rkmP 116536378068195,
  rkmP 129304684954455, rkmP 142205661180324, rkmP 155019364281302, rkmP 167508553924748,
  rkmP 179426202961859, rkmP 190523044947474, rkmP 200556501350494, rkmP 209299441190478,
  rkmP 216548411477135, rkmP 222132184886675, rkmP 225917810938572, rkmP 227816378919270,
  rkmP 227786336157265, rkmP 225834598794411, rkmP 222016646748461, rkmP 216433336365399,
  rkmP 209226969992600, rkmP 200575147477753, rkmP 190683540117425, rkmP 179777912529658,
  rkmP 168095684618648, rkmP 155877591895192, rkmP 143359822425220, rkmP 130766579834492,
  rkmP 118304514121759, rkmP 106157216995523, rkmP 94482145216641, rkmP 83408637914161,
  rkmP 73036585499436, rkmP 63437621120431, rkmP 54655953532688, rkmP 46711034791311,
  rkmP 39600556132188, rkmP 33303358749628, rkmP 27783539207261, rkmP 22993543608397,
  rkmP 18877764601786, rkmP 15375406287166, rkmP 12423353990899, rkmP 9958560981809,
  rkmP 7919630968148, rkmP 6248318493496, rkmP 4890876071167, rkmP 3798129588254,
  rkmP 2926389550284, rkmP 2237054122984, rkmP 1696615957510, rkmP 1276744853931,
  rkmP 953213612511, rkmP 706080148189, rkmP 518927927911, rkmP 378391857482, rkmP 273752048643,
  rkmP 196416581318, rkmP 139711963597, rkmP 98573110692, rkmP 68798105787, rkmP 47546556898,
  rkmP 32485174462, rkmP 21823612492, rkmP 14419127582, rkmP 9301573583, rkmP 5744654524,
  rkmP 3457879573, rkmP 1844798455, rkmP 826948434, rkmP 273532385]
/-- Generator list for `w64_m16_s4a`. -/
def rkmHbWin_w64_m16_s4a : List ℤ := altBuildHbFrom 1024 1024 29638027559 0 1024
/-- Entry `rkmXsWin_w64_m16_s4a_in`. -/
def rkmXsWin_w64_m16_s4a_in : List ℤ := [rkmP 167471570, rkmP 398761704, rkmP 668078071,
  rkmP 1132690329, rkmP 1872049499, rkmP 3003506106, rkmP 4896330265, rkmP 7729811679,
  rkmP 12157657717, rkmP 18827668228, rkmP 28821635294, rkmP 43717811533, rkmP 65518036753,
  rkmP 97280810745, rkmP 142777569773, rkmP 207352917658, rkmP 297988383307, rkmP 423744791245,
  rkmP 596451018322, rkmP 830813940799, rkmP 1145604985158, rkmP 1563763890355, rkmP 2113238717962,
  rkmP 2827491888833, rkmP 3745744463345, rkmP 4913732132657, rkmP 6383200034043,
  rkmP 8212074228739, rkmP 10463572154621, rkmP 13205159121563, rkmP 16507214634492,
  rkmP 20440465683802, rkmP 25073840733542, rkmP 30470927355472, rkmP 36686644921927,
  rkmP 43763358203996, rkmP 51726557024779, rkmP 60581292931836, rkmP 70307965630124,
  rkmP 80859569402976, rkmP 92159006336723, rkmP 104097860048620, rkmP 116536378068195,
  rkmP 129304684954455, rkmP 142205661180324, rkmP 155019364281302, rkmP 167508553924748,
  rkmP 179426202961859, rkmP 190523044947474, rkmP 200556501350494, rkmP 209299441190478,
  rkmP 216548411477135, rkmP 222132184886675, rkmP 225917810938572, rkmP 227816378919270,
  rkmP 227786336157265, rkmP 225834598794411, rkmP 222016646748461, rkmP 216433336365399,
  rkmP 209226969992600, rkmP 200575147477753, rkmP 190683540117425, rkmP 179777912529658,
  rkmP 168095684618648, rkmP 155877591895192, rkmP 143359822425220, rkmP 130766579834492,
  rkmP 118304514121759, rkmP 106157216995523, rkmP 94482145216641, rkmP 83408637914161,
  rkmP 73036585499436, rkmP 63437621120431, rkmP 54655953532688, rkmP 46711034791311,
  rkmP 39600556132188, rkmP 33303358749628, rkmP 27783539207261, rkmP 22993543608397,
  rkmP 18877764601786, rkmP 15375406287166, rkmP 12423353990899, rkmP 9958560981809,
  rkmP 7919630968148, rkmP 6248318493496, rkmP 4890876071167, rkmP 3798129588254,
  rkmP 2926389550284, rkmP 2237054122984, rkmP 1696615957510, rkmP 1276744853931,
  rkmP 953213612511, rkmP 706080148189, rkmP 518927927911, rkmP 378391857482, rkmP 273752048643,
  rkmP 196416581318, rkmP 139711963597, rkmP 98573110692, rkmP 68798105787, rkmP 47546556898,
  rkmP 32485174462, rkmP 21823612492, rkmP 14419127582, rkmP 9301573583, rkmP 5744654524,
  rkmP 3457879573, rkmP 1844798455, rkmP 826948434, rkmP 273532385]
/-- Exit `rkmXsWin_w64_m16_s4a_out`. -/
def rkmXsWin_w64_m16_s4a_out : List ℤ := [rkmN 227779891, rkmN 350119899, rkmN 585590871,
  rkmN 736229225, rkmN 719823250, rkmN 178673275, rkmP 1526167786, rkmP 5310363490,
  rkmP 13007770460, rkmP 27169000145, rkmP 51970476872, rkmP 93393625363, rkmP 159890372817,
  rkmP 263347335031, rkmP 419596341709, rkmP 649886770596, rkmP 981343234364, rkmP 1448140175712,
  rkmP 2092323372021, rkmP 2964274634587, rkmP 4123428191598, rkmP 5637581868071,
  rkmP 7582591793984, rkmP 10040788478086, rkmP 13098905323821, rkmP 16845440588253,
  rkmP 21366561613411, rkmP 26742301592776, rkmP 33041283200734, rkmP 40315875334793,
  rkmP 48596833185728, rkmP 57888281766064, rkmP 68163443207304, rkmP 79361119536072,
  rkmP 91383414892886, rkmP 104095360729159, rkmP 117325599288470, rkmP 130869812275196,
  rkmP 144495166679067, rkmP 157946805000397, rkmP 170956145018365, rkmP 183249327380930,
  rkmP 194557757608575, rkmP 204627499701212, rkmP 213228979474793, rkmP 220166065036634,
  rkmP 225282805526066, rkmP 228469909399080, rkmP 229667995228958, rkmP 228869270106596,
  rkmP 226117051830338, rkmP 221502688005836, rkmP 215161332633283, rkmP 207265323459195,
  rkmP 198017171619902, rkmP 187641049278464, rkmP 176374183300819, rkmP 164458771950330,
  rkmP 152133443719682, rkmP 139626597998005, rkmP 127149993208400, rkmP 114893997179363,
  rkmP 103023971268565, rkmP 91677989114012, rkmP 80966061096229, rkmP 70970338099543,
  rkmP 61746071298797, rkmP 53324211314970, rkmP 45713423101766, rkmP 38903537987808,
  rkmP 32868679619241, rkmP 27570251703753, rkmP 22960837138032, rkmP 18986308839242,
  rkmP 15588966920625, rkmP 12709816228235, rkmP 10290135664548, rkmP 8273426509410,
  rkmP 6606089407627, rkmP 5238637799928, rkmP 4125905381729, rkmP 3227422054722,
  rkmP 2507630608589, rkmP 1935240059632, rkmP 1483502260256, rkmP 1129573371414,
  rkmP 854332521943, rkmP 641889725182, rkmP 479027550271, rkmP 355049154121, rkmP 261400848425,
  rkmP 191024349314, rkmP 138654378768, rkmP 99833196492, rkmP 71225331682, rkmP 50422954020,
  rkmP 35289968762, rkmP 24428559917, rkmP 16615186987, rkmP 11081885684, rkmP 7230833820,
  rkmP 4488191069, rkmP 2651424215, rkmP 1386709698, rkmP 618512629, rkmP 207830276]

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
private def rkmPhb_w64_m16_s0 : List ℕ := uNatCatN
  [
   [184890922666496,259297729426383,314889039666531,360481854511775,399517987798514,
    433774829177037,464314803435893,491833971030356,516818137486854,539622426253643,
    560515755175030,579707481049331,597364250662632,613621132828245,628589240549117,
    642361108497627,655014584173859,666615705142819,677220866480498,686878479892585,
    695630261324504,703512242031100,710555570303768,716787152211271,722230166666000,
    726904480925766,730826986034523,734011866879496,736470817954990,738213213206655,
    739246236229318,739574975426242,739202487376714,738129830503601,736356070105538,
    733878254854573,730691363900738,726788222711360,722159384641177,716792973903736,
    710674483999344,703786523623265,696108499455512,687616221774668,678281414187795,
    668071102404125,656946848116920,644863781492615,631769367614911,617601815473370,
    602287997753412,585740687369812,567854817697641,548502311173052,527524745086161,
    504722634353780,479839200058794,452534691740680,422343503886124,388597416035508,
    350274929664271,305664667207053,251448143223254,179113081333168]]
private def rkmPhb_w64_m16_s1 : List ℕ := uNatCatN
  [
   [135182998920235,190336372754098,232080398409642,266787198592930,296936130088721,
    323804132031396,348152836519116,370480427090000,391134248436103,410368120646071,
    428374329089814,445302763273460,461273006415616,476382313658827,490711070258567,
    504326640291228,517286151181285,529638553450801,541426174041846,552685907772190,
    563450145067171,573747504093876,583603415532156,593040594744052,602079426797091,
    610738283254149,619033784967942,626981021729102,634593737126394,641884485124919,
    648864763474029,655545127996572,661935290996943,668044206394550,673880143696204,
    679450752532444,684763119174515,689823816202194,694638946294380,699214180953776,
    703554794846186,707665696327853,711551454646017,715216324224854,718664266388244,
    721898968820022,724923863019771,727742139976285,730356764250390,732770486632915,
    734985855521523,737005227141109,738830774716173,740464496689392,741908224068355,
    743163626971666,744232220436176,745115369538784,745814293878829,746330071460448,
    746663642008290,746815809744529,746787245650097,746578489228393,746189949785357,
    745621907235599,744874512440255,743947787078274,742841623048907,741555781399181,
    740089890766068,738443445318798,736615802182298,734606178317930,732413646832532,
    730037132681112,727475407722271,724727085078533,721790612745905,718664266388244,
    715346141241973,711834143045284,708125977892828,704219140901739,700110903557261,
    695798299585762,691278109178952,686546841364923,681600714288385,676435633122992,
    671047165291659,665430512614552,659580479936759,653491439705995,647157291871391,
    640571418353273,633726631184985,626615113243986,619228350260915,611557052509359,
    603591064218680,595319258294729,586729413347754,577808069271017,568540356629248,
    558909793821199,548898044259362,538484623495625,527646543071492,516357873525316,
    504589202904420,492306958473383,479472546774050,466041248680180,451960778146842,
    437169370133324,421593194451723,405142779519079,387707938125723,369150346895939,
    349292296389636,327898873030363,304648162645573,279077840505102,250480182140640,
    217667134160385,178329068140264,126522661738399]]
private def rkmPhb_w64_m16_s2 : List ℕ := uNatCatN
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
    743543827161221,742764163848517,741939317975165,741069291655299,740154078739029,
    739193664760046,738188026875211,737137133795974,736040945711446,734899414202936,
    733712482149739,732480083625944,731202143788000,729878578752764,728509295465725,
    727094191559068,725633155199231,724126064923552,722572789465600,720973187568729,
    719327107787372,717634388275554,715894856562047,714108329311579,712274612071427],
   [710393499002707,708464772595595,706488203367679,704463549544568,702390556721815,
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
private def rkmPhb_w64_m16_s3 : List ℕ := uNatCatN
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
    734522308722974,735048187762683,735559153867484,736055281633260,736536644555087,
    737003315045699,737455364453487,737892863080034,738315880197207,738724484063824,
    739118741941891,739498720112440,739864483890961,740216097642453,740553624796101,
    740877127859581,741186668433014,741482307222571,741764104053739,742032117884263,
    742286406816760,742527028111031,742754038196058,742967492681708,743167446370153],
   [743353953267002,743527066592157,743686838790401,743833321541732,743966565771425,
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
    684339256060878,683171023800219,681991690116472,680801244389550,679599675380226,
    678386971222860,677163119417888,675928106824080,674681919650541,673424543448473,
    672155963102670,670876162822747,669585126134107,668282835868614,666969274154993,
    665644422408920,664308261322825,662960770855368,661601930220602,660231717876807,
    658850111514979,657457088046971,656052623593278,654636693470446,653209272178101,
    651770333385585,650319849918184,648857793742945,647384135954047,645898846757744,
    644401895456838,642893250434680,641372879138688,639840748063348,638296822732707,
    636741067682319,635173446440633,633593921509811,632002454345949,630399005338678,
    628783533790137,627155997893276,625516354709488,623864560145529,622200568929708],
   [620524334587319,618835809415291,617134944456024,615421689470377,613695992909791,
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
    390603826933355,387117067330416,383594132313378,380034100165487,376436003514372,
    372798826176334,369121499714779,365402899680522,361641841497284,357837075950610,
    353987284232495,350091072487069,346146965794568,342153401521265,338108721951772,
    334011166106776,329858860633407,325649809636520,321381883296429,317052805091360,
    312660137409741,308201265297291,303673378034647,299073448180880,294398207643478,
    289644120242411,284807350119484,279883725197257,274868694705292,269757279552434,
    264544014015185,259222876809815,253787209086186,248229616176677,242541848985502,
    236714659612305,230737624020804,224598922065203,218285061630387,211780528487662,
    205067335850451,198124436108227,190926939406342,183445055397435,175642627948467,
    167475053345434,158886231827558,149803939734287,140132489712671,129740439714030,
    118438530578627,105936255605582,91744536452402,74909670740068,52969337825242]]
private def rkmPhb_w64_m16_s4a : List ℕ := uNatCatN
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
    748708993486617,748704990393167,748696195714102,748682623359899,748664287150396,
    748641200815666,748613377996880,748580832247159,748543577032408,748501625732153,
    748454991640354,748403687966218,748347727834998,748287124288776,748221890287253,
    748152038708509,748077582349769,747998533928154,747914906081418,747826711368688,
    747733962271183,747636671192933,747534850461483,747428512328592,747317668970925],
   [747202332490731,747082514916520,746958228203727,746829484235371,746696294822704,
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
    706647199088041,706077130456905,705503608014436,704926638283918,704346227759332,
    703762382905547,703175110158522,702584415925498,701990306585190,701392788487978,
    700791867956095,700187551283818,699579844737650,698968754556506,698354286951894,
    697736448108098,697115244182358,696490681305042,695862765579829,695231503083882,
    694596899868019,693958961956886,693317695349128,692673106017557,692025199909319,
    691373982946060,690719461024094,690061640014559,689400525763586,688736124092453,
    688068440797750,687397481651532,686723252401478,686045758771045,685365006459620,
    684681001142677,683993748471924,683303254075453,682609523557892,681912562500549,
    681212376461560,680508970976034,679802351556194,679092523691523,678379492848906],
   [677663264472765,676943843985204,676221236786144,675495448253459,674766483743115,
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
    595771236206766,594770431219940,593766868286040,592760551180000,591751483663939,
    590739669487233,589725112386575,588707816086040,587687784297155,586665020718959,
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
    530964640849045,529804632172356,528642071427648,527476961724346,526309306162342],
   [525139107832045,523966369814420,522791095181037,521613286994108,520432948306538,
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
    430340804433038,428985737563335,427628340537064,426268615822408,424906565880863,
    423542193167265,422175500129819,420806489210122,419435162843198,418061523457518,
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
    314764995121796,313230806351070,311694465812338,310155975515581,308615337465903],
   [307072553663557,305527626103958,303980556777706,302431347670599,300880000763652,
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
    218971540343534,217311644849309,215649710144578,213985737976411,212319730087957,
    210651688218456,208981614103255,207309509473819,205635376057746,203959215578782,
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
    106910540158429,105121567344100,103330661278280,101537823478991,99743055461103,97946358736344,
    96147734813311,94347185197480,92544711391215,90740314893779,88933997201342,87125759806995,
    85315604200755,83503531869579,81689544297371,79873642964993,78055829350274,76236104928021,
    74414471170028,72590929545084,70765481518985,68938128554541,67108872111589,65277713646998,
    63444654614684,61609696465612,59772840647812,57934088606385,56093441783513,54250901618466,
    52406469547617,50560147004444,48711935419544,46861836220640,45009850832590,43155980677396,
    41300227174216,39442591739366,37583075786337,35721680725796],
   [33858407965602,31993258910809,30126234963679,28257337523686,26386567987530,24513927749141,
    22639418199690,20763040727599,18884796718544,17004687555469,15122714618592,13238879285414,
    11353182930727,9465626926621,7576212642495,5684941445065,3791814698368,1896833763776]]
private theorem rkmStatOk_t04 : bAllT [
  muxIntListEq (uHb rkmPhb_w64_m16_s0) (altBuildHbFrom 64 1024 361115083333 0 64),
  muxIntListEq (uHb rkmPhb_w64_m16_s1) (altBuildHbFrom 128 1024 186696904761 0 128),
  muxIntListEq (uHb rkmPhb_w64_m16_s2) (altBuildHbFrom 256 1024 97199393939 0 256),
  muxIntListEq (uHb rkmPhb_w64_m16_s3) (altBuildHbFrom 512 1024 51677427350 42 470),
  muxIntListEq (uHb rkmPhb_w64_m16_s4a) (altBuildHbFrom 1024 1024 29638027559 206 818),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_m16_s0_in)) (Nat.add 64 1),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_m16_s1_in)) (Nat.add 128 1),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_m16_s2_in)) (Nat.add 256 1),
  Nat.ble (Nat.add 58 (altIntLen rkmXsWin_w64_m16_s3_in)) (Nat.add 512 1)
  ] = true := by decide +kernel
private theorem rkmHhb_w64_m16_s0 :
    uHb rkmPhb_w64_m16_s0 = rkmDropInts 0 rkmHbWin_w64_m16_s0 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd rkmStatOk_t04)).trans
    (drHb 64 1024 361115083333 0 64)
private theorem rkmHhb_w64_m16_s1 :
    uHb rkmPhb_w64_m16_s1 = rkmDropInts 0 rkmHbWin_w64_m16_s1 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl rkmStatOk_t04))).trans
    (drHb 128 1024 186696904761 0 128)
private theorem rkmHhb_w64_m16_s2 :
    uHb rkmPhb_w64_m16_s2 = rkmDropInts 0 rkmHbWin_w64_m16_s2 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl rkmStatOk_t04)))).trans
    (drHb 256 1024 97199393939 0 256)
private theorem rkmHhb_w64_m16_s3 :
    uHb rkmPhb_w64_m16_s3 = rkmDropInts 42 rkmHbWin_w64_m16_s3 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl rkmStatOk_t04))))).trans
    (drHb 512 1024 51677427350 42 512)
private theorem rkmHhb_w64_m16_s4a :
    uHb rkmPhb_w64_m16_s4a = rkmDropInts 206 rkmHbWin_w64_m16_s4a :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bTl4 rkmStatOk_t04))).trans
    (drHb 1024 1024 29638027559 206 1024)
private theorem rkmWC_w64_m16_s0_0 : bWinChk 0 12 100000000 64 rkmPhb_w64_m16_s0
    0 rkmXsWin_w64_m16_s0_in 0 rkmXsWin_w64_m16_s0_out 665633573 = true := by decide +kernel
private theorem rkmWinIter_w64_m16_s0 :
    RkmWinIterSound 12 64 rkmHbWin_w64_m16_s0 0 rkmXsWin_w64_m16_s0_in
      0 rkmXsWin_w64_m16_s0_out 665633573 :=
  bWinChk_sound rkmHhb_w64_m16_s0 rkmWC_w64_m16_s0_0
/-- Certified `w64_m16` seg `0` (`12` steps). -/
theorem rkmWinSegWalkSnd_w64_m16_s0 :
    RkmWinSegWalkSound 12 ⟨64, rkmHbWin_w64_m16_s0, 0, rkmXsWin_w64_m16_s0_in,
      0, rkmXsWin_w64_m16_s0_out, 665633573⟩ :=
  @rkmSegWalk_mk 12 64 0 0 665633573
    rkmHbWin_w64_m16_s0 rkmXsWin_w64_m16_s0_in rkmXsWin_w64_m16_s0_out
    (rkmw_buildHbFrom_length 64 1024 361115083333 64 0)
    (bAllT_hd (bAllT_tl (bTl4 rkmStatOk_t04)))
    rkmWinIter_w64_m16_s0
private theorem rkmWC_w64_m16_s1_0 : bWinChk 0 21 100000000 128 rkmPhb_w64_m16_s1
    0 rkmXsWin_w64_m16_s1_in 0 rkmXsWin_w64_m16_s1_out 1380127811 = true := by decide +kernel
private theorem rkmWinIter_w64_m16_s1 :
    RkmWinIterSound 21 128 rkmHbWin_w64_m16_s1 0 rkmXsWin_w64_m16_s1_in
      0 rkmXsWin_w64_m16_s1_out 1380127811 :=
  bWinChk_sound rkmHhb_w64_m16_s1 rkmWC_w64_m16_s1_0
/-- Certified `w64_m16` seg `1` (`21` steps). -/
theorem rkmWinSegWalkSnd_w64_m16_s1 :
    RkmWinSegWalkSound 21 ⟨128, rkmHbWin_w64_m16_s1, 0, rkmXsWin_w64_m16_s1_in,
      0, rkmXsWin_w64_m16_s1_out, 1380127811⟩ :=
  @rkmSegWalk_mk 21 128 0 0 1380127811
    rkmHbWin_w64_m16_s1 rkmXsWin_w64_m16_s1_in rkmXsWin_w64_m16_s1_out
    (rkmw_buildHbFrom_length 128 1024 186696904761 128 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bTl4 rkmStatOk_t04))))
    rkmWinIter_w64_m16_s1
private def rkmC_w64_m16_s2_1 : List ℤ := pzigCat
  [
   [463113732,951483298,2056662110,3900141498,7446682070,13692527352,24727302908,43685535366,
    75454350608,127816921144,212590398858,346680083734,554935066456,872653078558,1347553240578,
    2044831490870,3050183008316,4473085047458,6451789932880,9154636659946,12781881836320,
    17565313378806,23763779230910,31657423331882,41536067793050,53684635936252,68365204772170,
    85794389100188,106120238224866,129397207076692,155563800341304,184423903148586,
    215632493398654,248691680029670,282955012801792,317643053833418,351869808603296,
    384677915846310,415083767755434,442125871805174,464915833181010,482687461386964,
    494838991528162,500967850894450,500891660433590,494657120369014,482534736433056,
    464999371255302,442700913225380,416424090900428,387044330250910,355480726493818,
    322649790087174,289424837631358,256599996438170,224864435163736,194784346690384,
    166794155650628,141197075726962,118170971241908,97781996334936,80000240437820,64718417600150,
    51771441699142,40953858956672,32037768060578,24786100928520,18964828877396,14351774389450,
    10742014054024,7952743227546,5823729657440,4218487127582,3022772021058,2142520889266,
    1502432961564,1042182486440,715265026964,485676176784,326159902898,216786309248,142345466230,
    92489211670,59313673826,37491494256,23415721474,14165027610,8393533530,4553749450,2165254362,
    784820262,212279580]]
private theorem rkmWC_w64_m16_s2_0 : bWinChk 0 38 100000000 256 rkmPhb_w64_m16_s2
    0 rkmXsWin_w64_m16_s2_in 24 rkmC_w64_m16_s2_1 5408146930 = true := by decide +kernel
private theorem rkmWC_w64_m16_s2_1 : bWinChk 0 28 100000000 256 rkmPhb_w64_m16_s2
    24 rkmC_w64_m16_s2_1 58 rkmXsWin_w64_m16_s2_out 4835002900 = true := by decide +kernel
private theorem rkmWinIter_w64_m16_s2 :
    RkmWinIterSound 66 256 rkmHbWin_w64_m16_s2 0 rkmXsWin_w64_m16_s2_in
      58 rkmXsWin_w64_m16_s2_out 10243149830 :=
  rkmChS 66 10243149830 (bWinChk_sound rkmHhb_w64_m16_s2 rkmWC_w64_m16_s2_0) rkmHhb_w64_m16_s2
    rkmWC_w64_m16_s2_1 rfl rfl
/-- Certified `w64_m16` seg `2` (`66` steps). -/
theorem rkmWinSegWalkSnd_w64_m16_s2 :
    RkmWinSegWalkSound 66 ⟨256, rkmHbWin_w64_m16_s2, 0, rkmXsWin_w64_m16_s2_in,
      58, rkmXsWin_w64_m16_s2_out, 10243149830⟩ :=
  @rkmSegWalk_mk 66 256 0 58 10243149830
    rkmHbWin_w64_m16_s2 rkmXsWin_w64_m16_s2_in rkmXsWin_w64_m16_s2_out
    (rkmw_buildHbFrom_length 256 1024 97199393939 256 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bTl4 rkmStatOk_t04)))))
    rkmWinIter_w64_m16_s2
private def rkmC_w64_m16_s3_1 : List ℤ := pzigCat
  [
   [223790024,609577922,993763890,1802986984,2917550284,4755501128,7671176644,12213809446,
    19228274054,29923164516,46169809006,70294477422,106067286052,158297845582,233901381008,
    342179550990,495255315858,709898990448,1007065283330,1414286049474,1966533642574,
    2706927776376,3689299782408,4978303817194,6651607470664,8800201454728,11528883350740,
    14956771966060,19215307236722,24447732851628,30805022566980,38442237122094,47513564381758,
    58164454905098,70525110432134,84700691087070,100762740206354,118739484823388,138606120078204,
    160278123293138,183603442437516,208359364122864,234250897909964,260912651029426,
    287915508728368,314774782702972,340964607340782,365933435445982,389122919756342,
    409989084097452,428022344748822,442769399009936,453851075489102,460979013234860,
    463968511883654,462745559555948,457350976244210,447937023051760,434761140742686,
    418174278009748,398604799235772,376541213758606,352510865080156,327060413343434,
    300735206541442,274060329030242,247525001996414,221567980350356,196568855182758,
    172840820453848,150627966156204,130105993998522,111384310810660,94512737201966,79487518570802,
    66260227817882,54746526216560,44834283939102,36393128043336,29280834405742,23351040516438,
    18458315646926,14462329150226,11231976276410,8646399774816,6597596906284,4990059811832,
    3740980376802,2780087274054,2047753386556,1495212656058,1082152417082,776294767398,
    552091743682,389041681270,271823934920,188090477626,128906704060,87462776376,58520060922,
    38726294146,25045641748,15867920662,9687852562,5505359108,2913380726,1142890866,323370012]]
private def rkmC_w64_m16_s3_2 : List ℤ := pzigCat
  [
   [211743772,420075076,868784622,1373116496,2408875704,3843433482,6026018338,9570955614,
    14757206628,22749360354,34528451642,52026417084,77779672136,114881012434,168363734658,
    244290425962,351290559466,500516227820,706317964410,987820984080,1368582926422,1878852002370,
    2555810788194,3444877822760,4601297748502,6090062578214,7987994260398,10383121509418,
    13375237845488,17075645085006,21605136074010,27093213906450,33673887150368,41482634980208,
    50651431790518,61302360693170,73541996497318,87452771636542,103086527104088,120456432003858,
    139529629686042,160221741410858,182390675968136,205834978052342,230292266613400,
    255441429720782,280907805122782,306269738846640,331070468451020,354829948487600,
    377060603297126,397283707027428,415045669459362,429936175043566,441602632339886,
    449765188921310,454227384633518,454883707150584,451724643494202,444835450826360,
    434393743701968,420660965796658,403971830073244,384721309339244,363348084286094,
    340319547586104,316113775325918,291204264552696,266045098933294,241057372917016,
    216620133395002,193060963257720,170652497811550,149609001019278,130087070195032,
    112188026196496,95961858247336,81413209401388,68507600825948,57178799400258,47335408917214,
    38868494995902,31657215940686,25574819600860,20493970463392,16289578359602,12843150579932,
    10044159700130,7791786206230,5995856936662,4576567767642,3465283861790,2602709020056,
    1939123745426,1433190133238,1050691317492,764268877014,551326359966,394482891128,279909306118,
    196867808648,137396524684,94858532708,64859415798,43692192952,28898363094,18784279550,
    11725512582,7110567986,3906521262,1865163050,674844178]]
private def rkmC_w64_m16_s3_3 : List ℤ := pzigCat
  [
   [215286887,70607134,398481540,872395318,1579009478,2467115962,4096528676,6344685944,9885824662,
    15208058582,23063644174,34947709586,52122557060,77271934526,113440793428,165033434288,
    238187055390,340286618124,482112680218,676669093624,941493321450,1298327852304,1774410024480,
    2403803466480,3227677003266,4296143003238,5668310132272,7413558688276,9611854214216,
    12354018905296,15741423711372,19884895761448,24903415701278,30921198231208,38065331899322,
    46460851262578,56226212380890,67467738583326,80272322254274,94702063340580,110786149754246,
    128514756650052,147833158201336,168635823667538,190763942727300,214002670157438,
    238082411270896,262681168226608,287429881118650,311921121972384,335718135015682,
    358368669829330,379418091178954,398424601055208,414975049665736,428698990109090,
    439283674495866,446484633240730,450136007583162,450156703142680,446552717605310,
    439417785541330,428928104033216,415336327613110,398960656330308,380172601507480,
    359383837842826,337030104325790,313557650804466,289407666210168,265003810774438,
    240740747756922,216973770549226,194013062037906,172117598141044,151494064125960,
    132296162262214,114626239754514,98539901229782,84049358129780,71130756253262,59728917189418,
    49764618185222,41140536174392,33747062707738,27467821364826,22183933342490,17778058860228,
    14137085671758,11155150493712,8734298808174,6786137673178,5232164580984,4002970785408,
    3039145574982,2289664267770,1711821947208,1270045188142,934951476732,683171692658,
    495292474174,356302321750,254210455476,179768296252,126155779008,87602601714,60259550476,
    40821220044,27115544562,17656590652,11009667978,6644742830,3623269444,1713686852,614092034]]
private def rkmC_w64_m16_s3_4 : List ℤ := pzigCat
  [
   [401057340,858194790,1439225042,2508147428,3843870766,6089057532,9455847686,14579078942,
    22316789366,33554382266,50347497280,74624539626,109797504970,160120422436,231098472382,
    330709333922,468720344278,658630378502,917096988370,1265491406802,1730918263568,2346146977256,
    3152253881070,4197789036180,5541207461908,7250488693936,9404204310276,12091893579964,
    15413008441444,19476901153808,24400580436686,30306946239750,37321303402826,45567599945734,
    55163580122402,66215124200126,78810158991050,93011585112592,108851410159566,126323183180846,
    145376671637530,165912763852760,187779217111412,210770053859058,234624378697852,
    259029886493460,283627804515562,308019968432546,331779513194282,354461813231240,
    375619079835092,394814127654500,411635742726582,425713547761836,436730603592274,
    444436689346996,448656630818534,449297517326250,446351931494150,439897574784270,
    430094815169294,417178818476022,401451438725264,383268832406420,363028177749962,
    341154045350206,318082892836970,294250159096746,270075894453720,245953934330330,
    222242433009004,199255803584690,177260696460966,156471934551376,137053135282096,
    119117546615480,102730977660754,87916935290820,74660816030366,62917133931176,52614549803560,
    43662409933772,35956777956450,29384975743780,23831481150070,19180484632534,15319964102182,
    12143728488394,9552920977416,7458095977790,5778516364742,4443485683832,3391202541574,
    2568569978354,1930983896798,1440597468828,1066758509106,783947384722,571735903964,
    413884118406,297145470026,211720312938,149463442214,104546705376,72406324634,49432667700,
    33351639888,21931196584,14064845110,8625303836,4879578162,2543080542,976789188,269960820]]
private def rkmC_w64_m16_s3_5 : List ℤ := pzigCat
  [
   [449363246,955256600,1567010680,2639897010,4072512546,6548132282,10258092456,15873187826,
    24530519154,37242759664,56202673044,83823061822,123962381196,181508204184,262994073970,
    377700841446,537044487756,756623327116,1055875380144,1459560547526,1998896761434,
    2711922078432,3645596024526,4855514940552,6407998927524,8380128047194,10859829597688,
    13946654229618,17750019517822,22389081808080,27989487185236,34680929851542,42593494212402,
    51851931248154,62571193757844,74848793038930,88758854606102,104344542427536,121610814486850,
    140518829797830,160979031575560,182848109813854,205925735757526,229954753161806,
    254623692469086,279570577692758,304391666077482,328650322730554,351890096398896,
    373648361429714,393471061426678,410929434271804,425634301075518,437251645062666,
    445514443209566,450233053404240,451302916286884,448707400981500,442519257533212,
    432896236924196,420075185310330,404362333747364,386120669526316,365757065322824,
    343706272300836,320416867313336,296335933822830,271895349218276,247500250967042,
    223518040233856,200271903140810,178034686304308,157026583032280,137414625569802,
    119313528623278,102789936556984,87865998878494,74525833056496,62721282915270,52378110148332,
    43402951926276,35688319015286,29119059290414,23576387229492,18942161168620,15102332114994,
    11948665274640,9381420481020,7309536983134,5651818813686,4336869136718,3302481092684,
    2495832518502,1871862075266,1393284278594,1029217593088,754434348248,548800332950,
    396104706526,283523717436,201422872470,141666337792,98729671316,68103370616,46187932248,
    30841467868,20047492444,12734593438,7730938680,4309236976,2189047894,814198848,217451416]]
private theorem rkmWC_w64_m16_s3_0 : bWinChk 42 21 100000000 512 rkmPhb_w64_m16_s3
    58 rkmXsWin_w64_m16_s3_in 82 rkmC_w64_m16_s3_1 3595038355 = true := by decide +kernel
private theorem rkmWC_w64_m16_s3_1 : bWinChk 42 20 100000000 512 rkmPhb_w64_m16_s3
    82 rkmC_w64_m16_s3_1 108 rkmC_w64_m16_s3_2 3558784369 = true := by decide +kernel
private theorem rkmWC_w64_m16_s3_2 : bWinChk 42 19 100000000 512 rkmPhb_w64_m16_s3
    108 rkmC_w64_m16_s3_2 134 rkmC_w64_m16_s3_3 4105010185 = true := by decide +kernel
private theorem rkmWC_w64_m16_s3_3 : bWinChk 42 19 100000000 512 rkmPhb_w64_m16_s3
    134 rkmC_w64_m16_s3_3 164 rkmC_w64_m16_s3_4 3647384243 = true := by decide +kernel
private theorem rkmWC_w64_m16_s3_4 : bWinChk 42 19 100000000 512 rkmPhb_w64_m16_s3
    164 rkmC_w64_m16_s3_4 193 rkmC_w64_m16_s3_5 3558753672 = true := by decide +kernel
private theorem rkmWC_w64_m16_s3_5 : bWinChk 42 19 100000000 512 rkmPhb_w64_m16_s3
    193 rkmC_w64_m16_s3_5 222 rkmXsWin_w64_m16_s3_out 3688354132 = true := by decide +kernel
private theorem rkmWinIter_w64_m16_s3 :
    RkmWinIterSound 117 512 rkmHbWin_w64_m16_s3 58 rkmXsWin_w64_m16_s3_in
      222 rkmXsWin_w64_m16_s3_out 22153324956 :=
  rkmChS 117 22153324956 (rkmChS 98 18464970824 (rkmChS 79 14906217152 (rkmChS 60 11258832909
    (rkmChS 41 7153822724 (bWinChk_sound rkmHhb_w64_m16_s3 rkmWC_w64_m16_s3_0)
    rkmHhb_w64_m16_s3 rkmWC_w64_m16_s3_1 rfl rfl) rkmHhb_w64_m16_s3 rkmWC_w64_m16_s3_2 rfl rfl)
    rkmHhb_w64_m16_s3 rkmWC_w64_m16_s3_3 rfl rfl) rkmHhb_w64_m16_s3 rkmWC_w64_m16_s3_4 rfl rfl)
    rkmHhb_w64_m16_s3 rkmWC_w64_m16_s3_5 rfl rfl
/-- Certified `w64_m16` seg `3` (`117` steps). -/
theorem rkmWinSegWalkSnd_w64_m16_s3 :
    RkmWinSegWalkSound 117 ⟨512, rkmHbWin_w64_m16_s3, 58, rkmXsWin_w64_m16_s3_in,
      222, rkmXsWin_w64_m16_s3_out, 22153324956⟩ :=
  @rkmSegWalk_mk 117 512 58 222 22153324956
    rkmHbWin_w64_m16_s3 rkmXsWin_w64_m16_s3_in rkmXsWin_w64_m16_s3_out
    (rkmw_buildHbFrom_length 512 1024 51677427350 512 0)
    (bAllT_hd (bTl4 (bTl4 rkmStatOk_t04)))
    rkmWinIter_w64_m16_s3
private def rkmC_w64_m16_s4a_1 : List ℤ := pzigCat
  [
   [377245488,810120608,1337335636,2400020332,4051115430,6581516536,10631037688,16799528014,
    26529630958,41171790428,63236092242,96013078394,144178997570,214157414478,314459369062,
    456594492866,655901726310,932018629946,1310529496172,1823328007286,2510447864482,
    3421094632248,4614316199418,6161046986042,8143625865818,10657304030244,13809613513724,
    17719179171364,22515312307432,28333983045274,35315642905160,43599912573194,53320037323602,
    64596798523142,77530802728546,92194674033966,108625446650578,126816217087024,146710044675426,
    168193581675248,191093614911940,215175119252632,240141550119938,265639815110346,
    291265418234424,316573139570644,341089078973706,364324083926268,385791275339060,
    405021814291198,421582759752700,435093066163542,445238083481338,451781944014850,
    454576495032086,453566752757184,448793030854916,440388019752506,428571510456972,
    413640095624234,395955498880772,375930529484722,354012064083648,330666428342616,
    306362388001858,281556413569488,256679575298764,232125957586530,208244324947194,
    185332088180074,163630910641300,143326917361812,124550966715950,107382386329934,
    91853307820216,77954321071376,65641504794284,54842811623434,45464062075764,37396941117578,
    30523203425118,24720349278634,19866557733418,15842885231184,12537297577164,9845529531524,
    7672558766128,5933690920882,4553880561822,3468496960420,2621663203104,1966613613434,
    1464212106920,1081746440346,793208409652,577041276422,416583926676,298324267692,211695811310,
    148988685358,103669311166,71453446506,48529368218,32415630760,21190660372,13493521920,
    8137948884,4489385890,2289207124,882931478,248924540]]
private def rkmC_w64_m16_s4a_2 : List ℤ := pzigCat
  [
   [571398012,941295666,1817708352,3056404434,5108227884,8395478194,13410605874,21345663604,
    33612233060,52152094700,80135832780,121443511558,181957671136,269451832654,394309742176,
    570688780906,816585193892,1155836099138,1618133880158,2240967581920,3070846078096,
    4163527357222,5586695359502,7419207236586,9752541755656,12690822045088,16349619354042,
    20855034660092,26341433265732,32947884284932,40814511082460,50076464769118,60858225624338,
    73266054328956,87380372244436,103248578218814,120876219481206,140221171207108,161186498523472,
    183616592840380,207295241351114,231945047300248,257230830736400,282765801022010,
    308119055133388,332828187989976,356412127483694,378387124100842,398283103726256,
    415660152430428,430125130875080,441346588606870,449066684781702,453112101971128,
    453399553153558,449938998683958,442832835366824,432269630029132,418517829667524,
    401913531784718,382846648430426,361747203677566,339068282127070,315271384011542,
    290810655985928,266119807154558,241600623301596,217612865275730,194468563739850,
    172426303740580,151690605555904,132411716092486,114687563851662,98568998480518,84063481131740,
    71142521520276,59746775950028,49793546279130,41182718960770,33802454184680,27534793464980,
    22259974552550,17860305409732,14222574203870,11241050768632,8818117386892,6865823551754,
    5306200508948,4070322851538,3099260669684,2342408468924,1757377210694,1308795543326,
    967356493538,709810337238,516816495700,373421208872,267618597584,190078439790,133942080970,
    93343751396,64407359312,43753645218,29147972748,19062395862,11959753624,7291305888,4028552876,
    1935014364,704024320]]
private def rkmC_w64_m16_s4a_3 : List ℤ := pzigCat
  [
   [373083210,901777474,1615396640,2747208354,4675015808,7649991900,12567546600,20154078550,
    32150303258,50414129230,77948913438,119109614746,179569667962,267400091386,393520646104,
    571972878322,821980927438,1167537575498,1639546557378,2276765677424,3126659804148,
    4247173872222,5707689980922,7589244325348,9985708466446,13003054231222,16759126298814,
    21382200508444,27007680771694,33776048541516,41827027869222,51294447840198,62300661583308,
    74947751324324,89311544851584,105432442955326,123307982701414,142886962796206,164062525867448,
    186669178298522,210480223508128,235209350989178,260513424596526,285998559266526,
    311230719783164,335745702567198,359064718040584,380708519824842,400214630514842,
    417153798581270,431145404010542,441872244052464,449092036573792,452647002712864,
    452468945762536,448581698559176,441099099452438,430219909887782,416219043019388,
    399435857888470,380261813218340,359124209684350,336471722947178,312758994063948,
    288431603678328,263914140357592,239597901293452,215833071330148,192921684719484,
    171113824475772,150606461405776,131543048199134,114017475962182,98076725791624,83726505717876,
    70937248571382,59649848555812,49783094190176,41238236143936,33905910790906,27670634076036,
    22414986196396,18023945539062,14386437384648,11398985973550,8965935858242,7000800329898,
    5426833005950,4176084298366,3190548857542,2419961504598,1822366023178,1362478922408,
    1011250820692,745061206948,544900237060,395556910260,284836481026,203600479352,144169879866,
    101044128972,70098995380,47979606092,32452925800,21357878626,13664928342,8370197464,
    4759903128,2525209156,996578348,284017482]]
private def rkmC_w64_m16_s4a_4 : List ℤ := pzigCat
  [
   [205044738,437838240,1001880602,1720734366,3007493798,5190349140,8568608396,14326452296,
    23111859926,36964679044,58402562658,90486315672,138618892682,209325784624,312180928364,
    459756527332,668472497324,960178446694,1362365528480,1910578268278,2648140726598,
    3629108208632,4917914703854,6590708566582,8736770884608,11457701511236,14867576504184,
    19091210740800,24262640045458,30521626065400,38009677562648,46864864978816,57215656473762,
    69174137004392,82827637016670,98231821070666,115402131954042,134307150199312,154862343812804,
    176924631145300,200291264118228,224698122109170,249822990235354,275291012846816,
    300682256026548,325543408082008,349399861424190,371771885505572,392189861533678,
    410210995346590,425435943715662,437522462210766,446199670344154,451276867111362,
    452651050043082,450310312276452,444332848517548,434884067071014,422207709000840,
    406616964270402,388481207122274,368211501819272,346246404422538,323035468802412,
    299026297185656,274649396618736,250307482082060,226365508515420,203143416421364,
    180911539980174,159887628186514,140237012003866,122073948582350,105465368103134,
    90434763513812,76968410353438,65021072730086,54521857631144,45381307598260,37495773501010,
    30753758769732,25040167425614,20239897801604,16241535536734,12938849343512,10233711760674,
    8036099340496,6265227133640,4849944285934,3727652754282,2844942426250,2155799346878,
    1621989003056,1211802282898,898839161250,662089022700,484002526334,351195187712,252862744060,
    180516344546,127892427482,89585383450,62132805696,42442942658,28467029188,18770325600,
    11871852260,7284898456,4035038334,1935360014,701263784]]
private def rkmC_w64_m16_s4a_5 : List ℤ := pzigCat
  [
   [505634782,975648486,1731740116,3108163140,5494616022,9296446876,15643637070,25639237468,
    41260924360,65315696940,101906237722,157052418610,238169807536,356253982226,525593310254,
    765137235304,1099858115528,1560890701738,2188275792740,3030903450554,4148402469718,
    5612310171010,7506478407094,9928125846714,12986444857660,16803239558702,21510199864860,
    27246355348204,34155046485194,42377837216076,52050012359428,63292592877500,76205628241342,
    90860285159076,107290115381242,125484842583086,145381869222738,166862710721714,
    189748318666278,213798385234288,238712827845264,264135718063894,289663071906708,
    314851964785164,339233537451956,362327149204084,383656426538054,402765330441056,
    419234808306194,432698334254422,442854930882458,449481208946468,452438377557802,
    451677957604522,447242583345118,439262523058166,427950798533278,413592804306714,
    396535513419156,377173437502342,355933772506012,333261778603706,309604960601150,
    285400496120060,261061659202620,236968014157954,213457586267212,190820194363566,
    169295105523440,149068657541544,130276303858156,113004724376808,97295571522338,83151524727174,
    70540746598618,59404226742294,49660857880030,41213762749592,33956074587712,27774630403590,
    22555433465462,18185785319492,14558041304974,11571289310682,9132118422294,7156501042358,
    5568751586840,4302941361216,3301672898902,2515662598434,1903626981980,1430319604260,
    1067284397490,790740330782,581636529404,424868723462,307904603912,221558490946,157997208192,
    111656424284,78162641172,53950802000,36877050372,24622195100,16110611072,10121344590,
    5948779358,3073047126,1367919984,471093018]]
private def rkmC_w64_m16_s4a_6 : List ℤ := pzigCat
  [
   [447890702,1172432626,2203950218,4174106248,7191401228,12442847974,20741901068,34303275932,
    55676714572,88574309088,138648250628,213309468110,323328309664,482777788178,710565441180,
    1031245043912,1476405156358,2085971952516,2909445797284,4007457410344,5452349802344,
    7329650442250,9737763762558,12788600516804,16606298892836,21324854378234,27086565195462,
    34036741067972,42319716277078,52072349740620,63416743800650,76453560812634,91252595576306,
    107845689413242,126218441924608,146303912730380,167977428049788,191052478923580,
    215281265287054,240355119727516,265910065191670,291534193786228,316777583991290,
    341166229596146,364215597332452,385447884759166,404407681084244,420678705315478,
    433899732768182,443776738922722,450095084057098,452726029042314,451631716190796,
    446865399263570,438567624230588,426960971763374,412338993212116,395055349269346,
    375509222858420,354130515404662,331365438060548,307660444521310,283450102319540,
    259143805911334,235116326662114,211700015179922,189178509338674,167785117258958,
    147700441861062,129054636663120,111929578893106,96362854176390,82353992606698,69868708942144,
    58846511066080,49205234323360,40847759263892,33667033026312,27550742052970,22385562588396,
    18060156321370,14467989210690,11508921044650,9091211848806,7131380099418,5555238198542,
    4297729599830,3301866507930,2519403469522,1909130900972,1436779056944,1073883744816,
    796977982942,587498237518,429920302700,312309855574,225080136686,160821304374,114059973600,
    80037298194,55613965168,38015492692,25441356866,16655653184,10415517584,6287042708,3420447248,
    1611543888,575033074]]
private def rkmC_w64_m16_s4a_7 : List ℤ := pzigCat
  [
   [512551612,1086072660,2019683084,3936660976,7013563346,12515010250,21562035030,36201211358,
    59502530046,95684682690,151338182116,234860769970,358417446548,538012702068,795091000252,
    1157825314560,1661483937588,2351371214260,3282759656854,4522931403460,6152119609024,
    8263856174424,10965967028500,14378611673330,18634288538102,23874494094162,30246451945158,
    37899006632946,46975642141820,57609136150014,69912707716700,83972628707014,99839559377480,
    117519909153564,136969927369386,158088149660932,180712388510476,204617081427300,
    229514199298482,255057587476378,280848243093230,306445450779240,331377722758444,
    355157802018054,377298642822722,397329359832504,414813602382548,429363758820124,
    440656841852286,448445306499620,452566501780798,452948169637112,449609763392198,
    442661149835828,432296595030032,418786422653040,402465196381490,383718771804174,
    362969256155648,340660128265280,317241228083554,293153845395556,268819202245992,
    244626492718436,220924933675012,198017521967264,176156252319782,155541573071592,
    136321957211508,118596959994392,102420403593760,87805210263808,74729563237204,63141717998992,
    52967348664902,44114607350944,36479863324744,29952753504352,24419804888584,19769177603846,
    15892267437014,12686682451854,10057525297356,7918079226378,6191062111482,4807489127868,
    3707648931482,2839937403994,2160440874294,1632540705308,1225161549260,913241363058,
    675954694086,496742395936,362519228888,262517721774,188781760198,134558645060,95029645756,
    66416894850,45705723050,31055691704,20551098990,13270086596,8207011546,4690481454,2476711200,
    963566822,269609800]]
private def rkmC_w64_m16_s4a_8 : List ℤ := pzigCat
  [
   [463442872,1074778990,2416231606,4635116874,8852783750,15920026844,27884577052,47595024744,
    78907404308,128110198568,203183100786,316144149184,482877217354,724616304250,1069526730664,
    1553115527912,2221403998316,3130416344668,4349074327336,5959426638538,8057726917070,
    10754682681802,14174110937956,18452389798612,23735194311118,30174214836284,37921906222504,
    47125599543430,57920265167966,70420469307256,84712045272986,100843035855902,118816199790846,
    138580589157256,160026317649446,182980479645188,207204978607258,232398962914676,
    258201748884844,284201106638482,309943327091524,334945681117564,358712287209534,
    380749798267978,400585626060036,417784113706974,431962973618486,442807660349640,
    450082125766400,453638538713432,453420870019326,449466472524186,441903149162384,
    430942581260154,416871666152232,400039214784058,380843187248408,359714871571362,
    337103557435180,313462034429918,289231667445016,264831012692142,240644128571220,
    217013118375592,194232399508366,172544714639884,152140920939090,133159692611916,
    115691275006940,99780924217536,85433872487028,72621703872082,61287389887978,51352562804626,
    42722288885980,35290905102554,28947011660898,23576945469858,19069305904606,15316404245022,
    12217145126544,9678072092670,7614044471056,5949468081024,4617133761126,3559017580028,
    2724938023288,2072207894804,1565308412534,1174263064354,875004193696,647515141982,
    475835784448,347294535362,251500534268,180817603658,128811761526,90909049090,63494746402,
    43675545794,29656679038,19598614594,12615813030,7758041910,4398607466,2297792204,884655800,
    245113164]]
private def rkmC_w64_m16_s4a_9 : List ℤ := pzigCat
  [
   [229488230,718374716,1808591860,4000147576,8220352696,15551187194,28264490076,49482886294,
    83842072642,138364542246,222475266078,350105889986,539477841442,815074689532,1209266001618,
    1762952883186,2528333051634,3569265580592,4963327968582,6802491150930,9193341933494,
    12257445518694,16129322085244,20955369610124,26889396055556,34088512508002,42707583035872,
    52891232091000,64767012082934,78435658478224,93962857025614,111370120288964,130626505473584,
    151642683088280,174264903341122,198273819691632,223383977806766,249247258021716,
    275459894987500,301571463035402,327098606235488,351538700367854,374387236838238,
    395155289834078,413386665585698,428675690800284,440681179908498,449140096305538,
    453876244871446,454806247957222,451942238427978,445388961156366,435339220499048,
    422063842279268,405900661584916,387240829684562,366513024262910,344168757106800,
    320665736069854,296454315965532,271963895986648,247591644537590,223694351932704,
    200580969323198,178509770801150,157685726356108,138261344666558,120339232225008,
    103975193978040,89184244499338,75945093532036,64206989399058,53895592642304,44918690055816,
    37172592732656,30545984520788,24925248593020,20197328427828,16252832261604,12988674530912,
    10308766340346,8126057693958,6361992715416,4947199068350,3821211061896,2931545096488,
    2234016265682,1690952671924,1271322861284,949445300382,704176851066,518799147264,379445069252,
    275557832940,198576245384,141865503512,100517839018,70378344170,48744504664,33196929626,
    22135088194,14411861380,8934965096,5309367124,2825157766,1295516250,449791754]]
private def rkmC_w64_m16_s4a_10 : List ℤ := pzigCat
  [
   [247464129,167538057,470182002,1751205682,4623154040,9990166168,19908323728,37248983480,
    66432454572,114441578054,190505018696,308388036358,486516436350,749916574794,1131742350566,
    1674354445230,2431925445496,3470864230612,4872326668146,6732543847132,9163159999994,
    12291615112474,16258777172680,21217512935392,27327928352390,34752977555916,43652187438786,
    54173224562240,66444332132180,80563995255262,96592510729734,114542458699400,134370416260146,
    155971068264276,179171532708660,203730640868814,229339334302862,255625544072756,
    282162115972156,308476913756830,334067809969672,358417773226772,381013288947998,
    401362265408304,419011754966552,433565746441278,444698941283254,452169783953948,
    455828228226296,455620630167886,451590795421872,443875749781908,432699760968208,
    418363071938966,401229708689938,381712610352836,360257283399468,337326577423016,
    313384075936806,288880712028002,264241567136358,239855318715688,216066618825508,
    193169603108504,171405872232866,150962859664828,131975518453800,114529354826684,
    98664187897862,84380472629916,71644333614518,60394600857878,50548638012926,42008021655754,
    34664590694642,28404335211422,23112460588610,18676089669540,14987116330338,11944399970020,
    9454365967406,7432695773570,5803785917934,4501318645678,3467744953732,2653557130930,
    2016968397396,1522931533138,1142074817708,850888892266,629520811516,462513154960,337542168884,
    244352108984,175599623252,125077135884,88293614142,61621281112,42292846488,28663752400,
    18946833940,12229208530,7529497872,4253133462,2195713806,831016950,225950290]]
private def rkmC_w64_m16_s4a_11 : List ℤ := pzigCat
  [
   [235692767,505227957,648921937,506886551,85589989,1496534874,4999555188,12340760428,
    26192451266,50852916322,93139850560,162326683910,272429606440,442449619898,698520867652,
    1075260570992,1617234534834,2381702041550,3439183042292,4875925971250,6794185415534,
    9312679620098,12566467202280,16704508490522,21887939041378,28284699732444,36064318304938,
    45390723960614,56413547666272,69259759589568,84022635412122,100752751519018,119448174253252,
    140046434310478,162418740453840,186365128319860,211614587533056,237826654851884,
    264597854871370,291471158304234,317948039463390,343504815657198,367609144805208,
    389739567482666,409404181300378,426158946089602,439625103141204,449502476638224,
    455581319290904,457748678420282,455991724415722,450396818158884,441143615460162,
    428497043784810,412794328455712,394431410611702,373846765133548,351504893996538,
    327880112261256,303440747644744,278635058469060,253879797391136,229549709017674,
    205971670514364,183419258669118,162111032204086,142211427276584,123831650666368,
    107035210425682,91841809474212,78233457547966,66161393999542,55551342574296,46310804197176,
    38334063747834,31507993247112,25716303934410,20843055107522,16776578942402,13410539447306,
    10646506742266,8394638579650,6574159021554,5113862179042,3951076392066,3032273402434,
    2311605628438,1750467104886,1316744213330,983782712798,730009519412,538139741368,393787916380,
    286233335098,206404112502,147478054926,104569045996,73305139164,50837545784,34652500884,
    23181182796,15206050408,9513555434,5686900996,3015977708,1365539984,465345792]]
private theorem rkmWC_w64_m16_s4a_0 : bWinChk 206 10 100000000 1024 rkmPhb_w64_m16_s4a
    222 rkmXsWin_w64_m16_s4a_in 237 rkmC_w64_m16_s4a_1 1874990080 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4a_1 : bWinChk 206 9 100000000 1024 rkmPhb_w64_m16_s4a
    237 rkmC_w64_m16_s4a_1 251 rkmC_w64_m16_s4a_2 1843940699 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4a_2 : bWinChk 206 10 100000000 1024 rkmPhb_w64_m16_s4a
    251 rkmC_w64_m16_s4a_2 266 rkmC_w64_m16_s4a_3 1893971223 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4a_3 : bWinChk 206 9 100000000 1024 rkmPhb_w64_m16_s4a
    266 rkmC_w64_m16_s4a_3 279 rkmC_w64_m16_s4a_4 1856895388 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4a_4 : bWinChk 206 9 100000000 1024 rkmPhb_w64_m16_s4a
    279 rkmC_w64_m16_s4a_4 294 rkmC_w64_m16_s4a_5 1758117303 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4a_5 : bWinChk 206 10 100000000 1024 rkmPhb_w64_m16_s4a
    294 rkmC_w64_m16_s4a_5 310 rkmC_w64_m16_s4a_6 2103498628 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4a_6 : bWinChk 206 9 100000000 1024 rkmPhb_w64_m16_s4a
    310 rkmC_w64_m16_s4a_6 324 rkmC_w64_m16_s4a_7 1612091341 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4a_7 : bWinChk 206 10 100000000 1024 rkmPhb_w64_m16_s4a
    324 rkmC_w64_m16_s4a_7 340 rkmC_w64_m16_s4a_8 1681347111 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4a_8 : bWinChk 206 9 100000000 1024 rkmPhb_w64_m16_s4a
    340 rkmC_w64_m16_s4a_8 354 rkmC_w64_m16_s4a_9 1704350365 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4a_9 : bWinChk 206 10 100000000 1024 rkmPhb_w64_m16_s4a
    354 rkmC_w64_m16_s4a_9 369 rkmC_w64_m16_s4a_10 1909943631 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4a_10 : bWinChk 206 10 100000000 1024 rkmPhb_w64_m16_s4a
    369 rkmC_w64_m16_s4a_10 383 rkmC_w64_m16_s4a_11 2005802783 = true := by decide +kernel
private theorem rkmWC_w64_m16_s4a_11 : bWinChk 206 9 100000000 1024 rkmPhb_w64_m16_s4a
    383 rkmC_w64_m16_s4a_11 397 rkmXsWin_w64_m16_s4a_out 1760980816 = true := by decide +kernel
/-- Certified `w64_m16_s4a` partial walk (`114` substeps). -/
theorem rkmWinIterSnd_w64_m16_s4a :
    RkmWinIterSound 114 1024 rkmHbWin_w64_m16_s4a 222 rkmXsWin_w64_m16_s4a_in
      397 rkmXsWin_w64_m16_s4a_out 22005929368 :=
  rkmChS 114 22005929368 (rkmChS 105 20244948552 (rkmChS 95 18239145769 (rkmChS 85 16329202138
    (rkmChS 76 14624851773 (rkmChS 66 12943504662 (rkmChS 57 11331413321 (rkmChS 47 9227914693
    (rkmChS 38 7469797390 (rkmChS 29 5612902002 (rkmChS 19 3718930779 (bWinChk_sound
    rkmHhb_w64_m16_s4a rkmWC_w64_m16_s4a_0) rkmHhb_w64_m16_s4a rkmWC_w64_m16_s4a_1 rfl rfl)
    rkmHhb_w64_m16_s4a rkmWC_w64_m16_s4a_2 rfl rfl) rkmHhb_w64_m16_s4a rkmWC_w64_m16_s4a_3 rfl
    rfl) rkmHhb_w64_m16_s4a rkmWC_w64_m16_s4a_4 rfl rfl) rkmHhb_w64_m16_s4a rkmWC_w64_m16_s4a_5
    rfl rfl) rkmHhb_w64_m16_s4a rkmWC_w64_m16_s4a_6 rfl rfl) rkmHhb_w64_m16_s4a
    rkmWC_w64_m16_s4a_7 rfl rfl) rkmHhb_w64_m16_s4a rkmWC_w64_m16_s4a_8 rfl rfl)
    rkmHhb_w64_m16_s4a rkmWC_w64_m16_s4a_9 rfl rfl) rkmHhb_w64_m16_s4a rkmWC_w64_m16_s4a_10 rfl
    rfl) rkmHhb_w64_m16_s4a rkmWC_w64_m16_s4a_11 rfl rfl
/-- Cumulative `w64_m16` part `0` lane witness. -/
theorem rkmHiLane_w64_m16_wint0 :
    @rkmWinIterSnd_w64_m16_s4a = @rkmWinIterSnd_w64_m16_s4a := rfl
/-- Module lane witness for `FindAllJohnsonRampKickMuxHiW64T04`. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T04 :
    @rkmHiLane_w64_m16_wint0 = @rkmHiLane_w64_m16_wint0 := rfl

end
end QuantumComputation.Specs.DickeSol
