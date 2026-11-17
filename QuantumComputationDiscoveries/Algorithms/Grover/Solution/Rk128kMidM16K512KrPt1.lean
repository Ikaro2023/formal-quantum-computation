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

public import QuantumComputationDiscoveries.Algorithms.Grover.Solution.Rk128kEngine

/-
# `(16, 512)` `degP <= 64` Krotov `RampKick128k` Part 1 (`Rk128kMidM16K512KrPt1`)

Certifies Slice 1 (`r = 512` segments `60..81`, `22` segments, `442,880` F1272 /
`443,745 <= 450,000` Horner coord-ops, `dk = 15`, `lTableMax = 62`).
-/

namespace QuantumComputation.Specs.GroverFindAll.Rk128kMidM16K512KrPt1

@[expose] public section

open QuantumComputation.Specs.DickeSol

/-- Segments `60..81` (`22` segments) of `(16, 512)` `r = 512` at `lTableMax = 62`. -/
def mm16k512krS1Segs : List Rkm128kSeg := [
  ⟨34, 272815, 1, 25,
    rkm128kMask56 513 [7038196426790176, 72044846647603436, 69121212411101970,
      28154851683230928, 424009, 2147483648, 34359738368, 4785289369223168,
      30351093929098516, 498]⟩,
  ⟨34, 274345, 1, 25,
    rkm128kMask56 512 [62518920362332719, 69004833376630400, 7030002368984270,
      1400911742612537, 13531174, 274877906944, 8589934592, 22519372530712576,
      30225870561939780, 148]⟩,
  ⟨35, 274309, 1, 25,
    rkm128kMask56 512 [59025608730005453, 41086070931666285, 12787548560949292,
      65373205667028992, 402688128, 4294967344, 2251868533309440, 4524490348298240,
      4657482350605377, 214]⟩,
  ⟨35, 274005, 1, 25,
    rkm128kMask56 509 [43217020171870976, 70870177517732106, 13590854171885400,
      25318421168378783, 13709390722, 68719476736, 563224831328256, 19421790572904448,
      43706761318370304, 30]⟩,
  ⟨35, 274537, 1, 25,
    rkm128kMask56 513 [67429127057702827, 68464022942129319, 25364275537556999,
      9017104634311364, 490188591874, 274877906944, 8405056, 5981364729937920,
      59124601199822852, 346]⟩,
  ⟨35, 274274, 1, 25,
    rkm128kMask56 513 [67797429776431156, 23564849216767732, 23071216010481817,
      26241394524664343, 16694307437301, 68720459776, 70385924046848, 5717460464435200,
      23775125740494848, 316]⟩,
  ⟨36, 269812, 1, 25,
    rkm128kMask56 513 [27860769573619006, 37261627381495413, 54747398997717269,
      27784736415689740, 259623262553092, 140737519812608, 17596481013760, 19444038771998728,
      40073319438196752, 384]⟩,
  ⟨36, 272877, 1, 26,
    rkm128kMask56 512 [440159145027906, 38038820213463884, 12224770785096449,
      7156957598135339, 7269190128896588, 4398046511104, 0, 351912440367106,
      10226290296883236, 165]⟩,
  ⟨38, 266270, 1, 26,
    rkm128kMask56 513 [51912090942769507, 1407683107572482, 43353425745559166,
      12658824054887127, 41539549301679780, 2, 17825792, 17609386885120, 55040136167621132,
      365]⟩,
  ⟨39, 258991, 1, 26,
    rkm128kMask56 513 [52365828311900675, 39376873913974035, 48482145123490915,
      15651308596695855, 1093889086594423, 103079215216, 0, 18018796555993088,
      45200529223598216, 274]⟩,
  ⟨40, 484516, 2, 25,
    rkm128kMask56 512 [4048740444792636, 29058416612529463, 55862455464018918,
      50384291549060144, 36890815327367171, 57870, 0, 292059939968, 12112804815339776, 178]⟩,
  ⟨40, 483887, 2, 25,
    rkm128kMask56 513 [58828259257177647, 64482235140802663, 20608937507145761,
      32649361874858215, 30651486412217554, 13510798915550061, 18014407367917572,
      281474976743426, 35047115810940928, 271]⟩,
  ⟨42, 477636, 2, 26,
    rkm128kMask56 508 [71341588533344929, 8440469917563357, 53963969592486793,
      25051567895872254, 28597177400451220, 16931881216, 33555464, 4398131449920,
      66195513971572737, 10]⟩,
  ⟨43, 470100, 2, 25,
    rkm128kMask56 513 [18638413233421714, 65438283797105871, 46734373981461658,
      60705755969556977, 48773678521087356, 7895127955786, 35184372088832, 2268833513536,
      64010683438137376, 434]⟩,
  ⟨44, 457870, 2, 25,
    rkm128kMask56 513 [1131368900149566, 45165977623756775, 58986064439594635,
      36325146558013640, 18440668081036562, 1902164826539852, 2147483648, 38352099448471617,
      11307657289797634, 491]⟩,
  ⟨45, 459861, 2, 26,
    rkm128kMask56 513 [59755844727409440, 6863365352161313, 66582816662939891,
      24370941644808560, 440413207969802, 23579892077168301, 68719476751, 2291450951761920,
      14944716705497345, 449]⟩,
  ⟨45, 462900, 2, 26,
    rkm128kMask56 513 [5630066949828967, 2989589844723695, 57836502301326801,
      2211172383006529, 68937979147617832, 39266042731414082, 137438956688, 8594147329,
      106137240208000, 387]⟩,
  ⟨46, 455855, 2, 26,
    rkm128kMask56 513 [37143755505236202, 22506039873403927, 3304932513817555,
      61952516603908371, 45401045497845769, 67410325744126829, 52776559986194,
      4574522426605568, 13793442358886432, 307]⟩,
  ⟨47, 451038, 2, 26,
    rkm128kMask56 512 [56552299585145308, 54342777590969521, 34849304782812467,
      36484553176549280, 4225219613042561, 43986008391286804, 13510799354582344,
      36028797019226368, 45124232100708354, 226]⟩,
  ⟨52, 408878, 2, 25,
    rkm128kMask56 513 [18669980376434120, 67756081256123842, 16433608817782940,
      33803412874722298, 55407190583562087, 30608521527855512, 71028539425, 562949962072356,
      70245737397092352, 418]⟩,
  ⟨53, 415334, 2, 26,
    rkm128kMask56 513 [57422354506437903, 42834703015114655, 25582814774949072,
      61790354949549444, 7961427439984729, 567533162471427, 17732646486098, 9007199254773760,
      68187622345809928, 308]⟩,
  ⟨53, 413316, 2, 25,
    rkm128kMask56 511 [4194689690277124, 9784813786623887, 5330016093718096,
      5644720368650000, 8443250185702349, 67359849242530030, 8494683617750088,
      562949970722816, 11276591254474752, 98]⟩]

/-- Input multiplexing factor entering `mm16k512krS1Segs` (`34`). -/
def mm16k512krS1LIn : ℕ := 34

/-- Input Hilbert dimension entering `mm16k512krS1Segs` (`512`). -/
def mm16k512krS1DCurIn : ℕ := 512

/-- Input accumulated `10^15`-scale error pad entering `mm16k512krS1Segs`. -/
def mm16k512krS1PadIn : ℕ := 575422661

/-- Slice `0` (`64` entries) of `mm16k512krS1VecIn`. -/
def mm16k512krS1VecIn0 : List ℤ :=
  [Int.ofNat 277838162, Int.ofNat 313063736, Int.ofNat 191456390, Int.negSucc 692207758,
   Int.negSucc 260460961, Int.negSucc 119540860, Int.negSucc 240497313, Int.negSucc 284912154,
   Int.negSucc 1031108560, Int.negSucc 1588701012, Int.ofNat 2456421242, Int.ofNat 548796708,
   Int.ofNat 2541338054, Int.negSucc 3714468768, Int.ofNat 5777932682, Int.ofNat 3685040260,
   Int.ofNat 3650304320, Int.negSucc 5935348734, Int.negSucc 3584325492, Int.ofNat 2559878506,
   Int.ofNat 4252358174, Int.ofNat 2568794583, Int.ofNat 3430795035, Int.ofNat 2333936855,
   Int.ofNat 4434937189, Int.ofNat 2098873564, Int.ofNat 2500197156, Int.ofNat 4129318088,
   Int.ofNat 10534432479, Int.ofNat 38397467712, Int.ofNat 26332751329, Int.ofNat 14640977120,
   Int.negSucc 7991247457, Int.negSucc 13405677153, Int.negSucc 1619187255,
   Int.negSucc 2722463364, Int.ofNat 4195786934, Int.ofNat 30115499345,
   Int.negSucc 14334030523, Int.ofNat 4993616639, Int.ofNat 11232355909, Int.ofNat 29473211656,
   Int.ofNat 27395185103, Int.ofNat 14363991972, Int.negSucc 7637454655,
   Int.negSucc 14888247959, Int.ofNat 369981897, Int.negSucc 12882179175,
   Int.negSucc 27217536135, Int.negSucc 17437006492, Int.ofNat 22941940811,
   Int.ofNat 11745323065, Int.ofNat 42538696673, Int.ofNat 11415566016, Int.ofNat 18380982949,
   Int.ofNat 5964431122, Int.ofNat 13015401370, Int.ofNat 2066722572, Int.ofNat 12799572246,
   Int.negSucc 4007663555, Int.negSucc 2172643228, Int.negSucc 53151712971,
   Int.negSucc 90858186354, Int.negSucc 58128529921]
/-- Slice `1` (`64` entries) of `mm16k512krS1VecIn`. -/
def mm16k512krS1VecIn1 : List ℤ :=
  [Int.ofNat 25841141155, Int.ofNat 34697692996, Int.negSucc 5972336697, Int.ofNat 35823674019,
   Int.ofNat 8035777055, Int.ofNat 64711124042, Int.ofNat 62819489297, Int.ofNat 72194531253,
   Int.ofNat 129456496101, Int.ofNat 102385250521, Int.ofNat 25241447780,
   Int.ofNat 31807137410, Int.ofNat 56635786568, Int.negSucc 39243539075,
   Int.negSucc 113120414153, Int.negSucc 185703942612, Int.negSucc 208598619071,
   Int.negSucc 107318291796, Int.negSucc 45504926679, Int.ofNat 7704462980,
   Int.ofNat 62850790734, Int.ofNat 45270199241, Int.ofNat 63300580529, Int.ofNat 69163139072,
   Int.negSucc 71472582613, Int.negSucc 75978816896, Int.negSucc 79201972096,
   Int.negSucc 31699967214, Int.negSucc 26812213939, Int.negSucc 13582503368,
   Int.ofNat 34046364012, Int.negSucc 118712466204, Int.ofNat 12853839300,
   Int.negSucc 56104062368, Int.negSucc 3037928584, Int.ofNat 51996040407,
   Int.ofNat 267912952623, Int.ofNat 220299287446, Int.ofNat 138364274076,
   Int.negSucc 82210644212, Int.negSucc 16879774137, Int.negSucc 152614962394,
   Int.negSucc 70618288518, Int.ofNat 76380926871, Int.ofNat 123140460410,
   Int.ofNat 76516477841, Int.negSucc 60991691884, Int.ofNat 34828432483,
   Int.negSucc 27726522677, Int.ofNat 10827392245, Int.negSucc 40203705029,
   Int.negSucc 137814796177, Int.negSucc 51434602100, Int.ofNat 141817805374,
   Int.negSucc 7431652883, Int.negSucc 69703491731, Int.negSucc 221760167546,
   Int.negSucc 267637204255, Int.negSucc 414052436802, Int.negSucc 150178256130,
   Int.negSucc 99300274301, Int.negSucc 10740370738, Int.ofNat 233703178142,
   Int.negSucc 199698888072]
/-- Slice `2` (`64` entries) of `mm16k512krS1VecIn`. -/
def mm16k512krS1VecIn2 : List ℤ :=
  [Int.negSucc 247914056312, Int.negSucc 38044586484, Int.ofNat 585528621120,
   Int.ofNat 361946915085, Int.ofNat 160900145133, Int.ofNat 35139125470,
   Int.ofNat 246253180126, Int.ofNat 166768360553, Int.negSucc 224139158536,
   Int.ofNat 237950948608, Int.ofNat 153718441192, Int.negSucc 41829876652,
   Int.negSucc 232555829976, Int.negSucc 191603321702, Int.ofNat 490816602022,
   Int.ofNat 901382590003, Int.ofNat 693966275501, Int.ofNat 61129649120, Int.ofNat 849015267,
   Int.ofNat 216176692450, Int.ofNat 292555747793, Int.negSucc 163193459551,
   Int.negSucc 168352725476, Int.ofNat 385765904172, Int.negSucc 311806016583,
   Int.ofNat 240370434490, Int.ofNat 810559067582, Int.negSucc 589282914862,
   Int.negSucc 485588515962, Int.negSucc 642702969407, Int.negSucc 127360146296,
   Int.negSucc 296083823236, Int.negSucc 657968050641, Int.ofNat 149231628951,
   Int.negSucc 23902031630, Int.negSucc 782726559891, Int.negSucc 309567606773,
   Int.negSucc 1345366576614, Int.ofNat 685766377673, Int.ofNat 611882997123,
   Int.ofNat 3273213836246, Int.negSucc 2833376849293, Int.negSucc 2494299837278,
   Int.ofNat 1471555323617, Int.ofNat 1101684253757, Int.negSucc 1885950351816,
   Int.negSucc 2105236526273, Int.ofNat 839926952289, Int.negSucc 231186189334,
   Int.ofNat 1729491085439, Int.ofNat 1153471083828, Int.ofNat 1373571191487,
   Int.negSucc 1912527390379, Int.negSucc 2122019649952, Int.negSucc 1062768459461,
   Int.negSucc 1279613296988, Int.ofNat 714159093209, Int.negSucc 1093184606430,
   Int.negSucc 1963424874183, Int.negSucc 430509295924, Int.negSucc 1551009309904,
   Int.ofNat 1314033851473, Int.ofNat 1246271704711, Int.ofNat 979538318398]
/-- Slice `3` (`64` entries) of `mm16k512krS1VecIn`. -/
def mm16k512krS1VecIn3 : List ℤ :=
  [Int.ofNat 2562102245391, Int.negSucc 1891042993883, Int.negSucc 978115676185,
   Int.negSucc 2028697571531, Int.ofNat 42106121375, Int.ofNat 431433575448,
   Int.negSucc 478359185129, Int.ofNat 1204232392974, Int.ofNat 1643216584974,
   Int.ofNat 2028873793982, Int.negSucc 468145542686, Int.negSucc 421185142659,
   Int.ofNat 1964530751045, Int.negSucc 497591885097, Int.ofNat 415189036671,
   Int.ofNat 1162117235990, Int.ofNat 1816751202205, Int.ofNat 2005289198736,
   Int.ofNat 142171760030, Int.negSucc 1155724561408, Int.negSucc 2515620243542,
   Int.negSucc 1014077793925, Int.negSucc 4066698396431, Int.ofNat 2885191292440,
   Int.negSucc 3953560569991, Int.negSucc 3867311950990, Int.ofNat 591282561562,
   Int.ofNat 2315372090943, Int.negSucc 269816618455, Int.ofNat 2355936566347,
   Int.negSucc 1527899194475, Int.negSucc 654137878815, Int.ofNat 3123290693741,
   Int.ofNat 1157034944941, Int.negSucc 1394059880090, Int.negSucc 3042549855713,
   Int.ofNat 693731142846, Int.negSucc 1660028544241, Int.negSucc 354784640837,
   Int.ofNat 1042435961696, Int.negSucc 2801958920884, Int.negSucc 1363281058788,
   Int.ofNat 2547226393455, Int.ofNat 3199907290867, Int.ofNat 412262785527,
   Int.ofNat 3803126457234, Int.ofNat 1001752186788, Int.ofNat 11719842563934,
   Int.ofNat 34270242493146, Int.ofNat 64750227828257, Int.ofNat 101634519629181,
   Int.ofNat 143048588149148, Int.ofNat 185704166202740, Int.ofNat 225851421665350,
   Int.ofNat 260506125795239, Int.ofNat 287465696214811, Int.ofNat 305200563553530,
   Int.ofNat 313215421077015, Int.ofNat 312165884606858, Int.ofNat 302885499670064,
   Int.ofNat 286573006431093, Int.ofNat 263669277609053, Int.ofNat 237129845662785,
   Int.ofNat 207315424316950]
/-- Slice `4` (`64` entries) of `mm16k512krS1VecIn`. -/
def mm16k512krS1VecIn4 : List ℤ :=
  [Int.ofNat 178728479994338, Int.ofNat 150357749877609, Int.ofNat 124478756858446,
   Int.ofNat 101700702972394, Int.ofNat 80898493217399, Int.ofNat 63257248047356,
   Int.ofNat 49078313505459, Int.ofNat 37092948634377, Int.ofNat 27007489196216,
   Int.ofNat 19282859584859, Int.ofNat 13684510271006, Int.ofNat 9448008159576,
   Int.ofNat 6108719262640, Int.ofNat 3618304665322, Int.ofNat 1980532122505,
   Int.ofNat 1045889167885, Int.ofNat 571438529337, Int.ofNat 342275727002,
   Int.ofNat 224723616840, Int.ofNat 154208057579, Int.ofNat 106782186304,
   Int.ofNat 71382524868, Int.ofNat 48324397774, Int.ofNat 30277919323, Int.ofNat 18842124770,
   Int.ofNat 12437688437, Int.ofNat 7601883509, Int.ofNat 3862858328, Int.ofNat 1692260699,
   Int.ofNat 763574954, Int.ofNat 425636036, Int.ofNat 275637528, Int.ofNat 177674928,
   Int.ofNat 107134332, Int.ofNat 60432243, Int.ofNat 32413799, Int.ofNat 16787445,
   Int.ofNat 8483650, Int.ofNat 4208730, Int.ofNat 2056087, Int.ofNat 990595, Int.ofNat 470979,
   Int.ofNat 221033, Int.ofNat 102388, Int.ofNat 46803, Int.ofNat 21098, Int.ofNat 9373,
   Int.ofNat 4092, Int.ofNat 1748, Int.ofNat 727, Int.ofNat 291, Int.ofNat 108, Int.ofNat 37,
   Int.ofNat 10, Int.ofNat 2, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0]
/-- Slice `5` (`64` entries) of `mm16k512krS1VecIn`. -/
def mm16k512krS1VecIn5 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Slice `6` (`64` entries) of `mm16k512krS1VecIn`. -/
def mm16k512krS1VecIn6 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Slice `7` (`64` entries) of `mm16k512krS1VecIn`. -/
def mm16k512krS1VecIn7 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Slice `8` (`1` entries) of `mm16k512krS1VecIn`. -/
def mm16k512krS1VecIn8 : List ℤ :=
  [Int.ofNat 0]
/-- Checkpoint fixed-point vector entering `mm16k512krS1Segs` (`513` entries). -/
def mm16k512krS1VecIn : List ℤ :=
  mm16k512krS1VecIn0 ++ (
    mm16k512krS1VecIn1 ++ (
      mm16k512krS1VecIn2 ++ (
        mm16k512krS1VecIn3 ++ (
          mm16k512krS1VecIn4 ++ (
          mm16k512krS1VecIn5 ++ (
          mm16k512krS1VecIn6 ++ (
          mm16k512krS1VecIn7 ++ (
          mm16k512krS1VecIn8))))))))

/-- Output multiplexing factor exiting `mm16k512krS1Segs` (`53`). -/
def mm16k512krS1LOut : ℕ := 53

/-- Output Hilbert dimension exiting `mm16k512krS1Segs` (`512`). -/
def mm16k512krS1DCurOut : ℕ := 512

/-- Output accumulated `10^15`-scale error pad exiting `mm16k512krS1Segs`. -/
def mm16k512krS1PadOut : ℕ := 766172526

/-- Slice `0` (`64` entries) of `mm16k512krS1Vec`. -/
def mm16k512krS1Vec0 : List ℤ :=
  [Int.negSucc 25879693, Int.ofNat 72302561, Int.ofNat 302827352, Int.ofNat 80866118,
   Int.ofNat 25272983, Int.negSucc 20026342, Int.ofNat 174141308, Int.ofNat 198240811,
   Int.negSucc 400504222, Int.ofNat 367412143, Int.ofNat 340777222, Int.negSucc 64467009,
   Int.ofNat 62572563, Int.ofNat 161132744, Int.negSucc 288565870, Int.negSucc 63053385,
   Int.negSucc 588216700, Int.negSucc 665824020, Int.negSucc 529124939, Int.negSucc 1294052884,
   Int.negSucc 446461827, Int.negSucc 166959537, Int.negSucc 539036513, Int.ofNat 888155494,
   Int.ofNat 196128916, Int.ofNat 21303913, Int.ofNat 532844710, Int.ofNat 1663436096,
   Int.negSucc 513484361, Int.negSucc 1192359653, Int.ofNat 392722766, Int.negSucc 1454406145,
   Int.ofNat 1145293294, Int.negSucc 1902417168, Int.negSucc 111285210, Int.negSucc 558878905,
   Int.ofNat 577019539, Int.ofNat 548187097, Int.ofNat 733090200, Int.negSucc 1899567147,
   Int.ofNat 392266505, Int.ofNat 494108643, Int.ofNat 885939801, Int.ofNat 130620156,
   Int.ofNat 846957387, Int.negSucc 1634323621, Int.negSucc 3568743729, Int.negSucc 1394510646,
   Int.ofNat 3343578380, Int.ofNat 550462062, Int.ofNat 2800682767, Int.negSucc 766981676,
   Int.negSucc 544589802, Int.negSucc 2361650112, Int.negSucc 1949426764,
   Int.negSucc 1507495962, Int.negSucc 1507736008, Int.negSucc 286969355,
   Int.negSucc 1038798983, Int.negSucc 465929300, Int.negSucc 1778791841, Int.ofNat 2074143420,
   Int.ofNat 850838557, Int.ofNat 4156467137]
/-- Slice `1` (`64` entries) of `mm16k512krS1Vec`. -/
def mm16k512krS1Vec1 : List ℤ :=
  [Int.ofNat 4373765632, Int.ofNat 4389373292, Int.ofNat 2744515139, Int.ofNat 9279907265,
   Int.ofNat 7290130345, Int.ofNat 6099170927, Int.ofNat 5170679388, Int.ofNat 2785242567,
   Int.ofNat 2887272669, Int.ofNat 316362050, Int.negSucc 6843361280, Int.negSucc 3643478525,
   Int.negSucc 16045256731, Int.negSucc 9849158550, Int.negSucc 6840160012,
   Int.negSucc 3660573105, Int.negSucc 623274924, Int.ofNat 781563984, Int.ofNat 3474971329,
   Int.ofNat 4018062952, Int.ofNat 2473327445, Int.ofNat 2825696973, Int.ofNat 9664907928,
   Int.negSucc 1308051676, Int.negSucc 7673077410, Int.negSucc 15271108266,
   Int.ofNat 2238829364, Int.ofNat 3265085147, Int.negSucc 6584129039, Int.negSucc 1788088998,
   Int.negSucc 10543498634, Int.negSucc 2077407206, Int.negSucc 462340633,
   Int.negSucc 12314885650, Int.negSucc 7019187178, Int.ofNat 21969295619,
   Int.ofNat 9536745431, Int.negSucc 8213866598, Int.ofNat 2180674412, Int.ofNat 21402171779,
   Int.ofNat 20259663565, Int.ofNat 26580912891, Int.ofNat 17582608859, Int.ofNat 765949697,
   Int.negSucc 7531494008, Int.negSucc 12487013845, Int.negSucc 29722597059,
   Int.negSucc 20872200889, Int.negSucc 22822351388, Int.negSucc 20343994231,
   Int.negSucc 24929982667, Int.ofNat 21247647504, Int.ofNat 8662860999,
   Int.negSucc 36474107800, Int.negSucc 54290483365, Int.ofNat 14502705246,
   Int.ofNat 8026539910, Int.negSucc 66536404823, Int.negSucc 75705891109,
   Int.ofNat 4873241486, Int.ofNat 7216252393, Int.ofNat 293204369, Int.ofNat 55621650752,
   Int.ofNat 35470741005]
/-- Slice `2` (`64` entries) of `mm16k512krS1Vec`. -/
def mm16k512krS1Vec2 : List ℤ :=
  [Int.ofNat 37292563637, Int.ofNat 6342535829, Int.ofNat 5990368225, Int.negSucc 15417563475,
   Int.ofNat 11993549274, Int.negSucc 5383963853, Int.ofNat 46187293777, Int.ofNat 72688367523,
   Int.ofNat 162890830094, Int.negSucc 53217378131, Int.negSucc 54708581831,
   Int.negSucc 28549953243, Int.ofNat 4794090720, Int.ofNat 33351216522, Int.ofNat 65863362166,
   Int.ofNat 95932003394, Int.ofNat 14626926904, Int.negSucc 29565957215,
   Int.negSucc 6359171931, Int.negSucc 61158059979, Int.ofNat 31289806181,
   Int.negSucc 23080654976, Int.negSucc 104467733235, Int.negSucc 62874234254,
   Int.negSucc 54827172808, Int.negSucc 112111161336, Int.negSucc 121944301037,
   Int.negSucc 61729752268, Int.negSucc 20042599123, Int.negSucc 115619239547,
   Int.negSucc 84812515690, Int.negSucc 56102612390, Int.negSucc 143461329353,
   Int.negSucc 4058905607, Int.negSucc 7872244954, Int.negSucc 97165716255,
   Int.negSucc 16543999177, Int.ofNat 19382054205, Int.ofNat 189477263489,
   Int.ofNat 118831620199, Int.ofNat 4892804488, Int.ofNat 44902737353, Int.negSucc 3204553835,
   Int.ofNat 112030301128, Int.ofNat 93756511734, Int.ofNat 27373162890,
   Int.negSucc 105698353370, Int.ofNat 151943742821, Int.ofNat 143198596450,
   Int.ofNat 6508992110, Int.ofNat 158318735569, Int.ofNat 350998841735,
   Int.ofNat 185971644824, Int.ofNat 19877085072, Int.ofNat 125541688962,
   Int.negSucc 45266635465, Int.negSucc 62497053381, Int.negSucc 13687627655,
   Int.negSucc 90650392673, Int.ofNat 53765305699, Int.ofNat 73119240699,
   Int.ofNat 12669313268, Int.ofNat 68482214729, Int.ofNat 225235014556]
/-- Slice `3` (`64` entries) of `mm16k512krS1Vec`. -/
def mm16k512krS1Vec3 : List ℤ :=
  [Int.ofNat 269479829593, Int.ofNat 206973890928, Int.ofNat 423380420318,
   Int.ofNat 652788862827, Int.ofNat 313734913936, Int.negSucc 1446511582,
   Int.negSucc 318561050062, Int.negSucc 276346511223, Int.negSucc 145134043386,
   Int.ofNat 76069665618, Int.ofNat 146519497531, Int.ofNat 100312617706,
   Int.negSucc 377812479452, Int.ofNat 187221698967, Int.ofNat 84954317302,
   Int.negSucc 181674047744, Int.ofNat 1086642387, Int.negSucc 130728473178,
   Int.ofNat 64603983386, Int.negSucc 56253981412, Int.negSucc 75022231832,
   Int.negSucc 428676604683, Int.negSucc 387711955554, Int.negSucc 121230517025,
   Int.negSucc 354736557982, Int.negSucc 293691326672, Int.negSucc 238913622777,
   Int.negSucc 74729018683, Int.negSucc 12134496667, Int.ofNat 827214750210,
   Int.ofNat 1250932931808, Int.ofNat 1048129860879, Int.negSucc 532937490469,
   Int.negSucc 815915116690, Int.negSucc 254235453753, Int.ofNat 524272162145,
   Int.ofNat 512219126487, Int.negSucc 267091698843, Int.ofNat 426331120050,
   Int.ofNat 271422660316, Int.ofNat 493137787732, Int.ofNat 1031428888087,
   Int.ofNat 695060604356, Int.negSucc 750087244320, Int.negSucc 1551295607366,
   Int.negSucc 937266675485, Int.negSucc 401079949489, Int.ofNat 695445302969,
   Int.ofNat 205891570441, Int.ofNat 734539336106, Int.ofNat 1789734504502,
   Int.ofNat 1467099273931, Int.ofNat 1629438897199, Int.negSucc 1868167632,
   Int.negSucc 763633471331, Int.negSucc 1170096894630, Int.negSucc 229578330218,
   Int.negSucc 712164314848, Int.negSucc 1718088166600, Int.negSucc 961190269588,
   Int.negSucc 955899029316, Int.negSucc 687060256608, Int.negSucc 563317313731,
   Int.ofNat 420482846946]
/-- Slice `4` (`64` entries) of `mm16k512krS1Vec`. -/
def mm16k512krS1Vec4 : List ℤ :=
  [Int.negSucc 918140897422, Int.negSucc 337852638481, Int.ofNat 1052756767971,
   Int.negSucc 1435632478630, Int.ofNat 2394151648889, Int.negSucc 561597991948,
   Int.ofNat 15583868837, Int.ofNat 273470782435, Int.ofNat 2949918571337,
   Int.ofNat 2260281735930, Int.ofNat 3788686954898, Int.ofNat 4929914887712,
   Int.ofNat 5956907528206, Int.ofNat 5638811895903, Int.ofNat 7140337634752,
   Int.ofNat 5094501594438, Int.ofNat 1425050566877, Int.negSucc 2194023199414,
   Int.negSucc 3305700865289, Int.negSucc 514813936386, Int.ofNat 1876532230353,
   Int.ofNat 4902148847012, Int.negSucc 1192516254386, Int.negSucc 3428061754753,
   Int.negSucc 1642328096057, Int.ofNat 3278637144433, Int.ofNat 1750927471948,
   Int.negSucc 298386635526, Int.ofNat 3255925494617, Int.ofNat 1374218147441,
   Int.ofNat 822779703833, Int.ofNat 2155286016893, Int.ofNat 443218472259,
   Int.negSucc 3447430930905, Int.negSucc 4628601268842, Int.negSucc 5607127731747,
   Int.ofNat 1932319968013, Int.negSucc 5062507137493, Int.negSucc 7899615180620,
   Int.ofNat 475929498025, Int.ofNat 4145033748648, Int.negSucc 3513302276931,
   Int.ofNat 828541958811, Int.negSucc 541913035454, Int.ofNat 1517518504476,
   Int.ofNat 496591790056, Int.ofNat 2211891413379, Int.negSucc 1356423787830,
   Int.ofNat 1314490778958, Int.ofNat 257438138489, Int.negSucc 983827547911,
   Int.ofNat 3302253225153, Int.negSucc 1563062559160, Int.negSucc 2054720096341,
   Int.ofNat 560771949967, Int.ofNat 308477285868, Int.ofNat 1722161873101,
   Int.negSucc 3148316033340, Int.negSucc 996553767950, Int.negSucc 4333691642175,
   Int.negSucc 3076277110373, Int.negSucc 5044436793862, Int.negSucc 8894729157042,
   Int.negSucc 2023267502786]
/-- Slice `5` (`64` entries) of `mm16k512krS1Vec`. -/
def mm16k512krS1Vec5 : List ℤ :=
  [Int.negSucc 2462215482162, Int.negSucc 203249979460, Int.negSucc 4238728406914,
   Int.negSucc 8920625283100, Int.negSucc 2985335652316, Int.negSucc 372294917992,
   Int.negSucc 3644791394047, Int.negSucc 5776689455272, Int.negSucc 1802458491927,
   Int.negSucc 1433964799966, Int.negSucc 701965266328, Int.negSucc 2252818823709,
   Int.ofNat 1556032958576, Int.negSucc 3261792852871, Int.ofNat 2826830253179,
   Int.ofNat 8195250363877, Int.ofNat 2270406058845, Int.ofNat 2201344110751,
   Int.ofNat 913851528279, Int.ofNat 2348343377549, Int.negSucc 5791522246882,
   Int.negSucc 5888362287085, Int.ofNat 1149831025247, Int.ofNat 1331977909508,
   Int.negSucc 7441028864106, Int.negSucc 2890906893059, Int.ofNat 1217102592044,
   Int.negSucc 3593547027501, Int.ofNat 78162368983, Int.negSucc 1501886840263,
   Int.negSucc 6229131183906, Int.ofNat 8103700048598, Int.ofNat 440111648933,
   Int.ofNat 5222674298201, Int.ofNat 6479387984162, Int.negSucc 2336399575011,
   Int.negSucc 2767141645561, Int.ofNat 39649878087, Int.ofNat 9344012674431,
   Int.negSucc 277729520519, Int.negSucc 10901527359506, Int.negSucc 10235788687059,
   Int.negSucc 3607661976826, Int.ofNat 1540920300565, Int.negSucc 5557435635053,
   Int.ofNat 2423013138900, Int.ofNat 1881063870353, Int.negSucc 7313463015712,
   Int.negSucc 2613666042436, Int.ofNat 8982347724771, Int.negSucc 1864730597446,
   Int.negSucc 3244229229463, Int.negSucc 5312937613207, Int.negSucc 6726432485182,
   Int.negSucc 6011355413072, Int.negSucc 3078297341094, Int.ofNat 714625130028,
   Int.ofNat 7535492113259, Int.ofNat 3663939223110, Int.ofNat 2441577729335,
   Int.negSucc 7688432236935, Int.negSucc 10893868406251, Int.ofNat 3436324024320,
   Int.ofNat 2175738572027]
/-- Slice `6` (`64` entries) of `mm16k512krS1Vec`. -/
def mm16k512krS1Vec6 : List ℤ :=
  [Int.ofNat 4800297337879, Int.ofNat 8045934483837, Int.ofNat 11840778362435,
   Int.ofNat 17378990691540, Int.ofNat 13203615535948, Int.ofNat 28767599273990,
   Int.ofNat 84487678228397, Int.ofNat 137595110288649, Int.ofNat 198681384840406,
   Int.ofNat 257386627444608, Int.ofNat 297532687891082, Int.ofNat 324144360472089,
   Int.ofNat 343264284705213, Int.ofNat 347241297471419, Int.ofNat 330409208182523,
   Int.ofNat 300078447549052, Int.ofNat 268337189924752, Int.ofNat 238714983869814,
   Int.ofNat 208227858438842, Int.ofNat 172062325243248, Int.ofNat 131781073661224,
   Int.ofNat 92715276109618, Int.ofNat 59646897775396, Int.ofNat 35273274496653,
   Int.ofNat 19473294696625, Int.ofNat 10148372989077, Int.ofNat 4961781696602,
   Int.negSucc 2242891342579, Int.ofNat 945719822434, Int.ofNat 403913599090,
   Int.ofNat 206520586171, Int.ofNat 135797265020, Int.negSucc 100559899316,
   Int.ofNat 73277790132, Int.ofNat 49795872086, Int.ofNat 31208933246, Int.ofNat 18147732395,
   Int.ofNat 9956263227, Int.ofNat 5286083218, Int.ofNat 2790840678, Int.ofNat 1489715355,
   Int.ofNat 802640393, Int.ofNat 430432043, Int.ofNat 226585402, Int.ofNat 116360276,
   Int.ofNat 58388451, Int.ofNat 28792977, Int.ofNat 14030088, Int.ofNat 6771027,
   Int.ofNat 3232183, Int.ofNat 1520731, Int.ofNat 702558, Int.ofNat 317835, Int.ofNat 140632,
   Int.ofNat 60858, Int.ofNat 25774, Int.ofNat 10685, Int.negSucc 4331, Int.ofNat 1710,
   Int.ofNat 653, Int.ofNat 235, Int.ofNat 76, Int.ofNat 21, Int.ofNat 4]
/-- Slice `7` (`64` entries) of `mm16k512krS1Vec`. -/
def mm16k512krS1Vec7 : List ℤ :=
  [Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0, Int.ofNat 0,
   Int.ofNat 0]
/-- Slice `8` (`1` entries) of `mm16k512krS1Vec`. -/
def mm16k512krS1Vec8 : List ℤ :=
  [Int.ofNat 0]
/-- Checkpoint fixed-point vector exiting `mm16k512krS1Segs` (`513` entries). -/
def mm16k512krS1Vec : List ℤ :=
  mm16k512krS1Vec0 ++ (
    mm16k512krS1Vec1 ++ (
      mm16k512krS1Vec2 ++ (
        mm16k512krS1Vec3 ++ (
          mm16k512krS1Vec4 ++ (
          mm16k512krS1Vec5 ++ (
          mm16k512krS1Vec6 ++ (
          mm16k512krS1Vec7 ++ (
          mm16k512krS1Vec8))))))))

end

public section

open QuantumComputation.Specs.DickeSol

private abbrev s1P : ℕ → ℤ := Int.ofNat
private abbrev s1N : ℕ → ℤ := Int.negSucc
private def s1NatEq (x y : ℕ) : Bool := Bool.and (Nat.ble x y) (Nat.ble y x)
private theorem s1NatEq_eq {x y : ℕ} (h : s1NatEq x y = true) : x = y := by
  unfold s1NatEq at h; rw [Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq] at h; omega
private def s1IntEq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat x, Int.ofNat y => s1NatEq x y
  | Int.negSucc x, Int.negSucc y => s1NatEq x y
  | _, _ => false
private theorem s1IntEq_eq {a b : ℤ} (h : s1IntEq a b = true) : a = b := by
  cases a with
  | ofNat x =>
    cases b with
    | ofNat y => exact congrArg Int.ofNat (s1NatEq_eq h)
    | _ => cases h
  | negSucc x =>
    cases b with
    | ofNat _ => cases h
    | negSucc y => exact congrArg Int.negSucc (s1NatEq_eq h)
private def s1IntListEq (xs ys : List ℤ) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xr, y :: yr => cond (s1IntEq x y) (s1IntListEq xr yr) false
  | _, _ => false
private theorem s1IntListEq_eq {xs ys : List ℤ}
    (h : s1IntListEq xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons _ _ => cases h
  | cons x xr ih =>
    cases ys with
    | nil => cases h
    | cons y yr =>
      dsimp only [s1IntListEq] at h
      cases hxy : s1IntEq x y with
      | false => rw [hxy] at h; cases h
      | true => rw [hxy] at h; exact congrArg₂ List.cons (s1IntEq_eq hxy) (ih h)
private def s1SegStateAt (st : ℕ × ℕ × ℕ × List ℤ) (l d p : ℕ) (v : List ℤ) : Bool :=
  match st with
  | (ls, ds, ps, vs) =>
    Bool.and (s1NatEq ls l)
      (Bool.and (s1NatEq ds d) (Bool.and (s1NatEq ps p) (s1IntListEq vs v)))
private theorem s1SegStateAt_eq {st : ℕ × ℕ × ℕ × List ℤ} {l d p : ℕ} {v : List ℤ}
    (h : s1SegStateAt st l d p v = true) : st = (l, d, p, v) := by
  rcases st with ⟨ls, ds, ps, vs⟩; unfold s1SegStateAt at h; dsimp only at h
  simp only [Bool.and_eq_true] at h; rcases h with ⟨hl, ⟨hd, ⟨hp, hv⟩⟩⟩
  rw [s1NatEq_eq hl, s1NatEq_eq hd, s1NatEq_eq hp, s1IntListEq_eq hv]
private theorem s1Step {b rest : List Rkm128kSeg}
    {l0 p0 l1 p1 l2 p2 : ℕ} {v0 v1 v2 : List ℤ}
    (h1 : s1SegStateAt (rkm128kRunSegs 16 62 512 b l0 512 p0 v0) l1 512 p1 v1 = true)
    (h2 : rkm128kRunSegs 16 62 512 rest l1 512 p1 v1 = (l2, 512, p2, v2)) :
    rkm128kRunSegs 16 62 512 (b ++ rest) l0 512 p0 v0 = (l2, 512, p2, v2) := by
  rw [rkm128kRunSegs_append, s1SegStateAt_eq h1]; exact h2
private def s1B0 : List Rkm128kSeg := mm16k512krS1Segs.take 3
private def s1B1 : List Rkm128kSeg := (mm16k512krS1Segs.drop 3).take 3
private def s1B2 : List Rkm128kSeg := (mm16k512krS1Segs.drop 6).take 3
private def s1B3 : List Rkm128kSeg := (mm16k512krS1Segs.drop 9).take 2
private def s1B4 : List Rkm128kSeg := (mm16k512krS1Segs.drop 11).take 1
private def s1B5 : List Rkm128kSeg := (mm16k512krS1Segs.drop 12).take 1
private def s1B6 : List Rkm128kSeg := (mm16k512krS1Segs.drop 13).take 1
private def s1B7 : List Rkm128kSeg := (mm16k512krS1Segs.drop 14).take 1
private def s1B8 : List Rkm128kSeg := (mm16k512krS1Segs.drop 15).take 1
private def s1B9 : List Rkm128kSeg := (mm16k512krS1Segs.drop 16).take 1
private def s1B10 : List Rkm128kSeg := (mm16k512krS1Segs.drop 17).take 1
private def s1B11 : List Rkm128kSeg := (mm16k512krS1Segs.drop 18).take 1
private def s1B12 : List Rkm128kSeg := (mm16k512krS1Segs.drop 19).take 1
private def s1B13 : List Rkm128kSeg := (mm16k512krS1Segs.drop 20).take 1
private def s1B14 : List Rkm128kSeg := mm16k512krS1Segs.drop 21
private def s1V0S0 : List ℤ :=
  [s1P 181135348, s1P 141303501, s1P 415906065, s1P 258019067, s1N 561260997, s1N 460691970,
   s1N 312857745, s1P 66412869, s1P 1508890445, s1N 2200371792, s1N 1437114828, s1P 3410549705,
   s1P 1992661291, s1P 1609412688, s1P 1782493656, s1P 2301468975, s1N 1418992349,
   s1N 4950761753, s1N 2287085050, s1P 2631067434, s1P 6374420414, s1P 4677371742,
   s1P 651078362, s1P 7691736760, s1P 5151569097, s1P 3658600034, s1P 2707437099,
   s1N 2935852867, s1N 5046582136, s1P 1387645982, s1N 3955909195, s1P 2773466048,
   s1P 6214001812, s1N 4974773048, s1P 6905852491, s1P 2838102668, s1P 6882158751,
   s1P 43339295996, s1P 32250210694, s1N 11548052915, s1P 19692206979, s1P 8081628705,
   s1P 16770381866, s1P 8343002888, s1P 5727987607, s1N 7019673871, s1P 5841597423,
   s1P 11562462318, s1P 15380488932, s1P 40734884407, s1P 33479867475, s1N 4467599467,
   s1P 3001240494, s1P 6038166885, s1N 22318473341, s1N 21284256524, s1P 658152181,
   s1P 8677159600, s1P 15633125438, s1P 10794382378, s1P 11051010623, s1N 14169423439,
   s1N 54199810901, s1N 19875616797]
private def s1V0S1 : List ℤ :=
  [s1N 53439567548, s1N 28942973376, s1P 21681671220, s1P 27383187523, s1N 10981988726,
   s1P 25744668140, s1N 40313549189, s1P 9828038219, s1N 55040072716, s1P 53011226866,
   s1P 120891812881, s1P 83807650262, s1P 23525183456, s1N 59733120827, s1N 170942267208,
   s1N 111032376826, s1N 89326677377, s1N 21474305475, s1P 5393840959, s1P 76139702974,
   s1N 4200769667, s1N 27961094856, s1N 120653490685, s1N 4773814592, s1P 150598718969,
   s1N 18929039753, s1P 79121569695, s1P 116225732294, s1N 182526313137, s1P 67271001477,
   s1P 50397995368, s1N 23931877912, s1N 64763988932, s1N 97430911855, s1P 22628225512,
   s1P 43426057029, s1P 132131269076, s1P 64691080635, s1P 107193018264, s1N 18107602525,
   s1N 130153497062, s1P 23136097665, s1N 97594974865, s1N 104441957317, s1N 104729861084,
   s1N 77352279132, s1N 130931432140, s1P 74326119326, s1P 192748816744, s1P 214523597608,
   s1N 182422587749, s1N 76321642855, s1P 9170694765, s1P 218614007076, s1P 171586176110,
   s1N 121074183978, s1N 69443332192, s1N 220996654393, s1P 20931748995, s1P 65884137005,
   s1P 109167038310, s1N 27262568005, s1N 158049044055, s1N 355501303895]
private def s1V0S2 : List ℤ :=
  [s1N 313585415876, s1N 14667140212, s1P 72729059718, s1N 269687227049, s1N 492859255079,
   s1N 440005189540, s1N 140256457987, s1P 188950909633, s1N 122239430014, s1N 116954186835,
   s1P 61628892129, s1P 143670840909, s1P 313148200386, s1P 287465283442, s1P 45653960446,
   s1N 178882411590, s1N 30659630788, s1N 718934565660, s1P 23064150410, s1N 91453716350,
   s1P 337800569176, s1N 247292545020, s1N 730595311618, s1P 651348690348, s1P 623893557339,
   s1N 732059852345, s1P 346241747597, s1N 611635137269, s1N 949034962268, s1P 649348919,
   s1P 591667863589, s1N 256749275699, s1N 77511912833, s1P 359537131738, s1N 24083408069,
   s1P 884813425810, s1P 1415595674388, s1P 24878322627, s1P 681317591815, s1P 129388346372,
   s1P 269821779216, s1N 1156000251677, s1N 845577949304, s1N 1614629034704, s1N 175328670398,
   s1N 633280584392, s1P 655786577481, s1P 2218088825092, s1P 3117552694451, s1P 2151649441431,
   s1P 1761548598907, s1P 2568342959005, s1P 658608485278, s1N 2454924295506, s1P 139270590831,
   s1N 2388538465129, s1P 2540168437060, s1N 813102157843, s1N 810612131980, s1N 1497390086844,
   s1N 2413975104220, s1P 721939232902, s1P 879293775820, s1P 1427565341647]
private def s1V0S3 : List ℤ :=
  [s1P 937859385872, s1N 1207264696772, s1P 1745513052302, s1P 171561748908, s1P 57779802692,
   s1N 537312042811, s1N 797847747241, s1N 3390045802540, s1N 1808751070114, s1N 1477500828219,
   s1N 780721800524, s1P 1467075050637, s1P 264871637622, s1P 599154260001, s1P 2227770622994,
   s1P 240106880094, s1P 1755651804340, s1N 883359776940, s1P 1448181661017, s1P 984307879796,
   s1N 3363566484721, s1N 668294855911, s1N 401178589285, s1P 2374459774858, s1P 3193220457197,
   s1N 1610491068636, s1N 1483679400438, s1P 874587876716, s1P 4900056451463,
   s1N 2605321405942, s1N 1100251076802, s1N 4245014657407, s1N 813224534216,
   s1P 1356476740614, s1N 2153200396627, s1N 788163744703, s1N 2549660422548,
   s1N 1577882707804, s1N 862564148794, s1N 2657769679588, s1N 775179987240, s1N 2400089244957,
   s1N 3874073033692, s1P 490897389096, s1P 1251737145648, s1N 4091786361612, s1P 461489228483,
   s1P 602627882782, s1P 3119161140600, s1N 1020072742752, s1N 2268795426793,
   s1P 3023954854212, s1N 1563226170937, s1N 871535501835, s1N 941178920953, s1N 1010982193505,
   s1P 2115398649081, s1P 4724320646775, s1P 2616895526888, s1P 2468204776801,
   s1P 3458991552135, s1P 4287531105543, s1P 21737417588421, s1P 49470034133345]
private def s1V0S4 : List ℤ :=
  [s1P 86184657920380, s1P 128198814209818, s1P 171973854046802, s1P 214193048470724,
   s1P 251253257240157, s1P 280815821685518, s1P 302091945205184, s1P 314235145962462,
   s1P 316272230848328, s1P 308508586637035, s1P 292665632802837, s1P 270693451653209,
   s1P 244288221968943, s1P 215287052214047, s1P 185719690228769, s1P 157246376270182,
   s1P 130777645610638, s1P 106707480947827, s1P 85316802957736, s1P 66868909131493,
   s1P 51455916337602, s1P 38895730309377, s1P 28811478991928, s1P 20800194858261,
   s1P 14541091052057, s1P 9793427495347, s1P 6341098797916, s1P 3954328537865,
   s1N 2390180175404, s1N 1415961680668, s1P 834007681814, s1P 495366701752, s1P 299675089137,
   s1P 185381876625, s1P 117088229244, s1P 75028749417, s1P 48251642543, s1P 30723171077,
   s1P 19118119233, s1P 11521489914, s1P 6702668865, s1P 3775278819, s1P 2075999956,
   s1P 1127496049, s1P 611751267, s1P 334052296, s1P 183771618, s1P 101380068, s1P 55673085,
   s1P 30218680, s1P 16129722, s1P 8442331, s1P 4328522, s1P 2174848, s1P 1071959, s1P 518762,
   s1N 246769, s1P 115651, s1P 53475, s1P 24362, s1P 10818, s1P 4648, s1P 1924, s1P 756]
private def s1V0S5 : List ℤ :=
  [s1P 274, s1P 94, s1P 27, s1P 6, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V0 : List ℤ :=
  s1V0S0 ++
    (s1V0S1 ++
    (s1V0S2 ++
    (s1V0S3 ++
    (s1V0S4 ++
    (s1V0S5 ++
    (mm16k512krS1VecIn5 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V1S0 : List ℤ :=
  [s1N 114840123, s1N 130448218, s1N 201873505, s1N 601356297, s1N 35632658, s1N 316071484,
   s1P 487062598, s1P 271934533, s1P 356924642, s1P 1545548166, s1N 847735884, s1N 1260096238,
   s1N 3126851654, s1N 1996605760, s1P 178592620, s1P 1280980195, s1P 37576056, s1N 1578787464,
   s1P 3211802938, s1P 4733552131, s1P 49029402, s1P 2637886968, s1P 1734910129,
   s1N 1728141035, s1N 3286866643, s1P 2196249313, s1P 10160657770, s1N 3538231841,
   s1N 1241314368, s1P 1496161511, s1N 403314436, s1N 4364800512, s1P 3344989418,
   s1P 7334781210, s1P 12628166679, s1P 1494064907, s1N 13953505275, s1N 1690178991,
   s1N 10080757630, s1N 16664033602, s1N 4826915125, s1P 12799918716, s1N 25922591847,
   s1N 27853273694, s1N 31574150033, s1P 18132922417, s1N 2914251210, s1P 7435372514,
   s1P 18714465003, s1N 6311250967, s1N 4257965548, s1N 31259259727, s1N 11763605308,
   s1P 15603251158, s1P 10250739853, s1N 17042468479, s1P 31037022216, s1P 32294472794,
   s1N 12321376617, s1P 32463699290, s1P 18886949217, s1N 6942746138, s1N 5397781914,
   s1N 26543230690]
private def s1V1S1 : List ℤ :=
  [s1P 5622366061, s1P 40696742162, s1P 44590787925, s1N 13085395976, s1P 7190401543,
   s1N 43513719091, s1P 4554773684, s1N 154898903, s1N 27052696905, s1N 23856830412,
   s1N 86446033376, s1N 29284270338, s1P 25067475686, s1N 35761990573, s1N 48020830050,
   s1N 52029955913, s1N 19131344797, s1P 5638816221, s1P 44998632165, s1N 21812298211,
   s1N 69800581953, s1N 126486429374, s1N 154686559070, s1N 214142016286, s1N 204676064502,
   s1N 18851427574, s1P 62628457688, s1P 31442501843, s1N 40080630930, s1N 19558786515,
   s1P 23918765267, s1P 34304245410, s1P 39386593391, s1P 48293315845, s1P 78459047547,
   s1P 222098351864, s1P 66570343564, s1P 54439231960, s1P 22939623169, s1P 94814938801,
   s1N 63125492965, s1P 17090295966, s1N 79789245355, s1N 126357644978, s1N 93983775071,
   s1N 122398279370, s1N 16736897315, s1P 9739982879, s1P 21372214884, s1P 36374410728,
   s1P 82913821077, s1N 207527508694, s1N 23793237580, s1N 65758820927, s1N 208089978122,
   s1P 85462069184, s1N 10179591738, s1N 54321616478, s1N 316419701083, s1N 34841887322,
   s1P 178381389714, s1N 75134967218, s1P 159787020310, s1P 348561581979]
private def s1V1S2 : List ℤ :=
  [s1N 105265763638, s1P 95878498064, s1P 155127385937, s1P 240347162502, s1P 41032516741,
   s1P 77262594529, s1P 221914255105, s1P 441645694108, s1N 90171513508, s1N 333083472601,
   s1P 343896741813, s1N 80395916641, s1N 48243455477, s1N 130045536924, s1N 38366899288,
   s1N 284546308653, s1N 707222074587, s1N 469332425399, s1N 418702940155, s1P 120133633982,
   s1N 19209476429, s1N 215481469773, s1N 231791728249, s1N 249107101480, s1P 751770764252,
   s1P 35691386144, s1N 952985892718, s1N 562746981308, s1P 604890839975, s1P 807714620067,
   s1N 1177777356761, s1N 413028107213, s1P 97284765263, s1N 422616380364, s1P 317407161511,
   s1N 202597811376, s1P 297644784873, s1P 151053652839, s1P 1219941960764, s1P 732026237327,
   s1N 483241406380, s1N 29826872690, s1N 119196189133, s1P 8514619625, s1P 834708049632,
   s1P 1238564577439, s1P 359055374746, s1P 13919613052, s1N 262323906319, s1N 494279176076,
   s1P 497787746398, s1P 692153888538, s1P 1625985130419, s1N 291052026925, s1N 840800150558,
   s1P 3078552365463, s1P 4519841344110, s1N 655412929300, s1P 2116375199986, s1P 586440671337,
   s1N 366918476970, s1N 3049036911789, s1N 1445332669663, s1N 1660647734665]
private def s1V1S3 : List ℤ :=
  [s1P 1621971828008, s1P 2151318664753, s1P 35561699022, s1N 901765405913, s1N 736277038358,
   s1P 1038544315422, s1N 1609375131305, s1P 2304274648810, s1N 1410766678155,
   s1N 314539062937, s1P 165776567826, s1N 353286618279, s1N 3002357320818, s1N 2496827040134,
   s1N 297560785506, s1N 1666995603580, s1P 3751031903357, s1P 2559590412041,
   s1P 2836976447773, s1P 1506772841228, s1P 570580730561, s1N 4136487380480,
   s1P 2689143886401, s1P 596706658067, s1P 360524842344, s1P 1603016289860, s1P 690914461830,
   s1P 681088763253, s1P 285636286684, s1P 669137983345, s1P 3407095542419, s1P 469383244619,
   s1P 710968430419, s1P 18710740022, s1N 94705708943, s1N 815820760343, s1P 3134458468890,
   s1N 465651081077, s1P 2835144291311, s1N 6001202093936, s1P 1942461140895,
   s1N 1618070108037, s1P 20176810539, s1N 321194014568, s1P 684819637587, s1P 1050651026402,
   s1N 1807899535436, s1P 372265204740, s1P 1084434979228, s1P 1447695008665, s1P 110467273981,
   s1P 1349433116329, s1P 2989386559957, s1P 1678974152058, s1N 4211120319149,
   s1N 3494634447719, s1N 4640850775636, s1N 415067564223, s1N 2231569694113,
   s1N 1101868503098, s1P 70575083740, s1N 2319144911575, s1P 832419925955, s1N 460959985494]
private def s1V1S4 : List ℤ :=
  [s1N 2846896221636, s1N 872251393070, s1P 2486539602834, s1P 4845462914611, s1N 82263021642,
   s1N 666815679264, s1P 659298390639, s1P 3416169735606, s1N 3848874600847, s1P 386690541932,
   s1P 4660232128924, s1P 1405295966948, s1P 12705136058528, s1P 39408981423711,
   s1P 73700328528392, s1P 116448329372074, s1P 159550940500322, s1P 204294735048876,
   s1P 244211037176959, s1P 276095189173350, s1P 301901292422510, s1P 315334157914915,
   s1P 318213124941961, s1P 313464231072290, s1P 297760319561162, s1P 274530928882561,
   s1P 249461381483622, s1P 221402944253457, s1P 190160236067416, s1P 160455662189290,
   s1P 134599283587071, s1P 110520728584339, s1P 87328271139894, s1P 67202227844147,
   s1P 51886126533702, s1P 40457364346198, s1P 30840880790099, s1P 21989529309303,
   s1P 14232217965527, s1P 8280217385179, s1N 4376069290021, s1N 2182574180059,
   s1N 1109791951284, s1N 632485681081, s1P 416655361249, s1P 298858424676, s1P 217172908954,
   s1P 154066807290, s1P 105662195619, s1P 70157597076, s1P 45274216289, s1P 28478741522,
   s1P 17487733148, s1P 10492049042, s1P 6155085860, s1P 3536535647, s1P 1994436269,
   s1P 1108697439, s1P 606709523, s1P 332897195, s1N 177178433, s1P 94985956, s1P 52925277,
   s1P 28037146]
private def s1V1S5 : List ℤ :=
  [s1P 12959657, s1P 5248837, s1P 2030207, s1P 842774, s1P 393018, s1P 196944, s1P 101070,
   s1P 52165, s1P 26875, s1P 13671, s1P 6780, s1P 3247, s1P 1486, s1P 648, s1P 264, s1P 99,
   s1P 34, s1P 8, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V1 : List ℤ :=
  s1V1S0 ++
    (s1V1S1 ++
    (s1V1S2 ++
    (s1V1S3 ++
    (s1V1S4 ++
    (s1V1S5 ++
    (mm16k512krS1VecIn5 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V2S0 : List ℤ :=
  [s1P 88754750, s1P 32726742, s1N 508407114, s1P 290925554, s1N 148409608, s1N 518859051,
   s1N 167932153, s1P 519108918, s1P 374507711, s1P 532104035, s1P 1635787537, s1P 113203227,
   s1P 1097207880, s1P 971512496, s1P 2357415315, s1P 707868356, s1N 3023642999, s1N 273886176,
   s1N 2324019802, s1N 1155126781, s1P 2620530559, s1N 153535266, s1P 445273935,
   s1P 4621168229, s1P 1405750451, s1P 5590930822, s1P 8414727786, s1P 3821618581,
   s1P 3148874073, s1N 1825662411, s1N 4719468702, s1P 1153420029, s1P 2619428183,
   s1N 3749945740, s1N 4618641625, s1N 13430804633, s1P 1302728270, s1P 6064980338,
   s1P 7562135074, s1N 12200050542, s1N 1846116456, s1P 6940350485, s1P 13027728023,
   s1P 20420077299, s1N 13759248252, s1N 37808380047, s1N 9373952761, s1P 10036279826,
   s1P 7739794321, s1N 21023666921, s1N 19396023861, s1N 1356369735, s1P 3139716682,
   s1N 33483159212, s1N 15918816876, s1N 22532636635, s1P 895736214, s1P 15277060700,
   s1P 25112760827, s1P 32772176261, s1P 17630327901, s1N 356992063, s1N 23924423984,
   s1P 2263811892]
private def s1V2S1 : List ℤ :=
  [s1P 19264099176, s1N 2736397847, s1N 50399114169, s1N 35814694496, s1P 24480011489,
   s1P 55126445802, s1P 44554114140, s1P 11332297380, s1N 35471104217, s1N 15337258732,
   s1N 23859558280, s1P 41459199862, s1P 5898770477, s1P 32092097057, s1P 36825392008,
   s1N 15275743981, s1P 25644020481, s1P 39994669388, s1N 3017858095, s1N 13582010129,
   s1N 50582018745, s1P 11817495227, s1N 23024204603, s1N 11170896089, s1P 6605091373,
   s1P 50852374157, s1P 96983532118, s1P 13065734739, s1N 19278474111, s1P 6192327702,
   s1N 7253914737, s1N 10818473351, s1N 16217404225, s1N 113815338031, s1N 143149583808,
   s1N 243276350602, s1N 238513424214, s1N 22339284984, s1N 50420840881, s1P 20615902285,
   s1N 14698768264, s1N 100600715013, s1N 108426558762, s1P 4680211205, s1P 123189030707,
   s1P 160866024864, s1P 147110304485, s1N 9137681469, s1P 127138111309, s1P 28490240627,
   s1N 70760159566, s1N 89926108054, s1N 95921187733, s1N 94668656129, s1N 141784421496,
   s1P 17951084435, s1N 41251486074, s1N 133873110022, s1N 153175612922, s1N 138868427809,
   s1N 94515824546, s1P 81670231748, s1P 170944870177, s1P 40321569396]
private def s1V2S2 : List ℤ :=
  [s1P 127704197796, s1P 543078569488, s1N 4586988599, s1N 125951448901, s1N 91413073014,
   s1N 279098649757, s1N 90410263020, s1P 303311030444, s1N 182423932681, s1P 295238793246,
   s1N 80689452915, s1N 46249414231, s1P 29746636184, s1N 87223446153, s1P 216232274480,
   s1P 399462183595, s1P 209354213248, s1N 21139180335, s1N 140838619174, s1P 21693484433,
   s1N 102670892498, s1N 186553723390, s1N 382778890497, s1N 499218910507, s1N 119747249392,
   s1P 161396147770, s1P 677700606941, s1P 992000065506, s1P 1092604555565, s1P 313135939648,
   s1N 761023612784, s1N 847341673717, s1N 436511157664, s1P 810781310528, s1P 610333490484,
   s1N 676943521309, s1N 166817618805, s1P 538875666288, s1N 306898289156, s1P 763290982692,
   s1N 494681632751, s1P 174897874634, s1P 1180359185136, s1N 171647102981, s1P 22361331063,
   s1N 662795057990, s1N 411461830986, s1N 243409067969, s1N 660519681552, s1N 477694568085,
   s1P 62481026629, s1N 1019638962822, s1P 157024554223, s1P 999384609598, s1N 233295404516,
   s1N 724603305820, s1P 326218304716, s1N 1017267763637, s1N 321643287251, s1N 1521668962509,
   s1N 1753466402934, s1N 1065282792226, s1N 3356069128526, s1N 4540002724086]
private def s1V2S3 : List ℤ :=
  [s1N 944673855899, s1P 1860011267236, s1P 584901616951, s1N 234897246706, s1P 4236152412214,
   s1N 1505954107594, s1P 1693146912952, s1P 384618306413, s1P 1462606659705,
   s1P 1425351357440, s1N 413212728132, s1N 1824102215624, s1N 2165524843912,
   s1P 1259405355430, s1P 92110801340, s1N 837602287896, s1P 484645194285, s1N 700877083769,
   s1P 711851939091, s1P 1947868623482, s1P 5123430262671, s1P 4527498566289,
   s1P 1232092669465, s1N 1469340117727, s1N 1115938049104, s1N 890471874553,
   s1P 1100907587212, s1P 3239266774759, s1N 165210551715, s1P 4094585628730,
   s1P 3793523147218, s1N 2302552308276, s1N 682486490953, s1N 2339616682105,
   s1N 2138550366353, s1P 1018357679394, s1N 604557670519, s1N 1334277645673, s1N 541850560967,
   s1P 2162574743243, s1N 1917932583011, s1P 2015385161696, s1P 1061330432627,
   s1P 188208570763, s1P 335933058000, s1N 494455934013, s1N 564746981970, s1P 2103761576853,
   s1P 232130041699, s1P 3723300150619, s1N 822834431014, s1P 3137141845820, s1N 280014987318,
   s1N 69408557980, s1P 1407118329719, s1P 1275642228269, s1N 1415847261432, s1N 2579441811568,
   s1P 2058213719979, s1P 345856962821, s1N 1121416170441, s1P 2914812118418, s1N 583851445068,
   s1P 2078205038689]
private def s1V2S4 : List ℤ :=
  [s1N 2814154169955, s1N 2617417179239, s1N 1603032277233, s1N 6310851239087,
   s1N 2170754347495, s1P 1058010269752, s1N 3426933583209, s1P 3864653595296,
   s1P 3255037279373, s1P 5141551180470, s1P 2108702662524, s1P 2838323738037,
   s1P 181498512758, s1N 1955181338068, s1P 290301810157, s1N 1877910199270, s1N 5045028971106,
   s1P 726249502706, s1P 1436164908044, s1P 31771195718, s1P 1387220524858, s1P 2659268411089,
   s1P 4916039945351, s1N 2943685845791, s1N 2442481851207, s1P 2422384367125,
   s1P 4584858577078, s1P 30745296444295, s1P 61288011124068, s1P 103821370478663,
   s1P 147511632996213, s1P 192855706442281, s1P 239169336375066, s1P 272414050612372,
   s1P 297896910591051, s1P 317580713674872, s1P 322059284591821, s1P 315620531118121,
   s1P 302140391227947, s1P 280915596518741, s1P 253451890013511, s1P 224373347124265,
   s1P 196157802737520, s1P 167190128009207, s1P 136433146059812, s1P 108194688108550,
   s1P 87055768555770, s1P 71637982676575, s1P 57477701152284, s1P 42758077397093,
   s1P 28921838117039, s1P 17869504101541, s1P 10212371858320, s1P 5455611926211,
   s1P 2752479725877, s1P 1345309885059, s1P 679484835153, s1P 391190901068, s1P 267823960395,
   s1P 203944678834, s1P 157654204912, s1P 119067137898, s1P 84491094895, s1P 59526528976]
private def s1V2S5 : List ℤ :=
  [s1P 38115574248, s1P 24158656735, s1P 16115623738, s1P 9865983285, s1P 5018032620,
   s1P 2192991950, s1P 954414641, s1P 484884434, s1P 284656188, s1P 173430304, s1P 103326391,
   s1P 59003650, s1P 31877537, s1P 16142263, s1P 7671286, s1P 3476230, s1P 1546254, s1P 697821,
   s1P 326602, s1P 158674, s1P 78868, s1P 39427, s1P 19583, s1P 9592, s1P 4608, s1P 2163,
   s1P 984, s1P 430, s1P 178, s1P 68, s1P 22, s1P 6, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V2 : List ℤ :=
  s1V2S0 ++
    (s1V2S1 ++
    (s1V2S2 ++
    (s1V2S3 ++
    (s1V2S4 ++
    (s1V2S5 ++
    (mm16k512krS1VecIn5 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V3S0 : List ℤ :=
  [s1P 713397, s1P 87337180, s1P 284115545, s1P 469377954, s1P 313899567, s1N 36241578,
   s1P 454144364, s1N 544764693, s1P 113061823, s1P 666406799, s1P 35155881, s1P 803024662,
   s1N 907595433, s1N 2131929370, s1N 1599311338, s1P 881773640, s1N 145709502, s1N 9573857,
   s1N 2530075674, s1N 402076299, s1N 3426133922, s1N 1171080584, s1P 1015646766,
   s1P 935567844, s1P 3701425633, s1P 2434174999, s1N 268436539, s1N 700741397, s1N 2154180858,
   s1N 1301298539, s1N 2118038705, s1N 5022659876, s1N 4961529288, s1N 11975017590,
   s1N 7680720940, s1N 6022448949, s1P 560129722, s1P 8655438171, s1P 5513721655,
   s1P 1661828677, s1N 918359842, s1P 3558751446, s1P 9711371702, s1P 13884577346,
   s1P 3889671479, s1N 9884705746, s1N 8618644425, s1N 12295384349, s1N 14348068261,
   s1N 19905708757, s1N 31310970913, s1N 29365202564, s1N 10483789384, s1N 3745348842,
   s1N 11060118527, s1N 16582031612, s1N 17506268082, s1N 26616374740, s1N 13886329210,
   s1N 16078699925, s1N 20712558810, s1P 3700303962, s1P 30495420946, s1P 11642982605]
private def s1V3S1 : List ℤ :=
  [s1N 3514557982, s1N 20251389432, s1P 23144432042, s1P 19360668548, s1N 24135039200,
   s1P 2831072090, s1N 51805057307, s1N 51579852147, s1N 56958827507, s1N 49701368110,
   s1N 29878238956, s1P 9137180308, s1P 24596935843, s1N 7518430759, s1N 492811397,
   s1N 19182790502, s1N 43623661897, s1N 49980529447, s1N 6804194716, s1N 51863376925,
   s1N 24196433402, s1P 15071050362, s1P 13449691977, s1P 22786089108, s1N 8491642624,
   s1P 11674916133, s1N 514319766, s1N 17804422628, s1N 40985747903, s1P 7126153038,
   s1N 2647985994, s1P 12243907730, s1N 8857358999, s1P 21840506701, s1N 1692568897,
   s1N 60192325407, s1N 56786755517, s1N 20296665185, s1P 40086830484, s1P 65862117303,
   s1N 18592814135, s1N 82736986662, s1N 77226202172, s1N 63066301096, s1N 28041453494,
   s1N 143332715051, s1N 144765083363, s1P 116818811252, s1P 195784878295, s1N 219626988312,
   s1N 184004502174, s1N 40777818599, s1P 100390203054, s1N 2263145795, s1P 61254111444,
   s1P 208924769836, s1P 98547014987, s1P 42258251720, s1N 48097724863, s1P 54178293806,
   s1P 112136826277, s1P 161329898533, s1P 88489372609, s1P 34083108113]
private def s1V3S2 : List ℤ :=
  [s1P 3566560904, s1P 117941481945, s1P 131748608974, s1P 34232509891, s1N 13436041434,
   s1P 145858591390, s1P 273448009633, s1P 478986778720, s1P 485031549132, s1P 307440553516,
   s1P 221705929861, s1N 104332084219, s1N 16230062214, s1N 36565880982, s1N 109418370746,
   s1P 37074655239, s1N 182830739610, s1N 50052424815, s1P 255739238211, s1P 159359903325,
   s1N 22366215434, s1P 165512998690, s1P 91314983078, s1P 19632509672, s1P 115394057345,
   s1P 162667765827, s1N 278876167085, s1P 222221702967, s1N 150109912903, s1N 212605676232,
   s1N 224771109056, s1N 15449088217, s1N 112772569923, s1P 27668505420, s1N 260505970694,
   s1P 234685806386, s1P 677905579022, s1N 130494494223, s1N 159667568854, s1P 193884134576,
   s1P 1128049476825, s1P 1964621634997, s1P 1104795043209, s1P 332416735503, s1N 784930974521,
   s1N 619819851428, s1P 341781708958, s1P 724872871593, s1P 404041647930, s1P 439979516639,
   s1P 194959488800, s1P 167569179428, s1P 175158084456, s1N 120624790301, s1P 440638370394,
   s1N 540222091514, s1P 90968632826, s1N 92730508623, s1P 154599269445, s1N 33915870792,
   s1N 1283361543350, s1N 821151747229, s1N 1165675604550, s1N 537431994280]
private def s1V3S3 : List ℤ :=
  [s1N 618078225104, s1N 260824244037, s1P 39351769627, s1P 441947007069, s1P 1788939838269,
   s1P 1472818181158, s1N 562930619964, s1P 1031132371219, s1P 2426030294437,
   s1P 2590555737636, s1P 2120522576363, s1P 3927140976470, s1P 4338054810733,
   s1P 3544951622852, s1N 916862202734, s1N 136451478619, s1P 344231547636, s1N 248511804726,
   s1P 283807141787, s1P 1479704860189, s1P 725629484161, s1P 2108694445792, s1P 1114599082606,
   s1P 2091859128024, s1P 606144494611, s1N 673763630436, s1P 1484974405624, s1P 117496303327,
   s1P 1095855376423, s1P 753153751984, s1P 2549018310062, s1P 2872125417202,
   s1P 2964298920545, s1P 3430246627942, s1N 2794181382839, s1N 5351675786501,
   s1N 4753419547626, s1P 382066440554, s1N 1042940316237, s1P 1439926640636,
   s1N 3477710369600, s1N 4590930927655, s1N 1363899285639, s1P 812791148447, s1N 910499582336,
   s1N 1103395706971, s1P 141843227170, s1N 1660710123843, s1P 237783132982, s1P 1657805188892,
   s1N 1779806805723, s1N 545631439122, s1N 2038048179917, s1P 4040152051197, s1P 795704638467,
   s1P 163429106286, s1N 1196570562094, s1N 1675680942211, s1N 199399952628, s1P 1021562116839,
   s1N 2154187074242, s1P 2214070022164, s1N 15552119079, s1N 2405871061611]
private def s1V3S4 : List ℤ :=
  [s1N 4810866185919, s1P 2950057857155, s1N 3481748551738, s1N 3918601431277,
   s1P 2137684705476, s1N 1033320494633, s1P 507027348419, s1P 2630647416234,
   s1N 2425028484685, s1N 1318823953564, s1N 1333504735662, s1N 2852795481637,
   s1N 521624047542, s1P 6163456863358, s1N 2442182825850, s1P 2767067465721,
   s1N 1218442826568, s1P 134450311060, s1P 4799557509102, s1P 2444735488249,
   s1N 3370351229697, s1N 780657328627, s1N 3145915492376, s1P 1829613015362,
   s1N 1273511734754, s1P 4297703260613, s1P 580814674434, s1N 114011604597, s1N 4069984400712,
   s1N 4006523323091, s1N 720511599267, s1P 1191008682376, s1P 437138931705, s1P 797993439923,
   s1P 1330925155716, s1P 5595831758796, s1P 5543253239571, s1P 831336087137,
   s1P 6640915248697, s1P 3875695010797, s1P 9774261557119, s1P 34305188019552,
   s1P 70386466823509, s1P 115354379744842, s1P 162639232193926, s1P 207738017898952,
   s1P 249850336265004, s1P 286101780728908, s1P 311453362632552, s1P 321408663171573,
   s1P 321251231323253, s1P 310854557104129, s1P 297840346511747, s1P 274435555934230,
   s1P 244861402343755, s1P 213583117441071, s1P 179312848694655, s1P 149723383102083,
   s1P 126684510942906, s1P 104019230548408, s1P 81412038434786, s1P 62712374496206,
   s1P 47915828614466, s1P 34560287509451]
private def s1V3S5 : List ℤ :=
  [s1P 22185797076405, s1P 12265931480344, s1P 5812586903682, s1P 2433215330848,
   s1P 1001702416377, s1P 502384580694, s1P 342378474382, s1P 271893621518, s1P 216851693526,
   s1P 166131952072, s1P 122329330806, s1P 87299267881, s1P 60593718821, s1P 40781724921,
   s1P 26441161813, s1P 16415900577, s1P 9733468418, s1P 5522332169, s1P 3017927125,
   s1P 1605715267, s1P 842652740, s1P 441494455, s1P 232666881, s1P 123378033, s1P 65446152,
   s1P 34424707, s1P 17810680, s1P 9016003, s1P 4457231, s1P 2154851, s1P 1022704, s1P 479128,
   s1P 222910, s1P 103521, s1P 48146, s1P 22438, s1P 10457, s1P 4850, s1P 2225, s1P 1001,
   s1P 436, s1P 181, s1P 68, s1P 22, s1P 6, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V3 : List ℤ :=
  s1V3S0 ++
    (s1V3S1 ++
    (s1V3S2 ++
    (s1V3S3 ++
    (s1V3S4 ++
    (s1V3S5 ++
    (mm16k512krS1VecIn5 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V4S0 : List ℤ :=
  [s1P 10114534, s1P 14764793, s1N 36000782, s1P 44043269, s1P 734511478, s1N 9934063,
   s1P 150443849, s1P 864758405, s1N 447714010, s1N 115883507, s1P 87874235, s1P 121951459,
   s1P 591801196, s1P 2069475245, s1P 44449701, s1P 494821933, s1P 2917377446, s1P 1182626609,
   s1N 513089911, s1N 1208535066, s1P 576750685, s1P 372104008, s1P 1804153452, s1P 1090139982,
   s1P 2216200689, s1P 2935553472, s1P 138645158, s1N 1217162418, s1N 4636701702,
   s1N 1300528952, s1N 1793448022, s1P 1952180617, s1P 2426128886, s1P 123479415,
   s1P 705741259, s1P 1095747659, s1P 1967868956, s1P 3572002276, s1P 8914638104,
   s1P 13144781312, s1P 7245712714, s1P 5273781966, s1N 4096480202, s1N 8773073912,
   s1N 133733417, s1P 4618204457, s1N 1704804153, s1N 5953306784, s1P 12691057219,
   s1P 11905894926, s1P 5172657951, s1N 9730568730, s1N 1075771869, s1P 1512333674,
   s1P 12642269255, s1P 23470685497, s1P 21489119286, s1P 37351424895, s1P 10291550479,
   s1N 6477928017, s1N 16615526540, s1P 5873453338, s1P 35596260138, s1P 16105833654]
private def s1V4S1 : List ℤ :=
  [s1N 24905074472, s1N 50151296273, s1N 19733850316, s1N 2914452206, s1P 9571432573,
   s1P 2062218142, s1P 9370229181, s1N 13781285959, s1P 9531123343, s1P 13029811210,
   s1N 16286424894, s1N 8529690276, s1P 20751900221, s1P 19121619056, s1P 70052727980,
   s1P 37976844057, s1P 65221069336, s1P 44205333050, s1P 20043686345, s1N 19215206130,
   s1P 1955175087, s1P 4429310254, s1P 25077548912, s1P 5525741257, s1N 30530839231,
   s1N 51136056412, s1N 46497911220, s1N 27862925148, s1N 4733823251, s1N 19717243916,
   s1P 3422079955, s1P 37046487629, s1P 13164609097, s1P 9946048192, s1N 2217405861,
   s1N 23785955504, s1N 6682921945, s1N 33069269172, s1N 23744521700, s1P 5428696591,
   s1N 78504863211, s1N 38990792444, s1N 55774314396, s1N 131777011100, s1N 108968737460,
   s1N 111981357407, s1N 79153732697, s1P 76011185347, s1P 118792136708, s1P 166283495072,
   s1P 52520073279, s1N 195865178638, s1N 234099622338, s1P 22029223490, s1P 48265810131,
   s1P 15891053777, s1N 52013451175, s1N 28323103147, s1N 70305950134, s1P 109044457564,
   s1N 112956382356, s1P 8362333980, s1N 76313996023, s1N 154956583713]
private def s1V4S2 : List ℤ :=
  [s1N 160760101061, s1P 74632075780, s1N 43519409059, s1N 35099576538, s1P 132861853065,
   s1P 166826291250, s1P 60622564980, s1P 111010586113, s1N 80846577683, s1N 96610111660,
   s1N 171884750850, s1N 5492967541, s1N 144362006827, s1N 88472842400, s1P 52475342971,
   s1P 310182226829, s1P 477667911292, s1P 623163165807, s1N 17324444224, s1N 371215291356,
   s1N 136008019515, s1N 8305645693, s1N 8599181643, s1P 32009173371, s1P 298456912949,
   s1N 54612738381, s1N 118205698382, s1N 98096635109, s1N 222601192535, s1P 50837479217,
   s1P 173893906954, s1P 284490703746, s1P 294260512784, s1P 280521769660, s1P 170456147059,
   s1N 122755177820, s1N 222048964485, s1N 223589296138, s1N 183044992466, s1P 104572366156,
   s1P 513452585514, s1P 421380797829, s1P 18487347209, s1P 220601735552, s1P 864851494893,
   s1P 435483006757, s1P 497758920600, s1P 722286005722, s1P 784491836806, s1P 1833812467060,
   s1P 1175010991282, s1P 1156629005167, s1P 143780064935, s1N 100419854503, s1N 211820171364,
   s1N 132174584328, s1N 539599495261, s1P 370576172317, s1P 232698036687, s1P 232272829470,
   s1N 359318810230, s1N 764225982224, s1N 574311391655, s1N 169095441102]
private def s1V4S3 : List ℤ :=
  [s1N 97905742685, s1N 4486508691, s1P 228685036390, s1P 1065616341320, s1P 1474114465475,
   s1P 550529250430, s1P 400584291498, s1P 161131280786, s1P 1628251810107, s1P 2041212328577,
   s1N 31685885762, s1N 1711630547781, s1N 1148264294917, s1N 549508131415, s1N 1462061392556,
   s1P 693523800750, s1P 485878453580, s1P 571817549914, s1N 3048651723397, s1N 2945463027428,
   s1N 4200889424110, s1N 4223435124436, s1N 2312839089990, s1N 1552169106127, s1P 87255558826,
   s1N 1660420165125, s1N 1236743944018, s1P 463956915291, s1N 209248994452, s1N 2466413581190,
   s1N 22978446737, s1P 2980932381461, s1P 1244234566883, s1P 656158366040, s1P 1749251388480,
   s1P 1675299466791, s1P 621824452010, s1N 1116479433340, s1N 735241675898, s1N 2464649326932,
   s1P 5480171569746, s1P 6704497836737, s1P 2622845177191, s1P 2149005584332,
   s1P 3792300209218, s1P 5613707345, s1N 939166037910, s1N 1020512482063, s1N 1937575983719,
   s1N 3491585412029, s1N 2878438324358, s1P 1392192923613, s1P 2802633007320,
   s1P 806246714746, s1P 2587670426127, s1P 1004152701864, s1N 178906304207, s1N 1376458302952,
   s1P 3576169223659, s1P 2282715932951, s1P 3925855606787, s1N 1671205952354,
   s1P 384037742878, s1P 5078335843807]
private def s1V4S4 : List ℤ :=
  [s1P 2372818756710, s1N 2048777924763, s1N 41654076715, s1N 619709199322, s1P 1397399368336,
   s1P 3564972630896, s1P 4420960900137, s1P 1931224818440, s1P 299991838119,
   s1N 3907552340377, s1P 1053275576654, s1N 1299968327205, s1N 4536775094797,
   s1N 2450181557137, s1P 1475930811289, s1N 3271848046782, s1N 550492544423, s1N 992094182420,
   s1P 5142231201432, s1P 789226203551, s1P 2356663257426, s1N 680815670077, s1P 1021815217803,
   s1N 650932027049, s1N 828977261497, s1P 3062227709685, s1N 2109086642924, s1N 1504700759130,
   s1P 1586929151825, s1P 3676984840224, s1P 952823028222, s1N 2561223713760,
   s1N 1833207827744, s1N 5911327852473, s1N 1161417376552, s1P 2587660381995, s1P 21528818875,
   s1P 2181747439247, s1N 2754164612808, s1N 778132848268, s1P 381569617803, s1P 1415941610695,
   s1N 1095871386462, s1N 3747019446193, s1N 8305778667769, s1N 5458698760663,
   s1P 2405232543359, s1P 7579415321299, s1P 5130849537267, s1P 13050967022333,
   s1P 41999401449130, s1P 77188834292035, s1P 122573717130108, s1P 173423784335847,
   s1P 221434352724174, s1P 263400832318785, s1P 294901045106513, s1P 313061077767212,
   s1P 321682428940786, s1P 323228666009656, s1P 314168998296563, s1P 292796492495007,
   s1P 263853804715618, s1P 233127712527697]
private def s1V4S5 : List ℤ :=
  [s1P 202664366427157, s1P 172535393229866, s1P 143777119022605, s1P 117997461678627,
   s1P 95615873027636, s1P 75752829792482, s1P 57564136172139, s1P 41160153215388,
   s1P 27340032384007, s1P 16784307715563, s1P 9546535365711, s1P 5086600497689,
   s1N 2599266531362, s1N 1326957157126, s1P 714962851453, s1P 424790438543, s1P 278698712341,
   s1P 194783146281, s1N 139233667039, s1P 99030050978, s1P 69028376848, s1P 46767540960,
   s1P 30651254524, s1P 19382297642, s1P 11816430934, s1P 6952818902, s1P 3959865099,
   s1P 2192773555, s1P 1187288199, s1P 632411048, s1P 333184892, s1P 174280569, s1N 90638344,
   s1P 46827475, s1P 23975047, s1P 12128393, s1P 6046877, s1P 2966850, s1P 1432232, s1P 680981,
   s1P 319565, s1P 148394, s1P 68364, s1P 31314, s1N 14272, s1P 6469, s1P 2907, s1P 1286,
   s1P 553, s1N 229, s1P 88, s1P 29, s1P 8, s1P 1, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V4 : List ℤ :=
  s1V4S0 ++
    (s1V4S1 ++
    (s1V4S2 ++
    (s1V4S3 ++
    (s1V4S4 ++
    (s1V4S5 ++
    (mm16k512krS1VecIn5 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V5S0 : List ℤ :=
  [s1N 4570334, s1N 34954212, s1P 236505402, s1N 370211033, s1N 158865012, s1N 846906327,
   s1N 178728880, s1N 81389748, s1P 505415769, s1N 717165176, s1N 469036878, s1N 491537297,
   s1N 329954607, s1P 1551894854, s1N 539940836, s1N 1265343150, s1N 1001753831, s1N 903537689,
   s1N 1179066716, s1N 1988716625, s1N 1756635836, s1N 1762766019, s1N 1331755757,
   s1P 642886820, s1N 1046581448, s1N 1327058098, s1N 318148915, s1N 113602618, s1N 2965820841,
   s1N 2436533523, s1N 2638781712, s1N 1414126925, s1P 1782577989, s1P 2939159246,
   s1N 4113955943, s1N 1310057320, s1N 822204830, s1N 469337724, s1N 3687360773, s1P 160177254,
   s1N 110725469, s1N 1720794663, s1N 4092090857, s1N 2362722718, s1N 12589822322,
   s1N 15648698089, s1N 10592440882, s1N 3674136634, s1P 4143874405, s1P 10266414403,
   s1P 6606412415, s1P 1098720935, s1P 10265194952, s1N 1258306799, s1N 13854539233,
   s1N 6671190228, s1N 6016599537, s1N 4169411032, s1N 1941808136, s1P 6332387673,
   s1P 343676525, s1N 3346897184, s1N 31530682117, s1N 41876933034]
private def s1V5S1 : List ℤ :=
  [s1N 35350151104, s1N 14195995909, s1N 20690886349, s1N 14314448667, s1N 30649582678,
   s1N 13489552503, s1N 30013784650, s1N 42897931963, s1N 21081389090, s1N 22745078833,
   s1P 3046428632, s1P 7347978683, s1N 1978834121, s1P 12000495196, s1P 18205717533,
   s1P 12063453465, s1P 8070800659, s1P 9517897513, s1N 5222853271, s1P 6801963489,
   s1P 8250995464, s1P 16549913864, s1P 47985201282, s1P 73843158677, s1P 54067916580,
   s1P 43433469817, s1P 8840632987, s1N 18442313436, s1N 28766245783, s1P 35616284868,
   s1P 4708982141, s1N 14885552452, s1N 45278653279, s1N 13294400601, s1P 26503044135,
   s1P 71920727484, s1P 10220872208, s1P 6010882771, s1P 38175635361, s1N 52077466639,
   s1N 10052265313, s1P 6476477294, s1N 11141313077, s1P 8520512057, s1P 27256956528,
   s1P 33224104880, s1N 72439420898, s1P 10277968642, s1P 15926590023, s1N 11011520902,
   s1N 124529362546, s1N 79603086273, s1N 193499814140, s1N 219715489484, s1N 173816036668,
   s1N 33229739853, s1N 170460132988, s1N 210389376829, s1N 63384118919, s1P 105459324042,
   s1N 25992799179, s1P 51009664874, s1P 114582698973, s1N 115725611186]
private def s1V5S2 : List ℤ :=
  [s1N 83886987051, s1P 71880105551, s1N 43376450249, s1N 105605466875, s1P 26820217917,
   s1P 21137304203, s1N 60315475999, s1N 52922368834, s1N 164212565505, s1P 13041010767,
   s1P 112682876050, s1N 162133908821, s1P 118971899965, s1P 47190961981, s1N 154737890892,
   s1N 139402222068, s1N 79534766164, s1N 167056196119, s1P 9768355166, s1P 253453866541,
   s1P 316111093421, s1P 434969739100, s1P 153711275766, s1N 135343540258, s1N 406494658838,
   s1N 461105885568, s1N 350409691149, s1P 91165748700, s1P 60638027410, s1P 129454505171,
   s1N 134990160316, s1N 10627557617, s1N 205987819954, s1N 92561312517, s1N 38590732306,
   s1P 118453066824, s1P 39110737103, s1P 260815884819, s1N 227216342183, s1N 518323567303,
   s1N 307773028374, s1N 515053439098, s1N 392557525455, s1N 420974986560, s1P 181091134398,
   s1P 342102476341, s1P 329332715743, s1N 324425412399, s1N 153539043105, s1N 163628940749,
   s1P 1418027858, s1P 187133441101, s1P 677363725118, s1P 476414084551, s1P 24455436428,
   s1P 162990892959, s1P 581517455619, s1P 1118660000486, s1P 1417943325476, s1P 1162947474649,
   s1P 1456434994493, s1P 698133921477, s1P 524299601937, s1P 271074133988]
private def s1V5S3 : List ℤ :=
  [s1P 601943600429, s1P 229279923520, s1N 299925947622, s1N 400961564524, s1N 343251911513,
   s1N 155058480706, s1N 1060453727901, s1N 927014847623, s1N 1204290582161, s1N 1180283581729,
   s1P 448668015554, s1P 1524240311330, s1P 1318129384211, s1N 963054091182, s1N 788523225476,
   s1P 557627722212, s1P 1193247250995, s1P 1468169546268, s1P 1645190727663,
   s1P 1043762992359, s1N 668951286289, s1N 1826681058786, s1N 1009642074104, s1N 102710273778,
   s1P 556851124059, s1P 1314050560312, s1P 2143324451756, s1P 2756309938344,
   s1P 3304666312221, s1N 3420165082559, s1P 1553905370804, s1N 5249719716814,
   s1N 2563899773286, s1N 131640196358, s1P 1331937954344, s1N 1093016880900, s1P 371195188072,
   s1N 3264499879044, s1N 222403093059, s1N 2178529274300, s1N 1393978517447,
   s1N 1136344822806, s1P 3339194618310, s1P 4092833410382, s1P 1662535695841,
   s1P 2398503985638, s1P 201208760562, s1N 1863318912864, s1P 451746483167, s1P 1953808487851,
   s1P 6185393106547, s1N 1633787096439, s1P 3616551375784, s1P 4067862315915,
   s1P 2326885313379, s1N 956364089448, s1N 1446949021398, s1N 3303723682812,
   s1N 1107247075130, s1P 4029025732715, s1P 997205114282, s1N 4109469703411,
   s1P 3315533840201, s1N 2741347369312]
private def s1V5S4 : List ℤ :=
  [s1N 506634604798, s1N 669800171069, s1P 3392935421671, s1N 1068590346596, s1N 137465928815,
   s1N 894229543664, s1N 3775628691805, s1P 248702181772, s1P 6223318423561, s1P 357373504731,
   s1N 1654174838608, s1P 3226290659671, s1N 3427616595779, s1P 2710118408171,
   s1P 1251512941370, s1N 3473490624477, s1N 2137299632439, s1P 2593201444027,
   s1P 2861127296819, s1N 1346483253396, s1P 511527416295, s1P 2740851025301,
   s1P 2461865739915, s1N 2658567455730, s1N 1168037522595, s1N 2548976185492,
   s1P 1956708194914, s1P 4908504486535, s1N 1955673672547, s1P 1851162095997,
   s1P 374950167766, s1P 1626477187591, s1N 1136563910873, s1N 750843061569, s1N 2445017779414,
   s1N 120600746240, s1P 1235224825106, s1P 3786119185458, s1P 2535177164132,
   s1N 1436251055567, s1N 3855452163019, s1N 3488580491918, s1N 355074634014, s1P 924681345987,
   s1N 2231098460144, s1N 261133804385, s1N 5481080240116, s1N 335803084920, s1N 6725730708965,
   s1P 2823431634517, s1N 4831724039921, s1N 7103065397726, s1P 4151568533915,
   s1P 134746507111, s1P 65965522524, s1P 4457792247692, s1P 6987380561188, s1P 1911986934328,
   s1P 12648988246037, s1P 39393190966367, s1P 80586808138964, s1P 131581375465579,
   s1P 182603383155201, s1P 227518196672425]
private def s1V5S5 : List ℤ :=
  [s1P 265644163743281, s1P 297529379983686, s1P 318837937923868, s1P 329070998327042,
   s1P 323425101144184, s1P 310824032946938, s1P 286905668889958, s1P 258711266214862,
   s1P 229341216898943, s1P 195834435289547, s1P 165410419422636, s1P 140497220369294,
   s1P 114864252653963, s1P 89836930778911, s1P 69219352233951, s1P 52501845255711,
   s1P 37484584489364, s1P 23793446757822, s1P 12906715848053, s1N 5969237132387,
   s1P 2509786398767, s1P 1113542373896, s1P 580480236813, s1P 331242707881, s1P 192311927794,
   s1P 120920321837, s1N 88978106712, s1P 73019850494, s1P 59823402870, s1P 46186608549,
   s1P 33374548215, s1P 22642527806, s1P 14483993542, s1P 8865311949, s1P 5286903020,
   s1P 3074259183, s1P 1708663991, s1P 889040646, s1P 432156068, s1P 201310420, s1P 94319678,
   s1N 46571510, s1P 24498856, s1P 13331283, s1P 7226291, s1P 3823510, s1P 1967433, s1P 983010,
   s1P 472529, s1P 215846, s1P 93464, s1P 38988, s1P 16132, s1P 6766, s1P 2872, s1P 1210,
   s1P 498, s1P 198, s1P 75, s1P 25, s1P 6, s1P 1, s1P 0, s1P 0]
private def s1V5 : List ℤ :=
  s1V5S0 ++
    (s1V5S1 ++
    (s1V5S2 ++
    (s1V5S3 ++
    (s1V5S4 ++
    (s1V5S5 ++
    (mm16k512krS1VecIn5 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V6S0 : List ℤ :=
  [s1P 80421525, s1P 276376375, s1P 354203469, s1N 195815237, s1N 314723687, s1N 304958581,
   s1N 25570691, s1P 868020052, s1P 641269092, s1P 518134072, s1P 558159255, s1N 585546630,
   s1P 54798299, s1P 1347114807, s1P 664589888, s1P 327608894, s1P 852295933, s1P 210658914,
   s1P 970087483, s1P 9550620, s1P 1174068913, s1P 808783240, s1P 697934728, s1P 1092417543,
   s1P 3312494583, s1P 1329803294, s1P 469249015, s1P 742379210, s1P 2336918942,
   s1N 1407750494, s1N 2334989853, s1N 540013797, s1N 334563367, s1N 1323237087,
   s1N 6080436373, s1P 2078945604, s1P 421086487, s1P 1890848424, s1N 2703246401,
   s1N 724817800, s1N 978736810, s1P 3331996086, s1P 1792784880, s1P 344595776, s1P 1085309279,
   s1P 4875063974, s1P 2694557476, s1P 556644676, s1N 2217589639, s1N 2638526310,
   s1N 13731179064, s1N 18059383668, s1N 11708517181, s1N 696595186, s1P 8433604093,
   s1P 3411200026, s1N 5193225185, s1N 12317006315, s1N 4322406568, s1N 7432991895,
   s1N 10873183291, s1P 3208644335, s1P 9355512748, s1P 13934530097]
private def s1V6S1 : List ℤ :=
  [s1N 4308331576, s1N 5306333059, s1N 25091851425, s1N 6945667574, s1N 19444999792,
   s1N 19614320523, s1N 30204805840, s1N 27756762867, s1N 24524270988, s1N 23675190143,
   s1N 22222919416, s1N 4125076933, s1P 22212091953, s1P 35232084728, s1P 34246565055,
   s1N 29349663117, s1N 29558516242, s1N 5676670959, s1P 18246774496, s1P 345592712,
   s1N 1215261208, s1N 25346063405, s1N 9135671332, s1N 25902360611, s1N 14780371930,
   s1P 3299472513, s1P 8795330881, s1P 7574726439, s1N 12672516021, s1N 129680914,
   s1N 70529608792, s1N 49409220788, s1N 93276938405, s1N 33268057026, s1N 42165182178,
   s1N 35573216273, s1N 28471041636, s1N 26185715873, s1P 43899640103, s1P 13106790717,
   s1N 55504175354, s1N 10326323872, s1P 8221957807, s1N 71636603950, s1N 19920917362,
   s1N 43230933179, s1N 36470235517, s1N 4988792749, s1N 81991779236, s1N 19325096605,
   s1P 30146251378, s1P 1777247, s1P 31060688166, s1P 45407813239, s1P 25544429910,
   s1P 116551530552, s1P 59563299064, s1P 154886340267, s1P 106131889306, s1P 155762320186,
   s1P 48223335148, s1N 140721459470, s1N 209204443763, s1N 61969856750]
private def s1V6S2 : List ℤ :=
  [s1P 171428619270, s1P 305870658315, s1P 49795495402, s1N 129549096477, s1N 76203454202,
   s1N 33183090953, s1P 92528945268, s1N 87647719023, s1N 89456841801, s1P 151454570725,
   s1P 87203623107, s1N 115222402625, s1P 82572194858, s1P 5192423322, s1P 6499177226,
   s1N 39920124276, s1N 118085267846, s1P 20083303368, s1N 132457625545, s1N 104085696216,
   s1N 69462861011, s1N 103174666314, s1N 14893794558, s1N 33809497785, s1N 195498210072,
   s1N 176778772912, s1N 247787627994, s1P 48058082964, s1P 75103678290, s1P 489859921265,
   s1P 549093197221, s1P 63610522963, s1P 87857949970, s1P 457441097194, s1P 330289161827,
   s1N 245390799063, s1P 12706974931, s1P 184263681969, s1P 139502892108, s1N 5963554220,
   s1P 16848109496, s1N 310769458342, s1N 220168526840, s1P 78665062095, s1N 212404922427,
   s1N 22288544485, s1P 36692279404, s1N 203950039580, s1N 8291391864, s1N 714398277287,
   s1N 463972077193, s1N 670138222700, s1P 129590350464, s1N 156905815495, s1P 273176855086,
   s1P 308924858119, s1P 124446704317, s1P 435544532573, s1N 399007184929, s1P 353284104304,
   s1P 186507084712, s1N 390915526363, s1N 128673944285, s1P 72078760687]
private def s1V6S3 : List ℤ :=
  [s1P 195077564369, s1N 139347946091, s1N 1135971542334, s1N 1306854766357, s1N 1277780641510,
   s1N 888310847723, s1P 1092745973858, s1P 1116791325621, s1P 497402314202, s1P 707952637534,
   s1P 665780597437, s1N 442967215013, s1P 412114052521, s1P 593412314987, s1P 769440219580,
   s1P 1288212559242, s1P 2045760631856, s1P 1979911087442, s1P 987011281827,
   s1P 1612708902158, s1P 3279152732780, s1P 2368066726130, s1P 1846255625066,
   s1P 1637891968174, s1P 992468703133, s1N 1989672657981, s1N 2973277273647, s1N 896762794901,
   s1N 3058064650720, s1N 773066005537, s1P 732738347436, s1P 1269540984083, s1N 733816995315,
   s1N 759633093376, s1N 313726816566, s1N 2838363145171, s1N 3180819394948, s1N 3275632359322,
   s1N 739043647205, s1N 4400698312579, s1N 222304398410, s1N 2752324662011, s1N 506837785850,
   s1N 2718615197811, s1N 1299667503537, s1N 797351642291, s1P 2596311637864,
   s1N 1868553729478, s1P 1031290066506, s1P 4001738935111, s1N 1631774130403,
   s1P 3430226232237, s1P 5805845575169, s1P 1784421587388, s1P 4038185812192,
   s1P 2150093391370, s1P 869453691390, s1N 2390407292334, s1N 916959059961, s1N 1769831772884,
   s1N 3770551247800, s1N 6935692637429, s1N 2440537596850, s1N 412805563580]
private def s1V6S4 : List ℤ :=
  [s1P 1001294090353, s1P 1692404520094, s1P 3016930311248, s1P 4468338402778,
   s1N 2950623234201, s1N 1021757720846, s1N 2871133520459, s1N 4001703183444,
   s1P 2075287879305, s1N 1399699990670, s1N 1821035241492, s1P 682009448057, s1P 906621225484,
   s1N 4106489963385, s1P 2272365023355, s1P 1212618926859, s1N 3705190669827,
   s1N 1182360944093, s1P 2214297501683, s1N 5259579607845, s1N 93026607696, s1N 1408458567377,
   s1N 2216398772487, s1P 767447195477, s1P 959641806883, s1N 751901149072, s1N 2979588853034,
   s1N 253237163791, s1P 3442936372710, s1P 3238987924084, s1N 358785983943, s1N 1735954427043,
   s1P 942034055584, s1P 78980144550, s1N 245599486118, s1N 1910170308308, s1P 1288218111754,
   s1P 3754372720235, s1N 1518335615609, s1P 5428565465138, s1N 1999672848600,
   s1N 583832393600, s1P 3623000090304, s1P 2937305206625, s1P 7134167934491, s1N 86631882878,
   s1N 1846217845053, s1P 1689474711672, s1N 4271844230613, s1P 4104828720275,
   s1P 3808368735264, s1P 398081913885, s1P 4961885381681, s1P 256871867532, s1N 168166236064,
   s1N 3860638912703, s1N 3470839014006, s1P 971216335675, s1P 3681416231375,
   s1P 4744870599009, s1N 4682300333257, s1N 2010366560651, s1P 5706143014747,
   s1P 4200815557764]
private def s1V6S5 : List ℤ :=
  [s1P 2739455422609, s1P 11265734374000, s1P 5987516862034, s1P 15863662810554,
   s1P 49616153159187, s1P 94682771768662, s1P 143558445778866, s1P 190764115717072,
   s1P 238884042170623, s1P 278368069061707, s1P 310064959520036, s1P 320911323047144,
   s1P 334207995796580, s1P 320234983570605, s1P 304845604227612, s1P 280418501297226,
   s1P 245806125510106, s1P 218509076671381, s1P 191207790949239, s1P 157174982988926,
   s1P 126305949694655, s1P 104774134285765, s1P 86150879346509, s1P 65010803872445,
   s1P 43404794408477, s1P 25607263693730, s1P 13595791415350, s1P 6773807268240,
   s1P 3380376376835, s1P 1766244342940, s1P 941340485579, s1P 482903142079, s1P 236754636922,
   s1P 122633193256, s1P 78926440560, s1P 62917497402, s1P 53393413635, s1P 43418813131,
   s1P 32908651231, s1P 23399938187, s1P 15729948244, s1P 10050306700, s1P 6165043659,
   s1P 3660848740, s1P 2091384899, s1P 1128314246, s1P 566041158, s1P 264500131, s1P 118247663,
   s1P 53239577, s1P 25487316, s1P 13206143, s1P 7196688, s1P 3953873, s1P 2126833,
   s1P 1104834, s1P 551831, s1P 265058, s1P 122753, s1P 55039, s1P 24011, s1N 10243, s1P 4293,
   s1P 1767]
private def s1V6S6 : List ℤ :=
  [s1P 712, s1P 278, s1P 101, s1P 32, s1P 8, s1P 1, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V6 : List ℤ :=
  s1V6S0 ++
    (s1V6S1 ++
    (s1V6S2 ++
    (s1V6S3 ++
    (s1V6S4 ++
    (s1V6S5 ++
    (s1V6S6 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V7S0 : List ℤ :=
  [s1P 10882378, s1P 27394602, s1N 342125261, s1N 359286564, s1N 19768890, s1N 119359341,
   s1N 368869348, s1N 684615743, s1N 213632435, s1P 190293285, s1P 161478839, s1P 1150922466,
   s1P 1016394471, s1N 683498777, s1N 235854710, s1N 183417024, s1N 981008033, s1N 417565623,
   s1N 631575415, s1P 348353509, s1P 1332813339, s1P 385259175, s1N 566349897, s1P 850977619,
   s1N 1364016397, s1N 692107154, s1N 300691690, s1N 3434702462, s1N 666222034, s1P 2694595650,
   s1P 1801923796, s1P 4855765610, s1N 1488590705, s1N 124881175, s1N 2373391181,
   s1N 1679565463, s1N 308865657, s1P 1385924768, s1P 3622672226, s1P 2639569279,
   s1N 1574934790, s1P 2620518484, s1P 59308159, s1N 1251174040, s1N 3193365292, s1P 945763201,
   s1P 2637393462, s1N 2138705318, s1P 690868077, s1P 1823741033, s1N 3928027535,
   s1N 388112017, s1P 2554971786, s1P 5954165605, s1P 2623316318, s1P 5095841308,
   s1P 17167759792, s1P 16312069445, s1P 18645518814, s1P 6555753331, s1N 6498617977,
   s1N 4072967439, s1P 1531121839, s1P 378274651]
private def s1V7S1 : List ℤ :=
  [s1P 3892869132, s1P 12024247241, s1P 15351898497, s1P 7595943206, s1N 7192810617,
   s1N 9220676552, s1N 13711768127, s1N 11696830602, s1P 3958450230, s1P 11227519776,
   s1N 6998738507, s1N 14769805918, s1P 16994723427, s1P 35931471635, s1N 4270694175,
   s1N 23655537168, s1N 45861632764, s1N 46174477249, s1P 19063606171, s1P 38015643837,
   s1P 23484143340, s1N 26742929208, s1N 31289588369, s1N 17043634059, s1P 25605710077,
   s1N 8800486255, s1N 4995057639, s1P 1772569783, s1N 5379930183, s1P 31366943737,
   s1N 9707771355, s1N 17842687456, s1N 23717260443, s1N 500785456, s1N 9653521625,
   s1N 4934168449, s1N 57419882367, s1P 34511254450, s1P 87978739538, s1N 1557411728,
   s1N 57591466030, s1N 66837471521, s1N 60386314034, s1N 67548986675, s1N 10779482803,
   s1N 14054747287, s1N 65533617400, s1N 51728086540, s1P 23918690403, s1N 11363629953,
   s1N 48612536828, s1P 25100014512, s1N 10494718668, s1N 31335857608, s1N 38803673761,
   s1P 38505600576, s1N 77065211033, s1P 4053043495, s1P 9772917914, s1P 43379636967,
   s1P 38042308699, s1N 22892703153, s1N 89979300991, s1N 35459640946]
private def s1V7S2 : List ℤ :=
  [s1N 50857772661, s1N 86697222779, s1N 274917545334, s1N 221114355750, s1N 186827633472,
   s1N 228935159867, s1N 292109759493, s1N 119846845658, s1N 97145400492, s1P 94648454501,
   s1P 29999508245, s1N 68986515940, s1N 81380420891, s1N 84303240453, s1P 91727408369,
   s1P 56523757079, s1P 76323160865, s1N 69149136715, s1N 56207183282, s1P 74459771113,
   s1P 23066119000, s1P 9662871978, s1P 78509725041, s1P 103173531120, s1N 39270743982,
   s1N 33080667367, s1P 93093202131, s1P 225652041941, s1P 86260142933, s1N 139272302361,
   s1N 202105363977, s1N 142122182604, s1N 183429554481, s1N 398235448622, s1N 572062461985,
   s1P 43197861852, s1N 55004209221, s1N 30685005368, s1N 364898138113, s1P 45574396833,
   s1P 631142736148, s1P 225655034968, s1P 410439804217, s1P 102926570048, s1P 163024522516,
   s1P 133742574646, s1N 96823290629, s1N 395400493197, s1N 342734729933, s1P 235026779240,
   s1N 163878662373, s1N 187068508248, s1N 66929494807, s1P 384459115146, s1P 200769332642,
   s1P 305429101931, s1P 295330582536, s1N 167300175530, s1N 274877176666, s1N 703259950814,
   s1N 443526598577, s1N 604753433155, s1P 278974547749, s1P 130124063962]
private def s1V7S3 : List ℤ :=
  [s1P 230257352692, s1P 158031882198, s1P 692395682215, s1N 232761143334, s1P 365788959123,
   s1P 90783188391, s1P 771373193048, s1P 34362885266, s1N 879610712752, s1N 458165693576,
   s1P 293793816323, s1N 1139586304955, s1N 1075319296537, s1N 1796129726164, s1N 605713455552,
   s1N 599610571826, s1N 142786684789, s1P 696860900898, s1N 382499520887, s1N 1853197844632,
   s1N 1415871680223, s1N 228633272808, s1P 1389012692075, s1P 524975313291, s1N 671406861767,
   s1P 1397765806401, s1P 2268375994612, s1N 327396950710, s1P 2759412655760,
   s1P 1724180692952, s1P 4202457921359, s1N 510811010335, s1P 4618388515161, s1N 748000064472,
   s1N 833518143307, s1N 2523242444504, s1P 982878464816, s1N 2886215593273, s1N 688549111907,
   s1N 314520187762, s1P 218187073933, s1P 2620592363176, s1P 2422460999191, s1P 927857487646,
   s1N 1440788318758, s1N 6099683578774, s1N 1976125603422, s1N 1126870392669,
   s1N 2747965216664, s1N 3064915646584, s1P 482192249863, s1N 2924058284348,
   s1N 2481548284391, s1P 1704170707036, s1N 557883409364, s1N 705937281091, s1N 1124426814105,
   s1N 2054627320052, s1P 738519494304, s1N 1404514876997, s1N 1377966524662,
   s1P 5573971508869, s1P 5352579107705, s1P 754824134703]
private def s1V7S4 : List ℤ :=
  [s1P 4582685083682, s1P 2404964272733, s1P 288877281447, s1N 620728176446, s1P 1778046817085,
   s1P 6366942686748, s1N 2486322807301, s1P 4337117902893, s1P 4381213137718,
   s1N 1744729142599, s1P 6167961351224, s1N 1700489939362, s1P 3465273708228,
   s1P 1287916328338, s1N 5040093986918, s1P 666386382013, s1P 210020717935, s1N 1952315035330,
   s1N 1344903837694, s1N 313839076704, s1N 781179784568, s1N 648259631792, s1N 620319822750,
   s1N 780800122676, s1N 715755459288, s1N 897520098763, s1N 1005919927989, s1P 1096191072111,
   s1N 5371792353766, s1N 245245776032, s1P 1699229057393, s1P 4099841773693,
   s1P 3780040752231, s1P 4260463510767, s1N 2612931399221, s1N 1800637385791,
   s1P 1997738988376, s1P 1563629982067, s1P 760992703140, s1P 3553377597964,
   s1N 2397566902240, s1N 1737643210335, s1N 629371987255, s1P 4993205284093,
   s1P 4524719914636, s1P 1367002549628, s1N 1667435489982, s1N 851651641714,
   s1N 2043487886114, s1N 613015402751, s1P 2341666337534, s1P 6482158032528,
   s1P 2598544228461, s1P 1948372593715, s1N 162425945399, s1N 1052339151319, s1P 40425280434,
   s1N 2279108192274, s1N 2744841956541, s1P 6965926907613, s1P 8653369124340,
   s1N 4088155381961, s1N 3436412989213, s1N 302527134944]
private def s1V7S5 : List ℤ :=
  [s1P 249767689110, s1P 1178842747951, s1P 5600931968160, s1N 2464343670688,
   s1N 1617802636661, s1N 4733414428731, s1N 7742853572278, s1N 10693715903918,
   s1N 802867402152, s1P 4455690734837, s1P 6128691092040, s1P 3558516896601,
   s1P 32034596951878, s1P 68662190815655, s1P 113986940164185, s1P 168084516019529,
   s1P 217744135503617, s1P 258952309633887, s1P 296487904447196, s1P 324216654667371,
   s1P 332799048491248, s1P 325761731899313, s1P 312097478324374, s1P 293229967748904,
   s1P 266140379220700, s1P 232476522401478, s1P 198536689456167, s1P 168840347346480,
   s1P 143003864473037, s1P 118224679108167, s1P 93011918781364, s1P 68412057749636,
   s1P 46723526513675, s1P 29701571458524, s1P 17728058976852, s1P 10056302930122,
   s1P 5487222141488, s1P 2906181682904, s1P 1502743701371, s1P 764737791881, s1P 391030297963,
   s1P 209532050688, s1P 123840987575, s1P 82275268111, s1P 59321043655, s1P 43890043228,
   s1P 31993270764, s1N 22539399917, s1P 15259847745, s1P 9925825266, s1P 6203893778,
   s1P 3721137555, s1P 2136837527, s1P 1172616183, s1P 615268524, s1P 309994721, s1P 151361741,
   s1P 72591582, s1P 34755216, s1P 16862299, s1P 8340192, s1P 4189461, s1P 2123960, s1P 1077391]
private def s1V7S6 : List ℤ :=
  [s1P 537271, s1P 257191, s1P 116059, s1P 49250, s1P 19976, s1P 7988, s1P 3250, s1P 1362,
   s1N 574, s1P 235, s1P 90, s1P 30, s1P 9, s1P 1, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V7 : List ℤ :=
  s1V7S0 ++
    (s1V7S1 ++
    (s1V7S2 ++
    (s1V7S3 ++
    (s1V7S4 ++
    (s1V7S5 ++
    (s1V7S6 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V8S0 : List ℤ :=
  [s1N 46554620, s1P 111654554, s1P 103490450, s1N 266170064, s1N 288701912, s1P 277749831,
   s1N 20101831, s1P 167350071, s1P 497635165, s1P 633467804, s1P 97758215, s1P 706312489,
   s1N 661435545, s1P 1068336620, s1P 752035145, s1P 572846873, s1N 398619596, s1N 1743923,
   s1N 545713035, s1N 684347243, s1P 1468282622, s1P 1462515111, s1P 812084467, s1N 502042620,
   s1N 169001338, s1N 2914775256, s1N 2318833168, s1N 1576792484, s1N 528808324, s1P 572474184,
   s1P 289232637, s1P 2760739523, s1P 2792932809, s1P 540904849, s1N 296205883, s1N 4489189575,
   s1N 736959162, s1P 2499101091, s1P 1224670161, s1P 2062894721, s1P 2994582593,
   s1P 1987936779, s1P 2481019477, s1N 1909816608, s1N 2201475693, s1P 4612790332,
   s1N 3034533192, s1N 534170621, s1N 248266082, s1N 1288941478, s1N 2003085804,
   s1N 4800860378, s1N 1092566887, s1P 4527978346, s1P 1351199342, s1P 2170660119,
   s1P 865086106, s1N 1448781559, s1P 2549101206, s1P 3364163999, s1N 4351519521,
   s1P 796938912, s1P 8672081592, s1P 20470595540]
private def s1V8S1 : List ℤ :=
  [s1P 18491368804, s1P 9620159657, s1P 8337781816, s1P 6752992727, s1N 4406938959,
   s1N 6156500281, s1N 2377162892, s1N 10873038175, s1N 1991342058, s1N 11696271946,
   s1N 34150803075, s1N 14214806974, s1N 16447544658, s1N 9693677904, s1N 8176193814,
   s1P 4858162528, s1N 2960412992, s1N 27144346719, s1P 11730705623, s1P 21167920819,
   s1P 27178618681, s1P 49974087755, s1P 33479688257, s1P 53471649709, s1P 40701490732,
   s1P 8008022634, s1P 13611248062, s1P 29175258279, s1P 25882714279, s1P 11568707155,
   s1P 4107883361, s1N 17314276797, s1P 14583147434, s1P 20816662006, s1N 27249259993,
   s1P 21654669840, s1P 46658673542, s1P 26089155173, s1P 37257769437, s1P 26349742325,
   s1P 31942366655, s1N 28459482785, s1N 60774570440, s1P 1999863975, s1P 49153449003,
   s1P 48471042737, s1P 60720018338, s1P 54148767488, s1P 92824530098, s1P 12210626257,
   s1N 22870630345, s1N 72488035262, s1P 45280290259, s1P 14702400010, s1P 73668520848,
   s1P 19722548895, s1N 52537300640, s1P 13401753437, s1N 33975158193, s1P 2431769920,
   s1N 33896466366, s1N 14503173569, s1P 17609992666, s1N 31908379246]
private def s1V8S2 : List ℤ :=
  [s1N 137292062381, s1P 34100176504, s1N 96843768361, s1N 487589297, s1N 17198172048,
   s1N 61171797692, s1N 53839927411, s1P 13955982925, s1P 17611219478, s1P 78339473302,
   s1P 138673964438, s1P 73514311346, s1N 169214304349, s1N 258932648197, s1N 307644196009,
   s1N 281682411218, s1N 189849847517, s1P 24147741940, s1P 16123770551, s1P 113455564641,
   s1P 125955878368, s1P 12159709294, s1P 8679721208, s1N 26589536940, s1N 61408008307,
   s1P 180972592562, s1P 127162721043, s1N 52648009532, s1N 133750833664, s1P 59180130341,
   s1P 297950181804, s1P 151449583087, s1P 19399372778, s1N 189371346404, s1N 294747147982,
   s1N 224267835458, s1N 183682434902, s1N 71055397703, s1N 239646219370, s1N 167773701774,
   s1N 432319100557, s1N 264580700514, s1N 378954251504, s1N 71700989619, s1P 118567686927,
   s1P 384483821073, s1P 448204082220, s1N 112128769443, s1N 360861949525, s1N 194836714521,
   s1P 273176437044, s1P 319901267326, s1P 674129408100, s1P 4364758904, s1P 201879346424,
   s1P 170757340976, s1P 83451946377, s1N 346836304824, s1N 229967246621, s1N 612625107362,
   s1N 16361784587, s1N 53882950584, s1N 68945748977, s1N 165009137765]
private def s1V8S3 : List ℤ :=
  [s1N 631301303327, s1N 204272923179, s1N 555170863300, s1N 900673481610, s1N 26535130341,
   s1N 349705174951, s1N 852811998592, s1N 377622608587, s1P 221559583776, s1N 553414329069,
   s1P 54223017991, s1P 606119607267, s1N 767802127387, s1N 693521243582, s1P 113095942129,
   s1P 95136110281, s1N 415526159962, s1N 640877960830, s1N 1326718371517, s1N 2059596461818,
   s1N 2063376251769, s1N 2873891383936, s1N 880567838521, s1P 3349750094436,
   s1P 2685594683283, s1P 698515622840, s1P 714465160236, s1N 1319844148781, s1N 577364784070,
   s1N 2328580036877, s1P 785111323538, s1P 1416008368541, s1N 1006770312612, s1P 289218079186,
   s1P 1912478389100, s1P 226347834208, s1P 1378504193135, s1P 87700453678, s1P 2829190359471,
   s1P 3230724034258, s1P 2594843740572, s1P 1765755763414, s1P 2177450081119,
   s1N 601448611307, s1N 1206843528610, s1P 2212753040193, s1P 2906591245625,
   s1P 4888708297609, s1P 792867223921, s1P 1093650439371, s1P 2124775928683,
   s1P 2876472690534, s1N 278486721580, s1N 899282239001, s1P 1782624439264, s1P 4558466294745,
   s1P 631158258684, s1N 1773272818313, s1N 6035967095858, s1P 70972317300, s1P 2158379897629,
   s1P 449461685581, s1N 3264967961501, s1N 406240936062]
private def s1V8S4 : List ℤ :=
  [s1N 4382794435808, s1N 7783920962068, s1N 2071397538714, s1P 1530904534566,
   s1N 4188696441984, s1P 2491492511555, s1P 734437390933, s1N 5346834849781,
   s1P 4207987846202, s1P 499938827022, s1P 3144029990280, s1P 2424120256392, s1P 802989418468,
   s1P 1854198944732, s1P 3868031991387, s1N 1949569972054, s1N 375202400673,
   s1P 3452819724344, s1P 2046520096313, s1P 4980046531607, s1N 166418752990,
   s1P 2381215442249, s1P 353702059518, s1N 882469037091, s1P 770087911854, s1P 805569234677,
   s1P 3073723237524, s1P 1059736061749, s1P 1015499917015, s1P 936966300939,
   s1N 2778117855891, s1N 1267454147848, s1N 2835605301695, s1N 1278162447661,
   s1N 1351916576587, s1N 2264773071983, s1N 5098123835002, s1N 2119644381750,
   s1P 561076459688, s1P 3235379511972, s1P 3100509892667, s1N 3881354798901, s1N 221742723568,
   s1P 1350319520735, s1P 701334734273, s1P 4685315066518, s1P 3316952260239,
   s1N 1521109086091, s1P 1353484283800, s1P 755342728084, s1N 319334863127, s1P 2894811584810,
   s1N 4607772913290, s1N 1284593042340, s1N 3402999225806, s1N 4114095133210,
   s1P 4434591861511, s1P 2420063928617, s1P 4998299379984, s1P 3668643488998,
   s1P 5493579926172, s1P 6790249779858, s1N 1845016429088, s1P 4135621524608]
private def s1V8S5 : List ℤ :=
  [s1P 2124600673612, s1N 3219078860960, s1N 5331388540264, s1P 4026080024202,
   s1P 3496234945916, s1N 3209689958695, s1P 1033593566307, s1N 2633266769654,
   s1P 3312520455916, s1P 300784458201, s1P 8746503369270, s1P 4168368957718,
   s1P 6460326734124, s1N 8714005117764, s1P 5678078866816, s1N 2288818629584,
   s1P 427286063413, s1P 4688708970960, s1P 11781006224611, s1P 7937650129425,
   s1P 13635542609902, s1P 46963147676754, s1P 87000372474129, s1P 135343138948853,
   s1P 190570319793931, s1P 243391869248209, s1P 284532384679117, s1P 311890218606513,
   s1P 327777094871765, s1P 332838966512074, s1P 325416106969149, s1P 305484530455405,
   s1P 276895328988230, s1P 245309665084440, s1P 214655633698714, s1P 185696382396757,
   s1P 157341311702246, s1P 128779401928892, s1P 100628184414038, s1P 74510347461752,
   s1P 52209107410410, s1P 34601935001385, s1P 21823368802477, s1P 13127655582063,
   s1P 7556801858876, s1P 4213527985615, s1P 2279174815914, s1P 1188211510831,
   s1P 615627280940, s1P 338802306177, s1P 199118383491, s1P 115462169310, s1N 62474536423,
   s1P 32832057310, s1P 19020815762, s1P 13115248885, s1P 9938746418, s1P 7416804992,
   s1P 5187517469, s1P 3373321588, s1P 2052621857, s1P 1179630832, s1P 645897510, s1P 339614418]
private def s1V8S6 : List ℤ :=
  [s1P 172787941, s1P 85734314, s1P 41828137, s1P 20231744, s1P 9769522, s1P 4729883,
   s1P 2296238, s1P 1111858, s1P 532437, s1P 250423, s1P 115119, s1P 51362, s1P 22005,
   s1P 8970, s1P 3472, s1P 1288, s1P 466, s1P 167, s1P 55, s1P 14, s1P 4, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0]
private def s1V8 : List ℤ :=
  s1V8S0 ++
    (s1V8S1 ++
    (s1V8S2 ++
    (s1V8S3 ++
    (s1V8S4 ++
    (s1V8S5 ++
    (s1V8S6 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V9S0 : List ℤ :=
  [s1P 63437054, s1P 51572343, s1N 92114207, s1P 332006197, s1N 265905067, s1P 228001919,
   s1P 135287526, s1P 324873624, s1P 666972145, s1P 747294775, s1N 321257814, s1P 556933781,
   s1N 631456552, s1N 580920338, s1N 198706963, s1N 320260730, s1N 1114633975, s1N 261754610,
   s1P 684176484, s1N 383802417, s1N 1092420124, s1N 1330063139, s1N 889130465, s1N 355788613,
   s1P 87935983, s1P 1241326046, s1N 1004602987, s1N 1106859006, s1N 1171097920,
   s1N 2630433531, s1N 1129054761, s1N 1963108075, s1N 2348996436, s1N 352061490,
   s1P 1320936464, s1N 1253553230, s1P 3661476273, s1P 3883441508, s1P 366383220,
   s1N 1535179112, s1N 5243125739, s1P 831235003, s1P 770179083, s1N 2916353590,
   s1P 1676529452, s1P 4052689035, s1P 2583040627, s1P 2355577742, s1N 1001584701,
   s1P 1876216616, s1N 1998402304, s1N 2181326010, s1P 1248108824, s1P 3433765694,
   s1N 1722250946, s1P 513329951, s1P 3015170070, s1P 5342402804, s1P 2092153140,
   s1N 1755754674, s1P 2940117667, s1N 237215618, s1P 2345468724, s1N 807058131]
private def s1V9S1 : List ℤ :=
  [s1N 10897439707, s1P 1208789790, s1P 10584282575, s1P 4752251517, s1N 7572617443,
   s1P 11896843529, s1P 15014212128, s1P 9559046030, s1P 17633920170, s1P 13524325348,
   s1P 15908049530, s1P 10807562601, s1P 3755901425, s1N 16901721773, s1N 16199825284,
   s1N 135901052, s1N 1743293618, s1N 22501376481, s1N 20829903977, s1N 26704628357,
   s1N 13401058672, s1N 2238890540, s1N 1670580913, s1N 25946311927, s1N 10766392689,
   s1P 3816936713, s1P 19558626612, s1P 13975321055, s1P 21263074616, s1P 24983843927,
   s1P 77219487989, s1P 31087563815, s1N 11424832449, s1N 31872354090, s1N 41360345228,
   s1N 30314979106, s1N 8373796446, s1P 5249636088, s1P 47641696122, s1P 18718437930,
   s1P 3352747191, s1P 15547833918, s1P 40600335494, s1P 32259529124, s1P 17871889499,
   s1P 16584234625, s1P 75120587485, s1P 79563689666, s1P 44202907198, s1P 18593189833,
   s1N 25832546905, s1N 9590796139, s1P 15087024792, s1P 3386686305, s1N 28011016833,
   s1N 143373137127, s1N 31987415113, s1P 110399381940, s1P 73330716629, s1P 29741475370,
   s1N 56920121903, s1N 3286952730, s1P 1073686878, s1N 65311782685]
private def s1V9S2 : List ℤ :=
  [s1P 10643130737, s1N 3032464619, s1N 19009637924, s1P 11863381888, s1P 39493146620,
   s1N 47073833883, s1N 2336643880, s1P 41106596035, s1N 67696922198, s1N 8908624034,
   s1P 79835832155, s1P 61710152696, s1P 39154638386, s1N 39403957287, s1N 103550182114,
   s1N 43594676474, s1N 117251554221, s1N 65207596497, s1N 159566934951, s1N 117534259519,
   s1N 123847531583, s1P 67350805509, s1P 199211121813, s1P 306983522996, s1P 245433594732,
   s1N 197777810085, s1N 258944423346, s1N 58391517488, s1N 118970299384, s1N 170567544194,
   s1P 184954889356, s1P 11739185592, s1P 8639008920, s1P 210766526127, s1N 85263826762,
   s1P 69435929614, s1N 71188718425, s1N 110348566732, s1N 206204033954, s1N 170710235782,
   s1N 256359185057, s1N 16614812378, s1P 40614386280, s1N 400621555902, s1P 64528938260,
   s1N 249543069310, s1P 181308466106, s1N 114495646587, s1N 32747274466, s1P 477204354474,
   s1P 335346613065, s1P 702063854078, s1P 296205930685, s1P 415322345563, s1P 276360066896,
   s1P 285276456499, s1P 236918735814, s1N 311012035504, s1N 166150382123, s1P 112641683053,
   s1P 359659449494, s1N 235618341649, s1N 76881692483, s1P 457198334828]
private def s1V9S3 : List ℤ :=
  [s1P 696179840877, s1N 178099972458, s1N 399974254463, s1P 341169376314, s1P 630779356313,
   s1P 527476425953, s1P 461338234601, s1P 83585269385, s1N 531570982480, s1N 58189843733,
   s1P 108732557319, s1P 962805250255, s1N 335520110158, s1P 59867434645, s1N 886618088840,
   s1N 640561798112, s1P 312294191468, s1P 1269010043929, s1P 1614433075283, s1P 906962077320,
   s1P 554633020719, s1P 111485816120, s1N 104883405721, s1P 348007213926, s1P 1084988471317,
   s1N 377819789150, s1N 2582034783727, s1N 2425130891374, s1N 2175530431860,
   s1N 2750670554719, s1N 2878954963316, s1N 1566639390999, s1P 1285964832882,
   s1P 2490222307004, s1P 1784400939702, s1N 276452624713, s1N 1406672406438,
   s1N 1506933919110, s1N 1724190338907, s1N 759114897048, s1N 281625861879, s1N 754653172939,
   s1N 226929919465, s1P 355611045127, s1P 116045115408, s1P 1237225588766, s1N 461582463458,
   s1N 1730417720152, s1P 2019928546122, s1P 6324046737450, s1P 1566023916963,
   s1N 567293718420, s1N 671470625739, s1N 2260488671022, s1P 1737433200320, s1N 1769351194919,
   s1P 499355420696, s1N 3024146434031, s1N 5379482707840, s1N 3126754572071,
   s1N 4877250570792, s1P 587856504403, s1P 7668492462307, s1N 2153935568088]
private def s1V9S4 : List ℤ :=
  [s1P 5212593771019, s1N 485775578177, s1N 4225177201689, s1P 941889630319, s1N 265598461398,
   s1P 553036500980, s1P 2442651619128, s1P 478333408000, s1N 3944194452518, s1P 2561979561452,
   s1N 7728557651178, s1P 744412805867, s1N 737059409680, s1P 2021464461067, s1P 2156433049731,
   s1P 2007675292539, s1P 1684197724240, s1N 543222001281, s1P 206790373109, s1P 2187279351108,
   s1N 2965563936497, s1N 3937895349252, s1P 400433763900, s1N 1350603998630, s1P 242881068573,
   s1N 667203803099, s1P 1887828439500, s1P 3673367672716, s1P 2527990799198,
   s1P 2513733045593, s1N 1313318741766, s1N 949374667730, s1P 1817448973403, s1P 776164265901,
   s1P 1649625754993, s1P 2986074830877, s1P 1252921207786, s1P 2632669500350,
   s1P 665714810633, s1P 4398806326298, s1N 1205386518058, s1P 1903824805313,
   s1P 4604528249352, s1P 1579796820017, s1P 6872115477546, s1P 2461174670496,
   s1P 2025697410936, s1P 846252730655, s1P 3222691484577, s1N 3445891198400,
   s1N 1595820162932, s1P 2046648467714, s1P 490759502212, s1P 4303715269802, s1N 254925959608,
   s1P 3378408855785, s1N 745014148560, s1N 667039271044, s1P 4438369680051, s1P 1663181610300,
   s1N 3542159926428, s1N 4232146382986, s1N 2335588214701, s1N 8389762217817]
private def s1V9S5 : List ℤ :=
  [s1P 898896655835, s1P 2207364612126, s1P 6522173404444, s1N 2520813057424,
   s1P 9148121542499, s1P 2818618728822, s1P 10205360148241, s1P 3120364268675,
   s1N 501057787816, s1N 1382221823722, s1N 2295357514317, s1N 587210526568, s1P 3776134097346,
   s1P 420517608378, s1N 7288082325410, s1N 171888784538, s1P 4668988322128, s1P 652884827979,
   s1P 4643514848202, s1P 9202531560620, s1N 2435207426068, s1N 4980576479078,
   s1N 2200281126284, s1N 4429299811848, s1P 5716507387754, s1P 1856543096110,
   s1P 2521977594918, s1P 3556919581548, s1P 3978249469470, s1P 26623509594726,
   s1P 66638656473191, s1P 118611598839283, s1P 173600052825382, s1P 224851914303339,
   s1P 269464235040274, s1P 305193341480215, s1P 328749907991158, s1P 337071497903258,
   s1P 329964654920542, s1P 310949194614095, s1P 285116024038650, s1P 256545628568539,
   s1P 227100999037642, s1P 196992836352658, s1P 165976784464502, s1P 134877587270923,
   s1P 104886176109757, s1P 77976439747795, s1P 55234553879367, s1P 37305474978964,
   s1P 24174286318542, s1P 15013189130675, s1P 8904557156637, s1N 5098314833792,
   s1P 2872138213335, s1P 1594662796501, s1P 853149136744, s1P 429575348950, s1P 203757484271,
   s1P 94851826021, s1P 47074868072, s1P 27008953866, s1P 17959738805, s1P 12915374167]
private def s1V9S6 : List ℤ :=
  [s1P 9382370863, s1P 6627619022, s1P 4479394560, s1P 2882065827, s1P 1765514054,
   s1P 1032395106, s1P 578465743, s1P 311960817, s1N 162718126, s1P 82520549, s1P 40913132,
   s1P 19939032, s1P 9598487, s1P 4580751, s1P 2171214, s1P 1021904, s1P 476573, s1P 219406,
   s1P 99252, s1N 43896, s1P 18901, s1P 7898, s1N 3194, s1P 1248, s1P 466, s1P 164, s1P 50,
   s1P 14, s1P 2, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V9 : List ℤ :=
  s1V9S0 ++
    (s1V9S1 ++
    (s1V9S2 ++
    (s1V9S3 ++
    (s1V9S4 ++
    (s1V9S5 ++
    (s1V9S6 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V10S0 : List ℤ :=
  [s1N 13503171, s1N 247488295, s1N 316574382, s1N 255262072, s1P 52979226, s1P 1742113,
   s1P 120574671, s1N 450418623, s1N 624218888, s1P 533243667, s1P 568539662, s1N 318645299,
   s1N 389251642, s1N 742841332, s1N 166198345, s1N 734073802, s1N 60940285, s1N 164484020,
   s1N 732123022, s1N 873916015, s1N 935516880, s1P 721808017, s1N 142662712, s1P 381415780,
   s1P 318978215, s1N 1988772153, s1N 1232277595, s1N 533598484, s1N 59946396, s1N 339342813,
   s1P 2008154010, s1P 1513636625, s1N 1531516942, s1P 1278271953, s1P 3207026550,
   s1P 1661007035, s1N 1901358873, s1N 1871040870, s1P 87937346, s1N 3264672775,
   s1N 2512002305, s1N 5662944224, s1N 3037576338, s1P 1833235561, s1P 1521203142,
   s1P 59240233, s1P 225855588, s1P 1746123205, s1P 4295692798, s1N 1071793636, s1P 1573660931,
   s1N 161400989, s1P 3441131837, s1P 2811275516, s1P 4024297626, s1P 2270548662,
   s1P 3178089975, s1N 4423736426, s1P 1917758807, s1P 692778825, s1P 1338110161,
   s1P 352224050, s1N 679487149, s1P 8508738876]
private def s1V10S1 : List ℤ :=
  [s1P 4629316449, s1N 11227141056, s1N 7566482148, s1N 10157493762, s1N 197115730,
   s1P 8405028299, s1P 1095127923, s1P 466168311, s1P 864734117, s1N 570166546, s1N 3001536291,
   s1N 7049077370, s1N 10935933238, s1N 10621008727, s1N 4882433285, s1N 2167987293,
   s1N 27496882607, s1N 20490580071, s1N 19184136114, s1N 1696165234, s1P 479475501,
   s1P 17762453598, s1P 16173333306, s1P 4614525483, s1P 11055518846, s1P 21007556684,
   s1P 33048513919, s1P 8566384021, s1N 9906972717, s1N 31618550929, s1N 21374155537,
   s1N 15223964242, s1N 6717047244, s1N 1342567895, s1P 19996410270, s1N 10163743266,
   s1N 37000080554, s1N 42401696994, s1N 50625370925, s1N 47356877151, s1N 21108574865,
   s1P 4137426565, s1P 56411862059, s1P 44505051806, s1P 14035577415, s1N 8547321571,
   s1N 12676482819, s1N 11748709111, s1N 18496773601, s1N 60635491059, s1N 13391586446,
   s1P 34776271737, s1N 5289386767, s1N 15339722375, s1N 85677661961, s1N 91617757135,
   s1N 83746340584, s1P 31049152099, s1N 26906153026, s1P 84633416010, s1P 97194738650,
   s1P 44524589468, s1N 95045688695, s1N 38430782658]
private def s1V10S2 : List ℤ :=
  [s1N 71229648100, s1N 14666495218, s1N 82012503461, s1P 1964943856, s1N 3491598653,
   s1N 67725351251, s1P 58548761246, s1N 2237006305, s1N 50959056879, s1P 31339536478,
   s1N 35464484358, s1N 13846954074, s1P 6277299946, s1P 36214228586, s1P 42127723931,
   s1P 72657879911, s1P 12458195408, s1N 51091740583, s1P 21340775254, s1P 94621816065,
   s1N 62972201857, s1N 57404012211, s1N 98861742819, s1P 42221821620, s1P 239226398816,
   s1P 238970995275, s1P 120906772678, s1P 275375769957, s1P 256589140705, s1P 133743618660,
   s1P 39902534218, s1N 242454951450, s1N 284384406855, s1N 686977320, s1P 244541868104,
   s1P 355010804421, s1P 55345798122, s1N 186479551749, s1N 198614138434, s1P 140244578885,
   s1P 138581619099, s1N 225984916904, s1N 150375854634, s1P 180868919135, s1N 178987471707,
   s1N 53670703468, s1N 115995956845, s1N 267994815504, s1N 50882937467, s1N 199092823945,
   s1N 133492020475, s1N 223450407580, s1P 40291226788, s1N 142799879874, s1N 15627116275,
   s1N 206447563319, s1N 302639995538, s1P 14915262092, s1N 352887076069, s1N 427486913123,
   s1N 14690950228, s1P 361637630179, s1P 834475803901, s1P 793107389576]
private def s1V10S3 : List ℤ :=
  [s1P 456386223857, s1P 449450633874, s1P 97039342345, s1P 490692269322, s1P 592673715891,
   s1N 135425687634, s1N 202021926981, s1P 77851945536, s1P 574687415662, s1P 202861787550,
   s1P 235713231866, s1P 331287154561, s1N 295735100213, s1N 651868074486, s1N 652736982315,
   s1P 403976522923, s1N 23797962752, s1N 322779078984, s1N 381612741404, s1N 765493510865,
   s1N 936004917166, s1N 212842229156, s1N 148183812677, s1N 646169452964, s1N 1067986939474,
   s1N 407738135194, s1N 1320693822830, s1N 1854061774081, s1N 394302132844, s1N 141590448505,
   s1N 397207497295, s1N 1350354059565, s1N 1185195844745, s1N 40735264294, s1N 283128644272,
   s1N 625642414127, s1N 1359909776046, s1N 2635515395541, s1N 3883106863316,
   s1N 3682353716912, s1N 2139777627912, s1P 1138962669739, s1P 1021710372092,
   s1N 501817950987, s1N 3076148198500, s1N 3531888625352, s1N 107846940413, s1N 91682164772,
   s1N 1146797859337, s1N 1977713486782, s1P 2713182617034, s1P 1661537712929,
   s1N 3170372084298, s1N 3946818031858, s1N 2079690354041, s1N 4902691039413,
   s1N 1563675783013, s1P 5729712617950, s1P 917793406674, s1P 4106854277981,
   s1P 1511103824827, s1P 2242406432297, s1N 1209789112207, s1N 4491102753216]
private def s1V10S4 : List ℤ :=
  [s1N 3193159902467, s1N 4625841539371, s1N 5866688759157, s1N 4689120070161,
   s1N 4262029937401, s1N 4708428101295, s1P 609898663004, s1P 3171337556659,
   s1P 2335879014572, s1P 967889075640, s1P 423453772811, s1P 170696509268, s1N 1331801159440,
   s1N 893365421663, s1N 3817818511879, s1N 271670162177, s1N 775627997800, s1P 630772911682,
   s1N 3680712695337, s1N 3564255031564, s1N 1858761346240, s1N 1631615572712,
   s1P 444901153011, s1P 457846649876, s1N 2412316265268, s1P 2345418729299, s1N 1311815868544,
   s1N 1761845406975, s1N 2882811703680, s1N 542609808280, s1P 1701012042219, s1N 691233798601,
   s1P 3560518226567, s1P 2018109989614, s1P 3447428936010, s1P 719506136461,
   s1P 5340379211757, s1P 1413401218874, s1P 278095415062, s1N 248967534770, s1P 1798706298905,
   s1N 417086780013, s1N 923925882469, s1N 3384011486778, s1N 1596047716539, s1N 5549495574898,
   s1P 1808739565968, s1P 913142174624, s1P 195507975193, s1P 1281604213937, s1P 4491204573330,
   s1N 1196759029478, s1P 3527094952379, s1P 4913744181422, s1P 5772152497732,
   s1P 1171462766474, s1N 6011838526867, s1N 3841675999975, s1P 209399736111,
   s1N 2564643299456, s1N 7797380292614, s1N 3147674510751, s1N 2690167859441,
   s1P 1752656520399]
private def s1V10S5 : List ℤ :=
  [s1P 804105465131, s1P 2154430273183, s1N 3556614998419, s1N 3449620434669, s1P 363611622320,
   s1P 5693005246749, s1P 6530663217396, s1N 693756224736, s1P 1999251843748,
   s1P 2191857678661, s1N 2094745318513, s1N 1316389247804, s1P 1498498860873,
   s1N 12355939311242, s1N 9556679530819, s1P 3837718602038, s1P 4157697488717,
   s1N 150444408714, s1N 16278812434, s1P 2476754792217, s1P 1424575289383, s1N 53693954681,
   s1N 4464518741521, s1N 3900618003964, s1P 3513449386438, s1N 6344882834959,
   s1N 5239513915384, s1P 3284112124771, s1N 853826613875, s1N 5035210522946,
   s1P 4093519782453, s1P 2057250850297, s1P 6592482278377, s1P 3232945181876,
   s1P 6395851634959, s1P 12855330848488, s1P 6124918911273, s1P 18114681696322,
   s1P 57095178387895, s1P 105817798784792, s1P 159518257989250, s1P 213911950129982,
   s1P 264649646063931, s1P 303696694765465, s1P 330580355799352, s1P 335061853664809,
   s1P 334191204971617, s1P 310685082764863, s1P 292838455450512, s1P 264905986457994,
   s1P 231034974297760, s1P 203315576724294, s1P 171188837059153, s1P 133992416516423,
   s1P 102734540464462, s1P 79214992683844, s1P 58220236791879, s1P 38389459870352,
   s1P 22375377723875, s1P 11915683750347, s1N 6223164231009, s1N 3430175152733,
   s1P 2028722082042, s1P 1230957325480]
private def s1V10S6 : List ℤ :=
  [s1P 728258388803, s1P 410338532403, s1P 220279803996, s1P 115444577947, s1P 60963273325,
   s1P 33829054334, s1P 20393808022, s1P 13025229423, s1P 8503956436, s1P 5664610154,
   s1P 3781296086, s1P 2397459071, s1P 1380524593, s1P 716803077, s1P 346639268, s1P 165864627,
   s1P 83230474, s1P 44363148, s1P 24227959, s1P 13047118, s1P 6828390, s1P 3459382,
   s1N 1681544, s1P 775069, s1N 336423, s1P 137477, s1P 53159, s1P 19699, s1P 7183, s1P 2683,
   s1N 1059, s1P 440, s1P 182, s1P 70, s1P 24, s1P 6, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V10 : List ℤ :=
  s1V10S0 ++
    (s1V10S1 ++
    (s1V10S2 ++
    (s1V10S3 ++
    (s1V10S4 ++
    (s1V10S5 ++
    (s1V10S6 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V11S0 : List ℤ :=
  [s1P 63663836, s1N 53787259, s1P 79458503, s1P 374701695, s1P 195299284, s1N 187715933,
   s1P 279968301, s1N 338954307, s1N 391388282, s1N 765113399, s1N 365424855, s1P 320403435,
   s1P 637668721, s1P 299559057, s1N 199936490, s1P 102991471, s1P 684045216, s1N 139891848,
   s1N 958926840, s1N 323584710, s1P 727431220, s1N 1030746686, s1N 476871254, s1N 651022145,
   s1N 787587810, s1N 915072582, s1P 494521534, s1P 1656914694, s1P 1154407186, s1N 460410689,
   s1N 242465160, s1N 1794638936, s1N 1922523512, s1N 1114950402, s1N 3442703785,
   s1N 550896781, s1N 1322200403, s1P 769384543, s1P 1296359860, s1P 2653618130,
   s1P 2171451516, s1P 1753001085, s1P 1061064624, s1P 707428482, s1P 2126607473,
   s1P 4575647210, s1P 5047326750, s1P 4219930455, s1P 59714734, s1N 2415130612,
   s1P 1039601749, s1P 2988955476, s1P 3063572096, s1P 2408277057, s1P 179532847,
   s1N 2817113285, s1N 350590547, s1N 923395935, s1P 3122547821, s1N 1795211442,
   s1N 8560985456, s1N 5086949608, s1N 4194086777, s1N 3295610399]
private def s1V11S1 : List ℤ :=
  [s1P 2883305018, s1P 627200372, s1P 767881014, s1N 4194564524, s1P 496623854, s1N 9321908574,
   s1N 7511832735, s1N 3793508925, s1N 12313347267, s1P 1977027214, s1N 12361652256,
   s1N 1049103350, s1P 1274626665, s1N 255328143, s1P 2339190406, s1P 3657261258,
   s1P 12208339850, s1P 7587976592, s1N 7486872527, s1N 9524810817, s1P 1687874645,
   s1P 7039125474, s1P 2384967381, s1P 11141276596, s1P 18593579969, s1P 32365404622,
   s1P 16545481418, s1N 6592209814, s1N 9579058678, s1N 7507272604, s1P 10100856765,
   s1P 731398157, s1P 33116515201, s1P 19433655299, s1P 28387359842, s1P 16629101228,
   s1N 3590076877, s1N 15260063160, s1N 30226100654, s1N 28023752678, s1N 5741716652,
   s1P 825181858, s1N 349085587, s1P 18315597574, s1N 27147768024, s1P 235956255,
   s1P 75741586847, s1P 64340893547, s1P 65430188042, s1N 48504088304, s1N 19696872249,
   s1P 37636351744, s1N 17093985337, s1N 35383674708, s1N 2356869279, s1P 47432249434,
   s1P 90413592220, s1N 46299760946, s1N 7905220337, s1P 16954835430, s1N 23601326834,
   s1P 45256263322, s1P 19754687380, s1P 48914947261]
private def s1V11S2 : List ℤ :=
  [s1P 180724284830, s1P 37342543442, s1P 28863753784, s1N 18475541411, s1N 91074738825,
   s1N 65319616826, s1N 10598059302, s1N 5257033746, s1N 26517072185, s1N 44319795104,
   s1N 70917387755, s1N 4903933516, s1P 90253597915, s1P 5110679839, s1P 5607286898,
   s1N 46023196659, s1N 1270707168, s1N 60245821432, s1N 58061048214, s1N 42853906979,
   s1N 17397502624, s1N 34656305199, s1N 125383022668, s1P 59715938625, s1P 118686062665,
   s1N 44966928436, s1N 80401834984, s1N 106790759013, s1N 9353264796, s1N 76859176608,
   s1P 121256803933, s1P 25174166845, s1N 54388895070, s1N 83432150786, s1N 18992079840,
   s1N 251686099496, s1N 199622628893, s1N 427704853208, s1N 527135239899, s1N 321957829167,
   s1N 300012635325, s1N 91951297579, s1P 222333519566, s1P 65395421744, s1P 122833804156,
   s1P 5278852465, s1P 5357626567, s1N 169038245325, s1P 142130399686, s1P 15298232898,
   s1N 4939423797, s1N 110269760585, s1P 113287213344, s1N 64226316155, s1N 227791792017,
   s1N 92859019309, s1N 148297281244, s1N 156656685215, s1N 252251735642, s1N 245478383084,
   s1P 162391440010, s1P 281856475413, s1P 175712422486, s1P 56003313633]
private def s1V11S3 : List ℤ :=
  [s1N 13991713023, s1P 17572194664, s1P 214640779843, s1P 274873919661, s1P 931884339810,
   s1P 173734516084, s1N 367636164912, s1N 669195842202, s1N 223098988777, s1P 270749233891,
   s1P 818276932597, s1P 678456492688, s1P 131638385683, s1P 617582454491, s1P 253566868139,
   s1P 190314481249, s1N 226712855930, s1N 449916915947, s1N 723805779964, s1N 89572837433,
   s1N 645329632790, s1N 288021470587, s1N 946435125445, s1N 129688406360, s1N 268721460906,
   s1N 6232242092, s1N 531630674459, s1N 223641226466, s1N 239955765454, s1N 792908848887,
   s1N 1108414359153, s1N 418362457530, s1P 61871609566, s1N 587440089455, s1N 1428667563726,
   s1N 1562929261045, s1N 124074298423, s1N 1234711614227, s1N 206948636836, s1P 1223977499626,
   s1P 691109583220, s1P 1452191346010, s1P 531774633560, s1P 113697361695, s1P 749214324462,
   s1N 474976512465, s1N 3004619433579, s1N 5739560362801, s1N 5078437399676,
   s1N 3928175264483, s1N 3124826985506, s1N 1653757562188, s1P 677342550285,
   s1P 1561958714194, s1N 1807780439155, s1N 2385447757951, s1N 1450476202737,
   s1P 1917805326574, s1N 378188431387, s1N 2748403301029, s1N 2341887701101,
   s1N 2928046438239, s1N 3145403478861, s1P 3112715742554]
private def s1V11S4 : List ℤ :=
  [s1N 4456713557796, s1N 1594914754684, s1P 344129686939, s1P 2380576504256,
   s1N 2103900245246, s1P 5442399080582, s1N 752988496758, s1N 295531557344, s1N 1860251134631,
   s1P 1230922900162, s1N 3131070622477, s1N 5948048139957, s1N 6758504293626,
   s1N 6222605953216, s1N 3626070315903, s1P 1003149724570, s1P 2319591019488,
   s1N 2437379260707, s1N 1989225463018, s1N 1492487794842, s1P 1282266281712,
   s1N 3054205001296, s1N 1200259602406, s1N 1941140478141, s1P 2544179055843,
   s1N 2377757887646, s1P 1838925479728, s1N 3075867188201, s1P 476398025914,
   s1N 3963166001858, s1N 2219252877836, s1N 102949136706, s1P 860829347196, s1N 1491254673803,
   s1P 1591851623616, s1N 2205375147212, s1N 1105014338465, s1N 4019182285462,
   s1P 1522537825832, s1N 367943375034, s1N 524595138774, s1P 995863184116, s1P 4374206449645,
   s1P 545038184548, s1P 5158282465531, s1P 2759094821471, s1P 857313102700, s1P 2664023369238,
   s1N 2565018484741, s1P 1397844535693, s1P 1184987080667, s1N 1246982259927,
   s1N 2930009935237, s1P 1588522379481, s1N 5815437488323, s1N 1790258499721,
   s1P 3028781144683, s1P 365002406483, s1N 4127574127001, s1N 2035391455980,
   s1P 7102967541595, s1P 4450027276910, s1P 3612940439769, s1P 40660443898]
private def s1V11S5 : List ℤ :=
  [s1N 1491379684680, s1N 575559513533, s1P 1461627244454, s1N 2946038920173,
   s1N 5567968264244, s1N 9870240614305, s1N 1446569353145, s1P 4381782958645,
   s1N 4243100398160, s1N 745723522301, s1P 912313730910, s1P 5281057502489, s1N 841095009195,
   s1P 8040500148879, s1P 2130673572126, s1P 3768851964704, s1P 5120903471356,
   s1P 5065386749699, s1P 4707187888084, s1P 3637113778426, s1N 10084040234631,
   s1N 3545556268086, s1N 794307609251, s1N 9402446668348, s1N 2119980578295,
   s1P 4447235933424, s1P 481453236764, s1P 1291533917147, s1P 33334201777, s1P 2504745741470,
   s1P 2297793005774, s1N 6104836170758, s1N 1494256061748, s1N 973323409724,
   s1N 6288354092061, s1P 2868904641411, s1P 3772713077905, s1P 4239360869255,
   s1N 1629067385428, s1P 411253509105, s1P 12993370157378, s1P 8479770084280,
   s1P 1306226322069, s1P 5155066785103, s1P 4962781864559, s1P 15822233582940,
   s1P 52589008942243, s1P 96709311334190, s1P 153812337668550, s1P 215540781793441,
   s1P 264877056270548, s1P 304853974637066, s1P 328343016537833, s1P 341176151657528,
   s1P 328361079436611, s1P 314851469619565, s1P 297514948318860, s1P 266025219416910,
   s1P 235846518920676, s1P 203329879828479, s1P 163682001173707, s1P 129112500942618,
   s1P 104333232660541, s1P 81131069300535]
private def s1V11S6 : List ℤ :=
  [s1P 55276982746467, s1P 31383217093398, s1P 14739096365602, s1P 5976993255892,
   s1N 2456790380401, s1N 1337946269461, s1P 965644583827, s1P 727101150009, s1P 506673691612,
   s1P 322418294268, s1P 191058949920, s1P 108340530705, s1P 60478072658, s1P 34145113748,
   s1P 19923200492, s1P 12112383845, s1N 7577710082, s1P 4756167778, s1P 2910298954,
   s1P 1708320224, s1P 956968606, s1P 512118765, s1P 265044235, s1P 135657592, s1P 69730281,
   s1P 35647195, s1N 17538483, s1P 8011008, s1P 3324463, s1P 1258530, s1P 455470, s1P 174205,
   s1P 76610, s1P 37188, s1P 17908, s1P 8032, s1P 3325, s1P 1303, s1P 499, s1P 190, s1P 68,
   s1P 21, s1P 5, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V11 : List ℤ :=
  s1V11S0 ++
    (s1V11S1 ++
    (s1V11S2 ++
    (s1V11S3 ++
    (s1V11S4 ++
    (s1V11S5 ++
    (s1V11S6 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V12S0 : List ℤ :=
  [s1P 77552419, s1P 26069119, s1N 92752950, s1P 136439361, s1P 537899977, s1P 14099021,
   s1N 157790746, s1N 79210679, s1N 117706246, s1P 112427355, s1P 207467959, s1N 613447517,
   s1N 742552474, s1N 516940494, s1P 421414697, s1P 522023485, s1N 271483084, s1N 830515401,
   s1N 1012255627, s1N 673210150, s1N 280228161, s1N 559546498, s1N 78232724, s1N 69153656,
   s1N 187651637, s1N 624170353, s1N 364645464, s1P 431684146, s1N 2353235308, s1P 223197531,
   s1N 1388759339, s1N 1455491818, s1N 1103765714, s1N 851768597, s1N 81831603, s1P 31387362,
   s1P 756625714, s1P 1532968703, s1N 1819216479, s1N 1957552104, s1N 2473965065,
   s1N 1352938224, s1P 808206429, s1N 27556695, s1N 2191681426, s1P 1864649352, s1N 2289322782,
   s1P 1780309759, s1P 12422817, s1P 1487983743, s1P 4398466613, s1P 4488325959,
   s1P 5686751579, s1P 3374077955, s1P 1090606767, s1P 749970792, s1P 571451705, s1P 462705156,
   s1P 7479594578, s1P 1492401876, s1P 346927476, s1N 3927698801, s1N 2013939794,
   s1N 1698743795]
private def s1V12S1 : List ℤ :=
  [s1P 1859995296, s1P 7655746909, s1P 11399146837, s1P 996941200, s1N 7315696493,
   s1N 5637769956, s1N 1469845262, s1P 3320179962, s1P 1410110976, s1P 2578824824,
   s1P 647077216, s1N 3321286806, s1N 6484912718, s1P 3516824448, s1N 5077697820,
   s1P 7411629002, s1N 13389941060, s1N 157002735, s1N 797242509, s1N 9610445224,
   s1N 4634965617, s1N 4057064642, s1P 19849376206, s1P 1977262223, s1P 8647584632,
   s1N 11550265619, s1N 7770846799, s1N 4353701595, s1N 14003063301, s1N 5428368163,
   s1N 4932863170, s1N 19100271802, s1N 27564222894, s1N 22535783732, s1N 5661388991,
   s1P 11082356394, s1P 14380592476, s1P 8983729803, s1P 18319015093, s1P 25208664624,
   s1P 42808917872, s1P 21058075373, s1P 22250598451, s1P 36345928552, s1P 2359638303,
   s1P 3210010073, s1P 22168849452, s1P 69158186789, s1P 40551714163, s1P 15133692440,
   s1P 18213582559, s1P 49433130489, s1P 51750135478, s1P 84364817667, s1P 69356235250,
   s1P 34969153812, s1P 84100964355, s1P 18461960966, s1P 33127918498, s1P 4694980199,
   s1P 81064669329, s1P 2926622882, s1P 50504199055, s1P 5766104197]
private def s1V12S2 : List ℤ :=
  [s1P 7379278567, s1N 38521309006, s1N 21895419881, s1N 24069625396, s1N 13889680485,
   s1P 63606530912, s1N 27501187762, s1N 49309375322, s1N 105224665832, s1N 117723077047,
   s1N 86449985691, s1P 9251626752, s1P 84917280436, s1P 9279786238, s1N 2977275653,
   s1P 3181103436, s1P 33501932624, s1P 138750974853, s1N 31977217645, s1N 42862330676,
   s1N 1823351072, s1N 21615733973, s1N 128357303925, s1N 31611949349, s1N 73712594319,
   s1P 34190664284, s1P 95902657241, s1N 110568005928, s1N 56154866930, s1P 49274958917,
   s1P 148757510034, s1P 56306053355, s1P 101738374728, s1P 63269836800, s1P 79818198200,
   s1P 189018422528, s1P 44210428780, s1P 26316035247, s1P 69044469715, s1N 113640633748,
   s1P 108479320322, s1P 39302476046, s1P 863415405, s1N 16886771105, s1P 30883328684,
   s1P 242712630633, s1P 453989957096, s1P 367742627248, s1P 500632668626, s1P 433627647548,
   s1N 12711964412, s1N 38202353740, s1N 40171096755, s1N 1410764111, s1N 29889198007,
   s1N 53804082959, s1N 41893440676, s1P 204560758036, s1N 209588652493, s1N 63202198329,
   s1N 157501871839, s1N 198210237308, s1N 70307575853, s1N 142049242465]
private def s1V12S3 : List ℤ :=
  [s1N 50827347548, s1N 295653142135, s1N 328185994434, s1N 37630644812, s1N 489113783067,
   s1N 193239465518, s1N 210428372191, s1P 286835483731, s1N 76941987201, s1P 134591790389,
   s1P 559832178824, s1P 786034644919, s1P 584447551202, s1P 861578892673, s1N 184983917340,
   s1N 274690816002, s1N 493241947915, s1P 8963174891, s1P 161844083960, s1N 223514370052,
   s1N 321523319318, s1P 513107362156, s1P 780948967223, s1P 561970740523, s1P 118397776323,
   s1N 410861358018, s1P 335691379155, s1P 428263232134, s1P 322442739024, s1P 744833932018,
   s1P 598527954115, s1P 305804986900, s1P 1420258947452, s1P 493959756541, s1N 781339826914,
   s1N 357118987066, s1N 429919855867, s1P 849272264879, s1P 486661182486, s1N 396593692972,
   s1P 247650793464, s1P 495929770751, s1P 779975786771, s1P 247117052466, s1N 1689827070298,
   s1N 1569135298207, s1P 1587966716437, s1P 1218391169814, s1P 135035983131, s1N 435104618063,
   s1N 146600696431, s1N 2220145729043, s1N 1654516479657, s1N 1861526520179,
   s1N 2765744674728, s1N 2209372324582, s1N 6322824814993, s1N 5982474443241,
   s1N 5347056907241, s1P 978544532708, s1P 3751582378514, s1P 3254126423125,
   s1P 3945708528271, s1P 3097293091868]
private def s1V12S4 : List ℤ :=
  [s1N 891393187437, s1N 1931559495212, s1N 1629361843086, s1P 1554273633580, s1N 655263783916,
   s1N 2826539654842, s1N 2148028545768, s1P 835545673847, s1N 914147939293, s1N 4847040747781,
   s1N 556643080535, s1P 597794283983, s1N 2074706938485, s1N 458963733232, s1N 2633856900241,
   s1P 2080769961441, s1P 2739151169318, s1P 543774954738, s1N 3715031276721,
   s1N 6120003982696, s1N 7094091383946, s1N 6435482037815, s1P 3039938527232,
   s1P 2659487405392, s1N 1729075719324, s1N 2830231880488, s1P 2142623365146,
   s1P 2749960502745, s1P 522537363868, s1N 2040474086130, s1N 467070384330, s1P 2829522462192,
   s1P 318139537708, s1P 528496482274, s1P 1347699306414, s1P 2679178045167, s1P 562715312731,
   s1N 1601437886610, s1N 5519089964127, s1N 1258924905555, s1N 1334975696982,
   s1P 893163964132, s1P 420486987329, s1N 974624630280, s1N 2269419117196, s1P 808018346806,
   s1P 4257017803335, s1P 84713096108, s1P 1138327285152, s1N 3126865562353, s1N 2140806139204,
   s1P 3815617052893, s1P 3499383092611, s1P 610819590628, s1N 5338595242683,
   s1N 1596684160215, s1P 2225876348560, s1P 1502232986241, s1P 5103330989251,
   s1P 1738220376235, s1N 3089622416522, s1N 3103620625371, s1N 179156798792, s1P 2563534593651]
private def s1V12S5 : List ℤ :=
  [s1N 4818344297221, s1P 600467461853, s1P 5725766176400, s1N 2133364294375,
   s1N 4417985739167, s1N 7242457330827, s1N 4650780219156, s1N 1541014550048,
   s1P 6954630807959, s1P 1827800984051, s1P 3458893340166, s1P 2013221722472,
   s1N 7476292974963, s1P 1734864764864, s1P 2715636159399, s1N 5392089207950,
   s1N 1899334301199, s1N 2847852312012, s1N 3380267964998, s1P 8357867494856,
   s1P 2308385155727, s1P 2227150698905, s1P 4980625713377, s1P 5875401551433,
   s1P 7308871462101, s1P 4505904780826, s1P 3147476141853, s1P 6217151227480,
   s1N 7280651946005, s1N 6027837276149, s1N 2402720701815, s1P 4362868763878,
   s1P 2100992768454, s1N 1349345710350, s1P 2826822498703, s1P 1699457528707,
   s1N 1734231988118, s1N 5418026528545, s1P 3081988724755, s1P 10237413479993,
   s1P 3801040597483, s1P 2665243447147, s1N 1278891024031, s1N 1246491589485,
   s1N 2003138694060, s1P 226839945725, s1P 2144087133774, s1N 10059812412636,
   s1P 9118526783813, s1P 4586430309077, s1P 1517221692058, s1N 9917430133867,
   s1P 6660350367783, s1P 19056599300396, s1P 54084288853414, s1P 104252484767187,
   s1P 167657827913359, s1P 226736843784386, s1P 275012599307961, s1P 313240411010115,
   s1P 332193686470261, s1P 336262754776081, s1P 328335371723812, s1P 317985850214536]
private def s1V12S6 : List ℤ :=
  [s1P 296036302054012, s1P 259991385736660, s1P 223665680801152, s1P 189995839077837,
   s1P 156840412113355, s1P 125836126259050, s1P 96827548816278, s1P 68415179020737,
   s1P 42437963060814, s1P 22563418952662, s1N 10281855395444, s1P 4212292733084,
   s1P 1774240696686, s1N 951495024119, s1P 665365671748, s1P 490375775321, s1N 341034620263,
   s1P 226332800831, s1P 144760962217, s1P 86409663513, s1P 46576582855, s1P 22975713898,
   s1P 11169804091, s1P 6023322998, s1P 3760072227, s1P 2487128292, s1N 1609055383,
   s1P 998875209, s1P 590442437, s1P 325381986, s1P 164064557, s1N 75875245, s1P 33138077,
   s1P 14325237, s1P 6367465, s1P 2919385, s1P 1347455, s1P 611673, s1P 271089, s1P 117958,
   s1P 50842, s1P 21799, s1P 9275, s1P 3889, s1P 1592, s1P 630, s1P 238, s1P 82, s1P 23, s1P 5,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0,
   s1P 0]
private def s1V12 : List ℤ :=
  s1V12S0 ++
    (s1V12S1 ++
    (s1V12S2 ++
    (s1V12S3 ++
    (s1V12S4 ++
    (s1V12S5 ++
    (s1V12S6 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private def s1V13S0 : List ℤ :=
  [s1N 37979693, s1N 88313539, s1N 96790379, s1P 282087613, s1P 3960629, s1P 385889413,
   s1P 293055831, s1P 54876525, s1N 197972884, s1N 300477566, s1P 165685100, s1P 42603192,
   s1N 298007223, s1P 255482697, s1P 489134636, s1P 941553665, s1P 475400017, s1N 93145037,
   s1N 647412596, s1P 246134345, s1N 416411016, s1N 454686098, s1N 1188515821, s1N 381680203,
   s1N 2086753338, s1N 427254947, s1P 95566475, s1N 939038642, s1N 42385700, s1P 55114560,
   s1P 323332750, s1P 144075289, s1P 1123281197, s1N 436459139, s1N 1222792112, s1N 1396869940,
   s1P 659414011, s1N 890044584, s1P 2651723318, s1P 943705400, s1P 2627053070, s1P 2952720465,
   s1P 1358748702, s1N 971165041, s1N 754445601, s1N 2765537626, s1N 1031986566, s1N 666440121,
   s1N 807974184, s1N 966404844, s1N 583225754, s1P 2300000958, s1P 2496389977, s1N 2849739040,
   s1P 115806835, s1N 1009952955, s1N 2400614641, s1N 3096320401, s1N 6021017248,
   s1N 5344274849, s1N 3274194501, s1N 1006859030, s1N 838246495, s1N 4797292955]
private def s1V13S1 : List ℤ :=
  [s1N 2234327202, s1N 3268031549, s1N 3602698805, s1P 3770242526, s1P 5742794963,
   s1P 4400118633, s1P 8912206049, s1P 14160702360, s1P 2153349306, s1N 10499651919,
   s1N 1198906576, s1N 6100994519, s1P 3467156220, s1N 11632646263, s1N 6257745056,
   s1N 1291236923, s1N 10495153654, s1N 7742060606, s1N 3683762233, s1N 5282317207,
   s1P 3836986210, s1P 695432247, s1P 3533849733, s1N 1625269986, s1N 6233457346,
   s1P 4488205485, s1P 14681391243, s1P 8957392513, s1P 1122880603, s1N 393537645,
   s1N 10180493266, s1N 4624713986, s1N 9596673123, s1N 4972451560, s1P 14205416251,
   s1N 610913862, s1N 11192617026, s1N 13249935364, s1N 12104092407, s1N 27005743561,
   s1N 32537309153, s1N 5655212838, s1N 11313121592, s1P 13712797745, s1P 2679513016,
   s1P 19256750729, s1P 20379902043, s1P 24064411806, s1P 66932059162, s1P 20836943266,
   s1P 55536008313, s1N 11553379550, s1N 22270861554, s1N 20550466520, s1N 65065042707,
   s1N 40466024141, s1P 16405864162, s1P 19911956571, s1N 28578435147, s1P 41535763934,
   s1N 6057382732, s1N 89495764666, s1N 52240367766, s1N 71835760061]
private def s1V13S2 : List ℤ :=
  [s1N 73705680118, s1N 31674892701, s1P 39492924288, s1P 36754084091, s1P 44209580956,
   s1P 20184860414, s1P 42453292813, s1P 88943027301, s1P 25874048405, s1N 31909071451,
   s1N 47541231124, s1P 40128721577, s1P 10944246243, s1N 44008539259, s1P 18144413921,
   s1P 68313013329, s1P 87941014507, s1P 214458529228, s1P 10671869557, s1P 49927348340,
   s1N 7228178947, s1P 30075377315, s1P 22636435109, s1P 239298515, s1N 84384638760,
   s1N 50028769535, s1N 52562896169, s1P 91835886598, s1P 114334833368, s1P 100916081550,
   s1P 16557888292, s1P 174031207578, s1P 8711926244, s1N 64514392449, s1N 67854022135,
   s1P 64455673664, s1P 20031605799, s1N 56498884980, s1N 68337433446, s1P 52987428956,
   s1P 2593967765, s1P 127732933798, s1P 17360848762, s1P 178328733943, s1P 212983907526,
   s1P 31018925098, s1N 66357955012, s1N 188702802640, s1P 40923181922, s1P 128568599784,
   s1P 44726336309, s1P 10905465992, s1P 33410552305, s1P 230492847116, s1P 100593815029,
   s1P 383018473552, s1P 419964896045, s1P 534461653686, s1P 184915370796, s1P 507804579026,
   s1P 43132194029, s1P 127585117168, s1P 59584787264, s1P 4696127379]
private def s1V13S3 : List ℤ :=
  [s1P 106483320589, s1P 139424020849, s1N 44624608433, s1N 68301719305, s1P 446559386803,
   s1P 260775862909, s1N 195255158654, s1N 256661060978, s1N 39475299555, s1N 21400993669,
   s1N 147305933978, s1N 211069333183, s1N 380622187484, s1N 260332335758, s1N 196956506082,
   s1N 331236379179, s1P 108924092432, s1P 373744890533, s1P 320643402400, s1P 402039969479,
   s1P 898533401293, s1P 924401429519, s1P 622848091848, s1P 304385372745, s1N 262323734620,
   s1N 648813952960, s1N 733747422171, s1P 102409576186, s1P 426508133865, s1N 368963799497,
   s1N 796292603300, s1N 482131733894, s1N 318727957321, s1N 23300662473, s1N 35113481488,
   s1N 542829547917, s1N 580058317847, s1N 809003077629, s1N 579893163174, s1P 674649490276,
   s1P 1355257503716, s1P 1110503087362, s1P 301043205727, s1N 1047938963689, s1P 120938172032,
   s1N 2036732130192, s1N 1768447455794, s1N 128938527135, s1P 333573023170, s1N 1695689490939,
   s1N 989918927401, s1N 150665136242, s1P 502800204735, s1P 960796033327, s1P 405336360593,
   s1P 761608309690, s1N 616941426494, s1N 2072791535429, s1N 884325074076, s1N 1397263205230,
   s1N 2405727766486, s1N 116105048950, s1N 1290187965398, s1N 1599561406744]
private def s1V13S4 : List ℤ :=
  [s1N 3878526696504, s1N 5883035403998, s1N 5912429474740, s1N 5380319823391,
   s1N 5662183873930, s1N 4520749327438, s1N 4287821156729, s1N 1324740499756,
   s1P 1298089370585, s1P 1770440066208, s1P 1611292180347, s1P 1349670224548,
   s1N 662076749544, s1N 1658882565060, s1N 1745931388163, s1N 1410705637754,
   s1N 3648785909990, s1N 1288813481175, s1N 313660513441, s1P 2007587893380,
   s1P 1557355833538, s1N 1038153277897, s1N 4458493771441, s1N 1129720753715,
   s1N 3619011479213, s1N 6288926105608, s1N 558590970764, s1N 6719130651457,
   s1N 7222219017538, s1N 1112342237282, s1N 3402431917197, s1N 2719958258548,
   s1N 2879726445833, s1P 232247142954, s1P 1771694581808, s1N 313068803498, s1N 305493756117,
   s1N 305480518063, s1P 2354146317677, s1N 2161188734687, s1P 253775923578, s1P 740895640979,
   s1N 673232083438, s1N 5410078557517, s1P 1377356274925, s1N 1136314010038,
   s1N 3077677170514, s1P 2589466077607, s1P 46128189338, s1N 837710089593, s1N 628345109435,
   s1P 3401016707240, s1P 4229321736589, s1P 4075976545318, s1P 3422215972048,
   s1P 1034237661627, s1P 3467231124958, s1P 1228967386171, s1P 2096755722950,
   s1P 526392145468, s1P 6264649822417, s1P 394890240798, s1N 5678729763085, s1N 3284103492670]
private def s1V13S5 : List ℤ :=
  [s1P 5487054270370, s1P 921233026749, s1N 247528827200, s1P 3914268325936, s1N 1602578369988,
   s1P 2306718033467, s1N 2172455184545, s1N 6932601320615, s1P 3392010181744,
   s1N 3830942079410, s1N 1362221699772, s1P 5427741108621, s1N 6658376765654,
   s1N 8820316603759, s1N 3435079603554, s1N 1912157695514, s1P 3725660648382,
   s1N 4486646137974, s1N 2380404022058, s1P 1630249521233, s1P 732820859746,
   s1P 5177785219815, s1P 2272823167414, s1N 6205993179079, s1N 1759308295777,
   s1N 1070813079423, s1N 1075948649736, s1N 1211811480694, s1P 5113595699401,
   s1P 3644121298522, s1N 328797563133, s1P 4824205035849, s1P 9540354856921,
   s1P 12132117826342, s1P 102924536341, s1P 2115721348666, s1N 1294150211733,
   s1N 3537076407815, s1N 1991842679751, s1N 4698765760120, s1P 11433899930499,
   s1N 2757670306617, s1N 2380877374491, s1N 4284871365603, s1P 2547926888258,
   s1P 1671103640356, s1P 11228171915468, s1N 4355886171182, s1N 2250591411761,
   s1P 3669782247644, s1P 5573005139904, s1N 962743198019, s1N 7215865179230,
   s1P 1788407104535, s1P 1871065767588, s1P 3905775262322, s1P 4080269796156,
   s1P 1232667516931, s1N 6733340073412, s1N 15207879482325, s1P 7776426498645,
   s1P 17181965797263, s1P 55537349429442, s1P 112962678950282]
private def s1V13S6 : List ℤ :=
  [s1P 178287026366884, s1P 239840436843377, s1P 276853139635891, s1P 319216066389859,
   s1P 327039118033269, s1P 346238332809169, s1P 336385442820254, s1P 309383437482018,
   s1P 290722821988135, s1P 256189809085342, s1P 212319324956071, s1P 181908830595328,
   s1P 155814181547686, s1P 122079271070917, s1P 84114792226130, s1P 50506024773907,
   s1P 26575318316492, s1P 12609422871552, s1P 5664270098041, s1P 2494430412916,
   s1P 1069873632736, s1P 462042043601, s1P 237388216170, s1N 171108776464, s1P 145851464572,
   s1P 115755425260, s1P 81297400197, s1P 52233174641, s1P 31631803594, s1P 17853088894,
   s1P 9102544080, s1P 4269284342, s1P 2076628026, s1P 1181714968, s1P 735573151,
   s1P 436320244, s1P 233819080, s1P 115390168, s1P 55151117, s1P 26730543, s1P 13317585,
   s1P 6703913, s1P 3328948, s1P 1606909, s1P 750899, s1P 340399, s1P 150378, s1P 65034,
   s1P 27630, s1P 11553, s1P 4751, s1P 1914, s1P 747, s1P 278, s1P 94, s1P 28, s1P 6, s1P 0,
   s1P 0, s1P 0, s1P 0, s1P 0, s1P 0, s1P 0]
private def s1V13 : List ℤ :=
  s1V13S0 ++
    (s1V13S1 ++
    (s1V13S2 ++
    (s1V13S3 ++
    (s1V13S4 ++
    (s1V13S5 ++
    (s1V13S6 ++
    (mm16k512krS1VecIn5 ++
    mm16k512krS1VecIn8)))))))
private theorem s1Ok0 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B0 mm16k512krS1LIn 512 mm16k512krS1PadIn mm16k512krS1VecIn)
      35 512 599120491 s1V0 = true := by decide +kernel
private theorem s1Ok1 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B1 35 512 599120491 s1V0)
      35 512 631376954 s1V1 = true := by decide +kernel
private theorem s1Ok2 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B2 35 512 631376954 s1V1)
      38 512 653845203 s1V2 = true := by decide +kernel
private theorem s1Ok3 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B3 38 512 653845203 s1V2)
      40 512 668203646 s1V3 = true := by decide +kernel
private theorem s1Ok4 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B4 40 512 668203646 s1V3)
      40 512 676910268 s1V4 = true := by decide +kernel
private theorem s1Ok5 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B5 40 512 676910268 s1V4)
      42 512 681664430 s1V5 = true := by decide +kernel
private theorem s1Ok6 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B6 42 512 681664430 s1V5)
      43 512 698008438 s1V6 = true := by decide +kernel
private theorem s1Ok7 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B7 43 512 698008438 s1V6)
      44 512 708779525 s1V7 = true := by decide +kernel
private theorem s1Ok8 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B8 44 512 708779525 s1V7)
      45 512 714565652 s1V8 = true := by decide +kernel
private theorem s1Ok9 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B9 45 512 714565652 s1V8)
      45 512 721254568 s1V9 = true := by decide +kernel
private theorem s1Ok10 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B10 45 512 721254568 s1V9)
      46 512 726097027 s1V10 = true := by decide +kernel
private theorem s1Ok11 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B11 46 512 726097027 s1V10)
      47 512 731935477 s1V11 = true := by decide +kernel
private theorem s1Ok12 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B12 47 512 731935477 s1V11)
      52 512 743337030 s1V12 = true := by decide +kernel
private theorem s1Ok13 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B13 52 512 743337030 s1V12)
      53 512 750270750 s1V13 = true := by decide +kernel
private theorem s1Ok14 :
    s1SegStateAt
      (rkm128kRunSegs 16 62 512 s1B14 53 512 750270750 s1V13)
      mm16k512krS1LOut 512 mm16k512krS1PadOut mm16k512krS1Vec = true := by decide +kernel

/-- Segment count of `mm16k512krS1Segs` (`22` segments). -/
theorem mm16k512krS1_len : rkm128kSegListLen mm16k512krS1Segs = 22 := by
  rfl

/-- Exact `rkm128kRunSegs 16 62 512` Markovian step across `mm16k512krS1Segs` (`segs
  60..81`). -/
theorem mm16k512krS1_step :
    rkm128kRunSegs 16 62 512 mm16k512krS1Segs mm16k512krS1LIn mm16k512krS1DCurIn
      mm16k512krS1PadIn mm16k512krS1VecIn =
      (mm16k512krS1LOut, mm16k512krS1DCurOut, mm16k512krS1PadOut,
        mm16k512krS1Vec) := by
  have hSegs : mm16k512krS1Segs =
      s1B0 ++ (s1B1 ++ (s1B2 ++ (s1B3 ++ (s1B4 ++ (s1B5 ++ (s1B6 ++
        (s1B7 ++ (s1B8 ++ (s1B9 ++ (s1B10 ++ (s1B11 ++ (s1B12 ++
          (s1B13 ++ s1B14))))))))))))) := rfl
  rw [hSegs]
  exact s1Step s1Ok0 (s1Step s1Ok1 (s1Step s1Ok2 (s1Step s1Ok3
    (s1Step s1Ok4 (s1Step s1Ok5 (s1Step s1Ok6 (s1Step s1Ok7
      (s1Step s1Ok8 (s1Step s1Ok9 (s1Step s1Ok10 (s1Step s1Ok11
        (s1Step s1Ok12 (s1Step s1Ok13 (s1SegStateAt_eq s1Ok14))))))))))))))

/-- Suffix chaining lemma advancing `rkm128kRunSegs 16 62 512` past `mm16k512krS1Segs`. -/
theorem mm16k512krS1_run_after (rest : List Rkm128kSeg) :
    rkm128kRunSegs 16 62 512 (mm16k512krS1Segs ++ rest) mm16k512krS1LIn
      mm16k512krS1DCurIn mm16k512krS1PadIn mm16k512krS1VecIn =
      rkm128kRunSegs 16 62 512 rest mm16k512krS1LOut mm16k512krS1DCurOut
        mm16k512krS1PadOut mm16k512krS1Vec := by
  rw [rkm128kRunSegs_append]
  dsimp only
  rw [mm16k512krS1_step]

end

end QuantumComputation.Specs.GroverFindAll.Rk128kMidM16K512KrPt1
