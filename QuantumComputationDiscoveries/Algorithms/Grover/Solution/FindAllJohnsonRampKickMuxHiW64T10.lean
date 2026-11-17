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
# Caustic `r = 1024` Halo-16 Walk `w64` Part `10` (`FindAllJohnsonRampKickMuxHiW64T10`)

Certifies part `10` of `w_hi64_m64_r1024` (`m = 64`) halo-16 trajectory.
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section

/-- Generator list for `w64_s0`. -/
def rkmHbWin_w64_s0 : List ℤ := altBuildHbFrom 64 1024 361115083333 0 64
/-- Entry `rkmXsWin_w64_s0_in`. -/
def rkmXsWin_w64_s0_in : List ℤ := [rkmP 1000000000000000]
/-- Exit `rkmXsWin_w64_s0_out`. -/
def rkmXsWin_w64_s0_out : List ℤ := let p := rkmP; [p 82449610864028, p 188084270564178,
  p 300851702160193, p 389585466669760, p 433134580282446, p 426941764802837, p 380753645175864,
  p 311532619178295, p 236243515882359, p 167326846142323, p 111365040644977, p 69987425802437,
  p 41697205122603, p 23628976349164, p 12771477237913, p 6599697732115, p 3267125476459,
  p 1552212768349, p 708770187834, p 311459992188, p 131848462384, p 53841537230, p 21193626539,
  p 8000833495, p 2928574380, p 917191050, p 228720664]
/-- Generator list for `w64_s1`. -/
def rkmHbWin_w64_s1 : List ℤ := altBuildHbFrom 128 1024 186696904761 0 128
/-- Entry `rkmXsWin_w64_s1_in`. -/
def rkmXsWin_w64_s1_in : List ℤ := let p := rkmP; [p 82449610864028, p 188084270564178,
  p 300851702160193, p 389585466669760, p 433134580282446, p 426941764802837, p 380753645175864,
  p 311532619178295, p 236243515882359, p 167326846142323, p 111365040644977, p 69987425802437,
  p 41697205122603, p 23628976349164, p 12771477237913, p 6599697732115, p 3267125476459,
  p 1552212768349, p 708770187834, p 311459992188, p 131848462384, p 53841537230, p 21193626539,
  p 8000833495, p 2928574380, p 917191050, p 228720664]
/-- Exit `rkmXsWin_w64_s1_out`. -/
def rkmXsWin_w64_s1_out : List ℤ := let p := rkmP; [p 1396351305, p 7646591317, p 29906037377,
  p 95521986778, p 262489652791, p 641595839033, p 1423751003804, p 2908391505966, p 5526162130401,
  p 9843312390064, p 16537830127741, p 26339284389309, p 39929778471492, p 57816444132672,
  p 80193341013117, p 106818622466652, p 136938198551725, p 169278196186158, p 202119132834635,
  p 233450132478908, p 261181108315583, p 283381664757775, p 298507333095541, p 305574918154080,
  p 304261992060687, p 294916337790030, p 278480423854463, p 256349604905209, p 230189697134740,
  p 201746681813319, p 172674030686398, p 144398498060820, p 118035702141409, p 94354739984785,
  p 73788006990178, p 56472838142594, p 42312892374571, p 31047420746247, p 22316423474229,
  p 15717824501699, p 10850242973748, p 7342927697831, p 4872800460386, p 3171452944715,
  p 2024853435481, p 1268374115789, p 779741304438, p 470424212711, p 278569721585, p 161967134799,
  p 92422152944, p 51825465559, p 28431710970, p 15279367096, p 7989902343, p 4021359772,
  p 1861458549, p 772222283, p 257001481]
/-- Generator list for `w64_s2`. -/
def rkmHbWin_w64_s2 : List ℤ := altBuildHbFrom 256 1024 97199393939 0 256
/-- Entry `rkmXsWin_w64_s2_in`. -/
def rkmXsWin_w64_s2_in : List ℤ := let p := rkmP; [p 1396351305, p 7646591317, p 29906037377,
  p 95521986778, p 262489652791, p 641595839033, p 1423751003804, p 2908391505966, p 5526162130401,
  p 9843312390064, p 16537830127741, p 26339284389309, p 39929778471492, p 57816444132672,
  p 80193341013117, p 106818622466652, p 136938198551725, p 169278196186158, p 202119132834635,
  p 233450132478908, p 261181108315583, p 283381664757775, p 298507333095541, p 305574918154080,
  p 304261992060687, p 294916337790030, p 278480423854463, p 256349604905209, p 230189697134740,
  p 201746681813319, p 172674030686398, p 144398498060820, p 118035702141409, p 94354739984785,
  p 73788006990178, p 56472838142594, p 42312892374571, p 31047420746247, p 22316423474229,
  p 15717824501699, p 10850242973748, p 7342927697831, p 4872800460386, p 3171452944715,
  p 2024853435481, p 1268374115789, p 779741304438, p 470424212711, p 278569721585, p 161967134799,
  p 92422152944, p 51825465559, p 28431710970, p 15279367096, p 7989902343, p 4021359772,
  p 1861458549, p 772222283, p 257001481]
/-- Exit `rkmXsWin_w64_s2_out`. -/
def rkmXsWin_w64_s2_out : List ℤ := let p := rkmP; [p 235319579, p 519769118, p 880812455,
  p 1557269429, p 2568973982, p 4350550376, p 7194457137, p 11636041596, p 18715960903,
  p 29604398293, p 46419439454, p 71812656275, p 109663508674, p 165567650577, p 246807703480,
  p 363742856166, p 529603527722, p 762095111758, p 1083852029942, p 1523492713588,
  p 2116821599529, p 2907367766011, p 3947605502119, p 5299145126235, p 7033078355997,
  p 9229459571765, p 11976310726934, p 15367746913365, p 19501081314996, p 24473356425919,
  p 30376152442439, p 37290549191719, p 45280498747701, p 54386123719788, p 64617452262933,
  p 75947358392716, p 88306882081863, p 101580879140340, p 115606033973181, p 130171540768211,
  p 145021649150480, p 159862142337016, p 174368355866151, p 188196777041324, p 200998109517698,
  p 212431347784130, p 222179548169795, p 229963573131072, p 235556081061905, p 238792008059203,
  p 239576970290360, p 237891752444670, p 233792830482762, p 227409568551226, p 218937269543828,
  p 208627462325924, p 196775362265016, p 183706287607831, p 169760738964072, p 155280146080722,
  p 140593554467089, p 126005580359370, p 111787687909709, p 98170658065879, p 85340702651127,
  p 73438022476749, p 62557296379014, p 52750966178227, p 44033075952472, p 36385302520047,
  p 29762696790473, p 24099992466915, p 19318059834018, p 15328839237340, p 12040825788339,
  p 9362662028251, p 7206689311222, p 5491276093987, p 4141898860808, p 3092620390738,
  p 2285769912218, p 1672338001218, p 1211192069261, p 868261874285, p 616168357071,
  p 432747123067, p 300858926088, p 207042559105, p 140989096653, p 95065950402, p 63328319924,
  p 41732769494, p 27106723449, p 17313182395, p 10867334264, p 6555617663, p 3821375418,
  p 2010864212, p 916127320, p 316729513]
/-- Generator list for `w64_s3`. -/
def rkmHbWin_w64_s3 : List ℤ := altBuildHbFrom 512 1024 51677427350 0 512
/-- Entry `rkmXsWin_w64_s3_in`. -/
def rkmXsWin_w64_s3_in : List ℤ := let p := rkmP; [p 235319579, p 519769118, p 880812455,
  p 1557269429, p 2568973982, p 4350550376, p 7194457137, p 11636041596, p 18715960903,
  p 29604398293, p 46419439454, p 71812656275, p 109663508674, p 165567650577, p 246807703480,
  p 363742856166, p 529603527722, p 762095111758, p 1083852029942, p 1523492713588,
  p 2116821599529, p 2907367766011, p 3947605502119, p 5299145126235, p 7033078355997,
  p 9229459571765, p 11976310726934, p 15367746913365, p 19501081314996, p 24473356425919,
  p 30376152442439, p 37290549191719, p 45280498747701, p 54386123719788, p 64617452262933,
  p 75947358392716, p 88306882081863, p 101580879140340, p 115606033973181, p 130171540768211,
  p 145021649150480, p 159862142337016, p 174368355866151, p 188196777041324, p 200998109517698,
  p 212431347784130, p 222179548169795, p 229963573131072, p 235556081061905, p 238792008059203,
  p 239576970290360, p 237891752444670, p 233792830482762, p 227409568551226, p 218937269543828,
  p 208627462325924, p 196775362265016, p 183706287607831, p 169760738964072, p 155280146080722,
  p 140593554467089, p 126005580359370, p 111787687909709, p 98170658065879, p 85340702651127,
  p 73438022476749, p 62557296379014, p 52750966178227, p 44033075952472, p 36385302520047,
  p 29762696790473, p 24099992466915, p 19318059834018, p 15328839237340, p 12040825788339,
  p 9362662028251, p 7206689311222, p 5491276093987, p 4141898860808, p 3092620390738,
  p 2285769912218, p 1672338001218, p 1211192069261, p 868261874285, p 616168357071,
  p 432747123067, p 300858926088, p 207042559105, p 140989096653, p 95065950402, p 63328319924,
  p 41732769494, p 27106723449, p 17313182395, p 10867334264, p 6555617663, p 3821375418,
  p 2010864212, p 916127320, p 316729513]
/-- Exit `rkmXsWin_w64_s3_out`. -/
def rkmXsWin_w64_s3_out : List ℤ := let p := rkmP; [p 167471570, p 398761704, p 668078071,
  p 1132690329, p 1872049499, p 3003506106, p 4896330265, p 7729811679, p 12157657717,
  p 18827668228, p 28821635294, p 43717811533, p 65518036753, p 97280810745, p 142777569773,
  p 207352917658, p 297988383307, p 423744791245, p 596451018322, p 830813940799, p 1145604985158,
  p 1563763890355, p 2113238717962, p 2827491888833, p 3745744463345, p 4913732132657,
  p 6383200034043, p 8212074228739, p 10463572154621, p 13205159121563, p 16507214634492,
  p 20440465683802, p 25073840733542, p 30470927355472, p 36686644921927, p 43763358203996,
  p 51726557024779, p 60581292931836, p 70307965630124, p 80859569402976, p 92159006336723,
  p 104097860048620, p 116536378068195, p 129304684954455, p 142205661180324, p 155019364281302,
  p 167508553924748, p 179426202961859, p 190523044947474, p 200556501350494, p 209299441190478,
  p 216548411477135, p 222132184886675, p 225917810938572, p 227816378919270, p 227786336157265,
  p 225834598794411, p 222016646748461, p 216433336365399, p 209226969992600, p 200575147477753,
  p 190683540117425, p 179777912529658, p 168095684618648, p 155877591895192, p 143359822425220,
  p 130766579834492, p 118304514121759, p 106157216995523, p 94482145216641, p 83408637914161,
  p 73036585499436, p 63437621120431, p 54655953532688, p 46711034791311, p 39600556132188,
  p 33303358749628, p 27783539207261, p 22993543608397, p 18877764601786, p 15375406287166,
  p 12423353990899, p 9958560981809, p 7919630968148, p 6248318493496, p 4890876071167,
  p 3798129588254, p 2926389550284, p 2237054122984, p 1696615957510, p 1276744853931,
  p 953213612511, p 706080148189, p 518927927911, p 378391857482, p 273752048643, p 196416581318,
  p 139711963597, p 98573110692, p 68798105787, p 47546556898, p 32485174462, p 21823612492,
  p 14419127582, p 9301573583, p 5744654524, p 3457879573, p 1844798455, p 826948434, p 273532385]
/-- Generator list for `w64_s4`. -/
def rkmHbWin_w64_s4 : List ℤ := altBuildHbFrom 1024 1024 29638027559 0 1024
/-- Entry `rkmXsWin_w64_s4_in`. -/
def rkmXsWin_w64_s4_in : List ℤ := let p := rkmP; [p 167471570, p 398761704, p 668078071,
  p 1132690329, p 1872049499, p 3003506106, p 4896330265, p 7729811679, p 12157657717,
  p 18827668228, p 28821635294, p 43717811533, p 65518036753, p 97280810745, p 142777569773,
  p 207352917658, p 297988383307, p 423744791245, p 596451018322, p 830813940799, p 1145604985158,
  p 1563763890355, p 2113238717962, p 2827491888833, p 3745744463345, p 4913732132657,
  p 6383200034043, p 8212074228739, p 10463572154621, p 13205159121563, p 16507214634492,
  p 20440465683802, p 25073840733542, p 30470927355472, p 36686644921927, p 43763358203996,
  p 51726557024779, p 60581292931836, p 70307965630124, p 80859569402976, p 92159006336723,
  p 104097860048620, p 116536378068195, p 129304684954455, p 142205661180324, p 155019364281302,
  p 167508553924748, p 179426202961859, p 190523044947474, p 200556501350494, p 209299441190478,
  p 216548411477135, p 222132184886675, p 225917810938572, p 227816378919270, p 227786336157265,
  p 225834598794411, p 222016646748461, p 216433336365399, p 209226969992600, p 200575147477753,
  p 190683540117425, p 179777912529658, p 168095684618648, p 155877591895192, p 143359822425220,
  p 130766579834492, p 118304514121759, p 106157216995523, p 94482145216641, p 83408637914161,
  p 73036585499436, p 63437621120431, p 54655953532688, p 46711034791311, p 39600556132188,
  p 33303358749628, p 27783539207261, p 22993543608397, p 18877764601786, p 15375406287166,
  p 12423353990899, p 9958560981809, p 7919630968148, p 6248318493496, p 4890876071167,
  p 3798129588254, p 2926389550284, p 2237054122984, p 1696615957510, p 1276744853931,
  p 953213612511, p 706080148189, p 518927927911, p 378391857482, p 273752048643, p 196416581318,
  p 139711963597, p 98573110692, p 68798105787, p 47546556898, p 32485174462, p 21823612492,
  p 14419127582, p 9301573583, p 5744654524, p 3457879573, p 1844798455, p 826948434, p 273532385]
/-- Exit `rkmXsWin_w64_s4_out`. -/
def rkmXsWin_w64_s4_out : List ℤ := let p := rkmP; let n := rkmN; [p 208475749, p 386014885,
  p 525333499, p 455252394, p 35298947, n 715660460, n 1855818299, n 3223716549, n 4253275202,
  n 4232268483, n 2394487412, p 2482418525, p 10863091018, p 22547258948, p 36082717707,
  p 47755387050, p 51639115495, p 39527302265, p 1346751471, n 72896147310, n 190375855259,
  n 351709745780, n 545808339397, n 743561960009, n 892485334325, n 910406485342, n 681192365555,
  n 53131098634, p 1160199295956, p 3174848092231, p 6226956981310, p 10559333073392,
  p 16404700593234, p 23965808988182, p 33395075751257, p 44775036613076, p 58101146947046,
  p 73269359079508, p 90070447563239, p 108190189748895, p 127218429847025, p 146665028896870,
  p 165981868733857, p 184590379525564, p 201911715468875, p 217397344078097, p 230557880596850,
  p 240988729520037, p 248389733532730, p 252577774748094, p 253492496193230, p 251194670802832,
  p 245856745432672, p 237748944731940, p 227220131203274, p 214675991337184, p 200556385446120,
  p 185313079971181, p 169389094260290, p 153200782215716, p 137124129857374, p 121484447607337,
  p 106549700496227, p 92528508621575, p 79570979824947, p 67771845276927, p 57176159911061,
  p 47786675916372, p 39570828273556, p 32468947922410, p 26401691198462, p 21277038518749,
  p 16996080494740, p 13458013419912, p 10564505444230, p 8222261558362, p 6345008745819,
  p 4855198198630, p 3684313517836, p 2772654459695, p 2069360143248, p 1531855710058,
  p 1124780751493, p 819115650123, p 591652744755, p 423832021960, p 301160860410, p 212087432296,
  p 147969569060, p 102337756620, p 70029753905, p 47269417547, p 31471144421, p 20639132786,
  p 13200932185, p 8115778866, p 4744917810, p 2590661298, p 1223150569, p 380758498]

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
private def rkmPhb_w64_s0 : List ℕ := uNatCatN
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
private def rkmPhb_w64_s1 : List ℕ := uNatCatN
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
private def rkmPhb_w64_s2 : List ℕ := uNatCatN
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
private def rkmPhb_w64_s3 : List ℕ := uNatCatN
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
private def rkmPhb_w64_s4 : List ℕ := uNatCatN
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
private theorem rkmStatOk_hiw64t10 : bAllT [
  muxIntListEq (uHb rkmPhb_w64_s0) (altBuildHbFrom 64 1024 361115083333 0 64),
  muxIntListEq (uHb rkmPhb_w64_s1) (altBuildHbFrom 128 1024 186696904761 0 128),
  muxIntListEq (uHb rkmPhb_w64_s2) (altBuildHbFrom 256 1024 97199393939 0 256),
  muxIntListEq (uHb rkmPhb_w64_s3) (altBuildHbFrom 512 1024 51677427350 42 470),
  muxIntListEq (uHb rkmPhb_w64_s4) (altBuildHbFrom 1024 1024 29638027559 206 818),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_s0_in)) (Nat.add 64 1),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_s1_in)) (Nat.add 128 1),
  Nat.ble (Nat.add 0 (altIntLen rkmXsWin_w64_s2_in)) (Nat.add 256 1),
  Nat.ble (Nat.add 58 (altIntLen rkmXsWin_w64_s3_in)) (Nat.add 512 1),
  Nat.ble (Nat.add 222 (altIntLen rkmXsWin_w64_s4_in)) (Nat.add 1024 1)
  ] = true := by decide +kernel
private theorem rkmHhb_w64_s0 :
    uHb rkmPhb_w64_s0 = rkmDropInts 0 rkmHbWin_w64_s0 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd rkmStatOk_hiw64t10)).trans
    (drHb 64 1024 361115083333 0 64)
private theorem rkmHhb_w64_s1 :
    uHb rkmPhb_w64_s1 = rkmDropInts 0 rkmHbWin_w64_s1 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl rkmStatOk_hiw64t10))).trans
    (drHb 128 1024 186696904761 0 128)
private theorem rkmHhb_w64_s2 :
    uHb rkmPhb_w64_s2 = rkmDropInts 0 rkmHbWin_w64_s2 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl rkmStatOk_hiw64t10)))).trans
    (drHb 256 1024 97199393939 0 256)
private theorem rkmHhb_w64_s3 :
    uHb rkmPhb_w64_s3 = rkmDropInts 42 rkmHbWin_w64_s3 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl rkmStatOk_hiw64t10))))).trans
    (drHb 512 1024 51677427350 42 512)
private theorem rkmHhb_w64_s4 :
    uHb rkmPhb_w64_s4 = rkmDropInts 206 rkmHbWin_w64_s4 :=
  (muxIntListEq_eq_true.mp
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl rkmStatOk_hiw64t10)))))).trans
    (drHb 1024 1024 29638027559 206 1024)
private theorem rkmWC_w64_s0_0 : bWinChk 0 12 100000000 64 rkmPhb_w64_s0
    0 rkmXsWin_w64_s0_in 0 rkmXsWin_w64_s0_out 665633573 = true := by decide +kernel
private theorem rkmWinIter_w64_s0 :
    RkmWinIterSound 12 64 rkmHbWin_w64_s0 0 rkmXsWin_w64_s0_in
      0 rkmXsWin_w64_s0_out 665633573 :=
  bWinChk_sound rkmHhb_w64_s0 rkmWC_w64_s0_0
/-- Certified `w64` seg `0` (`12` steps). -/
theorem rkmWinSegWalkSnd_w64_s0 :
    RkmWinSegWalkSound 12 ⟨64, rkmHbWin_w64_s0, 0, rkmXsWin_w64_s0_in,
      0, rkmXsWin_w64_s0_out, 665633573⟩ :=
  @rkmSegWalk_mk 12 64 0 0 665633573
    rkmHbWin_w64_s0 rkmXsWin_w64_s0_in rkmXsWin_w64_s0_out
    (rkmw_buildHbFrom_length 64 1024 361115083333 64 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl rkmStatOk_hiw64t10))))))
    rkmWinIter_w64_s0
private theorem rkmWC_w64_s1_0 : bWinChk 0 21 100000000 128 rkmPhb_w64_s1
    0 rkmXsWin_w64_s1_in 0 rkmXsWin_w64_s1_out 1380127811 = true := by decide +kernel
private theorem rkmWinIter_w64_s1 :
    RkmWinIterSound 21 128 rkmHbWin_w64_s1 0 rkmXsWin_w64_s1_in
      0 rkmXsWin_w64_s1_out 1380127811 :=
  bWinChk_sound rkmHhb_w64_s1 rkmWC_w64_s1_0
/-- Certified `w64` seg `1` (`21` steps). -/
theorem rkmWinSegWalkSnd_w64_s1 :
    RkmWinSegWalkSound 21 ⟨128, rkmHbWin_w64_s1, 0, rkmXsWin_w64_s1_in,
      0, rkmXsWin_w64_s1_out, 1380127811⟩ :=
  @rkmSegWalk_mk 21 128 0 0 1380127811
    rkmHbWin_w64_s1 rkmXsWin_w64_s1_in rkmXsWin_w64_s1_out
    (rkmw_buildHbFrom_length 128 1024 186696904761 128 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl
      rkmStatOk_hiw64t10)))))))
    rkmWinIter_w64_s1
private def rkmC_w64_s2_1 : List ℤ := pzigCat
  [
   [512598912,987520258,2032791544,4069603450,7631747376,14254077242,25775167250,45760758154,
    79403040050,134957181808,225049106796,368088084150,590474785700,930037995846,1438483015728,
    2185070650436,3261797895206,4785825508086,6903774541148,9794881136036,13670523006040,
    18774249285260,25376860352722,33768126995348,44245590862016,57097136071156,72581814346926,
    90906426127460,112199959236182,136489313742542,163675746079676,193517458691782,
    225617650721602,259421727502992,294226578093862,329199023929594,363406785405862,
    395858296746526,425550119493280,451519543000026,472895722075658,488949254713104,
    499133301784196,503114225895638,500790005536022,492292703540304,477978572696668,
    458403401835432,434287376768206,406472530381102,375874310875242,343434321353624,
    310073796359408,276653591469748,243941886710878,212589758083650,183118100335648,
    155911618828824,131222572585722,109180664077548,89807342624836,73034885111872,58724771827722,
    46688059348052,36703213956774,28531994576116,21933720358908,16674654387932,12536827747146,
    9322256179874,6855926381968,4987167035522,3588148518598,2553640025970,1797680246024,
    1251806435420,862416238776,587641480362,396235586830,264198180318,174227014076,113642283384,
    73120979802,46575191818,29108780284,17920984032,10729261848,6042525538,3202365364,1267325118,
    362644444]]
private theorem rkmWC_w64_s2_0 : bWinChk 0 37 100000000 256 rkmPhb_w64_s2
    0 rkmXsWin_w64_s2_in 23 rkmC_w64_s2_1 5214223884 = true := by decide +kernel
private theorem rkmWC_w64_s2_1 : bWinChk 0 29 100000000 256 rkmPhb_w64_s2
    23 rkmC_w64_s2_1 58 rkmXsWin_w64_s2_out 5028925946 = true := by decide +kernel
private theorem rkmWinIter_w64_s2 :
    RkmWinIterSound 66 256 rkmHbWin_w64_s2 0 rkmXsWin_w64_s2_in
      58 rkmXsWin_w64_s2_out 10243149830 :=
  rkmChS 66 10243149830 (bWinChk_sound rkmHhb_w64_s2 rkmWC_w64_s2_0) rkmHhb_w64_s2
    rkmWC_w64_s2_1 rfl rfl
/-- Certified `w64` seg `2` (`66` steps). -/
theorem rkmWinSegWalkSnd_w64_s2 :
    RkmWinSegWalkSound 66 ⟨256, rkmHbWin_w64_s2, 0, rkmXsWin_w64_s2_in,
      58, rkmXsWin_w64_s2_out, 10243149830⟩ :=
  @rkmSegWalk_mk 66 256 0 58 10243149830
    rkmHbWin_w64_s2 rkmXsWin_w64_s2_in rkmXsWin_w64_s2_out
    (rkmw_buildHbFrom_length 256 1024 97199393939 256 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl
      rkmStatOk_hiw64t10))))))))
    rkmWinIter_w64_s2
private def rkmC_w64_s3_1 : List ℤ := pzigCat
  [
   [214503226,579890060,966879188,1684420422,2789876072,4468596218,7263141248,11398050032,
    18002075794,27947489640,42797428518,65196199188,97968447670,145944628354,215215816554,
    314168888470,454183594402,649858563580,920952428260,1292127681268,1795200451190,
    2469894802546,3364860386786,4540016628850,6066262274532,8027695946012,10521605691856,
    13658471707682,17561986969294,22366540242954,28216259131526,35260307415344,43648493416346,
    53525922647100,65024973198834,78258519413288,93310020862388,110225319438800,129003849074378,
    149589672101574,171865870579160,195648351931626,220684281200452,246652257553266,
    273165688378450,299781148856714,326007814642498,351322585103254,375186300221142,
    397062421572818,416437620638036,432840493577770,445861890245584,455171107182272,
    460530104692016,461803952375778,458965424592644,452097222541816,441386983097660,
    427119391240048,409663617792582,389456813405364,366987254374538,342773786331850,
    317347193936114,291230931244586,264923640001494,238885390491820,213524718240422,
    189191346336368,166170218166402,144679718400896,124873267119482,106841829261762,
    90620820179440,76196043897928,63512285867028,52481764387364,42991708174584,34913431181212,
    28108126338402,22434022385712,17751014696400,13924396426972,10828755758942,8348697871148,
    6381292045644,4835577104474,3632680417372,2705709485554,1997830793510,1462592120880,
    1061523161564,763783103068,544938711294,385297186438,270165996178,187630504362,129080435646,
    87932120840,59080724868,39283167974,25537364204,16275585544,10001528998,5720342242,
    3046787628,1201036216,341108484]]
private def rkmC_w64_s3_2 : List ℤ := pzigCat
  [
   [561654252,972652832,1620529412,2779619672,4303773470,6848406774,10613169440,16363217842,
    25071729706,37778376144,56692336418,84069304446,123641751446,180241932696,260172861766,
    372394308102,527901852380,741723172730,1032714631096,1424744889422,1948109872986,
    2639572110350,3544741375060,4717840901338,6223293668624,8136549653808,10543783087564,
    13543120927520,17242707520490,21760553475462,27222276004146,33757915037402,41499174840266,
    50573285222544,61098722547070,73178137101318,86891534966454,102289680523798,119385527342924,
    138148802330362,158498894045402,180300774338346,203362266124246,227432246130980,
    252203705858724,277316724374596,302366638615770,326913520507158,350493748775232,
    372635368591022,392871941391852,410760468651078,425896245661616,437928790245082,
    446575237264894,451631014973140,452978459670112,450590802812544,444533468362544,
    434960746885874,422109680299958,406289919295712,387871708896122,367271655547494,
    344936568640396,321328706656072,296909029673772,272123505363654,247390492982658,
    223089331798362,199553302909024,177063026214500,155844256651874,136066844289958,
    117846396761716,101248472684696,86292233110420,72957702898528,61191461178126,50913676029778,
    42025005113558,34412090073556,27954545284522,22528545368710,18011795055810,14286624888648,
    11242081743874,8776599848810,6797620576876,5223359445192,3982045717882,3011723958378,
    2260127302690,1682678350240,1243039444236,910986881358,662293530948,477789127178,
    341802394676,242690803446,170772483014,119079183498,82239388048,56003391250,37756029684,
    24885290994,16092708852,10036712814,5819026056,3137535468,1246524000,355810298]]
private def rkmC_w64_s3_3 : List ℤ := pzigCat
  [
   [436414214,825380840,1415565054,2368746514,3722048304,6017394802,9261216906,14209933744,
    21692217804,32635249622,49009651746,72618632368,106702536598,155437772834,224307225912,
    321006982230,455016215352,639323589372,890120628572,1228374339496,1680410687644,
    2278278037378,3061982236628,4079025738316,5386486474690,7051293607292,9150494776232,
    11772238362650,15014416596918,18985255696322,23800712313436,29582778162170,36456828952714,
    44546658175750,53971190718432,64837745044424,77236835963968,91235208455034,106868621948968,
    124136457892156,142994097292756,163349089681856,185056541498266,207917089085000,
    231677481785510,256031420097210,280626109023286,305067811838980,328932601839602,
    351777407141986,373153474202616,392621323589772,409765026394420,424207572419832,
    435624247669864,443755173268060,448414737824452,449498979067058,446989210146108,
    440952492137186,431539199830578,418975723020504,403556655293838,385632605866458,
    365597132455810,343873220348558,320897483487392,297107060907562,272925561889556,
    248751679679614,224949197974096,201838771112314,179693652055330,158735351807644,
    139133899392236,121008615903134,104430715201444,89428269639518,75990481895670,64074883237254,
    53612415928026,44513917628142,36676322475662,29987224459858,24330777975018,19590460708216,
    15653331503088,12412265160194,9767323410804,7627800457642,5911620415618,4546844901104,
    3470671875134,2629122437278,1976779578138,1474979228226,1092341651426,802779155402,
    585434495296,423768713344,304245279790,216821828356,153121740686,107146311188,74232349198,
    50690731564,34226169384,22547717666,14520043728,8969820164,5125733986,2707292874,1053436962,
    294719910]]
private def rkmC_w64_s3_4 : List ℤ := pzigCat
  [
   [482108210,981460012,1634546722,2839882578,4360672474,6867587242,10723888748,16562960454,
    25478326204,38562687510,58018125008,86263681588,127153647398,185637251826,268319097084,
    384432859094,545293243856,766462584534,1067372629038,1472604916210,2013098055120,
    2726514930532,3659337194684,4866602131716,6413830288140,8377090134636,10843189762786,
    13910476657344,17686874613992,22289836623306,27843432331974,34475835987862,42315620833528,
    51486194297958,62101652220448,74259199713184,88033210090534,103467921048788,120570234120730,
    139304177002616,159584043610290,181271450437910,204171927378682,228034720210870,
    252555262419106,277378826715080,302108927211380,326315627246678,349548227422890,
    371348830683310,391266710032630,408874674646204,423783030075290,435655198843072,
    444219709266720,449280566490480,450725184941788,448527492326070,442749912493268,
    433539390885538,421121849786246,405793033070634,387906304842852,367860288605524,
    346083010912992,323018002159888,299109162373124,274787099600192,250457666904510,
    226490624884438,203212909746764,180902198007722,159784343056820,140032706905184,
    121768578267050,105065171491678,89950824131358,76415306402270,64415514065736,53881516279086,
    44723557197938,36836893236974,30108343715664,24420356490488,19655367024220,15699441551268,
    12443981318770,9788596544226,7641282732980,5919722333436,4551333316200,3472651842596,
    2629695632594,1976257075994,1474012717930,1091150028530,801533127624,584389391154,
    422678728184,303351430892,215925337906,152324682680,106527678914,73607444258,50273978202,
    33731585906,22126691818,14130338182,8588092514,4931350702,2676567484,1044515552,287830298]]
private theorem rkmWC_w64_s3_0 : bWinChk 42 25 100000000 512 rkmPhb_w64_s3
    58 rkmXsWin_w64_s3_in 87 rkmC_w64_s3_1 4273829253 = true := by decide +kernel
private theorem rkmWC_w64_s3_1 : bWinChk 42 23 100000000 512 rkmPhb_w64_s3
    87 rkmC_w64_s3_1 119 rkmC_w64_s3_2 4382603482 = true := by decide +kernel
private theorem rkmWC_w64_s3_2 : bWinChk 42 23 100000000 512 rkmPhb_w64_s3
    119 rkmC_w64_s3_2 152 rkmC_w64_s3_3 4721625402 = true := by decide +kernel
private theorem rkmWC_w64_s3_3 : bWinChk 42 23 100000000 512 rkmPhb_w64_s3
    152 rkmC_w64_s3_3 187 rkmC_w64_s3_4 4357379916 = true := by decide +kernel
private theorem rkmWC_w64_s3_4 : bWinChk 42 23 100000000 512 rkmPhb_w64_s3
    187 rkmC_w64_s3_4 222 rkmXsWin_w64_s3_out 4417886903 = true := by decide +kernel
private theorem rkmWinIter_w64_s3 :
    RkmWinIterSound 117 512 rkmHbWin_w64_s3 58 rkmXsWin_w64_s3_in
      222 rkmXsWin_w64_s3_out 22153324956 :=
  rkmChS 117 22153324956 (rkmChS 94 17735438053 (rkmChS 71 13378058137 (rkmChS 48 8656432735
    (bWinChk_sound rkmHhb_w64_s3 rkmWC_w64_s3_0) rkmHhb_w64_s3 rkmWC_w64_s3_1 rfl rfl)
    rkmHhb_w64_s3 rkmWC_w64_s3_2 rfl rfl) rkmHhb_w64_s3 rkmWC_w64_s3_3 rfl rfl) rkmHhb_w64_s3
    rkmWC_w64_s3_4 rfl rfl
/-- Certified `w64` seg `3` (`117` steps). -/
theorem rkmWinSegWalkSnd_w64_s3 :
    RkmWinSegWalkSound 117 ⟨512, rkmHbWin_w64_s3, 58, rkmXsWin_w64_s3_in,
      222, rkmXsWin_w64_s3_out, 22153324956⟩ :=
  @rkmSegWalk_mk 117 512 58 222 22153324956
    rkmHbWin_w64_s3 rkmXsWin_w64_s3_in rkmXsWin_w64_s3_out
    (rkmw_buildHbFrom_length 512 1024 51677427350 512 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl
      rkmStatOk_hiw64t10)))))))))
    rkmWinIter_w64_s3
private def rkmC_w64_s4_1 : List ℤ := pzigCat
  [
   [553280730,996095842,1860343448,3064095030,5131634864,8465160186,13457436318,21481585658,
    33586078870,52167572674,80015583226,121123640278,181342884140,268283703398,392339994262,
    567492083960,811584863180,1148196101160,1606876416938,2224783270008,3047908785166,
    4131830830936,5543625146630,7361575833748,9676843919098,12592890860608,16224615199068,
    20698232930408,26147340342268,32711155434218,40529793862306,49738787564512,60463267988302,
    72810580845772,86862568327540,102668124325654,120234918615602,139522959903544,
    160437782056096,182826324482740,206474705455808,231107570883508,256392116051878,
    281942354410100,307328674557904,332088910574136,355741346083886,377800941098822,
    397795801039068,415283291542750,429867418537006,441212748985476,449058156628946,
    453226308101336,453630210249714,450276574810296,443264635503340,432781050696186,
    419092554768626,402533830659860,383495189326200,362407065300642,339723326041546,
    315907367956102,291415422874544,266683331139684,242115387609636,218073798369908,
    194872859303968,172773406300220,151981727562940,132649559122968,114876207065894,
    98713292280352,84168710447394,71214203776972,59790619238602,49814741640142,41186282582480,
    33792659783792,27515698112278,22234659970922,17831361690342,14192282883474,11210887506484,
    8789307991834,6839155323566,5281982168366,4048894141470,3080727024970,2326553153224,
    1743977603598,1297716884914,958353394902,702505840404,510956086166,368825049130,264075723346,
    187343807778,131809253046,91717951856,63206444820,42891771992,28524070092,18590019046,
    11607030832,7034084894,3867006890,1851081976,672386324]]
private def rkmC_w64_s4_2 : List ℤ := pzigCat
  [
   [609967632,1057623798,1934599046,3315707272,5501504798,9219725282,15104617914,24277946164,
    38689233586,60559929054,93561425388,142713436420,214649427486,319009170382,468083677934,
    678678944434,972427465204,1376504197776,1926390130272,2665197132608,3646245482454,
    4933884001764,6603611088878,8744132584620,11456085176114,14852708345782,19058290400690,
    24205979167454,30435019343120,37885955487176,46697242026202,56997002243906,68897638596288,
    82487716307780,97823961820646,114923882911200,133757945365880,154244153566058,
    176242716716542,199553599348066,223915804186106,249010090381040,274464006401548,
    299859719911778,324745178651486,348646424886646,371083513707070,391585521165820,
    409707566274978,425047534568760,437259670768158,446068933148152,451280338487990,
    452786526848712,450571318230522,444708987806264,435361490131708,422769985783956,
    407245827211500,389157261117732,368915158048392,346958772788222,323739086371126,
    299705338751512,275290467559888,250899850870064,226901536036068,203617833665932,
    181321879291094,160233687172708,140520771780466,122299215742354,105636717437228,
    90558318639442,77050310891132,65067870195256,54539998169464,45376590833976,37473901488962,
    30719665594490,24998021115812,20193226519968,16193085348870,12890900512100,10187907973856,
    7993481678348,6226484399892,4815433805606,3697412755518,2818822858468,2133682914134,
    1603587468126,1196599281846,886343597042,651950474136,475976293308,344933302094,247972166654,
    176685471856,124914640948,87347454922,60486503918,41239836254,27570650426,18084547048,
    11367212596,6930343916,3821413226,1828790474,662482972]]
private def rkmC_w64_s4_3 : List ℤ := pzigCat
  [
   [314218734,827188564,1504114274,2655416072,4955137196,8515151898,14445298262,23733034426,
    38455623706,61578468212,96800288482,149989791614,228678020440,343781988158,509407686762,
    744509569002,1074138304902,1529400719844,2150363103788,2986083566196,4096656349638,
    5554095129848,7442597653792,9860163475278,12916739154830,16735142904356,21447884814210,
    27195245440616,34121319638482,42368617013126,52072880894314,63355565504632,76316894292852,
    91027306792396,107519778768144,125782140151030,145750402274952,167303403263422,
    190259215199022,214374880069154,239346864929084,264816410617732,290376446831732,
    315581502477008,339961205615528,363033344958624,384321115734550,403369128205202,
    419759600439254,433128162497528,443176557442928,449684856243794,452518279268330,
    451632443730794,447073953378188,438976903474824,427557877494988,413105239710796,
    395968298524196,376543076140078,355257604453982,332557359145638,308889158477260,
    284688890728812,260368216262064,236304797302862,212834356464306,190244251168902,
    168771496197114,148600246560368,129863919758532,112647460788360,96991161828834,
    82896610365896,70331050116320,59234972614756,49527136087602,41110711281270,33878912518614,
    27718748551906,22516673325050,18160557952620,14543305110054,11564415373376,9130839527354,
    7158990506756,5573616144038,4309180063596,3308537647804,2522580385072,1910197386214,
    1436287262980,1072570653152,795298766904,585568693864,428075094566,310633951110,223632908820,
    159663503482,113045078188,79089895680,54809056652,37487209876,25149486282,16443611622,
    10204375372,6069225336,3255635686,1519251802,540257366]]
private def rkmC_w64_s4_4 : List ℤ := pzigCat
  [
   [242472104,552217558,1281898520,2409839028,4628742998,8545446922,15057207104,25985678876,
    43395275948,71315826224,114672383816,180682946284,279707804378,425352682096,636505080152,
    937299359100,1359689031778,1943896058560,2739860492256,3809440853444,5226333554454,
    7078388175846,9466802663022,12506543848868,16325466408246,21061657781774,26861705291822,
    33874963017838,42249577164948,52125614645352,63627411845298,76856300459022,91880896480556,
    108730364419344,127385373447246,147771772551002,169755858974966,193140289018462,
    217665136293536,243008430656264,268793090151000,294594285159378,319950830935984,
    344378904790304,367386936876790,388492934718894,407240879510732,423217698528686,
    436068202807980,445508557917892,451336278688166,453437463078146,451790490046690,
    446465067006656,437619300129320,425491097798834,410388480416846,392677219100158,
    372765716730544,351091049965886,328102605964122,304248057552448,279959750894002,
    255642867761680,231666343159056,208354326309014,185982461943998,164774443987966,
    144901809182472,126485922637906,109600249170784,94275731369788,80504946892864,68248857695066,
    57442725472976,48001526800364,39826548724290,32809480880528,26838097326270,21799380463000,
    17582743646950,14083114179054,11201749207722,8848570081394,6941728456060,5408482168252,
    4185216125218,3216457898074,2455332316576,1861605064888,1401920998158,1048604585792,
    778806361358,574515111044,420720610210,305955842726,220853260486,158084132044,112260691116,
    78786064442,54724966374,37415741254,25090900918,16487134210,10348565132,6256345170,
    3395160066,1589570662,562491474]]
private def rkmC_w64_s4_5 : List ℤ := pzigCat
  [
   [495323172,1549804458,3520481438,7462297542,14355320186,26510311202,46992503640,80213464516,
    133350810532,215813403382,341342279050,528268518970,801148438986,1192392542442,1743215606550,
    2506111809232,3545328406170,4939158160428,6780235704032,9175952561062,12249053748786,
    16135188988564,20981816959884,26943984786434,34179957417416,42845409286738,53085609185942,
    65028423249596,78774276587708,94388043200202,111889854730808,131246612480296,152366190262256,
    175091643937484,199199913601744,224401283113176,250343283971370,276618006589244,
    302771118110992,328315759732202,352746561362050,375557218619134,396257979098102,
    414392978826388,429558109408398,441414836366770,449703681729306,454252879079588,
    454984281490510,451915671079334,445157492794338,434908103590454,421443620769210,
    405106684123592,386292451343294,365432699520578,342981107276240,319396617700110,
    295129848890276,270609525415324,246231389584210,222350195061190,199272377947846,
    177253301670516,156494799853576,137146236972238,119307193120864,103030656165310,
    88329037803504,75178742038568,63527088367060,53298217200808,44398801683710,36724350911364,
    30163037466654,24600985170898,19925124162030,16026272602594,12801693216524,10155750946478,
    8001878736894,6262033060260,4867368701932,3757939787706,2881782067884,2195175211320,
    1660874858944,1248213930074,931823173042,690838991840,508768710884,371954628360,270000588804,
    194481851864,138873539886,98343352874,68811569882,47618476926,32392734594,21565789098,
    14011969758,8665658920,5133694588,2722999646,1244718774,430949368]]
private def rkmC_w64_s4_6 : List ℤ := pzigCat
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
    2311605628438,1750467104886,1316744213330,983782712798,730009519412,538139741368,
    393787916380,286233335098,206404112502,147478054926,104569045996,73305139164,50837545784,
    34652500884,23181182796,15206050408,9513555434,5686900996,3015977708,1365539984,465345792]]
private def rkmC_w64_s4_7 : List ℤ := pzigCat
  [
   [652464811,1271831723,2029608989,2836070357,3386453661,2989326167,38398359,8232594430,
    25995148678,60277813404,121350094494,224730918112,392303402454,653850573592,1049960075634,
    1632906211718,2470002760602,3644600719498,5257580797244,7429062229214,10296842239466,
    14016621904242,18758318560956,24701953668048,32032406380676,40930716405834,51566181296434,
    64085417019782,78601842242654,95184514362068,113847209874100,134539690336488,157139388842778,
    181447925961720,207188817238760,234010005839532,261490245684250,289148854961576,
    316459612065988,342867866469248,367809065419002,390729938217372,411108416673910,
    428474469880492,442427981489398,452653388411500,458932657442852,461151053849072,
    459300992219972,453480093159320,443884450456684,430799767796402,414586628851602,
    395665742633514,374500539112078,351579062863712,327397030217148,302440899619664,
    277174169144610,252024045617434,227372412719266,203548960376224,180826761958202,
    159421128024632,139490483900800,121138731401952,104420606871672,89346289031502,
    75888729055146,63989841352548,53566844571428,44520124659912,36737598035574,30100904213462,
    24489707911878,19785033865692,15873106786252,12646604446480,10006801333678,7863863027404,
    6137714401924,4758109575402,3663754331678,2802050158210,2128758296378,1606294352016,
    1204085213744,896507568938,662801853056,486774944752,354865400288,256803596562,184348540494,
    131216039088,92588992280,64554422314,44390389880,30174870064,19888766600,12825808652,
    7932693762,4500357072,2308857086,854898872,225743388]]
private def rkmC_w64_s4_8 : List ℤ := pzigCat
  [
   [581157103,1673037931,3471705033,5828622271,9030463621,12130824889,13885948153,11319040071,
    674562380,30598353282,91792809702,204118728860,396087133122,707213596852,1190221589876,
    1914147937370,2966046851262,4453499760408,6505202698606,9270684888386,12920078370760,
    17639594553414,23627732993708,31088052291700,40219861727522,51208653058332,64213075193656,
    79353780780914,96699913000500,116257312647262,137958859704672,161656405682308,
    187116467905070,214020253011304,241966983938914,270482978443222,299033821551676,
    327041676705850,353904922716406,379019778342902,401804607311694,421721085171868,
    438296662901642,451142850321076,459969867174072,464597723674194,464961176620944,
    461109750680100,453203925690568,441504736056136,426361504727726,408194970410588,
    387478912712594,364721847226384,340446398893658,315172167243206,289398215124108,
    263589365924986,238165350383884,213491531525604,189873834411336,167557171934134,
    146724633402100,127501066792782,109956778024810,94113892027626,79953202707364,67420279643702,
    56434370565250,46894083174654,38684287748542,31682329507332,25762428734752,20799970880470,
    16675065070302,13274397205222,10493803546776,8238111408386,6422673942352,4973187052698,
    3824411995816,2921093037610,2216040986162,1669757159566,1249611877758,928776245690,
    685590044658,502591483120,365626237896,264158596156,189274048680,134394777476,94636067614,
    65883802846,45235318594,30659341036,20136168286,12941719828,7947558776,4447003764,2229465160,
    803694230,206483148]]
private def rkmC_w64_s4_9 : List ℤ := pzigCat
  [
   [235371458,461470882,815367352,785514112,472139870,357192721,2433698055,5904459083,
    11673594919,19624183215,29225711729,38556310699,43244520431,35515713171,1876007935,
    78892865284,237882739608,519862832870,985332582488,1714343694862,2809197880824,4395562132384,
    6624913476060,9672401611910,13735387838002,19028597978698,25776962090830,34206828103612,
    44534089097648,56950880602216,71611751754172,88618236397226,108005898885224,129730909539518,
    153660231698944,179567069875650,207127798751710,235926460973350,265463035056802,
    295167733221668,324419436131286,352567313316620,378956170894568,402952552542156,
    423969613108960,441492586413240,455098447102284,464472980151994,469422429530368,
    469878984042676,465900799203722,457666334418608,445463107742362,429673323302816,
    410754132885448,389218114505058,365611972935172,340493951172246,314415774069514,
    287903587227674,261443305692948,235469295428134,210355565198084,186411146638666,
    163878541918410,142934309771616,123693583726760,106214444516692,90505487236662,
    76533117388406,64229335184976,53500038526508,44232103434670,36299852439002,29572288900586,
    23916493175262,19202708407146,15307571245464,12115654377966,9521450158670,7430238668432,
    5757578791070,4430568139564,3385835665974,2569501653110,1936634722208,1449567221600,
    1077396467976,795373014812,582843581478,424069872122,306307003710,219431579738,155957802646,
    109861659266,76422151308,52670599288,35634773460,23630977800,15314036214,9412982816,
    5390677302,2814944504,1026848192,261958272]]
private def rkmC_w64_s4_10 : List ℤ := pzigCat
  [
   [284687934,708513712,1501479404,2343681580,2696423286,2627693956,1037425926,3015340667,
    11035029589,24143235181,42847609933,66873143969,92960017765,113470478213,114600586767,
    72077232365,50603917648,306987993850,771690384742,1543503839634,2748794345142,4543642928974,
    7113643773102,10672525652062,15456727363716,21719092887522,29717717205914,39703074675790,
    51903043061230,66505334298362,83640048742934,103363560790170,125642247341186,150342337432582,
    177221813038348,205928460956680,236004920856752,266898494364140,297977561361254,
    328554742580442,357911492570608,385328283857432,410114231706884,431636327204670,
    449347050337522,462806737729034,471700984709046,475853151529626,475227110018534,
    469926174603720,460184149026204,446350475354972,428872049555862,408270829383150,
    385119473399094,360018385723354,333570658434270,306361735581786,278940941039396,
    251805858071098,225391869568128,200064905096356,176117313351706,153769469603674,
    133171329659790,114408457028926,97509359110128,82453010647240,69178184346964,57592496343698,
    47579762621976,39009301450744,31741677584074,25634853253290,20549408735874,16351515669926,
    12915894151902,10128211149730,7884790839634,6094316174692,4676919816052,3563603719984,
    2696113299618,2025459660980,1510738867508,1118992133642,822862929494,600691499026,
    435346752322,313037771516,223285357960,157985453098,110712068930,76685484254,52620688300,
    35307291764,23156082886,14827918758,8994124416,5059157398,2566636870,905237250,223061856]]
private def rkmC_w64_s4_11 : List ℤ := pzigCat
  [
   [466653114,1628273228,3356801250,5347013182,7462612898,8316869244,6656322288,129780788,
    14334109781,39351695987,77145792021,127939778179,187029003717,243296448665,274057448253,
    241440045001,87307421369,272369564532,951381314552,2097312738540,3894565710732,6562654805978,
    10354421518280,15548685502208,22439732240766,31323883256310,42481549043376,56157570886796,
    72541062120492,91742968583122,113778176338416,138549311617478,165835760500024,
    195289964405448,226439743530138,258698665602494,291384993947180,323744989558002,
    354983906661238,384299648415252,410917335880000,434125061356908,453304603982772,
    467958920909446,477732780655186,482425852843472,481997283957044,476563507529468,
    466386561954266,451857728588302,433475272197524,411818020396872,387518269953752,
    361234158590932,333622095209938,305314486108682,276898493047870,248900012356806,
    221773474621348,195893800484786,171554486749892,148969079536586,128275410930660,
    109542166549944,92778666484848,77943241559932,64954053200912,53698882601260,44043824775860,
    35842293212176,28942143339100,23190527988338,18440274217872,14552268645742,11397684059188,
    8860380532426,6836907961400,5236690330116,3981658557838,3005409977462,2251866372922,
    1675130948636,1236976383956,906610532860,659708562352,476451749048,341345448940,242611570928,
    171015173400,119226226472,82366444098,56099310546,37466690108,24564877264,15614694874,
    9399108440,5313121446,2702863456,936888088,224636914]]
private def rkmC_w64_s4_12 : List ℤ := pzigCat
  [
   [416142091,834913195,1237084447,1030206785,30138785,2114188894,5757846126,10653831198,
    16029870974,20466141946,20834345378,13032134288,8469392073,50131157361,116641280675,
    210294605529,326280590509,448540093707,544420616477,557860507481,402562131735,43538950464,
    944658578140,2509430328268,4990608220090,8681817197086,13908531662422,21014236440942,
    30343503832696,42218612546236,56915141777268,74636648293598,95488070327556,119454809015004,
    146384873056468,175978858716464,207788696221104,241225250662006,275574972624358,
    310026880294236,343705155540914,375707642229294,405148660256214,431199303325984,
    453127173932370,470330235597522,482363141342554,488954591633570,490015909748552,
    485638453733194,476083133914656,461761396262612,443208731954700,421056293413806,
    395997944463280,368757634445244,340059124855568,310598745340092,281020911409752,
    251901136518774,223733131253224,196920666479598,171776507604650,148523650918852,
    127301035115140,108172289807580,91136066288612,76136404309554,63075576439588,51824432315148,
    42232290844180,34137093392914,27372406053032,21773637312924,17183607106200,13455232056728,
    10454106268202,8059717981388,6166390294798,4681847220168,3527747696932,2638269110556,
    1958109694730,1442299204486,1054484741252,765127009278,550701770416,393402724424,
    278685933962,195613489314,136056150806,93543196026,63422058518,42391915870,27757985878,
    17546409466,10606045150,6147262136,3033237890,1212604758,351389726]]
private def rkmC_w64_s4_13 : List ℤ := pzigCat
  [
   [342844216,377892846,231774660,341758615,1184247325,2152493405,3121128347,3477977161,
    2349460321,791064140,7215059096,17003471254,29225508642,41555380816,49117926966,44408442960,
    17619781382,42739457999,147467145497,302558647409,505020771627,734593729113,946551087147,
    1062716598807,961822523001,472478416759,631282531182,2632277195328,5865628554976,
    10708143388504,17563078498308,26837182143940,38912448788966,54116274657970,72687473046352,
    94746172774834,120266885986048,149058309842836,180753133741064,214809006092010,
    250520830847546,287044697919014,323433835991304,358680527406554,391765169440470,
    421707005530038,447612792582606,468720644344060,484437049563134,494361990186722,
    498303278723270,496279828198006,488511211993676,475398171579168,457495747981762,
    435477688451982,410099744488422,382161433293934,352469218891696,321802890194696,
    290888313769818,260374918087892,230819603755182,202678714945792,176304545966890,
    151947231174156,129762319276542,109819636172708,92115691757908,76586796845732,63122642083772,
    51578210902252,41786423668496,33568609101694,26742005085078,21127524351692,16555222277486,
    12867143004782,9920028860442,7586875850048,5756397235538,4333078863286,3235970427290,
    2397928332674,1763011721022,1285950805432,930770615430,668350998748,475877577552,
    336043165272,235291933152,163083103362,111753248004,75663258500,50533066940,32890643614,
    20959671302,12927686350,7397427098,3815330996,1714485958,532557338]]
private theorem rkmWC_w64_s4_0 : bWinChk 206 17 100000000 1024 rkmPhb_w64_s4
    222 rkmXsWin_w64_s4_in 248 rkmC_w64_s4_1 3270828561 = true := by decide +kernel
private theorem rkmWC_w64_s4_1 : bWinChk 206 17 100000000 1024 rkmPhb_w64_s4
    248 rkmC_w64_s4_1 274 rkmC_w64_s4_2 3344178004 = true := by decide +kernel
private theorem rkmWC_w64_s4_2 : bWinChk 206 17 100000000 1024 rkmPhb_w64_s4
    274 rkmC_w64_s4_2 300 rkmC_w64_s4_3 3376377571 = true := by decide +kernel
private theorem rkmWC_w64_s4_3 : bWinChk 206 18 100000000 1024 rkmPhb_w64_s4
    300 rkmC_w64_s4_3 328 rkmC_w64_s4_4 3557855835 = true := by decide +kernel
private theorem rkmWC_w64_s4_4 : bWinChk 206 18 100000000 1024 rkmPhb_w64_s4
    328 rkmC_w64_s4_4 358 rkmC_w64_s4_5 3079224486 = true := by decide +kernel
private theorem rkmWC_w64_s4_5 : bWinChk 206 18 100000000 1024 rkmPhb_w64_s4
    358 rkmC_w64_s4_5 383 rkmC_w64_s4_6 3616484095 = true := by decide +kernel
private theorem rkmWC_w64_s4_6 : bWinChk 206 18 100000000 1024 rkmPhb_w64_s4
    383 rkmC_w64_s4_6 411 rkmC_w64_s4_7 3742084829 = true := by decide +kernel
private theorem rkmWC_w64_s4_7 : bWinChk 206 18 100000000 1024 rkmPhb_w64_s4
    411 rkmC_w64_s4_7 438 rkmC_w64_s4_8 3561466093 = true := by decide +kernel
private theorem rkmWC_w64_s4_8 : bWinChk 206 18 100000000 1024 rkmPhb_w64_s4
    438 rkmC_w64_s4_8 460 rkmC_w64_s4_9 3344855141 = true := by decide +kernel
private theorem rkmWC_w64_s4_9 : bWinChk 206 19 100000000 1024 rkmPhb_w64_s4
    460 rkmC_w64_s4_9 487 rkmC_w64_s4_10 3659196529 = true := by decide +kernel
private theorem rkmWC_w64_s4_10 : bWinChk 206 19 100000000 1024 rkmPhb_w64_s4
    487 rkmC_w64_s4_10 514 rkmC_w64_s4_11 3911209876 = true := by decide +kernel
private theorem rkmWC_w64_s4_11 : bWinChk 206 19 100000000 1024 rkmPhb_w64_s4
    514 rkmC_w64_s4_11 536 rkmC_w64_s4_12 3683415088 = true := by decide +kernel
private theorem rkmWC_w64_s4_12 : bWinChk 206 19 100000000 1024 rkmPhb_w64_s4
    536 rkmC_w64_s4_12 557 rkmC_w64_s4_13 3725381110 = true := by decide +kernel
private theorem rkmWC_w64_s4_13 : bWinChk 206 19 100000000 1024 rkmPhb_w64_s4
    557 rkmC_w64_s4_13 580 rkmXsWin_w64_s4_out 3294667847 = true := by decide +kernel
private theorem rkmWinIter_w64_s4 :
    RkmWinIterSound 254 1024 rkmHbWin_w64_s4 222 rkmXsWin_w64_s4_in
      580 rkmXsWin_w64_s4_out 49167225065 :=
  rkmChS 254 49167225065 (rkmChS 235 45872557218 (rkmChS 216 42147176108 (rkmChS 197
    38463761020 (rkmChS 178 34552551144 (rkmChS 159 30893354615 (rkmChS 141 27548499474 (rkmChS
    123 23987033381 (rkmChS 105 20244948552 (rkmChS 87 16628464457 (rkmChS 69 13549239971
    (rkmChS 51 9991384136 (rkmChS 34 6615006565 (bWinChk_sound rkmHhb_w64_s4 rkmWC_w64_s4_0)
    rkmHhb_w64_s4 rkmWC_w64_s4_1 rfl rfl) rkmHhb_w64_s4 rkmWC_w64_s4_2 rfl rfl) rkmHhb_w64_s4
    rkmWC_w64_s4_3 rfl rfl) rkmHhb_w64_s4 rkmWC_w64_s4_4 rfl rfl) rkmHhb_w64_s4 rkmWC_w64_s4_5
    rfl rfl) rkmHhb_w64_s4 rkmWC_w64_s4_6 rfl rfl) rkmHhb_w64_s4 rkmWC_w64_s4_7 rfl rfl)
    rkmHhb_w64_s4 rkmWC_w64_s4_8 rfl rfl) rkmHhb_w64_s4 rkmWC_w64_s4_9 rfl rfl) rkmHhb_w64_s4
    rkmWC_w64_s4_10 rfl rfl) rkmHhb_w64_s4 rkmWC_w64_s4_11 rfl rfl) rkmHhb_w64_s4
    rkmWC_w64_s4_12 rfl rfl) rkmHhb_w64_s4 rkmWC_w64_s4_13 rfl rfl
/-- Certified `w64` seg `4` (`254` steps). -/
theorem rkmWinSegWalkSnd_w64_s4 :
    RkmWinSegWalkSound 254 ⟨1024, rkmHbWin_w64_s4, 222, rkmXsWin_w64_s4_in,
      580, rkmXsWin_w64_s4_out, 49167225065⟩ :=
  @rkmSegWalk_mk 254 1024 222 580 49167225065
    rkmHbWin_w64_s4 rkmXsWin_w64_s4_in rkmXsWin_w64_s4_out
    (rkmw_buildHbFrom_length 1024 1024 29638027559 1024 0)
    (bAllT_hd (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl (bAllT_tl
      (bAllT_tl rkmStatOk_hiw64t10))))))))))
    rkmWinIter_w64_s4
/-- Cumulative `w64` part `10` lane witness. -/
theorem laneWitness_FindAllJohnsonRampKickMuxHiW64T10 :
    @rkmWinSegWalkSnd_w64_s4 = @rkmWinSegWalkSnd_w64_s4 :=
  rfl

end
end QuantumComputation.Specs.DickeSol
