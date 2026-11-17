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
# High-`m` Coupled Walk & Trajectory Part `6` (`FindAllJohnsonRampKickMuxHi256T6`)

Certifies `(256, 96)` (`6499` coords) and `(256, 512)` `s = 2_c0` (`87723` coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Unpacks `len` LSB-first bits of `< 2 ^ 50` word `w`
  (`FindAllJohnsonRampKickMuxHi256T6`). -/
def rkmWordBitsHi256T6 : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, w => Nat.ble 1 (Nat.mod w 2) :: rkmWordBitsHi256T6 j (Nat.div w 2)
/-- Unpacks `< 2 ^ 50` words of lengths `ns` (`FindAllJohnsonRampKickMuxHi256T6`). -/
def rkmUnpackMaskHi256T6 : List ℕ → List ℕ → List Bool
  | [], _ => []
  | _, [] => []
  | n :: ns, w :: ws => rkmWordBitsHi256T6 n w ++ rkmUnpackMaskHi256T6 ns ws
/-- Mask segment `0` for `(m = 256, r = 96)`. -/
def rkmMkHiHiB_m256_r96_s0 : List Bool := rkmUnpackMaskHi256T6 [7] [127]
/-- Mask segment `1` for `(m = 256, r = 96)`. -/
def rkmMkHiHiB_m256_r96_s1 : List Bool := rkmUnpackMaskHi256T6 [48] [281474976710655]
/-- Mask segment `2` for `(m = 256, r = 96)`. -/
def rkmMkHiHiB_m256_r96_s2 : List Bool := rkmUnpackMaskHi256T6 [32] [4294967295]
/-- Prefix-kick masks for `(m = 256, r = 96)`. -/
def rkmMasksHiHiB_m256_r96 : List (List Bool) :=
  [rkmMkHiHiB_m256_r96_s0, rkmMkHiHiB_m256_r96_s1, rkmMkHiHiB_m256_r96_s2, []]
/-- Part `0` of `rkmRowHiHiB_m256_r96`. -/
def rkmRowHiHiB_m256_r96_p0 : List ℕ :=
  [0, 23, 194, 1114, 4800, 16163, 43366, 93451, 161254, 219008, 224460, 156835, 54284, 150, 44580,
   137033, 167464, 95172, 9462, 23002, 120165, 169763, 101979, 10163, 26004, 134909, 185994, 126548,
   2529, 170, 360132, 233764, 9204, 342, 18218, 136438, 296314, 328165, 243148, 25140, 13370,
   607786, 1122, 2247147, 599068, 132316, 1914267, 1800108, 947, 886456, 712652, 1135, 1817443,
   9794275, 32670566, 92479920, 238844735, 573242104, 1284747080, 2692382260, 5277670960,
   9676738593, 16592813122, 26600659767]
/-- Part `1` of `rkmRowHiHiB_m256_r96`. -/
def rkmRowHiHiB_m256_r96_p1 : List ℕ :=
  [39855192193, 55782713236, 72895605206, 88882357046, 101047590775, 107021532868, 105497189724,
   96687735804, 82288674295, 64946995900, 47464366142, 32064409433, 19984356172, 11466388923,
   6041831640, 2915476252, 1284326913, 514629245, 186790599, 61116049, 17923942, 4680318, 1079406,
   217721, 37942, 5624, 694, 68, 4, 0, 0, 0]
/-- Certified `10 ^ 12`-scaled hit row `(m = 256, r = 96)`. -/
def rkmRowHiHiB_m256_r96 : List ℕ := rkmRowHiHiB_m256_r96_p0 ++ rkmRowHiHiB_m256_r96_p1
/-- Cumulative trajectory lane witness (`FindAllJohnsonRampKickMuxHi256T6`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi256T6 : (0 : ℕ) = 0 := rfl
/-- Zigzag `< 2 ^ 60` orbital vector decoder (`FindAllJohnsonRampKickMuxHi256T6`). -/
def rkmZigHi256T6 : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: rkmZigHi256T6 ws
/-- Chunked `< 2 ^ 60` orbital vector decoder (`FindAllJohnsonRampKickMuxHi256T6`). -/
def rkmZigCatHi256T6 : List (List ℕ) → List ℤ
  | [] => []
  | c :: cs => rkmZigHi256T6 c ++ rkmZigCatHi256T6 cs
/-- Quantized generator list for `m256_r512_s2_c0`. -/
def rkmHbHiHiB_m256_r512_s2_c0 : List ℤ :=
  altBuildHbFrom 1024 512 51900571906 0 512
/-- Input orbital vector for `m256_r512_s2_c0`. -/
def rkmViHiHiB_m256_r512_s2_c0 : List ℤ := rkmZigCatHi256T6
  [
   [460704,2114258,6673634,16667750,34765736,62129804,96164546,128811896,147051690,136833942,
    90008782,11489416,77719584,145327977,160605986,110468273,10334469,98006610,163522234,151296477,
    63228957,59044630,152682364,166834774,91026870,35362834,143998766,173145958,105431148,22930118,
    139107455,176564698,112877501,16439717,136763883,178775034,117512725,12045286,134884822,
    180354858,121938522,6773745,131605125,181434827,127915287,1699157,125280081,181764801,
    136520047,15198062,114238695,180511592,148020833,35068945,96538824,175929830,161578023,
    61970442,69914077,164999825,174759393,95342908,32162423,143253366,182824839,132440191,17786154,
    105300861,178047572,166754929,77892649,46696803,150122089,186201669,139763754,32265807,
    89248846,173158825,184779115,120172014,6612571,109971939,183921432,187210308,119407615,6740105,
    109034210,186524330,199034656,143030468,38331781,79838465,173334396,213180884,187864042,
    105926690,7768601,120458394,201170286,228821412,197122135,115243225,4223403,109222150,
    199301917,246768528,242642084,189192806,98196214,12439521,122566063,213631247,271822965,
    289763249,266643160,207356313,121037079,19107857,86781948,186322318,271446531,336828920,
    380040596,401196688,402215182,386083090,356260936,316030778,267746416,212184918,147992446,
    70879546,27714806,162549524,357314276,648794780,1093249246,1775727060,2823318974,4423962176,
    6852995944,10510036024,15969299432,24047498228,35894511158,53112905462,77913165024,
    113312440710,163385565628,233577479754,331085869284,465321837466,648454671518,896043755146,
    1227755948956,1668160277580,2247583672074,3003001795544,3978927568584,5228247235460,
    6812940529210,8804608771568,11284723634330,14344500979200,18084300236928,22612451963716,
    28043426089156,34495272018632,42086289767794,50930928832876,61134957982988],
   [72790002993102,85967607754380,100713033501020,117039066743392,134920154113314,154287216652898,
    175023512180314,196961908066244,219883895242608,243520616506090,267556099102720,
    291632776203120,315359259383658,338320191839634,360087878595596,380235265123990,
    398349729228546,414047071681320,426985046264768,436875764651610,443496348182368,
    446697276042974,446407993290242,442639485352388,435483688431008,425109776482358,
    411757533317798,395728171291148,377373085762584,357081128913932,335265042203720,
    312347701584866,288748804509052,264872566558714,241096904564846,217764470372386,
    195175774121368,173584507356040,153195053217138,134162060939136,116591870677086,
    100545506156794,86042908552048,73068065171498,61574689106718,51492127732692,42731214727386,
    35189827498466,28757964955406,23322215163004,18769534886526,14990310496614,11880710110902,
    9344369028866,7293474074018,5649327663458,4342480067834,3312519539544,2507606102982,
    1883827192570,1404443303590,1039080553300,762915506356,555886551980,401956065424,288438877582,
    205405371654,145161845018,101806530244,70856707826,48940468514,33545688396,22818461254,
    15403404682,10318760054,6859909286,4525731260,2963041105,1925144107,1241258387,794198749,
    504261811,317710103,198626744,123212472,75832376,46302490,28045566,16849574,10039860,5932334,
    3475554,2018662,1162208,663160,374982,210084,116600,64087,34872,18782,10007,5265,2729,1389,687,
    327,145,57,17,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
/-- Output orbital vector for `m256_r512_s2_c0`. -/
def rkmVoHiHiB_m256_r512_s2_c0 : List ℤ := rkmZigCatHi256T6
  [
   [23420453,42982869,41830613,15259867,9557302,8479283,77144295,142116167,124270677,5572665,
    126437242,148029406,32343478,102154109,107439161,29237112,163335452,163337824,51292742,
    14579593,6729614,81131900,11176667,66832025,258770521,19795707,217081969,175561206,436787907,
    212414184,502463097,469488788,389194425,274976212,274975789,52941833,197240340,330925467,
    311092714,370467611,159216304,156791440,213125659,307406964,383140265,28366124,53555732,
    422961379,153462238,311126359,61551649,301928476,354020961,46088410,134327919,318120579,
    373180366,67370823,22483899,301534212,248089451,131442550,168742804,304428869,252040620,
    121899892,158454189,256002350,212194521,257848237,326163734,12776907,93905500,341414600,
    245441129,41233197,241592340,174591573,172440404,313238178,175203697,137302198,178267600,
    257085999,125837686,154378358,244766357,153133122,170087480,212015779,161249018,140938888,
    265923865,75880532,67387442,312136665,85419306,182392778,230429199,1961104,38914822,311149229,
    108330680,377316372,66068665,4066380,134896690,238697027,29472217,290708574,134816653,
    162188981,208312834,49330137,136008223,167214736,141209861,328622069,166623878,176253118,
    83314449,215029830,175300362,245957277,22799995,157607766,204381653,81105285,215514080,
    137311757,214294461,187940628,52564860,121091043,224543876,122024044,277530945,7137961,
    194538952,153102039,68371653,223912698,78391883,182217361,182730666,18837160,287349675,
    67300058,216683062,137881615,18112261,253147842,43423695,108498523,232820632,15967051,
    420570357,82966649,192104056,55915473,27020946,227611524,140383573,246480955,291793120,
    335541516,129166815,94900767,35624400,273732033,206838847],
   [247142536,84104360,255970695,86971982,316838670,71363673,137435511,145582130,54130463,
    228496699,202296166,300616090,210741177,232796207,173411714,57365218,136644199,196044716,
    253735070,166060043,48670091,429060904,248220080,115510185,114627978,216069522,185555321,
    160350625,276938202,142669420,207424995,75660398,328066032,55905785,197161607,199220338,
    163278988,253761353,104325167,240100000,17925919,212911321,228020544,391678216,89864207,
    224887121,106132960,5100363,315748339,1035622,362870746,1311626,315306719,36846512,218828088,
    130733057,129171649,271640546,135821984,313587281,109850387,348695782,159455360,164263967,
    92711686,270766554,120772321,229072787,294605022,478428098,63415010,11461907,324970240,
    168939458,323881219,219227323,205876822,63601158,260211495,18212818,354133722,10635248,
    364446313,71362815,222336780,64064655,214601111,215034268,403982750,38632217,238975703,
    165434428,314210180,84733933,182141963,224169028,262650640,210261637,298475023,118225250,
    147664968,304037269,348627049,91606778,136807760,281800177,297147991,150555512,197911802,
    219061327,239515051,213451206,271399772,185074693,297720361,108795164,217751128,173010719,
    269982461,154191382,296582874,145685727,385181947,13226973,261334950,31818677,264148483,
    59298032,335663664,12284507,436057507,237882829,183122926,91046724,251554269,114732565,
    316578802,254672508,260495529,411221729,35632283,125520102,220820601,402828927,2040213,
    377745592,148658320,251896401,137763273,240369700,157224142,305328099,381257835,75563210,
    344706768,55065328,210785545,73295236,478412622,338758380,132283319,188124921,229384366,
    408387174,39979340,283463589,40467453,372390408,282031872,178293419,278294871],
   [155033630,470109910,215142510,166388093,44358191,406724930,469456178,17840179,411914013,
    231141163,136481498,39345450,446436961,622019309,197286793,280626708,219967048,169942175,
    199762669,293774050,705792598,517716056,25636692,76918831,337339326,661473252,398682032,
    153048057,303458169,101707146,479198522,288568752,254107585,463465357,79468043,399358296,
    361278186,135865835,438141167,121543617,459632370,551321486,204902909,1553218899,3213208415,
    5439708849,8574254441,11458372815,9312559141,8602292376,62196883680,185818643366,436192303648,
    902528925448,1717583381674,3068497999794,5206511401008,8454264590874,13208459445062,
    19934797282914,29152286973982,41405296558260,57223536998990,77071835377740,101292899943864,
    130047579392850,163258570083584,200564811220182,241294211382028,284461280461168,
    328793688732948,372788310525590,414793702109054,453112777569664,486116935812262,
    512361173654364,530688988153194,540316413358430,540886538642436,532489175595912,
    515644448788068,491253227578874,460520782535478,424862389019768,385800671071044,
    344864368065002,303497108674176,262982916204726,224392793024430,188554127284124,
    156042158577732,127190648715386,102117468528038,80760134827878,62916367630228,48285326017292,
    36506107476132,27191152554848,19953222043188,14425503338180,10275103148716,7210678903902,
    4985258345306,3395417995244,2277968928712,1505171570182,979311470190,627253950796,395388724536,
    245197615334,149540267022,89656068800,52820998240,30567934054,17369691080,9687915468,
    5302039266,2846509648,1498810936,773893364,391816616,194515638,94697162,45218070,21183828,
    9740536,4398020,1951080,850952,365104,154186,64106,26230,10550,4158,1596,588,198,56,12,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
end
public section
private abbrev fN := @HighDForce.withForcedNat
private abbrev fL := @HighDForce.withForcedList
private theorem ndiv (a b : ℕ) : Nat.div a b = a / b := rfl
private theorem bOfNatF_eq (n : ℕ) : primOfNatForced n = Int.ofNat n := by
  unfold primOfNatForced; rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
private theorem bNegSuccF_eq (n : ℕ) : primNegSuccForced n = Int.negSucc n := by
  unfold primNegSuccForced; rw [show Nat.add 1 n = n + 1 from Nat.one_add n]
private theorem bSub_eq (a b : ℕ) : rkmForcedSubNatNat a b = (a : ℤ) - (b : ℤ) := by
  unfold rkmForcedSubNatNat; simp only [Nat.sub_eq]; cases h : b - a with
  | zero => dsimp only; rw [bOfNatF_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private theorem bZero_eq (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bMul0 (z : ℕ) :
    muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZero_eq]; rfl
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x with
  | 0 => 0 :: xs
  | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [show Nat.add 1 x = x + 1 from Nat.one_add x]; cases xs <;> rfl
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | b :: bs => Int.ofNat b :: uOfNatHb bs
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | Int.ofNat b :: bs => match uToNatHb bs with | some r => some (uConsNat b r) | none => none
  | Int.negSucc _ :: _ => none
private theorem uToNatHb_sound : ∀ (hb : List ℤ) (bns : List ℕ),
    uToNatHb hb = some bns → uOfNatHb bns = hb
  | [], _, h => by injection h with h'; subst h'; rfl
  | Int.ofNat b :: bs, _, h => by
    dsimp only [uToNatHb] at h; revert h; cases hbs : uToNatHb bs with
    | none => intro h; cases h
    | some r =>
      intro h; injection h with h'; subst h'
      rw [uConsNat_eq]; exact congrArg (Int.ofNat b :: ·) (uToNatHb_sound bs r hbs)
  | Int.negSucc _ :: _, _, h => by cases h
private def bEnc1 (z : ℕ) (x : ℤ) : Option ℕ := match x with
  | Int.ofNat m => some (Nat.add z m)
  | Int.negSucc k =>
    match Nat.sub z (Nat.add k 1) with | 0 => none | u + 1 => some (Nat.add u 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs => match bEnc1 z x with
    | none => none
    | some u => match bEnc z xs with | none => none | some ws => some (uConsNat u ws)
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => rkmForcedSubNatNat u z :: bDec z us
private theorem bDec_nil (z : ℕ) : bDec z [] = [] := rfl
private theorem bDec_cons (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by
  dsimp only [bDec]; rw [bSub_eq]
private theorem bEnc1_sound (z : ℕ) (x : ℤ) (u : ℕ) (h : bEnc1 z x = some u) :
    ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat m =>
    injection h with h'; subst h'; simp only [Nat.add_eq, Int.ofNat_eq_natCast]
    push_cast; ring
  | negSucc k =>
    dsimp only [bEnc1] at h; revert h; simp only [Nat.sub_eq, Nat.add_eq]
    cases hs : z - (k + 1) with
    | zero => intro h; cases h
    | succ u0 => intro h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem bEnc_sound (z : ℕ) : ∀ (xs : List ℤ) (ws : List ℕ),
    bEnc z xs = some ws → bDec z ws = xs
  | [], _, h => by injection h with h'; subst h'; rfl
  | x :: xs, _, h => by
    dsimp only [bEnc] at h; revert h; cases hx : bEnc1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bEnc z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uConsNat_eq, bDec_cons, bEnc1_sound z x u hx, bEnc_sound z xs ws hxs]
private def zTdiv (x : ℤ) (d : ℕ) : ℤ := match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
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
    dsimp only; have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTdiv]; rw [bNeg_eq]
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
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq]; simp only [Int.ofNat_eq_natCast]
    push_cast; ring
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
    dsimp only [rkmForcedIntAdd]; rw [bOfNatF_eq, Nat.add_eq]
    simp only [Int.ofNat_eq_natCast]; omega
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]
    rw [bSub_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]
    rw [bSub_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bNegSuccF_eq, Nat.add_eq, Nat.add_eq]
    simp only [Int.negSucc_eq]; omega
private theorem bAddCons_eq (a b : ℤ) (xs : List ℤ) :
    rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bForcedAdd_eq]; cases a + b <;> cases xs <;> rfl
private def bStepVal (v P Q d : ℕ) : ℕ := match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) =
      ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSubNatTdiv_eq]; unfold bStepVal at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv; cases h : Q - P with
  | zero => intro _; dsimp only; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k => intro hv; dsimp only at hv ⊢; rw [bNeg_eq]; omega
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
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAllPos xs)
private theorem bAllPos_cons {x : ℕ} {xs : List ℕ} (h : bAllPos (x :: xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private theorem bAllPos_uCons {x : ℕ} {xs : List ℕ} (h : bAllPos (uConsNat x xs) = true) :
    0 < x ∧ bAllPos xs = true := by rw [uConsNat_eq] at h; exact bAllPos_cons h
private def bHeadOr (z : ℕ) : List ℕ → ℕ | [] => z | x :: _ => x
private def bTailN : List ℕ → List ℕ | [] => [] | _ :: xs => xs
private theorem bHeadOr_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHeadOr z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq]
  | c :: cs => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | x :: xs => by unfold bTailN; rw [bDec_cons]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs => match bns with
    | [] => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSlide z d rem 0 z [] (bTailN vs) (bTailN cs))
    | b :: bR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal z d b0 c0 b v (bHeadOr z cT)) (bSlide z d rem b c bR vT cT)
      | v :: vT, [] => uConsNat (bCellVal z d b0 c0 b v z) (bSlide z d rem b z bR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal z d b0 c0 b z (bHeadOr z cT)) (bSlide z d rem b c bR [] cT)
      | [], [] => uConsNat (bCellVal z d b0 c0 b z z) (bSlide z d rem b z bR [] [])
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
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi
      rw [bHeadOr_eq z vs] at hc; exact hc
    | cons b bR => cases vs with
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
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq]
    rw [← bStg_sound z dg mL cL bns vns cns mid hs]; exact hk mid h
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
    | none => none
    | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL bns vNext
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
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  let z := 10000000000000000
  match uToNatHb hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some bns => match bEnc z v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vns => match bIter z k mL cL bns vns with
      | none => muxUltraIterFullT16Rkm k mL cL hb v
      | some out => bDec z out
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; dsimp only; cases hh : uToNatHb hb with
  | none => rfl
  | some bns => dsimp only; cases hv : bEnc 10000000000000000 v with
    | none => rfl
    | some vns => dsimp only; cases hi : bIter 10000000000000000 k mL cL bns vns with
      | none => rfl
      | some out =>
        dsimp only; rw [bIter_sound 10000000000000000 k mL cL bns vns out hi,
          ← uToNatHb_sound hb bns hh, bEnc_sound 10000000000000000 v vns hv]
private def bSlideChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    fN (altIntLen inF) fun len0 => muxIntListEq (fIter steps maxLen len0 hbF inF) outF
private theorem bSlideChk_sound {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : bSlideChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold bSlideChk at h; dsimp only [fL, fN] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, fIter_eq] at h
  have h2 : muxUltraIterFullT16HiChk steps 0 maxLen hb vecIn vecOut = true := by
    unfold muxUltraIterFullT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq]; exact h
  exact muxUltraIterFullT16HiChk_sound h2
private def uNatApp : List ℕ → List ℤ → List ℤ
  | [], acc => acc
  | n :: ns, acc => Int.ofNat n :: uNatApp ns acc
private def uNatCat : List (List ℕ) → List ℤ
  | [] => []
  | ns :: nss => uNatApp ns (uNatCat nss)
private def pzeros : ℕ → List ℤ | 0 => [] | k + 1 => Int.ofNat 0 :: pzeros k
private def pzigApp : List ℕ → List ℤ → List ℤ
  | [], acc => acc
  | w :: ws, acc =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: pzigApp ws acc
private def pzigCat (z : ℕ) : List (List ℕ) → List ℤ
  | [] => pzeros z
  | ws :: wss => pzigApp ws (pzigCat z wss)
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private theorem rkmT2 {b0 b1 : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b0 :: b1 :: bs) = true) : rkmAllTrueF bs = true := rkmTl (rkmTl h)
private theorem rkmT4 {b0 b1 b2 b3 : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b0 :: b1 :: b2 :: b3 :: bs) = true) : rkmAllTrueF bs = true :=
  rkmT2 (rkmT2 h)
private theorem pdim_96_l1 : Nat.add (highdNatMin (Nat.mul 1 256) 96) 1 = 97 := rfl
private def phb_96_0 : List ℤ :=
  altBuildHbFrom 256 96 521436741935 0 96
private def pvi_96_0 : List ℤ := [rkmP 1000000000000000]
private def pvo_96_0 : List ℤ := pzigCat 24
  [
   [2175781566,12656137498,51647449928,170726449678,484848136206,1221658883460,2787207128462,
    5839176380234,11348660085246,20622317268164,35253042593092,56973461416688,87404745935508,
    127721444776466,178284567713860,238320152398756,305728938068634,377098303297672,
    447950747543932,513211860874606,567828368748108,607428199793396,628900820939438,
    630791337169474,613441707341760,578865796088906,530397775904830,472192893360276,
    408677955551622,344044644687180,281856362519524,224806862231836,174635425800100,
    132176142931358,97502173746622,70120542489526,49177089452458,33641253659318,22452648859978,
    14622882051324,9294851067250,5767142244916,3493360196758,2066034585794,1193114078452,
    672832560362,370540069926,199288008610,104677147854,53696570464,26900275808,13160315696,
    6287114924,2932785412,1335713350,593885132,257745780,109173098,45123276,18195458,7156640,
    2744952,1026414,374056,132802,45914,15446,5048,1598,484,138,36,6]]
private theorem dk_r96_s0_0 :
    bSlideChk 31 97 phb_96_0
      pvi_96_0 pvo_96_0 = true := by
  decide +kernel
private def phb_96_1 : List ℤ :=
  altBuildHbFrom 256 96 515327129032 0 96
private def pvi_96_1 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r96_s0 pvo_96_0
private def pvo_96_1 : List ℤ := pzigCat 0
  [
   [8309624795,34299385127,97083742463,216647481609,401914553711,634840300659,860338270251,
    993070553529,946322867975,675619563591,216841914341,305497155972,713780650604,848504165256,
    644708512132,174404102342,371807523811,761602590015,823215819801,524776741235,8296887518,
    547241972736,860228381328,812502768958,421640518374,154149449155,685525929109,965918599089,
    889445972133,483675266917,110062234168,694580576778,1086528161768,1171676367412,929717168066,
    426328972290,218226578495,869200735477,1412236783281,1774272484559,1928096916991,
    1883263618909,1668517069423,1310745080563,813611629915,136630108089,826470584480,
    2271990694364,4514325662614,8016917522040,13421796646242,21569366653658,33496218778932,
    50396361903726,73531887307528,104084245676174,142947816587702,190482741048546,
    246261604331624,308860111774586,375749831043582,443346189550918,507244410204964,
    562641329598278,604898424678370,630161308801994,635925307923670,621435023852040,
    587831623762278,538010595997678,476213150623138,407430497281256,336736921560342,
    268675587156684,206799570498340,153427534408754,109621944982790,75352028926504,
    49774411660700,31555942335194,19173423984208,11147011732828,6189500634084,3275446480538,
    1647925975192,785981753610,354180225102,150180205214,59625983320,22031018450,7516715762,
    2344098184,658864786,163553586,34720522,5943318,710442]]
private def phbv_r96_s1 : List ℤ := uNatCat
  [
   [161572930142948,226861026343863,275838202658074,316187525939455,350907126324358,
    381545366596623,409028228179069,433962969413622,456774060543601,477772451723735,
    497194279968450,515224053297589,532009312234721,547670316108820,562306677101045,
    576002043130672,588827489482959,600844030212418,612104513946107,622655079409055,
    632536289783591,641784028642252,650430216075761,658503387291692,666029164661949,
    673030646249144,679528728159871,685542373950427,691088841279312,696183873744111,
    700841864140911,705075994091014,708898353985485,712320046426744,715351275742789,
    718001425673263,720279126947746,722192316173011,723748287200895,724953735949046,
    725814799483509,726337090037296,726525724526916,726385350034694,725920165644982,
    725133940954081,724030031514509,722611391422213,720880583208852,718839785158876,
    716490796131759,713835037932097,710873555233592,707607013025949,704035691515632,
    700159478371041,695977858158898,691489898770045,686694234578017,681589046010636,
    676172035141358,670440396820207,664390784760430,658019271871906,651321303980144,
    644291645882875,636924318465103,629212525305172,621148566841852,612723739712899,
    603928218287845,594750914659739,585179312373355,575199267868971,564794771894655,
    553947660818743,542637264613538,530839973919497,518528702490538,505672212627377,
    492234258611579,478172484547144,463436984922393,447968392733236,431695290858386,
    414530628864842,396366634229624,377067364046295,356457403698089,334303953142648,
    310286847650489,283944780467273,254569515388606,220969004038625,180820351691126,
    128133165784777]]
private def pvm_r96_s1_1 : List ℤ := pzigCat 4
  [
   [1569139010829,100843403879,1133062087030,589086040314,699029776943,1023700271785,
    109231685139,910403382862,960857525040,61676901516,907162198867,1122757606647,457835361865,
    567415905066,1269203055376,1252265104746,557661021336,472580849695,1435540129767,
    2048884008175,2209106577799,1949155121979,1352798502049,473666061565,719574749140,
    2372471249596,4758657051484,8287644590072,13509864039666,21115828908472,31921913186430,
    46833743878624,66779705834476,92611290210912,124973536246014,164156767496222,209948821610078,
    261513159708286,317320621261738,375159564719350,432240088853764,485393766228590,
    531353144285666,567078636644748,590088178124356,598740387230852,592426665687906,
    571641243098726,537918085219378,493645708345610,441790631084036,385573443196680,
    328145895093052,272312750878224,220330176832112,173796349350234,133633455394856,
    100146583010424,73136290113216,52038600132946,36068188172680,24346068976286,16000292842946,
    10235254827812,6370971396798,3857448908778,2271010409980,1299522519152,722434804982,
    389986568086,204316058862,103824687990,51140236838,24399445402,11267111766,5031369772,
    2170636110,903766362,362729796,140151540,52054686,18554364,6334828,2067212,643130,190190,
    53274,14064,3476,792,160,26,2]]
private def phb_96_2 : List ℤ :=
  altBuildHbFrom 256 96 361972333333 0 96
private def pvi_96_2 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r96_s1 pvo_96_1
private def pvo_96_2 : List ℤ := pzigCat 0
  [
   [1852288532,8691960484,28141346162,72404540042,156519400602,292382036946,478976151260,
    692254354934,880938433194,974662553502,906702237030,645705152668,222995301948,260713189101,
    659416674929,833268216471,708512681843,318522011965,196914823258,639586176416,831214613616,
    688982371258,263923513144,276591404187,716028583607,876858226489,691988156221,229945947405,
    334782096596,791464392868,972819300654,813290227172,366098267540,222701479837,768749188089,
    1109890863177,1151639390745,885479274227,378976912407,251981381184,887834454534,
    1389819802542,1839203925558,1635808491982,2632650623114,182904886542,2990029702390,
    1081281434012,2026616967631,1925231174429,400799051596,3490453088656,7377164124538,
    12908552811824,21168465502554,33366763927058,50841621948024,74996491308404,107143456249388,
    148266093536062,198729691067086,257984306142064,324324127335882,394775758245888,
    465180426404992,530506896224850,585385393903784,624797485810464,644807339569316,
    643192186105220,619835903272966,576792080994088,517992927562506,448659605603490,
    374535780656634,301100587051440,232911067914624,173181387953566,123641587492654,
    84652373779882,55502569902836,34792958328492,20815167404584,11859481033938,6419342230532,
    3291673436148,1593604704434,725484436376,309046248358,122437513004,44763643336,14949323110,
    4497042906,1194037024,270968292,49555332,6325538]]
private def phb_96_3 : List ℤ :=
  altBuildHbFrom 256 96 396986500000 0 96
private def pvi_96_3 : List ℤ :=
  rkmApplyMaskBits rkmMkHiHiB_m256_r96_s2 pvo_96_2
private def pvo_96_3 : List ℤ := pzigCat 0
  [
   [546311687,2796698047,9908088799,28000740763,66805650423,138595557979,254283906535,
    416502890441,611405439573,803137070337,935972638779,947552008433,792055771183,465987314583,
    24634585493,422291857234,740367806240,818455818898,617007764532,194561741840,303341965827,
    693303529815,824054258619,638690550121,201645788519,322531242208,734607278512,862547878230,
    711481320766,100617276788,26166518631,1200226498681,966990766735,191896733697,37094999748,
    269966275549,738758987199,1088701016891,1145720112635,986208685467,317128376203,231270964599,
    1559219049824,67040000866,2998102780132,1547995488024,727513216850,2767145590614,
    2683367021356,61612561990,1883041399731,1688379644983,67414482694,2696256504762,
    6259165796274,11431638710464,19233300316066,30909208973188,47884953940094,71686741520660,
    103776345542264,145295165200992,196740834557198,257626191592818,326194177957816,
    399275308569736,472367290149978,539983726825854,596262889213214,635759678097094,
    654282918020882,649606622656882,621893036055466,573720055310006,509694013860486,
    435726368411164,358130759165108,282732076358568,214162455735410,155458444074160,
    107990304638034,71675018264996,45370886646102,27334275629692,15635355067048,8467339826412,
    4326813526608,2077895215074,933219303324,389584805068,150005925250,52731923214,16688874168,
    4659610254,1111401092,213529060,28620624]]
private def phbv_r512_s2_c0 : List ℤ := uNatCat
  [
   [75160056508810,106136656858142,129799584559857,149659364595528,167077928987539,
    182754818351966,197106209662422,210403663876630,222836083107279,234541205380215,
    245623161938375,256162968753997,266225145901054,275862080714619,285117009326714,
    294026116615063,302620053792274,310925059736244,318963805695950,326756042517157,
    334319104079234,341668304185087,348817253252547,355778113781922,362561808484415,
    369178191379880,375636189618858,381943921933734,388108798265158,394137604099824,
    400036572296032,405811444596278,411467524583037,417009723490888,422442600020104,
    427770395085907,432997062270213,438126294609049,443161548241359,448106063357962,
    452962882818664,457734868747638,462424717369543,467034972309476,471568036547131,
    476026183188253,480411565193593,484726224186318,488972098442583,493151030156155,
    497264772056287,501314993447981,505303285735229,509231167480410,513100089046712,
    516911436864894,520666537360992,524366660577380,528013023516049,531606793229742,
    535149089683881,538640988409772,542083522967432,545477687234529,548824437536237,
    552124694629350,555379345552709,558589245354795,561755218708352,564878061420965,
    567958541849686,570997402227082,573995359905405,576953108525002,579871319112547,
    582750641114178,585591703368234,588395115021839,591161466395272,593891329797726,
    596585260297753,599243796451453,601867460991218,604456761477607,607012190916756,
    609534228345520,612023339386407,614479976774170,616904580855841,619297580065805,
    621659391377443,623990420732737,626291063451143,628561704618944,630802719460221,
    633014473690485,635197323853959,637351617645429,639477694217511,641575884474158,
    643646511351121,645689890084103,647706328465239,649696127088526,651659579584784,
    653596972846681,655508587244346,657394696832034,659255569546304,661091467396124,
    662902646645316,664689357987697,666451846715293,668190352879934,669905111448570,
    671596352452586,673264301131413,674909178070678,676531199335175,678130576596860,
    679707517258122,681262224570531,682794897749256,684305732083367,685794919042172,
    687262646377789,688709098224094,690134455192213],
   [691538894462699,692922589874529,694285712011069,695628428283112,696950903009128,
    698253297492821,699535770098124,700798476321714,702041568863158,703265197692781,
    704469510117340,705654650843602,706820762039892,707967983395699,709096452179411,
    710206303294251,711297669332473,712370680627902,713425465306860,714462149337540,
    715480856577904,716481708822126,717464825845665,718430325448993,719378323500039,
    720308933975384,721222269000269,722118438887428,722997552174817,723859715662260,
    724705034447043,725533611958514,726345549991702,727140948739992,727919906826893,
    728682521336931,729428887845677,730159100448965,730873251791301,731571433093513,
    732253734179635,732920243503090,733571048172150,734206233974732,734825885402527,
    735430085674500,736018916759755,736592459399821,737150793130340,737693996302195,
    738222146102096,738735318572624,739233588631770,739717030091964,740185715678621,
    740639717048215,741079104805892,741503948522639,741914316752017,742310277046471,
    742691895973236,743059239129836,743412371159201,743751355764404,744076255723031,
    744387132901194,744684048267194,744967061904848,745236233026481,745491619985600,
    745733280289253,745961270610085,746175646798089,746376463892074,746563776130845,
    746737636964110,746898099063111,747045214331001,747179033912952,747299608206024,
    747406986868782,747501218830672,747582352301168,747650434778686,747705513059278,
    747747633245100,747776840752680,747793180320956,747796696019131,747787431254310,
    747765428778950,747730730698114,747683378476538,747623412945512,747550874309580,
    747465802153061,747368235446400,747258212552342,747135771231944,747000948650416,
    746853781382806,746694305419519,746522556171690,746338568476391,746142376601695,
    745934014251590,745713514570742,745480910149122,745236233026481,744979514696694,
    744710786111962,744430077686876,744137419302348,743832840309418,743516369532913,
    743188035274994,742847865318565,742495886930558,742132126865097,741756611366533,
    741369366172363,740970416516020,740559787129551,740137502246170,739703585602700,
    739258060441890,738800949514622,738332275081999],
   [737852058917321,737360322307949,736857086057045,736342370485217,735816195432034,
    735278580257441,734729543843058,734169104593368,733597280436795,733014088826672,
    732419546742094,731813670688667,731196476699143,730567980333945,729928196681579,
    729277140358939,728614825511500,727941265813399,727256474467402,726560464204764,
    725853247284975,725134835495385,724405240150729,723664472092529,722912541688379,
    722149458831121,721375232937900,720589872949101,719793387327172,718985784055319,
    718167070636086,717337254089815,716496340952977,715644337276377,714781248623244,
    713907080067179,713021836189982,712125521079349,711218138326430,710299691023255,
    709370181760029,708429612622280,707477985187869,706515300523859,705541559183240,
    704556761201499,703560906093046,702553992847490,701536019925747,700506985256003,
    699466886229508,698415719696207,697353481960205,696280168775056,695195775338884,
    694100296289320,692993725698258,691876057066431,690747283317785,689607396793673,
    688456389246838,687294251835200,686120975115432,684936549036325,683740962931935,
    682534205514503,681316264867152,680087128436346,678846783024109,677595214779999,
    676332409192826,675058351082115,673773024589301,672476413168646,671168499577884,
    669849265868569,668518693376132,667176762709631,665823453741186,664458745595097,
    663082616636626,661695044460438,660296005878691,658885476908767,657463432760628,
    656029847823790,654584695653897,653127948958896,651659579584784,650179558500926,
    648687855784925,647184440607032,645669281214077,644142344912913,642603598053350,
    641053006010567,639490533166981,637916142893555,636329797530535,634731458367584,
    633121085623295,631498638424069,629864074782336,628217351574077,626558424515653,
    624887248139887,623203775771395,621507959501123,619799750160070,618079097292162,
    616345949126252,614600252547207,612841953066048,611070994789114,609287320386207,
    607490871057675,605681586500405,603859404872669,602024262757786,600176095126555,
    598314835298397,596440414901176,594552763829621,592651810202310,590737480317148,
    588809698605280,586868387583368,584913467804172],
   [582944857805355,580962474056438,578966230903826,576956040513820,574931812813528,
    572893455429577,570840873624537,568773970230939,566692645582795,564596797444490,
    562486320936939,560361108460864,558221049617069,556066031123573,553895936729429,
    551710647125099,549510039849190,547293989191391,545062366091406,542815038033704,
    540551868937847,538272719044195,535977444794731,533665898708771,531337929253266,
    528993380707432,526632093021395,524253901668517,521858637491081,519446126538945,
    517016189900785,514568643527514,512103298047418,509619958572541,507118424495817,
    504598489278386,502059940226537,499502558257630,496926117654349,494330385806557,
    491715122939988,489080081830955,486425007506175,483749636926766,481053698655385,
    478336912505391,475598989170852,472839629836087,470058525763368,467255357857254,
    464429796203936,461581499583827,458710114955457,455815276908615,452896607084449,
    449953713560071,446986190194977,443993615936351,440975554080052,437931551483797,
    434861137728689,431763824224920,428639103257019,425486446963612,422305306246087,
    419095109600072,415855261862908,412585142869662,409284106009380,405951476672380,
    402586550578394,399188591974186,395756831687997,392290465026668,388788649499637,
    385250502352071,381675097887218,378061464555568,374408581785510,370715376526913,
    366980719475190,363203420939027,359382226309828,355515811084939,351602775389781,
    347641637935846,343630829341912,339568684734530,335453435530429,331283200287551,
    327055974492418,322769619128728,318421847844621,314010212502851,309532086857691,
    304984648053017,300364855575326,295669427220390,290894811538860,286037156109196,
    281092270838815,276055585306926,270922098922520,265686322360956,260342208338434,
    254883069251718,249301478502807,243589151376094,237736800038533,231733955442565,
    225568746402682,219227622544440,212695002648280,205952822260185,198979942885465,
    191751367194392,184237176204065,176401057658266,168198215242924,159572306956948,
    150450797276027,140737585666583,130300662509549,118949951418915,106393691277859,
    92140691890123,75233132763519,53198060886291]]
private def pvm_r512_s2_c0_1 : List ℤ := pzigCat 219
  [
   [21898,121040,470390,1412878,3989842,7414172,23208398,12153040,108686480,31770689,264176020,
    5884940,179606386,143783934,79846042,71843227,111268258,71030876,108870127,86430791,73169872,
    113391664,67680726,4115569,178209709,83737618,61474451,276518086,3997756,89519304,12029633,
    267174310,179163884,8038631,79456398,127494136,7237866,49923587,44990405,49870186,49538209,
    24245295,110694897,65522976,63734991,338844028,127025146,37735048,79522897,248071,214536417,
    50165944,61810691,212304299,279885473,107583818,118845751,99679277,27213154,143373213,
    146214350,113791879,98937366,132464742,25490412,110499971,60498215,290185685,88080126,
    93728326,89598603,10711073,99692717,75789203,13980324,74065919,44385967,190604344,121243623,
    314945615,57377965,44952394,63982669,78732643,77778872,29381271,152181413,67044727,116057147,
    88259434,77407132,143804782,152893517,1591773,14478461,254882996,136019626,230962910,
    42350417,172722269,229731976,266052402,65502874,103000257,283722236,39843370,280967516,
    98476102,5132193,307278290,225563635,37217861,134153145,80606152,63043682,34570813,338551930,
    408348240,9252441,189708407,64320395,48420745,203129867,220128215,124404209,6046151,4602041,
    87237361],
   [99881923,42726261,37546044,155522092,283203238,352073576,358965806,359711276,379712616,
    388402932,348998898,261187920,157070680,73589824,33686094,45405110,111139720,237741748,
    443883924,765694782,1263165110,2029447186,3204663626,4995930750,7705775978,11771642976,
    17819764876,26737550120,39769709976,58644378518,85736300126,124274902544,178605775378,
    254514460468,359621137122,503853545600,700003295584,964367391512,1317472005432,1784868919402,
    2397986627514,3195008056000,4221735495368,5532390944794,7190287217542,9268292859322,
    11849003511912,15024525217368,18895772688222,23571189193768,29164805872470,35793578183524,
    43573966480568,52617766173222,63027239675806,74889655568526,88271397479958,103211862556644,
    119717422606618,137755765200896,157250962286558,178079625728578,200068498960904,
    222993799098018,246582563585118,270516170920990,294436099548858,317951868149868,
    340650971536906,362110497682870,381909992405156,399645038166106,414940940835274,
    427465879946080,436942878451614,443159988861492,445978172474186,445336462716274,
    441254145128122,433829845836578,423237586504856,409720025284358,393579249195916,
    375165604000028,354865135473906,333086266270990,310246343335980,286758663329642,
    263020521605314,239402740218208,216241020148340,193829341189516,172415508725434,
    152198828198048,133329782586156,115911501144078,100002742514556,85622074018078,
    72752910067748,61349078517086,51340596355596,42639402088672,35144742912176,28748250917834,
    23337990915248,18802945930392,15034168853400,11931025392258,9395176630984,7345073167120,
    5695795033408,4386586605942,3351195577196,2540282699148,1913451805700,1428435988910,
    1058057415074,779667482274,569636660424,411448801640,295782847542,212602718530,150959203594,
    104739675024,72146068754,50747224762,36379279534,25554129910],
   [16779093592,9854102542,4842769370,1636430944,74433647,721562433,753014307,532249931,
    284359243,104756029,6165445,33372260,40508346,34315918,24963480,16644498,10519226,6451448,
    3891532,2309248,1337002,749654,405996,212028,105854,49360,20500,6772,998,913,1185,925,593,
    335,171,77,25,5]]
private def pvm_r512_s2_c0_2 : List ℤ := pzigCat 207
  [
   [35896,317399,1884076,7831815,25511524,61437921,115143976,145595181,126307072,19657235,
    5955231,18612382,136094204,34328134,34163594,198462572,195856974,48746262,24917517,192206080,
    12520517,180030042,204690661,6806074,64973423,119896700,89505578,57802692,3535243,160638163,
    65525769,174354382,69356540,1192981,33272669,205265788,70355738,187822288,28720467,255803656,
    66771202,72286962,9300026,84265344,142096975,111059724,35973670,58728827,202830265,22304774,
    8626171,43106859,431050026,25156256,30720820,49687393,25583432,32562880,21473687,265532437,
    10753849,132638179,197932157,11087514,129608617,75539625,21312538,113485293,122886297,
    131054242,103665164,111643112,61614184,218215387,120712903,58553970,47399495,121346585,
    24993824,166308150,236528031,134866007,58434597,152138294,71156959,58892128,121284409,
    51205853,137653911,105970299,42637415,107132665,170517704,48699971,94095639,231185267,
    43224726,137924969,53494062,352036706,312300161,47519839,110448627,216601738,284545760,
    30885041,10927902,74611772,142554992,120468784,25090179,115606076,199203834,144078,7125789,
    292990604,289748690,29080592,35692580,175204522,73462824,174549113,233496949,28617815,
    183550948,210091192,156765100,158711042],
   [155016276,59094210,77140149,161155967,172864237,137263101,82184529,45741935,61538043,
    114622973,144117497,103873353,6127597,99805872,178975816,233866908,285558864,343527226,
    394863828,416423552,393418106,328840562,240295868,150361652,78052670,35201302,27535304,
    58434624,133520442,265165898,476955294,808834934,1324133092,2119777810,3341093498,5202804538,
    8018422752,12240893194,18518056394,27767201002,41273877112,60821205416,88856935400,
    128706280266,184839044852,263199752200,371609176444,520244545190,722203361218,994152148840,
    1357056359262,1836981020460,2465943307526,3282788037064,4334045467516,5674718288936,
    7368932038974,9490371259186,12122413629888,15357867518798,19298216443768,24052278417962,
    29734200304272,36460728106594,44347724100966,53505940782098,64036108860474,76023450081224,
    89531782563330,104597442968292,121223301768554,139373190469922,158967088022658,
    179877423336898,201926838161716,224887717319994,248483730889292,272393546836512,
    296256766358398,319682013277794,342256980559048,363560110048920,383173464922370,
    400696258061914,415758429311866,428033634249598,437251000025518,443205077684658,
    445763426839906,444871571163190,440554763718516,432917162380458,422136999269716,
    408461018673962,392192629884908,373685193158190,353322008722050,331514604830376,
    308672979863956,285213988669894,261525295299982,237978709585446,214904040166028,
    192589450840880,171283286337290,151176308686586,132418032351436,115110183132376,
    99305381874590,85022947449330,72245869703438,60923936346968,50988353064406,42352797260726,
    34914062199048,28563937241482,23194018537454,18692708903334,14950398141300,11867027754390,
    9350210979504,7312222612522,5674220454596,4369673344006,3340996353136,2536074174334,
    1909828636122,1426432249708],
   [1057637336454,779379797402,570564479300,414050953616,297301160306,211440359944,149607072740,
    105865298146,75027622098,52940728434,36693212662,24517213460,15451486234,8950234236,
    4589803698,1930874824,509193266,111329697,283674385,252420815,160649373,75775555,19117073,
    10371924,21150862,21690112,17940410,13244184,9093762,5932542,3721900,2260982,1334608,766252,
    427426,230870,120052,59554,27784,11886,4422,1216,26,293,287,199,115,55,19,3]]
private def pvm_r512_s2_c0_3 : List ℤ := pzigCat 196
  [
   [2318256,12196619,39588184,88741115,138353770,139373063,66631880,18316978,16092535,49825067,
    43748200,58894932,67209525,7990833,20138878,191106944,179330249,152776934,19496936,239071868,
    114853678,49992038,55099446,81042154,159067686,113598162,56825383,22752514,120555009,
    17140465,30936029,301594840,17389349,282035,181544941,43193930,50129912,72063210,135153443,
    125634476,54035020,45766130,82104646,124470182,154292438,67928901,383443698,34425526,
    31980435,76883514,69081140,64770903,138012388,1090932,46124847,103113369,281886229,79335494,
    206441888,45754120,78281050,128768888,11639843,83860322,94531140,120773819,29915195,24529849,
    187560221,100411049,146227815,49968741,121058619,108494600,251505665,195755901,42009881,
    260253052,9613927,9692105,125209342,15376617,55354699,254646363,73819268,14362835,73033058,
    66593749,93126913,82432943,178918689,256736370,255802997,76021468,154082308,172316059,
    63585977,130578667,125747045,61115009,26257801,149650164,16699562,243227595,237586083,
    38749757,149007832,133610426,133541281,227719993,35228350,123949244,46111781,17279124,
    204522996,106319974,64802759,39063002,219422568,155100470,31542057,28286719,139697476,
    190126530,75741784,38978726,180227906,299139754],
   [222887156,36106306,89562575,110481943,81292207,33975545,36087058,121003926,191659898,
    219712920,187446194,94511176,27421767,120241003,140839489,100312977,54332127,51887455,
    94720449,143708861,157995993,126071373,65202173,1110424,62749700,124858440,195884658,
    275235364,350210314,402400580,417348858,391093304,330921252,251487870,169278878,98152832,
    47354736,21972650,24976788,59924248,133869868,260551810,464244284,784844768,1284980646,
    2060237154,3253939488,5078231848,7843593504,11999550950,18190170312,27328806884,40697464746,
    60077015844,87915491172,127542583068,183439154758,261570713564,369793328788,518339236562,
    720387134082,992718593260,1356456830366,1837877125166,2469269510900,3289824078150,
    4346497510058,5694806825704,7399483158628,9534906678858,12185232458130,15444113463718,
    19413917738790,24204359336248,29930433788186,36709663940346,44658487549628,53888095385214,
    64499175767330,76576871454524,90183859580390,105355918642682,122093013125164,140358395040216,
    160066581901748,181090209733942,203243549322538,226300292686864,249974234277062,
    273944871398756,297844429286778,321278825383024,343834746611222,365084454374450,
    384613361514734,402017647763750,416928348701536,429024153175082,438033925503536,
    443758678718514,446072263905050,444923138122868,440345375053838,432449956038164,
    421419255727654,407507521452068,391025454269028,372326719902936,351802322148864,
    329863909009424,306926094431558,283399554953392,259679828546388,236131284673164,
    213081274193798,190818288532536,169583751609696,149567349733130,130911654973946,
    113715120982478,98030677527202,83869577329926,71210740636630,60006525401442,50184671813784,
    41653624572272,34311224060980,28050357200474],
   [22760447708802,18329650049886,14649674054790,11619850328934,9147821324366,7148581643470,
    5544699860154,4267846448756,3259669702706,2470913403300,1859609852886,1389767660468,
    1031028665936,758706893218,553448112282,400293228870,287484326870,205482899062,146433429234,
    103996294386,73315955750,50921950668,34490973254,22517924352,13992593632,8158880004,
    4382086556,2104554010,849599226,237172158,9896855,74483513,64360915,34837889,9090907,6664430,
    13505130,14559266,12698068,9855734,7079650,4804066,3117014,1948344,1178626,691716,394134,
    217862,116566,60132,29730,13952,6116,2430,816,184,17,57,39,15,3]]
private def pvm_r512_s2_c0_4 : List ℤ := pzigCat 186
  [
   [27020528,82840043,142387806,139078203,49166754,35714108,15699993,39596597,8304123,95878262,
    73670999,46564852,163491279,230917252,76050821,38800269,22369151,28635168,85815774,10824370,
    61574435,45605952,4176937,238299424,75224970,151109786,79687901,210560352,42200238,132869052,
    87753000,170161892,76836551,61564371,166099185,25782170,246575592,24250262,43245012,
    179389445,172600530,79221997,76527911,104135408,32413668,159265973,135744942,131830502,
    64185601,112432786,50465722,124622064,199774588,73893026,92992186,180761880,41849085,
    97174003,194393062,157379630,24901565,28047048,236759375,97124047,70911525,145061892,
    76335869,139104810,77716562,84878288,57932720,106792912,65260282,145586039,179260308,
    69211651,164077493,282542793,8045272,104785904,196664759,75798243,284285685,100516690,
    219066165,79608041,214329226,61120941,174084700,114804358,230108849,84586735,22617366,
    20629784,19621325,42973591,9383460,57459443,152977161,59168039,16896382,36646773,2558548,
    75777058,26130358,72266023,212725975,261896803,11282958,262802240,42751340,282399905,
    202979325,28921496,13747800,84466235,15062723,56203472,61961597,180512183,68237287,124488440,
    116418108,34668157,49167887,104423616,185800080,91895208],
   [5071859,39467554,134857700,129644286,36493148,12638315,49023508,165733656,247326364,
    251383818,188707128,93950584,2758600,61647345,91695995,84966601,34855989,58413174,166864228,
    236877222,224909750,135314432,20648810,58409641,77082505,57136405,40550527,53902705,92779613,
    132817031,151853299,143716709,116183323,79587585,37425605,14541416,82092504,165223168,
    254959584,335804638,391712218,412036054,394711420,345891780,277036332,201202350,130019434,
    72052950,32587660,14529086,20045136,52630506,119410386,233809328,418900420,712278618,
    1172738564,1890870774,3002126964,4710158066,7309323940,11237955728,17105735986,25822458414,
    38589308790,57231568972,83992649320,122415679602,176464523132,252772658554,357987012716,
    503976676320,701466265978,970445425852,1327975075374,1805191287902,2429389007752,
    3244908376748,4295173146584,5638343561788,7339988622472,9472943409462,12126373230840,
    15391078137936,19373622864996,24185067373544,29939901772312,36760917391100,44763486600588,
    54060823219412,64757034305848,76934873025026,90659587888078,105966583736666,122853196821376,
    141280975468420,161164060811798,182365205144070,204700278156024,227931904915578,
    251770788801712,275886060095796,299906894093086,323429119583776,346031932916282,
    367287528631108,386770443161628,404076650836550,418838092116052,430730529088780,
    439487637798290,444914709912208,446891906643782,445376760340912,440410180108802,
    432114817536998,420685740120638,406383915063230,389530164818514,370491468515280,
    349664517838464,327464266628980,304313305585626,280626764132098,256797892763578,
    233189908174742,210130439928862,187904012956326],
   [166745634961778,146839962463880,128324079383778,111289382809522,95782751122006,
    81810408921750,69344971441432,58332507751628,48697492565478,40346905013800,33175480144010,
    27071862713070,21923714116704,17620691160614,14056097473214,11128580389840,8744238110096,
    6818389851090,5276210462226,4052225740500,3089349949308,2338144151352,1756470336508,
    1309254120204,967987197358,709842733550,516568870972,373448203724,268530526850,192170551564,
    136762654046,96526823004,67249327356,45961495718,30598527718,19696216708,12165095454,
    7150414196,3961355924,2042292538,961221534,399558822,137050586,32160950,1135702,1002865,
    4445334,9187008,11186586,10865836,9241036,7179514,5215384,3593036,2369378,1504830,924282,
    550428,318256,178712,97390,51422,26230,12872,6032,2670,1102,416,140,40,8]]
private def pvm_r512_s2_c0_5 : List ℤ := pzigCat 173
  [
   [105625538,163357757,90920206,36011208,49402957,10593563,37527057,141776012,133140859,
    109045786,162829397,91496432,90821692,67589721,63714593,15209716,7737530,125994448,121642953,
    41204310,113985021,129988228,42789237,127655968,70974533,51819697,43423449,182463016,
    77259174,63228158,157630058,27063811,197086046,58412303,156421736,106423542,214355068,
    162157696,135210331,233075667,93498722,104330886,101190895,177565254,84605768,109036621,
    11132390,43182480,16598429,16402202,48712707,65324735,94473126,114059494,173642559,163843618,
    43493196,62615886,29239561,252271502,139232970,144244902,104885544,71962275,37499804,
    54154232,312213850,25568367,32866838,14038047,178239721,55775623,117763493,176877062,
    210930161,93700622,169099836,65086746,114651802,159628819,192970976,304492644,157502257,
    68265019,40737415,164798779,23649569,4133731,119626005,112865433,63714087,102040989,
    211949481,199897131,24838956,153465480,51576896,12897092,43759896,43378387,90506815,16921385,
    10365468,9713240,16221396,59504621,96004605,877655,26130293,206558999,147190651,184979544,
    275510762,45258069,305117423,189010353,28189334,39227448,43804503,25230999,2014642,101113403,
    198051585,99237673,80237696,80944538,88160111,172884715],
   [70831067,43704994,16572902,70458573,60417343,43586106,110745768,79702736,22592488,27549878,
    90550426,138954644,121492092,53575398,7182835,11359621,48834888,139236906,211489136,
    236460894,215925426,166117602,96652310,11000284,74889921,124696083,102672877,7065937,
    118230610,209042944,223622024,167660474,83668290,17143602,12246667,15393005,16942881,
    34162499,67076797,103229003,129388779,139958137,137423397,126448771,108480501,78744319,
    31895785,38001608,122727570,220898936,299707198,377762142,385420244,425077030,320298420,
    378847660,130342986,333475840,125695587,377696160,391618529,520855934,575717805,664044198,
    494314141,669517242,85848888,615855774,1293911028,1172333022,3218814182,3747068440,
    6753218096,10329437804,15154993462,24185707238,35288729338,53086346966,78803136866,
    114356271342,166887043872,239579560180,340855378324,482335462546,674415094052,935551058656,
    1287376697070,1754095651634,2370389584598,3176002154428,4216886823224,5551854438698,
    7247235167472,9377771874156,12032154576366,15307441627162,19307797575244,24148523835640,
    29949826076748,36831806956632,44916168787264,54319613212560,65144659764020,77478277604034,
    91386380970386,106902426944290,124023104836046,142706108304866,162861320528608,
    184345501583310,206964687477520,230473759468556,254574416513574,278921497880490,
    303133211161146,326797485829880,349480677354194,370743611566334,390157162197864,
    407313306230574,421838330265266,433409577704392,441768080440218,446725152359082,
    448168866624594,446071081255270,440488987807258,431559990969496],
   [419495213860564,404573500491360,387131981103824,367551665947782,346242193130992,
    323629049984348,300141551105446,276199185156136,252197978413252,228500297263548,
    205428567323386,183260563116658,162225027605594,142499070660582,124209021731500,
    107434174858450,92211365481916,78539228486570,66382728462248,55678917332964,46343728588386,
    38278561923018,31375608369244,25521906411046,20602834183976,16505554788776,13122256698410,
    10352626635334,8105182015708,6297599869886,4856532666842,3717364327990,2824055404328,
    2128940448936,1592265313124,1181379166374,869683575214,635548607570,461384293266,
    332948261220,238857296342,170210635674,120237791282,83928329470,57649513882,38785534640,
    25433675500,16176873994,9931867384,5857393120,3301407008,1768524500,895078316,425712360,
    190164788,81281246,35817290,19076246,13621520,11644586,10218644,8597630,6828970,5130874,
    3668534,2511084,1653752,1051988,648250,387744,225404,127420,70036,37402,19374,9718,4710,2196,
    980,418,166,58,14,2]]
private def pvm_r512_s2_c0_6 : List ℤ := pzigCat 161
  [
   [185747220,68030867,91986013,61823502,41884199,164035176,184767159,78153518,42119187,14438641,
    98030690,21129502,149304289,59259516,63917599,177673842,90640565,35913102,137094521,71101992,
    17406048,54499078,28937125,4319401,22187675,145745487,214567884,33233337,84634394,95519955,
    56210065,31581860,28945910,61090552,110503094,64461448,49092834,240852574,46413841,153414335,
    244923582,300066076,75802036,91638484,32409086,73863421,126940451,108313860,96487531,
    205731664,19513326,38637553,35427501,151149022,22606472,160853043,90510152,45627765,48699818,
    99956809,76600280,55432248,63117365,175710142,145468461,84764086,34796992,309621438,
    185075826,74373767,181869246,45515799,259844,216882914,91421766,211289956,463308,197599423,
    117338314,34471646,273572667,118255179,92516456,70862090,31912532,8529326,245292,66448084,
    158599054,180918182,60786014,75714869,24683609,35675592,99916299,161544005,13972365,40196910,
    68126345,141165277,180437931,205837747,126235399,21295055,5069010,53123838,114978980,
    20712904,124086045,54014151,106584828,36239260,152568127,91469591,152904034,155806462,
    143354899,326581007,155701907,103039306,141426322,28189322,25990547,31698649,102571751,
    169904883,86394425,78734772],
   [100049748,63324823,197640405,142174201,900756,40218886,42174961,106761143,72728391,8476787,
    8964185,66347297,97444509,57460049,14485672,52435078,36420102,3850910,4522838,52477078,
    115387810,144107426,114786686,48548666,6838299,15466887,23238694,84262526,143868592,
    193496104,229476036,238011484,197338630,102375920,20451527,113591211,136167319,67809293,
    33308764,149682670,171251500,206374074,87364412,153178962,56411935,186486578,196890881,
    292897550,406359885,401826392,629692223,468061214,701225727,365956826,491020209,3748768,
    7361701,417121149,481162366,442273131,549853676,136227038,153528818,796968858,84471051,
    712817310,306514852,4607737,664184616,213023989,162805256,317473600,409080111,307135790,
    39601246,315944817,463995920,20633464,55869938,906865824,634330294,1250610692,2672026398,
    3395758370,5620427776,9383528644,13677969008,21142111804,32718298820,48386650692,72028248150,
    106933293234,155548026364,224814792528,323106219926,458600437812,644885045650,900123094778,
    1244083523028,1703080213436,2311976662918,3110589231040,4146396446836,5478922068914,
    7176913067174,9317352857874,11989866941338,15295919206358,19344101604634,24250747533804,
    30140546714732,37140289074676,45373141029448,54957376926156,66001401979394,78593907017092,
    92797452687536,108645060025076,126132711420588,145210176074770,165777179447562,
    187682551136450,210720895567172,234630176217854,259095700773594,283757665302278,
    308217448149296,332045144723076],
   [354792592274042,376009374891446,395256889252508,412121142847832,426227721456260,
    437257724352208,444960106566572,449159322527756,449761102711432,446757387782436,
    440227688516842,430334795559520,417316554532046,401476527663096,383173747312844,
    362809896546118,340813811525858,317625635232946,293682858380104,269408316398126,
    245199005140228,221415596549602,198374028287430,176340467883984,155529490043740,
    136104219631666,118177515761796,101814312982980,87035686651098,73824658673180,62132921888686,
    51887417137344,42996195734710,35353677301990,28845667653638,23354237824800,18762154148772,
    14956401605934,11830561203642,9286173677244,7233459343936,5591739852442,4289705350236,
    3265471342666,2466303183296,1847960541234,1373745071346,1013424906138,742212453512,
    539903056658,390191977508,280122970002,199603333848,140939474378,98380900696,67688059462,
    45749991198,30272480514,19543679736,12270374298,7469357420,4396084600,2495348608,1363544662,
    716910468,363638704,179658130,88481194,45363372,25600732,16417686,11695540,8768266,6608982,
    4882760,3498396,2423280,1623168,1052866,662464,404942,240770,139358,78558,43136,23066,12000,
    6074,2982,1416,648,282,114,40,10,2]]
private def pvm_r512_s2_c0_7 : List ℤ := pzigCat 150
  [
   [162812016,146374322,125741367,94755964,195939755,72407844,73846284,19800251,23520313,
    102518818,189579049,84706098,61973019,159896930,52716725,796393,91738949,11646559,62105278,
    26712486,104082420,199350613,105330704,76951443,13858555,70236114,40465212,24431002,59772083,
    86513439,29891975,128210454,2568384,15368914,79011188,130657467,102787925,184903120,21380037,
    88518463,12638898,372213126,17983345,59888708,24942417,16103063,109394286,176000178,
    221268066,39163494,264801736,61034669,133182153,13107647,30255524,162305042,195895529,
    157844946,11253898,33811836,55225132,55072213,102988724,106483601,21862256,105408924,
    217842733,37270990,150003768,22726663,44801086,80896829,81994201,151301830,75331174,76487930,
    297788166,140747914,145050599,16894379,204953682,164545680,50209638,58107018,133284258,
    122921706,7467928,78939691,118405699,131873183,18960457,106832950,6746112,130569175,20034259,
    136531898,108204796,61046956,107237732,117991286,67687266,14634572,66794765,122579123,
    46273805,49709754,1945385,94833693,79360525,83811797,223741085,287458785,93963233,121655724,
    64868144,116412091,80140043,128107020,152100582,77731727,222818379,68746713,161198982,
    167800118,9597241,132328765,131528207,114886931],
   [108293277,26044455,112445998,142296824,7452971,177311115,174743769,23932091,81105828,
    32372424,81312859,120796921,69599611,19803923,33673709,76614997,82521037,41693109,4680523,
    15587137,64358581,100017189,88085757,34746057,8932882,21100708,16520235,23535433,32595841,
    71404674,65572490,202402762,18251424,207985372,172121113,264139522,337856481,435751502,
    434326553,662294744,352847525,781925194,140571787,450862300,44673420,232956333,266278770,
    593841577,429581292,268833985,191605898,353031158,258676409,577768918,223860393,132087654,
    302781866,374241519,401398404,166305049,208698939,311687090,463525577,18688390,66395232,
    530395881,153029758,154819971,414633285,305832466,134830667,84639971,574091360,59979166,
    230168184,738922822,126294068,272311660,666631970,990182,95558890,495533078,140317389,
    110090473,383619982,155653333,241018459,369150464,13559788,217877463,509548184,536669598,
    315134080,1295460992,2228675166,2787547368,4859557544,8260029128,12186118972,18684139406,
    29446472182,44422259260,66002011672,98702667446,145790556154,211835886344,305758419282,
    438143111564,620608761312,870154855362,1209992754912,1667005135066,2273845714514,
    3073070564656,4116344511602,5462882101660,7182584138544,9358586250618,12084866024096,
    15464398709068,19610902795388,24648382872916,30705985207378,37913611456768,46400169523964,
    56289261294926,67690692190612,80692819254614],
   [95357707283112,111714984983220,129752834663100,149410432803670,170574546320416,
    193077457922080,216694012211044,241140639258496,266079531220560,291126473450018,
    315859207387798,339826741528596,362562246023718,383599432995520,402489208815978,
    418814533359484,432204495561820,442348757132374,449010859394422,452037658368452,
    451364063925492,447014474279578,439101992483170,427824665890744,413457484259508,
    396340429211744,376864456094030,355457096914856,332567983257162,308653872795454,
    284163459427222,259523306130172,235126329552608,211323302000712,188416860856716,
    166657399520498,146240802213022,127308453728826,109949759063666,94206755623000,
    80079914113478,67534286440180,56505619086368,46906461712734,38632357568596,31567959166176,
    25592658416596,20585296777412,16427745385892,13007446457428,10219191188208,7966399440640,
    6162026951306,4729084480972,3600703683434,2719736999500,2037977798294,1515162054602,
    1117924265380,818832558768,595554764844,430145502268,308414847826,219341742420,154515954876,
    107614487194,73930714112,49974585338,33153483724,21531821456,13658181328,8444193864,
    5079301302,2968530576,1684476980,928430918,498224904,261836412,136325148,71699226,39125976,
    22739474,14235818,9493122,6572336,4602838,3200420,2185286,1457288,946948,599222,369332,
    221822,129892,74200,41350,22480,11924,6170,3106,1516,716,324,136,52,16,2]]
private def pvm_r512_s2_c0_8 : List ℤ := pzigCat 139
  [
   [23949388,292165010,57853507,113894072,31536676,72822323,162150263,172352748,126605581,
    98791046,31926689,88260216,26535787,72092151,9949575,77079577,170600580,77494077,127116156,
    56854497,140745671,32028378,36240620,31678986,12649136,37962278,49626393,11980827,34835805,
    73494039,81664436,164556232,132007597,36814264,52295099,6263553,180990225,217623664,
    144770732,165200841,20695251,32089762,113574090,156279075,1776654,43104023,24714531,
    304349928,20569152,129452866,109426841,94385928,60661072,118814609,239035554,227307744,
    210178394,92209108,97564495,128769894,20474297,105332963,147050502,39451333,79034679,
    155017830,40959674,26895195,46523766,17432295,52721578,108142106,112755299,143509073,
    87739962,78476554,57442683,29233930,104904562,48786491,175877695,45493649,190557782,
    235411598,86191362,15348414,72460772,78249296,58487256,99195586,84398584,33501486,132723498,
    253327874,128979752,92727605,119156149,21754845,2321048,26972831,44316991,62329935,45129419,
    24926392,47219514,4201860,42581724,175628516,199258068,55766298,42095053,8696608,28720192,
    79564109,120391993,34579352,157992990,5820088,260812957,295733767,94698397,15083506,
    106951037,216837887,91124745,128336860,162528254,812169],
   [131650329,102697079,10789015,33831790,54975294,92282872,79085396,50501737,208096291,
    221045605,59570275,115089588,126262618,2656094,120279081,99391649,43630995,43261858,44523535,
    4886586,147743941,84177956,194784963,180908556,380692751,278102408,499523953,484796024,
    530520643,489689754,539352365,237099364,247601681,67350807,239047290,405968981,429195162,
    489840859,232200822,21808901,140422163,499226572,324117359,409084564,2242722,162120223,
    393267802,414612877,183865790,107350748,201759221,616111272,58927926,220437800,508939636,
    294167317,146421898,40298346,422573547,286582432,10511391,159804899,469787362,46070681,
    30615011,456291096,137401445,4974660,387022898,233820075,39831727,292235294,318764855,
    113274561,229362448,372309273,223724193,172042640,384618015,304478863,233437942,180504335,
    195990929,467017170,217917336,18349333,607382944,527329440,14697870,437481622,601969224,
    46005287,55700306,500822808,4473675,287235931,281456854,194183336,375442895,14775917,
    415747580,71839041,156407463,606345804,779935816,584826624,1513316792,3050024698,4247806438,
    6457813586,11021824012,17417992286,26182215064,40183520184,61784868062,92619525816,
    136896816014,201674545300,294429087974,424130688814,604662260774,854855400406,1196832776982,
    1657926136900,2274217001540,3090764001386,4160397502888,5545608065302],
   [7321684622986,9576612647586,12409011854726,15928181359176,20255193244550,25520878366614,
    31860924783094,39411818645940,48307954976782,58676496197626,70629036795832,84253232181634,
    99606391473126,116709123643934,135537215835922,156013606548348,178003471962968,
    201312516898678,225686444443880,250811346282914,276317237279180,301786221858404,
    326764010514308,350772659894934,373324241348564,393936572990402,412151048028216,
    427550564834244,439775314875904,448535808853214,453623751132084,454920800634596,
    452403971569722,446146300282086,436312692736172,423152131658872,406987445606608,
    388202972718868,367229954174182,344529995370988,320577842734922,295845048829328,
    270785546929026,245823324420152,221342019933534,197676524755906,175107070306650,
    153856293860160,134089308314088,115916227163882,99396335732978,84543262614362,71330855236308,
    59699678105746,49563994193886,40818873004926,33346916642718,27024148612162,21724839646880,
    17325304946818,13706858741004,10758111492166,8376698950074,6470437312620,4957872801874,
    3768243463882,2840953960396,2124727400706,1576610414544,1160970243164,848560521230,
    615675102392,443375576058,316771031288,224339232810,157293821820,109012497544,74542430904,
    50192843350,33214944792,21560490780,13704685582,8517620068,5170025486,3062367760,1769832596,
    998673176,551366408,299107054,160618200,86361464,47215536,26688902,15790746,9800120,6322416,
    4174602,2776860,1837722,1199924,769110,482602,296056,177468,103940,59480,33258,18172,9700,
    5054,2566,1266,602,272,112,42,12,2]]
private def pvm_r512_s2_c0_9 : List ℤ := pzigCat 129
  [
   [146594981,233858838,102522478,87441850,43601949,288266850,99835899,15718949,70672669,
    22071287,42365338,110436621,117703702,85302621,134789908,30369640,100387155,21887008,
    57767895,56040373,28733264,129864208,19887580,40758673,35615363,28804339,90890615,157187048,
    99605085,62459634,32618314,91325470,124213243,154624011,172825370,71194881,5765455,61220706,
    157742444,44441745,303709689,150551636,40232113,104672488,77486,67669677,75043478,59727879,
    146006126,15175512,244173917,3007447,17174604,74105584,117092092,15871757,193129230,
    140062890,196511345,28901141,124235574,30880382,191193214,261487162,76890560,65008428,
    91033436,3952492,32836700,33585924,93663699,22070021,154285466,56184568,107719211,7154151,
    140219966,79579114,38024015,18416435,51014524,11094843,127670569,52455335,148267978,
    150539744,39170303,127846049,80304369,36307915,40143840,152125440,133750808,17079384,
    34885688,157250664,141095786,352018,39752645,61126708,167153044,207642542,174337538,67956608,
    25681871,8745743,43932074,7410499,102654137,75928073,28947798,17065680,102524063,111349083,
    42133778,145429040,82974760,28018360,126646218,217749394,87054540,149230419,178741453,
    38962476,198135366,88700394,123340899,162906149],
   [49479907,6750635,140309471,249662205,226770881,44767109,2810790,86590530,47681071,109820538,
    178267317,77665462,366200785,325384934,221476507,635197148,460294225,361251120,698854479,
    301711324,273894485,179917964,89887572,304174571,342636834,481570325,390031168,272758377,
    22329033,160301114,398879367,413892182,337199611,31401788,65990500,445478929,343055622,
    260816121,4729387,219768630,461839261,203167504,131998799,248100127,351288820,311487495,
    17826075,165750368,415021653,200255678,74655314,245858617,399421142,6735124,87589593,
    431772922,147516931,118117879,255953050,309003581,22252619,418551784,42211431,293827506,
    552682212,89903685,93743910,274773058,329227593,71176033,272602540,231542437,9433769,
    406037538,96286929,31309305,447278184,3563645,138301221,383439218,61409674,289771911,
    222909778,143945142,377115211,1373325,205506624,386335037,303702459,168536068,241490685,
    472345533,141851024,172602136,274612271,145480514,613031950,167645456,60941458,656689508,
    543930836,32792323,238234940,612334466,82269026,237306213,282624626,340208486,282012129,
    228457053,346080408,141008088,375459255,13979727,533314320,248789092,35991738,836717350,
    1754542216,2162268246,3308886948,6169349484,10148540748,15359433612,23916836012,37905640016,
    58446936812,88032095158],
   [131959017976,196765610512,289552292672,420414288152,604489680626,861241104894,1214019091788,
    1692512517160,2335557087094,3191405669366,4317244313992,5780893791004,7663492831260,
    10059957585850,13077343433416,16833897004542,21459217672098,27092822713748,33879664164864,
    41964466837900,51486804454552,62575898817390,75343099888618,89872410134022,106211475072520,
    124364281033128,144284516794808,165868659541110,188950020075798,213295977065482,
    238609125824686,264531258151790,290649291079912,316503807619082,341601367896412,
    365430410620024,387479036697126,407252960034162,424293089902356,438192886594354,
    448614987969428,455305549594492,458104623700556,456951899477266,451888198703114,
    443053316603926,430680262458400,415085595488994,396655956625022,375831757668040,
    353089534895464,328924297516006,303832597071182,278296617173958,252769637990626,
    227663546362412,203339190177458,180100081436506,158189397092664,137789771976614,
    119025261089650,101965018287712,86628452199866,72991668355856,60994863760898,50550146599266,
    41549177611454,33870139225194,27383771451130,21958442154402,17464344175136,13776915683620,
    10779517912390,8365351748006,6438598426164,4914828283588,3720798992224,2793819328730,
    2080863359452,1537586041098,1127335705972,820206126840,592136825062,424058360856,
    301083081908,211751059656,147347371612,101306701416,68715019942,45908977068,30165017086,
    19464451992,12318522142,7638292824,4636884534,2754785236,1601954828,912662148,510426328,
    281222666,153490918,83658120,46002262,25806556,14906362,8902078,5481954,3452422,2199870,
    1403756,889676,556756,342714,207018,122546,71034,40304,22376,12154,6454,3346,1684,822,386,
    172,68,22,4]]
private def pvm_r512_s2_c0_10 : List ℤ := pzigCat 119
  [
   [227155163,40256564,3969798,309578062,62916179,38878554,145806040,62000980,182230008,
    131622441,48123866,43997941,80882219,71269482,66051783,58381187,30230058,81629180,3952689,
    31292182,16959122,48138932,213911631,62994468,56614601,47799660,93201428,25468764,38183230,
    187364797,99294576,23168266,149748567,24376494,21174128,245359074,193677791,14343931,
    140279694,134648475,57275263,83368755,113531208,192824412,88285433,8028870,50190753,
    152861545,107675150,65254338,48828789,6117283,83532053,82479660,216835608,90098885,145592823,
    77485226,39954263,151001331,29739094,96200014,78270858,158186360,98160888,56167333,45449811,
    4461221,7589067,120498506,235666320,127074000,33935906,143739344,202093476,48280778,91558943,
    29050341,98084888,72142434,55247539,50059613,77219880,77894690,40455043,16060655,129858170,
    122134068,36241133,108375695,65185667,18636493,50509408,137557886,92979422,83459569,
    159979395,49920843,58257356,40289964,3008847,26342546,93568754,143623292,148115004,74150852,
    38763243,50747713,84873424,206027078,168999766,73625886,87140588,156641926,104373438,
    45249499,91596787,20410950,77093440,22888309,157853789,80214273,17776326,69677692,147293325,
    24740273,1982698,448437400],
   [28927370,243526662,453708731,362273066,331738425,582017982,513794023,411200664,383456501,
    318994980,114987533,201168649,76070476,566216835,263622704,539824377,182939368,11956964,
    75312515,366462006,543218147,135063736,230409291,18787769,497000082,255893211,291275060,
    191780713,292232215,284182396,362484407,154682654,71920114,337769133,329155066,182976409,
    115140415,258482376,379632259,90080736,148849346,312508903,253503662,81732765,341427709,
    230054426,195855239,148705295,308254548,266262937,125163935,194006728,340278145,23148661,
    232061124,315947815,227184,166342912,361670205,2854320,194726342,302539921,66603256,
    318134224,160006635,141473516,388013292,202713723,97473437,214650902,268473349,143184733,
    431876756,122586102,41293440,551306060,228013524,195169135,227583620,158549822,348345013,
    17549266,302998174,193039845,91878457,418105014,70263456,191445661,335956256,305930096,
    232435083,40426716,388998602,115117753,272766909,261131096,125375116,415660831,127168703,
    210452760,300433375,513378541,51395350,96857080,396853633,139778629,464652692,236581316,
    110305253,377733504,732437674,232959388,832229,514052322,585236748,38224387,123828387,
    403578274,325375392,282166957,220827973,330763540,204825086,355644363,208311997,383614282,
    310150762,154274695],
   [125152022,984038840,1403722808,1644534048,2993846226,5738260156,9283005826,14227587190,
    22670398578,36463459722,56921785890,86827825584,131592153784,198208990086,294714470644,
    432056425308,626303231706,898890177314,1276237698550,1791269677134,2486305493108,
    3414729169534,4640972275752,6240948392408,8303983819352,10934444419202,14251140981910,
    18385151499240,23477866713688,29679230664492,37144284816348,46027003135016,56472624285360,
    68610095047482,82544545029348,98348581655064,116052266067180,135633396908354,157009881815382,
    180034530873334,204491609622354,230095149343292,256490255481398,283258732751892,
    309929076478686,335989695592908,360904282273226,384129086578114,405132190368276,
    423414161882884,438528464994384,450099756778274,457838908657940,461554448124460,
    461160353695712,456679767484240,448243901906656,436085756228490,420529089189332,
    401973805539792,380879056122688,357745018671560,333093983229510,307451363026512,
    281327531868714,255201605021206,229508145938644,204627313087382,180878429329654,
    158516636809988,137732267660118,118652674934112,101346324549444,85828845633974,
    72070530228994,60004608317498,49535613744106,40547308604142,32909862261828,26486176521996,
    21137346129544,16727250029420,13126238185750,10213869261112,7880693055518,6029146645664,
    4573710496234,3440517890366,2566613725006,1899024188254,1393747084692,1014724375526,
    732826571560,524865094056,372647980118,262098054472,182454295856,125573714360,85343255052,
    57201645842,37762524782,24524475168,15651307136,9806516206,6028244188,3634146428,2148498402,
    1246205060,709999166,398130304,220441448,121087080,66398524,36622744,20477982,11683974,
    6824814,4077164,2478948,1522956,938172,575558,349756,209700,123718,71698,40762,22718],
   [12400,6620,3454,1756,864,410,184,72,24,6]]
private def pvm_r512_s2_c0_11 : List ℤ := pzigCat 109
  [
   [233216423,13755686,223779459,39744014,234523726,4691087,149405032,61096913,52288844,
    202892916,38585776,91002986,64666246,21095787,84538467,52156926,37962803,35696776,184490399,
    86865688,9152900,70251711,95062202,2420153,126305708,52565943,52744977,70166462,236218643,
    53569100,12731304,146245730,28868698,191800099,181641002,63021936,171979949,45512719,
    37628341,107528422,40681196,135395445,123170098,127272558,96456161,31201163,81001405,
    113917781,96207092,99868412,36176674,79181304,99655353,178409785,109891412,148335716,
    127372475,116307499,63207614,37137130,7338178,71149416,34449688,15813569,15793746,39821865,
    138143327,73784469,41402864,50463724,82167044,171468096,121067000,63344021,127145179,3011100,
    121184922,78616436,50447,78859084,239429220,226280490,50694942,7500485,95196012,105947300,
    20604069,51882071,51687722,80268830,8376007,49185461,2810819,36178598,68018758,122534596,
    103449502,43306271,158924475,89740139,69496624,130525566,68763030,11886887,54696675,51626313,
    16718707,17969608,29318219,71022767,41706029,156700298,183369422,168416780,104034035,
    77802456,67637291,298881400,217971817,342869986,215616087,680045802,315956383,481319158,
    472721411,492880318,150639029,105415536],
   [83786451,287483205,438675294,353733421,273484134,517689771,26836055,244914628,78954685,
    531344054,336790805,213534476,94882920,164447685,389415806,360753427,181894350,116000522,
    232385777,380560506,262800159,19370832,121894348,546001015,12910566,275069721,227006187,
    427940268,182823895,15111453,39032910,506864821,146509018,118391564,145641289,388504342,
    85060547,207021985,260207748,248345401,112228277,228570672,304967091,2967849,241615644,
    281530583,50189072,144166658,357289343,71998270,187307144,270846231,113839804,124528542,
    381072567,20980624,141101332,304292135,64532598,185895370,340562473,57139211,188537850,
    291082163,85204017,256475048,228395695,196797937,241947524,152324045,305340275,196080218,
    10421675,301229763,240746402,315672188,143708151,135575108,331966646,253543977,269198659,
    222310914,27946045,205123077,391233032,454863234,48319551,171284070,468805840,56488891,
    248910031,252040442,137826282,334095755,11334944,382438148,61169491,191357407,361277692,
    320309790,206322071,10267022,436893788,40751734,305640427,157485714,336877040,218888611,
    311376153,195721120,82919258,495872157,348519297,151622992,89180501,501036351,92619725,
    417507914,127588326,165571007,323945960,719151512,300135888,26711433,404600774,682112194,
    179004538,189822945],
   [208785338,495204246,23476456,366908195,13836514,393437306,24445720,411987049,99712377,
    404784936,227877532,207437725,62076204,860193456,1300228924,1514193556,2648165238,5247537724,
    8942156780,14028865292,22364564382,36320942876,57908703056,89904893674,137597340208,
    208992510536,314085184508,465460127024,680531126354,983416958042,1405367010948,1985143606974,
    2770940461638,3823143234072,5216019220080,7037924000746,9391418118098,12394150529908,
    16179394797060,20894573546578,26697632668388,33752502935402,42224314205792,52273508982804,
    64047731735740,77671732634730,93236774256504,110790735937192,130328919330968,151785154693784,
    175023711000144,199833558819082,225926443493740,252939126271616,280439270715088,
    307934582101962,334885462169440,360721564833202,384861859956746,406736793006768,
    425810751320344,441603476914912,453709680258362,461816249067944,465716088648816,
    465317329159030,460646893370634,451848193614756,439173522636962,422972070838512,
    403674421950134,381774198022678,357807582205466,332331771154832,305903730476634,
    279060652930908,252303181882996,226081948789854,200787550855522,176743905669870,
    154204907622128,133354309185796,114308631021522,97122670142346,81796935509100,68286219937976,
    56508567957730,46354077574710,37693182673992,30384217084952,24280131687268,19234248785972,
    15104944252342,11759186175574,9074935439028,6942506582540,5265064237876,3958468081670,
    2950673193764,2180855308530,1598381582198,1161704532878,837228676120,598186087020,
    423553072478,297038531290,206170658682,141500909622,95933739690,64180008164,42323314908,
    27483231486,17557506868,11026163292,6802860762,4121958984,2452598060,1433464078,823608368,
    465837314,259942516,143554810,78793124,43207296,23809984,13260100,7495470,4308730],
   [2516276,1487462,885368,527584,313060,184156,107022,61282,34510,19086,10352,5498,2850,1438,
    704,328,142,52,16,4]]
private def pvm_r512_s2_c0_12 : List ℤ := pzigCat 100
  [
   [246744411,596085,21746703,305620033,1219330,11579672,32778522,211165216,40354600,18865861,
    19452694,135572088,10512251,176790510,39973112,158796510,21762630,134279115,123053198,
    21070675,21750761,12931253,134872403,149270474,149920265,22247933,70916700,37287833,
    117561034,35447713,46386392,174782952,199774031,173162771,74710766,31892004,42772042,
    51527437,60434131,198912778,81951088,172373257,26212317,40706162,58201235,4676354,9800119,
    63742453,95657954,131160330,30352997,10244475,12144632,176984415,147369231,158572326,
    195563590,37240157,91197313,5844902,17992822,12744332,25470706,38171727,79349387,2416571,
    37882648,19328405,6868645,86843492,88378562,1128699,34312507,15564445,57884269,138502835,
    109544147,67919606,214751316,147949390,30684577,58126683,65919368,81535606,57387623,93675547,
    61937510,178271840,129708036,80833524,135783698,168319498,97773486,30786280,30641972,
    39527748,21045582,47247138,56995932,19310448,109832889,45645393,16392638,237651350,45312490,
    154694682,246953399,130940050,335958621,396925992,299378539,505175980,515359497,413753012,
    362799675,394769518,213873533,153365195,33994998,254024681,536411944,324966725,343493598,
    103140843,106189864,304187412,414645231,313623988],
   [190342117,311545720,310168318,272265421,399223162,115413193,285079246,254021742,414109651,
    241149774,123490169,97820046,328998270,470277745,8390984,116070889,243563021,386896106,
    161342697,28539132,344407642,210995005,234708024,122874470,261083803,316542224,37656873,
    190123163,303954880,124773955,47285974,364475666,316028849,209997661,68444497,481978571,
    61158162,239835322,251371547,69992428,26863861,446715343,83900558,118139484,225577857,
    235320104,148559582,259486341,172486710,100992830,334377645,75110918,93186650,305810159,
    111246518,201691140,297499065,21875545,169503530,282758193,38702637,304707904,171663561,
    174443671,217749478,157348981,284929797,227028344,33395624,322747101,99603086,121507664,
    347459111,55907081,242119448,225822147,219808411,252563570,36403297,341065625,105797578,
    109176078,393845565,133938859,297060218,45540785,120580729,408731348,269043854,279482939,
    54655293,216993324,232427125,293926885,320529760,336602520,90645843,187965322,555832720,
    99950080,215278403,224970392,289622516,255141647,205844429,317905730,149415216,287663675,
    45605068,462631804,79525760,236644625,209316418,426562468,85007469,250486567,259706320,
    331249058,220329523,278204655,213131528,143990906,439562943,429019181,83259192,23692044,
    468295589,331814377],
   [281374188,311129654,128372169,8061197,584703356,617389688,98522014,43551248,541495864,
    609231772,51646100,180313071,251349682,472344418,7059548,369363013,36060115,376186074,
    117329286,370516163,240714785,298044070,365788620,71194027,131588051,546950328,1308754718,
    1723560364,2525268086,4800813418,8873117414,14779893016,23710145394,38371397264,62099953386,
    98577984820,153163857886,234555697218,355290735794,531615938390,784422317966,1141589484476,
    1640317485898,2328342356460,3264713185124,4521433609582,6185916193310,8362802092168,
    11174099406076,14758089342582,19267963694096,24870087499992,31740645382660,40059732138094,
    50003280620520,61733958294694,75391587586242,91082721408008,108869044072158,128755313008932,
    150678446218104,174499183211402,199996846879016,226867174507960,254723478036332,
    283101986261754,311472223402340,339252463330854,365829290946558,390579851386730,
    412895589559976,432206640513868,448005974317414,459871925468552,467487341172606,
    470653726629026,469299441536200,463481786994542,453383295239340,439302630143424,
    421640497289728,400881152961108,377570541950892,352292557977210,325645119556368,
    298217576601436,270570538477876,243218785563796,216617660522794,191153227237084,
    167136405555422,144801113930776,124306158496204,105740284305392,89129577024792,
    74446346670730,61618725696696,50540392366340,41079998098636,33089985109900,26414532620164,
    20896404357982,16382525676982,12728209803198,9800065688126,7477725084528,5654596791278,
    4237879837760,3148050601890,2317998604960,1691940809538,1224207722310,877971043690,
    623969679888,439283150302,306193732650,211168498856,143979812762,96969718584,64452175360,
    42238895902,27270181512,17331192060,10835565852,6661075424,4025126738,2390762706,1396132610],
   [802098030,453861594,253369570,139882214,76616410,41795104,22808324,12507600,6919032,3870638,
    2190858,1252760,721336,416478,240042,137536,78066,43764,24170,13124,6998,3654,1860,916,434,
    192,78,26,6]]
private def pvm_r512_s2_c0_13 : List ℤ := pzigCat 91
  [
   [187768907,209975729,112358522,42037269,220245857,68505531,123850669,73103355,35156025,
    231017502,15861254,76137062,39108750,43176559,158056488,23877399,7541509,245482688,21412904,
    181396850,37321317,56861687,171854476,54364183,25020187,27961272,93814453,68925682,23841875,
    181135895,78081048,71712982,123062673,5080943,83907042,114776848,136585852,108200123,
    203648723,69712778,91354290,123779943,70591385,52332412,33580202,78352938,76389410,73763157,
    58167987,84158184,132135,129837237,17554933,57699084,64575889,39817047,172199522,174844026,
    55594755,169244573,99022251,14378727,50905108,87644874,25294990,56709333,17860287,62286652,
    34091614,38055703,26068921,18811994,7678355,65156955,52201823,23932490,62104250,21214260,
    5227223,67945228,133483472,20703568,190244107,218196623,24149639,123600258,57720432,9818475,
    44871228,153186444,52532430,4913951,107060019,74315342,90512775,159044740,131788353,
    362667154,178105563,491491086,267488781,594476914,402574697,429305992,347845529,372626206,
    7498552,13483293,145176220,431839575,348927372,333595779,419174194,61018462,42577427,
    190239672,473073895,364802228,125390357,57432626,124347240,388048397,431319640,74614431,
    41829890,102528688,462280903,282923310],
   [107461995,147972819,232163384,270133497,371955802,226120918,263466897,218136968,197316329,
    71003790,414191514,267356127,122924554,200923036,45129839,510521510,28836160,243450111,
    262935486,95851491,91155080,364589652,278045467,53860249,99316288,376366565,42720266,
    89374944,267756507,251236320,167252318,210674983,258339964,120391102,157767687,285904880,
    1589564,316373635,216511758,135730926,47101913,375531938,19476604,444284857,48081679,
    125440833,334530267,189532800,113356670,339692393,1184334,22642388,379814981,807410,
    204672946,229321371,7822952,320303518,131521759,117604279,245709358,145081185,289396675,
    214540114,63216584,271505875,120469238,130625896,343823523,66019387,273256236,144254707,
    166918649,260435480,35144657,352975341,101757864,173084060,294286749,90227333,260949886,
    154343903,311243191,178352410,90178490,361487841,57678845,265899436,160670149,267469503,
    212915662,77072548,429654327,169661889,213722410,124613947,230266607,336625138,393837646,
    150703413,105677971,273102842,49249103,436174657,1442975,373567974,5788970,107749073,
    418967882,478059212,69390339,79127495,379653222,208093012,309355931,117524101,343151920,
    92020196,307277527,37333050,454410276,115632076,248683353,121507030,456127508,53645174,
    285934541,107882188],
   [427613762,12282420,349706431,2339343,290621982,138907659,555244609,239079107,151526424,
    132978877,507133817,172610555,377126984,277229300,125112707,56861368,611848072,620387718,
    114027132,4207488,456803480,619930098,139057210,227558089,72178210,448688374,196743036,
    310567885,265196149,224731244,329468780,131070923,406467717,40468559,411679890,298279768,
    72913269,117538952,1012512540,2028780902,3023346500,4934359884,9053376250,16204916876,
    27254461204,44450316988,72036447032,115839049832,183186257708,284209483042,433855397782,
    653273917958,970469583388,1421410372890,2052389885964,2922943030930,4108022109204,
    5699111322098,7805078416996,10553337290078,14090657074698,18582290379952,24208776360692,
    31160891322998,39633442238766,49817818148234,61892558214684,76011584715164,92290843223132,
    110794785516166,131523862237892,154403499451734,179274828898516,205887962102124,
    233899202094634,262873517629424,292292796593674,321569473878562,350064715404276,
    377110449231240,402034656633070,424189025636710,442977399967744,457882916279982,
    468491729513032,474511760525996,475785576159442,472296957690486,464170876795384,
    451666723230686,435164979638644,415148145455680,392177348089872,366866459464426,
    339855533145720,311785092047072,283272446816462,254890972767390,227153129120276,
    200497861665352,175282778362410,151781107968936,130183029967922,110600626955200,
    93075545414682,77588461003592,64069563907480,52409423112826,42469699684588,34093251122256,
    27113229550516,21360859253808,16671697982444,12890329188504,9873569755424,7492380863396,
    5632722928090,4195601239300,3096522075242,2264538732842,1641028242608,1178309962936,
    838197009140,590556739098,411942904044,284346969240,194099319236,130934154966],
   [87217011910,57322666978,37144448990,23713314426,14905517678,9220076494,5610411020,3357730814,
    1976522460,1144701058,652662116,366719764,203365940,111532774,60651022,32805512,17711334,
    9578472,5205294,2848732,1571354,872976,487434,272696,152314,84636,46630,25402,13648,7208,
    3732,1884,924,436,194,76,26,6]]
private def pvm_r512_s2_c0_14 : List ℤ := pzigCat 83
  [
   [28868453,257402241,188719051,90263594,18238265,34947887,184484037,6592726,141774755,
    218576243,5489266,45517189,50389232,230697780,104873665,96944566,89201128,38022145,117802776,
    56026931,28799019,235414818,94159176,46327474,118238210,33237987,44919214,155207220,73257165,
    84541093,111796876,22136016,84000867,34271739,53038401,581798,87621784,89948027,201963425,
    65423502,235426078,61508286,50114411,2752027,19724641,20989741,38459164,41735547,153335143,
    26797325,135179578,46644442,62766537,38068466,102459626,27174961,86868337,31909894,68148834,
    67327047,145152087,59682869,61784064,131460612,135744316,40126978,103184637,136487139,
    32091007,51310130,22679710,25251867,5510511,39743998,30624366,10851679,23672255,35594528,
    46973790,4137450,115730035,22849405,2723971,117263136,189272413,37162810,119772029,466459580,
    167507291,298002306,544268561,384556196,485049433,362033040,420918011,272199958,17381559,
    25696438,280965810,279019431,417268628,394955355,221599422,82097117,84704689,287371064,
    343675521,447210002,18851923,184183820,300832008,300938309,370350836,135866043,110592294,
    359710654,237970477,271655290,258123475,229417401,337900198,136740935,318262128,51166964,
    330329721,329311218,82556639,8014353],
   [175039446,403584571,174286644,225949344,183402565,253332992,122884653,139952927,337899690,
    270421831,209198483,123099606,205020749,266726180,284241146,306460773,116170964,142203504,
    125506947,300790978,27253123,304853995,305794656,175493522,27000836,394196408,35910631,
    173993653,330793464,33563098,63924155,348843542,28742675,176834189,194597570,188693497,
    317060411,188351298,35323893,196241359,236570128,10591584,178856511,343821392,214537808,
    197769005,100166308,26842650,299189829,198846142,422523734,44176549,52918366,161715030,
    363506295,287697371,175591914,115933061,243205171,180320476,38055345,389997429,15041980,
    81138968,346433757,74159765,274614230,103270063,116176501,309297834,18295760,334673779,
    80220396,177029670,250716557,52413421,284662204,139774097,324521035,158234916,118513068,
    286666097,7500106,291172972,164289259,285318551,196976136,103523904,330912813,47850253,
    270551522,149356793,313256143,166359628,145307230,348107455,176101347,257371966,30685911,
    323357209,100790438,269196658,266130757,390779875,83447834,56703258,341969479,63975111,
    458004214,208161924,216854033,56839980,297733810,164530217,424847471,67259940,329354412,
    67373013,130684681,400405380,485966408,31578957,101626153,355701378,311440562,228199163,
    228817867,268582092],
   [246684034,231636025,169503107,354983708,342933844,154665899,151777715,342285170,359583898,
    141736721,205996325,282418786,383442146,121641117,336892329,61892322,239705498,231716351,
    579158629,234902529,153579754,86540189,450572433,177191699,391378994,410034526,5863527,
    9802097,497948588,706063152,282751306,69606951,198522724,580027542,374176878,153556981,
    214171819,224420080,401531910,8850885,389551073,166651567,295468534,273595364,197212201,
    388007559,16218546,465975998,410049868,165742392,541730098,1836865052,3732336446,6284719486,
    10703003430,19015421124,33404065884,56528050266,92899279502,150138665380,239390674476,
    375608014146,578876802338,876884393570,1307496267372,1920636245298,2779837854184,
    3964364422366,5572002880552,7721520450804,10553654483778,14230406860986,18933153927288,
    24859788528678,32220224584658,41229252332032,52096403149486,65013497389226,80140947590170,
    97593501651360,117425649340610,139617101144808,164059512837940,190546239564716,
    218766769839866,248306742283486,278653722849554,309208673590154,339303132471616,
    368222032961394,395231504036390,419610102025844,440681243214110,457844482108700,
    470603637455878,478590237807078,481581045261630,479508536302796,472463427015556,
    460688845356982,444566547226748,424596388779392,401370819526440,375546333355990,
    347813704659624,318868638978318,289384315162810,259987182537772,231237198797304,
    203613361004108,177504896835012,153207948321730,130927131690066,110781086102480,
    92811039217570,76991458600668,63241946182990,51439615967724,41431264985296,33044727076096,
    26098914638122,20412212028594,15809067941026,12124809997258,9208841828792,6926464364790,
    5159590354814,3806609134410],
   [2781626590570,2013269139088,1443208940634,1024542230438,720131083392,500997962450,
    344840228330,234708737222,157872533884,104872664996,68753922922,44454457464,28329204778,
    17782840462,10990096994,6684551970,4000483838,2355571286,1364857794,778497664,437426712,
    242371350,132619556,71795026,38542488,20573202,10950430,5828500,3109796,1666004,896694,
    484590,262508,142198,76796,41224,21928,11520,5962,3022,1496,716,328,138,48,12]]
private def pvm_r512_s2_c0_15 : List ℤ := pzigCat 74
  [
   [57754404,9394015,276833557,143456581,144164517,72145748,47400606,153694973,22334079,43226348,
    230737263,11083995,130628951,261220569,42736974,27706726,9281187,149194008,4243912,35084815,
    176186216,68169472,75039225,37728868,8164352,16309543,185283190,168104842,35292559,34611134,
    159635388,61051260,1948492,29225108,21457227,9312934,120306986,6571328,182236657,62375367,
    146855822,57888210,133445931,126546595,42309229,114542,88846980,141148424,16604128,88968235,
    25145384,131331868,1494112,143671293,71262449,37519196,14372539,72298073,17453570,106155118,
    49005364,39930131,27959701,35865938,58706616,38494386,31023671,116796297,156059087,26862625,
    99829446,192247892,28072812,28345010,151758523,101655696,177283317,189550514,324304485,
    343307666,332696243,461079136,504867989,391288794,311350057,392620388,149695829,126798725,
    128019722,212136223,455826254,463928079,115132000,191893745,20868296,367372998,270298589,
    398364768,206974163,34907574,89488896,399893243,275069822,291051583,9175100,209408954,
    223782591,410658966,119042973,65262067,280653600,284965381,216813630,44863479,280773369,
    322194002,134470887,141598616,383048346,166535815,263695348,35258336,220819565,438451886,
    104768944,56092966,243383726,399440453],
   [44494935,275781078,159880695,181323742,56424420,250130895,346827984,119230932,238421487,
    154029700,124126627,116425511,342189496,135855451,174662443,309095062,13135759,14309808,
    192336080,375610707,217080975,269610232,84453761,22383479,206974036,209043365,12953832,
    408506830,76110013,126275067,168367744,166366747,28009167,423089714,47476198,53253043,
    333552564,18061202,140043687,303628982,121390868,102434643,317547322,157578672,300968833,
    10200684,89669464,286593017,10973259,186134860,277997971,156242883,320805822,75408428,
    25281381,320600270,870952,386614791,60969072,249449394,62780387,192021708,407449342,
    127528659,262854883,141121872,66920771,344958817,75960676,152083822,308317081,150008833,
    187003372,204929627,383989437,91411094,82098928,273679897,48389974,342721290,113471917,
    260110285,188850572,101241702,288530637,13550706,298444302,151862213,316671319,152586282,
    132250266,296022183,71504321,305587568,54063859,330747209,102575034,231503482,246755765,
    235010669,234545534,84969580,339901049,68104365,284782084,100142775,400692515,24107458,
    235337958,187296899,241569517,243755074,198996228,359229959,341879329,110673456,3725569,
    370270163,56487205,448626558,213096096,220439879,8113472,309427238,69098451,436602643,
    60266977,339714276],
   [53004710,210926641,200404220,548203430,179522516,177009309,139340478,434173774,50442890,
    333420023,21015675,364614782,92306568,286295471,12411501,430406168,232917616,223546829,
    88372337,383775250,321547626,157573303,177658565,291235194,381002490,114955035,384952763,
    45426507,201327960,172400199,586945625,359231003,130176098,104441168,289957265,255631215,
    293250298,582468484,258805266,45843507,230671486,666487962,553806692,43278566,102368141,
    282941272,523938074,176753186,282340715,201143195,250824718,352634810,74319191,408837071,
    165367483,292031882,294981612,152836737,384417149,15621819,549970564,769732620,851829404,
    1695245028,4068814658,8290753036,15010235120,26287338390,45931824198,79246655380,
    133309117152,218452232618,350369794660,551871907788,854198475178,1298757591582,1939968142966,
    2848798148974,4115908156652,5853748818872,8197852746906,11307753727748,15367220502758,
    20582688482038,27178828538252,35391036021624,45455368396242,57596456076554,72013429000338,
    88863748266522,108245424899116,130179045908828,154591556125414,181303530099740,
    210021067994694,240333059896030,271714594457144,303537396738188,335087870028752,
    365592451631136,394248924376986,420261560990218,442877750315996,461423890279246,
    475338490652980,484200439785986,487750388189990,485903467720078,478752248214570,
    466559812900218,449743805953732,428853000901958,404538281351480,377520027412722,
    348553925182080,318397238073652,287777545370708,257365754326290,227754765084006,
    199444559159188,172833826654358,148217691562522,125790725164686,105654255678220,
    87826929284358,72257485240594,58838737591060,47421808602246],
   [37829756214638,29869895697588,23344327495512,18058418919608,13827206965206,10479860104760,
    7862443213550,5839275686206,4293174713490,3124853303978,2251711558448,1606228347256,
    1134130981654,792491432088,547867515780,374576079114,253154070190,169035003046,111444985616,
    72505603008,46520671214,29419317912,18327523652,11242568046,6788395514,4033768750,2358646228,
    1357260224,768848156,428969998,235924630,128045952,68681158,36472910,19216766,10068768,
    5258822,2743890,1432712,749380,392692,205990,107992,56454,29344,15124,7702,3860,1892,904,412,
    172,62,18,2]]
private def pvm_r512_s2_c0_16 : List ℤ := pzigCat 66
  [
   [989378,159865416,55324457,88057093,151079999,258864795,139484113,152328530,102509697,
    88689037,105277188,101911421,105176189,75871304,97328271,202395311,74048851,143480759,
    165095341,70649962,92769612,65042539,17414062,116606332,23833500,46906864,142338472,2979734,
    133103229,7021486,135173334,71403158,46364714,90381928,51645690,46290462,150642598,122588846,
    67204623,80395757,120476530,167143822,18836569,122581575,41731815,27330860,30240756,49509966,
    14782058,130189369,187660729,22607045,136687540,67839068,64435391,14987591,109260670,
    95454332,23512325,31628379,2443122,19532628,104472767,43391733,93317245,128822078,83466555,
    214676844,234983479,252013452,364176655,473798462,314450349,499401358,505297027,178629804,
    359923075,94960332,168608526,137832765,366278728,368466381,385308238,205631803,24912685,
    46303464,305938629,444888880,272351697,64953230,34440393,193279499,474667176,259316685,
    55467670,1180866,216283055,440662642,205180793,23213431,81614582,390432807,236336390,
    96248637,73428399,391811280,200425625,145578704,148695612,288678221,216005432,180351763,
    277815535,249830778,188482657,52562298,252235278,253532997,200543246,175026216,222305115,
    238330070,43737547,266491365,199258920,137670557,38851599,473784370],
   [1160716,25729083,181787848,215509173,185922812,502007816,65343491,38196388,132500914,
    236514811,148327104,209075992,312817041,30712224,239313632,97964107,178035010,148676260,
    302664171,92773526,265291644,220387247,47700055,101431742,189104837,188342582,388399120,
    194371007,161850517,127761382,184828293,63204289,236438362,199265355,227528645,283296132,
    94270150,85464109,255651056,18810690,299451051,130397080,187272198,165663991,158231836,
    358679430,82483315,7549799,293645388,52845141,75475297,411993470,208881400,165114641,
    135807696,136700200,262415071,9819821,240351764,240461653,333461935,125421596,31950988,
    131821513,314059438,327544358,240947221,174022059,180602076,77850415,125372503,385037244,
    313725950,168562177,18996982,248938220,185784037,293738027,159543062,61472064,330352133,
    39008351,223838850,230160485,389726337,58327646,30572158,332976719,35562847,338970034,
    40423555,296386859,125283482,207426290,232035401,134988503,299203948,53128112,355420663,
    38049809,258799856,131513975,297114361,161497424,222216162,253477359,206179915,257134644,
    102255060,343234659,114612793,279952176,12771243,335548143,25230698,276789262,167402841,
    410743809,36258286,243962934,158403257,238030621,221957836,236589352,320374761,422948145,
    37084644,87062446],
   [304765157,194843905,356962610,358767154,145951049,181392183,227789786,157096816,336995195,
    309730405,217577680,298081122,112975925,106874353,395419150,484572388,1662348,165561859,
    238807736,380602166,73390077,325886095,68393906,385662156,67711210,272072645,12330506,
    425056884,232771688,217035699,121758113,354861318,383559120,74970541,220632889,179751698,
    390886748,20846505,447671579,271580247,111102070,16287267,479427911,504632107,2365556,
    306282614,37435806,230685001,69675984,580950724,589061524,146617942,22163735,344744806,
    653298418,383247022,112689711,148228405,265417902,450237242,79287722,344845633,235938701,
    223008250,352919766,44260107,412210091,235996605,237559548,354810384,30735393,343885353,
    29777067,799104206,1716776606,2917564642,5612634588,11587564212,22820788278,42100319332,
    74475862070,128602132420,217530015998,359594775178,580354972114,915707365338,1415367088400,
    2145926036242,3193530034384,4666746602278,6699737385076,9454888068252,13123614249430,
    17924543447228,24099055683790,31904403697210,41604205760596,53455685154390,67693306814246,
    84509397960010,104033259173762,126310580260876,151284715302970,178781081162298,
    208496036122946,239991935610088,272700132481078,305933117476022,338905902758128,
    370765622753000,400627577061528,427615609526330,450904538954360,469762083734180,
    483587383675096,491943093645156,494578375129488,491440973276000,482677700601490,
    468623723751170,449781855298578,426793582384024,400403938788410,371422644827330,
    340684181311654,309009515756144,277171953103612,245869030745964],
   [215701628460444,187160689375306,160621295794972,136343380939922,114478070199326,
    95078478625538,78113698063062,63484673708696,51040710107624,40595478334922,31941617778048,
    24863308724126,19146488947842,14586651480068,10994359963752,8198742815188,6049286994254,
    4416265541638,3190119557916,2280088879176,1612353396624,1127910905184,780377809686,
    533856726382,360972150008,241135068836,159062837814,103553919194,66498984018,42099674646,
    26262471026,16135632840,9760269396,5810781298,3404268030,1962482216,1113327510,621719622,
    341922868,185323958,99088708,52329220,27336872,14151446,7273396,3718918,1895146,963996,
    489932,248858,126274,63920,32220,16134,7994,3908,1870,866,384,156,56,14,2]]
private def pvm_r512_s2_c0_17 : List ℤ := pzigCat 59
  [
   [86787699,100319706,102590190,26962690,38359799,73161208,188300449,342158289,48313859,
    16171956,152559031,28600061,92963848,77785849,109877405,53030580,6618736,110146223,23233227,
    16651401,209141929,225368179,42611691,12958227,79871919,4805984,78784742,20916971,49017261,
    109269838,173857290,44097010,38858199,4515437,6467463,17944293,74674364,137520454,30281686,
    55143691,74733946,223285056,138092168,42791699,50818737,70047662,110194124,68203328,40934988,
    9457868,89682759,87157437,31935776,189355302,18389584,80815623,250727753,92354970,122257451,
    200180608,334022779,341599910,320760099,485669058,426117857,443811884,308030719,281490308,
    100533897,107899625,144547836,412365771,348388198,295869325,280712546,18679443,219550757,
    234459536,343773475,410939040,23711110,29425263,175703138,485993199,196565830,105065141,
    119689901,265079162,292273581,324738136,126160230,246860401,198705320,296765411,105738604,
    265197060,355091865,119098182,84273853,119017839,393331110,207429109,63823467,182209724,
    272782237,213558380,141474936,221662215,249143026,132397023,281550531,206373182,179891093,
    42858707,287809180,186408857,114425104,304848750,216132897,58590014,49206652,348462675,
    106052340,58372474,276954653,193345946,82758600,198505899],
   [250589378,89423772,127041689,281625794,52902011,385443055,95411964,62625144,10726905,
    387195468,20274288,313063463,200734400,199985618,2978005,331169410,116597510,185178199,
    274407928,217401214,248502861,14148784,93967742,174395969,179930148,259636612,245619667,
    35478411,318538812,31865099,48203493,148225466,245109161,214734769,343983174,161850024,
    150153999,151002868,61687406,243956155,111643148,188135650,306797669,167343305,190137676,
    91283489,80616437,329552564,75603066,228283939,131551602,124745892,270269223,20616030,
    354699360,1852374,41909345,302150854,34721586,226771305,240207016,378156110,54140079,
    39734778,311295252,47449597,171456843,279231766,166302828,350148401,187347351,85502234,
    206429783,148997815,386603662,262365024,225969283,43172051,182525884,182384567,194116235,
    332447942,286772222,133883125,79901612,352794726,70642089,302042007,110213254,140547006,
    285368269,135457583,268879480,38087263,430089275,106359545,120694870,257596599,286900221,
    214021752,186604554,284053795,148229349,275345498,47130294,290263831,44132314,307614458,
    114227023,331797217,104441232,229300584,224712393,259075311,209939588,176665378,277046965,
    167389515,271231862,87661364,354342217,137613305,285875622,54103256,316703129,46115521,
    270193354,87480295],
   [444119119,87501129,294078592,10669174,273042651,56256536,295975528,143004763,515605765,
    177885123,182577140,73400559,306521143,88739898,453461268,122778066,293273007,74872043,
    262335370,1379371,395711613,152542143,338796630,256298826,138576427,20133741,451350618,
    425973828,70719397,184365697,224103682,352661240,75038871,313743421,64063700,406923838,
    135103686,252218587,65515073,376058134,312755886,138819931,192337665,260921680,469419344,
    86625970,263882851,45280413,303897684,110432658,415206663,515771897,103349029,120922890,
    193121527,490682499,206759539,333721404,420300026,50764594,87266735,309795238,697034048,
    515428708,35966064,51103865,338700524,573140512,245692592,229156525,221270331,209501876,
    408156058,60290456,369655029,297301209,168114770,380129510,42565998,394819621,351652909,
    107792588,377130122,142732528,132217667,356846260,2070792240,5217152830,10719323480,
    21202156102,41337100750,77965849936,141019881436,245682795346,415247267376,683886472892,
    1099285555168,1725805167880,2648657336154,3978632783964,5856215829286,8454102541706,
    11977827968686,16664529178264,22779454607750,30609195759858,40450562728354,52594775465066,
    67307666128560,84807195611684,105239620153254,128655542665738,154987345716668,
    184030136255110,215428841836722,248673968444810,283107688227864,317940763571172,
    352279805876132,385163681613644,415607329700410,442650586613024,465408812006850,
    483121448510478,495194494738518,501233379959346,501063754982798,494738928997928],
   [482533804506562,464926096424168,442566426248602,416239632022000,386820300471802,
    355225970478314,322371522557168,289127898153728,256287566942904,224538260816274,
    194445609699344,166444569933692,140838965384298,117808040867990,97418623633300,
    79641291855796,64368875409014,51435683454480,40636064644030,31741225865494,24513606920462,
    18718468610126,14132652053840,10550684135214,7788538214330,5685426404724,4104020159896,
    2929486855676,2067702519524,1442960634720,995447298658,678697101222,457186033114,
    304162315544,199767667530,129463221092,82747199448,52134954980,32364150930,19786351074,
    11908697116,7053782918,4110930706,2357030536,1329527462,737900586,403086480,216824774,
    114928616,60082682,31014404,15829080,7999996,4010306,1997256,989724,488576,240440,117972,
    57680,28064,13556,6480,3048,1404,618,260,100,32,6]]
private def pvm_r512_s2_c0_18 : List ℤ := pzigCat 53
  [
   [106294123,20013217,41167058,153088068,4396468,42921241,152191550,83537874,233301619,
    253772651,51114167,76599469,185757269,55581041,74793824,36482591,112196827,6787422,39128352,
    81708241,69204037,66722150,25348060,154016849,180253261,88446369,104833357,155469503,
    56572987,64194662,9722538,92338579,36903251,85675910,100216296,63932672,81080472,65215742,
    48570735,97237093,28517456,152677082,69718710,64763851,49780881,139214488,157692020,
    142011916,35834341,118489686,105213053,190817886,159413519,449050668,249667087,332841120,
    592284295,408491402,263472969,435981554,194916819,70338167,86595788,300426419,326685644,
    430355761,231349604,107126613,62237725,279347380,324066957,353471220,148240491,33611472,
    275782740,301461937,267145362,249928253,157529461,236184196,271941029,304983906,29646315,
    283854515,208556348,258067625,205945848,317840250,251145393,206137470,114359949,189465081,
    247318366,348544297,80706993,259888244,133548135,273259928,32822402,345372211,255639668,
    16055264,118146473,227163636,273493821,119631141,277751026,183744157,53486090,198697252,
    289234135,63387488,135944440,219760783,238129958,164238010,259303539,119021572,13492619,
    288768993,158210448,23717979,255077039,257123758,122851744,113268581,270182694,17241524],
   [245851099,157267500,55656717,300123571,162525946,46363598,237834085,134960698,52868010,
    144313837,340341266,249488202,288246711,87518985,1946145,200847081,223458666,319081196,
    228219873,84512773,242377016,40361843,58508518,324907348,44507617,30278381,433197986,
    142772008,200166823,105684450,46690206,176226669,196815362,197781178,283042235,42699141,
    338274628,29170632,27128727,198854518,160225577,310862973,210215064,211972330,175809409,
    64684664,224199396,146190021,35915165,292115230,85447431,324757577,80553404,59153570,
    263570283,63261982,318796044,74853263,102006077,240491398,33970927,317975321,127933426,
    311767300,77494943,1099730,296256684,35228109,212264889,281827524,362323404,86550401,
    12769558,325577374,25519790,129966805,306704494,275113280,294846415,273900451,78783880,
    130789221,261360615,236481856,367238254,138843347,181236551,196998768,10554762,303892261,
    75062276,388524108,18770298,110179673,308826630,254896678,255316913,171245317,234672982,
    20566790,295209287,38661714,256947322,211819095,431241255,2623882,107204850,296631817,
    229744281,231125132,104291048,327614001,114414219,304135440,55333316,293982301,15280416,
    299828008,79515463,337196383,61229270,262695008,163945035,319404313,133041522,265849986,
    178712587,271572323],
   [161974388,194544578,265968357,272863261,220764028,252725902,221787967,269765965,137434088,
    105970880,343060301,293636271,236572462,300337602,159950361,246648597,126104774,104303908,
    388594237,460012883,52210864,266677158,87927377,210439639,208424108,390549990,52840799,
    374074435,59199371,250799228,28126731,346306723,44930077,426029242,312975542,99153895,
    24701941,406380794,393716802,95275909,258988365,138033070,370015102,25095604,289823653,
    14476473,395806674,252461154,195087867,186735903,271029230,428198994,46434694,218029287,
    85331326,454464940,254319878,255675733,345222699,22214820,154530104,246545219,604037481,
    369122001,127364864,193459828,163472153,268685313,170854908,612952804,493040878,60960158,
    1773907,408073816,673449066,369250956,117458255,145913491,265793720,477391690,138467446,
    321751353,298017723,153409690,397488352,89070812,365125005,361335555,92586412,389039356,
    117701568,406245419,550509923,146623587,395403652,839444452,1914291992,5393086080,
    13759727832,30470124078,61364347290,116790576330,213682219412,377522684030,644954608558,
    1067740865100,1717894251680,2693010870656,4120903264714,6163260331256,9018373889542,
    12922500335480,18148621097670,25001069897630,33805049190844,44891010578520,58574523127964,
    75132378849660,94775700117284,117621254230340,143663103866396,172747629290044,
    204555253438654,238591704857704,274190687201286,310528850156628,346653165216952,
    381520031944804],
   [414044419717462,443156075864314,467858625427658,487286690446518,500756219985840,
    507803968969092,508213194330416,502023859145728,489526823082848,471242673692304,
    447887052084098,420325472001656,389521528799738,356482833672324,322208885768216,
    287644472296460,253641251384060,220929140471694,190098163708180,161590576907804,
    135702397465634,112592913521688,92300343801280,74761597891310,59834072968794,47317614011754,
    36975117059962,28550696181926,21784784759742,16425936881670,12239399971870,9012738528096,
    6558913283920,4717279984060,3352985655176,2355221138168,1634745535802,1121037738274,
    759358815380,507933904024,335390388682,218526627728,140436012172,88976017716,55550171900,
    34160085320,20681873936,12323524886,7224670470,4166167374,2362807732,1317882588,722966648,
    390166014,207221006,108369956,55846034,28384700,14245116,7067878,3471810,1690760,817436,
    392800,187744,89276,42224,19842,9234,4242,1912,836,346,130,42,10]]
private def pvm_r512_s2_c0_19 : List ℤ := pzigCat 47
  [
   [83988289,45944733,88320973,12696500,155863274,69077852,85821995,14203702,208527812,122380134,
    140195399,194816187,68060591,78097433,201794441,161576567,2361130,16466046,92485391,75223595,
    40318892,20147800,102089153,86207935,52899030,74537928,46415017,103717913,57590459,76870215,
    182453715,191371097,61124019,26114122,29036541,81715527,46254533,19296864,13783315,39467044,
    81186858,225320766,31557123,23279130,248629667,295264826,157893075,379572920,467127437,
    409327596,373478357,489529020,208025297,282632466,107899180,146162807,238178954,371725325,
    506280092,32203845,128915150,44632668,401390519,357864844,196467123,183654972,113600928,
    284245885,327690592,274712147,4327436,106072004,363159969,260750124,151066103,88606565,
    291590996,297094503,166766816,105870766,191815119,385148250,86147537,114384055,178458036,
    382997349,51833950,219730132,195386671,216614676,120260433,345772391,277020188,19671711,
    23139493,302018018,191409897,52734860,283838604,321150345,102966493,29390710,256401545,
    253695720,191057980,278117005,132380812,71497840,173040725,265298512,18439920,280164489,
    159613810,41566339,218835649,256009642,27643602,198069687,178451316,79680657,223206257,
    274278470,77138624,161625449,217103968,11033856,228580775,155537468],
   [36751231,329690555,110854970,99466676,179415047,200989716,210821308,154007861,123178700,
    143023138,310600175,54803175,215182524,165630023,118188205,92728600,227721223,55778553,
    466368738,152442074,191343343,43836806,90255819,228226291,234388370,211068984,258559039,
    17434969,252316964,77507301,20998021,248738918,52834929,55914871,440895860,260255836,
    172232269,80217468,181463036,128995081,67354218,261444022,196644931,248102727,275020918,
    210097566,90146589,151464694,130867078,291737955,86507105,292225480,37655369,209033617,
    197701036,154398768,175229829,103539486,290118246,161016459,232625797,149932590,33884721,
    329363469,71338032,306496906,75660855,79382671,240769088,39539507,335633285,99808858,
    338142562,65092357,92448907,256961526,50946500,226747067,183149726,422149606,28403187,
    141375583,273370844,215213850,100564145,182536508,426824904,72507771,398793099,30839993,
    70265910,262320997,79641563,373152204,135126220,278022737,13627553,233783084,144228407,
    271023087,217938766,330654240,77177569,22387649,367269474,141189384,315474343,83294201,
    294454562,11742382,271792453,61145836,212869228,257379185,423460091,34871696,147546670,
    276360607,277158899,176344240,131794876,296214299,165754711,287850828,139387700,287258371,
    103593613,292788202],
   [61067322,333880225,93373283,268256320,1670193,341537733,31950405,324543900,14577012,
    353863187,76509653,257815598,20389047,319867569,6967092,345392894,11622272,404308011,
    174427769,191539484,16262117,326021261,35969049,382150374,150763050,343695003,275646335,
    98576180,14566679,415243671,289090799,243837358,319873860,103327523,201852863,189105008,
    293906796,156981383,414645857,50434955,288924300,49532260,254508693,16597880,474097146,
    375721404,81243919,113450119,292038556,378461926,54491765,300898143,43582862,395585322,
    171430494,239916343,142387477,304806014,363288844,55495109,246914555,128751092,492199480,
    279683822,162793589,151476819,239399048,304787040,165445119,546570851,341691741,66324176,
    24310350,383179613,471007211,4220179,439591376,326979564,52541803,33623407,435525904,
    718512598,420156416,42457435,39413497,379404100,566911460,199155550,270205245,241979141,
    204100950,424888982,92129334,367795837,351765089,115655704,417827792,155344542,341932417,
    455129711,83757119,216285928,66935123,727998999,964625307,8374836,2854815014,9051791350,
    22392911162,50303666468,104961312638,205078631706,379181514126,670334441762,1141518829298,
    1880973386440,3007449039794,4675588403658,7081046762330,10464014312600,15109352152096,
    21341961238872,29516801317014,40003476554450,53165336597452,69333082401318,88773479777534,
    111655005531786],
   [138013527529096,167721806310978,200466493069352,235735681509122,272819363624934,
    310824461995226,348705235294664,385308510521330,419431422131522,449887543108744,
    475576004644614,495547739322348,509063317039312,515637712877292,515068497632202,
    507445273415030,493139703341664,472777188150330,447192961216088,417376818559006,
    384411586750274,349410615086286,313459110797240,277563213832758,242609565085258,
    209336940836626,178320407919364,149967445662268,124524619589540,102092730522478,
    82647960248630,66066428141440,52149751436648,40649602759756,31289785549622,23784900439452,
    17855174225416,13237422861210,9692408552978,7009037697482,5005949374662,3531081829098,
    2459791955256,1692052412764,1149173741206,770405987484,509677198770,332634803906,
    214077985528,135808825902,84888094806,52256200038,31667658930,18884624170,11077990224,
    6390645924,3624609526,2020915248,1107604592,596757432,316131010,164714262,84448752,42630948,
    21206494,10404846,5040762,2414146,1144360,537522,250434,115802,53152,24208,10916,4858,2120,
    894,362,134,42,10]]
private def pvm_r512_s2_c0_20 : List ℤ := pzigCat 41
  [
   [65938675,27131701,44847801,113278445,76383887,83160714,158040654,30490304,106089979,22113037,
    178099152,199782748,10680616,123848115,73272675,21908201,119363493,221018947,153466139,
    21370263,22563579,110041053,91009423,26601134,49348976,61195309,121950949,33725099,57029026,
    28796698,50359889,18485451,5337752,10525421,205414299,135755297,211118017,99167624,249468371,
    175108792,357188961,378922146,476792767,341965854,434481607,477524030,20667721,114242818,
    60156058,334778027,411423180,266235955,292997428,90134479,133537409,295417160,356546683,
    299293194,6270102,75488446,411938832,358080273,138893290,8031961,37619641,512008678,
    185082063,59061988,98730004,312948449,304350824,55274895,110420577,328801946,236586761,
    61588212,166354168,332678415,155922022,46280731,283245515,263720754,125618863,124244845,
    262686556,240071559,114373,281972496,152184003,213488198,185691734,364859069,28198394,
    30088488,179826379,310958444,15227384,342123243,130559000,39777877,164371867,252176420,
    76393817,131243745,393408248,59731424,162398985,110995664,240559223,218722507,280247802,
    38153213,164858961,214427832,71699801,137211997,290184174,5680400,166283543,199053214,
    75283565,271371207,187599942,74714778,173221485,167318244,19674260,294547533],
   [114270212,161955646,197455367,93246552,218866836,156278045,33431540,200868512,240672919,
    170140381,170424978,145627341,193023729,232578996,83384004,73890761,265063174,74433958,
    318499547,49346552,244502156,141207135,98349697,22766704,320520471,144015357,417542590,
    197780586,155423007,85450128,37090000,230638169,90689584,227478110,221678227,138295033,
    297226198,58303680,182010709,119917658,71708096,164314543,230102140,445049320,41614891,
    114261179,281049876,133290078,93261647,192687528,122294878,323908301,90165903,349142838,
    80458484,113302195,211408186,116169218,258597435,801172,266702652,122134559,223931763,
    213387304,154922246,188186031,85388842,330368944,76908633,219142755,135369556,3003180,
    368846913,43564077,340032320,20302216,167613463,163517424,88745128,306911321,55262915,
    370237620,72575832,234874127,100142490,224958092,136918945,39713331,398697086,186926774,
    250125773,19414874,378670522,113057498,19268835,354326096,293499920,285928539,315174771,
    118648236,26034358,280801235,27714262,362224958,2732076,287763273,63824492,206023486,
    211849653,240867419,276665492,333676648,87114075,30705103,331537430,112376626,305663731,
    55457009,345829144,72143838,291354593,27159269,204680888,182254583,423931261,18646933,
    200002756,203415921],
   [367140163,68077662,224218108,183979561,271064725,175404674,257017574,185016037,245238279,
    195507430,228616418,238605713,293341141,156261360,215395036,204423075,233219937,199101234,
    216607952,258519103,330084355,138254470,270865630,128865693,241257271,144029340,221039576,
    250496907,442747063,4681909,286955608,18205499,246651653,75800598,313206416,75261881,
    492233991,268163621,141730214,16735572,321938339,138588203,339283026,311134264,162217161,
    270258291,110708708,229246002,175729989,400081979,14944155,378142144,188723968,159119403,
    9961260,443279438,397843474,79932457,225682137,159293252,390554150,61380644,282405559,
    64187523,361895986,297163654,153630279,255198119,165994496,450438296,171959600,188802065,
    27490699,413204990,421511026,69826219,381513407,137009753,174567966,26415485,507873401,
    571564661,104270721,255234378,66967936,271363067,131669203,407331546,667573362,349757286,
    42582367,70252822,521796064,644819942,218092618,221445997,122290203,326747758,463140112,
    56014952,384206407,294426617,191345600,423049334,89592146,379668465,376791535,98906094,
    432416794,151192546,519399897,983821229,1038804777,1062553825,1268234065,652572815,
    3618808314,16539457246,46285976560,106756497684,221532905568,428576854952,785278889402,
    1374188685142,2309885633104,3746667259740,5885674321096,8979611900696],
   [13333572193846,19301042336326,27274351565220,37668586298972,50898004946736,67344780658042,
    87321409110346,111029686261282,138520148315506,169656134808654,204086500558360,
    241230777201728,280280215201714,320217260960046,359854365242542,397890720538512,
    432983125367178,463825283156424,489228807275456,508199011155658,519999013958180,
    524196632862056,520689944450194,509709303435184,491795907567268,467759393700718,
    438619021231094,405534376920936,369732047990810,332434415690126,294795827527612,
    257850153874780,222472315728378,189354913855300,158999693661754,131722347643912,
    107668200343746,86835734336428,69104741575362,54266090863554,42050593239182,32155093509370,
    24264593255104,18069825301404,13280200279620,9632416656732,6895273194744,4871363757116,
    3396387163062,2336787141600,1586366720296,1062415349128,701763531862,457055109680,
    293414696552,185595522102,115624566980,70916662412,42803655288,25414023288,14837628360,
    8515521578,4802805396,2661497666,1448934992,774901500,407141622,210194250,106659706,53219310,
    26125954,12627404,6013910,2824934,1310108,600474,272244,122190,54306,23888,10382,4444,1858,
    752,290,100,28,4]]
private def pvm_r512_s2_c0_21 : List ℤ := pzigCat 36
  [
   [47970345,43955179,10380695,13480713,80921171,136598721,78623765,72231986,159570598,74968046,
    81972413,106176909,48290588,196573124,163118202,11286912,61422123,8378011,18229910,82019325,
    198741139,179592609,69629597,29328853,107499361,134656965,69962069,69455140,10947255,
    13351349,200703551,106247656,163914121,255547042,377473281,374778518,373001683,487841308,
    466887279,154738420,301261359,105757995,95934194,445652861,288445378,317853125,183937304,
    41567847,391221877,245135016,250625581,337493876,158990186,245190231,308314120,243758945,
    112179214,200144316,289486781,331698534,63130309,163323913,211202924,313165739,205746562,
    358593190,153018295,249458394,111942527,218966841,394871274,29601321,70441856,324006320,
    252364923,67353068,167070750,276202761,198771450,108083182,228773217,265361484,16476378,
    203743787,243274650,130166963,228793701,213683134,165148999,133642817,265883848,175967843,
    142021843,190507984,174386353,56693114,421476472,93870917,112280877,109309990,247573235,
    3720694,323782848,174282707,136560747,179555366,165806577,82097307,179034126,234601063,
    125594453,360442892,72539528,29628737,220123592,160241343,263574789,180495104,21179313,
    214245303,173831654,27302300,243642607,151730908,162582100,153470529,136127534,162919076],
   [282046743,69355925,208419026,120036673,51034105,223822704,127008965,198862727,200178676,
    193065,236937375,153796858,164022658,150560773,109500390,206844286,203936073,86538893,
    193398164,187226753,301599759,135861708,96283832,75455913,234476178,148019982,298720467,
    28716715,354418620,19860812,159578607,27584046,218156685,339528051,196810548,312572922,
    138761749,47773671,236065894,49752087,138058033,184452606,1696825,294388407,110913952,
    331131082,120913311,192076005,141924300,1893423,118084551,299765384,311528520,165672971,
    33202877,388399074,157269126,83662173,186558860,107296002,297963487,61595087,341680674,
    51095512,168049585,198827264,212389418,196834595,60921783,263325238,46370911,276884611,
    123284428,221685940,172528871,56568797,365508206,135225652,233454991,7682552,119110078,
    283190291,243144809,283330402,226595024,211725629,68553055,206128012,94306489,237790029,
    213957674,299895300,190505041,208962869,237238958,169234342,148539547,103065028,362246302,
    38296641,282436233,183950664,436913878,82766950,24022616,363139498,180956008,341760393,
    230008637,190325668,17047386,282867375,47304210,355498268,17707485,308021713,31374872,
    192398950,188602203,225293713,288272242,379750434,80529061,131036899,259658508,187103508,
    227450743,93424313],
   [338294222,163945948,299587331,168060037,200475910,18722797,402580623,169794279,198355110,
    50506787,394337661,104726011,266731068,4959840,329041827,36839431,316613244,42927164,
    301004367,39815673,276950196,16276909,364723651,76751657,315778424,83258450,306496035,
    119825897,231593114,25823606,345692639,127322679,331797664,209538342,261107423,249999667,
    125296414,75298286,333107761,291746487,219138524,354118608,77589443,294767105,18206168,
    170138744,224358183,508019945,158547183,265187918,108640932,241699701,85813861,326762628,
    243600592,248242347,357946661,47944938,239451692,94393119,314504331,47725612,467625026,
    307352736,115765603,77926223,335259984,391430734,46134453,283739685,54096866,406463486,
    196144426,234544797,189498823,254583992,382506314,2566799,264501705,49626170,487883222,
    397014628,68746513,203990317,147360592,357903364,6561011,509886595,492956987,51439029,
    124500760,211585461,501382381,218223255,347734822,502032850,140241452,116732137,175890578,
    650513722,651666230,162469208,169840879,70248048,500952820,476346234,28377767,383521119,
    152171059,328982876,399776158,54042707,455036767,285950407,246035342,477463704,126532578,
    370725275,443601721,158189437,231135573,1267316455,3082279541,4724398787,4751855853,
    689672035,12942542456,47718096232],
   [124918100158,279730136916,566816561138,1067908197190,1901072630274,3230282954680,
    5273628950126,8308856301934,12675155140350,18769781181292,27037523507434,37951034034870,
    51981060421180,69557367266658,91022846100520,116584491873324,146265608848666,179864132361402,
    216922413608932,256713862887720,298250960105312,340317103324452,381521903760540,
    420376536397116,455383259635206,485131536910308,508392335269670,524202068556518,
    531928324022900,531311065185674,522475443191092,505915419800570,482450606108566,
    453161476725162,419309994643658,382253507249684,343359625537514,303928888354398,
    265130574006770,227955252624738,193185750646778,161386307258946,132908040393828,
    107907591460516,86375104928496,68167543783674,53043666158048,40697644238560,30789124878490,
    22968364848032,16895820311910,12256175741440,8767244822306,6184470096650,4301905175032,
    2950604600732,1995296223226,1330095936554,873872325074,565704759410,360723728584,
    226490908752,139975655096,85114981620,50901988154,29927156584,17291549122,9814999842,
    5471473936,2994813998,1609196956,848745376,439406336,223310164,111424634,54602160,26288782,
    12442020,5792258,2654376,1198356,533432,234304,101606,43510,18386,7648,3122,1238,472,168,48,
    8]]
private theorem dk_r512_s2_c0_0 :
    bSlideChk 8 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 pvm_r512_s2_c0_1 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_1 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_1 pvm_r512_s2_c0_2 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_2 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_2 pvm_r512_s2_c0_3 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_3 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_3 pvm_r512_s2_c0_4 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_4 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_4 pvm_r512_s2_c0_5 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_5 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_5 pvm_r512_s2_c0_6 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_6 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_6 pvm_r512_s2_c0_7 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_7 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_7 pvm_r512_s2_c0_8 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_8 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_8 pvm_r512_s2_c0_9 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_9 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_9 pvm_r512_s2_c0_10 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_10 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_10 pvm_r512_s2_c0_11 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_11 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_11 pvm_r512_s2_c0_12 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_12 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_12 pvm_r512_s2_c0_13 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_13 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_13 pvm_r512_s2_c0_14 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_14 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_14 pvm_r512_s2_c0_15 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_15 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_15 pvm_r512_s2_c0_16 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_16 :
    bSlideChk 8 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_16 pvm_r512_s2_c0_17 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_17 :
    bSlideChk 7 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_17 pvm_r512_s2_c0_18 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_18 :
    bSlideChk 7 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_18 pvm_r512_s2_c0_19 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_19 :
    bSlideChk 7 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_19 pvm_r512_s2_c0_20 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_20 :
    bSlideChk 7 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_20 pvm_r512_s2_c0_21 = true := by
  decide +kernel
private theorem dk_r512_s2_c0_21 :
    bSlideChk 7 513 phbv_r512_s2_c0
      pvm_r512_s2_c0_21 rkmVoHiHiB_m256_r512_s2_c0 = true := by
  decide +kernel
private def pwalks_96 : List RkmSegWalk := [
  ⟨phb_96_0, pvi_96_0, pvo_96_0⟩,
  ⟨phb_96_1, pvi_96_1, pvo_96_1⟩,
  ⟨phb_96_2, pvi_96_2, pvo_96_2⟩,
  ⟨phb_96_3, pvi_96_3, pvo_96_3⟩
  ]
private theorem ptail_96 : rkmAllTrueF [
    muxIntListEq phb_96_1 phbv_r96_s1,
    bSlideChk 16 97 phbv_r96_s1
      pvi_96_1 pvm_r96_s1_1,
    bSlideChk 15 97 phbv_r96_s1
      pvm_r96_s1_1 pvo_96_1,
    bSlideChk 3 97 phb_96_2
      pvi_96_2 pvo_96_2,
    bSlideChk 2 97 phb_96_3
      pvi_96_3 pvo_96_3,
    muxIntListEq rkmHbHiHiB_m256_r512_s2_c0 phbv_r512_s2_c0,
    rkmCheckRowFromWalks 256 32 96 [1, 1, 1, 1]
      [16164539, 15975141, 1085917, 793973]
      [31, 31, 3, 2] rkmMasksHiHiB_m256_r96 pwalks_96 rkmRowHiHiB_m256_r96
  ] = true := by
  decide +kernel
private theorem pwalk_96_0 :
    muxFastIterFullT16 31 97
      phb_96_0 pvi_96_0 = pvo_96_0 :=
  bSlideChk_sound dk_r96_s0_0
private theorem pseg_96_0 :
    muxFastIterFullT16 31 (Nat.add (highdNatMin (Nat.mul 1 256) 96) 1)
      phb_96_0 pvi_96_0 = pvo_96_0 := by
  rw [pdim_96_l1]; exact pwalk_96_0
private theorem pw_r96_s1_1 :
    muxFastIterFullT16 31 97 phbv_r96_s1
      pvi_96_1 = pvo_96_1 :=
  (muxFastIterFullT16_add 16 15 97
    phbv_r96_s1 pvi_96_1).trans
    ((congrArg (muxFastIterFullT16 15 97 phbv_r96_s1)
      (bSlideChk_sound (rkmHd (rkmTl ptail_96)))).trans
      (bSlideChk_sound (rkmHd (rkmT2 ptail_96))))
private theorem pwalk_96_1 :
    muxFastIterFullT16 31 97
      phb_96_1 pvi_96_1 = pvo_96_1 :=
  (congrArg (fun h ↦ muxFastIterFullT16 31 97 h pvi_96_1)
    (muxIntListEq_eq_true.mp (rkmHd ptail_96))).trans pw_r96_s1_1
private theorem pseg_96_1 :
    muxFastIterFullT16 31 (Nat.add (highdNatMin (Nat.mul 1 256) 96) 1)
      phb_96_1 pvi_96_1 = pvo_96_1 := by
  rw [pdim_96_l1]; exact pwalk_96_1
private theorem pwalk_96_2 :
    muxFastIterFullT16 3 97
      phb_96_2 pvi_96_2 = pvo_96_2 :=
  bSlideChk_sound (rkmHd (rkmTl (rkmT2 ptail_96)))
private theorem pseg_96_2 :
    muxFastIterFullT16 3 (Nat.add (highdNatMin (Nat.mul 1 256) 96) 1)
      phb_96_2 pvi_96_2 = pvo_96_2 := by
  rw [pdim_96_l1]; exact pwalk_96_2
private theorem pwalk_96_3 :
    muxFastIterFullT16 2 97
      phb_96_3 pvi_96_3 = pvo_96_3 :=
  bSlideChk_sound (rkmHd (rkmT4 ptail_96))
private theorem pseg_96_3 :
    muxFastIterFullT16 2 (Nat.add (highdNatMin (Nat.mul 1 256) 96) 1)
      phb_96_3 pvi_96_3 = pvo_96_3 := by
  rw [pdim_96_l1]; exact pwalk_96_3
private theorem pwalks_snd_96 :
    RkmSegWalksSound 256 96 [1, 1, 1, 1]
      [31, 31, 3, 2] pwalks_96 := by
  dsimp only [RkmSegWalksSound, pwalks_96]
  exact ⟨pseg_96_0, ⟨pseg_96_1, ⟨pseg_96_2, ⟨pseg_96_3, trivial⟩⟩⟩⟩
/-- Trajectory row certificate `(m = 256, r = 96)` (`FindAllJohnsonRampKickMuxHi256T6`). -/
theorem rkmTrajHiHiB_m256_r96 :
    rkmLo12EqHi 256 32 96 [1, 1, 1, 1]
      [16164539, 15975141, 1085917, 793973]
      [31, 31, 3, 2] rkmMasksHiHiB_m256_r96 rkmRowHiHiB_m256_r96 :=
  rkmCheckRowFromWalks_sound pwalks_snd_96
    (rkmHd (rkmT2 (rkmT4 ptail_96)))
private theorem pw_r512_s2_c0_1 :
    muxFastIterFullT16 16 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_2 :=
  (muxFastIterFullT16_add 8 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      (bSlideChk_sound dk_r512_s2_c0_0)).trans
      (bSlideChk_sound dk_r512_s2_c0_1))
private theorem pw_r512_s2_c0_2 :
    muxFastIterFullT16 24 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_3 :=
  (muxFastIterFullT16_add 16 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_1).trans
      (bSlideChk_sound dk_r512_s2_c0_2))
private theorem pw_r512_s2_c0_3 :
    muxFastIterFullT16 32 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_4 :=
  (muxFastIterFullT16_add 24 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_2).trans
      (bSlideChk_sound dk_r512_s2_c0_3))
private theorem pw_r512_s2_c0_4 :
    muxFastIterFullT16 40 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_5 :=
  (muxFastIterFullT16_add 32 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_3).trans
      (bSlideChk_sound dk_r512_s2_c0_4))
private theorem pw_r512_s2_c0_5 :
    muxFastIterFullT16 48 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_6 :=
  (muxFastIterFullT16_add 40 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_4).trans
      (bSlideChk_sound dk_r512_s2_c0_5))
private theorem pw_r512_s2_c0_6 :
    muxFastIterFullT16 56 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_7 :=
  (muxFastIterFullT16_add 48 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_5).trans
      (bSlideChk_sound dk_r512_s2_c0_6))
private theorem pw_r512_s2_c0_7 :
    muxFastIterFullT16 64 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_8 :=
  (muxFastIterFullT16_add 56 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_6).trans
      (bSlideChk_sound dk_r512_s2_c0_7))
private theorem pw_r512_s2_c0_8 :
    muxFastIterFullT16 72 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_9 :=
  (muxFastIterFullT16_add 64 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_7).trans
      (bSlideChk_sound dk_r512_s2_c0_8))
private theorem pw_r512_s2_c0_9 :
    muxFastIterFullT16 80 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_10 :=
  (muxFastIterFullT16_add 72 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_8).trans
      (bSlideChk_sound dk_r512_s2_c0_9))
private theorem pw_r512_s2_c0_10 :
    muxFastIterFullT16 88 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_11 :=
  (muxFastIterFullT16_add 80 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_9).trans
      (bSlideChk_sound dk_r512_s2_c0_10))
private theorem pw_r512_s2_c0_11 :
    muxFastIterFullT16 96 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_12 :=
  (muxFastIterFullT16_add 88 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_10).trans
      (bSlideChk_sound dk_r512_s2_c0_11))
private theorem pw_r512_s2_c0_12 :
    muxFastIterFullT16 104 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_13 :=
  (muxFastIterFullT16_add 96 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_11).trans
      (bSlideChk_sound dk_r512_s2_c0_12))
private theorem pw_r512_s2_c0_13 :
    muxFastIterFullT16 112 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_14 :=
  (muxFastIterFullT16_add 104 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_12).trans
      (bSlideChk_sound dk_r512_s2_c0_13))
private theorem pw_r512_s2_c0_14 :
    muxFastIterFullT16 120 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_15 :=
  (muxFastIterFullT16_add 112 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_13).trans
      (bSlideChk_sound dk_r512_s2_c0_14))
private theorem pw_r512_s2_c0_15 :
    muxFastIterFullT16 128 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_16 :=
  (muxFastIterFullT16_add 120 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_14).trans
      (bSlideChk_sound dk_r512_s2_c0_15))
private theorem pw_r512_s2_c0_16 :
    muxFastIterFullT16 136 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_17 :=
  (muxFastIterFullT16_add 128 8 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 8 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_15).trans
      (bSlideChk_sound dk_r512_s2_c0_16))
private theorem pw_r512_s2_c0_17 :
    muxFastIterFullT16 143 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_18 :=
  (muxFastIterFullT16_add 136 7 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 7 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_16).trans
      (bSlideChk_sound dk_r512_s2_c0_17))
private theorem pw_r512_s2_c0_18 :
    muxFastIterFullT16 150 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_19 :=
  (muxFastIterFullT16_add 143 7 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 7 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_17).trans
      (bSlideChk_sound dk_r512_s2_c0_18))
private theorem pw_r512_s2_c0_19 :
    muxFastIterFullT16 157 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_20 :=
  (muxFastIterFullT16_add 150 7 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 7 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_18).trans
      (bSlideChk_sound dk_r512_s2_c0_19))
private theorem pw_r512_s2_c0_20 :
    muxFastIterFullT16 164 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = pvm_r512_s2_c0_21 :=
  (muxFastIterFullT16_add 157 7 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 7 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_19).trans
      (bSlideChk_sound dk_r512_s2_c0_20))
private theorem pw_r512_s2_c0_21 :
    muxFastIterFullT16 171 513 phbv_r512_s2_c0
      rkmViHiHiB_m256_r512_s2_c0 = rkmVoHiHiB_m256_r512_s2_c0 :=
  (muxFastIterFullT16_add 164 7 513
    phbv_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0).trans
    ((congrArg (muxFastIterFullT16 7 513 phbv_r512_s2_c0)
      pw_r512_s2_c0_20).trans
      (bSlideChk_sound dk_r512_s2_c0_21))
/-- Certified `T_16` walk chunk `m256_r512_s2_c0`. -/
theorem rkmWalkChkHiHiB_m256_r512_s2_c0 :
    muxFastIterFullT16 171 513
      rkmHbHiHiB_m256_r512_s2_c0 rkmViHiHiB_m256_r512_s2_c0 = rkmVoHiHiB_m256_r512_s2_c0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 171 513 h rkmViHiHiB_m256_r512_s2_c0)
    (muxIntListEq_eq_true.mp (rkmHd (rkmTl (rkmT4 ptail_96))))).trans pw_r512_s2_c0_21
end
end QuantumComputation.Specs.DickeSol
