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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T5

/-
# High-`m` Checkpointed Walk Part `6` (`FindAllJohnsonRampKickMuxHi1024T6`)

Certifies `1` `T_16` checkpoint walk(s) (`44118` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Quantized generator list for `m1024_r512_s1_c0`. -/
def rkmHbHi_m1024_r512_s1_c0 : List ℤ := altBuildHbFrom 1024 512 51956169884 0 512
/-- Part 0 of `rkmViHi_m1024_r512_s1_c0`. -/
def rkmViHi_m1024_r512_s1_c0_p0 : List ℤ := let p := rkmP; let n := rkmN; [
  p 0,p 0,n 2,n 6,n 8,p 0,p 5,n 9,n 11,p 4,p 11,p 2,p 4,n 2,n 3,n 3,n 15,n 2,p 3,n 3,p 1,p 7,n 3,
  n 11,n 5,p 1,p 5,n 0,n 11,n 16,n 10,p 4,p 21,p 14,n 14,n 39,n 7,p 11,n 13,n 21,p 6,p 16,n 15,
  n 22,p 1,p 9,p 21,p 15,n 12,n 20,n 14,p 0,p 9,p 15,p 2,p 1,n 4,n 6,n 10,n 0,p 8,n 6,n 18,n 28,
  p 8,p 32,n 6,n 34,n 11,p 2,n 4,p 4,p 22,p 3,n 4,n 8,n 21,p 2,p 26,p 18,p 6,p 12,p 12,n 9,n 2,
  p 16,p 5,n 21,n 13,p 2,p 15,p 15,p 1,p 6,p 6,n 9,n 22,n 19,p 9,p 32,p 37,p 8,n 7,n 12,n 0,p 16,
  p 27,p 10,n 8,p 5,p 12,p 4,p 9,p 4,p 22,p 43,p 37,p 30,p 11,n 11,n 11,p 11,p 22,p 16,p 3,p 4,p 8,
  p 0,p 20,p 33,p 20,p 6,p 17,p 34,p 33,p 19,p 23,p 33,p 37,p 18,p 23,p 35,p 23,p 28,p 42,p 45,
  p 46,p 49,p 47,p 51,n 52,n 58,n 56,n 61,n 70,n 67,n 73,n 84,n 96,p 128,p 172,p 254,p 410,n 661,
  n 1072,n 1762,p 2944,p 4921,p 8201,p 13631,p 22537,p 37073,p 60696,n 98802,p 159938,p 257452,
  n 412090,p 655903,n 1038048,n 1633526,n 2556102,p 3977149,n 6153355,n 9466843,p 14482835,
  p 22032460,p 33330148,p 50139630,p 75006515,n 111582239,p 165072152,n 242850712,p 355300580,
  p 516948806,p 747994213,p 1076346069,n 1540325392,p 2192217588,p 3102910009,p 4367899884,
  p 6115017474,p 8514276531,p 11790337580,p 16238148714,p 22242410544,p 30301593096,p 41057309082,
  p 55329912579,p 74161238107,p 98865412343,p 131088648436,p 172878859099,p 226765784964,
  p 295852116338,p 383915773978,p 495523097504,p 636152155598,p 812324736080,p 1031744793976,
  p 1303440237492,p 1637903931463,p 2047228717503,p 2545230128566,p 3147549358608,p 3871727996746,
  p 4737245121300,p 5765506652686,p 6979776472961,p 8405038825552,p 10067781997821,
  p 11995694341730,p 14217265369450,p 16761287011614,p 19656253158435,p 22929659295628,
  p 26607208329534,p 30711933459896,p 35263254045394,p 40275985614099,p 45759330255541,
  p 51715878319116,p 58140656341529,p 65020259135446,p 72332105707406,p 80043858882066,
  p 88113046989935,p 96486922595093,p 105102587953327,p 113887409751288,p 122759736846049,
  p 131629924466025,p 140401657021636,p 148973549762874,p 157240997543539,p 165098227478197,
  p 172440501898586,p 179166409295956]
/-- Part 1 of `rkmViHi_m1024_r512_s1_c0`. -/
def rkmViHi_m1024_r512_s1_c0_p1 : List ℤ := let p := rkmP; let n := rkmN; [
  p 185180174390403,p 190393914522899,p 194729768530720,p 198121826312952,p 200517792432608,
  p 201880325189704,p 202188003327872,p 201435885455011,p 199635641792990,p 196815253357327,
  p 193018289387777,p 188302789070955,p 182739787614305,p 176411538909079,p 169409496825500,
  p 161832124214130,p 153782602691946,p 145366517180642,p 136689587009542,p 127855510419850,
  p 118963981866700,p 110108932074243,p 101377029896166,p 92846473251225,p 84586084329511,
  p 76654712464026,p 69100937042595,p 61963053028787,p 55269313401522,p 49038396342570,
  p 43280060418384,p 37995948334557,p 33180499006913,p 28821928531604,p 24903242922008,
  p 21403248942331,p 18297533711485,p 15559388674409,p 13160658750568,p 11072502705039,
  p 9266055815120,p 7712990537795,p 6385974978361,p 5259032424319,p 4307807991843,p 3509750525391,
  p 2844219319766,p 2292526050949,p 1837922579109,p 1465545110606,p 1162324665534,p 916872985424,
  p 719352018762,p 561334018235,p 435658141147,n 336288319587,n 258176102568,n 197131200470,
  n 149701603116,n 113064407484,n 84927881628,n 63444804505,n 47136748791,p 34828702513,
  p 25593243280,p 18703370692,p 13593054491,p 9824554548,p 7061602182,p 5047589778,p 3587988603,
  p 2536296060,p 1782897348,p 1246309071,p 866350508,p 598860030,p 411638605,n 281359197,
  n 191229756,n 129239167,n 86850443,n 58034185,n 38558880,n 25473468,n 16732826,n 10928548,
  n 7096779,n 4582043,n 2941373,p 1877275,p 1191197,p 751459,p 471282,p 293828,p 182104,p 112186,
  p 68689,p 41796,n 25266,p 15167,n 9035,p 5339,n 3121,n 1802,n 1026,n 571,n 308,n 160,n 76,n 33,
  n 12,n 2,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0]
/-- Input orbital vector for `m1024_r512_s1_c0`. -/
def rkmViHi_m1024_r512_s1_c0 : List ℤ :=
  rkmViHi_m1024_r512_s1_c0_p0 ++ (rkmViHi_m1024_r512_s1_c0_p1)
/-- Part 0 of `rkmVoHi_m1024_r512_s1_c0`. -/
def rkmVoHi_m1024_r512_s1_c0_p0 : List ℤ := let p := rkmP; let n := rkmN; [
  p 0,p 0,n 2,n 6,n 8,n 7,n 11,n 16,p 3,n 2,n 11,n 7,p 2,n 4,n 2,p 3,p 1,n 4,n 0,n 4,n 5,n 27,n 10,
  p 2,p 10,p 9,p 16,p 2,n 4,n 14,n 15,n 4,n 8,p 2,p 14,n 0,n 4,n 28,n 31,n 15,n 3,p 17,p 13,p 15,
  p 2,n 5,n 55,n 14,n 14,p 77,n 126,p 218,n 509,p 865,n 1469,p 2208,n 2597,p 1571,p 3600,n 18587,
  p 54103,n 129210,p 275020,n 538551,p 985140,n 1694502,p 2746107,n 4185969,p 5963277,n 7832613,
  p 9218526,n 9055257,p 5638612,p 3445591,n 21220965,p 50936539,n 95307222,p 155357908,n 228998430,
  p 309660792,n 385547027,p 440176015,n 454841316,p 413184335,n 307314434,p 143898311,p 52248791,
  n 239763725,p 369275559,n 398299635,p 308649544,n 119620738,n 110600844,p 300027849,n 372621001,
  p 292614988,n 87500737,n 155219926,p 322388859,n 329321471,p 167864335,p 80456330,n 280793396,
  p 318001993,n 167384780,n 82268521,p 275814921,n 287868116,p 108858786,p 140650440,n 286682774,
  p 224186342,p 1550773,n 221193126,p 265931380,n 100663667,n 141757407,p 262567772,n 161027485,
  n 75696416,p 241437886,n 189613119,n 32347091,p 220052673,n 198125139,n 12042818,p 206711500,
  n 194389763,n 12382305,p 203347645,n 181249855,n 30981861,p 207543377,n 157227545,n 65567593,
  p 213156805,n 118009180,n 112216880,p 210238535,n 59044145,n 162454370,p 185740567,p 20041412,
  n 200572605,p 127120556,p 109383076,n 204046927,p 30520102,p 183965404,n 151084504,n 87852103,
  p 206306954,n 37335614,n 184840501,p 144120383,p 104532092,n 201749364,p 2301719,p 201140323,
  n 102796305,n 152321542,p 175627792,p 71268885,n 204775764,p 10537003,p 210510606,n 110910999,
  n 139044035,p 110534696,p 189370126,n 325323582,p 166049023,n 136543976,p 538907883,n 1072443751,
  p 1400577129,n 1823514704,p 2876599971,n 4523011051,p 6370923858,n 8561364524,p 11721660468,
  n 16001784206,p 20898711236,n 26177956438,p 32141550351,n 38637278104,p 44589181561,
  n 48947942551,p 51305803709,n 51065566293,p 46940596970,n 38094963566,p 25095220218,n 9144960144,
  n 8606205441,p 26153437808,n 40136911633,p 47412578394,n 46510239479,p 37176672818,n 20132008953,
  n 1594813624,p 22508847958,n 37097146326,p 41794616399,n 34963175658,p 17573235334,p 5242640908,
  n 25488648149,p 36280396814,n 34120293073,p 19221997333,p 3396282672,n 24220121496,p 33971389297,
  n 28722131925,p 10792534936,p 12318594780,n 29506842664,p 31323167337,n 16679338573,n 6449082353,
  p 26092011023,n 31499793526,p 18451185744,p 6056202417,n 26815457683,p 30997189343,n 15958360330,
  n 9798136462,p 29997792294,n 30032469552,p 9062675972,p 18319488326,n 33202875960,p 24704195269,
  p 2568231570,n 28865114725,p 33198815522,n 11724533097,n 19073905770,p 35502673865,n 23517903993,
  n 8747522515,p 34231643957,n 30486066121,p 558816719,p 30301928135,n 35090284177,p 7825413306,
  p 27377860442,n 37056885971,p 11918762830,p 24626706768,n 38147329013,p 14172533844]
/-- Part 1 of `rkmVoHi_m1024_r512_s1_c0`. -/
def rkmVoHi_m1024_r512_s1_c0_p1 : List ℤ := let p := rkmP; let n := rkmN; [
  p 24675076802,n 38488883780,p 12900779458,p 25828855908,n 38058183278,p 9862523851,p 29605667648,
  n 36469710071,p 2935532416,p 33497173051,n 32426252872,n 5860756453,p 37771055937,n 24769279817,
  n 17604621460,p 38312766103,n 12777882898,n 28630311749,p 34412149992,p 3750564761,n 36589977577,
  p 21949763514,p 20845053230,n 36322809204,p 3041904810,p 34399049187,n 24160143289,n 19013966408,
  p 35396860446,n 2061219514,n 34490391331,p 20805323299,p 23194798565,n 32457628893,n 6211777824,
  p 35673469530,n 10829304506,n 30934238439,p 24157585440,p 20197415947,n 32597996563,n 6938538419,
  p 35775385964,n 5846677734,n 33656135825,p 17235379208,p 27978862053,n 26512443804,n 20891558779,
  p 32399702499,p 12598558864,n 35711359514,n 3900724491,p 37731787150,n 3305490839,n 37526846709,
  p 10028209518,p 36445050218,n 16145323434,n 35868252495,p 19947622842,p 33872143675,
  n 24174960669,n 33466210201,p 26615813191,p 33482424637,n 27341434195,n 32086877112,
  p 31313118379,p 38671924534,n 22896051575,n 28612482926,p 39871322214,p 59241836116,p 3736763107,
  n 3734283953,p 77025060029,p 130566641139,p 105338793707,p 114008549700,p 232816992527,
  p 371388748637,p 446729048372,p 544536296914,p 783394257542,p 1127577145826,p 1475053663476,
  p 1862927850732,p 2438736432938,p 3253498433567,p 4226782266468,p 5336047106474,p 6714870523891,
  p 8505378577972,p 10708316974307,p 13265600525478,p 16236493201397,p 19791653442882,
  p 24039976391575,p 28952028357046,p 34485054274400,p 40713784949720,p 47774989989733,
  p 55710240113965,p 64427792917060,p 73824920143509,p 83891573669986,p 94655333666605,
  p 106048120548562,p 117870938347871,p 129894596399997,p 141962168416585,p 153970040849997,
  p 165763706946997,p 177083548594360,p 187625774022255,p 197146578531887,p 205497027012564,
  p 212564118854087,p 218196940742690,p 222203623858404,p 224421709426346,p 224789200915021,
  p 223349891302652,p 220196072087675,p 215408757707425,p 209049245312432,p 201202046163169,
  p 192023171714306,p 181747840923934,p 170650214118845,p 158986877120859,p 146964353586417,
  p 134747565985482,p 122493974677750,p 110382120285057,p 98611908260690,p 87376804132173,
  p 76827257837445,p 67048349896007,p 58063382986410,p 49858614329111,p 42413330083840,
  p 35719233135280,p 29781618741964,p 24605650105709,p 20178030337803,p 16454776523001,
  p 13360916691984,p 10801341692916,p 8677249982332,p 6901358502529,p 5406963224436,
  p 4149349246418,p 3101138660732,p 2244786721909,p 1565416120091,p 1046051765493,p 665866733430,
  p 400900914138,p 226152483494,p 117934861069,p 55725136950,p 23161965384,p 8208174184,
  p 2700709587,p 1572577437,p 1994575440,p 2602959694,p 2894320222,p 2803581525,p 2441804346,
  p 1954035719,p 1456519093,p 1019768335,p 673799695,p 420911727,p 248358471,p 137837769,
  p 71297951,p 33740579,p 14021815,p 4553415,p 549603,n 792441,n 990555,n 794547,n 531551,n 316993,
  n 172636,n 86498,n 39732,n 16450,n 5868,n 1563,n 81,p 279,p 263,p 171,p 89,p 39,p 13,p 2,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0]
/-- Output orbital vector for `m1024_r512_s1_c0`. -/
def rkmVoHi_m1024_r512_s1_c0 : List ℤ :=
  rkmVoHi_m1024_r512_s1_c0_p0 ++ (rkmVoHi_m1024_r512_s1_c0_p1)
end

public section

private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs
  | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs => match x with
    | Int.ofNat n => match uToNatHb xs with | some ns => some (uConsNat n ns) | none => none
    | Int.negSucc _ => none
private def uOfNatHb : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOfNatHb ns
private theorem uToNatHb_sound :
    ∀ (hb : List ℤ) (ns : List ℕ), uToNatHb hb = some ns → hb = uOfNatHb ns
  | [], ns, h => by injection h with h'; subst h'; rfl
  | Int.negSucc _ :: _, _, h => by dsimp only [uToNatHb] at h; cases h
  | Int.ofNat n :: xs, ns, h => by
    dsimp only [uToNatHb] at h; revert h; cases hxs : uToNatHb xs with
    | none => intro h; dsimp only at h; cases h
    | some ms =>
      intro h; dsimp only at h; injection h with h'; subst h'
      rw [uConsNat_eq, uOfNatHb, uToNatHb_sound xs ms hxs]
private def bConsZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
  | Int.ofNat v => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t
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
  | [] => []
  | u :: us => bConsZ (rkmForcedSubNatNat u z) (bDec z us)
private theorem bDec_nil (z : ℕ) : bDec z [] = [] := rfl
private theorem bDec_cons (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by rw [bDec, bConsZ_eq, bSub_eq]
private theorem bZero_eq (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bMul0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZero_eq]; rfl
private def bEnc1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k =>
    match Nat.sub z (Nat.add k 1) with | 0 => none | w + 1 => some (Nat.add w 1)
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
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h
    revert h; cases hz : z - (k + 1) with
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
    dsimp only
    have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
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
    dsimp only [rkmForcedIntAdd]; rw [bOfNatF_eq, Nat.add_eq]
    simp only [Int.ofNat_eq_natCast]; omega
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bSub_eq, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
    omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bNegSuccF_eq, Nat.add_eq, Nat.add_eq]
    simp only [Int.negSucc_eq]; omega
private theorem bAddCons_eq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bForcedAdd_eq]; cases a + b <;> cases xs <;> rfl
private def bStepVal (v P Q d : ℕ) : ℕ := match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
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
private def bHeadOr (z : ℕ) : List ℕ → ℕ
  | [] => z
  | x :: _ => x
private def bTailN : List ℕ → List ℕ
  | [] => []
  | _ :: xs => xs
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
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq] at h
  revert h
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
  let z := 100000000000000000
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
  | some bns => dsimp only; cases hv : bEnc 100000000000000000 v with
    | none => rfl
    | some vns => dsimp only; cases hi : bIter 100000000000000000 k mL cL bns vns with
      | none => rfl
      | some out =>
        dsimp only; rw [bIter_sound 100000000000000000 k mL cL bns vns out hi,
          ← uToNatHb_sound hb bns hh, bEnc_sound 100000000000000000 v vns hv]
private def muxFastIterBSlideChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    fN (altIntLen inF) fun len0 => muxIntListEq (fIter steps maxLen len0 hbF inF) outF
private theorem muxFastIterBSlideChk_sound {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : muxFastIterBSlideChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold muxFastIterBSlideChk at h; dsimp only [fL, fN] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq] at h
  rw [rkmb_forceNat_eq, fIter_eq] at h
  have h2 : muxUltraIterFullT16HiChk steps 0 maxLen hb vecIn vecOut = true := by
    unfold muxUltraIterFullT16HiChk; dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq]
    exact h
  exact muxUltraIterFullT16HiChk_sound h2
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true :=
  (rkmAllTrueF_cons h).2
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def phbv_w0_p0 : List ℤ := pzig
  [150481141962574,212500709419118,259877262180416,299639371440446,334513819156584,
   365901185313012,394634715507950,421258113470862,446149588146194,469584910686652,
   491772566677252,512874761637600,533020673948634,552315190519336,570844876246314,
   588682178410406,605888465106450,622516270306518,638610985081270,654212153438034,
   669354480273052,684068626001646,698381840619542,712318475185266,725900398522924,
   739147339784264,752077172396616,764706151218970,777049112008282,789119640275710,
   800930215091634,812492332242612,823816610256420,834912882124434,845790275014130,
   856457279842028,866921812242432,877191266199654,887272561396292,897172185156026,
   906896229717738,916450425461818,925840170614194,935070557874726,944146398351138,
   953072243125004,961852402730502,970490964788108,978991810002842,987358626709110,
   995594924120602,1003704044423778,1011689173836170,1019553352736030,1027299484957104,
   1034930346331316,1042448592552576,1049856766426674,1057157304564994,1064352543573412,
   1071444725782274,1078436004558496,1085328449236496,1092124049700972,1098824720651180,
   1105432305573412,1111948580445814,1118375257197270,1124713986940116,1130966362994522,
   1137133923720784,1143218155174252,1149220493596344,1155142327753868,1160985001137828,
   1166749814031930,1172438025460124,1178050855021742,1183589484622098,1189055060105732,
   1194448692798974,1199771460967870,1205024411197148,1210208559695366,1215324893531048,
   1220374371804238,1225357926757530,1230276464830412,1235130867660380,1239921993034118,
   1244650675791744,1249317728686946,1253923943205598,1258470090345308,1262956921358146,
   1267385168458676,1271755545499228,1276068748614306,1280325456835772,1284526332680482,
   1288672022711824,1292763158076594,1296800355018494,1300784215369542,1304715327020468,
   1308594264371276,1312421588762910,1316197848891036,1319923581202818,1323599310277546,
   1327225549191898,1330802799870624,1334331553423298,1337812290467894,1341245481441722,
   1344631586900390,1347971057805330,1351264335800400,1354511853478096,1357714034635836,
   1360871294522758,1363984040077458,1367052670157094,1370077575758204,1373059140229626,
   1375997739477852,1378893742165134,1381747509900684]
private def phbv_w0_p1 : List ℤ := pzig
  [1384559397425208,1387329752789112,1390058917524598,1392747226811928,1395395009640088,
   1398002588962076,1400570281845052,1403098399615518,1405587247999762,1408037127259742,
   1410448332324578,1412821152917832,1415155873680748,1417452774291586,1419712129581218,
   1421934209645112,1424119279951860,1426267601448346,1428379430661718,1430455019798256,
   1432494616839238,1434498465633960,1436466805989952,1438399873760548,1440297900929844,
   1442161115695202,1443989742547324,1445784002348024,1447544112405756,1449270286548980,
   1450962735197442,1452621665431430,1454247281059096,1455839782681872,1457399367758078,
   1458926230664764,1460420562757842,1461882552430578,1463312385170478,1464710243614628,
   1466076307603550,1467410754233596,1468713757907936,1469985490386206,1471226120832814,
   1472435815863974,1473614739593520,1474763053677496,1475880917357584,1476968487503422,
   1478025918653798,1479053363056794,1480050970708902,1481018889393124,1481957264716102,
   1482866240144306,1483745957039302,1484596554692116,1485418170356744,1486210939282808,
   1486974994747392,1487710468086092,1488417488723258,1489096184201524,1489746680210558,
   1490369100615132,1490963567482474,1491530201108942,1492069120046048,1492580441125830,
   1493064279485592,1493520748592040,1493949960264820,1494352024699470,1494727050489806,
   1495075144649756,1495396412634654,1495690958362006,1495958884231734,1496200291145934,
   1496415278528126,1496603944342034,1496766385109892,1496902695930300,1497012970495616,
   1497097301108934,1497155778700604,1497188492844360,1497195531773026,1497176982393806,
   1497132930303214,1497063459801586,1496968653907230,1496848594370204,1496703361685736,
   1496533035107274,1496337692659200,1496117411149194,1495872266180274,1495602332162486,
   1495307682324284,1494988388723592,1494644522258544,1494276152677922,1493883348591290,
   1493466177478838,1493024705700906,1492558998507260,1492069120046048,1491555133372496,
   1491017100457318,1490455082194856,1489869138410960,1489259327870590,1488625708285156,
   1487968336319620,1487287267599310,1486582556716512,1485854257236794,1485102421705086,
   1484327101651522,1483528347597032,1482706209058698,1481860734554868,1480991971610040,
   1480099966759514,1479184765553794,1478246412562780]
private def phbv_w0_p2 : List ℤ := pzig
  [1477284951379724,1476300424624950,1475292873949358,1474262340037698,1473208862611614,
   1472132480432476,1471033231303974,1469911152074510,1468766278639338,1467598645942520,
   1466408287978624,1465195237794226,1463959527489178,1462701188217662,1461420250189020,
   1460116742668356,1458790693976924,1457442131492298,1456071081648294,1454677569934700,
   1453261620896760,1451823258134430,1450362504301422,1448879381104006,1447373909299582,
   1445846108695030,1444295998144818,1442723595548870,1441128917850210,1439511981032354,
   1437872800116466,1436211389158272,1434527761244714,1432821928490372,1431093902033616,
   1429343692032522,1427571307660508,1425776757101722,1423960047546154,1422121185184496,
   1420260175202704,1418377021776300,1416471728064388,1414544296203384,1412594727300448,
   1410623021426630,1408629177609714,1406613193826748,1404575066996268,1402514792970210,
   1400432366525484,1398327781355230,1396201030059738,1394052104137020,1391880993973036,
   1389687688831558,1387472176843678,1385234444996930,1382974479124050,1380692263891336,
   1378387782786602,1376061018106744,1373711950944880,1371340561177052,1368946827448524,
   1366530727159594,1364092236450974,1361631330188700,1359147981948540,1356642163999936,
   1354113847289420,1351563001423520,1348989594651124,1346393593845310,1343774964484606,
   1341133670633662,1338469674923356,1335782938530254,1333073421155478,1330341081002900,
   1327585874756692,1324807757558178,1322006682982000,1319182603011536,1316335468013600,
   1313465226712352,1310571826162424,1307655211721238,1304715327020468,1301752113936648,
   1298765512560874,1295755461167594,1292721896182442,1289664752149078,1286583961695026,
   1283479455496462,1280351162241906,1277199008594814,1274022919154992,1270822816418824,
   1267598620738266,1264350250278556,1261077620974588,1257780646485938,1254459238150448,
   1251113304936352,1247742753392882,1244347487599284,1240927409112214,1237482416911420,
   1234012407343694,1230517274064968,1226996907980544,1223451197183348,1219880026890156,
   1216283279375688,1212660833904518,1209012566660696,1205338350674990,1201638055749676,
   1197911548380732,1194158691677402,1190379345278944,1186573365268510,1182740604084004,
   1178880910425810,1174994129161248,1171080101225624]
private def phbv_w0_p3 : List ℤ := pzig
  [1167138663519730,1163169648803648,1159172885586674,1155148198013230,1151095405744554,
   1147014323835990,1142904762609704,1138766527522582,1134599419029110,1130403232439026,
   1126177757769456,1121922779591314,1117638076869682,1113323422797890,1108978584624984,
   1104603323476264,1100197394166578,1095760545005966,1091292517597334,1086793046625704,
   1082261859638650,1077698676817458,1073103210738530,1068475166124518,1063814239584670,
   1059120119343790,1054392484959224,1049631007025202,1044835346863872,1040005156202264,
   1035140076834420,1030239740267842,1025303767353376,1020331767897570,1015323340256492,
   1010278070909918,1005195534014734,1000075290936278,994916889756322,989719864756234,
   984483735873766,979208008131876,973892171037718,968535697949978,963138045412416,
   957698652451460,952216939835408,946692309292698,941124142686404,935511801141990,
   929854624125004,924151928465216,918403007323304,912607129095958,906763536254850,
   900871444114516,894930039523798,888938479474970,882895889624120,876801362715830,
   870653956904446,864452693963554,858196557374448,851884490283442,845515393316882,
   839088122241584,832601485457108,826054241304898,819445095177692,812772696410790,
   806035634934746,799232437666756,792361564615364,785421404670212,778410271045158,
   771326396339250,764167927175698,756932918373954,749619326604246,742225003467318,
   734747687934486,727184998074232,719534421981388,711793307812924,703958852820482,
   696028091253414,687997880986904,679864888707096,671625573458296,663276168325434,
   654812659986924,646230765827360,637525908244558,628693185718940,619727340132376,
   610622719724698,601373236954664,591972320381758,582412859498372,572687141207688,
   562786776347352,552702614283738,542424643121168,531941872449586,521242194745204,
   510312220473496,499137080527114,487700187725008,475982946502082,463964396333494,
   451620769414442,438924935964630,425845700162480,412346894397224,398386196390666,
   383913557927070,368869076939796,353180051118112,336756791858654,319486494447608,
   301223932430418,281776698846422,260880491629466,238154750772610,213015328949748,
   184478793403010,150627451036432,106510097573240]
private def phbv_w0 : List ℤ := phbv_w0_p0 ++ (phbv_w0_p1 ++ (phbv_w0_p2 ++ phbv_w0_p3))
private def pvm_w0_1_p0 : List ℤ := pzig
  [0,0,5,13,17,21,0,14,1,33,7,6,8,18,5,2,16,17,23,3,5,17,1,14,12,7,21,19,4,8,12,9,23,43,49,30,74,
   10,57,29,18,31,53,3,8,8,11,35,47,6,32,44,18,19,41,29,8,2,20,22,6,0,29,41,26,54,27,91,11,32,0,
   4,11,37,25,15,7,14,56,20,43,37,6,7,3,52,44,12,5,2,44,24,17,39,7,0,12,6,18,40,38,11,65,47,3,26,
   86,56,21,25,1,32,40,6,0,24,24,6,2,5,4,36,100,104,42,2,8,4]
private def pvm_w0_1_p1 : List ℤ := pzig
  [12,28,54,14,19,1,34,60,10,8,56,46,16,70,32,84,26,52,94,40,0,104,46,64,54,63,580,617,1144,1257,
   1562,2255,3228,6447,13414,25367,31402,795,126361,412108,874341,1408008,1778817,1887636,
   1947531,1958664,763169,3933823,13306754,25666565,40751094,69047695,134116030,241779239,
   339384372,329037281,138059024,263407108,850924213,1489366512,1939771729,1927001228,1210176901,
   246698791,1460113514,1172260627,578604245,1764993484,467564772,1747320025,1035459915,
   1134320784,1845552504,821498188,388883813,635486573,172045028,1630717446,3436938620,
   5568586444,8217210728,11691411102,16376635678,22745416998,31392947264,43083210926,58802002262,
   79818344852,107757106334,144685488404,193215741684,256626186254,339002372220,445399899928,
   582029969922,756468100312,977885598736,1257302283188,1607857597946,2045095657102,
   2587257886264,3255574847190,4074546571544,5072198372688,6280296748654,7734507759690,
   9474478310690,11543819263782,13989968435002,16863911484570,20219739680676,24114025675280,
   28605001913712,33751531205468,39611865334214,46242195339914,53695006121256,62017258053336,
   71248429053712,81418461532132,92545669403680,104634670248068,117674416128978,131636402908180,
   146473141489644,162116974765114,178479320677194,195450414488382]
private def pvm_w0_1_p2 : List ℤ := pzig
  [212899611953862,230676299768118,248611440739512,266519759233036,284202548312328,
   301451054706910,318050372374234,333783751255858,348437206106940,361804292218956,
   373690901550116,383919925119452,392335626145270,398807573645272,403233998051696,
   405544448465868,405701654777318,403702525987840,399578247439984,393393472792868,
   385244639956332,375257472207954,363583754879506,350397502968816,335890654710966,
   320268439722464,303744577344510,286536461139664,268860479372484,250927609284132,
   232939405886492,215084484904944,197535575584918,180447193646146,163953958826454,
   148169557256214,133186323064204,119075407984886,105887426334300,93653729682228,82387317967508,
   72086773873874,62730732973958,54304244724674,46728142282184,40061593516506,34000850889138,
   29019339974000,24084568335788,20646246477000,16778691451812,14049362841670,11830322766538,
   9306652293114,7631482340326,6534219638260,5178108575326,3738494877150,3070238265820,
   2801570295958,2417929389910,1773337583118,948638339604,247084325668,128604909185,261758401081,
   308471068775,318296982061,277647621463,193246955775,100545012803,28593455147,11703433970,
   28064080576,30046247650,25490119004,20043357816,15168710820,10780859964,7424270004,5383847012,
   4108826304,2975153744,1835531430,879346262,241216796,81166713,188103127,191423963,155745809,
   111484067,75418197,51807933,36359817,23964867,13716853,6163359,1622781,444534,1038752,999950,
   783716,550882,346144,192146,95568,43960,18662,6344,454,1913,2377,1989,1389,859,493,263,127,53,
   17,3,0,0,0,0,0,0,0]
private def pvm_w0_1_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_1_p4 : List ℤ := pzig
  [0]
private def pvm_w0_1 : List ℤ :=
  pvm_w0_1_p0 ++ (pvm_w0_1_p1 ++ (pvm_w0_1_p2 ++ (pvm_w0_1_p3 ++ pvm_w0_1_p4)))
private def pvm_w0_2_p0 : List ℤ := pzig
  [0,0,5,13,17,23,21,19,20,12,21,13,17,1,24,0,7,18,18,11,13,1,5,23,15,9,20,16,1,17,27,0,2,3,24,
   26,27,97,43,66,34,19,11,14,17,21,39,33,0,20,8,37,35,43,7,44,42,12,5,35,29,1,0,13,42,68,35,75,
   6,44,18,23,35,41,5,26,4,17,2,1,73,45,30,30,22,4,2,21,35,33,26,52,20,9,4,36,44,22,9,31,8,4,37,
   5,32,40,54,30,33,73,55,10,80,50,0,17,14,16,6,16,24,0,24,44,22,37,53,18]
private def pvm_w0_2_p1 : List ℤ := pzig
  [56,78,78,66,30,0,43,88,38,10,0,12,26,26,11,20,166,293,572,827,1374,1829,2592,3533,5210,6361,
   4294,9428,51077,148796,336677,640222,1045735,1470164,1745143,1629846,807201,1197079,5229530,
   12734065,25741668,46506255,77035628,118492409,168692422,214720625,221835042,130226453,
   123295285,556187464,1092713531,1562256756,1756802039,1515755234,809774857,175830731,
   1010250240,1182637853,496255208,591015338,1118204939,452624740,775916310,1010739821,212941503,
   1138428526,176024053,1133108625,319721778,1189596878,190082737,1328028377,351758405,
   1180684748,1135009528,268484587,1257691019,863600463,318159432,1145850998,1072129504,
   366840468,353883429,625355483,305671745,525817598,1744695152,3300836620,5257763302,7785817568,
   11147039832,15692171560,21874544318,30278565936,41659789678,56995263136,77544638180,
   104923634628,141191949732,188957837686,251501521232,332919412728,438290812544,573868291658,
   747292311172,967829754630,1246634914386,1597030068586,2034801097590,2578501632570,
   3249757029220,4073557070314,5078523797716,6297138363966,7765908408952,9525455368012,
   11620499489330,14099719378876,17015462811000,20423286545284,24381305161018,28949332615564,
   34187805448536,40156483327666,46912930910760,54510794633682,62997898772438,72414196603688]
private def pvm_w0_2_p2 : List ℤ := pzig
  [82789624233074,94141916109092,106474451756992,119774212165956,134009930853008,149130528247612,
   165063918109992,181716270755902,198971809623706,216693205104986,234722612724230,
   252883382104108,270982439356590,288813319494824,306159798277562,322800045837788,
   338511198867156,353074225398638,366278937658498,377928995206432,387846733569440,
   395877653488532,401894412829124,405800177846612,407531209441792,407058593163762,
   404389029879392,399564715882462,392662124302486,383790329370674,373087147524178,
   360718376872364,346866001290072,331743071321480,315541119642088,298535295976248,
   280838876156670,262891194804444,244510765481400,226560613357408,208233176236548,
   191030941726710,173579864736254,157403996427398,141783203309788,126736335220040,
   113214327093568,100146550432996,88092727846532,77435397002998,67433500001160,58176801442096,
   50360638642576,43300717453242,36604164300160,30994822543634,26410987575112,22147114475768,
   18204877075806,15012452164332,12583963176212,10513730890490,8481750547822,6587433791116,
   5161407660290,4312296093936,3769522687262,3181435715016,2427225450230,1619213737170,
   914939544602,386530611948,27794740790,188792022169,287557964997,294468951665,241832167581,
   164173675533,89670602439,33783390909,570310288,17592526612,23126171372,22151171164,
   18349782656,14109490526,10567584444,7901589248,5847571384,4148595098,2721031100,1590572434,
   782609184,274380194,2740508,110158717,134463329,120102161,94946451,70511391,49801795,33044941,
   20138339,10950873,5055223,1705895,68217,561446,673478,566842,403290,256564,149560,80626,39932,
   17566,6164,934,1033,1459,1263,903,579,335,175,79,31,7]
private def pvm_w0_2_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_2_p4 : List ℤ := pzig
  [0]
private def pvm_w0_2 : List ℤ :=
  pvm_w0_2_p0 ++ (pvm_w0_2_p1 ++ (pvm_w0_2_p2 ++ (pvm_w0_2_p3 ++ pvm_w0_2_p4)))
private def pvm_w0_3_p0 : List ℤ := pzig
  [0,0,5,13,17,23,13,31,39,2,14,1,0,25,31,2,16,7,9,18,26,5,1,1,0,3,25,25,15,4,34,6,15,13,1,7,47,
   0,76,48,77,77,9,8,6,2,6,1,18,11,53,41,17,3,24,12,27,55,37,17,16,66,24,37,10,16,53,71,22,72,30,
   19,33,21,12,54,8,65,15,4,29,27,32,32,7,53,49,17,0,2,28,42,22,47,55,9,12,40,8,31,16,62,26,8,22,
   6,10,17,27,27,15,24,76,84,16,81,67,4,16,28,26,24,15,0,38,36,47,14]
private def pvm_w0_3_p1 : List ℤ := pzig
  [6,88,42,35,9,29,9,69,298,307,782,1121,1630,2109,2646,2489,518,6536,24733,65388,145263,284738,
   499509,784986,1090459,1288718,1144661,288056,1822036,5954111,13185372,24939001,42822274,
   68016075,99971946,134251369,159591536,154894851,88290158,77527278,368831677,773177244,
   1212200595,1538933798,1581567023,1229722660,522304515,321011035,961402074,1088762271,
   607384020,231618658,883536903,837582166,78059697,748166137,818144242,794333,823323417,
   634568890,398325278,893906957,70020942,885272660,403364275,787153543,584134338,721196548,
   644584471,743661137,597009120,862289862,405311815,1022140085,2690910,1057579890,606197424,
   681633149,1115519677,229065497,882868792,1040533700,199548042,747866435,981025765,415508611,
   419839844,927159126,855344064,351812486,238915721,605020541,584547583,157803221,625530632,
   1722613538,3146028814,4983462618,7401407594,10646628640,15054071984,21064775676,29254429386,
   40372427228,55391627956,75569761944,102524066182,138321146204,185584265710,247620288086,
   328568363532,433572169342,568977044628,742552686730,963741155848,1243928742888,1596738768014,
   2038340586828,2587767997052,3267237888440,4102457418936,5122905312260,6362070171304,
   7857626130506,9651523905546,11789973539094,14323294106464,17305605562540]
private def pvm_w0_3_p2 : List ℤ := pzig
  [20794339006664,24849544117328,29532976531888,34906953626596,41032974525032,47970109165356,
   55773171725194,64490705349650,74162817541582,84818918253004,96475424956578,109133510338180,
   122776977100350,137370352780916,152857295832800,169159419192998,186175587036308,
   203781861680786,221831898058332,240158553639756,258574857784968,276879083588470,
   294852304222730,312275693197464,328905380739328,344540560214344,358899537751936,
   371877007331484,383081229071838,392663201455362,399952499940400,405591513825944,
   408458168517730,409759200293798,408130639963126,404781216500806,399036473267752,
   391032602179766,381547221808456,369692088094356,356538913316852,342031846637488,
   325935550654756,309170635288488,291710424183922,273333922464738,254966464213628,
   236664110343692,218037037606118,199917384866888,182585442086636,165482301345462,
   149033332800126,133834655087720,119485659415538,105756187152456,93150069458508,81864986492498,
   71492050670514,61823505333314,53141968416756,45659567306642,39126913670114,33155291842578,
   27715812442790,23090788440740,19386693351414,16313154505676,13491593377750,10840948152030,
   8573378292920,6881042978056,5714315904782,4840770919452,4037974795988,3210455248288,
   2377273130074,1602316687926,941372218510,425538914374,64197263494,150685109329,242711116701,
   246906497675,201311870079,138058056085,78399912791,32682319535,3209424761,12339231474,
   18135620308,18325306872,16015659282,13027558502,10164862778,7660790446,5536760516,3782507766,
   2398094844,1376818758,685593034,263734024,36968502,65022673,96886239,94569265,78552639,
   59199913,41270933,26679451,15878947,8547209,3993643,1436963,177669,323336,434060,378254,
   275410,179114,106668,58556,29406,13124,4786,956,507,851]
private def pvm_w0_3_p3 : List ℤ := pzig
  [759,545,343,193,97,41,11,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_3_p4 : List ℤ := pzig
  [0]
private def pvm_w0_3 : List ℤ :=
  pvm_w0_3_p0 ++ (pvm_w0_3_p1 ++ (pvm_w0_3_p2 ++ (pvm_w0_3_p3 ++ pvm_w0_3_p4)))
private def pvm_w0_4_p0 : List ℤ := pzig
  [0,0,5,13,17,23,19,5,21,49,21,5,0,14,10,27,37,9,16,15,15,8,16,14,1,5,14,0,0,9,37,33,13,30,20,9,
   21,36,20,71,65,30,80,24,25,45,41,5,10,19,3,22,26,4,13,35,61,29,22,2,12,12,55,93,9,46,4,15,36,
   64,5,73,39,27,24,74,24,69,27,40,22,7,4,10,9,55,37,2,40,28,35,19,17,53,41,6,30,58,44,57,55,2,
   22,5,17,3,24,22,24,22,24,30,3,18,0,51,91,3,70,114,4,30,39,71,8,13,108,141]
private def pvm_w0_4_p1 : List ℤ := pzig
  [260,493,894,1177,1468,1503,552,2690,10667,28312,62931,125604,228695,380850,576821,777504,
   882873,698810,101838,2013359,5727006,12136693,22290650,37204309,57400032,81998113,107255280,
   124679269,119319478,69484393,50230157,260639068,563763359,925709960,1265193207,1460808542,
   1387914707,982003354,302434583,447036341,976734804,1043843673,600238964,135450312,752223747,
   865901612,382776873,370717163,813845456,552670189,214989895,770239102,525415953,296699065,
   779050368,318412211,550789365,695852306,124201464,776564009,268073522,670874832,535363131,
   507404179,684335078,371358688,754782849,304054341,779893234,321026342,769524469,424854099,
   704534102,603129802,537776853,808379209,212090312,927244686,281216370,777696055,796350329,
   218471226,971574932,587326082,444669889,991736309,542918453,391259722,928249586,656753642,
   112733249,738271167,791425203,307022213,347397112,775482074,783154406,427201056,79251209,
   501406499,675908257,535791885,83945807,653444834,1668889136,3000838240,4747586318,7074509560,
   10221581248,14516049778,20392957974,28424791006,39361065296,54178804910,74145251652,
   100894579170,136520713202,183688554218,245765945974,326978626078,432590115236,569108022834,
   744517536562,968541885188,1252928285680,1611756289120,2061763496224,2622681397556]
private def pvm_w0_4_p2 : List ℤ := pzig
  [3317571424624,4173148880670,5220078453816,6493225050450,8031832645960,9879623830306,
   12084751215238,14699685642024,17780733357858,21387847505224,25583057300666,30431353020552,
   35995270370900,42342437689714,49524898299630,57615579435892,66630815067896,76670371743786,
   87656278616384,99781799732080,112755879965008,126998517841402,141832816244462,158050937084476,
   174499404760652,192274413574294,210036065145902,228622826442550,247290643111774,
   265816991463796,284592743911840,302425656406696,320004500709986,336615033254570,
   351854401464116,366120077223102,378590952589170,389182400556982,398182825724150,
   404828436450700,409191825151412,411646734016870,411509698484248,408932633478788,
   404474749438746,397610969979928,388419603215538,377663341195414,365122915158994,
   350656580591240,335042378894760,318547837096732,300882162633560,282448075363054,
   263912203894758,245261829414080,226372104384438,207689329166914,189697726236284,
   172351835627912,155483039294770,139338013528684,124327367204892,110478781789550,
   97503282766464,85326340251600,74233504607180,64438868910438,55752362558554,47815955390054,
   40538236508124,34134387780326,28771135564664,24305691637250,20405070857444,16844535001930,
   13643425883424,10950955616848,8853092846568,7283606819558,6071926426356,5043850333102,
   4089222319762,3172366382426,2308507608294,1535026916050,890119431448,399120506920,67119628040,
   121724995835,198525860975,200537356523,162497992015,111106824125,63189113119,26677815015,
   3097497097,9619472312,14793245682,15516696798,14028153720,11678712174,9173267080,6843392772,
   4837816552,3217610978,1990859784,1125186930,559783112,221247558,38852616,45491041,73838641,
   73632791,61252449,45664015,31262103,19787111,11534403,6097261,2812761,1012485,142617,199598,
   276710,242500,176854,115016]
private def pvm_w0_4_p3 : List ℤ := pzig
  [68364,37372,18656,8260,2992,612,275,479,421,293,175,91,39,11,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0]
private def pvm_w0_4_p4 : List ℤ := pzig
  [0]
private def pvm_w0_4 : List ℤ :=
  pvm_w0_4_p0 ++ (pvm_w0_4_p1 ++ (pvm_w0_4_p2 ++ (pvm_w0_4_p3 ++ pvm_w0_4_p4)))
private def pvm_w0_5_p0 : List ℤ := pzig
  [0,0,5,13,17,19,27,25,4,9,35,35,19,21,5,16,32,15,45,11,4,7,15,27,16,14,2,6,3,10,4,14,4,13,51,
   55,18,32,17,43,30,68,1,71,53,15,48,64,2,37,23,5,17,31,1,5,6,42,38,29,37,23,53,47,36,68,2,95,
   39,10,31,47,18,36,40,56,4,101,71,30,66,2,25,4,1,0,5,2,46,28,51,57,1,15,8,24,0,5,1,55,85,37,58,
   68,2,15,21,14,11,19,25,26,21,16,10,48,46,91,160,115,350,567,678,955,672,496,3521,10816]
private def pvm_w0_5_p1 : List ℤ := pzig
  [25209,52128,98651,172184,277463,408454,534461,578570,388653,297047,1884688,4946837,10216098,
   18517129,30587094,46709053,66068330,85773479,99613710,96881589,61992634,23978020,178609125,
   409644204,703717015,1016053054,1267866803,1359305604,1202284821,767766612,128154549,534458979,
   978201490,1006601101,585984120,96306020,691999909,868075060,514117135,153148787,689390348,
   707666947,180262186,484097642,721104065,297945988,410046532,703306931,252575592,478975440,
   661031255,50538702,626375076,497809981,298150207,687779012,96758635,643672997,411835316,
   470454206,604170453,266704795,694907456,92987950,726036015,24150306,734718482,77002939,
   743330729,63762960,757227686,17826660,764124799,169426231,733064788,382830412,615998909,
   622015513,361204932,802116372,48422154,787279423,530341775,449030224,852683656,186533264,
   709250059,782810533,15216288,790394150,750265042,16755889,745149847,789498239,169973879,
   551194790,807985846,459850624,185162065,666436159,698888591,310980911,238341880,649935852,
   744044598,515962078,95219332,338976533,632724061,694692433,494828329,39307105,661151228,
   1618226382,2884398362,4564536830,6824831616,9903393878,14125654996,19927175080,27884225816,
   38756324598,53534611558,73516509534,100362494484,136248547402,183854152434,246794734304]
private def pvm_w0_5_p2 : List ℤ := pzig
  [329131753366,436983663282,575730697556,756494162558,983866227910,1280784977936,1642119278490,
   2121272582932,2676383227294,3437006094614,4260625961100,5444636693070,6631931382872,
   8420335530506,10112239977966,12690188189114,15127384182392,18624910765400,22187204511726,
   26676063142150,31792239535072,37442745999792,44339292519286,51614987206550,60211106021620,
   69670980758776,79975570840768,91684994557928,104142501721238,117713882618980,132528299041668,
   147982997275414,164509519730818,181973031837972,199775074693622,218333011890898,
   237348236754970,256174817687114,275185450298884,294038439228192,312002063566634,
   329380000723286,345943149438536,360888667345534,374385405245606,386473075361226,
   396402707872700,404100369212512,409903430915984,413386282150542,414199199235162,
   412742825375968,409158668265558,403089722921490,394630131260558,384303226458612,
   372235462324324,358272180836662,342682888407246,326036471665462,308558076063734,
   290178213777940,271114750911908,251917600391510,232927313026720,214087692626968,
   195395292774224,177218620459096,159983288112294,143741774124762,128283117635742,
   113585882885448,99943112396848,87616381756362,76528671608968,66387923022006,57036916550358,
   48588308835986,41230522292986,34972523594714,29600625431626,24846541558666,20568061759084,
   16786779773536,13592636899668,11026316171800,9027959451190,7461749729140,6174119693888,
   5042843066410,3999271272154,3026544651158,2143609873792,1384150932688,777411096766,
   335716001718,50644087544,103343318415,161086800777,158341984885,125418316411,83943345511,
   46564959113,18639459039,742321683,8950528096,12942032146,13467040874,12157457798,10061599248,
   7795637492,5696140872,3927159794,2544617312,1535886888,848329688,412012250,156621762,21759254,
   38886137,57706415,55596155,44997845,32656445,21748813,13381757,7577949,3886437]
private def pvm_w0_5_p3 : List ℤ := pzig
  [1732051,591401,60707,137284,174684,148050,105500,67234,39164,20942,10184,4364,1496,256,175,
   251,205,129,67,27,7,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_5_p4 : List ℤ := pzig
  [0]
private def pvm_w0_5 : List ℤ :=
  pvm_w0_5_p0 ++ (pvm_w0_5_p1 ++ (pvm_w0_5_p2 ++ (pvm_w0_5_p3 ++ pvm_w0_5_p4)))
private def pvm_w0_6_p0 : List ℤ := pzig
  [0,0,5,13,17,15,11,33,33,7,8,19,27,23,19,31,35,10,42,2,13,33,3,10,19,23,19,10,2,4,0,1,10,1,6,
   36,34,29,79,31,44,1,55,21,24,56,40,29,75,55,30,44,14,2,6,23,21,2,17,57,5,30,34,1,18,32,43,125,
   35,60,26,23,2,17,41,21,27,49,41,66,118,22,57,61,13,18,14,23,22,38,31,43,16,26,32,22,25,45,33,
   16,23,13,18,74,5,51,117,31,54,51,142,205,338,413,418,219,701,3150,8603,19154,38331,70726,
   120883,191358,277077,355570,370633,210870]
private def pvm_w0_6_p1 : List ℤ := pzig
  [320408,1534055,3877686,7934701,14370098,23790839,36467176,51861907,67939476,80288043,81242410,
   59420219,349612,110975918,284961613,519820020,793157187,1056329256,1236699729,1252593870,
   1042042225,598996610,1741727,587019505,963789442,967919525,573691972,61733212,641115001,
   864814852,603733747,2812038,573274156,752469631,409608698,216058298,659299459,568181306,
   6360557,552388373,602002154,78601763,521079209,582347756,18721333,567488765,501626342,
   162851588,630215565,299551386,425079568,581608555,66361109,624482980,274472629,490032989,
   508179984,274453794,622617887,54554871,648012576,127613379,625782779,258101270,591366766,
   338070667,568640983,372747148,570149178,364653709,598510329,310873276,646550714,203835545,
   695579851,35973688,713048754,190675940,653191841,449619597,467317294,674036646,131719157,
   754124019,306168431,572856422,687191334,99368923,766168251,492220257,370845360,807548080,
   343366076,488184585,806965397,316784865,468740386,804894288,420307150,307311591,756138833,
   595735263,1082380,564272818,707604238,376336186,174585369,592527547,651303169,352156759,
   120817694,529533796,699357766,588210088,254771878,144237611,523609717,669339823,765155207,
   309792147,290829721,1227357728,548553558,4708824898,1084016804,12469531622,47751888,
   29556005382]
private def pvm_w0_6_p2 : List ℤ := pzig
  [4625153887,64278655928,13916675225,125974184622,20504017389,217547951846,4587158588,
   327041592576,120593402328,437929407526,396041407352,581090309888,853052545300,899749241892,
   1451708563452,1615673906278,2225007629826,2854575849364,3466076929136,4594263477462,
   5606655685248,7006817740086,8831014942090,10698324038446,13226787650292,16180430464910,
   19427570353726,23567794993720,28229516829282,33453210704046,39793236301718,46807671634612,
   54615489082366,63736621153168,73688757693294,84562472349110,96860690633744,110092240650724,
   124197122056086,139663380312554,156051168169350,173046106172548,191063577632166,
   209819552264512,228729855969742,247989944574500,267565400612778,286765515376002,
   305392973250856,323599289306820,340919415222048,356785548709918,371231365725664,
   384237404942528,395279040122600,404019788721442,410615855001700,415064203884064,
   416986156442292,416236920900694,413110523283390,407786426144720,400093809342792,
   390000652084056,377906197801672,364224457850786,349005398467422,332228791375692,
   314240740793258,295599061452360,276592120488072,257195474772950,237501067876882,
   217937904467190,198968184809832,180725008558128,163092598655242,146077516042548,
   129958942699580,115054833373198,101433614020294,88914359146058,77315336437126,66648730409116,
   57073954832480,48701613548698,41462250361956,35144598925986,29535282509250,24527498148802,
   20128483277996,16390131191770,13330255121296,10893696565676,8961496957232,7388502789538,
   6044316503346,4840640779154,3739102994170,2742179704288,1874549656000,1163232627942,
   622965479752,249783586072,22319882690,91914429663,128661958641,120232139605,91486096933,
   58684517545,30489821253,10062376103,2698850880,9361732574,11815518664,11703620996,10244353478,
   8250330458,6216431822,4411159010,2950411666,1852999156,1081995334,574893988,264059854,
   88755746,520206,35965317]
private def pvm_w0_6_p3 : List ℤ := pzig
  [44498471,39936677,30800153,21454327,13746855,8138017,4424479,2165211,904897,270101,6742,98408,
   106312,84258,57370,35176,19732,10142,4708,1890,574,50,109,115,73,35,11,1,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_6_p4 : List ℤ := pzig
  [0]
private def pvm_w0_6 : List ℤ :=
  pvm_w0_6_p0 ++ (pvm_w0_6_p1 ++ (pvm_w0_6_p2 ++ (pvm_w0_6_p3 ++ pvm_w0_6_p4)))
private def pvm_w0_7_p0 : List ℤ := pzig
  [0,0,5,13,17,15,7,7,19,41,27,0,0,17,23,15,0,45,45,21,12,42,2,19,21,8,4,21,21,23,0,8,7,5,12,10,
   7,35,10,86,40,53,51,9,18,5,37,53,21,50,84,12,53,49,15,19,30,42,8,21,1,20,1,67,39,22,0,53,26,
   110,26,59,69,39,17,1,34,5,43,5,38,33,93,81,5,94,86,19,25,12,29,31,15,42,8,18,23,25,39,48,70,
   47,94,195,250,251,39,578,2193,5822,12593,25066,46123,78448,123995,179172,229429,237412,126717,
   239791,1085638,2742675,5658082,10365685,17393400,27069331,39186742,52503725]
private def pvm_w0_7_p1 : List ℤ := pzig
  [64090972,68628247,57888204,20820411,55201051,181400178,362639845,591014076,839748031,
   1060533794,1188162243,1155412346,917789391,481982082,74236644,605786487,938119024,935214073,
   573693806,16456852,581162505,848959812,675120565,143891576,448529250,748998287,566935460,
   18679855,522283273,669351622,310281923,280810449,629189976,438588451,134089261,577032622,
   469613379,97975347,564172096,437008177,164818547,583496640,329818653,317123929,579469446,
   115252283,500062987,457566428,205121774,587023625,137733552,514346396,407162751,318368319,
   556110952,83858584,594020191,130578850,556813492,297869203,483814245,414164756,406290026,
   487576431,344834615,529190206,311151576,547529225,310816561,545773140,345102320,520761601,
   411044293,463335936,499628134,360336635,592587043,199284510,659281486,23037964,656728979,
   287970017,537791664,541798426,272939679,692167303,114054659,631182716,511357934,299539795,
   723166247,222084741,560015958,664957178,16665321,680584373,584505137,144675314,718354072,
   557009654,151025601,704757029,601734187,35263010,620287078,686987140,182009198,393576131,
   753770923,363724877,133384507,918426782,62833083,1608395138,2340407293,3243034976,6874267685,
   9696121908,15807486975,24393156348,34497794717,50207775224,66747220555,86873706748,
   106967702847,122560388830,132876471287,128021466576]
private def pvm_w0_7_p2 : List ℤ := pzig
  [109377766651,71639868168,18905797311,37068376683,92932970694,115552573213,123238873482,
   67816762557,27305327910,73258513962,67057320823,131363572318,11008039580,49326266146,
   184217562228,57768526818,228030059500,300469366932,263798188620,539002468424,620575400676,
   744153051740,1162258045222,1367950863892,1749139555510,2428609451036,2933783129146,
   3738836617584,4899040194210,5974230490022,7472463921420,9459148895272,11502821963996,
   14094313649490,17388594416202,20944204651198,25164821316334,30355028235686,36084264473866,
   42569979598720,50268496639174,58845815392736,68238387504226,78944094014338,90853568481050,
   103625479405816,117563131800196,132835360140692,149016760317814,165986129154428,
   184003524882206,202860694751880,222068106882092,241582335774184,261469197171012,
   281306763974402,300597588428586,319277300213202,337296418557454,354181019145622,
   369446499985680,383028384346016,394922154354146,404759484525926,412119763046524,
   416989042373434,419544251502588,419676030090902,417096987642152,411832039460184,
   404249185006846,394594559638052,382804805945544,368878107622938,353188914161298,
   336259320733978,318351692487796,299478516360728,279775495121992,259683317124938,
   239701120529268,220066471087572,200769310403316,181841533384120,163540994515896,
   146228002715990,130111087657124,115153291051550,101212249615788,88238564937532,76335408058486,
   65652654014980,56241886607804,48002170461174,40741365766004,34283561018544,28539421510488,
   23505079845834,19209989414942,15657224563802,12789883553410,10493522165322,8624751956344,
   7047787277534,5662742696004,4417144327148,3300595191492,2328507758830,1522950473662,
   897376134632,448800226748,157572653864,7529135963,82074228395,99406978787,86369537413,
   61696891405,36546363841,16225175977,2229316781,5995092330,9815350966,10694608158,9861872552,
   8216771662,6349676886,4604275746,3146477090]
private def pvm_w0_7_p3 : List ℤ := pzig
  [2025190550,1220602280,679520974,338959050,139958720,34114730,14738639,31567961,32362915,
   26571565,19246083,12711077,7746025,4356953,2238095,1019543,379621,80105,36760,65984,59650,
   43302,27668,16048,8526,4122,1772,640,154,13,39,25,9,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_7_p4 : List ℤ := pzig
  [0]
private def pvm_w0_7 : List ℤ :=
  pvm_w0_7_p0 ++ (pvm_w0_7_p1 ++ (pvm_w0_7_p2 ++ (pvm_w0_7_p3 ++ pvm_w0_7_p4)))
private def pvm_w0_8_p0 : List ℤ := pzig
  [0,0,5,13,17,15,7,5,1,1,29,43,21,9,8,21,27,1,5,9,45,57,33,12,38,0,15,5,2,10,5,35,21,7,0,5,23,7,
   52,16,53,49,30,76,42,17,31,27,8,24,3,89,69,16,56,38,28,13,45,59,7,42,30,27,15,68,22,67,21,26,
   5,85,49,38,70,40,26,23,87,45,26,8,21,29,29,72,42,63,139,35,6,26,38,14,88,125,106,55,373,1276,
   3231,7284,14561,26874,46477,74456,109315,142958,153119,92588,126976,654451,1720344,3650553,
   6858180,11796229,18838098,28055807,38869944,49563651,56708524,54632125,35174000,11890674,
   97316323,229370044,409318361,626101004]
private def pvm_w0_8_p1 : List ℤ := pzig
  [851857487,1040924240,1135250131,1078158524,835499109,418768770,99721112,591335845,903025440,
   913473571,595050636,50952503,502346135,817044428,734487615,284620516,302091158,700596115,
   675237228,237266793,336976719,666874040,523716945,8521476,497003794,603347911,223397686,
   332797342,591932519,321563026,239463892,567525557,338896756,229377924,557859205,290550952,
   295752352,549483775,167550256,414886760,494556693,42309939,527847746,326702477,311442003,
   528439500,11329647,524598247,303908374,366518054,489553129,136648637,553603064,94150513,
   520716161,283922870,429668062,418444029,316479583,502008486,207214374,547598039,117477081,
   569719688,55073754,580327351,23303557,586972872,23546312,592128265,56607723,592941246,
   122662632,581170191,219759063,543578994,340973790,463574977,470662967,325264088,581076744,
   121028763,631915857,137348687,576835618,406898084,381053441,608713903,50423852,643037910,
   337500036,434640305,627951143,7686518,634029862,472028218,289991845,672139243,332417877,
   521473990,539069128,446377314,1000874107,186180846,1644060177,3033473506,3488066493,
   6952796220,10987335745,15433748834,24283593989,34554300638,46951497283,64130373018,
   81390969989,99102957260,115892634843,124611147180,124754802595,111749915608,81765953301,
   39696075218,12448117194,64382424349,102196313806,117968049305,101188856260,55690358923]
private def pvm_w0_8_p2 : List ℤ := pzig
  [5338835961,64233817692,94389190291,85897110132,38715012485,26168790007,74472727484,
   83638092953,42118977188,22847073938,74696859007,78069014252,24651659329,42126732877,
   89367326264,53869037771,2990427953,93302905992,60702718119,42131671424,110409745332,
   34938672799,108519494930,173439559580,52815823002,238343701256,343979369746,274434939918,
   524835723368,742981095706,784092585072,1156304999128,1601927797726,1879147172318,
   2487841293900,3338496306950,4082555590758,5140404501886,6655478608892,8235005524234,
   10108164158558,12648145670286,15569014572464,18824346990920,22877020598234,27725621398682,
   33109244009290,39317580449432,46666331818264,54939573993716,64063375874424,74404663619802,
   86054543135042,98725163969364,112433403099030,127459084466952,143705409450948,160817248557918,
   178767300193108,197697956133834,217370139555294,237323270542596,257406515009128,
   277649441442562,297747472803618,317147793422924,335567437747958,352994487654032,
   369196897061700,383639509019458,395955924704806,406155988798536,414236492236106,
   419877546039460,422729555368666,422810460110842,420384197958960,415537513603210,
   408115660140956,398089945533594,385790226238414,371674564582300,355983295028330,
   338748138985266,320105353949332,300471882555092,280366733035208,260123087031604,
   239836828818020,219576562856872,199582440486242,180235195817018,161855591476532,
   144558877860550,128296095682952,113013223414544,98766153630792,85702152264590,73949754044892,
   63522777432270,54308776466816,46134634737186,38851592069280,32384442867006,26725630830488,
   21891127453952,17870681410010,14599065842604,11957865951010,9801010609850,7988705678988,
   6414777562102,5018723247894,3781663181800,2711379548386,1824031505634,1129168655350,
   621688843468,281072306526,75830206266,29840670341,69861317687,72121725685,56786081029,
   36599994437,18370642721,4820411919,3733429022]
private def pvm_w0_8_p3 : List ℤ := pzig
  [8126871994,9555569180,9150804068,7803269900,6128694886,4501548348,3112877762,2029305490,
   1242841588,708122640,367336388,164870332,54368742,818488,20177887,24391303,21244463,15861935,
   10683581,6615875,3785447,1990399,943223,382785,112089,796,36064,38166,29342,19310,11414,6158,
   3034,1344,522,166,34,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0]
private def pvm_w0_8_p4 : List ℤ := pzig
  [0]
private def pvm_w0_8 : List ℤ :=
  pvm_w0_8_p0 ++ (pvm_w0_8_p1 ++ (pvm_w0_8_p2 ++ (pvm_w0_8_p3 ++ pvm_w0_8_p4)))
private def pvm_w0_9_p0 : List ℤ := pzig
  [0,0,5,13,17,15,7,5,7,1,16,7,19,41,41,4,5,15,23,21,6,6,0,37,73,43,6,16,14,13,15,10,18,0,9,37,
   27,16,8,43,39,16,68,12,49,57,6,38,56,38,21,65,10,50,24,49,71,47,15,26,48,60,20,89,51,34,30,49,
   21,58,56,29,43,38,38,37,53,37,71,32,70,76,8,37,71,21,80,57,79,86,489,1588,3517,7254,13953,
   24532,40607,61648,84249,97260,74769,33785,318898,927331,2078574,4072445,7272510,12047595,
   18643966,26959827,36205628,44457507,48160670,41721227,17421364,34014216,121842575,252469722,
   425444627,628969694,836397549,1005892264,1085603727,1025770706,796810807,408900312,75003444,
   542192433]
private def pvm_w0_9_p1 : List ℤ := pzig
  [855872682,901696443,641375410,149209633,393948301,761331862,780628429,430107390,126160890,
   601201769,732132920,438295907,109364001,571601170,648377735,286296594,264074820,606928997,
   486784786,4967848,479511833,549025296,153075199,367892077,549773962,222019951,311888841,
   536157680,221771341,318711003,520791482,158902781,379043339,486824102,28657527,464936725,
   394830716,166189824,518872509,201426218,383534350,455128149,97069127,516407072,203659115,
   405213579,420829780,193111880,516442707,43232794,500413038,248957225,407224591,397826944,
   275697036,486848603,137283601,526812588,12247526,533832019,89243108,523775904,163967479,
   509499617,212321088,499970844,235678429,500309027,234701192,512013424,208564387,532964911,
   155058268,557099182,71605699,573932245,42705601,568483750,183967224,522280667,339867161,
   417385484,484941050,240500907,585230659,4653892,579587410,287494906,488777839,452820167,
   84491880,809221422,167940441,78106180,1527745717,1916305940,2206509519,4837780160,7651880169,
   10448224348,16533477945,24593446146,33357962773,46114971986,61692529717,77071276468,
   93979159021,109687033868,118557766627,120409851218,111683899385,87604702376,51760698177,
   6755169558,43126741750,84672560933,109025232312,109838790649,80936350602,30628587279,
   26699195017,75247964254,93932879309,75670480492,27977294299,32382181649,74971630718,
   79052950835]
private def pvm_w0_9_p2 : List ℤ := pzig
  [42825595618,18361533438,67694310329,76083853686,37683601069,27607748171,73995836318,
   69952568201,15447032166,53856135636,82275426025,48230208542,27277511638,82985423159,
   68917868484,4108654316,78313017599,81062149454,9671619741,73889594365,88152357806,11700234363,
   72942379003,92615225100,756094568,73181292293,97061553648,34331440276,62818423947,
   108457615718,103310423190,12651676181,149617403142,237755531066,138461828448,284166358128,
   503754874962,506863899436,660599952452,1049027703252,1300953931348,1574976170146,
   2188554335534,2885147911504,3541204587880,4528066441790,5893505950882,7357104235550,
   9079513122858,11395375706728,14179137108374,17285601767438,21025136194296,25630203188600,
   30922068385122,36877025984406,43844033109760,51971157591866,61059396153204,71118777552920,
   82465877571850,95177917440824,109000917574328,123870769189872,140011952036050,157430270527196,
   175772819002354,194805211971504,214604557509920,235121167911996,255918275086116,
   276553288118194,296918056324208,316956253800592,336269264815572,354288599054656,
   370720739883644,385541187110600,398578899817766,409376761492756,417542345948816,
   423041436638472,426009379042126,426391817773040,423944879682002,418572830490364,
   410516007202796,400146406425614,387666845726028,373101568876974,356556350228292,
   338396831175742,319132565756226,299163009388550,278677328339926,257790435456078,
   236733911445950,215892131582484,195663522579268,176300570746024,157876178322312,
   140384369404200,123866663461606,108456545434004,94322337512810,81570748155038,70188889697792,
   60059118909870,51025657341208,42964451904938,35816919738774,29577567902420,24252392760450,
   19815829449974,16188173758602,13240689739900,10821513798214,8788088303024,7032422031374,
   5491449958940,4142182125250,2986867052710,2035482528714,1291744363106,745870145372,
   374178851038,143430121684,17044302968]
private def pvm_w0_9_p3 : List ℤ := pzig
  [39228817717,53580108537,46656292075,31879176703,16820099105,4922758683,2909695254,7096103536,
   8568761182,8310331104,7135953730,5626506986,4142024922,2868856266,1873731028,1151334010,
   660308964,347309570,161004734,58730486,8395876,12252627,17526503,15935295,12092363,8199277,
   5092823,2921303,1543505,740139,309727,100525,11503,18336,22598,18046,12024,7126,3842,1896,854,
   348,124,38,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_9_p4 : List ℤ := pzig
  [0]
private def pvm_w0_9 : List ℤ :=
  pvm_w0_9_p0 ++ (pvm_w0_9_p1 ++ (pvm_w0_9_p2 ++ (pvm_w0_9_p3 ++ pvm_w0_9_p4)))
private def pvm_w0_10_p0 : List ℤ := pzig
  [0,0,5,13,17,15,7,5,1,17,5,10,0,20,11,45,33,17,2,7,23,19,21,7,32,14,27,59,61,27,16,10,11,7,5,2,
   38,12,23,53,1,30,8,61,57,12,60,16,3,45,57,11,66,82,0,49,19,18,60,2,31,31,51,89,17,100,80,23,
   61,14,34,31,91,42,40,4,7,4,4,32,9,174,615,1308,3107,6076,11199,19582,31161,45274,57711,56648,
   16889,109341,405052,1003641,2100578,3958545,6889210,11194443,17044966,24270287,32046696,
   38496321,40250034,32107063,6996908,43468740,127554787,250878372,412891753,602971248,797354135,
   958743360,1040552881,997051894,798796487,449872258,474291,453180745,787833872,891107199,
   708794652,282565439,244236917,667128730,801855115,575943318]
private def pvm_w0_10_p1 : List ℤ := pzig
  [83134633,440199337,722813434,606062587,149122070,383432330,666373607,517960432,33057905,
   460258949,615789162,320317419,206214793,559522904,460273173,11346219,462191868,505640097,
   101934298,386594462,507945267,143796348,356215218,494936277,125759588,372895782,469485341,
   51012762,424067042,413562971,80480361,479481716,295966977,255460787,485942854,91447187,
   424705587,376430898,183047296,492460619,112445478,429575248,352134491,243292677,478339998,
   9917218,485146345,206503952,399816908,368418999,261602075,464246868,106549080,500540569,
   39753224,492930202,163267245,459102839,259218698,414701054,328715647,371685101,375623110,
   338257134,404228151,319490179,417722612,318082990,417409037,334722497,402118900,368612398,
   369331459,414820775,311158800,472732344,234158603,508226361,89352930,591828188,38251471,
   408224941,446707859,894553812,334197189,855644362,2476000521,3280534822,4400163469,7800533136,
   12034251909,16518219024,23880739161,34178439154,45309140039,58598928238,74835549665,
   90388809366,103439793485,113919345970,117207198463,109208900112,90694053043,60713328826,
   19192451065,26265436977,67647907774,98755115573,109313424692,93683579703,56469925630,
   4584236363,48841183243,83867074202,89260347257,63305537726,11963285449,42783603343,
   76049324816,74890743253,36762168082,20726040750,64978575807,73618753872,39935096963,
   19620029441,66124298026,70590438769]
private def pvm_w0_10_p2 : List ℤ := pzig
  [28829802792,35432927888,75223019441,61018502010,1753071017,62331320917,78629480846,
   31833390981,41687296695,83939899076,54210143921,24187798135,82272336794,67852135901,
   11932921553,81655326422,73067346253,7399995583,83577500000,73099608529,13557373967,
   87290957732,67018872621,29557558879,91609279940,50425798733,52242523329,91457583894,
   19802076467,75410826697,78496629732,24663646312,86043886405,47322147174,76213330918,
   63429237969,7008396242,122554661162,15488630576,3294228527,162470716654,169149550038,
   97068120092,248407065018,424053724854,428406955176,546455105982,883389000850,1153422937584,
   1377223858366,1863500757584,2553848691086,3216750786332,4024856294868,5243544197408,
   6741950733626,8377617025046,10408028003286,13067380832340,16214814896696,19773228669446,
   24041304484084,29251974820026,35275074928966,42044765680754,49854963637694,58948446039220,
   69196176948108,80467014516716,92973528608734,106945863747344,122238954460000,138579620886238,
   155990309189752,174631254746856,194347955173802,214708384770100,235450983881732,
   256582149282682,277978636283136,299164247275786,319617529079894,339112810756266,
   357576737815692,374714428482888,389988294288988,402973553052118,413568594226458,
   421783900236142,427440785059140,430204601484940,429890361837866,426625811335428,
   420678014992726,412188824844372,401147578517760,387606477372778,371858251502394,
   354371662058444,335574033063048,315722206716612,294976284066490,273567346062662,
   251874520603186,230343270855874,209335584659838,189049145500078,169560217068748,
   150933560204148,133300722509290,116851906607746,101761639628336,88111947086298,75866377259060,
   64905073545534,55091525016690,46328965034072,38578832032652,31839827487690,26106695761732,
   21333787708176,17420783805494,14224002380752,11584623572286,9359800469736,7444484939826,
   5778117249246,4337310882658]
private def pvm_w0_10_p3 : List ℤ := pzig
  [3120357595558,2130629586612,1364313141882,804864496654,423681203576,184711658478,50310339020,
   13758641983,35240471271,34350306865,24294555217,12662891195,3075989023,3319429454,6700482588,
   7794989244,7428341820,6301970302,4918370716,3586288978,2461018084,1592917540,970430146,
   552357528,288996614,134046468,49913210,8884566,7891949,12309583,11299479,8538387,5737307,
   3524253,1997801,1043529,495607,206529,68055,9837,9620,12642,10106,6658,3890,2068,1012,458,188,
   62,16,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_10_p4 : List ℤ := pzig
  [0]
private def pvm_w0_10 : List ℤ :=
  pvm_w0_10_p0 ++ (pvm_w0_10_p1 ++ (pvm_w0_10_p2 ++ (pvm_w0_10_p3 ++ pvm_w0_10_p4)))
private def pvm_w0_11_p0 : List ℤ := pzig
  [0,0,5,13,17,15,7,5,2,6,23,5,5,11,20,24,8,23,41,27,1,15,5,11,33,39,5,18,28,16,37,73,37,25,4,1,
   1,31,19,16,54,18,29,65,12,48,0,47,55,21,10,32,64,17,71,65,4,72,68,13,47,18,20,4,8,64,9,83,151,
   5,88,40,93,190,383,994,2189,4234,7879,13452,21163,30048,36067,29252,11426,125843,383370,
   894685,1823946,3392019,5861888,9491867,14429516,20531929,27094486,32493769,33794336,26423961,
   4097794,40763352,115851913,226840386,374336293,550369706,735411377,897435106,994762111,
   983983904,832869845,535865734,127145323,315621015,683001450,863089353,782798194,447011105,
   43812449,513986420,773715023,702716926,319106695,207819133,622646338,708559503,411974194,
   108345552,553380117,653819974]
private def pvm_w0_11_p1 : List ℤ := pzig
  [343437565,180664469,570415534,557326029,149544384,356382328,581418813,352300152,149788262,
   517686577,445609380,5143396,441633949,473953438,71454329,391144897,471705118,88913631,
   378407101,453853478,54401741,400445771,416993448,29713908,441783047,343296510,159160030,
   471389359,208950954,313669812,441573007,2540658,441490176,301348825,245661809,458704268,
   35223323,439754501,287664792,282427140,439448403,58142505,469917876,163917431,397560711,
   336893104,259877454,440721863,96058893,476809844,63270597,459205535,199516914,406532468,
   305074637,336522827,380224186,263320598,429784517,196735561,460145498,143192506,478225473,
   104996001,486786262,88526210,498062961,77239683,479899576,134097008,547110611,47264403,
   315404784,490383102,955332513,556100578,941055765,2538404266,3794391999,4900718566,7837501239,
   12452935314,17370236255,23817370366,33497031849,45077696032,57357752693,71595972136,
   87071888003,100101381194,108967789423,113014878090,108399821489,91955926502,65165085879,
   29771319108,12574783178,54683202317,87016563276,103889376057,100408969038,73136263527,
   28022057346,22336968290,65875457955,89012311516,80998291967,44984869216,5514513872,
   53627044893,78657311520,67361267825,26211865494,26232399116,66334268631,70768494466,
   35872026563,17811521183,61855839870,69658223761,32524945018,25530456732,67027610033,
   65250284676,16910599871,45445316987,74818164570,49952583881]
private def pvm_w0_11_p2 : List ℤ := pzig
  [13976488059,70162601166,70438991407,13462571312,55706191562,80778386485,35249345740,
   42838344878,83147704047,49158161688,32549234494,85185817165,54844400928,29192735680,
   85974573209,55608105170,34300520076,87694396975,47838344310,45074628930,89168375419,
   31113431504,61926337212,83467903845,5688903990,79867213126,65902913921,28863663937,
   87934578768,33013541635,65028750655,75228048560,14449994970,85648407289,35454136920,
   62695048884,71396498331,23615543699,84494911026,15366766923,70648367661,57033702686,
   60110753526,59768262079,4478815155,107461125382,33036899334,24323801903,106940772596,
   179336032118,102932385842,150595199120,351218589912,442212870970,464284509258,686409587258,
   1046207601630,1315089474974,1618131267928,2210281024098,2994704812892,3783171044960,
   4750843951248,6161366619556,7929607690510,9895953068942,12259001050618,15318629533520,
   19037918480436,23265426182996,28182980593826,34131742936154,41147914402168,49062668668612,
   57968022813664,68198229717046,79864884164828,92765120631634,106804450544672,122189514927932,
   139066078976204,157216816597384,176307277430626,196257294883352,217138164357072,
   238776730470838,260693547039794,282456838162420,303906247368738,324930950958978,
   345158491772504,364014382652384,381058217214802,396128678436914,409127719563432,
   419768554742214,427629496630050,432431384310716,434182749916580,433033463484728,
   429042060368366,422138016883288,412301991606390,399738284285312,384848391156726,
   368048837404394,349630222733564,329784471351112,308744013731762,286878599828044,
   264658110505520,242523930812844,220784175120696,199610220521794,179118613006852,
   159459969009786,140845896001214,123502731776120,107594595248678,93171961019406,80176162509934,
   68490754464760,58004913631468,48653796570736,40419917821606,33302996192060,27280069412280,
   22278015263086]
private def pvm_w0_11_p3 : List ℤ := pzig
  [18170297043654,14796336213150,11992324741882,9619787587208,7582010499346,5825281337366,
   4328142471480,3085205887904,2092093539500,1335746699686,791291760186,424199392720,
   195282108750,66099051548,3112692092,20078103043,22317188293,15741947855,7269335823,196896491,
   4404272806,6642323334,7110941190,6487772422,5341399428,4068875664,2903493312,1952145368,
   1238356480,739179404,411881452,210612904,95135994,34136582,5343354,5895805,8518563,7549275,
   5543933,3627073,2170165,1197845,608593,280549,112945,35435,4205,5558,6672,5106,3250,1846,952,
   450,192,72,20,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_11_p4 : List ℤ := pzig
  [0]
private def pvm_w0_11 : List ℤ :=
  pvm_w0_11_p0 ++ (pvm_w0_11_p1 ++ (pvm_w0_11_p2 ++ (pvm_w0_11_p3 ++ pvm_w0_11_p4)))
private def pvm_w0_12_p0 : List ℤ := pzig
  [0,0,5,13,17,15,7,3,19,12,6,13,1,9,19,15,2,18,40,1,27,25,17,21,3,8,9,35,27,49,0,32,44,0,31,51,
   43,37,6,6,7,37,55,16,70,32,29,61,12,24,8,0,33,61,49,18,48,76,11,83,91,46,36,36,43,112,227,562,
   1309,2556,4519,8060,12865,17982,21243,15148,15248,99209,288264,666673,1362132,2551097,4452472,
   7294133,11235220,16225115,21780060,26677949,28599156,23792125,6907274,28792368,90599753,
   184701798,313634431,473124104,649033263,815629928,936732541,971125450,882749029,654398708,
   301341057,120803915,520089518,788083609,833908496,623231929,206333560,281967902,660324727,
   770498492,553109499,91892788,405645962,696577279,626314824,223797777,294654869,632990018,
   587164085,180843406,331010946,613420469,474209954,8466735,451664549,568220094]
private def pvm_w0_12_p1 : List ℤ := pzig
  [253145819,249928441,542367862,387177873,86234893,475421334,442510603,16933004,415506624,
   454442539,62392114,383658980,444937837,57977666,383966748,420151213,8493444,409491260,
   372554283,83459479,442505142,285160283,210114859,452156332,140343303,346749459,396301210,
   63111948,441666877,236976330,286678366,421927741,24923789,438684558,231842143,309016997,
   402216400,97102034,453449321,126184306,395227238,307243191,261874383,418613970,94189910,
   456491103,73076142,432798654,216942131,366521039,326421412,277427736,400607037,180919335,
   442495456,91928948,466254853,4873903,456217970,32288781,501604525,167024908,342300112,
   69572116,796916093,715984548,477681741,1361526358,2848565869,3832290226,5167325283,8322347238,
   12770814991,17571176708,23929960987,33199935070,44318298553,56099918000,69353874747,
   83889591408,96695094493,105371161180,109355491263,106415961652,93022802097,68957990720,
   36807434757,1469204091,42068268138,76720010785,97578574088,100805316817,83887322290,
   47207183271,680043051,46393232540,78520432063,87436539118,67449884651,24663192636,24695442746,
   63684558209,77586671222,58068259161,13038509834,35995084152,67500953699,66356856138,
   30196899985,22200058575,61069774432,65845481131,32681994000,21856245804,63261426585,
   63763062512,23443302363,33527101661,69914001540,56826146061,2087384692,54473847014,
   72567862817,35709264816,31475079470,74422411675,57651653856,6205835868]
private def pvm_w0_12_p2 : List ℤ := pzig
  [67559083147,72360388110,12677545067,58537464535,78405787112,27148365677,51957478767,
   82281125260,32675270605,48806729925,83572026532,33509466635,52816976959,83328310602,
   25806056435,59980826827,81351696344,10744012365,71850625931,71638152130,11308891900,
   82026818371,53465360904,40547234668,83266591251,22400730112,67556414452,69720599229,
   20044492785,81583179556,34018382117,60393115375,70510707658,18937112230,79694380795,
   26558244620,66120005100,59726937645,36100168285,75897298520,75540893,77216977739,30601288042,
   63057099992,55895396327,43414531161,71263243196,22274914998,74517580739,5521356562,
   84045194874,10532592573,58762330169,58004602634,99066588564,3425802915,3634642266,
   150264966376,185260187674,116270679656,200826748530,418405930204,526165497844,574530506100,
   825791127130,1250334289572,1617248073126,1991770498370,2655088240318,3612642941190,
   4649498242866,5819535109744,7433965477378,9579935202680,12073954688724,14927946970276,
   18467895717876,22897591730652,28096313333716,33998966115046,40877743978190,49038707203552,
   58461654697262,68984415999808,80701117588704,93907317230282,108690095530244,124823543186340,
   142114457829190,160635862843086,180490828805644,201481090000156,223175025254264,
   245254117585510,267625449088278,290158437214830,312441744679890,333900508895308,
   354102343798118,372846067299104,389946589148254,405026501089086,417587700643548,
   427265151575496,433954493657570,437684969447776,438415238525224,435994506401772,
   430318441250266,421493551705574,409835465090770,395716682123118,379425478866528,
   361163258935994,341157930093560,319766640610126,297468562898762,274758157114076,
   252031649311382,229551576861780,207500699859734,186067893778962,165495320499398,
   146056122811528,127985631951122,111417181002090,96363253395966,82748840791910]
private def pvm_w0_12_p3 : List ℤ := pzig
  [70472354106618,59458236179504,49676337124810,41125134811770,33794811905158,27633075045760,
   22530865260054,18332547163462,14863307062610,11960537400160,9497056314302,7389811367808,
   5594557696332,4091827300302,2871008422360,1917967355716,1208801937488,709529885428,
   379751364986,177823617062,65541889932,11213184654,9122963369,11988614663,7692888413,
   1920552417,2730639446,5492131520,6520328180,6321168300,5432001304,4279450946,3142637056,
   2169607186,1413354318,868713052,501777568,269739978,132230218,56416550,18176508,1190484,
   4777887,5674049,4663251,3250681,2034177,1166959,617381,299793,131169,49265,13557,277,3268,
   3234,2276,1364,734,356,152,56,14,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_12_p4 : List ℤ := pzig
  [0]
private def pvm_w0_12 : List ℤ :=
  pvm_w0_12_p0 ++ (pvm_w0_12_p1 ++ (pvm_w0_12_p2 ++ (pvm_w0_12_p3 ++ pvm_w0_12_p4)))
private def pvm_w0_13_p0 : List ℤ := pzig
  [0,0,5,13,17,15,19,2,13,23,10,1,3,1,2,17,11,21,25,4,38,26,2,11,11,45,11,7,6,0,3,37,51,51,2,32,
   30,24,19,43,47,57,4,22,16,51,83,0,60,40,17,7,33,8,10,50,33,34,185,174,585,1286,2225,4082,6767,
   9738,11921,9138,7666,56775,171752,409339,859816,1654301,2965108,4990505,7907374,11772573,
   16359090,20910435,23825002,22317893,12156396,12361694,57973897,131332908,237057287,375021138,
   537308663,705723914,851161249,936287294,922571219,781512980,508017279,131700746,279542916,
   628950745,815211776,767602911,480768688,33225047,424874627,719300872,722631519,419859310,
   66532056,515908929,707668008,536936051,85111126,405576994,656407341,515764566,64033249,
   418449239,619562466,403219263,84627215,501589238,546154217,184716200,308490606,549949791,
   347804218,132826284,491797519,424475180]
private def pvm_w0_13_p1 : List ℤ := pzig
  [9876474,426164421,448623140,57081719,380741915,446167146,75183001,364815335,429468982,
   50924647,376668307,398189994,12487770,406318833,341912394,112028218,434426057,244561372,
   237361188,430739227,93319398,361050378,357958877,105784561,432604886,188095753,309325539,
   388267404,66693128,430390483,188341888,323529912,369860543,124336617,436497776,96963909,
   390444265,282598896,262401950,399375379,93671109,439092136,78318397,410858683,225614502,
   336185372,338842083,227452085,398412852,133608578,464702003,33434702,364853720,52974760,
   660670703,547776042,229376863,802163964,2007020555,2813109800,3547166229,5563167264,
   8977518991,12799235644,17301162701,23994846184,33078554657,43289550564,54439992615,
   67396031142,81246836851,93281426920,101884963289,106442946786,104617738125,93286486220,
   72096525483,43007827554,7648864559,31047963381,66292450946,90488317411,99168881484,
   89805673303,61359648820,18556911065,27473213951,65019128772,84818521129,79672614430,
   48896876749,2842744990,42130005220,71186186831,73195442702,45072349529,1779739359,46047406822,
   68858404427,59945580388,21256312947,28573666603,62252005782,62092220213,28344334254,
   22371626672,61029636185,62080474412,24355211777,28503953777,64372911780,58580239853,
   11517512484,44567678970,69333950711,45253247636,12732372008,63765117555,66427304598,
   16518373843,46696635325,74007480724,41652464863,27611292513,74654503972,56969454571,
   10322940655,69887694012]
private def pvm_w0_13_p2 : List ℤ := pzig
  [67831099805,1788385664,66951385068,71937385367,8325426484,64692707002,74844939135,8042416374,
   67300451980,72539965893,2180426152,71819436064,68358889007,11648901627,77953724092,
   56211905613,29490465525,82026581876,36971715109,52513873545,77208156250,7973141193,
   71412246955,60799932572,28419533838,79457982217,26431618398,60961474932,66793425085,
   19265461663,77746600904,27118037189,60654951143,62133114262,27027790062,75952107113,
   11479960366,68909512992,45368844907,48475437685,66555969406,20518663122,73856558029,
   9599342318,71442376510,34379656385,59841682247,53366548670,42840557488,67638410565,
   26593315877,73428843810,7990957706,77185905781,7502214544,78057711626,18524302953,72105181611,
   36650686052,81422201882,27712583511,53548546415,72742279230,109746108110,5800248528,
   8613719672,166744111730,236363999112,175429518826,237446770306,485784926224,685009677902,
   775340391978,1012621263872,1513712212334,2074297963510,2595774205906,3322609308866,
   4460723300192,5882161567274,7444928710372,9347161049512,11893590422336,15095338203316,
   18794637464972,23086417050156,28318155913390,34679286670036,42063697235808,50413716809130,
   59971898970366,71040410104484,83636520229226,97571113729216,112804029767652,129523508399796,
   147838956430542,167547449565366,188299122382820,209901502325858,232329761718990,
   255447314940002,278833843636724,301945954192238,324385684860828,345935634127126,
   366345669198536,385166009384414,401838215459006,415928887731818,427236517034900,
   435674390658988,441091762191302,443243047498500,441930542673682,437159697972134,
   429149978845186,418204576258804,404576063665076,388448993485912,370035062416918,
   349674737975476,327846863860252,305078522415226,281830365746198,258441965277686,
   235163975256558,212235889453052]
private def pvm_w0_13_p3 : List ℤ := pzig
  [189942119008134,168605423816070,148526704735402,129915417796146,112855368755162,
   97323098700364,83243000174216,70545344023684,59197619500916,49198936468804,40548087508116,
   33207084383376,27080106227270,22016772449274,17835883216268,14357570983456,11430709126274,
   8947070059244,6840614393882,5075978276104,3632800288356,2491946917906,1627179489028,
   1002914866100,576621071150,303503763876,141317759692,53908111044,12965196726,1849524463,
   3899372229,1114454883,2387227796,4891614210,6020288034,6010621600,5287394236,4245754634,
   3168898162,2219985976,1466950102,915586488,538695776,296931384,151330306,69356674,26685310,
   6635976,1385637,3621417,3461645,2574267,1671217,983787,532449,265365,120629,48653,16143,3201,
   968,1696,1352,852,462,222,94,32,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_13_p4 : List ℤ := pzig
  [0]
private def pvm_w0_13 : List ℤ :=
  pvm_w0_13_p0 ++ (pvm_w0_13_p1 ++ (pvm_w0_13_p2 ++ (pvm_w0_13_p3 ++ pvm_w0_13_p4)))
private def pvm_w0_14_p0 : List ℤ := pzig
  [0,0,5,13,17,15,25,9,8,27,11,2,0,9,8,1,11,9,13,35,27,6,40,8,22,0,19,35,19,15,6,2,8,7,55,55,35,
   7,46,24,24,7,41,55,63,8,44,10,93,45,15,56,11,102,203,360,805,1570,2797,4668,6719,7920,5269,
   9149,49794,144593,341996,718529,1387688,2502045,4240538,6769481,10157562,14228945,18339132,
   21078289,19942172,11055425,10902025,52357506,119874729,218389164,348669221,504362028,
   669411951,817067730,911893653,915891400,798826085,551093466,195383725,208198715,568851706,
   786244821,783338552,541235247,121215498,340808284,674227025,739812778,497091559,39143324,
   431939934,690497017,600736928,200068813,302328131,627232118,583259061,191119734,311473008,
   605804599,497184658,55921237,414468233,580058182,319435811,173658993,522787204,455225151,
   25365374,415394238,499713167,156723976,314864714,497462879,227122006,246715454]
private def pvm_w0_14_p1 : List ℤ := pzig
  [480189999,251161760,217804456,463737777,239521968,226494772,450821081,195750432,267004596,
   433764811,117810466,328724078,396371893,3049802,392427972,317054003,143283853,426679518,
   176952733,297057199,390228720,24146728,407587033,247851570,247407936,405587453,2436462,
   405510116,239788955,270508575,390198510,62053158,423913095,151711720,351179422,318247005,
   207041369,411126806,31834592,424075663,132760460,380298406,281336055,265747899,338962466,
   215651958,505250879,101578388,185026942,345065856,1087663167,1233002598,1303880837,2381620066,
   4330610949,6247852428,8414523519,12169518030,17831225479,24492293544,32109260467,41869488284,
   53920728945,66649325390,78851044557,90471749056,100305586099,105235076604,102881649431,
   92853780790,74652556539,47317424834,12514955699,24638248359,58696783824,85031375215,
   97978277512,92297666633,67793740716,29751011259,14376057971,55231316274,81058743975,
   82871842178,60259663147,20248395972,25865024324,62808298625,75563002124,58745845759,
   19769112934,26352368404,61313466833,68321845552,42651220327,2798942681,45754476806,
   65757255935,51255501782,7804897569,40089875553,64218895666,51066289175,7303816082,42579054348,
   66243324579,46185015912,4543046918,52629310999,66262323394,33416321867,25325770297,
   66327574112,58177202649,6556053910,51592186874,71419440079,33627941974,32719819054,
   72432754327,52642190778,12039988214,68689653371,65510903786,2768976371,62619750983,
   71461878328,14369408943]
private def pvm_w0_14_p2 : List ℤ := pzig
  [58266702011,75728272802,18360469743,57003332645,75871868262,18476279565,59552961051,
   75743294170,10664516235,65288376597,70623313336,1315811276,73094372987,61664776522,
   21183569396,78338504079,43867923504,42722590656,78454332311,17131554246,64941786476,
   64635922635,16688357683,76882178820,36843440595,52255051677,70239947098,6020878334,
   73357029251,39883996282,49979728698,68222144407,11325227079,73255195836,28711845279,
   58614814053,57986753626,30938051034,71341138179,2186555364,70553608894,32116876849,
   58415113161,53772870102,37759804090,67719888063,14733240589,73674506786,6667205609,
   71244371537,27235960782,65430844544,43732732165,57207456265,55324092032,45735856602,
   66378849115,37261937093,72154127194,27707974900,76990308319,19008269941,83710626472,
   18880183162,78153666943,2344102421,101296235456,32571352026,58029185653,32248732930,
   157776960586,114305657970,43512564256,165331546822,363148425696,416715049244,432774569282,
   663118103662,1059689503488,1391928609670,1702580470976,2272811527682,3171078009088,
   4195646741796,5303229076862,6768893560720,8811200067820,11335128490872,14221240741250,
   17663403358258,21998272590772,27319414813306,33500135284550,40569662421376,48835521504118,
   58568379326714,69742910534176,82214929130570,96043044974176,111468497112960,128592153455074,
   147217212505078,167061803394554,188020171967792,210110133846936,233195053941722,
   256861513455718,280602860767162,304058221585256,327011523192938,349179946836474,
   370075311463772,389109776954326,405817105506134,419942612770412,431327533961710,
   439745845084538,444883810935776,446479705414928,444472772396476,439016329189278,
   430357217561290,418708183144888,404228042453488,387110012129758,367681030123796,
   346416420870378,323856475360436]
private def pvm_w0_14_p3 : List ℤ := pzig
  [300492532883616,276705261662406,252787123191342,229014771995660,205706810449744,
   183222732232562,161906308306030,142014103489202,123674786600858,106900524691582,
   91638629110916,77831051484000,65450548724264,54500182657388,44984191462158,36871251136224,
   30071014306938,24434621672638,19776867405350,15908603603482,12665926961206,9926779352390,
   7612432062224,5677327026338,4093766635500,2837721884970,1879686005984,1181599173270,
   698631692564,383568971336,191592905936,83958659730,29938027172,7102623000,413942562,692131884,
   2949394474,4906443576,5842313044,5801558864,5109066688,4113268420,3078540038,2162449552,
   1432816268,897124842,530134516,294204036,151710064,71115420,28808944,8596550,193674,2462063,
   2671431,2069893,1368869,813805,443373,222425,102133,42037,14677,3583,172,1002,874,562,306,142,
   54,18,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_14_p4 : List ℤ := pzig
  [0]
private def pvm_w0_14 : List ℤ :=
  pvm_w0_14_p0 ++ (pvm_w0_14_p1 ++ (pvm_w0_14_p2 ++ (pvm_w0_14_p3 ++ pvm_w0_14_p4)))
private theorem dk_w0_0 : muxFastIterBSlideChk 6 513 phbv_w0
    rkmViHi_m1024_r512_s1_c0 pvm_w0_1 = true := by
  decide +kernel
private theorem dk_w0_1 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_1 pvm_w0_2 = true := by
  decide +kernel
private theorem dk_w0_2 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_2 pvm_w0_3 = true := by
  decide +kernel
private theorem dk_w0_3 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_3 pvm_w0_4 = true := by
  decide +kernel
private theorem dk_w0_4 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_4 pvm_w0_5 = true := by
  decide +kernel
private theorem dk_w0_5 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_5 pvm_w0_6 = true := by
  decide +kernel
private theorem dk_w0_6 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_6 pvm_w0_7 = true := by
  decide +kernel
private theorem dk_w0_7 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_7 pvm_w0_8 = true := by
  decide +kernel
private theorem dk_w0_8 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_8 pvm_w0_9 = true := by
  decide +kernel
private theorem dk_w0_9 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_9 pvm_w0_10 = true := by
  decide +kernel
private theorem dk_w0_10 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_10 pvm_w0_11 = true := by
  decide +kernel
private theorem dk_w0_11 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_11 pvm_w0_12 = true := by
  decide +kernel
private theorem dk_w0_12 : muxFastIterBSlideChk 6 513 phbv_w0
    pvm_w0_12 pvm_w0_13 = true := by
  decide +kernel
private theorem dk_w0_13 : muxFastIterBSlideChk 4 513 phbv_w0
    pvm_w0_13 pvm_w0_14 = true := by
  decide +kernel
private theorem dk_w0_14 : muxFastIterBSlideChk 4 513 phbv_w0
    pvm_w0_14 rkmVoHi_m1024_r512_s1_c0 = true := by
  decide +kernel
private theorem ptail_ok : rkmAllTrueF [
    muxIntListEq rkmHbHi_m1024_r512_s1_c0 phbv_w0
  ] = true := by
  decide +kernel
private theorem pw_w0_1 : muxFastIterFullT16 12 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_2 :=
  (muxFastIterFullT16_add 6 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) (muxFastIterBSlideChk_sound dk_w0_0)).trans
      (muxFastIterBSlideChk_sound dk_w0_1))
private theorem pw_w0_2 : muxFastIterFullT16 18 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_3 :=
  (muxFastIterFullT16_add 12 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_1).trans
      (muxFastIterBSlideChk_sound dk_w0_2))
private theorem pw_w0_3 : muxFastIterFullT16 24 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_4 :=
  (muxFastIterFullT16_add 18 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_2).trans
      (muxFastIterBSlideChk_sound dk_w0_3))
private theorem pw_w0_4 : muxFastIterFullT16 30 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_5 :=
  (muxFastIterFullT16_add 24 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_3).trans
      (muxFastIterBSlideChk_sound dk_w0_4))
private theorem pw_w0_5 : muxFastIterFullT16 36 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_6 :=
  (muxFastIterFullT16_add 30 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_4).trans
      (muxFastIterBSlideChk_sound dk_w0_5))
private theorem pw_w0_6 : muxFastIterFullT16 42 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_7 :=
  (muxFastIterFullT16_add 36 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_5).trans
      (muxFastIterBSlideChk_sound dk_w0_6))
private theorem pw_w0_7 : muxFastIterFullT16 48 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_8 :=
  (muxFastIterFullT16_add 42 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_6).trans
      (muxFastIterBSlideChk_sound dk_w0_7))
private theorem pw_w0_8 : muxFastIterFullT16 54 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_9 :=
  (muxFastIterFullT16_add 48 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_7).trans
      (muxFastIterBSlideChk_sound dk_w0_8))
private theorem pw_w0_9 : muxFastIterFullT16 60 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_10 :=
  (muxFastIterFullT16_add 54 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_8).trans
      (muxFastIterBSlideChk_sound dk_w0_9))
private theorem pw_w0_10 : muxFastIterFullT16 66 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_11 :=
  (muxFastIterFullT16_add 60 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_9).trans
      (muxFastIterBSlideChk_sound dk_w0_10))
private theorem pw_w0_11 : muxFastIterFullT16 72 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_12 :=
  (muxFastIterFullT16_add 66 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_10).trans
      (muxFastIterBSlideChk_sound dk_w0_11))
private theorem pw_w0_12 : muxFastIterFullT16 78 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_13 :=
  (muxFastIterFullT16_add 72 6 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_w0) pw_w0_11).trans
      (muxFastIterBSlideChk_sound dk_w0_12))
private theorem pw_w0_13 : muxFastIterFullT16 82 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = pvm_w0_14 :=
  (muxFastIterFullT16_add 78 4 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 4 513 phbv_w0) pw_w0_12).trans
      (muxFastIterBSlideChk_sound dk_w0_13))
private theorem pw_w0_14 : muxFastIterFullT16 86 513
    phbv_w0 rkmViHi_m1024_r512_s1_c0 = rkmVoHi_m1024_r512_s1_c0 :=
  (muxFastIterFullT16_add 82 4 513 phbv_w0 rkmViHi_m1024_r512_s1_c0).trans
    ((congrArg (muxFastIterFullT16 4 513 phbv_w0) pw_w0_13).trans
      (muxFastIterBSlideChk_sound dk_w0_14))
/-- Certified `T_16` walk chunk `m1024_r512_s1_c0`. -/
theorem rkmWalkChkHi_m1024_r512_s1_c0 : muxFastIterFullT16 86 513
    rkmHbHi_m1024_r512_s1_c0 rkmViHi_m1024_r512_s1_c0 = rkmVoHi_m1024_r512_s1_c0 :=
  (congrArg (fun h ↦ muxFastIterFullT16 86 513 h rkmViHi_m1024_r512_s1_c0)
    (muxIntListEq_eq_true.mp (rkmHd ptail_ok))).trans pw_w0_14
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi1024T6`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi1024T6 :
    rkmWalkChkHi_m1024_r512_s1_c0 = rkmWalkChkHi_m1024_r512_s1_c0 :=
  rfl
private theorem laneRoot_Hi1024T6 : rkmHbHi_m1024_r512_s1_c0 = rkmHbHi_m1024_r512_s1_c0 :=
  (And.intro (Eq.refl rkmHbHi_m1024_r512_s0_c2) rfl).right

end
end QuantumComputation.Specs.DickeSol
