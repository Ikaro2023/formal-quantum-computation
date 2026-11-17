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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T4

/-
# High-`m` Checkpointed Walk Part `5` (`FindAllJohnsonRampKickMuxHi1024T5`)

Certifies `1` `T_16` checkpoint walk(s) (`43605` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Quantized generator list for `m1024_r512_s0_c2`. -/
def rkmHbHi_m1024_r512_s0_c2 : List ℤ := altBuildHbFrom 1024 512 51956407114 0 512
/-- Part 0 of `rkmViHi_m1024_r512_s0_c2`. -/
def rkmViHi_m1024_r512_s0_c2_p0 : List ℤ := let p := rkmP; let n := rkmN; [
  p 0,p 0,n 2,p 0,n 6,n 2,n 5,n 4,n 8,p 4,n 1,p 2,p 6,p 8,p 2,p 8,p 3,p 0,n 1,p 6,p 14,p 7,p 8,p 9,
  p 7,p 11,p 12,p 20,p 19,p 10,p 22,p 24,p 21,p 25,p 19,p 15,p 20,p 20,p 29,p 27,p 37,p 39,p 37,
  p 34,p 49,p 60,p 89,p 165,p 301,p 571,p 1087,p 2094,p 4011,p 7604,p 14285,p 26588,p 48970,
  p 89254,p 160997,p 287414,p 507886,p 888507,p 1538962,p 2639497,p 4483280,p 7542248,p 12568594,
  p 20749220,p 33938490,p 55005323,p 88345148,p 140627237,p 221874146,p 347004431,p 538014331,
  p 827030453,p 1260536044,p 1905159794,p 2855519975,p 4244739087,p 6258384612,p 9152748347,
  p 13278546871,p 19111301532,p 27289828746,p 38664427384,p 54356470723,p 75831174566,
  p 104985294120,p 144251369841,p 196719864301,p 266280075016,p 357780039732,p 477204744948,
  p 631870785933,p 830634202359,p 1084106538292,p 1404872281751,p 1807698784769,p 2309727634440,
  p 2930634353258,p 3692741393863,p 4621067823680,p 5743298052681,p 7089651631259,p 8692636721745,
  p 10586671492823,p 12807560531201,p 15391817488244,p 18375830589245,p 21794874256006,
  p 25681977762542,p 30066670293941,p 34973630649853,p 40421278680548,p 46420353851443,
  p 52972533545568,p 60069149268011,p 67690062275404,p 75802760849395,p 84361739108394,
  p 93308211694511,p 102570209847309,p 112063092443990,p 121690490912280,p 131345690071370,
  p 140913428668470,p 150272084534884,p 159296190862900,p 167859213112517,p 175836501479387,
  p 183108322582113,p 189562866794155,p 195099124981708,p 199629530595584,p 203082270110886,
  p 205403176443184,p 206557135660078,p 206528956279280,p 205323671743252,p 202966269196402,
  p 199500860316943,p 194989331534393,p 189509530436700,p 183153061622511,p 176022777960960,
  p 168230061690981,p 159891993782385,p 151128509503719,p 142059633449794,p 132802878840302,
  p 123470884347587,p 114169347808392,p 104995300754559,p 96035751610743,p 87366709470538,
  p 79052585315168,p 71145954007629,p 63687648867854,p 56707151447178,p 50223232452835,
  p 44244795657606,p 38771874962115,p 33796735343419,p 29305030920558,p 25276977435056,
  p 21688501688830,p 18512336505741,p 15719036204885,p 13277894047974,p 11157749353439,
  p 9327677716601,p 7757562861327,p 6418552957619,p 5283407711813,p 4326745163688,p 3525198941723,
  p 2857497800155,p 2304479680800,p 1849052413370,p 1476112600385,p 1172433338167,p 926530306468,
  p 728514509791,p 569938653189,p 443642850190,p 343604140638,p 264793179353,p 203040465107,
  p 154913626947,p 117606574458,p 88840745855,p 66778243820,p 49946320784,p 37172447443,
  p 27529055766,p 20286973754,p 14876549987,p 10855487561,p 7882457961,p 5695635843,p 4095377311,
  p 2930350987,p 2086518183,p 1478441835,p 1042481862,p 731505441,p 510803574,p 354960536,
  p 245469974,p 168931712,p 115696641,p 78855003,p 53485843,p 36103690,p 24253216,p 16214149,
  p 10787675,p 7142857,p 4706821,p 3086714,p 2014558,p 1308516,p 845845,p 544145,p 348381,p 221971,
  p 140744,p 88808,p 55761,p 34834,p 21652,p 13381,p 8224,p 5022,p 3044,p 1830,p 1087,p 634,p 363,
  p 199,p 104,p 51,p 21,p 6,p 1,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0]
/-- Part 1 of `rkmViHi_m1024_r512_s0_c2`. -/
def rkmViHi_m1024_r512_s0_c2_p1 : List ℤ := let p := rkmP; [
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0]
/-- Input orbital vector for `m1024_r512_s0_c2`. -/
def rkmViHi_m1024_r512_s0_c2 : List ℤ :=
  rkmViHi_m1024_r512_s0_c2_p0 ++ (rkmViHi_m1024_r512_s0_c2_p1)
/-- Part 0 of `rkmVoHi_m1024_r512_s0_c2`. -/
def rkmVoHi_m1024_r512_s0_c2_p0 : List ℤ := let p := rkmP; let n := rkmN; [
  p 0,p 0,n 2,n 6,n 8,p 0,p 5,n 9,n 11,p 4,p 11,p 2,p 4,n 2,n 3,n 3,n 15,n 2,p 3,n 3,p 1,p 7,n 3,
  n 11,n 5,p 1,p 5,n 0,n 11,n 16,n 10,p 4,p 21,p 14,n 14,n 39,n 7,p 11,n 13,n 21,p 6,p 16,n 15,
  n 22,p 1,p 9,p 21,p 15,n 12,n 20,n 14,p 0,p 9,p 15,p 2,p 1,n 4,n 6,n 10,n 0,p 8,n 6,n 18,n 28,
  p 8,p 32,n 6,n 34,n 11,p 2,n 4,p 4,p 22,p 3,n 4,n 8,n 21,p 2,p 26,p 18,p 6,p 12,p 12,n 9,n 2,
  p 16,p 5,n 21,n 13,p 2,p 15,p 15,p 1,p 6,p 6,n 9,n 22,n 19,p 9,p 32,p 37,p 8,n 7,n 12,n 0,p 16,
  p 27,p 10,n 8,p 5,p 12,p 4,p 9,p 4,p 22,p 43,p 37,p 30,p 11,n 11,n 11,p 11,p 22,p 16,p 3,p 4,p 8,
  p 0,p 20,p 33,p 20,p 6,p 17,p 34,p 33,p 19,p 23,p 33,p 37,p 18,p 23,p 35,p 23,p 28,p 42,p 45,
  p 46,p 49,p 47,p 51,p 53,p 59,p 57,p 62,p 71,p 68,p 74,p 85,p 97,p 128,p 172,p 254,p 410,p 662,
  p 1073,p 1763,p 2944,p 4921,p 8201,p 13631,p 22537,p 37073,p 60696,p 98803,p 159938,p 257452,
  p 412091,p 655903,p 1038049,p 1633527,p 2556103,p 3977149,p 6153356,p 9466844,p 14482835,
  p 22032460,p 33330148,p 50139630,p 75006515,p 111582240,p 165072152,p 242850713,p 355300580,
  p 516948806,p 747994213,p 1076346069,p 1540325393,p 2192217588,p 3102910009,p 4367899884,
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
/-- Part 1 of `rkmVoHi_m1024_r512_s0_c2`. -/
def rkmVoHi_m1024_r512_s0_c2_p1 : List ℤ := let p := rkmP; [
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
  p 719352018762,p 561334018235,p 435658141147,p 336288319588,p 258176102569,p 197131200471,
  p 149701603117,p 113064407485,p 84927881629,p 63444804506,p 47136748792,p 34828702513,
  p 25593243280,p 18703370692,p 13593054491,p 9824554548,p 7061602182,p 5047589778,p 3587988603,
  p 2536296060,p 1782897348,p 1246309071,p 866350508,p 598860030,p 411638605,p 281359198,
  p 191229757,p 129239168,p 86850444,p 58034186,p 38558881,p 25473469,p 16732827,p 10928549,
  p 7096780,p 4582044,p 2941374,p 1877275,p 1191197,p 751459,p 471282,p 293828,p 182104,p 112186,
  p 68689,p 41796,p 25267,p 15167,p 9036,p 5339,p 3122,p 1803,p 1027,p 572,p 309,p 161,p 77,p 34,
  p 13,p 3,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0]
/-- Output orbital vector for `m1024_r512_s0_c2`. -/
def rkmVoHi_m1024_r512_s0_c2 : List ℤ :=
  rkmVoHi_m1024_r512_s0_c2_p0 ++ (rkmVoHi_m1024_r512_s0_c2_p1)
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
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws =>
    (match Nat.mod w 2 with
     | 0 => primOfNatForced (Nat.div w 2)
     | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def phbv_w0_p0 : List ℤ := pzig
  [150481829054046,212501679689702,259878448770632,299640739583020,334515346534630,
   365902856004642,394636517395846,421260036920234,446151625249142,469587054794438,
   491774812093074,512877103405286,533023107701830,552317712370600,570847482703456,
   588684866312026,605891231571354,622519112693382,638613900956022,654215140547160,
   669357536521496,684071749434350,698385029405866,712321727605764,725903712957994,
   739150714704390,752080606353892,764709642839708,777052659986534,789123243367560,
   800933872110142,812496042053332,823820371773384,834916694306576,845794136862056,
   856461190395114,866925770576198,877195271423374,887276612650844,897176281611904,
   906900370573254,916454609941446,925844397967060,935074827373208,944150709289580,
   953076594818532,961856794513924,970495396014890,978996280044180,987363134953030,
   995599469971160,1003708627300288,1011693793172492,1019558007979908,1027304175569544,
   1034935071785996,1042453352335296,1049861560034848,1057162131507164,1064357403368782,
   1071449617960294,1078440928658442,1085333404807098,1092129036300040,1098829737845270,
   1105437352937498,1111953657562976,1118380363658406,1124719122343662,1130971526946194,
   1137139115833314,1143223375067164,1149225740895718,1155147602092122,1160990302153520,
   1166755141369550,1172443378769912,1178056233959508,1183594888849046,1189060489288302,
   1194454146608676,1199776939081140,1205029913295200,1210214085464052,1215330442660732,
   1220379943989656,1225363521697682,1230282082228432,1235136507223428,1239927654473272,
   1244656358821892,1249323433026690,1253929668577152,1258475836474404,1262962687973952,
   1267390955293698,1271761352289234,1276074575098242,1280331302755684,1284532197781442,
   1288677906741858,1292769060786602,1296806276162200,1300790154703408,1304721284303650,
   1308600239365546,1312427581232606,1316203858602998,1319929607926340,1323605353784314,
   1327231609255944,1330808876268266,1334337645933104,1337818398870618,1341251605520272,
   1344637726439778,1347977212592620,1351270505624678,1354518038130424,1357720233909208,
   1360877508212064,1363990267979448,1367058912070338,1370083831483058,1373065409568198,
   1376004022233960,1378900038144286,1381753818910036]
private def phbv_w0_p1 : List ℤ := pzig
  [1384565719273538,1387336087286786,1390065264483540,1392753586045594,1395401380963432,
   1398008972191534,1400576676798504,1403104806112264,1405593665860500,1408043556306542,
   1410454772380852,1412827603808320,1415162335231488,1417459246329890,1419718611935656,
   1421940702145488,1424125782429188,1426274113734832,1428385952590742,1430461551204344,
   1432501157558054,1434505015502276,1436473364845642,1438406441442554,1440304477278174,
   1442167700550904,1443996335752470,1445790603745696,1447550721840028,1449276903864900,
   1450969360241020,1452628298049624,1454253921099792,1455846429993874,1457406022191088,
   1458932892069376,1460427230985520,1461889227333650,1463319066602114,1464716931428834,
   1466083001655156,1467417454378236,1468720464002046,1469992202287000,1471232838398280,
   1472442538952866,1473621468065336,1474769787392470,1475887656176686,1476975231288330,
   1478032667266896,1479060116361168,1480057728568316,1481025651672020,1481964031279586,
   1482873010858140,1483752731769890,1484603333306504,1485424952722598,1486217725268416,
   1486981784221652,1487717260918494,1488424284783892,1489102983361056,1489753482340232,
   1490375905586756,1490970375168412,1491537011382108,1492075932779900,1492587256194356,
   1493071096763306,1493527567953976,1493956781586520,1494358847856982,1494733875359672,
   1495081971109008,1495403240560804,1495697787633040,1495965714726108,1496207122742564,
   1496422111106380,1496610777781730,1496773219291286,1496909530734084,1497019805802910,
   1497104136801278,1497162614659954,1497195328953084,1497202367913888,1497183818449972,
   1497139766158242,1497070295339412,1496975489012176,1496855428926964,1496710195579368,
   1496539868223200,1496344524883200,1496124242367396,1495879096279154,1495609161028856,
   1495314509845294,1494995214786718,1494651346751588,1494282975489004,1493890169608844,
   1493472996591602,1493031522797926,1492565813477878,1492075932779900,1491561943759502,
   1491023908387684,1490461887559068,1489875941099774,1489266127775030,1488632505296514,
   1487975130329440,1487294058499394,1486589344398912,1485861041593804,1485109202629244,
   1484333879035596,1483535121334024,1482712979041834,1481867500677598,1480998733766032,
   1480106724842642,1479191519458146,1478253162182646]
private def phbv_w0_p2 : List ℤ := pzig
  [1477291696609594,1476307165359506,1475299610083474,1474269071466434,1473215589230210,
   1472139202136348,1471039947988716,1469917863635876,1468772984973256,1467605346945068,
   1466414983546042,1465201927822900,1463966211875642,1462707866858596,1461426922981236,
   1460123409508802,1458797354762682,1457448786120566,1456077730016398,1454684211940082,
   1453268256436968,1451829887107126,1450369126604368,1448885996635064,1447380517956712,
   1445852710376278,1444302592748316,1442730182972834,1441135497992932,1439518553792202,
   1437879365391874,1436217946847736,1434534311246794,1432828470703680,1431100436356818,
   1429350218364330,1427577825899672,1425783267147032,1423966549296434,1422127678538596,
   1420266660059500,1418383498034686,1416478195623272,1414550754961682,1412601177157084,
   1410629462280528,1408635609359794,1406619616371918,1404581480235426,1402521196802230,
   1400438760849220,1398334166069504,1396207405063344,1394058469328708,1391887349251514,
   1389694034095484,1387478511991654,1385240769927502,1382980793735702,1380698568082474,
   1378394076455562,1376067301151782,1373718223264160,1371346822668654,1368953078010422,
   1366536966689666,1364098464846986,1361637547348302,1359154187769264,1356648358379186,
   1354120030124466,1351569172611496,1348995754089016,1346399741429958,1343781100112684,
   1341139794201690,1338475786327674,1335789037667030,1333079507920696,1330347155292352,
   1327591936465970,1324813806582674,1322012719216890,1319188626351778,1316341478353928,
   1313471223947260,1310577810186170,1307661182427828,1304721284303650,1301758057689904,
   1298771442677416,1295761377540352,1292727798704050,1289670640711876,1286589836191046,
   1283485315817418,1280357008279190,1277204840239478,1274028736297744,1270828618950022,
   1267604408547904,1264356023256252,1261083379009576,1257786389467060,1254464965966138,
   1251119017474632,1247748450541344,1244353169245086,1240933075142060,1237488067211556,
   1234018041799892,1230522892562512,1227002510404224,1223456783417440,1219885596818414,
   1216288832881326,1212666370870200,1209018086968520,1205343854206478,1201643542385750,
   1197917018001708,1194164144162970,1190384780508152,1186578783119750,1182746004434994,
   1178886293153580,1174999494142114,1171085448335178]
private def phbv_w0_p3 : List ℤ := pzig
  [1167143992632822,1163174959794362,1159178178328312,1155153472378290,1151100661604708,
   1147019561062072,1142909981071678,1138771727089522,1134604599569184,1130408393819464,
   1126182899856528,1121927902250308,1117643179964878,1113328506192532,1108983648181250,
   1104608367055246,1100202417628246,1095765548209140,1091297500399656,1086798008883604,
   1082266801207312,1077703597550794,1073108110489132,1068480044743636,1063819096922164,
   1059124955248100,1054397299277326,1049635799602566,1044840117544426,1040009904828342,
   1035144803246720,1030244444305382,1025308448853442,1020336426695666,1015327976186288,
   1010282683803196,1005200123701330,1000079857244028,994921432511000,989724383781482,
   984488230991040,979212479160366,973896617794288,968540120249084,963142443066036,
   957703025269006,952221287623652,946696631855678,941128439825336,935516072655172,
   929858869807720,924156148109630,918407200718350,912611296027234,906767676504492,
   900875557461076,894934125742120,888942538336044,882899920894946,876805366159266,
   870657932279048,864456641023414,858200475869014,851888379957336,845519253909708,
   839091953487724,832605287085498,826058013038806,819448836734478,812776407501642,
   806039315264418,799236086933276,792365182509724,785424990876052,778413825238414,
   771329918187788,764171416338924,756936374502392,749622749339086,742228392439946,
   734751042765960,727188318374736,719537707349638,711796557835526,703962067071244,
   696031269292604,688001022360444,679867992945686,671628640076470,663279196820524,
   654815649837942,646233716493758,637528819164888,628696056309378,619730169785086,
   610625507806040,601375982803200,591975023306048,582415518774508,572689756076544,
   562789346011498,552705137903964,542427119812548,531944301277014,521244574718288,
   510314550540710,499139359569044,487702414546496,475985119823070,463966514778214,
   451622831498606,438926940080076,425847644558606,412348777158288,398388015407688,
   383915310862546,368870761182712,353181663725502,336758329478034,319487953211432,
   301225307808042,281777985428678,260881682800392,238155838178624,213016301570066,
   184479635726534,150628138795948,106510583894510]
private def phbv_w0 : List ℤ := phbv_w0_p0 ++ (phbv_w0_p1 ++ (phbv_w0_p2 ++ phbv_w0_p3))
private def pvm_w0_1_p0 : List ℤ := pzig
  [0,0,5,0,13,5,11,3,23,5,3,3,5,16,6,8,12,12,12,11,3,12,16,18,14,18,22,4,20,40,26,26,36,34,52,46,
   48,32,30,36,46,36,46,78,64,70,72,76,78,78,106,174,276,470,874,1644,3094,5826,10886,20184,
   37156,67710,122184,218392,386586,677818,1177268,2025644,3453212,5833100,9764184,16198482,
   26635164,43412984,70146594,112371046,178484468,281112954,439067100,680119084,1044904272,
   1592348338,2407140404,3609919170,5371015396,7928802236,11613943722,16881100974,24349947826,
   34857654720,49525305618,69840997760,97762608982,135843368066,187383387596,256610166594,
   348890687070,470977060150,631286663392,840216304848,1110488109870,1457522531804,1899831142844,
   2459418701002,3162180488670,4038277198042,5122465864694,6454361740738,8078602812202,
   10044886200678,12407844268492,15226728198902,18564868461472,22488885169208,27067627091874,
   32370826111790,38467464174284,45423862126972,53301513928532,62154705041250,72027969742262,
   82953457791352,94948295469932,108012038475698,122124323540946,137242831013886,153301671204334,
   170210302447732]
private def pvm_w0_1_p1 : List ℤ := pzig
  [187853078241806,206089504424070,224755265492550,243664052491020,262610194382722,
   281372061837376,299716178405822,317401940870814,334186819923144,349831885948372,
   364107484199756,376798870287462,387711611689198,396676564410102,403554246045746,
   408238446899610,410658948574854,410783253280768,408617265305350,404204906806596,
   397626691237198,388997317312474,378462382548092,366194346352296,352387897098286,
   337254894564814,321019068086716,303910651624170,286161130090676,267998257419848,
   249641487063792,231297931213296,213158937472700,195397342530484,178165433027114,
   161593615706588,145789773238462,130839259770802,116805472016346,103730917902794,
   91638695680636,80534291778120,70407605306064,61235110454480,52982074476624,45604757833390,
   39052533653134,33269875248276,28198172364552,23777348547590,19947263015868,16648890359548,
   13825279979220,11422304285458,9389210241226,7678992871252,6248611980562,5059074661588,
   4075406405384,3266532965138,2605093749176,2067205643516,1632193959508,1282304829198,
   1002410963976,779720357096,603495329406,464787346282,356191305696,271621529268,206110478640,
   155630258292,116936232440,87431551900,65051030010,48162593974,35484443316,26016041992,
   18981133996,13781082136,9956969852,7159062784,5122389514,3647361028,2584501822,1822506226,
   1278961214,893190150,620769884,429357862,295537166,202446588,138011784,93633430,63220272,
   42480918,28408266,18906474,12522530,8254500,5415114,3535422,2297174,1485472,955974,612268,
   390250,247536,156248,98132,61320,38124,23564,14480,8842,5360,3212,1900,1108,630,342,176,80,34,
   10,0,0,0]
private def pvm_w0_1_p2 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_1_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_1_p4 : List ℤ := pzig
  [0]
private def pvm_w0_1 : List ℤ :=
  pvm_w0_1_p0 ++ (pvm_w0_1_p1 ++ (pvm_w0_1_p2 ++ (pvm_w0_1_p3 ++ pvm_w0_1_p4)))
private def pvm_w0_2_p0 : List ℤ := pzig
  [0,0,5,0,13,5,11,2,13,17,11,2,15,5,6,8,12,6,16,24,6,5,7,6,18,6,12,34,16,0,18,20,34,26,26,28,36,
   46,56,50,20,44,42,28,28,38,56,64,60,68,80,74,58,66,86,98,144,210,336,612,1122,2052,3800,7010,
   12874,23474,42442,76044,135022,237608,414402,716298,1227172,2084042,3508534,5855988,9690974,
   15902312,25877002,41760330,66841004,106116624,167115606,261080684,404656738,622275208,
   949490370,1437602954,2160006136,3220811528,4766459906,7001196948,10207495064,14772732556,
   21223692900,30270715054,42863600016,60261642794,84120390842,116597904646,160483377086,
   219350918118,297741083746,401372275710,537383410918,714608209908,943880041290,1238364454706,
   1613914327986,2089439955804,2687283461230,3433583695088,4358614417956,5497075195644,
   6888311282058,8576436049052,10610327522534,13043469579584,15933608642658,19342198543186,
   23333609846490,27974085498226,33330432244394,39468446854958,46451087577430,54336414154280,
   63175333695798,73009204116092]
private def pvm_w0_2_p1 : List ℤ := pzig
  [83867360993202,95764646790696,108699032516480,122649430220138,137573799430436,153407651004316,
   170063047367008,187428188464770,205367657893006,223723383867496,242316345551808,
   260949027618672,279408595957336,297470736514810,314904068895820,331475018132404,
   346953003524438,361115784077536,373754787031186,384680240184032,393725930715206,
   400753423092020,405655586132122,408359303620460,408827272949680,407058830624918,
   403089780477270,396991238259936,388867543121834,378853320511240,367109810782476,
   353820601856212,339186921748574,323422657047716,306749266289464,289390752870534,
   271568851207140,253498563174274,235384160570314,217415744727928,199766427801432,
   182590173071468,166020305106550,150168675955680,135125451669572,120959465085732,
   107719066442928,95433393246246,84113974882628,73756585577172,64343261000648,55844398672296,
   48220869646100,41426078176308,35407916475630,30110572687954,25476161234942,21446155280338,
   17962610802210,14969180382594,12411922128374,10239915031428,8405696545652,6865541260962,
   5579601398680,4511930588208,3630412185552,2906612442988,2315577321858,1835589828598,
   1447902607776,1136458279446,887607775736,689834800856,533492575002,410557268654,314401014818,
   239586109186,181680969988,137097613994,102949793836,76930509012,57207322066,42333756066,
   31174994132,22846122924,16661238666,12091849812,8733148758,6276875856,4489651594,3195802654,
   2263847706,1595938228,1119665202,781744916,543185574,375611692,258487206,177031044,120662268,
   81847674,55252906,37120938,24819822,16515632,10937270,7208434,4728150,3086450,2005136,1296418,
   834178,534166,340402,215876,136228,85538,53434,33202,20514,12594,7680,4646,2780,1640,944,530]
private def pvm_w0_2_p2 : List ℤ := pzig
  [288,144,64,24,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_2_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_2_p4 : List ℤ := pzig
  [0]
private def pvm_w0_2 : List ℤ :=
  pvm_w0_2_p0 ++ (pvm_w0_2_p1 ++ (pvm_w0_2_p2 ++ (pvm_w0_2_p3 ++ pvm_w0_2_p4)))
private def pvm_w0_3_p0 : List ℤ := pzig
  [0,0,5,0,13,5,11,2,0,5,25,5,5,13,9,5,10,10,2,8,20,22,20,7,13,12,10,13,16,24,24,8,4,18,26,26,20,
   34,16,22,56,52,36,38,44,42,28,20,28,48,54,38,66,80,64,68,66,54,70,88,92,108,154,238,398,698,
   1246,2256,4096,7468,13526,24284,43286,76544,134176,233258,402088,687272,1164938,1958320,
   3265048,5399432,8857096,14412908,23267898,37268148,59227230,93397660,146153484,226969468,
   349813628,535109306,812474170,1224509496,1831993734,2720935226,4012060286,5873457862,
   8537271012,12321518946,17658349434,25130255202,35516033002,49848508008,69486274934,
   96201898408,132289143692,180691842908,245156905206,330413709582,442381636114,588406748054,
   777527595562,1020768738034,1331458852148,1725568203754,2222057828712,2843230035184,
   3615066882660,4567540223994,5734873860490,7155735543334,8873334172350,10935395833518,
   13393991540608,16305189952920,19728510172476,23726153179452]
private def pvm_w0_3_p1 : List ℤ := pzig
  [28361995685196,33700337230528,39804400195326,46734592859476,54546557485436,63289038169914,
   73001616400766,83712375214624,95435564851514,108169353071058,121893751046876,136568810255406,
   152133186379040,168503162461068,185572215082854,203211194127130,221269168949762,
   239574971992704,257939445787314,276158371929528,294016032164020,311289323552488,
   327752323252928,343181175120812,357359151484202,370081730185110,381161520202930,
   390432869446540,397755995817738,403020497221592,406148117259148,407094669953882,
   405851057804194,402443351249844,396931932671486,389409742636402,379999698628026,
   368851385454694,356137140647378,342047676433788,326787391658192,310569532003152,
   293611355122678,276129449217822,258335339882142,240431501664994,222607868874296,
   205038915901690,187881352062594,171272450821732,155329009435910,140146913443418,
   125801261825874,112346993602586,99819945403098,88238262294774,77604080708364,67905402422446,
   59118081815334,51207854446312,44132342906870,37842985179658,32286840869528,27408241075908,
   23150257875798,19455978977244,16269581770394,13537208523882,11207650716224,9232855401460,
   7568270105712,6173045110818,5010113225012,4046167416584,3251556162766,2600115214360,
   2068952865070,1638203898932,1290765309228,1012024755206,789590645134,613030779580,
   473624708666,364133385650,278588352026,212101570270,160696120620,121157282562,90903009210,
   67872449378,50430952580,37289881982,27439536782,20093526044,14643023794,10619453852,
   7664289546,5504797924,3934703436,2798885370,1981353562,1395866316,978659946,682852726,
   474166194,327675086,225354624,154241278,105062246,71220572,48048238,32259926,21555786,
   14334378,9486564,6248188,4095572,2671702,1734494,1120646,720560,461074,293608,186048,117304,
   73592,45930,28504]
private def pvm_w0_3_p2 : List ℤ := pzig
  [17588,10786,6566,3958,2356,1380,790,440,234,114,52,16,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0]
private def pvm_w0_3_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_3_p4 : List ℤ := pzig
  [0]
private def pvm_w0_3 : List ℤ :=
  pvm_w0_3_p0 ++ (pvm_w0_3_p1 ++ (pvm_w0_3_p2 ++ (pvm_w0_3_p3 ++ pvm_w0_3_p4)))
private def pvm_w0_4_p0 : List ℤ := pzig
  [0,0,5,0,13,5,11,3,5,12,7,17,5,13,9,15,15,0,6,2,6,4,8,30,32,11,2,12,2,7,5,16,22,16,0,16,18,12,
   28,42,18,6,26,46,40,36,42,46,56,32,6,36,38,26,38,48,56,70,78,62,52,56,66,78,80,82,98,114,156,
   268,414,694,1234,2212,3972,7142,12764,22660,39940,69904,121338,208934,356918,604868,1016984,
   1696484,2807844,4611302,7514962,12153628,19506814,31073732,49130610,77105696,120121340,
   185770330,285218444,434756464,657965828,988713942,1475260518,2185837050,3216160396,4699459092,
   6819732000,9829119408,14070450312,20006232310,28255566370,39640693388,55245098678,76485301418,
   105198617230,143749281238,195155323928,263238471848,352799062268,469817473706,621682849268,
   817448885562,1068115152416,1386930777510,1789715372352,2295189810552,2925306937444,
   3705569561990,4665320260386,5837984741666]
private def pvm_w0_4_p1 : List ℤ := pzig
  [7261247953628,8977139940794,11032006920620,13476342351936,16364453159090,19753937964698,
   23704957351572,28279280954542,33539102631194,39545623051204,46357408641566,54028546686808,
   62606628145274,72130601932530,82628556463460,94115495483738,106591184957306,120038155293716,
   134419947818670,149679695511356,165739125177070,182498061090852,199834498641908,
   217605300769640,235647550403478,253780569338330,271808588870418,289524031153232,
   306711333826824,323151225327338,338625335709632,352921009057888,365836169720944,
   377184086573656,386797877882092,394534604423556,400278810220216,403945388168382,
   405481671233890,404868677685830,402121469767144,397288617798712,390450794444802,
   381718555202504,371229389679928,359144152630648,345643002992328,330920992602396,
   315183453420922,298641332906118,281506621906516,263988008598134,246286876398506,
   228593744414168,211085226937628,193921564970094,177244758867444,161177308075170,
   145821542494350,131259511101100,117553377627838,104746260798796,92863447980728,81913906148654,
   71892012589832,62779429442566,54547050545392,47156955636248,40564315132472,34719197978212,
   29568244828364,25056178659384,21127134338308,17725797399970,14798350024246,12293228799332,
   10161704212654,8358295910368,6841040651310,5571631642446,4515448706974,3641498651366,
   2922284424930,2333620365430,1854409151438,1466394177784,1153899057560,903563935542,
   704086356702,545972630036,421304005262,323520562034,247224509934,188003610248,142274646524,
   107146275270,80300157134,59888981200,44449826502,32831231612,24132345128,17652586970,
   12850346734,9309366020,6711586668,4815386432,3438261352,2443145426,1727679934,1215854440,
   851539774,593518170,411689182,284191982,195236764,133480938,90820774,61497816,41442212,
   27792986,18549682,12321024,8144528,5357884,3507736,2285420,1481870,956216]
private def pvm_w0_4_p2 : List ℤ := pzig
  [614036,392386,249528,157892,99408,62264,38796,24042,14804,9052,5490,3294,1950,1136,642,350,
   184,90,36,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_4_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_4_p4 : List ℤ := pzig
  [0]
private def pvm_w0_4 : List ℤ :=
  pvm_w0_4_p0 ++ (pvm_w0_4_p1 ++ (pvm_w0_4_p2 ++ (pvm_w0_4_p3 ++ pvm_w0_4_p4)))
private def pvm_w0_5_p0 : List ℤ := pzig
  [0,0,5,0,13,5,11,3,13,0,16,7,5,13,9,7,13,23,11,3,4,4,16,17,1,36,22,4,4,14,8,2,19,3,22,12,4,18,
   16,1,8,40,42,14,8,20,32,46,24,20,64,58,36,30,24,22,28,32,26,34,54,70,76,62,42,64,58,64,84,82,
   70,76,98,130,162,248,388,630,1108,1972,3486,6196,10950,19264,33704,58496,100756,172258,292322,
   492296,822792,1364854,2247164,3672420,5957474,9593656,15337046,24341946,38357254,60012196,
   93229066,143814796,220300710,335125718,506288592,759636248,1132005626,1675501100,2463267490,
   3597213958,5218258588,7519794912,10765236752,15310668796,21633819824,30370777126,42362066082,
   58709919700,80848743396,110630922052,150430197472,203264838268,272942697308,364229974916,
   483045039300,636677967330,834035524394,1085910078344]
private def pvm_w0_5_p1 : List ℤ := pzig
  [1405269420178,1807562644350,2311035137102,2937043373372,3710357692448,4659438604906,
   5816669598200,7218527008466,8905665487618,10922896116332,13319033506026,16146588505360,
   19461284581606,23321378753752,27786772238272,32917901794614,38774410111870,45413602351562,
   52888705948680,61246961656612,70527585184076,80759650100126,91959953386334,104130934453516,
   117258725955924,131311419687476,146237632659858,161965456669014,178401868931832,
   195432671579210,212923013996840,230718534507474,248647137221084,266521396788996,
   284141559227570,301299082019258,317780632543462,333372441757852,347864891129530,
   361057196178022,372762040537068,382810010831348,391053685270950,397371237751866,
   401669434146950,403885917788816,403990706008420,401986847873744,397910223669032,
   391828497751356,383839266776224,374067473508920,362662181274042,349792824481660,
   335645065797382,320416399873850,304311646925260,287538476900148,270303096979170,
   252806222234760,235239432385806,217781997657962,200598234899344,183835432402720,
   167622359410494,152068354996064,137262971754530,123276133157896,110158750005022,
   97943731399710,86647319202856,76270671832840,66801623387120,58216546956844,50482256249840,
   43557886711460,37396705704886,31947810458126,27157681913362,22971571891480,19334709744424,
   16193322622116,13495470423428,11191702302150,9235546204708,7583846333910,6196965723780,
   5038872376262,4077127779784,3282796252768,2630292582798,2097184017110,1663960946152,
   1313788734330,1032251203368,807094352986,627977082218,486234003100,374653951564,287276515356,
   219207821390,166455950648,125785664858,94591616916,70788856858,52719213084,39072002808,
   28817484716,21151490054,15449739512,11230456226,8124008556,5848449120,4189951704,2987279104,
   2119539640,1496603196,1051650772,735421770,511801714,354460232,244305918,167571914,114385044,
   77703044,52529998,35340872,23661786]
private def pvm_w0_5_p2 : List ℤ := pzig
  [15765856,10454100,6898492,4530220,2960606,1925458,1246182,802630,514422,328090,208222,131484,
   82606,51634,32092,19826,12170,7420,4482,2666,1568,906,510,272,136,62,20,4,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_5_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_5_p4 : List ℤ := pzig
  [0]
private def pvm_w0_5 : List ℤ :=
  pvm_w0_5_p0 ++ (pvm_w0_5_p1 ++ (pvm_w0_5_p2 ++ (pvm_w0_5_p3 ++ pvm_w0_5_p4)))
private def pvm_w0_6_p0 : List ℤ := pzig
  [0,0,5,0,13,5,11,3,5,23,4,4,8,5,9,9,1,9,13,27,5,15,11,26,8,19,11,24,18,12,6,8,24,18,15,13,6,4,
   0,16,28,6,15,10,30,34,36,3,6,40,36,12,18,44,50,56,42,24,26,32,22,32,12,14,52,68,64,66,56,46,
   42,68,82,68,64,78,68,80,108,122,160,218,328,532,930,1608,2794,4904,8634,15086,26196,45174,
   77398,131688,222384,372892,620706,1025780,1683102,2741962,4435278,7123780,11361902,17995284,
   28304444,44213636,68593282,105693624,161761484,245910856,371341374,557029846,830059516,
   1228800728,1807218308,2640656554,3833542292,5529555732,7924943768,11285795156,15970258378,
   22456860854,31380274906,43576068456,60136163710,82476894528,112421683538,152300434630]
private def pvm_w0_6_p1 : List ℤ := pzig
  [205067728828,274441794478,365065964718,482693903990,634399249112,828809438036,1076362368682,
   1389583123816,1783376313008,2275327632864,2886006065378,3639255774884,4562464312876,
   5686791303452,7047339496714,8683248105354,10637686859992,12957728425902,15694076915170,
   18900631389416,22633865647736,26952009356160,31914020772450,37578347957526,44001483363344,
   51236325873828,59330374483680,68323788461684,78247359603534,89120452502216,100948978063726,
   113723473157922,127417364714868,141985499194646,157363017700402,173464652722468,
   190184514405120,207396422318558,224954823205638,242696316477420,260441787990242,
   277999129670982,295166498848412,311736047786596,327498032046306,342245187056274,
   355777246717122,367905466903586,378457011091918,387279055483588,394242477105096,
   399245000310600,402213694469304,403106737665660,401914387010716,398659124489816,
   393394976857428,386206037571652,377204246795376,366526510821546,354331263809168,
   340794591562790,326106048626538,310464305855252,294072765823438,277135278174232,
   259852076792532,242416046221340,225009406911848,207800888699092,190943440369402,
   174572501370646,158804840582112,143737947472028,129449943644076,115999968253452,
   103428979421180,91760905765316,81004077499158,71152865060248,62189454636954,54085693858782,
   46804946845322,40303905267234,34534310549206,29444551348882,24981109532272,21089836641824,
   17717051002740,14810452891424,12319861432044,10197781999404,8399816863418,6884934641208,
   5615615904478,4557893131798,3681303231738,2958770237254,2366434633992,1883444277262,
   1491720105910,1175707994690,922126196324,719715992178,559001455232,432062674298,332325420686,
   254369070056,193753623916,146865900350,110784365462,83161640152,62123417226,46182341012,
   34165313430,25152677500,18427771534,13435430344,9748119390,7038512204,5057453396,3616380138,
   2573401444,1822352340,1284246858,900649848,628571472,436560482]
private def pvm_w0_6_p2 : List ℤ := pzig
  [301734548,207537342,142055382,96762936,65591844,44246566,29702814,19842816,13191544,8727170,
   5745612,3764276,2454186,1592252,1027990,660436,422206,268580,170006,107058,67060,41786,25896,
   15944,9742,5904,3546,2100,1222,696,382,200,94,38,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_6_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_6_p4 : List ℤ := pzig
  [0]
private def pvm_w0_6 : List ℤ :=
  pvm_w0_6_p0 ++ (pvm_w0_6_p1 ++ (pvm_w0_6_p2 ++ (pvm_w0_6_p3 ++ pvm_w0_6_p4)))
private def pvm_w0_7_p0 : List ℤ := pzig
  [0,0,5,0,13,5,11,13,8,13,13,11,4,8,6,13,1,9,8,9,27,1,15,29,19,26,14,13,13,2,16,22,4,3,22,30,6,
   3,0,4,15,13,30,22,14,1,19,8,46,34,1,14,30,26,18,14,8,46,54,48,50,24,16,44,38,18,6,16,32,44,64,
   80,52,36,56,58,64,72,76,60,66,68,74,84,116,122,128,182,272,452,708,1192,2078,3614,6294,10930,
   18884,32408,55354,93850,158000,264224,438772,723594,1185102,1927578,3113738,4995596,7960464,
   12599560,19808564,30934846,47990642,73959556,113233848,172233638,260276054,390786528,
   582972970,864121540,1272719226,1862667196,2708919514,3914967324,5622690468,8025216478,
   11383562622,16047988306]
private def pvm_w0_7_p1 : List ℤ := pzig
  [22485151450,31312338540,43340218390,59625745000,81536994008,110831842478,149752477478,
   201137719728,268555048748,356453988992,470342130232,616984479534,804626050698,1043236563372,
   1344774834936,1723468896194,2196106057148,2782325119316,3504900723110,4390007504570,
   5467449413942,6770837339014,8337696225572,10209481361472,12431482569100,15052594917620,
   18124935402104,21703287003248,25844354768808,30605823131674,36045209621620,42218517388642,
   49178697402028,56973940593570,65645830261658,75227395338652,85741115166162,97196935682004,
   109590364823582,122900720916322,137089611294338,152099718910974,167853971863062,
   184255164334336,201186087392308,218510214467920,236072969530740,253703586468834,
   271217546704922,288419559502074,305107026734748,321073912195374,336114915864828,
   350029837042158,362627997742838,373732590108256,383184809275664,390847636532774,
   396609146639538,400385227660130,402121620951638,401795212281976,399414531367750,
   395019445243974,388680059517704,380494869416784,370588228369654,359107224510930,
   346218074048642,332102154125508,316951806196526,300966043840612,284346296416764,
   267292312418692,249998334357300,232649641279988,215419536523636,198466837980508,
   181933907040306,165945231429268,150606557294338,136004547841808,122206930255760,
   109263079935586,97204981570134,86048500298604,75794893123858,66432490626662,57938481551200,
   50280737577500,43419622096932,37309734569828,31901550582514,27142926575824,22980446976538,
   19360599780480,16230774231440,13540080911294,11240000172888,9284869346812,7632222533840,
   6242999107514,5081638382358,4116078373960,3317676318618,2661067779632,2123979884546,
   1687012649458,1333400575394,1048764854474,820864687976,639354465698,495551937758,382221059784,
   293371932434,224079192362,170319341708,128826817102,96968079828,72632637888,54139666894,
   40158757460,29643263338,21774735798,15916989860,11578441932,8381473224,6037699976]
private def pvm_w0_7_p2 : List ℤ := pzig
  [4328161294,3087563160,2191838122,1548392186,1088511308,761489542,530119118,367249274,
   253177886,173686980,118572696,80552176,54455800,36634000,24524310,16337306,10830128,7144222,
   4689690,3063350,1991170,1287886,828898,530846,338264,214464,135290,84906,52998,32894,20290,
   12434,7560,4552,2714,1594,914,510,272,136,60,20,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_7_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_7_p4 : List ℤ := pzig
  [0]
private def pvm_w0_7 : List ℤ :=
  pvm_w0_7_p0 ++ (pvm_w0_7_p1 ++ (pvm_w0_7_p2 ++ (pvm_w0_7_p3 ++ pvm_w0_7_p4)))
private def pvm_w0_8_p0 : List ℤ := pzig
  [0,0,5,0,13,5,1,21,3,0,7,15,9,13,16,4,4,7,19,16,2,15,17,6,7,41,29,6,14,2,9,17,2,26,6,5,6,24,30,
   5,14,24,11,15,11,2,20,44,4,33,3,34,16,16,10,14,36,26,4,12,12,22,54,62,38,22,32,50,36,18,24,4,
   0,30,66,58,54,48,48,46,66,74,54,74,70,62,56,60,98,104,94,90,136,164,218,342,504,840,1450,2476,
   4268,7386,12682,21736,37018,62636,105300,175874,291786,480904,787276,1280252,2068128,3318778,
   5290650,8378914,13183478,20608574,32007822,49393368,75735436,115388092,174689766,262803774,
   392885730,583692298,861781342,1264496758]
private def pvm_w0_8_p1 : List ℤ := pzig
  [1843986474,2672568260,3849837540,5512007062,7844078736,11095574286,15600694714,21803934226,
   30292340726,41835786366,57436779706,78391505154,106363901568,143474672502,192407136430,
   256531750048,340050946772,448165597410,587263891540,765132728800,991190776858,1276741179174,
   1635240472618,2082578608214,2637363078602,3321198081954,4158947457774,5178967897454,
   6413296773098,7897776972142,9672099525036,11779743735772,14267794145700,17186614152092,
   20589357627934,24531302581652,29068994853960,34259195115848,40157628987000,46817547838272,
   54288116593464,62612654334382,71826763384854,81956392367776,93015888002026,105006098590610,
   117912598693268,131704108835462,146331185789438,161725257564246,177798072473614,
   194441623372776,211528596405534,228913378602662,246433640843316,263912492637572,
   281161183686146,297982305133852,314173421861216,329531047103608,343854853181790,
   356951998129720,368641438342138,378758092672266,387156724098742,393715411295930,
   398338494050708,400958893061952,401539725562530,400075162519604,396590499815692,
   391141443587306,383812637544694,374715486366876,363985353003380,351778227895190,
   338266983934628,323637341831960,308083676122568,291804792281240,274999800521656,
   257864202299188,240586291961686,223343959221202,206301959072744,189609695437096,
   173399544125320,157785720628812,142863679547732,128710015868670,115382824314880,
   102922461975742,91352651557382,80681857900086,70904868743204,62004511826002,53953443926990,
   46715952937450,40249721061478,34507505255864,29438699599944,24990752988126,21110423989600,
   17744862608492,14842515762716,12353859413048,10231965317258,8432914322764,6916070967514,
   5644235998120,4583694336726,3704176159690,2978748227012,2383651564292,1898100187050,
   1504053896442,1185976383680,930588052142,726621182420,564583387182,436533773286,335874876432,
   257162272500,195932802942,148551572238,112077271456,84144935100,62864928956]
private def pvm_w0_8_p2 : List ℤ := pzig
  [46736773806,34576311574,25454698372,18647743260,13594187744,9861624706,7118875878,5113774532,
   3655428940,2600166088,1840471568,1296348182,908610900,633719518,439823246,303752784,208747986,
   142752324,97140838,65777448,44320774,29716068,19825664,13161798,8694632,5715230,3738186,
   2432930,1575564,1015244,650918,415244,263560,166430,104556,65328,40592,25068,15380,9372,5664,
   3382,1992,1156,652,352,182,84,32,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0]
private def pvm_w0_8_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_8_p4 : List ℤ := pzig
  [0]
private def pvm_w0_8 : List ℤ :=
  pvm_w0_8_p0 ++ (pvm_w0_8_p1 ++ (pvm_w0_8_p2 ++ (pvm_w0_8_p3 ++ pvm_w0_8_p4)))
private def pvm_w0_9_p0 : List ℤ := pzig
  [0,0,5,0,11,13,4,9,17,7,2,15,3,23,15,0,1,22,2,17,9,14,8,21,15,14,6,27,37,19,1,18,2,25,13,4,30,
   0,23,20,20,4,6,30,16,2,4,21,41,24,46,12,5,11,2,28,12,1,16,28,22,28,16,0,3,12,60,50,26,34,44,
   30,42,48,28,0,9,22,26,60,64,38,40,46,62,54,60,64,88,70,26,56,80,76,90,96,74,106,128,142,178,
   248,354,574,946,1594,2726,4666,7996,13672,23254,39296,66058,110348,183138,302008,494860,
   805608,1303030,2093990,3343534,5304650,8362528,13099758,20391338,31542542,48487402,74071988]
private def pvm_w0_9_p1 : List ℤ := pzig
  [112456264,169679670,254450838,379242596,561798514,827189770,1210602304,1761084042,2546544190,
   3660370284,5230117278,7428826078,10489647694,14724582180,20548289456,28508087014,39321412742,
   53922194470,73517720388,99657732772,134317559068,179997126488,239837660374,317757715574,
   418609908856,548359280694,714283591384,925195022754,1191681697932,1526366133214,1944176201190,
   2462622425738,3102073480232,3886019670572,4841312029498,5998362522518,7391288889922,
   9057985959396,11040104019324,13382914207194,16135041010120,19348043057500,23075825549732,
   27373871021224,32298279747246,37904616975954,44246571238336,51374436117270,59333436818046,
   68161932368398,77889533898500,88535188755522,100105288687432,112591867453100,125970958446930,
   140201185764100,155222662143532,170956264072298,187303347813510,204145960183700,
   221347584684508,238754447405642,256197388464038,273494284305566,290452984796896,
   306874707612292,322557811982390,337301855434204,350911821693350,363202396313286,
   374002159561200,383157564142068,390536568754706,396031807256754,399563187107446,
   401079829227802,400561283701006,398017980859722,393490904152698,387050498539234,
   378794854797466,368847234863188,357353025061560,344476221945192,330395568707834,
   315300468349592,299386802733820,282852784469366,265894961491506,248704482845200,
   231463719212206,214343314029088,197499721548762,181073267867282,165186750705492,
   149944574462918,135432399498922,121717269349102,108848167096466,96856942660574,85759546447558,
   75557501565730,66239546463842,57783382086314,50157462068778,43322770673696,37234540613754,
   31843871158454,27099215521070,22947715072400,19336366082564,16213012172140,13527162254910,
   11230639340238,9278070066330,7627228247054,6239248077230,5078724037010,4113715075574,
   3315670468462,2659293970694,2122361668454,1685507399436,1331987886456,1047437918840,
   819624108072,638204010828,494495805776]
private def pvm_w0_9_p2 : List ℤ := pzig
  [381262266878,292511516212,223315973618,169650045244,128246400056,96470157468,72209930828,
   53784420132,39863103092,29399513430,21575602624,15755737986,11448980254,8278397348,5956295638,
   4264379020,3037973120,2153572924,1519083546,1066225348,744664056,517504992,357857518,
   246232754,168585460,114850134,77853540,52512066,35242934,23535050,15638194,10339136,6801518,
   4451934,2899402,1878804,1211332,777040,495924,314904,198934,125006,78128,48562,30006,18422,
   11230,6792,4062,2404,1398,794,438,226,108,46,14,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0]
private def pvm_w0_9_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_9_p4 : List ℤ := pzig
  [0]
private def pvm_w0_9 : List ℤ :=
  pvm_w0_9_p0 ++ (pvm_w0_9_p1 ++ (pvm_w0_9_p2 ++ (pvm_w0_9_p3 ++ pvm_w0_9_p4)))
private def pvm_w0_10_p0 : List ℤ := pzig
  [0,0,5,0,1,17,3,2,5,23,2,15,3,2,27,9,15,15,6,22,8,21,13,20,12,19,21,10,14,3,17,43,21,1,12,8,41,
   17,22,14,15,1,20,2,1,26,12,2,40,26,27,31,17,16,40,10,17,6,16,4,6,4,18,18,26,42,34,21,9,20,24,
   42,40,46,16,26,58,48,46,26,2,19,14,44,48,48,26,50,70,38,26,80,74,74,62,40,42,78,80,74,80,78,
   88,102,118,124,154,184,248,384,608,972,1644,2792,4758,8102,13752,23268,39142,65426,108756,
   179688,295008,481342,780412,1257344,2013106,3202992]
private def pvm_w0_10_p1 : List ℤ := pzig
  [5064496,7958274,12428416,19290210,29757234,45624002,69526492,105310958,158552624,237279502,
   352974918,521956092,767255978,1121171918,1628692290,2352068062,3376865064,4819914226,
   6839673120,9649622274,13535445876,18876884182,26175296580,36088130984,49471654610,67433453006,
   91396338556,123175411130,165070066766,219972732908,291496000702,384119597552,503358273824,
   655951137730,850072237888,1095561245114,1404171908692,1789834552892,2268927247802,
   2860548455126,3586781958548,4472942801800,5547790858818,6843696656898,8396742291942,
   10246738859850,12437140938270,15014838451202,18029806898266,21534598576110,25583660186766,
   30232466198104,35536462529256,41549821550682,48324016910406,55906235144752,64337650141168,
   73651595947668,83871682755798,95009909644938,107064835357686,120019874450378,133841790121220,
   148479456399542,163862960801776,179903113756788,196491422949666,213500579267664,
   230785486475232,248184849497832,265523316839052,282614151931560,299262387000306,
   315268392256034,330431773940628,344555497901274,357450121896022,368938010523426,
   378857402139586,387066197774702,393445348036464,397901725173466,400370383480314,
   400816131424232,399234362401182,395651116854788,390122375458798,382732609960050,
   373592643900500,362836898652274,350620120014432,337113696224574,322501689048978,
   306976705300880,290735736627438,273976090887220,256891529333108,239668710745280,
   222484027405464,205500899261228,188867572743550,172715450420026,157157957893980,
   142289935901280,128187529097884,114908529100092,102493118300984,90964953033942,80332519817884,
   70590696579360,61722451657700,53700616713844,46489674960898,40047512955124,34327092054556,
   29278004105856,24847884531146,20983664376782,17632650742926,14743432089664,12266611041624,
   10155372384226,8365897922186,6857642770590,5593489534288,4539797798276,3666366522688,
   2946326446916]
private def pvm_w0_10_p2 : List ℤ := pzig
  [2355978598068,1874593606632,1484184887854,1169266962302,916608364858,714986807578,
   554952579194,428604630170,329382433392,251875542906,191651799970,145104351152,109317033746,
   81947233942,61125010808,45367084298,33504186962,24620256074,18001978256,13097275086,
   9481423028,6829622674,4894960698,3490837758,2477060820,1748915208,1228639268,858819720,
   597310252,413348702,284609944,194983844,132910838,90143286,60829686,40841796,27283434,
   18134092,11992028,7890184,5165064,3363990,2179802,1405286,901336,575140,365102,230564,144834,
   90486,56216,34722,21308,12984,7850,4704,2784,1622,928,512,268,130,56,18,4,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0]
private def pvm_w0_10_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_10_p4 : List ℤ := pzig
  [0]
private def pvm_w0_10 : List ℤ :=
  pvm_w0_10_p0 ++ (pvm_w0_10_p1 ++ (pvm_w0_10_p2 ++ (pvm_w0_10_p3 ++ pvm_w0_10_p4)))
private def pvm_w0_11_p0 : List ℤ := pzig
  [0,0,5,0,8,13,13,5,14,17,9,1,23,4,3,13,11,15,23,25,3,30,16,19,21,16,24,15,13,13,6,22,5,9,39,43,
   2,28,9,43,11,18,11,5,20,3,9,26,12,9,10,32,40,26,21,49,5,20,16,1,4,10,14,5,10,20,13,8,36,54,28,
   3,8,11,6,40,48,22,24,34,22,52,70,56,24,11,25,44,40,10,32,60,52,40,34,34,66,88,76,44,44,48,66,
   78,72,66,84,78,88,110,112,116,128,146,196,264,368,592,964,1586,2686,4544,7708,13042,21952,
   36760,61254,101476]
private def pvm_w0_11_p1 : List ℤ := pzig
  [167122,273558,445056,719646,1156526,1847204,2932424,4626900,7256274,11311222,17526154,
   26993066,41325406,62891258,95143998,143086708,213920772,317944466,469789050,690106818,
   1007859418,1463396630,2112567996,3032172080,4327123838,6139808548,8662194072,12151390862,
   16949479642,23508570178,32422207100,44464393592,60637657246,82231721482,110894459430,
   148716880750,198333914544,263042684492,346939800208,455078886984,593649118922,770174882064,
   993735854862,1275205733580,1627506544690,2065873975074,2608127430338,3274936635924,
   4090074574958,5080644483958,6277266598960,7714208472088,9429441100690,11464601974240,
   13864845610792,16678562383212,19956947579842,23753404839566,28122771448642,33120357545254,
   38800797051576,45216715075734,52417224461218,60446272887068,69340871140816,79129242522366,
   89828942349662,101445004738596,113968180703404,127373336654742,141618085075360,
   156641719106584,172364519655526,188687497234116,205492621017152,222643574683238,
   239987062779850,257354673120258,274565280728244,291427957895614,307745333920568,
   323317328029636,337945160848868,351435534537252,363604860188938,374283404062582,
   383319222122926,390581755564124,395964968452286,399389922134398,400806699108576,
   400195610897962,397567649171510,392964165817600,386455794713894,378140654331504,
   368141894892144,356604675485664,343692674440998,329584249617442,314468373675962,
   298540472592554,281998293737552,265037923064392,247850059850090,230616642712058,
   213507903132444,196679903379142,180272595478084,164408417698244,149191425726706,
   134706938089686,121021660033500,108184237471012,96226183009836,85163109622716,74996204155542,
   65713872409914,57293489686396,49703195042256,42903673658494,36849879151378,31492655927850,
   26780230319430,22659547830606,19077442050002,15981628316194,13321521893576]
private def pvm_w0_11_p2 : List ℤ := pzig
  [11048886055876,9118320027192,7487600180454,6117890282746,4973837987876,4023575321208,
   3238640710566,2593839332114,2067057302120,1639043689386,1293172573588,1015195538914,
   792993160916,616332289324,476634304278,366758065008,280799998916,213912705382,162142569650,
   122286187146,91764873946,68516163390,50900942130,37624738990,27671625812,20249202402,
   14743199236,10680327324,7698122164,5520657150,3939134184,2796488340,1975266296,1388151308,
   970609436,675222272,467349160,321829998,220495480,150299910,101929830,68774106,46166524,
   30832268,20486004,13541896,8905714,5826692,3792578,2455852,1582052,1013876,646374,409924,
   258596,162264,101260,62830,38758,23756,14460,8738,5226,3094,1806,1032,572,298,148,66,24,6,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0]
private def pvm_w0_11_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_11_p4 : List ℤ := pzig
  [0]
private def pvm_w0_11 : List ℤ :=
  pvm_w0_11_p0 ++ (pvm_w0_11_p1 ++ (pvm_w0_11_p2 ++ (pvm_w0_11_p3 ++ pvm_w0_11_p4)))
private def pvm_w0_12_p0 : List ℤ := pzig
  [0,0,5,7,10,0,5,25,8,6,15,4,13,19,3,0,7,11,13,9,25,39,21,20,36,19,21,6,12,20,19,21,3,2,10,22,0,
   51,55,10,24,27,21,4,21,13,20,1,13,8,16,6,4,15,3,40,64,20,21,33,3,14,15,10,22,2,1,8,32,3,21,2,
   28,32,40,46,7,13,4,14,26,50,18,26,18,6,60,104,52,3,16,16,10,10,20,32,60,56,30,16,36,58,90,74,
   40,50,54,54,70,70,66,70,70,74,102,98,100,112,118,130,156,182,248,362,556,878,1454,2428]
private def pvm_w0_12_p1 : List ℤ := pzig
  [4118,6948,11686,19620,32798,54486,90100,148100,242008,393102,634718,1018692,1625112,2577032,
   4062252,6365368,9915124,15353218,23633920,36167246,55023266,83221818,125139982,187081442,
   278066714,410921394,603764376,882028632,1281184480,1850383106,2657294798,3794485384,
   5387756294,7606968860,10679983626,14910468368,20700465962,28578759202,39236223024,53569507774,
   72734541606,98211465840,131882709884,176125953678,233923699400,308991053774,405923086760,
   530362754344,689189828408,890730541116,1144986706308,1463881913700,1861520998982,
   2354457383002,2961961072066,3706278157420,4612870609244,5710623110638,7032001724316,
   8613147453824,10493886392714,12717637304760,15331197305374,18384386976684,21929537890464,
   26020808254760,30713316323214,36062086345716,42120808165280,48940418982556,56567524137810,
   65042682745372,74398593322846,84658223777376,95832938783348,107920685203890,120904302254336,
   134750027075284,149406267816222,164802714846478,180849856038564,197438954075764,
   214442532452318,231715402466474,249096246442642,266409753227162,283469281407486,
   300080004566104,316042472151984,331156500225516,345225289401508,358059653698400,
   369482234503078,379331569111214,387465883714350,393766486445896,398140647068628,
   400523865719708,400881453203984,399209368797692,395534287363644,389912894632476,
   382430436556108,373198574472526,362352621293154,350048254020142,336457813791758,
   321766315737050,306167296844152,289858630723104,273038433747584,255901178002776,
   238634113370266,221414084729874,204404811552436,187754677055678,171595053561860,
   156039170646624,141181513934714,127097725675064,113844964062602,101462667045626,
   89973658263830,79385527842692,69692218905054,60875751600628,52908019847228,45752601395218]
private def pvm_w0_12_p2 : List ℤ := pzig
  [39366528797218,33701976903560,28707831136278,24331109580844,20518220490604,17216044800434,
   14372840443796,11938971486060,9867470220668,8114444385942,6639344566684,5405108712660,
   4378201637292,3528567478982,2829512557930,2257534985328,1792115922562,1415485678244,
   1112375986668,869767934662,676643175748,523744353720,403349098224,309060578874,235616428002,
   178716866116,134872082572,101268321978,75651685906,56228360192,41579794866,30591278870,
   22392340110,16307448802,11815587884,8517368402,6108495748,4358527248,3093995950,2185103350,
   1535303392,1073208444,746344246,516365324,355414542,243372196,165791276,112358158,75752498,
   50808434,33901448,22503032,14859388,9760996,6378476,4146342,2681228,1724724,1103602,702426,
   444718,280044,175390,109236,67644,41640,25470,15468,9326,5572,3290,1916,1092,600,318,158,70,
   26,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0]
private def pvm_w0_12_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_12_p4 : List ℤ := pzig
  [0]
private def pvm_w0_12 : List ℤ :=
  pvm_w0_12_p0 ++ (pvm_w0_12_p1 ++ (pvm_w0_12_p2 ++ (pvm_w0_12_p3 ++ pvm_w0_12_p4)))
private def pvm_w0_13_p0 : List ℤ := pzig
  [0,0,5,13,4,2,14,15,25,10,7,7,6,5,17,9,1,3,13,13,3,7,5,49,49,12,16,14,17,19,10,26,2,9,9,11,19,
   10,58,12,65,31,8,21,9,6,19,27,2,5,5,7,3,1,26,22,15,27,17,54,68,6,3,3,5,21,7,26,10,17,1,40,14,
   5,1,7,15,36,42,40,34,5,13,8,14,10,60,50,13,15,42,68,68,50,32,16,22,4,9,14,32,56,62,20,2,28,56,
   76,72,46,54,52,52,68,74,58,58,62,74,82,94,90,106,110,116,122,134,132]
private def pvm_w0_13_p1 : List ℤ := pzig
  [192,244,320,488,778,1262,2104,3534,5954,9976,16706,27890,46300,76466,125604,205150,333110,
   537648,862694,1376146,2182226,3440214,5391676,8400746,13012952,20040334,30684098,46709778,
   70696170,106386016,159177240,236805758,350287960,515212714,753499588,1095774206,1584554588,
   2278493154,3257983308,4632513530,6550240678,9210356424,12878937326,17909098752,24766414422,
   34060713334,46585519324,63366547412,85720808422,115327983090,154315796382,205361133704,
   271808570318,357807811922,468471242332,610052318444,790144917800,1017902909672,1304278169196,
   1662273978118,2107209255742,2656987357058,3332361291636,4157185209568,5158639939458,
   6367418340962,7817854366788,9547978145956,11599478254034,14017551783210,16850623026176,
   20149912697982,23968841773684,28362257321124,33385472221424,39093116399438,45537804074780,
   52768629456372,60829512024962,69757421784748,79580524245622,90316293980716,101969653905704,
   114531204422886,127975611747982,142260227597200,157324012521862,173086832203894,
   189449189751102,206292447396478,223479578120774,240856471875824,258253802764350,
   275489443381858,292371391348240,308701151769040,324277498962404,338900522277466,
   352375845194184,364518895019022,375159093112120,384143833243564,391342118683420,
   396647737026994,399981865314030,401295016220184,400568258237784,397813667865270,
   393073998778928,386421580551630,377956486466968,367804035141448,356111712906050,
   343045622262636,328786575481532,313525961057906,297461514063588,280793119466148,
   263718770539016,246430793084636,229112431064328,211934871238736,195054764528264,
   178612280992800,162729714572878,147510633924602,133039557602284,119382116132190]
private def pvm_w0_13_p2 : List ℤ := pzig
  [106585650646644,94680188004184,83679725822524,73583757548564,64378967388430,56041027303032,
   48536432936116,41824321812658,35858224933602,30587711501190,25959895469030,21920781500680,
   18416436377264,15393979629480,12802393968400,10593161812710,8720738791596,7142878535122,
   5820825398742,4719393094252,3806947637140,3055312710986,2439614639930,1938082801802,
   1531819643216,1204552607724,942378363722,733507817356,568018585138,437619937634,335433743212,
   255793658888,194063741880,146476784076,109991992378,82171131794,61071893848,45157028702,
   33217661272,24309178544,17698106490,12818473372,9236265718,6620712234,4721268432,3349313542,
   2363705846,1659467990,1158989262,805234204,556537462,382642346,261706834,178056328,120508298,
   81131656,54334336,36196420,23986132,15810826,10366800,6761242,4386274,2830382,1816650,1159758,
   736410,465070,292108,182454,113316,69972,42944,26186,15858,9532,5672,3338,1936,1092,602,318,
   158,70,26,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0]
private def pvm_w0_13_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_13_p4 : List ℤ := pzig
  [0]
private def pvm_w0_13 : List ℤ :=
  pvm_w0_13_p0 ++ (pvm_w0_13_p1 ++ (pvm_w0_13_p2 ++ (pvm_w0_13_p3 ++ pvm_w0_13_p4)))
private def pvm_w0_14_p0 : List ℤ := pzig
  [0,0,5,13,1,5,10,22,21,13,0,11,7,4,4,9,13,7,2,15,5,11,21,24,2,35,51,33,4,26,3,25,11,16,18,5,4,
   16,35,59,34,58,2,15,9,37,17,0,7,17,11,7,13,8,7,17,11,5,46,34,27,49,3,46,34,22,20,22,29,35,12,
   24,25,1,10,4,28,22,3,13,11,21,32,64,24,16,34,5,33,1,58,56,18,3,11,32,66,54,52,44,32,26,8,23,3,
   26,60,58,18,0,26,38,60,70,58,38,48,56,70,66,62,46,66,56,68,92,82,84]
private def pvm_w0_14_p1 : List ℤ := pzig
  [112,114,108,100,122,140,142,170,224,290,416,652,1056,1752,2892,4862,8162,13622,22708,37704,
   62298,102360,167278,271776,438980,704956,1125526,1786594,2819564,4423990,6901360,10704078,
   16506844,25309602,38585088,58488842,88156142,132118764,196886052,291749400,429888376,
   629880368,917746904,1329707276,1915856858,2745045344,3911298008,5542204818,7809797654,
   10944545072,15253217114,21141509252,29142460882,39951856992,54471954484,73865020954,
   99618300010,133622111704,178262842112,236532551866,312156819326,409742203224,534944338058,
   694657138006,897222855942,1152661805932,1472919395746,1872126724912,2366869393974,
   2976457362452,3723186727332,4632582232010,5733607238010,7058825902942,8644500532998,
   10530605656364,12760739456096,15381912965628,18444198030000,22000216622326,26104456799030,
   30812404472836,36179485315272,42259817451162,49104783082314,56761435604884,65270767909220,
   74665877037436,84970069812188,96194962967564,108338639196846,121383926847618,135296875221196,
   150025499093062,165498864760088,181626585350378,198298785151410,215386581336858,
   232743116900132,250205161219396,267595275057084,284724515675186,301395636007536,
   317406710450728,332555099848718,346641650679814,359475009272144,370875921919034,
   380681386700928,388748523095556,394958031253630,399217124046478,401461831286226,
   401658596236076,399805108797028,395930346509372,390093822539940,382384067867918,
   372916401663736,361830068175634,349284839235710,335457197901770,320536230129118,
   304719357351974,288208043358488,271203604051492,253903239039506,236496390154704]
private def pvm_w0_14_p2 : List ℤ := pzig
  [219161514779854,202063342232230,185350660412602,169154658495388,153587830576168,
   138743425771688,124695413012500,111498914243970,99191048341956,87792119952644,77307082704984,
   67727204677852,59031865356550,51190417199644,44164050894730,37907610909848,32371316525706,
   27502352667822,23246304082016,19548415316422,16354667251150,13612668305000,11272364770582,
   9286579887808,7611395232742,6206390803678,5034761910744,4063331731916,3262478329010,
   2605994172718,2070894961880,1637192889730,1287647645062,1007506462524,784242554580,
   607299351124,467846201720,358549603436,273362629174,207334057488,156437745356,117422027572,
   87678355522,65127981006,48125225436,35375726056,25867996200,18816654460,13615748366,
   9800705374,7017574346,4998361650,3541410906,2495915740,1749787732,1220223780,846426062,
   584023972,400830760,273638154,185812084,125501638,84313908,56340350,37446100,24754618,
   16276618,10644514,6923676,4479112,2881940,1844210,1173706,742878,467608,292696,182172,112732,
   69342,42392,25746,15530,9290,5506,3218,1848,1044,572,296,146,64,24,6,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_14_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_14_p4 : List ℤ := pzig
  [0]
private def pvm_w0_14 : List ℤ :=
  pvm_w0_14_p0 ++ (pvm_w0_14_p1 ++ (pvm_w0_14_p2 ++ (pvm_w0_14_p3 ++ pvm_w0_14_p4)))
private def pvm_w0_15_p0 : List ℤ := pzig
  [0,0,5,13,1,3,15,20,22,13,5,1,11,13,0,4,4,19,3,1,19,8,3,29,21,10,20,6,37,59,33,8,20,13,29,2,24,
   17,7,52,22,63,39,6,22,28,24,13,29,7,17,13,2,19,11,11,9,10,2,35,47,16,52,32,35,31,2,14,5,46,68,
   0,9,3,3,1,10,15,15,16,12,14,46,0,41,25,14,14,6,54,60,14,23,33,10,54,52,10,0,7,22,48,46,48,50,
   48,50,14,27,25,30,42,46,28,12,0,32,46,64,56,30,48,60,50,70,70,52,40]
private def pvm_w0_15_p1 : List ℤ := pzig
  [58,76,64,54,88,108,90,102,104,112,116,110,140,152,158,190,260,358,530,850,1394,2286,3836,6386,
   10670,17792,29548,48878,80444,131650,214212,346582,557576,891886,1418470,2243018,3526536,
   5512888,8568916,13243174,20350990,31096498,47247164,71381294,107236548,160197768,237974752,
   351537450,516397192,754350042,1095831880,1583076692,2274322072,3249367642,4616867424,
   6523825508,9167866338,12812968330,17809479834,24619378968,33847891572,46282736666,62942422546,
   85135157922,114530058366,153242405634,203934736254,269935474632,355376663382,465352050858,
   606096350070,785185856700,1011759783056,1296760616244,1653190526146,2096379337066,
   2644257847794,3317628369506,4140422298444,5139932422406,6347005568650,7796179252050,
   9525744312080,11577714286076,13997681620468,16834540936854,20140060607430,23968285999896,
   28374761037222,33415559255686,39146121349886,45619903211426,52886846570666,60991693322646,
   69972174161352,79857111879498,90664489163474,102399539416528,115052926536484,128599085111696,
   142994795656340,158178069827072,174067417676658,190561562675436,207539660386308,
   224862063414424,242371658868360,259895785548072,277248717096236,294234675249064,
   310651315062946,326293602619174,340957986293326,354446746253388,366572394365450,
   377161988925322,386061226178098,393138173766304,398286520113224,401428228058684,
   402515500296302,401531987520258,398493196663288,393446085007366,386467854982704,
   377663992812616,367165620523054,355126254040136]
private def pvm_w0_15_p2 : List ℤ := pzig
  [341718079143840,327127871156296,311552692909840,295195508537838,278260848028616,
   260950649620842,243460394585638,225975632530026,208668976005526,191697621952742,
   175201435413082,159301609030962,144099891097932,129678356081514,116099675391566,
   103407833046150,91629221190420,80774044188824,70837957172904,61803865244696,53643812649084,
   46320896679878,39791148361856,34005330516700,28910613142006,24452095613602,20574154617260,
   17221605556134,14340673170102,11879774034214,9790119346744,8026150920196,6545826565294,
   5310773175316,4286326888398,3441479866624,2748752640962,2184009792794,1726235135460,
   1357280671900,1061601570370,825987331664,639297310778,492206873080,376968760244,287192744102,
   217645373512,164070570068,123030995220,91769477112,68089328200,50252080796,36890991458,
   26938591542,19566568106,14136324794,10158679314,7261286876,5162525464,3650729630,2567807740,
   1796416978,1249999904,865101922,595491084,407690026,277605326,188002816,126629734,84827676,
   56515258,37446886,24676448,16171948,10540210,6831854,4403764,2822932,1799526,1140746,719094,
   450738,280918,174068,107214,65638,39940,24136,14476,8606,5064,2942,1682,936,506,262,128,52,18,
   4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_15_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_15_p4 : List ℤ := pzig
  [0]
private def pvm_w0_15 : List ℤ :=
  pvm_w0_15_p0 ++ (pvm_w0_15_p1 ++ (pvm_w0_15_p2 ++ (pvm_w0_15_p3 ++ pvm_w0_15_p4)))
private def pvm_w0_16_p0 : List ℤ := pzig
  [0,0,5,13,7,6,15,19,20,22,1,1,1,15,9,17,6,12,15,2,1,23,9,10,0,19,29,17,16,28,10,35,63,35,18,8,
   37,21,38,13,45,10,58,20,21,29,39,5,40,20,14,3,21,11,11,7,9,1,31,27,0,36,1,53,57,16,58,5,3,16,
   15,39,4,38,40,42,16,23,14,12,15,3,4,15,27,32,56,8,7,5,9,23,11,12,70,66,10,23,29,8,46,42,20,3,
   0,6,42,34,30,50,90,64,24,7,25,2,32,38,50,4,9,24,38,44,48,50,38,32]
private def pvm_w0_16_p1 : List ℤ := pzig
  [52,86,56,32,60,66,60,44,56,80,82,78,100,112,100,86,122,116,120,136,138,156,184,220,296,434,
   672,1070,1752,2916,4836,8056,13440,22360,37080,61152,100276,163586,265386,428094,686648,
   1095106,1736610,2738248,4293144,6692770,10374554,15990964,24508994,37353110,56608760,85310200,
   127845080,190518672,282336096,416078658,609774574,888694808,1288041920,1856546418,2661242638,
   3793763680,5378577472,7583681370,10634382508,14830917282,20570800254,28376944430,38932751356,
   53125528892,72099748140,97321786608,130657909394,174467297528,231711922262,306084962080,
   402159242496,525556818306,683140288592,883225710544,1135816036256,1452852823520,1848482558792,
   2339332284250,2944787363002,3687262183886,4592452462850,5689555621934,7011443625946,
   8594770759298,10479997278832,12711308847050,15336411303710,18406180848016,21974151234662,
   26095822277182,30827777897814,36226607217110,42347628724722,49243425322956,56962206819932,
   65546026001826,75028884389504,85434773753474,96775708923346,109049815838498,122239545578622,
   136310089723064,151208074300262,166860608367810,183174758586386,200037512846314,
   217316284081034,234859990055250,252500726556064,270056030646320,287331708251832,
   304125177289866,320229254858054,335436295801754,349542571369874,362352761694036,
   373684425392004,383372304418750,391272322842468,397265144702598,401259168405002,
   403192852815608]
private def pvm_w0_16_p2 : List ℤ := pzig
  [403036292621190,400791986679950,396494771812268,390210924478782,382036462670714,
   372094708727308,360533199400854,347520051179266,333239905727128,317889591664726,
   301673644410046,284799825402960,267474775960618,249899929792932,232267792590158,
   214758678012520,197537967919104,180753941880354,164536198026884,148994665135524,
   134219185457318,120279629912268,107226492483956,95091899315080,83890960300230,73623386869494,
   64275298958984,55821146530050,48225675977360,41445878831430,35432868751804,30133642357552,
   25492689414068,21453427802790,17959448128100,14955561428356,12388651011008,10208335765056,
   8367457342740,6822407341446,5533313116728,4464102223086,3582465853308,2859741191456,
   2270731481202,1793481010256,1409020284274,1101094553346,855886686680,661743266896,
   508910774122,389286907926,296190488212,224152003026,168725735784,126323497662,94069298056,
   69673782852,51326932456,37607312096,27406079142,19863951218,14319402902,10266467958,
   7320661918,5191692802,3661787000,2568612948,1791932756,1243248910,857834686,588645690,
   401702750,272616212,183988236,123485300,82418092,54702492,36104710,23696690,15465836,10037256,
   6477494,4156644,2652252,1682738,1061542,665826,415202,257400,158630,97168,59152,35772,21476,
   12794,7552,4406,2534,1434,790,420,212,98,40,12,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_16_p3 : List ℤ := pzig
  [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
   0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
private def pvm_w0_16_p4 : List ℤ := pzig
  [0]
private def pvm_w0_16 : List ℤ :=
  pvm_w0_16_p0 ++ (pvm_w0_16_p1 ++ (pvm_w0_16_p2 ++ (pvm_w0_16_p3 ++ pvm_w0_16_p4)))
private theorem dk_w0_0 : muxFastIterBSlideChk 5 513 phbv_w0
    rkmViHi_m1024_r512_s0_c2 pvm_w0_1 = true := by
  decide +kernel
private theorem dk_w0_1 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_1 pvm_w0_2 = true := by
  decide +kernel
private theorem dk_w0_2 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_2 pvm_w0_3 = true := by
  decide +kernel
private theorem dk_w0_3 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_3 pvm_w0_4 = true := by
  decide +kernel
private theorem dk_w0_4 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_4 pvm_w0_5 = true := by
  decide +kernel
private theorem dk_w0_5 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_5 pvm_w0_6 = true := by
  decide +kernel
private theorem dk_w0_6 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_6 pvm_w0_7 = true := by
  decide +kernel
private theorem dk_w0_7 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_7 pvm_w0_8 = true := by
  decide +kernel
private theorem dk_w0_8 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_8 pvm_w0_9 = true := by
  decide +kernel
private theorem dk_w0_9 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_9 pvm_w0_10 = true := by
  decide +kernel
private theorem dk_w0_10 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_10 pvm_w0_11 = true := by
  decide +kernel
private theorem dk_w0_11 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_11 pvm_w0_12 = true := by
  decide +kernel
private theorem dk_w0_12 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_12 pvm_w0_13 = true := by
  decide +kernel
private theorem dk_w0_13 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_13 pvm_w0_14 = true := by
  decide +kernel
private theorem dk_w0_14 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_14 pvm_w0_15 = true := by
  decide +kernel
private theorem dk_w0_15 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_15 pvm_w0_16 = true := by
  decide +kernel
private theorem dk_w0_16 : muxFastIterBSlideChk 5 513 phbv_w0
    pvm_w0_16 rkmVoHi_m1024_r512_s0_c2 = true := by
  decide +kernel
private theorem dkhb_w0 : muxIntListEq rkmHbHi_m1024_r512_s0_c2 phbv_w0 = true := by
  decide +kernel
private theorem pw_w0_1 : muxFastIterFullT16 10 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_2 :=
  (muxFastIterFullT16_add 5 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) (muxFastIterBSlideChk_sound dk_w0_0)).trans
      (muxFastIterBSlideChk_sound dk_w0_1))
private theorem pw_w0_2 : muxFastIterFullT16 15 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_3 :=
  (muxFastIterFullT16_add 10 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_1).trans
      (muxFastIterBSlideChk_sound dk_w0_2))
private theorem pw_w0_3 : muxFastIterFullT16 20 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_4 :=
  (muxFastIterFullT16_add 15 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_2).trans
      (muxFastIterBSlideChk_sound dk_w0_3))
private theorem pw_w0_4 : muxFastIterFullT16 25 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_5 :=
  (muxFastIterFullT16_add 20 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_3).trans
      (muxFastIterBSlideChk_sound dk_w0_4))
private theorem pw_w0_5 : muxFastIterFullT16 30 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_6 :=
  (muxFastIterFullT16_add 25 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_4).trans
      (muxFastIterBSlideChk_sound dk_w0_5))
private theorem pw_w0_6 : muxFastIterFullT16 35 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_7 :=
  (muxFastIterFullT16_add 30 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_5).trans
      (muxFastIterBSlideChk_sound dk_w0_6))
private theorem pw_w0_7 : muxFastIterFullT16 40 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_8 :=
  (muxFastIterFullT16_add 35 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_6).trans
      (muxFastIterBSlideChk_sound dk_w0_7))
private theorem pw_w0_8 : muxFastIterFullT16 45 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_9 :=
  (muxFastIterFullT16_add 40 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_7).trans
      (muxFastIterBSlideChk_sound dk_w0_8))
private theorem pw_w0_9 : muxFastIterFullT16 50 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_10 :=
  (muxFastIterFullT16_add 45 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_8).trans
      (muxFastIterBSlideChk_sound dk_w0_9))
private theorem pw_w0_10 : muxFastIterFullT16 55 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_11 :=
  (muxFastIterFullT16_add 50 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_9).trans
      (muxFastIterBSlideChk_sound dk_w0_10))
private theorem pw_w0_11 : muxFastIterFullT16 60 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_12 :=
  (muxFastIterFullT16_add 55 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_10).trans
      (muxFastIterBSlideChk_sound dk_w0_11))
private theorem pw_w0_12 : muxFastIterFullT16 65 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_13 :=
  (muxFastIterFullT16_add 60 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_11).trans
      (muxFastIterBSlideChk_sound dk_w0_12))
private theorem pw_w0_13 : muxFastIterFullT16 70 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_14 :=
  (muxFastIterFullT16_add 65 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_12).trans
      (muxFastIterBSlideChk_sound dk_w0_13))
private theorem pw_w0_14 : muxFastIterFullT16 75 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_15 :=
  (muxFastIterFullT16_add 70 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_13).trans
      (muxFastIterBSlideChk_sound dk_w0_14))
private theorem pw_w0_15 : muxFastIterFullT16 80 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = pvm_w0_16 :=
  (muxFastIterFullT16_add 75 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_14).trans
      (muxFastIterBSlideChk_sound dk_w0_15))
private theorem pw_w0_16 : muxFastIterFullT16 85 513
    phbv_w0 rkmViHi_m1024_r512_s0_c2 = rkmVoHi_m1024_r512_s0_c2 :=
  (muxFastIterFullT16_add 80 5 513 phbv_w0 rkmViHi_m1024_r512_s0_c2).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_w0) pw_w0_15).trans
      (muxFastIterBSlideChk_sound dk_w0_16))
/-- Certified `T_16` walk chunk `m1024_r512_s0_c2`. -/
theorem rkmWalkChkHi_m1024_r512_s0_c2 : muxFastIterFullT16 85 513
    rkmHbHi_m1024_r512_s0_c2 rkmViHi_m1024_r512_s0_c2 = rkmVoHi_m1024_r512_s0_c2 :=
  (congrArg (fun h ↦ muxFastIterFullT16 85 513 h rkmViHi_m1024_r512_s0_c2)
    (muxIntListEq_eq_true.mp dkhb_w0)).trans pw_w0_16
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi1024T5`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi1024T5 :
    rkmWalkChkHi_m1024_r512_s0_c2 = rkmWalkChkHi_m1024_r512_s0_c2 :=
  rfl
private theorem laneRoot_Hi1024T5 : rkmHbHi_m1024_r512_s0_c2 = rkmHbHi_m1024_r512_s0_c2 :=
  (And.intro (Eq.refl rkmHbHi_m1024_r512_s0_c1) rfl).right
end
end QuantumComputation.Specs.DickeSol
