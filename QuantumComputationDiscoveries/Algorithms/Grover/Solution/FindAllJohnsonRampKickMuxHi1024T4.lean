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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi1024T3

/-
# High-`m` Checkpointed Walk Part `4` (`FindAllJohnsonRampKickMuxHi1024T4`)

Certifies `1` `T_16` checkpoint walk(s) (`43092` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Quantized generator list for `m1024_r512_s0_c1`. -/
def rkmHbHi_m1024_r512_s0_c1 : List ℤ := altBuildHbFrom 1024 512 51956407114 0 512
/-- Part 0 of `rkmViHi_m1024_r512_s0_c1`. -/
def rkmViHi_m1024_r512_s0_c1_p0 : List ℤ := let p := rkmP; [
  p 1413998,p 9305402,p 43236817,p 163783930,p 536491409,p 1569428382,p 4184762416,p 10314943692,
  p 23746851171,p 51464406083,p 105649177013,p 206473740185,p 385748348878,p 691346905444,
  p 1192142853144,p 1982944467065,p 3188665354697,p 4966749709579,p 7506753071595,p 11026016908918,
  p 15760612606133,p 21951181044811,p 29823931414640,p 39567817468221,p 51309674335953,
  p 65089745871866,p 80840433789605,p 98371153999425,p 117361839340995,p 137366891002528,
  p 157830329053994,p 178111657965524,p 197520713903425,p 215358673275475,p 230961631302514,
  p 243742813265412,p 253229603745363,p 259092145918141,p 261161186775002,p 259433992390641,
  p 254068374729730,p 245366004726081,p 233747106403122,p 219719244800549,p 203843195914712,
  p 186698827336380,p 168853572131337,p 150835522635291,p 133112496146436,p 116077721841196,
  p 100042146686464,p 85232817020521,p 71796397673863,p 59806654483368,p 49274641144562,
  p 40160374880727,p 32384925690841,p 25842046010083,p 20408698063382,p 15954066603520,
  p 12346853668859,p 9460825640432,p 7178714534816,p 5394664409968,p 4015463659845,p 2960821280420,
  p 2162937649006,p 1565595825028,p 1122964968258,p 798269057608,p 562436106293,p 392808500930,
  p 271965667227,p 186686685147,p 127062693115,p 85756393871,p 57397892097,p 38101544169,
  p 25086591394,p 16384284755,p 10615329344,p 6823263521,p 4351462009,p 2753553460,p 1729008779,
  p 1077396622,p 666280900,p 408950164,p 249139126,p 150660217,p 90441195,p 53897719,p 31888611,
  p 18732080,p 10925597,p 6327557,p 3638992,p 2078266,p 1178739,p 663972,p 371462,p 206406,
  p 113919,p 62447,p 33994,p 18382,p 9867,p 5255,p 2776,p 1451,p 748,p 381,p 188,p 88,p 38,p 13,
  p 4,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0]
/-- Part 1 of `rkmViHi_m1024_r512_s0_c1`. -/
def rkmViHi_m1024_r512_s0_c1_p1 : List ℤ := let p := rkmP; [
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
/-- Input orbital vector for `m1024_r512_s0_c1`. -/
def rkmViHi_m1024_r512_s0_c1 : List ℤ :=
  rkmViHi_m1024_r512_s0_c1_p0 ++ (rkmViHi_m1024_r512_s0_c1_p1)
/-- Part 0 of `rkmVoHi_m1024_r512_s0_c1`. -/
def rkmVoHi_m1024_r512_s0_c1_p0 : List ℤ := let p := rkmP; let n := rkmN; [
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
/-- Part 1 of `rkmVoHi_m1024_r512_s0_c1`. -/
def rkmVoHi_m1024_r512_s0_c1_p1 : List ℤ := let p := rkmP; [
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
/-- Output orbital vector for `m1024_r512_s0_c1`. -/
def rkmVoHi_m1024_r512_s0_c1 : List ℤ :=
  rkmVoHi_m1024_r512_s0_c1_p0 ++ (rkmVoHi_m1024_r512_s0_c1_p1)
end
public section
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem n0m (z : ℕ) : (0 : ℕ) = Nat.mul 0 z := by rw [Nat.mul_eq]; omega
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uConsNat (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uConsNat_eq (x : ℕ) (xs : List ℕ) : uConsNat x xs = x :: xs := by
  unfold uConsNat; rw [n1a]; cases xs <;> rfl
private def uMulZ (z : ℕ) : List ℕ → List ℕ
  | [] => [] | b :: bs => uConsNat (Nat.mul b z) (uMulZ z bs)
private def uToNatHb : List ℤ → Option (List ℕ)
  | [] => some [] | Int.negSucc _ :: _ => none
  | Int.ofNat n :: xs => match uToNatHb xs with | some ns => some (uConsNat n ns) | none => none
private def uOfNatHb : List ℕ → List ℤ | [] => [] | n :: ns => Int.ofNat n :: uOfNatHb ns
private theorem uToNatHb_sound : ∀ (hb : List ℤ) (ns : List ℕ), uToNatHb hb = some ns →
    hb = uOfNatHb ns
  | [], _, h => by injection h with h'; subst h'; rfl
  | Int.negSucc _ :: _, _, h => by dsimp only [uToNatHb] at h; cases h
  | Int.ofNat n :: xs, _, h => by
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
    | none => none | some u => match bEnc z xs with | none => none | some us => some (uConsNat u us)
private theorem bEnc1_sound (z : ℕ) (x : ℤ) (u : ℕ) (h : bEnc1 z x = some u) :
    ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bEnc1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bEnc1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w => intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem bEnc_sound (z : ℕ) : ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us →
    bDec z us = xs
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
private def zTdiv (x : ℤ) (d : ℕ) : ℤ :=
  match x with | Int.ofNat m => Int.ofNat (m / d) | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg_eq : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTdivNat_eq : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTdiv x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => by dsimp only [muxRawIntTdivNat, zTdiv]; rw [bNeg_eq, ndiv, Nat.add_eq]
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
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTdiv]; rw [bNeg_eq, ndiv, Nat.add_eq]
      rw [Nat.add_eq]; exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [bSubNatTdiv_eq, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTdiv t d) (by simp only [Int.negSucc_eq]; omega)
private theorem bMul_eq (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a <;> cases b <;>
    simp only [muxRawIntMul, bNeg_eq, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast,
      Int.negSucc_eq] <;> push_cast <;> ring
private theorem bForcedAdd_eq (a b : ℤ) : rkmForcedIntAdd a b = a + b := by
  cases a <;> cases b <;>
    simp only [rkmForcedIntAdd, bOfNatF_eq, bNegSuccF_eq, bSub_eq, Nat.add_eq,
      Int.ofNat_eq_natCast, Int.negSucc_eq] <;> omega
private theorem bAddCons_eq (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bForcedAdd_eq]; cases a + b <;> cases xs <;> rfl
private def bStepVal (v P Q d : ℕ) : ℕ := match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d) | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bStepVal_eq (z v P Q d : ℕ) (hv : 0 < bStepVal v P Q d) :
    ((bStepVal v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTdiv ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSubNatTdiv_eq]; unfold bStepVal at hv ⊢; unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢; revert hv; cases h : Q - P with
  | zero => intro _; dsimp only; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k => intro hv; dsimp only at hv ⊢; rw [bNeg_eq]; omega
private abbrev bCellVal (d b0 bz0 c0 b bz v c1 : ℕ) : ℕ :=
  bStepVal v (Nat.add (Nat.mul b0 c0) bz) (Nat.add (Nat.mul b c1) bz0) d
private theorem bCell_hb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCellVal d b0 (Nat.mul b0 z) c0 b (Nat.mul b z) v c1) (ht : bDec z rest = tailZ) :
    bDec z (uConsNat (bCellVal d b0 (Nat.mul b0 z) c0 b (Nat.mul b z) v c1) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
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
private def bAllPos : List ℕ → Bool | [] => true | x :: xs => cond (Nat.ble x 0) false (bAllPos xs)
private theorem bAllPos_uCons {x : ℕ} {xs : List ℕ} (h : bAllPos (uConsNat x xs) = true) :
    0 < x ∧ bAllPos xs = true := by
  rw [uConsNat_eq] at h
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private def bHeadOr (z : ℕ) : List ℕ → ℕ | [] => z | x :: _ => x
private def bTailN : List ℕ → List ℕ | [] => [] | _ :: xs => xs
private theorem bHeadOr_eq (z : ℕ) : ∀ (cs : List ℕ),
    ((bHeadOr z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHeadOr; rw [bDec_nil, bZero_eq] | _ :: _ => by unfold bHeadOr; rw [bDec_cons]
private theorem bTailN_eq (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTailN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl | _ :: _ => by unfold bTailN; rw [bDec_cons]
private def bSlide (z d : ℕ) : ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _, _, _ => []
  | rem + 1, b0, bz0, c0, bns, bzs, vs, cs => match bns, bzs with
    | b :: bR, bz :: bzR => match vs, cs with
      | v :: vT, c :: cT =>
        uConsNat (bCellVal d b0 bz0 c0 b bz v (bHeadOr z cT)) (bSlide z d rem b bz c bR bzR vT cT)
      | v :: vT, [] =>
        uConsNat (bCellVal d b0 bz0 c0 b bz v z) (bSlide z d rem b bz z bR bzR vT [])
      | [], c :: cT =>
        uConsNat (bCellVal d b0 bz0 c0 b bz z (bHeadOr z cT)) (bSlide z d rem b bz c bR bzR [] cT)
      | [], [] => uConsNat (bCellVal d b0 bz0 c0 b bz z z) (bSlide z d rem b bz z bR bzR [] [])
    | _, _ => uConsNat (bStepVal (bHeadOr z vs) (Nat.mul b0 c0) bz0 d)
        (bSlide z d rem 0 0 z [] [] (bTailN vs) (bTailN cs))
private theorem bSlide_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAllPos (bSlide z d rem b0 (Nat.mul b0 z) c0 bns (uMulZ z bns) vs cs) = true →
    bDec z (bSlide z d rem b0 (Nat.mul b0 z) c0 bns (uMulZ z bns) vs cs) =
      rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOfNatHb bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSlide, uMulZ, uOfNatHb, rkmUltraSlideLoopAux] at h ⊢
      have hp := bAllPos_uCons h
      have hp2 : bAllPos (bSlide z d rem 0 (Nat.mul 0 z) z [] (uMulZ z [])
          (bTailN vs) (bTailN cs)) = true := by dsimp only [uMulZ]; rw [← n0m z]; exact hp.2
      have hi := bSlide_sound z d rem 0 z [] (bTailN vs) (bTailN cs) hp2
      dsimp only [uMulZ] at hi; rw [← n0m z, bMul0, uOfNatHb, bTailN_eq z vs, bTailN_eq z cs] at hi
      have hc := bCell_nil z d b0 c0 (bHeadOr z vs) hp.1 hi; rw [bHeadOr_eq z vs] at hc; exact hc
    | cons b bR =>
      rw [uMulZ, uConsNat_eq] at h ⊢; cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSlide, uOfNatHb] at h ⊢; rw [bDec_nil, rkmUltraSlideLoopAux]
          have hp := bAllPos_uCons h; have hi := bSlide_sound z d rem b z bR [] [] hp.2
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
private def bStg (z dg mL cL : ℕ) (bns bzs vns cns : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlide z d nL 0 0 z bns bzs vns cns) fun out => cond (bAllPos out) (some out) none
private theorem bStg_sound (z dg mL cL : ℕ) (bns vns cns out : List ℕ)
    (h : bStg z dg mL cL bns (uMulZ z bns) vns cns = some out) :
    bDec z out = rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z vns) (bDec z cns) := by
  unfold bStg at h; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq] at h; revert h
  cases hp : bAllPos (bSlide z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 0 z
      bns (uMulZ z bns) vns cns) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]
    have hp0 : bAllPos (bSlide z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 (Nat.mul 0 z) z
        bns (uMulZ z bns) vns cns) = true := by rw [← n0m z]; exact hp
    have hs := bSlide_sound z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z bns vns cns hp0
    rw [← n0m z] at hs; exact hs
private def bBind (z dg mL cL : ℕ) (bns bzs vns cns : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL =>
    match bStg z dg mL cL bns bzs vns cns with | none => none | some out => k nL out
private theorem bBind_sound {z dg mL cL : ℕ} {bns vns cns out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBind z dg mL cL bns (uMulZ z bns) vns cns kB = some out)
    (hk : ∀ (mid : List ℕ), kB (rkmNextLen mL cL) mid = some out →
      bDec z out = kU (rkmNextLen mL cL) (bDec z mid)) :
    bDec z out = (HighDForce.withForcedNat (rkmNextLen mL cL) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage dg mL cL (uOfNatHb bns) (bDec z vns) (bDec z cns)) (kU nL)) := by
  unfold bBind at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h
  revert h; cases hs : bStg z dg mL cL bns (uMulZ z bns) vns cns with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bStg_sound z dg mL cL bns vns cns mid hs]
    exact hk mid h
private def bStep (z mL c : ℕ) (bns bzs vns : List ℕ) : Option (List ℕ) :=
  bBind z 16 mL c bns bzs vns vns fun l1 c1 => bBind z 15 mL l1 bns bzs vns c1 fun l2 c2 =>
  bBind z 14 mL l2 bns bzs vns c2 fun l3 c3 => bBind z 13 mL l3 bns bzs vns c3 fun l4 c4 =>
  bBind z 12 mL l4 bns bzs vns c4 fun l5 c5 => bBind z 11 mL l5 bns bzs vns c5 fun l6 c6 =>
  bBind z 10 mL l6 bns bzs vns c6 fun l7 c7 => bBind z 9 mL l7 bns bzs vns c7 fun l8 c8 =>
  bBind z 8 mL l8 bns bzs vns c8 fun l9 c9 => bBind z 7 mL l9 bns bzs vns c9 fun la ca =>
  bBind z 6 mL la bns bzs vns ca fun lb cb => bBind z 5 mL lb bns bzs vns cb fun lc cc =>
  bBind z 4 mL lc bns bzs vns cc fun ld cd => bBind z 3 mL ld bns bzs vns cd fun le ce =>
  bBind z 2 mL le bns bzs vns ce fun lf cf => bStg z 1 mL lf bns bzs vns cf
private theorem bStep_sound (z mL cL : ℕ) (bns vns out : List ℕ)
    (h : bStep z mL cL bns (uMulZ z bns) vns = some out) :
    bDec z out = rkmUltraHornerT16Step mL cL (uOfNatHb bns) (bDec z vns) := by
  unfold bStep at h; unfold rkmUltraHornerT16Step
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  refine bBind_sound h fun _ h => bBind_sound h fun _ h => bBind_sound h fun _ h => ?_
  exact bStg_sound _ _ _ _ _ _ _ _ h
private def bIter (z : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, _, vns => some vns
  | k + 1, mL, cL, bns, bzs, vns => match bStep z mL cL bns bzs vns with
    | none => none | some vNext => fN (rkmNextLen16 mL cL) fun nL => bIter z k mL nL bns bzs vNext
private theorem bIter_sound (z : ℕ) : ∀ (k mL cL : ℕ) (bns vns out : List ℕ),
    bIter z k mL cL bns (uMulZ z bns) vns = some out →
    bDec z out = muxUltraIterFullT16Rkm k mL cL (uOfNatHb bns) (bDec z vns)
  | 0, _, _, _, _, _, h => by injection h with h'; subst h'; rfl
  | k + 1, mL, cL, bns, vns, out, h => by
    unfold bIter at h; revert h; cases hs : bStep z mL cL bns (uMulZ z bns) vns with
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
    | some vns => fL (uMulZ z bns) fun bzs => match bIter z k mL cL bns bzs vns with
      | none => muxUltraIterFullT16Rkm k mL cL hb v | some out => bDec z out
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; dsimp only [fL]; cases hh : uToNatHb hb with
  | none => rfl
  | some bns =>
    dsimp only; cases hv : bEnc 10000000000000000 v with
    | none => rfl
    | some vns =>
      dsimp only; rw [rkmb_forceList_eq]
      cases hi : bIter 10000000000000000 k mL cL bns (uMulZ 10000000000000000 bns) vns with
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
private theorem rkmHd {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : b = true := (rkmAllTrueF_cons h).1
private theorem rkmTl {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def pzig : List ℕ → List ℤ
  | [] => []
  | w :: ws => (match Nat.mod w 2 with
    | 0 => primOfNatForced (Nat.div w 2) | _ => primNegSuccForced (Nat.div w 2)) :: pzig ws
private def pzigCat : List (List ℕ) → List ℤ | [] => [] | ws :: wss => pzig ws ++ pzigCat wss
private def phbv_g0 : List ℤ := pzigCat
  [
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
    1376004022233960,1378900038144286,1381753818910036,1384565719273538,1387336087286786,
    1390065264483540,1392753586045594,1395401380963432,1398008972191534,1400576676798504,
    1403104806112264,1405593665860500,1408043556306542,1410454772380852,1412827603808320,
    1415162335231488,1417459246329890,1419718611935656,1421940702145488,1424125782429188,
    1426274113734832,1428385952590742,1430461551204344,1432501157558054,1434505015502276,
    1436473364845642,1438406441442554,1440304477278174,1442167700550904,1443996335752470,
    1445790603745696,1447550721840028,1449276903864900,1450969360241020,1452628298049624],
   [1454253921099792,1455846429993874,1457406022191088,1458932892069376,1460427230985520,
    1461889227333650,1463319066602114,1464716931428834,1466083001655156,1467417454378236,
    1468720464002046,1469992202287000,1471232838398280,1472442538952866,1473621468065336,
    1474769787392470,1475887656176686,1476975231288330,1478032667266896,1479060116361168,
    1480057728568316,1481025651672020,1481964031279586,1482873010858140,1483752731769890,
    1484603333306504,1485424952722598,1486217725268416,1486981784221652,1487717260918494,
    1488424284783892,1489102983361056,1489753482340232,1490375905586756,1490970375168412,
    1491537011382108,1492075932779900,1492587256194356,1493071096763306,1493527567953976,
    1493956781586520,1494358847856982,1494733875359672,1495081971109008,1495403240560804,
    1495697787633040,1495965714726108,1496207122742564,1496422111106380,1496610777781730,
    1496773219291286,1496909530734084,1497019805802910,1497104136801278,1497162614659954,
    1497195328953084,1497202367913888,1497183818449972,1497139766158242,1497070295339412,
    1496975489012176,1496855428926964,1496710195579368,1496539868223200,1496344524883200,
    1496124242367396,1495879096279154,1495609161028856,1495314509845294,1494995214786718,
    1494651346751588,1494282975489004,1493890169608844,1493472996591602,1493031522797926,
    1492565813477878,1492075932779900,1491561943759502,1491023908387684,1490461887559068,
    1489875941099774,1489266127775030,1488632505296514,1487975130329440,1487294058499394,
    1486589344398912,1485861041593804,1485109202629244,1484333879035596,1483535121334024,
    1482712979041834,1481867500677598,1480998733766032,1480106724842642,1479191519458146,
    1478253162182646,1477291696609594,1476307165359506,1475299610083474,1474269071466434,
    1473215589230210,1472139202136348,1471039947988716,1469917863635876,1468772984973256,
    1467605346945068,1466414983546042,1465201927822900,1463966211875642,1462707866858596,
    1461426922981236,1460123409508802,1458797354762682,1457448786120566,1456077730016398,
    1454684211940082,1453268256436968,1451829887107126,1450369126604368,1448885996635064,
    1447380517956712,1445852710376278,1444302592748316,1442730182972834,1441135497992932,
    1439518553792202,1437879365391874,1436217946847736,1434534311246794,1432828470703680,
    1431100436356818,1429350218364330,1427577825899672,1425783267147032,1423966549296434,
    1422127678538596,1420266660059500,1418383498034686,1416478195623272,1414550754961682,
    1412601177157084,1410629462280528,1408635609359794,1406619616371918,1404581480235426,
    1402521196802230,1400438760849220,1398334166069504,1396207405063344,1394058469328708,
    1391887349251514,1389694034095484,1387478511991654,1385240769927502,1382980793735702,
    1380698568082474,1378394076455562,1376067301151782,1373718223264160,1371346822668654],
   [1368953078010422,1366536966689666,1364098464846986,1361637547348302,1359154187769264,
    1356648358379186,1354120030124466,1351569172611496,1348995754089016,1346399741429958,
    1343781100112684,1341139794201690,1338475786327674,1335789037667030,1333079507920696,
    1330347155292352,1327591936465970,1324813806582674,1322012719216890,1319188626351778,
    1316341478353928,1313471223947260,1310577810186170,1307661182427828,1304721284303650,
    1301758057689904,1298771442677416,1295761377540352,1292727798704050,1289670640711876,
    1286589836191046,1283485315817418,1280357008279190,1277204840239478,1274028736297744,
    1270828618950022,1267604408547904,1264356023256252,1261083379009576,1257786389467060,
    1254464965966138,1251119017474632,1247748450541344,1244353169245086,1240933075142060,
    1237488067211556,1234018041799892,1230522892562512,1227002510404224,1223456783417440,
    1219885596818414,1216288832881326,1212666370870200,1209018086968520,1205343854206478,
    1201643542385750,1197917018001708,1194164144162970,1190384780508152,1186578783119750,
    1182746004434994,1178886293153580,1174999494142114,1171085448335178,1167143992632822,
    1163174959794362,1159178178328312,1155153472378290,1151100661604708,1147019561062072,
    1142909981071678,1138771727089522,1134604599569184,1130408393819464,1126182899856528,
    1121927902250308,1117643179964878,1113328506192532,1108983648181250,1104608367055246,
    1100202417628246,1095765548209140,1091297500399656,1086798008883604,1082266801207312,
    1077703597550794,1073108110489132,1068480044743636,1063819096922164,1059124955248100,
    1054397299277326,1049635799602566,1044840117544426,1040009904828342,1035144803246720,
    1030244444305382,1025308448853442,1020336426695666,1015327976186288,1010282683803196,
    1005200123701330,1000079857244028,994921432511000,989724383781482,984488230991040,
    979212479160366,973896617794288,968540120249084,963142443066036,957703025269006,
    952221287623652,946696631855678,941128439825336,935516072655172,929858869807720,
    924156148109630,918407200718350,912611296027234,906767676504492,900875557461076,
    894934125742120,888942538336044,882899920894946,876805366159266,870657932279048,
    864456641023414,858200475869014,851888379957336,845519253909708,839091953487724,
    832605287085498,826058013038806,819448836734478,812776407501642,806039315264418,
    799236086933276,792365182509724,785424990876052,778413825238414,771329918187788,
    764171416338924,756936374502392,749622749339086,742228392439946,734751042765960,
    727188318374736,719537707349638,711796557835526,703962067071244,696031269292604,
    688001022360444,679867992945686,671628640076470,663279196820524,654815649837942,
    646233716493758,637528819164888,628696056309378,619730169785086,610625507806040],
   [601375982803200,591975023306048,582415518774508,572689756076544,562789346011498,
    552705137903964,542427119812548,531944301277014,521244574718288,510314550540710,
    499139359569044,487702414546496,475985119823070,463966514778214,451622831498606,
    438926940080076,425847644558606,412348777158288,398388015407688,383915310862546,
    368870761182712,353181663725502,336758329478034,319487953211432,301225307808042,
    281777985428678,260881682800392,238155838178624,213016301570066,184479635726534,
    150628138795948,106510583894510]]
private def pvm_c0_1 : List ℤ := pzigCat
  [
   [129126,916084,4588962,18741264,66184244,208734820,600043662,1594537190,3957552332,9246503492,
    20463679190,43114816642,86837438390,167778864970,311892492718,559267598968,969499589362,
    1627937150068,2652413662362,4199800316020,6471441643690,9716299425890,14230496081128,
    20351971725088,28449196032742,38903328328270,52083883577034,68318784561946,87860569391992,
    110851357669842,137289825147994,167003771969640,199631801881478,234617118209908,
    271215508489632,308518319093292,345489754449980,381016348615760,413965136380940,
    443246065522246,467873667345202,487023004600234,500075440226962,506650746386776,
    506623375599702,500122184504074,487514364645200,469375634854466,446449759224082,
    419601091739288,389764082658904,357893531290736,324918894421108,291705247299878,
    259022646676450,227524764684960,197736838105926,170052278980208,144736764187524,
    121938282524646,101701464371200,83984529650648,68677330965144,55619201155454,44615598367916,
    35452841137096,27910511867540,21771358402382,16828727370390,12891714481236,9788316769002,
    7366925261948,5496511692452,4065848861576,2982070321644,2168829435518,1564267501736,
    1118950756096,793890305670,558719595932,390071833548,270174960004,185663746586,126596447806,
    85656126628,57513155942,38324495892,25346273292,16638241974,10841341238,7012402082,4502815706,
    2870515256,1816845730,1141779870,712485338,441490414,271669244,166017952,100759538,60737138,
    36364674,21626294,12775578,7497098,4370580,2531252,1456456,832608,472898,266870,149636,83358,
    46132,25354,13836,7498,4024,2138,1116,570,282,130,56,18,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_2 : List ℤ := pzigCat
  [
   [4670,35556,191150,838264,3178910,10766248,33235042,94839378,252765772,634166836,1507096062,
    3409665714,7374237434,15299210844,30539025510,58801066036,109452394916,197344117250,
    345249876408,586980205848,971169885362,1565637542054,2462086811178,3780764392970,
    5674527966900,8331629308160,11976413899220,16867108739784,23289942885644,31549039685170,
    41951840540066,54790253484510,70318231771296,88727024992822,110119841382026,134488042802934,
    161691196542336,191443279273722,223307042842736,256698015015424,290898860960126,
    325083943464504,358352984697902,389771853444722,418417779914578,443425819719744,
    464033205819518,479618363457506,489731802201076,494116790413408,492718583029568,
    485681919200928,473337433985286,456178447520210,434830233782998,410014281855446,
    382510226450914,353118049695902,322622874708286,291764232540094,261211146383154,
    231543801394952,203242011092366,176680197950376,152128209314420,129757008188794,
    109648116237008,91805635945172,76169724015666,62630506810332,51041596919272,41232564117652,
    33019913226780,26216308967014,20637951797844,16110141792108,12471166906560,9574718240858,
    7291071255860,5507283318796,4126649998126,3067640946518,2262506235242,1655710100902,
    1202314745552,866404631146,619613257760,439790568126,309830126016,216660876180,150398127222,
    103641763560,70905896298,48162529080,32481735336,21751802956,14464384784,9551584166,
    6263876076,4079663256,2639000824,1695543640,1082062674,685944832,431954702,270220310,
    167937100,103691218,63609400,38770516,23480072,14129638,8449136,5020640,2964724,1739812,
    1014668,588126,338792,193960,110356,62394,35058,19568,10844,5962,3248,1750,922,474,236,108,48,
    16,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_3 : List ℤ := pzigCat
  [
   [134,1104,6248,29244,118622,429870,1420134,4336978,12370322,33214466,84473854,204525504,
    473373164,1051000522,2245085988,4625976478,9214683354,17779222812,33285269104,60557573244,
    107216887214,184960380238,311248205554,511441113698,821400210798,1290507619560,1984995447642,
    2991382634122,4419721184850,6406255304176,9115012922810,12737795573028,17492026508278,
    23615973432688,31360991280954,40980634514400,52716759813616,66783060392168,83346813628180,
    102509947460828,124290797027532,148608091313866,175268746774042,203960929585656,
    234253575241234,265603136811808,297367802976702,328828830888782,359218034754568,
    387749920147018,413656514475320,436222662999566,454819468108998,468933657916934,
    478190967903886,482372075983456,481420200838526,475440099536274,464688823807756,
    449559158878672,430557127514394,408275261754306,383363508451744,356499641418262,
    328360916811874,299598455421666,270815499607338,242550311324964,215264087750774,
    189333905174866,165050385987470,142619535391758,122168022977872,103751090436302,
    87362244639418,72943934197796,60398493406370,49598754991266,40397867376612,32637990070264,
    26157671436834,20797828686010,16406345390844,12841374998368,9973489606636,7686843485446,
    5879533306162,4463335340578,3362987690910,2515166453616,1867281713014,1376194968336,
    1006935972360,731475360158,527590701074,377848099282,268709240708,189764634586,133087371808,
    92697583740,64125477832,44059913722,30069572668,20384534172,13727238322,9183176462,6103067842,
    4029644568,2643418682,1722911144,1115768766,717986486,459097698,291713430,184198296,115586648,
    72083756,44677542,27521846,16850624,10254580,6202918,3729614,2229118,1324386,782198,459244,
    268038,155518,89694,51414,29292,16586,9320,5194,2866,1562,838,434,216,102,44,14,2,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_4 : List ℤ := pzigCat
  [
   [2,40,182,812,3456,13278,46726,152210,463206,1327102,3601498,9304450,22978720,54437846,
    124080348,272798418,579806998,1193648950,2384366016,4628523944,8743526680,16093397594,
    28894665206,50657578012,86803605538,145503652274,238780799112,383914590814,605168740244,
    935838743354,1420579144516,2117922144194,3102841694132,4469154043764,6331482956096,
    8826463597234,12112822954720,16369966564038,21794730464064,28596030417508,36987260334970,
    47176456106908,59354441195134,73681391756840,90272481802144,109183469281782,130397237187712,
    153812386589194,179234972732260,206374370302386,234844048892810,264167744685472,
    293791149958790,323098837853004,351435731502236,378132052183528,402530376701164,
    424013230079700,442029556685988,456118460325356,465928778121388,471233338316120,
    471937122365598,468078973319806,459826928245848,447467665423310,431390914212420,
    412069950879038,390039480348522,365872274983006,340155910018200,313470812902762,
    286370648798608,259365819530834,232910582602210,207394024027848,183134864412748,
    160379858297056,139305373581392,120021616673820,102578900656010,86975334711788,73165336465948,
    61068425784936,50577839041752,41568596931224,33904757582086,27445682330066,22051228248394,
    17585855412558,13921695737120,10940673471210,8535795750684,6611746573846,5084921367488,
    3883034384896,2944419981670,2217133627980,1657941308514,1231268329112,908161693260,
    665304954680,484111281514,349909596054,251230077928,179188886980,126967424438,89378510052,
    62510197528,43437280962,29990595266,20574750998,14025784566,9501201292,6395935074,4278768936,
    2844707864,1879641662,1234369622,805679114,522684198,337046968,216037142,137646840,87179938,
    54889816,34356110,21377900,13224720,8133542,4973424,3023600,1827664,1098444,656412,390026,
    230424,135362,79054,45898,26484,15186,8644,4884,2732,1506,814,432,220,104,46,14,2,0,0,0,0,0,0,
    0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_5 : List ℤ := pzigCat
  [
   [0,8,28,54,170,630,2246,7642,24424,73658,210540,573018,1490824,3720780,8934386,20693298,
    46333422,100486484,211456322,432417822,860513306,1668495960,3155717520,5828066218,10519957546,
    18575600012,32111283106,54384951694,90303182582,147097944052,235205027494,369371441786,
    570008948780,864794038172,1290490134764,1894935548402,2739101457510,3899080151154,
    5467818310824,7556368125140,10294396439550,13829675533630,18326284998344,23961288110870,
    30919711704422,39387756584936,49544293247454,61550848202018,75540448912618,91605856137428,
    109787855077656,130064384323896,152341338526766,176445874652674,202122975300838,
    229035874965346,256770742586574,284845749598254,312724356455706,339832346323152,
    365577848366286,389373350621454,410658526194242,428922603496698,443725010878092,
    454713119426396,461636087473548,464354061270858,462842287159876,457190016222594,
    447594406397688,434349924175976,417833996572030,398489847800546,376807564171140,
    353304462289598,328505793480222,302926710895504,277056268842880,251344032885614,
    226189671645322,201935693640868,178863299601440,157191154121920,137076748322496,
    118619931605400,101868136385056,86822802450744,73446522667028,61670472689746,51401747120996,
    42530295798612,34935229960172,28490343020078,23068760040810,18546690376776,14806307436292,
    11737817240962,9240803640762,7224953603878,5610272387376,4326897341424,3314612429244,
    2522155012248,1906393638856,1431441815172,1067759083734,791277962090,582583907940,
    426165764666,309746199626,223695436854,160526967252,114470695240,81116924824,57123467632,
    39977751880,27805928192,19221437780,13206195866,9018341260,6121334026,4129991252,2769802062,
    1846535024,1223736754,806217622,528034570,343819064,222569984,143246352,91662566,58318008,
    36891500,23204560,14512888,9025634,5581550,3432370,2098956,1276408,771894,464214,277628,
    165120,97654,57420,33568,19504,11262,6450,3662,2056,1136,618,324,162,72,28,8],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_6 : List ℤ := pzigCat
  [
   [0,0,16,24,24,52,118,348,1094,3416,10174,29084,79534,208752,527202,1284368,3024792,6900002,
    15272136,32848688,68754946,140216716,278931376,541807102,1028611804,1910266632,3473111512,
    6186514840,10803710206,18508675656,31125083902,51406584554,83430516694,133119013224,
    208911600310,322610944540,490417413944,734157706524,1082697255298,1573505109354,2254313736666,
    3184785652482,4438065766470,6102065598384,8280296622626,11092049209756,14671705483920,
    19166983283202,24735937909416,31542600720260,39751209116980,49519078955402,60988283022088,
    74276420505724,89466882628830,106599127516162,125659561149856,146573669763844,169200053097326,
    193326961592120,218671842097284,244884248948728,271552288349036,298212546221380,
    324363219150580,349479942833676,373033611312690,394509320493714,413425465355528,
    429351981590732,441926753458270,450869308654182,455991080521334,457201725365188,
    454511221651666,448027729841516,437951437491966,424564836207010,408220059988648,
    389324047416038,368322366402074,345682558485308,321877822799362,297371775112026,
    272604894773946,247983124093768,223868923296830,200574922145096,178360157435792,
    157428752801172,137930789816426,119965041007884,103583186958568,88795120058616,75574943422278,
    63867300658828,53593715357588,44658672907740,36955236429750,30370048517640,24787627369314,
    20093916834568,16179093025628,12939664408300,10279927511322,8112856986360,6360517619418,
    4954088235670,3833584600954,2947361770558,2251467154256,1708904989754,1288861886640,
    965932354778,719373291840,532407618180,391589791640,286239863414,207947999452,150147878652,
    107754931856,76863831702,54498805378,38410054466,26909679028,18740889256,12974844054,
    8930100398,6110327992,4156599834,2811180514,1890284540,1263759574,840061846,555236614,
    364901186,238458560,154953338,100126518,64337918,41111554,26124566,16509404,10375762,6485190,
    4031322,2492312,1532470,937184,570038,344854,207488,124160,73892,43722,25722,15042,8730,5030,
    2872],
   [1618,896,482,250,122,54,20,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_7 : List ℤ := pzigCat
  [
   [0,0,6,24,18,24,30,48,60,166,440,1252,3510,9632,25488,65166,161160,386132,897664,2027946,
    4458290,9549692,19953062,40707662,81170496,158325942,302332158,565607666,1037389384,
    1866551236,3296604462,5718246150,9746593608,16332320354,26918216318,43655080266,69693070530,
    109566339322,169689493288,258983595944,389646424606,578075872396,845946164618,1221423531010,
    1740491018210,2448331529178,3400694745322,4665148727254,6322092722752,8465386625894,
    11202437643118,14653579240132,18950584448072,24234177669138,30650447885604,38346121968602,
    47462728289700,58129764916754,70457078336564,84526751261366,100384883790406,118033722557820,
    137424639239464,158452475699658,180951752833724,204695181172178,229394814128410,
    254706053431780,280234558195800,305545934554014,330177904318722,353654482235998,
    375501545566152,395263068986160,412517231751798,426891588790286,438076534983488,
    445836380142600,450017484783664,450553074006408,447464536175278,440859210847648,
    430924862387592,417921208799974,402169018393722,384037391650170,363929907209826,
    342270327824388,319488536476394,296007309646552,272230441230486,248532615712474,
    225251302420672,202680813393186,181068544111152,160613306216172,141465569656936,
    123729361872094,107465525026754,92696008607972,79408871979762,67563686796026,57097058733102,
    47928027750468,39963151948626,33101128299760,27236850829468,22264850632918,18082100532608,
    14590199058672,11696973228858,9317557356870,7375016287934,5800586827406,4533611657366,
    3521236777616,2717937502878,2084930264712,1589518750234,1204413958198,907059106090,
    678982366966,505193398044,373633674600,274685792648,200743112790,145838294736,105327296146,
    75624144334,53981098702,38308574192,27029274318,18961287144,13225344050,9171964912,6324764374,
    4336736196,2956843200,2004702740,1351567262,906151378,604155162,400580652,264139952,173216640,
    112970516,73277226,47272612,30331574,19356778,12286598,7757070,4871234,3042714,1890470,
    1168352,718246,439206,267150,161632],
   [97274,58216,34642,20498,12050,7034,4072,2332,1318,730,394,202,96,38,12,2,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_8 : List ℤ := pzigCat
  [
   [0,0,3,16,18,22,14,36,32,36,40,82,164,398,1042,2734,7032,17610,42898,101648,234394,526674,
    1154336,2470450,5167456,10573262,21179450,41563802,79966370,150927030,279609080,508745258,
    909576544,1598743934,2763870418,4701563742,7872796610,12982078748,21088488618,33758406428,
    53271548176,82893442228,127228536996,192668331392,287947861802,424821109006,618860950822,
    890381787428,1265472636650,1777115276132,2466346125576,3383402607626,4588775704378,
    6154071776850,8162570273410,10709351872022,13900866194438,17853811766260,22693215346098,
    28549624500344,35555366886402,43839881564642,53524189952912,64714643617452,77496158557720,
    91925215568180,108022967570922,125768841272440,145095046292080,165882405254808,
    187957890063906,211094191587960,235011563629318,259382071115880,283836243170366,
    307971992246578,331365520451382,353583803685522,374198133275452,392798112144696,
    409005455168944,422486935482944,432965851482356,440231461283416,444145937673574,
    444648529733562,441756768031840,435564708134866,426238361438446,414008602908406,
    399161963525736,382029804383370,362976425240012,342386681288232,320653668902748,
    298166997476310,275302095283362,252410909118094,229814257434020,207795992172554,
    186599022263716,166423157863888,147424653469874,129717263395232,113374576496506,
    98433368863234,84897702549332,72743503432558,61923369324598,52371387470532,44007775377330,
    36743197400082,30482648888832,25128837591644,20585026570394,16757332814422,13556500260790,
    10899184758426,8708801756316,6915995579024,5458792719350,4282501404002,3339416599460,
    2588384437042,1994273499486,1527393181210,1162891952696,880161243960,662264115100,
    495402096942,368428662496,272413758634,200260654804,146373984382,106376166836,76868300080,
    55230992358,39460355518,28034414298,19805413756,13913862644,9720578566,6753458166,4666152550,
    3206262204,2191064330,1489140468,1006581508,676710842,452487130,300930416,199062950,130974534,
    85716170,55798882,36131180,23272332,14910946,9503518,6025384],
   [3800246,2384348,1488210,924060,570792,350750,214410,130382,78862,47440,28378,16876,9974,5848,
    3398,1952,1108,614,324,166,80,30,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_9 : List ℤ := pzigCat
  [
   [0,0,5,6,14,22,10,20,26,36,28,30,36,50,74,132,286,698,1702,4166,10000,23508,53952,120990,
    265138,568422,1193054,2453322,4945826,9781078,18986952,36198040,67810980,124885324,226212940,
    403185434,707375020,1222133292,2080026574,3488589822,5767708256,9402938324,15120245662,
    23988937196,37560930678,58055831670,88602419462,133547872060,198846125666,292535862362,
    425316420880,611226098572,868421567874,1220049262210,1695189531006,2329842258190,
    3167908864658,4262110853442,5674770287986,7478364103992,9755753473938,12599983261084,
    16113546634370,20407017743346,25596972220224,31803141898110,39144786506938,47736310364862,
    57682204401874,69071450459812,81971582074010,96422649559846,112431382537090,129965875372024,
    148951136179636,169265834655724,190740556026356,213157817332616,236254029438618,
    259723496738660,283224441461282,306386927075722,328822442960390,350134807982774,
    369931961567024,387838143954640,403505928039778,416627556829456,426945064466630,
    434258713739184,438433365687938,439402501925638,437169740631350,431807814943322,
    423455109334376,412309967513790,398623087349448,382688398543250,364832873380048,
    345405747837136,324767629705642,303279944017804,281295117458268,259147837233492,
    237147641515204,215573013801244,194667067950362,174634829328266,155642044704180,
    137815392489660,121243917705412,105981483658068,92050014609664,79443299727474,68131136600508,
    58063610402322,49175329899852,41389471427748,34621514257252,28782583334696,23782346351640,
    19531440147266,15943425573656,12936289624302,10433528648826,8364856975440,6666591594514,
    5281766249208,4160027954918,3257366292018,2535721437288,1962511419174,1510113030440,
    1155324643414,878833190712,664702046624,499891632382,373820362718,277970077878,205537346154,
    151129924374,110506153738,80354060402,58106334836,41787096408,29886329156,21258033130,
    15038413222,10580776432,7404191868,5153357418,3567492516,2456425946,1682362356,1146088066,
    776615790,523469400,350978212,234088234,155308890],
   [102503080,67298876,43955706,28560472,18461388,11871832,7595064,4834040,3060974,1928342,
    1208610,753648,467550,288580,177204,108242,65780,39754,23888,14272,8468,4988,2908,1674,948,
    524,278,140,64,24,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_10 : List ℤ := pzigCat
  [
   [0,0,5,0,4,22,10,16,10,30,28,30,30,32,32,44,46,64,92,188,386,896,2074,4798,10966,24588,53998,
    116202,245158,507502,1031242,2058012,4035704,7780110,14751672,27521642,50542930,91404110,
    162834980,285861426,494687450,844127952,1420743740,2359256940,3866366610,6254752282,
    9990852488,15760927374,24560934600,37816816180,57542831288,86546464622,128689036552,
    189211254304,275132348256,395729890454,563104645526,792830629542,1104684776118,1523443146838,
    2079721523798,2810827703088,3761581290270,4985044928212,6543099533816,8506786358898,
    10956331751660,13980767686362,17677063725610,22148695200104,27503588851380,33851411353404,
    41300197808850,49952355631456,59900122590380,71220603907588,83970559255332,98181152916476,
    113852915636520,130951191246110,149402351759458,169091058835112,189858825672918,
    211504091282810,233783959629168,256417681867488,279091874509604,301467374760154,
    323187542135534,343887728875286,363205566572730,380791658322568,396320228934532,
    409499273439866,420079757608668,427863463100382,432709132006774,434536647117438,
    433329080118952,429132544078716,422053892450412,412256407992390,399953715440630,
    385402226484360,368892480763516,350739779924690,331274522467882,310832635938284,
    289746472073832,268336483033110,246903936822526,225724861994338,205045340180436,
    185078194420284,166001055401130,147955729811472,131048747333724,115352926789850,
    100909778140652,87732545160564,75809692714406,65108651179458,55579646856866,47159469192714,
    39775051246558,33346767176902,27791377851014,23024581604316,18963150577418,15526653189368,
    12638779728230,10228300613512,8229695708930,6583498429890,5236400723502,4141164805158,
    3256385355324,2546142245192,1979579268144,1530439241478,1176580578600,899495304622,
    683843713762,517016589322,388732209998,290672280862,216158446682,159869130614,117595035294,
    86030678438,62598736896,45303670328,32611021234,23348880664,16628218272,11779057788,
    8299800352,5817333228,4055890884,2812945442],
   [1940687752,1331912792,909343636,617616110,417305070,280504086,187577648,124791534,82595620,
    54387890,35630860,23223856,15060230,9716802,6237540,3983890,2531676,1600736,1007030,630344,
    392578,243266,149976,91984,56124,34058,20552,12328,7336,4336,2536,1464,830,454,240,120,54,18,
    4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_11 : List ℤ := pzigCat
  [
   [0,0,5,0,5,18,10,16,8,12,20,28,30,32,24,34,34,48,40,48,56,70,108,210,412,900,1984,4432,9754,
    21094,44760,93388,191496,386056,765556,1493762,2869054,5426408,10110192,18562122,33593780,
    59949718,105521364,183248544,314053554,531301452,887479632,1464054838,2385805136,3841353864,
    6112158742,9612836378,14946426344,22979001868,34938882720,52546544548,78182068480,
    115097528456,167681934008,241786073892,345113657640,487683338646,682363339798,945476336296,
    1297466878864,1763616945330,2374787284554,3168153295330,4187894660094,5485788390862,
    7121646077960,9163528832800,11687668666866,14778023864206,18525399256586,23026071029040,
    28379870344432,34687700903340,42048492323034,50555623183780,60292883456570,71330083965286,
    83718458242684,97486036959876,112633204201226,129128665409080,146906066283828,165861498249742,
    185852107970086,206695995420988,228173537859314,250030217383092,271980960469756,
    293715922585310,314907574071606,335218869821236,354312219565820,371858922446924,
    387548692744780,401098886062902,412263038529206,420838355927774,426671833956572,
    429664752512650,429775362374148,427019667327438,421470293574550,413253525869782,
    402544671199042,389561981406520,374559422320792,357818616038398,339640303688690,
    320335678066250,300217919979990,279594241062704,258758691955718,237985941635544,
    217526174874946,197601194135230,178401753047336,160086094092304,142779615584834,
    126575554359760,111536541698740,97696871354522,85065309734192,73628278559406,63353248390482,
    54192195765670,46084995713378,38962643371686,32750221818628,27369556570258,22741519369552,
    18787963956704,15433293844790,12605676352948,10237928138020,8268105282554,6639835870280,
    5302435250492,4210844273228,3325429113990,2611678344672,2039829065448,1584449565868,
    1224001449024,940399687216,718584873868,546118129580,412805792010,310358207736,232084650636,
    172624591884,127714196924,93985970308,68798848866,50095697676,36285031648],
   [26143816516,18738349648,13360444658,9476412244,6686618770,4693694092,3277740040,2277149474,
    1573879820,1082231538,740359882,503900772,341217988,229884002,154092172,102766700,68191324,
    45021030,29574408,19330160,12571238,8134824,5237802,3355718,2139236,1356970,856500,537928,
    336160,209028,129320,79600,48744,29680,17970,10816,6460,3828,2240,1292,730,402,210,102,44,14,
    2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_12 : List ℤ := pzigCat
  [
   [0,0,5,0,13,6,10,16,8,10,10,12,20,32,24,32,22,32,38,42,38,52,44,52,50,78,112,198,356,726,1586,
    3410,7268,15274,31604,64386,129202,255342,497142,953854,1804004,3364306,6188330,11230370,
    20112850,35556726,62064706,106990148,182186406,306516780,509621682,837495672,1360631500,
    2185751760,3472478828,5456699886,8482869270,13048053482,19861155994,29921437724,44621139774,
    65877663196,96301294860,139404791202,199861130402,283815281012,399254769316,556442007012,
    768408630558,1051508394714,1426020392392,1916788553816,2553876608658,3373210189800,
    4417169855592,5735090980486,7383619308336,9426865187386,11936295889646,14990304766846,
    18673399074372,23074955756480,28287506783534,34404532946026,41517767169448,49714034849694,
    59071688420256,69656724927848,81518707010436,94686637248204,109164961128900,124929892560018,
    141926265859032,160065117704532,179222190409842,199237523551180,219916264709248,
    241030782988400,262324113033816,283514695218218,304302312878736,324375063730610,
    343417143804618,361117172262474,377176747645688,391318903245164,403296123183278,
    412897592277076,419955381470854,424349315145700,426010324463796,424922158767708,
    421121400995102,414695808815500,405781076441890,394556178766636,381237516097334,
    366072121549500,349330222213658,331297458668214,312267065358008,292532297831866,
    272379363661902,252081074505126,231891390089348,212040973979872,192733828867282,
    174145028654320,156419518285616,139671912041942,123987188330978,109422154681380,
    96007540945716,83750571380472,72637866602462,62638533386744,53707312610114,45787671977900,
    38814749101232,32718070688694,27423993889496,22857835170876,18945669742066,15615799888632,
    12799903312258,10433882539290,8458443699116,6819437647932,5467998797758,4360517441516,
    3458480215672,2728210988930,2140541272176,1670435535960,1296592882306,1001042578972,
    768747205704,587223713202,446189641212,337239124484],
   [253551148354,189630783694,141082803742,104416119364,76876812638,56307152004,41027781724,
    29740248752,21447117956,15387095932,10982804486,7799093104,5510036948,3873019336,2708536328,
    1884579718,1304650286,898624574,615845484,419932176,284908246,192333002,129190290,86345060,
    57422328,37998272,25020196,16393252,10687856,6933794,4476190,2875462,1838100,1169214,740082,
    466152,292166,182214,113076,69810,42870,26190,15902,9592,5744,3410,2002,1154,652,356,186,88,
    36,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_13 : List ℤ := pzigCat
  [
   [0,0,5,0,13,5,0,16,8,10,10,10,2,20,22,32,26,24,18,34,32,40,40,52,42,46,50,42,62,84,104,148,266,
    520,1068,2246,4646,9552,19368,38746,76498,148942,286076,542156,1013970,1871976,3412316,
    6142882,10923510,19191690,33320750,57180950,97007482,162725464,269946876,442941890,719004230,
    1154782932,1835350866,2887027832,4495283616,6929414520,10576120634,15984604100,23926349530,
    35473317520,52098843802,75806045070,109288922616,156131545958,221050594180,310186024426,
    431443605342,594891383800,813209737880,1102191427398,1481283941894,1974161482876,
    2609308188160,3420587891744,4447769087658,5736967213042,7340960364932,9319329684826,
    11738372511674,14670735669206,18194718540756,22393201436212,27352164564860,33158776880894,
    39899052083808,47655090739098,56501952102604,66504225710402,77712399743320,90159148945128,
    103855687647472,118788351359900,134915581629524,152165491897654,170434185687694,
    189584981966384,209448675851060,229824926593496,250484820252752,271174603635556,
    291620531463950,311534713285766,330621793581588,348586251078436,365140064497754,
    380010464466584,392947477107688,403730965126030,412176887366062,418142527247728,
    421530482724746,422291263166276,420424398920416,415978033898352,409047036731722,
    399769728335420,388323379746824,374918681074012,359793418072354,343205615841236,
    325426418765206,306732972305218,287401556521552,267701194873066,247887926984664,
    228199893138906,208853333815916,190039562247798,171922924063566,154639717762586,
    138298014648172,122978288191852,108734741305618,95597205919078,83573482400750,72651986164796,
    62804574414998,53989436344156,46153944065920,39237377916942,33173457388822,27892626794100,
    23324061954096,19397380010602,16044048388528,13198500640598,10798976230604,8788108248102,
    7113287714712,5726835750290,4586015691634,3652916612032,2894237897758,2281001917732],
   [1788218663690,1394522798542,1081800045210,834816448382,640860874072,489408264484,371808688754,
    281005145116,211281373918,158039611838,117607222582,87070437384,64132984002,46997132028,
    34264591198,24854730012,17937699952,12880226260,9202037324,6541131650,4626310122,3255622262,
    2279581208,1588189110,1100980544,759436536,521244858,355987286,241920948,163592178,110079222,
    73706464,49109644,32560590,21482524,14104232,9214826,5991034,3876106,2495570,1598918,1019448,
    646822,408398,256594,160428,99802,61766,38024,23282,14176,8568,5140,3056,1792,1036,584,318,
    162,72,28,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_14 : List ℤ := pzigCat
  [
   [0,0,5,0,13,5,11,6,8,10,10,18,0,8,4,16,24,34,18,22,16,34,28,38,44,36,46,50,42,34,40,62,62,80,
    92,110,186,324,634,1294,2602,5238,10448,20620,40188,77394,147230,276570,513258,941138,1705388,
    3054346,5407936,9467512,16391094,28068510,47548928,79696680,132185258,216986432,352573722,
    567145058,903279858,1424589342,2225100676,3442341868,5275368512,8009301468,12048322792,
    17959503546,26530299010,38843025898,56370101584,81094238730,115658093074,163547992838,
    229316254788,318846125046,439662477280,601289961910,815658240976,1097551198398,1465093548934,
    1940264091390,2549420029920,3323811459672,4300059496500,5520565925168,7033817027316,
    8894539885276,11163666446674,13908059511918,17199956096162,21116087787074,25736445135626,
    31142663991780,37416026037786,44635083348140,52872937113804,62194222926606,72651878177862,
    84283789898046,97109442294774,111126700785380,126308881929556,142602264935132,159924199164724,
    178161952504092,197172427207062,216782843081192,236792453366486,256975317692974,
    277084110916292,296854898687534,316012762888226,334278115275788,351373498529256,
    367030642836288,380997525301832,393045170318236,402973932478630,410619019757478,
    415855042873788,418599415610548,418814478354926,416508270700116,411733935713544,
    404587795374838,395206190709852,383761228518642,370455616945612,355516802643170,
    339190641745510,321734844792518,303412432302586,284485423698494,265208959099336,
    245826022887968,226562902018550,207625472951500,189196371098758,171433057793050,
    154466763875676,138402257505928,123318357819122,109269096273922,96285414201410,84377278085760,
    73536093037036,63737299066300,54943043259884,47104832788350,40166087845038,34064529091962,
    28734350074288,24108140548628,20118541100270,16699622305716,13787992694582,11323648699700],
   [9250586609450,7517201321660,6076499602898,4886156803034,3908445826204,3110065896496,
    2461896557894,1938699679220,1518789231144,1183685467670,917767043938,707931663664,
    543273164254,414780573752,315062640980,238099655938,179023029446,133922065004,99676598232,
    73813663132,54386028348,39870293688,29082210274,21106954216,15242216298,10952145270,
    7830380058,5570613438,3943334554,2777592010,1946799540,1357768152,942291292,650733866,
    447181396,305794370,208086510,140906258,94949268,63669434,42486538,28213398,18644304,12261002,
    8024118,5225914,3387058,2184640,1402272,895740,569416,360218,226766,142052,88540,54902,33868,
    20780,12670,7666,4608,2742,1608,928,522,280,140,62,22,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private def pvm_c0_15 : List ℤ := pzigCat
  [
   [0,0,5,0,13,5,11,7,0,10,0,20,10,8,4,10,3,18,24,28,14,14,26,20,34,38,36,38,40,58,42,32,44,38,46,
    68,62,76,82,92,120,188,358,660,1298,2564,5030,9776,18904,36106,68196,127368,235206,429532,
    775688,1385580,2448422,4280718,7406038,12681098,21492578,36061238,59905978,98544406,160538594,
    259038566,414034874,655609960,1028578296,1599035162,2463495856,3761506640,5692850382,
    8540754140,12702833632,18731875746,27388955238,39711789740,57101633318,81432359556,
    115185646030,161616288346,224951578946,310628310306,425570224610,578507555004,780338613962,
    1044531122432,1387558106156,1829359711740,2393818258482,3109229343462,4008747018038,
    5130776183934,6519280715362,8223971759840,10300337615592,12809474969760,15817681553778,
    19395772847594,23618090689764,28561179767810,34302119061664,40916509299114,48476134048982,
    57046330685710,66683127343446,77430222157060,89315900407176,102350002374220,116521068443574,
    131793797018528,148106953955316,165371868638256,183471640894342,202261164538498,
    221568047731778,241194478293710,260920044872968,280505484108470,299697281608562,
    318233012974324,335847272524428,352278004120518,367273022613366,380596497646684,
    392035165104082,401404036025866,408551388383750,413362853062642,415764440521570,
    415724397110120,413253827691506,408406071565260,401274869064658,391991404030738,
    380720350244536,367655085780024,353012266530656,337025967809678,319941610460640,
    302009885451466,283480879124556,264598581273078,245595931517828,226690527849214,
    208081086578880,189944707241048,172434961013794,155680788614784,139786164708428,
    124830461657486,110869426623128,97936672873124,86045578672638,75191484990382,65354085900172,
    56499912260968,48584819172280,41556399931224],
   [35356262873454,29922121731438,25189664249838,21094177141598,17571917566996,14561231829312,
    12003430697770,9843437610214,8030230997834,6517105225660,5261776329694,4226359076152,
    3377241111880,2684878367948,2123533659546,1670977816774,1308169876156,1018930023514,
    789616234654,608813007660,467038283814,356472653598,270713255452,204553394392,153787821104,
    115042792524,85629450394,63418671290,46735323388,34269779374,25004549848,18153990486,
    13115174600,9428192984,6744328136,4800739222,3400478360,2396832032,1681140474,1173389760,
    814995966,563308658,387452124,265199744,180640160,122445908,82597252,55447348,37041802,
    24626460,16293436,10728180,7029814,4584240,2975080,1921484,1235046,790024,502914,318592,
    200846,125996,78648,48838,30166,18528,11306,6852,4120,2450,1436,828,460,242,118,52,18,4,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]
private theorem pchk_c0_s0 : rkmAllTrueF [
    muxIntListEq rkmHbHi_m1024_r512_s0_c1 phbv_g0,
    bSlideChk 6 513 phbv_g0 rkmViHi_m1024_r512_s0_c1 pvm_c0_1
  ] = true := by decide +kernel
private theorem pchk_c0_s1 : bSlideChk 6 513
    phbv_g0 pvm_c0_1 pvm_c0_2 = true := by decide +kernel
private theorem pchk_c0_s2 : bSlideChk 6 513
    phbv_g0 pvm_c0_2 pvm_c0_3 = true := by decide +kernel
private theorem pchk_c0_s3 : bSlideChk 6 513
    phbv_g0 pvm_c0_3 pvm_c0_4 = true := by decide +kernel
private theorem pchk_c0_s4 : bSlideChk 5 513
    phbv_g0 pvm_c0_4 pvm_c0_5 = true := by decide +kernel
private theorem pchk_c0_s5 : bSlideChk 5 513
    phbv_g0 pvm_c0_5 pvm_c0_6 = true := by decide +kernel
private theorem pchk_c0_s6 : bSlideChk 5 513
    phbv_g0 pvm_c0_6 pvm_c0_7 = true := by decide +kernel
private theorem pchk_c0_s7 : bSlideChk 5 513
    phbv_g0 pvm_c0_7 pvm_c0_8 = true := by decide +kernel
private theorem pchk_c0_s8 : bSlideChk 5 513
    phbv_g0 pvm_c0_8 pvm_c0_9 = true := by decide +kernel
private theorem pchk_c0_s9 : bSlideChk 5 513
    phbv_g0 pvm_c0_9 pvm_c0_10 = true := by decide +kernel
private theorem pchk_c0_s10 : bSlideChk 5 513
    phbv_g0 pvm_c0_10 pvm_c0_11 = true := by decide +kernel
private theorem pchk_c0_s11 : bSlideChk 5 513
    phbv_g0 pvm_c0_11 pvm_c0_12 = true := by decide +kernel
private theorem pchk_c0_s12 : bSlideChk 5 513
    phbv_g0 pvm_c0_12 pvm_c0_13 = true := by decide +kernel
private theorem pchk_c0_s13 : bSlideChk 5 513
    phbv_g0 pvm_c0_13 pvm_c0_14 = true := by decide +kernel
private theorem pchk_c0_s14 : bSlideChk 5 513
    phbv_g0 pvm_c0_14 pvm_c0_15 = true := by decide +kernel
private theorem pchk_c0_s15 : bSlideChk 5 513
    phbv_g0 pvm_c0_15 rkmVoHi_m1024_r512_s0_c1 = true := by decide +kernel
private theorem pacc_c0_s1 : muxFastIterFullT16 12 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_2 :=
  (muxFastIterFullT16_add 6 6 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_g0)
      (bSlideChk_sound (rkmHd (rkmTl pchk_c0_s0)))).trans (bSlideChk_sound pchk_c0_s1))
private theorem pacc_c0_s2 : muxFastIterFullT16 18 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_3 :=
  (muxFastIterFullT16_add 12 6 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_g0)
      pacc_c0_s1).trans (bSlideChk_sound pchk_c0_s2))
private theorem pacc_c0_s3 : muxFastIterFullT16 24 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_4 :=
  (muxFastIterFullT16_add 18 6 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 6 513 phbv_g0)
      pacc_c0_s2).trans (bSlideChk_sound pchk_c0_s3))
private theorem pacc_c0_s4 : muxFastIterFullT16 29 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_5 :=
  (muxFastIterFullT16_add 24 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s3).trans (bSlideChk_sound pchk_c0_s4))
private theorem pacc_c0_s5 : muxFastIterFullT16 34 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_6 :=
  (muxFastIterFullT16_add 29 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s4).trans (bSlideChk_sound pchk_c0_s5))
private theorem pacc_c0_s6 : muxFastIterFullT16 39 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_7 :=
  (muxFastIterFullT16_add 34 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s5).trans (bSlideChk_sound pchk_c0_s6))
private theorem pacc_c0_s7 : muxFastIterFullT16 44 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_8 :=
  (muxFastIterFullT16_add 39 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s6).trans (bSlideChk_sound pchk_c0_s7))
private theorem pacc_c0_s8 : muxFastIterFullT16 49 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_9 :=
  (muxFastIterFullT16_add 44 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s7).trans (bSlideChk_sound pchk_c0_s8))
private theorem pacc_c0_s9 : muxFastIterFullT16 54 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_10 :=
  (muxFastIterFullT16_add 49 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s8).trans (bSlideChk_sound pchk_c0_s9))
private theorem pacc_c0_s10 : muxFastIterFullT16 59 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_11 :=
  (muxFastIterFullT16_add 54 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s9).trans (bSlideChk_sound pchk_c0_s10))
private theorem pacc_c0_s11 : muxFastIterFullT16 64 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_12 :=
  (muxFastIterFullT16_add 59 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s10).trans (bSlideChk_sound pchk_c0_s11))
private theorem pacc_c0_s12 : muxFastIterFullT16 69 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_13 :=
  (muxFastIterFullT16_add 64 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s11).trans (bSlideChk_sound pchk_c0_s12))
private theorem pacc_c0_s13 : muxFastIterFullT16 74 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_14 :=
  (muxFastIterFullT16_add 69 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s12).trans (bSlideChk_sound pchk_c0_s13))
private theorem pacc_c0_s14 : muxFastIterFullT16 79 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = pvm_c0_15 :=
  (muxFastIterFullT16_add 74 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s13).trans (bSlideChk_sound pchk_c0_s14))
private theorem pacc_c0_s15 : muxFastIterFullT16 84 513
    phbv_g0 rkmViHi_m1024_r512_s0_c1 = rkmVoHi_m1024_r512_s0_c1 :=
  (muxFastIterFullT16_add 79 5 513 phbv_g0 rkmViHi_m1024_r512_s0_c1).trans
    ((congrArg (muxFastIterFullT16 5 513 phbv_g0)
      pacc_c0_s14).trans (bSlideChk_sound pchk_c0_s15))
/-- Certified `T_16` walk chunk `m1024_r512_s0_c1`. -/
theorem rkmWalkChkHi_m1024_r512_s0_c1 : muxFastIterFullT16 84 513
    rkmHbHi_m1024_r512_s0_c1 rkmViHi_m1024_r512_s0_c1 = rkmVoHi_m1024_r512_s0_c1 :=
  (congrArg (fun h ↦ muxFastIterFullT16 84 513 h rkmViHi_m1024_r512_s0_c1)
    (muxIntListEq_eq_true.mp (rkmHd pchk_c0_s0))).trans pacc_c0_s15
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi1024T4`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi1024T4 :
    rkmWalkChkHi_m1024_r512_s0_c1 = rkmWalkChkHi_m1024_r512_s0_c1 :=
  rfl
private theorem laneRoot_Hi1024T4 : rkmHbHi_m1024_r512_s0_c1 = rkmHbHi_m1024_r512_s0_c1 :=
  (And.intro (Eq.refl rkmHbHi_m1024_r512_s0_c0) rfl).right
end
end QuantumComputation.Specs.DickeSol
