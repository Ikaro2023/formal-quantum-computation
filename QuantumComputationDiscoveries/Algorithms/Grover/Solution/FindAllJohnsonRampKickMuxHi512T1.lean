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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T8

/-
# High-`m` Checkpointed Walk Part `1` (`FindAllJohnsonRampKickMuxHi512T1`)

Certifies `2` `T_16` checkpoint walk(s) (`66563` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Gap-encoded sign-flip helper (`FindAllJohnsonRampKickMuxHi512T1`). -/
def rkmFlipGapsHi512T1 : List ℕ → List ℤ → List ℤ
  | [], vs => vs
  | _, [] => []
  | 0 :: gs, v :: vs => muxRawIntNeg v :: rkmFlipGapsHi512T1 gs vs
  | (g + 1) :: gs, v :: vs => v :: rkmFlipGapsHi512T1 (g :: gs) vs
/-- Quantized generator list for `m512_r256_s0_c0`. -/
def rkmHbHi_m512_r256_s0_c0 : List ℤ := altBuildHbFrom 512 256 146267356589 0 256
/-- Input orbital vector for `m512_r256_s0_c0`. -/
def rkmViHi_m512_r256_s0_c0 : List ℤ := [rkmP 1000000000000000]
/-- Output orbital vector for `m512_r256_s0_c0`. -/
def rkmVoHi_m512_r256_s0_c0 : List ℤ := let p := rkmP; let n := rkmN; [
  p 1,n 1,n 8,p 4,n 0,p 0,n 2,n 4,n 8,n 2,p 5,p 3,p 4,n 4,n 6,n 1,p 10,p 7,n 2,p 0,p 1,n 0,n 1,n 7,
  n 9,p 1,p 12,p 7,n 2,p 4,p 7,p 4,p 7,p 7,p 2,p 1,p 3,p 7,p 20,p 10,p 2,p 8,p 7,p 4,p 8,p 14,p 16,
  p 13,p 12,p 10,p 14,p 26,p 20,p 16,p 19,p 21,p 24,p 29,p 29,p 34,p 54,p 64,p 124,p 262,p 533,
  p 1149,p 2469,p 5243,p 11085,p 23153,p 47727,p 97221,p 195593,p 388592,p 762475,p 1477673,
  p 2828620,p 5348707,p 9991490,p 18439569,p 33623262,p 60579589,p 107854538,p 189759379,
  p 329949294,p 567016553,p 963104712,p 1616978924,p 2683560166,p 4402675920,p 7140720489,
  p 11450068402,p 18152437300,p 28453914200,p 44100956770,p 67588215243,p 102430271220,
  p 153510051152,p 227516350682,p 333481126907,p 483423449099,p 693100708076,p 982858397118,
  p 1378557180896,p 1912540023366,p 2624583216147,p 3562754117260,p 4784076776504,p 6354886539708,
  p 8350738957508,p 10855730114670,p 13961088290847,p 17762913940021,p 22358978952434,
  p 27844548463539,p 34307258786245,p 41821170868379,p 50440215065035,p 60191342555845,
  p 71067791899556,p 83022955051787,p 95965374360951,p 109755410244900,p 124204080499808,
  p 139074482394488,p 154086068728296,p 168921865406001,p 183238503030608,p 196678705756909,
  p 208885657963055,p 219518475457803,p 228267864240816,p 234870973997743,p 239124457355785,
  p 240894833583992,p 240125422438245,p 236839347293795,p 231138386355329,p 223197751186315,
  p 213257165282591,p 201608874898972,p 188583426557774,p 174534173664361,p 159821519487376,
  p 144797865214559,p 129794118003084,p 115108440039695,p 100997705642542,p 87671901768931,
  p 75291480083125,p 63967465523741,p 53763962195510,p 44702581956409,p 36768257947386,
  p 29915892670514,p 24077321655250,p 19168139635847,p 15094025154801,p 11756300010899,
  p 9056561374170,p 6900317979635,p 5199641301630,p 3874904303461,p 2855722981772,p 2081240245520,
  p 1499899950740,p 1068854348581,p 753134373738,p 524692618437,p 361406620006,p 246107754865,
  p 165680410939,p 110258363004,p 72530967601,p 47161018020,p 30308609003,p 19250697133,
  p 12083649639,p 7495379829,p 4594145161,p 2782287593,p 1664773771,p 984085711,p 574648943,
  p 331459628,p 188834851,p 106248066,p 59035049,p 32389939,p 17546126,p 9383863,p 4954135,
  p 2581631,p 1327733,p 673854,p 337444,p 166704,p 81227,p 39023,p 18475,p 8613,p 3950,p 1775,
  p 780,p 332,p 134,p 49,p 16,p 4,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0]
/-- Quantized generator list for `m512_r256_s1_c0`. -/
def rkmHbHi_m512_r256_s1_c0 : List ℤ := altBuildHbFrom 512 256 146751538461 0 256
/-- Input orbital vector for `m512_r256_s1_c0`. -/
def rkmViHi_m512_r256_s1_c0 : List ℤ := rkmFlipGapsHi512T1
  [75, 0, 0, 0, 0, 2, 97, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]
  rkmVoHi_m512_r256_s0_c0
/-- Output orbital vector for `m512_r256_s1_c0`. -/
def rkmVoHi_m512_r256_s1_c0 : List ℤ := let p := rkmP; let n := rkmN; [
  n 28692,p 171263,n 711598,p 2365157,n 6690665,p 16495744,n 36440160,p 71969338,n 130435381,
  p 211834261,n 320547613,p 426311658,n 535106407,p 555203895,n 547939786,p 355002880,n 183865856,
  n 149519262,p 316131333,n 456950491,p 385558299,n 142551397,n 90074459,p 362436661,n 399725045,
  p 249294292,n 21922115,n 286033398,p 385479112,n 266349795,p 50348292,p 254741825,n 382083122,
  p 244361205,n 16725916,n 255396188,p 380675767,n 204004996,n 65729794,p 278001923,n 352053877,
  p 146996704,p 169818430,n 317929387,p 275732695,n 53703377,n 253563142,p 349263093,n 166634268,
  n 91648616,p 297269891,n 312254742,p 51029877,p 245772830,n 315818241,p 176427883,p 85119732,
  n 322177649,p 290029276,n 2883555,n 248359554,p 302235160,n 153579274,n 142722459,p 344217478,
  n 230455270,n 63845924,p 272611091,n 286525807,p 81735993,p 226956913,n 341358463,p 141850483,
  p 149133825,n 300824497,p 236317663,p 31772617,n 304804884,p 297809882,n 21107451,n 241131653,
  p 299299602,n 133990583,n 164360821,p 343966398,n 198583504,n 124459413,p 308589489,n 236170199,
  n 15798420,p 278463051,n 312171074,p 42187928,p 264160041,n 309851147,p 97986448,p 180217344,
  n 325292110,p 190407908,p 143873795,n 345653504,p 212714005,p 93803832,n 299511050,p 262151495,
  p 5958737,n 297912455,p 314529039,n 21205844,n 275058699,p 305885613,n 82360895,n 212668289,
  p 341055082,n 150011945,n 203626059,p 354466270,n 162888063,n 156963165,p 327877257,n 220764992,
  n 98572458,p 350777024,n 260883477,n 89720856,p 336020248,n 262121725,n 34473740,p 305445615,
  n 311873671,p 8342201,p 321219022,n 326427151,p 14087409,p 290175246,n 323168954,p 68642642,
  p 267374634,n 364682646,p 90843200,p 279696701,n 359520008,p 95142644,p 242614710,n 360461521,
  p 143060361,p 236145763,n 393678707,p 143886274,p 245288666,n 376252480,p 151114236,p 211878698,
  n 388916383,p 185852038,p 226276454,n 410775628,p 168228967,p 229697211,n 390629763,p 181880368,
  p 211722222,n 417427478,p 193533814,p 244944097,n 421896993,p 165476022,p 241322240,n 411626619,
  p 181530135,p 252615556,n 443333210,p 159308733,p 292070444,n 427374617,p 133686980,p 289899250,
  n 437298889,p 132120166,p 336203985,n 448434688,p 77186273,p 361710577,n 423419142,p 59009478,
  p 384427076,n 440469538,p 8770831,p 440418554,n 405663574,n 51837182,p 449702157,n 391251786,
  n 93401991,p 505061211,n 359826407,n 186626665,p 517827187,n 299271472,n 235884322,p 544598305,
  n 259004780,n 339223243,p 556414134,n 155741241,n 402433700,p 539961938,n 89898454,n 497506279,
  p 529208505,p 49723710,n 559015947,p 459665540,p 143388918,n 629709921,p 401641981,p 310834609,
  n 654241090,p 274065577,p 414159393,n 684198305,p 147325485,p 585458659,n 624728406,n 20492413,
  p 674347797,n 587081288,n 233130742,p 745645712,n 453639000,n 286207268,p 991405895,n 584493799,
  n 1382943012,p 1442860443,p 3363737525,n 244140457,n 12126678652,n 15028086411,p 32445397642,
  p 96667062673,n 12322646418,n 384948359025,n 476016614530,p 769226168610,p 3022297849254,
  p 2160664150690,n 7620772888183,n 23251610764620,n 20559983705953,p 41263318654433,
  p 187063604085940,p 384519667175545,p 540030812994236,p 556799445017153,p 415787560367376,
  p 199686677302352]
end
public section
private abbrev bZ : ℕ := 2000000000000000
private theorem hbZ0 : Nat.ble bZ 0 = false := rfl
private abbrev fN {α : Type} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β : Type} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by
  rw [Nat.add_eq]
  exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private theorem hzMul0 (z : ℕ) : Nat.mul 0 z = 0 := by
  rw [Nat.mul_eq]
  omega
private def uC (x : ℕ) (xs : List ℕ) : List ℕ :=
  match Nat.add 1 x, xs with
  | 0, _ => xs
  | v + 1, [] => [v]
  | v + 1, h :: t => v :: h :: t
private theorem uC_eq (x : ℕ) (l : List ℕ) : uC x l = x :: l := by
  unfold uC
  rw [n1a]
  cases l <;> rfl
private def uOh : List ℕ → List ℤ
  | [] => []
  | n :: ns => Int.ofNat n :: uOh ns
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
  | Int.ofNat v => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t
private theorem bCZ_eq (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by
  cases x <;> cases xs <;> rfl
private theorem bOfF (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  unfold primOfNatForced
  rw [n1a]
private theorem bNsF (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  unfold primNegSuccForced
  rw [n1a]
private theorem bSubF (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat
  rw [bOfF, Nat.sub_eq]
  cases h : z - u with
  | zero =>
    dsimp only
    rw [Nat.sub_eq, Int.ofNat_eq_natCast]
    omega
  | succ k =>
    dsimp only
    rw [Int.negSucc_eq]
    omega
private def bDc (z : ℕ) : List ℕ → List ℤ
  | [] => []
  | u :: us => bCZ (rkmForcedSubNatNat u z) (bDc z us)
private theorem bDc0 (z : ℕ) : bDc z [] = [] := rfl
private theorem bDcS (z u : ℕ) (us : List ℕ) :
    bDc z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDc z us := by
  rw [bDc, bCZ_eq, bSubF]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]
  omega
private theorem bM0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZ0]
  rfl
private def bNL : List ℕ → ℕ
  | [] => 0
  | _ :: us => Nat.add (bNL us) 1
private theorem bNL_eq (z : ℕ) : ∀ (us : List ℕ), bNL us = altIntLen (bDc z us)
  | [] => rfl
  | _ :: us => by
    dsimp only [bNL]
    rw [bDcS]
    dsimp only [altIntLen]
    rw [bNL_eq z us]
private def zTd (x : ℤ) (d : ℕ) : ℤ := match x with
  | Int.ofNat m => Int.ofNat (m / d)
  | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNeg : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.ofNat_eq_natCast]
    omega
  | k + 1 => by
    dsimp only [muxRawNegOfNat]
    rw [Int.negSucc_eq]
    omega
private theorem bTdN : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTd x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc _, _ => by
    dsimp only [muxRawIntTdivNat, zTd]
    rw [bNeg, ndiv, Nat.add_eq]
private theorem bSTdN (m n d : ℕ) : rkmUltraSubNatTdiv m n d = zTd ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv
  simp only [Nat.sub_eq, ndiv, Nat.add_eq]
  cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by
      rw [Int.ofNat_eq_natCast]
      omega
    rw [hm]
    rfl
  | succ k =>
    dsimp only
    have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by
      rw [Int.negSucc_eq]
      omega
    rw [hm]
    dsimp only [zTd]
    rw [bNeg]
private theorem bSTd (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTd (a - b) d := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => exact bSTdN m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]
        omega
      dsimp only [rkmUltraSubTdiv]
      rw [hm]
      dsimp only [zTd]
      rw [ndiv, Nat.add_eq, Nat.add_eq]
  | negSucc m =>
    cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
        omega
      dsimp only [rkmUltraSubTdiv]
      rw [hm]
      dsimp only [zTd]
      rw [bNeg, ndiv, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]
      rw [bSTdN, Nat.add_eq, Nat.add_eq]
      refine congrArg (fun t => zTd t d) ?_
      simp only [Int.negSucc_eq]
      omega
private theorem bMul (a b : ℤ) : muxRawIntMul a b = a * b := by
  cases a with
  | ofNat _ =>
    cases b with
    | ofNat _ =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
      push_cast
      ring
    | negSucc _ =>
      dsimp only [muxRawIntMul]
      simp only [bNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
  | negSucc _ =>
    cases b with
    | ofNat _ =>
      dsimp only [muxRawIntMul]
      simp only [bNeg, Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
    | negSucc _ =>
      dsimp only [muxRawIntMul]
      simp only [Nat.mul_eq, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      push_cast
      ring
private theorem bFAdd (a b : ℤ) : rkmForcedIntAdd a b = a + b := by
  cases a with
  | ofNat _ =>
    cases b with
    | ofNat _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bOfF, Nat.add_eq, Int.ofNat_eq_natCast]
      omega
    | negSucc _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bSubF, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
  | negSucc _ =>
    cases b with
    | ofNat _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bSubF, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
    | negSucc _ =>
      dsimp only [rkmForcedIntAdd]
      simp only [bNsF, Nat.add_eq, Int.negSucc_eq]
      omega
private theorem bAC (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons
  rw [bFAdd]
  cases a + b <;> cases xs <;> rfl
private def bSV (v P Q d : ℕ) : ℕ := match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d)
  | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bSV_eq (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  unfold bSV at hv ⊢
  simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢
  revert hv
  cases h : Q - P with
  | zero =>
    intro _
    have hm : (P : ℤ) - (Q : ℤ) = Int.ofNat (P - Q) := by
      rw [Int.ofNat_eq_natCast]
      omega
    rw [hm]
    dsimp only [zTd]
    rw [Int.ofNat_eq_natCast]
    push_cast
    ring
  | succ k =>
    intro hv
    have hm : (P : ℤ) - (Q : ℤ) = Int.negSucc k := by
      rw [Int.negSucc_eq]
      omega
    rw [hm]
    dsimp only [zTd] at hv ⊢
    omega
private theorem bSV_same (z P d : ℕ) : bSV z P P d = z := by
  unfold bSV
  simp only [Nat.sub_eq, Nat.add_eq, ndiv, Nat.sub_self, Nat.zero_div, Nat.add_zero]
private theorem bSV_comm (z A B d : ℕ) : bSV z (Nat.add A B) (Nat.add B A) d = z := by
  have hc : Nat.add B A = Nat.add A B := by
    simp only [Nat.add_eq]
    omega
  rw [hc]
  exact bSV_same z (Nat.add A B) d
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bSV v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bChb (z d b0 c0 b v c1 : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bDc z rest = tailZ) :
    bDc z (uC (bCV z d b0 c0 b v c1) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ)) (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0)
        ((c0 : ℤ) - (z : ℤ))) (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uC_eq, bDcS, ht, bAC, bSTd, bMul, bMul]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
  unfold bCV at hv ⊢
  rw [bSV_eq z v _ _ d hv, hpq]
private theorem bC0 (z d b0 c0 v : ℕ) {rest : List ℕ} {tailZ : List ℤ}
    (hv : 0 < bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDc z rest = tailZ) :
    bDc z (uC (bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) rest) =
      rkmUltraAddCons ((v : ℤ) - (z : ℤ))
        (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tailZ := by
  rw [uC_eq, bDcS, ht, bAC, bTdN, bMul]
  refine congrArg (· :: tailZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [bSV_eq z v _ _ d hv, hpq]
private def bAP : List ℕ → Bool
  | [] => true
  | x :: xs => cond (Nat.ble x 0) false (bAP xs)
private theorem apC {x : ℕ} {xs : List ℕ} (h : bAP (uC x xs) = true) :
    0 < x ∧ bAP xs = true := by
  rw [uC_eq] at h
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
    ((bHO z cs : ℤ) - (z : ℤ)) = (match bDc z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by
    unfold bHO
    rw [bDc0, bZ0]
  | _ :: _ => by
    unfold bHO
    rw [bDcS]
private theorem tnEq (z : ℕ) : ∀ (xs : List ℕ),
    bDc z (bTN xs) = (match bDc z xs with | _ :: t => t | [] => [])
  | [] => rfl
  | _ :: _ => by
    unfold bTN
    rw [bDcS]
private def rPad (z : ℕ) : ℕ → List ℕ → List ℕ
  | 0, xs => xs
  | k + 1, [] => uC z (rPad z k [])
  | k + 1, x :: xs => uC x (rPad z k xs)
private theorem rPad_uC (z r x : ℕ) (xs : List ℕ) :
    rPad z (r + 1) (uC x xs) = uC x (rPad z r xs) := by
  rw [uC_eq]
  rfl
private theorem rPad_hd (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ), bHO z (rPad z k xs) = bHO z xs
  | 0, _ => rfl
  | _ + 1, [] => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
  | _ + 1, _ :: _ => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
private theorem rPad_tl (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ),
    bTN (rPad z k xs) = rPad z (k - 1) (bTN xs)
  | 0, _ => rfl
  | _ + 1, [] => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
  | _ + 1, _ :: _ => by
    dsimp only [rPad]
    rw [uC_eq]
    rfl
private theorem rPad_bNL (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ),
    Nat.ble (bNL xs) k = true → bNL (rPad z k xs) = k
  | 0, [], _ => rfl
  | 0, _ :: xs, h => by
    dsimp only [bNL] at h
    rw [Nat.add_eq] at h
    have h1 : bNL xs + 1 ≤ 0 := Nat.le_of_ble_eq_true h
    omega
  | k + 1, [], _ => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bNL]
    rw [rPad_bNL z k [] rfl, Nat.add_eq]
  | k + 1, _ :: xs, h => by
    have hk : Nat.ble (bNL xs) k = true := by
      have h1 := Nat.le_of_ble_eq_true h
      dsimp only [bNL] at h1
      rw [Nat.add_eq] at h1
      exact Nat.ble_eq_true_of_le (by omega)
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bNL]
    rw [rPad_bNL z k xs hk, Nat.add_eq]
private theorem bAP_rPad {z : ℕ} (hz : Nat.ble z 0 = false) :
    ∀ (k : ℕ) (xs : List ℕ), bAP xs = true → bAP (rPad z k xs) = true
  | 0, _, h => h
  | k + 1, [], _ => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bAP]
    rw [hz]
    dsimp only [cond]
    exact bAP_rPad hz k [] rfl
  | k + 1, x :: xs, h => by
    dsimp only [bAP] at h
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bAP]
    revert h
    cases Nat.ble x 0 with
    | true =>
      intro h
      dsimp only [cond] at h
      cases h
    | false =>
      intro h
      dsimp only [cond] at h ⊢
      exact bAP_rPad hz k xs h
private def bEqN (a b : ℕ) : Bool :=
  cond (Nat.ble a b) (Nat.ble b a) false
private theorem bEqN_self (a : ℕ) : bEqN a a = true := by
  have hle : Nat.ble a a = true := Nat.ble_eq_true_of_le (by omega)
  unfold bEqN
  rw [hle]
  rfl
private theorem bEqN_eq (a b : ℕ) (h : bEqN a b = true) : a = b := by
  unfold bEqN at h
  revert h
  cases hab : Nat.ble a b with
  | false =>
    intro h
    dsimp only [cond] at h
    cases h
  | true =>
    cases hba : Nat.ble b a with
    | false =>
      intro h
      dsimp only [cond] at h
      cases h
    | true =>
      intro _
      have h1 := Nat.le_of_ble_eq_true hab
      have h2 := Nat.le_of_ble_eq_true hba
      omega
private def bCT (z x : ℕ) (xs : List ℕ) : List ℕ :=
  match xs with
  | h :: t => x :: h :: t
  | [] => cond (bEqN x z) [] [x]
private def bTrim (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => bCT z x (bTrim z xs)
private theorem bTrim_rPad (z : ℕ) : ∀ (k : ℕ) (xs : List ℕ), bTrim z (rPad z k xs) = bTrim z xs
  | 0, _ => rfl
  | k + 1, [] => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bTrim]
    rw [bTrim_rPad z k []]
    dsimp only [bTrim, bCT]
    rw [bEqN_self z]
    rfl
  | k + 1, x :: xs => by
    dsimp only [rPad]
    rw [uC_eq]
    dsimp only [bTrim]
    rw [bTrim_rPad z k xs]
private theorem rPad_bTrim_len (z : ℕ) : ∀ (xs : List ℕ), rPad z (bNL xs) (bTrim z xs) = xs
  | [] => rfl
  | x :: t => by
    have hal : bNL (x :: t) = bNL t + 1 := rfl
    rw [hal]
    dsimp only [bTrim]
    have ih := rPad_bTrim_len z t
    revert ih
    cases bTrim z t with
    | cons _ _ =>
      intro ih
      dsimp only [bCT, rPad]
      rw [uC_eq, ih]
    | nil =>
      intro ih
      dsimp only [bCT]
      cases he : bEqN x z with
      | true =>
        dsimp only [cond, rPad]
        rw [uC_eq, bEqN_eq x z he, ih]
      | false =>
        dsimp only [cond, rPad]
        rw [uC_eq, ih]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, [], vs, cs =>
    uC (bSV (bHO z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d) (bSl z d rem 0 z [] (bTN vs) (bTN cs))
  | rem + 1, b0, c0, b :: bR, vs, cs =>
    uC (bCV z d b0 c0 b (bHO z vs) (bHO z (bTN cs)))
      (bSl z d rem b (bHO z cs) bR (bTN vs) (bTN cs))
private theorem bSl_len (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bNL (bSl z d rem b0 c0 bns vs cs) = rem
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, [], vs, cs => by
    dsimp only [bSl]
    rw [uC_eq]
    dsimp only [bNL]
    rw [bSl_len z d rem 0 z [] (bTN vs) (bTN cs), Nat.add_eq]
  | rem + 1, b0, c0, b :: bR, vs, cs => by
    dsimp only [bSl]
    rw [uC_eq]
    dsimp only [bNL]
    rw [bSl_len z d rem b (bHO z cs) bR (bTN vs) (bTN cs), Nat.add_eq]
private theorem bSl_rPad (z d : ℕ) : ∀ (rem b0 c0 kv kc : ℕ) (bns vs cs : List ℕ),
    bSl z d rem b0 c0 bns (rPad z kv vs) (rPad z kc cs) = bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, kv, kc, [], vs, cs => by
    dsimp only [bSl]
    rw [rPad_hd z kv vs, rPad_tl z kv vs, rPad_tl z kc cs]
    rw [bSl_rPad z d rem 0 z (kv - 1) (kc - 1) [] (bTN vs) (bTN cs)]
  | rem + 1, b0, c0, kv, kc, b :: bR, vs, cs => by
    dsimp only [bSl]
    rw [rPad_hd z kv vs, rPad_tl z kc cs, rPad_hd z (kc - 1) (bTN cs), rPad_hd z kc cs,
      rPad_tl z kv vs]
    rw [bSl_rPad z d rem b (bHO z cs) (kv - 1) (kc - 1) bR (bTN vs) (bTN cs)]
private theorem bSl_zero (z d : ℕ) : ∀ (rem b0 : ℕ) (bns : List ℕ),
    bSl z d rem b0 z bns [] [] = rPad z rem []
  | 0, _, _ => rfl
  | rem + 1, b0, [] => by
    dsimp only [bSl, bHO, bTN, rPad]
    rw [bSV_same z (Nat.mul b0 z) d, bSl_zero z d rem 0 []]
  | rem + 1, b0, b :: bR => by
    dsimp only [bSl, bCV, bHO, bTN, rPad]
    rw [bSV_comm z (Nat.mul b0 z) (Nat.mul b z) d, bSl_zero z d rem b bR]
private theorem bSl_sound (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAP (bSl z d rem b0 c0 bns vs cs) = true → bDc z (bSl z d rem b0 c0 bns vs cs) =
      rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uOh bns) (bDc z vs) (bDc z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, [], vs, cs, h => by
    dsimp only [bSl, uOh, rkmUltraSlideLoopAux] at h ⊢
    have hp := apC h
    have hi := bSl_sound z d rem 0 z [] (bTN vs) (bTN cs) hp.2
    rw [bM0, uOh, tnEq z vs, tnEq z cs] at hi
    have hc := bC0 z d b0 c0 (bHO z vs) hp.1 hi
    rw [hoEq z vs] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, [], [], h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDc0]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b z bR [] [] hp.2
    rw [bZ0 z, bDc0] at hi
    have hc := bChb z d b0 c0 b z z hp.1 hi
    rw [bZ0 z] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, [], c :: cT, h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDc0, bDcS z c cT]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b c bR [] cT hp.2
    rw [bDc0] at hi
    have hc := bChb z d b0 c0 b z (bHO z cT) hp.1 hi
    rw [hoEq z cT, bZ0 z] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, v :: vT, [], h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDcS z v vT, bDc0]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b z bR vT [] hp.2
    rw [bZ0 z, bDc0] at hi
    have hc := bChb z d b0 c0 b v z hp.1 hi
    rw [bZ0 z] at hc
    exact hc
  | rem + 1, b0, c0, b :: bR, v :: vT, c :: cT, h => by
    dsimp only [bSl, bHO, bTN, uOh] at h ⊢
    rw [bDcS z v vT, bDcS z c cT]
    dsimp only [rkmUltraSlideLoopAux]
    have hp := apC h
    have hi := bSl_sound z d rem b c bR vT cT hp.2
    have hc := bChb z d b0 c0 b v (bHO z cT) hp.1 hi
    rw [hoEq z cT] at hc
    exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => uC b (uC (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs => match hbz with
    | [] => match vs, cs with
      | [], [] => uC (bSV z p0 q0 d) []
      | _, _ => uC (bSV (bHO z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTN vs) (bTN cs))
    | [_] => []
    | b :: bz :: bR => match vs, cs with
      | [], [] => uC (bSV z (Nat.add p0 bz) (Nat.add bz q0) d) []
      | v :: vT, c :: cT => uC (bSV v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] => uC (bSV v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT => uC (bSV z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
          (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
private theorem bSlZ_rPad (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    rPad z rem (bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs) =
      bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, _, _, bns, vs, cs => by
    cases bns with
    | nil =>
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, bSl_zero z d rem 0 []]
        | cons _ cT =>
          have hrec := bSlZ_rPad z d rem 0 z [] [] cT
          dsimp only [mkHbZ] at hrec
          rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, hrec]
      | cons _ vT =>
        cases cs with
        | nil =>
          have hrec := bSlZ_rPad z d rem 0 z [] vT []
          dsimp only [mkHbZ] at hrec
          rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, hrec]
        | cons _ cT =>
          have hrec := bSlZ_rPad z d rem 0 z [] vT cT
          dsimp only [mkHbZ] at hrec
          rw [hzMul0 z] at hrec
          dsimp only [mkHbZ, bSlZ, bSl, bHO, bTN]
          rw [rPad_uC, hrec]
    | cons b bR =>
      dsimp only [mkHbZ]
      rw [uC_eq, uC_eq]
      cases vs with
      | nil =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSl_zero z d rem b bR]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSlZ_rPad z d rem b c bR [] cT]
      | cons v vT =>
        cases cs with
        | nil =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSlZ_rPad z d rem b z bR vT []]
        | cons c cT =>
          dsimp only [bSlZ, bSl, bCV, bHO, bTN]
          rw [rPad_uC, bSlZ_rPad z d rem b c bR vT cT]
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
    uCN4 x1 x2 x3 x4 xs = uC x1 (uC x2 (uC x3 (uC x4 xs))) := by
  unfold uCN4
  rw [n1a x1, n1a x2, n1a x3, n1a x4, uC_eq, uC_eq, uC_eq, uC_eq]
  cases xs <;> rfl
private def bAP4 : List ℕ → Bool
  | a :: b :: c :: d :: xs => cond (Nat.ble a 0) false (cond (Nat.ble b 0) false
      (cond (Nat.ble c 0) false (cond (Nat.ble d 0) false (bAP4 xs))))
  | xs => bAP xs
private theorem bAP4e : ∀ (xs : List ℕ), bAP4 xs = bAP xs
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: _ :: _ :: xs => by
    dsimp only [bAP4, bAP]
    rw [bAP4e xs]
private def bChkP (out : List ℕ) : Option (List ℕ) := match out with
  | [] => some []
  | x :: xs => cond (bAP4 (x :: xs)) (some (x :: xs)) none
private theorem bChkPe (out : List ℕ) : bChkP out = cond (bAP out) (some out) none := by
  cases out with
  | nil => rfl
  | cons _ _ =>
    dsimp only [bChkP]
    rw [bAP4e]
private theorem cond_some_eq {α : Type} {b : Bool} {x y : α}
    (h : cond b (some x) none = some y) : b = true ∧ x = y := by
  cases b with
  | false => cases h
  | true =>
    dsimp only [cond] at h
    injection h with h'
    exact ⟨rfl, h'⟩
private inductive HbZ4 : Type
  | tail : List ℕ → HbZ4
  | c4 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → HbZ4 → HbZ4
private abbrev hbz4C (b1 z1 b2 z2 b3 z3 b4 z4 : ℕ) (t : List ℕ) : List ℕ :=
  b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: t
private def hbz4L : HbZ4 → List ℕ
  | HbZ4.tail l => l
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 r => hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L r)
private def fH4 {α : Type} (h : HbZ4) (k : HbZ4 → α) : α := match h with
  | HbZ4.tail l => fL l fun lF => k (HbZ4.tail lF)
  | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r => k (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 r)
private theorem fH4e {α : Type} (h : HbZ4) (k : HbZ4 → α) : fH4 h k = k h := by
  cases h with
  | tail _ =>
    dsimp only [fH4, fL]
    rw [rkmb_forceList_eq]
  | c4 _ _ _ _ _ _ _ _ _ => rfl
private def toH4 : List ℕ → HbZ4
  | b1 :: z1 :: b2 :: z2 :: b3 :: z3 :: b4 :: z4 :: bs => match toH4 bs with
    | HbZ4.tail l => HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.tail l)
    | HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t =>
      HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 (HbZ4.c4 a1 a2 a3 a4 a5 a6 a7 a8 t)
  | bs => HbZ4.tail bs
private theorem hbz4L_toH4 : ∀ (xs : List ℕ), hbz4L (toH4 xs) = xs
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | [_, _, _, _] => rfl
  | [_, _, _, _, _] => rfl
  | [_, _, _, _, _, _] => rfl
  | [_, _, _, _, _, _, _] => rfl
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: bs => by
    have ih := hbz4L_toH4 bs
    dsimp only [toH4]
    revert ih
    cases toH4 bs with
    | tail _ =>
      intro ih
      dsimp only [hbz4L, hbz4C] at ih ⊢
      rw [ih]
    | c4 _ _ _ _ _ _ _ _ _ =>
      intro ih
      dsimp only [hbz4L, hbz4C] at ih ⊢
      rw [ih]
private def bSlZ4 (z d : ℕ) : HbZ4 → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ
  | HbZ4.tail l, rem, p0, q0, vs, cs => bSlZ z d rem p0 q0 l vs cs
  | HbZ4.c4 b1 z1 b2 z2 b3 z3 b4 z4 bR, rem, p0, q0, vs, cs => match rem with
    | 0 => []
    | r3 + 1 => match r3 with
      | 0 => bSlZ z d 1 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
      | r2 + 1 => match r2 with
        | 0 => bSlZ z d 2 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
        | r1 + 1 => match r1 with
          | 0 => bSlZ z d 3 p0 q0 (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
          | r0 + 1 => match vs, cs with
            | [], [] => uC (bSV z (Nat.add p0 z1) (Nat.add z1 q0) d) []
            | v1 :: v2 :: v3 :: v4 :: vR, c1 :: c2 :: c3 :: c4 :: c5 :: cR =>
              uCN4 (bSV v1 (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                (bSV v2 (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                (bSV v3 (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                (bSV v4 (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 c5) z3) d)
                (bSlZ4 z d bR r0 (Nat.mul b4 c4) z4 vR (c5 :: cR))
            | [], c1 :: c2 :: c3 :: c4 :: c5 :: cR =>
              uCN4 (bSV z (Nat.add p0 z1) (Nat.add (Nat.mul b1 c2) q0) d)
                (bSV z (Nat.add (Nat.mul b1 c1) z2) (Nat.add (Nat.mul b2 c3) z1) d)
                (bSV z (Nat.add (Nat.mul b2 c2) z3) (Nat.add (Nat.mul b3 c4) z2) d)
                (bSV z (Nat.add (Nat.mul b3 c3) z4) (Nat.add (Nat.mul b4 c5) z3) d)
                (bSlZ4 z d bR r0 (Nat.mul b4 c4) z4 [] (c5 :: cR))
            | _, _ =>
              bSlZ z d ((((r0 + 1) + 1) + 1) + 1) p0 q0
                (hbz4C b1 z1 b2 z2 b3 z3 b4 z4 (hbz4L bR)) vs cs
private theorem bSlZ4_eq (z d : ℕ) : ∀ (hbz : HbZ4) (rem p0 q0 : ℕ) (vs cs : List ℕ),
    bSlZ4 z d hbz rem p0 q0 vs cs = bSlZ z d rem p0 q0 (hbz4L hbz) vs cs
  | HbZ4.tail _, _, _, _, _, _ => rfl
  | HbZ4.c4 _ _ _ _ _ _ b4 z4 bR, rem, _, _, vs, cs => by
    match rem with
    | 0 => rfl
    | r3 + 1 => match r3 with
      | 0 => rfl
      | r2 + 1 => match r2 with
        | 0 => rfl
        | r1 + 1 => match r1 with
          | 0 => rfl
          | r0 + 1 => match vs with
            | [] => match cs with
              | [] => rfl
              | [_] => rfl
              | [_, _] => rfl
              | [_, _, _] => rfl
              | [_, _, _, _] => rfl
              | _ :: _ :: _ :: c4 :: c5 :: cR =>
                dsimp only [bSlZ4, hbz4L, hbz4C, bSlZ, bHO]
                rw [uCN4e]
                exact congrArg (fun r => uC _ (uC _ (uC _ (uC _ r))))
                  (bSlZ4_eq z d bR r0 (Nat.mul b4 c4) z4 [] (c5 :: cR))
            | [_] => rfl
            | [_, _] => rfl
            | [_, _, _] => rfl
            | _ :: _ :: _ :: _ :: vR => match cs with
              | [] => rfl
              | [_] => rfl
              | [_, _] => rfl
              | [_, _, _] => rfl
              | [_, _, _, _] => rfl
              | _ :: _ :: _ :: c4 :: c5 :: cR =>
                dsimp only [bSlZ4, hbz4L, hbz4C, bSlZ, bHO]
                rw [uCN4e]
                exact congrArg (fun r => uC _ (uC _ (uC _ (uC _ r))))
                  (bSlZ4_eq z d bR r0 (Nat.mul b4 c4) z4 vR (c5 :: cR))
private def bDg (z dg mL cL : ℕ) (h4 : HbZ4) (vT cT : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlZ4 z d h4 nL 0 0 vT cT) fun raw => bChkP raw
private theorem bDg_rPad {z dg mL cL : ℕ} {b vT cT outT : List ℕ}
    (h : bDg z dg mL cL (toH4 (mkHbZ z b)) vT cT = some outT) :
    bAP outT = true ∧
      rPad z (rkmNextLen mL cL) outT =
        bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b vT cT := by
  unfold bDg at h
  dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq, bChkPe, bSlZ4_eq, hbz4L_toH4] at h
  rcases cond_some_eq h with ⟨hp, rfl⟩
  have hsl := bSlZ_rPad z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b vT cT
  rw [hzMul0 z] at hsl
  exact ⟨hp, hsl⟩
private theorem bDg_sound {z : ℕ} (hz : Nat.ble z 0 = false) (dg mL vL cL : ℕ)
    (b vT cT outT : List ℕ) (h : bDg z dg mL cL (toH4 (mkHbZ z b)) vT cT = some outT) :
    bDc z (rPad z (rkmNextLen mL cL) outT) =
      rkmUltraHornerStage dg mL cL (uOh b) (bDc z (rPad z vL vT)) (bDc z (rPad z cL cT)) := by
  rcases bDg_rPad h with ⟨hp, hsl⟩
  have hpos : bAP (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b
      (rPad z vL vT) (rPad z cL cT)) = true := by
    rw [bSl_rPad, ← hsl]
    exact bAP_rPad hz _ _ hp
  unfold rkmUltraHornerStage
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bM0 z, hsl,
    ← bSl_rPad z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z vL cL b vT cT]
  exact bSl_sound z _ _ 0 z b (rPad z vL vT) (rPad z cL cT) hpos
private def bDg1 (z mL cL : ℕ) (h4 : HbZ4) (vT cT : List ℕ) : Option (List ℕ) :=
  match bDg z 1 mL cL h4 vT cT with
  | none => none
  | some raw => fL (bTrim z raw) fun outT => some outT
private theorem bDg1_sound {z : ℕ} (hz : Nat.ble z 0 = false) (mL vL cL : ℕ)
    (b vT cT outT : List ℕ) (h : bDg1 z mL cL (toH4 (mkHbZ z b)) vT cT = some outT) :
    bDc z (rPad z (rkmNextLen mL cL) outT) =
      rkmUltraHornerStage 1 mL cL (uOh b) (bDc z (rPad z vL vT)) (bDc z (rPad z cL cT)) := by
  unfold bDg1 at h
  revert h
  cases hd : bDg z 1 mL cL (toH4 (mkHbZ z b)) vT cT with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some raw =>
    intro h
    dsimp only [fL] at h
    rw [rkmb_forceList_eq] at h
    injection h with h'
    subst h'
    rcases bDg_rPad hd with ⟨_, hsl⟩
    have hpad := rPad_bTrim_len z (bSl z (Nat.mul 1 wdScale) (rkmNextLen mL cL) 0 z b vT cT)
    rw [bSl_len] at hpad
    rw [← bTrim_rPad z (rkmNextLen mL cL) raw, hsl, hpad, ← hsl]
    exact bDg_sound hz 1 mL vL cL b vT cT raw hd
private def bBdD (z g m c : ℕ) (h4 : HbZ4) (vT xT : List ℕ)
    (k : ℕ → List ℕ → Option (List ℕ)) : Option (List ℕ) :=
  fN (rkmNextLen m c) fun n => match bDg z g m c h4 vT xT with | none => none | some o => k n o
private theorem bBdD_sound {z : ℕ} (hz : Nat.ble z 0 = false) {endL g m vL c : ℕ}
    {b vT xT outT : List ℕ} {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBdD z g m c (toH4 (mkHbZ z b)) vT xT kB = some outT)
    (hk : ∀ m0, kB (rkmNextLen m c) m0 = some outT →
      bDc z (rPad z endL outT) = kU (rkmNextLen m c) (bDc z (rPad z (rkmNextLen m c) m0))) :
    bDc z (rPad z endL outT) =
      (HighDForce.withForcedNat (rkmNextLen m c) fun nL => HighDForce.withForcedList
        (rkmUltraHornerStage g m c (uOh b) (bDc z (rPad z vL vT)) (bDc z (rPad z c xT))) (kU nL)) :=
  by
  unfold bBdD at h
  dsimp only [fN] at h
  rw [rkmb_forceNat_eq] at h
  revert h
  cases hs : bDg z g m c (toH4 (mkHbZ z b)) vT xT with
  | none =>
    intro h
    dsimp only at h
    cases h
  | some mid =>
    intro h
    rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bDg_sound hz g m vL c b vT xT mid hs]
    exact hk mid h
private def bSpD (z m c : ℕ) (h4 : HbZ4) (vT : List ℕ) : Option (List ℕ) :=
  bBdD z 16 m c h4 vT vT fun l x => bBdD z 15 m l h4 vT x fun l x =>
  bBdD z 14 m l h4 vT x fun l x => bBdD z 13 m l h4 vT x fun l x =>
  bBdD z 12 m l h4 vT x fun l x => bBdD z 11 m l h4 vT x fun l x =>
  bBdD z 10 m l h4 vT x fun l x => bBdD z 9 m l h4 vT x fun l x =>
  bBdD z 8 m l h4 vT x fun l x => bBdD z 7 m l h4 vT x fun l x =>
  bBdD z 6 m l h4 vT x fun l x => bBdD z 5 m l h4 vT x fun l x =>
  bBdD z 4 m l h4 vT x fun l x => bBdD z 3 m l h4 vT x fun l x =>
  bBdD z 2 m l h4 vT x fun l x => bDg1 z m l h4 vT x
private theorem bSpD_sound {z : ℕ} (hz : Nat.ble z 0 = false) (mL cL : ℕ) (b vT outT : List ℕ)
    (h : bSpD z mL cL (toH4 (mkHbZ z b)) vT = some outT) :
    bDc z (rPad z (rkmNextLen16 mL cL) outT) =
      rkmUltraHornerT16Step mL cL (uOh b) (bDc z (rPad z cL vT)) := by
  unfold bSpD at h
  unfold rkmUltraHornerT16Step
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  refine bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => bBdD_sound hz h fun _ h => ?_
  unfold rkmNextLen16
  exact bDg1_sound hz mL cL _ b vT _ outT h
private def bItD (z : ℕ) : ℕ → ℕ → ℕ → HbZ4 → List ℕ → Option (ℕ × List ℕ)
  | 0, _, c, _, vT => some (c, vT)
  | k + 1, m, c, h4, vT => match bSpD z m c h4 vT with
    | none => none
    | some vN => fN (rkmNextLen16 m c) fun nL => bItD z k m nL h4 vN
private theorem bItD_sound {z : ℕ} (hz : Nat.ble z 0 = false) :
    ∀ (k m c : ℕ) (b vT : List ℕ) (endL : ℕ) (outT : List ℕ),
      bItD z k m c (toH4 (mkHbZ z b)) vT = some (endL, outT) →
        bDc z (rPad z endL outT) = muxUltraIterFullT16Rkm k m c (uOh b) (bDc z (rPad z c vT))
  | 0, _, _, _, _, _, _, h => by
    injection h with h'
    injection h' with hc hv
    subst hc
    subst hv
    rfl
  | k + 1, m, c, b, vT, endL, outT, h => by
    unfold bItD at h
    revert h
    cases hs : bSpD z m c (toH4 (mkHbZ z b)) vT with
    | none =>
      intro h
      dsimp only at h
      cases h
    | some vN =>
      intro h
      dsimp only [fN] at h
      rw [rkmb_forceNat_eq] at h
      unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bSpD_sound hz m c b vT vN hs]
      exact bItD_sound hz k m _ b vN endL outT h
private theorem u2f {s m : ℕ} {b u v : List ℤ}
    (h : muxUltraIterFullT16Rkm s m (altIntLen u) b u = v) : muxFastIterFullT16 s m b u = v := by
  have hc : muxUltraIterFullT16HiChk s 0 m b u v = true := by
    unfold muxUltraIterFullT16HiChk
    dsimp only
    rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, h]
    exact muxIntListEq_eq_true.mpr rfl
  exact muxUltraIterFullT16HiChk_sound hc
private def pWOk (k m : ℕ) (bns : List ℕ) (l0 : ℕ) (uT : List ℕ) (l1 : ℕ) (vT : List ℕ) : Prop :=
  muxFastIterFullT16 k m (uOh bns) (bDc bZ (rPad bZ l0 uT)) = bDc bZ (rPad bZ l1 vT)
private def bSlChk (s m : ℕ) (bns : List ℕ) (l0 : ℕ) (uT : List ℕ) (l1 : ℕ) (vT : List ℕ) :
    Bool :=
  fL bns fun bF => fL uT fun uF => fL vT fun vF =>
    cond (Nat.ble (bNL uF) l0)
      (fH4 (toH4 (mkHbZ bZ bF)) fun h4 =>
        match bItD bZ s m l0 h4 uF with
        | none => false
        | some (endL, outT) => cond (muxNatListEq [endL] [l1]) (muxNatListEq outT vF) false)
      false
private theorem bSlSnd {s m : ℕ} {bns : List ℕ} {l0 : ℕ} {uT : List ℕ} {l1 : ℕ} {vT : List ℕ}
    (h : bSlChk s m bns l0 uT l1 vT = true) : pWOk s m bns l0 uT l1 vT := by
  unfold bSlChk at h
  unfold pWOk
  dsimp only [fL] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq] at h
  revert h
  cases hle : Nat.ble (bNL uT) l0 with
  | false =>
    intro h
    dsimp only [cond] at h
    exact Bool.noConfusion h
  | true =>
    intro h
    dsimp only [cond] at h
    rw [fH4e] at h
    revert h
    cases hi : bItD bZ s m l0 (toH4 (mkHbZ bZ bns)) uT with
    | none =>
      intro h
      dsimp only at h
      exact Bool.noConfusion h
    | some p =>
      cases p with
      | mk endL outT =>
        intro h
        dsimp only at h
        revert h
        cases he : muxNatListEq [endL] [l1] with
        | false =>
          intro h
          dsimp only [cond] at h
          exact Bool.noConfusion h
        | true =>
          intro h
          dsimp only [cond] at h
          have hl1 : endL = l1 := (List.cons.inj (muxNatListEq_eq_true.mp he)).1
          have hot : outT = vT := muxNatListEq_eq_true.mp h
          have hit := bItD_sound hbZ0 s m l0 bns uT endL outT hi
          rw [hl1, hot] at hit
          have hln : altIntLen (bDc bZ (rPad bZ l0 uT)) = l0 := by
            rw [← bNL_eq bZ]
            exact rPad_bNL bZ l0 uT hle
          refine u2f ?_
          rw [hln]
          exact hit.symm
private theorem bCh (k1 k2 mL : ℕ) {bns : List ℕ} {l0 : ℕ} {v0 : List ℕ}
    {l1 : ℕ} {v1 : List ℕ} {l2 : ℕ} {v2 : List ℕ}
    (h1 : pWOk k1 mL bns l0 v0 l1 v1) (h2 : bSlChk k2 mL bns l1 v1 l2 v2 = true) :
    pWOk (k1 + k2) mL bns l0 v0 l2 v2 :=
  (muxFastIterFullT16_add k1 k2 mL (uOh bns) (bDc bZ (rPad bZ l0 v0))).trans
    ((congrArg (muxFastIterFullT16 k2 mL (uOh bns)) h1).trans (bSlSnd h2))
private theorem bLift {n m : ℕ} {hb1 hb2 vi1 vi2 vo1 vo2 : List ℤ}
    (hw : muxFastIterFullT16 n m hb1 vi1 = vo1)
    (hhb : muxIntListEq hb1 hb2 = true) (hvi : muxIntListEq vi1 vi2 = true)
    (hvo : muxIntListEq vo1 vo2 = true) : muxFastIterFullT16 n m hb2 vi2 = vo2 := by
  rw [← muxIntListEq_eq_true.mp hhb, ← muxIntListEq_eq_true.mp hvi,
    ← muxIntListEq_eq_true.mp hvo]
  exact hw
private theorem bH {b : Bool} {bs : List Bool} (h : rkmAllTrueF (b :: bs) = true) : b = true :=
  (rkmAllTrueF_cons h).1
private theorem bT {b : Bool} {bs : List Bool}
    (h : rkmAllTrueF (b :: bs) = true) : rkmAllTrueF bs = true := (rkmAllTrueF_cons h).2
private def pCat : List ℕ → List ℕ → List ℕ
  | [], ys => ys
  | x :: xs, ys => x :: pCat xs ys
private def phbn_w0_p0 : List ℕ := [105908879063360,149338899447892,182364366395688,
  209955161526427,234042396821001,255619436985228,275278118410665,293405171567037,310269990014657,
  326069274755081,340951937769037,355033992669033,368407955458100,381149044877090,393319421981127,
  404971177980257,416148494808663,426889242517676,437226183332455,447187894775024,456799488136996,
  466083175235417,475058720916254,483743808296034,492154336499605,500304665568679,508207819585023,
  515875656420657,523319010594284,530547814275513,537571200396956,544397591012149,551034773406085,
  557489965976222,563769875519791,569880747262391,575828408724111,581618308328713,587255549507984,
  592744920929237,598090923372819,603297793703829,608369526314088,613309892354150,618122457028342,
  622810595186743,627377505415311,631826222797794,636159630499754,640380470305313,644491352220409,
  648494763241959,652393075380071,656188553009808,659883359619951,663479564018245,666979146045840,
  670384001847638,673695948740112,676916729713594,680048017602085,683091418950148,686048477603368,
  688920678046170]
private def phbn_w0_p1 : List ℕ := [691709448508377,694416163859796,697042148310217,
  699588677930549,702056983009343,704448250257585,706763624873508,709004212478062,711171080930748,
  713265262034685,715287753138963,717239518645684,719121491428450,720934574168485,722679640614076,
  724357536768560,725969082011639,727515070158454,728996270460474,730413428551963,731767267345479,
  733058487879609,734287770121900,735455773729719,736563138771587,737610486411330,738598419557240,
  739527523478256,740398366389068,741211500005872,741967460074427,742666766871910,743309925683995,
  743897427258459,744429748236563,744907351563327,745330686877791,745700190884238,746016287705336,
  746279389218043,746489895373107,746648194498917,746754663590409,746809668583705,746813564617084,
  746766696278893,746669397842918,746521993491728,746324797528475,746078114577570,745782239774669,
  745437458946335,745044048779746,744602276982760,744112402434676,743574675327939,742989337301078,
  742356621563108,741676753009617,740949948330748,740176416111247,739356356922759,738489963408510,
  737577420360509]
private def phbn_w0_p2 : List ℕ := [736618904789396,735614585987017,734564625581831,
  733469177587209,732328388442675,731142397048133,729911334791111,728635325567016,727314485792403,
  725948924411246,724538742894146,723084035230467,721584887913286,720041379917117,718453582668270,
  716821560007761,715145368146617,713425055613429,711660663193983,709852223862783,707999762706240,
  706103296837304,704162835301284,702178378972567,700149920441940,698077443894183,695960924975558,
  693800330650828,691595619049370,689346739299920,687053631353479,684716225793826,682334443635084,
  679908196105717,677437384418279,674921899524235,672361621853035,669756421034662,667106155604711,
  664410672691076,661669807681175,658883383868612,656051212078056,653173090267040,650248803103265,
  647278121515890,644260802219161,641196587206600,638085203213829,634926361147931,631719755481100,
  628465063606107,625161945150923,621810041249594,618408973766220,614958344468581,611457734147682,
  607906701679114,604304783021757,600651490148947,596946309906729,593188702793348,589378101653500,
  585513910280274]
private def phbn_w0_p3 : List ℕ := [581595501916964,577622217650152,573593364684556,
  569508214489139,565366000802845,561165917487052,556907116210419,552588703950158,548209740291947,
  543769234508630,539266142395460,534699362836959,530067734077410,525370029663438,520604954023111,
  515771137641340,510867131785968,505891402732736,500842325430082,495718176536350,490517126752146,
  485237232359114,479876425862879,474432505621955,468903124325556,463285776160791,457577782482928,
  451776275770297,445878181606718,439880198387524,433778774388317,427570081766036,421249986976320,
  414814016985426,408257320523311,401574623459655,394760177176734,387807698548846,380710299799667,
  373460406071857,366049657973498,358468795615991,350707519660327,342754323546217,334596289249757,
  326218836390385,317605410970191,308737094991839,299592110901828,290145184017823,280366709802928,
  270221647624523,259668022493461,248654850359547,237119190301533,224981827645684,212140720163038,
  198460603168753,183755581701841,167757882080313,150056336253845,129958525751475,106113917824816,
  75035011369245]
private def phbn_w0 : List ℕ := pCat phbn_w0_p0 (pCat phbn_w0_p1 (pCat phbn_w0_p2 phbn_w0_p3))
private def phbv_w0 : List ℤ := uOh phbn_w0
private def pvn_w0_0 : List ℕ := [3000000000000000]
private def pvn_w0_1_p0 : List ℕ := [2000041441181930,2000191861130165,2000626205573109,
  2001663746393093,2003816538613899,2007806829007848,2014533234298207,2024971545823414,
  2040012642088376,2060260543655876,2085831363640403,2116202138779669,2150153338069501,
  2185830661461774,2220925307022599,2252944628678467,2279524595933542,2298726980099275,
  2309269258526852,2310651535464277,2303167286206286,2287807457302914,2266085243807067,
  2239818603258639,2210908600090754,2181145465765437,2152063568878743,2124854415439764,
  2100335981673704,2078968823332179,2060905154732800,2046056202523340,2034164792715908,
  2024873275627496,2017780539375896,2012485250335255,2008615132031631,2005843878833078,
  2003898237422903,2002558044739259,2001651802178758,2001049900557244,2000657055604010,
  2000404983538853,2000245904038791,2000147127352594,2000086760508688,2000050436907296,
  2000028911119078,2000016344052565,2000009114176400,2000005014397317,2000002722331828,
  2000001458674947,2000000771511159,2000000402865708,2000000207719965,2000000105769112,
  2000000053193985,2000000026426962,2000000012970858,2000000006290431,2000000003014627,
  2000000001427835]
private def pvn_w0_1_p1 : List ℕ := [2000000000668433,2000000000309325,2000000000141513,
  2000000000064007,2000000000028620,2000000000012650,2000000000005525,2000000000002384,
  2000000000001013,2000000000000420,2000000000000170,2000000000000067,2000000000000023,
  2000000000000006,2000000000000001]
private def pvn_w0_1 : List ℕ := pCat pvn_w0_1_p0 pvn_w0_1_p1
private def pvn_w0_2_p0 : List ℕ := [2000000000034245,2000000000255960,2000000001348521,
  2000000005782780,2000000021407713,2000000070659289,2000000212223791,2000000588243903,
  2000001520311347,2000003692621201,2000008481199416,2000018513055837,2000038565140848,
  2000076933677820,2000147410040928,2000271977427573,2000484280060918,2000833803211383,
  2001390534775095,2002249666076497,2003535654733218,2005404755491435,2008044978201968,
  2011672412683876,2016523018327525,2022839341453289,2030852191741631,2040758034852141,
  2052693653736489,2066710374814268,2082750710508671,2100630509336340,2120029537349139,
  2140492807259014,2161443962906269,2182210727777008,2202061005992329,2220246883323441,
  2236052713226413,2248842851220602,2258104518011771,2263481743938671,2264797307430332,
  2262060890257877,2255463148305813,2245356839273385,2232227375894881,2216656046146659,
  2199279582318477,2180749756880367,2161696283626547,2142695602786255,2124247250409868,
  2106758582735542,2090537759795007,2075794177002964,2062645022746250,2051126352963743,
  2041206998588633,2032803723757002,2025796283517255,2020041336650537,2015384502676995,
  2011670171443726]
private def pvn_w0_2_p1 : List ℕ := [2008748949766084,2006482845573871,2004748440130887,
  2003438386164550,2002461603157297,2001742532818774,2001219780926313,2000844418422393,
  2000578154996854,2000391539931542,2000262292750529,2000173822923899,2000113964427001,
  2000073926975857,2000047450059656,2000030136900670,2000018941538120,2000011781826205,
  2000007252966323,2000004419248929,2000002665227226,2000001591092283,2000000940271821,
  2000000550084209,2000000318597715,2000000182689307,2000000103719195,2000000058304020,
  2000000032452515,2000000017886493,2000000009762132,2000000005276204,2000000002824038,
  2000000001496940,2000000000785840,2000000000408578,2000000000210387,2000000000107294,
  2000000000054193,2000000000027105,2000000000013423,2000000000006579,2000000000003186,
  2000000000001524,2000000000000720,2000000000000333,2000000000000148,2000000000000062,
  2000000000000022,2000000000000006,2000000000000001]
private def pvn_w0_2 : List ℕ := pCat pvn_w0_2_p0 pvn_w0_2_p1
private def pvn_w0_3_p0 : List ℕ := [2000000000000001,1999999999999995,2000000000000005,
  2000000000000010,2000000000000022,2000000000000051,2000000000000195,2000000000000706,
  2000000000002454,2000000000008048,2000000000025007,2000000000073832,2000000000208045,
  2000000000561325,2000000001454463,2000000003628337,2000000008733661,2000000020324135,
  2000000045803958,2000000100123414,2000000212572779,2000000438892293,2000000882215827,
  2000001728234771,2000003302537716,2000006161444441,2000011231813932,2000020020111611,
  2000034916082445,2000059620988953,2000099733458927,2000163526082287,2000262941211293,
  2000414823007859,2000642382830485,2000976865284226,2001459342425300,2002142515027320,
  2003092345783494,2004389295389827,2006128886342791,2008421290365925,2011389633693487,
  2015166749260809,2019890182932285,2025695384649433,2032707181283934,2041029825603305,
  2050736127692100,2061856378111796,2074367939083747,2088186483758258,2103159880497600,
  2119065632972028,2135612592707961,2152447366739160,2169165471091245,2185326865008062,
  2200475083760387,2214158815778567,2225954486560520,2235488252858576,2242455798260697,
  2246638461054193]
private def pvn_w0_3_p1 : List ℕ := [2247914505127746,2246264736279911,2241772128630831,
  2234615610451534,2225058615958033,2213433394651814,2200122347871623,2185537812264157,
  2170101726062567,2154226505359062,2138298245435189,2122663076954710,2107617183140598,
  2093400656642112,2080195074414983,2068124419504107,2057258795511516,2047620269173792,
  2039190137037035,2031916935196792,2025724583354439,2020520160550027,2016200934103010,
  2012660391192276,2009793142425747,2007498670253276,2005683977143711,2004265247202759,
  2003168671068824,2002330600094761,2001697195765403,2001223728261615,2000873658248508,
  2000617612072160,2000432335643394,2000299688628243,2000205719641091,2000139845752922,
  2000094146037144,2000062768928947,2000041446460524,2000027104403927,2000017555413873,
  2000011261848958,2000007155563829,2000004503199556,2000002807041616,2000001733139495,
  2000001059940312,2000000642093503,2000000385291491,2000000229012755,2000000134838348,
  2000000078642018,2000000045434612,2000000026002371,2000000014741293,2000000008278597,
  2000000004605515,2000000002538052,2000000001385555,2000000000749283,2000000000401387,
  2000000000212994]
private def pvn_w0_3_p2 : List ℕ := [2000000000111956,2000000000058285,2000000000030052,
  2000000000015345,2000000000007755,2000000000003873,2000000000001911,2000000000000928,
  2000000000000440,2000000000000203,2000000000000089,2000000000000036,2000000000000012,
  2000000000000002]
private def pvn_w0_3 : List ℕ := pCat pvn_w0_3_p0 (pCat pvn_w0_3_p1 pvn_w0_3_p2)
private def pvn_w0_4_p0 : List ℕ := [2000000000000001,1999999999999995,2000000000000000,
  1999999999999996,2000000000000002,1999999999999995,2000000000000005,2000000000000005,
  2000000000000010,2000000000000009,2000000000000007,2000000000000011,2000000000000015,
  2000000000000011,2000000000000016,2000000000000017,2000000000000023,2000000000000063,
  2000000000000150,2000000000000396,2000000000001033,2000000000002680,2000000000006764,
  2000000000016715,2000000000040280,2000000000094788,2000000000217918,2000000000489799,
  2000000001076928,2000000002317814,2000000004885859,2000000010092769,2000000020441207,
  2000000040610381,2000000079176479,2000000151553817,2000000284919018,2000000526286708,
  2000000955483879,2000001705570280,2000002994324036,2000005171796427,2000008790659016,
  2000014708102318,2000024230319627,2000039312956206,2000062833044774,2000098949469611,
  2000153569349067,2000234936211444,2000354351682038,2000527034801934,2000773111363754,
  2001118709328269,2001597115465412,2002249923453175,2003128076166896,2004292677097657,
  2005815420954849,2007778475512378,2010273640104748,2013400615330899,2017264247332498,
  2021970661006635]
private def pvn_w0_4_p1 : List ℕ := [2027622270173268,2034311746866272,2042115141327734,
  2051084460645131,2061240126271925,2072563826071072,2084992341629518,2098412954086521,
  2112661002087711,2127520078664823,2142725210541264,2157969170710783,2172911846632902,
  2187192340976337,2200443242167412,2212306292037810,2222448520180549,2230577827620098,
  2236456997955970,2239915195919573,2240856176060726,2239262654306158,2235196571587169,
  2228795276037612,2220263940965825,2209864793650202,2197903932794097,2184716644327184,
  2170652178044881,2156058921431439,2141270809687698,2126595656543768,2112305897231602,
  2098632023355178,2085758779325704,2073823999159126,2062919804497717,2053095768635679,
  2044363580942436,2036702720485180,2030066662004152,2024389184001467,2019590418268455,
  2015582362980319,2012273668424037,2009573587765922,2007395059134845,2005656945861909,
  2004285507118736,2003215201297967,2002388940488680,2001757918443688,2001281129142072,
  2000924681178916,2000660997369388,2000467971386111,2000328135742983,2000227879280820,
  2000156738310807,2000106774129964,2000072040810728,2000048140822398,2000031861854800,
  2000020885798908]
private def pvn_w0_4_p2 : List ℕ := [2000013559792843,2000008719186327,2000005552881468,
  2000003502503435,2000002188034788,2000001353763197,2000000829546881,2000000503437330,
  2000000302588361,2000000180117951,2000000106182989,2000000061992743,2000000035843386,
  2000000020523589,2000000011637703,2000000006534966,2000000003633902,2000000002001008,
  2000000001091090,2000000000589111,2000000000314950,2000000000166717,2000000000087370,
  2000000000045324,2000000000023273,2000000000011824,2000000000005938,2000000000002945,
  2000000000001440,2000000000000689,2000000000000322,2000000000000143,2000000000000059,
  2000000000000022,2000000000000006,2000000000000001]
private def pvn_w0_4 : List ℕ := pCat pvn_w0_4_p0 (pCat pvn_w0_4_p1 pvn_w0_4_p2)
private def pvn_w0_5_p0 : List ℕ := [2000000000000001,1999999999999995,2000000000000000,
  1999999999999996,2000000000000002,2000000000000001,1999999999999996,1999999999999999,
  1999999999999999,1999999999999997,1999999999999994,2000000000000009,2000000000000000,
  2000000000000007,2000000000000005,2000000000000009,2000000000000003,2000000000000007,
  2000000000000010,2000000000000015,2000000000000008,2000000000000012,2000000000000012,
  2000000000000014,2000000000000012,2000000000000011,2000000000000017,2000000000000018,
  2000000000000020,2000000000000027,2000000000000049,2000000000000090,2000000000000209,
  2000000000000471,2000000000001096,2000000000002533,2000000000005786,2000000000013008,
  2000000000028761,2000000000062544,2000000000133746,2000000000281330,2000000000582203,
  2000000001185672,2000000002376853,2000000004691258,2000000009118540,2000000017458529,
  2000000032932865,2000000061218095,2000000112161433,2000000202582683,2000000360773176,
  2000000633598584,2000001097523983,2000001875437679,2000003161886262,2000005260274733,
  2000008636749148,2000013996861061,2000022392676316,2000035369650529,2000055164201289,
  2000084964234667]
private def pvn_w0_5_p1 : List ℕ := [2000129245615275,2000194197296385,2000288246062972,
  2000422688048561,2000612427832767,2000876816555617,2001240567822444,2001734714240642,
  2002397548668656,2003275473638693,2004423661514585,2005906408964557,2007797055017709,
  2010177325468721,2013135970931675,2016766584363944,2021164518569036,2026422875971000,
  2032627611034004,2039851867207195,2048149760099440,2057549909493817,2068049105844494,
  2079606562127809,2092139239438012,2105518735851735,2119570186641522,2134073537324977,
  2148767421195542,2163355706667133,2177516588460133,2190913895772183,2203210098097230,
  2214080324028745,2223226587657745,2230391355143693,2235369589638736,2238018488514355,
  2238264268344124,2236105549209554,2231613123861966,2224926148457711,2216245037691196,
  2205821566625064,2193946855829819,2180938031977012,2167124405328307,2152833987848787,
  2138381096560702,2124055657267770,2110114658830562,2096776024717442,2084214983688109,
  2072562850675812,2061907984714039,2052298581695740,2043746890173058,2036234408477789,
  2029717627760215,2024133921983143,2019407244648239,2015453364592125,2012184451360139,
  2009512897248078]
private def pvn_w0_5_p2 : List ℕ := [2007354332408040,2005629847511049,2004267483189140,
  2003203076288898,2002380570612678,2001751906002275,2001276596599868,2000921099394314,
  2000658060156009,2000465507744029,2000326051301772,2000226119360674,2000155266217972,
  2000105559618089,2000071054896282,2000047354241101,2000031245341941,2000020411062644,
  2000013200543911,2000008451920291,2000005357316723,2000003361693755,2000002088227997,
  2000001284092113,2000000781631402,2000000470959890,2000000280885929,2000000165816487,
  2000000096886671,2000000056030614,2000000032069899,2000000018166275,2000000010183914,
  2000000005649735,2000000003101623,2000000001684919,2000000000905685,2000000000481681,
  2000000000253457,2000000000131940,2000000000067936,2000000000034595,2000000000017417,
  2000000000008664,2000000000004254,2000000000002056,2000000000000976,2000000000000453,
  2000000000000203,2000000000000085,2000000000000032,2000000000000011,2000000000000002]
private def pvn_w0_5 : List ℕ := pCat pvn_w0_5_p0 (pCat pvn_w0_5_p1 pvn_w0_5_p2)
private def pvn_w0_6_p0 : List ℕ := [2000000000000001,1999999999999995,2000000000000000,
  2000000000000000,1999999999999993,2000000000000000,1999999999999998,2000000000000009,
  1999999999999996,1999999999999996,2000000000000000,2000000000000006,1999999999999999,
  1999999999999997,1999999999999993,2000000000000000,2000000000000001,1999999999999998,
  2000000000000003,2000000000000009,2000000000000010,2000000000000000,2000000000000003,
  2000000000000004,2000000000000012,2000000000000007,2000000000000001,2000000000000007,
  2000000000000011,2000000000000009,2000000000000009,2000000000000010,2000000000000007,
  2000000000000007,2000000000000013,2000000000000017,2000000000000016,2000000000000015,
  2000000000000015,2000000000000017,2000000000000019,2000000000000020,2000000000000026,
  2000000000000030,2000000000000037,2000000000000071,2000000000000138,2000000000000280,
  2000000000000611,2000000000001337,2000000000002937,2000000000006375,2000000000013656,
  2000000000028879,2000000000060253,2000000000123978,2000000000251624,2000000000503770,
  2000000000995003,2000000001939042,2000000003728848,2000000007076853,2000000013256731,
  2000000024513985]
private def pvn_w0_6_p1 : List ℕ := [2000000044752982,2000000080669338,2000000143588366,
  2000000252405383,2000000438217160,2000000751506711,2000001273118852,2000002130767968,
  2000003523478966,2000005757201743,2000009295872527,2000014833421531,2000023393616891,
  2000036466119969,2000056188588295,2000085585911024,2000128878434073,2000191870985251,
  2000282433224475,2000411078848333,2000591645984977,2000842073282597,2001185255406397,
  2001649947825711,2002271674139136,2003093570437993,2004167081560984,2005552405330129,
  2007318565313928,2009542983114943,2012310420636681,2015711174188031,2019838428098849,
  2024784717291151,2030637506130807,2037473963240943,2045355095101381,2054319489382112,
  2064377004351371,2075502814250713,2087632272540938,2100657076148851,2114423196687240,
  2128730984322830,2143337745641760,2157962952192008,2172296059837751,2186006723545004,
  2198756994108330,2210214900977706,2220068677180475,2228040784776862,2233900864750884,
  2237476770467800,2238662948839442,2237425601111220,2233804272189269,2227909764950753,
  2219918532086155,2210063939914390,2198625005097345,2185913358924010,2172259283115667,
  2157997680873105]
private def pvn_w0_6_p2 : List ℕ := [2143454799019030,2128936409819340,2114718007748605,
  2101037393812112,2088089826132321,2076025727816708,2064950776763103,2054928068500311,
  2045981949486029,2038103067003960,2031254171206230,2025376229767753,2020394468453912,
  2016224022751035,2012774967466371,2009956574489632,2007680726754651,2005864483707729,
  2004431847102924,2003314814399576,2002453830728155,2001797760830904,2001303501884899,
  2000935349380384,2000664213999216,2000466770233701,2000324599416367,2000223372513376,
  2000152102575492,2000102483777902,2000068323755991,2000045068400657,2000029413150769,
  2000018991730224,2000012131795636,2000007666666680,2000004792827115,2000002963894404,
  2000001813012955,2000001096950590,2000000656449410,2000000388528463,2000000227420917,
  2000000131644228,2000000075355363,2000000042652419,2000000023870731,2000000013208537,
  2000000007225770,2000000003907742,2000000002089062,2000000001103898,2000000000576536,
  2000000000297578,2000000000151772,2000000000076481,2000000000038070,2000000000018709,
  2000000000009072,2000000000004335,2000000000002039,2000000000000939,2000000000000418,
  2000000000000182]
private def pvn_w0_6_p3 : List ℕ := [2000000000000074,2000000000000026,2000000000000006,
  2000000000000001]
private def pvn_w0_6 : List ℕ := pCat pvn_w0_6_p0 (pCat pvn_w0_6_p1 (pCat pvn_w0_6_p2
  pvn_w0_6_p3))
private def pvn_w0_7_p0 : List ℕ := [2000000000000001,1999999999999998,1999999999999991,
  2000000000000004,1999999999999999,2000000000000000,1999999999999997,1999999999999995,
  1999999999999991,1999999999999997,2000000000000005,2000000000000003,2000000000000004,
  1999999999999995,1999999999999993,1999999999999998,2000000000000010,2000000000000007,
  1999999999999997,2000000000000000,2000000000000001,1999999999999999,1999999999999998,
  1999999999999992,1999999999999990,2000000000000001,2000000000000012,2000000000000007,
  1999999999999997,2000000000000004,2000000000000007,2000000000000004,2000000000000007,
  2000000000000007,2000000000000002,2000000000000001,2000000000000003,2000000000000007,
  2000000000000020,2000000000000010,2000000000000002,2000000000000008,2000000000000007,
  2000000000000004,2000000000000008,2000000000000014,2000000000000016,2000000000000013,
  2000000000000012,2000000000000010,2000000000000014,2000000000000026,2000000000000020,
  2000000000000016,2000000000000019,2000000000000021,2000000000000024,2000000000000029,
  2000000000000029,2000000000000034,2000000000000054,2000000000000064,2000000000000124,
  2000000000000262]
private def pvn_w0_7_p1 : List ℕ := [2000000000000533,2000000000001149,2000000000002469,
  2000000000005243,2000000000011085,2000000000023153,2000000000047727,2000000000097221,
  2000000000195593,2000000000388592,2000000000762475,2000000001477673,2000000002828620,
  2000000005348707,2000000009991490,2000000018439569,2000000033623262,2000000060579589,
  2000000107854538,2000000189759379,2000000329949294,2000000567016553,2000000963104712,
  2000001616978924,2000002683560166,2000004402675920,2000007140720489,2000011450068402,
  2000018152437300,2000028453914200,2000044100956770,2000067588215243,2000102430271220,
  2000153510051152,2000227516350682,2000333481126907,2000483423449099,2000693100708076,
  2000982858397118,2001378557180896,2001912540023366,2002624583216147,2003562754117260,
  2004784076776504,2006354886539708,2008350738957508,2010855730114670,2013961088290847,
  2017762913940021,2022358978952434,2027844548463539,2034307258786245,2041821170868379,
  2050440215065035,2060191342555845,2071067791899556,2083022955051787,2095965374360951,
  2109755410244900,2124204080499808,2139074482394488,2154086068728296,2168921865406001,
  2183238503030608]
private def pvn_w0_7_p2 : List ℕ := [2196678705756909,2208885657963055,2219518475457803,
  2228267864240816,2234870973997743,2239124457355785,2240894833583992,2240125422438245,
  2236839347293795,2231138386355329,2223197751186315,2213257165282591,2201608874898972,
  2188583426557774,2174534173664361,2159821519487376,2144797865214559,2129794118003084,
  2115108440039695,2100997705642542,2087671901768931,2075291480083125,2063967465523741,
  2053763962195510,2044702581956409,2036768257947386,2029915892670514,2024077321655250,
  2019168139635847,2015094025154801,2011756300010899,2009056561374170,2006900317979635,
  2005199641301630,2003874904303461,2002855722981772,2002081240245520,2001499899950740,
  2001068854348581,2000753134373738,2000524692618437,2000361406620006,2000246107754865,
  2000165680410939,2000110258363004,2000072530967601,2000047161018020,2000030308609003,
  2000019250697133,2000012083649639,2000007495379829,2000004594145161,2000002782287593,
  2000001664773771,2000000984085711,2000000574648943,2000000331459628,2000000188834851,
  2000000106248066,2000000059035049,2000000032389939,2000000017546126,2000000009383863,
  2000000004954135]
private def pvn_w0_7_p3 : List ℕ := [2000000002581631,2000000001327733,2000000000673854,
  2000000000337444,2000000000166704,2000000000081227,2000000000039023,2000000000018475,
  2000000000008613,2000000000003950,2000000000001775,2000000000000780,2000000000000332,
  2000000000000134,2000000000000049,2000000000000016,2000000000000004]
private def pvn_w0_7 : List ℕ := pCat pvn_w0_7_p0 (pCat pvn_w0_7_p1 (pCat pvn_w0_7_p2
  pvn_w0_7_p3))
private def pvi_w0 : List ℤ := bDc bZ (rPad bZ 1 pvn_w0_0)
private def pvo_w0 : List ℤ := bDc bZ (rPad bZ 257 pvn_w0_7)
private def phbn_w1_p0 : List ℕ := [106259464187219,149833248902092,182968038481974,
  210650166109230,234817136232876,256465601846653,276189358469971,294376416748032,311297062001832,
  327148646362898,342080574748202,356209244804595,369627478786430,382410744427579,394621408551950,
  406311734804644,417526051373198,428302353668373,438673512366562,448668199588601,458311609750818,
  467626028196979,476631285199681,485345122411030,493783491585992,501960800301639,509890115752739,
  517583335063861,525051328618700,532304061464851,539350696767242,546199684458530,552858837601588,
  559335398488591,565636096117962,571767196388573,577734546111076,583543611744890,589199513615452,
  594707056241769,600070755302910,605294861689065,610383383014501,615340102913233,620168598391314,
  624872255470426,629454283324659,633917727084650,638265479459968,642500291310733,646624781282662,
  650641444605259,654552661140583,658360702759352,662067740112040,665675848854668,669187015382160,
  672603142116136,675926052388846,679157494960359,682299148202180,685352623976938,688319471240739,
  691201179392025]
private def phbn_w1_p1 : List ℕ := [693999181388421,696714856650899,699349533772717,
  701904493048903,704380968840572,706780151787023,709103190877387,711351195392494,713525236726733,
  715626350098750,717655536159112,719613762502337,721501965090073,723321049591646,725071892647672,
  726755343061972,728372222926602,729923328684431,731409432133344,732831281375843,734189601717510,
  735485096517546,736718447994361,737890317988957,739001348688641,740052163313450,741043366767453,
  741975546256978,742849271877647,743665097171979,744423559659185,745125181338692,745770469168794,
  746359915521770,746893998616683,747373182931019,747797919592234,748168646750215,748485789931582,
  748749762376710,748960965360284,749119788496159,749226610027220,749281797100928,749285706031161,
  749238682546940,749141062028581,748993169731781,748795321000112,748547821466370,748250967243185,
  747905045103278,747510332649729,747067098476581,746575602320086,746036095200890,745448819557405,
  744814009370628,744131890280609,743402679694788,742626586888381,741803813096975,740934551601493,
  740018987805654]
private def phbn_w1_p2 : List ℕ := [739057299306046,738049655954915,736996219915751,
  735897145711747,734752580267179,733562662941746,732327525557901,731047292421176,729722080333496,
  728351998599463,726937149025576,725477625912323,723973516039099,722424898641840,720831845383298,
  719194420315819,717512679836500,715786672634575,714016439630842,712202013908959,710343420638378,
  708440676988699,706493792035171,704502766655077,702467593414679,700388256446401,698264731315891,
  696096984878556,693884975125170,691628651016074,689327952303490,686982809341412,684593142882502,
  682158863861364,679679873163544,677156061379526,674587308542954,671973483852251,669314445374732,
  666610039732242,663860101767293,661064454188544,658222907194447,655335258073724,652401290781271,
  649420775487965,646393468102713,643319109764973,640197426305791,637028127675281,633810907334262,
  630545441607594,627231388996530,623868389447180,620456063571918,616994011820275,613481813595569,
  609919026313156,606305184395826,602639798201420,598922352877316,595152307135872,591329091944356,
  587452109122262]
private def phbn_w1_p3 : List ℕ := [583520729838161,579534292997466,575492103511567,
  571393430437805,567237504978606,563023518326828,558750619342937,554417912048014,550024452914730,
  545569247936372,541051249451609,536469352699995,531822392080108,527109137078703,522328287835177,
  517478470301002,512558230948350,507566030975947,502500239952903,497359128832864,492140862260994,
  486843490084739,481464937965794,476002996974684,470455312030435,464819369025280,459092480447497,
  453271769283195,447354150939102,441336312881405,435214691628603,428985446666506,422644430767680,
  416187156091510,409608755309024,402903936831200,396066933010939,389091439923806,381970546993199,
  374696654287088,367261374741858,359655417816341,351868450078115,343888926877273,335703887427992,
  327298703084968,318656765052381,309759092709545,300583836413765,291105637817124,281294794384235,
  271116149489142,260527589194887,249477960681198,237904114676490,225726574286464,212842959496620,
  199117557861867,184363859061968,168313203016458,150553060604973,130388721276629,106465181678733,
  75283396197668]
private def phbn_w1 : List ℕ := pCat phbn_w1_p0 (pCat phbn_w1_p1 (pCat phbn_w1_p2 phbn_w1_p3))
private def phbv_w1 : List ℤ := uOh phbn_w1
private def pvn_w1_0_p0 : List ℕ := [2000000000000001,1999999999999998,1999999999999991,
  2000000000000004,1999999999999999,2000000000000000,1999999999999997,1999999999999995,
  1999999999999991,1999999999999997,2000000000000005,2000000000000003,2000000000000004,
  1999999999999995,1999999999999993,1999999999999998,2000000000000010,2000000000000007,
  1999999999999997,2000000000000000,2000000000000001,1999999999999999,1999999999999998,
  1999999999999992,1999999999999990,2000000000000001,2000000000000012,2000000000000007,
  1999999999999997,2000000000000004,2000000000000007,2000000000000004,2000000000000007,
  2000000000000007,2000000000000002,2000000000000001,2000000000000003,2000000000000007,
  2000000000000020,2000000000000010,2000000000000002,2000000000000008,2000000000000007,
  2000000000000004,2000000000000008,2000000000000014,2000000000000016,2000000000000013,
  2000000000000012,2000000000000010,2000000000000014,2000000000000026,2000000000000020,
  2000000000000016,2000000000000019,2000000000000021,2000000000000024,2000000000000029,
  2000000000000029,2000000000000034,2000000000000054,2000000000000064,2000000000000124,
  2000000000000262]
private def pvn_w1_0_p1 : List ℕ := [2000000000000533,2000000000001149,2000000000002469,
  2000000000005243,2000000000011085,2000000000023153,2000000000047727,2000000000097221,
  2000000000195593,2000000000388592,2000000000762475,1999999998522327,1999999997171380,
  1999999994651293,1999999990008510,1999999981560431,2000000033623262,2000000060579589,
  1999999892145462,2000000189759379,2000000329949294,2000000567016553,2000000963104712,
  2000001616978924,2000002683560166,2000004402675920,2000007140720489,2000011450068402,
  2000018152437300,2000028453914200,2000044100956770,2000067588215243,2000102430271220,
  2000153510051152,2000227516350682,2000333481126907,2000483423449099,2000693100708076,
  2000982858397118,2001378557180896,2001912540023366,2002624583216147,2003562754117260,
  2004784076776504,2006354886539708,2008350738957508,2010855730114670,2013961088290847,
  2017762913940021,2022358978952434,2027844548463539,2034307258786245,2041821170868379,
  2050440215065035,2060191342555845,2071067791899556,2083022955051787,2095965374360951,
  2109755410244900,2124204080499808,2139074482394488,2154086068728296,2168921865406001,
  2183238503030608]
private def pvn_w1_0_p2 : List ℕ := [2196678705756909,2208885657963055,2219518475457803,
  2228267864240816,2234870973997743,2239124457355785,2240894833583992,2240125422438245,
  2236839347293795,2231138386355329,2223197751186315,2213257165282591,2201608874898972,
  2188583426557774,2174534173664361,2159821519487376,2144797865214559,2129794118003084,
  2115108440039695,2100997705642542,2087671901768931,2075291480083125,2063967465523741,
  2053763962195510,2044702581956409,2036768257947386,2029915892670514,2024077321655250,
  2019168139635847,2015094025154801,2011756300010899,2009056561374170,2006900317979635,
  2005199641301630,2003874904303461,2002855722981772,2002081240245520,2001499899950740,
  2001068854348581,2000753134373738,2000524692618437,2000361406620006,2000246107754865,
  2000165680410939,2000110258363004,2000072530967601,2000047161018020,2000030308609003,
  2000019250697133,2000012083649639,2000007495379829,2000004594145161,1999997217712407,
  1999998335226229,1999999015914289,1999999425351057,1999999668540372,1999999811165149,
  1999999893751934,1999999940964951,1999999967610061,1999999982453874,1999999990616137,
  1999999995045865]
private def pvn_w1_0_p3 : List ℕ := [1999999997418369,1999999998672267,2000000000673854,
  2000000000337444,2000000000166704,1999999999918773,2000000000039023,2000000000018475,
  2000000000008613,2000000000003950,2000000000001775,2000000000000780,2000000000000332,
  2000000000000134,2000000000000049,2000000000000016,2000000000000004]
private def pvn_w1_0 : List ℕ := pCat pvn_w1_0_p0 (pCat pvn_w1_0_p1 (pCat pvn_w1_0_p2
  pvn_w1_0_p3))
private def pvn_w1_1_p0 : List ℕ := [2000000000000001,2000000000000009,1999999999999995,
  1999999999999994,1999999999999997,2000000000000000,2000000000000000,1999999999999995,
  2000000000000000,2000000000000002,2000000000000000,1999999999999997,1999999999999989,
  1999999999999992,1999999999999995,1999999999999991,2000000000000002,2000000000000012,
  2000000000000009,1999999999999997,1999999999999989,1999999999999996,2000000000000002,
  2000000000000001,2000000000000006,2000000000000001,1999999999999991,1999999999999997,
  2000000000000012,2000000000000007,1999999999999997,1999999999999995,1999999999999985,
  1999999999999995,2000000000000008,1999999999999998,2000000000000001,2000000000000008,
  2000000000000004,1999999999999996,1999999999999997,2000000000000016,2000000000000015,
  2000000000000001,2000000000000000,1999999999999998,1999999999999998,2000000000000007,
  2000000000000020,1999999999999974,2000000000000114,1999999999999695,2000000000000961,
  1999999999997348,2000000000006823,1999999999983662,2000000000036102,1999999999927454,
  2000000000129747,1999999999804186,2000000000211958,1999999999988627,1999999999220766,
  2000000002864450]
private def pvn_w1_1_p1 : List ℕ := [1999999992644771,2000000015592552,1999999971639230,
  2000000044207834,1999999942615466,2000000057657912,1999999964492658,1999999993328622,
  2000000045916853,1999999951054851,2000000005846968,2000000043784880,1999999959077633,
  1999999984163339,2000000048881420,1999999994859974,1999999953942636,2000000013224772,
  2000000043746543,1999999989988575,1999999956345805,1999999996461665,2000000039474838,
  2000000023816000,1999999979060347,1999999964365821,1999999991056999,2000000024132932,
  2000000030310905,2000000006840111,1999999973661572,1999999951922823,1999999951579508,
  1999999972470812,2000000011828608,2000000071314494,2000000161474695,2000000305044159,
  2000000541546536,2000000935361113,2000001589154297,2000002664835324,2000004414990884,
  2000007228935122,2000011698976399,2000018714204460,2000029591000229,2000046251478126,
  2000071463020064,2000109153677687,2000164819113974,2000246036411770,2000363097865469,
  2000529773087562,2000764199680552,2001089890709532,2001536830845196,2002142612295949,
  2002953537043288,2004025584704082,2005425117699515,2007229170364452,2009525150078625,
  2012409770953310]
private def pvn_w1_1_p2 : List ℕ := [2015987048783743,2020365214221433,2025652452668965,
  2031951455588089,2039352867404384,2047927830387401,2057719958632306,2068737200020496,
  2080944157550856,2094255523023379,2108531311350328,2123574559795356,2139132064803292,
  2154898567906898,2170524577491265,2185627739342364,2199807368049268,2212661451600377,
  2223805174197975,2232889798251219,2239620632167031,2243772804356771,2245203673270632,
  2243860923148294,2239785707747626,2233110581058095,2224052357806891,2212900439539194,
  2200001478542951,2185741521053314,2170526883554028,2154765154185632,2138847339958983,
  2123132742180698,2107936053299441,2093520110156614,2080088141621380,2067788043143177,
  2056704787953440,2046880482103921,2038299347915830,2030922503682746,2024669309399756,
  2019446152288350,2015147977715277,2011656378751887,2008861824595889,2006657528450930,
  2004939231915630,2003619127193169,2002621106096514,2001874780050682,2001322736492970,
  2000921918188170,2000636018371897,2000433258411851,2000290025256661,2000191015342581,
  2000125020942936,2000081994206694,2000053451490849,2000033724934067,2000019883239054,
  2000010548698099]
private def pvn_w1_1_p3 : List ℕ := [2000004787482911,2000001650443345,2000000204995618,
  1999999694739894,1999999616245391,1999999690768979,1999999790634965,1999999871122427,
  1999999925110899,1999999958205781,1999999977586965,1999999988583358,1999999994569016,
  1999999997630778,1999999999072975,1999999999687786,1999999999920010,1999999999994138,
  2000000000010996,2000000000010678,2000000000007041,2000000000003958,2000000000002019,
  2000000000000955,2000000000000422,2000000000000173,2000000000000065,2000000000000021,
  2000000000000004]
private def pvn_w1_1 : List ℕ := pCat pvn_w1_1_p0 (pCat pvn_w1_1_p1 (pCat pvn_w1_1_p2
  pvn_w1_1_p3))
private def pvn_w1_2_p0 : List ℕ := [2000000000000001,2000000000000009,2000000000000007,
  2000000000000005,2000000000000000,1999999999999995,1999999999999993,2000000000000003,
  2000000000000000,1999999999999998,2000000000000001,1999999999999994,1999999999999994,
  2000000000000006,2000000000000006,2000000000000001,1999999999999998,1999999999999994,
  1999999999999997,1999999999999996,1999999999999986,1999999999999980,1999999999999991,
  2000000000000010,2000000000000003,2000000000000003,2000000000000012,1999999999999992,
  1999999999999985,2000000000000001,2000000000000000,2000000000000006,2000000000000007,
  1999999999999992,2000000000000004,1999999999999942,2000000000000155,1999999999999627,
  2000000000000968,1999999999997729,2000000000004934,1999999999990125,2000000000017756,
  1999999999972798,2000000000029661,2000000000001405,1999999999868222,2000000000500904,
  1999999998632554,2000000003150565,1999999993573300,2000000011813129,1999999980341381,
  2000000029511362,1999999960505324,2000000045994750,1999999955691325,2000000030791946,
  1999999993807214,1999999978293164,2000000039292139,1999999965700714,2000000006508420,
  2000000026600229]
private def pvn_w1_2_p1 : List ℕ := [1999999961346204,2000000016651596,2000000021555673,
  1999999962064776,2000000012734275,2000000027443466,1999999966232482,1999999996089875,
  2000000036112078,1999999983658828,1999999972231456,2000000028058201,2000000017270901,
  1999999967166778,1999999990685861,2000000033888961,2000000005472116,1999999966500230,
  1999999994108049,2000000032335919,2000000010252149,1999999970466858,1999999982292768,
  2000000023079117,2000000026035824,1999999989091245,1999999969309725,1999999993362889,
  2000000025473469,2000000023560801,1999999992834131,1999999971915596,1999999983270441,
  2000000011692130,2000000026766703,2000000015425587,1999999990714009,1999999975270187,
  1999999980803999,2000000001341351,2000000021208479,2000000027430937,2000000016845507,
  1999999995335130,1999999972491792,1999999956360525,1999999950956649,1999999956702588,
  1999999972535121,1999999998396487,2000000037515401,2000000098650652,2000000199003953,
  2000000368830055,2000000659047877,2000001153557455,2000001988613254,2000003382561960,
  2000005680567091,2000009420640505,2000015429395226,2000024958397505,2000039874735953,
  2000062922247312]
private def pvn_w1_2_p2 : List ℕ := [2000098072407621,2000150985709689,2000229604706926,
  2000344897923597,2000511768469619,2000750131357000,2001086148121540,2001553585752397,
  2002195238610059,2003064318374475,2004225677717640,2005756696984555,2007747620128311,
  2010301117409317,2013530800502666,2017558525700036,2022510149351176,2028509945074476,
  2035673031048976,2044097280088717,2053852510073273,2064972153387084,2077439809472382,
  2091185533983929,2106070269632998,2121893621206920,2138376839598501,2155186993874320,
  2171922519748935,2188149185846229,2203399446396327,2217203424661775,2229113378704664,
  2238716822806069,2245675090093330,2249730926446172,2250726916474865,2248623121952528,
  2243487536003157,2235500151369646,2224945078285544,2212183958339702,2197643035993876,
  2181791352561342,2165107121051742,2148059480146970,2131091012123079,2114592242534828,
  2098889934927013,2084245473458682,2070847607045206,2058810212903742,2048182991826171,
  2038961768974177,2031093673922087,2024487265985672,2019028025351938,2014589329519038,
  2011037545310263,2008238196024755,2006064503243766,2004402911160652,2003153412895367,
  2002228341803161]
private def pvn_w1_2_p3 : List ℕ := [2001552857502839,2001066136303511,2000720821763291,
  2000480423012590,2000316373808841,2000206205535938,2000132820039110,2000084008335396,
  2000051614997029,2000030388043246,2000016881891580,2000008689241906,2000004034054163,
  2000001601101791,2000000460609297,2000000004423705,1999999870762791,1999999866345588,
  1999999900086051,1999999935647971,1999999962317694,1999999979493466,1999999989533177,
  1999999994976002,1999999997735753,1999999999046938,1999999999629316,1999999999869589,
  1999999999960483,1999999999991162,1999999999999785,2000000000001329,2000000000001074,
  2000000000000612,2000000000000292,2000000000000123,2000000000000045,2000000000000014,
  2000000000000002]
private def pvn_w1_2 : List ℕ := pCat pvn_w1_2_p0 (pCat pvn_w1_2_p1 (pCat pvn_w1_2_p2
  pvn_w1_2_p3))
private def pvn_w1_3_p0 : List ℕ := [2000000000000001,2000000000000009,2000000000000007,
  2000000000000006,2000000000000004,2000000000000007,2000000000000012,1999999999999998,
  1999999999999996,1999999999999999,1999999999999998,1999999999999990,2000000000000000,
  2000000000000006,2000000000000004,1999999999999997,1999999999999991,1999999999999993,
  1999999999999998,2000000000000002,2000000000000010,2000000000000002,2000000000000005,
  1999999999999938,2000000000000163,1999999999999630,2000000000000831,1999999999998328,
  2000000000002828,1999999999996440,2000000000000505,2000000000015840,1999999999930475,
  2000000000213310,1999999999448505,2000000001269403,1999999997340048,2000000005124943,
  1999999990887871,2000000014942759,1999999977493330,2000000030873897,1999999961999354,
  2000000040842487,1999999963791064,2000000022442190,1999999998597903,1999999979496120,
  2000000033792916,1999999969490820,2000000010262573,2000000016523866,1999999967411816,
  2000000025240068,2000000001841212,1999999972340508,2000000029225411,1999999996593142,
  1999999974028136,2000000028550092,1999999999948425,1999999971366303,2000000023448228,
  2000000010684958]
private def pvn_w1_3_p1 : List ℕ := [1999999968824938,2000000010287516,2000000024708843,
  1999999975411496,1999999988491532,2000000030110910,1999999998086641,1999999970837134,
  2000000012272255,2000000025097684,1999999981079366,1999999979433911,2000000022512003,
  2000000017129678,1999999976033542,1999999984507799,2000000023929004,2000000015822634,
  1999999977420634,1999999982064925,2000000019641603,2000000021275386,1999999985459623,
  1999999975235611,2000000006749500,2000000026645688,2000000003599892,1999999975382927,
  1999999985081939,2000000016630113,2000000023600508,1999999997422809,1999999975346255,
  1999999986309524,2000000014508476,2000000023974331,2000000004393519,1999999980281580,
  1999999979055330,2000000000589941,2000000020784053,2000000019288473,1999999999077247,
  1999999980464918,1999999980144428,1999999997056802,2000000015861479,2000000021411472,
  2000000010380790,1999999991886999,1999999979197964,1999999980339226,1999999993982913,
  2000000011811281,2000000024213915,2000000025341303,2000000014889247,1999999997213369,
  1999999977977105,1999999963015103,1999999953872386,1999999954252810,1999999957345090,
  1999999974389211]
private def pvn_w1_3_p2 : List ℕ := [1999999982047060,2000000027408435,2000000035735364,
  2000000165795695,2000000191470710,2000000574911605,2000000714480267,2000001784854835,
  2000002428140379,2000005217242067,2000007665543997,2000014534895278,2000022479280892,
  2000038799149946,2000061314520953,2000099300413681,2000156209362041,2000242855543050,
  2000373858104232,2000564782513878,2000844907977075,2001244332252995,2001808375968536,
  2002593929663577,2003667728822833,2005118500330578,2007045897147030,2009567101254908,
  2012817925461924,2016940245518506,2022087040479313,2028411935915780,2036054238311608,
  2045137161306990,2055749256064380,2067927293371161,2081651186463969,2096826138656357,
  2113270350465565,2130717803506468,2148814409289751,2167120847604274,2185133476634456,
  2202303196140763,2218056051253932,2231828973506968,2243104463326283,2251436575176810,
  2256481097329218,2258023776223201,2255992032847204,2250457294828349,2241635111264962,
  2229873005777225,2215623511524260,2199414615595547,2181821392625129,2163432437452344,
  2144813873570706,2126481363142679,2108881694552313,2092378124008204,2077239588802977,
  2063639328094875]
private def pvn_w1_3_p3 : List ℕ := [2051663112080229,2041321014357579,2032559019727812,
  2025272139334940,2019320478389851,2014545568875083,2010783134581022,2007871530814163,
  2005657870868486,2004003370106506,2002787404420161,2001909081595754,2001286224877840,
  2000852946834862,2000557155002027,2000358567781262,2000227063755889,2000140998510781,
  2000085374691644,2000050037496946,2000028144243357,2000015044776637,2000007553603204,
  2000003502844208,2000001456830546,2000000507817202,2000000115732677,1999999981583043,
  1999999953030117,1999999959784090,1999999973413128,1999999984675017,1999999991972301,
  1999999996109164,1999999998241035,1999999999256366,1999999999706443,1999999999892435,
  1999999999963874,1999999999989168,1999999999997274,1999999999999536,2000000000000025,
  2000000000000068,2000000000000036,2000000000000013,2000000000000002]
private def pvn_w1_3 : List ℕ := pCat pvn_w1_3_p0 (pCat pvn_w1_3_p1 (pCat pvn_w1_3_p2
  pvn_w1_3_p3))
private def pvn_w1_4_p0 : List ℕ := [2000000000000001,2000000000000009,2000000000000007,
  2000000000000006,2000000000000009,2000000000000006,2000000000000001,1999999999999999,
  2000000000000010,2000000000000013,2000000000000004,1999999999999998,2000000000000016,
  1999999999999968,2000000000000094,1999999999999814,2000000000000197,2000000000000320,
  1999999999996852,2000000000013281,1999999999956399,2000000000123864,1999999999683819,
  2000000000738148,1999999998409966,2000000003173661,1999999994122455,2000000010089280,
  1999999984000375,2000000023296755,1999999969167742,2000000036458758,1999999962673720,
  2000000030865664,1999999983628514,1999999996542926,2000000022170614,1999999968482078,
  2000000025710916,1999999993899832,1999999982780248,2000000029748218,1999999977988107,
  1999999998137069,2000000024428499,1999999972969011,2000000006223191,2000000020352350,
  1999999972328397,2000000007516289,2000000020501172,1999999973418078,2000000003054202,
  2000000024065217,1999999977424317,1999999993334136,2000000027511570,1999999987456952,
  1999999980779950,2000000024576045,2000000004690706,1999999972847371,2000000009468504,
  2000000022476771]
private def pvn_w1_4_p1 : List ℕ := [1999999980370897,1999999985845650,2000000025025591,
  2000000005221359,1999999973424028,2000000002515870,2000000025758268,1999999991657324,
  1999999976063858,2000000012222498,2000000022097415,1999999985592921,1999999979164577,
  2000000015173312,2000000020420755,1999999985313928,1999999979128231,2000000012956041,
  2000000021985261,1999999990131171,1999999976674874,2000000005280326,2000000024195545,
  2000000000816396,1999999976348010,1999999991943553,2000000020630191,2000000015449144,
  1999999985721244,1999999978765028,2000000004529952,2000000023080604,2000000007219263,
  1999999981139371,1999999982282550,2000000008078445,2000000022418617,2000000006583686,
  1999999982424783,1999999981187148,2000000003426334,2000000021130480,2000000013111742,
  1999999990384678,1999999978331033,1999999991953172,2000000011176231,2000000023351013,
  2000000001952253,1999999996023903,1999999964635369,2000000017426082,1999999969651702,
  2000000084484376,1999999912865234,2000000139182072,1999999774860785,2000000267019442,
  1999999626489898,2000000479282909,1999999466899360,2000000627350605,1999999364172875,
  2000000568999433]
private def pvn_w1_4_p2 : List ℕ := [1999999518313664,2000000247566351,1999999991039758,
  1999999769831978,2000000469918036,1999999499817328,2000000460514353,1999999779134676,
  1999999893085091,2000000333814031,1999999463066678,2000000360054109,1999999834108957,
  1999999737186232,2000000431122505,1999999547121497,2000000165720135,2000000257449506,
  1999999628738668,2000000596012781,2000000342614618,2000000421558214,2000001913225213,
  2000002425946444,2000004658744055,2000009177175647,2000014998185109,2000026464652565,
  2000045753340282,2000075571004525,2000125172150117,2000203750963692,2000324252745436,
  2000509905569588,2000789182895304,2001199941323446,2001797352428971,2002650504928932,
  2003845142345430,2005491823339859,2007722614376908,2010688520594581,2014563231074635,
  2019536287784599,2025800206091171,2033543386048287,2042936901852857,2054111166384292,
  2067137084752804,2082010544958473,2098630830334453,2116782762224127,2136132449553164,
  2156229005367927,2176510208104385,2196322939580742,2214958521601521,2231691878488664,
  2245823137373866,2256726211884078,2263897509330494,2266992946042643,2265851984980202,
  2260512248660016]
private def pvn_w1_4_p3 : List ℕ := [2251210747635082,2238365850520692,2222543401288173,
  2204415646848111,2184716534550417,2164193091252535,2143556860157858,2123443459061915,
  2104384861330066,2086792961707211,2070951991260783,2057020202680289,2045041763255953,
  2034966593571280,2026673236557200,2019990774942383,2014718609865859,2010644319234395,
  2007559152023199,2005269805016797,2003605503087532,2002420751367922,2001595171604839,
  2001031876066512,2000655199360556,2000408015896760,2000248694839362,2000147875111189,
  2000085385021226,2000047612504743,2000025477958190,2000012989137913,2000006254307532,
  2000002810685360,2000001156883007,2000000420524047,2000000123008825,2000000018625035,
  1999999990535502,1999999988069476,1999999991752610,1999999995393803,1999999997737906,
  1999999998991881,1999999999586615,1999999999843140,1999999999944880,1999999999982119,
  1999999999994687,1999999999998575,1999999999999661,1999999999999930,1999999999999989,
  1999999999999999]
private def pvn_w1_4 : List ℕ := pCat pvn_w1_4_p0 (pCat pvn_w1_4_p1 (pCat pvn_w1_4_p2
  pvn_w1_4_p3))
private def pvn_w1_5_p0 : List ℕ := [2000000000000001,2000000000000009,2000000000000007,
  2000000000000006,2000000000000009,2000000000000013,1999999999999959,2000000000000329,
  1999999999998478,2000000000006105,1999999999978895,2000000000065016,1999999999818895,
  2000000000460118,1999999998928129,2000000002296390,1999999995471623,2000000008211272,
  1999999986350670,2000000020679821,1999999971720433,2000000034326339,1999999964146597,
  2000000030082236,1999999983851533,1999999996785270,2000000021347144,1999999970133002,
  2000000023275713,1999999996326501,1999999981816386,2000000028104895,1999999981753853,
  1999999994709907,2000000024653402,1999999976550182,2000000001704480,2000000021623745,
  1999999975662106,2000000002908938,2000000021535695,1999999976922262,1999999999244132,
  2000000023755081,1999999980953881,1999999991478895,2000000025607603,1999999989650828,
  1999999981692006,2000000022720277,2000000003634202,1999999975047416,2000000011025820,
  2000000018768283,1999999979022470,1999999991815873,2000000024836966,1999999997012074,
  1999999976484691,2000000012301971,2000000018885231,1999999981224193,1999999987188170,
  2000000022475556]
private def pvn_w1_5_p1 : List ℕ := [2000000006686899,1999999975989485,1999999998660132,
  2000000024144395,1999999997144228,1999999976430695,2000000005817470,2000000022810173,
  1999999992395422,1999999977792630,2000000008312421,2000000021932844,1999999991988317,
  1999999977988446,2000000006726537,2000000022334935,1999999995555389,1999999977335857,
  2000000001154876,2000000022633092,2000000003082651,1999999978244595,1999999991933973,
  2000000019514187,2000000013274213,1999999984688328,1999999981875501,2000000009317952,
  2000000020692913,1999999999746429,1999999977453205,1999999994305084,2000000013348075,
  2000000022963777,1999999979127551,1999999998116537,1999999968516888,2000000065560369,
  1999999943161832,2000000090783141,1999999834381533,2000000200261582,1999999749491879,
  2000000360356315,1999999563587982,2000000484606401,1999999429697838,2000000605086834,
  1999999448823570,2000000488460162,1999999637766668,2000000133296711,2000000078938770,
  1999999732490815,2000000449607698,1999999510258457,2000000387262631,1999999776191446,
  1999999956010798,2000000313888519,1999999571652525,2000000421613769,1999999743709031,
  1999999938304260]
private def pvn_w1_5_p2 : List ℕ := [2000000313564295,1999999571208414,2000000375088597,
  1999999915357344,1999999768721111,2000000404269061,1999999603797824,2000000113718114,
  2000000235278279,1999999593235458,2000000364023167,1999999963851142,1999999681507438,
  2000000412064403,1999999743688316,1999999853854787,2000000421365128,1999999664910391,
  2000000026974242,2000000380422492,1999999601853599,2000000088944917,2000000293790706,
  1999999538274966,2000000092305920,2000000256070353,1999999522547466,2000000084956465,
  2000000293141503,1999999550019523,2000000049364613,2000000384526218,1999999641814892,
  2000000031331041,2000000644736507,2000000136199086,2000000672141083,2000002276809495,
  2000003459852416,2000006493297903,2000013390163961,2000024188081362,2000042979124461,
  2000077124089385,2000134005410241,2000226743048868,2000378173774944,2000618536976532,
  2000989695135907,2001553568012905,2002393548789971,2003615869568036,2005357532040822,
  2007790040331089,2011115060447093,2015561357629598,2021381061321683,2028834795578912,
  2038168810680806,2049592446105919,2063251871196927,2079195833292602,2097342634681912,
  2117457415691188]
private def pvn_w1_5_p3 : List ℕ := [2139137815215411,2161807910347216,2184729621788982,
  2207036745400476,2227785380198154,2246014226332605,2260814336152121,2271404742236049,
  2277201762239156,2277870198722118,2273352895290374,2263878584704905,2249945207596520,
  2232276753387396,2211759058185753,2189365661533069,2166083300267334,2142842492438362,
  2120457943216397,2099584953514306,2080696649506641,2064081903673745,2049859337101671,
  2038001872041178,2028367779875555,2020735146312187,2014836249645124,2010387935625304,
  2007115046981284,2004766042898629,2003121791950275,2001999250300479,2001251514548320,
  2000765275354444,2000456477789542,2000265012858495,2000149274304675,2000081252781073,
  2000042539267457,2000021307685892,2000010149837782,2000004564992000,2000001920547685,
  2000000745540891,2000000260888403,2000000078396760,2000000017564085,2000000000856358,
  1999999997968777,1999999998412600,1999999999164681,1999999999635866,1999999999860763,
  1999999999952269,1999999999985209,1999999999995852,1999999999998955,1999999999999767,
  1999999999999957,1999999999999995]
private def pvn_w1_5 : List ℕ := pCat pvn_w1_5_p0 (pCat pvn_w1_5_p1 (pCat pvn_w1_5_p2
  pvn_w1_5_p3))
private def pvn_w1_6_p0 : List ℕ := [1999999999999978,2000000000000225,1999999999998553,
  2000000000007281,1999999999970081,2000000000104935,1999999999679514,2000000000864398,
  1999999997923523,2000000004464271,1999999991397589,2000000014828748,1999999977274336,
  2000000030575022,1999999964767547,2000000032972415,1999999978497629,2000000002434470,
  2000000017540453,1999999971304743,2000000023800011,1999999995692798,1999999982047628,
  2000000027155870,1999999984572412,1999999991178531,2000000025380586,1999999981008286,
  1999999994742149,2000000024266266,1999999981482299,1999999993277306,2000000024578623,
  1999999985178278,1999999987982497,2000000024553575,1999999992791205,1999999980916259,
  2000000021009451,2000000004434634,1999999976059158,2000000010935374,2000000017172993,
  1999999978948658,1999999994747095,2000000023856797,1999999992925589,1999999979670321,
  2000000016606148,2000000012872461,1999999977967759,1999999996015893,2000000023494937,
  1999999995541206,1999999978075571,2000000011394012,2000000018479275,1999999983543442,
  1999999985798224,2000000019747534,2000000009870315,1999999978390663,1999999994016640,
  2000000022458587]
private def pvn_w1_6_p1 : List ℕ := [2000000002810401,1999999977315884,1999999999535956,
  2000000022596570,1999999998965438,1999999977590762,2000000001701085,2000000022247330,
  1999999998422820,1999999977888321,2000000000630507,2000000022059877,2000000000896016,
  1999999978465349,1999999996231614,2000000021825795,2000000005177106,1999999982225087,
  1999999986414394,2000000023993389,2000000003453451,2000000001758862,1999999957330956,
  2000000049257292,1999999960756100,2000000082009264,1999999857014311,2000000165975307,
  1999999793349610,2000000303105835,1999999617937645,2000000424229687,1999999503307963,
  2000000570127695,1999999437734597,2000000509701937,1999999548058884,2000000316713641,
  1999999897764375,1999999910446863,2000000254278220,1999999583463253,2000000475641896,
  1999999614335154,2000000233886338,1999999968189758,1999999773569447,2000000401005820,
  1999999589263569,2000000317226454,1999999886181918,1999999821956417,2000000375267478,
  1999999606350030,2000000283482597,1999999968065224,1999999729871776,2000000403137941,
  1999999667425238,2000000124590586,2000000187109855,1999999596670623,2000000347920964,
  1999999885009383]
private def pvn_w1_6_p2 : List ℕ := [1999999818995506,2000000405222054,1999999661689450,
  2000000036078884,2000000255308193,1999999597840084,2000000264869379,2000000104892055,
  1999999636231377,2000000349337704,1999999911919340,1999999713518955,2000000411258904,
  1999999827068495,1999999822240905,2000000407721314,1999999725750937,1999999858071735,
  2000000389919335,1999999705045074,1999999921693394,2000000415408000,1999999703393886,
  1999999898713375,2000000391912566,1999999690858956,1999999842200824,2000000418449728,
  1999999772180037,1999999801377578,2000000455858212,1999999880617002,1999999691463565,
  2000000399102043,1999999989802065,1999999555894538,2000000265029401,2000000156130361,
  1999999508678733,2000000072675142,2000000350317128,1999999611212865,1999999822260792,
  2000000455647362,1999999884137938,1999999613972276,2000000416623640,2000000420463607,
  1999999985612449,2000001045234145,2000002815485445,2000004800102260,2000010014771429,
  2000021373749379,2000041358843371,2000077687857833,2000144524075221,2000261019660930,
  2000456965425577,2000780903763064,2001303073874756,2002119765077198,2003363954544035,
  2005213465114853]
private def pvn_w1_6_p3 : List ℕ := [2007891850107841,2011668264718967,2016855979995260,
  2023799550908649,2032848427641996,2044323947018784,2058480595069072,2075457340444429,
  2095224266067261,2117537907425121,2141913073142053,2167612813370494,2193662504033267,
  2218896988111958,2242040808099879,2261810621724856,2277027523610932,2286729742744022,
  2290273323723701,2287403729653028,2278284679024908,2263481163945836,2243902040393138,
  2220710112055623,2195209317059874,2168723055005408,2142481144193875,2117530468911279,
  2094677080825585,2074460568579462,2057157855865911,2042811826490297,2031278064783496,
  2022280749899188,2015468262144496,2010461223336267,2006889305075378,2004416279542946,
  2002754496906498,2001670560751903,2000984173259968,2000562297359304,2000310832512092,
  2000165731265081,2000084907456732,2000041612909936,2000019412497598,2000008571559970,
  2000003558979783,2000001378439326,2000000492685429,2000000159906711,2000000045828238,
  2000000010922100,2000000001788380,1999999999961253,1999999999811611,1999999999901260,
  1999999999963807,1999999999989291,1999999999997356,1999999999999461,1999999999999913,
  1999999999999992]
private def pvn_w1_6 : List ℕ := pCat pvn_w1_6_p0 (pCat pvn_w1_6_p1 (pCat pvn_w1_6_p2
  pvn_w1_6_p3))
private def pvn_w1_7_p0 : List ℕ := [1999999999942301,2000000000323477,1999999998785065,
  2000000003512154,1999999991772973,2000000015952348,1999999974304785,2000000033887421,
  1999999965069625,2000000024290393,1999999996862128,1999999980826192,2000000028943275,
  1999999981837486,1999999993581929,2000000025235032,1999999978669132,1999999997423728,
  2000000023619427,1999999979989675,1999999994942796,2000000024229353,1999999984659378,
  1999999988349192,2000000024219371,1999999993583982,1999999980529010,2000000019696845,
  2000000006405092,1999999976377573,2000000007938994,2000000018885672,1999999981564751,
  1999999991061875,2000000022940023,1999999997632899,1999999978261132,2000000012137631,
  2000000016444428,1999999981153759,1999999990986486,2000000022146247,2000000001132678,
  1999999977541087,2000000006038868,2000000020566358,1999999988117895,1999999982686799,
  2000000016207639,2000000013434228,1999999980890069,1999999990516123,2000000020835017,
  2000000005832661,1999999978315706,1999999997307256,2000000021942587,2000000000179535,
  1999999978114195,2000000001732335,2000000021595889,1999999997162936,1999999978381447,
  2000000003937217]
private def pvn_w1_7_p1 : List ℕ := [2000000020589081,1999999997565730,1999999976782997,
  2000000006552728,2000000015372235,2000000007484781,1999999963693116,2000000024007708,
  1999999984914988,2000000055749249,1999999900841623,2000000106697598,1999999866626269,
  2000000212840601,1999999714999108,2000000323520800,1999999612136290,2000000482768844,
  1999999468693002,2000000524476429,1999999481523270,2000000486216465,1999999638924880,
  2000000183405274,1999999977538697,1999999852124257,2000000334209960,1999999560950996,
  2000000418209758,1999999667041806,2000000190219038,2000000040575105,1999999730097395,
  2000000380821614,1999999616005738,2000000300493196,1999999909581525,1999999821369675,
  2000000347275943,1999999624967920,2000000292748622,1999999923144487,1999999793226902,
  2000000371095839,1999999651560115,2000000198419773,2000000054409855,1999999683321371,
  2000000390822176,1999999762451296,1999999990154670,2000000258062593,1999999606976407,
  2000000269502937,2000000033478490,1999999719153275,2000000363243909,1999999760531693,
  1999999923781644,2000000347270959,1999999654419235,2000000123349057,2000000173035143,
  1999999618690162]
private def pvn_w1_7_p2 : List ℕ := [2000000293282980,2000000043134086,1999999684835220,
  2000000346509902,1999999871037048,1999999772804772,2000000398190648,1999999796296636,
  1999999861522098,2000000360642670,1999999703261190,1999999936673824,2000000371615251,
  1999999692225281,1999999982514144,2000000330342091,1999999645829853,1999999998231582,
  2000000353151063,1999999672516601,1999999998598002,2000000348175809,1999999653360305,
  1999999940797106,2000000380400926,1999999714378711,1999999899703231,2000000411758340,
  1999999758437490,1999999775634003,2000000399410860,1999999864770720,1999999695035134,
  2000000399674856,2000000034572966,1999999603615017,2000000276600837,2000000181372486,
  1999999548033402,2000000089667062,2000000366242364,1999999659856248,1999999882644587,
  2000000474130335,1999999880596133,1999999638547563,2000000357729008,2000000146936342,
  1999999506092056,2000000045413261,2000000385452629,1999999655658488,1999999680137142,
  2000000414814510,2000000058667243,1999999489763866,2000000109590569,2000000439163367,
  1999999690293988,1999999653709629,2000000464902266,2000000359608139,1999999991775741,
  2000001395779985]
private def pvn_w1_7_p3 : List ℕ := [2000004448846648,2000009674331801,2000022298791638,
  2000050897528714,2000107861063289,2000217162498155,2000422200468097,2000790773272288,
  2001425177623217,2002478791784675,2004169877460745,2006789192454600,2010705324866988,
  2016363499909587,2024265868872537,2034929272481809,2048825671081254,2066307592618448,
  2087519176053709,2112304246310923,2140133465949925,2170069526678053,2200780723238777,
  2230610493823692,2257707528020640,2280207784150447,2296442264900961,2305136445935448,
  2305570687053053,2297677222052302,2282055464656086,2259898787395149,2232844116713054,
  2202772577112779,2171596395399475,2141064205353409,2112609399556352,2087257660244286,
  2065599633784465,2047822791703305,2033786108572230,2023116327092206,2015306219051733,
  2009800832140480,2006063910792283,2003621743112168,2002085480280341,2001155744599143,
  2000614975182871,2000313220989656,2000152113757371,2000070115060375,2000030511347708,
  2000012458570393,2000004740106773,2000001666662645,2000000536149989,2000000155772148,
  2000000040152325,2000000008937710,2000000001639662,2000000000223978,2000000000015663,
  1999999999998372]
private def pvn_w1_7_p4 : List ℕ := [1999999999999428]
private def pvn_w1_7 : List ℕ := pCat pvn_w1_7_p0 (pCat pvn_w1_7_p1 (pCat pvn_w1_7_p2 (pCat
  pvn_w1_7_p3 pvn_w1_7_p4)))
private def pvn_w1_8_p0 : List ℕ := [1999999994598255,2000000016343935,1999999969610708,
  2000000037454490,1999999973350527,1999999999230193,2000000025751001,1999999974283079,
  1999999999697522,2000000024964561,1999999979980039,1999999991039880,2000000025882755,
  1999999991299920,1999999980228996,2000000020434371,2000000007735435,1999999975718527,
  2000000004895880,2000000021531985,1999999985127857,1999999985338107,2000000020900692,
  2000000006088134,1999999976973034,2000000002376138,2000000022000900,1999999990371317,
  1999999981192338,2000000015171596,2000000014385563,1999999981065681,1999999990508105,
  2000000021103199,2000000004666358,1999999978012265,1999999999752113,2000000021930059,
  1999999996414824,1999999978749609,2000000006768086,2000000020224362,1999999990683032,
  1999999980943802,2000000011257280,2000000017962172,1999999987232966,1999999983159690,
  2000000013493939,2000000016571858,1999999984995078,1999999985562534,2000000012374268,
  2000000019216519,1999999979249576,1999999994660491,1999999997807356,2000000041391027,
  1999999947707851,2000000041242818,1999999928833751,2000000135074746,1999999827537416,
  2000000196452506]
private def pvn_w1_8_p1 : List ℕ := [1999999733093608,2000000362247817,1999999582325556,
  2000000450895628,1999999490852452,2000000548627165,1999999493793551,2000000415622742,
  1999999677709674,2000000184111675,2000000020929409,1999999789025405,2000000327131890,
  1999999598729613,2000000426146159,1999999669925627,2000000129419555,2000000071507250,
  1999999763750258,2000000372108038,1999999594155832,2000000275037495,1999999941882566,
  1999999857794328,2000000308173019,1999999606118408,2000000305094063,1999999927338775,
  1999999842475427,2000000311164196,1999999632809615,2000000257216379,2000000006675883,
  1999999747378142,2000000348837432,1999999700511944,2000000113701400,2000000166813256,
  1999999639037106,2000000324112999,1999999879715543,1999999873951377,2000000327779166,
  1999999650723229,2000000124760716,2000000174658502,1999999665929946,2000000300400386,
  1999999909646389,1999999787201705,2000000376392311,1999999750746093,1999999963248472,
  2000000276157253,1999999652324714,2000000168306667,2000000170017054,1999999634387367,
  2000000260898166,2000000017554789,1999999716123461,2000000355223342,1999999882150174,
  1999999765861301]
private def pvn_w1_8_p2 : List ℕ := [2000000361997155,1999999807677708,1999999882024038,
  2000000355436411,1999999712624672,1999999932460415,2000000345645204,1999999703787812,
  2000000003751249,2000000306018291,1999999649175062,2000000031247577,2000000317736332,
  1999999666169907,2000000046132472,2000000289667723,1999999636964091,2000000041231972,
  2000000330758888,1999999667126163,2000000006254076,2000000325918517,1999999662267097,
  1999999957656749,2000000383651882,1999999725297478,1999999880229865,2000000383051436,
  1999999765785299,1999999784258656,2000000412328265,1999999897044310,1999999696121914,
  2000000363528282,2000000006747742,1999999596572219,2000000280107567,2000000197170651,
  1999999593484265,2000000129462373,2000000334532766,1999999620227157,1999999894158946,
  2000000426832550,1999999809343554,1999999708303640,2000000417248581,2000000066862899,
  1999999549874832,2000000192160751,2000000306714027,1999999582411668,1999999893062362,
  2000000478974367,1999999875773735,1999999626525816,2000000374570066,2000000241422061,
  1999999525126548,1999999968039014,2000000457349290,1999999763087053,1999999547351821,
  2000000332608590]
private def pvn_w1_8_p3 : List ℕ := [2000000238351110,1999999485858354,1999999870806897,
  2000000512428016,1999999919724867,1999999470605574,2000000217048598,2000000455130228,
  1999999595701206,1999999467617433,2000000192248804,2000000075409145,2000000169140273,
  2000004624707202,2000018853605475,2000054960235540,2000142690940670,2000339376205330,
  2000743858172681,2001521711365279,2002935735315751,2005370905655474,2009350661983473,
  2015539659136845,2024716078220203,2037697032623482,2055216596471106,2077768263422778,
  2105428384022243,2137688640661203,2173342768439842,2210475256862243,2246579775632206,
  2278806492515555,2304311865854798,2320659516811579,2326197327844088,2320328415486570,
  2303613730597827,2277684518229301,2244985584252786,2208403390854278,2170853520021441,
  2134907455733052,2102524859666604,2074926334296073,2052604347871076,2035440509786218,
  2022883234419072,2014139981706127,2008347655694328,2004698670908290,2002515104426737,
  2001276034018010,2000610999963043,2000274631973231,2000115100332977,2000044608584280,
  2000015823974793,2000005071388843,2000001443575809,2000000356376311,2000000073575937,
  2000000011913123]
private def pvn_w1_8_p4 : List ℕ := [2000000001300222]
private def pvn_w1_8 : List ℕ := pCat pvn_w1_8_p0 (pCat pvn_w1_8_p1 (pCat pvn_w1_8_p2 (pCat
  pvn_w1_8_p3 pvn_w1_8_p4)))
private def pvn_w1_9_p0 : List ℕ := [1999999959992247,2000000030950601,2000000012742762,
  1999999968831398,1999999999464376,2000000028628411,1999999993055490,1999999974604788,
  2000000011858958,2000000022132635,1999999984846008,1999999980891864,2000000017363068,
  2000000016432483,1999999981175914,1999999985855312,2000000019763971,2000000012249067,
  1999999979660507,1999999989266731,2000000020659754,2000000009577700,1999999979200200,
  1999999991239622,2000000020809390,2000000008259604,1999999979280886,1999999991945996,
  2000000020542327,2000000008127921,1999999979709866,1999999991556784,2000000019912702,
  2000000009069831,1999999980422070,1999999990386548,2000000018523103,2000000011478579,
  1999999980582963,1999999990344722,2000000013242406,2000000019938230,1999999972788911,
  2000000003516942,1999999986131364,2000000059590748,1999999922027559,2000000077092258,
  1999999877998720,2000000199657138,1999999752591796,2000000284807229,1999999632674668,
  2000000458454917,1999999506756514,2000000498725157,1999999486060434,2000000483939971,
  1999999638158424,2000000204601320,1999999940786331,1999999889128279,2000000298489842,
  1999999592063097]
private def pvn_w1_9_p1 : List ℕ := [2000000402987622,1999999661708572,2000000219713498,
  1999999986890764,1999999785279422,2000000346356745,1999999631894097,2000000315624392,
  1999999838273778,1999999915964297,2000000291229515,1999999640403822,2000000313283626,
  1999999824584145,1999999940832379,2000000291292766,1999999631242542,2000000275128298,
  1999999905866125,1999999870050265,2000000328949461,1999999640023614,2000000182974506,
  2000000065725771,1999999742346952,2000000343913717,1999999739958095,2000000000661207,
  2000000261589273,1999999656751604,2000000238141050,1999999978535847,1999999768925294,
  2000000364155931,1999999756839822,1999999961437733,2000000264594810,1999999673232368,
  2000000204064156,2000000074352078,1999999675204291,2000000325763152,1999999907451731,
  1999999824238731,2000000327328835,1999999729177533,1999999995083688,2000000296030026,
  1999999662286005,2000000120689208,2000000160535210,1999999667901110,2000000266103880,
  2000000037562789,1999999678474427,2000000315941537,1999999940982745,1999999775948634,
  2000000343848622,1999999816337768,1999999835421805,2000000366000999,1999999776178879,
  1999999905020220]
private def pvn_w1_9_p2 : List ℕ := [2000000321111896,1999999711479810,1999999984557173,
  2000000330787115,1999999681892226,2000000000957352,2000000291649647,1999999677959910,
  2000000061400135,2000000287801763,1999999642634152,2000000048762595,2000000291241402,
  1999999668437134,2000000063702216,2000000283740815,1999999639836939,2000000036231738,
  2000000325815665,1999999676530703,1999999998693470,2000000324309411,1999999675065831,
  1999999951404853,2000000381950065,1999999732389098,1999999867147917,2000000375125001,
  1999999780134237,1999999797659087,2000000410077810,1999999884728974,1999999692954026,
  2000000355797373,1999999993145769,1999999632819137,2000000314366714,2000000150460098,
  1999999578667365,2000000161488162,2000000277411853,1999999608977153,2000000014802282,
  2000000411251371,1999999711303107,1999999790457459,2000000418837764,1999999894503274,
  1999999634042839,2000000366041766,2000000158634934,1999999549219621,2000000129976418,
  2000000353861785,1999999615713638,1999999852250463,2000000482829771,1999999894733371,
  1999999605939672,2000000354907262,2000000204167003,1999999499763554,2000000014091118,
  2000000464309631]
private def pvn_w1_9_p3 : List ℕ := [1999999734443773,1999999671835149,2000000470359091,
  2000000169644185,1999999493998359,2000000082905160,2000000482679188,1999999682091883,
  1999999573974003,2000000410080553,2000000190506365,1999999420103040,1999999922812721,
  2000000547629328,1999999845048564,1999999436979078,2000000285848649,2000000493140654,
  1999999637362874,1999999738771068,2000000610528042,1999999820598521,1999997060210071,
  1999993436660180,1999989166971631,1999991072406476,2000029486609708,2000180716240528,
  2000603966994454,2001600851112005,2003685327341224,2007639831198128,2014534121449129,
  2025676527512522,2042459137912749,2066078511992292,2097162097278384,2135377483941168,
  2179130129394091,2225466035957796,2270276348628519,2308831334747347,2336564676896916,
  2349933685458228,2347139398269774,2328514092799763,2296464302355357,2254977565514142,
  2208826707723950,2162688328102916,2120397926241460,2084496765926952,2056121565978056,
  2035189668839123,2020767826815901,2011493091820269,2005935958482707,2002843620801981,
  2001253228721837,2000502559277237,2000180610845994,2000056909959258,2000015195655247,
  2000003234906942]
private def pvn_w1_9_p4 : List ℕ := [2000000474405846]
private def pvn_w1_9 : List ℕ := pCat pvn_w1_9_p0 (pCat pvn_w1_9_p1 (pCat pvn_w1_9_p2 (pCat
  pvn_w1_9_p3 pvn_w1_9_p4)))
private def pvn_w1_10_p0 : List ℕ := [1999999971033280,1999999960124662,1999999982025449,
  2000000018956549,2000000029183539,2000000000996941,1999999973390165,1999999984818874,
  2000000017704066,2000000022979655,1999999993357908,1999999974874593,1999999995956075,
  2000000022841214,2000000012867273,1999999982532150,1999999980939789,2000000010284143,
  2000000022355314,1999999997592615,1999999977142395,1999999994813460,2000000020791428,
  2000000011992067,1999999982894502,1999999983493387,2000000010384207,2000000022283697,
  1999999991378696,1999999984512361,1999999987787370,2000000039187807,1999999978402827,
  2000000027223511,1999999916940913,2000000117826535,1999999870865651,2000000191097421,
  1999999714820974,2000000339942761,1999999613870507,2000000471628425,1999999468349551,
  2000000511932806,1999999533951011,2000000410340163,1999999724647967,2000000070963612,
  2000000108008332,1999999752224198,2000000379414458,1999999563372185,2000000350844587,
  1999999815766328,2000000009752813,2000000184067122,1999999641714584,2000000395920051,
  1999999718996328,2000000106414331,2000000089792436,1999999708338440,2000000388235674,
  1999999703331569]
private def pvn_w1_10_p1 : List ℕ := [2000000095455353,2000000109586044,1999999712293258,
  2000000370141745,1999999739853598,2000000011960192,2000000208253826,1999999679160184,
  2000000313015029,1999999854268291,1999999869654875,2000000324481582,1999999681630391,
  2000000165103820,2000000058606165,1999999718916767,2000000354114488,1999999810600618,
  1999999915931156,2000000275813119,1999999684164769,2000000189652593,2000000078425784,
  1999999684038084,2000000322664923,1999999885555108,1999999862768528,2000000304807866,
  1999999701864050,2000000071781820,2000000227198963,1999999656351036,2000000207477870,
  2000000046181759,1999999731359258,2000000327027937,1999999867192907,1999999815446215,
  2000000342234054,1999999771388437,1999999968991292,2000000267308430,1999999673890878,
  2000000117278012,2000000208644620,1999999652896205,2000000194349902,2000000088951273,
  1999999697850001,2000000294341160,1999999973275715,1999999714834615,2000000333143785,
  1999999910938264,1999999794692777,2000000330086960,1999999808652655,1999999863684537,
  2000000359106134,1999999764459377,1999999899369297,2000000321872513,1999999734633539,
  1999999981172072]
private def pvn_w1_10_p2 : List ℕ := [2000000312580000,1999999680697873,1999999999070583,
  2000000310282049,1999999692738838,2000000032485730,2000000272071202,1999999659947300,
  2000000062584898,2000000297275547,1999999659113100,2000000040923525,2000000277791710,
  1999999668228421,2000000062944147,2000000297842389,1999999647571974,2000000017001584,
  2000000321608923,1999999686177107,1999999998139633,2000000326959952,1999999676943466,
  1999999946996956,2000000377461652,1999999732194542,1999999878029218,2000000369895746,
  1999999767556391,1999999822814648,2000000408364353,1999999845964900,1999999722792440,
  2000000373008778,1999999941876455,1999999674683978,2000000354985865,2000000051953695,
  1999999590202027,2000000257858350,2000000191418469,1999999595193835,2000000152384768,
  2000000303988005,1999999596918637,1999999978206926,2000000412219256,1999999721290171,
  1999999815606541,2000000434464868,1999999858699184,1999999636083703,2000000387142255,
  2000000100947748,1999999560410765,2000000224259280,2000000293498904,1999999551045875,
  1999999974816684,2000000463877973,1999999739279500,1999999724814462,2000000461245865,
  1999999989246888]
private def pvn_w1_10_p3 : List ℕ := [1999999510450867,2000000275681816,2000000318113987,
  1999999542890093,1999999972450629,2000000517792023,1999999756703900,1999999593381765,
  2000000431218352,2000000143632539,1999999453753347,2000000127279728,2000000524374869,
  1999999666375721,1999999677689656,2000000533712513,2000000104198991,1999999387521324,
  2000000103177731,2000000509030383,1999999598150497,1999999540815331,2000000502016617,
  2000000223041120,1999999357748890,1999999933256456,2000000559079519,1999999650203917,
  1999999335770310,2000001197186045,2000003359000917,2000003982681405,1999999560491045,
  1999977284004624,1999919954202606,1999836767603146,1999827430483906,2000198223739972,
  2001637491724995,2005403324943971,2013420146775867,2028161406422289,2052215460111149,
  2087509364229655,2134323653823371,2190417299933327,2250673053095169,2307582370003653,
  2352626202046252,2378257721622453,2379889872898505,2357192747150459,2314208543841235,
  2258230717546455,2197860365260162,2140927358034606,2092941153424797,2056458791428766,
  2031371563653618,2015793357631595,2007106694126761,2002801309345192,2000936464210371,
  2000250183407175]
private def pvn_w1_10_p4 : List ℕ := [2000046216938625]
private def pvn_w1_10 : List ℕ := pCat pvn_w1_10_p0 (pCat pvn_w1_10_p1 (pCat pvn_w1_10_p2 (pCat
  pvn_w1_10_p3 pvn_w1_10_p4)))
private def pvn_w1_11_p0 : List ℕ := [1999999997880733,1999999992450699,1999999982604273,
  1999999970849879,1999999964176424,1999999970583186,1999999991569706,2000000016786396,
  2000000028624743,2000000016787807,1999999990574054,1999999974007518,1999999983543117,
  2000000009997113,2000000024807800,2000000012503501,1999999984591135,1999999978466609,
  1999999991761774,2000000027365531,2000000005448268,2000000017560205,1999999937674395,
  2000000053513906,1999999918626598,2000000164263859,1999999793280752,2000000252878632,
  1999999636554182,2000000445336844,1999999526840921,2000000522131634,1999999462883685,
  2000000440637021,1999999694082462,2000000165570807,2000000043531558,1999999739292831,
  2000000371032610,1999999599499363,2000000371504983,1999999787689385,1999999964401885,
  2000000229145010,1999999658913069,2000000382178450,1999999725733683,2000000029388079,
  2000000194665614,1999999680297476,2000000354883378,1999999755904923,1999999987193969,
  2000000248031411,1999999663521204,2000000297618495,1999999863615703,1999999870866358,
  2000000332881672,1999999671656730,2000000166813764,2000000050719145,1999999732299405,
  2000000358141740]
private def pvn_w1_11_p1 : List ℕ := [1999999786001567,1999999943363848,2000000258075394,
  1999999681085755,2000000222888991,2000000030056364,1999999713117367,2000000335327506,
  1999999834197077,1999999926076149,2000000272416456,1999999673112474,2000000148808225,
  2000000151942853,1999999676532909,2000000264690276,1999999942180934,1999999809159417,
  2000000338947280,1999999765133543,1999999938534903,2000000290048811,1999999705113527,
  2000000115391645,2000000147140383,1999999667486140,2000000259672328,2000000035084401,
  1999999717035074,2000000298410262,1999999887798858,1999999843204994,2000000334200337,
  1999999758521565,1999999930557555,2000000307436801,1999999718716337,2000000053585532,
  2000000212403663,1999999665833107,2000000174382258,2000000156879990,1999999658865206,
  2000000221456772,2000000061217418,1999999713063964,2000000295671445,1999999956856051,
  1999999727168283,2000000335023336,1999999912678415,1999999785980685,2000000322826952,
  1999999829100265,1999999856232409,2000000353233210,1999999775651174,1999999876842883,
  2000000334703204,1999999761407817,1999999945890696,2000000310772252,1999999702997041,
  1999999981548824]
private def pvn_w1_11_p2 : List ℕ := [2000000326335268,1999999699540947,1999999992893500,
  2000000288017224,1999999689420789,2000000044293690,2000000291776687,1999999656397152,
  2000000033482502,2000000298361794,1999999679521810,2000000045096158,2000000275666316,
  1999999655026634,2000000053072089,2000000312635079,1999999660400651,2000000013413667,
  2000000305854046,1999999678711810,2000000018185196,2000000328608355,1999999664534591,
  1999999963513644,2000000361320128,1999999712248150,1999999926356163,2000000359091750,
  1999999719630919,1999999880159538,2000000405112030,1999999775353156,1999999798346541,
  2000000389241784,1999999836532621,1999999757322870,2000000403372904,1999999902307098,
  1999999662879835,2000000369691163,2000000018598363,1999999629140572,2000000316761361,
  2000000102923032,1999999569674977,2000000241667226,2000000245856198,1999999574875546,
  2000000108838150,2000000327703193,1999999601732810,1999999982221063,2000000436582575,
  1999999693977874,1999999799064662,2000000447764982,1999999836583883,1999999670077199,
  2000000438478129,2000000025378038,1999999535130125,2000000298247104,2000000230927818,
  1999999525745971]
private def pvn_w1_11_p3 : List ℕ := [2000000128877536,2000000415483862,1999999579803007,
  1999999853711980,2000000502514518,1999999789148514,1999999644271267,2000000485127451,
  2000000061906752,1999999461776728,2000000261972570,2000000347811602,1999999494404612,
  1999999976903722,2000000567059299,1999999710253058,1999999608635328,2000000513029333,
  2000000056449680,1999999396876027,2000000263938338,2000000479278207,1999999503477071,
  1999999837052907,2000000652065319,1999999853415958,1999999399986960,2000000416783296,
  2000000343508651,1999999310693561,1999999853801937,2000000643604094,1999999801752966,
  1999999630109638,2000000816746730,1999999859642701,1999996457194810,1999995526226916,
  2000003146878720,2000026123150359,2000059067723625,2000045260896611,1999852771189066,
  1999351733143230,1998682892669161,1998764651666301,2001927161556971,2012286665616543,
  2035291800363479,2076051162359397,2136649077262626,2213451915203664,2295939977488901,
  2368342774945266,2414133809164822,2421799950282987,2389282382384442,2324873443550234,
  2244051780216192,2163790595022347,2097057994567020,2049854380988018,2021527667681960,
  2007376909837828]
private def pvn_w1_11_p4 : List ℕ := [2001738668391555]
private def pvn_w1_11 : List ℕ := pCat pvn_w1_11_p0 (pCat pvn_w1_11_p1 (pCat pvn_w1_11_p2 (pCat
  pvn_w1_11_p3 pvn_w1_11_p4)))
private def pvn_w1_12_p0 : List ℕ := [1999999999985937,1999999999916991,1999999999663356,
  1999999998939897,1999999997196510,1999999993824090,1999999987916618,1999999980576101,
  1999999970860635,1999999968637908,1999999962795819,1999999989635469,1999999977532213,
  2000000055510393,1999999962030379,2000000128451694,1999999835850093,2000000221214790,
  1999999646568548,2000000407144917,1999999514876597,2000000564580707,1999999487137931,
  2000000438996966,1999999685191326,2000000066377339,2000000148529385,1999999694318401,
  2000000438952312,1999999596006299,2000000219374657,1999999979010151,1999999789592238,
  2000000393711948,1999999630936096,2000000207600710,1999999998357816,1999999751542942,
  2000000390802073,1999999697057354,2000000101162754,2000000124434128,1999999666586273,
  2000000360649225,1999999840985508,1999999909223153,2000000275940747,1999999648619630,
  2000000211763231,2000000082867465,1999999708725136,2000000316313957,1999999807430026,
  1999999935088168,2000000312843348,1999999670789051,2000000126326228,2000000117371368,
  1999999702400192,2000000313809874,1999999909273738,1999999793074822,2000000326110211,
  1999999770589096]
private def pvn_w1_12_p1 : List ℕ := [2000000007990307,2000000244021790,1999999655682589,
  2000000165770058,2000000132197243,1999999699846503,2000000267555612,1999999934670472,
  1999999785099163,2000000346682472,1999999814585404,1999999891401997,2000000290183909,
  1999999727148970,2000000066388958,2000000222412695,1999999655833514,2000000165200208,
  2000000132934233,1999999700232679,2000000252615310,1999999980108902,1999999740272161,
  2000000332542498,1999999894438564,1999999804411447,2000000313025272,1999999803010163,
  1999999931581132,2000000307265153,1999999708927168,2000000001959288,2000000277121064,
  1999999699943018,2000000091240675,2000000183686585,1999999669372911,2000000193725664,
  2000000138795274,1999999660030013,2000000224208910,2000000066054876,1999999712075256,
  2000000284206302,1999999971297208,1999999719802892,2000000328752652,1999999937530255,
  1999999759935489,2000000316708010,1999999866791765,1999999826907813,2000000348875917,
  1999999805742413,1999999840540786,2000000347405866,1999999794804698,1999999896911456,
  2000000319085298,1999999737476510,1999999946355669,2000000339604474,1999999714486515,
  1999999952337968]
private def pvn_w1_12_p2 : List ℕ := [2000000313105669,1999999714630190,2000000006925624,
  2000000294855718,1999999669736886,2000000024403473,2000000312410686,1999999676585356,
  2000000025464857,2000000279385742,1999999670928137,2000000066078656,2000000287603080,
  1999999641449390,2000000049777684,2000000299819220,1999999664952403,2000000053488309,
  2000000278964063,1999999645015518,2000000063952688,2000000314652237,1999999642449710,
  2000000023656660,2000000315394606,1999999665451061,2000000027656583,2000000325940414,
  1999999644772331,1999999990789236,2000000367585714,1999999679240002,1999999946960295,
  2000000361462760,1999999690577401,1999999926142571,2000000403743237,1999999710078515,
  1999999848584005,2000000412933050,1999999770501617,1999999813755083,2000000417901385,
  1999999795843021,1999999740681217,2000000438068684,1999999886043524,1999999675530079,
  2000000399623461,1999999950721841,1999999629054515,2000000393199794,2000000050731869,
  1999999556623320,2000000315174760,2000000160547179,1999999548895676,2000000247447329,
  2000000256319650,1999999515549675,2000000128731811,2000000380274067,1999999568307481,
  1999999993885546]
private def pvn_w1_12_p3 : List ℕ := [2000000442852515,1999999618124993,1999999845481770,
  2000000521280395,1999999756506324,1999999682137199,2000000495836699,1999999902226633,
  1999999555786437,2000000460839391,2000000117390481,1999999455292126,2000000295015624,
  2000000301287256,1999999445152707,2000000119080295,2000000505590044,1999999525911080,
  1999999840846140,2000000579636942,1999999700773886,1999999605169719,2000000606685817,
  2000000005519204,1999999409721918,2000000424934956,2000000284714086,1999999317149574,
  2000000135506599,2000000593441431,1999999477781322,1999999795977822,2000000742891886,
  1999999756975736,1999999374609366,2000000630925281,2000000305278773,1999999237100936,
  1999999760014515,1999999601653441,1999999726094691,2000004752970648,2000007688207940,
  1999990819257248,1999953655153860,1999948755059066,2000085154997084,2000398247048090,
  2000541989639208,1999611651767815,1996781909679359,1993247935915988,1994832608902450,
  2013009309676447,2061509511420271,2147858486204828,2263765592510446,2381761779760112,
  2463608386571950,2478327971002504,2419413001432249,2309267942118886,2187041721782838,
  2087956575845797]
private def pvn_w1_12_p4 : List ℕ := [2027970041158227]
private def pvn_w1_12 : List ℕ := pCat pvn_w1_12_p0 (pCat pvn_w1_12_p1 (pCat pvn_w1_12_p2 (pCat
  pvn_w1_12_p3 pvn_w1_12_p4)))
private def pvn_w1_13_p0 : List ℕ := [1999999999971307,2000000000171263,1999999999288401,
  2000000002365157,1999999993309334,2000000016495744,1999999963559839,2000000071969338,
  1999999869564618,2000000211834261,1999999679452386,2000000426311658,1999999464893592,
  2000000555203895,1999999452060213,2000000355002880,1999999816134143,1999999850480737,
  2000000316131333,1999999543049508,2000000385558299,1999999857448602,1999999909925540,
  2000000362436661,1999999600274954,2000000249294292,1999999978077884,1999999713966601,
  2000000385479112,1999999733650204,2000000050348292,2000000254741825,1999999617916877,
  2000000244361205,1999999983274083,1999999744603811,2000000380675767,1999999795995003,
  1999999934270205,2000000278001923,1999999647946122,2000000146996704,2000000169818430,
  1999999682070612,2000000275732695,1999999946296622,1999999746436857,2000000349263093,
  1999999833365731,1999999908351383,2000000297269891,1999999687745257,2000000051029877,
  2000000245772830,1999999684181758,2000000176427883,2000000085119732,1999999677822350,
  2000000290029276,1999999997116444,1999999751640445,2000000302235160,1999999846420725,
  1999999857277540]
private def pvn_w1_13_p1 : List ℕ := [2000000344217478,1999999769544729,1999999936154075,
  2000000272611091,1999999713474192,2000000081735993,2000000226956913,1999999658641536,
  2000000141850483,2000000149133825,1999999699175502,2000000236317663,2000000031772617,
  1999999695195115,2000000297809882,1999999978892548,1999999758868346,2000000299299602,
  1999999866009416,1999999835639178,2000000343966398,1999999801416495,1999999875540586,
  2000000308589489,1999999763829800,1999999984201579,2000000278463051,1999999687828925,
  2000000042187928,2000000264160041,1999999690148852,2000000097986448,2000000180217344,
  1999999674707889,2000000190407908,2000000143873795,1999999654346495,2000000212714005,
  2000000093803832,1999999700488949,2000000262151495,2000000005958737,1999999702087544,
  2000000314529039,1999999978794155,1999999724941300,2000000305885613,1999999917639104,
  1999999787331710,2000000341055082,1999999849988054,1999999796373940,2000000354466270,
  1999999837111936,1999999843036834,2000000327877257,1999999779235007,1999999901427541,
  2000000350777024,1999999739116522,1999999910279143,2000000336020248,1999999737878274,
  1999999965526259]
private def pvn_w1_13_p2 : List ℕ := [2000000305445615,1999999688126328,2000000008342201,
  2000000321219022,1999999673572848,2000000014087409,2000000290175246,1999999676831045,
  2000000068642642,2000000267374634,1999999635317353,2000000090843200,2000000279696701,
  1999999640479991,2000000095142644,2000000242614710,1999999639538478,2000000143060361,
  2000000236145763,1999999606321292,2000000143886274,2000000245288666,1999999623747519,
  2000000151114236,2000000211878698,1999999611083616,2000000185852038,2000000226276454,
  1999999589224371,2000000168228967,2000000229697211,1999999609370236,2000000181880368,
  2000000211722222,1999999582572521,2000000193533814,2000000244944097,1999999578103006,
  2000000165476022,2000000241322240,1999999588373380,2000000181530135,2000000252615556,
  1999999556666789,2000000159308733,2000000292070444,1999999572625382,2000000133686980,
  2000000289899250,1999999562701110,2000000132120166,2000000336203985,1999999551565311,
  2000000077186273,2000000361710577,1999999576580857,2000000059009478,2000000384427076,
  1999999559530461,2000000008770831,2000000440418554,1999999594336425,1999999948162817,
  2000000449702157]
private def pvn_w1_13_p3 : List ℕ := [1999999608748213,1999999906598008,2000000505061211,
  1999999640173592,1999999813373334,2000000517827187,1999999700728527,1999999764115677,
  2000000544598305,1999999740995219,1999999660776756,2000000556414134,1999999844258758,
  1999999597566299,2000000539961938,1999999910101545,1999999502493720,2000000529208505,
  2000000049723710,1999999440984052,2000000459665540,2000000143388918,1999999370290078,
  2000000401641981,2000000310834609,1999999345758909,2000000274065577,2000000414159393,
  1999999315801694,2000000147325485,2000000585458659,1999999375271593,1999999979507586,
  2000000674347797,1999999412918711,1999999766869257,2000000745645712,1999999546360999,
  1999999713792731,2000000991405895,1999999415506200,1999998617056987,2000001442860443,
  2000003363737525,1999999755859542,1999987873321347,1999984971913588,2000032445397642,
  2000096667062673,1999987677353581,1999615051640974,1999523983385469,2000769226168610,
  2003022297849254,2002160664150690,1992379227111816,1976748389235379,1979440016294046,
  2041263318654433,2187063604085940,2384519667175545,2540030812994236,2556799445017153,
  2415787560367376]
private def pvn_w1_13_p4 : List ℕ := [2199686677302352]
private def pvn_w1_13 : List ℕ := pCat pvn_w1_13_p0 (pCat pvn_w1_13_p1 (pCat pvn_w1_13_p2 (pCat
  pvn_w1_13_p3 pvn_w1_13_p4)))
private def pvi_w1 : List ℤ := bDc bZ (rPad bZ 257 pvn_w1_0)
private def pvo_w1 : List ℤ := bDc bZ (rPad bZ 257 pvn_w1_13)
private abbrev dP_0 : Prop := rkmAllTrueF [
    bSlChk 10 257 phbn_w1 257 pvn_w1_6 257 pvn_w1_7
  ] = true
private theorem bk_0 : dP_0 := by decide +kernel
private abbrev dP_1 : Prop := rkmAllTrueF [
    bSlChk 10 257 phbn_w1 257 pvn_w1_7 257 pvn_w1_8
  ] = true
private theorem bk_1 : dP_1 := by decide +kernel
private abbrev dP_2 : Prop := rkmAllTrueF [
    bSlChk 10 257 phbn_w1 257 pvn_w1_8 257 pvn_w1_9
  ] = true
private theorem bk_2 : dP_2 := by decide +kernel
private abbrev dP_3 : Prop := rkmAllTrueF [
    bSlChk 10 257 phbn_w1 257 pvn_w1_9 257 pvn_w1_10
  ] = true
private theorem bk_3 : dP_3 := by decide +kernel
private abbrev dP_4 : Prop := rkmAllTrueF [
    bSlChk 10 257 phbn_w1 257 pvn_w1_10 257 pvn_w1_11
  ] = true
private theorem bk_4 : dP_4 := by decide +kernel
private abbrev dP_5 : Prop := rkmAllTrueF [
    bSlChk 10 257 phbn_w1 257 pvn_w1_11 257 pvn_w1_12
  ] = true
private theorem bk_5 : dP_5 := by decide +kernel
private abbrev dP_6 : Prop := rkmAllTrueF [
    bSlChk 10 257 phbn_w1 257 pvn_w1_12 257 pvn_w1_13
  ] = true
private theorem bk_6 : dP_6 := by decide +kernel
private abbrev dP_7 : Prop := rkmAllTrueF [
    bSlChk 10 257 phbn_w1 257 pvn_w1_4 257 pvn_w1_5
  ] = true
private theorem bk_7 : dP_7 := by decide +kernel
private abbrev dP_8 : Prop := rkmAllTrueF [
    bSlChk 10 257 phbn_w1 257 pvn_w1_3 257 pvn_w1_4
  ] = true
private theorem bk_8 : dP_8 := by decide +kernel
private abbrev dP_9 : Prop := rkmAllTrueF [
    bSlChk 11 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_1
  ] = true
private theorem bk_9 : dP_9 := by decide +kernel
private abbrev dP_10 : Prop := rkmAllTrueF [
    bSlChk 10 257 phbn_w1 257 pvn_w1_2 257 pvn_w1_3
  ] = true
private theorem bk_10 : dP_10 := by decide +kernel
private abbrev dP_11 : Prop := rkmAllTrueF [
    bSlChk 10 257 phbn_w1 257 pvn_w1_1 257 pvn_w1_2
  ] = true
private theorem bk_11 : dP_11 := by decide +kernel
private abbrev dP_12 : Prop := rkmAllTrueF [
    bSlChk 17 257 phbn_w0 257 pvn_w0_2 257 pvn_w0_3
  ] = true
private theorem bk_12 : dP_12 := by decide +kernel
private abbrev dP_13 : Prop := rkmAllTrueF [
    bSlChk 11 257 phbn_w0 257 pvn_w0_6 257 pvn_w0_7
  ] = true
private theorem bk_13 : dP_13 := by decide +kernel
private abbrev dP_14 : Prop := rkmAllTrueF [
    bSlChk 9 257 phbn_w1 257 pvn_w1_5 257 pvn_w1_6
  ] = true
private theorem bk_14 : dP_14 := by decide +kernel
private abbrev dP_15 : Prop := rkmAllTrueF [
    bSlChk 22 257 phbn_w0 257 pvn_w0_1 257 pvn_w0_2
  ] = true
private theorem bk_15 : dP_15 := by decide +kernel
private abbrev dP_16 : Prop := rkmAllTrueF [
    bSlChk 14 257 phbn_w0 257 pvn_w0_3 257 pvn_w0_4
  ] = true
private theorem bk_16 : dP_16 := by decide +kernel
private abbrev dP_17 : Prop := rkmAllTrueF [
    bSlChk 42 257 phbn_w0 1 pvn_w0_0 257 pvn_w0_1
  ] = true
private theorem bk_17 : dP_17 := by decide +kernel
private abbrev dP_18 : Prop := rkmAllTrueF [
    bSlChk 12 257 phbn_w0 257 pvn_w0_4 257 pvn_w0_5,
    muxIntListEq pvi_w0 rkmViHi_m512_r256_s0_c0,
    muxIntListEq phbv_w1 rkmHbHi_m512_r256_s1_c0,
    muxIntListEq pvo_w1 rkmVoHi_m512_r256_s1_c0
  ] = true
private theorem bk_18 : dP_18 := by decide +kernel
private abbrev dP_19 : Prop := rkmAllTrueF [
    bSlChk 11 257 phbn_w0 257 pvn_w0_5 257 pvn_w0_6,
    muxIntListEq phbv_w0 rkmHbHi_m512_r256_s0_c0,
    muxIntListEq pvo_w0 rkmVoHi_m512_r256_s0_c0,
    muxIntListEq pvi_w1 rkmViHi_m512_r256_s1_c0
  ] = true
private theorem bk_19 : dP_19 := by decide +kernel
private theorem pw_w0_1 : pWOk 64 257 phbn_w0 1 pvn_w0_0 257 pvn_w0_2 :=
  bCh 42 22 257 (bSlSnd (bH bk_17))
    (bH bk_15)
private theorem pw_w0_2 : pWOk 81 257 phbn_w0 1 pvn_w0_0 257 pvn_w0_3 :=
  bCh 64 17 257 pw_w0_1
    (bH bk_12)
private theorem pw_w0_3 : pWOk 95 257 phbn_w0 1 pvn_w0_0 257 pvn_w0_4 :=
  bCh 81 14 257 pw_w0_2
    (bH bk_16)
private theorem pw_w0_4 : pWOk 107 257 phbn_w0 1 pvn_w0_0 257 pvn_w0_5 :=
  bCh 95 12 257 pw_w0_3
    (bH bk_18)
private theorem pw_w0_5 : pWOk 118 257 phbn_w0 1 pvn_w0_0 257 pvn_w0_6 :=
  bCh 107 11 257 pw_w0_4
    (bH bk_19)
private theorem pw_w0_6 : pWOk 129 257 phbn_w0 1 pvn_w0_0 257 pvn_w0_7 :=
  bCh 118 11 257 pw_w0_5
    (bH bk_13)
private theorem pwalk_w0 : muxFastIterFullT16 129 257 phbv_w0 pvi_w0 = pvo_w0 :=
  pw_w0_6
/-- Certified `T_16` walk chunk `m512_r256_s0_c0`. -/
theorem rkmWalkChkHi_m512_r256_s0_c0 : muxFastIterFullT16 129 257
    rkmHbHi_m512_r256_s0_c0 rkmViHi_m512_r256_s0_c0 = rkmVoHi_m512_r256_s0_c0 :=
  bLift pwalk_w0 (bH (bT bk_19))
    (bH (bT bk_18))
    (bH (bT (bT bk_19)))
private theorem pw_w1_1 : pWOk 21 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_2 :=
  bCh 11 10 257 (bSlSnd (bH bk_9))
    (bH bk_11)
private theorem pw_w1_2 : pWOk 31 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_3 :=
  bCh 21 10 257 pw_w1_1
    (bH bk_10)
private theorem pw_w1_3 : pWOk 41 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_4 :=
  bCh 31 10 257 pw_w1_2
    (bH bk_8)
private theorem pw_w1_4 : pWOk 51 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_5 :=
  bCh 41 10 257 pw_w1_3
    (bH bk_7)
private theorem pw_w1_5 : pWOk 60 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_6 :=
  bCh 51 9 257 pw_w1_4
    (bH bk_14)
private theorem pw_w1_6 : pWOk 70 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_7 :=
  bCh 60 10 257 pw_w1_5
    (bH bk_0)
private theorem pw_w1_7 : pWOk 80 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_8 :=
  bCh 70 10 257 pw_w1_6
    (bH bk_1)
private theorem pw_w1_8 : pWOk 90 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_9 :=
  bCh 80 10 257 pw_w1_7
    (bH bk_2)
private theorem pw_w1_9 : pWOk 100 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_10 :=
  bCh 90 10 257 pw_w1_8
    (bH bk_3)
private theorem pw_w1_10 : pWOk 110 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_11 :=
  bCh 100 10 257 pw_w1_9
    (bH bk_4)
private theorem pw_w1_11 : pWOk 120 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_12 :=
  bCh 110 10 257 pw_w1_10
    (bH bk_5)
private theorem pw_w1_12 : pWOk 130 257 phbn_w1 257 pvn_w1_0 257 pvn_w1_13 :=
  bCh 120 10 257 pw_w1_11
    (bH bk_6)
private theorem pwalk_w1 : muxFastIterFullT16 130 257 phbv_w1 pvi_w1 = pvo_w1 :=
  pw_w1_12
/-- Certified `T_16` walk chunk `m512_r256_s1_c0`. -/
theorem rkmWalkChkHi_m512_r256_s1_c0 : muxFastIterFullT16 130 257
    rkmHbHi_m512_r256_s1_c0 rkmViHi_m512_r256_s1_c0 = rkmVoHi_m512_r256_s1_c0 :=
  bLift pwalk_w1 (bH (bT (bT bk_18)))
    (bH (bT (bT (bT bk_19))))
    (bH (bT (bT (bT bk_18))))
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi512T1`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi512T1 :
    rkmWalkChkHi_m512_r256_s0_c0 = rkmWalkChkHi_m512_r256_s0_c0 :=
  rfl
private theorem laneRoot_Hi512T1 : rkmFlipGapsHi512T1 = rkmFlipGapsHi512T1 :=
  (And.intro (Eq.refl rkmZigHi512T8) rfl).right
end
end QuantumComputation.Specs.DickeSol
