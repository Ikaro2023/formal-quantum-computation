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
import QuantumComputationDiscoveries.Algorithms.Grover.Solution.FindAllJohnsonRampKickMuxHi512T3

/-
# High-`m` Checkpointed Walk Part `4` (`FindAllJohnsonRampKickMuxHi512T4`)

Certifies `1` `T_16` checkpoint walk(s) (`29754` substep-coords).
-/

namespace QuantumComputation.Specs.DickeSol

@[expose] public section
/-- Quantized generator list for `m512_r512_s0_c1`. -/
def rkmHbHi_m512_r512_s0_c1 : List ℤ := altBuildHbFrom 512 512 83769689655 0 512
/-- Part 0 of `rkmViHi_m512_r512_s0_c1`. -/
def rkmViHi_m512_r512_s0_c1_p0 : List ℤ := let p := rkmP; [
  p 3432741364,p 17655272984,p 64079898934,p 189518204759,p 484435964816,p 1105327151791,
  p 2297613731212,p 4412761526084,p 7911646707288,p 13346405411144,p 21315648405512,
  p 32392933534914,p 47034859330127,p 65481520644908,p 87666562322847,p 113155195551839,
  p 141125607776344,p 170402550511038,p 199542868300713,p 226963311089557,p 251093232692577,
  p 270530367357037,p 284177615602128,p 291342508727317,p 291787752840310,p 285729435290568,
  p 273787438482878,p 256898932307880,p 236209610338379,p 212958322228732,p 188369230146218,
  p 163562278377968,p 139488496431934,p 116892318806258,p 96299382834397,p 78025582085654,
  p 62201656595285,p 48807213761617,p 37708562109047,p 28695799482930,p 21515922350375,
  p 15900058086479,p 11584087403210,p 8322819796184,p 5898481434867,p 4124594149881,
  p 2846418704030,p 1939070337421,p 1304253114025,p 866355237174,p 568439665854,p 368478239974,
  p 236026022147,p 149419327576,p 93503482364,p 57848930259,p 35389884548,p 21411465984,
  p 12813325649,p 7585566010,p 4443089606,p 2575202091,p 1477144452,p 838637710,p 471322472,
  p 262243734,p 144472284,p 78814127,p 42580415,p 22784878,p 12076965,p 6341400,p 3298902,
  p 1700394,p 868484,p 439583,p 220506,p 109630,p 54019,p 26381,p 12766,p 6121,p 2907,p 1364,p 630,
  p 285,p 124,p 50,p 18,p 5,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0]
/-- Part 1 of `rkmViHi_m512_r512_s0_c1`. -/
def rkmViHi_m512_r512_s0_c1_p1 : List ℤ := let p := rkmP; [
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
/-- Input orbital vector for `m512_r512_s0_c1`. -/
def rkmViHi_m512_r512_s0_c1 : List ℤ :=
  rkmViHi_m512_r512_s0_c1_p0 ++ (rkmViHi_m512_r512_s0_c1_p1)
/-- Part 0 of `rkmVoHi_m512_r512_s0_c1`. -/
def rkmVoHi_m512_r512_s0_c1_p0 : List ℤ := let p := rkmP; let n := rkmN; [
  p 7,p 6,n 0,p 1,p 12,p 3,p 5,p 7,p 10,p 7,p 12,p 19,p 18,p 27,p 33,p 67,p 147,p 381,p 958,p 2420,
  p 5950,p 14286,p 33467,p 76559,p 171065,p 373703,p 798679,p 1671200,p 3426010,p 6885323,
  p 13573515,p 26262228,p 49896054,p 93133598,p 170863721,p 308235478,p 546991021,p 955230799,
  p 1642191525,p 2780194813,p 4636641549,p 7619782292,p 12342970088,p 19713153237,p 31050413790,
  p 48246280251,p 73969172935,p 111925460014,p 167183954179,p 246569977515,p 359132076558,
  p 516679826304,p 734384743354,p 1031428090940,p 1431669445602,p 1964298687710,p 2664422234504,
  p 3573522799907,p 4739721957116,p 6217767725191,p 8068666834912,p 10358884750476,
  p 13159047214799,p 16542095915562,p 20580878095099,p 25345185030176,p 30898295877010,
  p 37293129078564,p 44568150179510,p 52743228626747,p 61815672701523,p 71756696874228,
  p 82508585758759,p 93982810507797,p 106059325255718,p 118587223010197,p 131386863934865,
  p 144253507774328,p 156962391392040,p 169275098425523,p 180946978054917,p 191735291082564,
  p 201407700618796,p 209750687131253,p 216577457142891,p 221734933000384,p 225109457079266,
  p 226630914447032,p 226275068240885,p 224064005141792,p 220064696691430,p 214385787893802,
  p 207172820088073,p 198602174058218,p 188874076913464,p 178205049490053,p 166820178997009,
  p 154945585451261,p 142801412975011,p 130595622498844,p 118518795981362,p 106740089486774,
  p 95404398841170,p 84630732083110,p 74511721646930,p 65114159193880,p 56480399074756,
  p 48630453225498,p 41564590453841,p 35266255273634,p 29705133734814,p 24840213729251,
  p 20622712516032,p 16998772252526,p 13911852922018,p 11304779355168,p 9121423621818,
  p 7308024949135,p 5814165966476,p 4593436341689,p 3603822933718,p 2807869857172,p 2172652909998,
  p 1669611310950,p 1274276302190,p 965931531322,p 727234803103,p 543825255951,p 403934641799,
  p 298016434256,p 218402131192,p 158990441645,p 114972076832,p 82590572837,p 58937898037,
  p 41782458840,p 29426422056,p 20588930036,p 14311709073,p 9883687175,p 6781479304,p 4622914468,
  p 3131129865,p 2107112740,p 1408910590,p 936042133,p 617917988,p 405318817,p 264180066,
  p 171098965,p 110114698,p 70420672,p 44752599,p 28262185,p 17736518,p 11061446,p 6855541,
  p 4222438,p 2584529,p 1572176,p 950442,p 571026,p 340955,p 202323,p 119315,p 69925,p 40720,
  p 23562,p 13544,p 7729,p 4378,p 2458,p 1364,p 747,p 400,p 207,p 102,p 46,p 18,p 5,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,p 0,
  p 0,p 0]
/-- Part 1 of `rkmVoHi_m512_r512_s0_c1`. -/
def rkmVoHi_m512_r512_s0_c1_p1 : List ℤ := let p := rkmP; [
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
/-- Output orbital vector for `m512_r512_s0_c1`. -/
def rkmVoHi_m512_r512_s0_c1 : List ℤ :=
  rkmVoHi_m512_r512_s0_c1_p0 ++ (rkmVoHi_m512_r512_s0_c1_p1)
end
public section
private abbrev fN {α} (x : ℕ) (k : ℕ → α) : α := HighDForce.withForcedNat x k
private abbrev fL {α β} (xs : List α) (k : List α → β) : β := HighDForce.withForcedList xs k
private theorem n1a (x : ℕ) : Nat.add 1 x = x + 1 := by rw [Nat.add_eq]; exact Nat.add_comm 1 x
private theorem ndiv (x y : ℕ) : Nat.div x y = x / y := rfl
private def uCN (x : ℕ) (xs : List ℕ) : List ℕ := match Nat.add 1 x with
  | 0 => xs | v + 1 => match xs with | [] => [v] | h :: t => v :: h :: t
private theorem uCNe (x : ℕ) (xs : List ℕ) : uCN x xs = x :: xs := by
  unfold uCN; rw [n1a]; cases xs <;> rfl
private def u2N : List ℤ → Option (List ℕ)
  | [] => some [] | Int.negSucc _ :: _ => none
  | Int.ofNat n :: xs => match u2N xs with | some ns => some (uCN n ns) | none => none
private def uON : List ℕ → List ℤ | [] => [] | n :: ns => Int.ofNat n :: uON ns
private theorem u2NS : ∀ (hb : List ℤ) (ns : List ℕ), u2N hb = some ns → hb = uON ns
  | [], ns, h => by injection h with h'; subst h'; rfl
  | Int.negSucc _ :: _, _, h => by dsimp only [u2N] at h; cases h
  | Int.ofNat n :: xs, ns, h => by
    dsimp only [u2N] at h; revert h; cases hxs : u2N xs with
    | none => intro h; dsimp only at h; cases h
    | some ms =>
      intro h; dsimp only at h; injection h with h'; subst h'; rw [uCNe, uON, u2NS xs ms hxs]
private def bCZ (x : ℤ) (xs : List ℤ) : List ℤ := match x with
  | Int.ofNat v => match xs with | [] => [Int.ofNat v] | h :: t => Int.ofNat v :: h :: t
  | Int.negSucc v => match xs with | [] => [Int.negSucc v] | h :: t => Int.negSucc v :: h :: t
private theorem bCZe (x : ℤ) (xs : List ℤ) : bCZ x xs = x :: xs := by cases x <;> cases xs <;> rfl
private theorem bONF (x : ℕ) : primOfNatForced x = Int.ofNat x := by
  simp [primOfNatForced, Nat.one_add]
private theorem bNSF (x : ℕ) : primNegSuccForced x = Int.negSucc x := by
  simp [primNegSuccForced, Nat.one_add]
private theorem bSE (u z : ℕ) : rkmForcedSubNatNat u z = (u : ℤ) - (z : ℤ) := by
  unfold rkmForcedSubNatNat; rw [bONF, Nat.sub_eq]; cases h : z - u with
  | zero => dsimp only; rw [Nat.sub_eq, Int.ofNat_eq_natCast]; omega
  | succ k => dsimp only; rw [Int.negSucc_eq]; omega
private def bDec (z : ℕ) : List ℕ → List ℤ
  | [] => [] | u :: us => bCZ (rkmForcedSubNatNat u z) (bDec z us)
private theorem bDN (z : ℕ) : bDec z [] = [] := rfl
private theorem bDC (z u : ℕ) (us : List ℕ) :
    bDec z (u :: us) = ((u : ℤ) - (z : ℤ)) :: bDec z us := by rw [bDec, bCZe, bSE]
private theorem bZ0 (z : ℕ) : ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [Int.ofNat_eq_natCast]; omega
private theorem bMul0 (z : ℕ) : muxRawIntMul (Int.ofNat 0) ((z : ℤ) - (z : ℤ)) = Int.ofNat 0 := by
  rw [bZ0]; rfl
private def bE1 (z : ℕ) : ℤ → Option ℕ
  | Int.ofNat n => some (Nat.add z n)
  | Int.negSucc k => match Nat.sub z (Nat.add k 1) with | 0 => none | w + 1 => some (Nat.add w 1)
private def bEnc (z : ℕ) : List ℤ → Option (List ℕ)
  | [] => some []
  | x :: xs => match bE1 z x with
    | none => none | some u => match bEnc z xs with | none => none | some us => some (uCN u us)
private theorem bE1S (z : ℕ) (x : ℤ) (u : ℕ) (h : bE1 z x = some u) : ((u : ℤ) - (z : ℤ)) = x := by
  cases x with
  | ofNat n =>
    unfold bE1 at h; injection h with h'; subst h'; rw [Nat.add_eq, Int.ofNat_eq_natCast]; omega
  | negSucc k =>
    unfold bE1 at h; simp only [Nat.sub_eq, Nat.add_eq] at h; revert h
    cases hz : z - (k + 1) with
    | zero => intro h; dsimp only at h; cases h
    | succ w => intro h; dsimp only at h; injection h with h'; subst h'; rw [Int.negSucc_eq]; omega
private theorem bES (z : ℕ) : ∀ (xs : List ℤ) (us : List ℕ), bEnc z xs = some us → bDec z us = xs
  | [], us, h => by injection h with h'; subst h'; rfl
  | x :: xs, us, h => by
    dsimp only [bEnc] at h; revert h; cases hx : bE1 z x with
    | none => intro h; dsimp only at h; cases h
    | some u =>
      dsimp only; cases hxs : bEnc z xs with
      | none => intro h; dsimp only at h; cases h
      | some ws =>
        intro h; dsimp only at h; injection h with h'; subst h'
        rw [uCNe, bDC, bE1S z x u hx, bES z xs ws hxs]
private def zTd (x : ℤ) (d : ℕ) : ℤ := match x with
  | Int.ofNat m => Int.ofNat (m / d) | Int.negSucc k => -(((k + 1) / d : ℕ) : ℤ)
private theorem bNg : ∀ (n : ℕ), muxRawNegOfNat n = -(n : ℤ)
  | 0 => by dsimp only [muxRawNegOfNat]; rw [Int.ofNat_eq_natCast]; omega
  | k + 1 => by dsimp only [muxRawNegOfNat]; rw [Int.negSucc_eq]; omega
private theorem bTD : ∀ (x : ℤ) (d : ℕ), muxRawIntTdivNat x d = zTd x d
  | Int.ofNat _, _ => rfl
  | Int.negSucc k, d => by dsimp only [muxRawIntTdivNat, zTd]; rw [bNg, ndiv, Nat.add_eq]
private theorem bSND (m n d : ℕ) : rkmUltraSubNatTdiv m n d = zTd ((m : ℤ) - (n : ℤ)) d := by
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, ndiv, Nat.add_eq]; cases h : n - m with
  | zero =>
    have hm : (m : ℤ) - (n : ℤ) = Int.ofNat (m - n) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm]; rfl
  | succ k =>
    dsimp only; have hm : (m : ℤ) - (n : ℤ) = Int.negSucc k := by rw [Int.negSucc_eq]; omega
    rw [hm]; dsimp only [zTd]; rw [bNg]
private theorem bSTD (a b : ℤ) (d : ℕ) : rkmUltraSubTdiv a b d = zTd (a - b) d := by
  cases a with
  | ofNat m => cases b with
    | ofNat n => exact bSND m n d
    | negSucc n =>
      have hm : Int.ofNat m - Int.negSucc n = Int.ofNat (m + (n + 1)) := by
        rw [Int.ofNat_eq_natCast, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
      rw [hm]; rfl
  | negSucc m => cases b with
    | ofNat n =>
      have hm : Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
      dsimp only [rkmUltraSubTdiv]; rw [hm]; dsimp only [zTd]
      rw [bNg, ndiv, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t : ℕ => -(((t / d : ℕ) : ℤ))) (by omega)
    | negSucc n =>
      dsimp only [rkmUltraSubTdiv]; rw [bSND, Nat.add_eq, Nat.add_eq]
      exact congrArg (fun t => zTd t d) (by simp only [Int.negSucc_eq]; omega)
private theorem bME : ∀ (a b : ℤ), muxRawIntMul a b = a * b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq]; simp only [Int.ofNat_eq_natCast]; push_cast; ring
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [bNg, Nat.mul_eq, Nat.add_eq]
    rw [Int.ofNat_eq_natCast, Int.negSucc_eq]; push_cast; ring
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [muxRawIntMul]; rw [bNg, Nat.mul_eq, Nat.add_eq]
    rw [Int.negSucc_eq, Int.ofNat_eq_natCast]; push_cast; ring
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [muxRawIntMul]; rw [Nat.mul_eq, Nat.add_eq, Nat.add_eq, Int.ofNat_eq_natCast]
    simp only [Int.negSucc_eq]; push_cast; ring
private theorem bFA : ∀ (a b : ℤ), rkmForcedIntAdd a b = a + b
  | Int.ofNat m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bONF, Nat.add_eq]; simp only [Int.ofNat_eq_natCast]; omega
  | Int.ofNat m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bSE, Nat.add_eq, Int.ofNat_eq_natCast, Int.negSucc_eq]; omega
  | Int.negSucc m, Int.ofNat n => by
    dsimp only [rkmForcedIntAdd]; rw [bSE, Nat.add_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega
  | Int.negSucc m, Int.negSucc n => by
    dsimp only [rkmForcedIntAdd]; rw [bNSF, Nat.add_eq, Nat.add_eq]; simp [Int.negSucc_eq]; omega
private theorem bAC (a b : ℤ) (xs : List ℤ) : rkmUltraAddCons a b xs = (a + b) :: xs := by
  unfold rkmUltraAddCons; rw [bFA]; cases a + b <;> cases xs <;> rfl
private def bSV (v P Q d : ℕ) : ℕ :=
  match Nat.sub Q P with
  | 0 => Nat.add v (Nat.div (Nat.sub P Q) d) | k + 1 => Nat.sub v (Nat.div (Nat.add k 1) d)
private theorem bSVE (z v P Q d : ℕ) (hv : 0 < bSV v P Q d) :
    ((bSV v P Q d : ℤ) - (z : ℤ)) = ((v : ℤ) - (z : ℤ)) + zTd ((P : ℤ) - (Q : ℤ)) d := by
  rw [← bSND]; unfold bSV at hv ⊢
  unfold rkmUltraSubNatTdiv; simp only [Nat.sub_eq, Nat.add_eq, ndiv] at hv ⊢
  revert hv; cases h : Q - P with
  | zero => intro _; dsimp only; rw [Int.ofNat_eq_natCast]; push_cast; ring
  | succ k => intro hv; dsimp only at hv ⊢; rw [bNg]; omega
private abbrev bCV (z d b0 c0 b v c1 : ℕ) : ℕ :=
  bSV v (Nat.add (Nat.mul b0 c0) (Nat.mul b z)) (Nat.add (Nat.mul b c1) (Nat.mul b0 z)) d
private theorem bCH (z d b0 c0 b v c1 : ℕ) {r : List ℕ} {tZ : List ℤ}
    (hv : 0 < bCV z d b0 c0 b v c1) (ht : bDec z r = tZ) :
    bDec z (uCN (bCV z d b0 c0 b v c1) r) = rkmUltraAddCons ((v : ℤ) - (z : ℤ))
      (rkmUltraSubTdiv (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (muxRawIntMul (Int.ofNat b) ((c1 : ℤ) - (z : ℤ))) d) tZ := by
  rw [uCNe, bDC, ht, bAC, bSTD, bME, bME]; refine congrArg (· :: tZ) ?_
  have hpq : ((Nat.add (Nat.mul b0 c0) (Nat.mul b z) : ℕ) : ℤ) -
      ((Nat.add (Nat.mul b c1) (Nat.mul b0 z) : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) - (Int.ofNat b) * ((c1 : ℤ) - (z : ℤ)) := by
    simp only [Nat.add_eq, Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  unfold bCV at hv ⊢; rw [bSVE z v _ _ d hv, hpq]
private theorem bCN (z d b0 c0 v : ℕ) {r : List ℕ} {tZ : List ℤ}
    (hv : 0 < bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) (ht : bDec z r = tZ) :
    bDec z (uCN (bSV v (Nat.mul b0 c0) (Nat.mul b0 z) d) r) = rkmUltraAddCons ((v : ℤ) - (z : ℤ))
      (muxRawIntTdivNat (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ))) d) tZ := by
  rw [uCNe, bDC, ht, bAC, bTD, bME]; refine congrArg (· :: tZ) ?_
  have hpq : ((Nat.mul b0 c0 : ℕ) : ℤ) - ((Nat.mul b0 z : ℕ) : ℤ) =
      (Int.ofNat b0) * ((c0 : ℤ) - (z : ℤ)) := by
    simp only [Nat.mul_eq, Int.ofNat_eq_natCast]; push_cast; ring
  rw [bSVE z v _ _ d hv, hpq]
private def bAP : List ℕ → Bool | [] => true | x :: xs => cond (Nat.ble x 0) false (bAP xs)
private theorem bAP_cons {x : ℕ} {xs : List ℕ} (h : bAP (x :: xs) = true) :
    0 < x ∧ bAP xs = true := by
  cases x with | zero => exact Bool.noConfusion h | succ k => exact ⟨Nat.succ_pos k, h⟩
private theorem bAPu {x : ℕ} {xs : List ℕ} (h : bAP (uCN x xs) = true) :
    0 < x ∧ bAP xs = true := by rw [uCNe] at h; exact bAP_cons h
private def bHO (z : ℕ) : List ℕ → ℕ | [] => z | x :: _ => x
private def bTN : List ℕ → List ℕ | [] => [] | _ :: xs => xs
private theorem bHOe (z : ℕ) : ∀ (cs : List ℕ),
    ((bHO z cs : ℤ) - (z : ℤ)) = (match bDec z cs with | cn :: _ => cn | [] => Int.ofNat 0)
  | [] => by unfold bHO; rw [bDN, bZ0] | c :: cs => by unfold bHO; rw [bDC]
private theorem bTNe (z : ℕ) : ∀ (xs : List ℕ),
    bDec z (bTN xs) = (match bDec z xs with | _ :: t => t | [] => [])
  | [] => rfl | x :: xs => by unfold bTN; rw [bDC]
private def bSl (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, b0, c0, bns, vs, cs => match bns with
    | [] => uCN (bSV (bHO z vs) (Nat.mul b0 c0) (Nat.mul b0 z) d)
        (bSl z d rem 0 z [] (bTN vs) (bTN cs))
    | b :: bR => match vs, cs with
      | v :: vT, c :: cT => uCN (bCV z d b0 c0 b v (bHO z cT)) (bSl z d rem b c bR vT cT)
      | v :: vT, [] => uCN (bCV z d b0 c0 b v z) (bSl z d rem b z bR vT [])
      | [], c :: cT => uCN (bCV z d b0 c0 b z (bHO z cT)) (bSl z d rem b c bR [] cT)
      | [], [] => uCN (bCV z d b0 c0 b z z) (bSl z d rem b z bR [] [])
private theorem bSlS (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bAP (bSl z d rem b0 c0 bns vs cs) = true → bDec z (bSl z d rem b0 c0 bns vs cs) =
      rkmUltraSlideLoopAux d rem (muxRawIntMul (Int.ofNat b0) ((c0 : ℤ) - (z : ℤ)))
        (uON bns) (bDec z vs) (bDec z cs)
  | 0, _, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs, h => by
    cases bns with
    | nil =>
      dsimp only [bSl, uON, rkmUltraSlideLoopAux] at h ⊢; have hp := bAPu h
      have hi := bSlS z d rem 0 z [] (bTN vs) (bTN cs) hp.2; rw [bMul0, uON, bTNe, bTNe] at hi
      have hc := bCN z d b0 c0 (bHO z vs) hp.1 hi; rw [bHOe z vs] at hc; exact hc
    | cons b bR => cases vs with
      | nil => cases cs with
        | nil =>
          dsimp only [bSl, uON] at h ⊢; rw [bDN]; dsimp only [rkmUltraSlideLoopAux]
          have hp := bAPu h; have hi := bSlS z d rem b z bR [] [] hp.2; rw [bZ0 z, bDN] at hi
          have hc := bCH z d b0 c0 b z z hp.1 hi; rw [bZ0 z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uON] at h ⊢; rw [bDN, bDC z c cT]; dsimp only [rkmUltraSlideLoopAux]
          have hp := bAPu h; have hi := bSlS z d rem b c bR [] cT hp.2; rw [bDN] at hi
          have hc := bCH z d b0 c0 b z (bHO z cT) hp.1 hi; rw [bHOe z cT, bZ0 z] at hc; exact hc
      | cons v vT => cases cs with
        | nil =>
          dsimp only [bSl, uON] at h ⊢; rw [bDC z v vT, bDN]; dsimp only [rkmUltraSlideLoopAux]
          have hp := bAPu h; have hi := bSlS z d rem b z bR vT [] hp.2; rw [bZ0 z, bDN] at hi
          have hc := bCH z d b0 c0 b v z hp.1 hi; rw [bZ0 z] at hc; exact hc
        | cons c cT =>
          dsimp only [bSl, uON] at h ⊢; rw [bDC z v vT, bDC z c cT]
          dsimp only [rkmUltraSlideLoopAux]; have hp := bAPu h
          have hi := bSlS z d rem b c bR vT cT hp.2
          have hc := bCH z d b0 c0 b v (bHO z cT) hp.1 hi; rw [bHOe z cT] at hc; exact hc
private def mkHbZ (z : ℕ) : List ℕ → List ℕ
  | [] => [] | b :: bs => uCN b (uCN (Nat.mul b z) (mkHbZ z bs))
private def bSlZ (z d : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _, _, _, _ => []
  | rem + 1, p0, q0, hbz, vs, cs => match hbz with
    | [] => uCN (bSV (bHO z vs) p0 q0 d) (bSlZ z d rem 0 0 [] (bTN vs) (bTN cs))
    | [_] => []
    | b :: bz :: bR => match vs, cs with
      | v :: vT, c :: cT =>
          uCN (bSV v (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
            (bSlZ z d rem (Nat.mul b c) bz bR vT cT)
      | v :: vT, [] => uCN (bSV v (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR vT [])
      | [], c :: cT =>
          uCN (bSV z (Nat.add p0 bz) (Nat.add (Nat.mul b (bHO z cT)) q0) d)
            (bSlZ z d rem (Nat.mul b c) bz bR [] cT)
      | [], [] => uCN (bSV z (Nat.add p0 bz) (Nat.add bz q0) d) (bSlZ z d rem bz bz bR [] [])
private theorem bSlZ_eq (z d : ℕ) : ∀ (rem b0 c0 : ℕ) (bns vs cs : List ℕ),
    bSlZ z d rem (Nat.mul b0 c0) (Nat.mul b0 z) (mkHbZ z bns) vs cs =
      bSl z d rem b0 c0 bns vs cs
  | 0, _, _, _, _, _ => rfl
  | rem + 1, b0, c0, bns, vs, cs => by
    cases bns with
    | nil =>
      have hrec := bSlZ_eq z d rem 0 z [] (bTN vs) (bTN cs)
      have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
      dsimp only [mkHbZ] at hrec; rw [hz0] at hrec; dsimp only [mkHbZ, bSlZ, bSl]; rw [hrec]
    | cons b bR =>
      dsimp only [mkHbZ]; rw [uCNe, uCNe]; cases vs with
      | nil => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR [] []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR [] cT]
      | cons v vT => cases cs with
        | nil => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b z bR vT []]
        | cons c cT => dsimp only [bSlZ, bSl, bCV]; rw [bSlZ_eq z d rem b c bR vT cT]
private def bStg (z dg mL cL : ℕ) (hbz v c : List ℕ) : Option (List ℕ) :=
  fN (rkmNextLen mL cL) fun nL => fN (Nat.mul dg wdScale) fun d =>
    fL (bSlZ z d nL 0 0 hbz v c) fun out => cond (bAP out) (some out) none
private theorem bSS (z dg mL cL : ℕ) (b v c out : List ℕ)
    (h : bStg z dg mL cL (mkHbZ z b) v c = some out) :
    bDec z out = rkmUltraHornerStage dg mL cL (uON b) (bDec z v) (bDec z c) := by
  have hsl := bSlZ_eq z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c
  have hz0 : Nat.mul 0 z = 0 := by rw [Nat.mul_eq]; omega
  rw [hz0] at hsl; unfold bStg at h; dsimp only [fN, fL] at h
  rw [rkmb_forceNat_eq, rkmb_forceNat_eq, rkmb_forceList_eq, hsl] at h; revert h
  cases hp : bAP (bSl z (Nat.mul dg wdScale) (rkmNextLen mL cL) 0 z b v c) with
  | false => intro h; dsimp only [cond] at h; cases h
  | true =>
    intro h; injection h with h'; subst h'; unfold rkmUltraHornerStage
    rw [rkmb_forceNat_eq, rkmb_forceNat_eq, ← bMul0 z]; exact bSlS z _ _ 0 z b v c hp
private def bBd (z g m c : ℕ) (hbz v x : List ℕ) (k : ℕ → List ℕ → Option (List ℕ)) :
    Option (List ℕ) :=
  fN (rkmNextLen m c) fun n => match bStg z g m c hbz v x with | none => none | some o => k n o
private theorem bBS {z g m c : ℕ} {b v x out : List ℕ}
    {kB : ℕ → List ℕ → Option (List ℕ)} {kU : ℕ → List ℤ → List ℤ}
    (h : bBd z g m c (mkHbZ z b) v x kB = some out)
    (hk : ∀ m0, kB (rkmNextLen m c) m0 = some out → bDec z out = kU (rkmNextLen m c) (bDec z m0)) :
    bDec z out = (HighDForce.withForcedNat (rkmNextLen m c) fun nL =>
      HighDForce.withForcedList
        (rkmUltraHornerStage g m c (uON b) (bDec z v) (bDec z x)) (kU nL)) := by
  unfold bBd at h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; revert h
  cases hs : bStg z g m c (mkHbZ z b) v x with
  | none => intro h; dsimp only at h; cases h
  | some mid =>
    intro h; rw [rkmb_forceNat_eq, rkmb_forceList_eq, ← bSS z g m c b v x mid hs]; exact hk mid h
private def bSp (z m c : ℕ) (hbz v : List ℕ) : Option (List ℕ) :=
  bBd z 16 m c hbz v v fun l x => bBd z 15 m l hbz v x fun l x => bBd z 14 m l hbz v x fun l x =>
  bBd z 13 m l hbz v x fun l x => bBd z 12 m l hbz v x fun l x => bBd z 11 m l hbz v x fun l x =>
  bBd z 10 m l hbz v x fun l x => bBd z 9 m l hbz v x fun l x => bBd z 8 m l hbz v x fun l x =>
  bBd z 7 m l hbz v x fun l x => bBd z 6 m l hbz v x fun l x => bBd z 5 m l hbz v x fun l x =>
  bBd z 4 m l hbz v x fun l x => bBd z 3 m l hbz v x fun l x => bBd z 2 m l hbz v x fun l x =>
  bStg z 1 m l hbz v x
private theorem bSpS (z mL cL : ℕ) (b v out : List ℕ) (h : bSp z mL cL (mkHbZ z b) v = some out) :
    bDec z out = rkmUltraHornerT16Step mL cL (uON b) (bDec z v) := by
  unfold bSp at h; unfold rkmUltraHornerT16Step
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  refine bBS h fun _ h => bBS h fun _ h => bBS h fun _ h => ?_
  exact bSS z 1 mL _ b v _ out h
private def bIt (z : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, v => some v
  | k + 1, m, c, hbz, v => match bSp z m c hbz v with
    | none => none | some vN => fN (rkmNextLen16 m c) fun nL => bIt z k m nL hbz vN
private theorem bItS (z : ℕ) : ∀ (k m c : ℕ) (b v out : List ℕ),
    bIt z k m c (mkHbZ z b) v = some out →
      bDec z out = muxUltraIterFullT16Rkm k m c (uON b) (bDec z v)
  | 0, _, _, _, _, _, h => by injection h with h'; subst h'; rfl
  | k + 1, m, c, b, v, out, h => by
    unfold bIt at h; revert h; cases hs : bSp z m c (mkHbZ z b) v with
    | none => intro h; dsimp only at h; cases h
    | some vN =>
      intro h; dsimp only [fN] at h; rw [rkmb_forceNat_eq] at h; unfold muxUltraIterFullT16Rkm
      rw [rkmb_forceList_eq, rkmb_forceNat_eq, ← bSpS z m c b v vN hs]
      exact bItS z k m _ b vN out h
private def rkmZZ (w : ℕ) : ℤ := match Nat.ble (Nat.mod w 2) 0 with
  | true => Int.ofNat (Nat.div w 2) | false => Int.negSucc (Nat.div w 2)
private def rkmMapZZ : List ℕ → List ℤ | [] => [] | w :: ws => rkmZZ w :: rkmMapZZ ws
private def rkmNatZ : List ℕ → List ℤ | [] => [] | w :: ws => Int.ofNat w :: rkmNatZ ws
private def pzeros : ℕ → List ℤ | 0 => [] | k + 1 => Int.ofNat 0 :: pzeros k
private def pZZZ (z : ℕ) : List (List ℕ) → List ℤ
  | [] => pzeros z | xs :: xss => rkmMapZZ xs ++ pZZZ z xss
private def pNZCat : List (List ℕ) → List ℤ | [] => [] | xs :: xss => rkmNatZ xs ++ pNZCat xss
private def fIter (k mL cL : ℕ) (hb v : List ℤ) : List ℤ :=
  let z := 100000000000000000
  match u2N hb with
  | none => muxUltraIterFullT16Rkm k mL cL hb v
  | some b => match bEnc z v with
    | none => muxUltraIterFullT16Rkm k mL cL hb v
    | some vn => fL (mkHbZ z b) fun hbz => match bIt z k mL cL hbz vn with
      | none => muxUltraIterFullT16Rkm k mL cL hb v | some out => bDec z out
private theorem fIter_eq (k mL cL : ℕ) (hb v : List ℤ) :
    fIter k mL cL hb v = muxUltraIterFullT16Rkm k mL cL hb v := by
  unfold fIter; dsimp only [fL]; cases hh : u2N hb with
  | none => rfl
  | some b => dsimp only; cases hv : bEnc 100000000000000000 v with
    | none => rfl
    | some vn =>
      dsimp only; rw [rkmb_forceList_eq]
      cases hi : bIt 100000000000000000 k mL cL (mkHbZ 100000000000000000 b) vn with
      | none => rfl
      | some out => dsimp only; rw [bItS _ k mL cL b vn out hi, ← u2NS hb b hh, bES _ v vn hv]
private def pChk (steps maxLen : ℕ) (hb vecIn vecOut : List ℤ) : Bool :=
  fL hb fun hbF => fL vecIn fun inF => fL vecOut fun outF =>
    fN (altIntLen inF) fun len0 => muxIntListEq (fIter steps maxLen len0 hbF inF) outF
private theorem pCS {steps maxLen : ℕ} {hb vecIn vecOut : List ℤ}
    (h : pChk steps maxLen hb vecIn vecOut = true) :
    muxFastIterFullT16 steps maxLen hb vecIn = vecOut := by
  unfold pChk at h; dsimp only [fL, fN] at h
  rw [rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceList_eq, rkmb_forceNat_eq, fIter_eq] at h
  have h2 : muxUltraIterFullT16HiChk steps 0 maxLen hb vecIn vecOut = true := by
    unfold muxUltraIterFullT16HiChk; simp only [rkmb_forceList_eq, rkmb_forceNat_eq]; exact h
  exact muxUltraIterFullT16HiChk_sound h2
private theorem pChFull (k1 k2 mL : ℕ) {hb v0 v1 v2 : List ℤ}
    (h1 : muxFastIterFullT16 k1 mL hb v0 = v1) (h2 : pChk k2 mL hb v1 v2 = true) :
    muxFastIterFullT16 (k1 + k2) mL hb v0 = v2 :=
  (muxFastIterFullT16_add k1 k2 mL hb v0).trans
    ((congrArg (muxFastIterFullT16 k2 mL hb) h1).trans (pCS h2))
private def phbv_0 : List ℤ := pNZCat
  [
   [85780162206720,121074532312855,147995225789071,170555088137580,190311756051003,
    208065697503977,224293371426976,239305827076290,253319541516720,266492436304416,
    278943959907711,290767090667940,302035911380807,312810603129220,323140858498975,
    333068286068280,342628148443393,351850646740881,360761888397054,369384628870647,
    377738848686404,385842208447369,393710411978660,401357499327198,408796085516400,
    416037556861296,423092233726405,429969506490448,436677949926375,443225420048361,
    449619136607567,455865753757209,461971420900028,467941835338199,473782288038677,
    479497703585220,485092675196553,490571495536965,495938183922389,501196510425402,
    506350017301397,511402038091825,516355714705768,521214012735923,525979735227575,
    530655535087807,535243926295960,539747294054261,544167903998880,548507910575852,
    552769364672844,556954220586209,561064342392979,565101509788908,569067423446437,
    572963709940095,576791926281407,580553564100614,584250053508348,587882766666811,
    591453021096803,594962082744190,598411168826913,601801450481520,605134055226255,
    608410069256080,611630539583472,614796476037541,617908853132788,620968611817801,
    623976661113210,626933879647389,629841117097638,632699195543879,635508910741307,
    638271033317865,640986309901929,643655464185128,646279197924828,648858191890428,
    651393106757280,653884583951769,656333246450771,658739699538486,661104531523402,
    663428314417947,665711604583171,667954943340660,670158857553694,672323860179531,
    674450450794560,676539116093943,678590330367250,680604555951491,682582243662851,
    684523833208351,686429753578554,688300423422398,690136251405135,691937636550300,
    693704968566581,695438628160411,697138987335018,698806409676675,700441250628792,
    702043857754499,703614570988300,705153722877341,706661638812846,708138637252170,
    709585029931964,711001122072865,712387212576143,713743594212660,715070553804542,
    716368372399880,717637325440799,718877682925202,720089709562472,721273664923420,
    722429803584720,723558375268099,724659624974504,725733793113460,726781115627846,
    727801824114278,728796145939284,729764304351458],
   [730706518589765,731623003988143,732513972076582,733379630678794,734220184006649,
    735035832751474,735826774172366,736593202181632,737335307427468,738053277373981,
    738747296378674,739417545767476,740064203907422,740687446277072,741287445534748,
    741864371584680,742418391641136,742949670290614,743458369552160,743944648935890,
    744408665499779,744850573904770,745270526468289,745668673216186,746045161933196,
    746400138211941,746733745500548,747046125148916,747337416453680,747607756701933,
    747857281213719,748086123383371,748294414719709,748482284885148,748649861733751,
    748797271348252,748924638076106,749032084564568,749119731794854,749187699115413,
    749236104274320,749265063450842,749274691286190,749265100913476,749236403986924,
    749188710710327,749122129864802,749036768835847,748932733639725,748810128949196,
    748669058118626,748509623208473,748331925009184,748136063064517,747922135694301,
    747690240016653,747440471969672,747172926332614,746887696746578,746584875734709,
    746264554721921,745926824054184,745571773017349,745199489855561,744810061789235,
    744403575032646,743980114811108,743539765377780,743082610030087,742608731125793,
    742118210098705,741611127474047,741087562883485,740547595079843,739991301951484,
    739418760536402,738830047035993,738225236828551,737604404482470,736967623769171,
    736314967675753,735646508417395,734962317449485,734262465479507,733547022478688,
    732816057693397,732069639656320,731307836197411,730530714454613,729738340884376,
    728930781271955,728108100741512,727270363766015,726417634176941,725549975173792,
    724667449333424,723770118619200,722858044389954,721931287408800,720989907851759,
    720033965316230,719063518829293,718078626855865,717079347306693,716065737546206,
    715037854400216,713995754163476,712939492607104,711869124985861,710784706045309,
    709686290028825,708573930684500,707447681271904,706307594568733,705153722877341,
    703986118031150,702804831400948,701609913901076,700401415995506,699179387703815,
    697943878607050,696694937853493,695432614164331,694156955839219,692868010761756,
    691565826404864,690250449836072,688921927722720],
   [687580306337062,686225631561299,684857948892508,683477303447511,682083739967644,
    680677302823457,679258036019337,677825983198049,676381187645208,674923692293677,
    673453539727893,671970772188120,670475431574640,668967559451874,667447197052433,
    665914385281112,664369164718812,662811575626410,661241657948560,659659451317436,
    658064995056421,656458328183734,654839489416001,653208517171773,651565449574989,
    649910324458385,648243179366853,646564051560747,644872978019137,643169995443020,
    641455140258477,639728448619785,637989956412480,636239699256379,634477712508555,
    632704031266264,630918690369835,629121724405517,627313167708276,625493054364564,
    623661418215038,621818292857243,619963711648257,618097707707299,616220313918293,
    614331562932405,612431487170536,610520118825784,608597489865872,606663632035535,
    604718576858883,602762355641722,600794999473851,598816539231320,596827005578660,
    594826428971083,592814839656652,590792267678414,588758742876515,586714294890282,
    584658953160269,582592746930290,580515705249408,578427856973915,576329230769267,
    574219855112011,572099758291671,569968968412620,567827513395918,565675420981139,
    563512718728156,561339434018920,559155594059203,556961225880328,554756356340866,
    552541012128323,550315219760795,548079005588608,545832395795934,543575416402387,
    541308093264600,539030452077782,536742518377249,534444317539947,532135874785946,
    529817215179922,527488363632612,525149344902263,522800183596050,520440904171489,
    518071530937821,515692088057386,513302599546979,510903089279187,508493580983715,
    506074098248688,503644664521943,501205303112305,498756037190844,496296889792122,
    493827883815421,491349042025958,488860387056083,486361941406469,483853727447280,
    481335767419330,478808083435232,476270697480518,473723631414770,471166906972714,
    468600545765317,466024569280863,463438998886024,460843855826909,458239161230108,
    455624936103725,453001201338391,450367977708274,447725285872074,445073146374006,
    442411579644772,439740606002525,437060245653817,434370518694542,431671445110863,
    428963044780135,426245337471808,423518342848332],
   [420782080466043,418036569776042,415281830125064,412517880756342,409744740810451,
    406962429326153,404170965241229,401370367393302,398560654520648,395741845263004,
    392913958162366,390077011663772,387231024116085,384376013772764,381511998792626,
    378638997240600,375757027088474,372866106215638,369966252409808,367057483367754,
    364139816696013,361213269911602,358277860442712,355333605629407,352380522724306,
    349418628893267,346447941216055,343468476687009,340480252215698,337483284627577,
    334477590664629,331463186986002,328440090168643,325408316707924,322367883018258,
    319318805433714,316261100208623,313194783518179,310119871459032,307036380049879,
    303944325232042,300843722870051,297734588752208,294616938591160,291490788024451,
    288356152615083,285213047852061,282061489150936,278901491854346,275733071232546,
    272556242483938,269371020735590,266177421043756,262975458394391,259765147703652,
    256546503818404,253319541516720,250084275508369,246840720435309,243588890872166,
    240328801326718,237060466240365,233783899988600,230499116881477,227206131164069,
    223904957016924,220595608556524,217278099835723,213952444844201,210618657508897,
    207276751694447,203926741203617,200568639777728,197202461097084,193828218781386,
    190445926390154,187055597423134,183657245320710,180250883464309,176836525176796,
    173414183722881,169983872309504,166545604086231,163099392145636,159645249523688,
    156183189200130,152713224098852,149235367088269,145749630981687,142256028537671,
    138754572460405,135245275400058,131728149953134,128203208662829,124670464019383,
    121129928460421,117581614371305,114025534085470,110461699884763,106890123999780,
    103310818610197,99723795845101,96129067783315,92526646453721,88916543835584,85298771858868,
    81673342404553,78040267304946,74399558343992,70751227257583,67095285733859,63431745413515,
    59760617890098,56081914710305,52395647374275,48701827335886,45000466003042,41291574737959,
    37575164857454,33851247633222,30119834292120,26380936016446,22634563944210,18880729169411,
    15119442742305,11350715669677,7574558915106,3790983399228]]
private theorem dkhb_0 : muxIntListEq rkmHbHi_m512_r512_s0_c1 phbv_0 = true := by
  decide +kernel
private def pvm_0_1 : List ℤ := pZZZ 418
  [
   [1761643726,9563942270,36641001490,114387075406,308631608944,743310664174,1630908296428,
    3306233177394,6256881135488,11140914187996,18780971879378,30125224607474,46169786300264,
    67844129554556,95869508762542,130608528017308,171929687996106,219112250581008,270813184372266,
    325109591293566,379618324701736,431681787379352,478597715469372,517863342721196,
    547402078736464,565743982484264,572139018232016,566592661133758,549824790851842,
    523162963918554,488388546419692,447557979375582,402821557694170,356259093035300,
    309746690511812,264862753889888,222835326683730,184527815412146,150456531959270,
    120831501271154,95611492212604,74564934884848,57329886334160,43468093155372,32510127831872,
    23990293720620,17471352776564,12560075147358,8915157214858,6249267295290,4326940932630,
    2959848327556,2000672681332,1336530894138,882579031750,576198699446,371967277258,237475149308,
    149960656934,93679528318,57900263250,35411398338,21433275802,12840186464,7614545512,
    4470513288,2598727732,1495897524,852759906,481482318,269281158,149192068,81891808,44537902,
    24002256,12818722,6784896,3559452,1850956,954148,487606,247044,124086,61790,30506,14926,7232,
    3472,1640,758,340,148,60,18,4]]
private def pvm_0_2 : List ℤ := pZZZ 414
  [
   [419804184,2400440522,9685989558,31847372336,90501207040,229561462994,530481382114,
    1132617849306,2257430965022,4233322828478,7515881830786,12696699231324,20493417921690,
    31714811798234,47197721715678,67717369014096,93878202204174,125997879589340,164000967137064,
    207340316580796,254962233815792,305326478145198,356484590491502,406211349354270,
    452175900920622,492132839952756,524110365023060,546573099117286,558541052761320,
    559652689055596,550167895907908,530914514457142,503188687657300,468623802688262,
    429044791120250,386324075894058,342252953179972,298438352930666,256230502000782,
    216682727150834,180541029509610,148258470148332,120027942709564,95826502736680,75464874255662,
    58636795208960,44964217360416,34035798874606,25437433035258,18774626497628,13687321299188,
    9858244968754,7016107069642,4934993096794,3431198942494,2358558649034,1603092642478,
    1077578456896,716444047534,471217294992,306638029856,197448971154,125824160768,79361137392,
    49549465592,30627262922,18744107260,11359425888,6817564426,4052547754,2386143002,1391798426,
    804282498,460503536,261268994,146896262,81853620,45206888,24748288,13430516,7225694,3854218,
    2038420,1069006,555922,286694,146626,74362,37398,18652,9220,4506,2176,1034,482,214,90,34,8]]
private def pvm_0_3 : List ℤ := pZZZ 409
  [
   [92829180,557945946,2366496040,8178867224,24430302838,65136669450,158214381190,355063163858,
    743841257592,1466182069606,2736052032508,4858143045758,8241876171374,13406123465246,
    20969528500290,31622152419494,46076237105452,64997033335796,88918460432594,118152164014170,
    152701515516008,192193502265232,235840782781088,282443305964698,330434136351518,
    377968212871922,423046680631240,463664221930928,497963371014484,524378695524070,
    541755105048482,549428104375450,547258890981880,535622937685218,515356200482198,
    487667572406820,454029136080824,416056924090882,375394350832034,333608548332152,
    292106991136002,252078553523850,214459990168744,179926148331906,148900245156746,
    121579371081920,97969976401436,77928336289150,61201691231034,47466731164712,36363154775744,
    27521047984768,20581690146644,15212060379648,11113766087448,8027366524568,5733149859720,
    4049384667652,2828948716438,1955077068486,1336797863656,904458975148,605605087890,
    401348862662,263292819056,170998113770,109958345120,70016004970,44151444264,27575013628,
    17058985714,10454407780,6347391528,3818391234,2276110584,1344533098,787138560,456738636,
    262697252,149777962,84659820,47443366,26361670,14524438,7935678,4299866,2310674,1231568,
    651090,341424,177594,91636,46904,23808,11976,5972,2946,1430,684,316,138,54,18,4]]
private def pvm_0_4 : List ℤ := pZZZ 405
  [
   [19029766,120012996,534104528,1936845352,6070282882,16981689658,43278635542,101906633414,
    223997573252,463248638072,907007294308,1689716677290,3007625980386,5132773424154,
    8423365934008,13327035117238,20373292477378,30152049756216,43276419620612,60330113591716,
    81802368222286,108016049873950,139056903234396,174713306647476,214435977464418,
    257325643568684,302153845698242,347418117884226,391428388537496,432417245096098,
    468663386742116,498615684326674,521005065134556,534932945807558,539927876410280,
    535965945024318,523454721819964,503184484878382,476253652657536,443977403390572,
    407789246450510,369144880496588,329436246208120,289921580637024,251674868507004,
    215555705835324,182198519873552,152018510892756,125230680496508,101877882363788,
    81863899350408,64987996780360,50978089002278,39520452857750,30284715960126,22943557199256,
    17187130962112,12732643706796,9329773821618,6762751669742,4849934228662,3441648852512,
    2416973066152,1679987211740,1155903639242,787353293508,531005808102,354615886208,234526864318,
    153619829346,99670273050,64060425442,40790652532,25734623260,16087917056,9966532178,
    6119091224,3723605912,2245994918,1342936596,796042808,467824670,272600332,157505660,90244682,
    51277996,28896958,16151462,8954390,4924366,2686450,1453930,780658,415864,219806,115266,59970,
    30954,15844,8038,4038,2008,978,466,214,92,34,8]]
private def pvm_0_5 : List ℤ := pZZZ 400
  [
   [3613014,23869880,111283708,422746954,1387942556,4067403668,10858767766,26784086612,
    61671128386,133602234748,274011087868,534719263846,996981611154,1782229358968,3063671155818,
    5077288048332,8130140745344,12603439236892,18947667078978,27667349875780,39293896755688,
    54346317978450,73281408541132,96436950454188,123973304865202,155820089093280,191635151334732,
    230782563214418,272334803505558,315101844679580,357686787325106,398564447917104,
    436176373029638,469033571247684,495817151335532,515467189756088,527251487025596,
    530808194537300,526159248644284,513694712457380,494131073839626,468448922198542,
    437816982482828,403510115758476,366828632199826,329025249003442,291244484755646,
    254477469639290,219533317231284,187026558440612,157378830461174,130832123522508,
    107470430023742,87246574745486,70011254514340,55541785095366,43568643633212,33798518124738,
    25933160948500,19683843187638,14781594075410,10983678138792,8076918880582,5878539077174,
    4235175801122,3020665902302,2133105846478,1491585900950,1032895738192,708405350900,
    481246661386,323859237630,215917764682,142627626046,93355656828,60553150240,38924972350,
    24799942918,15661674618,9804473228,6084730984,3743873536,2283991104,1381627776,828781966,
    493026824,290877080,170209626,98791750,56878060,32484892,18405800,10346384,5770402,3193214,
    1753374,955358,516558,277166,147586,77986,40886,21270,10972,5610,2838,1414,692,328,148,62,20,
    4]]
private def pvm_0_6 : List ℤ := pZZZ 395
  [
   [634666,4386042,21389598,84995752,291897688,894778336,2498701396,6446780490,15526614204,
    35183092774,75476273734,154058891208,300443844694,561760999492,1010039996356,1750786805586,
    2932251190564,4754342146432,7475701787510,11417085643760,16959025057114,24531867272066,
    34596773817472,47617127336014,64020999161488,84156735750604,108245136287148,136332881865920,
    168252604610990,203595064571410,241698231932288,281656665668896,322352573808954,
    362507579082158,400751812275108,435704849774846,466061502004430,490674761177024,
    508628426047834,519293001570342,522360263170574,517854126252926,506117869208550,
    487780018659892,463703057888692,434920378847660,402567475225786,367813275824038,
    331796834957588,295573481053348,260073158878442,226072270315620,194178986729452,
    164830896979332,138303045375084,114723931274712,94096872211120,76324229160968,61232290107778,
    48595033340732,38155474856794,29643785090226,22791794005790,17343861527098,13064358698092,
    9742182947238,7192826716340,5258546717012,3807157994306,2729919676610,1938902906568,
    1364148323268,950839750604,656648468838,449341912344,304702993962,204771100302,136391745604,
    90047019728,58931275146,38234029462,24593121914,15684381392,9918391162,6219627250,3867810560,
    2385456144,1459184034,885334524,532830488,318112014,188410366,110710040,64543106,37334980,
    21429274,12205226,6898448,3869408,2153986,1190052,652570,355170,191870,102876,54750,28916,
    15148,7868,4048,2058,1030,502,238,106,40,12,2]]
private def pvm_0_7 : List ℤ := pZZZ 391
  [
   [103040,743836,3789456,15730452,56434126,180713322,527168034,1420803430,3574544238,8461105688,
    18960471980,40426620964,82353557282,160844202826,302081113646,546947752072,956836479922,
    1620493770960,2661495198656,4245630246160,6587147536754,9952521482708,14660221734226,
    21074969748436,29595212421892,40633062497922,54586738098298,71806517115984,92556294315638,
    116973839343330,145033634769074,176516567818662,210990640994502,247806204514374,
    286108028056444,324864934863956,362915902705340,399029723036466,431973741356850,
    460586090077372,483845321470758,500931520016164,511273795460780,514580418220316,
    510849578015546,500360607145394,483647288280200,461456365706670,434695451812900,
    404375086210356,371549751845798,337262232585698,302494910597600,268130579350084,
    234924227995132,203486164320478,174275891368808,147605409517034,123650118042122,
    102465241433066,84005682176430,68147360713714,54708391907280,43468810901478,34187949601838,
    26618937093504,20520123568094,15663489913324,11840296948038,8864350940204,6573323305628,
    4828573720202,3513900234704,2533590040582,1810081512364,1281481110444,899114340414,
    625232597058,430949741222,294444447362,199436362978,133924853206,89167101654,58866027236,
    38536351314,25017889668,16107667764,10285929724,6514928404,4093139948,2550993788,1577220674,
    967452300,588767624,355515218,213007282,126640986,74716880,43747006,25420448,14660296,8391622,
    4767720,2688774,1505198,836452,461434,252704,137386,74144,39718,21114,11136,5818,3008,1536,
    774,376,172,74,26,8]]
private def pvm_0_8 : List ℤ := pZZZ 386
  [
   [15450,116312,618236,2677686,10023158,33488376,101927288,286621734,752360076,1858053874,
    4344128094,9663610096,20538512052,41850713478,82002680786,154900752120,282712365318,
    499516718740,855894277790,1424375744092,2305493754662,3633959114912,5584239070122,
    8374582650836,12268363193688,17571541834422,24625145963928,33791937518944,45436927664230,
    59902054929056,77476125716980,98361929252572,122643170536926,150254394664608,180957296045858,
    214326640810382,249748452433284,286432149800246,323437072158532,359712414089370,
    394148193807894,425633664427926,453118705929678,475673318873760,492540434086022,
    503177844130294,507286077613666,504820350356858,495986180450176,481219680361080,
    461154785234528,436580621485262,408392788134856,377542490074008,344987250924454,
    311646406831364,278363832055584,245879476139200,214810402786588,185641201342212,
    158722960301026,134279490469254,112419179110740,93150738625762,76401159192708,62034348021180,
    49869196898128,39696123438132,31291443455006,24429223209642,18890510756378,14470043727260,
    10980672912096,8255829301412,6150403546068,4540410212832,3321784838544,2408619325098,
    1731089210368,1233271676144,871000875710,609860602272,423375283140,291429376002,198922194722,
    134649168318,90390402954,60181938758,39743081696,26033590326,16916431932,10904607288,
    6973674228,4424730856,2785532922,1739995322,1078518994,663389388,404940132,245309738,
    147489140,88012778,52130346,30648758,17886706,10362400,5959634,3402698,1928798,1085486,606524,
    336484,185346,101360,55036,29664,15860,8416,4422,2300,1178,588,284,128,54,18,4]]
private def pvm_0_9 : List ℤ := pZZZ 382
  [
   [2146,16756,92798,418850,1634054,5690114,18050120,52900216,144720146,372488186,907619284,
    2104182240,4660706332,9897383472,20210465012,39785833950,75673250148,139336923604,
    248800289862,431485161020,727799494552,1195446956288,1914312004882,2991619210072,
    4566885894456,6816003129306,9953620481036,14232909679932,19941777995124,27394725027928,
    36919806201604,48840582886570,63453479746552,81001586523482,101646564212546,125440860146234,
    152302815575484,181997386043952,214125036369208,248120900683508,283265537630158,
    318707627142126,353497849259598,386632081079732,417101075388392,443943062204662,
    466295332234648,483440867767534,494846482795242,500189673739912,499372378652542,
    492520982084300,479973059283294,462252405986022,440034747449346,414107091651324,
    385323952456436,354563621863216,322687352058654,290503778737188,258740252746670,
    228022027604504,198859550390478,171643484615206,146646599761816,124031317520806,
    103861514599462,86117135630866,70710244463220,57501308097712,46314732248106,36952919667544,
    29208374965074,22873611539730,17748813139952,13647356611816,10399411560834,7853899347726,
    5879123611454,4362384671612,3208868617280,2340066240182,1691933888010,1212963188526,
    862283416028,607881682236,424993598902,294691102080,202674574058,138262618490,93563952788,
    62810899806,41831933328,27640795954,18121139288,11787858458,7608873696,4873746818,3098013198,
    1954345632,1223592842,760342214,468960904,287103070,174473948,105252486,63031876,37474074,
    22118754,12961794,7541536,4356714,2499058,1423404,805038,452126,252152,139644,76790,41924,
    22720,12220,6520,3442,1796,920,456,220],
   [100,40,10]]
private def pvm_0_10 : List ℤ := pZZZ 377
  [
   [284,2228,12812,60156,244310,885746,2925490,8926938,25427086,68139560,172864320,417249328,
    962211136,2127360608,4522669144,9269162444,18354546278,35184586032,65406031366,118088932710,
    207361071940,354579537978,591098281292,961640263454,1528204863242,2374335198740,3609440643238,
    5372727861442,7836156461240,11205725763742,15720343537606,21647551874220,29275510875608,
    38900878788868,50812574631504,65271845936054,82489551958030,102602058184696,125647558101096,
    151544928040026,180077323530940,210882601266990,243452285412220,277140206453854,
    311181171917150,344719154459728,376843595958450,406631624861154,433193360851668,
    455717109776232,473511178247380,486039272227510,492946962225538,494077442439702,
    489475700984064,479381158657916,464209728718356,444527014238820,421014927031810,
    394434342824408,365586489728574,335275616308114,304275139390070,273298983563574,
    242979255309010,213850806330126,186342687855428,160776023933630,137367466294096,
    116237150354794,97419951644314,80878832939366,66519155227024,54202975899314,43762549747462,
    35012458181350,27759999019858,21813657302228,16989636202702,13116550658042,10038473472490,
    7616576596714,5729633494460,4273647863970,3160855771386,2318318543516,1686287900282,
    1216487130284,870415880712,617753534226,434908435350,303737896410,210446878054,144661036384,
    98661768432,66766187098,44832834938,29873688992,19754003258,12963285996,8442837628,5457507088,
    3501478476,2229863148,1409588838,884528198,551001780,340747840,209203214,127518950,77173420,
    46372750,27667808,16391468,9642874,5633190,3267934,1882674,1077140,612030,345372,193560,
    107724,59540,32672,17800,9622,5156],
   [2732,1426,730,366,172,74,26,6]]
private def pvm_0_11 : List ℤ := pZZZ 372
  [
   [44,280,1634,7936,33482,126206,433578,1376288,4077818,11367292,29997492,75317030,180668038,
    415490362,918795910,1958684962,4034252588,8043826380,15553005490,29207036042,53343653874,
    94872845120,164496310010,278338189870,460045644364,743388871050,1175341585008,1819553010066,
    2760032142550,4104759392822,5988829208934,8576624029860,12062442735844,16668975424454,
    22643049833564,30248187926364,39753711270480,51420417382426,65483199961034,82131374700368,
    101487858746540,123588688156238,148364594679524,175626456871596,205056359234682,
    236205723321954,268501525122842,301261015330384,333714665825272,365036344867984,
    394379050509768,420913980209078,443870346908924,462573210897472,476476700735710,
    485190336304756,488496707648850,486359448597526,478921203977152,466492048122330,
    449529498587074,428611822268858,404406709046576,377637568951070,349049692884358,
    319378323581774,289320347908646,259510888716404,230505593401398,202768934447576,
    176668395715206,152474048557570,130362744123660,110425970951474,92680348157640,77079733654228,
    63528007394752,51891721950240,42011976307696,33715044610616,26821463455086,21153436935464,
    16540549623222,12823879717822,9858676805198,7515812752556,5682233885764,4260642438184,
    3168620414590,2337384404836,1710329885346,1241491763680,894017086568,638717826478,
    452747603796,318426576928,222223546368,153893239060,105759233604,72128424140,48820657824,
    32796615688,21867614112,14472350008,9507359162,6199853538,4013476716,2579256770,1645581018,
    1042343356,655518288,409313978,253770442,156225828,95500634,57971590,34945672,20919640,
    12436846,7343016,4305842,2507682,1450534,833366,475554,269544,151738,84838],
   [47106,25980,14218,7718,4150,2206,1152,592,296,136,58,18,4]]
private def pvm_0_12 : List ℤ := pZZZ 367
  [
   [16,42,202,970,4218,16466,58704,193688,596436,1728058,4739674,12368500,30836280,73704396,
    169394260,375306964,803383214,1664773694,3345298702,6528769502,12392105386,22904349842,
    41270633032,72570801218,124649177756,209314422794,343903850086,553251652170,872072227294,
    1347725890346,2043273901606,3040654483240,4443725825922,6380833908144,9006483440772,
    12501633193120,17072117357410,22944726699120,30360578044976,39565563462230,50797898582888,
    64273070790220,80166800548414,98596942612248,119605531941640,143142383810448,169051753907074,
    197063525551852,226790203788944,257730662554726,289281131436906,320753359342098,
    351399303531440,380441121684914,407104750817030,430654992954478,450429833965832,
    465871721699150,476553725094492,482198868931170,482691452677520,478079765993930,
    468570249487792,454513758030674,436385111605776,414757522641884,390273741442690,
    363615851738544,335475582178662,306526796742128,277401518443072,248670463726334,
    220828658949804,194286312444666,169364757315668,146296984919530,125232071285672,
    106242663992314,89334642431996,74458080755518,61518716360784,50389241506158,40919874960830,
    32947819211668,26305353619056,20826445068840,16351868389488,12732915522070,9833834319274,
    7533176255036,5724250134742,4314879901238,3226652987282,2393825433732,1762024832288,
    1286865112860,932560638448,670602658416,478539935936,338887803704,238176094484,166136121520,
    115019740138,79038999546,53912457612,36503370686,24535225778,16371072230,10844524596,
    7131916156,4656717506,3018886614,1943219738,1241995018,788233566,496753734,310879568,
    193206366,119245502,73091474,44494672,26901608,16154340,9635014,5707926,3358754,1963184,
    1139828],
   [657380,376608,214320,121156,68028,37932,21008,11546,6290,3390,1808,948,486,240,108,42,12,2]]
private def pvm_0_13 : List ℤ := pZZZ 363
  [
   [14,14,36,118,496,1994,7266,24868,79496,239180,681312,1846448,4780954,11867880,28327064,
    65179008,144896230,311815534,650699722,1318788536,2599453026,4989336888,9335743658,
    17046984904,30405202068,53018251092,90453630284,151101703462,247315726700,396870163348,
    624764053012,965370572830,1464895852922,2184059280560,3200845446886,4613108334552,
    6540737616696,9127033785914,12538893907306,16965394645600,22614384836376,29706774904458,
    38468339302366,49119029382634,61860019187452,76858959585490,94234174310510,114038767121732,
    136245792743412,160735747121156,187287631837942,215574729209804,245165986383762,
    275533559807540,306066640122882,336091197659000,364894804023422,391755242786192,
    415971266800072,436893628756150,453954430698550,466692917946822,474776077412592,
    478012768213156,476360579233716,469925130248044,458952062642436,443812456100216,
    424982818189794,403021093935988,378540313831618,352181536412652,324587653278486,
    296379428909134,268134871322052,240372703467342,213540361130028,188006610547684,
    164058582685754,141902779340758,121669429862860,103419469984900,87153373279704,72821083299182,
    60332359121640,49566945633526,40384098856022,32631123391916,26150702881522,20786916909528,
    16389933432022,12819441384542,9946942833692,7657058805334,5848020027254,4431516332580,
    3332069802442,2486080283184,1840670800740,1352437251390,986183652618,713702700182,
    512642370732,365483352042,258639320718,181682399574,126689210166,87698384438,60267767688,
    41118395450,27852256910,18731523512,12508039552,8293225200,5459967476,3569464274,2317267170,
    1493903928,956435826,608118810,384001594,240825182,150005452,92802622,57026006,34806190,
    21101908,12708050],
   [7602184,4517626,2666890,1563970,911146,527338,303202,173182,98268,55392,31006,17234,9502,5194,
    2810,1500,788,400,192,86,32,8]]
private def pvm_0_14 : List ℤ := pZZZ 358
  [
   [14,12,20,30,56,248,846,2928,9662,30114,89032,250372,672786,1733250,4293558,10252924,23654656,
    52828892,114409870,240636676,492228896,980440126,1903771982,3607414150,6676877194,12081548822,
    21388956428,37076095722,62969765124,104852590290,171274139610,274605695686,432371080846,
    668872590556,1017108910810,1520949789592,2237490066494,3239454698732,4617469642536,
    6481955769690,8964351184224,12217329613116,16413667983156,21743433577810,28409217390744,
    36619239541970,46578294655006,58476684362814,72477489339726,88702747745080,107219309710376,
    128025305120798,151038271225484,176086017432414,202901242864450,231120762178360,
    260289941180108,289872610897240,319266341777776,347822551049414,374870522961548,
    399744081174164,421809398861978,440492291564836,455303326232880,465859200586646,
    471899090214764,473295005273672,470055613288948,462323432417992,450365741627424,
    434559953623580,415374521805762,393346681255550,369058443324726,343112271946756,
    316107775604030,288620568502388,261184210446500,234275852863390,208305924476264,
    183611908287424,160456011734760,139026328740484,119440944544746,101754344539018,
    85965454423148,72026654394888,59853165356008,49332289348116,40332088357594,32709194710356,
    26315553450854,21003995259218,16632622653808,13068059618200,10187664434328,7880838001126,
    6049577014384,4608425558772,3483972750714,2614030947626,1946611381404,1438794197020,
    1055569649696,768708028852,555698672174,398783748936,284100536734,200936652296,141095908216,
    98367837470,68091082674,46799412756,31938751362,21643965702,14565011056,9733147104,6459179628,
    4256923854,2786258510,1811199272,1169344266,749827986,477568342,302117098,189841866,118494006],
   [73468152,45249148,27684724,16826670,10160012,6094490,3631910,2150296,1264826,739160,429160,
    247558,141876,80780,45688,25662,14306,7914,4342,2356,1258,654,328,158,70,24,4]]
private def pvm_0_15 : List ℤ := pZZZ 353
  [
   [14,12,14,28,12,42,116,336,1098,3458,10578,30820,85864,229392,589350,1459652,3492786,8090482,
    18172296,39641136,84097654,173726004,349848492,687506414,1319666382,2476382584,4546565254,
    8172988412,14394824300,24856227890,42104060056,70002284176,114294193254,183345459316,
    289099824152,448273676416,683804341484,1026548370930,1517199603588,2208362172278,
    3166671888052,4474812810706,6233228045044,8561280078256,11597582692666,15499210749856,
    20439502987360,26604212419164,34185832918582,43376039890748,54356324453680,67287066635160,
    82295471749248,99462969556272,118812829738380,140298860621948,163796113381126,189094497333160,
    215896115404338,243816951891338,272393295094122,301092971331434,329331127517640,
    356489955249360,381941430936162,405071883761002,425307021907968,442135966289978,
    455132869548822,463974835700928,468455091511342,468490674422680,464124266602664,
    455520189254886,442954943733410,426803016493816,407518928896170,385616692960160,
    361647921404600,336179834418608,309774314379242,282968997527952,256261177481822,
    230095050846948,204852581787412,180848020066390,158325892343910,137462111523916,
    118367720960820,101094711825038,85643321051496,71970228754844,59997120042790,49619147684026,
    40712919618144,33143729869198,26771845234436,21457746937950,17066301812872,13469898823640,
    10550632795336,8201648359436,6327774657738,4845587259560,3683030395294,2778722445120,
    2081052972470,1547162521808,1141878606140,836664099568,608618539532,439559194722,315197436280,
    224416993772,158653947820,111373563732,77635999484,53741203988,36942643644,25219572874,
    17098154140,11512635942,7698859482,5113471874,3373298200,2210315464,1438551780,929992082],
   [597208646,380957348,241401624,151959384,95027214,59035206,36435610,22340958,13609648,8237022,
    4953132,2959258,1756652,1036078,607168,353536,204538,117572,67146,38086,21454,12000,6660,3656,
    1978,1058,554,274,128,54,18,4]]
private def pvm_0_16 : List ℤ := pZZZ 348
  [
   [14,12,8,28,12,12,36,52,146,388,1160,3454,9946,27498,73210,187898,466044,1118996,2605336,
    5891124,12954730,27739380,57901992,117941350,234651478,456394884,868489040,1618131118,
    2953827498,5286325994,9280613416,15991637542,27059947568,44987208308,73515152182,118134424710,
    186751176234,290538192892,444992735966,671213930258,997397480098,1460523984508,2108189007444,
    3000488963948,4211838440564,5832554552320,7970006284104,10749096412900,14311826180328,
    18815694134524,24430705679978,31334822673618,39707764494536,49723182068592,61539359597798,
    75288746899038,91066776686186,108920561695114,128838180819372,150739336232410,174468181717280,
    199789076825636,226385908107894,253865439957698,281764922849416,309563911588116,
    336699951576630,362587501384676,386639200495900,408288385884722,427011629836030,
    442350027725762,453928014121896,461468625867960,464804350851240,463882982866346,
    458768223000816,449635100012844,436760599660528,420510171536152,401321001765286,
    379683087132988,356119213975810,331164933851608,305349544463048,279178940853656,
    253121014603044,227594065692128,202958471131278,179511643136660,157486121642894,
    137050491679834,118312702007532,101325289768952,86091985528458,72575179686670,60703768528016,
    50380958433652,41491682032856,33909362543342,27501845422294,22136394151148,17683715406754,
    14021035435358,11034292938284,8619544191990,6683694382160,5144676805104,3931200637888,
    2982180496294,2245949031636,1679339215022,1246707284474,918951824536,672570010078,
    488779265670,352721787250,252760642624,179869445760,127112707666,89210657982,62180329220,
    43043723574,29593680146,20208402114,13706296412,9233672272,6178823606],
   [4107000204,2711699724,1778551936,1158802720,750032648,482267558,308065060,195502554,123261360,
    77210194,48051172,29711406,18253262,11142004,6757714,4072454,2438592,1450952,857832,503954,
    294188,170644,98340,56304,32032,18092,10138,5636,3102,1682,896,464,230,106,42,12,2]]
private def pvm_0_17 : List ℤ := pZZZ 344
  [
   [14,12,2,26,18,4,24,20,40,68,148,372,1068,2998,8238,21872,56152,139652,336828,789064,1797686,
    3987992,8624144,18199084,37511236,75583582,149002440,287593318,543851000,1008259122,
    1833631188,3272947306,5736902670,9879562672,16723122798,27835724618,45579405402,73448258264,
    116519301092,182039784516,280173947784,424928678118,635270224218,936432206132,1361398024550,
    1952518165008,2763195173278,3859537356336,5321848540596,7245788423836,9743009980492,
    12941061455986,16982335431970,22021860746696,28223768367802,35756321788362,44785486189970,
    55467115917204,67937961296444,82305825250060,98639326830668,116957840423288,137222263107908,
    159327306528022,183096003822590,208277060616374,234545560318652,261507362043984,
    288707313856542,315641159293416,341770759714598,366542009736658,389404608947172,
    409832689606388,427345202678160,441524943399140,452035156232136,458632793977826,
    461177706837120,459637288389240,454086386681608,444702577627244,431757172330604,
    415602569486378,396656752083702,375385852877822,352285769876562,327863801806142,
    302621200028372,277037408065440,251556596353634,226576913425022,202442680967708,
    179439573570828,157792656623500,137667017025400,119170616923974,102358933064894,
    87240912846422,73785779529250,61930248057446,51585763187712,42645436211740,34990428752090,
    28495605841674,23034350698896,18482496447412,14721382943688,11640088524204,9136916597482,
    7120236172342,5508784849492,4231544121616,3227291821014,2443927026652,1837650364592,
    1372068861036,1017280513984,748980431546,547618354978,397627010270,286732171176,205348567622,
    146060717578,103184203728,72400627692,50458208288,34929511818],
   [24017897756,16404749968,11130291286,7501630412,5022578500,3340636688,2207356658,1448990816,
    944968926,612261442,394123494,252064746,160171206,101124706,63436374,39539878,24488126,
    15069756,9214980,5599206,3380710,2028352,1209316,716476,421816,246774,143460,82870,47556,
    27108,15344,8620,4798,2638,1430,762,394,192,86,32,8]]
private def pvm_0_18 : List ℤ := pZZZ 339
  [
   [14,12,1,18,24,4,18,16,22,28,50,66,132,324,856,2322,6122,15734,39246,95176,224488,515708,
    1154856,2523634,5386408,11238846,22942340,45852948,89785400,172356916,324558238,599842274,
    1088644972,1941111840,3401947338,5862777804,9939249378,16582263020,27235219492,44051771950,
    70191130480,110210078360,170572070024,260293479552,391744559090,581617197004,852062421312,
    1231987198502,1758482136136,2478329335134,3449513554280,4742631423566,6442064808776,
    8646758446004,11470422101376,15040967609958,19498995061884,24995163552412,31686322759246,
    39730343141208,49279663824860,60473675057422,73430160891790,88236139754988,104938546193834,
    123535285819384,143967256658862,166111954214416,189779257203194,214709922185280,
    240577198151174,266991811255166,293510374387888,319647059316746,344888146827938,
    368708860426480,390591709396712,410045433330032,426623565136978,439941620921120,
    449691985181088,455655685037016,457710428381570,455834504151504,450106391018290,
    440700174663178,427877114398756,411973909913026,393388384227066,372563409750980,
    349969955687570,326090127097938,301401003502588,276359976637308,251392144422604,
    226880154439590,203156718655350,180499854404884,159130755526054,139214070409150,
    120860266078240,104129691863956,89037922637876,75561957517770,63646871203254,53212556287870,
    44160250086616,36378602794990,29749109701410,24150794054134,19464085395948,15573888174936,
    12371875744188,9758074965062,7641826821878,5942219640324,4588094989114,3517723663470,
    2678241889466,2024927566288,1520384331560,1133688626576,839542636244,617464623312,
    451038177832,327233475810,235806842182,168779679740],
   [119994015542,84739336042,59443820874,41422327708,28673329762,19717285270,13469478614,
    9141095350,6163088474,4128193094,2747208256,1816358202,1193157914,778733516,504989274,
    325375938,208308114,132510936,83758554,52607234,32832758,20362064,12548586,7684788,4676696,
    2828282,1699752,1015156,602508,355366,208288,121316,70210,40370,23054,13072,7352,4094,2256,
    1222,648,330,158,70,24,4]]
private def pvm_0_19 : List ℤ := pZZZ 336
  [
   [14,12,1,10,24,4,14,16,20,18,36,44,54,98,198,514,1336,3486,8844,21934,52880,124280,284774,
    636798,1390842,2969668,6203342,12686898,25420828,49934870,96217624,181962196,337915278,
    616516798,1105579758,1949527612,3381725446,5772749278,9701061514,16054492836,26173127862,
    42046537578,66580606434,103951169688,160062907118,243131918636,364408535970,539052544936,
    787165464928,1134973310400,1616138016548,2273156454480,3158783162034,4337387623678,
    5886130834542,7895821324358,10471290716394,13731116577304,17806519235792,22839272629254,
    28978499634076,36376271175882,45181995576718,55535668064482,67560146064484,81352717691798,
    96976330881680,114450939715494,133745493130840,154771130216978,177376148044370,
    201343267276868,226389635791934,252169883187028,278282375453150,304278629184342,
    329675641607938,353970691772718,376657985553670,397246368179814,415277226033652,
    430341654253994,442095983393072,450274837097878,454701028358282,455291784376806,
    452061005799320,445117498563450,434659348570910,420964823883012,404380371267908,
    385306411996124,364181728146994,341467262214500,317630130817400,293128583207582,
    268398525689112,243842094937868,219818608635490,196638062925290,174557194131132,
    153777986358680,134448394107344,116664964352286,100476987581206,85891781454610,72880711549448,
    61385576972968,51325029465310,42600747493468,35103146399992,28716466998936,23323143964394,
    18807408719294,15058127089026,11970908486308,9449550456962,7406900371492,5765225761882,
    4456187505018,3420507156548,2607412701786,1973937200564,1484133494664,1108256350564,
    821951930628,605483904140,443016196414],
   [321964524722,232422532866,166663454624,118714675476,84000146996,59044140994,41229115202,
    28600312796,19709973366,13494553266,9179029214,6203104832,4164892544,2778361778,1841500902,
    1212720962,793529610,515924344,333301060,213954870,136473798,86501700,54482224,34099366,
    21208258,13108012,8050952,4914078,2980750,1796814,1076404,640834,379148,222930,130258,75624,
    43624,24998,14220,8028,4488,2482,1354,720,370,180,80,30,8]]
private theorem pchk_0_0 : pChk 3 513
    phbv_0 rkmViHi_m512_r512_s0_c1 pvm_0_1 = true := by
  decide +kernel
private theorem pchk_0_1 : pChk 3 513
    phbv_0 pvm_0_1 pvm_0_2 = true := by
  decide +kernel
private theorem pchk_0_2 : pChk 3 513
    phbv_0 pvm_0_2 pvm_0_3 = true := by
  decide +kernel
private theorem pchk_0_3 : pChk 3 513
    phbv_0 pvm_0_3 pvm_0_4 = true := by
  decide +kernel
private theorem pchk_0_4 : pChk 3 513
    phbv_0 pvm_0_4 pvm_0_5 = true := by
  decide +kernel
private theorem pchk_0_5 : pChk 3 513
    phbv_0 pvm_0_5 pvm_0_6 = true := by
  decide +kernel
private theorem pchk_0_6 : pChk 3 513
    phbv_0 pvm_0_6 pvm_0_7 = true := by
  decide +kernel
private theorem pchk_0_7 : pChk 3 513
    phbv_0 pvm_0_7 pvm_0_8 = true := by
  decide +kernel
private theorem pchk_0_8 : pChk 3 513
    phbv_0 pvm_0_8 pvm_0_9 = true := by
  decide +kernel
private theorem pchk_0_9 : pChk 3 513
    phbv_0 pvm_0_9 pvm_0_10 = true := by
  decide +kernel
private theorem pchk_0_10 : pChk 3 513
    phbv_0 pvm_0_10 pvm_0_11 = true := by
  decide +kernel
private theorem pchk_0_11 : pChk 3 513
    phbv_0 pvm_0_11 pvm_0_12 = true := by
  decide +kernel
private theorem pchk_0_12 : pChk 3 513
    phbv_0 pvm_0_12 pvm_0_13 = true := by
  decide +kernel
private theorem pchk_0_13 : pChk 3 513
    phbv_0 pvm_0_13 pvm_0_14 = true := by
  decide +kernel
private theorem pchk_0_14 : pChk 3 513
    phbv_0 pvm_0_14 pvm_0_15 = true := by
  decide +kernel
private theorem pchk_0_15 : pChk 3 513
    phbv_0 pvm_0_15 pvm_0_16 = true := by
  decide +kernel
private theorem pchk_0_16 : pChk 3 513
    phbv_0 pvm_0_16 pvm_0_17 = true := by
  decide +kernel
private theorem pchk_0_17 : pChk 3 513
    phbv_0 pvm_0_17 pvm_0_18 = true := by
  decide +kernel
private theorem pchk_0_18 : pChk 2 513
    phbv_0 pvm_0_18 pvm_0_19 = true := by
  decide +kernel
private theorem pchk_0_19 : pChk 2 513
    phbv_0 pvm_0_19 rkmVoHi_m512_r512_s0_c1 = true := by
  decide +kernel
private theorem pwalkF_0 : muxFastIterFullT16 58 513
    phbv_0 rkmViHi_m512_r512_s0_c1 = rkmVoHi_m512_r512_s0_c1 :=
  pChFull 56 2 513 (pChFull 54 2 513 (pChFull 51 3 513 (pChFull 48 3 513 (pChFull 45 3 513
    (pChFull 42 3 513 (pChFull 39 3 513 (pChFull 36 3 513 (pChFull 33 3 513 (pChFull 30 3 513
    (pChFull 27 3 513 (pChFull 24 3 513 (pChFull 21 3 513 (pChFull 18 3 513 (pChFull 15 3 513
    (pChFull 12 3 513 (pChFull 9 3 513 (pChFull 6 3 513 (pChFull 3 3 513 (pCS pchk_0_0) pchk_0_1)
    pchk_0_2) pchk_0_3) pchk_0_4) pchk_0_5) pchk_0_6) pchk_0_7) pchk_0_8) pchk_0_9) pchk_0_10)
    pchk_0_11) pchk_0_12) pchk_0_13) pchk_0_14) pchk_0_15) pchk_0_16) pchk_0_17) pchk_0_18)
    pchk_0_19
/-- Certified `T_16` walk chunk `m512_r512_s0_c1`. -/
theorem rkmWalkChkHi_m512_r512_s0_c1 : muxFastIterFullT16 58 513
    rkmHbHi_m512_r512_s0_c1 rkmViHi_m512_r512_s0_c1 = rkmVoHi_m512_r512_s0_c1 :=
  (congrArg (fun h => muxFastIterFullT16 58 513 h rkmViHi_m512_r512_s0_c1)
    (muxIntListEq_eq_true.mp dkhb_0)).trans pwalkF_0
/-- Standalone table witness (`FindAllJohnsonRampKickMuxHi512T4`). -/
theorem laneWitness_FindAllJohnsonRampKickMuxHi512T4 :
    rkmWalkChkHi_m512_r512_s0_c1 = rkmWalkChkHi_m512_r512_s0_c1 :=
  rfl
private theorem laneRoot_Hi512T4 : rkmHbHi_m512_r512_s0_c1 = rkmHbHi_m512_r512_s0_c1 :=
  (And.intro (Eq.refl rkmHbHi_m512_r512_s0_c0) rfl).right
end
end QuantumComputation.Specs.DickeSol
